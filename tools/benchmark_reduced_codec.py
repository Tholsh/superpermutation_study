# SPDX-License-Identifier: GPL-3.0-or-later
# Copyright (C) 2026 Theo H.

"""Compare both codec layouts and direct gzip, checking every successful decode."""
import argparse
import gzip
import hashlib
import json
import lzma
import os
from pathlib import Path
import platform
import subprocess
import sys
import tempfile
import zlib

ROOT = Path(__file__).resolve().parents[1]
CHUNK = 1024 * 1024
WHITESPACE = b" \t\r\n\f\v"


def digest_file(path):
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(CHUNK), b""):
            digest.update(chunk)
    return digest.hexdigest()


def gzip_size(path, level):
    # Empty filename and fixed time exclude per-run metadata from the comparison.
    with tempfile.TemporaryFile() as sink:
        with gzip.GzipFile(filename="", fileobj=sink, mode="wb",
                           compresslevel=level, mtime=0) as compressed:
            with path.open("rb") as source:
                for chunk in iter(lambda: source.read(CHUNK), b""):
                    compressed.write(chunk)
        return sink.tell()


def positive_int(value):
    number = int(value)
    if number <= 0:
        raise argparse.ArgumentTypeError("must be positive")
    return number


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("n", type=int, choices=range(1, 33), metavar="N")
    parser.add_argument("input", type=Path, help="word file, optionally .xz compressed")
    parser.add_argument("--codec", type=Path,
                        default=ROOT / ("reduced-codec.exe" if os.name == "nt" else "reduced-codec"))
    parser.add_argument("-z", "--zero-based", action="store_true")
    parser.add_argument("--bits", type=int, choices=[4, 6], nargs="+", default=[4, 6])
    parser.add_argument("--prefix-bytes", type=positive_int,
                        help="test only this many decompressed input bytes, before whitespace removal")
    parser.add_argument("--gzip-level", type=int, choices=range(1, 10), default=9)
    args = parser.parse_args()
    codec = str(args.codec.resolve())
    with tempfile.TemporaryDirectory(prefix="reduced-codec-benchmark-") as directory:
        work = Path(directory)
        word = work / "word.txt"
        opener = lzma.open if args.input.suffix.lower() == ".xz" else open
        with opener(args.input, "rb") as source, word.open("wb") as output:
            remaining = args.prefix_bytes
            while remaining is None or remaining > 0:
                chunk = source.read(CHUNK if remaining is None else min(CHUNK, remaining))
                if not chunk:
                    break
                if remaining is not None:
                    remaining -= len(chunk)
                output.write(chunk.translate(None, WHITESPACE))
        expected_hash = digest_file(word)
        result = {
            "input": str(args.input), "n": args.n, "zero_based": args.zero_based,
            "prefix_bytes_limit": args.prefix_bytes,
            "word_bytes": word.stat().st_size, "word_sha256": expected_hash,
            "gzip_level": args.gzip_level,
            "python": platform.python_version(), "zlib": zlib.ZLIB_RUNTIME_VERSION,
            "direct_gzip_bytes": gzip_size(word, args.gzip_level), "layouts": [],
        }
        for bits in args.bits:
            packed = work / f"word-{bits}.spra"
            command = [codec, "encode", "--bits", str(bits)]
            if args.zero_based:
                command.append("-z")
            with packed.open("wb") as output:
                encoded = subprocess.run(command + [str(args.n), str(word)],
                                         stdout=output, stderr=subprocess.PIPE)
            if encoded.returncode:
                result["layouts"].append({"bits_per_field": bits, "fits": False,
                                          "error": encoded.stderr.decode(errors="replace").strip()})
                continue
            restored = work / "restored.txt"
            with restored.open("wb") as output:
                decoded = subprocess.run([codec, "decode", str(packed)],
                                         stdout=output, stderr=subprocess.PIPE)
            if decoded.returncode:
                raise RuntimeError(decoded.stderr.decode(errors="replace").strip())
            if restored.stat().st_size != word.stat().st_size or digest_file(restored) != expected_hash:
                raise RuntimeError(f"{bits}-bit round trip differs from input")
            result["layouts"].append({"bits_per_field": bits, "fits": True,
                                      "spra_bytes": packed.stat().st_size,
                                      "gzip_bytes": gzip_size(packed, args.gzip_level),
                                      "round_trip_sha256_matches": True})
        print(json.dumps(result, indent=2))


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, lzma.LZMAError, RuntimeError) as error:
        print(f"benchmark-reduced-codec: {error}", file=sys.stderr)
        sys.exit(1)
