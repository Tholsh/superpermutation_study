# SPRA corpus

The complete [Tholsh/SPRA](https://github.com/Tholsh/SPRA) repository is a submodule at `SPRA/`, pinned to `c11da7d4aac3d100deb705c7982aa890f4cba863`. This includes its source, corpus, recipes, provenance, and history. Corpus words are trusted as maintained upstream; this migration does not revalidate their results.

## Initialize and update

```sh
git submodule update --init --recursive
# Intentionally adopt a later upstream revision:
git -C SPRA fetch origin
git -C SPRA checkout --detach origin/main
git add SPRA
git commit -m "Update pinned SPRA corpus"
```

Normal initialization checks out the recorded revision rather than following the latest upstream branch. See [SPRA's corpus guide](../SPRA/docs/corpus.md) for formats, collections, and attribution.

## Read corpus words

Paths are now `SPRA/words/N/LENGTH/`. Smaller words include plain text and N=6 collection archives. N>=9 use one-based `.spra.xz` archives. The parent repository's historical version-1 codec remains unchanged; use SPRA's decoder for current archives.

Run SPRA builds and commands in WSL/Linux Bash. The following keeps generated binaries and expanded words outside the submodule:

```sh
mkdir -p build/spra
g++ -std=c++20 -O2 SPRA/tools/reduced_codec.cpp -o build/spra/reduced_codec
export SPRA_CODEC="$PWD/build/spra/reduced_codec"
set -o pipefail
bash SPRA/tools/spra-xz.sh decode SPRA/words/9/408731/superpermutation-9-408731.spra.xz
# Prepare the zero-based N=11 baseline for the existing reproduction script:
bash SPRA/tools/spra-xz.sh decode SPRA/words/11/43930628/superpermutation-11-43930628.spra.xz | python3 tools/relabel_words.py --to 0 -n 11 > build/halfar-input.txt
```

SPRA decoding emits word symbols without a final newline. `xz -dc` alone emits binary SPRA tokens for `.spra.xz` files. The course-exchange model needs zero-based labels, so translate decoded SPRA words before using that search. Check pipeline status before keeping output.

For an archived collection:

```sh
mkdir -p build/n6
tar -xJf SPRA/words/6/872/872-treelike.tar.xz -C build/n6
# Or stream just one member:
tar -xOJf SPRA/words/6/872/872-treelike.tar.xz 872-treelike/872-00001.txt
```

The original N=8 source package remains in `data/n8/46173/` with its original examples and checksums. Search models and research evidence remain in this parent repository. Only the corpus is supplied by SPRA.

## History cleanup

The old parent `words/` corpus was removed from every local branch's history with `git-filter-repo`. Historical `data/corpus/`, `word.spra`, and `restored.txt` paths were also excluded. Empty corpus-only commits were pruned, changing commit IDs. Experiment models and the original N=8 source package were retained. No history backup was created, as requested; SPRA retains the corpus history.

The rewrite was local. GitHub still has the old branch history until the migration is committed and the rewritten branch is published. After reviewing and committing the migration, publish `main` with an explicit lease against its pre-rewrite head:

```sh
git push --force-with-lease=refs/heads/main:415ed468d50a9962d6fba51e692cb36901413f80 origin main
```

The lease refuses to replace a remote branch that changed in the meantime. Only publish intended branches; `dev` and `reduced_alphabet` were rewritten locally as well. Existing collaborators should use a fresh clone. Fetching or merging old history into a cleaned checkout makes the old corpus reachable again. GitHub's retention of unreachable objects is separate from rewriting branch history.
