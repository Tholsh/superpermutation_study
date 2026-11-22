#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
# Copyright (C) 2026 Theo H.
"""Run this record's current C++ RLLB stage before replaying its witness."""
from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[3] / "tools"))
from reproduce_record import main
if __name__ == "__main__":
    main(Path(__file__).with_name("record.json"))
