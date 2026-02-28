import os
import re
from datetime import datetime
from pathlib import Path
from typing import Optional, Tuple


def _sanitize_name(name: Optional[str]) -> str:
    if not name:
        return ""
    clean = re.sub(r"[^A-Za-z0-9_]+", "_", name.strip())
    return clean.strip("_")


def _infer_test_set_from_path(path_str: Optional[str]) -> str:
    if not path_str:
        return ""
    parts = Path(path_str).parts
    if "input" in parts:
        idx = parts.index("input")
        if idx + 1 < len(parts):
            return _sanitize_name(parts[idx + 1])
    return ""


def resolve_run_dirs(
    test_set: Optional[str],
    output_dir: Optional[str] = None,
    log_dir: Optional[str] = None,
) -> Tuple[str, str, str, str]:
    """
    Resolve output/log dirs with unified policy:
    - default: output/<test_set>_<timestamp>, log/<test_set>_<timestamp>
    - fallback test_set: tmp
    """
    run_tag = os.environ.get("SAM2INV_RUN_TAG", "").strip() or datetime.now().strftime("%Y%m%d_%H%M%S")
    resolved_test_set = _sanitize_name(test_set) or _sanitize_name(os.environ.get("SAM2INV_TEST_SET", "")) or "tmp"
    resolved_output = output_dir or os.path.join("output", f"{resolved_test_set}_{run_tag}")
    resolved_log = log_dir or os.path.join("log", f"{resolved_test_set}_{run_tag}")
    return resolved_output, resolved_log, resolved_test_set, run_tag


def resolve_verified_output_path(file_path: str) -> str:
    """
    Resolve where syntax/verification snapshots should be written.
    Priority:
    1) env SAM2INV_OUTPUT_DIR
    2) keep existing output/<folder>/ structure if file already under output/
    3) infer dataset from input/<dataset>/ and write output/<dataset>_<timestamp>/
    4) fallback output/tmp_<timestamp>/
    """
    base_name = os.path.basename(file_path)

    forced_output_dir = os.environ.get("SAM2INV_OUTPUT_DIR", "").strip()
    if forced_output_dir:
        os.makedirs(forced_output_dir, exist_ok=True)
        return os.path.join(forced_output_dir, base_name)

    parts = Path(file_path).parts
    if "output" in parts:
        out_idx = parts.index("output")
        if out_idx + 1 < len(parts) - 1:
            output_dir = os.path.join("output", parts[out_idx + 1])
            os.makedirs(output_dir, exist_ok=True)
            return os.path.join(output_dir, base_name)

    inferred_set = _infer_test_set_from_path(file_path) or "tmp"
    run_tag = os.environ.get("SAM2INV_RUN_TAG", "").strip() or datetime.now().strftime("%Y%m%d_%H%M%S")
    output_dir = os.path.join("output", f"{inferred_set}_{run_tag}")
    os.makedirs(output_dir, exist_ok=True)
    return os.path.join(output_dir, base_name)
