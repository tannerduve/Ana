#!/usr/bin/env python3
"""Coq artifact-audit negative fixtures, using the pinned official task image."""
import json
from pathlib import Path
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "runner"))
import public_bench as runner


def main():
    lock = json.loads((ROOT / "public-lock.json").read_text())
    task = next(t for t in runner.tasks(lock) if t["id"] == "prove-plus-comm")
    # Tests stay offline: docker create otherwise pulls an absent image.
    runner.docker("image", "inspect", task["image_digest"])
    container = runner.create_container(task["image_digest"], workspace=task["workspace"])
    try:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            fixtures = [
                ("valid", "Require Import Arith.\nTheorem plus_comm : forall n m : nat, n+m=m+n.\n"
                 "Proof. apply Nat.add_comm. Qed.\n", True),
                ("comment_spoof", "(* Theorem plus_comm : forall n m : nat, n+m=m+n. *)\n"
                 "Theorem plus_comm : True. Proof. exact I. Qed.\n", False),
                ("admitted", "Theorem plus_comm : forall n m : nat, n+m=m+n. Admitted.\n", False),
            ]
            for name, source, expected in fixtures:
                path = root / "plus_comm.v"
                path.write_text(source)
                runner.docker("cp", path, container + ":/workspace/plus_comm.v")
                runner.docker("exec", container, "coqc", "plus_comm.v")
                output = root / name
                output.mkdir()
                actual = runner.coq_audit(container, output, task["workspace"])
                assert actual["passed"] == expected, (name, actual)
        print("3 Coq artifact-audit fixtures passed (valid, changed type, admitted proof)")
    finally:
        runner.remove_container(container)


if __name__ == "__main__":
    main()
