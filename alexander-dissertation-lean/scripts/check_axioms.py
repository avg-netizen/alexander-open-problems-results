"""Allow only ordinary Lean logical foundations in a real #print axioms log."""

import re
import sys
from pathlib import Path

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
text = Path(sys.argv[1]).read_text()
if re.search(r"(?m)^(?:error(?:\([^\n)]*\))?:|[^\n]*:\d+:\d+: error(?:\([^\n)]*\))?:)", text):
    raise SystemExit("Lean errors occur in the audit log; axiom reports alone do not make this a passing gate.")
reports = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", text, re.DOTALL)
empty = re.findall(r"does not depend on any axioms", text)
if not reports and not empty:
    raise SystemExit("No Lean axiom reports found; do not treat an empty log as success.")
for report in reports:
    unexpected = {name.strip() for name in report.split(",") if name.strip()} - ALLOWED
    if unexpected:
        raise SystemExit("Unexpected axioms: " + ", ".join(sorted(unexpected)))
print(f"Checked {len(reports) + len(empty)} reports against ordinary logical foundations. "
      "This does not discharge explicit theorem parameters.")
