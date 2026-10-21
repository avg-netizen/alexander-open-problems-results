"""Plot final-policy values from the unchanged saved experiment record."""
import json
import os
from pathlib import Path
import tempfile

os.environ.setdefault("MPLCONFIGDIR", str(Path(tempfile.gettempdir()) / "alexander-explanatory-mpl"))
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

HERE = Path(__file__).resolve().parent
DATA = HERE.parent / "09-further-results/pseudovisibility/selfrefl_exp.json"
rows = json.loads(DATA.read_text())
plt.rcParams.update({"font.family": "cmr10", "mathtext.fontset": "cm",
                     "axes.formatter.use_mathtext": True, "font.size": 11})
fig, axes = plt.subplots(1, 2, figsize=(8, 3.4), sharey=True)
for ax, horizon in zip(axes, (2000, 20000)):
    record = rows[f"drift_T{horizon}"]
    for shift, arm, label, color in [
        (-.17, "plain", "Plain", "#325c83"),
        (.17, "selfrefl", "Annotated", "#ab3b35"),
    ]:
        entries = [record["runs"][f"{base}/{arm}"]
                   for base in ("tab/sa/greedy", "lin/0.05/greedy")]
        ax.bar([shift, 1+shift], [x["final_mean"] for x in entries],
               yerr=[x["final_se"] for x in entries], width=.32,
               label=label, color=color, capsize=3)
    ax.axhline(record["optimum"], color="0.35", linestyle="--", linewidth=1)
    ax.set_xticks([0, 1], ["Tabular", "Linear"])
    ax.set_title(f"{horizon:,} episodes")
    ax.set_ylim(0, 1)
    ax.spines[["top", "right"]].set_visible(False)
axes[0].set_ylabel("Final greedy policy value")
fig.legend(*axes[0].get_legend_handles_labels(), frameon=False,
           loc="upper center", bbox_to_anchor=(.5, 1.10), ncol=2)
fig.tight_layout()
(HERE / "figures").mkdir(exist_ok=True)
fig.savefig(HERE / "figures/final-values.pdf", bbox_inches="tight",
            metadata={"CreationDate": None, "ModDate": None})
