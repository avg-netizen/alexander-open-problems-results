"""Illustrate the successful branch of the signed quitting construction."""
import os
from pathlib import Path
import tempfile

os.environ.setdefault("MPLCONFIGDIR", str(Path(tempfile.gettempdir()) / "alexander-explanatory-mpl"))
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

HERE = Path(__file__).resolve().parent
plt.rcParams.update({"font.family": "cmr10", "mathtext.fontset": "cm",
                     "axes.formatter.use_mathtext": True, "font.size": 11})
fig, axes = plt.subplots(1, 2, figsize=(8, 2.9), sharex=True)
t = list(range(5))
for ax, sign, title in zip(axes, (1, -1), ("Positive environment", "Reward dual")):
    a = [sign*x for x in (0, 1, 2, 3, 4 if sign == 1 else 3)]
    q = [sign*x for x in (0, 1, 2, 3, 3)]
    ax.step(t, a, where="post", color="#325c83", label="Original A", linewidth=2)
    ax.step(t, q, where="post", color="#ab3b35", label="Quitter / Q", linestyle="--", linewidth=2)
    ax.scatter(t, a, color="#325c83", s=12)
    ax.set_xticks(t)
    ax.set_yticks(range(0, 5) if sign == 1 else range(-4, 1))
    ax.set_title(title)
    ax.set_xlabel("Reward opportunity after initial flag")
    ax.spines[["top", "right"]].set_visible(False)
axes[0].set_ylabel("Cumulative reward")
axes[0].legend(frameon=False, loc="upper left")
fig.suptitle("Successful branch: K = 3, L = 4, probability 1/4", y=1.04)
fig.tight_layout()
(HERE / "figures").mkdir(exist_ok=True)
fig.savefig(HERE / "figures/rare-branch.pdf", bbox_inches="tight",
            metadata={"CreationDate": None, "ModDate": None})
