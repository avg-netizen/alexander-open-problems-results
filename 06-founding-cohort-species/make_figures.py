"""Draw the two genealogies used in the explanatory species paper."""
from pathlib import Path
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

HERE = Path(__file__).resolve().parent
plt.rcParams.update({"font.family": "cmr10", "mathtext.fontset": "cm",
                     "axes.formatter.use_mathtext": True, "font.size": 11})
fig, axes = plt.subplots(1, 2, figsize=(9, 2.9))

def graph(ax, points, edges, founders=(), label_right=False):
    for a,b in edges:
        ax.annotate("", points[b], points[a],
                    arrowprops={"arrowstyle": "->", "color": "0.4",
                                "shrinkA": 9, "shrinkB": 9})
    for name,(x,y) in points.items():
        ax.scatter([x],[y],s=105,color="#ab3b35" if name in founders else "#325c83",zorder=3)
        if label_right:
            ax.text(x+.16,y+.15,"$"+name+"$",ha="left",va="center")
        else:
            ax.text(x,y-0.26,"$"+name+"$",ha="center",va="top")
    ax.set_xlim(-.35,max(x for x,y in points.values())+.5)
    ax.set_ylim(-.6,max(y for x,y in points.values())+.65)
    ax.axis("off")

points={"a_0":(0,0),"a_1":(1,0),"a_2":(2,0),"b":(2.3,1),"c_0":(3.2,0),"c_1":(4.2,0)}
graph(axes[0],points,[("a_0","a_1"),("a_1","a_2"),("a_2","c_0"),("b","c_0"),("c_0","c_1")],["a_0","b"])
axes[0].plot([4.46,4.55,4.64],[0,0,0],".",color="0.25",markersize=2)
axes[0].set_title("A founder can arrive late",pad=12)
points={"b_0":(0,1.3),"b_1":(1.7,1.3),"b_2":(3.4,1.3),
        "a_0":(0,.3),"a_1":(1.7,.3),"a_2":(3.4,.3)}
graph(axes[1],points,[("b_0","b_1"),("b_1","b_2"),
                     ("b_0","a_0"),("b_1","a_1"),("b_2","a_2")],label_right=True)
axes[1].plot([3.70,3.78,3.86],[1.3,1.3,1.3],".",color="0.25",markersize=2)
for x in [0,1.7,3.4]:
    axes[1].annotate("",(x,-.35),(x,.13),arrowprops={"arrowstyle":"->","color":"0.4"})
    axes[1].plot([x,x,x],[-.46,-.54,-.62],".",color="0.25",markersize=2)
axes[1].set_ylim(-.8,1.95)
axes[1].set_title("One side chain per input row",pad=12)
fig.tight_layout()
(HERE/"figures").mkdir(exist_ok=True)
fig.savefig(HERE/"figures/founders-and-backbone.pdf",bbox_inches="tight",
            metadata={"CreationDate":None,"ModDate":None})
