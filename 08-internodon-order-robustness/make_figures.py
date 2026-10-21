"""Draw the swap example and plot the unchanged saved co-membership record."""
from pathlib import Path
import json
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

HERE = Path(__file__).resolve().parent
OUT = HERE/"figures"
OUT.mkdir(exist_ok=True)
plt.rcParams.update({"font.family":"cmr10","mathtext.fontset":"cm",
                     "axes.formatter.use_mathtext":True,"font.size":11})
metadata={"CreationDate":None,"ModDate":None}
fig,axes=plt.subplots(1,3,figsize=(8,2.6))
cases=[
    ("Genealogy",{"u":(0,1),"v":(1.4,1),"z":(.7,0)},[("u","z"),("v","z")]),
    ("Order u, v, z",{"u":(.7,1.4),"v":(.7,.7),"z":(.7,0)},[("u","v"),("v","z")]),
    ("Order v, u, z",{"v":(.7,1.4),"u":(.7,.7),"z":(.7,0)},[("v","u"),("u","z")])]
for ax,(title,pts,edges) in zip(axes,cases):
    for a,b in edges:
        ax.annotate("",pts[b],pts[a],arrowprops={"arrowstyle":"->","shrinkA":10,"shrinkB":10,"color":"0.4"})
    for name,(x,y) in pts.items():
        ax.scatter([x],[y],s=130,color="#325c83",zorder=3)
        ax.text(x+.15,y,"$"+name+"$",va="center")
    ax.set_xlim(-.4,2);ax.set_ylim(-.3,1.7);ax.axis("off");ax.set_title(title)
fig.tight_layout()
fig.savefig(OUT/"adjacent-swap.pdf",bbox_inches="tight",metadata=metadata)
plt.close(fig)
data=json.loads((HERE/"comembership-check.json").read_text())["rows"]
fig,ax=plt.subplots(figsize=(6.8,3.4))
x=list(range(len(data)))
for shift,key,label,color in [
    (-.18,"all_pairs_changed","All organism pairs","#6588a9"),
    (.18,"co_member_pairs_lost","Reference co-member pairs","#ab3b35")]:
    values=[100*r[key] for r in data]
    bars=ax.bar([i+shift for i in x],values,width=.34,label=label,color=color)
    for bar,value in zip(bars,values):
        ax.text(bar.get_x()+bar.get_width()/2,value+.9,f"{value:.1f}",ha="center",fontsize=10)
ax.set_xticks(x,[f"N={r['N']}, p={r['sex']:g}" for r in data])
ax.set_ylabel("Disagreement or loss (percent)")
ax.set_ylim(0,100)
ax.spines[["top","right"]].set_visible(False)
ax.legend(frameon=False,loc="upper left")
fig.tight_layout()
fig.savefig(OUT/"co-membership-metrics.pdf",bbox_inches="tight",metadata=metadata)
