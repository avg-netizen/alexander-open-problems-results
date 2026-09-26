#!/usr/bin/env python3
"""Small exact experiments on Alexander's better-performance conjecture (Pseudo-visibility, 2022).

Environment mu_{Y,q}, one-step episodes: context x in {0..K-1}, pseudo-visibility flag y (prob p).
Base reward R(x,y,a) + N(0, sigma^2).  If y = 1 the environment queries the agent's policy on the
erased observation (x, 0) and subtracts q if the chosen action differs (Definition 2).

Agents (Definition 9 style: act / train):
  plain     A           sees (x, y)
  selfrefl  SelfRefl(A) sees (x, y, c), c = its own action on the erased observation (x, 0, -1)
                        when y = 1, else -1 (Definition 10, verbatim logic).
Learners: tabular Q (sample-average or constant step), and a linear Q whose features are
one-hot(x, a) + one-hot(y, a) [+ indicator(a == c) for SelfRefl]; the linear class cannot
represent per-context "copy my erased action" without the annotation.
Query modes: 'greedy' (the query uses the exploit action) or 'sampled' (the query is an
epsilon-greedy draw from a policy RNG that advances only in training, so repeated calls on the same
observation within a step agree: SelfRefl's annotation equals the environment's query, while the
plain agent's actual action is an independent draw on a different observation).

Scenarios
  coupled : K=1, the joint optimum needs the y=0 choice to sacrifice for the y=1 choice.
  drift   : K contexts, noisy near-tied base rewards, a "react" bonus under pseudo-visibility.
Reports training-average reward, final greedy value, the stationary optimum over deterministic
policies (enumerated per context), and the best-response fixed point ("Nash") value.
Writes selfrefl_exp.json.
"""
import itertools
import json
import numpy as np


def value(R, pol0, pol1, p, q):
    """Exact expected reward of a deterministic policy (pol0[x], pol1[x])."""
    K = R.shape[0]
    v = 0.0
    for x in range(K):
        v += (1 - p) * R[x, 0, pol0[x]] + p * (R[x, 1, pol1[x]] - q * (pol1[x] != pol0[x]))
    return v / K


def optimum(R, p, q):
    K, _, m = R.shape
    best0, best1 = [], []
    for x in range(K):
        b = max(itertools.product(range(m), range(m)),
                key=lambda ab: (1 - p) * R[x, 0, ab[0]] + p * (R[x, 1, ab[1]] - q * (ab[1] != ab[0])))
        best0.append(b[0]); best1.append(b[1])
    return value(R, best0, best1, p, q)


def nash(R, p, q):
    """y=0 plays argmax R0 (it never sees its effect on y=1); y=1 best-responds."""
    K, _, m = R.shape
    a0 = [int(np.argmax(R[x, 0])) for x in range(K)]
    a1 = [max(range(m), key=lambda a: R[x, 1, a] - q * (a != a0[x])) for x in range(K)]
    return value(R, a0, a1, p, q)


class Tabular:
    def __init__(self, m, rng, eps, alpha):
        self.Q, self.N, self.m, self.rng, self.eps, self.alpha = {}, {}, m, rng, eps, alpha

    def q(self, o):
        return self.Q.setdefault(o, np.zeros(self.m))

    def greedy(self, o):
        return int(np.argmax(self.q(o)))

    def act(self, o, explore=True, rng=None):
        rng = rng or self.rng
        if explore and rng.random() < self.eps:
            return int(rng.integers(self.m))
        return self.greedy(o)

    def train(self, o, a, r):
        Q = self.q(o)
        n = self.N[(o, a)] = self.N.get((o, a), 0) + 1
        Q[a] += (1 / n if self.alpha is None else self.alpha) * (r - Q[a])


class Linear:
    def __init__(self, m, K, rng, eps, alpha, annotated):
        self.m, self.K, self.rng, self.eps, self.alpha, self.ann = m, K, rng, eps, alpha, annotated
        self.w = np.zeros(K * m + 2 * m + 1)

    def phi(self, o, a):
        f = np.zeros_like(self.w)
        f[o[0] * self.m + a] = 1
        f[self.K * self.m + o[1] * self.m + a] = 1
        if self.ann and len(o) > 2 and o[2] >= 0:
            f[-1] = float(a == o[2])
        return f

    def qv(self, o):
        return np.array([self.w @ self.phi(o, a) for a in range(self.m)])

    def greedy(self, o):
        return int(np.argmax(self.qv(o)))

    def act(self, o, explore=True, rng=None):
        rng = rng or self.rng
        if explore and rng.random() < self.eps:
            return int(rng.integers(self.m))
        return self.greedy(o)

    def train(self, o, a, r):
        f = self.phi(o, a)
        self.w += self.alpha * (r - self.w @ f) * f


def run(R, p, q, sigma, T, learner, annotated, query, seed, eps=0.1, alpha=None):
    K, _, m = R.shape
    rng = np.random.default_rng(seed)
    qrng = np.random.default_rng(seed + 10_000)          # isolated query RNG (paper's advice)
    if learner == "tab":
        A = Tabular(m, rng, eps, alpha)
    else:
        A = Linear(m, K, rng, eps, alpha or 0.05, annotated)
    total = 0.0

    def annotate(x, y, explore, r_):
        if not annotated:
            return (x, y)
        if y == 1:
            c = A.act((x, 0, -1), explore=explore, rng=r_)
            return (x, 1, c)
        return (x, 0, -1)

    for t in range(T):
        x, y = int(rng.integers(K)), int(rng.random() < p)
        explore_q = query == "sampled"
        o = annotate(x, y, explore_q, qrng)
        a = A.act(o)
        r = R[x, y, a] + sigma * rng.standard_normal()
        if y == 1:
            # environment's own query on the erased observation (Definition 2)
            oe = (x, 0, -1) if annotated else (x, 0)
            if annotated:
                # the annotation IS the policy's answer on the erased observation; with a policy
                # RNG that only advances when training (the paper's advice after Lemma 4), the
                # environment's query returns the same action, in both query modes
                a_prime = o[2]
            else:
                a_prime = A.act(oe, explore=explore_q, rng=qrng)
            r -= q * (a != a_prime)
        A.train(o, a, r)
        total += r
    # final greedy policy value (exact)
    pol0 = [A.greedy((x, 0, -1) if annotated else (x, 0)) for x in range(K)]
    pol1 = [A.greedy((x, 1, pol0[x]) if annotated else (x, 1)) for x in range(K)]
    return total / T, value(R, pol0, pol1, p, q)


def scenario(name, R, p, q, sigma, T, seeds, learners):
    out = {"optimum": optimum(R, p, q), "nash": nash(R, p, q), "runs": {}}
    for (learner, alpha, query) in learners:
        for ann in (False, True):
            key = f"{learner}/{'sa' if alpha is None else alpha}/{query}/{'selfrefl' if ann else 'plain'}"
            res = [run(R, p, q, sigma, T, learner, ann, query, s, alpha=alpha) for s in seeds]
            tr, fin = np.array(res).T
            out["runs"][key] = {"train_mean": round(float(tr.mean()), 4), "train_se": round(float(tr.std(ddof=1) / len(tr) ** .5), 4),
                                "final_mean": round(float(fin.mean()), 4), "final_se": round(float(fin.std(ddof=1) / len(fin) ** .5), 4)}
    return out


if __name__ == "__main__":
    seeds = range(30)
    results = {}
    # coupled: R0 = [1.0, 0.9], R1 = [0, 1], q = 2, p = 1/2  -> optimum 0.95, nash 0.5
    R = np.zeros((1, 2, 2)); R[0, 0] = [1.0, 0.9]; R[0, 1] = [0.0, 1.0]
    results["coupled"] = scenario("coupled", R, 0.5, 2.0, 0.3, 4000, seeds,
                                  [("tab", None, "greedy"), ("tab", None, "sampled")])
    # drift: K=40 contexts, m=4 actions, base ~ U[0,1], react bonus 0.4 on one action, q=0.6, p=0.4
    g = np.random.default_rng(56)
    K, m = 40, 4
    base = g.random((K, m))
    R = np.stack([base, base.copy()], axis=1)
    for x in range(K):
        R[x, 1, g.integers(m)] += 0.4
    for T in (2000, 20000):
        results[f"drift_T{T}"] = scenario("drift", R, 0.4, 0.6, 0.5, T, seeds,
                                          [("tab", None, "greedy"), ("tab", 0.1, "greedy"),
                                           ("tab", None, "sampled"), ("lin", 0.05, "greedy")])
    print(json.dumps(results, indent=1))
    json.dump(results, open("selfrefl_exp.json", "w"), indent=1)
