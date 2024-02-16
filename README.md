# Playing around with Lean
I formalize the Lemma below, which pertains to an extension of *Decentralized Optimization in Networks with Arbitrary Delays* without assuming bounded gradients, available soon.
```
@article{ortega2024decentralized,
  title={Decentralized Optimization in Networks with Arbitrary Delays},
  author={Ortega, Tomas and Jafarkhani, Hamid},
  journal={arXiv preprint arXiv:2401.11344},
  year={2024}
}
```

**Lemma**
Let us consider two constants $B > 0$, $b > 0$, and non-negative sequences $r_t$ and $e_t$ satisfying

$$
r_{t+1} \leq (1 - \frac{c}{2}) r_t + A \eta^2 + C \eta^2 e_t,
$$

where $r_0 = 0$, $A,C,\eta$ are positive, and $c \in (0,1]$. Then, if $\eta \leq \frac{1}{2} \sqrt{\frac{bc}{BC}}$, it holds that for any integer $T > 0$,

$$
B \sum_{t=0}^{T-1} r_t \leq BA\eta^2 \frac{2}{c} T +  \frac{b}{2} \sum_{t=0}^{T-1} e_t.
$$

**Proof**
First, we recursively apply the statement about $r_{t+1}$ until $t=0$, and obtain

$$
r_{t+1} \leq  A \eta^2 \sum_{s=0}^t (1 - \frac{c}{2})^{t-s} + C \eta^2 \sum_{s=0}^t (1 - \frac{c}{2})^{t-s} e_s.
$$

We bound the first term with the geometric sum bound,

$$
r_{t+1} \leq  A \eta^2 \frac{2}{c} + C \eta^2 \sum_{s=0}^t (1 - \frac{c}{2})^{t-s} e_s,
$$

and we add up the terms for $t = 0, \ldots, T-1$,

$$
\sum_{t=0}^{T-1}r_{t} \leq  T A \eta^2 \frac{2}{c} + C \eta^2 \sum_{t=0}^{T-1} \sum_{s=0}^{t-1} (1 - \frac{c}{2})^{t-1-s} e_s.
$$

A change of variable and a geometric bound yields

$$
\sum_{t=0}^{T-1}r_{t} \leq  T A \eta^2 \frac{2}{c} + C \eta^2 \sum_{t=0}^{T-1} \frac{2}{c} e_t.
$$

Multiplying both sides by $B$, and using that $B C \eta^2 \frac{2}{c} \leq \frac{b}{2}$,
we substitute on the RHS and obtain the Lemma's statement.

