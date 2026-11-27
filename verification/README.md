# Verification

Every computation here is exact rational arithmetic, in rational function fields or in rigorous ball arithmetic. The basic field is $\mathbb Q(t,r)$ with $r=\tan(\delta/2)$. The rotation calculation adjoins the rational half-angle variable $a$. Curvature is computed directly from the 2-jets of the metric in the chart of `quadratic_coefficient.chart()`. Section numbers refer to [`../proof/PROOF.md`](../proof/PROOF.md). The derivation notes are [`../proof/DERIVATIONS.md`](../proof/DERIVATIONS.md).

## What each script certifies

| Script | Certifies |
|---|---|
| `full_metric_check.py` | **Part A, Prop. 5.1.** The structure of $V^{(2)}$ for the complete tensors, at every regular pair and every $t$. It is exact at 165 rotations on which polynomials of degree $\le4$ on $SO(3)$ are determined, plus the $t=0$ limits of section 5. It writes `data/quadratic_coefficients.json`.<br>**Part B, Prop. 6.1.** $V^{(2)}=0$ on the equatorial torus, and the exact rotation mean $1/(40000(1+2t)^2)$ of the full cubic coefficient. Checks the fixed-plane conformal response on a basis of all 15 spatial two-jets. |
| `equator_rotation.py` | Recomputes the entire cubic orbit in $\mathbb Q(t,r,a)$, compares all six profile jets with their zero-profile reference and verifies the integer table in Lean. Use `--write` to regenerate the table. |
| `quadratic_lean.py` | Checks the Lean polynomial tables against the Part A export, including the signed sine factors of the fitted vectors and matrices. Use `--write` to regenerate the tables. Lean checks the rational interval bounds in `QuadraticCertificate.lean`. |
| `background_curvature.py` | Computes the full background curvature operator in the longitude-height chart after applying the inverse Cheeger endomorphism. Checks all 36 entries against the table used in the Lean sum-of-squares proof of (Z). |
| `t0_certificate.py` | Prop. 5.2: $V^{(2)}\ge\frac3{10}\rho$ for $0<t\le\frac1{100}$, by ball arithmetic (FLINT `arb`) over $(t,u)\in[0,\frac1{100}]\times[-1,1]$. Other thresholds are passed as arguments, e.g. `python t0_certificate.py 1/60 1/50`. |
| `first_order_weights.py` | The first-order weights $P_t,Q$: the tilt-Hessian asymptotics, regularity of the soft gradients, and $F_0>1$ on $[-1,1]$. |
| `normal_corrections.py` | The normal corrections $M_t,N_t$: the $a,d$ and $b,d$ coefficients vanish, and the $d,d$ limits are $\le\frac14$. |
| `cd_tensor.py` | The tensor $h_{cd}$: the $c,d$ coefficient vanishes, the $c,c$ coefficient vanishes, and the $\lambda_c$ bound. |
| `cubic_cd_channel.py` | The cubic $c\,d^2$ channel on the torus in closed form, for every separation and $t$. |
| `quadratic_coefficient.py` | The $d,d$ weight $1/(4h)$, and agreement with Brendle–Hung at $t=1$ ($0.36893\ldots$). Also shows $t^3V^{(2)}\to-16/25$ for their tensors. |
| `jets.py` | Jet arithmetic and curvature, used by all scripts. As a script, it reproduces the Brendle–Hung cubic integral $\pi^2/(18\sqrt3)$ at $t=1$. |
| `weights_ode.py`, `single_separation_weights.py` | Derivation of the weights (DERIVATIONS.md, sections 1–2). |
| `flint_field.py` | A FLINT implementation of the field $\mathbb Q(t,r)$ with canonical reduced fractions, so that equality is exact. |

Archived verification runs are in [`logs/`](logs).

## Running

```sh
python3 -m venv .venv && . .venv/bin/activate     # from the repository root
pip install -r requirements.txt
cd verification
HOPF_BACKEND=flint python full_metric_check.py   # parts A and B, uses all cores
python t0_certificate.py
python quadratic_lean.py
python background_curvature.py
python equator_rotation.py
HOPF_BACKEND=flint python first_order_weights.py    # and likewise for the others
```

- **Backends.** `HOPF_BACKEND=flint` selects the FLINT backend; without it, SymPy's pure-Python field is used. The rotation-table exporter uses FLINT over three variables. The archived logs use FLINT. With FLINT, `full_metric_check.py` takes about 35 minutes on 8 cores. With SymPy it is several times slower.
- **Directory.** Run `full_metric_check.py` from this directory, because its worker processes import the neighbouring modules.
