# The Local Hopf Problem on $S^2\times S^2$

## The problem

The Hopf Problem asks whether $S^2\times S^2$ admits a metric of positive sectional curvature. Brendle and Hung [BH] have constructed such a metric. Bettiol [Be] formulated a local version, which asks for such metrics near the product metric:

> **Local Hopf Problem I** [Be, Introduction]. Is there a sequence $g_n$ of metrics on $S^2\times S^2$ with ${\rm sec}_{g_n}>0$ that converges to the standard product metric?

## Main theorem

Let $g_{\rm prod}$ be the product of two unit round metrics on $M=S^2\times S^2$.

> **Theorem.** There is a sequence of smooth Riemannian metrics on $M$ with strictly positive sectional curvature that converges to $g_{\rm prod}$ in $C^\infty$. In particular, the Local Hopf Problem I has an affirmative answer.

The product metric is nonnegatively curved. Its flat planes are the *mixed* planes $\mathrm{span}\{(X,0),(0,Y)\}$. By Berger's theorem, a variation of the metric cannot make all of them positive at first order. The theorem says that all of them become positive under arbitrarily small smooth changes of $g_{\rm prod}$.

The proof is computer-assisted. Every algebraic identity and inequality it uses is certified by exact rational arithmetic or rigorous ball arithmetic in [`verification/`](../verification). Section 8 lists which script certifies which statement. Section 9 relates the result to earlier work.

### Strategy

We use a two-parameter family of metrics:

1. **Background.** For a Cheeger parameter $t>0$, the background $g_t$ is half the Cheeger deformation of $g_{\rm prod}$ by the diagonal $SO(3)$-action. It has nonnegative curvature, and its flat planes form a compact 4-manifold $Z$ of planes. As $t\to 0$, $2g_t\to g_{\rm prod}$ smoothly.
2. **Perturbation.** Following Brendle and Hung [BH], who used it at $t=1$, we perturb the background: $G_{t,s}=g_t+s\,h^{(1)}+s^2h^{(2)}+s^3h^{(3)}$. Their tensors do not work for small $t$, because the tilt Hessian of the flat planes degenerates like $t^3$. We give tensors that work for all sufficiently small $t$ (section 2).
3. **Reduction.** A perturbation theorem on the bundle of 2-planes (section 3) reduces positivity of $G_{t,s}$ for small $s$ to three conditions:
   - a quadratic growth bound for the background (section 4);
   - a lower bound $\kappa\rho$ on the second-order coefficient $V^{(2)}$ (section 5);
   - positivity of the third-order coefficient on the zero set of $V^{(2)}$, an equatorial torus (section 6).
4. **Limit.** For each fixed $t\in(0,t_0]$, with $t_0=\frac1{100}$, we get positive curvature for $0<s<s_0(t)$. A diagonal sequence $t_j\to0$, $s_j\to 0$ proves the theorem (section 7).

### Notation

- Points of $M$ are $p=(p_1,p_2)$ with $p_i\in S^2\subset\mathbb R^3$, and $u=\langle p_1,p_2\rangle$. A pair is *regular* if $p_1\neq\pm p_2$; otherwise it is coincident or antipodal.
- For $\omega\in\mathbb R^3$ define vector fields $K_\omega=(\omega\times p_1,\ \omega\times p_2)$ (the Killing fields of the diagonal action) and $J_\omega=(\omega\times p_1,\ -\omega\times p_2)$. A superscript $\flat$ lowers an index with $g_t$.
- $\alpha\odot\beta=\tfrac12(\alpha\otimes\beta+\beta\otimes\alpha)$.
- $e_x,e_y,e_z$ is the standard basis of $\mathbb R^3$, and $h=1+2t$.
- $\mathcal N$ is the bundle of tangent 2-planes of $M$, a compact 8-manifold with a fixed Riemannian distance $d_{\mathcal N}$.

---

## 1. The background metric

$P_p$ denotes the orbit tensor $P_p=2I-p_1p_1^{T}-p_2p_2^{T}$, so that $\langle P_p\omega,\omega'\rangle=g_{\rm prod}(K_\omega,K_{\omega'})$. The Cheeger deformation $g_{{\rm CM},t}$ is the metric on $M$ for which
$$(M\times SO(3),\ g_{\rm prod}+Q/t)\longrightarrow M,\qquad (p,q)\mapsto q^{-1}p,$$
is a Riemannian submersion. Here $Q$ is the standard inner product on $\mathfrak{so}(3)=\mathbb R^3$. Explicitly, $g_{{\rm CM},t}(X,Y)=g_{\rm prod}(C_tX,Y)$, where $C_t$ is the identity on horizontal vectors and $C_tK_\omega=K_{(I+tP_p)^{-1}\omega}$. We set
$$g_t=\tfrac12\,g_{{\rm CM},t}.$$
As $t\to0$, $2g_t\to g_{\rm prod}$ in $C^\infty$.

**The flat locus.** Let $Z\subset\mathcal N$ be the set of planes
$$\pi_{b,p}=\mathrm{span}\{(b\times p_1,0),\,(0,b\times p_2)\}=\mathrm{span}\{K_b,J_b\},\qquad |b|=1,\ b\perp p_1,\ b\perp p_2 .$$
- At a regular pair $b=\pm n$, where $n=p_1\times p_2/|p_1\times p_2|$, so there is exactly one such plane.
- At a coincident or antipodal pair, $b$ ranges over a circle.

$Z$ is the image of the compact 4-manifold $\{([n],p_1,p_2): [n]\in\mathbb{RP}^2,\ p_1,p_2\perp n\}$, and the map onto it is an injective immersion:
- The plane determines $n\times p_1$, hence $[n]$, so the map is injective.
- It is an immersion: moving $p$ moves the base point, and moving $[n]$ with $p$ fixed rotates the first factor of the plane.

So $Z$ is a compact embedded submanifold of dimension 4. $C_t$ fixes every plane of $Z$, because:
- $J_b$ is horizontal: $\langle J_b,K_\omega\rangle=(b\cdot\omega-(b\cdot p_1)(\omega\cdot p_1))-(b\cdot\omega-(b\cdot p_2)(\omega\cdot p_2))=0$;
- $P_pb=2b$, so $C_tK_b=K_b/(1+2t)$.

The planes of $Z$ are tangent to the flat, totally geodesic tori $\Gamma\times\Gamma$, where $\Gamma=n^\perp\cap S^2$. On such a torus we use the commuting fields $U$ (simultaneous rotation of $p_1,p_2$ about $n$) and $V$ (opposite rotation). They satisfy $g_t(U,U)=1/h$, $g_t(V,V)=1$ and $g_t(U,V)=0$.

Set $\rho=1-\langle n,e_z\rangle^2$ on $Z$, using the line $[n]$ of each plane. Its zero set
$$\Sigma=\{\rho=0\}$$
is the lift of the equatorial torus $\{p_1,p_2\perp e_z\}$ with its tangent planes.

---

## 2. The perturbation

For $\lambda_c=\tfrac1{100}$ and $\lambda_d=\tfrac1{10}$ let
$$G_{t,s}=g_t+s\,h^{(1)}+s^2h^{(2)}+s^3h^{(3)}.$$
Put $w=p_2-p_1$, $v=p_1+p_2$, $\Delta_{ij}=(p_2\cdot e_i)(p_2\cdot e_j)-(p_1\cdot e_i)(p_1\cdot e_j)$ and $q_4(u)=2u^2-1$.

**First order.** $h^{(1)}=h_a+h_b+\lambda_ch_c+\lambda_dh_d$, where
$$\begin{aligned}
h_a&=P_t(-u)\,K^\flat_{v}\odot K^\flat_{e_x}+Q(-u)\,K^\flat_{w}\odot J^\flat_{e_x}, &
h_c&=K^\flat_{e_z}\odot K^\flat_{e_z},\\
h_b&=P_t(u)\,K^\flat_{w}\odot K^\flat_{e_y}+Q(u)\,K^\flat_{v}\odot J^\flat_{e_y}, &
h_d&=K^\flat_{e_x}\odot J^\flat_{e_z},
\end{aligned}$$
$$P_t(u)=\Big(\tfrac{16}5+\tfrac u2-\tfrac{2u^2}5\Big)\big(1-t^2(1+u)^2\big),\qquad Q(u)=2u^2-\tfrac{7u}{10}-4 .$$

**Second order.**
$$h^{(2)}=h_{aa}+h_{bb}+\lambda_c^2h_{cc}+2\lambda_c(h_{ac}+h_{bc})+\lambda_d^2h_{dd}+2\lambda_d(h_{ad}+h_{bd})+2\lambda_c\lambda_dh_{cd},$$
with
$$\begin{aligned}
h_{aa}&=9f_{aa}(u)\,K^\flat_{e_x}\odot K^\flat_{e_x},\qquad h_{bb}=9f_{bb}(u)\,K^\flat_{e_y}\odot K^\flat_{e_y},\qquad h_{cc}=g_t(K_{e_z},K_{e_z})\,K^\flat_{e_z}\odot K^\flat_{e_z},\\
h_{ac}&=\tfrac1{20}\langle v,e_z\rangle(-5-14u+3q_4)\,K^\flat_{e_x}\odot K^\flat_{e_z},\qquad
h_{bc}=\tfrac1{20}\langle w,e_z\rangle(-5+14u+3q_4)\,K^\flat_{e_y}\odot K^\flat_{e_z},\\
h_{dd}&=\tfrac1{4h}\,g_t(J_{e_x},J_{e_x})\,J^\flat_{e_z}\odot J^\flat_{e_z},\\
h_{ad}&=\tfrac{\langle w,e_x\rangle}{400}(-406-92u+18q_4)\,K^\flat_{e_x}\odot K^\flat_{e_z}+\tfrac{\langle w,e_z\rangle}{200}(-823+154u+9q_4)\,K^\flat_{e_x}\odot K^\flat_{e_x}\\
&\qquad-M_t(u)\langle w,e_x\rangle\,J^\flat_{e_x}\odot J^\flat_{e_z}-N_t(u)\langle w,e_z\rangle\,J^\flat_{e_x}\odot J^\flat_{e_x},\\
h_{bd}&=\tfrac{\langle v,e_x\rangle}{400}(-406+92u+18q_4)\,K^\flat_{e_y}\odot K^\flat_{e_z}+\tfrac{\langle v,e_z\rangle}{200}(-823-154u+9q_4)\,K^\flat_{e_x}\odot K^\flat_{e_y}\\
&\qquad-M_t(-u)\langle v,e_x\rangle\,J^\flat_{e_y}\odot J^\flat_{e_z}-N_t(-u)\langle v,e_z\rangle\,J^\flat_{e_y}\odot J^\flat_{e_x},\\
h_{cd}&=-\tfrac14\big[\varphi_t(u)\,\Delta_{zx}\,J^\flat_{e_z}\odot J^\flat_{e_z}+\psi_t(u)\,\Delta_{zz}\,J^\flat_{e_x}\odot J^\flat_{e_z}\big].
\end{aligned}$$

The scalar profiles are as follows.

- **$f_{aa}$, $f_{bb}$.** With $T_n$ the Chebyshev polynomials, $k=4-\sqrt{15}$ and $(H_1,\dots,H_6)=\big(\tfrac{2203841}{1920},\tfrac{5579141}{153600},\tfrac{214597}{103680},\tfrac{48211}{307200},\tfrac{251}{19200},\tfrac{25}{165888}\big)$:
  $$f_{bb}(u)=\sum_{n=1}^{6}H_nT_n(u)-\tfrac{42025}{6}\sqrt{\tfrac53}\sum_{n\ge1}\frac{k^n}{n^2}T_n(u),\qquad f_{aa}(u)=f_{bb}(-u).$$
  These are the profiles of [BH, §5], where they are written in the angle $\theta$ with $u=\cos2\theta$. The series converge geometrically with all derivatives, so $f_{aa}$ and $f_{bb}$ are smooth functions of $u$ on $[-1,1]$, and the tensors $h_{aa}$, $h_{bb}$ are smooth on $M$.
- **$M_t$, $N_t$.** These are rational functions with denominators $80h^2(1+t(1+u))$ and $80h^2(1+t(1+u))^2$. Their numerator tables are in [`normal_corrections.py`](../verification/normal_corrections.py).
- **$\varphi_t$, $\psi_t$.** With $D=(1+t)^2-t^2u^2\ \ (\ge h)$,
  $$\varphi_t=\frac{(1+t)^2+t^2u^2}{hD^2},\qquad \psi_t=-\frac{(1+t)\big(h^2+6ht^2u^2+t^4(u^4-1)\big)}{h^2D^3}.$$

Every coefficient is a polynomial in $p_1,p_2$ divided by a positive function, so $h^{(1)}$ and $h^{(2)}$ are smooth on $M$. The complete list is implemented in `tensors()` of [`full_metric_check.py`](../verification/full_metric_check.py). [`DERIVATIONS.md`](DERIVATIONS.md) explains how the profiles $P_t,Q,M_t,N_t,\varphi_t,\psi_t$ and the factor $1/(4h)$ were found, and why each is necessary. The third-order tensor $h^{(3)}$ is defined in section 6.

**Relation to [BH].** At $t=1$, $P_1$ and $Q$ differ from the weights of [BH, §5]. Without the $M_t,N_t$ terms and with the [BH] form of $h_{cd}$, the tensors above are those of [BH]. [`DERIVATIONS.md`](DERIVATIONS.md), section 1, shows that the [BH] tensors give a negative quadratic coefficient for small $t$: at a fixed regular pair, $t^3V^{(2)}\to-16/25$ as $t\to0$.

---

## 3. A perturbation theorem on the bundle of planes

Let $\mathcal N$ be a compact manifold with a Riemannian distance $d$, and $Z\subset\mathcal N$ a compact embedded submanifold of codimension $n$. Let $u:\mathcal N\times[0,s_0]\to\mathbb R$ be $C^4$ with
$$u=u_0+s\,u_1+s^2u_2+s^3u_3+O(s^4),$$
where the $u_k$ are $C^4$ and the $O(s^4)$ is uniform on $\mathcal N$. Assume:

- **(H0)** $u_0=0$ on $Z$, and $u_0\ge\sigma\,d(\cdot,Z)^2$ on $\mathcal N$ for some $\sigma>0$;
- **(H1)** $u_1=0$ on $Z$.

**Lemma 3.1 (minimization).** Let $F(z,s)$ be $C^4$ on $\overline B_\delta\times[0,s_0]$, depending on a parameter in a compact set with uniform $C^4$ bounds. Assume $F(0,0)=0$, $F(z,0)\ge\lambda|z|^2$ and $\partial_sF(0,0)=0$. Write $F_k=\partial_s^kF(\cdot,0)/k!$, $H=\nabla^2F_0(0)$, $g=\nabla F_1(0)$ and $\bar z=-H^{-1}g$. Then, uniformly in the parameter,
$$\min_{|z|\le\delta}F(z,s)=s^2W_2+s^3W_3+O(s^4),$$
$$W_2=F_2(0)+\tfrac12 g\cdot\bar z,\qquad W_3=F_3(0)+\nabla F_2(0)\cdot\bar z+\tfrac12\bar z^{T}\nabla^2F_1(0)\bar z+\tfrac16\nabla^3F_0(0)[\bar z,\bar z,\bar z].$$

*Proof.*
1. **Minimizers are $O(s)$.** Since $F_1(z)=O(|z|)$, we have $F(z,s)\ge\lambda|z|^2-Cs|z|-Cs^2$, while $F(0,s)=O(s^2)$. So every minimizer satisfies $|z|\le C's$.
2. **Rescaled expansion.** Put $z=s\zeta$ with $|\zeta|\le C'$. Taylor expansion gives $F(s\zeta,s)=s^2\mathcal Q(\zeta)+s^3\mathcal P(\zeta)+O(s^4)$ uniformly, where $\mathcal Q(\zeta)=W_2+\tfrac12(\zeta-\bar z)^TH(\zeta-\bar z)$ and $\mathcal P(\zeta)=F_3+\nabla F_2\cdot\zeta+\tfrac12\zeta^T\nabla^2F_1\zeta+\tfrac16\nabla^3F_0[\zeta^3]$.
3. **Upper bound.** Taking $\zeta=\bar z$ gives $s^2W_2+s^3\mathcal P(\bar z)+O(s^4)$.
4. **Lower bound.** We have $\mathcal P(\zeta)\ge\mathcal P(\bar z)-C|\zeta-\bar z|$, and $s^2\lambda a^2-Cs^3a\ge-C^2s^4/(4\lambda)$ for every $a$. So the minimum is at least $s^2W_2+s^3\mathcal P(\bar z)-C''s^4$. $\square$

**Definition 3.2.** Fix a tubular map $E(x,w)$ on the normal bundle of $Z$, with $E(x,0)=x$. By (H0), $f(x,w,s)=u(E(x,w),s)$ satisfies the hypotheses of Lemma 3.1 at each $x\in Z$. Let $U_2(x)$ and $U_3(x)$ be the corresponding $W_2,W_3$. They are explicit expressions in derivatives of the $u_k$ at $x$, with a uniformly positive Hessian, so they are continuous on $Z$.

**Lemma 3.3 (chart invariance).** Let $\Omega\subset Z$ be open. Let $\Phi:\Omega\times B\to\mathcal N$ be $C^4$ with $\Phi(y,0)=y$ and $D\Phi(y,0)$ invertible, and let $\Upsilon>0$ be $C^4$. Let $V_2(y),V_3(y)$ be $W_2,W_3$ for $F(z,s)=\Upsilon(y,z)\,u(\Phi(y,z),s)$. Then:
- $V_2=\Upsilon(\cdot,0)\,U_2$ on $\Omega$;
- at points where $U_2=0$ and $dU_2=0$, also $V_3=\Upsilon(\cdot,0)\,U_3$.

*Proof.* Fix $y$ and write $\Upsilon_0=\Upsilon(y,0)$. Let $m(x,s)=\min_wf(x,w,s)$ and $\mathcal M(y',s)=\min_z\Upsilon(y',z)u(\Phi(y',z),s)$. By Lemma 3.1, $m(x,s)=s^2U_2(x)+s^3U_3(x)+O(s^4)$ uniformly in $x$, and $\mathcal M(y',s)=s^2V_2(y')+s^3V_3(y')+O(s^4)$ uniformly for $y'$ near $y$. The minimizers are $O(s)$ in both charts. Since $D\Phi(y,0)$ is invertible, every point near $y$ has the form $\Phi(y',z')=E(x,w)$, with $|y'-y|+|z'|$ comparable to $|x-y|+|w|$.

- **Lower bound.** If $z_s$ minimizes $\mathcal M(y,s)$, write $\Phi(y,z_s)=E(x_s,w_s)$ with $|x_s-y|=O(s)$. Then $\mathcal M(y,s)\ge(\Upsilon_0+O(s))\,m(x_s,s)$.
- **Upper bound.** If $w_s$ minimizes $m(y,s)$, write $E(y,w_s)=\Phi(y'_s,z'_s)$ with $|y'_s-y|=O(s)$. Then $\mathcal M(y'_s,s)\le(\Upsilon_0+O(s))\,m(y,s)$.

**Order $s^2$.** Since $U_2(x_s)=U_2(y)+O(s)$ and $V_2(y'_s)=V_2(y)+O(s)$, the two bounds give $V_2(y)=\Upsilon_0U_2(y)$.

**Order $s^3$.** Now assume $U_2(y)=0$ and $dU_2(y)=0$.
- $U_2(x_s)=O(s^2)$, by the assumption at $y$.
- $V_2(y'_s)=O(s^2)$, because $V_2=\Upsilon U_2$ near $y$.

So the $s^2$ terms are $O(s^4)$. Since $U_3(x_s)=U_3(y)+O(s)$ and $V_3(y'_s)=V_3(y)+O(s)$, the two bounds give $V_3(y)=\Upsilon_0U_3(y)$. $\square$

**Theorem 3.4.** Assume (H0), (H1) and

- **(H2)** there are a continuous $\rho:Z\to[0,\infty)$ and $\kappa>0$ with $U_2\ge\kappa\rho$ on $Z$ and $U_3\ge\kappa$ on $\Sigma=\{\rho=0\}$.

Then $\min_{\mathcal N}u(\cdot,s)>0$ for all sufficiently small $s>0$.

*Proof.* Fix a small $\delta>0$.
1. **Away from $Z$.** Where $d(\cdot,Z)\ge\delta$, we have $u\ge\sigma\delta^2-Cs$.
2. **In the tube.** Every point is $E(x,w)$, and $u(E(x,w),s)\ge m(x,s)\ge s^2U_2(x)+s^3U_3(x)-Cs^4$.
3. **Near $\Sigma$.** On the open set $A=\{U_3>\kappa/2\}\supset\Sigma$, this is at least $s^3\kappa/2-Cs^4$.
4. **On $Z\setminus A$.** This set is compact and disjoint from $\Sigma$, so $\rho\ge\rho_0>0$ there, and the bound is at least $s^2\kappa\rho_0-Cs^3$.

All of these are positive for small $s>0$. $\square$

**How it is applied.** We take $u(\pi,s)=R_{G_{t,s}}(e_1,e_2,e_1,e_2)$ for a $g_t$-orthonormal basis $e_1,e_2$ of $\pi$. This is the curvature with a fixed background area normalization, and its sign is the sign of ${\rm sec}_{G_{t,s}}(\pi)$.
- $\Omega\subset Z$ is the set of planes over regular pairs, which is dense in $Z$.
- $\Phi$ is the *graph chart* $\Phi(y,z)=\mathrm{span}\{U+z_1N_1+z_2N_2,\ V+z_3N_1+z_4N_2\}$ at the base point of $y$, where $N_1,N_2$ span the normal directions to the torus $\Gamma\times\Gamma$. $D\Phi(y,0)$ is invertible because $\Omega$ projects diffeomorphically onto the regular pairs.
- $\Upsilon=|U\wedge V|^2_{g_t}$, so $\Upsilon(\cdot,0)=1/h$.

In this chart $\Upsilon u$ is the curvature numerator on the tilted plane. The verification scripts compute exactly this numerator from the jets of $G_{t,s}$, so their $V^{(2)},V^{(3)}$ are the $V_2,V_3$ of Lemma 3.3.

---

## 4. The background estimate

**Input** (Ziller [Z, Prop. 1.3], after Müter [Mü]). For every $t>0$ and $\xi,\eta\in T_pM$,
$$R_{\rm prod}(\xi,\eta,\xi,\eta)+\tfrac{t^3}4\big|[P\xi_{\mathfrak m},P\eta_{\mathfrak m}]\big|_Q^2\ \le\ R_{{\rm CM},t}(C_t^{-1}\xi,C_t^{-1}\eta,C_t^{-1}\xi,C_t^{-1}\eta).\tag{Z}$$
Here $Q(P\xi_{\mathfrak m},\omega)=g_{\rm prod}(\xi,K_\omega)$ for all $\omega$. Define $a(\xi)=p_1\times\xi_1+p_2\times\xi_2$. Since $g_{\rm prod}(\xi,K_\omega)=\langle a(\xi),\omega\rangle$, we get $P\xi_{\mathfrak m}=a(\xi)$ at every point, including coincident and antipodal pairs, and the bracket is the cross product.

**Lemma 4.1.** Let $t>0$. Suppose $\xi,\eta$ are $g_{\rm prod}$-orthonormal and the right side of (Z) is $<\varepsilon^2$. Then
$$d_{\mathcal N}(\mathrm{span}\{\xi,\eta\},Z)\le C_0(1+t^{-3/2})\,\varepsilon,$$
where $C_0$ is independent of $t$ and $p$.

*Proof.* For $\varepsilon>1/8$ the bound holds once $C_0\ge 8\,{\rm diam}(\mathcal N)$, so let $\varepsilon\le1/8$.
1. **Two bounds from (Z).** For unit spheres, $R_{\rm prod}(\xi,\eta,\xi,\eta)=|\xi_1\wedge\eta_1|^2+|\xi_2\wedge\eta_2|^2$. So (Z) gives $|\xi_1\wedge\eta_1|,|\xi_2\wedge\eta_2|\le\varepsilon$ and $|a(\xi)\times a(\eta)|\le2t^{-3/2}\varepsilon$.
2. **Normal form.** Both bounds depend only on the plane, so we may pass to the orthonormal basis that diagonalizes $X\mapsto|X_1|^2$. Then $\langle\xi_1,\eta_1\rangle=0$, and also $\langle\xi_2,\eta_2\rangle=0$, giving $|\xi_1||\eta_1|\le\varepsilon$ and $|\xi_2||\eta_2|\le\varepsilon$. After possibly interchanging $\xi$ and $\eta$, $|\xi_1|^2\ge\frac12$. Then $|\eta_1|\le\sqrt2\varepsilon$, so $|\eta_2|^2\ge\frac12$ and $|\xi_2|\le\sqrt2\varepsilon$.
3. **Comparison with $Z$.**
   - Let $x=\xi_1/|\xi_1|$ and $y=\eta_2/|\eta_2|$. Then $|\xi-(x,0)|,|\eta-(0,y)|\le2\varepsilon$.
   - Let $b_1=p_1\times x$ and $b_2=p_2\times y$. These are unit vectors with $x=b_1\times p_1$ and $y=b_2\times p_2$.
   - Since $|p\times v|\le|v|$, we get $|a(\xi)-b_1|$, $|a(\eta)-b_2|\le2\varepsilon$, and therefore $|b_1\times b_2|\le(2t^{-3/2}+5)\varepsilon$.
   - So there is $\varsigma=\pm1$ with $|b_2-\varsigma b_1|\le C_1\varepsilon$, where $C_1=\sqrt2(2t^{-3/2}+5)$.
4. **Projection onto $Z$.** Put $b=b_1$. Then $b\perp p_1$ and $|b\cdot p_2|\le C_1\varepsilon$, and we may assume $C_1\varepsilon\le\frac12$. Let $p_2'$ be the normalized projection of $p_2$ onto $b^\perp$, so $|p_2'-p_2|\le2C_1\varepsilon$, and let $y'=b\times p_2'$.
   - The plane $\mathrm{span}\{(b\times p_1,0),(0,b\times p_2')\}$ at $(p_1,p_2')$ lies in $Z$.
   - Its orthonormal basis $(x,0),(0,\varsigma y')$ lies within $(3C_1+2)\varepsilon$ of $(\xi,\eta)$. $\square$

No step uses $p_1\neq\pm p_2$.

**Proposition 4.2 (quadratic growth).** For each $t>0$ there is $\sigma_t>0$ with
$${\rm sec}_{g_t}(\pi)\ge\sigma_t\,d_{\mathcal N}(\pi,Z)^2\qquad\text{on }\mathcal N.$$

*Proof.* The map $\pi\mapsto C_t\pi$ is a diffeomorphism of $\mathcal N$ that fixes $Z$ (section 1); let $L_t$ be a Lipschitz constant of its inverse.
1. Given $\pi$, let $\xi,\eta$ be a $g_{\rm prod}$-orthonormal basis of $C_t\pi$, and let $\nu\ge0$ be the right side of (Z).
2. Lemma 4.1 gives $d(C_t\pi,Z)\le C(t)\sqrt\nu$, so $d(\pi,Z)\le L_tC(t)\sqrt\nu$.
3. The area of $C_t^{-1}\xi\wedge C_t^{-1}\eta$ is bounded by compactness, and ${\rm sec}_{g_t}=2\,{\rm sec}_{g_{{\rm CM},t}}$. Together these give the claim. $\square$

So (H0) holds at every $t>0$, and on $Z$ we also have $u_0=0$. The scripts confirm flatness of the planes of $\Omega$ exactly, at every frame they evaluate.

**Lemma 4.3 (first variation).** For every $t>0$, $u_1=0$ on $Z$.

*Proof.* On a torus $\Gamma\times\Gamma$, the pullback of each first-order tensor is constant.
- The $a,b$ pullbacks vanish, because $p_2\pm p_1$ lies in the plane of $\Gamma$.
- The $c,d$ pullbacks involve only the fixed projections of $e_z,e_x$ onto $n$.

A constant variation of a flat, totally geodesic torus has zero first-order curvature. The scripts assert this vanishing at every frame. By continuity and density it holds on all of $Z$. $\square$

---

## 5. The quadratic coefficient

Fix a regular pair and its torus $\Gamma\times\Gamma$, and write $n_i=\langle n,e_i\rangle$. Let $x',z'$ be the projections of $e_x,e_z$ to the plane of $\Gamma$, and write $V^{(2)}$ for the coefficient $V_2$ in the graph chart.

**Proposition 5.1 (structure).** For every $t>0$ and every regular pair,
$$V^{(2)}=n_x^2\,F^x_t+n_y^2\,F^y_t+\lambda_c\,n_z\big[n_x\,A_t\cdot z'+n_y\,B_t\cdot z'\big]+\lambda_d^2\big[2n_zn_x\,x'^{T}M^1_tz'+n_x^2\,z'^{T}M^2_tz'\big].$$
Here $F^x_t,F^y_t$ (scalars), $A_t,B_t$ (in-plane vectors) and $M^1_t,M^2_t$ ($2\times2$, with $M^2_t$ symmetric) depend only on $t$ and the separation. In particular the $\lambda_d$, $\lambda_c^2$ and $\lambda_c\lambda_d$ parts vanish identically.

- $F^y_t$ is the base value of $V^{(2)}$ when $n=e_y$, and $F^x_t$ the base value when $n=e_x$.
- Both are rational functions of $(t,u)$ plus rational multiples of $f(u)$, $f'(u)$, $f''(u)$ for $f=f_{aa},f_{bb}$.

*Proof.* [`full_metric_check.py`](../verification/full_metric_check.py), part A.
1. Put the pair in a standard frame, with $p_1=(1,0,0)$, $p_2=(\cos\delta,\sin\delta,0)$ and $n=(0,0,1)$. The fixed axes $e_x,e_y,e_z$ are then the columns of a rotation $R$.
2. Write $V^{(2)}$ as a polynomial in $(\lambda_c,\lambda_d)$, keeping the profile jets as free symbols. $V^{(2)}$ is linear in $h^{(2)}$, so this is exact. Each coefficient is computed exactly in $\mathbb Q(t,r)$, where $r=\tan\frac\delta2$.
3. Every claimed identity is a polynomial identity of degree $\le4$ in the entries of $R$, with coefficients in $\mathbb Q(t,r)$: $h^{(1)}$ has degree $\le2$ in the axes and $h^{(2)}$ degree $\le4$.
4. Restricted to $SO(3)$, these polynomials span the matrix coefficients of the representations $V_l$ with $l\le4$, a space of dimension $1+9+25+49+81=165$. The script evaluates at 165 rotations whose evaluation matrix on all 715 monomials of degree $\le 4$ has rank 165. A polynomial of degree $\le4$ that vanishes there vanishes on $SO(3)$.
5. The unknowns $A_t,B_t,M^1_t,M^2_t$ are solved for from some of these rotations. All identities are then exact at all 165. $\square$

At $t=0$ the coefficients have explicit limits. The script and [`first_order_weights.py`](../verification/first_order_weights.py) check them by exact root counting:
- $F^y_0(u)=\tfrac1{400}(1152u^6-400u^5-10400u^4-2956u^3+18544u^2+6920u-4643)-18\,\partial_\delta^2f_{bb}$, and $F^y_0>1$ on $[-1,1]$;
- $F^x_0(u)=F^y_0(-u)$;
- $|A_0|^2+|B_0|^2=\tfrac1{100}(9801-37892u^2+52836u^4-23520u^6)<100$;
- $|M^1_0|_F^2=|M^2_0|_F^2=u^2/8$.

**Proposition 5.2 (lower bound).** For $0<t\le t_0=\tfrac1{100}$ and every regular pair,
$$V^{(2)}\ \ge\ \kappa_2\,\rho,\qquad \kappa_2=\tfrac3{10}.$$

*Proof.* Since $n_x^2+n_y^2=\rho$, $|z'|=\sqrt\rho$ and $|x'|,|n_z|\le1$, Proposition 5.1 gives $V^{(2)}\ge\rho\,\mathcal G(t,u)$, where
$$\mathcal G=\min(F^x_t,F^y_t)-\lambda_c\sqrt{|A_t|^2+|B_t|^2}-\lambda_d^2\big(2|M^1_t|_F+|M^2_t|_F\big).$$
[`t0_certificate.py`](../verification/t0_certificate.py) proves $\mathcal G\ge\kappa_2$ on $[0,t_0]\times[-1,1]$, using the exact coefficient functions written out by part A. It uses rigorous ball arithmetic with adaptive subdivision. The profile jets are enclosed by the mean value theorem, with Markov's inequality $|T_n^{(j)}|\le T_n^{(j)}(1)$ for the derivative bounds and an explicit bound for the geometric tail. The interval $u\in[-1,1]$ includes the coincident and antipodal limits. $\square$

On the equator ($n=\pm e_z$), $\rho=0$ and $V^{(2)}=0$. Since $V^{(2)}\ge0$ is smooth on $\Omega$, its differential also vanishes there. By Lemma 3.3, $U_2=hV^{(2)}$ on $\Omega$. By continuity and density, $U_2\ge h\kappa_2\rho$ on all of $Z$.

The same certificate gives $V^{(2)}\ge\rho/10$ for $t\le\frac1{80}$, $V^{(2)}\ge\rho/20$ for $t\le\frac1{70}$ and $V^{(2)}\ge\rho/50$ for $t\le\frac1{60}$. Sampling the exact $V^{(2)}$ at 72 frames shows that a restriction to small $t$ is necessary. The minimum of $V^{(2)}/\rho$ is $-3.3$ at $t=1/20$, $-0.27$ at $t=1/50$ and $+0.69$ at $t=1/100$.

---

## 6. The cubic coefficient on the equatorial torus

On the equatorial torus $\Sigma$ we have $n=e_z$. Rotating the fixed axes about $e_z$ by an angle $\phi$ is translation along $U$.
- Each first-order tensor carries at most one factor of $e_x$ or $e_y$.
- Each second-order tensor carries at most two.
- $e_z$ is fixed by the rotation.

So $V^{(3)}$ is a trigonometric polynomial of degree $\le3$ in $\phi$, and its mean over $\phi$ equals its average over $\phi\in\{0,\frac\pi2,\pi,\frac{3\pi}2\}$.

**Proposition 6.1.** For every $t>0$ and every separation, the mean of $V^{(3)}$ under $U$-translation is
$$\mu_t=\frac{\lambda_c\lambda_d^2}{4h^2}=\frac1{40000\,h^2}.$$

*Proof.* [`full_metric_check.py`](../verification/full_metric_check.py), part B, uses the complete tensors with the final amplitudes and keeps the profile jets as free symbols. It computes $V^{(3)}$ exactly in $\mathbb Q(t,r)$ at the four rotations and checks two things: the mean is $1/(40000h^2)$, and the profiles $f_{aa},f_{bb}$ contribute zero. The same computation confirms $V^{(2)}=0$ on $\Sigma$. $\square$

The flat coordinates $(U,V)$ of $\Sigma$ are affine in $(\phi,\delta)$, so $\mu_t$ is also the mean of $V^{(3)}$ over $\Sigma$. Two other scripts compute the same coefficient in closed form from the $c\,d^2$ channel alone: [`cubic_cd_channel.py`](../verification/cubic_cd_channel.py) for these tensors, and [`jets.py`](../verification/jets.py) for the [BH] tensors. The torus integral is $\lambda_c\lambda_d^2\pi^2/(2h^{5/2})$. At $t=1$ this is the value $\pi^2/(18\sqrt3)$ found in [BH, Prop. 5.5].

Why only $\lambda_c\lambda_d^2$ survives:
- For $\lambda_d=0$ the metrics are invariant under reflection in the equatorial plane, so $\Sigma$ stays flat and totally geodesic.
- Rotation by $\pi$ reverses the $a$ and $b$ channels.

**The third-order tensor.** By Lemma 3.3, $V^{(3)}=U_3/h$ on $\Sigma\cap\Omega$, where $U_3$ is continuous on $Z$. Since $U_2=0$ and $dU_2=0$ there, $V^{(3)}$ extends smoothly to all of $\Sigma$. Let $\Delta_\Sigma=hU^2+V^2$ be the Laplacian of the flat metric of $\Sigma$, and solve
$$\Delta_\Sigma\chi_t=V^{(3)}-\mu_t,\qquad\int_\Sigma\chi_t=0 .$$
This is solvable because $\mu_t$ is the mean. Extend $\chi_t$ to $M$ with a tubular projection and a cutoff equal to $1$ near $\Sigma$, and set
$$h^{(3)}=2h\,\chi_t\,g_t .$$
To first order, $s^3h^{(3)}$ is the conformal change $e^{2\phi}g_t$ with $\phi=s^3h\chi_t$. On the totally geodesic surface $\Sigma$, the linearized sectional curvature of the tangent plane is therefore $-\Delta\phi$. The cross-terms with the tilt are $O(s^4)$. So the corrected cubic coefficient equals $\mu_t$ on $\Sigma\cap\Omega$, and by continuity $U_3=h\mu_t$ on all of $\Sigma$. The quadratic coefficient is unchanged.

---

## 7. Proof of the main theorem

Fix $t\in(0,t_0]$ and apply Theorem 3.4 to $u(\pi,s)=R_{G_{t,s}}(e_1,e_2,e_1,e_2)$. The hypotheses hold:
- **(H0)** by Proposition 4.2;
- **(H1)** by Lemma 4.3;
- **(H2)** with $\kappa=h\min(\kappa_2,\mu_t)>0$, by Proposition 5.2 and section 6.

So there is $s_0(t)>0$ such that $G_{t,s}$ has positive sectional curvature for $0<s<s_0(t)$.

Now choose $t_j\downarrow0$ in $(0,t_0]$, and for each $j$ choose $0<s_j<\min\{s_0(t_j),1/j\}$ with $\|G_{t_j,s_j}-g_{t_j}\|_{C^j}<1/j$. This is possible because the tensors are smooth at each fixed $t_j$. Since $2g_{t_j}\to g_{\rm prod}$ in $C^\infty$, the metrics $2G_{t_j,s_j}$ have positive sectional curvature and converge to $g_{\rm prod}$ in $C^\infty$. $\blacksquare$

The threshold $s_0(t)$ comes from compactness and is not computed.

---

## 8. Computer verification

| Statement | Certified by |
|---|---|
| Prop. 5.1 (structure of $V^{(2)}$ in general position) | `full_metric_check.py`, part A: exact over $\mathbb Q(t,r)$ at 165 frames on which degree-$\le4$ polynomials on $SO(3)$ are determined |
| $t=0$ limits in section 5, $F_0>1$ | `full_metric_check.py` (part A), `first_order_weights.py`; exact root counts |
| Prop. 5.2 ($V^{(2)}\ge\kappa_2\rho$ for $t\le t_0$) | `t0_certificate.py`; ball arithmetic |
| Prop. 6.1 (cubic mean), $V^{(2)}=0$ on $\Sigma$ | `full_metric_check.py`, part B; exact over $\mathbb Q(t,r)$ |
| Lemma 4.3, flatness of $Z$ | asserted at every frame by `quadratic()` |
| Individual channels: normal corrections, $h_{cd}$, $h_{dd}$, cubic $c\,d^2$ channel | `normal_corrections.py`, `cd_tensor.py`, `quadratic_coefficient.py`, `cubic_cd_channel.py` |
| Agreement with [BH] at $t=1$ ($0.36893\ldots$, $\pi^2/(18\sqrt3)$) | `quadratic_coefficient.py`, `jets.py` |

All curvature coefficients are computed directly from the 2-jets of the metric (Christoffel symbols and the curvature tensor), not from variation formulas. Exact arithmetic runs either in SymPy or in FLINT (`HOPF_BACKEND=flint`). Both implement the same field $\mathbb Q(t,r)$ in canonical form, and every individual script gives identical output under both. The logs were produced with FLINT. See [`verification/README.md`](../verification/README.md).

## 9. Relation to earlier work

**The problem.** Bettiol [Be, Introduction] posed the Local Hopf Problem I and recorded it as unanswered, together with the Hopf Problem I. He proved that metrics satisfying the weaker conditions ${\rm sec}_\theta>0$ exist arbitrarily close to $g_{\rm prod}$ [Be, Ch. 6], [Be2], but such metrics have planes of negative curvature. Brendle and Hung [BH] constructed a metric with ${\rm sec}>0$ on $S^2\times S^2$ by perturbing the fixed Cheeger metric $\frac12g_{{\rm CM},1}$. Their metrics stay a definite distance from $g_{\rm prod}$.

**First-order obstructions.**
- Berger [Ber], as quoted in [BDS1, §1.1]: if a one-parameter family $g(s)$ with $g(0)=g_1\times g_2$ has $\sigma'(0)\ge0$ on all mixed planes, then $\sigma'(0)=0$ there.
- Strake [St1], [St2] (see [Be, §3.4]): metrics with totally geodesic flat tori admit no first-order deformation with positive first variation on all flat planes. This includes $g_{\rm prod}$ and the Cheeger metrics $g_t$.

These do not apply here. The first variation is exactly $0$ on the flat planes (Lemma 4.3), and positivity comes from the second- and third-order coefficients through Theorem 3.4. As [Be, Rem. 3.11] observes, totally geodesic flat tori do not obstruct higher-order deformations.

**Analytic deformations.** Bourguignon, Deschamps and Sentenac [BDS1, §1.3] proved the following:

> Let $(M,g_0)$ be a Riemannian product without infinitesimal isometries. Then no analytic variation $g(s)$ issuing from $g_0$ has positive sectional curvature for all $s\in(0,\varepsilon]$.

This does not apply to the Local Hopf Problem I, for two independent reasons:
- $g_{\rm prod}$ has a six-dimensional isometry group, and [Be, Rem. 3.14] notes that the argument of [BDS1] needs the absence of Killing fields.
- The metrics here form a sequence $2G_{t_j,s_j}$ with two parameters tending to $0$, not an analytic curve issuing from $g_{\rm prod}$.

**Higher-order variations of products.** Bourguignon, Deschamps and Sentenac [BDS2] constructed variations of $g_{\rm prod}$ in which the first nonzero derivative of the curvature of every mixed plane is positive. These variations have no uniform control near the flat planes. They descend to $\mathbb{RP}^2\times\mathbb{RP}^2$, so by Synge's theorem they cannot have ${\rm sec}>0$ [Be, Rem. 3.11]. Here uniform control is provided by Theorem 3.4, and the metrics are not invariant under the simultaneous antipodal map $(p_1,p_2)\mapsto(-p_1,-p_2)$. Indeed, this map commutes with the diagonal action and preserves $K_\omega$ and $J_\omega$, while $p_1+p_2$ and $p_2-p_1$ change sign, so $h_a$ and $h_b$ change sign. This is consistent with Synge's theorem: the quotient of $S^2\times S^2$ by that map is orientable and not simply connected, so it carries no metric of positive curvature.

## References

- **[Be]** R. G. Bettiol, *On different notions of positivity of curvature*, PhD thesis, University of Notre Dame, 2015.
- **[Be2]** R. G. Bettiol, *Positive biorthogonal curvature on $S^2\times S^2$*, arXiv:1210.0043.
- **[Ber]** M. Berger, *Trois remarques sur les variétés riemanniennes à courbure positive*, C. R. Acad. Sci. Paris 263 (1966).
- **[BDS1]** J.-P. Bourguignon, A. Deschamps, P. Sentenac, *Conjecture de H. Hopf sur les produits de variétés*, Ann. Sci. École Norm. Sup. (4) 5 (1972), 277–302.
- **[BDS2]** J.-P. Bourguignon, A. Deschamps, P. Sentenac, *Quelques variations particulières d'un produit de métriques*, Ann. Sci. École Norm. Sup. (4) 6 (1973), 1–16.
- **[BH]** S. Brendle, P.-K. Hung, *A metric on $S^2\times S^2$ with positive sectional curvature*, arXiv:2608.19068.
- **[Mü]** M. Müter, *Krümmungserhöhende Deformationen mittels Gruppenaktionen*, Dissertation, Münster, 1987.
- **[St1]** M. Strake, *Variationen von Metriken nichtnegativer Schnittkrümmung*, Dissertation, Münster, 1986.
- **[St2]** M. Strake, *Curvature increasing metric variations*, Math. Ann. 276 (1987), 633–641.
- **[Z]** W. Ziller, *Examples of Riemannian manifolds with non-negative sectional curvature*, Surveys in Differential Geometry XI (2007), 63–102.
