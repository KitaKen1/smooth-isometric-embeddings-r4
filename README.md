# Smooth Isometric Embeddings of Closed Orientable Surfaces in Four-Space

The smooth isometric embedding problem for closed orientable surfaces in Euclidean four-space asks for the following statement.

> [!NOTE]
> **Conjecture (Smooth isometric embeddings in four-space).**
>
> For every closed orientable smooth surface $M$ and every smooth Riemannian metric $g$ on $M$, there exists a smooth embedding
>
> $$
> f:M\hookrightarrow\mathbb R^4
> $$
>
> such that
>
> $$
> \langle df_p(v),df_p(w)\rangle=g_p(v,w)
> \qquad(p\in M,\ v,w\in T_pM).
> $$

Here closed means compact without boundary, and smooth means $C^\infty$. No curvature restriction is imposed. The embedding must be globally injective, and the isometry condition is the pullback identity $f^*\delta_4=g$.

This repository presents a proposed proof of this conjecture. A proof sketch follows; the [PDF manuscript](PDF/smooth-isometric-embeddings-r4.pdf) contains the detailed proof.

## Proof sketch

### 1. Decompose the metric change into primitive additions

Start from a smooth embedding of $M$ into $S^3$ and scale it to obtain $F^0:M\hookrightarrow\mathbb R^4$ with $\gamma^0=(F^0)^*\delta_4<g$. Prepare a finite sequence of metrics

$$
\gamma^j=\gamma^0+\sum_{i=1}^j a_i^2\,dx_i^2,
\qquad \gamma^K=g.
$$

Each addition is supported on a coordinate disk. The phases are chosen so that

$$
\mathrm{Hess}_{\gamma^{j-1}}x_j(\partial_{y_j},\partial_{y_j})>0.
$$

The task is to realize each addition while preserving the embedding and the conditions needed for the next step.

### 2. Identify a plane transverse to the old surface

For the current embedding $F$, define

$$
P_p=\mathrm{span}(F_y(p),F_{yy}(p))^\perp.
$$

The decomposition

$$
F_{yy}=\Gamma^x_{yy}F_x+\Gamma^y_{yy}F_y+B_{yy},
\qquad
\Gamma^x_{yy}=-\mathrm{Hess}_{\gamma(F)}x(\partial_y,\partial_y)\ne0
$$

shows that $P_p$ is a complement to $dF_p(T_pM)$. The leading derivative oscillation of a primitive correction lies in $P$.

### 3. Cancel the derivative oscillation with a tubular projection

Extend $P$ to a global complement $E$ along $F$, and let $H$ be the tubular retraction along $E$. The exact corrected maps satisfy

$$
f_z\to F\text{ in }C^0,
\qquad df_z-dF=W_z+R_z,
\qquad \|R_z\|_{C^0}\to0,
$$

where $W_z$ takes values in $E$ and $df_z$ is uniformly bounded. Since $DH_F$ annihilates $E$,

$$
d(H\circ f_z)-dF
=(DH_{f_z}-DH_F)df_z+DH_F R_z\longrightarrow0.
$$

Thus $H\circ f_z\to F$ in $C^1$. For small $z$, the composition is an embedding, which forces $f_z$ itself to be an embedding.

### 4. Retain the exact metric and the later boundary conditions

**The projection is only used to prove injectivity.** The final map is the exact corrected map $f_z$, whose induced metric is

$$
f_z^*\delta_4=\gamma(F)+a^2\,dx^2.
$$

The boundary conditions for subsequent additions hold for these same maps after adjusting the preferred normal fields. The scale can be chosen small enough to meet both requirements.

### 5. Complete the finite construction

The spherical preparation is taken sufficiently $C^1$ close to the starting embedding to preserve injectivity. Apply the embedding-preserving primitive step successively along the prepared metric sequence.

After finitely many steps, the resulting smooth embedding $F^K$ satisfies $(F^K)^*\delta_4=g$. For a disconnected surface, construct the embeddings componentwise and separate their compact images by translations.

## Detailed manuscript

- [PDF manuscript](PDF/smooth-isometric-embeddings-r4.pdf)

Public draft 1, 9 October 2026.
