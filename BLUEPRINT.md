# Blueprint

Plain-mathematics proof route for unitary power dilation, von
Neumann's polynomial inequality, and the Crouzeix–Palencia
numerical-range bound.

## Target

Three theorems for bounded operators on a complex Hilbert space:

1. Every contraction has a unitary power dilation: an embedding into a
   larger Hilbert space and a unitary whose powers compress back to
   the contraction's powers.

2. For every contraction and complex polynomial, the operator norm of
   the polynomial applied to the contraction is bounded by the
   supremum of the polynomial on the closed unit disk (von Neumann's
   inequality).

3. The closure of the numerical range of every bounded operator is a
   (1 + √2)-polynomial spectral set (Crouzeix–Palencia).

## Proof route

The proof has two chains. Chain A (dilation → von Neumann) is
self-contained. Chain B (numerical range → Crouzeix–Palencia) is
independent of Chain A except that both reuse a shared
spectral-mapping bound for normal operators.

### Chain A — dilation and von Neumann's inequality

**Layer A1 — off-diagonal self-adjoint contraction.** For a contraction
T, the off-diagonal block map a: (x, y) ↦ (Ty, T*x) on E ⊕ E is
self-adjoint (by adjoint symmetry of the two components) and a
contraction (by T's own norm bound).

**Layer A2 — functional-calculus completion to unitary.** The
self-adjoint contraction a from Layer A1 is completed to a unitary via
w = a + i · √(I − a²), where the square root is the continuous
functional calculus applied to the nonneg operator I − a². This is a
general Mathlib fact: every self-adjoint contraction in a C*-algebra
completes to a unitary this way. Composing with the coordinate flip
gives a unitary U on E ⊕ E whose compression to the first summand is
exactly T — for one step only: V*UV = T, but V*U²V ≠ T².

**Layer A3 — Schäffer power dilation.** The power dilation uses a
bilateral repeated-interaction model on ℓ²(ℤ, E ⊕ E). The same
Halmos unitary acts independently at every integer site; a bilateral
shift moves each site's environment output one position to the right.
An induction shows the system component at site 0 after n steps is
exactly Tⁿx, with negative sites staying zero. This gives the genuine
power-compression identity V*UⁿV = Tⁿ for all n ≥ 0.

**Layer A4 — von Neumann's inequality.** Two steps: (a) for a unitary
U in a C*-algebra, p(U) is normal, so ‖p(U)‖ equals its spectral
radius, and spectral mapping gives σ(p(U)) = p(σ(U)) ⊆ p(unit
circle), hence ‖p(U)‖ ≤ sup_{|z|≤1} |p(z)|; (b) linearity converts
the power identity into V*p(U)V = p(T), and compression by a
co-isometry does not increase norm, so
‖p(T)‖ ≤ ‖p(U)‖ ≤ sup_{|z|≤1} |p(z)|.

### Chain B — numerical range and Crouzeix–Palencia

**Layer B1 — numerical range foundations.** The numerical range
W(A) = {⟨x, Ax⟩ : ‖x‖ = 1} is bounded (by ‖A‖), and the
Toeplitz–Hausdorff theorem guarantees it is convex (proved via a
phase-rotation trick reducing to an intermediate-value argument on a
real line segment). The spectrum of A lies in the closure of W(A)
(proved by showing that if z ∉ W̄(A), then A − zI is bounded below
and its adjoint is also bounded below, forcing bijectivity).

**Layer B2 — the auxiliary contour-integral operator.** For a smooth
strictly-convex Jordan domain Ω containing W̄(A), define the auxiliary
operator as a normalized contour integral of the resolvent against a
scalar boundary datum h:

    G_h = (2πi)⁻¹ ∮_{∂Ω} h(σ) · (σI − A)⁻¹ dσ

Specializing h to the conjugate of a polynomial's boundary values
gives the polynomial auxiliary operator.

**Layer B3 — double-layer positivity.** The symmetrized kernel
ν · (σI − A)⁻¹ + (ν · (σI − A)⁻¹)* has nonnegative quadratic form
at any boundary point σ where the outward normal ν satisfies the
supporting-half-plane condition against W(A). This is the classical
double-layer-potential positivity underlying the Crouzeix–Palencia
argument. Integrating this positive kernel yields the sharp
symmetrized estimate:

    ‖p(A) + G_p*‖ ≤ 2 · sup_{∂Ω} |p|

**Layer B4 — scalar companion and Plemelj formula.** A scalar
prototype of the auxiliary operator is analyzed via the classical
Sokhotski–Plemelj jump formula for Cauchy-type boundary integrals,
giving explicit boundary values used to control the product bound.

**Layer B5 — scalar-companion approximation and multiplicative-triple
bound.** A scalar prototype of the auxiliary operator (the scalar
Cauchy companion) is approximated uniformly by polynomials on the
smooth domain, via Mergelyan's theorem (compact convex ⟹ connected
complement ⟹ polynomial approximants). The product bound
‖p(A) G_p p(A)‖ ≤ K · sup³ is established via the multiplicative
triple: submultiplicativity of polynomial sup norms on compact convex
sets, combined with the norm of the auxiliary operator.

**Layer B6 — the algebraic core (Ransford–Schwenninger quartic
bootstrap).** Using the C*-identity ‖F‖⁴ ≤ ‖F + G*‖ · ‖F‖³ +
‖FGF‖ · ‖F‖ with F = p(A) and G = the auxiliary operator, plus the
symmetrized bound (Layer B3) and the multiplicative-triple bound
(Layer B5), produces a quartic inequality in the best constant K:

    K⁴ ≤ 2K³ + K²

Solving algebraically gives K ≤ 1 + √2 exactly. This follows the
Ransford–Schwenninger (2018) short proof, not the original 2017
Crouzeix–Palencia argument.

**Layer B7 — smooth Jordan approximation.** Layers B2–B6 require Ω to
be a smooth strictly-convex Jordan domain. But W̄(A) for a general
operator is merely compact and convex. A large geometric pipeline:
(a) approximates the convex set by a polytope with rounded corners;
(b) proves every full-dimensional finite convex hull has arbitrarily
tight smooth Jordan outer approximations, chosen recursively into a
strict nested exhaustion Ω₀ ⊃ Ω₁ ⊃ ⋯ with ⋂ₙ closure(Ωₙ) = W̄(A); and
(c) invokes Mergelyan's theorem (Layer B5) on every Ωₙ, discharging
the scalar-companion approximation hypothesis at each stage.

The bound produced by Layers B2–B6 is therefore available at every
stage n, in terms of the polynomial sup-norm on closure(Ωₙ). Passing
this to a bound on W̄(A) itself is a separate step, unrelated to
Mergelyan: since the closure(Ωₙ) form a decreasing sequence of compact
sets intersecting to W̄(A), Cantor's intersection theorem together with
the extreme value theorem show the polynomial sup-norms on closure(Ωₙ)
converge to the sup-norm on W̄(A). Feeding this convergence into the
ε-limit form of the Layer B6 balance estimate recovers the bound on
W̄(A) exactly.

**Normal-operator shortcut.** For normal A, the sharp constant 1
(not 1 + √2) follows directly from the spectral mapping theorem in a
C*-algebra — the same spectral-mapping bound that also proves von
Neumann's inequality for unitaries in Chain A.

## Key lemmas

1. **Off-diagonal self-adjoint contraction.** The map (x,y) ↦ (Ty, T*x)
   is self-adjoint and contractive. The starting point for the dilation.

2. **Functional-calculus completion.** a + i√(1 − a²) is unitary for any
   self-adjoint contraction a. Produces the Halmos unitary.

3. **Schäffer power induction.** V*UⁿV = Tⁿ for all n ≥ 0. The
   "power" in power dilation.

4. **Spectral mapping for normal elements.** ‖p(U)‖ =
   sup_{z ∈ σ(U)} |p(z)|. Shared between Chain A (unitaries) and
   Chain B (normal shortcut).

5. **Toeplitz–Hausdorff (convexity of the numerical range).** A
   prerequisite for the entire Chain B geometry.

6. **Spectrum in the closure of the numerical range.** σ(A) ⊆ W̄(A).
   Needed so the smooth Jordan domain encloses the spectrum.

7. **Double-layer positivity.** The nonnegative-quadratic-form
   condition on the symmetrized resolvent kernel. The classical heart
   of Crouzeix–Palencia.

8. **The quartic inequality and its solution.** K⁴ ≤ 2K³ + K² ⟹
   K ≤ 1 + √2. The algebraic core of the bound.

9. **Smooth Jordan outer approximation for polytopes.** The geometric
   reduction that lets the smooth-domain argument apply to a general
   compact convex numerical range.

10. **Polynomial sup-norm convergence along decreasing compacts.** If
    Kₙ is a decreasing sequence of nonempty compact sets, the
    polynomial sup-norms on Kₙ converge to the sup-norm on ⋂ₙ Kₙ, via
    Cantor's intersection theorem and the extreme value theorem. The
    mechanism that passes the Layer B2–B6 bound from each smooth stage
    to W̄(A) itself — distinct from Mergelyan's role in Layer B5.

## Pitfalls

1. **The dilation route is not the textbook one.** The power dilation
   uses a bilateral repeated-interaction/quantum-walk construction,
   not the classical Sz.-Nagy–Foiaș unilateral-shift construction. A
   reader checking against standard references will see a different
   construction.

2. **The Crouzeix–Palencia proof follows Ransford–Schwenninger (2018),
   not the original 2017 argument.** A reader who goes to the original
   paper expecting to match steps will find a different (simpler,
   quartic-inequality-based) argument.

3. **Most of the library is geometric plumbing, not the core
   argument.** The algebraic core (the quartic inequality) is
   comparatively short. Roughly 80% of the Crouzeix–Palencia
   directory is smooth-Jordan-domain approximation apparatus needed
   solely because W̄(A) is merely convex, not smooth, and the
   contour-integral/Plemelj machinery needs smoothness.

4. **Two independent proofs of the normal spectral-mapping bound get
   reused across both chains.** Von Neumann for unitaries (Chain A)
   and the normal-operator sharp-constant-1 shortcut (Chain B) share
   the same lemma. The shared dependency is structural, not
   accidental.

5. **Two distinct approximation steps are easy to conflate.**
   Mergelyan's theorem supplies the polynomial approximants to the
   scalar companion needed at each individual smooth stage Ωₙ
   (Layer B5) — this is where the connected-complement condition is
   load-bearing. The separate passage from "bound on each smooth
   Jordan domain Ωₙ ⊃ W̄(A)" to "bound on W̄(A) itself" is not a second
   application of Mergelyan: it uses convergence of polynomial
   sup-norms along the decreasing compact sequence closure(Ωₙ), via
   Cantor's intersection theorem and the extreme value theorem.
