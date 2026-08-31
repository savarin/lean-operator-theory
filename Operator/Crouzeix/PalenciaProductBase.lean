/-
# Crouzeix--Palencia assembly with only positive-degree product hypotheses

The sharp product estimate for degree-zero polynomials is proved in
`ProductBase.lean`.  Consequently, the polynomial auxiliary-bound assembly
does not need to assume L4.2e for constants: it suffices to establish the
product bound for polynomials of positive natural degree.

The zero Hilbert space is handled directly.  In a nontrivial Hilbert space,
the closed numerical range is nonempty, so the constant-polynomial theorem
applies with the target control set `closure (numericalRange A)`.

## Main declaration

* `crouzeix_palencia_of_polynomial_auxiliary_bounds_of_pos_natDegree` -- the
  exact `(1 + √2)` spectral-set assembly with L4.2e required only in positive
  degree.
* `crouzeix_palencia_of_polynomial_auxiliary_bounds_of_remainder_induction` --
  the same conclusion from a remainder-to-parent product-bound step.
* `crouzeix_palencia_of_polynomial_auxiliary_bounds_of_normalized_product` --
  the infinite-control-set conclusion from unit-sup-norm product bounds.
-/
import Operator.Crouzeix.Palencia
import Operator.Crouzeix.GeneralSymmetrized
import Operator.Crouzeix.ProductBase
import Operator.Crouzeix.ProductInduction
import Operator.Crouzeix.ProductNormalization

open Complex Polynomial Set
open scoped InnerProductSpace Interval Real

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- If the symmetrized bound holds for every polynomial and the product
bound holds for every positive-degree polynomial, then the full
Crouzeix--Palencia spectral-set conclusion follows.  The raw resolvent Cauchy
identity supplies the omitted constant-polynomial product case. -/
theorem crouzeix_palencia_of_polynomial_auxiliary_bounds_of_pos_natDegree
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (hCauchy : contourIntegral (resolvent A) Omega.boundaryParam =
      (2 * (Real.pi : ℂ) * Complex.I) • (1 : E →L[ℂ] E))
    (hsymm : ∀ p : Polynomial ℂ,
      ‖Polynomial.aeval A p + star (crouzeixPolynomialAuxiliaryOperator A Omega p)‖ ≤
        2 * polynomialSupNorm p (closure (numericalRange A)))
    (hprod : ∀ p : Polynomial ℂ, 0 < p.natDegree →
      ‖Polynomial.aeval A p * crouzeixPolynomialAuxiliaryOperator A Omega p‖ ≤
        polynomialSupNorm p (closure (numericalRange A)) ^ 2) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  apply crouzeix_palencia_of_polynomial_auxiliary_bounds A Omega
  intro p
  refine ⟨hsymm p, ?_⟩
  by_cases hp : p.natDegree = 0
  · rcases subsingleton_or_nontrivial E with hE | hE
    · let _ := hE
      have hzero : Polynomial.aeval A p *
          crouzeixPolynomialAuxiliaryOperator A Omega p = 0 := Subsingleton.elim _ _
      rw [hzero, norm_zero]
      exact sq_nonneg _
    · let _ := hE
      have hnonempty : (closure (numericalRange A)).Nonempty := by
        obtain ⟨x, hx⟩ : (Metric.sphere (0 : E) 1).Nonempty :=
          NormedSpace.sphere_nonempty.mpr zero_le_one
        have hxnorm : ‖x‖ = 1 := by
          rw [Metric.mem_sphere, dist_zero_right] at hx
          exact hx
        have hW : (numericalRange A).Nonempty :=
          ⟨⟪x, A x⟫_ℂ, (mem_numericalRange A _).mpr ⟨x, hxnorm, rfl⟩⟩
        exact hW.mono subset_closure
      exact
        norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_le_polynomialSupNorm_sq_of_natDegree_eq_zero
          A Omega p hnonempty hp hCauchy
  · exact hprod p (Nat.pos_of_ne_zero hp)

/-- The exact Crouzeix--Palencia conclusion follows if the sharp product
bound can be propagated from the strict lower-degree product remainder back
to every positive-degree polynomial.  The landed degree-zero product theorem
and remainder induction principle supply the full product hypothesis.

The propagation step is a genuine additional hypothesis, not a consequence
of remainder product control and the containing-contour geometry alone.  For
the scalar operator `A=0`, an off-center enclosing disk and an affine
polynomial give a constant remainder satisfying its sharp product bound while
the parent product bound fails.  Thus any proof through this connector must
also use compatible global data (such as the all-polynomial symmetrized
hypothesis) in an essential coupled way.  The published Crouzeix--Palencia
proof instead uses the global fourth-power bootstrap exposed in
`Palencia.lean`. -/
theorem crouzeix_palencia_of_polynomial_auxiliary_bounds_of_remainder_induction
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (hCauchy : contourIntegral (resolvent A) Omega.boundaryParam =
      (2 * (Real.pi : ℂ) * Complex.I) • (1 : E →L[ℂ] E))
    (hsymm : ∀ p : Polynomial ℂ,
      ‖Polynomial.aeval A p +
          star (crouzeixPolynomialAuxiliaryOperator A Omega p)‖ ≤
        2 * polynomialSupNorm p (closure (numericalRange A)))
    (hstep : ∀ p : Polynomial ℂ, 0 < p.natDegree →
      ‖Polynomial.aeval A (crouzeixProductRemainderPolynomial Omega p) *
          crouzeixPolynomialAuxiliaryOperator A Omega
            (crouzeixProductRemainderPolynomial Omega p)‖ ≤
        polynomialSupNorm (crouzeixProductRemainderPolynomial Omega p)
            (closure (numericalRange A)) ^ 2 →
      ‖Polynomial.aeval A p *
          crouzeixPolynomialAuxiliaryOperator A Omega p‖ ≤
        polynomialSupNorm p (closure (numericalRange A)) ^ 2) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  let P : Polynomial ℂ → Prop := fun p ↦
    ‖Polynomial.aeval A p *
        crouzeixPolynomialAuxiliaryOperator A Omega p‖ ≤
      polynomialSupNorm p (closure (numericalRange A)) ^ 2
  have hzero : ∀ p : Polynomial ℂ, p.natDegree = 0 → P p := by
    intro p hp
    rcases subsingleton_or_nontrivial E with hE | hE
    · let _ := hE
      have hproductZero : Polynomial.aeval A p *
          crouzeixPolynomialAuxiliaryOperator A Omega p = 0 :=
        Subsingleton.elim _ _
      simp only [P, hproductZero, norm_zero]
      exact sq_nonneg _
    · let _ := hE
      obtain ⟨x, hx⟩ : (Metric.sphere (0 : E) 1).Nonempty :=
        NormedSpace.sphere_nonempty.mpr zero_le_one
      have hxnorm : ‖x‖ = 1 := by
        rw [Metric.mem_sphere, dist_zero_right] at hx
        exact hx
      have hW : (numericalRange A).Nonempty :=
        ⟨⟪x, A x⟫_ℂ, (mem_numericalRange A _).mpr ⟨x, hxnorm, rfl⟩⟩
      change ‖Polynomial.aeval A p *
          crouzeixPolynomialAuxiliaryOperator A Omega p‖ ≤
        polynomialSupNorm p (closure (numericalRange A)) ^ 2
      exact
        norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_le_polynomialSupNorm_sq_of_natDegree_eq_zero
          A Omega p (hW.mono subset_closure) hp hCauchy
  have hall : ∀ p, P p :=
    polynomial_induction_on_crouzeixProductRemainder Omega P hzero (by
      intro p hp hrem
      exact hstep p hp hrem)
  apply crouzeix_palencia_of_polynomial_auxiliary_bounds_of_pos_natDegree
    A Omega hCauchy hsymm
  intro p _
  exact hall p

/-- The exact Crouzeix--Palencia conclusion follows from a
cancellation-preserving remainder induction on unit-vector quadratic forms.
This is strictly weaker than propagating the operator norm of the auxiliary
product: the final C⋆ balance only evaluates that product against one unit
vector. -/
theorem
    crouzeix_palencia_of_polynomial_auxiliary_inner_bounds_of_remainder_induction
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (hCauchy : contourIntegral (resolvent A) Omega.boundaryParam =
      (2 * (Real.pi : ℂ) * Complex.I) • (1 : E →L[ℂ] E))
    (hsymm : ∀ p : Polynomial ℂ,
      ‖Polynomial.aeval A p +
          star (crouzeixPolynomialAuxiliaryOperator A Omega p)‖ ≤
        2 * polynomialSupNorm p (closure (numericalRange A)))
    (hstep : ∀ p : Polynomial ℂ, 0 < p.natDegree →
      (∀ x : E, ‖x‖ = 1 →
        ‖⟪x, (Polynomial.aeval A (crouzeixProductRemainderPolynomial Omega p) *
          crouzeixPolynomialAuxiliaryOperator A Omega
            (crouzeixProductRemainderPolynomial Omega p)) x⟫_ℂ‖ ≤
          polynomialSupNorm (crouzeixProductRemainderPolynomial Omega p)
            (closure (numericalRange A)) ^ 2) →
      ∀ x : E, ‖x‖ = 1 →
        ‖⟪x, (Polynomial.aeval A p *
          crouzeixPolynomialAuxiliaryOperator A Omega p) x⟫_ℂ‖ ≤
          polynomialSupNorm p (closure (numericalRange A)) ^ 2) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  let P : Polynomial ℂ → Prop := fun p ↦
    ∀ x : E, ‖x‖ = 1 →
      ‖⟪x, (Polynomial.aeval A p *
        crouzeixPolynomialAuxiliaryOperator A Omega p) x⟫_ℂ‖ ≤
        polynomialSupNorm p (closure (numericalRange A)) ^ 2
  have hzero : ∀ p : Polynomial ℂ, p.natDegree = 0 → P p := by
    intro p hp
    rcases subsingleton_or_nontrivial E with hE | hE
    · let _ := hE
      intro x _
      have hproductZero : Polynomial.aeval A p *
          crouzeixPolynomialAuxiliaryOperator A Omega p = 0 :=
        Subsingleton.elim _ _
      simp only [hproductZero, zero_apply, inner_zero_right, norm_zero]
      exact sq_nonneg _
    · let _ := hE
      obtain ⟨x, hx⟩ : (Metric.sphere (0 : E) 1).Nonempty :=
        NormedSpace.sphere_nonempty.mpr zero_le_one
      have hxnorm : ‖x‖ = 1 := by
        rw [Metric.mem_sphere, dist_zero_right] at hx
        exact hx
      have hW : (numericalRange A).Nonempty :=
        ⟨⟪x, A x⟫_ℂ, (mem_numericalRange A _).mpr ⟨x, hxnorm, rfl⟩⟩
      have hop :=
        norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_le_polynomialSupNorm_sq_of_natDegree_eq_zero
          A Omega p (hW.mono subset_closure) hp hCauchy
      intro y hy
      calc
        ‖⟪y, (Polynomial.aeval A p *
            crouzeixPolynomialAuxiliaryOperator A Omega p) y⟫_ℂ‖ ≤
          ‖y‖ * ‖(Polynomial.aeval A p *
            crouzeixPolynomialAuxiliaryOperator A Omega p) y‖ :=
              norm_inner_le_norm _ _
        _ ≤ ‖y‖ * (‖Polynomial.aeval A p *
            crouzeixPolynomialAuxiliaryOperator A Omega p‖ * ‖y‖) :=
          mul_le_mul_of_nonneg_left
            ((Polynomial.aeval A p *
              crouzeixPolynomialAuxiliaryOperator A Omega p).le_opNorm y)
            (norm_nonneg y)
        _ ≤ 1 * (polynomialSupNorm p (closure (numericalRange A)) ^ 2 * 1) := by
          rw [hy]
          gcongr
        _ = polynomialSupNorm p (closure (numericalRange A)) ^ 2 := by ring
  have hall : ∀ p, P p :=
    polynomial_induction_on_crouzeixProductRemainder Omega P hzero (by
      intro p hp hrem
      exact hstep p hp hrem)
  apply crouzeix_palencia_of_auxiliary_inner_bounds A
  intro p
  exact ⟨crouzeixPolynomialAuxiliaryOperator A Omega p, hsymm p, hall p⟩

/-- The exact Crouzeix--Palencia conclusion follows from the weakest signed
product invariant used by the final balance: on unit vectors, the real part
of the auxiliary product is bounded below by minus the squared sup norm.
The induction step therefore retains the sign of the separated
square-auxiliary-minus-remainder identity instead of estimating its norm. -/
theorem
    crouzeix_palencia_of_polynomial_auxiliary_re_inner_lower_bounds_of_remainder_induction
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (hCauchy : contourIntegral (resolvent A) Omega.boundaryParam =
      (2 * (Real.pi : ℂ) * Complex.I) • (1 : E →L[ℂ] E))
    (hsymm : ∀ p : Polynomial ℂ,
      ‖Polynomial.aeval A p +
          star (crouzeixPolynomialAuxiliaryOperator A Omega p)‖ ≤
        2 * polynomialSupNorm p (closure (numericalRange A)))
    (hstep : ∀ p : Polynomial ℂ, 0 < p.natDegree →
      (∀ x : E, ‖x‖ = 1 →
        -(polynomialSupNorm (crouzeixProductRemainderPolynomial Omega p)
            (closure (numericalRange A)) ^ 2) ≤
          RCLike.re ⟪x,
            (Polynomial.aeval A (crouzeixProductRemainderPolynomial Omega p) *
              crouzeixPolynomialAuxiliaryOperator A Omega
                (crouzeixProductRemainderPolynomial Omega p)) x⟫_ℂ) →
      ∀ x : E, ‖x‖ = 1 →
        -(polynomialSupNorm p (closure (numericalRange A)) ^ 2) ≤
          RCLike.re ⟪x, (Polynomial.aeval A p *
            crouzeixPolynomialAuxiliaryOperator A Omega p) x⟫_ℂ) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  let P : Polynomial ℂ → Prop := fun p ↦
    ∀ x : E, ‖x‖ = 1 →
      -(polynomialSupNorm p (closure (numericalRange A)) ^ 2) ≤
        RCLike.re ⟪x, (Polynomial.aeval A p *
          crouzeixPolynomialAuxiliaryOperator A Omega p) x⟫_ℂ
  have hzero : ∀ p : Polynomial ℂ, p.natDegree = 0 → P p := by
    intro p hp
    rcases subsingleton_or_nontrivial E with hE | hE
    · let _ := hE
      intro x _
      have hproductZero : Polynomial.aeval A p *
          crouzeixPolynomialAuxiliaryOperator A Omega p = 0 :=
        Subsingleton.elim _ _
      simp only [hproductZero, zero_apply, inner_zero_right, map_zero]
      exact neg_nonpos.mpr (sq_nonneg _)
    · let _ := hE
      obtain ⟨x, hx⟩ : (Metric.sphere (0 : E) 1).Nonempty :=
        NormedSpace.sphere_nonempty.mpr zero_le_one
      have hxnorm : ‖x‖ = 1 := by
        rw [Metric.mem_sphere, dist_zero_right] at hx
        exact hx
      have hW : (numericalRange A).Nonempty :=
        ⟨⟪x, A x⟫_ℂ, (mem_numericalRange A _).mpr ⟨x, hxnorm, rfl⟩⟩
      have hop :=
        norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_le_polynomialSupNorm_sq_of_natDegree_eq_zero
          A Omega p (hW.mono subset_closure) hp hCauchy
      intro y hy
      let T := Polynomial.aeval A p *
        crouzeixPolynomialAuxiliaryOperator A Omega p
      have hinner : ‖⟪y, T y⟫_ℂ‖ ≤
          polynomialSupNorm p (closure (numericalRange A)) ^ 2 := by
        calc
          ‖⟪y, T y⟫_ℂ‖ ≤ ‖y‖ * ‖T y‖ := norm_inner_le_norm _ _
          _ ≤ ‖y‖ * (‖T‖ * ‖y‖) :=
            mul_le_mul_of_nonneg_left (T.le_opNorm y) (norm_nonneg y)
          _ ≤ 1 * (polynomialSupNorm p (closure (numericalRange A)) ^ 2 * 1) := by
            rw [hy]
            gcongr
          _ = polynomialSupNorm p (closure (numericalRange A)) ^ 2 := by ring
      have hreal : -‖⟪y, T y⟫_ℂ‖ ≤ RCLike.re ⟪y, T y⟫_ℂ := by
        have hre := RCLike.re_le_norm (-⟪y, T y⟫_ℂ)
        simp only [map_neg, norm_neg] at hre
        linarith
      exact (neg_le_neg hinner).trans hreal
  have hall : ∀ p, P p :=
    polynomial_induction_on_crouzeixProductRemainder Omega P hzero (by
      intro p hp hrem
      exact hstep p hp hrem)
  apply crouzeix_palencia_of_auxiliary_re_inner_lower_bounds A
  intro p
  exact ⟨crouzeixPolynomialAuxiliaryOperator A Omega p, hsymm p, hall p⟩

/-- A deliberately stronger, diagnostic sufficient condition for the signed
remainder-induction step.  If the evaluated remainder itself has the stated
upper quadratic-form bound, square-auxiliary positivity and the exact identity
`p(A) G_p = SquareAux - R_p(A)` give the required lower product bound.

This standalone remainder bound is not the expected sharp invariant.  In the
centered-disk model with `A = 0` and `p = X`, the parent product is zero while
`SquareAux = 1` and `R_p(A) = 1`; their exact cancellation is essential even
though the sup norm of `p` on `closure (numericalRange A) = {0}` is zero. -/
theorem
    crouzeix_palencia_of_polynomial_auxiliary_remainder_evaluation_upper_bounds
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hCauchy : contourIntegral (resolvent A) Omega.boundaryParam =
      (2 * (Real.pi : ℂ) * Complex.I) • (1 : E →L[ℂ] E))
    (hsymm : ∀ p : Polynomial ℂ,
      ‖Polynomial.aeval A p +
          star (crouzeixPolynomialAuxiliaryOperator A Omega p)‖ ≤
        2 * polynomialSupNorm p (closure (numericalRange A)))
    (hsupport : ∀ t ∈ Set.Ioc (0 : ℝ) (2 * Real.pi),
      ∀ w ∈ numericalRange A,
        ((starRingEnd ℂ) (-Complex.I * deriv Omega.boundaryParam t) *
          (w - Omega.boundaryParam t)).re ≤ 0)
    (hrem : ∀ p : Polynomial ℂ, 0 < p.natDegree →
      ∀ x : E, ‖x‖ = 1 →
        RCLike.re ⟪x,
          Polynomial.aeval A (crouzeixProductRemainderPolynomial Omega p) x⟫_ℂ ≤
            polynomialSupNorm p (closure (numericalRange A)) ^ 2) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  apply
    crouzeix_palencia_of_polynomial_auxiliary_re_inner_lower_bounds_of_remainder_induction
      A Omega hCauchy hsymm
  intro p hp _ x hx
  have hcancel :=
    neg_re_inner_aeval_crouzeixProductRemainderPolynomial_le_re_inner_product
      A Omega p hOmega hsupport x
  exact (neg_le_neg (hrem p hp x hx)).trans hcancel

/-- If the closed numerical range is infinite, exact homogeneity reduces the
remaining positive-degree product hypothesis to polynomials of unit sup norm.
Together with the all-degree symmetrized estimate and the resolvent mass
identity, these normalized bounds imply the exact Crouzeix--Palencia
conclusion. -/
theorem crouzeix_palencia_of_polynomial_auxiliary_bounds_of_normalized_product
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (hKinf : (closure (numericalRange A)).Infinite)
    (hCauchy : contourIntegral (resolvent A) Omega.boundaryParam =
      (2 * (Real.pi : ℂ) * Complex.I) • (1 : E →L[ℂ] E))
    (hsymm : ∀ p : Polynomial ℂ,
      ‖Polynomial.aeval A p +
          star (crouzeixPolynomialAuxiliaryOperator A Omega p)‖ ≤
        2 * polynomialSupNorm p (closure (numericalRange A)))
    (hnormalized : ∀ p : Polynomial ℂ, 0 < p.natDegree →
      polynomialSupNorm p (closure (numericalRange A)) = 1 →
      ‖Polynomial.aeval A p *
          crouzeixPolynomialAuxiliaryOperator A Omega p‖ ≤ 1) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  have hKcompact : IsCompact (closure (numericalRange A)) := by
    have hbounded : Bornology.IsBounded (numericalRange A) :=
      Metric.isBounded_closedBall.subset (fun z hz ↦ by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact norm_le_of_mem_numericalRange A hz)
    exact hbounded.isCompact_closure
  apply crouzeix_palencia_of_polynomial_auxiliary_bounds_of_pos_natDegree
    A Omega hCauchy hsymm
  intro p hp
  exact
    norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_le_of_normalized
      A Omega (closure (numericalRange A)) hKcompact hKinf p hp hnormalized
