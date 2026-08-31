/-
# Obstruction to uncoupled Crouzeix product-remainder induction

The strict degree descent of `crouzeixProductRemainderPolynomial` does not by
itself propagate either of the sharp product estimates needed by the
Crouzeix--Palencia balance.  This file records a concrete scalar
counterexample on an off-center disk.

Take `A = 0` on `ℂ`, the disk `ball 4 5`, and `p = X - 1`.  The disk contains
the closed numerical range and satisfies the resolvent Cauchy mass identity.
The product remainder has degree zero, so its sharp product bound follows
from the landed base case.  Nevertheless, the parent auxiliary is `3 I`
while `p(A) = -I` and the sup norm of `p` on `closure W(A) = {0}` is one.
Thus the parent product is `-3 I`: its norm exceeds one and its quadratic
real part at the unit vector `1` is below `-1`.

Any successful induction invariant must therefore retain additional coupled
data from the parent square-auxiliary term; lower-degree product control and
containing Cauchy geometry alone are insufficient.

## Main declaration

* `exists_crouzeixProductRemainder_bound_but_parent_bounds_fail` -- a valid
  positive-degree Cauchy-contour example whose remainder satisfies the sharp
  norm product bound while both the parent norm bound and the weaker signed
  quadratic-form bound fail.
* `exists_smooth_convex_cauchy_support_product_bound_fails` -- the same
  witness proves that the literal fixed-domain product inequality itself is
  false even under full polynomial Cauchy reproduction, outward support, and
  the sharp symmetrized bound for the witness polynomial; it also records
  explicitly that the universal symmetrized family fails on this domain.
-/
import Operator.Crouzeix.AffineAuxiliary
import Operator.Crouzeix.PalenciaProductBase
import Operator.Crouzeix.PolynomialCauchyFromResolventMass

open Complex Polynomial Set
open scoped InnerProductSpace Interval Real

noncomputable section

private def productInductionObstructionOperator : ℂ →L[ℂ] ℂ := 0

private def productInductionObstructionDomain : SmoothJordanDomain :=
  SmoothJordanDomain.ball 4 5 (by norm_num)

private def productInductionObstructionPolynomial : Polynomial ℂ :=
  Polynomial.X - Polynomial.C 1

private theorem productInductionObstruction_norm_sub_center :
    ‖productInductionObstructionOperator -
        (4 : ℂ) • (1 : ℂ →L[ℂ] ℂ)‖ < 5 := by
  unfold productInductionObstructionOperator
  rw [zero_sub, norm_neg, norm_smul, norm_one]
  norm_num

private theorem productInductionObstruction_numericalRange :
    numericalRange productInductionObstructionOperator = {0} := by
  ext z
  constructor
  · intro hz
    obtain ⟨x, _hx, rfl⟩ :=
      (mem_numericalRange productInductionObstructionOperator _).mp hz
    simp only [productInductionObstructionOperator, zero_apply,
      inner_zero_right, Set.mem_singleton_iff]
  · intro hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    apply (mem_numericalRange productInductionObstructionOperator 0).mpr
    refine ⟨1, norm_one, ?_⟩
    simp only [productInductionObstructionOperator, zero_apply,
      inner_zero_right]

private theorem productInductionObstruction_contained :
    closure (numericalRange productInductionObstructionOperator) ⊆
      productInductionObstructionDomain.carrier := by
  rw [productInductionObstruction_numericalRange, closure_singleton]
  intro z hz
  rw [Set.mem_singleton_iff] at hz
  subst z
  change (0 : ℂ) ∈ Metric.ball 4 5
  rw [Metric.mem_ball]
  norm_num

private theorem productInductionObstruction_supNorm :
    polynomialSupNorm productInductionObstructionPolynomial
      (closure (numericalRange productInductionObstructionOperator)) = 1 := by
  rw [productInductionObstruction_numericalRange, closure_singleton]
  apply le_antisymm
  · unfold polynomialSupNorm
    refine Real.iSup_le (fun z => ?_) zero_le_one
    refine Real.iSup_le (fun hz => ?_) zero_le_one
    rw [Set.mem_singleton_iff] at hz
    subst z
    simp only [productInductionObstructionPolynomial, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C]
    norm_num
  · have hlower := norm_eval_le_polynomialSupNorm
      productInductionObstructionPolynomial
      (bddAbove_norm_eval_image_of_isCompact
        productInductionObstructionPolynomial isCompact_singleton)
      (show (0 : ℂ) ∈ ({0} : Set ℂ) by exact Set.mem_singleton 0)
    simpa only [productInductionObstructionPolynomial, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C, zero_sub, norm_neg, norm_one]
      using hlower

private theorem productInductionObstruction_aeval :
    Polynomial.aeval productInductionObstructionOperator
        productInductionObstructionPolynomial =
      (-1 : ℂ) • (1 : ℂ →L[ℂ] ℂ) := by
  unfold productInductionObstructionOperator
    productInductionObstructionPolynomial
  rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
    Algebra.algebraMap_eq_smul_one]
  module

private theorem productInductionObstruction_auxiliary :
    crouzeixPolynomialAuxiliaryOperator productInductionObstructionOperator
        productInductionObstructionDomain
        productInductionObstructionPolynomial =
      (3 : ℂ) • (1 : ℂ →L[ℂ] ℂ) := by
  change crouzeixPolynomialAuxiliaryOperator
      productInductionObstructionOperator
      (SmoothJordanDomain.ball 4 5 _)
      productInductionObstructionPolynomial = _
  rw [crouzeixPolynomialAuxiliaryOperator_ball_center_eq_eval_center_smul_one
    productInductionObstructionOperator 4
      productInductionObstruction_norm_sub_center
      productInductionObstructionPolynomial]
  unfold productInductionObstructionPolynomial
  norm_num

private theorem productInductionObstruction_degree :
    productInductionObstructionPolynomial.natDegree = 1 := by
  unfold productInductionObstructionPolynomial
  rw [Polynomial.natDegree_sub_C, Polynomial.natDegree_X]

private theorem productInductionObstruction_cauchy :
    contourIntegral (resolvent productInductionObstructionOperator)
        productInductionObstructionDomain.boundaryParam =
      (2 * (Real.pi : ℂ) * Complex.I) • (1 : ℂ →L[ℂ] ℂ) := by
  rw [show productInductionObstructionDomain.boundaryParam =
      circleMap 4 5 by rfl, contourIntegral_circleMap]
  exact
    circleIntegral_resolvent_eq_two_pi_I_smul_one_of_norm_sub_smul_one_lt
      productInductionObstructionOperator 4
        productInductionObstruction_norm_sub_center

private theorem productInductionObstruction_remainder_bound :
    ‖Polynomial.aeval productInductionObstructionOperator
          (crouzeixProductRemainderPolynomial
            productInductionObstructionDomain
            productInductionObstructionPolynomial) *
        crouzeixPolynomialAuxiliaryOperator
          productInductionObstructionOperator
          productInductionObstructionDomain
          (crouzeixProductRemainderPolynomial
            productInductionObstructionDomain
            productInductionObstructionPolynomial)‖ ≤
      polynomialSupNorm
          (crouzeixProductRemainderPolynomial
            productInductionObstructionDomain
            productInductionObstructionPolynomial)
          (closure (numericalRange productInductionObstructionOperator)) ^ 2 := by
  have hp : 0 < productInductionObstructionPolynomial.natDegree := by
    rw [productInductionObstruction_degree]
    norm_num
  have hrdeg :
      (crouzeixProductRemainderPolynomial
        productInductionObstructionDomain
        productInductionObstructionPolynomial).natDegree = 0 := by
    have hlt := natDegree_crouzeixProductRemainderPolynomial_lt
      productInductionObstructionDomain
      productInductionObstructionPolynomial hp
    rw [productInductionObstruction_degree] at hlt
    exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hlt)
  have hK :
      (closure
        (numericalRange productInductionObstructionOperator)).Nonempty := by
    rw [productInductionObstruction_numericalRange, closure_singleton]
    exact Set.singleton_nonempty 0
  exact
    norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_le_polynomialSupNorm_sq_of_natDegree_eq_zero
      productInductionObstructionOperator
      productInductionObstructionDomain
      (crouzeixProductRemainderPolynomial
        productInductionObstructionDomain
        productInductionObstructionPolynomial)
      hK hrdeg productInductionObstruction_cauchy

/-- Sharp control of the strict product remainder does not force either the
parent norm product bound or even the weaker signed real-inner lower bound.

The witness also has the expected containing-domain and resolvent-mass
hypotheses, so this rules out an uncoupled induction from remainder product
control plus Cauchy geometry.  It does not rule out an invariant carrying
additional parent/remainder cancellation data. -/
theorem exists_crouzeixProductRemainder_bound_but_parent_bounds_fail :
    ∃ (A : ℂ →L[ℂ] ℂ) (Omega : SmoothJordanDomain) (p : Polynomial ℂ),
      closure (numericalRange A) ⊆ Omega.carrier ∧
      contourIntegral (resolvent A) Omega.boundaryParam =
        (2 * (Real.pi : ℂ) * Complex.I) • (1 : ℂ →L[ℂ] ℂ) ∧
      0 < p.natDegree ∧
      ‖Polynomial.aeval A (crouzeixProductRemainderPolynomial Omega p) *
          crouzeixPolynomialAuxiliaryOperator A Omega
            (crouzeixProductRemainderPolynomial Omega p)‖ ≤
        polynomialSupNorm (crouzeixProductRemainderPolynomial Omega p)
            (closure (numericalRange A)) ^ 2 ∧
      (¬ ∀ x : ℂ, ‖x‖ = 1 →
        -(polynomialSupNorm p (closure (numericalRange A)) ^ 2) ≤
          RCLike.re ⟪x, (Polynomial.aeval A p *
            crouzeixPolynomialAuxiliaryOperator A Omega p) x⟫_ℂ) ∧
      ¬ ‖Polynomial.aeval A p *
          crouzeixPolynomialAuxiliaryOperator A Omega p‖ ≤
        polynomialSupNorm p (closure (numericalRange A)) ^ 2 := by
  refine ⟨productInductionObstructionOperator,
    productInductionObstructionDomain,
    productInductionObstructionPolynomial,
    productInductionObstruction_contained,
    productInductionObstruction_cauchy, ?_,
    productInductionObstruction_remainder_bound, ?_, ?_⟩
  · rw [productInductionObstruction_degree]
    norm_num
  · intro hparent
    have hx := hparent 1 norm_one
    rw [productInductionObstruction_supNorm,
      productInductionObstruction_aeval,
      productInductionObstruction_auxiliary] at hx
    norm_num at hx
  · intro hparent
    rw [productInductionObstruction_supNorm,
      productInductionObstruction_aeval,
      productInductionObstruction_auxiliary] at hparent
    simp only [smul_mul_smul, norm_smul, norm_mul, norm_one, mul_one,
      one_pow] at hparent
    norm_num at hparent

private theorem productInductionObstruction_support :
    ∀ t ∈ Set.Ioc (0 : ℝ) (2 * Real.pi),
      ∀ w ∈ numericalRange productInductionObstructionOperator,
        ((starRingEnd ℂ)
            (-Complex.I * deriv productInductionObstructionDomain.boundaryParam t) *
          (w - productInductionObstructionDomain.boundaryParam t)).re ≤ 0 := by
  intro t _ht w hw
  have hwc : dist w (4 : ℂ) ≤ 5 := by
    rw [productInductionObstruction_numericalRange, Set.mem_singleton_iff] at hw
    subst w
    norm_num
  change ((starRingEnd ℂ) (-Complex.I * deriv (circleMap 4 5) t) *
    (w - circleMap 4 5 t)).re ≤ 0
  have hζ : ‖circleMap 0 5 t‖ = 5 := by
    rw [norm_circleMap_zero]
    norm_num
  have hν : -Complex.I * deriv (circleMap 4 5) t = circleMap 0 5 t := by
    rw [deriv_circleMap]
    linear_combination (-circleMap 0 5 t) * I_sq
  have hsub : w - circleMap 4 5 t = (w - 4) - circleMap 0 5 t := by
    rw [← circleMap_sub_center 4 5 t]
    ring
  have hfirst :
      ((starRingEnd ℂ) (circleMap 0 5 t) * (w - 4)).re ≤
        5 * dist w 4 := by
    calc
      ((starRingEnd ℂ) (circleMap 0 5 t) * (w - 4)).re ≤
          ‖(starRingEnd ℂ) (circleMap 0 5 t) * (w - 4)‖ :=
        Complex.re_le_norm _
      _ = 5 * dist w 4 := by
        rw [norm_mul, Complex.norm_conj, hζ, dist_eq_norm]
  have hsecond :
      ((starRingEnd ℂ) (circleMap 0 5 t) * circleMap 0 5 t).re =
        5 ^ 2 := by
    rw [Complex.conj_mul', hζ, ← Complex.ofReal_pow, Complex.ofReal_re]
  have hthird : 5 * dist w 4 ≤ 5 * 5 :=
    mul_le_mul_of_nonneg_left hwc (by norm_num)
  rw [hν, hsub, mul_sub, Complex.sub_re]
  linarith [hfirst, hsecond, hthird]

private theorem productInductionObstruction_symmetrized_bound :
    ‖Polynomial.aeval productInductionObstructionOperator
          productInductionObstructionPolynomial +
        star (crouzeixPolynomialAuxiliaryOperator
          productInductionObstructionOperator
          productInductionObstructionDomain
          productInductionObstructionPolynomial)‖ ≤
      2 * polynomialSupNorm productInductionObstructionPolynomial
        (closure (numericalRange productInductionObstructionOperator)) := by
  rw [productInductionObstruction_supNorm,
    productInductionObstruction_aeval,
    productInductionObstruction_auxiliary]
  change ‖(-1 : ℂ) • (1 : ℂ →L[ℂ] ℂ) +
      ContinuousLinearMap.adjoint ((3 : ℂ) • (1 : ℂ →L[ℂ] ℂ))‖ ≤ 2 * 1
  rw [map_smulₛₗ, Complex.conj_ofNat,
    ContinuousLinearMap.adjoint_one]
  have hsum :
      (-1 : ℂ) • (1 : ℂ →L[ℂ] ℂ) +
          (3 : ℂ) • (1 : ℂ →L[ℂ] ℂ) =
        (2 : ℂ) • (1 : ℂ →L[ℂ] ℂ) := by
    module
  rw [hsum, norm_smul, norm_one]
  norm_num

private theorem productInductionObstruction_supNorm_X :
    polynomialSupNorm Polynomial.X
      (closure (numericalRange productInductionObstructionOperator)) = 0 := by
  rw [productInductionObstruction_numericalRange, closure_singleton]
  apply le_antisymm
  · unfold polynomialSupNorm
    refine Real.iSup_le (fun z => ?_) le_rfl
    refine Real.iSup_le (fun hz => ?_) le_rfl
    rw [Set.mem_singleton_iff] at hz
    subst z
    rw [Polynomial.eval_X, norm_zero]
  · exact polynomialSupNorm_nonneg Polynomial.X {0}

private theorem productInductionObstruction_auxiliary_X :
    crouzeixPolynomialAuxiliaryOperator productInductionObstructionOperator
        productInductionObstructionDomain Polynomial.X =
      (4 : ℂ) • (1 : ℂ →L[ℂ] ℂ) := by
  change crouzeixPolynomialAuxiliaryOperator
      productInductionObstructionOperator
      (SmoothJordanDomain.ball 4 5 _) Polynomial.X = _
  rw [crouzeixPolynomialAuxiliaryOperator_ball_center_eq_eval_center_smul_one
    productInductionObstructionOperator 4
      productInductionObstruction_norm_sub_center Polynomial.X,
    Polynomial.eval_X]
  norm_num

private theorem productInductionObstruction_universal_symmetrized_fails :
    ¬ ∀ q : Polynomial ℂ,
      ‖Polynomial.aeval productInductionObstructionOperator q +
          star (crouzeixPolynomialAuxiliaryOperator
            productInductionObstructionOperator
            productInductionObstructionDomain q)‖ ≤
        2 * polynomialSupNorm q
          (closure (numericalRange productInductionObstructionOperator)) := by
  intro hsymm
  have hX := hsymm (Polynomial.X : Polynomial ℂ)
  have hAevalX : Polynomial.aeval productInductionObstructionOperator
      (Polynomial.X : Polynomial ℂ) = 0 := by
    rw [Polynomial.aeval_X]
    rfl
  rw [hAevalX, productInductionObstruction_auxiliary_X,
    productInductionObstruction_supNorm_X] at hX
  change ‖(0 : ℂ →L[ℂ] ℂ) +
      ContinuousLinearMap.adjoint ((4 : ℂ) • (1 : ℂ →L[ℂ] ℂ))‖ ≤
    2 * 0 at hX
  rw [zero_add, map_smulₛₗ, Complex.conj_ofNat,
    ContinuousLinearMap.adjoint_one, norm_smul, norm_one] at hX
  norm_num at hX

/-- The literal fixed-domain L4.2e product estimate is false even when all
of the intended smooth convex Cauchy/support hypotheses and the sharp L4.2d
symmetrized estimate for that polynomial hold.  The witness is the scalar
zero operator, the smooth convex disk `ball 4 5`, and the affine polynomial
`X - 1`.  The universal all-polynomial symmetrized family fails on this
off-center domain (already at `X`), so the result deliberately does not rule
out a stronger invariant which uses that family essentially. -/
theorem exists_smooth_convex_cauchy_support_product_bound_fails :
    ∃ (A : ℂ →L[ℂ] ℂ) (Omega : SmoothJordanDomain) (p : Polynomial ℂ),
      Convex ℝ Omega.carrier ∧
      closure (numericalRange A) ⊆ Omega.carrier ∧
      (∀ q : Polynomial ℂ,
        Polynomial.aeval A q =
          (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
            contourIntegral
              (fun z => Polynomial.eval z q • resolvent A z)
              Omega.boundaryParam) ∧
      (∀ t ∈ Set.Ioc (0 : ℝ) (2 * Real.pi),
        ∀ w ∈ numericalRange A,
          ((starRingEnd ℂ) (-Complex.I * deriv Omega.boundaryParam t) *
            (w - Omega.boundaryParam t)).re ≤ 0) ∧
      (¬ ∀ q : Polynomial ℂ,
        ‖Polynomial.aeval A q +
            star (crouzeixPolynomialAuxiliaryOperator A Omega q)‖ ≤
          2 * polynomialSupNorm q (closure (numericalRange A))) ∧
      ‖Polynomial.aeval A p +
          star (crouzeixPolynomialAuxiliaryOperator A Omega p)‖ ≤
        2 * polynomialSupNorm p (closure (numericalRange A)) ∧
      0 < p.natDegree ∧
      ¬ ‖Polynomial.aeval A p *
          crouzeixPolynomialAuxiliaryOperator A Omega p‖ ≤
        polynomialSupNorm p (closure (numericalRange A)) ^ 2 := by
  refine ⟨productInductionObstructionOperator,
    productInductionObstructionDomain,
    productInductionObstructionPolynomial, ?_,
    productInductionObstruction_contained, ?_,
    productInductionObstruction_support,
    productInductionObstruction_universal_symmetrized_fails,
    productInductionObstruction_symmetrized_bound, ?_, ?_⟩
  · exact convex_ball 4 5
  · intro q
    exact
      polynomial_aeval_eq_normalized_contourIntegral_of_resolvent_mass
        productInductionObstructionOperator
        productInductionObstructionDomain
        productInductionObstruction_contained
        productInductionObstruction_cauchy q
  · rw [productInductionObstruction_degree]
    norm_num
  · intro hparent
    rw [productInductionObstruction_supNorm,
      productInductionObstruction_aeval,
      productInductionObstruction_auxiliary] at hparent
    simp only [smul_mul_smul, norm_smul, norm_mul, norm_one, mul_one,
      one_pow] at hparent
    norm_num at hparent

end
