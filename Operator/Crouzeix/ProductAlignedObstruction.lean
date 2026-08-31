/-
# An aligned nonnormal obstruction to same-polynomial product coupling

The off-center scalar example in `ProductInductionObstruction.lean` shows
that the fixed-domain auxiliary product estimate cannot hold without a
compatibility condition on the contour.  This file shows that merely putting
the circle center in the closed numerical range is still insufficient for a
nonnormal operator.

For the two-dimensional nilpotent shift, the closed numerical range is the
disk of radius `1 / 2`.  At the aligned center `2 / 5`, the polynomial
`X + 1` satisfies the sharp symmetrized estimate, but its actual circle
auxiliary product has norm strictly larger than its squared numerical-range
sup norm.  Its universal all-polynomial symmetrized family fails already at
`X`.  Thus the star-normal hypothesis in `NormalProduct.lean` is substantive,
while the example deliberately leaves open an implication that uses universal
symmetrization essentially.

## Main declaration

* `exists_aligned_same_polynomial_symmetrized_product_bound_fails` gives the
  explicit aligned nonnormal witness.
-/
import Operator.Crouzeix.AffineAuxiliary
import Operator.Crouzeix.VonNeumann
import Operator.NumericalRange.Convex
import Mathlib.Analysis.InnerProductSpace.ProdL2

open Complex Polynomial Set
open scoped InnerProductSpace

private abbrev AlignedObstructionSpace := WithLp 2 (ℂ × ℂ)

private noncomputable def alignedObstructionShiftLinear :
    AlignedObstructionSpace →ₗ[ℂ] AlignedObstructionSpace where
  toFun x := WithLp.toLp 2 (x.snd, 0)
  map_add' x y := by
    apply WithLp.ofLp_injective 2
    exact Prod.ext rfl (add_zero (0 : ℂ)).symm
  map_smul' a x := by
    apply WithLp.ofLp_injective 2
    exact Prod.ext rfl (smul_zero a).symm

private theorem alignedObstructionShiftLinear_bound
    (x : AlignedObstructionSpace) :
    ‖alignedObstructionShiftLinear x‖ ≤ 1 * ‖x‖ := by
  rw [one_mul, WithLp.prod_norm_eq_of_L2]
  change Real.sqrt (‖x.snd‖ ^ 2 + ‖0‖ ^ 2) ≤ _
  rw [norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero,
    Real.sqrt_sq (norm_nonneg _)]
  exact WithLp.norm_snd_le ℂ x

private noncomputable def alignedObstructionShift :
    AlignedObstructionSpace →L[ℂ] AlignedObstructionSpace :=
  alignedObstructionShiftLinear.mkContinuous 1 alignedObstructionShiftLinear_bound

@[simp] private theorem alignedObstructionShift_apply
    (x : AlignedObstructionSpace) :
    alignedObstructionShift x = WithLp.toLp 2 (x.snd, 0) := rfl

private theorem norm_alignedObstructionShift_le :
    ‖alignedObstructionShift‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one alignedObstructionShiftLinear_bound

private noncomputable def alignedObstructionPolynomial : Polynomial ℂ :=
  Polynomial.X + 1

private theorem alignedObstruction_aeval :
    Polynomial.aeval alignedObstructionShift alignedObstructionPolynomial =
      alignedObstructionShift + 1 := by
  unfold alignedObstructionPolynomial
  rw [map_add, Polynomial.aeval_X, map_one]

private theorem alignedObstruction_inner (x : AlignedObstructionSpace) :
    ⟪x, alignedObstructionShift x⟫_ℂ =
      (starRingEnd ℂ) x.fst * x.snd := by
  rw [alignedObstructionShift_apply]
  simp only [WithLp.prod_inner_apply, WithLp.ofLp_fst, WithLp.ofLp_snd,
    RCLike.inner_apply', mul_zero, add_zero]

private theorem alignedObstruction_numericalRange_norm_le {z : ℂ}
    (hz : z ∈ numericalRange alignedObstructionShift) : ‖z‖ ≤ 1 / 2 := by
  obtain ⟨x, hx, rfl⟩ := (mem_numericalRange alignedObstructionShift _).mp hz
  rw [alignedObstruction_inner, norm_mul]
  rw [Complex.norm_conj]
  have hsquares : ‖x.fst‖ ^ 2 + ‖x.snd‖ ^ 2 = 1 := by
    rw [← WithLp.prod_norm_sq_eq_of_L2, hx]
    norm_num
  have hdiff : 0 ≤ (‖x.fst‖ - ‖x.snd‖) ^ 2 := sq_nonneg _
  nlinarith only [hsquares, hdiff]

private theorem alignedObstruction_closure_numericalRange_subset :
    closure (numericalRange alignedObstructionShift) ⊆
      Metric.closedBall (0 : ℂ) (1 / 2) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right]
  exact alignedObstruction_numericalRange_norm_le hz

private noncomputable def alignedObstructionBoundaryVector :
    AlignedObstructionSpace :=
  let s : ℂ := (Real.sqrt 2 : ℂ) / 2
  WithLp.toLp 2 (s, s)

private theorem alignedObstructionBoundaryVector_norm :
    ‖alignedObstructionBoundaryVector‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [WithLp.prod_norm_sq_eq_of_L2]
  change ‖((Real.sqrt 2 : ℂ) / 2)‖ ^ 2 +
      ‖((Real.sqrt 2 : ℂ) / 2)‖ ^ 2 = 1 ^ 2
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg 2), norm_ofNat]
  have hsqrt : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith only [hsqrt]

private theorem half_mem_alignedObstruction_numericalRange :
    (1 / 2 : ℂ) ∈ numericalRange alignedObstructionShift := by
  apply (mem_numericalRange alignedObstructionShift _).mpr
  refine ⟨alignedObstructionBoundaryVector,
    alignedObstructionBoundaryVector_norm, ?_⟩
  rw [alignedObstruction_inner]
  change (starRingEnd ℂ) (((Real.sqrt 2 : ℂ) / 2)) *
      ((Real.sqrt 2 : ℂ) / 2) = 1 / 2
  have hcoe : ((Real.sqrt 2 : ℂ) / 2) =
      ((Real.sqrt 2 / 2 : ℝ) : ℂ) := by push_cast; rfl
  rw [hcoe, Complex.conj_ofReal]
  have hsqrt : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hreal : (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) = (1 / 2 : ℝ) := by
    nlinarith only [hsqrt]
  calc
    ((Real.sqrt 2 / 2 : ℝ) : ℂ) * ((Real.sqrt 2 / 2 : ℝ) : ℂ) =
        (((Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) : ℝ) : ℂ) := by
      push_cast
      rfl
    _ = ((1 / 2 : ℝ) : ℂ) :=
      congrArg (fun r : ℝ => (r : ℂ)) hreal
    _ = (1 / 2 : ℂ) := by norm_num

private theorem alignedObstruction_supNorm :
    polynomialSupNorm alignedObstructionPolynomial
      (closure (numericalRange alignedObstructionShift)) = 3 / 2 := by
  apply le_antisymm
  · unfold polynomialSupNorm
    refine Real.iSup_le (fun z ↦ ?_) (by norm_num)
    refine Real.iSup_le (fun hz ↦ ?_) (by norm_num)
    have hzball := alignedObstruction_closure_numericalRange_subset hz
    rw [Metric.mem_closedBall, dist_zero_right] at hzball
    simp only [alignedObstructionPolynomial, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_one]
    calc
      ‖z + 1‖ ≤ ‖z‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ 3 / 2 := by rw [norm_one]; linarith only [hzball]
  · have hlower := norm_eval_le_polynomialSupNorm
      alignedObstructionPolynomial
      (bddAbove_norm_eval_image_of_isCompact alignedObstructionPolynomial
        ((isBounded_numericalRange alignedObstructionShift).isCompact_closure))
      (subset_closure half_mem_alignedObstruction_numericalRange)
    have hval : ‖((1 / 2 : ℂ) + 1)‖ = (3 / 2 : ℝ) := by norm_num
    rw [alignedObstructionPolynomial, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_one, hval] at hlower
    exact hlower

private theorem alignedObstruction_supNorm_X :
    polynomialSupNorm Polynomial.X
      (closure (numericalRange alignedObstructionShift)) = 1 / 2 := by
  apply le_antisymm
  · unfold polynomialSupNorm
    refine Real.iSup_le (fun z ↦ ?_) (by norm_num)
    refine Real.iSup_le (fun hz ↦ ?_) (by norm_num)
    rw [Polynomial.eval_X]
    have hzball := alignedObstruction_closure_numericalRange_subset hz
    rwa [Metric.mem_closedBall, dist_zero_right] at hzball
  · simpa only [Polynomial.eval_X, norm_div, norm_one, norm_ofNat] using
      norm_eval_le_polynomialSupNorm Polynomial.X
        (bddAbove_norm_eval_image_of_isCompact Polynomial.X
          ((isBounded_numericalRange alignedObstructionShift).isCompact_closure))
        (subset_closure half_mem_alignedObstruction_numericalRange)

private theorem zero_mem_alignedObstruction_numericalRange :
    0 ∈ numericalRange alignedObstructionShift := by
  apply (mem_numericalRange alignedObstructionShift 0).mpr
  let x : AlignedObstructionSpace := WithLp.toLp 2 ((1 : ℂ), 0)
  refine ⟨x, ?_, ?_⟩
  · rw [WithLp.prod_norm_eq_of_L2]
    change Real.sqrt (‖(1 : ℂ)‖ ^ 2 + ‖(0 : ℂ)‖ ^ 2) = 1
    norm_num
  · rw [alignedObstruction_inner]
    change (starRingEnd ℂ) (1 : ℂ) * 0 = 0
    norm_num

private theorem alignedObstruction_center_mem :
    (2 / 5 : ℂ) ∈ closure (numericalRange alignedObstructionShift) := by
  have hconv := convex_numericalRange alignedObstructionShift
  have hmem := hconv zero_mem_alignedObstruction_numericalRange
    half_mem_alignedObstruction_numericalRange
    (show (0 : ℝ) ≤ 1 / 5 by norm_num)
    (show (0 : ℝ) ≤ 4 / 5 by norm_num)
    (show (1 / 5 : ℝ) + 4 / 5 = 1 by norm_num)
  apply subset_closure
  norm_num [smul_eq_mul] at hmem ⊢
  exact hmem

private theorem alignedObstruction_enclosure :
    ‖alignedObstructionShift -
        (2 / 5 : ℂ) • (1 : AlignedObstructionSpace →L[ℂ]
          AlignedObstructionSpace)‖ < 2 := by
  calc
    ‖alignedObstructionShift - (2 / 5 : ℂ) •
        (1 : AlignedObstructionSpace →L[ℂ] AlignedObstructionSpace)‖ ≤
        ‖alignedObstructionShift‖ + ‖(2 / 5 : ℂ) •
          (1 : AlignedObstructionSpace →L[ℂ] AlignedObstructionSpace)‖ :=
      norm_sub_le _ _
    _ ≤ 1 + 2 / 5 := by
      rw [norm_smul, norm_one]
      norm_num
      linarith only [norm_alignedObstructionShift_le]
    _ < 2 := by norm_num

private theorem alignedObstruction_symmetrized_operator_bound :
    ‖alignedObstructionShift +
        (12 / 5 : ℂ) • (1 : AlignedObstructionSpace →L[ℂ]
          AlignedObstructionSpace)‖ ≤ 3 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  have happ : (alignedObstructionShift +
        (12 / 5 : ℂ) • (1 : AlignedObstructionSpace →L[ℂ]
          AlignedObstructionSpace)) x =
      WithLp.toLp 2
        (x.snd + (12 / 5 : ℂ) * x.fst, (12 / 5 : ℂ) * x.snd) := by
    rw [add_apply, alignedObstructionShift_apply, smul_apply,
      one_apply_eq_self]
    apply WithLp.ofLp_injective 2
    change (x.snd, 0) + (12 / 5 : ℂ) • (x.fst, x.snd) =
      (x.snd + (12 / 5 : ℂ) * x.fst, (12 / 5 : ℂ) * x.snd)
    exact Prod.ext rfl (zero_add _)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num) (norm_nonneg x))).mp
  rw [happ, WithLp.prod_norm_sq_eq_of_L2]
  change
    ‖x.snd + (12 / 5 : ℂ) * x.fst‖ ^ 2 +
        ‖(12 / 5 : ℂ) * x.snd‖ ^ 2 ≤ (3 * ‖x‖) ^ 2
  have hfirst : ‖x.snd + (12 / 5 : ℂ) * x.fst‖ ≤
      ‖x.snd‖ + (12 / 5 : ℝ) * ‖x.fst‖ := by
    calc
      ‖x.snd + (12 / 5 : ℂ) * x.fst‖ ≤
          ‖x.snd‖ + ‖(12 / 5 : ℂ) * x.fst‖ := norm_add_le _ _
      _ = ‖x.snd‖ + (12 / 5 : ℝ) * ‖x.fst‖ := by
        rw [norm_mul]
        norm_num
  have hfirstsq := pow_le_pow_left₀ (norm_nonneg _) hfirst 2
  have hcross :
      120 * ‖x.fst‖ * ‖x.snd‖ ≤
        80 * ‖x.fst‖ ^ 2 + 45 * ‖x.snd‖ ^ 2 := by
    have hsquare : 0 ≤ (4 * ‖x.fst‖ - 3 * ‖x.snd‖) ^ 2 := sq_nonneg _
    nlinarith only [hsquare]
  have hnormsq : ‖x‖ ^ 2 = ‖x.fst‖ ^ 2 + ‖x.snd‖ ^ 2 :=
    WithLp.prod_norm_sq_eq_of_L2 x
  rw [norm_mul]
  norm_num
  nlinarith only [hfirstsq, hcross, hnormsq]

private theorem alignedObstruction_auxiliary :
    crouzeixPolynomialAuxiliaryOperator alignedObstructionShift
        (SmoothJordanDomain.ball (2 / 5) 2
          ((norm_nonneg (alignedObstructionShift -
            (2 / 5 : ℂ) • (1 : AlignedObstructionSpace →L[ℂ]
              AlignedObstructionSpace))).trans_lt alignedObstruction_enclosure))
        alignedObstructionPolynomial =
      (7 / 5 : ℂ) • (1 : AlignedObstructionSpace →L[ℂ]
        AlignedObstructionSpace) := by
  rw [crouzeixPolynomialAuxiliaryOperator_ball_center_eq_eval_center_smul_one
    alignedObstructionShift (2 / 5) alignedObstruction_enclosure
    alignedObstructionPolynomial]
  unfold alignedObstructionPolynomial
  norm_num

private theorem alignedObstruction_symmetrized_bound :
    ‖Polynomial.aeval alignedObstructionShift alignedObstructionPolynomial +
        star (crouzeixPolynomialAuxiliaryOperator alignedObstructionShift
          (SmoothJordanDomain.ball (2 / 5) 2
            ((norm_nonneg (alignedObstructionShift -
              (2 / 5 : ℂ) • (1 : AlignedObstructionSpace →L[ℂ]
                AlignedObstructionSpace))).trans_lt alignedObstruction_enclosure))
          alignedObstructionPolynomial)‖ ≤
      2 * polynomialSupNorm alignedObstructionPolynomial
        (closure (numericalRange alignedObstructionShift)) := by
  rw [alignedObstruction_aeval, alignedObstruction_auxiliary,
    alignedObstruction_supNorm]
  change ‖alignedObstructionShift + 1 +
      ContinuousLinearMap.adjoint ((7 / 5 : ℂ) •
        (1 : AlignedObstructionSpace →L[ℂ] AlignedObstructionSpace))‖ ≤
    2 * (3 / 2)
  rw [map_smulₛₗ,
    show (starRingEnd ℂ) (7 / 5 : ℂ) = 7 / 5 by
      rw [map_div₀, Complex.conj_ofNat, Complex.conj_ofNat],
    ContinuousLinearMap.adjoint_one]
  have hsum : alignedObstructionShift +
        (1 : AlignedObstructionSpace →L[ℂ] AlignedObstructionSpace) +
        (7 / 5 : ℂ) • 1 =
      alignedObstructionShift + (12 / 5 : ℂ) • 1 := by
    module
  rw [hsum]
  norm_num
  exact alignedObstruction_symmetrized_operator_bound

private noncomputable def alignedObstructionTestVector : AlignedObstructionSpace :=
  WithLp.toLp 2 ((3 / 5 : ℂ), (4 / 5 : ℂ))

private theorem alignedObstructionTestVector_norm :
    ‖alignedObstructionTestVector‖ = 1 := by
  rw [WithLp.prod_norm_eq_of_L2]
  change Real.sqrt (‖(3 / 5 : ℂ)‖ ^ 2 + ‖(4 / 5 : ℂ)‖ ^ 2) = 1
  norm_num

private theorem alignedObstruction_auxiliary_X :
    crouzeixPolynomialAuxiliaryOperator alignedObstructionShift
        (SmoothJordanDomain.ball (2 / 5) 2
          ((norm_nonneg (alignedObstructionShift -
            (2 / 5 : ℂ) • (1 : AlignedObstructionSpace →L[ℂ]
              AlignedObstructionSpace))).trans_lt alignedObstruction_enclosure))
        Polynomial.X =
      (2 / 5 : ℂ) • (1 : AlignedObstructionSpace →L[ℂ]
        AlignedObstructionSpace) := by
  rw [crouzeixPolynomialAuxiliaryOperator_ball_center_eq_eval_center_smul_one
    alignedObstructionShift (2 / 5) alignedObstruction_enclosure Polynomial.X,
    Polynomial.eval_X]
  norm_num [map_div₀, Complex.conj_ofNat]

private theorem alignedObstruction_universal_symmetrized_fails :
    ¬ ∀ q : Polynomial ℂ,
      ‖Polynomial.aeval alignedObstructionShift q +
          star (crouzeixPolynomialAuxiliaryOperator alignedObstructionShift
            (SmoothJordanDomain.ball (2 / 5) 2
              ((norm_nonneg (alignedObstructionShift -
                (2 / 5 : ℂ) • (1 : AlignedObstructionSpace →L[ℂ]
                  AlignedObstructionSpace))).trans_lt alignedObstruction_enclosure)) q)‖ ≤
        2 * polynomialSupNorm q
          (closure (numericalRange alignedObstructionShift)) := by
  intro hall
  have hX := hall (Polynomial.X : Polynomial ℂ)
  rw [Polynomial.aeval_X, alignedObstruction_auxiliary_X,
    alignedObstruction_supNorm_X] at hX
  change ‖alignedObstructionShift +
      ContinuousLinearMap.adjoint ((2 / 5 : ℂ) •
        (1 : AlignedObstructionSpace →L[ℂ] AlignedObstructionSpace))‖ ≤
    2 * (1 / 2) at hX
  rw [map_smulₛₗ,
    show (starRingEnd ℂ) (2 / 5 : ℂ) = 2 / 5 by
      rw [map_div₀, Complex.conj_ofNat, Complex.conj_ofNat],
    ContinuousLinearMap.adjoint_one] at hX
  let F : AlignedObstructionSpace →L[ℂ] AlignedObstructionSpace :=
    alignedObstructionShift + (2 / 5 : ℂ) • 1
  have happ : F alignedObstructionTestVector =
      WithLp.toLp 2 ((26 / 25 : ℂ), (8 / 25 : ℂ)) := by
    dsimp only [F]
    rw [add_apply, alignedObstructionShift_apply, smul_apply,
      one_apply_eq_self]
    apply WithLp.ofLp_injective 2
    norm_num [alignedObstructionTestVector]
  have hnormsq : ‖F alignedObstructionTestVector‖ ^ 2 = (148 / 125 : ℝ) := by
    rw [happ, WithLp.prod_norm_sq_eq_of_L2]
    norm_num
  have hnormgt : (1 : ℝ) < ‖F alignedObstructionTestVector‖ := by
    have hnonneg := norm_nonneg (F alignedObstructionTestVector)
    nlinarith only [hnormsq, hnonneg]
  have hle := F.le_opNorm alignedObstructionTestVector
  rw [alignedObstructionTestVector_norm, mul_one] at hle
  change ‖F‖ ≤ 2 * (1 / 2) at hX
  norm_num at hX
  linarith only [hnormgt, hle, hX]

private theorem alignedObstruction_product_bound_fails :
    ¬ ‖Polynomial.aeval alignedObstructionShift alignedObstructionPolynomial *
        crouzeixPolynomialAuxiliaryOperator alignedObstructionShift
          (SmoothJordanDomain.ball (2 / 5) 2
            ((norm_nonneg (alignedObstructionShift -
              (2 / 5 : ℂ) • (1 : AlignedObstructionSpace →L[ℂ]
                AlignedObstructionSpace))).trans_lt alignedObstruction_enclosure))
          alignedObstructionPolynomial‖ ≤
      polynomialSupNorm alignedObstructionPolynomial
        (closure (numericalRange alignedObstructionShift)) ^ 2 := by
  rw [alignedObstruction_aeval, alignedObstruction_auxiliary,
    alignedObstruction_supNorm]
  let F : AlignedObstructionSpace →L[ℂ] AlignedObstructionSpace :=
    (alignedObstructionShift + 1) * ((7 / 5 : ℂ) • 1)
  have happ : F alignedObstructionTestVector =
      WithLp.toLp 2 ((49 / 25 : ℂ), (28 / 25 : ℂ)) := by
    dsimp only [F]
    rw [mul_apply_eq_comp, smul_apply, one_apply_eq_self, add_apply,
      alignedObstructionShift_apply, one_apply_eq_self]
    apply WithLp.ofLp_injective 2
    norm_num [alignedObstructionTestVector]
  have hnormsq : ‖F alignedObstructionTestVector‖ ^ 2 = (637 / 125 : ℝ) := by
    rw [happ, WithLp.prod_norm_sq_eq_of_L2]
    norm_num
  have hnormgt : (9 / 4 : ℝ) < ‖F alignedObstructionTestVector‖ := by
    have hnonneg := norm_nonneg (F alignedObstructionTestVector)
    nlinarith only [hnormsq, hnonneg]
  have hle := F.le_opNorm alignedObstructionTestVector
  rw [alignedObstructionTestVector_norm, mul_one] at hle
  change ¬ ‖F‖ ≤ (3 / 2 : ℝ) ^ 2
  intro hF
  norm_num at hF
  linarith only [hnormgt, hle, hF]

/-- Center alignment and the sharp symmetrized estimate for one polynomial
do not imply the sharp auxiliary product bound for a nonnormal operator.  The
type also records that the universal symmetrized family fails on the witness,
so it does not refute an implication using that family essentially. -/
theorem exists_aligned_same_polynomial_symmetrized_product_bound_fails :
    ∃ (A : WithLp 2 (ℂ × ℂ) →L[ℂ] WithLp 2 (ℂ × ℂ))
      (c : ℂ) (R : ℝ) (p : Polynomial ℂ)
      (hA : ‖A - c • (1 : WithLp 2 (ℂ × ℂ) →L[ℂ]
        WithLp 2 (ℂ × ℂ))‖ < R),
      c ∈ closure (numericalRange A) ∧
      (¬ ∀ q : Polynomial ℂ,
        ‖Polynomial.aeval A q +
            star (crouzeixPolynomialAuxiliaryOperator A
              (SmoothJordanDomain.ball c R
                ((norm_nonneg (A - c • 1)).trans_lt hA)) q)‖ ≤
          2 * polynomialSupNorm q (closure (numericalRange A))) ∧
      ‖Polynomial.aeval A p +
          star (crouzeixPolynomialAuxiliaryOperator A
            (SmoothJordanDomain.ball c R
              ((norm_nonneg (A - c • 1)).trans_lt hA)) p)‖ ≤
        2 * polynomialSupNorm p (closure (numericalRange A)) ∧
      ¬ ‖Polynomial.aeval A p *
          crouzeixPolynomialAuxiliaryOperator A
            (SmoothJordanDomain.ball c R
              ((norm_nonneg (A - c • 1)).trans_lt hA)) p‖ ≤
        polynomialSupNorm p (closure (numericalRange A)) ^ 2 := by
  refine ⟨alignedObstructionShift, 2 / 5, 2,
    alignedObstructionPolynomial, alignedObstruction_enclosure,
    alignedObstruction_center_mem, alignedObstruction_universal_symmetrized_fails,
    alignedObstruction_symmetrized_bound,
    alignedObstruction_product_bound_fails⟩
