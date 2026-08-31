/-
# Defect operators of a contraction (foundation for L3.0 / L3.1)

For a contraction `T` (`‖T‖ ≤ 1`) on a complex Hilbert space `E`, the operator `1 - T†T` is
positive, and its positive square root `D_T = (1 - T†T)^{1/2}` is the *defect operator* of `T`.
It is the ingredient of the Halmos 2×2 block dilation (L3.0) and the Schäffer power dilation
(L3.1): the isometry identity `‖T x‖² + ‖D_T x‖² = ‖x‖²` is what makes the first column
`[T; D_T]` of the Halmos block an isometry.

The square root is Mathlib's continuous-functional-calculus square root `CFC.sqrt` in the
C*-algebra `E →L[ℂ] E`, with respect to the Loewner order
(`ContinuousLinearMap.instLoewnerPartialOrder`).

## Main declarations

* `one_sub_adjoint_mul_self_nonneg` — `0 ≤ 1 - T†T` for `‖T‖ ≤ 1`.
* `defect T` — the defect operator `CFC.sqrt (1 - T†T)`.
* `defect_nonneg`, `isSelfAdjoint_defect` — `D_T` is positive, hence self-adjoint.
* `defect_mul_defect` — `D_T * D_T = 1 - T†T` for `‖T‖ ≤ 1`.
* `norm_apply_sq_add_norm_defect_apply_sq` — `‖T x‖² + ‖D_T x‖² = ‖x‖²` for `‖T‖ ≤ 1`.
* `defect_adjoint`, `norm_adjoint_le_one` — the defect operator of `T†` is
  `(1 - TT†)^{1/2}`, and `T†` is again a contraction.
* `SemiconjBy.cfcₙ_real`, `SemiconjBy.cfcSqrt` — an intertwiner of self-adjoint (resp. positive)
  operators intertwines their real continuous functional calculi (resp. square roots).
* `mul_defect_eq_defect_adjoint_mul` — the intertwining relation `T D_T = D_{T†} T`, which makes
  the Halmos block `[[T, D_{T†}], [D_T, -T†]]` unitary.

Requires `[CompleteSpace E]` (adjoints, the C*-algebra structure on `E →L[ℂ] E`).
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

open ContinuousLinearMap
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The quadratic form of `1 - T†T`: `⟪x, (1 - T†T) x⟫ = ‖x‖² - ‖T x‖²`. -/
theorem inner_one_sub_adjoint_mul_self_apply (T : E →L[ℂ] E) (x : E) :
    ⟪x, (1 - adjoint T * T) x⟫_ℂ = ((‖x‖ ^ 2 - ‖T x‖ ^ 2 : ℝ) : ℂ) := by
  rw [sub_apply, one_apply_eq_self, mul_apply_eq_comp, inner_sub_right, adjoint_inner_right,
    inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- For a contraction `T`, the operator `1 - T†T` is positive (Loewner order). -/
theorem one_sub_adjoint_mul_self_nonneg (T : E →L[ℂ] E) (hT : ‖T‖ ≤ 1) :
    0 ≤ 1 - adjoint T * T := by
  rw [nonneg_iff_isPositive, isPositive_iff_complex]
  intro x
  have hx : ‖T x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    have h1 : ‖T x‖ ≤ ‖x‖ := by
      calc ‖T x‖ ≤ ‖T‖ * ‖x‖ := T.le_opNorm x
        _ ≤ 1 * ‖x‖ := by gcongr
        _ = ‖x‖ := one_mul _
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  have hsymm : ⟪(1 - adjoint T * T) x, x⟫_ℂ = ((‖x‖ ^ 2 - ‖T x‖ ^ 2 : ℝ) : ℂ) := by
    rw [← inner_conj_symm, inner_one_sub_adjoint_mul_self_apply, Complex.conj_ofReal]
  rw [hsymm]
  refine ⟨?_, ?_⟩
  · simp only [RCLike.re_to_complex, Complex.ofReal_re]
  · rw [RCLike.re_to_complex, Complex.ofReal_re]
    linarith

/-- The defect operator `D_T = (1 - T†T)^{1/2}` of `T`, via the continuous functional calculus
square root in the C*-algebra `E →L[ℂ] E`. -/
noncomputable def defect (T : E →L[ℂ] E) : E →L[ℂ] E :=
  CFC.sqrt (1 - adjoint T * T)

/-- The defect operator is positive. -/
theorem defect_nonneg (T : E →L[ℂ] E) : 0 ≤ defect T :=
  CFC.sqrt_nonneg _

/-- The defect operator is self-adjoint. -/
theorem isSelfAdjoint_defect (T : E →L[ℂ] E) : IsSelfAdjoint (defect T) :=
  IsSelfAdjoint.of_nonneg (defect_nonneg T)

/-- For a contraction `T`, `D_T * D_T = 1 - T†T`. -/
theorem defect_mul_defect (T : E →L[ℂ] E) (hT : ‖T‖ ≤ 1) :
    defect T * defect T = 1 - adjoint T * T :=
  CFC.sqrt_mul_sqrt_self _ (one_sub_adjoint_mul_self_nonneg T hT)

/-- The isometry identity of the defect operator: for a contraction `T`,
`‖T x‖² + ‖D_T x‖² = ‖x‖²`. -/
theorem norm_apply_sq_add_norm_defect_apply_sq (T : E →L[ℂ] E) (hT : ‖T‖ ≤ 1) (x : E) :
    ‖T x‖ ^ 2 + ‖defect T x‖ ^ 2 = ‖x‖ ^ 2 := by
  have h : ⟪defect T x, defect T x⟫_ℂ = ⟪x, (1 - adjoint T * T) x⟫_ℂ := by
    rw [← defect_mul_defect T hT, mul_apply_eq_comp, ← adjoint_inner_right,
      (isSelfAdjoint_defect T).adjoint_eq]
  have h3 := congrArg RCLike.re (h.trans (inner_one_sub_adjoint_mul_self_apply T x))
  rw [inner_self_eq_norm_sq, RCLike.re_to_complex, Complex.ofReal_re] at h3
  linarith

/-- The defect operator of the adjoint is `(1 - TT†)^{1/2}`. -/
theorem defect_adjoint (T : E →L[ℂ] E) :
    defect (adjoint T) = CFC.sqrt (1 - T * adjoint T) := by
  simp only [defect, adjoint_adjoint]

/-- The adjoint of a contraction is a contraction. -/
theorem norm_adjoint_le_one (T : E →L[ℂ] E) (hT : ‖T‖ ≤ 1) : ‖adjoint T‖ ≤ 1 := by
  have h : ‖adjoint T‖ = ‖T‖ :=
    (ContinuousLinearMap.adjoint : (E →L[ℂ] E) ≃ₗᵢ⋆[ℂ] (E →L[ℂ] E)).norm_map T
  rw [h]
  exact hT

/-! ### The intertwining relation `T D_T = D_{T†} T` -/

open scoped NNReal ContinuousMapZero

/-- `T` intertwines `1 - T†T` and `1 - TT†`: `T (1 - T†T) = (1 - TT†) T`. -/
theorem semiconjBy_one_sub_adjoint_mul_self (T : E →L[ℂ] E) :
    SemiconjBy T (1 - adjoint T * T) (1 - T * adjoint T) := by
  simp only [SemiconjBy, mul_sub, sub_mul, mul_one, one_mul, mul_assoc]

/-- If `x` intertwines the self-adjoint operators `a` and `b` (`x * a = b * x`) and `f : ℝ → ℝ`
is continuous, then `x` intertwines `cfcₙ f a` and `cfcₙ f b`. Proof:
continuous-functional-calculus induction on the product algebra, mirroring Mathlib's
`Commute.cfcₙHom`. -/
theorem SemiconjBy.cfcₙ_real {x a b : E →L[ℂ] E} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (h : SemiconjBy x a b) {f : ℝ → ℝ} (hf : Continuous f) :
    SemiconjBy x (cfcₙ f a) (cfcₙ f b) := by
  have key : SemiconjBy x (cfcₙ f (a, b)).1 (cfcₙ f (a, b)).2 := by
    refine cfcₙ_cases (fun y : (E →L[ℂ] E) × (E →L[ℂ] E) => SemiconjBy x y.1 y.2) (a, b)
      f (SemiconjBy.zero_right x) ?_
    intro hf' hf0' hab
    have main : ∀ g : C(quasispectrum ℝ ((a, b) : (E →L[ℂ] E) × (E →L[ℂ] E)), ℝ)₀,
        SemiconjBy x (cfcₙHom hab g).1 (cfcₙHom hab g).2 := by
      intro g
      open scoped NonUnitalContinuousFunctionalCalculus in
      induction g using ContinuousMapZero.induction_on_of_compact with
      | zero => rw [map_zero]; exact SemiconjBy.zero_right x
      | id => rw [cfcₙHom_id hab]; exact h
      | star_id =>
        rw [map_star, cfcₙHom_id hab]
        change SemiconjBy x (star a) (star b)
        rw [ha.star_eq, hb.star_eq]
        exact h
      | add f g hf hg => rw [map_add]; exact hf.add_right hg
      | mul f g hf hg => rw [map_mul]; exact hf.mul_right hg
      | smul r f hf => rw [map_smul]; exact hf.smul_right r
      | frequently f hf =>
        change x * (cfcₙHom hab f).1 = (cfcₙHom hab f).2 * x
        rw [← Set.mem_ofPred (p := fun y : (E →L[ℂ] E) × (E →L[ℂ] E) => x * y.1 = y.2 * x),
          ← (isClosed_eq (by fun_prop) (by fun_prop)).closure_eq]
        apply mem_closure_of_frequently_of_tendsto hf
        exact cfcₙHom_continuous hab |>.tendsto _
    exact main _
  have hab : IsSelfAdjoint ((a, b) : (E →L[ℂ] E) × (E →L[ℂ] E)) := Prod.ext ha.star_eq hb.star_eq
  rwa [cfcₙ_map_prod (S := ℝ) f a b hf.continuousOn hab ha hb] at key

/-- If `x` intertwines the positive operators `a` and `b`, then it intertwines their square
roots: `x * √a = √b * x`. -/
theorem SemiconjBy.cfcSqrt {x a b : E →L[ℂ] E} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : SemiconjBy x a b) : SemiconjBy x (CFC.sqrt a) (CFC.sqrt b) := by
  unfold CFC.sqrt
  rw [cfcₙ_nnreal_eq_real NNReal.sqrt a ha, cfcₙ_nnreal_eq_real NNReal.sqrt b hb]
  exact h.cfcₙ_real (IsSelfAdjoint.of_nonneg ha) (IsSelfAdjoint.of_nonneg hb)
    (NNReal.continuous_coe.comp (NNReal.sqrt.continuous.comp continuous_real_toNNReal))

/-- The intertwining relation of the defect operators: for a contraction `T`,
`T D_T = D_{T†} T`, i.e. `T (1 - T†T)^{1/2} = (1 - TT†)^{1/2} T`. -/
theorem mul_defect_eq_defect_adjoint_mul (T : E →L[ℂ] E) (hT : ‖T‖ ≤ 1) :
    T * defect T = defect (adjoint T) * T := by
  rw [defect_adjoint]
  unfold defect
  have hb : 0 ≤ 1 - T * adjoint T := by
    simpa only [adjoint_adjoint] using
      one_sub_adjoint_mul_self_nonneg (adjoint T) (norm_adjoint_le_one T hT)
  exact (semiconjBy_one_sub_adjoint_mul_self T).cfcSqrt (one_sub_adjoint_mul_self_nonneg T hT) hb
