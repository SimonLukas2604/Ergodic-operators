/-
# Paper III: abstract polar construction of the exact well basis  (paper §3.1, §3.3, §3.4)

*Periodic magnetic Schrödinger operators: Dry Ten Martini and spectral transitions.*

Operator-theoretic core of the exact well-basis construction.  For complex Hilbert spaces
`E` (the coefficient space `ℓ²(ℤ²)`) and `F` (the physical Hilbert space) and a bounded
synthesis map `Vh : E →L[ℂ] F` (the projected map `𝒱 = P𝓔`), we set

  `K = 𝒱* 𝒱`  (`gram`),   `K^{-1/2}`  (`gramInvSqrt`, via `CFC.rpow`),   `𝒰 = 𝒱 K^{-1/2}`  (`polar`)

(paper `c-eq:correct-gram`, and the display opening §3).

* **Proposition `c-prop:projected-completeness`** (abstract part): if `K` is invertible then
  `𝒰* 𝒰 = 1` (`adjoint_polar_comp_polar`), `Ran 𝒰 = Ran 𝒱` (`range_polar`), `Ran 𝒱` is closed
  (`isClosed_range`), and `𝒰` is a unitary `E ≃ₗᵢ M` onto any submodule `M = Ran 𝒱`
  (the paper's `Ran P`) (`polarEquiv`).  Hence `φ_j = 𝒰 δ_j` is a Hilbert basis of `M`
  (`polarBasis`, `polarBasis_apply`), with expansion `φ_j = Σ_l (K^{-1/2})_{lj} v_l`
  (`hasSum_polar_apply`) and Gram entries `⟪v_l, v_j⟫ = ⟪δ_l, K δ_j⟫`
  (`inner_map_map_eq_inner_gram`).
  The analytic input (that `Ran 𝒱 = Ran P` and `K ≥ c₀ > 0`) is *not* formalized here; it is
  the hypothesis `IsUnit K` (or `‖K - 1‖ < 1`, `isUnit_gram_of_norm_sub_one_lt`) and `hM`.
* **§3.3, covariance of the Gram construction**: if `𝒱 σ = S 𝒱` for unitaries `σ, S`, then
  `K`, `K^{-1/2}` commute with `σ` and `𝒰 σ = S 𝒰` (`gram_commute`, `gramInvSqrt_commute`,
  `polar_comp_intertwine`, `polar_apply_intertwine`).
* **Proposition `c-prop:weighted-polar`**, operator-norm version of `c-eq:polar-bound` and
  `c-eq:reference-transfer`: if `‖K - 1‖ ≤ ℓ ≤ 1/2` then `‖K^{-1/2} - 1‖ ≤ ℓ` (so `C = 1`)
  (`norm_gramInvSqrt_sub_one_le`), `‖K^{-1/2}‖ ≤ (1-ℓ)^{-1/2}` (`norm_rpow_neg_half_le`),
  `‖K^{-1/2} J K^{-1/2}‖ ≤ ‖J‖/(1-ℓ)` (`norm_gramInvSqrt_conj_le`) and
  `‖K^{-1/2} J K^{-1/2} - T‖ ≤ ‖J-T‖/(1-ℓ) + 3ℓ‖T‖` (`norm_gramInvSqrt_conj_sub_le`).
  The compression identity `𝒰* T 𝒰 = K^{-1/2} (𝒱* T 𝒱) K^{-1/2}` (the last identity of
  `c-eq:exact-residual-formulas`, for bounded `T`) is `adjoint_polar_comp_comp_polar`.
  The weighted-algebra norm `‖·‖_{a,h}` is not treated here; only the `ℓ² → ℓ²` operator norm.
-/
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric

noncomputable section
open ContinuousLinearMap
namespace CMS
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The Gram operator `K = 𝒱* 𝒱` (paper `c-eq:correct-gram`). -/
def gram (Vh : E →L[ℂ] F) : E →L[ℂ] E := adjoint Vh ∘L Vh
/-- `K^{-1/2}`, defined by the continuous functional calculus (`CFC.rpow`). -/
def gramInvSqrt (Vh : E →L[ℂ] F) : E →L[ℂ] E := (gram Vh) ^ (-(1/2 : ℝ))
/-- The polar isometry `𝒰 = 𝒱 K^{-1/2}` (paper `c-eq:correct-gram`). -/
def polar (Vh : E →L[ℂ] F) : E →L[ℂ] F := Vh ∘L gramInvSqrt Vh

lemma gram_nonneg (Vh : E →L[ℂ] F) : 0 ≤ gram Vh :=
  nonneg_iff_isPositive.mpr (isPositive_adjoint_comp_self Vh)

lemma gram_isStrictlyPositive {Vh : E →L[ℂ] F} (hK : IsUnit (gram Vh)) :
    IsStrictlyPositive (gram Vh) := hK.isStrictlyPositive (gram_nonneg Vh)

lemma gramInvSqrt_nonneg (Vh : E →L[ℂ] F) : 0 ≤ gramInvSqrt Vh := CFC.rpow_nonneg

lemma adjoint_gramInvSqrt (Vh : E →L[ℂ] F) : adjoint (gramInvSqrt Vh) = gramInvSqrt Vh := by
  rw [← star_eq_adjoint]; exact (IsSelfAdjoint.of_nonneg (gramInvSqrt_nonneg Vh)).star_eq

lemma isUnit_gramInvSqrt {Vh : E →L[ℂ] F} (hK : IsUnit (gram Vh)) :
    IsUnit (gramInvSqrt Vh) :=
  (IsStrictlyPositive.rpow (gram Vh) (-(1/2 : ℝ)) (gram_isStrictlyPositive hK)).isUnit

lemma gramInvSqrt_mul_gram_mul {Vh : E →L[ℂ] F} (hK : IsUnit (gram Vh)) :
    gramInvSqrt Vh * gram Vh * gramInvSqrt Vh = 1 := by
  have h1 : gram Vh = gram Vh ^ (1 : ℝ) := (CFC.rpow_one _ (gram_nonneg Vh)).symm
  unfold gramInvSqrt
  calc gram Vh ^ (-(1/2 : ℝ)) * gram Vh * gram Vh ^ (-(1/2 : ℝ))
      = gram Vh ^ (-(1/2 : ℝ)) * gram Vh ^ (1 : ℝ) * gram Vh ^ (-(1/2 : ℝ)) := by rw [← h1]
    _ = gram Vh ^ (-(1/2 : ℝ) + 1 + -(1/2 : ℝ)) := by rw [CFC.rpow_add hK, CFC.rpow_add hK]
    _ = 1 := by norm_num; exact CFC.rpow_zero _ (gram_nonneg Vh)

/-- `𝒰* 𝒰 = 1`: the polar factor is an isometry (Prop. `c-prop:projected-completeness`). -/
theorem adjoint_polar_comp_polar {Vh : E →L[ℂ] F} (hK : IsUnit (gram Vh)) :
    adjoint (polar Vh) ∘L polar Vh = 1 := by
  have := gramInvSqrt_mul_gram_mul hK
  simp only [polar, adjoint_comp, adjoint_gramInvSqrt]
  rw [← this]; rfl

/-- `‖𝒰 x‖ = ‖x‖`. -/
theorem norm_polar_apply {Vh : E →L[ℂ] F} (hK : IsUnit (gram Vh)) (x : E) :
    ‖polar Vh x‖ = ‖x‖ :=
  (norm_map_iff_adjoint_comp_self (polar Vh)).mpr (adjoint_polar_comp_polar hK) x

theorem isometry_polar {Vh : E →L[ℂ] F} (hK : IsUnit (gram Vh)) : Isometry (polar Vh) :=
  (isometry_iff_adjoint_comp_self _).mpr (adjoint_polar_comp_polar hK)

/-- `Ran 𝒰 = Ran 𝒱`, since `K^{-1/2}` is invertible. -/
theorem range_polar {Vh : E →L[ℂ] F} (hK : IsUnit (gram Vh)) :
    LinearMap.range (polar Vh : E →ₗ[ℂ] F) = LinearMap.range (Vh : E →ₗ[ℂ] F) := by
  obtain ⟨u, hu⟩ := isUnit_gramInvSqrt hK
  have hsurj : Function.Surjective (gramInvSqrt Vh) := fun y =>
    ⟨(↑u⁻¹ : E →L[ℂ] E) y, by
      rw [← hu]; change ((u : E →L[ℂ] E) * ↑u⁻¹) y = y; simp⟩
  ext y
  simp only [LinearMap.mem_range]
  constructor
  · rintro ⟨x, rfl⟩; exact ⟨_, rfl⟩
  · rintro ⟨x, rfl⟩; obtain ⟨z, rfl⟩ := hsurj x; exact ⟨z, rfl⟩

/-- If `K` is invertible then `𝒱` has closed range. -/
theorem isClosed_range {Vh : E →L[ℂ] F} (hK : IsUnit (gram Vh)) :
    IsClosed (LinearMap.range (Vh : E →ₗ[ℂ] F) : Set F) := by
  rw [← range_polar hK, LinearMap.coe_range]
  exact (isometry_polar hK).isClosedEmbedding.isClosed_range

lemma polar_mem {Vh : E →L[ℂ] F} (hK : IsUnit (gram Vh)) {M : Submodule ℂ F}
    (hM : LinearMap.range (Vh : E →ₗ[ℂ] F) = M) (x : E) : polar Vh x ∈ M := by
  rw [← hM, ← range_polar hK]; exact LinearMap.mem_range_self _ x

/-- `𝒰` as a unitary from `E` onto any submodule `M = Ran 𝒱` (the paper's `Ran P`). -/
def polarEquiv {Vh : E →L[ℂ] F} (hK : IsUnit (gram Vh)) (M : Submodule ℂ F)
    (hM : LinearMap.range (Vh : E →ₗ[ℂ] F) = M) : E ≃ₗᵢ[ℂ] M :=
  { LinearEquiv.ofBijective ((polar Vh : E →ₗ[ℂ] F).codRestrict M (polar_mem hK hM))
      ⟨fun x y hxy => (isometry_polar hK).injective (congrArg Subtype.val hxy), by
        rintro ⟨y, hy⟩
        rw [← hM, ← range_polar hK] at hy
        obtain ⟨x, rfl⟩ := hy
        exact ⟨x, rfl⟩⟩ with
    norm_map' := fun x => norm_polar_apply hK x }

@[simp] lemma polarEquiv_apply {Vh : E →L[ℂ] F} (hK : IsUnit (gram Vh)) (M : Submodule ℂ F)
    (hM : LinearMap.range (Vh : E →ₗ[ℂ] F) = M) (x : E) : (polarEquiv hK M hM x : F) = polar Vh x := rfl

/-- The exact well basis `φ_j = 𝒰 δ_j`: a Hilbert basis of `M = Ran 𝒱`
(Prop. `c-prop:projected-completeness`). -/
def polarBasis {ι : Type*} {Vh : E →L[ℂ] F} (hK : IsUnit (gram Vh)) (M : Submodule ℂ F)
    (hM : LinearMap.range (Vh : E →ₗ[ℂ] F) = M) (b : HilbertBasis ι ℂ E) : HilbertBasis ι ℂ M :=
  HilbertBasis.ofRepr ((polarEquiv hK M hM).symm.trans b.repr)

/-- `φ_j = 𝒰 (b j)`. -/
theorem polarBasis_apply {ι : Type*} {Vh : E →L[ℂ] F} (hK : IsUnit (gram Vh))
    (M : Submodule ℂ F) (hM : LinearMap.range (Vh : E →ₗ[ℂ] F) = M) (b : HilbertBasis ι ℂ E) (j : ι) :
    (polarBasis hK M hM b j : F) = polar Vh (b j) := by
  classical
  rw [← HilbertBasis.repr_symm_single, ← b.repr_symm_single]
  rfl

/-- Gram entries: `⟪𝒱 x, 𝒱 y⟫ = ⟪x, K y⟫`; for basis vectors, `⟪v_l, v_j⟫ = ⟪δ_l, K δ_j⟫`. -/
theorem inner_map_map_eq_inner_gram (Vh : E →L[ℂ] F) (x y : E) :
    inner ℂ (Vh x) (Vh y) = inner ℂ x (gram Vh y) :=
  (adjoint_inner_right Vh x (Vh y)).symm

/-- Expansion `φ_j = Σ_l (K^{-1/2})_{lj} v_l`, `v_l = 𝒱 δ_l`, as a convergent sum. -/
theorem hasSum_polar_apply {ι : Type*} (Vh : E →L[ℂ] F) (b : HilbertBasis ι ℂ E) (j : ι) :
    HasSum (fun l => inner ℂ (b l) (gramInvSqrt Vh (b j)) • Vh (b l)) (polar Vh (b j)) := by
  have := (b.hasSum_repr (gramInvSqrt Vh (b j))).mapL Vh
  simpa [b.repr_apply_apply, polar] using this

/-- A Gram operator within distance `< 1` of the identity is invertible. -/
theorem isUnit_gram_of_norm_sub_one_lt {Vh : E →L[ℂ] F} (h : ‖gram Vh - 1‖ < 1) :
    IsUnit (gram Vh) := by
  have h' : ‖1 - gram Vh‖ < 1 := by rwa [norm_sub_rev]
  simpa using (Units.oneSub (1 - gram Vh) h').isUnit

/-! ### Covariance -/

/-- Covariance (§3.3): if `𝒱 σ = S 𝒱` with `σ, S` unitary, then `K σ = σ K`. -/
theorem gram_commute {Vh : E →L[ℂ] F} {σ : E →L[ℂ] E} {S : F →L[ℂ] F}
    (hσ : σ ∈ unitary (E →L[ℂ] E)) (hS : S ∈ unitary (F →L[ℂ] F))
    (h : Vh ∘L σ = S ∘L Vh) : Commute (gram Vh) σ := by
  have hS' : adjoint S ∘L S = 1 := by
    rw [← star_eq_adjoint]; exact Unitary.star_mul_self_of_mem hS
  have hconj : star σ * gram Vh * σ = gram Vh := by
    rw [star_eq_adjoint]
    change adjoint σ ∘L (adjoint Vh ∘L Vh) ∘L σ = adjoint Vh ∘L Vh
    calc adjoint σ ∘L (adjoint Vh ∘L Vh) ∘L σ = adjoint (Vh ∘L σ) ∘L (Vh ∘L σ) := by
          rw [adjoint_comp]; rfl
      _ = adjoint Vh ∘L (adjoint S ∘L S) ∘L Vh := by rw [h, adjoint_comp]; rfl
      _ = adjoint Vh ∘L Vh := by rw [hS']; rfl
  have hσσ : σ * star σ = 1 := Unitary.mul_star_self_of_mem hσ
  change gram Vh * σ = σ * gram Vh
  calc gram Vh * σ = (σ * star σ) * (gram Vh * σ) := by rw [hσσ, one_mul]
    _ = σ * (star σ * gram Vh * σ) := by simp only [mul_assoc]
    _ = σ * gram Vh := by rw [hconj]

/-- Covariance (§3.3): `K^{-1/2} σ = σ K^{-1/2}`. -/
theorem gramInvSqrt_commute {Vh : E →L[ℂ] F} {σ : E →L[ℂ] E} {S : F →L[ℂ] F}
    (hσ : σ ∈ unitary (E →L[ℂ] E)) (hS : S ∈ unitary (F →L[ℂ] F))
    (h : Vh ∘L σ = S ∘L Vh) : Commute (gramInvSqrt Vh) σ :=
  (gram_commute hσ hS h).cfc_nnreal _

/-- Covariance (§3.3): `𝒰 σ = S 𝒰`. -/
theorem polar_comp_intertwine {Vh : E →L[ℂ] F} {σ : E →L[ℂ] E} {S : F →L[ℂ] F}
    (hσ : σ ∈ unitary (E →L[ℂ] E)) (hS : S ∈ unitary (F →L[ℂ] F))
    (h : Vh ∘L σ = S ∘L Vh) : polar Vh ∘L σ = S ∘L polar Vh := by
  have hc : gramInvSqrt Vh ∘L σ = σ ∘L gramInvSqrt Vh := gramInvSqrt_commute hσ hS h
  simp only [polar]
  rw [comp_assoc, hc, ← comp_assoc, h, comp_assoc]

/-! ### Quantitative bound -/

/-- Scalar inequality `|t^{-1/2} - 1| ≤ ℓ` for `|t - 1| ≤ ℓ ≤ 1/2`. -/
lemma abs_rpow_neg_half_sub_one_le {x ℓ : ℝ} (hx : |x - 1| ≤ ℓ) (hℓ : ℓ ≤ 1/2) :
    |x ^ (-(1/2 : ℝ)) - 1| ≤ ℓ := by
  have hx0 : 1/2 ≤ x := by linarith [(abs_le.mp hx).1]
  have hxpos : 0 < x := by linarith
  rw [Real.rpow_neg hxpos.le, ← Real.sqrt_eq_rpow]
  set s := Real.sqrt x with hs_def
  have hss : s * s = x := Real.mul_self_sqrt hxpos.le
  have hs : (7/10 : ℝ) ≤ s := Real.le_sqrt_of_sq_le (by nlinarith)
  have hspos : 0 < s := by linarith
  have key : s⁻¹ - 1 = (1 - x) / (s * (1 + s)) := by
    rw [← hss]; field_simp; ring
  rw [key, abs_div, abs_of_pos (by positivity : 0 < s * (1 + s)), div_le_iff₀ (by positivity)]
  have h1 : |1 - x| ≤ ℓ := by rw [abs_sub_comm]; exact hx
  have h2 : 1 ≤ s * (1 + s) := by nlinarith
  have hℓ0 : 0 ≤ ℓ := le_trans (abs_nonneg _) hx
  nlinarith

/-- The spectrum of a self-adjoint `a` lies within `‖a - 1‖` of `1`. -/
lemma abs_sub_one_le_of_mem_spectrum {a : E →L[ℂ] E} (ha : IsSelfAdjoint a) {x : ℝ}
    (hx : x ∈ spectrum ℝ a) : |x - 1| ≤ ‖a - 1‖ := by
  have hcfc : cfc (fun t : ℝ => t - 1) a = a - 1 := by
    rw [cfc_sub (fun t : ℝ => t) (fun _ => 1) a, cfc_id' ℝ a, cfc_const_one ℝ a]
  have := norm_apply_le_norm_cfc (fun t : ℝ => t - 1) a hx
  rwa [hcfc, Real.norm_eq_abs] at this

/-- `‖a^{-1/2} - 1‖ ≤ ℓ` when `0 ≤ a` and `‖a - 1‖ ≤ ℓ ≤ 1/2`. -/
theorem norm_rpow_neg_half_sub_one_le {a : E →L[ℂ] E} (ha : 0 ≤ a) {ℓ : ℝ}
    (hK : ‖a - 1‖ ≤ ℓ) (hℓ : ℓ ≤ 1/2) : ‖a ^ (-(1/2 : ℝ)) - 1‖ ≤ ℓ := by
  have hsa : IsSelfAdjoint a := IsSelfAdjoint.of_nonneg ha
  have hspec : ∀ x ∈ spectrum ℝ a, |x - 1| ≤ ℓ := fun x hx =>
    (abs_sub_one_le_of_mem_spectrum hsa hx).trans hK
  have hcont : ContinuousOn (fun t : ℝ => t ^ (-(1/2 : ℝ))) (spectrum ℝ a) := by
    refine ContinuousOn.rpow_const continuousOn_id fun x hx => Or.inl (ne_of_gt ?_)
    have := (abs_le.mp (hspec x hx)).1
    show 0 < x
    linarith
  rw [CFC.rpow_eq_cfc_real ha, ← cfc_const_one ℝ a,
    ← cfc_sub (fun t : ℝ => t ^ (-(1/2 : ℝ))) (fun _ => 1) a]
  refine norm_cfc_le ((norm_nonneg _).trans hK) fun x hx => ?_
  rw [Real.norm_eq_abs]
  exact abs_rpow_neg_half_sub_one_le (hspec x hx) hℓ

/-- Operator-norm version of `c-eq:polar-bound` (with `C = 1`): `‖K^{-1/2} - 1‖ ≤ ℓ`. -/
theorem norm_gramInvSqrt_sub_one_le {Vh : E →L[ℂ] F} {ℓ : ℝ} (hK : ‖gram Vh - 1‖ ≤ ℓ)
    (hℓ : ℓ ≤ 1/2) : ‖gramInvSqrt Vh - 1‖ ≤ ℓ :=
  norm_rpow_neg_half_sub_one_le (gram_nonneg Vh) hK hℓ

/-- `‖a^{-1/2}‖ ≤ (1 - ℓ)^{-1/2}` when `0 ≤ a` and `‖a - 1‖ ≤ ℓ ≤ 1/2`. -/
theorem norm_rpow_neg_half_le {a : E →L[ℂ] E} (ha : 0 ≤ a) {ℓ : ℝ}
    (hK : ‖a - 1‖ ≤ ℓ) (hℓ : ℓ ≤ 1/2) : ‖a ^ (-(1/2 : ℝ))‖ ≤ (1 - ℓ) ^ (-(1/2 : ℝ)) := by
  have hsa : IsSelfAdjoint a := IsSelfAdjoint.of_nonneg ha
  have hspec : ∀ x ∈ spectrum ℝ a, 1 - ℓ ≤ x := fun x hx => by
    have := (abs_le.mp ((abs_sub_one_le_of_mem_spectrum hsa hx).trans hK)).1; linarith
  have hpos : 0 < 1 - ℓ := by linarith
  have hcont : ContinuousOn (fun t : ℝ => t ^ (-(1/2 : ℝ))) (spectrum ℝ a) := by
    refine ContinuousOn.rpow_const continuousOn_id fun x hx => Or.inl (ne_of_gt ?_)
    have := hspec x hx
    show 0 < x
    linarith
  rw [CFC.rpow_eq_cfc_real ha]
  refine norm_cfc_le (Real.rpow_nonneg hpos.le _) fun x hx => ?_
  have hx := hspec x hx
  rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (by linarith) _)]
  exact Real.rpow_le_rpow_of_nonpos hpos hx (by norm_num)

lemma rpow_neg_half_sq {ℓ : ℝ} (hℓ : ℓ < 1) :
    ((1 - ℓ) ^ (-(1/2 : ℝ))) ^ 2 = (1 - ℓ)⁻¹ := by
  have hpos : 0 < 1 - ℓ := by linarith
  rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
  norm_num
  exact Real.rpow_neg_one _

/-- `‖G J G‖ ≤ ‖J‖/(1-ℓ)` when `‖G‖ ≤ (1-ℓ)^{-1/2}`. -/
theorem norm_conj_le {G J : E →L[ℂ] E} {ℓ : ℝ} (hℓ : ℓ < 1)
    (hG : ‖G‖ ≤ (1 - ℓ) ^ (-(1/2 : ℝ))) : ‖G * J * G‖ ≤ ‖J‖ / (1 - ℓ) := by
  have hpos : 0 < 1 - ℓ := by linarith
  set c := (1 - ℓ) ^ (-(1/2 : ℝ))
  have hc2 : c ^ 2 = (1 - ℓ)⁻¹ := rpow_neg_half_sq hℓ
  calc ‖G * J * G‖ ≤ ‖G‖ * ‖J‖ * ‖G‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ c * ‖J‖ * c := by gcongr
    _ = ‖J‖ / (1 - ℓ) := by rw [div_eq_mul_inv, ← hc2]; ring

/-- Operator-norm version of the first bound in `c-eq:polar-bound`:
`‖K^{-1/2} J K^{-1/2}‖ ≤ ‖J‖/(1-ℓ)`. -/
theorem norm_gramInvSqrt_conj_le {Vh : E →L[ℂ] F} {ℓ : ℝ} (hK : ‖gram Vh - 1‖ ≤ ℓ)
    (hℓ : ℓ ≤ 1/2) (J : E →L[ℂ] E) :
    ‖gramInvSqrt Vh * J * gramInvSqrt Vh‖ ≤ ‖J‖ / (1 - ℓ) :=
  norm_conj_le (by linarith) (norm_rpow_neg_half_le (gram_nonneg Vh) hK hℓ)

/-- Operator-norm version of `c-eq:reference-transfer`:
`‖K^{-1/2} J K^{-1/2} - T‖ ≤ ‖J - T‖/(1-ℓ) + 3ℓ‖T‖`. -/
theorem norm_gramInvSqrt_conj_sub_le {Vh : E →L[ℂ] F} {ℓ : ℝ} (hK : ‖gram Vh - 1‖ ≤ ℓ)
    (hℓ : ℓ ≤ 1/2) (J T : E →L[ℂ] E) :
    ‖gramInvSqrt Vh * J * gramInvSqrt Vh - T‖ ≤ ‖J - T‖ / (1 - ℓ) + 3 * ℓ * ‖T‖ := by
  set G := gramInvSqrt Vh
  have hpos : 0 < 1 - ℓ := by linarith
  have hℓ0 : 0 ≤ ℓ := (norm_nonneg _).trans hK
  have hG1 : ‖G - 1‖ ≤ ℓ := norm_gramInvSqrt_sub_one_le hK hℓ
  have hGc : ‖G‖ ≤ (1 - ℓ) ^ (-(1/2 : ℝ)) := norm_rpow_neg_half_le (gram_nonneg Vh) hK hℓ
  have hG2 : ‖G‖ ≤ 2 := by
    have hc2 := rpow_neg_half_sq (show ℓ < 1 by linarith)
    have hc0 : 0 ≤ (1 - ℓ) ^ (-(1/2 : ℝ)) := Real.rpow_nonneg hpos.le _
    have : (1 - ℓ)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ hpos (by norm_num)]; linarith
    nlinarith
  have hid : G * J * G - T = G * (J - T) * G + (G - 1) * T * G + T * (G - 1) := by
    noncomm_ring
  rw [hid]
  have h1 : ‖G * (J - T) * G‖ ≤ ‖J - T‖ / (1 - ℓ) := norm_conj_le (by linarith) hGc
  have h2 : ‖(G - 1) * T * G‖ ≤ ℓ * ‖T‖ * 2 :=
    (norm_mul_le _ _).trans (mul_le_mul ((norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right hG1 (norm_nonneg _))) hG2 (norm_nonneg _) (by positivity))
  have h3 : ‖T * (G - 1)‖ ≤ ‖T‖ * ℓ :=
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hG1 (norm_nonneg _))
  calc _ ≤ ‖G * (J - T) * G‖ + ‖(G - 1) * T * G‖ + ‖T * (G - 1)‖ := norm_add₃_le
    _ ≤ _ := by nlinarith [norm_nonneg T]

/-- Compression identity `𝒰* T 𝒰 = K^{-1/2} (𝒱* T 𝒱) K^{-1/2}`
(cf. `c-eq:exact-residual-formulas`). -/
theorem adjoint_polar_comp_comp_polar (Vh : E →L[ℂ] F) (T : F →L[ℂ] F) :
    adjoint (polar Vh) ∘L T ∘L polar Vh =
      gramInvSqrt Vh ∘L (adjoint Vh ∘L T ∘L Vh) ∘L gramInvSqrt Vh := by
  simp only [polar, adjoint_comp, adjoint_gramInvSqrt]; rfl

/-- Covariance (§3.3) pointwise, e.g. `φ_ν = S_ν φ_0`. -/
theorem polar_apply_intertwine {Vh : E →L[ℂ] F} {σ : E →L[ℂ] E} {S : F →L[ℂ] F}
    (hσ : σ ∈ unitary (E →L[ℂ] E)) (hS : S ∈ unitary (F →L[ℂ] F))
    (h : Vh ∘L σ = S ∘L Vh) (x : E) : polar Vh (σ x) = S (polar Vh x) :=
  congrArg (fun A : E →L[ℂ] F => A x) (polar_comp_intertwine hσ hS h)

end CMS
