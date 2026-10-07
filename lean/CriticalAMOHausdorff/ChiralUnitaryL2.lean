/-
Copyright (c) 2026. Formalization of
  S. Becker, S. Jitomirskaya, I. Krasovsky, "Critical almost Mathieu operator: hidden
  singularity, gap continuity, and the Hausdorff dimension of the spectrum"
  (arXiv:1909.04429v2).

# Theorem 3.1 as a unitary equivalence on `L²(𝕋; ℓ²(ℤ))`  (paper §3, `chiralrepresentthm`)

TeX references (`Arxiv_version-5.tex`): the unitaries `T`, `S`, `U_x`, `R` (3.2)–(3.4)
(`SandT`, `Q`, `R`, lines ~556–567), `S^x` (line ~572), the fibre representations of `M_α` and
`M̃_α` (lines ~578–589), Theorem 3.1 (lines ~619–627) and its proof (lines ~630–692).

`ChiralGauge.lean` proves the intertwining identity pointwise on a class of functions.  Here
Theorem 3.1 is stated literally: there is a unitary `Q = U_1 R U_{1/2}` of `L²(𝕋; ℓ²(ℤ))` with
`Q (T² + T⁻² + S + S⁻¹) Q⁻¹ = M̃_α` as bounded operators.

## The Hilbert space
`L²(𝕋; ℓ²(ℤ))` is realised as `H = ℓ²(ℤ; L²(𝕋))` (`lp (fun _ : ℤ => L2T) 2`), i.e. `φ(n, θ)` with
`φ(n, ·) ∈ L²(𝕋)` and `∑ₙ ‖φ(n,·)‖² < ∞`.  This is the same space by Fubini/Tonelli.  `L²(𝕋)` is
`L2T = Lp ℂ 2 (volume.restrict (Ioc 0 1))`.  The paper represents phases by `θ ∈ [0,1)`, and the
two choices differ by a null set.  This matters because `U_{1/2}` is not `1`-periodic.

## Construction
* `T`, `T⁻¹ = T.symm` (`Top`) shift `n`.  `S^x` (`Sop`) and `U_x` (`Uop`) act fibrewise by
  multiplication with `e(x(θ+nα))` and `e(nx(θ+nα/2))` (`emul`: multiplication by `e(Aθ+B)` on
  `L²(𝕋)`, a unitary).  `Sop_ae` and `Uop_ae` give the pointwise formulas (3.2), (3.3).
* The Fourier transform `F : L²(𝕋) ≃ ℓ²(ℤ)`, `(Ff)(m) = ∫_0^1 e(-mβ) f(β) dβ`
  (`F_apply_integral`), comes from Mathlib's `fourierBasis` on `AddCircle 1`.  It is transported
  along the measure-preserving bijection `(0,1] ≃ ℝ/ℤ` (`J`).  The key identity is `F_emul`:
  multiplication by `e(jθ + B)` shifts the Fourier coefficients.
* `R = W⁻¹ P W`.  Here `W` is the fibrewise Fourier transform and `P` is the unitary
  `(Pc)(n,m) = e(mnα) c(-m,n)` of `ℓ²(ℤ;ℓ²(ℤ))`.  `P` is unitary by a double-series interchange
  (`norm_swapFun`).  `Rop_hasSum` shows that `R` is literally (3.4):
  `(Rφ)(n,·) = ∑_k e^{-2πiknα} (∫_0^1 e^{-2πinβ} φ(k,β) dβ) e^{-2πik·}`, with the sum taken in
  `L²(𝕋)`.
* The relations `(RS)`, `(RS-1)`, `(RTpm1)` (`R_S`, `R_Sinv`, `R_T`, `R_Tinv`) are proved on the
  Fourier side.  The `U`–`S`–`T` relations are fibrewise identities of exponentials (`U_D`,
  `U_M`).  Together they give `Q_D`.

## Main results
* `chiralrepresentthm` — **Theorem 3.1**: `Q ∘ (T²+T⁻²+S+S⁻¹) ∘ Q⁻¹ = M̃_α` as bounded operators,
  where `Q = Qop α = U_1 R U_{1/2}` is a `LinearIsometryEquiv` (a unitary);
* `chiralrepresentthm'` — the existential form;
* `Rop_hasSum` — the formula (3.4) for `R`;
* `Mfun_ae` — `M̃_α` is decomposable with fibres `H̃_{α,θ} = Ĥ_{α,1/4+α/2+θ}`;
* `Dfun_ae` — fibres of `T²+T⁻²+S+S⁻¹`;
* `F_emul`, `norm_swapFun`, `reidx`, `emul` — the supporting unitaries.

There are no `sorry`s and no additional hypotheses in this file.
-/
import CriticalAMOHausdorff.ChiralSpectrum

noncomputable section

open Real Complex MeasureTheory Set
open scoped ComplexConjugate ENNReal

namespace CAH

namespace ChiralL2

/-! ### `ℓ²(ℤ; E)`: reindexing, fibrewise unitaries, the swap -/

/-- `ℓ²(ℤ; E)`. -/
abbrev L2Z (E : Type*) [NormedAddCommGroup E] := lp (fun _ : ℤ => E) 2

lemma two_toReal : (2 : ℝ≥0∞).toReal = 2 := by norm_num

lemma two_toReal_pos : 0 < (2 : ℝ≥0∞).toReal := by norm_num

section Generic

variable {G G' : Type*} [NormedAddCommGroup G] [NormedAddCommGroup G']

lemma memℓp_two_iff {f : ℤ → G} : Memℓp f 2 ↔ Summable fun n => ‖f n‖ ^ 2 := by
  rw [memℓp_gen_iff two_toReal_pos, two_toReal]
  simp only [Real.rpow_two]

lemma norm_sq_eq_tsum' (f : L2Z G) : ‖f‖ ^ 2 = ∑' n, ‖f n‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum two_toReal_pos f
  rw [two_toReal] at h
  simpa only [Real.rpow_two] using h

lemma summable_sq (f : L2Z G) : Summable fun n => ‖f n‖ ^ 2 := memℓp_two_iff.1 f.2

lemma norm_eq_of_tsum {f : L2Z G} {g : L2Z G'}
    (h : ∑' n, ‖f n‖ ^ 2 = ∑' n, ‖g n‖ ^ 2) : ‖f‖ = ‖g‖ := by
  rw [← Real.sqrt_sq (norm_nonneg f), ← Real.sqrt_sq (norm_nonneg g), norm_sq_eq_tsum',
    norm_sq_eq_tsum', h]

end Generic

section Reidx

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F]

/-- `(f ↦ (n ↦ V_n (f (e n))))` on `ℓ²(ℤ; E)`. -/
def reidxFun (e : ℤ ≃ ℤ) (V : ℤ → E ≃ₗᵢ[ℂ] F) (f : L2Z E) : L2Z F :=
  ⟨fun n => V n (f (e n)), by
    show Memℓp _ 2
    rw [memℓp_two_iff]
    simp only [LinearIsometryEquiv.norm_map]
    exact (e.summable_iff (f := fun n => ‖f n‖ ^ 2)).2 (summable_sq f)⟩

@[simp] lemma reidxFun_apply (e : ℤ ≃ ℤ) (V : ℤ → E ≃ₗᵢ[ℂ] F) (f : L2Z E) (n : ℤ) :
    reidxFun e V f n = V n (f (e n)) := rfl

/-- Reindexing combined with fibrewise unitaries, as a unitary `ℓ²(ℤ;E) ≃ ℓ²(ℤ;F)`. -/
def reidx (e : ℤ ≃ ℤ) (V : ℤ → E ≃ₗᵢ[ℂ] F) : L2Z E ≃ₗᵢ[ℂ] L2Z F where
  toFun := reidxFun e V
  invFun := reidxFun e.symm (fun n => (V (e.symm n)).symm)
  map_add' f g := lp.ext (funext fun n => by simp)
  map_smul' c f := lp.ext (funext fun n => by simp)
  left_inv f := lp.ext (funext fun n => by simp)
  right_inv g := lp.ext (funext fun n => by simp)
  norm_map' f := norm_eq_of_tsum (by
    show ∑' n, ‖V n (f (e n))‖ ^ 2 = _
    simp only [LinearIsometryEquiv.norm_map]
    exact e.tsum_eq (fun n => ‖f n‖ ^ 2))

@[simp] lemma reidx_apply (e : ℤ ≃ ℤ) (V : ℤ → E ≃ₗᵢ[ℂ] F) (f : L2Z E) (n : ℤ) :
    reidx e V f n = V n (f (e n)) := rfl

@[simp] lemma reidx_symm_apply (e : ℤ ≃ ℤ) (V : ℤ → E ≃ₗᵢ[ℂ] F) (g : L2Z F) (n : ℤ) :
    (reidx e V).symm g n = (V (e.symm n)).symm (g (e.symm n)) := rfl

end Reidx

section UnitSmul

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Multiplication by a unimodular scalar, as a unitary. -/
def unitSmul (z : ℂ) (hz : ‖z‖ = 1) : E ≃ₗᵢ[ℂ] E where
  toFun x := z • x
  invFun x := conj z • x
  map_add' := smul_add z
  map_smul' c x := smul_comm z c x
  left_inv x := by
    simp only [smul_smul, Complex.conj_mul', hz]
    simp
  right_inv x := by
    simp only [smul_smul, Complex.mul_conj', hz]
    simp
  norm_map' x := by simp [norm_smul, hz]

@[simp] lemma unitSmul_apply (z : ℂ) (hz : ‖z‖ = 1) (x : E) : unitSmul z hz x = z • x := rfl

end UnitSmul

section Swap

/-- `‖c k j‖² ≤ ‖c k‖²`. -/
lemma sq_le_norm_sq (c : L2Z (L2Z ℂ)) (k j : ℤ) : ‖c k j‖ ^ 2 ≤ ‖c k‖ ^ 2 :=
  pow_le_pow_left₀ (norm_nonneg _) (lp.norm_apply_le_norm (by norm_num) _ _) 2

variable (σ₁ σ₂ : ℤ ≃ ℤ) (w : ℤ → ℤ → ℂ) (hw : ∀ n m, ‖w n m‖ = 1)

/-- The `n`-th fibre of the swap: `m ↦ w(n,m) c(σ₁ m)(σ₂ n)`. -/
def swapInner (c : L2Z (L2Z ℂ)) (n : ℤ) : L2Z ℂ :=
  ⟨fun m => w n m * c (σ₁ m) (σ₂ n), by
    show Memℓp _ 2
    rw [memℓp_two_iff]
    simp only [norm_mul, hw, one_mul]
    exact Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun m => sq_le_norm_sq c _ _)
      ((σ₁.summable_iff (f := fun k => ‖c k‖ ^ 2)).2 (summable_sq c))⟩

@[simp] lemma swapInner_apply (c : L2Z (L2Z ℂ)) (n m : ℤ) :
    swapInner σ₁ σ₂ w hw c n m = w n m * c (σ₁ m) (σ₂ n) := rfl

lemma norm_swapInner_sq (c : L2Z (L2Z ℂ)) (n : ℤ) :
    ‖swapInner σ₁ σ₂ w hw c n‖ ^ 2 = ∑' k, ‖c k (σ₂ n)‖ ^ 2 := by
  rw [norm_sq_eq_tsum']
  simp only [swapInner_apply, norm_mul, hw, one_mul]
  exact σ₁.tsum_eq (fun k => ‖c k (σ₂ n)‖ ^ 2)

lemma summable_uncurry_sq (c : L2Z (L2Z ℂ)) :
    Summable (Function.uncurry fun k j => ‖c k j‖ ^ 2) := by
  refine (summable_prod_of_nonneg (fun _ => sq_nonneg _)).2 ⟨fun k => summable_sq (c k), ?_⟩
  simp_rw [← norm_sq_eq_tsum']
  exact summable_sq c

lemma summable_swap_sq (c : L2Z (L2Z ℂ)) : Summable fun j => ∑' k, ‖c k j‖ ^ 2 := by
  have h := (summable_uncurry_sq c).prod_symm
  have h2 := ((summable_prod_of_nonneg (fun _ => sq_nonneg _)).1 h).2
  simpa only [Prod.swap_prod_mk, Function.uncurry_apply_pair] using h2

/-- The swap `c ↦ (n ↦ (m ↦ w(n,m) c(σ₁ m)(σ₂ n)))` on `ℓ²(ℤ;ℓ²(ℤ))`. -/
def swapFun (c : L2Z (L2Z ℂ)) : L2Z (L2Z ℂ) :=
  ⟨fun n => swapInner σ₁ σ₂ w hw c n, by
    show Memℓp _ 2
    rw [memℓp_two_iff]
    simp only [norm_swapInner_sq]
    exact (σ₂.summable_iff (f := fun j => ∑' k, ‖c k j‖ ^ 2)).2 (summable_swap_sq c)⟩

@[simp] lemma swapFun_apply (c : L2Z (L2Z ℂ)) (n m : ℤ) :
    swapFun σ₁ σ₂ w hw c n m = w n m * c (σ₁ m) (σ₂ n) := rfl

lemma norm_swapFun (c : L2Z (L2Z ℂ)) : ‖swapFun σ₁ σ₂ w hw c‖ = ‖c‖ := by
  refine norm_eq_of_tsum ?_
  show ∑' n, ‖swapInner σ₁ σ₂ w hw c n‖ ^ 2 = _
  simp only [norm_swapInner_sq]
  rw [σ₂.tsum_eq (fun j => ∑' k, ‖c k j‖ ^ 2), (summable_uncurry_sq c).tsum_comm]
  simp_rw [← norm_sq_eq_tsum']

end Swap

/-! ### `L²(0,1)` and multiplication by exponentials -/

instance factOnePos : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩

/-- Lebesgue measure on `(0,1]` (the paper's representatives `θ ∈ [0,1)` of `𝕋`, up to a null
set). -/
abbrev μT : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)

/-- `L²(𝕋)`, realised as `L²((0,1])`. -/
abbrev L2T := Lp ℂ 2 μT

lemma memLp_emul (A B : ℝ) (f : L2T) : MemLp (fun x => ex (A * x + B) * f x) 2 μT := by
  have hc : Continuous fun x : ℝ => ex (A * x + B) := by fun_prop
  have hm : AEStronglyMeasurable (fun x => ex (A * x + B) * f x) μT :=
    hc.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f)
  refine (Lp.memLp f).of_le hm (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_mul, norm_ex, one_mul]

/-- Multiplication by `e(Aθ + B)` on `L²(𝕋)` (as a function). -/
def emulF (A B : ℝ) (f : L2T) : L2T := (memLp_emul A B f).toLp _

lemma emulF_ae (A B : ℝ) (f : L2T) : emulF A B f =ᵐ[μT] fun x => ex (A * x + B) * f x :=
  (memLp_emul A B f).coeFn_toLp

lemma emulF_emulF (A B A' B' : ℝ) (f : L2T) :
    emulF A B (emulF A' B' f) = emulF (A + A') (B + B') f := by
  apply Lp.ext
  filter_upwards [emulF_ae A B (emulF A' B' f), emulF_ae A' B' f,
    emulF_ae (A + A') (B + B') f] with x h1 h2 h3
  rw [h1, h2, h3, ← mul_assoc, ← ex_add]
  congr 2; ring

lemma emulF_zero (f : L2T) : emulF 0 0 f = f := by
  apply Lp.ext
  filter_upwards [emulF_ae 0 0 f] with x h1
  rw [h1]; simp [ex]

lemma emulF_add (A B : ℝ) (f g : L2T) : emulF A B (f + g) = emulF A B f + emulF A B g := by
  apply Lp.ext
  filter_upwards [emulF_ae A B (f + g), Lp.coeFn_add f g, Lp.coeFn_add (emulF A B f) (emulF A B g),
    emulF_ae A B f, emulF_ae A B g] with x h1 h2 h3 h4 h5
  rw [h1, h3, Pi.add_apply, h4, h5, h2, Pi.add_apply, mul_add]

lemma emulF_smul (A B : ℝ) (c : ℂ) (f : L2T) : emulF A B (c • f) = c • emulF A B f := by
  apply Lp.ext
  filter_upwards [emulF_ae A B (c • f), Lp.coeFn_smul c f, Lp.coeFn_smul c (emulF A B f),
    emulF_ae A B f] with x h1 h2 h3 h4
  rw [h1, h3, Pi.smul_apply, h4, h2, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  ring

lemma norm_emulF (A B : ℝ) (f : L2T) : ‖emulF A B f‖ = ‖f‖ := by
  rw [emulF, Lp.norm_toLp, Lp.norm_def]
  congr 1
  have hc : Continuous fun x : ℝ => ex (A * x + B) := by fun_prop
  refine eLpNorm_congr_norm_ae (hc.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
    (Lp.aestronglyMeasurable f) (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_mul, norm_ex, one_mul]

/-- Multiplication by `e(Aθ + B)`, a unitary operator on `L²(𝕋)`. -/
def emul (A B : ℝ) : L2T ≃ₗᵢ[ℂ] L2T where
  toFun := emulF A B
  invFun := emulF (-A) (-B)
  map_add' := emulF_add A B
  map_smul' := emulF_smul A B
  left_inv f := by rw [emulF_emulF, neg_add_cancel, neg_add_cancel, emulF_zero]
  right_inv f := by rw [emulF_emulF, add_neg_cancel, add_neg_cancel, emulF_zero]
  norm_map' := norm_emulF A B

lemma emul_apply (A B : ℝ) (f : L2T) : emul A B f = emulF A B f := rfl

lemma emul_ae (A B : ℝ) (f : L2T) : emul A B f =ᵐ[μT] fun x => ex (A * x + B) * f x :=
  emulF_ae A B f

lemma emul_emul (A B A' B' : ℝ) (f : L2T) :
    emul A B (emul A' B' f) = emul (A + A') (B + B') f := emulF_emulF A B A' B' f

lemma smul_emul (c A B : ℝ) (f : L2T) : ex c • emul A B f = emul A (c + B) f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_smul (ex c) (emul A B f), emul_ae A B f, emul_ae A (c + B) f]
    with x h1 h2 h3
  rw [h1, Pi.smul_apply, h2, h3, smul_eq_mul, ← mul_assoc, ← ex_add]
  congr 2; ring

lemma emul_congr {A B A' B' : ℝ} (hA : A = A') (hB : B = B') (f : L2T) :
    emul A B f = emul A' B' f := by rw [hA, hB]

/-! ### The Fourier transform `L²(𝕋) ≃ ℓ²(ℤ)` -/

lemma volume_eq_haar : (volume : Measure (AddCircle (1 : ℝ))) = AddCircle.haarAddCircle := by
  rw [AddCircle.volume_eq_smul_haarAddCircle, ENNReal.ofReal_one, one_smul]

lemma mp_mk : MeasurePreserving (fun x : ℝ => (x : AddCircle (1 : ℝ))) μT
    AddCircle.haarAddCircle := by
  have h := AddCircle.measurePreserving_mk (1 : ℝ) 0
  rw [zero_add, volume_eq_haar] at h
  exact h

/-- The representative in `(0,1]` of a point of `𝕋 = ℝ/ℤ`. -/
def rep (y : AddCircle (1 : ℝ)) : ℝ := (AddCircle.equivIoc 1 0 y : ℝ)

lemma mp_rep : MeasurePreserving rep AddCircle.haarAddCircle μT := by
  have h1 := AddCircle.measurePreserving_equivIoc (T := 1) (a := 0)
  have h2 := measurePreserving_subtype_coe (μa := (volume : Measure ℝ))
    (measurableSet_Ioc (a := (0 : ℝ)) (b := 0 + 1))
  have h := h2.comp h1
  rw [volume_eq_haar] at h
  refine ⟨h.measurable, ?_⟩
  rw [show rep = Subtype.val ∘ AddCircle.equivIoc 1 0 from rfl, h.map_eq, zero_add]

lemma rep_mk {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) : rep (x : AddCircle (1 : ℝ)) = x := by
  have hx' : x ∈ Ioc (0 : ℝ) (0 + 1) := by rwa [zero_add]
  rw [rep, AddCircle.equivIoc_coe_eq hx']

/-- `L²(𝕋, haar) → L²((0,1])`, `g ↦ g ∘ mk`. -/
def Jli : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)) →ₗᵢ[ℂ] L2T :=
  Lp.compMeasurePreservingₗᵢ ℂ _ mp_mk

/-- `L²((0,1]) → L²(𝕋, haar)`, `f ↦ f ∘ rep`. -/
def Jinv : L2T →ₗᵢ[ℂ] Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)) :=
  Lp.compMeasurePreservingₗᵢ ℂ rep mp_rep

lemma Jli_ae (g : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) :
    Jli g =ᵐ[μT] fun x => g (x : AddCircle (1 : ℝ)) :=
  Lp.coeFn_compMeasurePreserving g mp_mk

lemma Jli_Jinv (f : L2T) : Jli (Jinv f) = f := by
  apply Lp.ext
  have h2 : (Jinv f : AddCircle (1 : ℝ) → ℂ) =ᵐ[AddCircle.haarAddCircle] f ∘ rep :=
    Lp.coeFn_compMeasurePreserving f mp_rep
  have h3 := mp_mk.quasiMeasurePreserving.ae_eq_comp h2
  have h4 : ∀ᵐ x ∂μT, x ∈ Ioc (0 : ℝ) 1 := ae_restrict_mem measurableSet_Ioc
  filter_upwards [Jli_ae (Jinv f), h3, h4] with x hx1 hx3 hx4
  rw [hx1]
  simp only [Function.comp] at hx3
  rw [hx3, rep_mk hx4]

/-- `L²(𝕋, haar) ≃ L²((0,1])`. -/
def J : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)) ≃ₗᵢ[ℂ] L2T :=
  LinearIsometryEquiv.ofSurjective Jli (fun f => ⟨Jinv f, Jli_Jinv f⟩)

lemma J_apply (g : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) : J g = Jli g := rfl

/-- The exponential `e_m(θ) = e(mθ)` in `L²(𝕋)`. -/
def eL (m : ℤ) : L2T := J (fourierLp (T := 1) 2 m)

lemma eL_ae (m : ℤ) : eL m =ᵐ[μT] fun x => ex (m * x) := by
  have h1 := Jli_ae (fourierLp (T := 1) 2 m)
  have h2 := mp_mk.quasiMeasurePreserving.ae_eq_comp (coeFn_fourierLp (T := 1) 2 m)
  filter_upwards [h1, h2] with x hx1 hx2
  rw [eL, J_apply, hx1]
  simp only [Function.comp] at hx2
  rw [hx2, fourier_coe_apply]
  simp only [ex]
  congr 1; push_cast; ring

/-- The Fourier transform `F : L²(𝕋) ≃ ℓ²(ℤ)`, `(Ff)(m) = ∫_0^1 e(-mβ) f(β) dβ`. -/
def F : L2T ≃ₗᵢ[ℂ] L2Z ℂ := J.symm.trans fourierBasis.repr

lemma F_apply (f : L2T) (m : ℤ) : F f m = inner ℂ (eL m) f := by
  rw [F, LinearIsometryEquiv.trans_apply, HilbertBasis.repr_apply_apply, coe_fourierBasis,
    ← J.inner_map_map, LinearIsometryEquiv.apply_symm_apply]
  rfl

lemma inner_eL (m : ℤ) (f : L2T) :
    inner ℂ (eL m) f = ∫ x, ex (-(m * x)) * f x ∂μT := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [eL_ae m] with x hx
  rw [hx, RCLike.inner_apply, conj_ex]
  ring

/-- `(Ff)(m) = ∫_0^1 e(-mβ) f(β) dβ`. -/
theorem F_apply_integral (f : L2T) (m : ℤ) : F f m = ∫ x in Ioc (0 : ℝ) 1, ex (-(m * x)) * f x :=
  by rw [F_apply, inner_eL]

/-- **Multiplication by `e(jθ + B)` shifts Fourier coefficients:**
`F(e(jθ+B) f)(m) = e(B) (Ff)(m - j)`. -/
theorem F_emul (j : ℤ) (B : ℝ) (f : L2T) (m : ℤ) :
    F (emul j B f) m = ex B * F f (m - j) := by
  rw [F_apply, F_apply, inner_eL, inner_eL, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [emul_ae j B f] with x hx
  rw [hx]
  have e : ex (-(m * x)) * ex (j * x + B) = ex B * ex (-(((m - j : ℤ) : ℝ) * x)) := by
    rw [← ex_add, ← ex_add]; congr 1; push_cast; ring
  linear_combination (f x) * e

/-! ### The operators `T`, `S^x`, `U_x`, `R`, `Q` on `L²(𝕋; ℓ²(ℤ))` -/

/-- The paper's Hilbert space `L²(𝕋; ℓ²(ℤ))`, realised as `ℓ²(ℤ; L²(𝕋))`: `φ(n, θ)`. -/
abbrev H := L2Z L2T

/-- The Fourier side `ℓ²(ℤ; ℓ²(ℤ))`. -/
abbrev Hc := L2Z (L2Z ℂ)

variable (α : ℝ)

/-- `(Tφ)(n,θ) = φ(n+1,θ)` (3.2). -/
def Top : H ≃ₗᵢ[ℂ] H := reidx (Equiv.addRight 1) (fun _ => LinearIsometryEquiv.refl ℂ L2T)

/-- `(S^xφ)(n,θ) = e^{2πix(θ+nα)} φ(n,θ)`; `S = S^1`, `S⁻¹ = S^{-1}` (3.2). -/
def Sop (x : ℝ) : H ≃ₗᵢ[ℂ] H := reidx (Equiv.refl ℤ) (fun n => emul x (x * n * α))

/-- `(U_xφ)(n,θ) = e^{2πinx(θ+nα/2)} φ(n,θ)` (3.3). -/
def Uop (x : ℝ) : H ≃ₗᵢ[ℂ] H :=
  reidx (Equiv.refl ℤ) (fun n => emul (n * x) (n * x * (n * α / 2)))

/-- The fibrewise Fourier transform `L²(𝕋; ℓ²(ℤ)) ≃ ℓ²(ℤ; ℓ²(ℤ))`. -/
def Wop : H ≃ₗᵢ[ℂ] Hc := reidx (Equiv.refl ℤ) (fun _ => F)

/-- The shift on the Fourier side. -/
def Tc : Hc ≃ₗᵢ[ℂ] Hc := reidx (Equiv.addRight 1) (fun _ => LinearIsometryEquiv.refl ℂ (L2Z ℂ))

/-- The shift on `ℓ²(ℤ)`. -/
def lsh (k : ℤ) : L2Z ℂ ≃ₗᵢ[ℂ] L2Z ℂ :=
  reidx (Equiv.addRight k) (fun _ => LinearIsometryEquiv.refl ℂ ℂ)

/-- `S^s` (`s ∈ ℤ`) on the Fourier side: `c(k, m) ↦ e(skα) c(k, m - s)`. -/
def Sc (s : ℤ) : Hc ≃ₗᵢ[ℂ] Hc :=
  reidx (Equiv.refl ℤ) (fun k => (lsh (-s)).trans (unitSmul (ex (s * k * α)) (norm_ex _)))

/-- `R` on the Fourier side: `(Pc)(n, m) = e(mnα) c(-m, n)`. -/
def PcFun (c : Hc) : Hc :=
  swapFun (Equiv.neg ℤ) (Equiv.refl ℤ) (fun n m => ex (m * n * α)) (fun _ _ => norm_ex _) c

/-- The inverse of `PcFun`: `(P⁻¹d)(k, n) = e(knα) d(n, -k)`. -/
def PcInvFun (d : Hc) : Hc :=
  swapFun (Equiv.refl ℤ) (Equiv.neg ℤ) (fun k n => ex (k * n * α)) (fun _ _ => norm_ex _) d

lemma PcFun_apply (c : Hc) (n m : ℤ) : PcFun α c n m = ex (m * n * α) * c (-m) n := rfl

lemma PcInvFun_apply (d : Hc) (k n : ℤ) : PcInvFun α d k n = ex (k * n * α) * d n (-k) := rfl

lemma ex_mul_ex_neg (t : ℝ) : ex t * ex (-t) = 1 := by
  rw [← ex_add, add_neg_cancel]; simp [ex]

/-- `R` on the Fourier side, a unitary of `ℓ²(ℤ; ℓ²(ℤ))`. -/
def Pc : Hc ≃ₗᵢ[ℂ] Hc where
  toFun := PcFun α
  invFun := PcInvFun α
  map_add' c d := lp.ext (funext fun n => lp.ext (funext fun m => by
    simp only [PcFun_apply, lp.coeFn_add, Pi.add_apply]; ring))
  map_smul' z c := lp.ext (funext fun n => lp.ext (funext fun m => by
    simp only [PcFun_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring))
  left_inv c := lp.ext (funext fun k => lp.ext (funext fun n => by
    show ex (k * n * α) * (ex (((-k : ℤ) : ℝ) * n * α) * c (-(-k)) n) = c k n
    rw [neg_neg]
    have e : ex (k * n * α) * ex (((-k : ℤ) : ℝ) * n * α) = 1 := by
      rw [show ((-k : ℤ) : ℝ) * n * α = -(k * n * α) by push_cast; ring, ex_mul_ex_neg]
    linear_combination (c k n) * e))
  right_inv d := lp.ext (funext fun n => lp.ext (funext fun m => by
    show ex (m * n * α) * (ex (((-m : ℤ) : ℝ) * n * α) * d n (-(-m))) = d n m
    rw [neg_neg]
    have e : ex (m * n * α) * ex (((-m : ℤ) : ℝ) * n * α) = 1 := by
      rw [show ((-m : ℤ) : ℝ) * n * α = -(m * n * α) by push_cast; ring, ex_mul_ex_neg]
    linear_combination (d n m) * e))
  norm_map' := norm_swapFun _ _ _ _

/-- `(Rφ)(n,θ) = ∑_k e^{-2πik(θ+nα)} ∫_𝕋 e^{-2πinβ} φ(k,β) dβ` (3.4), realised as
`W⁻¹ ∘ P ∘ W` (see `Rop_hasSum` for the literal formula). -/
def Rop : H ≃ₗᵢ[ℂ] H := ((Wop).trans (Pc α)).trans (Wop).symm

/-- `Q = U_1 R U_{1/2}` (Theorem 3.1). -/
def Qop : H ≃ₗᵢ[ℂ] H := ((Uop α (1 / 2)).trans (Rop α)).trans (Uop α 1)

@[simp] lemma Top_apply (φ : H) (n : ℤ) : Top φ n = φ (n + 1) := rfl
@[simp] lemma Top_symm_apply (φ : H) (n : ℤ) : Top.symm φ n = φ (n - 1) := rfl
@[simp] lemma Sop_apply (x : ℝ) (φ : H) (n : ℤ) : Sop α x φ n = emul x (x * n * α) (φ n) := rfl
@[simp] lemma Uop_apply (x : ℝ) (φ : H) (n : ℤ) :
    Uop α x φ n = emul (n * x) (n * x * (n * α / 2)) (φ n) := rfl
lemma Wop_apply (φ : H) (n : ℤ) : Wop φ n = F (φ n) := rfl
lemma Wop_symm_apply (c : Hc) (n : ℤ) : Wop.symm c n = F.symm (c n) := rfl
lemma Tc_apply (c : Hc) (n : ℤ) : Tc c n = c (n + 1) := rfl
lemma Tc_symm_apply (c : Hc) (n : ℤ) : Tc.symm c n = c (n - 1) := rfl
lemma Sc_apply (s : ℤ) (c : Hc) (k m : ℤ) : Sc α s c k m = ex (s * k * α) * c k (m + -s) := rfl
lemma Pc_apply (c : Hc) (n m : ℤ) : Pc α c n m = ex (m * n * α) * c (-m) n := rfl
lemma Rop_apply (φ : H) : Rop α φ = Wop.symm (Pc α (Wop φ)) := rfl
lemma Qop_apply (φ : H) : Qop α φ = Uop α 1 (Rop α (Uop α (1 / 2) φ)) := rfl

/-! #### Fibre formulas: the operators are the paper's -/

lemma Sop_ae (x : ℝ) (φ : H) (n : ℤ) :
    Sop α x φ n =ᵐ[μT] fun θ => ex (x * (θ + n * α)) * φ n θ := by
  filter_upwards [emul_ae x (x * n * α) (φ n)] with θ h
  rw [Sop_apply, h]; congr 2; ring

lemma Uop_ae (x : ℝ) (φ : H) (n : ℤ) :
    Uop α x φ n =ᵐ[μT] fun θ => ex (n * x * (θ + n * α / 2)) * φ n θ := by
  filter_upwards [emul_ae (n * x) (n * x * (n * α / 2)) (φ n)] with θ h
  rw [Uop_apply, h]; congr 2; ring

/-! #### Relations on the Fourier side -/

lemma W_T (φ : H) : Wop (Top φ) = Tc (Wop φ) := rfl
lemma W_Tsymm (φ : H) : Wop (Top.symm φ) = Tc.symm (Wop φ) := rfl
lemma Wsymm_Tc (c : Hc) : Wop.symm (Tc c) = Top (Wop.symm c) := rfl
lemma Wsymm_Tcsymm (c : Hc) : Wop.symm (Tc.symm c) = Top.symm (Wop.symm c) := rfl

lemma W_S (s : ℤ) (φ : H) : Wop (Sop α s φ) = Sc α s (Wop φ) :=
  lp.ext (funext fun k => lp.ext (funext fun m => by
    show F (emul (s : ℝ) ((s : ℝ) * k * α) (φ k)) m = ex (s * k * α) * F (φ k) (m + -s)
    rw [F_emul, sub_eq_add_neg]))

lemma Wsymm_Sc (s : ℤ) (c : Hc) : Wop.symm (Sc α s c) = Sop α s (Wop.symm c) := by
  conv_lhs => rw [← Wop.apply_symm_apply c]
  rw [← W_S, LinearIsometryEquiv.symm_apply_apply]

lemma Pc_Sc1 (c : Hc) : Pc α (Sc α 1 c) = Tc.symm (Pc α c) :=
  lp.ext (funext fun n => lp.ext (funext fun m => by
    show ex (m * n * α) * (ex (((1 : ℤ) : ℝ) * ((-m : ℤ) : ℝ) * α) * c (-m) (n + -1)) =
      ex (m * ((n - 1 : ℤ) : ℝ) * α) * c (-m) (n - 1)
    rw [← sub_eq_add_neg]
    have e : ex (m * n * α) * ex (((1 : ℤ) : ℝ) * ((-m : ℤ) : ℝ) * α) =
        ex (m * ((n - 1 : ℤ) : ℝ) * α) := by
      rw [← ex_add]; congr 1; push_cast; ring
    linear_combination (c (-m) (n - 1)) * e))

lemma Pc_Scm1 (c : Hc) : Pc α (Sc α (-1) c) = Tc (Pc α c) :=
  lp.ext (funext fun n => lp.ext (funext fun m => by
    show ex (m * n * α) * (ex (((-1 : ℤ) : ℝ) * ((-m : ℤ) : ℝ) * α) * c (-m) (n + -(-1))) =
      ex (m * ((n + 1 : ℤ) : ℝ) * α) * c (-m) (n + 1)
    rw [neg_neg]
    have e : ex (m * n * α) * ex (((-1 : ℤ) : ℝ) * ((-m : ℤ) : ℝ) * α) =
        ex (m * ((n + 1 : ℤ) : ℝ) * α) := by
      rw [← ex_add]; congr 1; push_cast; ring
    linear_combination (c (-m) (n + 1)) * e))

lemma Pc_Tc (c : Hc) : Pc α (Tc c) = Sc α 1 (Pc α c) :=
  lp.ext (funext fun n => lp.ext (funext fun m => by
    show ex (m * n * α) * c (-m + 1) n =
      ex (((1 : ℤ) : ℝ) * n * α) * (ex (((m + -1 : ℤ) : ℝ) * n * α) * c (-(m + -1)) n)
    rw [show -(m + -1) = -m + 1 by ring]
    have e : ex (m * n * α) =
        ex (((1 : ℤ) : ℝ) * n * α) * ex (((m + -1 : ℤ) : ℝ) * n * α) := by
      rw [← ex_add]; congr 1; push_cast; ring
    linear_combination (c (-m + 1) n) * e))

lemma Pc_Tcsymm (c : Hc) : Pc α (Tc.symm c) = Sc α (-1) (Pc α c) :=
  lp.ext (funext fun n => lp.ext (funext fun m => by
    show ex (m * n * α) * c (-m - 1) n =
      ex (((-1 : ℤ) : ℝ) * n * α) * (ex (((m + -(-1) : ℤ) : ℝ) * n * α) * c (-(m + -(-1))) n)
    rw [show -(m + -(-1)) = -m - 1 by ring]
    have e : ex (m * n * α) =
        ex (((-1 : ℤ) : ℝ) * n * α) * ex (((m + -(-1) : ℤ) : ℝ) * n * α) := by
      rw [← ex_add]; congr 1; push_cast; ring
    linear_combination (c (-m - 1) n) * e))

/-! #### The commutation relations `(RS)`, `(RS-1)`, `(RTpm1)` -/

/-- `(RS)`: `R S = T⁻¹ R`. -/
theorem R_S (φ : H) : Rop α (Sop α 1 φ) = Top.symm (Rop α φ) := by
  have h := W_S α 1 φ
  rw [Int.cast_one] at h
  rw [Rop_apply, h, Pc_Sc1, Wsymm_Tcsymm]; rfl

/-- `(RS-1)`: `R S⁻¹ = T R`. -/
theorem R_Sinv (φ : H) : Rop α (Sop α (-1) φ) = Top (Rop α φ) := by
  have h := W_S α (-1) φ
  rw [Int.cast_neg, Int.cast_one] at h
  rw [Rop_apply, h, Pc_Scm1, Wsymm_Tc]; rfl

/-- `(RTpm1)`: `R T = S R`. -/
theorem R_T (φ : H) : Rop α (Top φ) = Sop α 1 (Rop α φ) := by
  have h := Wsymm_Sc α 1 (Pc α (Wop φ))
  rw [Int.cast_one] at h
  rw [Rop_apply, W_T, Pc_Tc, h]; rfl

/-- `(RTpm1)`: `R T⁻¹ = S⁻¹ R`. -/
theorem R_Tinv (φ : H) : Rop α (Top.symm φ) = Sop α (-1) (Rop α φ) := by
  have h := Wsymm_Sc α (-1) (Pc α (Wop φ))
  rw [Int.cast_neg, Int.cast_one] at h
  rw [Rop_apply, W_Tsymm, Pc_Tcsymm, h]; rfl

/-! #### Theorem 3.1 -/

/-- `T² + T⁻² + S + S⁻¹`. -/
def Dfun (φ : H) : H := Top (Top φ) + Top.symm (Top.symm φ) + Sop α 1 φ + Sop α (-1) φ

/-- `M̃_α = e^{iπα}(ST + S⁻¹T⁻¹) + e^{-iπα}(ST⁻¹ + S⁻¹T)`. -/
def Mfun (φ : H) : H :=
  cexp (π * I * α) • (Sop α 1 (Top φ) + Sop α (-1) (Top.symm φ)) +
    cexp (-(π * I * α)) • (Sop α 1 (Top.symm φ) + Sop α (-1) (Top φ))

lemma cexp_pi (t : ℝ) : cexp (π * I * t) = ex (t / 2) := by
  simp only [ex]; congr 1; push_cast; ring

lemma cexp_neg_pi (t : ℝ) : cexp (-(π * I * t)) = ex (-(t / 2)) := by
  simp only [ex]; congr 1; push_cast; ring

lemma sum4 {a b c d a' b' c' d' : L2T} (ha : a = a') (hb : b = b') (hc : c = c')
    (hd : d = d') : a + b + c + d = a' + b' + c' + d' := by subst_vars; rfl

lemma sum4' {a b c d a' b' c' d' : L2T} (ha : a = a') (hb : b = b') (hc : c = c')
    (hd : d = d') : a + b + c + d = a' + b' + (c' + d') := by subst_vars; abel

/-- `U_{1/2}(T² + T⁻² + S + S⁻¹) = (e^{-2πiα}S⁻¹T² + e^{2πiα}T⁻²S + S + S⁻¹)U_{1/2}`. -/
lemma U_D (φ : H) : Uop α (1 / 2) (Dfun α φ) =
    ex (-α) • Sop α (-1) (Top (Top (Uop α (1 / 2) φ))) +
      ex α • Top.symm (Top.symm (Sop α 1 (Uop α (1 / 2) φ))) +
      Sop α 1 (Uop α (1 / 2) φ) + Sop α (-1) (Uop α (1 / 2) φ) := by
  refine lp.ext (funext fun n => ?_)
  simp only [Dfun, map_add, lp.coeFn_add, Pi.add_apply, lp.coeFn_smul, Pi.smul_apply,
    Top_apply, Top_symm_apply, Sop_apply, Uop_apply, emul_emul, smul_emul]
  refine sum4 (emul_congr ?_ ?_ _) (emul_congr ?_ ?_ _) (emul_congr ?_ ?_ _)
    (emul_congr ?_ ?_ _) <;> push_cast <;> ring

/-- `U_1(e^{-2πiα}TS² + e^{2πiα}S⁻²T⁻¹ + T⁻¹ + T) = M̃_α U_1`. -/
lemma U_M (χ : H) : Uop α 1 (ex (-α) • Top (Sop α 1 (Sop α 1 χ)) +
    ex α • Sop α (-1) (Sop α (-1) (Top.symm χ)) + Top.symm χ + Top χ) =
    Mfun α (Uop α 1 χ) := by
  refine lp.ext (funext fun n => ?_)
  simp only [Mfun, cexp_pi, cexp_neg_pi, map_add, map_smul, smul_add, lp.coeFn_add,
    Pi.add_apply, lp.coeFn_smul, Pi.smul_apply, Top_apply, Top_symm_apply, Sop_apply, Uop_apply,
    emul_emul, smul_emul]
  refine sum4' (emul_congr ?_ ?_ _) (emul_congr ?_ ?_ _) (emul_congr ?_ ?_ _)
    (emul_congr ?_ ?_ _) <;> push_cast <;> ring

/-- `R(e^{-2πiα}S⁻¹T² + e^{2πiα}T⁻²S + S + S⁻¹) = (e^{-2πiα}TS² + e^{2πiα}S⁻²T⁻¹ + T⁻¹ + T)R`. -/
lemma R_D' (ψ : H) : Rop α (ex (-α) • Sop α (-1) (Top (Top ψ)) +
      ex α • Top.symm (Top.symm (Sop α 1 ψ)) + Sop α 1 ψ + Sop α (-1) ψ) =
    ex (-α) • Top (Sop α 1 (Sop α 1 (Rop α ψ))) +
      ex α • Sop α (-1) (Sop α (-1) (Top.symm (Rop α ψ))) + Top.symm (Rop α ψ) +
      Top (Rop α ψ) := by
  simp only [map_add, map_smul]
  rw [R_Sinv, R_T, R_T, R_Tinv, R_Tinv, R_S, R_Sinv]

/-- **Theorem 3.1 (`chiralrepresentthm`), applied form:** `Q(T² + T⁻² + S + S⁻¹) = M̃_α Q`
on all of `L²(𝕋; ℓ²(ℤ))`. -/
theorem Q_D (φ : H) : Qop α (Dfun α φ) = Mfun α (Qop α φ) := by
  rw [Qop_apply, U_D, R_D', U_M, Qop_apply]

/-- A unitary of `L²(𝕋; ℓ²(ℤ))` as a bounded operator. -/
def toCLM (e : H ≃ₗᵢ[ℂ] H) : H →L[ℂ] H := e.toLinearIsometry.toContinuousLinearMap

@[simp] lemma toCLM_apply (e : H ≃ₗᵢ[ℂ] H) (φ : H) : toCLM e φ = e φ := rfl

/-- `T² + T⁻² + S + S⁻¹` as a bounded operator on `L²(𝕋; ℓ²(ℤ))`. -/
def Dop : H →L[ℂ] H :=
  toCLM Top ∘L toCLM Top + toCLM Top.symm ∘L toCLM Top.symm + toCLM (Sop α 1) +
    toCLM (Sop α (-1))

/-- `M̃_α = e^{iπα}(ST + S⁻¹T⁻¹) + e^{-iπα}(ST⁻¹ + S⁻¹T)` as a bounded operator
(the decomposable operator with fibres `H̃_{α,θ}`, see `Mfun_ae`). -/
def Mop : H →L[ℂ] H :=
  cexp (π * I * α) • (toCLM (Sop α 1) ∘L toCLM Top + toCLM (Sop α (-1)) ∘L toCLM Top.symm) +
    cexp (-(π * I * α)) • (toCLM (Sop α 1) ∘L toCLM Top.symm + toCLM (Sop α (-1)) ∘L toCLM Top)

lemma Dop_apply (φ : H) : Dop α φ = Dfun α φ := rfl

lemma Mop_apply (φ : H) : Mop α φ = Mfun α φ := rfl

/-- **Theorem 3.1 (`chiralrepresentthm`).**  `Q = U_1 R U_{1/2}` is a unitary operator on
`L²(𝕋; ℓ²(ℤ))` and `Q (T² + T⁻² + S + S⁻¹) Q⁻¹ = M̃_α` as bounded operators. -/
theorem chiralrepresentthm :
    toCLM (Qop α) ∘L Dop α ∘L toCLM (Qop α).symm = Mop α := by
  refine ContinuousLinearMap.ext fun φ => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, toCLM_apply, toCLM_apply,
    Dop_apply, Q_D, LinearIsometryEquiv.apply_symm_apply, Mop_apply]

/-- **Theorem 3.1, existential form:** the operators `T² + T⁻² + S + S⁻¹` and `M̃_α` are
unitarily equivalent, via the unitary `Q = U_1 R U_{1/2}`. -/
theorem chiralrepresentthm' : ∃ Q : H ≃ₗᵢ[ℂ] H,
    (∀ φ, Q φ = Uop α 1 (Rop α (Uop α (1 / 2) φ))) ∧
      toCLM Q ∘L Dop α ∘L toCLM Q.symm = Mop α :=
  ⟨Qop α, fun _ => rfl, chiralrepresentthm α⟩

/-! #### The literal formula (3.4) for `R` and the fibres of `M̃_α` -/

lemma F_symm_hasSum (d : L2Z ℂ) : HasSum (fun m => d m • eL m) (F.symm d) := by
  have h := J.toLinearIsometry.toContinuousLinearMap.hasSum (fourierBasis.hasSum_repr_symm d)
  simp only [map_smul] at h
  convert h using 1
  · funext m
    simp only [eL, coe_fourierBasis]
    rfl
  · rfl

/-- **The formula (3.4) for `R`:** for every `φ ∈ L²(𝕋; ℓ²(ℤ))` and `n`,
`(Rφ)(n, ·) = ∑_k e^{-2πiknα} (∫_0^1 e^{-2πinβ} φ(k,β) dβ) e^{-2πikθ}` in `L²(𝕋)`
(`eL (-k)` is the function `θ ↦ e^{-2πikθ}`, see `eL_ae`). -/
theorem Rop_hasSum (φ : H) (n : ℤ) :
    HasSum (fun k : ℤ => (ex (-(k * n * α)) *
      ∫ β in Ioc (0 : ℝ) 1, ex (-(n * β)) * φ k β) • eL (-k)) (Rop α φ n) := by
  have h := F_symm_hasSum (Pc α (Wop φ) n)
  rw [← (Equiv.neg ℤ).hasSum_iff] at h
  rw [show Rop α φ n = F.symm (Pc α (Wop φ) n) from rfl]
  convert h using 1
  funext k
  simp only [Function.comp, Equiv.neg_apply, Pc_apply, Wop_apply, F_apply_integral, neg_neg]
  congr 2
  push_cast; ring_nf

lemma two_sin_chiral (θ t : ℝ) :
    ((2 * Real.sin (2 * π * (1 / 4 + α / 2 + θ + t)) : ℝ) : ℂ) =
      cexp (π * I * α) * ex (θ + t) + cexp (-(π * I * α)) * ex (-(θ + t)) := by
  rw [show 2 * π * (1 / 4 + α / 2 + θ + t) = (2 * π * (θ + t) + π * α) + π / 2 by ring,
    Real.sin_add_pi_div_two]
  push_cast
  rw [Complex.two_cos]
  simp only [ex, ← Complex.exp_add]
  push_cast
  ring_nf

/-- **Fibres of `M̃_α`:** `(M̃_α φ)(n,θ) = (Ĥ_{α,1/4+α/2+θ} φ(·,θ))(n)`, i.e.
`M̃_α = ∫^⊕ H̃_{α,θ} dθ` with `H̃_{α,θ} = Ĥ_{α,1/4+α/2+θ}` (tex l. ~551, (3.13)). -/
theorem Mfun_ae (φ : H) (n : ℤ) : Mfun α φ n =ᵐ[μT] fun θ =>
    ((2 * Real.sin (2 * π * (1 / 4 + α / 2 + θ + (n - 1) * α)) : ℝ) : ℂ) * φ (n - 1) θ +
      ((2 * Real.sin (2 * π * (1 / 4 + α / 2 + θ + n * α)) : ℝ) : ℂ) * φ (n + 1) θ := by
  have hM : Mfun α φ n = cexp (π * I * α) • (emul 1 (1 * n * α) (φ (n + 1)) +
      emul (-1) (-1 * n * α) (φ (n - 1))) + cexp (-(π * I * α)) •
      (emul 1 (1 * n * α) (φ (n - 1)) + emul (-1) (-1 * n * α) (φ (n + 1))) := by
    simp only [Mfun, lp.coeFn_add, Pi.add_apply, lp.coeFn_smul, Pi.smul_apply, Sop_apply,
      Top_apply, Top_symm_apply]
  rw [hM]
  filter_upwards [Lp.coeFn_add (cexp (π * I * α) • (emul 1 (1 * n * α) (φ (n + 1)) +
      emul (-1) (-1 * n * α) (φ (n - 1)))) (cexp (-(π * I * α)) •
      (emul 1 (1 * n * α) (φ (n - 1)) + emul (-1) (-1 * n * α) (φ (n + 1)))),
    Lp.coeFn_smul (cexp (π * I * α)) (emul 1 (1 * n * α) (φ (n + 1)) +
      emul (-1) (-1 * n * α) (φ (n - 1))),
    Lp.coeFn_smul (cexp (-(π * I * α))) (emul 1 (1 * n * α) (φ (n - 1)) +
      emul (-1) (-1 * n * α) (φ (n + 1))),
    Lp.coeFn_add (emul 1 (1 * n * α) (φ (n + 1))) (emul (-1) (-1 * n * α) (φ (n - 1))),
    Lp.coeFn_add (emul 1 (1 * n * α) (φ (n - 1))) (emul (-1) (-1 * n * α) (φ (n + 1))),
    emul_ae 1 (1 * n * α) (φ (n + 1)), emul_ae (-1) (-1 * n * α) (φ (n - 1)),
    emul_ae 1 (1 * n * α) (φ (n - 1)), emul_ae (-1) (-1 * n * α) (φ (n + 1))]
    with θ h1 h2 h3 h4 h5 h6 h7 h8 h9
  rw [h1, Pi.add_apply, h2, h3, Pi.smul_apply, Pi.smul_apply, h4, h5, Pi.add_apply,
    Pi.add_apply, h6, h7, h8, h9, two_sin_chiral, two_sin_chiral]
  have e1 : ex (1 * θ + 1 * n * α) = ex (θ + n * α) := by congr 1; ring
  have e2 : ex (-1 * θ + -1 * n * α) = ex (-(θ + n * α)) := by congr 1; ring
  have e3 : ex (θ + (n - 1) * α) = ex (θ + n * α) * ex (-α) := by rw [← ex_add]; congr 1; ring
  have e4 : ex (-(θ + (n - 1) * α)) = ex (-(θ + n * α)) * ex α := by
    rw [← ex_add]; congr 1; ring
  have e5 : cexp (π * I * α) = ex (α / 2) := cexp_pi α
  have e6 : cexp (-(π * I * α)) = ex (-(α / 2)) := cexp_neg_pi α
  have e7 : ex (α / 2) * ex (-α) = ex (-(α / 2)) := by rw [← ex_add]; congr 1; ring
  have e8 : ex (-(α / 2)) * ex α = ex (α / 2) := by rw [← ex_add]; congr 1; ring
  rw [e1, e2, e3, e4, e5, e6]
  simp only [smul_eq_mul]
  linear_combination (-(ex (θ + n * α) * φ (n - 1) θ)) * e7 +
    (-(ex (-(θ + n * α)) * φ (n - 1) θ)) * e8

/-- **Fibres of `T² + T⁻² + S + S⁻¹`:**
`((T²+T⁻²+S+S⁻¹)φ)(n,θ) = φ(n+2,θ) + φ(n-2,θ) + 2cos 2π(θ+nα) φ(n,θ)`; on even (odd) sites this
is `H_{2α,θ}` (`H_{2α,θ+α}`), cf. `ChiralGauge.doubled_even/odd`. -/
theorem Dfun_ae (φ : H) (n : ℤ) : Dfun α φ n =ᵐ[μT] fun θ =>
    φ (n + 1 + 1) θ + φ (n - 1 - 1) θ +
      ((2 * Real.cos (2 * π * (θ + n * α)) : ℝ) : ℂ) * φ n θ := by
  have hD : Dfun α φ n = φ (n + 1 + 1) + φ (n - 1 - 1) + emul 1 (1 * n * α) (φ n) +
      emul (-1) (-1 * n * α) (φ n) := by
    simp only [Dfun, lp.coeFn_add, Pi.add_apply, Sop_apply, Top_apply, Top_symm_apply]
  rw [hD]
  filter_upwards [Lp.coeFn_add (φ (n + 1 + 1) + φ (n - 1 - 1) + emul 1 (1 * n * α) (φ n))
      (emul (-1) (-1 * n * α) (φ n)),
    Lp.coeFn_add (φ (n + 1 + 1) + φ (n - 1 - 1)) (emul 1 (1 * n * α) (φ n)),
    Lp.coeFn_add (φ (n + 1 + 1)) (φ (n - 1 - 1)),
    emul_ae 1 (1 * n * α) (φ n), emul_ae (-1) (-1 * n * α) (φ n)] with θ h1 h2 h3 h4 h5
  rw [h1, Pi.add_apply, h2, Pi.add_apply, h3, Pi.add_apply, h4, h5]
  have c : ((2 * Real.cos (2 * π * (θ + n * α)) : ℝ) : ℂ) =
      ex (1 * θ + 1 * n * α) + ex (-1 * θ + -1 * n * α) := by
    rw [two_cos_ex]; congr 1 <;> congr 1 <;> ring
  rw [c]; ring

end ChiralL2

end CAH
