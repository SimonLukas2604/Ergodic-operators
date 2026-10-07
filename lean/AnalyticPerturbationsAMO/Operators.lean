/-
Copyright (c) 2026. Formalization of
  S. Becker, "Analytic perturbations of the almost Mathieu operator:
  Dry Ten Martini and spectral transitions".

# Weighted shifts on `ℓ²(ι)`

The magnetic generators `U`, `V_x`, `W_{r,q}` of the paper, and their two-dimensional
analogues, are all *weighted shifts*: operators of the form
`(T u)(i) = c i * u (σ i)` for a bounded weight `c : ι → ℂ` and a bijection `σ : ι ≃ ι`.
This file constructs these operators on `ℓ²(ι)` and proves their basic algebra:
composition, scalar multiplication, operator norm bound, and adjoint.
-/
import Mathlib

noncomputable section

open scoped ENNReal ComplexConjugate InnerProductSpace

/-- The Hilbert space `ℓ²(ι)` of square-summable complex sequences. -/
abbrev L2 (ι : Type*) := lp (fun _ : ι => ℂ) 2

namespace L2

variable {ι : Type*}

lemma memℓp_two_iff (f : ι → ℂ) : Memℓp f 2 ↔ Summable fun i => ‖f i‖ ^ 2 := by
  rw [memℓp_gen_iff (by norm_num)]
  simp

lemma norm_sq_eq_tsum (u : L2 ι) : ‖u‖ ^ 2 = ∑' i, ‖u i‖ ^ 2 := by
  have := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) u
  simpa [Real.rpow_two] using this

lemma summable_norm_sq (u : L2 ι) : Summable fun i => ‖u i‖ ^ 2 :=
  (memℓp_two_iff _).1 (lp.memℓp u)

/-- The underlying function of a weighted shift. -/
def wsFun (c : ι → ℂ) (σ : ι ≃ ι) (u : ι → ℂ) : ι → ℂ := fun i => c i * u (σ i)

lemma summable_wsFun {c : ι → ℂ} {M : ℝ} (hc : ∀ i, ‖c i‖ ≤ M) (σ : ι ≃ ι) (u : L2 ι) :
    Summable fun i => ‖wsFun c σ u i‖ ^ 2 := by
  have h2 : Summable fun i => ‖u (σ i)‖ ^ 2 :=
    (σ.summable_iff (f := fun i => ‖u i‖ ^ 2)).2 (summable_norm_sq u)
  refine (h2.mul_left (M ^ 2)).of_nonneg_of_le (fun _ => by positivity) (fun i => ?_)
  simp only [wsFun, norm_mul, mul_pow]
  gcongr
  exact hc i

lemma norm_wsFun_sq_le {c : ι → ℂ} {M : ℝ} (hc : ∀ i, ‖c i‖ ≤ M) (σ : ι ≃ ι) (u : L2 ι) :
    ∑' i, ‖wsFun c σ u i‖ ^ 2 ≤ M ^ 2 * ‖u‖ ^ 2 := by
  have h2 : Summable fun i => ‖u (σ i)‖ ^ 2 :=
    (σ.summable_iff (f := fun i => ‖u i‖ ^ 2)).2 (summable_norm_sq u)
  rw [norm_sq_eq_tsum, ← σ.tsum_eq (fun i => ‖u i‖ ^ 2), ← tsum_mul_left]
  refine (summable_wsFun hc σ u).tsum_le_tsum (fun i => ?_) (h2.mul_left _)
  simp only [wsFun, norm_mul, mul_pow]
  gcongr
  exact hc i

/-- The weighted shift as a linear map, for a bounded weight. -/
def wsLinear (c : ι → ℂ) {M : ℝ} (hc : ∀ i, ‖c i‖ ≤ M) (σ : ι ≃ ι) :
    L2 ι →ₗ[ℂ] L2 ι where
  toFun u := ⟨wsFun c σ u, (memℓp_two_iff _).2 (summable_wsFun hc σ u)⟩
  map_add' u v := by
    ext i
    simp only [wsFun, lp.coeFn_add, Pi.add_apply, mul_add]
  map_smul' a u := by
    ext i
    simp [wsFun]
    ring

/-- The weighted shift `(T u)(i) = c i * u (σ i)` on `ℓ²(ι)`.  It is defined to be `0`
when the weight is unbounded (a case that never occurs below). -/
def weightedShift (c : ι → ℂ) (σ : ι ≃ ι) : L2 ι →L[ℂ] L2 ι :=
  open Classical in
  if h : ∃ M, ∀ i, ‖c i‖ ≤ M then
    (wsLinear c (M := max h.choose 0)
        (fun i => (h.choose_spec i).trans (le_max_left _ _)) σ).mkContinuous
      (max h.choose 0) (fun u => by
        have hM0 : 0 ≤ max h.choose 0 := le_max_right _ _
        have key := norm_wsFun_sq_le
          (fun i => (h.choose_spec i).trans (le_max_left _ _)) σ u (M := max h.choose 0)
        have hsq : ‖(wsLinear c (M := max h.choose 0)
            (fun i => (h.choose_spec i).trans (le_max_left _ _)) σ) u‖ ^ 2
              ≤ (max h.choose 0 * ‖u‖) ^ 2 := by
          rw [norm_sq_eq_tsum, mul_pow]
          exact key
        exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq)
  else 0

variable {c c' : ι → ℂ} {σ σ' : ι ≃ ι}

/-- A weight is bounded. -/
def Bdd (c : ι → ℂ) : Prop := ∃ M, ∀ i, ‖c i‖ ≤ M

@[simp]
lemma weightedShift_apply (hc : Bdd c) (u : L2 ι) (i : ι) :
    weightedShift c σ u i = c i * u (σ i) := by
  unfold weightedShift
  split_ifs with h
  · rfl
  · exact absurd hc h

lemma norm_weightedShift_le {M : ℝ} (hM : 0 ≤ M) (hc : ∀ i, ‖c i‖ ≤ M) :
    ‖weightedShift c σ‖ ≤ M := by
  refine ContinuousLinearMap.opNorm_le_bound _ hM (fun u => ?_)
  have key := norm_wsFun_sq_le hc σ u
  have hsq : ‖weightedShift c σ u‖ ^ 2 ≤ (M * ‖u‖) ^ 2 := by
    rw [norm_sq_eq_tsum, mul_pow]
    convert key using 3 with i
    rw [weightedShift_apply ⟨M, hc⟩]
    rfl
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq

lemma weightedShift_congr (h1 : ∀ i, c i = c' i) (h2 : ∀ i, σ i = σ' i) :
    weightedShift c σ = weightedShift c' σ' := by
  have hc : c = c' := funext h1
  have hσ : σ = σ' := Equiv.ext h2
  subst hc hσ
  rfl

lemma Bdd.mul (hc : Bdd c) (hc' : Bdd c') : Bdd (fun i => c i * c' i) := by
  obtain ⟨M, hM⟩ := hc
  obtain ⟨M', hM'⟩ := hc'
  refine ⟨max M 0 * max M' 0, fun i => ?_⟩
  rw [norm_mul]
  exact mul_le_mul ((hM i).trans (le_max_left _ _)) ((hM' i).trans (le_max_left _ _))
    (norm_nonneg _) (le_max_right _ _)

lemma Bdd.comp (hc : Bdd c) (σ : ι ≃ ι) : Bdd (fun i => c (σ i)) := by
  obtain ⟨M, hM⟩ := hc
  exact ⟨M, fun i => hM _⟩

lemma Bdd.const_mul (a : ℂ) (hc : Bdd c) : Bdd (fun i => a * c i) :=
  Bdd.mul ⟨‖a‖, fun _ => le_rfl⟩ hc

lemma Bdd.conj (hc : Bdd c) : Bdd (fun i => conj (c i)) := by
  obtain ⟨M, hM⟩ := hc
  exact ⟨M, fun i => by simpa using hM i⟩

lemma bdd_of_norm_eq_one (hc : ∀ i, ‖c i‖ = 1) : Bdd c := ⟨1, fun i => (hc i).le⟩

/-- Composition of weighted shifts. -/
lemma weightedShift_comp (hc : Bdd c) (hc' : Bdd c') :
    weightedShift c σ ∘L weightedShift c' σ' =
      weightedShift (fun i => c i * c' (σ i)) (σ.trans σ') := by
  ext u i
  rw [ContinuousLinearMap.comp_apply, weightedShift_apply hc,
    weightedShift_apply hc', weightedShift_apply (hc.mul (hc'.comp σ))]
  simp [mul_assoc]

lemma smul_weightedShift (a : ℂ) (hc : Bdd c) :
    a • weightedShift c σ = weightedShift (fun i => a * c i) σ := by
  ext u i
  rw [smul_apply, lp.coeFn_smul, Pi.smul_apply,
    weightedShift_apply hc, weightedShift_apply (hc.const_mul a), smul_eq_mul, mul_assoc]

lemma weightedShift_one_refl : weightedShift (fun _ : ι => (1 : ℂ)) (Equiv.refl ι) = 1 := by
  ext u i
  rw [weightedShift_apply ⟨1, fun _ => by simp⟩]
  simp

/-- The adjoint of a weighted shift is again a weighted shift. -/
lemma adjoint_weightedShift (hc : Bdd c) :
    ContinuousLinearMap.adjoint (weightedShift c σ) =
      weightedShift (fun j => conj (c (σ.symm j))) σ.symm := by
  have hc' : Bdd (fun j => conj (c (σ.symm j))) := (hc.comp σ.symm).conj
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro u v
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  rw [← σ.tsum_eq (fun j => ⟪(weightedShift (fun j => conj (c (σ.symm j))) σ.symm u) j, v j⟫_ℂ)]
  congr 1
  funext i
  rw [weightedShift_apply hc', weightedShift_apply hc]
  simp only [Equiv.symm_apply_apply, RCLike.inner_apply, map_mul, RingHomCompTriple.comp_apply,
    RingHom.id_apply]
  ring

lemma star_weightedShift (hc : Bdd c) :
    star (weightedShift c σ) = weightedShift (fun j => conj (c (σ.symm j))) σ.symm :=
  adjoint_weightedShift hc

end L2
