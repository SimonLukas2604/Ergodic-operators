/-
# Proposition 2.4 (`ext-prop:sharp-width-preparation`): widths and growth

The proof of the sharp-width preparation has a quantitative skeleton that does not depend on
anything outside this project once the AMO Lyapunov profiles are granted:

* **Width bookkeeping** (`Widths`): with `c = log(1/η)` and `ν = min(s, ℓ - c)`, the paper's
  `ℓ₀ = c + ν/4`, `ℓ₁ = c + ν/2`, `r₀ = ν/16`, `r₁ = ν/8`, `γ₁ = 3s/4`, `γ₂ = c + 3ν/16` satisfy
  `ext-eq:nested-widths`, `ℓ₁ - c ≤ s/2 < γ₁ < s`, `c + r₁ < γ₂ < ℓ₀`, and the two inverse
  denominators are `1 - e^{-s/4}` and `1 - e^{-ν/16}`.
* **Finite-block growth near a compact set** (`uniform_growth_near`): a strengthening of
  Lemma 2.5 where the Lyapunov bound is only assumed on a compact subset `S` of the parameter
  space, and the uniform growth bound holds on an open neighbourhood of `S` and for nearby
  frequencies.
* **Strip growth from the AMO profiles** (`amo_strip_growth`): assuming the profiles
  `ext-eq:AMO-profiles` on a compact set `K` of energies (e.g. the AMO spectrum), the direct AMO
  cocycle on the strip `|Im x| ≤ ℓ₁/(2π)` grows at most like `C₁ e^{γ₁ m}` and the dual one on
  `|Im x| ≤ r₁/(2π)` like `C₂ e^{γ₂ m}`, uniformly for energies within `δ` of `K`.

The profiles themselves come from Avila's global theory and enter as the hypothesis
`AMOProfiles`.  Everything here is proved.
-/
import AnalyticPerturbationsAMO.UniformGrowth

noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Metric Set

namespace AMO

/-! ### Finite-block growth near a compact set -/

section Near

variable {P : Type*} [TopologicalSpace P] [CompactSpace P] (A : P → ℝ → M2)

/-- **Lemma 2.5, local form.**  If `L(α, A_p) < γ` for `p` in a compact set `S`, the bound
`‖A_{p,n}(x)‖ ≤ C e^{γ n}` holds for all `p` in an open neighbourhood of `S` and all frequencies
near `α`. -/
theorem uniform_growth_near {α γ : ℝ} (hα : Irrational α)
    (hcont : Continuous fun z : P × ℝ => A z.1 z.2) (hcoc : ∀ p, IsSLCocycle (A p))
    (hγ : 0 ≤ γ) {S : Set P} (hS : IsCompact S) (hL : ∀ p ∈ S, lyapunov α (A p) < γ) :
    ∃ C : ℝ, 0 < C ∧ ∃ V : Set P, IsOpen V ∧ S ⊆ V ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ α' : ℝ,
      |α' - α| < δ → ∀ p ∈ V, ∀ (n : ℕ) (x : ℝ), ‖iter α' (A p) n x‖ ≤ C * Real.exp (γ * n) := by
  obtain ⟨M, hM1, hM⟩ := exists_norm_bound_family A hcont (fun p => (hcoc p).periodic)
  have hloc : ∀ p : S, ∃ m : ℕ, 1 ≤ m ∧ ∃ U : Set (ℝ × P), IsOpen U ∧ (α, (p : P)) ∈ U ∧
      ∀ z ∈ U, ∀ x, ‖iter z.1 (A z.2) m x‖ ≤ Real.exp (γ * m) := by
    rintro ⟨p, hp⟩
    have hLp := hL p hp
    set γ' := (lyapunov α (A p) + γ) / 2 with hγ'
    have hgap : 0 < γ - γ' := by rw [hγ']; linarith
    obtain ⟨Cp, hCp, hgrowth⟩ := (hcoc p).uniform_growth hα (show lyapunov α (A p) < γ' by
      rw [hγ']; linarith)
    obtain ⟨m₀, hm₀⟩ := exists_nat_gt (Real.log Cp / (γ - γ'))
    set m := m₀ + 1
    have hm1 : 1 ≤ m := by omega
    have hstrict : ∀ x, ‖iter α (A p) m x‖ < Real.exp (γ * m) := by
      intro x
      refine (hgrowth m x).trans_lt ?_
      rw [← Real.exp_log hCp, ← Real.exp_add]
      apply Real.exp_lt_exp.2
      have : Real.log Cp < (γ - γ') * m := by
        rw [div_lt_iff₀ hgap] at hm₀
        have : (m₀ : ℝ) < m := by simp only [m]; push_cast; linarith
        nlinarith
      linarith
    set W : Set ((ℝ × P) × ℝ) := {z | ‖iter z.1.1 (A z.1.2) m z.2‖ < Real.exp (γ * m)}
    have hW : IsOpen W := by
      have hc := (continuous_iter_family A hcont m).comp
        (Continuous.prodMk (continuous_fst.comp continuous_fst)
          (Continuous.prodMk (continuous_snd.comp continuous_fst) continuous_snd))
      exact isOpen_lt (continuous_norm.comp hc) continuous_const
    have hsub : ({(α, p)} : Set (ℝ × P)) ×ˢ Set.Icc (0 : ℝ) 1 ⊆ W := by
      rintro ⟨z, x⟩ ⟨hz, -⟩
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact hstrict x
    obtain ⟨u, v, hu, -, hαu, hv, huv⟩ :=
      generalized_tube_lemma isCompact_singleton isCompact_Icc hW hsub
    refine ⟨m, hm1, u, hu, hαu rfl, fun z hz x => ?_⟩
    have hper : Function.Periodic (iter z.1 (A z.2) m) 1 := iter_periodic (hcoc z.2).periodic m
    obtain ⟨y, hy, hxy⟩ := hper.exists_mem_Ico₀ one_pos x
    rw [hxy]
    exact (huv ⟨hz, hv ⟨hy.1, hy.2.le⟩⟩ : (z, y) ∈ W).le
  choose m hm1 U hUo hαU hU using hloc
  have hcover : ({α} : Set ℝ) ×ˢ S ⊆ ⋃ p : S, U p := by
    rintro ⟨a, p⟩ ⟨ha, hp⟩
    rw [Set.mem_singleton_iff] at ha
    subst ha
    exact Set.mem_iUnion.2 ⟨⟨p, hp⟩, hαU ⟨p, hp⟩⟩
  obtain ⟨t, ht⟩ := (isCompact_singleton.prod hS).elim_finite_subcover U hUo hcover
  have hO : IsOpen (⋃ p ∈ t, U p) := isOpen_biUnion fun p _ => hUo p
  obtain ⟨u, v, hu, hv, hαu, hSv, huv⟩ :=
    generalized_tube_lemma isCompact_singleton hS hO ht
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hu α (hαu rfl)
  set C := 1 + ∑ p ∈ t, M ^ m p
  have hC : 0 < C := by positivity
  refine ⟨C, hC, v, hv, hSv, δ, hδ, fun α' hα' p hp n x => ?_⟩
  have hmem : (α', p) ∈ ⋃ q ∈ t, U q :=
    huv ⟨hball (by rw [Metric.mem_ball, Real.dist_eq]; exact hα'), hp⟩
  obtain ⟨q, hqt, hq⟩ := Set.mem_iUnion₂.1 hmem
  have hb := norm_iter_block_bound hM1 (hM p) hγ (hm1 q) (β := α')
    (fun y => hU q (α', p) hq y) n x
  have hle : M ^ m q ≤ C := by
    have := Finset.single_le_sum (f := fun p => M ^ m p) (fun p _ => by positivity) hqt
    linarith
  exact hb.trans (mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le)

end Near

/-! ### Strip growth for families of complexified cocycles -/

/-- **Uniform growth on a strip near a compact set of energies.**  For a jointly continuous
family `F(E, y)` of `SL(2, ℂ)` cocycles with `L(α, F(E, y)) < γ` for `E ∈ K` and `|y| ≤ Y`,
the bound `‖F(E, y)_n(x)‖ ≤ C e^{γ n}` holds for all `E` within `δ` of `K` (with `‖E‖ ≤ R`),
all `|y| ≤ Y` and all frequencies near `α`. -/
theorem strip_growth (F : ℂ × ℝ → ℝ → M2)
    (hF : Continuous fun z : (ℂ × ℝ) × ℝ => F z.1 z.2) (hcoc : ∀ q, IsSLCocycle (F q))
    {α γ Y R : ℝ} (hα : Irrational α) (hγ : 0 ≤ γ) {K : Set ℂ} (hK : IsCompact K)
    (hKR : K ⊆ closedBall 0 R)
    (hL : ∀ E ∈ K, ∀ y ∈ Icc (-Y) Y, lyapunov α (F (E, y)) < γ) :
    ∃ C : ℝ, 0 < C ∧ ∃ δ : ℝ, 0 < δ ∧ ∃ δα : ℝ, 0 < δα ∧ ∀ α' : ℝ, |α' - α| < δα →
      ∀ E : ℂ, ‖E‖ ≤ R → (∃ k ∈ K, dist E k < δ) → ∀ y ∈ Icc (-Y) Y, ∀ (n : ℕ) (x : ℝ),
        ‖iter α' (F (E, y)) n x‖ ≤ C * Real.exp (γ * n) := by
  haveI : CompactSpace (closedBall (0 : ℂ) R) := isCompact_iff_compactSpace.1 (isCompact_closedBall _ _)
  haveI : CompactSpace (Icc (-Y) Y) := isCompact_iff_compactSpace.1 isCompact_Icc
  set A : closedBall (0 : ℂ) R × Icc (-Y) Y → ℝ → M2 := fun p => F ((p.1 : ℂ), (p.2 : ℝ))
  have hcontA : Continuous fun z : (closedBall (0 : ℂ) R × Icc (-Y) Y) × ℝ => A z.1 z.2 :=
    hF.comp (Continuous.prodMk (Continuous.prodMk
      (continuous_subtype_val.comp (continuous_fst.comp continuous_fst))
      (continuous_subtype_val.comp (continuous_snd.comp continuous_fst))) continuous_snd)
  set K1 : Set (closedBall (0 : ℂ) R) := {E | (E : ℂ) ∈ K}
  have hK1 : IsCompact K1 :=
    (hK.isClosed.preimage continuous_subtype_val).isCompact
  have hS : IsCompact (K1 ×ˢ (univ : Set (Icc (-Y) Y))) := hK1.prod isCompact_univ
  obtain ⟨C, hC, V, hV, hSV, δα, hδα, hgrow⟩ := uniform_growth_near A hα hcontA
    (fun p => hcoc _) hγ hS (fun p hp => hL _ hp.1 _ p.2.2)
  obtain ⟨u, v, hu, -, hK1u, hv, huv⟩ := generalized_tube_lemma hK1 isCompact_univ hV hSV
  obtain ⟨δ, hδ, hthick⟩ := hK1.exists_thickening_subset_open hu hK1u
  refine ⟨C, hC, δ, hδ, δα, hδα, fun α' hα' E hE ⟨k, hk, hEk⟩ y hy n x => ?_⟩
  have hEu : (⟨E, mem_closedBall_zero_iff.2 hE⟩ : closedBall (0 : ℂ) R) ∈ u := by
    refine hthick (mem_thickening_iff.2 ⟨⟨k, hKR hk⟩, hk, ?_⟩)
    exact hEk
  exact hgrow α' hα' (⟨E, mem_closedBall_zero_iff.2 hE⟩, ⟨y, hy⟩)
    (huv ⟨hEu, hv (mem_univ _)⟩) n x

/-! ### The AMO cocycles and their profiles -/

/-- The complexified AMO transfer cocycle of `U + U^{-1} + η(V + V^{-1}) - E` at `Im x = y`. -/
def amoCoc (η : ℝ) (q : ℂ × ℝ) : ℝ → M2 := fun x =>
  transferMatrix (2 * η * Complex.cos (2 * Real.pi * ((x : ℂ) + q.2 * Complex.I)) - q.1) 1

/-- The complexified transfer cocycle of the dual `η(U + U^{-1}) + V + V^{-1} - E`. -/
def dualCoc (η : ℝ) (q : ℂ × ℝ) : ℝ → M2 := fun x =>
  transferMatrix (2 * Complex.cos (2 * Real.pi * ((x : ℂ) + q.2 * Complex.I)) - q.1) η

lemma continuous_transferFamily (c : ℂ) (hc : c ≠ 0) (k : ℂ) :
    Continuous fun z : (ℂ × ℝ) × ℝ =>
      transferMatrix (k * Complex.cos (2 * Real.pi * ((z.2 : ℂ) + z.1.2 * Complex.I)) - z.1.1) c := by
  have hb : Continuous fun z : (ℂ × ℝ) × ℝ =>
      k * Complex.cos (2 * Real.pi * ((z.2 : ℂ) + z.1.2 * Complex.I)) - z.1.1 := by fun_prop
  unfold transferMatrix
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j <;> simp
  all_goals fun_prop

lemma isSLCocycle_transferFamily (c : ℂ) (hc : c ≠ 0) (k : ℂ) (q : ℂ × ℝ) :
    IsSLCocycle fun x : ℝ =>
      transferMatrix (k * Complex.cos (2 * Real.pi * ((x : ℂ) + q.2 * Complex.I)) - q.1) c := by
  refine ⟨?_, ?_, ?_⟩
  · have := (continuous_transferFamily c hc k).comp
      (Continuous.prodMk (continuous_const (y := q)) continuous_id)
    exact this
  · intro x
    simp only
    congr 2
    push_cast
    rw [show 2 * (Real.pi : ℂ) * ((x : ℂ) + 1 + q.2 * Complex.I) =
      2 * Real.pi * ((x : ℂ) + q.2 * Complex.I) + 2 * Real.pi by ring, Complex.cos_add_two_pi]
  · intro x
    exact det_transferMatrix _ hc

lemma isSLCocycle_amoCoc (η : ℝ) (q : ℂ × ℝ) : IsSLCocycle (amoCoc η q) := by
  exact isSLCocycle_transferFamily 1 one_ne_zero (2 * η) q

lemma isSLCocycle_dualCoc {η : ℝ} (hη : η ≠ 0) (q : ℂ × ℝ) : IsSLCocycle (dualCoc η q) := by
  exact isSLCocycle_transferFamily (η : ℂ) (by exact_mod_cast hη) 2 q

lemma continuous_amoCoc (η : ℝ) : Continuous fun z : (ℂ × ℝ) × ℝ => amoCoc η z.1 z.2 := by
  exact continuous_transferFamily 1 one_ne_zero (2 * η)

lemma continuous_dualCoc {η : ℝ} (hη : η ≠ 0) :
    Continuous fun z : (ℂ × ℝ) × ℝ => dualCoc η z.1 z.2 := by
  exact continuous_transferFamily (η : ℂ) (by exact_mod_cast hη) 2

/-- **The AMO Lyapunov profiles** `ext-eq:AMO-profiles` on a set `K` of energies:
`L_E(y) = max(0, 2π|y| - c)` and `L̂_E(y) = c + 2π|y|`, `c = log(1/η)`.  These come from Avila's
global theory (`eq:two-direction`) and are a hypothesis here. -/
def AMOProfiles (α η : ℝ) (K : Set ℂ) : Prop :=
  ∀ E ∈ K, ∀ y : ℝ,
    lyapunov α (amoCoc η (E, y)) = max 0 (2 * Real.pi * |y| - Real.log (1 / η)) ∧
      lyapunov α (dualCoc η (E, y)) = Real.log (1 / η) + 2 * Real.pi * |y|

/-! ### The widths -/

/-- The paper's explicit widths for `0 < η < 1`, `s > 0`, `ℓ > log(1/η)`. -/
structure Widths (η s ℓ : ℝ) : Prop where
  hη0 : 0 < η
  hη1 : η < 1
  hs : 0 < s
  hℓ : Real.log (1 / η) < ℓ

namespace Widths

variable {η s ℓ : ℝ}

/-- `c = log(1/η)`. -/
def c (η : ℝ) : ℝ := Real.log (1 / η)
/-- `ν = min(s, ℓ - c)`. -/
def ν (η s ℓ : ℝ) : ℝ := min s (ℓ - c η)
def ℓ₀ (η s ℓ : ℝ) : ℝ := c η + ν η s ℓ / 4
def ℓ₁ (η s ℓ : ℝ) : ℝ := c η + ν η s ℓ / 2
def r₀ (η s ℓ : ℝ) : ℝ := ν η s ℓ / 16
def r₁ (η s ℓ : ℝ) : ℝ := ν η s ℓ / 8
def γ₁ (s : ℝ) : ℝ := 3 * s / 4
def γ₂ (η s ℓ : ℝ) : ℝ := c η + 3 * ν η s ℓ / 16

variable (W : Widths η s ℓ)
include W

lemma c_pos : 0 < c η := by
  unfold c
  exact Real.log_pos (by rw [one_div]; exact (one_lt_inv₀ W.hη0).2 W.hη1)

lemma ν_pos : 0 < ν η s ℓ := lt_min W.hs (by unfold c at *; linarith [W.hℓ])

omit W in
lemma ν_le_s : ν η s ℓ ≤ s := min_le_left _ _
omit W in
lemma ν_le_ℓ : ν η s ℓ ≤ ℓ - c η := min_le_right _ _

/-- `ext-eq:nested-widths`, first chain: `c < ℓ₀ < ℓ₁ < min(ℓ, c + s)`. -/
lemma nested_ℓ : c η < ℓ₀ η s ℓ ∧ ℓ₀ η s ℓ < ℓ₁ η s ℓ ∧ ℓ₁ η s ℓ < ℓ ∧ ℓ₁ η s ℓ < c η + s := by
  have h := W.ν_pos; have h1 : ν η s ℓ ≤ s := min_le_left _ _; have h2 : ν η s ℓ ≤ ℓ - c η := min_le_right _ _
  unfold ℓ₀ ℓ₁
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- `ext-eq:nested-widths`, second chain: `0 < r₀ < r₁ < min(s, ℓ₀ - c)`. -/
lemma nested_r : 0 < r₀ η s ℓ ∧ r₀ η s ℓ < r₁ η s ℓ ∧ r₁ η s ℓ < s ∧ r₁ η s ℓ < ℓ₀ η s ℓ - c η := by
  have h := W.ν_pos; have h1 : ν η s ℓ ≤ s := min_le_left _ _
  unfold r₀ r₁ ℓ₀
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- `ℓ₁ - c ≤ s/2 < γ₁ < s`. -/
lemma gap₁ : ℓ₁ η s ℓ - c η ≤ s / 2 ∧ s / 2 < γ₁ s ∧ γ₁ s < s := by
  have h1 : ν η s ℓ ≤ s := min_le_left _ _; have hs := W.hs
  unfold ℓ₁ γ₁
  refine ⟨by linarith, by linarith, by linarith⟩

/-- `c + r₁ < γ₂ < ℓ₀`. -/
lemma gap₂ : c η + r₁ η s ℓ < γ₂ η s ℓ ∧ γ₂ η s ℓ < ℓ₀ η s ℓ := by
  have h := W.ν_pos
  unfold r₁ γ₂ ℓ₀
  refine ⟨by linarith, by linarith⟩

/-- The two denominators of the inverse bound: `1 - e^{γ₁ - s} = 1 - e^{-s/4}` and
`1 - e^{γ₂ - ℓ₀} = 1 - e^{-ν/16}`, both positive. -/
lemma denominators :
    1 - Real.exp (γ₁ s - s) = 1 - Real.exp (-(s / 4)) ∧ 0 < 1 - Real.exp (-(s / 4)) ∧
      1 - Real.exp (γ₂ η s ℓ - ℓ₀ η s ℓ) = 1 - Real.exp (-(ν η s ℓ / 16)) ∧
        0 < 1 - Real.exp (-(ν η s ℓ / 16)) := by
  have hs := W.hs; have hν := W.ν_pos
  refine ⟨by unfold γ₁; ring_nf, sub_pos.2 (Real.exp_lt_one_iff.2 (by linarith)),
    by unfold γ₂ ℓ₀; ring_nf, sub_pos.2 (Real.exp_lt_one_iff.2 (by linarith))⟩

end Widths

/-! ### Strip growth from the AMO profiles -/

/-- **Uniform strip growth from the AMO profiles** (the first step of the proof of
Proposition 2.4).  Assume the AMO profiles on a compact set `K` of energies.  Then there are
`C₁, C₂, δ > 0` and a frequency window around `α` such that, for `E` within `δ` of `K`,
* `‖A⁰_{E,m}(x + iy)‖ ≤ C₁ e^{γ₁ m}` for `|y| ≤ ℓ₁/(2π)`, and
* `‖Â⁰_{E,m}(x + iy)‖ ≤ C₂ e^{γ₂ m}` for `|y| ≤ r₁/(2π)`. -/
theorem amo_strip_growth {α η s ℓ R : ℝ} (W : Widths η s ℓ) (hα : Irrational α) {K : Set ℂ}
    (hK : IsCompact K) (hKR : K ⊆ closedBall 0 R) (hprof : AMOProfiles α η K) :
    ∃ C₁ C₂ δ δα : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ 0 < δ ∧ 0 < δα ∧ ∀ α' : ℝ, |α' - α| < δα →
      ∀ E : ℂ, ‖E‖ ≤ R → (∃ k ∈ K, dist E k < δ) → ∀ (m : ℕ) (x : ℝ),
        (∀ y ∈ Icc (-(Widths.ℓ₁ η s ℓ / (2 * Real.pi))) (Widths.ℓ₁ η s ℓ / (2 * Real.pi)),
          ‖iter α' (amoCoc η (E, y)) m x‖ ≤ C₁ * Real.exp (Widths.γ₁ s * m)) ∧
        (∀ y ∈ Icc (-(Widths.r₁ η s ℓ / (2 * Real.pi))) (Widths.r₁ η s ℓ / (2 * Real.pi)),
          ‖iter α' (dualCoc η (E, y)) m x‖ ≤ C₂ * Real.exp (Widths.γ₂ η s ℓ * m)) := by
  have hpi : 0 < 2 * Real.pi := by positivity
  have hc := W.c_pos
  have hν := W.ν_pos
  -- the profile bounds on the two strips
  have habs : ∀ {w y : ℝ}, 0 ≤ w → y ∈ Icc (-(w / (2 * Real.pi))) (w / (2 * Real.pi)) →
      2 * Real.pi * |y| ≤ w := fun {w y} _ hy => by
    have := abs_le.2 ⟨hy.1, hy.2⟩
    rw [le_div_iff₀ hpi] at this
    linarith
  have hL1 : ∀ E ∈ K, ∀ y ∈ Icc (-(Widths.ℓ₁ η s ℓ / (2 * Real.pi))) (Widths.ℓ₁ η s ℓ / (2 * Real.pi)),
      lyapunov α (amoCoc η (E, y)) < Widths.γ₁ s := fun E hE y hy => by
    rw [(hprof E hE y).1]
    have h1 := habs (by unfold Widths.ℓ₁; linarith) hy
    have h2 := W.gap₁
    have h3 : 0 < Widths.γ₁ s := by unfold Widths.γ₁; linarith [W.hs]
    exact max_lt h3 (by unfold Widths.c at *; linarith [h2.1, h2.2.1])
  have hL2 : ∀ E ∈ K, ∀ y ∈ Icc (-(Widths.r₁ η s ℓ / (2 * Real.pi))) (Widths.r₁ η s ℓ / (2 * Real.pi)),
      lyapunov α (dualCoc η (E, y)) < Widths.γ₂ η s ℓ := fun E hE y hy => by
    rw [(hprof E hE y).2]
    have h1 := habs (by unfold Widths.r₁; linarith) hy
    have h2 := W.gap₂
    unfold Widths.c at *
    linarith [h2.1]
  obtain ⟨C₁, hC₁, δ₁, hδ₁, a₁, ha₁, hg₁⟩ := strip_growth (amoCoc η) (continuous_amoCoc η)
    (isSLCocycle_amoCoc η) hα (by unfold Widths.γ₁; linarith [W.hs]) hK hKR hL1
  obtain ⟨C₂, hC₂, δ₂, hδ₂, a₂, ha₂, hg₂⟩ := strip_growth (dualCoc η)
    (continuous_dualCoc W.hη0.ne') (isSLCocycle_dualCoc W.hη0.ne') hα
    (by unfold Widths.γ₂; linarith) hK hKR hL2
  refine ⟨C₁, C₂, min δ₁ δ₂, min a₁ a₂, hC₁, hC₂, lt_min hδ₁ hδ₂, lt_min ha₁ ha₂,
    fun α' hα' E hE ⟨k, hk, hEk⟩ m x => ⟨fun y hy => ?_, fun y hy => ?_⟩⟩
  · exact hg₁ α' (hα'.trans_le (min_le_left _ _)) E hE
      ⟨k, hk, hEk.trans_le (min_le_left _ _)⟩ y hy m x
  · exact hg₂ α' (hα'.trans_le (min_le_right _ _)) E hE
      ⟨k, hk, hEk.trans_le (min_le_right _ _)⟩ y hy m x

end AMO
