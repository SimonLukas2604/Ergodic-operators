/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# §3.9.3: rotation numbers and the Schwartzman homomorphism (book pp. 296–302)

Main results:
* `DF.homotopyLift` — **Proposition 3.9.9** (converse direction): homotopic maps `Ω → 𝕋` differ
  by `π ∘ ψ` for a continuous `ψ : Ω → ℝ` (proved with Mathlib's homotopy lifting for the
  covering `ℝ → 𝕋`; no compactness or connectedness of `Ω` is needed). This proves
  `DF.HomotopyLiftStatement` (`DF.homotopyLiftStatement`).
* `DF.exists_isLiftAlong` — lifts of `t ↦ φ(ϕ_t ω)` exist; `DF.isLiftAlong_unique` — they are
  unique up to an additive constant;
* `DF.FlowErgodic.ae_eq_const` — flow-invariant measurable functions are a.e. constant;
* `DF.ae_hasRotationNumber` — **Theorem 3.9.13(a), (b)**: for an ergodic flow on a compact
  metric space and `φ ∈ C(Ω, 𝕋)`, the rotation number `rot(φ; ω)` exists and is a.e. constant;
* `DF.schwartzman_general` — **Theorem 3.9.13** in full (existence of the Schwartzman
  homomorphism `A_μ`, a.e. equal to the rotation number, homotopy invariant and additive), for
  ergodic continuous flows on arbitrary compact spaces; `DF.schwartzman` — the resulting proof of
  `DF.SchwartzmanStatement` (compact metric spaces).

Deviation from the book: instead of approximating `φ` by maps that are `C¹` along the flow
(Lemma 3.9.11, Corollary 3.9.12) and using Birkhoff's theorem for flows, we lift the homotopy
`(s, ω) ↦ φ(ϕ_s ω) - φ(ω)`, `s ∈ [0, 1]`, to a continuous `L : [0,1] × Ω → ℝ`; the increment of
every lift over `[k, k+1]` is then `h(ϕ_k ω)` with `h = L(1, ·)` continuous, and the rotation
number is the Birkhoff limit of `h` under the time-one map. Flow-invariance of this limit plus
ergodicity of the flow give its a.e. constancy.
-/
import DamanikFillman.Ch3.Flows
import DamanikFillman.Ch3.Birkhoff

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Filter Set Function Topology unitInterval

namespace DF

lemma isCoveringMap_coe_unit : IsCoveringMap ((↑) : ℝ → UnitAddCircle) :=
  AddCircle.isCoveringMap_coe 1

/-! ### Proposition 3.9.9 -/

section lift

variable {Ω : Type*} [TopologicalSpace Ω]

/-- **Proposition 3.9.9** (converse direction): if `φ ≃ φ'` in `C(Ω, 𝕋)` then
`φ = φ' + π ∘ ψ` for some continuous `ψ : Ω → ℝ`. -/
theorem homotopyLift {φ φ' : C(Ω, UnitAddCircle)} (h : φ.Homotopic φ') :
    ∃ ψ : C(Ω, ℝ), ∀ x, φ x = φ' x + (ψ x : UnitAddCircle) := by
  obtain ⟨F⟩ := h
  let K : C(I × Ω, UnitAddCircle) :=
    ⟨fun p => F (σ p.1, p.2) - φ' p.2,
      (F.continuous.comp ((continuous_symm.comp continuous_fst).prodMk continuous_snd)).sub
        (φ'.continuous.comp continuous_snd)⟩
  have hK0 : ∀ a, K (0, a) = ((ContinuousMap.const Ω (0 : ℝ) a : ℝ) : UnitAddCircle) := by
    intro a
    simp [K]
  let L := isCoveringMap_coe_unit.liftHomotopy K (ContinuousMap.const Ω 0) hK0
  refine ⟨⟨fun a => L (1, a), L.continuous.comp (continuous_const.prodMk continuous_id)⟩,
    fun a => ?_⟩
  have h1 : ((L (1, a) : ℝ) : UnitAddCircle) = K (1, a) :=
    congr_fun (isCoveringMap_coe_unit.liftHomotopy_lifts K (ContinuousMap.const Ω 0) hK0) (1, a)
  show φ a = φ' a + ((L (1, a) : ℝ) : UnitAddCircle)
  rw [h1]
  simp [K]

/-- The Statement `DF.HomotopyLiftStatement` holds. -/
theorem homotopyLiftStatement : HomotopyLiftStatement :=
  fun _ _ _ _ _ h => homotopyLift h

/-- Two lifts of the same map along an orbit differ by a constant. -/
lemma isLiftAlong_unique {ϕ : Flow ℝ Ω} {φ : C(Ω, UnitAddCircle)} {ω : Ω} {g₁ g₂ : ℝ → ℝ}
    (h₁ : IsLiftAlong ϕ φ ω g₁) (h₂ : IsLiftAlong ϕ φ ω g₂) : ∀ t, g₁ t - g₂ t = g₁ 0 - g₂ 0 := by
  intro t
  refine isCoveringMap_coe_unit.const_of_comp (h₁.1.sub h₂.1) (fun a a' => ?_) t 0
  show ((g₁ a - g₂ a : ℝ) : UnitAddCircle) = ((g₁ a' - g₂ a' : ℝ) : UnitAddCircle)
  rw [AddCircle.coe_sub, AddCircle.coe_sub, h₁.2, h₂.2, h₁.2, h₂.2, sub_self, sub_self]

/-- Lifts of `t ↦ φ(ϕ_t ω)` exist (3.9.29). -/
lemma exists_isLiftAlong (ϕ : Flow ℝ Ω) (φ : C(Ω, UnitAddCircle)) (ω : Ω) :
    ∃ g, IsLiftAlong ϕ φ ω g := by
  let f : C(ℝ, UnitAddCircle) := ⟨fun t => φ (ϕ t ω),
    φ.continuous.comp (ϕ.continuous continuous_id continuous_const)⟩
  obtain ⟨e, he⟩ := QuotientAddGroup.mk_surjective (f 0)
  obtain ⟨G, ⟨-, hG⟩, -⟩ := isCoveringMap_coe_unit.existsUnique_continuousMap_lifts f 0 e he
  exact ⟨G, G.continuous, fun t => congr_fun hG t⟩

end lift

/-! ### Ergodic flows -/

section flow

variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω]

/-- Flow-invariant measurable real functions are a.e. constant for an ergodic flow. -/
theorem FlowErgodic.ae_eq_const {ϕ : Flow ℝ Ω} {μ : Measure Ω} (h : FlowErgodic ϕ μ)
    {F : Ω → ℝ} (hF : Measurable F) (hinv : ∀ t x, F (ϕ t x) = F x) :
    ∃ c, ∀ᵐ x ∂μ, F x = c := by
  obtain ⟨c, hc⟩ := Filter.exists_eventuallyEq_const_of_forall_separating (l := ae μ) (f := F)
    MeasurableSet fun U hU => by
      have hE : MeasurableSet (F ⁻¹' U) := hF hU
      have hEi : ∀ t, ϕ t ⁻¹' (F ⁻¹' U) = F ⁻¹' U := fun t => by
        ext x; simp [hinv t x]
      rcases h.2 _ hE hEi with h0 | h0
      · right; exact measure_eq_zero_iff_ae_notMem.1 h0
      · left
        exact (measure_eq_zero_iff_ae_notMem.1 h0).mono fun x hx => by simpa using hx
  exact ⟨c, hc⟩

variable [CompactSpace Ω] (ϕ : Flow ℝ Ω) (φ : C(Ω, UnitAddCircle))

/-- The homotopy `(s, ω) ↦ φ(ϕ_s ω) - φ(ω)`, `s ∈ [0, 1]`. -/
def incHom : C(I × Ω, UnitAddCircle) :=
  ⟨fun p => φ (ϕ p.1 p.2) - φ p.2,
    (φ.continuous.comp (ϕ.continuous (continuous_subtype_val.comp continuous_fst)
      continuous_snd)).sub (φ.continuous.comp continuous_snd)⟩

lemma incHom_zero (a : Ω) : incHom ϕ φ (0, a) = ((ContinuousMap.const Ω (0 : ℝ) a : ℝ) :
    UnitAddCircle) := by
  simp [incHom, Flow.map_zero_apply]

/-- A continuous lift `L` of `incHom`, with `L(0, ω) = 0`. -/
def incLift : C(I × Ω, ℝ) :=
  isCoveringMap_coe_unit.liftHomotopy (incHom ϕ φ) (ContinuousMap.const Ω 0) (incHom_zero ϕ φ)

lemma incLift_lifts (p : I × Ω) : ((incLift ϕ φ p : ℝ) : UnitAddCircle) = incHom ϕ φ p :=
  congr_fun (isCoveringMap_coe_unit.liftHomotopy_lifts (incHom ϕ φ) (ContinuousMap.const Ω 0)
    (incHom_zero ϕ φ)) p

lemma incLift_zero (a : Ω) : incLift ϕ φ (0, a) = 0 :=
  isCoveringMap_coe_unit.liftHomotopy_zero (incHom ϕ φ) (ContinuousMap.const Ω 0)
    (incHom_zero ϕ φ) a

variable {ϕ φ}

/-- The increment of a lift over `[a, a + s]`, `s ∈ [0, 1]`, is `L(s, ϕ_a ω)`. -/
lemma lift_incr {ω : Ω} {g : ℝ → ℝ} (hg : IsLiftAlong ϕ φ ω g) (a : ℝ) (s : I) :
    g (a + s) - g a = incLift ϕ φ (s, ϕ a ω) := by
  have := isCoveringMap_coe_unit.eq_of_comp_eq (A := I) (g₁ := fun s : I => g (a + s) - g a)
    (g₂ := fun s : I => incLift ϕ φ (s, ϕ a ω))
    ((hg.1.comp (continuous_const.add continuous_subtype_val)).sub continuous_const)
    ((incLift ϕ φ).continuous.comp (continuous_id.prodMk continuous_const))
    (by
      funext s
      simp only [comp_apply]
      rw [incLift_lifts, AddCircle.coe_sub, hg.2, hg.2]
      simp only [incHom, ContinuousMap.coe_mk]
      rw [add_comm, Flow.map_add])
    0 (by simp [incLift_zero])
  exact congr_fun this s

variable (ϕ φ)

lemma exists_incLift_bound : ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ p, |incLift ϕ φ p| ≤ Cb := by
  obtain ⟨C, hC⟩ := (isCompact_range (incLift ϕ φ).continuous).isBounded.exists_norm_le
  exact ⟨max C 0, le_max_right _ _, fun p => (hC _ ⟨p, rfl⟩).trans (le_max_left _ _)⟩

variable {ϕ φ}

lemma lift_shift_bound {Cb : ℝ} (hCb0 : 0 ≤ Cb) (hCb : ∀ p, |incLift ϕ φ p| ≤ Cb) {ω : Ω}
    {g : ℝ → ℝ} (hg : IsLiftAlong ϕ φ ω g) (s a : ℝ) : |g (a + s) - g a| ≤ (|s| + 1) * Cb := by
  have hnat : ∀ n : ℕ, ∀ a s : ℝ, 0 ≤ s → s ≤ n + 1 → |g (a + s) - g a| ≤ (n + 1) * Cb := by
    intro n
    induction n with
    | zero =>
      intro a s hs0 hs1
      have := lift_incr hg a ⟨s, hs0, by simpa using hs1⟩
      simp only at this
      rw [this]; simpa using hCb _
    | succ n ih =>
      intro a s hs0 hs1
      by_cases hs : s ≤ n + 1
      · exact (ih a s hs0 hs).trans (by push_cast; nlinarith)
      · push Not at hs
        have h1 := ih a (s - 1) (by linarith) (by push_cast at hs1; linarith)
        have h2 := lift_incr hg (a + (s - 1)) ⟨1, by norm_num, le_rfl⟩
        simp only at h2
        have h3 := hCb ((1 : I), ϕ (a + (s - 1)) ω)
        rw [show a + (s - 1) + 1 = a + s by ring] at h2
        calc |g (a + s) - g a| = |(g (a + s) - g (a + (s - 1))) + (g (a + (s - 1)) - g a)| := by
              ring_nf
          _ ≤ |g (a + s) - g (a + (s - 1))| + |g (a + (s - 1)) - g a| := abs_add_le _ _
          _ ≤ Cb + (n + 1) * Cb := by
              apply add_le_add _ h1
              rw [h2]
              exact h3
          _ = ((n + 1 : ℕ) + 1) * Cb := by push_cast; ring
  have hpos : ∀ a s : ℝ, 0 ≤ s → |g (a + s) - g a| ≤ (s + 1) * Cb := by
    intro a s hs
    have := hnat ⌊s⌋₊ a s hs (Nat.lt_floor_add_one s).le
    exact this.trans (mul_le_mul_of_nonneg_right (by linarith [Nat.floor_le hs]) hCb0)
  rcases le_total 0 s with hs | hs
  · rw [abs_of_nonneg hs]; exact hpos a s hs
  · have := hpos (a + s) (-s) (by linarith)
    rw [show a + s + -s = a by ring, abs_sub_comm] at this
    rw [abs_of_nonpos hs]; exact this

/-- The increment function `h = L(1, ·)`. -/
def rotInc (ϕ : Flow ℝ Ω) (φ : C(Ω, UnitAddCircle)) (x : Ω) : ℝ := incLift ϕ φ ((1 : I), x)

lemma continuous_rotInc : Continuous (rotInc ϕ φ) :=
  (incLift ϕ φ).continuous.comp (continuous_const.prodMk continuous_id)

lemma flow_natCast (k : ℕ) (x : Ω) : ϕ (k : ℝ) x = (ϕ 1)^[k] x := by
  induction k generalizing x with
  | zero => simp [Flow.map_zero_apply]
  | succ k ih => rw [iterate_succ_apply, ← ih]; push_cast; rw [Flow.map_add]

lemma lift_sum {ω : Ω} {g : ℝ → ℝ} (hg : IsLiftAlong ϕ φ ω g) (n : ℕ) :
    g n - g 0 = birkhoffSum (ϕ 1) (rotInc ϕ φ) n ω := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [birkhoffSum_succ_apply, ← ih]
    have := lift_incr hg n (1 : I)
    simp only [Set.Icc.coe_one] at this
    push_cast
    rw [rotInc, ← flow_natCast]
    linarith

/-- If the Birkhoff averages of `h` under the time-one map converge to `r`, then every lift `g`
along `ω` satisfies `g(t)/t → r`. -/
lemma tendsto_lift_of_tendsto {Cb : ℝ} (hCb0 : 0 ≤ Cb) (hCb : ∀ p, |incLift ϕ φ p| ≤ Cb)
    {ω : Ω} {g : ℝ → ℝ} (hg : IsLiftAlong ϕ φ ω g) {r : ℝ}
    (hr : Tendsto (fun n : ℕ => birkhoffSum (ϕ 1) (rotInc ϕ φ) n ω / n) atTop (𝓝 r)) :
    Tendsto (fun t => g t / t) atTop (𝓝 r) := by
  have h1 : Tendsto (fun t : ℝ => birkhoffSum (ϕ 1) (rotInc ϕ φ) ⌊t⌋₊ ω / ⌊t⌋₊ * (⌊t⌋₊ / t))
      atTop (𝓝 (r * 1)) :=
    (hr.comp tendsto_nat_floor_atTop).mul tendsto_nat_floor_div_atTop
  have h2 : Tendsto (fun t : ℝ => (g t - g ⌊t⌋₊ + g 0) / t) atTop (𝓝 0) := by
    have hb : ∀ t, 0 ≤ t → |g t - g ⌊t⌋₊ + g 0| ≤ Cb + |g 0| := by
      intro t ht
      have hs0 : 0 ≤ t - ⌊t⌋₊ := by linarith [Nat.floor_le ht]
      have hs1 : t - ⌊t⌋₊ ≤ 1 := by linarith [Nat.lt_floor_add_one t]
      have := lift_incr hg ⌊t⌋₊ ⟨t - ⌊t⌋₊, hs0, hs1⟩
      simp only at this
      rw [show (⌊t⌋₊ : ℝ) + (t - ⌊t⌋₊) = t by ring] at this
      rw [this]
      exact (abs_add_le _ _).trans (add_le_add (hCb _) le_rfl)
    have h0 : Tendsto (fun t : ℝ => (Cb + |g 0|) / t) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    refine squeeze_zero_norm' ?_ h0
    filter_upwards [eventually_gt_atTop 0] with t ht
    rw [Real.norm_eq_abs, abs_div, abs_of_pos ht]
    exact div_le_div_of_nonneg_right (hb t ht.le) ht.le
  rw [mul_one] at h1
  have h3 := h1.add h2
  rw [add_zero] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with t ht
  have hfl : (0 : ℝ) < ⌊t⌋₊ := by
    have : 1 ≤ ⌊t⌋₊ := Nat.le_floor (by exact_mod_cast ht)
    exact_mod_cast this
  have ht0 : t ≠ 0 := by linarith
  rw [← lift_sum hg]
  field_simp
  ring

/-- Birkhoff averages of `h` at `ω` and `ϕ_s ω` are asymptotic. -/
lemma tendsto_sub_birkhoff {Cb : ℝ} (hCb0 : 0 ≤ Cb) (hCb : ∀ p, |incLift ϕ φ p| ≤ Cb)
    (ω : Ω) (s : ℝ) :
    Tendsto (fun n : ℕ => birkhoffSum (ϕ 1) (rotInc ϕ φ) n (ϕ s ω) / n -
      birkhoffSum (ϕ 1) (rotInc ϕ φ) n ω / n) atTop (𝓝 0) := by
  obtain ⟨g, hg⟩ := exists_isLiftAlong ϕ φ ω
  have hg' : IsLiftAlong ϕ φ (ϕ s ω) (fun t => g (t + s)) :=
    ⟨hg.1.comp (continuous_id.add continuous_const), fun t => by rw [hg.2, Flow.map_add]⟩
  have hb : ∀ n : ℕ, |birkhoffSum (ϕ 1) (rotInc ϕ φ) n (ϕ s ω) -
      birkhoffSum (ϕ 1) (rotInc ϕ φ) n ω| ≤ 2 * ((|s| + 1) * Cb) := by
    intro n
    rw [← lift_sum hg', ← lift_sum hg]
    simp only [zero_add]
    have e1 := lift_shift_bound hCb0 hCb hg s n
    have e2 := lift_shift_bound hCb0 hCb hg s 0
    rw [zero_add] at e2
    calc |g (n + s) - g s - (g n - g 0)| = |(g (n + s) - g n) - (g (0 + s) - g 0)| := by
          rw [zero_add]; ring_nf
      _ ≤ |g (n + s) - g n| + |g (0 + s) - g 0| := abs_sub _ _
      _ ≤ (|s| + 1) * Cb + (|s| + 1) * Cb := by rw [zero_add]; exact add_le_add e1 e2
      _ = _ := by ring
  have h0 : Tendsto (fun n : ℕ => 2 * ((|s| + 1) * Cb) / n) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  refine squeeze_zero_norm' ?_ h0
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.norm_eq_abs, ← sub_div, abs_div, abs_of_pos hnpos]
  exact div_le_div_of_nonneg_right (hb n) hnpos.le

/-- **Theorem 3.9.13 (a), (b)**: for an ergodic flow on a compact metric space and
`φ ∈ C(Ω, 𝕋)`, there is a constant `A` such that for a.e. `ω` and every lift `g` of `φ` along
the orbit of `ω`, `g(t)/t → A`. -/
theorem ae_hasRotationNumber {μ : Measure Ω} [IsProbabilityMeasure μ] (hϕ : FlowErgodic ϕ μ)
    (φ : C(Ω, UnitAddCircle)) : ∃ A : ℝ, ∀ᵐ x ∂μ, HasRotationNumber ϕ φ x A := by
  obtain ⟨Cb, hCb0, hCb⟩ := exists_incLift_bound ϕ φ
  set T1 := ϕ 1
  set h := rotInc ϕ φ
  have hT1 : MeasurePreserving T1 μ μ := hϕ.1 1
  have hhm : Measurable h := (continuous_rotInc (ϕ := ϕ) (φ := φ)).measurable
  have hhi : Integrable h μ := by
    refine (integrable_const Cb).mono' hhm.aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]; exact hCb _
  set u : ℕ → Ω → ℝ := fun n x => birkhoffSum T1 h n x / n
  have hum : ∀ n, Measurable (u n) := fun n =>
    (Birkhoff.measurable_birkhoffSum hT1.measurable hhm n).div_const _
  set Conv := {x | ∃ c, Tendsto (fun n => u n x) atTop (𝓝 c)}
  have hConv : MeasurableSet Conv :=
    StronglyMeasurable.measurableSet_exists_tendsto fun n => (hum n).stronglyMeasurable
  set F : Ω → ℝ := Conv.indicator fun x => limsup (fun n => u n x) atTop
  have hFm : Measurable F := (Measurable.limsup hum).indicator hConv
  have hinvConv : ∀ t x, ϕ t x ∈ Conv ↔ x ∈ Conv := by
    intro t x
    have hd := tendsto_sub_birkhoff hCb0 hCb x t
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_⟩
      have := hc.sub hd
      rw [sub_zero] at this
      refine this.congr' (Eventually.of_forall fun n => ?_)
      simp only [u, T1, h]; ring
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_⟩
      have := hc.add hd
      rw [add_zero] at this
      refine this.congr' (Eventually.of_forall fun n => ?_)
      simp only [u, T1, h]; ring
  have hFinv : ∀ t x, F (ϕ t x) = F x := by
    intro t x
    by_cases hx : x ∈ Conv
    · have hx' : ϕ t x ∈ Conv := (hinvConv t x).2 hx
      obtain ⟨c, hc⟩ := hx
      have hd := tendsto_sub_birkhoff hCb0 hCb x t
      have hc' : Tendsto (fun n => u n (ϕ t x)) atTop (𝓝 c) := by
        have := hc.add hd
        rw [add_zero] at this
        refine this.congr' (Eventually.of_forall fun n => ?_)
        simp only [u, T1, h]; ring
      simp only [F, indicator_of_mem hx', indicator_of_mem (show x ∈ Conv from ⟨c, hc⟩),
        hc.limsup_eq, hc'.limsup_eq]
    · have hx' : ϕ t x ∉ Conv := fun h => hx ((hinvConv t x).1 h)
      simp only [F, indicator_of_notMem hx, indicator_of_notMem hx']
  obtain ⟨c, hc⟩ := hϕ.ae_eq_const hFm hFinv
  refine ⟨c, ?_⟩
  filter_upwards [hc, Birkhoff.ae_tendsto_of_measurable hT1 hhi hhm] with x hx hB g hg
  obtain ⟨L, hL⟩ := hB
  simp only [Birkhoff.birkhoffAverage_eq_div] at hL
  have hxC : x ∈ Conv := ⟨L, hL⟩
  have : F x = L := by simp only [F, indicator_of_mem hxC]; exact hL.limsup_eq
  rw [hx] at this
  rw [this]
  exact tendsto_lift_of_tendsto hCb0 hCb hg hL

/-- **Theorem 3.9.13** (the Schwartzman homomorphism), for an ergodic continuous flow on any
compact topological space (with a σ-algebra containing the open sets): there is
`A_μ : C(Ω, 𝕋) → ℝ` with `rot(φ; ω) = A_μ(φ)` for a.e. `ω` and every lift, which is constant on
homotopy classes and additive. -/
theorem schwartzman_general {μ : Measure Ω} [IsProbabilityMeasure μ] (hϕ : FlowErgodic ϕ μ) :
    ∃ A : C(Ω, UnitAddCircle) → ℝ,
      (∀ φ, ∀ᵐ x ∂μ, HasRotationNumber ϕ φ x (A φ)) ∧
      (∀ φ φ', φ.Homotopic φ' → A φ = A φ') ∧
      (∀ φ φ', A (φ + φ') = A φ + A φ') := by
  choose A hA using fun φ => ae_hasRotationNumber hϕ φ
  haveI : (ae μ).NeBot := ae_neBot.2 (IsProbabilityMeasure.ne_zero μ)
  refine ⟨A, hA, ?_, ?_⟩
  · intro φ φ' hφ
    obtain ⟨ψ, hψ⟩ := homotopyLift hφ
    obtain ⟨Cψ, hCψ⟩ := (isCompact_range ψ.continuous).isBounded.exists_norm_le
    obtain ⟨x, hx, hx'⟩ := ((hA φ).and (hA φ')).exists
    obtain ⟨g', hg'⟩ := exists_isLiftAlong ϕ φ' x
    have hg : IsLiftAlong ϕ φ x (fun t => g' t + ψ (ϕ t x)) :=
      ⟨hg'.1.add (ψ.continuous.comp (ϕ.continuous continuous_id continuous_const)),
        fun t => by rw [AddCircle.coe_add, hg'.2, hψ]⟩
    have h1 := hx _ hg
    have h2 := hx' _ hg'
    have h3 : Tendsto (fun t : ℝ => ψ (ϕ t x) / t) atTop (𝓝 0) := by
      refine squeeze_zero_norm' ?_ ((tendsto_const_nhds (x := Cψ)).div_atTop tendsto_id)
      filter_upwards [eventually_gt_atTop 0] with t ht
      rw [norm_div, Real.norm_of_nonneg ht.le]
      exact div_le_div_of_nonneg_right (hCψ _ ⟨_, rfl⟩) ht.le
    have h4 := h2.add h3
    rw [add_zero] at h4
    refine tendsto_nhds_unique h1 (h4.congr' ?_)
    filter_upwards [eventually_ne_atTop 0] with t ht
    simp only [add_div]
  · intro φ φ'
    obtain ⟨x, hx, hx', hx''⟩ := ((hA (φ + φ')).and ((hA φ).and (hA φ'))).exists
    obtain ⟨g, hg⟩ := exists_isLiftAlong ϕ φ x
    obtain ⟨g', hg'⟩ := exists_isLiftAlong ϕ φ' x
    have hsum : IsLiftAlong ϕ (φ + φ') x (fun t => g t + g' t) :=
      ⟨hg.1.add hg'.1, fun t => by rw [AddCircle.coe_add, hg.2, hg'.2]; rfl⟩
    refine tendsto_nhds_unique (hx _ hsum) (((hx' _ hg).add (hx'' _ hg')).congr' ?_)
    filter_upwards with t
    simp only [add_div]

/-- **Theorem 3.9.13**: `DF.SchwartzmanStatement` holds. -/
theorem schwartzman : SchwartzmanStatement :=
  fun _ _ _ _ _ _ _ _ hϕ => schwartzman_general hϕ

end flow

end DF
