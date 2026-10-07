/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# §2.6  Basic bounds on spreading  (book pp. 168–178)

The unitary group is `DF.propagator V t = e^{-itH}` (Mathlib's `NormedSpace.exp`).

## Main results
* `DF.propagator_mem_unitary`, `DF.norm_propagator_apply` — `e^{-itH}` is unitary.
* `DF.schr_pow_dlt_apply_eq_zero` — finite propagation speed: `⟨δₙ, Hᵏ δ₀⟩ = 0` for `k < |n|`.
* **Theorem 2.6.1**, (2.6.3): `DF.spreading_bound` — for `t ≥ 0` and `|n| ≥ ν₀ t`,
  `ν₀ = 2e‖H‖`: `|⟨δₙ, e^{-itH} δ₀⟩|² ≤ 4 e^{-(log 4)|n|}` (the book: `C = 16`).
* **Theorem 2.6.1**, (2.6.4): `DF.spreading_bound_avg` (time-averaged version, `C = 5`,
  `c = log 4`), with the time average `DF.expTimeAvg` of (2.6.2).
* **Theorem 2.6.2**, (2.6.8): `DF.ballistic_bound` — the ballistic upper bound
  `|X|^p_{δ₀}(t) ≤ C (t^p + 1)` for the moments `DF.schrMoment` (2.6.1), together with
  summability of the defining series; (2.6.9): `DF.ballistic_bound_avg`.
* **Exercise 2.6.5**: `DF.norm_pow_sub_pow_le` — `‖Aᵏ - Bᵏ‖ ≤ k max(‖A‖,‖B‖)^{k-1} ‖A - B‖`.

## Not formalized
Theorem 2.6.3 (pure point spectrum), Exercise 2.6.3, and
Theorems 2.6.4–2.6.5 (which involve the unbounded position operator `X` and its Heisenberg
evolution).
-/
import DamanikFillman.Ch2.Schrodinger

noncomputable section

open scoped InnerProductSpace ComplexConjugate Nat
open L2 Filter Topology NormedSpace

namespace DF

/-- **Exercise 2.6.5**: `‖Aᵏ - Bᵏ‖ ≤ k · max(‖A‖, ‖B‖)^{k-1} ‖A - B‖` in any normed ring. -/
theorem norm_pow_sub_pow_le {R : Type*} [NormedRing R] (A B : R) (k : ℕ) :
    ‖A ^ k - B ^ k‖ ≤ k * max ‖A‖ ‖B‖ ^ (k - 1) * ‖A - B‖ := by
  set M := max ‖A‖ ‖B‖
  have hM : 0 ≤ M := le_max_of_le_left (norm_nonneg _)
  have hB : ∀ j : ℕ, ‖B ^ j‖ ≤ M ^ j ∨ j = 0 := by
    intro j
    rcases Nat.eq_zero_or_pos j with h | h
    · exact Or.inr h
    · exact Or.inl ((norm_pow_le' B h).trans (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) j))
  induction k with
  | zero => simp
  | succ k ih =>
    have hsplit : A ^ (k + 1) - B ^ (k + 1) = A * (A ^ k - B ^ k) + (A - B) * B ^ k := by
      rw [pow_succ', pow_succ']; noncomm_ring
    rw [hsplit]
    have hA : ‖A‖ ≤ M := le_max_left _ _
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · have hBk : ‖B ^ k‖ ≤ M ^ k := (norm_pow_le' B hk).trans
        (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) k)
      calc ‖A * (A ^ k - B ^ k) + (A - B) * B ^ k‖
          ≤ ‖A‖ * ‖A ^ k - B ^ k‖ + ‖A - B‖ * ‖B ^ k‖ :=
            (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
        _ ≤ M * (k * M ^ (k - 1) * ‖A - B‖) + ‖A - B‖ * M ^ k := by gcongr
        _ = ((k + 1 : ℕ) : ℝ) * M ^ (k + 1 - 1) * ‖A - B‖ := by
            obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
            simp only [Nat.add_sub_cancel, pow_succ]; push_cast; ring

variable {V : ℤ → ℝ}

/-- The unitary group `e^{-itH}`. -/
def propagator (V : ℤ → ℝ) (t : ℝ) : Op := exp ((-(t * Complex.I)) • schr V)

lemma propagator_mem_unitary (hV : BddPot V) (t : ℝ) :
    propagator V t ∈ unitary Op := by
  have hsa : IsSelfAdjoint (((-t : ℝ) : ℂ) • schr V) := by
    rw [IsSelfAdjoint, star_smul, (isSelfAdjoint_schr hV).star_eq, Complex.star_def,
      Complex.conj_ofReal]
  have hmem := (selfAdjoint.expUnitary (⟨((-t : ℝ) : ℂ) • schr V, hsa⟩ : selfAdjoint Op)).prop
  have hs : (-((t : ℂ) * Complex.I)) • schr V = Complex.I • (((-t : ℝ) : ℂ) • schr V) := by
    rw [smul_smul]
    congr 1
    push_cast; ring
  have e : propagator V t = ((selfAdjoint.expUnitary (⟨((-t : ℝ) : ℂ) • schr V, hsa⟩ :
      selfAdjoint Op)) : Op) := by
    rw [propagator, hs]
    rfl
  rw [e]; exact hmem

lemma norm_propagator_apply (hV : BddPot V) (t : ℝ) (ψ : L2 ℤ) :
    ‖propagator V t ψ‖ = ‖ψ‖ :=
  ContinuousLinearMap.norm_map_of_mem_unitary (propagator_mem_unitary hV t) ψ

/-- Finite propagation speed: `(Hᵏ δ₀)(m) = 0` for `k < |m|`. -/
theorem schr_pow_dlt_apply_eq_zero (hV : BddPot V) (k : ℕ) (m : ℤ) (hk : (k : ℤ) < |m|) :
    (((schr V) ^ k) (dlt 0)) m = 0 := by
  induction k generalizing m with
  | zero =>
    simp only [pow_zero, ContinuousLinearMap.one_apply, dlt_apply]
    have : m ≠ 0 := by rintro rfl; simp at hk
    simp [this]
  | succ k ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply, schr_apply hV]
    push_cast at hk
    rw [lt_abs] at hk
    have h1 := ih (m + 1) (by rw [lt_abs]; omega)
    have h2 := ih (m - 1) (by rw [lt_abs]; omega)
    have h3 := ih m (by rw [lt_abs]; omega)
    rw [h1, h2, h3]; ring

lemma norm_schr_pow_dlt_apply_le (k : ℕ) (n : ℤ) :
    ‖(((schr V) ^ k) (dlt 0)) n‖ ≤ ‖schr V‖ ^ k := by
  calc ‖(((schr V) ^ k) (dlt 0)) n‖ ≤ ‖((schr V) ^ k) (dlt 0)‖ := lp.norm_apply_le_norm (by norm_num) _ n
    _ ≤ ‖(schr V) ^ k‖ * ‖dlt 0‖ := ContinuousLinearMap.le_opNorm _ _
    _ = ‖(schr V) ^ k‖ := by rw [norm_dlt, mul_one]
    _ ≤ ‖schr V‖ ^ k := by
        rcases Nat.eq_zero_or_pos k with rfl | hk
        · simp only [pow_zero]
          exact ContinuousLinearMap.norm_id_le
        · exact norm_pow_le' _ hk

/-- Power series for the matrix elements of `e^{-itH}`. -/
lemma hasSum_propagator_apply (t : ℝ) (n : ℤ) :
    HasSum (fun k : ℕ => ((k ! : ℂ)⁻¹) * ((-(t * Complex.I)) ^ k * (((schr V) ^ k) (dlt 0)) n))
      (propagator V t (dlt 0) n) := by
  have hs := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) ((-(t * Complex.I)) • schr V)
  set Φ : Op →L[ℂ] ℂ := (innerSL ℂ (dlt n)).comp (ContinuousLinearMap.apply ℂ (L2 ℤ) (dlt 0))
  have h := hs.mapL Φ
  have hΦ : ∀ T : Op, Φ T = T (dlt 0) n := by
    intro T; simp [Φ, inner_dlt]
  simp only [hΦ] at h
  refine h.congr_fun fun k => ?_
  simp only [smul_pow, ContinuousLinearMap.smul_apply, lp.coeFn_smul, Pi.smul_apply,
    smul_eq_mul]

/-- The elementary bound `aᵏ / k! ≤ 2⁻ᵏ` for `0 ≤ a ≤ k / (2e)`. -/
lemma pow_div_factorial_le_half_pow {a : ℝ} (ha : 0 ≤ a) {k : ℕ}
    (hak : a ≤ k / (2 * Real.exp 1)) : a ^ k / k ! ≤ (1 / 2) ^ k := by
  have he := Real.exp_pos 1
  have h1 : a ^ k ≤ (k / (2 * Real.exp 1)) ^ k := pow_le_pow_left₀ ha hak k
  have h2 : (k : ℝ) ^ k / k ! ≤ Real.exp k := Real.pow_div_factorial_le_exp (k : ℝ) (Nat.cast_nonneg k) k
  have hf : (0 : ℝ) < k ! := by exact_mod_cast Nat.factorial_pos k
  calc a ^ k / k ! ≤ (k / (2 * Real.exp 1)) ^ k / k ! := by gcongr
    _ = ((k : ℝ) ^ k / k !) / (2 * Real.exp 1) ^ k := by rw [div_pow]; ring
    _ ≤ Real.exp k / (2 * Real.exp 1) ^ k := by gcongr
    _ = Real.exp k / (2 ^ k * Real.exp k) := by rw [mul_pow, Real.exp_one_pow]
    _ = 1 / 2 ^ k := by field_simp
    _ = (1 / 2) ^ k := by rw [one_div_pow]

/-- **Theorem 2.6.1**, estimate (2.6.3): if `t ≥ 0` and `|n| ≥ ν₀ t` with `ν₀ = 2e‖H‖`, then
`|⟨δₙ, e^{-itH} δ₀⟩|² ≤ 4 e^{-(log 4)|n|}`. -/
theorem spreading_bound (hV : BddPot V) {t : ℝ} (ht : 0 ≤ t) {n : ℤ}
    (hn : 2 * Real.exp 1 * ‖schr V‖ * t ≤ |(n : ℝ)|) :
    ‖⟪dlt n, propagator V t (dlt 0)⟫_ℂ‖ ^ 2 ≤ 4 * Real.exp (-(Real.log 4) * |(n : ℝ)|) := by
  rw [inner_dlt]
  set N := n.natAbs
  have hN : (N : ℝ) = |(n : ℝ)| := by simp [N, Nat.cast_natAbs, Int.cast_abs]
  set f : ℕ → ℂ := fun k => ((k ! : ℂ)⁻¹) * ((-(t * Complex.I)) ^ k * (((schr V) ^ k) (dlt 0)) n)
  have hf := hasSum_propagator_apply (V := V) t n
  have hzero : ∀ k, k < N → f k = 0 := by
    intro k hk
    simp only [f]
    rw [schr_pow_dlt_apply_eq_zero hV k n (by
      have : (k : ℤ) < N := by exact_mod_cast hk
      simpa [N] using this)]
    ring
  have hsum0 : ∑ i ∈ Finset.range N, f i = 0 :=
    Finset.sum_eq_zero fun i hi => hzero i (Finset.mem_range.mp hi)
  have hshift : HasSum (fun k => f (k + N)) (propagator V t (dlt 0) n) := by
    have := (hasSum_nat_add_iff' N).mpr hf
    rwa [hsum0, sub_zero] at this
  have he := Real.exp_pos 1
  have hbound : ∀ k, ‖f (k + N)‖ ≤ (1 / 2) ^ N * (1 / 2) ^ k := by
    intro k
    have hnorm : ‖f (k + N)‖ = ((k + N)! : ℝ)⁻¹ *
        (t ^ (k + N) * ‖(((schr V) ^ (k + N)) (dlt 0)) n‖) := by
      simp only [f, norm_mul, norm_inv, norm_pow, norm_neg, Complex.norm_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, Complex.norm_natCast, abs_of_nonneg ht]
    rw [hnorm, ← pow_add, add_comm N k]
    have hk := norm_schr_pow_dlt_apply_le (V := V) (k + N) n
    have ha : t * ‖schr V‖ ≤ (k + N : ℕ) / (2 * Real.exp 1) := by
      rw [le_div_iff₀ (by positivity)]
      push_cast
      nlinarith [norm_nonneg (schr V)]
    have := pow_div_factorial_le_half_pow (by positivity) ha
    have hf' : (0 : ℝ) < (k + N)! := by exact_mod_cast Nat.factorial_pos _
    calc ((k + N)! : ℝ)⁻¹ * (t ^ (k + N) * ‖(((schr V) ^ (k + N)) (dlt 0)) n‖)
        ≤ ((k + N)! : ℝ)⁻¹ * (t ^ (k + N) * ‖schr V‖ ^ (k + N)) := by gcongr
      _ = (t * ‖schr V‖) ^ (k + N) / (k + N)! := by rw [mul_pow]; ring
      _ ≤ (1 / 2) ^ (k + N) := this
  have hg : HasSum (fun k : ℕ => (1 / 2 : ℝ) ^ N * (1 / 2) ^ k) ((1 / 2) ^ N * 2) :=
    hasSum_geometric_two.mul_left _
  have hle : ‖propagator V t (dlt 0) n‖ ≤ (1 / 2) ^ N * 2 := by
    rw [← hshift.tsum_eq]; exact tsum_of_norm_bounded hg hbound
  have h0 : 0 ≤ ‖propagator V t (dlt 0) n‖ := norm_nonneg _
  calc ‖propagator V t (dlt 0) n‖ ^ 2 ≤ ((1 / 2) ^ N * 2) ^ 2 := by gcongr
    _ = 4 * (1 / 4) ^ N := by rw [mul_pow, ← pow_mul, mul_comm N 2, pow_mul]; norm_num; ring
    _ = 4 * Real.exp (-(Real.log 4) * |(n : ℝ)|) := by
        rw [← hN, ← Real.exp_log (show (0 : ℝ) < 1 / 4 by norm_num), ← Real.exp_nat_mul]
        congr 2
        rw [one_div, Real.log_inv]; ring

/-- The moments (2.6.1): `|X|^p_{δ₀}(t) = ∑ₙ |n|^p |⟨δₙ, e^{-itH} δ₀⟩|²`. -/
def schrMoment (V : ℤ → ℝ) (p t : ℝ) : ℝ :=
  ∑' n : ℤ, |(n : ℝ)| ^ p * ‖⟪dlt n, propagator V t (dlt 0)⟫_ℂ‖ ^ 2

lemma summable_rpow_mul_exp_neg {p c : ℝ} (hp : 0 < p) (hc : 0 < c) :
    Summable fun n : ℤ => |(n : ℝ)| ^ p * Real.exp (-c * |(n : ℝ)|) := by
  set k := ⌈p⌉₊
  have hnat : Summable fun n : ℕ => (n : ℝ) ^ p * Real.exp (-c * n) := by
    refine (Real.summable_pow_mul_exp_neg_nat_mul k hc).of_nonneg_of_le
      (fun n => by positivity) fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [Real.zero_rpow hp.ne']
    · gcongr
      have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      calc (n : ℝ) ^ p ≤ (n : ℝ) ^ (k : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 (Nat.le_ceil p)
        _ = (n : ℝ) ^ k := Real.rpow_natCast _ _
  refine summable_int_iff_summable_nat_and_neg.mpr ⟨hnat.congr fun n => ?_, hnat.congr fun n => ?_⟩
  · simp
  · simp

/-- **Theorem 2.6.2**, (2.6.8) (ballistic upper bound): for every `p > 0` there is `C` such
that for all `t ≥ 0` the series defining `|X|^p_{δ₀}(t)` converges and
`|X|^p_{δ₀}(t) ≤ C (t^p + 1)`. -/
theorem ballistic_bound (hV : BddPot V) {p : ℝ} (hp : 0 < p) :
    ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t →
      Summable (fun n : ℤ => |(n : ℝ)| ^ p * ‖⟪dlt n, propagator V t (dlt 0)⟫_ℂ‖ ^ 2) ∧
        schrMoment V p t ≤ C * (t ^ p + 1) := by
  set ν₀ := 2 * Real.exp 1 * ‖schr V‖
  have hν₀ : 0 ≤ ν₀ := by positivity
  have hlog : 0 < Real.log 4 := Real.log_pos (by norm_num)
  set e : ℤ → ℝ := fun n => |(n : ℝ)| ^ p * (4 * Real.exp (-(Real.log 4) * |(n : ℝ)|))
  have he : Summable e := by
    have := (summable_rpow_mul_exp_neg hp hlog).mul_left 4
    refine this.congr fun n => ?_
    simp only [e]; ring
  set K := ∑' n, e n
  have hK : 0 ≤ K := tsum_nonneg fun n => by positivity
  refine ⟨ν₀ ^ p + K, fun t ht => ?_⟩
  set ψ := propagator V t (dlt 0)
  set a : ℤ → ℝ := fun n => ‖⟪dlt n, ψ⟫_ℂ‖ ^ 2
  have ha : Summable a := by
    simp only [a, inner_dlt]; exact summable_norm_sq ψ
  have hasum : ∑' n, a n = 1 := by
    simp only [a, inner_dlt]
    rw [← norm_sq_eq_tsum, norm_propagator_apply hV, norm_dlt]; norm_num
  have hbound : ∀ n : ℤ, |(n : ℝ)| ^ p * a n ≤ (ν₀ * t) ^ p * a n + e n := by
    intro n
    have ha0 : 0 ≤ a n := by positivity
    have he0 : 0 ≤ e n := by positivity
    rcases le_or_gt |(n : ℝ)| (ν₀ * t) with h | h
    · have : |(n : ℝ)| ^ p ≤ (ν₀ * t) ^ p := Real.rpow_le_rpow (abs_nonneg _) h hp.le
      nlinarith
    · have hs := spreading_bound hV ht (n := n) (by simp only [ν₀] at h; linarith)
      have h1 : |(n : ℝ)| ^ p * a n ≤ e n := by
        simp only [e, a]
        exact mul_le_mul_of_nonneg_left hs (by positivity)
      have h2 : 0 ≤ (ν₀ * t) ^ p * a n := by positivity
      linarith
  have hg : Summable fun n => (ν₀ * t) ^ p * a n + e n := (ha.mul_left _).add he
  have hf : Summable fun n : ℤ => |(n : ℝ)| ^ p * a n :=
    hg.of_nonneg_of_le (fun n => by positivity) hbound
  refine ⟨hf, ?_⟩
  calc schrMoment V p t = ∑' n : ℤ, |(n : ℝ)| ^ p * a n := rfl
    _ ≤ ∑' n : ℤ, ((ν₀ * t) ^ p * a n + e n) := hf.tsum_le_tsum hbound hg
    _ = (ν₀ * t) ^ p * 1 + K := by
        rw [(ha.mul_left _).tsum_add he, tsum_mul_left, hasum]
    _ = ν₀ ^ p * t ^ p + K := by rw [Real.mul_rpow hν₀ ht, mul_one]
    _ ≤ (ν₀ ^ p + K) * (t ^ p + 1) := by
        have h1 : 0 ≤ ν₀ ^ p := by positivity
        have h2 : 0 ≤ t ^ p := by positivity
        nlinarith

/-- The time average (2.6.2): `⟨f⟩(T) = (2/T) ∫₀^∞ e^{-2t/T} f(t) dt`. -/
def expTimeAvg (f : ℝ → ℝ) (T : ℝ) : ℝ :=
  2 / T * ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(2 / T * t)) * f t

/-- **Theorem 2.6.2**, (2.6.9): the time-averaged ballistic bound
`⟨|X|^p_{δ₀}⟩(T) ≤ C (T^p + 1)` for all `T > 0`. -/
theorem ballistic_bound_avg (hV : BddPot V) {p : ℝ} (hp : 0 < p) :
    ∃ C : ℝ, ∀ T : ℝ, 0 < T → expTimeAvg (schrMoment V p) T ≤ C * (T ^ p + 1) := by
  obtain ⟨C0, hC0⟩ := ballistic_bound hV hp
  have hmom0 : ∀ t, 0 ≤ schrMoment V p t := fun t =>
    tsum_nonneg fun n => by positivity
  have hC0nn : 0 ≤ C0 := by
    have := (hC0 0 le_rfl).2
    rw [Real.zero_rpow hp.ne', zero_add, mul_one] at this
    exact (hmom0 0).trans this
  refine ⟨C0 * (Real.Gamma (p + 1) + 1), fun T hT => ?_⟩
  set r := 2 / T
  have hr : 0 < r := by positivity
  have hG : 0 < Real.Gamma (p + 1) := Real.Gamma_pos_of_pos (by linarith)
  -- the majorant
  have hi1 : MeasureTheory.IntegrableOn (fun t : ℝ => t ^ p * Real.exp (-(r * t)))
      (Set.Ioi 0) := by
    have := integrableOn_rpow_mul_exp_neg_mul_rpow (s := p) (p := 1) (b := r)
      (by linarith) one_pos hr
    refine this.congr_fun (fun t ht => ?_) measurableSet_Ioi
    simp [Real.rpow_one, neg_mul]
  have hi2 : MeasureTheory.IntegrableOn (fun t : ℝ => Real.exp (-(r * t))) (Set.Ioi 0) := by
    have := integrableOn_exp_mul_Ioi (a := -r) (by linarith) 0
    refine this.congr_fun (fun t _ => by ring_nf) measurableSet_Ioi
  have hint1 : ∫ t in Set.Ioi (0 : ℝ), t ^ p * Real.exp (-(r * t)) =
      (1 / r) ^ (p + 1) * Real.Gamma (p + 1) := by
    have := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := p + 1) (by linarith) hr
    rw [show p + 1 - 1 = p by ring] at this
    exact this
  have hint2 : ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(r * t)) = 1 / r := by
    have := integral_exp_mul_Ioi (a := -r) (by linarith) 0
    simp only [mul_zero, Real.exp_zero] at this
    rw [show (fun t : ℝ => Real.exp (-(r * t))) = fun t => Real.exp (-r * t) by
      funext t; ring_nf, this]
    field_simp
  set g : ℝ → ℝ := fun t => C0 * (t ^ p * Real.exp (-(r * t))) + C0 * Real.exp (-(r * t))
  have hg : MeasureTheory.IntegrableOn g (Set.Ioi 0) :=
    (hi1.const_mul C0).add (hi2.const_mul C0)
  have hle : ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(r * t)) * schrMoment V p t ≤
      ∫ t in Set.Ioi (0 : ℝ), g t := by
    refine MeasureTheory.integral_mono_of_nonneg ?_ hg ?_
    · exact Filter.Eventually.of_forall fun t => mul_nonneg (Real.exp_pos _).le (hmom0 t)
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
      have := (hC0 t (le_of_lt ht)).2
      simp only [g]
      nlinarith [Real.exp_pos (-(r * t))]
  have hgint : ∫ t in Set.Ioi (0 : ℝ), g t =
      C0 * ((1 / r) ^ (p + 1) * Real.Gamma (p + 1)) + C0 * (1 / r) := by
    simp only [g]
    rw [MeasureTheory.integral_add (hi1.const_mul C0) (hi2.const_mul C0),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, hint1, hint2]
  have hTp : (T / 2) ^ p ≤ T ^ p := by
    apply Real.rpow_le_rpow (by positivity) (by linarith) hp.le
  have h1r : 1 / r = T / 2 := by simp [r]
  unfold expTimeAvg
  calc 2 / T * ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(2 / T * t)) * schrMoment V p t
      ≤ 2 / T * (C0 * ((1 / r) ^ (p + 1) * Real.Gamma (p + 1)) + C0 * (1 / r)) := by
        rw [← hgint]; exact mul_le_mul_of_nonneg_left hle (by positivity)
    _ = C0 * (Real.Gamma (p + 1) * (T / 2) ^ p + 1) := by
        rw [h1r, Real.rpow_add (by positivity), Real.rpow_one]
        field_simp
    _ ≤ C0 * (Real.Gamma (p + 1) * T ^ p + 1) := by gcongr
    _ ≤ C0 * (Real.Gamma (p + 1) + 1) * (T ^ p + 1) := by
        have h0 : 0 ≤ T ^ p := by positivity
        nlinarith [mul_nonneg hC0nn h0, mul_nonneg hC0nn hG.le]

lemma norm_schr_pos (hV : BddPot V) : 0 < ‖schr V‖ := by
  have h1 : (schr V (dlt 0)) 1 = 1 := by
    rw [schr_apply hV]; simp [dlt_apply]
  have h2 : ‖(schr V (dlt 0)) 1‖ ≤ ‖schr V‖ := by
    calc ‖(schr V (dlt 0)) 1‖ ≤ ‖schr V (dlt 0)‖ := lp.norm_apply_le_norm (by norm_num) _ 1
      _ ≤ ‖schr V‖ * ‖dlt 0‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖schr V‖ := by rw [norm_dlt, mul_one]
  rw [h1, norm_one] at h2
  linarith

/-- **Theorem 2.6.1**, (2.6.4): for `ε > 0`, `T > 0` and `|n| ≥ (ν₀ T)^{1+ε}`,
`(2/T) ∫₀^∞ e^{-2t/T} |⟨δₙ, e^{-itH} δ₀⟩|² dt ≤ 5 e^{-(log 4) |n|^γ}`, `γ = ε/(1+ε)`
(the book: `C = 17`). -/
theorem spreading_bound_avg (hV : BddPot V) {ε : ℝ} (hε : 0 < ε) {T : ℝ} (hT : 0 < T)
    {n : ℤ} (hn : (2 * Real.exp 1 * ‖schr V‖ * T) ^ (1 + ε) ≤ |(n : ℝ)|) :
    expTimeAvg (fun t => ‖⟪dlt n, propagator V t (dlt 0)⟫_ℂ‖ ^ 2) T ≤
      5 * Real.exp (-(Real.log 4) * |(n : ℝ)| ^ (ε / (1 + ε))) := by
  set ν₀ := 2 * Real.exp 1 * ‖schr V‖
  have hν : 0 < ν₀ := by have := norm_schr_pos hV; positivity
  set a := |(n : ℝ)|
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity) hn
  set r := 2 / T
  have hr : 0 < r := by positivity
  set c := Real.log 4
  have hc : 0 < c := Real.log_pos (by norm_num)
  have hc2 : c ≤ 2 := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_lt_d9
    simp only [c]; rw [h4]; linarith
  set t₀ := a / ν₀
  have ht₀ : 0 < t₀ := by positivity
  -- pointwise majorant
  set h : ℝ → ℝ := fun t => 4 * Real.exp (-c * a) * Real.exp (-(r * t)) +
    (Set.Ioi t₀).indicator (fun t => Real.exp (-(r * t))) t
  have hpt : ∀ t, 0 < t → Real.exp (-(r * t)) * ‖⟪dlt n, propagator V t (dlt 0)⟫_ℂ‖ ^ 2 ≤ h t := by
    intro t ht
    have he := Real.exp_pos (-(r * t))
    by_cases htt : t ≤ t₀
    · have hsb := spreading_bound hV ht.le (n := n) (by
        have : ν₀ * t ≤ a := by
          calc ν₀ * t ≤ ν₀ * t₀ := by gcongr
            _ = a := by simp only [t₀]; field_simp
        simpa [ν₀, mul_comm] using this)
      have hind : 0 ≤ (Set.Ioi t₀).indicator (fun t => Real.exp (-(r * t))) t :=
        Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) t
      simp only [h, neg_mul] at hsb ⊢
      nlinarith
    · have hle1 : ‖⟪dlt n, propagator V t (dlt 0)⟫_ℂ‖ ^ 2 ≤ 1 := by
        rw [inner_dlt]
        have := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0)
          (propagator V t (dlt 0)) n
        rw [norm_propagator_apply hV, norm_dlt] at this
        nlinarith [norm_nonneg ((propagator V t (dlt 0)) n)]
      have hind : (Set.Ioi t₀).indicator (fun t => Real.exp (-(r * t))) t =
          Real.exp (-(r * t)) := Set.indicator_of_mem (by simpa using lt_of_not_ge htt) _
      simp only [h, hind]
      nlinarith [Real.exp_pos (-c * a)]
  -- integrals
  have hi2 : MeasureTheory.IntegrableOn (fun t : ℝ => Real.exp (-(r * t))) (Set.Ioi 0) := by
    have := integrableOn_exp_mul_Ioi (a := -r) (by linarith) 0
    refine this.congr_fun (fun t _ => by ring_nf) measurableSet_Ioi
  have hint2 : ∀ x : ℝ, ∫ t in Set.Ioi x, Real.exp (-(r * t)) = Real.exp (-(r * x)) / r := by
    intro x
    have := integral_exp_mul_Ioi (a := -r) (by linarith) x
    rw [show (fun t : ℝ => Real.exp (-(r * t))) = fun t => Real.exp (-r * t) by
      funext t; ring_nf, this]
    rw [neg_mul, neg_div_neg_eq]
  have hint3 : MeasureTheory.IntegrableOn
      ((Set.Ioi t₀).indicator (fun t => Real.exp (-(r * t)))) (Set.Ioi 0) :=
    hi2.indicator measurableSet_Ioi
  have hhint : MeasureTheory.IntegrableOn h (Set.Ioi 0) :=
    (hi2.const_mul (4 * Real.exp (-c * a))).add hint3
  have hhval : ∫ t in Set.Ioi (0 : ℝ), h t =
      4 * Real.exp (-c * a) * (1 / r) + Real.exp (-(r * t₀)) / r := by
    simp only [h]
    rw [MeasureTheory.integral_add (hi2.const_mul _) hint3, MeasureTheory.integral_const_mul,
      hint2 0, MeasureTheory.setIntegral_indicator measurableSet_Ioi,
      show Set.Ioi (0 : ℝ) ∩ Set.Ioi t₀ = Set.Ioi t₀ from
        Set.inter_eq_right.mpr (Set.Ioi_subset_Ioi ht₀.le), hint2 t₀]
    simp
  have hle : ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(2 / T * t)) *
      ‖⟪dlt n, propagator V t (dlt 0)⟫_ℂ‖ ^ 2 ≤ ∫ t in Set.Ioi (0 : ℝ), h t := by
    refine MeasureTheory.integral_mono_of_nonneg ?_ hhint ?_
    · exact Filter.Eventually.of_forall fun t => by positivity
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
      exact hpt t ht
  -- the exponent
  set γ := ε / (1 + ε)
  have hγ1 : γ ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have ha1 : 1 ≤ a := by
    have hn0 : n ≠ 0 := by
      intro h0
      have : a = 0 := by simp [a, h0]
      linarith
    have : (1 : ℝ) ≤ |(n : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hn0
    exact this
  have haγ : a ^ γ ≤ a := by
    calc a ^ γ ≤ a ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le ha1 hγ1
      _ = a := Real.rpow_one a
  have hkey : a ^ γ ≤ a / (ν₀ * T) := by
    have h1 : ν₀ * T ≤ a ^ (1 / (1 + ε)) := by
      have := Real.rpow_le_rpow (by positivity) hn (show (0 : ℝ) ≤ 1 / (1 + ε) by positivity)
      rwa [← Real.rpow_mul (by positivity), mul_one_div_cancel (by linarith), Real.rpow_one]
        at this
    rw [le_div_iff₀ (by positivity)]
    calc a ^ γ * (ν₀ * T) ≤ a ^ γ * a ^ (1 / (1 + ε)) := by gcongr
      _ = a := by
        rw [← Real.rpow_add ha0, show γ + 1 / (1 + ε) = 1 by
          simp only [γ]; field_simp; ring, Real.rpow_one]
  have hrt : 2 * a ^ γ ≤ r * t₀ := by
    simp only [r, t₀]
    rw [show 2 / T * (a / ν₀) = 2 * (a / (ν₀ * T)) by field_simp]
    linarith
  unfold expTimeAvg
  calc 2 / T * ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(2 / T * t)) *
        ‖⟪dlt n, propagator V t (dlt 0)⟫_ℂ‖ ^ 2
      ≤ r * (4 * Real.exp (-c * a) * (1 / r) + Real.exp (-(r * t₀)) / r) := by
        rw [← hhval]; exact mul_le_mul_of_nonneg_left hle hr.le
    _ = 4 * Real.exp (-c * a) + Real.exp (-(r * t₀)) := by field_simp
    _ ≤ 4 * Real.exp (-c * a ^ γ) + Real.exp (-c * a ^ γ) := by
        have e1 : Real.exp (-c * a) ≤ Real.exp (-c * a ^ γ) :=
          Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left haγ hc.le])
        have e2 : Real.exp (-(r * t₀)) ≤ Real.exp (-c * a ^ γ) :=
          Real.exp_le_exp.mpr (by
            nlinarith [mul_le_mul_of_nonneg_right hc2 (Real.rpow_nonneg ha0.le γ)])
        linarith
    _ = 5 * Real.exp (-c * a ^ γ) := by ring

end DF
