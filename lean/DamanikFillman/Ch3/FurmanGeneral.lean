/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# §3.5.2: Furman's theorem in full generality (Theorem 3.5.8)

Main result:
* `DF.furmanStatement` — **Theorem 3.5.8**: the Statement `DF.FurmanStatement`, without the
  bound `|f_n| ≤ C n` assumed in `DF.furman`.

Proof: subadditivity gives `f_n ≤ n ‖f_1‖_∞`. Pick `k₀` with `(1/k₀) ∫ f_{k₀} < λ + ε/2` and
truncate from below, `g_n = max(f_n, -C n)` with `C ≥ ‖f_{k₀}‖_∞`: the `g_n` are continuous,
subadditive and satisfy `|g_n| ≤ C' n`, `g_{k₀} = f_{k₀}` and `f_n ≤ g_n`, so `DF.furman` applied
to `(g_n)` gives the claim. (If `n ↦ (1/n) ∫ f_n` is unbounded below, the infimum is `0` by
convention, and the same argument applies with any `k₀` for which `(1/k₀) ∫ f_{k₀} < ε/2`.)
-/
import DamanikFillman.Ch3.Furman

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Filter Set Function Topology

namespace DF

/-- **Theorem 3.5.8** (Furman), general case. -/
theorem furmanStatement : FurmanStatement := by
  intro X _ _ _ _ S μ hS hμ f hsub ε hε
  obtain ⟨-, hprob⟩ := UniquelyErgodic.ergodic hμ
  set lamF := ⨅ k : ℕ, (∫ y, f (k + 1) y ∂μ) / (k + 1) with hlamF
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℕ, (∫ y, f (k₀ + 1) y ∂μ) / (k₀ + 1) < lamF + ε / 2 := by
    by_cases hb : BddBelow (range fun k : ℕ => (∫ y, f (k + 1) y ∂μ) / (k + 1))
    · exact exists_lt_of_ciInf_lt (lt_add_of_pos_right _ (half_pos hε))
    · rw [not_bddBelow_iff] at hb
      obtain ⟨_, ⟨k, rfl⟩, hk⟩ := hb (lamF + ε / 2)
      exact ⟨k, hk⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = ‖f 1‖ := ⟨_, rfl⟩
  set C := max ‖f (k₀ + 1)‖ (max B 1) with hC
  have hC0 : 0 ≤ C := le_trans zero_le_one (le_trans (le_max_right _ _) (le_max_right _ _))
  have hBC : B ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  have hnorm : ∀ (h : C(X, ℝ)) x, |h x| ≤ ‖h‖ := fun h x =>
    (Real.norm_eq_abs _).symm.trans_le (h.norm_coe_le_norm x)
  have hf1 : ∀ x, f 1 x ≤ B := fun x => by
    rw [hB]; exact (le_abs_self _).trans (hnorm (f 1) x)
  -- `f_n ≤ n B`
  have hup' : ∀ n : ℕ, ∀ x, f (n + 1) x ≤ ((n : ℝ) + 1) * B := by
    intro n
    induction n with
    | zero => intro x; simpa using hf1 x
    | succ n ih =>
      intro x
      have h1 := hsub (n + 1) 1 x (by omega) le_rfl
      have h2 := ih x
      have h3 := hf1 ((S)^[n + 1] x)
      push_cast
      linarith
  have hup : ∀ n x, 1 ≤ n → f n x ≤ n * B := by
    intro n x hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have := hup' m x
    push_cast
    linarith
  -- the truncation
  let g : ℕ → C(X, ℝ) := fun n =>
    ⟨fun x => max (f n x) (-(C * n)), (f n).continuous.max continuous_const⟩
  have hg : ∀ n x, g n x = max (f n x) (-(C * n)) := fun n x => rfl
  have hsubg : ∀ n m x, 1 ≤ n → 1 ≤ m → g (n + m) x ≤ g n x + g m (S^[n] x) := by
    intro n m x hn hm
    rw [hg, hg, hg]
    refine max_le ((hsub n m x hn hm).trans (add_le_add (le_max_left _ _) (le_max_left _ _))) ?_
    have e : C * ((n + m : ℕ) : ℝ) = C * n + C * m := by push_cast; ring
    rw [e]
    linarith [le_max_right (f n x) (-(C * n)), le_max_right (f m (S^[n] x)) (-(C * m))]
  have hgb : ∀ n x, 1 ≤ n → |g n x| ≤ C * n := by
    intro n x hn
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    rw [abs_le, hg]
    constructor
    · exact le_max_right _ _
    · refine max_le ?_ ?_
      · have := hup n x hn
        have : (n : ℝ) * B ≤ C * n := by rw [mul_comm]; exact mul_le_mul_of_nonneg_right hBC hn0
        linarith
      · have : 0 ≤ C * n := mul_nonneg hC0 hn0
        linarith
  obtain ⟨N, hN⟩ := furman hS hμ hsubg hgb (ε / 2) (half_pos hε)
  -- `g_{k₀+1} = f_{k₀+1}`
  have hgk : ∀ x, g (k₀ + 1) x = f (k₀ + 1) x := by
    intro x
    rw [hg]
    apply max_eq_left
    have h1 := hnorm (f (k₀ + 1)) x
    have h2 : ‖f (k₀ + 1)‖ ≤ C := le_max_left _ _
    have h3 : C ≤ C * ((k₀ + 1 : ℕ) : ℝ) :=
      le_mul_of_one_le_right hC0 (by push_cast; linarith [(Nat.cast_nonneg k₀ : (0 : ℝ) ≤ k₀)])
    have := neg_abs_le (f (k₀ + 1) x)
    linarith
  have hbdd : BddBelow (range fun k : ℕ => (∫ y, g (k + 1) y ∂μ) / (k + 1)) := by
    refine ⟨-C, ?_⟩
    rintro _ ⟨k, rfl⟩
    have hk : (0 : ℝ) < k + 1 := by positivity
    rw [le_div_iff₀ hk]
    have hgi : Integrable (g (k + 1)) μ :=
      (g (k + 1)).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have : ∫ _y, -(C * ((k : ℝ) + 1)) ∂μ ≤ ∫ y, g (k + 1) y ∂μ := by
      refine integral_mono (integrable_const _) hgi fun y => ?_
      have := (abs_le.1 (hgb (k + 1) y (by omega))).1
      push_cast at this
      linarith
    simp only [integral_const, measureReal_univ_eq_one, one_smul] at this
    rw [neg_mul]
    exact this
  have hlamg : (⨅ k : ℕ, (∫ y, g (k + 1) y ∂μ) / (k + 1)) ≤
      (∫ y, f (k₀ + 1) y ∂μ) / (k₀ + 1) := by
    refine (ciInf_le hbdd k₀).trans_eq ?_
    simp only [hgk]
  refine ⟨max N 1, fun n hn x => ?_⟩
  have h1 := hN n (le_trans (le_max_left _ _) hn) x
  have hn1 : (0 : ℝ) < n := by
    have : 1 ≤ n := le_trans (le_max_right _ _) hn
    exact_mod_cast this
  have h2 : f n x / n ≤ g n x / n := div_le_div_of_nonneg_right (le_max_left _ _) hn1.le
  linarith

end DF
