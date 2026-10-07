/-
# Uniform exponential growth bound  (paper Lemma 2.5, `lem:finite-block-growth`)

For a continuous `1`-periodic `SL(2,ℂ)` cocycle over an irrational rotation,
`L(α, A) < γ` implies `sup_x ‖A_n(x)‖ ≤ C e^{γ n}` for all `n`.
The paper invokes Furman's uniform subadditive theorem; for irrational rotations we prove it
from Weyl's uniform equidistribution (`Equidistribution.lean`) and a block decomposition with
blocks of a fixed length `N` for which `(1/N) ∫ log ‖A_N‖ < L + ε`.
Everything here is proved (single cocycle; the paper's compact-family version follows by the
finite-cover argument given there).
-/
import AnalyticPerturbationsAMO.Equidistribution
import AnalyticPerturbationsAMO.Cocycle

noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology Finset

namespace AMO

variable {α : ℝ} {A : ℝ → M2}

namespace IsSLCocycle

variable (hA : IsSLCocycle A)
include hA

/-- `log ‖A‖` is bounded above. -/
lemma exists_log_norm_bound : ∃ M₀ : ℝ, 0 ≤ M₀ ∧ ∀ x, Real.log ‖A x‖ ≤ M₀ := by
  have hc : Continuous fun x => Real.log ‖A x‖ :=
    hA.continuous.norm.log (fun x => (zero_lt_one.trans_le
      (one_le_norm_of_det_eq_one (hA.det_eq_one x))).ne')
  obtain ⟨y, -, hy⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_isMaxOn
    (Set.nonempty_Icc.2 zero_le_one) hc.continuousOn
  refine ⟨max (Real.log ‖A y‖) 0, le_max_right _ _, fun x => ?_⟩
  have hp : Function.Periodic (fun x => Real.log ‖A x‖) 1 := fun x => by
    simp only [hA.periodic x]
  obtain ⟨z, hz, hxz⟩ := hp.exists_mem_Ico₀ one_pos x
  rw [hxz]
  exact (hy ⟨hz.1, hz.2.le⟩).trans (le_max_left _ _)

lemma log_norm_iter_le {M₀ : ℝ} (hM : ∀ x, Real.log ‖A x‖ ≤ M₀) (n : ℕ) (x : ℝ) :
    Real.log ‖iter α A n x‖ ≤ n * M₀ := by
  induction n generalizing x with
  | zero => simp [iter]
  | succ n ih =>
    have h1 := hA.one_le_norm_iter (α := α) n x
    have h2 := one_le_norm_of_det_eq_one (hA.det_eq_one (x + n * α))
    have h3 := hA.one_le_norm_iter (α := α) (n + 1) x
    rw [iter] at h3 ⊢
    calc Real.log ‖A (x + n * α) * iter α A n x‖
        ≤ Real.log (‖A (x + n * α)‖ * ‖iter α A n x‖) :=
          Real.log_le_log (by linarith) (norm_mul_le _ _)
      _ = Real.log ‖A (x + n * α)‖ + Real.log ‖iter α A n x‖ :=
          Real.log_mul (by positivity) (by positivity)
      _ ≤ M₀ + n * M₀ := add_le_add (hM _) (ih x)
      _ = ((n + 1 : ℕ) : ℝ) * M₀ := by push_cast; ring

lemma log_norm_iter_add_le (m n : ℕ) (x : ℝ) :
    Real.log ‖iter α A (n + m) x‖ ≤
      Real.log ‖iter α A m (x + n * α)‖ + Real.log ‖iter α A n x‖ := by
  have h1 := hA.one_le_norm_iter (α := α) m (x + n * α)
  have h2 := hA.one_le_norm_iter (α := α) n x
  have h3 := hA.one_le_norm_iter (α := α) (n + m) x
  rw [iter_add] at h3 ⊢
  rw [← Real.log_mul (by positivity) (by positivity)]
  exact Real.log_le_log (by linarith) (norm_mul_le _ _)

/-- Block decomposition: `log ‖A_{mN}(x)‖ ≤ ∑_{j<m} log ‖A_N(x + jNα)‖`. -/
lemma log_norm_iter_blocks (N m : ℕ) (x : ℝ) :
    Real.log ‖iter α A (m * N) x‖ ≤
      ∑ j ∈ range m, Real.log ‖iter α A N (x + j * (N * α))‖ := by
  induction m with
  | zero => simp [iter]
  | succ m ih =>
    rw [sum_range_succ, show (m + 1) * N = m * N + N by ring]
    refine (hA.log_norm_iter_add_le N (m * N) x).trans ?_
    rw [add_comm]
    refine add_le_add ih (le_of_eq ?_)
    congr 3
    push_cast
    ring

/-- **Uniform growth bound** (Lemma 2.5 for a single cocycle): if `L(α, A) < γ` then
`‖A_n(x)‖ ≤ C e^{γ n}` for all `n` and `x`. -/
theorem uniform_growth (hα : Irrational α) {γ : ℝ} (hγ : lyapunov α A < γ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (x : ℝ), ‖iter α A n x‖ ≤ C * Real.exp (γ * n) := by
  obtain ⟨M₀, hM₀, hM⟩ := hA.exists_log_norm_bound
  set L := lyapunov α A
  have hL0 : 0 ≤ L := hA.lyapunov_nonneg
  set ε := (γ - L) / 4 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  -- a block length `N ≥ 1` with `(1/N) ∫ log ‖A_N‖ < L + ε`
  obtain ⟨N, hN1, hN⟩ : ∃ N : ℕ, 1 ≤ N ∧ lyapSeq α A N / N < L + ε := by
    have h := (hA.tendsto_lyapunov (α := α)).eventually (gt_mem_nhds (by linarith : L < L + ε))
    obtain ⟨N, hN⟩ := (h.and (eventually_ge_atTop 1)).exists
    exact ⟨N, hN.2, hN.1⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  -- Weyl's theorem for the block function along the rotation by `Nα`
  have hg : Continuous fun x => Real.log ‖iter α A N x‖ := hA.continuous_log_norm_iter N
  have hgp : Function.Periodic (fun x => Real.log ‖iter α A N x‖) 1 := fun x => by
    simp only [iter_periodic (α := α) hA.periodic N x]
  have hβ : Irrational (N * α) := hα.natCast_mul (by omega)
  obtain ⟨m₀, hm₀⟩ := weyl_uniform_real hβ hg hgp (by positivity : 0 < N * ε)
  have hint : ∫ y in (0 : ℝ)..1, Real.log ‖iter α A N y‖ = lyapSeq α A N := rfl
  have hlyN : lyapSeq α A N < N * (L + ε) := by
    rwa [div_lt_iff₀ hNpos, mul_comm] at hN
  set K : ℝ := N * M₀ * (m₀ + 1) + N * M₀
  refine ⟨Real.exp K, Real.exp_pos _, fun n x => ?_⟩
  have hn1 := hA.one_le_norm_iter (α := α) n x
  rw [← Real.exp_log (zero_lt_one.trans_le hn1), ← Real.exp_add]
  apply Real.exp_le_exp.2
  have hγ0 : 0 ≤ γ := hL0.trans hγ.le
  -- write `n = m N + r`
  obtain ⟨m, r, hnmr, hr⟩ : ∃ m r : ℕ, n = m * N + r ∧ r < N :=
    ⟨n / N, n % N, (Nat.div_add_mod' n N).symm, Nat.mod_lt _ (by omega)⟩
  subst hnmr
  have hsplit : Real.log ‖iter α A (m * N + r) x‖ ≤
      r * M₀ + ∑ j ∈ range m, Real.log ‖iter α A N (x + j * (N * α))‖ := by
    have h1 := hA.log_norm_iter_add_le (α := α) r (m * N) x
    have h2 := hA.log_norm_iter_blocks (α := α) N m x
    have h3 := hA.log_norm_iter_le (α := α) hM r (x + ((m * N : ℕ) : ℝ) * α)
    linarith
  have hrM : (r : ℝ) * M₀ ≤ N * M₀ := by
    gcongr
  have hnge : (m : ℝ) * N ≤ ((m * N + r : ℕ) : ℝ) := by
    push_cast; linarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)]
  by_cases hm : m₀ ≤ m
  · -- many blocks: Weyl
    have hw := hm₀ m hm x
    have hsum : ∑ j ∈ range m, Real.log ‖iter α A N (x + j * (N * α))‖ ≤ m * (lyapSeq α A N + N * ε) := by
      rcases Nat.eq_zero_or_pos m with h0 | hmpos
      · subst h0; simp
      have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
      have h1 : (m : ℝ)⁻¹ * ∑ j ∈ range m, Real.log ‖iter α A N (x + j * (N * α))‖ ≤ lyapSeq α A N + N * ε := by
        have := (abs_le.1 hw).2
        rw [hint] at this
        linarith
      rwa [inv_mul_le_iff₀ hmR] at h1
    have hlb : 0 ≤ lyapSeq α A N + N * ε := by
      have := hA.lyapSeq_nonneg (α := α) N
      positivity
    have hmN : (m : ℝ) * (lyapSeq α A N + N * ε) ≤ ((m * N + r : ℕ) : ℝ) * (L + 2 * ε) := by
      calc (m : ℝ) * (lyapSeq α A N + N * ε) ≤ m * (N * (L + ε) + N * ε) := by
            gcongr
        _ = (m * N) * (L + 2 * ε) := by ring
        _ ≤ ((m * N + r : ℕ) : ℝ) * (L + 2 * ε) := by
            gcongr
    have hK : N * M₀ ≤ K := by
      have : 0 ≤ (N : ℝ) * M₀ * (m₀ + 1) := by positivity
      linarith
    have hγn : ((m * N + r : ℕ) : ℝ) * (L + 2 * ε) ≤ γ * ((m * N + r : ℕ) : ℝ) := by
      rw [mul_comm γ]
      gcongr
      linarith
    linarith
  · -- few blocks: crude bound
    push_neg at hm
    have hnb : ((m * N + r : ℕ) : ℝ) < (m₀ + 1) * N := by
      have h1 : (m : ℝ) + 1 ≤ m₀ := by exact_mod_cast hm
      push_cast
      have : (r : ℝ) < N := by exact_mod_cast hr
      nlinarith
    have hcrude := hA.log_norm_iter_le (α := α) hM (m * N + r) x
    have h2 : ((m * N + r : ℕ) : ℝ) * M₀ ≤ N * M₀ * (m₀ + 1) := by
      have : ((m * N + r : ℕ) : ℝ) * M₀ ≤ ((m₀ + 1) * N) * M₀ := by gcongr
      linarith
    have hγn : 0 ≤ γ * ((m * N + r : ℕ) : ℝ) := by positivity
    have : 0 ≤ (N : ℝ) * M₀ := by positivity
    linarith

end IsSLCocycle

/-! ### Compact families and nearby frequencies -/

section Family

variable {P : Type*} [TopologicalSpace P] [CompactSpace P] (A : P → ℝ → M2)

lemma continuous_iter_family (hcont : Continuous fun z : P × ℝ => A z.1 z.2) (n : ℕ) :
    Continuous fun z : ℝ × P × ℝ => iter z.1 (A z.2.1) n z.2.2 := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    change Continuous fun z : ℝ × P × ℝ => A z.2.1 (z.2.2 + n * z.1) * iter z.1 (A z.2.1) n z.2.2
    refine Continuous.mul ?_ ih
    exact hcont.comp (Continuous.prodMk (continuous_fst.comp continuous_snd)
      ((continuous_snd.comp continuous_snd).add (continuous_const.mul continuous_fst)))

lemma exists_norm_bound_family (hcont : Continuous fun z : P × ℝ => A z.1 z.2)
    (hper : ∀ p, Function.Periodic (A p) 1) : ∃ M : ℝ, 1 ≤ M ∧ ∀ p x, ‖A p x‖ ≤ M := by
  have hK : IsCompact (Set.univ ×ˢ Set.Icc (0 : ℝ) 1 : Set (P × ℝ)) :=
    isCompact_univ.prod isCompact_Icc
  obtain ⟨B, hB⟩ := (hK.image (continuous_norm.comp hcont)).isBounded.subset_closedBall 0
  refine ⟨max B 1, le_max_right _ _, fun p x => ?_⟩
  obtain ⟨y, hy, hxy⟩ := (hper p).exists_mem_Ico₀ one_pos x
  rw [hxy]
  have := hB ⟨(p, y), ⟨Set.mem_univ _, hy.1, hy.2.le⟩, rfl⟩
  simp only [Metric.mem_closedBall, dist_zero_right, Function.comp_apply, norm_norm] at this
  exact this.trans (le_max_left _ _)

lemma norm_iter_le_pow {B : ℝ → M2} {M : ℝ} (hM1 : 1 ≤ M) (hM : ∀ x, ‖B x‖ ≤ M) (β : ℝ)
    (n : ℕ) (x : ℝ) : ‖iter β B n x‖ ≤ M ^ n := by
  induction n generalizing x with
  | zero => simp [iter]
  | succ n ih =>
    rw [iter, pow_succ']
    exact (norm_mul_le _ _).trans (mul_le_mul (hM _) (ih x) (norm_nonneg _) (by positivity))

/-- Block bound: a strict bound at one length `m` propagates to all lengths. -/
lemma norm_iter_block_bound {B : ℝ → M2} {M γ β : ℝ} (hM1 : 1 ≤ M) (hM : ∀ x, ‖B x‖ ≤ M)
    (hγ : 0 ≤ γ) {m : ℕ} (hm : 1 ≤ m) (hblock : ∀ x, ‖iter β B m x‖ ≤ Real.exp (γ * m))
    (n : ℕ) (x : ℝ) : ‖iter β B n x‖ ≤ M ^ m * Real.exp (γ * n) := by
  have hk : ∀ k : ℕ, ∀ x, ‖iter β B (k * m) x‖ ≤ Real.exp (γ * (k * m : ℕ)) := by
    intro k
    induction k with
    | zero => intro x; simp [iter]
    | succ k ih =>
      intro x
      rw [show (k + 1) * m = k * m + m by ring, iter_add]
      calc ‖iter β B m (x + ((k * m : ℕ) : ℝ) * β) * iter β B (k * m) x‖
          ≤ Real.exp (γ * m) * Real.exp (γ * (k * m : ℕ)) :=
            (norm_mul_le _ _).trans (mul_le_mul (hblock _) (ih x) (norm_nonneg _)
              (Real.exp_pos _).le)
        _ = Real.exp (γ * ((k * m + m : ℕ) : ℝ)) := by rw [← Real.exp_add]; push_cast; ring_nf
  obtain ⟨k, r, rfl, hr⟩ : ∃ k r : ℕ, n = k * m + r ∧ r < m :=
    ⟨n / m, n % m, (Nat.div_add_mod' n m).symm, Nat.mod_lt _ (by omega)⟩
  rw [iter_add]
  calc ‖iter β B r (x + ((k * m : ℕ) : ℝ) * β) * iter β B (k * m) x‖
      ≤ M ^ r * Real.exp (γ * (k * m : ℕ)) :=
        (norm_mul_le _ _).trans (mul_le_mul (norm_iter_le_pow hM1 hM β r _) (hk k x)
          (norm_nonneg _) (by positivity))
    _ ≤ M ^ m * Real.exp (γ * ((k * m + r : ℕ) : ℝ)) := by
        refine mul_le_mul (pow_le_pow_right₀ hM1 hr.le) (Real.exp_le_exp.2
          (mul_le_mul_of_nonneg_left ?_ hγ)) (Real.exp_pos _).le (by positivity)
        push_cast; linarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)]

/-- **Lemma 2.5 (finite-block growth).**  For a jointly continuous compact family of `SL(2)`
cocycles over an irrational rotation with `sup_p L(α, A_p) < γ`, there are `C` and a
neighbourhood of `α` (containing rational frequencies) on which
`sup_p sup_x ‖A_{p,n}(x)‖ ≤ C e^{γ n}` for all `n`. -/
theorem uniform_growth_family {α γ : ℝ} (hα : Irrational α)
    (hcont : Continuous fun z : P × ℝ => A z.1 z.2) (hcoc : ∀ p, IsSLCocycle (A p))
    (hL : ∀ p, lyapunov α (A p) < γ) :
    ∃ C : ℝ, 0 < C ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ α' : ℝ, |α' - α| < δ →
      ∀ (p : P) (n : ℕ) (x : ℝ), ‖iter α' (A p) n x‖ ≤ C * Real.exp (γ * n) := by
  obtain ⟨M, hM1, hM⟩ := exists_norm_bound_family A hcont (fun p => (hcoc p).periodic)
  -- for each `p`: a length `m p` and an open neighbourhood `U p` of `(α, p)`
  have hloc : ∀ p : P, ∃ m : ℕ, 1 ≤ m ∧ ∃ U : Set (ℝ × P), IsOpen U ∧ (α, p) ∈ U ∧
      ∀ z ∈ U, ∀ x, ‖iter z.1 (A z.2) m x‖ ≤ Real.exp (γ * m) := by
    intro p
    have hLp := hL p
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
    -- the open set where the length-`m` bound is strict
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
  -- finite subcover of `{α} × P`
  have hcover : ({α} : Set ℝ) ×ˢ (Set.univ : Set P) ⊆ ⋃ p, U p := by
    rintro ⟨a, p⟩ ⟨ha, -⟩
    rw [Set.mem_singleton_iff] at ha
    subst ha
    exact Set.mem_iUnion.2 ⟨p, hαU p⟩
  obtain ⟨t, ht⟩ := (isCompact_singleton.prod isCompact_univ).elim_finite_subcover U hUo hcover
  have hO : IsOpen (⋃ p ∈ t, U p) := isOpen_biUnion fun p _ => hUo p
  obtain ⟨u, v, hu, -, hαu, hv, huv⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_univ hO ht
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hu α (hαu rfl)
  set C := 1 + ∑ p ∈ t, M ^ m p
  have hC : 0 < C := by positivity
  refine ⟨C, hC, δ, hδ, fun α' hα' p n x => ?_⟩
  have hmem : (α', p) ∈ ⋃ q ∈ t, U q :=
    huv ⟨hball (by rw [Metric.mem_ball, Real.dist_eq]; exact hα'), hv (Set.mem_univ p)⟩
  obtain ⟨q, hqt, hq⟩ := Set.mem_iUnion₂.1 hmem
  have hγ0 : 0 ≤ γ := ((hcoc p).lyapunov_nonneg (α := α)).trans (hL p).le
  have hb := norm_iter_block_bound hM1 (hM p) hγ0 (hm1 q) (β := α')
    (fun y => hU q (α', p) hq y) n x
  have hle : M ^ m q ≤ C := by
    have := Finset.single_le_sum (f := fun p => M ^ m p) (fun p _ => by positivity) hqt
    linarith
  exact hb.trans (mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le)

end Family

end AMO
