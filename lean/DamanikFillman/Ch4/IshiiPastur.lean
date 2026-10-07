/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# §4.7.1: the Ishii–Pastur theorem   (book pp. 343–344)

## Main results
* `DF.Cocycle.decay_of_ruelle` — a deterministic consequence of Ruelle's theorem
  (Theorem 3.8.7): if `(1/n) log ‖A_n ⋯ A_1‖ → L > 0`, then any orbit `A_n ⋯ A_1 v` that grows at
  most linearly decays exponentially.
* `DF.ErgodicFamily.atom_of_lyapBehavior` — the deterministic step in the proof of
  Theorem 4.7.2: if `H_ω` has Lyapunov behavior at `x ∈ ℝ` with `L(x) > 0` and `x` is a
  generalized eigenvalue, then `x` is an eigenvalue of `H_ω`, hence an atom of the canonical
  spectral measure `η_ω`.
* `DF.ErgodicFamily.measurableSet_lyapBehavior` — the set of pairs `(x, ω)` such that `H_ω` has
  Lyapunov behavior at `x` is measurable (needed for Fubini).
* `DF.ErgodicFamily.ae_volume_not_lyapBehavior` — (4.7.8): for `μ`-a.e. `ω`, `H_ω` has Lyapunov
  behavior at Lebesgue-a.e. `x`.
* `DF.ErgodicFamily.ishii_pastur` — **Theorem 4.7.2 (Ishii–Pastur)**, (4.7.4): for `μ`-a.e. `ω`,
  the absolutely continuous part of `η_ω` gives no weight to `{x : L(x) > 0} = ℝ \ Z`.

## Hypotheses
The proof uses Theorem 2.4.2(b) (generalized eigenvalues support the canonical spectral
measure), which is only available as the statement `DF.GenEigSupportStatement`; it enters as a
hypothesis (for the potentials `V_ω`).

## Deviations
The absolutely continuous part of a measure `η` is written
`volume.withDensity (η.rnDeriv volume)` (Lebesgue decomposition).
-/
import DamanikFillman.Ch4.Lyapunov
import DamanikFillman.Ch3.Ruelle
import DamanikFillman.Ch2.GenEigenSupport
import DamanikFillman.Ch1.SpectralDecomposition

noncomputable section

open scoped InnerProductSpace ComplexConjugate Matrix.Norms.L2Operator
open MeasureTheory Set Filter Topology

namespace DF

namespace Cocycle

lemma norm_C2_sq (w : C2) : ‖w‖ ^ 2 = ‖w 0‖ ^ 2 + ‖w 1‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two]

lemma norm_apply_le_C2 (w : C2) (i : Fin 2) : ‖w i‖ ≤ ‖w‖ := by
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  rw [norm_C2_sq]
  fin_cases i
  · simp only [Fin.zero_eta]; nlinarith [sq_nonneg ‖w 1‖]
  · simp only [Fin.mk_one]; nlinarith [sq_nonneg ‖w 0‖]

lemma norm_C2_le (w : C2) : ‖w‖ ≤ ‖w 0‖ + ‖w 1‖ := by
  refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 ?_
  rw [norm_C2_sq]; nlinarith [norm_nonneg (w 0), norm_nonneg (w 1)]

lemma tendsto_log_one_add_div : Tendsto (fun n : ℕ => Real.log (1 + n) / n) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
    (tendsto_atTop_add_const_left atTop (1 : ℝ) (tendsto_natCast_atTop_atTop (R := ℝ)))
  have h2 : Tendsto (fun n : ℕ => (1 + (n : ℝ)) / n) atTop (𝓝 1) := by
    have : Tendsto (fun n : ℕ => 1 / (n : ℝ) + 1) atTop (𝓝 (0 + 1)) :=
      tendsto_one_div_atTop_nhds_zero_nat.add tendsto_const_nhds
    rw [zero_add] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have : (n : ℝ) ≠ 0 := by positivity
    field_simp
  have := h.mul h2
  rw [zero_mul] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have : (n : ℝ) ≠ 0 := by positivity
  simp only [Function.comp_apply, pow_one, one_mul, add_zero]
  field_simp

/-- A deterministic consequence of Ruelle's theorem (Theorem 3.8.7): under its hypotheses
(with `‖A_n‖` bounded), an orbit `A_n ⋯ A_1 v`, `v ≠ 0`, of at most linear growth decays
exponentially. -/
theorem decay_of_ruelle {A : ℕ → M2} {L : ℝ} (hdet : ∀ n, (A n).det = 1) {K : ℝ}
    (hK : ∀ n, ‖A n‖ ≤ K)
    (hT : Tendsto (fun n : ℕ => Real.log ‖seqProd A n‖ / n) atTop (𝓝 L)) (hL : 0 < L)
    {v : C2} (hv : v ≠ 0) {C : ℝ} (hpoly : ∀ n : ℕ, ‖actC (seqProd A n) v‖ ≤ C * (1 + n)) :
    ∃ c > 0, ∀ᶠ n : ℕ in atTop, ‖actC (seqProd A n) v‖ ≤ Real.exp (-(c * n)) := by
  have hA1 : ∀ n, 1 ≤ ‖A n‖ := fun n => one_le_norm_of_det_eq_one (hdet n)
  have hA0 : Tendsto (fun n : ℕ => Real.log ‖A n‖ / n) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (tendsto_const_div_atTop_nhds_zero_nat (Real.log K)) (fun n => ?_) (fun n => ?_)
    · exact div_nonneg (Real.log_nonneg (hA1 n)) (Nat.cast_nonneg n)
    · exact div_le_div_of_nonneg_right (Real.log_le_log (by linarith [hA1 n]) (hK n))
        (Nat.cast_nonneg n)
  obtain ⟨W, -, hin, hout⟩ := ruelle A L hdet hA0 hT hL
  by_cases hvW : v ∈ W
  · refine ⟨L / 2, by positivity, ?_⟩
    have h := hin v hvW hv
    filter_upwards [h.eventually (gt_mem_nhds (show -L < -(L / 2) by linarith)),
      eventually_ge_atTop 1] with n hn hn1
    set w := actC (seqProd A n) v
    rcases (norm_nonneg w).eq_or_lt with h0 | hpos
    · rw [← h0]; exact (Real.exp_pos _).le
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
      have : Real.log ‖w‖ < -(L / 2 * n) := by
        rw [div_lt_iff₀ hn0] at hn; linarith
      exact ((Real.log_lt_iff_lt_exp hpos).1 this).le
  · exfalso
    have h := hout v hvW
    set D := max C 1
    have hD : 1 ≤ D := le_max_right _ _
    have hup : Tendsto (fun n : ℕ => Real.log D / n + Real.log (1 + n) / n) atTop (𝓝 (0 + 0)) :=
      (tendsto_const_div_atTop_nhds_zero_nat _).add tendsto_log_one_add_div
    rw [add_zero] at hup
    have hle : ∀ n : ℕ, Real.log ‖actC (seqProd A n) v‖ / n ≤
        Real.log D / n + Real.log (1 + n) / n := by
      intro n
      rw [← add_div]
      refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg n)
      have h1n : (1 : ℝ) ≤ 1 + n := by have := Nat.cast_nonneg (α := ℝ) n; linarith
      rw [← Real.log_mul (by linarith) (by linarith)]
      have hb : ‖actC (seqProd A n) v‖ ≤ D * (1 + n) :=
        (hpoly n).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith))
      rcases (norm_nonneg (actC (seqProd A n) v)).eq_or_lt with h0 | hpos
      · rw [← h0, Real.log_zero]; exact Real.log_nonneg (by nlinarith)
      · exact Real.log_le_log hpos hb
    have := le_of_tendsto_of_tendsto' h hup hle
    linarith

end Cocycle

/-! ### Solutions and transfer matrices -/

/-- The initial vector `(u(1), u(0))` of a sequence, as an element of `ℂ²`. -/
def initVec (u : ℤ → ℂ) : Cocycle.C2 := WithLp.toLp 2 ![u 1, u 0]

lemma initVec_ne_zero {V : ℤ → ℝ} {z : ℂ} {u : ℤ → ℂ} (hu : IsSolution V z u) (hne : u ≠ 0) :
    initVec u ≠ 0 := by
  intro h
  have h0 : u 1 = 0 := by simpa [initVec] using congrArg (fun w : Cocycle.C2 => w 0) h
  have h1 : u 0 = 0 := by simpa [initVec] using congrArg (fun w : Cocycle.C2 => w 1) h
  exact hne (eq_zero_of_isSolution hu h1 h0)

/-- For a solution `u`, `A_z(n) (u(1), u(0))ᵀ = (u(n+1), u(n))ᵀ` (2.2.9), componentwise. -/
lemma actC_transferZ {V : ℤ → ℝ} {z : ℂ} {u : ℤ → ℂ} (hu : IsSolution V z u) (n : ℤ) :
    Cocycle.actC (transferZ V z n) (initVec u) 0 = u (n + 1) ∧
      Cocycle.actC (transferZ V z n) (initVec u) 1 = u n := by
  have key := (isSolution_iff_transferZ V z u).1 hu n
  have k0 := congrFun key 0
  have k1 := congrFun key 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one] at k0 k1
  rw [Cocycle.actC_apply, Cocycle.actC_apply]
  simp only [initVec, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  exact ⟨k0.symm, k1.symm⟩

lemma norm_le_norm_actC_transferZ {V : ℤ → ℝ} {z : ℂ} {u : ℤ → ℂ} (hu : IsSolution V z u)
    (n : ℤ) : ‖u n‖ ≤ ‖Cocycle.actC (transferZ V z n) (initVec u)‖ := by
  rw [← (actC_transferZ hu n).2]; exact Cocycle.norm_apply_le_C2 _ 1

lemma norm_actC_transferZ_le {V : ℤ → ℝ} {z : ℂ} {u : ℤ → ℂ} (hu : IsSolution V z u) (n : ℤ) :
    ‖Cocycle.actC (transferZ V z n) (initVec u)‖ ≤ ‖u (n + 1)‖ + ‖u n‖ := by
  have := Cocycle.norm_C2_le (Cocycle.actC (transferZ V z n) (initVec u))
  rwa [(actC_transferZ hu n).1, (actC_transferZ hu n).2] at this

/-! ### Continuity of transfer matrices in the energy -/

lemma continuous_transfer (v : ℝ) : Continuous fun z : ℂ => transfer z v := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j <;> simp [transfer] <;> fun_prop

lemma continuous_transferInv (v : ℝ) : Continuous fun z : ℂ => transferInv z v := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j <;> simp [transferInv] <;> fun_prop

lemma continuous_transferProd (V : ℤ → ℝ) (n : ℕ) : Continuous fun z : ℂ => transferProd V z n := by
  induction n with
  | zero => exact continuous_const
  | succ n ih => exact (continuous_transfer _).matrix_mul ih

lemma continuous_transferNeg (V : ℤ → ℝ) (n : ℕ) : Continuous fun z : ℂ => transferNeg V z n := by
  induction n with
  | zero => exact continuous_const
  | succ n ih => exact (continuous_transferInv _).matrix_mul ih

/-! ### Lyapunov behavior and eigenvalues -/

namespace ErgodicFamily

variable {Ω : Type*} [MeasurableSpace Ω] (E : ErgodicFamily Ω)

/-- The one-step matrices whose products are `A^n_z(ω)`. -/
def topSeq (z : ℂ) (ω : Ω) (n : ℕ) : Cocycle.M2 := E.Az z ((⇑E.T)^[n - 1] ω)

lemma seqProd_topSeq (z : ℂ) (ω : Ω) (n : ℕ) :
    Cocycle.seqProd (E.topSeq z ω) n = E.An z n ω := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Cocycle.seqProd, ih, An_succ]; simp [topSeq]

/-- The one-step matrices whose products are `A^{-n}_z(ω)`. -/
def botSeq (z : ℂ) (ω : Ω) (n : ℕ) : Cocycle.M2 := E.Bz z ((⇑E.T.symm)^[n - 1] ω)

lemma seqProd_botSeq (z : ℂ) (ω : Ω) (n : ℕ) :
    Cocycle.seqProd (E.botSeq z ω) n = E.AnNeg z n ω := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Cocycle.seqProd, ih]; simp [botSeq, AnNeg, Cocycle.iter_succ]

/-- If `H_ω` has Lyapunov behavior at `z` with `L(z) > 0`, then every solution of `H_ω u = z u`
growing at most linearly is square-summable at `±∞`; in particular it is an `ℓ²` solution. -/
theorem memℓp_of_lyapBehavior {ω : Ω} {z : ℂ} (hL : E.LyapBehavior z ω) (hpos : 0 < E.lyap z)
    {u : ℤ → ℂ} (hu : IsSolution (E.V ω) z u) (hne : u ≠ 0) {C : ℝ}
    (hC : ∀ n : ℤ, ‖u n‖ ≤ C * (1 + |(n : ℝ)|)) : Memℓp u 2 := by
  have hv := initVec_ne_zero hu hne
  have hgeom : ∀ c : ℝ, 0 < c → Summable fun n : ℕ => Real.exp (-(c * n)) ^ 2 := by
    intro c hc
    have : Summable fun n : ℕ => (Real.exp (-(2 * c))) ^ n :=
      summable_geometric_of_lt_one (Real.exp_pos _).le (Real.exp_lt_one_iff.2 (by linarith))
    refine this.congr fun n => ?_
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; ring_nf
  refine memℓp_of_sqSum ?_ ?_
  · -- `+∞`
    have hbound : ∀ n : ℕ, ‖Cocycle.actC (Cocycle.seqProd (E.topSeq z ω) n) (initVec u)‖ ≤
        (3 * C) * (1 + n) := by
      intro n
      rw [seqProd_topSeq, ← E.transferProd_eq, ← transferZ_natCast]
      refine (norm_actC_transferZ_le hu n).trans ?_
      have h1 := hC (n + 1); have h2 := hC n
      push_cast at h1 h2
      rw [abs_of_nonneg (by positivity)] at h1 h2
      have hC0 : 0 ≤ C := by
        have := hC 0; simp at this; linarith [norm_nonneg (u 0)]
      nlinarith
    obtain ⟨c, hc, hev⟩ := Cocycle.decay_of_ruelle (A := E.topSeq z ω) (L := E.lyap z)
      (fun n => E.det_Az z _) (fun n => E.norm_Az_le z _)
      (by have := hL.1; unfold LyapBehaviorTop at this; simpa only [seqProd_topSeq] using this) hpos hv hbound
    refine Summable.of_norm_bounded_eventually_nat (hgeom c hc) ?_
    filter_upwards [hev] with n hn
    rw [seqProd_topSeq, ← E.transferProd_eq, ← transferZ_natCast] at hn
    rw [norm_pow, norm_norm]
    exact pow_le_pow_left₀ (norm_nonneg _) ((norm_le_norm_actC_transferZ hu n).trans hn) 2
  · -- `-∞`
    have hbound : ∀ n : ℕ, ‖Cocycle.actC (Cocycle.seqProd (E.botSeq z ω) n) (initVec u)‖ ≤
        (3 * C) * (1 + n) := by
      intro n
      rw [seqProd_botSeq, ← E.transferZ_neg_eq]
      refine (norm_actC_transferZ_le hu (-(n : ℤ))).trans ?_
      have h1 := hC (-(n : ℤ) + 1); have h2 := hC (-(n : ℤ))
      have hC0 : 0 ≤ C := by
        have := hC 0; simp at this; linarith [norm_nonneg (u 0)]
      have e1 : |((-(n : ℤ) + 1 : ℤ) : ℝ)| ≤ 1 + n := by
        push_cast; rw [abs_le]; constructor <;> linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      have e2 : |((-(n : ℤ) : ℤ) : ℝ)| = n := by push_cast; rw [abs_neg]; simp
      rw [e2] at h2
      have h1' : ‖u (-(n : ℤ) + 1)‖ ≤ C * (2 + n) :=
        h1.trans (mul_le_mul_of_nonneg_left (by linarith) hC0)
      nlinarith
    obtain ⟨c, hc, hev⟩ := Cocycle.decay_of_ruelle (A := E.botSeq z ω) (L := E.lyap z)
      (fun n => E.det_Bz z _) (fun n => E.norm_Bz_le z _)
      (by have := hL.2; unfold LyapBehaviorBot at this; simpa only [seqProd_botSeq] using this) hpos hv hbound
    refine Summable.of_norm_bounded_eventually_nat (hgeom c hc) ?_
    filter_upwards [hev] with n hn
    rw [seqProd_botSeq, ← E.transferZ_neg_eq] at hn
    rw [norm_pow, norm_norm]
    exact pow_le_pow_left₀ (norm_nonneg _) ((norm_le_norm_actC_transferZ hu _).trans hn) 2

/-- If `ψ` is an eigenvector of `H_ω` for the eigenvalue `x` and `ψ(j) ≠ 0`, then `x` is an
atom of `η_{ω,j}`. -/
theorem spec_singleton_pos_of_eigen {ω : Ω} {x : ℝ} {ψ : L2 ℤ} (heig : E.H ω ψ = (x : ℂ) • ψ)
    {j : ℤ} (hj : ψ j ≠ 0) : 0 < E.spec ω (dlt j) {x} := by
  have hS : MeasurableSet ({x} : Set ℝ) := measurableSet_singleton x
  have hP : specProj (E.H ω) (E.isSelfAdjoint_H ω) {x} ψ = ψ :=
    (eigen_iff_specProj_singleton (A := E.H ω) (hA := E.isSelfAdjoint_H ω) ψ x).1 heig
  rw [pos_iff_ne_zero]
  intro h0
  have hnorm := norm_specProj_apply_sq (A := E.H ω) (hA := E.isSelfAdjoint_H ω) hS (dlt j)
  have h0' : (spectralMeasure (E.H ω) (E.isSelfAdjoint_H ω) (dlt j)).real {x} = 0 := by
    simp only [measureReal_def]; rw [show spectralMeasure (E.H ω) (E.isSelfAdjoint_H ω) (dlt j)
      = E.spec ω (dlt j) from rfl, h0, ENNReal.toReal_zero]
  rw [h0', sq_eq_zero_iff, norm_eq_zero] at hnorm
  have hsa := (isSelfAdjoint_specProj (A := E.H ω) (hA := E.isSelfAdjoint_H ω) hS).adjoint_eq
  have : ⟪dlt j, ψ⟫_ℂ = 0 := by
    rw [← hP, ← ContinuousLinearMap.adjoint_inner_left, hsa, hnorm, inner_zero_left]
  rw [inner_dlt] at this
  exact hj this

/-- **The deterministic step of Theorem 4.7.2**: if `H_ω` has Lyapunov behavior at `x ∈ ℝ`,
`L(x) > 0`, and `x` is a generalized eigenvalue (with a solution of at most linear growth), then
`x` is an eigenvalue of `H_ω`, so `η_ω({x}) > 0`. -/
theorem atom_of_lyapBehavior {ω : Ω} {x : ℝ} (hL : E.LyapBehavior (x : ℂ) ω)
    (hpos : 0 < E.lyap x) (hG : (x : ℂ) ∈ genEigSet (E.V ω) 1) : 0 < E.canonical ω {x} := by
  obtain ⟨u, hu0, hsol, C, hC⟩ := hG
  have hC' : ∀ n : ℤ, ‖u n‖ ≤ C * (1 + |(n : ℝ)|) := fun n => by simpa using hC n
  have hm := E.memℓp_of_lyapBehavior hL hpos hsol hu0 hC'
  set ψ : L2 ℤ := ⟨u, hm⟩
  have heig : E.H ω ψ = (x : ℂ) • ψ := eigen_of_isSolution (E.bddPot ω) hsol hm
  have hψ : ∀ n, ψ n = u n := fun n => rfl
  by_cases h0 : u 0 = 0
  · have h1 : u 1 ≠ 0 := fun h1 => hu0 (eq_zero_of_isSolution hsol h0 h1)
    have := E.spec_singleton_pos_of_eigen heig (j := 1) (by rwa [hψ])
    exact lt_of_lt_of_le this (by simp [canonical])
  · have := E.spec_singleton_pos_of_eigen heig (j := 0) (by rwa [hψ])
    exact lt_of_lt_of_le this (by simp [canonical])

/-! ### Measurability -/

lemma continuous_An (n : ℕ) (ω : Ω) : Continuous fun z : ℂ => E.An z n ω := by
  have : (fun z : ℂ => E.An z n ω) = fun z => transferProd (E.V ω) z n :=
    funext fun z => (E.transferProd_eq z ω n).symm
  rw [this]; exact continuous_transferProd _ n

lemma continuous_AnNeg (n : ℕ) (ω : Ω) : Continuous fun z : ℂ => E.AnNeg z n ω := by
  have : (fun z : ℂ => E.AnNeg z n ω) = fun z => transferNeg (E.V ω) z n :=
    funext fun z => by rw [← E.transferZ_neg_eq, transferZ_neg_natCast]
  rw [this]; exact continuous_transferNeg _ n

lemma measurable_AnNeg (z : ℂ) (n : ℕ) : Measurable (E.AnNeg z n) :=
  Cocycle.measurable_iter E.T.symm.measurable (E.measurable_Bz z) n

lemma one_le_norm_AnNeg (z : ℂ) (n : ℕ) (ω : Ω) : 1 ≤ ‖E.AnNeg z n ω‖ :=
  Cocycle.one_le_norm_of_det_eq_one (Cocycle.det_iter (E.det_Bz z) n ω)

/-- Joint measurability of `(x, ω) ↦ log ‖A^n_x(ω)‖`. -/
lemma measurable_logNorm_An (n : ℕ) :
    Measurable fun p : ℝ × Ω => Real.log ‖E.An (p.1 : ℂ) n p.2‖ := by
  refine measurable_uncurry_of_continuous_of_measurable
    (u := fun (x : ℝ) (ω : Ω) => Real.log ‖E.An (x : ℂ) n ω‖) (fun ω => ?_) (fun x => ?_)
  · refine Real.continuousOn_log.comp_continuous
      (((E.continuous_An n ω).comp Complex.continuous_ofReal).norm) (fun x => ?_)
    have := E.one_le_norm_An (x : ℂ) n ω
    simp only [mem_compl_iff, mem_singleton_iff]; linarith
  · exact (E.measurable_An x n).norm.log

/-- Joint measurability of `(x, ω) ↦ log ‖A^{-n}_x(ω)‖`. -/
lemma measurable_logNorm_AnNeg (n : ℕ) :
    Measurable fun p : ℝ × Ω => Real.log ‖E.AnNeg (p.1 : ℂ) n p.2‖ := by
  refine measurable_uncurry_of_continuous_of_measurable
    (u := fun (x : ℝ) (ω : Ω) => Real.log ‖E.AnNeg (x : ℂ) n ω‖) (fun ω => ?_) (fun x => ?_)
  · refine Real.continuousOn_log.comp_continuous
      (((E.continuous_AnNeg n ω).comp Complex.continuous_ofReal).norm) (fun x => ?_)
    have := E.one_le_norm_AnNeg (x : ℂ) n ω
    simp only [mem_compl_iff, mem_singleton_iff]; linarith
  · exact (E.measurable_AnNeg x n).norm.log

/-- The Lyapunov exponent is a measurable function of the (real) energy. -/
lemma measurable_lyap_real : Measurable fun x : ℝ => E.lyap x := by
  refine measurable_of_tendsto_metrizable
    (f := fun (n : ℕ) (x : ℝ) => (∫ ω, Real.log ‖E.An (x : ℂ) n ω‖ ∂E.μ) / n) (fun n => ?_)
    (tendsto_pi_nhds.2 fun x => E.tendsto_integral_lyap x)
  exact ((E.measurable_logNorm_An n).stronglyMeasurable.integral_prod_right' (ν := E.μ)).measurable.div_const _

/-- The set of `(x, ω)` such that `H_ω` has Lyapunov behavior at `x` is measurable. -/
lemma measurableSet_lyapBehavior :
    MeasurableSet {p : ℝ × Ω | E.LyapBehavior (p.1 : ℂ) p.2} := by
  have htop : MeasurableSet {p : ℝ × Ω | E.LyapBehaviorTop (p.1 : ℂ) p.2} := by
    have : {p : ℝ × Ω | E.LyapBehaviorTop (p.1 : ℂ) p.2} = {p : ℝ × Ω | Tendsto
        (fun n : ℕ => Real.log ‖E.An (p.1 : ℂ) n p.2‖ / n - E.lyap p.1) atTop (𝓝 0)} := by
      ext p; simp only [mem_ofPred_eq, LyapBehaviorTop]; exact tendsto_sub_nhds_zero_iff.symm
    rw [this]
    exact measurableSet_tendsto (𝓝 0) fun n =>
      ((E.measurable_logNorm_An n).div_const _).sub (E.measurable_lyap_real.comp measurable_fst)
  have hbot : MeasurableSet {p : ℝ × Ω | E.LyapBehaviorBot (p.1 : ℂ) p.2} := by
    have : {p : ℝ × Ω | E.LyapBehaviorBot (p.1 : ℂ) p.2} = {p : ℝ × Ω | Tendsto
        (fun n : ℕ => Real.log ‖E.AnNeg (p.1 : ℂ) n p.2‖ / n - E.lyap p.1) atTop (𝓝 0)} := by
      ext p; simp only [mem_ofPred_eq, LyapBehaviorBot]; exact tendsto_sub_nhds_zero_iff.symm
    rw [this]
    exact measurableSet_tendsto (𝓝 0) fun n =>
      ((E.measurable_logNorm_AnNeg n).div_const _).sub (E.measurable_lyap_real.comp measurable_fst)
  exact htop.inter hbot

/-- (4.7.8): for `μ`-a.e. `ω`, `H_ω` has Lyapunov behavior at Lebesgue-a.e. energy `x`
(Fubini, from Remark 4.4.4). -/
theorem ae_ae_lyapBehavior :
    ∀ᵐ ω ∂E.μ, ∀ᵐ x : ℝ ∂(volume : Measure ℝ), E.LyapBehavior (x : ℂ) ω :=
  (Measure.ae_ae_comm (μ := (volume : Measure ℝ)) (ν := E.μ)
    (p := fun (x : ℝ) ω => E.LyapBehavior (x : ℂ) ω) E.measurableSet_lyapBehavior).1
    (ae_of_all _ fun x => E.ae_lyapBehavior (x : ℂ))

/-! ### Theorem 4.7.2 -/

/-- **Theorem 4.7.2 (Ishii–Pastur)**, (4.7.4): assuming Theorem 2.4.2(b) for the potentials
`V_ω` (`DF.GenEigSupportStatement`), for `μ`-a.e. `ω` the absolutely continuous part of the
canonical spectral measure `η_ω` gives zero weight to `ℝ \ Z = {x : L(x) ≠ 0}`. -/
theorem ishii_pastur (hGE : ∀ ω, GenEigSupportStatement (E.V ω) (E.bddPot ω)) :
    ∀ᵐ ω ∂E.μ, volume.withDensity ((E.canonical ω).rnDeriv volume) {x : ℝ | E.lyap x ≠ 0} = 0 := by
  filter_upwards [E.ae_ae_lyapBehavior] with ω hω
  set η := E.canonical ω
  have : IsFiniteMeasure η := by simp only [η, canonical, spec]; infer_instance
  set ac := volume.withDensity (η.rnDeriv volume)
  have hac : ac ≪ volume := withDensity_absolutelyContinuous _ _
  have hle : ac ≤ η := Measure.withDensity_rnDeriv_le η volume
  set A := {x : ℝ | ¬ E.LyapBehavior (x : ℂ) ω}
  set B := {x : ℝ | (x : ℂ) ∉ genEigSet (E.V ω) 1}
  set C := {x : ℝ | 0 < η {x}}
  have hA : ac A = 0 := hac (by rw [ae_iff] at hω; exact hω)
  have hB : ac B = 0 := by
    have : η B = 0 := hGE ω 1 (by norm_num)
    exact le_antisymm ((hle.trans le_rfl) B |>.trans this.le) zero_le
  have hC : ac C = 0 := by
    have hcount : C.Countable := Measure.countable_meas_pos_of_disjoint_iUnion
      (As := fun x : ℝ => ({x} : Set ℝ)) (fun x => measurableSet_singleton x)
      (fun x y hxy => disjoint_singleton.2 hxy)
    exact hac (hcount.measure_zero _)
  have hsub : {x : ℝ | E.lyap x ≠ 0} ⊆ A ∪ B ∪ C := by
    intro x hx
    by_cases h1 : E.LyapBehavior (x : ℂ) ω
    · by_cases h2 : (x : ℂ) ∈ genEigSet (E.V ω) 1
      · right
        exact E.atom_of_lyapBehavior h1 (lt_of_le_of_ne (E.lyap_nonneg _) (Ne.symm hx)) h2
      · left; right; exact h2
    · left; left; exact h1
  refine le_antisymm ((measure_mono hsub).trans ?_) zero_le
  refine (measure_union_le _ _).trans ?_
  rw [hC, add_zero]
  refine (measure_union_le _ _).trans ?_
  rw [hA, hB, add_zero]

end ErgodicFamily

end DF
