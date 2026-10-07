/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# §4.4 The Lyapunov exponent   (book pp. 323–326)

## Main definitions (namespace `DF.ErgodicFamily`)
* `E.Az z ω = [[z - f(Tω), -1], [1, 0]]` — the one-step cocycle generator (4.4.4);
* `E.An z n ω` — the transfer matrices `A^n_z(ω) = A_z(T^{n-1}ω) ⋯ A_z(ω)` (4.4.3), i.e. the
  iterates of the `SL(2, ℂ)` cocycle `(T, A_z)` (4.4.5)–(4.4.6);
* `E.AnNeg z n ω` — the left half-line transfer matrices `A^{-n}_z(ω)` (Remark 4.4.2), defined
  as iterates of the inverse cocycle over `T⁻¹`;
* `E.lyap z` — the Lyapunov exponent `L(z) = inf_n (1/n) E(log ‖A^n_z‖)` (4.4.8);
* `E.LyapBehaviorTop`, `E.LyapBehaviorBot`, `E.LyapBehavior` — Definition 4.4.3.

## Main results
* `E.transferProd_eq`, `E.transferZ_neg_eq` — the cocycle iterates are exactly the transfer
  matrices `A_z(n)` of `H_ω` from Chapter 2 (for `n ≥ 0` and `n ≤ 0`), cf. (4.4.2);
* `E.An_add` — the cocycle identity (4.4.7); `E.AnNeg_eq` — (4.4.11);
* `E.lyap_spec` — **Proposition 4.4.1**: `L(z) ≥ 0`,
  `L(z) = inf_n (1/n) E log‖A^n_z‖ = lim_n (1/n) E log‖A^n_z‖` and
  `(1/n) log ‖A^n_z(ω)‖ → L(z)` for `μ`-a.e. `ω`;
* `E.lyapNeg_eq_lyap` — **Remark 4.4.2**: the left Lyapunov exponent coincides with `L(z)`;
* `E.ae_lyapBehavior` — **Remark 4.4.4**: for each fixed `z`, `H_ω` has Lyapunov behavior at `z`
  (at both `±∞`) for `μ`-a.e. `ω`.

Proposition 4.4.5 (positivity of `L` off the almost sure spectrum) is in
`DamanikFillman/Ch4/LyapunovPositive.lean`.

No `Statement` props are introduced in this file.
-/
import DamanikFillman.Ch4.Setting
import DamanikFillman.Ch3.Cocycle
import DamanikFillman.Ch2.Transfer
import DamanikFillman.Ch1.SL2

noncomputable section

open scoped Matrix.Norms.L2Operator InnerProductSpace
open MeasureTheory Set Filter Topology Matrix

namespace DF

/-- `‖[[z - v, -1], [1, 0]]‖ ≤ ‖z‖ + |v| + 1`. -/
lemma norm_transfer_le (z : ℂ) (v : ℝ) : ‖transfer z v‖ ≤ ‖z‖ + |v| + 1 := by
  have hJ : (!![0, -1; 1, 0] : Mat2) ∈ unitary Mat2 := by
    rw [Unitary.mem_iff]
    constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_two]
  have hJn : ‖(!![0, -1; 1, 0] : Mat2)‖ = 1 := CStarRing.norm_of_mem_unitary hJ
  have hdec : transfer z v = !![z - v, 0; 0, 0] + !![0, -1; 1, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [transfer]
  rw [hdec]
  refine (norm_add_le _ _).trans ?_
  rw [hJn]
  have := norm_diag_le (z - v)
  have h2 : ‖z - (v : ℂ)‖ ≤ ‖z‖ + |v| := by
    refine (norm_sub_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
  linarith

namespace ErgodicFamily

variable {Ω : Type*} [MeasurableSpace Ω] (E : ErgodicFamily Ω)

/-! ### The transfer matrix cocycle -/

/-- The one-step cocycle generator `A_z(ω) = [[z - f(Tω), -1], [1, 0]]` (4.4.4). -/
def Az (z : ℂ) (ω : Ω) : Cocycle.M2 := transfer z (E.f (E.T ω))

/-- The transfer matrices `A^n_z(ω) = A_z(T^{n-1}ω) ⋯ A_z(Tω) A_z(ω)` (4.4.3). -/
def An (z : ℂ) (n : ℕ) (ω : Ω) : Cocycle.M2 := Cocycle.iter E.T (E.Az z) n ω

lemma Az_eq (z : ℂ) (ω : Ω) : E.Az z ω = transfer z (E.V ω 1) := by
  rw [Az, V_one]

/-- The cocycle identity (4.4.7): `A^{n+m}_z(ω) = A^m_z(Tⁿω) A^n_z(ω)`. -/
lemma An_add (z : ℂ) (n m : ℕ) (ω : Ω) :
    E.An z (n + m) ω = E.An z m ((⇑E.T)^[n] ω) * E.An z n ω :=
  Cocycle.iter_add n m ω

@[simp] lemma An_zero (z : ℂ) (ω : Ω) : E.An z 0 ω = 1 := rfl

lemma An_succ (z : ℂ) (n : ℕ) (ω : Ω) :
    E.An z (n + 1) ω = E.Az z ((⇑E.T)^[n] ω) * E.An z n ω := rfl

/-- The cocycle iterates are the transfer matrices `A_z(n)` of `H_ω` (2.2.4), cf. (4.4.2). -/
theorem transferProd_eq (z : ℂ) (ω : Ω) (n : ℕ) : transferProd (E.V ω) z n = E.An z n ω := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [transferProd, ih, An_succ, Az]
    congr 2
    rw [V, ← Nat.cast_succ, Tz_natCast, Function.iterate_succ_apply']

lemma det_Az (z : ℂ) (ω : Ω) : (E.Az z ω).det = 1 := det_transfer _ _

lemma det_An (z : ℂ) (n : ℕ) (ω : Ω) : (E.An z n ω).det = 1 :=
  Cocycle.det_iter (E.det_Az z) n ω

lemma one_le_norm_An (z : ℂ) (n : ℕ) (ω : Ω) : 1 ≤ ‖E.An z n ω‖ :=
  Cocycle.one_le_norm_of_det_eq_one (E.det_An z n ω)

lemma norm_Az_le (z : ℂ) (ω : Ω) : ‖E.Az z ω‖ ≤ ‖z‖ + E.fBound + 1 :=
  (norm_transfer_le _ _).trans (by linarith [E.abs_f_le (E.T ω)])

lemma norm_An_le (z : ℂ) (n : ℕ) (ω : Ω) : ‖E.An z n ω‖ ≤ (‖z‖ + E.fBound + 1) ^ n :=
  Cocycle.norm_iter_le (E.norm_Az_le z) n ω

lemma log_norm_An_nonneg (z : ℂ) (n : ℕ) (ω : Ω) : 0 ≤ Real.log ‖E.An z n ω‖ :=
  Real.log_nonneg (E.one_le_norm_An z n ω)

lemma log_norm_An_le (z : ℂ) (n : ℕ) (ω : Ω) :
    Real.log ‖E.An z n ω‖ ≤ n * Real.log (‖z‖ + E.fBound + 1) := by
  have h1 := E.one_le_norm_An z n ω
  calc Real.log ‖E.An z n ω‖ ≤ Real.log ((‖z‖ + E.fBound + 1) ^ n) :=
        Real.log_le_log (by linarith) (E.norm_An_le z n ω)
    _ = n * Real.log (‖z‖ + E.fBound + 1) := Real.log_pow _ _

lemma measurable_Az (z : ℂ) : Measurable (E.Az z) := by
  have hf : Measurable fun ω => ((E.f (E.T ω) : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp (E.measurable_f.comp E.T.measurable)
  refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
  fin_cases i <;> fin_cases j <;> simp [Az, transfer]
  · exact measurable_const.sub hf

lemma measurable_An (z : ℂ) (n : ℕ) : Measurable (E.An z n) :=
  Cocycle.measurable_iter E.T.measurable (E.measurable_Az z) n

lemma integrable_log_norm_An (z : ℂ) (n : ℕ) :
    Integrable (fun ω => Real.log ‖E.An z n ω‖) E.μ := by
  refine (integrable_const (n * Real.log (‖z‖ + E.fBound + 1))).mono'
    (E.measurable_An z n).norm.log.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (E.log_norm_An_nonneg z n ω)]
  exact E.log_norm_An_le z n ω

/-! ### The Lyapunov exponent: Proposition 4.4.1 -/

/-- The **Lyapunov exponent** `L(z) = inf_{n ≥ 1} (1/n) E(log ‖A^n_z‖)` (4.4.8). -/
def lyap (z : ℂ) : ℝ := Cocycle.lyap E.μ E.T (E.Az z)

lemma lyap_eq_iInf (z : ℂ) :
    E.lyap z = ⨅ n : ℕ, (∫ ω, Real.log ‖E.An z (n + 1) ω‖ ∂E.μ) / (n + 1) := rfl

/-- **Proposition 4.4.1.** For every `z ∈ ℂ`, `L(z) ∈ [0, ∞)`,
`L(z) = inf_n (1/n) E log ‖A^n_z‖ = lim_n (1/n) E log ‖A^n_z‖`, and
`(1/n) log ‖A^n_z(ω)‖ → L(z)` for `μ`-a.e. `ω`. -/
theorem lyap_spec (z : ℂ) :
    0 ≤ E.lyap z ∧
      Tendsto (fun n : ℕ => (∫ ω, Real.log ‖E.An z n ω‖ ∂E.μ) / n) atTop (𝓝 (E.lyap z)) ∧
      ∀ᵐ ω ∂E.μ, Tendsto (fun n : ℕ => Real.log ‖E.An z n ω‖ / n) atTop (𝓝 (E.lyap z)) :=
  Cocycle.lyapunov_exponent E.ergodic (E.measurable_Az z) (E.det_Az z) (E.norm_Az_le z)

lemma lyap_nonneg (z : ℂ) : 0 ≤ E.lyap z := (E.lyap_spec z).1

lemma tendsto_integral_lyap (z : ℂ) :
    Tendsto (fun n : ℕ => (∫ ω, Real.log ‖E.An z n ω‖ ∂E.μ) / n) atTop (𝓝 (E.lyap z)) :=
  (E.lyap_spec z).2.1

lemma lyap_le (z : ℂ) (n : ℕ) (hn : 1 ≤ n) :
    E.lyap z ≤ (∫ ω, Real.log ‖E.An z n ω‖ ∂E.μ) / n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hb : BddBelow (range fun k : ℕ => (∫ ω, Real.log ‖E.An z (k + 1) ω‖ ∂E.μ) / (k + 1)) :=
    ⟨0, by
      rintro _ ⟨k, rfl⟩
      exact div_nonneg (integral_nonneg fun ω => E.log_norm_An_nonneg z _ ω) (by positivity)⟩
  have := ciInf_le hb k
  rw [← lyap_eq_iInf] at this
  simpa using this

/-- Proposition 4.4.1 in terms of the transfer matrices `A_z(n)` of `H_ω`. -/
theorem ae_tendsto_log_norm_transferProd (z : ℂ) :
    ∀ᵐ ω ∂E.μ, Tendsto (fun n : ℕ => Real.log ‖transferProd (E.V ω) z n‖ / n) atTop
      (𝓝 (E.lyap z)) := by
  filter_upwards [(E.lyap_spec z).2.2] with ω hω
  simpa only [E.transferProd_eq] using hω

/-- Lyapunov behavior at `+∞` (Definition 4.4.3, (4.4.13)). -/
def LyapBehaviorTop (z : ℂ) (ω : Ω) : Prop :=
  Tendsto (fun n : ℕ => Real.log ‖E.An z n ω‖ / n) atTop (𝓝 (E.lyap z))

/-! ### The left half-line (Remark 4.4.2) -/

/-- Generator of the inverse cocycle over `T⁻¹`: `B_z(ω) = A_z(T⁻¹ω)⁻¹`. -/
def Bz (z : ℂ) (ω : Ω) : Cocycle.M2 := (E.Az z (E.T.symm ω))⁻¹

/-- The left half-line transfer matrices `A^{-n}_z(ω) = A_z(T^{-n}ω)⁻¹ ⋯ A_z(T^{-1}ω)⁻¹`. -/
def AnNeg (z : ℂ) (n : ℕ) (ω : Ω) : Cocycle.M2 := Cocycle.iter E.T.symm (E.Bz z) n ω

lemma Tz_neg_natCast (m : ℕ) (ω : Ω) : E.Tz (-(m : ℤ)) ω = (⇑E.T.symm)^[m] ω := by
  induction m with
  | zero => simp
  | succ m ihm =>
    rw [Nat.cast_succ, neg_add, ← sub_eq_add_neg, Tz_pred, ihm, Function.iterate_succ_apply']

lemma Bz_eq (z : ℂ) (ω : Ω) : E.Bz z ω = transferInv z (E.f ω) := by
  rw [Bz, Az, MeasurableEquiv.apply_symm_apply, transferInv_eq_inv]

/-- Identity (4.4.11): `A^{-n}_z(ω) = (A^n_z(T^{-n}ω))⁻¹`. -/
theorem AnNeg_eq (z : ℂ) (n : ℕ) (ω : Ω) :
    E.AnNeg z n ω = (E.An z n ((⇑E.T.symm)^[n] ω))⁻¹ := by
  induction n generalizing ω with
  | zero => simp [AnNeg, An]
  | succ n ih =>
    set y := (⇑E.T.symm)^[n] ω with hy
    have hA := E.An_add z 1 n (E.T.symm y)
    rw [add_comm 1 n, Function.iterate_one, MeasurableEquiv.apply_symm_apply] at hA
    have h1 : E.An z 1 (E.T.symm y) = E.Az z (E.T.symm y) := by simp [An]
    rw [AnNeg, Cocycle.iter_succ, ← AnNeg, ih, Bz, Function.iterate_succ_apply', ← hy, hA, h1,
      Matrix.mul_inv_rev]

/-- The left transfer matrices are the transfer matrices `A_z(-n)` of `H_ω` (2.2.10). -/
theorem transferZ_neg_eq (z : ℂ) (ω : Ω) (n : ℕ) :
    transferZ (E.V ω) z (-(n : ℤ)) = E.AnNeg z n ω := by
  rw [transferZ_neg_natCast]
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [transferNeg, ih]
    show _ = Cocycle.iter E.T.symm (E.Bz z) (n + 1) ω
    rw [Cocycle.iter_succ, Bz_eq, V, Tz_neg_natCast]; rfl

lemma det_Bz (z : ℂ) (ω : Ω) : (E.Bz z ω).det = 1 := by
  rw [Bz_eq]; simp [transferInv, Matrix.det_fin_two]

lemma norm_Bz_le (z : ℂ) (ω : Ω) : ‖E.Bz z ω‖ ≤ ‖z‖ + E.fBound + 1 := by
  rw [Bz, norm_inv_eq_norm _ (E.det_Az z _)]
  exact E.norm_Az_le z _

lemma measurable_Bz (z : ℂ) : Measurable (E.Bz z) := by
  have hf : Measurable fun ω => ((E.f ω : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp E.measurable_f
  have : E.Bz z = fun ω => transferInv z (E.f ω) := funext (E.Bz_eq z)
  rw [this]
  refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
  fin_cases i <;> fin_cases j <;> simp [transferInv]
  · exact measurable_const.sub hf

/-- `‖A^{-n}_z(ω)‖ = ‖A^n_z(T^{-n}ω)‖`. -/
lemma norm_AnNeg (z : ℂ) (n : ℕ) (ω : Ω) :
    ‖E.AnNeg z n ω‖ = ‖E.An z n ((⇑E.T.symm)^[n] ω)‖ := by
  rw [AnNeg_eq, norm_inv_eq_norm _ (E.det_An z n _)]

lemma integral_log_norm_AnNeg (z : ℂ) (n : ℕ) :
    ∫ ω, Real.log ‖E.AnNeg z n ω‖ ∂E.μ = ∫ ω, Real.log ‖E.An z n ω‖ ∂E.μ := by
  simp_rw [norm_AnNeg]
  have hmp : MeasurePreserving ((⇑E.T.symm)^[n]) E.μ E.μ := E.measurePreserving_symm.iterate n
  have := integral_map (μ := E.μ) hmp.measurable.aemeasurable
    (f := fun ω => Real.log ‖E.An z n ω‖) (E.measurable_An z n).norm.log.aestronglyMeasurable
  rw [hmp.map_eq] at this
  exact this.symm

/-- The left Lyapunov exponent `L_-(z) = inf_n (1/n) E log ‖A^{-n}_z‖` (4.4.10). -/
def lyapNeg (z : ℂ) : ℝ := Cocycle.lyap E.μ E.T.symm (E.Bz z)

/-- **Remark 4.4.2**: `L_-(z) = L(z)` (4.4.12). -/
theorem lyapNeg_eq_lyap (z : ℂ) : E.lyapNeg z = E.lyap z := by
  unfold lyapNeg lyap Cocycle.lyap
  refine iInf_congr fun n => ?_
  have := E.integral_log_norm_AnNeg z (n + 1)
  simp only [AnNeg, An] at this
  rw [this]

/-- Lyapunov behavior at `-∞` (Definition 4.4.3, (4.4.14)). -/
def LyapBehaviorBot (z : ℂ) (ω : Ω) : Prop :=
  Tendsto (fun n : ℕ => Real.log ‖E.AnNeg z n ω‖ / n) atTop (𝓝 (E.lyap z))

/-- Lyapunov behavior at `z` (at both `±∞`), Definition 4.4.3. -/
def LyapBehavior (z : ℂ) (ω : Ω) : Prop := E.LyapBehaviorTop z ω ∧ E.LyapBehaviorBot z ω

/-- **Remark 4.4.4**: for every `z`, `H_ω` has Lyapunov behavior at `z` for `μ`-a.e. `ω`. -/
theorem ae_lyapBehavior (z : ℂ) : ∀ᵐ ω ∂E.μ, E.LyapBehavior z ω := by
  have hneg := Cocycle.lyapunov_exponent E.ergodic.symm (E.measurable_Bz z) (E.det_Bz z)
    (E.norm_Bz_le z)
  filter_upwards [(E.lyap_spec z).2.2, hneg.2.2] with ω h1 h2
  refine ⟨h1, ?_⟩
  have h3 : Cocycle.lyap E.μ E.T.symm (E.Bz z) = E.lyap z := E.lyapNeg_eq_lyap z
  rw [h3] at h2
  exact h2

end ErgodicFamily

end DF
