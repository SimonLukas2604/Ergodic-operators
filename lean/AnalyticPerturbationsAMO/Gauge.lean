/-
# Gauge transform and consequences of an exact preparation  (paper §2.2)

* For a Jacobi operator `J = a U + ā(·-1) U^{-1} + b` with `a_n = c_n q_n`, `|q_n| = 1`, the
  diagonal unitary `Γ` with `γ_{n+1} = \overline{q_n} γ_n` satisfies `Γ^* J Γ = J^r`, where
  `J^r = c U + c(·-1) U^{-1} + b` has the moduli `c_n` as hoppings.  Such a `γ` exists for every
  phase sequence (no cohomological equation is needed).
* For an exact preparation `H_x - E = Q_x^* J_x Q_x`:  `u ∈ ker(H_x - E) ⇔ Q_x u ∈ ker J_x`, and
  `H_x - E` is invertible iff `J_x` is; in particular `E ∈ spec H_x ⇔ J_x` is not invertible.
Everything here is proved.
-/
import AnalyticPerturbationsAMO.Spectral

noncomputable section

open scoped ComplexConjugate
open L2

namespace AMO

/-! ### Jacobi operators with sequence coefficients -/

/-- `(J u)_n = a_n u_{n+1} + \overline{a_{n-1}} u_{n-1} + b_n u_n`. -/
def jac (a b : ℤ → ℂ) : Op ℤ :=
  weightedShift a (Equiv.addRight 1) + weightedShift (fun n => conj (a (n - 1))) (Equiv.addRight (-1)) +
    weightedShift b (Equiv.refl ℤ)

lemma jac_apply {a b : ℤ → ℂ} (ha : Bdd a) (hb : Bdd b) (u : L2 ℤ) (n : ℤ) :
    jac a b u n = a n * u (n + 1) + conj (a (n - 1)) * u (n - 1) + b n * u n := by
  have ha' : Bdd (fun n => conj (a (n - 1))) := by
    have := (ha.comp (Equiv.addRight (-1))).conj
    convert this using 3 with n
    simp [sub_eq_add_neg]
  simp only [jac, ContinuousLinearMap.add_apply, lp.coeFn_add, Pi.add_apply,
    weightedShift_apply ha, weightedShift_apply ha', weightedShift_apply hb]
  simp [sub_eq_add_neg]

/-- The diagonal operator `(Γ u)_n = γ_n u_n`. -/
def diagOp (γ : ℤ → ℂ) : Op ℤ := weightedShift γ (Equiv.refl ℤ)

lemma diagOp_apply {γ : ℤ → ℂ} (hγ : Bdd γ) (u : L2 ℤ) (n : ℤ) : diagOp γ u n = γ n * u n := by
  simp [diagOp, weightedShift_apply hγ]

lemma star_diagOp {γ : ℤ → ℂ} (hγ : Bdd γ) : star (diagOp γ) = diagOp (fun n => conj (γ n)) := by
  rw [diagOp, star_weightedShift hγ]
  rfl

/-- **Gauge identity** `Γ^* J Γ = J^r`. -/
theorem gauge_identity {c b q γ : ℤ → ℂ} (hc : Bdd c) (hb : Bdd b)
    (hq : ∀ n, ‖q n‖ = 1) (hγ : ∀ n, ‖γ n‖ = 1) (hrec : ∀ n, γ (n + 1) = conj (q n) * γ n) :
    star (diagOp γ) * jac (fun n => c n * q n) b * diagOp γ = jac c b := by
  have hγb : Bdd γ := bdd_of_norm_eq_one hγ
  have hγb' : Bdd (fun n => conj (γ n)) := hγb.conj
  have hab : Bdd (fun n => c n * q n) := hc.mul (bdd_of_norm_eq_one hq)
  have hnorm : ∀ z : ℂ, ‖z‖ = 1 → conj z * z = 1 := fun z hz => by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]; simp
  rw [star_diagOp hγb]
  ext u n
  simp only [ContinuousLinearMap.mul_apply, diagOp_apply hγb', jac_apply hab hb,
    diagOp_apply hγb, jac_apply hc hb]
  have h1 : conj (γ n) * (c n * q n) * γ (n + 1) = c n := by
    rw [hrec, show conj (γ n) * (c n * q n) * (conj (q n) * γ n) =
      c n * (q n * conj (q n)) * (conj (γ n) * γ n) by ring, hnorm _ (hγ n),
      mul_comm (q n), hnorm _ (hq n)]
    ring
  have h2 : conj (γ n) * conj (c (n - 1) * q (n - 1)) * γ (n - 1) = conj (c (n - 1)) := by
    have hr := hrec (n - 1)
    rw [sub_add_cancel] at hr
    rw [hr]
    simp only [map_mul, Complex.conj_conj]
    have e1 := hnorm _ (hq (n - 1))
    have e2 := hnorm _ (hγ (n - 1))
    linear_combination (conj (c (n - 1)) * (conj (γ (n - 1)) * γ (n - 1))) * e1 +
      conj (c (n - 1)) * e2
  have h3 : conj (γ n) * b n * γ n = b n := by
    rw [show conj (γ n) * b n * γ n = b n * (conj (γ n) * γ n) by ring, hnorm _ (hγ n), mul_one]
  calc conj (γ n) * ((c n * q n) * (γ (n + 1) * u (n + 1)) +
        conj (c (n - 1) * q (n - 1)) * (γ (n - 1) * u (n - 1)) + b n * (γ n * u n))
      = (conj (γ n) * (c n * q n) * γ (n + 1)) * u (n + 1) +
        (conj (γ n) * conj (c (n - 1) * q (n - 1)) * γ (n - 1)) * u (n - 1) +
        (conj (γ n) * b n * γ n) * u n := by ring
    _ = c n * u (n + 1) + conj (c (n - 1)) * u (n - 1) + b n * u n := by rw [h1, h2, h3]

/-- The gauge `γ` exists for every unimodular phase sequence. -/
def gaugeSeq (q : ℤ → ℂ) : ℤ → ℂ
  | (n : ℕ) => ∏ k ∈ Finset.range n, conj (q k)
  | Int.negSucc n => ∏ k ∈ Finset.range (n + 1), q (-((k : ℤ) + 1))

theorem gaugeSeq_spec {q : ℤ → ℂ} (hq : ∀ n, ‖q n‖ = 1) :
    (∀ n, ‖gaugeSeq q n‖ = 1) ∧ ∀ n, gaugeSeq q (n + 1) = conj (q n) * gaugeSeq q n := by
  have hnorm : ∀ z : ℂ, ‖z‖ = 1 → conj z * z = 1 := fun z hz => by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]; simp
  refine ⟨fun n => ?_, fun n => ?_⟩
  · cases n with
    | ofNat n => simp [gaugeSeq, Finset.prod_eq_one, hq]
    | negSucc n => simp [gaugeSeq, Finset.prod_eq_one, hq]
  · cases n with
    | ofNat n =>
      show gaugeSeq q ((n + 1 : ℕ) : ℤ) = _
      simp only [gaugeSeq, Finset.prod_range_succ]
      rw [mul_comm]
      rfl
    | negSucc n =>
      cases n with
      | zero =>
        show gaugeSeq q 0 = conj (q (-1)) * gaugeSeq q (Int.negSucc 0)
        simp only [gaugeSeq, Finset.prod_range_one, Finset.range_zero, Finset.prod_empty,
          Nat.cast_zero, zero_add]
        exact (hnorm _ (hq _)).symm
      | succ n =>
        have : Int.negSucc (n + 1) + 1 = Int.negSucc n := by omega
        rw [this]
        simp only [gaugeSeq, Finset.prod_range_succ]
        have e : -(((n + 1 : ℕ) : ℤ) + 1) = Int.negSucc (n + 1) := by omega
        rw [e]
        have h1 := hnorm _ (hq (Int.negSucc (n + 1)))
        linear_combination (-((∏ k ∈ Finset.range n, q (-((k : ℤ) + 1))) *
          q (-((n : ℤ) + 1)))) * h1

/-! ### Consequences of an exact preparation -/

namespace JacobiPrep

variable {α : ℝ} {Hx : ℝ → Op ℤ} {E : ℝ} (P : JacobiPrep α Hx E)

lemma star_units_isUnit (Q : (Op ℤ)ˣ) : IsUnit (star (Q : Op ℤ)) := by
  refine ⟨⟨star (Q : Op ℤ), star (↑Q⁻¹ : Op ℤ), ?_, ?_⟩, rfl⟩
  · rw [← star_mul, Q.inv_mul, star_one]
  · rw [← star_mul, Q.mul_inv, star_one]

/-- `u ∈ ker(H_x - E) ⇔ Q_x u ∈ ker J_x`. -/
theorem ker_iff (x : ℝ) (u : L2 ℤ) :
    (Hx x - algebraMap ℂ (Op ℤ) E) u = 0 ↔ jacobi α P.a P.b x ((P.Q x : Op ℤ) u) = 0 := by
  rw [P.factor x]
  change (star (P.Q x : Op ℤ)) (jacobi α P.a P.b x ((P.Q x : Op ℤ) u)) = 0 ↔ _
  obtain ⟨S, hS⟩ := star_units_isUnit (P.Q x)
  constructor
  · intro h
    have h2 : (↑S⁻¹ : Op ℤ) ((S : Op ℤ) (jacobi α P.a P.b x ((P.Q x : Op ℤ) u))) =
        jacobi α P.a P.b x ((P.Q x : Op ℤ) u) := by
      rw [← ContinuousLinearMap.mul_apply, S.inv_mul]; rfl
    rw [← h2, hS, h, map_zero]
  · intro h
    rw [h, map_zero]

/-- `H_x - E` is invertible iff the prepared Jacobi operator `J_x` is. -/
theorem isUnit_iff (x : ℝ) :
    IsUnit (Hx x - algebraMap ℂ (Op ℤ) E) ↔ IsUnit (jacobi α P.a P.b x) := by
  rw [P.factor x]
  obtain ⟨S, hS⟩ := star_units_isUnit (P.Q x)
  rw [← hS, mul_assoc, Units.isUnit_units_mul, Units.isUnit_mul_units]

/-- `E ∈ spec(H_x)` iff `J_x` is not invertible. -/
theorem mem_spectrum_iff (x : ℝ) :
    (E : ℂ) ∈ spectrum ℂ (Hx x) ↔ ¬ IsUnit (jacobi α P.a P.b x) := by
  rw [spectrum.mem_iff, ← P.isUnit_iff x, ← neg_sub]
  exact ⟨fun h hu => h hu.neg, fun h hu => h (by simpa using hu.neg)⟩

end JacobiPrep

end AMO
