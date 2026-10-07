/-
# The Green series for the tail recurrence  (paper Lemma 2.4, `ext-lem:tail-inverse`, core)

In any complete normed ring `B` (in the paper: the phase-coefficient Wiener algebra), consider
the tail recurrence
  `l_j = β_j l_{j+1} - l_{j+2} + d_j`,   `j ≥ 0`,
with transfer matrices `A_j = [[β_j, -1], [1, 0]]` and products `P_{j,m} = A_j ⋯ A_{j+m-1}`.
If `‖P_{j,m}‖ ≤ C e^{γ m}` and `γ < s`, the **Green series**
  `(l_j, l_{j+1}) = ∑_{m ≥ 0} P_{j,m} e₁ d_{j+m}`
converges, solves the recurrence, satisfies
  `∑_j e^{s j} ‖l_j‖ ≤ C (1 - e^{γ - s})^{-1} ∑_j e^{s j} ‖d_j‖`,
and is the **unique** solution with `∑_j e^{s j} ‖l_j‖ < ∞` (no boundary condition needed).
Everything here is proved.
-/
import Mathlib

noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology

namespace AMO

namespace Tail

variable {B : Type*} [NormedRing B] [CompleteSpace B]

/-- The transfer matrix `[[β, -1], [1, 0]]`. -/
def tm (β : B) : Matrix (Fin 2) (Fin 2) B := !![β, -1; 1, 0]

/-- Products `P_{j,m} = A_j A_{j+1} ⋯ A_{j+m-1}`. -/
def P (β : ℕ → B) : ℕ → ℕ → Matrix (Fin 2) (Fin 2) B
  | _, 0 => 1
  | j, m + 1 => tm (β j) * P β (j + 1) m

/-- `e₁ d = (d, 0)`. -/
def e1 (d : B) : Fin 2 → B := ![d, 0]

lemma norm_e1_le (d : B) : ‖e1 d‖ ≤ ‖d‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg d)).2 fun i => ?_
  fin_cases i <;> simp [e1]

variable (β : ℕ → B) (d : ℕ → B)

/-- The terms of the Green series. -/
def gterm (j m : ℕ) : Fin 2 → B := P β j m *ᵥ e1 (d (j + m))

/-- The Green series `∑_m P_{j,m} e₁ d_{j+m}`. -/
def green (j : ℕ) : Fin 2 → B := ∑' m, gterm β d j m

variable {β d} {C γ s : ℝ}

section Bounds

variable (hC : 0 ≤ C) (hP : ∀ j m, ‖P β j m‖ ≤ C * Real.exp (γ * m)) (hγs : γ < s)
  (hd : Summable fun r : ℕ => Real.exp (s * r) * ‖d r‖)
include hC hP hγs hd

lemma norm_gterm_le (j m : ℕ) :
    ‖gterm β d j m‖ ≤ C * Real.exp (-s * j) * (Real.exp ((γ - s) * m) *
      (Real.exp (s * (j + m : ℕ)) * ‖d (j + m)‖)) := by
  unfold gterm
  refine (linfty_opNorm_mulVec _ _).trans ?_
  calc ‖P β j m‖ * ‖e1 (d (j + m))‖ ≤ C * Real.exp (γ * m) * ‖d (j + m)‖ :=
        mul_le_mul (hP j m) (norm_e1_le _) (norm_nonneg _) (by positivity)
    _ = C * Real.exp (-s * j) * (Real.exp ((γ - s) * m) *
          (Real.exp (s * (j + m : ℕ)) * ‖d (j + m)‖)) := by
        have : Real.exp (γ * m) = Real.exp (-s * j) * (Real.exp ((γ - s) * m) *
            Real.exp (s * (j + m : ℕ))) := by
          rw [← Real.exp_add, ← Real.exp_add]; congr 1; push_cast; ring
        rw [this]; ring

lemma summable_shift (j : ℕ) : Summable fun m : ℕ => Real.exp (s * (j + m : ℕ)) * ‖d (j + m)‖ :=
  hd.comp_injective (add_right_injective j)

lemma summable_gterm_norm (j : ℕ) : Summable fun m => ‖gterm β d j m‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_gterm_le hC hP hγs hd j) ?_
  refine Summable.mul_left _ (((summable_shift hC hP hγs hd j)).of_nonneg_of_le
    (fun m => by positivity) (fun m => ?_))
  have : Real.exp ((γ - s) * m) ≤ 1 :=
    Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg (by linarith) (Nat.cast_nonneg m))
  calc Real.exp ((γ - s) * m) * (Real.exp (s * (j + m : ℕ)) * ‖d (j + m)‖)
      ≤ 1 * (Real.exp (s * (j + m : ℕ)) * ‖d (j + m)‖) := by gcongr
    _ = _ := one_mul _

lemma summable_gterm (j : ℕ) : Summable (gterm β d j) :=
  (summable_gterm_norm hC hP hγs hd j).of_norm

/-- **The Green series solves the vector recurrence** `v_j = e₁ d_j + A_j v_{j+1}`. -/
theorem green_rec (j : ℕ) : green β d j = e1 (d j) + tm (β j) *ᵥ green β d (j + 1) := by
  unfold green
  rw [(summable_gterm hC hP hγs hd j).tsum_eq_zero_add]
  congr 1
  · simp [gterm, P]
  · have hmap : HasSum (fun m => tm (β j) *ᵥ gterm β d (j + 1) m)
        (tm (β j) *ᵥ ∑' m, gterm β d (j + 1) m) :=
      (summable_gterm hC hP hγs hd (j + 1)).hasSum.map
        (AddMonoidHom.mk' (fun v => tm (β j) *ᵥ v) (fun v w => Matrix.mulVec_add _ v w))
        (Continuous.matrix_mulVec continuous_const continuous_id)
    rw [← hmap.tsum_eq]
    congr 1
    funext m
    simp only [gterm, P, Matrix.mulVec_mulVec]
    congr 3
    omega

/-- The two coordinates of the Green series agree at adjacent sites. -/
theorem green_snd (j : ℕ) : green β d j 1 = green β d (j + 1) 0 := by
  rw [green_rec hC hP hγs hd j]
  simp [e1, tm, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- **The scalar recurrence** `l_j = β_j l_{j+1} - l_{j+2} + d_j` for `l_j = (green j)₀`. -/
theorem green_scalar (j : ℕ) :
    green β d j 0 = β j * green β d (j + 1) 0 - green β d (j + 2) 0 + d j := by
  have h := congrFun (green_rec hC hP hγs hd j) 0
  rw [h, ← green_snd hC hP hγs hd (j + 1)]
  simp [e1, tm, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  abel

/-- **The weighted bound** `∑_j e^{sj}‖v_j‖ ≤ C (1 - e^{γ-s})^{-1} ∑_r e^{sr}‖d_r‖`. -/
theorem green_weighted_bound :
    Summable (fun j : ℕ => Real.exp (s * j) * ‖green β d j‖) ∧
      ∑' j : ℕ, Real.exp (s * j) * ‖green β d j‖ ≤
        C / (1 - Real.exp (γ - s)) * ∑' r : ℕ, Real.exp (s * r) * ‖d r‖ := by
  set D : ℕ → ℝ := fun r => Real.exp (s * r) * ‖d r‖ with hD
  have hD0 : ∀ r, 0 ≤ D r := fun r => by positivity
  set q := Real.exp (γ - s)
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hqm : ∀ m : ℕ, Real.exp ((γ - s) * m) = q ^ m := fun m => by
    rw [← Real.exp_nat_mul]; ring_nf
  -- the double majorant `F(m, j) = q^m D(j + m)`
  set F : ℕ × ℕ → ℝ := fun z => q ^ z.1 * D (z.2 + z.1)
  have hF0 : 0 ≤ F := fun z => mul_nonneg (pow_nonneg hq0 _) (hD0 _)
  have htail : ∀ m : ℕ, ∑' j : ℕ, D (j + m) ≤ ∑' r, D r := fun m => by
    rw [← hd.sum_add_tsum_nat_add m]
    exact le_add_of_nonneg_left (Finset.sum_nonneg fun r _ => hD0 r)
  have hF : Summable F := by
    refine (summable_prod_of_nonneg hF0).2 ⟨fun m => ?_, ?_⟩
    · exact ((hd.comp_injective (add_left_injective m)).mul_left (q ^ m)).congr fun j => rfl
    · refine ((summable_geometric_of_lt_one hq0 hq1).mul_right (∑' r, D r)).of_nonneg_of_le
        (fun m => tsum_nonneg fun j => hF0 (m, j)) (fun m => ?_)
      simp only [F]
      rw [tsum_mul_left]
      exact mul_le_mul_of_nonneg_left (htail m) (pow_nonneg hq0 _)
  -- pointwise bound on `e^{sj}‖v_j‖`
  have hpt : ∀ j : ℕ, Real.exp (s * j) * ‖green β d j‖ ≤ C * ∑' m : ℕ, F (m, j) := by
    intro j
    have h1 : ‖green β d j‖ ≤ ∑' m, ‖gterm β d j m‖ :=
      norm_tsum_le_tsum_norm (summable_gterm_norm hC hP hγs hd j)
    have h2 : ∑' m, ‖gterm β d j m‖ ≤ ∑' m : ℕ, C * Real.exp (-s * j) * (Real.exp ((γ - s) * m) *
        (Real.exp (s * (j + m : ℕ)) * ‖d (j + m)‖)) :=
      (summable_gterm_norm hC hP hγs hd j).tsum_le_tsum (norm_gterm_le hC hP hγs hd j)
        ((hF.prod_symm.prod_factor j).mul_left (C * Real.exp (-s * j)) |>.congr fun m => by
          simp only [F, hqm, D, Prod.swap_prod_mk])
    rw [tsum_mul_left] at h2
    calc Real.exp (s * j) * ‖green β d j‖
        ≤ Real.exp (s * j) * (C * Real.exp (-s * j) * ∑' m : ℕ, Real.exp ((γ - s) * m) *
          (Real.exp (s * (j + m : ℕ)) * ‖d (j + m)‖)) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) (Real.exp_pos _).le
      _ = C * ∑' m : ℕ, F (m, j) := by
          have he : Real.exp (s * j) * Real.exp (-s * j) = 1 := by
            rw [← Real.exp_add]; simp
          rw [show Real.exp (s * j) * (C * Real.exp (-s * j) * ∑' m : ℕ, Real.exp ((γ - s) * m) *
            (Real.exp (s * (j + m : ℕ)) * ‖d (j + m)‖)) = (Real.exp (s * j) * Real.exp (-s * j)) *
            (C * ∑' m : ℕ, Real.exp ((γ - s) * m) * (Real.exp (s * (j + m : ℕ)) * ‖d (j + m)‖))
            by ring, he, one_mul]
          congr 1
          congr 1
          funext m
          simp only [F, hqm, D, add_comm j m]
  have hsum : Summable fun j : ℕ => Real.exp (s * j) * ‖green β d j‖ :=
    (hF.prod_symm.prod.mul_left C).of_nonneg_of_le (fun j => by positivity) hpt
  refine ⟨hsum, ?_⟩
  calc ∑' j : ℕ, Real.exp (s * j) * ‖green β d j‖
      ≤ ∑' j : ℕ, C * ∑' m : ℕ, F (m, j) := hsum.tsum_le_tsum hpt (hF.prod_symm.prod.mul_left C)
    _ = C * ∑' m : ℕ, ∑' j : ℕ, F (m, j) := by
        rw [tsum_mul_left]
        congr 1
        exact hF.tsum_comm (f := fun m j => F (m, j))
    _ ≤ C * ∑' m : ℕ, q ^ m * ∑' r, D r := by
        gcongr
        · exact hF.prod
        · exact (summable_geometric_of_lt_one hq0 hq1).mul_right _
        · simp only [F]; rw [tsum_mul_left]
          exact mul_le_mul_of_nonneg_left (htail _) (pow_nonneg hq0 _)
    _ = C / (1 - q) * ∑' r, D r := by
        rw [tsum_mul_right, tsum_geometric_of_lt_one hq0 hq1]; ring

end Bounds

/-! ### Uniqueness -/

omit [CompleteSpace B] in
lemma P_mulVec_iter {w : ℕ → Fin 2 → B} (hw : ∀ j, w j = tm (β j) *ᵥ w (j + 1)) (j m : ℕ) :
    w j = P β j m *ᵥ w (j + m) := by
  induction m generalizing j with
  | zero => simp [P]
  | succ m ih =>
    rw [P, ← Matrix.mulVec_mulVec, ← show j + 1 + m = j + (m + 1) by omega, ← ih (j + 1), ← hw]

/-- **Uniqueness**: a solution of the homogeneous recurrence with `∑ e^{sj}‖l_j‖ < ∞`
vanishes identically. -/
theorem homogeneous_eq_zero (hC : 0 ≤ C) (hP : ∀ j m, ‖P β j m‖ ≤ C * Real.exp (γ * m))
    (hγs : γ < s) (hs : 0 ≤ s) {l : ℕ → B} (hrec : ∀ j, l j = β j * l (j + 1) - l (j + 2))
    (hl : Summable fun j : ℕ => Real.exp (s * j) * ‖l j‖) (j : ℕ) : l j = 0 := by
  set w : ℕ → Fin 2 → B := fun j => ![l j, l (j + 1)]
  have hw : ∀ j, w j = tm (β j) *ᵥ w (j + 1) := by
    intro j
    ext i
    fin_cases i
    · simp [w, tm, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hrec j]; abel
    · simp [w, tm, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  set S := ∑' r : ℕ, Real.exp (s * r) * ‖l r‖
  have hlr : ∀ r : ℕ, ‖l r‖ ≤ S * Real.exp (-s * r) := by
    intro r
    have h := hl.le_tsum r (fun _ _ => by positivity)
    have he : Real.exp (s * r) * Real.exp (-s * r) = 1 := by rw [← Real.exp_add]; simp
    calc ‖l r‖ = (Real.exp (s * r) * ‖l r‖) * Real.exp (-s * r) := by
          rw [mul_comm (Real.exp _), mul_assoc, he, mul_one]
      _ ≤ S * Real.exp (-s * r) := mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
  have hwr : ∀ r : ℕ, ‖w r‖ ≤ S * Real.exp (-s * r) := by
    intro r
    have hS : 0 ≤ S := tsum_nonneg fun _ => by positivity
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    fin_cases i
    · simpa [w] using hlr r
    · have := hlr (r + 1)
      have hmono : Real.exp (-s * ((r + 1 : ℕ) : ℝ)) ≤ Real.exp (-s * r) :=
        Real.exp_le_exp.2 (by push_cast; nlinarith)
      simp only [w]
      exact this.trans (mul_le_mul_of_nonneg_left hmono hS)
  -- `‖w_j‖ ≤ C S e^{-sj} e^{(γ - s) m} → 0`
  have hbound : ∀ m : ℕ, ‖w j‖ ≤ C * S * Real.exp (-s * j) * Real.exp ((γ - s) * m) := by
    intro m
    rw [P_mulVec_iter hw j m]
    refine (linfty_opNorm_mulVec _ _).trans ?_
    calc ‖P β j m‖ * ‖w (j + m)‖ ≤ C * Real.exp (γ * m) * (S * Real.exp (-s * (j + m : ℕ))) :=
          mul_le_mul (hP j m) (hwr _) (norm_nonneg _) (by positivity)
      _ = C * S * Real.exp (-s * j) * Real.exp ((γ - s) * m) := by
          rw [show C * Real.exp (γ * m) * (S * Real.exp (-s * (j + m : ℕ))) =
            C * S * (Real.exp (γ * m) * Real.exp (-s * (j + m : ℕ))) by ring, ← Real.exp_add,
            mul_assoc (C * S), ← Real.exp_add]
          congr 2; push_cast; ring
  have hlim : Tendsto (fun m : ℕ => C * S * Real.exp (-s * j) * Real.exp ((γ - s) * m)) atTop
      (𝓝 0) := by
    have : Tendsto (fun m : ℕ => Real.exp ((γ - s) * m)) atTop (𝓝 0) := by
      have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos (γ - s)).le
        (Real.exp_lt_one_iff.2 (by linarith)))
      refine h.congr fun m => ?_
      rw [← Real.exp_nat_mul]; ring_nf
    simpa using this.const_mul (C * S * Real.exp (-s * j))
  have h0 : ‖w j‖ ≤ 0 := ge_of_tendsto' hlim (fun m => hbound m) |> fun h => h
  have hw0 : w j = 0 := norm_le_zero_iff.1 h0
  have := congrFun hw0 0
  simpa [w] using this

/-- **The Green series is the unique weighted solution** of the inhomogeneous recurrence. -/
theorem green_unique (hC : 0 ≤ C) (hP : ∀ j m, ‖P β j m‖ ≤ C * Real.exp (γ * m))
    (hγs : γ < s) (hs : 0 ≤ s) (hd : Summable fun r : ℕ => Real.exp (s * r) * ‖d r‖)
    {l : ℕ → B} (hrec : ∀ j, l j = β j * l (j + 1) - l (j + 2) + d j)
    (hl : Summable fun j : ℕ => Real.exp (s * j) * ‖l j‖) (j : ℕ) : l j = green β d j 0 := by
  set g : ℕ → B := fun j => green β d j 0
  have hg : Summable fun j : ℕ => Real.exp (s * j) * ‖g j‖ :=
    (green_weighted_bound hC hP hγs hd).1.of_nonneg_of_le (fun _ => by positivity) fun j => by
      gcongr; exact norm_le_pi_norm (green β d j) 0
  have hdiff := homogeneous_eq_zero (l := fun j => l j - g j) hC hP hγs hs
    (fun j => by
      simp only [g]
      rw [hrec j, green_scalar hC hP hγs hd j]
      noncomm_ring)
    ((hl.add hg).of_nonneg_of_le (fun _ => by positivity) fun j => by
      rw [← mul_add]; gcongr; exact norm_sub_le _ _) j
  exact sub_eq_zero.1 hdiff

end Tail

end AMO
