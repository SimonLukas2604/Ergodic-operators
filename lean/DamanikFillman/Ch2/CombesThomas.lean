/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# §2.5  The Combes–Thomas estimate  (book pp. 165–168)

## Main results
* **Theorem 2.5.1 (Combes–Thomas estimate)**: `DF.combes_thomas` — for `z ∈ ρ(H)` and
  `ε = dist(z, σ(H))`,
  `|⟨δₙ, (H - z)⁻¹ δₘ⟩| ≤ 2 ε⁻¹ e^{-min(ε/8, 1) |n - m|}`; and the existential form
  `DF.combes_thomas_exists` (there is a universal `c > 0`).

## Deviation (method of proof)
The book conjugates `H` by the unbounded multiplication operator `e^{γ n}` and leaves the
identity (2.5.10) `⟨δₙ, R_γ δₘ⟩ = e^{γ(n-m)} ⟨δₙ, R δₘ⟩` as an exercise.  To keep everything
bounded we conjugate instead by the bounded, boundedly invertible multiplication operator
`W_L` by `e^{γ clamp_L(n)}`, `clamp_L(n) = max(-L, min(n, L))`, for which the analogues of
(2.5.4), (2.5.9) and (2.5.10) hold uniformly in `L`; choosing `L ≥ |n|, |m|` gives the
estimate.  The resolvent is `DF.res` from `Ch1/BoundedOperators.lean`.
-/
import DamanikFillman.Ch2.Schrodinger
import DamanikFillman.Ch1.BoundedOperators

noncomputable section

open scoped InnerProductSpace ComplexConjugate
open L2 Metric

namespace DF

section CT

variable {V : ℤ → ℝ}

/-- `clamp_L(n) = max(-L, min(n, L))`. -/
def clampL (L : ℕ) (n : ℤ) : ℤ := max (-(L : ℤ)) (min n L)

lemma clampL_succ (L : ℕ) (n : ℤ) : clampL L (n + 1) - clampL L n = 0 ∨
    clampL L (n + 1) - clampL L n = 1 := by
  unfold clampL; omega

lemma clampL_of_abs_le {L : ℕ} {n : ℤ} (h : |n| ≤ L) : clampL L n = n := by
  unfold clampL; rw [abs_le] at h; omega

/-- The weight `w(n) = e^{γ clamp_L(n)}`. -/
def ctWeight (γ : ℝ) (L : ℕ) (n : ℤ) : ℝ := Real.exp (γ * clampL L n)

lemma ctWeight_pos (γ : ℝ) (L : ℕ) (n : ℤ) : 0 < ctWeight γ L n := Real.exp_pos _

lemma ctWeight_bdd (γ : ℝ) (L : ℕ) : Bdd fun n => ((ctWeight γ L n : ℝ) : ℂ) := by
  refine ⟨Real.exp (|γ| * L), fun n => ?_⟩
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (ctWeight_pos γ L n), ctWeight,
    Real.exp_le_exp]
  have : |(clampL L n : ℝ)| ≤ L := by
    have h : |clampL L n| ≤ L := by unfold clampL; rw [abs_le]; omega
    exact_mod_cast h
  calc γ * clampL L n ≤ |γ * clampL L n| := le_abs_self _
    _ = |γ| * |(clampL L n : ℝ)| := abs_mul _ _
    _ ≤ |γ| * L := by gcongr

lemma ctWeight_inv_bdd (γ : ℝ) (L : ℕ) : Bdd fun n => (((ctWeight γ L n)⁻¹ : ℝ) : ℂ) := by
  obtain ⟨M, hM⟩ := ctWeight_bdd (-γ) L
  refine ⟨M, fun n => ?_⟩
  have e : (ctWeight γ L n)⁻¹ = ctWeight (-γ) L n := by
    rw [ctWeight, ctWeight, ← Real.exp_neg]; ring_nf
  show ‖(((ctWeight γ L n)⁻¹ : ℝ) : ℂ)‖ ≤ M
  rw [e]; exact hM n

/-- Ratio bound: `|w(n)/w(n ± 1) - 1| ≤ 2|γ|` for `|γ| ≤ 1`. -/
lemma ctWeight_ratio_succ {γ : ℝ} (hγ : |γ| ≤ 1) (L : ℕ) (n : ℤ) :
    ‖((ctWeight γ L n / ctWeight γ L (n + 1) - 1 : ℝ) : ℂ)‖ ≤ 2 * |γ| := by
  rw [Complex.norm_real, Real.norm_eq_abs, ctWeight, ctWeight, ← Real.exp_sub]
  rcases clampL_succ L n with h | h
  · have : γ * (clampL L n : ℝ) - γ * (clampL L (n + 1) : ℝ) = 0 := by
      have h' : (clampL L (n + 1) : ℝ) = clampL L n := by
        have : clampL L (n + 1) = clampL L n := by omega
        exact_mod_cast this
      rw [h']; ring
    rw [this]; simp
  · have : γ * (clampL L n : ℝ) - γ * (clampL L (n + 1) : ℝ) = -γ := by
      have h' : (clampL L (n + 1) : ℝ) = clampL L n + 1 := by
        have : clampL L (n + 1) = clampL L n + 1 := by omega
        exact_mod_cast this
      rw [h']; ring
    rw [this]
    have := Real.abs_exp_sub_one_le (x := -γ) (by rwa [abs_neg])
    rwa [abs_neg] at this

lemma ctWeight_ratio_pred {γ : ℝ} (hγ : |γ| ≤ 1) (L : ℕ) (n : ℤ) :
    ‖((ctWeight γ L n / ctWeight γ L (n - 1) - 1 : ℝ) : ℂ)‖ ≤ 2 * |γ| := by
  rw [Complex.norm_real, Real.norm_eq_abs, ctWeight, ctWeight, ← Real.exp_sub]
  rcases clampL_succ L (n - 1) with h | h
  · have : γ * (clampL L n : ℝ) - γ * (clampL L (n - 1) : ℝ) = 0 := by
      have h' : (clampL L n : ℝ) = clampL L (n - 1) := by
        have : clampL L n = clampL L (n - 1) := by rw [sub_add_cancel] at h; omega
        exact_mod_cast this
      rw [h']; ring
    rw [this]; simp
  · have : γ * (clampL L n : ℝ) - γ * (clampL L (n - 1) : ℝ) = γ := by
      have h' : (clampL L n : ℝ) = clampL L (n - 1) + 1 := by
        have : clampL L n = clampL L (n - 1) + 1 := by rw [sub_add_cancel] at h; omega
        exact_mod_cast this
      rw [h']; ring
    rw [this]
    exact Real.abs_exp_sub_one_le hγ

/-- Multiplication by the weight. -/
def ctW (γ : ℝ) (L : ℕ) : Op := weightedShift (fun n => ((ctWeight γ L n : ℝ) : ℂ)) (Equiv.refl ℤ)

/-- Multiplication by the inverse weight. -/
def ctWinv (γ : ℝ) (L : ℕ) : Op :=
  weightedShift (fun n => (((ctWeight γ L n)⁻¹ : ℝ) : ℂ)) (Equiv.refl ℤ)

lemma ctW_apply (γ : ℝ) (L : ℕ) (ψ : L2 ℤ) (n : ℤ) :
    ctW γ L ψ n = (ctWeight γ L n : ℂ) * ψ n := by
  rw [ctW, weightedShift_apply (ctWeight_bdd γ L)]; rfl

lemma ctWinv_apply (γ : ℝ) (L : ℕ) (ψ : L2 ℤ) (n : ℤ) :
    ctWinv γ L ψ n = (((ctWeight γ L n)⁻¹ : ℝ) : ℂ) * ψ n := by
  rw [ctWinv, weightedShift_apply (ctWeight_inv_bdd γ L)]; rfl

lemma ctW_mul_ctWinv (γ : ℝ) (L : ℕ) : ctW γ L * ctWinv γ L = 1 := by
  ext ψ n
  simp only [ContinuousLinearMap.mul_apply, ctW_apply, ctWinv_apply, ContinuousLinearMap.one_apply]
  have h : ((ctWeight γ L n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (ctWeight_pos γ L n).ne'
  push_cast
  field_simp

lemma ctWinv_mul_ctW (γ : ℝ) (L : ℕ) : ctWinv γ L * ctW γ L = 1 := by
  ext ψ n
  simp only [ContinuousLinearMap.mul_apply, ctW_apply, ctWinv_apply, ContinuousLinearMap.one_apply]
  have h : ((ctWeight γ L n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (ctWeight_pos γ L n).ne'
  push_cast
  field_simp

/-- The perturbation `W H W⁻¹ - H`. -/
def ctD (γ : ℝ) (L : ℕ) : Op :=
  weightedShift (fun n => ((ctWeight γ L n / ctWeight γ L (n + 1) - 1 : ℝ) : ℂ))
      (Equiv.addRight 1) +
    weightedShift (fun n => ((ctWeight γ L n / ctWeight γ L (n - 1) - 1 : ℝ) : ℂ))
      (Equiv.addRight (-1))

lemma bdd_ratio_succ (γ : ℝ) (L : ℕ) :
    Bdd fun n => ((ctWeight γ L n / ctWeight γ L (n + 1) - 1 : ℝ) : ℂ) := by
  obtain ⟨M, hM⟩ := ctWeight_bdd γ L
  obtain ⟨M', hM'⟩ := ctWeight_inv_bdd γ L
  refine ⟨M * M' + 1, fun n => ?_⟩
  have h1 := hM n; have h2 := hM' (n + 1)
  rw [Complex.norm_real] at h1 h2 ⊢
  calc ‖ctWeight γ L n / ctWeight γ L (n + 1) - 1‖
      ≤ ‖ctWeight γ L n / ctWeight γ L (n + 1)‖ + ‖(1 : ℝ)‖ := norm_sub_le _ _
    _ = ‖ctWeight γ L n‖ * ‖(ctWeight γ L (n + 1))⁻¹‖ + 1 := by
        rw [div_eq_mul_inv, norm_mul]; simp
    _ ≤ M * M' + 1 := by gcongr; exact (norm_nonneg _).trans h1

lemma bdd_ratio_pred (γ : ℝ) (L : ℕ) :
    Bdd fun n => ((ctWeight γ L n / ctWeight γ L (n - 1) - 1 : ℝ) : ℂ) := by
  obtain ⟨M, hM⟩ := ctWeight_bdd γ L
  obtain ⟨M', hM'⟩ := ctWeight_inv_bdd γ L
  refine ⟨M * M' + 1, fun n => ?_⟩
  have h1 := hM n; have h2 := hM' (n - 1)
  rw [Complex.norm_real] at h1 h2 ⊢
  calc ‖ctWeight γ L n / ctWeight γ L (n - 1) - 1‖
      ≤ ‖ctWeight γ L n / ctWeight γ L (n - 1)‖ + ‖(1 : ℝ)‖ := norm_sub_le _ _
    _ = ‖ctWeight γ L n‖ * ‖(ctWeight γ L (n - 1))⁻¹‖ + 1 := by
        rw [div_eq_mul_inv, norm_mul]; simp
    _ ≤ M * M' + 1 := by gcongr; exact (norm_nonneg _).trans h1

/-- (2.5.4): `‖W H W⁻¹ - H‖ ≤ 4|γ|` for `|γ| ≤ 1`. -/
lemma norm_ctD_le {γ : ℝ} (hγ : |γ| ≤ 1) (L : ℕ) : ‖ctD γ L‖ ≤ 4 * |γ| := by
  refine (norm_add_le _ _).trans ?_
  have h1 := norm_weightedShift_le (σ := Equiv.addRight (1 : ℤ)) (by positivity : (0 : ℝ) ≤ 2 * |γ|)
    (ctWeight_ratio_succ hγ L)
  have h2 := norm_weightedShift_le (σ := Equiv.addRight (-1 : ℤ))
    (by positivity : (0 : ℝ) ≤ 2 * |γ|) (ctWeight_ratio_pred hγ L)
  linarith

/-- The conjugated operator: `W H W⁻¹ = H + D`. -/
lemma ctW_conj (hV : BddPot V) (γ : ℝ) (L : ℕ) :
    ctW γ L * schr V * ctWinv γ L = schr V + ctD γ L := by
  ext ψ n
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.add_apply, ctD, lp.coeFn_add,
    Pi.add_apply, ctW_apply, schr_apply hV, ctWinv_apply]
  rw [weightedShift_apply (bdd_ratio_succ γ L), weightedShift_apply (bdd_ratio_pred γ L)]
  simp only [Equiv.coe_addRight]
  have h0 : ((ctWeight γ L n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (ctWeight_pos γ L n).ne'
  have hn : ((ctWeight γ L n : ℝ) : ℂ) * ((ctWeight γ L n : ℝ) : ℂ)⁻¹ = 1 := mul_inv_cancel₀ h0
  rw [show n + -1 = n - 1 by ring]
  push_cast
  simp only [div_eq_mul_inv]
  linear_combination ((V n : ℂ) * ψ n) * hn

/-- The abstract core of the proof of Theorem 2.5.1, (2.5.6)–(2.5.9): if `W H W⁻¹ = H + D`,
`‖(H - z)⁻¹‖ ≤ ε⁻¹` and `‖D‖ ε⁻¹ ≤ 1/2`, then `‖W (H - z)⁻¹ W⁻¹‖ ≤ 2 ε⁻¹`. -/
lemma ct_core {H D W Wi R zI : Op} (hWWi : W * Wi = 1) (hWiW : Wi * W = 1)
    (hconj : W * H * Wi = H + D) (hzc : W * zI * Wi = zI) (hRl : R * (H - zI) = 1)
    (hRr : (H - zI) * R = 1) {ε : ℝ} (hR : ‖R‖ ≤ ε⁻¹) (hD : ‖D‖ * ε⁻¹ ≤ 1 / 2) :
    ‖W * R * Wi‖ ≤ 2 * ε⁻¹ := by
  have hsub : H + D - zI = W * (H - zI) * Wi := by
    rw [mul_sub, sub_mul, hconj, hzc]
  have hleft : W * R * Wi * (H + D - zI) = 1 := by
    rw [hsub]
    calc W * R * Wi * (W * (H - zI) * Wi) = W * (R * (Wi * W) * (H - zI)) * Wi := by
          simp only [mul_assoc]
      _ = 1 := by rw [hWiW, mul_one, hRl, mul_one, hWWi]
  have h1 : W * R * Wi * (H - zI) = 1 - W * R * Wi * D := by
    have : W * R * Wi * (H + D - zI) = W * R * Wi * (H - zI) + W * R * Wi * D := by
      rw [show H + D - zI = (H - zI) + D by abel, mul_add]
    rw [hleft] at this
    rw [eq_sub_iff_add_eq]; exact this.symm
  have hres : W * R * Wi = R - W * R * Wi * D * R := by
    calc W * R * Wi = W * R * Wi * ((H - zI) * R) := by rw [hRr, mul_one]
      _ = (W * R * Wi * (H - zI)) * R := by simp only [mul_assoc]
      _ = R - W * R * Wi * D * R := by rw [h1, sub_mul, one_mul]
  have h2 : ‖W * R * Wi‖ ≤ ‖R‖ + ‖W * R * Wi‖ * (‖D‖ * ‖R‖) := by
    calc ‖W * R * Wi‖ = ‖R - W * R * Wi * D * R‖ := by rw [← hres]
      _ ≤ ‖R‖ + ‖W * R * Wi * D * R‖ := norm_sub_le _ _
      _ ≤ ‖R‖ + ‖W * R * Wi‖ * (‖D‖ * ‖R‖) := by
          have : ‖W * R * Wi * D * R‖ ≤ ‖W * R * Wi‖ * (‖D‖ * ‖R‖) := by
            calc ‖W * R * Wi * D * R‖ ≤ ‖W * R * Wi * D‖ * ‖R‖ := norm_mul_le _ _
              _ ≤ ‖W * R * Wi‖ * ‖D‖ * ‖R‖ := by gcongr; exact norm_mul_le _ _
              _ = ‖W * R * Wi‖ * (‖D‖ * ‖R‖) := by ring
          linarith
  have h3 : ‖D‖ * ‖R‖ ≤ 1 / 2 :=
    le_trans (mul_le_mul_of_nonneg_left hR (norm_nonneg _)) hD
  have h4 : ‖W * R * Wi‖ * (‖D‖ * ‖R‖) ≤ ‖W * R * Wi‖ * (1 / 2) :=
    mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
  linarith

/-- **Theorem 2.5.1 (Combes–Thomas estimate)** with `c = 1/8`: for `z ∈ ρ(H)` and
`ε = dist(z, σ(H))`, `|⟨δₙ, (H - z)⁻¹ δₘ⟩| ≤ 2 ε⁻¹ e^{-min(ε/8, 1)|n - m|}`. -/
theorem combes_thomas (hV : BddPot V) {z : ℂ} (hz : z ∈ resolventSet ℂ (schr V)) (n m : ℤ) :
    ‖⟪dlt n, res (schr V) z (dlt m)⟫_ℂ‖ ≤
      2 * (infDist z (spectrum ℂ (schr V)))⁻¹ *
        Real.exp (-(min (infDist z (spectrum ℂ (schr V)) / 8) 1) * |(n : ℝ) - m|) := by
  have : Nontrivial (L2 ℤ) := ⟨⟨dlt 0, 0, fun h => by
    have := congrArg (fun f : L2 ℤ => f 0) h; simp at this⟩⟩
  have hsa : IsSelfAdjoint (schr V) := isSelfAdjoint_schr hV
  have : IsStarNormal (schr V) := hsa.isStarNormal
  obtain ⟨ε, hε⟩ : ∃ ε, ε = infDist z (spectrum ℂ (schr V)) := ⟨_, rfl⟩
  rw [← hε]
  have hεpos : 0 < ε := by
    rw [hε]
    exact ((spectrum.isClosed (schr V)).notMem_iff_infDist_pos (spectrum.nonempty _)).mp
      (mem_resolventSet_iff_notMem.mp hz)
  have hR : ‖res (schr V) z‖ = ε⁻¹ := by rw [hε]; exact norm_res_eq (schr V) hz
  obtain ⟨η, hη⟩ : ∃ η, η = min (ε / 8) 1 := ⟨_, rfl⟩
  rw [← hη]
  have hη0 : 0 < η := by rw [hη]; exact lt_min (by positivity) one_pos
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, γ = if m ≤ n then η else -η := ⟨_, rfl⟩
  have hγabs : |γ| = η := by
    rw [hγ]; split_ifs <;> simp [abs_of_pos hη0]
  have hγ1 : |γ| ≤ 1 := by rw [hγabs, hη]; exact min_le_right _ _
  obtain ⟨L, hL⟩ : ∃ L : ℕ, L = max n.natAbs m.natAbs := ⟨_, rfl⟩
  have hzc : ctW γ L * algebraMap ℂ Op z * ctWinv γ L = algebraMap ℂ Op z := by
    rw [mul_assoc, Algebra.commutes, ← mul_assoc, ctW_mul_ctWinv, one_mul]
  have hD : ‖ctD γ L‖ * ε⁻¹ ≤ 1 / 2 := by
    have h1 : ‖ctD γ L‖ ≤ 4 * η := by rw [← hγabs]; exact norm_ctD_le hγ1 L
    have h2 : 4 * η ≤ ε / 2 := by
      have := min_le_left (ε / 8) 1; rw [hη]; linarith
    calc ‖ctD γ L‖ * ε⁻¹ ≤ (ε / 2) * ε⁻¹ := by gcongr; exact h1.trans h2
      _ = 1 / 2 := by field_simp
  have hRγ := ct_core (ctW_mul_ctWinv γ L) (ctWinv_mul_ctW γ L) (ctW_conj hV γ L) hzc
    (res_mul_sub hz) (sub_mul_res hz) hR.le hD
  -- (2.5.10): matrix elements
  have hWi : ctWinv γ L (dlt m) = (((ctWeight γ L m)⁻¹ : ℝ) : ℂ) • dlt m := by
    ext k
    simp only [ctWinv_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, dlt_apply]
    split_ifs with hk
    · rw [hk]
    · simp
  have hmat : (ctW γ L * res (schr V) z * ctWinv γ L) (dlt m) n =
      ((ctWeight γ L n : ℝ) : ℂ) * ((((ctWeight γ L m)⁻¹ : ℝ) : ℂ) * res (schr V) z (dlt m) n) := by
    rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, hWi, map_smul, ctW_apply,
      lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  have hLn : |n| ≤ L := by
    have : (n.natAbs : ℤ) ≤ L := by rw [hL]; simp
    rwa [Int.natCast_natAbs] at this
  have hLm : |m| ≤ L := by
    have : (m.natAbs : ℤ) ≤ L := by rw [hL]; simp
    rwa [Int.natCast_natAbs] at this
  have hratio : ctWeight γ L m / ctWeight γ L n = Real.exp (-η * |(n : ℝ) - m|) := by
    rw [ctWeight, ctWeight, ← Real.exp_sub, clampL_of_abs_le hLn, clampL_of_abs_le hLm]
    congr 1
    rw [hγ]
    split_ifs with h
    · have h' : (m : ℝ) ≤ n := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith)]; ring
    · have h' : (n : ℝ) < m := by exact_mod_cast (lt_of_not_ge h)
      rw [abs_of_neg (by linarith)]; ring
  rw [inner_dlt]
  have hwn := ctWeight_pos γ L n
  have hwm := ctWeight_pos γ L m
  have key : res (schr V) z (dlt m) n = ((ctWeight γ L m / ctWeight γ L n : ℝ) : ℂ) *
      (ctW γ L * res (schr V) z * ctWinv γ L) (dlt m) n := by
    rw [hmat]
    have h1 : ((ctWeight γ L n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hwn.ne'
    have h2 : ((ctWeight γ L m : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hwm.ne'
    push_cast
    field_simp
  rw [key, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hwm hwn), hratio]
  have hel : ‖(ctW γ L * res (schr V) z * ctWinv γ L) (dlt m) n‖ ≤
      ‖ctW γ L * res (schr V) z * ctWinv γ L‖ := by
    calc _ ≤ ‖(ctW γ L * res (schr V) z * ctWinv γ L) (dlt m)‖ :=
          lp.norm_apply_le_norm (by norm_num) _ n
      _ ≤ ‖ctW γ L * res (schr V) z * ctWinv γ L‖ * ‖dlt m‖ := ContinuousLinearMap.le_opNorm _ _
      _ = _ := by rw [norm_dlt, mul_one]
  calc Real.exp (-η * |(n : ℝ) - m|) * ‖(ctW γ L * res (schr V) z * ctWinv γ L) (dlt m) n‖
      ≤ Real.exp (-η * |(n : ℝ) - m|) * (2 * ε⁻¹) := by gcongr; exact hel.trans hRγ
    _ = 2 * ε⁻¹ * Real.exp (-η * |(n : ℝ) - m|) := by ring

/-- **Theorem 2.5.1**, existential form: there is a universal constant `c > 0` such that
`|⟨δₙ, (H - z)⁻¹ δₘ⟩| ≤ 2 ε⁻¹ e^{-min(cε, 1)|n - m|}` for every bounded Schrödinger operator
`H`, all `n, m ∈ ℤ` and `z ∈ ρ(H)`, where `ε = dist(z, σ(H))`. -/
theorem combes_thomas_exists : ∃ c : ℝ, 0 < c ∧ ∀ (V : ℤ → ℝ), BddPot V →
    ∀ z ∈ resolventSet ℂ (schr V), ∀ n m : ℤ,
      ‖⟪dlt n, res (schr V) z (dlt m)⟫_ℂ‖ ≤
        2 * (infDist z (spectrum ℂ (schr V)))⁻¹ *
          Real.exp (-(min (c * infDist z (spectrum ℂ (schr V))) 1) * |(n : ℝ) - m|) := by
  refine ⟨1 / 8, by norm_num, fun V hV z hz n m => ?_⟩
  have := combes_thomas hV hz n m
  rwa [show (1 / 8 : ℝ) * infDist z (spectrum ℂ (schr V)) =
    infDist z (spectrum ℂ (schr V)) / 8 by ring]

end CT

end DF
