/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# §4.9.1: Johnson's theorem  (book pp. 379–382)

Topological setting: `X` a compact metric space, `T : X ≃ₜ X` a homeomorphism and
`f : X → ℝ` continuous.  No invariant measure is needed for Johnson's theorem.

## Main definitions
* `DF.Johnson.schrMat E v ∈ SL(2, ℝ)` — the matrix `[[E - v, -1], [1, 0]]`;
* `DF.Johnson.schrCoc T f E` — the Schrödinger cocycle `A_E(ω) = [[E - f(Tω), -1], [1, 0]]`
  (4.10.4) as a continuous `SL(2, ℝ)` cocycle over `T`;
* `DF.Johnson.pot T f ω n = f(Tⁿω)` and `DF.Johnson.ham T f ω = H_ω`;
* `DF.Johnson.UHset T f` — the set `𝒰ℋ` of energies at which `(T, A_E)` is uniformly
  hyperbolic (4.9.2).

## Main results
* `DF.Johnson.sq_le_of_UH` / `DF.Johnson.norm_sq_le_of_UH` — the key estimate: if `E ∈ 𝒰ℋ`,
  there is `C` with `‖ψ‖² ≤ C ‖(H_ω - E) ψ‖²` for **all** `ω` and `ψ ∈ ℓ²(ℤ)`;
* `DF.Johnson.not_mem_spectrum_of_UH` — `E ∈ 𝒰ℋ ⇒ E ∉ σ(H_ω)` for every `ω`;
* `DF.Johnson.mem_spectrum_of_not_UH` — `E ∉ 𝒰ℋ ⇒ E ∈ σ(H_ω)` for some `ω`;
* `DF.Johnson.johnson` — **Theorem 4.9.3**: `⋃_ω σ(H_ω) = ℝ \ 𝒰ℋ`.

## Deviation from the book
The book proves `σ(H_ω) ⊆ ℝ \ 𝒰ℋ` through Theorem 2.4.2(c) (`σ(H) = closure 𝒢`), whose part (b)
is only recorded as a `Statement` in Chapter 2.  We instead give a direct proof: using the
uniform one-sided exponential growth of every vector under a uniformly hyperbolic cocycle
(`DF.Cocycle.one_sided_growth_of_uniformExpGrowth`) and a Duhamel formula for the
inhomogeneous equation `(H_ω - E) ψ = φ`, we show that `H_ω - E` is bounded below, which for a
self-adjoint operator excludes `E` from the spectrum.  The other inclusion follows the book
(bounded orbits give bounded solutions, i.e. generalized eigenfunctions; Theorem 2.4.2(a)).

No `Statement` props are introduced in this file.
-/
import DamanikFillman.Ch3.UHOpen
import DamanikFillman.Ch2.GenEigen
import DamanikFillman.Ch1.BoundedOperators

noncomputable section

set_option linter.unusedSectionVars false

open Filter Set Function Topology Matrix Metric L2
open scoped Matrix.Norms.L2Operator

namespace DF

namespace Johnson

open Cocycle

/-! ### The Schrödinger cocycle -/

/-- The matrix `[[E - v, -1], [1, 0]] ∈ SL(2, ℝ)`. -/
def schrMat (E v : ℝ) : SL2R := ⟨!![E - v, -1; 1, 0], by simp [Matrix.det_fin_two]⟩

lemma schrMat_coe (E v : ℝ) : ((schrMat E v : SL2R) : M2R) = !![E - v, -1; 1, 0] := rfl

variable {X : Type*} [MetricSpace X] [CompactSpace X] (T : X ≃ₜ X) (f : X → ℝ)

/-- The Schrödinger cocycle `A_E(ω) = [[E - f(Tω), -1], [1, 0]]` (4.10.4). -/
def schrCoc (E : ℝ) : X → SL2R := fun ω => schrMat E (f (T ω))

/-- `Tⁿ`, `n ∈ ℤ`. -/
abbrev tp (n : ℤ) : X → X := tpow T.toEquiv n

/-- The potential `V_ω(n) = f(Tⁿω)`. -/
def pot (ω : X) (n : ℤ) : ℝ := f (tp T n ω)

/-- The operator `H_ω`. -/
def ham (ω : X) : Op := schr (pot T f ω)

/-- The set `𝒰ℋ` of energies `E` for which `(T, A_E)` is uniformly hyperbolic (4.9.2). -/
def UHset : Set ℝ := {E | UniformExpGrowth T (schrCoc T f E)}

variable {T f}

lemma continuous_schrCoc (hf : Continuous f) (E : ℝ) :
    Continuous fun ω => ((schrCoc T f E ω : SL2R) : M2R) := by
  simp only [schrCoc, schrMat_coe]
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j <;> simp <;>
    first | exact continuous_const | exact continuous_const.sub (hf.comp T.continuous)

lemma bddPot (hf : Continuous f) (ω : X) : BddPot (pot T f ω) := by
  obtain ⟨C, hC⟩ := (isCompact_range hf).isBounded.exists_norm_le
  exact ⟨C, fun n => by rw [← Real.norm_eq_abs]; exact hC _ ⟨_, rfl⟩⟩

lemma tp_add_one (n : ℤ) (ω : X) : tp T (n + 1) ω = T (tp T n ω) := tpow_add_one n ω

lemma iterate_tp (n : ℤ) (m : ℕ) (ω : X) : (⇑T.toEquiv)^[m] (tp T n ω) = tp T (n + m) ω := by
  rw [tp, tp, tpow_add, tpow_natCast]

/-! ### Bounded orbits give generalized eigenfunctions -/

/-- The cocycle iterates propagate the vector `(u(n+1), u(n))`. -/
lemma iterZ_succ_act (E : ℝ) (ω : X) (v : EuclideanSpace ℝ (Fin 2)) (n : ℤ) :
    act ((iterZ T.toEquiv (schrCoc T f E) (n + 1) ω : SL2R) : M2R) v =
      act (schrMat E (pot T f ω (n + 1)) : M2R)
        (act ((iterZ T.toEquiv (schrCoc T f E) n ω : SL2R) : M2R) v) := by
  rw [iterZ_succ, Matrix.SpecialLinearGroup.coe_mul, act_mul]
  simp only [schrCoc, pot]
  rw [tp_add_one]

/-- A bounded orbit of `(T, A_E)` produces a bounded nonzero solution of `H_ω u = E u`. -/
theorem genEig_of_boundedOrbit {E : ℝ} (h : BoundedOrbit T (schrCoc T f E)) :
    ∃ ω : X, ∃ u : ℤ → ℂ, IsGenEigenfun (pot T f ω) E 1 u := by
  obtain ⟨ω, v, hv1, hvb⟩ := h
  set X' : ℤ → EuclideanSpace ℝ (Fin 2) :=
    fun n => act ((iterZ T.toEquiv (schrCoc T f E) n ω : SL2R) : M2R) v with hX'
  have hstep : ∀ n, X' (n + 1) = act (schrMat E (pot T f ω (n + 1)) : M2R) (X' n) :=
    fun n => iterZ_succ_act E ω v n
  have h0 : ∀ n, (X' (n + 1)) 1 = (X' n) 0 := by
    intro n; rw [hstep, act_apply]; simp [schrMat_coe]
  have h1 : ∀ n, (X' (n + 1)) 0 = (E - pot T f ω (n + 1)) * (X' n) 0 - (X' n) 1 := by
    intro n; rw [hstep, act_apply]; simp [schrMat_coe]; ring
  set u : ℤ → ℂ := fun n => ((X' n) 1 : ℂ) with hu
  have hu1 : ∀ n, ((X' n) 0 : ℂ) = u (n + 1) := by intro n; simp only [hu, h0]
  refine ⟨ω, u, ⟨?_, ?_, 1, fun n => ?_⟩⟩
  · intro h0'
    have hX0 : X' 0 = v := by simp [hX', iterZ_zero, act_one]
    have ha : v 1 = 0 := by
      have := congrFun h0' 0; simp only [hu, Pi.zero_apply, Complex.ofReal_eq_zero] at this
      rwa [hX0] at this
    have hb : v 0 = 0 := by
      have := congrFun h0' 1
      simp only [hu, Pi.zero_apply, Complex.ofReal_eq_zero] at this
      rw [show (1 : ℤ) = 0 + 1 by norm_num, h0, hX0] at this; exact this
    have : ‖v‖ = 0 := by
      rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, ha, hb]; simp
    rw [hv1] at this; norm_num at this
  · intro n
    have := h1 n
    have e1 : u (n + 1) = ((X' n) 0 : ℂ) := (hu1 n).symm
    have e2 : u (n - 1 + 1) = ((X' (n - 1)) 0 : ℂ) := (hu1 (n - 1)).symm
    have e3 : u n = ((X' (n - 1 + 1)) 1 : ℂ) := by simp only [hu, sub_add_cancel]
    have h1' := h1 (n - 1)
    rw [sub_add_cancel] at e2 h1'
    have h0' := h0 (n - 1)
    rw [sub_add_cancel] at h0'
    simp only [hu] at e1 e2 ⊢
    rw [e1, show n - 1 = n - 1 from rfl]
    rw [← e2] at *
    have hx : ((X' n) 0 : ℂ) = ((E : ℂ) - (pot T f ω n : ℂ)) * ((X' n) 1 : ℂ) - ((X' (n - 1)) 1) := by
      rw [h1', h0']; push_cast; ring
    rw [hx]; ring
  · have hb : ‖X' n‖ ≤ 1 := hvb n
    have : |(X' n) 1| ≤ ‖X' n‖ := by
      rw [← Real.norm_eq_abs]; exact PiLp.norm_apply_le (X' n) 1
    simp only [hu, Complex.norm_real, Real.norm_eq_abs, Real.rpow_one]
    have : 0 ≤ |(n : ℝ)| := abs_nonneg _
    nlinarith

/-! ### Uniform hyperbolicity: `H_ω - E` is bounded below -/

section estimate

variable (T f)

/-- `φ = (H_ω - E) ψ` for a real sequence `ψ`. -/
def defect (E : ℝ) (ω : X) (ψ : ℤ → ℝ) (n : ℤ) : ℝ :=
  ψ (n + 1) + ψ (n - 1) + pot T f ω n * ψ n - E * ψ n

variable {T f}

/-- `Ψ_n = (ψ(n+1), ψ(n))`. -/
def vec (ψ : ℤ → ℝ) (n : ℤ) : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![ψ (n + 1), ψ n]

/-- The vector `(a, 0)`. -/
def evec (a : ℝ) : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![a, 0]

lemma norm_vec_sq (ψ : ℤ → ℝ) (n : ℤ) : ‖vec ψ n‖ ^ 2 = ψ (n + 1) ^ 2 + ψ n ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]; simp [vec, sq_abs]

lemma norm_evec (a : ℝ) : ‖evec a‖ = |a| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]; simp [evec, Real.sqrt_sq_eq_abs]

lemma vec_step (E : ℝ) (ω : X) (ψ : ℤ → ℝ) (n : ℤ) :
    vec ψ (n + 1) = act (schrCoc T f E (tp T n ω) : M2R) (vec ψ n) +
      evec (defect T f E ω ψ (n + 1)) := by
  ext i; fin_cases i
  · simp [act_apply, vec, evec, defect, schrCoc, schrMat_coe, pot, tpow_add_one]; ring
  · simp [act_apply, vec, evec, schrCoc, schrMat_coe]

lemma act_sub (B : M2R) (x y : EuclideanSpace ℝ (Fin 2)) : act B (x - y) = act B x - act B y := by
  simp [act, map_sub]

/-- Duhamel formula for the inhomogeneous equation, with an error bound. -/
lemma duhamel (E : ℝ) (ω : X) (ψ : ℤ → ℝ) {K : ℝ} (hK1 : 1 ≤ K)
    (hK : ∀ x, ‖(schrCoc T f E x : M2R)‖ ≤ K) (n : ℤ) (m : ℕ) :
    ‖vec ψ (n + m) - act ((iter T.toEquiv (schrCoc T f E) m (tp T n ω) : SL2R) : M2R) (vec ψ n)‖ ≤
      K ^ m * ∑ j ∈ Finset.range m, |defect T f E ω ψ (n + j + 1)| := by
  induction m with
  | zero => simp [act_one]
  | succ m ih =>
    rw [iter_succ, Matrix.SpecialLinearGroup.coe_mul, act_mul, iterate_tp,
      show n + ((m + 1 : ℕ) : ℤ) = n + m + 1 by push_cast; ring, vec_step E ω ψ (n + m),
      Finset.sum_range_succ]
    set w := act ((iter T.toEquiv (schrCoc T f E) m (tp T n ω) : SL2R) : M2R) (vec ψ n)
    set A := ((schrCoc T f E (tp T (n + m) ω) : SL2R) : M2R)
    set d := defect T f E ω ψ (n + m + 1)
    set S := ∑ j ∈ Finset.range m, |defect T f E ω ψ (n + j + 1)|
    have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hKm : 1 ≤ K ^ (m + 1) := one_le_pow₀ hK1
    have heq : act A (vec ψ (n + m)) + evec d - act A w = act A (vec ψ (n + m) - w) + evec d := by
      rw [act_sub]; abel
    rw [heq]
    calc ‖act A (vec ψ (n + m) - w) + evec d‖ ≤ ‖act A (vec ψ (n + m) - w)‖ + ‖evec d‖ :=
          norm_add_le _ _
      _ ≤ K * (K ^ m * S) + |d| := by
          refine add_le_add ((norm_act_le _ _).trans ?_) (norm_evec d).le
          exact mul_le_mul (hK _) ih (norm_nonneg _) (by linarith)
      _ ≤ K ^ (m + 1) * (S + |d|) := by
          have h1 : 1 ≤ K ^ m * K := by rw [← pow_succ]; exact hKm
          rw [pow_succ]; nlinarith [mul_le_mul_of_nonneg_right h1 (abs_nonneg d)]

lemma norm_iter_le_R {A : X → SL2R} {K : ℝ} (hK1 : 1 ≤ K) (hK : ∀ x, ‖(A x : M2R)‖ ≤ K)
    (m : ℕ) (y : X) : ‖((iter T.toEquiv A m y : SL2R) : M2R)‖ ≤ K ^ m := by
  induction m with
  | zero =>
    simp only [iter_zero, Matrix.SpecialLinearGroup.coe_one, pow_zero]
    rw [Matrix.cstar_norm_def]
    exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by simp
  | succ m ih =>
    rw [iter_succ, Matrix.SpecialLinearGroup.coe_mul, pow_succ']
    exact (norm_mul_le _ _).trans (mul_le_mul (hK _) ih (norm_nonneg _) (by linarith))

lemma four_sq (a b c d : ℝ) : (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c),
    sq_nonneg (b - d), sq_nonneg (c - d)]

lemma summable_shift {g : ℤ → ℝ} (hg : Summable g) (k : ℤ) : Summable fun n => g (n + k) :=
  (Equiv.addRight k).summable_iff.2 hg

lemma hasSum_shift {g : ℤ → ℝ} {a : ℝ} (hg : HasSum g a) (k : ℤ) : HasSum (fun n => g (n + k)) a :=
  (Equiv.addRight k).hasSum_iff.2 hg

lemma summable_defect (hf : Continuous f) (E : ℝ) (ω : X) {ψ : ℤ → ℝ}
    (hψ : Summable fun n => ψ n ^ 2) : Summable fun n => defect T f E ω ψ n ^ 2 := by
  obtain ⟨B, hB⟩ := bddPot hf ω
  have h1 := summable_shift hψ 1
  have h2 := summable_shift hψ (-1)
  refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_)
    (((h1.add h2).add (hψ.mul_left (B ^ 2 + E ^ 2))).mul_left 4)
  have hb : |pot T f ω n| ≤ B := hB n
  have hb2 : pot T f ω n ^ 2 ≤ B ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hb 2
  have := four_sq (ψ (n + 1)) (ψ (n - 1)) (pot T f ω n * ψ n) (-(E * ψ n))
  simp only [← sub_eq_add_neg] at this
  simp only [sub_eq_add_neg n 1] at *
  refine this.trans ?_
  nlinarith [sq_nonneg (ψ n), mul_le_mul_of_nonneg_right hb2 (sq_nonneg (ψ n))]

/-- **Key estimate.** If `(T, A_E)` is uniformly hyperbolic, then `Σ ψ² ≤ C Σ ((H_ω - E)ψ)²` for
every real square-summable `ψ` and every `ω`, with `C` independent of `ω` and `ψ`. -/
theorem sq_le_of_UH (hf : Continuous f) {E : ℝ} (hE : E ∈ UHset T f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ω : X) (ψ : ℤ → ℝ), Summable (fun n => ψ n ^ 2) →
      ∑' n, ψ n ^ 2 ≤ C * ∑' n, defect T f E ω ψ n ^ 2 := by
  have hA := continuous_schrCoc (T := T) hf E
  obtain ⟨C0, hC0, l, hl, M0, hg⟩ := one_sided_growth_of_uniformExpGrowth T _ hA hE
  obtain ⟨K1, hK1⟩ := (isCompact_range hA).isBounded.exists_norm_le
  set K := max K1 1
  have hK1' : 1 ≤ K := le_max_right _ _
  have hK : ∀ x, ‖(schrCoc T f E x : M2R)‖ ≤ K := fun x => (hK1 _ ⟨x, rfl⟩).trans (le_max_left _ _)
  obtain ⟨N, hN3, hNM⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hl).eventually_ge_atTop
    (3 / C0) |>.and (eventually_ge_atTop M0)).exists
  have h3 : 3 ≤ l ^ N * C0 := by rwa [div_le_iff₀ hC0] at hN3
  set D : ℝ := 4 * K ^ N * K ^ N
  have hKN : 1 ≤ K ^ N := one_le_pow₀ hK1'
  have hD : K ^ N ≤ D := by simp only [D]; nlinarith
  refine ⟨8 * D ^ 2 * (N : ℝ) ^ 2, by positivity, fun ω ψ hψ => ?_⟩
  set φ := defect T f E ω ψ
  have hφ : Summable fun n => φ n ^ 2 := summable_defect hf E ω hψ
  set r : ℤ → ℝ := fun n => ∑ j ∈ Finset.range N, |φ (n + j + 1)|
  have hr0 : ∀ n, 0 ≤ r n := fun n => Finset.sum_nonneg fun _ _ => abs_nonneg _
  -- the pointwise estimate
  have hpt : ∀ n : ℤ, 3 * ‖vec ψ n‖ ≤ ‖vec ψ (n + N)‖ + ‖vec ψ (n - N)‖ +
      D * r n + D * r (n - N) := by
    intro n
    have hrn := hr0 n
    have hrm := hr0 (n - N)
    have hvn := norm_nonneg (vec ψ (n - N))
    have hvp := norm_nonneg (vec ψ (n + N))
    rcases hg (tp T n ω) (vec ψ n) with h | h
    · have h1 := h N hNM
      have h2 := duhamel E ω ψ hK1' hK n N
      have h4 : ‖act ((iter T.toEquiv (schrCoc T f E) N (tp T n ω) : SL2R) : M2R) (vec ψ n)‖ ≤
          ‖vec ψ (n + N)‖ + K ^ N * r n := by
        have := norm_sub_norm_le (act ((iter T.toEquiv (schrCoc T f E) N (tp T n ω) : SL2R) : M2R)
          (vec ψ n)) (vec ψ (n + N))
        rw [norm_sub_rev] at this
        have h2' : ‖vec ψ (n + N) - act ((iter T.toEquiv (schrCoc T f E) N (tp T n ω) : SL2R) : M2R)
            (vec ψ n)‖ ≤ K ^ N * r n := h2
        linarith
      have h5 : 3 * ‖vec ψ n‖ ≤ l ^ N * C0 * ‖vec ψ n‖ :=
        mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
      have h1' : l ^ N * C0 * ‖vec ψ n‖ ≤
          ‖act ((iter T.toEquiv (schrCoc T f E) N (tp T n ω) : SL2R) : M2R) (vec ψ n)‖ := h1
      nlinarith [mul_le_mul_of_nonneg_right hD hrn, mul_nonneg (by linarith : (0:ℝ) ≤ D) hrm]
    · have h1 := h N hNM
      set y := tp T (n - N) ω
      have hy : (⇑T.toEquiv)^[N] y = tp T n ω := by rw [iterate_tp, sub_add_cancel]
      set M := iter T.toEquiv (schrCoc T f E) N y
      have hinv : iterZ T.toEquiv (schrCoc T f E) (-(N : ℤ)) (tp T n ω) = M⁻¹ := by
        rw [← hy]; exact iterZ_neg_apply N y
      rw [hinv] at h1
      set w := act ((M⁻¹ : SL2R) : M2R) (vec ψ n)
      have hw : act (M : M2R) w = vec ψ n := by
        simp only [w]; rw [← act_mul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
          Matrix.SpecialLinearGroup.coe_one, act_one]
      have h2 := duhamel E ω ψ hK1' hK (n - N) N
      rw [sub_add_cancel, ← hw, ← act_sub] at h2
      have h6 := norm_le_inv_mul_act M (w - vec ψ (n - N))
      have hMinv : ‖((M⁻¹ : SL2R) : M2R)‖ ≤ 4 * K ^ N := by
        rw [Matrix.SpecialLinearGroup.coe_inv]
        exact (norm_adjugate_le_R _).trans (by
          have := norm_iter_le_R (T := T) hK1' hK N y; linarith)
      have h7 : ‖w - vec ψ (n - N)‖ ≤ D * r (n - N) := by
        refine h6.trans ?_
        calc ‖((M⁻¹ : SL2R) : M2R)‖ * ‖act (M : M2R) (w - vec ψ (n - N))‖
            ≤ (4 * K ^ N) * (K ^ N * r (n - N)) :=
              mul_le_mul hMinv h2 (norm_nonneg _) (by positivity)
          _ = D * r (n - N) := by simp only [D]; ring
      have h8 : ‖w‖ ≤ ‖vec ψ (n - N)‖ + ‖w - vec ψ (n - N)‖ := by
        have := norm_add_le (vec ψ (n - N)) (w - vec ψ (n - N))
        rwa [add_sub_cancel] at this
      have h5 : 3 * ‖vec ψ n‖ ≤ l ^ N * C0 * ‖vec ψ n‖ :=
        mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
      have h1' : l ^ N * C0 * ‖vec ψ n‖ ≤ ‖w‖ := h1
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ D) hrn]
  -- squares and sums
  set a : ℤ → ℝ := fun n => ‖vec ψ n‖ ^ 2
  have ha : Summable a := by
    have : a = fun n => ψ (n + 1) ^ 2 + ψ n ^ 2 := funext fun n => norm_vec_sq ψ n
    rw [this]; exact (summable_shift hψ 1).add hψ
  set S := ∑' n, a n
  have hS : HasSum a S := ha.hasSum
  set Sφ := ∑' n, φ n ^ 2
  have hφS : HasSum (fun n => φ n ^ 2) Sφ := hφ.hasSum
  have hrsq : ∀ n, r n ^ 2 ≤ N * ∑ j ∈ Finset.range N, φ (n + j + 1) ^ 2 := by
    intro n
    have := sq_sum_le_card_mul_sum_sq (s := Finset.range N) (f := fun j => |φ (n + j + 1)|)
    simpa [sq_abs] using this
  have hsumN : HasSum (fun n => (N : ℝ) * ∑ j ∈ Finset.range N, φ (n + j + 1) ^ 2)
      (N * ((N : ℝ) * Sφ)) := by
    refine HasSum.mul_left _ ?_
    have : HasSum (fun n => ∑ j ∈ Finset.range N, φ (n + j + 1) ^ 2)
        (∑ j ∈ Finset.range N, Sφ) := by
      refine hasSum_sum fun j _ => ?_
      have := hasSum_shift hφS ((j : ℤ) + 1)
      simpa [add_assoc] using this
    simpa using this
  have hrs : Summable fun n => r n ^ 2 :=
    Summable.of_nonneg_of_le (fun n => sq_nonneg _) hrsq hsumN.summable
  set R := ∑' n, r n ^ 2
  have hR : HasSum (fun n => r n ^ 2) R := hrs.hasSum
  have hRle : R ≤ N * ((N : ℝ) * Sφ) := hasSum_le hrsq hR hsumN
  have hbig : HasSum (fun n => 4 * (a (n + N) + a (n - N) + D ^ 2 * r n ^ 2 + D ^ 2 * r (n - N) ^ 2))
      (4 * (S + S + D ^ 2 * R + D ^ 2 * R)) := by
    refine HasSum.mul_left _ (((hasSum_shift hS N).add ?_).add (hR.mul_left _) |>.add ?_)
    · simpa [sub_eq_add_neg] using hasSum_shift hS (-(N : ℤ))
    · have := (hasSum_shift hR (-(N : ℤ))).mul_left (D ^ 2)
      simpa [sub_eq_add_neg] using this
  have hpt2 : ∀ n, 9 * a n ≤ 4 * (a (n + N) + a (n - N) + D ^ 2 * r n ^ 2 + D ^ 2 * r (n - N) ^ 2) := by
    intro n
    have h := hpt n
    have h0 : 0 ≤ 3 * ‖vec ψ n‖ := by positivity
    have hsq := pow_le_pow_left₀ h0 h 2
    have := four_sq ‖vec ψ (n + N)‖ ‖vec ψ (n - N)‖ (D * r n) (D * r (n - N))
    simp only [a]; nlinarith
  have h9 : 9 * S ≤ 4 * (S + S + D ^ 2 * R + D ^ 2 * R) := hasSum_le hpt2 (hS.mul_left 9) hbig
  have hψS : ∑' n, ψ n ^ 2 ≤ S := by
    refine hψ.tsum_le_tsum (fun n => ?_) ha
    simp only [a]; rw [norm_vec_sq]; nlinarith [sq_nonneg (ψ (n + 1))]
  have hD2 : 0 ≤ D ^ 2 := sq_nonneg _
  have : D ^ 2 * R ≤ D ^ 2 * (N * ((N : ℝ) * Sφ)) := mul_le_mul_of_nonneg_left hRle hD2
  nlinarith

end estimate

/-! ### Johnson's theorem -/

section johnson

lemma ham_sub_apply (hf : Continuous f) (ω : X) (E : ℝ) (ψ : L2 ℤ) (n : ℤ) :
    (ham T f ω - algebraMap ℂ Op (E : ℂ)) ψ n =
      ψ (n + 1) + ψ (n - 1) + (pot T f ω n : ℂ) * ψ n - (E : ℂ) * ψ n := by
  rw [_root_.sub_apply, algebraMap_apply_L2'']
  simp only [lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, ham,
    schr_apply (bddPot hf ω)]

/-- `H_ω - E` is bounded below for `E ∈ 𝒰ℋ`, uniformly in `ω`. -/
theorem norm_sq_le_of_UH (hf : Continuous f) {E : ℝ} (hE : E ∈ UHset T f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ω : X) (ψ : L2 ℤ),
      ‖ψ‖ ^ 2 ≤ C * ‖(ham T f ω - algebraMap ℂ Op (E : ℂ)) ψ‖ ^ 2 := by
  obtain ⟨C, hC, hest⟩ := sq_le_of_UH hf hE
  refine ⟨C, hC, fun ω ψ => ?_⟩
  set φ := (ham T f ω - algebraMap ℂ Op (E : ℂ)) ψ
  have hsq : ∀ z : ℂ, ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := fun z => by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hre : ∀ u : L2 ℤ, Summable fun n => (u n).re ^ 2 := fun u =>
    Summable.of_nonneg_of_le (fun n => sq_nonneg _)
      (fun n => by rw [hsq]; nlinarith [sq_nonneg (u n).im]) (summable_norm_sq u)
  have him : ∀ u : L2 ℤ, Summable fun n => (u n).im ^ 2 := fun u =>
    Summable.of_nonneg_of_le (fun n => sq_nonneg _)
      (fun n => by rw [hsq]; nlinarith [sq_nonneg (u n).re]) (summable_norm_sq u)
  have hnorm : ∀ u : L2 ℤ, ‖u‖ ^ 2 = ∑' n, (u n).re ^ 2 + ∑' n, (u n).im ^ 2 := fun u => by
    rw [norm_sq_eq_tsum, ← (hre u).tsum_add (him u)]
    exact tsum_congr fun n => hsq _
  have hφre : ∀ n, (φ n).re = defect T f E ω (fun k => (ψ k).re) n := by
    intro n; simp only [φ, ham_sub_apply hf, defect]; simp
  have hφim : ∀ n, (φ n).im = defect T f E ω (fun k => (ψ k).im) n := by
    intro n; simp only [φ, ham_sub_apply hf, defect]; simp
  have h1 := hest ω (fun k => (ψ k).re) (hre ψ)
  have h2 := hest ω (fun k => (ψ k).im) (him ψ)
  rw [hnorm ψ, hnorm φ]
  simp only [hφre, hφim]
  nlinarith

lemma nontrivial_L2 : Nontrivial (L2 ℤ) := ⟨⟨dlt 0, 0, fun h => by
    have := congrArg (fun f : L2 ℤ => f 0) h; simp at this⟩⟩

/-- **Johnson's theorem, first inclusion**: if `(T, A_E)` is uniformly hyperbolic, then `E` lies
in the resolvent set of every `H_ω`. -/
theorem not_mem_spectrum_of_UH (hf : Continuous f) {E : ℝ} (hE : E ∈ UHset T f) (ω : X) :
    E ∉ spectrum ℝ (ham T f ω) := by
  have := nontrivial_L2
  obtain ⟨C, hC, hest⟩ := norm_sq_le_of_UH hf hE
  rw [ham, ← spectrum.algebraMap_mem_iff ℂ]
  intro hmem
  change ((E : ℂ)) ∈ spectrum ℂ (schr (pot T f ω)) at hmem
  set ε : ℝ := 1 / (C + 1)
  have hε : 0 < ε := by positivity
  obtain ⟨v, hv1, hv⟩ := exists_unit_norm_sub_lt (isSelfAdjoint_schr (bddPot (T := T) hf ω)) (E : ℂ) hε
  rw [infDist_zero_of_mem hmem, zero_add] at hv
  have h := hest ω v
  rw [hv1] at h
  have hsq : ‖(ham T f ω - algebraMap ℂ Op (E : ℂ)) v‖ ^ 2 < ε ^ 2 :=
    pow_lt_pow_left₀ hv (norm_nonneg _) two_ne_zero
  have hεC : C * ε ^ 2 < 1 := by
    have : C * ε < 1 := by
      simp only [ε]; rw [mul_one_div, div_lt_one (by positivity)]; linarith
    have hε1 : ε ≤ 1 := by
      simp only [ε]; rw [div_le_one (by positivity)]; linarith
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hsq.le hC]

/-- **Johnson's theorem, second inclusion**: if `(T, A_E)` is not uniformly hyperbolic, then `E`
belongs to the spectrum of some `H_ω`. -/
theorem mem_spectrum_of_not_UH (hf : Continuous f) {E : ℝ} (hE : E ∉ UHset T f) :
    ∃ ω : X, E ∈ spectrum ℝ (ham T f ω) := by
  have hb : BoundedOrbit T (schrCoc T f E) := by
    by_contra h
    exact hE (uniformExpGrowth_of_not_boundedOrbit T _ (continuous_schrCoc hf E) h)
  obtain ⟨ω, u, hu⟩ := genEig_of_boundedOrbit hb
  refine ⟨ω, ?_⟩
  rw [ham, ← spectrum.algebraMap_mem_iff ℂ]
  exact genEig_mem_spectrum (bddPot hf ω) zero_le_one hu

/-- **Theorem 4.9.3** (Johnson): `⋃_{ω ∈ Ω} σ(H_ω) = ℝ \ 𝒰ℋ`. -/
theorem johnson (hf : Continuous f) : (⋃ ω : X, spectrum ℝ (ham T f ω)) = (UHset T f)ᶜ := by
  ext E
  simp only [mem_iUnion, mem_compl_iff]
  constructor
  · rintro ⟨ω, hω⟩ hE; exact not_mem_spectrum_of_UH hf hE ω hω
  · exact mem_spectrum_of_not_UH hf

/-- Every `σ(H_ω)` is contained in `ℝ \ 𝒰ℋ`. -/
theorem spectrum_subset_compl_UH (hf : Continuous f) (ω : X) :
    spectrum ℝ (ham T f ω) ⊆ (UHset T f)ᶜ := fun _ hE hU => not_mem_spectrum_of_UH hf hU ω hE

end johnson

end Johnson

end DF
