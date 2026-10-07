/-
# Elementary pieces of the rational band geometry and of the corner oscillator models

Formalization of elementary algebraic/analytic steps from S. Becker,
"Self-dual perturbations of the critical almost Mathieu operator: Dry Ten Martini and
Hausdorff dimension" (`spectral_gaps_and_dimension.tex`):

* §1 (l.376): integer shift of the frequency changes Weyl coefficients by `(-1)^{krs}`.
* §2.2 (l.596–650): Rieffel projection functions `f_a`, `g_a`, their projection identities
  and `∫₀¹ f_a = a`.
* §2.3, proof of Prop. `dim:prop:corners` (l.1453–1486, l.1670–1689): the phase contraction
  argument for `f_E` with `‖f_E'‖ ≤ 1/2`, Jordan's inequality, and nondegeneracy of the
  Hessian at a corner.
* §2.4 (l.1953–2010, l.2020–2040, l.2131–2147): band length lower bound by the mean value
  theorem, the Pauli/Dirac determinant, and the determinant–distance estimate
  `gap:eq:det-distance`.
* §5.2 (l.6150–6510): the Dirac square identity, the 2×2 ladder blocks
  `gap:eq:pair-levels`, the pair spacings `gap:eq:pair-spacing`, the polynomial division
  identity (l.6278) and the scalar inequality (l.6502).
-/
import Mathlib

noncomputable section

open Real

namespace SGD

namespace CornerGeometry

/-! ## Distance to `πℤ` and the phase contraction (Prop. `dim:prop:corners`) -/

/-- The distance `d(t) = dist(t, πℤ)` used in the proof of Prop. `dim:prop:corners`
(l.1460, l.1670), realized by the nearest multiple `round (t/π) · π`. -/
def distPiZ (t : ℝ) : ℝ := |t - round (t / π) * π|

lemma distPiZ_eq (t : ℝ) : distPiZ t = π * |t / π - round (t / π)| := by
  have hπ := Real.pi_pos
  have e : t - round (t / π) * π = π * (t / π - round (t / π)) := by
    field_simp
  rw [distPiZ, e, abs_mul, abs_of_pos hπ]

/-- `d(t)` is at most the distance to any multiple `kπ`, `k ∈ ℤ` (so `d(t) = dist(t, πℤ)`). -/
lemma distPiZ_le (t : ℝ) (k : ℤ) : distPiZ t ≤ |t - k * π| := by
  have hπ := Real.pi_pos
  have e : t - k * π = π * (t / π - k) := by field_simp
  rw [distPiZ_eq, e, abs_mul, abs_of_pos hπ]
  exact mul_le_mul_of_nonneg_left (round_le (t / π) k) hπ.le

lemma distPiZ_nonneg (t : ℝ) : 0 ≤ distPiZ t := abs_nonneg _

/-- `d(t) ≤ π/2`. -/
lemma distPiZ_le_pi_div_two (t : ℝ) : distPiZ t ≤ π / 2 := by
  rw [distPiZ_eq]
  have := abs_sub_round (t / π)
  have hπ := Real.pi_pos
  nlinarith

/-- `d(t) = 0` iff `t ∈ πℤ`. -/
lemma distPiZ_eq_zero_iff (t : ℝ) : distPiZ t = 0 ↔ ∃ k : ℤ, t = k * π := by
  constructor
  · intro h
    exact ⟨round (t / π), by rw [distPiZ, abs_eq_zero, sub_eq_zero] at h; exact h⟩
  · rintro ⟨k, hk⟩
    refine le_antisymm ?_ (distPiZ_nonneg t)
    simpa [hk] using distPiZ_le t k

lemma distPiZ_neg (t : ℝ) : distPiZ (-t) = distPiZ t := by
  apply le_antisymm
  · have := distPiZ_le (-t) (-round (t / π))
    rw [distPiZ]
    calc distPiZ (-t) ≤ |-t - ((-round (t / π) : ℤ) : ℝ) * π| := this
      _ = |t - round (t / π) * π| := by
        rw [← abs_neg]; push_cast; ring_nf
  · have := distPiZ_le t (-round (-t / π))
    calc distPiZ t ≤ |t - ((-round (-t / π) : ℤ) : ℝ) * π| := this
      _ = distPiZ (-t) := by
        rw [distPiZ, ← abs_neg]; push_cast; ring_nf

/-- Triangle inequality for `d`: `d(x) ≤ d(x + y) + |y|`. -/
lemma distPiZ_le_add (x y : ℝ) : distPiZ x ≤ distPiZ (x + y) + |y| := by
  calc distPiZ x ≤ |x - round ((x + y) / π) * π| := distPiZ_le x _
    _ = |(x + y - round ((x + y) / π) * π) - y| := by ring_nf
    _ ≤ |x + y - round ((x + y) / π) * π| + |y| := abs_sub _ _
    _ = distPiZ (x + y) + |y| := rfl

/-- **Prop. `dim:prop:corners`, proof (l.1430–1437, 1670–1676).** If `f` is `1/2`-Lipschitz
(the bound `‖f_E'‖_∞ ≤ 1/2`, `dim:rat:argument-contraction`) and vanishes on `πℤ`
(`f_E(0) = f_E(π) = 0`, together with `π`-periodicity), then `|f(t)| ≤ d(t)/2`. -/
lemma abs_le_half_distPiZ {f : ℝ → ℝ} (hf : ∀ x y, |f x - f y| ≤ |x - y| / 2)
    (h0 : ∀ k : ℤ, f (k * π) = 0) (t : ℝ) : |f t| ≤ distPiZ t / 2 := by
  have := hf t (round (t / π) * π)
  rwa [h0, sub_zero] at this

/-- The Lipschitz hypothesis used above follows from `LipschitzWith (1/2) f`. -/
lemma lipschitz_half_iff {f : ℝ → ℝ} (hf : LipschitzWith (1 / 2) f) (x y : ℝ) :
    |f x - f y| ≤ |x - y| / 2 := by
  have := hf.dist_le_mul x y
  simp only [Real.dist_eq] at this
  have h2 : (((1 / 2 : NNReal)) : ℝ) = 1 / 2 := by norm_num
  rw [h2] at this
  linarith

/-- **Prop. `dim:prop:corners`, proof (l.1674–1676).** The two one-sided contraction
inequalities `d_θ ≤ e₁ + d_φ/2` and `d_φ ≤ e₂ + d_θ/2`, where
`e₁ = d(θ + f(φ))` and `e₂ = d(-φ + f(θ))`. -/
lemma phase_contraction_steps {f : ℝ → ℝ} (hf : ∀ x y, |f x - f y| ≤ |x - y| / 2)
    (h0 : ∀ k : ℤ, f (k * π) = 0) (θ φ : ℝ) :
    distPiZ θ ≤ distPiZ (θ + f φ) + distPiZ φ / 2 ∧
      distPiZ φ ≤ distPiZ (-φ + f θ) + distPiZ θ / 2 := by
  constructor
  · have h1 := distPiZ_le_add θ (f φ)
    have h2 := abs_le_half_distPiZ hf h0 φ
    linarith
  · have h1 := distPiZ_le_add (-φ) (f θ)
    have h2 := abs_le_half_distPiZ hf h0 θ
    rw [distPiZ_neg] at h1
    linarith

/-- **Prop. `dim:prop:corners`, proof (l.1674–1678), quantitative contraction.**
`max(d_θ, d_φ) ≤ 2 max(e₁, e₂)`, with the paper's constant `2`. -/
theorem phase_contraction {f : ℝ → ℝ} (hf : ∀ x y, |f x - f y| ≤ |x - y| / 2)
    (h0 : ∀ k : ℤ, f (k * π) = 0) (θ φ : ℝ) :
    max (distPiZ θ) (distPiZ φ) ≤
      2 * max (distPiZ (θ + f φ)) (distPiZ (-φ + f θ)) := by
  obtain ⟨h1, h2⟩ := phase_contraction_steps hf h0 θ φ
  have m1 := le_max_left (distPiZ (θ + f φ)) (distPiZ (-φ + f θ))
  have m2 := le_max_right (distPiZ (θ + f φ)) (distPiZ (-φ + f θ))
  apply max_le <;> linarith

/-- **Prop. `dim:prop:corners`, proof (l.1458–1461).** If `θ + f(φ) ∈ πℤ` and
`-φ + f(θ) ∈ πℤ`, then `θ, φ ∈ πℤ` (both phases are corners). -/
theorem phase_contraction_exact {f : ℝ → ℝ} (hf : ∀ x y, |f x - f y| ≤ |x - y| / 2)
    (h0 : ∀ k : ℤ, f (k * π) = 0) {θ φ : ℝ}
    (h1 : ∃ k : ℤ, θ + f φ = k * π) (h2 : ∃ k : ℤ, -φ + f θ = k * π) :
    (∃ k : ℤ, θ = k * π) ∧ ∃ k : ℤ, φ = k * π := by
  have e1 := (distPiZ_eq_zero_iff _).2 h1
  have e2 := (distPiZ_eq_zero_iff _).2 h2
  have h := phase_contraction hf h0 θ φ
  rw [e1, e2, max_self, mul_zero] at h
  have hθ := distPiZ_nonneg θ
  have hφ := distPiZ_nonneg φ
  have a1 := le_max_left (distPiZ θ) (distPiZ φ)
  have a2 := le_max_right (distPiZ θ) (distPiZ φ)
  exact ⟨(distPiZ_eq_zero_iff θ).1 (by linarith), (distPiZ_eq_zero_iff φ).1 (by linarith)⟩

/-- **Jordan's inequality (l.1679):** `|sin t| ≥ (2/π) dist(t, πℤ)`. -/
theorem two_div_pi_mul_distPiZ_le_abs_sin (t : ℝ) : 2 / π * distPiZ t ≤ |sin t| := by
  have hπ := Real.pi_pos
  set k := round (t / π)
  set s := t - k * π with hs
  have hsin : |sin s| = |sin t| := by
    rw [hs, Real.sin_sub_int_mul_pi, abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul]
  have hd : distPiZ t = |s| := rfl
  have hle : |s| ≤ π / 2 := hd ▸ distPiZ_le_pi_div_two t
  rw [hd, ← hsin]
  rcases le_total 0 s with h | h
  · rw [abs_of_nonneg h]
    have := Real.mul_le_sin h (by rwa [abs_of_nonneg h] at hle)
    exact this.trans (le_abs_self _)
  · rw [abs_of_nonpos h]
    have := Real.mul_le_sin (x := -s) (by linarith) (by rwa [abs_of_nonpos h] at hle)
    rw [Real.sin_neg] at this
    exact this.trans (neg_le_abs _)

/-! ## Hessian nondegeneracy at a corner -/

/-- **Prop. `dim:prop:corners`, proof (l.1475–1486).** If `b = a f'(φ)` and
`b = -d f'(θ)` (here `α = f'(φ)`, `β = f'(θ)`) with `|f'| ≤ 1/2` and `a, d ≠ 0`, then
`ad - b² = ad(1 + f'(φ) f'(θ)) ≠ 0`. -/
theorem hessian_det {a b d α β : ℝ} (hb1 : b = a * α) (hb2 : b = -d * β)
    (hα : |α| ≤ 1 / 2) (hβ : |β| ≤ 1 / 2) (ha : a ≠ 0) (hd : d ≠ 0) :
    a * d - b ^ 2 = a * d * (1 + α * β) ∧ a * d - b ^ 2 ≠ 0 := by
  have key : a * d - b ^ 2 = a * d * (1 + α * β) := by
    linear_combination (-b) * hb1 + (-a * α) * hb2
  refine ⟨key, ?_⟩
  rw [key]
  have hab : |α * β| ≤ 1 / 4 := by
    rw [abs_mul]; nlinarith [abs_nonneg α, abs_nonneg β]
  have : -(1 / 4) ≤ α * β := by have := neg_abs_le (α * β); linarith
  exact mul_ne_zero (mul_ne_zero ha hd) (by linarith)

/-! ## Rieffel projection functions (l.596–650) -/

/-- The function `f_a` on `[0, 1]` (l.620–628). -/
def rieffelF0 (a ε : ℝ) (r : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x ≤ ε then r x else if x ≤ a then 1 else if x ≤ a + ε then 1 - r (x - a) else 0

/-- The periodic function `f_a(x)` (l.620), defined via `Int.fract`. -/
def rieffelF (a ε : ℝ) (r : ℝ → ℝ) (x : ℝ) : ℝ := rieffelF0 a ε r (Int.fract x)

/-- The periodic function `g_a(x)` (l.627–630). -/
def rieffelG (a ε : ℝ) (r : ℝ → ℝ) (x : ℝ) : ℝ :=
  if a ≤ Int.fract x ∧ Int.fract x ≤ a + ε then
    √(rieffelF a ε r x * (1 - rieffelF a ε r x)) else 0

/-- Hypotheses of l.613–617: `0 < ε < min(a, 1-a)`, `r : [0, ε] → [0, 1]` continuous with
`r 0 = 0`, `r ε = 1`. -/
structure RieffelData (a ε : ℝ) (r : ℝ → ℝ) : Prop where
  ε_pos : 0 < ε
  ε_lt_a : ε < a
  ε_lt_one_sub : ε < 1 - a
  cont : ContinuousOn r (Set.Icc 0 ε)
  r_zero : r 0 = 0
  r_eps : r ε = 1
  r_mem : ∀ x ∈ Set.Icc 0 ε, 0 ≤ r x ∧ r x ≤ 1

namespace RieffelData

variable {a ε : ℝ} {r : ℝ → ℝ} (h : RieffelData a ε r)
include h

set_option linter.unusedSectionVars false in
lemma F0_first {y : ℝ} (hy : y ≤ ε) : rieffelF0 a ε r y = r y := by
  simp [rieffelF0, hy]

lemma F0_second {y : ℝ} (hy1 : ε ≤ y) (hy2 : y ≤ a) : rieffelF0 a ε r y = 1 := by
  rcases eq_or_lt_of_le hy1 with e | lt
  · subst e; simp [rieffelF0, h.r_eps]
  · simp [rieffelF0, not_le.2 lt, hy2]

lemma F0_third {y : ℝ} (hy1 : a ≤ y) (hy2 : y ≤ a + ε) :
    rieffelF0 a ε r y = 1 - r (y - a) := by
  have h1 : ¬ y ≤ ε := not_le.2 (lt_of_lt_of_le h.ε_lt_a hy1)
  rcases eq_or_lt_of_le hy1 with e | lt
  · subst e; simp [rieffelF0, h1, h.r_zero]
  · simp [rieffelF0, h1, not_le.2 lt, hy2]

lemma F0_fourth {y : ℝ} (hy : a + ε ≤ y) : rieffelF0 a ε r y = 0 := by
  have h1 : ¬ y ≤ ε := by have := h.ε_pos; have := h.ε_lt_a; intro c; linarith
  have h2 : ¬ y ≤ a := by have := h.ε_pos; intro c; linarith
  rcases eq_or_lt_of_le hy with e | lt
  · subst e; simp [rieffelF0, h1, h2, h.r_eps]
  · simp [rieffelF0, h1, h2, not_le.2 lt]

lemma fract_sub {x : ℝ} (hx : a ≤ Int.fract x) : Int.fract (x - a) = Int.fract x - a := by
  have := h.ε_pos; have := h.ε_lt_a
  rw [Int.fract_eq_iff]
  refine ⟨by linarith, by linarith [Int.fract_lt_one x], ⌊x⌋, ?_⟩
  rw [← Int.self_sub_fract]; ring

lemma fract_add_lt {x : ℝ} (hx : Int.fract x + a < 1) : Int.fract (x + a) = Int.fract x + a := by
  have := h.ε_pos; have := h.ε_lt_a
  rw [Int.fract_eq_iff]
  refine ⟨by linarith [Int.fract_nonneg x], hx, ⌊x⌋, ?_⟩
  rw [← Int.self_sub_fract]; ring

lemma fract_add_ge {x : ℝ} (hx : 1 ≤ Int.fract x + a) :
    Int.fract (x + a) = Int.fract x + a - 1 := by
  have := h.ε_pos; have := h.ε_lt_one_sub
  rw [Int.fract_eq_iff]
  refine ⟨by linarith, by linarith [Int.fract_lt_one x], ⌊x⌋ + 1, ?_⟩
  push_cast
  rw [← Int.self_sub_fract]; ring

set_option linter.unusedSectionVars false in
lemma G_of_not {x : ℝ} (hx : ¬ (a ≤ Int.fract x ∧ Int.fract x ≤ a + ε)) :
    rieffelG a ε r x = 0 := by
  simp only [rieffelG, hx, ↓reduceIte]

lemma G_add_eq_zero {x : ℝ} (hx : ε < Int.fract x) : rieffelG a ε r (x + a) = 0 := by
  apply h.G_of_not
  have := h.ε_lt_a
  rintro ⟨h1, h2⟩
  rcases lt_or_ge (Int.fract x + a) 1 with c | c
  · rw [h.fract_add_lt c] at h2; linarith
  · rw [h.fract_add_ge c] at h1; linarith [Int.fract_lt_one x]

/-- **Rieffel identity (l.635):** `g_a(x) g_a(x - a) = 0`. -/
theorem g_mul_g_sub (x : ℝ) : rieffelG a ε r x * rieffelG a ε r (x - a) = 0 := by
  by_cases hx : a ≤ Int.fract x ∧ Int.fract x ≤ a + ε
  · have := h.ε_lt_a
    have h0 : rieffelG a ε r (x - a) = 0 := by
      apply h.G_of_not
      rw [h.fract_sub hx.1]
      rintro ⟨h1, h2⟩
      linarith [hx.2]
    rw [h0, mul_zero]
  · rw [h.G_of_not hx, zero_mul]

/-- **Rieffel identity (l.635):** `g_a(x) (1 - f_a(x) - f_a(x - a)) = 0`. -/
theorem g_mul_one_sub (x : ℝ) :
    rieffelG a ε r x * (1 - rieffelF a ε r x - rieffelF a ε r (x - a)) = 0 := by
  by_cases hx : a ≤ Int.fract x ∧ Int.fract x ≤ a + ε
  · have e1 : rieffelF a ε r x = 1 - r (Int.fract x - a) := h.F0_third hx.1 hx.2
    have e2 : rieffelF a ε r (x - a) = r (Int.fract x - a) := by
      rw [rieffelF, h.fract_sub hx.1]
      exact h.F0_first (by linarith [hx.2])
    rw [e1, e2]; ring
  · rw [h.G_of_not hx, zero_mul]

/-- **Rieffel identity (l.636):** `f_a(x)(1 - f_a(x)) = g_a(x)² + g_a(x + a)²`. -/
theorem f_mul_one_sub (x : ℝ) :
    rieffelF a ε r x * (1 - rieffelF a ε r x) =
      rieffelG a ε r x ^ 2 + rieffelG a ε r (x + a) ^ 2 := by
  have hε := h.ε_pos; have hεa := h.ε_lt_a; have hεb := h.ε_lt_one_sub
  have y0 := Int.fract_nonneg x
  have y1 := Int.fract_lt_one x
  set y := Int.fract x with hy
  by_cases hx : a ≤ y ∧ y ≤ a + ε
  · -- third piece
    have hG2 := h.G_add_eq_zero (x := x) (by linarith [hx.1])
    have e1 : rieffelF a ε r x = 1 - r (y - a) := h.F0_third hx.1 hx.2
    have hm := h.r_mem (y - a) ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hG : rieffelG a ε r x = √(rieffelF a ε r x * (1 - rieffelF a ε r x)) := by
      simp only [rieffelG, ← hy, hx, and_self, ↓reduceIte]
    rw [hG2, hG, Real.sq_sqrt (by rw [e1]; nlinarith)]
    ring
  · rw [h.G_of_not hx]
    by_cases hy1 : y ≤ ε
    · -- first piece
      have hfa : Int.fract (x + a) = y + a := h.fract_add_lt (by linarith)
      have hin : a ≤ Int.fract (x + a) ∧ Int.fract (x + a) ≤ a + ε := by
        rw [hfa]; constructor <;> linarith
      have e1 : rieffelF a ε r x = r y := h.F0_first hy1
      have e2 : rieffelF a ε r (x + a) = 1 - r y := by
        rw [rieffelF, hfa, h.F0_third (by linarith) (by linarith)]; ring_nf
      have hm := h.r_mem y ⟨y0, hy1⟩
      have hG : rieffelG a ε r (x + a) =
          √(rieffelF a ε r (x + a) * (1 - rieffelF a ε r (x + a))) := by
        simp only [rieffelG, hin, and_self, ↓reduceIte]
      rw [hG, Real.sq_sqrt (by rw [e2]; nlinarith), e1, e2]
      ring
    · replace hy1 := not_le.1 hy1
      rw [h.G_add_eq_zero hy1]
      have : rieffelF a ε r x = 1 ∨ rieffelF a ε r x = 0 := by
        by_cases hya : y ≤ a
        · exact Or.inl (h.F0_second hy1.le hya)
        · replace hya := not_le.1 hya
          have : a + ε < y := by
            by_contra c; exact hx ⟨hya.le, not_lt.1 c⟩
          exact Or.inr (h.F0_fourth this.le)
      rcases this with e | e <;> rw [e] <;> ring

lemma F_eqOn : Set.EqOn (rieffelF a ε r) (rieffelF0 a ε r) (Set.uIcc 0 1) := by
  intro x hx
  rw [Set.uIcc_of_le zero_le_one] at hx
  rcases eq_or_lt_of_le hx.2 with e | lt
  · subst e
    have := h.ε_lt_one_sub
    rw [rieffelF, Int.fract_one, h.F0_first h.ε_pos.le, h.r_zero,
      h.F0_fourth (by linarith)]
  · rw [rieffelF, Int.fract_eq_self.2 ⟨hx.1, lt⟩]

/-- **Trace of the Rieffel projection (l.645):** `∫₀¹ f_a(x) dx = a`. -/
theorem integral_f : ∫ x in (0 : ℝ)..1, rieffelF a ε r x = a := by
  have hε := h.ε_pos; have hεa := h.ε_lt_a; have hεb := h.ε_lt_one_sub
  rw [intervalIntegral.integral_congr h.F_eqOn]
  -- continuity on each of the four pieces
  have c1 : ContinuousOn (rieffelF0 a ε r) (Set.uIcc 0 ε) := by
    rw [Set.uIcc_of_le hε.le]
    exact h.cont.congr (fun y hy => h.F0_first hy.2)
  have c2 : ContinuousOn (rieffelF0 a ε r) (Set.uIcc ε a) := by
    rw [Set.uIcc_of_le hεa.le]
    exact continuousOn_const.congr (fun y hy => h.F0_second hy.1 hy.2)
  have hcomp : ContinuousOn (fun y => 1 - r (y - a)) (Set.Icc a (a + ε)) := by
    refine continuousOn_const.sub (h.cont.comp (continuousOn_id.sub continuousOn_const) ?_)
    intro y hy; simp only [Set.mem_Icc] at hy ⊢; constructor <;> linarith [hy.1, hy.2]
  have c3 : ContinuousOn (rieffelF0 a ε r) (Set.uIcc a (a + ε)) := by
    rw [Set.uIcc_of_le (by linarith)]
    exact hcomp.congr (fun y hy => h.F0_third hy.1 hy.2)
  have c4 : ContinuousOn (rieffelF0 a ε r) (Set.uIcc (a + ε) 1) := by
    rw [Set.uIcc_of_le (by linarith)]
    exact continuousOn_const.congr (fun y hy => h.F0_fourth hy.1)
  rw [← intervalIntegral.integral_add_adjacent_intervals c1.intervalIntegrable
      ((c2.intervalIntegrable).trans (c3.intervalIntegrable.trans c4.intervalIntegrable)),
    ← intervalIntegral.integral_add_adjacent_intervals c2.intervalIntegrable
      (c3.intervalIntegrable.trans c4.intervalIntegrable),
    ← intervalIntegral.integral_add_adjacent_intervals c3.intervalIntegrable
      c4.intervalIntegrable]
  have i1 : ∫ x in (0 : ℝ)..ε, rieffelF0 a ε r x = ∫ x in (0 : ℝ)..ε, r x := by
    apply intervalIntegral.integral_congr
    intro y hy; rw [Set.uIcc_of_le hε.le] at hy; exact h.F0_first hy.2
  have i2 : ∫ x in ε..a, rieffelF0 a ε r x = a - ε := by
    rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ))]
    · simp
    · intro y hy; rw [Set.uIcc_of_le hεa.le] at hy; exact h.F0_second hy.1 hy.2
  have hr : IntervalIntegrable r MeasureTheory.volume 0 ε := by
    apply ContinuousOn.intervalIntegrable; rw [Set.uIcc_of_le hε.le]; exact h.cont
  have i3 : ∫ x in a..a + ε, rieffelF0 a ε r x = ε - ∫ x in (0 : ℝ)..ε, r x := by
    rw [intervalIntegral.integral_congr (g := fun y => 1 - r (y - a))]
    · rw [intervalIntegral.integral_comp_sub_right (fun y => 1 - r y) a]
      simp only [sub_self, add_sub_cancel_left]
      rw [intervalIntegral.integral_sub intervalIntegrable_const hr]
      simp
    · intro y hy; rw [Set.uIcc_of_le (by linarith)] at hy; exact h.F0_third hy.1 hy.2
  have i4 : ∫ x in a + ε..1, rieffelF0 a ε r x = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))]
    · simp
    · intro y hy; rw [Set.uIcc_of_le (by linarith)] at hy; exact h.F0_fourth hy.1
  rw [i1, i2, i3, i4]
  ring

end RieffelData

/-! ## Dirac operators and Pauli matrices (§2.4, §5.2) -/

section Pauli

variable {A : Type*} [Ring A] [Algebra ℂ A]

/-- Pauli matrix `σ₁` (l.2023) with entries in a `ℂ`-algebra. -/
def σ₁ : Matrix (Fin 2) (Fin 2) A := !![0, 1; 1, 0]
/-- Pauli matrix `σ₂` (l.2024). -/
def σ₂ : Matrix (Fin 2) (Fin 2) A :=
  !![0, -(algebraMap ℂ A Complex.I); algebraMap ℂ A Complex.I, 0]
/-- Pauli matrix `σ₃` (l.2025). -/
def σ₃ : Matrix (Fin 2) (Fin 2) A := !![1, 0; 0, -1]

/-- The Dirac model `D = d σ₃ + v (x σ₁ + χ p σ₂)` of `gap:eq:effective-pair` (l.6051),
with `x, p` elements of a (noncommutative) `ℂ`-algebra acting diagonally on spinors. -/
def dirac (d v χ : ℂ) (x p : A) : Matrix (Fin 2) (Fin 2) A :=
  d • σ₃ + v • (Matrix.scalar (Fin 2) x * σ₁ + χ • (Matrix.scalar (Fin 2) p * σ₂))

/-- **Dirac square identity (l.6085, l.6193).** If `xp - px = iħ` and `χ² = 1`, then
`D² = d² I + v² ((x² + p²) I - χ ħ σ₃)`. -/
theorem dirac_sq (d v χ ħ : ℂ) (x p : A) (hxp : x * p - p * x = (Complex.I * ħ) • (1 : A))
    (hχ : χ ^ 2 = 1) :
    dirac d v χ x p * dirac d v χ x p =
      (d ^ 2) • (1 : Matrix (Fin 2) (Fin 2) A) +
        v ^ 2 • (Matrix.scalar (Fin 2) (x * x + p * p) - (χ * ħ) • σ₃) := by
  have hxp' : x * p = p * x + (Complex.I * ħ) • (1 : A) := by rw [← hxp]; abel
  have hD : dirac d v χ x p = !![d • (1 : A), v • x - (v * χ * Complex.I) • p;
      v • x + (v * χ * Complex.I) • p, -(d • (1 : A))] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [dirac, σ₁, σ₂, σ₃, Algebra.algebraMap_eq_smul_one]
    all_goals module
  have hR : (d ^ 2) • (1 : Matrix (Fin 2) (Fin 2) A) +
        v ^ 2 • (Matrix.scalar (Fin 2) (x * x + p * p) - (χ * ħ) • σ₃) =
      !![d ^ 2 • (1 : A) + v ^ 2 • (x * x + p * p - (χ * ħ) • 1), 0;
        0, d ^ 2 • (1 : A) + v ^ 2 • (x * x + p * p + (χ * ħ) • 1)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [σ₃]
  rw [hD, hR, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one,
      Fin.isValue] <;>
    simp only [mul_add, add_mul, mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, smul_smul,
      one_mul, mul_one, mul_neg, neg_mul, smul_add, smul_sub, smul_neg, hxp'] <;>
    match_scalars <;> ring_nf <;> simp only [Complex.I_sq, hχ] <;> ring_nf

/-- **Pauli/Dirac determinant (l.1984, l.2035).** For real `d, v, k₁, k₂` and `ε = ±1`,
`det(d σ₃ + v (k₁ σ₁ + ε k₂ σ₂)) = -(d² + v² (k₁² + k₂²))`. -/
theorem det_dirac_block (d v k₁ k₂ ε : ℝ) (hε : ε ^ 2 = 1) :
    ((d : ℂ) • (σ₃ : Matrix (Fin 2) (Fin 2) ℂ) +
        (v : ℂ) • ((k₁ : ℂ) • σ₁ + ((ε * k₂ : ℝ) : ℂ) • σ₂)).det =
      -((d : ℂ) ^ 2 + (v : ℂ) ^ 2 * ((k₁ : ℂ) ^ 2 + (k₂ : ℂ) ^ 2)) := by
  have hε' : (ε : ℂ) ^ 2 = 1 := by exact_mod_cast hε
  rw [Matrix.det_fin_two]
  simp [σ₁, σ₂, σ₃]
  linear_combination (-(v : ℂ) ^ 2 * (k₂ : ℂ) ^ 2) * hε' + ((v : ℂ) ^ 2 * (ε : ℂ) ^ 2 * (k₂ : ℂ) ^ 2) * Complex.I_sq

/-! ## Ladder blocks and pair levels (`gap:eq:pair-levels`) -/

/-- The pair level `√(d² + 2v²ħn)` of `gap:eq:pair-levels` (l.6163). -/
def pairLevel (d v ħ : ℝ) (n : ℕ) : ℝ := √(d ^ 2 + 2 * v ^ 2 * ħ * n)

/-- The invariant 2×2 block of `D` on a pair of consecutive Hermite states (l.6193–6196):
`!![d, v√(2ħn); v√(2ħn), -d]`. -/
def ladderBlock (d v ħ : ℝ) (n : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![d, v * √(2 * ħ * n); v * √(2 * ħ * n), -d]

/-- Characteristic polynomial of the ladder block: `det(B - λ) = λ² - (d² + 2v²ħn)`. -/
theorem det_ladderBlock_sub (d v ħ : ℝ) (hħ : 0 ≤ ħ) (n : ℕ) (μ : ℝ) :
    (ladderBlock d v ħ n - μ • (1 : Matrix (Fin 2) (Fin 2) ℝ)).det =
      μ ^ 2 - (d ^ 2 + 2 * v ^ 2 * ħ * n) := by
  have h2 : √(2 * ħ * n) ^ 2 = 2 * ħ * n := Real.sq_sqrt (by positivity)
  have hB : ladderBlock d v ħ n - μ • (1 : Matrix (Fin 2) (Fin 2) ℝ) =
      !![d - μ, v * √(2 * ħ * n); v * √(2 * ħ * n), -d - μ] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ladderBlock]
  rw [hB, Matrix.det_fin_two_of]
  linear_combination (-v ^ 2) * h2

/-- **`gap:eq:pair-levels` (l.6161–6164, 6193–6196).** The ladder block has eigenvalues exactly
`±√(d² + 2v²ħn)`. -/
theorem ladderBlock_eigenvalues (d v ħ : ℝ) (hħ : 0 ≤ ħ) (n : ℕ) (μ : ℝ) :
    (ladderBlock d v ħ n - μ • (1 : Matrix (Fin 2) (Fin 2) ℝ)).det = 0 ↔
      μ = pairLevel d v ħ n ∨ μ = -pairLevel d v ħ n := by
  rw [det_ladderBlock_sub d v ħ hħ n μ, sub_eq_zero, pairLevel,
    ← Real.sq_sqrt (by positivity : (0 : ℝ) ≤ d ^ 2 + 2 * v ^ 2 * ħ * n), sq_eq_sq_iff_eq_or_eq_neg,
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ d ^ 2 + 2 * v ^ 2 * ħ * n)]

/-- **`gap:eq:edge-levels` (l.6169–6172).** Consecutive edge levels
`E_* + ħβ₀ + εκ(2n+1)ħ` are spaced by `2εκħ` (so `γ_E = 2κħ`, l.6201). -/
theorem edge_level_spacing (Estar ħ β₀ ε κ : ℝ) (n : ℕ) :
    (Estar + ħ * β₀ + ε * κ * (2 * ((n + 1 : ℕ) : ℝ) + 1) * ħ) -
      (Estar + ħ * β₀ + ε * κ * (2 * (n : ℝ) + 1) * ħ) = 2 * ε * κ * ħ := by
  push_cast; ring

/-! ## Spacings and elementary inequalities (l.6197–6201, 6278, 6502) -/

lemma pairLevel_pos (d v ħ : ℝ) (hv : v ≠ 0) (hħ : 0 < ħ) (n : ℕ) :
    0 < pairLevel d v ħ (n + 1) := by
  apply Real.sqrt_pos.2
  have : 0 < v ^ 2 := by positivity
  have : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  positivity

/-- **Pair spacing (l.6197–6201).** `√(d²+2v²ħ(n+1)) - √(d²+2v²ħn)
= 2v²ħ / (√(d²+2v²ħ(n+1)) + √(d²+2v²ħn))`. -/
theorem pairLevel_succ_sub (d v ħ : ℝ) (hv : v ≠ 0) (hħ : 0 < ħ) (n : ℕ) :
    pairLevel d v ħ (n + 1) - pairLevel d v ħ n =
      2 * v ^ 2 * ħ / (pairLevel d v ħ (n + 1) + pairLevel d v ħ n) := by
  have h1 := pairLevel_pos d v ħ hv hħ n
  have h0 : 0 ≤ pairLevel d v ħ n := Real.sqrt_nonneg _
  rw [eq_div_iff (by linarith)]
  have s1 : pairLevel d v ħ (n + 1) ^ 2 = d ^ 2 + 2 * v ^ 2 * ħ * ((n + 1 : ℕ) : ℝ) :=
    Real.sq_sqrt (by positivity)
  have s0 : pairLevel d v ħ n ^ 2 = d ^ 2 + 2 * v ^ 2 * ħ * n := Real.sq_sqrt (by positivity)
  push_cast at s1
  linear_combination s1 - s0

/-- **`gap:eq:pair-spacing` (l.6197–6200), with constant `c = 1`.** For `v, ħ > 0`,
`√(d²+2v²ħ(n+1)) - √(d²+2v²ħn) ≥ v²ħ / (|d| + v√(2ħ(n+1)))`. -/
theorem pairLevel_spacing_ge (d v ħ : ℝ) (hv : 0 < v) (hħ : 0 < ħ) (n : ℕ) :
    v ^ 2 * ħ / (|d| + v * √(2 * ħ * ((n + 1 : ℕ) : ℝ))) ≤
      pairLevel d v ħ (n + 1) - pairLevel d v ħ n := by
  have h1 := pairLevel_pos d v ħ hv.ne' hħ n
  have h0 : 0 ≤ pairLevel d v ħ n := Real.sqrt_nonneg _
  set w := v * √(2 * ħ * ((n + 1 : ℕ) : ℝ)) with hw
  have hw0 : 0 ≤ w := mul_nonneg hv.le (Real.sqrt_nonneg _)
  have hw2 : w ^ 2 = v ^ 2 * (2 * ħ * ((n + 1 : ℕ) : ℝ)) := by
    rw [hw, mul_pow, Real.sq_sqrt (by positivity)]
  have hup : pairLevel d v ħ (n + 1) ≤ |d| + w := by
    rw [pairLevel, Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have := sq_abs d
    nlinarith [abs_nonneg d]
  have hmono : pairLevel d v ħ n ≤ pairLevel d v ħ (n + 1) := by
    apply Real.sqrt_le_sqrt
    have : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by push_cast; linarith
    have : 0 ≤ v ^ 2 * ħ := by positivity
    nlinarith
  rw [pairLevel_succ_sub d v ħ hv.ne' hħ n]
  have hdw : 0 < |d| + w := by linarith
  rw [div_le_div_iff₀ hdw (by linarith)]
  have : 0 ≤ v ^ 2 * ħ := by positivity
  nlinarith

/-- **`gap:eq:pair-spacing` for the unpaired level (l.6196–6200).** For `v, ħ > 0`,
`√(d²+2v²ħ) - |d| ≥ v²ħ / (|d| + v√(2ħ))`. -/
theorem first_pair_spacing_ge (d v ħ : ℝ) (hv : 0 < v) (hħ : 0 < ħ) :
    v ^ 2 * ħ / (|d| + v * √(2 * ħ)) ≤ √(d ^ 2 + 2 * v ^ 2 * ħ) - |d| := by
  have := pairLevel_spacing_ge d v ħ hv hħ 0
  simpa [pairLevel, Real.sqrt_sq_eq_abs] using this

/-- **Polynomial division (l.6276–6279).** In any `R`-algebra,
`(X + ħ)² = (X - ζ)(X + ζ + 2ħ) + (ζ + ħ)²`, which gives
`(H+ħ)²(H-ζ)⁻¹ = H + ζ + 2ħ + (ζ+ħ)²(H-ζ)⁻¹`. -/
theorem poly_division {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (X : A) (ζ ħ : R) :
    (X + algebraMap R A ħ) ^ 2 =
      (X - algebraMap R A ζ) * (X + algebraMap R A ζ + 2 * algebraMap R A ħ) +
        (algebraMap R A ζ + algebraMap R A ħ) ^ 2 := by
  have key : ((Polynomial.X + Polynomial.C ħ) ^ 2 : Polynomial R) =
      (Polynomial.X - Polynomial.C ζ) * (Polynomial.X + Polynomial.C ζ + 2 * Polynomial.C ħ) +
        (Polynomial.C ζ + Polynomial.C ħ) ^ 2 := by ring
  have := congrArg (Polynomial.aeval X) key
  simpa [map_ofNat] using this

/-- **Scalar inequality (l.6499–6503), with constant `C = 1`.** For `ħ > 0` and
`ζ ≤ ħ/2`, `ζ²/(ħ - ζ) ≤ |ζ| + ħ`. -/
theorem sq_div_le (ζ ħ : ℝ) (hħ : 0 < ħ) (hζ : ζ ≤ ħ / 2) :
    ζ ^ 2 / (ħ - ζ) ≤ |ζ| + ħ := by
  rw [div_le_iff₀ (by linarith)]
  rcases le_total 0 ζ with h | h
  · rw [abs_of_nonneg h]; nlinarith
  · rw [abs_of_nonpos h]; nlinarith

/-! ## Band length and determinant–distance (§2.4) -/

/-- **Lemma `gap:lem:band-order`, proof (l.2001–2010).** Let `N₀ = N_q(·,0,0)` and
`N_π = N_q(·,π,π)`. If `N₀` is differentiable with `|N₀'| ≤ K` between the band endpoints
`a, c`, `N₀(c) - N_π(c) > 6`, `N₀(a) = 0` and `N_π(c) = 0`, then `|a - c| > 6/K`
(with `K = e^{Cq}` this is `|a_j - c_j| ≥ 6e^{-Cq}`). -/
theorem band_length_lower {N₀ Nπ : ℝ → ℝ} {a c K : ℝ} (hK : 0 < K)
    (hdiff : ∀ E ∈ Set.uIcc a c, DifferentiableAt ℝ N₀ E)
    (hbound : ∀ E ∈ Set.uIcc a c, |deriv N₀ E| ≤ K)
    (hgap : 6 < N₀ c - Nπ c) (ha : N₀ a = 0) (hc : Nπ c = 0) :
    6 / K < |a - c| := by
  have := Convex.norm_image_sub_le_of_norm_deriv_le hdiff
    (fun E hE => by rw [Real.norm_eq_abs]; exact hbound E hE) (convex_uIcc a c)
    Set.left_mem_uIcc Set.right_mem_uIcc
  rw [Real.norm_eq_abs, Real.norm_eq_abs, ha, sub_zero, abs_sub_comm c a] at this
  rw [div_lt_iff₀ hK]
  have h6 : 6 < |N₀ c| := by rw [hc, sub_zero] at hgap; exact hgap.trans_le (le_abs_self _)
  linarith

/-- **`gap:eq:det-distance`, proof (l.2140–2145).** For a Hermitian matrix `H` whose
eigenvalues all satisfy `|λ_j - E| ≤ C₁`, and any `j₀` (in particular the eigenvalue nearest
`E`), `|det(H - E)| ≤ C₁^{q-1} |λ_{j₀} - E|`, where `q` is the size of `H`. -/
theorem norm_det_sub_le {n : Type*} [Fintype n] [DecidableEq n] {H : Matrix n n ℂ}
    (hH : H.IsHermitian) (E C₁ : ℝ) (hC : ∀ j, |hH.eigenvalues j - E| ≤ C₁) (j₀ : n) :
    ‖(H - Matrix.scalar n (E : ℂ)).det‖ ≤
      C₁ ^ (Fintype.card n - 1) * |hH.eigenvalues j₀ - E| := by
  have hdet : (H - Matrix.scalar n (E : ℂ)).det = (-1) ^ Fintype.card n *
      ∏ i, ((E : ℂ) - (hH.eigenvalues i : ℂ)) := by
    rw [← neg_sub, Matrix.det_neg, ← Matrix.eval_charpoly, hH.charpoly_eq,
      Polynomial.eval_prod]
    simp
  have hnorm : ‖(H - Matrix.scalar n (E : ℂ)).det‖ = ∏ i, |hH.eigenvalues i - E| := by
    rw [hdet, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_prod]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
  rw [hnorm, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j₀), mul_comm]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  calc ∏ i ∈ Finset.univ.erase j₀, |hH.eigenvalues i - E|
      ≤ ∏ _i ∈ Finset.univ.erase j₀, C₁ :=
        Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) (fun i _ => hC i)
    _ = C₁ ^ (Fintype.card n - 1) := by
        rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _),
          Finset.card_univ]

/-! ## Integer shifts of the frequency (l.376) -/

/-- **Integer shift sign (l.376–380).** `e^{πi(k+a)rs} = (-1)^{krs} e^{πiars}` for
`k, r, s ∈ ℤ` and real `a`; hence `W^{(k+a)}_{r,s} = (-1)^{krs} W^{(a)}_{r,s}`. -/
theorem exp_int_shift (k r s : ℤ) (a : ℝ) :
    Complex.exp (π * Complex.I * ((k + a) * r * s)) =
      (-1 : ℂ) ^ (k * r * s) * Complex.exp (π * Complex.I * (a * r * s)) := by
  rw [show (π : ℂ) * Complex.I * ((k + a) * r * s) =
      ((k * r * s : ℤ) : ℂ) * (π * Complex.I) + π * Complex.I * (a * r * s) by push_cast; ring,
    Complex.exp_add, Complex.exp_int_mul, Complex.exp_pi_mul_I]

end Pauli


end CornerGeometry

end SGD
