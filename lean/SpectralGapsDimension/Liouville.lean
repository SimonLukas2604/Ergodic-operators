/-
Copyright (c) 2026. Formalization of
  S. Becker, "Self-dual perturbations of the critical almost Mathieu operator:
  Dry Ten Martini and Hausdorff dimension" (Paper II).

# The Liouville branch  (paper §6: Lemma 4.17 and the proof of Theorem 1.2)

* `nums_dens_int`: numerators and denominators of the continued fraction are integers.
* `exists_rat_liouville`: for Liouville `α` and every `M ≥ 0` there are reduced fractions
  `p/q = r` with arbitrarily large `q` and `h = 2π q² |α - r| ≤ q^{-M}`, `h > 0`
  (Lemma 4.17, second part, in the form used by the proof of Theorem 1.2).
* `PacketCover`: the shape of the covers produced by Proposition 4.12 (`dim:prop:packet-cover`).
* `dimH_eq_zero_of_packetCovers`: the Hausdorff-cost computation of the proof of Theorem 1.2:
  if packet covers exist for every quantization order `N ≥ 2` (with constants depending on `N`)
  at a supply of approximants with `h ≤ q^{-M}` for every `M`, the set has dimension `0`.
  With `d > 0`, `N d > 1`, `K d > 1` and `η = q^{-K}`, the corner cost is
  `≤ 3q (2η)^d` and the regular cost is `≤ C^{1+d} q^{A(1+K)(1+d)} h^{Nd-1}`, both `→ 0`.

-/
import SpectralGapsDimension.Arithmetic
import SpectralGapsDimension.Hausdorff

noncomputable section

open MeasureTheory Filter Topology Set GenContFract
open scoped ENNReal NNReal

namespace SGD

/-! ### Integrality of numerators and denominators -/

lemma exists_s_get {α : ℝ} (hα : Irrational α) (n : ℕ) :
    ∃ gp, (GenContFract.of α).s.get? n = some gp :=
  Option.ne_none_iff_exists'.1 (not_terminatedAt hα n)

lemma partDen_int {α : ℝ} {n : ℕ} {gp : Pair ℝ} (h : (GenContFract.of α).s.get? n = some gp) :
    ∃ z : ℤ, gp.b = z :=
  exists_int_eq_of_partDen (partDen_eq_s_b h)

lemma partNum_one {α : ℝ} {n : ℕ} {gp : Pair ℝ} (h : (GenContFract.of α).s.get? n = some gp) :
    gp.a = 1 :=
  of_partNum_eq_one (partNum_eq_s_a h)

/-- The numerators `p_n` and denominators `q_n` of the continued fraction of an irrational
number are integers. -/
theorem nums_dens_int {α : ℝ} (hα : Irrational α) :
    ∀ n, (∃ z : ℤ, (GenContFract.of α).nums n = z) ∧ (∃ z : ℤ, (GenContFract.of α).dens n = z) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => exact ⟨⟨⌊α⌋, by rw [zeroth_num_eq_h, of_h_eq_floor]⟩, ⟨1, by simp⟩⟩
    | 1 =>
      obtain ⟨gp, hgp⟩ := exists_s_get hα 0
      obtain ⟨z, hz⟩ := partDen_int hgp
      refine ⟨⟨z * ⌊α⌋ + 1, ?_⟩, ⟨z, ?_⟩⟩
      · rw [first_num_eq hgp, hz, partNum_one hgp, of_h_eq_floor]; push_cast; ring
      · rw [first_den_eq hgp, hz]
    | k + 2 =>
      obtain ⟨gp, hgp⟩ := exists_s_get hα (k + 1)
      obtain ⟨z, hz⟩ := partDen_int hgp
      obtain ⟨⟨a0, ha0⟩, ⟨b0, hb0⟩⟩ := ih k (by omega)
      obtain ⟨⟨a1, ha1⟩, ⟨b1, hb1⟩⟩ := ih (k + 1) (by omega)
      refine ⟨⟨z * a1 + a0, ?_⟩, ⟨z * b1 + b0, ?_⟩⟩
      · rw [nums_recurrence hgp ha0 ha1, hz, partNum_one hgp]; push_cast; ring
      · rw [dens_recurrence hgp hb0 hb1, hz, partNum_one hgp]; push_cast; ring

/-! ### Rational Liouville approximants -/

/-- Irrational numbers stay uniformly away from fractions with bounded denominators. -/
lemma exists_pos_le_abs_sub {α : ℝ} (hα : Irrational α) (N₀ : ℕ) :
    ∃ m > 0, ∀ r : ℚ, r.den ≤ N₀ → m ≤ |α - r| := by
  set F : ℕ := N₀.factorial
  have hF : (0 : ℝ) < F := by exact_mod_cast Nat.factorial_pos N₀
  set e := |(F : ℝ) * α - round ((F : ℝ) * α)|
  have he : 0 < e := by
    refine abs_pos.2 (sub_ne_zero.2 fun h => ?_)
    exact (hα.natCast_mul (Nat.factorial_ne_zero N₀)) ⟨(round ((F : ℝ) * α) : ℚ), by
      push_cast; exact h.symm⟩
  refine ⟨e / F, div_pos he hF, fun r hr => ?_⟩
  have hdvd : r.den ∣ F := Nat.dvd_factorial r.den_pos hr
  obtain ⟨c, hc⟩ := hdvd
  have hint : ((F : ℝ) * (r : ℝ)) = ((r.num * c : ℤ) : ℝ) := by
    have : (r : ℝ) = r.num / r.den := by exact_mod_cast (Rat.num_div_den r).symm
    rw [this, hc]
    have hd : (r.den : ℝ) ≠ 0 := by exact_mod_cast r.den_ne_zero
    push_cast
    field_simp
  rw [div_le_iff₀ hF]
  calc e ≤ |(F : ℝ) * α - ((r.num * c : ℤ) : ℝ)| := round_le _ _
    _ = |α - r| * F := by
      rw [← hint, ← mul_sub, abs_mul, abs_of_pos hF, mul_comm]

/-- **Lemma 4.17, rational form.**  If `α` is Liouville, then for every `M ≥ 0` and every
`N₀` there is a fraction `r = p/q` (in lowest terms) with `q ≥ N₀`, `α ≠ r` and
`h = 2π q² |α - r| ≤ q^{-M}`. -/
theorem exists_rat_liouville {α : ℝ} (hα : Irrational α) (hL : Liouville α) {M : ℝ}
    (hM : 0 ≤ M) (N₀ : ℕ) :
    ∃ r : ℚ, N₀ ≤ r.den ∧ 0 < |α - r| ∧
      2 * Real.pi * (r.den : ℝ) ^ 2 * |α - r| ≤ (r.den : ℝ) ^ (-M) := by
  obtain ⟨m, hm, hmr⟩ := exists_pos_le_abs_sub hα N₀
  have hq := cfGrowth hα
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hq.tendsto_atTop.eventually_gt_atTop (m⁻¹ + 1))
  obtain ⟨n, hnN, hn1, hn⟩ := exists_convergent_liouville hα hL M N
  set Q := AMO.cfDen α n
  have hQ1 : 1 < Q := hn1
  have hQ0 : 0 < Q := zero_lt_one.trans hQ1
  obtain ⟨⟨P, hP⟩, ⟨Qz, hQz⟩⟩ := nums_dens_int hα n
  have hQz' : (Q : ℝ) = Qz := hQz
  have hQzpos : 0 < Qz := by exact_mod_cast hQz' ▸ hQ0
  set r : ℚ := (P : ℚ) / (Qz : ℚ)
  have hr : ((r : ℚ) : ℝ) = (GenContFract.of α).convs n := by
    show _ = (GenContFract.of α).nums n / (GenContFract.of α).dens n
    rw [hP, hQz]
    simp [r]
  have hden : (r.den : ℝ) ≤ Q := by
    have h1 : r.den ∣ Qz.natAbs := by
      have := Rat.den_dvd P Qz
      rw [Rat.divInt_eq_div] at this
      exact Int.ofNat_dvd_left.1 this
    have h2 : r.den ≤ Qz.natAbs := Nat.le_of_dvd (Int.natAbs_pos.2 hQzpos.ne') h1
    rw [hQz']
    have : ((Qz.natAbs : ℕ) : ℝ) = (Qz : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos (by exact_mod_cast hQzpos)]
    rw [← this]; exact_mod_cast h2
  have hdpos : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have habs : 0 < |α - (GenContFract.of α).convs n| := by
    refine abs_pos.2 (sub_ne_zero.2 fun h => hα ⟨r, ?_⟩)
    rw [hr]; exact h.symm
  -- `|α - r| < m`, hence `r.den > N₀`
  have hsmall : |α - (GenContFract.of α).convs n| < m := by
    have hQm : m⁻¹ + 1 < Q := hN n hnN
    have h2 : 2 * Real.pi * Q ^ 2 * |α - (GenContFract.of α).convs n| ≤ 1 := by
      refine hn.trans (Real.rpow_le_one_of_one_le_of_nonpos hQ1.le (by linarith))
    have hpi : 1 ≤ 2 * Real.pi * Q ^ 2 := by nlinarith [Real.pi_gt_three]
    have h3 : |α - (GenContFract.of α).convs n| ≤ 1 / (2 * Real.pi * Q ^ 2) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    have h4 : 1 / (2 * Real.pi * Q ^ 2) < m := by
      rw [div_lt_iff₀ (by positivity)]
      have : m⁻¹ < Q := by linarith
      have hQQ : Q ≤ 2 * Real.pi * Q ^ 2 := by nlinarith [Real.pi_gt_three]
      calc (1 : ℝ) = m * m⁻¹ := (mul_inv_cancel₀ hm.ne').symm
        _ < m * Q := by gcongr
        _ ≤ m * (2 * Real.pi * Q ^ 2) := by gcongr
    linarith
  refine ⟨r, ?_, by rw [hr]; exact habs, ?_⟩
  · by_contra hlt
    have := hmr r (by omega)
    rw [hr] at this
    linarith
  · rw [hr]
    calc 2 * Real.pi * (r.den : ℝ) ^ 2 * |α - (GenContFract.of α).convs n|
        ≤ 2 * Real.pi * Q ^ 2 * |α - (GenContFract.of α).convs n| := by gcongr
      _ ≤ Q ^ (-M) := hn
      _ ≤ (r.den : ℝ) ^ (-M) := Real.rpow_le_rpow_of_nonpos hdpos hden (by linarith)

/-! ### Packet covers and the Hausdorff cost -/

/-- The cover of Proposition 4.12 (`dim:prop:packet-cover`) at denominator `q`, radius `η`,
field `h`, constants `C, A` and quantization order `N`: at most `3q` corner intervals of
diameter `≤ 2η`, and at most `C q^A η^{-A} h^{-1}` remaining intervals of diameter
`≤ C q^A η^{-A} h^N`. -/
def PacketCover (K : Set ℝ) (q η h C A : ℝ) (N : ℕ) : Prop :=
  ∃ (m₁ m₂ : ℕ) (a₁ b₁ : Fin m₁ → ℝ) (a₂ b₂ : Fin m₂ → ℝ),
    K ⊆ (⋃ i, Icc (a₁ i) (b₁ i)) ∪ ⋃ j, Icc (a₂ j) (b₂ j) ∧
    (m₁ : ℝ) ≤ 3 * q ∧ (∀ i, a₁ i ≤ b₁ i ∧ b₁ i - a₁ i ≤ 2 * η) ∧
    (m₂ : ℝ) ≤ C * q ^ A * η ^ (-A) * h⁻¹ ∧
    (∀ j, a₂ j ≤ b₂ j ∧ b₂ j - a₂ j ≤ C * q ^ A * η ^ (-A) * h ^ N)

/-- **Hausdorff cost of packet covers** (proof of Theorem 1.2, eqs. (6.2)–(6.3)).
`good q h` describes the approximants at which Proposition 4.12 applies.  If for every
order `N ≥ 2` there are constants `C, A, L` such that packet covers exist below the
threshold `h ≤ C^{-1} q^{-L} η^L`, and approximants with `h ≤ q^{-M}` exist with arbitrarily
large `q` for every `M`, then `dim_H K = 0`. -/
theorem dimH_eq_zero_of_packetCovers {K : Set ℝ} (good : ℝ → ℝ → Prop)
    (hcov : ∀ N : ℕ, 2 ≤ N → ∃ C A L : ℝ, 0 < C ∧ 0 ≤ A ∧ 0 ≤ L ∧
      ∀ q h η : ℝ, good q h → 0 < η → η ≤ 1 → 0 < h → h ≤ C⁻¹ * q ^ (-L) * η ^ L →
        PacketCover K q η h C A N)
    (hsupply : ∀ M : ℝ, 0 ≤ M → ∀ Q₀ : ℝ, ∃ q h : ℝ, good q h ∧ Q₀ ≤ q ∧ 1 ≤ q ∧ 0 < h ∧
      h ≤ q ^ (-M)) :
    dimH K = 0 := by
  refine Hausdorff.dimH_eq_zero_of_forall fun d hd => ?_
  -- choice of the quantization order and of the radius exponent
  set N : ℕ := ⌈2 / d⌉₊ + 2 with hNdef
  have hN2 : 2 ≤ N := by omega
  have hNd : 2 ≤ (N : ℝ) * d := by
    have h1 : 2 / d ≤ (N : ℝ) := by
      have := Nat.le_ceil (2 / d)
      have : ((⌈2 / d⌉₊ : ℕ) : ℝ) ≤ N := by exact_mod_cast (by omega : ⌈2 / d⌉₊ ≤ N)
      linarith
    calc (2 : ℝ) = 2 / d * d := by field_simp
      _ ≤ N * d := by gcongr
  obtain ⟨C, A, L, hC, hA, hL, hcovN⟩ := hcov N hN2
  set κ : ℝ := 2 / d with hκ
  have hκ0 : 0 < κ := by positivity
  have hκd : κ * d = 2 := by rw [hκ]; field_simp
  obtain ⟨B, hB⟩ : ∃ B : ℝ,
      B = L * (1 + κ) + 1 + (A * (1 + κ) * (1 + d) + 1) + (A * (1 + κ) + 1) := ⟨_, rfl⟩
  have hp1 : 0 ≤ L * (1 + κ) := by positivity
  have hp2 : 0 ≤ A * (1 + κ) * (1 + d) := by positivity
  have hp3 : 0 ≤ A * (1 + κ) := by positivity
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hB1 : L * (1 + κ) + 1 ≤ B := by rw [hB]; linarith
  have hB2 : A * (1 + κ) * (1 + d) + 1 ≤ B := by rw [hB]; linarith
  have hB3 : A * (1 + κ) + 1 ≤ B := by rw [hB]; linarith
  -- the supply of approximants, indexed by `k : ℕ`
  have hs : ∀ k : ℕ, ∃ q h : ℝ, good q h ∧ (k : ℝ) + C + 1 ≤ q ∧ 1 ≤ q ∧ 0 < h ∧
      h ≤ q ^ (-B) := fun k => hsupply B hB0 _
  choose q h hgood hqk hq1 hh0 hhB using hs
  have hq0 : ∀ k, 0 < q k := fun k => zero_lt_one.trans_le (hq1 k)
  set η : ℕ → ℝ := fun k => q k ^ (-κ) with hη
  have hη0 : ∀ k, 0 < η k := fun k => Real.rpow_pos_of_pos (hq0 k) _
  have hη1 : ∀ k, η k ≤ 1 := fun k => Real.rpow_le_one_of_one_le_of_nonpos (hq1 k) (by linarith)
  -- basic power bounds
  have hpow_le : ∀ k (x y : ℝ), x ≤ y → q k ^ x ≤ q k ^ y := fun k x y hxy =>
    Real.rpow_le_rpow_of_exponent_le (hq1 k) hxy
  have hqinv : ∀ k, (q k)⁻¹ ≤ C⁻¹ := fun k => by
    have : C < q k := by linarith [hqk k, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    exact inv_anti₀ hC this.le
  have hh1 : ∀ k, h k ≤ 1 := fun k =>
    (hhB k).trans (Real.rpow_le_one_of_one_le_of_nonpos (hq1 k) (by linarith))
  have hηpow : ∀ k (t : ℝ), η k ^ t = q k ^ (-κ * t) := fun k t => by
    rw [hη]; dsimp only; rw [← Real.rpow_mul (hq0 k).le]
  -- the threshold of Proposition 4.12 holds
  have hthr : ∀ k, h k ≤ C⁻¹ * q k ^ (-L) * η k ^ L := fun k => by
    rw [hηpow, mul_assoc, ← Real.rpow_add (hq0 k)]
    calc h k ≤ q k ^ (-B) := hhB k
      _ ≤ q k ^ ((-L + -κ * L) + -1) := hpow_le k (-B) ((-L + -κ * L) + -1) (by linarith)
      _ = (q k)⁻¹ * q k ^ (-L + -κ * L) := by
        rw [Real.rpow_add (hq0 k), Real.rpow_neg_one, mul_comm]
      _ ≤ C⁻¹ * q k ^ (-L + -κ * L) :=
        mul_le_mul_of_nonneg_right (hqinv k) (Real.rpow_nonneg (hq0 k).le _)
  have hcovk : ∀ k, PacketCover K (q k) (η k) (h k) C A N := fun k =>
    hcovN _ _ _ (hgood k) (hη0 k) (hη1 k) (hh0 k) (hthr k)
  choose m₁ m₂ a₁ b₁ a₂ b₂ hK hm₁ hl₁ hm₂ hl₂ using hcovk
  -- `X = C q^A η^{-A} = C q^{A(1+κ)}`
  set X : ℕ → ℝ := fun k => C * q k ^ (A * (1 + κ)) with hX
  have hX0 : ∀ k, 0 < X k := fun k => mul_pos hC (Real.rpow_pos_of_pos (hq0 k) _)
  have hXeq : ∀ k, C * q k ^ A * η k ^ (-A) = X k := fun k => by
    rw [hηpow, mul_assoc, ← Real.rpow_add (hq0 k)]; congr 2; ring
  have hhN : ∀ k, h k ^ N ≤ h k := fun k =>
    pow_le_of_le_one (hh0 k).le (hh1 k) (by omega)
  -- length bounds
  have hXh : ∀ k, X k * h k ≤ C * (q k)⁻¹ := fun k => by
    calc X k * h k ≤ X k * q k ^ (-B) := mul_le_mul_of_nonneg_left (hhB k) (hX0 k).le
      _ = C * q k ^ (A * (1 + κ) - B) := by
          simp only [hX]
          rw [mul_assoc, ← Real.rpow_add (hq0 k), sub_eq_add_neg]
      _ ≤ C * q k ^ (-1 : ℝ) :=
          mul_le_mul_of_nonneg_left (hpow_le k _ _ (by linarith)) hC.le
      _ = C * (q k)⁻¹ := by rw [Real.rpow_neg_one]
  set δ : ℕ → ℝ := fun k => 2 * η k + C * (q k)⁻¹
  have hqtop : Tendsto q atTop atTop :=
    tendsto_atTop_mono (fun k => by linarith [hqk k]) tendsto_natCast_atTop_atTop
  have hδ : Tendsto δ atTop (𝓝 0) := by
    have h1 : Tendsto η atTop (𝓝 0) := (tendsto_rpow_neg_atTop hκ0).comp hqtop
    have h2 : Tendsto (fun k => C * (q k)⁻¹) atTop (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero.comp hqtop).const_mul C
    simpa using (h1.const_mul 2).add h2
  -- the combined cover
  let ι : ℕ → Type := fun k => Fin (m₁ k) ⊕ Fin (m₂ k)
  let a : ∀ k, ι k → ℝ := fun k => Sum.elim (a₁ k) (a₂ k)
  let b : ∀ k, ι k → ℝ := fun k => Sum.elim (b₁ k) (b₂ k)
  have hlen : ∀ k (i : ι k), a k i ≤ b k i ∧ b k i - a k i ≤ δ k := by
    intro k i
    have hηn : 0 ≤ η k := (hη0 k).le
    have hCq : 0 ≤ C * (q k)⁻¹ := by have := hq0 k; positivity
    rcases i with i | j
    · exact ⟨(hl₁ k i).1, by simp only [a, b, Sum.elim_inl, δ]; linarith [(hl₁ k i).2]⟩
    · refine ⟨(hl₂ k j).1, ?_⟩
      simp only [a, b, Sum.elim_inr, δ]
      calc b₂ k j - a₂ k j ≤ C * q k ^ A * η k ^ (-A) * h k ^ N := (hl₂ k j).2
        _ = X k * h k ^ N := by rw [hXeq]
        _ ≤ X k * h k := mul_le_mul_of_nonneg_left (hhN k) (hX0 k).le
        _ ≤ C * (q k)⁻¹ := hXh k
        _ ≤ 2 * η k + C * (q k)⁻¹ := by linarith
  have hcov' : ∀ k, K ⊆ ⋃ i, Icc (a k i) (b k i) := by
    intro k x hx
    rcases hK k hx with hx | hx
    · obtain ⟨i, hi⟩ := mem_iUnion.1 hx
      exact mem_iUnion.2 ⟨Sum.inl i, hi⟩
    · obtain ⟨j, hj⟩ := mem_iUnion.1 hx
      exact mem_iUnion.2 ⟨Sum.inr j, hj⟩
  -- the cost bound `∑ |I|^d ≤ (3·2^d + C^{1+d}) / q`
  have hcost_le : ∀ k, ∑ i, (b k i - a k i) ^ d ≤ (3 * 2 ^ d + C ^ (1 + d)) * (q k)⁻¹ := by
    intro k
    have hqk0 := hq0 k
    rw [Fintype.sum_sum_type]
    simp only [a, b, Sum.elim_inl, Sum.elim_inr]
    -- corner intervals
    have hexc : ∑ i, (b₁ k i - a₁ k i) ^ d ≤ 3 * 2 ^ d * (q k)⁻¹ := by
      calc ∑ i, (b₁ k i - a₁ k i) ^ d ≤ ∑ _i : Fin (m₁ k), (2 * η k) ^ d :=
            Finset.sum_le_sum fun i _ => Real.rpow_le_rpow (by linarith [(hl₁ k i).1])
              (hl₁ k i).2 hd.le
        _ = m₁ k * (2 * η k) ^ d := by simp
        _ ≤ 3 * q k * (2 * η k) ^ d := by gcongr; exact hm₁ k
        _ = 3 * 2 ^ d * (q k)⁻¹ := by
          rw [Real.mul_rpow (by norm_num) (hη0 k).le, hηpow, ← Real.rpow_neg_one,
            show -κ * d = -2 by rw [neg_mul, hκd]]
          have : q k * q k ^ (-2 : ℝ) = q k ^ (-1 : ℝ) := by
            rw [← Real.rpow_one_add' hqk0.le (by norm_num)]; norm_num
          calc 3 * q k * (2 ^ d * q k ^ (-2 : ℝ)) = 3 * 2 ^ d * (q k * q k ^ (-2 : ℝ)) := by
                ring
            _ = _ := by rw [this]
    -- remaining intervals
    have hreg : ∑ j, (b₂ k j - a₂ k j) ^ d ≤ C ^ (1 + d) * (q k)⁻¹ := by
      have hXn : 0 ≤ X k * h k ^ N := by have := hX0 k; have := hh0 k; positivity
      have hstep : ∀ j, (b₂ k j - a₂ k j) ^ d ≤ (X k * h k ^ N) ^ d := fun j =>
        Real.rpow_le_rpow (by linarith [(hl₂ k j).1]) (by rw [← hXeq]; exact (hl₂ k j).2) hd.le
      have hm₂' : (m₂ k : ℝ) ≤ X k * (h k)⁻¹ := by rw [← hXeq]; exact hm₂ k
      have hpow : (h k ^ N) ^ d * (h k)⁻¹ ≤ h k := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (hh0 k).le, ← Real.rpow_neg_one,
          ← Real.rpow_add (hh0 k)]
        calc h k ^ ((N : ℝ) * d + -1) ≤ h k ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_ge (hh0 k) (hh1 k) (by linarith)
          _ = h k := Real.rpow_one _
      calc ∑ j, (b₂ k j - a₂ k j) ^ d ≤ ∑ _j : Fin (m₂ k), (X k * h k ^ N) ^ d :=
            Finset.sum_le_sum fun j _ => hstep j
        _ = m₂ k * (X k * h k ^ N) ^ d := by simp
        _ ≤ X k * (h k)⁻¹ * (X k * h k ^ N) ^ d := by
            gcongr
        _ = X k ^ (1 + d) * ((h k ^ N) ^ d * (h k)⁻¹) := by
            rw [Real.mul_rpow (hX0 k).le (by have := hh0 k; positivity),
              Real.rpow_add (hX0 k), Real.rpow_one]; ring
        _ ≤ X k ^ (1 + d) * h k :=
            mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg (hX0 k).le _)
        _ ≤ X k ^ (1 + d) * q k ^ (-B) :=
            mul_le_mul_of_nonneg_left (hhB k) (Real.rpow_nonneg (hX0 k).le _)
        _ = C ^ (1 + d) * q k ^ (A * (1 + κ) * (1 + d) - B) := by
            simp only [hX]
            rw [Real.mul_rpow hC.le (Real.rpow_nonneg hqk0.le _), ← Real.rpow_mul hqk0.le,
              mul_assoc, ← Real.rpow_add hqk0]; ring_nf
        _ ≤ C ^ (1 + d) * q k ^ (-1 : ℝ) :=
            mul_le_mul_of_nonneg_left (hpow_le k _ _ (by linarith))
              (Real.rpow_nonneg hC.le _)
        _ = C ^ (1 + d) * (q k)⁻¹ := by rw [Real.rpow_neg_one]
    calc _ ≤ 3 * 2 ^ d * (q k)⁻¹ + C ^ (1 + d) * (q k)⁻¹ := add_le_add hexc hreg
      _ = _ := by ring
  have hcost : Tendsto (fun k => ∑ i, (b k i - a k i) ^ d) atTop (𝓝 0) := by
    have hup : Tendsto (fun k => (3 * 2 ^ d + C ^ (1 + d)) * (q k)⁻¹) atTop (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero.comp hqtop).const_mul (3 * 2 ^ d + C ^ (1 + d))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun k => ?_)
      hcost_le
    exact Finset.sum_nonneg fun i _ => Real.rpow_nonneg (by linarith [(hlen k i).1]) _
  exact Hausdorff.hausdorffMeasure_eq_zero_of_covers hd.le ι a b δ hδ
    (Eventually.of_forall hlen) (Eventually.of_forall hcov') hcost

end SGD
