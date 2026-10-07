/-
# Magnetic generators, Weyl series and Fourier duality  (paper §1.1 and §2.1)

On `ℓ²(ℤ)`, with frequency `α` and phase `x`,
  `(U u)_n = u_{n+1}`,  `(V_x u)_n = e^{2πi(x+nα)} u_n`,  `W_{r,q} = e^{πiαrq} V_x^q U^r`,
so that `(W_{r,q} u)_n = e^{2πi(αrq/2 + q(x+nα))} u_{n+r}`.

We prove (fully, no `sorry`):
* the Weyl relations `W_{r,q} W_{r',q'} = e^{πiα(rq'-r'q)} W_{r+r',q+q'}` and `W_{r,q}^* = W_{-r,-q}`;
* that an absolutely summable Weyl series `H_x = ∑ R_{r,q} W_{r,q}` is bounded with
  `‖H_x‖ ≤ ∑ |R_{r,q}|`, self-adjoint when `R_{-r,-q} = conj R_{r,q}`, covariant
  (`U H_x = H_{x+α} U`), `1`-periodic and norm-continuous in `x`;
* the algebra of Fourier duality `𝓕(W_{r,q}) = W_{q,-r}` on symbols: it preserves the Weyl
  phases and self-adjointness, exchanges the two analytic weights, satisfies `𝓕⁴ = id`, and
  maps the almost Mathieu symbol at coupling `η` to `η` times the one at coupling `η⁻¹`.
-/
import AnalyticPerturbationsAMO.Operators

noncomputable section

open scoped ComplexConjugate
open Complex L2

namespace AMO

/-- `e(t) = exp(2πit)`. -/
def e (t : ℝ) : ℂ := Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * I)

@[simp] lemma norm_e (t : ℝ) : ‖e t‖ = 1 := Complex.norm_exp_ofReal_mul_I _

lemma e_add (s t : ℝ) : e (s + t) = e s * e t := by
  unfold e
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

@[simp] lemma e_zero : e 0 = 1 := by simp [e]

lemma conj_e (t : ℝ) : conj (e t) = e (-t) := by
  unfold e
  rw [← Complex.exp_conj]
  congr 1
  simp [map_mul, Complex.conj_ofReal, map_ofNat]

lemma e_intCast (k : ℤ) : e k = 1 := by
  unfold e
  have : (((2 * Real.pi * (k : ℝ) : ℝ) : ℂ) * I) = k * (2 * Real.pi * I) := by
    push_cast
    ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

lemma e_add_int (t : ℝ) (k : ℤ) : e (t + k) = e t := by
  rw [e_add, e_intCast, mul_one]

lemma e_congr {s t : ℝ} (h : s = t) : e s = e t := by rw [h]

lemma bdd_e {ι : Type*} (f : ι → ℝ) : Bdd (fun n => e (f n)) := bdd_of_norm_eq_one (fun _ => norm_e _)

/-! ### The generators -/

/-- The magnetic Weyl operator `W_{r,q}(x)` on `ℓ²(ℤ)`, frequency `α`. -/
def W (α x : ℝ) (r q : ℤ) : L2 ℤ →L[ℂ] L2 ℤ :=
  weightedShift (fun n : ℤ => e (α * r * q / 2 + q * (x + n * α))) (Equiv.addRight r)

/-- The shift `(U u)_n = u_{n+1}`. -/
def U (α x : ℝ) : L2 ℤ →L[ℂ] L2 ℤ := W α x 1 0

/-- The phase operator `(V_x u)_n = e^{2πi(x+nα)} u_n`. -/
def V (α x : ℝ) : L2 ℤ →L[ℂ] L2 ℤ := W α x 0 1

lemma W_apply (α x : ℝ) (r q : ℤ) (u : L2 ℤ) (n : ℤ) :
    W α x r q u n = e (α * r * q / 2 + q * (x + n * α)) * u (n + r) := by
  rw [W, weightedShift_apply (bdd_e _)]
  rfl

lemma U_apply (α x : ℝ) (u : L2 ℤ) (n : ℤ) : U α x u n = u (n + 1) := by
  simp [U, W_apply]

lemma V_apply (α x : ℝ) (u : L2 ℤ) (n : ℤ) : V α x u n = e (x + n * α) * u n := by
  simp [V, W_apply]

lemma norm_W_le (α x : ℝ) (r q : ℤ) : ‖W α x r q‖ ≤ 1 :=
  norm_weightedShift_le zero_le_one (fun _ => (norm_e _).le)

/-- The phase dependence of `W_{r,q}(x)` is a scalar factor `e(qx)`. -/
lemma W_eq_smul (α x : ℝ) (r q : ℤ) : W α x r q = e (q * x) • W α 0 r q := by
  ext u n
  rw [smul_apply, lp.coeFn_smul, Pi.smul_apply, W_apply, W_apply, smul_eq_mul, ← mul_assoc,
    ← e_add]
  congr 2
  ring

/-- `UV_x = e^{2πiα} V_x U`. -/
lemma U_mul_V (α x : ℝ) : U α x ∘L V α x = e α • (V α x ∘L U α x) := by
  ext u n
  simp only [ContinuousLinearMap.comp_apply, U_apply, V_apply, smul_apply, lp.coeFn_smul,
    Pi.smul_apply, smul_eq_mul]
  rw [← mul_assoc, ← e_add]
  congr 2
  push_cast
  ring

/-- **Weyl relation.** `W_{r,q} W_{r',q'} = e^{πiα(rq'-r'q)} W_{r+r',q+q'}`. -/
theorem W_mul (α x : ℝ) (r q r' q' : ℤ) :
    W α x r q ∘L W α x r' q' = e (α * (r * q' - r' * q) / 2) • W α x (r + r') (q + q') := by
  ext u n
  simp only [ContinuousLinearMap.comp_apply, W_apply, smul_apply, lp.coeFn_smul,
    Pi.smul_apply, smul_eq_mul]
  simp only [← mul_assoc, ← e_add, add_assoc n r r']
  congr 2
  push_cast
  ring

/-- `W_{r,q}^* = W_{-r,-q}`. -/
theorem star_W (α x : ℝ) (r q : ℤ) : star (W α x r q) = W α x (-r) (-q) := by
  rw [W, star_weightedShift (bdd_e _), W]
  apply weightedShift_congr
  · intro n
    rw [conj_e]
    congr 1
    simp only [Equiv.addRight_symm_apply]
    push_cast
    ring
  · intro n
    simp

/-- Covariance of the generators: `U W_{r,q}(x) = W_{r,q}(x+α) U`. -/
theorem U_comp_W (α x : ℝ) (r q : ℤ) :
    U α x ∘L W α x r q = W α (x + α) r q ∘L U α x := by
  ext u n
  simp only [ContinuousLinearMap.comp_apply, U_apply, W_apply]
  congr 1
  · congr 1
    push_cast
    ring
  · rw [add_right_comm]

lemma W_add_int (α x : ℝ) (k : ℤ) (r q : ℤ) : W α (x + k) r q = W α x r q := by
  rw [W_eq_smul, W_eq_smul α x]
  congr 1
  rw [mul_add, ← Int.cast_mul, e_add, e_intCast, mul_one]

/-- `U` is unitary: `U U^{-1} = U^{-1} U = 1` with `U^{-1} = W_{-1,0}`. -/
lemma U_comp_Uinv (α x : ℝ) : U α x ∘L W α x (-1) 0 = 1 := by
  ext u n
  simp [U_apply, W_apply]

lemma Uinv_comp_U (α x : ℝ) : W α x (-1) 0 ∘L U α x = 1 := by
  ext u n
  simp [U_apply, W_apply]

/-! ### Weyl symbols and Weyl series -/

/-- A Weyl symbol: the coefficients `R_{r,q}` of `R = ∑ R_{r,q} W_{r,q}`. -/
abbrev Symbol := ℤ × ℤ → ℂ

/-- The weighted analytic norm `‖R‖_{s,ℓ} = ∑ |R_{r,q}| e^{s|r| + ℓ|q|}`. -/
def wnorm (s ℓ : ℝ) (R : Symbol) : ℝ :=
  ∑' p : ℤ × ℤ, ‖R p‖ * Real.exp (s * |(p.1 : ℝ)| + ℓ * |(p.2 : ℝ)|)

/-- `‖R‖_{s,ℓ} < ε`, including summability of the weighted series. -/
def WSmall (s ℓ : ℝ) (R : Symbol) (ε : ℝ) : Prop :=
  Summable (fun p : ℤ × ℤ => ‖R p‖ * Real.exp (s * |(p.1 : ℝ)| + ℓ * |(p.2 : ℝ)|)) ∧
    wnorm s ℓ R < ε

/-- Self-adjointness of a symbol: `R_{-r,-q} = conj R_{r,q}`. -/
def SymbolSelfAdjoint (R : Symbol) : Prop := ∀ p, R (-p) = conj (R p)

/-- Absolute summability of a symbol. -/
def SymbolSummable (R : Symbol) : Prop := Summable fun p => ‖R p‖

lemma WSmall.summable {s ℓ ε : ℝ} {R : Symbol} (hs : 0 ≤ s) (hℓ : 0 ≤ ℓ) (h : WSmall s ℓ R ε) :
    SymbolSummable R := by
  refine h.1.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_)
  refine le_mul_of_one_le_right (norm_nonneg _) ?_
  exact Real.one_le_exp (by positivity)

/-- The Weyl series `R_x = ∑ R_{r,q} W_{r,q}(x)` as a bounded operator. -/
def op (α : ℝ) (R : Symbol) (x : ℝ) : L2 ℤ →L[ℂ] L2 ℤ :=
  ∑' p : ℤ × ℤ, R p • W α x p.1 p.2

lemma summable_op {α : ℝ} {R : Symbol} (hR : SymbolSummable R) (x : ℝ) :
    Summable fun p : ℤ × ℤ => R p • W α x p.1 p.2 := by
  refine Summable.of_norm_bounded hR (fun p => ?_)
  rw [norm_smul]
  exact mul_le_of_le_one_right (norm_nonneg _) (norm_W_le _ _ _ _)

/-- `‖R_x‖ ≤ ∑ |R_{r,q}|`. -/
theorem norm_op_le {α : ℝ} {R : Symbol} (hR : SymbolSummable R) (x : ℝ) :
    ‖op α R x‖ ≤ ∑' p, ‖R p‖ := by
  refine tsum_of_norm_bounded hR.hasSum (fun p => ?_)
  rw [norm_smul]
  exact mul_le_of_le_one_right (norm_nonneg _) (norm_W_le _ _ _ _)

lemma op_add {α : ℝ} {R R' : Symbol} (hR : SymbolSummable R) (hR' : SymbolSummable R')
    (x : ℝ) : op α (R + R') x = op α R x + op α R' x := by
  unfold op
  rw [← (summable_op hR x).tsum_add (summable_op hR' x)]
  congr 1
  funext p
  exact add_smul (R p) (R' p) (W α x p.1 p.2)

/-- A self-adjoint symbol gives a self-adjoint operator. -/
theorem isSelfAdjoint_op {α : ℝ} {R : Symbol} (hR : SymbolSummable R)
    (hsa : SymbolSelfAdjoint R) (x : ℝ) : IsSelfAdjoint (op α R x) := by
  have h1 := (summable_op (α := α) hR x).hasSum.star
  have h2 := ((Equiv.neg (ℤ × ℤ)).hasSum_iff).2 (summable_op (α := α) hR x).hasSum
  unfold IsSelfAdjoint op
  refine h1.unique ?_
  convert h2 using 1
  funext p
  simp [star_W, hsa p]

lemma summable_op_apply {α : ℝ} {R : Symbol} (hR : SymbolSummable R) (x : ℝ) (u : L2 ℤ) :
    Summable fun p : ℤ × ℤ => R p • W α x p.1 p.2 u := by
  refine Summable.of_norm_bounded (hR.mul_right ‖u‖) (fun p => ?_)
  rw [norm_smul]
  gcongr
  exact (W α x p.1 p.2).le_of_opNorm_le (norm_W_le _ _ _ _) u |>.trans (by simp)

lemma op_apply {α : ℝ} {R : Symbol} (hR : SymbolSummable R) (x : ℝ) (u : L2 ℤ) :
    op α R x u = ∑' p : ℤ × ℤ, R p • W α x p.1 p.2 u := by
  have := (ContinuousLinearMap.apply ℂ (L2 ℤ) u).map_tsum (summable_op (α := α) hR x)
  exact this

/-- **Covariance.** `U R_x = R_{x+α} U`, i.e. `R_{x+α} = U R_x U^{-1}`. -/
theorem U_comp_op {α : ℝ} {R : Symbol} (hR : SymbolSummable R) (x : ℝ) :
    U α x ∘L op α R x = op α R (x + α) ∘L U α x := by
  refine ContinuousLinearMap.ext fun u => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, op_apply hR, op_apply hR,
    (U α x).map_tsum (summable_op_apply hR x u)]
  congr 1
  funext p
  rw [map_smul]
  congr 1
  exact DFunLike.congr_fun (U_comp_W α x p.1 p.2) u

theorem op_conj_U {α : ℝ} {R : Symbol} (hR : SymbolSummable R) (x : ℝ) :
    op α R (x + α) = U α x ∘L op α R x ∘L W α x (-1) 0 := by
  rw [← ContinuousLinearMap.comp_assoc, U_comp_op hR, ContinuousLinearMap.comp_assoc,
    U_comp_Uinv]
  rfl

lemma op_add_int (α : ℝ) (R : Symbol) (x : ℝ) (k : ℤ) : op α R (x + k) = op α R x := by
  unfold op
  simp [W_add_int]

/-- **Norm continuity of the family** `x ↦ R_x`. -/
theorem continuous_op {α : ℝ} {R : Symbol} (hR : SymbolSummable R) :
    Continuous (op α R) := by
  have : op α R = fun x => ∑' p : ℤ × ℤ, (R p * e (p.2 * x)) • W α 0 p.1 p.2 := by
    funext x
    unfold op
    congr 1
    funext p
    rw [W_eq_smul, smul_smul]
  rw [this]
  refine continuous_tsum (f := fun (p : ℤ × ℤ) (x : ℝ) => (R p * e (p.2 * x)) • W α 0 p.1 p.2)
    (fun p => ?_) hR (fun p x => ?_)
  · unfold e
    fun_prop
  · rw [norm_smul, norm_mul, norm_e, mul_one]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_W_le _ _ _ _)

/-! ### Fourier duality on symbols -/

/-- Fourier duality `𝓕(W_{r,q}) = W_{q,-r}` acting on symbols:
`(𝓕 R)_{r',q'} = R_{-q',r'}`. -/
def fourier (R : Symbol) : Symbol := fun p => R (-p.2, p.1)

lemma fourier_single (r q : ℤ) (c : ℂ) :
    fourier (Pi.single (r, q) c) = Pi.single (q, -r) c := by
  funext p
  obtain ⟨a, b⟩ := p
  by_cases h : (a, b) = (q, -r)
  · simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [fourier]
  · rw [Pi.single_eq_of_ne h]
    unfold fourier
    rw [Pi.single_eq_of_ne]
    intro h'
    simp only [Prod.mk.injEq] at h h'
    omega

/-- Fourier duality preserves the Weyl commutation phases (it is a symplectic map of `ℤ²`). -/
lemma fourier_preserves_phase (r q r' q' : ℤ) :
    (q * (-r') - q' * (-r) : ℤ) = r * q' - r' * q := by ring

lemma fourier_fourier (R : Symbol) (p : ℤ × ℤ) : fourier (fourier R) p = R (-p) := rfl

theorem fourier_four (R : Symbol) : fourier (fourier (fourier (fourier R))) = R := by
  funext p
  simp [fourier]

lemma SymbolSelfAdjoint.fourier {R : Symbol} (h : SymbolSelfAdjoint R) :
    SymbolSelfAdjoint (fourier R) := by
  intro p
  show R (-(-p).2, (-p).1) = conj (R (-p.2, p.1))
  rw [← h]
  congr 1

lemma SymbolSummable.fourier {R : Symbol} (h : SymbolSummable R) :
    SymbolSummable (fourier R) := by
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    { toFun := fun p => (-p.2, p.1), invFun := fun p => (p.2, -p.1),
      left_inv := fun p => by simp, right_inv := fun p => by simp }
  exact (e.summable_iff (f := fun p => ‖R p‖)).2 h

/-- Fourier duality exchanges the hopping and phase weights: `‖𝓕R‖_{s,ℓ} = ‖R‖_{ℓ,s}`. -/
theorem wnorm_fourier (s ℓ : ℝ) (R : Symbol) : wnorm s ℓ (fourier R) = wnorm ℓ s R := by
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    { toFun := fun p => (p.2, -p.1), invFun := fun p => (-p.2, p.1),
      left_inv := fun p => by simp, right_inv := fun p => by simp }
  unfold wnorm
  rw [← e.tsum_eq]
  congr 1
  funext p
  simp only [fourier, Equiv.coe_fn_mk, e, neg_neg, Int.cast_neg, abs_neg]
  congr 2
  ring

theorem WSmall.fourier {s ℓ ε : ℝ} {R : Symbol} (h : WSmall ℓ s R ε) :
    WSmall s ℓ (fourier R) ε := by
  refine ⟨?_, by rw [wnorm_fourier]; exact h.2⟩
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    { toFun := fun p => (p.2, -p.1), invFun := fun p => (-p.2, p.1),
      left_inv := fun p => by simp, right_inv := fun p => by simp }
  rw [← e.summable_iff]
  convert h.1 using 2 with p
  simp only [Function.comp_apply, AMO.fourier, Equiv.coe_fn_mk, e, neg_neg, Int.cast_neg,
    abs_neg]
  congr 2
  ring

/-! ### The almost Mathieu symbol -/

/-- The symbol of `U + U^{-1} + η (V + V^{-1})`. -/
def amo (η : ℂ) : Symbol :=
  Pi.single (1, 0) 1 + Pi.single (-1, 0) 1 + Pi.single (0, 1) η + Pi.single (0, -1) η

lemma amo_summable (η : ℂ) : SymbolSummable (amo η) := by
  unfold SymbolSummable
  apply summable_of_ne_finset_zero (s := {(1, 0), (-1, 0), (0, 1), (0, -1)})
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp
  simp [amo, Pi.single_apply, hp.1, hp.2.1, hp.2.2.1, hp.2.2.2]

lemma amo_selfAdjoint (η : ℝ) : SymbolSelfAdjoint (amo η) := by
  intro p
  obtain ⟨a, b⟩ := p
  simp only [amo, Pi.add_apply, Pi.single_apply, Prod.mk.injEq, Prod.neg_mk, map_add]
  split_ifs <;> simp_all <;> omega

/-- Aubry duality of the almost Mathieu operator: `𝓕(H_η) = η · H_{η⁻¹}`. -/
theorem fourier_amo {η : ℂ} (hη : η ≠ 0) : fourier (amo η) = η • amo η⁻¹ := by
  funext p
  obtain ⟨a, b⟩ := p
  simp only [fourier, amo, Pi.add_apply, Pi.smul_apply, Pi.single_apply, Prod.mk.injEq,
    smul_eq_mul]
  split_ifs <;> simp_all <;> omega

/-- The full Hamiltonian `H_x = U + U^{-1} + η(V_x + V_x^{-1}) + R_x`. -/
def H (α η : ℝ) (R : Symbol) (x : ℝ) : L2 ℤ →L[ℂ] L2 ℤ := op α (amo η + R) x

/-- Its Fourier dual `Ĥ_x = 𝓕(H)_x`. -/
def Hdual (α η : ℝ) (R : Symbol) (x : ℝ) : L2 ℤ →L[ℂ] L2 ℤ := op α (fourier (amo η + R)) x

lemma SymbolSummable.add {R R' : Symbol} (h : SymbolSummable R) (h' : SymbolSummable R') :
    SymbolSummable (R + R') :=
  (Summable.add h h').of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => norm_add_le _ _)

lemma symbolSummable_single (p : ℤ × ℤ) (c : ℂ) : SymbolSummable (Pi.single p c) :=
  summable_of_ne_finset_zero (s := {p}) (fun q hq => by
    simp only [Finset.mem_singleton] at hq
    simp [Pi.single_apply, hq])

lemma op_single (α : ℝ) (p : ℤ × ℤ) (c : ℂ) (x : ℝ) :
    op α (Pi.single p c) x = c • W α x p.1 p.2 := by
  unfold op
  rw [tsum_eq_single p]
  · simp
  · intro q hq
    rw [Pi.single_eq_of_ne hq]
    exact zero_smul ℂ (W α x q.1 q.2)

lemma H_eq (α η : ℝ) {R : Symbol} (hR : SymbolSummable R) (x : ℝ) :
    H α η R x = U α x + W α x (-1) 0 + (η : ℂ) • V α x + (η : ℂ) • W α x 0 (-1) + op α R x := by
  have s := symbolSummable_single
  unfold H amo
  rw [op_add ((((s _ _).add (s _ _)).add (s _ _)).add (s _ _)) hR,
    op_add (((s _ _).add (s _ _)).add (s _ _)) (s _ _),
    op_add ((s _ _).add (s _ _)) (s _ _), op_add (s _ _) (s _ _),
    op_single, op_single, op_single, op_single,
    show (1 : ℂ) • W α x (1, (0 : ℤ)).1 (1, (0 : ℤ)).2 = U α x from one_smul ℂ _,
    show (1 : ℂ) • W α x (-1, (0 : ℤ)).1 (-1, (0 : ℤ)).2 = W α x (-1) 0 from one_smul ℂ _]
  rfl

lemma isSelfAdjoint_H (α η : ℝ) {R : Symbol} (hR : SymbolSummable R)
    (hsa : SymbolSelfAdjoint R) (x : ℝ) : IsSelfAdjoint (H α η R x) := by
  refine isSelfAdjoint_op ((amo_summable η).add hR) ?_ x
  · intro p
    simp [amo_selfAdjoint η p, hsa p]

lemma isSelfAdjoint_Hdual (α η : ℝ) {R : Symbol} (hR : SymbolSummable R)
    (hsa : SymbolSelfAdjoint R) (x : ℝ) : IsSelfAdjoint (Hdual α η R x) := by
  have hs : SymbolSummable (amo η + R) := (amo_summable η).add hR
  refine isSelfAdjoint_op hs.fourier (SymbolSelfAdjoint.fourier ?_) x
  intro p
  simp [amo_selfAdjoint η p, hsa p]

end AMO
