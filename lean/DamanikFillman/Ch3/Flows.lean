/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# §3.9 Flows, suspensions, and the Schwartzman homomorphism (book pp. 292–305)

Continuous flows are Mathlib's `Flow ℝ Ω` (`ϕ (s + t) x = ϕ s (ϕ t x)`).

Main definitions:
* `DF.FlowErgodic ϕ μ` — ergodicity of a measure-preserving flow (§3.9.1);
* `DF.FlowCocycle ϕ` — `SL(2, ℝ)` cocycles over a flow, (3.9.4)–(3.9.5);
* `DF.FlowUniformExpGrowth`, `DF.FlowBoundedOrbit` — Definition 3.9.4;
* `DF.suspSetoid T`, `DF.Suspension T`, `DF.suspFlow T` — the suspension `S(Ω, T)` of a
  topological dynamical system and its translation flow (Definition 3.9.6);
* `DF.IsLiftAlong`, `DF.HasRotationNumber` — lifts of `φ ∘ ϕ_t(ω)` and rotation numbers (3.9.32).

Main results:
* `DF.suspFlow_one` — (3.9.14): the time-one map of the suspension flow acts on fibres as `T`;
* `DF.homotopic_add` — **Proposition 3.9.8(a)**: homotopy is compatible with pointwise addition in
  `C(Ω, 𝕋)`;
* `DF.homotopic_of_eq_add_proj` — the easy direction of **Proposition 3.9.9**;
* `DF.isLiftAlong_add_int` — lifts can be shifted by integers.

Statements: `DF.FlowBirkhoffStatement` (Theorem 3.9.2) is stated only. `DF.FlowUHStatement`
(Theorem 3.9.5, items (a), (c), (d)) is **proved** in `DamanikFillman.Ch3.FlowUH` (`DF.flowUH`). `DF.SuspensionErgodicStatement` (Lemma 3.9.7) is **proved**
in `DamanikFillman.Ch3.Suspension` (`DF.suspension_ergodic`).
`DF.HomotopyLiftStatement` (Proposition 3.9.9, converse direction) and `DF.SchwartzmanStatement`
(Theorem 3.9.13) are **proved** in `DamanikFillman.Ch3.Schwartzman` (`DF.homotopyLiftStatement`,
`DF.schwartzman`).
-/
import DamanikFillman.Ch3.Cocycle

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Filter Set Function Topology unitInterval
open scoped Matrix.Norms.L2Operator

namespace DF

open Cocycle

variable {Ω : Type*} [TopologicalSpace Ω]

/-! ### Measure-preserving and ergodic flows -/

/-- A flow is *measure-preserving* if every `ϕ_t` preserves `μ`. -/
def FlowMeasurePreserving [MeasurableSpace Ω] (ϕ : Flow ℝ Ω) (μ : Measure Ω) : Prop :=
  ∀ t : ℝ, MeasurePreserving (ϕ t) μ μ

/-- A measure-preserving flow is *ergodic* if every measurable set `E` with `ϕ_t E = E` for all
`t` is null or conull (§3.9.1). -/
def FlowErgodic [MeasurableSpace Ω] (ϕ : Flow ℝ Ω) (μ : Measure Ω) : Prop :=
  FlowMeasurePreserving ϕ μ ∧
    ∀ E : Set Ω, MeasurableSet E → (∀ t : ℝ, ϕ t ⁻¹' E = E) → μ E = 0 ∨ μ Eᶜ = 0

/-- **Theorem 3.9.2** (Birkhoff's theorem for flows): for an ergodic flow and `f ∈ L¹`,
`(1/t) ∫₀ᵗ f(ϕ_s ω) ds → E(f)` for a.e. `ω`. Stated, not proved. -/
def FlowBirkhoffStatement : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] (ϕ : Flow ℝ X)
    (μ : Measure X) [IsProbabilityMeasure μ], FlowErgodic ϕ μ →
    ∀ f : X → ℝ, Integrable f μ → ∀ᵐ x ∂μ,
      Tendsto (fun t : ℝ => (1 / t) * ∫ s in (0 : ℝ)..t, f (ϕ s x)) atTop (𝓝 (∫ y, f y ∂μ))

/-! ### Cocycles over flows -/

/-- Example 3.9.3: an `SL(2, ℝ)` cocycle over the flow `ϕ` is a map `Φ : Ω × ℝ → SL(2, ℝ)` with
`Φ(ω, 0) = I` (3.9.4) and `Φ(ω, s + t) = Φ(ϕ_s ω, t) Φ(ω, s)` (3.9.5). -/
structure FlowCocycle (ϕ : Flow ℝ Ω) where
  /-- the cocycle `Φ_t(ω) = Φ(ω, t)` -/
  toFun : Ω → ℝ → SL2R
  map_zero : ∀ ω, toFun ω 0 = 1
  map_add : ∀ ω s t, toFun ω (s + t) = toFun (ϕ s ω) t * toFun ω s

/-- Definition 3.9.4: uniform exponential growth `‖Φ_t(ω)‖ ≥ C λ^{|t|}`. -/
def FlowUniformExpGrowth {ϕ : Flow ℝ Ω} (Φ : FlowCocycle ϕ) : Prop :=
  ∃ C > (0 : ℝ), ∃ l > (1 : ℝ), ∀ (t : ℝ) (ω : Ω), C * l ^ |t| ≤ ‖((Φ.toFun ω t : SL2R) : M2R)‖

/-- Definition 3.9.4: `Φ` enjoys a bounded orbit if `sup_t ‖Φ_t(ω) v‖ < ∞` for some `ω` and some
unit vector `v` (3.9.9). -/
def FlowBoundedOrbit {ϕ : Flow ℝ Ω} (Φ : FlowCocycle ϕ) : Prop :=
  ∃ ω : Ω, ∃ v : EuclideanSpace ℝ (Fin 2), ‖v‖ = 1 ∧
    BddAbove (range fun t : ℝ => ‖act ((Φ.toFun ω t : SL2R) : M2R) v‖)

/-- **Theorem 3.9.5** (items (a), (c), (d)): for a continuous cocycle `Φ` over a continuous flow on
a compact metric space, uniform exponential growth, absence of bounded orbits, and uniform
hyperbolicity (uniform exponential growth) of the time-one cocycle `(ϕ_1, Φ_1)` are equivalent.
Stated, not proved. -/
def FlowUHStatement : Prop :=
  ∀ (X : Type) [MetricSpace X] [CompactSpace X] (ϕ : Flow ℝ X) (Φ : FlowCocycle ϕ),
    Continuous (fun p : X × ℝ => ((Φ.toFun p.1 p.2 : SL2R) : M2R)) →
      (FlowUniformExpGrowth Φ ↔ ¬ FlowBoundedOrbit Φ) ∧
      (FlowUniformExpGrowth Φ ↔ UniformExpGrowth (ϕ.toHomeomorph 1) (fun ω => Φ.toFun ω 1))

/-! ### The suspension (Definition 3.9.6) -/

section suspension

variable (T : Ω ≃ₜ Ω)

/-- The equivalence relation (3.9.11) on `Ω × ℝ`: `(ω, t) ∼ (Tⁿω, t - n)`, `n ∈ ℤ`. -/
def suspSetoid : Setoid (Ω × ℝ) where
  r p q := ∃ n : ℤ, q = (T.flow n p.1, p.2 - n)
  iseqv := by
    refine ⟨fun p => ⟨0, by simp [Homeomorph.flow_apply]⟩, ?_, ?_⟩
    · rintro p q ⟨n, rfl⟩
      refine ⟨-n, Prod.ext ?_ ?_⟩
      · show p.1 = (T.flow (-n)) ((T.flow n) p.1)
        rw [← Flow.map_add, neg_add_cancel, Flow.map_zero_apply]
      · show p.2 = p.2 - n - ((-n : ℤ) : ℝ)
        push_cast; ring
    · rintro p q r ⟨n, rfl⟩ ⟨m, rfl⟩
      refine ⟨m + n, Prod.ext ?_ ?_⟩
      · show (T.flow m) ((T.flow n) p.1) = (T.flow (m + n)) p.1
        rw [Flow.map_add]
      · show p.2 - n - m = p.2 - ((m + n : ℤ) : ℝ)
        push_cast; ring

/-- The suspension `S(Ω, T) = (Ω × ℝ)/∼` (3.9.13). -/
def Suspension : Type _ := Quotient (suspSetoid T)

instance : TopologicalSpace (Suspension T) := instTopologicalSpaceQuotient

/-- The class `[ω, s] ∈ S(Ω, T)`. -/
def suspMk (ω : Ω) (s : ℝ) : Suspension T := Quotient.mk (suspSetoid T) (ω, s)

/-- The translation flow `T_t [ω, s] = [ω, s + t]` on the suspension (as a family of maps). -/
def suspFlow (t : ℝ) : Suspension T → Suspension T :=
  Quotient.map (fun p : Ω × ℝ => (p.1, p.2 + t)) (by
    rintro p q ⟨n, rfl⟩
    exact ⟨n, by simp only [Prod.mk.injEq, true_and]; ring⟩)

lemma suspFlow_mk (t : ℝ) (ω : Ω) (s : ℝ) : suspFlow T t (suspMk T ω s) = suspMk T ω (s + t) :=
  rfl

lemma suspFlow_add (t₁ t₂ : ℝ) (x : Suspension T) :
    suspFlow T (t₁ + t₂) x = suspFlow T t₂ (suspFlow T t₁ x) := by
  induction x using Quotient.inductionOn with
  | h p => exact congrArg (Quotient.mk _) (by simp only [Prod.mk.injEq, true_and]; ring)

lemma suspFlow_zero (x : Suspension T) : suspFlow T 0 x = x := by
  induction x using Quotient.inductionOn with
  | h p => exact congrArg (Quotient.mk _) (by simp)

/-- (3.9.14): `T_1 [ω, s] = [ω, s + 1] = [Tω, s]`: the time-one map preserves each fibre and acts
on it as `T`. -/
theorem suspFlow_one (ω : Ω) (s : ℝ) : suspFlow T 1 (suspMk T ω s) = suspMk T (T ω) s := by
  rw [suspFlow_mk]
  apply Quotient.sound
  refine ⟨1, ?_⟩
  simp only [Prod.mk.injEq]
  constructor
  · simp [Homeomorph.flow_apply]
  · push_cast; ring

/-- **Lemma 3.9.7**: the suspension `μ̄ = ∫₀¹ μ_s ds` of a `T`-invariant (resp. ergodic) measure
`μ` is invariant (resp. ergodic) for the suspension flow; here `μ̄` is the push-forward of
`μ × Leb|_{[0,1)}` under the quotient map. Stated, not proved. -/
def SuspensionErgodicStatement : Prop :=
  ∀ (X : Type) [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (S : X ≃ₜ X) (μ : Measure X) [IsProbabilityMeasure μ],
    letI : MeasurableSpace (Suspension S) := borel _
    let μbar : Measure (Suspension S) :=
      (μ.prod (volume.restrict (Ico (0 : ℝ) 1))).map (fun p => suspMk S p.1 p.2)
    (MeasurePreserving S μ μ → ∀ t, MeasurePreserving (suspFlow S t) μbar μbar) ∧
    (Ergodic S μ → ∀ E : Set (Suspension S), MeasurableSet E →
      (∀ t, suspFlow S t ⁻¹' E = E) → μbar E = 0 ∨ μbar Eᶜ = 0)

end suspension

/-! ### Homotopy classes of maps into the circle -/

section homotopy

/-- **Proposition 3.9.8(a)**: if `φⱼ ≃ φⱼ'` (homotopic) for `j = 1, 2`, then
`φ₁ + φ₂ ≃ φ₁' + φ₂'` in `C(Ω, 𝕋)`. -/
theorem homotopic_add {φ₁ φ₂ φ₁' φ₂' : C(Ω, UnitAddCircle)}
    (h₁ : φ₁.Homotopic φ₁') (h₂ : φ₂.Homotopic φ₂') : (φ₁ + φ₂).Homotopic (φ₁' + φ₂') := by
  obtain ⟨F₁⟩ := h₁
  obtain ⟨F₂⟩ := h₂
  exact ⟨{ toFun := fun p => F₁ p + F₂ p
           continuous_toFun := F₁.continuous.add F₂.continuous
           map_zero_left := fun x => by simp
           map_one_left := fun x => by simp }⟩

/-- **Proposition 3.9.9** (easy direction): if `φ = φ' + π ∘ ψ` with `ψ : Ω → ℝ` continuous, then
`φ` and `φ'` are homotopic. -/
theorem homotopic_of_eq_add_proj {φ φ' : C(Ω, UnitAddCircle)} (ψ : C(Ω, ℝ))
    (h : ∀ ω, φ ω = φ' ω + (ψ ω : UnitAddCircle)) : φ.Homotopic φ' := by
  refine ⟨{ toFun := fun p => φ p.2 - (((p.1 : ℝ) * ψ p.2 : ℝ) : UnitAddCircle)
            continuous_toFun := ?_
            map_zero_left := fun x => by simp
            map_one_left := fun x => by simp [h] }⟩
  exact (φ.continuous.comp continuous_snd).sub
    (continuous_quotient_mk'.comp ((continuous_subtype_val.comp continuous_fst).mul
      (ψ.continuous.comp continuous_snd)))

/-- **Proposition 3.9.9** (converse direction): two homotopic maps `Ω → 𝕋` differ by `π ∘ ψ` for
a continuous `ψ : Ω → ℝ` (Ω a compact metric space). Stated, not proved. -/
def HomotopyLiftStatement : Prop :=
  ∀ (X : Type) [MetricSpace X] [CompactSpace X] (φ φ' : C(X, UnitAddCircle)),
    φ.Homotopic φ' → ∃ ψ : C(X, ℝ), ∀ x, φ x = φ' x + (ψ x : UnitAddCircle)

/-- `g : ℝ → ℝ` is a continuous lift of `t ↦ φ(ϕ_t ω)` (3.9.29). -/
def IsLiftAlong (ϕ : Flow ℝ Ω) (φ : C(Ω, UnitAddCircle)) (ω : Ω) (g : ℝ → ℝ) : Prop :=
  Continuous g ∧ ∀ t, (g t : UnitAddCircle) = φ (ϕ t ω)

lemma isLiftAlong_add_int {ϕ : Flow ℝ Ω} {φ : C(Ω, UnitAddCircle)} {ω : Ω} {g : ℝ → ℝ}
    (hg : IsLiftAlong ϕ φ ω g) (n : ℤ) : IsLiftAlong ϕ φ ω (fun t => g t + n) := by
  refine ⟨hg.1.add continuous_const, fun t => ?_⟩
  rw [AddCircle.coe_add, hg.2 t]
  simp

/-- The rotation number `rot(φ; ω) = lim_{t → ∞} g(t)/t` of `φ` along the orbit of `ω` exists
and equals `r` (3.9.32), for every lift `g`. -/
def HasRotationNumber (ϕ : Flow ℝ Ω) (φ : C(Ω, UnitAddCircle)) (ω : Ω) (r : ℝ) : Prop :=
  ∀ g, IsLiftAlong ϕ φ ω g → Tendsto (fun t => g t / t) atTop (𝓝 r)

/-- **Theorem 3.9.13** (the Schwartzman homomorphism): for a continuous flow on a compact metric
space and an ergodic measure `μ`, there is `A_μ : C(Ω, 𝕋) → ℝ` such that `rot(φ; ω) = A_μ(φ)` for
a.e. `ω` (and every lift), `A_μ` is constant on homotopy classes, and `A_μ` is additive.
Stated, not proved. -/
def SchwartzmanStatement : Prop :=
  ∀ (X : Type) [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (ϕ : Flow ℝ X) (μ : Measure X) [IsProbabilityMeasure μ], FlowErgodic ϕ μ →
    ∃ A : C(X, UnitAddCircle) → ℝ,
      (∀ φ, ∀ᵐ x ∂μ, HasRotationNumber ϕ φ x (A φ)) ∧
      (∀ φ φ', φ.Homotopic φ' → A φ = A φ') ∧
      (∀ φ φ', A (φ + φ') = A φ + A φ')

end homotopy

end DF
