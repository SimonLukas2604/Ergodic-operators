/-
# `𝒲_{s,ℓ}` as a Banach algebra

The weighted symbol space, with the twisted product as multiplication, is a complete normed
ring.  This packages `Weights.mul` (associative, unital, distributive, submultiplicative) as a
`NormedRing` instance on a type synonym, so that general Banach-algebra results (Neumann series,
the Green series of `TailInverse.lean`, matrices over the algebra) apply verbatim.
Everything here is proved.
-/
import AnalyticPerturbationsAMO.WeightedSpace

noncomputable section

namespace AMO

/-- The Banach algebra `𝒲_{s,ℓ}` with frequency `α`. -/
def WAlg (_ω : Weights) (_α : ℝ) : Type := WA

namespace WAlg

variable (ω : Weights) (α : ℝ)

instance : NormedAddCommGroup (WAlg ω α) := inferInstanceAs (NormedAddCommGroup WA)
instance : NormedSpace ℂ (WAlg ω α) := inferInstanceAs (NormedSpace ℂ WA)
instance : CompleteSpace (WAlg ω α) := inferInstanceAs (CompleteSpace WA)

/-- The underlying element of `WA`. -/
def toWA : WAlg ω α → WA := id
/-- An element of `WA` viewed in the algebra. -/
def ofWA : WA → WAlg ω α := id

instance : Mul (WAlg ω α) := ⟨fun f g => ω.mul α f g⟩
instance : One (WAlg ω α) := ⟨ω.one'⟩

lemma mul_def (f g : WAlg ω α) : f * g = (ω.mul α f g : WA) := rfl
lemma one_def : (1 : WAlg ω α) = (ω.one' : WA) := rfl

instance instAddCommGroup : AddCommGroup (WAlg ω α) := inferInstanceAs (AddCommGroup WA)

instance instRing : Ring (WAlg ω α) :=
  { (inferInstance : AddCommGroup (WAlg ω α)) with
    mul := (· * ·)
    one := 1
    mul_assoc := fun f g h => ω.mul_assoc' α f g h
    one_mul := fun f => ω.one'_mul α f
    mul_one := fun f => ω.mul_one' α f
    left_distrib := fun f g h => ω.mul_add α f g h
    right_distrib := fun f g h => ω.add_mul α f g h
    zero_mul := fun f => ω.zero_mul' α f
    mul_zero := fun f => ω.mul_zero' α f }

instance instNormedRing : NormedRing (WAlg ω α) :=
  { (inferInstance : NormedAddCommGroup (WAlg ω α)), (inferInstance : Ring (WAlg ω α)) with
    norm_mul_le := fun f g => ω.norm_mul_le α f g }

lemma norm_one : ‖(1 : WAlg ω α)‖ = 1 := by
  change ‖ω.one'‖ = 1
  rw [Weights.one', Weights.norm_ofS, wnorm_one]

/-- The symbol represented by an element of the algebra. -/
def sym (f : WAlg ω α) : Symbol := ω.toS f

lemma sym_mul (f g : WAlg ω α) : sym ω α (f * g) = tmul α (sym ω α f) (sym ω α g) :=
  ω.toS_mul α f g

lemma sym_add (f g : WAlg ω α) : sym ω α (f + g) = sym ω α f + sym ω α g := ω.toS_add f g

lemma sym_sub (f g : WAlg ω α) : sym ω α (f - g) = sym ω α f - sym ω α g := ω.toS_sub f g

lemma sym_one : sym ω α 1 = one := ω.toS_one'

lemma sym_injective : Function.Injective (sym ω α) := ω.toS_injective

lemma norm_eq_wnorm (f : WAlg ω α) : ‖f‖ = wnorm ω.s ω.ℓ (sym ω α f) :=
  (ω.wnorm_toS f).symm

/-- `𝒲_{s,ℓ}` is a normed `ℂ`-algebra (needed for holomorphic dependence on the energy). -/
instance instAlgebra : Algebra ℂ (WAlg ω α) :=
  Algebra.ofModule (fun c f g => ω.smul_mul α c f g) (fun c f g => ω.mul_smul α c f g)

instance instNormedAlgebra : NormedAlgebra ℂ (WAlg ω α) :=
  { instAlgebra ω α with norm_smul_le := fun c f => norm_smul_le c f }

lemma sym_smul (c : ℂ) (f : WAlg ω α) : sym ω α (c • f) = c • sym ω α f := ω.toS_smul c f

end WAlg

end AMO
