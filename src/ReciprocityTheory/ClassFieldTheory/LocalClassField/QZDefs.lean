module

public import ReciprocityTheory.NeutralLocalFields.Duality
public import ReciprocityTheory.GroupCohomology.ContinuousContractNth

@[expose] public section

section -- merged from ReciprocityTheory.ClassFieldTheory.LocalClassField.QZDefs
namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh ReciprocityTheory.Gal Function

noncomputable section

def trivRep (G : Type) [Group G] [TopologicalSpace G] (A : Type) [AddCommGroup A] : TRep ℤ G :=
  letI : TopologicalSpace A := ⊥
  haveI : DiscreteTopology A := ⟨rfl⟩
  { V := A
    rho := 1
    cont := continuous_snd }

scoped instance (G : Type) [Group G] [TopologicalSpace G] (A : Type) [AddCommGroup A] :
    DiscreteTopology (trivRep G A).V := ⟨rfl⟩

def trivMap (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {A B : Type} [AddCommGroup A]
    [AddCommGroup B] (f : A →+ B) : Pair (trivRep G A) (trivRep G B) :=
  Pair.ofMap (M := trivRep G A) (M' := trivRep G B) f.toIntLinearMap continuous_of_discreteTopology
    fun _ _ => rfl

def charGrp (G : Type) [Group G] [TopologicalSpace G] : AddSubgroup (Additive G →+ QZ) where
  carrier := {χ | IsLocallyConstant fun g : G => χ (Additive.ofMul g)}
  zero_mem' := IsLocallyConstant.const 0
  add_mem' := fun ha hb => IsLocallyConstant.add ha hb
  neg_mem' := fun ha => IsLocallyConstant.neg ha

end

end ReciprocityTheory.DiscreteGroups.LocalClassField
end

section -- merged from ReciprocityTheory.ClassFieldTheory.LocalClassField.KbarRepContAction
namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem kbarRep_contAction : ReciprocityTheory.Gal.ContAction (kbarRep p K) := by
  have hint : Algebra.IsIntegral K (PadicAlgCl p) := Algebra.IsIntegral.tower_top (R := ℚ_[p])
  show Continuous fun q : GK p K × KbarMult p => kbarRep p K q.1 q.2
  rw [continuous_prod_of_discrete_right]
  intro y
  rw [continuous_discrete_rng]
  intro x
  rw [isOpen_iff_mem_nhds]
  intro g0 hg0
  have hop := stabilizer_isOpen_of_isIntegral (K := K) (L := PadicAlgCl p)
    (((Additive.toMul (α := (PadicAlgCl p)ˣ) y : (PadicAlgCl p)ˣ)) : PadicAlgCl p)
  have hn : (fun g : GK p K => g0⁻¹ * g) ⁻¹' (MulAction.stabilizer (GK p K)
      (((Additive.toMul (α := (PadicAlgCl p)ˣ) y : (PadicAlgCl p)ˣ)) : PadicAlgCl p) : Set (GK p K)) ∈ nhds g0 :=
    (hop.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp)
  filter_upwards [hn] with g hg
  have hg' : (g0⁻¹ * g) (((Additive.toMul (α := (PadicAlgCl p)ˣ) y : (PadicAlgCl p)ˣ)) : PadicAlgCl p)
      = (((Additive.toMul (α := (PadicAlgCl p)ˣ) y : (PadicAlgCl p)ˣ)) : PadicAlgCl p) := hg
  have hgg : g (((Additive.toMul (α := (PadicAlgCl p)ˣ) y : (PadicAlgCl p)ˣ)) : PadicAlgCl p)
      = g0 (((Additive.toMul (α := (PadicAlgCl p)ˣ) y : (PadicAlgCl p)ˣ)) : PadicAlgCl p) := by
    have := congrArg g0 hg'
    rw [AlgEquiv.mul_apply] at this
    rw [← this]
    exact (g0.apply_symm_apply _).symm
  have hxy : kbarRep p K g y = kbarRep p K g0 y := Units.ext hgg
  show kbarRep p K g y = x
  rw [hxy]
  exact hg0

noncomputable def kbarT : TRep ℤ (GK p K) where
  V := KbarMult p
  rho := kbarRep p K
  cont := kbarRep_contAction p K

scoped instance : DiscreteTopology (kbarT p K).V := inferInstanceAs (DiscreteTopology (KbarMult p))

end ReciprocityTheory.DiscreteGroups.LocalClassField
end
