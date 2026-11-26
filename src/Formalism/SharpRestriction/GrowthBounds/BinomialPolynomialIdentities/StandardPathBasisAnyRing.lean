module

public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.AdmissiblePolynomialBasisProv
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.RaiseLowerPowCommutatorOnWeight
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.WeightConditionFromIntegralForm

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.StandardPathBasisAnyRing
noncomputable section
open MvPolynomial Finset
open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

namespace Formalism.MainNotions.G.ColumnFamilies

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem standardPath_basis_any_ring (R : Type) [CommRing R] (N n : ℕ) (LL : Letters (Fin N)) (B : Fin N → ℕ) :
    LinearIndependent R (fun x : {x : PPath n N LL B × (ℤ → Finset (Fin n)) // IsSt x.1.mu x.2} =>
      Psi R x.1.1.mu x.1.2) ∧
    Submodule.span R {G | ∃ P : PPath n N LL B, ∃ I : ℤ → Finset (Fin n), IsSt P.mu I ∧ G = Psi R P.mu I} =
      Pol R n B := by
  have hT := restPathTo
  have hF := restPathFrom
  have hS := restStd
  have hP := restPsi
  have hPol := restPol
  obtain ⟨hLI, hSp⟩ := Formalism.InvariantFactorPaths.GelfandTsetlinBases.Top.psiPath_basis n N (isV LL) (Bn B) R
  have hinj : Function.Injective
      (rename (iv N n) : MvPolynomial (Fin N × Fin n) R →ₐ[R] MvPolynomial (ℕ × Fin n) R).toLinearMap :=
    rename_injective _ (iv_inj N n)
  have hfun : (fun x : WIdx n N LL B =>
      (rename (iv N n) : MvPolynomial (Fin N × Fin n) R →ₐ[R] MvPolynomial (ℕ × Fin n) R).toLinearMap
        (Psi R x.1.1.mu x.1.2)) =
      (fun y : Formalism.InvariantFactorPaths.GelfandTsetlinBases.PathIdx n N (isV LL) (Bn B) => Formalism.InvariantFactorPaths.GelfandTsetlinBases.psiPath R (isV LL) y.1.1 N y.1.2) ∘
        (e17 hT hF hS n N LL B) := by
    funext x
    exact rename_Psi hT hF hS hP R x
  constructor
  · have h1 := hLI.comp (e17 hT hF hS n N LL B) (e17 hT hF hS n N LL B).injective
    rw [← hfun] at h1
    exact LinearIndependent.of_comp _ h1
  · apply Submodule.map_injective_of_injective hinj
    rw [hPol R n N B, ← hSp, Submodule.map_span]
    congr 1
    ext G
    constructor
    · rintro ⟨_, ⟨P, I, hI, rfl⟩, rfl⟩
      exact ⟨e17 hT hF hS n N LL B ⟨(P, I), hI⟩, (congrFun hfun ⟨(P, I), hI⟩).symm⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨x, rfl⟩ := (e17 hT hF hS n N LL B).surjective y
      exact ⟨Psi R x.1.1.mu x.1.2, ⟨x.1.1, x.1.2, x.2, rfl⟩, congrFun hfun x⟩

theorem standardPath_index_finite (N n : ℕ) (LL : Letters (Fin N)) (B : Fin N → ℕ) :
    Finite {x : PPath n N LL B × (ℤ → Finset (Fin n)) // IsSt x.1.mu x.2} := by
  have := Formalism.InvariantFactorPaths.GelfandTsetlinBases.Top.pathIdxFinite n N (isV LL) (Bn B)
  exact Finite.of_equiv _ (e17 restPathTo restPathFrom restStd n N LL B).symm

end Formalism.MainNotions.G.ColumnFamilies
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.ContragredientIrreducibleGeneratedByHighestWeigh
noncomputable section

open Finset

namespace Formalism.MainNotions.G.ColumnFamilies

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory

def lowWt {n : ℕ} (mu : Fin n → ℤ) : Fin n → ℤ := fun a => mu (Fin.rev a)

def ContragredientIrreducibleGeneratedByHighestWeight : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
    (_S : UniformizedDVR p O) (n : ℕ) (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V]
    [IsScalarTower O (KK O) V] (E : GLOps n (KK O) V) (mu : Fin n → ℤ) (v : V) (v' : Module.Dual (KK O) V),
    IsIrrHW E mu v → IsHWV (dualOps E) (dualWt mu) v' → IsIrrHW (dualOps E) (dualWt mu) v'

def DualFunctionalInjectiveOnLowestWeightSpace : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
    (_S : UniformizedDVR p O) (n : ℕ) (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V]
    [IsScalarTower O (KK O) V] (E : GLOps n (KK O) V) (mu : Fin n → ℤ) (v : V) (v' : Module.Dual (KK O) V),
    IsIrrHW E mu v → IsHWV (dualOps E) (dualWt mu) v' →
    (∀ x ∈ weightSp E (lowWt mu), v' x = 0 → x = 0) ∧ ∀ nu, nu ≠ lowWt mu → ∀ x ∈ weightSp E nu, v' x = 0

def LowestWeightExtremalVector : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
    (_S : UniformizedDVR p O) (n : ℕ) (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V]
    [IsScalarTower O (KK O) V] (E : GLOps n (KK O) V) (mu : Fin n → ℤ) (v : V),
    IsIrrHW E mu v →
    ∃ w ∈ Delta (O := O) E v, w ∈ weightSp E (lowWt mu) ∧ ∃ u ∈ UZmon E, u w = v

def DeltaGeneratedByLowestWeightVector : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
    (_S : UniformizedDVR p O) (n : ℕ) (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V]
    [IsScalarTower O (KK O) V] (E : GLOps n (KK O) V) (mu : Fin n → ℤ) (v : V) (v' : Module.Dual (KK O) V),
    IsIrrHW E mu v → IsHWV (dualOps E) (dualWt mu) v' →
    v' '' (Delta (O := O) E v : Set V) = Set.range (algebraMap O (KK O)) →
    ∃ x0 ∈ Delta (O := O) E v, x0 ∈ weightSp E (lowWt mu) ∧ v' x0 = 1 ∧
      Delta (O := O) E v = Submodule.span O {x | ∃ u ∈ UZmon E, x = u x0}

def DeltaFinitelyGenerated : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
    (_S : UniformizedDVR p O) (n : ℕ) (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V]
    [IsScalarTower O (KK O) V] (E : GLOps n (KK O) V) (mu : Fin n → ℤ) (v : V) (v' : Module.Dual (KK O) V),
    IsIrrHW E mu v → IsHWV (dualOps E) (dualWt mu) v' →
    v' '' (Delta (O := O) E v : Set V) = Set.range (algebraMap O (KK O)) → (Delta (O := O) E v).FG

def NablaContragredientEqDualLatticeDelta : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
    (_S : UniformizedDVR p O) (n : ℕ) (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V]
    [IsScalarTower O (KK O) V] (E : GLOps n (KK O) V) (mu : Fin n → ℤ) (v : V) (v' : Module.Dual (KK O) V),
    IsIrrHW E mu v → IsHWV (dualOps E) (dualWt mu) v' →
    v' '' (Delta (O := O) E v : Set V) = Set.range (algebraMap O (KK O)) →
    Nabla (O := O) (dualOps E) (dualWt mu) v' =
      {φ | ∀ x ∈ Delta (O := O) E v, φ x ∈ Set.range (algebraMap O (KK O))}

def LatticeBiduality : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (V : Type) [AddCommGroup V]
    [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V] (M : Submodule O V), M.FG →
    Submodule.span (KK O) (M : Set V) = ⊤ →
    (M : Set V) = {x | ∀ φ : Module.Dual (KK O) V, (∀ y ∈ M, φ y ∈ Set.range (algebraMap O (KK O))) →
      φ x ∈ Set.range (algebraMap O (KK O))}

end Formalism.MainNotions.G.ColumnFamilies
end
end
