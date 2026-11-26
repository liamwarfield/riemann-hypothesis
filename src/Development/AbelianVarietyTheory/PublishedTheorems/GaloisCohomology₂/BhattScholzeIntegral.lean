module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormLeOneOfMemOL
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalPeriodRingsDataUnramifiedLaws
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrobeniusPeriodRingInjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSumRootsOfUnity

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.Per GlobalTheory.Prism

namespace GlobalTheory.Published

def BhattScholzeIntegral : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (P₀ : Obj l ↥(OL K)) (e : P₀.A ≃+* Ainf l), IsAinf K P₀ e →
    (∀ (P : LocPrime l) (AI : LocAinf l P), IsStd P AI →
      ∀ (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V]
        [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V]
        (ρ : Representation ℚ_[l] ↥(GK K) V) (L : Lattice (O := ℤ_[l]) ρ),
        (∀ x, Continuous fun g => ρ g x) → IsCrys (P.PD K) ρ →
        ∃ (E : FCrys l ↥(OL K))
          (j : E.M P₀ →ₛₗ[(inclW l).comp e.toRingHom] (WCb l ⊗[ℤ_[l]] ↥L.T)),
          Realises K E P₀ e ↥L.T (fun g => actT L g) j) ∧
    (∀ (T T' : Type) [AddCommGroup T] [Module ℤ_[l] T] [AddCommGroup T'] [Module ℤ_[l] T']
      (ρ : ↥(GK K) → (T →ₗ[ℤ_[l]] T)) (ρ' : ↥(GK K) → (T' →ₗ[ℤ_[l]] T'))
      (E E' : FCrys l ↥(OL K))
      (j : E.M P₀ →ₛₗ[(inclW l).comp e.toRingHom] (WCb l ⊗[ℤ_[l]] T))
      (j' : E'.M P₀ →ₛₗ[(inclW l).comp e.toRingHom] (WCb l ⊗[ℤ_[l]] T')),
      Realises K E P₀ e T ρ j → Realises K E' P₀ e T' ρ' j' →
      ∀ f : T →ₗ[ℤ_[l]] T', (∀ g x, f (ρ g x) = ρ' g (f x)) →
        ∃! u : FHom E E', ∀ x, j' (u.u P₀ x) = f.lTensor (WCb l) (j x))

end GlobalTheory.Published
end
end

section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.Published

def PhiSubOneOntoFilZero {l : ℕ} [Fact l.Prime] (C : Core l) : Prop :=
  ∀ y : Per.Bcris l, ∃ x : Per.Bcris l, C.ι x ∈ Per.FilD l 0 ∧ Per.φB l x - x = y

def FontaineBcris : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (C : Core l),
    C.TensorInj ∧ C.PhiInj ∧ C.IotaInj ∧ C.Fund ∧ PhiSubOneOntoFilZero C ∧ C.FundOnto ∧ C.Regular

namespace FontaineBcris

variable {l : ℕ} [Fact l.Prime]

theorem tensorInj (h : FontaineBcris) (C : Core l) : C.TensorInj := (h l C).1

theorem iotaInj (h : FontaineBcris) (C : Core l) : C.IotaInj := (h l C).2.2.1

theorem ontoFilZero (h : FontaineBcris) (C : Core l) : PhiSubOneOntoFilZero C := (h l C).2.2.2.2.1

theorem fundOnto (h : FontaineBcris) (C : Core l) : C.FundOnto := (h l C).2.2.2.2.2.1

theorem regular (h : FontaineBcris) (C : Core l) : C.Regular := (h l C).2.2.2.2.2.2

theorem oneSubPhiOnto_of_filZero {C : Core l} (h : PhiSubOneOntoFilZero C) : C.OneSubPhiOnto := by
  intro y
  obtain ⟨x, -, hx⟩ := h (-y)
  exact ⟨x, by rw [← neg_sub, hx, neg_neg]⟩

theorem filZero_of_onto {C : Core l} (h1 : C.OneSubPhiOnto) (h2 : C.FundOnto) : PhiSubOneOntoFilZero C := by
  intro y
  obtain ⟨x, hx⟩ := h1 y
  obtain ⟨b, hb, hF⟩ := h2 (C.ι x)
  refine ⟨b - x, by rwa [map_sub], ?_⟩
  rw [map_sub, hb, ← hx]
  ring

theorem of_rest (h : ∀ (l : ℕ) [Fact l.Prime] (C : Core l),
    C.TensorInj ∧ C.Fund ∧ C.FundOnto ∧ C.Regular) : FontaineBcris := fun l _ C =>
  ⟨(h l C).1, phiB_injective l, (ULaws.u_laws l C).2.2.2.1, (h l C).2.1,
    filZero_of_onto (one_sub_phi_onto l C) (h l C).2.2.1, (h l C).2.2.1, (h l C).2.2.2⟩

end FontaineBcris

end GlobalTheory.Published
end
end

section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.LocalSituation TensorProduct GlobalTheory.Per GlobalTheory.Prism

namespace GlobalTheory.Published

def BhattScholzeCrystallineLattices : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (P₀ : Obj l ↥(OL K)) (e : P₀.A ≃+* Ainf l), IsAinf K P₀ e →
    (∀ (P : LocPrime l) (AI : LocAinf l P), IsStd P AI →
      ∀ (LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys (P.PD K) T.ρ →
        letI := zlMod LL T
        ∃ (E : FCrys l ↥(OL K))
          (j : E.M P₀ →ₛₗ[(inclW l).comp e.toRingHom] (WCb l ⊗[ℤ_[l]] ↥T.L.T)),
          Realises K E P₀ e ↥T.L.T (fun g => actTZ LL T g) j) ∧
    (∀ (T T' : Type) [AddCommGroup T] [Module ℤ_[l] T] [AddCommGroup T'] [Module ℤ_[l] T']
      (ρ : ↥(GK K) → (T →ₗ[ℤ_[l]] T)) (ρ' : ↥(GK K) → (T' →ₗ[ℤ_[l]] T'))
      (E E' : FCrys l ↥(OL K))
      (j : E.M P₀ →ₛₗ[(inclW l).comp e.toRingHom] (WCb l ⊗[ℤ_[l]] T))
      (j' : E'.M P₀ →ₛₗ[(inclW l).comp e.toRingHom] (WCb l ⊗[ℤ_[l]] T')),
      Realises K E P₀ e T ρ j → Realises K E' P₀ e T' ρ' j' →
      ∀ f : T →ₗ[ℤ_[l]] T', (∀ g x, f (ρ g x) = ρ' g (f x)) →
        ∃! u : FHom E E', ∀ x, j' (u.u P₀ x) = f.lTensor (WCb l) (j x))

end GlobalTheory.Published
end
end
