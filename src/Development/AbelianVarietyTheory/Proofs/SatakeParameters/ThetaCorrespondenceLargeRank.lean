module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FormsBaseChange
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CoeEqAlgebraMapZeroEquiv

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaCorrespondenceLargeRank
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.Published
open scoped TensorProduct

namespace GlobalTheory.ThetaLiftGL

theorem compactOpen_basis (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) :
    ∀ U ∈ nhds (1 : GL (Fin n) k), ∃ K : Subgroup (GL (Fin n) k),
      IsOpen (K : Set (GL (Fin n) k)) ∧ IsCompact (K : Set (GL (Fin n) k)) ∧ (K : Set (GL (Fin n) k)) ⊆ U := by
  intro U hU
  obtain ⟨J, h1, h2, h3, -⟩ := exists_open_normalised_subgroup_subset k (Fin n) U hU
  exact ⟨J, h1, SplitFlip.isCompact_KO.of_isClosed_subset (J.isClosed_of_isOpen h1) h3, h2⟩

end GlobalTheory.ThetaLiftGL
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OmegaPullId
open CategoryTheory AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.HodgeCoh

set_option autoImplicit false

namespace GlobalTheory.HodgeCoh
open GlobalTheory.CechDR

variable {k : Type} [CommRing k] {X : Scheme.{0}}

theorem formPull_id (s : X ⟶ Sp k) (j : ℕ) (U : X.Opens) (x : OmU s U j) :
    formPull (f := 𝟙 X) (Category.id_comp s) U j x = x :=
  SemiHom.mOm_id _ (fun _ ↦ rfl) x

theorem omegaPull_id (s : X ⟶ Sp k) (j : ℕ) :
    omegaPull (f := 𝟙 X) (Category.id_comp s) j =
      (Scheme.Modules.pushforwardId X).inv.app (Omega s j) := by
  refine (Equiv.symm_apply_eq _).2 ?_
  refine Eq.trans ?_ (Adjunction.homEquiv_unit _ _ _ _).symm
  ext U x
  exact congrArg ((toOmega s j).app U).hom (formPull_id s j U.unop x)

theorem hodgePull_id (s : X ⟶ Sp k) (j q : ℕ) (x : hodgeH s j q) :
    hodgePull (f := 𝟙 X) (Category.id_comp s) j q x = x := by
  letI := algΓ s
  apply (cohOn.toH' (Omega s j) ⊤ q).injective
  refine (cohOn.toH'_pull (appTop_algebraMap (Category.id_comp s))
    (omegaPull (Category.id_comp s) j) (le_refl ((𝟙 X) ⁻¹ᵁ ⊤)) (n := q) x).trans ?_
  rw [omegaPull_id]
  exact (SheafPull.pull_id (X := X.toTopCat) (𝟙 ((toAbSheaf X).obj (Omega s j))) q
    (homOfLE (le_refl ⊤)) _).trans (by rw [SheafLES.map_id]; exact SheafLES.res_id _ _ _)

end GlobalTheory.HodgeCoh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HodgePullHodgePull
open CategoryTheory AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.HodgeCoh GlobalTheory.CechDR

set_option autoImplicit false

namespace GlobalTheory.HodgeCoh
variable {k : Type} [CommRing k] {X X' X'' : Scheme.{0}} {s : X ⟶ Sp k} {s' : X' ⟶ Sp k}
  {s'' : X'' ⟶ Sp k} {f : X' ⟶ X} {g : X'' ⟶ X'}

theorem formPull_formPull (hf : f ≫ s = s') (hg : g ≫ s' = s'') (hgf : (g ≫ f) ≫ s = s'')
    (U : X.Opens) (j : ℕ) (x : OmU s U j) :
    formPull hg (f ⁻¹ᵁ U) j (formPull hf U j x) = formPull hgf U j x := by
  refine SemiHom.mOm_mOm (semiHom_appSec hf U) (semiHom_appSec hg (f ⁻¹ᵁ U))
    (semiHom_appSec hgf U) (fun b ↦ ?_) x
  change (f.app U ≫ g.app (f ⁻¹ᵁ U)).hom b = ((g ≫ f).app U).hom b
  rw [Scheme.Hom.comp_app]
  rfl

theorem omega_hom_ext {j : ℕ} {M : X.Modules} (φ ψ : Omega s j ⟶ M)
    (h : ∀ (U : X.Opens) (x : OmU s U j), φ.val.app (op U) ((toOmega s j).app (op U) x) =
      ψ.val.app (op U) ((toOmega s j).app (op U) x)) : φ = ψ := by
  apply ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv _ _).injective
  have e₁ := (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv_unit
    (formsPre s j) M φ
  have e₂ := (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv_unit
    (formsPre s j) M ψ
  refine e₁.trans (Eq.trans ?_ e₂.symm)
  ext U x
  exact h U.unop x

theorem omegaPull_comp (hf : f ≫ s = s') (hg : g ≫ s' = s'') (hgf : (g ≫ f) ≫ s = s'')
    (j : ℕ) :
    omegaPull hgf j = omegaPull hf j ≫ (Scheme.Modules.pushforward f).map (omegaPull hg j) := by
  refine omega_hom_ext _ _ fun U x ↦ ?_
  rw [omegaPull_toOmega]
  change _ = (omegaPull hg j).val.app (op (f ⁻¹ᵁ U)) ((omegaPull hf j).val.app (op U) ((toOmega s j).app (op U) x))
  rw [omegaPull_toOmega, omegaPull_toOmega, formPull_formPull hf hg hgf]
  rfl

theorem hodgePull_comp (hf : f ≫ s = s') (hg : g ≫ s' = s'') (hgf : (g ≫ f) ≫ s = s'')
    (j q : ℕ) (x : hodgeH s j q) :
    hodgePull hg j q (hodgePull hf j q x) = hodgePull hgf j q x := by
  letI := algΓ s; letI := algΓ s'; letI := algΓ s''
  apply (cohOn.toH' (Omega s'' j) ⊤ q).injective
  have e₁ := cohOn.toH'_pull (σ := RingHom.id k) (appTop_algebraMap hg) (omegaPull hg j)
    (le_refl (g ⁻¹ᵁ ⊤)) (hodgePull hf j q x)
  have e₂ := cohOn.toH'_pull (σ := RingHom.id k) (appTop_algebraMap hf) (omegaPull hf j)
    (le_refl (f ⁻¹ᵁ ⊤)) x
  have e₃ := cohOn.toH'_pull (σ := RingHom.id k) (appTop_algebraMap hgf) (omegaPull hgf j)
    (le_refl ((g ≫ f) ⁻¹ᵁ ⊤)) x
  refine e₁.trans (Eq.trans ?_ e₃.symm)
  refine (congrArg (SheafPull.pull.{0, 0} g.base (toAbSheafPush (omegaPull hg j)) q _) e₂).trans ?_
  refine (SheafPull.pull_pull.{0, 0, 0} f.base g.base _ _ q _ _ _).trans ?_
  rw [omegaPull_comp hf hg hgf]
  rfl

theorem hodgePull_hodgePull {X X' X'' : Scheme.{0}} (s : X ⟶ Sp k) (f : X' ⟶ X)
    (g : X'' ⟶ X') (j q : ℕ) (x : hodgeH s j q) :
    hodgePull (s' := g ≫ f ≫ s) rfl j q (hodgePull (s' := f ≫ s) rfl j q x) =
      hodgePull (f := g ≫ f) (s' := g ≫ f ≫ s) (Category.assoc g f s) j q x :=
  hodgePull_comp rfl rfl (Category.assoc g f s) j q x

end GlobalTheory.HodgeCoh
end
