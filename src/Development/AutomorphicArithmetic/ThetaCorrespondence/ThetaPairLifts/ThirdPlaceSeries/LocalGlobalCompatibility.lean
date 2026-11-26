module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.JointConditionOfConstituentConditionSplit
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.RankOneOfLong
public import Development.AutomorphicArithmetic.ThetaCorrespondence.CuspidalSupport.CuspOfCq

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalGlobalCompatibility
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace Formalism.MainNotions.PairedCharacterCondition
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
  Module Polynomial
variable {D : D7}
def PairedCharacterConditionAlt (C : ℝ) (CT : ℕ) : Prop :=
  ∀ (i : D.nd.Loc) (k k' : Fin 2), k ≠ k' → D.nd.l i = D.host.g k →
  ∀ (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))),
    GoodR D.nd i r → (∀ π ∈ D.nd.Z i, Formalism.MainNotions.TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) →
  ∀ (eta s S : ℕ) (sg : HeightOneSpectrum (𝓞 D.host.E) → Bool)
    (U : HeightOneSpectrum (𝓞 D.host.E) → Finset ℤ),
    eta + D.R.t + 1 < s →
    Real.log (D.host.g k' : ℝ) ≤ 2 * Real.log (D.host.g k : ℝ) →
    CT * ((s + S) * (D.R.nV + 1) ^ 2 + (D.R.nV + 1) ^ 3) < D.host.g k →
    SignOK i sg → HostJ i r eta s S sg U → (∀ π ∈ D.nd.Zgood i, Br.sFin D.loc D.nbr i ρ π) →
    (∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) < ⊤) →
    (D.nd.etaLoc i : ℝ) ≤ ∑ π ∈ D.nd.Zgood i, (D.nd.mult i π : ℝ) * rhs C eta i ρ π
def GaloisFamilyConditions' : Prop :=
  ∀ i r, GoodR D.nd i r →
    Formalism.MainNotions.SumRepresentations.At.G1 D.nd i r ∧ _root_.UpperTheory.GalS.G2a D.nd D.naut i r ∧ _root_.UpperTheory.GalS.G3 D.nd i r ∧
      Formalism.MainNotions.SumRepresentations.At.G4 D.nd i r
def LocalGlobalCompatibility' : Prop := _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D
section Pending
end Pending
end Formalism.MainNotions.PairedCharacterCondition
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisConditionFourOf
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace Formalism.MainNotions.N
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open NumberField IsDedekindDomain
theorem galois_condition_one_of_alt (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (h32 : _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D) (hr : Formalism.MainNotions.N.GoodR D.nd i r) : Formalism.MainNotions.TruncatedSeriesCountingIdentities.admG1 (D := D) i r := by
  intro g k
  obtain ⟨f, hf⟩ := ((h32 i).2.2 r hr).1 g k
  have e : (fun x : D.nd.X i => ((Formalism.MainNotions.N.rO D.nd i r x g).charpolyRev).coeff k) =
      (f : D.nd.X i → D.nd.O i) := funext fun x => (hf x).symm
  rw [e]
  exact f.2
theorem admG4_of_goodR (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (h32 : _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D) (hr : Formalism.MainNotions.N.GoodR D.nd i r) : Formalism.MainNotions.TruncatedSeriesCountingIdentities.admG4 (D := D) i r := by
  intro x v hl hS hQ g hg
  exact ((h32 i).2.2 r hr).2.2.2 x v hl hS hQ (D.nd.plOm.1 v) (D.nd.plOm.2 v) g hg
end Formalism.MainNotions.N
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MainAltAlt
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CrysLoc
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal
end
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
namespace GlobalTheory.CrysFromGTwo
theorem crys_loc_alt_alt (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (hr : GoodR D.nd i r) (hG : _root_.UpperTheory.GalS.G2a D.nd D.naut i r) (h0 : D.nd.l i ≠ D.host.g 0)
    (h1 : D.nd.l i ≠ D.host.g 1) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (x : D.nd.X i) :
    IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw (rO D.nd i r x))) := by
  have hc := (_root_.UpperTheory.GalS.g2a' hG w hw h0 h1 x).1
  exact ((D.loc_tie i w hw).2.1 D.R.nV (r x) (hr x).1).1.mp hc
end GlobalTheory.CrysFromGTwo
end
section
namespace GlobalTheory.DualTwistCrys
end GlobalTheory.DualTwistCrys
end
section
namespace GlobalTheory.CrysChiOne
end GlobalTheory.CrysChiOne
end
section
namespace Formalism.MainNotions.N
end Formalism.MainNotions.N
end
section
namespace GlobalTheory.AbsoluteIrreducibilityOfTraceSpan
end GlobalTheory.AbsoluteIrreducibilityOfTraceSpan
end
section
end
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
namespace GlobalTheory.CrysFromGTwo
theorem main_alt_alt : GlobalTheory.Published.FontaineBcris → ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), GoodR D.nd i r → _root_.UpperTheory.GalS.G2a D.nd D.naut i r → D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 → TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw), IsCrys (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (TruncatedSeriesCountingIdentities.chi1C C)⁻¹) ∧ ∀ x, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x))) ∧ IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x))) := by
  intro hF D i r ρ π hr hG h0 h1 hD w hw C
  have hχ := crys_chi hF D i r ρ π hD (fun w' hw' => _root_.GlobalTheory.CrysFromGTwo.crys_loc_alt_alt D i r hr hG h0 h1 w' hw' π) w hw C
  have hx : ∀ x, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x))) := fun x =>
    crys_coef D i r w hw C x (_root_.GlobalTheory.CrysFromGTwo.crys_loc_alt_alt D i r hr hG h0 h1 w hw x)
  exact ⟨hχ, fun x => ⟨hx x, crys_tw D i r w hw C x hχ (hx x)⟩⟩
end GlobalTheory.CrysFromGTwo
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MainAltAltBis
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RxCrys
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal
end
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
namespace GlobalTheory.CrysFromGTwo
end GlobalTheory.CrysFromGTwo
end
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
namespace GlobalTheory.DualTwistCrys
end GlobalTheory.DualTwistCrys
end
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
namespace GlobalTheory.CrysChiOne
variable {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
  {hw : w ∈ placesOver D.host.E (D.nd.l i)}
theorem rx_crys_alt_alt (h41 : _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (hr : GoodR D.nd i r) (hl0 : D.nd.l i ≠ D.host.g 0) (hl1 : D.nd.l i ≠ D.host.g 1)
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (x : D.nd.X i) :
    IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x))) := by
  have h1 := (_root_.UpperTheory.GalS.g2a' ((h41 i).2.2 r hr).2.1 w hw hl0 hl1 x).1
  have h2 : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw (rO D.nd i r x))) :=
    ((D.loc_tie i w hw).2.1 D.R.nV (r x) (by simpa [rO] using (hr x).1)).1.1 h1
  exact GlobalTheory.CrysCoef.isCrys_inclusion (D.nd.l i) (D.loc (D.nd.l i)) (D.nbr i w hw).Kw (D.nbr i w hw).LL C.LL C.le
    D.R.nV _ h2
end GlobalTheory.CrysChiOne
end
section
namespace Formalism.MainNotions.N
end Formalism.MainNotions.N
end
section
namespace GlobalTheory.AbsoluteIrreducibilityOfTraceSpan
end GlobalTheory.AbsoluteIrreducibilityOfTraceSpan
end
section
end
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MainAltAltBis
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
noncomputable section
namespace GlobalTheory.CrysChiOne
variable {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
  {hw : w ∈ placesOver D.host.E (D.nd.l i)}
theorem main_alt_alt : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i → GoodR D.nd i r → (Continuous fun g => ((ρ π g : GL (Fin D.R.r) (D.nd.O i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i))) → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π → D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw), IsCrys (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (TruncatedSeriesCountingIdentities.chi1C C)⁻¹) ∧ (∀ x, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rDuO D.nd i r x)))) ∧ IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (WpO D.nd i ρ π))) ∧ IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (T2O D.nd i ρ π))) := by
  intro D i r ρ π h41 hfont hr hρc hd hl0 hl1 w hw C
  have hF := hfont w hw C
  have hcA : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r := continuous_family_of D i r hr
  have hrx := _root_.GlobalTheory.CrysChiOne.rx_crys_alt_alt h41 r hr hl0 hl1 C
  have hchi := chi1inv_crys C hF r ρ π hd (hrx π) (hcA π)
  have hTw : ∀ x, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x))) := by
    intro x
    have hc' := locC_cont' C _ (rTwO_cont D i r hcA x)
    rw [locC_rTwO] at hc' ⊢
    exact twist_crys C hF _ _ (locC_cont' C _ (hcA x)) hc' hchi (hrx x)
  obtain ⟨B, A, hAB, hint⟩ := decomp_rho r ρ π hd
  have hrho := sub_crys C hF r π (hrx π) (hcA π) (rhoO D.nd i ρ π) hρc B A hAB hint
  have hWc : Continuous fun g => WpO D.nd i ρ π g := by
    have h1 : Continuous fun g : GE D.nd => ((((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ)) : D.nd.O i) := by
      have e : (fun g : GE D.nd => ((((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ)) : D.nd.O i)) =
          fun g => ((D.nd.chi i 1 g⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) := by
        funext g
        rw [map_inv]
        rfl
      rw [e]
      exact (D.nd.chi_cont i 1).comp continuous_inv
    exact h1.smul hρc
  have hW : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (WpO D.nd i ρ π))) := by
    have hc' := locC_cont' C _ hWc
    rw [locC_WpO] at hc' ⊢
    exact twist_crys C hF _ _ (locC_cont' C _ hρc) hc' hchi hrho
  refine ⟨hchi, fun x => ?_, hW, ?_⟩
  · rw [locC_rDuO]
    exact (GlobalTheory.HTW.Rec.tateDual_matRep_crys (D.loc (D.nd.l i)) (D.nbr i w hw).Kw C.LL _ hF.2.2.1
      (locC_cont' C _ (rTwO_cont D i r hcA x)) (hTw x)).2
  · rw [locC_T2O]
    exact (GlobalTheory.HTW.Rec.tateDual_matRep_crys (D.loc (D.nd.l i)) (D.nbr i w hw).Kw C.LL _ hF.2.2.1
      (locC_cont' C _ hWc) hW).2
end GlobalTheory.CrysChiOne
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MainAltAltBisStatement
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.decomposition_fontaine_at_places_over_l : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i → GoodR D.nd i r → (Continuous fun g => ((ρ π g : GL (Fin D.R.r) (D.nd.O i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i))) → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π → D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw), IsCrys (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (TruncatedSeriesCountingIdentities.chi1C C)⁻¹) ∧ (∀ x, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rDuO D.nd i r x)))) ∧ IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (WpO D.nd i ρ π))) ∧ IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (T2O D.nd i ρ π))) := by
  first | exact @_root_.GlobalTheory.CrysChiOne.main_alt_alt | exact _root_.GlobalTheory.CrysChiOne.main_alt_alt | (intros; apply _root_.GlobalTheory.CrysChiOne.main_alt_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MainAltAltAltMore
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
namespace GlobalTheory.ChiOneNoPt
open GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary GlobalTheory.JumpDictionaryFoundation
theorem main_alt_alt_alt : GlobalTheory.Published.FontaineBcris → ∀ D : D7, SumRepresentations.tie0 D → _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D → SumRepresentations.adm5 D →
    GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.BlockCharParam D → GlobalTheory.HubX.MuUnr D → ∀ i : D.nd.Loc, D.nd.l i ∉ TwistedPlaces.gset D →
    GlobalTheory.PtCore.ChiOneE D i := by
  intro hF D _h0 h2 h5 hB hM i hl w hw L' hL
  obtain ⟨ρ, hρc, haway, habove⟩ :=
    (_root_.UpperTheory.GalS.weak' h2 i).2.2 (D.naut.tw (D.naut.muC i) D.naut.etaTinv) (sOne D) (integral D hB i)
  have hρ := eq_chi D h5 i w hw ρ hρc haway
  obtain ⟨hdR, hwd, -⟩ := habove w hw
  have hun : D.naut.unr (D.naut.wdOf i ρ w) := by
    rw [hwd]; exact (D.naut.unr_tw _ _).2 (hM i hl w hw)
  have hcW : D.naut.IsCrysW i ρ w := (D.naut.wdOf_unrL i ρ w hw hρc hdR).1 hun
  subst hρ
  have hc : Br.IsCrysW D.loc D.nbr i w hw (chiGL D i 1) :=
    (((D.loc_tie i w hw).2.1 1 _ (continuous_chiGL D i 1)).1).1 hcW
  have hR := GlobalTheory.BlockCrys.subDualRules_of_fontaine hF (D.nd.l i) (D.loc _) (D.locA _) ⟨D.locT _⟩
  have hE := GlobalTheory.CrysCoef.isCrys_inclusion (D.nd.l i) (D.loc _) (D.nbr i w hw).Kw (D.nbr i w hw).LL L' hL _ _
    ((GlobalTheory.BlockCrys.matCrysAt_iff D i w hw _).2 hc)
  exact GlobalTheory.BlockCrys.isCrys_inv _ (hR.1 _ _) (hR.2 _ _) _
    (GlobalTheory.ChiOneEnl.isCrys_chiE_of_constituent D i w hw L' hL (hR.1 _ _) _ _ (isConstituent_chiGL D i) hE)
end GlobalTheory.ChiOneNoPt
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CrysBridge
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal
end
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
namespace GlobalTheory.CrysFromGTwo
end GlobalTheory.CrysFromGTwo
end
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
namespace GlobalTheory.DualTwistCrys
theorem crys_bridge_alt_alt (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (hR : GoodR D.nd i r) (hCr : _root_.UpperTheory.GalS.G2a D.nd D.naut i r) (h0 : D.nd.l i ≠ D.host.g 0)
    (h1 : D.nd.l i ≠ D.host.g 1) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (x : D.nd.X i) :
    IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw (rO D.nd i r x))) :=
  ((D.loc_tie i w hw).2.1 D.R.nV (r x) (hR x).1).1.1 (_root_.UpperTheory.GalS.g2a' hCr w hw h0 h1 x).1
end GlobalTheory.DualTwistCrys
end
section
namespace GlobalTheory.CrysChiOne
end GlobalTheory.CrysChiOne
end
section
namespace Formalism.MainNotions.N
end Formalism.MainNotions.N
end
section
namespace GlobalTheory.AbsoluteIrreducibilityOfTraceSpan
end GlobalTheory.AbsoluteIrreducibilityOfTraceSpan
end
section
end
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PartFrobEigNormO
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.PartUnitary
theorem frobEig_openB_and_norm_one_of_isBCV : ∀ (D : D7), SumRepresentations.tie0 D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → ∀ (i : D.nd.Loc) (P : D.naut.AV i)
    (Pa : List (Part D.naut.CG)), IsBCV D.nd D.naut i P Pa → ∀ p ∈ Pa, ∀ w : PlE D.host,
    D.naut.unr (D.naut.locG p.π w) → ∀ α ∈ D.naut.frobEig (D.naut.locG p.π w), UpperTheory.GalN.OpenB (Formalism.ConjugateSelfDual.normV w) α ∧ (p.a = 1 → ‖α‖ = 1) := by
  intro D ht hT i P Pa hB p hp w hu α hα
  have hW := GlobalTheory.LocalInv.weightRegular_of_ext D.nd D.naut D.nbc
  have hAut := ht.2.1
  obtain ⟨ha1, hd1, hcsd⟩ := hB.1 p hp
  have hle : ∀ τ, (D.naut.infG p.π τ).map (· + (((p.d : ℂ) - 1) / 2 - ((0 : ℕ) : ℂ))) ≤
      D.naut.infWt i τ := by
    intro τ
    rw [← hB.2.2.2.2.2 τ]
    unfold isoInf
    refine le_trans ?_ (List.single_le_sum (fun _ _ => Multiset.zero_le _) _ (List.mem_map_of_mem hp))
    refine List.single_le_sum (fun _ _ => Multiset.zero_le _) _
      (List.mem_map_of_mem (f := fun k : ℂ => (D.naut.infG p.π τ).map (· + (((p.d : ℂ) - 1) / 2 - k))) ?_)
    rw [GlobalTheory.LocalInv.list_coe]
    exact List.mem_map_of_mem (List.mem_range.mpr hd1)
  have hnd : ∀ τ, (D.naut.infG p.π τ).Nodup := fun τ =>
    Multiset.Nodup.of_map _ (Multiset.nodup_of_le (hle τ) (hW i P τ).1)
  have hint : ∀ τ, ∀ z ∈ D.naut.infG p.π τ, ∃ k : ℤ,
      z + ((p.d : ℂ) - 1) / 2 = (k : ℂ) + ((D.R.nV : ℂ) - 1) / 2 := by
    intro τ z hz
    obtain ⟨k, hk⟩ := (hW i P τ).2 _ (Multiset.mem_of_le (hle τ) (Multiset.mem_map_of_mem _ hz))
    exact ⟨k, by rw [← hk]; push_cast; ring⟩
  rcases Int.even_or_odd ((D.R.nV : ℤ) - p.d - p.a + 1) with ⟨m, hm⟩ | ⟨m, hm⟩
  · have hr : D.naut.ralg p.π := (D.naut.ralg_def _).2 fun τ => ⟨hnd τ, fun z hz => by
      obtain ⟨k, hk⟩ := hint τ z hz
      refine ⟨k + m, ?_⟩
      have hm' : ((D.R.nV : ℤ) : ℂ) - ((p.d : ℤ) : ℂ) - ((p.a : ℤ) : ℂ) + 1 = (m : ℂ) + m := by
        exact_mod_cast hm
      push_cast at hm' ⊢
      linear_combination hk + (1 / 2 : ℂ) * hm'⟩
    exact (_root_.UpperTheory.GalN.tempo' hT p.a p.π ha1 hcsd hr w).part hu α hα
  · have hr : D.naut.ralg (D.naut.tw p.π D.naut.etaT) := (D.naut.ralg_def _).2 fun τ => by
      obtain ⟨s, hs, k0, hk0⟩ : ∃ s : ℂ, D.naut.infG D.naut.etaT τ = {s} ∧ ∃ k0 : ℤ, s = (k0 : ℂ) + 1 / 2 := by
        rcases (hAut.2.1 τ).1 with h | h
        · exact ⟨1 / 2, h, 0, by simp⟩
        · exact ⟨-(1 / 2), h, -1, by push_cast; ring⟩
      rw [D.naut.infG_tw _ _ τ s hs]
      refine ⟨(hnd τ).map (add_left_injective s), fun z hz => ?_⟩
      obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hz
      obtain ⟨k, hk⟩ := hint τ y hy
      refine ⟨k + k0 + m + 1, ?_⟩
      have hm' : ((D.R.nV : ℤ) : ℂ) - ((p.d : ℤ) : ℂ) - ((p.a : ℤ) : ℂ) + 1 = 2 * (m : ℂ) + 1 := by
        exact_mod_cast hm
      push_cast at hm' ⊢
      rw [hk0]
      linear_combination hk + (1 / 2 : ℂ) * hm'
    exact (_root_.UpperTheory.GalN.tempo' hT p.a _ ha1 (D.naut.csd_tw _ _ hAut.1.1 hcsd) hr w).part_tw hAut hu α hα
end GlobalTheory.PartUnitary
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeCharEqOfLAdicRealisation
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.StringRepresentationDecomposition
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal
def CentredStringDecompositionAlt : Prop :=
  ∀ D : D7, _root_.Formalism.MainNotions.SumRepresentations.AdmissibleDatum D → ∀ (i : D.nd.Loc) (x : D.nd.X i) (P : D.naut.AV i)
    (Pa : List (Part D.naut.CG)), D.naut.ptV i P = some x → IsBCV D.nd D.naut i P Pa →
    ∀ r, GoodR D.nd i r →
    ∃ R : ∀ k : Fin Pa.length, Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin (Pa.get k).a) (Qbar (D.nd.l i)),
      (∀ k, _root_.UpperTheory.GalS.IsStringRepN D i (Pa.get k) (R k)) ∧
      ∀ g, ((mapRep (iotaOQ D.nd D.naut i) (r x) g : GL _ _) :
          Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (D.nd.l i))).charpoly =
        ∏ k : Fin Pa.length, ∏ a ∈ Finset.range (Pa.get k).d,
          (((R k g : GL _ _) : Matrix (Fin (Pa.get k).a) (Fin (Pa.get k).a) (Qbar (D.nd.l i))).charpoly).scaleRoots
            ((epsQ D i g)⁻¹ ^ a)
def PurityStringWeight' : Prop :=
  ∀ D : D7, _root_.Formalism.MainNotions.SumRepresentations.AdmissibleDatum D → ∀ (i : D.nd.Loc) (x : D.nd.X i) (P : D.naut.AV i)
    (Pa : List (Part D.naut.CG)), D.naut.ptV i P = some x → IsBCV D.nd D.naut i P Pa →
    ∀ (k : Fin Pa.length) (R : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin (Pa.get k).a) (Qbar (D.nd.l i))),
      _root_.UpperTheory.GalS.IsStringRepN D i (Pa.get k) R → ∀ a < (Pa.get k).d,
      (∃ v : Fin (Pa.get k).a → Qbar (D.nd.l i), v ≠ 0 ∧ ∀ g,
        ((epsQ D i g)⁻¹ ^ a) • ((R g : GL _ _) : Matrix (Fin (Pa.get k).a) (Fin (Pa.get k).a)
          (Qbar (D.nd.l i))).mulVec v = iotaOQ D.nd D.naut i (chi1 D.nd i g) • v) →
      ((Pa.get k).d : ℤ) - 1 - 2 * a = (D.R.t : ℤ) - 1
def HeckeCharEqOfLAdicRealisation' : Prop :=
  ∀ D : D7, _root_.Formalism.MainNotions.SumRepresentations.AdmissibleDatum D → ∀ (i : D.nd.Loc) (χ χ' : D.naut.CG 1) (s : ℝ)
    (ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin 1) (Qbar (D.nd.l i))),
    (∀ w, w ∉ placesOver D.host.E (D.nd.l i) → D.naut.wdOf i ρ w = D.naut.lpTw (D.naut.locG χ w) s) →
    (∀ w, w ∉ placesOver D.host.E (D.nd.l i) → D.naut.wdOf i ρ w = D.naut.lpTw (D.naut.locG χ' w) s) →
    χ = χ'
def MuCharacterCondition : Prop :=
  ∀ D : D7, _root_.Formalism.MainNotions.SumRepresentations.AdmissibleDatum D → ∀ (i : D.nd.Loc), HG D.nd D.naut i →
    ∀ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin 1) (Qbar (D.nd.l i)),
    (∀ g, ((ρ g : GL _ _) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0 =
      iotaOQ D.nd D.naut i (chi1 D.nd i g)) →
    ∀ w, w ∉ placesOver D.host.E (D.nd.l i) →
      D.naut.wdOf i ρ w = D.naut.lpTw (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) w)
        (((D.R.t : ℝ) - 1) / 2 + (1 - (D.R.nV : ℝ)) / 2)
def ResidueCount : Prop :=
  ∀ D : D7, _root_.Formalism.MainNotions.SumRepresentations.AdmissibleDatum D → RbEx D → ∀ (i : D.nd.Loc), HG D.nd D.naut i →
    ∀ (r : D.nd.X i → (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r → ∀ (x : D.nd.X i)
    (Pa : List (Part D.naut.CG))
    (R : ∀ k : Fin Pa.length, Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin (Pa.get k).a) (Qbar (D.nd.l i))),
    (∀ k, _root_.UpperTheory.GalS.IsStringRepN D i (Pa.get k) (R k)) →
    (∀ g, ((mapRep (iotaOQ D.nd D.naut i) (r x) g : GL _ _) :
          Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (D.nd.l i))).charpoly =
        ∏ k : Fin Pa.length, ∏ a ∈ Finset.range (Pa.get k).d,
          (((R k g : GL _ _) : Matrix (Fin (Pa.get k).a) (Fin (Pa.get k).a) (Qbar (D.nd.l i))).charpoly).scaleRoots
            ((epsQ D i g)⁻¹ ^ a)) →
    ∃ Ak : Fin Pa.length → Multiset ℕ, (∀ k, (Ak k).sum = (Pa.get k).a ∧ ∀ a ∈ Ak k, 1 ≤ a) ∧
      ∑ k, (Pa.get k).d • Ak k = D.R.r ::ₘ Multiset.replicate D.R.t 1
def LocalGlobalCompatible (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (r : D.nd.X i → (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r →
    ∀ w : PlE D.host, (w ∈ D.nd.S i ∨ w ∈ D.nd.Q i) → _root_.UpperTheory.GalS.LGCatN D.nd r D.naut w
end GlobalTheory.StringRepresentationDecomposition
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisConditionThreeOf
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal
end
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
namespace GlobalTheory.CrysFromGTwo
end GlobalTheory.CrysFromGTwo
end
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
namespace GlobalTheory.DualTwistCrys
end GlobalTheory.DualTwistCrys
end
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
namespace GlobalTheory.CrysChiOne
variable {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
  {hw : w ∈ placesOver D.host.E (D.nd.l i)}
end GlobalTheory.CrysChiOne
end
section
namespace Formalism.MainNotions.N
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open NumberField IsDedekindDomain
theorem galois_condition_three_of_alt_alt (D : D7) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (h32 : _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D) (hr : GoodR D.nd i r)
    (hdec : Formalism.MainNotions.TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π)
    (hcont : Continuous (fun g => ((ρ π g : GL (Fin D.R.r) (D.nd.O i)) :
      Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i))))
    (hHG : HG D.nd D.naut i) (hN9 : ResidualIrreducibleRankR D) (hB : LitBurnside (GE D.nd))
    (hc : AbsIrreducibleDistinct D i r) : Formalism.MainNotions.TruncatedSeriesCountingIdentities.admG3 (D := D) i r ρ π := by
  have h2 : ∀ x (g : GE D.nd), (mapM (IsLocalRing.residue (D.nd.O i)) (rO D.nd i r x) g).charpoly =
      (mapM (IsLocalRing.residue (D.nd.O i)) (rhoO D.nd i ρ π) g).charpoly *
        ∏ c ∈ Finset.Icc 1 D.R.t,
          (X - C (IsLocalRing.residue (D.nd.O i) ((chiU D.nd i c g : (D.nd.O i)ˣ) : D.nd.O i))) := by
    intro x g
    have e1 := (_root_.UpperTheory.GalS.g3' ((h32 i).2.2 r hr).2.2.1).2 x π g
    have e2 := congrArg (Polynomial.map (IsLocalRing.residue (D.nd.O i))) (charpoly_of_decomp D i r ρ π hdec g)
    rw [Polynomial.map_mul, Polynomial.map_prod, ← Matrix.charpoly_map, ← Matrix.charpoly_map] at e2
    refine e1.trans (e2.trans ?_)
    congr 1
    refine Finset.prod_congr rfl fun c _ => ?_
    simp
  refine ⟨hc, h2, ?_⟩
  have hrb : IsRhoBar D.nd i (redRep D.nd i (ρ π)) := by
    refine ⟨isOpen_ker_redRep D i _ hcont, ?_⟩
    intro x w hw B σ hB' hσ
    rw [← (hr x).2.2 w hw B σ hB' hσ, ← Matrix.charpoly_map]
    exact (h2 x σ).symm
  have h3 := hB (D.nd.l i) D.R.r _ (hN9 i hHG _ hrb).1
  exact span_descent (D.naut.kFbar i) (fun g => mapM (IsLocalRing.residue (D.nd.O i)) (rhoO D.nd i ρ π) g) h3
end Formalism.MainNotions.N
end
section
namespace GlobalTheory.AbsoluteIrreducibilityOfTraceSpan
end GlobalTheory.AbsoluteIrreducibilityOfTraceSpan
end
section
end
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SEtaChi
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead
noncomputable section
namespace GlobalTheory.SplitRead
open Formalism.MainNotions.SumRepresentations.At
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
theorem chiIne_of_lp_aut_admissible_mult_one (hLP : TieLP N A) (hAut : TieAut N A) (h2 : _root_.UpperTheory.GalS.AutomorphicGaloisAdmissible N A) (h5 : JacquetShalikaStrongMultOne N A)
    (hMu : MuInt N A) : ChiIne N A := by
  intro i w hw σ hσ
  obtain ⟨ρ, hρ, hwd, -⟩ := (_root_.UpperTheory.GalS.weakA' h2 i).2.2 (A.tw (A.muC i) A.etaTinv) (blockShift R)
    (fun τ z hz => blockChar_integral N A hAut hMu i τ z hz)
  have hρσ := blockChar_eq N A h5 i ρ hρ hwd σ
  have e := A.wdOf_ine i ρ w hw hρ σ hσ
  rw [hwd w hw, A.inePol_tw _ _ _ hσ, A.locG_tw, charpoly_fin_one, hρσ] at e
  have hdim : A.lpDim (A.locG A.etaTinv w) = 1 := A.locG_dim _ _
  have hine : A.inePol (A.locG A.etaTinv w) σ = X - C 1 := by
    have := ((A.unr_iff_ine _).1 (A.etaTinv_def w).1).2 σ hσ
    rw [hdim, pow_one] at this
    simpa using this
  have hs := ((hLP w (A.locG (A.muC i) w) (A.locG (A.muC i) w) (A.locG A.etaTinv w) (A.locG A.etaTinv w) 0
    hdim hdim).2.2.2.2.2 σ hσ).2 1 hine
  rw [hs, Polynomial.scaleRoots_one] at e
  rw [← e]
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  rfl
end GlobalTheory.SplitRead
namespace GlobalTheory.XiOver
theorem main_alt_alt_alt : ∀ (D : D7) (C : Formalism.L2.Host.CharFrame D) (nch : NChoice D) (Tp : Formalism.L2.Host.TupTied D C nch), Formalism.L2.Host.NCharTied D C nch Tp → Formalism.L2.Host.ValLL0 D C → Formalism.MainNotions.SumRepresentations.tie0 D → _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D → Formalism.MainNotions.SumRepresentations.adm5 D → XiOverO D.nd D.naut := by
  intro D C nch Tp T V ht h2 h5 i
  have hA : Formalism.MainNotions.SumRepresentations.At.TieAut D.nd D.naut := ht.2.1
  obtain ⟨ρ, hρ, hwd, -⟩ := (_root_.UpperTheory.GalS.weak' h2 i).2.2 D.naut.etaTinv (-(D.R.t : ℝ) / 2) (inf_int D hA)
  have hun : ∀ w, w ∉ placesOver D.host.E (D.nd.l i) → D.naut.unr (D.naut.wdOf i ρ w) := fun w hw => by
    rw [hwd w hw]
    exact (D.naut.unr_tw _ _).2 (D.naut.etaTinv_def w).1
  have hfrob : ∀ w, w ∉ placesOver D.host.E (D.nd.l i) → ∀ (B : ValuationSubring D.nd.Om) (σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om),
      IsPlaceOver (F := D.host.E) B w → IsFrob (F := D.host.E) B (normV w) σ →
      D.naut.frobEig (D.naut.lpTw (D.naut.locG D.naut.etaTinv w) (-(D.R.t : ℝ) / 2)) =
        {D.naut.iotaQC i (((ρ σ : GL (Fin 1) (Qbar (D.nd.l i))) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0)} := by
    intro w hw B σ hB hσ
    have e := D.naut.wdOf_frob i ρ w hw hρ (hun w hw) B σ hB hσ
    obtain ⟨a, ha⟩ := Multiset.card_eq_one.1
      ((D.naut.frobEig_card _ (hun w hw)).trans (D.naut.wdOf_dim i ρ w))
    rw [ha, charpoly_fin_one] at e
    simp only [Multiset.map_singleton, Multiset.prod_singleton, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_C] at e
    have e2 := C_injective (sub_right_injective e)
    rw [← hwd w hw, ha]
    exact congrArg _ e2.symm
  let d : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* Qbar (D.nd.l i) :=
    (Units.coeHom _).comp (Matrix.GeneralLinearGroup.det.comp ρ)
  have hde : ∀ g, d g = ((ρ g : GL (Fin 1) (Qbar (D.nd.l i))) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0 :=
    fun g => Matrix.det_fin_one _
  have hd : Continuous d := by
    have : (d : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om → Qbar (D.nd.l i)) = fun g =>
        ((ρ g : GL (Fin 1) (Qbar (D.nd.l i))) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0 := funext hde
    rw [this]
    exact (continuous_apply_apply 0 0).comp hρ
  have hfin : (placesOver D.host.E (D.nd.l i)).Finite :=
    GlobalTheory.SplitRead.finite_placesOver _ (Fact.out : (D.nd.l i).Prime).ne_zero
  have hS := h5.2.2.1 _ hfin
  obtain ⟨ξ, hξc, hξ⟩ := exists_integral_char D.nd D.naut i d hd _ hS (by
    rintro σ ⟨w, hw, -, B, hB, hσ⟩
    obtain ⟨x, hx⟩ := frob_value D C nch Tp T V w
    have e := hfrob w hw B σ hB hσ
    rw [hx, Multiset.singleton_inj, ← D.naut.iota_LL i x, ← hde] at e
    exact ⟨_, (D.naut.iotaQC i).injective e⟩)
  refine ⟨ξ, hξc, fun w hw => ⟨fun σ hσ => ?_, fun B σ hB hσ => ?_⟩⟩
  · have h1 := (D.naut.wdOf_unr i ρ w hw hρ).1 (hun w hw) σ hσ
    apply Units.ext
    apply iota_inj D.nd D.naut i
    rw [hξ, hde, h1]
    simp
  · rw [hfrob w hw B σ hB hσ, ← hde, ← hξ]
    rfl
end GlobalTheory.XiOver
end
end
end
