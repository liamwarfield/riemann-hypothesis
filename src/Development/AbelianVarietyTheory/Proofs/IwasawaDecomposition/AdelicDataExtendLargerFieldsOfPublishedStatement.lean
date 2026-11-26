module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExtendedColumnDataAllClausesButPlaces
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftFormsLatticeDefiniteLatticeBaseChangeExtende

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicDataExtendLargerFieldsOfHyp
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtendedDataNonzeroIndexPlacesCorrespond
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtendedDataDefiniteLiftLatticeBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtendedDataLiftBlockDatumEqBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtendedDataLiftBlockDatumEqBaseChange
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

namespace GlobalTheory.Mem.R3.TwistedPlaceExtensions


set_option maxHeartbeats 4000000 in
theorem blockBC_lift : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∃ e, GlobalTheory.Mem.R3.DefLatBC.BlockBaseChange φ e ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0)
          ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.lvlA z.F.P0 z.F.ψ0) ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.lvlA z'.F.P0 z'.F.ψ0) ((zsOf z.R z.F).Zl j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) ((zsOf z'.R z'.F).Zl j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0)) := by
  intro h1 h2 h3 h4 h5 h6 h7
  refine StepW.trans (StepW.and (GlobalTheory.T.typePrimeFiniteGroup_eq_extendedData h1 h2 h3 h4 h5 h6 h7) (StepW.and (GlobalTheory.T.baseLevelLift_extendedData_eq_map_smallerField h1 h2 h3 h4 h5 h6 h7)
    (StepW.and (GlobalTheory.T.goodCharacters_extendedData_eq_map_smallerData h1 h2 h3 h4 h5 h6 h7) (StepW.and (GlobalTheory.T.exists_semilinearFormsLift_sameComplexValues h1 h2 h3 h4 h5 h6 h7) (StepW.and (GlobalTheory.T.liftForms_referenceTuple_basis_extended h1 h2 h3 h4 h5 h6 h7)
    (StepW.and (GlobalTheory.T.formsLift_extendedData_carries_classSum h1 h2 h3 h4 h5 h6 h7) (StepW.and (GlobalTheory.T.formsLift_extendedData_intertwines_finiteGroup h1 h2 h3 h4 h5 h6 h7) (StepW.and (GlobalTheory.T.integralForms_referenceTuple_extension_span h1 h2 h3 h4 h5 h6 h7)
    (GlobalTheory.T.liftSubspace_extendedData_eq_span_smallerLifts h1 h2 h3 h4 h5 h6 h7))))))))) (StepW.of_all ?_)
  intro K B' f' T' w' _ _ H B f T w hE hff hPin hpx Z hX Wt z hG hGA hFine hHL Z' hX' hG' hGA' hVol z' hFine' hExt j j' hj φ hφ
  obtain ⟨Hg, Hl, Hx, HL, Hb, Hc, Ha, Hn, Hs⟩ := H
  obtain ⟨e, he⟩ := Hg B f T w hE hff hPin hpx Z hX Wt z hG hGA hFine hHL Z' hX' hG' hGA' hVol z' hFine' hExt j j' hj φ hφ
  obtain ⟨hP, hψ⟩ := Hl B f T w hE hff hPin hpx Z hX Wt z hG hGA hFine hHL Z' hX' hG' hGA' hVol z' hFine' hExt j j' hj φ hφ e he
  have hXg := Hx B f T w hE hff hPin hpx Z hX Wt z hG hGA hFine hHL Z' hX' hG' hGA' hVol z' hFine' hExt j j' hj φ hφ e he
  obtain ⟨L, hL, hC⟩ := HL B f T w hE hff hPin hpx Z hX Wt z hG hGA hFine hHL Z' hX' hG' hGA' hVol z' hFine' hExt j j' hj φ hφ
  obtain ⟨hli, hsp⟩ := Hb B f T w hE hff hPin hpx Z hX Wt z hG hGA hFine hHL Z' hX' hG' hGA' hVol z' hFine' hExt j j' hj φ hφ L hL hC
  have hcs := Hc B f T w hE hff hPin hpx Z hX Wt z hG hGA hFine hHL Z' hX' hG' hGA' hVol z' hFine' hExt j j' hj φ hφ L hL hC
  have hac := Ha B f T w hE hff hPin hpx Z hX Wt z hG hGA hFine hHL Z' hX' hG' hGA' hVol z' hFine' hExt j j' hj φ hφ e he L hL hC
  have hnb := Hn B f T w hE hff hPin hpx Z hX Wt z hG hGA hFine hHL Z' hX' hG' hGA' hVol z' hFine' hExt j j' hj φ hφ L hL hC
  have hsb := Hs B f T w hE hff hPin hpx Z hX Wt z hG hGA hFine hHL Z' hX' hG' hGA' hVol z' hFine' hExt j j' hj φ hφ L hL hC
  exact ⟨e, ⟨GlobalTheory.T.forms_of_semilinear_alt φ e _ _ _ _ L hL hli hsp hcs hac hnb hsb, hXg, hP, hψ⟩⟩

end GlobalTheory.Mem.R3.TwistedPlaceExtensions

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtendedDataLiftBlockDatumEqBaseChangeStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extendedData_lift_blockDatum_eq_baseChange : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∃ e, GlobalTheory.Mem.R3.DefLatBC.BlockBaseChange φ e ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0)
          ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.lvlA z.F.P0 z.F.ψ0) ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.lvlA z'.F.P0 z'.F.ψ0) ((zsOf z.R z.F).Zl j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) ((zsOf z'.R z'.F).Zl j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0)) := by
  exact @GlobalTheory.Mem.R3.TwistedPlaceExtensions.blockBC_lift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtendedDataDefiniteLiftLatticeBaseChange
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.TwistedPlaceExtensions


set_option maxHeartbeats 4000000 in
theorem defLat0_baseChange : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∃ G : Matrix (Fin (((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).side3 z'.F.P0 z'.F.ψ0 (zsOf z'.R z'.F)).dZ j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0)) (Fin (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).dZ j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0)) (w'.st Z').toD7.what₂.LL, Function.Bijective G.mulVec ∧
          ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).side3 z'.F.P0 z'.F.ψ0 (zsOf z'.R z'.F)).Tl j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0 = Submodule.span (𝓞 (w'.st Z').toD7.what₂.LL) ((fun x : Fin (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).dZ j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) → (w.st Z).toD7.what₂.LL => Matrix.mulVec G fun k => φ (x k)) '' ((((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).Tl j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0 : Submodule (𝓞 (w.st Z).toD7.what₂.LL) (Fin (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).dZ j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) → (w.st Z).toD7.what₂.LL)) : Set (Fin (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).dZ j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) → (w.st Z).toD7.what₂.LL))) ∧
          ∀ x y : Fin (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).dZ j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) → (w.st Z).toD7.what₂.LL, Formalism.DivisionValues.hform (((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).side3 z'.F.P0 z'.F.ψ0 (zsOf z'.R z'.F)).HT j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0) (Matrix.mulVec G fun k => φ (x k)) (Matrix.mulVec G fun k => φ (y k)) =
            φ (Formalism.DivisionValues.hform (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).HT j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) x y)) := by
  intro h1 h2 h3 h4 h5 h6 h7
  refine StepW.trans (GlobalTheory.T.extendedData_lift_blockDatum_eq_baseChange h1 h2 h3 h4 h5 h6 h7) (StepW.of_all ?_)
  intro K B' f' T' w' _ _ H B f T w hE hff hPin hpx Z hX Wt z hG hGA hFine hHL Z' hX' hG' hGA' hVol z' hFine' hExt j j' hj φ hφ
  obtain ⟨e, he⟩ := H B f T w hE hff hPin hpx Z hX Wt z hG hGA hFine hHL Z' hX' hG' hGA' hVol z' hFine' hExt j j' hj φ hφ
  have hstar : ∀ x, φ (star x) = star (φ x) := fun x =>
    (w'.st Z').toD7.what₂.embLL.injective (by rw [hφ, (w.st Z).toD7.starLL_cx, (w'.st Z').toD7.starLL_cx, hφ])
  exact GlobalTheory.T.block_data_level_forms_transport_field_map φ hstar e _ _ _ _ _ _ 1 (hHL.ok.ok2.lifts j _) he

end GlobalTheory.Mem.R3.TwistedPlaceExtensions

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtendedDataDefiniteLiftLatticeBaseChangeStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extendedData_definiteLiftLattice_baseChange : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∃ G : Matrix (Fin (((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).side3 z'.F.P0 z'.F.ψ0 (zsOf z'.R z'.F)).dZ j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0)) (Fin (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).dZ j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0)) (w'.st Z').toD7.what₂.LL, Function.Bijective G.mulVec ∧
          ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).side3 z'.F.P0 z'.F.ψ0 (zsOf z'.R z'.F)).Tl j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0 = Submodule.span (𝓞 (w'.st Z').toD7.what₂.LL) ((fun x : Fin (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).dZ j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) → (w.st Z).toD7.what₂.LL => Matrix.mulVec G fun k => φ (x k)) '' ((((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).Tl j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0 : Submodule (𝓞 (w.st Z).toD7.what₂.LL) (Fin (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).dZ j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) → (w.st Z).toD7.what₂.LL)) : Set (Fin (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).dZ j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) → (w.st Z).toD7.what₂.LL))) ∧
          ∀ x y : Fin (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).dZ j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) → (w.st Z).toD7.what₂.LL, Formalism.DivisionValues.hform (((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).side3 z'.F.P0 z'.F.ψ0 (zsOf z'.R z'.F)).HT j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0) (Matrix.mulVec G fun k => φ (x k)) (Matrix.mulVec G fun k => φ (y k)) =
            φ (Formalism.DivisionValues.hform (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).HT j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) x y)) := by
  first | exact @GlobalTheory.Mem.R3.TwistedPlaceExtensions.defLat0_baseChange | exact GlobalTheory.Mem.R3.TwistedPlaceExtensions.defLat0_baseChange | (intros; apply GlobalTheory.Mem.R3.TwistedPlaceExtensions.defLat0_baseChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemZeroContentPlacesIffOverOfNonvanishing
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl

namespace GlobalTheory.Mem.R3.TwistedPlaceExtensions

theorem mem_conjPl_iff {K : Type} [Field K] [StarRing K] (Q : HeightOneSpectrum (𝓞 K)) (y : 𝓞 K) :
    y ∈ (Formalism.DivisionValues.conjPl Q).asIdeal ↔ (Formalism.DivisionValues.cO K).symm y ∈ Q.asIdeal := by
  show y ∈ Ideal.map (Formalism.DivisionValues.cO K) Q.asIdeal ↔ _
  rw [Ideal.mem_map_of_equiv]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro h
    exact ⟨_, h, (Formalism.DivisionValues.cO K).apply_symm_apply y⟩

theorem coe_cO {K : Type} [Field K] [StarRing K] (y : 𝓞 K) : ((Formalism.DivisionValues.cO K y : 𝓞 K) : K) = star (y : K) := rfl

theorem coe_cO_symm {K : Type} [Field K] [StarRing K] (y : 𝓞 K) : (((Formalism.DivisionValues.cO K).symm y : 𝓞 K) : K) = star (y : K) := by
  have h := congrArg (fun u : 𝓞 K => (u : K)) ((Formalism.DivisionValues.cO K).apply_symm_apply y)
  simp only [coe_cO] at h
  rw [← h, star_star]

theorem over_conjPl {D D' : D7} {P : HeightOneSpectrum (𝓞 D.what₂.LL)} {P' : HeightOneSpectrum (𝓞 D'.what₂.LL)}
    (h : ∀ (x : 𝓞 D.what₂.LL) (x' : 𝓞 D'.what₂.LL), D.what₂.embLL (x : D.what₂.LL) = D'.what₂.embLL (x' : D'.what₂.LL) →
      (x ∈ P.asIdeal ↔ x' ∈ P'.asIdeal)) (x : 𝓞 D.what₂.LL) (x' : 𝓞 D'.what₂.LL)
    (hx : D.what₂.embLL (x : D.what₂.LL) = D'.what₂.embLL (x' : D'.what₂.LL)) :
    x ∈ (Formalism.DivisionValues.conjPl P).asIdeal ↔ x' ∈ (Formalism.DivisionValues.conjPl P').asIdeal := by
  rw [mem_conjPl_iff, mem_conjPl_iff]
  apply h
  rw [coe_cO_symm, coe_cO_symm, D.starLL_cx, D'.starLL_cx, hx]

theorem mem_zeroContentPlaces_iff_over_of_nonvanishing {X X' : Stages} {px : PreX X.B.toPre} {px' : PreX X'.B.toPre} {I : ColIn X.B px} {I' : ColIn X'.B px'}
    {hX : X.B.fields.Ok} {hX' : X'.B.fields.Ok} {T : TwDat X.B} {T' : TwDat X'.B} {Wt : Set X.B.places.Pl}
    {Wt' : Set X'.B.places.Pl} (z : Dat X I hX T Wt) (z' : Dat X' I' hX' T' Wt') (hm : X.toD7.R.m = X'.toD7.R.m)
    (hN : ∀ (j : Fin X.toD7.R.m) (j' : Fin X'.toD7.R.m), (j : ℕ) = j' →
      ∀ (P : HeightOneSpectrum (𝓞 X.toD7.what₂.LL)) (P' : HeightOneSpectrum (𝓞 X'.toD7.what₂.LL)),
        (∀ (x : 𝓞 X.toD7.what₂.LL) (x' : 𝓞 X'.toD7.what₂.LL),
          X.toD7.what₂.embLL (x : X.toD7.what₂.LL) = X'.toD7.what₂.embLL (x' : X'.toD7.what₂.LL) → (x ∈ P.asIdeal ↔ x' ∈ P'.asIdeal)) →
        (NzAt z.R z.F (fun _ _ => 0) j P ↔ NzAt z'.R z'.F (fun _ _ => 0) j' P'))
    (v : X.B.places.Pl) (v' : X'.B.places.Pl) (hB : Below X.toD7 X'.toD7 v v') :
    v ∈ z.W1 (fun _ _ => 0) ↔ v' ∈ z'.W1 (fun _ _ => 0) := by
  have hB' := over_conjPl (D := X.toD7) (D' := X'.toD7) hB
  rw [Dat.mem_nonzero_index_places_iff_at_place_or_conjugate, Dat.mem_nonzero_index_places_iff_at_place_or_conjugate]
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨⟨j, hm ▸ j.2⟩, ?_⟩
    exact hj.imp (fun h => (hN j ⟨j, hm ▸ j.2⟩ rfl _ _ hB).1 h) (fun h => (hN j ⟨j, hm ▸ j.2⟩ rfl _ _ hB').1 h)
  · rintro ⟨j', hj⟩
    refine ⟨⟨j', hm.symm ▸ j'.2⟩, ?_⟩
    exact hj.imp (fun h => (hN ⟨j', hm.symm ▸ j'.2⟩ j' rfl _ _ hB).2 h) (fun h => (hN ⟨j', hm.symm ▸ j'.2⟩ j' rfl _ _ hB').2 h)

theorem nzAt_iff_of {X X' : Stages} {px : PreX X.B.toPre} {px' : PreX X'.B.toPre} {I : ColIn X.B px} {I' : ColIn X'.B px'}
    {hX : X.B.fields.Ok} {hX' : X'.B.fields.Ok} {T : TwDat X.B} {T' : TwDat X'.B} {Wt : Set X.B.places.Pl}
    {Wt' : Set X'.B.places.Pl} (z : Dat X I hX T Wt) (z' : Dat X' I' hX' T' Wt') (j : Fin X.toD7.R.m) (j' : Fin X'.toD7.R.m)
    (P : HeightOneSpectrum (𝓞 X.toD7.what₂.LL)) (P' : HeightOneSpectrum (𝓞 X'.toD7.what₂.LL))
    (hI : (s0Of z.R z.F).Iw j (famR X I hX (usedOf I T Wt) z.Xg z.tr).A.μ0 P ≠ 0 ↔
      (s0Of z'.R z'.F).Iw j' (famR X' I' hX' (usedOf I' T' Wt') z'.Xg z'.tr).A.μ0 P' ≠ 0)
    (hJ : Formalism.DivisionValues.jw (((famR X I hX (usedOf I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).HT j
          (famR X I hX (usedOf I T Wt) z.Xg z.tr).A.μ0) P
          (((famR X I hX (usedOf I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).Tl j
          (famR X I hX (usedOf I T Wt) z.Xg z.tr).A.μ0) ≠ 0 ↔
      Formalism.DivisionValues.jw (((famR X' I' hX' (usedOf I' T' Wt') z'.Xg z'.tr).side3 z'.F.P0 z'.F.ψ0 (zsOf z'.R z'.F)).HT j'
                (famR X' I' hX' (usedOf I' T' Wt') z'.Xg z'.tr).A.μ0) P'
                (((famR X' I' hX' (usedOf I' T' Wt') z'.Xg z'.tr).side3 z'.F.P0 z'.F.ψ0 (zsOf z'.R z'.F)).Tl j'
                (famR X' I' hX' (usedOf I' T' Wt') z'.Xg z'.tr).A.μ0) ≠ 0) :
    NzAt z.R z.F (fun _ _ => 0) j P ↔ NzAt z'.R z'.F (fun _ _ => 0) j' P' := by
  unfold NzAt
  exact or_congr hI (or_congr hJ Iff.rfl)

end GlobalTheory.Mem.R3.TwistedPlaceExtensions

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeIndexNonzeroIffUnderFieldMap
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeIndexNonzeroIffUnderFieldMap
open NumberField IsDedekindDomain IsLocalRing TensorProduct

namespace GlobalTheory.LidxBaseChange

theorem length_eq_of_residue (R O M : Type*) [CommRing R] [CommRing O] [IsLocalRing O] [Algebra R O]
    [AddCommGroup M] [Module R M] [Module O M] [IsScalarTower R O M]
    (h1 : Module.length R (ResidueField O) = 1) : Module.length R M = Module.length O M := by
  have step : ∀ {p q : Submodule O M}, p ⋖ q → Module.length R q = Module.length R p + 1 := by
    intro p q h
    let f : p →ₗ[O] q := Submodule.inclusion h.le
    have key : IsSimpleModule O (q ⧸ f.range) := by
      rwa [Submodule.range_inclusion, ← covBy_iff_quot_is_simple h.le]
    obtain ⟨m, hm, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp key
    rw [eq_maximalIdeal hm] at e
    let g : q →ₗ[O] ResidueField O := e.comp f.range.mkQ
    have : Function.Injective f := Submodule.inclusion_injective _
    have : Function.Surjective g := e.surjective.comp f.range.mkQ_surjective
    have : Function.Exact f g := LinearMap.exact_iff.mpr ((e.ker_comp f.range.mkQ).trans f.range.ker_mkQ)
    rw [Module.length_eq_add_of_exact (f.restrictScalars R) (g.restrictScalars R)
      (by simpa) (by simpa) (by simpa), h1]
  by_cases h : IsFiniteLength O M
  · obtain ⟨s, hs_bot, hs_top⟩ := isFiniteLength_iff_exists_compositionSeries.mp h
    rw [← Module.length_compositionSeries s hs_bot hs_top]
    suffices ∀ k, Module.length R (s k) = k by
      rw [← Fin.val_last s.length, ← this, ← RelSeries.last, hs_top]
      exact Module.length_top.symm
    intro k
    induction k using Fin.induction with
    | zero => rw [← RelSeries.head, hs_bot]; simp
    | succ i hi => simpa [hi] using step (s.step i)
  · have : ¬ IsFiniteLength R M := by
      contrapose! h
      rw [isFiniteLength_iff_isNoetherian_isArtinian] at h ⊢
      exact h.imp (isNoetherian_of_tower R) (isArtinian_of_tower R)
    rw [← Module.length_ne_top_iff, not_ne_iff] at h this
    rw [h, this]

theorem length_residue_atPrime {R : Type*} [CommRing R] (P : Ideal R) [P.IsMaximal] :
    Module.length R (ResidueField (Localization.AtPrime P)) = 1 := by
  rw [Module.length_eq_of_surjective (S := R) (R := ResidueField (Localization.AtPrime P))
    (Ideal.algebraMap_residueField_surjective P)]
  simp

theorem mem_localization_iff {R W : Type*} [CommRing R] (P : Ideal R) [P.IsPrime] [AddCommGroup W] [Module R W]
    [Module (Localization.AtPrime P) W] [IsScalarTower R (Localization.AtPrime P) W] (X : Submodule R W) (x : W) :
    x ∈ Formalism.HermitianLatticesTheory.localization₂ P X ↔ x ∈ Submodule.span (Localization.AtPrime P) (X : Set W) := by
  constructor
  · rintro ⟨s, hs, hx⟩
    obtain ⟨u, hu⟩ := IsLocalization.map_units (Localization.AtPrime P) (⟨s, hs⟩ : P.primeCompl)
    have : x = (↑u⁻¹ : Localization.AtPrime P) • (s • x) := by
      rw [← algebraMap_smul (Localization.AtPrime P) s x]
      change x = _ • (algebraMap R (Localization.AtPrime P) ((⟨s, hs⟩ : P.primeCompl) : R)) • x
      rw [← hu, smul_smul, Units.inv_mul, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hx)
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact ⟨1, P.primeCompl.one_mem, by simpa using hy⟩
    | zero => exact Submodule.zero_mem _
    | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
    | smul c y _ hy =>
      obtain ⟨s, hs, hy⟩ := hy
      obtain ⟨⟨a, t⟩, h⟩ := IsLocalization.surj P.primeCompl c
      refine ⟨s * t, P.primeCompl.mul_mem hs t.2, ?_⟩
      have : (s * (t : R)) • c • y = a • s • y := by
        rw [mul_smul, ← algebraMap_smul (Localization.AtPrime P) (t : R), smul_smul _ c, mul_comm _ c]
        dsimp only at h
        rw [h, algebraMap_smul, smul_comm]
      rw [this]
      exact X.smul_mem a hy

theorem length_localized_eq₂ {R W : Type*} [CommRing R] (P : Ideal R) [P.IsMaximal] [AddCommGroup W] [Module R W]
    [Module (Localization.AtPrime P) W] [IsScalarTower R (Localization.AtPrime P) W] (X Y : Submodule R W) :
    Module.length R (↥(Formalism.HermitianLatticesTheory.localization₂ P X) ⧸ (Formalism.HermitianLatticesTheory.localization₂ P Y).comap (Formalism.HermitianLatticesTheory.localization₂ P X).subtype) =
      Module.length (Localization.AtPrime P) (↥(Submodule.span (Localization.AtPrime P) (X : Set W)) ⧸
        (Submodule.span (Localization.AtPrime P) (Y : Set W)).comap
          (Submodule.span (Localization.AtPrime P) (X : Set W)).subtype) := by
  rw [← length_eq_of_residue R _ _ (length_residue_atPrime P)]
  have hX : Formalism.HermitianLatticesTheory.localization₂ P X = (Submodule.span (Localization.AtPrime P) (X : Set W)).restrictScalars R :=
    Submodule.ext fun x => mem_localization_iff P X x
  have hY : Formalism.HermitianLatticesTheory.localization₂ P Y = (Submodule.span (Localization.AtPrime P) (Y : Set W)).restrictScalars R :=
    Submodule.ext fun x => mem_localization_iff P Y x
  rw [hX, hY]
  exact (Submodule.Quotient.restrictScalarsEquiv R ((Submodule.span (Localization.AtPrime P) (Y : Set W)).comap
          (Submodule.span (Localization.AtPrime P) (X : Set W)).subtype)).length_eq

theorem span_image_inf {A O V W : Type*} [CommRing A] [CommRing O] [Algebra A O] [Module.Flat A O]
    [AddCommGroup V] [Module A V] [AddCommGroup W] [Module A W] [Module O W] [IsScalarTower A O W]
    (φ : V →ₗ[A] W) (h : Function.Injective (φ.liftBaseChange O)) (M N : Submodule A V) :
    Submodule.span O (φ '' (M : Set V)) ⊓ Submodule.span O (φ '' (N : Set V)) =
      Submodule.span O (φ '' ((M ⊓ N : Submodule A V) : Set V)) := by
  have key : ∀ X : Submodule A V,
      Submodule.span O (φ '' (X : Set V)) = (X.baseChange O).map (φ.liftBaseChange O) := fun X => by
    rw [Submodule.baseChange_eq_span, Submodule.map_span, Submodule.map_coe, Set.image_image]
    congr 1
    exact Set.image_congr fun v _ => by simp
  rw [key, key, key, baseChange_inf, Submodule.map_inf _ h]

theorem exists_lidx_eq_mul (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    {d d' : ℕ} (ψ : (Fin d → K) →ₗ[K] (Fin d' → K')) (hψ : LinearIndependent K' (ψ ∘ Pi.basisFun K (Fin d)))
    (P : HeightOneSpectrum (𝓞 K)) (P' : HeightOneSpectrum (𝓞 K')) [P'.asIdeal.LiesOver P.asIdeal] :
    ∃ e : ℕ, 0 < e ∧ ∀ A B : Submodule (𝓞 K) (Fin d → K),
      Formalism.HermitianLatticesTheory.lidx P'.asIdeal (Submodule.span (𝓞 K') (ψ '' (A : Set (Fin d → K))))
        (Submodule.span (𝓞 K') (ψ '' (B : Set (Fin d → K)))) = Formalism.HermitianLatticesTheory.lidx P.asIdeal A B * e := by
  have hPm := P.isMaximal
  have hPm' := P'.isMaximal
  let O := Localization.AtPrime P.asIdeal
  let O' := Localization.AtPrime P'.asIdeal
  letI : Algebra O K := IsLocalization.localizationAlgebraOfSubmonoidLe O K P.asIdeal.primeCompl
    (nonZeroDivisors (𝓞 K)) P.asIdeal.primeCompl_le_nonZeroDivisors
  have : IsScalarTower (𝓞 K) O K := IsLocalization.localization_isScalarTower_of_submonoid_le O K _ _ _
  letI : Algebra O' K' := IsLocalization.localizationAlgebraOfSubmonoidLe O' K' P'.asIdeal.primeCompl
    (nonZeroDivisors (𝓞 K')) P'.asIdeal.primeCompl_le_nonZeroDivisors
  have : IsScalarTower (𝓞 K') O' K' := IsLocalization.localization_isScalarTower_of_submonoid_le O' K' _ _ _
  have : IsFractionRing O K := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P.asIdeal.primeCompl O K
  have : IsFractionRing O' K' :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P'.asIdeal.primeCompl O' K'
  have : IsScalarTower (𝓞 K) O' K' := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 K') O', ← IsScalarTower.algebraMap_apply (𝓞 K') O' K',
      ← IsScalarTower.algebraMap_apply]
  letI : Algebra O O' := Localization.AtPrime.algebraOfLiesOver P.asIdeal P'.asIdeal
  have : Localization.AtPrime.IsLiesOverAlgebra P.asIdeal P'.asIdeal := inferInstance
  have : IsScalarTower (𝓞 K) O O' := inferInstance
  have : IsLocalHom (algebraMap O O') := inferInstance
  have : IsDiscreteValuationRing O :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) P.ne_bot _
  have : IsDiscreteValuationRing O' :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K') P'.ne_bot _
  have : FaithfulSMul O O' := inferInstance
  have : Module.Flat O O' := inferInstance
  have : IsLocalHom (algebraMap O O) := inferInstance
  refine ⟨(maximalIdeal O').ramificationIdx O, ramificationIdx_maximalIdeal_pos O O', ?_⟩
  have hlen : ∀ M N : Submodule (𝓞 K) (Fin d → K), N ≤ M →
      Formalism.HermitianLatticesTheory.locLen P'.asIdeal (Submodule.span (𝓞 K') (ψ '' (M : Set (Fin d → K))))
        (Submodule.span (𝓞 K') (ψ '' (N : Set (Fin d → K)))) =
        Formalism.HermitianLatticesTheory.locLen P.asIdeal M N * (maximalIdeal O').ramificationIdx O := by
    intro M N hNM
    unfold Formalism.HermitianLatticesTheory.locLen
    rw [length_localized_eq₂, length_localized_eq₂, Submodule.span_span_of_tower, Submodule.span_span_of_tower]
    have h1 := Formalism.BasicNotions.FBC.length_flat_tower P.asIdeal (IsFractionRing.injective O' K') ψ _ hψ N M hNM
    have h2 := Formalism.BasicNotions.FBC.length_flat_tower P.asIdeal (IsFractionRing.injective O K)
      (LinearMap.id : (Fin d → K) →ₗ[K] (Fin d → K)) (Pi.basisFun K (Fin d))
      (Pi.basisFun K (Fin d)).linearIndependent N M hNM
    rw [length_fibre_eq_ramificationIdx O O'] at h1
    have h3 : Module.length O (O ⧸ (maximalIdeal O).map (algebraMap O O)) = 1 := by
      rw [Algebra.algebraMap_self, Ideal.map_id]
      have h4 := IsDiscreteValuationRing.length_quotient_pow_maximalIdeal O 1
      rw [pow_one] at h4
      exact_mod_cast h4
    rw [h3, mul_one, LinearMap.id_coe, Set.image_id, Set.image_id] at h2
    rw [h1, h2, ENat.toNat_mul, ENat.toNat_coe]
  intro A B
  have hinj := Formalism.BasicNotions.FBC.liftBaseChange_injective_top (A := 𝓞 K) (IsFractionRing.injective (𝓞 K') K') ψ _ hψ
  have hinf := span_image_inf _ hinj A B
  unfold Formalism.HermitianLatticesTheory.lidx
  erw [hinf]
  erw [hlen A _ inf_le_left, hlen B _ inf_le_right]
  push_cast
  ring

theorem lidx_ne_zero_iff : ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] (φ : K →+* K') (d d' : ℕ) (G : Matrix (Fin d') (Fin d) K'),
  Function.Bijective G.mulVec → ∀ (P : HeightOneSpectrum (𝓞 K)) (P' : HeightOneSpectrum (𝓞 K')),
  (∀ (x : 𝓞 K) (x' : 𝓞 K'), φ (x : K) = (x' : K') → (x ∈ P.asIdeal ↔ x' ∈ P'.asIdeal)) →
  ∀ A B : Submodule (𝓞 K) (Fin d → K), A.FG → B.FG →
    (Formalism.HermitianLatticesTheory.lidx P.asIdeal A B ≠ 0 ↔ Formalism.HermitianLatticesTheory.lidx P'.asIdeal
      (Submodule.span (𝓞 K') ((fun x : Fin d → K => Matrix.mulVec G fun k => φ (x k)) '' (A : Set (Fin d → K))))
      (Submodule.span (𝓞 K') ((fun x : Fin d → K => Matrix.mulVec G fun k => φ (x k)) '' (B : Set (Fin d → K)))) ≠ 0) := by
  intro K K' _ _ _ _ φ d d' G hG P P' hP A B _ _
  letI : Algebra K K' := φ.toAlgebra
  have : P'.asIdeal.LiesOver P.asIdeal := ⟨Ideal.ext fun x => hP x (algebraMap (𝓞 K) (𝓞 K') x) rfl⟩
  let ψ : (Fin d → K) →ₗ[K] (Fin d' → K') :=
    (G.mulVecLin.restrictScalars K) ∘ₗ (Algebra.linearMap K K').compLeft (Fin d)
  have hψ : LinearIndependent K' (ψ ∘ Pi.basisFun K (Fin d)) := by
    have h := (Pi.basisFun K' (Fin d)).linearIndependent.map' G.mulVecLin (LinearMap.ker_eq_bot.2 hG.1)
    have e : ψ ∘ Pi.basisFun K (Fin d) = G.mulVecLin ∘ Pi.basisFun K' (Fin d) := by
      funext i
      simp only [ψ, Function.comp_apply, LinearMap.comp_apply, LinearMap.restrictScalars_apply]
      congr 1
      funext k
      by_cases hk : k = i <;> simp [hk, Pi.single_apply]
    rw [e]
    exact h
  obtain ⟨e, he, h⟩ := exists_lidx_eq_mul K K' ψ hψ P P'
  have h' := h A B
  have hf : (fun x : Fin d → K => Matrix.mulVec G fun k => φ (x k)) = ψ := rfl
  rw [hf, h']
  simp [he.ne']

end GlobalTheory.LidxBaseChange
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeIndexNonzeroIffUnderFieldMapStatement
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_index_nonzero_iff_under_field_map : ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] (φ : K →+* K') (d d' : ℕ) (G : Matrix (Fin d') (Fin d) K'),
  Function.Bijective G.mulVec → ∀ (P : HeightOneSpectrum (𝓞 K)) (P' : HeightOneSpectrum (𝓞 K')),
  (∀ (x : 𝓞 K) (x' : 𝓞 K'), φ (x : K) = (x' : K') → (x ∈ P.asIdeal ↔ x' ∈ P'.asIdeal)) →
  ∀ A B : Submodule (𝓞 K) (Fin d → K), A.FG → B.FG →
    (Formalism.HermitianLatticesTheory.lidx P.asIdeal A B ≠ 0 ↔ Formalism.HermitianLatticesTheory.lidx P'.asIdeal
      (Submodule.span (𝓞 K') ((fun x : Fin d → K => Matrix.mulVec G fun k => φ (x k)) '' (A : Set (Fin d → K))))
      (Submodule.span (𝓞 K') ((fun x : Fin d → K => Matrix.mulVec G fun k => φ (x k)) '' (B : Set (Fin d → K)))) ≠ 0) := by
  first | exact @GlobalTheory.LidxBaseChange.lidx_ne_zero_iff | exact GlobalTheory.LidxBaseChange.lidx_ne_zero_iff | (intros; apply GlobalTheory.LidxBaseChange.lidx_ne_zero_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianDualLatticeBaseChange
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.Mem.DualBC

variable {K : Type} [Field K] [NumberField K] [StarRing K]


omit [NumberField K] in
theorem mem_dual_iff {d : ℕ} (H : Matrix (Fin d) (Fin d) K) (A : Submodule (𝓞 K) (Fin d → K)) (x : Fin d → K) :
    x ∈ Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform H) A ↔
      ∀ y ∈ A, ∃ c : 𝓞 K, algebraMap (𝓞 K) K c = Formalism.DivisionValues.hform H y x := by
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply, Submodule.mem_one]


omit [NumberField K] in
theorem hform_eq {d : ℕ} (H : Matrix (Fin d) (Fin d) K) (x y : Fin d → K) :
    Formalism.DivisionValues.hform H x y = ∑ j, star (x j) * (H.mulVec y) j := by
  simp only [Formalism.DivisionValues.hform, Matrix.toLinearMapₛₗ₂'_apply, starRingEnd_apply, RingHom.id_apply,
    Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [smul_eq_mul]
  ring


omit [NumberField K] in
theorem star_int (c : 𝓞 K) : algebraMap (𝓞 K) K (Formalism.DivisionValues.cO K c) = star (algebraMap (𝓞 K) K c) := rfl


omit [StarRing K] in
theorem exists_extend {d : ℕ} (A : Submodule (𝓞 K) (Fin d → K)) (hA : Submodule.IsFullLattice K A)
    (f : A →ₗ[𝓞 K] 𝓞 K) :
    ∃ F : (Fin d → K) →ₗ[K] K, ∀ x : A, F x = algebraMap (𝓞 K) K (f x) := by
  classical
  have hinj : Function.Injective (algebraMap (𝓞 K) K) := FaithfulSMul.algebraMap_injective _ _
  obtain ⟨s, hs, b, hb, hsA⟩ := Formalism.HermitianLatticesTheory.dualLattice_basis (R := 𝓞 K) A hA.span_eq_top
  obtain ⟨c, hc0, hc⟩ := Formalism.HermitianLatticesTheory.dualLattice_denom (R := 𝓞 K) b A hA.fg
  have hbA : ∀ i, b i ∈ A := fun i => by rw [hb i]; exact hsA i.2
  let F : (Fin d → K) →ₗ[K] K := b.constr K (fun i => algebraMap (𝓞 K) K (f ⟨b i, hbA i⟩))
  let F' : A →ₗ[𝓞 K] K := (F.restrictScalars (𝓞 K)).comp A.subtype
  let g' : A →ₗ[𝓞 K] K := (Algebra.linearMap (𝓞 K) K).comp f
  let P : Submodule (𝓞 K) (Fin d → K) := (LinearMap.eqLocus F' g').map A.subtype
  have hspan : Submodule.span (𝓞 K) (Set.range b) ≤ P := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨⟨b i, hbA i⟩, ?_, rfl⟩
    show F (b i) = algebraMap (𝓞 K) K (f ⟨b i, hbA i⟩)
    exact b.constr_basis K _ i
  refine ⟨F, fun x => ?_⟩
  obtain ⟨z, hz, hzx⟩ := hspan (hc x x.2)
  have hz' : z = c • x := Subtype.ext (by simpa using hzx)
  have hzF : F' z = g' z := hz
  rw [hz', map_smul, map_smul] at hzF
  simp only [F', g', LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.restrictScalars_apply,
    Algebra.linearMap_apply, Algebra.smul_def] at hzF
  exact mul_left_cancel₀ (by simpa using hc0) hzF

theorem exists_family {d : ℕ} (H : Matrix (Fin d) (Fin d) K) (hH : IsUnit H.det)
    (A : Submodule (𝓞 K) (Fin d → K)) (hA : Submodule.IsFullLattice K A) :
    ∃ (n : ℕ) (a b : Fin n → Fin d → K), (∀ i, a i ∈ A) ∧ (∀ i, b i ∈ Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform H) A) ∧
      ∀ y, y = ∑ i, Formalism.DivisionValues.hform H (a i) y • b i := by
  classical
  have hinj : Function.Injective (algebraMap (𝓞 K) K) := FaithfulSMul.algebraMap_injective _ _
  obtain ⟨n, g, f, hgf⟩ := Formalism.HermitianLatticesTheory.finitely_generated_projective_coords (K := K) A hA.fg hinj
  choose F hF using fun i => exists_extend A hA (f i)
  let w : Fin n → Fin d → K := fun i => H⁻¹.mulVec (fun j => star (F i (Pi.single j 1)))
  have hFcoord : ∀ i (y : Fin d → K), F i y = ∑ j, y j * F i (Pi.single j 1) := by
    intro i y
    conv_lhs => rw [← Finset.univ_sum_single y]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show (Pi.single j (y j) : Fin d → K) = y j • Pi.single j 1 by
      ext k; by_cases hk : k = j <;> simp [hk], map_smul, smul_eq_mul]
  have hw : ∀ i (y : Fin d → K), Formalism.DivisionValues.hform H y (w i) = star (F i y) := by
    intro i y
    rw [hform_eq, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hH, Matrix.one_mulVec, hFcoord,
      star_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [star_mul']
  have hexp : ∀ y : Fin d → K, y = ∑ i, F i y • (g i : Fin d → K) := by
    have hT : (∑ i, (F i).smulRight (g i : Fin d → K)) = LinearMap.id := by
      refine LinearMap.ext_on hA.span_eq_top fun x hx => ?_
      have h1 := congrArg (fun v : A => (v : Fin d → K)) (hgf ⟨x, hx⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h1
      simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.id_apply]
      conv_rhs => rw [h1]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hF i ⟨x, hx⟩, algebraMap_smul]
    intro y
    have := LinearMap.congr_fun hT y
    simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.id_apply] at this
    exact this.symm
  have hnd : ∀ z : Fin d → K, (∀ u, Formalism.DivisionValues.hform H u z = 0) → z = 0 := by
    intro z hz
    have hHz : H.mulVec z = 0 := by
      ext i
      have := hz (Pi.single i 1)
      rw [hform_eq, Finset.sum_eq_single i (fun j _ hj => by simp [hj])
        (by simp)] at this
      simpa using this
    rw [← Matrix.one_mulVec z, ← Matrix.nonsing_inv_mul _ hH, ← Matrix.mulVec_mulVec, hHz,
      Matrix.mulVec_zero]
  refine ⟨n, fun i => (g i : Fin d → K), w, fun i => (g i).2, fun i => ?_, fun y => ?_⟩
  · rw [mem_dual_iff]
    intro y hy
    refine ⟨Formalism.DivisionValues.cO K (f i ⟨y, hy⟩), ?_⟩
    rw [star_int, hw, hF i ⟨y, hy⟩]
  · refine (sub_eq_zero.1 (hnd _ fun u => ?_)).symm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, sub_eq_zero, map_sum]
    conv_rhs => rw [hexp u]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, map_smulₛₗ, LinearMap.smul_apply, hw, smul_eq_mul, smul_eq_mul,
      starRingEnd_apply, mul_comm]

theorem dual_baseChange : ∀ (K K' : Type) [Field K] [NumberField K] [StarRing K] [Field K'] [NumberField K'] [StarRing K'] (φ : K →+* K') (d d' : ℕ)
  (G : Matrix (Fin d') (Fin d) K'), Function.Bijective G.mulVec → ∀ (H : Matrix (Fin d) (Fin d) K) (H' : Matrix (Fin d') (Fin d') K'),
  (∀ x y : Fin d → K, Formalism.DivisionValues.hform H' (Matrix.mulVec G fun k => φ (x k)) (Matrix.mulVec G fun k => φ (y k)) = φ (Formalism.DivisionValues.hform H x y)) →
  IsUnit H.det → ∀ A : Submodule (𝓞 K) (Fin d → K), Submodule.IsFullLattice K A →
    Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform H')
      (Submodule.span (𝓞 K') ((fun x : Fin d → K => Matrix.mulVec G fun k => φ (x k)) '' (A : Set (Fin d → K)))) =
    Submodule.span (𝓞 K') ((fun x : Fin d → K => Matrix.mulVec G fun k => φ (x k)) ''
      ((Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform H) A : Submodule (𝓞 K) (Fin d → K)) : Set (Fin d → K))) := by
  intro K K' _ _ _ _ _ _ φ d d' G hG H H' hHH' hH A hA
  classical
  set ι : (Fin d → K) → (Fin d' → K') := fun x => Matrix.mulVec G fun k => φ (x k) with hι
  have ι_add : ∀ x y, ι (x + y) = ι x + ι y := by
    intro x y
    simp only [hι, Pi.add_apply, map_add (f := _)]
    rw [← Matrix.mulVec_add]
    rfl
  have ι_smul : ∀ (c : K) x, ι (c • x) = φ c • ι x := by
    intro c x
    simp only [hι, Pi.smul_apply, smul_eq_mul, map_mul]
    rw [← Matrix.mulVec_smul]
    rfl
  have ι_sum : ∀ {m : ℕ} (v : Fin m → Fin d → K), ι (∑ i, v i) = ∑ i, ι (v i) := by
    intro m v
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hι, Finset.sum_apply, map_sum]
    rw [← Matrix.mulVec_sum]
    congr 1
    ext k
    simp [Finset.sum_apply]
  have ι_single : ∀ k : Fin d, ι (Pi.single k 1) = G.mulVec (Pi.single k 1) := by
    intro k
    simp only [hι]
    congr 1
    ext j
    by_cases hj : j = k <;> simp [hj]
  have hspanι : Submodule.span K' (Set.range ι) = ⊤ := by
    refine eq_top_iff.2 fun z _ => ?_
    obtain ⟨v, rfl⟩ := hG.2 z
    rw [← Finset.univ_sum_single v, Matrix.mulVec_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [show (Pi.single k (v k) : Fin d → K') = v k • Pi.single k 1 by
      ext j; by_cases hj : j = k <;> simp [hj], Matrix.mulVec_smul, ← ι_single]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  have hιH : ∀ x y, Formalism.DivisionValues.hform H' (ι x) (ι y) = φ (Formalism.DivisionValues.hform H x y) := hHH'
  apply le_antisymm
  · intro x hx
    obtain ⟨n, a, b, ha, hb, hab⟩ := exists_family H hH A hA
    have hT : (∑ i, (Formalism.DivisionValues.hform H' (ι (a i))).smulRight (ι (b i))) = LinearMap.id := by
      refine LinearMap.ext_on hspanι ?_
      rintro _ ⟨y, rfl⟩
      simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.id_apply,
        hιH]
      conv_rhs => rw [hab y]
      rw [ι_sum]
      simp only [ι_smul]
    have hx' : x = ∑ i, Formalism.DivisionValues.hform H' (ι (a i)) x • ι (b i) := by
      have := LinearMap.congr_fun hT x
      simp only [LinearMap.sum_apply, LinearMap.smulRight_apply,
        LinearMap.id_apply] at this
      exact this.symm
    rw [hx']
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨c, hc⟩ := (mem_dual_iff H' _ x).1 hx (ι (a i))
      (Submodule.subset_span ⟨a i, ha i, rfl⟩)
    rw [← hc, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b i, hb i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨z, hz, rfl⟩
    rw [SetLike.mem_coe, mem_dual_iff]
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨y, hy, rfl⟩ := hy
      obtain ⟨c, hc⟩ := (mem_dual_iff H A z).1 hz y hy
      refine ⟨RingOfIntegers.mapRingHom φ c, ?_⟩
      rw [hιH, ← hc]
      rfl
    | zero => exact ⟨0, by simp⟩
    | add y₁ y₂ _ _ h₁ h₂ =>
      obtain ⟨c₁, hc₁⟩ := h₁
      obtain ⟨c₂, hc₂⟩ := h₂
      exact ⟨c₁ + c₂, by rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, hc₁, hc₂]⟩
    | smul r y _ h =>
      obtain ⟨c, hc⟩ := h
      refine ⟨Formalism.DivisionValues.cO K' r * c, ?_⟩
      rw [← algebraMap_smul K' r y, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, map_mul, hc,
        star_int, starRingEnd_apply]

end GlobalTheory.Mem.DualBC

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtendedDataNonzeroIndexPlacesCorrespond
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.TwistedPlaceExtensions

theorem exists_hom_of_range {K K' : Type} [Field K] [Field K'] (σ : K →+* ℂ) (σ' : K' →+* ℂ) (h : Set.range σ ⊆ Set.range σ') :
    ∃ φ : K →+* K', ∀ x, σ' (φ x) = σ x := by
  choose g hg using fun x => h ⟨x, rfl⟩
  exact ⟨{ toFun := g
           map_one' := σ'.injective (by rw [hg, map_one, map_one])
           map_mul' := fun a b => σ'.injective (by rw [map_mul σ', hg, hg, hg, map_mul])
           map_zero' := σ'.injective (by rw [hg, map_zero, map_zero])
           map_add' := fun a b => σ'.injective (by rw [map_add σ', hg, hg, hg, map_add (f := _)]) }, hg⟩


set_option maxHeartbeats 4000000 in
theorem extendedData_nonzero_index_places_correspond : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ v v', Below (w.D Z) (w'.D Z') v v' → (v ∈ z.W1 (fun _ _ => 0) ↔ v' ∈ z'.W1 fun _ _ => 0)) := by
  intro h1 h2 h3 h4 h5 h6 h7
  refine StepW.trans (StepW.and (GlobalTheory.T.liftFormsLattice_definiteLattice_baseChange_extended h1 h2 h3 h4 h5 h6 h7) (GlobalTheory.T.extendedData_definiteLiftLattice_baseChange h1 h2 h3 h4 h5 h6 h7)) (StepW.of_all ?_)
  intro K B' f' T' w' _ _ hIJ B f T w hE hff hPin hpx Z hX Wt z hG hGA hFine hHL Z' hX' hG' hGA' hVol z' hFine' hExt v v' hB
  have hm : (w.st Z).toD7.R.m = (w'.st Z').toD7.R.m := congrArg (fun P : Pre => P.R.m) hE.1.symm
  obtain ⟨φ, hφ⟩ := exists_hom_of_range (w.st Z).toD7.what₂.embLL (w'.st Z').toD7.what₂.embLL hE.2.2.2
  have hok := hHL.ok.ok2
  refine mem_zeroContentPlaces_iff_over_of_nonvanishing z z' hm (fun j j' hj P P' hPP => ?_) v v' hB
  have hP : ∀ (x : 𝓞 (w.st Z).toD7.what₂.LL) (x' : 𝓞 (w'.st Z').toD7.what₂.LL), φ (x : (w.st Z).toD7.what₂.LL) = (x' : (w'.st Z').toD7.what₂.LL) →
      (x ∈ P.asIdeal ↔ x' ∈ P'.asIdeal) := fun x x' e => hPP x x' (by rw [← e, hφ])
  have hT : Submodule.IsLattice (w.st Z).toD7.what₂.LL (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).Tl j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) := Formalism.L2.DIV.BlockDat.Tl_lat hok.conj (hok.lifts j _) hok.irr
  have hTfull : Submodule.IsFullLattice (w.st Z).toD7.what₂.LL (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).Tl j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) :=
    Formalism.L2.DIV.BlockDat.Tl_full hok.conj (hok.lifts j _) hok.irr
  have hH : IsUnit (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).HT j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).det := Formalism.L2.DIV.BlockDat.HZ_det hok.conj (hok.lifts j _) hok.irr
  obtain ⟨G, hG1, hG2, hG3⟩ := hIJ.1 B f T w hE hff hPin hpx Z hX Wt z hG hGA hFine hHL Z' hX' hG' hGA' hVol z' hFine' hExt j j' hj φ hφ
  obtain ⟨N, hN1, hN2, hN3⟩ := hIJ.2 B f T w hE hff hPin hpx Z hX Wt z hG hGA hFine hHL Z' hX' hG' hGA' hVol z' hFine' hExt j j' hj φ hφ
  refine nzAt_iff_of z z' j j' P P' ?_ ?_
  · have k := GlobalTheory.T.lattice_index_nonzero_iff_under_field_map _ _ φ _ _ G hG1 P P' hP ((s0Of z.R z.F).M j)
      (Formalism.DivisionValues.matLat ((s0Of z.R z.F).θ j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).Tl j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0)) (hHL.mLat j).fg (hT.fg.map _)
    rw [← hG2, ← hG3] at k
    exact k
  · have k := GlobalTheory.T.lattice_index_nonzero_iff_under_field_map _ _ φ _ _ N hN1 P P' hP _ _ hT.fg (GlobalTheory.Mem.NonzeroPlacesOverPrimes.dual_fg _ hH _ hTfull)
    rw [← GlobalTheory.Mem.DualBC.dual_baseChange _ _ φ _ _ N hN1 _ _ hN3 hH _ hTfull, ← hN2] at k
    exact k

end GlobalTheory.Mem.R3.TwistedPlaceExtensions

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtendedDataNonzeroIndexPlacesCorrespondStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extendedData_nonzero_index_places_correspond_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ v v', Below (w.D Z) (w'.D Z') v v' → (v ∈ z.W1 (fun _ _ => 0) ↔ v' ∈ z'.W1 fun _ _ => 0)) := by
  first | exact @GlobalTheory.Mem.R3.TwistedPlaceExtensions.extendedData_nonzero_index_places_correspond | exact GlobalTheory.Mem.R3.TwistedPlaceExtensions.extendedData_nonzero_index_places_correspond | (intros; apply GlobalTheory.Mem.R3.TwistedPlaceExtensions.extendedData_nonzero_index_places_correspond <;> assumption)
end
end

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw


set_option maxHeartbeats 4000000 in
theorem datExt0_of_hypotheses : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → DatExt0 := by
  intro h1 h2 h3 h4 h5 h6 h7
  refine ((GlobalTheory.T.exists_extendedColumnData_all_clauses_but_places h1 h2 h3 h4 h5 h6 h7).and (GlobalTheory.T.extendedData_nonzero_index_places_correspond_alt h1 h2 h3 h4 h5 h6 h7)).trans (StepW.of_all ?_)
  intro K B' f' T' w' _ _ hAB B f T w hE hf hP hpx Z hX Wt z hg hga hF hL Z' hX' hg' hga' hV
  obtain ⟨z', hz', he⟩ := hAB.1 B f T w hE hf hP hpx Z hX Wt z hg hga hF hL Z' hX' hg' hga' hV
  exact ⟨z', hz', he.ext (hAB.2 B f T w hE hf hP hpx Z hX Wt z hg hga hF hL Z' hX' hg' hga' hV z' hz' he)⟩

end GlobalTheory.Mem.R3.Rw

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicData_extend_largerFields_of_hypotheses : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → DatExt0 := by
  first | exact @GlobalTheory.Mem.R3.Rw.datExt0_of_hypotheses | exact GlobalTheory.Mem.R3.Rw.datExt0_of_hypotheses | (intros; apply GlobalTheory.Mem.R3.Rw.datExt0_of_hypotheses <;> assumption)
