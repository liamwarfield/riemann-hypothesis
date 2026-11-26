module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionOfNumericsModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassSumsSpanCuspFormsBaseTupleSecondField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupLiftTangentPhiLinear
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoefScale
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IInfThetaGeneratorsLeLocalDepthPrimeToLevel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassesAt
public import ReciprocityTheory.ReductiveGroups.LatticeEmbeddings.IotaPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianHomExtensionHolds
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelLiftIsLiftPrincipalLevelDatumRealisation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoTangentPullConstantDeformation

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneFormMapRowThreeLevelOfCharacterisation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormsAgreementContainsFormIndependentFields
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormsAgreementContainsFormIndependentFields
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem tieIn_of_nonempty_tie :
    ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) , Nonempty (FWTie T R κ v₀) → TieIn T R κ v₀ :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ ⟨fw⟩ => ⟨fw.laws, fw.alg_eq, fw.kap, fw.hv₀, fw.chiR, fw.x0⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormsAgreementContainsFormIndependentFieldsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspFormsAgreement_contains_formIndependentFields : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) , Nonempty (FWTie T R κ v₀) → TieIn T R κ v₀ := by
  first | exact @GlobalTheory.tieIn_of_nonempty_tie | exact GlobalTheory.tieIn_of_nonempty_tie | (intros; apply GlobalTheory.tieIn_of_nonempty_tie <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapAllTuplesOverCoreOfRankBound
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapRowAllTuplesOfCoreClauses
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaOneMapIdentityEveryNormalisedFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaOneMapIdentityEveryNormalisedFamily
set_option autoImplicit false

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OneMapAll

theorem identityRow_of_core : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) , GlobalTheory.Hk3.Core R F → TieIn T R κ v₀ → IoExt R → ∀ i, GlobalTheory.OneMapAll.IdentityRow T R κ v₀ i := by
  intro hCI D G _ _ Pl0 T0 A T _ R F κ v₀ hR ht hio i Tp tup O _ hO
  obtain ⟨cc, -, u, -, -, -, h⟩ := GlobalTheory.T.exists_unitModulus_constants_equivariant_dictionary hCI D G Pl0 T0 A T R F κ v₀ hR ht hio i Tp tup O hO
  exact ⟨u • cc, 1, h⟩

end GlobalTheory.OneMapAll
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaOneMapIdentityEveryNormalisedFamilyStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaOneMap_identity_every_normalised_family : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) , GlobalTheory.Hk3.Core R F → TieIn T R κ v₀ → IoExt R → ∀ i, GlobalTheory.OneMapAll.IdentityRow T R κ v₀ i := by
  first | exact @GlobalTheory.OneMapAll.identityRow_of_core | exact GlobalTheory.OneMapAll.identityRow_of_core | (intros; apply GlobalTheory.OneMapAll.identityRow_of_core <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapRowAllTuplesOfCoreClauses
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OneMapCore

theorem oneMapRowR_of_core : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), GlobalTheory.Hk3.Core R F → R.tup_mu_off → R.tup_mu_used → Nonempty (FWTie T R κ v₀) → IoExt R → ∀ i, OMPins T R κ v₀ O i → PhaseTie T R κ v₀ O ph i → GlobalTheory.OneMapAll.ClassSumsSpan (O i) (κ i) → OneMapRowR T R κ v₀ O ph i := by
  intro hCI D G _ _ Pl0 T0 A T _ R F κ v₀ O ph hR hoff hused hfw hio i hpins htie hspan
  have hin : TieIn T R κ v₀ := GlobalTheory.T.cuspFormsAgreement_contains_formIndependentFields D G Pl0 T0 A T R κ v₀ hfw
  refine GlobalTheory.T.oneMapRow_of_baseTuple_identityRow_span D G Pl0 T0 A T R κ v₀ O ph i hR.lev hR.grp.chiW hR.fam hR.models hpins htie
    (GlobalTheory.T.thetaOneMap_baseTuple_of_characterisation_extremal hCI D G Pl0 T0 A T R F κ v₀ hR hin hio O i hpins) (fun hG => ?_)
    (GlobalTheory.T.thetaOneMap_identity_every_normalised_family hCI D G Pl0 T0 A T R F κ v₀ hR hin hio i) hspan
  obtain ⟨O', h1, h2, -⟩ := GlobalTheory.T.exists_normalisedData_allTuples_of_baseTuple D G Pl0 T0 A T R κ v₀ O hR.lev hR.grp.chiW hR.fam hR.models hR.thP.vP hoff hused
    hfw i hpins hG
  exact ⟨O', h1, h2⟩

end GlobalTheory.OneMapCore
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapRowAllTuplesOfCoreClausesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oneMapRow_all_tuples_of_core_clauses : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), GlobalTheory.Hk3.Core R F → R.tup_mu_off → R.tup_mu_used → Nonempty (FWTie T R κ v₀) → IoExt R → ∀ i, OMPins T R κ v₀ O i → PhaseTie T R κ v₀ O ph i → GlobalTheory.OneMapAll.ClassSumsSpan (O i) (κ i) → OneMapRowR T R κ v₀ O ph i := by
  first | exact @GlobalTheory.OneMapCore.oneMapRowR_of_core | exact GlobalTheory.OneMapCore.oneMapRowR_of_core | (intros; apply GlobalTheory.OneMapCore.oneMapRowR_of_core <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapAllTuplesOverCoreOfRankBound
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OneMapCore

theorem oneMapRowR_of_core_of_size :
    ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → R.tup_mu_off → R.tup_mu_used → Nonempty (FWTie T R κ v₀) → IoExt R → ∀ i, OMPins T R κ v₀ O i → PhaseTie T R κ v₀ O ph i → OneMapRowR T R κ v₀ O ph i := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ O ph hn hC hoff hused hT hI i hP hph
  have hci : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 := GlobalTheory.chartIndependence_unconditional
  have h0 : OneMapRow0 T R κ v₀ O i :=
    GlobalTheory.T.thetaOneMap_baseTuple_of_characterisation_extremal hci D G Pl0 T0 A T R F κ v₀ hC (GlobalTheory.T.cuspFormsAgreement_contains_formIndependentFields D G Pl0 T0 A T R κ v₀ hT) hI O i hP
  exact GlobalTheory.T.oneMapRow_all_tuples_of_core_clauses hci D G Pl0 T0 A T R F κ v₀ O ph hC hoff hused hT hI i hP hph
    (GlobalTheory.T.classSums_span_cuspForms_baseTuple_second_field D G Pl0 T0 A T R F κ v₀ O hn hC hT hI i hP h0)

end GlobalTheory.OneMapCore
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapAllTuplesOverCoreOfRankBoundStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oneMap_all_tuples_over_core_of_rankBound : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → R.tup_mu_off → R.tup_mu_used → Nonempty (FWTie T R κ v₀) → IoExt R → ∀ i, OMPins T R κ v₀ O i → PhaseTie T R κ v₀ O ph i → OneMapRowR T R κ v₀ O ph i := by
  first | exact @GlobalTheory.OneMapCore.oneMapRowR_of_core_of_size | exact GlobalTheory.OneMapCore.oneMapRowR_of_core_of_size | (intros; apply GlobalTheory.OneMapCore.oneMapRowR_of_core_of_size <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneFormMapRowThreeLevelOfCharacterisation
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OneMapRow3

theorem oneFormMapRow_threeLevel_of_characterisation : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → R.WeakCharacterisation F → R.toRealDat.ExAt → Nonempty (FWTie T R.toRealDat κ v₀) → IoExt R.toRealDat → ∀ i, OMPins T R.toRealDat κ v₀ O i → PhaseTie T R.toRealDat κ v₀ O ph i → OneMapRowR T R.toRealDat κ v₀ O ph i := by
  intro D G _ _ Pl0 I0 T0 A3 T _ R F κ v₀ O ph hn hC hE hFW hIo i hP hT
  obtain ⟨hcore, hoff, hused⟩ := GlobalTheory.T.hk3Core_and_tup_mu_of_weakCharacterisation D G Pl0 I0 T0 A3 T.Q.c.F R F hC hE
  exact GlobalTheory.T.oneMap_all_tuples_over_core_of_rankBound D G Pl0 T0 A3.A T R.toRealDat F.lv2 κ v₀ O ph hn hcore hoff hused hFW hIo i hP hT

end GlobalTheory.OneMapRow3
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneFormMapRowThreeLevelOfCharacterisationStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oneMapRowR_of_weakCharacterisation : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → R.WeakCharacterisation F → R.toRealDat.ExAt → Nonempty (FWTie T R.toRealDat κ v₀) → IoExt R.toRealDat → ∀ i, OMPins T R.toRealDat κ v₀ O i → PhaseTie T R.toRealDat κ v₀ O ph i → OneMapRowR T R.toRealDat κ v₀ O ph i := by
  first | exact @GlobalTheory.OneMapRow3.oneFormMapRow_threeLevel_of_characterisation | exact GlobalTheory.OneMapRow3.oneFormMapRow_threeLevel_of_characterisation | (intros; apply GlobalTheory.OneMapRow3.oneFormMapRow_threeLevel_of_characterisation <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusActionModelCoordinates
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusActionModelCoordinates
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical
noncomputable section
namespace GlobalTheory.TorusDilate

variable {F : Type} [Field F] [NumberField F]

theorem infScale_inv_mul (t : ℝ) (ht : t ≠ 0) (a : AF F) :
    GlobalTheory.TorusTheta.infScale F t⁻¹ * (GlobalTheory.TorusTheta.infScale F t * a) = a := by
  have h : GlobalTheory.TorusTheta.infScale F t⁻¹ * GlobalTheory.TorusTheta.infScale F t = 1 := by
    unfold GlobalTheory.TorusTheta.infScale
    refine Prod.ext ?_ ?_
    · show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ t⁻¹) *
        (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ t) = 1
      rw [← map_mul, ← map_mul, inv_mul_cancel₀ ht, map_one, map_one]
    · show (1 : FiniteAdeleRing (𝓞 F) F) * 1 = 1
      exact one_mul 1
  rw [← mul_assoc, h, one_mul]

theorem proj_zero_mem_adm' (κ : Type) [Fintype κ] :
    (LinearMap.proj (R := ℂ) (φ := fun _ : (κ → AF F) => ℂ) 0) ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨g 0 • (BoundedContinuousFunction.evalCLM ℂ 0).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ), fun f => ?_⟩
  simp only [LinearMap.proj_apply, pureA, ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_comp',
    Function.comp_apply, Pi.smul_apply, SchwartzMap.toBoundedContinuousFunctionCLM_apply,
    BoundedContinuousFunction.evalCLM_apply, smul_eq_mul]
  have h1 : (fun i : κ => InfiniteAdeleRing.ringEquiv_mixedSpace F ((0 : κ → AdeleRing (𝓞 F) F) i).1) = 0 := by
    funext i; exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  have h2 : (fun i : κ => ((0 : κ → AdeleRing (𝓞 F) F) i).2) = 0 := by
    funext i; rfl
  rw [h1, h2, mul_comm]

theorem memLp_of_mem_schA {κ : Type} [Fintype κ] (μ : @Measure (κ → AF F) (borel _))
    (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    (letI : MeasurableSpace (κ → AF F) := borel _; MemLp Φ 2 μ) := by
  letI mA : MeasurableSpace (κ → AF F) := borel _
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    exact GlobalTheory.ThetaSobolevBase.memLp_pureA μ hμ f hg
  | zero => exact MemLp.zero
  | add _ _ _ _ h1 h2 => exact h1.add h2
  | smul c _ _ h => exact h.const_smul c

theorem lintegral_sq_ne_zero {κ : Type} [Fintype κ] (μ : @Measure (κ → AF F) (borel _))
    (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) {Φ : (κ → AF F) → ℂ} (hc : Continuous Φ) (h0 : Φ 0 ≠ 0) :
    ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ ≠ 0 := by
  letI mA : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  intro h
  have hm : AEMeasurable (fun x => ‖Φ x‖ₑ ^ 2) μ := (hc.measurable.enorm.pow_const 2).aemeasurable
  rw [lintegral_eq_zero_iff' hm] at h
  have h' : Φ =ᵐ[μ] 0 := h.mono fun x hx => by
    simpa using hx
  have := (hc.ae_eq_iff_eq μ continuous_const).1 h'
  exact h0 (congrFun this 0)

end GlobalTheory.TorusDilate

namespace GlobalTheory.TorusDilate

theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (g : UA σ X.J) (u : Fin n × Fin d → ℝ), (∀ j, 0 < u j) →
    (∀ z : Matrix (Fin n) (Fin d) (AE F E), M.co.e (mat g * z) =
      (fun j => GlobalTheory.TorusTheta.infScale F ((u j)⁻¹) * (M.co.e z).1 j,
       fun j => GlobalTheory.TorusTheta.infScale F (u j) * (M.co.e z).2 j)) →
    ∃ κ : ℂ, ‖κ‖ ^ 2 = ∏ j, u j ^ Module.finrank ℚ F ∧
      ∀ Φ ∈ schA F (Fin n × Fin d), ∀ x, om (g, 1) Φ x = κ * Φ (fun j => GlobalTheory.TorusTheta.infScale F (u j) * x j) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP g u hu hg
  have hψ : IsStd B.ψ := hP.base.std
  have hS := IsUWeilPair.isUSplitting hP.weil
  have hact : ∀ w, actAB (cA σ) (g, (1 : UA σ W.J)) w = mat g * w := fun w => by
    simp [actAB, mat]
  have himpl : ∀ w, ∀ φ ∈ schA F (Fin n × Fin d),
      om (g, 1) (schr B.ψ (M.co.e w) φ) = schr B.ψ (M.co.e (mat g * w)) (om (g, 1) φ) := fun w φ hφ => by
    have := hS.impl (g, 1) w φ hφ
    rw [hact] at this
    exact this
  set l₁ : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ :=
    (LinearMap.proj (R := ℂ) (φ := fun _ : (Fin n × Fin d → AF F) => ℂ) 0) ∘ₗ om (g, 1) with hl₁
  have hadm : l₁ ∈ (adeleClass F).adm (Fin n × Fin d) := hS.adm (g, 1) _ (proj_zero_mem_adm' _)
  obtain ⟨c, hc⟩ := GlobalTheory.T.character_invariant_adelic_form_eq_mul_eval_zero F B.ψ hψ (Fin n × Fin d) l₁ hadm (fun y φ hφ => by
    have e : (fun x => B.ψ (x ⬝ᵥ y) * φ x) = schr B.ψ (M.co.e (M.co.e.symm (0, y))) φ := by
      funext x; simp [schr]
    rw [e]
    simp only [hl₁, LinearMap.comp_apply, LinearMap.proj_apply]
    rw [himpl _ φ hφ, hg]
    (simp [schr, dotProduct]) <;> rfl)
  have hval : ∀ Φ ∈ schA F (Fin n × Fin d), ∀ x,
      om (g, 1) Φ x = c * Φ (fun j => GlobalTheory.TorusTheta.infScale F (u j) * x j) := fun Φ hΦ x => by
    set p : (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F) :=
      (fun j => GlobalTheory.TorusTheta.infScale F (u j) * x j, 0) with hp
    have hmem := GlobalTheory.HeisSchA.schr_mem_schA B.ψ hψ p Φ hΦ
    have h1 := hc _ hmem
    simp only [hl₁, LinearMap.comp_apply, LinearMap.proj_apply] at h1
    have e : schr B.ψ p Φ = schr B.ψ (M.co.e (M.co.e.symm p)) Φ := by rw [LinearEquiv.apply_symm_apply]
    rw [e, himpl _ Φ hΦ, hg, LinearEquiv.apply_symm_apply] at h1
    have hx : (fun j => GlobalTheory.TorusTheta.infScale F (u j)⁻¹ * (GlobalTheory.TorusTheta.infScale F (u j) * x j)) = x :=
      funext fun j => infScale_inv_mul (u j) (hu j).ne' (x j)
    simp only [hp, hx] at h1
    simpa [schr, dotProduct] using h1
  refine ⟨c, ?_, hval⟩

  letI mA : MeasurableSpace (Fin n × Fin d → AF F) := borel _
  haveI : BorelSpace (Fin n × Fin d → AF F) := ⟨rfl⟩
  let μ : Measure (Fin n × Fin d → AF F) := Measure.addHaar
  have hμ : μ.IsAddHaarMeasure := inferInstance
  obtain ⟨Φ, hΦ, h0⟩ := GlobalTheory.SchANonzero.exists_mem_schA_ne_zero F (Fin n × Fin d)
  have hI0 : ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ ≠ 0 :=
    lintegral_sq_ne_zero μ hμ (GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA (F := F) hΦ) h0
  have hIt : ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ ≠ ⊤ := by
    have h2 := (memLp_of_mem_schA μ hμ hΦ).eLpNorm_lt_top
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)] at h2
    · simpa using h2.ne
    · exact (memLp_of_mem_schA μ hμ hΦ).aestronglyMeasurable
  have hU := hS.unit μ hμ (g, 1) Φ hΦ
  have hsc := GlobalTheory.T.lintegral_infinite_scaling F (Fin n × Fin d) u hu μ hμ (fun y => ‖Φ y‖ₑ ^ 2)
  simp only [hval Φ hΦ, enorm_mul, mul_pow] at hU
  rw [lintegral_const_mul' _ _ (by simp), hsc] at hU
  set P := ENNReal.ofReal (∏ j, u j ^ Module.finrank ℚ F) with hPdef
  have hPpos : 0 < ∏ j, u j ^ Module.finrank ℚ F := Finset.prod_pos fun j _ => pow_pos (hu j) _
  have hP0 : P ≠ 0 := by rw [hPdef]; exact (ENNReal.ofReal_pos.2 hPpos).ne'
  have hPt : P ≠ ⊤ := ENNReal.ofReal_ne_top
  have hk : ‖c‖ₑ ^ 2 * P⁻¹ = 1 := by
    rw [← mul_assoc] at hU
    exact (ENNReal.mul_eq_right hI0 hIt).1 hU
  have hk' : ‖c‖ₑ ^ 2 = P := by
    have := congrArg (· * P) hk
    simpa [mul_assoc, ENNReal.inv_mul_cancel hP0 hPt] using this
  have hk'' : ENNReal.ofReal (‖c‖ ^ 2) = ENNReal.ofReal (∏ j, u j ^ Module.finrank ℚ F) := by
    rw [← hPdef, ← hk', ← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
  exact (ENNReal.ofReal_eq_ofReal_iff (by positivity) hPpos.le).1 hk''

end GlobalTheory.TorusDilate
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusActionModelCoordinatesStatement
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_action_model_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (g : UA σ X.J) (u : Fin n × Fin d → ℝ), (∀ j, 0 < u j) →
    (∀ z : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), M.co.e (mat g * z) =
      (fun j => GlobalTheory.TorusTheta.infScale F ((u j)⁻¹) * (M.co.e z).1 j,
       fun j => GlobalTheory.TorusTheta.infScale F (u j) * (M.co.e z).2 j)) →
    ∃ κ : ℂ, ‖κ‖ ^ 2 = ∏ j, u j ^ Module.finrank ℚ F ∧
      ∀ Φ ∈ schA F (Fin n × Fin d), ∀ x, om (g, 1) Φ x = κ * Φ (fun j => GlobalTheory.TorusTheta.infScale F (u j) * x j) := by
  first | exact @GlobalTheory.TorusDilate.main | exact GlobalTheory.TorusDilate.main | (intros; apply GlobalTheory.TorusDilate.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeSmallGeneration
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp

theorem coefLat_le_span {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {F : Face D A}
    {κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
    {O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)} (hC : GlobalTheory.Hk3.Core R F) (hFW : Nonempty (FWTie T R κw v₀))
    (hio : IoExt R) (i : Fin D.R.m) (hO : OMPins T R κw v₀ O i) (B : Base (Vc D i) (Wc D i)) (hB : B.Good)
    (hBo : BaseOf R i B) {Oc Oc' : Subring ℂ} (hc : IsCoefRing (embLL0 D) (labLL0 D) Oc)
    (hc' : IsCoefRing (embLL0 D) (labLL0 D) Oc') (h : Bridge.Gf (Vc D i)) {P : PolF D (Wc D i).rank (Vc D i).rank}
    (hP : P ∈ B.coefLat (embLL0 D) (labLL0 D) Oc h) :
    P ∈ Submodule.span Oc (B.coefLat (embLL0 D) (labLL0 D) Oc' h : Set (PolF D (Wc D i).rank (Vc D i).rank)) := by
  obtain ⟨c, hcE, -, -⟩ := GlobalTheory.CoefExtC.exists_extC_bijective_unique D G Pl0 T0 A T R F κw v₀ hC hFW i Unit _ (O i) hO.2
  obtain ⟨u, w₀, hu, -, -⟩ := FWT.IsChosenExtremalVector.io _ hO.2.lift.v0 hio
  obtain ⟨κ, -, -, -, hL⟩ := GlobalTheory.CoefLatConj.coefLat_conj D G Pl0 T0 A T R F κw v₀ O hC hFW hio i hO c hcE u hu B hB hBo
  have e1 := (hL ↥D.LL0 (embLL0 D) (labLL0 D) Oc hc).1 h
  have e2 := (hL ↥D.LL0 (embLL0 D) (labLL0 D) Oc' hc').1 h
  rw [e1] at hP
  refine Submodule.span_mono ?_ hP
  intro Q hQ
  rw [SetLike.mem_coe, e2]
  exact Submodule.subset_span hQ

theorem baseOf_of_realPin_at {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type}
    {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd}
    (hL : Rl.toLevCh.Is A3.A.μ0) {ρ : Setup D.ntw} (hρ : ρ.Good) (hp : RealPin Rl cG ρ) (i : D.ntw.Tw)
    (j : Fin D.R.m) (b : Bool) : BaseOf Rl.toRealDat j (ρ.B i j b) := by
  have hB := hρ.base i j b
  have hlam := GlobalTheory.BaseLiftWeight.lam_eq D _ Rl.toLevCh A3.A.μ0 j (ρ.B i j b) hL hB (hp.mu0 i j b) (hp.ap i j b) (hp.am i j b)
  have hc : ∀ τ, (ρ.B i j b).w.c τ = liftC D j τ := fun τ => GlobalTheory.BaseLiftWeight.c_eq hL hB (hp.mu0 i j b) τ
  have hP : (ρ.B i j b).w.p = GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.pS D j := funext fun τ => congrArg Prod.fst (hB.sig τ)
  have hQ : (ρ.B i j b).w.q = GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.qS D j := funext fun τ => congrArg Prod.snd (hB.sig τ)
  have hAP : (ρ.B i j b).w.ap = GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.aP D j := funext fun τ => hp.ap i j b τ
  have hAM : (ρ.B i j b).w.am = GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.aM D j := funext fun τ => hp.am i j b τ
  refine
    { ψ := hp.psi i j b, θ := hp.inf i j b, sT := hp.cartT i j b, BS := hp.onbS i j b, BT := hp.onbT i j b,
      ΛS := hp.latS i j b, ΛT := hp.latT i j b, βS := hp.frS i j b, βT := hp.frT i j b, vac := hp.vac i j b,
      Pg := hp.Pg i j b, mu0 := hp.mu0 i j b, eta := hp.eta i j b, lam := hlam, delta := ?_, p := hP, q := hQ,
      c := funext hc }
  rw [← liftWeight_delta, Weight.delta, Weight.delta, hP, hQ, hAP, hAM]
  rfl

theorem smallInt_isCoefRing (D : D7) : IsCoefRing (embLL0 D) (labLL0 D) (smallInt D) :=
  ⟨embLL0_labLL0, fun a => ⟨a, rfl⟩⟩

end GlobalTheory.BigOn.Exp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsShortPeriodLatticeBasisBalancedSlope
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsShortPeriodLatticeBasisBalancedSlope
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShortPhi

theorem exists_shortBasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (φ : ℝ), HasPhi y φ → ∀ (C : IntegralChartA3 Xo c T io y) (P : PELUnif (maximalIdeal T.V) C.I.G) (ϖ : T.V), Irreducible ϖ → ∀ Q : P.D.toPre.X → ℤ, IsQ P.D.toPre ϖ Q → ∃ r : ℕ, r ≤ Module.finrank ℚ E * Dw.q ∧ ShortBasis Q r ((|(discr E : ℝ)| ^ ((2 : ℝ) / Module.finrank ℚ E)) / (2 * Module.finrank ℚ E) * (r : ℝ) ^ 3 * φ) (2 * Real.sqrt r) := by
  intro E _ _ _ H Dw l Xo c T io y φ hφ C P ϖ hϖ Q hQ
  let := H.starRing
  let := io.toAlgebra
  obtain ⟨Q', β, hQ', h0, hβ, hβ2, -⟩ :=
    GlobalTheory.ValForm.main E H T.V C.I.G P ϖ hϖ (IsCMField.complexConj E : E → E) fun _ => rfl
  obtain rfl : Q = Q' := funext fun χ => QForm.QVal_unique hϖ P.D (hQ χ) (hQ' χ)
  have hφ' : HasPhi y (Formalism.MainNotions.ModuliIntegralCharts.phiC _ β) := ⟨C.I.G, C.I.t', C.I.m1, C.I.m2, P, ϖ, Q, β, hϖ, hQ, h0, hβ2, rfl⟩
  have hnn := hφ.nonneg
  obtain rfl : φ = Formalism.MainNotions.ModuliIntegralCharts.phiC _ β := (hasPhi_exists_ext_and_unique E H Dw l Xo c).2 T io y _ _ hφ hφ'
  obtain ⟨ρ, hρ, -, hq⟩ := GlobalTheory.ToricRank.rank_le_signature E H Dw l Xo T.V C.I.G P C.I.t' C.I.m2 y.1.x C.I.m1
    inferInstance
  have hrt : IsCMField.complexConj E (H.rt : E) = -(H.rt : E) := by
    rw [← H.bar_eq, HostModel.bar_rt]; simp
  have hw : (H.w0 : E) + IsCMField.complexConj E (H.w0 : E) = 1 := by
    have h2 : (2 : E) * (H.w0 : E) = 1 + (H.rt : E) := by
      simpa only [map_mul, map_add (f := _), map_one, map_ofNat] using congrArg (algebraMap (𝓞 E) E) H.two_weight_eq_one_add_root
    have h3 := congrArg (IsCMField.complexConj E) h2
    rw [map_mul, map_add (f := _), map_one, map_ofNat, hrt] at h3
    linear_combination (h2 + h3) / 2
  have hne : ∃ z : E, IsCMField.complexConj E z ≠ z := by
    by_contra! h
    exact IsCMField.complexConj_ne_one E (AlgEquiv.ext h)
  have hpos := QForm.gram_posDef hϖ P.D hQ (Module.finBasis ℤ P.D.toPre.X)
  obtain ⟨b, h1, h2⟩ := gram_form_phi_holds E (IsCMField.complexConj E : E → E)
    (fun ψ z => IsCMField.complexEmbedding_complexConj E ψ z) hne H.w0 hw P.D.toPre.X β
    ⟨_, inferInstance, Module.finBasis ℤ P.D.toPre.X, by simpa only [hβ] using hpos⟩
  refine ⟨Module.finrank ℤ P.D.toPre.X, ?_, by positivity, b, fun j => ?_, fun j z => ?_⟩
  · rw [hρ]
    exact Nat.mul_le_mul (Nat.mul_div_le _ _) hq
  · have := h1 j
    rwa [hβ2, mul_div_cancel_left₀ _ two_ne_zero] at this
  · have := h2 j z
    rwa [hβ2, mul_div_cancel_left₀ _ two_ne_zero, hβ] at this

end GlobalTheory.ShortPhi
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsShortPeriodLatticeBasisBalancedSlopeStatement
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_short_periodLattice_basis_balanced_slope : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (φ : ℝ), HasPhi y φ → ∀ (C : IntegralChartA3 Xo c T io y) (P : PELUnif (maximalIdeal T.V) C.I.G) (ϖ : T.V), Irreducible ϖ → ∀ Q : P.D.toPre.X → ℤ, IsQ P.D.toPre ϖ Q → ∃ r : ℕ, r ≤ Module.finrank ℚ E * Dw.q ∧ ShortBasis Q r ((|(discr E : ℝ)| ^ ((2 : ℝ) / Module.finrank ℚ E)) / (2 * Module.finrank ℚ E) * (r : ℝ) ^ 3 * φ) (2 * Real.sqrt r) := by
  first | exact @GlobalTheory.ShortPhi.exists_shortBasis | exact GlobalTheory.ShortPhi.exists_shortBasis | (intros; apply GlobalTheory.ShortPhi.exists_shortBasis <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IInfThRuleLeNuLocOf
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory
open Limits MonoidalCategory CartesianMonoidalCategory MonObj Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open GlobalTheory.ThetaLeast

namespace GlobalTheory.RefSum

theorem iInf_thRule_le_nuLocOf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (nab : NabV Xo c), IsNab Xo c nab → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → ∀ (P : PELUnif (maximalIdeal T.V) C.I.G), P.TorsionIso → y.IsAlg → ∀ (ϖ : T.V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q → ∀ (r : ℕ) (Φ M0 : ℝ), ShortBasis Q r Φ M0 → ∀ (α : 𝓞 E), α * star α = ((l.M : ℕ) : 𝓞 E) → l.Mb = Ideal.span {star α} → IsUnit ((l.M : ℕ) : T.V) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n e : ℕ), 1 ≤ n → 0 < e → 4 * DF Dw a + 4 ≤ l.M → (DF Dw a : ℝ) * M0 < l.M → ∀ P₁ ∈ harmA (Dw := Dw) c a n, (⨅ (f : Rul Xo c) (_ : ∃ x : Fin n → Dw.La, IsThRule Xo c nab x P₁ f), nval T.V e (evI y f)) ≤ nuLocOf C e l.M (MvPolynomial.map io P₁) + (((DF Dw a : ℝ) ^ 2 * Φ / l.M / e : ℝ) : EReal) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro nab hnab T io y C hTr P hP hy ϖ hϖ Q hQ r Φ M0 hSB α hα hMb hu a n e hn he h4 hM0 P₁ hP₁
  obtain ⟨hΦ, b, hb, hb'⟩ := hSB
  have hth : ThValTot Xo c nab :=
    GlobalTheory.thValTot_of_chartIndep GlobalTheory.firstFiveLaws.1 GlobalTheory.chartIndependence_unconditional E H Dw l Xo c nab hnab
  letI := io.toAlgebra
  obtain ⟨F, _, _, _, _, _, _, v, hv, hvx⟩ : ∃ (F : Type) (_ : Field F) (_ : IsAlgClosed F) (_ : CharZero F)
      (_ : Algebra T.Fr F) (_ : Algebra T.V F) (_ : IsScalarTower T.V T.Fr F) (v : AddValuation F (WithTop ℚ)),
      ValOver ϖ F v ∧ ∀ x : T.Fr, x ≠ 0 → v (algebraMap T.Fr F x) = (((vV T.V x : ℤ) : ℚ) : WithTop ℚ) := by
    obtain ⟨v, hv⟩ := GlobalTheory.ValClosure.exists_valuation_closure T.V ϖ hϖ
    exact ⟨AlgebraicClosure T.Fr, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, v, hv⟩
  obtain ⟨TI⟩ := GlobalTheory.T.nonempty_tateIsometry_integralFramedPoint_chart E H Dw l Xo c T io y C P F
  obtain ⟨D', A', G', _, _, pD, pA, pG, U', PU, _, oD', hx, hact, hθ⟩ :=
    (GlobalTheory.T.exists_productData_copies_trivialisation_valuation E H Dw l Xo c T io y C P ϖ hϖ).2 n
  obtain ⟨θ, θα, hθ1, hθ2, hθ3⟩ := hθ F v hv Q hQ α l.M (by have := l.three_le; omega) hα
  have hcop : ∃ u u' : 𝓞 E, u * α + u' * star α = 1 := by
    have h1 := l.coprime
    rw [hMb, Ideal.map_span, Set.image_singleton] at h1
    have h2 : (H.bar : 𝓞 E →+* 𝓞 E) (star α) = α := star_star α
    rw [h2, sup_comm, ← Ideal.span_insert, Ideal.eq_top_iff_one, Ideal.mem_span_pair] at h1
    exact h1
  have hdeg1 : P₁.totalDegree ≤ DF Dw a := by
    have key : ∀ m ∈ P₁.support, (m.sum fun _ e => e) = DF Dw a := by
      intro m hm
      rw [Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sigma, DF]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun i _ => hP₁.1.2.2 m hm τ i
    exact Finset.sup_le fun m' hm' => (key m' hm').le
  unfold nuLocOf
  refine le_iInf_add_coe fun f => le_iInf_add_coe fun hf => ?_
  set Pp : MvPolynomial (LtN Dw n) T.Fr := MvPolynomial.map io P₁ with hPp
  set x0 := nabValN C.ch.B T.Fr C.ch.h H.w0 l.M f (fun ℓ : LtN Dw n => ℓ.2.2)
    (fun ℓ : LtN Dw n => C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) Pp with hx0def
  by_cases hx0 : x0 = 0
  · rw [hx0, nval_zero, EReal.top_add_coe]; exact le_top
  have hmap : (∑ _i : Fin 1, algebraMap T.Fr F (algebraMap T.V T.Fr 1) •
      MvPolynomial.map ((algebraMap T.Fr F).comp io) P₁) = MvPolynomial.map (algebraMap T.Fr F) Pp := by
    rw [Fin.sum_univ_one, map_one, map_one, one_smul, hPp, MvPolynomial.map_map]
  have hdeg : (MvPolynomial.map (algebraMap T.Fr F) Pp).totalDegree ≤ DF Dw a :=
    (Finset.sup_mono (MvPolynomial.support_map_subset _ _)).trans
      ((Finset.sup_mono (MvPolynomial.support_map_subset _ _)).trans hdeg1)
  have hval := nabValN_algebraMap T.Fr F _ _ C.ch.B C.ch.h (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.cc_h C.ch.gauge) H.w0 l.M n f
    (LtN Dw n) (fun ℓ : LtN Dw n => ℓ.2.2) (fun ℓ : LtN Dw n => C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) Pp
  have hpoint : RPointT := by
    obtain ⟨h1, h2, h3, h4, h5⟩ := GlobalTheory.firstFiveLaws
    exact GlobalTheory.SmallTranslate.main h1 h2 h3 h4 h5 GlobalTheory.twistBaseChange_and_valuation_statements.1
  obtain ⟨i, p, w, ζ, x, t₀, t, σ', h, ρ, h1, h2, h3, h4', h5, h6, h7, h8, h9, hρ, hle⟩ :=
    hpoint E H Dw l Xo c T io y C hTr P hP hy ϖ hϖ Q hQ F v hv TI Φ M0 r b hΦ hb hb' n D' A' G' pD pA pG U' PU
      oD' hx hact hn α l.M (DF Dw a) hα hcop hu h4 hM0 θ θα hθ1 hθ2 hθ3 (Fin 1)
      (fun _ => MvPolynomial.map ((algebraMap T.Fr F).comp io) P₁)
      (fun _ => algebraMap T.Fr F (algebraMap T.V T.Fr 1)) (fun _ => val_algebraMap_nonneg T v hvx _)
      (by rw [hmap]; exact hdeg) f hf ((vV T.V x0 : ℤ) : ℚ)
      (by rw [hmap, Nat.one_mul, hval]; exact hvx x0 hx0)
  obtain ⟨xx, u, hu0, hrel⟩ := GlobalTheory.PtTie.harmonicValue_translate E H Dw l Xo c nab hnab T io y C hTr P hP hy ϖ hϖ Q hQ
    F v hv n D' A' G' pD pA pG U' PU oD' hx hact α l.M rfl hα hMb θ θα hθ2 hθ3 p w ζ x t₀ t (1 * l.M) rfl σ' h
    h1 h2 h3 h4' h6 h7 h8 h9 h5
  obtain ⟨g, hg, -⟩ := existsUnique_thRule Xo c nab hth xx hP₁
  have hgv := hrel a P₁ hP₁ g hg
  rw [hgv, map_mul (algebraMap T.Fr F), ← _root_.mul_assoc] at hρ
  have hint : ∀ τ : E →+* ℂ, ∃ z : T.V, algebraMap T.V T.Fr z = io (embK c τ α) := fun τ => by
    obtain ⟨φ, hφ⟩ := exists_lift_integers E T.V T.Fr (io.comp (embF c τ))
    exact ⟨φ α, hφ α⟩
  choose z hz using hint
  have hε' : 0 ≤ v (u * algebraMap T.Fr F (io (nrm Dw c a α))) := by
    rw [AddValuation.map_mul, hu0, zero_add]
    have := val_algebraMap_nonneg T v hvx (∏ τ : E →+* ℂ, z τ ^ (∑ i : Fin (Dw.mult τ), a (τ, i)))
    simpa only [nrm, map_prod, map_pow, hz] using this
  exact (iInf₂_le g ⟨xx, hg⟩).trans (nval_le_of_val T v hvx hx0 hε' hρ hle e)

end GlobalTheory.RefSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdeleEmbeddingExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdeleEmbeddingExtension
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.EvExtend

variable {F : Type} [Field F] [NumberField F] {l : ℕ} [Fact l.Prime]

theorem norm_natCast_lt_one : ‖((l : ℕ) : PadicAlgCl l)‖ < 1 := by
  have h := PadicComplex.norm_extends l ((l : ℕ) : PadicAlgCl l)
  rw [← h]
  simpa using ReciprocityTheory.ChartRestriction.B3.IotaPl.norm_p_lt_one (p := l)

omit [NumberField F] in
theorem norm_int_le_one (φ : F →+* PadicAlgCl l) (y : 𝓞 F) : ‖φ (y : F)‖ ≤ 1 := by
  have hi : IsIntegral ℤ (φ (y : F)) := (RingOfIntegers.isIntegral_coe y).map φ.toIntAlgHom
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := PadicAlgCl l))).isIntegral_iff_v_le_one.mp
    hi.tower_top
  exact_mod_cast (show ‖φ (y : F)‖₊ ≤ 1 from h2)

def placeOf (φ : F →+* PadicAlgCl l) : HeightOneSpectrum (𝓞 F) where
  asIdeal := ReciprocityTheory.ChartRestriction.B3.IotaPl.smallIdeal ((algebraMap (PadicAlgCl l) ℂ_[l]).comp φ)
  isPrime := ReciprocityTheory.ChartRestriction.B3.IotaPl.smallIdeal_isPrime _
  ne_bot := by
    intro h
    have hm : ((l : ℕ) : 𝓞 F) ∈ ReciprocityTheory.ChartRestriction.B3.IotaPl.smallIdeal ((algebraMap (PadicAlgCl l) ℂ_[l]).comp φ) := by
      rw [ReciprocityTheory.ChartRestriction.B3.IotaPl.mem_smallIdeal]
      simpa using ReciprocityTheory.ChartRestriction.B3.IotaPl.norm_p_lt_one (p := l)
    rw [h, Submodule.mem_bot] at hm
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) hm

theorem mem_placeOf (φ : F →+* PadicAlgCl l) (x : 𝓞 F) : x ∈ (placeOf φ).asIdeal ↔ ‖φ (x : F)‖ < 1 := by
  show ‖(algebraMap (PadicAlgCl l) ℂ_[l]) (φ (x : F))‖ < 1 ↔ _
  rw [show ‖(algebraMap (PadicAlgCl l) ℂ_[l]) (φ (x : F))‖ = ‖φ (x : F)‖ from PadicComplex.norm_extends _ _]

theorem norm_le_one_iff (φ : F →+* PadicAlgCl l) (x : F) : ‖φ x‖ ≤ 1 ↔ (placeOf φ).valuation F x ≤ 1 :=
  Formalism.BasicNotions.Examples₂.norm_le_one_iff_val φ (placeOf φ) (norm_int_le_one φ) (mem_placeOf φ) x

theorem val_lt_one_iff (φ : F →+* PadicAlgCl l) (x : F) : (placeOf φ).valuation F x < 1 ↔ ‖φ x‖ < 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have h := norm_le_one_iff φ x⁻¹
  have hpos : 0 < ‖φ x‖ := norm_pos_iff.2 ((map_ne_zero φ).2 hx)
  have hv : 0 < (placeOf φ).valuation F x := by
    rw [pos_iff_ne_zero]; exact (Valuation.ne_zero_iff _).2 hx
  rw [map_inv₀, norm_inv, inv_le_one₀ hpos, map_inv₀, inv_le_one₀ hv] at h
  rw [← not_le, ← not_le, h]

end GlobalTheory.EvExtend

namespace GlobalTheory.EvExtend

variable {F : Type} [Field F] [NumberField F] {l : ℕ} [Fact l.Prime]

theorem exists_ext (φ : F →+* PadicAlgCl l) :
    ∃ j : (placeOf φ).adicCompletion F →+* PadicAlgCl l, Continuous j ∧
      (∀ x : F, j (algebraMap F _ x) = φ x) ∧
      (∀ y ∈ (placeOf φ).adicCompletionIntegers F, ‖j y‖ ≤ 1) ∧
      ∀ (K : IntermediateField ℚ_[l] (PadicAlgCl l)), FiniteDimensional ℚ_[l] K → (∀ x, φ x ∈ K) → ∀ y, j y ∈ K := by
  obtain ⟨j, hjc, hj⟩ := GlobalTheory.exists_continuous_extension_adicCompletion F l φ (placeOf φ) (val_lt_one_iff φ)
  have hj' : ∀ x : F, j (algebraMap F _ x) = φ x := fun x => RingHom.congr_fun hj x
  have hd := HeightOneSpectrum.denseRange_algebraMap F (placeOf φ)
  refine ⟨j, hjc, hj', fun y hy => ?_, fun K hK hφK y => ?_⟩
  · have hO : IsOpen (((placeOf φ).adicCompletionIntegers F : Set ((placeOf φ).adicCompletion F))) :=
      Valued.isOpen_valuationSubring _
    have hcl : IsClosed {y : (placeOf φ).adicCompletion F | ‖j y‖ ≤ 1} :=
      isClosed_le (continuous_norm.comp hjc) continuous_const
    refine closure_minimal ?_ hcl (hd.open_subset_closure_inter hO hy)
    rintro _ ⟨hy1, x, rfl⟩
    show ‖j (algebraMap F _ x)‖ ≤ 1
    rw [hj', norm_le_one_iff]
    rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers, ReciprocityTheory.Aut.adic_valued_algebraMap] at hy1
    exact hy1
  · have : CompleteSpace K := FiniteDimensional.completeSpace ℚ_[l] K
    have hKc : IsClosed (K : Set (PadicAlgCl l)) := (completeSpace_coe_iff_isComplete.mp ‹_›).isClosed
    exact hd.induction_on (p := fun y => j y ∈ K) y (hKc.preimage hjc) fun x => by
      show j (algebraMap F _ x) ∈ K
      rw [hj']; exact hφK x

end GlobalTheory.EvExtend

namespace GlobalTheory.EvExtend

theorem exists_evOk : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (l : ℕ) [Fact l.Prime]
    (i : E →+* PadicAlgCl l), ∃ ev : FiniteAdeleRing (𝓞 F) F ⊗[F] E →+* PadicAlgCl l, GlobalTheory.FrameOf.EvOk i ev := by
  intro F E _ _ _ _ _ l _ i
  let φ : F →+* PadicAlgCl l := i.comp (algebraMap F E)
  obtain ⟨j, -, hj, hint, hK⟩ := exists_ext φ
  let v := placeOf φ
  let e0 : FiniteAdeleRing (𝓞 F) F →+* v.adicCompletion F :=
    { toFun := fun a => a v, map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl,
      map_add' := fun _ _ => rfl }
  let : Algebra F (PadicAlgCl l) := φ.toAlgebra
  let f : FiniteAdeleRing (𝓞 F) F →ₐ[F] PadicAlgCl l :=
    { j.comp e0 with commutes' := fun x => hj x }
  let g : E →ₐ[F] PadicAlgCl l := { i with commutes' := fun x => rfl }
  let ev : FiniteAdeleRing (𝓞 F) F ⊗[F] E →+* PadicAlgCl l :=
    (Algebra.TensorProduct.lift f g fun _ _ => Commute.all _ _).toRingHom
  have hev : ∀ a e, ev (a ⊗ₜ[F] e) = j (a v) * i e := fun a e => Algebra.TensorProduct.lift_tmul _ _ _ _ _
  refine ⟨ev, fun x => ?_, fun a ha => ?_, fun a ha => ?_, fun y => ?_⟩
  · rw [hev]
    show j 1 * i x = i x
    rw [map_one, one_mul]
  · rw [hev, map_one, mul_one]
    exact hint _ (ha v)
  · have hl : ((l : ℕ) : 𝓞 F) ∈ v.asIdeal := by
      rw [mem_placeOf]
      simpa [φ] using norm_natCast_lt_one (l := l)
    rw [hev, ha v hl, map_zero, zero_mul]
  · have hKle : Formalism.BasicNotions.Examples₂.LB.Kphi i ≤ IntermediateField.adjoin ℚ_[l] (Set.range i) :=
      IntermediateField.adjoin.mono _ _ _ (by rintro _ ⟨k, rfl⟩; exact ⟨_, rfl⟩)
    have hmem : ∀ a e, ev (a ⊗ₜ[F] e) ∈ Formalism.BasicNotions.Examples₂.LB.Kphi i := fun a e => by
      rw [hev]
      exact mul_mem (hK _ inferInstance (fun x => Formalism.BasicNotions.Examples₂.LB.phi_mem i _) _) (Formalism.BasicNotions.Examples₂.LB.phi_mem i e)
    refine hKle ?_
    induction y using TensorProduct.inductionOn with
    | tmul a e => exact hmem a e
    | add y z hy hz => rw [map_add]; exact add_mem hy hz

end GlobalTheory.EvExtend
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdeleEmbeddingExtensionStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteAdeleEmbeddingExtension : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (l : ℕ) [Fact l.Prime]
    (i : E →+* PadicAlgCl l), ∃ ev : FiniteAdeleRing (𝓞 F) F ⊗[F] E →+* PadicAlgCl l, EvOk i ev := by
  first | exact @GlobalTheory.EvExtend.exists_evOk | exact GlobalTheory.EvExtend.exists_evOk | (intros; apply GlobalTheory.EvExtend.exists_evOk <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueHomExtensionOfIsOpenImmersion
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SemiAbExtDomain

variable {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]

theorem existsUnique_hom_extension_generic (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]
    (G H : Over (Sp R)) [GrpObj G] [GrpObj H] (hG : IsSemiAbelian G) (hH : IsSemiAbelian H)
    (f : (Over.pullback (spMap (algebraMap R K))).obj G ⟶ (Over.pullback (spMap (algebraMap R K))).obj H)
    [IsMonHom f] :
    ∃! F : G ⟶ H, IsMonHom F ∧ (Over.pullback (spMap (algebraMap R K))).map F = f :=
  GlobalTheory.semiAbelianHomExtension_holds.fractionField R K G H hG hH f

theorem existsUnique_iso_extension_generic (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]
    (G H : Over (Sp R)) [GrpObj G] [GrpObj H] (hG : IsSemiAbelian G) (hH : IsSemiAbelian H)
    (e : (Over.pullback (spMap (algebraMap R K))).obj G ≅ (Over.pullback (spMap (algebraMap R K))).obj H)
    [IsMonHom e.hom] :
    ∃! E : G ≅ H, IsMonHom E.hom ∧ (Over.pullback (spMap (algebraMap R K))).map E.hom = e.hom :=
  GlobalTheory.semiAbelianHomExtension_holds.generic_existsUnique_iso (GlobalTheory.IsNormalScheme.pred _)
    (.fractionField R K) hG hH e

end GlobalTheory.SemiAbExtDomain
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowSubst
set_option autoImplicit false

noncomputable section

open MvPolynomial Formalism.GradedWeylDivisibility

namespace GlobalTheory.GenCoef

variable (O : Type) [CommRing O] (N : ℕ)

def rowSubst (R : Type) [CommRing R] [Algebra O R] (Y : Matrix (Fin N) (Fin N) R) :
    MvPolynomial (Fin N × Fin N) O →ₐ[O] MvPolynomial (Fin N × Fin N) R :=
  aeval fun v => ∑ b : Fin N, C (Y v.1 b) * X (b, v.2)

def dwAlg (ν : Fin N → ℕ) : Subalgebra O (Module.End O (dualWeyl O N N ν)) :=
  Algebra.adjoin O (Set.range (fun g : GL (Fin N) O => Formalism.UG.dualWeylRep O N N ν g) ∪ Set.range (GlobalTheory.ExpFrame.rowProj O N ν))

def Expr (ν : Fin N → ℕ) (R : Type) [CommRing R] [Algebra O R] (Y : Matrix (Fin N) (Fin N) R) : Prop :=
  ∃ (n : ℕ) (r : Fin n → R) (p : Fin n → Module.End O (dualWeyl O N N ν)), (∀ i, p i ∈ dwAlg O N ν) ∧
    ∀ f : dualWeyl O N N ν, rowSubst O N R Y (f : MvPolynomial (Fin N × Fin N) O) =
      ∑ i, r i • MvPolynomial.map (algebraMap O R) (p i f : MvPolynomial (Fin N × Fin N) O)

def lowGen : Matrix (Fin N) (Fin N) (MvPolynomial (Fin N × Fin N) O) :=
  fun a b => if a = b then 1 else if b < a then X (a, b) else 0

def diagGen : Matrix (Fin N) (Fin N) (MvPolynomial (Fin N × Fin N) O) :=
  Matrix.diagonal fun a => X (a, a)

def upGen : Matrix (Fin N) (Fin N) (MvPolynomial (Fin N × Fin N) O) :=
  fun a b => if a = b then 1 else if a < b then X (a, b) else 0

def lduHom : MvPolynomial (Fin N × Fin N) O →ₐ[O] MvPolynomial (Fin N × Fin N) O :=
  aeval fun v => (lowGen O N * diagGen O N * upGen O N) v.1 v.2

end GlobalTheory.GenCoef

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceOfAt
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT Formalism.IndefR.Datum GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.OnCmp
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist GlobalTheory.FlatVecSum
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp.SerBase

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (w : D.what₂.places.Pl) (j : Fin D.R.m)

abbrev delW : Formalism.L2.Host.HChar D.host.E := (R2 p).C.delAt (Formalism.EigenvalueLevelCeiling.plc (D.plEq w))

abbrev plW : Finset (Pl D.host.E) := GlobalTheory.OnTies.placesOver (R2 p) ((R2 p).mu (D.plEq w)) (ownAt D (D.plEq w))

abbrev IsEv (u : ∀ τ, lowT ((R2 p).MW j (sg0 D p.P.A3.A)) τ) : Prop :=
  ∀ τ, (u τ : ((R2 p).MW j (sg0 D p.P.A3.A)).sm τ) = p.v₀ j (sg0 D p.P.A3.A) τ

def KerOf : Prop := ∀ ρ : Setup D.ntw, ρ.Good → RealPin p.R p.cG ρ →
  BaseOf (R2 p) j (ρ.B (ex.nch.twI w) j (ex.nch.sd w)) ∧ (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).de.Q = plW p w ∧
    ∃ ξR φ, KerDat (R2 p) j (delW p w) (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).de.chi ξR (plW p w)
      (ρ.om (ex.nch.twI w) j (ex.nch.sd w) 1) φ

def TraceOf : Prop := ∀ ρ : Setup D.ntw, ρ.Good → RealPin p.R p.cG ρ → ρ.LevelOf D.nexp → ∀ h P,
  ρ.theta (ex.nch.twI w) j (ex.nch.sd w) h P = levelTrace (R2 p) j (F2 p).P0 (F2 p).ψ0⁻¹
    (series (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).F (ρ.om (ex.nch.twI w) j (ex.nch.sd w) 1)
      (princ (ρ.B (ex.nch.twI w) j (ex.nch.sd w))).vecBase h P)

def KerRat : Prop := ∀ χ ξR ω φ, KerDat (R2 p) j (delW p w) χ ξR (plW p w) ω φ → ∀ h ∈ GfC (Vc D j), ∀ y, InCoefLat (R2 p) j h y →
  ∀ u, IsEv p j u → ∃ x, adForm (R2 p) j x (fun τ => u τ) = singleSeries (R2 p) j ω φ h y u

def LatIo : Prop := ∀ ρ : Setup D.ntw, ρ.Good → RealPin p.R p.cG ρ → ∀ c : ℂ, c ≠ 0 →
  IsScale p.R p.v₀ (ρ.B (ex.nch.twI w) j (ex.nch.sd w)) c → ∃ u, IsEv p j u ∧ ∀ h ∈ GfC (Vc D j),
    ∀ P ∈ ρ.lat (ex.nch.twI w) j (ex.nch.sd w) (smallInt D) h,
      ∃ y, InCoefLat (R2 p) j h y ∧ (R2 p).ioP j (PiTensorProduct.tprod ℂ u) y = c • P

def ReadCmp : Prop := ∀ (ρ : Setup D.ntw) (hρ : ρ.Good) (e : FractionRing (ex.nch.Oe w) →+* ℂ),
  (∀ x, e (ex.nch.embW w x) = D.what₂.embLL x) →
  (∀ a : D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w),
    e (algebraMap (ex.nch.Oe w) _ (algebraMap _ (ex.nch.Oe w) a)) = ρ.eOk (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) a) →
  ∀ ν : ℂ, ν ≠ 0 → ∀ rd : Can p w j, IsCan p rd → ∀ u, IsEv p j u → ∀ f x (a : ℂ),
    rdAt p w j hρ ν f = a • ν⁻¹ • adForm (R2 p) j x (fun τ => u τ) →
      f = 0 ∨ ∃ b, e b = a ∧ ((1 : FractionRing (ex.nch.Oe w)) ⊗ₜ[D.ntw.O (ex.nch.twI w)] f : Tgt ex w j) = b • rd x

end Point

def FlatKer : Prop := ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
  (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R →
  ∀ i : Fin D.R.m, VStd D i → ∀ B : Base (Vc D i) (Wc D i), B.Good → BaseOf R i B →
  ∀ ξ ξR ω φ, KerDat R i ξ B.de.chi ξR B.de.Q ω φ → (∃ t, B.de.Q ⊆ R.Q t) → ∀ N : ℕ, N ≠ 0 →
    (∀ PP ∈ B.de.Q, (N : 𝓞 D.host.E) ∈ PP.asIdeal) →
    ∃ (z : GA D (Vc D i)) (c : ℂ), IsCentAt i B.de.Q z ∧ UnitOff N c ∧
      ∀ h P, series B.F ω (princ B).vecBase h P = c • series B.F ω φ (h * z) P

def CentLat : Prop := ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
  (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (Q : Finset (Pl D.host.E))
  (z : GA D (Vc D i)), IsCentAt i Q z → ∀ N : ℕ, N ≠ 0 → (∀ PP ∈ Q, (N : 𝓞 D.host.E) ∈ PP.asIdeal) →
    ∃ m : ℕ, ∀ h ∈ GfC (Vc D i), ∀ y, (InCoefLat R i h y → InCoefLat R i (h * z) ((N : ℂ) ^ m • y)) ∧
      (InCoefLat R i (h * z) y → InCoefLat R i h ((N : ℂ) ^ m • y))

def TraceRat : Prop := ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
  (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → R.LUnif →
  ∀ (i : Fin D.R.m) (v₀ : (R.MW i (sg0 D A)).Vec), IsExtVec (R.MW i (sg0 D A)) v₀ →
  ∀ ξ χ ξR Q ω φ, KerDat R i ξ χ ξR Q ω φ → ∀ (U : Subgroup G) (ψ : U →* D.what₂.LLˣ) h y
    (u : ∀ τ, lowT (R.MW i (sg0 D A)) τ), (∀ τ, (u τ : (R.MW i (sg0 D A)).sm τ) = v₀ τ) →
    ∀ x, adForm R i x (fun τ => u τ) = singleSeries R i ω φ h y u →
      ∃ x', ∀ v : ∀ τ, lowT (R.MW i (sg0 D A)) τ, adForm R i x' (fun τ => v τ) = levelTrace R i U ψ (singleSeries R i ω φ h y v)

def OwnUnit : Prop := ∀ (D : D7) (c : NChoice D) (w : D.what₂.places.Pl), IsUnit ((ownAt D (D.plEq w) : ℕ) : c.Oe w)

end GlobalTheory.BigOn.Exp.SerBase
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompositumIntermediateFieldExistsPlaceValuationEStatement
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compositum_intermediateField_exists_place_valuation_eq : ∀ (F F' K : IntermediateField ℚ ℂ) [NumberField F] [NumberField F'] [NumberField K] (hF : F ≤ K), K = F ⊔ F' → ∀ q : ℕ, q.Prime → ¬ (q : ℤ) ∣ discr F' → ∀ w : HeightOneSpectrum (𝓞 F), ((q : ℕ) : 𝓞 F) ∈ w.asIdeal → ∃ 𝔭 : HeightOneSpectrum (𝓞 K), ∀ a : F, vLa 𝔭 (IntermediateField.inclusion hF a) = vLa w a := by
  first | exact @GlobalTheory.UnramCompositum.exists_vLa_eq | exact GlobalTheory.UnramCompositum.exists_vLa_eq | (intros; apply GlobalTheory.UnramCompositum.exists_vLa_eq <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCompSymm
noncomputable section

open MeasureTheory
open scoped Matrix Pointwise NNReal

namespace GlobalTheory.ChangeVarPi

theorem map_symm_eq_smul (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ι : Type) [Fintype ι]
    (μ : Measure (ι → k)) [μ.IsAddHaarMeasure] (M : (ι → k) ≃ₗ[k] (ι → k)) :
    μ.map M.symm = (distribHaarChar k (LinearEquiv.det M)) • μ := by
  classical
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hc : Continuous M.symm := (M.symm : (ι → k) →ₗ[k] (ι → k)).continuous_on_pi
  ext s hs
  rw [Measure.map_apply hc.measurable hs, Measure.smul_apply, ← GroundTheory.Automorphic.Measures.distribHaarChar_pi_eq,
    ENNReal.smul_def, smul_eq_mul, distribHaarChar_mul μ M s]
  have : (M.symm : (ι → k) → (ι → k)) ⁻¹' s = M • s := by
    ext x
    simp only [Set.mem_preimage]
    constructor
    · intro h
      exact ⟨M.symm x, h, by simp [LinearEquiv.smul_def]⟩
    · rintro ⟨y, hy, rfl⟩
      simpa [LinearEquiv.smul_def] using hy
  rw [this]

end GlobalTheory.ChangeVarPi
end
end
