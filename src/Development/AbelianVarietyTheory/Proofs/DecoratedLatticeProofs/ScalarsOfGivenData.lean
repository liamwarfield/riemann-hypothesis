module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedThetaChainStepAdjointScalar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnfoldingSchurOrthogonalityDefiniteCoefficients
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealDatumNormShrinkOfScalarHypotheses
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowsOfPartHavePartParamsFirstChainMember
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedChainStepConstantsTupleIndep
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealQuotientVolumeGrowthOfScalarHypotheses
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalFlatMapFactorIntertwinesTranslations
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainLevelIntegralRealZetaOfTwistedTransformLaws
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompactAverageThetaFamilySmooth
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainFirstStageLValuesPositive
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainTwistPlacesIntegralPeelOfDoubling
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowerBlockParameterOfOneNonzeroValue
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainTwistEulerFactorsRestoreProof
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatHalfTensorSplitPlaceSelfDual

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealTupleTwistedChainOfScalarHypotheses
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealTupleTwistedChainOfScalarHypotheses
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)

theorem GlobalTheory.ChainTw.rChain_of_given : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → ∀ h : RangeX R, RChain R h := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG h
  exact GlobalTheory.ChainTw.RModel.rChain R hG.core.lev hG.core.models hG.core.chain h
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealTupleTwistedChainOfScalarHypothesesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realTupleTwistedChain_of_scalarHypotheses : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → ∀ h : RangeX R, RChain R h := by
  first | exact @GlobalTheory.ChainTw.rChain_of_given | exact GlobalTheory.ChainTw.rChain_of_given | (intros; apply GlobalTheory.ChainTw.rChain_of_given <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealFormsRangeMultiplicityOfScalarHypotheses
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealFormsRangeMultiplicityOfScalarHypotheses
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)

namespace GlobalTheory.ChainTw

theorem rangeX_of_given : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → RangeX R := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG t
  have hm := hG.core.models
  exact GlobalTheory.DefiniteMult.range_top R hm.inf hm.cX hm.prX hm.HX t

end GlobalTheory.ChainTw
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealFormsRangeMultiplicityOfScalarHypothesesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realFormsRangeMultiplicity_of_scalarHypotheses : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → RangeX R := by
  first | exact @GlobalTheory.ChainTw.rangeX_of_given | exact GlobalTheory.ChainTw.rangeX_of_given | (intros; apply GlobalTheory.ChainTw.rangeX_of_given <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealLastStageNormalizedOfScalarHypotheses
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealLastStageNormalizedOfScalarHypotheses
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)

noncomputable section

namespace GlobalTheory.ChainTwNorm

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

theorem orZero_of {X : Type} [Zero X] {p : X → Prop} {x : X} (hx : p x) : OrZero p x :=
  ⟨fun _ => hx, fun hn => absurd ⟨x, hx⟩ hn⟩

theorem baseW_of_given (hG : Given R F) : R.BaseW F := by
  obtain ⟨lev, grp, fam, models, chain, thP⟩ := hG.core
  exact ⟨lev, grp, fam, models,
    ⟨chain.ωY, chain.ωX, chain.vY, chain.vX, chain.ptY, chain.ptX, fun k hk => orZero_of fun t => chain.ItY t k hk,
      orZero_of chain.ItX, fun t k hk => orZero_of (chain.ioY t k (by omega)), fun t => orZero_of (chain.ioX t),
      fun t => orZero_of (chain.Th t)⟩,
    ⟨thP.ωP, thP.vP, thP.pt_theta, fun i => orZero_of (thP.ioP i), fun i t => orZero_of ⟨thP.thF_mem i t, thP.thF i t⟩,
      fun i t => orZero_of (thP.thG i t)⟩⟩

theorem alg_step {d I aa xy ipv P P' na : ℂ} (hna : na ≠ 0) (e1 : aa = na ^ 2) (e2 : P = P') (h1 : d * I = aa * xy)
    (h2 : I = ipv * P) : xy = d * P' / na ^ 2 * ipv := by
  subst e1 e2 h2
  field_simp
  linear_combination -h1

theorem riesz {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (ℓ : W →ₗ[ℂ] ℂ) : ∃ a : W, ∀ w, ℓ w = ⟪a, w⟫_ℂ :=
  ⟨(InnerProductSpace.toDual ℂ W).symm (LinearMap.toContinuousLinearMap ℓ), fun w => by
    rw [InnerProductSpace.toDual_symm_apply]; rfl⟩

theorem normX : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → ∀ h : RangeX R, NormX R h := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG h
  have hB := baseW_of_given R F hG
  have hm := hG.core.models
  obtain ⟨w0, v0, hw0⟩ : ∃ (w : R.cX.W) (v : R.MX.Vec), R.prX w (PiTensorProduct.tprod ℂ v) ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply hm.prX.1
    refine LinearMap.ext fun w => LinearMap.ext fun x => ?_
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r v => simp [hc w v]
    | add x y hx hy => simp [map_add (f := _), hx, hy]
  obtain ⟨a, ha⟩ := riesz (R.prX.flip (PiTensorProduct.tprod ℂ v0))
  have ha' : ∀ w, R.prX w (PiTensorProduct.tprod ℂ v0) = ⟪a, w⟫_ℂ := fun w => ha w
  have hna : a ≠ 0 := by
    rintro rfl
    exact hw0 (by rw [ha']; simp)
  have hv : ∀ τ, (v0 τ : R.MX.H τ) ≠ 0 := by
    intro τ h0
    apply hw0
    have : v0 τ = 0 := Subtype.ext h0
    rw [(PiTensorProduct.tprod ℂ).map_coord_zero τ this, map_zero]
  haveI : Nontrivial R.cX.W := hm.cX.2.2.2.1
  have hd : (0 : ℝ) < Module.finrank ℂ R.cX.W := by exact_mod_cast Module.finrank_pos
  have hP : (0 : ℝ) < ∏ τ, ‖(v0 τ : R.MX.H τ)‖ ^ 2 :=
    Finset.prod_pos fun τ _ => pow_pos (norm_pos_iff.2 (hv τ)) 2
  have hA : (0 : ℝ) < ‖a‖ ^ 2 := pow_pos (norm_pos_iff.2 hna) 2
  refine ⟨(Module.finrank ℂ R.cX.W : ℝ) * (∏ τ, ‖(v0 τ : R.MX.H τ)‖ ^ 2) / ‖a‖ ^ 2, by positivity, fun t => ⟨?_, ?_⟩⟩
  · have hi := GlobalTheory.DefiniteMult.top_injective R hm.inf hm.cX hm.prX hm.HX t
    refine ⟨fun x y e => ?_, fun z => ?_⟩
    · have e2 := (LinearEquiv.ofEq _ _ (h t)).injective e
      exact hi (congrArg Subtype.val e2)
    · obtain ⟨u, hu⟩ := (LinearMap.surjective_rangeRestrict _) ((LinearEquiv.ofEq _ _ (h t)).symm z)
      refine ⟨u, ?_⟩
      simp only [toCC, hu]
      exact (LinearEquiv.ofEq _ _ (h t)).apply_symm_apply z
  · intro ipD ip hM x y
    have hS := hM.schur (toCC R h t y) (toCC R h t x) (PiTensorProduct.tprod ℂ v0) (PiTensorProduct.tprod ℂ v0)
    have hS' := hS.trans (congrArg _ (hM.pure v0 v0))
    have hI := (GlobalTheory.T.unfolding_schur_orthogonality_definite_coefficients D G Pl0 T A Ks R F hB t x y a a).2
    have hJ : (∫ g in R.fdX t, star ⟪a, R.cX.ext ((R.HX t).e x) g⟫_ℂ * ⟪a, R.cX.ext ((R.HX t).e y) g⟫_ℂ ∂(R.νX t)) =
        ip (toCC R h t y) (toCC R h t x) * ∏ τ, ⟪(v0 τ : R.MX.H τ), (v0 τ : R.MX.H τ)⟫_ℂ := by
      refine Eq.trans ?_ hS'
      unfold Lift.pet
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
      have e3 : (((toCC R h t y : (stX R t).CC (comR R t)) : SmT (stX R t).M →ₗ[ℂ] (GA D (stX R t).V → ℂ))
          (PiTensorProduct.tprod ℂ v0)) g = R.prX (R.cX.ext ((R.HX t).e y) g) (PiTensorProduct.tprod ℂ v0) := rfl
      have e4 : (((toCC R h t x : (stX R t).CC (comR R t)) : SmT (stX R t).M →ₗ[ℂ] (GA D (stX R t).V → ℂ))
          (PiTensorProduct.tprod ℂ v0)) g = R.prX (R.cX.ext ((R.HX t).e x) g) (PiTensorProduct.tprod ℂ v0) := rfl
      simp only [e3, e4, ha', starRingEnd_apply]
      exact mul_comm _ _
    have e1 : ⟪a, a⟫_ℂ = ((‖a‖ : ℂ)) ^ 2 := inner_self_eq_norm_sq_to_K a
    have e2 : (∏ τ, ⟪(v0 τ : R.MX.H τ), (v0 τ : R.MX.H τ)⟫_ℂ) = ∏ τ, ((‖(v0 τ : R.MX.H τ)‖ : ℂ)) ^ 2 :=
      Finset.prod_congr rfl fun τ _ => inner_self_eq_norm_sq_to_K _
    have hA' : (‖a‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.2 hna).ne'
    have H := alg_step hA' e1 e2 hI hJ
    rw [H]
    push_cast
    ring
end GlobalTheory.ChainTwNorm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealLastStageNormalizedOfScalarHypothesesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realLastStageNormalized_of_scalarHypotheses : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → ∀ h : RangeX R, NormX R h := by
  first | exact @GlobalTheory.ChainTwNorm.normX | exact GlobalTheory.ChainTwNorm.normX | (intros; apply GlobalTheory.ChainTwNorm.normX <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainStepScalarsOfRealisation
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainStepScalarsOfRealisation
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)

noncomputable section

open GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars (EigSys rowPart badPl IsLValue IsIP IsUp topStep IsUpTop reached reached_zero reached_succ StepScalar TopScalar ScalarsWith Scalars)

namespace GlobalTheory.ChainTw

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

namespace StepScal

open GlobalTheory.ChainOnto

theorem sesq_eq_of_tprod {ι : Type} {s : ι → Type} [∀ i, AddCommGroup (s i)] [∀ i, Module ℂ (s i)]
    (f g : (⨂[ℂ] i, s i) →ₗ[ℂ] (⨂[ℂ] i, s i) →ₗ⋆[ℂ] ℂ)
    (h : ∀ v v' : ∀ i, s i, f (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ v') =
      g (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ v')) : f = g := by
  have h1 : ∀ (v : ∀ i, s i) y, f (PiTensorProduct.tprod ℂ v) y = g (PiTensorProduct.tprod ℂ v) y := by
    intro v y
    induction y using PiTensorProduct.induction_on with
    | smul_tprod r v' => rw [LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, h]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have h2 : ∀ x y, f x y = g x y := by
    intro x
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r v => intro y; rw [map_smul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply, h1]
    | add x x' hx hx' => intro y; rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, hx, hx']
  exact LinearMap.ext fun x => LinearMap.ext fun y => h2 x y

theorem adjVec_unique {c : Com D} {s s' : PiLocalization₂ D} {p : Step c s s'}
    {ipD : SmT s.M →ₗ[ℂ] SmT s.M →ₗ⋆[ℂ] ℂ} {ipD' : SmT s'.M →ₗ[ℂ] SmT s'.M →ₗ⋆[ℂ] ℂ}
    {ip' : s'.CC c →ₗ[ℂ] s'.CC c →ₗ⋆[ℂ] ℂ} (hm : IsMet c s' ipD' ip')
    {φ : PolF D s'.V.rank s.V.rank} {v : SmT s.M} {w₀ w₁ : SmT s'.M}
    (h₀ : IsAdjVec p ipD ipD' φ v w₀) (h₁ : IsAdjVec p ipD ipD' φ v w₁) : w₀ = w₁ := by
  by_contra hne
  have hd : w₀ - w₁ ∈ s'.KF := sub_mem h₀.1 h₁.1
  have e : ipD' (w₀ - w₁) (w₀ - w₁) = 0 := by
    rw [map_sub (ipD' (w₀ - w₁)), h₀.2 _ hd, h₁.2 _ hd, sub_self]
  have := hm.posD _ (sub_ne_zero.2 hne)
  rw [e] at this
  simp at this

theorem eq_zero_of_ip {c : Com D} {s : PiLocalization₂ D} {ipD : SmT s.M →ₗ[ℂ] SmT s.M →ₗ⋆[ℂ] ℂ}
    {ip : s.CC c →ₗ[ℂ] s.CC c →ₗ⋆[ℂ] ℂ} (hm : IsMet c s ipD ip) {x : s.CC c} (h : ∀ y, ip y x = 0) : x = 0 := by
  by_contra hx
  have := hm.pos x hx
  rw [h x] at this
  simp at this

theorem isUp_iff (R : RealDat D A Ks) (hIP : IPDict R) {t : T} {k : ℕ} (hk : k + 1 < D.R.m)
    {ipD ip ipD' ip'} (hm : IsMet (comR R t) (stY R t k) ipD ip) (hm' : IsMet (comR R t) (stY R t (k + 1)) ipD' ip')
    (U : (stY R t k).CC (comR R t)) (X : (stY R t (k + 1)).CC (comR R t)) :
    IsUp R t k (PiTensorProduct.lift.symm U.1) (PiTensorProduct.lift.symm X.1) ↔
      ∀ y, ip' y X = ip ((stepY R t k).io y) U := by
  constructor
  · rintro ⟨-, hy⟩ y
    obtain ⟨a, h1, h2⟩ := hy y
    rw [← (hIP t (k + 1) hk ipD' ip' hm' X y a).1 h1, ← (hIP t k (by omega) ipD ip hm U ((stepY R t k).io y) a).1 h2]
  · intro hy
    have hX : PiTensorProduct.lift (PiTensorProduct.lift.symm X.1) ∈ (stY R t (k + 1)).CC (comR R t) := by
      rw [LinearEquiv.apply_symm_apply]; exact X.2
    refine ⟨hX, fun y => ⟨ip' y X, (hIP t (k + 1) hk ipD' ip' hm' X y _).2 rfl, ?_⟩⟩
    exact (hIP t k (by omega) ipD ip hm U ((stepY R t k).io y) _).2 (hy y)

theorem isUpTop_iff (R : RealDat D A Ks) (hIP : IPDict R) (h : RangeX R) (hm2 : 2 ≤ D.R.m) {t : T} {ipD ip}
    (hm : IsMet (comR R t) (stY R t (D.R.m - 1)) ipD ip) (U : (stY R t (D.R.m - 1)).CC (comR R t)) (x : (R.HX t).H) :
    IsUpTop R t (PiTensorProduct.lift.symm U.1) x ↔ ∀ y, ⟪x, y⟫_ℂ = ip ((stepX R h t).io (toCC R h t y)) U :=
  forall_congr' fun y => hIP t (D.R.m - 1) (by omega) ipD ip hm U ((stepX R h t).io (toCC R h t y)) _

end StepScal

namespace StepScal

open GlobalTheory.ChainOnto

def GoodAt (R : RealDat D A Ks) (t : T) (B : GlobalTheory.LFun.Fam D.host.E) (k : ℕ) (u : MMap (R.MY k)) : Prop :=
  ∃ hu : PiTensorProduct.lift u ∈ (stY R t k).CC (comR R t),
    u = 0 ∨ (IsPar (⟨_, hu⟩ : (stY R t k).CC (comR R t)) (chainPar (comR R t) B k) ∧
      IsQ (twR R t) k (⟨_, hu⟩ : (stY R t k).CC (comR R t)))

theorem reached_good (R : RealDat D A Ks) (hN : GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.NodeGap D) (hSoft : SoftQ D) (hQ : QOfVal D)
    (hSL : StepLam D) (h : RangeX R) (hRC : RChain R h) (hRU : RUnif R h) (hRP : RowPar R) (hIP : IPDict R)
    (t : T) (c : EigSys D) (B : GlobalTheory.LFun.Fam D.host.E) (hB : GlobalTheory.LFun.IsSysParamD D (badPl R t) D.R.r c B)
    (hb : GlobalTheory.LFun.Bounded (GlobalTheory.LFun.above D.host.E (badPl R t : Set (HeightOneSpectrum (𝓞 D.host.F)))) B D.R.r
      ((D.R.r : ℝ) / 2)) :
    ∀ k < D.R.m, (∀ u ∈ reached R t c k, GoodAt R t B k u) ∧
      (rowPart R (badPl R t) c ≠ ⊥ → ∃ u ∈ reached R t c k, u ≠ 0) := by
  have hw := (hRC t).1
  intro k
  induction k with
  | zero =>
    intro hm0
    refine ⟨fun u hu => ?_, fun hne => ?_⟩
    · obtain ⟨hu', hpar⟩ := (hRP t c).2 u hu
      refine ⟨hu', ?_⟩
      by_cases h0 : u = 0
      · exact Or.inl h0
      · exact Or.inr ⟨hpar h0 B hB, (hQ _ _ hw 0 (Nat.zero_le _) _ ((hRC t).2.1 0 hm0)).2 rfl _⟩
    · obtain ⟨u, hu, h0⟩ := (Submodule.ne_bot_iff _).1 hne
      exact ⟨u, hu, h0⟩
  | succ k ih =>
    intro hk1
    have hk : k < D.R.m := by omega
    have hs := (hRC t).2.1 k hk
    have hs' := (hRC t).2.1 (k + 1) hk1
    have hp := (hRC t).2.2.2.1 k hk1
    obtain ⟨-, ⟨ipD, ip, hm⟩, -⟩ := hSoft _ _ hw k hk.le _ hs
    obtain ⟨hfin', ⟨ipD', ip', hm'⟩, -⟩ := hSoft _ _ hw (k + 1) hk1.le _ hs'
    obtain ⟨K, φ, v, hK, hU⟩ := hRU.1 k hk1
    obtain ⟨mm, X, mR, H₀, hcov, hlev, hconv, hH, hkap⟩ := hU t
    have hSLt := hSL hN _ _ hw k hk _ _ hs hs' _ hp ipD ip ipD' ip' hm hm' mm X hcov mR hlev φ v hconv H₀ hH
      (by rw [hkap]; exact hK) B hb
    refine ⟨fun x hx => ?_, fun hne => ?_⟩
    · obtain ⟨u, hu, hup⟩ := hx
      obtain ⟨hu', hgood⟩ := (ih hk).1 u hu
      have hx' : PiTensorProduct.lift x ∈ (stY R t (k + 1)).CC (comR R t) := hup.1
      have hup' : IsUp R t k (PiTensorProduct.lift.symm (⟨_, hu'⟩ : (stY R t k).CC (comR R t)).1)
          (PiTensorProduct.lift.symm (⟨_, hx'⟩ : (stY R t (k + 1)).CC (comR R t)).1) := by
        simpa using hup
      have hadj := (isUp_iff R hIP hk1 hm hm' _ _).1 hup'
      refine ⟨hx', ?_⟩
      rcases hgood with h0 | ⟨hpar, hq⟩
      · left
        have hU0 : (⟨_, hu'⟩ : (stY R t k).CC (comR R t)) = 0 := by
          subst h0; exact Subtype.ext (map_zero _)
        have hX0 := eq_zero_of_ip hm' fun y => by rw [hadj y, hU0, map_zero]
        have h1 : PiTensorProduct.lift x = 0 := congrArg Subtype.val hX0
        exact (LinearEquiv.map_eq_zero_iff _).1 h1
      · obtain ⟨w₀, -, -, hx1⟩ := hSLt _ hpar hq
        obtain ⟨hpx, hqx, -⟩ := hx1 _ hadj
        exact Or.inr ⟨hpx, hqx⟩
    · obtain ⟨u, hu, h0⟩ := (ih hk).2 hne
      obtain ⟨hu', hgood⟩ := (ih hk).1 u hu
      rcases hgood with h0' | ⟨hpar, hq⟩
      · exact absurd h0' h0
      obtain ⟨Xa, hXa, -⟩ := GlobalTheory.hermitian_adjoint_exists_unique _ _ ip ip' hm'.herm hm'.pos
        (stepY R t k).io ⟨_, hu'⟩
      obtain ⟨w₀, -, -, hx1⟩ := hSLt _ hpar hq
      obtain ⟨hpx, -, -⟩ := hx1 _ hXa
      refine ⟨PiTensorProduct.lift.symm Xa.1, ⟨u, hu, ?_⟩, ?_⟩
      · have := (isUp_iff R hIP hk1 hm hm' ⟨_, hu'⟩ Xa).2 hXa
        simpa using this
      · intro hz
        apply hpx.1
        apply Subtype.ext
        show Xa.1 = 0
        exact (LinearEquiv.map_eq_zero_iff _).1 hz

end StepScal

namespace StepScal

open GlobalTheory.ChainOnto

theorem conj_step {P Q K d : ℂ} {l : ℝ} (hd : conj d = d) (hd0 : d ≠ 0) (hf : P * d = conj (K * l) * Q) :
    conj P = K / d * l * conj Q := by
  have h2 := congrArg conj hf
  simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal, hd] at h2
  field_simp
  linear_combination h2

theorem pos_ratio {a b d K : ℂ} {l : ℝ} (ha : conj a = a) (ha0 : 0 < a.re) (hb : conj b = b) (hb0 : 0 < b.re)
    (hd : conj d = d) (hd0 : 0 < d.re) (hl : 0 < l) (hf : a * d = conj (K * l) * b) :
    ∃ q : ℝ, 0 < q ∧ (q : ℂ) = K / d := by
  have h2 := congrArg conj hf
  simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal, ha, hd, hb] at h2
  have ha' : (a.re : ℂ) = a := Complex.conj_eq_iff_re.1 ha
  have hb' : (b.re : ℂ) = b := Complex.conj_eq_iff_re.1 hb
  have hd' : (d.re : ℂ) = d := Complex.conj_eq_iff_re.1 hd
  refine ⟨a.re / (l * b.re), by positivity, ?_⟩
  rw [← ha', ← hb', ← hd'] at h2
  rw [← hd']
  have h3 : (d.re : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
  have h4 : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  have h5 : (b.re : ℂ) ≠ 0 := by exact_mod_cast hb0.ne'
  push_cast
  field_simp
  linear_combination h2

end StepScal

namespace StepScal

open GlobalTheory.ChainOnto


set_option maxHeartbeats 1600000 in
theorem mid_scalar (R : RealDat D A Ks) (hN : GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.NodeGap D) (hSoft : SoftQ D) (hQ : QOfVal D)
    (hLP : LPos D) (hLF : LFull D) (hSL : StepLam D) (h : RangeX R) (hRC : RChain R h) (hRU : RUnif R h)
    (hRP : RowPar R) (hIP : IPDict R) (k : ℕ) (hk1 : k + 1 < D.R.m) :
    ∃ r : ℝ, 0 < r ∧ ∀ (t : T) (c : EigSys D), rowPart R (badPl R t) c ≠ ⊥ →
      ∀ B, GlobalTheory.LFun.IsSysParamD D (badPl R t) D.R.r c B →
        ∃ l, IsLValue R t B (k + 1) l ∧ StepScalar R t c k (r * l) := by
  have hk : k < D.R.m := by omega
  obtain ⟨K, φ, v, hK, hU⟩ := hRU.1 k hk1
  have key : ∀ (ipD₀ : SmT (R.MY k) →ₗ[ℂ] SmT (R.MY k) →ₗ⋆[ℂ] ℂ)
      (ipD₀' : SmT (R.MY (k + 1)) →ₗ[ℂ] SmT (R.MY (k + 1)) →ₗ⋆[ℂ] ℂ),
      (∀ v v' : (R.MY k).Vec, ipD₀ (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ v') =
        ∏ τ, ⟪(v' τ : (R.MY k).H τ), (v τ : (R.MY k).H τ)⟫_ℂ) →
      (∀ v v' : (R.MY (k + 1)).Vec, ipD₀' (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ v') =
        ∏ τ, ⟪(v' τ : (R.MY (k + 1)).H τ), (v τ : (R.MY (k + 1)).H τ)⟫_ℂ) →
      ∀ (t : T) (c : EigSys D), rowPart R (badPl R t) c ≠ ⊥ → ∀ B, GlobalTheory.LFun.IsSysParamD D (badPl R t) D.R.r c B →
        (∃ w₀, w₀ ≠ 0 ∧ IsAdjVec (stepY R t k) ipD₀ ipD₀' φ (PiTensorProduct.tprod ℂ v) w₀) ∧
        ∀ w₀, IsAdjVec (stepY R t k) ipD₀ ipD₀' φ (PiTensorProduct.tprod ℂ v) w₀ →
          ∃ l, IsLValue R t B (k + 1) l ∧ (∃ q : ℝ, 0 < q ∧ (q : ℂ) = K / ipD₀' w₀ w₀) ∧
            ∀ z : ℝ, (z : ℂ) = K / ipD₀' w₀ w₀ → StepScalar R t c k (z * l) := by
    intro ipD₀ ipD₀' hp₀ hp₀' t c hc B hB
    have hw := (hRC t).1
    have hs0 := (hRC t).2.1 0 (by omega)
    have hs := (hRC t).2.1 k hk
    have hs' := (hRC t).2.1 (k + 1) hk1
    have hp := (hRC t).2.2.2.1 k hk1
    obtain ⟨-, ⟨ipD, ip, hm⟩, -⟩ := hSoft _ _ hw k hk.le _ hs
    obtain ⟨hfin', ⟨ipD', ip', hm'⟩, -⟩ := hSoft _ _ hw (k + 1) hk1.le _ hs'
    haveI := hfin'
    obtain rfl : ipD = ipD₀ := sesq_eq_of_tprod _ _ fun v v' => (hm.pure v v').trans (hp₀ v v').symm
    obtain rfl : ipD' = ipD₀' := sesq_eq_of_tprod _ _ fun v v' => (hm'.pure v v').trans (hp₀' v v').symm
    obtain ⟨u₀, hu₀, hu₀0⟩ := (Submodule.ne_bot_iff _).1 hc
    obtain ⟨hu₀', hpar₀⟩ := (hRP t c).2 u₀ hu₀
    obtain ⟨hb, hL⟩ := hLP _ _ hw 0 (Nat.zero_le _) _ hs0 rfl _ B (hpar₀ hu₀0 B hB)
    obtain ⟨l, hl0, hleq⟩ := hL k hk
    obtain ⟨H, -, -, hconv, -, -⟩ := hLF _ hw.com B hb k hk
    have hLV : IsLValue R t B (k + 1) l := ⟨hconv, hl0, hleq⟩
    have hgood := reached_good R hN hSoft hQ hSL h hRC hRU hRP hIP t c B hB hb
    obtain ⟨mm, X, mR, H₀, hcov, hlev, hconv', hH, hkap⟩ := hU t
    have hSLt := hSL hN _ _ hw k hk _ _ hs hs' _ hp ipD ip ipD' ip' hm hm' mm X hcov mR hlev φ v hconv' H₀ hH
      (by rw [hkap]; exact hK) B hb
    obtain ⟨u₁, hu₁, hu₁0⟩ := (hgood k hk).2 hc
    obtain ⟨hu₁', hg₁⟩ := (hgood k hk).1 u₁ hu₁
    obtain ⟨hpar₁, hq₁⟩ := hg₁.resolve_left hu₁0
    obtain ⟨w₁, hw₁0, hadj₁, hx₁⟩ := hSLt _ hpar₁ hq₁
    refine ⟨⟨w₁, hw₁0, hadj₁⟩, fun w₀ hadj₀ => ?_⟩
    have e := adjVec_unique hm' hadj₁ hadj₀
    subst e
    refine ⟨l, hLV, ?_, fun z hz => ⟨fun u hu => ?_, fun u₁ hu₁ u₂ hu₂ x₁ x₂ hup₁ hup₂ => ?_⟩⟩
    · obtain ⟨Xa, hXa, -⟩ := GlobalTheory.hermitian_adjoint_exists_unique _ _ ip ip' hm'.herm hm'.pos (stepY R t k).io
        ⟨_, hu₁'⟩
      obtain ⟨hpx, -, hf⟩ := hx₁ _ hXa
      have hf' := hf _ _ hXa
      rw [hkap, hleq] at hf'
      exact pos_ratio (hm'.herm _ _).symm (hm'.pos _ hpx.1) (hm.herm _ _).symm (hm.pos _ hpar₁.1)
        (hm'.hermD _ _).symm (hm'.posD _ hw₁0) hl0 hf'
    · obtain ⟨hu', -⟩ := (hgood k hk).1 u hu
      obtain ⟨Xa, hXa, -⟩ := GlobalTheory.hermitian_adjoint_exists_unique _ _ ip ip' hm'.herm hm'.pos (stepY R t k).io
        ⟨_, hu'⟩
      refine ⟨PiTensorProduct.lift.symm Xa.1, ?_⟩
      have := (isUp_iff R hIP hk1 hm hm' ⟨_, hu'⟩ Xa).2 hXa
      simpa using this
    · obtain ⟨hu₁', hg₁⟩ := (hgood k hk).1 u₁ hu₁
      obtain ⟨hu₂', -⟩ := (hgood k hk).1 u₂ hu₂
      have hx₁' : PiTensorProduct.lift x₁ ∈ (stY R t (k + 1)).CC (comR R t) := hup₁.1
      have hx₂' : PiTensorProduct.lift x₂ ∈ (stY R t (k + 1)).CC (comR R t) := hup₂.1
      have hup₁' : IsUp R t k (PiTensorProduct.lift.symm (⟨_, hu₁'⟩ : (stY R t k).CC (comR R t)).1)
          (PiTensorProduct.lift.symm (⟨_, hx₁'⟩ : (stY R t (k + 1)).CC (comR R t)).1) := by simpa using hup₁
      have hup₂' : IsUp R t k (PiTensorProduct.lift.symm (⟨_, hu₂'⟩ : (stY R t k).CC (comR R t)).1)
          (PiTensorProduct.lift.symm (⟨_, hx₂'⟩ : (stY R t (k + 1)).CC (comR R t)).1) := by simpa using hup₂
      have hA₁ := (isUp_iff R hIP hk1 hm hm' _ _).1 hup₁'
      have hA₂ := (isUp_iff R hIP hk1 hm hm' _ _).1 hup₂'
      refine ⟨ip ⟨_, hu₂'⟩ ⟨_, hu₁'⟩, ?_, ?_⟩
      · have := (hIP t k hk ipD ip hm ⟨_, hu₁'⟩ ⟨_, hu₂'⟩ _).2 rfl
        simp only [Subtype.coe_mk, LinearEquiv.symm_apply_apply] at this
        exact this
      · have hmain : ip' ⟨_, hx₂'⟩ ⟨_, hx₁'⟩ = ((z * l : ℝ) : ℂ) * ip ⟨_, hu₂'⟩ ⟨_, hu₁'⟩ := by
          rcases hg₁ with h0 | ⟨hpar, hq⟩
          · have hU0 : (⟨_, hu₁'⟩ : (stY R t k).CC (comR R t)) = 0 := by
              subst h0; exact Subtype.ext (map_zero _)
            have hX0 := eq_zero_of_ip hm' fun y => by rw [hA₁ y, hU0, map_zero]
            rw [hU0, hX0, map_zero, map_zero, mul_zero]
          · obtain ⟨w₂, -, hadj₂', hx⟩ := hSLt ⟨_, hu₁'⟩ hpar hq
            have e2 := adjVec_unique hm' hadj₂' hadj₀
            subst e2
            obtain ⟨-, -, hf⟩ := hx _ hA₁
            have hf' := hf _ _ hA₂
            rw [hkap, hleq] at hf'
            have h1 := conj_step (hm'.hermD _ _).symm (fun h0 => by
              have := hm'.posD _ hw₁0; rw [h0] at this; simp at this) hf'
            rw [← hm'.herm, ← hm.herm] at h1
            have hz' : (z : ℂ) = K / ipD' w₂ w₂ := hz
            rw [h1]
            push_cast
            rw [hz']
        have := (hIP t (k + 1) hk1 ipD' ip' hm' ⟨_, hx₁'⟩ ⟨_, hx₂'⟩ _).2 hmain.symm
        simp only [Subtype.coe_mk, LinearEquiv.symm_apply_apply] at this
        exact this
  by_cases hex : ∃ (t : T) (c : EigSys D), rowPart R (badPl R t) c ≠ ⊥ ∧ ∃ B, GlobalTheory.LFun.IsSysParamD D (badPl R t) D.R.r c B
  · obtain ⟨t₀, c₀, hc₀, B₀, hB₀⟩ := hex
    have hw := (hRC t₀).1
    obtain ⟨-, ⟨ipD, ip, hm⟩, -⟩ := hSoft _ _ hw k hk.le _ ((hRC t₀).2.1 k hk)
    obtain ⟨-, ⟨ipD', ip', hm'⟩, -⟩ := hSoft _ _ hw (k + 1) hk1.le _ ((hRC t₀).2.1 (k + 1) hk1)
    obtain ⟨⟨w₀, -, hadj₀⟩, hrest⟩ := key ipD ipD' hm.pure hm'.pure t₀ c₀ hc₀ B₀ hB₀
    obtain ⟨-, -, ⟨q, hq0, hq⟩, -⟩ := hrest w₀ hadj₀
    refine ⟨q, hq0, fun t c hc B hB => ?_⟩
    obtain ⟨l, hl, -, hS⟩ := (key ipD ipD' hm.pure hm'.pure t c hc B hB).2 w₀ hadj₀
    exact ⟨l, hl, hS q hq⟩
  · exact ⟨1, one_pos, fun t c hc B hB => absurd ⟨t, c, hc, B, hB⟩ hex⟩

end StepScal

namespace StepScal

open GlobalTheory.ChainOnto


set_option maxHeartbeats 4000000 in
theorem top_key (R : RealDat D A Ks) (hN : GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.NodeGap D) (hSoft : SoftQ D) (hQ : QOfVal D)
    (hLP : LPos D) (hLF : LFull D) (hSL : StepLam D) (h : RangeX R) (hRC : RChain R h)
    (hRU : RUnif R h) (hRP : RowPar R) (hIP : IPDict R) (δ : ℝ) (hδ : 0 < δ)
    (hNXt : ∀ t, Function.Bijective (toCC R h t) ∧ ∀ ipD ip, IsMet (comR R t) (stX R t) ipD ip →
      ∀ x y : (R.HX t).H, ⟪x, y⟫_ℂ = (δ : ℂ) * ip (toCC R h t y) (toCC R h t x))
    (K : ℂ) (φ : PolF D D.sp.X'.rank (Yc D (D.R.m - 1)).rank) (v : (R.MY (D.R.m - 1)).Vec)
    (hKU : IsUnif R (D.R.m - 1) (fun t => stY R t (D.R.m - 1)) (fun t => stX R t) (fun t => stepX R h t) K
      (fun _ => φ) fun _ => v) :
    ∀ (ipD₀ : SmT (R.MY (D.R.m - 1)) →ₗ[ℂ] SmT (R.MY (D.R.m - 1)) →ₗ⋆[ℂ] ℂ)
    (ipD₀' : SmT R.MX →ₗ[ℂ] SmT R.MX →ₗ⋆[ℂ] ℂ),
    (∀ v v' : (R.MY (D.R.m - 1)).Vec, ipD₀ (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ v') =
      ∏ τ, ⟪(v' τ : (R.MY (D.R.m - 1)).H τ), (v τ : (R.MY (D.R.m - 1)).H τ)⟫_ℂ) →
    (∀ v v' : R.MX.Vec, ipD₀' (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ v') =
      ∏ τ, ⟪(v' τ : R.MX.H τ), (v τ : R.MX.H τ)⟫_ℂ) →
    ∀ (t : T) (c : EigSys D), rowPart R (badPl R t) c ≠ ⊥ → ∀ B, GlobalTheory.LFun.IsSysParamD D (badPl R t) D.R.r c B →
      (∃ w₀, w₀ ≠ 0 ∧ IsAdjVec (stepX R h t) ipD₀ ipD₀' φ (PiTensorProduct.tprod ℂ v) w₀) ∧
      ∀ w₀, IsAdjVec (stepX R h t) ipD₀ ipD₀' φ (PiTensorProduct.tprod ℂ v) w₀ →
        ∃ l, IsLValue R t B D.R.m l ∧ (∃ q : ℝ, 0 < q ∧ (q : ℂ) = K / ipD₀' w₀ w₀) ∧
          ∀ z : ℝ, (z : ℂ) = K / ipD₀' w₀ w₀ → TopScalar R t c (z / δ * l) := by
  have hm2 : 2 ≤ D.R.m := D.R.two_le_m
  have hk : D.R.m - 1 < D.R.m := by omega
  have e : D.R.m - 1 + 1 = D.R.m := by omega
  obtain ⟨hK, hU⟩ := hKU
  intro ipD₀ ipD₀' hp₀ hp₀' t c hc B hB
  have hw := (hRC t).1
  have hs0 := (hRC t).2.1 0 (by omega)
  have hs := (hRC t).2.1 (D.R.m - 1) hk
  have hsX := (hRC t).2.2.1
  have hsX' : IsStage (comR R t) (twR R t) (D.R.m - 1 + 1) (stX R t) := by rw [e]; exact hsX
  have hp : IsStep (twR R t) (D.R.m - 1 + 1) (stepX R h t) := by rw [e]; exact (hRC t).2.2.2.2
  obtain ⟨-, ⟨ipD, ip, hm⟩, -⟩ := hSoft _ _ hw (D.R.m - 1) hk.le _ hs
  obtain ⟨hfin', ⟨ipD', ip', hm'⟩, -⟩ := hSoft _ _ hw D.R.m le_rfl _ hsX
  haveI := hfin'
  obtain ⟨hbij, hnorm⟩ := hNXt t
  have hnorm' := hnorm ipD' ip' hm'
  obtain rfl : ipD = ipD₀ := sesq_eq_of_tprod _ _ fun v v' => (hm.pure v v').trans (hp₀ v v').symm
  obtain rfl : ipD' = ipD₀' := sesq_eq_of_tprod _ _ fun v v' => (hm'.pure v v').trans (hp₀' v v').symm
  obtain ⟨u₀, hu₀, hu₀0⟩ := (Submodule.ne_bot_iff _).1 hc
  obtain ⟨hu₀', hpar₀⟩ := (hRP t c).2 u₀ hu₀
  obtain ⟨hb, hL⟩ := hLP _ _ hw 0 (Nat.zero_le _) _ hs0 rfl _ B (hpar₀ hu₀0 B hB)
  obtain ⟨l, hl0, hleq⟩ := hL (D.R.m - 1) hk
  obtain ⟨H, -, -, hconv, -, -⟩ := hLF _ hw.com B hb (D.R.m - 1) hk
  have hLV : IsLValue R t B D.R.m l := by
    have h1 := hleq
    rw [e] at hconv h1
    exact ⟨hconv, hl0, h1⟩
  have hgood := reached_good R hN hSoft hQ hSL h hRC hRU hRP hIP t c B hB hb
  obtain ⟨mm, X, mR, H₀, hcov, hlev, hconv', hH, hkap⟩ := hU t
  have hSLt := hSL hN _ _ hw (D.R.m - 1) hk _ _ hs hsX' _ hp ipD ip ipD' ip' hm hm' mm X hcov mR hlev φ v hconv'
    H₀ hH (by rw [hkap]; exact hK) B hb
  obtain ⟨u₁, hu₁, hu₁0⟩ := (hgood _ hk).2 hc
  obtain ⟨hu₁', hg₁⟩ := (hgood _ hk).1 u₁ hu₁
  obtain ⟨hpar₁, hq₁⟩ := hg₁.resolve_left hu₁0
  obtain ⟨w₁, hw₁0, hadj₁, hx₁⟩ := hSLt _ hpar₁ hq₁
  refine ⟨⟨w₁, hw₁0, hadj₁⟩, fun w₀ hadj₀ => ?_⟩
  have e1 := adjVec_unique hm' hadj₁ hadj₀
  subst e1
  have hδc : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ.ne'

  have hread : ∀ (U : (stY R t (D.R.m - 1)).CC (comR R t)) (x : (R.HX t).H),
      (∀ y, ⟪x, y⟫_ℂ = ip ((stepX R h t).io (toCC R h t y)) U) →
      ∀ Y, ip' Y ((δ : ℂ) • toCC R h t x) = ip ((stepX R h t).io Y) U := by
    intro U x hx Y
    obtain ⟨y, rfl⟩ := hbij.2 Y
    rw [LinearMap.map_smulₛₗ, Complex.conj_ofReal, smul_eq_mul, ← hnorm', hx]
  refine ⟨l, hLV, ?_, fun z hz => ⟨fun u hu => ?_, fun u₁ hu₁ u₂ hu₂ x₁ x₂ hup₁ hup₂ => ?_⟩⟩
  · obtain ⟨Xa, hXa, -⟩ := GlobalTheory.hermitian_adjoint_exists_unique _ _ ip ip' hm'.herm hm'.pos (stepX R h t).io
      ⟨_, hu₁'⟩
    obtain ⟨hpx, -, hf⟩ := hx₁ _ hXa
    have hf' := hf _ _ hXa
    rw [hkap, hleq] at hf'
    exact pos_ratio (hm'.herm _ _).symm (hm'.pos _ hpx.1) (hm.herm _ _).symm (hm.pos _ hpar₁.1)
      (hm'.hermD _ _).symm (hm'.posD _ hw₁0) hl0 hf'
  · obtain ⟨hu', -⟩ := (hgood _ hk).1 u hu
    obtain ⟨Xa, hXa, -⟩ := GlobalTheory.hermitian_adjoint_exists_unique _ _ ip ip' hm'.herm hm'.pos (stepX R h t).io
      ⟨_, hu'⟩
    obtain ⟨x, hx⟩ := hbij.2 ((δ : ℂ)⁻¹ • Xa)
    refine ⟨x, ?_⟩
    have := (isUpTop_iff R hIP h hm2 hm ⟨_, hu'⟩ x).2 fun y => by
      rw [hnorm', hx, LinearMap.map_smulₛₗ, hXa, map_inv₀, Complex.conj_ofReal, smul_eq_mul, ← mul_assoc,
        mul_inv_cancel₀ hδc, one_mul]
    simp only [Subtype.coe_mk, LinearEquiv.symm_apply_apply] at this
    exact this
  · obtain ⟨hu₁', hg₁⟩ := (hgood _ hk).1 u₁ hu₁
    obtain ⟨hu₂', -⟩ := (hgood _ hk).1 u₂ hu₂
    have hup₁' : IsUpTop R t (PiTensorProduct.lift.symm (⟨_, hu₁'⟩ : (stY R t (D.R.m - 1)).CC (comR R t)).1) x₁ := by
      simp only [Subtype.coe_mk, LinearEquiv.symm_apply_apply]; exact hup₁
    have hup₂' : IsUpTop R t (PiTensorProduct.lift.symm (⟨_, hu₂'⟩ : (stY R t (D.R.m - 1)).CC (comR R t)).1) x₂ := by
      simp only [Subtype.coe_mk, LinearEquiv.symm_apply_apply]; exact hup₂
    have hA₁ := (isUpTop_iff R hIP h hm2 hm _ _).1 hup₁'
    have hA₂ := (isUpTop_iff R hIP h hm2 hm _ _).1 hup₂'
    refine ⟨ip ⟨_, hu₂'⟩ ⟨_, hu₁'⟩, ?_, ?_⟩
    · have := (hIP t (D.R.m - 1) hk ipD ip hm ⟨_, hu₁'⟩ ⟨_, hu₂'⟩ _).2 rfl
      simp only [Subtype.coe_mk, LinearEquiv.symm_apply_apply] at this
      exact this
    · rcases hg₁ with h0 | ⟨hpar, hq⟩
      · have hU0 : (⟨_, hu₁'⟩ : (stY R t (D.R.m - 1)).CC (comR R t)) = 0 := by
          subst h0; exact Subtype.ext (map_zero _)
        rw [hA₁ x₂, hU0, map_zero, map_zero, mul_zero]
      · obtain ⟨w₂, -, hadj₂', hx⟩ := hSLt ⟨_, hu₁'⟩ hpar hq
        have e2 := adjVec_unique hm' hadj₂' hadj₀
        subst e2
        obtain ⟨-, -, hf⟩ := hx _ (hread _ _ hA₁)
        have hf' := hf _ _ (hread _ _ hA₂)
        rw [hkap, hleq] at hf'
        have h1 := conj_step (hm'.hermD _ _).symm (fun h0 => by
          have := hm'.posD _ hw₁0; rw [h0] at this; simp at this) hf'
        rw [← hm'.herm, ← hm.herm] at h1
        rw [LinearMap.map_smulₛₗ, LinearMap.map_smul, Complex.conj_ofReal, smul_eq_mul, LinearMap.smul_apply,
          smul_eq_mul, ← hnorm'] at h1
        have hz' : (z : ℂ) = K / ipD' w₂ w₂ := hz
        push_cast
        rw [div_eq_mul_inv (z : ℂ), hz']
        field_simp
        linear_combination h1


set_option maxHeartbeats 1600000 in
theorem top_scalar (R : RealDat D A Ks) (hN : GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.NodeGap D) (hSoft : SoftQ D) (hQ : QOfVal D)
    (hLP : LPos D) (hLF : LFull D) (hSL : StepLam D) (h : RangeX R) (hRC : RChain R h) (hNX : NormX R h)
    (hRU : RUnif R h) (hRP : RowPar R) (hIP : IPDict R) :
    ∃ r : ℝ, 0 < r ∧ ∀ (t : T) (c : EigSys D), rowPart R (badPl R t) c ≠ ⊥ →
      ∀ B, GlobalTheory.LFun.IsSysParamD D (badPl R t) D.R.r c B →
        ∃ l, IsLValue R t B D.R.m l ∧ TopScalar R t c (r * l) := by
  have hk : D.R.m - 1 < D.R.m := by have := D.R.two_le_m; omega
  obtain ⟨δ, hδ, hNXt⟩ := hNX
  obtain ⟨K, φ, v, hKU⟩ := hRU.2
  have key := top_key R hN hSoft hQ hLP hLF hSL h hRC hRU hRP hIP δ hδ hNXt K φ v hKU
  by_cases hex : ∃ (t : T) (c : EigSys D), rowPart R (badPl R t) c ≠ ⊥ ∧ ∃ B, GlobalTheory.LFun.IsSysParamD D (badPl R t) D.R.r c B
  · obtain ⟨t₀, c₀, hc₀, B₀, hB₀⟩ := hex
    have hw := (hRC t₀).1
    obtain ⟨-, ⟨ipD, ip, hm⟩, -⟩ := hSoft _ _ hw (D.R.m - 1) hk.le _ ((hRC t₀).2.1 (D.R.m - 1) hk)
    obtain ⟨-, ⟨ipD', ip', hm'⟩, -⟩ := hSoft _ _ hw D.R.m le_rfl _ (hRC t₀).2.2.1
    obtain ⟨⟨w₀, -, hadj₀⟩, hrest⟩ := key ipD ipD' hm.pure hm'.pure t₀ c₀ hc₀ B₀ hB₀
    obtain ⟨-, -, ⟨q, hq0, hq⟩, -⟩ := hrest w₀ hadj₀
    refine ⟨q / δ, div_pos hq0 hδ, fun t c hc B hB => ?_⟩
    obtain ⟨l, hl, -, hS⟩ := (key ipD ipD' hm.pure hm'.pure t c hc B hB).2 w₀ hadj₀
    exact ⟨l, hl, hS q hq⟩
  · exact ⟨1, one_pos, fun t c hc B hB => absurd ⟨t, c, hc, B, hB⟩ hex⟩

end StepScal


open StepScal in
theorem scalars_of_realisation : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.NodeGap D → SoftQ D → QOfVal D → LPos D → LFull D → StepLam D → ∀ h : RangeX R, RChain R h → NormX R h → RUnif R h → RowPar R → IPDict R → GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.Scalars R := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F _ hN hSoft hQ hLP hLF hSL h hRC hNX hRU hRP hIP
  obtain ⟨rT, hrT, hT⟩ := top_scalar R hN hSoft hQ hLP hLF hSL h hRC hNX hRU hRP hIP
  have hmid := fun k (hk1 : k + 1 < D.R.m) => mid_scalar R hN hSoft hQ hLP hLF hSL h hRC hRU hRP hIP k hk1
  choose! rM hrM hM using hmid
  refine ⟨fun j => if j = D.R.m then rT else rM (j - 1), fun j hj1 hjm => ?_, fun t c hc => ?_⟩
  · by_cases hj : j = D.R.m
    · simp only [if_pos hj]; exact hrT
    · simp only [if_neg hj]; exact hrM (j - 1) (by omega)
  · refine ⟨(hRP t c).1 hc, fun B hB => ⟨fun k hk => ?_, ?_⟩⟩
    · obtain ⟨l, hl, hS⟩ := hM k hk t c hc B hB
      refine ⟨l, hl, ?_⟩
      simp only [if_neg (show k + 1 ≠ D.R.m by omega), Nat.add_sub_cancel]
      exact hS
    · obtain ⟨l, hl, hS⟩ := hT t c hc B hB
      refine ⟨l, hl, ?_⟩
      simp only [if_pos rfl]
      exact hS

end GlobalTheory.ChainTw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainStepScalarsOfRealisationStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chainStep_scalars_of_realisation : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.NodeGap D → SoftQ D → QOfVal D → LPos D → LFull D → StepLam D → ∀ h : RangeX R, RChain R h → NormX R h → RUnif R h → RowPar R → IPDict R → GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.Scalars R := by
  first | exact @GlobalTheory.ChainTw.scalars_of_realisation | exact GlobalTheory.ChainTw.scalars_of_realisation | (intros; apply GlobalTheory.ChainTw.scalars_of_realisation <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainThetaLiftsAdjointOfCuspRapidDecay
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainThetaLiftsAdjointOfCuspRapidDecay
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ChainTw

theorem upAdjQ_of_cuspRapidDecay : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, UpAdjQ D := by
  intro hP D _ c w hw k _ s s' hs hs' p hp u y φ v _ w' _
  obtain ⟨hr, -, hfl⟩ := hs
  obtain ⟨hr', -, hfl'⟩ := hs'
  have hc : c.Is := hw.com
  have hF := GlobalTheory.T.thetaKernel_iterated_integrals_swap D c.ψ c.θ s.V s'.V (c.chS (k + 1)) (c.chT (k + 1)) p.ω hc.inf hp.weil (p.pt φ) (hp.theta φ)
    s.ν s.fd s'.ν s'.fd hfl.haar hfl.fund hfl'.haar hfl'.fund (PiLocalization₂.val u v) (PiLocalization₂.val y w')
    (rapidDec_val hP hc u v) (rapidDec_val hP hc y w')
  simp only [PiLocalization₂.pet, Lift.pet, Step.up]
  calc ∫ h in s'.fd, PiLocalization₂.val y w' h * starRingEnd ℂ (∫ g in s.fd, conj (thetaKO p.ω g h (p.pt φ)) * PiLocalization₂.val u v g ∂s.ν) ∂s'.ν
      = ∫ h in s'.fd, ∫ g in s.fd, thetaKO p.ω g h (p.pt φ) * PiLocalization₂.val y w' h * conj (PiLocalization₂.val u v g) ∂s.ν ∂s'.ν := by
        congr 1; funext h
        rw [← integral_conj, ← integral_const_mul]
        congr 1; funext g
        simp only [map_mul, Complex.conj_conj]; ring
    _ = ∫ g in s.fd, ∫ h in s'.fd, thetaKO p.ω g h (p.pt φ) * PiLocalization₂.val y w' h * conj (PiLocalization₂.val u v g) ∂s'.ν ∂s.ν := hF
    _ = ∫ g in s.fd, PiLocalization₂.val (p.io y) (p.It φ w') g * starRingEnd ℂ (PiLocalization₂.val u v g) ∂s.ν := by
        congr 1; funext g
        rw [integral_mul_const]
        congr 1
        exact hp.io.eq y φ w' g

end GlobalTheory.ChainTw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainThetaLiftsAdjointOfCuspRapidDecayStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chainThetaLiftsAdjoint_of_cuspRapidDecay : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, UpAdjQ D := by
  first | exact @GlobalTheory.ChainTw.upAdjQ_of_cuspRapidDecay | exact GlobalTheory.ChainTw.upAdjQ_of_cuspRapidDecay | (intros; apply GlobalTheory.ChainTw.upAdjQ_of_cuspRapidDecay <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainThetaLiftUpEqAdjointValue
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainThetaLiftUpEqAdjointValue
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ChainTw

theorem upVal_of_span_adj : ∀ D : D7, SoftQ D → UpSpanQ D → UpAdjQ D → UpVal D := by
  intro D hSoft hSpan hAdj
  intro hgap c tw htw k hk s s' hs hs' p hp ipD ip ipD' ip' hM hM' φ v hv
  have hk' : k + 1 ≤ D.R.m := hk
  haveI : FiniteDimensional ℂ (s'.CC c) := (hSoft c tw htw (k + 1) hk' s' hs').1
  have hl : ∀ (u : s.CC c) (x : s'.CC c), (∀ y, ip' y x = ip (p.io y) u) → ∀ (y : s'.CC c), ∀ w ∈ s'.KF,
      s'.pet (PiLocalization₂.val y w) (p.up φ (PiLocalization₂.val u v)) = ip' y x * ipD (p.It φ w) v := by
    intro u x hx y w hw
    rw [hx y]
    exact (hAdj hgap c tw htw k hk s s' hs hs' p hp u y φ v hv w hw).trans (hM.schur _ _ _ _)
  have key : ∀ (u : s.CC c) (x : s'.CC c), (∀ y, ip' y x = ip (p.io y) u) → p.up φ (PiLocalization₂.val u v) ≠ 0 →
      x ≠ 0 ∧ ∃ w₁, IsAdjVec p ipD ipD' φ v w₁ ∧ p.up φ (PiLocalization₂.val u v) = PiLocalization₂.val x w₁ := by
    intro u x hx hF
    obtain ⟨hx0, w₁, hw₁, hFx⟩ := GlobalTheory.ChainOnto.value_of_adjoint_of_mem_span (GA D s'.V) (SmT s'.M) (s'.CC c)
      (s'.CC c).subtype s'.KF ipD' ip' s'.pet hM'.hermD hM'.posD hM'.herm hM'.pos
      (fun y w n ys ws => pet_val_sum hM' y w n ys ws) x (p.up φ (PiLocalization₂.val u v)) (fun w => ipD (p.It φ w) v)
      (hSpan hgap c tw htw k hk s s' hs hs' p hp u φ v hv) (hl u x hx) hF
    have hFx' : p.up φ (PiLocalization₂.val u v) = PiLocalization₂.val x w₁ := hFx
    refine ⟨hx0, w₁, ⟨hw₁, fun w hw => ?_⟩, hFx'⟩
    have h1 := hl u x hx x w hw
    rw [hFx'] at h1
    have h2 := (hM'.schur x x w w₁).symm.trans h1
    have hxx : ip' x x ≠ 0 := fun h => by
      have := hM'.pos x hx0
      rw [h] at this
      simp at this
    exact mul_left_cancel₀ hxx h2
  refine ⟨fun ⟨u, hF⟩ => ?_, fun w₀ hw₀ u x hx => ?_⟩
  · obtain ⟨x, hx, -⟩ := GlobalTheory.hermitian_adjoint_exists_unique (s.CC c) (s'.CC c) ip ip' hM'.herm hM'.pos p.io u
    obtain ⟨-, w₁, hw₁, hFx⟩ := key u x hx hF
    refine ⟨w₁, fun h => hF ?_, hw₁⟩
    rw [hFx, h]
    simp
  · by_cases hF : p.up φ (PiLocalization₂.val u v) = 0
    · have h1 := hl u x hx x w₀ hw₀.1
      rw [hF, ← hw₀.2 w₀ hw₀.1] at h1
      have h0 : s'.pet (PiLocalization₂.val x w₀) (0 : GA D s'.V → ℂ) = 0 := by
        simp [PiLocalization₂.pet, Lift.pet]
      rw [h0] at h1
      rw [hF]
      rcases mul_eq_zero.mp h1.symm with h | h
      · have hx0 : x = 0 := by
          by_contra hne
          have := hM'.pos x hne
          rw [h] at this
          simp at this
        subst hx0
        first | rfl | simp [PiLocalization₂.val]
      · have hw0 : w₀ = 0 := by
          by_contra hne
          have := hM'.posD w₀ hne
          rw [h] at this
          simp at this
        subst hw0
        simp
    · obtain ⟨-, w₁, hw₁, hFx⟩ := key u x hx hF
      have hd : w₁ = w₀ := by
        by_contra hne
        have hdK : w₁ - w₀ ∈ s'.KF := s'.KF.sub_mem hw₁.1 hw₀.1
        have hz : ipD' (w₁ - w₀) (w₁ - w₀) = 0 := by
          rw [map_sub, hw₁.2 _ hdK, hw₀.2 _ hdK, sub_self]
        have := hM'.posD _ (sub_ne_zero.mpr hne)
        rw [hz] at this
        simp at this
      rw [hFx, hd]

end GlobalTheory.ChainTw
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainThetaLiftUpEqAdjointValueStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chain_theta_lift_up_eq_adjoint_value : ∀ D : D7, SoftQ D → UpSpanQ D → UpAdjQ D → UpVal D := by
  first | exact @GlobalTheory.ChainTw.upVal_of_span_adj | exact GlobalTheory.ChainTw.upVal_of_span_adj | (intros; apply GlobalTheory.ChainTw.upVal_of_span_adj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalarsOfGivenData
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)

namespace GlobalTheory.ChainTw

theorem scalars_of_given_all : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.UnramifiedDoublingGL → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.NodeGap D → GlobalTheory.Core.Rk.SW.HeckeFormNS D → GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.Scalars R := by
  intro hHCF hCRD hDSC hHCM hCW hHowe hUDG D G _ _ Pl0 T A Ks _ _ _ R F g hNG hHecke
  have soft : SoftQ D := GlobalTheory.T.twistedChain_stage_soft_properties hHCF hCRD D
  have law : LevelLawQ D := GlobalTheory.T.twistedChain_datum_laws_under_levels D
  have restore : Restore D := GlobalTheory.T.chainTwistEulerFactorsRestore_proof D
  have lfull : LFull D := GlobalTheory.T.twistedThetaChain_LValue_quotientFactorization D
  have upSpan : UpSpanQ D := GlobalTheory.T.twistedChain_thetaLiftUpSpan hDSC hHCM hCRD hCW D law
  have upAdj : UpAdjQ D := GlobalTheory.T.chainThetaLiftsAdjoint_of_cuspRapidDecay hCRD D
  have upVal : UpVal D := GlobalTheory.T.chain_theta_lift_up_eq_adjoint_value D soft upSpan upAdj
  have exact : StepExactNS D :=
    GlobalTheory.T.thetaLiftChainStep_exact_innerProduct D hHecke soft (GlobalTheory.T.chainTwistPlacesIntegralPeel_of_doubling hUDG hCRD D) (GlobalTheory.T.chainLevelIntegralRealZeta_of_twisted_transform_laws D law)
  have lam : StepLam D := GlobalTheory.T.twistedThetaChain_step_adjoint_scalar D soft (GlobalTheory.T.chainThetaLiftUp_parameter_of_transfer hCRD hHowe D) (GlobalTheory.T.chainThetaLiftUpLowerBlockParameter_proof hCRD D)
    (GlobalTheory.T.lowerBlockParameter_of_one_nonzeroValue D soft) upVal exact lfull restore
  have hX : RangeX R := GlobalTheory.T.realFormsRangeMultiplicity_of_scalarHypotheses R F g
  have chain : ∀ h : RangeX R, RChain R h := GlobalTheory.T.realTupleTwistedChain_of_scalarHypotheses R F g
  have zeta : RealZetaQ D := GlobalTheory.T.twistedChain_realZeta_nonvanishing hHCM D (GlobalTheory.T.archimedeanThetaCorrespondence_towers_real_data hDSC hHCM D)
  have unif : RUnif R hX := GlobalTheory.T.twistedChain_step_constants_tuple_indep R F g hNG zeta restore hX (chain hX)
    (GlobalTheory.T.realMeasureUniformInTuple_of_thetaLiftScalar R F g chain hX) (GlobalTheory.T.realQuotientVolumeGrowth_of_scalarHypotheses R F g chain hX) (GlobalTheory.T.realDatumNormShrink_of_scalarHypotheses R F g)
  exact GlobalTheory.T.chainStep_scalars_of_realisation R F g hNG soft (GlobalTheory.T.lowerBlockParameter_of_one_nonzeroValue D soft) (GlobalTheory.T.chain_first_stage_L_values_positive hCRD D) lfull lam hX
    (chain hX) (GlobalTheory.T.realLastStageNormalized_of_scalarHypotheses R F g hX) unif (GlobalTheory.T.rows_of_part_have_part_params_first_chain_member hCRD R F g chain hX) (GlobalTheory.T.schurProduct_typings_agree_thetaChain R F g)

end GlobalTheory.ChainTw
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalarsOfGivenDataStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaChain_steps_positive_multiple_of_LValue : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.UnramifiedDoublingGL → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.NodeGap D → GlobalTheory.Core.Rk.SW.HeckeFormNS D → GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.Scalars R := by
  first | exact @GlobalTheory.ChainTw.scalars_of_given_all | exact GlobalTheory.ChainTw.scalars_of_given_all | (intros; apply GlobalTheory.ChainTw.scalars_of_given_all <;> assumption)
end
