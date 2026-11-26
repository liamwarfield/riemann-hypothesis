module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundHolds
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointHeightDualAndLinearComb
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilOperatorIdempotentSumVacuumNormalisedSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemModelInteriorOfMemAbelianLocusPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothConeFaceOfInteriorCommonPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjHalfCosetRepsScalarDilation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyRuleScaleSectionPowEight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelAfterExt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroStandardThetaLineReadAdelic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureTranslateLevelRealBoxLeIndexMul

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleTrivialOfSamePolarization
open CategoryTheory AlgebraicGeometry Set Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.ArInt GlobalTheory.TorsionForm
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt stdLat symMat tauU siegel symPart ChernIsFlat IsMetric InducesPolarisation cov)
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology
open scoped ContDiff
open MonoidalCategory CartesianMonoidalCategory Limits
open GlobalTheory.CechPic (Pic cls lam)
open MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleKerFibre

theorem relAmple_kTriv_of_lam_eq : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ (L₀ : LB B.left) (h₀ : L₀.IsLB), Out.RelAmple B L₀ → Out.KTriv B L₀ → ∀ (N : LB B.left) (hN : N.IsLB), lam (cls N hN) (fst B B) (snd B B) = lam (cls L₀ h₀) (fst B B) (snd B B) → Out.RelAmple B N ∧ Out.KTriv B N := by
  intro K _ _ B _ hB L₀ h₀ hA hK N hN hlam
  have := hB.comm
  obtain ⟨O, hO, eO⟩ := CechPic.cls_surj (cls N hN - cls L₀ h₀)
  have lamO : lam (cls O hO) (fst B B) (snd B B) = 0 := by
    rw [eO, GlobalTheory.PrimitiveOverField.lam_sub, hlam, sub_self]
  obtain ⟨x, hx⟩ := GlobalTheory.PointTranslate.exists_point_cls_eq_lam K B hB L₀ h₀ hK O hO lamO
  have hR : (GlobalTheory.RigidTranslate.rigTransl L₀ x).IsLB := LB.isLB_linComb h₀ _ _
  have hcls : cls _ hR = cls N hN := by
    rw [CechPic.cls_linComb h₀, Fin.sum_univ_two]
    have e1 : cls N hN = cls O hO + cls L₀ h₀ := by rw [eO]; abel
    rw [e1, hx, GlobalTheory.PrimitiveOverField.lam_const, Over.id_left, CechPic.pull_id]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul]
    rw [GlobalTheory.PrimitiveOverField.pull_const, GlobalTheory.PolTranslate.transl, _root_.mul_comm (𝟙 B)]
    abel
  have hiso := (CechPic.cls_eq_iff hR hN).1 hcls
  refine ⟨?_, GlobalTheory.MulDescent.kTriv_of_lbIso hR hN hiso
    (GlobalTheory.RigidTranslate.kTriv_rigTransl_any _ B L₀ h₀ x hK)⟩
  have hAR := GlobalTheory.RigidTranslate.relAmple_rigTransl_point K B hB L₀ h₀ x hA
  obtain ⟨w, hw⟩ : LBIso N ((GlobalTheory.RigidTranslate.rigTransl L₀ x).pull (𝟙 B.left)) :=
    hiso.symm.chartPull (Geo.Tor.chartPullId N) (Geo.Tor.chartPullPull _ (𝟙 _) (𝟙 _) rfl)
  exact relAmple_pull (A' := B) (IsPullback.id_horiz B.hom) hR hN ((isGen_iff w).1 hw) ⊤
    (isAffineOpen_top _) (fun _ => trivial) hAR

end GlobalTheory.AmpleKerFibre
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationExtendLocalizationAtPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationExtendLocalizationAtPrime
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

theorem derivation_extend_localization_atPrime (F A R : Type) [CommRing F] [CommRing A] [CommRing R]
    [Algebra F A] [Algebra A R] [Algebra F R] [IsScalarTower F A R] (P : Ideal A) [P.IsPrime]
    [IsLocalization.AtPrime R P] (D : Derivation F A R) :
    ∃ D' : Derivation F R R, ∀ a, D' (algebraMap A R a) = D a := by
  haveI : Algebra.FormallyEtale A R := Algebra.FormallyEtale.of_isLocalization P.primeCompl
  have hb := KaehlerDifferential.isBaseChange_of_formallyEtale F A R
  refine ⟨(hb.lift D.liftKaehlerDifferential).compDer (KaehlerDifferential.D F R), fun a => ?_⟩
  show hb.lift D.liftKaehlerDifferential (KaehlerDifferential.D F R (algebraMap A R a)) = D a
  rw [← KaehlerDifferential.map_D F F A R, hb.lift_eq, Derivation.liftKaehlerDifferential_comp_D]

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationExtendLocalizationAtPrimeStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_derivation_extend_localization_atPrime : ∀ (F A R : Type) [CommRing F] [CommRing A] [CommRing R] [Algebra F A] [Algebra A R] [Algebra F R] [IsScalarTower F A R] (P : Ideal A) [P.IsPrime] [IsLocalization.AtPrime R P] (D : Derivation F A R), ∃ D' : Derivation F R R, ∀ a, D' (algebraMap A R a) = D a := by
  first | exact @GlobalTheory.derivation_extend_localization_atPrime | exact GlobalTheory.derivation_extend_localization_atPrime | (intros; apply GlobalTheory.derivation_extend_localization_atPrime <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupStalkNoetherianNormalFractionRing
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupStalkNoetherianNormalFractionRing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem stalk_isNoetherian_normal_fractionRing : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ)
    (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z),
    letI : Algebra (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ := (X₁.M.stalkHom z₁).toAlgebra;
    IsDomain (X₁.M.Z.presheaf.stalk z₁) ∧ IsFractionRing (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ ∧
      IsIntegrallyClosed (X₁.M.Z.presheaf.stalk z₁) ∧ IsNoetherianRing (X₁.M.Z.presheaf.stalk z₁) := by
  intro g n F W Z i X₁ z₁
  letI : Algebra (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ := (X₁.M.stalkHom z₁).toAlgebra
  have hN := X₁.normal
  refine ⟨GlobalTheory.IsNormalScheme.isDomain_stalk z₁, ?_, GlobalTheory.IsNormalScheme.isIntegrallyClosed_stalk z₁, ?_⟩
  · have : FaithfulSMul (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ :=
      (faithfulSMul_iff_algebraMap_injective _ _).2 (X₁.M.stalkHom_injective z₁)
    refine IsFractionRing.of_field _ _ fun x => ?_
    obtain ⟨a, b, -, hx⟩ := IsFractionRing.div_surjective (A := X₁.M.O z₁) x
    refine ⟨(X₁.M.stalkEquiv z₁).symm a, (X₁.M.stalkEquiv z₁).symm b, ?_⟩
    have h : ∀ c : X₁.M.O z₁, algebraMap (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ ((X₁.M.stalkEquiv z₁).symm c) = c := fun c => by
      change X₁.M.stalkHom z₁ _ = _
      rw [← RatModel.coe_stalkEquiv, RingEquiv.apply_symm_apply]
    rw [h, h, ← hx]
    rfl
  · have : IsDedekindDomain X₁.o₁ := X₁.ar.ded
    have := X₁.M.lft
    have : IsLocallyNoetherian (Sp X₁.o₁) :=
      inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of X₁.o₁)))
    have : IsLocallyNoetherian X₁.M.Z := LocallyOfFiniteType.isLocallyNoetherian X₁.M.s
    infer_instance

end GlobalTheory.Poinc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupStalkNoetherianNormalFractionRingStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSetup_stalk_noetherian_normal_fractionRing : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z), letI : Algebra (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ := (X₁.M.stalkHom z₁).toAlgebra; IsDomain (X₁.M.Z.presheaf.stalk z₁) ∧ IsFractionRing (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ ∧ IsIntegrallyClosed (X₁.M.Z.presheaf.stalk z₁) ∧ IsNoetherianRing (X₁.M.Z.presheaf.stalk z₁) := by
  first | exact @GlobalTheory.Poinc.stalk_isNoetherian_normal_fractionRing | exact GlobalTheory.Poinc.stalk_isNoetherian_normal_fractionRing | (intros; apply GlobalTheory.Poinc.stalk_isNoetherian_normal_fractionRing <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiFor
noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {p : ℕ} [Fact p.Prime] {S : Scheme.{0}}

def RosatiFor (D : Datum p) {A : Over S} [GrpObj A] (act : OActN D.O A) (P : LB (G2 A).left) : Prop :=
  ∀ c : D.O, LBIso (P.pull (lift (fst A A ≫ act.act c) (snd A A)).left)
    (P.pull (lift (fst A A) (snd A A ≫ act.act (D.star c).unop)).left)

def EtaOK (D : Datum p) (N : ℕ) {A : Over S} [GrpObj A] (act : OActN D.O A) (eta : D.La → (𝟙_ (Over S) ⟶ A)) :
    Prop :=
  (∀ x y, eta (x + y) = eta x * eta y) ∧ (∀ (c : D.O) x, eta (c • x) = eta x ≫ act.act c) ∧ ∀ x, eta (N • x) = 1

def GeomAt (D : Datum p) (N : ℕ) {A : Over S} [GrpObj A] (act : OActN D.O A) (P : LB (G2 A).left)
    (eta : D.La → (𝟙_ (Over S) ⟶ A)) (k : Type) [Field k] (x : Sp k ⟶ S) : Prop :=
  ∃ I : TateIsoO D k (Over.mk x ⟶ A) (fun c g => g ≫ act.act c)
      (fun n g g' z => Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) n g g' (unitOn z)),
    ∀ y, toUnit _ ≫ eta y = I.ev N y

variable {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {s : S ⟶ Sp R}

theorem Obj.rosatiFor (o : Obj b N s) : RosatiFor D o.act o.P := o.rosati

theorem Obj.etaOK (o : Obj b N s) : EtaOK D N o.act o.eta := ⟨o.eta_add, o.eta_lin, o.eta_ker⟩

theorem Obj.geomAt (o : Obj b N s) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : R →+* k)
    (hx : x ≫ s = spMap β) : GeomAt D N o.act o.P o.eta k x := o.geom k x β hx

theorem Obj.lieHer (o : Obj b N s) (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ S)
    (hx : x ≫ s = spMap β) : LieHer b o.act β x := by
  intro R'' _ g
  have e₁ : (spMap g ≫ x) ≫ s = spMap (g.comp β) := by
    rw [Category.assoc, hx]
    simp [spMap, ← Spec.map_comp]
    try rfl
  refine ⟨o.lie R'' (g.comp β) (spMap g ≫ x) e₁, fun k _ _ g' i => ?_⟩
  refine o.lieRank k (spMap g' ≫ spMap g ≫ x) (g'.comp (g.comp β)) ?_ i
  rw [Category.assoc, Category.assoc, hx]
  simp [spMap, ← Spec.map_comp]
  try rfl

theorem RosatiFor.of_iso {A : Over S} [GrpObj A] {act : OActN D.O A} {P P' : LB (G2 A).left} (hP : P.IsLB)
    (hP' : P'.IsLB) (H : LBIso P P') (h : RosatiFor D act P) : RosatiFor D act P' := fun c =>
  LBIso.trans (pull_isLB hP' _) (pull_isLB hP _) (pull_isLB hP' _)
    (GlobalTheory.RigidBundleGlue.LBIso.pull H _).symm
    (LBIso.trans (pull_isLB hP _) (pull_isLB hP _) (pull_isLB hP' _) (h c) (GlobalTheory.RigidBundleGlue.LBIso.pull H _))

end GlobalTheory.UPel.HT
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MongeAmpereIntegralInvariantHomeomorphTransport
namespace MongeAmpereTransport
section
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CxPts GlobalTheory.Mean4O.CombForm

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.MaTransport

variable {e : ℕ} {X X' : Type} [TopologicalSpace X] [TopologicalSpace X']

def carryPartition (A : FinHolAtlas e X) (h : X ≃ₜ X') (P : ChartPartition A) :
    ChartPartition (tAtlas A h) where
  χ j := P.χ j ∘ h.symm
  smooth j k := by
    have e₁ : (P.χ j ∘ h.symm) ∘ ((tAtlas A h).chart k).symm = P.χ j ∘ (A.chart k).symm :=
      funext fun y => by simp [tAtlas_symm]
    rw [e₁]
    exact P.smooth j k
  nonneg j x := P.nonneg j _
  tsupport_subset j := fun x hx =>
    P.tsupport_subset j (tsupport_comp_subset_preimage (P.χ j) h.symm.continuous hx)
  sum_eq_one x := P.sum_eq_one (h.symm x)

theorem isPotential_pullback (A : FinHolAtlas e X) (h : X ≃ₜ X') {Q : LocPot X'}
    (hQ : IsPotential (tAtlas A h) Q) : IsPotential A (Q.pullback h h.continuous) := by
  refine ⟨fun x j => ?_, fun x x' y hy => ?_⟩
  · exact hQ.1 (h x) j
  · obtain ⟨W, hW, hyW, G, hG, hd⟩ := hQ.2 (h x) (h x') (h y) hy
    refine ⟨h ⁻¹' W, hW.preimage h.continuous, hyW, G ∘ h, fun j => ?_, fun z hz => ?_⟩
    · exact hG j
    · exact hd (h z) hz

theorem integralWith_carry (A : FinHolAtlas e X) (h : X ≃ₜ X') (P : ChartPartition A)
    (Φ : Fin e → LocPot X') (g : X' → ℝ) :
    integralWith (tAtlas A h) (carryPartition A h P) Φ g =
      integralWith A P (fun i => (Φ i).pullback h h.continuous) (g ∘ h) := by
  refine Finset.sum_congr rfl fun j _ => ?_
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  change P.χ j (h.symm (h ((A.chart j).symm y))) * g (h ((A.chart j).symm y)) * _ =
    P.χ j ((A.chart j).symm y) * g (h ((A.chart j).symm y)) * _
  rw [h.symm_apply_apply]
  rfl

theorem mInt_tAtlas (e : ℕ) (X X' : Type) [TopologicalSpace X] [TopologicalSpace X'] [CompactSpace X]
    [T2Space X] [CompactSpace X'] [T2Space X'] (A : FinHolAtlas e X) (h : X ≃ₜ X')
    (Φ : Fin e → LocPot X') (g : X' → ℝ) (hΦ : ∀ i, IsPotential (tAtlas A h) (Φ i))
    (hg : Continuous g) :
    mInt (tAtlas A h) Φ g = mInt A (fun i => (Φ i).pullback h h.continuous) (g ∘ h) := by
  obtain ⟨P⟩ := existsPartition A
  have hΨ : ∀ i, IsPotential A ((Φ i).pullback h h.continuous) :=
    fun i => isPotential_pullback A h (hΦ i)
  rw [mIntEq (tAtlas A h) (carryPartition A h P) Φ hΦ g (mIntegrableCont _ Φ hΦ g hg),
    mIntEq A P _ hΨ (g ∘ h) (mIntegrableCont A _ hΨ _ (hg.comp h.continuous)),
    integralWith_carry]

end GlobalTheory.CompanionTheory.MaTransport

end
end

end MongeAmpereTransport
section
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CxPts GlobalTheory.Mean4O.CombForm
theorem _root_.GlobalTheory.Adopt.mongeAmpereIntegral_invariant_homeomorph_transport : ∀ (e : ℕ) (X X' : Type) [TopologicalSpace X] [TopologicalSpace X'] [CompactSpace X] [T2Space X] [CompactSpace X'] [T2Space X'] (A : FinHolAtlas e X) (h : X ≃ₜ X') (Φ : Fin e → LocPot X') (g : X' → ℝ), (∀ i, IsPotential (tAtlas A h) (Φ i)) → Continuous g → mInt (tAtlas A h) Φ g = mInt A (fun i => (Φ i).pullback h h.continuous) (g ∘ h) := by
  first | exact @MongeAmpereTransport.GlobalTheory.CompanionTheory.MaTransport.mInt_tAtlas | exact MongeAmpereTransport.GlobalTheory.CompanionTheory.MaTransport.mInt_tAtlas | (intros; apply MongeAmpereTransport.GlobalTheory.CompanionTheory.MaTransport.mInt_tAtlas <;> assumption)

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralUniformiserActsByDilationTameKernel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralUniformiserActsByDilationTameKernel
set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open Formalism.IndefR.Fin Formalism.IndefR.Fin.LevelGroupLemmas
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BaseCmp

theorem unitOff_mul' {N : ℕ} {u v : ℂ} (hu : GlobalTheory.ConjTwist.UnitOff N u) (hv : GlobalTheory.ConjTwist.UnitOff N v) :
    GlobalTheory.ConjTwist.UnitOff N (u * v) := by
  obtain ⟨hu0, n, h1, h2⟩ := hu
  obtain ⟨hv0, m, h3, h4⟩ := hv
  refine ⟨mul_ne_zero hu0 hv0, n + m, ?_, ?_⟩
  · have e : (N : ℂ) ^ (n + m) * (u * v) = ((N : ℂ) ^ n * u) * ((N : ℂ) ^ m * v) := by ring
    rw [e]; exact h1.mul h3
  · have e : (N : ℂ) ^ (n + m) * (u * v)⁻¹ = ((N : ℂ) ^ n * u⁻¹) * ((N : ℂ) ^ m * v⁻¹) := by
      rw [mul_inv]; ring
    rw [e]; exact h2.mul h4

theorem dilKer_of_ne_zero : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m), VStd D i → ∀ (ξ : Formalism.L2.Host.HChar D.host.E) (χ : (AE D)ˣ →* Circle) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (ω : WeilRep D i) (φ : WO (Vc D i) (Wc D i) → ℂ), KerDat R i ξ χ ξR Q ω φ → (∃ t, Q ⊆ R.Q t) → ∀ N : ℕ, N ≠ 0 → (∀ PP ∈ Q, (N : 𝓞 D.host.E) ∈ PP.asIdeal) → ∀ (eg eQ : AE D) (fg : WO (Vc D i) (Wc D i) → ℂ), IsIdemSum eg R.Pg → IsIdemSum eQ Q → IsTypeVec R i eg fg → ∀ ϖ : 𝓞 D.host.E, (ϖ : D.host.E) ≠ 0 → (∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) → ∀ z : GA D (Vc D i), mt (Vc D i) z = Matrix.diagonal (fun _ => eQ * incA D ((ϖ : D.host.E)⁻¹) + cA D eQ * cA D (incA D (ϖ : D.host.E)) + (1 - eQ - cA D eQ)) → ∃ κ : ℂ, UnitOff N κ ∧ ∀ Tm, IsModel R i eQ fg Tm → ∀ Ψ : WO (Vc D i) (Wc D i) → ℂ, IsSBHalf eQ (lattice₂ R i) Ψ → ω (z, 1) (Tm Ψ) = κ • Tm (fun x => Ψ (dil i (ϖ : D.host.E)⁻¹ x)) := by

  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC hQG i hV ξ χ ξR Q ω φ hK hQt N hN hNQ eg eQ fg heg heQ hfg ϖ hϖ0 hϖ z hz
  obtain ⟨hSV, hSW, hθ, hfix⟩ := GlobalTheory.T.tameKernel_typePlaceThetaVector_latticeFixed D G Pl0 T0 A Ks R F hC hQG i hV ξ χ ξR Q ω φ hK hQt eg eQ fg heg heQ hfg
  have hW := hK.weil
  obtain ⟨hsupp, ⟨x, hx⟩, hpull, hsb, hlat⟩ :=
    GlobalTheory.T.scalarDilationElement_support_det_pullback D (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) Q eQ heQ N hN hNQ ϖ hϖ0 hϖ z hz
  obtain ⟨Rr, hR1, hR2, hR3, hRc⟩ :=
    GlobalTheory.T.exists_conjHalf_cosetReps_scalarDilation D (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) hSV hSW Q eQ heQ N hN hNQ ϖ hϖ0 hϖ z hz
  have hchi := GlobalTheory.T.twisted_splitting_character_unit_off_places D G Pl0 T0 A Ks R F hC hQG i hV ξ χ ξR Q ω φ hK hQt N hN hNQ eQ heQ ϖ hϖ0 hϖ z hz x hx
  refine ⟨((((Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 x : Circle) : ℂ))⁻¹ *
      ((Real.sqrt (Rr.card : ℝ) : ℝ) : ℂ), unitOff_mul' hchi hRc, fun Tm hTm Ψ hΨ => ?_⟩
  have hom := GlobalTheory.T.weilOperator_idempotentSum_vacuum_normalised_sum D R.ψ (Vc D i) (Wc D i) _ _ ω hW (R.ΛV i) (R.ΛW i) hSV hSW Q eQ heQ z x hsupp hx Rr hR1 hR2 hR3
    fg hθ hfix
  have hsum := GlobalTheory.T.sum_heisenbergTranslates_baseVector_eq_card_smul D R.ψ hW.std (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) hSV hSW Q eQ heQ z hlat Rr hR1 hR2 hR3 fg Tm hTm
  have hvac : ω (z, 1) fg = (((((Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 x : Circle) : ℂ))⁻¹ *
      ((Real.sqrt (Rr.card : ℝ) : ℝ) : ℂ)) •
      Tm (actPull (z, (1 : GA D (Wc D i))) (halfInd eQ (latAll (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i)))) := by
    rw [hom, hsum, smul_smul]
    congr 1
    have hs : ((Rr.card : ℕ) : ℂ) = ((Real.sqrt (Rr.card : ℝ) : ℝ) : ℂ) * ((Real.sqrt (Rr.card : ℝ) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]
    rw [hs]
    simp only [splitFacO, map_one, mul_one, Circle.coe_mul, Circle.coe_inv]
    by_cases h0 : ((Real.sqrt (Rr.card : ℝ) : ℝ) : ℂ) = 0
    · rw [h0]; simp
    · field_simp
  have h := GlobalTheory.T.weilRep_apply_eq_smul_of_halfIndicator_base D R.ψ (Vc D i) (Wc D i) _ _ ω hW (R.ΛV i) (R.ΛW i) hSV hSW Q eQ heQ fg hθ hfix Tm hTm (z, 1) _ hsb hvac
    Ψ hΨ
  rw [h, hpull Ψ hΨ.1]

end GlobalTheory.BaseCmp

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralUniformiserActsByDilationTameKernelStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.central_uniformiser_acts_by_dilation_tame_kernel : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m), VStd D i → ∀ (ξ : Formalism.L2.Host.HChar D.host.E) (χ : (AE D)ˣ →* Circle) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (ω : WeilRep D i) (φ : WO (Vc D i) (Wc D i) → ℂ), KerDat R i ξ χ ξR Q ω φ → (∃ t, Q ⊆ R.Q t) → ∀ N : ℕ, N ≠ 0 → (∀ PP ∈ Q, (N : 𝓞 D.host.E) ∈ PP.asIdeal) → ∀ (eg eQ : AE D) (fg : WO (Vc D i) (Wc D i) → ℂ), IsIdemSum eg R.Pg → IsIdemSum eQ Q → IsTypeVec R i eg fg → ∀ ϖ : 𝓞 D.host.E, (ϖ : D.host.E) ≠ 0 → (∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) → ∀ z : GA D (Vc D i), mt (Vc D i) z = Matrix.diagonal (fun _ => eQ * incA D ((ϖ : D.host.E)⁻¹) + cA D eQ * cA D (incA D (ϖ : D.host.E)) + (1 - eQ - cA D eQ)) → ∃ κ : ℂ, UnitOff N κ ∧ ∀ Tm, IsModel R i eQ fg Tm → ∀ Ψ : WO (Vc D i) (Wc D i) → ℂ, IsSBHalf eQ (lattice₂ R i) Ψ → ω (z, 1) (Tm Ψ) = κ • Tm (fun x => Ψ (dil i (ϖ : D.host.E)⁻¹ x)) := by
  first | exact @GlobalTheory.BaseCmp.dilKer_of_ne_zero | exact GlobalTheory.BaseCmp.dilKer_of_ne_zero | (intros; apply GlobalTheory.BaseCmp.dilKer_of_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicThetaReadsCurveThetaFunction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicThetaReadsCurveThetaFunction
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.NormExact.ReadEx

theorem exists_vac_reads : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∃ e0 ∈ Th D (tor0 D cc δ) (stdL D a) (stdL D d), e0 ≠ 0 ∧ ∃ f₀, Reads ψ θ hS hT cc δ r e0 f₀ := GlobalTheory.T.exists_nonzero_standardThetaLine_read_adelic

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {a d : ℕ} {hS : S.rank = a}
  {hT : T.rank = d} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {r : D.host.E}

theorem reads_zero : Reads ψ θ hS hT cc δ r 0 0 :=
  ⟨(GlobalTheory.FinWeilO.thetaSub ψ S T).zero_mem, fun w _ => by simp⟩

theorem reads_sum {k : ℕ} (G : Fin k → VC D a d → ℂ) (f : Fin k → WO S T → ℂ)
    (h : ∀ i, Reads ψ θ hS hT cc δ r (G i) (f i)) : Reads ψ θ hS hT cc δ r (∑ i, G i) (∑ i, f i) := by
  have key : ∀ s : Finset (Fin k), Reads ψ θ hS hT cc δ r (∑ i ∈ s, G i) (∑ i ∈ s, f i) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simpa using (reads_zero : Reads ψ θ hS hT cc δ r 0 0)
    · intro i s hi ih
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact (h i).add ih
  exact key Finset.univ

theorem exists_reads : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ G ∈ TT D (tor0 D cc δ) a d, ∃ f, Reads ψ θ hS hT cc δ r G f := by
  intro D ψ θ S T a d hS hT cc δ r hP G hG
  obtain ⟨e0, he0, hne, f₀, hf₀⟩ := exists_vac_reads ψ θ S T hS hT cc δ r hP
  obtain ⟨k, c, z, rfl⟩ := GlobalTheory.ThetaSpan.theta_span D cc δ hP.crv a d e0 he0 hne G hG
  refine ⟨∑ i, c i • (Formalism.MainNotions.StandardLatticesGL3.wdPh D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z i)) •
    heisO ψ S T (finPt hS hT r (z i)) f₀), reads_sum _ _ fun i => ?_⟩
  have h := ((GlobalTheory.T.heisenbergFinitePoint_reads_classicalTranslation ψ θ S T hS hT cc δ r hP e0 f₀ hf₀ (z i)).smul
    (Formalism.MainNotions.StandardLatticesGL3.wdPh D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z i)))).smul (c i)
  convert h using 2
  ext x
  simp [Formalism.MainNotions.StandardLatticesGL3.Wd]

end GlobalTheory.NormExact.ReadEx
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicThetaReadsCurveThetaFunctionStatement
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelicTheta_reads_curveThetaFunction : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ G ∈ TT D (tor0 D cc δ) a d, ∃ f, Reads ψ θ hS hT cc δ r G f := by
  first | exact @GlobalTheory.NormExact.ReadEx.exists_reads | exact GlobalTheory.NormExact.ReadEx.exists_reads | (intros; apply GlobalTheory.NormExact.ReadEx.exists_reads <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowEqOneOfGeometricPointsTorsion
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowEqOneOfGeometricPointsTorsion
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.TorsGeomPow

theorem pow_eq_one_of_geometric_points : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A →
    ∀ (n : ℕ), IsUnit (n : Γ(S, ⊤)) → ∀ (T : Over S) (x : T ⟶ A), x ^ n = 1 → ∀ d : ℕ,
    (∀ (k : Type) [Field k] [IsAlgClosed k] (ξ : Sp k ⟶ T.left),
      ((Over.homMk ξ rfl : Over.mk (ξ ≫ T.hom) ⟶ T) ≫ x) ^ d = 1) → x ^ d = 1 := by
  intro S A _ hA n hn T x hx d hpt
  obtain ⟨-, -, hZe⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion A (hG := hA) hn
  set P : Over S := pullback (mulN A n) (η : 𝟙_ (Over S) ⟶ A) with hP
  have hPe : Etale P.hom := hZe
  have hxd : (x ^ d) ≫ mulN A n = toUnit T ≫ (η : 𝟙_ (Over S) ⟶ A) := by
    rw [GlobalTheory.GrpTangent.comp_mulN, ← pow_mul, mul_comm, pow_mul, hx, one_pow, CategoryTheory.Hom.one_def]
  have h1 : (1 : T ⟶ A) ≫ mulN A n = toUnit T ≫ (η : 𝟙_ (Over S) ⟶ A) := by
    rw [GlobalTheory.GrpTangent.comp_mulN, one_pow, CategoryTheory.Hom.one_def]
  let y₁ : T ⟶ P := pullback.lift (x ^ d) (toUnit T) hxd
  let u₁ : T ⟶ P := pullback.lift 1 (toUnit T) h1
  have hy : y₁ ≫ pullback.fst (mulN A n) (η : 𝟙_ (Over S) ⟶ A) = x ^ d := pullback.lift_fst _ _ _
  have hu : u₁ ≫ pullback.fst (mulN A n) (η : 𝟙_ (Over S) ⟶ A) = 1 := pullback.lift_fst _ _ _
  have key : ∀ {W : Over S} (f : W ⟶ T), (f ≫ x) ^ d = 1 → f ≫ y₁ = f ≫ u₁ := by
    intro W f hf
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, hy, hu, MonObj.comp_pow, hf, MonObj.comp_one]
    · rw [Category.assoc, Category.assoc, pullback.lift_snd, pullback.lift_snd]
  have hyu : y₁ = u₁ := by
    haveI := hPe
    have hw : y₁.left ≫ P.hom = u₁.left ≫ P.hom := by rw [Over.w, Over.w]
    let l : T.left ⟶ pullback P.hom P.hom := pullback.lift _ _ hw
    have hl1 : l ≫ pullback.fst _ _ = y₁.left := pullback.lift_fst _ _ _
    have hl2 : l ≫ pullback.snd _ _ = u₁.left := pullback.lift_snd _ _ _
    have hs : Function.Surjective (pullback.snd (pullback.diagonal P.hom) l) := by
      intro s
      let k := AlgebraicClosure (T.left.residueField s)
      let ξ : Sp k ⟶ T.left :=
        Spec.map (CommRingCat.ofHom (algebraMap (T.left.residueField s) k)) ≫ T.left.fromSpecResidueField s
      have hξ : ξ ≫ y₁.left = ξ ≫ u₁.left :=
        congrArg CommaMorphism.left (key (Over.homMk ξ rfl : Over.mk (ξ ≫ T.hom) ⟶ T) (hpt k ξ))
      have hq : (ξ ≫ y₁.left) ≫ pullback.diagonal P.hom = ξ ≫ l := by
        apply pullback.hom_ext
        · simp only [Category.assoc]
          rw [pullback.diagonal_fst, Category.comp_id, hl1]
        · simp only [Category.assoc]
          rw [pullback.diagonal_snd, Category.comp_id, hl2, hξ]
      refine ⟨pullback.lift _ _ hq (IsLocalRing.closedPoint k), ?_⟩
      have e : (pullback.lift _ _ hq ≫ pullback.snd (pullback.diagonal P.hom) l) (IsLocalRing.closedPoint k) =
          ξ (IsLocalRing.closedPoint k) := by rw [Limits.pullback.lift_snd]
      refine (Eq.trans ?_ e).trans ?_
      · rfl
      exact (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply s _)
    have : Epi (pullback.snd (pullback.diagonal P.hom) l).base :=
      (TopCat.epi_iff_surjective _).2 hs
    have : IsIso (pullback.snd (pullback.diagonal P.hom) l) := IsOpenImmersion.isIso _
    have hl : l = inv (pullback.snd (pullback.diagonal P.hom) l) ≫ pullback.fst _ _ ≫
        pullback.diagonal P.hom := by
      rw [pullback.condition, IsIso.inv_hom_id_assoc]
    apply Over.OverMorphism.ext
    rw [← hl1, ← hl2, hl]
    simp
  rw [← hy, hyu, hu]

end GlobalTheory.TorsGeomPow
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowEqOneOfGeometricPointsTorsionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pow_eq_one_of_geometric_points_torsion : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (n : ℕ), IsUnit (n : Γ(S, ⊤)) → ∀ (T : Over S) (x : T ⟶ A), x ^ n = 1 → ∀ d : ℕ, (∀ (k : Type) [Field k] [IsAlgClosed k] (ξ : Sp k ⟶ T.left), ((Over.homMk ξ rfl : Over.mk (ξ ≫ T.hom) ⟶ T) ≫ x) ^ d = 1) → x ^ d = 1 := by
  first | (exact @GlobalTheory.TorsGeomPow.pow_eq_one_of_geometric_points) | (exact GlobalTheory.TorsGeomPow.pow_eq_one_of_geometric_points) | (intros; apply GlobalTheory.TorsGeomPow.pow_eq_one_of_geometric_points  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegralArchimedeanInvariant
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ThetaRightTranslate

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cA_eq_sigR (σ : E →ₐ[F] E) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) : cA σ z = sigR (AF F) σ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [cA, sigR]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem ug_eq_uj (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    UG (cA σ) (incM F J) = Formalism.UG.UJ (sigR (AF F) σ) (JR (AF F) Jᵀ) := by
  ext g
  show (g : Matrix _ _ _)ᵀ * incM F J * (g : Matrix _ _ _).map (cA σ) = incM F J ↔
    Formalism.UG.cT (sigR (AF F) σ) (g : Matrix _ _ _) * JR (AF F) Jᵀ * (g : Matrix _ _ _) = JR (AF F) Jᵀ
  have hc : (g : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))).map (cA σ) = (g : Matrix _ _ _).map (sigR (AF F) σ) := by
    ext i j; exact cA_eq_sigR σ _
  have hJ : JR (AF F) Jᵀ = (incM F J)ᵀ := rfl
  rw [hc, hJ, Formalism.UG.cT]
  constructor
  · intro h
    have := congrArg Matrix.transpose h
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
  · intro h
    have := congrArg Matrix.transpose h
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this

def toHA (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : UA σ J ≃ₜ* HA (AF F) σ Jᵀ where
  toMulEquiv := MulEquiv.subgroupCongr (ug_eq_uj σ J)
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

theorem isMulRightInvariant_of_equiv {G H : Type} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup G] [IsTopologicalGroup H]
    [MeasurableSpace G] [MeasurableSpace H] [BorelSpace G] [BorelSpace H]
    (e : G ≃ₜ* H) (μ : Measure G) (h : (μ.map e).IsMulRightInvariant) :
    μ.IsMulRightInvariant := by
  have he : Measurable e := e.continuous.measurable
  have hs : Measurable e.symm := e.symm.continuous.measurable
  have hμ : μ = (μ.map e).map e.symm := by
    rw [Measure.map_map hs he]
    have : (e.symm : H → G) ∘ e = id := by ext x; simp
    rw [this, Measure.map_id]
  refine ⟨fun g => ?_⟩
  have h1 := h.map_mul_right_eq_self (e g)
  have hc : (fun x : G => x * g) ∘ (e.symm : H → G) = (e.symm : H → G) ∘ (fun y : H => y * e g) := by
    ext y; simp
  conv_lhs => rw [hμ]
  rw [Measure.map_map (measurable_mul_const g) hs, hc,
    ← Measure.map_map hs (measurable_mul_const _), h1, ← hμ]

theorem isMulRightInvariant (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (hd : IsUnit J.det) (μ : Measure (UA σ J)) [μ.IsHaarMeasure] :
    μ.IsMulRightInvariant := by
  haveI : IsTopologicalRing (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : BorelSpace (UA σ J) := ⟨rfl⟩
  haveI : IsTopologicalGroup (HA (AF F) σ Jᵀ) := inferInstanceAs (IsTopologicalGroup (HR (AF F) σ Jᵀ))
  haveI : BorelSpace (HA (AF F) σ Jᵀ) := ⟨rfl⟩
  refine isMulRightInvariant_of_equiv (toHA σ J) μ ?_
  haveI : (μ.map (toHA σ J)).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map μ (toHA σ J)
  obtain ⟨d, hd'⟩ := GlobalTheory.HermLineZeros.exists_conj_ne hcm
  have hss := GlobalTheory.HermLineZeros.conj_invol hcm
  have hJ' : IsHermND σ Jᵀ := ⟨fun i j => hJ j i, by rw [Matrix.det_transpose]; exact hd.ne_zero⟩
  exact @GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_adelic F E _ _ _ _ _ σ hss (σ d - d) (sub_ne_zero.2 hd')
    (by rw [map_sub, hss]; abel) n Jᵀ hJ' (μ.map (toHA σ J)) this

theorem countable_subgroupOf_range {G H : Type} [Group G] [Group H] [Countable G] (f : G →* H)
    (K : Subgroup H) : Countable ((f.range).subgroupOf K) := by
  have hc : (Set.range f).Countable := Set.countable_range f
  haveI := hc.to_subtype
  refine Function.Injective.countable (f := fun γ : (f.range).subgroupOf K =>
    (⟨γ.1.1, MonoidHom.mem_range.1 (Subgroup.mem_subgroupOf.1 γ.2)⟩ : Set.range f)) ?_
  intro a b hab
  exact Subtype.ext (Subtype.ext (Subtype.mk.inj hab))

theorem countable_ratU (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Countable (ratU σ J) := by
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin n) (Fin n) E) := inferInstanceAs (Countable (Fin n → Fin n → E))
  haveI : Countable (GL (Fin n) E) := Function.Injective.countable (f := (Units.val : GL (Fin n) E → Matrix (Fin n) (Fin n) E)) (fun a b h => Units.ext h)
  unfold ratU
  exact countable_subgroupOf_range _ _

end GlobalTheory.ThetaRightTranslate
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogDerivationExtensionBasicOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogDerivationExtensionBasicOpen
noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LogDerLoc

def dualHom {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (D : Derivation ℤ A A) :
    A →+* TrivSqZeroExt B B where
  toFun r := TrivSqZeroExt.inl (φ r) + TrivSqZeroExt.inr (φ (D r))
  map_one' := by ext <;> simp
  map_mul' x y := by
    ext
    · simp
    · simp [D.leibniz, mul_comm, -DualNumber.inr_eq_smul_eps]
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp [-DualNumber.inr_eq_smul_eps]

theorem exists_extension {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (f : A) [IsLocalization.Away f B]
    (D : Derivation ℤ A A) : ∃ E : Derivation ℤ B B, ∀ r, E (algebraMap A B r) = algebraMap A B (D r) := by
  have hu : IsUnit (dualHom (algebraMap A B) D f) :=
    TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (by
      simpa [dualHom] using IsLocalization.Away.algebraMap_isUnit (S := B) f)
  let L : B →+* TrivSqZeroExt B B := IsLocalization.Away.lift f hu
  have hfst : ∀ x, (L x).fst = x := fun x => by
    have : (TrivSqZeroExt.fstHom B _ _).toRingHom.comp L = RingHom.id _ := by
      refine IsLocalization.ringHom_ext (Submonoid.powers f) (RingHom.ext fun r => ?_)
      simp [L, dualHom]
    exact congr($this x)
  let e : B →+ B :=
    { toFun := fun x => (L x).snd
      map_zero' := by rw [map_zero, TrivSqZeroExt.snd_zero]
      map_add' := fun x y => by rw [map_add (f := _), TrivSqZeroExt.snd_add] }
  refine ⟨Derivation.mk' e.toIntLinearMap fun x y => ?_, fun r => ?_⟩
  · change (L (x * y)).snd = x • (L y).snd + y • (L x).snd
    rw [map_mul, TrivSqZeroExt.snd_mul, hfst, hfst]
    simp [mul_comm]
  · change (L (algebraMap A B r)).snd = _
    simp [L, dualHom, -DualNumber.inr_eq_smul_eps]

theorem map_mem_map {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (D : Derivation ℤ A A)
    (E : Derivation ℤ B B) (h : ∀ r, E (φ r) = φ (D r)) (J : Ideal A) (hJ : ∀ g ∈ J, D g ∈ J) :
    ∀ x ∈ J.map φ, E x ∈ J.map φ := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, hg, rfl⟩ := hx
    rw [h]
    exact Ideal.mem_map_of_mem φ (hJ g hg)
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x hx hE =>
    rw [smul_eq_mul, E.leibniz, smul_eq_mul, smul_eq_mul]
    exact add_mem (Ideal.mul_mem_left _ a hE) (Ideal.mul_mem_right _ _ hx)

theorem exists_logDer_basicOpen : ∀ (X : Scheme.{0}) (K : Type) [CommRing K] (s : X ⟶ Sp K) (I : X.IdealSheafData) (U W : X.affineOpens) (hW : W.1 ≤ U.1) (f : Γ(X, U.1)), W.1 = X.basicOpen f → ∀ Dl ∈ GlobalTheory.LogKS.logDer s I U, ∃ DlW ∈ GlobalTheory.LogKS.logDer s I W, ∀ r, DlW ((X.presheaf.map (homOfLE hW).op).hom r) = (X.presheaf.map (homOfLE hW).op).hom (Dl r) := by
  intro X K _ s I U W hW f hf Dl hD
  obtain rfl : W = X.affineBasicOpen f := Subtype.ext hf
  haveI : IsLocalization.Away f Γ(X, X.basicOpen f) := U.2.isLocalization_basicOpen f
  obtain ⟨E, hE⟩ := exists_extension (B := Γ(X, X.basicOpen f)) f Dl
  have hE' : ∀ r, E ((X.presheaf.map (homOfLE hW).op).hom r) = (X.presheaf.map (homOfLE hW).op).hom (Dl r) := hE
  refine ⟨E, ⟨fun a => ?_, ?_⟩, hE'⟩
  · have hc : (X.presheaf.map (homOfLE hW).op).hom (constFn s U.1 a) = constFn s (X.affineBasicOpen f).1 a := by
      exact congr(($(Scheme.Hom.appLE_map s (U := ⊤) (V := U.1) (fun _ _ => trivial) (homOfLE hW).op)).hom
        ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a))
    have := hE' (constFn s U.1 a)
    rw [hc, hD.1 a, map_zero] at this
    exact this
  · rw [← I.map_ideal_basicOpen U f]
    exact map_mem_map _ Dl E hE' _ hD.2

end GlobalTheory.LogDerLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogDerivationExtensionBasicOpenStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_logDerivation_extension_basicOpen : ∀ (X : Scheme.{0}) (K : Type) [CommRing K] (s : X ⟶ Sp K) (I : X.IdealSheafData) (U W : X.affineOpens) (hW : W.1 ≤ U.1) (f : Γ(X, U.1)), W.1 = X.basicOpen f → ∀ Dl ∈ GlobalTheory.LogKS.logDer s I U, ∃ DlW ∈ GlobalTheory.LogKS.logDer s I W, ∀ r, DlW ((X.presheaf.map (homOfLE hW).op).hom r) = (X.presheaf.map (homOfLE hW).op).hom (Dl r) := by
  first | exact @GlobalTheory.LogDerLoc.exists_logDer_basicOpen | exact GlobalTheory.LogDerLoc.exists_logDer_basicOpen | (intros; apply GlobalTheory.LogDerLoc.exists_logDer_basicOpen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentCombinationPreservedByBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentCombinationPreservedByBaseChange
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TanBaseChange

open MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

theorem spMap_comp_spMap' {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R' →+* R'')
    (g : R →+* R') : spMap f ≫ spMap g = spMap (f.comp g) := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

theorem dualMap_comp_algebraMap {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) :
    (Formalism.L2.Pj.dualMap ψ).comp (algebraMap S (DualNumber S)) = (algebraMap T (DualNumber T)).comp ψ := by
  ext s <;> simp [Formalism.L2.Pj.dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem fstHom_comp_dualMap {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) :
    (TrivSqZeroExt.fstHom T T T).toRingHom.comp (Formalism.L2.Pj.dualMap ψ) =
      ψ.comp (TrivSqZeroExt.fstHom S S S).toRingHom := by
  ext s <;> simp [Formalism.L2.Pj.dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem dualMap_comp_epsMul' {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (a : S) :
    (Formalism.L2.Pj.dualMap ψ).comp (epsMul a) = (epsMul (ψ a)).comp (Formalism.L2.Pj.dualMap ψ) := by
  ext s <;> simp [Formalism.L2.Pj.dualMap, epsMul, TrivSqZeroExt.algebraMap_eq_inl]

theorem list_prod_comp' {X0 : Scheme.{0}} {G : Over X0} [MonObj G] {T T' : Over X0} (f : T' ⟶ T)
    (L : List (T ⟶ G)) : (L.map (f ≫ ·)).prod = f ≫ L.prod := by
  induction L with
  | nil => simp [Hom.one_def]
  | cons a L ih => simp only [List.map_cons, List.prod_cons, ih, Hom.mul_def, comp_lift_assoc]

theorem tan_comb_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S') (x : Sp S ⟶ X) (x' : Sp S' ⟶ X), spMap φ ≫ x = x' → (∀ v : Sp (DualNumber S) ⟶ t.G.left, IsTanAtG t x v → IsTanAtG t x' (spMap (dualMap φ) ≫ v)) ∧ ∀ (m : ℕ) (v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)) (cf : Fin m → S) (w : Sp (DualNumber S) ⟶ t.G.left), IsCombAtG t x v cf w → IsCombAtG t x' (fun i => spMap (dualMap φ) ≫ v i) (fun i => φ (cf i)) (spMap (dualMap φ) ≫ w) := by
  intro E _ _ _ H X t S S' _ _ φ x x' hx
  subst hx
  refine ⟨fun v hv => ?_, fun m v cf w h => ?_⟩
  · obtain ⟨h1, h2⟩ := hv
    refine ⟨?_, ?_⟩
    · rw [Category.assoc, h1, ← Category.assoc, spMap_comp_spMap', dualMap_comp_algebraMap, ← spMap_comp_spMap',
        Category.assoc]
    · rw [← Category.assoc, spMap_comp_spMap', fstHom_comp_dualMap, ← spMap_comp_spMap', Category.assoc, h2]
      have e : (Over.homMk (spMap φ) rfl : Over.mk (spMap φ ≫ x) ⟶ Over.mk x) ≫ (1 : Over.mk x ⟶ t.G) = 1 := by
        simp [Hom.one_def]
      rw [← e, Over.comp_left]
      rfl
  · obtain ⟨u, hu, hp⟩ := h
    let q : tEpsG (spMap φ ≫ x) ⟶ tEpsG x := Over.homMk (spMap (Formalism.L2.Pj.dualMap φ)) (by
      show spMap (Formalism.L2.Pj.dualMap φ) ≫ spMap (algebraMap S (DualNumber S)) ≫ x =
        spMap (algebraMap S' (DualNumber S')) ≫ spMap φ ≫ x
      rw [← Category.assoc, ← Category.assoc, spMap_comp_spMap', spMap_comp_spMap', dualMap_comp_algebraMap])
    refine ⟨fun i => q ≫ u i, fun i => ?_, ?_⟩
    · show spMap (Formalism.L2.Pj.dualMap φ) ≫ (u i).left = _
      rw [hu i, ← Category.assoc, spMap_comp_spMap', dualMap_comp_epsMul', ← spMap_comp_spMap', Category.assoc]
    · have e : List.ofFn (fun i => q ≫ u i) = (List.ofFn u).map (q ≫ ·) := by
        rw [List.map_ofFn]
        rfl
      rw [e, list_prod_comp', Over.comp_left, hp]
      rfl

end GlobalTheory.TanBaseChange
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentCombinationPreservedByBaseChangeStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_combination_preserved_by_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S') (x : Sp S ⟶ X) (x' : Sp S' ⟶ X), spMap φ ≫ x = x' → (∀ v : Sp (DualNumber S) ⟶ t.G.left, IsTanAtG t x v → IsTanAtG t x' (spMap (dualMap φ) ≫ v)) ∧ ∀ (m : ℕ) (v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)) (cf : Fin m → S) (w : Sp (DualNumber S) ⟶ t.G.left), IsCombAtG t x v cf w → IsCombAtG t x' (fun i => spMap (dualMap φ) ≫ v i) (fun i => φ (cf i)) (spMap (dualMap φ) ≫ w) := by
  first | exact @GlobalTheory.TanBaseChange.tan_comb_baseChange | exact GlobalTheory.TanBaseChange.tan_comb_baseChange | (intros; apply GlobalTheory.TanBaseChange.tan_comb_baseChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogTarget
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section

namespace GlobalTheory.UPel.HT.ES.CorrQF

def IsogTarget {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    (M : Model b N) (c : ℕ) {L : Type} [Field L] (ξ ζ : Sp L ⟶ M.X) : Prop :=
  ξ ≫ M.s = ζ ≫ M.s ∧ ∃ (o o' : Obj b N (ξ ≫ M.s)) (ψ : o.A ⟶ o'.A),
    Nonempty (ObjMap o M.univ ξ) ∧ Nonempty (ObjMap o' M.univ ζ) ∧ IsPIsog c o o' ψ

end GlobalTheory.UPel.HT.ES.CorrQF
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentFrameBaseChange
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel.LiftBC

theorem isCombAtG_unique {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}}
    (t : SAB H X) {S : Type} [CommRing S] {x : Sp S ⟶ X} {m : ℕ} {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)}
    {a : Fin m → S} {w₁ w₂ : Sp (DualNumber S) ⟶ t.G.left} (h₁ : IsCombAtG t x v a w₁) (h₂ : IsCombAtG t x v a w₂) :
    w₁ = w₂ := by
  obtain ⟨u₁, hu₁, hw₁⟩ := h₁
  obtain ⟨u₂, hu₂, hw₂⟩ := h₂
  have hu : u₁ = u₂ := funext fun i => Over.OverMorphism.ext ((hu₁ i).trans (hu₂ i).symm)
  rw [← hw₁, ← hw₂, hu]

end GlobalTheory.FlatModel.LiftBC
end
