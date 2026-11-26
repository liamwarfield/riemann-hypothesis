module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSectionOfChg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsLiftPt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneFormMapRowThreeLevelOfCharacterisation

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteOpenImmersionPSpace
namespace GlobalTheory.ZMain

open CategoryTheory AlgebraicGeometry TopologicalSpace

theorem finite_integralClosure_field (R L : Type*) [CommRing R] [Algebra.FiniteType ℤ R] [Field L]
    [Algebra R L] [Algebra.EssFiniteType R L] : Module.Finite R (integralClosure R L) := by
  rcases CharP.char_is_prime_or_zero L (ringChar L) with hp | h0
  · let p := ringChar L
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : CharP L p := ringChar.charP L
    let I := RingHom.ker (algebraMap R L)
    let R' := R ⧸ I
    letI : Algebra R' L := (Ideal.Quotient.lift I (algebraMap R L) fun _ h => h).toAlgebra
    haveI : IsScalarTower R R' L := .of_algebraMap_eq fun _ => rfl
    have hinj : Function.Injective (algebraMap R' L) := by
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro a ha
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
    haveI : IsDomain R' := hinj.isDomain _
    haveI : FaithfulSMul R' L := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
    haveI : CharP R' p := ⟨fun n => by
      rw [← map_eq_zero_iff _ hinj, map_natCast, CharP.cast_eq_zero_iff L]⟩
    letI : Algebra (ZMod p) R' := (ZMod.castHom dvd_rfl R').toAlgebra
    haveI : Algebra.FiniteType ℤ R' := .trans (S := R) inferInstance inferInstance
    haveI : Algebra.FiniteType (ZMod p) R' := .of_restrictScalars_finiteType ℤ (ZMod p) R'
    haveI : IsNoetherianRing R' := Algebra.FiniteType.isNoetherianRing (ZMod p) R'
    haveI : Module.Finite R R' := Module.Finite.of_surjective (Algebra.linearMap R R')
      Ideal.Quotient.mk_surjective
    let F := FractionRing R'
    letI : Algebra F L := FractionRing.liftAlgebra R' L
    haveI : Algebra.EssFiniteType R' L := .of_comp R R' L
    haveI : Algebra.EssFiniteType F L := .of_comp R' F L
    let E := algebraicClosure F L
    haveI : FiniteDimensional F E := finiteDimensional_algebraicClosure_of_essFiniteType F L
    haveI : Module.Finite R' (integralClosure R' E) :=
      NormFin.finite_integralClosure_of_perfectField (ZMod p) R' F E
    haveI : IsScalarTower R' E L := .of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply R' F L x, IsScalarTower.algebraMap_apply R' F E x,
        ← IsScalarTower.algebraMap_apply F E L]
    have hmem : ∀ z : integralClosure R' L, (z : L) ∈ E := fun z =>
      mem_algebraicClosure_iff.mpr (z.2.tower_top (A := F)).isAlgebraic
    let ψ : integralClosure R' L →ₗ[R'] integralClosure R' E :=
      { toFun := fun z => ⟨⟨z, hmem z⟩, (isIntegral_algHom_iff (IsScalarTower.toAlgHom R' E L)
            (IsScalarTower.toAlgHom R' E L).toRingHom.injective).mp z.2⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    haveI : Module.Finite R' (integralClosure R' L) := Module.Finite.of_injective ψ
      fun a b h => Subtype.ext (congrArg (fun w : integralClosure R' E => ((w : E) : L)) h)
    exact finite_integralClosure_of_finite_tower R R' L
  · haveI : CharZero L := (CharP.ringChar_zero_iff_CharZero L).mp h0
    exact finite_integralClosure_of_essFiniteType_field ℤ R L

universe u

theorem isFinite_fromNormalization_int {X Y : Scheme.{u}} {o : CommRingCat.{u}}
    [Algebra.FiniteType ℤ o] (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] (g : Y ⟶ Spec o)
    [LocallyOfFiniteType g] [IsIntegral X]
    (hess : (f.residueFieldMap (genericPoint X)).hom.EssFiniteType) :
    IsFinite f.fromNormalization := by
  refine ⟨fun U hU => ?_⟩
  letI := (f.app U).hom.toAlgebra
  letI : Algebra o Γ(Y, U) := ((Scheme.ΓSpecIso o).inv ≫ g.appLE ⊤ U le_top).hom.toAlgebra
  haveI : Algebra.FiniteType o Γ(Y, U) :=
    (g.finiteType_appLE (isAffineOpen_top _) hU le_top).comp
      (.of_surjective _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso o).inv).2)
  haveI : Algebra.FiniteType ℤ Γ(Y, U) := .trans (S := o) inferInstance inferInstance
  haveI : IsNoetherianRing Γ(Y, U) := Algebra.FiniteType.isNoetherianRing ℤ _
  let D : Set X := {genericPoint X}
  have hD : Dense D := dense_iff_closure_eq.mpr (genericPoint_spec X)
  let ι := ↥(D ∩ (f ⁻¹ᵁ U : X.Opens))
  haveI : Finite ι := ((Set.finite_singleton _).inter_of_left _).to_subtype
  letI (x : ι) : Algebra Γ(Y, U) (X.residueField x.1) :=
    (f.app U ≫ X.evaluation (f ⁻¹ᵁ U) x.1 x.2.2).hom.toAlgebra
  haveI (x : ι) : Algebra.EssFiniteType Γ(Y, U) (X.residueField x.1) := by
    change (f.app U ≫ X.evaluation (f ⁻¹ᵁ U) x.1 x.2.2).hom.EssFiniteType
    rw [← Scheme.evaluation_naturality f (V := U) x.1 x.2.2]
    have hx : x.1 = genericPoint X := x.2.1
    exact .comp (.comp (essFiniteType_germ hU (f x.1) x.2.2)
      (RingHom.FiniteType.of_surjective _ (Y.residue_surjective _)).essFiniteType)
      (by rw [hx] at *; exact hess)
  haveI (x : ι) := finite_integralClosure_field Γ(Y, U) (X.residueField x.1)
  haveI : Module.Finite Γ(Y, U) (integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U)) := by
    refine finite_integralClosure_of_family (L := fun x : ι => X.residueField x.1)
      (fun x => { (X.evaluation (f ⁻¹ᵁ U) x.1 x.2.2).hom with commutes' := fun _ => rfl })
      fun b hb => ?_
    rw [← basicOpen_eq_bot_iff, eq_bot_iff]
    intro y hy
    obtain ⟨x, hx, hxD⟩ := hD.inter_open_nonempty _ (X.basicOpen b).isOpen ⟨y, hy⟩
    exact ((X.evaluation_eq_zero_iff_notMem_basicOpen x (X.basicOpen_le b hx) b).mp
      (hb ⟨x, hxD, X.basicOpen_le b hx⟩) hx).elim
  rw [f.fromNormalization_app hU]
  exact RingHom.Finite.comp
    (.of_surjective _ (ConcreteCategory.bijective_of_isIso (f.normalizationObjIso hU).inv).2)
    (RingHom.finite_algebraMap.mpr this)


open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor in
theorem exists_finite_openImmersion_pSpace : ∀ (o : Type) [CommRing o] [IsNoetherianRing o]
    [Algebra.FiniteType ℤ o] (m : ℕ) (X : Scheme.{0}) (f : X ⟶ PSpace o m), IsIntegral X →
    Geo.Tor.IsNormalScheme X → LocallyOfFiniteType f → QuasiCompact f → IsSeparated f →
    LocallyQuasiFinite f → ∃ (Z : Scheme.{0}) (z : Z ⟶ PSpace o m) (i : X ⟶ Z), IsFinite z ∧
      IsOpenImmersion i ∧ i ≫ z = f ∧ Geo.Tor.IsNormalScheme Z ∧ IsIntegral Z ∧
      Dense (Set.range i) := by
  intro o _ _ _ m X f hX hN _ _ _ _
  haveI : Algebra.FiniteType ℤ (CommRingCat.of o) := ‹Algebra.FiniteType ℤ o›
  haveI := isProper_str o m
  haveI : GlobalTheory.IsNormalScheme X := GlobalTheory.IsNormalScheme.of_pred hN
  refine ⟨f.normalization, f.fromNormalization, f.toNormalization,
    isFinite_fromNormalization_int f (PSpace.str o m)
      (LocallyOfFiniteType.stalkMap f _).residueFieldMap,
    inferInstance, f.toNormalization_fromNormalization,
    (GlobalTheory.IsNormalScheme.normalization_of_isIntegral f).pred _, inferInstance,
    (inferInstance : IsDominant f.toNormalization).denseRange⟩

end GlobalTheory.ZMain
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatThetaQuotientAtPrincipalLevelProof
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatThetaQuotientAtPrincipalLevelProof
set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BaseCmp

open GlobalTheory.PlaceModel


open Classical in
theorem resC_eq_of_kerDat {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m}
    {ξ : Formalism.L2.Host.HChar D.host.E} {χ : (AE D)ˣ →* Circle} {ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ}
    {ω : WeilRep D i} {φ : WO (Vc D i) (Wc D i) → ℂ} {B : Base (Vc D i) (Wc D i)} (hB : B.Good)
    (hK : KerDat R i ξ χ ξR B.de.Q ω φ) (hc : ChrEq B.de.chi ξ) {PP : Pl D.host.E} (hPP : PP ∈ B.de.Q) :
    ξR PP = B.de.resC PP := by
  refine MonoidHom.ext fun u => Units.ext ?_
  obtain ⟨x, hx⟩ := exists_isLocUnit (hB.de.split.isIdemAt hPP) u
  obtain ⟨k1, k2⟩ := hx.res
  have e1 := eq_res_of_chrEq hc (hB.de.split.isIdemAt hPP) (hK.tame PP) (hK.res PP hPP) x hx.off k1 u k2
  have e2 := hx.eq (hB.de.res PP hPP)
  rw [← e1, e2]
  rfl


open Classical in
theorem omegaFlat_eq_locFn_empty {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m}
    {ξ : Formalism.L2.Host.HChar D.host.E} {χ : (AE D)ˣ →* Circle} {ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ}
    {ω : WeilRep D i} {φ : WO (Vc D i) (Wc D i) → ℂ} {B : Base (Vc D i) (Wc D i)} (hB : B.Good)
    (hK : KerDat R i ξ χ ξR B.de.Q ω φ) (hc : ChrEq B.de.chi ξ) (y : Reds D (Wc D i).rank (Vc D i).rank) :
    omegaFlat B.de.Q (Wc D i).rank ξR y = (GlobalTheory.FlatVecSum.princ B).locFn ∅ (fun _ _ => 1) y := by
  rw [GlobalTheory.FlatVecSum.omegaFlat_eq_prod, Base.locFn]
  simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one]
  exact Finset.prod_congr rfl fun PP hP => by rw [resC_eq_of_kerDat hB hK hc hP]; rfl


open Classical in
theorem flatTwoStep_holds : FlatTwoStep := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i ξ χ ξR ω φ B hB h hK hc
  obtain ⟨hvac, e, he, -⟩ := hK.vec
  have hψ := hvac.1
  have sV : IsSelfDualC (Vc D i) (R.ΛV i) :=
    GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hR.lev.βV i))
  have sW : IsSelfDualC (Wc D i) (R.ΛW i) :=
    GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hR.lev.βW i))
  have fV := Formalism.IndefR.Fin.PDA.selfDual_isFullLattice (Vc D i) (R.ΛV i) sV
  have fW := Formalism.IndefR.Fin.PDA.selfDual_isFullLattice (Wc D i) (R.ΛW i) sW
  have hdisj : Disjoint R.Pg B.de.Q := h.Pg ▸ hB.places.disj
  obtain ⟨eg, eQ, hg, hq, h1, h2, h3⟩ := GlobalTheory.FlatVecExist.idemSum_split he hdisj
  have hinfg := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart hg)
  obtain ⟨fg, hfg⟩ := GlobalTheory.PlaceVec.exists_isThetaAt hψ sV sW (a := cA D eg)
    (by rw [← RingHom.map_mul, GlobalTheory.PlaceVec.idemSum_mul_self hg]) hinfg
    (GlobalTheory.PlaceModelSum.placeModelExistsSum D R.ψ hψ _ _ _ _ sV sW _ eg hg _ hvac.2.theta hvac.2.lat).2
    (GlobalTheory.PlaceVec.isSBHalf_of_red fV fW hinfg (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i))
      (GlobalTheory.PlaceVec.frMapAdj_add _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_up _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_down _ _ _ _) R.Pg
      (fun y => omegaK R.Pg y) fun y y' h => GlobalTheory.PlaceVec.omegaK_congr R.Pg h)
  have hoQ := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum hq
  have fix : ∀ u, (∀ a b, cA D eg * u a b = 0 ∧ eg * u a b = 0) →
      heisO R.ψ (Vc D i) (Wc D i) u (R.vacP i) = R.vacP i → heisO R.ψ (Vc D i) (Wc D i) u fg = fg :=
    fun u hu h0 => GlobalTheory.Hk3.heisO_fix_thetaAt_off R.ψ _ _ (cA D eg) _ 1 _ _ fg hfg u
      (fun a b => by rw [GlobalTheory.DualPairCheck.cA_cA]; exact hu a b) h0
  have hPM := GlobalTheory.FlatVecExist.exists_model_of_fix hψ sV sW hoQ hq.2
    (fun u hu => fix u (fun a b => (GlobalTheory.FlatVecExist.off_of_half h1 (by rw [mul_comm, h3])
        ((isHalf_iff _ _).2 hu.2) a b).symm)
      (hoQ.heisO_eq (by rw [mul_comm, hq.2]) hvac.2.lat u hu))
    (fun u hu => fix u (fun a b => (GlobalTheory.FlatVecExist.off_of_half h2
        (by rw [← RingHom.map_mul, h1, map_zero]) ((isHalf_iff _ _).2 hu.2) a b).symm)
      (hoQ.conj.heisO_eq (by rw [GlobalTheory.DualPairCheck.cA_cA, hq.2]) hvac.2.lat u hu))
  have hinfQ := GlobalTheory.PlaceDatum.infPart_idemSum hq
  obtain ⟨K, hK', hC⟩ := GlobalTheory.PlaceDatum.exists_nsmul_of_frMapO fV fW (R.βV i) (R.βW i)
  obtain ⟨f, hf⟩ := GlobalTheory.PlaceDatum.exists_isThetaAt hψ sV sW (GlobalTheory.PlaceDatum.idemSum_mul_self hq) hinfQ hPM
    (GlobalTheory.PlaceDatum.isSBHalf_of_red eQ _ (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i)) (GlobalTheory.PlaceDatum.frMapO_add _ _)
      (GlobalTheory.PlaceDatum.exists_den_frMapO sV.1.fg sW.1.fg _ _)
      ⟨K, hK', fun x hx => hC x (GlobalTheory.PlaceDatum.infPart_of_half hinfQ hx)⟩ B.de.Q
      (fun y => GlobalTheory.ConjTwist.omegaFlat B.de.Q (Wc D i).rank ξR y) fun y y' h => GlobalTheory.FlatVecExist.omegaFlat_congr _ _ _ h)
  have hfeq : f = (GlobalTheory.FlatVecSum.princ B).vecBase := by
    have k1 := hfg
    have k2 := hf
    simp only [omegaFlat_eq_locFn_empty hB hK hc] at k2
    rw [← idem_eq hg] at k1
    rw [← idem_eq hq] at k2
    rw [← h.ψ, ← h.ΛS, ← h.ΛT, ← h.βS, ← h.βT] at k1 k2
    rw [← h.vac, ← h.Pg] at k1
    unfold Base.vecBase Base.vecAt
    rw [Finset.union_empty]
    refine GlobalTheory.FlatVecSum.eq_vec_of_two_steps (G := GlobalTheory.FlatVecSum.princG B.G) hB.frame hB.places (fun y y' hy => ?_)
      (fg := fg) ?_ k2
    · unfold Base.locFn
      rw [Finset.prod_congr rfl fun PP hPP => by rw [hy PP hPP]]
    · simp only [GlobalTheory.FlatVecSum.omegaG_princ]
      exact k1
  refine ⟨eg, eQ, fg, hg, hq, hfg, ?_⟩
  rw [← hfeq]
  exact hf

end GlobalTheory.BaseCmp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatThetaQuotientAtPrincipalLevelProofStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatThetaQuotientAtPrincipalLevel_proof : GlobalTheory.BaseCmp.FlatTwoStep := by
  first | exact @GlobalTheory.BaseCmp.flatTwoStep_holds | exact GlobalTheory.BaseCmp.flatTwoStep_holds | (intros; apply GlobalTheory.BaseCmp.flatTwoStep_holds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DilatedFlatDatumIsSBHalfTameKernel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DilatedFlatDatumIsSBHalfTameKernel
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.DilFlat

theorem eToEAf_int' {D : D7} (x : 𝓞 D.host.E) : eToEAf D (x : D.host.E) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
  Subring.subset_closure (Or.inl ⟨⟨(x : D.host.E), ⟨x, rfl⟩⟩, rfl⟩)

theorem isSBHalf_dilFlat : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m), VStd D i → ∀ (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)),
    (∃ t, Q ⊆ R.Q t) → ∀ eQ : AE D, IsIdemSum eQ Q → ∀ ϖ : 𝓞 D.host.E, ϖ ≠ 0 → (∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) →
    ∀ Gc : ℂ, IsSBHalf eQ (lattice₂ R i) (fun x => Gc * flatDat R i Q ξR eQ (dil i (ϖ : D.host.E) x)) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC _ i _ ξR Q _ eQ hq ϖ hϖ _ Gc
  suffices hΦ : IsSBHalf eQ (lattice₂ R i) (fun x => flatDat R i Q ξR eQ (dil i (ϖ : D.host.E) x)) by
    obtain ⟨h1, k, hk, h2, h3⟩ := hΦ
    exact ⟨fun t ht => h1 t (right_ne_zero_of_mul ht), k, hk, fun v hv hv' t => by simp only [h2 v hv hv' t],
      fun t ht => h3 t (right_ne_zero_of_mul ht)⟩
  have sV : IsSelfDualC (Vc D i) (R.ΛV i) :=
    GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hC.lev.βV i))
  have sW : IsSelfDualC (Wc D i) (R.ΛW i) :=
    GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hC.lev.βW i))
  have hinfQ := GlobalTheory.PlaceDatum.infPart_idemSum hq
  have hϖE : (ϖ : D.host.E) ≠ 0 := by exact_mod_cast hϖ
  have hu : IsUnit (incA D (ϖ : D.host.E)) := (Ne.isUnit hϖE).map _
  have hc : eToEAf D (ϖ : D.host.E) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := eToEAf_int' ϖ
  have hfr : ∀ x : WO (Vc D i) (Wc D i), ∀ a b,
      frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (dil i (ϖ : D.host.E) x) a b =
        eToEAf D (ϖ : D.host.E) * frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) x a b := by
    intro x a b
    have hm : ((dil i (ϖ : D.host.E) x : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) (AE D)).map (toEAf D)) =
        eToEAf D (ϖ : D.host.E) • (x : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) (AE D)).map (toEAf D) := by
      ext a' b'
      simp only [dil, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, RingHom.map_mul]
      rfl
    simp only [frMapO]
    rw [hm, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
  have hhalf : ∀ x : WO (Vc D i) (Wc D i), IsHalf eQ (dil i (ϖ : D.host.E) x) ↔ IsHalf eQ x := by
    intro x
    refine ⟨fun h a b => hu.mul_left_cancel ?_, fun h a b => ?_⟩
    · have := h a b
      simp only [dil, Matrix.map_apply] at this
      rw [← this]; ring
    · simp only [dil, Matrix.map_apply]
      rw [mul_left_comm, h a b]
  have key : (fun x => flatDat R i Q ξR eQ (dil i (ϖ : D.host.E) x)) = fun x =>
      if IsHalf eQ x ∧ IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (dil i (ϖ : D.host.E) x)) then
        omegaFlat Q (Wc D i).rank ξR (fun PP => redM PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (dil i (ϖ : D.host.E) x)))
      else 0 := by
    funext x
    unfold flatDat
    by_cases h : IsHalf eQ x ∧ IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (dil i (ϖ : D.host.E) x))
    · rw [if_pos h, if_pos ⟨(hhalf x).2 h.1, h.2⟩]
    · rw [if_neg h, if_neg fun h' => h ⟨(hhalf x).1 h'.1, h'.2⟩]
  rw [key]
  refine GlobalTheory.PlaceDatum.isSBHalf_of_red eQ _ (fun x => frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (dil i (ϖ : D.host.E) x))
    ?_ ?_ ?_ Q _ fun y y' h => GlobalTheory.FlatVecExist.omegaFlat_congr _ _ _ h
  · intro x u k a b
    simp only [hfr, GlobalTheory.PlaceDatum.frMapO_add]
    ring
  · obtain ⟨M, hM, h⟩ := GlobalTheory.PlaceDatum.exists_den_frMapO sV.1.fg sW.1.fg (R.βV i) (R.βW i)
    refine ⟨M, hM, fun u hu' a b => ?_⟩
    simp only [hfr]
    rw [mul_left_comm]
    exact mul_mem hc (h u hu' a b)
  · obtain ⟨K, hK, h⟩ := GlobalTheory.PlaceDatum.exists_nsmul_of_frMapO
      (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ sV)
      (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ sW) (R.βV i) (R.βW i)
    have hI : Ideal.span {ϖ} ≠ ⊥ := by simpa [Ideal.span_singleton_eq_bot] using hϖ
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {ϖ}))
    set n := Ideal.absNorm (Ideal.span {ϖ})
    have hn : 0 < n := Nat.pos_of_ne_zero fun h0 => hI (Ideal.absNorm_eq_zero_iff.1 h0)
    have hnE : eToEAf D ((y : 𝓞 D.host.E) : D.host.E) * eToEAf D (ϖ : D.host.E) = (n : EAf D) := by
      rw [← RingHom.map_mul, ← map_natCast (eToEAf D)]
      congr 1
      exact_mod_cast hy
    refine ⟨K * n, Nat.mul_pos hK hn, fun t ht hti => ?_⟩
    have hnt : IsHalf eQ (n • t) := fun a b => by
      change eQ * (n • t a b) = n • t a b
      rw [mul_smul_comm, ht a b]
    have hfn : ∀ a b, frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (n • t) a b =
        (n : EAf D) * frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) t a b := fun a b => by
      have := GlobalTheory.PlaceDatum.frMapO_add (R.βV i) (R.βW i) 0 t n a b
      rw [zero_add] at this
      rw [this]
      simp [frMapO]
    rw [← smul_smul]
    refine h _ (GlobalTheory.PlaceDatum.infPart_of_half hinfQ hnt) fun a b => ?_
    rw [hfn, ← hnE, mul_assoc, ← hfr]
    exact mul_mem (eToEAf_int' y) (hti a b)

end GlobalTheory.DilFlat

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DilatedFlatDatumIsSBHalfTameKernelStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dilatedFlatDatum_isSBHalf_tameKernel : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m), VStd D i → ∀ (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)),
    (∃ t, Q ⊆ R.Q t) → ∀ eQ : AE D, IsIdemSum eQ Q → ∀ ϖ : 𝓞 D.host.E, ϖ ≠ 0 → (∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) →
    ∀ Gc : ℂ, IsSBHalf eQ (lattice₂ R i) (fun x => Gc * flatDat R i Q ξR eQ (dil i (ϖ : D.host.E) x)) := by
  first | exact @GlobalTheory.DilFlat.isSBHalf_dilFlat | exact GlobalTheory.DilFlat.isSBHalf_dilFlat | (intros; apply GlobalTheory.DilFlat.isSBHalf_dilFlat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasMarkingPreservingTransportOfConjEmbedding
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasMarkingPreservingTransportOfConjEmbedding
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm
open GlobalTheory.ArchMetricCompare GlobalTheory.ConjUnif

namespace GlobalTheory.ConjTransport

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {D : Datum H} {l : Level H}
  {B : Type} [CommRing B] {b : Base l B} {s s₁ : Sp ℂ ⟶ Sp B} {o : Obj D l b s} {o₁ : Obj D l b s₁}

theorem cjPt_act (m : ObjMap o₁ o cj) (x : 𝟙_ (Over (Sp ℂ)) ⟶ o.t.G) (a : 𝓞 E) :
    cjPt m.cart (x ≫ o.t.act.act a) = cjPt m.cart x ≫ o₁.t.act.act a := by
  refine pt_ext m.cart ((cjPt_comp _ _).trans ?_)
  rw [Over.comp_left, Over.comp_left, Category.assoc, m.act, ← Category.assoc (cjPt m.cart x).left, cjPt_comp]
  exact (Category.assoc _ _ _).symm

theorem cjPt_eta (m : ObjMap o₁ o cj) (a : D.La) : cjPt m.cart (o.eta a) = o₁.eta a :=
  pt_ext m.cart ((cjPt_comp _ _).trans (m.eta a).symm)

theorem cjPt_etaA (m : ObjMap o₁ o cj) (a : D.La) : cjPt m.cart (o.etaA a) = o₁.etaA a :=
  pt_ext m.cart ((cjPt_comp _ _).trans (m.etaA a).symm)

theorem exists_unif (m : ObjMap o₁ o cj) {g : ℕ} (u : HolUnif o.t.G o.t.PP.L g) {Hm : Matrix (Fin g) (Fin g) ℂ}
    {κ : u.Λ → ℂ} (hA : u.IsAH Hm κ) :
    ∃ (u₁ : HolUnif o₁.t.G o₁.t.PP.L g) (κ₁ : u₁.Λ → ℂ), u₁.IsAH (Hm.map star) κ₁ ∧
      (∀ z, z ∈ u₁.Λ ↔ star z ∈ u.Λ) ∧ ∀ z, u₁.ex z = cjPt m.cart (u.ex (star z)) := by
  obtain ⟨w, hw, -⟩ := m.lin
  obtain ⟨w', hw', -⟩ := exists_inv w hw
  have hP := pull_isLB o.t.PP.isLB m.cm.F
  exact ⟨carry (conjPull m.cart u) hP o₁.t.PP.isLB hw', _,
    carry_isAH hP o₁.t.PP.isLB hw' (conjPull_isAH m.cart u hA), fun _ => Iff.rfl, fun _ => rfl⟩

theorem herm_map_star {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    (herm (Hm.map star) z w).im = -(herm Hm (star z) (star w)).im := by
  rw [herm, herm, ← star_form]
  rfl

def conjEquiv (g : ℕ) : (Fin g → ℂ) ≃ₗ[ℝ] (Fin g → ℂ) := (starL' ℝ (A := Fin g → ℂ)).toLinearEquiv

theorem conjEquiv_apply {g : ℕ} (z : Fin g → ℂ) : conjEquiv g z = star z := rfl

theorem isTransport_conj {s' s₁' : Sp ℂ ⟶ Sp B} {o' : Obj D l b s'} {o₁' : Obj D l b s₁'}
    (m : ObjMap o₁ o cj) (m' : ObjMap o₁' o' cj) {g g' : ℕ}
    {u : HolUnif o.t.G o.t.PP.L g} {u' : HolUnif o'.t.G o'.t.PP.L g'}
    {u₁ : HolUnif o₁.t.G o₁.t.PP.L g} {u₁' : HolUnif o₁'.t.G o₁'.t.PP.L g'}
    {Hm : Matrix (Fin g) (Fin g) ℂ} {Hm' : Matrix (Fin g') (Fin g') ℂ}
    (hΛ : ∀ z, z ∈ u₁.Λ ↔ star z ∈ u.Λ) (hx : ∀ z, u₁.ex z = cjPt m.cart (u.ex (star z)))
    (hΛ' : ∀ z, z ∈ u₁'.Λ ↔ star z ∈ u'.Λ) (hx' : ∀ z, u₁'.ex z = cjPt m'.cart (u'.ex (star z)))
    {φ : (Fin g → ℂ) ≃ₗ[ℝ] (Fin g' → ℂ)} (h : IsTransport o₁ o₁' u₁ u₁' (Hm.map star) (Hm'.map star) φ) :
    IsTransport o o' u u' Hm Hm' ((conjEquiv g).trans (φ.trans (conjEquiv g'))) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have e : ∀ z, ((conjEquiv g).trans (φ.trans (conjEquiv g'))) z = star (φ (star z)) := fun _ => rfl
  refine ⟨fun z => ?_, fun a z w hw => ?_, fun z w => ?_, fun a z hz => ?_, fun a z hz => ?_⟩
  · rw [e, ← hΛ', h1, hΛ, star_star]
  · refine cjPt_injective m'.cart ?_
    rw [e, e, cjPt_act, ← hx', ← hx']
    refine h2 a _ _ ?_
    rw [hx, hx, star_star, star_star, hw, cjPt_act]
  · have := h3 (star z) (star w)
    rw [herm_map_star, herm_map_star, star_star, star_star] at this
    rw [e, e]
    exact neg_injective this
  · refine cjPt_injective m'.cart ?_
    rw [e, ← hx', cjPt_eta]
    refine h4 a _ ?_
    rw [hx, star_star, hz, cjPt_eta]
  · refine cjPt_injective m'.cart ?_
    rw [e, ← hx', cjPt_etaA]
    refine h5 a _ ?_
    rw [hx, star_star, hz, cjPt_etaA]

theorem exists_conj_obj (Xo : Moduli D l) (c : Coeff l) (y : Sp ℂ ⟶ Xo.XF c)
    (o : Obj D l (baseKA l) (y ≫ toX Xo c ≫ Xo.s)) (n : ObjMap o Xo.univ (y ≫ toX Xo c)) :
    ∃ o₁ : Obj D l (baseKA l) ((cj ≫ y) ≫ toX Xo c ≫ Xo.s),
      Nonempty (ObjMap o₁ o cj) ∧ Nonempty (ObjMap o₁ Xo.univ ((cj ≫ y) ≫ toX Xo c)) := by
  obtain ⟨o₁, ⟨m⟩⟩ := GlobalTheory.obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ _
    ((cj ≫ y) ≫ toX Xo c ≫ Xo.s) cj rfl rfl
    (by rw [DetExtendZero.spMap_id, Category.comp_id, Category.assoc]) o
  obtain ⟨k, -⟩ := ObjComp.objMap_comp n m
  exact ⟨o₁, ⟨m⟩, by rw [Category.assoc cj y (toX Xo c)]; exact ⟨k⟩⟩

end GlobalTheory.ConjTransport

namespace GlobalTheory

open ConjTransport

theorem hasTransport_of_conj (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (D : Datum H)
    (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (e : c.F →+* ℂ)
    (h : HasTransport Xo c U ((starRingEnd ℂ).comp e)) : HasTransport Xo c U e := by
  rintro y y' hy hy' hU hU' o o' ⟨n⟩ ⟨n'⟩ g g' u u' Hm Hm' κ κ' hA hA'
  obtain ⟨o₁, ⟨m⟩, k⟩ := exists_conj_obj Xo c y o n
  obtain ⟨o₁', ⟨m'⟩, k'⟩ := exists_conj_obj Xo c y' o' n'
  obtain ⟨u₁, κ₁, hA₁, hΛ, hx⟩ := exists_unif m u hA
  obtain ⟨u₁', κ₁', hA₁', hΛ', hx'⟩ := exists_unif m' u' hA'
  have a : ∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ toF Xo c = spMap e →
      (cj ≫ y) ≫ toF Xo c = spMap ((starRingEnd ℂ).comp e) := fun y hy => by
    rw [Category.assoc, hy, DetExtendZero.spMap_comp]
  have r : ∀ y : Sp ℂ ⟶ Xo.XF c, Set.range y ⊆ U → Set.range (cj ≫ y) ⊆ U := by
    rintro y hy _ ⟨z, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact hy ⟨_, rfl⟩
  obtain ⟨φ, hφ⟩ := h (cj ≫ y) (cj ≫ y') (a y hy) (a y' hy') (r y hU) (r y' hU') o₁ o₁' k k' g g' u₁ u₁' _ _ κ₁ κ₁'
    hA₁ hA₁'
  exact ⟨_, isTransport_conj m m' hΛ hx hΛ' hx' hφ⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasMarkingPreservingTransportOfConjEmbeddingStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasMarkingPreservingTransport_of_conj_embedding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (e : c.F →+* ℂ), HasTransport Xo c U ((starRingEnd ℂ).comp e) → HasTransport Xo c U e := by
  first | exact @GlobalTheory.hasTransport_of_conj | exact GlobalTheory.hasTransport_of_conj | (intros; apply GlobalTheory.hasTransport_of_conj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyRuleLieBasisChangeUnitFactor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyRuleLieBasisChangeUnitFactor
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MBLow.BasisChange

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

def cb {n : ℕ} (c : Fin n → R) (v : Fin n → (epsR R ⟶ G)) : epsR R ⟶ G :=
  ∏ i, GrpTangent.epsScale (c i) ≫ v i

theorem comb_iff {n : ℕ} (c : Fin n → R) (v : Fin n → (epsR R ⟶ G)) (w : epsR R ⟶ G) :
    IsLieComb c v w ↔ w = cb c v := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [List.prod_ofFn]
    exact Finset.prod_congr rfl fun i _ => Over.OverMorphism.ext (hu i)
  · rintro rfl
    exact ⟨fun i => GrpTangent.epsScale (c i) ≫ v i, fun i => rfl, by rw [List.prod_ofFn]; rfl⟩

theorem comp_prod' {T T' : Over (Sp R)} (s : T' ⟶ T) {J : Type} (S : Finset J) (u : J → (T ⟶ G)) :
    s ≫ ∏ i ∈ S, u i = ∏ i ∈ S, s ≫ u i := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [MonObj.comp_one]
  | insert a S ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, MonObj.comp_mul, ih]

theorem cb_tan {n : ℕ} (c : Fin n → R) {v : Fin n → (epsR R ⟶ G)} (hv : ∀ i, IsTangent (v i)) :
    IsTangent (cb c v) := by
  rw [GrpTangent.isTangent_iff, cb, comp_prod']
  exact Finset.prod_eq_one fun i _ => (GrpTangent.isTangent_iff _).1 (GrpTangent.isTangent_epsScale _ (hv i))

theorem scale_sum {w : epsR R ⟶ G} (hw : IsTangent w) {J : Type} (S : Finset J) (a : J → R) :
    GrpTangent.epsScale (∑ i ∈ S, a i) ≫ w = ∏ i ∈ S, GrpTangent.epsScale (a i) ≫ w := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using GrpTangent.epsScale_zero_comp hw
  | insert j S hj ih => rw [Finset.prod_insert hj, Finset.sum_insert hj, GrpTangent.epsScale_add_comp _ _ hw, ih]

theorem cb_cb {m n : ℕ} (a : Fin m → R) (M : Matrix (Fin m) (Fin n) R) {v : Fin n → (epsR R ⟶ G)}
    (hv : ∀ i, IsTangent (v i)) : cb a (fun i => cb (M i) v) = cb (Matrix.vecMul a M) v := by
  simp only [cb, comp_prod', GrpTangent.epsScale_mul_assoc]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← scale_sum (hv j)]
  rfl

theorem cb_single {n : ℕ} {v : Fin n → (epsR R ⟶ G)} (hv : ∀ i, IsTangent (v i)) (j : Fin n) :
    cb (Pi.single j 1) v = v j := by
  rw [cb, Finset.prod_eq_single j]
  · rw [Pi.single_eq_same, GrpTangent.epsScale_one, Category.id_comp]
  · intro i _ hi
    rw [Pi.single_eq_of_ne hi, GrpTangent.epsScale_zero_comp (hv i)]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem exists_unit {n : ℕ} {y y' : Fin n → (epsR R ⟶ G)} (hy : IsLieBasis y) (hy' : IsLieBasis y') :
    ∃ M : Matrix (Fin n) (Fin n) R, IsUnit M ∧ ∀ i, IsLieComb (M i) y (y' i) := by
  choose M hM using fun i => (hy.2 _ (hy'.1 i)).exists
  choose N hN using fun i => (hy'.2 _ (hy.1 i)).exists
  refine ⟨Matrix.of M, ?_, hM⟩
  have e : y' = fun i => cb (Matrix.of M i) y := funext fun i => (comb_iff _ _ _).1 (hM i)
  have h : Matrix.of N * Matrix.of M = 1 := by
    ext i j
    have k : y i = cb (Matrix.vecMul (N i) (Matrix.of M)) y := by
      rw [← cb_cb _ _ hy.1, ← e]
      exact (comb_iff _ _ _).1 (hN i)
    have := (hy.2 _ (hy.1 i)).unique ((comb_iff _ _ _).2 k) ((comb_iff _ _ _).2 (cb_single hy.1 i).symm)
    have := congrFun this j
    rw [Matrix.one_apply, Matrix.mul_apply]
    simpa [Matrix.vecMul, dotProduct, Pi.single_apply, eq_comm] using this
  exact IsUnit.of_mul_eq_one_right _ h

theorem basis_of_unit {n : ℕ} {v v' : Fin n → (epsR R ⟶ G)} (hv : IsLieBasis v) {M : Matrix (Fin n) (Fin n) R}
    (hM : IsUnit M) (h : ∀ i, IsLieComb (M i) v (v' i)) : IsLieBasis v' := by
  have e : v' = fun i => cb (M i) v := funext fun i => (comb_iff _ _ _).1 (h i)
  subst e
  refine ⟨fun i => cb_tan _ hv.1, fun w hw => ?_⟩
  obtain ⟨c, hc, hu⟩ := hv.2 w hw
  obtain ⟨U, rfl⟩ := hM
  set M : Matrix (Fin n) (Fin n) R := U.val with hMU
  have hN : M * U.inv = 1 := U.val_inv
  have hN' : U.inv * M = 1 := U.inv_val
  have key : ∀ b, IsLieComb b (fun i => cb (M i) v) w ↔ Matrix.vecMul b M = c := fun b => by
    rw [comb_iff, cb_cb _ _ hv.1, ← comb_iff]
    exact ⟨fun q => hu _ q, fun q => by rw [q]; exact hc⟩
  refine ⟨Matrix.vecMul c U.inv, (key _).2 ?_, fun b hb => ?_⟩
  · rw [Matrix.vecMul_vecMul, hN', Matrix.vecMul_one]
  · rw [← (key b).1 hb, Matrix.vecMul_vecMul, hN, Matrix.vecMul_one]

end GlobalTheory.MBLow.BasisChange

theorem GlobalTheory.MBLow.key_basis_change : ∀ κ : Rule, Homog (fun _ => 1) κ → ∀ (R K : Type) [CommRing R] [Field K] [CharZero K] (f : R →+* K) (x : KeyIn K) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (φ : x.P.A.left ⟶ G.left), IsGrpPullback x.P.A G (spMap f) φ → ∀ (y y' : Fin x.P.g → (epsR R ⟶ G)) (v' : Fin x.P.g → (epsR K ⟶ x.P.A)), IsLieBasis y → IsLieBasis y' → (∀ i, IsVecOver f φ (y i) (x.v i)) → (∀ i, IsVecOver f φ (y' i) (v' i)) → ∃ (hv : IsLieBasis v') (u : Rˣ), (κ K ⟨x.P, x.g_pos, x.rig, x.rig_gen, x.th, x.th_ne, v', hv⟩ : K) = f u * κ K x := by
  intro κ hκ R K _ _ _ f x G _ _ φ hφ y y' v' hy hy' hv hv'
  obtain ⟨M, hM, hMy⟩ := GlobalTheory.MBLow.BasisChange.exists_unit hy hy'
  have hc : ∀ i, IsLieComb ((M.map f) i) x.v (v' i) := fun i =>
    Chart.comb_baseChange f hφ (hMy i) hv (hv' i)
  let _ := x.P.isAb.comm
  have hb : IsLieBasis v' := GlobalTheory.MBLow.BasisChange.basis_of_unit x.basis (hM.map f.mapMatrix) hc
  have hd : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).1 hM
  refine ⟨hb, hd.unit ^ 4, ?_⟩
  have := hκ K x.P x.g_pos x.rig x.rig_gen x.th x.th_ne x.v x.basis x.th x.th_ne v' hb 1 (M.map f)
    (fun i => by rw [show Geo.Tor.constFn x.P.A.hom _ (1 : K) = 1 by simp [Geo.Tor.constFn], _root_.one_mul]) hc
  have e : (M.map f).det = f M.det := (RingHom.map_det f M).symm
  rw [e] at this
  simpa using this
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyRuleLieBasisChangeUnitFactorStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaKeyRule_lieBasisChange_unit_factor : ∀ κ : Rule, Homog (fun _ => 1) κ → ∀ (R K : Type) [CommRing R] [Field K] [CharZero K] (f : R →+* K) (x : KeyIn K) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (φ : x.P.A.left ⟶ G.left), IsGrpPullback x.P.A G (spMap f) φ → ∀ (y y' : Fin x.P.g → (epsR R ⟶ G)) (v' : Fin x.P.g → (epsR K ⟶ x.P.A)), IsLieBasis y → IsLieBasis y' → (∀ i, IsVecOver f φ (y i) (x.v i)) → (∀ i, IsVecOver f φ (y' i) (v' i)) → ∃ (hv : IsLieBasis v') (u : Rˣ), (κ K ⟨x.P, x.g_pos, x.rig, x.rig_gen, x.th, x.th_ne, v', hv⟩ : K) = f u * κ K x := by
  first | exact @GlobalTheory.MBLow.key_basis_change | exact GlobalTheory.MBLow.key_basis_change | (intros; apply GlobalTheory.MBLow.key_basis_change <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelObjectOfGaloisDescendedData
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelObjectOfGaloisDescendedData
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegelGaloisDescent

open GlobalTheory.CechPic

variable {S : Scheme.{0}}

theorem eta_lift_one_id (A : Over S) [GrpObj A] : η[A] ≫ lift (1 : A ⟶ A) (𝟙 A) = η[A ⊗ A] := by
  ext <;> simp [Hom.one_def]

theorem eta_lift_id_one (A : Over S) [GrpObj A] : η[A] ≫ lift (𝟙 A) (1 : A ⟶ A) = η[A ⊗ A] := by
  ext <;> simp [Hom.one_def]

theorem eta_swap (A : Over S) [GrpObj A] : η[A ⊗ A] ≫ lift (snd A A) (fst A A) = η[A ⊗ A] := by
  ext <;> simp

theorem eq_zero_of_cart (hG : Out.GlobalFnsSt) {S' : Scheme.{0}} (π : S' ⟶ S) [Flat π] [Surjective π]
    [QuasiCompact π] {A : Over S} [GrpObj A] (hA : IsAbelianScheme A) {B : Over S'} {φ : B.left ⟶ A.left}
    (hp : IsPullback φ B.hom A.hom π) (c : Pic A.left) (h₀ : pull (eSec A) c = 0) (h₁ : pull φ c = 0) : c = 0 := by
  refine TripleDescent.eq_zero_of_pull hG π hA c h₀ ?_
  have e : (TripleDescent.fibreProj A π).left = hp.isoPullback.inv ≫ φ := by
    simp [TripleDescent.fibreProj]
  rw [e, pull_comp, h₁, map_zero]

end GlobalTheory.SiegelGaloisDescent

namespace GlobalTheory

open SiegelDescent SiegelGaloisDescent CechPic

theorem exists_siegPre_of_galois_descended_data : ∀ (h M : ℕ) (o : Type) [CommRing o] (ζ : o) (X Y : Scheme.{0}) (π : X ⟶ Y) (s : X ⟶ Sp o) (sY : Y ⟶ Sp o) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (c : SiegPre h M ζ s) (A₀ : Over Y) [GrpObj A₀] (φ : c.A.left ⟶ A₀.left) (φ₂ : (G2 c.A).left ⟶ (G2 A₀).left) (P₀ : LB (G2 A₀).left) (lev₀ : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over Y) ⟶ A₀)), s = π ≫ sY → IsGaloisCover Ga ρ π → IsAbelianScheme A₀ → IsGrpPullback c.A A₀ π φ → IsSquare φ φ₂ → P₀.IsLB → LBIso c.P (P₀.pull φ₂) → (∃ t : (P₀.pull (eSec (G2 A₀))).Gen, t.IsGen) → (∀ a, (c.lev a).left ≫ φ = π ≫ (lev₀ a).left) → ∃ c₀ : SiegPre h M ζ sY, SiegPB c c₀ π := by
  intro h M o _ ζ X Y π s sY Ga _ ρ c A₀ _ φ φ₂ P₀ lev₀ hs hGal ab hp sq hP₀ hw ht hlev
  haveI := ab.comm
  have gf : Out.GlobalFnsSt := abelianSchemeLaws_all.1.globalFns
  haveI : IsFinite π := hGal.fin
  haveI : Etale π := hGal.etale
  haveI : Surjective π := hGal.onto
  haveI : Epi π := Flat.epi_of_flat_of_surjective π
  have hφ : φ ≫ A₀.hom = c.A.hom ≫ π := hp.1.w
  have one := one_comp hp c.A A₀ φ hφ
  have idφ : (𝟙 c.A : c.A ⟶ c.A).left ≫ φ = φ ≫ (𝟙 A₀ : A₀ ⟶ A₀).left := by simp
  have ab₂ := AbelianSchemeGerms.isAbelianScheme_tensor A₀ A₀ ab ab
  have hp₂ := isPullback_square hp.1 φ₂ sq
  have clsP : cls c.P c.isLB = pull φ₂ (cls P₀ hP₀) := by
    rw [← cls_pull hP₀ φ₂ (pull_isLB hP₀ _)]
    exact (cls_eq_iff _ _).2 hw
  have P₀e : pull (eSec (G2 A₀)) (cls P₀ hP₀) = 0 := by
    rw [← cls_pull hP₀ _ (pull_isLB hP₀ _)]
    exact (cls_eq_zero_iff _).2 ht
  have rig : ∀ (a : c.A ⟶ c.A ⊗ c.A) (a₀ : A₀ ⟶ A₀ ⊗ A₀), a.left ≫ φ₂ = φ ≫ a₀.left →
      η[A₀] ≫ a₀ = η[A₀ ⊗ A₀] → (∃ t : (c.P.pull a.left).Gen, t.IsGen) →
      ∃ t : (P₀.pull a₀.left).Gen, t.IsGen := by
    intro a a₀ e e₀ hta
    have e₀' : eSec A₀ ≫ a₀.left = eSec (G2 A₀) := congrArg (fun q => q.left) e₀
    refine (cls_eq_zero_iff (pull_isLB hP₀ _)).1 ?_
    rw [cls_pull hP₀ _ (pull_isLB hP₀ _)]
    refine eq_zero_of_cart gf π ab hp.1 _ ?_ ?_
    · rw [← pull_comp, e₀', P₀e]
    · rw [← pull_comp, ← e, pull_comp, ← clsP, ← cls_pull c.isLB _ (pull_isLB c.isLB _)]
      exact (cls_eq_zero_iff _).2 hta
  have symm : LBIso P₀ (P₀.pull (lift (snd A₀ A₀) (fst A₀ A₀)).left) := by
    have esw : eSec (G2 A₀) ≫ (lift (snd A₀ A₀) (fst A₀ A₀)).left = eSec (G2 A₀) :=
      congrArg (fun q => q.left) (eta_swap A₀)
    have swsq := lift_square sq sq.2.symm sq.1.symm
    refine (cls_eq_iff hP₀ (pull_isLB hP₀ _)).1 (sub_eq_zero.1 (eq_zero_of_cart gf π ab₂ hp₂ _ ?_ ?_))
    · rw [map_sub, cls_pull hP₀ _ (pull_isLB hP₀ _), ← pull_comp, esw, P₀e, sub_zero]
    · rw [map_sub, cls_pull hP₀ _ (pull_isLB hP₀ _), ← pull_comp, ← swsq, pull_comp, ← clsP,
        ← cls_pull c.isLB _ (pull_isLB c.isLB _), sub_eq_zero]
      exact (cls_eq_iff _ _).2 c.symm
  have diag : LBIso (c.P.pull (lift (𝟙 c.A) (𝟙 c.A)).left) ((P₀.pull (lift (𝟙 A₀) (𝟙 A₀)).left).pull φ) :=
    lbIso_square c.isLB hP₀ hw (lift_square sq idφ idφ)

  obtain ⟨ρl, hρ⟩ := exists_liftHom hp (𝟙_ _) (𝟙_ _) π
    ((Category.comp_id _).trans (Category.id_comp _).symm)
  have ρlev : ∀ a, ρl (lev₀ a) = c.lev a := fun a => (hρ _ _).2 (hlev a)
  have ρinj : Function.Injective ρl := fun x y e =>
    Over.OverMorphism.ext ((cancel_epi π).1 (((hρ x _).1 rfl).symm.trans ((hρ y _).1 e.symm)))
  refine ⟨{ A := A₀, ab := ab, P := P₀, isLB := hP₀
            rig₁ := rig _ _ (lift_square sq one idφ) (eta_lift_one_id A₀) c.rig₁
            rig₂ := rig _ _ (lift_square sq idφ one) (eta_lift_id_one A₀) c.rig₂
            symm := symm, lev := lev₀
            lev_add := fun a b => ρinj (by rw [map_mul, ρlev, ρlev, ρlev, c.lev_add])
            lev_tors := fun a => ρinj (by rw [map_pow, ρlev, c.lev_tors, map_one])
            geom := ?_ }, φ, φ₂, hp, sq, hw, hlev⟩
  intro k _ _ x β z hx hz
  obtain ⟨y, hy⟩ := exists_lift_pt π x
  obtain ⟨g₁, g₂, g₃⟩ := c.geom k y β z (by rw [hs, ← Category.assoc, hy, hx]) hz
  obtain ⟨σ, hσ⟩ := exists_liftHom hp (Over.mk y) (Over.mk x) (𝟙 _) ((Category.id_comp _).trans hy.symm)
  have σinj : Function.Injective σ := fun u v e => Over.OverMorphism.ext (by
    simpa using ((hσ u _).1 rfl).symm.trans ((hσ v _).1 e.symm))
  have pt : ∀ a, (toUnit (Over.mk y) ≫ c.lev a).left ≫ φ = (toUnit (Over.mk x) ≫ lev₀ a).left := fun a => by
    change (y ≫ (c.lev a).left) ≫ φ = x ≫ (lev₀ a).left
    rw [Category.assoc, hlev, ← Category.assoc, hy]
  have σlev : ∀ a, σ (toUnit _ ≫ lev₀ a) = toUnit _ ≫ c.lev a := fun a =>
    (hσ _ _).2 ((pt a).trans (Category.id_comp _).symm)
  refine ⟨fun a => ?_, fun g hg => ?_, fun a b => ?_⟩
  · rw [← g₁ a, ← σlev, map_eq_one_iff σ σinj]
  · obtain ⟨a, ha⟩ := g₂ (σ g) (by rw [← map_pow, hg, map_one])
    exact ⟨a, σinj ((σlev a).trans ha)⟩
  · have hD := pull_isLB hP₀ (lift (𝟙 A₀) (𝟙 A₀)).left
    have H := (weilIs_grpPullback_of_comm _ _ A₀ c.A π φ _ _ hD (pull_isLB c.isLB _) hp diag _ _ _ _
      (pushPt hφ _) (pushPt hφ _) _ rfl rfl).1 (g₃ a b)
    exact weilIs_congr hy _ _ _ _ _ _ (pt a) (pt b) _ H

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelObjectOfGaloisDescendedDataStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_siegelObject_of_galois_descended_data : ∀ (h M : ℕ) (o : Type) [CommRing o] (ζ : o) (X Y : Scheme.{0}) (π : X ⟶ Y) (s : X ⟶ Sp o) (sY : Y ⟶ Sp o) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (c : SiegPre h M ζ s) (A₀ : Over Y) [GrpObj A₀] (φ : c.A.left ⟶ A₀.left) (φ₂ : (G2 c.A).left ⟶ (G2 A₀).left) (P₀ : LB (G2 A₀).left) (lev₀ : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over Y) ⟶ A₀)), s = π ≫ sY → IsGaloisCover Ga ρ π → IsAbelianScheme A₀ → IsGrpPullback c.A A₀ π φ → IsSquare φ φ₂ → P₀.IsLB → LBIso c.P (P₀.pull φ₂) → (∃ t : (P₀.pull (eSec (G2 A₀))).Gen, t.IsGen) → (∀ a, (c.lev a).left ≫ φ = π ≫ (lev₀ a).left) → ∃ c₀ : SiegPre h M ζ sY, SiegPB c c₀ π := by
  first | exact @GlobalTheory.exists_siegPre_of_galois_descended_data | exact GlobalTheory.exists_siegPre_of_galois_descended_data | (intros; apply GlobalTheory.exists_siegPre_of_galois_descended_data <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericRowSubstitutionCoeffExponentLeDegree
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalDegreeAevalLeOfDegLeOne
set_option autoImplicit false

open NumberField MvPolynomial

noncomputable section

namespace GlobalTheory.SZShift

theorem totalDegree_aeval_le_of_deg_le_one {σ τ F E : Type} [CommRing F] [CommRing E] [Algebra F E]
    (g : σ → MvPolynomial τ E) (hg : ∀ i, (g i).totalDegree ≤ 1) (P : MvPolynomial σ F) :
    (aeval g P).totalDegree ≤ P.totalDegree := by
  classical
  conv_lhs => rw [P.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun d hd => ?_)
  rw [aeval_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.algebraMap_apply, totalDegree_C, zero_add, Finsupp.prod]
  refine (totalDegree_finsetProd _ _).trans ?_
  refine le_trans ?_ (le_totalDegree hd)
  rw [Finsupp.sum]
  refine Finset.sum_le_sum fun i _ => ?_
  exact (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (d i) (hg i))

end GlobalTheory.SZShift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericRowSubstitutionCoeffExponentLeDegree
set_option autoImplicit false

open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef

namespace GlobalTheory.GenSubDeg

theorem genSub_coeff_le : ∀ (O : Type) [CommRing O] (N : ℕ) (D : ℕ) (f : MvPolynomial (Fin N × Fin N) O), f.totalDegree ≤ D → ∀ m, (GlobalTheory.HighWt.genSub O N f).coeff m ≠ 0 → ∀ v, m v ≤ D := by
  intro O _ N D f hf m hm v
  have hg : ∀ i : Fin N × Fin N, (∑ b : Fin N, (X (i.1, b) * C (X (b, i.2)) : MvPolynomial (Fin N × Fin N) (MvPolynomial (Fin N × Fin N) O))).totalDegree ≤ 1 := by
    intro i
    refine totalDegree_finsetSum_le fun b _ => ?_
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, add_zero]
    rw [X]
    exact (totalDegree_monomial_le _ _).trans (by simp)
  have hdeg := GlobalTheory.SZShift.totalDegree_aeval_le_of_deg_le_one _ hg f
  have h1 : m.degree ≤ (GlobalTheory.HighWt.genSub O N f).totalDegree := by
    rw [Finsupp.degree]
    exact le_totalDegree (mem_support_iff.mpr hm)
  have h2 : m v ≤ m.degree := by
    classical
    rw [Finsupp.degree]
    by_cases hv : v ∈ m.support
    · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hv
    · simp [Finsupp.notMem_support_iff.mp hv]
  exact h2.trans (h1.trans ((hdeg.trans hf)))

end GlobalTheory.GenSubDeg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericRowSubstitutionCoeffExponentLeDegreeStatement
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericRowSubstitution_coeff_exponent_le_degree : ∀ (O : Type) [CommRing O] (N : ℕ) (D : ℕ) (f : MvPolynomial (Fin N × Fin N) O), f.totalDegree ≤ D → ∀ m, (GlobalTheory.HighWt.genSub O N f).coeff m ≠ 0 → ∀ v, m v ≤ D := by
  first | exact @GlobalTheory.GenSubDeg.genSub_coeff_le | exact GlobalTheory.GenSubDeg.genSub_coeff_le | (intros; apply GlobalTheory.GenSubDeg.genSub_coeff_le <;> assumption)
end
end
