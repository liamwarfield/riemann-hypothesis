module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitMkOfFormallyUnramified
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLatticeTransportPreservesSelfDual
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntertwinerSelfDualVacuumIsVacuum
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AdmissibleCharactersExist
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonemptyCompactDualHaar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Spread
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AbsNormEqOfSplit
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemZmuOfPowPred
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricLevelTypePrimeDatumLocallySmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantSecond
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HolomorphicUniformizationTangentUnimodularRiemann
public import CompanionTheory.AutomorphicTheory.MirabolicRestriction.MirabolicInduction.CuspidalMirabolic
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableToGLEntry
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SecScalOfIsPullSec
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecBaseChangeOfPerf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricLevelTypePrimeDatumLocallySmallStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX isPushout_sections)

namespace GlobalTheory

namespace TopForm

open LB

section Ring

variable {k k' A B : Type} [CommRing k] [CommRing k'] [CommRing A] [CommRing B]
  {α : k →+* A} {β : k' →+* B}

def formMapSq (D : ℕ) (σ : k →+* k') (ρ : A →+* B) (h : ρ.comp α = β.comp σ) :
    Forms α D →ₛₗ[ρ] Forms β D :=
  letI := α.toAlgebra
  letI := β.toAlgebra
  letI := ρ.toAlgebra
  letI := σ.toAlgebra
  letI := (ρ.comp α).toAlgebra
  haveI : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower k k' B := IsScalarTower.of_algebraMap_eq' h
  haveI : SMulCommClass k' A B := SMulCommClass.of_commMonoid _ _ _
  { toFun := exteriorPowerMapOver B D (KaehlerDifferential.map k k' A B)
    map_add' := map_add _
    map_smul' := fun a x => by
      rw [map_smul, ← algebraMap_smul B]
      rfl }

variable {D : ℕ}

theorem formMapSq_dForm (σ : k →+* k') (ρ : A →+* B) (h : ρ.comp α = β.comp σ) (f : Fin D → A) :
    formMapSq D σ ρ h (dForm α f) = dForm β fun i => ρ (f i) := by
  letI := α.toAlgebra
  letI := β.toAlgebra
  letI := ρ.toAlgebra
  letI := σ.toAlgebra
  letI := (ρ.comp α).toAlgebra
  haveI : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower k k' B := IsScalarTower.of_algebraMap_eq' h
  haveI : SMulCommClass k' A B := SMulCommClass.of_commMonoid _ _ _
  change exteriorPowerMapOver B D (KaehlerDifferential.map k k' A B)
    (exteriorPower.ιMulti A D _) = _
  rw [exteriorPowerMapOver_ιMulti, dForm_eq]
  simp only [KaehlerDifferential.map_D]
  rfl

theorem IsFreeGen.formMapSq (σ : k →+* k') (ρ : A →+* B) (h : ρ.comp α = β.comp σ)
    (H : IsPushout (CommRingCat.ofHom α) (CommRingCat.ofHom σ) (CommRingCat.ofHom ρ)
      (CommRingCat.ofHom β)) {ω : Forms α D} (hω : IsFreeGen A ω) :
    IsFreeGen B (formMapSq D σ ρ h ω) := by
  letI := α.toAlgebra
  letI := β.toAlgebra
  letI := ρ.toAlgebra
  letI := σ.toAlgebra
  letI := (ρ.comp α).toAlgebra
  haveI : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower k k' B := IsScalarTower.of_algebraMap_eq' h
  haveI : SMulCommClass k' A B := SMulCommClass.of_commMonoid _ _ _
  haveI : Algebra.IsPushout k k' A B := (CommRingCat.isPushout_iff_isPushout.1 H).symm
  refine hω.of_isBaseChange (isBaseChange_exteriorPower
    (IsBaseChange.of_equiv (KaehlerDifferential.tensorKaehlerEquiv k k' A B) fun x => ?_) D)
  have hx : x ∈ Submodule.span A (Set.range (KaehlerDifferential.D k A)) :=
    (KaehlerDifferential.span_range_derivation k A).ge Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    simp
  | zero => simp
  | add x y _ _ hx hy => rw [TensorProduct.tmul_add, map_add (f := _), map_add (f := _), hx, hy]
  | smul a x _ hx =>
    rw [TensorProduct.tmul_smul, ← algebraMap_smul B, map_smul, hx, map_smul, algebraMap_smul]

end Ring

variable {k k' : Type} [CommRing k] [CommRing k'] {σ : k →+* k'} {Y Y' : Scheme.{0}}
  {p : Y ⟶ Sp k} {p' : Y' ⟶ Sp k'} {φ : Y' ⟶ Y} {D : ℕ}

theorem appLE_comp_algX (w : φ ≫ p = p' ≫ spMap σ) {V : Y.Opens} {W : Y'.Opens}
    (h : W ≤ φ ⁻¹ᵁ V) : (φ.appLE V W h).hom.comp (algX p V) = (algX p' W).comp σ := by
  have e₁ : p.appLE ⊤ V le_top ≫ φ.appLE V W h =
      (spMap σ).appLE ⊤ ⊤ le_top ≫ p'.appLE ⊤ W le_top := by
    refine (Scheme.Hom.appLE_comp_appLE φ p ⊤ V W le_top h).trans (Eq.trans ?_
      (Scheme.Hom.appLE_comp_appLE p' (spMap σ) ⊤ ⊤ W le_top le_top).symm)
    simp only [w]
  have e₂ := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom σ)
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE] at e₂
  have e₃ : (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ V le_top ≫ φ.appLE V W h =
      CommRingCat.ofHom σ ≫ (Scheme.ΓSpecIso (CommRingCat.of k')).inv ≫ p'.appLE ⊤ W le_top := by
    rw [e₁, ← Category.assoc, ← Category.assoc, e₂]
    rfl
  exact congrArg CommRingCat.Hom.hom e₃

def pullForm (w : φ ≫ p = p' ≫ spMap σ) {V : Y.Opens} {W : Y'.Opens} (h : W ≤ φ ⁻¹ᵁ V) :
    FormsOn p D V →ₛₗ[(φ.appLE V W h).hom] FormsOn p' D W :=
  formMapSq D σ (φ.appLE V W h).hom (appLE_comp_algX w h)

variable (w : φ ≫ p = p' ≫ spMap σ) {U V : Y.Opens} {U' W W' : Y'.Opens}

theorem pullForm_dOn (h : W ≤ φ ⁻¹ᵁ V) (f : Fin D → Γ(Y, V)) :
    pullForm w h (dOn p f) = dOn p' fun a => (φ.appLE V W h).hom (f a) :=
  formMapSq_dForm _ _ _ f

theorem resForm_pullForm (h : W ≤ φ ⁻¹ᵁ V) (e : W' ≤ W) (η : FormsOn p D V) :
    resForm e (pullForm w h η) = pullForm w (e.trans h) η := by
  haveI : RingHomCompTriple (φ.appLE V W h).hom (resG Y' e) (φ.appLE V W' (e.trans h)).hom :=
    ⟨RingHom.ext (resG_appLE φ h e)⟩
  refine LinearMap.congr_fun (forms_ext (φ := (resForm e).comp (pullForm w h))
    (ψ := pullForm w (e.trans h)) fun f => ?_) η
  rw [LinearMap.comp_apply, pullForm_dOn, pullForm_dOn, resForm_dOn]
  simp only [resG_appLE]

theorem pullForm_resForm (e : V ≤ U) (h : W ≤ φ ⁻¹ᵁ V) (η : FormsOn p D U) :
    pullForm w h (resForm e η) = pullForm w (h.trans (φ.preimage_mono e)) η := by
  haveI : RingHomCompTriple (resG Y e) (φ.appLE V W h).hom
      (φ.appLE U W (h.trans (φ.preimage_mono e))).hom :=
    ⟨RingHom.ext (appLE_resG φ e h)⟩
  refine LinearMap.congr_fun (forms_ext (φ := (pullForm w h).comp (resForm e))
    (ψ := pullForm w (h.trans (φ.preimage_mono e))) fun f => ?_) η
  rw [LinearMap.comp_apply, resForm_dOn, pullForm_dOn, pullForm_dOn]
  simp only [appLE_resG]

theorem IsFrame.coeff_pullForm {ω : FormsOn p D U} (hω : IsFrame ω) (hU : U' ≤ φ ⁻¹ᵁ U)
    (hω' : IsFrame (pullForm w hU ω)) (e : V ≤ U) (e' : W ≤ U') (h : W ≤ φ ⁻¹ᵁ V)
    (η : FormsOn p D V) :
    hω'.coeff e' (pullForm w h η) = (φ.appLE V W h).hom (hω.coeff e η) := by
  refine fun_ext_of_cover (fun T : {T : Y.Opens // IsAffineOpen T ∧ T ≤ V} => W ⊓ φ ⁻¹ᵁ T.1)
    (fun _ => inf_le_left) (fun x hx => ?_) fun T => ?_
  · obtain ⟨T, hT⟩ := Opens.mem_iSup.1 (le_iSup_affine V (h hx))
    exact Opens.mem_iSup.2 ⟨T, hx, hT⟩
  · have h₁ := congrArg (pullForm w (inf_le_right : W ⊓ φ ⁻¹ᵁ T.1 ≤ _))
      (hω.resForm_eq_coeff_smul e η T.2.1 T.2.2)
    rw [map_smulₛₗ, pullForm_resForm, pullForm_resForm, appLE_resG] at h₁
    rw [IsFrame.resG_coeff, resForm_pullForm, resG_appLE]
    exact hω'.coeff_eq_of_eq_smul _ (h₁.trans (by rw [resForm_pullForm]))

theorem isAffineOpen_preimage_of_isPullback (H : IsPullback φ p' p (spMap σ))
    (hU : IsAffineOpen U) : IsAffineOpen (φ ⁻¹ᵁ U) :=
  haveI : IsAffineHom φ := MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance
  hU.preimage φ

theorem IsFrame.pullForm (H : IsPullback φ p' p (spMap σ)) {ω : FormsOn p D U} (hω : IsFrame ω)
    (hW : IsAffineOpen W) (h : W ≤ φ ⁻¹ᵁ U) : IsFrame (pullForm H.w h ω) := by
  letI := σ.toAlgebra
  have h₁ : IsFrame (TopForm.pullForm H.w (inf_le_left : φ ⁻¹ᵁ U ⊓ p' ⁻¹ᵁ ⊤ ≤ _) ω) := by
    refine ⟨?_, hω.gen.formMapSq σ _ _ (isPushout_sections p p' φ H U hω.affine)⟩
    rw [show φ ⁻¹ᵁ U ⊓ p' ⁻¹ᵁ ⊤ = φ ⁻¹ᵁ U from inf_top_eq _]
    exact isAffineOpen_preimage_of_isPullback H hω.affine
  have h₂ := h₁.res hW (le_inf h le_top)
  rwa [resForm_pullForm] at h₂

end TopForm

namespace CanonLB

open TopForm LB

variable {k k' : Type} [CommRing k] [CommRing k'] {σ : k →+* k'} {Y Y' : Scheme.{0}}
  {p : Y ⟶ Sp k} {p' : Y' ⟶ Sp k'} {φ : Y' ⟶ Y} {D : ℕ}
  [SmoothOfRelativeDimension D p] [SmoothOfRelativeDimension D p']

theorem isFrame_pull (H : IsPullback φ p' p (spMap σ)) (K : CanonLB p D)
    (i : (K.bundle.pull φ).ι) : IsFrame (pullForm H.w (pull_U_le φ i) (K.om (i PUnit.unit))) :=
  (K.isFrame _).pullForm H
    (by rw [pull_U]; exact isAffineOpen_preimage_of_isPullback H (K.affine _)) _

def baseChange (H : IsPullback φ p' p (spMap σ)) (K : CanonLB p D) : CanonLB p' D where
  bundle := K.bundle.pull φ
  isLB := Semi.LB.isLB_linComb K.isLB _ _
  affine i := (K.isFrame_pull H i).affine
  om i := pullForm H.w (pull_U_le φ i) (K.om (i PUnit.unit))
  gen i := (K.isFrame_pull H i).gen
  trans i j W hW hi hj := by
    have h : W ≤ φ ⁻¹ᵁ (K.bundle.U (i PUnit.unit) ⊓ K.bundle.U (j PUnit.unit)) :=
      le_inf (hi.trans (pull_U_le φ i)) (hj.trans (pull_U_le φ j))
    have h₁ := (K.isFrame _).coeff_pullForm H.w _ (K.isFrame_pull H i) inf_le_left hi h
      (resForm inf_le_right (K.om (j PUnit.unit)))
    rw [pullForm_resForm] at h₁
    rw [resG_pull_g, g_eq_ratio, resForm_pullForm]
    exact ((K.isFrame_pull H i).coeff_smul_resForm hW hi _).symm.trans (congrArg (· • _) h₁)

theorem jacobian_baseChange (H : IsPullback φ p' p (spMap σ)) (K : CanonLB p D)
    (i : (K.bundle.pull φ).ι) {V : Y.Opens} (hV : V ≤ K.bundle.U (i PUnit.unit)) {W : Y'.Opens}
    (hW : W ≤ (K.bundle.pull φ).U i) (h : W ≤ φ ⁻¹ᵁ V) (f : Fin D → Γ(Y, V)) :
    (K.baseChange H).jacobian i hW (fun a => (φ.appLE V W h).hom (f a)) =
      (φ.appLE V W h).hom (K.jacobian (i PUnit.unit) hV f) := by
  have h₁ := (K.isFrame _).coeff_pullForm H.w _ (K.isFrame_pull H i) hV hW h (dOn p f)
  rw [pullForm_dOn] at h₁
  exact h₁

end CanonLB

theorem canonLB_baseChange (k k' : Type) [CommRing k] [CommRing k'] (σ : k →+* k')
    (Y Y' : Scheme.{0}) (p : Y ⟶ Sp k) (p' : Y' ⟶ Sp k') (φ : Y' ⟶ Y) (D : ℕ)
    [SmoothOfRelativeDimension D p] [SmoothOfRelativeDimension D p']
    (H : IsPullback φ p' p (spMap σ)) (K : CanonLB p D) (K' : CanonLB p' D) :
    ∃ w : LB.Iso K'.bundle (K.bundle.pull φ), w.IsGen ∧
      ∀ (i : (K.bundle.pull φ).ι) (j : K'.bundle.ι) (V : Y.Opens)
        (hV : V ≤ K.bundle.U (i PUnit.unit)) (W : Y'.Opens) (hW : W ≤ K'.bundle.U j)
        (h : W ≤ φ ⁻¹ᵁ V) (hw : W ≤ (LB.div (K.bundle.pull φ) K'.bundle).U (i, j))
        (f : Fin D → Γ(Y, V)),
        (φ.appLE V W h).hom (K.jacobian (i PUnit.unit) hV f) =
          resG Y' hw (w.s (i, j)).val * K'.jacobian j hW (fun a => (φ.appLE V W h).hom (f a)) :=
  ⟨K'.iso (K.baseChange H), K'.iso_isGen (K.baseChange H), fun i j _ hV _ hW h hw f =>
    (K.jacobian_baseChange H i hV (hw.trans inf_le_left) h f).symm.trans
      (K'.coeff_eq_iso_mul (K.baseChange H) i j _ hW _)⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVacuumMovedThetaVacuum
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVacuumMovedThetaVacuum
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.MovedVacuum

theorem isVacuum_thetaIntertwiner_selfDual (D : D7) (cc : Ideal (𝓞 D.host.K)) (dl t0 : ℂ) (hc : StandardLatticesGL3.Crv D cc dl)
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (TaylorLogMetric.lamOf D cc dl) t0) {a b : ℕ}
    {L L₁ : Submodule (𝓞 D.host.E) (Fin a → D.host.E)} {L' L₁' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)}
    (hL : StandardLatticesGL3.SD D L) (hL' : StandardLatticesGL3.SD D L') (hL₁ : StandardLatticesGL3.SD D L₁) (hL₁' : StandardLatticesGL3.SD D L₁')
    {G : TaylorLogMetric.VC D a b → ℂ} (hG : StandardLatticesGL3.ThetaVectorUpToUnits D (TaylorLogMetric.tor0 D cc dl) t0 L L' G) :
    StandardLatticesGL3.ThetaVectorUpToUnits D (TaylorLogMetric.tor0 D cc dl) t0 L₁ L₁'
      (TaylorLogMetric.Iop D (TaylorLogMetric.tor0 D cc dl) (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc dl) L L')
        (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc dl) L₁ L₁') G) := by
  obtain ⟨e, κ, he, hκ, rfl⟩ := hG
  obtain ⟨μ, hμ, h⟩ := GlobalTheory.TripleIntertwiner.triple_constant D cc dl hc a b _ _ _
    (Or.inl ⟨_, e, he, rfl⟩) (Or.inr ⟨L, L', hL, hL', rfl⟩) (Or.inr ⟨L₁, L₁', hL₁, hL₁', rfl⟩) _
    (GlobalTheory.VacuumMove.pullbackOrthonormal_normalizedTheta_mem_thetaSpace D (GlobalTheory.InducedType.induced_type D).1 cc dl t0 hc ht e he.1)
  refine ⟨e, κ * μ, he, GlobalTheory.VacuumMove.mod1All_mul hκ hμ, funext fun z => ?_⟩
  rw [GlobalTheory.VacuumMove.Iop_mul, mul_assoc κ μ]
  exact congrArg (κ * ·) (congrFun h z)

theorem sd_stdL (D : D7) (n : ℕ) : StandardLatticesGL3.SD D (StandardLatticesGL3.stdL D n) := by
  letI := D.host.cmStar
  exact GlobalTheory.SeamSelfDual.isSDLat_pi D.host.E n

theorem isVacuum_movedThetaVacuum : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (dl : ℂ) (B : Base D cc dl) (t0 : ℂ), StandardLatticesGL3.Crv D cc dl → GL3Theta.IsTwoTorsionPointUnkilled D (TaylorLogMetric.lamOf D cc dl) t0 → ∀ (a b : ℕ) (L : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), StandardLatticesGL3.SD D L → StandardLatticesGL3.SD D L' → StandardLatticesGL3.ThetaVectorUpToUnits D (TaylorLogMetric.tor0 D cc dl) t0 (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b) (B.thZero a b) → StandardLatticesGL3.ThetaVectorUpToUnits D (TaylorLogMetric.tor0 D cc dl) t0 L L' (B.thMoved a b L L') := by
  intro D cc dl B t0 hc ht a b L L' hL hL' h0
  exact isVacuum_thetaIntertwiner_selfDual D cc dl t0 hc ht hL (sd_stdL D b) hL hL'
    (isVacuum_thetaIntertwiner_selfDual D cc dl t0 hc ht (sd_stdL D a) (sd_stdL D b) hL (sd_stdL D b) h0)

end GlobalTheory.MovedVacuum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVacuumMovedThetaVacuumStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaVectorUpToUnits_thMoved_of_thZero : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (dl : ℂ) (B : Base D cc dl) (t0 : ℂ), StandardLatticesGL3.Crv D cc dl → GL3Theta.IsTwoTorsionPointUnkilled D (TaylorLogMetric.lamOf D cc dl) t0 → ∀ (a b : ℕ) (L : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), StandardLatticesGL3.SD D L → StandardLatticesGL3.SD D L' → StandardLatticesGL3.ThetaVectorUpToUnits D (TaylorLogMetric.tor0 D cc dl) t0 (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b) (B.thZero a b) → StandardLatticesGL3.ThetaVectorUpToUnits D (TaylorLogMetric.tor0 D cc dl) t0 L L' (B.thMoved a b L L') := by
  first | exact @GlobalTheory.MovedVacuum.isVacuum_movedThetaVacuum | exact GlobalTheory.MovedVacuum.isVacuum_movedThetaVacuum | (intros; apply GlobalTheory.MovedVacuum.isVacuum_movedThetaVacuum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDensityOfImmersion
noncomputable section

namespace GlobalTheory.SUVol

open MeasureTheory Filter Topology Matrix Metric Set
open scoped ENNReal NNReal

theorem exists_density_of_immersion (V M G : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (lam : Measure V) [lam.IsAddHaarMeasure] (μ : Measure G) [μ.IsHaarMeasure]
    (e : V → G) (m : G → M) (j : V →L[ℝ] M) (hj : Function.Injective j) (L : G → M →L[ℝ] M) (he : Continuous e)
    (h0 : e 0 = 1) (hd : HasStrictFDerivAt (fun x => m (e x)) j 0)
    (hL : ContinuousAt L 1) (hL1 : L 1 = ContinuousLinearMap.id ℝ M)
    (hm : ∀ g h, m (g * h) = L g (m h)) (hn : ∀ r : ℝ, 0 < r → e '' ball 0 r ∈ 𝓝 (1 : G)) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
      Tendsto (fun r : ℝ => μ (e '' ball 0 r) / lam (ball 0 r)) (𝓝[>] 0) (𝓝 c) := by
  obtain ⟨p₀, hp₀⟩ := (j : V →ₗ[ℝ] M).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hj)
  let p : M →L[ℝ] V := LinearMap.toContinuousLinearMap p₀
  have hp : ∀ v, p (j v) = v := fun v => LinearMap.congr_fun hp₀ v
  let E : M →L[ℝ] V × M := p.prod (ContinuousLinearMap.id ℝ M - j.comp p)
  let D : V × M →L[ℝ] M := j.coprod (ContinuousLinearMap.id ℝ M)
  have hDE : ∀ x, D (E x) = x := fun x => by simp [D, E]
  let J : V →ₗᵢ[ℝ] V × M := ⟨LinearMap.inl ℝ V M, fun v => by simp⟩
  have hJ : E.comp j = J.toContinuousLinearMap := by
    ext v <;> simp [E, J, hp]
  refine GlobalTheory.CompactDualExists.exists_density_of_chart V (V × M) G lam μ e (fun g => E (m g)) J
    (fun g => ContinuousLinearMap.id ℝ _ + E.comp ((L g - ContinuousLinearMap.id ℝ M).comp D)) he h0
    (hJ ▸ E.hasStrictFDerivAt.comp 0 hd) ?_ (by simp [hL1]) (fun g h => ?_) hn
  · exact continuousAt_const.add (continuousAt_const.clm_comp ((hL.sub continuousAt_const).clm_comp
      continuousAt_const))
  · simp [hm, hDE]

section OneMatrix

variable {r : ℕ}

theorem det_exp (X : Matrix (Fin r) (Fin r) ℂ) : (NormedSpace.exp X).det = Complex.exp X.trace := by
  have hder : HasDerivAt (fun t : ℝ => (NormedSpace.exp (t • X)).det) X.trace 0 := by
    have h1 : ∀ a b, HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X) a b) (X a b) 0 := by
      intro a b
      open scoped Matrix.Norms.Operator in
      have h2 := ((Matrix.entryLinearMap ℝ ℂ a b).toContinuousLinearMap.hasFDerivAt).comp_hasDerivAt 0
        (hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0)
      rw [zero_smul, NormedSpace.exp_zero, one_mul] at h2
      exact h2
    have h3 := ReciprocityTheory.GeometryOfNumbersTheory.hasDerivAt_det (fun t : ℝ => NormedSpace.exp (t • X)) X 0 h1
    simpa only [zero_smul, NormedSpace.exp_zero, Matrix.adjugate_one, Matrix.one_mul] using h3
  have hadd : ∀ s t : ℝ,
      NormedSpace.exp ((s + t) • X) = NormedSpace.exp (s • X) * NormedSpace.exp (t • X) := by
    intro s t
    rw [add_smul]
    exact Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left s).smul_right t)
  set f : ℝ → ℂ := fun t => (NormedSpace.exp (t • X)).det with hf
  have hd : ∀ t, HasDerivAt f (f t * X.trace) t := by
    intro t
    have h0 : HasDerivAt f X.trace (t - t) := by
      rw [sub_self]; exact hder
    have h1 := (h0.comp_sub_const t t).const_mul (f t)
    refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    simp only [hf]
    rw [← Matrix.det_mul, ← hadd, add_sub_cancel]
  have hg : ∀ t : ℝ, HasDerivAt (fun s : ℝ => f s * Complex.exp (-(s * X.trace))) 0 t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => -((s : ℂ) * X.trace)) (-X.trace) t := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const X.trace).fun_neg
    exact ((hd t).fun_mul h1.cexp).congr_deriv (by ring)
  have h2 := is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt) (fun t => (hg t).deriv) 1 0
  simp only [hf, one_smul, zero_smul, NormedSpace.exp_zero, Matrix.det_one, Complex.ofReal_one, one_mul,
    Complex.ofReal_zero, zero_mul, neg_zero, Complex.exp_zero, Complex.exp_neg] at h2
  exact (mul_inv_eq_one₀ (Complex.exp_ne_zero _)).1 h2

theorem map_conj_eq (A : Matrix (Fin r) (Fin r) ℂ) : A.map (starRingEnd ℂ) = Aᴴᵀ := rfl

theorem exp_map_conj (A : Matrix (Fin r) (Fin r) ℂ) :
    NormedSpace.exp (A.map (starRingEnd ℂ)) = (NormedSpace.exp A).map (starRingEnd ℂ) := by
  rw [map_conj_eq, map_conj_eq, Matrix.exp_transpose, Matrix.exp_conjTranspose]

def twist (H X : Matrix (Fin r) (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  (H * (-X).map (starRingEnd ℂ) * H⁻¹)ᵀ

theorem continuous_twist (H : Matrix (Fin r) (Fin r) ℂ) : Continuous (twist H) :=
  ((continuous_const.matrix_mul (continuous_neg.matrix_map Complex.continuous_conj)).matrix_mul
    continuous_const).matrix_transpose

variable {H : Matrix (Fin r) (Fin r) ℂ}

theorem twist_transpose_mul (hH : H.det ≠ 0) (X : Matrix (Fin r) (Fin r) ℂ) :
    (twist H X)ᵀ * H = -(H * X.map (starRingEnd ℂ)) := by
  rw [twist, transpose_transpose, Matrix.nonsing_inv_mul_cancel_right _ _ hH.isUnit,
    Matrix.map_neg _ (map_neg _), Matrix.mul_neg]

theorem twist_eq_iff (hH : H.det ≠ 0) (X : Matrix (Fin r) (Fin r) ℂ) :
    twist H X = X ↔ Xᵀ * H + H * X.map (starRingEnd ℂ) = 0 := by
  constructor
  · intro h
    have := twist_transpose_mul hH X
    rw [h] at this
    rw [this, neg_add_cancel]
  · intro h
    rw [twist, Matrix.map_neg _ (map_neg _), Matrix.mul_neg, ← eq_neg_of_add_eq_zero_left h,
      Matrix.mul_nonsing_inv_cancel_right _ _ hH.isUnit, transpose_transpose]

theorem exp_twist (hH : H.det ≠ 0) (X : Matrix (Fin r) (Fin r) ℂ) :
    (NormedSpace.exp (twist H X))ᵀ * H * (NormedSpace.exp X).map (starRingEnd ℂ) = H := by
  rw [twist, Matrix.exp_transpose, transpose_transpose,
    Matrix.exp_conj _ _ ((Matrix.isUnit_iff_isUnit_det _).2 hH.isUnit),
    Matrix.nonsing_inv_mul_cancel_right _ _ hH.isUnit, exp_map_conj, Matrix.mul_assoc, ← Matrix.map_mul,
    GlobalTheory.UpqExpChart.exp_neg_mul_exp]
  simp

theorem exp_twist_eq (hH : H.det ≠ 0) {X : Matrix (Fin r) (Fin r) ℂ}
    (h : (NormedSpace.exp X)ᵀ * H * (NormedSpace.exp X).map (starRingEnd ℂ) = H) :
    NormedSpace.exp (twist H X) = NormedSpace.exp X := by
  have h1 := (exp_twist hH X).trans h.symm
  have h2 := congrArg (fun A => A * (NormedSpace.exp (-X)).map (starRingEnd ℂ) * H⁻¹) h1
  simp only [Matrix.mul_assoc _ ((NormedSpace.exp X).map (starRingEnd ℂ)), ← Matrix.map_mul,
    GlobalTheory.UpqExpChart.exp_mul_exp_neg, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one,
    Matrix.mul_nonsing_inv_cancel_right _ _ hH.isUnit] at h2
  exact transpose_injective h2

end OneMatrix

variable {ι : Type} {r : ℕ} {H : ι → Matrix (Fin r) (Fin r) ℂ}


end GlobalTheory.SUVol
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfValEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfValEqZero
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ValInj

theorem eq_zero_of_val_eq_zero : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A →
    ∀ (U : A.left.Opens) (b : Γ(A.left, U)), (∀ z ∈ pre u.ex U, val u.ex U b z = 0) → b = 0 := by
  intro A _ g L u hA U b hb
  haveI : Smooth A.hom := hA.smooth
  haveI : IsReduced A.left := isReduced_of_smooth A.hom
  refine GlobalTheory.ComplexPoints.eq_of_valAt'_eq A.hom U b 0 fun x hx hxU => ?_
  obtain ⟨z, hz⟩ := u.ex_onto (Over.homMk x hx)
  have hzx : (u.ex z).left = x := by rw [hz]; rfl
  have h1 : val u.ex U b z = 0 := hb z (by show ⊤ ≤ (u.ex z).left ⁻¹ᵁ U; rw [hzx]; exact hxU)
  rw [show val u.ex U b z = valAt' (u.ex z).left U b from rfl, hzx] at h1
  rw [h1]
  unfold valAt' valAt
  split_ifs <;> simp

end GlobalTheory.ValInj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfValEqZeroStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_val_eq_zero_abelian : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (U : A.left.Opens) (b : Γ(A.left, U)), (∀ z ∈ pre u.ex U, val u.ex U b z = 0) → b = 0 := by
  first | exact @GlobalTheory.ValInj.eq_zero_of_val_eq_zero | exact GlobalTheory.ValInj.eq_zero_of_val_eq_zero | (intros; apply GlobalTheory.ValInj.eq_zero_of_val_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantThird
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.ColNormsUnit

theorem mem_of_divs {A : Type} [CommRing A] [IsDedekindDomain A] {a : A} {P : HeightOneSpectrum A} (h : P ∈ divs a) :
    a ∈ P.asIdeal := by
  unfold divs at h
  split_ifs at h with hf
  · exact hf.mem_toFinset.1 h
  · simp at h

theorem qe_one {X : Fields} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {Sg : Set ℕ} :
    QE sel ((1 : Tup X.F X.E X.K Sg) : Chr X.F X.E X.K) = ∅ := by
  have h : Qprime ((1 : Tup X.F X.E X.K Sg) : Chr X.F X.E X.K) = ∅ := by
    change Qprime (1 : Chr X.F X.E X.K) = ∅
    ext v
    simp [Qprime, MonoidHom.ker_one]
  unfold QE
  split_ifs with hf
  · rw [(Set.Finite.toFinset_eq_empty (h := hf)).2 h]
    rfl
  · rfl

theorem exists_prime {X : Fields} {Pr : Primes X} (hPr : Pr.Ok) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E))
    {Sg : Set ℕ} (u : Pr.Word) (P : HeightOneSpectrum (𝓞 X.E)) (hP : P ∈ Sall sel (1 : Tup X.F X.E X.K Sg) u) :
    ∃ l : ℕ, l.Prime ∧ (l : 𝓞 X.E) ∈ P.asIdeal ∧ ¬ l ∣ Pr.cond := by
  classical
  have hg : ∀ i, P ∈ Pr.vG i → ∃ l : ℕ, l.Prime ∧ (l : 𝓞 X.E) ∈ P.asIdeal ∧ ¬ l ∣ Pr.cond := by
    intro i hi
    refine ⟨Pr.g i, hPr.g_prime i, hPr.piG_norm i ▸ P.asIdeal.mul_mem_left _ (mem_of_divs hi), fun hd => ?_⟩
    have h1 : Pr.g i ≡ 1 [MOD Pr.g i] := (hPr.g_cong i).of_dvd hd
    have h2 : Pr.g i ∣ 1 := (Nat.modEq_zero_iff_dvd).1 (h1.symm.trans ((Nat.modEq_zero_iff_dvd).2 dvd_rfl))
    exact (hPr.g_prime i).one_lt.ne' (Nat.dvd_one.1 h2)
  unfold Sall at hP
  simp only [rowSG, uSG, qe_one, Primes.vGs, Finset.mem_union, Finset.notMem_empty, or_false] at hP
  rcases hP with h | h | h
  · have h0 : Pr.piT u ∈ P.asIdeal := mem_of_divs h
    have hT : (Pr.T u : 𝓞 X.E) ∈ P.asIdeal := hPr.piT_norm u ▸ P.asIdeal.mul_mem_right _ h0
    refine ⟨Pr.T u, hPr.T_prime u, hT, fun hd => ?_⟩
    have h1 : (Pr.T u : 𝓞 X.E) ∣ Pr.piT u - 1 :=
      (Nat.cast_dvd_cast (hd.mul_right _)).trans (hPr.piT_cong u)
    have h2 : Pr.piT u - 1 ∈ P.asIdeal := Ideal.mem_of_dvd _ h1 hT
    have h3 := P.asIdeal.sub_mem h0 h2
    rw [sub_sub_cancel] at h3
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h3)
  · exact hg 0 h
  · exact hg 1 h

end GlobalTheory.ColNormsUnit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantFourth
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.ColNorms.MovedDatum

section Gen

variable {E K : Type} [Field E] [NumberField E] [Field K] {P : HeightOneSpectrum (𝓞 E)}

theorem norm_unitV (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {a : E} (h : IsUnit (redP P a)) (σ : K →+* ℂ) :
    ‖σ (LocE.unitV χ a)‖ = 1 := by
  unfold LocE.unitV
  rw [dite_eq_left h]
  have : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  have hc : 0 < Nat.card (𝓞 E ⧸ P.asIdeal)ˣ := Nat.card_pos
  have h1 : ((χ h.unit : Kˣ) : K) ^ Nat.card (𝓞 E ⧸ P.asIdeal)ˣ = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]
  have h2 : ‖σ ((χ h.unit : Kˣ) : K)‖ ^ Nat.card (𝓞 E ⧸ P.asIdeal)ˣ = 1 := by
    rw [← norm_pow, ← map_pow, h1, map_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hc.ne').1 h2

variable [StarRing E]

theorem locSmall_om {a b : ℕ} {e e' : ℕ → ℤ} (cq sq : K) (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)
    {g : Sp E a ≃ₗ[E] Sp E a} {g' : Sp E b ≃ₗ[E] Sp E b}
    (hg : g ∈ stabL E a (LocE.sclLat P (qOf P) a e)) (hg' : g' ∈ stabL E b (LocE.sclLat P (qOf P) b e'))
    {Φ : HomE E a b → K} {β : ℝ}
    (hΦ : LocSmall (qOf P) (LocE.sclLat P (qOf P) a e) (LocE.sclLat P (qOf P) b e') Φ β) :
    LocSmall (qOf P) (LocE.sclLat P (qOf P) a e) (LocE.sclLat P (qOf P) b e')
      (Loc.om (LocE.locChar (qOf P) cq χ) (LocE.vP P (qOf P)) sq g g' Φ) β := by
  have hu := GlobalTheory.LastSteps.isUnit_det_of_stab hg
  have hu' := GlobalTheory.LastSteps.isUnit_det_of_stab hg'
  obtain ⟨h1, h2, h3⟩ := hΦ
  refine ⟨fun x hx y hy => ?_, fun x z hz => ?_, fun σ x => ?_⟩
  · unfold Loc.om at hx
    have h4 := h1 _ (right_ne_zero_of_mul hx) (g.symm y) ((hg _).1 (by simpa using hy))
    have h5 := (hg' _).2 h4
    simpa using h5
  · unfold Loc.om
    congr 1
    have h4 := h2 (g'.symm.toLinearMap ∘ₗ x ∘ₗ g.toLinearMap) (g'.symm.toLinearMap ∘ₗ z ∘ₗ g.toLinearMap) fun y hy =>
      (hg' _).1 (by simpa using hz _ ((hg y).2 hy))
    rw [← h4]
    congr 1
    refine LinearMap.ext fun y => ?_
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply, map_add (f := _), map_smul]
  · have locChar_eq_unitV {x : E} (hx : IsUnit (redP P x)) :
        LocE.locChar (qOf P) cq χ x = LocE.unitV χ x := by
      simp [LocE.locChar, GlobalTheory.LastSteps.vP_unit hx]
    unfold Loc.om
    rw [locChar_eq_unitV hu, locChar_eq_unitV hu', GlobalTheory.LastSteps.vP_unit hu,
      GlobalTheory.LastSteps.vP_unit hu']
    simp only [neg_zero, zero_mul, zpow_zero, mul_one, map_mul, map_inv₀, norm_mul, norm_inv, norm_unitV χ hu,
      norm_unitV χ hu', inv_one, one_mul]
    exact h3 σ _

end Gen

end GlobalTheory.ColNorms.MovedDatum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPullbackEllipticModel
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PowFibre

section Pow

variable {S : Scheme.{0}} {G₀ G : Over S} [GrpObj G₀] [GrpObj G] {j : ℕ} (p : Out.IsPowGrp G₀ G j)

theorem over_ext {T : Over S} {a b : T ⟶ G₀} (h : ∀ i, a ≫ p.pr i = b ≫ p.pr i) : a = b :=
  p.lim.hom_ext fun ⟨i⟩ => h i

theorem left_ext {T : Scheme.{0}} {a b : T ⟶ G₀.left} (h₀ : a ≫ G₀.hom = b ≫ G₀.hom)
    (h : ∀ i, a ≫ (p.pr i).left = b ≫ (p.pr i).left) : a = b := by
  have := over_ext p (T := Over.mk (b ≫ G₀.hom)) (a := Over.homMk a h₀) (b := Over.homMk b rfl)
    fun i => Over.OverMorphism.ext (h i)
  exact congrArg (·.left) this

theorem exists_left_lift {T : Scheme.{0}} (s : T ⟶ S) (a : Fin j → (T ⟶ G.left)) (ha : ∀ i, a i ≫ G.hom = s) :
    ∃ x : T ⟶ G₀.left, x ≫ G₀.hom = s ∧ ∀ i, x ≫ (p.pr i).left = a i := by
  let c : Fan (fun _ : Fin j => G) := Fan.mk (Over.mk s) fun i => Over.homMk (a i) (ha i)
  exact ⟨(p.lim.lift c).left, Over.w (p.lim.lift c), fun i => congrArg (·.left) (p.lim.fac c ⟨i⟩)⟩

end Pow

section Pull

variable {S S' : Scheme.{0}} {G₀ G : Over S} [GrpObj G₀] [GrpObj G] {G₀' G' : Over S'} [GrpObj G₀'] [GrpObj G']
  {j : ℕ} {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

theorem exists_pow_pullback (p : Out.IsPowGrp G₀ G j) (p' : Out.IsPowGrp G₀' G' j) (h : IsGrpPullback G' G f φ) :
    ∃ φ₀ : G₀'.left ⟶ G₀.left, IsGrpPullback G₀' G₀ f φ₀ ∧ ∀ i, φ₀ ≫ (p.pr i).left = (p'.pr i).left ≫ φ := by
  obtain ⟨φ₀, hw, hφ₀⟩ := exists_left_lift p (G₀'.hom ≫ f) (fun i => (p'.pr i).left ≫ φ) fun i => by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w]
  refine ⟨φ₀, ⟨⟨⟨hw⟩, ⟨?_⟩⟩, fun T x y x₀ y₀ hx hy => ?_⟩, hφ₀⟩
  · have hs : ∀ (s : PullbackCone G₀.hom f) (i : Fin j), (s.fst ≫ (p.pr i).left) ≫ G.hom = s.snd ≫ f :=
      fun s i => by rw [Category.assoc, Over.w, s.condition]
    choose l hl₁ hl₂ using fun s : PullbackCone G₀.hom f =>
      exists_left_lift p' s.snd (fun i => h.1.lift _ _ (hs s i)) fun i => h.1.lift_snd _ _ _
    refine PullbackCone.IsLimit.mk _ l (fun s => left_ext p ?_ fun i => ?_) hl₁
      fun s m h₁ h₂ => left_ext p' (h₂.trans (hl₁ s).symm) fun i => ?_
    · rw [Category.assoc, hw, ← Category.assoc, hl₁, s.condition]
    · rw [Category.assoc, hφ₀, ← Category.assoc, hl₂, h.1.lift_fst]
    · rw [hl₂]
      refine h.1.hom_ext ?_ ?_
      · rw [h.1.lift_fst, Category.assoc, ← hφ₀, ← Category.assoc, h₁]
      · rw [h.1.lift_snd, Category.assoc, Over.w, h₂]
  · refine left_ext p ?_ fun i => ?_
    · rw [Over.w, Category.assoc, hw, ← Category.assoc, Over.w]
      rfl
    · have := p.hom i
      have := p'.hom i
      have e := h.2 T (x ≫ p'.pr i) (y ≫ p'.pr i) (x₀ ≫ p.pr i) (y₀ ≫ p.pr i)
        (by rw [Over.comp_left, Over.comp_left, hx, Category.assoc, Category.assoc, hφ₀])
        (by rw [Over.comp_left, Over.comp_left, hy, Category.assoc, Category.assoc, hφ₀])
      rw [← MonObj.mul_comp, ← MonObj.mul_comp, Over.comp_left, Over.comp_left] at e
      rw [e, Category.assoc, Category.assoc, hφ₀]

end Pull



end GlobalTheory.PowFibre

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantEleventh
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.IndexCount

open Formalism.L2.Col.Loc Formalism.L2.Col.LocE GlobalTheory.RowTypeInv GlobalTheory.SymLevelDatum

section

variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ)

theorem sclLat_anti (hq : q ≠ 0) {N : ℕ} {e e' : ℕ → ℤ} (h : ∀ l, e l ≤ e' l) : sclLat P q N e' ≤ sclLat P q N e := by
  have hq' : (q : E) ≠ 0 := Nat.cast_ne_zero.2 hq
  intro x hx
  rw [mem_sclLat] at hx ⊢
  intro l
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.2 (h l.1))
  have h1 : IntAt P ((q : E) ^ k) := (intRing P).pow_mem (intAt_natCast P q) k
  convert h1.mul (hx l) using 1
  rw [show e' l.1 = e l.1 + k by omega, zpow_add₀ hq', zpow_natCast]
  field_simp

theorem mem_sclLat_succ (hq : q ≠ 0) {N : ℕ} (e : ℕ → ℤ) (x : Sp E N) :
    x ∈ sclLat P q N (fun l => e l + 1) ↔ (q : E)⁻¹ • x ∈ sclLat P q N e := by
  have hq' : (q : E) ≠ 0 := Nat.cast_ne_zero.2 hq
  rw [mem_sclLat, mem_sclLat]
  refine forall_congr' fun l => ?_
  rw [zpow_add₀ hq', zpow_one, Pi.smul_apply, smul_eq_mul, mul_inv, mul_assoc]

theorem mem_stabL_of_cong {N : ℕ} {M₀ M M₁ : Submodule (𝓞 E) (Sp E N)} (h₀ : M₀ ≤ M) (h₁ : M ≤ M₁)
    {κ : Sp E N ≃ₗ[E] Sp E N} (hκ : κ ∈ stabL E N M₁) (hc : ∀ y ∈ M₁, κ y - y ∈ M₀) : κ ∈ stabL E N M := by
  intro x
  constructor
  · intro hx
    simpa using M.sub_mem hx (h₀ (hc x ((hκ x).1 (h₁ hx))))
  · intro hx
    simpa using M.add_mem (h₀ (hc x (h₁ hx))) hx

noncomputable def resMat {N : ℕ} (e : ℕ → ℤ) (h : Sp E N ≃ₗ[E] Sp E N) : Fin N × Fin N → 𝓞 E ⧸ P.asIdeal :=
  fun p => redP P (h (eN E N p.2.1) p.1 * (q : E) ^ (e p.2.1 - e p.1.1))

theorem cong_of_resMat_eq (hq : q ≠ 0) (hdiv : ∀ a : E, IntAt P a → redP P a = 0 → IntAt P (a / (q : E)))
    {N : ℕ} {e : ℕ → ℤ} {h h' : Sp E N ≃ₗ[E] Sp E N} (hh : h ∈ stabL E N (sclLat P q N e))
    (hh' : h' ∈ stabL E N (sclLat P q N e)) (hres : resMat P q e h = resMat P q e h') :
    ∀ y ∈ sclLat P q N e, (h⁻¹ * h') y - y ∈ sclLat P q N (fun l => e l + 1) := by
  have hq' : (q : E) ≠ 0 := Nat.cast_ne_zero.2 hq
  have a1 := (maps_iff P q hq e e h.toLinearMap).1 fun y hy => (hh y).2 hy
  have a2 := (maps_iff P q hq e e h'.toLinearMap).1 fun y hy => (hh' y).2 hy
  have a3 := (maps_iff P q hq e (fun l => e l + 1) (h'.toLinearMap - h.toLinearMap)).2 fun l l' => by
    have b1 : IntAt P (h' (eN E N l'.1) l * (q : E) ^ (e l'.1 - e l.1) - h (eN E N l'.1) l * (q : E) ^ (e l'.1 - e l.1)) :=
      (intRing P).sub_mem (a2 l l') (a1 l l')
    have b2 := reduction_add b1 (a1 l l')
    have b3 : redP P (h (eN E N l'.1) l * (q : E) ^ (e l'.1 - e l.1)) =
      redP P (h' (eN E N l'.1) l * (q : E) ^ (e l'.1 - e l.1)) := congrFun hres (l, l')
    erw [sub_add_cancel, b3, right_eq_add] at b2
    convert hdiv _ b1 b2 using 1
    rw [show e l'.1 - (e l.1 + 1) = e l'.1 - e l.1 - 1 by ring, zpow_sub_one₀ hq']
    simp only [LinearMap.sub_apply, Pi.sub_apply, LinearEquiv.coe_coe]
    field_simp
  intro y hy
  have a4 := a3 y hy
  rw [mem_sclLat_succ P q hq] at a4 ⊢
  rw [← hh, map_smul, map_sub]
  simpa using a4

theorem mem_JGsym_of_cong (hq : q ≠ 0) (k rS r t n c : ℕ) {κ : Sp E (n + c) ≃ₗ[E] Sp E (n + c)}
    (hκ : κ ∈ stabL E (n + c) (lamY P q n c fun i => i + 1))
    (hc : ∀ y ∈ lamY P q n c fun i => i + 1, κ y - y ∈ sclLat P q (n + c) (fun l => scE n (fun i => i + 1) l + 1)) :
    κ ∈ JGsym P q k rS r t n c := by
  have h₀ : ∀ s, sclLat P q (n + c) (fun l => scE n (fun i => i + 1) l + 1) ≤ flagS P q k rS n c s := fun s =>
    sclLat_anti P q hq fun l => by split_ifs <;> omega
  have h₁ : ∀ s, flagS P q k rS n c s ≤ lamY P q n c fun i => i + 1 := fun s =>
    sclLat_anti P q hq fun l => by split_ifs <;> omega
  refine ⟨hκ, fun s _ => mem_stabL_of_cong (h₀ s) (h₁ s) hκ hc, fun s _ => ⟨mem_stabL_of_cong (h₀ s) (h₁ s) hκ hc, h₀ s (hc _ ?_)⟩⟩
  have hq' : (q : E) ≠ 0 := Nat.cast_ne_zero.2 hq
  unfold lamY bvecS bvecG
  rw [mem_sclLat]
  intro i
  by_cases hi : i.1 = fIdx k c n (symIdxInv k rS s)
  · simp only [Pi.smul_apply, eN, hi, if_true, smul_eq_mul, mul_one]
    rw [inv_mul_cancel₀ (zpow_ne_zero _ hq')]
    exact intAt_one P
  · simp only [Pi.smul_apply, eN, hi, if_false, smul_eq_mul, mul_zero]
    exact intAt_zero P

end

end GlobalTheory.IndexCount
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalMirabolicHolds
namespace GlobalTheory

theorem cuspidalMirabolic_holds : GlobalTheory.Published.CuspidalMirabolic :=
  CompanionTheory.Mirab.cuspidalMirabolic

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeAndPullOfIsGrpPullback
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory.GrpPullbackPol

theorem isAbelianScheme_and_pull_of_isGrpPullback :
    ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (A : Over S) [GrpObj A] [IsCommMonObj A] (A' : Over S')
      [GrpObj A'] [IsCommMonObj A'] (φ : A'.left ⟶ A.left) (L : LB A.left),
      IsGrpPullback A' A f φ → IsAbelianScheme A → L.IsLB → Out.Rigidified A L →
        Out.RelAmple A L →
        IsAbelianScheme A' ∧ (L.pull φ).IsLB ∧ Out.Rigidified A' (L.pull φ) ∧
          Out.RelAmple A' (L.pull φ) := by
  intro S S' f A _ _ A' _ _ φ L h hA hL hr ha
  have hp : IsProper A.hom := hA.proper
  refine ⟨⟨inferInstance, ?_, ?_, ?_⟩, pull_isLB hL φ, PolBaseChange.rigidified_pull h hr, ?_⟩
  · exact MorphismProperty.of_isPullback (P := @Smooth) h.1 hA.smooth
  · exact MorphismProperty.of_isPullback (P := @IsProper) h.1 hA.proper
  · exact MorphismProperty.of_isPullback (P := @GeometricallyConnected) h.1 hA.geomConnected
  · exact AmpleBaseChange.relAmple_of_isPullback hL ha h.1

end GlobalTheory.GrpPullbackPol
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRapidSuperpositionCharacters
open MeasureTheory GlobalTheory.JSW
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW

theorem exists_rapid_superposition_characters :
    ∀ (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] (Φ : Z → ℂ), ContDiff ℝ ∞ Φ → HasCompactSupport Φ → ∃ (X : Type) (_ : MeasurableSpace X) (ν : Measure X) (_ : SFinite ν) (κ : X → ℂ) (τ : X → Z →L[ℝ] ℝ), Measurable κ ∧ (∀ z, Measurable fun x => τ x z) ∧ (∀ N : ℕ, Integrable (fun x => ‖κ x‖ * (1 + ‖τ x‖) ^ N) ν) ∧ ∀ z, Φ z = ∫ x, κ x * (𝐞 (τ x z) : ℂ) ∂ν := by
  intro Z _ _ _ Φ hΦ hc
  obtain ⟨m, A, φ, hφ, hint, hinv⟩ := GlobalTheory.fourier_inversion_real_linear_forms (hc.toSchwartzMap hΦ)
  let B : EuclideanSpace ℝ (Fin m) →L[ℝ] (Z →L[ℝ] ℝ) := (2 * Real.pi)⁻¹ • A
  have hB : ∀ w z, 2 * Real.pi * B w z = A w z := by
    intro w z
    have : (2 * Real.pi) ≠ 0 := by positivity
    simp only [B, ContinuousLinearMap.smul_apply, smul_eq_mul]
    field_simp
  refine ⟨EuclideanSpace ℝ (Fin m), inferInstance, volume, inferInstance, φ, fun w => B w,
    hφ.measurable, fun z => ?_, fun N => ?_, fun z => ?_⟩
  · exact (by fun_prop : Continuous fun x => B x z).measurable
  · refine ((hint N).const_mul ((1 + ‖B‖) ^ N)).mono' ?_ (Filter.Eventually.of_forall fun w => ?_)
    · exact (by fun_prop : Continuous fun x => ‖φ x‖ * (1 + ‖B x‖) ^ N).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), ← mul_assoc, ← mul_pow, mul_comm]
      refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) ?_ N) (norm_nonneg _)
      have h1 := B.le_opNorm w
      nlinarith [norm_nonneg B, norm_nonneg w]
  · have h := hinv z
    have h0 : (hc.toSchwartzMap hΦ) z = Φ z := rfl
    rw [h0] at h
    rw [h]
    congr 1
    ext w
    rw [Real.fourierChar_apply, hB]

end GlobalTheory.JSW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsEmbedOfBaseChangeStableBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsEmbedOfBaseChangeStableBasis
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.HomFixUniv

theorem embedsBy_fA_of_isBCBasis (Rg : Type) [CommRing Rg] (B : Over (Sp Rg)) [GrpObj B] (M : LB B.left) (k mB : ℕ)
    (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (hB : IsAbelianScheme B) (hM : M.IsLB) (_hk : 1 ≤ k)
    (hVA : VeryAmpleAt B M k) (hb : IsBCBasis B M k bB) : GlobalTheory.AmpleSpan.EmbedsBy (GlobalTheory.HomFixUniv.fA B) bB := by
  have hp : IsProper B.hom := hB.proper
  let t : Spec (CommRingCat.of Rg) ⟶ (topS Rg).left := (Sp Rg).topIso.inv
  choose b' hb' using fun i => GlobalTheory.AbLaw.SecBC.exists_pullSec B M (k : ℤ) (homAt t) (bB i)
  have hspan := (hb Rg t b' hb').2
  have hE := GlobalTheory.AmpleSpan.embedsBy_baseAt B hM hVA (isAffineOpen_top (Sp Rg)) t b' hspan
  have hS := fun i => GlobalTheory.SpanFrame.secScal_of_isPullSec B hM (k : ℤ) (homAt t) (hb' i)
  haveI : IsIso (homAt t) := by
    haveI : IsIso ((Over.forget _).map (homAt t)) := by change IsIso t; infer_instance
    exact isIso_of_reflects_iso (homAt t) (Over.forget _)
  haveI : IsIso (homAt t ▷ B).left := inferInstanceAs (IsIso ((Over.forget _).map (homAt t ▷ B)))
  haveI : IsAffine (baseAt t).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of Rg)))
  have hw : (homAt t ▷ B).left ≫ fA B = (fst (baseAt t) B).left ≫ 𝟙 _ := by
    have e1 := Over.w (homAt t ▷ B)
    have e2 := Over.w (fst (baseAt t) B)
    have e3 : (baseAt t).hom = 𝟙 _ := by simp [baseAt, t, baseOver]
    rw [Category.comp_id, fA, e1, ← e2, e3, Category.comp_id]
  have sq : IsPullback (inv (homAt t ▷ B).left) (fA B) (fst (baseAt t) B).left (𝟙 _) := by
    refine IsPullback.of_horiz_isIso ⟨?_⟩
    rw [IsIso.inv_comp_eq, Category.comp_id, hw, Category.comp_id]
  exact GlobalTheory.AmpleSpan.EmbedsBy.secScal hM sq hE
    fun i => GlobalTheory.AmpleSpan.secScal_symm hM (hS i) (IsIso.inv_hom_id _)

end GlobalTheory.HomFixUniv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsEmbedOfBaseChangeStableBasisStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sectionsEmbed_of_baseChangeStableBasis : ∀ (Rg : Type) [CommRing Rg] (B : Over (Sp Rg)) [GrpObj B] (M : LB B.left) (k mB : ℕ) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))), IsAbelianScheme B → M.IsLB → 1 ≤ k → VeryAmpleAt B M k → IsBCBasis B M k bB → GlobalTheory.AmpleSpan.EmbedsBy (GlobalTheory.HomFixUniv.fA B) bB := by
  first | (exact @GlobalTheory.HomFixUniv.embedsBy_fA_of_isBCBasis) | (exact GlobalTheory.HomFixUniv.embedsBy_fA_of_isBCBasis) | (intros; apply GlobalTheory.HomFixUniv.embedsBy_fA_of_isBCBasis  <;> assumption)
end
end
