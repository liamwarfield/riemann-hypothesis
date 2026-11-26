module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionPointActionPeriodValueFractionFiel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCohomologyTrivialBundleAbelian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftValuationSubring
public import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupHomCharacterMapConstant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveFamilyRepresentativeZariskiGlue
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSymmetricFunctionsDegreeFactorialBasicPrope
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedDataBaseChangeSymmetric

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrFactorPointPadicAlgClosure
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrFactorPointPadicAlgClosure
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

theorem GlobalTheory.ValPt.exists_dvr_factor : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M : RatModel o Ω) (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V], IsAdicComplete (maximalIdeal V) V → ∀ (κ : FractionRing V →+* PadicAlgCl p), (∀ x, ‖κ x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) → ∀ y : Sp (OO p) ⟶ M.Z, ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (fV : V →+* V') (fK : FractionRing V →+* FractionRing V') (κ' : FractionRing V' →+* PadicAlgCl p) (iV : V' →+* OO p) (ξ : Sp V' ⟶ M.Z), IsLocalHom fV ∧ (∀ x, fK (algebraMap V _ x) = algebraMap V' _ (fV x)) ∧ κ'.comp fK = κ ∧ IsLocalHom iV ∧ (∀ x, (iV x : PadicAlgCl p) = κ' (algebraMap V' _ x)) ∧ spMap iV ≫ ξ = y := by
  intro o Ω _ _ _ _ M p _ V _ _ _ hc κ hV y

  haveI : CharZero (FractionRing V) := κ.charZero
  haveI : CharZero V := (algebraMap V (FractionRing V)).charZero
  set x : M.Z := y (cPt p) with hxdef
  obtain ⟨φ, hφloc, hφ, -⟩ := GlobalTheory.ValPt.exists_unique_stalk_hom M.Z x p y rfl
  obtain ⟨U, hU, hxU, hft⟩ := GlobalTheory.RatModel.exists_affineOpen_finiteType_int o Ω M x
  have hQ := GlobalTheory.PadicUnitBall.padic_mem_range p V hc κ hV
  let y₀ : Γ(M.Z, U) →+* PadicAlgCl p := (OO p).subtype.comp (φ.comp (M.Z.presheaf.germ U x hxU).hom)
  obtain ⟨W, _, _, _, hcW, _, fV, fK, κ', -, hfVloc, -, hfK, hκ', hW, hy₀⟩ :=
    GlobalTheory.DvrFinExt.exists_finite_extension p V hc κ hV hQ Γ(M.Z, U) y₀
  let j : W →+* PadicAlgCl p := κ'.comp (algebraMap W (FractionRing W))
  have hj : Function.Injective j :=
    κ'.injective.comp (IsFractionRing.injective W (FractionRing W))
  let ψ : M.Z.presheaf.stalk x →+* PadicAlgCl p := (OO p).subtype.comp φ

  have hψK : ∀ s, ψ s ∈ κ'.range := by
    intro s
    let xU : U := ⟨x, hxU⟩
    letI := M.Z.presheaf.algebra_section_stalk xU
    haveI := hU.isLocalization_stalk xU
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (hU.primeIdealOf xU).asIdeal.primeCompl (show M.Z.presheaf.stalk (xU : M.Z) from s)
    have hb : IsUnit (algebraMap Γ(M.Z, U) (M.Z.presheaf.stalk (xU : M.Z)) (b : Γ(M.Z, U))) :=
      IsLocalization.map_units _ b
    have hb' : ψ (algebraMap Γ(M.Z, U) (M.Z.presheaf.stalk (xU : M.Z)) (b : Γ(M.Z, U))) ≠ 0 :=
      ((hb.map φ).map (OO p).subtype).ne_zero
    have hga : ∀ c : Γ(M.Z, U), ψ (algebraMap Γ(M.Z, U) (M.Z.presheaf.stalk (xU : M.Z)) c) = y₀ c := fun c => rfl
    obtain ⟨ka, hka⟩ := hy₀ a
    obtain ⟨kb, hkb⟩ := hy₀ (b : Γ(M.Z, U))
    have e1 : ψ s * y₀ b = y₀ a := by
      rw [← hga, ← hga, ← map_mul, hab]
    have hb'' : y₀ b ≠ 0 := by rw [← hga]; exact hb'
    refine ⟨ka * kb⁻¹, ?_⟩
    rw [map_mul, map_inv₀, hka, hkb, ← e1, mul_inv_cancel_right₀ hb'']
  have hψW : ∀ s, ψ s ∈ j.range := by
    intro s
    obtain ⟨k, hk⟩ := hψK s
    have hn : ‖κ' k‖ ≤ 1 := by rw [hk]; exact (mem_OO_iff _).1 (φ s).2
    obtain ⟨w, hw⟩ := (hW k).1 hn
    exact ⟨w, by rw [← hk, ← hw]; rfl⟩
  let e := RingEquiv.ofBijective j.rangeRestrict ⟨fun a b h => hj (congrArg Subtype.val h), j.rangeRestrict_surjective⟩
  let φ' : M.Z.presheaf.stalk x →+* W := e.symm.toRingHom.comp (ψ.codRestrict j.range hψW)
  have hjφ' : ∀ s, j (φ' s) = ψ s := by
    intro s
    have h := e.apply_symm_apply (ψ.codRestrict j.range hψW s)
    exact congrArg Subtype.val h
  have hjO : ∀ w, j w ∈ OO p := fun w => (mem_OO_iff _).2 ((hW _).2 ⟨w, rfl⟩)
  let iV : W →+* OO p := j.codRestrict (OO p) hjO
  have hiVloc : IsLocalHom iV := by
    constructor
    intro w hw
    obtain ⟨u, hu⟩ := hw
    have hw0 : j w ≠ 0 := by
      intro h0
      have : ((u : OO p) : PadicAlgCl p) = 0 := by rw [hu]; exact h0
      exact u.ne_zero (Subtype.ext this)
    have hwne : algebraMap W (FractionRing W) w ≠ 0 := fun h => hw0 (by simp [j, h])
    have hinv : ‖κ' (algebraMap W (FractionRing W) w)⁻¹‖ ≤ 1 := by
      have h1 : ((u⁻¹ : (OO p)ˣ) : OO p) * (u : OO p) = 1 := u.inv_mul
      have h2 : ((((u⁻¹ : (OO p)ˣ) : OO p) : PadicAlgCl p)) * j w = 1 := by
        have := congrArg (fun t : OO p => (t : PadicAlgCl p)) h1
        simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at this
        rw [hu] at this; exact this
      have h3 : κ' (algebraMap W (FractionRing W) w)⁻¹ = (((u⁻¹ : (OO p)ˣ) : OO p) : PadicAlgCl p) := by
        rw [map_inv₀]
        exact (eq_inv_of_mul_eq_one_left h2).symm
      rw [h3]; exact (mem_OO_iff _).1 (Subtype.prop _)
    obtain ⟨w', hw'⟩ := (hW _).1 hinv
    have hww : w * w' = 1 := by
      apply IsFractionRing.injective W (FractionRing W)
      rw [map_mul, hw', map_one, mul_inv_cancel₀ hwne]
    exact ⟨⟨w, w', hww, by rw [mul_comm]; exact hww⟩, rfl⟩
  have hcomp : iV.comp φ' = φ := by
    ext s
    exact hjφ' s
  refine ⟨W, inferInstance, inferInstance, inferInstance, fV, fK, κ', iV, spMap φ' ≫ M.Z.fromSpecStalk x,
    hfVloc, hfK, hκ', hiVloc, fun w => rfl, ?_⟩
  rw [← Category.assoc, ← hφ, ← hcomp]
  show (Spec.map (CommRingCat.ofHom iV) ≫ Spec.map (CommRingCat.ofHom φ')) ≫ _ = Spec.map (CommRingCat.ofHom (iV.comp φ')) ≫ _
  rw [← Spec.map_comp]
  rfl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrFactorPointPadicAlgClosureStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dvr_factor_point_padicAlgClosure : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M : RatModel o Ω) (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V], IsAdicComplete (maximalIdeal V) V → ∀ (κ : FractionRing V →+* PadicAlgCl p), (∀ x, ‖κ x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) → ∀ y : Sp (OO p) ⟶ M.Z, ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (fV : V →+* V') (fK : FractionRing V →+* FractionRing V') (κ' : FractionRing V' →+* PadicAlgCl p) (iV : V' →+* OO p) (ξ : Sp V' ⟶ M.Z), IsLocalHom fV ∧ (∀ x, fK (algebraMap V _ x) = algebraMap V' _ (fV x)) ∧ κ'.comp fK = κ ∧ IsLocalHom iV ∧ (∀ x, (iV x : PadicAlgCl p) = κ' (algebraMap V' _ x)) ∧ spMap iV ≫ ξ = y := by
  first | exact @GlobalTheory.ValPt.exists_dvr_factor | exact GlobalTheory.ValPt.exists_dvr_factor | (intros; apply GlobalTheory.ValPt.exists_dvr_factor <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyH1AxesPrimitiveRank
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyH1AxesPrimitiveRank
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.AbCoh.Axes

theorem exists_cover {K : Type} [Field K] {X : Scheme.{0}} (s : X ⟶ Sp K) [QuasiCompact s] :
    ∃ (n : ℕ) (D : Fin n → X.Opens), (∀ i, IsAffineOpen (D i)) ∧ ⨆ i, D i = ⊤ := by
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  obtain ⟨t, ht, hU⟩ := isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens.mp
    ⟨(isCompact_univ : IsCompact (Set.univ : Set X)), isOpen_univ⟩
  haveI := ht.fintype
  refine ⟨Fintype.card t, fun i ↦ ((Fintype.equivFin t).symm i).1.1, fun i ↦ ((Fintype.equivFin t).symm i).1.2, ?_⟩
  refine eq_top_iff.2 fun x _ ↦ ?_
  have hx : x ∈ (Set.univ : Set X) := trivial
  rw [hU] at hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨i, hi, hxi⟩ := hx
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨Fintype.equivFin t ⟨i, hi⟩, ?_⟩
  simpa using hxi

theorem ho1_fin {K : Type} [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] (g : ℕ)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) :
    FiniteDimensional K (HO1 A.hom) ∧ Module.finrank K (HO1 A.hom) = g := by
  haveI := hA.proper
  obtain ⟨n, D, hD, hcov⟩ := exists_cover A.hom
  obtain ⟨⟨e⟩, -⟩ := GlobalTheory.T.cech_cohomology_structure_sheaf_iso K A.left A.hom (Fin n) D inferInstance hD hcov
  obtain ⟨hf, h1, -⟩ := GlobalTheory.T.cech_cohomology_trivial_bundle_abelian K A g hA hg (Fin n) D hD hcov
  haveI := hf 1
  exact ⟨Module.Finite.equiv e.symm, e.finrank_eq.trans h1⟩

theorem smooth_sq {K : Type} [Field K] {A : Over (Sp K)} {g : ℕ} (hg : SmoothOfRelativeDimension g A.hom) :
    SmoothOfRelativeDimension (g + g) (A ⊗ A).hom := by
  have : SmoothOfRelativeDimension g (Limits.pullback.fst A.hom A.hom) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback
      (IsPullback.of_hasPullback A.hom A.hom).flip hg
  rw [Over.tensorObj_hom]
  exact smoothOfRelativeDimension_comp g g _ _

theorem pO1_comp {K : Type} [Field K] {X Y Z : Over (Sp K)} (f : X ⟶ Y) (h : Y ⟶ Z) (a : HO1 Z.hom) :
    pO1 (f ≫ h) a = pO1 f (pO1 h a) :=
  ((GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id.1 K K Z.left Y.left Z.hom Y.hom (RingHom.id K) h.left (ovw h) K X.left X.hom
    (RingHom.id K) f.left (ovw f) (RingHom.id K) (f ≫ h).left (ovw (f ≫ h)) (by simp)
    (fun _ ↦ rfl)).1 a).symm

theorem pO1_id {K : Type} [Field K] (X : Over (Sp K)) (a : HO1 X.hom) : pO1 (𝟙 X) a = a :=
  (GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id.2.2 K X).1 a

theorem pO1_unit {K : Type} [Field K] {X Y : Over (Sp K)} (f : X ⟶ 𝟙_ (Over (Sp K))) (h : 𝟙_ (Over (Sp K)) ⟶ Y)
    (a : HO1 Y.hom) : pO1 (f ≫ h) a = 0 := by
  have : IsAffine (𝟙_ (Over (Sp K))).left := by
    show IsAffine (Spec _); infer_instance
  haveI := (GlobalTheory.AbCoh.Vanish.main.1 K _ (𝟙_ (Over (Sp K))).hom this).1
  rw [pO1_comp, Subsingleton.elim (pO1 h a) 0, map_zero]

def axesRes {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] : HO1 (A ⊗ A).hom →ₗ[K] HO1 A.hom × HO1 A.hom :=
  (pO1 (lift (𝟙 A) (toUnit A ≫ η[A]))).prod (pO1 (lift (toUnit A ≫ η[A]) (𝟙 A)))

def projSum {K : Type} [Field K] (A : Over (Sp K)) : HO1 A.hom × HO1 A.hom →ₗ[K] HO1 (A ⊗ A).hom :=
  (pO1 (fst A A)).coprod (pO1 (snd A A))

theorem axesRes_projSum {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] (x : HO1 A.hom × HO1 A.hom) :
    axesRes A (projSum A x) = x := by
  obtain ⟨a, b⟩ := x
  refine Prod.ext ?_ ?_ <;>
  simp only [axesRes, projSum, LinearMap.prod_apply, Function.prod, LinearMap.coprod_apply, map_add (f := _),
    ← pO1_comp, lift_fst, lift_snd, pO1_id, pO1_unit, Prod.fst_add, Prod.snd_add, add_zero, zero_add]

theorem axesRes_injective {K : Type} [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] (g : ℕ)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) : Function.Injective (axesRes A) := by
  obtain ⟨h1, h2⟩ := ho1_fin A g hA hg
  obtain ⟨h3, h4⟩ := ho1_fin (A ⊗ A) (g + g) (AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA) (smooth_sq hg)
  have hinj : Function.Injective (projSum A) := Function.LeftInverse.injective (axesRes_projSum A)
  have hsurj : Function.Surjective (projSum A) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [Module.finrank_prod, h2, h4])).1 hinj
  intro y y' h
  obtain ⟨x, rfl⟩ := hsurj y
  obtain ⟨x', rfl⟩ := hsurj y'
  rw [axesRes_projSum, axesRes_projSum] at h
  rw [h]

theorem main : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom → GlobalTheory.AbCoh.AxesVanishingStructureSheafDegOne A ∧ GlobalTheory.AbCoh.StructureSheafH1Primitive A ∧ Module.finrank K (HO1 A.hom) = g := by
  intro K _ _ A _ g hA hg
  have hN := axesRes_injective A g hA hg
  refine ⟨fun y h₁ h₂ ↦ ?_, fun x ↦ ?_, (ho1_fin A g hA hg).2⟩
  · refine hN ?_
    refine Prod.ext ?_ ?_ <;> simp only [axesRes, LinearMap.prod_apply, Function.prod, h₁, h₂, map_zero, Prod.fst_zero, Prod.snd_zero]
  · have := axesRes_projSum A (x, x)
    refine hN ?_
    rw [show pO1 (fst A A) x + pO1 (snd A A) x = projSum A (x, x) from rfl, this]
    refine Prod.ext ?_ ?_ <;> simp only [axesRes, LinearMap.prod_apply, Function.prod, ← pO1_comp, pO1_id, MonObj.lift_comp_one_left, MonObj.lift_comp_one_right]

end GlobalTheory.AbCoh.Axes
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyH1AxesPrimitiveRankStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_variety_h1_axes_primitive_rank : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → GlobalTheory.AbCoh.AxesVanishingStructureSheafDegOne A ∧ GlobalTheory.AbCoh.StructureSheafH1Primitive A ∧ Module.finrank K (HO1 A.hom) = g := by
  first | exact @GlobalTheory.AbCoh.Axes.main | exact GlobalTheory.AbCoh.Axes.main | (intros; apply GlobalTheory.AbCoh.Axes.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelsInducedAllEmbeddingsOfGalois
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelsInducedAllEmbeddingsOfGalois
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.AllEmb

open GlobalTheory.LabTrans GlobalTheory.ArcPull GlobalTheory.TorusExt GlobalTheory.ArcExt ReciprocityTheory.ChartRestriction.G.DVR

theorem lab_indep_level {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] {k : ℕ} (hB : D.TauBimult) {A : PolAV (Sp (FractionRing R))} {lab : Labels D A}
    (hlab : ∀ (σ : Kb R →ₐ[FractionRing R] Kb R) (p p' : QkPt D (Kb R) k), QkExt σ.toRingHom p p' →
      (lab k p').left = spMap σ.toRingHom ≫ (lab k p).left)
    (τ₁ τ₂ : Kb R →ₐ[FractionRing R] F) {p q : QkPt D (Kb R) k} {r : QkPt D F k}
    (h₁ : QkExt τ₁.toRingHom p r) (h₂ : QkExt τ₂.toRingHom q r) :
    spMap τ₁.toRingHom ≫ (lab k p).left = spMap τ₂.toRingHom ≫ (lab k q).left := by
  obtain ⟨σ, hσ⟩ : ∃ σ : Kb R →ₐ[FractionRing R] Kb R, τ₂.toRingHom.comp σ.toRingHom = τ₁.toRingHom := by
    letI : Algebra (Kb R) F := τ₂.toRingHom.toAlgebra
    haveI : IsScalarTower (FractionRing R) (Kb R) F := IsScalarTower.of_algebraMap_eq fun x => (τ₂.commutes x).symm
    exact ⟨τ₁.restrictNormal (Kb R), RingHom.ext fun x => τ₁.restrictNormal_commutes (Kb R) x⟩
  obtain ⟨q', hq'⟩ := exists_ext hB σ p
  obtain ⟨r', hr'⟩ := exists_ext hB τ₂ q'
  have h₃ := qkExt_trans hq' hr'
  rw [hσ] at h₃
  obtain rfl := ext_unique hB τ₁ h₁ h₃
  obtain rfl := qkExt_inj hB τ₂ h₂ hr'
  rw [hlab σ p q hq', ← Category.assoc, ← Geo.Tor.spMap_comp, hσ]

theorem induces_of_one_embedding : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → GalEqN n lab → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), Function.Injective φ → IsLocalHom φ → ∀ (G' : Over (Sp W)) [GrpObj G'] [IsCommMonObj G'] (D' : DegData W (maximalIdeal W)) (A' : PolAV (Sp (FractionRing W))) (U' : Unif (maximalIdeal W) D' A' G') (a : A'.A.left ⟶ A.A.left), IsSemiAbelian G' → IsFib φ A A' a → ∀ (hD : IsPullDeg φ D.toPre D'.toPre) (j : ℕ), (∃ (C : Type) (_ : Field C) (_ : IsAlgClosed C) (_ : Algebra (FractionRing W) C) (_ : Algebra (FractionRing R) C) (em : Kb R →ₐ[FractionRing R] C), (∀ r, algebraMap (FractionRing R) C (algebraMap R _ r) = algebraMap (FractionRing W) C (algebraMap W _ (φ r))) ∧  ∀ (p : QkPt D.toPre (Kb R) (n ^ j)) (p₁ : QkPt D.toPre C (n ^ j)) (p' : QkPt D'.toPre C (n ^ j)) (x' : TFK (R := W) C ⟶ A'.A), QkExt em.toRingHom p p₁ → p'.y = hD.xe.symm p₁.y → IsPullGtF φ hD C p₁.g p'.g → x'.left ≫ a = spMap em.toRingHom ≫ (lab (n ^ j) p).left → QkToAkU U'.toUnifPre C (n ^ j) p' x') → Induces lab φ U' hD a (n ^ j) := by
  intro R _ _ _ hR D A lab n hn _ _ hlab W _ _ _ hW φ iφ _ G' _ _ D' A' U' a hG ⟨ga, hga, gpa, _⟩ hD j
    ⟨C, _, _, _, _, emC, cC, HC⟩ F _ _ _ _ em cF p p₁ p' x' y₁ y₂ y₃ y₄
  have hGF := GlobalTheory.firstFiveLaws.1.globalFns
  have := hR.2
  have := hW.1
  have := hW.2.2
  have hB := D.tau_bimult
  have hB' := D'.tau_bimult
  have hk : 1 ≤ n ^ j := Nat.one_le_pow _ _ hn.pos
  have bW : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  letI : Algebra (FractionRing R) (Kb W) := ((algebraMap (FractionRing W) (Kb W)).comp ga).toAlgebra
  have cK : Compat φ (Kb W) := fun r => congrArg (algebraMap (FractionRing W) (Kb W)) (hga r)
  obtain ⟨e⟩ := nonempty_lift (FractionRing R) (Kb W)

  have fac : ∀ (L : Type) [Field L] [Algebra (FractionRing W) L] [Algebra (FractionRing R) L], Compat φ L →
      algebraMap (FractionRing R) L = (algebraMap (FractionRing W) L).comp ga := fun L _ _ _ c =>
    IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => (c r).trans
      (congrArg (algebraMap (FractionRing W) L) (hga r).symm))
  have up : ∀ (L : Type) [Field L] [Algebra (FractionRing W) L] [Algebra (FractionRing R) L], Compat φ L →
      ∀ i : Kb W →ₐ[FractionRing W] L, ∃ i' : Kb W →ₐ[FractionRing R] L, i'.toRingHom = i.toRingHom := fun L _ _ _ c i =>
    ⟨⟨i.toRingHom, fun t => by rw [fac L c]; exact i.commutes (ga t)⟩, rfl⟩

  have key : ∀ (L : Type) [Field L] [IsAlgClosed L] [Algebra (FractionRing W) L] [Algebra (FractionRing R) L],
      Compat φ L → ∀ (i : Kb W →ₐ[FractionRing W] L) (m : Kb R →ₐ[FractionRing R] L)
      (q : QkPt D.toPre (Kb R) (n ^ j)) (q₁ : QkPt D.toPre (Kb W) (n ^ j)) (x₀ : TFK (R := W) (Kb W) ⟶ A'.A),
      QkExt e.toRingHom q q₁ → x₀.left ≫ a = spMap e.toRingHom ≫ (lab (n ^ j) q).left →
      ∀ (s : QkPt D.toPre (Kb R) (n ^ j)) (s₁ : QkPt D.toPre L (n ^ j)) (s' : QkPt D'.toPre L (n ^ j))
        (z : TFK (R := W) L ⟶ A'.A), QkExt i.toRingHom q₁ s₁ → QkExt m.toRingHom s s₁ → s'.y = hD.xe.symm s₁.y →
        IsPullGtF φ hD L s₁.g s'.g → z.left ≫ a = spMap m.toRingHom ≫ (lab (n ^ j) s).left →
        (QkToAkU U'.toUnifPre (Kb W) (n ^ j) (pullQk hD hGF cK hB hB' q₁) x₀ ↔ QkToAkU U'.toUnifPre L (n ^ j) s' z) := by
    intro L _ _ _ _ c i m q q₁ x₀ hq hx₀ s s₁ s' z w₀ w₁ w₂ w₃ w₄
    obtain ⟨i', hi'⟩ := up L c i
    obtain ⟨⟨t, ht⟩, -, hgal⟩ := GlobalTheory.UT.Cl.galois_holds W _ bW D' A' G' hG U' _ L i (n ^ j) hk
      (pullQk hD hGF cK hB hB' q₁)
    have t₁ : IsPullGtF φ hD L s₁.g t.g :=
      isPullGtF_ext hD c i.toRingHom i.comp_algebraMap (isPullGtF_pullGt hD hGF cK _) w₀ ht
    have t₂ : t.y = hD.xe.symm s₁.y := by rw [ht.1, w₀.1]; rfl
    obtain rfl : s' = t := ((eq_pullQk_iff hD hGF c hB hB' _ _).2 ⟨w₂, w₃⟩).trans
      ((eq_pullQk_iff hD hGF c hB hB' _ _).2 ⟨t₂, t₁⟩).symm
    have u : QkExt (i'.comp e).toRingHom q s₁ := by
      have := qkExt_trans hq w₀
      rw [← hi'] at this
      exact this
    have l := lab_indep_level hB (fun σ => hlab σ j) m (i'.comp e) w₁ u
    refine hgal s' x₀ z ht ?_
    apply gpa.1.hom_ext
    · rw [w₄, Category.assoc, hx₀, ← Category.assoc, ← Geo.Tor.spMap_comp, l, ← hi']
      rfl
    · rw [Category.assoc, Over.w z, Over.w x₀]
      exact ((Geo.Tor.spMap_comp _ _).symm.trans (congrArg spMap i.comp_algebraMap)).symm
  obtain ⟨i⟩ := nonempty_lift (FractionRing W) F
  obtain ⟨i₀⟩ := nonempty_lift (FractionRing W) C
  obtain ⟨i', hi'⟩ := up F cF i
  obtain ⟨i₀', hi₀'⟩ := up C cC i₀
  obtain ⟨q₁, hq₁⟩ := exists_of_ext hB i' hk p₁
  obtain ⟨q, hq⟩ := exists_of_ext hB e hk q₁
  obtain ⟨x₀, hx₀⟩ := exists_lift_pt gpa.1 e.toRingHom e.comp_algebraMap (lab (n ^ j) q)
  obtain ⟨r₁, hr₁⟩ := exists_ext hB i₀' q₁
  obtain ⟨r, hr⟩ := exists_of_ext hB emC hk r₁
  obtain ⟨z, hz⟩ := exists_lift_pt gpa.1 emC.toRingHom (emC.comp_algebraMap.trans (fac C cC)) (lab (n ^ j) r)
  have hC := HC r r₁ (pullQk hD hGF cC hB hB' r₁) z hr rfl (isPullGtF_pullGt hD hGF cC _) hz
  exact (key F cF i em q q₁ x₀ hq hx₀ p p₁ p' x' (hi' ▸ hq₁) y₁ y₂ y₃ y₄).1
    ((key C cC i₀ emC q q₁ x₀ hq hx₀ r r₁ _ z (hi₀' ▸ hr₁) hr rfl (isPullGtF_pullGt hD hGF cC _) hz).2 hC)

end GlobalTheory.Mum.AllEmb
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelsInducedAllEmbeddingsOfGaloisStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.labels_induced_all_embeddings_of_galois : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → GalEqN n lab → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), Function.Injective φ → IsLocalHom φ → ∀ (G' : Over (Sp W)) [GrpObj G'] [IsCommMonObj G'] (D' : DegData W (maximalIdeal W)) (A' : PolAV (Sp (FractionRing W))) (U' : Unif (maximalIdeal W) D' A' G') (a : A'.A.left ⟶ A.A.left), IsSemiAbelian G' → IsFib φ A A' a → ∀ (hD : IsPullDeg φ D.toPre D'.toPre) (j : ℕ), (∃ (C : Type) (_ : Field C) (_ : IsAlgClosed C) (_ : Algebra (FractionRing W) C) (_ : Algebra (FractionRing R) C) (em : Kb R →ₐ[FractionRing R] C), (∀ r, algebraMap (FractionRing R) C (algebraMap R _ r) = algebraMap (FractionRing W) C (algebraMap W _ (φ r))) ∧  ∀ (p : QkPt D.toPre (Kb R) (n ^ j)) (p₁ : QkPt D.toPre C (n ^ j)) (p' : QkPt D'.toPre C (n ^ j)) (x' : TFK (R := W) C ⟶ A'.A), QkExt em.toRingHom p p₁ → p'.y = hD.xe.symm p₁.y → IsPullGtF φ hD C p₁.g p'.g → x'.left ≫ a = spMap em.toRingHom ≫ (lab (n ^ j) p).left → QkToAkU U'.toUnifPre C (n ^ j) p' x') → Induces lab φ U' hD a (n ^ j) := by
  first | exact @GlobalTheory.Mum.AllEmb.induces_of_one_embedding | exact GlobalTheory.Mum.AllEmb.induces_of_one_embedding | (intros; apply GlobalTheory.Mum.AllEmb.induces_of_one_embedding <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoGenericFibreExtendsUniformisedGr
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoGenericFibreExtendsUniformisedGr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

noncomputable section

namespace GlobalTheory.TInj

open GlobalTheory.CechPic GlobalTheory.ZH.EndoExtend

theorem lbIso_lam_of_generic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (J : Ideal R), AdmBase R J → ∀ (D₁ : DegData R J) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : UnifPre J D₁ A₁ G₁) (D₂ : DegData R J) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : UnifPre J D₂ A₂ G₂), IsSemiAbelian G₁ → ∀ (a : G₁ ⟶ G₂) (cA : A₁.A ⟶ A₂.A), IsMonHom a → IsMonHom cA → Gen₀ U₁ U₂ a cA → LBIso (abelian₂ A₁.A A₁.L) ((abelian₂ A₂.A A₂.L).pull (lift (fst A₁.A A₁.A ≫ cA) (snd A₁.A A₁.A ≫ cA) : G2 A₁.A ⟶ G2 A₂.A).left) → LBIso (abelian₂ G₁ U₁.LG.L) ((abelian₂ G₂ U₂.LG.L).pull (lift (fst G₁ G₁ ≫ a) (snd G₁ G₁ ≫ a) : G2 G₁ ⟶ G2 G₂).left) := by
  intro R _ _ _ J hR D₁ A₁ G₁ _ _ U₁ D₂ A₂ G₂ _ _ U₂ hS a cA ha hcA hgen hA
  haveI : IsNoetherianRing R := hR.1
  haveI : IsIntegrallyClosed R := hR.2.2.1
  haveI := hS.smooth
  haveI := hS.geomConnected
  haveI := GlobalTheory.smooth_tensorObj_hom G₁ G₁
  haveI := GlobalTheory.geometricallyIntegral_tensorObj_hom G₁ G₁
  let δ := CartesianMonoidalCategory.prodComparison (Over.pullback (jK R)) G₁ G₁
  let u := lift (fst ((Over.pullback (jK R)).obj G₁) ((Over.pullback (jK R)).obj G₁) ≫ U₁.gen.hom)
    (snd ((Over.pullback (jK R)).obj G₁) ((Over.pullback (jK R)).obj G₁) ≫ U₁.gen.hom)
  have key : ∀ {D : DegData R J} {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
      (U : UnifPre J D A G) (x y : G₁ ⟶ G) (cx cy : A₁.A ⟶ A.A), Gen₀ U₁ U x cx → Gen₀ U₁ U y cy →
      CechPic.pull (pullback.fst (G₁ ⊗ G₁).hom (jK R)) (cubeCls G ![fst G₁ G₁ ≫ x, snd G₁ G₁ ≫ y] (cls U.LG.L U.LG.isLB)) =
        CechPic.pull δ.left (CechPic.pull u.left
          (cubeCls A.A ![fst A₁.A A₁.A ≫ cx, snd A₁.A A₁.A ≫ cy] (cls A.L A.isLB))) := by
    intro D A G _ _ U x y cx cy hx hy
    have hL := U.LG.isLB
    have hA := A.isLB
    have hgen := U.gen_hom
    have hc' : CechPic.pull (pullback.fst G.hom (jK R)) (cls U.LG.L hL) =
        CechPic.pull U.gen.hom.left (cls A.L hA) := by
      obtain ⟨w, hw⟩ := U.ext
      rw [← cls_pull hL _ (pull_isLB hL _), ← cls_pull hA _ (pull_isLB hA _)]
      exact ((cls_eq_iff _ _).2 ⟨w, hw⟩).symm
    have Aw : ∀ {Y Z : Over (Sp R)} (q : Y ⟶ Z),
        ((Over.pullback (jK R)).map q).left ≫ pullback.fst Z.hom (jK R) = pullback.fst Y.hom (jK R) ≫ q.left :=
      fun q => pullback.lift_fst _ _ _
    have hu : u.left ≫ (A₁.A ⊗ A₁.A).hom =
        ((Over.pullback (jK R)).obj G₁ ⊗ (Over.pullback (jK R)).obj G₁).hom ≫ 𝟙 _ := by
      rw [Category.comp_id]; exact Over.w u
    have e' := push_cubeCls (isGrpPullback_pullback G (jK R)) (T' := (Over.pullback (jK R)).obj (G₁ ⊗ G₁))
      (T := G₁ ⊗ G₁) (fun i => (Over.pullback (jK R)).map (![fst G₁ G₁ ≫ x, snd G₁ G₁ ≫ y] i))
      ![fst G₁ G₁ ≫ x, snd G₁ G₁ ≫ y] (pullback.fst (G₁ ⊗ G₁).hom (jK R)) pullback.condition
      (fun i => Aw _) (cls U.LG.L hL)
    refine e'.trans ((pull_cubeCls _ ![fst _ _ ≫ (Over.pullback (jK R)).map x,
      snd _ _ ≫ (Over.pullback (jK R)).map y] _ δ (fun i => ?_) _).symm.trans ?_)
    · fin_cases i <;> simp [δ]
    rw [hc']
    refine congrArg (CechPic.pull δ.left) (push_cubeCls (isGrpPullback_of_iso U.gen) _ _ u.left hu (fun i => ?_) _).symm
    fin_cases i
    · show ((fst _ _ ≫ (Over.pullback (jK R)).map x) ≫ U.gen.hom).left = (u ≫ fst A₁.A A₁.A ≫ cx).left
      congr 1
      simp only [u, Category.assoc, lift_fst_assoc]
      rw [hx]
    · show ((snd _ _ ≫ (Over.pullback (jK R)).map y) ≫ U.gen.hom).left = (u ≫ snd A₁.A A₁.A ≫ cy).left
      congr 1
      simp only [u, Category.assoc, lift_snd_assoc]
      rw [hy]
  have hL₁ := U₁.LG.isLB
  have hL₂ := U₂.LG.isLB
  have hA₁ := A₁.isLB
  have hA₂ := A₂.isLB
  have lG₁ : (abelian₂ G₁ U₁.LG.L).IsLB := LB.isLB_linComb hL₁ _ _
  have lG₂ : (abelian₂ G₂ U₂.LG.L).IsLB := LB.isLB_linComb hL₂ _ _
  have lA₁ : (abelian₂ A₁.A A₁.L).IsLB := LB.isLB_linComb hA₁ _ _
  have lA₂ : (abelian₂ A₂.A A₂.L).IsLB := LB.isLB_linComb hA₂ _ _
  have g₁ : Gen₀ U₁ U₁ (𝟙 G₁) (𝟙 A₁.A) := by
    unfold Gen₀; rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  have cG₁ : cls (abelian₂ G₁ U₁.LG.L) lG₁ = cubeCls G₁ ![fst G₁ G₁ ≫ 𝟙 G₁, snd G₁ G₁ ≫ 𝟙 G₁] (cls _ hL₁) := by
    refine (cls_cubeLB G₁ (x2 G₁) hL₁).trans ?_
    congr 1
  have cA₁ : cls (abelian₂ A₁.A A₁.L) lA₁ = cubeCls A₁.A ![fst A₁.A A₁.A ≫ 𝟙 A₁.A, snd A₁.A A₁.A ≫ 𝟙 A₁.A] (cls _ hA₁) := by
    refine (cls_cubeLB A₁.A (x2 A₁.A) hA₁).trans ?_
    congr 1
  have cG₂ : cls ((abelian₂ G₂ U₂.LG.L).pull (lift (fst G₁ G₁ ≫ a) (snd G₁ G₁ ≫ a) : G2 G₁ ⟶ G2 G₂).left) (pull_isLB lG₂ _) =
      cubeCls G₂ ![fst G₁ G₁ ≫ a, snd G₁ G₁ ≫ a] (cls _ hL₂) := by
    rw [cls_pull lG₂ _ (pull_isLB lG₂ _)]
    refine (congrArg _ (cls_cubeLB G₂ (x2 G₂) hL₂)).trans ?_
    exact pull_cubeCls G₂ _ _ _ (fun i => by fin_cases i <;> simp [x2]) _
  have cA₂ : cls ((abelian₂ A₂.A A₂.L).pull (lift (fst A₁.A A₁.A ≫ cA) (snd A₁.A A₁.A ≫ cA) : G2 A₁.A ⟶ G2 A₂.A).left)
      (pull_isLB lA₂ _) = cubeCls A₂.A ![fst A₁.A A₁.A ≫ cA, snd A₁.A A₁.A ≫ cA] (cls _ hA₂) := by
    rw [cls_pull lA₂ _ (pull_isLB lA₂ _)]
    refine (congrArg _ (cls_cubeLB A₂.A (x2 A₂.A) hA₂)).trans ?_
    exact pull_cubeCls A₂.A _ _ _ (fun i => by fin_cases i <;> simp [x2]) _
  have eA : cubeCls A₁.A ![fst A₁.A A₁.A ≫ 𝟙 A₁.A, snd A₁.A A₁.A ≫ 𝟙 A₁.A] (cls _ hA₁) =
      cubeCls A₂.A ![fst A₁.A A₁.A ≫ cA, snd A₁.A A₁.A ≫ cA] (cls _ hA₂) :=
    cA₁.symm.trans (((cls_eq_iff lA₁ (pull_isLB lA₂ _)).2 hA).trans cA₂)
  refine GlobalTheory.Mum.lbIso_of_generic_local R (G₁ ⊗ G₁) (η[G₁ ⊗ G₁]).left (Over.w _) _ _ lG₁ (pull_isLB lG₂ _) ?_
  refine (cls_eq_iff (pull_isLB lG₁ _) (pull_isLB (pull_isLB lG₂ _) _)).1 ?_
  rw [cls_pull lG₁ _ (pull_isLB lG₁ _), cls_pull (pull_isLB lG₂ _) _ (pull_isLB (pull_isLB lG₂ _) _), cG₁, cG₂,
    key U₁ (𝟙 G₁) (𝟙 G₁) (𝟙 A₁.A) (𝟙 A₁.A) g₁ g₁, key U₂ a a cA cA hgen hgen, eA]

end GlobalTheory.TInj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoGenericFibreExtendsUniformisedGrStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumfordBundleIso_genericFibre_extends_uniformisedGroups : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (J : Ideal R), AdmBase R J → ∀ (D₁ : DegData R J) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : UnifPre J D₁ A₁ G₁) (D₂ : DegData R J) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : UnifPre J D₂ A₂ G₂), IsSemiAbelian G₁ → ∀ (a : G₁ ⟶ G₂) (cA : A₁.A ⟶ A₂.A), IsMonHom a → IsMonHom cA → Gen₀ U₁ U₂ a cA → LBIso (abelian₂ A₁.A A₁.L) ((abelian₂ A₂.A A₂.L).pull (lift (fst A₁.A A₁.A ≫ cA) (snd A₁.A A₁.A ≫ cA) : G2 A₁.A ⟶ G2 A₂.A).left) → LBIso (abelian₂ G₁ U₁.LG.L) ((abelian₂ G₂ U₂.LG.L).pull (lift (fst G₁ G₁ ≫ a) (snd G₁ G₁ ≫ a) : G2 G₁ ⟶ G2 G₂).left) := by
  first | exact @GlobalTheory.TInj.lbIso_lam_of_generic | exact GlobalTheory.TInj.lbIso_lam_of_generic | (intros; apply GlobalTheory.TInj.lbIso_lam_of_generic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionTranslateThetaSectionUnit
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionTranslateThetaSectionUnit
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.IntTerm

theorem gs_comp_stalkMap {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (h : g (f z) ∈ U)
    (a : Γ(X, U)) : gs (f ≫ g) z U a = (f.stalkMap z).hom (gs g (f z) U a) := by
  rw [← gs_pull f g z U h a, gs_eq f z _ h, gs_eq g (f z) U h]
  exact (Scheme.Hom.germ_stalkMap_apply f _ z h _).symm

theorem formEq_famφB_zero {V : Type} [CommRing V] [IsDomain V] (D : DegPre V) {Y : Scheme.{0}} (h : Y ⟶ D.P.A.left) :
    FormEq (fun i => h ≫ D.famφB 0 i) (DegPre.famε 1) (fun _ : Fin 1 => h) (fun _ => (1 : ℤ)) := by
  intro U _ hh
  have e0 : D.famφB 0 0 = 𝟙 _ := rfl
  have e1 : D.famφB 0 1 = 𝟙 _ := by
    show (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c 0)).left = _
    rw [ThetaOne.c_zero, MonObj.comp_one]
    show ((𝟙 D.P.A) * 1).left = _
    rw [_root_.mul_one]; rfl
  have e2 : D.famφB 0 2 = D.famφB 0 3 := by
    show (toUnit D.P.A ≫ D.c 0).left = (toUnit D.P.A ≫ η[D.P.A]).left
    rw [ThetaOne.c_zero, MonObj.comp_one]
    rfl
  simp only [Fin.prod_univ_four, Fin.prod_univ_one, e0, e1, e2]
  simp [DegPre.famε]

theorem exists_unitAt_mul : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegPre V) (θ : D.SecB 1 0), IntTerm.IsTheta D θ → ∀ N : ℕ, 2 ≤ N → IsUnit (N : V) → ∀ (C : Type) (b : C → (𝟙_ (Over (Sp V)) ⟶ D.P.A)), IntTerm.Exhausts D.P N b → ∀ a : 𝟙_ (Over (Sp V)) ⟶ D.P.A, ∃ c, IntTerm.UnitAt D θ (a * b c) := by
  intro V _ _ _ D θ hθ N hN hNV C b hb a
  have hL := GlobalTheory.abelianSchemeLaws_all.1
  let k := AlgebraicClosure (ResidueField V)
  let f : V →+* k := (algebraMap (ResidueField V) k).comp (residue V)
  let r : Sp k ⟶ Sp V := Spec.map (CommRingCat.ofHom f)
  have hNk : (N : k) ≠ 0 := by
    have := (hNV.map f).ne_zero
    rwa [map_natCast] at this
  let θ' := ThetaOne.pullTo D f θ
  have hbasis := hθ k f θ' (ThetaOne.isPullSecLC_pullTo D f θ)
  obtain ⟨j₀, hj₀⟩ := ThetaOne.exists_ne_zero D f θ' hbasis
  obtain ⟨th, hth⟩ := exists_sec D.P.isLB (formEq_famφB_zero D (snd (Over.mk r) D.P.A).left) θ'
  have hne : SecM.ofSec D.P.A (L := D.P.L) (a := 1) (T := Over.mk r) th ≠ 0 := by
    intro h0
    apply hj₀
    have hz : ∀ j, th.f j = 0 := fun j => congrFun (congrArg Subtype.val h0) j
    refine sec_ext_val D.P.isLB (s' := H1.SectionArithmetic.secZero _) (fun y J hJ => ?_) j₀
    rw [← hth _ (𝟙 _) y J hJ]
    show gs _ y _ (th.f _) = gs _ y _ 0
    erw [hz]
    have gz : ∀ {Y : Scheme.{0}} (y : Y) (U : Y.Opens), gs (𝟙 Y) y U 0 = 0 := fun y U => by
      unfold gs; split_ifs <;> simp only [map_zero]
    exact (gz _ _).trans (gz _ _).symm
  obtain ⟨y, hy, hu⟩ := GlobalTheory.UT.ExactTerm.exists_good_point hL.goodPt hL.polBaseChange D.P r hN hNk th hne
    (toUnit (Over.mk r) ≫ a)
  obtain ⟨c, hc⟩ := hb k r y hy
  refine ⟨c, ?_⟩
  have hmul : (toUnit (Over.mk r) ≫ a) * y = toUnit (Over.mk r) ≫ (a * b c) := by rw [hc, MonObj.comp_mul]
  rw [hmul] at hu
  let g := a * b c
  let q : Sp k := closedPoint k
  obtain ⟨J, hJ, -⟩ := exists_good D.P.L D.P.isLB q (K := Empty) Empty.elim Empty.elim (·.elim) (·.elim)
  have h1 := hu q J hJ
  have hρ : (ptSecT D.P.A (toUnit (Over.mk r) ≫ g)).left ≫ (snd (Over.mk r) D.P.A).left = r ≫ g.left := by
    rw [← Over.comp_left, ptSecT, lift_snd, Over.comp_left]
    congr 1
  have hθ'e : θ' = H1.SectionArithmetic.pullSec θ (snd (Over.mk r) D.P.A).left :=
    SecOps.sec_ext fun j => ThetaOne.isPullSecLC_pullTo D f θ j
  have h2 : IsUnit (sval θ (r ≫ g.left) q J) := by
    have e := hth _ (ptSecT D.P.A (toUnit (Over.mk r) ≫ g)).left q J hJ
    rw [← hρ, ← H1.SectionArithmetic.sval_pullSec θ _ _ q hJ, ← hθ'e, ← e]
    exact h1
  have hrq : r q = closedPoint V := by
    show (Spec.map (CommRingCat.ofHom f)).base (closedPoint k) = _
    rw [Spec.map_base]
    exact IsLocalRing.comap_closedPoint f
  refine ⟨fun σ => J (r ≫ σ), fun σ => ?_, ?_⟩
  · have := hJ (r ≫ σ)
    rwa [Scheme.Hom.comp_apply, hrq] at this
  · rw [sval_of θ (r ≫ g.left) q J (fun i => J (r ≫ g.left ≫ D.famφB 0 i)) (fun i => by rw [Category.assoc])] at h2
    have hm : g.left (r q) ∈ (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)).U
        (fun i => J (r ≫ g.left ≫ D.famφB 0 i)) :=
      show g.left (r q) ∈ LB.wchart D.P.L (D.famφB 0) (fun i => J (r ≫ g.left ≫ D.famφB 0 i)) from Set.mem_iInter.2 fun i => by
        have := hJ (r ≫ g.left ≫ D.famφB 0 i)
        simpa [Scheme.Hom.comp_apply] using this
    have h2' : IsUnit ((r.stalkMap q).hom (gs g.left (r q) _ (θ.f (fun i => J (r ≫ g.left ≫ D.famφB 0 i))))) := by
      rw [← gs_comp_stalkMap r g.left q _ hm]; exact h2
    have h3 := isUnit_of_map_unit (r.stalkMap q).hom _ h2'
    rw [hrq] at h3
    exact h3

end GlobalTheory.Poinc.IntTerm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionTranslateThetaSectionUnitStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torsionTranslate_thetaSection_unit : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegPre V) (θ : D.SecB 1 0), IntTerm.IsTheta D θ → ∀ N : ℕ, 2 ≤ N → IsUnit (N : V) → ∀ (C : Type) (b : C → (𝟙_ (Over (Sp V)) ⟶ D.P.A)), IntTerm.Exhausts D.P N b → ∀ a : 𝟙_ (Over (Sp V)) ⟶ D.P.A, ∃ c, IntTerm.UnitAt D θ (a * b c) := by
  first | exact @GlobalTheory.Poinc.IntTerm.exists_unitAt_mul | exact GlobalTheory.Poinc.IntTerm.exists_unitAt_mul | (intros; apply GlobalTheory.Poinc.IntTerm.exists_unitAt_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationGenericFibreEqSiegelFibrePullback
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationGenericFibreEqSiegelFibrePullback
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

namespace GlobalTheory.TInj.GenPull

theorem pull_comp_iso {X Y Z : Scheme.{0}} {L : LB X} {M : LB Y} {F : Y ⟶ X} (H : LBIso M (L.pull F)) (h : Z ⟶ Y) :
    LBIso (M.pull h) (L.pull (h ≫ F)) :=
  LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull M h h rfl) (chartPullSame L _ _ _ h fun _ => rfl) H

theorem pull_congr_iso {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {a b : Y ⟶ X} (e : a = b) :
    LBIso (L.pull a) (L.pull b) := e ▸ GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hL a)

theorem pull_pull_iso {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (a : Y ⟶ X) (b : Z ⟶ Y) :
    LBIso ((L.pull a).pull b) (L.pull (b ≫ a)) :=
  pull_comp_iso (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hL a)) b

theorem pull_id_iso {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) : LBIso L (L.pull (𝟙 X)) :=
  LBIso.chartPull (chartPullId _) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ (𝟙 _) (𝟙 _) rfl) (GlobalTheory.PolBaseChange.lbIso_refl hL)

end GlobalTheory.TInj.GenPull


open GlobalTheory.TInj.GenPull in
theorem GlobalTheory.TInj.overPt_genPull : ∀ {X : Scheme.{0}} {g n : ℕ} {B : Type} [CommRing B] {ζ : B} {sX : X ⟶ Sp B} (c : SiegPre g n ζ sX) (R : Type) [CommRing R] [IsDomain R] (V : Type) [CommRing V] [IsDomain V] (J : Ideal R) (J' : Ideal V) (D₀ : DegData R J) (A₀ : PolAV (Sp (FractionRing R))) (G₀ : Over (Sp R)) [GrpObj G₀] [IsCommMonObj G₀] (U₀ : Unif J D₀ A₀ G₀) (f : R →+* V) (D : DegData V J') (hD : IsPullDeg f D₀.toPre D.toPre) (A : PolAV (Sp (FractionRing V))) (U : Unif J' D A ((Over.pullback (specOf f)).obj G₀)), IsPullUnif f hD (Iso.refl _) U₀ U → ∀ (y₀ : Sp (FractionRing R) ⟶ X) (α₀ : A₀.A.left ⟶ c.A.left), OverPt c A₀ y₀ α₀ → ∀ κ : Sp (FractionRing V) ⟶ Sp (FractionRing R), κ ≫ jK R = jK V ≫ spMap f → ∃ α : A.A.left ⟶ c.A.left, OverPt c A (κ ≫ y₀) α ∧ ∀ (Z : Scheme.{0}) (x : Z ⟶ A.A.left) (x₀ : Z ⟶ A₀.A.left), x ≫ U.gen.inv.left ≫ pullback.fst ((Over.pullback (specOf f)).obj G₀).hom (jK V) ≫ pullback.fst G₀.hom (specOf f) = x₀ ≫ U₀.gen.inv.left ≫ pullback.fst G₀.hom (jK R) → x ≫ α = x₀ ≫ α₀ := by
  intro X g n B _ ζ sX c R _ _ V _ _ J J' D₀ A₀ G₀ _ _ U₀ f D hD A U hU y₀ α₀ hO κ hκ
  let G := (Over.pullback (specOf f)).obj G₀
  let p := pullback.fst G.hom (jK V)
  let q := pullback.fst G₀.hom (specOf f)
  let p₀ := pullback.fst G₀.hom (jK R)
  have hsq : jK V ≫ specOf f = κ ≫ jK R := hκ.symm
  let κG : pullback G.hom (jK V) ⟶ pullback G₀.hom (jK R) :=
    pullback.lift (p ≫ q) (pullback.snd _ _ ≫ κ) (by
      have c1 : q ≫ G₀.hom = G.hom ≫ specOf f := pullback.condition
      have c2 : p ≫ G.hom = pullback.snd G.hom (jK V) ≫ jK V := pullback.condition
      rw [Category.assoc, c1, ← Category.assoc, c2, Category.assoc, hsq, Category.assoc])
  have hκf : κG ≫ p₀ = p ≫ q := pullback.lift_fst _ _ _
  have w : κG ≫ ((Over.pullback (jK R)).obj G₀).hom = ((Over.pullback (jK V)).obj G).hom ≫ κ :=
    pullback.lift_snd _ _ _
  have hκG : IsGrpPullback ((Over.pullback (jK V)).obj G) ((Over.pullback (jK R)).obj G₀) κ κG :=
    (isGrpPullback_pullback G₀ (jK R)).cancel
      (((isGrpPullback_pullback G (jK V)).comp (isGrpPullback_pullback G₀ (specOf f))).congr hsq hκf.symm) w
  have : IsMonHom U.gen.hom := U.gen_hom
  have : IsMonHom U₀.gen.hom := U₀.gen_hom
  have : IsMonHom U.gen.symm.hom := show IsMonHom U.gen.inv by infer_instance
  have hu : IsGrpPullback A.A ((Over.pullback (jK V)).obj G) (𝟙 _) U.gen.inv.left := isGrpPullback_of_iso U.gen.symm
  have hg : IsGrpPullback ((Over.pullback (jK R)).obj G₀) A₀.A (𝟙 _) U₀.gen.hom.left := isGrpPullback_of_iso U₀.gen
  let π : A.A.left ⟶ A₀.A.left := U.gen.inv.left ≫ κG ≫ U₀.gen.hom.left
  have hπ : IsGrpPullback A.A A₀.A κ π := (hu.comp (hκG.comp hg)).congr (by simp) rfl
  obtain ⟨hO₁, α₀₂, sα₀, hΛ₀⟩ := hO

  have hLG : U.LG.L.IsLB := U.LG.isLB
  have hLG₀ : U₀.LG.L.IsLB := U₀.LG.isLB
  obtain ⟨wL, hwL, -⟩ := hU.lg
  have E1 : LBIso (A.L.pull U.gen.hom.left) (U.LG.L.pull p) := U.ext
  have E2 : LBIso (U.LG.L.pull p) (U₀.LG.L.pull (p ≫ (Iso.refl G).hom.left ≫ q)) := pull_comp_iso ⟨wL, hwL⟩ p
  have E4 : LBIso (U₀.LG.L.pull (p ≫ (Iso.refl G).hom.left ≫ q)) (U₀.LG.L.pull (κG ≫ p₀)) :=
    pull_congr_iso hLG₀ (by rw [hκf, Iso.refl_hom, Over.id_left, Category.id_comp])
  have E3 : LBIso ((A₀.L.pull U₀.gen.hom.left).pull κG) (U₀.LG.L.pull (κG ≫ p₀)) := pull_comp_iso U₀.ext κG
  have E5 := pull_pull_iso A₀.isLB U₀.gen.hom.left κG
  have hA₀g := pull_isLB A₀.isLB U₀.gen.hom.left
  have X1 : LBIso (A.L.pull U.gen.hom.left) (A₀.L.pull (κG ≫ U₀.gen.hom.left)) :=
    LBIso.trans (pull_isLB A.isLB _) (pull_isLB hLG _) (pull_isLB A₀.isLB _) E1
      (LBIso.trans (pull_isLB hLG _) (pull_isLB hLG₀ _) (pull_isLB A₀.isLB _) E2
        (LBIso.trans (pull_isLB hLG₀ _) (pull_isLB hLG₀ _) (pull_isLB A₀.isLB _) E4
          (LBIso.trans (pull_isLB hLG₀ _) (pull_isLB hA₀g _) (pull_isLB A₀.isLB _) E3.symm E5)))
  have X2 : LBIso ((A.L.pull U.gen.hom.left).pull U.gen.inv.left) (A₀.L.pull π) := pull_comp_iso X1 _
  have X3 : LBIso A.L ((A.L.pull U.gen.hom.left).pull U.gen.inv.left) :=
    LBIso.trans A.isLB (pull_isLB A.isLB _) (pull_isLB (pull_isLB A.isLB _) _) (pull_id_iso A.isLB)
      (LBIso.trans (pull_isLB A.isLB _) (pull_isLB A.isLB _) (pull_isLB (pull_isLB A.isLB _) _)
        (pull_congr_iso A.isLB (by rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]))
        (pull_pull_iso A.isLB _ _).symm)
  have hA : LBIso A.L (A₀.L.pull π) :=
    LBIso.trans A.isLB (pull_isLB (pull_isLB A.isLB _) _) (pull_isLB A₀.isLB _) X3 X2
  have sπ := GlobalTheory.LamPull.exists_isSquare hπ.1.w
  have hΛ := GlobalTheory.LamPull.lbIso_lam_pull hπ A₀.isLB A.isLB hA sπ
  have hΛA : (abelian₂ A.A A.L).IsLB := DVR.linComb_isLB _ A.isLB _ _
  have hΛA₀ : (abelian₂ A₀.A A₀.L).IsLB := DVR.linComb_isLB _ A₀.isLB _ _
  refine ⟨π ≫ α₀, ⟨hπ.comp hO₁, _ ≫ α₀₂, ⟨?_, ?_⟩,
    LBIso.trans hΛA (pull_isLB hΛA₀ _) (pull_isLB c.isLB _) hΛ (pull_comp_iso hΛ₀ _)⟩, ?_⟩
  · rw [Category.assoc, sα₀.1, ← Category.assoc, sπ.1, Category.assoc]
  · rw [Category.assoc, sα₀.2, ← Category.assoc, sπ.2, Category.assoc]
  · intro Z x x₀ hx
    have : Mono (jK R) := GlobalTheory.GenericBundleDescent.mono_jK R
    have : Mono p₀ := pullback.fst_of_mono
    have h1 : x ≫ U.gen.inv.left ≫ κG = x₀ ≫ U₀.gen.inv.left := by
      apply (cancel_mono p₀).1
      simp only [Category.assoc, hκf]
      exact hx
    show x ≫ (U.gen.inv.left ≫ κG ≫ U₀.gen.hom.left) ≫ α₀ = x₀ ≫ α₀
    rw [← Category.assoc, ← Category.assoc, ← Category.assoc, Category.assoc x, h1]
    simp only [Category.assoc]
    rw [← Category.assoc U₀.gen.inv.left, ← Over.comp_left, Iso.inv_hom_id, Over.id_left, Category.id_comp]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationGenericFibreEqSiegelFibrePullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisation_genericFibre_eq_siegelFibre_pullback : ∀ {X : Scheme.{0}} {g n : ℕ} {B : Type} [CommRing B] {ζ : B} {sX : X ⟶ Sp B} (c : SiegPre g n ζ sX) (R : Type) [CommRing R] [IsDomain R] (V : Type) [CommRing V] [IsDomain V] (J : Ideal R) (J' : Ideal V) (D₀ : DegData R J) (A₀ : PolAV (Sp (FractionRing R))) (G₀ : Over (Sp R)) [GrpObj G₀] [IsCommMonObj G₀] (U₀ : Unif J D₀ A₀ G₀) (f : R →+* V) (D : DegData V J') (hD : IsPullDeg f D₀.toPre D.toPre) (A : PolAV (Sp (FractionRing V))) (U : Unif J' D A ((Over.pullback (specOf f)).obj G₀)), IsPullUnif f hD (Iso.refl _) U₀ U → ∀ (y₀ : Sp (FractionRing R) ⟶ X) (α₀ : A₀.A.left ⟶ c.A.left), OverPt c A₀ y₀ α₀ → ∀ κ : Sp (FractionRing V) ⟶ Sp (FractionRing R), κ ≫ jK R = jK V ≫ spMap f → ∃ α : A.A.left ⟶ c.A.left, OverPt c A (κ ≫ y₀) α ∧ ∀ (Z : Scheme.{0}) (x : Z ⟶ A.A.left) (x₀ : Z ⟶ A₀.A.left), x ≫ U.gen.inv.left ≫ pullback.fst ((Over.pullback (specOf f)).obj G₀).hom (jK V) ≫ pullback.fst G₀.hom (specOf f) = x₀ ≫ U₀.gen.inv.left ≫ pullback.fst G₀.hom (jK R) → x ≫ α = x₀ ≫ α₀ := by
  first | exact @GlobalTheory.TInj.overPt_genPull | exact GlobalTheory.TInj.overPt_genPull | (intros; apply GlobalTheory.TInj.overPt_genPull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoOriginOneOfGenericOriginDomain
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoOriginOneOfGenericOriginDomain
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

noncomputable section

namespace GlobalTheory.GenOrigin

theorem jK_appTop_inj (R : Type) [CommRing R] [IsDomain R] : Function.Injective (jK R).appTop.hom := by
  have hs := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).2
  have hi := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv).1
  intro x y h
  obtain ⟨a, rfl⟩ := hs x
  obtain ⟨b, rfl⟩ := hs y
  have e := fun c => congrArg (fun q => q.hom c)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  have := hi ((e a).trans (h.trans (e b).symm))
  rw [IsFractionRing.injective R (FractionRing R) this]

theorem exists_unit_along {S X X' B B' : Scheme.{0}} (M : LB B) (M' : LB B') (hM : M.IsLB) (hM' : M'.IsLB)
    {K : Type} [Fintype K] (φ : K → (X ⟶ B)) (φ' : K → (X' ⟶ B')) (ε : K → ℤ) (hε : ∑ k, ε k = 0) (F : X' ⟶ X)
    (e : S ⟶ X') (q : S ⟶ B) (q' : S ⟶ B') (hq : ∀ k, (e ≫ F) ≫ φ k = q)
    (hq' : ∀ k, e ≫ φ' k = q') (w : LB.Iso (LB.LinComb M' φ' ε) ((LB.LinComb M φ ε).pull F)) (hw : w.IsGen) :
    ∃ u : Γ(S, ⊤)ˣ, ∀ (Z : Scheme.{0}) (t : Z ⟶ S) (z : Z) (a : M.ι) (b : M'.ι), q (t z) ∈ M.U a →
      q' (t z) ∈ M'.U b → gw w (t ≫ e) z (fun _ => a) (fun _ => b) = gm t z ⊤ u := by
  let C : M.ι × M'.ι → X'.Opens := fun i =>
    ((LB.LinComb M φ ε).pull F).U (fun _ _ => i.1) ⊓ (LB.LinComb M' φ' ε).U (fun _ => i.2)
  have mem : ∀ (x : S) (a : M.ι) (b : M'.ι), q x ∈ M.U a → q' x ∈ M'.U b → e x ∈ C (a, b) := fun x a b ha hb =>
    ⟨mem_pull.2 (NormIso.mem_const M φ (e ≫ F) q hq x a ha), NormIso.mem_const M' φ' e q' hq' x b hb⟩
  obtain ⟨u, hu⟩ := glue_unit (⊤ : S.Opens) (fun i => e ⁻¹ᵁ C i) (fun _ => le_top) (fun x _ => by
      obtain ⟨a, ha⟩ := exists_chart hM (q x)
      obtain ⟨b, hb⟩ := exists_chart hM' (q' x)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(a, b), mem x a b ha hb⟩)
    (fun i => pullU e (C i) (w.s (fun _ _ => i.1, fun _ => i.2))) (fun i j x hx => by
      have hi : e x ∈ C i := hx.1
      have hj : e x ∈ C j := hx.2
      refine (gm_pull (𝟙 S) e x (C i) hi _).trans (Eq.trans ?_ (gm_pull (𝟙 S) e x (C j) hj _).symm)
      rw [Category.id_comp]
      have h := (isGen_iff w).1 hw S e x (fun _ => i.1) (fun _ => j.1) (fun _ => i.2) (fun _ => j.2)
        (mem_pull.1 hi.1) (mem_pull.1 hj.1) hi.2 hj.2
      refine h.trans ((congrArg (· * _) ((congrArg₂ (fun s t => s * t⁻¹)
        (NormIso.gm_const M φ ε hε (e ≫ F) q hq x i.1 j.1 (mem_pull.1 hi.1) (mem_pull.1 hj.1))
        (NormIso.gm_const M' φ' ε hε e q' hq' x i.2 j.2 hi.2 hj.2)).trans (mul_inv_cancel 1))).trans (_root_.one_mul _)))
  refine ⟨u, fun Z t z a b ha hb => ?_⟩
  have hm : e (t z) ∈ C (a, b) := mem (t z) a b ha hb
  exact (gm_pull t e z (C (a, b)) hm _).symm.trans ((congrArg (gm t z (e ⁻¹ᵁ C (a, b))) (hu (a, b)).symm).trans
    (gm_res t z le_top hm u))

theorem lamVal_origin_of_generic : ∀ {S : Scheme.{0}} {V : Type} [CommRing V] [IsDomain V] (B : Over S) (B' : Over (Sp V)) [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B'] (M : LB B.left) (M' : LB B'.left), M.IsLB → M'.IsLB → ∀ (f : Sp V ⟶ S) (β : B'.left ⟶ B.left) (β₂ : (G2 B').left ⟶ (G2 B).left) (w : LB.Iso (abelian₂ B' M') ((abelian₂ B M).pull β₂)), IsGrpPullback B' B f β → IsSquare β β₂ → w.IsGen → (∀ (z : (TK V).left) (J : ((TK V).left ⟶ B.left) → M.ι) (J' : ((TK V).left ⟶ B'.left) → M'.ι), Good M z J → Good M' z J' → lamVal w (lift (1 : TK V ⟶ B') (1 : TK V ⟶ B')).left z J J' = 1) → ∀ (T : Over (Sp V)) (z : T.left) (J : (T.left ⟶ B.left) → M.ι) (J' : (T.left ⟶ B'.left) → M'.ι), Good M z J → Good M' z J' → lamVal w (lift (1 : T ⟶ B') (1 : T ⟶ B')).left z J J' = 1 := by
  intro S V _ _ B B' _ _ _ _ M M' hM hM' f β β₂ w hpb hs hw hgen
  let O : Over (Sp V) := 𝟙_ (Over (Sp V))
  let e : O.left ⟶ (G2 B').left := (lift (1 : O ⟶ B') 1).left
  let q : O.left ⟶ B.left := (1 : Over.mk (O.hom ≫ f) ⟶ B).left
  let q' : O.left ⟶ B'.left := (1 : O ⟶ B').left
  have hq : ∀ I : ULift.{0} (Finset (Fin 2)), (e ≫ β₂) ≫ (psum B (x2 B) I.down).left = q := fun I =>
    (congrArg (· ≫ (psum B (x2 B) I.down).left) (NormIso.origin_square hpb hs O)).trans
      (congrArg (fun z => z.left) (NormIso.lift_one_psum B (T := Over.mk (O.hom ≫ f)) I.down))
  have hq' : ∀ I : ULift.{0} (Finset (Fin 2)), e ≫ (psum B' (x2 B') I.down).left = q' := fun I =>
    congrArg (fun z => z.left) (NormIso.lift_one_psum B' (T := O) I.down)
  obtain ⟨u, hu⟩ := exists_unit_along M M' hM hM' (K := ULift.{0} (Finset (Fin 2)))
    (fun I => (psum B (x2 B) I.down).left) (fun I => (psum B' (x2 B') I.down).left)
    (fun I => (-1) ^ (2 - I.down.card)) (by decide) β₂ e q q' hq hq' w hw
  have hval : ∀ (T : Over (Sp V)) (z : T.left) (J : (T.left ⟶ B.left) → M.ι) (J' : (T.left ⟶ B'.left) → M'.ι),
      Good M z J → Good M' z J' →
      lamVal w (lift (1 : T ⟶ B') (1 : T ⟶ B')).left z J J' = gm (toUnit T).left z ⊤ u := by
    intro T z J J' hJ hJ'
    have hp : (lift (1 : T ⟶ B') (1 : T ⟶ B')).left = (toUnit T).left ≫ e := by
      show _ = (toUnit T ≫ lift (1 : O ⟶ B') 1).left
      rw [comp_lift, MonObj.comp_one]
    have key : ∀ (p : T.left ⟶ (G2 B').left) (j : (abelian₂ B M).ι) (k : (abelian₂ B' M').ι),
        (fun I : ULift.{0} (Finset (Fin 2)) => J (p ≫ β₂ ≫ (psum B (x2 B) I.down).left)) = j →
        (fun I : ULift.{0} (Finset (Fin 2)) => J' (p ≫ (psum B' (x2 B') I.down).left)) = k →
        lamVal w p z J J' = gw (L := abelian₂ B M) (L' := abelian₂ B' M') w p z j k := by
      rintro p _ _ rfl rfl
      rfl
    rw [hp]
    refine (key _ (fun _ => J ((toUnit T).left ≫ q)) (fun _ => J' ((toUnit T).left ≫ q')) (funext fun I => ?_)
      (funext fun I => ?_)).trans (hu T.left (toUnit T).left z _ _ (hJ ((toUnit T).left ≫ q)) (hJ' ((toUnit T).left ≫ q')))
    · rw [← hq I, Category.assoc, Category.assoc]
    · rw [← hq' I, Category.assoc]
  have hK : (toUnit (TK V)).left = jK V := by simpa using Over.w (toUnit (TK V))
  have h1 : (Units.map (jK V).appTop.hom.toMonoidHom u : Γ((TK V).left, ⊤)ˣ) = 1 := unit_ext fun x _ => by
    choose a ha using fun χ : (TK V).left ⟶ B.left => exists_chart hM (χ x)
    choose b hb using fun χ : (TK V).left ⟶ B'.left => exists_chart hM' (χ x)
    have h := (hval (TK V) x a b ha hb).symm.trans (hgen x a b ha hb)
    rw [hK] at h
    rw [map_one]
    exact (gm_pull (𝟙 _) (jK V) x ⊤ trivial u).trans ((congrArg (fun g => gm g x ⊤ u) (Category.id_comp _)).trans h)
  have hu1 : u = 1 := Units.ext (jK_appTop_inj V (by
    have := congrArg Units.val h1
    simpa using this))
  intro T z J J' hJ hJ'
  rw [hval T z J J' hJ hJ', hu1]; exact map_one _

end GlobalTheory.GenOrigin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoOriginOneOfGenericOriginDomainStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumfordBundleIso_origin_one_of_generic_origin_domain : ∀ {S : Scheme.{0}} {V : Type} [CommRing V] [IsDomain V] (B : Over S) (B' : Over (Sp V)) [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B'] (M : LB B.left) (M' : LB B'.left), M.IsLB → M'.IsLB → ∀ (f : Sp V ⟶ S) (β : B'.left ⟶ B.left) (β₂ : (G2 B').left ⟶ (G2 B).left) (w : LB.Iso (abelian₂ B' M') ((abelian₂ B M).pull β₂)), IsGrpPullback B' B f β → IsSquare β β₂ → w.IsGen → (∀ (z : (TK V).left) (J : ((TK V).left ⟶ B.left) → M.ι) (J' : ((TK V).left ⟶ B'.left) → M'.ι), Good M z J → Good M' z J' → lamVal w (lift (1 : TK V ⟶ B') (1 : TK V ⟶ B')).left z J J' = 1) → ∀ (T : Over (Sp V)) (z : T.left) (J : (T.left ⟶ B.left) → M.ι) (J' : (T.left ⟶ B'.left) → M'.ι), Good M z J → Good M' z J' → lamVal w (lift (1 : T ⟶ B') (1 : T ⟶ B')).left z J J' = 1 := by
  first | exact @GlobalTheory.GenOrigin.lamVal_origin_of_generic | exact GlobalTheory.GenOrigin.lamVal_origin_of_generic | (intros; apply GlobalTheory.GenOrigin.lamVal_origin_of_generic <;> assumption)
end
end
