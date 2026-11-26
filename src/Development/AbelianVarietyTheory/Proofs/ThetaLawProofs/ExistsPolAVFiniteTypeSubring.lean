module

public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRefinementOfIsLimit
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusOfUnit
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfAmpleGeometricFibresAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothGrpSchemeDescendsToFgSubring

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.RelAmpleSubring
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

namespace GlobalTheory.AmpleSubring

theorem relAmple_subring : ∀ (S : Type) [CommRing S] [IsLocalRing S] (R₀ : Subring S) [IsNoetherianRing R₀] (P : Out.PolAV (Sp S)) (A₀ : Over (Sp R₀)) [GrpObj A₀] (φ : P.A.left ⟶ A₀.left) (L₀ : LB A₀.left), IsAbelianScheme A₀ → IsProjOver A₀.hom → L₀.IsLB → IsGrpPullback P.A A₀ (spMap R₀.subtype) φ → LBIso P.L (L₀.pull φ) → ∃ F : Finset S, ∀ (R₁ : Subring S) (h : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (A₁ : Over (Sp R₁)) [GrpObj A₁] (π : A₁.left ⟶ A₀.left), IsGrpPullback A₁ A₀ (spMap (Subring.inclusion h)) π → Out.RelAmple A₁ (L₀.pull π) := by
  intro S _ _ R₀ _ P A₀ _ φ L₀ hA₀ hproj hL₀ hφ e
  have := hA₀.proper
  have := hA₀.smooth
  let x : R₀ →+* IsLocalRing.ResidueField S := (IsLocalRing.residue S).comp R₀.subtype
  let p : Ideal R₀ := RingHom.ker x
  have : p.IsPrime := RingHom.ker_isPrime x
  let g := algebraMap R₀ p.ResidueField
  let i : p.ResidueField →+* IsLocalRing.ResidueField S :=
    Ideal.ResidueField.lift p x le_rfl fun a ha => IsUnit.mk0 _ ha
  have hi : i.comp g = x := RingHom.ext fun a => Ideal.ResidueField.lift_algebraMap p x le_rfl
    (fun a ha => IsUnit.mk0 _ ha) a
  have hu : spMap (IsLocalRing.residue S) ≫ spMap R₀.subtype = spMap i ≫ spMap g := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hi]
  have h₂ := IsPullback.of_hasPullback A₀.hom (spMap i ≫ spMap g)
  obtain ⟨r, hr, hA⟩ := GlobalTheory.T.relAmple_near_fibre_flat_projective R₀ A₀ L₀ inferInstance
    ((ProjSpace.isProjBy_iff_isProjOver _).2 hproj) hL₀ _ g (FibreAmple.residueField_fraction p)
    (FibreAmple.relAmple_of_fieldExtension hL₀ i (IsPullback.of_hasPullback A₀.hom (spMap g)) h₂
      (LB.isLB_pull hL₀ _) (GlobalTheory.lbIso_refl (LB.isLB_pull hL₀ _))
      (FibreAmple.relAmple_of_factor hL₀ hφ.1 h₂ _ hu P.isLB e P.ample))
  have hx : x r ≠ 0 := fun h => hr (Ideal.algebraMap_residueField_eq_zero.2 h)
  obtain ⟨v, hv⟩ : IsUnit (r : S) := (IsLocalRing.residue_ne_zero_iff_isUnit _).1 hx
  refine ⟨{v⁻¹.val}, fun R₁ h hF A₁ _ π hπ => ?_⟩
  have hu₁ : IsUnit (Subring.inclusion h r) :=
    IsUnit.of_mul_eq_one (⟨v⁻¹.val, hF (by simp)⟩ : R₁) (Subtype.ext (by
      change (r : S) * v⁻¹.val = 1
      rw [← hv, Units.mul_inv]))
  let D : (Spec (CommRingCat.of R₀)).Opens := PrimeSpectrum.basicOpen r
  have hrange : Set.range (spMap (Subring.inclusion h)) ⊆ Set.range D.ι := by
    rintro _ ⟨z, rfl⟩
    exact ⟨⟨_, fun hm => z.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hm hu₁)⟩, rfl⟩
  exact FibreAmple.relAmple_of_factor hL₀ (IsPullback.of_hasPullback A₀.hom D.ι) hπ.1
    (IsOpenImmersion.lift D.ι _ hrange) (IsOpenImmersion.lift_fac _ _ _) (LB.isLB_pull hL₀ _)
    (GlobalTheory.lbIso_refl (LB.isLB_pull hL₀ _)) hA

end GlobalTheory.AmpleSubring
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsFinsetKTrivOfSubring
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

namespace GlobalTheory


open scoped CategoryTheory.Obj in
theorem exists_finset_kTriv_of_subring :
    ∀ (S : Type) [CommRing S] [IsLocalRing S] (R₀ : Subring S) [IsNoetherianRing R₀] (P : Out.PolAV (Sp S)) (A₀ : Over (Sp R₀)) [GrpObj A₀] (φ : P.A.left ⟶ A₀.left) (L₀ : LB A₀.left), IsAbelianScheme A₀ → L₀.IsLB → Out.RelAmple A₀ L₀ → IsGrpPullback P.A A₀ (spMap R₀.subtype) φ → LBIso P.L (L₀.pull φ) → ∃ F : Finset S, ∀ (R₁ : Subring S) (h : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (A₁ : Over (Sp R₁)) [GrpObj A₁] (π : A₁.left ⟶ A₀.left), IsGrpPullback A₁ A₀ (spMap (Subring.inclusion h)) π → Out.KTriv A₁ (L₀.pull π) := by
  intro S _ _ R₀ _ P A₀ _ φ L₀ hA hL hamp hφ e
  let r : S →+* IsLocalRing.ResidueField S := IsLocalRing.residue S
  letI : GrpObj ((Over.pullback (spMap r)).obj P.A) := Functor.grpObjObj
  have h₁ := isGrpPullback_pullback P.A (spMap r)
  have hc : spMap r ≫ spMap R₀.subtype = spMap (r.comp R₀.subtype) := by
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  have h₂ := h₁.comp hφ
  rw [hc] at h₂
  have he : LBIso (L₀.pull (pullback.fst P.A.hom (spMap r) ≫ φ))
      (P.L.pull (pullback.fst P.A.hom (spMap r))) :=
    LBIso.symm (LBIso.chartPull (chartPullPull P.L _)
      (chartPullSame L₀ (fun _ : PUnit => pullback.fst P.A.hom (spMap r) ≫ φ) (fun _ => φ) (fun _ => 1) _
        fun _ => rfl) e)
  have hK := (amplePt _ _ _ _ _ _ h₁ _ _ P.isLB (pull_isLB hL _) he P.ample P.ktriv).2
  obtain ⟨f, hf, H⟩ := GlobalTheory.KTrivSpread.exists_kTriv_of_isUnit R₀ A₀ L₀ _ (r.comp R₀.subtype) _ _ hA hL hamp h₂ hK
  have hu : IsUnit (f : S) := (IsLocalRing.residue_ne_zero_iff_isUnit _).1 hf
  obtain ⟨g, hg⟩ := hu.exists_right_inv
  refine ⟨{g}, fun R₁ h hF A₁ _ π hπ => H R₁ (Subring.inclusion h) A₁ π ?_ hπ⟩
  have hg₁ : g ∈ R₁ := hF (by simp)
  exact IsUnit.of_mul_eq_one (⟨g, hg₁⟩ : R₁) (Subtype.ext hg)

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsProjectiveAbelianModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open scoped CategoryTheory.Obj

namespace GlobalTheory.KeyTf

theorem exists_isGrpPullback_of_le {S : Type} [CommRing S] {R₀ R₁ : Subring S} (h : R₀ ≤ R₁) (A : Over (Sp S))
    [GrpObj A] (A₀ : Over (Sp R₀)) [GrpObj A₀] (φ : A.left ⟶ A₀.left)
    (H : IsGrpPullback A A₀ (spMap R₀.subtype) φ) :
    ∃ φ₁ : A.left ⟶ ((Over.pullback (spMap (Subring.inclusion h))).obj A₀).left,
      IsGrpPullback A ((Over.pullback (spMap (Subring.inclusion h))).obj A₀) (spMap R₁.subtype) φ₁ := by
  have e : spMap R₀.subtype = spMap R₁.subtype ≫ spMap (Subring.inclusion h) :=
    spMap_comp (Subring.inclusion h) R₁.subtype
  have hp := isGrpPullback_pullback A₀ (spMap (Subring.inclusion h))
  refine ⟨hp.1.lift φ (A.hom ≫ spMap R₁.subtype) (by rw [H.1.w, e, Category.assoc]), ?_⟩
  exact IsGrpPullback.cancel hp (H.congr e (hp.1.lift_fst _ _ _).symm) (hp.1.lift_snd _ _ _)

theorem exists_projective_abelian_model : ∀ (S : Type) [CommRing S] [IsDomain S] [IsLocalRing S] (P : Out.PolAV (Sp S)), ∃ (R : Subring S) (A₀ : Over (Sp R)) (_ : GrpObj A₀) (φ : P.A.left ⟶ A₀.left), Algebra.FiniteType ℤ R ∧ IsAbelianScheme A₀ ∧ SmoothOfRelativeDimension P.g A₀.hom ∧ IsProjOver A₀.hom ∧ IsGrpPullback P.A A₀ (spMap R.subtype) φ := by
  intro S _ _ _ P
  have hc := P.isAb.comm
  have hs := P.isAb.smooth
  have hpr := P.isAb.proper
  have hg := P.isAb.geomConnected
  obtain ⟨R₀, A₀, _, _, φ₀, -, hft₀, hs₀, hsep₀, hqc₀, H₀⟩ :=
    GlobalTheory.smooth_grpScheme_descends_to_fg_subring S P.A ∅ hs inferInstance inferInstance
  obtain ⟨F, hF⟩ := GlobalTheory.T.isProjOver_descends_to_subring' S R₀ _ _ P.A.hom A₀.hom φ₀ H₀.1 (GlobalTheory.ProjSpace.isProjOver_polAV P)
  obtain ⟨R₁, h₀₁, hF₁, hft₁⟩ := exists_finiteType_subring_adjoin S R₀ F hft₀
  obtain ⟨A₁, _, _, φ₁, hp₁, hs₁, H₁⟩ : ∃ (A₁ : Over (Sp R₁)) (_ : GrpObj A₁) (_ : IsCommMonObj A₁)
      (φ₁ : P.A.left ⟶ A₁.left), IsProjOver A₁.hom ∧ Smooth A₁.hom ∧ IsGrpPullback P.A A₁ (spMap R₁.subtype) φ₁ := by
    obtain ⟨φ₁, H₁⟩ := exists_isGrpPullback_of_le h₀₁ P.A A₀ φ₀ H₀
    exact ⟨_, _, inferInstance, φ₁, hF R₁ h₀₁ hF₁ _ _ _ (IsPullback.of_hasPullback _ _),
      inferInstanceAs (Smooth (pullback.snd _ _)), H₁⟩
  let κ := IsLocalRing.residue S
  have e₁ : spMap (κ.comp R₁.subtype) = spMap κ ≫ spMap R₁.subtype := spMap_comp _ _
  have hfib : GeometricallyConnected (pullback.snd A₁.hom (spMap (κ.comp R₁.subtype))) := by
    have Q := IsPullback.of_hasPullback A₁.hom (spMap (κ.comp R₁.subtype))
    let l := H₁.1.lift (pullback.fst A₁.hom (spMap (κ.comp R₁.subtype))) (pullback.snd _ _ ≫ spMap κ)
      (by rw [Q.w, e₁, Category.assoc])
    have Q' : IsPullback l (pullback.snd A₁.hom (spMap (κ.comp R₁.subtype))) P.A.hom (spMap κ) :=
      IsPullback.of_right (by rw [H₁.1.lift_fst, ← e₁]; exact Q) (H₁.1.lift_snd _ _ _) H₁.1
    exact MorphismProperty.of_isPullback (P := @GeometricallyConnected) Q' hg
  obtain ⟨f, hf, hconn⟩ := GlobalTheory.T.geometricallyConnected_open_condition_smooth_projective R₁ _ A₁.hom _ (κ.comp R₁.subtype) hp₁ hs₁ hfib
  obtain ⟨u, hu⟩ : IsUnit (f : S) := (IsLocalRing.residue_ne_zero_iff_isUnit _).1 hf
  obtain ⟨R₂, h₁₂, hF₂, hft₂⟩ := exists_finiteType_subring_adjoin S R₁ {((u⁻¹ : Sˣ) : S)} hft₁
  obtain ⟨φ₂, H₂⟩ := exists_isGrpPullback_of_le h₁₂ P.A A₁ φ₁ H₁
  have hunit : IsUnit (Subring.inclusion h₁₂ f) :=
    IsUnit.of_mul_eq_one (⟨((u⁻¹ : Sˣ) : S), hF₂ (by simp)⟩ : R₂) (Subtype.ext (by
      show (f : S) * _ = 1
      rw [← hu]; exact u.mul_inv))
  have hp₂ : IsProjOver ((Over.pullback (spMap (Subring.inclusion h₁₂))).obj A₁).hom :=
    GlobalTheory.ProjSpace.isProjOver_pullback_snd _ hp₁
  have hab : IsAbelianScheme ((Over.pullback (spMap (Subring.inclusion h₁₂))).obj A₁) :=
    ⟨inferInstance, inferInstanceAs (Smooth (pullback.snd _ _)), projProper _ _ _ hp₂, hconn R₂ _ hunit⟩
  refine ⟨R₂, _, inferInstance, φ₂, hft₂, hab, ?_, hp₂, H₂⟩
  have e₂ : spMap (κ.comp R₂.subtype) = spMap κ ≫ spMap R₂.subtype := spMap_comp _ _
  refine GlobalTheory.CM.smoothOfRelativeDimension_of_fibre R₂ _ (κ.comp R₂.subtype) _ _
    (pullback.fst P.A.hom (spMap κ) ≫ φ₂) (pullback.snd P.A.hom (spMap κ)) P.g hab ?_ ?_
  · rw [e₂]; exact (IsPullback.of_hasPullback _ _).paste_horiz H₂.1
  · exact (smoothOfRelativeDimension_isStableUnderBaseChange P.g).of_isPullback (IsPullback.of_hasPullback _ _)
      P.smoothDim

end GlobalTheory.KeyTf
end

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

namespace GlobalTheory.KeyTf

private theorem spMap_subtype_comp_inclusion' {S : Type} [CommRing S] {R R' : Subring S} (h : R ≤ R') :
    spMap R'.subtype ≫ spMap (Subring.inclusion h) = spMap R.subtype := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

private theorem exists_lift_to_pullback_grpPullback {S : Type} [CommRing S] {R R' : Subring S} (h : R ≤ R') (A : Over (Sp S))
    [GrpObj A] (A₀ : Over (Sp R)) [GrpObj A₀] (φ : A.left ⟶ A₀.left) (H : IsGrpPullback A A₀ (spMap R.subtype) φ) :
    ∃ φ₁ : A.left ⟶ ((Over.pullback (spMap (Subring.inclusion h))).obj A₀).left,
      φ₁ ≫ pullback.fst A₀.hom (spMap (Subring.inclusion h)) = φ ∧
      IsGrpPullback A ((Over.pullback (spMap (Subring.inclusion h))).obj A₀) (spMap R'.subtype) φ₁ := by
  have w : φ ≫ A₀.hom = (A.hom ≫ spMap R'.subtype) ≫ spMap (Subring.inclusion h) := by
    rw [Category.assoc, spMap_subtype_comp_inclusion' h]
    exact H.1.w
  refine ⟨pullback.lift φ (A.hom ≫ spMap R'.subtype) w, pullback.lift_fst _ _ _, ?_⟩
  refine IsGrpPullback.cancel (isGrpPullback_pullback A₀ (spMap (Subring.inclusion h))) ?_ ?_
  · exact H.congr (spMap_subtype_comp_inclusion' h).symm (pullback.lift_fst _ _ _).symm
  · exact pullback.lift_snd _ _ _

theorem exists_model_of_le {S : Type} [CommRing S] {R R' : Subring S} (h : R ≤ R') (A : Over (Sp S)) [GrpObj A]
    (A₀ : Over (Sp R)) [GrpObj A₀] (φ : A.left ⟶ A₀.left) (H : IsGrpPullback A A₀ (spMap R.subtype) φ) :
    ∃ (A₁ : Over (Sp R')) (_ : GrpObj A₁) (φ₁ : A.left ⟶ A₁.left) (π : A₁.left ⟶ A₀.left), φ₁ ≫ π = φ ∧
      IsGrpPullback A₁ A₀ (spMap (Subring.inclusion h)) π ∧ IsGrpPullback A A₁ (spMap R'.subtype) φ₁ := by
  obtain ⟨φ₁, e, H₁⟩ := exists_lift_to_pullback_grpPullback h A A₀ φ H
  exact ⟨_, inferInstance, φ₁, _, e, isGrpPullback_pullback A₀ _, H₁⟩

private theorem lbIso_pull_comp_theta_law {X Y Z : Scheme.{0}} {L : LB Z} (hL : L.IsLB) (φ₁ : X ⟶ Y) (π : Y ⟶ Z) :
    LBIso (L.pull (φ₁ ≫ π)) ((L.pull π).pull φ₁) := by
  refine LBLimit.lbIso_of_refinement _ _ (LB.isLB_pull hL _) (fun a _ => a ⟨⟩ ⟨⟩) ?_ ?_
  · intro a y hy
    have h1 := (mem_pull (L := L.pull π)).1 hy
    have h2 := (mem_pull (L := L)).1 h1
    exact (mem_pull (L := L)).2 h2
  · intro a b y ha hb
    have ha' := (mem_pull (L := L)).1 ((mem_pull (L := L.pull π)).1 ha)
    have hb' := (mem_pull (L := L)).1 ((mem_pull (L := L.pull π)).1 hb)
    rw [gm_pull_g (L.pull π) φ₁ (𝟙 X) y a b ha hb, gm_pull_g L π (𝟙 X ≫ φ₁) y (a ⟨⟩) (b ⟨⟩)
      ((mem_pull (L := L.pull π)).1 ha) ((mem_pull (L := L.pull π)).1 hb),
      gm_pull_g L (φ₁ ≫ π) (𝟙 X) y (fun _ => a ⟨⟩ ⟨⟩) (fun _ => b ⟨⟩ ⟨⟩) ((mem_pull (L := L)).2 ha')
      ((mem_pull (L := L)).2 hb')]
    simp only [Category.assoc]

theorem lbIso_pull_pull_of_comp {X Y Z : Scheme.{0}} {M : LB X} {L : LB Z} (hM : M.IsLB) (hL : L.IsLB)
    {φ : X ⟶ Z} {φ₁ : X ⟶ Y} {π : Y ⟶ Z} (e : φ₁ ≫ π = φ) (H : LBIso M (L.pull φ)) :
    LBIso M ((L.pull π).pull φ₁) := by
  subst e
  exact LBIso.trans hM (LB.isLB_pull hL _) (LB.isLB_pull (LB.isLB_pull hL _) _) H (lbIso_pull_comp_theta_law hL φ₁ π)

private theorem exists_intermediate_abelian_model_factorization {S : Type} [CommRing S] {g : ℕ} {R R' : Subring S} (h : R ≤ R') (A : Over (Sp S))
    [GrpObj A] (A₀ : Over (Sp R)) [GrpObj A₀] (φ : A.left ⟶ A₀.left) (H : IsGrpPullback A A₀ (spMap R.subtype) φ)
    (hab : IsAbelianScheme A₀) (hpr : IsProjOver A₀.hom) (hsm : SmoothOfRelativeDimension g A₀.hom) :
    ∃ (A₁ : Over (Sp R')) (_ : GrpObj A₁) (φ₁ : A.left ⟶ A₁.left) (π : A₁.left ⟶ A₀.left), φ₁ ≫ π = φ ∧
      IsGrpPullback A₁ A₀ (spMap (Subring.inclusion h)) π ∧ IsGrpPullback A A₁ (spMap R'.subtype) φ₁ ∧
      IsAbelianScheme A₁ ∧ IsProjOver A₁.hom ∧ SmoothOfRelativeDimension g A₁.hom := by
  obtain ⟨φ₁, e, H₁⟩ := exists_lift_to_pullback_grpPullback h A A₀ φ H
  have hp := isGrpPullback_pullback A₀ (spMap (Subring.inclusion h))
  refine ⟨_, inferInstance, φ₁, _, e, hp, H₁, ?_, ?_, ?_⟩
  · exact Out.TLinPf.isAb_pullback _ A₀ hab
  · exact ProjSpace.isProjOver_of_isPullback_spMap (Subring.inclusion h) hp.1 hpr
  · exact (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hp.1 hsm

theorem exists_polAV_finiteType_subring :
    ∀ (S : Type) [CommRing S] [IsDomain S] [IsLocalRing S] (P : Out.PolAV (Sp S)), ∃ (R : Subring S) (P₀ : Out.PolAV (Sp R)) (φ : P.A.left ⟶ P₀.A.left), Algebra.FiniteType ℤ R ∧ P₀.g = P.g ∧ IsGrpPullback P.A P₀.A (spMap R.subtype) φ ∧ LBIso P.L (P₀.L.pull φ) := by
  classical
  intro S _ _ _ P
  obtain ⟨R₀, A₀, _, φ₀, hR₀, hab₀, hsm₀, hpr₀, H₀⟩ := exists_projective_abelian_model S P
  have := hab₀.proper
  obtain ⟨F₁, hF₁⟩ := LBLimit.lb_descends_to_fg_subring S R₀ P.A.left A₀.left P.A.hom A₀.hom φ₀ P.L H₀.1 P.isLB
  obtain ⟨R₁, hle₁, hsub₁, hR₁⟩ := exists_finiteType_subring_adjoin S R₀ F₁ hR₀
  obtain ⟨A₁, _, φ₁, π₁, e₁, Hπ₁, H₁, hab₁, hpr₁, hsm₁⟩ := exists_intermediate_abelian_model_factorization hle₁ P.A A₀ φ₀ H₀ hab₀ hpr₀ hsm₀
  obtain ⟨L₁, hL₁, hiso₁⟩ := hF₁ R₁ hle₁ hsub₁ A₁.left A₁.hom π₁ φ₁ Hπ₁.1 e₁ H₁.1.w
  have : IsNoetherianRing R₁ := Algebra.FiniteType.isNoetherianRing ℤ R₁
  obtain ⟨F₂, hF₂⟩ := AmpleSubring.relAmple_subring S R₁ P A₁ φ₁ L₁ hab₁ hpr₁ hL₁ H₁ hiso₁
  obtain ⟨F₃, hF₃⟩ := rigidified_sym_descend_to_subring S R₁ P A₁ φ₁ L₁ hab₁ hL₁ H₁ hiso₁
  obtain ⟨R₂, hle₂, hsub₂, hR₂⟩ := exists_finiteType_subring_adjoin S R₁ (F₂ ∪ F₃) hR₁
  rw [Finset.coe_union, Set.union_subset_iff] at hsub₂
  obtain ⟨A₂, _, φ₂, π₂, e₂, Hπ₂, H₂, hab₂, hpr₂, hsm₂⟩ := exists_intermediate_abelian_model_factorization hle₂ P.A A₁ φ₁ H₁ hab₁ hpr₁ hsm₁
  have ha₂ := hF₂ R₂ hle₂ hsub₂.1 A₂ π₂ Hπ₂
  have hrs₂ := hF₃ R₂ hle₂ hsub₂.2 A₂ π₂ Hπ₂
  have hL₂ := LB.isLB_pull hL₁ π₂
  have hiso₂ := lbIso_pull_pull_of_comp P.isLB hL₁ e₂ hiso₁
  have : IsNoetherianRing R₂ := Algebra.FiniteType.isNoetherianRing ℤ R₂
  obtain ⟨F₄, hF₄⟩ := exists_finset_kTriv_of_subring S R₂ P A₂ φ₂ (L₁.pull π₂) hab₂ hL₂ ha₂ H₂ hiso₂
  obtain ⟨R₃, hle₃, hsub₃, hR₃⟩ := exists_finiteType_subring_adjoin S R₂ F₄ hR₂
  obtain ⟨A₃, _, φ₃, π₃, e₃, Hπ₃, H₃, hab₃, hpr₃, hsm₃⟩ := exists_intermediate_abelian_model_factorization hle₃ P.A A₂ φ₂ H₂ hab₂ hpr₂ hsm₂
  have hk₃ := hF₄ R₃ hle₃ hsub₃ A₃ π₃ Hπ₃
  have hL₃ := LB.isLB_pull hL₂ π₃
  have hpol := pol_pull _ _ A₂ A₃ _ π₃ _ _ hL₂ hL₃ hab₂ Hπ₃ (PolBaseChange.lbIso_refl hL₃)
  have hiso₃ := lbIso_pull_pull_of_comp P.isLB hL₂ e₃ hiso₂
  refine ⟨R₃,
    { A := A₃
      isAb := hab₃
      g := P.g
      smoothDim := hsm₃
      L := (L₁.pull π₂).pull π₃
      isLB := hL₃
      rigid := PolBaseChange.rigidified_pull Hπ₃ hrs₂.1
      sym := PolBaseChange.sym_pull Hπ₃ hrs₂.2
      ample := hpol.2.1 ha₂
      ktriv := hk₃ }, φ₃, hR₃, rfl, H₃, hiso₃⟩

end GlobalTheory.KeyTf
