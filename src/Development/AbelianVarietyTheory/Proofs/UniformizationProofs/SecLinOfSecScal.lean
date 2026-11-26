module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsSecOfLocal
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.OneTmulNeZeroOfDomain
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsEqPowOfTorsionCompEqOne
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIsoAppTopOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecEqZeroAndHomEqOfThickenings
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueOfIsAdicComplete
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.RingKrullDimOfEtaleMvPolynomial
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProperAndGeometricallyConnectedOfIsNilpotent

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SecLinOfSecScal
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ExpansionTotal

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FieldBaseChange

theorem globalFns : GlobalFnsSt :=
  GlobalFunctions.globalFns_of forall_geometricallyIntegral_of_smooth_of_geometricallyConnected
    FlatFibreInjective.injective_baseChange exists_noetherian_model_of_smooth

variable {R : Type} [CommRing R] [IsDomain R] {F F' : Type} [Field F] [Algebra (FractionRing R) F]
  [Field F'] [Algebra (FractionRing R) F'] (θ : TF (R := R) F ⟶ TF (R := R) F') (D : DegPre R)

def toBK : DegPre.BF D F ⟶ DegPre.BF D F' := lift (fst _ _ ≫ θ) (snd _ _)

theorem toBK_fst : toBK θ D ≫ fst _ _ = fst _ _ ≫ θ := lift_fst _ _

theorem toBK_prB : toBK θ D ≫ DegPre.prB D F' = DegPre.prB D F := lift_snd _ _

theorem famφ_eq (α : D.X) (i : Fin 4) :
    DegPre.famφ D F α i = (toBK θ D).left ≫ DegPre.famφ D F' α i := by
  have e₀ := toBK_prB θ D
  have e₂ := comp_cP D (toBK θ D) α
  fin_cases i
  · exact congrArg (fun q => q.left) e₀.symm
  · exact congrArg (fun q => q.left) ((MonObj.comp_mul (toBK θ D) (DegPre.prB D _) (cP D _ α)).trans
      (congrArg₂ (· * ·) e₀ e₂)).symm
  · exact congrArg (fun q => q.left) e₂.symm
  · exact congrArg (fun q : DegPre.BF D F ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) (toBK θ D)).symm

theorem trF_toBK (mu : D.X) :
    DegPre.trF D F mu ≫ toBK θ D = toBK θ D ≫ DegPre.trF D F' mu := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, toBK_fst, Category.assoc, trF_eq, trF_eq, tr_fst, toBK_fst, ← Category.assoc, tr_fst]
  · refine (Category.assoc _ _ _).trans ((congrArg _ (toBK_prB θ D)).trans (Eq.trans ?_ (Category.assoc _ _ _).symm))
    rw [trF_eq, trF_eq, tr_pr]
    refine Eq.trans ?_ (congrArg (toBK θ D ≫ ·) (tr_pr D F' (cP D _ mu))).symm
    rw [MonObj.comp_mul, toBK_prB, comp_cP, comp_cP, comp_cP]

theorem exists_famPull (hθ : θ.left ≫ jFK (R := R) F' = jFK (R := R) F) (k : ℕ) (S : Fam D F' k) : ∃ S' : Fam D F k,
    ∀ (α : D.X) (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D F).left) (z : Z) (J), Good D.P.L z J →
      sval (S'.s α) r z J = sval (S.s α) (r ≫ (toBK θ D).left) z J := by
  have hp : (toBK θ D).left ≫ (DegPre.BF D F').hom =
      (DegPre.BF D F).hom ≫ Spec.map (CommRingCat.ofHom (RingHom.id R)) :=
    (Over.w _).trans ((Category.comp_id _).symm.trans (congrArg _ (Spec.map_id _).symm))
  let s : ∀ α : D.X, LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k)) := fun α =>
    pullOver D.P.L (DegPre.famε k) hp (famφ_eq θ D α) (S.s α)
  have hs : ∀ (α : D.X) (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D F).left) (z : Z) (J), Good D.P.L z J →
      sval (s α) r z J = sval (S.s α) (r ≫ (toBK θ D).left) z J := fun α Z r z J hJ =>
    sval_pullOver hp (famφ_eq θ D α) (S.s α) r hJ
  refine ⟨⟨s, fun mu α u hu hc => (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).2 fun y J hJ => ?_⟩, hs⟩
  have e₁ := (gen_fe globalFns k mu α).2 u hu hc _ (𝟙 _) y J hJ
  obtain ⟨⟨u', hu', hc'⟩, hv'⟩ := gen_fe (D := D) (F := F') globalFns k mu α
  have e₂ := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u').1 (S.fe mu α u' hu' hc') _ (toBK θ D).left y J hJ
  rw [hv' u' hu' hc' _ (toBK θ D) y J hJ, ← Over.comp_left, ← trF_toBK, Over.comp_left] at e₂
  rw [Over.id_left] at e₁
  rw [hs _ _ _ y J hJ, hs _ _ _ y J hJ, Category.id_comp, Category.id_comp, e₂, e₁]
  have a : (toBK θ D ≫ fst _ _).left ≫ jFK (R := R) F' =
      (𝟙 (DegPre.BF D F) ≫ fst _ _).left ≫ jFK (R := R) F := by
    rw [toBK_fst, Category.id_comp, Over.comp_left, Category.assoc, hθ]
  rw [val_famMult _ hJ, val_famMult _ hJ, a, uVal, uVal, toBK_prB, comp_cP, comp_cP, comp_cP, comp_cP,
    Category.id_comp (DegPre.prB D F)]




end GlobalTheory.ExpansionTotal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValuesNatural
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem gs_comp_stalkMap {Y Z Z' : Scheme.{0}} (r : Z ⟶ Y) (ρ : Z' ⟶ Z) (z : Z') (U : Y.Opens)
    (h : r (ρ z) ∈ U) (a : Γ(Y, U)) :
    gs (ρ ≫ r) z U a = (ρ.stalkMap z).hom (gs r (ρ z) U a) := by
  rw [← gs_pull ρ r z U h a, gs_eq r (ρ z) U h, gs_eq ρ z (r ⁻¹ᵁ U) h]
  exact (Scheme.Hom.germ_stalkMap_apply ρ (r ⁻¹ᵁ U) z h _).symm

theorem values_natural : ∀ (X Y Z Z' : Scheme.{0}) (L : LB X) (K : Type) [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (r : Z ⟶ Y) (ρ : Z' ⟶ Z) (z : Z') (J : (Z' ⟶ X) → L.ι), Good L z J → Good L (ρ z) (fun ψ : Z ⟶ X => J (ρ ≫ ψ)) ∧ (∀ s : LB.Sec (LB.LinComb L φ ε), sval s (ρ ≫ r) z J = (ρ.stalkMap z).hom (sval s r (ρ z) (fun ψ => J (ρ ≫ ψ)))) ∧ (∀ t : LB.Gen (LB.LinComb L φ ε), (val t (ρ ≫ r) z J).val = (ρ.stalkMap z).hom (val t r (ρ z) (fun ψ => J (ρ ≫ ψ))).val) ∧ ∀ c : Γ(Y, ⊤), gs (ρ ≫ r) z ⊤ c = (ρ.stalkMap z).hom (gs r (ρ z) ⊤ c) := by
  intro X Y Z Z' L K _ φ ε r ρ z J hJ
  have hJ' : Good L (ρ z) (fun ψ : Z ⟶ X => J (ρ ≫ ψ)) := fun ψ => hJ (ρ ≫ ψ)
  have hm := hJ'.mem φ r
  refine ⟨hJ', fun s => ?_, fun t => ?_, fun c => gs_comp_stalkMap r ρ z ⊤ trivial c⟩
  · rw [sval_of s (ρ ≫ r) z J (fun k => J (ρ ≫ r ≫ φ k)) (fun k => by rw [Category.assoc])]
    exact gs_comp_stalkMap r ρ z _ hm _
  · rw [val_of t (ρ ≫ r) z J (fun k => J (ρ ≫ r ≫ φ k)) (fun k => by rw [Category.assoc])]
    exact (gs_unit (ρ ≫ r) z _ hm _).symm.trans ((gs_comp_stalkMap r ρ z _ hm _).trans
      (congrArg (ρ.stalkMap z).hom (gs_unit r (ρ z) _ hm _)))

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.StalkMapInjectiveOfFlat
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftTest

theorem stalkMap_injective_of_flat {W Z : Scheme.{0}} (f : W ⟶ Z) [Flat f] (w : W) :
    Function.Injective (f.stalkMap w).hom := by
  have h := Flat.stalkMap f w
  algebraize [(f.stalkMap w).hom]
  have : IsLocalHom (algebraMap (Z.presheaf.stalk (f w)) (W.presheaf.stalk w)) := f.toLRSHom.prop w
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := Z.presheaf.stalk (f w)) (B := W.presheaf.stalk w)
  exact FaithfulSMul.algebraMap_injective (Z.presheaf.stalk (f w)) (W.presheaf.stalk w)

theorem gs_comp {W Z Y : Scheme.{0}} (f : W ⟶ Z) (r : Z ⟶ Y) (w : W) (U : Y.Opens) (h : r (f w) ∈ U)
    (a : Γ(Y, U)) : gs (f ≫ r) w U a = (f.stalkMap w).hom (gs r (f w) U a) := by
  rw [← gs_pull f r w U h, gs_eq f w (r ⁻¹ᵁ U) h, gs_eq r (f w) U h]
  exact (Scheme.Hom.germ_stalkMap_apply f (r ⁻¹ᵁ U) w h _).symm

theorem sval_eq_zero_of_flat {X Y Z W : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} (d : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (f : W ⟶ Z) [Flat f] (w : W)
    (h : ∀ J, Good L w J → sval d (f ≫ r) w J = 0) (J) (hJ : Good L (f w) J) : sval d r (f w) J = 0 := by
  choose I hI using fun χ : W ⟶ X => exists_chart hL (χ w)
  have hm : r (f w) ∈ LB.wchart L φ (fun k => J (r ≫ φ k)) := hJ.mem φ r
  have e := sec_trans d (f ≫ r) w (j := fun k => J (r ≫ φ k)) hm (Good.mem hI φ (f ≫ r))
  have e0 : gs (f ≫ r) w (LB.wchart L φ (fun k => I ((f ≫ r) ≫ φ k))) (d.f (fun k => I ((f ≫ r) ≫ φ k))) = 0 := h I hI
  rw [e0, mul_zero] at e
  exact (map_eq_zero_iff _ (stalkMap_injective_of_flat f w)).1 ((gs_comp f r w _ hm _).symm.trans e)

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (Y : Over (Spec (CommRingCat.of R))) (p : Y ⟶ D.P.A) (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (K : Type) [Fintype K] (φ : K → (Y.left ⟶ X)) (ε : K → ℤ) (d : LB.Sec (LB.LinComb L φ ε)), (∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (r : Z ⟶ Y.left), r ≫ p.left = x ≫ g.pG.left → ∀ (z : Z) (J), Good L z J → sval d r z J = 0) → ∀ (Z : Scheme.{0}) (r : Z ⟶ Y.left), (∃ ρ : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))), ρ ≫ thick R I e = r ≫ Y.hom) → ∀ (z : Z) (J), Good L z J → sval d r z J = 0 := by
  intro R _ _ I D e G _ _ g Y p X L hL K _ φ ε d H Z r ⟨ρ, hρ⟩ z J hJ
  have := g.q_flat
  have := g.q_surj
  let b : Z ⟶ (thickObj R I e D.P.A).left :=
    pullback.lift (r ≫ p.left) ρ (by rw [Category.assoc, Over.w p, hρ])
  have hb : b ≫ pullback.fst D.P.A.hom (thick R I e) = r ≫ p.left := pullback.lift_fst _ _ _
  obtain ⟨w, rfl⟩ := (pullback.fst b g.q.left).surjective z
  refine sval_eq_zero_of_flat hL d r (pullback.fst b g.q.left) w (fun J' hJ' => ?_) J hJ
  refine H _ (pullback.snd b g.q.left) _ ?_ w J' hJ'
  rw [Category.assoc, ← hb, pullback.condition_assoc]
  rfl

end GlobalTheory.LiftTest
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SecEqZeroOfThickeningsOfSection
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory


open ThickeningDetermines in
theorem sec_eq_zero_of_thickenings_of_section (R : Type) [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (hI : I ≤ Ideal.jacobson ⊥) (H : Over (Spec (CommRingCat.of R)))
    [Smooth H.hom] [GeometricallyConnected H.hom] (e : 𝟙_ _ ⟶ H) (N : LB H.left) (hN : N.IsLB)
    (s : LB.Sec N) (hs : ∀ (n : ℕ) j, ((fstG I n H).left.app _).hom (s.f j) = 0) (j) :
    s.f j = 0 := by
  have := geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres H.hom
  have key := isIso_of_isClosedImmersion_of_thickenings R I hI H e (fun p ↦ inferInstance)
  refine eq_zero_of_secIdeal_eq_bot hN s ?_ j
  have := key _ (secIdeal hN s).subschemeι fun n ↦ by
    have : IsClosedImmersion (thick R I n) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    have : QuasiCompact (fstG I n H).left :=
      inferInstanceAs (QuasiCompact (pullback.fst H.hom (thick R I n)))
    exact ⟨IsClosedImmersion.lift _ (fstG I n H).left (by
      rw [Scheme.IdealSheafData.ker_subschemeι]
      exact secIdeal_le_ker hN s _ (hs n)), IsClosedImmersion.lift_fac _ _ _⟩
  rw [← Scheme.IdealSheafData.ker_subschemeι (secIdeal hN s)]
  exact IsClosedImmersion.isIso_iff_ker_eq_bot.1 this

theorem app_sec_eq_zero_of_sval {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type}
    [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} (d : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y)
    (h : ∀ (z : Z) (J), Good L z J → sval d r z J = 0) (j) : (r.app _).hom (d.f j) = 0 := by
  apply TopCat.Presheaf.section_ext Z.sheaf _
  intro z hz
  choose I hI using fun χ : Z ⟶ X => exists_chart hL (χ z)
  have e := sec_trans d r z (j := j) hz (Good.mem hI φ r)
  have e' : gs r z (LB.wchart L φ j) (d.f j) = 0 :=
    e.trans ((congrArg _ (h z I hI)).trans (mul_zero _))
  exact ((gs_eq r z _ hz _).symm.trans e').trans (map_zero _).symm

theorem sec_eq_zero_of_sval_finite_level : ∀ (R : Type) [CommRing R] (I : Ideal R) (T B : Over (Spec (CommRingCat.of R))) [IsAffine T.left] [IsNoetherianRing Γ(T.left, ⊤)] [GrpObj B] [Smooth B.hom] [GeometricallyConnected B.hom], (∀ r ∈ I, scal T.hom r ∈ Ideal.jacobson (⊥ : Ideal Γ(T.left, ⊤))) → ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (K : Type) [Fintype K] (φ : K → ((T ⊗ B).left ⟶ X)) (ε : K → ℤ) (d : LB.Sec (LB.LinComb L φ ε)), (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ B).left), (∃ ρ : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))), ρ ≫ thick R I e = r ≫ (T ⊗ B).hom) → ∀ (z : Z) (J), Good L z J → sval d r z J = 0) → ∀ j, d.f j = 0 := by
  intro R _ I T B _ _ _ _ _ hI X L hL K _ φ ε d hd j
  let ψ : CommRingCat.of R ⟶ Γ(T.left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ T.hom.appTop
  have hψ : T.left.isoSpec.hom ≫ Spec.map ψ = T.hom := by
    rw [Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc,
      Scheme.isoSpec_Spec_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]
  let H : Over (Spec (CommRingCat.of Γ(T.left, ⊤))) :=
    Over.mk (pullback.fst T.hom B.hom ≫ T.left.isoSpec.hom)
  have : Smooth H.hom := inferInstanceAs (Smooth (pullback.fst T.hom B.hom ≫ T.left.isoSpec.hom))
  have : GeometricallyConnected H.hom :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected)
      (IsPullback.of_iso (IsPullback.of_hasPullback T.hom B.hom).flip (Iso.refl _) (Iso.refl _)
        T.left.isoSpec (Iso.refl _) (fst' := pullback.snd T.hom B.hom) (snd' := H.hom)
        (f' := B.hom) (g' := Spec.map ψ) (by simp) (Category.id_comp _).symm (by simp)
        (by simp [hψ])) ‹GeometricallyConnected B.hom›
  let σ : T ⟶ T ⊗ B := lift (𝟙 T) (toUnit T ≫ η[B])
  have hσ : σ.left ≫ pullback.fst T.hom B.hom = 𝟙 _ :=
    congrArg CommaMorphism.left (lift_fst (𝟙 T) (toUnit T ≫ η[B]))
  let e : 𝟙_ _ ⟶ H := Over.homMk (T.left.isoSpec.inv ≫ σ.left) (by
    change (T.left.isoSpec.inv ≫ σ.left) ≫ pullback.fst T.hom B.hom ≫ T.left.isoSpec.hom = 𝟙 _
    rw [Category.assoc, reassoc_of% hσ, Iso.inv_hom_id])
  refine sec_eq_zero_of_thickenings_of_section Γ(T.left, ⊤) (I.map ψ.hom)
    (Ideal.map_le_iff_le_comap.2 hI) H e (LB.LinComb L φ ε) (DVR.linComb_isLB L hL φ ε) d
    (fun n j ↦ app_sec_eq_zero_of_sval hL d _ (hd n _ _ ⟨pullback.snd H.hom (thick _ (I.map ψ.hom) n) ≫
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap ((I.map ψ.hom) ^ (n + 1)) ψ.hom
          (by rw [← Ideal.map_pow]; exact Ideal.le_comap_map))), ?_⟩) j) j
  change _ = pullback.fst H.hom (thick _ (I.map ψ.hom) n) ≫ pullback.fst T.hom B.hom ≫ T.hom
  have h1 : pullback.fst T.hom B.hom ≫ T.hom = H.hom ≫ Spec.map ψ :=
    (congrArg (pullback.fst T.hom B.hom ≫ ·) hψ.symm).trans (Category.assoc _ _ _).symm
  rw [h1, pullback.condition_assoc, Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsBasisOfFormEq
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PowBasis

theorem gs_sum {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) {m : ℕ} (a : Fin m → Γ(X, U)) :
    gs f y U (∑ i, a i) = ∑ i, gs f y U (a i) := by simp only [gs_eq f y U h, map_sum]

theorem comb_iff {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {m : ℕ} (s : LB.Sec (LB.LinComb L φ ε)) (b : Fin m → LB.Sec (LB.LinComb L φ ε)) (r : Fin m → Γ(Y, ⊤)) :
    (∀ j, s.f j = ∑ i, (Y.presheaf.map (homOfLE le_top).op).hom (r i) * (b i).f j) ↔
      ∀ y J, Good L y J → sval s (𝟙 Y) y J = ∑ i, gs (𝟙 Y) y ⊤ (r i) * sval (b i) (𝟙 Y) y J := by
  have key : ∀ (j : K → L.ι) (y : Y) (hy : y ∈ LB.wchart L φ j),
      gs (𝟙 Y) y (LB.wchart L φ j)
        (∑ i, (Y.presheaf.map (homOfLE (le_top : (LB.LinComb L φ ε).U j ≤ ⊤)).op).hom (r i) * (b i).f j :
          Γ(Y, (LB.LinComb L φ ε).U j)) =
      ∑ i, gs (𝟙 Y) y ⊤ (r i) * gs (𝟙 Y) y (LB.wchart L φ j) ((b i).f j) := fun j y hy =>
    (gs_sum (𝟙 Y) y _ hy _).trans (Finset.sum_congr rfl fun i _ =>
      (gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg (· * _) (gs_res (𝟙 Y) y le_top hy _)))
  constructor
  · intro h y J hJ
    exact (congrArg (gs (𝟙 Y) y _) (h _)).trans (key _ y (hJ.mem φ (𝟙 Y)))
  · intro h j
    refine fn_ext fun y hy => ?_
    choose I hI using fun χ : Y ⟶ X => exists_chart hL (χ y)
    refine ((sec_trans s (𝟙 Y) y hy (Good.mem hI φ (𝟙 Y))).trans ((congrArg _ (h y I hI)).trans ?_)).trans
      (key j y hy).symm
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sec_trans (b i) (𝟙 Y) y hy (Good.mem hI φ (𝟙 Y)), mul_left_comm]
    rfl

theorem exists_basis_of_formEq {S : Scheme.{0}} {A T : Over S} {X : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    {K K' : Type} [Fintype K] [Fintype K'] {φ : K → ((T ⊗ A).left ⟶ X)} {ε : K → ℤ}
    {φ' : K' → ((T ⊗ A).left ⟶ X)} {ε' : K' → ℤ} (h : FormEq φ ε φ' ε') {m : ℕ}
    {b : Fin m → LB.Sec (LB.LinComb L φ ε)} (hb : IsSecBasis _ b) :
    ∃ b' : Fin m → LB.Sec (LB.LinComb L φ' ε'), IsSecBasis _ b' := by
  choose b' hb' using fun i => exists_sec hL h (b i)
  refine ⟨b', fun t => ?_⟩
  obtain ⟨s, hs⟩ := exists_sec hL (φ := φ') (ε := ε') (φ' := φ) (ε' := ε) (fun U _ g => (h U g).symm) t
  refine (existsUnique_congr fun r => ?_).1 (hb s)
  refine (comb_iff hL s b fun i => (fst T A).left.appTop.hom (r i)).trans
    (Iff.trans ?_ (comb_iff hL t b' fun i => (fst T A).left.appTop.hom (r i)).symm)
  refine forall_congr' fun y => forall_congr' fun J => forall_congr' fun hJ => ?_
  rw [hs _ _ y J hJ]
  simp only [hb' _ _ _ y J hJ]

theorem translPt_one {S : Scheme.{0}} (A : Over S) [GrpObj A] (T : Over S) :
    translPt A (1 : T ⟶ A) = snd T A := by
  have e : translPt A (1 : T ⟶ A) = (fst T A ≫ (1 : T ⟶ A)) * snd T A := rfl
  rw [e, MonObj.comp_one, _root_.one_mul]

theorem exists_basis_pow (hT : SecTwistSt) {S : Scheme.{0}} (P : PolAV S) (k : ℕ) (hk : 1 ≤ k) (R : Type) [CommRing R]
    [IsLocalRing R] (t : Spec (CommRingCat.of R) ⟶ S) :
    ∃ b : Fin (k ^ P.g) → LB.Sec (LPow P.A P.L (k : ℤ) (Over.mk t)), IsSecBasis _ b := by
  obtain ⟨⟨b, hb⟩, -⟩ := hT S P k hk R t 1
  refine exists_basis_of_formEq P.isLB (fun U _ g => ?_) hb
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, translPt_one, Fintype.prod_unique]
  rw [← zpow_add, sub_add_cancel]

theorem exists_basis_pow_field : SecTwistSt → ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → ∃ b : Fin (k ^ A.g) → LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F)), ∀ t : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F)), ∃! c : Fin (k ^ A.g) → F, ∀ j, t.f j = ∑ i, liftFun A.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c i)) * (b i).f j := by
  intro hT R _ _ A F _ _ k hk
  obtain ⟨b, hb⟩ := exists_basis_pow hT A k hk F (jFK (R := R) F)
  refine ⟨b, fun t => ?_⟩
  obtain ⟨r, hr, hu⟩ := hb t
  refine ⟨fun i => (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom (r i), fun j => ?_, fun c hc => ?_⟩
  · refine (hr j).trans (Finset.sum_congr rfl fun i _ => ?_)
    exact congrArg (fun x => liftFun A.A _ x * (b i).f j)
      ((Scheme.ΓSpecIso (CommRingCat.of F)).hom_inv_id_apply (r i)).symm
  · have e := hu (fun i => (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c i)) hc
    funext i
    rw [← congrFun e i]
    exact ((Scheme.ΓSpecIso (CommRingCat.of F)).inv_hom_id_apply (c i)).symm

end GlobalTheory.PowBasis
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIntermediateFieldOfPowEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFiniteSeparablePoint
open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.FiniteSeparablePoints

theorem exists_factor_of_unramified {k Ω S : Type} [Field k] [Field Ω] [Algebra k Ω] [CommRing S]
    [Algebra k S] [Algebra.FormallyUnramified k S] [Algebra.FiniteType k S] (φ : S →ₐ[k] Ω) :
    ∃ K : IntermediateField k Ω, FiniteDimensional k K ∧ Algebra.IsSeparable k K ∧
      ∃ ψ : S →+* K, (algebraMap K Ω).comp ψ = φ.toRingHom := by
  classical
  let R : Subalgebra k Ω := φ.range
  have hsurj : Function.Surjective φ.rangeRestrict := φ.rangeRestrict_surjective
  have : Algebra.FiniteType k R := Algebra.FiniteType.of_surjective φ.rangeRestrict hsurj
  have : Algebra.FormallyUnramified k R := Algebra.FormallyUnramified.of_surjective φ.rangeRestrict hsurj
  have : Module.Finite k R := Algebra.FormallyUnramified.finite_of_free k R
  have hF : IsField R := isField_of_isIntegral_of_isField' (R := k) (Field.toIsField k)
  let K : IntermediateField k Ω := R.toIntermediateField' hF
  have hmem : ∀ x, φ x ∈ K.toSubalgebra := fun x => ⟨x, rfl⟩
  let ψ : S →ₐ[k] K := φ.codRestrict K.toSubalgebra hmem
  have hψ : Function.Surjective ψ := by
    rintro ⟨y, x, rfl⟩
    exact ⟨x, rfl⟩
  have : Algebra.FiniteType k K := Algebra.FiniteType.of_surjective ψ hψ
  have : Algebra.FormallyUnramified k K := Algebra.FormallyUnramified.of_surjective ψ hψ
  have : Module.Finite k K := Algebra.FormallyUnramified.finite_of_free k K
  refine ⟨K, inferInstance, (Algebra.FormallyUnramified.iff_isSeparable k K).1 inferInstance,
    ψ.toRingHom, ?_⟩
  ext x
  rfl

theorem exists_finite_separable_point {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    {X : Scheme} (p : X ⟶ Spec (CommRingCat.of k)) [FormallyUnramified p]
    [LocallyOfFiniteType p] (a : Spec (CommRingCat.of Ω) ⟶ X)
    (h : a ≫ p = Spec.map (CommRingCat.ofHom (algebraMap k Ω))) :
    ∃ K : IntermediateField k Ω, FiniteDimensional k K ∧ Algebra.IsSeparable k K ∧
      ∃ b : Spec (CommRingCat.of K) ⟶ X,
        Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫ b = a := by
  classical
  obtain ⟨pt⟩ : Nonempty (Spec (CommRingCat.of Ω)) := inferInstance
  obtain ⟨_, ⟨U, hU0, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (a pt)) isOpen_univ
  have hU : IsAffineOpen U := hU0
  have hrange : Set.range a ⊆ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    rintro _ ⟨y, rfl⟩
    rwa [Subsingleton.elim y pt]
  have hca : IsOpenImmersion.lift hU.fromSpec a hrange ≫ hU.fromSpec = a :=
    IsOpenImmersion.lift_fac _ _ _
  obtain ⟨f, hf⟩ : ∃ f, Spec.map f = IsOpenImmersion.lift hU.fromSpec a hrange :=
    ⟨_, Spec.map_preimage _⟩
  obtain ⟨g, hg⟩ : ∃ g, Spec.map g = hU.fromSpec ≫ p := ⟨_, Spec.map_preimage _⟩
  have hgf : g ≫ f = CommRingCat.ofHom (algebraMap k Ω) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hf, hg, ← Category.assoc, hca, h]
  have hU1 : RingHom.FormallyUnramified g.hom := by
    rw [← HasRingHomProperty.Spec_iff (P := @FormallyUnramified), hg]
    exact HasRingHomProperty.comp_of_isOpenImmersion @FormallyUnramified hU.fromSpec p ‹_›
  have hU2 : RingHom.FiniteType g.hom := by
    rw [← HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), hg]
    infer_instance
  let _ : Algebra k Γ(X, U) := g.hom.toAlgebra
  have : Algebra.FormallyUnramified k Γ(X, U) := hU1
  have : Algebra.FiniteType k Γ(X, U) := hU2
  let φ' : Γ(X, U) →ₐ[k] Ω :=
    { f.hom with
      commutes' := fun r => by
        have e := congrArg (fun q => q.hom r) hgf
        simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
        exact e }
  obtain ⟨K, hK1, hK2, ψ, hψ⟩ := exists_factor_of_unramified φ'
  refine ⟨K, hK1, hK2, Spec.map (CommRingCat.ofHom ψ) ≫ hU.fromSpec, ?_⟩
  have e : CommRingCat.ofHom ψ ≫ CommRingCat.ofHom (algebraMap K Ω) = f := by
    ext x
    exact congrArg (fun q => q x) hψ
  rw [← Category.assoc, ← Spec.map_comp, e, hf, hca]

end GlobalTheory.FiniteSeparablePoints
end

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionSeparable

theorem exists_intermediateField {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of k)) [FormallyUnramified p] [LocallyOfFiniteType p]
    (a : Spec (CommRingCat.of Ω) ⟶ X)
    (ha : a ≫ p = Spec.map (CommRingCat.ofHom (algebraMap k Ω))) :
    ∃ K : IntermediateField k Ω, FiniteDimensional k K ∧ Algebra.IsSeparable k K ∧
      ∃ b : Spec (CommRingCat.of K) ⟶ X,
        Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫ b = a := by
  first
  | (rename_i h_2 h_3 h_4 h_7 h_8; revert k Ω h_2 h_3 h_4 X p h_7 h_8 a ha; exact @_root_.GlobalTheory.FiniteSeparablePoints.exists_finite_separable_point)
  | exact @_root_.GlobalTheory.FiniteSeparablePoints.exists_finite_separable_point
  | exact _root_.GlobalTheory.FiniteSeparablePoints.exists_finite_separable_point
  | (apply _root_.GlobalTheory.FiniteSeparablePoints.exists_finite_separable_point <;> assumption)
  | (intros; apply _root_.GlobalTheory.FiniteSeparablePoints.exists_finite_separable_point <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FiniteSeparablePoints.exists_finite_separable_point <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FiniteSeparablePoints.exists_finite_separable_point ..)

theorem exists_intermediateField_of_pow_eq_one {V : Type} [CommRing V]
    (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] [LocallyOfFiniteType G.hom]
    {N : ℕ} (hN : IsUnit (N : V)) {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (r : V →+* k)
    (f : V →+* Ω) (hf : (algebraMap k Ω).comp r = f)
    (x : Over.mk (Spec.map (CommRingCat.ofHom f)) ⟶ G) (hx : x ^ N = 1) :
    ∃ K : IntermediateField k Ω, FiniteDimensional k K ∧ Algebra.IsSeparable k K ∧
      ∃ b : Spec (CommRingCat.of K) ⟶ G.left,
        Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫ b = x.left := by
  have hN' : IsUnit (N : Γ(Spec (CommRingCat.of V), ⊤)) := by
    simpa using hN.map (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom
  have h₁ := formallyUnramified_mulN _ G N hN'
  have h₂ : LocallyOfFiniteType (mulN G N).left := by
    have : LocallyOfFiniteType ((mulN G N).left ≫ G.hom) := by rw [Over.w]; infer_instance
    exact locallyOfFiniteType_of_comp _ G.hom
  let T : Over (Spec (CommRingCat.of V)) := Over.mk (Spec.map (CommRingCat.ofHom r))
  let e : Spec (CommRingCat.of k) ⟶ G.left := (1 : T ⟶ G).left
  let j : Over.mk (Spec.map (CommRingCat.ofHom f)) ⟶ T :=
    Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) (by
      subst hf
      exact (Spec.map_comp _ _).symm)
  have hw : x.left ≫ (mulN G N).left = Spec.map (CommRingCat.ofHom (algebraMap k Ω)) ≫ e := by
    change (x ≫ mulN G N).left = (j ≫ (1 : T ⟶ G)).left
    rw [MulUnramified.comp_mulN, hx, comp_one]
  have : FormallyUnramified (pullback.snd (mulN G N).left e) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @FormallyUnramified)
      (IsPullback.of_hasPullback _ _) h₁
  obtain ⟨K, hK, hK', b, hb⟩ := exists_intermediateField (pullback.snd (mulN G N).left e)
    (pullback.lift x.left _ hw) (pullback.lift_snd _ _ _)
  exact ⟨K, hK, hK', b ≫ pullback.fst _ _, by rw [reassoc_of% hb, pullback.lift_fst]⟩

theorem epi_specMap {K L : Type} [Field K] [Field L] (σ : K →+* L) :
    Epi (Spec.map (CommRingCat.ofHom σ)) := by
  have : Flat (Spec.map (CommRingCat.ofHom σ)) := inferInstance
  have : Surjective (Spec.map (CommRingCat.ofHom σ)) :=
    ⟨fun u => ⟨IsLocalRing.closedPoint L, Subsingleton.elim _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

end GlobalTheory.TorsionSeparable

namespace GlobalTheory

open TorsionSeparable IsLocalRing

theorem exists_finite_extension_torsion_lift : UnramExtSt → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (N : ℕ), IsUnit (N : V) → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (f : V →+* Ω), IsLocalHom f → ∀ s : Finset (Over.mk (Spec.map (CommRingCat.ofHom f)) ⟶ G), (∀ x ∈ s, x ^ N = 1) → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : IsAdicComplete (IsLocalRing.maximalIdeal W) W) (_ : Algebra V W) (f' : W →+* Ω), Module.Finite V W ∧ Function.Injective (algebraMap V W) ∧ IsLocalHom (algebraMap V W) ∧ IsLocalHom f' ∧ f'.comp (algebraMap V W) = f ∧ ∀ x ∈ s, ∃ y : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G, y ^ N = 1 ∧ Spec.map (CommRingCat.ofHom f') ≫ y.left = x.left := by
  intro hU V _ _ _ _ G _ _ _ N hN Ω _ _ f hf s hs
  let : Algebra (ResidueField V) Ω := (ResidueField.lift f).toAlgebra
  have hr : (algebraMap (ResidueField V) Ω).comp (residue V) = f := ResidueField.lift_comp_residue f
  choose K hK hK' b hb using fun x : s =>
    exists_intermediateField_of_pow_eq_one G hN (residue V) f hr x.1 (hs x.1 x.2)
  let L : IntermediateField (ResidueField V) Ω := ⨆ x, K x
  have : FiniteDimensional (ResidueField V) L := inferInstance
  have : Algebra.IsSeparable (ResidueField V) L := inferInstance
  obtain ⟨W, _, _, _, _, _, hfin, hinj, hloc, -, e, he⟩ := hU V L
  let σ : ResidueField W →+* Ω := (algebraMap L Ω).comp e.toRingHom
  have hcomp : (σ.comp (residue W)).comp (algebraMap V W) = f := by
    ext v
    change algebraMap L Ω (e (residue W (algebraMap V W v))) = f v
    rw [he, ← IsScalarTower.algebraMap_apply, ← hr]
    rfl
  have hσ : IsLocalHom (σ.comp (residue W)) := ⟨fun a ha => by
    by_contra hn
    exact ha.ne_zero (by rw [RingHom.comp_apply, (residue_eq_zero_iff a).2 hn, map_zero])⟩
  refine ⟨W, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    σ.comp (residue W), hfin, hinj, hloc, hσ, hcomp, fun x hx => ?_⟩
  have := epi_specMap σ
  let c : Spec (CommRingCat.of (ResidueField W)) ⟶ G.left :=
    Spec.map (CommRingCat.ofHom (e.symm.toRingHom.comp
      (IntermediateField.inclusion (le_iSup K ⟨x, hx⟩)).toRingHom)) ≫ b ⟨x, hx⟩
  have hc : Spec.map (CommRingCat.ofHom σ) ≫ c = x.left := by
    rw [← hb ⟨x, hx⟩, ← Spec.map_comp_assoc]
    congr 2
    ext t
    simp [σ]
  have hp : Spec.map (CommRingCat.ofHom σ) ≫ Spec.map (CommRingCat.ofHom (residue W)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap V W)) = Spec.map (CommRingCat.ofHom f) := by
    rw [← hcomp, ← Spec.map_comp, ← Spec.map_comp]
    rfl
  let T : Over (Spec (CommRingCat.of V)) := Over.mk (Spec.map (CommRingCat.ofHom (residue W)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap V W)))
  let x₀ : T ⟶ G := Over.homMk c (by
    rw [← cancel_epi (Spec.map (CommRingCat.ofHom σ))]
    exact ((reassoc_of% hc) _).trans ((Over.w x).trans hp.symm))
  let j : Over.mk (Spec.map (CommRingCat.ofHom f)) ⟶ T :=
    Over.homMk (Spec.map (CommRingCat.ofHom σ)) hp
  have hj : j ≫ x₀ = x := Over.OverMorphism.ext hc
  have : Epi j.left := epi_specMap σ
  have : Epi j := Over.epi_of_epi_left j
  have hx₀ : x₀ ^ N = 1 := by
    rw [← cancel_epi j, comp_pow, hj, hs x hx, comp_one]
  obtain ⟨y, ⟨hy, hy'⟩, -⟩ := existsUnique_torsion_lift W _ G
    (Spec.map (CommRingCat.ofHom (algebraMap V W))) N
    (by simpa using hN.map (algebraMap V W)) x₀ hx₀
  refine ⟨y, hy, ?_⟩
  rw [← hc, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hy']
  rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AppWhiskerRightInjectiveOfFlat
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem app_whiskerRight_injective_of_flat :
    ∀ (S : Scheme.{0}) (B T T' : Over S) [Flat B.hom] [IsAffine T.left] [IsAffine T'.left] (φ : T' ⟶ T), Function.Injective φ.left.appTop.hom → ∀ U : (T ⊗ B).left.Opens, Function.Injective ((φ ▷ B).left.app U).hom := by
  intro S B T T' _ _ _ φ hφ U
  have hd : IsSchemeTheoreticallyDominant φ.left := by
    refine ⟨Scheme.IdealSheafData.ext_of_isAffine ?_⟩
    rw [Scheme.Hom.ker_apply]
    simp only [Scheme.IdealSheafData.ideal_bot, Pi.bot_apply]
    rw [← RingHom.injective_iff_ker_eq_bot]
    exact hφ
  have pb : IsPullback (pullback.fst T'.hom B.hom) (φ ▷ B).left φ.left (pullback.fst T.hom B.hom) := by
    refine (IsPullback.of_right (h₁₁ := (φ ▷ B).left) (v₁₁ := pullback.fst T'.hom B.hom)
      (h₂₁ := φ.left) (v₁₂ := pullback.fst T.hom B.hom) ?_ (Over.whiskerRight_left_fst φ)
      (IsPullback.of_hasPullback T.hom B.hom).flip).flip
    rw [Over.whiskerRight_left_snd, Over.w]
    exact (IsPullback.of_hasPullback T'.hom B.hom).flip
  have : IsSchemeTheoreticallyDominant (φ ▷ B).left := .of_isPullback pb
  have : QuasiCompact (φ ▷ B).left := MorphismProperty.of_isPullback pb inferInstance
  exact (φ ▷ B).left.app_injective U

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecRelationDefect
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_sec_smul_sub_smul {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s t : LB.Sec (LB.LinComb L φ ε)) (c' c : Γ(Y, ⊤)) : ∃ d : LB.Sec (LB.LinComb L φ ε),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
        sval d r z J = gs r z ⊤ c' * sval s r z J - gs r z ⊤ c * sval t r z J := by
  have gsub : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (U : Y.Opens) (_ : r z ∈ U) (a b : Γ(Y, U)),
      gs r z U (a - b) = gs r z U a - gs r z U b := fun Z r z U h a b => by
    simp only [gs_eq r z U h, map_sub]
  have v : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : K → L.ι), r z ∈ LB.wchart L φ j →
      gs r z (LB.wchart L φ j)
        ((Y.presheaf.map (homOfLE (le_top : LB.wchart L φ j ≤ ⊤)).op).hom c' * (show Γ(Y, LB.wchart L φ j) from s.f j) -
          (Y.presheaf.map (homOfLE (le_top : LB.wchart L φ j ≤ ⊤)).op).hom c * (show Γ(Y, LB.wchart L φ j) from t.f j)) =
      gs r z ⊤ c' * gs r z (LB.wchart L φ j) (s.f j) - gs r z ⊤ c * gs r z (LB.wchart L φ j) (t.f j) :=
    fun Z r z j hj => (gsub Z r z _ hj _ _).trans (congrArg₂ (· - ·)
      ((gs_mul r z _ hj _ _).trans (congrArg (· * _) (gs_res r z _ hj _)))
      ((gs_mul r z _ hj _ _).trans (congrArg (· * _) (gs_res r z _ hj _))))
  refine ⟨⟨fun j => (Y.presheaf.map (homOfLE (le_top : LB.wchart L φ j ≤ ⊤)).op).hom c' * (show Γ(Y, LB.wchart L φ j) from s.f j) -
          (Y.presheaf.map (homOfLE (le_top : LB.wchart L φ j ≤ ⊤)).op).hom c * (show Γ(Y, LB.wchart L φ j) from t.f j),
      fun (j j' : K → L.ι) => fn_ext fun y hy => ?_⟩, fun Z r z J hJ => v Z r z _ (hJ.mem φ r)⟩
  refine ((gs_res (𝟙 Y) y _ hy _).trans (v _ _ y j hy.1)).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans
    (congrArg₂ (· * ·) ((gs_unit (𝟙 Y) y _ hy _).trans
      (congrArg Units.val (gm_linComb L _ _ (𝟙 Y) y j j' hy.1 hy.2)))
      ((gs_res (𝟙 Y) y _ hy _).trans (v _ _ y j' hy.2)))).symm)
  rw [sec_trans s (𝟙 Y) y hy.1 hy.2, sec_trans t (𝟙 Y) y hy.1 hy.2]
  simp only [trF]
  ring

theorem exists_sec_relation_defect : ∀ (Y : Scheme.{0}) (X Y₂ : Scheme.{0}) (L : LB X), L.IsLB → ∀ (K K' K'' : Type) [Fintype K] [Fintype K'] [Fintype K''] (φ : K → (Y₂ ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) (φu : K'' → (Y ⟶ X)) (εu : K'' → ℤ) (τ : Y ⟶ Y₂) (s : LB.Sec (LB.LinComb L φ ε)) (s' : LB.Sec (LB.LinComb L φ' ε')) (u : LB.Gen (LB.LinComb L φu εu)) (c c' : Γ(Y, ⊤)), u.IsGen → FormEq φ' ε' (Sum.elim (fun k => τ ≫ φ k) φu) (Sum.elim ε εu) → ∃ d : LB.Sec (LB.LinComb L φ' ε'), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J → sval d r z J = gs r z ⊤ c' * sval s' r z J - gs r z ⊤ c * (sval s (r ≫ τ) z J * (val u r z J).val) := by
  intro Y X Y₂ L hL K K' K'' _ _ _ φ ε φ' ε' φu εu τ s s' u c c' hu hF
  obtain ⟨t, ht⟩ := exists_sec hL (fun U _ h => (hF U h).symm : FormEq _ _ φ' ε') (pullMulSec s τ u hu)
  obtain ⟨d, hd⟩ := exists_sec_smul_sub_smul s' t c' c
  exact ⟨d, fun Z r z J hJ => by rw [hd Z r z J hJ, ht Z r z J hJ, sval_pullMulSec s τ u hu r z hJ]⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNeZeroIffSvalGenericPointNeZero
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem gs_id_eq_zero_iff {Y : Scheme.{0}} [IsIntegral Y] (y : Y) (U : Y.Opens) (hy : y ∈ U) (a : Γ(Y, U)) :
    gs (𝟙 Y) y U a = 0 ↔ a = 0 := by
  have e : gs (𝟙 Y) y U a = (Y.presheaf.germ U y hy).hom a := gs_eq (𝟙 Y) y U hy a
  rw [e]
  exact map_eq_zero_iff _ (germ_injective_of_isIntegral Y y hy)

theorem exists_ne_zero_iff_sval_ne_zero {Y X : Scheme.{0}} [IsIntegral Y] {L : LB X} {K : Type} [Fintype K]
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) {y : Y} {J : (Y ⟶ X) → L.ι} (hJ : Good L y J) :
    (∃ j, s.f j ≠ 0) ↔ sval s (𝟙 Y) y J ≠ 0 := by
  have hm : y ∈ LB.wchart L φ (fun k => J (𝟙 Y ≫ φ k)) := hJ.mem φ (𝟙 Y)
  constructor
  · rintro ⟨j, hj⟩ h0
    apply hj
    have h1 : s.f (fun k => J (𝟙 Y ≫ φ k)) = 0 := (gs_id_eq_zero_iff y _ hm _).1 h0
    refine fn_ext (V := LB.wchart L φ j) fun x hx => ?_
    have hne : (LB.wchart L φ j : Set Y).Nonempty := ⟨x, hx⟩
    obtain ⟨w, hw, hw'⟩ := nonempty_preirreducible_inter (LB.wchart L φ j).isOpen
      (LB.wchart L φ (fun k => J (𝟙 Y ≫ φ k))).isOpen hne ⟨y, hm⟩
    have h2 := sec_trans s (𝟙 Y) w hw hw'
    have h3 : gs (𝟙 Y) w (LB.wchart L φ (fun k => J (𝟙 Y ≫ φ k))) (s.f (fun k => J (𝟙 Y ≫ φ k))) = 0 :=
      (gs_id_eq_zero_iff w _ hw' _).2 h1
    rw [h3, mul_zero] at h2
    exact congrArg (gs (𝟙 Y) x (LB.wchart L φ j)) ((gs_id_eq_zero_iff w _ hw _).1 h2)
  · intro h
    exact ⟨fun k => J (𝟙 Y ≫ φ k), fun h0 => h ((gs_id_eq_zero_iff y _ hm _).2 h0)⟩

theorem exists_ne_zero_of_sval_eq_mul_unit : ∀ (Y X : Scheme.{0}) [IsIntegral Y] (L : LB X), L.IsLB → ∀ (K K' K'' : Type) [Fintype K] [Fintype K'] [Fintype K''] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) (φ'' : K'' → (Y ⟶ X)) (ε'' : K'' → ℤ) (s : LB.Sec (LB.LinComb L φ ε)) (s' : LB.Sec (LB.LinComb L φ' ε')) (d : LB.Sec (LB.LinComb L φ'' ε'')), (∀ (y : Y) (J), Good L y J → ∃ v : (Y.presheaf.stalk y)ˣ, sval d (𝟙 Y) y J = sval s (𝟙 Y) y J * sval s' (𝟙 Y) y J * v.val) → (∃ j, s.f j ≠ 0) → (∃ j, s'.f j ≠ 0) → ∃ j, d.f j ≠ 0 := by
  intro Y X _ L hL K K' K'' _ _ _ φ ε φ' ε' φ'' ε'' s s' d h hs hs'
  choose J hJ using fun χ : Y ⟶ X => exists_chart hL (χ (genericPoint Y))
  have hG : Good L (genericPoint Y) J := hJ
  obtain ⟨v, hv⟩ := h _ J hG
  rw [exists_ne_zero_iff_sval_ne_zero _ hG] at hs hs' ⊢
  rw [hv]
  exact mul_ne_zero (mul_ne_zero hs hs') v.ne_zero

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LocalizationOfIsStandardSmooth
open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.StabFlat

theorem flat_of_regular {V C : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing C] {ϖ : V}
    (hϖ : Irreducible ϖ) (σ : V →+* C) (h : IsSMulRegular C (σ ϖ)) : σ.Flat := by
  let _ := σ.toAlgebra
  change Module.Flat V C
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
  rintro a ⟨⟨v, hv⟩, hva⟩
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (nonZeroDivisors.ne_zero hv) hϖ
  have h1 : σ (u * ϖ ^ n) * a = 0 := hva
  rw [map_mul, mul_assoc, map_pow] at h1
  exact (h.pow n).right_eq_zero_of_smul (((u.isUnit.map σ).mul_right_eq_zero).1 h1)

theorem flat_of_ideals : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (X H : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of V)) (j : H ⟶ X), IsClosedImmersion j → (∀ (h : H) (σ : V →+* X.presheaf.stalk (j h)), X.fromSpecStalk (j h) ≫ f = Spec.map (CommRingCat.ofHom σ) → ¬ IsUnit (σ ϖ) → ∃ I : Ideal (X.presheaf.stalk (j h)), IsSMulRegular (X.presheaf.stalk (j h) ⧸ I) (σ ϖ) ∧ ∀ (R : Type) [CommRing R] [IsLocalRing R] (φ : X.presheaf.stalk (j h) →+* R), (∃ y : Spec (CommRingCat.of R) ⟶ H, y ≫ j = Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk (j h)) ↔ I ≤ RingHom.ker φ) → Flat (j ≫ f) := by
  intro V _ _ _ ϖ hϖ X H f j hj hI
  refine Flat.of_stalkMap _ fun h => ?_
  obtain ⟨σ, hσ⟩ := Spec.map_surjective (X.fromSpecStalk (j h) ≫ f)
  have reg : IsSMulRegular (H.presheaf.stalk h) ((j.stalkMap h).hom (σ.hom ϖ)) := by
    by_cases hu : IsUnit (σ.hom ϖ)
    · exact (hu.map _).isRegular.left.isSMulRegular
    obtain ⟨I, hr, hI⟩ := hI h σ.hom hσ.symm hu
    have h₁ : I ≤ RingHom.ker (j.stalkMap h).hom :=
      (hI (H.presheaf.stalk h) (j.stalkMap h).hom).1
        ⟨H.fromSpecStalk h, (Scheme.SpecMap_stalkMap_fromSpecStalk j).symm⟩
    have : Nontrivial (X.presheaf.stalk (j h) ⧸ I) := Ideal.Quotient.nontrivial_iff.2
      (ne_top_of_le_ne_top (RingHom.ker_ne_top _) h₁)
    have : IsLocalRing (X.presheaf.stalk (j h) ⧸ I) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    obtain ⟨y, hy⟩ := (hI (X.presheaf.stalk (j h) ⧸ I) (Ideal.Quotient.mk I)).2 Ideal.mk_ker.ge
    have hl : IsLocalHom (Ideal.Quotient.mk I) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    have e : y (IsLocalRing.closedPoint _) = h := by
      apply j.isClosedEmbedding.injective
      refine (congrArg (fun q => q (IsLocalRing.closedPoint _)) hy).trans ?_
      exact (congrArg (X.fromSpecStalk (j h)) (IsLocalRing.comap_closedPoint (Ideal.Quotient.mk I))).trans
        Scheme.fromSpecStalk_closedPoint
    let ψ := H.presheaf.stalkSpecializes (specializes_of_eq e) ≫ Scheme.stalkClosedPointTo y
    have hψ : j.stalkMap h ≫ ψ = CommRingCat.ofHom (Ideal.Quotient.mk I) := by
      apply Spec.map_injective
      rw [← cancel_mono (X.fromSpecStalk (j h)), ← hy, Spec.map_comp, Category.assoc,
        Scheme.SpecMap_stalkMap_fromSpecStalk, Spec.map_comp, Category.assoc,
        Scheme.SpecMap_stalkSpecializes_fromSpecStalk_assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk_assoc]
    have hψ' : ∀ a, ψ.hom ((j.stalkMap h).hom a) = Ideal.Quotient.mk I a := fun a => congrArg (fun q => q.hom a) hψ
    refine IsSMulRegular.of_right_eq_zero_of_smul fun b hb => ?_
    obtain ⟨a, rfl⟩ := j.stalkMap_surjective h b
    refine h₁ (Ideal.Quotient.eq_zero_iff_mem.1 (hr.right_eq_zero_of_smul ?_))
    have := congrArg ψ.hom hb
    rw [smul_eq_mul, map_mul, hψ', hψ', map_zero] at this
    exact this
  have fl : (σ ≫ j.stalkMap h).hom.Flat := flat_of_regular hϖ _ reg
  have e : σ ≫ j.stalkMap h = StructureSheaf.toStalk V ((j ≫ f) h) ≫ (j ≫ f).stalkMap h := by
    apply Spec.map_injective
    refine Eq.trans ?_ (Spec.map_comp _ _).symm
    refine Eq.trans ?_ (congrArg (_ ≫ ·) (Spec.fromSpecStalk_eq' (CommRingCat.of V) ((j ≫ f) h)))
    rw [Spec.map_comp, hσ, Scheme.SpecMap_stalkMap_fromSpecStalk_assoc]
    exact (Scheme.SpecMap_stalkMap_fromSpecStalk (j ≫ f)).symm
  let S := (Spec (CommRingCat.of V)).presheaf.stalk ((j ≫ f) h)
  letI : Algebra V S := StructureSheaf.stalkAlgebra V ((j ≫ f) h)
  have : ((j ≫ f) h).asIdeal.IsPrime := PrimeSpectrum.isPrime (R := V) _
  have : IsLocalization.AtPrime S ((j ≫ f) h).asIdeal := StructureSheaf.IsLocalization.to_stalk V _
  letI : Algebra V (H.presheaf.stalk h) := (σ ≫ j.stalkMap h).hom.toAlgebra
  letI : Algebra S (H.presheaf.stalk h) := ((j ≫ f).stalkMap h).hom.toAlgebra
  have : IsScalarTower V S (H.presheaf.stalk h) := IsScalarTower.of_algebraMap_eq' (congrArg (·.hom) e)
  exact (Module.flat_iff_of_isLocalization S ((j ≫ f) h).asIdeal.primeCompl (H.presheaf.stalk h)).2 fl

theorem height_of_etale_mvPolynomial (K B : Type*) [Field K] [CommRing B] (g : ℕ)
    [Algebra (MvPolynomial (Fin g) K) B] [Algebra.Etale (MvPolynomial (Fin g) K) B] (m : Ideal B) [hm : m.IsMaximal] :
    (m.height : WithBot ℕ∞) = g := by
  have : Nontrivial B := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    exact hm.ne_top (Subsingleton.elim _ _)
  refine le_antisymm (Ideal.height_le_ringKrullDim_of_isPrime.trans
    (SmoothDim.ringKrullDim_of_etale_mvPolynomial K B g).le) ?_
  letI : Algebra K B := ((algebraMap (MvPolynomial (Fin g) K) B).comp
    (algebraMap K (MvPolynomial (Fin g) K))).toAlgebra
  haveI : IsScalarTower K (MvPolynomial (Fin g) K) B := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.FiniteType K B := Algebra.FiniteType.trans
    (S := MvPolynomial (Fin g) K) inferInstance inferInstance
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing K B
  haveI hp := SmoothDim.isMaximal_under_of_finiteType K (MvPolynomial (Fin g) K) B m
  have h1 := ReciprocityTheory.CA.height_add_ringKrullDim_quotient_mvPolynomial_field K g
    (m.under (MvPolynomial (Fin g) K))
  letI := Ideal.Quotient.field (m.under (MvPolynomial (Fin g) K))
  rw [ringKrullDim_eq_zero_of_field, add_zero] at h1
  rw [← h1, WithBot.coe_le_coe, Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
    (m.under (MvPolynomial (Fin g) K)) m]
  exact le_self_add

theorem localization_of_isStandardSmooth {V R A : Type} [CommRing V] [IsNoetherianRing V] [CommRing R] [CommRing A]
    {ϖ : V} (h₀ : ϖ ∈ nonZeroDivisors V) [(Ideal.span {ϖ}).IsMaximal] {g : ℕ} {ρ : V →+* R}
    (hρ : ρ.IsStandardSmoothOfRelativeDimension g) (n : Ideal R) [n.IsMaximal] [Algebra R A]
    [IsLocalization.AtPrime A n] (hn : ρ ϖ ∈ n) :
    IsNoetherianRing A ∧ algebraMap R A (ρ ϖ) ∈ nonZeroDivisors A ∧
      IsRegularLocalRing (A ⧸ Ideal.span {algebraMap R A (ρ ϖ)}) ∧
      ringKrullDim (A ⧸ Ideal.span {algebraMap R A (ρ ϖ)}) = g := by
  have hq : (Ideal.quotientMap ((Ideal.span {ϖ}).map ρ) ρ Ideal.le_comap_map).IsStandardSmoothOfRelativeDimension g := by
    have := RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.2
      (RingHom.isStandardSmoothOfRelativeDimension_isStableUnderBaseChange.{0} g)
    exact MorphismProperty.of_isPushout
      (P := RingHom.toMorphismProperty (@RingHom.IsStandardSmoothOfRelativeDimension g))
      (NilpotentLift.isPushout_quotient_map (Ideal.span {ϖ}) (CommRingCat.ofHom ρ)).flip hρ
  letI := ρ.toAlgebra
  have : Algebra.IsStandardSmoothOfRelativeDimension g V R := hρ
  have : Algebra.IsStandardSmooth V R := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth g
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing V R
  refine ⟨IsLocalization.isNoetherianRing n.primeCompl A inferInstance, ?_, ?_⟩
  · have h₁ : IsSMulRegular R ϖ := Module.Flat.isSMulRegular_of_nonZeroDivisors h₀
    refine IsLocalization.map_nonZeroDivisors_le n.primeCompl A ⟨ρ ϖ, ?_, rfl⟩
    exact mem_nonZeroDivisors_iff_left.2 fun x hx => h₁.right_eq_zero_of_smul hx
  letI := Ideal.Quotient.field (Ideal.span {ϖ})
  set J := (Ideal.span {ϖ}).map ρ with hJ
  obtain ⟨φ, -, hφ⟩ := hq.exists_etale_mvPolynomial
  have hJ' : J = Ideal.span {ρ ϖ} := by rw [hJ, Ideal.map_span, Set.image_singleton]
  have hJn : RingHom.ker (Ideal.Quotient.mk J) ≤ n := by
    rwa [Ideal.mk_ker, hJ', Ideal.span_singleton_le_iff_mem]
  letI := φ.toAlgebra
  have : Algebra.Etale (MvPolynomial (Fin g) (V ⧸ Ideal.span {ϖ})) (R ⧸ J) := hφ.toAlgebra
  have : IsRegularRing (R ⧸ J) := isRegularRing_of_etale (MvPolynomial (Fin g) (V ⧸ Ideal.span {ϖ})) _
  have hm : (n.map (Ideal.Quotient.mk J)).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective hJn
  have hle : J ≤ (Ideal.span {algebraMap R A (ρ ϖ)}).comap (algebraMap R A) := by
    rw [hJ', Ideal.span_singleton_le_iff_mem]
    exact Ideal.mem_span_singleton_self _
  letI : Algebra (R ⧸ J) (A ⧸ Ideal.span {algebraMap R A (ρ ϖ)}) := (Ideal.quotientMap _ _ hle).toAlgebra
  have hl := IsLocalization.of_surjective n.primeCompl A (S' := A ⧸ Ideal.span {algebraMap R A (ρ ϖ)})
    (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective rfl
    (by rw [Ideal.mk_ker, Ideal.mk_ker, hJ', Ideal.map_span, Set.image_singleton])
  have e : n.primeCompl.map (Ideal.Quotient.mk J) = (n.map (Ideal.Quotient.mk J)).primeCompl := by
    have hc : (n.map (Ideal.Quotient.mk J)).comap (Ideal.Quotient.mk J) = n := by
      rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, sup_eq_left.2 hJn]
    ext y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    constructor
    · rintro ⟨x', hx', e⟩ hx
      exact hx' (hc.le (show Ideal.Quotient.mk J x' ∈ _ from e ▸ hx))
    · exact fun hx => ⟨x, fun h => hx (Ideal.mem_map_of_mem _ h), rfl⟩
  rw [e] at hl
  refine ⟨?_, (IsLocalization.AtPrime.ringKrullDim_eq_height (n.map (Ideal.Quotient.mk J)) _).trans
    (height_of_etale_mvPolynomial (V ⧸ Ideal.span {ϖ}) (R ⧸ J) g _)⟩
  have := IsRegularRing.isRegularLocalRing_localization (n.map (Ideal.Quotient.mk J))
  exact IsRegularLocalRing.of_ringEquiv (IsLocalization.algEquiv (n.map (Ideal.Quotient.mk J)).primeCompl
    (Localization.AtPrime (n.map (Ideal.Quotient.mk J))) _).toRingEquiv

theorem stalk_of_smooth : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of V)) (g : ℕ), SmoothOfRelativeDimension g f → ∀ x : X, IsClosed ({x} : Set X) → ∀ σ : V →+* X.presheaf.stalk x, X.fromSpecStalk x ≫ f = Spec.map (CommRingCat.ofHom σ) → ¬ IsUnit (σ ϖ) → IsNoetherianRing (X.presheaf.stalk x) ∧ σ ϖ ∈ nonZeroDivisors (X.presheaf.stalk x) ∧ IsRegularLocalRing (X.presheaf.stalk x ⧸ Ideal.span {σ ϖ}) ∧ ringKrullDim (X.presheaf.stalk x ⧸ Ideal.span {σ ϖ}) = g := by
  intro V _ _ _ ϖ hϖ X f g hg x hx σ hσ hn
  obtain ⟨U, hU, W, hW, hxW, e, H⟩ := hg.exists_isStandardSmoothOfRelativeDimension x
  have hfx : f x = IsLocalRing.closedPoint V := by
    refine ((congrArg f Scheme.fromSpecStalk_closedPoint.symm).trans
      (congrArg (fun q => q (IsLocalRing.closedPoint _)) hσ)).trans ?_
    refine PrimeSpectrum.ext (Eq.symm ((IsLocalRing.maximalIdeal.isMaximal V).eq_of_le
      (PrimeSpectrum.isPrime _).ne_top ?_))
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_le_iff_mem]
    exact hn
  obtain rfl : U = ⊤ := (IsLocalRing.closedPoint_mem_iff U).1 (hfx ▸ e hxW)
  let ρ := (Scheme.ΓSpecIso (CommRingCat.of V)).inv ≫ f.appLE ⊤ W e
  have hρ : ρ.hom.IsStandardSmoothOfRelativeDimension g :=
    (RingHom.isStandardSmoothOfRelativeDimension_respectsIso.cancel_left_isIso _ _).2 H
  have hc : ρ ≫ X.presheaf.germ W x hxW = CommRingCat.ofHom σ := by
    apply Spec.map_injective
    rw [← hσ, ← hW.fromSpecStalk_eq_fromSpecStalk hxW, Spec.map_comp, Spec.map_comp, IsAffineOpen.fromSpecStalk,
      Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec f hU hW e, IsAffineOpen.fromSpec_top,
      Scheme.isoSpec_Spec_inv]
  letI : Algebra Γ(X, W) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hxW⟩
  have hl : IsLocalization.AtPrime (X.presheaf.stalk x) (hW.primeIdealOf ⟨x, hxW⟩).asIdeal :=
    hW.isLocalization_stalk ⟨x, hxW⟩
  haveI := hW.primeIdealOf_isMaximal_of_isClosed ⟨x, hxW⟩ hx
  have hs : algebraMap Γ(X, W) (X.presheaf.stalk x) (ρ.hom ϖ) = σ ϖ := congrArg (fun q => q.hom ϖ) hc
  haveI : (Ideal.span {ϖ}).IsMaximal := hϖ.maximalIdeal_eq ▸ IsLocalRing.maximalIdeal.isMaximal V
  rw [← hs]
  refine localization_of_isStandardSmooth (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero) hρ
    (hW.primeIdealOf ⟨x, hxW⟩).asIdeal ?_
  by_contra hm
  exact hn (hs ▸ IsLocalization.map_units (X.presheaf.stalk x)
    (⟨_, hm⟩ : (hW.primeIdealOf ⟨x, hxW⟩).asIdeal.primeCompl))

end GlobalTheory.StabFlat
end
