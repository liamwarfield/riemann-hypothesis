module

public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLiftOfRangeSubset
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardTorsionPointsUnconditional
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsEndomorphismAlgebraisingThickenings
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiCompEndomorphismEqPowOfPullbackIso
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatKernelPolarisationCosetsOverDVR
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RelAmpleNearFibreFlatProjective

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SemiAbelianHomExtensionDvr
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SemiAbelianHomExtensionDvr
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

namespace GlobalTheory

theorem homExtension_semiAbelian_dvr_unconditional : HomExtSt :=
  GlobalTheory.existsUnique_hom_extension_semiAbelian_dvr
    (GlobalTheory.AbelianSubgroupFinite.finite_of_no_torsion GlobalTheory.UU.TorsionCount.card_torsion_points_unconditional)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SemiAbelianHomExtensionDvrStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiAbelian_hom_extension_dvr : HomExtSt := by
  first | exact @GlobalTheory.homExtension_semiAbelian_dvr_unconditional | exact GlobalTheory.homExtension_semiAbelian_dvr_unconditional | (intros; apply GlobalTheory.homExtension_semiAbelian_dvr_unconditional <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsEndomorphismActionUniformizationData
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGeneratorOfCompatibleThickeningGenerators
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGeneratorOfCompatibleThickeningGenerators
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Unif

theorem exists_gen_of_thick : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), IsAdicComplete I R → ∀ (Y : Over (Spec (CommRingCat.of R))), Smooth Y.hom → IsProjBy Y.hom → ∀ (W : Scheme.{0}) (L : LB W) (K : Type) [Fintype K] (φ : K → (Y.left ⟶ W)) (ε : K → ℤ) (φ' : ∀ e, K → ((thickObj R I e Y).left ⟶ W)), L.IsLB → (∀ e k, pullback.fst Y.hom (thick R I e) ≫ φ k = φ' e k) → ∀ f : ∀ e, LB.Gen (LB.LinComb L (φ' e) ε), (∀ e, (f e).IsGen) → (∀ e z J, Good L z J → val (f (e + 1)) (thickMap R I e Y) z J = val (f e) (𝟙 _) z J) → ∃ u : LB.Gen (LB.LinComb L φ ε), u.IsGen ∧ ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e Y).left) (z : Z) (J), Good L z J → val u (r ≫ pullback.fst Y.hom (thick R I e)) z J = val (f e) r z J := by
  intro R _ _ I hI Y hs hp W L K _ φ ε φ' hL hφ f hf hc
  obtain ⟨s, hsv⟩ := GlobalTheory.T.exists_section_linearCombination_of_compatible_thickenings R I hI Y hs hp W L K φ ε φ' hL hφ (fun e => genSec (f e) (hf e))
    (fun e z J hJ => (sval_genSec _ _ _ z hJ).trans
      ((congrArg Units.val (hc e z J hJ)).trans (sval_genSec _ _ _ z hJ).symm))
  have : IsProper Y.hom := GlobalTheory.AbLaw.isProper_of_isProjBy _ _ _ hp
  have top : nonzeroLocus s = ⊤ :=
    eq_top_of_special_part R I (IsAdicComplete.le_jacobson_bot I) Y _ fun z => by
      choose J hJ using fun ψ : (thickObj R I 0 Y).left ⟶ W => exists_chart hL (ψ z)
      have h1 := hsv 0 _ (𝟙 _) z J hJ
      rw [Category.id_comp, sval_genSec _ _ _ z hJ] at h1
      refine (TwistZero.mem_nonzeroLocus_iff s (pullback.fst Y.hom (thick R I 0)) z hJ).2 ?_
      exact (congrArg IsUnit h1).mpr (Units.isUnit _)
  have hu : ∀ j, IsUnit (s.f j) := fun j => Y.left.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
    obtain ⟨J, hJ, e⟩ := sval_trans hL s y j hy
    exact (congrArg IsUnit ((gs_eq (𝟙 Y.left) y (LB.wchart L φ j) hy _).symm.trans e)).mpr
      ((Units.isUnit _).mul ((TwistZero.mem_nonzeroLocus_iff s (𝟙 _) y hJ).1 (by rw [top]; trivial)))
  refine ⟨⟨fun j => (hu j).unit⟩, fun i j => Units.ext (s.compat i j), fun e Z r z J hJ => Units.ext ?_⟩
  exact (gs_unit _ z _ (hJ.mem φ _) _).symm.trans ((hsv e Z r z J hJ).trans (sval_genSec _ _ r z hJ))

end GlobalTheory.Unif
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGeneratorOfCompatibleThickeningGeneratorsStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generator_of_compatible_thickening_generators : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), IsAdicComplete I R → ∀ (Y : Over (Spec (CommRingCat.of R))), Smooth Y.hom → IsProjBy Y.hom → ∀ (W : Scheme.{0}) (L : LB W) (K : Type) [Fintype K] (φ : K → (Y.left ⟶ W)) (ε : K → ℤ) (φ' : ∀ e, K → ((thickObj R I e Y).left ⟶ W)), L.IsLB → (∀ e k, pullback.fst Y.hom (thick R I e) ≫ φ k = φ' e k) → ∀ f : ∀ e, LB.Gen (LB.LinComb L (φ' e) ε), (∀ e, (f e).IsGen) → (∀ e z J, Good L z J → val (f (e + 1)) (thickMap R I e Y) z J = val (f e) (𝟙 _) z J) → ∃ u : LB.Gen (LB.LinComb L φ ε), u.IsGen ∧ ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e Y).left) (z : Z) (J), Good L z J → val u (r ≫ pullback.fst Y.hom (thick R I e)) z J = val (f e) r z J := by
  first | exact @GlobalTheory.Unif.exists_gen_of_thick | exact GlobalTheory.Unif.exists_gen_of_thick | (intros; apply GlobalTheory.Unif.exists_gen_of_thick <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsEndomorphismActionUniformizationData
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.EndData

theorem val_eq_of_flat {X Y Y' Y₁ Y₂ : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    {φ₁ : K → (Y₁ ⟶ X)} {φ₂ : K → (Y₂ ⟶ X)} {ε : K → ℤ} (t₁ : LB.Gen (LB.LinComb L φ₁ ε))
    (t₂ : LB.Gen (LB.LinComb L φ₂ ε)) (m₁ : Y ⟶ Y₁) (m₂ : Y ⟶ Y₂) (hm : ∀ k, m₁ ≫ φ₁ k = m₂ ≫ φ₂ k)
    (π : Y' ⟶ Y) [Flat π] [Surjective π]
    (h : ∀ x J, Good L x J → val t₁ (π ≫ m₁) x J = val t₂ (π ≫ m₂) x J) (y : Y) (J) (hJ : Good L y J) :
    val t₁ m₁ y J = val t₂ m₂ y J := by
  have : Epi π := Flat.epi_of_flat_of_surjective _
  let j : K → L.ι := fun k => J (m₁ ≫ φ₁ k)
  have h₁ : m₁ y ∈ LB.wchart L φ₁ j := hJ.mem φ₁ m₁
  have e₂ : ∀ k, J (m₂ ≫ φ₂ k) = j k := fun k => congrArg J (hm k).symm
  have h₂ : m₂ y ∈ LB.wchart L φ₂ j := (funext e₂ : _ = j) ▸ hJ.mem φ₂ m₂
  have key := UnifCompare.gm_eq_of_flat_surjective π (pullU m₁ (LB.wchart L φ₁ j) (t₁.s j))
    (pullU m₂ (LB.wchart L φ₂ j) (t₂.s j)) (fun x hx₁ hx₂ => by
      obtain ⟨J', hJ', e⟩ := exists_good L hL x (fun k => (π ≫ m₁) ≫ φ₁ k) j
        (fun a b e => congrArg J (by simpa only [Category.assoc, cancel_epi] using e))
        (fun k => Set.mem_iInter.1 hx₁ k)
      have := h x J' hJ'
      rw [val_of t₁ _ x J' j e, val_of t₂ _ x J' j (fun k => by
        rw [Category.assoc, ← hm, ← Category.assoc]; exact e k)] at this
      exact (gm_pull π m₁ x _ hx₁ _).trans (this.trans (gm_pull π m₂ x _ hx₂ _).symm)) (𝟙 Y) y h₁ h₂
  have k₁ := gm_pull (𝟙 Y) m₁ y _ h₁ (t₁.s j)
  have k₂ := gm_pull (𝟙 Y) m₂ y _ h₂ (t₂.s j)
  rw [Category.id_comp] at k₁ k₂
  rw [val_of t₂ m₂ y J j e₂]
  exact k₁.symm.trans (key.trans k₂)

theorem val_eq_one {R : Type} [CommRing R] (I : Ideal R) [IsHausdorff I R] {X : Scheme.{0}} {L : LB X}
    (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Spec (CommRingCat.of R) ⟶ X)} {ε : K → ℤ}
    (hf : FormEq (K' := PEmpty) φ ε PEmpty.elim PEmpty.elim) (c : LB.Gen (LB.LinComb L φ ε)) (hc : c.IsGen)
    (h : ∀ e z J, Good L z J → val c (thick R I e) z J = 1) (y) (J) (hJ : Good L y J) :
    val c (𝟙 _) y J = 1 := by
  obtain ⟨c', -, hv⟩ := exists_gen hL hf c hc
  have le : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ LB.wchart L (K := PEmpty) PEmpty.elim PEmpty.elim :=
    fun _ _ => Set.mem_iInter.2 fun k => k.elim
  have ev : ∀ (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of R)) (z : Z) (J), Good L z J →
      val c r z J = gm r z ⊤ (res le (c'.s PEmpty.elim)) := fun Z r z J hJ =>
    (hv Z r z J hJ).symm.trans ((val_of c' r z J PEmpty.elim (fun k => k.elim)).trans
      (gm_res r z le trivial _).symm)
  have one : res le (c'.s PEmpty.elim) = 1 := by
    refine Units.ext ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).hom).1
      (SecAlg.eq_of_forall_mk I fun e => ?_))
    have key : ((thick R I e).app ⊤).hom (res le (c'.s PEmpty.elim)).val = ((thick R I e).app ⊤).hom 1 := by
      refine fn_ext fun z hz => ?_
      choose J hJ using fun ψ : Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) ⟶ X => exists_chart hL (ψ z)
      rw [gs_pull _ _ z ⊤ trivial, gs_pull _ _ z ⊤ trivial, Category.id_comp, gs_unit _ z ⊤ trivial,
        ← ev _ _ z J hJ, h e z J hJ, gs_eq _ z ⊤ trivial, map_one, map_one, Units.val_one]
    have nat := fun x => congrArg (fun φ => φ.hom x)
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1)))))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at nat
    exact (nat _).symm.trans ((congrArg _ key).trans (nat 1))
  rw [ev _ _ y J hJ, one, map_one]

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}

theorem prod_unit (D : DegPre R) (p : D.P.A ⟶ D.P.A) [IsMonHom p] (χ : D.X) {U : Type} [CommGroup U]
    (h : (Spec (CommRingCat.of R) ⟶ D.P.A.left) → U) :
    ∏ k, h (eSec D.P.A ≫ D.Oφ p χ k) ^ Oε k = 1 ∧ ∏ k, h (eSec D.P.A ≫ D.Oφ p χ k) ^ Oinvε k = 1 := by
  let T := 𝟙_ (Over (Spec (CommRingCat.of R)))
  have o : η[D.P.A] ≫ p = (1 : T ⟶ D.P.A) := by simp [Hom.one_def, T]
  have e0 : ∀ k, eSec D.P.A ≫ D.Oφ p χ k = D.Oφ (1 : T ⟶ D.P.A) χ k :=
    fun k => (WeightPf.Oφ_comp η[D.P.A] p χ k).trans (congrArg (D.Oφ · χ k) o)
  simp only [e0]
  rw [Fin.prod_univ_four, Fin.prod_univ_four]
  constructor
  · show h ((1 : T ⟶ D.P.A) * (toUnit T ≫ D.c χ)).left ^ (1 : ℤ) * h (toUnit T ≫ D.c χ).left ^ (-1 : ℤ) *
      h (1 : T ⟶ D.P.A).left ^ (-1 : ℤ) * h (1 : T ⟶ D.P.A).left ^ (1 : ℤ) = 1
    rw [_root_.one_mul]
    simp
  · show h ((1 : T ⟶ D.P.A) * (toUnit T ≫ D.c χ)).left ^ (-1 : ℤ) * h (toUnit T ≫ D.c χ).left ^ (1 : ℤ) *
      h (1 : T ⟶ D.P.A).left ^ (1 : ℤ) * h (1 : T ⟶ D.P.A).left ^ (-1 : ℤ) = 1
    rw [_root_.one_mul]
    simp

omit [IsDomain R] in
theorem map_fst (e : ℕ) {G G' : Over (Spec (CommRingCat.of R))} (a : G ⟶ G') :
    ((Over.pullback (thick R I e)).map a).left ≫ pullback.fst G'.hom (thick R I e) =
      pullback.fst G.hom (thick R I e) ≫ a.left := pullback.lift_fst _ _ _

omit [IsDomain R] in
theorem trans_fst (e : ℕ) (G : Over (Spec (CommRingCat.of R))) :
    thickMap R I e G ≫ pullback.fst G.hom (thick R I (e + 1)) = pullback.fst G.hom (thick R I e) :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)


omit [IsDomain R] in
theorem trans_map (e : ℕ) {G G' : Over (Spec (CommRingCat.of R))} (a : G ⟶ G') :
    thickMap R I e G ≫ ((Over.pullback (thick R I (e + 1))).map a).left =
      ((Over.pullback (thick R I e)).map a).left ≫ thickMap R I e G' := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, map_fst, trans_fst, map_fst, ← Category.assoc, trans_fst]
  · have k : ∀ B : Over (Spec (CommRingCat.of R)), thickMap R I e B ≫ pullback.snd _ _ =
        pullback.snd _ _ ≫ thickTrans R I e := fun B => pullback.lift_snd _ _ _
    have l : ∀ n, ((Over.pullback (thick R I n)).map a).left ≫ pullback.snd _ _ = pullback.snd _ _ :=
      fun n => pullback.lift_snd _ _ _
    rw [Category.assoc, Category.assoc, l, k, k, ← Category.assoc, l]

variable {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem exists_abelian (hL : LL) (hR : AdmBase R I) (U : UnifPre I D A G) (aG : G ⟶ G) [IsMonHom aG] :
    ∃ aB : D.toPre.P.A ⟶ D.toPre.P.A, IsMonHom aB ∧ ∀ e,
      (Over.pullback (thick R I e)).map aG ≫ (U.gt e).q = (U.gt e).q ≫ (Over.pullback (thick R I e)).map aB := by
  have hN := hR.1
  have hC := hR.2.2.2
  choose b hb hq using fun e => (gtCoord_end_torus_abelian hL R I hR D.toPre e G (U.gt e)
    ((Over.pullback (thick R I e)).map aG) inferInstance).2.exists
  have hql : ∀ e, (U.gt e).q.left ≫ (b e).left = ((Over.pullback (thick R I e)).map aG).left ≫ (U.gt e).q.left :=
    fun e => (congrArg (·.left) (hq e)).symm
  obtain ⟨aB, haB⟩ := T.exists_endomorphism_algebraising_thickenings R I hC D.toPre.P.A D.toPre.P.isAb.smooth
    (AbProj.isProjBy_of_isPullback D.toPre.P (IsPullback.id_horiz _))
    (fun e => (b e).left ≫ pullback.fst D.toPre.P.A.hom (thick R I e))
    (fun e => by
      have w : (b e).left ≫ pullback.snd D.toPre.P.A.hom (thick R I e) = pullback.snd _ _ := Over.w (b e)
      rw [Category.assoc, pullback.condition, ← Category.assoc, w])
    (fun e => by
      have := (U.gt e).q_flat
      have := (U.gt e).q_surj
      have : Epi (U.gt e).q.left := Flat.epi_of_flat_of_surjective _
      rw [← cancel_epi (U.gt e).q.left, ← Category.assoc, ← UnifCompare.trans_comp_q, Category.assoc,
        ← Category.assoc (U.gt (e + 1)).q.left, hql, ← Category.assoc (U.gt e).q.left, hql, ← Category.assoc,
        ← Category.assoc, trans_map, Category.assoc _ (thickMap R I e G), UnifCompare.trans_comp_q,
        Category.assoc, Category.assoc, trans_fst, Category.assoc])
  have hm : ∀ e, (Over.pullback (thick R I e)).map aB = b e := fun e =>
    Over.OverMorphism.ext (pullback.hom_ext ((map_fst e aB).trans (haB e)) ((Over.w _).trans (Over.w (b e)).symm))
  refine ⟨aB, AbelianPartIso.isMonHom_of_thickenings (IsAdicComplete.le_jacobson_bot I) D.toPre.P.isAb
    D.toPre.P.isAb aB fun e => ?_, fun e => ?_⟩
  · rw [hm]; exact hb e
  · rw [hm]; exact hq e

theorem exists_endU : LL → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (aG : G ⟶ G) (aA : A.A ⟶ A.A), IsMonHom aG → IsMonHom aA → (Over.pullback (jK R)).map aG ≫ U.gen.hom = U.gen.hom ≫ aA → ∃ E : EndU U.toUnifPre, E.aG = aG ∧ E.aA = aA := by
  intro hL R _ _ _ I hR D A G _ _ _ U aG aA hG hA hext
  have hC := hR.2.2.2
  have hB := D.toPre.P.isLB
  obtain ⟨aB, haB, hq⟩ := exists_abelian hL hR U.toUnifPre aG
  obtain ⟨h, hh⟩ := T.uniformisation_endomorphism_character_map_constant hL R I hR D A G U.toUnifPre aG hG
  choose t ht hi using hh
  choose v hv vv using fun χ e => T.exists_gen_of_torusEnd_compat R I D.toPre e G (U.gt e) ((Over.pullback (thick R I e)).map aG) aB h (t e)
    inferInstance (ht e) (hi e) (hq e) χ
  have down : ∀ χ e (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J), Good D.toPre.P.L z J →
      val ((U.gt (e + 1)).t χ) (r ≫ thickMap R I e G) z J = val ((U.gt e).t χ) r z J :=
    fun χ e Z r z J hJ => (val_pull hJ _ _ _).symm.trans (val_corr hJ (U.gt_t e χ) r)
  choose u hu uv using fun χ => T.exists_generator_of_compatible_thickening_generators R I hC D.toPre.P.A D.toPre.P.isAb.smooth
    (AbProj.isProjBy_of_isPullback D.toPre.P (IsPullback.id_horiz _)) _ D.toPre.P.L _ _ _ _ hB (fun _ _ => rfl)
    (v χ) (hv χ) (fun e z J hJ => by
      have := (U.gt e).q_flat
      have := (U.gt e).q_surj
      refine val_eq_of_flat hB _ _ _ _ (fun k => ?_) (U.gt e).q.left (fun x J hJ => ?_) z J hJ
      · rw [← Category.assoc, trans_fst, Category.id_comp]
      · have k₁ := vv χ (e + 1) _ (𝟙 _ ≫ thickMap R I e G) x J hJ
        have k₀ := vv χ e _ (𝟙 _) x J hJ
        rw [down _ _ _ _ _ _ hJ, Category.assoc, trans_map, ← Category.assoc, down _ _ _ _ _ _ hJ, k₀,
          Category.id_comp, Category.id_comp, UnifCompare.trans_comp_q] at k₁
        rw [Category.comp_id]
        exact (mul_left_cancel k₁).symm)
  refine ⟨⟨aG, aA, aB, hG, hA, haB, h, hext, hq, fun e => ⟨t e, ht e, hi e⟩, u, fun χ => ⟨hu χ, ?_⟩,
    fun e χ Z x z J hJ => ?_⟩, rfl, rfl⟩
  · refine corr_of_val hB fun y J hJ => Eq.trans ?_ (val_one _).symm
    refine val_eq_one I hB (fun V _ k => ?_) _ (pullGen_isGen _ _ _ _ (hu χ) _) (fun e z J hJ => ?_) y J hJ
    · refine (Fintype.prod_sum_type _).trans ((congrArg₂ (· * ·) (prod_unit D.toPre (𝟙 _) (h χ) k).1
        (prod_unit D.toPre aB χ k).2).trans ((_root_.mul_one _).trans (Fintype.prod_empty _).symm))
    · have := (U.gt e).q_hom
      have k := vv χ e _ (1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e G).left z J hJ
      rw [← Over.comp_left, ← Over.comp_left, MonObj.one_comp, MonObj.one_comp, TorusCoord.val_unit _ _ hJ,
        TorusCoord.val_unit _ _ hJ, _root_.one_mul, ← uv χ e _ _ z J hJ] at k
      have o : (1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e D.toPre.P.A) =
        η[thickObj R I e D.toPre.P.A] := by simp [Hom.one_def]
      rw [o] at k
      exact (val_pull hJ _ _ _).trans ((congrArg (fun p => val (u χ) p z J)
        (UnitValue.eSec_pullback_fst (thick R I e) D.toPre.P.A).symm).trans k.symm)
  · refine (vv χ e Z x z J hJ).trans (congrArg (_ * ·) ((uv χ e Z _ z J hJ).symm.trans ?_))
    exact congrArg (fun p => val (u χ) p z J) (Category.assoc _ _ _)

end GlobalTheory.EndData
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsEndomorphismActionUniformizationDataStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_endomorphism_action_uniformization_data : LL → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (aG : G ⟶ G) (aA : A.A ⟶ A.A), IsMonHom aG → IsMonHom aA → (Over.pullback (jK R)).map aG ≫ U.gen.hom = U.gen.hom ≫ aA → ∃ E : EndU U.toUnifPre, E.aG = aG ∧ E.aA = aA := by
  first | exact @GlobalTheory.EndData.exists_endU | exact GlobalTheory.EndData.exists_endU | (intros; apply GlobalTheory.EndData.exists_endU <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiFunctionEqThetaOfPrimitiveLineBundle
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiFunctionEqThetaOfPrimitiveLineBundle
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section

namespace GlobalTheory.PsiPrim

theorem exists_norm_three {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (Lr : RigLB G) (f : G ⟶ G) [IsMonHom f]
    (N : ℕ) (h : HasGen Lr.L (fsum (K := Fin 2) ![𝟙 G.left, f.left] ![((1 * N : ℕ) : ℤ), -((1 : ℕ) : ℤ)])) :
    ∃ β : LB.Gen (LB.LinComb Lr.L (K := Fin 3) ![𝟙 _, f.left, (1 : G ⟶ G).left]
      ![(N : ℤ), -((1 : ℕ) : ℤ), ((1 : ℕ) : ℤ) - N]), β.IsGen ∧
      LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ β (eSec G)) (LB.oneGen Lr.L) := by
  have h1 := h.add ((GlobalTheory.PullGenG.hasGen_one Lr).zsmul (((1 : ℕ) : ℤ) - N))
  obtain ⟨X0, hX0⟩ := h1.gen Lr.isLB (K' := Fin 3) ![𝟙 _, f.left, (1 : G ⟶ G).left]
      ![(N : ℤ), -((1 : ℕ) : ℤ), ((1 : ℕ) : ℤ) - N] (by
    simp only [fsum, Fin.sum_univ_two, Fin.sum_univ_three, Matrix.cons_val, lf_single, Finsupp.smul_single_one,
      _root_.one_mul, Matrix.cons_val_zero, Matrix.cons_val_one])
  have hzp : eSec G ≫ (toUnit G).left = 𝟙 _ := by
    simp only [eSec, ← Over.comp_left]
    rw [show η[G] ≫ toUnit G = 𝟙 _ from toUnit_unique _ _]
    rfl
  obtain ⟨β, hβ, n⟩ := exists_normalized Lr.isLB _ _ X0 hX0 (toUnit G).left (eSec G) hzp (by
    have ha : eSec G ≫ f.left = eSec G := by
      simp only [eSec, ← Over.comp_left, IsMonHom.one_hom]
    have hb : eSec G ≫ (1 : G ⟶ G).left = eSec G := by
      show eSec G ≫ (toUnit G).left ≫ eSec G = _
      rw [← Category.assoc, hzp, Category.id_comp]
    simp only [fsum, Fin.sum_univ_three, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id,
      ha, hb, ← Finsupp.single_add]
    rw [show (N : ℤ) + -((1 : ℕ) : ℤ) + (((1 : ℕ) : ℤ) - N) = 0 by ring, Finsupp.single_zero])
  exact ⟨β, hβ, corr_one_of (fun j hj => n j hj)⟩

theorem star_smul_injective {O : Type} [CommRing O] [StarRing O] {X : Type} [AddCommGroup X] [Module O X]
    [Module.Free ℤ X] (a : O) (N : ℕ) (hN : a * star a = (N : O)) (hN1 : 1 ≤ N) {x y : X}
    (h : star a • x = star a • y) : x = y := by
  have h2 := congrArg (a • ·) h
  simp only [smul_smul, hN, Nat.cast_smul_eq_nsmul] at h2
  have hN0 : (N : ℤ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have h3 : (N : ℤ) • (x - y) = 0 := by
    rw [smul_sub, natCast_zsmul, natCast_zsmul, h2, sub_self]
  exact sub_eq_zero.1 ((smul_eq_zero.1 h3).resolve_left hN0)

theorem exists_norm_form : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (ιD : D.toPre.OAct O) (ιA : A.OAct O) (ιG : RingAct G O), U.toUnifPre.OLinear O ιD ιA ιG → (∀ a, LBIso (cubeLB G ![fst G G ≫ ιG.act a, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ ιG.act (star a)] U.LG.L)) → ∀ (w₀ : O), LBIso U.LG.L (cubeLB G ![𝟙 G, ιG.act w₀] U.LG.L) → ∀ (a : O) (N : ℕ), a * star a = (N : O) → 1 ≤ N →
    ∃ κ : LB.Gen (kapLB D.toPre (ιD.onB.act a) N 1), Normd κ ∧ ∀ y (z : (TK R).left) J, Good D.toPre.P.L z J →
      val (D.toPre.psi (a • y)) (𝟙 _) z J * rigV D.toPre (TK R).hom z J =
        val (D.toPre.psi y) (𝟙 _) z J ^ N * val κ (D.toPre.xK y) z J * rigV D.toPre (TK R).hom z J ^ N := by
  intro hL h1 h2 h3 h4 R _ _ _ I hI D A G _ _ hG U O _ _ _ ιD ιA ιG hlin hadj w₀ hprim a N hN hN1
  obtain ⟨E, eG, -, eB, eh, -⟩ := GlobalTheory.T.exists_uniformizationEndomorphism_of_linear hL R I hI D A G hG U O ιD ιA ιG hlin a
  obtain ⟨E', eG', -, -, eh', -⟩ := GlobalTheory.T.exists_uniformizationEndomorphism_of_linear hL R I hI D A G hG U O ιD ιA ιG hlin (star a)
  have hg := GlobalTheory.PullGenG.hasGen_pull U.LG U.cubG ιG w₀ a N hN (hadj a) hprim 1
  rw [← eG] at hg
  haveI := E.homG
  obtain ⟨β, hβ, nβ⟩ := exists_norm_three U.LG E.aG N hg
  obtain ⟨κ, hκ, -⟩ := GlobalTheory.T.descent_powerIso_endomorphism_abelianPart_uniformization hL R I hI D A G hG U E N 1 β hβ nβ
  have key := GlobalTheory.T.psi_comp_endomorphism_eq_pow_of_pullback_iso hL h1 h2 h3 h4 R I hI D A G hG U (AlgebraicClosure (FractionRing R)) E E'
    (by rw [eG, eG']; exact hadj a)
    (fun x y e => star_smul_injective a N hN hN1 (by rw [← eh, ← eh]; exact e)) N hN1
    (fun y => by rw [eh, eh', star_star, smul_smul, mul_comm, hN, Nat.cast_smul_eq_nsmul])
    (hg.gen U.LG.isLB _ _ (by rw [_root_.one_mul])) κ hκ
  rw [← eB]
  refine ⟨κ, hκ, fun y z J hJ => ?_⟩
  have := key y z J hJ
  rwa [eh', star_star] at this

theorem prod_kap {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (f : D.P.A ⟶ D.P.A) (N : ℕ) {U : Type} [CommGroup U]
    (h : (D.P.A.left ⟶ D.P.A.left) → U) :
    ∏ i : Fin 3, h ((![𝟙 _, f.left, (1 : D.P.A ⟶ D.P.A).left] : Fin 3 → _) i) ^
      (![(N : ℤ), -((1 : ℕ) : ℤ), ((1 : ℕ) : ℤ) - N] : Fin 3 → ℤ) i =
      h (𝟙 _) ^ (N : ℤ) * h f.left ^ (-((1 : ℕ) : ℤ)) * h (1 : D.P.A ⟶ D.P.A).left ^ (((1 : ℕ) : ℤ) - N) :=
  Fin.prod_univ_three _

theorem traceFormTwistIso_of_primitive_lineBundle : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (ιD : D.toPre.OAct O) (ιA : A.OAct O) (ιG : RingAct G O), U.toUnifPre.OLinear O ιD ιA ιG → (∀ a, LBIso (cubeLB G ![fst G G ≫ ιG.act a, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ ιG.act (star a)] U.LG.L)) → ∀ (w₀ : O) (ν : ℕ), w₀ + star w₀ = 1 → w₀ * star w₀ = (ν : O) → 1 ≤ ν → Even ν → LBIso U.LG.L (cubeLB G ![𝟙 G, ιG.act w₀] U.LG.L) → TraceFormTwistIso D.toPre ιD w₀ := by
  intro hL h1 h2 h3 h4 R _ _ _ I hI D A G _ _ hG U O _ _ _ ιD ιA ιG hlin hadj w₀ ν htr hν hν1 _ hprim
  have H := exists_norm_form hL h1 h2 h3 h4 R I hI D A G hG U O ιD ιA ιG hlin hadj w₀ hprim
  obtain ⟨κ₀, ⟨g₀, n₀⟩, v₀⟩ := H w₀ ν hν hν1
  obtain ⟨κ₁, ⟨g₁, n₁⟩, v₁⟩ := H (1 + w₀) (ν + 2) (by
    rw [star_add, star_one]; push_cast; linear_combination htr + hν) (by omega)
  have e₁ : ιD.onB.act (1 + w₀) = padd D.toPre.P.A (𝟙 _) (ιD.onB.act w₀) := by
    rw [ιD.onB.map_add, ιD.onB.map_one]
  obtain ⟨u, hu, vu⟩ := exists_gen D.toPre.P.isLB (K' := Fin 4)
    (φ' := ![(padd D.toPre.P.A (𝟙 _) (ιD.onB.act w₀)).left, 𝟙 D.toPre.P.A.left, (ιD.onB.act w₀).left,
      (toUnit D.toPre.P.A ≫ η[D.toPre.P.A]).left]) (ε' := ![1, -2, -1, 2]) (fun V _ h => by
      refine (prod_sum₂ (K := Fin 3) (K' := Fin 3) (U := V) _ (prod_kap D.toPre _ ν h)
        (prod_neg _ _ (prod_kap D.toPre _ (ν + 2) h))).trans ?_
      rw [Fin.prod_univ_four, e₁]
      have o : (toUnit D.toPre.P.A ≫ η[D.toPre.P.A]) = 1 := rfl
      rw [o]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one]
      push_cast
      module)
    (LB.mulGen D.toPre.P.L _ _ _ _ κ₀ (LB.invGen D.toPre.P.L _ _ κ₁))
    (mulGen_isGen _ _ _ _ _ _ _ g₀ (invGen_isGen _ _ _ _ g₁))
  refine ⟨u, hu, corr_of_val D.toPre.P.isLB fun z J hJ => ?_, fun y => corr_of_val D.toPre.P.isLB fun z J hJ => ?_⟩
  · have a₀ := val_corr hJ n₀ (𝟙 _)
    have a₁ := val_corr hJ n₁ (𝟙 _)
    rw [val_pull hJ] at a₀ a₁
    rw [val_pull hJ, vu _ _ z J hJ, val_mul hJ, val_inv, a₀, a₁, mul_inv_cancel, val_one]
  · have t : val (D.toPre.tau y (w₀ • y)) (𝟙 _) z J = val (D.toPre.psi (y + w₀ • y)) (𝟙 _) z J *
        (val (D.toPre.psi y) (𝟙 _) z J)⁻¹ * (val (D.toPre.psi (w₀ • y)) (𝟙 _) z J)⁻¹ * (val D.toPre.rigK (𝟙 _) z J)⁻¹ :=
      (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
        (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))
    have r : val D.toPre.rigK (𝟙 _) z J = rigV D.toPre (TK R).hom z J :=
      (val_pull hJ _ _ _).trans (by rw [Category.id_comp]; rfl)
    have b₀ := v₀ y z J hJ
    have b₁ := v₁ y z J hJ
    rw [add_smul, one_smul] at b₁
    rw [val_mul hJ, val_mul hJ, val_pull hJ, Category.id_comp, vu _ _ z J hJ, val_mul hJ, val_inv, t, r]
    apply Additive.ofMul.injective
    have c₀ := congrArg Additive.ofMul b₀
    have c₁ := congrArg Additive.ofMul b₁
    simp only [ofMul_mul, ofMul_inv, ofMul_pow] at c₀ c₁ ⊢
    linear_combination (norm := module) c₁ - c₀

end GlobalTheory.PsiPrim

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiFunctionEqThetaOfPrimitiveLineBundleStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psiFunction_eq_theta_of_primitive_lineBundle : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (ιD : D.toPre.OAct O) (ιA : A.OAct O) (ιG : RingAct G O), U.toUnifPre.OLinear O ιD ιA ιG → (∀ a, LBIso (cubeLB G ![fst G G ≫ ιG.act a, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ ιG.act (star a)] U.LG.L)) → ∀ (w₀ : O) (ν : ℕ), w₀ + star w₀ = 1 → w₀ * star w₀ = (ν : O) → 1 ≤ ν → Even ν → LBIso U.LG.L (cubeLB G ![𝟙 G, ιG.act w₀] U.LG.L) → TraceFormTwistIso D.toPre ιD w₀ := by
  first | exact @GlobalTheory.PsiPrim.traceFormTwistIso_of_primitive_lineBundle | exact GlobalTheory.PsiPrim.traceFormTwistIso_of_primitive_lineBundle | (intros; apply GlobalTheory.PsiPrim.traceFormTwistIso_of_primitive_lineBundle <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsVeryAmpleH1Zero
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.MemPowOfFlatQuotient
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FlatThickenings

theorem mem_pow_of_flat_quotient {V C : Type} [CommRing V] [IsDomain V] [CommRing C] (σ : V →+* C)
    {ϖ : V} (hϖ : ϖ ≠ 0) (I : Ideal V) (hI : I = Ideal.span {ϖ}) (e : ℕ)
    (h : (Ideal.quotientMap ((I ^ (e + 1)).map σ) σ (Ideal.le_comap_map (I := I ^ (e + 1)))).Flat)
    {a : C} (ha : σ ϖ * a = 0) : a ∈ Ideal.span {σ ϖ} ^ e := by
  set φ := Ideal.quotientMap ((I ^ (e + 1)).map σ) σ (Ideal.le_comap_map (I := I ^ (e + 1))) with hφ
  let _ := φ.toAlgebra
  have : Module.Flat (V ⧸ I ^ (e + 1)) (C ⧸ (I ^ (e + 1)).map σ) := h
  have hsm : ∀ (v : V) (c : C), (Ideal.Quotient.mk (I ^ (e + 1)) v) •
      (Ideal.Quotient.mk ((I ^ (e + 1)).map σ) c) = Ideal.Quotient.mk _ (σ v * c) := by
    intro v c
    rw [Algebra.smul_def, map_mul]
    rfl
  obtain ⟨l, c, y, hy, hc⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero
    (R := V ⧸ I ^ (e + 1)) (M := C ⧸ (I ^ (e + 1)).map σ)
    (f := fun _ : Unit => Ideal.Quotient.mk _ ϖ) (x := fun _ => Ideal.Quotient.mk _ a)
    (by rw [Fintype.sum_unique, hsm, ha, map_zero])
  choose c' hc' using fun j => Ideal.Quotient.mk_surjective (c () j)
  choose y' hy' using fun j => Ideal.Quotient.mk_surjective (y j)
  have hd : ∀ j, ϖ ^ e ∣ c' j := by
    intro j
    have h1 := hc j
    rw [Fintype.sum_unique, ← hc', ← map_mul, Ideal.Quotient.eq_zero_iff_mem, hI,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton, pow_succ'] at h1
    exact (mul_dvd_mul_iff_left hϖ).1 h1
  have h2 : a - ∑ j, σ (c' j) * y' j ∈ (I ^ (e + 1)).map σ := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Ideal.Quotient.eq, map_sum]
    refine (hy ()).trans ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hc', ← hy', hsm]
  rw [hI, Ideal.map_pow, Ideal.map_span, Set.image_singleton] at h2
  have h3 : ∑ j, σ (c' j) * y' j ∈ Ideal.span {σ ϖ} ^ e := by
    refine Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ ?_
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, ← map_pow]
    exact map_dvd σ (hd j)
  simpa using Ideal.add_mem _ (Ideal.pow_le_pow_right (Nat.le_succ e) h2) h3

theorem flat_of_flat_quotient {V C : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [CommRing C] [IsNoetherianRing C] (σ : V →+* C)
    (h : ∀ e : ℕ, (Ideal.quotientMap ((IsLocalRing.maximalIdeal V ^ (e + 1)).map σ) σ
      (Ideal.le_comap_map (I := IsLocalRing.maximalIdeal V ^ (e + 1)))).Flat) : σ.Flat := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have key : ∀ a : C, σ ϖ * a = 0 → a = 0 := by
    intro a ha
    have hm : a ∈ ⨅ i : ℕ, (Ideal.span {σ ϖ} ^ i • ⊤ : Submodule C C) := by
      rw [Submodule.mem_iInf]
      intro e
      rw [smul_eq_mul, Ideal.mul_top]
      exact mem_pow_of_flat_quotient σ hϖ.ne_zero _ hϖ.maximalIdeal_eq e (h e) ha
    obtain ⟨⟨r, hr⟩, hra⟩ := (Ideal.mem_iInf_smul_pow_eq_bot_iff _ a).1 hm
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    rw [← hra]
    change c * σ ϖ * a = 0
    rw [_root_.mul_assoc, ha, mul_zero]
  have keyn : ∀ (n : ℕ) (a : C), σ ϖ ^ n * a = 0 → a = 0 := by
    intro n
    induction n with
    | zero => intro a ha; simpa using ha
    | succ n ih => intro a ha; exact key a (ih _ (by rw [← ha]; ring))
  let _ := σ.toAlgebra
  change Module.Flat V C
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
  rintro a ⟨⟨v, hv⟩, hva⟩
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (nonZeroDivisors.ne_zero hv) hϖ
  have h1 : σ (u * ϖ ^ n) * a = 0 := hva
  rw [map_mul, _root_.mul_assoc, map_pow] at h1
  exact keyn n a (((u.isUnit.map σ).mul_right_eq_zero).1 h1)

theorem flat_chart {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {B : Scheme.{0}} (f : B ⟶ Spec (CommRingCat.of V)) [LocallyOfFiniteType f]
    (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1)))))
    (b : ∀ e, (Y e).left ⟶ B)
    (hb : ∀ e, IsPullback (b e) (Y e).hom f (thick V (IsLocalRing.maximalIdeal V) e))
    (hY : ∀ e, Flat (Y e).hom) {C : CommRingCat.{0}} (u : Spec C ⟶ B) [IsOpenImmersion u] :
    Flat (u ≫ f) := by
  obtain ⟨σ, hσ⟩ := Spec.map_surjective (u ≫ f)
  have hft : LocallyOfFiniteType (Spec.map σ) := by rw [hσ]; infer_instance
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType.{0})] at hft
  have hN : IsNoetherianRing C := by
    let _ : Algebra V C := σ.hom.toAlgebra
    have : Algebra.FiniteType V C := hft
    exact Algebra.FiniteType.isNoetherianRing V C
  rw [← hσ, HasRingHomProperty.Spec_iff (P := @Flat.{0})]
  refine flat_of_flat_quotient σ.hom fun e => ?_
  have H := isPullback_SpecMap_of_isPushout _ _ _ _
    (NilpotentLift.isPushout_quotient_map (IsLocalRing.maximalIdeal V ^ (e + 1)) σ)
  have H' := (IsPullback.of_hasPullback (b e) u).flip.paste_vert (hb e)
  rw [← hσ] at H'
  have := hY e
  have hf : Flat ((H.isoIsPullback _ _ H').hom ≫ pullback.fst (b e) u ≫ (Y e).hom) := inferInstance
  rw [IsPullback.isoIsPullback_hom_snd, HasRingHomProperty.Spec_iff (P := @Flat.{0})] at hf
  exact hf

theorem flat_of_flat_thickenings :
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (B : Over (Spec (CommRingCat.of V))) [LocallyOfFiniteType B.hom] (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1))))) (b : ∀ e, (Y e).left ⟶ B.left), (∀ e, IsPullback (b e) (Y e).hom B.hom (thick V (IsLocalRing.maximalIdeal V) e)) → (∀ e, Flat (Y e).hom) → Flat B.hom := by
  intro V _ _ _ B _ Y b hb hY
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat.{0})
  exact IsZariskiLocalAtSource.of_openCover (P := @Flat) B.left.affineOpenCover.openCover
    fun i =>
      have : IsOpenImmersion (B.left.affineOpenCover.f i) := B.left.affineOpenCover.map_prop i
      flat_chart B.hom Y b hb hY (B.left.affineOpenCover.f i)

end GlobalTheory.FlatThickenings
end

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.Algebraise
variable {X Y : Scheme.{0}}

theorem res_res {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (u : Γ(X, U)ˣ) :
    res h₂ (res h₁ u) = res (h₂.trans h₁) u :=
  Units.ext (rs_rs h₁ h₂ u.val)

theorem pw_pw (H : LB X) (a b : ℤ) : AbLaw.pw (AbLaw.pw H a) b = AbLaw.pw H (a * b) := by
  exact congrArg (fun g => (⟨H.ι, H.U, g⟩ : LB X))
    (funext fun i => funext fun j => (zpow_mul (H.g i j) a b).symm)

theorem pw_pull (H : LB X) (f : Y ⟶ X) (a : ℤ) :
    (AbLaw.pw H a).pull f = AbLaw.pw (H.pull f) a := by
  have : ((AbLaw.pw H a).pull f).g = (AbLaw.pw (H.pull f) a).g := by
    funext j j'
    change (∏ k : PUnit, (res _ (pullU f _ (H.g (j k) (j' k) ^ a))) ^ (1 : ℤ)) =
      (∏ k : PUnit, (res _ (pullU f _ (H.g (j k) (j' k)))) ^ (1 : ℤ)) ^ a
    simp only [Fintype.prod_unique, zpow_one, map_zpow]
  exact congrArg (fun g => (⟨(H.pull f).ι, (H.pull f).U, g⟩ : LB Y)) this

theorem lbIso_pw {A B : LB X} (h : LBIso A B) (a : ℤ) : LBIso (AbLaw.pw A a) (AbLaw.pw B a) := by
  obtain ⟨w, hw⟩ := h
  refine ⟨⟨fun p => (w.s p) ^ a⟩, fun p q => ?_⟩
  have key : ∀ {G : Type} [CommGroup G] {x y z u : G}, x = y * z⁻¹ * u →
      x ^ a = y ^ a * (z ^ a)⁻¹ * u ^ a := by
    rintro G _ x y z u rfl
    rw [mul_zpow, mul_zpow, inv_zpow]
  change res _ (w.s p ^ a) = (res _ (B.g p.1 q.1 ^ a) * (res _ (A.g p.2 q.2 ^ a))⁻¹) * res _ (w.s q ^ a)
  rw [map_zpow, map_zpow, map_zpow, map_zpow]
  exact key (hw p q)

theorem cocycle_on {H : LB X} (hH : H.IsLB) (i j k : H.ι) {W : X.Opens} (hi : W ≤ H.U i)
    (hj : W ≤ H.U j) (hk : W ≤ H.U k) :
    res (le_inf hi hj) (H.g i j) * res (le_inf hj hk) (H.g j k) = res (le_inf hi hk) (H.g i k) := by
  have h := congrArg (res (le_inf (le_inf hi hj) hk : W ≤ H.U i ⊓ H.U j ⊓ H.U k)) (hH.cocycle i j k)
  simpa only [map_mul, res_res] using h

theorem rel_on {H : LB X} (hH : H.IsLB) (i k i' k' : H.ι) {W : X.Opens} (hi : W ≤ H.U i)
    (hk : W ≤ H.U k) (hi' : W ≤ H.U i') (hk' : W ≤ H.U k') :
    res (le_inf hi hk) (H.g i k) = res (le_inf hi hi') (H.g i i') * (res (le_inf hk hk') (H.g k k'))⁻¹ *
      res (le_inf hi' hk') (H.g i' k') := by
  rw [mul_right_comm, eq_mul_inv_iff_mul_eq, cocycle_on hH i k k' hi hk hk',
    cocycle_on hH i i' k' hi hi' hk']

theorem lbIso_tw {H : LB X} (hH : H.IsLB) (t : ℤ) : LBIso (AbLaw.pw H (t + 1)) (tw H H t) := _root_.GlobalTheory.AmpleNear.lbIso_tw (H := H) hH t

theorem exists_veryAmple_h1Zero (R : Type) [CommRing R] [IsNoetherianRing R]
    (B : Over (Spec (CommRingCat.of R))) (L : LB B.left) (hL : L.IsLB) (h : RelAmple B L) :
    ∃ d : ℕ, 1 ≤ d ∧ FirstCohomologyVanishes (AbLaw.pw L d) ∧
      ∃ (n : ℕ) (s : Fin (n + 1) → LB.Sec (AbLaw.pw L d)), VeryAmpleBy B.hom (AbLaw.pw L d) s := by
  obtain ⟨d₀, hd₀, n₀, s₀, hs₀⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy R B L hL).1 h
  have hH := isLB_pw hL (d₀ : ℤ)
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.AbLaw.serre_h1Zero_and_sections_polynomial.1 R B.left B.hom _ n₀ s₀ hH hs₀ _ hH
  have h1 := ht₀ (t₀.toNat : ℤ) (Int.self_le_toNat t₀)
  obtain ⟨w, hw⟩ := lbIso_tw hH (t₀.toNat : ℤ)
  have h2 := H1Iso.firstCohomologyVanishes_of_iso_of_isGen (isLB_tw hH hH _).cover (isLB_pw hH _) w hw h1
  have h3 := veryAmpleBy_pw R B.left B.hom _ n₀ s₀ hH hs₀ (t₀.toNat + 1) (Nat.le_add_left _ _)
  have e : AbLaw.pw (AbLaw.pw L (d₀ : ℤ)) ((t₀.toNat + 1 : ℕ) : ℤ) =
      AbLaw.pw L ((d₀ * (t₀.toNat + 1) : ℕ) : ℤ) := by
    rw [pw_pw, Nat.cast_mul]
  refine ⟨d₀ * (t₀.toNat + 1), Nat.mul_pos hd₀ (Nat.succ_pos _), ?_, ?_⟩
  · rw [← e, Nat.cast_add, Nat.cast_one]
    exact h2
  · rw [← e]
    exact h3

theorem algebraisation : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans V (IsLocalRing.maximalIdeal V) e)) → (∀ e, Flat (Y e).hom) → ∀ (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))), (∀ e, (N e).IsLB ∧ (v e).IsGen) → RelAmple (Y 0) (N 0) → ∃ (B : Over (Spec (CommRingCat.of V))) (M H : LB B.left) (b : ∀ e, (Y e).left ⟶ B.left) (n d : ℕ) (s : Fin (n + 1) → LB.Sec H), M.IsLB ∧ H.IsLB ∧ Flat B.hom ∧ VeryAmpleBy B.hom H s ∧ 1 ≤ d ∧ (∀ e, IsPullback (b e) (Y e).hom B.hom (thick V (IsLocalRing.maximalIdeal V) e)) ∧ (∀ e, β e ≫ b (e + 1) = b e) ∧ ∀ e, LBIso (N e) (M.pull (b e)) ∧ LBIso (pw (N e) d) (H.pull (b e)) := by
  intro V _ _ _ _ Y β hβ hY N v hN hA
  obtain ⟨d, hd, h0, n, s₀, hs₀⟩ := exists_veryAmple_h1Zero _ (Y 0) (N 0) (hN 0).1 hA
  have hv : ∀ e, LBIso (AbLaw.pw (N e) d) ((AbLaw.pw (N (e + 1)) d).pull (β e)) := fun e => by
    rw [pw_pull]
    exact lbIso_pw ⟨v e, (hN e).2⟩ d
  choose v' hv' using hv
  have hN' : ∀ e, (AbLaw.pw (N e) d).IsLB ∧ (v' e).IsGen := fun e => ⟨isLB_pw (hN e).1 d, hv' e⟩
  choose s hs0 hs using fun j => GlobalTheory.SecLifts.exists_compatible_sections V Y β hβ hY
    (fun e => AbLaw.pw (N e) d) v' hN' h0 (s₀ j)
  have hva : VeryAmpleBy (Y 0).hom (AbLaw.pw (N 0) d) (fun j => s j 0) := by
    have : (fun j => s j 0) = s₀ := funext hs0
    rw [this]
    exact hs₀
  obtain ⟨B, H, s', b, w, hH, hB, hb, hbβ, hw, -⟩ := GlobalTheory.Unif.exists_projective_of_formal_embedding V Y β hβ hY
    (fun e => AbLaw.pw (N e) d) v' hN' n (fun e j => s j e) (fun e j => hs j e) hva
  have hP : IsProjBy B.hom := ⟨H, hH, n, s', hB⟩
  have := isProper_of_isProjBy V B.left B.hom hP
  have hF : Flat B.hom := GlobalTheory.FlatThickenings.flat_of_flat_thickenings V B Y b hb hY
  obtain ⟨M, hM, hNM⟩ := GlobalTheory.LBAlg.exists_lineBundle_of_thickenings V Y β hβ B b hP hF hb hbβ N v hN
  exact ⟨B, M, H, b, n, d, s', hM, hH, hF, hB, hd, hb, hbβ, fun e => ⟨hNM e, w e, (hw e).1⟩⟩

end GlobalTheory.Algebraise
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.KTrivOfGeneric
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KTrivGeneric

theorem dominant_field (V : Type) [CommRing V] [IsDomain V] (F : Type) [Field F] [Algebra (FractionRing V) F] :
    IsSchemeTheoreticallyDominant (TF (R := V) F).hom := by
  have h₁ : IsDominant (jK V) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
      (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective V (FractionRing V))).le.trans bot_le)⟩
  have h₂ : IsDominant (jFK (R := V) F) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
      (((RingHom.injective_iff_ker_eq_bot _).1 (algebraMap (FractionRing V) F).injective).le.trans bot_le)⟩
  have h₃ : IsDominant (TF (R := V) F).hom := inferInstanceAs (IsDominant (jFK (R := V) F ≫ jK V))
  have h₄ : IsReduced (Spec (CommRingCat.of V)) := inferInstance
  exact IsSchemeTheoreticallyDominant.of_isDominant _

theorem kTriv_of_generic : GlobalFnsSt → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V] (B : Over (Spec (CommRingCat.of V))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ (L : RigLB B) (_ : CubicalStr B L), RelAmple B L.L → (∀ x : TF (R := V) (AlgebraicClosure (FractionRing V)) ⟶ B, InK B L.L x → x = 1) → KTriv B L.L := by
  intro hG V _ _ _ _ B _ _ hB L c hL hx
  have hLB : L.L.IsLB := L.isLB
  obtain ⟨d, -, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy V B L.L hLB).1 hL
  have hP : IsProjBy B.hom := ⟨_, isLB_pw hLB _, n, s, hs⟩
  obtain ⟨hO, hu, hK⟩ := GlobalTheory.UU.TrivTwist.inK_iff_trivial_twist _ B L.L hLB
  obtain ⟨H, j, hj, hH⟩ := GlobalTheory.T.exists_closed_subscheme_translation_kernel hG V B hB hP L.L (pw L.L 0) hLB hO
  have hfin : IsFinite H.hom :=
    GlobalTheory.AmpleStabFinite.isFinite_of_relAmple hG V B hB L.L (pw L.L 0) hLB hO hL H j hj hH
  have hflat : Flat H.hom := GlobalTheory.T.flat_kernelPolarisation_cosets_over_DVR hG V B hB hP L c (pw L.L 0) hO hu H j hj hH hfin
  have hrep : ∀ (T : Over (Spec (CommRingCat.of V))) (x : T ⟶ B), InK B L.L x ↔ ∃ y : T ⟶ H, y ≫ j = x :=
    fun T x => (hK _ rfl T x).trans (hH T x)
  have hm : Mono j := (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono j.left))
  have hchar : CharZero (AlgebraicClosure (FractionRing V)) := inferInstance
  have key := GlobalTheory.FiniteOnePoint.main _ B H j hm hfin ((hrep _ _).1 (inK_one hLB _))
    (fun T x y => (hrep _ _).1 (InK.mul hLB ((hrep _ _).2 ⟨x, rfl⟩) (InK.inv hLB ((hrep _ _).2 ⟨y, rfl⟩))))
    (AlgebraicClosure (FractionRing V)) (TF (R := V) (AlgebraicClosure (FractionRing V))).hom
    (fun x => hx _ ((hrep _ _).2 ⟨x, rfl⟩))
  have hd := dominant_field V (AlgebraicClosure (FractionRing V))
  have hsep : IsSeparated B.hom := by
    have := hB.proper
    infer_instance
  have hj1 : j = 1 := by
    let T := TF (R := V) (AlgebraicClosure (FractionRing V))
    have h1 : fst H T ≫ j = fst H T ≫ 1 := by
      rw [MonObj.comp_one]
      exact key (H ⊗ T) (snd H T) (fst H T)
    have h0 : QuasiCompact T.hom :=
      inferInstanceAs (QuasiCompact (jFK (R := V) (AlgebraicClosure (FractionRing V)) ≫ jK V))
    have h2 : IsSchemeTheoreticallyDominant (fst H T).left :=
      IsSchemeTheoreticallyDominant.of_isPullback (IsPullback.of_hasPullback H.hom T.hom).flip
    exact GlobalTheory.over_ext_of_schemeTheoreticallyDominant (fst H T).left (congrArg (fun q => q.left) h1)
  refine kTriv_iff_forall.2 fun T x hxK => ?_
  obtain ⟨y, rfl⟩ := (hrep T x).1 hxK
  rw [hj1, MonObj.comp_one]

end GlobalTheory.KTrivGeneric
end
