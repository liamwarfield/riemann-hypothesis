module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistSectionsLocallyGenerated

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PPhiQis
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem single_key {R : Type} [CommRing R] (Φ : Shv R ⥤ Shv R) [Φ.Additive] (F : Shv R) :
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (Φ.obj F)).inv ≫
      ((HomologicalComplex.singleMapHomologicalComplex Φ (ComplexShape.up ℤ) 0).inv.app F).f 0 =
    Φ.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv := by
  rw [HomologicalComplex.singleMapHomologicalComplex_inv_app_self]
  simp

theorem UpperTheory.Gal.TranscendenceTraces.phiQis_of :
    PhiQis := by
  intro R _ Φ _ hΦ F
  obtain ⟨-, -, -, hq, hι, -, -, -⟩ := GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R F
  haveI : Φ.PreservesHomology := (Φ.exact_tfae.out 2 3).1 hΦ
  let e := (HomologicalComplex.singleMapHomologicalComplex Φ (ComplexShape.up ℤ) 0).app F
  let φ : (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0 ⋙
      Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj F ⟶
      (Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj (res R F) :=
    (Φ.mapHomologicalComplex (ComplexShape.up ℤ)).map (resAug F)
  haveI hφ : QuasiIso φ :=
    (inferInstance : QuasiIso ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).map (resAug F)))
  haveI he : QuasiIso e.inv := inferInstance
  refine ⟨e.inv ≫ φ, quasiIso_comp e.inv φ, ?_⟩
  erw [HomologicalComplex.comp_f]
  rw [← Category.assoc]
  erw [single_key]
  exact (Φ.map_comp _ _).symm.trans (congrArg Φ.map hι)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PPtInj
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem q_smul_sec (q : ℕ) (i : ℤ) {V : Scheme.{0}} (t : Sec (tw q i) V) : q • t = 0 := by
  have h0 : ((q : ℕ) : ULift.{1} (ZMod q)) = 0 := by
    apply ULift.ext
    simp
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q)) q t, h0, zero_smul]

private theorem res_sub' {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (a b : Sec F U) :
    Sec.res g (a - b) = Sec.res g a - Sec.res g b := map_sub (F.obj.map g.op).hom a b

private theorem res_nsmul' {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (c : ℕ) (a : Sec F U) :
    Sec.res g (c • a) = c • Sec.res g a := map_nsmul (F.obj.map g.op).hom c a

private theorem sec_empty {R : Type} [CommRing R] (F : Shv R) {V : Scheme.{0}} [IsEmpty V] (a b : Sec F V) : a = b :=
  (GlobalTheory.T.etaleSheafSections_ext_and_glue R F V).1 a b ((GlobalTheory.T.etaleLocal_property_calculus_rules).2.2.2.2.2.2 V _)

theorem UpperTheory.Gal.TranscendenceTraces.ptInj_of :
    PtEx → PtInj := by
  intro hEx q _ i U b b' h
  have hy : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : gp Ω ⟶ U), Sec.res x (b - b') = 0 := by
    intro Ω _ _ x
    rw [res_sub', h Ω x, sub_self]
  refine (GlobalTheory.T.etaleSheafSections_ext_and_glue (ZMod q) (tw q i) U).1 b b' ?_
  refine (GlobalTheory.T.etaleLocal_property_calculus_rules).2.1 U _ _ ((GlobalTheory.T.tateTwist_sections_locally_generated q i).1 U (b - b')) ?_
  intro V g hg
  have key : Sec.res g (b - b') = 0 := by
    rcases hg with hg | ⟨ζ, c, hc⟩
    · exact hg
    · rcases isEmpty_or_nonempty V with hV | ⟨⟨v⟩⟩
      · exact sec_empty _ _ _
      · obtain ⟨Ω, _, _, x, -⟩ := hEx V v
        have h1 : c • twGen i (ζ.map x.appTop.hom) = 0 := by
          have h2 := hy Ω (x ≫ g)
          rw [← res_res, hc, res_nsmul', (GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.2.1] at h2
          exact h2
        haveI : Nonempty (gp Ω) := ⟨IsLocalRing.closedPoint Ω⟩
        obtain ⟨d, rfl⟩ := (GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.1 (gp Ω) _ c h1
        rw [hc, mul_nsmul', q_smul_sec]
  rw [res_sub'] at key
  exact sub_eq_zero.1 key
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PPhiUniv
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces
open scoped DirectSum Classical

namespace UpperTheory.Gal.TranscendenceTraces

private def famL {Q : ℕ} {Z S : Scheme.{0}} (p : Z ⟶ S) {G J : Shv (ZMod Q)} (t : Fam0 p G J)
    {U : Scheme.{0}} (u : U ⟶ S) : Sec G (pullback p u) →ₗ[ULift.{1} (ZMod Q)] Sec J U where
  toFun := t.app (Sq.of p u)
  map_add' := map_add _
  map_smul' c a := by
    obtain ⟨c⟩ := c
    obtain ⟨n, rfl⟩ := ZMod.intCast_surjective c
    have hc : (⟨(n : ZMod Q)⟩ : ULift.{1} (ZMod Q)) = ((n : ℤ) : ULift.{1} (ZMod Q)) :=
      ULift.ext (by simp)
    rw [hc, RingHom.id_apply, Int.cast_smul_eq_zsmul]
    exact (map_zsmul (t.app (Sq.of p u)) n a).trans (Int.cast_smul_eq_zsmul _ n _).symm

private def famS {Q : ℕ} {Z S : Scheme.{0}} (p : Z ⟶ S) {G J : Shv (ZMod Q)} (t : Fam0 p G J)
    (U : Scheme.{0}) : DS p G U →ₗ[ULift.{1} (ZMod Q)] Sec J U :=
  DirectSum.toModule _ _ _ fun u => famL p t u

private theorem famS_inc {Q : ℕ} {Z S : Scheme.{0}} (p : Z ⟶ S) {G J : Shv (ZMod Q)} (t : Fam0 p G J)
    {U : Scheme.{0}} (u : U ⟶ S) (a : Sec G (pullback p u)) :
    famS p t U (inc p G u a) = t.app (Sq.of p u) a :=
  DirectSum.toModule_lof _ _ _

private def famP {Q : ℕ} {Z S : Scheme.{0}} (p : Z ⟶ S) {G J : Shv (ZMod Q)} (t : Fam0 p G J) :
    phiP p G ⟶ J.obj where
  app U := ModuleCat.ofHom (famS p t U.unop)
  naturality U V g := ModuleCat.hom_ext (DS.hom_ext p fun u a => by
    change famS p t _ (DS.res p G g.unop (inc p G u a)) = Sec.res g.unop (famS p t _ (inc p G u a))
    rw [DS.res_inc p G g.unop u _ rfl, famS_inc, famS_inc]
    exact (t.nat (A := Sq.of p (g.unop ≫ u)) (B := Sq.of p u)
      ⟨g.unop, pbm p g.unop u _ rfl, rfl, pbm_fst .., pbm_snd ..⟩ a).symm)

theorem phiUniv_of : PhiUniv := by
  intro Q Z S p G J t
  obtain ⟨ψ, hψ, huniq⟩ := (GlobalTheory.T.etaleToSheafify_locally_bijective_and_lift (ZMod Q) (phiP p G)).2.2 J (famP p t)
  have key : ∀ (U : Scheme) (y : DS p G U), Sec.map ψ (phiSec p G U y) = famS p t U y := by
    intro U y
    exact congrArg (fun φ => ModuleCat.Hom.hom (φ.app (op U)) y) hψ
  refine ⟨ψ, fun A a => ?_, fun m hm => huniq m ?_⟩
  · change Sec.map ψ (phiSec p G A.U (inc p G A.u (Sec.res A.cmp a))) = _
    rw [key, famS_inc]
    have hn : Sec.res (𝟙 A.U) (t.app A a) = t.app (Sq.of p A.u) (Sec.res A.cmp a) :=
      t.nat (A := Sq.of p A.u) (B := A)
        ⟨𝟙 _, A.cmp, Category.id_comp _, A.cmp_v, A.cmp_r.trans (Category.comp_id _).symm⟩ a
    rw [res_id] at hn
    exact hn.symm
  · apply NatTrans.ext
    funext U
    apply ModuleCat.hom_ext
    apply DS.hom_ext p
    intro u a
    change Sec.map m (phiSec p G U.unop (inc p G u a)) = famS p t U.unop (inc p G u a)
    rw [← phiE_of]
    exact (hm (Sq.of p u) a).trans (famS_inc p t u a).symm

end UpperTheory.Gal.TranscendenceTraces

end
end
