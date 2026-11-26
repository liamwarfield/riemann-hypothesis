module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubicalSymmetricStructureOfGenericSymmetri
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieModelIsBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtTwoTorsionRationalPullbacks
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrderTwoTranslateEvenCubicalBundle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitCocycleLiftObstructionPullbackNaturality

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenTranslateOrderTwoTorus
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenTranslateTwoTorsionSplitClosedFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslateCubicalBundlePrincipalPolarisatio
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslateCubicalBundlePrincipalPolarisatio
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.GenTranslPkg

open GlobalTheory.RigidTranslate GlobalTheory.PolTranslate GlobalTheory.GenTransl

variable {R : Type} [CommRing R] [IsDomain R]

def genPoint (G : Over (Sp R)) (a : Over.mk (jK R) ⟶ G) :
    𝟙_ (Over (Sp (FractionRing R))) ⟶ (Over.pullback (jK R)).obj G :=
  Over.homMk (pullback.lift a.left (𝟙 _) (by rw [Category.id_comp]; exact Over.w a)) (pullback.lift_snd _ _ _)

theorem genPoint_fst (G : Over (Sp R)) (a : Over.mk (jK R) ⟶ G) :
    (genPoint G a).left ≫ pullback.fst G.hom (jK R) = a.left :=
  pullback.lift_fst _ _ _

set_option synthInstance.maxHeartbeats 200000 in
theorem one_left_fst (G : Over (Sp R)) [GrpObj G] (T : Over (Sp (FractionRing R))) :
    (1 : T ⟶ (Over.pullback (jK R)).obj G).left ≫ pullback.fst G.hom (jK R) =
      (1 : Over.mk (T.hom ≫ jK R) ⟶ G).left := by
  have H := isGrpPullback_pullback G (jK R)
  let c : Over.mk (T.hom ≫ jK R) ⟶ G :=
    Over.homMk ((1 : T ⟶ (Over.pullback (jK R)).obj G).left ≫ pullback.fst G.hom (jK R)) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      erw [Over.w (1 : T ⟶ (Over.pullback (jK R)).obj G)]
      rfl)
  have hc : c * c = c := by
    apply Over.OverMorphism.ext
    rw [H.2 T 1 1 c c rfl rfl, _root_.mul_one]
    rfl
  have : c = 1 := mul_eq_left.mp hc
  exact congrArg (fun q => q.left) this

set_option synthInstance.maxHeartbeats 200000 in
theorem genPoint_mul_self (G : Over (Sp R)) [GrpObj G] (a : Over.mk (jK R) ⟶ G) (ha : a * a = 1) :
    genPoint G a * genPoint G a = 1 := by
  have H := isGrpPullback_pullback G (jK R)
  let T := 𝟙_ (Over (Sp (FractionRing R)))
  let U : Over.mk (T.hom ≫ jK R) ⟶ Over.mk (jK R) := Over.homMk (𝟙 _) (by simp [T])
  have hx : (U ≫ a).left = (genPoint G a).left ≫ pullback.fst G.hom (jK R) := by
    rw [genPoint_fst, Over.comp_left]
    exact Category.id_comp _
  have e := H.2 T (genPoint G a) (genPoint G a) (U ≫ a) (U ≫ a) hx hx
  rw [← MonObj.comp_mul, ha, MonObj.comp_one] at e
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · rw [← e, one_left_fst]
  · erw [Over.w (genPoint G a * genPoint G a), Over.w (1 : T ⟶ (Over.pullback (jK R)).obj G)]

theorem transl_genPoint_fst (G : Over (Sp R)) [GrpObj G] (a : Over.mk (jK R) ⟶ G) :
    (PolTranslate.transl (genPoint G a)).left ≫ pullback.fst G.hom (jK R) = (genPr G * genPt G a).left := by
  have H := isGrpPullback_pullback G (jK R)
  refine (H.2 _ (𝟙 _) (toUnit _ ≫ genPoint G a) (genPr G) (genPt G a) ?_ ?_).symm
  · exact (Category.id_comp _).symm
  · show pullback.snd G.hom (jK R) ≫ a.left = _
    rw [Over.comp_left, Category.assoc, genPoint_fst]
    rfl

end GlobalTheory.GenTranslPkg


open GlobalTheory.RigidTranslate GlobalTheory.PolTranslate GlobalTheory.GenTransl GlobalTheory.GenTranslPkg in
theorem GlobalTheory.Mum.exists_transl_pkg : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (P : GlobalTheory.UU.CP G) (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) → ∀ a : Over.mk (jK R) ⟶ G, a * a = 1 → ∃ (P₁ : GlobalTheory.UU.CP G) (A₁ : PolAV (Sp (FractionRing R))) (gen₁ : (Over.pullback (jK R)).obj G ≅ A₁.A), IsMonHom gen₁.hom ∧ LBIso (A₁.L.pull gen₁.hom.left) (P₁.L.L.pull (pullback.fst G.hom (jK R))) ∧ LBIso (abelian₂ G P₁.L.L) (abelian₂ G P.L.L) ∧ GlobalTheory.GenTransl.IsGenTransl G P.L.L P₁.L.L a := by
  intro R _ _ _ hR G _ _ hG P A gen hgen hL a ha
  obtain ⟨hdvr, -, -⟩ := hR
  haveI := hdvr
  haveI := hG.smooth
  haveI := hG.separated
  haveI := hG.quasiCompact
  haveI : GeometricallyIntegral G.hom := @GlobalTheory.geometricallyIntegral_of_isSemiAbelian _ G _ hG
  haveI := A.isAb.comm
  haveI := A.isAb.proper
  let b := genPoint G a
  have hb : b * b = 1 := genPoint_mul_self G a ha
  let b' : 𝟙_ _ ⟶ A.A := b ≫ gen.hom
  have hb' : b' * b' = 1 := by
    show (b ≫ gen.hom) * (b ≫ gen.hom) = 1
    rw [← MonObj.mul_comp, hb, MonObj.one_comp]
  let L₁ : LB A.A.left := rigTransl A.L b'
  have hL₁ : L₁.IsLB := DVR.linComb_isLB _ A.isLB _ _
  let A₁ : PolAV (Sp (FractionRing R)) :=
    { A := A.A, isAb := A.isAb, g := A.g, smoothDim := A.smoothDim, L := L₁, isLB := hL₁,
      rigid := rigidified_rigTransl A.isLB, sym := sym_rigTransl hb' A.isLB A.sym,
      ample := relAmple_rigTransl hb' A.isLB A.ample, ktriv := kTriv_rigTransl hb' A.isLB A.ktriv }
  let LG := L₁.pull gen.hom.left
  have hLG : LG.IsLB := pull_isLB hL₁ _
  obtain ⟨L', hL', hLL'⟩ := GlobalTheory.T.lineBundle_generic_fibre_extends_over_dvr R G LG hLG
  have hpr : IsProper (pullback.snd G.hom (jK R)) := by
    have e : pullback.snd G.hom (jK R) = gen.hom.left ≫ A.A.hom := (Over.w gen.hom).symm
    have : IsIso gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map gen.hom))
    rw [e]; infer_instance
  have hsym : Out.Sym ((Over.pullback (jK R)).obj G) (L'.pull (pullback.fst G.hom (jK R))) :=
    GlobalTheory.T.symmetric_of_lineBundleIso_pull_groupHom _ _ _ gen.hom hgen L₁ _ hL₁ (pull_isLB hL' _) A₁.sym hLL'
  obtain ⟨P₁, hP₁⟩ := GlobalTheory.T.exists_cubicalSymmetricStructure_of_genericSymmetric R G hG hpr L' hL' hsym
  have hPL := P.L.isLB

  have htr : LBIso LG (P.L.L.pull (genPr G * genPt G a).left) := by
    haveI hU : Unique (Sp (FractionRing R)) := inferInstanceAs (Unique (PrimeSpectrum (FractionRing R)))
    let p0 : (𝟙_ (Over (Sp (FractionRing R)))).left := hU.default
    obtain ⟨i, hi⟩ := exists_chart A.isLB (b'.left p0)
    have h1 : LBIso LG (A.L.pull (gen.hom.left ≫ (PolTranslate.transl b').left)) :=
      lbIso_diff_pull A.isLB _ _ _ i fun z => by
        show b'.left ((gen.hom.left ≫ A.A.hom) z) ∈ A.L.U i
        have : (gen.hom.left ≫ A.A.hom) z = p0 := hU.uniq _
        rw [this]
        exact hi
    have e : gen.hom.left ≫ (PolTranslate.transl b').left = (PolTranslate.transl b).left ≫ gen.hom.left := by
      rw [← Over.comp_left, ← Over.comp_left, comp_transl, PolTranslate.transl, MonObj.mul_comp, Category.id_comp,
        Category.assoc]
    rw [e] at h1
    have h2 := GlobalTheory.ZM.SiegClause.lbIso_pull_pull (LBIso.symm hL) (PolTranslate.transl b).left
    have h3 := GlobalTheory.ZM.SiegClause.lbIso_pull_pull (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hPL (pullback.fst G.hom (jK R))))
      (PolTranslate.transl b).left
    rw [transl_genPoint_fst] at h3
    exact LBIso.trans hLG (pull_isLB A.isLB _) (pull_isLB hPL _) h1
      (LBIso.trans (pull_isLB A.isLB _) (pull_isLB (pull_isLB hPL _) _) (pull_isLB hPL _) (LBIso.symm h2) h3)

  have hext : ExtLam G LG (abelian₂ G P.L.L) := by
    refine ⟨DVR.linComb_isLB _ hPL _ _, fun κ₂ hκ => ?_⟩
    obtain ⟨c, hc⟩ := GlobalTheory.Moduli.cube_of_isLB _ A A.L A.isLB
    have e1 : LBIso (abelian₂ _ LG) ((abelian₂ A.A L₁).pull (gen.hom ⊗ₘ gen.hom).left) :=
      GlobalTheory.ZM.SiegClause.lbIso_lam_pull gen.hom hLG hL₁ (GlobalTheory.PolBaseChange.lbIso_refl hLG)
    have e2 : LBIso (abelian₂ _ (P.L.L.pull (pullback.fst G.hom (jK R))))
        ((abelian₂ A.A A.L).pull (gen.hom ⊗ₘ gen.hom).left) :=
      GlobalTheory.ZM.SiegClause.lbIso_lam_pull gen.hom (pull_isLB hPL _) A.isLB (LBIso.symm hL)
    have e3 := GlobalTheory.ZM.SiegClause.lbIso_pull_pull (lam_rigTransl (t := b') A.isLB c hc) (gen.hom ⊗ₘ gen.hom).left
    rw [Category.comp_id] at e3
    have e4 : LBIso (abelian₂ _ (P.L.L.pull (pullback.fst G.hom (jK R)))) ((abelian₂ G P.L.L).pull κ₂) :=
      GlobalTheory.LamPull.lbIso_lam_pull (isGrpPullback_pullback G (jK R)) hPL (pull_isLB hPL _)
        (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hPL _)) hκ
    have lb : ∀ {S : Scheme.{0}} (H : Over S) [GrpObj H] {M : LB H.left}, M.IsLB → (abelian₂ H M).IsLB :=
      fun _ _ _ h => DVR.linComb_isLB _ h _ _
    exact LBIso.trans (lb _ hLG) (pull_isLB (lb _ hL₁) _) (pull_isLB (lb _ hPL) _) e1
      (LBIso.trans (pull_isLB (lb _ hL₁) _) (pull_isLB (lb _ A.isLB) _) (pull_isLB (lb _ hPL) _) e3
        (LBIso.trans (pull_isLB (lb _ A.isLB) _) (lb _ (pull_isLB hPL _)) (pull_isLB (lb _ hPL) _)
          (LBIso.symm e2) e4))
  refine ⟨P₁, A₁, gen, hgen, ?_, ?_, ?_⟩
  · rw [hP₁]; exact hLL'
  · rw [hP₁]; exact GlobalTheory.T.lineBundleIso_mumford_of_generic_extension R G hG L' LG (abelian₂ G P.L.L) hL' hLG hLL' hext
  · show LBIso _ _
    rw [hP₁]
    exact LBIso.trans (pull_isLB hL' _) hLG (pull_isLB hPL _) (LBIso.symm hLL') htr
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslateCubicalBundlePrincipalPolarisatioStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_translateCubicalBundle_principalPolarisation : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (P : GlobalTheory.UU.CP G) (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) → ∀ a : Over.mk (jK R) ⟶ G, a * a = 1 → ∃ (P₁ : GlobalTheory.UU.CP G) (A₁ : PolAV (Sp (FractionRing R))) (gen₁ : (Over.pullback (jK R)).obj G ≅ A₁.A), IsMonHom gen₁.hom ∧ LBIso (A₁.L.pull gen₁.hom.left) (P₁.L.L.pull (pullback.fst G.hom (jK R))) ∧ LBIso (abelian₂ G P₁.L.L) (abelian₂ G P.L.L) ∧ GlobalTheory.GenTransl.IsGenTransl G P.L.L P₁.L.L a := by
  first | exact @GlobalTheory.Mum.exists_transl_pkg | exact GlobalTheory.Mum.exists_transl_pkg | (intros; apply GlobalTheory.Mum.exists_transl_pkg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrderTwoTranslateEvenCubicalBundleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orderTwo_translate_even_cubicalBundle : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → GlobalTheory.Mum.SplitClosed G → GlobalTheory.Mum.TwoTorsRat G → ∀ (P : GlobalTheory.UU.CP G) (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) → ∃ a : Over.mk (jK R) ⟶ G, a * a = 1 ∧ ∀ P₁ : GlobalTheory.UU.CP G, GlobalTheory.GenTransl.IsGenTransl G P.L.L P₁.L.L a → GlobalTheory.Mum.EvenOn P₁ := by
  first | exact @GlobalTheory.EvenTransl.exists_even_of_transl | exact GlobalTheory.EvenTransl.exists_even_of_transl | (intros; apply GlobalTheory.EvenTransl.exists_even_of_transl <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenTranslateTwoTorsionSplitClosedFibre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_even_translate_split : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → SplitClosed G → TwoTorsRat G → ∀ (P : GlobalTheory.UU.CP G) (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) → ∃ (P₁ : GlobalTheory.UU.CP G) (A₁ : PolAV (Sp (FractionRing R))) (gen₁ : (Over.pullback (jK R)).obj G ≅ A₁.A), IsMonHom gen₁.hom ∧ LBIso (A₁.L.pull gen₁.hom.left) (P₁.L.L.pull (pullback.fst G.hom (jK R))) ∧ LBIso (abelian₂ G P₁.L.L) (abelian₂ G P.L.L) ∧ EvenOn P₁ := by
  intro R _ _ _ hR G _ _ hG hS hT P A gen hgen hL
  obtain ⟨a, ha, hE⟩ := GlobalTheory.T.exists_orderTwo_translate_even_cubicalBundle R hR G hG hS hT P A gen hgen hL
  obtain ⟨P₁, A₁, gen₁, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_translateCubicalBundle_principalPolarisation R hR G hG P A gen hgen hL a ha
  exact ⟨P₁, A₁, gen₁, h1, h2, h3, hE P₁ h4⟩

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenTranslateTwoTorsionSplitClosedFibreStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_even_translate_two_torsion_split_closed_fibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → SplitClosed G → TwoTorsRat G → ∀ (P : GlobalTheory.UU.CP G) (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) → ∃ (P₁ : GlobalTheory.UU.CP G) (A₁ : PolAV (Sp (FractionRing R))) (gen₁ : (Over.pullback (jK R)).obj G ≅ A₁.A), IsMonHom gen₁.hom ∧ LBIso (A₁.L.pull gen₁.hom.left) (P₁.L.L.pull (pullback.fst G.hom (jK R))) ∧ LBIso (abelian₂ G P₁.L.L) (abelian₂ G P.L.L) ∧ EvenOn P₁ := by
  first | exact @GlobalTheory.Mum.exists_even_translate_split | exact GlobalTheory.Mum.exists_even_translate_split | (intros; apply GlobalTheory.Mum.exists_even_translate_split <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionSplitClosedFibreRationalTwo
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionSplitClosedFibreRationalTwo
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem splitClosed_of_isGrpPullback_id {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {G' G₁ : Over (Sp R)}
    [GrpObj G'] [GrpObj G₁] {φ : G₁.left ⟶ G'.left} (hφ : IsGrpPullback G₁ G' (𝟙 _) φ) (h : SplitClosed G') :
    SplitClosed G₁ := by
  obtain ⟨X, _, _, _, ⟨Q⟩⟩ := h
  let t := thick R (maximalIdeal R) 0
  have h2 := (isGrpPullback_pullback G₁ t).comp hφ
  have h3 := isGrpPullback_pullback G' t
  let ψ : (thickObj R (maximalIdeal R) 0 G₁).left ⟶ (thickObj R (maximalIdeal R) 0 G').left :=
    pullback.lift (pullback.fst G₁.hom t ≫ φ) (pullback.snd G₁.hom t) (by
      rw [Category.assoc, hφ.1.w, Category.comp_id, pullback.condition])
  have hc : IsGrpPullback (thickObj R (maximalIdeal R) 0 G₁) (thickObj R (maximalIdeal R) 0 G') (𝟙 _) ψ :=
    IsGrpPullback.cancel h3 (h2.congr (by rw [Category.comp_id, Category.id_comp]) (pullback.lift_fst _ _ _).symm)
      (by
        rw [Category.comp_id]
        exact pullback.lift_snd _ _ _)
  obtain ⟨Q', -⟩ := GlobalTheory.UU.exists_tq_baseChange _ _ (𝟙 _) X _ _ ψ hc Q
  exact ⟨X, inferInstance, inferInstance, inferInstance, ⟨Q'⟩⟩

noncomputable section

theorem exists_finExt_splitClosed_twoTorsRat : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R'), GlobalTheory.LN.CDvr R' ∧ FinExt ρ ∧ ∀ (G₁ : Over (Sp R')) [GrpObj G₁] [IsCommMonObj G₁] (β : G₁.left ⟶ G.left), IsGrpPullback G₁ G (spMap ρ) β → SplitClosed G₁ ∧ TwoTorsRat G₁ := by
  intro R _ _ _ hR G _ _ hG A gen hgen
  obtain ⟨K', _, _, hK'fin, H⟩ := GlobalTheory.T.exists_finite_ext_two_torsion_rational_pullbacks R G A gen hgen
  haveI : IsDiscreteValuationRing R := hR.1
  haveI : IsAdicComplete (maximalIdeal R) R := hR.2.1
  haveI : CharZero R := hR.2.2
  haveI : CharZero (FractionRing R) := (algebraMap R (FractionRing R)).charZero_iff (IsFractionRing.injective R _) |>.1 inferInstance
  obtain ⟨W, _, _, _, hWc, _, _, _, hc, hWfin, hWinj, hWloc, -, -⟩ :=
    GlobalTheory.SS.exists_complete_dvr_finite_extension R (FractionRing R) K'
  haveI : CharZero W := (algebraMap R W).charZero_iff hWinj |>.1 inferInstance
  have hWd : GlobalTheory.LN.CDvr W := ⟨inferInstance, hWc, inferInstance⟩
  have hGW : IsSemiAbelian ((Over.pullback (spMap (algebraMap R W))).obj G) := IsSemiAbelian.pullback _ G hG
  obtain ⟨R₂, _, _, _, ρ₂, G', _, _, β', X, _, _, _, hfin₂, hpb', ⟨Q⟩⟩ :=
    GlobalTheory.Mum.exists_finExt_tq_closedFibre W ⟨⟨inferInstance, inferInstance, inferInstance, hWc⟩, inferInstance⟩ _ hGW
  have hsp : spMap (ρ₂.comp (algebraMap R W)) = spMap ρ₂ ≫ spMap (algebraMap R W) := by
    rw [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  refine ⟨R₂, inferInstance, inferInstance, inferInstance, ρ₂.comp (algebraMap R W), GlobalTheory.T.isCompleteDVRCharZero_of_finiteInjectiveExtension W R₂ ρ₂ hWd hfin₂,
    ⟨hfin₂.1, hfin₂.2.1.comp hWinj, hfin₂.2.2.comp (RingHom.finite_algebraMap.2 hWfin)⟩, ?_⟩
  intro G₁ _ _ β hβ
  have hGWp := isGrpPullback_pullback G (spMap (algebraMap R W))
  let gam : G₁.left ⟶ ((Over.pullback (spMap (algebraMap R W))).obj G).left :=
    pullback.lift β (G₁.hom ≫ spMap ρ₂) (by rw [hβ.1.w, hsp, Category.assoc])
  have hgam : IsGrpPullback G₁ _ (spMap ρ₂) gam :=
    IsGrpPullback.cancel hGWp (hβ.congr hsp (pullback.lift_fst _ _ _).symm) (pullback.lift_snd _ _ _)
  obtain ⟨e, he, -⟩ := grpPullback_iso hgam hpb'
  haveI := he
  have hsplit' : SplitClosed G' := ⟨X, inferInstance, inferInstance, inferInstance, ⟨Q⟩⟩
  refine ⟨splitClosed_of_isGrpPullback_id (isGrpPullback_of_iso e) hsplit', ?_⟩
  · let j : FractionRing W →+* FractionRing R₂ :=
      IsLocalization.map (M := nonZeroDivisors W) (T := nonZeroDivisors R₂) (FractionRing R₂) ρ₂
        (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective ρ₂ hfin₂.2.1)
    let i : K' →+* FractionRing R₂ := j.comp (FractionRing.algEquiv W K').symm.toRingHom
    refine H R₂ (ρ₂.comp (algebraMap R W)) i (fun r => ?_) G₁ β hβ
    have h1 := congrArg (fun f => f r) hc
    simp only [RingHom.comp_apply] at h1
    rw [← h1]
    show j ((FractionRing.algEquiv W K').symm (algebraMap W K' (algebraMap R W r))) = _
    rw [AlgEquiv.commutes]
    exact IsLocalization.map_eq _ _

end

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionSplitClosedFibreRationalTwoStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteExtension_splitClosedFibre_rationalTwoTorsion : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R'), GlobalTheory.LN.CDvr R' ∧ FinExt ρ ∧ ∀ (G₁ : Over (Sp R')) [GrpObj G₁] [IsCommMonObj G₁] (β : G₁.left ⟶ G.left), IsGrpPullback G₁ G (spMap ρ) β → SplitClosed G₁ ∧ TwoTorsRat G₁ := by
  first | exact @GlobalTheory.Mum.exists_finExt_splitClosed_twoTorsRat | exact GlobalTheory.Mum.exists_finExt_splitClosed_twoTorsRat | (intros; apply GlobalTheory.Mum.exists_finExt_splitClosed_twoTorsRat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseChangeSemiAbelianCubicalPolarisedData
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseChangeSemiAbelianCubicalPolarisedData
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_baseChange_semiAbelian_data : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (P : GlobalTheory.UU.CP G) (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), GlobalTheory.LN.CDvr R' → FinExt ρ → ∃ (G₁ : Over (Sp R')) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (β : G₁.left ⟶ G.left) (β₂ : (G2 G₁).left ⟶ (G2 G).left) (P₁ : GlobalTheory.UU.CP G₁) (A₁ : PolAV (Sp (FractionRing R'))) (gen₁ : (Over.pullback (jK R')).obj G₁ ≅ A₁.A), IsSemiAbelian G₁ ∧ IsGrpPullback G₁ G (spMap ρ) β ∧ Geo.Tor.IsSquare β β₂ ∧ IsMonHom gen₁.hom ∧ LBIso (A₁.L.pull gen₁.hom.left) (P₁.L.L.pull (pullback.fst G₁.hom (jK R'))) ∧ LBIso (abelian₂ G₁ P₁.L.L) ((abelian₂ G P.L.L).pull β₂) := by
  intro R _ _ _ _ G _ _ hG P A gen hmon hext R' _ _ _ ρ _ hfin
  have hinj : Function.Injective ρ := hfin.2.1

  have gpG₁ : IsGrpPullback ((Over.pullback (spMap ρ)).obj G) G (spMap ρ) (pullback.fst G.hom (spMap ρ)) :=
    isGrpPullback_pullback G (spMap ρ)
  obtain ⟨β₂, hsq, hlam⟩ := lbIso_lam_pull_of_isGrpPullback _ _ (spMap ρ) G ((Over.pullback (spMap ρ)).obj G) _ gpG₁

  obtain ⟨rig, hr, c, s, h₁, h₂, h₃, -⟩ := GlobalTheory.UU.exists_isCPMap (hw := pullback.condition) P
    (GlobalTheory.UU.toBase_mul_pullback G (spMap ρ)) _ (pull_isLB P.L.isLB _) _ (GlobalTheory.UU.pullIso_isGen P.L.isLB _)
  let P₁ : GlobalTheory.UU.CP ((Over.pullback (spMap ρ)).obj G) :=
    ⟨⟨P.L.L.pull (pullback.fst G.hom (spMap ρ)), rig, pull_isLB P.L.isLB _, hr⟩, c, s, h₁, h₂, h₃⟩

  obtain ⟨A', gA, pA, dA, mA, tA⟩ := GlobalTheory.firstFiveLaws.1.polBaseChange _ _ (spMap (GlobalTheory.ArcPull.fracMap hinj)) A
  have gpA : IsGrpPullback A'.A A.A (spMap (GlobalTheory.ArcPull.fracMap hinj)) gA := ⟨pA, fun T x y x₀ y₀ hx hy => by
    have e₁ : x₀ = Out.toBase pA.w x := Over.OverMorphism.ext hx
    have e₂ : y₀ = Out.toBase pA.w y := Over.OverMorphism.ext hy
    rw [e₁, e₂, ← mA]; rfl⟩
  haveI := hmon
  haveI : IsMonHom gen.symm.hom := by show IsMonHom gen.inv; infer_instance
  have gpGen : IsGrpPullback A.A G (jK R) (gen.inv.left ≫ pullback.fst G.hom (jK R)) :=
    ((isGrpPullback_of_iso gen.symm).comp (isGrpPullback_pullback G (jK R))).congr (Category.id_comp _) rfl
  have sq : spMap (GlobalTheory.ArcPull.fracMap hinj) ≫ jK R = jK R' ≫ spMap ρ :=
    (GlobalTheory.ArcPull.fracMap_sq hinj).symm.trans (Category.id_comp _)
  have gp' : IsGrpPullback ((Over.pullback (jK R')).obj ((Over.pullback (spMap ρ)).obj G)) G
      (spMap (GlobalTheory.ArcPull.fracMap hinj) ≫ jK R)
      (pullback.fst ((Over.pullback (spMap ρ)).obj G).hom (jK R') ≫ pullback.fst G.hom (spMap ρ)) :=
    ((isGrpPullback_pullback ((Over.pullback (spMap ρ)).obj G) (jK R')).comp gpG₁).congr sq.symm rfl
  obtain ⟨eA, mE, heA⟩ := grpPullback_iso gp' (gpA.comp gpGen)
  refine ⟨(Over.pullback (spMap ρ)).obj G, inferInstance, inferInstance, pullback.fst G.hom (spMap ρ), β₂, P₁, A', eA,
    IsSemiAbelian.pullback _ G hG, gpG₁, hsq, mE, ?_, ?_⟩
  · refine LBIso.trans (pull_isLB A'.isLB _) (pull_isLB (pull_isLB A.isLB gA) eA.hom.left)
      (pull_isLB (pull_isLB P.L.isLB _) _)
      ((LBIso.symm tA).chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull A'.L _ _ rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (A.L.pull gA) _ _ rfl)) ?_
    have hgi : gen.inv.left ≫ gen.hom.left = 𝟙 _ := by
      rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
    refine LBIso.chartPull (h := eA.hom.left ≫ gA ≫ gen.inv.left)
      (chartPullLinComb A.L gA (fun _ => eA.hom.left) (fun _ => gen.hom.left) _ _ fun _ => ?_)
      (chartPullLinComb P.L.L (pullback.fst G.hom (spMap ρ))
        (fun _ => pullback.fst ((Over.pullback (spMap ρ)).obj G).hom (jK R'))
        (fun _ => pullback.fst G.hom (jK R)) _ _ fun _ => ?_) hext
    · rw [Category.assoc, Category.assoc, hgi, Category.comp_id]
    · rw [← heA]; simp only [Category.assoc]
  · have hL := P.L.isLB
    have h := hlam P.L.L (P.L.L.pull (pullback.fst G.hom (spMap ρ))) _ (abelian₂ G P.L.L) (𝟙 _) hL (pull_isLB hL _)
      (LB.isLB_linComb hL _ _) (lbIso_refl (pull_isLB hL _)) (LBIso.symm (lbIso_pull_id (LB.isLB_linComb hL _ _)))
    rwa [Category.comp_id] at h

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseChangeSemiAbelianCubicalPolarisedDataStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_baseChange_semiAbelian_cubical_polarised_data : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (P : GlobalTheory.UU.CP G) (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), GlobalTheory.LN.CDvr R' → FinExt ρ → ∃ (G₁ : Over (Sp R')) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (β : G₁.left ⟶ G.left) (β₂ : (G2 G₁).left ⟶ (G2 G).left) (P₁ : GlobalTheory.UU.CP G₁) (A₁ : PolAV (Sp (FractionRing R'))) (gen₁ : (Over.pullback (jK R')).obj G₁ ≅ A₁.A), IsSemiAbelian G₁ ∧ IsGrpPullback G₁ G (spMap ρ) β ∧ Geo.Tor.IsSquare β β₂ ∧ IsMonHom gen₁.hom ∧ LBIso (A₁.L.pull gen₁.hom.left) (P₁.L.L.pull (pullback.fst G₁.hom (jK R'))) ∧ LBIso (abelian₂ G₁ P₁.L.L) ((abelian₂ G P.L.L).pull β₂) := by
  first | exact @GlobalTheory.Mum.exists_baseChange_semiAbelian_data | exact GlobalTheory.Mum.exists_baseChange_semiAbelian_data | (intros; apply GlobalTheory.Mum.exists_baseChange_semiAbelian_data <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenTranslateOrderTwoTorus
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_even_translate : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (P : GlobalTheory.UU.CP G) (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (G₁ : Over (Sp R')) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (β : G₁.left ⟶ G.left) (β₂ : (G2 G₁).left ⟶ (G2 G).left) (P₁ : GlobalTheory.UU.CP G₁) (A₁ : PolAV (Sp (FractionRing R'))) (gen₁ : (Over.pullback (jK R')).obj G₁ ≅ A₁.A), GlobalTheory.LN.CDvr R' ∧ FinExt ρ ∧ IsGrpPullback G₁ G (spMap ρ) β ∧ Geo.Tor.IsSquare β β₂ ∧ IsMonHom gen₁.hom ∧ LBIso (A₁.L.pull gen₁.hom.left) (P₁.L.L.pull (pullback.fst G₁.hom (jK R'))) ∧ LBIso (abelian₂ G₁ P₁.L.L) ((abelian₂ G P.L.L).pull β₂) ∧ EvenOn P₁ := by
  intro R _ _ _ hR G _ _ hG P A gen hgen hL
  obtain ⟨R', _, _, _, ρ, hR', hρ, hall⟩ := GlobalTheory.T.exists_finiteExtension_splitClosedFibre_rationalTwoTorsion R hR G hG A gen hgen
  obtain ⟨G₁, _, _, β, β₂, P₁, A₁, gen₁, hG₁, hpb, hsq, hgen₁, hL₁, hLam₁⟩ :=
    GlobalTheory.T.exists_baseChange_semiAbelian_cubical_polarised_data R hR G hG P A gen hgen hL R' ρ hR' hρ
  obtain ⟨hsp, htw⟩ := hall G₁ β hpb
  obtain ⟨P₂, A₂, gen₂, hgen₂, hL₂, hLam₂, hev⟩ := GlobalTheory.T.exists_even_translate_two_torsion_split_closed_fibre R' hR' G₁ hG₁ hsp htw P₁ A₁ gen₁ hgen₁ hL₁
  refine ⟨R', inferInstance, inferInstance, inferInstance, ρ, G₁, inferInstance, inferInstance, β, β₂, P₂, A₂, gen₂,
    hR', hρ, hpb, hsq, hgen₂, hL₂, ?_, hev⟩
  exact LBIso.trans (LB.isLB_linComb P₂.L.isLB _ _) (LB.isLB_linComb P₁.L.isLB _ _)
    (pull_isLB (LB.isLB_linComb P.L.isLB _ _) _) hLam₂ hLam₁

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenTranslateOrderTwoTorusStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_even_translate_order_two_torus : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (P : GlobalTheory.UU.CP G) (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (G₁ : Over (Sp R')) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (β : G₁.left ⟶ G.left) (β₂ : (G2 G₁).left ⟶ (G2 G).left) (P₁ : GlobalTheory.UU.CP G₁) (A₁ : PolAV (Sp (FractionRing R'))) (gen₁ : (Over.pullback (jK R')).obj G₁ ≅ A₁.A), GlobalTheory.LN.CDvr R' ∧ FinExt ρ ∧ IsGrpPullback G₁ G (spMap ρ) β ∧ Geo.Tor.IsSquare β β₂ ∧ IsMonHom gen₁.hom ∧ LBIso (A₁.L.pull gen₁.hom.left) (P₁.L.L.pull (pullback.fst G₁.hom (jK R'))) ∧ LBIso (abelian₂ G₁ P₁.L.L) ((abelian₂ G P.L.L).pull β₂) ∧ EvenOn P₁ := by
  first | exact @GlobalTheory.Mum.exists_even_translate | exact GlobalTheory.Mum.exists_even_translate | (intros; apply GlobalTheory.Mum.exists_even_translate <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisationFiniteExtSameMumfordBundle
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.UExt

theorem lam_isLB {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] {L : LB G.left} (hL : L.IsLB) :
    (abelian₂ G L).IsLB :=
  DVR.linComb_isLB L hL _ _

theorem lbIso_pull {X Y : Scheme.{0}} {P Q : LB X} (h : LBIso P Q) (f : Y ⟶ X) : LBIso (P.pull f) (Q.pull f) :=
  h.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull P f f rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull Q f f rfl)

end GlobalTheory.Mum.UExt


open GlobalTheory.Mum.UExt in
theorem GlobalTheory.Mum.exists_unif_finExt_lam : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∀ PP : LB (G2 G).left, ExtLam G (A.L.pull gen.hom.left) PP → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (D₁ : DegData R' (maximalIdeal R')) (G₁ : Over (Sp R')) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (β : G₁.left ⟶ G.left) (β₂ : (G2 G₁).left ⟶ (G2 G).left) (A₁ : PolAV (Sp (FractionRing R'))) (U₁ : Unif (maximalIdeal R') D₁ A₁ G₁), GlobalTheory.LN.CDvr R' ∧ FinExt ρ ∧ IsGrpPullback G₁ G (spMap ρ) β ∧ Geo.Tor.IsSquare β β₂ ∧ LBIso (abelian₂ G₁ U₁.LG.L) (PP.pull β₂) := by
  intro R _ _ _ hR G _ _ hG A gen hgen PP hPP
  obtain ⟨hdvr, hcomp, hchar⟩ := hR
  haveI := hG.smooth
  haveI := hG.separated
  haveI := hG.quasiCompact
  haveI : GeometricallyIntegral G.hom := @GlobalTheory.geometricallyIntegral_of_isSemiAbelian _ G _ hG
  have hL : (A.L.pull gen.hom.left).IsLB := LB.isLB_pull A.isLB _
  obtain ⟨L', hL', hLL'⟩ := GlobalTheory.T.lineBundle_generic_fibre_extends_over_dvr R G (A.L.pull gen.hom.left) hL
  have hpr : IsProper (pullback.snd G.hom (jK R)) := by
    have := A.isAb.proper
    have e : pullback.snd G.hom (jK R) = gen.hom.left ≫ A.A.hom := (Over.w gen.hom).symm
    have : IsIso gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map gen.hom))
    rw [e]; infer_instance
  have hsym : Out.Sym ((Over.pullback (jK R)).obj G) (L'.pull (pullback.fst G.hom (jK R))) :=
    GlobalTheory.T.symmetric_of_lineBundleIso_pull_groupHom _ _ _ gen.hom hgen A.L _ A.isLB (LB.isLB_pull hL' _) A.sym hLL'
  obtain ⟨P, hP⟩ := GlobalTheory.T.exists_cubicalSymmetricStructure_of_genericSymmetric R G hG hpr L' hL' hsym
  subst hP
  obtain ⟨R', _, _, _, ρ, G₁, _, _, β, β₂, P₁, A₁, gen₁, hR', hρ, hβ, hsq, hgen₁, hL₁, hLam, hEven⟩ :=
    GlobalTheory.T.exists_even_translate_order_two_torus R ⟨hdvr, hcomp, hchar⟩ G hG P A gen hgen hLL'
  have hB' : Base R' := ⟨hρ.1, @charZero_of_injective_ringHom _ _ _ _ ρ hρ.2.1 hchar⟩
  have hG₁ : IsSemiAbelian G₁ := by
    obtain ⟨bc, mbc, -⟩ := grpPullback_iso hβ (isGrpPullback_pullback G (spMap ρ))
    exact GlobalTheory.isSemiAbelian_of_grpIso bc (Geo.Tor.IsSemiAbelian.pullback (spMap ρ) G hG)
  obtain ⟨D, U, hU, -⟩ := GlobalTheory.T.exists_uniformisation_completeLocal_evenOnTorus R' hB' G₁ P₁ hG₁ hEven A₁ gen₁ hgen₁ hL₁
  have hE : LBIso (abelian₂ G P.L.L) PP := GlobalTheory.T.lineBundleIso_mumford_of_generic_extension R G hG P.L.L _ PP P.L.isLB hL hLL' hPP
  refine ⟨R', _, _, _, ρ, D, G₁, _, _, β, β₂, A₁, U, hR', hρ, hβ, hsq, ?_⟩
  rw [hU]
  exact LBIso.trans (lam_isLB G₁ P₁.L.isLB) (LB.isLB_pull (lam_isLB G P.L.isLB) _) (LB.isLB_pull hPP.1 _) hLam
    (lbIso_pull hE β₂)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisationFiniteExtSameMumfordBundleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformisation_finiteExt_sameMumfordBundle : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∀ PP : LB (G2 G).left, ExtLam G (A.L.pull gen.hom.left) PP → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (D₁ : DegData R' (maximalIdeal R')) (G₁ : Over (Sp R')) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (β : G₁.left ⟶ G.left) (β₂ : (G2 G₁).left ⟶ (G2 G).left) (A₁ : PolAV (Sp (FractionRing R'))) (U₁ : Unif (maximalIdeal R') D₁ A₁ G₁), GlobalTheory.LN.CDvr R' ∧ FinExt ρ ∧ IsGrpPullback G₁ G (spMap ρ) β ∧ Geo.Tor.IsSquare β β₂ ∧ LBIso (abelian₂ G₁ U₁.LG.L) (PP.pull β₂) := by
  first | exact @GlobalTheory.Mum.exists_unif_finExt_lam | exact GlobalTheory.Mum.exists_unif_finExt_lam | (intros; apply GlobalTheory.Mum.exists_unif_finExt_lam <;> assumption)
end
