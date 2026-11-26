module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FamilyUniformisationOfAbelianSchemeLaws
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueHomExtensionSemiAbelianNormal
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoefficientFieldIntegersDedekindFractionField
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.IsQProjOverOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSemiAbelianDescentTameQuotient
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DualNumberRingHomExt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionIdentificationWithPairing
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueHomExtensionSemiAbelian
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpSeriesCoeffNormBoundedRingLaws
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.TateUniformizationInput
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PsiGenOnInteriorOfPsiUnitOn
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGtExtOfTorsion
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.DeltaIsGreatest
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionsCountSqEqDetFormOnTorsion

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModuliConsequenceOfAbelianSchemeLaws
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModuliConsequenceOfAbelianSchemeLaws
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem _root_.GlobalTheory.closing_of_abelianSchemeLaws : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.N1c :=
  _root_.GlobalTheory.familyUnif_of_laws _root_.GlobalTheory.abelianSchemeLaws_all.1

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModuliConsequenceOfAbelianSchemeLawsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmModuli_consequence_of_abelianSchemeLaws : N1c := by
  first | exact @GlobalTheory.closing_of_abelianSchemeLaws | exact GlobalTheory.closing_of_abelianSchemeLaws | (intros; apply GlobalTheory.closing_of_abelianSchemeLaws <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabMapIdOfCommonGeneric
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory
namespace TripleExt

theorem exists_hom {X U : Scheme.{0}} {j : U ⟶ X} {G G' : Over X} [GrpObj G] [GrpObj G'] {G₀ : Over U} [GrpObj G₀]
    {φ : G₀.left ⟶ G.left} {φ' : G₀.left ⟶ G'.left} (h : IsGrpPullback G₀ G j φ) (h' : IsGrpPullback G₀ G' j φ')
    (hx : ∀ f : (Over.pullback j).obj G ⟶ (Over.pullback j).obj G', IsMonHom f →
      ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback j).map F = f) :
    ∃ F : G ⟶ G', IsMonHom F ∧ φ ≫ F.left = φ' := by
  obtain ⟨e, he, hφ⟩ := grpPullback_iso h (isGrpPullback_pullback G j)
  obtain ⟨e', he', hφ'⟩ := grpPullback_iso h' (isGrpPullback_pullback G' j)
  obtain ⟨F, ⟨hF, hFf⟩, -⟩ := hx (e.inv ≫ e'.hom) inferInstance
  refine ⟨F, hF, ?_⟩
  rw [← hφ, Category.assoc, ← ExtUnique.pullback_map_left_fst j F, hFf, ← Category.assoc, ← Over.comp_left,
    e.hom_inv_id_assoc, hφ']

end TripleExt
end GlobalTheory

theorem GlobalTheory.exists_sabMap_id_of_common_generic : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X U : Scheme.{0}) (j : U ⟶ X), (Geo.Tor.IsNormalScheme X ∧ ∃ z : X ⟶ Sp ℤ, LocallyOfFiniteType z ∧ Flat z) → IsPreimmersion j → Flat j → IsDominant j → QuasiCompact j → ∀ (t₀ : SAB H U) (t t' : SAB H X) (a : SABMap t₀ t j) (a' : SABMap t₀ t' j), IsProper t₀.G.hom → ∃ b : SABMap t t' (𝟙 X), a.φ ≫ b.φ = a'.φ := by
  intro hdvr E _ _ _ H X U j hX hj₁ hj₂ hj₃ hj₄ t₀ t t' a a' hp
  obtain ⟨hgen, -, hdom, -⟩ := densePart_basic X U j hj₁ hj₂ hj₃ hj₄
  have hred : IsReduced X := by
    have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
      have := (hX.1 x).1
      infer_instance
    exact isReduced_of_isReduced_stalk X
  have hnoeth : IsLocallyNoetherian X := by
    obtain ⟨z, hz, -⟩ := hX.2
    exact LocallyOfFiniteType.isLocallyNoetherian z
  have := hdom hred
  obtain ⟨_, _⟩ := ExtUnique.flat_and_isSeparated_of_isSemiAbelian t.G t.semi
  obtain ⟨_, _⟩ := ExtUnique.flat_and_isSeparated_of_isSemiAbelian t'.G t'.semi
  obtain ⟨F, hF, hφ⟩ := TripleExt.exists_hom a.cart a'.cart
    (GlobalTheory.T.existsUnique_hom_extension_semiAbelian_normal_base_alt hdvr X U j hX hj₁ hj₂ hj₃ hj₄ t.G t'.G t.semi t'.semi)
  obtain ⟨F', -, hφ'⟩ := TripleExt.exists_hom a'.cart a.cart
    (GlobalTheory.T.existsUnique_hom_extension_semiAbelian_normal_base_alt hdvr X U j hX hj₁ hj₂ hj₃ hj₄ t'.G t.G t'.semi t.semi)
  have hiso : IsIso F := ExtUnique.isIso_of_isPullback a.cart.1 a'.cart.1 (Iso.refl _) F F'
    ((Category.id_comp _).trans hφ.symm) ((Category.id_comp _).trans hφ'.symm)
  have gp : IsGrpPullback t.G t'.G (𝟙 X) F.left :=
    haveI : IsMonHom (asIso F).hom := hF
    isGrpPullback_of_iso (asIso F)
  have hact : ∀ x, (t.act.act x).left ≫ F.left = F.left ≫ (t'.act.act x).left := fun x => by
    have : t.act.act x ≫ F = F ≫ t'.act.act x := ExtUnique.over_hom_ext_of_isPullback a.cart.1 (by
      rw [Over.comp_left, Over.comp_left, ← Category.assoc, ← a.act, Category.assoc, hφ, ← Category.assoc, hφ,
        a'.act])
    exact congrArg (fun z => z.left) this
  have hlb : LBIso t.PP.L (t'.PP.L.pull F.left) := by
    obtain ⟨w, hw, -⟩ := (isPullCubical_iff _ _ _).1 a.lin
    obtain ⟨w', hw', -⟩ := (isPullCubical_iff _ _ _).1 a'.lin
    have hw'' : ∃ w'' : LB.Iso t₀.PP.L (t'.PP.L.pull (a.cm.F ≫ F.left)), PGen w'' := by
      rw [hφ]; exact ⟨w', hw'⟩
    obtain ⟨w'', hw''⟩ := hw''
    obtain ⟨r, hr, -⟩ := Exist.CubicalExtension.exists_quot_of_isos t'.PP.isLB t.PP.isLB t₀.PP.isLB w w'' hw hw''
      a.cart.1.isoPullback.inv (pullback.fst t.G.hom j) a.cart.1.isoPullback_inv_fst
    obtain ⟨ρ, hρ, -⟩ := Exist.CubicalExtension.exists_quot_of_gens (CubeMap.ofHom F).e_comm t'.PP.rig t.PP.rig
      t'.PP.rigGen t.PP.rigGen
    have sm := t.semi.smooth
    have gc := t.semi.geomConnected
    exact GlobalTheory.T.exists_lineBundleGenerator_extending_densePart X U j hX.1 hj₁ hj₂ hj₃ hj₄ t.G (eSec t.G) (LB.div (t'.PP.L.pull F.left) t.PP.L) (Over.w η[t.G])
      sm (grpObj_geometricallyIntegral_of_smooth X t.G) (LB.isLB_div (LB.isLB_pull t'.PP.isLB _) t.PP.isLB) ⟨ρ, hρ⟩ ⟨r, hr⟩
  obtain ⟨b, hb⟩ := exists_sabMap_of_lbIso E H X X t' t (𝟙 X) F.left
    ⟨hred, hgen.trans (range_subset_abLocus_of_isProper t.semi a.cart.1)⟩ gp hact hlb
  exact ⟨b, by rw [hb]; exact hφ⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabDescentOfFieldExtension
noncomputable section

namespace GlobalTheory.ModelRelCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ModelCompare GlobalTheory.Models

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

section Dominates

variable {O' : Type} [CommRing O'] {β' : O' →+* c.F} (Y : Model Xo c β) (Y' : Model Xo c β') (b : O →+* O')
  (hb : β'.comp b = β)

end Dominates

section Dense

variable (Y : Model Xo c β)

theorem densePart (h : IsDedFrac β) : IsLocallyNoetherian Y.X ∧ IsReduced Y.X ∧ Y.X.IsSeparated ∧
    IsPreimmersion Y.j ∧ Flat Y.j ∧ IsDominant Y.j ∧ QuasiCompact Y.j := by
  obtain ⟨⟨_, _⟩, -, hfr⟩ := h
  letI := β.toAlgebra
  obtain ⟨h₁, -, h₂, h₃⟩ :=
    GlobalTheory.genericPart_dense_proOpen O c.F Y.X _ Y.s Y.jQ Y.flat Y.proj Y.jQ_open Y.jQ_dense
  have : ∀ x : Y.X, _root_.IsReduced (Y.X.presheaf.stalk x) := fun x ↦
    have := (Y.normal x).1
    inferInstance
  exact ⟨h₁, isReduced_of_isReduced_stalk Y.X, h₂, h₃⟩

end Dense

section Transition

variable {l₂ : Level H} {Xo₂ : Moduli D l₂} {c₂ : Coeff l₂} {O₂ : Type} [CommRing O₂] {β₂ : O₂ →+* c₂.F}
  (Y : Model Xo c β) (Y₂ : Model Xo₂ c₂ β₂) (hl : l.Dvd l₂) (hF : c.F ≤ c₂.F) (b : O →+* O₂)
  (hb : β₂.comp b = (IntermediateField.inclusion hF).toRingHom.comp β) (π : Y₂.X ⟶ Y.X)

end Transition

section Algebra

end Algebra

section Action

variable (Y : Model Xo c β)

variable {Y}

variable (Y)

end Action

end GlobalTheory.ModelRelCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBaseChangeUniformization
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TorsionFormCompare
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.TorsionFormCompare

open UnifBaseChange ExpandsLinear in
theorem exists_unif_pull_of_deg (hP : PolBaseChangeSt) (hG : GlobalFnsSt) (hS : SecBaseChangeSt)
    (hT : DVR.TwistBaseChangeStatement)
    (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R)
    (I' : Ideal R') (hR : AdmBase R I) (hR' : AdmBase R' I') (φ : R →+* R') (hI : I.map φ ≤ I')
    (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R))))
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (hsa : IsSemiAbelian G)
    (U : Unif I D A G) (D' : DegData R' I') (hD : IsPullDeg φ D.toPre D'.toPre) (hgD : D'.toPre.P.g = D.toPre.P.g)
    (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G']
    (bc : G' ≅ (Over.pullback (specOf φ)).obj G) (hbc : IsMonHom bc.hom)
    (A' : PolAV (Spec (CommRingCat.of (FractionRing R')))) (hg : A'.g = A.g)
    (eA : (Over.pullback (jK R')).obj G' ≅ A'.A) (heA : IsMonHom eA.hom)
    (hwA : ∃ wA : LB.Iso (A'.L.pull eA.hom.left)
      (U.LG.L.pull (pullback.fst G'.hom (jK R') ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ))), wA.IsGen)
    (L' : RigLB G') (wL : LB.Iso L'.L (U.LG.L.pull (bc.hom.left ≫ pullback.fst G.hom (specOf φ))))
    (he : eSec G' ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ) = specOf φ ≫ eSec G)
    (hwL : wL.IsGen)
    (hrig : LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G') (fun _ => 1)) L'.rig
      (rigPullOf (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) (specOf φ) he U.LG.L U.LG.rig)) :
    ∃ U' : Unif I' D' A' G', U'.LG = L' ∧ U'.gen = eA ∧ IsPullUnif φ hD bc U U' := by
  obtain ⟨U', wL', hL, hgen, hw, hlev⟩ := exists_unifPre_pull hG R R' I I' φ D D' hD A A' G G' bc hI hbc
    U.toUnifPre eA heA hwA L' wL he hwL hrig
  subst hL
  obtain rfl := eq_of_heq hw
  haveI := hsa.geomConnected
  haveI := hsa.quasiCompact
  haveI : GeometricallyConnected G'.hom := by
    rw [← Over.w bc.hom]
    have : IsIso bc.hom.left := ((Over.forget _).mapIso bc).isIso_hom
    have : GeometricallyConnected ((Over.pullback (specOf φ)).obj G).hom :=
      inferInstanceAs (GeometricallyConnected (pullback.snd G.hom (specOf φ)))
    exact MorphismProperty.of_isPullback (P := @GeometricallyConnected)
      (IsPullback.of_horiz_isIso (fst := bc.hom.left) (f := ((Over.pullback (specOf φ)).obj G).hom) (g := 𝟙 _)
        ⟨(Category.comp_id _).symm⟩) this
  haveI := hR.1
  haveI := hR'.1
  have hexp : ∀ k : ℕ, 1 ≤ k → U'.ExpBij k := by
    intro k hk
    obtain ⟨-, hd⟩ := FamDim.finrank_fam hG hP hT R D.toPre D.tau_bimult (psiOnExists R I hR D) (FractionRing R) k hk
    obtain ⟨hfin, hd'⟩ := FamDim.finrank_fam hG hP hT R' D'.toPre D'.tau_bimult (psiOnExists R' I' hR' D')
      (FractionRing R') k hk
    have hdA := finrank_fam_of_expBij hS R I hR D A G U.toUnifPre k hk (U.expand k hk)
    have hrk : D'.toPre.rank = D.toPre.rank := hD.xe.toIntLinearEquiv.finrank_eq
    refine ExpansionCriterion.expBij_of_onto hS R' I' hR' D' A' G' U' k hk hfin (by rw [hd', hrk, hgD, ← hd, hdA, hg]) fun F₀ => ?_
    obtain ⟨n, F, f, F', f', hF, hspan⟩ := T.exists_integral_families_span_pullDegeneration hP hG hT R R' I hR φ D D'.toPre hD k hk
    have hb : ∀ i, ∃ b : U'.SecK k, U'.Expands k b (F' i) := by
      intro i
      obtain ⟨σ, hσ⟩ := exists_sec_expandsAt_of_integral_family R I hR D A G U.toUnifPre k (fun F => ((U.expand k hk).2 F).exists) (F i) (f i)
        (hF i).1
      obtain ⟨σ', hσ', -⟩ := SecPull.existsUnique_secPull _ _ _ _ U.LG.L U'.LG.L _ U.LG.isLB U'.LG.isLB wL' hwL
        (Fin 1) (fun _ => 𝟙 G'.left) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))
        (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) (fun _ => by rw [Category.id_comp, Category.comp_id]) σ
      obtain ⟨b, hb⟩ := exists_secScal_one U'.LG.L (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => (k : ℤ))
        (pullback.fst G'.hom (jK R')) (fun _ => pullback.fst G'.hom (jK R'))
        (funext fun _ => (Category.comp_id _).symm) σ'
      refine ⟨b, 1, one_ne_zero, σ', f' i, by rw [scal_one]; exact hb,
        fun α => by rw [scal_one]; exact (hF i).2.1 α, fun e => ?_⟩
      obtain ⟨h, hh⟩ := hlev e
      exact expandsAt_transport R R' I I' D D' A A' G G' U.toUnifPre U' _ hD.w hD.xe _ wL' hD.w_gen hwL
        (ExpGTrans.famφB_pull hD) e e k h ⟨hh.1, hh.2⟩ σ σ' (f i) (f' i) hσ' (hF i).2.2 (hσ e)
    choose b hb using hb
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 (hspan ▸ Submodule.mem_top : F₀ ∈ _)
    exact ⟨secComb (fun i => scal (pullback.snd G'.hom (jK R')) (c i)) b,
      expands_linear R' I' hR' D' A' G' U' k n b F' c _ hb fun _ => rfl⟩
  exact ⟨⟨U', hexp⟩, rfl, hgen,
    (isPullUnif_iff_stalks R R' I I' φ D D' hD A A' G G' bc U ⟨U', hexp⟩).2 ⟨wL', hwL, he, hrig, hlev⟩⟩

theorem RigAlong.read {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G]
    {ε : G' ⟶ G} [IsMonHom ε] {L : RigLB G} {L' : RigLB G'} {w : LB.Iso L'.L (L.L.pull ε.left)}
    (h : RigAlong ε L L' w) {F : G'.left ⟶ G.left} (hF : F = ε.left) {e : S ⟶ S} (he₀ : e = 𝟙 S) :
    ∃ (wL : LB.Iso L'.L (L.L.pull F)) (he : eSec G' ≫ F = e ≫ eSec G), wL.IsGen ∧
      LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G') (fun _ => 1)) L'.rig
        (rigPullOf F e he L.L L.rig) := by
  subst hF he₀
  have he : eSec G' ≫ ε.left = 𝟙 S ≫ eSec G := by
    refine Eq.trans ?_ (Category.id_comp _).symm
    exact congrArg (fun f => f.left) (IsMonHom.one_hom ε)
  exact ⟨w, he, h.1, (maps_iff _ _ (fun _ => eSec G) _ L'.rig L.rig (𝟙 _) _ (rigPull_le _ _ he L.L)
    (fun _ => rfl)).2 h.2⟩

theorem exists_unif_move : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G G' : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (ε : G' ≅ G), AdmBase R I → IsSemiAbelian G → IsMonHom ε.hom → ∀ (U : Unif I D A G) (L' : RigLB G') (w : LB.Iso L'.L (U.LG.L.pull ε.hom.left)), RigAlong ε.hom U.LG L' w → ∀ hD : IsPullDeg (RingHom.id R) D.toPre D.toPre, ∃ (bc : G' ≅ (Over.pullback (specOf (RingHom.id R))).obj G) (U' : Unif I D A G'), IsMonHom bc.hom ∧ bc.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id R)) = ε.hom.left ∧ U'.LG = L' ∧ U'.gen.hom = (Over.pullback (jK R)).map ε.hom ≫ U.gen.hom ∧ IsPullUnif (RingHom.id R) hD bc U U' := by
  intro R _ _ I D A G G' _ _ _ _ ε hR hsa hε U L' w hw hD
  have hs := specOf_id R
  have gp₁ : IsGrpPullback G' G (specOf (RingHom.id R)) ε.hom.left :=
    (isGrpPullback_of_iso ε).congr hs.symm rfl
  obtain ⟨bc, mbc, hbc⟩ := grpPullback_iso gp₁ (isGrpPullback_pullback G (specOf (RingHom.id R)))
  have := U.gen_hom
  let eA : (Over.pullback (jK R)).obj G' ≅ A.A := (Over.pullback (jK R)).mapIso ε ≪≫ U.gen
  have mE : IsMonHom eA.hom := by
    show IsMonHom ((Over.pullback (jK R)).map ε.hom ≫ U.gen.hom)
    infer_instance
  have wA : LBIso (A.L.pull eA.hom.left) (U.LG.L.pull (pullback.fst G'.hom (jK R) ≫ bc.hom.left ≫
      pullback.fst G.hom (specOf (RingHom.id R)))) :=
    LBIso.chartPull (h := ((Over.pullback (jK R)).map ε.hom).left)
      (chartPullSame A.L (fun _ => eA.hom.left) (fun _ => U.gen.hom.left) _ _ fun _ => rfl)
      (chartPullSame U.LG.L _ (fun _ => pullback.fst G.hom (jK R)) _ _ fun _ => by
        rw [hbc]; exact (pullback.lift_fst _ _ _).symm) U.ext
  obtain ⟨wL, he, gL, rL⟩ := hw.read hbc hs
  obtain ⟨U', hL, hgen, hPU⟩ := exists_unif_pull_of_deg GlobalTheory.abelianSchemeLaws_all.1.polBaseChange
    GlobalTheory.abelianSchemeLaws_all.1.globalFns GlobalTheory.abelianSchemeLaws_all.1.secBaseChange GlobalTheory.twistBaseChange
    R R I I hR hR (RingHom.id R) (by rw [Ideal.map_id]) D A G hsa U D hD rfl G' bc mbc A rfl eA mE wA L' wL he gL rL
  exact ⟨bc, U', mbc, hbc, hL, by rw [hgen]; rfl, hPU⟩

end GlobalTheory.TorsionFormCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelExtensionOverDvr
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ThetaExtend

open GlobalTheory.CechPic GlobalTheory.TripleProd GlobalTheory.ThetaObjPull

theorem pic_local {R : Type} [CommRing R] [IsLocalRing R] (c : Pic (Sp R)) : c = 0 := by
  obtain ⟨U, hU, h⟩ := locZero_base (𝟙 (Sp R)) c (IsLocalRing.closedPoint R)
  have := pull_eq_zero_of_range h (𝟙 _) fun y =>
    (IsLocalRing.specializes_closedPoint y).mem_open U.isOpen hU
  rwa [pull_id, pull_id] at this

theorem locZero_lam {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB) {T : Over S} (x : T ⟶ A)
    (h₁ : LocZero (fst T A).left (cls (Out.translDiff A L x) (LB.isLB_linComb hL _ _))) :
    LocZero (fst T A).left (lam (cls L hL) (fst T A ≫ x) (snd T A)) := by
  have h₂ := (h₁.sub (locZero_base (fst T A).left (pull x.left (cls L hL)))).sub
    (locZero_base (fst T A).left (-pull (1 : T ⟶ A).left (cls L hL)))
  convert h₂ using 1
  rw [cls_translDiff hL, lam]
  simp only [map_neg, ← pull_comp, ← Over.comp_left, MonObj.comp_one]
  abel

theorem kTriv_of_lam {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB) {P : LB (A ⊗ A).left}
    (hP : P.IsLB) (e : cls P hP = lam (cls L hL) (fst A A) (snd A A))
    (h : ∀ (T : Over S) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x = 1) :
    Out.KTriv A L := by
  intro R _ t x hx
  have h₁ := (locZero_iff _ (LB.isLB_linComb hL _ _)).1 hx
  have h₂ := locZero_lam hL x h₁
  refine Over.OverMorphism.ext (Scheme.hom_ext_of_forall x.left (1 : Over.mk t ⟶ A).left fun p => ?_)
  obtain ⟨V, hV, H⟩ := h₂ p
  refine ⟨V, hV, ?_⟩
  let T' : Over S := Out.overRes (T := Over.mk t) V
  let i : T' ⟶ Over.mk t := Out.overResι V
  have H' := pull_eq_zero_of_range H (lift (snd A T' ≫ i) (fst A T')).left fun y => by
    have e := congrArg (fun q => q.left y) (lift_fst (snd A T' ≫ i) (fst A T'))
    show (fst (Over.mk t) A).left ((lift (snd A T' ≫ i) (fst A T')).left y) ∈ V
    refine e ▸ ?_
    exact ((snd A T').left y).2
  have := h T' (i ≫ x) ((cls_eq_zero_iff (pull_isLB hP _)).1 (by
    rw [cls_pull hP, e, pull_lam, lift_fst, lift_snd]
    rwa [pull_lam, lift_fst_assoc, lift_snd, Category.assoc] at H'))
  exact congrArg (fun q => q.left) (this.trans (MonObj.comp_one i).symm)

section Dvr

variable {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]

variable {A : Over (Sp V)} [GrpObj A] {B : Over (Sp K)} [GrpObj B] {ψ : B.left ⟶ A.left}

end Dvr

section Pol

variable {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
  {A : Over (Sp V)} [GrpObj A]

end Pol

end GlobalTheory.ThetaExtend
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinitePartOfIsFinitePart
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorsionFormCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.TorusModel GlobalTheory.FormalPoint GlobalTheory.AdicColimit GlobalTheory.KernelNoTorsion IsLocalRing
open scoped CategoryTheory.Obj

section Points

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {Gt : Over (Sp R)} [GrpObj Gt]
  {Φ : ∀ T, (T ⟶ Gt) ≃ GtPt D T}

theorem isZero_unique {T : Over (Sp R)} {g g' : GtPt D T} (h : g.IsZero) (h' : g'.IsZero) : g = g' :=
  pt_ext (h.1.trans h'.1.symm) fun χ _ _ hJ =>
    (val_corr hJ (h.2 χ) (𝟙 _)).trans (val_corr hJ (h'.2 χ) (𝟙 _)).symm

theorem isZero_of_isAdd {T : Over (Sp R)} {g : GtPt D T} (h : g.IsAdd g g) : g.IsZero := by
  obtain ⟨hb, hv⟩ := (TorusModel.isAdd_iff _ _ _).1 h
  have hb1 : g.b = 1 := mul_eq_left.1 hb.symm
  refine ⟨hb1, fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩
  have C : IsCub (th D (T := T) y J) := isCub_cubV D.cub hJ
  have e' : th D y J (cP D T χ) g.b g.b = 1 := by
    rw [hb1, C.face₃]
  have e := hv χ y J hJ
  rw [e', _root_.mul_one] at e
  have e₂ : cv g χ y J = 1 := mul_eq_left.1 e.symm
  exact e₂.trans (val_one _).symm

theorem isZero_one (hΦ : Represents Φ) (T : Over (Sp R)) : (Φ T 1).IsZero := by
  have h := hΦ.2 T 1 1
  rw [_root_.mul_one] at h
  exact isZero_of_isAdd h

theorem tors_iff (hΦ : Represents Φ) (k : ℕ) {T : Over (Sp R)} (x : T ⟶ Gt) :
    FlatIsoUnitGenerator.GtTors k (Φ T x) ↔ x ^ k = 1 := by
  constructor
  · rintro ⟨_, ⟨u, u0, us, rfl⟩, hz⟩
    have : ∀ i : Fin (k + 1), u i = Φ T (x ^ (i : ℕ)) := fun i => by
      induction i using Fin.induction with
      | zero => exact isZero_unique u0 (by simpa using isZero_one hΦ T)
      | succ i ih =>
        have h := us i
        rw [ih] at h
        rw [Fin.val_succ, pow_succ]
        exact isAdd_unique h (hΦ.2 T _ _)
    exact (Φ T).injective ((this (Fin.last k)).symm.trans (isZero_unique hz (isZero_one hΦ T)))
  · intro hx
    refine ⟨Φ T (x ^ k), ⟨fun i => Φ T (x ^ (i : ℕ)), by simpa using isZero_one hΦ T, fun i => ?_, rfl⟩,
      hx ▸ isZero_one hΦ T⟩
    simp only [Fin.val_succ, Fin.val_castSucc, pow_succ]
    exact hΦ.2 T _ _

theorem isPull_iff_comp (hΦ : Represents Φ) {T T' : Over (Sp R)} (h : T' ⟶ T) (x : T ⟶ Gt) (x' : T' ⟶ Gt) :
    GtPt.IsPull h.left (Φ T x) (Φ T' x') ↔ h ≫ x = x' :=
  ⟨fun H => (Φ T').injective (isPull_unique (hΦ.1 _ _ h x) H), fun H => H ▸ hΦ.1 _ _ h x⟩

theorem exists_represents [IsNoetherianRing R] (D : DegPre R) :
    ∃ (Gt : Over (Sp R)) (_ : GrpObj Gt) (_ : IsCommMonObj Gt) (Φ : ∀ T, (T ⟶ Gt) ≃ GtPt D T), Represents Φ ∧
      ∀ k : ℕ, 1 ≤ k → IsFinite (torsion Gt k).hom ∧ Flat (torsion Gt k).hom := by
  have hL := abelianSchemeLaws_all.1
  obtain ⟨H, _, _, hH⟩ := exists_isGt hL.globalFns (splitExt D)
  obtain ⟨Φ, hΦ⟩ := exists_points hL.globalFns hH
  refine ⟨H, inferInstance, inferInstance, Φ, hΦ, fun k hk => ?_⟩
  obtain ⟨h₁, h₂, -⟩ := hL.mulN _ D.P k hk
  have h₁' : IsFinite (𝟙 D.P.A ^ k).left := h₁
  have h₂' : Flat (𝟙 D.P.A ^ k).left := h₂
  rw [← MulEtaleDvr.mulN_eq_pow] at h₁' h₂'
  have P := MulEtaleDvr.isPullback_torsion D.P.A k
  exact isFinite_flat_torsion_of_isGt _ (splitExt D) H hH k hk (MorphismProperty.of_isPullback (P := @IsFinite) P h₁')
    (MorphismProperty.of_isPullback (P := @Flat) P h₂')

end Points

theorem isAdicColimit_of_isFinite {R : Type} [CommRing R] [IsLocalRing R] (hc : IsAdicComplete (maximalIdeal R) R)
    (N : Over (Sp R)) [IsFinite N.hom] [Flat N.hom] : IsAdicColimit (maximalIdeal R) N := by
  have : IsAffine N.left := isAffine_of_isAffineHom N.hom
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (N.left.isoSpec.inv ≫ N.hom)
  have hf : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  have hl : Flat (Spec.map φ) := by rw [hφ]; infer_instance
  rw [IsFinite.SpecMap_iff] at hf
  rw [HasRingHomProperty.Spec_iff (P := @Flat)] at hl
  letI : Algebra R Γ(N.left, ⊤) := φ.hom.toAlgebra
  have : Module.Finite R Γ(N.left, ⊤) := hf
  have : Module.Flat R Γ(N.left, ⊤) := hl
  have H := isAdicColimit_of_finite_flat (maximalIdeal R) (RingHom.id R) (by rwa [Ideal.map_id])
    (fun a ha => ⟨1, by rwa [Ideal.map_id, pow_one]⟩) Γ(N.left, ⊤)
  exact IsAdicColimit.of_iso (Over.isoMk N.left.isoSpec.symm hφ.symm) H

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {t : SAB H (Sp R)}

theorem formalEq_iff {D : DegData R I} {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G]
    [IsCommMonObj G] (U : UnifPre I D A G) {T : Over (Sp R)} (x : T ⟶ G) (g : GtPt D.toPre T) :
    FlatIsoUnitGenerator.FormalEq U x g ↔ IsPointOf U g x := by
  rw [isPointOf_iff_thick]
  refine forall_congr' fun e => and_congr eq_comm (forall_congr' fun χ => ⟨fun h => ?_, fun h => ?_⟩) <;>
  exact corr_of_val D.toPre.P.isLB fun _ _ hJ => (val_corr hJ h (𝟙 _)).symm

end GlobalTheory.TorsionFormCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.InjectiveOfIsAlgebraic
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj NumberField
open scoped TensorProduct

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ArcInputCompare

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.TorusExt

attribute [local instance] gtGroup

section Classes

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O D.X]

variable (hB : D.TauBimult) (oa : D.OAct O) (F : Type) [Field F] [Algebra (FractionRing R) F]

variable {F} {k : ℕ}

variable {F' : Type} [Field F'] [Algebra (FractionRing R) F'] (f : F →+* F')
  (hf : f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F')

theorem isRatio_ext {p p' : QkPt D F k} {z : F} (h : QkPairing.IsRatio p p' z) :
    QkPairing.IsRatio (qkExt hB f hf p) (qkExt hB f hf p') (f z) := by
  intro T σ y J hJ
  have e := h T (σ ≫ extMap f hf) y J hJ
  have v : ∀ (g : GtPtF D F) χ, val ((gtExt D f hf g).s χ) σ.left y J = val (g.s χ) (σ ≫ extMap f hf).left y J :=
    fun g χ => (val_corr hJ (((eq_gtExt_iff f hf g _).1 rfl).2 χ) _).trans (val_pull hJ _ _ _)
  have w : gs σ.left y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F')).inv.hom (f z)) =
      gs (σ ≫ extMap f hf).left y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom z) := by
    refine Eq.trans (congrArg (gs σ.left y ⊤) ?_) (gs_pull σ.left (spMap f) y ⊤ trivial _)
    exact congrArg (fun g => g.hom z) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  dsimp only [qkExt, qkMk]
  rw [v, v, w, gtExt_b, gtExt_b, ← Category.assoc, ← Category.assoc]
  exact e

theorem weil_ext (k : ℕ) (hk : 1 ≤ k) (p p' : QkPt D F k) (z : F) (h : WeilQkIs D F k p p' z) :
    WeilQkIs D F' k (qkExt hB f hf p) (qkExt hB f hf p') (f z) := by
  obtain ⟨u, hu⟩ := QkPairing.exists_ratio p p'
  obtain rfl := QkPairing.weil_unique globalFns_holds abelianSchemeLaws_all.2.secTwist hB hk p p' h
    (QkPairing.weil_of_ratio globalFns_holds p p' hu)
  exact QkPairing.weil_of_ratio globalFns_holds _ _ (ζ := Units.map f.toMonoidHom u) (isRatio_ext hB f hf hu)

end Classes

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

section Data

variable {R : Type} [CommRing R] [IsDomain R] {D : Datum H} {P : DegPre R} [Module (𝓞 E) P.X]
  {oa : letI := H.starRing; P.OAct (𝓞 E)} {F : Type} [Field F] [Algebra (FractionRing R) F]

variable (hB : P.TauBimult)

end Data

section Lev

variable (D : Datum H) (l : Level H)

end Lev

section Level

variable {R : Type} [CommRing R] [IsDomain R] {D : Datum H} {l : Level H} {P : DegPre R} [Module (𝓞 E) P.X]
  {oa : letI := H.starRing; P.OAct (𝓞 E)} {F F' : Type} [Field F] [Algebra (FractionRing R) F] [Field F']
  [Algebra (FractionRing R) F'] (hB : P.TauBimult)

variable (f : F →+* F') (hf : f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F')

end Level

section ThetaShiftProofs

variable {D : Datum H} {l : Level H} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'}

end ThetaShiftProofs

section Main

variable {D : Datum H} {l : Level H} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'}

end Main

end GlobalTheory.ArcInputCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionsDimAdditionGraphPrincipalPolarisation
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

namespace GlobalTheory.AdditionGraph

open GlobalTheory.CechPic
open scoped Kronecker

section Algebra

variable {G H σ κ : Type} [CommGroup G] [CommGroup H] [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]

omit [DecidableEq κ] in
theorem apply_prod_single (Φ : H ≃* (σ → G)) (pt : κ → G) (a : σ × κ → ℕ) (b : σ) :
    Φ (∏ x : σ × κ, Φ.symm (Pi.mulSingle x.1 (pt x.2)) ^ a x) b = ∏ j, pt j ^ a (b, j) := by
  rw [map_prod, Finset.prod_apply, Fintype.prod_prod_type, Finset.prod_eq_single b]
  · simp
  · intro c _ hc
    simp [Pi.mulSingle_eq_of_ne' hc]
  · simp

omit [DecidableEq κ] in
theorem existsUnique_prod_single (Φ : H ≃* (σ → G)) {k : ℕ} (pt : κ → G)
    (h : ∀ y : G, y ^ k = 1 → ∃! c : κ → ZMod k, ∏ j, pt j ^ (c j).val = y) (y : H) (hy : y ^ k = 1) :
    ∃! c : σ × κ → ZMod k, ∏ x : σ × κ, Φ.symm (Pi.mulSingle x.1 (pt x.2)) ^ (c x).val = y := by
  have hb : ∀ b, Φ y b ^ k = 1 := fun b => by
    rw [← Pi.pow_apply, ← map_pow, hy, map_one, Pi.one_apply]
  choose c hc hu using fun b => h _ (hb b)
  refine ⟨fun x => c x.1 x.2, Φ.injective (funext fun b => ?_), fun c' hc' => funext fun x => ?_⟩
  · rw [apply_prod_single]
    exact hc b
  · refine congrFun (hu x.1 (fun j => c' (x.1, j)) ?_) x.2
    rw [← hc', apply_prod_single]

theorem act_prod_single (Φ : H ≃* (σ → G)) {k : ℕ} (pt : κ → G) (h : ∀ j, pt j ^ k = 1) (C : Matrix σ σ ℕ)
    (s : H → H) (hs : ∀ y b, Φ (s y) b = ∏ a, Φ y a ^ C b a) (x : σ × κ) :
    s (Φ.symm (Pi.mulSingle x.1 (pt x.2))) = ∏ x' : σ × κ, Φ.symm (Pi.mulSingle x'.1 (pt x'.2)) ^
      ((C.map (Nat.cast : ℕ → ZMod k) ⊗ₖ (1 : Matrix κ κ (ZMod k))) x' x).val := by
  refine Φ.injective (funext fun b => ?_)
  rw [apply_prod_single, hs, Finset.prod_eq_single x.1, Finset.prod_eq_single x.2]
  · simp [ZMod.val_natCast, ← pow_eq_pow_mod _ (h _)]
  · intro j _ hj
    simp [Matrix.one_apply_ne hj]
  · simp
  · intro a _ ha
    simp [Pi.mulSingle_eq_of_ne ha]
  · simp

theorem eq_of_forall_zmod {l a b : ℕ} (hl : l.Prime) (h : ∀ j, (a : ZMod (l ^ j)) = b) : a = b := by
  have hlt : a + b < l ^ (a + b) := Nat.lt_pow_self hl.one_lt
  exact Nat.ModEq.eq_of_lt_of_lt ((ZMod.natCast_eq_natCast_iff _ _ _).1 (h (a + b))) (by omega) (by omega)

end Algebra

section Geometry

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

theorem linComb_equiv {T : Over S} {n : ℕ} {σ : Type} [Fintype σ] (ε : Fin n ≃ σ) (y : σ → (T ⟶ B)) (a : σ → ℕ) :
    Out.linComb (fun i => y (ε i)) (fun i => a (ε i)) = ∏ x, y x ^ a x := by
  rw [Out.linComb, List.prod_ofFn]
  exact ε.prod_comp fun x => y x ^ a x

def pointsEquiv (e : B ≅ A ⊗ A) [IsMonHom (e.hom ≫ fst A A)] [IsMonHom (e.hom ≫ snd A A)] (T : Over S) :
    (T ⟶ B) ≃* (Fin 2 → (T ⟶ A)) where
  toFun x := ![x ≫ e.hom ≫ fst A A, x ≫ e.hom ≫ snd A A]
  invFun y := lift (y 0) (y 1) ≫ e.inv
  left_inv x := by
    rw [← cancel_mono e.hom]
    ext <;> simp
  right_inv y := by
    funext i
    fin_cases i <;> simp
  map_mul' x y := by
    funext i
    fin_cases i
    · exact MonObj.mul_comp x y (e.hom ≫ fst A A)
    · exact MonObj.mul_comp x y (e.hom ≫ snd A A)

omit [IsCommMonObj B] in
theorem isMonHom_mul (p q : B ⟶ A) [IsMonHom p] [IsMonHom q] : IsMonHom (p * q) := by
  refine ⟨?_, ?_⟩
  · rw [MonObj.comp_mul, IsMonHom.one_hom p, IsMonHom.one_hom q,
      MonObj.one_eq_one A, _root_.mul_one]
  · rw [← lift_fst_comp_snd_comp (p * q) (p * q), ← Hom.mul_def, MonObj.mul_eq_mul B]
    simp only [MonObj.comp_mul, MonObj.mul_comp]
    exact mul_mul_mul_comm _ _ _ _

omit [IsCommMonObj A] [IsCommMonObj B] in
theorem lam_add {T : Over S} (c d : Pic B.left) (x y : T ⟶ B) : lam (c + d) x y = lam c x y + lam d x y := by
  simp only [lam, map_add (f := _)]
  abel

end Geometry

end GlobalTheory.AdditionGraph

namespace GlobalTheory

open GlobalTheory.CechPic GlobalTheory.AdditionGraph
open scoped Kronecker

theorem sectionsDim_additionGraph_principalPolarisation : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N : ℕ), 1 ≤ N → ∀ e ≥ 1, SectionsHaveFiniteDimension (P.A ⊗ P.A).hom (lbPow (LB.LinComb P.L (K := Fin 3) ![(fst P.A P.A).left, (snd P.A P.A).left, (fst P.A P.A * snd P.A P.A).left] ![(N : ℤ), (N : ℤ), (N : ℤ)]) e) (3 ^ P.g * (N * e) ^ (2 * P.g)) := by
  intro laws laws₂ K _ _ P N hN e he
  obtain ⟨Q, φ, hp, hq, hg, hQ⟩ := SquarePol.exists_square K P
  have := P.isAb.comm
  have := Q.isAb.comm
  have := P.isAb.proper
  have := Q.isAb.proper
  have hL := P.isLB
  obtain ⟨rig, hrig⟩ := P.rigid
  obtain ⟨cub⟩ := (laws.cube _ P ⟨P.L, rig, hL, hrig⟩ rfl).1
  have hΘ : ∃ t : LB.Gen (Theta P.A P.L), t.IsGen := ⟨cub.t, cub.isGen⟩
  obtain ⟨-, -, hsym, -, -, htor⟩ := GlobalTheory.T.principalPolarisation_volume_form_symmetric_ample laws laws₂ K P
  let Φ := pointsEquiv φ
  set p := φ.hom ≫ fst P.A P.A with hpd
  set q := φ.hom ≫ snd P.A P.A with hqd
  have hpq := isMonHom_mul p q
  set c := cls P.L hL with hc

  let M : LB Q.A.left := LB.LinComb P.L (K := Fin 3) ![p.left, q.left, (p * q).left] ![(N : ℤ), (N : ℤ), (N : ℤ)]
  have hM : M.IsLB := LB.isLB_linComb hL _ _
  have cM : cls M hM = N • (pull p.left c + pull q.left c + pull (p * q).left c) := by
    rw [cls_linComb hL, Fin.sum_univ_three]
    simp [← hc]
  have cQ : cls Q.L Q.isLB = pull p.left c + pull q.left c := by
    rw [(cls_eq_iff Q.isLB (LB.isLB_linComb hL _ _)).2 hQ, cls_linComb hL, Fin.sum_univ_two]
    simp [← hc]

  have hamp : Out.RelAmple Q.A M := by
    obtain ⟨n, hn, hgen⟩ := ((relAmple_iff_isAmpleLB_of_isAffine P.A hL).1 P.ample).exists_isGenerated_pow
    have a₁ := (isAmpleLB_pow_iff Q.isLB (k := n * N) (Nat.mul_pos hn hN)).2
      ((relAmple_iff_isAmpleLB_of_isAffine Q.A Q.isLB).1 Q.ample)
    have a₂ := (hgen.pow N).pull (p * q).left
    have hMn : (lbPow M n).IsLB := LB.isLB_linComb hM _ _
    refine (relAmple_iff_isAmpleLB_of_isAffine Q.A hM).2 ((isAmpleLB_pow_iff hM hn).1
      (a₁.tensor_isGenerated a₂ hMn ((cls_eq_zero_iff (LB.isLB_div (LB.isLB_div hMn a₁.isLB) a₂.isLB)).1 ?_)))
    rw [cls_div (LB.isLB_div hMn a₁.isLB) a₂.isLB, cls_div hMn a₁.isLB, cls_pull (hgen.pow N).isLB,
      cls_lbPow hgen.isLB, cls_lbPow hL, cls_lbPow hM, cls_lbPow Q.isLB, cM, cQ, map_nsmul, map_nsmul, ← hc]
    module

  have hsymM : SymB M := by
    have e₁ : pull (GrpObj.inv : P.A ⟶ P.A).left c = c :=
      ((cls_eq_iff hL (pull_isLB hL _)).2 hsym).symm
    have e₂ : ∀ (r : Q.A ⟶ P.A) [IsMonHom r],
        pull (GrpObj.inv : Q.A ⟶ Q.A).left (pull r.left c) = pull r.left c := fun r _ => by
      rw [← pull_comp, ← Over.comp_left, GrpObj.inv_hom, Over.comp_left, pull_comp, e₁]
    refine (cls_eq_iff hM (pull_isLB hM _)).1 ?_
    rw [cls_pull hM, cM, map_nsmul, map_add (f := _), map_add (f := _), e₂, e₂, e₂]

  let C : Matrix (Fin 2) (Fin 2) ℕ := !![2 * N, N; N, 2 * N]
  let s : Q.A ⟶ Q.A := (Φ Q.A).symm ![p ^ (2 * N) * q ^ N, p ^ N * q ^ (2 * N)]
  have sp : s ≫ p = p ^ (2 * N) * q ^ N := congrFun ((Φ Q.A).apply_symm_apply _) 0
  have sq : s ≫ q = p ^ N * q ^ (2 * N) := congrFun ((Φ Q.A).apply_symm_apply _) 1
  have hs : ∀ {T : Over (Sp K)} (y : T ⟶ Q.A) (b : Fin 2), Φ T (y ≫ s) b = ∏ a, Φ T y a ^ C b a := by
    intro T y b
    rw [Fin.prod_univ_two]
    fin_cases b
    · change (y ≫ s) ≫ p = (y ≫ p) ^ (2 * N) * (y ≫ q) ^ N
      rw [Category.assoc, sp, MonObj.comp_mul, MonObj.comp_pow, MonObj.comp_pow]
    · change (y ≫ s) ≫ q = (y ≫ p) ^ N * (y ≫ q) ^ (2 * N)
      rw [Category.assoc, sq, MonObj.comp_mul, MonObj.comp_pow, MonObj.comp_pow]
  have hform : FormIs Q M s := by
    refine ⟨laws.rigidity _ _ _ Q.isAb Q.isAb _ ?_, ?_⟩
    · have e₁ : (η[Q.A] : 𝟙_ _ ⟶ Q.A) = 1 := by rw [Hom.one_def]; simp
      rw [e₁]
      refine (Φ _).injective (funext fun b => ?_)
      rw [hs, map_one]
      simp
    · have mr : ∀ {T : Over (Sp K)} (x y z : T ⟶ P.A), lam c x (y * z) = lam c x y + lam c x z := fun x y z => by
        rw [lam_comm, lam_mul_left hL hΘ, lam_comm _ y, lam_comm _ z]
      refine (cls_eq_iff (LB.isLB_linComb hM _ _) (LB.isLB_linComb Q.isLB _ _)).1 ?_
      refine (cls_cube_two hM _ _ _).trans (Eq.trans ?_ (cls_cube_two Q.isLB _ _ _).symm)
      rw [cM, cQ, lam_nsmul]
      simp only [lam_add, lam_pull, Category.assoc, sp, sq, MonObj.comp_mul, MonObj.comp_pow, mr]
      simp only [hc, lam_mul_left hL hΘ, lam_pow_right hL hΘ]
      module

  obtain ⟨l, hl, hlK⟩ : ∃ l : ℕ, l.Prime ∧ (l : K) ≠ 0 := by
    by_cases h : ((2 : ℕ) : K) = 0
    · refine ⟨3, Nat.prime_three, fun h' => one_ne_zero (α := K) ?_⟩
      push_cast at h h'
      linear_combination h' - h
    · exact ⟨2, Nat.prime_two, h⟩
  obtain ⟨δ, -, hδ, hdet⟩ := GlobalTheory.T.sections_count_sq_eq_det_form_on_torsion laws laws₂ K Q M s l hl hlK hM hamp hsymM hform
  have hsq : δ ^ 2 = ((3 * N ^ 2) ^ P.g) ^ 2 := by
    refine eq_of_forall_zmod hl fun j => ?_
    obtain ⟨pt, ⟨h₀, h₁, h₂⟩, -⟩ := htor (l ^ j) (by rw [Nat.cast_pow]; exact pow_ne_zero _ hlK)
    let ε : Fin (2 * Q.g) ≃ Fin 2 × Fin (2 * P.g) := (finCongr (by rw [hg])).trans finProdFinEquiv.symm
    let z : Fin 2 × Fin (2 * P.g) → (Out.baseOver (Sp K) ⟶ Q.A) := fun x => (Φ _).symm (Pi.mulSingle x.1 (pt x.2))
    let D := C.map (Nat.cast : ℕ → ZMod (l ^ j)) ⊗ₖ (1 : Matrix (Fin (2 * P.g)) (Fin (2 * P.g)) (ZMod (l ^ j)))
    have h₃ := hdet j (fun i => z (ε i)) (D.submatrix ε ε) ⟨h₀, fun i => ?_, fun y hy => ?_⟩
      ⟨h₀, fun i => ?_⟩
    · have hC : (C.map (Nat.cast : ℕ → ZMod (l ^ j))).det = 3 * (N : ZMod (l ^ j)) ^ 2 := by
        simp [C, Matrix.det_fin_two]
        ring
      rw [Matrix.det_submatrix_equiv_self, Matrix.det_kronecker, hC, Matrix.det_one, one_pow, _root_.mul_one,
        Fintype.card_fin] at h₃
      push_cast
      rw [h₃, ← pow_mul, _root_.mul_comm P.g]
    · rw [← map_pow, ← Pi.mulSingle_pow, h₁, Pi.mulSingle_one, map_one]
    · have h₄ := existsUnique_prod_single (Φ _) pt (fun y hy => by
        simpa only [Out.linComb, List.prod_ofFn] using h₂ y hy) y hy
      refine ((Equiv.arrowCongr ε.symm (Equiv.refl _)).existsUnique_congr fun a => ?_).1 h₄
      rw [← linComb_equiv ε z fun x => (a x).val]
      rfl
    · exact (act_prod_single (Φ _) pt h₁ C (· ≫ s) hs (ε i)).trans
        (linComb_equiv ε z fun x => (D x (ε i)).val).symm
  have hδ' : δ = (3 * N ^ 2) ^ P.g := Nat.pow_left_injective two_ne_zero hsq
  have H := hδ e he
  rw [show δ * e ^ Q.g = 3 ^ P.g * (N * e) ^ (2 * P.g) by rw [hδ', hg]; ring] at H

  let M' := LB.LinComb P.L (K := Fin 3)
    ![(fst P.A P.A).left, (snd P.A P.A).left, (fst P.A P.A * snd P.A P.A).left] ![(N : ℤ), (N : ℤ), (N : ℤ)]
  have hM' : M'.IsLB := LB.isLB_linComb hL _ _
  have hMe : (lbPow M e).IsLB := LB.isLB_linComb hM _ _
  have hMe' : (lbPow M' e).IsLB := LB.isLB_linComb hM' _ _
  refine ((SecDim.lbPow_mul_and_pull_and_sectionsFiniteDim_iso_invariant K _ (P.A ⊗ P.A).hom _ hMe').2.2.2.2.2 _ ((Over.forget _).mapIso φ) _).2 ?_
  change SectionsHaveFiniteDimension (φ.hom.left ≫ (P.A ⊗ P.A).hom) ((lbPow M' e).pull φ.hom.left) _
  rw [Over.w]
  refine ((SecDim.lbPow_mul_and_pull_and_sectionsFiniteDim_iso_invariant K _ Q.A.hom _ hMe).2.1 _ (pull_isLB hMe' _) ?_).1 _ H
  refine (cls_eq_iff hMe (pull_isLB hMe' _)).1 ?_
  rw [cls_pull hMe', cls_lbPow hM, cls_lbPow hM', cM, cls_linComb hL, Fin.sum_univ_three]
  have e₁ : ∀ r : P.A ⊗ P.A ⟶ P.A, pull φ.hom.left (pull r.left c) = pull (φ.hom ≫ r).left c := fun r => by
    rw [Over.comp_left, pull_comp]
  simp only [← hc, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, map_nsmul, map_add (f := _), map_zsmul, e₁,
    MonObj.comp_mul, ← hpd, ← hqd]
  module

end GlobalTheory
end
end
