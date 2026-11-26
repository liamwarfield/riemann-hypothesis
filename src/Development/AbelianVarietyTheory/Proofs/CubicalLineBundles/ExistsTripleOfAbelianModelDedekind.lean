module

public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SumExtendByZeroLeSum
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RelAmpleOfGenericIso
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsRankOneCuspLatticeDataOfPrincipal
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsNumberFieldDefiningCmCurveHoms
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogLieNormSqEqMeanLogEta
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModelFiniteOverModuliModelDescends
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjOverBaseChangeOfProperQuasiProjective

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsTripleOfAbelianModelDedekind
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsRigLBExtensionDedekind
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

open GlobalTheory.CechPic in
theorem exists_rigLB_extension_dedekind :
    ∀ (R K : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G], IsAbelianScheme G → ∀ (X' : Scheme.{0}) (π : X' ⟶ G.left) (p : X' ⟶ Sp K), IsPullback π p G.hom (spMap (algebraMap R K)) → ∀ L : LB X', L.IsLB → ∃ L' : RigLB G, LBIso (L'.L.pull π) L := by
  intro R K _ _ _ _ _ A _ hA X' φ p hφ N hN
  have := hA.smooth
  have := hA.proper
  have hR : IsRegularRing R := inferInstance
  have : GeometricallyIntegral A.hom :=
    forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hA.smooth
      hA.geomConnected
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian A.hom
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have : GeometricallyIntegral p :=
    MorphismProperty.of_isPullback (P := @GeometricallyIntegral) hφ inferInstance
  have : Smooth p := MorphismProperty.of_isPullback (P := @Smooth) hφ inferInstance
  have : IsIntegral X' := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian p
  have h1 : IsPreimmersion (spMap (algebraMap R K)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have h2 : Flat (spMap (algebraMap R K)) := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat K (nonZeroDivisors R))
  have : IsPreimmersion φ := MorphismProperty.of_isPullback (P := @IsPreimmersion) hφ.flip h1
  have : Flat φ := MorphismProperty.of_isPullback (P := @Flat) hφ.flip h2
  have hst : ∀ x : A.left, UniqueFactorizationMonoid (A.left.presheaf.stalk x) := fun x =>
    have := ExtendRig.isRegularRing_stalk isRegularRing_of_smooth R A.hom x
    uniqueFactorizationMonoid_of_isRegularRing_of_isLocalRing
      exists_hasProjectiveDimensionLE_of_isRegularLocalRing
      isPrincipal_map_away_of_hasProjectiveDimensionLE _
  obtain ⟨L, hL, hLN⟩ := exists_lineBundle_extension_of_generalizing A.left X' φ
    (Flat.generalizingMap φ) hst N hN
  let e : Sp R ⟶ A.left := eSec A
  have he : e ≫ A.hom = 𝟙 _ := Over.w η[A]
  have hL' : (L.pull (A.hom ≫ e)).IsLB := pull_isLB hL _
  have hM : (LB.div L (L.pull (A.hom ≫ e))).IsLB := LB.isLB_div hL hL'
  obtain ⟨t, ht⟩ : ∃ t : LB.Gen ((LB.div L (L.pull (A.hom ≫ e))).pull e), t.IsGen := by
    refine (cls_eq_zero_iff (pull_isLB hM e)).1 ?_
    rw [cls_pull hM e (pull_isLB hM e), cls_div hL hL' hM, cls_pull hL (A.hom ≫ e) hL', map_sub, ← pull_comp, ← Category.assoc, he,
      Category.id_comp, sub_self]
  refine ⟨⟨LB.div L (L.pull (A.hom ≫ e)), t, hM, ht⟩, (cls_eq_iff (pull_isLB hM φ) hN).1 ?_⟩
  have h0 : pull (spMap (algebraMap R K) ≫ e) (cls L hL) = 0 :=
    (cls_eq_zero_iff (pull_isLB hL _)).2 (DVR.exists_gen_of_local L hL _ _)
  rw [cls_pull hM φ (pull_isLB hM φ), cls_div hL hL' hM, cls_pull hL (A.hom ≫ e) hL', map_sub, ← pull_comp, ← Category.assoc, hφ.w,
    Category.assoc, pull_comp, h0, map_zero, sub_zero]
  exact (cls_eq_iff (pull_isLB hL φ) hN).2 hLN

end GlobalTheory.CM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsTripleOfAbelianModelDedekind
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section

namespace GlobalTheory.CM.TripleModel

section Tensor

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {X Y : Over S} {X' Y' : Over S'}

theorem isPullback_tensor {a : X'.left ⟶ X.left} {b : Y'.left ⟶ Y.left} (ha : IsPullback a X'.hom X.hom f)
    (hb : IsPullback b Y'.hom Y.hom f) {c : (X' ⊗ Y').left ⟶ (X ⊗ Y).left}
    (h₁ : c ≫ (fst X Y).left = (fst X' Y').left ≫ a) (h₂ : c ≫ (snd X Y).left = (snd X' Y').left ≫ b) :
    IsPullback c (X' ⊗ Y').hom (X ⊗ Y).hom f := by
  have h : IsPullback (fst X' Y').left (snd X' Y').left X'.hom Y'.hom := .of_hasPullback _ _
  have h₀ : IsPullback (fst X Y).left (snd X Y).left X.hom Y.hom := .of_hasPullback _ _
  have h₃ : IsPullback c (snd X' Y').left (snd X Y).left b := by
    refine IsPullback.of_right ?_ h₂ h₀
    rw [h₁, hb.w]
    exact h.paste_horiz ha
  rw [← Over.w (snd X' Y'), ← Over.w (snd X Y)]
  exact h₃.paste_vert hb

end Tensor

section Cube

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
  [IsCommMonObj G'] {φ : G'.left ⟶ G.left} {M : LB G.left} {M' : LB G'.left}

theorem lbIso_cube_pull (h : IsGrpPullback G' G f φ) (hM : M.IsLB) (hM' : M'.IsLB) (e : LBIso (M.pull φ) M')
    {T' : Over S'} {T : Over S} {n : ℕ} (x' : Fin n → (T' ⟶ G')) (x : Fin n → (T ⟶ G))
    (U : Over.mk (T'.hom ≫ f) ⟶ T) (hx : ∀ i, pushPt h.1.w (x' i) = U ≫ x i) :
    LBIso ((cubeLB G x M).pull U.left) (cubeLB G' x' M') := by
  have hc : (cubeLB G x M).IsLB := DVR.linComb_isLB _ hM _ _
  have h₁ : LBIso ((cubeLB G x M).pull U.left) (cubeLB G' x' (M.pull φ)) :=
    LBIso.chartPull (Geo.Tor.chartPullPull _ _ U.left rfl)
      (chartPullLinComb M _ _ _ _ U.left fun I => psum_push h _ _ U hx I.down) (PolBaseChange.lbIso_refl hc)
  exact LBIso.trans (pull_isLB hc _) (DVR.linComb_isLB _ (pull_isLB hM _) _ _) (DVR.linComb_isLB _ hM' _ _) h₁
    (PowPrimitive.lbIso_linComb e _ _)

theorem lbIso_cube_of_eq (hM : M.IsLB) {T T' : Over S} (ρ : T' ⟶ T) {n : ℕ} (x y : Fin n → (T ⟶ G))
    (h : ∀ i, ρ ≫ x i = ρ ≫ y i) : LBIso ((cubeLB G x M).pull ρ.left) ((cubeLB G y M).pull ρ.left) :=
  LBIso.chartPull (chartPullOut M _ _ ρ.left _ fun I => PrimNorm.psum_pre ρ x (fun i => ρ ≫ x i) (fun _ => rfl) I.down)
    (chartPullOut M _ _ ρ.left _ fun I => PrimNorm.psum_pre ρ y (fun i => ρ ≫ x i) h I.down)
    (PolBaseChange.lbIso_refl (L := cubeLB G (fun i => ρ ≫ x i) M) (DVR.linComb_isLB _ hM _ _))

theorem exists_gen_theta_zero (hM : M.IsLB) :
    ∃ t : LB.Gen ((Theta G M).pull (eSec (G ⊗ G ⊗ G))), t.IsGen := by
  have e : η[G ⊗ G ⊗ G] = lift (1 : 𝟙_ _ ⟶ G) (lift (1 : 𝟙_ _ ⟶ G) (1 : 𝟙_ _ ⟶ G)) := by
    ext <;> simp [Hom.one_def]
  obtain ⟨t, ht⟩ := (PrimNorm.hasGen_iff hM
    (fun I : thK => (lift (1 : 𝟙_ _ ⟶ G) (lift (1 : 𝟙_ _ ⟶ G) (1 : 𝟙_ _ ⟶ G))).left ≫ thφ G (x3 G) I) thε).2
    ((prod_cub _ _ _ (PrimNorm.cls M)).trans (by simp))
  exact gen_chartPull (chartPullOut M (thφ G (x3 G)) thε (eSec (G ⊗ G ⊗ G)) _ fun I => by rw [eSec, e]) t ht

end Cube

theorem exists_gen_of_lbIso {X : Scheme.{0}} {L N : LB X} (hL : L.IsLB) (hN : N.IsLB) (H : LBIso L N)
    (h : ∃ t : L.Gen, t.IsGen) : ∃ t : N.Gen, t.IsGen :=
  (CechPic.iso_triv_iff N).1 (LBIso.trans (LB.isLB_triv X) hL hN ((CechPic.iso_triv_iff L).2 h) H)

theorem exists_triple_of_abelian_model : Out.Laws → (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R K : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (t₀ : SAB H (Sp K)) (B : Over (Sp R)) [GrpObj B] (φ : t₀.G.left ⟶ B.left), IsAbelianScheme B → IsGrpPullback t₀.G B (spMap (algebraMap R K)) φ → ∃ (t : SAB H (Sp R)) (m : SABMap t₀ t (spMap (algebraMap R K))) (e : t.G ≅ B), IsMonHom e.hom ∧ m.φ ≫ e.hom.left = φ := by
  intro hL hext E _ _ _ H R K _ _ _ _ _ t₀ B _ φ hB h
  have := hB.comm
  have hB₂ := AbelianSchemeGerms.isAbelianScheme_tensor B B hB hB
  have hB₃ := AbelianSchemeGerms.isAbelianScheme_tensor B _ hB hB₂
  obtain ⟨act, hact⟩ := exists_oAct_extend_dedekind hext R K (𝓞 E) B t₀.G φ hB h t₀.act
  obtain ⟨M, hM⟩ := exists_rigLB_extension_dedekind R K B hB _ φ t₀.G.hom h.1 t₀.PP.L t₀.PP.isLB
  have lb : ∀ {T : Over (Sp R)} {n : ℕ} (x : Fin n → (T ⟶ B)) {L : LB B.left}, L.IsLB → (cubeLB B x L).IsLB :=
    fun x L hL => DVR.linComb_isLB _ hL _ _
  have lb₀ : ∀ {T : Over (Sp K)} {n : ℕ} (x : Fin n → (T ⟶ t₀.G)), (cubeLB t₀.G x t₀.PP.L).IsLB :=
    fun x => DVR.linComb_isLB _ t₀.PP.isLB _ _
  have pa : ∀ {T : Over (Sp K)} (x : T ⟶ t₀.G) a,
      pushPt h.1.w (x ≫ t₀.act.act a) = pushPt h.1.w x ≫ act.act a := fun x a =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, hact, Category.assoc])
  let U₂ := lift (pushPt h.1.w (fst t₀.G t₀.G)) (pushPt h.1.w (snd t₀.G t₀.G))
  have p₂ : IsPullback U₂.left (t₀.G ⊗ t₀.G).hom (B ⊗ B).hom (spMap (algebraMap R K)) :=
    isPullback_tensor h.1 h.1
      (congrArg (fun q => q.left) (lift_fst (pushPt h.1.w (fst t₀.G t₀.G)) (pushPt h.1.w (snd t₀.G t₀.G))))
      (congrArg (fun q => q.left) (lift_snd (pushPt h.1.w (fst t₀.G t₀.G)) (pushPt h.1.w (snd t₀.G t₀.G))))
  let U₃ := lift (pushPt h.1.w (x3 t₀.G 0)) (lift (pushPt h.1.w (x3 t₀.G 1)) (pushPt h.1.w (x3 t₀.G 2)))
  have p₃ : IsPullback U₃.left (t₀.G ⊗ t₀.G ⊗ t₀.G).hom (B ⊗ B ⊗ B).hom (spMap (algebraMap R K)) := by
    refine isPullback_tensor h.1 p₂ (congrArg (fun q => q.left) (lift_fst (pushPt h.1.w (x3 t₀.G 0))
        (lift (pushPt h.1.w (x3 t₀.G 1)) (pushPt h.1.w (x3 t₀.G 2)))))
      ((congrArg (fun q => q.left) (lift_snd (pushPt h.1.w (x3 t₀.G 0))
        (lift (pushPt h.1.w (x3 t₀.G 1)) (pushPt h.1.w (x3 t₀.G 2))))).trans ?_)
    apply pullback.hom_ext
    · refine (congrArg (fun q => q.left) (lift_fst (pushPt h.1.w (x3 t₀.G 1)) (pushPt h.1.w (x3 t₀.G 2)))).trans ?_
      refine Eq.trans ?_ (Category.assoc _ _ _).symm
      exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (congrArg (fun q => q.left) (lift_fst
        (pushPt h.1.w (fst t₀.G t₀.G)) (pushPt h.1.w (snd t₀.G t₀.G)))).symm)
    · refine (congrArg (fun q => q.left) (lift_snd (pushPt h.1.w (x3 t₀.G 1)) (pushPt h.1.w (x3 t₀.G 2)))).trans ?_
      refine Eq.trans ?_ (Category.assoc _ _ _).symm
      exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (congrArg (fun q => q.left) (lift_snd
        (pushPt h.1.w (fst t₀.G t₀.G)) (pushPt h.1.w (snd t₀.G t₀.G)))).symm)
  have hT : ∃ t : LB.Gen (Theta B M.L), t.IsGen :=
    TrivDedekind.exists_gen_of_generic R K (B ⊗ B ⊗ B) hB₃ _ U₃.left _ p₃ (Theta B M.L) (lb _ M.isLB) (exists_gen_theta_zero M.isLB)
      (exists_gen_of_lbIso (lb₀ _) (pull_isLB (lb _ M.isLB) _)
        (lbIso_cube_pull h M.isLB t₀.PP.isLB hM (x3 t₀.G) (x3 B) U₃
          (fun i => by fin_cases i <;> simp [U₃, x3])).symm ⟨t₀.cub.t, t₀.cub.isGen⟩)
  have ha : ∀ a, LBIso (cubeLB B ![fst B B ≫ act.act a, snd B B] M.L)
      (cubeLB B ![fst B B, snd B B ≫ act.act (H.bar a)] M.L) := by
    intro a
    have := act.hom a
    have := act.hom (H.bar a)
    refine IsoDescent.lbIso_of_field R K (algebraMap R K) (IsFractionRing.injective R K) (B ⊗ B) hB₂ _ U₂.left _ p₂ _ _
      (lb _ M.isLB) (lb _ M.isLB) (lbIso_cube_of_eq M.isLB η[B ⊗ B] _ _ fun i => ?_) ?_
    · fin_cases i <;> simp
    · refine LBIso.trans (pull_isLB (lb _ M.isLB) _) (lb₀ _) (pull_isLB (lb _ M.isLB) _)
        (lbIso_cube_pull h M.isLB t₀.PP.isLB hM _ _ U₂ fun i => ?_)
        (LBIso.trans (lb₀ _) (lb₀ _) (pull_isLB (lb _ M.isLB) _) (t₀.adj a)
          (lbIso_cube_pull h M.isLB t₀.PP.isLB hM _ _ U₂ fun i => ?_).symm)
      · fin_cases i
        · exact (pa _ a).trans (by simp [U₂])
        · simp [U₂]
      · fin_cases i
        · simp [U₂]
        · exact (pa _ _).trans (by simp [U₂])
  obtain ⟨PP, cub, sym, hPP, -, prim, adj⟩ :=
    PrimNorm.exists_primitive_normalisation hL.globalFns E H _ B act M.L hB M.isLB hT ha
  let t : SAB H (Sp R) := ⟨B, isSemiAbelian_of_isAbelianScheme B hB, act, PP, cub, sym, adj, prim⟩
  have hφ : LBIso t₀.PP.L (PP.L.pull φ) := by
    let U := pushPt h.1.w (𝟙 t₀.G)
    have eU : U.left = φ := Category.id_comp _
    have h₁ : LBIso ((cubeLB B ![𝟙 B, act.act H.w0] M.L).pull U.left)
        (cubeLB t₀.G ![𝟙 t₀.G, t₀.act.act H.w0] t₀.PP.L) := by
      refine lbIso_cube_pull h M.isLB t₀.PP.isLB hM _ _ U fun i => ?_
      fin_cases i
      · simp [U]
      · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa _ _)
    rw [eU] at h₁
    exact LBIso.trans t₀.PP.isLB (lb₀ _) (pull_isLB PP.isLB _) t₀.prim
      (LBIso.trans (lb₀ _) (pull_isLB (lb _ M.isLB) _) (pull_isLB PP.isLB _) h₁.symm
        (PowPrimitive.lbIso_linComb hPP.symm _ _))
  obtain ⟨m, hm⟩ := CartTriple.exists_tripleMap hL.globalFns E H _ _ _ t₀ t φ (PolPull.isAbelianScheme_of_isGrpPullback hB h) h hact hφ
  exact ⟨t, m, Iso.refl B, inferInstanceAs (IsMonHom (𝟙 B)), (Category.comp_id _).trans hm⟩

end GlobalTheory.CM.TripleModel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsTripleOfAbelianModelDedekindStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_triple_of_abelian_model_dedekind : Out.Laws → (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R K : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (t₀ : SAB H (Sp K)) (B : Over (Sp R)) [GrpObj B] (φ : t₀.G.left ⟶ B.left), IsAbelianScheme B → IsGrpPullback t₀.G B (spMap (algebraMap R K)) φ → ∃ (t : SAB H (Sp R)) (m : SABMap t₀ t (spMap (algebraMap R K))) (e : t.G ≅ B), IsMonHom e.hom ∧ m.φ ≫ e.hom.left = φ := by
  first | exact @GlobalTheory.CM.TripleModel.exists_triple_of_abelian_model | exact GlobalTheory.CM.TripleModel.exists_triple_of_abelian_model | (intros; apply GlobalTheory.CM.TripleModel.exists_triple_of_abelian_model <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLamLettersIsGood
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem exists_lieComb_image {R R' : Type} [CommRing R] [CommRing R'] (A B : Out.PolAV (Sp R)) (x y : KeyIn R')
    (f : Sp R' ⟶ Sp R) (φ : x.P.A.left ⟶ A.A.left) (ψ : y.P.A.left ⟶ B.A.left)
    (hx : IsFibreOf A x f φ) (hy : IsFibreOf B y f ψ) (F : A.A ⟶ B.A) (hF : IsMonHom F) (i : Fin x.P.g) :
    ∃ (u : Fin y.P.g → R') (w : epsR R' ⟶ y.P.A), w.left ≫ ψ = (x.v i).left ≫ φ ≫ F.left ∧ IsLieComb u y.v w := by
  obtain ⟨⟨F', hF', -⟩, hmon⟩ := existsUnique_hom_of_isGrpPullback _ _ f A.A B.A x.P.A y.P.A φ ψ hx.1 hy.1 F
  have hm : IsMonHom F' := hmon F' hF' hF
  have ht : IsTangent (x.v i ≫ F') :=
    ((GlobalTheory.LieCombHom.lieComb_add_pow_map R' x.P.A y.P.A x.P.g x.v x.basis.1).2.2.2 F' hm).1 i
  obtain ⟨u, hu, -⟩ := y.basis.2 _ ht
  exact ⟨u, x.v i ≫ F', by rw [Over.comp_left, Category.assoc, hF'], hu⟩

def blockEquiv {T : Type} (p : T → Prop) [DecidablePred p] (a b : ℕ) {α β : Type} (s : α ≃ {t // p t})
    (s' : β ≃ {t // ¬ p t}) : (Σ t, Fin (if p t then a else b)) ≃ (Fin a × α) ⊕ (Fin b × β) where
  toFun z := if h : p z.1 then Sum.inl (z.2.cast (if_pos h), s.symm ⟨z.1, h⟩)
    else Sum.inr (z.2.cast (if_neg h), s'.symm ⟨z.1, h⟩)
  invFun
    | Sum.inl q => ⟨(s q.2).1, q.1.cast (if_pos (s q.2).2).symm⟩
    | Sum.inr q => ⟨(s' q.2).1, q.1.cast (if_neg (s' q.2).2).symm⟩
  left_inv := by
    rintro ⟨t, i⟩
    by_cases h : p t
    · simp only [dif_pos h]
      refine Sigma.ext (by simp) ?_
      exact (Fin.heq_ext_iff (by simp)).2 rfl
    · simp only [dif_neg h]
      refine Sigma.ext (by simp) ?_
      exact (Fin.heq_ext_iff (by simp)).2 rfl
  right_inv := by
    rintro (q | q)
    · simp [dif_pos (s q.2).2]
    · simp [dif_neg (s' q.2).2]

theorem exists_lamLetters_isGood : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] (H : Host E) (l : Level H) (c : Coeff l) (nΨ n' f : ℕ) (o : LamObj c nΨ n') (La : ℝ), LamObjGood o f La → ∃ L : LamLetters o, L.IsGood ∧ ∀ b : E →+* ℂ, (b (H.rt : E) = H.rt0 → L.m b = nΨ) ∧ (b (H.rt : E) ≠ H.rt0 → L.m b = n') := by
  intro E _ _ _ _ H l c nΨ n' f o La hg
  classical
  obtain ⟨-, -, -, hB, hΨ, h', g1, g2, g3, -, -, -, -, ⟨m1, m2, -⟩, -⟩ := hg
  let p : (E →+* ℂ) → Prop := fun b => b (H.rt : E) = H.rt0
  let ε := blockEquiv p nΨ n' o.τΨ o.τ'
  have hc : Fintype.card ((Fin nΨ × Fin o.xΨ.P.g) ⊕ (Fin n' × Fin o.x'.P.g)) = o.xB.P.g := by
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    rw [g1, g2, g3]; ring
  let κ := Fintype.equivFinOfCardEq hc
  have hU : ∀ q : (Fin nΨ × Fin o.xΨ.P.g) ⊕ (Fin n' × Fin o.x'.P.g),
      ∃ (u : Fin o.xB.P.g → o.K₁) (w : epsR o.K₁ ⟶ o.xB.P.A),
        (match q with
          | Sum.inl q => w.left ≫ o.φB = (o.xΨ.v q.2).left ≫ o.φΨg ≫ (o.φΨ q.1).left
          | Sum.inr q => w.left ≫ o.φB = (o.x'.v q.2).left ≫ o.φ'g ≫ (o.φ' q.1).left) ∧ IsLieComb u o.xB.v w := by
    rintro (q | q)
    · exact exists_lieComb_image _ _ _ _ _ _ _ hΨ hB _ (m1 q.1) q.2
    · exact exists_lieComb_image _ _ _ _ _ _ _ h' hB _ (m2 q.1) q.2
  choose u w hw hu using hU
  refine ⟨⟨fun b => if p b then nΨ else n', ε.trans κ, κ.symm, fun k => u (κ.symm k),
    fun k => Sum.elim (fun q => o.ℓΨ q.2) (fun q => o.ℓ' q.2) (κ.symm k)⟩, ⟨κ.symm.bijective, ?_, ?_, ?_⟩, ?_⟩
  · intro b i
    have : κ.symm ((ε.trans κ) ⟨b, i⟩) = ε ⟨b, i⟩ := by simp
    simp only [this]
    by_cases h : p b
    · have e1 : ε ⟨b, i⟩ = Sum.inl (i.cast (if_pos h), o.τΨ.symm ⟨b, h⟩) := dif_pos h
      rw [e1]; simp
    · have e1 : ε ⟨b, i⟩ = Sum.inr (i.cast (if_neg h), o.τ'.symm ⟨b, h⟩) := dif_neg h
      rw [e1]; simp
  · intro k
    refine ⟨w (κ.symm k), ?_, hu _⟩
    have := hw (κ.symm k)
    unfold LamLetters.IsLetter
    dsimp only
    generalize κ.symm k = q at this ⊢
    cases q <;> exact this
  · intro k
    dsimp only
    generalize κ.symm k = q
    cases q <;> rfl
  · intro b
    exact ⟨fun h => if_pos h, fun h => if_neg h⟩

end GlobalTheory.LamF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmEllipticCurveExistsOfUniformisation
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LatticeUnifFibreEqOfPeriod
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory

theorem lattice_unif_fibre_eq_of_period : ThetaUnifAV → ∀ (R : Type) [CommRing R] (P : Out.PolAV (Sp R)) (v : epsR R ⟶ P.A) (s : R →+* ℂ) (L : PeriodPair) (c₀ ω : ℂ), P.g = 1 → IsTangent v → (∀ (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g) (w' : Fin P'.g → ℂ), IsPolFibre s P P' φ' → IsVecOver s φ' v v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∀ z : ℂ, z ∈ L.lattice ↔ z • w' ∈ u'.Λ) → c₀ ≠ 0 → (∀ z, z ∈ L.lattice ↔ ∃ m n : ℤ, z = c₀ * (m + n * ω)) → ∀ (P' : Out.PolAV (Sp ℂ)) (φ : P'.A.left ⟶ P.A.left), IsPolFibre s P P' φ → ∀ u : HolUnif P'.A P'.L P'.g, ∃ c : ℂ, c ≠ 0 ∧ ∀ z, z ∈ u.Λ ↔ ∃ m n : ℤ, z = fun _ => c * (m + n * ω) := by
  intro hU R _ P v s L c₀ ω hg hv H hc hL P' φ hφ u
  obtain ⟨v', hv', -⟩ := existsUnique_isVecOver hφ.2.1.1 v
  have htan : IsTangent v' := IsVecOver.isTangent hφ.2.1 hv' hv
  obtain ⟨w, hw, -⟩ := (GlobalTheory.T.holomorphicUniformisation_tangent_unimodular_riemannForm hU P' u).1 v' htan
  obtain ⟨hw0, hwL⟩ := H P' φ v' u w hφ hv' hw

  have hg' : P'.g = 1 := hφ.1.trans hg
  have i0 : Fin P'.g := ⟨0, by omega⟩
  have : Subsingleton (Fin P'.g) := by rw [hg']; infer_instance
  have hwi : w i0 ≠ 0 := by
    intro h
    apply hw0
    funext i
    rw [Subsingleton.elim i i0, h]
    rfl
  refine ⟨c₀ * w i0, mul_ne_zero hc hwi, fun z => ?_⟩
  obtain ⟨t, ht⟩ : ∃ t, t = z i0 / w i0 := ⟨_, rfl⟩
  have hz : z = t • w := by
    funext i
    rw [Subsingleton.elim i i0, Pi.smul_apply, smul_eq_mul, ht, div_mul_cancel₀ _ hwi]
  constructor
  · intro hzm
    rw [hz] at hzm
    obtain ⟨m, n, hmn⟩ := (hL t).1 ((hwL t).2 hzm)
    refine ⟨m, n, ?_⟩
    rw [hz]
    funext i
    rw [Subsingleton.elim i i0, Pi.smul_apply, smul_eq_mul, hmn]
    ring
  · rintro ⟨m, n, hmn⟩
    have hzi : z i0 = c₀ * w i0 * (m + n * ω) := congrFun hmn i0
    have htL : t ∈ L.lattice := by
      rw [hL]
      refine ⟨m, n, ?_⟩
      rw [ht, hzi]
      field_simp
    rw [hz]
    exact (hwL t).1 htL

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmEllipticCurveExistsOfUniformisation
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory

theorem half_one_add_sqrt_quadratic {K : Type} [Field K] [CharZero K] {d : ℕ} (h4 : d % 4 = 3) {r w : K}
    (hr : r ^ 2 = -(d : K)) (hw : 2 * w = 1 + r) : w * w + (((1 + d) / 4 : ℕ) : K) = w := by
  have e : 4 * ((1 + d) / 4) = 1 + d := by omega
  have e' : (4 : K) * (((1 + d) / 4 : ℕ) : K) = 1 + d := by exact_mod_cast congrArg (Nat.cast : ℕ → K) e
  have e4 : (4 : K) ≠ 0 := by norm_num
  refine mul_left_cancel₀ e4 ?_
  have hr' : r = 2 * w - 1 := by linear_combination -hw
  subst hr'
  linear_combination e' + hr

theorem cmCurve_of_uniformisation : ThetaUnifAV → Out.PolBaseChangeSt → (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → CMCurve := by
  intro hU hB hE d _ hs h4 K _ _ h2 ⟨r, hr⟩
  obtain ⟨w, bar, hw, -, hgen, hσ, σ₀, hσ₀⟩ := ringOfIntegers_sqrt_neg_three_mod_four d hs h4 K h2 r hr
  have hnr := (hσ σ₀).1
  choose 𝔟 h𝔟 using ClassGroup.mk0_surjective (R := 𝓞 K)
  obtain ⟨M, hM, κ, P, v, L₀, Q, t, L, δ, hκ, hP, hQ, hδ, hc, hβ⟩ := GlobalTheory.T.exists_numberField_defining_cm_curve_homs hU hB K h2 σ₀ hnr 𝔟
    (exists_cm_curves_of_weierstrass_curves (GlobalTheory.T.exists_ellipticCurve_polarised_lattice_family hU hB) K h2 σ₀ hnr 𝔟)
  have hv : IsTangent v := hP.2.1.1 0
  have hwc : ((κ (w : K) : M) : ℂ) = (1 + Complex.I * √d) / 2 := by
    have e := congrArg σ₀ hw
    rw [map_mul, map_add (f := _), map_one, map_ofNat, hσ₀] at e
    rw [hκ]
    linear_combination e / 2
  refine ⟨M, hM, κ (w : K), P, v, hwc, hP.1, hP.2.1, ?_, ?_, fun s => ?_,
    GlobalTheory.T.mean_log_lieNormSq_eq_mean_log_eta_alt hU hB hE K h2 σ₀ hnr 𝔟 h𝔟 M κ P v L₀ Q t L δ ⟨hκ, hP, hQ, hδ, hc⟩ hβ⟩
  · obtain ⟨P₀, φ, hφ⟩ := exists_isPolFibre hB (algebraMap (𝓞 M) M) P
    obtain ⟨v₀, hv₀, -⟩ := existsUnique_isVecOver hφ.2.1.1 v
    obtain ⟨β, -, hend, -⟩ := hβ
    obtain ⟨W, hW, hWv⟩ := hend w P₀ P₀ φ φ v₀ v₀ hφ hφ hv₀ hv₀
    have hP₀ := GlobalTheory.T.ellipticCurve_lattice_baseChange_stable _ P v L₀ M _ P₀ φ v₀ hP hφ hv₀
    refine ⟨P₀, φ, v₀, W, hφ, hv₀, hP₀.2.1, hW, ?_, hWv⟩
    refine LieMultiple.quadratic_equation_of_derivative hU hB M (algebraMap M ℂ) P₀ v₀ W _ _ (hP₀.2.1.1 0)
      hP₀.2.2.1 hW hWv ?_
    have e := congrArg κ (half_one_add_sqrt_quadratic h4 hr hw)
    rwa [map_add, map_mul, map_natCast] at e
  · obtain ⟨c, hc0, hc⟩ := hc
    refine lattice_unif_fibre_eq_of_period hU _ P v _ (L₀ _) c _ hP.1 hv (hP.2.2.2 _) hc0 fun z => ?_
    rw [hc, hκ]
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨m, n, rfl⟩ := hgen a
      exact ⟨m, n, by simp⟩
    · rintro ⟨m, n, rfl⟩
      exact ⟨m + n * w, by simp⟩
  · exact ⟨_, isLieNormSq_iff_eq_pi_div_covolume hU hB _ P v _ (L₀ _) hP.1 hv (hP.2.2.2 _)⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmEllipticCurveExistsOfUniformisationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmEllipticCurve_exists_of_uniformisation : ThetaUnifAV → Out.PolBaseChangeSt → (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → CMCurve := by
  first | exact @GlobalTheory.cmCurve_of_uniformisation | exact GlobalTheory.cmCurve_of_uniformisation | (intros; apply GlobalTheory.cmCurve_of_uniformisation <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LambdaBundleIsoOfWeilPairingCompatible
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LambdaBundleIsoOfWeilPairingCompatible
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section

namespace GlobalTheory.CM.LamOfWeil

open ReciprocityTheory.ChartRestriction.G.Out CommutatorPairing DescentPairing IsoDescent

section

variable {S : Scheme.{0}} {A T T' : Over S} [GrpObj A] [IsCommMonObj A]

abbrev sqφ (a b : T ⟶ A) : ULift.{0} (Finset (Fin 2)) → (T.left ⟶ A.left) := fun I => (psum A ![a, b] I.down).left

abbrev sqε : ULift.{0} (Finset (Fin 2)) → ℤ := fun I => (-1) ^ (2 - I.down.card)

theorem prod_sq (ρ : T' ⟶ T) (a b : T ⟶ A) {U : Type} [CommGroup U] (h : (T'.left ⟶ A.left) → U) :
    ∏ I, h (ρ.left ≫ sqφ a b I) ^ sqε I =
      h ((ρ ≫ a) * (ρ ≫ b)).left * (h (ρ ≫ a).left)⁻¹ * (h (ρ ≫ b).left)⁻¹ * h (1 : T' ⟶ A).left := by
  have p := NormRos.prod_square a b (fun q => h (ρ.left ≫ q))
  simp only [← Over.comp_left, MonObj.comp_mul, MonObj.comp_one] at p
  exact p

theorem exists_gen_axis {L : LB A.left} (hL : L.IsLB) (ρ : T' ⟶ T) (a b : T ⟶ A) (H : ρ ≫ a = 1 ∨ ρ ≫ b = 1) :
    ∃ t : LB.Gen (LB.LinComb L (fun I => ρ.left ≫ sqφ a b I) sqε), t.IsGen :=
  AdjointOfPairing.exists_gen_of_formEq_zero hL fun U _ h => by
    rw [prod_sq]
    rcases H with H | H
    · rw [H, _root_.one_mul]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one]
      abel
    · rw [H, _root_.mul_one]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one]
      abel

end

theorem exists_gen_div {X X' Y Y' : Scheme.{0}} {K K' : Type} [Fintype K] [Fintype K'] (L : LB X) (L' : LB X')
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X')) (ε' : K' → ℤ) (f : Y' ⟶ Y)
    (H : LBIso (LB.LinComb L (fun k => f ≫ φ k) ε) (LB.LinComb L' (fun k => f ≫ φ' k) ε')) :
    ∃ t : LB.Gen ((LB.div (LB.LinComb L' φ' ε') (LB.LinComb L φ ε)).pull f), t.IsGen := by
  obtain ⟨w, hw⟩ := H.chartPull (chartPullOut L φ ε f _ fun _ => rfl) (chartPullOut L' φ' ε' f _ fun _ => rfl)
  exact gen_chartPull (IsoDescent.chartPullDiv _ _ f) w hw

variable {k : Type} [Field k] {X Y : Over (Sp k)} [GrpObj X] [GrpObj Y]

theorem exists_gen_fibre (hG : GlobalFnsSt) (hC : CubeSt) (P : PolAV (Sp k)) (f₁ : X ⟶ P.A) (f₂ : Y ⟶ P.A)
    [IsMonHom f₁] [IsMonHom f₂] (n : ℕ) (x : 𝟙_ (Over (Sp k)) ⟶ X) (hx : x ^ n = 1) :
    ∃ u : LB.Gen (LB.LinComb P.L (fun I => (mulA Y n).left ≫ (lift (toUnit Y ≫ x) (𝟙 Y)).left ≫
        sqφ (fst X Y ≫ f₁) (snd X Y ≫ f₂) I) sqε),
      u.IsGen ∧ ∀ (y : 𝟙_ (Over (Sp k)) ⟶ Y) (c : Γ((𝟙_ (Over (Sp k))).left, ⊤)ˣ), y ^ n = 1 →
        WeilIs P.A P.L n (x ≫ f₁) (y ≫ f₂) c → ∀ (z : Y.left) (J), Good P.L z J →
          val u ((toUnit Y ≫ y) * 𝟙 Y).left z J = val u (𝟙 _) z J * gm (toUnit Y).left z ⊤ c := by
  have := P.isAb.comm
  obtain ⟨rig, hrig⟩ := P.rigid
  let L : RigLB P.A := ⟨P.L, rig, P.isLB, hrig⟩
  obtain ⟨⟨cb⟩, -⟩ := hC _ P L rfl
  let T := 𝟙_ (Over (Sp k))
  let p₀ : T.left := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k)
  have hT : ∀ p : T.left, p = p₀ := fun p => Subsingleton.elim (α := PrimeSpectrum k) p p₀
  have hx₁ : (x ≫ f₁) ^ n = 1 := by rw [← MonObj.pow_comp, hx, MonObj.one_comp]
  obtain ⟨u₀, hu₀, v₀⟩ := PairingDetermines.exists_gen_transl hG P.isAb cb p₀ hT n (x ≫ f₁) hx₁
  obtain ⟨σ, hσ⟩ := exists_frame P.isLB (K := Fin 2) ![(x ≫ f₁).left, (1 : T ⟶ P.A).left] ![-1, 1] p₀ hT
  obtain ⟨u, hu, v⟩ := exists_gen P.isLB
    (φ' := fun I => (mulA Y n).left ≫ (lift (toUnit Y ≫ x) (𝟙 Y)).left ≫
      sqφ (fst X Y ≫ f₁) (snd X Y ≫ f₂) I) (ε' := sqε)
    (fun U _ h => by
      have e₀ : mulA Y n ≫ lift (toUnit Y ≫ x) (𝟙 Y) = lift (toUnit Y ≫ x) (𝟙 Y ^ n) := by
        rw [comp_lift, comp_toUnit_assoc, Category.comp_id]
      have e₁ : lift (toUnit Y) f₂ ≫ mulT P.A T n ≫ translPt P.A (x ≫ f₁) =
          (toUnit Y ≫ x ≫ f₁) * ((𝟙 Y ^ n) ≫ f₂) := by
        rw [← Category.assoc, mulT, comp_lift, lift_translPt, lift_fst, MonObj.comp_pow, lift_snd,
          MonObj.pow_comp, Category.id_comp]
      have e₂ : lift (toUnit Y) f₂ ≫ snd T P.A ^ n = (𝟙 Y ^ n) ≫ f₂ := by
        rw [MonObj.comp_pow, lift_snd, MonObj.pow_comp, Category.id_comp]
      have e₃ : toUnit Y ≫ (1 : T ⟶ P.A) = 1 := MonObj.comp_one _
      have e := prod_sq (lift (toUnit Y ≫ x) (𝟙 Y ^ n)) (fst X Y ≫ f₁) (snd X Y ≫ f₂) h
      rw [lift_fst_assoc, lift_snd_assoc, Category.assoc] at e
      refine Eq.trans ?_ (e.symm.trans (Finset.prod_congr rfl fun I _ => by
        rw [← e₀, Over.comp_left, Category.assoc]))
      refine (Fintype.prod_sum_type _).trans ?_
      simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ, ← Over.comp_left, e₁, e₂, e₃, Category.assoc, zpow_neg, zpow_one, _root_.mul_one]
      ac_rfl)
    (LB.mulGen P.L _ _ _ _ (LB.pullGen P.L _ _ u₀ (lift (toUnit Y) f₂).left) (LB.pullGen P.L _ _ σ (toUnit Y).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu₀ _) (DVR.pullGen_isGen _ _ _ _ hσ _))
  refine ⟨u, hu, fun y c hy hc z J hJ => ?_⟩
  have hy₂ : (y ≫ f₂) ^ n = 1 := by rw [← MonObj.pow_comp, hy, MonObj.one_comp]
  have w : ∀ a : Y ⟶ Y, val u a.left z J =
      val u₀ (lift (toUnit Y) (a ≫ f₂)).left z J * val σ (toUnit Y).left z J := fun a => by
    rw [v _ _ z J hJ, val_mul hJ, val_pull hJ, val_pull hJ, ← Over.comp_left, ← Over.comp_left, comp_lift,
      comp_toUnit]
  have w₀ := v₀ (y ≫ f₂) c hy₂ hc Y (toUnit Y) (𝟙 Y ≫ f₂) z J hJ
  refine (w _).trans (Eq.trans ?_ (congrArg (· * _) (w (𝟙 Y))).symm)
  rw [MonObj.mul_comp, Category.assoc, mul_right_comm]
  exact congrArg (fun q => q * _) w₀

end GlobalTheory.CM.LamOfWeil

namespace GlobalTheory.CM

open LamOfWeil IsoDescent

theorem lamEq_of_weilEq : Out.Laws → ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (X Y A B : Out.PolAV (Sp k)) (f₁ : X.A ⟶ A.A) (f₂ : Y.A ⟶ A.A) (g₁ : X.A ⟶ B.A) (g₂ : Y.A ⟶ B.A), IsMonHom f₁ → IsMonHom f₂ → IsMonHom g₁ → IsMonHom g₂ → WeilEq A.L f₁ f₂ B.L g₁ g₂ (𝟙 (Sp k)) → LamEq A.L f₁ f₂ B.L g₁ g₂ := by
  intro hL k _ _ _ X Y A B f₁ f₂ g₁ g₂ hf₁ hf₂ hg₁ hg₂ hW
  haveI : IsCommMonObj A.A := A.isAb.comm
  haveI : IsCommMonObj B.A := B.isAb.comm
  haveI : IsCommMonObj Y.A := Y.isAb.comm
  have axis : ∀ {Z : Over (Sp k)} (ρ : Z ⟶ X.A ⊗ Y.A), ρ ≫ fst _ _ = 1 ∨ ρ ≫ snd _ _ = 1 →
      ∃ t : LB.Gen ((LB.div (LB.LinComb B.L (sqφ (fst X.A Y.A ≫ g₁) (snd X.A Y.A ≫ g₂)) sqε)
        (LB.LinComb A.L (sqφ (fst X.A Y.A ≫ f₁) (snd X.A Y.A ≫ f₂)) sqε)).pull ρ.left), t.IsGen := by
    intro Z ρ H
    obtain ⟨u, hu⟩ := exists_gen_axis A.isLB ρ (fst X.A Y.A ≫ f₁) (snd X.A Y.A ≫ f₂)
      (H.imp (fun h => by rw [reassoc_of% h, MonObj.one_comp]) (fun h => by rw [reassoc_of% h, MonObj.one_comp]))
    obtain ⟨u', hu'⟩ := exists_gen_axis B.isLB ρ (fst X.A Y.A ≫ g₁) (snd X.A Y.A ≫ g₂)
      (H.imp (fun h => by rw [reassoc_of% h, MonObj.one_comp]) (fun h => by rw [reassoc_of% h, MonObj.one_comp]))
    exact exists_gen_div _ _ _ _ _ _ _ (lbIso_of_gens A.isLB B.isLB _ _ _ _ u hu u' hu')
  refine T.seesaw_triviality_on_dense_fibres_product_abelian hL.globalFns k X.A Y.A
    (LB.div (LB.LinComb B.L (sqφ (fst X.A Y.A ≫ g₁) (snd X.A Y.A ≫ g₂)) sqε)
      (LB.LinComb A.L (sqφ (fst X.A Y.A ≫ f₁) (snd X.A Y.A ≫ f₂)) sqε)) Y.L X.isAb Y.isAb Y.isLB Y.ample
    (LB.isLB_div (DVR.linComb_isLB _ B.isLB _ _) (DVR.linComb_isLB _ A.isLB _ _))
    (axis _ (Or.inl (lift_fst _ _))) ?_ (axis _ (Or.inr (lift_snd _ _)))
  refine (TorsionDense.dense_torsion X hL.irred hL.kerPow).mono (Set.biUnion_subset_biUnion_left ?_)
  rintro x ⟨n, hn, hx⟩
  obtain ⟨u, hu, v⟩ := exists_gen_fibre hL.globalFns hL.cube A f₁ f₂ n x hx
  obtain ⟨u', hu', v'⟩ := exists_gen_fibre hL.globalFns hL.cube B g₁ g₂ n x hx
  refine exists_gen_div _ _ _ _ _ _ _ ?_
  refine lbIso_of_invariant A.isLB B.isLB _ _ _ _ (Out.mulA Y.A n).left
    (I := {y : 𝟙_ (Over (Sp k)) ⟶ Y.A // y ^ n = 1}) (fun y => ((toUnit Y.A ≫ y.1) * 𝟙 Y.A).left) (fun y => ?_)
    (fun U f hf => torsion_invariant_descends (fun S _ P n hn => by
      obtain ⟨a, b, c, e, -⟩ := hL.mulN S P n hn
      exact ⟨a, b, c, e⟩) k Y n (Nat.cast_ne_zero.2 hn.ne') U f fun y hy => hf ⟨y, hy⟩) u hu u' hu'
    (fun y z J J' hJ hJ' => ?_)
  · rw [← Over.comp_left, Out.mulA, MonObj.comp_pow, Category.comp_id, mul_pow, ← MonObj.comp_pow, y.2,
      MonObj.comp_one, _root_.one_mul]
  · have hx₁ : (x ≫ f₁) ^ n = 1 := by rw [← MonObj.pow_comp, hx, MonObj.one_comp]
    have hy₂ : (y.1 ≫ f₂) ^ n = 1 := by rw [← MonObj.pow_comp, y.2, MonObj.one_comp]
    obtain ⟨c, hc, -⟩ := (hL.weil _ A n _).1 (x ≫ f₁) (y.1 ≫ f₂) hx₁ hy₂
    obtain ⟨c, rfl⟩ : ∃ c₀ : kˣ, unitOn c₀ = c :=
      ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom.toMonoidHom c,
        Units.ext ((Scheme.ΓSpecIso (CommRingCat.of k)).hom_inv_id_apply c.val)⟩
    have h₁ := v y.1 (unitOn c) y.2 hc z J hJ
    have h₂ := v' y.1 (unitOn c) y.2 ((hW n x y.1 c hn hx y.2).1 hc) z J' hJ'
    refine (congrArg₂ (fun a b => a * b⁻¹) h₂ h₁).trans ?_
    exact mul_div_mul_right_eq_div _ _ _ |> fun h => by simpa only [div_eq_mul_inv] using h

end GlobalTheory.CM

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LambdaBundleIsoOfWeilPairingCompatibleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lambdaBundleIso_of_weilPairing_compatible : Out.Laws → ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (X Y A B : Out.PolAV (Sp k)) (f₁ : X.A ⟶ A.A) (f₂ : Y.A ⟶ A.A) (g₁ : X.A ⟶ B.A) (g₂ : Y.A ⟶ B.A), IsMonHom f₁ → IsMonHom f₂ → IsMonHom g₁ → IsMonHom g₂ → WeilEq A.L f₁ f₂ B.L g₁ g₂ (𝟙 (Sp k)) → LamEq A.L f₁ f₂ B.L g₁ g₂ := by
  first | exact @GlobalTheory.CM.lamEq_of_weilEq | exact GlobalTheory.CM.lamEq_of_weilEq | (intros; apply GlobalTheory.CM.lamEq_of_weilEq <;> assumption)
end
end
