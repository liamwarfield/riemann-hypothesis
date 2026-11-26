module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCoverOpenImmersionNormalisedThetaClosure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerFirstFactorThetaModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantBundlePowEightIsoDetHodgePowFour
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealisedThetaSystemNormalLevelModelStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCoverImageOpenFiniteOverModuli
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelThetaMapDeepLevelFiniteFibres
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxFamilyLinearIndependentProductDegeneration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeBundlePowerIsoMinimalSiegelCompactification

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalProjectiveToricMinorModel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalProjectiveToricMinorModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section

namespace GlobalTheory.SiegJoin

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem isUnit_of_isHom {X M : RatModel o Ω} {f : M.Z ⟶ X.Z} (hf : X.IsHom M (AlgHom.id o Ω) f) {z : M.Z} {y : Ω}
    (hy : y ∈ X.O (f z)) (hu : IsUnit (⟨y, hf.map_mem_O hy⟩ : M.O z)) : IsUnit (⟨y, hy⟩ : X.O (f z)) := by
  obtain ⟨U, a, hz, rfl⟩ := hy
  rw [RatModel.isUnit_valF_iff hz]
  have hz' : z ∈ f ⁻¹ᵁ U := hz
  have e : (⟨valF X.pt U a, hf.map_mem_O ⟨U, a, hz, rfl⟩⟩ : M.O z) =
      ⟨valF M.pt (f ⁻¹ᵁ U) (f.app U a), RatModel.valF_mem_O hz' _⟩ :=
    Subtype.ext (hf.valF_app ⟨_, hz⟩ a).symm
  rw [e, RatModel.isUnit_valF_iff hz', ← Scheme.preimage_basicOpen] at hu
  exact hu

theorem div_iff_of_isHom {X M : RatModel o Ω} {f : M.Z ⟶ X.Z} (hf : X.IsHom M (AlgHom.id o Ω) f) {J : Type}
    {t : J → Ω} (hX : X.HasDiv t) (z : M.Z) (x : J) : M.Div t x z ↔ X.Div t x (f z) := by
  obtain ⟨i, hi⟩ := hX (f z)
  have hi' : M.Div t i z := hf.div hi
  refine ⟨fun hx => ?_, fun hx => hf.div hx⟩
  rw [hi.div_iff_isUnit]
  exact isUnit_of_isHom hf (hi.2 x) ((hi'.div_iff_isUnit x).1 hx)

end GlobalTheory.SiegJoin

namespace GlobalTheory.SiegJoin

theorem minor_model : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real), S.Big → Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j, x = S.th j / S.th i})) Ω → ∃ (X M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (f : M.Z ⟶ X.Z) (Xab : X.Z.Opens) (Zh : ZHOut ρ M U₀ EE), MinorAt S X M U₀ EE f Xab ∧ IsOpen (abLocus Zh.G) ∧ (abLocus Zh.G : Set M.Z) = f ⁻¹' (Xab : Set X.Z) := by
  intro o Ω _ _ _ _ S ρ hB hfin
  have hL := GlobalTheory.abelianSchemeLaws_all
  have hT : S.HasTests := (GlobalTheory.T.thetaSystem_hasTests_of_real_point GlobalTheory.T.semistableReduction_ppav_padicField GlobalTheory.T.uniformisationExistence_and_torsion_statements.1 hL.1 hL.2 GlobalTheory.T.uniformisationExistence_and_torsion_statements.2 o Ω S ρ).1
  obtain ⟨n, a, GG, X, M, U₀, EE, f, Xab, hNm, hP, -, hO, hE, hH, hXab, hI, hgen, -⟩ := GlobalTheory.T.exists_normal_model_theta_tuple_maximal_minors o Ω S hT hfin
  obtain ⟨Zh⟩ := GlobalTheory.T.zarhinGeometric_of_semistableReduction GlobalTheory.T.semistableReduction_ppav_padicField o Ω S ρ hB M U₀ EE hO hE ⟨n, a, GG, hgen⟩
  have hsupI : ∀ z : M.Z, S.supI M z = S.supI X (f z) := fun z =>
    Set.ext fun x => div_iff_of_isHom hH hNm.1 z x
  have key : (abLocus Zh.G : Set M.Z) = f ⁻¹' (Xab : Set X.Z) := by
    rw [Zh.ab, hXab]
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_preimage, ThetaSys.TT, ThetaSys.HH, hsupI z]
  refine ⟨X, M, U₀, EE, f, Xab, Zh, ⟨hNm, hP, (GlobalTheory.isNormalScheme_iff_pred _).1 hNm.isNormalScheme, hO, hE, hH, hXab, hI⟩, ?_, key⟩
  rw [key]
  exact Xab.isOpen.preimage f.continuous

end GlobalTheory.SiegJoin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalProjectiveToricMinorModelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normal_projective_toric_minor_model : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real), S.Big → Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j, x = S.th j / S.th i})) Ω → ∃ (X M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (f : M.Z ⟶ X.Z) (Xab : X.Z.Opens) (Zh : ZHOut ρ M U₀ EE), MinorAt S X M U₀ EE f Xab ∧ IsOpen (abLocus Zh.G) ∧ (abLocus Zh.G : Set M.Z) = f ⁻¹' (Xab : Set X.Z) := by
  first | exact @GlobalTheory.SiegJoin.minor_model | exact GlobalTheory.SiegJoin.minor_model | (intros; apply GlobalTheory.SiegJoin.minor_model <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalSchemeExtensionThroughFiniteCover
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionOfFinite
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.FiniteSectionLift

theorem exists_section_of_finite (R A K : CommRingCat) (φ : R ⟶ K)
    (hinj : Function.Injective φ.hom)
    (hint : ∀ x : K, φ.hom.IsIntegralElem x → ∃ r : R, φ.hom r = x)
    (g : R ⟶ A) (hg : g.hom.Finite) (f : A ⟶ K) (hf : g ≫ f = φ) :
    ∃ s : A ⟶ R, g ≫ s = 𝟙 R ∧ s ≫ φ = f := by
  have hmem : ∀ a, f.hom a ∈ φ.hom.range := by
    intro a
    obtain ⟨q, hq, h0⟩ := hg.to_isIntegral a
    obtain ⟨r, hr⟩ := hint (f.hom a) ⟨q, hq, by
      rw [← hf, CommRingCat.hom_comp, ← Polynomial.hom_eval₂, h0, map_zero]⟩
    exact ⟨r, hr⟩
  let e : R ≃+* φ.hom.range := RingEquiv.ofBijective φ.hom.rangeRestrict
    ⟨fun a b h => hinj (congrArg Subtype.val h), φ.hom.rangeRestrict_surjective⟩
  let t : A →+* R := e.symm.toRingHom.comp (f.hom.codRestrict φ.hom.range hmem)
  have hkey : ∀ a, φ.hom (t a) = f.hom a := by
    intro a
    have h1 : e (e.symm ⟨f.hom a, hmem a⟩) = ⟨f.hom a, hmem a⟩ := e.apply_symm_apply _
    exact congrArg Subtype.val h1
  refine ⟨CommRingCat.ofHom t, ?_, ?_⟩
  · ext r
    apply hinj
    change φ.hom (t (g.hom r)) = φ.hom r
    rw [hkey, ← hf]
    rfl
  · ext a
    exact hkey a

theorem lift_of_finite : ∀ (R K : CommRingCat) (φ : R ⟶ K),
    Function.Injective (⇑(CommRingCat.Hom.hom φ) : (↑R : Type) → (↑K : Type)) →
    (∀ (x : (↑K : Type)), RingHom.IsIntegralElem (CommRingCat.Hom.hom φ) x →
      ∃ (r : (↑R : Type)), (CommRingCat.Hom.hom φ : (↑R : Type) → (↑K : Type)) r = x) →
    ∀ (Z P : AlgebraicGeometry.Scheme) (p : Z ⟶ P) (ξ₀ : AlgebraicGeometry.Spec R ⟶ P)
      (y : AlgebraicGeometry.Spec K ⟶ Z), AlgebraicGeometry.IsFinite p →
      CategoryTheory.CategoryStruct.comp y p =
        CategoryTheory.CategoryStruct.comp (AlgebraicGeometry.Spec.map φ) ξ₀ →
      ∃ (ξ : AlgebraicGeometry.Spec R ⟶ Z),
        CategoryTheory.CategoryStruct.comp (AlgebraicGeometry.Spec.map φ) ξ = y ∧
        CategoryTheory.CategoryStruct.comp ξ p = ξ₀ := by
  intro R K φ hinj hint Z P p ξ₀ y hp hy
  haveI : IsAffine (pullback p ξ₀) := isAffine_of_isAffineHom (pullback.snd p ξ₀)
  let l : Spec K ⟶ pullback p ξ₀ := pullback.lift y (Spec.map φ) hy
  let g : R ⟶ Γ(pullback p ξ₀, ⊤) :=
    Spec.preimage ((pullback p ξ₀).isoSpec.inv ≫ pullback.snd p ξ₀)
  let f : Γ(pullback p ξ₀, ⊤) ⟶ K := Spec.preimage (l ≫ (pullback p ξ₀).isoSpec.hom)
  have hgS : Spec.map g = (pullback p ξ₀).isoSpec.inv ≫ pullback.snd p ξ₀ := Spec.map_preimage _
  have hfS : Spec.map f = l ≫ (pullback p ξ₀).isoSpec.hom := Spec.map_preimage _
  have hgfin : g.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hgS]
    infer_instance
  have hf : g ≫ f = φ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hfS, hgS]
    simp only [l, Category.assoc, Iso.hom_inv_id_assoc]
    exact pullback.lift_snd _ _ _
  obtain ⟨s, hs1, hs2⟩ := exists_section_of_finite R _ K φ hinj hint g hgfin f hf
  refine ⟨Spec.map s ≫ (pullback p ξ₀).isoSpec.inv ≫ pullback.fst p ξ₀, ?_, ?_⟩
  · rw [← Category.assoc, ← Spec.map_comp, hs2, hfS]
    simp only [l, Category.assoc, Iso.hom_inv_id_assoc]
    exact pullback.lift_fst _ _ _
  · rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc _ (pullback.snd p ξ₀),
      ← hgS, ← Category.assoc, ← Spec.map_comp, hs1, Spec.map_id, Category.id_comp]

end GlobalTheory.FiniteSectionLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalSchemeExtensionThroughFiniteCover
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.NormalFiniteLift

theorem finite_lift_of_integral (R K : CommRingCat.{0}) (φ : R ⟶ K) (hinj : Function.Injective φ.hom)
    (H : ∀ x : K, φ.hom.IsIntegralElem x → ∃ r : R, φ.hom r = x)
    (Z P : Scheme.{0}) (p : Z ⟶ P) (ξ₀ : Spec R ⟶ P) (y : Spec K ⟶ Z)
    (hp : IsFinite p) (hy : y ≫ p = Spec.map φ ≫ ξ₀) :
    ∃ ξ : Spec R ⟶ Z, Spec.map φ ≫ ξ = y ∧ ξ ≫ p = ξ₀ := by
  first
  | exact @_root_.GlobalTheory.FiniteSectionLift.lift_of_finite
  | exact _root_.GlobalTheory.FiniteSectionLift.lift_of_finite
  | (apply _root_.GlobalTheory.FiniteSectionLift.lift_of_finite <;> assumption)
  | (intros; apply _root_.GlobalTheory.FiniteSectionLift.lift_of_finite <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FiniteSectionLift.lift_of_finite <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FiniteSectionLift.lift_of_finite ..)

theorem isDominant_of_generic {T S : Scheme.{0}} [IsIntegral S] (r : T ⟶ S) [IsOpenImmersion r]
    (K : CommRingCat.{0}) [IsLocalRing K] (w : Spec K ⟶ T)
    (hw : r (w (IsLocalRing.closedPoint K)) = genericPoint S) : IsDominant w := by
  refine ⟨?_⟩
  rw [DenseRange, dense_iff_inter_open]
  rintro O hO ⟨t, ht⟩
  obtain ⟨t', ht', e⟩ : genericPoint S ∈ r '' O :=
    ((genericPoint_spec S).mem_open_set_iff (r.isOpenEmbedding.isOpenMap O hO)).2 ⟨r t, Set.mem_univ _, t, ht, rfl⟩
  refine ⟨w (IsLocalRing.closedPoint K), ?_, ⟨_, rfl⟩⟩
  rw [← r.isOpenEmbedding.injective (e.trans hw.symm)]
  exact ht'

end GlobalTheory.NormalFiniteLift

namespace GlobalTheory.NormalFiniteLift

theorem exists_lift_of_finite : ∀ (o : Type) [CommRing o] (N : ℕ) (S' X Z : Scheme.{0}) (U : S'.Opens)
    (c : U.toScheme ⟶ X) (i : X ⟶ Z) (p : Z ⟶ PSpace o N) (h : S' ⟶ PSpace o N), IsIntegral S' →
    Geo.Tor.IsNormalScheme S' → IsIntegral Z → Dense (U : Set S') → IsDominant c → IsFinite p →
    IsOpenImmersion i → Dense (Set.range i) → U.ι ≫ h = c ≫ i ≫ p →
    ∃ π : S' ⟶ Z, U.ι ≫ π = c ≫ i ∧ π ≫ p = h := by
  intro o _ N S' X Z U c i p h _ hN _ hU _ hp _ _ e
  have := GlobalTheory.IsNormalScheme.of_pred hN
  have hη : ∀ V : S'.Opens, (V : Set S').Nonempty → genericPoint S' ∈ V := fun V hV =>
    ((genericPoint_spec S').mem_open_set_iff V.isOpen).2 (by simpa using hV)
  have hηU : genericPoint S' ∈ U := hη U hU.nonempty
  let gS : Spec S'.functionField ⟶ S' := S'.fromSpecStalk (genericPoint S')
  have hgS : gS (IsLocalRing.closedPoint S'.functionField) = genericPoint S' := Scheme.fromSpecStalk_closedPoint
  have hrO : ∀ O : S'.Opens, genericPoint S' ∈ O → Set.range gS ⊆ Set.range O.ι := by
    rintro O hO _ ⟨q, rfl⟩
    rw [Scheme.Opens.range_ι]
    have : gS q ⤳ genericPoint S' := (S'.range_fromSpecStalk (x := genericPoint S')).le ⟨q, rfl⟩
    exact this.mem_open O.isOpen hO
  let gO : ∀ O : S'.Opens, genericPoint S' ∈ O → (Spec S'.functionField ⟶ O.toScheme) := fun O hO =>
    IsOpenImmersion.lift O.ι gS (hrO O hO)
  have hgO : ∀ O hO, gO O hO ≫ O.ι = gS := fun O hO => IsOpenImmersion.lift_fac _ _ _
  let y : Spec S'.functionField ⟶ Z := gO U hηU ≫ c ≫ i
  have hy : y ≫ p = gS ≫ h := by
    simp only [y, Category.assoc, ← e]
    rw [← Category.assoc, hgO U hηU]

  have loc : ∀ (V : S'.Opens) (hV : IsAffineOpen V) (hηV : genericPoint S' ∈ V),
      ∃ m : V.toScheme ⟶ Z, m ≫ p = V.ι ≫ h ∧ gO V hηV ≫ m = y := by
    intro V hV hηV
    have : Nonempty V := ⟨⟨_, hηV⟩⟩
    have : IsIntegrallyClosed Γ(S', V) := GlobalTheory.IsNormalScheme.isIntegrallyClosed_of_isAffineOpen hV
    have : IsFractionRing Γ(S', V) S'.functionField := functionField_isFractionRing_of_isAffineOpen S' V hV
    have hsp : Spec.map (S'.germToFunctionField V) ≫ hV.fromSpec = gS :=
      hV.fromSpecStalk_eq_fromSpecStalk hηV
    obtain ⟨ξ, h1, h2⟩ := finite_lift_of_integral Γ(S', V) S'.functionField (S'.germToFunctionField V)
      (S'.germToFunctionField_injective V) (fun x hx => IsIntegrallyClosed.isIntegral_iff.1 hx) Z _ p
      (hV.fromSpec ≫ h) y hp (by rw [hy, ← Category.assoc, hsp])
    have hg : gO V hηV ≫ hV.isoSpec.hom = Spec.map (S'.germToFunctionField V) := by
      rw [← cancel_mono hV.fromSpec, Category.assoc, IsAffineOpen.isoSpec_hom_fromSpec, hgO V hηV, hsp]
    refine ⟨hV.isoSpec.hom ≫ ξ, ?_, ?_⟩
    · rw [Category.assoc, h2, ← Category.assoc, IsAffineOpen.isoSpec_hom_fromSpec]
    · rw [← Category.assoc, hg, h1]

  choose V hVa hxV _ using fun x : S' => exists_isAffineOpen_mem_and_subset (X := S') (U := ⊤) (x := x) (by simp)
  have hcov : TopologicalSpace.IsOpenCover V := eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxV x⟩
  have hηV : ∀ x, genericPoint S' ∈ V x := fun x => hη (V x) ⟨x, hxV x⟩
  choose m hm hmy using fun x => loc (V x) (hVa x) (hηV x)
  let 𝒰 := S'.openCoverOfIsOpenCover V hcov
  have hc : ∀ a b, pullback.fst (V a).ι (V b).ι ≫ m a = pullback.snd (V a).ι (V b).ι ≫ m b := by
    intro a b
    let r := pullback.fst (V a).ι (V b).ι ≫ (V a).ι
    have : IsReduced (pullback (V a).ι (V b).ι) := isReduced_of_isOpenImmersion r
    let w : Spec S'.functionField ⟶ pullback (V a).ι (V b).ι :=
      pullback.lift (gO (V a) (hηV a)) (gO (V b) (hηV b)) ((hgO (V a) (hηV a)).trans (hgO (V b) (hηV b)).symm)
    have : IsDominant w := isDominant_of_generic r _ w (by
      show (w ≫ pullback.fst _ _ ≫ (V a).ι) (IsLocalRing.closedPoint _) = _
      rw [pullback.lift_fst_assoc, hgO (V a) (hηV a)]; exact hgS)
    refine ext_of_isDominant_of_isSeparated p ?_ w ?_
    · rw [Category.assoc, Category.assoc, hm, hm, pullback.condition_assoc]
    · rw [pullback.lift_fst_assoc, pullback.lift_snd_assoc, hmy, hmy]
  have hg : ∀ a, (V a).ι ≫ 𝒰.glueMorphisms m hc = m a := fun a => 𝒰.ι_glueMorphisms m hc a
  let π := 𝒰.glueMorphisms m hc
  have hπp : π ≫ p = h := 𝒰.hom_ext _ _ fun a => ((reassoc_of% hg a) p).trans (hm a)
  refine ⟨π, ?_, hπp⟩
  have : IsReduced U.toScheme := isReduced_of_isOpenImmersion U.ι
  have : IsDominant (gO U hηU) := isDominant_of_generic U.ι _ _ (by
    show (gO U hηU ≫ U.ι) (IsLocalRing.closedPoint _) = _
    rw [hgO U hηU]; exact hgS)
  refine ext_of_isDominant_of_isSeparated p ?_ (gO U hηU) ?_
  · rw [Category.assoc, hπp, e]; simp only [Category.assoc]
  · let x := genericPoint S'
    rw [← Category.assoc, hgO U hηU, ← hgO (V x) (hηV x), Category.assoc, hg, hmy]
end GlobalTheory.NormalFiniteLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalSchemeExtensionThroughFiniteCoverStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normal_scheme_extension_through_finite_cover : ∀ (o : Type) [CommRing o] (N : ℕ) (S' X Z : Scheme.{0}) (U : S'.Opens) (c : U.toScheme ⟶ X) (i : X ⟶ Z) (p : Z ⟶ PSpace o N) (h : S' ⟶ PSpace o N), IsIntegral S' → Geo.Tor.IsNormalScheme S' → IsIntegral Z → Dense (U : Set S') → IsDominant c → IsFinite p → IsOpenImmersion i → Dense (Set.range i) → U.ι ≫ h = c ≫ i ≫ p → ∃ π : S' ⟶ Z, U.ι ≫ π = c ≫ i ∧ π ≫ p = h := by
  first | exact @GlobalTheory.NormalFiniteLift.exists_lift_of_finite | exact GlobalTheory.NormalFiniteLift.exists_lift_of_finite | (intros; apply GlobalTheory.NormalFiniteLift.exists_lift_of_finite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullO1SectionCoordinatesPower
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullO1SectionCoordinatesPower
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Points GlobalTheory.ZM

namespace GlobalTheory.SiegTh.PullO1

theorem top_le_wchart {X : Scheme.{0}} (L : LB X) {K : Type} [Field K] (x : Sp K ⟶ X) (p : L.ι)
    (hp : ⊤ ≤ x ⁻¹ᵁ L.U p) : ⊤ ≤ (𝟙 (Sp K)) ⁻¹ᵁ (L.pull x).U (fun _ => p) :=
  fun w _ => Set.mem_iInter.2 fun _ => hp (Set.mem_univ w)

theorem valR_id_resG_inv {K : Type} [Field K] {W : (Sp K).Opens} (hW : ⊤ ≤ (𝟙 (Sp K)) ⁻¹ᵁ W) (a : K) :
    valR (𝟙 (Sp K)) W (resG (Sp K) le_top ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a)) = a := by
  rw [valR_res _ le_top hW]
  have := valR_specMap (C := K) (𝟙 (CommRingCat.of K)) a
  simpa using this

theorem valR_resG' {C : Type} [CommRing C] {X : Scheme.{0}} (x : Sp C ⟶ X) {U V : X.Opens} (e : V ≤ U)
    (h : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(X, U)) : valR x V (resG X e f) = valR x U f :=
  valR_res x e h f

theorem valR_unit_ne_zero {K : Type} [Field K] {X : Scheme.{0}} (x : Sp K ⟶ X) {W : X.Opens} (hW : ⊤ ≤ x ⁻¹ᵁ W)
    (u : Γ(X, W)ˣ) : valR x W (u : Γ(X, W)) ≠ 0 := by
  rw [valR_eq x W hW]
  exact (u.isUnit.map (valMap x W hW).hom).ne_zero

end GlobalTheory.SiegTh.PullO1

namespace GlobalTheory.SiegTh.PullO1

theorem secCoord_vals {X : Scheme.{0}} {L : LB X} {I : Type} {σ : I → L.Sec} {K : Type} [Field K] {x : Sp K ⟶ X}
    {v : I → K} (hs : SecCoord L σ x v) :
    ∃ c : L.ι → K, (∀ p, ⊤ ≤ x ⁻¹ᵁ L.U p → c p ≠ 0 ∧ ∀ i, valF x (L.U p) ((σ i).f p) = v i * c p) ∧
      ∀ p p', ⊤ ≤ x ⁻¹ᵁ (L.U p ⊓ L.U p') →
        valF x (L.U p ⊓ L.U p') (L.g p p' : Γ(X, L.U p ⊓ L.U p')) * c p' = c p := by
  obtain ⟨τ, hτ, hv⟩ := hs
  refine ⟨fun p => valR (𝟙 (Sp K)) ((L.pull x).U (fun _ => p)) (τ.s (fun _ => p) : Γ(Sp K, _)), ?_, ?_⟩
  · intro p hp
    have hW := top_le_wchart L x p hp
    refine ⟨valR_unit_ne_zero _ hW _, fun i => ?_⟩
    have e := congrArg (valR (𝟙 (Sp K)) _) (hv i (fun _ => p) (LB.wchart_le L (fun _ => x) (fun _ => p) PUnit.unit))
    dsimp only at e
    have e2 := valR_appLE (𝟙 (Sp K)) x (LB.wchart_le L (fun _ => x) (fun _ => p) PUnit.unit) hW ((σ i).f p)
    rw [Category.id_comp] at e2
    rw [valF_eq_valR, ← e2]
    refine e.trans ?_
    rw [valR_mul _ _ hW, valR_id_resG_inv hW]
  · intro p p' hpp
    have hp : ⊤ ≤ x ⁻¹ᵁ L.U p := fun w hw => (hpp hw).1
    have hp' : ⊤ ≤ x ⁻¹ᵁ L.U p' := fun w hw => (hpp hw).2
    have hW := top_le_wchart L x p hp
    have hW' := top_le_wchart L x p' hp'
    have hWW : ⊤ ≤ (𝟙 (Sp K)) ⁻¹ᵁ ((L.pull x).U (fun _ => p) ⊓ (L.pull x).U (fun _ => p')) :=
      fun w hw => ⟨hW hw, hW' hw⟩
    have e0 := congrArg Units.val (hτ (fun _ => p) (fun _ => p'))
    have e := congrArg (valR (𝟙 (Sp K)) _) e0
    simp only [Units.val_mul] at e
    rw [valR_mul _ _ hWW] at e
    simp only [res, Units.coe_map, MonoidHom.coe_coe] at e
    rw [valR_res _ _ hWW, valR_res _ _ hWW] at e
    show _ * valR _ _ _ = valR _ _ _
    rw [e]
    congr 1
    rw [ProjSpace.linComb_punit_g, zpow_one]
    change valF x _ _ = valR (𝟙 (Sp K)) _ (resG (Sp K) _ ((x.app (L.U p ⊓ L.U p')).hom (L.g p p' : Γ(X, _))))
    refine Eq.symm ((valR_resG' (𝟙 (Sp K)) _ hWW _).trans ?_)
    refine (valR_comp (𝟙 (Sp K)) x _ _).symm.trans ?_
    rw [Category.id_comp]
    rfl

end GlobalTheory.SiegTh.PullO1

namespace GlobalTheory.SiegTh.PullO1

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem coe_res {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)ˣ) :
    ((res h a : Γ(X, V)ˣ) : Γ(X, V)) = resG X h (a : Γ(X, U)) := rfl

theorem coe_res_mul {X : Scheme.{0}} {V P Q R : X.Opens} (a : Γ(X, P)ˣ) (b : Γ(X, Q)ˣ) (c : Γ(X, R)ˣ) (ha : V ≤ P)
    (hb : V ≤ Q) (hc : V ≤ R) :
    ((res ha a * (res hb b)⁻¹ * res hc c : Γ(X, V)ˣ) : Γ(X, V)) =
      resG X ha (a : Γ(X, P)) * resG X hb (↑b⁻¹ : Γ(X, Q)) * resG X hc (c : Γ(X, R)) := rfl

theorem valF_pt_mul (M : RatModel o Ω) {V : M.Z.Opens} (hV : (V : Set M.Z).Nonempty) (f g : Γ(M.Z, V)) :
    valF M.pt V (f * g) = valF M.pt V f * valF M.pt V g := by
  rw [← M.res_apply V hV, ← M.res_apply V hV, ← M.res_apply V hV, map_mul]

theorem valF_pt_one (M : RatModel o Ω) {V : M.Z.Opens} (hV : (V : Set M.Z).Nonempty) :
    valF M.pt V (1 : Γ(M.Z, V)) = 1 := by
  rw [← M.res_apply V hV, map_one]

theorem valF_pt_inv (M : RatModel o Ω) {V : M.Z.Opens} (hV : (V : Set M.Z).Nonempty) (u : Γ(M.Z, V)ˣ) :
    valF M.pt V (↑u⁻¹ : Γ(M.Z, V)) = (valF M.pt V (u : Γ(M.Z, V)))⁻¹ := by
  rw [← M.res_apply V hV, ← M.res_apply V hV]
  exact map_units_inv (M.res V hV) u

theorem valF_pt_ne_zero (M : RatModel o Ω) {V : M.Z.Opens} (hV : (V : Set M.Z).Nonempty) (u : Γ(M.Z, V)ˣ) :
    valF M.pt V (u : Γ(M.Z, V)) ≠ 0 := by
  rw [← M.res_apply V hV]
  exact (u.isUnit.map (M.res V hV)).ne_zero

theorem exists_unit_of_val (M : RatModel o Ω) {V : M.Z.Opens} (hV : (V : Set M.Z).Nonempty) {w : Ω} (h0 : w ≠ 0)
    (h : ∀ z ∈ V, w ∈ M.O z ∧ w⁻¹ ∈ M.O z) : ∃ u : Γ(M.Z, V)ˣ, valF M.pt V (u : Γ(M.Z, V)) = w := by
  obtain ⟨f, hf⟩ := (RatModel.mem_ringOn_iff_exists hV).1 (RatModel.mem_ringOn.2 fun z hz => (h z hz).1)
  obtain ⟨g, hg⟩ := (RatModel.mem_ringOn_iff_exists hV).1 (RatModel.mem_ringOn.2 fun z hz => (h z hz).2)
  have hfg : f * g = 1 := M.valF_injective hV (by rw [valF_pt_mul M hV, valF_pt_one M hV, hf, hg, mul_inv_cancel₀ h0])
  exact ⟨⟨f, g, hfg, by rw [mul_comm]; exact hfg⟩, hf⟩

end GlobalTheory.SiegTh.PullO1

namespace GlobalTheory.SiegTh.PullO1

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem lbIso_of_vals (M : RatModel o Ω) {L A : LB M.Z} (cL : L.ι → Ω) (cA : A.ι → Ω)
    (hL0 : ∀ q, (L.U q : Set M.Z).Nonempty → cL q ≠ 0) (hA0 : ∀ p, (A.U p : Set M.Z).Nonempty → cA p ≠ 0)
    (hLg : ∀ q q', ((L.U q ⊓ L.U q' : M.Z.Opens) : Set M.Z).Nonempty →
      valF M.pt _ (L.g q q' : Γ(M.Z, L.U q ⊓ L.U q')) * cL q' = cL q)
    (hAg : ∀ p p', ((A.U p ⊓ A.U p' : M.Z.Opens) : Set M.Z).Nonempty →
      valF M.pt _ (A.g p p' : Γ(M.Z, A.U p ⊓ A.U p')) * cA p' = cA p)
    (hloc : ∀ p q z, z ∈ A.U p → z ∈ L.U q → cA p / cL q ∈ M.O z ∧ cL q / cA p ∈ M.O z) :
    LBIso L A := by
  have key : ∀ pq : A.ι × L.ι, ∃ u : Γ(M.Z, A.U pq.1 ⊓ L.U pq.2)ˣ,
      ((A.U pq.1 ⊓ L.U pq.2 : M.Z.Opens) : Set M.Z).Nonempty →
        valF M.pt _ (u : Γ(M.Z, A.U pq.1 ⊓ L.U pq.2)) = cA pq.1 / cL pq.2 := by
    intro pq
    by_cases hV : ((A.U pq.1 ⊓ L.U pq.2 : M.Z.Opens) : Set M.Z).Nonempty
    · have h0 : cA pq.1 / cL pq.2 ≠ 0 :=
        div_ne_zero (hA0 _ (by obtain ⟨z, hz⟩ := hV; exact ⟨z, hz.1⟩)) (hL0 _ (by obtain ⟨z, hz⟩ := hV; exact ⟨z, hz.2⟩))
      obtain ⟨u, hu⟩ := exists_unit_of_val M hV h0 fun z hz => by
        rw [inv_div]; exact hloc pq.1 pq.2 z hz.1 hz.2
      exact ⟨u, fun _ => hu⟩
    · exact ⟨1, fun h => absurd h hV⟩
  choose u hu using key
  refine ⟨⟨u⟩, fun pq pq' => ?_⟩
  by_cases hV : (((A.U pq.1 ⊓ L.U pq.2) ⊓ (A.U pq'.1 ⊓ L.U pq'.2) : M.Z.Opens) : Set M.Z).Nonempty
  · have h1 : ((A.U pq.1 ⊓ L.U pq.2 : M.Z.Opens) : Set M.Z).Nonempty := by obtain ⟨z, hz⟩ := hV; exact ⟨z, hz.1⟩
    have h2 : ((A.U pq'.1 ⊓ L.U pq'.2 : M.Z.Opens) : Set M.Z).Nonempty := by obtain ⟨z, hz⟩ := hV; exact ⟨z, hz.2⟩
    have hAA : ((A.U pq.1 ⊓ A.U pq'.1 : M.Z.Opens) : Set M.Z).Nonempty := by obtain ⟨z, hz⟩ := hV; exact ⟨z, hz.1.1, hz.2.1⟩
    have hLL : ((L.U pq.2 ⊓ L.U pq'.2 : M.Z.Opens) : Set M.Z).Nonempty := by obtain ⟨z, hz⟩ := hV; exact ⟨z, hz.1.2, hz.2.2⟩
    have cA' := hA0 _ (by obtain ⟨z, hz⟩ := h2; exact ⟨z, hz.1⟩)
    have cL' := hL0 _ (by obtain ⟨z, hz⟩ := h2; exact ⟨z, hz.2⟩)
    have cL0 := hL0 _ (by obtain ⟨z, hz⟩ := h1; exact ⟨z, hz.2⟩)
    have eA := hAg pq.1 pq'.1 hAA
    have eL := hLg pq.2 pq'.2 hLL
    have gL0 : valF M.pt _ (L.g pq.2 pq'.2 : Γ(M.Z, L.U pq.2 ⊓ L.U pq'.2)) ≠ 0 := valF_pt_ne_zero M hLL _
    dsimp only [LB.div]
    refine Units.ext (M.valF_injective hV ?_)
    erw [coe_res_mul, coe_res]
    rw [valF_pt_mul M hV, valF_pt_mul M hV, M.valF_resG _ hV, M.valF_resG _ hV]
    erw [M.valF_resG _ hV, M.valF_resG _ hV]
    rw [valF_pt_inv M hLL, hu _ h1, hu _ h2, ← eA, ← eL]
    field_simp
  · exact unit_ext fun x hx => absurd ⟨x, hx⟩ hV

end GlobalTheory.SiegTh.PullO1

namespace GlobalTheory.SiegTh.PullO1

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem valF_pt_zpow (M : RatModel o Ω) {V : M.Z.Opens} (hV : (V : Set M.Z).Nonempty) (u : Γ(M.Z, V)ˣ) (n : ℤ) :
    valF M.pt V (↑(u ^ n) : Γ(M.Z, V)) = (valF M.pt V (u : Γ(M.Z, V))) ^ n := by
  rw [← M.res_apply V hV, ← M.res_apply V hV]
  have h1 : ∀ w : Γ(M.Z, V)ˣ, M.res V hV (w : Γ(M.Z, V)) = ((Units.map (M.res V hV : Γ(M.Z, V) →* Ω) w : Ωˣ) : Ω) :=
    fun _ => rfl
  rw [h1, h1, map_zpow, Units.val_zpow_eq_zpow_val]

theorem valF_linComb_g (M : RatModel o Ω) {Y : Scheme.{0}} (L : LB Y) (φ : M.Z ⟶ Y) (n : ℤ) (P P' : PUnit → L.ι)
    (hV : (((LB.LinComb L (K := PUnit) (fun _ => φ) (fun _ => n)).U P ⊓
      (LB.LinComb L (K := PUnit) (fun _ => φ) (fun _ => n)).U P' : M.Z.Opens) : Set M.Z).Nonempty) :
    valF M.pt ((LB.LinComb L (K := PUnit) (fun _ => φ) (fun _ => n)).U P ⊓
      (LB.LinComb L (K := PUnit) (fun _ => φ) (fun _ => n)).U P')
      (((LB.LinComb L (K := PUnit) (fun _ => φ) (fun _ => n)).g P P' : Γ(M.Z, _)ˣ) : Γ(M.Z, _)) =
      valF (M.pt ≫ φ) (L.U (P PUnit.unit) ⊓ L.U (P' PUnit.unit)) (L.g (P PUnit.unit) (P' PUnit.unit) : Γ(Y, _)) ^ n := by
  rw [ProjSpace.linComb_punit_g]
  erw [valF_pt_zpow M hV]
  congr 1
  erw [coe_res, M.valF_resG _ hV]
  exact (valR_comp M.pt φ (L.U (P PUnit.unit) ⊓ L.U (P' PUnit.unit)) (L.g (P PUnit.unit) (P' PUnit.unit) : Γ(Y, _))).symm

end GlobalTheory.SiegTh.PullO1

namespace GlobalTheory.SiegTh.PullO1

theorem lbIso_pull_O1_lbPow : ∀ (k Ω o : Type) [CommRing k] [Field Ω] [Algebra k Ω] [CommRing o] (M : RatModel k Ω) (I : Type) [Finite I]
    (th : I → Ω) (δ : LB M.Z) (t : I → δ.Sec) (N D : ℕ) (e : Fin (N + 1) → Ω) (h : M.Z ⟶ PSpace o N), δ.IsLB →
    (⨆ a, nonzeroLocus (t a)) = ⊤ → SecCoord δ t M.pt th → PCrd (M.pt ≫ h) e → SameScale M th e D →
    LBIso ((GlobalTheory.ProjSpace.O1 o N).pull h) (lbPow δ D) := by
  intro k Ω o _ _ _ _ M I _ th δ t N D e h _ hcov hsc hpc hss
  obtain ⟨c, hc0, hcg⟩ := secCoord_vals hsc
  obtain ⟨d, hd0, hdg⟩ := secCoord_vals hpc
  have ptU : ∀ {U : M.Z.Opens}, (U : Set M.Z).Nonempty → ⊤ ≤ M.pt ⁻¹ᵁ U := fun hU => M.top_le_preimage_pt hU
  refine lbIso_of_vals M (fun Q => d (Q PUnit.unit)) (fun P => c (P PUnit.unit) ^ D) ?_ ?_ ?_ ?_ ?_
  · intro Q hQ
    exact (hd0 _ (fun w hw => LB.wchart_le _ (fun _ => h) Q PUnit.unit (ptU hQ hw))).1
  · intro P hP
    exact pow_ne_zero _ (hc0 _ (fun w hw => LB.wchart_le δ (fun _ => 𝟙 M.Z) P PUnit.unit (ptU hP hw))).1
  · intro Q Q' hQQ
    rw [valF_linComb_g M _ h 1 Q Q' hQQ, zpow_one]
    exact hdg _ _ (fun w hw => ⟨LB.wchart_le _ (fun _ => h) Q PUnit.unit (ptU hQQ hw).1,
      LB.wchart_le _ (fun _ => h) Q' PUnit.unit (ptU hQQ hw).2⟩)
  · intro P P' hPP
    rw [valF_linComb_g M δ (𝟙 M.Z) (D : ℤ) P P' hPP, zpow_natCast, Category.comp_id, ← mul_pow]
    rw [hcg _ _ (fun w hw => ⟨LB.wchart_le δ (fun _ => 𝟙 M.Z) P PUnit.unit (ptU hPP hw).1,
      LB.wchart_le δ (fun _ => 𝟙 M.Z) P' PUnit.unit (ptU hPP hw).2⟩)]
  · intro P Q z hzP hzQ
    show c (P PUnit.unit) ^ D / d (Q PUnit.unit) ∈ M.O z ∧ d (Q PUnit.unit) / c (P PUnit.unit) ^ D ∈ M.O z
    have hzp : z ∈ δ.U (P PUnit.unit) := LB.wchart_le δ (fun _ => 𝟙 M.Z) P PUnit.unit hzP
    have hzq : z ∈ h ⁻¹ᵁ (GlobalTheory.ProjSpace.O1 o N).U (Q PUnit.unit) := LB.wchart_le _ (fun _ => h) Q PUnit.unit hzQ
    generalize P PUnit.unit = p at hzp ⊢
    generalize Q PUnit.unit = q at hzq ⊢
    have hUp : ⊤ ≤ M.pt ⁻¹ᵁ δ.U p := ptU ⟨z, hzp⟩
    have hUq : ⊤ ≤ (M.pt ≫ h) ⁻¹ᵁ (GlobalTheory.ProjSpace.O1 o N).U q := ptU (U := h ⁻¹ᵁ _) ⟨z, hzq⟩
    obtain ⟨cp0, hcv⟩ := hc0 p hUp
    obtain ⟨dq0, hdv⟩ := hd0 q hUq
    have hed : ∀ i, e i * d q ∈ M.O z := fun i => by
      rw [← hdv i, valF_eq_valR, valR_comp]
      exact RatModel.valF_mem_O hzq _
    have heq1 : e q * d q = 1 := by
      have h11 : (ProjSpace.coord o N q).f q = 1 := ProjSpace.ratioOn_self (hi := le_rfl)
      rw [← hdv q, h11, valF_eq_valR]
      exact valR_one _ _ hUq
    obtain ⟨a, ha⟩ : ∃ a, z ∈ nonzeroLocus (t a) := by
      have hz : z ∈ (⨆ a, nonzeroLocus (t a)) := hcov ▸ trivial
      exact TopologicalSpace.Opens.mem_iSup.1 hz
    obtain ⟨kk, hk⟩ : ∃ kk, z ∈ M.Z.basicOpen ((t a).f kk) := TopologicalSpace.Opens.mem_iSup.1 ha
    have hzk : z ∈ δ.U kk := M.Z.basicOpen_le _ hk
    have hbo : z ∈ M.Z.basicOpen ((t a).f p) := by
      have e1 := congrArg M.Z.basicOpen ((t a).compat p kk)
      rw [Scheme.basicOpen_res, Scheme.basicOpen_mul, Scheme.basicOpen_res,
        Scheme.basicOpen_of_isUnit _ (δ.g p kk).isUnit] at e1
      have hz : z ∈ (δ.U p ⊓ δ.U kk) ⊓ ((δ.U p ⊓ δ.U kk) ⊓ M.Z.basicOpen ((t a).f kk)) :=
        ⟨⟨hzp, hzk⟩, ⟨hzp, hzk⟩, hk⟩
      rw [← e1] at hz
      exact hz.2
    have hua : th a * c p ≠ 0 ∧ (th a * c p)⁻¹ ∈ M.O z := by
      have hu := (RatModel.isUnit_O_iff _).1 ((RatModel.isUnit_valF_iff hzp ((t a).f p)).2 hbo)
      simpa only [hcv a] using hu
    have hmem : ∀ b, th b * c p ∈ M.O z := fun b => by
      rw [← hcv b]
      exact RatModel.valF_mem_O hzp _
    have tha0 : th a ≠ 0 := left_ne_zero_of_mul hua.1
    have hdiv : M.Div th a z := ⟨tha0, fun b => by
      have hb : th b / th a = (th b * c p) * (th a * c p)⁻¹ := by field_simp
      rw [hb]
      exact mul_mem (hmem b) hua.2⟩
    obtain ⟨j, hj, h1, h2⟩ := hss z a hdiv
    have ej0 : e j ≠ 0 := hj.1
    have heq : e q = (d q)⁻¹ := eq_inv_of_mul_eq_one_left heq1
    have key : c p ^ D / d q = (th a * c p) ^ D * (e j / th a ^ D) * (e q / e j) := by
      rw [heq]
      field_simp
      ring
    have U3 : (e q / e j)⁻¹ ∈ M.O z := by
      rw [inv_div, heq, div_inv_eq_mul]
      exact hed j
    have hx : c p ^ D / d q ∈ M.O z :=
      key ▸ mul_mem (mul_mem (pow_mem (hmem a) D) h2) (hj.2 q)
    have hy : (c p ^ D / d q)⁻¹ ∈ M.O z := by
      rw [key, mul_inv, mul_inv, ← inv_pow, inv_div (e j) (th a ^ D)]
      exact mul_mem (mul_mem (pow_mem hua.2 D) h1) U3
    exact ⟨hx, by rwa [inv_div] at hy⟩

end GlobalTheory.SiegTh.PullO1
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullO1SectionCoordinatesPowerStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pull_O1_section_coordinates_power : ∀ (k Ω o : Type) [CommRing k] [Field Ω] [Algebra k Ω] [CommRing o] (M : RatModel k Ω) (I : Type) [Finite I] (th : I → Ω) (δ : LB M.Z) (t : I → δ.Sec) (N D : ℕ) (e : Fin (N + 1) → Ω) (h : M.Z ⟶ PSpace o N), δ.IsLB → (⨆ a, nonzeroLocus (t a)) = ⊤ → SecCoord δ t M.pt th → PCrd (M.pt ≫ h) e → SameScale M th e D → LBIso ((GlobalTheory.ProjSpace.O1 o N).pull h) (lbPow δ D) := by
  first | exact @GlobalTheory.SiegTh.PullO1.lbIso_pull_O1_lbPow | exact GlobalTheory.SiegTh.PullO1.lbIso_pull_O1_lbPow | (intros; apply GlobalTheory.SiegTh.PullO1.lbIso_pull_O1_lbPow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResGInjectiveOfTop
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section
namespace GlobalTheory.TupleBundle

theorem resG_injective_of_top {X : Scheme.{0}} {V : X.Opens} (h : ⊤ ≤ V) : Function.Injective (resG X h) := by
  obtain rfl : V = ⊤ := top_unique h
  have e : (homOfLE h : (⊤ : X.Opens) ⟶ ⊤) = 𝟙 _ := Subsingleton.elim _ _
  intro a b hab
  simpa [resG, e] using hab

theorem resG_resG {X : Scheme.{0}} {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (a : Γ(X, U)) :
    resG X h2 (resG X h1 a) = resG X (h2.trans h1) a := by
  show (X.presheaf.map _ ≫ X.presheaf.map _).hom a = _
  rw [← Functor.map_comp]
  rfl

theorem resG_appLE {X Y : Scheme.{0}} (f : Y ⟶ X) {U : X.Opens} {V W : Y.Opens} (h : V ≤ f ⁻¹ᵁ U) (h2 : W ≤ V)
    (a : Γ(X, U)) : resG Y h2 ((f.appLE U V h).hom a) = (f.appLE U W (h2.trans h)).hom a := by
  show (f.appLE U V h ≫ Y.presheaf.map _).hom a = _
  rw [Scheme.Hom.appLE_map]

variable {Ω : Type} [Field Ω]

def ev (V : (Sp Ω).Opens) (hV : ⊤ ≤ V) : Γ(Sp Ω, V) →+* Ω :=
  (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom.comp (resG (Sp Ω) hV)

theorem ev_injective (V : (Sp Ω).Opens) (hV : ⊤ ≤ V) : Function.Injective (ev V hV) :=
  (Scheme.ΓSpecIso (CommRingCat.of Ω)).commRingCatIsoToRingEquiv.injective.comp (resG_injective_of_top hV)

theorem ev_resG {V W : (Sp Ω).Opens} (hV : ⊤ ≤ V) (hW : ⊤ ≤ W) (h : W ≤ V) (a : Γ(Sp Ω, V)) :
    ev W hW (resG (Sp Ω) h a) = ev V hV a := by
  simp only [ev, RingHom.comp_apply, resG_resG]

theorem ev_resG_top {V : (Sp Ω).Opens} (hV : ⊤ ≤ V) (x : Ω) :
    ev V hV (resG (Sp Ω) le_top ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom x)) = x := by
  have e : (homOfLE (hV.trans le_top) : (⊤ : (Sp Ω).Opens) ⟶ ⊤) = 𝟙 _ := Subsingleton.elim _ _
  simp only [ev, RingHom.comp_apply, resG_resG]
  simp [resG, e]

theorem ev_appLE {X : Scheme.{0}} (x : Sp Ω ⟶ X) {U : X.Opens} {V : (Sp Ω).Opens} (hV : ⊤ ≤ V) (h : V ≤ x ⁻¹ᵁ U)
    (f : Γ(X, U)) : ev V hV ((x.appLE U V h).hom f) = valF x U f := by
  simp only [ev, RingHom.comp_apply, resG_appLE, valF, dif_pos (hV.trans h)]

end GlobalTheory.TupleBundle

namespace GlobalTheory.TupleBundle

theorem exists_lb_of_hasDiv : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : ZH.RatModel o Ω) (J : Type)
    [Finite J] (v : J → Ω), M.HasDiv v → ∃ (δ : LB M.Z) (t : J → δ.Sec), δ.IsLB ∧ (⨆ a, nonzeroLocus (t a)) = ⊤ ∧
    (∀ a z, z ∈ nonzeroLocus (t a) ↔ M.Div v a z) ∧ ZM.SecCoord δ t M.pt v := by
  intro o Ω _ _ _ M J _ v hv
  let U : {a // v a ≠ 0} → M.Z.Opens := fun k => ⟨{z | M.Div v k.1 z}, M.isOpen_setOf_div v k.1⟩
  have hU : ⨆ k, U k = ⊤ := by
    refine top_unique fun z _ => ?_
    obtain ⟨i, hi⟩ := hv z
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨i, hi.1⟩, hi⟩
  obtain ⟨g, hLB, hGT⟩ := ZH.RatModel.exists_isLB_genTriv_of_ratios o Ω M {a // v a ≠ 0} U (fun k => v k.1) hU
    (fun k => k.2) (fun k k' z hz => hz.1.2 k'.1)
  let δ : LB M.Z := ⟨{a // v a ≠ 0}, U, g⟩
  have hsec : ∀ a, ∃ σ : δ.Sec, M.HasVal (H := δ) (fun k => v k.1) σ (v a) := fun a =>
    hGT.exists_sec_hasVal (v a) fun k z hz => hz.2 a
  choose t ht using hsec
  have hnz : ∀ a z, z ∈ nonzeroLocus (t a) ↔ M.Div v a z := by
    intro a z
    simp only [nonzeroLocus, TopologicalSpace.Opens.mem_iSup]
    constructor
    · rintro ⟨k, hk⟩
      have hzk : z ∈ U k := M.Z.basicOpen_le _ hk
      have hval : valF M.pt (U k) ((t a).f k) = v a / v k.1 := ht a k ⟨z, hzk⟩
      have hu := (ZH.RatModel.isUnit_valF_iff (M := M) hzk ((t a).f k)).2 hk
      rw [ZH.RatModel.isUnit_O_iff] at hu
      simp only [hval] at hu
      obtain ⟨h1, h2⟩ := hu
      have hk0 := k.2
      have ha0 : v a ≠ 0 := (div_ne_zero_iff.1 h1).1
      refine ⟨ha0, fun j => ?_⟩
      have e : v j / v a = (v j / v k.1) * (v a / v k.1)⁻¹ := by field_simp
      rw [e]
      exact mul_mem (hzk.2 j) h2
    · intro h
      refine ⟨⟨a, h.1⟩, ?_⟩
      have hzk : z ∈ U ⟨a, h.1⟩ := h
      rw [← ZH.RatModel.isUnit_valF_iff (M := M) hzk, ZH.RatModel.isUnit_O_iff]
      have hv1 : valF M.pt (U ⟨a, h.1⟩) ((t a).f ⟨a, h.1⟩) = 1 := (ht a ⟨a, h.1⟩ ⟨z, hzk⟩).trans (div_self h.1)
      simp only [hv1, inv_one]
      exact ⟨one_ne_zero, one_mem _⟩
  refine ⟨δ, t, hLB, ?_, hnz, ?_⟩
  · refine top_unique fun z _ => ?_
    obtain ⟨i, hi⟩ := hv z
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, (hnz i z).2 hi⟩
  · have hgen : ∀ k : {a // v a ≠ 0}, ⊤ ≤ M.pt ⁻¹ᵁ U k := fun k w _ => by
      show M.pt w ∈ U k
      rw [M.pt_apply w]
      exact ZH.RatModel.div_genericPoint (M := M) k.2
    have hW : ∀ j, ⊤ ≤ (δ.pull M.pt).U j := fun j w _ =>
      Set.mem_iInter.2 fun _ => hgen (j PUnit.unit) (x := w) trivial
    let τ : (δ.pull M.pt).Gen := ⟨fun j => Units.map (resG (Sp Ω) (le_top : (δ.pull M.pt).U j ≤ ⊤)).toMonoidHom
      (Units.map (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom.toMonoidHom
        (Units.mk0 (v (j PUnit.unit).1)⁻¹ (inv_ne_zero (j PUnit.unit).2)))⟩
    have hτ : ∀ j, ((τ.s j : Γ(Sp Ω, (δ.pull M.pt).U j)ˣ) : Γ(Sp Ω, (δ.pull M.pt).U j)) =
        resG (Sp Ω) le_top ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (v (j PUnit.unit).1)⁻¹) := fun j => rfl
    refine ⟨τ, fun j j' => ?_, fun i j h => ?_⟩
    · have hle : (δ.pull M.pt).U j ⊓ (δ.pull M.pt).U j' ≤ M.pt ⁻¹ᵁ (U (j PUnit.unit) ⊓ U (j' PUnit.unit)) :=
        le_inf (inf_le_left.trans (LB.wchart_le δ (fun _ => M.pt) j PUnit.unit))
          (inf_le_right.trans (LB.wchart_le δ (fun _ => M.pt) j' PUnit.unit))
      have e0 : (δ.pull M.pt).g j j' = Semi.res hle (pullU M.pt _ (δ.g (j PUnit.unit) (j' PUnit.unit))) :=
        (Fintype.prod_unique fun _ : PUnit.{1} =>
          Semi.res hle (pullU M.pt _ (δ.g (j PUnit.unit) (j' PUnit.unit))) ^ (1 : ℤ)).trans (zpow_one _)
      have hne : ((U (j PUnit.unit) ⊓ U (j' PUnit.unit) : M.Z.Opens) : Set M.Z).Nonempty :=
        ⟨genericPoint M.Z, ZH.RatModel.div_genericPoint (M := M) (j PUnit.unit).2,
          ZH.RatModel.div_genericPoint (M := M) (j' PUnit.unit).2⟩
      have hg := hGT.g_eq (j PUnit.unit) (j' PUnit.unit) hne
      have hV : ⊤ ≤ (δ.pull M.pt).U j ⊓ (δ.pull M.pt).U j' := le_inf (hW j) (hW j')
      refine Units.ext (ev_injective _ hV ?_)
      rw [e0]
      show ev _ hV (resG (Sp Ω) inf_le_left (τ.s j : Γ(Sp Ω, _))) =
        ev _ hV ((M.pt.appLE _ _ hle).hom (δ.g (j PUnit.unit) (j' PUnit.unit) : Γ(M.Z, _)) *
          resG (Sp Ω) inf_le_right (τ.s j' : Γ(Sp Ω, _)))
      rw [map_mul, ev_resG (hW j), ev_resG (hW j'), ev_appLE, hτ, hτ, ev_resG_top, ev_resG_top]
      have h1 := (j PUnit.unit).2
      have h2 := (j' PUnit.unit).2
      have hg' : valF M.pt (U (j PUnit.unit) ⊓ U (j' PUnit.unit)) (δ.g (j PUnit.unit) (j' PUnit.unit) : Γ(M.Z, _)) =
          v (j' PUnit.unit).1 / v (j PUnit.unit).1 := hg
      rw [hg']
      field_simp
    · have hne : (U (j PUnit.unit) : Set M.Z).Nonempty :=
        ⟨genericPoint M.Z, ZH.RatModel.div_genericPoint (M := M) (j PUnit.unit).2⟩
      have hv' : valF M.pt (U (j PUnit.unit)) ((t i).f (j PUnit.unit)) = v i / v (j PUnit.unit).1 :=
        ht i (j PUnit.unit) hne
      refine ev_injective _ (hW j) ?_
      simp only [map_mul, hτ]
      rw [ev_appLE, ev_resG_top]
      change _ = v i * ev _ (hW j) (resG (Sp Ω) le_top ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (v (j PUnit.unit).1)⁻¹))
      rw [ev_resG_top, hv', div_eq_mul_inv]

end GlobalTheory.TupleBundle
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinimalSiegelCompactificationExists
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SiegMinTop

theorem lemProper : ∀ (R o' : Type) [CommRing R] [IsNoetherianRing R] [CommRing o'] (β : R →+* o') (S' X Z : Scheme.{0}) (s' : S' ⟶ Sp o') (z : Z ⟶ Sp R) (π : S' ⟶ Z) (i : X ⟶ Z) (U : S'.Opens) (c : U.toScheme ⟶ X), IsProjOver s' → β.Finite → IsProjOver z → Surjective c → U.ι ≫ π = c ≫ i → Dense (Set.range i) → π ≫ z = s' ≫ spMap β → Surjective π ∧ IsProper π ∧ AlgebraicGeometry.IsNoetherian Z := by
  intro R o' _ _ _ β S' X Z s' z π i U c hs' hβ hz hc hUπ hi hπz
  have := GlobalTheory.ProperFamily.isProper_of_isProjOver hs'
  have := GlobalTheory.ProperFamily.isProper_of_isProjOver hz
  haveI : IsFinite (spMap β) := (IsFinite.SpecMap_iff _).2 hβ
  haveI : IsProper (π ≫ z) := by rw [hπz]; infer_instance
  haveI : IsProper π := IsProper.of_comp π z
  refine ⟨⟨?_⟩, inferInstance, ?_⟩
  · have hcl : IsClosed (Set.range π) := π.isClosedMap.isClosed_range
    have hsub : Set.range i ⊆ Set.range π := by
      rintro _ ⟨x, rfl⟩
      obtain ⟨u, rfl⟩ := c.surjective x
      exact ⟨U.ι u, by rw [← Scheme.Hom.comp_apply, hUπ, Scheme.Hom.comp_apply]⟩
    have h := hi.closure_eq ▸ closure_minimal hsub hcl
    exact fun y => h (Set.mem_univ y)
  · have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian z
    have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace z
    exact {}

theorem lemGen : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (U : M.Z.Opens) [Nonempty U], ∃ x : Sp Ω ⟶ U.toScheme, x ≫ U.ι = M.pt ∧ Set.range x = {genericPoint U.toScheme} := by
  intro o Ω _ _ _ M U _
  obtain ⟨⟨y₀, hy₀⟩⟩ := ‹Nonempty U›
  have hsub : Set.range M.pt ⊆ Set.range U.ι := by
    rw [M.gen, Scheme.Opens.range_ι, Set.singleton_subset_iff]
    exact (genericPoint_specializes y₀).mem_open U.isOpen hy₀
  have hg : U.ι (genericPoint U.toScheme) = genericPoint M.Z := by
    have h1 := (genericPoint_spec U.toScheme).image U.ι.continuous
    rw [Set.image_univ, Scheme.Opens.range_ι, (U.isOpen.dense ⟨y₀, hy₀⟩).closure_eq] at h1
    exact h1.eq (genericPoint_spec M.Z)
  set x := IsOpenImmersion.lift U.ι M.pt hsub with hx
  have hxU : x ≫ U.ι = M.pt := IsOpenImmersion.lift_fac _ _ _
  have hxa : ∀ a, x a = genericPoint U.toScheme := fun a => by
    apply U.ι.isOpenEmbedding.injective
    rw [hg, ← M.pt_apply a, ← hxU, Scheme.Hom.comp_apply]
  refine ⟨x, hxU, Set.eq_singleton_iff_unique_mem.2 ⟨⟨IsLocalRing.closedPoint Ω, hxa _⟩, ?_⟩⟩
  rintro _ ⟨a, rfl⟩
  exact hxa a

theorem minSt5 : GlobalTheory.SiegJoin.MinSt5 := by
  intro g hg n hn ho F
  obtain ⟨ℓ, hℓ, hℓn⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
  have hℓo : Odd ℓ := Odd.of_dvd_nat ho hℓn
  obtain ⟨W, hW, hbas⟩ := GlobalTheory.ZM.exists_isE8_isSharpBasis
  obtain ⟨hXi, hXn, -⟩ := GlobalTheory.T.siegelModuli_integral_normal_locallyNoetherian g n hg hn ho F
  obtain ⟨P, rig, hPg, hPs, hrig, -⟩ := GlobalTheory.T.exists_polarised_E8ThetaPower_over_moduli g n hg hn ho F W hW
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.T.siegelThetaMap_deepLevel_finite_fibres ℓ hℓ hℓo g
  have hmo : Odd (ℓ ^ (j₀ + 1)) := hℓo.pow
  have hm3 : 3 ≤ ℓ ^ (j₀ + 1) := by
    have h2 := hℓ.two_le
    have h1 : ℓ ≤ ℓ ^ (j₀ + 1) := Nat.le_self_pow (by omega) ℓ
    obtain ⟨k, hk⟩ := hℓo
    omega
  have hmu : IsUnit ((ℓ ^ (j₀ + 1) : ℕ) : cycAway n) := by
    obtain ⟨k, hk⟩ := hℓn
    have hu := isUnit_natCast (n := n) (by omega)
    have e : ((n : ℕ) : cycAway n) = (ℓ : cycAway n) * (k : cycAway n) := by
      rw [← Nat.cast_mul, ← hk]
    rw [e] at hu
    rw [Nat.cast_pow]
    exact (isUnit_of_mul_isUnit_left hu).pow _
  obtain ⟨N, f, hf⟩ := GlobalTheory.T.exists_thetaMap_eighthPower_siegelModuli g n hg hn ho F W hW P rig (ℓ ^ (j₀ + 1)) hPg hPs hrig hmo hm3 hmu
  have hq : QFin f := hj₀ (j₀ + 1) (by omega) n hg hn ho F W hW hℓn P rig N f hf
  haveI : IsDedekindDomain (cycAway n) := GlobalTheory.CycAwayReg.isDedekindDomain_cycAway n
  haveI : Algebra.FiniteType ℤ (cycAway n) := finiteType_cycAway n
  have hfs : f ≫ PSpace.str (cycAway n) N = F.s := hf.2.2.2.2.2.2.2.1
  have hlft : LocallyOfFiniteType F.s := GlobalTheory.SiegUnram.locallyOfFiniteType_of_isQProjOver F.qproj
  have hqc : QuasiCompact F.s := GlobalTheory.SiegelFamilyBaseChange.quasiCompact_of_isQProjOver F.qproj
  obtain ⟨Z, p, i, hpf, hio, hip, hZn, hZi, hid⟩ :=
    GlobalTheory.T.exists_finite_normalisation_projective_quasiFinite (cycAway n) N F.X F.s f hXi hXn hlft hqc F.isSeparated hfs hq
  obtain ⟨hzproj, hOZlb, hOZamp, -⟩ := GlobalTheory.T.finite_over_projectiveSpace_projective_ample_twist (cycAway n) N 8 Z p (by norm_num) hpf
  obtain ⟨o, Ω, _, _, _, _, β, S, ρ, u, Y, q, hsys, hlev, hbig, hfin⟩ :=
    GlobalTheory.T.exists_realisedThetaSystem_normalLevelModel ℓ hℓ hℓo j₀ g n hg hn ho F W hW hℓn (hbas g)
  obtain ⟨X, M, U₀, EE, fM, Xab, Zh, hmin, hab, habeq⟩ := GlobalTheory.T.exists_normal_projective_toric_minor_model o Ω S ρ hbig hfin
  have hXnm : X.IsNm S.th := hmin.1
  have hXnorm : Geo.Tor.IsNormalScheme X.Z := hmin.2.2.1
  have hover : S.Over₀ M U₀ := hmin.2.2.2.1
  obtain ⟨d, hd, hdo⟩ :=
    GlobalTheory.T.levelCover_openImmersion_normalisedThetaClosure g n hg hn ho F W hW P rig (ℓ ^ (j₀ + 1)) N f hf o Ω β S ρ u hsys hq Y X q hlev hXnm hXnorm
  obtain ⟨U, c, hUc, -⟩ :=
    GlobalTheory.T.level_cover_image_open_finite_over_moduli g n hg hn ho F W hW o Ω β S ρ u hsys Y X M q U₀ EE fM Xab Zh d hlev hmin habeq hd hdo
  obtain ⟨G, _, e, _, hGs, hGsm, hGpb, hGh⟩ :=
    GlobalTheory.T.eighth_power_first_factor_theta_model g n hg hn ho F W hW o Ω β S ρ u hsys M U₀ EE Zh U c hover hUc
  obtain ⟨eS, hSymE, hcrd⟩ := GlobalTheory.T.exists_symmetric_theta_constants_eq_thetaMap_coords g n hg hn ho F W hW P rig (ℓ ^ (j₀ + 1)) N f hf o Ω β S ρ u hsys
  have hMn : Geo.Tor.IsNormalScheme M.Z := hover.normal
  have hscale := GlobalTheory.T.thetaConstant_pow_eq_unit_mul_symmetricFunction g n hg hn ho F W hW P rig (ℓ ^ (j₀ + 1)) N f hf o Ω β S ρ u hsys M eS hMn
    hover.div hSymE
  have hediv : M.HasDiv eS := fun z' => by
    obtain ⟨i', hi'⟩ := hover.div z'
    obtain ⟨j', hj', -⟩ := hscale z' i' hi'
    exact ⟨j', hj'⟩
  obtain ⟨h, hhs, hhc⟩ := GlobalTheory.T.exists_projSpace_map_of_tuple_hasDivisor o Ω (cycAway n) β M N eS hediv
  haveI : NeZero (S.r * S.N) := ⟨by have := S.r_pos; have := S.N_ge; positivity⟩
  obtain ⟨δ, t, hδ, htop, -, hsec⟩ := GlobalTheory.TupleBundle.exists_lb_of_hasDiv o Ω M S.Gam S.th hover.div
  have hhb := GlobalTheory.T.pull_O1_section_coordinates_power o Ω (cycAway n) M S.Gam S.th δ t N (N + 1).factorial eS h hδ htop hsec hhc hscale
  have hSg : S.g = 8 * g := hsys.2.2.1
  have hkey := GlobalTheory.T.thetaConstantBundle_pow_eight_iso_detHodge_pow_four o Ω S ρ M U₀ EE Zh (by omega) hover hab δ t hδ htop hsec
  haveI : Nonempty U := ⟨⟨_, hUc.1.some_mem⟩⟩
  obtain ⟨x, hxU, hxg⟩ := lemGen o Ω M U
  have hUh : U.ι ≫ h = c ≫ f := GlobalTheory.T.eq_of_same_generic_projective_coords (cycAway n) N U.toScheme (c ≫ F.s) (U.ι ≫ h) (c ≫ f) Ω x eS
    (by rw [Category.assoc, hhs, hUc.2.2.2.1]) (by rw [Category.assoc, hfs]) hxg
    (by rw [← Category.assoc, hxU]; exact hhc)
    (by rw [← Category.assoc, hUc.2.2.2.2 x hxU, Category.assoc]; exact hcrd _ rfl)
  haveI : Surjective c := hUc.2.2.1
  have hUd : Dense (U : Set M.Z) := U.isOpen.dense hUc.1
  obtain ⟨π, hπU, hπp⟩ := GlobalTheory.T.normal_scheme_extension_through_finite_cover (cycAway n) N M.Z F.X Z U c i p h inferInstance hMn hZi hUd
    inferInstance hpf hio hid (by rw [hUh, hip])
  have hss : π ≫ p ≫ PSpace.str (cycAway n) N = M.s ≫ spMap β := by rw [← Category.assoc, hπp, hhs]
  obtain ⟨hπs, hπpr, hZno⟩ := lemProper (cycAway n) o β M.Z F.X Z M.s (p ≫ PSpace.str (cycAway n) N) π i U c
    hover.proj hsys.1 hzproj hUc.2.2.1 hπU hid hss
  have hTI : GlobalTheory.Poinc.ThetaInt F W i := by
    have h0 := GlobalTheory.T.siegelThetaConstants_projectively_integral_anyBase g n hg hn ho F W hW P rig (ℓ ^ (j₀ + 1)) N f hf
    rw [← hip] at h0
    intro o' Ω' _ _ _ _ S' ρ' u' hsh hgen M' π' hM' hpt
    exact h0 o' Ω' S' ρ' u' hsh hgen M' (π' ≫ p) hM' (by rw [← Category.assoc, hpt]; simp only [Category.assoc])
  have hiz : i ≫ p ≫ PSpace.str (cycAway n) N = F.s := by rw [← Category.assoc, hip, hfs]

  haveI : IsSeparated G.hom := hGs.separated
  haveI : IsSeparated Zh.G.hom := Zh.semi.separated
  haveI := hGsm
  haveI := Zh.dim
  have hH2 : (hodge G g).IsLB := (GlobalTheory.LieVB.isVB_omega G g).isLB_det
  have hH1 : (hodge Zh.G S.g).IsLB := (GlobalTheory.LieVB.isVB_omega Zh.G S.g).isLB_det
  have hO := GlobalTheory.ProjSpace.O1_isLB (cycAway n) N
  have hLB : LBIso ((lbPow ((GlobalTheory.ProjSpace.O1 (cycAway n) N).pull p) 8).pull π)
      (lbPow (hodge G g) (32 * (N + 1).factorial)) := by
    have e1 := (GlobalTheory.CechPic.cls_eq_iff (pull_isLB hO h) (isLB_lbPow hδ _)).2 hhb
    have e2 := (GlobalTheory.CechPic.cls_eq_iff (isLB_lbPow hδ 8) (isLB_lbPow hH1 4)).2 hkey
    have e3 := (GlobalTheory.CechPic.cls_eq_iff hH1 (isLB_lbPow hH2 8)).2 hGh
    rw [GlobalTheory.CechPic.cls_pull hO, GlobalTheory.CechPic.cls_lbPow hδ] at e1
    rw [GlobalTheory.CechPic.cls_lbPow hδ, GlobalTheory.CechPic.cls_lbPow hH1] at e2
    rw [GlobalTheory.CechPic.cls_lbPow hH2] at e3
    refine (GlobalTheory.CechPic.cls_eq_iff (pull_isLB hOZlb π) (isLB_lbPow hH2 _)).1 ?_
    rw [GlobalTheory.CechPic.cls_pull hOZlb, GlobalTheory.CechPic.cls_lbPow (pull_isLB hO p), GlobalTheory.CechPic.cls_pull hO,
      GlobalTheory.CechPic.cls_lbPow hH2, map_nsmul, ← GlobalTheory.CechPic.pull_comp, hπp, e1, smul_comm 8, e2, e3, smul_smul,
      smul_smul]
    congr 1
    ring
  refine ⟨Z, p ≫ PSpace.str (cycAway n) N, i, lbPow ((GlobalTheory.ProjSpace.O1 (cycAway n) N).pull p) 8, o, inferInstance, β,
    M.Z, M.s, U, c, π, G, inferInstance, e, inferInstance, 32 * (N + 1).factorial,
    ⟨⟨hzproj, GlobalTheory.IsNormalScheme.of_pred hZn, hio, hiz, hid, W, hW, hTI⟩, hzproj, GlobalTheory.IsNormalScheme.of_pred hZn,
      hiz, hid, hOZlb, hOZamp⟩,
    ⟨hsys.1, hsys.2.1, hover.proj, GlobalTheory.IsNormalScheme.of_pred hMn, hUd, hUc.2.1, hUc.2.2.1, hπU, hss, hπs, hπpr, hZno⟩,
    ⟨hGs, hGsm, hGpb⟩, by have := Nat.factorial_pos (N + 1); omega, hLB⟩

end GlobalTheory.SiegMinTop
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinimalSiegelCompactificationExistsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.minimalSiegelCompactification_exists : GlobalTheory.SiegJoin.MinSt5 := by
  first | exact @GlobalTheory.SiegMinTop.minSt5 | exact GlobalTheory.SiegMinTop.minSt5 | (intros; apply GlobalTheory.SiegMinTop.minSt5 <;> assumption)
end
