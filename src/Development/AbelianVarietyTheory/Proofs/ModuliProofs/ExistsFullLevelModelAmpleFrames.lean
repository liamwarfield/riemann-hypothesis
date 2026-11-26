module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmFamilyFiniteUnramifiedOverSiegelFamily
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyAmpleFramedModelPELThetaFamily
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformisationTriplesCompleteDVRTorsion
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHomBirationalModelsAmpleFrames
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianLocusOpenFamilyOverLevel
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FullLevelChangeActsOnUnitaryFamily
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaFamilyPelSmoothGenericFibre

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFullLevelModelOfFamilyBirationalModel
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFullLevelModelOfFamilyBirationalModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.TopOfFamily

attribute [local simp] pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc pullback.lift_snd_assoc

theorem exists_section {U M : Scheme.{0}} (u : U ⟶ M) (W : M.Opens) [IsIso (u ∣_ W)] :
    ∃ i : W.toScheme ⟶ U, IsOpenImmersion i ∧ i ≫ u = W.ι ∧
      ∀ (T : Scheme.{0}) (g : T ⟶ U) (b : T ⟶ W.toScheme), g ≫ u = b ≫ W.ι → g = b ≫ i := by
  have hp := isPullback_morphismRestrict u W
  refine ⟨inv (u ∣_ W) ≫ (u ⁻¹ᵁ W).ι, inferInstance, ?_, fun T g b h => ?_⟩
  · rw [Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
  · have h1 := hp.lift_fst b g h.symm
    have h2 := hp.lift_snd b g h.symm
    rw [← h1, Category.assoc, IsIso.hom_inv_id_assoc, h2]

theorem isProjOver_comp_iso {R : Type} [CommRing R] {Z : Scheme.{0}} {s : Z ⟶ Sp R} (h : IsProjOver s) (σ : R ≃+* R) :
    IsProjOver (s ≫ spMap σ.toRingHom) := by
  obtain ⟨L, hL⟩ := GlobalTheory.exists_isAmpleLB_of_isProjOver h
  have := projProper _ _ _ h
  have : IsIso (CommRingCat.ofHom σ.toRingHom) := σ.toCommRingCatIso.isIso_hom
  exact hL.isProjOver _

theorem isReduced_of_normal {Z : Scheme.{0}} (h : Geo.Tor.IsNormalScheme Z) : IsReduced Z := by
  have : ∀ x : Z, _root_.IsReduced (Z.presheaf.stalk x) := fun x ↦
    have := (h x).1
    inferInstance
  exact isReduced_of_isReduced_stalk Z

theorem charZero_residueField {k : Type} [Field k] [CharZero k] {S : Scheme.{0}} (s : S ⟶ Sp k) (p : S) :
    CharZero (S.residueField p) := by
  obtain ⟨φ, -⟩ := Spec.map_surjective (S.fromSpecResidueField p ≫ s)
  exact charZero_of_injective_ringHom (R := k) φ.hom.injective

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : B →+* C) (g : A →+* B) :
    spMap f ≫ spMap g = spMap (f.comp g) := by
  rw [spMap, spMap, ← Spec.map_comp]; rfl

theorem asIdeal_spMap {A k : Type} [CommRing A] [Field k] (β : A →+* k) (hβ : Function.Injective β) (x : Sp k) :
    (spMap β x).asIdeal = ⊥ := by
  have h : x.asIdeal = ⊥ := @Ideal.eq_bot_of_prime _ _ _ x.isPrime
  change Ideal.comap β x.asIdeal = ⊥
  rw [h]
  exact (RingHom.injective_iff_ker_eq_bot _).1 hβ

theorem isDominant_snd {X U Y : Scheme.{0}} (j : U ⟶ X) [IsDominant j] (p : Y ⟶ X) [IsOpenImmersion p] :
    IsDominant (pullback.snd j p) := by
  have := isDominant_pullback_fst_of_isOpenMap j p p.isOpenEmbedding.isOpenMap
  rw [← pullbackSymmetry_hom_comp_fst]
  infer_instance

theorem comp_eq_of_dense {Z U M W W₀ W' X : Scheme.{0}} [IsReduced Z] [Z.IsSeparated] (v : U ⟶ Z) [IsOpenImmersion v]
    (u : U ⟶ M) (w₀ : W₀ ⟶ M) [IsOpenImmersion w₀] (i : W₀ ⟶ U) [IsOpenImmersion i] (hi : i ≫ u = w₀)
    (hu : ∀ (T : Scheme.{0}) (g : T ⟶ U) (b : T ⟶ W₀), g ≫ u = b ≫ w₀ → g = b ≫ i)
    (j : W ⟶ U) (e₁ e₂ : W' ⟶ W) [IsDominant (e₁ ≫ j ≫ v)] (ρ : M ≅ M) (he : e₁ ≫ j ≫ u ≫ ρ.hom = e₂ ≫ j ≫ u)
    (τ : Z ⟶ Z) (hτ : (e₁ ≫ j ≫ v) ≫ τ = e₂ ≫ j ≫ v) (b b' : X ⟶ W₀) (hb : b ≫ w₀ ≫ ρ.hom = b' ≫ w₀) :
    (b ≫ i ≫ v) ≫ τ = b' ≫ i ≫ v := by
  let d₁ := pullback.fst (w₀ ≫ ρ.hom) w₀
  let d₂ := pullback.snd (w₀ ≫ ρ.hom) w₀
  have hd : d₁ ≫ w₀ ≫ ρ.hom = d₂ ≫ w₀ := pullback.condition
  have key : (d₁ ≫ i ≫ v) ≫ τ = d₂ ≫ i ≫ v := by
    have := isReduced_of_isOpenImmersion (d₁ ≫ i ≫ v)
    have := isDominant_snd (e₁ ≫ j ≫ v) (d₁ ≫ i ≫ v)
    have hq := pullback.condition (f := e₁ ≫ j ≫ v) (g := d₁ ≫ i ≫ v)
    set q₁ := pullback.fst (e₁ ≫ j ≫ v) (d₁ ≫ i ≫ v)
    set q₂ := pullback.snd (e₁ ≫ j ≫ v) (d₁ ≫ i ≫ v)
    refine ext_of_isDominant q₂ ?_
    have h1 : q₁ ≫ e₁ ≫ j = q₂ ≫ d₁ ≫ i := by
      rw [← cancel_mono v]; simpa using hq
    have h2 : q₁ ≫ e₂ ≫ j = (q₂ ≫ d₂) ≫ i := by
      refine hu _ _ _ ?_
      simp only [Category.assoc]
      rw [← he, reassoc_of% h1, reassoc_of% hi, hd]
    rw [← Category.assoc q₂, ← hq, Category.assoc, hτ, reassoc_of% h2]
  have h1 := pullback.lift_fst b b' (f := w₀ ≫ ρ.hom) (g := w₀) hb
  have h2 := pullback.lift_snd b b' (f := w₀ ≫ ρ.hom) (g := w₀) hb
  rw [← h1]
  conv_rhs => rw [← h2]
  simp only [Category.assoc] at key ⊢
  rw [key]

theorem exists_finite_lift {Z M W₀ X B B' : Scheme.{0}} (U : Z.Opens) (s : Z ⟶ B) (sM : M ⟶ B) (β : B' ⟶ B)
    (u : U.toScheme ⟶ M) (hs : u ≫ sM = U.ι ≫ s) (w₀ : W₀ ⟶ M) [IsOpenImmersion w₀] (i : W₀ ⟶ U.toScheme)
    (hi : i ≫ u = w₀) (hu : ∀ (T : Scheme.{0}) (g : T ⟶ U) (b : T ⟶ W₀), g ≫ u = b ≫ w₀ → g = b ≫ i)
    (hr : Set.range (pullback.fst sM β) ⊆ Set.range w₀) (b : X ⟶ W₀) (c : X ⟶ B') (h : (b ≫ w₀) ≫ sM = c ≫ β)
    (hf : IsFinite (pullback.lift _ _ h)) (hsu : Surjective (pullback.lift _ _ h)) :
    ∃ f : X ⟶ (pullback.fst s β ⁻¹ᵁ U).toScheme, IsFinite f ∧ Surjective f ∧
      f ≫ (pullback.fst s β ⁻¹ᵁ U).ι ≫ pullback.fst _ _ = b ≫ i ≫ U.ι ∧
      f ≫ (pullback.fst s β ⁻¹ᵁ U).ι ≫ pullback.snd _ _ = c := by
  have hp := isPullback_morphismRestrict (pullback.fst s β) U
  obtain ⟨p, hp₀⟩ : ∃ p, p ≫ w₀ = pullback.fst sM β := ⟨_, IsOpenImmersion.lift_fac w₀ _ hr⟩
  have c₁ : (p ≫ i ≫ U.ι) ≫ s = pullback.snd sM β ≫ β := by
    simp only [Category.assoc]
    rw [← hs, reassoc_of% hi, reassoc_of% hp₀, pullback.condition]
  have c₂ : (p ≫ i) ≫ U.ι = pullback.lift _ _ c₁ ≫ pullback.fst s β := by simp
  have c₃ : (pullback.fst s β ∣_ U ≫ u) ≫ sM = ((pullback.fst s β ⁻¹ᵁ U).ι ≫ pullback.snd s β) ≫ β := by
    simp only [Category.assoc]
    rw [hs, morphismRestrict_ι_assoc, pullback.condition]
  have g₁ := hp.lift_fst _ _ c₂
  have g₂ := hp.lift_snd _ _ c₂
  set g := hp.lift _ _ c₂
  have hk : pullback.fst s β ∣_ U = (pullback.lift _ _ c₃ ≫ p) ≫ i := hu _ _ _ (by simp [hp₀])
  have : IsIso g := by
    refine ⟨pullback.lift _ _ c₃, ?_, ?_⟩
    · apply pullback.hom_ext
      · simp [reassoc_of% g₁, hi, hp₀]
      · simp [reassoc_of% g₂]
    · apply hp.hom_ext
      · rw [Category.assoc, g₁, Category.id_comp, ← Category.assoc, ← hk]
      · rw [Category.assoc, g₂, Category.id_comp]
        apply pullback.hom_ext
        · simp only [Category.assoc, pullback.lift_fst]
          rw [← morphismRestrict_ι]
          conv_rhs => rw [hk]
          simp
        · simp
  refine ⟨pullback.lift _ _ h ≫ g, inferInstance, inferInstance, ?_, ?_⟩
  · have : pullback.lift _ _ h ≫ p = b := by
      rw [← cancel_mono w₀]; simp [hp₀]
    simp [reassoc_of% g₂, reassoc_of% this]
  · simp [reassoc_of% g₂]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem comp_of_eq {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S}
    {g : S'' ⟶ S'} {h : S'' ⟶ S} (m : SABMap t' t f) (m' : SABMap t'' t' g) (e : g ≫ f = h) :
    ∃ n : SABMap t'' t h, n.φ = m'.φ ≫ m.φ := by
  subst e
  exact sabComp pullCubComp E H _ _ _ t t' t'' f g m m'

theorem cancel_of_eq {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S}
    {g : S'' ⟶ S'} {h : S'' ⟶ S} (m : SABMap t' t f) (n : SABMap t'' t h) (e : g ≫ f = h) :
    ∃ m' : SABMap t'' t' g, n.φ = m'.φ ≫ m.φ := by
  subst e
  exact sabCancel pullCubCancel E H _ _ _ t t' t'' f g m n

section Model

variable {R : Type} [CommRing R] {MM : Scheme.{0}} {sM : MM ⟶ Sp R} {tM : SAB H MM} {m : ℕ} (C : ZOn sM tM m)

theorem isLocallyNoetherian [IsNoetherianRing R] : IsLocallyNoetherian C.Z := by
  have := projProper _ _ _ C.proj
  exact LocallyOfFiniteType.isLocallyNoetherian C.s

theorem isSeparated : C.Z.IsSeparated := by
  have := projProper _ _ _ C.proj
  refine ⟨?_⟩
  rw [← terminal.comp_from C.s]
  infer_instance

theorem genericPoints_subset [IsNoetherianRing R] [IsProper tM.G.hom] : genericPoints C.Z ⊆ abLocus C.t.G := by
  have := isLocallyNoetherian C
  have := C.j_open
  have := C.j_dom
  refine (genericPoints_subset_range_of_isDominant C.j).trans ?_
  rintro _ ⟨x, rfl⟩
  rw [abLocus_pullback abLocusOne C.t.semi C.m₂.cart.1, ← abLocus_pullback abLocusOne tM.semi C.m₁.cart.1]
  intro K _ _ t _
  infer_instance

theorem range_j_subset [IsProper tM.G.hom] : Set.range C.j ⊆ abLocus C.t.G := by
  rintro _ ⟨x, rfl⟩
  rw [abLocus_pullback abLocusOne C.t.semi C.m₂.cart.1, ← abLocus_pullback abLocusOne tM.semi C.m₁.cart.1]
  intro K _ _ t _
  infer_instance

theorem exists_iso (hH : GlobalTheory.LN.HomExtSt) (hR : IsDedekindDomain R) [CharZero R] (hft : Algebra.FiniteType ℤ R)
    [IsProper tM.G.hom] (ρ : MM ≅ MM) (mu : SABMap tM tM ρ.hom) (σ : R ≃+* R)
    (hρ : ρ.hom ≫ sM = sM ≫ spMap σ.toRingHom) :
    ∃ (W' : Scheme.{0}) (e₁ e₂ : W' ⟶ C.W.toScheme) (τ : C.Z ≅ C.Z), IsDominant (e₁ ≫ C.j) ∧
      e₁ ≫ C.W.ι ≫ ρ.hom = e₂ ≫ C.W.ι ∧ (e₁ ≫ C.j) ≫ τ.hom = e₂ ≫ C.j := by
  have := isLocallyNoetherian C
  have := isSeparated C
  have := isReduced_of_normal (fun x => ⟨C.normal.1 x, C.normal.2 x⟩)
  have := C.j_open
  have := C.j_dom
  have : IsDominant C.W.ι := ⟨by rw [DenseRange, Scheme.Opens.range_ι]; exact C.dense⟩
  have d₁ := isDominant_pullback_fst_of_isOpenMap C.W.ι (C.W.ι ≫ ρ.hom) (C.W.ι ≫ ρ.hom).isOpenEmbedding.isOpenMap
  have d₂ := isDominant_snd (C.W.ι ≫ ρ.hom) C.W.ι
  have he := pullback.condition (f := C.W.ι ≫ ρ.hom) (g := C.W.ι)
  have o₁ : IsOpenImmersion (pullback.fst (C.W.ι ≫ ρ.hom) C.W.ι) := inferInstance
  have o₂ : IsOpenImmersion (pullback.snd (C.W.ι ≫ ρ.hom) C.W.ι) := inferInstance
  set e₁ := pullback.fst (C.W.ι ≫ ρ.hom) C.W.ι
  set e₂ := pullback.snd (C.W.ι ≫ ρ.hom) C.W.ι
  obtain ⟨t', ⟨n₁⟩⟩ : ∃ t' : SAB H _, Nonempty (SABMap t' C.tW e₁) := by
    have pull : ∀ {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S), ∃ t' : SAB H S', Nonempty (SABMap t' t f) := by
      intro S S' f t
      have hC := Out.CubePf.cubePull
      have hsemi : IsSemiAbelian ((Over.pullback f).obj t.G) := by
        refine { comm := ?_, smooth := ?_, separated := ?_, quasiCompact := ?_, geomConnected := ?_, fibres := ?_ }
        · have := t.semi.comm
          infer_instance
        · have := t.semi.smooth
          change Smooth (pullback.snd t.G.hom f)
          infer_instance
        · have := t.semi.separated
          change IsSeparated (pullback.snd t.G.hom f)
          infer_instance
        · have := t.semi.quasiCompact
          change QuasiCompact (pullback.snd t.G.hom f)
          infer_instance
        · have := t.semi.geomConnected
          change GeometricallyConnected (pullback.snd t.G.hom f)
          infer_instance
        · intro Ω _ _ q
          obtain ⟨A⟩ := t.semi.fibres Ω (q ≫ f)
          exact ⟨torusExtOfIso (pullCompIso q f t.G) A⟩
      have hp : ∃ (PP' : RigLB ((Over.pullback f).obj t.G)) (cub : CubicalStr _ PP') (sym : PP'.IsSymmetric) (adj : _) (prim : _)
          (m : SABMap ⟨(Over.pullback f).obj t.G, hsemi, OAct.pullback f t.G t.act, PP', cub,
            sym, adj, prim⟩ t f), m.φ = pullback.fst t.G.hom f := by
        have h := isGrpPullback_pullback t.G f
        obtain ⟨hL, hr, ⟨c', hc'⟩, hs⟩ := hC S S' t.G _ (cubeMapOf h) t.PP t.cub
        have hact : ∀ a, ((OAct.pullback f t.G t.act).act a).left ≫ pullback.fst t.G.hom f =
            pullback.fst t.G.hom f ≫ (t.act.act a).left := fun a => pullback.lift_fst _ _ _
        have pa : ∀ {T : Over S'} (x : T ⟶ (Over.pullback f).obj t.G) a,
            pushPt h.1.w (x ≫ (OAct.pullback f t.G t.act).act a) = pushPt h.1.w x ≫ t.act.act a := fun x a =>
          Over.OverMorphism.ext (by
            show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
            rw [Category.assoc, hact, Category.assoc])
        refine ⟨(cubeMapOf h).rigLB t.PP hL hr, c', hs t.sym, fun a => ?_, ?_, ⟨cubeMapOf h, h, rfl, hact, hc'⟩, rfl⟩
        · let U := lift (pushPt h.1.w (fst ((Over.pullback f).obj t.G) ((Over.pullback f).obj t.G)))
            (pushPt h.1.w (snd ((Over.pullback f).obj t.G) ((Over.pullback f).obj t.G)))
          refine LBIso.chartPull (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down)
            (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) (t.adj a)
          · fin_cases i
            · exact (pa _ a).trans (by simp [U])
            · simp [U]
          · fin_cases i
            · simp [U]
            · exact (pa _ _).trans (by simp [U])
        · let U := pushPt h.1.w (𝟙 ((Over.pullback f).obj t.G))
          refine LBIso.chartPull (chartPullPull t.PP.L _)
            (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) t.prim
          fin_cases i
          · simp [U]
          · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa _ _)
      obtain ⟨_, _, _, _, _, m, -⟩ := hp
      exact ⟨_, ⟨m⟩⟩
    exact pull e₁ C.tW
  obtain ⟨k₁, -⟩ := comp_of_eq C.m₁ n₁ rfl
  obtain ⟨k₂, -⟩ := comp_of_eq mu k₁ ((Category.assoc _ _ _).trans he)
  obtain ⟨n₂, -⟩ := cancel_of_eq C.m₁ k₂ rfl
  obtain ⟨p₁, -⟩ := comp_of_eq C.m₂ n₁ rfl
  obtain ⟨p₂, -⟩ := comp_of_eq C.m₂ n₂ rfl
  have hp : IsProper t'.G.hom := MorphismProperty.of_isPullback k₁.cart.1 inferInstance
  have h₂ : (e₂ ≫ C.j) ≫ C.s = (e₁ ≫ C.j) ≫ C.s ≫ spMap σ.toRingHom := by
    simp only [Category.assoc]
    rw [C.j_over, reassoc_of% C.j_over, ← reassoc_of% he, hρ]
  have h₁ : (e₁ ≫ C.j) ≫ C.s = (e₂ ≫ C.j) ≫ C.s ≫ spMap σ.symm.toRingHom := by
    have : spMap σ.toRingHom ≫ spMap σ.symm.toRingHom = 𝟙 _ := by
      rw [spMap_comp, RingEquiv.toRingHom_comp_symm_toRingHom]
      exact Spec.map_id _
    rw [← Category.assoc _ C.s, h₂, Category.assoc (e₁ ≫ C.j), Category.assoc C.s, this, Category.comp_id]
  obtain ⟨τ, hτ⟩ := GlobalTheory.T.exists_hom_birational_models_ampleFrames hH E H R C.Z C.Z _ C.s _ C.t C.t t' _ _ p₁ p₂ _ C.amp C.amp hR inferInstance hft
    (fun x => ⟨C.normal.1 x, C.normal.2 x⟩) C.proj (isProjOver_comp_iso C.proj σ.symm) C.flat inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance hp h₁ rfl rfl
  obtain ⟨τ', hτ'⟩ := GlobalTheory.T.exists_hom_birational_models_ampleFrames hH E H R C.Z C.Z _ C.s _ C.t C.t t' _ _ p₂ p₁ _ C.amp C.amp hR inferInstance hft
    (fun x => ⟨C.normal.1 x, C.normal.2 x⟩) C.proj (isProjOver_comp_iso C.proj σ) C.flat inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance hp h₂ rfl rfl
  refine ⟨_, e₁, e₂, ⟨τ, τ', ?_, ?_⟩, inferInstance, he, hτ⟩
  · refine ext_of_isDominant (e₁ ≫ C.j) ?_
    rw [← Category.assoc, hτ, hτ', Category.comp_id]
  · refine ext_of_isDominant (e₂ ≫ C.j) ?_
    rw [← Category.assoc, hτ', hτ, Category.comp_id]

end Model

theorem exists_inc {n N : ℕ} (hn : n.Prime) (hN : ∃ j, 1 ≤ j ∧ N = n ^ j) (l : Level H) (h : l.A = N) :
    IsDedekindDomain (RZ H n N) ∧ ∃ β : RZ H n N →+* KA l, IsInc (RZ H n N).subtype (KA l).val.toRingHom β ∧
      Function.Injective β ∧ Flat (spMap β) := by
  subst h
  obtain ⟨j, -, hj⟩ := hN
  obtain ⟨⟨β, hβ⟩, -, h⟩ := BaseRing.isDedFrac_RZ E H l n j hn.pos hj.dvd
  obtain ⟨⟨_, hd⟩, -, hf⟩ := h β hβ
  letI := β.toAlgebra
  refine ⟨hd, β, hβ, IsFractionRing.injective (RZ H n l.A) (KA l), ?_⟩
  rw [Flat.SpecMap_iff]
  exact IsLocalization.flat (KA l) (nonZeroDivisors (RZ H n l.A))

theorem eq_of_isInc {R : Type} [CommRing R] {i : R →+* ℂ} {l : Level H} {β β' : R →+* KA l}
    (h : IsInc i (KA l).val.toRingHom β) (h' : IsInc i (KA l).val.toRingHom β') : β = β' :=
  RingHom.ext fun x => Subtype.ext ((h x).trans (h' x).symm)

theorem eq_of_level (hL : Out.Laws) {D : Datum H} {n N : ℕ} (h3 : 3 ≤ N) (hodd : Odd N) {MM : Scheme.{0}}
    {sM : MM ⟶ Sp (RZ H n N)} {tM : SAB H MM} {lev : D.La → (𝟙_ (Over MM) ⟶ tM.G)} (F : FamCore D sM tM lev)
    {l : Level H} (h : l.A = N) (Xo : Moduli D l) {β : RZ H n N →+* KA l}
    (hβ : IsInc (RZ H n N).subtype (KA l).val.toRingHom β) [Flat (spMap β)] {a a' : Xo.X ⟶ MM}
    (ν : SABMap Xo.univ.t tM a) (ν' : SABMap Xo.univ.t tM a') (ha : a ≫ sM = Xo.s ≫ spMap β)
    (ha' : a' ≫ sM = Xo.s ≫ spMap β) (hν : ∀ x, (Xo.univ.etaA x).left ≫ ν.φ = a ≫ (lev x).left)
    (hν' : ∀ x, (Xo.univ.etaA x).left ≫ ν'.φ = a' ≫ (lev x).left) : a = a' ∧ ν.φ = ν'.φ := by
  subst h
  have := Xo.smooth
  have hs : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  obtain ⟨hr, -, hno⟩ := isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ Xo.s hs
  have e : a = a' := (F.rep _ _ _ _ hr hno inferInstance (fullObj_of_obj Xo.s Xo.univ β hβ)).unique
    ⟨ha, ν, hν⟩ ⟨ha', ν', hν'⟩
  subst e
  exact ⟨rfl, GlobalTheory.fullObj_rigid hL E H D n _ _ _ sM tM lev _ a ν ν' Xo.univ.etaA h3 hodd F.obj hr
    (charZero_residueField Xo.s) hν hν'⟩

theorem exists_top : GlobalTheory.LN.HomExtSt → Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (MM : Scheme.{0}) (sM : MM ⟶ Sp (RZ H n N)) (tM : SAB H MM) (lev : D.La → (𝟙_ (Over MM) ⟶ tM.G)) (m : ℕ) (C : ZOn sM tM m), 1 ≤ D.p + D.q → AuxiliaryInertOddPrime H n → (∃ j, 1 ≤ j ∧ N = n ^ j) → 0 < m → FamCore D sM tM lev → SiegClause D sM tM lev → ∃ T : Top Xo n N, Nonempty (GlobalTheory.LN.AmpFrames T.t.G T.t.PP.L (m ^ 2)) := by
  intro hH hL hL2 E _ _ _ H D Xo n N MM sM tM lev m C hD hn hN hm F hS
  obtain ⟨U, hU, -⟩ := C.good.1
  obtain ⟨u, tU, mU, mM, hu, ufin, usurj, ⟨W₀, hW₀, hiso⟩, hj⟩ :=
    GlobalTheory.T.abelian_locus_open_family_over_level hH hL hL2 E H D n N MM sM tM lev m C U hn.1 (hN.imp fun _ h => h.2) hm F hU
  obtain ⟨i, hio, hi, hi'⟩ := exists_section u W₀
  have hab := F.obj.proper
  have hft := BaseRing.finiteType_RZ H n N
  have hnoeth : IsNoetherianRing (RZ H n N) := Algebra.FiniteType.isNoetherianRing ℤ _
  have hodd : Odd N := by
    obtain ⟨j, -, rfl⟩ := hN
    exact hn.2.1.pow
  have h3 : 3 ≤ N := by
    obtain ⟨j, hj, rfl⟩ := hN
    have h2 := hn.1.two_le
    obtain ⟨c, hc⟩ := hn.2.1
    exact le_trans (by omega) (Nat.le_self_pow (by omega) n)
  have hgen : ∀ {l : Level H} (β : RZ H n N →+* KA l), Function.Injective β → ∀ {T : Scheme.{0}} (f : T ⟶ MM)
      (c : T ⟶ Sp (KA l)), f ≫ sM = c ≫ spMap β → Set.range f ⊆ Set.range W₀.ι := by
    rintro l β hβ T f c h _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    refine hW₀ _ ?_
    rw [← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply]
    exact asIdeal_spMap β hβ _
  have key : ∀ l : Level H, l.A = N → ∃ (β : RZ H n N →+* KA l) (b : (Xo l).X ⟶ W₀.toScheme)
      (ν : SABMap (Xo l).univ.t tM (b ≫ W₀.ι)) (ν' : SABMap (Xo l).univ.t tU (b ≫ i))
      (ν'' : SABMap (Xo l).univ.t C.t (b ≫ i ≫ U.ι)) (h : (b ≫ W₀.ι) ≫ sM = (Xo l).s ≫ spMap β),
      IsInc (RZ H n N).subtype (KA l).val.toRingHom β ∧ Function.Injective β ∧ Flat (spMap β) ∧
      ν.φ = ν'.φ ≫ mM.φ ∧ ν''.φ = ν'.φ ≫ mU.φ ∧
      (∀ x, ((Xo l).univ.etaA x).left ≫ ν.φ = (b ≫ W₀.ι) ≫ (lev x).left) ∧
      IsFinite (pullback.lift _ _ h) ∧ Surjective (pullback.lift _ _ h) := by
    intro l h
    obtain ⟨-, β, hβ, hinj, hfl⟩ := exists_inc hn.1 hN l h
    have hc : N.Coprime l.M := by
      obtain ⟨j, -, rfl⟩ := hN
      exact ((exists_two_auxiliary_inert_odd_primes_coprime_level E H).2 n hn l).pow_left j
    obtain ⟨a, ν, ha, h₁, h₂, h₃⟩ := GlobalTheory.T.moduli_finite_surjective_over_generic_family hL hL2 E H D n N MM sM tM lev l (Xo l) β h hn.1 hn.2.1 hN hc hβ F
    obtain ⟨b, rfl⟩ : ∃ b, b ≫ W₀.ι = a := ⟨_, IsOpenImmersion.lift_fac W₀.ι a (hgen β hinj a _ ha)⟩
    obtain ⟨ν', hν'⟩ := cancel_of_eq (g := b ≫ i) mM ν (by rw [Category.assoc, hi])
    obtain ⟨ν'', hν''⟩ := comp_of_eq mU ν' (Category.assoc _ _ _)
    exact ⟨β, b, ν, ν', ν'', ha, hβ, hinj, hfl, hν', hν'', h₁, h₂, h₃⟩
  choose β b ν ν' ν'' hb hβ hinj hfl hν hν' hlev hfin hsurj using key
  refine ⟨{
    Z := C.Z, s := C.s, normal := fun x => ⟨C.normal.1 x, C.normal.2 x⟩, proj := C.proj, flat := C.flat, t := C.t, qproj := C.qproj
    good := C.good, ga := genericPoints_subset C, a := fun l h => b l h ≫ i ≫ U.ι, m := ν''
    fin := ?_, compat := ?_, sym := ?_, U := U, U_eq := hU, MM := MM, sM := sM, tM := tM, lev := lev
    MM_red := F.red, MM_flat := F.flat, MM_ab := hab, u := u, u_over := hu, u_fin := ufin, u_surj := usurj
    u_gen := ⟨W₀, hW₀, hiso⟩, tU := tU, mU := mU, mM := mM, lev_eq := ?_, sieg := hS }, ⟨C.amp⟩⟩
  · intro l h β' hβ'
    obtain rfl := eq_of_isInc (hβ l h) hβ'
    obtain ⟨f, hf⟩ := exists_finite_lift U C.s sM (spMap (β l h)) u hu W₀.ι i hi hi'
      (hgen _ (hinj l h) _ _ pullback.condition) (b l h) (Xo l).s (hb l h) (hfin l h) (hsurj l h)
    exact ⟨_, f, by rw [← hU]; rfl, hf⟩
  · intro l l' h h' r κ k hk hr hκ
    have hkβ : k.comp (β l h) = β l' h' :=
      eq_of_isInc (i := (RZ H n N).subtype) (fun x => (hk _).trans (hβ l h x)) (hβ l' h')
    obtain ⟨κ', hκ'⟩ := comp_of_eq (ν l h) κ rfl
    have := hfl l' h'
    obtain ⟨e₁, e₂⟩ := eq_of_level hL h3 hodd F h' (Xo l') (hβ l' h') κ' (ν l' h')
      (by rw [Category.assoc, hb, reassoc_of% hr, spMap_comp, hkβ]) (hb l' h')
      (fun x => by rw [hκ', reassoc_of% hκ x, hlev, Category.assoc r]) (hlev l' h')
    have e₃ : r ≫ b l h = b l' h' := by rwa [← cancel_mono W₀.ι, Category.assoc]
    refine ⟨by rw [reassoc_of% e₃], ?_⟩
    have e₄ : κ.φ ≫ (ν' l h).φ = (ν' l' h').φ := by
      apply mM.cart.1.hom_ext
      · rw [Category.assoc]
        exact (congrArg (κ.φ ≫ ·) (hν l h).symm).trans (hκ'.symm.trans (e₂.trans (hν l' h')))
      · rw [Category.assoc, (ν' l h).cart.1.w, (ν' l' h').cart.1.w, reassoc_of% κ.cart.1.w, reassoc_of% e₃]
    rw [hν', hν', reassoc_of% e₄]
  · intro l h r κ g σ hσ hr hκ
    obtain ⟨ρ, mu, σ₀, h₁, h₂, -⟩ := GlobalTheory.T.fullLevelChange_acts_on_unitaryFamily hL hL2 E H D n N MM sM tM lev l (Xo l) (β l h) _ (ν l h) (hb l h) r κ g σ
      hD h hn.1 hn.2.1 hN (hβ l h) F (hsurj l h) (hlev l h) hσ hr hκ
    obtain ⟨W', e₁, e₂, τ, hd, he, hτ⟩ := exists_iso C hH (exists_inc hn.1 hN l h).1 hft ρ mu σ₀ h₂
    obtain ⟨j', hj'⟩ : ∃ j', j' ≫ U.ι = C.j :=
      ⟨_, IsOpenImmersion.lift_fac U.ι C.j (by rw [Scheme.Opens.range_ι, hU]; exact range_j_subset C)⟩
    have hju := hj j' hj'
    have := isSeparated C
    have := isReduced_of_normal (fun x => ⟨C.normal.1 x, C.normal.2 x⟩)
    rw [← hj'] at hd hτ
    refine ⟨τ, ?_⟩
    rw [← Category.assoc r.hom]
    exact comp_eq_of_dense U.ι u W₀.ι i hi hi' j' e₁ e₂ ρ (by rw [reassoc_of% hju, hju, he]) τ.hom hτ _ _
      (by simpa only [Category.assoc] using h₁)
  · intro l h a' x y ha hy
    have e : a' = b l h ≫ i := by rw [← cancel_mono U.ι, ha, Category.assoc]
    have : Mono mU.φ := MorphismProperty.of_isPullback (P := .monomorphisms _) mU.cart.1.flip
      (inferInstanceAs (Mono U.ι))
    have e' : y = ((Xo l).univ.etaA x).left ≫ (ν' l h).φ := by
      rw [← cancel_mono mU.φ, hy, hν', Category.assoc]
    rw [e', Category.assoc, ← hν, hlev, e, Category.assoc, Category.assoc, reassoc_of% hi]

end GlobalTheory.TopOfFamily
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFullLevelModelOfFamilyBirationalModelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fullLevel_model_of_family_birationalModel : GlobalTheory.LN.HomExtSt → Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (MM : Scheme.{0}) (sM : MM ⟶ Sp (RZ H n N)) (tM : SAB H MM) (lev : D.La → (𝟙_ (Over MM) ⟶ tM.G)) (m : ℕ) (C : ZOn sM tM m), 1 ≤ D.p + D.q → AuxiliaryInertOddPrime H n → (∃ j, 1 ≤ j ∧ N = n ^ j) → 0 < m → FamCore D sM tM lev → SiegClause D sM tM lev → ∃ T : Top Xo n N, Nonempty (GlobalTheory.LN.AmpFrames T.t.G T.t.PP.L (m ^ 2)) := by
  first | exact @GlobalTheory.TopOfFamily.exists_top | exact GlobalTheory.TopOfFamily.exists_top | (intros; apply GlobalTheory.TopOfFamily.exists_top <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniversalFullLevelOfPelThetaFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniversalFullLevelOfPelThetaFamily
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.TripleTheta

open CharZeroPts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {g : ℕ} {J : Type}

theorem map_bas {A : Type} [CommGroup A] (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (u : D.La → A)
    (hu : ∀ x y, u (x + y) = u x * u y) (v : Fin (2 * g) → ℤ) :
    u (bas v) = ∏ i, u (bas (Pi.single i 1)) ^ v i := by
  rw [LatticeTorsion.eq_prod_zpow ((Pi.basisFun ℤ (Fin (2 * g))).map bas) u hu]
  simp

theorem map_nsmul' {A : Type} [Group A] (u : D.La → A) (hu : ∀ x y, u (x + y) = u x * u y) (n : ℕ) (x : D.La) :
    u (n • x) = u x ^ n :=
  (MonoidHom.mk' (fun x : Multiplicative D.La => u x.toAdd) fun _ _ => hu _ _).map_pow (Multiplicative.ofAdd x) n

theorem existsUnique_coeff {A : Type} [CommGroup A] (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (u : D.La → A)
    (hu : ∀ x y, u (x + y) = u x * u y) {N : ℕ} (hN : 0 < N) (hk : ∀ x, u x = 1 ↔ ∃ y, x = N • y) (x : D.La) :
    ∃! c : Fin (2 * g) → ZMod N, ∏ i, u (bas (Pi.single i 1)) ^ (c i).val = u x := by
  have : NeZero N := ⟨hN.ne'⟩
  obtain ⟨v, rfl⟩ := bas.surjective x
  have key : ∀ c : Fin (2 * g) → ZMod N,
      ∏ i, u (bas (Pi.single i 1)) ^ (c i).val = u (bas v) ↔ c = fun i => (v i : ZMod N) := fun c => by
    have e₁ : ∏ i, u (bas (Pi.single i 1)) ^ (c i).val = u (bas fun i => ((c i).val : ℤ)) := by
      rw [map_bas bas u hu]; simp only [zpow_natCast]
    have e₂ := hu (bas (v - fun i => ((c i).val : ℤ))) (bas fun i => ((c i).val : ℤ))
    rw [← map_add (f := _), sub_add_cancel] at e₂
    rw [e₁, e₂, right_eq_mul, hk]
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨w, rfl⟩ := bas.surjective y
      rw [← map_nsmul] at hy
      funext i
      have := congrArg (fun z : ℤ => (z : ZMod N)) (congrFun (bas.injective hy) i)
      simp at this
      exact (sub_eq_zero.1 this).symm
    · intro hc
      have : ∀ i, ∃ w : ℤ, v i - ((c i).val : ℤ) = N * w := fun i =>
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).1 (by simp [hc])
      choose w hw using this
      refine ⟨bas w, ?_⟩
      rw [← map_nsmul]
      congr 1
      funext i
      simpa using hw i
  simp only [key]
  exact existsUnique_eq

theorem coe_rt (n N : ℕ) : ((RZ.rt H n N : RZ H n N) : ℂ) = H.rt0 := by
  show ((2 : RZ H n N) : ℂ) * ((1 + H.rt0) / 2) - 1 = H.rt0
  have : ((2 : RZ H n N) : ℂ) = 2 := map_ofNat (RZ H n N).subtype 2
  rw [this]; ring

theorem rt_sq (n N : ℕ) : RZ.rt H n N ^ 2 = -(H.d : RZ H n N) := by
  apply Subtype.ext
  push_cast
  rw [coe_rt, H.sqrt_neg_disc_sq]

theorem map_unitS {o K : Type} [CommRing o] [CommRing K] {S : Scheme.{0}} (s : S ⟶ Sp o) (x : Sp K ⟶ S) (β : o →+* K)
    (h : x ≫ s = spMap β) (u : oˣ) (v : Kˣ) (hv : (v : K) = β u) :
    Units.map x.appTop.hom.toMonoidHom (unitS s u) = unitOn v := by
  apply Units.ext
  show x.appTop.hom (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom u)) =
    (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom v
  have e := congrArg (fun q => q.hom (u : o)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β))
  have e' := congrArg (fun q : Sp K ⟶ Sp o => q.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom u)) h
  rw [hv]
  exact e'.trans e.symm


set_option maxHeartbeats 800000 in
theorem exists_under (hL : Out.Laws) {n N : ℕ} (hN : 0 < N) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La)
    (hbas : IsSympBasis D bas) (b : TBase (RZ H n N) N) (hb : (b.ζ : RZ H n N) = RZ.ze H n N) {S : Scheme.{0}}
    {s : S ⟶ Sp (RZ H n N)} [Flat s] {t : SAB H S} {lv : D.La → (𝟙_ (Over S) ⟶ t.G)} (h : FullObj D s t lv) :
    ∃ T : TObj g N J b s, Under t lv a bas T ∧ IsPEL D a bas (RZ.rt H n N) T t := by
  have hab : IsAbelianScheme t.G := ⟨t.semi.comm, t.semi.smooth, h.proper, t.semi.geomConnected⟩
  have hg : Module.finrank ℚ E / 2 * (D.p + D.q) = g := by
    have := bas.finrank_eq
    rw [datum_finrank_int, Module.finrank_fin_fun] at this
    omega
  have hdim : SmoothOfRelativeDimension g t.G.hom := by
    have := t.semi.smooth
    have := t.semi.geomConnected
    refine smoothOfRelativeDimension_of_generization _ g fun y => ?_
    obtain ⟨K, _, _, _, z, β, hβ, hz⟩ := exists_generization (t.G.hom ≫ s) y
    refine ⟨K, inferInstance, z, hz, fun m hm => ?_⟩
    refine (ObjDim.dim_eq_of_detCond D t.act (z ≫ t.G.hom) ?_
      (h.geom K _ β ((Category.assoc _ _ _).trans hβ)).1 hm).trans hg
    rw [← map_pow, rt_sq, map_neg, map_natCast]
  let pt : Fin (2 * g) → (Out.baseOver S ⟶ t.G) := fun i => toUnit _ ≫ lv (bas (Pi.single i 1))
  have hpt : ∀ i, pt i ^ N = 1 := fun i => by
    rw [← MonObj.comp_pow, ← map_nsmul' lv h.add, h.ker, MonObj.comp_one]
  have hptx : ∀ {X : Scheme.{0}} (x : X ⟶ S) (i), toB x ≫ pt i = toUnit _ ≫ lv (bas (Pi.single i 1)) := fun x i => by
    rw [← Category.assoc, toUnit_unique (toB x ≫ toUnit _) (toUnit _)]
  have hu : IsUnit (N : Γ(S, ⊤)) := by
    have := b.unit.map (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of (RZ H n N))).inv.hom)
    rwa [map_natCast] at this
  have hζ : b.ζ ^ N = 1 := by
    apply Units.ext
    apply Subtype.val_injective
    exact (b.prim ℂ (RZ H n N).subtype).pow_eq_one
  let P : Out.PolAV S :=
    { A := t.G, isAb := hab, g := g, smoothDim := hdim, L := t.PP.L, isLB := t.PP.isLB, rigid := ObjDim.rigidified,
      sym := ObjDim.sym, ample := h.ample, ktriv := h.ktriv }
  have : IsMonHom (Iso.refl t.G).hom := inferInstanceAs (IsMonHom (𝟙 t.G))
  have hid : LBIso t.PP.L (t.PP.L.pull (Iso.refl t.G).hom.left) :=
    LBIso.chartPull (chartPullId _) (Geo.Tor.chartPullPull _ _ (𝟙 _) (Category.id_comp _).symm)
      (PolBaseChange.lbIso_refl t.PP.isLB)
  have hpl : ∀ i, (lv (bas (Pi.single i 1))).left ≫ (Iso.refl t.G).hom.left = (pt i).left := fun i => by
    have e : (toUnit (Out.baseOver S)).left = 𝟙 S := ObjPull.toUnit_left' _
    rw [Iso.refl_hom, Over.id_left, Category.comp_id, Over.comp_left, e]
    exact (Category.id_comp (X := S) _).symm
  refine ⟨{ A := t.G, ab := hab, dim := hdim, L := t.PP.L, isLB := t.PP.isLB, rigid := ObjDim.rigidified,
            sym := ObjDim.sym, ample := h.ample, ktriv := h.ktriv, pt := pt, torsion := hpt,
            bij := torsion_basis_of_generization t.G N _ pt hab hN hu hpt fun p => ?_,
            pairing := fun i j => weilIs_of_generization hL P N _ _ _ hN hu (hpt i) (hpt j) ?_ fun p => ?_,
            act := fun j => t.act.act (a j), hom := fun j => t.act.hom _ },
    ⟨Iso.refl _, this, hid, fun j => by simp, hpl⟩,
    ⟨Iso.refl _, this, hid, fun j => by simp, fun K _ _ _ x β hx => ?_⟩⟩
  · obtain ⟨K, _, _, _, z, β, hβ, hz⟩ := exists_generization s p
    obtain ⟨-, I, -, hI⟩ := h.geom K z β hβ
    refine ⟨K, inferInstance, inferInstance, z, hz, fun y hy => ?_⟩
    obtain ⟨x, rfl⟩ := (I.onto N hN y).1 hy
    simp only [hptx, hI, Out.linComb, List.prod_ofFn]
    exact existsUnique_coeff bas (I.ev N) (I.add N) hN (I.ker N hN) x
  · rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, unitS, unitOn, ← map_pow, ← map_pow, hζ, map_one,
      map_one, one_zpow]
  · obtain ⟨K, _, _, _, z, β, hβ, hz⟩ := exists_generization s p
    obtain ⟨-, I, hIζ, hI⟩ := h.geom K z β hβ
    refine ⟨K, inferInstance, z, hz, ?_⟩
    have hc : Units.map z.appTop.hom.toMonoidHom (unitS s b.ζ ^ Out.stdSymp g i j) =
        unitOn (I.ζ N ^ Out.stdSymp g i j) := by
      rw [map_zpow, map_unitS s z β hβ b.ζ (I.ζ N) (by rw [hIζ, hb]), unitOn, unitOn, map_zpow]
    have e : Out.WeilIs t.G t.PP.L N (toB z ≫ pt i) (toB z ≫ pt j)
        (Units.map z.appTop.hom.toMonoidHom (unitS s b.ζ ^ Out.stdSymp g i j)) := by
      rw [hc, hptx z i, hptx z j, hI, hI, ← hbas i j]
      exact I.isom N hN _ _
    exact e
  · obtain ⟨hd, I, hIζ, hI⟩ := h.geom K x β hx
    refine ⟨hd, I, by rw [hIζ, hb], fun i => ?_⟩
    have e : I.ev N (bas (Pi.single i 1)) ≫ 𝟙 t.G = toB x ≫ pt i := by rw [hptx, hI, Category.comp_id]
    exact e

theorem exists_level {n N : ℕ} {a : J → 𝓞 E} {bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La}
    {b : TBase (RZ H n N) N} (hb : (b.ζ : RZ H n N) = RZ.ze H n N) {S : Scheme.{0}}
    {s : S ⟶ Sp (RZ H n N)} {t : SAB H S} {T : TObj g N J b s} (h : IsPEL D a bas (RZ.rt H n N) T t) :
    ∃ lv : D.La → (𝟙_ (Over S) ⟶ t.G), Under t lv a bas T ∧ FullObj D s t lv := by
  obtain ⟨φ, hφ, hφL, hφa, hgeom⟩ := h
  let j : 𝟙_ (Over S) ⟶ Out.baseOver S := Over.homMk (𝟙 S) (Category.id_comp _)
  let q : Fin (2 * g) → (𝟙_ (Over S) ⟶ t.G) := fun i => j ≫ T.pt i ≫ φ.inv
  have hq : ∀ i, q i ^ N = 1 := fun i => by
    rw [← MonObj.comp_pow, ← MonObj.pow_comp, T.torsion, MonObj.one_comp, MonObj.comp_one]
  let lv : D.La → (𝟙_ (Over S) ⟶ t.G) := fun x => ∏ i, q i ^ bas.symm x i
  have hadd : ∀ x y, lv (x + y) = lv x * lv y := fun x y => by
    simp only [lv, map_add (f := _), Pi.add_apply, zpow_add, Finset.prod_mul_distrib]
  have hlv : ∀ i, lv (bas (Pi.single i 1)) = q i := fun i => by
    simp only [lv, LinearEquiv.symm_apply_apply]
    rw [Finset.prod_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (by simp)]
    simp
  obtain ⟨hab, hA, hK⟩ := PolPull.pol_pull_of_relAmple_local AmpleLocal.relAmple_of_locally S S T.A t.G _ _ T.L t.PP.L
    T.isLB t.PP.isLB T.ab (isGrpPullback_of_iso φ) hφL
  refine ⟨lv, ⟨φ, hφ, hφL, hφa, fun i => ?_⟩, hab.proper, hA T.ample, hK T.ktriv, hadd, fun x => ?_,
    fun K _ _ _ x β hx => ?_⟩
  · rw [hlv]
    show (𝟙 S ≫ (T.pt i).left ≫ φ.inv.left) ≫ _ = _
    rw [Category.assoc, Category.assoc, inv_hom_left]
    exact (Category.id_comp _).trans (Category.comp_id _)
  · rw [map_nsmul' lv hadd, ← Finset.prod_pow]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hq, one_zpow]
  · obtain ⟨hd, I, hIζ, hI⟩ := hgeom K x β hx
    refine ⟨hd, I, by rw [hIζ, hb], eq_of_basis bas (fun y => toUnit _ ≫ lv y) (I.ev N)
      (fun y y' => by rw [hadd, MonObj.comp_mul]) (I.add N) fun i => ?_⟩
    have e : toUnit (Over.mk x) ≫ j = toB x := Over.OverMorphism.ext
      ((Category.comp_id _).trans (ObjPull.toUnit_left' _))
    rw [hlv, ← Category.assoc, e, ← Category.assoc, Iso.comp_inv_eq]
    exact (hI i).symm

theorem arBase_RZ (H : Host E) {n N e : ℕ} (hn : 0 < n) (hN : 0 < N) (h : N ∣ n ^ e) : ArBase (RZ H n N).subtype := by
  obtain ⟨l⟩ : Nonempty (Level H) := HostModel.instNonemptyLevel H
  exact ⟨BaseRing.isDedekindDomain_RZ { l with A := N, A_pos := hN } hn h, BaseRing.finiteType_RZ H n N,
    Subtype.val_injective⟩

end GlobalTheory.TripleTheta

namespace GlobalTheory


open TripleTheta CharZeroPts in
theorem exists_famCore_of_thetaFam : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n N' : ℕ) (g : ℕ) (J : Type) [Finite J] (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (b : TBase (RZ H n (N' ^ 2)) (N' ^ 2)) (F : ThetaFam n (RZ H n (N' ^ 2)).subtype (PELClass (b := b) D a bas (RZ.rt H n (N' ^ 2)) (RZ H n (N' ^ 2)).subtype)) (τ : SAB H F.MM), IsSympBasis D bas → Subring.closure (Set.range a) = ⊤ → (∃ w w', a w = H.w0 ∧ a w' = H.bar H.w0) → (b.ζ : RZ H n (N' ^ 2)) = RZ.ze H n (N' ^ 2) → IsPEL D a bas (RZ.rt H n (N' ^ 2)) F.univ τ → SmoothOfRelativeDimension D.dim (pullback.snd F.s (spMap (algebraMap (RZ H n (N' ^ 2)) (FractionRing (RZ H n (N' ^ 2)))))) → 1 ≤ D.p + D.q → n.Prime → Odd n → (∃ j, 1 ≤ j ∧ N' = n ^ j) → ∃ lev : D.La → (𝟙_ (Over F.MM) ⟶ τ.G), FamCore D F.s τ lev := by
  intro hL hL2 E _ _ _ H D n N' g J _ a bas b F τ hbas ha ⟨w, w', hw, hw'⟩ hb hP hsm hpq hn _ ⟨j, _, hj⟩
  have hN : 0 < N' ^ 2 := by rw [hj]; exact pow_pos (pow_pos hn.pos _) _
  have hbase : ArBase (RZ H n (N' ^ 2)).subtype := arBase_RZ H (e := j * 2) hn.pos hN (by rw [hj, pow_mul])
  obtain ⟨lev, hU, hF⟩ := exists_level hb hP
  refine ⟨lev, F.reduced, F.flat, F.qproj, SmoothOfRelativeDimension.smooth D.dim _, hF,
    fun S s t lv hS _ hs ho => ?_, fun k _ x t lv ν ν' hx hν hν' => ?_⟩
  · obtain ⟨T, hT, hTP⟩ := exists_under hL hN a bas hbas b hb ho
    obtain ⟨f, ⟨hf, hm⟩, huniq⟩ := F.rep S s T hS fun p => by
      obtain ⟨K, _, _, _, z, β, -, hz⟩ := exists_generization s p
      exact (hz (default : PrimeSpectrum K)).mem_closed isClosed_closure (subset_closure ⟨K, inferInstance, z, ⟨_, rfl⟩,
        PELFrom.fromC_of_isPEL hL hL2 E H D g J a w w' bas hpq hbas hw hw' ha N' _ b _ _ (coe_rt n _) hbase S s T t hTP K z⟩)
    exact ⟨f, ⟨hf, sabMap_of_tmap hU hT hF.add ho.add ha hS ho.proper hm⟩,
      fun f' ⟨hf', ν, hν⟩ => huniq f' ⟨hf', tmap_of_sabMap hU hT ν hν⟩⟩
  · obtain ⟨T, hT⟩ := tObj_pull _ g _ J b _ _ F.s (x ≫ F.s) x F.univ rfl
    exact F.unram k x T hx hT (tmap_of_sabMap hU (under_of_tmap hU hT ν hν) ν' hν')

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniversalFullLevelOfPelThetaFamilyStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_universal_fullLevel_of_pelThetaFamily : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n N' : ℕ) (g : ℕ) (J : Type) [Finite J] (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (b : TBase (RZ H n (N' ^ 2)) (N' ^ 2)) (F : ThetaFam n (RZ H n (N' ^ 2)).subtype (PELClass (b := b) D a bas (RZ.rt H n (N' ^ 2)) (RZ H n (N' ^ 2)).subtype)) (τ : SAB H F.MM), IsSympBasis D bas → Subring.closure (Set.range a) = ⊤ → (∃ w w', a w = H.w0 ∧ a w' = H.bar H.w0) → (b.ζ : RZ H n (N' ^ 2)) = RZ.ze H n (N' ^ 2) → IsPEL D a bas (RZ.rt H n (N' ^ 2)) F.univ τ → SmoothOfRelativeDimension D.dim (pullback.snd F.s (spMap (algebraMap (RZ H n (N' ^ 2)) (FractionRing (RZ H n (N' ^ 2)))))) → 1 ≤ D.p + D.q → n.Prime → Odd n → (∃ j, 1 ≤ j ∧ N' = n ^ j) → ∃ lev : D.La → (𝟙_ (Over F.MM) ⟶ τ.G), FamCore D F.s τ lev := by
  first | exact @GlobalTheory.exists_famCore_of_thetaFam | exact GlobalTheory.exists_famCore_of_thetaFam | (intros; apply GlobalTheory.exists_famCore_of_thetaFam <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFullLevelModelAmpleFrames
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.Models

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_ringGenerators (x y : 𝓞 E) : ∃ (J : Type) (_ : Finite J) (a : J → 𝓞 E) (w w' : J),
    a w = x ∧ a w' = y ∧ Subring.closure (Set.range a) = ⊤ := by
  classical
  let b := NumberField.RingOfIntegers.basis E
  refine ⟨Option (Option (Module.Free.ChooseBasisIndex ℤ (𝓞 E))), inferInstance,
    fun j => Option.elim j x (fun j' => Option.elim j' y b), none, some none, rfl, rfl, ?_⟩
  rw [eq_top_iff]
  rintro z -
  have hz : z ∈ Submodule.span ℤ (Set.range b) := by
    rw [b.span_eq]
    exact Submodule.mem_top
  induction hz using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨i, rfl⟩ := hu
    exact Subring.subset_closure ⟨some (some i), rfl⟩
  | zero => exact zero_mem _
  | add u v _ _ hu hv => exact add_mem hu hv
  | smul m u _ hu => exact zsmul_mem hu m

theorem RZ.coe_rt (H : Host E) (S A : ℕ) : (RZ H S A).subtype (RZ.rt H S A) = H.rt0 := by
  rw [RZ.rt, map_sub, map_mul, map_ofNat, map_one]
  show 2 * ((1 + H.rt0) / 2) - 1 = H.rt0
  ring

theorem exists_tBase_RZ (H : Host E) {n N e : ℕ} (hn : 0 < n) (hN : N = n ^ e) :
    ∃ b : TBase (RZ H n N) N, (b.ζ : RZ H n N) = RZ.ze H n N := by
  have hN0 : N ≠ 0 := by
    rw [hN]
    exact pow_ne_zero _ hn.ne'
  have hζ : IsPrimitiveRoot (zeta N) N := Complex.isPrimitiveRoot_exp N hN0
  have hpow : (RZ.ze H n N) ^ N = 1 := by
    apply Subtype.val_injective
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    exact hζ.pow_eq_one
  have hinv : ((n : ℂ))⁻¹ ∈ RZ H n N := Subring.subset_closure (Or.inr (Or.inl rfl))
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hunit_n : IsUnit (n : RZ H n N) := by
    refine isUnit_iff_exists_inv.mpr ⟨⟨_, hinv⟩, ?_⟩
    apply Subtype.val_injective
    simp [hn']
  have hunit : IsUnit (N : RZ H n N) := by
    have h : (N : RZ H n N) = (n : RZ H n N) ^ e := by rw [← Nat.cast_pow, ← hN]
    rw [h]
    exact hunit_n.pow e
  have key : ∀ {S : Type} [CommRing S] (f : RZ H n N →+* S),
      (Polynomial.cyclotomic N ℤ).eval₂ (Int.castRingHom S) (f (RZ.ze H n N)) =
        f ((Polynomial.cyclotomic N ℤ).eval₂ (Int.castRingHom (RZ H n N)) (RZ.ze H n N)) := by
    intro S _ f
    rw [Polynomial.hom_eval₂]
    congr 1
    exact RingHom.ext_int _ _
  have h0 : (Polynomial.cyclotomic N ℤ).eval₂ (Int.castRingHom (RZ H n N)) (RZ.ze H n N) = 0 := by
    apply Subtype.val_injective
    show (RZ H n N).subtype _ = (RZ H n N).subtype 0
    rw [map_zero, ← key]
    have hr := ((Polynomial.isRoot_cyclotomic_iff_charZero (R := ℂ) (Nat.pos_of_ne_zero hN0)).mpr hζ).eq_zero
    rw [← Polynomial.map_cyclotomic_int, Polynomial.eval_map] at hr
    exact hr
  refine ⟨⟨Units.ofPowEqOne _ N hpow hN0, hunit, ?_⟩, rfl⟩
  intro K _ β
  have : NeZero ((N : ℕ) : K) := ⟨by simpa [map_natCast] using (hunit.map β).ne_zero⟩
  show IsPrimitiveRoot (β (RZ.ze H n N)) N
  apply Polynomial.isRoot_cyclotomic_iff.mp
  show Polynomial.eval _ _ = 0
  rw [← Polynomial.map_cyclotomic_int, Polynomial.eval_map, key, h0, map_zero]

theorem arBase_RZ (H : Host E) {n N e : ℕ} (hn : 0 < n) (hN : N = n ^ e) : ArBase (RZ H n N).subtype := by
  have hN0 : 0 < N := by
    rw [hN]
    exact pow_pos hn e
  have hrt2 : H.rt ^ 2 = -(H.d : 𝓞 E) := H.5
  have hw0 : 2 * H.w0 = 1 + H.rt := H.7
  have hd16 : H.d % 16 = 7 := H.2
  have hconj : ∀ a : 𝓞 E, ((H.bar a : 𝓞 E) : E) = IsCMField.complexConj E (a : E) := H.9
  have hd0 : (0 : ℝ) < H.d := by exact_mod_cast H.3.pos

  have hbar_rt : H.bar H.rt = -H.rt := by
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have hE : (H.rt : E) ^ 2 = -(H.d : E) := by
      have h := congrArg ((↑) : 𝓞 E → E) hrt2
      push_cast at h
      exact h
    have hz2 : (φ (H.rt : E)) ^ 2 = -(H.d : ℂ) := by
      rw [← map_pow, hE, map_neg, map_natCast]
    set z := φ (H.rt : E) with hz
    have hx : z.re = 0 := by
      have h1 := congrArg Complex.re hz2
      have h2 := congrArg Complex.im hz2
      simp only [sq, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
        Complex.natCast_re, Complex.natCast_im, neg_zero] at h1 h2
      have h3 : z.re * z.im = 0 := by nlinarith
      rcases mul_eq_zero.mp h3 with h | h
      · exact h
      · exfalso
        rw [h] at h1
        nlinarith [mul_self_nonneg z.re]
    have hc : φ (IsCMField.complexConj E (H.rt : E)) = φ (-(H.rt : E)) := by
      rw [IsCMField.complexEmbedding_complexConj, map_neg, ← hz]
      apply Complex.ext <;> simp [hx]
    have h4 : ((H.bar H.rt : 𝓞 E) : E) = ((-H.rt : 𝓞 E) : E) := by
      rw [hconj, φ.injective hc]
      norm_cast
    exact_mod_cast h4
  obtain ⟨m, hm⟩ : ∃ m, H.d = 16 * m + 7 := ⟨H.d / 16, by omega⟩
  have hdE : (H.d : 𝓞 E) = 16 * m + 7 := by
    rw [hm]
    push_cast
    ring
  have hbal : H.bar (2 + H.rt) = 2 - H.rt := by
    rw [map_add (f := _), map_ofNat, hbar_rt]
    ring
  have hal : (2 + H.rt) ∈ Algebra.adjoin ℤ {H.w0} := by
    have h : 2 + H.rt = 1 + H.w0 + H.w0 := by linear_combination -hw0
    rw [h]
    have hw := Algebra.subset_adjoin (R := ℤ) (Set.mem_singleton H.w0)
    exact add_mem (add_mem (one_mem _) hw) hw

  obtain ⟨l, hl⟩ : ∃ l : Level H, l.A = N := by
    refine ⟨⟨H.d + 4, by omega, ⟨H.d / 2 + 2, by omega⟩, Ideal.span {2 + H.rt}, ?_, ?_, ?_, N, hN0⟩, rfl⟩
    · exact le_antisymm
        (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr
          (Ideal.subset_span ⟨Ideal.subset_span (Set.mem_singleton _), hal⟩)))
        (Ideal.span_le.mpr fun a ha => ha.1)
    · rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_mul_span_singleton]
      congr 2
      rw [RingEquiv.coe_toRingHom, hbal]
      push_cast
      linear_combination -hrt2
    · rw [Ideal.map_span, Set.image_singleton, Ideal.eq_top_iff_one]
      have h1 : (1 : 𝓞 E) = ((4 * m + 3 : 𝓞 E) - (2 - H.rt)) * (2 + H.rt) +
          (4 * m + 3 : 𝓞 E) * H.bar (2 + H.rt) := by
        rw [hbal]
        linear_combination -hrt2 + hdE
      rw [h1]
      exact Submodule.add_mem_sup (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton _)))
        (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton _)))
  subst hl
  obtain ⟨⟨β, hβ⟩, hft, hded⟩ := BaseRing.isDedFrac_RZ E H l n e hn ⟨1, by rw [hN, Nat.mul_one]⟩
  obtain ⟨⟨_, hD⟩, -, -⟩ := hded β hβ
  exact ⟨hD, hft, Subtype.val_injective⟩

theorem one_le_finrank_div_two : 1 ≤ Module.finrank ℚ E / 2 := by
  have h1 := NumberField.IsTotallyComplex.finrank (K := E)
  have h2 : 0 < Module.finrank ℚ E := Module.finrank_pos
  omega

theorem topAmpExists : GlobalTheory.LN.HomExtSt → Out.Laws → Out.Laws2 → GlobalTheory.Published.SemistableReductionSt → GlobalTheory.ZH.ThmUSt → GlobalTheory.ZH.UTorsSt → GlobalTheory.ZH.ZHGeoSt → (∀ (g n : ℕ) (J : Type) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Finite (IsLocalRing.ResidueField V)] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (β : o →+* V) (t : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V K) ≫ spMap β)) (v : Ix g ((n ^ j) ^ 2) → V), t.Prim w w' → t.HasTh (𝟙 _) (fun a => algebraMap V K (v a)) → Coset n (n ^ j) v (IsLocalRing.maximalIdeal V) → ∃ (V' K' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : Field K') (_ : Algebra V' K') (_ : IsFractionRing V' K') (φ : V →+* V') (ψ : K →+* K') (t' : TObj g ((n ^ j) ^ 2) J b (spMap φ ≫ spMap β)) (tK : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V' K') ≫ spMap φ ≫ spMap β)), IsLocalHom φ ∧ ψ.comp (algebraMap V K) = (algebraMap V' K').comp φ ∧ TMap tK t (spMap ψ) ∧ TMap tK t' (spMap (algebraMap V' K')) ∧ t'.HasTh (𝟙 _) (fun a => φ (v a))) → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → TopAmpExists := by
  intro hHE hL hL2 hSR hTU hUT hZG hRed hGen hTh
  unfold TopAmpExists
  intro E _ _ _ H D hpq Xo n hn
  have hnp : n.Prime := hn.1
  have hno : Odd n := hn.2.1
  have hn0 : 0 < n := hnp.pos
  obtain ⟨bas, hbas⟩ := GlobalTheory.ZM.exists_isSympBasis E H D
  obtain ⟨J, hJ, a, w, w', haw, haw', hcl⟩ := exists_ringGenerators H.w0 (H.bar H.w0)
  have := hJ
  have hg1 : 1 ≤ Module.finrank ℚ E / 2 * (D.p + D.q) :=
    calc 1 = 1 * 1 := rfl
      _ ≤ _ := Nat.mul_le_mul (one_le_finrank_div_two (E := E)) hpq
  obtain ⟨j₁, hj₁⟩ := GlobalTheory.T.exists_thetaFamily_pel_smooth_generic_fibre hL hL2 hRed hGen hTh E H D _ J a w w' bas hpq hbas haw haw' hcl n hnp hno
  obtain ⟨k, j₂, hj₂⟩ := GlobalTheory.T.nonempty_ampleFramedModel_PELThetaFamily hL hL2 hSR hTU hUT hZG E H D n hpq hnp hno
  obtain ⟨j₃, hj₃⟩ := GlobalTheory.T.exists_universal_quasiProjective_siegelFamily_large_level hL hL2 hGen hTh _ n hg1 hnp hno
  obtain ⟨j, hj1, hj2, hj3, hj⟩ : ∃ j, j₁ ≤ j ∧ j₂ ≤ j ∧ j₃ ≤ j ∧ 1 ≤ j :=
    ⟨max (max j₁ j₂) (max j₃ 1), by omega, by omega, by omega, by omega⟩
  have hNe : (n ^ j) ^ 2 = n ^ (j * 2) := (pow_mul n j 2).symm
  obtain ⟨b, hb⟩ := exists_tBase_RZ H hn0 hNe
  have hAr := arBase_RZ H hn0 hNe
  obtain ⟨F, τ, hPEL, hsm⟩ := hj₁ j hj1 (RZ H n ((n ^ j) ^ 2)) b (RZ H n ((n ^ j) ^ 2)).subtype
    (RZ.rt H n ((n ^ j) ^ 2)) (RZ.coe_rt H n _) hAr
  obtain ⟨C⟩ := hj₂ j hj2 (n ^ j) rfl _ J a bas b F τ hbas hcl ⟨w, w', haw, haw'⟩ hb hPEL hsm
  obtain ⟨lev, hcore⟩ := GlobalTheory.T.exists_universal_fullLevel_of_pelThetaFamily hL hL2 E H D n (n ^ j) _ J a bas b F τ hbas hcl
    ⟨w, w', haw, haw'⟩ hb hPEL hsm hpq hnp hno ⟨j, hj, rfl⟩
  have hcl2 := GlobalTheory.T.cmFamily_finite_unramified_over_siegelFamily hHE hL hL2 E H D n ((n ^ j) ^ 2) F.MM F.s τ lev hpq hnp hno
    ⟨j * 2, by omega, hNe⟩ hcore (hj₃ j hj3)
  obtain ⟨T, hT⟩ := GlobalTheory.T.exists_fullLevel_model_of_family_birationalModel hHE hL hL2 E H D Xo n ((n ^ j) ^ 2) F.MM F.s τ lev (n ^ k) C hpq hn
    ⟨j * 2, by omega, hNe⟩ (pow_pos hn0 k) hcore hcl2
  refine ⟨j * 2, k, ?_⟩
  rw [← hNe]
  exact ⟨T, by omega, hT⟩

end GlobalTheory.Models
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFullLevelModelAmpleFramesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fullLevel_model_ample_frames : GlobalTheory.LN.HomExtSt → Out.Laws → Out.Laws2 → GlobalTheory.Published.SemistableReductionSt → GlobalTheory.ZH.ThmUSt → GlobalTheory.ZH.UTorsSt → GlobalTheory.ZH.ZHGeoSt → (∀ (g n : ℕ) (J : Type) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Finite (IsLocalRing.ResidueField V)] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (β : o →+* V) (t : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V K) ≫ spMap β)) (v : Ix g ((n ^ j) ^ 2) → V), t.Prim w w' → t.HasTh (𝟙 _) (fun a => algebraMap V K (v a)) → Coset n (n ^ j) v (IsLocalRing.maximalIdeal V) → ∃ (V' K' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : Field K') (_ : Algebra V' K') (_ : IsFractionRing V' K') (φ : V →+* V') (ψ : K →+* K') (t' : TObj g ((n ^ j) ^ 2) J b (spMap φ ≫ spMap β)) (tK : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V' K') ≫ spMap φ ≫ spMap β)), IsLocalHom φ ∧ ψ.comp (algebraMap V K) = (algebraMap V' K').comp φ ∧ TMap tK t (spMap ψ) ∧ TMap tK t' (spMap (algebraMap V' K')) ∧ t'.HasTh (𝟙 _) (fun a => φ (v a))) → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → TopAmpExists := by
  first | exact @GlobalTheory.Models.topAmpExists | exact GlobalTheory.Models.topAmpExists | (intros; apply GlobalTheory.Models.topAmpExists <;> assumption)
end
