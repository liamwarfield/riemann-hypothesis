module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.BiadditiveOfTrivAxes
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbIsoGenericSpreadsOut
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TautologicalModel
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjProperRelAmpleOfProjectiveCoordinateRep
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SegreCoordinates

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FullLevelObjectPullbackExistsAndFull
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FullLevelObjectPullbackExistsAndFull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

theorem GlobalTheory.fullObj_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n N : ℕ) (S S' : Scheme.{0}) (s : S ⟶ Sp (RZ H n N)) (t : SAB H S) (lev : D.La → (𝟙_ (Over S) ⟶ t.G)) (f : S' ⟶ S), (∃ (t' : SAB H S') (ν : SABMap t' t f) (lv : D.La → (𝟙_ (Over S') ⟶ t'.G)), ∀ a, (lv a).left ≫ ν.φ = f ≫ (lev a).left) ∧ ∀ (t' : SAB H S') (ν : SABMap t' t f) (lv : D.La → (𝟙_ (Over S') ⟶ t'.G)), (∀ a, (lv a).left ≫ ν.φ = f ≫ (lev a).left) → FullObj D s t lev → FullObj D (f ≫ s) t' lv := by
  intro E _ _ _ H D n N S S' s t lev f
  refine ⟨?_, fun t' m lv hlv o => ?_⟩
  · obtain ⟨t', ⟨m⟩⟩ : ∃ t' : SAB H S', Nonempty (SABMap t' t f) := by
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
    exact ⟨t', m, fun a => GlobalTheory.ObjPull.secPull m.cart (lev a), fun a => GlobalTheory.ObjPull.secPull_left m.cart _⟩
  have hlv' : ∀ a, lv a = GlobalTheory.ObjPull.secPull m.cart (lev a) := fun a => by
    apply Over.OverMorphism.ext
    apply m.cart.1.hom_ext
    · exact (hlv a).trans (GlobalTheory.ObjPull.secPull_left m.cart _).symm
    · rw [Over.w, Over.w]
  have hL : LBIso t'.PP.L (t.PP.L.pull m.cm.F) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  have hpr := o.proper
  obtain ⟨-, hamp, hk⟩ := GlobalTheory.PolPull.pol_pull_of_relAmple_local GlobalTheory.AmpleLocal.relAmple_of_locally
    S S' t.G t'.G f m.cm.F t.PP.L t'.PP.L t.PP.isLB t'.PP.isLB
    (AbelianSchemeGerms.isAbelianScheme_of_proper t.G t.semi) m.cart hL
  refine
    { proper := MorphismProperty.of_isPullback (P := @IsProper) m.cart.1 hpr
      ample := hamp o.ample
      ktriv := hk o.ktriv
      add := fun a c => by rw [hlv', hlv', hlv', o.add, map_mul]
      ker := fun a => by rw [hlv', o.ker a, map_one]
      geom := fun k _ _ _ x β hx => ?_ }
  obtain ⟨hdet, I, hI, hA⟩ := o.geom k (x ≫ f) β (by rw [Category.assoc, hx])
  refine ⟨fun τ => ?_, GlobalTheory.ObjPull.tateMove (GlobalTheory.ObjPull.pushEquiv m.cart (Over.mk x)) (fun c g => ?_)
    (fun n g g' c hc => ?_) I, hI, fun a => ?_⟩
  · rw [GlobalTheory.LiePull.lieMult_pull _ S S' t.G t'.G f m.cm.F t.act t'.act m.cart m.act k x τ,
      GlobalTheory.LiePull.lieMult_pull _ S S' t.G t'.G f m.cm.F t.act t'.act m.cart m.act k x τ]
    exact hdet τ
  · apply Over.OverMorphism.ext
    show (g.left ≫ _) ≫ _ = (g.left ≫ _) ≫ _
    rw [Category.assoc, m.act, Category.assoc]
  · exact (GlobalTheory.weilIs_grpPullback_of_comm S S' t.G t'.G f m.cm.F t.PP.L t'.PP.L t.PP.isLB t'.PP.isLB m.cart hL
      (Over.mk x) n g g' _ _ _ rfl rfl).2 hc
  · rw [hlv']
    exact (MulEquiv.eq_symm_apply _).2 ((GlobalTheory.ObjPull.pushEquiv_secPull m.cart _ _).trans (hA a))
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FullLevelObjectPullbackExistsAndFullStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fullLevelObject_pullback_exists_and_full : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n N : ℕ) (S S' : Scheme.{0}) (s : S ⟶ Sp (RZ H n N)) (t : SAB H S) (lev : D.La → (𝟙_ (Over S) ⟶ t.G)) (f : S' ⟶ S), (∃ (t' : SAB H S') (ν : SABMap t' t f) (lv : D.La → (𝟙_ (Over S') ⟶ t'.G)), ∀ a, (lv a).left ≫ ν.φ = f ≫ (lev a).left) ∧ ∀ (t' : SAB H S') (ν : SABMap t' t f) (lv : D.La → (𝟙_ (Over S') ⟶ t'.G)), (∀ a, (lv a).left ≫ ν.φ = f ≫ (lev a).left) → FullObj D s t lev → FullObj D (f ≫ s) t' lv := by
  first | exact @GlobalTheory.fullObj_pull | exact GlobalTheory.fullObj_pull | (intros; apply GlobalTheory.fullObj_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianLocusIsOpenOfOpenImmersionCover
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianLocusIsOpenOfOpenImmersionCover
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum

namespace GlobalTheory.AbLocusLocal

private theorem isProper_of_isPullback_of_pullback_snd {A B C D : Scheme.{0}} {fst : A ⟶ B} {snd : A ⟶ C} {f : B ⟶ D}
    {g : C ⟶ D} (h : IsPullback fst snd f g) (H : IsProper (pullback.snd f g)) : IsProper snd := by
  rw [← h.isoPullback_hom_snd]
  exact (MorphismProperty.cancel_left_of_respectsIso @IsProper h.isoPullback.hom (pullback.snd f g)).2 H

private theorem isProper_pullback_snd_of_isPullback {A B C D : Scheme.{0}} {fst : A ⟶ B} {snd : A ⟶ C} {f : B ⟶ D}
    {g : C ⟶ D} (h : IsPullback fst snd f g) (H : IsProper snd) : IsProper (pullback.snd f g) := by
  rw [← h.isoPullback_inv_snd]
  exact (MorphismProperty.cancel_left_of_respectsIso @IsProper h.isoPullback.inv snd).2 H

private theorem isProper_snd_of_isPullback_of_isProper {A B C D : Scheme.{0}} {fst : A ⟶ B} {snd : A ⟶ C} {f : B ⟶ D}
    {g : C ⟶ D} (h : IsPullback fst snd f g) (hf : IsProper f) : IsProper snd :=
  isProper_of_isPullback_of_pullback_snd h inferInstance

theorem isProper_restrict_of_cover {X Z : Scheme.{0}} (p : X ⟶ Z) {I : Type} {Y X' : I → Scheme.{0}}
    (f : ∀ i, Y i ⟶ Z) [∀ i, IsOpenImmersion (f i)] (p' : ∀ i, X' i ⟶ Y i) (F : ∀ i, X' i ⟶ X)
    (h : ∀ i, IsPullback (F i) (p' i) p (f i)) (V : ∀ i, (Y i).Opens) (hV : ∀ i, IsProper (p' i ∣_ V i))
    (U : Z.Opens) (hle : ∀ i, Set.range ((V i).ι ≫ f i) ⊆ Set.range U.ι)
    (hc : ∀ z ∈ U, ∃ i, z ∈ Set.range ((V i).ι ≫ f i)) : IsProper (p ∣_ U) := by
  have hsq : ∀ i, IsPullback (((p' i) ⁻¹ᵁ V i).ι ≫ F i) (p' i ∣_ V i) p ((V i).ι ≫ f i) := fun i =>
    (isPullback_morphismRestrict (p' i) (V i)).flip.paste_horiz (h i)
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (fun i => U.ι ⁻¹ᵁ ((V i).ι ≫ f i).opensRange) ?_ ?_
  · rw [eq_top_iff]
    intro x _
    rw [TopologicalSpace.Opens.mem_iSup]
    obtain ⟨i, hi⟩ := hc (U.ι x) x.2
    exact ⟨i, by simpa [Scheme.Hom.coe_opensRange] using hi⟩
  · intro i
    let W : U.toScheme.Opens := U.ι ⁻¹ᵁ ((V i).ι ≫ f i).opensRange
    have hr : Set.range (W.ι ≫ U.ι) ⊆ Set.range ((V i).ι ≫ f i) := by
      rintro _ ⟨x, rfl⟩
      have hx : U.ι x.val ∈ ((V i).ι ≫ f i).opensRange := x.2
      rw [← SetLike.mem_coe, Scheme.Hom.coe_opensRange] at hx
      exact hx
    let e := IsOpenImmersion.lift ((V i).ι ≫ f i) (W.ι ≫ U.ι) hr
    have he : e ≫ ((V i).ι ≫ f i) = W.ι ≫ U.ι := IsOpenImmersion.lift_fac _ _ _
    have big := (isPullback_morphismRestrict (p ∣_ U) W).flip.paste_horiz (isPullback_morphismRestrict p U).flip
    rw [← he] at big
    have hw : ((((p ∣_ U) ⁻¹ᵁ W).ι ≫ (p ⁻¹ᵁ U).ι)) ≫ p = ((p ∣_ U) ∣_ W ≫ e) ≫ ((V i).ι ≫ f i) := by
      rw [big.w, Category.assoc]
    have sq : IsPullback ((hsq i).lift _ _ hw) ((p ∣_ U) ∣_ W) (p' i ∣_ V i) e := by
      refine IsPullback.of_right ?_ ((hsq i).lift_snd _ _ hw) (hsq i)
      rw [(hsq i).lift_fst]
      exact big
    exact isProper_snd_of_isPullback_of_isProper sq (hV i)

private theorem mem_abLocus_of_map_mem_of_isPullback {Y Z : Scheme.{0}} {A : Over Y} {B : Over Z} {g : Y ⟶ Z}
    {φ : A.left ⟶ B.left} (h : IsPullback φ A.hom B.hom g) (y : Y) (hy : g y ∈ abLocus B) :
    y ∈ abLocus A := by
  simp only [abLocus, Set.mem_setOf_eq] at hy ⊢
  intro K _ _ s hs
  obtain ⟨x, rfl⟩ := hs
  have big := (IsPullback.of_hasPullback A.hom s).paste_horiz h
  exact isProper_of_isPullback_of_pullback_snd big (hy K (s ≫ g) ⟨x, by rw [Scheme.Hom.comp_apply]⟩)

private theorem map_mem_abLocus_of_isPullback {Y Z : Scheme.{0}} {A : Over Y} {B : Over Z} {g : Y ⟶ Z}
    [IsOpenImmersion g] {φ : A.left ⟶ B.left} (h : IsPullback φ A.hom B.hom g) (y : Y)
    (hy : y ∈ abLocus A) : g y ∈ abLocus B := by
  simp only [abLocus, Set.mem_setOf_eq] at hy ⊢
  intro K _ _ s hs
  obtain ⟨x0, hx0⟩ := hs
  have hr : Set.range s ⊆ Set.range g := by
    rintro _ ⟨x, rfl⟩
    rw [Subsingleton.elim x x0, hx0]
    exact ⟨y, rfl⟩
  have hs' : IsOpenImmersion.lift g s hr ≫ g = s := IsOpenImmersion.lift_fac g s hr
  have big := (IsPullback.of_hasPullback A.hom (IsOpenImmersion.lift g s hr)).paste_horiz h
  rw [hs'] at big
  have hy' : y ∈ Set.range (IsOpenImmersion.lift g s hr) := by
    refine ⟨x0, g.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hs', hx0]
  exact isProper_pullback_snd_of_isPullback big (hy K _ hy')

theorem abOpen_of_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Z : Scheme.{0}) (t : SAB H Z) (I : Type) (Y : I → Scheme.{0}) (f : ∀ i, Y i ⟶ Z) (u : ∀ i, SAB H (Y i)) (_ : ∀ i, SABMap (u i) t (f i)), (∀ i, IsOpenImmersion (f i)) → (∀ z : Z, ∃ i, z ∈ Set.range (f i)) → (∀ i, AbOpen (u i).G) → AbOpen t.G := by
  intro E _ _ _ H Z t I Y f u m hf hc hab
  unfold AbOpen at hab ⊢
  choose V hVs hVp using hab
  have hpb : ∀ i, IsPullback (m i).φ (u i).G.hom t.G.hom (f i) := fun i => (m i).cart.1
  refine ⟨⨆ i, ((V i).ι ≫ f i).opensRange, ?_, ?_⟩
  · ext z
    simp only [TopologicalSpace.Opens.coe_iSup, Set.mem_iUnion, Scheme.Hom.coe_opensRange]
    constructor
    · rintro ⟨i, v, rfl⟩
      rw [Scheme.Hom.comp_apply]
      exact map_mem_abLocus_of_isPullback (hpb i) _ (by rw [← hVs i]; exact v.2)
    · intro hz
      obtain ⟨i, y, rfl⟩ := hc z
      have hy := mem_abLocus_of_map_mem_of_isPullback (hpb i) y hz
      rw [← hVs i] at hy
      exact ⟨i, ⟨y, hy⟩, rfl⟩
  · refine isProper_restrict_of_cover t.G.hom f (fun i => (u i).G.hom) _ hpb V hVp _ ?_ ?_
    · intro i z hz
      rw [Scheme.Opens.range_ι]
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, by rw [← SetLike.mem_coe, Scheme.Hom.coe_opensRange]; exact hz⟩
    · intro z hz
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
      rw [← SetLike.mem_coe, Scheme.Hom.coe_opensRange] at hi
      exact ⟨i, hi⟩

end GlobalTheory.AbLocusLocal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianLocusIsOpenOfOpenImmersionCoverStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianLocus_isOpen_of_openImmersion_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Z : Scheme.{0}) (t : SAB H Z) (I : Type) (Y : I → Scheme.{0}) (f : ∀ i, Y i ⟶ Z) (u : ∀ i, SAB H (Y i)) (_ : ∀ i, SABMap (u i) t (f i)), (∀ i, IsOpenImmersion (f i)) → (∀ z : Z, ∃ i, z ∈ Set.range (f i)) → (∀ i, AbOpen (u i).G) → AbOpen t.G := by
  first | exact @GlobalTheory.AbLocusLocal.abOpen_of_cover | exact GlobalTheory.AbLocusLocal.abOpen_of_cover | (intros; apply GlobalTheory.AbLocusLocal.abOpen_of_cover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeRingKrullDimThetaFamilyGenericFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeRingKrullDimThetaFamilyGenericFibre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.GenericDim

open GlobalTheory.CoordChart

theorem exists_secCoord_field {X : Scheme.{0}} {M : LB X} (hM : M.IsLB) {σ : Type} (th : σ → M.Sec)
    {K : Type} [Field K] (x : Sp K ⟶ X) : ∃ v, SecCoord M th x v := by
  let p₀ : Sp K := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K)
  have h : x p₀ ∈ ⨆ i, M.U i := by rw [hM.cover]; trivial
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 h
  refine GlobalTheory.SegreCoord.exists_secCoord hM (k := k) fun y => ?_
  have : y = p₀ := Subsingleton.elim (α := PrimeSpectrum K) _ _
  rw [this]; exact hk

theorem exists_common_field {R L : Type} [CommRing R] [CommRing L] [IsDomain L] (q : Ideal R) [q.IsPrime]
    (φ : R →+* L) (h : RingHom.ker φ = q) :
    ∃ (K : Type) (_ : Field K) (lam : L →+* K) (j : FractionRing (R ⧸ q) →+* K), Function.Injective lam ∧
      j.comp ((algebraMap (R ⧸ q) _).comp (Ideal.Quotient.mk q)) = lam.comp φ := by
  have hl := IsFractionRing.injective L (FractionRing L)
  have hχ : Function.Injective ((algebraMap L (FractionRing L)).comp (Ideal.Quotient.lift q φ fun a ha => h.ge ha)) :=
    hl.comp ((Ideal.injective_lift_iff fun a ha => h.ge ha).2 h)
  refine ⟨FractionRing L, inferInstance, algebraMap L (FractionRing L),
    IsFractionRing.lift (A := R ⧸ q) (K := FractionRing (R ⧸ q)) hχ, hl, ?_⟩
  refine RingHom.ext fun r => ?_
  rw [RingHom.comp_apply, RingHom.comp_apply, IsFractionRing.lift_algebraMap hχ, RingHom.comp_apply,
    RingHom.comp_apply]
  exact congrArg _ (Ideal.Quotient.lift_mk q φ _)

theorem exists_extension {o : Type} [CommRing o] {g n N' : ℕ} {I : Ideal (MvPolynomial (Ix g (N' ^ 2)) o)}
    (Y : MMPre n N' I) {R : Type} [CommRing R] (β : o →+* R) (x : Sp R ⟶ Y.MM) [IsOpenImmersion x]
    (hx : x ≫ Y.s = spMap β) (q : Ideal R) [q.IsPrime] (hmin : q ∈ minimalPrimes R)
    (y : R →+* FractionRing (R ⧸ q)) (hy : y = (algebraMap (R ⧸ q) _).comp (Ideal.Quotient.mk q))
    (v : Ix g (N' ^ 2) → FractionRing (R ⧸ q)) (hv : SecCoord Y.de Y.th (spMap y ≫ x) v)
    (P : Ideal (MvPolynomial (Ix g (N' ^ 2)) o)) (hP : P.IsPrime) (hI : I ≤ P)
    (hle : P ≤ RingHom.ker (MvPolynomial.eval₂Hom (y.comp β) v)) :
    ∃ (K : Type) (_ : Field K) (j : FractionRing (R ⧸ q) →+* K) (u : Kˣ),
      RingHom.ker (MvPolynomial.eval₂Hom (j.comp (y.comp β)) (fun a => u * j (v a))) = P := by
  have h3 : (spMap y ≫ x) ≫ Y.s = spMap (y.comp β) := by rw [Category.assoc, hx, sp_comp]
  have hK := Y.loc _ _ _ _ h3 hv
  set ev := MvPolynomial.eval₂Hom (y.comp β) v with hev
  let e : (MvPolynomial (Ix g (N' ^ 2)) o ⧸ P) →+* FractionRing (R ⧸ q) :=
    Ideal.Quotient.lift P ev fun a ha => hle ha
  haveI : (RingHom.ker e).IsPrime := RingHom.ker_isPrime e
  let L := Localization.AtPrime (RingHom.ker e)
  have hu : ∀ s : (RingHom.ker e).primeCompl, IsUnit (e s) := fun s => IsUnit.mk0 _ s.2
  let ψ : L →+* FractionRing (R ⧸ q) := IsLocalization.lift (M := (RingHom.ker e).primeCompl) hu
  let π : MvPolynomial (Ix g (N' ^ 2)) o →+* L := (algebraMap _ L).comp (Ideal.Quotient.mk P)
  have hπ : ∀ F, ψ (π F) = ev F := fun F => by
    simp only [ψ, π, RingHom.comp_apply, IsLocalization.lift_eq]
    rfl
  have hπe : ∀ F, MvPolynomial.eval₂ (π.comp MvPolynomial.C) (fun a => π (MvPolynomial.X a)) F = π F := fun F => by
    conv_rhs => rw [← MvPolynomial.eval₂_eta F, MvPolynomial.eval₂_comp_left]
    rfl
  have hπ0 : ∀ F, π F = 0 ↔ F ∈ P := fun F => by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact map_eq_zero_iff _ (IsLocalization.injective L (RingHom.ker e).primeCompl_le_nonZeroDivisors)
  have hψ : ∀ l, ψ l ≠ 0 → IsUnit l := by
    intro l hl
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (RingHom.ker e).primeCompl l
    rw [IsLocalization.AtPrime.isUnit_mk'_iff L (RingHom.ker e)]
    intro ha
    apply hl
    change ψ (IsLocalization.mk' L a s) = 0
    rw [IsLocalization.lift_mk'_spec, mul_zero]
    exact ha
  have hw : ∀ a, ψ (π (MvPolynomial.X a)) = v a := fun a => by rw [hπ]; simp [hev]
  have hβ : ψ.comp (π.comp MvPolynomial.C) = y.comp β := by ext t; simp [hπ, hev]
  have hL : InMM n N' I (π.comp MvPolynomial.C) (fun a => π (MvPolynomial.X a)) := by
    refine ⟨fun F hF => by rw [hπe, hπ0]; exact hI hF, fun r hr a => ?_⟩
    obtain ⟨c, hc⟩ := hK.2 ⊥ Ideal.isPrime_bot a
    refine ⟨c, fun hm => hr.ne_top (Ideal.eq_top_of_isUnit_mem _ hm (hψ _ ?_))⟩
    rw [hw]
    simpa using hc
  obtain ⟨z, ⟨hz1, hz2⟩, -⟩ := Y.pts L _ _ hL
  have h4 := (Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ Y.isLB hz2).1 _ ψ
  have h5 : (spMap ψ ≫ z) ≫ Y.s = spMap (y.comp β) := by rw [Category.assoc, hz1, sp_comp, hβ]
  have heq : spMap ψ ≫ z = spMap y ≫ x := by
    refine (Y.pts _ _ _ hK).unique ⟨h5, ?_⟩ ⟨h3, hv⟩
    simpa only [hw] using h4
  have hr : Set.range z ⊆ Set.range x := by
    rintro _ ⟨p, rfl⟩
    let p₀ : Sp (FractionRing (R ⧸ q)) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing (R ⧸ q)))
    have hs : p ⤳ spMap ψ p₀ := by
      refine (PrimeSpectrum.le_iff_specializes (R := L) p (spMap ψ p₀)).1 ?_
      intro l hl
      change ψ l ∈ (⊥ : Ideal _)
      by_contra hne
      exact p.2.ne_top (Ideal.eq_top_of_isUnit_mem _ hl (hψ _ (by simpa using hne)))
    refine (hs.map z.continuous).mem_open x.isOpenEmbedding.isOpen_range ⟨spMap y p₀, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, heq]
  obtain ⟨φ, hφ⟩ := sp_surj (IsOpenImmersion.lift x z hr)
  have hz : spMap φ ≫ x = z := by rw [hφ, IsOpenImmersion.lift_fac]
  have hφy : ψ.comp φ = y := sp_inj (by rw [← cancel_mono x, ← sp_comp, Category.assoc, hz, heq])
  have hφβ : φ.comp β = π.comp MvPolynomial.C := sp_inj (by rw [← sp_comp, ← hx, ← Category.assoc, hz, hz1])
  have hy0 : ∀ r, y r = 0 ↔ r ∈ q := fun r => by
    rw [hy, RingHom.comp_apply, map_eq_zero_iff _ (IsFractionRing.injective (R ⧸ q) _),
      Ideal.Quotient.eq_zero_iff_mem]
  have hk1 : RingHom.ker φ ≤ q := fun r hr => by
    rw [RingHom.mem_ker] at hr
    rw [← hy0, ← hφy, RingHom.comp_apply, hr, map_zero]
  have hk2 : q ≤ RingHom.ker φ := hmin.2 ⟨RingHom.ker_isPrime φ, bot_le⟩ hk1
  haveI : IsDomain L := IsLocalization.isDomain_localization (RingHom.ker e).primeCompl_le_nonZeroDivisors
  obtain ⟨K, _, lam, j, hl, hj⟩ := exists_common_field q φ (le_antisymm hk1 hk2)
  rw [← hy] at hj
  have h6 := (Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ Y.isLB hv).1 _ j
  have h7 := (Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ Y.isLB hz2).1 _ lam
  rw [← Category.assoc, sp_comp, hj, ← sp_comp, Category.assoc, hz] at h6
  obtain ⟨u, hu'⟩ := (Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ Y.isLB h6).2.2 _ h7
  refine ⟨K, inferInstance, j, u, ?_⟩
  ext F
  rw [RingHom.mem_ker, ← hπ0, ← map_eq_zero_iff lam hl, ← hπe, MvPolynomial.eval₂_comp_left, ← RingHom.comp_assoc, hj,
    RingHom.comp_assoc, hφβ, MvPolynomial.coe_eval₂Hom, ← funext hu']
  rfl

theorem le_ringKrullDim_of_independent {o : Type} [CommRing o] [IsDomain o] {R : Type} [CommRing R] [Algebra o R]
    [Algebra.FiniteType o R] {d : ℕ}
    (h : ∀ (q : Ideal R) [q.IsPrime], q ∈ minimalPrimes R → ∃ y : Fin d → FractionRing (R ⧸ q), AlgebraicIndependent o y)
    (q : Ideal (FractionRing o ⊗[o] R)) (hq : q ∈ minimalPrimes (FractionRing o ⊗[o] R)) :
    (d : WithBot ℕ∞) ≤ ringKrullDim ((FractionRing o ⊗[o] R) ⧸ q) := by
  have hqp : q.IsPrime := hq.1.1
  let f : R →ₐ[o] FractionRing o ⊗[o] R := Algebra.TensorProduct.includeRight
  have hmin : q.comap f ∈ minimalPrimes R := by
    letI : Algebra R (FractionRing o ⊗[o] R) := Algebra.TensorProduct.rightAlgebra
    have h1 := IsLocalization.minimalPrimes_map (Algebra.algebraMapSubmonoid R (nonZeroDivisors o))
      (FractionRing o ⊗[o] R) ⊥
    rw [Ideal.map_bot] at h1
    have h2 : q ∈ (⊥ : Ideal (FractionRing o ⊗[o] R)).minimalPrimes := hq
    rw [h1] at h2
    exact h2
  obtain ⟨y, hy⟩ := h (q.comap f) hmin
  let B := (FractionRing o ⊗[o] R) ⧸ q
  let f' : (R ⧸ q.comap f) →ₐ[o] FractionRing B :=
    (IsScalarTower.toAlgHom o B (FractionRing B)).comp (Ideal.quotientMapₐ q f le_rfl)
  have hf' : Function.Injective f' :=
    (IsFractionRing.injective B (FractionRing B)).comp (Ideal.quotientMap_injective' (f := f.toRingHom) (H := le_rfl) le_rfl)
  let j : FractionRing (R ⧸ q.comap f) →ₐ[o] FractionRing B := IsFractionRing.liftAlgHom hf'
  have h1 : AlgebraicIndependent o (j ∘ y) := hy.map' j.toRingHom.injective
  have : Algebra.IsAlgebraic o (FractionRing o) := IsLocalization.isAlgebraic _ (nonZeroDivisors o)
  have h2 := (h1.extendScalars (FractionRing o)).cardinalMk_le_trdeg
  have : Algebra.IsAlgebraic B (FractionRing B) := IsLocalization.isAlgebraic _ (nonZeroDivisors B)
  obtain ⟨s, hs1, hs2⟩ := GlobalTheory.exists_ringKrullDim_eq_and_trdeg_eq (FractionRing o) B
  have : FaithfulSMul (FractionRing o) B :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap (FractionRing o) B).injective
  rw [GlobalTheory.trdeg_eq_of_isAlgebraic_top (FractionRing o) B (FractionRing B), hs2] at h2
  have h3 : d ≤ s := by simpa using h2
  rw [hs1]
  exact_mod_cast h3

theorem le_ringKrullDim_genericFibre : Out.Laws → Out.Laws2 → ∀ (g n N' : ℕ) (J : Type) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) (w w' : J) (o : Type) [CommRing o] (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (C : TObj g (N' ^ 2) J b (spMap em) → Prop) (d : ℕ) (F : WFam n em C Mat κ), 3 ≤ N' → Odd N' → ArBase em → GoodClass em C Mat κ w w' d → ∀ (R : Type) [CommRing R] [Algebra o R] (x : Sp R ⟶ F.U.toScheme), IsOpenImmersion x → x ≫ F.U.ι ≫ F.Y.s = spMap (algebraMap o R) → ∀ q ∈ minimalPrimes (FractionRing o ⊗[o] R), (d : WithBot ℕ∞) ≤ ringKrullDim ((FractionRing o ⊗[o] R) ⧸ q) := by
  intro h1 h2 g n N' J Mat κ w w' o _ b em C d F hN _ hb hC R _ _ x hox hx
  have : IsDedekindDomain o := hb.1
  have hx' : (x ≫ F.U.ι) ≫ F.Y.s = spMap (algebraMap o R) := by rw [Category.assoc, hx]
  have : Algebra.FiniteType o R := by
    obtain ⟨N, i, hi, -, hs⟩ := F.Y.qproj
    have := isProper_str o N
    have h : LocallyOfFiniteType (spMap (algebraMap o R)) := by
      rw [← hx', ← hs]; infer_instance
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at h
    exact RingHom.finiteType_algebraMap.mp h
  refine le_ringKrullDim_of_independent fun q _ hq => ?_
  let y : R →+* FractionRing (R ⧸ q) := (algebraMap (R ⧸ q) _).comp (Ideal.Quotient.mk q)
  have hy : y.comp (algebraMap o R) = algebraMap o _ := by
    rw [IsScalarTower.algebraMap_eq o (R ⧸ q) (FractionRing (R ⧸ q))]; rfl
  obtain ⟨v, hv⟩ := exists_secCoord_field F.Y.isLB F.Y.th (spMap y ≫ x ≫ F.U.ι)
  have hK := F.Y.loc _ (y.comp (algebraMap o R)) _ _ (by rw [Category.assoc, hx', sp_comp]) hv
  obtain ⟨c, hc⟩ := hK.2 ⊥ Ideal.isPrime_bot 0
  obtain ⟨P, a₀, a, hP, hI, hle, -, hind⟩ := GlobalTheory.T.theta_ideal_prime_avoiding_variable h1 h2 g N' J Mat κ w w' o b em C d hb hC
    (RingHom.ker (MvPolynomial.eval₂Hom (y.comp (algebraMap o R)) v)) _ (by omega) (RingHom.ker_isPrime _)
    (fun G hG => hK.1 G hG) (by rw [RingHom.mem_ker, MvPolynomial.eval₂Hom_X']; simpa using hc)
  obtain ⟨K, _, j, u, hker⟩ := exists_extension F.Y _ (x ≫ F.U.ι) hx' q hq y rfl v hv P hP hI hle
  refine ⟨fun i => v (a i) / v a₀, algebraicIndependent_iff.2 fun G hG => hind K _ _ hker G ?_⟩
  have := congrArg j hG
  rw [map_zero, MvPolynomial.aeval_def, MvPolynomial.eval₂_comp_left, ← hy] at this
  convert this using 2
  ext i
  simp [mul_div_mul_left]

end GlobalTheory.ZM.GenericDim
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeRingKrullDimThetaFamilyGenericFibreStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.le_ringKrullDim_thetaFamily_genericFibre : Out.Laws → Out.Laws2 → ∀ (g n N' : ℕ) (J : Type) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) (w w' : J) (o : Type) [CommRing o] (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (C : TObj g (N' ^ 2) J b (spMap em) → Prop) (d : ℕ) (F : WFam n em C Mat κ), 3 ≤ N' → Odd N' → ArBase em → GoodClass em C Mat κ w w' d → ∀ (R : Type) [CommRing R] [Algebra o R] (x : Sp R ⟶ F.U.toScheme), IsOpenImmersion x → x ≫ F.U.ι ≫ F.Y.s = spMap (algebraMap o R) → ∀ q ∈ minimalPrimes (FractionRing o ⊗[o] R), (d : WithBot ℕ∞) ≤ ringKrullDim ((FractionRing o ⊗[o] R) ⧸ q) := by
  first | exact @GlobalTheory.ZM.GenericDim.le_ringKrullDim_genericFibre | exact GlobalTheory.ZM.GenericDim.le_ringKrullDim_genericFibre | (intros; apply GlobalTheory.ZM.GenericDim.le_ringKrullDim_genericFibre <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PulledSectionsFormBasisIdOfPulledSectionsFormBas
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PulledSectionsFormBasisIdOfPulledSectionsFormBas
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum

namespace GlobalTheory.ModelSum

theorem exists_pull_LPow_sec {Z : Scheme.{0}} (G : Over Z) (L : LB G.left) (hL : L.IsLB) (N : ℕ) {T T' : Over Z}
    (h : T' ⟶ T) (b : LB.Sec (Out.LPow G L (N : ℤ) T)) :
    ∃ b' : LB.Sec (Out.LPow G L (N : ℤ) T'), ∀ (Y : Scheme.{0}) (r : Y ⟶ (T' ⊗ G).left) (z : Y) (J), Good L z J →
      sval (L := L) (φ := fun _ : Fin 1 => (snd T' G).left) (ε := fun _ => (N : ℤ)) b' r z J =
        sval (L := L) (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => (N : ℤ)) b (r ≫ (h ▷ G).left) z J := by
  have hu : (LB.oneGen L (Y := (T' ⊗ G).left)).IsGen := by
    intro (i : PEmpty → L.ι) (j : PEmpty → L.ι)
    simp [LB.oneGen, LB.LinComb, res]
    ext
    erw [Units.val_mul, Units.coe_map, Units.coe_map, Units.val_one, _root_.one_mul, map_one, map_one]
  have hf : FormEq (Sum.elim (fun _ : Fin 1 => (h ▷ G).left ≫ (snd T G).left)
      (PEmpty.elim : PEmpty → ((T' ⊗ G).left ⟶ G.left))) (Sum.elim (fun _ => (N : ℤ)) PEmpty.elim)
      (fun _ : Fin 1 => (snd T' G).left) (fun _ => (N : ℤ)) := by
    intro U _ f
    simp [Fintype.prod_sum_type]
  obtain ⟨b', hb'⟩ := exists_sec hL hf
    (pullMulSec (L := L) (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => (N : ℤ)) b (h ▷ G).left
      (LB.oneGen L (Y := (T' ⊗ G).left)) hu)
  refine ⟨b', fun Y r z J hJ => (hb' Y r z J hJ).trans ((sval_pullMulSec _ _ _ hu r z hJ).trans ?_)⟩
  rw [val_one, Units.val_one, _root_.mul_one]

theorem basisAlong_id_of_basisAlong : ∀ (Z : Scheme.{0}) (G : Over Z) (L : LB G.left) (N n : ℕ) (T T' : Over Z) (h : T' ⟶ T) (b : Fin n → LB.Sec (Out.LPow G L (N : ℤ) T)), L.IsLB → GlobalTheory.LN.BasisAlong G L N h b → ∃ b' : Fin n → LB.Sec (Out.LPow G L (N : ℤ) T'), GlobalTheory.LN.BasisAlong G L N (𝟙 T') b' := by
  intro Z G L N n T T' h b hL hB
  choose b' hb' using fun i => exists_pull_LPow_sec G L hL N h (b i)
  have key : ∀ s c, GlobalTheory.LN.Lin G L N (𝟙 T') b' c s ↔ GlobalTheory.LN.Lin G L N h b c s := by
    intro s c
    have e : ∀ i (z : (T' ⊗ G).left) J, Good L z J →
        sval (L := L) (φ := fun _ : Fin 1 => (snd T' G).left) (ε := fun _ => (N : ℤ)) (b' i) ((𝟙 T') ▷ G).left z J =
          sval (L := L) (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => (N : ℤ)) (b i) (h ▷ G).left z J := by
      intro i z J hJ
      rw [hb' i _ _ z J hJ]
      simp
    unfold GlobalTheory.LN.Lin
    refine forall_congr' fun z => forall_congr' fun J => imp_congr_right fun hJ => ?_
    simp only [e _ z J hJ]
  unfold GlobalTheory.LN.BasisAlong at hB ⊢
  refine ⟨b', fun s => ?_⟩
  obtain ⟨c, hc, hu⟩ := hB s
  exact ⟨c, (key s c).2 hc, fun c' hc' => hu c' ((key s c').1 hc')⟩

end GlobalTheory.ModelSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PulledSectionsFormBasisIdOfPulledSectionsFormBasStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pulledSectionsFormBasis_id_of_pulledSectionsFormBasis : ∀ (Z : Scheme.{0}) (G : Over Z) (L : LB G.left) (N n : ℕ) (T T' : Over Z) (h : T' ⟶ T) (b : Fin n → LB.Sec (Out.LPow G L (N : ℤ) T)), L.IsLB → GlobalTheory.LN.BasisAlong G L N h b → ∃ b' : Fin n → LB.Sec (Out.LPow G L (N : ℤ) T'), GlobalTheory.LN.BasisAlong G L N (𝟙 T') b' := by
  first | exact @GlobalTheory.ModelSum.basisAlong_id_of_basisAlong | exact GlobalTheory.ModelSum.basisAlong_id_of_basisAlong | (intros; apply GlobalTheory.ModelSum.basisAlong_id_of_basisAlong <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbIsoCubeGraphOfDenseFibres
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbIsoCubeGraphOfDenseFibres
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.PrimDense

theorem exists_gen_cube_eSec {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left} (hL : L.IsLB)
    (u : A ⟶ A) [IsMonHom u] : ∃ c : ((cubeLB A ![𝟙 A, u] L).pull (eSec A)).Gen, c.IsGen := by
  have e₁ : (1 : 𝟙_ (Over S) ⟶ A) = η[A] := by rw [Hom.one_def]; simp
  have key : ∀ I, η[A] ≫ psum A ![𝟙 A, u] I = η[A] := fun I => by
    refine (psum_hom (preHom (G := A) η[A]) _ I).trans ?_
    have : (fun i => preHom (G := A) η[A] (![𝟙 A, u] i)) = fun i => (1 : (A ⟶ A) →* (𝟙_ (Over S) ⟶ A)) (![𝟙 A, u] i) := by
      funext i
      fin_cases i
      · exact (Category.comp_id _).trans e₁.symm
      · exact (IsMonHom.one_hom u).trans e₁.symm
    rw [this, ← psum_hom]
    exact e₁
  obtain ⟨t, ht, -⟩ := exists_gen hL (φ' := fun _ : ULift.{0} (Finset (Fin 2)) => eSec A)
    (ε' := fun I => (-1) ^ (2 - I.down.card))
    (fun U _ k => (Fintype.prod_empty _).trans (by
      have : ∑ I : ULift.{0} (Finset (Fin 2)), (-1 : ℤ) ^ (2 - I.down.card) = 0 := by decide
      have e := congrArg Additive.toMul (map_sum (zmultiplesHom (Additive U) (Additive.ofMul (k (eSec A))))
        (fun I : ULift.{0} (Finset (Fin 2)) => (-1 : ℤ) ^ (2 - I.down.card)) Finset.univ)
      rw [this, map_zero, toMul_sum] at e
      exact e)) (LB.oneGen L (Y := (𝟙_ (Over S)).left))
    (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
  exact gen_chartPull (chartPullOut L _ _ (eSec A) _ fun I => congrArg (fun z => z.left) (key I.down).symm) t ht

end GlobalTheory.PrimDense

namespace GlobalTheory

theorem lbIso_cube_of_dense : Out.GlobalFnsSt → ∀ (S : Scheme.{0}) [IsReduced S] (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left) (u : A ⟶ A), IsAbelianScheme A → L.IsLB → Out.RelAmple A L → Out.Rigidified A L → IsMonHom u → Dense {p : S | ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ S) (G : Over (Sp K)) (_ : GrpObj G) (_ : IsCommMonObj G) (φ : G.left ⟶ A.left) (L' : LB G.left) (u' : G ⟶ G), p ∈ Set.range x ∧ IsGrpPullback G A x φ ∧ L'.IsLB ∧ LBIso L' (L.pull φ) ∧ u'.left ≫ φ = φ ≫ u.left ∧ LBIso L' (cubeLB G ![𝟙 G, u'] L')} → LBIso L (cubeLB A ![𝟙 A, u] L) := by
  intro hG S _ A _ _ L u hA hL hamp hrig hu hd
  have hM : (cubeLB A ![𝟙 A, u] L).IsLB := DVR.linComb_isLB _ hL _ _
  refine GlobalTheory.T.seesaw_reduced_base_abelianScheme_of_dense_fibres hG S A L hA hL hamp S A.left (𝟙 _) (𝟙 _) A.hom (LB.div (cubeLB A ![𝟙 A, u] L) L)
    (IsPullback.of_horiz_isIso ⟨by simp⟩) (LB.isLB_div hM hL) (hd.mono ?_) (eSec A) (Over.w η[A]) ?_
  · rintro p ⟨K, _, x, G, _, _, φ, L', u', hp, h, hL', H, hu', H'⟩
    refine ⟨K, inferInstance, x, G.left, φ, G.hom, hp, h.1, ?_⟩
    have i : LBIso (cubeLB G ![𝟙 G, u'] L') ((cubeLB A ![𝟙 A, u] L).pull φ) := by
      obtain ⟨w, hw⟩ := H
      refine LBIso.chartPull (chartPullId _) (chartPullOut L _ _ φ _ fun I => ?_) (iso_linComb ((isGen_iff w).1 hw) _ _)
      refine psum_push h _ _ (Over.homMk φ h.1.w) (fun i => ?_) I.down
      fin_cases i
      exacts [Over.OverMorphism.ext ((Category.id_comp _).trans (Category.comp_id _).symm), Over.OverMorphism.ext hu']
    have a' : (cubeLB G ![𝟙 G, u'] L').IsLB := DVR.linComb_isLB _ hL' _ _
    obtain ⟨w, hw⟩ := LBIso.trans (LB.isLB_pull hL φ) hL' (LB.isLB_pull hM φ) H.symm
      (LBIso.trans hL' a' (LB.isLB_pull hM φ) H' i)
    exact gen_chartPull (IsoDescent.chartPullDiv _ L _) w hw
  · obtain ⟨c, hc⟩ := hrig
    obtain ⟨c', hc'⟩ := PrimDense.exists_gen_cube_eSec hL u
    obtain ⟨w, hw⟩ := IsoDescent.lbIso_of_gens hL hM _ _ _ _ c hc c' hc'
    exact gen_chartPull (IsoDescent.chartPullDiv _ L _) w hw

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbIsoCubeGraphOfDenseFibresStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lbIso_cube_graph_of_dense_fibres : Out.GlobalFnsSt → ∀ (S : Scheme.{0}) [IsReduced S] (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left) (u : A ⟶ A), IsAbelianScheme A → L.IsLB → Out.RelAmple A L → Out.Rigidified A L → IsMonHom u → Dense {p : S | ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ S) (G : Over (Sp K)) (_ : GrpObj G) (_ : IsCommMonObj G) (φ : G.left ⟶ A.left) (L' : LB G.left) (u' : G ⟶ G), p ∈ Set.range x ∧ IsGrpPullback G A x φ ∧ L'.IsLB ∧ LBIso L' (L.pull φ) ∧ u'.left ≫ φ = φ ≫ u.left ∧ LBIso L' (cubeLB G ![𝟙 G, u'] L')} → LBIso L (cubeLB A ![𝟙 A, u] L) := by
  first | exact @GlobalTheory.lbIso_cube_of_dense | exact GlobalTheory.lbIso_cube_of_dense | (intros; apply GlobalTheory.lbIso_cube_of_dense <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ProjRepGraphSegreCoordinatesFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ProjRepGraphSegreCoordinatesFibre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.GraphSegre

theorem idealOf_eq_graphIdeal {K σ₁ σ₂ : Type} [CommRing K] {Y X₁ X₂ : Scheme.{0}} (s : Y ⟶ Sp K)
    (M₁ : LB X₁) (th₁ : σ₁ → M₁.Sec) (a₁ : Y ⟶ X₁) (M₂ : LB X₂) (th₂ : σ₂ → M₂.Sec) (a₂ : Y ⟶ X₂)
    (N : LB Y) (ty : σ₁ × σ₂ → N.Sec) (h₁ : M₁.IsLB) (h₂ : M₂.IsLB) (hN : N.IsLB)
    (H : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ Y) (v₁ : σ₁ → T) (v₂ : σ₂ → T), SecCoord M₁ th₁ (y ≫ a₁) v₁ →
      SecCoord M₂ th₂ (y ≫ a₂) v₂ → SecCoord N ty y (fun i => v₁ i.1 * v₂ i.2)) :
    idealOf s N ty (𝟙 Y) = graphIdeal s M₁ th₁ a₁ M₂ th₂ a₂ := by
  ext F
  simp only [idealOf, graphIdeal, Ideal.mem_iInf, RingHom.mem_ker, Category.comp_id]
  constructor
  · intro hF T _ β y v₁ v₂ h
    exact hF T _ β y _ ⟨h.1, H T y v₁ v₂ h.2.1 h.2.2⟩
  · intro hF T _ β y v h
    refine eq_zero_of_localization _ fun J hJ => ?_
    set φ := algebraMap T (Localization.AtPrime J) with hφ
    obtain ⟨v₁, hv₁⟩ := (GlobalTheory.ZM.LocalCoord.secCoord_local X₁ M₁ σ₁ th₁ h₁).1 (Localization.AtPrime J) ((spMap φ ≫ y) ≫ a₁)
    obtain ⟨v₂, hv₂⟩ := (GlobalTheory.ZM.LocalCoord.secCoord_local X₂ M₂ σ₂ th₂ h₂).1 (Localization.AtPrime J) ((spMap φ ≫ y) ≫ a₂)
    have hv := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique Y N _ ty T y v hN h.2).1 _ φ
    obtain ⟨u, hu⟩ := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique Y N _ ty _ _ _ hN (H _ _ v₁ v₂ hv₁ hv₂)).2.2 _ hv
    have hv₁' := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique X₁ M₁ _ th₁ _ _ _ h₁ hv₁).2.1 u
    have hs : (spMap φ ≫ y) ≫ s = spMap (φ.comp β) := by
      rw [Category.assoc, h.1]
      exact (Spec.map_comp (CommRingCat.ofHom β) (CommRingCat.ofHom φ)).symm
    have key := hF _ _ (φ.comp β) (spMap φ ≫ y) _ v₂ ⟨hs, hv₁', hv₂⟩
    rw [MvPolynomial.map_eval₂Hom, ← key]
    congr 2
    funext i
    rw [hu i, _root_.mul_assoc]

theorem projRep_graph : ∀ (R K σ₁ σ₂ : Type) [CommRing R] [CommRing K] [Finite σ₁] [Finite σ₂] (x : R →+* K) (I₁ : Ideal (MvPolynomial σ₁ R)) (I₂ : Ideal (MvPolynomial σ₂ R)) (Z₁ Z₂ : Over (Sp R)) (M₁ : LB Z₁.left) (M₂ : LB Z₂.left) (th₁ : σ₁ → M₁.Sec) (th₂ : σ₂ → M₂.Sec) (Y : Scheme.{0}) (s : Y ⟶ Sp K) (a₁ : Y ⟶ Z₁.left) (a₂ : Y ⟶ Z₂.left), ProjRep I₁ Z₁.hom M₁ th₁ → ProjRep I₂ Z₂.hom M₂ th₂ → IsPullback a₁ s Z₁.hom (spMap x) → a₂ ≫ Z₂.hom = s ≫ spMap x → ∃ (N : LB Y) (ty : σ₁ × σ₂ → N.Sec), ProjRep (graphIdeal s M₁ th₁ a₁ M₂ th₂ a₂) s N ty ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ Y) (v₁ : σ₁ → T) (v₂ : σ₂ → T), SecCoord M₁ th₁ (y ≫ a₁) v₁ → SecCoord M₂ th₂ (y ≫ a₂) v₂ → SecCoord N ty y (fun i => v₁ i.1 * v₂ i.2) := by
  intro R K σ₁ σ₂ _ _ _ _ x I₁ I₂ Z₁ Z₂ M₁ M₂ th₁ th₂ Y s a₁ a₂ r₁ r₂ hp ha₂
  obtain ⟨I₃, M₃, th₃, r₃, hseg⟩ := GlobalTheory.ZM.SegreCoord.segre_coordinates R σ₁ σ₂ I₁ I₂ Z₁ Z₂ M₁ M₂ th₁ th₂ r₁ r₂
  have hprop : IsProper Z₂.hom := (GlobalTheory.ZM.projRep_projective_ample R σ₂ I₂ Z₂ M₂ th₂ r₂).2.1
  have hP : IsPullback (fst Z₁ Z₂).left (snd Z₁ Z₂).left Z₁.hom Z₂.hom := IsPullback.of_hasPullback Z₁.hom Z₂.hom
  have hW := IsPullback.of_hasPullback (Z₁ ⊗ Z₂).hom (spMap x)
  generalize pullback.fst (Z₁ ⊗ Z₂).hom (spMap x) = π at hW
  generalize pullback.snd (Z₁ ⊗ Z₂).hom (spMap x) = s' at hW
  generalize pullback (Z₁ ⊗ Z₂).hom (spMap x) = Wd at π s' hW
  obtain ⟨th', r', hbc⟩ := GlobalTheory.ZM.RepBC.projRep_baseChange R K _ x I₃ _ Wd _ s' π M₃ th₃ r₃ hW
  have hfw : (fst Z₁ Z₂).left ≫ Z₁.hom = (Z₁ ⊗ Z₂).hom := Over.w _
  let a : Y ⟶ (Z₁ ⊗ Z₂).left := hP.lift a₁ a₂ (hp.w.trans ha₂.symm)
  have e₁ : a ≫ (fst Z₁ Z₂).left = a₁ := hP.lift_fst _ _ _
  have e₂ : a ≫ (snd Z₁ Z₂).left = a₂ := hP.lift_snd _ _ _
  let i : Y ⟶ Wd := hW.lift a s (by rw [← hfw, ← Category.assoc, e₁, hp.w])
  have i₁ : i ≫ π = a := hW.lift_fst _ _ _
  have i₂ : i ≫ s' = s := hW.lift_snd _ _ _
  let q : Wd ⟶ Y := hp.lift (π ≫ (fst Z₁ Z₂).left) s' (by rw [Category.assoc, hfw, hW.w])
  have q₁ : q ≫ a₁ = π ≫ (fst Z₁ Z₂).left := hp.lift_fst _ _ _
  have q₂ : q ≫ s = s' := hp.lift_snd _ _ _
  have hq : IsPullback π q (fst Z₁ Z₂).left a₁ := by
    refine IsPullback.of_bot ?_ q₁.symm hp
    rw [q₂, hfw]; exact hW
  have hsf : IsSeparated (fst Z₁ Z₂).left :=
    MorphismProperty.of_isPullback (P := @IsSeparated) hP.flip inferInstance
  have hsq : IsSeparated q := MorphismProperty.of_isPullback (P := @IsSeparated) hq hsf
  have hiq : i ≫ q = 𝟙 Y := by
    refine hp.hom_ext ?_ ?_
    · rw [Category.assoc, q₁, ← Category.assoc, i₁, e₁, Category.id_comp]
    · rw [Category.assoc, q₂, i₂, Category.id_comp]
  have hci : IsClosedImmersion i := by
    have : IsClosedImmersion (i ≫ q) := by rw [hiq]; infer_instance
    exact IsClosedImmersion.of_comp i q
  have hN : ((M₃.pull π).pull i).IsLB := pull_isLB r'.1 i
  have hc : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ Y) (v : σ₁ × σ₂ → T),
      SecCoord ((M₃.pull π).pull i) (fun j => GlobalTheory.ZM.RepBC.secPull _ i (th' j)) y v ↔
        SecCoord (M₃.pull π) th' (y ≫ i) v := fun T _ y v => GlobalTheory.ZM.RepBC.secCoord_pull _ th' i y v
  have rY := GlobalTheory.ZM.ClosedCoord.projRep_closed K _ _ Wd Y s' _ th' i _ _ r' hci hN hc
  have H : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ Y) (v₁ : σ₁ → T) (v₂ : σ₂ → T), SecCoord M₁ th₁ (y ≫ a₁) v₁ →
      SecCoord M₂ th₂ (y ≫ a₂) v₂ →
      SecCoord ((M₃.pull π).pull i) (fun j => GlobalTheory.ZM.RepBC.secPull _ i (th' j)) y (fun i => v₁ i.1 * v₂ i.2) := by
    intro T _ y v₁ v₂ h₁ h₂
    rw [hc, hbc, Category.assoc, i₁]
    refine hseg T _ v₁ v₂ ?_ ?_
    · rwa [Category.assoc, e₁]
    · rwa [Category.assoc, e₂]
  rw [i₂, idealOf_eq_graphIdeal s M₁ th₁ a₁ M₂ th₂ a₂ _ _ r₁.1 r₂.1 hN H] at rY
  exact ⟨_, _, rY, H⟩

end GlobalTheory.ZM.GraphSegre
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ProjRepGraphSegreCoordinatesFibreStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projRep_graph_segre_coordinates_fibre : ∀ (R K σ₁ σ₂ : Type) [CommRing R] [CommRing K] [Finite σ₁] [Finite σ₂] (x : R →+* K) (I₁ : Ideal (MvPolynomial σ₁ R)) (I₂ : Ideal (MvPolynomial σ₂ R)) (Z₁ Z₂ : Over (Sp R)) (M₁ : LB Z₁.left) (M₂ : LB Z₂.left) (th₁ : σ₁ → M₁.Sec) (th₂ : σ₂ → M₂.Sec) (Y : Scheme.{0}) (s : Y ⟶ Sp K) (a₁ : Y ⟶ Z₁.left) (a₂ : Y ⟶ Z₂.left), ProjRep I₁ Z₁.hom M₁ th₁ → ProjRep I₂ Z₂.hom M₂ th₂ → IsPullback a₁ s Z₁.hom (spMap x) → a₂ ≫ Z₂.hom = s ≫ spMap x → ∃ (N : LB Y) (ty : σ₁ × σ₂ → N.Sec), ProjRep (graphIdeal s M₁ th₁ a₁ M₂ th₂ a₂) s N ty ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ Y) (v₁ : σ₁ → T) (v₂ : σ₂ → T), SecCoord M₁ th₁ (y ≫ a₁) v₁ → SecCoord M₂ th₂ (y ≫ a₂) v₂ → SecCoord N ty y (fun i => v₁ i.1 * v₂ i.2) := by
  first | exact @GlobalTheory.ZM.GraphSegre.projRep_graph | exact GlobalTheory.ZM.GraphSegre.projRep_graph | (intros; apply GlobalTheory.ZM.GraphSegre.projRep_graph <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqOnTorsion
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.FullRigid

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem eq_of_field (hS : Out.SerreSt) {S : Scheme.{0}} {t : SAB H S} (hp : IsProper t.G.hom)
    (hA : Out.RelAmple t.G t.PP.L) (hK : Out.KTriv t.G t.PP.L) {K : Type} [Field K] [CharZero K] {z : Sp K ⟶ S}
    {t' : SAB H (Sp K)} (m m' : SABMap t' t z) {N : ℕ} (hN : 3 ≤ N)
    (hfix : ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (x : Sp k ⟶ Sp K) (y : Over.mk x ⟶ t'.G),
      y ^ N = 1 → y.left ≫ m.φ = y.left ≫ m'.φ) : m.φ = m'.φ := by
  obtain ⟨θ, hθ, hφ, -, -, w, hw, -⟩ := sabMap_iso m m' rfl rfl
  have := t'.semi.smooth
  have := t'.semi.geomConnected
  obtain ⟨w₁, g₁, -⟩ := m.lin
  obtain ⟨U, hU, hc, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤)
    (x := z (IsLocalRing.closedPoint K)) trivial
  have hy : ∀ y, z y ∈ U := fun y =>
    (congrArg (fun V => y ∈ V) (Scheme.preimage_eq_top_of_closedPoint_mem z hc)).mpr trivial
  have : ConnectedSpace t'.G.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := t'.G.hom) (𝟙 _) (𝟙 _) t'.G.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected t'.G.hom (eSec t'.G (default : PrimeSpectrum K))
  obtain ⟨-, ws, gs', -⟩ := t'.sym
  let P : Out.PolAV (Sp K) :=
    { A := t'.G, g := d, smoothDim := hd, L := t'.PP.L, isLB := t'.PP.isLB
      ample := relAmple_pull m.cart.1 t.PP.isLB t'.PP.isLB ((isGen_iff w₁).1 g₁) U hU hy hA
      ktriv := kTriv_pull m.cart t.PP.isLB t'.PP.isLB ((isGen_iff w₁).1 g₁) hK
      isAb := ⟨inferInstance, inferInstance, MorphismProperty.of_isPullback (P := @IsProper) m.cart.1 hp, ‹_›⟩
      rigid := ⟨t'.PP.rig, t'.PP.rigGen⟩
      sym := fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩ }
  have hNK : IsUnit (N : K) := (Nat.cast_ne_zero.2 (by omega)).isUnit
  have hMu : IsUnit (N : Γ(Sp K, ⊤)) := by
    simpa using hNK.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  have : Etale (Out.mulA t'.G N).left := GrpTangent.etale_id_pow t'.G hMu
  have h : θ.hom = 𝟙 _ := by
    refine hS (Sp K) P N hN θ hθ (fun _ => ⟨⊤, trivial, ?_⟩)
      (fix_torsion_of_forall_geometric t'.G N θ.hom fun k _ _ x y hy => ?_)
    · obtain ⟨t, ht⟩ := gen_of_iso ((isGen_iff w).1 hw) (t'.G.hom ⁻¹ᵁ ⊤).ι
      refine gen_chartPull (chartPullOut t'.PP.L _ _ _ _ fun n => ?_) t ht
      fin_cases n
      exacts [rfl, (Category.comp_id _).symm]
    · let β : K →+* k := (Spec.preimage x).hom
      have : CharZero k := (RingHom.charZero_iff β.injective).1 inferInstance
      apply Over.OverMorphism.ext
      apply m'.cart.1.hom_ext
      · rw [Over.comp_left, Category.assoc]
        exact (congrArg _ hφ).trans (hfix k x y hy)
      · rw [Over.w, Over.w]
  rw [← hφ, h, Over.id_left, Category.id_comp]

theorem eq_on_torsion {D : Datum H} {n N : ℕ} {S S' : Scheme.{0}} {s : S ⟶ Sp (RZ H n N)} {t : SAB H S}
    {lev : D.La → (𝟙_ (Over S) ⟶ t.G)} {t' : SAB H S'} {f : S' ⟶ S} (ν ν' : SABMap t' t f)
    (lv : D.La → (𝟙_ (Over S') ⟶ t'.G)) (hN : 0 < N) (o : FullObj D s t lev)
    (h : ∀ a, (lv a).left ≫ ν.φ = f ≫ (lev a).left) (h' : ∀ a, (lv a).left ≫ ν'.φ = f ≫ (lev a).left)
    (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (x : Sp k ⟶ S') (y : Over.mk x ⟶ t'.G) (hy : y ^ N = 1) :
    y.left ≫ ν.φ = y.left ≫ ν'.φ := by
  obtain ⟨-, I, -, hI⟩ := o.geom k (x ≫ f) (Spec.preimage ((x ≫ f) ≫ s)).hom (Spec.map_preimage _).symm
  have hy₁ : pushHom ν.cart (Over.mk x) y ^ N = 1 := by rw [← map_pow, hy, map_one]
  obtain ⟨a, ha⟩ := (I.onto N hN _).1 hy₁
  have e : (x ≫ f) ≫ (lev a).left = y.left ≫ ν.φ := congrArg (fun q => q.left) ((hI a).trans ha)
  have e₁ : y.left = x ≫ (lv a).left := by
    apply ν.cart.1.hom_ext
    · rw [Category.assoc]
      exact e.symm.trans ((Category.assoc _ _ _).trans (congrArg (x ≫ ·) (h a).symm))
    · rw [Over.w, Category.assoc, Over.w]
      exact (Category.comp_id _).symm
  rw [e₁, Category.assoc, Category.assoc]
  exact congrArg (x ≫ ·) ((h a).trans (h' a).symm)

end GlobalTheory.FullRigid

theorem GlobalTheory.fullObj_rigid : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n N : ℕ) (S S' : Scheme.{0}) (s : S ⟶ Sp (RZ H n N)) (t : SAB H S) (lev : D.La → (𝟙_ (Over S) ⟶ t.G)) (t' : SAB H S') (f : S' ⟶ S) (ν ν' : SABMap t' t f) (lv : D.La → (𝟙_ (Over S') ⟶ t'.G)), 3 ≤ N → Odd N → FullObj D s t lev → IsReduced S' → (∀ x : S', CharZero (S'.residueField x)) → (∀ a, (lv a).left ≫ ν.φ = f ≫ (lev a).left) → (∀ a, (lv a).left ≫ ν'.φ = f ≫ (lev a).left) → ν.φ = ν'.φ := by
  intro hL E _ _ _ H D n N S S' s t lev t' f ν ν' lv hN _ o _ hc h h'
  obtain ⟨θ, hθ, hφ, -⟩ := sabMap_iso ν ν' rfl rfl
  have hA : IsAbelianScheme t'.G := ⟨t'.semi.comm, t'.semi.smooth,
    MorphismProperty.of_isPullback (P := @IsProper) ν.cart.1 o.proper, t'.semi.geomConnected⟩
  have key : θ.hom = 𝟙 _ := by
    refine GlobalTheory.eq_id_of_forall_geometric_fibre hL.globalFns t'.G hA θ.hom (IsMonHom.one_hom θ.hom) fun p => ?_
    have := hc p
    let j : Sp (S'.residueField p) ⟶ S' := S'.fromSpecResidueField p
    have hsemi : IsSemiAbelian ((Over.pullback j).obj t'.G) := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · have := t'.semi.comm; infer_instance
      · have := t'.semi.smooth; change Smooth (pullback.snd t'.G.hom j); infer_instance
      · have := t'.semi.separated; change IsSeparated (pullback.snd t'.G.hom j); infer_instance
      · have := t'.semi.quasiCompact; change QuasiCompact (pullback.snd t'.G.hom j); infer_instance
      · have := t'.semi.geomConnected; change GeometricallyConnected (pullback.snd t'.G.hom j); infer_instance
      · intro Ω _ _ q
        obtain ⟨E⟩ := t'.semi.fibres Ω (q ≫ j)
        exact ⟨torusExtOfIso (pullCompIso q j t'.G) E⟩
    have hPull : ∃ (PP' : RigLB ((Over.pullback j).obj t'.G))
        (cub : CubicalStr _ PP') (sym : PP'.IsSymmetric) (adj : _) (prim : _)
        (m : SABMap ⟨(Over.pullback j).obj t'.G, hsemi,
          OAct.pullback j t'.G t'.act, PP', cub, sym, adj, prim⟩ t' j),
        m.φ = pullback.fst t'.G.hom j := by
      have h := isGrpPullback_pullback t'.G j
      obtain ⟨hL, hr, ⟨c', hc'⟩, hs⟩ := Out.CubePf.cubePull _ _ t'.G _ (cubeMapOf h) t'.PP t'.cub
      have hact : ∀ a, ((OAct.pullback j t'.G t'.act).act a).left ≫ pullback.fst t'.G.hom j =
          pullback.fst t'.G.hom j ≫ (t'.act.act a).left := fun a => pullback.lift_fst _ _ _
      have pa : ∀ {T : Over (Sp (S'.residueField p))} (x : T ⟶ (Over.pullback j).obj t'.G) a,
          pushPt h.1.w (x ≫ (OAct.pullback j t'.G t'.act).act a) = pushPt h.1.w x ≫ t'.act.act a := fun x a =>
        Over.OverMorphism.ext (by
          show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
          rw [Category.assoc, hact, Category.assoc])
      refine ⟨(cubeMapOf h).rigLB t'.PP hL hr, c', hs t'.sym, fun a => ?_, ?_,
        ⟨cubeMapOf h, h, rfl, hact, hc'⟩, rfl⟩
      · let U := lift (pushPt h.1.w (fst ((Over.pullback j).obj t'.G) ((Over.pullback j).obj t'.G)))
          (pushPt h.1.w (snd ((Over.pullback j).obj t'.G) ((Over.pullback j).obj t'.G)))
        refine LBIso.chartPull (chartPullLinComb t'.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down)
          (chartPullLinComb t'.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) (t'.adj a)
        · fin_cases i
          · exact (pa _ a).trans (by simp [U])
          · simp [U]
        · fin_cases i
          · simp [U]
          · exact (pa _ _).trans (by simp [U])
      · let U := pushPt h.1.w (𝟙 ((Over.pullback j).obj t'.G))
        refine LBIso.chartPull (chartPullPull t'.PP.L _)
          (chartPullLinComb t'.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) t'.prim
        fin_cases i
        · simp [U]
        · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa _ _)
    obtain ⟨PP', cub, sym, adj, prim, m, -⟩ := hPull
    generalize (⟨(Over.pullback j).obj t'.G, hsemi,
      OAct.pullback _ t'.G t'.act, PP', cub, sym, adj, prim⟩ : SAB H _) = t'' at m
    obtain ⟨a, ha⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ ν m
    obtain ⟨b, hb⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ ν' m
    have e : a.φ = b.φ := GlobalTheory.FullRigid.eq_of_field hL.serre o.proper o.ample o.ktriv a b hN fun k _ _ _ x y hy => by
      have hy₁ : pushHom m.cart (Over.mk x) y ^ N = 1 := by rw [← map_pow, hy, map_one]
      have e₁ := GlobalTheory.FullRigid.eq_on_torsion ν ν' lv (by omega) o h h' k (x ≫ j) _ hy₁
      rw [ha, hb, ← Category.assoc, ← Category.assoc]
      exact e₁
    refine ⟨_, _, j, m.φ, _, (default : PrimeSpectrum (S'.residueField p)),
      Scheme.fromSpecResidueField_apply p _, m.cart.1, ?_⟩
    apply ν'.cart.1.hom_ext
    · rw [Category.assoc]
      exact (congrArg (m.φ ≫ ·) hφ).trans (ha.symm.trans (e.trans hb))
    · rw [Category.assoc, Over.w]
  rw [← hφ, key, Over.id_left, Category.id_comp]
end
