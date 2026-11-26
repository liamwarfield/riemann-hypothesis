module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FontaineAinfLocalDomainXiAdicOrder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentMapIsIntegral
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LegendreBoundsFactorialMultiIndexCapelli
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.AwayLiftCompFromZeroRingHom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussianFirstCoordsMeasurePreserving
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiIsoHypercohomologyBijective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceCohomologyPresheafClassesAsCocycles
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceCohomologyPresheafClassesAsCocycles
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.DiscElt

variable (R : Type) [CommRing R]

theorem hkpull_comp {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (F : Shv R) (n : ℤ) (x : HK R M F n) :
    HK.pull R (f ≫ g) F n x = HK.pull R f F n (HK.pull R g F n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_comp]

theorem hkpull_single {X Y : Shv R} (g : X ⟶ Y) (F : Shv R) (n : ℤ) (t : Y ⟶ (res R F).X n)
    (ht : t ≫ (res R F).d n (n + 1) = 0) :
    HK.pull R ((CochainComplex.singleFunctor (Shv R) 0).map g) F n
      (CohomologyClass.mk (Cocycle.fromSingleMk t (zero_add n) (n + 1) rfl ht)) =
      CohomologyClass.mk (Cocycle.fromSingleMk (g ≫ t) (zero_add n) (n + 1) rfl (by simp [ht])) := by
  rw [Cocycle.fromSingleMk_precomp g t (zero_add n) (n + 1) rfl ht]
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cocycle.precomp]

end GlobalTheory.EtC.DiscElt

namespace GlobalTheory.EtC


open GlobalTheory.EtC.DiscElt in
theorem disc_elt_cls : ∀ (R : Type) [CommRing R] (F : Shv R), ∃ cl : ∀ (P : PSh) (n : ℤ) (t : (free R).obj P ⟶ (res R F).X n), t ≫ (res R F).d n (n + 1) = 0 → H R (disc.obj P) F n, (∀ P n x, ∃ t ht, cl P n t ht = x) ∧ (∀ P n t ht t' ht', cl P n t ht = cl P n t' ht' ↔ ∃ y : (free R).obj P ⟶ (res R F).X (n - 1), t = t' + y ≫ (res R F).d (n - 1) n) ∧ (∀ P n, cl P n 0 zero_comp = 0) ∧ ∀ (P P' : PSh) (f : P ⟶ P') n t ht, ∃ h, pull R (disc.map f) F n (cl P' n t ht) = cl P n ((free R).map f ≫ t) h := by
  intro R _ F
  obtain ⟨e, -, hnat⟩ := chains_disc_homotopyEquiv R
  have hb : ∀ (P : PSh) (n : ℤ), Function.Bijective (HK.pull R (e P).hom F n) := fun P n => by
    haveI : QuasiIso (e P).hom := (e P).quasiIso_hom
    exact quasiIso_hypercohomology_bijective' R (e P).hom F n
  let E : ∀ (P : PSh) (n : ℤ), H R (disc.obj P) F n ≃ HK R (sgl ((free R).obj P)) F n :=
    fun P n => Equiv.ofBijective _ (hb P n)
  have hE : ∀ P n x, E P n x = HK.pull R (e P).hom F n x := fun _ _ _ => rfl
  let c : ∀ (P : PSh) (n : ℤ) (t : (free R).obj P ⟶ (res R F).X n), t ≫ (res R F).d n (n + 1) = 0 →
      HK R (sgl ((free R).obj P)) F n :=
    fun P n t ht => CohomologyClass.mk (Cocycle.fromSingleMk t (zero_add n) (n + 1) rfl ht)
  refine ⟨fun P n t ht => (E P n).symm (c P n t ht), ?_, ?_, ?_, ?_⟩
  · intro P n x
    obtain ⟨z, hz⟩ := (E P n x).mk_surjective
    obtain ⟨t, ht, rfl⟩ := Cocycle.fromSingleMk_surjective z n (zero_add n) (n + 1) rfl
    exact ⟨t, ht, by rw [Equiv.symm_apply_eq]; exact hz⟩
  · intro P n t ht t' ht'
    rw [(E P n).symm.injective.eq_iff]
    change CohomologyClass.mk _ = CohomologyClass.mk _ ↔ _
    rw [← sub_eq_zero, ← CohomologyClass.mk_sub, ← Cocycle.fromSingleMk_sub _ _ _ _ _ ht ht',
      CohomologyClass.mk_eq_zero_iff,
      Cocycle.fromSingleMk_mem_coboundaries_iff _ _ _ _ _ (n - 1) (by omega)]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y, by rw [hy]; abel⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, by rw [hy]; abel⟩
  · intro P n
    change (E P n).symm (CohomologyClass.mk _) = 0
    rw [Equiv.symm_apply_eq, hE, map_zero, Cocycle.fromSingleMk_zero, CohomologyClass.mk_zero]
  · intro P P' f n t ht
    refine ⟨by simp [ht], ?_⟩
    rw [Equiv.eq_symm_apply, hE]
    change HK.pull R (e P).hom F n (HK.pull R ((chains R).map (disc.map f)) F n _) = _
    rw [← hkpull_comp, hnat f, hkpull_comp]
    have h1 : HK.pull R (e P').hom F n ((E P' n).symm (c P' n t ht)) = c P' n t ht := by
      rw [← hE, Equiv.apply_symm_apply]
    rw [h1]
    exact hkpull_single R ((free R).map f) F n t ht

end GlobalTheory.EtC
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceCohomologyPresheafClassesAsCocyclesStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleSpaceCohomology_presheaf_classes_as_cocycles : ∀ (R : Type) [CommRing R] (F : Shv R), ∃ cl : ∀ (P : PSh) (n : ℤ) (t : (free R).obj P ⟶ (res R F).X n), t ≫ (res R F).d n (n + 1) = 0 → H R (disc.obj P) F n, (∀ P n x, ∃ t ht, cl P n t ht = x) ∧ (∀ P n t ht t' ht', cl P n t ht = cl P n t' ht' ↔ ∃ y : (free R).obj P ⟶ (res R F).X (n - 1), t = t' + y ≫ (res R F).d (n - 1) n) ∧ (∀ P n, cl P n 0 zero_comp = 0) ∧ ∀ (P P' : PSh) (f : P ⟶ P') n t ht, ∃ h, pull R (disc.map f) F n (cl P' n t ht) = cl P n ((free R).map f ≫ t) h := by
  first | (exact @GlobalTheory.EtC.disc_elt_cls) | (exact GlobalTheory.EtC.disc_elt_cls) | (intros; apply GlobalTheory.EtC.disc_elt_cls <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyCoefficientMapFunctorialAdditive
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyCoefficientMapFunctorialAdditive
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.PostFun

variable {R : Type} [CommRing R]

theorem post_eq_cpush (K : Cx R) {F G : Shv R} (φ : F ⟶ G) (n : ℤ) :
    HK.post R K φ n = cpush K (resMap R φ) n := rfl

def resMapIdHomotopy (F : Shv R) : Homotopy (resMap R (𝟙 F)) (𝟙 (res R F)) := by
  have H2 := (InjectiveResolution.descIdHomotopy F (injectiveResolution F)).extend ComplexShape.embeddingUpNat
  rw [HomologicalComplex.extendMap_id] at H2
  exact H2

def resMapCompHomotopy {F G M : Shv R} (φ : F ⟶ G) (ψ : G ⟶ M) :
    Homotopy (resMap R (φ ≫ ψ)) (resMap R φ ≫ resMap R ψ) := by
  have H2 := (InjectiveResolution.descCompHomotopy φ ψ (injectiveResolution F) (injectiveResolution G)
    (injectiveResolution M)).extend ComplexShape.embeddingUpNat
  rw [HomologicalComplex.extendMap_comp] at H2
  exact H2

def resMapAddHomotopy {F G : Shv R} (φ ψ : F ⟶ G) :
    Homotopy (resMap R (φ + ψ)) (resMap R φ + resMap R ψ) := by
  have H : Homotopy (InjectiveResolution.desc (φ + ψ) (injectiveResolution G) (injectiveResolution F))
      (InjectiveResolution.desc φ (injectiveResolution G) (injectiveResolution F) +
        InjectiveResolution.desc ψ (injectiveResolution G) (injectiveResolution F)) := by
    apply InjectiveResolution.descHomotopy (φ + ψ)
    · simp
    · simp [Preadditive.comp_add, Preadditive.add_comp, Functor.map_add (f := _)]
  have H2 := H.extend ComplexShape.embeddingUpNat
  rw [HomologicalComplex.extendMap_add] at H2
  exact H2

theorem cpush_add (K : Cx R) {I J : Cx R} (f g : I ⟶ J) (n : ℤ) (x : CohomologyClass K I n) :
    cpush K (f + g) n x = cpush K f n x + cpush K g n x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  change CohomologyClass.mk _ = CohomologyClass.mk _ + CohomologyClass.mk _
  rw [← CohomologyClass.mk_add]
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_add, Cochain.comp_add]

theorem post_id (K : Cx R) (F : Shv R) (n : ℤ) (x : HK R K F n) : HK.post R K (𝟙 F) n x = x := by
  rw [post_eq_cpush, InjResCmp.cpush_homotopy K (resMapIdHomotopy F), InjResCmp.cpush_id]

theorem post_comp (K : Cx R) {F G M : Shv R} (φ : F ⟶ G) (ψ : G ⟶ M) (n : ℤ) (x : HK R K F n) :
    HK.post R K (φ ≫ ψ) n x = HK.post R K ψ n (HK.post R K φ n x) := by
  rw [post_eq_cpush, InjResCmp.cpush_homotopy K (resMapCompHomotopy φ ψ), InjResCmp.cpush_comp]
  rfl

theorem post_add (K : Cx R) {F G : Shv R} (φ ψ : F ⟶ G) (n : ℤ) :
    HK.post R K (φ + ψ) n = HK.post R K φ n + HK.post R K ψ n := by
  ext x
  rw [post_eq_cpush, InjResCmp.cpush_homotopy K (resMapAddHomotopy φ ψ), cpush_add]
  rfl

def postHom (K : Cx R) (F G : Shv R) (n : ℤ) : (F ⟶ G) →+ (HK R K F n →+ HK R K G n) :=
  AddMonoidHom.mk' (fun φ => HK.post R K φ n) (fun φ ψ => post_add K φ ψ n)

theorem post_zsmul (K : Cx R) {F G : Shv R} (φ : F ⟶ G) (c : ℤ) (n : ℤ) (x : HK R K F n) :
    HK.post R K (c • φ) n x = c • HK.post R K φ n x := by
  have h := map_zsmul (postHom K F G n) c φ
  exact DFunLike.congr_fun h x

theorem pull_post {K L : Cx R} (f : L ⟶ K) {F G : Shv R} (φ : F ⟶ G) (n : ℤ) (x : HK R K F n) :
    HK.pull R f G n (HK.post R K φ n x) = HK.post R L φ n (HK.pull R f F n x) :=
  ZcFun.cpull_cpush f (resMap R φ) n x

theorem main : ∀ (R : Type) [CommRing R] (K : Cx R) (n : ℤ), (∀ (F : Shv R) x, HK.post R K (𝟙 F) n x = x) ∧ (∀ {F G M : Shv R} (φ : F ⟶ G) (ψ : G ⟶ M) x, HK.post R K (φ ≫ ψ) n x = HK.post R K ψ n (HK.post R K φ n x)) ∧ (∀ {F G : Shv R} (φ ψ : F ⟶ G), HK.post R K (φ + ψ) n = HK.post R K φ n + HK.post R K ψ n) ∧ (∀ {F G : Shv R} (φ : F ⟶ G) (c : ℤ) x, HK.post R K (c • φ) n x = c • HK.post R K φ n x) ∧ ∀ {L : Cx R} (f : L ⟶ K) {F G : Shv R} (φ : F ⟶ G) x, HK.pull R f G n (HK.post R K φ n x) = HK.post R L φ n (HK.pull R f F n x) := by
  intro R _ K n
  exact ⟨fun F x => post_id K F n x, fun φ ψ x => post_comp K φ ψ n x, fun φ ψ => post_add K φ ψ n,
    fun φ c x => post_zsmul K φ c n x, fun f _ _ φ x => pull_post f φ n x⟩

end GlobalTheory.EtC.PostFun
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyCoefficientMapFunctorialAdditiveStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hypercohomologyCoefficientMap_functorial_additive : ∀ (R : Type) [CommRing R] (K : Cx R) (n : ℤ), (∀ (F : Shv R) x, HK.post R K (𝟙 F) n x = x) ∧ (∀ {F G M : Shv R} (φ : F ⟶ G) (ψ : G ⟶ M) x, HK.post R K (φ ≫ ψ) n x = HK.post R K ψ n (HK.post R K φ n x)) ∧ (∀ {F G : Shv R} (φ ψ : F ⟶ G), HK.post R K (φ + ψ) n = HK.post R K φ n + HK.post R K ψ n) ∧ (∀ {F G : Shv R} (φ : F ⟶ G) (c : ℤ) x, HK.post R K (c • φ) n x = c • HK.post R K φ n x) ∧ ∀ {L : Cx R} (f : L ⟶ K) {F G : Shv R} (φ : F ⟶ G) x, HK.pull R f G n (HK.post R K φ n x) = HK.post R L φ n (HK.pull R f F n x) := by
  first | (exact @GlobalTheory.EtC.PostFun.main) | (exact GlobalTheory.EtC.PostFun.main) | (intros; apply GlobalTheory.EtC.PostFun.main  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactMappingConeResolutionHomotopyEquiv
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactMappingConeResolutionHomotopyEquiv
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.ConeRes

variable {C : Type*} [Category C] [Abelian C]


open DerivedCategory Pretriangulated in
theorem quasiIso_mappingCone_map {K₁ L₁ K₂ L₂ : CochainComplex C ℤ} (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂)
    (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) (comm : φ₁ ≫ b = a ≫ φ₂) [QuasiIso a] [QuasiIso b] :
    QuasiIso (mappingCone.map φ₁ φ₂ a b comm) := by
  letI := HasDerivedCategory.standard C
  rw [← isIso_Q_map_iff_quasiIso]
  exact isIso₃_of_isIso₁₂ (Q.mapTriangle.map (mappingCone.triangleMap φ₁ φ₂ a b comm))
    (mappingCone_triangle_distinguished φ₁) (mappingCone_triangle_distinguished φ₂)
    (show IsIso (Q.map a) from inferInstance) (show IsIso (Q.map b) from inferInstance)

theorem homotopy_of_mk_eq {K L : CochainComplex C ℤ} {f g : K ⟶ L}
    (h : CohomologyClass.mk (Cocycle.ofHom f) = CohomologyClass.mk (Cocycle.ofHom g)) : Nonempty (Homotopy f g) := by
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ (-1) (by omega)] at h
  obtain ⟨β, hβ⟩ := h
  refine ⟨(Cochain.equivHomotopy f g).symm ⟨β, ?_⟩⟩
  rw [hβ]
  simp

theorem quasiIso_of_homotopy {K L : CochainComplex C ℤ} {f g : K ⟶ L} (h : Homotopy f g) (hg : QuasiIso g) :
    QuasiIso f := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap, h.homologyMap_eq]
  infer_instance

variable {R : Type} [CommRing R]

theorem mk_ofHom_comp {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) :
    CohomologyClass.mk (Cocycle.ofHom (f ≫ g)) = cpull f M 0 (CohomologyClass.mk (Cocycle.ofHom g)) := by
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_comp]

theorem resAug_comm {F G : Shv R} (φ : F ⟶ G) :
    (CochainComplex.singleFunctor (Shv R) 0).map φ ≫ resAug G = resAug F ≫ resMap R φ :=
  (InjectiveResolution.Hom.ι'_comp_hom'
    (⟨InjectiveResolution.desc φ (injectiveResolution G) (injectiveResolution F),
      InjectiveResolution.desc_commutes_zero φ _ _⟩ : InjectiveResolution.Hom _ _ φ)).symm

instance resAug_quasiIso (F : Shv R) : QuasiIso (resAug F) := (inferInstance : QuasiIso (injectiveResolution F).ι')

instance res_isKInjective (F : Shv R) : (res R F).IsKInjective :=
  inferInstanceAs ((injectiveResolution F).cochainComplex.IsKInjective)

theorem cone_isKInjective {F G : Shv R} (φ : F ⟶ G) : (mappingCone (resMap R φ)).IsKInjective := by
  haveI : ∀ n, Injective ((res R F).X n) := fun n => inferInstanceAs (Injective ((injectiveResolution F).cochainComplex.X n))
  haveI : ∀ n, Injective ((res R G).X n) := fun n => inferInstanceAs (Injective ((injectiveResolution G).cochainComplex.X n))
  haveI : (res R F).IsStrictlyGE 0 := inferInstanceAs ((injectiveResolution F).cochainComplex.IsStrictlyGE 0)
  haveI : (res R G).IsStrictlyGE 0 := inferInstanceAs ((injectiveResolution G).cochainComplex.IsStrictlyGE 0)
  haveI : ∀ n, Injective ((mappingCone (resMap R φ)).X n) := fun n =>
    Injective.of_iso (HomologicalComplex.homotopyCofiber.XIsoBiprod (resMap R φ) n (n + 1) rfl).symm inferInstance
  haveI : (mappingCone (resMap R φ)).IsStrictlyGE (-1) := CochainComplex.isStrictlyGE_mappingCone _ 0 0 (-1)
  exact isKInjective_of_injective _ (-1)

end GlobalTheory.EtC.ConeRes


open GlobalTheory.EtC.ConeRes in
theorem GlobalTheory.EtC.cone_resMap_homotopyEquiv : ∀ (R : Type) [CommRing R] (S : ShortComplex (Shv R)), S.ShortExact →
    ∃ e : HomotopyEquiv (mappingCone (resMap R S.f)) (res R S.X₃),
      Nonempty (Homotopy (mappingCone.inr (resMap R S.f) ≫ e.hom) (resMap R S.g)) := by
  intro R _ S hS
  have hS' : (S.map (CochainComplex.singleFunctor (Shv R) 0)).ShortExact :=
    hS.map_of_exact (HomologicalComplex.single _ _ _)
  haveI := mappingCone.quasiIso_descShortComplex hS'
  haveI := cone_isKInjective S.f
  let q := mappingCone.descShortComplex (S.map (CochainComplex.singleFunctor (Shv R) 0))
  let m := mappingCone.map _ (resMap R S.f) (resAug S.X₁) (resAug S.X₂) (resAug_comm S.f)
  haveI : QuasiIso m := quasiIso_mappingCone_map _ _ _ _ _
  obtain ⟨c, hc⟩ := (GlobalTheory.EtC.cpull_bijective_of_quasiIso R m (res R S.X₃) 0).2
    (CohomologyClass.mk (Cocycle.ofHom (q ≫ resAug S.X₃)))
  obtain ⟨z, rfl⟩ := c.mk_surjective
  let u : mappingCone (resMap R S.f) ⟶ res R S.X₃ := Cocycle.homOf z
  have hz : z = Cocycle.ofHom u := (Cocycle.ofHom_homOf_eq_self z).symm
  rw [hz, ← mk_ofHom_comp] at hc
  obtain ⟨H1⟩ := homotopy_of_mk_eq hc
  haveI : QuasiIso (m ≫ u) := quasiIso_of_homotopy H1 ((quasiIso_iff_comp_left q (resAug S.X₃)).2 (resAug_quasiIso S.X₃))
  haveI : QuasiIso u := (quasiIso_iff_comp_left m u).1 inferInstance
  obtain ⟨e, he⟩ := (CochainComplex.IsKInjective.quasiIso_iff u).1 inferInstance
  refine ⟨e, homotopy_of_mk_eq ?_⟩
  apply (GlobalTheory.EtC.cpull_bijective_of_quasiIso R (resAug S.X₂) (res R S.X₃) 0).1
  rw [← mk_ofHom_comp, ← mk_ofHom_comp, he]
  have hinr : mappingCone.inr (S.map (CochainComplex.singleFunctor (Shv R) 0)).f ≫ m =
      resAug S.X₂ ≫ mappingCone.inr (resMap R S.f) :=
    mappingCone.inr_desc ((CochainComplex.singleFunctor (Shv R) 0).map S.f) _ _ _
  have hq : mappingCone.inr (S.map (CochainComplex.singleFunctor (Shv R) 0)).f ≫ q =
      (CochainComplex.singleFunctor (Shv R) 0).map S.g := mappingCone.inr_descShortComplex _
  have h1 : resAug S.X₂ ≫ mappingCone.inr (resMap R S.f) ≫ u =
      mappingCone.inr (S.map (CochainComplex.singleFunctor (Shv R) 0)).f ≫ m ≫ u :=
    ((reassoc_of% hinr) u).symm
  have h2 : mappingCone.inr (S.map (CochainComplex.singleFunctor (Shv R) 0)).f ≫ q ≫ resAug S.X₃ =
      (CochainComplex.singleFunctor (Shv R) 0).map S.g ≫ resAug S.X₃ :=
    (reassoc_of% hq) (resAug S.X₃)
  exact ((congrArg (fun x => CohomologyClass.mk (Cocycle.ofHom x)) h1).trans (mk_ofHom_comp _ _)).trans
    ((congrArg (cpull _ _ 0) hc).trans ((mk_ofHom_comp _ _).symm.trans
      ((congrArg (fun x => CohomologyClass.mk (Cocycle.ofHom x)) h2).trans
        (congrArg (fun x => CohomologyClass.mk (Cocycle.ofHom x)) (resAug_comm S.g)))))
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactMappingConeResolutionHomotopyEquivStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shortExact_mappingCone_resolution_homotopyEquiv : ∀ (R : Type) [CommRing R] (S : ShortComplex (Shv R)), S.ShortExact → ∃ e : HomotopyEquiv (mappingCone (resMap R S.f)) (res R S.X₃), Nonempty (Homotopy (mappingCone.inr (resMap R S.f) ≫ e.hom) (resMap R S.g)) := by
  first | (exact @GlobalTheory.EtC.cone_resMap_homotopyEquiv) | (exact GlobalTheory.EtC.cone_resMap_homotopyEquiv) | (intros; apply GlobalTheory.EtC.cone_resMap_homotopyEquiv  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerContentValuationDetPowBounds
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerContentValuationDetPowBounds
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.DetPowContent

theorem rpow_digitSum_le (p : ℕ) (hp : 2 ≤ p) (n : ℕ) :
    (p : ℝ) ^ ((((Nat.digits p n).sum : ℕ) : ℝ) / ((p : ℝ) - 1)) ≤ (n : ℝ) + 1 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hpos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hdig : ∀ d : ℕ, d < p → (p : ℝ) ^ ((d : ℝ) / ((p : ℝ) - 1)) ≤ (d : ℝ) + 1 := by
    intro d hd
    have hd' : (d : ℝ) ≤ (p : ℝ) - 1 := by
      have h1 : d + 1 ≤ p := hd
      have h2 : (d : ℝ) + 1 ≤ p := by exact_mod_cast h1
      linarith
    have ht0 : 0 ≤ (d : ℝ) / ((p : ℝ) - 1) := div_nonneg (Nat.cast_nonneg _) hpos.le
    have ht1 : (d : ℝ) / ((p : ℝ) - 1) ≤ 1 := (div_le_one hpos).mpr hd'
    have h := Real.geom_mean_le_arith_mean2_weighted ht0 (sub_nonneg.mpr ht1)
      (by linarith : (0 : ℝ) ≤ p) zero_le_one (add_sub_cancel _ _)
    rw [Real.one_rpow, mul_one] at h
    have e : (d : ℝ) / ((p : ℝ) - 1) * p + (1 - (d : ℝ) / ((p : ℝ) - 1)) * 1 = (d : ℝ) + 1 := by
      field_simp
      ring
    linarith
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [Nat.digits_def' (by omega) hn, List.sum_cons, Nat.cast_add, add_div,
        Real.rpow_add (by linarith)]
      have h1 := ih (n / p) (Nat.div_lt_self hn (by omega))
      have h2 := hdig (n % p) (Nat.mod_lt _ (by omega))
      have hmod : ((n % p : ℕ) : ℝ) + (p : ℝ) * ((n / p : ℕ) : ℝ) = n := by
        exact_mod_cast Nat.mod_add_div n p
      have hlt : ((n % p : ℕ) : ℝ) + 1 ≤ p := by
        exact_mod_cast (Nat.mod_lt n (by omega : 0 < p))
      have hm0 : (0 : ℝ) ≤ ((n / p : ℕ) : ℝ) := Nat.cast_nonneg _
      calc (p : ℝ) ^ (((n % p : ℕ) : ℝ) / ((p : ℝ) - 1)) *
            (p : ℝ) ^ ((((Nat.digits p (n / p)).sum : ℕ) : ℝ) / ((p : ℝ) - 1))
          ≤ (((n % p : ℕ) : ℝ) + 1) * (((n / p : ℕ) : ℝ) + 1) :=
            mul_le_mul h2 h1 (Real.rpow_nonneg (by linarith) _) (by positivity)
        _ ≤ (n : ℝ) + 1 := by nlinarith

theorem digitSum_le_logb (p : ℕ) (hp : 2 ≤ p) (n : ℕ) :
    (((Nat.digits p n).sum : ℕ) : ℝ) ≤ ((p : ℝ) - 1) * Real.logb p ((n : ℝ) + 1) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hpos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have h2 : (((Nat.digits p n).sum : ℕ) : ℝ) / ((p : ℝ) - 1) ≤ Real.logb p ((n : ℝ) + 1) :=
    (Real.le_logb_iff_rpow_le hp1 (by positivity)).mpr (rpow_digitSum_le p hp n)
  rw [div_le_iff₀ hpos] at h2
  linarith [mul_comm (Real.logb p ((n : ℝ) + 1)) ((p : ℝ) - 1)]

theorem padicValNat_factorial_ge (p : ℕ) (hp : p.Prime) (N : ℕ) :
    (N : ℝ) / ((p : ℝ) - 1) - Real.logb p ((N : ℝ) + 1) ≤ (padicValNat p N.factorial : ℝ) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have h := digitSum_le_logb p hp.two_le N
  have h3 : (((Nat.digits p N).sum : ℕ) : ℝ) / ((p : ℝ) - 1) ≤ Real.logb p ((N : ℝ) + 1) := by
    rw [div_le_iff₀ hpos]
    linarith [mul_comm (Real.logb p ((N : ℝ) + 1)) ((p : ℝ) - 1)]
  rw [GlobalTheory.LegendreBounds.legendre_real p hp N, sub_div]
  linarith

theorem toE_coe (r : ℝ) : toE (r : WithTop ℝ) = (r : EReal) := rfl

theorem toE_mono {x y : WithTop ℝ} (h : x ≤ y) : toE x ≤ toE y := by
  unfold toE
  exact WithBot.coe_le_coe.mpr h

theorem val_mfact {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {p : ℕ} (hp : p.Prime)
    (hv : v (p : C) = 1) {σ : Type} [Fintype σ] (α : σ →₀ ℕ) :
    v (mfact α : C) = ((∑ k, (padicValNat p (α k).factorial : ℝ) : ℝ) : WithTop ℝ) := by
  classical
  have hne : (∏ k, (α k).factorial) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun k _ => Nat.factorial_ne_zero _)
  have e : (mfact α : C) = ((∏ k, (α k).factorial : ℕ) : C) := by
    unfold mfact
    rw [Finsupp.prod_fintype _ _ (fun k => by simp), Nat.cast_prod]
  rw [e, ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.natCast_eq_factorization v hp hv hne, Nat.factorization_def _ hp, ← Nat.padicValNat_def,
    GlobalTheory.LegendreBounds.padicValNat_prod_factorial p hp Finset.univ α]

theorem content_detPow_bounds : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ), p.Prime → v (p : C) = 1 → ∀ (i c : ℕ), content v (detPow C i c) ≤ (((i * c : ℝ) / (p - 1) : ℝ) : EReal) ∧ ((((i * c : ℝ) / (p - 1) - (i : ℝ) ^ 2 * Real.logb p (c + 1) : ℝ)) : EReal) ≤ content v (detPow C i c) := by
  intro C _ _ v p hp hv i c
  classical
  obtain ⟨-, hint, hdiag, hrows⟩ := GlobalTheory.T.matrixVariablesDeterminantPow_monomial_shape C i c
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have key : ∀ α ∈ (detPow C i c).support,
      (∑ k, ((α k : ℕ) : ℝ)) = (i : ℝ) * c ∧ ∀ k, α k ≤ c := by
    intro α hα
    obtain ⟨-, hb⟩ := hrows α hα
    refine ⟨?_, ?_⟩
    · rw [Fintype.sum_sigma]
      have hb' : ∀ b : Fin i, (∑ a : Fin i, ((α ⟨b, a⟩ : ℕ) : ℝ)) = c := by
        intro b
        exact_mod_cast hb b
      simp only [hb', Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    · rintro ⟨b, a⟩
      rw [← hb b]
      exact Finset.single_le_sum (f := fun a' => α ⟨b, a'⟩) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ a)
  have upS : ∀ α ∈ (detPow C i c).support,
      (∑ k, (padicValNat p (α k).factorial : ℝ)) ≤ (i * c : ℝ) / (p - 1) := by
    intro α hα
    calc (∑ k, (padicValNat p (α k).factorial : ℝ))
        ≤ ∑ k, ((α k : ℕ) : ℝ) / ((p : ℝ) - 1) :=
          Finset.sum_le_sum (fun k _ => GlobalTheory.LegendreBounds.upper p hp (α k))
      _ = (i * c : ℝ) / (p - 1) := by rw [← Finset.sum_div, (key α hα).1]
  have loS : ∀ α ∈ (detPow C i c).support,
      (i * c : ℝ) / (p - 1) - (i : ℝ) ^ 2 * Real.logb p (c + 1)
        ≤ ∑ k, (padicValNat p (α k).factorial : ℝ) := by
    intro α hα
    obtain ⟨hsum, hle⟩ := key α hα
    have h1 : ∀ k, ((α k : ℕ) : ℝ) / ((p : ℝ) - 1) - Real.logb p ((c : ℝ) + 1)
        ≤ (padicValNat p (α k).factorial : ℝ) := by
      intro k
      have hl : Real.logb p (((α k : ℕ) : ℝ) + 1) ≤ Real.logb p ((c : ℝ) + 1) :=
        Real.logb_le_logb_of_le hp1 (by positivity) (by exact_mod_cast Nat.add_le_add_right (hle k) 1)
      have := padicValNat_factorial_ge p hp (α k)
      linarith
    calc (i * c : ℝ) / (p - 1) - (i : ℝ) ^ 2 * Real.logb p (c + 1)
        = ∑ k, (((α k : ℕ) : ℝ) / ((p : ℝ) - 1) - Real.logb p ((c : ℝ) + 1)) := by
          rw [Finset.sum_sub_distrib, ← Finset.sum_div, hsum]
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_sigma, Fintype.card_fin,
            smul_eq_mul, nsmul_eq_mul]
          push_cast
          ring
      _ ≤ ∑ k, (padicValNat p (α k).factorial : ℝ) := Finset.sum_le_sum (fun k _ => h1 k)
  constructor
  · set α0 : (Σ _ : Fin i, Fin i) →₀ ℕ := ∑ a : Fin i, Finsupp.single ⟨a, a⟩ c with hα0
    have hmem : α0 ∈ (detPow C i c).support := by
      rw [MvPolynomial.mem_support_iff, hdiag]
      exact one_ne_zero
    calc content v (detPow C i c) ≤ toE (v ((detPow C i c).coeff α0 * mfact α0)) := by
          unfold content
          exact iInf₂_le α0 hmem
      _ = (((∑ k, (padicValNat p (α0 k).factorial : ℝ)) : ℝ) : EReal) := by
          rw [hdiag, one_mul, val_mfact v hp hv α0, toE_coe]
      _ ≤ _ := EReal.coe_le_coe_iff.mpr (upS α0 hmem)
  · unfold content
    refine le_iInf₂ (fun α hα => ?_)
    obtain ⟨n, hn⟩ := hint α
    rw [← toE_coe]
    apply toE_mono
    rw [AddValuation.map_mul, val_mfact v hp hv α, hn]
    exact le_trans (WithTop.coe_le_coe.mpr (loS α hα))
      (le_add_of_nonneg_left (ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.intCast_nonneg v n))

end GlobalTheory.DetPowContent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerContentValuationDetPowBoundsStatement
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dividedPowerContentValuation_detPow_bounds : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ), p.Prime → v (p : C) = 1 → ∀ (i c : ℕ), content v (detPow C i c) ≤ (((i * c : ℝ) / (p - 1) : ℝ) : EReal) ∧ ((((i * c : ℝ) / (p - 1) - (i : ℝ) ^ 2 * Real.logb p (c + 1) : ℝ)) : EReal) ≤ content v (detPow C i c) := by
  first | exact @GlobalTheory.DetPowContent.content_detPow_bounds | exact GlobalTheory.DetPowContent.content_detPow_bounds | (intros; apply GlobalTheory.DetPowContent.content_detPow_bounds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentCechNerveLevelSpecTensorPower
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentCechNerveLevelSpecTensorPower
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

noncomputable section

namespace GlobalTheory.EtC.GmStep.LevelIso

theorem T_eq_unit_zpow (B : Type) [CommRing B] (m : ℤ) :
    (LaurentPolynomial.T m : LaurentPolynomial B) =
      ((laurentVarUnit B ^ m : (LaurentPolynomial B)ˣ) : LaurentPolynomial B) := by
  have h := laurentMap_T (RingHom.id B) m
  rw [laurentMap, LaurentPolynomial.eval₂_T] at h
  exact h.symm

theorem laurent_ringHom_ext {B R : Type} [CommRing B] [CommRing R] {φ ψ : LaurentPolynomial B →+* R}
    (hC : φ.comp LaurentPolynomial.C = ψ.comp LaurentPolynomial.C)
    (hT : φ (LaurentPolynomial.T 1) = ψ (LaurentPolynomial.T 1)) : φ = ψ := by
  have hu : Units.map φ.toMonoidHom (laurentVarUnit B) = Units.map ψ.toMonoidHom (laurentVarUnit B) :=
    Units.ext hT
  have e : ∀ (χ : LaurentPolynomial B →+* R) (m : ℤ),
      χ ((laurentVarUnit B ^ m : (LaurentPolynomial B)ˣ) : LaurentPolynomial B) =
        ((Units.map χ.toMonoidHom (laurentVarUnit B) ^ m : Rˣ) : R) := by
    intro χ m
    rw [← map_zpow]
    rfl
  have hTm : ∀ m : ℤ, φ (LaurentPolynomial.T m) = ψ (LaurentPolynomial.T m) := fun m => by
    rw [T_eq_unit_zpow, e φ, e ψ, hu]
  refine RingHom.ext fun p => ?_
  induction p using LaurentPolynomial.induction_on' with
  | add p r hp hr => rw [map_add (f := _), map_add (f := _), hp, hr]
  | C_mul_T n b => rw [map_mul, map_mul, hTm n, ← RingHom.comp_apply, hC, RingHom.comp_apply]

theorem laurentMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    (laurentMap g).comp (laurentMap f) = laurentMap (g.comp f) :=
  laurent_ringHom_ext (RingHom.ext fun a => by simp [laurentMap_C])
    (by rw [RingHom.comp_apply, laurentMap_T, laurentMap_T, laurentMap_T])

theorem tensorPow_univ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (k : ℕ) (R : Type) [CommRing R]
    (g : Fin (k + 1) → (B →+* R)) (hg : ∀ j, (g j).comp (algebraMap A B) = (g 0).comp (algebraMap A B)) :
    ∃! φ : PiTensorProduct A (fun _ : Fin (k + 1) => B) →+* R,
      ∀ j, φ.comp (PiTensorProduct.singleAlgHom (R := A) (A := fun _ : Fin (k + 1) => B) j).toRingHom = g j := by
  classical
  letI : Algebra A R := ((g 0).comp (algebraMap A B)).toAlgebra
  let g' : Fin (k + 1) → (B →ₐ[A] R) := fun j => ⟨g j, fun r => RingHom.congr_fun (hg j) r⟩
  refine ⟨(GlobalTheory.piTensorLift g').toRingHom, fun j => ?_, fun ψ hψ => ?_⟩
  · ext x
    exact GlobalTheory.piTensorLift_single g' j x
  · have hc : ∀ r : A, ψ (algebraMap A (PiTensorProduct A fun _ : Fin (k + 1) => B) r) = algebraMap A R r := by
      intro r
      have h1 : algebraMap A (PiTensorProduct A fun _ : Fin (k + 1) => B) r =
          PiTensorProduct.singleAlgHom (R := A) (A := fun _ : Fin (k + 1) => B) 0 (algebraMap A B r) :=
        ((PiTensorProduct.singleAlgHom (R := A) (A := fun _ : Fin (k + 1) => B) 0).commutes r).symm
      rw [h1]
      exact RingHom.congr_fun (hψ 0) (algebraMap A B r)
    let ψ' : PiTensorProduct A (fun _ : Fin (k + 1) => B) →ₐ[A] R := ⟨ψ, hc⟩
    have : ψ' = GlobalTheory.piTensorLift g' := PiTensorProduct.algHom_ext fun j => by
      ext x
      change ψ _ = _
      rw [AlgHom.comp_apply, GlobalTheory.piTensorLift_single]
      exact RingHom.congr_fun (hψ j) x
    exact congrArg AlgHom.toRingHom this

theorem laurent_univ (A B T : Type) [CommRing A] [CommRing B] [CommRing T] (a : A →+* B) (k : ℕ)
    (ι : Fin (k + 1) → (B →+* T))
    (hu : ∀ (R : Type) [CommRing R] (g : Fin (k + 1) → (B →+* R)), (∀ j, (g j).comp a = (g 0).comp a) →
      ∃! φ : T →+* R, ∀ j, φ.comp (ι j) = g j)
    (R : Type) [CommRing R] (g : Fin (k + 1) → (LaurentPolynomial B →+* R))
    (hg : ∀ j, (g j).comp (laurentMap a) = (g 0).comp (laurentMap a)) :
    ∃! φ : LaurentPolynomial T →+* R, ∀ j, φ.comp (laurentMap (ι j)) = g j := by
  have hT : ∀ j, g j (LaurentPolynomial.T 1) = g 0 (LaurentPolynomial.T 1) := fun j => by
    have := RingHom.congr_fun (hg j) (LaurentPolynomial.T 1)
    rwa [RingHom.comp_apply, RingHom.comp_apply, laurentMap_T] at this
  obtain ⟨ψ, hψ, hψu⟩ := hu R (fun j => (g j).comp LaurentPolynomial.C) (fun j => by
    refine RingHom.ext fun x => ?_
    have := RingHom.congr_fun (hg j) (LaurentPolynomial.C x)
    simpa [laurentMap_C] using this)
  let u : Rˣ := Units.map (g 0).toMonoidHom (laurentVarUnit B)
  refine ⟨LaurentPolynomial.eval₂ ψ u, fun j => ?_, fun φ hφ => ?_⟩
  · apply laurent_ringHom_ext
    · refine RingHom.ext fun b => ?_
      rw [RingHom.comp_apply, RingHom.comp_apply, laurentMap_C, LaurentPolynomial.eval₂_C]
      exact RingHom.congr_fun (hψ j) b
    · rw [RingHom.comp_apply, laurentMap_T, LaurentPolynomial.eval₂_T, zpow_one, hT j]
      rfl
  · have hC : φ.comp LaurentPolynomial.C = ψ := hψu _ (fun j => by
      refine RingHom.ext fun b => ?_
      have := RingHom.congr_fun (hφ j) (LaurentPolynomial.C b)
      simpa [laurentMap_C] using this)
    apply laurent_ringHom_ext
    · refine RingHom.ext fun t => ?_
      rw [RingHom.comp_apply, RingHom.comp_apply, LaurentPolynomial.eval₂_C, ← hC]
      rfl
    · rw [LaurentPolynomial.eval₂_T, zpow_one]
      have := RingHom.congr_fun (hφ 0) (LaurentPolynomial.T 1)
      rw [RingHom.comp_apply, laurentMap_T] at this
      rw [this]
      rfl

end GlobalTheory.EtC.GmStep.LevelIso

namespace GlobalTheory.EtC.GmStep.LevelIso

theorem level_iso : ∀ (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (k : ℕ),
  ∃ (e0 : yoneda.obj (Spec (CommRingCat.of (PiTensorProduct A (fun _ : Fin (k + 1) => A')))) ≅ (cech (baseHom A A')).obj (op ⦋k⦌))
    (e : yoneda.obj (Spec (CommRingCat.of (LaurentPolynomial (PiTensorProduct A (fun _ : Fin (k + 1) => A'))))) ≅
      (cech (laurentHom A A')).obj (op ⦋k⦌)),
    e.hom ≫ (cechC A A').app (op ⦋k⦌) =
      yoneda.map (Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : PiTensorProduct A (fun _ : Fin (k + 1) => A') →+*
        LaurentPolynomial (PiTensorProduct A (fun _ : Fin (k + 1) => A'))))) ≫ e0.hom ∧
    e.hom ≫ (cechAug (laurentHom A A')).app (op ⦋k⦌) =
      yoneda.map (Spec.map (CommRingCat.ofHom (GmStep.laurentMap (algebraMap A (PiTensorProduct A (fun _ : Fin (k + 1) => A')))))) := by
  intro A A' _ _ _ k
  let ι : Fin (k + 1) → (A' →+* PiTensorProduct A (fun _ : Fin (k + 1) => A')) := fun j =>
    (PiTensorProduct.singleAlgHom (R := A) (A := fun _ : Fin (k + 1) => A') j).toRingHom
  have hιA : ∀ j, (ι j).comp (algebraMap A A') = algebraMap A (PiTensorProduct A (fun _ : Fin (k + 1) => A')) :=
    fun j => RingHom.ext fun x => (PiTensorProduct.singleAlgHom (R := A) (A := fun _ : Fin (k + 1) => A') j).commutes x
  have hι : ∀ j, (ι j).comp (algebraMap A A') = (ι 0).comp (algebraMap A A') := fun j => by rw [hιA, hιA]
  have hu := tensorPow_univ A A' k
  obtain ⟨e0, he0⟩ := GlobalTheory.SpecWidePullback.yoneda_spec_isoWidePullback A A' _ (algebraMap A A') k ι hι hu
  have hι' : ∀ j, (laurentMap (ι j)).comp (laurentMap (algebraMap A A')) =
      (laurentMap (ι 0)).comp (laurentMap (algebraMap A A')) := by
    intro j; rw [laurentMap_comp, laurentMap_comp, hι j]
  obtain ⟨e, he⟩ := GlobalTheory.SpecWidePullback.yoneda_spec_isoWidePullback (LaurentPolynomial A) (LaurentPolynomial A')
    (LaurentPolynomial (PiTensorProduct A (fun _ : Fin (k + 1) => A'))) (laurentMap (algebraMap A A')) k
    (fun j => laurentMap (ι j)) hι' (laurent_univ A A' _ (algebraMap A A') k ι (fun R _ g hg => hu R g hg))
  refine ⟨e0, e, ?_, ?_⟩
  · change e.hom ≫ WidePullback.lift _ _ _ = _
    apply WidePullback.hom_ext
    · intro j
      simp only [Category.assoc, WidePullback.lift_π, Arrow.mk_hom, laurentHom, baseHom]
      refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (he j)).trans ?_)
      refine Eq.trans ?_ (congrArg (_ ≫ ·) (he0 j)).symm
      simp only [constSq, Arrow.homMk_left, ← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        laurentMap_comp_C]
    · simp only [Category.assoc, WidePullback.lift_base, Arrow.mk_hom, laurentHom, baseHom]
      rw [← WidePullback.π_arrow _ 0]
      simp only [Category.assoc]
      refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (he 0)).trans ?_)
      refine Eq.trans ?_ ((congrArg (_ ≫ ·) (((congrArg (· ≫ yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A A')))) (he0 0)).symm.trans (Category.assoc _ _ _)).trans (congrArg (e0.hom ≫ ·) (WidePullback.π_arrow _ 0)))).trans (Category.assoc _ _ _).symm)
      simp only [constSq, Arrow.homMk_right, ← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        laurentMap_comp_C]
      congr 3
      exact RingHom.ext fun x => by simp [laurentMap_C]
  · change e.hom ≫ WidePullback.base _ = _
    rw [← WidePullback.π_arrow _ 0, ← Category.assoc, he 0]
    simp only [laurentHom, ← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, laurentMap_comp, hιA 0]

end GlobalTheory.EtC.GmStep.LevelIso
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentCechNerveLevelSpecTensorPowerStatement
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laurentCechNerve_level_spec_tensorPower : ∀ (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (k : ℕ),
  ∃ (e0 : yoneda.obj (Spec (CommRingCat.of (PiTensorProduct A (fun _ : Fin (k + 1) => A')))) ≅ (cech (baseHom A A')).obj (op ⦋k⦌))
    (e : yoneda.obj (Spec (CommRingCat.of (LaurentPolynomial (PiTensorProduct A (fun _ : Fin (k + 1) => A'))))) ≅
      (cech (laurentHom A A')).obj (op ⦋k⦌)),
    e.hom ≫ (cechC A A').app (op ⦋k⦌) =
      yoneda.map (Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : PiTensorProduct A (fun _ : Fin (k + 1) => A') →+*
        LaurentPolynomial (PiTensorProduct A (fun _ : Fin (k + 1) => A'))))) ≫ e0.hom ∧
    e.hom ≫ (cechAug (laurentHom A A')).app (op ⦋k⦌) =
      yoneda.map (Spec.map (CommRingCat.ofHom (GmStep.laurentMap (algebraMap A (PiTensorProduct A (fun _ : Fin (k + 1) => A')))))) := by
  first | (exact @GlobalTheory.EtC.GmStep.LevelIso.level_iso) | (exact GlobalTheory.EtC.GmStep.LevelIso.level_iso) | (intros; apply GlobalTheory.EtC.GmStep.LevelIso.level_iso  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonHypercohomologyOfLocallyExactOnSuppo
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonHypercohomologyOfLocallyExactOnSuppo
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.SuppAcyc

variable {R : Type} [CommRing R]

theorem map_comp {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (a : Sec F U) :
    Sec.map (φ ≫ ψ) a = Sec.map ψ (Sec.map φ a) := rfl

theorem map_zero' {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} : Sec.map φ (0 : Sec F U) = 0 :=
  map_zero (φ.hom.app (op U)).hom

theorem res_zero' {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) : Sec.res g (0 : Sec F U) = 0 :=
  map_zero (F.obj.map g.op).hom

theorem cpush_zero (K I J : Cx R) (n : ℤ) (x : CohomologyClass K I n) : cpush K (0 : I ⟶ J) n x = 0 := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  rw [cpush, cpost_mk]
  have : zcomp x (Cocycle.ofHom (0 : I ⟶ J)) (add_zero n) = 0 := Cocycle.ext (by simp [zcomp])
  rw [this]
  exact CohomologyClass.mk_zero _ _ _

theorem delta_comp_ofHom {K I J : Cx R} {n : ℤ} (a : Cochain K I n) (f : I ⟶ J) :
    δ n (n + 1) (a.comp (Cochain.ofHom f) (add_zero n)) = (δ n (n + 1) a).comp (Cochain.ofHom f) (add_zero _) := by
  rw [δ_comp _ _ (add_zero n) (n + 1) 1 (n + 1) rfl rfl (zero_add 1)]
  simp

end GlobalTheory.EtC.SuppAcyc


open GlobalTheory.EtC.SuppAcyc in
theorem GlobalTheory.EtC.subsingleton_of_locExact_supp : ∀ (R : Type) [CommRing R] (E : Spc) (C : Cx R) [C.IsKInjective], (∀ (U : Scheme.{0}), Nonempty (Sx E 0 U) → ∀ (n : ℤ) (b : Sec (C.X n) U), Sec.map (C.d n (n + 1)) b = 0 → Loc U fun V g => ∃ a : Sec (C.X (n - 1)) V, Sec.map (C.d (n - 1) n) a = Sec.res g b) → ∀ n, Subsingleton (CohomologyClass ((chains R).obj E) C n) := by
  intro R _ E C _ hC n
  let Z : Scheme.{0} → Prop := fun U => Nonempty (Sx E 0 U)
  have hZ : ∀ (V U : Scheme.{0}) (_ : V ⟶ U), Z U → Z V := fun V U g ⟨x⟩ => ⟨Sx.res g x⟩
  obtain ⟨D, ι, hinj, hchar⟩ := SuppSub.exists_supp_sub R C Z hZ
  obtain ⟨ltop, lmono, -, -, ltrans, -, -⟩ := GlobalTheory.EtC.loc_calculus
  have hin : ∀ k U (a : Sec (C.X k) U), Z U → ∃ b, Sec.map (ι.f k) b = a := fun k U a hU =>
    (hchar k U a).2 (ltop _ _ fun V g => Or.inl (hZ V U g hU))

  have hD : D.Acyclic := by
    intro k
    rw [HomologicalComplex.exactAt_iff' D (k - 1) k (k + 1) (by simp) (by simp), GlobalTheory.T.etaleSheaf_shortComplex_exact_iff_locally]
    intro U (b : Sec (D.X k) U) hb
    change Sec.map (D.d k (k + 1)) b = 0 at hb
    have hc : Sec.map (C.d k (k + 1)) (Sec.map (ι.f k) b) = 0 := by
      rw [← map_comp, ι.comm, map_comp, hb, map_zero']
    have hloc := (hchar k U (Sec.map (ι.f k) b)).1 ⟨b, rfl⟩
    refine ltrans _ _ (lmono _ _ _ hloc fun V g hg => ?_)
    rcases hg with hV | h0
    · have hc' : Sec.map (C.d k (k + 1)) (Sec.res g (Sec.map (ι.f k) b)) = 0 := by
        have := congrArg (Sec.res g) hc
        rwa [SuppSub.res_map, res_zero'] at this
      refine lmono _ _ _ (hC V hV k _ hc') fun W h => ?_
      rintro ⟨a, ha⟩
      obtain ⟨a', rfl⟩ := hin (k - 1) W a (hZ W V h hV)
      refine ⟨a', hinj k W ?_⟩
      change Sec.map (ι.f k) (Sec.map (D.d (k - 1) k) a') = Sec.map (ι.f k) (Sec.res (h ≫ g) b)
      rw [← map_comp, ← ι.comm, map_comp, ha, SuppSub.res_comp, SuppSub.res_map, SuppSub.res_map]
    · have h0' : Sec.res g b = 0 := hinj k V (by rw [← SuppSub.res_map, h0, map_zero'])
      refine ltop _ _ fun W h => ⟨0, ?_⟩
      change Sec.map (D.d (k - 1) k) 0 = Sec.res (h ≫ g) b
      rw [map_zero', SuppSub.res_comp, h0', res_zero']
  have hnull : Nonempty (Homotopy ι 0) := IsKInjective.nonempty_homotopy_zero ι hD
  have hpush : cpush ((chains R).obj E) ι n = cpush _ (0 : D ⟶ C) n :=
    ((GlobalTheory.EtC.ZcFun.main R).2.2.2.2 ι 0 hnull ((chains R).obj E) n).2
  have hbasic :
      ∀ {I : Cx R} {n : ℤ},
      (∀ (α β : Cochain ((chains R).obj E) I n) p s h U x,
        ev (α + β) p s h U x = ev α p s h U x + ev β p s h U x ∧
        ev (α - β) p s h U x = ev α p s h U x - ev β p s h U x ∧
        ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 ∧
        ∀ c : ℤ, ev (c • α) p s h U x = c • ev α p s h U x) ∧
      (∀ (α : Cochain ((chains R).obj E) I n) p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U),
        Sec.res g (ev α p s h U x) = ev α p s h V (x.res g)) ∧
      (∀ α β : Cochain ((chains R).obj E) I n,
        (∀ p s h U x, ev α p s h U x = ev β p s h U x) → α = β) ∧
      (∀ {E' : Spc} (f : E' ⟶ E) (α : Cochain ((chains R).obj E) I n) p s h U (x : Sx E' p U),
        ev ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x = ev α p s h U (x.map f)) ∧
      ∀ {J : Cx R} (m : I ⟶ J) (α : Cochain ((chains R).obj E) I n) p s h U x,
        ev (α.comp (Cochain.ofHom m) (add_zero n)) p s h U x = Sec.map (m.f s) (ev α p s h U x) := by
    intro I n
    have ev_eq {F : Spc} {J : Cx R} (α : Cochain ((chains R).obj F) J n)
        (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx F p U) :
        ev α p s h U x = Sec.map ((chainsXIso R F p).inv ≫ α.v _ _ h) (freeGen R _ U x) := rfl
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro α β p s h U x
      have hadd (a b : Cochain ((chains R).obj E) I n) :
          ev (a + b) p s h U x = ev a p s h U x + ev b p s h U x := by
        simp [ev, Cochain.add_v]
      let eval : Cochain ((chains R).obj E) I n →+ Sec (I.X s) U :=
        AddMonoidHom.mk' (fun a => ev a p s h U x) hadd
      exact ⟨hadd α β, map_sub eval α β, map_zero eval, fun c => map_zsmul eval c α⟩
    · intro α p s h V U g x
      rw [ev_eq, CupSpec.map_res, CupSpec.freeGen_res]
      rfl
    · intro α β H
      ext p s hs : 1
      by_cases hp : p ≤ 0
      · obtain ⟨k, rfl⟩ : ∃ k : ℕ, p = -(k : ℤ) := ⟨(-p).toNat, by omega⟩
        rw [← cancel_epi (chainsXIso R E k).inv]
        exact CupSpec.free_ext _ _ (fun U x => H k s hs U x)
      · exact (CupSpec.isZero_chains E p (by omega)).eq_of_src _ _
    · intro E' f α p s h U x
      rw [ev_eq, ev_eq, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
        ← Category.assoc, CupSpec.chains_map, Category.assoc]
      change Sec.map ((chainsXIso R E p).inv ≫ α.v _ _ h)
        (Sec.map ((free R).map _) (freeGen R _ U x)) = _
      rw [CupSpec.freeGen_map]
      rfl
    · intro J m α p s h U x
      rw [ev_eq, ev_eq, Cochain.comp_zero_cochain_v, Cochain.ofHom_v,
        ← Category.assoc]
      rfl
  obtain ⟨-, hnat, hdet, -, -⟩ := hbasic (I := C) (n := n)
  obtain ⟨-, -, -, -, hpost⟩ := hbasic (I := D) (n := n)
  obtain ⟨haddD1, -, hdetD, -, hpost1⟩ := hbasic (I := D) (n := n + 1)
  obtain ⟨haddC1, -, -, -, -⟩ := hbasic (I := C) (n := n + 1)
  have hzero : ∀ c : CohomologyClass ((chains R).obj E) C n, c = 0 := by
    intro c
    obtain ⟨α, rfl⟩ := c.mk_surjective

    have hv : ∀ (p : ℕ) (U : Scheme.{0}), Sx E p U → Z U := fun p U x =>
      ⟨Sx.along x (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk p) 0)⟩
    let v : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (D.X s) U :=
      fun p s h U x => Classical.choose (hin s U (ev α.1 p s h U x) (hv p U x))
    have hvspec : ∀ p s h U x, Sec.map (ι.f s) (v p s h U x) = ev α.1 p s h U x :=
      fun p s h U x => Classical.choose_spec (hin s U (ev α.1 p s h U x) (hv p U x))
    have hvnat : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (v p s h U x) = v p s h V (x.res g) := by
      intro p s h V U g x
      apply hinj s V
      rw [← SuppSub.res_map, hvspec, hvspec, (hnat α.1 p s h V U g x)]
    have hex : ∃ α : Cochain ((chains R).obj E) D n, ∀ p s h U x, ev α p s h U x = v p s h U x := by
      have components : ∀ (i j : ℤ) (hij : i + n = j), ∃ φ : ((chains R).obj E).X i ⟶ D.X j,
          ∀ (p : ℕ) (hp : i = -(p : ℤ)) U x,
            Sec.map ((chainsXIso R E p).inv ≫ eqToHom (congrArg ((chains R).obj E).X hp.symm) ≫ φ)
              (freeGen R _ U x) = v p j (hp ▸ hij) U x := by
        intro i j hij
        by_cases hi : i ≤ 0
        · obtain ⟨k, rfl⟩ : ∃ k : ℕ, i = -(k : ℤ) := ⟨(-i).toNat, by omega⟩
          obtain ⟨φ, hφ⟩ := CupSpec.free_exists (R := R) _ _ (v k j hij) (hvnat k j hij)
          refine ⟨(chainsXIso R E k).hom ≫ φ, fun p hp U x => ?_⟩
          obtain rfl : k = p := by omega
          rw [eqToHom_refl, Category.id_comp, Iso.inv_hom_id_assoc]
          exact hφ U x
        · exact ⟨0, fun p hp => by omega⟩
      choose φ hφ using components
      refine ⟨Cochain.mk φ, fun p s h U x => ?_⟩
      have hEval := hφ _ _ h p rfl U x
      rw [eqToHom_refl, Category.id_comp] at hEval
      exact hEval
    obtain ⟨α', hα'⟩ := hex
    have hcomp : α'.comp (Cochain.ofHom ι) (add_zero n) = α.1 := by
      apply hdet
      intro p s h U x
      rw [hpost, hα', hvspec]
    have hcoc : δ n (n + 1) α' = 0 := by
      apply hdetD
      intro p s h U x
      apply hinj s U
      rw [← hpost1, ← delta_comp_ofHom, hcomp, (Cocycle.mem_iff n (n + 1) rfl α.1).1 α.2, (haddC1 0 0 p s h U x).2.2.1,
        (haddD1 0 0 p s h U x).2.2.1, map_zero']
    let β : Cocycle ((chains R).obj E) D n := Cocycle.mk α' (n + 1) rfl hcoc
    have hαβ : α = zcomp β (Cocycle.ofHom ι) (add_zero n) := Cocycle.ext hcomp.symm
    rw [hαβ, ← cpost_mk, ← cpush, hpush, cpush_zero]
  exact ⟨fun a b => (hzero a).trans (hzero b).symm⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonHypercohomologyOfLocallyExactOnSuppoStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subsingleton_hypercohomology_of_locallyExact_on_support : ∀ (R : Type) [CommRing R] (E : Spc) (C : Cx R) [C.IsKInjective], (∀ (U : Scheme.{0}), Nonempty (Sx E 0 U) → ∀ (n : ℤ) (b : Sec (C.X n) U), Sec.map (C.d n (n + 1)) b = 0 → Loc U fun V g => ∃ a : Sec (C.X (n - 1)) V, Sec.map (C.d (n - 1) n) a = Sec.res g b) → ∀ n, Subsingleton (CohomologyClass ((chains R).obj E) C n) := by
  first | (exact @GlobalTheory.EtC.subsingleton_of_locExact_supp) | (exact GlobalTheory.EtC.subsingleton_of_locExact_supp) | (intros; apply GlobalTheory.EtC.subsingleton_of_locExact_supp  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.Pull1RestrictSurjectiveOfComma
open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

namespace GlobalTheory.CatCoh

theorem pull1_restrict_surjective_of_comma : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), (∀ (T : C) (x : F.obj T), (∀ t (u : T ⟶ G.obj t), mp F u x = 0) → x = 0) → (∀ (T : C) (s : ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t)), (∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), s t' (u ≫ G.map a) = mp F (G.map a) (s t u)) → ∃ x : F.obj T, ∀ t u, mp F u x = s t u) → (∀ (T : C) (y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → F.obj (G.obj t')), (∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), y t t'' u (a ≫ b) = mp F (G.map b) (y t t' u a) + y t' t'' (u ≫ G.map a) b) → ∃ g : ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t), ∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), g t' (u ≫ G.map a) - mp F (G.map a) (g t u) = y t t' u a) → Function.Surjective (CoefMap.restrict F G).pull1 := by
  intro R _ C _ C' _ F G hsep hglue hvan c
  obtain ⟨y, rfl⟩ := H1.mk_surjective _ c
  have hb : ∀ T : C, ∃ b : ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t), ∀ t t' (u : T ⟶ G.obj t)
      (a : t ⟶ t'), b t' (u ≫ G.map a) - mp F (G.map a) (b t u) = y.1 t t' a := fun T ↦
    hvan T (fun t t' _ a ↦ y.1 t t' a) fun t t' t'' _ a a' ↦ Z1.comp y a a'
  choose b hb using hb
  have hx : ∀ T T' (φ : T ⟶ T'), ∃ x : F.obj T', ∀ t u, mp F u x = b T t (φ ≫ u) - b T' t u := by
    intro T T' φ
    refine hglue T' _ fun t t' u a ↦ ?_
    have k1 := hb T t t' (φ ≫ u) a
    have k2 := hb T' t t' u a
    rw [Category.assoc] at k1
    rw [map_sub]
    linear_combination k1 - k2
  choose x hx using hx
  have hxc : x ∈ Z1 F := fun T T' T'' φ ψ ↦ sub_eq_zero.1 (hsep T'' _ fun t u ↦ by
    have k1 := hx T T'' (φ ≫ ψ) t u
    have k2 := hx T T' φ t (ψ ≫ u)
    have k3 := hx T' T'' ψ t u
    rw [mp_comp] at k2
    simp only [map_sub, map_add (f := _), Category.assoc] at k1 k2 ⊢
    linear_combination k1 - k2 - k3)
  refine ⟨H1.mk F ⟨x, hxc⟩, ?_⟩
  rw [CoefMap.pullCohomologyOne_class, H1.mk_eq_mk]
  refine ⟨fun t ↦ -b (G.obj t) t (𝟙 _), ?_⟩
  funext t t' a
  have k1 := hx _ _ (G.map a) t' (𝟙 _)
  have k2 := hb (G.obj t) t t' (𝟙 _) a
  rw [mp_id, Category.comp_id] at k1
  rw [Category.id_comp] at k2
  show -b _ t' (𝟙 _) - mp F (G.map a) (-b _ t (𝟙 _)) = x _ _ (G.map a) - (show F.obj (G.obj t') from y.1 t t' a)
  rw [map_neg]
  linear_combination -k1 - k2

end GlobalTheory.CatCoh
end
