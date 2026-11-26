module

public import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomOfBigCellGenericRelations
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InverseUnipotentVolumeConjDiagonalUnitsGLMul

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussianFirstCoordsMeasurePreserving
open MeasureTheory Set MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.SphereMeanDrop

noncomputable section

namespace GlobalTheory.GaussMarginal

open Real

theorem lintegral_pi_fin {E : Type*} [MeasurableSpace E] (n : ℕ) (μ : Measure E) [SigmaFinite μ]
    (f : Fin n → E → ENNReal) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : Fin n → E, ∏ i, f i (x i) ∂(Measure.pi fun _ => μ) = ∏ i, ∫⁻ t, f i t ∂μ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).symm
    rw [← h.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _), Fin.prod_univ_succ,
      ← ih (fun i => f i.succ) (fun i => hf _), ← lintegral_prod_mul (hf 0).aemeasurable
        (Finset.measurable_prod _ fun i _ => (hf i.succ).comp (measurable_pi_apply i)).aemeasurable]
    refine lintegral_congr fun q => ?_
    simp [Fin.prod_univ_succ, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]

theorem lintegral_pi_prod {ι E : Type*} [Fintype ι] [MeasurableSpace E] (μ : Measure E) [SigmaFinite μ]
    (f : ι → E → ENNReal) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : ι → E, ∏ i, f i (x i) ∂(Measure.pi fun _ => μ) = ∏ i, ∫⁻ t, f i t ∂μ := by
  let e := (Fintype.equivFin ι).symm
  have h := measurePreserving_piCongrLeft (fun _ : ι => μ) e
  rw [← h.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _), ← e.prod_comp,
    ← lintegral_pi_fin _ μ (fun i => f (e i)) (fun i => hf _)]
  refine lintegral_congr fun q => ?_
  rw [← e.prod_comp]
  simp [MeasurableEquiv.coe_piCongrLeft]

theorem pi_withDensity_const {ι E : Type*} [Fintype ι] [MeasurableSpace E] (μ : Measure E)
    [SigmaFinite μ] (f : E → ENNReal) (hf : Measurable f) [SigmaFinite (μ.withDensity f)] :
    (Measure.pi fun _ : ι => μ.withDensity f) =
      (Measure.pi fun _ : ι => μ).withDensity fun x => ∏ i, f (x i) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  simp_rw [withDensity_apply _ (hs _), ← lintegral_indicator (hs _)]
  rw [← lintegral_pi_prod μ (fun i => (s i).indicator f) (fun i => hf.indicator (hs i))]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ Set.univ.pi s
  · rw [Set.indicator_of_mem hx]
    exact Finset.prod_congr rfl fun i _ => (Set.indicator_of_mem (hx i trivial) _).symm
  · rw [Set.indicator_of_notMem hx]
    obtain ⟨i, hi⟩ : ∃ i, x i ∉ s i := by simpa [Set.mem_pi] using hx
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm

theorem isProbabilityMeasure_complexGaussian_one :
    IsProbabilityMeasure (GlobalTheory.complexGaussian ℂ 1) :=
  GlobalTheory.isProbabilityMeasure_complexGaussian (by simp [Complex.finrank_real_complex])

theorem gaussProb_eq_complexGaussian (k : ℕ) :
    gaussProb k = GlobalTheory.complexGaussian (EuclideanSpace ℂ (Fin k)) k := by
  have hP := GlobalTheory.isProbabilityMeasure_complexGaussian (E := EuclideanSpace ℂ (Fin k)) (g := k)
    (by rw [GlobalTheory.finrank_real_euclideanSpace_complex, Fintype.card_fin])
  set ν := (volume : Measure (EuclideanSpace ℂ (Fin k))).withDensity
    fun x => ENNReal.ofReal (Real.exp (-‖x‖ ^ 2)) with hν
  have hm : Measurable fun x : EuclideanSpace ℂ (Fin k) => ENNReal.ofReal (Real.exp (-‖x‖ ^ 2)) := by
    fun_prop
  have hc : GlobalTheory.complexGaussian (EuclideanSpace ℂ (Fin k)) k = ENNReal.ofReal ((π ^ k)⁻¹) • ν := by
    ext s hs
    rw [Measure.smul_apply, GlobalTheory.complexGaussian, withDensity_apply _ hs, hν, withDensity_apply _ hs,
      smul_eq_mul, ← lintegral_const_mul _ hm]
    refine lintegral_congr fun x => ?_
    rw [ENNReal.ofReal_mul (by positivity)]
  have h1 := hP.measure_univ
  rw [hc, Measure.smul_apply, smul_eq_mul] at h1
  rw [gaussProb, ProbabilityTheory.cond, Measure.restrict_univ, hc, ← hν,
    ← ENNReal.eq_inv_of_mul_eq_one_left h1]

theorem map_ofLp_gaussProb (k : ℕ) :
    (gaussProb k).map (WithLp.ofLp (p := 2) (V := Fin k → ℂ)) =
      Measure.pi fun _ : Fin k => GlobalTheory.complexGaussian ℂ 1 := by
  haveI := isProbabilityMeasure_complexGaussian_one
  have hmp := GlobalTheory.volume_preserving_ofLp_complex (Fin k)
  set f1 : ℂ → ENNReal := fun z => ENNReal.ofReal ((π ^ 1)⁻¹ * Real.exp (-‖z‖ ^ 2)) with hf1
  have hf1m : Measurable f1 := by fun_prop
  haveI : SigmaFinite ((volume : Measure ℂ).withDensity f1) :=
    inferInstanceAs (SigmaFinite (GlobalTheory.complexGaussian ℂ 1))
  have hG : Measurable fun y : Fin k → ℂ => ∏ i, f1 (y i) := by fun_prop
  ext s hs
  rw [Measure.map_apply hmp.measurable hs, gaussProb_eq_complexGaussian, GlobalTheory.complexGaussian,
    withDensity_apply _ (hmp.measurable hs), show GlobalTheory.complexGaussian ℂ 1 = (volume : Measure ℂ).withDensity f1 from rfl,
    pi_withDensity_const _ f1 hf1m, ← volume_pi, withDensity_apply _ hs,
    ← hmp.setLIntegral_comp_preimage hs hG]
  refine lintegral_congr fun x => ?_
  simp only [hf1]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity), Finset.prod_mul_distrib,
    ← Real.exp_sum, Finset.prod_const, Finset.card_univ, Fintype.card_fin, EuclideanSpace.norm_sq_eq,
    ← Finset.sum_neg_distrib, pow_one, inv_pow]

theorem measurePreserving_restrict_castLE {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] {N n : ℕ} (h : N ≤ n) :
    MeasurePreserving (fun (y : Fin n → α) (j : Fin N) => y (Fin.castLE h j))
      (Measure.pi fun _ => μ) (Measure.pi fun _ => μ) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  have hr : Measurable fun (y : Fin (N + m) → α) (j : Fin N) => y (Fin.castLE h j) :=
    Measurable.of_eval fun j => measurable_pi_apply _
  refine ⟨hr, (Measure.pi_eq fun s hs => ?_).symm⟩
  rw [Measure.map_apply hr (MeasurableSet.univ_pi hs)]
  have hpre : (fun (y : Fin (N + m) → α) (j : Fin N) => y (Fin.castLE h j)) ⁻¹' univ.pi s =
      univ.pi (Fin.append s fun _ : Fin m => (univ : Set α)) := by
    ext y
    simp only [mem_preimage, mem_univ_pi]
    constructor
    · intro hy i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · rw [Fin.append_left]; exact hy j
      · rw [Fin.append_right]; exact mem_univ _
    · intro hy j
      have := hy (Fin.castAdd m j)
      rwa [Fin.append_left] at this
  rw [hpre, Measure.pi_pi, Fin.prod_univ_add]
  simp [Fin.append_left, Fin.append_right]

theorem measurePreserving_firstCoords_gaussProb :
    ∀ (N n : ℕ) (h : N ≤ n), MeasurePreserving (firstCoords h) (gaussProb n) (gaussProb N) := by
  intro N n h
  haveI := isProbabilityMeasure_complexGaussian_one
  have hofn : Measurable (WithLp.ofLp (p := 2) (V := Fin n → ℂ)) :=
    (GlobalTheory.volume_preserving_ofLp_complex (Fin n)).measurable
  have hofN : Measurable (WithLp.ofLp (p := 2) (V := Fin N → ℂ)) :=
    (GlobalTheory.volume_preserving_ofLp_complex (Fin N)).measurable
  have htoN : Measurable (WithLp.toLp 2 : (Fin N → ℂ) → EuclideanSpace ℂ (Fin N)) := by fun_prop
  have e1 : MeasurePreserving (WithLp.ofLp (p := 2) (V := Fin n → ℂ)) (gaussProb n)
      (Measure.pi fun _ : Fin n => GlobalTheory.complexGaussian ℂ 1) := ⟨hofn, map_ofLp_gaussProb n⟩
  have e3 : MeasurePreserving (WithLp.toLp 2 : (Fin N → ℂ) → EuclideanSpace ℂ (Fin N))
      (Measure.pi fun _ : Fin N => GlobalTheory.complexGaussian ℂ 1) (gaussProb N) := by
    refine ⟨htoN, ?_⟩
    rw [← map_ofLp_gaussProb N, Measure.map_map htoN hofN]
    convert Measure.map_id
    funext x
    rfl
  exact e3.comp ((measurePreserving_restrict_castLE _ h).comp e1)

end GlobalTheory.GaussMarginal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSuppSub
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.SuppSub

variable {R : Type} [CommRing R] (Z : Scheme.{0} → Prop) (hZ : ∀ (V U : Scheme.{0}) (_ : V ⟶ U), Z U → Z V)

theorem res_comp {F : Shv R} {W V U : Scheme.{0}} (f : W ⟶ V) (g : V ⟶ U) (a : Sec F U) :
    Sec.res (f ≫ g) a = Sec.res f (Sec.res g a) := by
  change (F.obj.map (f ≫ g).op).hom a = _
  rw [op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

def sv {F : Shv R} {U : Scheme.{0}} (a : Sec F U) : Sieve U where
  arrows V g := Z V ∨ Sec.res g a = 0
  downward_closed {V W} g hg f := by
    rcases hg with h | h
    · exact Or.inl (hZ _ _ f h)
    · right
      rw [res_comp, h]; exact map_zero (F.obj.map f.op).hom

theorem loc_iff {F : Shv R} {U : Scheme.{0}} (a : Sec F U) :
    (Loc U fun V g => Z V ∨ Sec.res g a = 0) ↔ sv Z hZ a ∈ Scheme.etaleTopology U := by
  constructor
  · rintro ⟨S, hS, h⟩
    exact GrothendieckTopology.superset_covering _ (fun V g hg => h V g hg) hS
  · intro h
    exact ⟨_, h, fun V g hg => hg⟩

def supp (F : Shv R) (U : Scheme.{0}) : Submodule (ULift.{1} R) (Sec F U) where
  carrier := {a | sv Z hZ a ∈ Scheme.etaleTopology U}
  zero_mem' := by
    change sv Z hZ (0 : Sec F U) ∈ Scheme.etaleTopology U
    refine Scheme.etaleTopology.superset_covering ?_ (Scheme.etaleTopology.top_mem U)
    intro V g _
    exact Or.inr (map_zero (F.obj.map g.op).hom)
  add_mem' {a b} ha hb := by
    change sv Z hZ a ∈ Scheme.etaleTopology U at ha
    change sv Z hZ b ∈ Scheme.etaleTopology U at hb
    change sv Z hZ (a + b) ∈ Scheme.etaleTopology U
    refine Scheme.etaleTopology.superset_covering ?_ (Scheme.etaleTopology.intersection_covering ha hb)
    intro V g hg
    rcases hg.1 with h | h
    · exact Or.inl h
    rcases hg.2 with h' | h'
    · exact Or.inl h'
    · right; change (F.obj.map g.op).hom (a + b) = 0; rw [map_add (f := _)]; exact (congrArg₂ (· + ·) h h').trans (add_zero 0)
  smul_mem' c a ha := by
    change sv Z hZ a ∈ Scheme.etaleTopology U at ha
    change sv Z hZ (c • a) ∈ Scheme.etaleTopology U
    refine Scheme.etaleTopology.superset_covering ?_ ha
    intro V g hg
    rcases hg with h | h
    · exact Or.inl h
    · right; change (F.obj.map g.op).hom (c • a) = 0; rw [map_smul]; exact (congrArg (c • ·) h).trans (smul_zero c)

theorem supp_res {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) {a : Sec F U} (ha : a ∈ supp Z hZ F U) :
    Sec.res g a ∈ supp Z hZ F V := by
  refine GrothendieckTopology.superset_covering _ (fun W f hf => ?_) (Scheme.etaleTopology.pullback_stable g (show sv Z hZ a ∈ Scheme.etaleTopology U from ha))
  change Z W ∨ Sec.res (f ≫ g) a = 0 at hf
  rw [res_comp] at hf
  exact hf

def suppP (F : Shv R) : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R) where
  obj U := ModuleCat.of _ (supp Z hZ F U.unop)
  map {U V} g := ModuleCat.ofHom ((F.obj.map g).hom.restrict (fun a ha => supp_res Z hZ g.unop ha))
  map_id U := by
    ext ⟨a, ha⟩
    change (F.obj.map (𝟙 U)).hom a = a
    rw [F.obj.map_id]; rfl
  map_comp {U V W} f g := by
    ext ⟨a, ha⟩
    change (F.obj.map (f ≫ g)).hom a = (F.obj.map g).hom ((F.obj.map f).hom a)
    rw [F.obj.map_comp]; rfl

def suppT (F : Shv R) : Subfunctor (F.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) where
  obj U := {a | a ∈ supp Z hZ F U.unop}
  map {U V} g a ha := supp_res Z hZ g.unop ha

theorem sheafT (F : Shv R) : Presieve.IsSheaf Scheme.etaleTopology (F.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) :=
  (isSheaf_iff_isSheaf_of_type _ _).1 ((Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget _)).1 F.property)

theorem suppT_isSheaf (F : Shv R) : Presieve.IsSheaf Scheme.etaleTopology (suppT Z hZ F).toFunctor := by
  rw [Subfunctor.isSheaf_iff _ (sheafT F)]
  intro U s hs
  change sv Z hZ (F := F) (U := U.unop) s ∈ Scheme.etaleTopology U.unop
  refine Scheme.etaleTopology.transitive hs _ (fun V f hf => ?_)
  have hf' : sv Z hZ (Sec.res f s) ∈ Scheme.etaleTopology V := hf
  refine Scheme.etaleTopology.superset_covering (fun W h hh => ?_) hf'
  change Z W ∨ Sec.res (h ≫ f) s = 0
  rw [res_comp]
  exact hh

theorem sectionsWithSupport_isSheaf (F : Shv R) : Presheaf.IsSheaf Scheme.etaleTopology (suppP Z hZ F) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget _), isSheaf_iff_isSheaf_of_type]
  refine Presieve.isSheaf_iso _ (NatIso.ofComponents (fun U => Iso.refl _) (fun _ => rfl)).symm (suppT_isSheaf Z hZ F)

theorem res_map {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (a : Sec F U) :
    Sec.res g (Sec.map φ a) = Sec.map φ (Sec.res g a) := by
  change (φ.hom.app (op U) ≫ G.obj.map g.op).hom a = (F.obj.map g.op ≫ φ.hom.app (op V)).hom a
  rw [φ.hom.naturality]

theorem supp_map {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} {a : Sec F U} (ha : a ∈ supp Z hZ F U) :
    Sec.map φ a ∈ supp Z hZ G U := by
  refine Scheme.etaleTopology.superset_covering (fun V g hg => ?_) (show sv Z hZ a ∈ Scheme.etaleTopology U from ha)
  rcases hg with h | h
  · exact Or.inl h
  · right
    change Sec.res g (Sec.map φ a) = 0
    rw [res_map, h]
    exact map_zero (φ.hom.app (op V)).hom

def suppS (F : Shv R) : Shv R := ⟨suppP Z hZ F, sectionsWithSupport_isSheaf Z hZ F⟩

def suppF : Shv R ⥤ Shv R where
  obj F := suppS Z hZ F
  map {F G} φ := ObjectProperty.homMk
    { app U := ModuleCat.ofHom ((φ.hom.app U).hom.restrict (fun a ha => supp_map Z hZ φ ha))
      naturality U V g := by
        ext ⟨a, ha⟩
        exact Subtype.ext (res_map φ g.unop a).symm }
  map_id F := by
    apply ObjectProperty.hom_ext
    ext U ⟨a, ha⟩
    rfl
  map_comp f g := by
    apply ObjectProperty.hom_ext
    ext U ⟨a, ha⟩
    rfl

def suppι : suppF Z hZ ⟶ 𝟭 (Shv R) where
  app F := ObjectProperty.homMk
    { app U := ModuleCat.ofHom (supp Z hZ F U.unop).subtype
      naturality U V g := by
        ext ⟨a, ha⟩
        rfl }
  naturality F G φ := by
    apply ObjectProperty.hom_ext
    ext U ⟨a, ha⟩
    rfl

instance : (suppF Z hZ (R := R)).PreservesZeroMorphisms where
  map_zero F G := by
    apply ObjectProperty.hom_ext
    ext U ⟨a, ha⟩
    apply Subtype.ext
    change ((0 : F ⟶ G).hom.app U).hom a = 0
    simp

def suppCx (C : Cx R) : Cx R := ((suppF Z hZ).mapHomologicalComplex _).obj C

def suppCxι (C : Cx R) : suppCx Z hZ C ⟶ C where
  f n := (suppι Z hZ).app (C.X n)
  comm' i j _ := (suppι Z hZ).naturality (C.d i j)

theorem exists_supp_sub : ∀ (R : Type) [CommRing R] (C : Cx R) (Z : Scheme.{0} → Prop), (∀ (V U : Scheme.{0}) (_ : V ⟶ U), Z U → Z V) → ∃ (D : Cx R) (ι : D ⟶ C), (∀ n U, Function.Injective (Sec.map (ι.f n) (U := U))) ∧ ∀ n U (a : Sec (C.X n) U), (∃ b, Sec.map (ι.f n) b = a) ↔ Loc U fun V g => Z V ∨ Sec.res g a = 0 := by
  intro R _ C Z hZ
  refine ⟨suppCx Z hZ C, suppCxι Z hZ C, fun n U => ?_, fun n U a => ?_⟩
  · intro b b' h
    exact Subtype.ext (p := fun x => x ∈ supp Z hZ (C.X n) U) h
  · rw [loc_iff Z hZ]
    constructor
    · rintro ⟨b, rfl⟩
      exact (show ↥(supp Z hZ (C.X n) U) from b).2
    · intro h
      exact ⟨(⟨a, h⟩ : ↥(supp Z hZ (C.X n) U)), rfl⟩

end GlobalTheory.EtC.SuppSub
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFlipSheafComplexPairing
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFlipSheafComplexPairing
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped DirectSum TensorProduct

noncomputable section
namespace GlobalTheory.EtC.SwapTransfer

variable {R : Type} [CommRing R]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
theorem _root_.GlobalTheory.EtC.SwapTransfer.negOnePow_sq' (n m : ℤ) :
    (n.negOnePow : ℤ) * ((m.negOnePow : ℤ) * (n.negOnePow : ℤ)) = m.negOnePow := by
  rw [mul_left_comm, ← Units.val_mul, Int.units_mul_self, Units.val_one, mul_one]

def flipPair {I J K : Cx R} (μ : Pair I J K) : Pair J I K where
  mul U t s w h := (((s * t).negOnePow : ℤ) • μ.mul U s t w (by omega)).flip
  nat g t s w h b a := by
    simp only [LinearMap.flip_apply, LinearMap.smul_apply, Sec.res, map_zsmul]
    rw [← Sec.res, μ.nat]
  leibniz U t s w h b a := by
    simp only [LinearMap.flip_apply, LinearMap.smul_apply, Sec.map, map_zsmul]
    rw [← Sec.map, μ.leibniz]
    have h1 : (s * (t + 1)).negOnePow = (s * t).negOnePow * s.negOnePow := by
      rw [mul_add, mul_one, Int.negOnePow_add]
    have h2 : ((s + 1) * t).negOnePow = (s * t).negOnePow * t.negOnePow := by
      rw [add_mul, one_mul, Int.negOnePow_add]
    rw [h1, h2]
    simp only [Units.smul_def, smul_add, smul_smul, Units.val_mul]
    rw [negOnePow_sq']
    exact add_comm _ _

def swIdx {w : ℤ} (p : {p : ℤ × ℤ // p.1 + p.2 = w}) : {p : ℤ × ℤ // p.1 + p.2 = w} :=
  ⟨(p.1.2, p.1.1), by have := p.2; simp only at this ⊢; omega⟩

def swapT (I J : Cx R) (U : Scheme.{0}) (w : ℤ) : Tens I J U w →ₗ[ULift.{1} R] Tens J I U w := by
  classical
  exact DirectSum.toModule _ _ _ fun p =>
    ((p.1.1 * p.1.2).negOnePow : ℤ) • ((DirectSum.lof (ULift.{1} R) _ (fun q : {p : ℤ × ℤ // p.1 + p.2 = w} =>
      Sec (J.X q.1.1) U ⊗[ULift.{1} R] Sec (I.X q.1.2) U) (swIdx p)) ∘ₗ
      (TensorProduct.comm (ULift.{1} R) (Sec (I.X p.1.1) U) (Sec (J.X p.1.2) U)).toLinearMap)

end GlobalTheory.EtC.SwapTransfer

namespace GlobalTheory.EtC

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
private theorem flipPair_mul_eq_negOnePow_smul_mul {I J K : _root_.GlobalTheory.EtC.Cx R} (μ : _root_.GlobalTheory.EtC.Pair I J K) (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w)
    (a : _root_.GlobalTheory.EtC.Sec (I.X s) U) (b : _root_.GlobalTheory.EtC.Sec (J.X t) U) :
    (_root_.GlobalTheory.EtC.SwapTransfer.flipPair μ).mul U t s w (by omega) b a = (s * t).negOnePow • μ.mul U s t w h a b := by
  rw [Units.smul_def]
  rfl

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
private theorem koszulSwap_lof_tmul_lemma_5 (I J : _root_.GlobalTheory.EtC.Cx R) (U : Scheme.{0}) {w s t : ℤ} (h : s + t = w)
    (a : _root_.GlobalTheory.EtC.Sec (I.X s) U) (b : _root_.GlobalTheory.EtC.Sec (J.X t) U) :
    _root_.GlobalTheory.EtC.SwapTransfer.swapT I J U w
        (DirectSum.lof (ULift.{1} R) _ (fun q : {p : ℤ × ℤ // p.1 + p.2 = w} =>
          _root_.GlobalTheory.EtC.Sec (I.X q.1.1) U ⊗[ULift.{1} R] _root_.GlobalTheory.EtC.Sec (J.X q.1.2) U)
          ⟨(s, t), h⟩ (a ⊗ₜ b)) =
      (s * t).negOnePow • DirectSum.lof (ULift.{1} R) _ (fun q : {p : ℤ × ℤ // p.1 + p.2 = w} =>
          _root_.GlobalTheory.EtC.Sec (J.X q.1.1) U ⊗[ULift.{1} R] _root_.GlobalTheory.EtC.Sec (I.X q.1.2) U)
          ⟨(t, s), by omega⟩ (b ⊗ₜ a) := by
  unfold _root_.GlobalTheory.EtC.SwapTransfer.swapT
  erw [DirectSum.toModule_lof]
  rw [Units.smul_def]
  rfl

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
private theorem lift_lof_tmul {I J K : _root_.GlobalTheory.EtC.Cx R} (μ : _root_.GlobalTheory.EtC.Pair I J K) (U : Scheme.{0}) {w s t : ℤ} (h : s + t = w)
    (a : _root_.GlobalTheory.EtC.Sec (I.X s) U) (b : _root_.GlobalTheory.EtC.Sec (J.X t) U) :
    μ.lift U w
        (DirectSum.lof (ULift.{1} R) _ (fun q : {p : ℤ × ℤ // p.1 + p.2 = w} =>
          _root_.GlobalTheory.EtC.Sec (I.X q.1.1) U ⊗[ULift.{1} R] _root_.GlobalTheory.EtC.Sec (J.X q.1.2) U)
          ⟨(s, t), h⟩ (a ⊗ₜ b)) = μ.mul U s t w h a b := by
  unfold _root_.GlobalTheory.EtC.Pair.lift
  erw [DirectSum.toModule_lof]
  rfl

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
private theorem lift_comp_swapT_eq_flipPair_lift {I J K : _root_.GlobalTheory.EtC.Cx R} (μ : _root_.GlobalTheory.EtC.Pair I J K) (U : Scheme.{0}) (w : ℤ) :
    μ.lift U w ∘ₗ _root_.GlobalTheory.EtC.SwapTransfer.swapT J I U w =
      (_root_.GlobalTheory.EtC.SwapTransfer.flipPair μ).lift U w := by
  unfold _root_.GlobalTheory.EtC.Tens
  apply DirectSum.linearMap_ext
  rintro ⟨⟨t, s⟩, h⟩
  apply TensorProduct.ext'
  intro b a
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, koszulSwap_lof_tmul_lemma_5, map_zsmul_unit, lift_lof_tmul, lift_lof_tmul, Units.smul_def, mul_comm t s]
  rfl

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
private theorem swapT_comp_swapT (I J : _root_.GlobalTheory.EtC.Cx R) (U : Scheme.{0}) (w : ℤ) :
    _root_.GlobalTheory.EtC.SwapTransfer.swapT J I U w ∘ₗ _root_.GlobalTheory.EtC.SwapTransfer.swapT I J U w = LinearMap.id := by
  unfold _root_.GlobalTheory.EtC.Tens
  apply DirectSum.linearMap_ext
  rintro ⟨⟨s, t⟩, h⟩
  apply TensorProduct.ext'
  intro a b
  rw [LinearMap.comp_apply, LinearMap.comp_apply, koszulSwap_lof_tmul_lemma_5, map_zsmul_unit, koszulSwap_lof_tmul_lemma_5, smul_smul, mul_comm t s, Int.units_mul_self, one_smul]
  rfl

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
private theorem tensorRestrict_lof_tmul_lemma_7 (I J : _root_.GlobalTheory.EtC.Cx R) {V U : Scheme.{0}} (g : V ⟶ U) {w s t : ℤ} (h : s + t = w)
    (a : _root_.GlobalTheory.EtC.Sec (I.X s) U) (b : _root_.GlobalTheory.EtC.Sec (J.X t) U) :
    _root_.GlobalTheory.EtC.Tens.res g w
        (DirectSum.lof (ULift.{1} R) _ (fun q : {p : ℤ × ℤ // p.1 + p.2 = w} =>
          _root_.GlobalTheory.EtC.Sec (I.X q.1.1) U ⊗[ULift.{1} R] _root_.GlobalTheory.EtC.Sec (J.X q.1.2) U)
          ⟨(s, t), h⟩ (a ⊗ₜ b)) =
      DirectSum.lof (ULift.{1} R) _ (fun q : {p : ℤ × ℤ // p.1 + p.2 = w} =>
          _root_.GlobalTheory.EtC.Sec (I.X q.1.1) V ⊗[ULift.{1} R] _root_.GlobalTheory.EtC.Sec (J.X q.1.2) V)
          ⟨(s, t), h⟩ (_root_.GlobalTheory.EtC.Sec.res g a ⊗ₜ _root_.GlobalTheory.EtC.Sec.res g b) := by
  unfold _root_.GlobalTheory.EtC.Tens.res
  erw [DirectSum.lmap_lof]
  rfl

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
private theorem res_comp_swapT (I J : _root_.GlobalTheory.EtC.Cx R) {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) :
    _root_.GlobalTheory.EtC.Tens.res g w ∘ₗ _root_.GlobalTheory.EtC.SwapTransfer.swapT I J U w =
      _root_.GlobalTheory.EtC.SwapTransfer.swapT I J V w ∘ₗ _root_.GlobalTheory.EtC.Tens.res g w := by
  unfold _root_.GlobalTheory.EtC.Tens
  apply DirectSum.linearMap_ext
  rintro ⟨⟨s, t⟩, h⟩
  apply TensorProduct.ext'
  intro a b
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, koszulSwap_lof_tmul_lemma_5, map_zsmul_unit, tensorRestrict_lof_tmul_lemma_7, tensorRestrict_lof_tmul_lemma_7, koszulSwap_lof_tmul_lemma_5]


open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
theorem _root_.GlobalTheory.EtC.Pair.exists_isFlip (R : Type) [CommRing R]
    {I J K : _root_.GlobalTheory.EtC.Cx R} (μ : _root_.GlobalTheory.EtC.Pair I J K) :
    ∃ ν : _root_.GlobalTheory.EtC.Pair J I K, μ.IsFlip ν ∧ ν.IsFlip μ ∧
      (μ.IsTensor → ν.IsTensor) := by
  refine ⟨_root_.GlobalTheory.EtC.SwapTransfer.flipPair μ, ?_, ?_, ?_⟩
  · intro U s t w h a b
    exact flipPair_mul_eq_negOnePow_smul_mul μ U s t w h a b
  · intro U t s w h b a
    rw [flipPair_mul_eq_negOnePow_smul_mul μ U s t w (by omega) a b, smul_smul, mul_comm t s, Int.units_mul_self, one_smul]
  · rintro ⟨hsurj, hinj⟩
    refine ⟨fun U w y => ?_, fun U w x hx => ?_⟩
    · obtain ⟨S, hS, hP⟩ := hsurj U w y
      refine ⟨S, hS, fun V g hg => ?_⟩
      obtain ⟨x, hx⟩ := hP V g hg
      refine ⟨_root_.GlobalTheory.EtC.SwapTransfer.swapT I J V w x, ?_⟩
      rw [← lift_comp_swapT_eq_flipPair_lift, LinearMap.comp_apply, ← LinearMap.comp_apply (_root_.GlobalTheory.EtC.SwapTransfer.swapT J I V w), swapT_comp_swapT, LinearMap.id_apply]
      exact hx
    · have hx' : μ.lift U w (_root_.GlobalTheory.EtC.SwapTransfer.swapT J I U w x) = 0 := by
        rw [← LinearMap.comp_apply, lift_comp_swapT_eq_flipPair_lift]
        exact hx
      obtain ⟨S, hS, hP⟩ := hinj U w _ hx'
      refine ⟨S, hS, fun V g hg => ?_⟩
      have hV := congrArg (_root_.GlobalTheory.EtC.SwapTransfer.swapT I J V w) (hP V g hg)
      rw [← LinearMap.comp_apply (_root_.GlobalTheory.EtC.Tens.res g w), res_comp_swapT, LinearMap.comp_apply,
        ← LinearMap.comp_apply (_root_.GlobalTheory.EtC.SwapTransfer.swapT I J V w), swapT_comp_swapT, LinearMap.id_apply, map_zero] at hV
      exact hV

end GlobalTheory.EtC

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFlipSheafComplexPairingStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isFlip_sheafComplexPairing : ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K), ∃ ν : Pair J I K, μ.IsFlip ν ∧ ν.IsFlip μ ∧ (μ.IsTensor → ν.IsTensor) := by
  first | exact @GlobalTheory.EtC.Pair.exists_isFlip | exact GlobalTheory.EtC.Pair.exists_isFlip | (intros; apply GlobalTheory.EtC.Pair.exists_isFlip <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardIsGaloisTwistedNormGLMulCardGL
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardIsGaloisTwistedNormGLMulCardGL
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

noncomputable section

namespace GlobalTheory.Shin.NormFibre

theorem card_conj_mul_card_commute {G : Type} [Group G] (g : G) :
    Nat.card {g' : G // IsConj g g'} * Nat.card {x : G // Commute x g} = Nat.card G := by
  have e1 : {g' : G // IsConj g g'} ≃ MulAction.orbit (ConjAct G) g :=
    Equiv.subtypeEquivRight (fun g' => by rw [ConjAct.mem_orbit_conjAct, isConj_comm])
  have e2 : {x : G // Commute x g} ≃ MulAction.stabilizer (ConjAct G) g :=
    { toFun := fun x => ⟨ConjAct.toConjAct x.1, by
          rw [MulAction.mem_stabilizer_iff, ConjAct.toConjAct_smul, x.2.eq, mul_inv_cancel_right]⟩
      invFun := fun y => ⟨ConjAct.ofConjAct y.1, by
          have h := y.2
          rw [MulAction.mem_stabilizer_iff, ConjAct.smul_def, mul_inv_eq_iff_eq_mul] at h
          exact h⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  rw [Nat.card_congr e1, Nat.card_congr e2, ← Nat.card_prod,
    Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (ConjAct G) g),
    Nat.card_congr (ConjAct.toConjAct (G := G)).toEquiv.symm]

section Fields

variable {F F' : Type} [Field F] [Field F'] [Algebra F F']

theorem galAct_incl (n : ℕ) (t : F' ≃ₐ[F] F') (γ : GL (Fin n) F) :
    galAct F F' n t (incl F F' n γ) = incl F F' n γ := by
  ext i j
  simp [galAct_apply, gal, incl]

theorem galAct_coe (n : ℕ) (t : F' ≃ₐ[F] F') (x : GL (Fin n) F') :
    ((galAct F F' n t x : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') =
      (x : Matrix (Fin n) (Fin n) F').map t := by
  ext i j
  simp [galAct_apply, gal]

end Fields

section Count

variable {F F' : Type} [Field F] [Field F'] [Algebra F F'] [Finite F']

def nrmFibreEquivOf (s : F' ≃ₐ[F] F') (hs : ∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) {n : ℕ}
    {c g' : GL (Fin n) F'} (y : GL (Fin n) F') (hy : y * c * y⁻¹ = g') :
    {δ : GL (Fin n) F' // nrm s δ = g'} ≃ {δ : GL (Fin n) F' // nrm s δ = c} :=
  have htw := (GlobalTheory.T.galoisTwistedNormGL_basic_properties F F' s hs n).2.2.1
  { toFun := fun δ => ⟨y⁻¹ * δ.1 * galAct F F' n s y, by
        rw [htw, δ.2, ← hy]; group⟩
    invFun := fun ε => ⟨y * ε.1 * galAct F F' n s y⁻¹, by
        have := htw ε.1 y⁻¹
        rw [inv_inv] at this
        rw [this, ε.2, hy]⟩
    left_inv := fun δ => by
      apply Subtype.ext
      simp only [map_inv]
      group
    right_inv := fun ε => by
      apply Subtype.ext
      simp only [map_inv]
      group }

def nrmFibreEquiv (s : F' ≃ₐ[F] F') (hs : ∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) {n : ℕ}
    {c g' : GL (Fin n) F'} (h : IsConj c g') :
    {δ : GL (Fin n) F' // nrm s δ = g'} ≃ {δ : GL (Fin n) F' // nrm s δ = c} :=
  nrmFibreEquivOf s hs _ (isConj_iff.1 h).choose_spec

theorem card_isConj_nrm (s : F' ≃ₐ[F] F') (hs : ∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) {n : ℕ}
    (c : GL (Fin n) F') :
    Nat.card {δ : GL (Fin n) F' // IsConj c (nrm s δ)} =
      Nat.card {g' : GL (Fin n) F' // IsConj c g'} * Nat.card {δ : GL (Fin n) F' // nrm s δ = c} := by
  have e : {δ : GL (Fin n) F' // IsConj c (nrm s δ)} ≃
      Σ g' : {g' : GL (Fin n) F' // IsConj c g'}, {δ : GL (Fin n) F' // nrm s δ = g'.1} :=
    { toFun := fun δ => ⟨⟨nrm s δ.1, δ.2⟩, ⟨δ.1, rfl⟩⟩
      invFun := fun p => ⟨p.2.1, by rw [p.2.2]; exact p.1.2⟩
      left_inv := fun δ => rfl
      right_inv := fun p => by
        rcases p with ⟨⟨g', hg⟩, ⟨δ, hδ⟩⟩
        dsimp only at hδ
        subst hδ
        rfl }
  rw [← Nat.card_prod]
  exact Nat.card_congr (e.trans ((Equiv.sigmaCongrRight fun g' => nrmFibreEquiv s hs g'.2).trans
    (Equiv.sigmaEquivProd _ _)))

end Count

section Centraliser

variable {F F' : Type} [Field F] [Field F'] [Algebra F F'] [Finite F']

theorem card_nrm_eq_mul_card_commute (s : F' ≃ₐ[F] F') (hs : ∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s)
    (n : ℕ) (γ : GL (Fin n) F) :
    Nat.card {δ : GL (Fin n) F' // nrm s δ = incl F F' n γ} * Nat.card {x : GL (Fin n) F // Commute x γ} =
      Nat.card {x : GL (Fin n) F' // Commute x (incl F F' n γ)} := by
  obtain ⟨-, hinj, -, hcomm, hmul⟩ := GlobalTheory.T.galoisTwistedNormGL_basic_properties F F' s hs n
  obtain ⟨δ₀, hδ₀B, hδ₀⟩ := GlobalTheory.T.norm_map_surjective_finite_field F F' s hs n γ
  have hcfix : ∀ t : F' ≃ₐ[F] F', galAct F F' n t (incl F F' n γ) = incl F F' n γ := fun t => galAct_incl n t γ
  set c := incl F F' n γ with hc
  set B := Subalgebra.centralizer F' {(c : Matrix (Fin n) (Fin n) F')} with hB
  have memB : ∀ x : GL (Fin n) F', (x : Matrix (Fin n) (Fin n) F') ∈ B ↔ Commute x c := by
    intro x
    rw [hB, Subalgebra.mem_centralizer_iff]
    simp only [Set.mem_singleton_iff, forall_eq]
    rw [Commute, SemiconjBy, Units.ext_iff, Units.val_mul, Units.val_mul]
    exact eq_comm
  have hcs : (c : Matrix (Fin n) (Fin n) F').map s = c := by rw [← galAct_coe, hcfix]
  have hstab : ∀ x ∈ B, x.map s ∈ B := by
    intro x hx
    rw [hB, Subalgebra.mem_centralizer_iff] at hx ⊢
    simp only [Set.mem_singleton_iff, forall_eq] at hx ⊢
    have e1 : ((c : Matrix (Fin n) (Fin n) F') * x).map s = ((c : Matrix (Fin n) (Fin n) F').map s) * x.map s :=
      Matrix.map_mul (f := (s : F' →+* F'))
    have e2 : (x * (c : Matrix (Fin n) (Fin n) F')).map s = x.map s * ((c : Matrix (Fin n) (Fin n) F').map s) :=
      Matrix.map_mul (f := (s : F' →+* F'))
    rw [hcs] at e1 e2
    rw [← e1, ← e2, hx]
  have h90 := GlobalTheory.T.card_twistedNorm_one_mul_card_fixed_units F F' s hs n B hstab
  have hδ₀comm : ∀ e : GL (Fin n) F', Commute e c → Commute δ₀ e := by
    intro e he
    have hle : Algebra.adjoin F' {(c : Matrix (Fin n) (Fin n) F')} ≤
        Subalgebra.centralizer F' {(e : Matrix (Fin n) (Fin n) F')} := by
      apply Algebra.adjoin_le
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz, SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      rw [hg, ← Units.val_mul, ← Units.val_mul, he.eq]
    have h1 := hle hδ₀B
    rw [Subalgebra.mem_centralizer_iff] at h1
    have h2 := h1 _ rfl
    exact Units.ext (by rw [Units.val_mul, Units.val_mul]; exact h2.symm)
  have hδ₀c : Commute δ₀ c := hδ₀comm c (Commute.refl c)
  have key : ∀ ε : GL (Fin n) F', Commute ε c → nrm s (δ₀ * ε) = c * nrm s ε := by
    intro ε hε
    rw [hmul δ₀ ε ?_, hδ₀]
    intro t u
    have h3 : Commute δ₀ (galAct F F' n (t⁻¹ * u) ε) := by
      apply hδ₀comm
      have := hε.map (galAct F F' n (t⁻¹ * u))
      rwa [hcfix] at this
    have h4 := h3.map (galAct F F' n t)
    have e : galAct F F' n t (galAct F F' n (t⁻¹ * u) ε) = galAct F F' n u ε := by
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel_left]
    rwa [e] at h4
  have hYcomm : ∀ δ : GL (Fin n) F', nrm s δ = c → Commute δ c := by
    intro δ h
    have := hcomm δ
    rw [h, hcfix] at this
    exact this
  have eY : {δ : GL (Fin n) F' // nrm s δ = c} ≃
      {ε : GL (Fin n) F' // (ε : Matrix (Fin n) (Fin n) F') ∈ B ∧ nrm s ε = 1} :=
    { toFun := fun δ => ⟨δ₀⁻¹ * δ.1, (memB _).2 (hδ₀c.inv_left.mul_left (hYcomm _ δ.2)), by
          have := key (δ₀⁻¹ * δ.1) (hδ₀c.inv_left.mul_left (hYcomm _ δ.2))
          rw [mul_inv_cancel_left, δ.2] at this
          simpa using this.symm⟩
      invFun := fun ε => ⟨δ₀ * ε.1, by rw [key _ ((memB _).1 ε.2.1), ε.2.2, mul_one]⟩
      left_inv := fun δ => Subtype.ext (mul_inv_cancel_left _ _)
      right_inv := fun ε => Subtype.ext (inv_mul_cancel_left _ _) }
  have eC' : {x : GL (Fin n) F' // (x : Matrix (Fin n) (Fin n) F') ∈ B} ≃ {x : GL (Fin n) F' // Commute x c} :=
    Equiv.subtypeEquivRight memB
  have eC : {x : GL (Fin n) F // ((incl F F' n x : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') ∈ B} ≃
      {x : GL (Fin n) F // Commute x γ} :=
    Equiv.subtypeEquivRight fun x => by
      rw [memB]
      exact ⟨fun h => hinj (by simpa only [map_mul] using h.eq), fun h => h.map _⟩
  rw [Nat.card_congr eY, ← Nat.card_congr eC, ← Nat.card_congr eC']
  exact h90

end Centraliser

theorem card_isNorm_mul_card : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'),
    (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (n : ℕ) (γ : GL (Fin n) F),
    Nat.card {δ : GL (Fin n) F' // IsNorm s δ γ} * Nat.card (GL (Fin n) F) =
      Nat.card {γ' : GL (Fin n) F // IsConj γ γ'} * Nat.card (GL (Fin n) F') := by
  intro F F' _ _ _ _ s hs n γ
  have hX : Nat.card {δ : GL (Fin n) F' // IsNorm s δ γ} =
      Nat.card {g' : GL (Fin n) F' // IsConj (incl F F' n γ) g'} *
        Nat.card {δ : GL (Fin n) F' // nrm s δ = incl F F' n γ} :=
    card_isConj_nrm s hs (incl F F' n γ)
  have hY := card_nrm_eq_mul_card_commute s hs n γ
  have h1 := card_conj_mul_card_commute (incl F F' n γ)
  have h2 := card_conj_mul_card_commute γ
  rw [hX, ← h2, ← h1, ← hY]
  ring

end GlobalTheory.Shin.NormFibre
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardIsGaloisTwistedNormGLMulCardGLStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_isGaloisTwistedNormGL_mul_card_GL : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (n : ℕ) (γ : GL (Fin n) F), Nat.card {δ : GL (Fin n) F' // IsNorm s δ γ} * Nat.card (GL (Fin n) F) = Nat.card {γ' : GL (Fin n) F // IsConj γ γ'} * Nat.card (GL (Fin n) F') := by
  first | (exact @GlobalTheory.Shin.NormFibre.card_isNorm_mul_card) | (exact GlobalTheory.Shin.NormFibre.card_isNorm_mul_card) | (intros; apply GlobalTheory.Shin.NormFibre.card_isNorm_mul_card  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiGPairingEqChGPairing
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraInductionGLTrivialOrthogonalHyperpl
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraInductionGLTrivialOrthogonalHyperpl
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem hc_one_orth_hfree : ∀ (F : Type) [Field F] [Finite F], ∀ (a b n : ℕ), n = a + b → 0 < b →
    ∀ (α : GL (Fin a) F → ℂ) (Y : GL (Fin n) F → ℂ), IsChar ℂ ℂ Y → HFree Y →
    ∑ᶠ x, hc a b α (fun _ => 1) n x * star (Y x) = 0 := by
  intro F _ _ a b n hn hb α Y hY hF
  haveI : Fintype (GL (Fin n) F) := Fintype.ofFinite _
  have hn0 : 0 < n := by omega
  have hcl : ∀ g x : GL (Fin n) F, Y (x⁻¹ * g * x) = Y g :=
    (virt_mul_comap_conj_ind_linear (GL (Fin n) F)).2.2.1 Y (isChar_mem_virt_complex hY)
  let Pm : GL (Fin n) F → Prop := fun x => ∀ i j : Fin n, (j : ℕ) + 1 < n →
    (x : Matrix (Fin n) (Fin n) F) i j = (1 : Matrix (Fin n) (Fin n) F) i j
  have hR : ∀ (M : Matrix (Fin n) (Fin n) F) (x : GL (Fin n) F), Pm x → ∀ i j : Fin n, (j : ℕ) + 1 < n →
      (M * (x : Matrix (Fin n) (Fin n) F)) i j = M i j := by
    intro M x hx i j hj
    rw [Matrix.mul_apply]
    simp only [hx _ j hj]
    rw [← Matrix.mul_apply, Matrix.mul_one]
  let H : Subgroup (GL (Fin n) F) :=
    { carrier := {x | Pm x}
      one_mem' := fun i j _ => by simp
      mul_mem' := fun {x y : GL (Fin n) F} hx hy i j hj => by
        show ((x * y : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j = _
        rw [Units.val_mul, hR _ y hy i j hj]; exact hx i j hj
      inv_mem' := fun {x : GL (Fin n) F} hx i j hj => by
        have h1 : ((x⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (x : Matrix (Fin n) (Fin n) F) = 1 := by
          rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
        have := hR ((x⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) x hx i j hj
        rw [h1] at this
        exact this.symm }
  have hH : ∑ᶠ u : H, Y u = 0 := by
    have := hF hn0
    rw [← finsum_set_coe_eq_finsum_mem] at this
    exact this
  have hcos := char_coset_sum_eq_zero (GL (Fin n) F) Y hY H hH
  haveI : Fintype H := Fintype.ofFinite _
  let f : GL (Fin n) F → ℂ := fun x => if InPar a x then α (tlG a x) else 0
  have hent : ∀ x : GL (Fin n) F, ∀ h ∈ H, ∀ i j : Fin n, (j : ℕ) < a →
      ((x * h : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j = (x : Matrix (Fin n) (Fin n) F) i j := by
    intro x h hh i j hj
    rw [Units.val_mul]
    exact hR _ h hh i j (by omega)
  have hinv : ∀ x : GL (Fin n) F, ∀ h ∈ H, f (x * h) = f x := by
    intro x h hh
    have h1 : InPar a (x * h) ↔ InPar a x := by
      unfold InPar
      constructor
      · intro H' i j hj hi; rw [← hent x h hh i j hj]; exact H' i j hj hi
      · intro H' i j hj hi; rw [hent x h hh i j hj]; exact H' i j hj hi
    have h2 : tlG a (x * h) = tlG a x := by
      unfold tlG
      congr 1
      funext i j
      unfold tl ent
      split_ifs with hij
      · exact hent x h hh _ _ j.2
      · rfl
    simp only [f, h1, h2]
  have hS : ∑ x, f x * star (Y x) = 0 := by
    have hh : ∀ h : H, ∑ x, f x * star (Y x) = ∑ x, f x * star (Y (x * h)) := by
      intro h
      refine Fintype.sum_equiv (Equiv.mulRight (h : GL (Fin n) F)).symm _ _ ?_
      intro x
      simp only [Equiv.coe_mulRight, Equiv.mulRight_symm]
      rw [inv_mul_cancel_right, hinv x _ (H.inv_mem h.2)]
    have hsum : (Fintype.card H : ℂ) * ∑ x, f x * star (Y x) = 0 := by
      rw [← nsmul_eq_mul, ← Finset.card_univ, ← Finset.sum_const]
      rw [Finset.sum_congr rfl fun h _ => hh h, Finset.sum_comm]
      refine Finset.sum_eq_zero fun x _ => ?_
      rw [← Finset.mul_sum, ← star_sum]
      have := hcos x
      rw [finsum_eq_sum_of_fintype] at this
      rw [this, star_zero, mul_zero]
    have hc0 : (Fintype.card H : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    exact (mul_eq_zero.mp hsum).resolve_left hc0
  have hmain : ∀ y : GL (Fin n) F, ∑ x, f (y⁻¹ * x * y) * star (Y x) = 0 := by
    intro y
    rw [← hS]
    refine Fintype.sum_equiv (MulAut.conj y⁻¹).toEquiv _ _ ?_
    intro x
    simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, inv_inv, hcl]
  have hg : ∀ y : GL (Fin n) F, gal (RingHom.id F) n y = y := fun y => by
    ext i j; simp [gal]
  rw [finsum_eq_sum_of_fintype]
  unfold hc hcTw
  simp only [hg, mul_one, finsum_eq_sum_of_fintype]
  simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun y _ => ?_
  rw [← Finset.mul_sum]
  have := hmain y
  simp only [f, mul_assoc] at this
  rw [this, mul_zero]

end GlobalTheory.Shin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraInductionGLTrivialOrthogonalHyperplStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harishChandraInductionGL_trivial_orthogonal_hyperplaneFixer : ∀ (F : Type) [Field F] [Finite F], ∀ (a b n : ℕ), n = a + b → 0 < b → ∀ (α : GL (Fin a) F → ℂ) (Y : GL (Fin n) F → ℂ), IsChar ℂ ℂ Y → HFree Y → ∑ᶠ x, hc a b α (fun _ => 1) n x * star (Y x) = 0 := by
  first | (exact @GlobalTheory.Shin.hc_one_orth_hfree) | (exact GlobalTheory.Shin.hc_one_orth_hfree) | (intros; apply GlobalTheory.Shin.hc_one_orth_hfree  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiGPairingEqChGPairing
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory

theorem psiG_pairing_eq_chG_pairing : ∀ (F : Type) [Field F] [Finite F], ∀ (S : F[X] → ℂ) (n : ℕ)
    (Y : GL (Fin n) F → ℂ), IsChar ℂ ℂ Y → HFree Y →
    ∑ᶠ x, psiG S n x * star (Y x) = ∑ᶠ x, chG S n x * star (Y x) := by
  intro F _ _ S n Y hY hF
  have hfin : Finite (GL (Fin n) F) := inferInstance
  have hfs : ∀ f : GL (Fin n) F → ℂ, (Function.support f).Finite := fun f => Set.toFinite _
  have hz : ∀ a ∈ Finset.range n,
      ∑ᶠ x, hc a (n - a) (psiG S a) (fun _ => 1) n x * star (Y x) = 0 := by
    intro a ha
    have ha' : a < n := Finset.mem_range.mp ha
    exact GlobalTheory.T.harishChandraInductionGL_trivial_orthogonal_hyperplaneFixer F a (n - a) n (by omega) (by omega) (psiG S a) Y hY hF
  have hrec : ∀ x, psiG S n x * star (Y x) = chG S n x * star (Y x)
      - ∑ a ∈ Finset.range n, hc a (n - a) (psiG S a) (fun _ => 1) n x * star (Y x) := by
    intro x
    rw [GlobalTheory.T.primitiveFunctionCharpolyGL_harishChandra_recursion F S n x, sub_mul, Finset.sum_mul]
  simp_rw [hrec]
  rw [finsum_sub_distrib (hfs _) (hfs _), finsum_sum_comm (Finset.range n) _ (fun a _ => hfs _),
    Finset.sum_eq_zero hz, sub_zero]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiGPairingEqChGPairingStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_psiG_mul_star_eq_chG : ∀ (F : Type) [Field F] [Finite F], ∀ (S : F[X] → ℂ) (n : ℕ) (Y : GL (Fin n) F → ℂ), IsChar ℂ ℂ Y → HFree Y → ∑ᶠ x, psiG S n x * star (Y x) = ∑ᶠ x, chG S n x * star (Y x) := by
  first | (exact @GlobalTheory.psiG_pairing_eq_chG_pairing) | (exact GlobalTheory.psiG_pairing_eq_chG_pairing) | (intros; apply GlobalTheory.psiG_pairing_eq_chG_pairing <;> assumption)
end
end
