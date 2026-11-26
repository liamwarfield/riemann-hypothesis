module

public import Development.EtaleCohomology.TateTwists.EtaleLocallyExistsPrimitiveRootOfUnityOfInvertib
public import Development.EtaleCohomology.TateTwists.EtaleChainCochainEvalBasicPropertiesHold
public import Development.EtaleCohomology.TateTwists.ExistsEtaleKummerChernClassCochainOfDegreeValues

@[expose] public section

section -- merged from Development.EtaleCohomology.TateTwists.TPaTensUnivPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped DirectSum TensorProduct

namespace LateralTheory.EtaleFoundations

variable {R : Type} [CommRing R]

abbrev tl {I J : Cx R} {U : Scheme.{0}} {w : ℤ} (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) : Tens I J U w :=
  DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} => Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) p (a ⊗ₜ b)

theorem tu_ext {I J : Cx R} {U : Scheme.{0}} {w : ℤ} {M : Type 1} [AddCommGroup M] [Module (ULift.{1} R) M]
    {f g : Tens I J U w →ₗ[ULift.{1} R] M}
    (h : ∀ p a b, f (tl p a b) = g (tl p a b)) : f = g :=
  DirectSum.linearMap_ext _ fun p => TensorProduct.ext' fun a b => h p a b

theorem tu_res_lof {I J : Cx R} {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) :
    Tens.res g w (tl p a b) = tl p (Sec.res g a) (Sec.res g b) := by
  simp [tl, Tens.res, DirectSum.lmap_lof]

theorem tu_lift_lof {I J K : Cx R} (μ : Pair I J K) (U : Scheme.{0}) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) :
    μ.lift U w (tl p a b) = μ.mul U p.1.1 p.1.2 w p.2 a b := by
  simp [tl, Pair.lift, DirectSum.toModule_lof]

theorem tu_sec_res_id {F : Shv R} {U : Scheme.{0}} (a : Sec F U) : Sec.res (𝟙 U) a = a := by
  simp [Sec.res]

theorem tu_sec_res_comp {F : Shv R} {W V U : Scheme.{0}} (f : W ⟶ V) (g : V ⟶ U) (a : Sec F U) :
    Sec.res (f ≫ g) a = Sec.res f (Sec.res g a) := by
  simp [Sec.res]

def TP (I J : Cx R) (w : ℤ) : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R) where
  obj U := ModuleCat.of _ (Tens I J U.unop w)
  map g := ModuleCat.ofHom (Tens.res g.unop w)
  map_id U := by
    refine ModuleCat.hom_ext (tu_ext fun p a b => ?_)
    simp only [ModuleCat.hom_ofHom, unop_id, ModuleCat.hom_id, LinearMap.id_apply]
    rw [tu_res_lof, tu_sec_res_id, tu_sec_res_id]
  map_comp f g := by
    refine ModuleCat.hom_ext (tu_ext fun p a b => ?_)
    simp only [ModuleCat.hom_ofHom, unop_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [tu_res_lof, tu_res_lof, tu_res_lof, tu_sec_res_comp, tu_sec_res_comp]

theorem tu_lift_nat {I J K : Cx R} (μ : Pair I J K) {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (x : Tens I J U w) :
    μ.lift V w (Tens.res g w x) = Sec.res g (μ.lift U w x) := by
  have : (μ.lift V w).comp (Tens.res g w) = ((K.X w).obj.map g.op).hom.comp (μ.lift U w) := by
    refine tu_ext fun p a b => ?_
    simp only [LinearMap.comp_apply]
    rw [tu_res_lof, tu_lift_lof, tu_lift_lof, ← μ.nat]
  exact LinearMap.congr_fun this x

def Lf {I J K : Cx R} (μ : Pair I J K) (w : ℤ) : TP I J w ⟶ (K.X w).obj where
  app U := ModuleCat.ofHom (μ.lift U.unop w)
  naturality V U g := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    exact tu_lift_nat μ g.unop w x

theorem tu_locInj {I J T : Cx R} (τ : Pair I J T) (hτ : τ.IsTensor) (w : ℤ) :
    Presheaf.IsLocallyInjective Scheme.etaleTopology.{0} (Lf τ w) := by
  constructor
  intro U x' y' hxy
  let x : Tens I J U.unop w := x'
  let y : Tens I J U.unop w := y'
  have hxy' : τ.lift U.unop w x = τ.lift U.unop w y := hxy
  have h0 : τ.lift U.unop w (x - y) = 0 := by
    rw [map_sub]; exact sub_eq_zero.mpr hxy'
  obtain ⟨S, hS, hP⟩ := hτ.2 U.unop w (x - y) h0
  refine Scheme.etaleTopology.superset_covering ?_ hS
  intro V g hg
  have h1 : Tens.res g w (x - y) = 0 := hP V g hg
  rw [map_sub, sub_eq_zero] at h1
  exact h1

theorem tu_locSurj {I J T : Cx R} (τ : Pair I J T) (hτ : τ.IsTensor) (w : ℤ) :
    Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} (Lf τ w) := by
  constructor
  intro U y
  obtain ⟨S, hS, hP⟩ := hτ.1 U w y
  refine Scheme.etaleTopology.superset_covering ?_ hS
  intro V g hg
  obtain ⟨x, hx⟩ := hP V g hg
  exact ⟨x, hx⟩

theorem etaleTensorPairingLift_isSheafifyLocalIso {I J T : Cx R} (τ : Pair I J T) (hτ : τ.IsTensor) (w : ℤ) :
    Scheme.etaleTopology.{0}.W (Lf τ w) := by
  have := tu_locInj τ hτ w
  have := tu_locSurj τ hτ w
  exact GrothendieckTopology.W_of_isLocallyBijective _ _

def uf {I J T K : Cx R} (τ : Pair I J T) (hτ : τ.IsTensor) (μ : Pair I J K) (w : ℤ) : (T.X w).obj ⟶ (K.X w).obj :=
  ((etaleTensorPairingLift_isSheafifyLocalIso τ hτ w) _ (K.X w).property).2 (Lf μ w) |>.choose

theorem uf_spec {I J T K : Cx R} (τ : Pair I J T) (hτ : τ.IsTensor) (μ : Pair I J K) (w : ℤ) :
    Lf τ w ≫ uf τ hτ μ w = Lf μ w :=
  ((etaleTensorPairingLift_isSheafifyLocalIso τ hτ w) _ (K.X w).property).2 (Lf μ w) |>.choose_spec

theorem uf_lift {I J T K : Cx R} (τ : Pair I J T) (hτ : τ.IsTensor) (μ : Pair I J K) (w : ℤ) (U : Scheme.{0})
    (x : Tens I J U w) : ((uf τ hτ μ w).app (op U)).hom (τ.lift U w x) = μ.lift U w x := by
  have := congrArg (fun φ => (φ.app (op U)).hom x) (uf_spec τ hτ μ w)
  exact this

theorem uf_mul {I J T K : Cx R} (τ : Pair I J T) (hτ : τ.IsTensor) (μ : Pair I J K) (U : Scheme.{0})
    (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U) :
    ((uf τ hτ μ w).app (op U)).hom (τ.mul U s t w h a b) = μ.mul U s t w h a b := by
  have := uf_lift τ hτ μ w U (tl (w := w) ⟨(s, t), h⟩ a b)
  rwa [tu_lift_lof, tu_lift_lof] at this

theorem uf_comm {I J T K : Cx R} (τ : Pair I J T) (hτ : τ.IsTensor) (μ : Pair I J K) (i : ℤ) :
    uf τ hτ μ i ≫ (K.d i (i + 1)).hom = (T.d i (i + 1)).hom ≫ uf τ hτ μ (i + 1) := by
  apply ((etaleTensorPairingLift_isSheafifyLocalIso τ hτ i) _ (K.X (i + 1)).property).1
  refine NatTrans.ext (funext fun U => ModuleCat.hom_ext (tu_ext fun p a b => ?_))
  obtain ⟨⟨s, t⟩, h⟩ := p
  simp only [NatTrans.comp_app, ModuleCat.hom_comp]
  change ((K.d i (i + 1)).hom.app U).hom (((uf τ hτ μ i).app (op U.unop)).hom (τ.lift U.unop i (tl _ a b))) =
    ((uf τ hτ μ (i + 1)).app (op U.unop)).hom (((T.d i (i + 1)).hom.app U).hom (τ.lift U.unop i (tl _ a b)))
  rw [tu_lift_lof, uf_mul]
  have l1 := μ.leibniz U.unop s t i h a b
  have l2 := τ.leibniz U.unop s t i h a b
  simp only [Sec.map] at l1 l2
  rw [l1, l2, map_add (f := _), Units.smul_def, Units.smul_def, map_zsmul, uf_mul, uf_mul]

def uc {I J T K : Cx R} (τ : Pair I J T) (hτ : τ.IsTensor) (μ : Pair I J K) : T ⟶ K where
  f w := ⟨uf τ hτ μ w⟩
  comm' i j hij := by
    simp only [ComplexShape.up_Rel] at hij
    subst hij
    ext1
    exact uf_comm τ hτ μ i

theorem t_pa_tens_univ_of : t_pa_tens_univ := by
  intro R _ I J T K τ hτ μ
  refine ⟨uc τ hτ μ, fun U s t w h a b => ?_⟩
  simp only [HomologicalComplex.id_f, pa_sec_map_id]
  exact uf_mul τ hτ μ U s t w h a b

end LateralTheory.EtaleFoundations
end
end

section -- merged from Development.EtaleCohomology.TateTwists.CcAwFlipPf
section -- merged from Development.EtaleCohomology.TateTwists.CcCupFlipPf
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.cc_cup_ex : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (E : Spc) {n m k : ℤ} (hk : n + m = k),
    ∃ c : CohomologyClass ((chains R).obj E) I n →+ CohomologyClass ((chains R).obj E) J m →+ CohomologyClass ((chains R).obj E) K k,
      ∀ (α : Cocycle _ I n) (β : Cocycle _ J m) (γ : Cocycle _ K k), μ.IsAW hk α.1 β.1 γ.1 →
        c (CohomologyClass.mk α) (CohomologyClass.mk β) = CohomologyClass.mk γ

def LateralTheory.EtaleFoundations.cc_aw_flip : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (ν : Pair J I K), μ.IsFlip ν → ∀ (E : Spc) {n m k : ℤ}
    (h : n + m = k) (h' : m + n = k) (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m)
    (γ γ' : Cocycle ((chains R).obj E) K k), μ.IsAW h α.1 β.1 γ.1 → ν.IsAW h' β.1 α.1 γ'.1 →
      CohomologyClass.mk γ = (n * m).negOnePow • CohomologyClass.mk γ'
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleFreeModuleCohomologyHomOfComponents
namespace LateralTheory.Fin.EtaleFreeSheafUniversalProperty
theorem etale_free_module_cohomology_hom_of_components : LateralTheory.EtaleFoundations.EtaleFreeSheafUniversalProperty := by
  apply LateralTheory.EtaleFoundations.etale_free_sheaf_hom_universal_property_holds
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleFreeSheafUniversalProperty := etale_free_module_cohomology_hom_of_components
end LateralTheory.Fin.EtaleFreeSheafUniversalProperty
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleCochainComplexBasicPropertiesOfComponents
section -- merged from Development.EtaleCohomology.TateTwists.EtaleSimplicialChainsBasicPropertiesHold
section -- merged from Development.EtaleCohomology.TateTwists.EtaleSimplicialChainsFreeDescription
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleSimplicialChainsFreeDescription : Prop :=
  ∀ (R : Type) [CommRing R] , (∀ E : Spc, ((chains R).obj E).IsStrictlyLE 0) ∧ (∀ {E E' : Spc} (f : E ⟶ E') (p : ℕ), ((chains R).map f).f (-(p : ℤ)) ≫ (chainsXIso R E' p).hom = (chainsXIso R E p).hom ≫ (free R).map (f.app (op (SimplexCategory.mk p)))) ∧ ∀ (E : Spc) (p : ℕ), (chainsXIso R E (p + 1)).inv ≫ ((chains R).obj E).d (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) ≫ (chainsXIso R E p).hom = ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i)
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.ChainsBasicPf

variable (R : Type) [CommRing R]

lemma chainsN_d (E : Spc) (p : ℕ) :
    ((chainsN R).obj E).d (p + 1) p = ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i) :=
  AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq _ p

lemma chains_map_f {E E' : Spc} (f : E ⟶ E') (p : ℕ) :
    ((chains R).map f).f (-(p : ℤ)) =
      (chainsXIso R E p).hom ≫ (free R).map (f.app (op (SimplexCategory.mk p))) ≫ (chainsXIso R E' p).inv :=
  HomologicalComplex.extendMap_f _ _ rfl

lemma chains_d (E : Spc) (p : ℕ) :
    ((chains R).obj E).d (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) =
      (chainsXIso R E (p + 1)).hom ≫ ((chainsN R).obj E).d (p + 1) p ≫ (chainsXIso R E p).inv :=
  HomologicalComplex.extend_d_eq _ _ rfl rfl

lemma chains_d' (E : Spc) (p : ℕ) :
    (chainsXIso R E (p + 1)).inv ≫ ((chains R).obj E).d (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) ≫ (chainsXIso R E p).hom =
      ((chainsN R).obj E).d (p + 1) p := by
  rw [chains_d R E p]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  erw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

lemma chains_le (E : Spc) : ((chains R).obj E).IsStrictlyLE 0 :=
  inferInstanceAs (CochainComplex.IsStrictlyLE (((chainsN R).obj E).extend ComplexShape.embeddingDownNat) 0)

end LateralTheory.EtaleFoundations.ChainsBasicPf

open LateralTheory.EtaleFoundations.ChainsBasicPf in
theorem LateralTheory.EtaleFoundations.etale_simplicial_chains_basic_properties_hold : LateralTheory.EtaleFoundations.EtaleSimplicialChainsFreeDescription := by
  intro R _
  refine ⟨fun E => chains_le R E, fun {E E'} f p => ?_, fun E p => ?_⟩
  · rw [chains_map_f R f p]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · rw [chains_d' R E p]
    exact chainsN_d R E p
end

namespace LateralTheory.Fin.EtaleSimplicialChainsFreeDescription
theorem etale_cochain_complex_basic_properties_of_components : LateralTheory.EtaleFoundations.EtaleSimplicialChainsFreeDescription := by
  apply LateralTheory.EtaleFoundations.etale_simplicial_chains_basic_properties_hold
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleSimplicialChainsFreeDescription := etale_cochain_complex_basic_properties_of_components
end LateralTheory.Fin.EtaleSimplicialChainsFreeDescription
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleEvaluationMapConstructionOfComponents
namespace LateralTheory.Fin.EtaleCochainExistsOfNaturalEvaluation
theorem etale_evaluation_map_construction_of_components : LateralTheory.EtaleFoundations.EtaleCochainExistsOfNaturalEvaluation := by
  apply LateralTheory.EtaleFoundations.etale_chain_cochain_exists_of_eval_data
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleCochainExistsOfNaturalEvaluation := etale_evaluation_map_construction_of_components
end LateralTheory.Fin.EtaleCochainExistsOfNaturalEvaluation
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem LateralTheory.EtaleFoundations.cupflip_ev_ext_pf : LateralTheory.EtaleFoundations.cupflip_ev_ext := by
  intro R _ E I n α β hab
  refine Cochain.ext _ _ fun p q hpq => ?_
  rcases le_or_gt p 0 with hp | hp
  · obtain ⟨N, rfl⟩ : ∃ N : ℕ, p = -(N : ℤ) := ⟨p.natAbs, by omega⟩
    have key : (chainsXIso R E N).inv ≫ α.v _ q hpq = (chainsXIso R E N).inv ≫ β.v _ q hpq := by
      refine (LateralTheory.Fin.EtaleFreeSheafUniversalProperty.intersectionNumber_baseChange R _ _).2.1 _ _ fun U x => ?_
      exact hab N q hpq U x
    simpa using congrArg (fun f => (chainsXIso R E N).hom ≫ f) key
  · have := (LateralTheory.Fin.EtaleSimplicialChainsFreeDescription.intersectionNumber_baseChange R).1 E
    have hz : IsZero (((chains R).obj E).X p) := CochainComplex.isZero_of_isStrictlyLE _ 0 p hp
    exact hz.eq_of_src _ _

namespace LateralTheory.EtaleFoundations

theorem ev_res' {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E p U) :
    Sec.res g (ev α p s h U x) = ev α p s h V (x.res g) := by
  have h3 := (LateralTheory.Fin.EtaleFreeSheafUniversalProperty.intersectionNumber_baseChange R (E.obj (op (SimplexCategory.mk p))) (I.X s)).2.2.1 V U g x
  unfold ev
  rw [show Sx.res g x = (E.obj (op (SimplexCategory.mk p))).map g.op x from rfl, ← h3]
  have := congrArg (fun f => (ModuleCat.Hom.hom f) (freeGen R (E.obj (op (SimplexCategory.mk p))) U x))
    (((chainsXIso R E p).inv ≫ α.v _ _ h).hom.naturality g.op)
  simpa using this.symm

theorem along_res' {E : Spc} {p N : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E N U)
    (θ : SimplexCategory.mk p ⟶ SimplexCategory.mk N) : (x.along θ).res g = (x.res g).along θ := by
  unfold Sx.along Sx.res
  exact (NatTrans.naturality_apply (E.map θ.op) g.op x).symm

theorem cupflip_eta_mk_pf : cupflip_eta_mk := by
  intro h _ R _ I J K μ E n m k hk α β
  obtain ⟨η, hη⟩ := LateralTheory.Fin.EtaleCochainExistsOfNaturalEvaluation.intersectionNumber_baseChange R (E := E) (I := K) (n := k - 1)
    (fun N s _ U x => phi μ hk α β x s (h N)) (by
      intro N s hs V U g x
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [phi, Finsupp.sum, Sec.res, map_sum, map_zsmul]
      refine Finset.sum_congr rfl fun z _ => ?_
      congr 1
      unfold phiT
      split_ifs with hw
      · rw [map_zsmul]
        have := μ.nat g _ _ _ (by omega : -(z.1 : ℤ) + n + (-(z.2.1 : ℤ) + m) = s)
          (ev α z.1 _ rfl U (x.along z.2.2.1)) (ev β z.2.1 _ rfl U (x.along z.2.2.2))
        simp only [Sec.res] at this
        have ea := ev_res' α _ _ rfl g (x.along z.2.2.1)
        have eb := ev_res' β _ _ rfl g (x.along z.2.2.2)
        rw [along_res'] at ea eb
        simp only [Sec.res] at ea eb
        rw [this, ea, eb]
      · simp)
  exact ⟨η, fun N s hs U x => hη N s hs U x⟩

end LateralTheory.EtaleFoundations

theorem LateralTheory.EtaleFoundations.cc_aw_flip_of (hst : LateralTheory.EtaleFoundations.cupflip_steen) (hdl : LateralTheory.EtaleFoundations.cupflip_eta_delta) :
    LateralTheory.EtaleFoundations.cc_aw_flip :=
  LateralTheory.EtaleFoundations.cupflip_aw_flip_of hst (LateralTheory.EtaleFoundations.cupflip_homotopy_of LateralTheory.EtaleFoundations.cupflip_ev_ext_pf
    LateralTheory.EtaleFoundations.cupflip_eta_mk_pf hdl)
end

section -- merged from Development.EtaleCohomology.TateTwists.ExistsNaturalEtaleKummerDegreeOneValueOfRootsKum
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.V1

theorem loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hPQ : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun V g hg => hPQ V g (hP V g hg)⟩

theorem loc_bind {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hPQ : ∀ V g, P V g → Loc V (fun W k => Q W (k ≫ g))) : Loc U Q := by
  classical
  obtain ⟨S, hS, hP⟩ := h
  let R : ∀ ⦃Y⦄ ⦃f : Y ⟶ U⦄, S.arrows f → Sieve Y := fun Y f H => (hPQ Y f (hP Y f H)).choose
  refine ⟨Sieve.bind S.arrows R, Scheme.etaleTopology.bind_covering hS
    (fun Y f H => (hPQ Y f (hP Y f H)).choose_spec.1), ?_⟩
  rintro W _ ⟨Y, k, f, H, hk, rfl⟩
  exact (hPQ Y f (hP Y f H)).choose_spec.2 W k hk

theorem sec_res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U)
    (s : Sec F U) : Sec.res k (Sec.res g s) = Sec.res (k ≫ g) s := by
  simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem sec_res_id {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (s : Sec F U) :
    Sec.res (𝟙 U) s = s := by
  simp only [Sec.res, op_id, CategoryTheory.Functor.map_id]; rfl

theorem sec_res_map {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U)
    (s : Sec F U) : Sec.res g (Sec.map φ s) = Sec.map φ (Sec.res g s) := by
  simp only [Sec.res, Sec.map]
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← LinearMap.comp_apply, ← ModuleCat.hom_comp,
    φ.hom.naturality]

theorem sx_res_comp {E : Spc} {p : ℕ} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (x : Sx E p U) :
    (x.res g).res k = x.res (k ≫ g) := by
  simp only [Sx.res, op_comp, CategoryTheory.Functor.map_comp_apply]

theorem sx_res_id {E : Spc} {p : ℕ} {U : Scheme.{0}} (x : Sx E p U) : x.res (𝟙 U) = x := by
  simp only [Sx.res, op_id, CategoryTheory.Functor.map_id_apply]

theorem units_map_comp {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (u : (Γ(U, ⊤))ˣ) :
    Units.map k.appTop.hom.toMonoidHom (Units.map g.appTop.hom.toMonoidHom u) =
      Units.map (k ≫ g).appTop.hom.toMonoidHom u := by
  ext; simp [Scheme.Hom.comp_appTop]; rfl

theorem sec_map_comp {R : Type} [CommRing R] {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}}
    (s : Sec F U) : Sec.map ψ (Sec.map φ s) = Sec.map (φ ≫ ψ) s := rfl

theorem d_resGen (q : ℕ) {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) :
    Sec.map ((res _ (tw q 1)).d 0 1) (resGen 1 ζ) = 0 := by
  have h : resι _ (tw q 1) ≫ (res _ (tw q 1)).d 0 1 = 0 := by
    have hc : (injectiveResolution (tw q 1)).ι'.f 0 ≫ (injectiveResolution (tw q 1)).cochainComplex.d 0 1 = 0 := by
      rw [(injectiveResolution (tw q 1)).ι'.comm 0 1]; simp
    exact (Category.assoc _ _ _).trans ((congrArg (fun f => _ ≫ f) hc).trans Limits.comp_zero)
  rw [resGen, sec_map_comp, h]
  simp [Sec.map]

theorem lineUnit_res {E : Spc} (L : E ⟶ ofCat (glCat 1)) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E 1 U) :
    lineUnit L (x.res g) = Units.map g.appTop.hom.toMonoidHom (lineUnit L x) := by
  simp only [lineUnit, Sx.res]
  rw [NatTrans.naturality_apply]
  change Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map g.appTop.hom (glMat ((L.app _).app (op U) x))) = _
  ext
  simp [Matrix.GeneralLinearGroup.map, RingHom.map_det]

noncomputable abbrev dkT (q : ℕ) (V : Scheme.{0}) (v : (Γ(V, ⊤))ˣ) : Sec ((res _ (tw q 1)).X 1) V :=
  Sec.map ((res _ (tw q 1)).d 0 1) (kumT q V v)

theorem isUnit_res {q : ℕ} {V U : Scheme.{0}} (hU : IsUnit (q : Γ(U, ⊤))) (g : V ⟶ U) : IsUnit (q : Γ(V, ⊤)) := by
  simpa using hU.map g.appTop.hom

theorem kT_nat {q : ℕ} (hk : IsKum q (kumT q)) {V U : Scheme.{0}} (hU : IsUnit (q : Γ(U, ⊤))) (g : V ⟶ U)
    (v : (Γ(U, ⊤))ˣ) : Sec.res g (dkT q U v) = dkT q V (Units.map g.appTop.hom.toMonoidHom v) := by
  rw [dkT, sec_res_map, hk.1 V U g v hU]

theorem kT_pow {q : ℕ} (hk : IsKum q (kumT q)) {W : Scheme.{0}} (ζ : Prim q Γ(W, ⊤)) (w : (Γ(W, ⊤))ˣ) (a : ℕ) :
    ∀ w' : (Γ(W, ⊤))ˣ, (w' : Γ(W, ⊤)) = ζ.1 ^ a * w → dkT q W w' = dkT q W w := by
  induction a with
  | zero => intro w' h; have : w' = w := Units.ext (by simpa using h); subst this; rfl
  | succ n ih =>
    intro w' h
    have hu : IsUnit (ζ.1 ^ n * (w : Γ(W, ⊤))) :=
      isUnit_of_mul_isUnit_right (x := ζ.1) (by rw [← mul_assoc, ← pow_succ', ← h]; exact w'.isUnit)
    have e : (w' : Γ(W, ⊤)) = ζ.1 * (hu.unit : Γ(W, ⊤)) := by rw [IsUnit.unit_spec, h, pow_succ', mul_assoc]
    rw [dkT, hk.2 W ζ hu.unit w' e]
    simp only [Sec.map, map_add (f := _)]
    have h0 := d_resGen q ζ
    simp only [Sec.map] at h0
    rw [h0, add_zero]
    exact ih hu.unit (IsUnit.unit_spec hu)

theorem indep {q : ℕ} [NeZero q] (hp : LateralTheory.EtaleFoundations.EtalePrimitiveRootsExistLocally) (hk : IsKum q (kumT q))
    (hs : LateralTheory.EtaleFoundations.EtaleSheafSectionsSeparatedAndGlue) {V : Scheme.{0}} (hV : IsUnit (q : Γ(V, ⊤))) (v v' : (Γ(V, ⊤))ˣ)
    (h : v ^ q = v' ^ q) : dkT q V v = dkT q V v' := by
  apply (hs (ZMod q) ((res _ (tw q 1)).X 1) V).1
  refine loc_bind ((hp q V).1 hV) ?_
  rintro W g ⟨ζ⟩
  have h1 : (v' * v⁻¹) ^ q = 1 := by rw [mul_pow, inv_pow, ← h, mul_inv_cancel]
  have hx : ((Units.map g.appTop.hom.toMonoidHom (v' * v⁻¹) : (Γ(W, ⊤))ˣ) : Γ(W, ⊤)) ^ q = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, h1, map_one, Units.val_one]
  refine loc_mono ((hp q W).2.2.1 ζ _ hx) ?_
  rintro W' k ⟨a, ha⟩
  rw [kT_nat hk hV, kT_nat hk hV]
  have hx' : ((Units.map k.appTop.hom.toMonoidHom (Units.map g.appTop.hom.toMonoidHom (v' * v⁻¹)) : (Γ(W', ⊤))ˣ) : Γ(W', ⊤))
      = (Prim.map k.appTop.hom ζ).1 ^ a := ha
  have e : ((Units.map (k ≫ g).appTop.hom.toMonoidHom v' : (Γ(W', ⊤))ˣ) : Γ(W', ⊤)) =
      (Prim.map k.appTop.hom ζ).1 ^ a * (Units.map (k ≫ g).appTop.hom.toMonoidHom v : (Γ(W', ⊤))ˣ) := by
    rw [← units_map_comp, ← units_map_comp, ← hx', ← Units.val_mul, ← map_mul, ← map_mul, inv_mul_cancel_right]
  exact (kT_pow hk _ _ a _ e).symm

def Q (q : ℕ) {E : Spc} (L : E ⟶ ofCat (glCat 1)) {U : Scheme.{0}} (x : Sx E 1 U) (s : Sec ((res _ (tw q 1)).X 1) U) : Prop :=
  ∀ (V : Scheme.{0}) (g : V ⟶ U) (v : (Γ(V, ⊤))ˣ), v ^ q = lineUnit L (x.res g) → Sec.res g s = dkT q V v

theorem Q_res {q : ℕ} {E : Spc} {L : E ⟶ ofCat (glCat 1)} {V U : Scheme.{0}} {x : Sx E 1 U} {s} (hQ : Q q L x s)
    (g : V ⟶ U) : Q q L (x.res g) (Sec.res g s) := by
  intro W k v hv
  rw [sec_res_comp]
  exact hQ W (k ≫ g) v (by rwa [← sx_res_comp])

theorem Q_uniq {q : ℕ} [NeZero q] (hp : LateralTheory.EtaleFoundations.EtalePrimitiveRootsExistLocally) (hs : LateralTheory.EtaleFoundations.EtaleSheafSectionsSeparatedAndGlue)
    {E : Spc} {L : E ⟶ ofCat (glCat 1)} {U : Scheme.{0}} (hU : IsUnit (q : Γ(U, ⊤))) {x : Sx E 1 U} {s s'}
    (hQ : Q q L x s) (hQ' : Q q L x s') : s = s' := by
  apply (hs (ZMod q) ((res _ (tw q 1)).X 1) U).1
  refine loc_mono ((hp q U).2.2.2 hU (lineUnit L x)) ?_
  rintro V g ⟨v, hv⟩
  have hv' : v ^ q = lineUnit L (x.res g) := by rw [lineUnit_res]; exact hv
  rw [hQ V g v hv', hQ' V g v hv']

theorem Q_ex {q : ℕ} [NeZero q] (hp : LateralTheory.EtaleFoundations.EtalePrimitiveRootsExistLocally) (hk : IsKum q (kumT q))
    (hs : LateralTheory.EtaleFoundations.EtaleSheafSectionsSeparatedAndGlue)
    {E : Spc} (L : E ⟶ ofCat (glCat 1)) {U : Scheme.{0}} (hU : IsUnit (q : Γ(U, ⊤))) (x : Sx E 1 U) :
    ∃ s, Q q L x s := by
  obtain ⟨S, hS, hr⟩ := (hp q U).2.2.2 hU (lineUnit L x)
  choose vs hvs using hr
  obtain ⟨s, hs'⟩ := (hs (ZMod q) ((res _ (tw q 1)).X 1) U).2 S hS (fun V g hg => dkT q V (vs V g hg)) (by
    intro V W g k hg
    rw [kT_nat hk (isUnit_res hU g)]
    apply indep hp hk hs (isUnit_res hU (k ≫ g))
    rw [← map_pow, hvs V g hg, units_map_comp, hvs W (k ≫ g) _])
  refine ⟨s, fun V g v hv => ?_⟩
  apply (hs (ZMod q) ((res _ (tw q 1)).X 1) V).1
  refine loc_mono (P := fun W h => S.arrows (h ≫ g))
    ⟨S.pullback g, Scheme.etaleTopology.pullback_stable g hS, fun W h hh => hh⟩ ?_
  intro W h hh
  rw [sec_res_comp, hs' W (h ≫ g) hh, kT_nat hk (isUnit_res hU g)]
  apply indep hp hk hs (isUnit_res hU (h ≫ g))
  rw [hvs, ← map_pow, hv, lineUnit_res, units_map_comp]

end LateralTheory.EtaleFoundations.V1

open LateralTheory.EtaleFoundations.V1 in
theorem LateralTheory.EtaleFoundations.exists_natural_etale_kummer_degree_one_value_of_roots_kummer_gluing (hp : LateralTheory.EtaleFoundations.EtalePrimitiveRootsExistLocally) (hk : LateralTheory.EtaleFoundations.EtaleKummerTriangleExists)
    (hs : LateralTheory.EtaleFoundations.EtaleSheafSectionsSeparatedAndGlue) : LateralTheory.EtaleFoundations.ExistsNaturalEtaleKummerChernClassDegreeOneValue := by
  classical
  intro q _ E L hi
  have hU : ∀ (U : Scheme.{0}) (x : Sx E 1 U), IsUnit (q : Γ(U, ⊤)) := fun U x => hi U ⟨x.face 0⟩
  have hex : ∀ (U : Scheme.{0}) (x : Sx E 1 U), ∃ s, Q q L x s := fun U x => Q_ex hp (hk q) hs L (hU U x) x
  refine ⟨fun U x => (hex U x).choose, fun V U g x =>
    Q_uniq hp hs (hU V (x.res g)) (Q_res (hex U x).choose_spec g) (hex V (x.res g)).choose_spec, fun U x v hv => ?_⟩
  have h := (hex U x).choose_spec U (𝟙 U) v (by rwa [sx_res_id])
  rwa [sec_res_id] at h
end

section -- merged from Development.EtaleCohomology.TateTwists.TwSecLocPfZarR
section -- merged from Development.EtaleCohomology.TateTwists.TwSecLocPfR
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite TensorProduct GlobalTheory.EtC GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec

namespace LateralTheory.EtaleFoundations.TwSecLocPf

theorem loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hPQ : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun V g hg => hPQ V g (hP V g hg)⟩

theorem loc_true (U : Scheme.{0}) : Loc U fun _ _ => True :=
  ⟨⊤, Scheme.etaleTopology.top_mem U, fun _ _ _ => trivial⟩

theorem loc_and {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P) (hQ : Loc U Q) :
    Loc U fun V g => P V g ∧ Q V g := by
  obtain ⟨S, hS, hS'⟩ := hP
  obtain ⟨T, hT, hT'⟩ := hQ
  exact ⟨S ⊓ T, Scheme.etaleTopology.intersection_covering hS hT, fun V g hg => ⟨hS' V g hg.1, hT' V g hg.2⟩⟩

theorem loc_bind {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} {Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop}
    (hP : Loc U P) (hQ : ∀ V (g : V ⟶ U), P V g → Loc V fun W h => Q W (h ≫ g)) : Loc U Q := by
  obtain ⟨S, hS, hS'⟩ := hP
  choose T hT hT' using fun V (g : V ⟶ U) (hg : S.arrows g) => hQ V g (hS' V g hg)
  refine ⟨Sieve.bind S.arrows T, Scheme.etaleTopology.bind_covering hS hT, ?_⟩
  rintro W _ ⟨V, h, g, hg, hh, rfl⟩
  exact hT' V g hg W h hh

theorem loc_surj {R : Type} [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) (U : Scheme.{0})
    (y : Sec (ofRings R M) U) :
    Loc U fun V g => ∃ x : M.obj Γ(V, ⊤), Sec.res g y = ofRings.sec M V x := by
  have h := Presheaf.imageSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)) y
  refine ⟨_, h, fun V g hg => ?_⟩
  obtain ⟨x, hx⟩ := hg
  exact ⟨x, hx.symm⟩

end LateralTheory.EtaleFoundations.TwSecLocPf

namespace LateralTheory.EtaleFoundations.TwSecLocPf

def ZarPow : Prop := ∀ (q : ℕ) [NeZero q] (V : Scheme.{0}) (ζ ξ : Prim q Γ(V, ⊤)),
  Loc V fun W h => ∃ a : (ZMod q)ˣ, (ξ.map h.appTop.hom).1 = (ζ.map h.appTop.hom).1 ^ (a : ZMod q).val

theorem ulift_smul_eq_nsmul {q : ℕ} [NeZero q] {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M]
    (r : ULift.{1} (ZMod q)) (m : M) : r • m = r.down.val • m := by
  have : r = ((r.down.val : ℕ) : ULift.{1} (ZMod q)) := by
    cases r with
    | up a =>
      change ULift.up a = ULift.up ((a.val : ℕ) : ZMod q)
      rw [ZMod.natCast_zmod_val]
  conv_lhs => rw [this]
  exact Nat.cast_smul_eq_nsmul _ _ _

theorem twF_map_mk (q : ℕ) (i : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B) (x : Prim q A →₀ ULift.{1} (ZMod q)) :
    ((twF q i).map f).hom (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map f.hom) x) : (twF q i).obj B) := rfl

theorem twF_single_pow (q : ℕ) [NeZero q] (i : ℤ) (A : CommRingCat.{0}) (ζ ξ : Prim q A) (a : (ZMod q)ˣ)
    (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) (b : ULift.{1} (ZMod q)) :
    (Submodule.Quotient.mk (Finsupp.single ξ b) : (twF q i).obj A) =
      (b.down * ((a ^ i : (ZMod q)ˣ) : ZMod q)).val • (Submodule.Quotient.mk (Finsupp.single ζ 1) : (twF q i).obj A) := by
  have hrel : (Submodule.Quotient.mk (Finsupp.single ξ 1) : (twF q i).obj A) =
      Submodule.Quotient.mk (Finsupp.single ζ (ULift.up ((a ^ i : (ZMod q)ˣ) : ZMod q))) :=
    (Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨ζ, ξ, a, h, rfl⟩)
  have e1 : Finsupp.single ξ b = b • Finsupp.single ξ (1 : ULift.{1} (ZMod q)) := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  have e2 : Finsupp.single ζ (ULift.up ((a ^ i : (ZMod q)ˣ) : ZMod q)) =
      (ULift.up ((a ^ i : (ZMod q)ˣ) : ZMod q)) • Finsupp.single ζ (1 : ULift.{1} (ZMod q)) := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [e1, Submodule.Quotient.mk_smul, hrel, e2, Submodule.Quotient.mk_smul, smul_smul]
  exact ulift_smul_eq_nsmul _ _

theorem twF_loc (hZ : ZarPow) (q : ℕ) [NeZero q] (i : ℤ) (V : Scheme.{0}) (ζ : Prim q Γ(V, ⊤))
    (x : (twF q i).obj Γ(V, ⊤)) :
    Loc V fun W h => ∃ c : ℕ, ((twF q i).map h.appTop).hom x =
      c • (Submodule.Quotient.mk (Finsupp.single (ζ.map h.appTop.hom) 1) : (twF q i).obj Γ(W, ⊤)) := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  induction f using Finsupp.induction with
  | zero =>
    refine loc_mono (loc_true V) fun W h _ => ⟨0, ?_⟩
    rw [zero_smul, Submodule.Quotient.mk_zero]
    exact map_zero ((twF q i).map h.appTop).hom
  | single_add ξ b g _ _ ih =>
    refine loc_mono (loc_and (hZ q V ζ ξ) ih) fun W h ⟨⟨a, ha⟩, ⟨c, hc⟩⟩ =>
      ⟨(b.down * ((a ^ i : (ZMod q)ˣ) : ZMod q)).val + c, ?_⟩
    rw [Submodule.Quotient.mk_add]
    refine (map_add ((twF q i).map h.appTop).hom _ _).trans ?_
    rw [hc, twF_map_mk, Finsupp.mapDomain_single,
      twF_single_pow q i _ _ _ a ha b, add_smul]
    rfl

theorem TwSecLoc_of (hZ : ZarPow) : LateralTheory.EtaleFoundations.TwLocPf.TwSecLoc := by
  intro q _ i U ζ y
  refine loc_bind (loc_surj (twF q i) U y) fun V g ⟨x, hx⟩ => ?_
  refine loc_mono (twF_loc hZ q i V (ζ.map g.appTop.hom) x) fun W h ⟨c, hc⟩ => ⟨c, ?_⟩
  have e : Sec.res (h ≫ g) y = Sec.res h (Sec.res g y) := by
    simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  have hp : (ζ.map g.appTop.hom).map h.appTop.hom = ζ.map (h ≫ g).appTop.hom := by
    apply Subtype.ext
    simp [Prim.map]
    rfl
  rw [e]
  refine (congrArg (fun z => ((tw q i).obj.map h.op).hom z) hx).trans ?_
  have hres : Sec.res h (ofRings.sec (twF q i) V x) =
      ofRings.sec (twF q i) W (((twF q i).map h.appTop).hom x) := by
    have hn := congrArg (fun f => f.hom x)
      ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).naturality h.op)
    simp only [ModuleCat.hom_comp] at hn
    exact hn.symm
  refine hres.trans ?_
  rw [hc, ← hp]
  unfold twGen ofRings.sec
  exact map_nsmul _ _ _

end LateralTheory.EtaleFoundations.TwSecLocPf
end
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite TensorProduct GlobalTheory.EtC GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec

namespace LateralTheory.EtaleFoundations.TwSecLocPf

def AlgPow : Prop := ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] (ζ ξ : Prim q A),
  ∃ s : Set A, Ideal.span s = ⊤ ∧ ∀ f ∈ s, ∃ (a : (ZMod q)ˣ) (n : ℕ), f ^ n * (ξ.1 - ζ.1 ^ (a : ZMod q).val) = 0

theorem ZarPow_of (hA : AlgPow) : ZarPow := by
  intro q _ V ζ ξ
  obtain ⟨s, hs, hf⟩ := hA q Γ(V, ⊤) ζ ξ
  let U : s → V.Opens := fun f => V.basicOpen f.1
  have hU : TopologicalSpace.IsOpenCover U := by
    unfold TopologicalSpace.IsOpenCover
    have h := iSup_basicOpen_of_span_eq_top ⊤ s hs
    show ⨆ f : s, V.basicOpen f.1 = ⊤
    rw [iSup_subtype]
    exact h
  let 𝒰 := V.openCoverOfIsOpenCover U hU
  refine ⟨Sieve.generate (Presieve.ofArrows 𝒰.X 𝒰.f),
    Scheme.zariskiTopology_le_etaleTopology _ (Scheme.mem_grothendieckTopology_iff.2 ⟨𝒰, Sieve.le_generate _⟩), ?_⟩
  rintro W g ⟨Y, h, _, ⟨i⟩, rfl⟩
  obtain ⟨a, n, hn⟩ := hf i.1 i.2
  refine ⟨a, ?_⟩
  have hle : (U i).ι ''ᵁ ⊤ ≤ V.basicOpen i.1 := by simp [U]
  have hu : IsUnit ((U i).ι.appTop.hom i.1) := by
    have := (V.toRingedSpace.isUnit_res_basicOpen i.1).map (V.presheaf.map (homOfLE hle).op).hom
    have e : V.presheaf.map (homOfLE (x := (U i).ι ''ᵁ ⊤) (y := ⊤) le_top).op =
        V.presheaf.map (homOfLE (V.basicOpen_le i.1)).op ≫ V.presheaf.map (homOfLE hle).op := by
      rw [← Functor.map_comp]; rfl
    rw [Scheme.Opens.ι_appTop, e]
    exact this
  have key : (U i).ι.appTop.hom ξ.1 = ((U i).ι.appTop.hom ζ.1) ^ (a : ZMod q).val := by
    have h0 : (U i).ι.appTop.hom (i.1 ^ n * (ξ.1 - ζ.1 ^ (a : ZMod q).val)) = 0 := by rw [hn, map_zero]
    rw [map_mul, map_pow, map_sub, map_pow] at h0
    exact sub_eq_zero.1 ((hu.pow n).mul_right_eq_zero.1 h0)
  have hc : ∀ x, (h ≫ (U i).ι).appTop.hom x = h.appTop.hom ((U i).ι.appTop.hom x) := fun x => by
    rfl
  show (h ≫ (U i).ι).appTop.hom ξ.1 = ((h ≫ (U i).ι).appTop.hom ζ.1) ^ _
  rw [hc, hc, key]
  exact map_pow _ _ _

theorem TwSecLoc_of_alg (hA : AlgPow) : LateralTheory.EtaleFoundations.TwLocPf.TwSecLoc := TwSecLoc_of (ZarPow_of hA)

end LateralTheory.EtaleFoundations.TwSecLocPf
end
end

section -- merged from Development.EtaleCohomology.TateTwists.TPaTensExPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped DirectSum TensorProduct

namespace LateralTheory.EtaleFoundations.TensEx
variable {R : Type} [CommRing R]

abbrev Jt := Scheme.etaleTopology.{0}
abbrev MC (R : Type) [CommRing R] := ModuleCat.{1} (ULift.{1} R)
abbrev Ix (w : ℤ) := {p : ℤ × ℤ // p.1 + p.2 = w}

theorem sec_nat {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (a : Sec F U) :
    Sec.map φ (Sec.res g a) = Sec.res g (Sec.map φ a) :=
  congrArg (fun f => ModuleCat.Hom.hom f a) (φ.hom.naturality g.op)

theorem tres_lof (I J : Cx R) {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (p : Ix w)
    (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) :
    Tens.res (I := I) (J := J) g w (DirectSum.lof (ULift.{1} R) _ _ p (a ⊗ₜ b)) =
      DirectSum.lof (ULift.{1} R) _ _ p (Sec.res g a ⊗ₜ Sec.res g b) := by
  simp [Tens.res, DirectSum.lmap_lof]

def TP (I J : Cx R) (w : ℤ) : Scheme.{0}ᵒᵖ ⥤ MC R where
  obj U := ModuleCat.of _ (Tens I J U.unop w)
  map g := ModuleCat.ofHom (Tens.res g.unop w)
  map_id U := by
    apply ModuleCat.hom_ext; apply DirectSum.linearMap_ext; intro p; apply TensorProduct.ext'; intro a b
    simp only [ModuleCat.hom_ofHom, LinearMap.comp_apply, unop_id, tres_lof, ModuleCat.hom_id, LinearMap.id_apply]
    simp [Sec.res]
  map_comp f g := by
    apply ModuleCat.hom_ext; apply DirectSum.linearMap_ext; intro p; apply TensorProduct.ext'; intro a b
    simp only [ModuleCat.hom_ofHom, LinearMap.comp_apply, unop_comp, tres_lof, ModuleCat.hom_comp]
    simp [Sec.res]

def dc (I J : Cx R) (U : Scheme.{0}) (w : ℤ) (p : Ix w) :
    Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U →ₗ[ULift.{1} R] Tens I J U (w + 1) :=
  DirectSum.lof (ULift.{1} R) _ (fun q : Ix (w + 1) => Sec (I.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U)
      ⟨(p.1.1 + 1, p.1.2), by have := p.2; simp only; omega⟩ ∘ₗ
    TensorProduct.map ((I.d p.1.1 (p.1.1 + 1)).hom.app (op U)).hom LinearMap.id +
  ((p.1.1.negOnePow : ℤ) • (DirectSum.lof (ULift.{1} R) _ (fun q : Ix (w + 1) => Sec (I.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U)
      ⟨(p.1.1, p.1.2 + 1), by have := p.2; simp only; omega⟩ ∘ₗ
    TensorProduct.map LinearMap.id ((J.d p.1.2 (p.1.2 + 1)).hom.app (op U)).hom))

def dT (I J : Cx R) (U : Scheme.{0}) (w : ℤ) : Tens I J U w →ₗ[ULift.{1} R] Tens I J U (w + 1) :=
  DirectSum.toModule _ _ _ (dc I J U w)

theorem dT_lof (I J : Cx R) (U : Scheme.{0}) (w : ℤ) (p : Ix w) (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) :
    dT I J U w (DirectSum.lof (ULift.{1} R) _ _ p (a ⊗ₜ b)) =
      DirectSum.lof (ULift.{1} R) _ (fun q : Ix (w + 1) => Sec (I.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U)
        ⟨(p.1.1 + 1, p.1.2), by have := p.2; simp only; omega⟩ (Sec.map (I.d p.1.1 (p.1.1 + 1)) a ⊗ₜ b) +
      (p.1.1.negOnePow : ℤ) • DirectSum.lof (ULift.{1} R) _ (fun q : Ix (w + 1) => Sec (I.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U)
        ⟨(p.1.1, p.1.2 + 1), by have := p.2; simp only; omega⟩ (a ⊗ₜ Sec.map (J.d p.1.2 (p.1.2 + 1)) b) := by
  simp [dT, dc, DirectSum.toModule_lof]

theorem dT_res (I J : Cx R) {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) :
    dT I J V w ∘ₗ Tens.res g w = Tens.res g (w + 1) ∘ₗ dT I J U w := by
    apply DirectSum.linearMap_ext; intro p; apply TensorProduct.ext'; intro a b
    simp only [LinearMap.comp_apply]
    rw [tres_lof, dT_lof, dT_lof, map_add (f := _), map_zsmul, tres_lof, tres_lof, sec_nat, sec_nat]

def dP (I J : Cx R) (w : ℤ) : TP I J w ⟶ TP I J (w + 1) where
  app U := ModuleCat.ofHom (dT I J U.unop w)
  naturality U V g := ModuleCat.hom_ext (dT_res I J g.unop w)

end LateralTheory.EtaleFoundations.TensEx

namespace LateralTheory.EtaleFoundations.TensEx
variable {R : Type} [CommRing R]

theorem sec_dd (K : Cx R) (h i j : ℤ) {U : Scheme.{0}} (a : Sec (K.X h) U) :
    Sec.map (K.d i j) (Sec.map (K.d h i) a) = 0 := by
  change Sec.map (K.d h i ≫ K.d i j) a = 0
  rw [K.d_comp_d]
  rfl

theorem dT_dT (I J : Cx R) (U : Scheme.{0}) (w : ℤ) (x : Tens I J U w) :
    dT I J U (w + 1) (dT I J U w x) = 0 := by
  rw [← LinearMap.comp_apply (f := dT I J U (w + 1))]
  suffices h : dT I J U (w + 1) ∘ₗ dT I J U w = 0 by rw [h]; rfl
  apply DirectSum.linearMap_ext; intro p; apply TensorProduct.ext'; intro a b
  simp only [LinearMap.comp_apply, LinearMap.zero_apply]
  rw [dT_lof, map_add (f := _), map_zsmul, dT_lof, dT_lof]
  simp only [sec_dd, TensorProduct.zero_tmul, TensorProduct.tmul_zero, map_zero, zero_add, add_zero, smul_add,
    smul_zero, Int.negOnePow_succ, Units.val_neg, neg_smul, smul_smul]
  exact neg_add_cancel _

theorem tensorDifferential_comp_eq_zero (I J : Cx R) (w : ℤ) : dP I J w ≫ dP I J (w + 1) = 0 := by
  ext U : 2
  apply ModuleCat.hom_ext; apply LinearMap.ext; intro x
  exact dT_dT I J U.unop w x

def T (I J : Cx R) : Cx R :=
  CochainComplex.of (fun w => (presheafToSheaf Jt (MC R)).obj (TP I J w))
    (fun w => (presheafToSheaf Jt (MC R)).map (dP I J w))
    (fun w => by rw [← Functor.map_comp, tensorDifferential_comp_eq_zero, Functor.map_zero])

theorem T_d (I J : Cx R) (w : ℤ) : (T I J).d w (w + 1) = (presheafToSheaf Jt (MC R)).map (dP I J w) :=
  by unfold T; simp [CochainComplex.of]

theorem toS_res (P : Scheme.{0}ᵒᵖ ⥤ MC R) {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    ((sheafify Jt P).map g.op).hom (((toSheafify Jt P).app (op U)).hom x) =
      ((toSheafify Jt P).app (op V)).hom ((P.map g.op).hom x) :=
  (congrArg (fun f => ModuleCat.Hom.hom f x) ((toSheafify Jt P).naturality g.op)).symm

theorem toS_map {P Q : Scheme.{0}ᵒᵖ ⥤ MC R} (η : P ⟶ Q) {U : Scheme.{0}} (x : P.obj (op U)) :
    ((sheafifyMap Jt η).app (op U)).hom (((toSheafify Jt P).app (op U)).hom x) =
      ((toSheafify Jt Q).app (op U)).hom ((η.app (op U)).hom x) :=
  (congrArg (fun f => ModuleCat.Hom.hom (NatTrans.app f (op U)) x) (toSheafify_naturality Jt η)).symm

def tS (I J : Cx R) (U : Scheme.{0}) (w : ℤ) : Tens I J U w →ₗ[ULift.{1} R] Sec ((T I J).X w) U :=
  ((toSheafify Jt (TP I J w)).app (op U)).hom

def mulT (I J : Cx R) (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) :
    Sec (I.X s) U →ₗ[ULift.{1} R] Sec (J.X t) U →ₗ[ULift.{1} R] Sec ((T I J).X w) U :=
  (TensorProduct.mk (ULift.{1} R) _ _).compr₂
    (tS I J U w ∘ₗ
      DirectSum.lof (ULift.{1} R) (Ix w) (fun p => Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) ⟨(s, t), h⟩)

theorem mulT_apply (I J : Cx R) (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) a b :
    mulT I J U s t w h a b = tS I J U w
      (DirectSum.lof (ULift.{1} R) (Ix w) (fun p => Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) ⟨(s, t), h⟩ (a ⊗ₜ b)) :=
  rfl

def tau (I J : Cx R) : Pair I J (T I J) where
  mul := mulT I J
  nat g s t w h a b := by
    rw [mulT_apply, mulT_apply]
    exact (toS_res (TP I J w) g _).trans (congrArg _ (tres_lof I J g w ⟨(s, t), h⟩ a b))
  leibniz U s t w h a b := by
    rw [mulT_apply, mulT_apply, mulT_apply, T_d]
    refine Eq.trans (toS_map (dP I J w) _) ?_
    show tS I J U (w + 1) (dT I J U w _) = tS I J U (w + 1) _ + s.negOnePow • tS I J U (w + 1) _
    rw [dT_lof, map_add (f := _), map_zsmul, Units.smul_def]

theorem tau_lift (I J : Cx R) (U : Scheme.{0}) (w : ℤ) :
    (tau I J).lift U w = tS I J U w := by
  apply DirectSum.linearMap_ext; intro p; apply TensorProduct.ext'; intro a b
  simp only [Pair.lift, LinearMap.comp_apply, DirectSum.toModule_lof, TensorProduct.lift.tmul]
  rfl

theorem tau_isTensor (I J : Cx R) : (tau I J).IsTensor := by
  constructor
  · intro U w y
    refine ⟨_, Presheaf.imageSieve_mem Jt (toSheafify Jt (TP I J w)) (U := op U) y, ?_⟩
    intro V g hg
    obtain ⟨x, hx⟩ := hg
    exact ⟨x, by rw [tau_lift]; exact hx⟩
  · intro U w x hx
    rw [tau_lift] at hx
    refine ⟨_, Presheaf.equalizerSieve_mem Jt (toSheafify Jt (TP I J w)) (X := op U) x 0
      (by rw [map_zero]; exact hx), ?_⟩
    intro V g hg
    have : (TP I J w).map g.op x = (TP I J w).map g.op 0 := hg
    rw [map_zero] at this
    exact this

end LateralTheory.EtaleFoundations.TensEx

namespace LateralTheory.EtaleFoundations

theorem t_pa_tens_ex_of : t_pa_tens_ex := by
  intro R _ I J
  exact ⟨TensEx.T I J, TensEx.tau I J, TensEx.tau_isTensor I J⟩

end LateralTheory.EtaleFoundations
end
end
