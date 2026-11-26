module

public import Development.EtaleCohomology.TateTwists.EtaleTateTwistGeneratorMapInjectiveOfSectionsGlu
public import Development.EtaleCohomology.TateTwists.EtaleLocallyExistsPrimitiveRootOfUnityOfInvertibleOrder

@[expose] public section

section -- merged from Development.EtaleCohomology.TateTwists.EtaleTateTwistLocalGenerationAndRootCompatOfPart
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

def LateralTheory.EtaleFoundations.EtaleTateTwistSectionsLocallyMultiplesOfGenerator : Prop :=
  ∀ (q : ℕ) [NeZero q] (i : ℤ) (U : Scheme.{0}) (a : Sec (tw q i) U),
    Loc U fun V g => Sec.res g a = 0 ∨ ∃ (ζ : Prim q Γ(V, ⊤)) (c : ℕ), Sec.res g a = c • twGen i ζ

def LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorRestrictionAndRootChange : Prop :=
  ∀ (q : ℕ) [NeZero q] (j : ℤ),
    (∀ (V U : Scheme.{0}) (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)), Sec.res g (twGen j ζ) = twGen j (ζ.map g.appTop.hom)) ∧
    ∀ (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)), Loc U fun _ g => ∃ c : ℕ, Sec.res g (twGen j ξ) = c • twGen j (ζ.map g.appTop.hom)

namespace LateralTheory.EtaleFoundations.GenIsoSurjPf
theorem res_nsmul {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (c : ℕ) (x : Sec F U) :
    Sec.res g (c • x) = c • Sec.res g x := by
  simp [Sec.res]

theorem map_nsmul' {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (c : ℕ) (x : Sec F U) :
    Sec.map φ (c • x) = c • Sec.map φ x := by
  simp [Sec.map]
end LateralTheory.EtaleFoundations.GenIsoSurjPf

open LateralTheory.EtaleFoundations.GenIsoSurjPf in
theorem LateralTheory.EtaleFoundations.etale_tate_twist_generator_map_hits_products_locally (hl : LateralTheory.EtaleFoundations.EtaleTateTwistSectionsLocallyMultiplesOfGenerator)
    (hr : LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorRestrictionAndRootChange) : LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorMapHitsProductsLocally := by
  intro q _ i j k T μ hk φ hφ U a b
  refine loc_bind' (loc_mono' (loc_and' (hl q i U a) (hl q j U b)) fun V g hab => ?_)
  rcases hab with ⟨ha | ⟨ζ, c, ha⟩, hb | ⟨ξ, d, hb⟩⟩
  · exact loc_top' fun W h => ⟨0, by rw [← res_res, ha]; simp⟩
  · exact loc_top' fun W h => ⟨0, by rw [← res_res, ha]; simp⟩
  · exact loc_top' fun W h => ⟨0, by rw [← res_res (F := tw q j), hb]; simp⟩
  · refine loc_mono' ((hr q j).2 V ζ ξ) fun W h ⟨e, he⟩ => ?_
    refine ⟨(c * (d * e)) • twGen k (ζ.map h.appTop.hom), ?_⟩
    rw [← res_res, ← res_res (F := tw q j), ha, hb, res_nsmul, res_nsmul, he, (hr q i).1, smul_smul,
      map_nsmul', map_nsmul', map_nsmul', map_nsmul', hφ]
    simp only [map_nsmul, LinearMap.smul_apply, smul_smul]
    ring_nf

theorem LateralTheory.EtaleFoundations.etale_tate_twist_generator_map_surjective_of_local_and_root (hl : LateralTheory.EtaleFoundations.EtaleTateTwistSectionsLocallyMultiplesOfGenerator)
    (hr : LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorRestrictionAndRootChange) : LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorMapLocallySurjective :=
  LateralTheory.EtaleFoundations.etale_tate_twist_generator_map_locally_surjective_of_pairs (LateralTheory.EtaleFoundations.etale_tate_twist_generator_map_hits_products_locally hl hr)
end
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleSheafRestrictScalarsFunctorExactOfAdjoints
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

lemma restr_isRightAdjoint (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) :
    (restr φ).IsRightAdjoint := by
  unfold restr
  exact (Sheaf.adjunction Scheme.etaleTopology.{0} (ModuleCat.extendRestrictScalarsAdj.{1, 1, 1}
    ((ULift.ringEquiv.symm : S ≃+* ULift.{1} S).toRingHom.comp (φ.comp (ULift.ringEquiv : ULift.{1} R ≃+* R).toRingHom)))).isRightAdjoint

lemma restr_isLeftAdjoint (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) :
    (restr φ).IsLeftAdjoint := by
  unfold restr
  set f := ((ULift.ringEquiv.symm : S ≃+* ULift.{1} S).toRingHom.comp (φ.comp (ULift.ringEquiv : ULift.{1} R ≃+* R).toRingHom))
  have hpl : PreservesLimitsOfSize.{0, 1} (ModuleCat.coextendScalars.{1, 1, 1} f) :=
    (ModuleCat.restrictCoextendScalarsAdj.{1, 1, 1} f).rightAdjoint_preservesLimits
  have : Scheme.etaleTopology.{0}.HasSheafCompose (ModuleCat.coextendScalars.{1, 1, 1} f) :=
    hasSheafCompose_of_preservesLimitsOfSize _
  have adj := Sheaf.adjunction Scheme.etaleTopology.{0} (ModuleCat.restrictCoextendScalarsAdj.{1, 1, 1} f)
  have := (sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).counit_isIso_of_R_fully_faithful
  have e : Sheaf.composeAndSheafify Scheme.etaleTopology.{0} (ModuleCat.restrictScalars.{1} f) ≅
      sheafCompose Scheme.etaleTopology.{0} (ModuleCat.restrictScalars.{1} f) :=
    NatIso.ofComponents (fun X => (asIso (sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).counit).app
      ((sheafCompose Scheme.etaleTopology.{0} (ModuleCat.restrictScalars.{1} f)).obj X)) (by
        intro X Y g
        exact (sheafificationAdjunction _ _).counit.naturality
          ((sheafCompose Scheme.etaleTopology.{0} (ModuleCat.restrictScalars.{1} f)).map g))
  exact ⟨_, ⟨adj.ofNatIsoLeft e⟩⟩

theorem etaleSheaf_restrictScalars_functor_exact_of_adjoints : EtaleSheafRestrictScalarsFunctorExact := by
  intro R S _ _ φ
  have := restr_isRightAdjoint R S φ
  have := restr_isLeftAdjoint R S φ
  exact ⟨inferInstance, inferInstance⟩

end LateralTheory.EtaleFoundations
end

section -- merged from Development.EtaleCohomology.TateTwists.Imports
section -- merged from Development.EtaleCohomology.TateTwists.EtaleCohomologyEvaluationConnectingHom
namespace LateralTheory.Fin.EtaleCochainSemilinearMapOnClasses
theorem etale_evaluation_map_basic_of_components : LateralTheory.EtaleFoundations.pp_ev_basic := by
  apply LateralTheory.EtaleFoundations.pp_ev_basic_of
theorem etale_cohomology_evaluation_mk : LateralTheory.EtaleFoundations.pp_ev_mk := by
  apply LateralTheory.EtaleFoundations.pp_ev_mk_of
theorem etale_cohomology_evaluation_connecting_hom : LateralTheory.EtaleFoundations.pp_ev_delta := by
  apply LateralTheory.EtaleFoundations.pp_ev_delta_of
theorem etale_torsion_cohomology_operation_spec : LateralTheory.EtaleFoundations.EtaleCochainSemilinearMapOnClasses := by
  apply LateralTheory.EtaleFoundations.etale_semilinear_cohomology_operation_exists_of_evaluation <;> first | exact etale_evaluation_map_basic_of_components | exact etale_cohomology_evaluation_mk | exact etale_cohomology_evaluation_connecting_hom
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleCochainSemilinearMapOnClasses := etale_torsion_cohomology_operation_spec
end LateralTheory.Fin.EtaleCochainSemilinearMapOnClasses
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleSemilinearCohomologyOperationImageSpecOfHyp
section -- merged from Development.EtaleCohomology.TateTwists.EtaleCohomologyOperationCompOfImageSpec
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def EtaleSemilinearCohomologyOperationImageSpec : Prop :=
  ∀ (S R : Type) [CommRing S] [CommRing R] {I : Cx S} {J : Cx R} (ρ : SemiMap I J),
    (∀ (E : Spc) (n : ℤ) (α : Cocycle ((chains S).obj E) I n), ∃ β : Cocycle ((chains R).obj E) J n, ρ.IsImage α.1 β.1) ∧
    ∀ (E : Spc) (n : ℤ) (α : Cocycle ((chains S).obj E) I n) (β : Cocycle ((chains R).obj E) J n),
      ρ.IsImage α.1 β.1 → ρ.op.app E n (CohomologyClass.mk α) = CohomologyClass.mk β

namespace OpCompPf

theorem ev_comp_ofHom {R : Type} [CommRing R] {E : Spc} {I J : Cx R} {n : ℤ} (m : I ⟶ J)
    (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (α.comp (Cochain.ofHom m) (add_zero n)) p s h U x = Sec.map (m.f s) (ev α p s h U x) := by
  simp only [ev, Cochain.comp_zero_cochain_v, Cochain.ofHom_v]
  rfl

noncomputable def invMap {S R : Type} [CommRing S] [CommRing R] {I : Cx S} {J : Cx R} (ρ : SemiMap I J)
    (hb : ∀ (U : Scheme.{0}) (s : ℤ), Function.Bijective (ρ.app U s)) : SemiMap J I where
  app U s := (AddEquiv.ofBijective (ρ.app U s) (hb U s)).symm.toAddMonoidHom
  nat {V U} g s a := by
    apply (hb V s).1
    have h1 := ρ.nat g s ((AddEquiv.ofBijective (ρ.app U s) (hb U s)).symm a)
    have h2 : ρ.app U s ((AddEquiv.ofBijective (ρ.app U s) (hb U s)).symm a) = a :=
      (AddEquiv.ofBijective (ρ.app U s) (hb U s)).apply_symm_apply a
    have h3 : ρ.app V s ((AddEquiv.ofBijective (ρ.app V s) (hb V s)).symm (Sec.res g a)) = Sec.res g a :=
      (AddEquiv.ofBijective (ρ.app V s) (hb V s)).apply_symm_apply _
    simp only [AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass]
    rw [h3, ← h1, h2]
  comm U s t a := by
    apply (hb U t).1
    have h1 := ρ.comm U s t ((AddEquiv.ofBijective (ρ.app U s) (hb U s)).symm a)
    have h2 : ρ.app U s ((AddEquiv.ofBijective (ρ.app U s) (hb U s)).symm a) = a :=
      (AddEquiv.ofBijective (ρ.app U s) (hb U s)).apply_symm_apply a
    have h3 : ρ.app U t ((AddEquiv.ofBijective (ρ.app U t) (hb U t)).symm (Sec.map (J.d s t) a)) = Sec.map (J.d s t) a :=
      (AddEquiv.ofBijective (ρ.app U t) (hb U t)).apply_symm_apply _
    simp only [AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass]
    rw [h3, ← h1, h2]

theorem invMap_app {S R : Type} [CommRing S] [CommRing R] {I : Cx S} {J : Cx R} (ρ : SemiMap I J)
    (hb : ∀ (U : Scheme.{0}) (s : ℤ), Function.Bijective (ρ.app U s)) (U : Scheme.{0}) (s : ℤ) (a : Sec (J.X s) U) :
    ρ.app U s ((invMap ρ hb).app U s a) = a :=
  (AddEquiv.ofBijective (ρ.app U s) (hb U s)).apply_symm_apply a

theorem app_invMap {S R : Type} [CommRing S] [CommRing R] {I : Cx S} {J : Cx R} (ρ : SemiMap I J)
    (hb : ∀ (U : Scheme.{0}) (s : ℤ), Function.Bijective (ρ.app U s)) (U : Scheme.{0}) (s : ℤ) (a : Sec (I.X s) U) :
    (invMap ρ hb).app U s (ρ.app U s a) = a :=
  (AddEquiv.ofBijective (ρ.app U s) (hb U s)).symm_apply_apply a

end OpCompPf

open OpCompPf in
theorem etale_cohomology_operation_comp_of_image_spec (hspec : EtaleSemilinearCohomologyOperationImageSpec) : EtaleCochainSemilinearMapCompCompatible := by
  intro S R _ _ I J J' ρ ρ' u hu
  constructor
  · intro E n x
    obtain ⟨α, rfl⟩ := x.mk_surjective
    obtain ⟨β, hβ⟩ := (hspec S R ρ).1 E n α
    rw [(hspec S R ρ).2 E n α β hβ, cpost_mk]
    apply (hspec S R ρ').2
    intro p s h U y
    show ev (β.1.comp (Cochain.ofHom u) (add_zero n)) p s h U y = _
    rw [ev_comp_ofHom, hβ p s h U y, hu]
  · intro hb E n
    let σ := invMap ρ hb
    rw [Function.bijective_iff_has_inverse]
    refine ⟨σ.op.app E n, ?_, ?_⟩
    · intro x
      obtain ⟨α, rfl⟩ := x.mk_surjective
      obtain ⟨β, hβ⟩ := (hspec S R ρ).1 E n α
      rw [(hspec S R ρ).2 E n α β hβ]
      apply (hspec R S σ).2
      intro p s h U y
      rw [hβ p s h U y]
      exact (app_invMap ρ hb U s _).symm
    · intro x
      obtain ⟨β, rfl⟩ := x.mk_surjective
      obtain ⟨γ, hγ⟩ := (hspec R S σ).1 E n β
      rw [(hspec R S σ).2 E n β γ hγ]
      apply (hspec S R ρ).2
      intro p s h U y
      rw [hγ p s h U y]
      exact (invMap_app ρ hb U s _).symm

end LateralTheory.EtaleFoundations
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

theorem etale_semilinear_cohomology_operation_image_spec_of_hyp
    (hImage₂ : ∀ (S R : Type) [CommRing S] [CommRing R] {I : Cx S} {J : Cx R} (ρ : SemiMap I J),
      (∀ (E : Spc) (n : ℤ) (α : Cocycle ((chains S).obj E) I n), ∃ β : Cocycle ((chains R).obj E) J n, ρ.IsImage α.1 β.1) ∧
      ∀ (E : Spc) (n : ℤ) (α : Cocycle ((chains S).obj E) I n) (β : Cocycle ((chains R).obj E) J n),
        ρ.IsImage α.1 β.1 → ρ.op.app E n (CohomologyClass.mk α) = CohomologyClass.mk β) :
    EtaleSemilinearCohomologyOperationImageSpec :=
  hImage₂

end LateralTheory.EtaleFoundations
end

theorem LateralTheory.Fix.EtaleCochainSemilinearMapCompCompatible.intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleCochainSemilinearMapCompCompatible :=
  LateralTheory.EtaleFoundations.etale_cohomology_operation_comp_of_image_spec
    (LateralTheory.EtaleFoundations.etale_semilinear_cohomology_operation_image_spec_of_hyp (by
      have h := LateralTheory.Fin.EtaleCochainSemilinearMapOnClasses.intersectionNumber_baseChange
      unfold LateralTheory.EtaleFoundations.EtaleCochainSemilinearMapOnClasses at h
      exact h))
end

section -- merged from Development.EtaleCohomology.TateTwists.TwpairTensUnivPf
section -- merged from Development.EtaleCohomology.TateTwists.TensorLocallyBijectiveHolds
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.TensLocbij

theorem loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hPQ : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun V g hg => hPQ V g (hP V g hg)⟩

theorem loc_and {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h1 : Loc U P)
    (h2 : Loc U Q) : Loc U (fun V g => P V g ∧ Q V g) := by
  obtain ⟨S, hS, hP⟩ := h1
  obtain ⟨T, hT, hQ⟩ := h2
  exact ⟨S ⊓ T, (Scheme.etaleTopology).intersection_covering hS hT,
    fun V g hg => ⟨hP V g hg.1, hQ V g hg.2⟩⟩

theorem map_comp_apply' (R : Type) [CommRing R] (P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R))
    {U V W : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (p : P.obj (op U)) :
    (P.map (k ≫ g).op).hom p = (P.map k.op).hom ((P.map g.op).hom p) := by
  simp [op_comp, Functor.map_comp]

end LateralTheory.EtaleFoundations.TensLocbij
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

theorem secmap_comp {R : Type} [CommRing R] {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map ψ (Sec.map φ x) = Sec.map (φ ≫ ψ) x := rfl

theorem secmap_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  have := congrArg (fun k => k.hom x) (φ.hom.naturality g.op)
  exact this.symm

noncomputable def pairPost {R : Type} [CommRing R] {I J K K' : Cx R} (μ : Pair I J K) (u : K ⟶ K') : Pair I J K' where
  mul U s t w h := (μ.mul U s t w h).compr₂ ((u.f w).hom.app (op U)).hom
  nat g s t w h a b := by
    simp only [LinearMap.compr₂_apply]
    rw [← μ.nat g s t w h a b]
    exact secmap_res (u.f w) g _
  leibniz U s t w h a b := by
    simp only [LinearMap.compr₂_apply]
    have hc : Sec.map (K'.d w (w + 1)) (Sec.map (u.f w) (μ.mul U s t w h a b)) =
        Sec.map (u.f (w + 1)) (Sec.map (K.d w (w + 1)) (μ.mul U s t w h a b)) := by
      rw [secmap_comp, secmap_comp, u.comm]
    show Sec.map (K'.d w (w + 1)) (Sec.map (u.f w) (μ.mul U s t w h a b)) = _
    rw [hc, μ.leibniz U s t w h a b]
    show Sec.map (u.f (w + 1)) _ = Sec.map (u.f (w + 1)) _ + _ • Sec.map (u.f (w + 1)) _
    rw [Sec.map, map_add (f := _), map_zsmul_unit]

def twpair_tens_univ_uniq : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (τ : Pair I J K), τ.IsTensor → ∀ {I' J' K' : Cx R} (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J') (u u' : K ⟶ K'), τ.Compat ν f g u → τ.Compat ν f g u' → u = u'

def twpair_tens_univ_ex : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (τ : Pair I J K), τ.IsTensor → ∀ {I' J' K' : Cx R} (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J'), ∃ u : K ⟶ K', τ.Compat ν f g u

def twpair_tens_univ_ge : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (τ : Pair I J K), τ.IsTensor → I.IsStrictlyGE 0 → J.IsStrictlyGE 0 → K.IsStrictlyGE 0

theorem pairPost_compat {R : Type} [CommRing R] {I J K K' : Cx R} (μ : Pair I J K) (u : K ⟶ K') :
    μ.Compat (pairPost μ u) (𝟙 I) (𝟙 J) u := by
  intro U s t w h a b
  rfl

theorem lift_comp_eq {R : Type} [CommRing R] {I J K I' J' K' : Cx R} (τ : Pair I J K) (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J') (u u' : K ⟶ K')
    (hu : τ.Compat ν f g u) (hu' : τ.Compat ν f g u') (V : Scheme.{0}) (w : ℤ) (x : Tens I J V w) :
    Sec.map (u.f w) (τ.lift V w x) = Sec.map (u'.f w) (τ.lift V w x) := by
  classical
  have key : ((u.f w).hom.app (op V)).hom ∘ₗ τ.lift V w = ((u'.f w).hom.app (op V)).hom ∘ₗ τ.lift V w := by
    apply DirectSum.linearMap_ext
    intro p
    apply TensorProduct.ext'
    intro a b
    simp only [LinearMap.comp_apply, Pair.lift, DirectSum.toModule_lof, TensorProduct.lift.tmul]
    exact (hu V _ _ _ p.2 a b).trans (hu' V _ _ _ p.2 a b).symm
  exact congrArg (fun k => k x) key

theorem tens_univ_uniq_of (hsep : LateralTheory.EtaleFoundations.EtaleTensorTripleProductLeibnizSeparated.SecSep) : twpair_tens_univ_uniq := by
  intro R _ I J K τ hτ I' J' K' ν f g u u' hu hu'
  ext w U y
  apply hsep R (K'.X w) U.unop
  refine TensLocbij.loc_mono (hτ.1 U.unop w y) ?_
  rintro V r ⟨x, hx⟩
  rw [secmap_res, secmap_res, ← hx]
  exact lift_comp_eq τ ν f g u u' hu hu' V w x

theorem sec_zero_of_isZero {R : Type} [CommRing R] {F : Shv R} (hF : IsZero F) {U : Scheme.{0}} (x : Sec F U) : x = 0 := by
  have h := hF.eq_of_src (𝟙 F) 0
  have : Sec.map (𝟙 F) x = Sec.map (0 : F ⟶ F) x := by rw [h]
  exact this

theorem isZero_of_sec {R : Type} [CommRing R] {F : Shv R} (h : ∀ (U : Scheme.{0}) (x : Sec F U), x = 0) : IsZero F := by
  rw [IsZero.iff_id_eq_zero]
  ext U y
  exact (h U.unop y).trans (h U.unop _).symm

theorem tens_univ_ge_of (hsep : LateralTheory.EtaleFoundations.EtaleTensorTripleProductLeibnizSeparated.SecSep) : twpair_tens_univ_ge := by
  intro R _ I J K τ hτ hI hJ
  have hK : ∀ w : ℤ, w < 0 → IsZero (K.X w) := by
    intro w hw
    apply isZero_of_sec
    intro U y
    apply hsep R (K.X w) U
    refine TensLocbij.loc_mono (hτ.1 U w y) ?_
    rintro V r ⟨x, hx⟩
    rw [← hx]
    classical
    have hl : τ.lift V w = 0 := by
      apply DirectSum.linearMap_ext
      intro p
      apply TensorProduct.ext'
      intro a b
      simp only [LinearMap.comp_apply, Pair.lift, DirectSum.toModule_lof, TensorProduct.lift.tmul, LinearMap.zero_apply]
      rcases lt_or_ge p.1.1 0 with hs | hs
      · rw [sec_zero_of_isZero (CochainComplex.isZero_of_isStrictlyGE I 0 p.1.1 hs) a, map_zero, LinearMap.zero_apply]
      · have ht : p.1.2 < 0 := by have := p.2; omega
        rw [sec_zero_of_isZero (CochainComplex.isZero_of_isStrictlyGE J 0 p.1.2 ht) b, map_zero]
    rw [hl, LinearMap.zero_apply]
    exact (map_zero _).symm
  exact ⟨fun i hi => hK i ((ComplexShape.notMem_range_embeddingUpIntGE_iff (p := 0) i).1 hi)⟩

theorem etale_sheaf_sections_separated_holds : LateralTheory.EtaleFoundations.EtaleTensorTripleProductLeibnizSeparated.SecSep := by
  intro R _ F U a b hab
  obtain ⟨S, hS, hP⟩ := hab
  have h1 : Presheaf.IsSheaf Scheme.etaleTopology.{0} (F.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) :=
    Presheaf.isSheaf_comp_of_isSheaf _ _ _ F.property
  have h2 := (isSheaf_iff_isSheaf_of_type _ _).1 h1
  exact (h2 S hS).isSeparatedFor.ext fun V g hg => hP V g hg

def twpair_tens_univ_exdeg : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (τ : Pair I J K), τ.IsTensor → ∀ {I' J' K' : Cx R} (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J') (w : ℤ), ∃ φ : K.X w ⟶ K'.X w, ∀ (U : Scheme.{0}) (s t : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
    Sec.map φ (τ.mul U s t w h a b) = ν.mul U s t w h (Sec.map (f.f s) a) (Sec.map (g.f t) b)

theorem tens_univ_ex_of (hdeg : twpair_tens_univ_exdeg) : twpair_tens_univ_ex := by
  intro R _ I J K τ hτ I' J' K' ν f g
  choose φ hφ using hdeg R τ hτ ν f g
  have hsep := etale_sheaf_sections_separated_holds
  refine ⟨⟨φ, ?_⟩, fun U s t w h a b => hφ w U s t h a b⟩
  rintro i j (hij : i + 1 = j)
  subst hij
  ext U y
  apply hsep R (K'.X (i + 1)) U.unop
  refine TensLocbij.loc_mono (hτ.1 U.unop i y) ?_
  rintro V r ⟨x, hx⟩
  show Sec.res r (Sec.map (φ i ≫ K'.d i (i + 1)) y) = Sec.res r (Sec.map (K.d i (i + 1) ≫ φ (i + 1)) y)
  rw [secmap_res, secmap_res, ← hx]
  classical
  have key : ((K.d i (i + 1) ≫ φ (i + 1)).hom.app (op V)).hom ∘ₗ τ.lift V i =
      ((φ i ≫ K'.d i (i + 1)).hom.app (op V)).hom ∘ₗ τ.lift V i := by
    apply DirectSum.linearMap_ext
    intro p
    apply TensorProduct.ext'
    intro a b
    simp only [LinearMap.comp_apply, Pair.lift, DirectSum.toModule_lof, TensorProduct.lift.tmul]
    have e1 : Sec.map (K.d i (i + 1) ≫ φ (i + 1)) (τ.mul V p.1.1 p.1.2 i p.2 a b) =
        Sec.map (φ (i + 1)) (Sec.map (K.d i (i + 1)) (τ.mul V p.1.1 p.1.2 i p.2 a b)) := rfl
    have e2 : Sec.map (φ i ≫ K'.d i (i + 1)) (τ.mul V p.1.1 p.1.2 i p.2 a b) =
        Sec.map (K'.d i (i + 1)) (Sec.map (φ i) (τ.mul V p.1.1 p.1.2 i p.2 a b)) := rfl
    change Sec.map (K.d i (i + 1) ≫ φ (i + 1)) (τ.mul V p.1.1 p.1.2 i p.2 a b) = Sec.map (φ i ≫ K'.d i (i + 1)) (τ.mul V p.1.1 p.1.2 i p.2 a b)
    have h1 := hφ (i + 1) V (p.1.1 + 1) p.1.2 (by have := p.2; omega) (Sec.map (I.d p.1.1 (p.1.1 + 1)) a) b
    have h2 := hφ (i + 1) V p.1.1 (p.1.2 + 1) (by have := p.2; omega) a (Sec.map (J.d p.1.2 (p.1.2 + 1)) b)
    have hf : Sec.map (I'.d p.1.1 (p.1.1 + 1)) (Sec.map (f.f p.1.1) a) = Sec.map (f.f (p.1.1 + 1)) (Sec.map (I.d p.1.1 (p.1.1 + 1)) a) := by
      rw [secmap_comp, secmap_comp, f.comm]
    have hg : Sec.map (J'.d p.1.2 (p.1.2 + 1)) (Sec.map (g.f p.1.2) b) = Sec.map (g.f (p.1.2 + 1)) (Sec.map (J.d p.1.2 (p.1.2 + 1)) b) := by
      rw [secmap_comp, secmap_comp, g.comm]
    rw [e1, e2, τ.leibniz, hφ i, ν.leibniz, hf, hg]
    simp only [Sec.map, map_add (f := _), map_zsmul_unit] at h1 h2 ⊢
    rw [h1, h2]
  exact (congrArg (fun k => k x) key).symm

theorem twpair_tens_univ_of (hdeg : twpair_tens_univ_exdeg) :
    LateralTheory.EtaleFoundations.twpair_tens_univ := by
  have hsep := etale_sheaf_sections_separated_holds
  have hex := tens_univ_ex_of hdeg
  intro R _ I J K τ hτ
  refine ⟨?_, tens_univ_ge_of hsep R τ hτ, fun u => ⟨pairPost τ u, pairPost_compat τ u⟩⟩
  intro I' J' K' ν f g
  obtain ⟨u, hu⟩ := hex R τ hτ ν f g
  exact ⟨u, hu, fun u' hu' => tens_univ_uniq_of hsep R τ hτ ν f g u' u hu' hu⟩

end LateralTheory.EtaleFoundations
end

section -- merged from Development.EtaleCohomology.TateTwists.TtTensExPfSh
section -- merged from Development.EtaleCohomology.TateTwists.TtTensExPfLoc
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

variable {R : Type} [CommRing R]

theorem tt_sheafify_locSurj (P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) (U : Scheme.{0})
    (y : ((presheafToSheaf Scheme.etaleTopology.{0} _).obj P).obj.obj (op U)) :
    Loc U fun V g => ∃ x, ((toSheafify Scheme.etaleTopology.{0} P).app (op V)).hom x =
      (((presheafToSheaf Scheme.etaleTopology.{0} _).obj P).obj.map g.op).hom y :=
  ⟨_, Presheaf.imageSieve_mem Scheme.etaleTopology.{0} (toSheafify Scheme.etaleTopology.{0} P) y,
    fun _ _ ⟨x, hx⟩ => ⟨x, hx⟩⟩

theorem tt_sheafify_locInj (P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) (U : Scheme.{0})
    (x : P.obj (op U)) (hx : ((toSheafify Scheme.etaleTopology.{0} P).app (op U)).hom x = 0) :
    Loc U fun _ g => (P.map g.op).hom x = 0 := by
  refine ⟨_, Presheaf.equalizerSieve_mem Scheme.etaleTopology.{0} (toSheafify Scheme.etaleTopology.{0} P) x 0
    (by simpa using hx), fun _ _ h => ?_⟩
  simpa using h

end LateralTheory.EtaleFoundations
end

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped DirectSum TensorProduct

namespace LateralTheory.EtaleFoundations

variable {R : Type} [CommRing R]

noncomputable section

abbrev shK {I J : Cx R} (T : TensPre I J) : Cx R :=
  ((presheafToSheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj T.P

abbrev tS {I J : Cx R} (T : TensPre I J) (U : Scheme.{0}) (w : ℤ) :
    Tens I J U w →ₗ[ULift.{1} R] Sec ((shK T).X w) U :=
  ((toSheafify Scheme.etaleTopology.{0} (T.P.X w)).app (op U)).hom ∘ₗ (T.e U w).toLinearMap

theorem tS_nat {I J : Cx R} (T : TensPre I J) {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (x : Tens I J U w) :
    Sec.res g (tS T U w x) = tS T V w (Tens.res g w x) := by
  have h1 := ConcreteCategory.congr_hom ((toSheafify Scheme.etaleTopology.{0} (T.P.X w)).naturality g.op) (T.e U w x)
  simp only [ConcreteCategory.comp_apply] at h1
  show Sec.res g (((toSheafify Scheme.etaleTopology.{0} (T.P.X w)).app (op U)).hom (T.e U w x)) =
    ((toSheafify Scheme.etaleTopology.{0} (T.P.X w)).app (op V)).hom (T.e V w (Tens.res g w x))
  rw [T.nat]
  exact h1.symm

theorem tS_d {I J : Cx R} (T : TensPre I J) (U : Scheme.{0}) (w : ℤ) (x : Tens I J U w) :
    Sec.map ((shK T).d w (w + 1)) (tS T U w x) =
      ((toSheafify Scheme.etaleTopology.{0} (T.P.X (w + 1))).app (op U)).hom
        (((T.P.d w (w + 1)).app (op U)).hom (T.e U w x)) := by
  simp only [tS, LinearMap.comp_apply, LinearEquiv.coe_coe]
  exact (ConcreteCategory.congr_hom (congrArg (fun f => NatTrans.app f (op U))
    (toSheafify_naturality Scheme.etaleTopology.{0} (T.P.d w (w + 1)))) _).symm

def shPair {I J : Cx R} (T : TensPre I J) : Pair I J (shK T) where
  mul U s t w h := (TensorProduct.mk _ _ _).compr₂ (tS T U w ∘ₗ DirectSum.lof (ULift.{1} R) {p : ℤ × ℤ // p.1 + p.2 = w} (fun p => Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) ⟨(s, t), h⟩)
  nat {V} {U} g s t w h a b := by
    change Sec.res g (tS T U w (DirectSum.of _ ⟨(s, t), h⟩ (a ⊗ₜ b))) =
      tS T V w (DirectSum.of _ ⟨(s, t), h⟩ (Sec.res g a ⊗ₜ Sec.res g b))
    rw [tS_nat, Tens.res, DirectSum.lmap_of, TensorProduct.map_tmul]
  leibniz U s t w h a b := by
    change Sec.map ((shK T).d w (w + 1))
      (tS T U w (DirectSum.of _ ⟨(s, t), h⟩ (a ⊗ₜ b))) = _
    rw [tS_d, T.leibniz]
    simp only [map_add, Units.smul_def, map_zsmul]
    rfl

theorem shPair_lift {I J : Cx R} (T : TensPre I J) (U : Scheme.{0}) (w : ℤ) :
    (shPair T).lift U w = tS T U w := by
  classical
  apply DirectSum.linearMap_ext; intro p; apply TensorProduct.ext'; intro a b
  simp [Pair.lift, shPair, DirectSum.toModule_lof]

theorem shPair_isTensor {I J : Cx R} (T : TensPre I J) : (shPair T).IsTensor := by
  refine ⟨fun U w y => ?_, fun U w x hx => ?_⟩
  · obtain ⟨S, hS, hP⟩ := tt_sheafify_locSurj (T.P.X w) U y
    refine ⟨S, hS, fun V g hg => ?_⟩
    obtain ⟨x, hx⟩ := hP V g hg
    refine ⟨(T.e V w).symm x, ?_⟩
    rw [shPair_lift]
    show ((toSheafify Scheme.etaleTopology.{0} (T.P.X w)).app (op V)).hom (T.e V w ((T.e V w).symm x)) = _
    rw [LinearEquiv.apply_symm_apply]
    exact hx
  · rw [shPair_lift] at hx
    obtain ⟨S, hS, hP⟩ := tt_sheafify_locInj (T.P.X w) U (T.e U w x) hx
    refine ⟨S, hS, fun V g hg => ?_⟩
    have h2 := hP V g hg
    simp only at h2 ⊢
    rw [← T.nat] at h2
    exact (LinearEquiv.map_eq_zero_iff _).mp h2

theorem etale_presheaf_tensor_data_sheafification_is_tensor_complex : tt_tens_sheafify := fun _ _ _ _ T => ⟨_, shPair T, shPair_isTensor T⟩

end

end LateralTheory.EtaleFoundations
end

section -- merged from Development.EtaleCohomology.TateTwists.TtTensPrePf
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped DirectSum TensorProduct

namespace LateralTheory.EtaleFoundations
namespace TTP

variable {R : Type} [CommRing R]

noncomputable section

abbrev dI (I : Cx R) (U : Scheme.{0}) (s : ℤ) : Sec (I.X s) U →ₗ[ULift.{1} R] Sec (I.X (s + 1)) U :=
  ((I.d s (s + 1)).hom.app (op U)).hom

theorem dI_dI (I : Cx R) (U : Scheme.{0}) (s : ℤ) (a : Sec (I.X s) U) : dI I U (s + 1) (dI I U s a) = 0 := by
  have h := congrArg (fun f => ((f.hom.app (op U)).hom a)) (I.d_comp_d s (s + 1) (s + 1 + 1))
  exact h.trans (by simp)

theorem dI_res (I : Cx R) {V U : Scheme.{0}} (g : V ⟶ U) (s : ℤ) (a : Sec (I.X s) U) :
    dI I V s (((I.X s).obj.map g.op).hom a) = ((I.X (s + 1)).obj.map g.op).hom (dI I U s a) := by
  have h := congrArg (fun f => ModuleCat.Hom.hom f a) ((I.d s (s + 1)).hom.naturality g.op)
  exact h

def dT (I J : Cx R) (U : Scheme.{0}) (w : ℤ) : Tens I J U w →ₗ[ULift.{1} R] Tens I J U (w + 1) :=
  DirectSum.toModule _ _ _ fun p =>
    (DirectSum.lof (ULift.{1} R) {q : ℤ × ℤ // q.1 + q.2 = w + 1}
        (fun q => Sec (I.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U)
        ⟨(p.1.1 + 1, p.1.2), by have := p.2; simp only at this ⊢; omega⟩ ∘ₗ
      TensorProduct.map (dI I U p.1.1) LinearMap.id) +
    ((p.1.1.negOnePow : ℤ) • (DirectSum.lof (ULift.{1} R) {q : ℤ × ℤ // q.1 + q.2 = w + 1}
        (fun q => Sec (I.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U)
        ⟨(p.1.1, p.1.2 + 1), by have := p.2; simp only at this ⊢; omega⟩ ∘ₗ
      TensorProduct.map LinearMap.id (dI J U p.1.2)))

theorem dT_of (I J : Cx R) (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U) :
    dT I J U w (DirectSum.of (fun q : {q : ℤ × ℤ // q.1 + q.2 = w} => Sec (I.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U)
      ⟨(s, t), h⟩ (a ⊗ₜ b)) =
    DirectSum.of (fun q : {q : ℤ × ℤ // q.1 + q.2 = w + 1} => Sec (I.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U)
      ⟨(s + 1, t), by omega⟩ (dI I U s a ⊗ₜ b) +
    (s.negOnePow : ℤ) • DirectSum.of (fun q : {q : ℤ × ℤ // q.1 + q.2 = w + 1} => Sec (I.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U)
      ⟨(s, t + 1), by omega⟩ (a ⊗ₜ dI J U t b) := by
  rw [← DirectSum.lof_eq_of (ULift.{1} R), dT, DirectSum.toModule_lof]
  simp [DirectSum.lof_eq_of]

theorem dT_dT (I J : Cx R) (U : Scheme.{0}) (w : ℤ) : (dT I J U (w + 1)).comp (dT I J U w) = 0 := by
  apply DirectSum.linearMap_ext; rintro ⟨⟨s, t⟩, h⟩; apply TensorProduct.ext'; intro a b
  simp only [LinearMap.comp_apply, DirectSum.lof_eq_of, LinearMap.zero_apply]
  rw [dT_of, map_add (f := _), map_zsmul, dT_of, dT_of]
  simp [dI_dI, Int.negOnePow_succ]

theorem res_of (I J : Cx R) {V U : Scheme.{0}} (g : V ⟶ U) (s t w : ℤ) (h : s + t = w)
    (a : Sec (I.X s) U) (b : Sec (J.X t) U) :
    Tens.res (I := I) (J := J) g w (DirectSum.of (fun q : {q : ℤ × ℤ // q.1 + q.2 = w} => Sec (I.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U)
      ⟨(s, t), h⟩ (a ⊗ₜ b)) =
    DirectSum.of (fun q : {q : ℤ × ℤ // q.1 + q.2 = w} => Sec (I.X q.1.1) V ⊗[ULift.{1} R] Sec (J.X q.1.2) V)
      ⟨(s, t), h⟩ (((I.X s).obj.map g.op).hom a ⊗ₜ ((J.X t).obj.map g.op).hom b) := by
  rw [← DirectSum.lof_eq_of (ULift.{1} R), Tens.res, DirectSum.lmap_lof, TensorProduct.map_tmul, DirectSum.lof_eq_of]

theorem res_id (I J : Cx R) (U : Scheme.{0}) (w : ℤ) : Tens.res (I := I) (J := J) (𝟙 U) w = LinearMap.id := by
  apply DirectSum.linearMap_ext; rintro ⟨⟨s, t⟩, h⟩; apply TensorProduct.ext'; intro a b
  simp only [LinearMap.comp_apply, DirectSum.lof_eq_of, LinearMap.id_apply]
  rw [res_of]
  simp

theorem res_comp (I J : Cx R) {W V U : Scheme.{0}} (f : W ⟶ V) (g : V ⟶ U) (w : ℤ) :
    Tens.res (I := I) (J := J) (f ≫ g) w = Tens.res f w ∘ₗ Tens.res g w := by
  apply DirectSum.linearMap_ext; rintro ⟨⟨s, t⟩, h⟩; apply TensorProduct.ext'; intro a b
  simp only [LinearMap.comp_apply, DirectSum.lof_eq_of]
  rw [res_of, res_of, res_of]
  simp

theorem dT_res (I J : Cx R) {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) :
    dT I J V w ∘ₗ Tens.res g w = Tens.res g (w + 1) ∘ₗ dT I J U w := by
  apply DirectSum.linearMap_ext; rintro ⟨⟨s, t⟩, h⟩; apply TensorProduct.ext'; intro a b
  simp only [LinearMap.comp_apply, DirectSum.lof_eq_of]
  rw [res_of, dT_of, dT_of, map_add (f := _), map_zsmul, res_of, res_of, dI_res, dI_res]

def PF (I J : Cx R) (w : ℤ) : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R) where
  obj U := ModuleCat.of (ULift.{1} R) (Tens I J U.unop w)
  map g := ModuleCat.ofHom (Tens.res g.unop w)
  map_id U := by
    apply ModuleCat.hom_ext
    simp only [unop_id, ModuleCat.hom_ofHom, ModuleCat.hom_id]
    exact res_id I J U.unop w
  map_comp f g := by
    apply ModuleCat.hom_ext
    simp only [unop_comp, ModuleCat.hom_ofHom, ModuleCat.hom_comp]
    exact res_comp I J g.unop f.unop w

def dN (I J : Cx R) (w : ℤ) : PF I J w ⟶ PF I J (w + 1) where
  app U := ModuleCat.ofHom (dT I J U.unop w)
  naturality U V g := by
    apply ModuleCat.hom_ext
    simp only [PF, ModuleCat.hom_ofHom, ModuleCat.hom_comp]
    exact dT_res I J g.unop w

theorem dN_dN (I J : Cx R) (w : ℤ) : dN I J w ≫ dN I J (w + 1) = 0 := by
  ext U : 2
  apply ModuleCat.hom_ext
  simp only [NatTrans.comp_app, dN, NatTrans.app_zero, ModuleCat.hom_zero]
  exact dT_dT I J U.unop w

def PC (I J : Cx R) : CochainComplex (Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) ℤ :=
  CochainComplex.of (fun w => PF I J w) (fun w => dN I J w) (fun w => dN_dN I J w)

def tensPre (I J : Cx R) : TensPre I J where
  P := PC I J
  e U w := LinearEquiv.refl (ULift.{1} R) (Tens I J U w)
  nat g w x := rfl
  leibniz U s t w h a b := by
    simp only [PC]
    rw [CochainComplex.of_d]
    exact (dT_of I J U s t w h a b).trans (congrArg (HAdd.hAdd _) (Units.smul_def _ _).symm)

end

end TTP

theorem tt_tens_pre_of : tt_tens_pre := fun _ _ I J => ⟨TTP.tensPre I J⟩

end LateralTheory.EtaleFoundations
end
