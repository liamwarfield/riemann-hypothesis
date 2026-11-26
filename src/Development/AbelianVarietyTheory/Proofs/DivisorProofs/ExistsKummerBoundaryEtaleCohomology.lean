module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerSequenceEtaleTateTwist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyCoefficientRingInvariance
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerConnectingUnitClassEqKummerClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerBoundaryLineBundleFirstChernClass

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConnectingCocycleHypercohomologyLes
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MappingConeShortExactAugmentationClassEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MappingConeShortExactAugmentationClassEq
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.ConeClass

variable {R : Type} [CommRing R]

theorem mk_ofHom_comp {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) :
    CohomologyClass.mk (Cocycle.ofHom (f ≫ g)) = cpull f M 0 (CohomologyClass.mk (Cocycle.ofHom g)) := by
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_comp]

theorem mk_injective_sgl (X : Shv R) (I : Cx R) [I.IsStrictlyGE 0] :
    Function.Injective (CohomologyClass.mk : Cocycle (sgl X) I 0 → CohomologyClass (sgl X) I 0) := by
  intro a b h
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff (m := -1) (hm := by norm_num)] at h
  obtain ⟨β, hβ⟩ := h
  have hβ0 : β = 0 := by
    refine Cochain.ext _ _ fun p q hpq => ?_
    by_cases hp : p = 0
    · subst hp
      exact (CochainComplex.isZero_of_isStrictlyGE I 0 q (by omega)).eq_of_tgt _ _
    · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hp).eq_of_src _ _
  rw [hβ0, δ_zero] at hβ
  exact sub_eq_zero.1 (Cocycle.ext hβ.symm)

theorem cpull_single_injective {X Y : Shv R} (g : X ⟶ Y) [Epi g] (I : Cx R) [I.IsStrictlyGE 0] :
    Function.Injective (cpull ((CochainComplex.singleFunctor (Shv R) 0).map g) I 0) := by
  intro x y h
  obtain ⟨x, rfl⟩ := x.mk_surjective
  obtain ⟨y, rfl⟩ := y.mk_surjective
  have h' := mk_injective_sgl X I h
  have hg : Epi (((CochainComplex.singleFunctor (Shv R) 0).map g).f 0) := by
    change Epi (((HomologicalComplex.single _ _ 0).map g).f 0)
    rw [HomologicalComplex.single_map_f_self]
    infer_instance
  congr 1
  refine Cocycle.ext (Cochain.ext _ _ fun p q hpq => ?_)
  by_cases hp : p = 0
  · subst hp
    obtain rfl : q = 0 := by omega
    have e := congrArg (fun z : Cocycle (sgl X) I 0 => z.1.v 0 0 (add_zero 0)) h'
    simp only [zcomp, Cocycle.mk_coe, Cocycle.ofHom_coe, Cochain.comp_v _ _ (zero_add 0) 0 0 0 (add_zero 0) (add_zero 0),
      Cochain.ofHom_v] at e
    exact (cancel_epi _).1 e
  · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hp).eq_of_src _ _

theorem mk_ofHom_eq_of_homotopy {K L : Cx R} (f g : K ⟶ L) (h : Homotopy f g) :
    CohomologyClass.mk (Cocycle.ofHom f) = CohomologyClass.mk (Cocycle.ofHom g) := by
  have e := congrArg (fun φ => φ (CohomologyClass.mk (Cocycle.ofHom (𝟙 L)))) ((GlobalTheory.T.hypercohomologyPullbackPushforward_functorial R).2.2.2.2 f g ⟨h⟩ L 0).1
  simpa only [← mk_ofHom_comp, Category.comp_id] using e

end GlobalTheory.EtC.ConeClass

namespace GlobalTheory.EtC.ConeClass

theorem cone_class_eq : ∀ (R : Type) [CommRing R] (S : ShortComplex (Shv R)), S.ShortExact →
    ∀ (hc : (CochainComplex.singleFunctor (Shv R) 0).map S.f ≫ resAug S.X₂ = resAug S.X₁ ≫ resMap R S.f)
    (e : HomotopyEquiv (mappingCone (resMap R S.f)) (res R S.X₃)),
    Homotopy (mappingCone.inr (resMap R S.f) ≫ e.hom) (resMap R S.g) →
    CohomologyClass.mk (Cocycle.ofHom
        (mappingCone.descShortComplex (S.map (CochainComplex.singleFunctor (Shv R) 0)) ≫ resAug S.X₃)) =
      CohomologyClass.mk (Cocycle.ofHom
        (mappingCone.map _ (resMap R S.f) (resAug S.X₁) (resAug S.X₂) hc ≫ e.hom)) := by
  intro R _ S hS hc e hh
  have hS' : (S.map (CochainComplex.singleFunctor (Shv R) 0)).ShortExact :=
    hS.map_of_exact (HomologicalComplex.single _ _ _)
  haveI : QuasiIso (mappingCone.descShortComplex (S.map (CochainComplex.singleFunctor (Shv R) 0))) :=
    mappingCone.quasiIso_descShortComplex hS'
  haveI : (res R S.X₃).IsKInjective := inferInstanceAs ((injectiveResolution S.X₃).cochainComplex.IsKInjective)
  haveI : (res R S.X₃).IsStrictlyGE 0 := inferInstanceAs ((injectiveResolution S.X₃).cochainComplex.IsStrictlyGE 0)
  haveI : Epi S.g := hS.epi_g
  have hbij := GlobalTheory.T.hypercohomologyPullback_bijective_of_quasiIso R (mappingCone.descShortComplex (S.map (CochainComplex.singleFunctor (Shv R) 0))) (res R S.X₃) 0
  obtain ⟨c, hc'⟩ := hbij.2 (CohomologyClass.mk (Cocycle.ofHom
    (mappingCone.map _ (resMap R S.f) (resAug S.X₁) (resAug S.X₂) hc ≫ e.hom)))
  refine (mk_ofHom_comp _ _).trans (Eq.trans ?_ hc')
  refine congrArg _ ?_
  have hinr : mappingCone.inr (S.map (CochainComplex.singleFunctor (Shv R) 0)).f ≫
      mappingCone.map _ (resMap R S.f) (resAug S.X₁) (resAug S.X₂) hc = resAug S.X₂ ≫ mappingCone.inr (resMap R S.f) := by
    simp [mappingCone.map]
  have hres : resAug S.X₂ ≫ resMap R S.g = (CochainComplex.singleFunctor (Shv R) 0).map S.g ≫ resAug S.X₃ :=
    InjectiveResolution.Hom.ι'_comp_hom'
      ⟨InjectiveResolution.desc S.g (injectiveResolution _) (injectiveResolution _),
        InjectiveResolution.desc_commutes_zero _ _ _⟩
  apply cpull_single_injective S.g (res R S.X₃)
  have hA : cpull ((CochainComplex.singleFunctor (Shv R) 0).map S.g) (res R S.X₃) 0
      (CohomologyClass.mk (Cocycle.ofHom (resAug S.X₃))) =
      CohomologyClass.mk (Cocycle.ofHom (resAug S.X₂ ≫ mappingCone.inr (resMap R S.f) ≫ e.hom)) := by
    calc cpull ((CochainComplex.singleFunctor (Shv R) 0).map S.g) (res R S.X₃) 0
            (CohomologyClass.mk (Cocycle.ofHom (resAug S.X₃)))
        = CohomologyClass.mk (Cocycle.ofHom ((CochainComplex.singleFunctor (Shv R) 0).map S.g ≫ resAug S.X₃)) :=
          (mk_ofHom_comp _ _).symm
      _ = CohomologyClass.mk (Cocycle.ofHom (resAug S.X₂ ≫ resMap R S.g)) := by rw [hres]
      _ = CohomologyClass.mk (Cocycle.ofHom (resAug S.X₂ ≫ mappingCone.inr (resMap R S.f) ≫ e.hom)) :=
          (mk_ofHom_eq_of_homotopy _ _ (hh.compLeft (resAug S.X₂))).symm
  have hB1 : CohomologyClass.mk (Cocycle.ofHom (mappingCone.inr (S.map (CochainComplex.singleFunctor (Shv R) 0)).f ≫
        mappingCone.map _ (resMap R S.f) (resAug S.X₁) (resAug S.X₂) hc ≫ e.hom)) =
      cpull (mappingCone.inr (S.map (CochainComplex.singleFunctor (Shv R) 0)).f) (res R S.X₃) 0
          (cpull (mappingCone.descShortComplex (S.map (CochainComplex.singleFunctor (Shv R) 0))) (res R S.X₃) 0 c) := by
    rw [hc', mk_ofHom_comp]
  have hB2 : cpull (mappingCone.inr (S.map (CochainComplex.singleFunctor (Shv R) 0)).f) (res R S.X₃) 0
          (cpull (mappingCone.descShortComplex (S.map (CochainComplex.singleFunctor (Shv R) 0))) (res R S.X₃) 0 c) =
      cpull ((CochainComplex.singleFunctor (Shv R) 0).map S.g) (res R S.X₃) 0 c := by
    rw [← (GlobalTheory.T.hypercohomologyPullbackPushforward_functorial R).2.1, mappingCone.inr_descShortComplex]
    rfl
  have hC : (CohomologyClass.mk (Cocycle.ofHom (resAug S.X₂ ≫ mappingCone.inr (resMap R S.f) ≫ e.hom)) :
        CohomologyClass (sgl S.X₂) (res R S.X₃) 0) =
      CohomologyClass.mk (Cocycle.ofHom (mappingCone.inr (S.map (CochainComplex.singleFunctor (Shv R) 0)).f ≫
        mappingCone.map _ (resMap R S.f) (resAug S.X₁) (resAug S.X₂) hc ≫ e.hom)) := by
    rw [reassoc_of% hinr]
  exact hA.trans (hC.trans (hB1.trans hB2))

end GlobalTheory.EtC.ConeClass
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MappingConeShortExactAugmentationClassEqStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mappingCone_shortExact_augmentation_class_eq : ∀ (R : Type) [CommRing R] (S : ShortComplex (Shv R)), S.ShortExact →
    ∀ (hc : (CochainComplex.singleFunctor (Shv R) 0).map S.f ≫ resAug S.X₂ = resAug S.X₁ ≫ resMap R S.f)
    (e : HomotopyEquiv (mappingCone (resMap R S.f)) (res R S.X₃)),
    Homotopy (mappingCone.inr (resMap R S.f) ≫ e.hom) (resMap R S.g) →
    CohomologyClass.mk (Cocycle.ofHom
        (mappingCone.descShortComplex (S.map (CochainComplex.singleFunctor (Shv R) 0)) ≫ resAug S.X₃)) =
      CohomologyClass.mk (Cocycle.ofHom
        (mappingCone.map _ (resMap R S.f) (resAug S.X₁) (resAug S.X₂) hc ≫ e.hom)) := by
  first | (exact @GlobalTheory.EtC.ConeClass.cone_class_eq) | (exact GlobalTheory.EtC.ConeClass.cone_class_eq) | (intros; apply GlobalTheory.EtC.ConeClass.cone_class_eq  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MappingConeConnectingCocycleShortComplexDegreeZe
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MappingConeConnectingCocycleShortComplexDegreeZe
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.ConeConn


set_option backward.isDefEq.respectTransparency false in
theorem cone_connecting_class : ∀ (R : Type) [CommRing R] (S : ShortComplex (Shv R))
    (hc : (CochainComplex.singleFunctor (Shv R) 0).map S.f ≫ resAug S.X₂ = resAug S.X₁ ≫ resMap R S.f)
    (φ : S.X₂ ⟶ (res R S.X₁).X 0) (ψ : S.X₃ ⟶ (res R S.X₁).X 1),
    S.f ≫ φ = resι R S.X₁ → S.g ≫ ψ = φ ≫ (res R S.X₁).d 0 1 →
    ∀ w : Cocycle (sgl S.X₃) (res R S.X₁) 1, sglι S.X₃ ≫ w.1.v 0 1 (zero_add 1) = ψ →
    CohomologyClass.mk (zcomp (Cocycle.ofHom (mappingCone.map _ (resMap R S.f) (resAug S.X₁) (resAug S.X₂) hc))
        (mappingCone.fst (resMap R S.f)) (zero_add 1)) =
      CohomologyClass.mk (zcomp (Cocycle.ofHom
        (mappingCone.descShortComplex (S.map (CochainComplex.singleFunctor (Shv R) 0)))) w (zero_add 1)) := by
  intro R _ S hc φ ψ hφ hψ w hw
  let Φ : Cochain (sgl S.X₂) (res R S.X₁) 0 := Cochain.fromSingleMk φ (zero_add 0)
  have hw1 : w.1 = Cochain.fromSingleMk ψ (zero_add 1) := by
    obtain ⟨f, hf⟩ := Cochain.fromSingleMk_surjective w.1 1 (zero_add 1)
    rw [← hf]; congr 1
    rw [← hw, ← hf, Cochain.fromSingleMk_v]; exact (Iso.inv_hom_id_assoc _ _).symm
  have h1 : δ 0 1 Φ = (Cochain.ofHom (S.map (CochainComplex.singleFunctor (Shv R) 0)).g).comp w.1 (zero_add 1) := by
    rw [hw1, Cochain.δ_fromSingleMk φ (zero_add 0) 1 1 (zero_add 1), ← hψ]
    exact Cochain.fromSingleMk_precomp S.g ψ (zero_add 1)
  have h2 : (Cochain.ofHom (S.map (CochainComplex.singleFunctor (Shv R) 0)).f).comp Φ (zero_add 0) =
      Cochain.ofHom (resAug S.X₁) := by
    refine (Cochain.fromSingleMk_precomp S.f φ (zero_add 0)).symm.trans ?_
    rw [hφ]
    apply (Cochain.fromSingleEquiv (X := S.X₁) (K := res R S.X₁) (p := 0) (zero_add 0)).injective
    rw [Cochain.fromSingleEquiv_fromSingleMk]
    change resι R S.X₁ = (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 S.X₁).inv ≫ (Cochain.ofHom (resAug S.X₁)).v 0 0 (add_zero 0)
    rw [Cochain.ofHom_v]; rfl
  have h3 : Cochain.ofHom (mappingCone.descShortComplex (S.map (CochainComplex.singleFunctor (Shv R) 0))) =
      (mappingCone.snd (S.map (CochainComplex.singleFunctor (Shv R) 0)).f).comp
        (Cochain.ofHom (S.map (CochainComplex.singleFunctor (Shv R) 0)).g) (zero_add 0) := by
    rw [mappingCone.descShortComplex, mappingCone.ofHom_desc, mappingCone.descCochain]
    simp
  have h4 : (Cochain.ofHom (mappingCone.map _ (resMap R S.f) (resAug S.X₁) (resAug S.X₂) hc)).comp
      (mappingCone.fst (resMap R S.f)).1 (zero_add 1) =
      (mappingCone.fst (S.map (CochainComplex.singleFunctor (Shv R) 0)).f).1.comp
        (Cochain.ofHom (resAug S.X₁)) (add_zero 1) := by
    simp [mappingCone.map, mappingCone.ofHom_desc, mappingCone.descCochain, Cochain.add_comp]
  symm
  refine sub_eq_zero.1 ((CohomologyClass.mk_sub _ _).symm.trans ?_)
  refine (CohomologyClass.mk_eq_zero_iff _).2 ((mem_coboundaries_iff _ 0 (zero_add 1)).2
    ⟨(mappingCone.snd (S.map (CochainComplex.singleFunctor (Shv R) 0)).f).comp Φ (zero_add 0), ?_⟩)
  have e1 := δ_zero_cochain_comp (mappingCone.snd (S.map (CochainComplex.singleFunctor (Shv R) 0)).f) Φ 1 (zero_add 1)
  rw [h1, mappingCone.δ_snd, Int.negOnePow_zero, one_smul, Cochain.neg_comp,
    Cochain.comp_assoc_of_second_is_zero_cochain, h2,
    ← Cochain.comp_assoc_of_first_is_zero_cochain, ← h3, ← h4] at e1
  refine e1.trans ?_
  simp [zcomp, sub_eq_add_neg]

end GlobalTheory.EtC.ConeConn
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MappingConeConnectingCocycleShortComplexDegreeZeStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mappingCone_connecting_cocycle_shortComplex_degree_zero : ∀ (R : Type) [CommRing R] (S : ShortComplex (Shv R))
    (hc : (CochainComplex.singleFunctor (Shv R) 0).map S.f ≫ resAug S.X₂ = resAug S.X₁ ≫ resMap R S.f)
    (φ : S.X₂ ⟶ (res R S.X₁).X 0) (ψ : S.X₃ ⟶ (res R S.X₁).X 1),
    S.f ≫ φ = resι R S.X₁ → S.g ≫ ψ = φ ≫ (res R S.X₁).d 0 1 →
    ∀ w : Cocycle (sgl S.X₃) (res R S.X₁) 1, sglι S.X₃ ≫ w.1.v 0 1 (zero_add 1) = ψ →
    CohomologyClass.mk (zcomp (Cocycle.ofHom (mappingCone.map _ (resMap R S.f) (resAug S.X₁) (resAug S.X₂) hc))
        (mappingCone.fst (resMap R S.f)) (zero_add 1)) =
      CohomologyClass.mk (zcomp (Cocycle.ofHom
        (mappingCone.descShortComplex (S.map (CochainComplex.singleFunctor (Shv R) 0)))) w (zero_add 1)) := by
  first | (exact @GlobalTheory.EtC.ConeConn.cone_connecting_class) | (exact GlobalTheory.EtC.ConeConn.cone_connecting_class) | (intros; apply GlobalTheory.EtC.ConeConn.cone_connecting_class  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConnectingCocycleHypercohomologyLes
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.LesChar

variable {R' : Type} [CommRing R']

theorem resAug_comm (R : Type) [CommRing R] {F G : Shv R} (φ : F ⟶ G) :
    (CochainComplex.singleFunctor (Shv R) 0).map φ ≫ resAug G = resAug F ≫ resMap R φ :=
  (InjectiveResolution.Hom.ι'_comp_hom'
    (⟨InjectiveResolution.desc φ (injectiveResolution G) (injectiveResolution F),
      InjectiveResolution.desc_commutes_zero φ _ _⟩ : InjectiveResolution.Hom _ _ φ)).symm

theorem mk_ofHom_eq {K L : Cx R'} {f g : K ⟶ L} (ho : Homotopy f g) :
    CohomologyClass.mk (Cocycle.ofHom f) = CohomologyClass.mk (Cocycle.ofHom g) := by
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff]
  exact ⟨-1, by omega, Cochain.ofHomotopy ho, by ext; simp [δ_ofHomotopy]⟩

theorem exact_part : ∀ (R : Type) [CommRing R] (S : ShortComplex (Shv R))
    (e : HomotopyEquiv (mappingCone (resMap R S.f)) (res R S.X₃)),
    Homotopy (mappingCone.inr (resMap R S.f) ≫ e.hom) (resMap R S.g) → ∀ (K : Cx R) (n : ℤ),
    Function.Exact (HK.post R K S.f n) (HK.post R K S.g n) ∧
    Function.Exact (HK.post R K S.g n)
      (HK.ext R K (zcomp (Cocycle.ofHom e.inv) (mappingCone.fst (resMap R S.f)) (zero_add 1)) n (n + 1) rfl) ∧
    Function.Exact (HK.ext R K (zcomp (Cocycle.ofHom e.inv) (mappingCone.fst (resMap R S.f)) (zero_add 1)) n (n + 1) rfl)
      (HK.post R K S.f (n + 1)) := by
  intro R _ S e h K n
  obtain ⟨hid, -, hcomp, -, hhtp⟩ := GlobalTheory.T.hypercohomologyPullbackPushforward_functorial R
  obtain ⟨-, -, hass⟩ := GlobalTheory.T.cocycleCompHomComplex_assoc_on_cohomology_classes R (add_zero n) (zero_add 1) (rfl : n + 1 = n + 1) (rfl : n + 1 = n + 1)
  obtain ⟨x1, x2, x3⟩ := GlobalTheory.T.hypercohomology_mappingCone_second_variable_exact R K (resMap R S.f) n
  have hg : ∀ x, HK.post R K S.g n x = cpush K e.hom n (cpush K (mappingCone.inr (resMap R S.f)) n x) := by
    intro x
    rw [← hcomp]
    exact (congrFun (congrArg DFunLike.coe ((hhtp _ _ ⟨h⟩ K n).2)) x).symm
  have hz : ∀ x, HK.ext R K (zcomp (Cocycle.ofHom e.inv) (mappingCone.fst (resMap R S.f)) (zero_add 1)) n (n + 1) rfl x =
      cpost K (mappingCone.fst (resMap R S.f)) n (n + 1) rfl (cpush K e.inv n x) := fun x => hass _ _ _
  have hie : ∀ x, cpush K e.inv n (cpush K e.hom n x) = x := by
    intro x
    rw [← hcomp, (hhtp _ _ ⟨e.homotopyHomInvId⟩ K n).2]
    exact (hid K _ n x).2
  have hei : ∀ x, cpush K e.hom n (cpush K e.inv n x) = x := by
    intro x
    rw [← hcomp, (hhtp _ _ ⟨e.homotopyInvHomId⟩ K n).2]
    exact (hid K _ n x).2
  refine ⟨fun y => ?_, fun y => ?_, fun y => ?_⟩
  · rw [hg, ← map_zero (cpush K e.hom n)]
    constructor
    · intro hy
      exact (x1 _).1 (by rw [← hie (cpush K (mappingCone.inr (resMap R S.f)) n y), hy, hie])
    · intro hy
      rw [(x1 _).2 hy]
  · rw [hz]
    constructor
    · intro hy
      obtain ⟨x, hx⟩ := (x2 _).1 hy
      exact ⟨x, by rw [hg, hx, hei]⟩
    · rintro ⟨x, rfl⟩
      rw [hg, hie]
      exact (x2 _).2 ⟨x, rfl⟩
  · constructor
    · intro hy
      obtain ⟨x, hx⟩ := (x3 _).1 hy
      exact ⟨cpush K e.hom n x, by rw [hz, hie, hx]⟩
    · rintro ⟨x, rfl⟩
      rw [hz]
      exact (x3 _).2 ⟨_, rfl⟩

theorem zcomp_ofHom_ofHom {K L M N : Cx R'} {n : ℤ} (f : K ⟶ L) (g : L ⟶ M) (b : Cocycle M N n) :
    zcomp (Cocycle.ofHom f) (zcomp (Cocycle.ofHom g) b (zero_add n)) (zero_add n) =
      zcomp (Cocycle.ofHom (f ≫ g)) b (zero_add n) := by
  ext1
  change (Cochain.ofHom f).comp ((Cochain.ofHom g).comp b.1 (zero_add n)) (zero_add n) =
    (Cochain.ofHom (f ≫ g)).comp b.1 (zero_add n)
  rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]

theorem assemble {D C I₃ I₁ X : Cx R'} (q : D ⟶ X) (a : X ⟶ I₃) (m : D ⟶ C) (eh : C ⟶ I₃) (ei : I₃ ⟶ C)
    (fst : Cocycle C I₁ 1) (w : Cocycle X I₁ 1) (hh : Homotopy (eh ≫ ei) (𝟙 C))
    (cmp : CohomologyClass.mk (Cocycle.ofHom (q ≫ a)) = CohomologyClass.mk (Cocycle.ofHom (m ≫ eh)))
    (key : CohomologyClass.mk (zcomp (Cocycle.ofHom m) fst (zero_add 1)) =
      CohomologyClass.mk (zcomp (Cocycle.ofHom q) w (zero_add 1))) :
    cpull q I₁ 1 (CohomologyClass.mk (zcomp (Cocycle.ofHom a) (zcomp (Cocycle.ofHom ei) fst (zero_add 1)) (zero_add 1))) =
      cpull q I₁ 1 (CohomologyClass.mk w) := by
  have h1 : CohomologyClass.mk (Cocycle.ofHom ((m ≫ eh) ≫ ei)) = CohomologyClass.mk (Cocycle.ofHom m) :=
    mk_ofHom_eq (((Homotopy.ofEq (Category.assoc _ _ _)).trans (hh.compLeft m)).trans
      (Homotopy.ofEq (Category.comp_id m)))
  change CohomologyClass.mk (zcomp (Cocycle.ofHom q) _ (zero_add 1)) = CohomologyClass.mk (zcomp (Cocycle.ofHom q) w (zero_add 1))
  rw [zcomp_ofHom_ofHom, ← key, ← cpost_mk, cmp, cpost_mk, zcomp_ofHom_ofHom, ← cpost_mk, h1, cpost_mk]

theorem exists_connecting_cocycle : ∀ (R : Type) [CommRing R] (S : ShortComplex (Shv R)), S.ShortExact →
  ∃ z : Cocycle (res R S.X₃) (res R S.X₁) 1,
    (∀ (K : Cx R) (n : ℤ),
      Function.Exact (HK.post R K S.f n) (HK.post R K S.g n) ∧
      Function.Exact (HK.post R K S.g n) (HK.ext R K z n (n + 1) rfl) ∧
      Function.Exact (HK.ext R K z n (n + 1) rfl) (HK.post R K S.f (n + 1))) ∧
    ∃ s : ℤˣ, ∀ (φ : S.X₂ ⟶ (res R S.X₁).X 0) (ψ : S.X₃ ⟶ (res R S.X₁).X 1),
      S.f ≫ φ = resι R S.X₁ → S.g ≫ ψ = φ ≫ (res R S.X₁).d 0 1 →
      ∀ w : Cocycle (sgl S.X₃) (res R S.X₁) 1, sglι S.X₃ ≫ w.1.v 0 1 (zero_add 1) = ψ →
        CohomologyClass.mk (zcomp (Cocycle.ofHom (resAug S.X₃)) z (zero_add 1)) = s • CohomologyClass.mk w := by
  intro R _ S hS
  obtain ⟨e, ⟨h⟩⟩ := GlobalTheory.T.shortExact_mappingCone_resolution_homotopyEquiv R S hS
  refine ⟨_, exact_part R S e h, 1, ?_⟩
  intro φ ψ hφ hψ w hw
  rw [one_smul]
  have hc := resAug_comm R S.f
  have hS' : (S.map (CochainComplex.singleFunctor (Shv R) 0)).ShortExact := hS.map_of_exact (HomologicalComplex.single _ _ _)
  haveI := mappingCone.quasiIso_descShortComplex hS'
  haveI : (res R S.X₁).IsKInjective := by unfold res; infer_instance
  apply (GlobalTheory.T.hypercohomologyPullback_bijective_of_quasiIso R (mappingCone.descShortComplex (S.map (CochainComplex.singleFunctor (Shv R) 0)))
    (res R S.X₁) 1).1
  exact assemble _ _ _ _ _ _ _ e.homotopyHomInvId (GlobalTheory.T.mappingCone_shortExact_augmentation_class_eq R S hS hc e h) (GlobalTheory.T.mappingCone_connecting_cocycle_shortComplex_degree_zero R S hc φ ψ hφ hψ w hw)

end GlobalTheory.EtC.LesChar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConnectingCocycleHypercohomologyLesStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_connecting_cocycle_hypercohomology_les : ∀ (R : Type) [CommRing R] (S : ShortComplex (Shv R)), S.ShortExact →
  ∃ z : Cocycle (res R S.X₃) (res R S.X₁) 1,
    (∀ (K : Cx R) (n : ℤ),
      Function.Exact (HK.post R K S.f n) (HK.post R K S.g n) ∧
      Function.Exact (HK.post R K S.g n) (HK.ext R K z n (n + 1) rfl) ∧
      Function.Exact (HK.ext R K z n (n + 1) rfl) (HK.post R K S.f (n + 1))) ∧
    ∃ s : ℤˣ, ∀ (φ : S.X₂ ⟶ (res R S.X₁).X 0) (ψ : S.X₃ ⟶ (res R S.X₁).X 1),
      S.f ≫ φ = resι R S.X₁ → S.g ≫ ψ = φ ≫ (res R S.X₁).d 0 1 →
      ∀ w : Cocycle (sgl S.X₃) (res R S.X₁) 1, sglι S.X₃ ≫ w.1.v 0 1 (zero_add 1) = ψ →
        CohomologyClass.mk (zcomp (Cocycle.ofHom (resAug S.X₃)) z (zero_add 1)) = s • CohomologyClass.mk w := by
  first | (exact @GlobalTheory.EtC.LesChar.exists_connecting_cocycle) | (exact GlobalTheory.EtC.LesChar.exists_connecting_cocycle) | (intros; apply GlobalTheory.EtC.LesChar.exists_connecting_cocycle  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerCokernelToMultiplicativeGroupBijective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerCokernelToMultiplicativeGroupBijective
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.KumCoker

instance instWLBKumCoker (R : Type) [CommRing R] :
    (Scheme.etaleTopology.{0}).WEqualsLocallyBijective (ModuleCat.{1} (ULift.{1} R)) := by
  have : EssentiallySmall.{1} Scheme.{0} := inferInstance
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

theorem isSheaf_forget {R : Type} [CommRing R] (F : Shv R) :
    Presieve.IsSheaf Scheme.etaleTopology (F.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) :=
  (isSheaf_iff_isSheaf_of_type _ _).1
    ((Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget (ModuleCat.{1} (ULift.{1} R)))).1 F.property)

theorem sec_res_zero {R : Type} [CommRing R] (F : Shv R) {V U : Scheme.{0}} (g : V ⟶ U) : Sec.res g (0 : Sec F U) = 0 :=
  map_zero _

theorem sec_eq_zero {R : Type} [CommRing R] (F : Shv R) {U : Scheme.{0}} (x : Sec F U)
    (h : Loc U fun _ g => Sec.res g x = 0) : x = 0 := by
  obtain ⟨S, hS, hP⟩ := h
  refine ((isSheaf_forget F) S hS).isSeparatedFor.ext (fun V g hg => ?_)
  change Sec.res g x = Sec.res g 0
  rw [hP V g hg, sec_res_zero]

theorem sec_map_comp {R : Type} [CommRing R] {F G H : Shv R} (f : F ⟶ G) (g : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (f ≫ g) x = Sec.map g (Sec.map f x) := rfl

theorem sec_map_zero {R : Type} [CommRing R] {F G : Shv R} {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (0 : F ⟶ G) x = 0 := rfl

theorem sec_nat {R : Type} [CommRing R] {F G : Shv R} (f : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map f x) = Sec.map f (Sec.res g x) := by
  have e := congrArg (fun φ => φ.hom x) (f.hom.naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e
  exact e.symm

theorem sec_res_comp {R : Type} [CommRing R] (F : Shv R) {W V U : Scheme.{0}} (h : W ⟶ V) (g : V ⟶ U) (x : Sec F U) :
    Sec.res h (Sec.res g x) = Sec.res (h ≫ g) x := by
  simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem unit_res {q : ℕ} {V U : Scheme.{0}} (hU : IsUnit (q : Γ(U, ⊤))) (g : V ⟶ U) : IsUnit (q : Γ(V, ⊤)) := by
  simpa using hU.map g.appTop.hom

end GlobalTheory.EtC.KumCoker

open GlobalTheory.EtC.KumCoker in
theorem GlobalTheory.EtC.kumCoker_bijective : ∀ (q : ℕ) [NeZero q] (κ : (restr (Int.castRingHom (ZMod q))).obj (tw q 1) ⟶ Gm) (h0 : κ ≫ ((q : ℤ) • 𝟙 Gm) = 0),
  (∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ b : Sec Gm U, Sec.map ((q : ℤ) • 𝟙 Gm) b = 0 → ∃ a, Sec.map κ a = b) →
  (∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ b : Sec Gm U, Loc U fun V g => ∃ c : Sec Gm V, Sec.map ((q : ℤ) • 𝟙 Gm) c = Sec.res g b) →
  ∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → Function.Bijective (Sec.map (cokernel.desc κ ((q : ℤ) • 𝟙 Gm) h0) (U := U)) := by
  intro q _ κ h0 H1 H2
  set qb := cokernel.desc κ ((q : ℤ) • 𝟙 Gm) h0 with hqb
  have key : ∀ {V : Scheme.{0}} (b : Sec Gm V), Sec.map qb (Sec.map (cokernel.π κ) b) = Sec.map ((q : ℤ) • 𝟙 Gm) b := by
    intro V b
    rw [← sec_map_comp, hqb, cokernel.π_desc]
  have hls : Sheaf.IsLocallySurjective (cokernel.π κ) := (Sheaf.isLocallySurjective_iff_epi' _ _).2 inferInstance
  have inj : ∀ U : Scheme.{0}, IsUnit (q : Γ(U, ⊤)) → Function.Injective (Sec.map qb (U := U)) := by
    intro U hU
    refine (injective_iff_map_eq_zero ((qb.hom.app (op U)).hom)).2 (fun c hc => ?_)
    have hc' : Sec.map qb c = 0 := hc
    apply sec_eq_zero
    refine ⟨_, Presheaf.imageSieve_mem Scheme.etaleTopology (cokernel.π κ).hom c, fun V g hg => ?_⟩
    obtain ⟨b, hb⟩ := hg
    have hb' : Sec.map (cokernel.π κ) b = Sec.res g c := hb
    have hz : Sec.map ((q : ℤ) • 𝟙 Gm) b = 0 := by
      rw [← key, hb', ← sec_nat, hc', sec_res_zero]
    obtain ⟨a, rfl⟩ := H1 V (unit_res hU g) b hz
    rw [← hb', ← sec_map_comp, cokernel.condition, sec_map_zero]
  intro U hU
  refine ⟨inj U hU, fun b => ?_⟩
  obtain ⟨S, hS, hP⟩ := H2 U hU b
  choose c hc using hP
  let x : Presieve.FamilyOfElements ((cokernel κ).obj ⋙ forget (ModuleCat.{1} (ULift.{1} ℤ))) S.arrows :=
    fun V g hg => Sec.map (cokernel.π κ) (c V g hg)
  have hx : x.Compatible := by
    intro Y₁ Y₂ Z f₁ f₂ g₁ g₂ hg₁ hg₂ w
    apply inj Z (unit_res hU (f₁ ≫ g₁))
    change Sec.map qb (Sec.res f₁ (Sec.map (cokernel.π κ) (c _ g₁ hg₁))) =
      Sec.map qb (Sec.res f₂ (Sec.map (cokernel.π κ) (c _ g₂ hg₂)))
    rw [← sec_nat, ← sec_nat, key, key, hc, hc, sec_res_comp, sec_res_comp, w]
  obtain ⟨t, ht, -⟩ := isSheaf_forget (cokernel κ) S hS x hx
  refine ⟨t, sub_eq_zero.1 (sec_eq_zero Gm _ ⟨S, hS, fun V g hg => ?_⟩)⟩
  have ht' : Sec.res g t = Sec.map (cokernel.π κ) (c V g hg) := ht g hg
  change (Gm.obj.map g.op).hom (Sec.map qb t - b) = 0
  rw [map_sub]
  change Sec.res g (Sec.map qb t) - Sec.res g b = 0
  rw [sec_nat, ht', key, hc, sub_self]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerCokernelToMultiplicativeGroupBijectiveStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open GlobalTheory.EtC.KumCoker in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummer_cokernel_to_multiplicativeGroup_bijective : ∀ (q : ℕ) [NeZero q] (κ : (restr (Int.castRingHom (ZMod q))).obj (tw q 1) ⟶ Gm) (h0 : κ ≫ ((q : ℤ) • 𝟙 Gm) = 0),
  (∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ b : Sec Gm U, Sec.map ((q : ℤ) • 𝟙 Gm) b = 0 → ∃ a, Sec.map κ a = b) →
  (∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ b : Sec Gm U, Loc U fun V g => ∃ c : Sec Gm V, Sec.map ((q : ℤ) • 𝟙 Gm) c = Sec.res g b) →
  ∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → Function.Bijective (Sec.map (cokernel.desc κ ((q : ℤ) • 𝟙 Gm) h0) (U := U)) := by
  intro q _ κ h0 H1 H2
  set qb := cokernel.desc κ ((q : ℤ) • 𝟙 Gm) h0 with hqb
  have key : ∀ {V : Scheme.{0}} (b : Sec Gm V), Sec.map qb (Sec.map (cokernel.π κ) b) = Sec.map ((q : ℤ) • 𝟙 Gm) b := by
    intro V b
    rw [← sec_map_comp, hqb, cokernel.π_desc]
  have hls : Sheaf.IsLocallySurjective (cokernel.π κ) :=
    (Sheaf.isLocallySurjective_iff_epi' _ _).2 inferInstance
  have inj : ∀ U : Scheme.{0}, IsUnit (q : Γ(U, ⊤)) → Function.Injective (Sec.map qb (U := U)) := by
    intro U hU
    refine (injective_iff_map_eq_zero ((qb.hom.app (op U)).hom)).2 (fun c hc => ?_)
    have hc' : Sec.map qb c = 0 := hc
    apply sec_eq_zero
    refine ⟨_, Presheaf.imageSieve_mem Scheme.etaleTopology (cokernel.π κ).hom c, fun V g hg => ?_⟩
    obtain ⟨b, hb⟩ := hg
    have hb' : Sec.map (cokernel.π κ) b = Sec.res g c := hb
    have hz : Sec.map ((q : ℤ) • 𝟙 Gm) b = 0 := by
      rw [← key, hb', ← sec_nat, hc', sec_res_zero]
    obtain ⟨a, rfl⟩ := H1 V (unit_res hU g) b hz
    rw [← hb', ← sec_map_comp, cokernel.condition, sec_map_zero]
  intro U hU
  refine ⟨inj U hU, fun b => ?_⟩
  obtain ⟨S, hS, hP⟩ := H2 U hU b
  choose c hc using hP
  let x : Presieve.FamilyOfElements ((cokernel κ).obj ⋙ forget (ModuleCat.{1} (ULift.{1} ℤ))) S.arrows :=
    fun V g hg => Sec.map (cokernel.π κ) (c V g hg)
  have hx : x.Compatible := by
    intro Y₁ Y₂ Z f₁ f₂ g₁ g₂ hg₁ hg₂ w
    apply inj Z (unit_res hU (f₁ ≫ g₁))
    change Sec.map qb (Sec.res f₁ (Sec.map (cokernel.π κ) (c _ g₁ hg₁))) =
      Sec.map qb (Sec.res f₂ (Sec.map (cokernel.π κ) (c _ g₂ hg₂)))
    rw [← sec_nat, ← sec_nat, key, key, hc, hc, sec_res_comp, sec_res_comp, w]
  obtain ⟨t, ht, -⟩ := isSheaf_forget (cokernel κ) S hS x hx
  refine ⟨t, sub_eq_zero.1 (sec_eq_zero Gm _ ⟨S, hS, fun V g hg => ?_⟩)⟩
  have ht' : Sec.res g t = Sec.map (cokernel.π κ) (c V g hg) := ht g hg
  change (Gm.obj.map g.op).hom (Sec.map qb t - b) = 0
  rw [map_sub]
  change Sec.res g (Sec.map qb t) - Sec.res g b = 0
  rw [sec_nat, ht', key, hc, sub_self]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKummerBoundaryEtaleCohomology
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory

theorem hk_pull_ext : ∀ (R : Type) [CommRing R] {K L : Cx R} (f : L ⟶ K) {F G : Shv R} {n : ℤ} (z : Cocycle (res R F) (res R G) n) (m k : ℤ) (h : m + n = k) (x : HK R K F m),
  HK.pull R f G k (HK.ext R K z m k h x) = HK.ext R L z m k h (HK.pull R f F m x) := by
  intro R _ K L f F G n z m k h x
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.comp_assoc_of_first_is_zero_cochain]

theorem kummer_boundary : ∀ (q : ℕ) [NeZero q], ∃ κ : (restr (Int.castRingHom (ZMod q))).obj (tw q 1) ⟶ Gm, (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (u : (Γ(U, ⊤))ˣ), (u : Γ(U, ⊤)) = ζ.1 → Sec.map κ (show Sec ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) U from twGen 1 ζ) = unitSec u) ∧ ∃ bd : ∀ (E : Spc) (n : ℤ), H ℤ E Gm n →+ Ht q E (n + 1) 1, (∀ {E E' : Spc} (f : E ⟶ E'), Inv q E' → ∀ (n : ℤ) x, pull _ f _ _ (bd E' n x) = bd E n (pull _ f _ _ x)) ∧ (∀ (E : Spc), Inv q E → ∀ n : ℤ, Function.Exact (HK.post ℤ ((chains ℤ).obj E) ((q : ℤ) • 𝟙 Gm) n) (bd E n) ∧ Function.Exact (bd E n) (fun c => HK.post ℤ ((chains ℤ).obj E) κ (n + 1) (restrH (Int.castRingHom (ZMod q)) E (tw q 1) (n + 1) c)) ∧ Function.Exact (fun c => HK.post ℤ ((chains ℤ).obj E) κ (n + 1) (restrH (Int.castRingHom (ZMod q)) E (tw q 1) (n + 1) c)) (HK.post ℤ ((chains ℤ).obj E) ((q : ℤ) • 𝟙 Gm) (n + 1))) ∧ (∃ s : ℤˣ, ∀ (X : Scheme.{0}) (u : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) → bd (sch.obj X) 0 (secClass Gm (unitSec u)) = s • kum q u) ∧ ∃ s : ℤˣ, ∀ (E : Spc) (L : E ⟶ ofCat (glCat 1)), Inv q E → bd E 1 (picClass L) = s • c1 q L := by
  intro q _
  obtain ⟨κ, hmono, h0, hgen, hker, hloc⟩ := GlobalTheory.T.kummer_sequence_etale_tateTwist q
  refine ⟨κ, hgen, ?_⟩
  let S : ShortComplex (Shv ℤ) := ShortComplex.mk κ (cokernel.π κ) (cokernel.condition κ)
  have hS : S.ShortExact :=
    { exact := S.exact_of_g_is_cokernel (cokernelIsCokernel κ), mono_f := hmono, epi_g := (inferInstance : Epi (cokernel.π κ)) }
  obtain ⟨z, hex, s, hchar⟩ := GlobalTheory.T.exists_connecting_cocycle_hypercohomology_les ℤ S hS
  set qb := cokernel.desc κ ((q : ℤ) • 𝟙 Gm) h0 with hqb
  have hπq : cokernel.π κ ≫ qb = (q : ℤ) • 𝟙 Gm := cokernel.π_desc _ _ _
  have hbij := GlobalTheory.T.kummer_cokernel_to_multiplicativeGroup_bijective q κ h0 hker hloc
  have hP : ∀ E, Inv q E → ∀ n, Function.Bijective (HK.post ℤ ((chains ℤ).obj E) qb n) := fun E hE n =>
    GlobalTheory.T.etaleCohomology_bijective_of_support_bijective ℤ E qb (fun U hU => hbij U (hE U hU)) n
  have hR : ∀ E n, Function.Bijective (restrH (Int.castRingHom (ZMod q)) E (tw q 1) n) := fun E n =>
    GlobalTheory.T.etaleCohomology_coefficientRing_invariance ℤ (ZMod q) _ E (tw q 1) n
  have hpostc : ∀ (K : Cx ℤ) n x, HK.post ℤ K ((q : ℤ) • 𝟙 Gm) n x = HK.post ℤ K qb n (HK.post ℤ K (cokernel.π κ) n x) := by
    intro K n x
    rw [← hπq]
    exact (GlobalTheory.T.hypercohomologyCoefficientMap_functorial_additive ℤ K n).2.1 _ _ x
  let Pe : ∀ E, Inv q E → ∀ n, H ℤ E (cokernel κ) n ≃+ H ℤ E Gm n := fun E hE n =>
    AddEquiv.ofBijective (HK.post ℤ _ qb n) (hP E hE n)
  let Re : ∀ E n, Ht q E n 1 ≃+ H ℤ E ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) n := fun E n =>
    AddEquiv.ofBijective (restrH _ E (tw q 1) n) (hR E n)
  have hPe : ∀ E hE n x, Pe E hE n x = HK.post ℤ _ qb n x := fun _ _ _ _ => rfl
  have hRe : ∀ E n x, Re E n x = restrH _ E (tw q 1) n x := fun _ _ _ => rfl
  classical
  let bd : ∀ (E : Spc) (n : ℤ), H ℤ E Gm n →+ Ht q E (n + 1) 1 := fun E n =>
    if hE : Inv q E then
      (Re E (n + 1)).symm.toAddMonoidHom.comp ((HK.ext ℤ _ z n (n + 1) rfl).comp (Pe E hE n).symm.toAddMonoidHom)
    else 0
  have hbd : ∀ E (hE : Inv q E) n x, bd E n x = (Re E (n + 1)).symm (HK.ext ℤ _ z n (n + 1) rfl ((Pe E hE n).symm x)) := by
    intro E hE n x
    simp only [bd, dif_pos hE]
    rfl
  refine ⟨bd, ?_, ?_, ?_, ?_⟩
  · intro E E' f hE' n x
    have hE : Inv q E := fun U ⟨y⟩ => hE' U ⟨(f.app _).app _ y⟩
    rw [hbd E hE, hbd E' hE']
    apply (Re E (n + 1)).injective
    rw [AddEquiv.apply_symm_apply, hRe]
    have h1 : restrH (Int.castRingHom (ZMod q)) E (tw q 1) (n + 1) (pull _ f _ _ ((Re E' (n + 1)).symm
        (HK.ext ℤ _ z n (n + 1) rfl ((Pe E' hE' n).symm x)))) =
        pull _ f _ _ (restrH (Int.castRingHom (ZMod q)) E' (tw q 1) (n + 1) ((Re E' (n + 1)).symm
        (HK.ext ℤ _ z n (n + 1) rfl ((Pe E' hE' n).symm x)))) :=
      ((restrMap (Int.castRingHom (ZMod q)) (tw q 1)).op.nat f (n + 1) _).symm
    rw [h1, ← hRe, AddEquiv.apply_symm_apply]
    have h2 : HK.pull ℤ ((chains ℤ).map f) (cokernel κ) n ((Pe E' hE' n).symm x) = (Pe E hE n).symm (pull _ f _ _ x) := by
      apply (Pe E hE n).injective
      rw [AddEquiv.apply_symm_apply, hPe E hE n]
      change HK.post ℤ _ qb n (HK.pull ℤ ((chains ℤ).map f) _ n _) = HK.pull ℤ ((chains ℤ).map f) _ n x
      rw [← (GlobalTheory.T.hypercohomologyCoefficientMap_functorial_additive ℤ _ n).2.2.2.2 ((chains ℤ).map f) qb, ← hPe E' hE', AddEquiv.apply_symm_apply]
    change HK.pull ℤ _ _ _ (HK.ext ℤ _ z n (n + 1) rfl _) = _
    rw [hk_pull_ext, h2]
  · intro E hE n
    obtain ⟨e1, e2, e3⟩ := hex ((chains ℤ).obj E) n
    obtain ⟨e1', -, -⟩ := hex ((chains ℤ).obj E) (n + 1)
    refine ⟨fun y => ?_, fun c => ?_, fun y => ?_⟩
    · rw [hbd E hE, AddEquivClass.map_eq_zero_iff, e2]
      constructor
      · rintro ⟨w, hw⟩
        refine ⟨w, ?_⟩
        rw [hpostc, ← hPe E hE, hw]
        exact AddEquiv.apply_symm_apply _ _
      · rintro ⟨w, rfl⟩
        refine ⟨w, ?_⟩
        change _ = (Pe E hE n).symm _
        rw [hpostc, ← hPe E hE, AddEquiv.symm_apply_apply]
    · change HK.post ℤ _ κ (n + 1) (restrH _ E (tw q 1) (n + 1) c) = 0 ↔ _
      rw [show HK.post ℤ _ κ (n + 1) = HK.post ℤ _ S.f (n + 1) from rfl, e3]
      constructor
      · rintro ⟨w, hw⟩
        refine ⟨(Pe E hE n) w, ?_⟩
        rw [hbd E hE, AddEquiv.symm_apply_apply]
        apply (Re E (n + 1)).injective
        rw [AddEquiv.apply_symm_apply, hw, hRe]
      · rintro ⟨w, rfl⟩
        refine ⟨(Pe E hE n).symm w, ?_⟩
        rw [hbd E hE, ← hRe, AddEquiv.apply_symm_apply]
    · rw [hpostc]
      have : HK.post ℤ _ qb (n + 1) (HK.post ℤ _ (cokernel.π κ) (n + 1) y) = 0 ↔ HK.post ℤ _ (cokernel.π κ) (n + 1) y = 0 := by
        rw [← hPe E hE]; exact (Pe E hE (n + 1)).map_eq_zero_iff
      rw [this, show HK.post ℤ _ (cokernel.π κ) (n + 1) = HK.post ℤ _ S.g (n + 1) from rfl, e1']
      constructor
      · rintro ⟨w, rfl⟩
        refine ⟨(Re E (n + 1)).symm w, ?_⟩
        change HK.post ℤ _ κ (n + 1) (Re E (n + 1) _) = _
        rw [AddEquiv.apply_symm_apply]
      · rintro ⟨c, rfl⟩
        exact ⟨_, rfl⟩
  · refine ⟨s, fun X u hu => ?_⟩
    have hE : Inv q (sch.obj X) := by
      rintro U ⟨x⟩
      have := hu.map x.appTop.hom
      rw [map_natCast] at this
      exact this
    obtain ⟨c, hc⟩ := (hbij X hu).2 (unitSec u)
    have hpre : (Pe _ hE 0).symm (secClass Gm (unitSec u)) = secClass (cokernel κ) c := by
      apply (Pe _ hE 0).injective
      rw [AddEquiv.apply_symm_apply, hPe _ hE 0, (GlobalTheory.T.degreeZeroSectionClass_properties ℤ (cokernel κ) X).2.2.2.2 qb c, hc]
    rw [hbd _ hE, hpre, GlobalTheory.T.kummerConnecting_unitClass_eq_kummerClass q κ h0 hmono hgen hker hloc hbij z s hchar X u c hu hc, Units.smul_def, Units.smul_def,
      map_zsmul, ← hRe, AddEquiv.symm_apply_apply]
  · refine ⟨s, fun E L hE => ?_⟩
    have hy : HK.post ℤ _ qb 1 ((Pe E hE 1).symm (picClass L)) = picClass L := by
      rw [← hPe E hE, AddEquiv.apply_symm_apply]
    rw [hbd E hE, GlobalTheory.T.kummerBoundary_lineBundle_firstChernClass q κ h0 hmono hgen hker hloc hbij z s hchar E L hE _ hy, Units.smul_def, Units.smul_def,
      map_zsmul, ← hRe, AddEquiv.symm_apply_apply]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKummerBoundaryEtaleCohomologyStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_kummer_boundary_etale_cohomology : ∀ (q : ℕ) [NeZero q], ∃ κ : (restr (Int.castRingHom (ZMod q))).obj (tw q 1) ⟶ Gm, (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (u : (Γ(U, ⊤))ˣ), (u : Γ(U, ⊤)) = ζ.1 → Sec.map κ (show Sec ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) U from twGen 1 ζ) = unitSec u) ∧ ∃ bd : ∀ (E : Spc) (n : ℤ), H ℤ E Gm n →+ Ht q E (n + 1) 1, (∀ {E E' : Spc} (f : E ⟶ E'), Inv q E' → ∀ (n : ℤ) x, pull _ f _ _ (bd E' n x) = bd E n (pull _ f _ _ x)) ∧ (∀ (E : Spc), Inv q E → ∀ n : ℤ, Function.Exact (HK.post ℤ ((chains ℤ).obj E) ((q : ℤ) • 𝟙 Gm) n) (bd E n) ∧ Function.Exact (bd E n) (fun c => HK.post ℤ ((chains ℤ).obj E) κ (n + 1) (restrH (Int.castRingHom (ZMod q)) E (tw q 1) (n + 1) c)) ∧ Function.Exact (fun c => HK.post ℤ ((chains ℤ).obj E) κ (n + 1) (restrH (Int.castRingHom (ZMod q)) E (tw q 1) (n + 1) c)) (HK.post ℤ ((chains ℤ).obj E) ((q : ℤ) • 𝟙 Gm) (n + 1))) ∧ (∃ s : ℤˣ, ∀ (X : Scheme.{0}) (u : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) → bd (sch.obj X) 0 (secClass Gm (unitSec u)) = s • kum q u) ∧ ∃ s : ℤˣ, ∀ (E : Spc) (L : E ⟶ ofCat (glCat 1)), Inv q E → bd E 1 (picClass L) = s • c1 q L := by
  first | (exact @GlobalTheory.kummer_boundary) | (exact GlobalTheory.kummer_boundary) | (intros; apply GlobalTheory.kummer_boundary <;> assumption)
end
