module

public import Development.EtaleCohomology.EtaleTrace.LocalSplitting.Cover2
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupChernKummerPullbackNaturality
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.OffDiagonalContinuationInductive
public import Development.EtaleCohomology.WeilConjectures.FermatCount
public import Development.EtaleCohomology.KummerTheory.NrmMkPf
public import Development.EtaleCohomology.KummerTheory.AffRingPf
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ExistsUnitKummerEqOfPicardTorsionFree
public import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsRootOfKummerClassEqZero

@[expose] public section

section -- merged from Development.EtaleCohomology.KummerTheory.FinAlgExt
namespace LateralTheory.Fin.AlgExt
theorem etale_cohomology_place_restriction_good_reduction : LateralTheory.KummerTheory.PlaceResGood := by
  apply LateralTheory.KummerTheory.PlaceResGood_of
theorem etale_cohomology_place_localization_inductive_extension : LateralTheory.KummerTheory.PlaceStep := by
  apply LateralTheory.KummerTheory.PlaceStep_of <;> first | exact etale_cohomology_place_restriction_good_reduction
theorem etale_cohomology_place_localization_exists : LateralTheory.KummerTheory.PlaceEx := by
  apply LateralTheory.KummerTheory.PlaceEx_of_step <;> first | exact etale_cohomology_place_localization_inductive_extension
theorem etale_cohomology_place_localization_holds : LateralTheory.KummerTheory.Place := by
  apply LateralTheory.KummerTheory.Place_of_ex <;> first | exact etale_cohomology_place_localization_exists
theorem etale_cohomology_algebraic_extension_invariance_of_places : LateralTheory.KummerTheory.AlgExt := by
  apply LateralTheory.KummerTheory.AlgExt_of <;> first | exact etale_cohomology_place_localization_holds
theorem intersectionNumber_baseChange : LateralTheory.KummerTheory.AlgExt := etale_cohomology_algebraic_extension_invariance_of_places
end LateralTheory.Fin.AlgExt
end

section -- merged from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ExistsMayerVietorisConnectingExact
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace UpperTheory.Cb.MV

variable {R : Type} [CommRing R]

private theorem cpull_comp' {K L M I : Cx R} (a : K ⟶ L) (b : L ⟶ M) (n : ℤ)
    (x : CohomologyClass M I n) : cpull (a ≫ b) I n x = cpull a I n (cpull b I n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_comp]

private theorem cpull_add' {K L I : Cx R} (a b : K ⟶ L) (n : ℤ)
    (x : CohomologyClass L I n) : cpull (a + b) I n x = cpull a I n x + cpull b I n x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  rw [cpre_mk, cpre_mk, cpre_mk, ← CohomologyClass.mk_add]
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_add]

private theorem cpull_neg' {K L I : Cx R} (a : K ⟶ L) (n : ℤ)
    (x : CohomologyClass L I n) : cpull (-a) I n x = - cpull a I n x := by
  have h : cpull (-a + a) I n x = 0 := by
    rw [neg_add_cancel]
    obtain ⟨x, rfl⟩ := x.mk_surjective
    rw [cpre_mk]
    have : zcomp (Cocycle.ofHom (0 : K ⟶ L)) x (zero_add n) = 0 := by
      refine Cocycle.ext ?_
      simp [zcomp]
    rw [this]
    exact CohomologyClass.mk_zero _ _ _
  rw [cpull_add'] at h
  exact eq_neg_of_add_eq_zero_left h

private noncomputable def mvS {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) : ShortComplex (Cx R) :=
  ShortComplex.mk (biprod.lift ((chains R).map (pullback.fst f g)) (-(chains R).map (pullback.snd f g)))
    (biprod.desc ((chains R).map f) ((chains R).map g)) (by
      rw [biprod.lift_desc, Preadditive.neg_comp, ← Functor.map_comp, ← Functor.map_comp,
        pullback.condition, add_neg_cancel])

private theorem mvS_exact {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) (h : Cover2 R f g) :
    (mvS (R := R) f g).ShortExact := by
  obtain ⟨w, hw⟩ := GlobalTheory.T.etaleSpaceChains_mayerVietoris_shortExact R f g h
  exact hw

private noncomputable def mvMap {U V E U' V' E' : Spc} (f : U ⟶ E) (g : V ⟶ E) (f' : U' ⟶ E') (g' : V' ⟶ E')
    (p : E ⟶ E') (u : U ⟶ U') (v : V ⟶ V') (hu : f ≫ p = u ≫ f') (hv : g ≫ p = v ≫ g') :
    mvS (R := R) f g ⟶ mvS f' g' where
  τ₁ := (chains R).map (pullback.map f g f' g' u v p hu hv)
  τ₂ := biprod.map ((chains R).map u) ((chains R).map v)
  τ₃ := (chains R).map p
  comm₁₂ := by
    apply biprod.hom_ext
    · simp only [mvS, Category.assoc, biprod.map_fst, biprod.lift_fst, biprod.lift_fst_assoc,
        ← Functor.map_comp, pullback.lift_fst, pullback.map]
    · simp only [mvS, Category.assoc, biprod.map_snd, biprod.lift_snd, biprod.lift_snd_assoc,
        Preadditive.neg_comp, Preadditive.comp_neg, ← Functor.map_comp, pullback.lift_snd, pullback.map]
  comm₂₃ := by
    apply biprod.hom_ext'
    · simp only [mvS, biprod.inl_map_assoc, biprod.inl_desc, biprod.inl_desc_assoc, ← Functor.map_comp, hu]
    · simp only [mvS, biprod.inr_map_assoc, biprod.inr_desc, biprod.inr_desc_assoc, ← Functor.map_comp, hv]

private theorem cpull_inl_desc {K L M I : Cx R} (a : K ⟶ M) (b : L ⟶ M) (n : ℤ) (x : CohomologyClass M I n) :
    cpull (biprod.inl : K ⟶ K ⊞ L) I n (cpull (biprod.desc a b) I n x) = cpull a I n x := by
  rw [← cpull_comp', biprod.inl_desc]

private theorem cpull_inr_desc {K L M I : Cx R} (a : K ⟶ M) (b : L ⟶ M) (n : ℤ) (x : CohomologyClass M I n) :
    cpull (biprod.inr : L ⟶ K ⊞ L) I n (cpull (biprod.desc a b) I n x) = cpull b I n x := by
  rw [← cpull_comp', biprod.inr_desc]

private theorem cpull_lift {K L P I : Cx R} (a : P ⟶ K) (b : P ⟶ L) (n : ℤ) (y : CohomologyClass (K ⊞ L) I n) :
    cpull (biprod.lift a b) I n y =
      cpull a I n (cpull (biprod.inl : K ⟶ K ⊞ L) I n y) + cpull b I n (cpull (biprod.inr : L ⟶ K ⊞ L) I n y) := by
  rw [biprod.lift_eq, cpull_add', cpull_comp', cpull_comp']

end UpperTheory.Cb.MV

theorem UpperTheory.Cb.exists_mayerVietoris_connecting_exact :
    ∀ (R : Type) [CommRing R] (F : Shv R), ∃ d : ∀ {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E), Cover2 R f g → ∀ n : ℤ, H R (pullback f g) F n →+ H R E F (n + 1), (∀ {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) (h : Cover2 R f g) (n : ℤ), (∀ a b, pull R (pullback.fst f g) F n a = pull R (pullback.snd f g) F n b ↔ ∃ x, pull R f F n x = a ∧ pull R g F n x = b) ∧ (∀ c, d f g h n c = 0 ↔ ∃ a b, c = pull R (pullback.fst f g) F n a - pull R (pullback.snd f g) F n b) ∧ ∀ x, (pull R f F (n + 1) x = 0 ∧ pull R g F (n + 1) x = 0) ↔ ∃ c, d f g h n c = x) ∧ ∀ {U V E U' V' E' : Spc} (f : U ⟶ E) (g : V ⟶ E) (f' : U' ⟶ E') (g' : V' ⟶ E') (p : E ⟶ E') (u : U ⟶ U') (v : V ⟶ V') (hu : f ≫ p = u ≫ f') (hv : g ≫ p = v ≫ g') (h : Cover2 R f g) (h' : Cover2 R f' g') (n : ℤ) c, pull R p F (n + 1) (d f' g' h' n c) = d f g h n (pull R (pullback.map f g f' g' u v p hu hv) F n c) := by
  intro R _ F
  obtain ⟨D, hex, hnat⟩ := GlobalTheory.T.hypercohomology_longExact_first_of_injective R (res R F) (fun n => by dsimp only [res]; infer_instance)
  have hbij := fun (K L : Cx R) (n : ℤ) => GlobalTheory.T.hypercohomologyPullback_biprod_inl_inr_bijective R K L (res R F) n

  have hf : ∀ {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) (n : ℤ) (y : CohomologyClass (((chains R).obj U) ⊞ ((chains R).obj V)) (res R F) n),
      cpull (UpperTheory.Cb.MV.mvS (R := R) f g).f (res R F) n y =
        pull R (pullback.fst f g) F n (cpull biprod.inl (res R F) n y) -
          pull R (pullback.snd f g) F n (cpull biprod.inr (res R F) n y) := by
    intro U V E f g n y
    refine (UpperTheory.Cb.MV.cpull_lift (I := res R F) ((chains R).map (pullback.fst f g)) (-(chains R).map (pullback.snd f g)) n y).trans ?_
    rw [UpperTheory.Cb.MV.cpull_neg', sub_eq_add_neg]
    rfl
  refine ⟨fun {U V E} f g h n => D (UpperTheory.Cb.MV.mvS f g) (UpperTheory.Cb.MV.mvS_exact f g h) n, ?_, ?_⟩
  · intro U V E f g h n
    obtain ⟨e₁, e₂, e₃⟩ := hex (UpperTheory.Cb.MV.mvS f g) (UpperTheory.Cb.MV.mvS_exact f g h) n
    have hi := fun (m : ℤ) (x : H R E F m) => UpperTheory.Cb.MV.cpull_inl_desc (I := res R F) ((chains R).map f) ((chains R).map g) m x
    have hr := fun (m : ℤ) (x : H R E F m) => UpperTheory.Cb.MV.cpull_inr_desc (I := res R F) ((chains R).map f) ((chains R).map g) m x
    refine ⟨?_, ?_, ?_⟩
    · intro a b
      obtain ⟨y, hy⟩ := (hbij ((chains R).obj U) ((chains R).obj V) n).2 (a, b)
      have hya : cpull biprod.inl (res R F) n y = a := congrArg Prod.fst hy
      have hyb : cpull biprod.inr (res R F) n y = b := congrArg Prod.snd hy
      have key := e₁ y
      rw [hf, hya, hyb] at key
      refine (sub_eq_zero.symm.trans key).trans ?_
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨x, (hi n x).symm.trans hya, (hr n x).symm.trans hyb⟩
      · rintro ⟨x, hxa, hxb⟩
        refine ⟨x, (hbij ((chains R).obj U) ((chains R).obj V) n).1 ?_⟩
        exact Prod.ext ((hi n x).trans (hxa.trans hya.symm)) ((hr n x).trans (hxb.trans hyb.symm))
    · intro c
      refine (e₂ c).trans ?_
      constructor
      · rintro ⟨y, rfl⟩
        exact ⟨_, _, hf f g n y⟩
      · rintro ⟨a, b, rfl⟩
        obtain ⟨y, hy⟩ := (hbij ((chains R).obj U) ((chains R).obj V) n).2 (a, b)
        have hya : cpull biprod.inl (res R F) n y = a := congrArg Prod.fst hy
        have hyb : cpull biprod.inr (res R F) n y = b := congrArg Prod.snd hy
        refine ⟨y, ?_⟩
        rw [hf, hya, hyb]
    · intro x
      constructor
      · rintro ⟨h1, h2⟩
        refine (e₃ x).1 ((hbij ((chains R).obj U) ((chains R).obj V) (n + 1)).1 ?_)
        have z1 : cpull (biprod.inl : (chains R).obj U ⟶ (chains R).obj U ⊞ (chains R).obj V) (res R F) (n + 1) 0 = 0 := map_zero _
        have z2 : cpull (biprod.inr : (chains R).obj V ⟶ (chains R).obj U ⊞ (chains R).obj V) (res R F) (n + 1) 0 = 0 := map_zero _
        exact Prod.ext ((hi (n + 1) x).trans (h1.trans z1.symm)) ((hr (n + 1) x).trans (h2.trans z2.symm))
      · intro hc
        have h0 : cpull (biprod.desc ((chains R).map f) ((chains R).map g)) (res R F) (n + 1) x = 0 := (e₃ x).2 hc
        have h1 := hi (n + 1) x
        have h2 := hr (n + 1) x
        rw [h0, map_zero] at h1 h2
        exact ⟨h1.symm, h2.symm⟩
  · intro U V E U' V' E' f g f' g' p u v hu hv h h' n c
    exact hnat _ _ (UpperTheory.Cb.MV.mvS_exact f g h) (UpperTheory.Cb.MV.mvS_exact f' g' h')
      (UpperTheory.Cb.MV.mvMap f g f' g' p u v hu hv) n c
end

section -- merged from Development.EtaleCohomology.WeilConjectures.EmptyVan2
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.EWeil.EmptyVan₂

instance isEmpty_bot : IsEmpty (⊥_ Scheme.{0}) := by
  infer_instance

theorem sec_subsingleton {R : Type} [CommRing R] (G : Shv R) {U : Scheme.{0}} (f : U ⟶ ⊥_ Scheme.{0}) :
    Subsingleton (G.obj.obj (op U)) := by
  have : IsEmpty U := ⟨fun x => isEmptyElim (f.base x)⟩
  exact (ModuleCat.isZero_iff_subsingleton).1
    (IsTerminal.isZero (Sheaf.isTerminalOfBotCover G U (Scheme.bot_mem_grothendieckTopology U)))

theorem free_hom_subsingleton {R : Type} [CommRing R] (G : Shv R) :
    Subsingleton ((free R).obj (yoneda.obj (⊥_ Scheme.{0})) ⟶ G) := by
  constructor
  intro f g
  apply ((sheafificationAdjunction Scheme.etaleTopology.{0} _).homEquiv _ _).injective
  ext U x
  by_cases h : Nonempty (U.unop ⟶ ⊥_ Scheme.{0})
  · obtain ⟨φ⟩ := h
    exact @Subsingleton.elim _ (sec_subsingleton G φ) _ _
  · have : IsEmpty (U.unop ⟶ ⊥_ Scheme.{0}) := not_nonempty_iff.1 h
    have hx : x = 0 := Finsupp.ext fun a => isEmptyElim (a.down : U.unop ⟶ ⊥_ Scheme.{0})
    subst hx
    simp only [map_zero]

theorem isZero_free {R : Type} [CommRing R] : IsZero ((free R).obj (yoneda.obj (⊥_ Scheme.{0}))) := by
  rw [IsZero.iff_id_eq_zero]
  have := free_hom_subsingleton (R := R) ((free R).obj (yoneda.obj (⊥_ Scheme.{0})))
  exact Subsingleton.elim _ _

end LateralTheory.EWeil.EmptyVan₂
end
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsH1MuOfLocallyUnitTimesPower
section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsH1MuGlueOfCompatible
section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.H1PlEqZeroOfLeISupOfLocalZero
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

namespace UpperTheory.Cb.SeparatedH1Cohomology

private theorem res_nsmul' {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (k : V ⟶ U) (n : ℕ)
    (a : Sec F U) : Sec.res k (n • a) = n • Sec.res k a :=
  map_nsmul (F.obj.map k.op).hom n a

private theorem exists_h0_restriction_eq_of_le_open {q : ℕ} [NeZero q] {X E : Scheme.{0}} [IsIntegral X] (ζ : Prim q Γ(X, ⊤))
    (j : E ⟶ X) [IsOpenImmersion j] {O P : E.Opens} (h : P ≤ O) (c : Ht q (sch.obj P) 0 1) :
    ∃ a : Ht q (sch.obj O) 0 1, pl q 1 (E.homOfLE h) 0 a = c := by
  obtain ⟨-, e, he, -⟩ := GlobalTheory.T.etaleCohomology_negative_vanishing_degree_zero (ZMod q) (tw q 1)
  by_cases hP : Nonempty (P : Scheme.{0})
  · haveI : IsIntegral (P : Scheme.{0}) := isIntegral_of_isOpenImmersion (P.ι ≫ j)
    haveI : ConnectedSpace (P : Scheme.{0}) := inferInstance
    obtain ⟨k, hk⟩ := UpperTheory.twisted_section_eq_nsmul_generator_of_connected q 1 (P : Scheme.{0}) (ζ.map (P.ι ≫ j).appTop.hom) ((e P).symm c)
    refine ⟨e O (k • twGen 1 (ζ.map (O.ι ≫ j).appTop.hom)), ?_⟩
    have h1 : c = e P (k • twGen 1 (ζ.map (P.ι ≫ j).appTop.hom)) := by
      rw [← hk, AddEquiv.apply_symm_apply]
    have hk : E.homOfLE h ≫ O.ι ≫ j = P.ι ≫ j := by simp
    rw [h1, he, res_nsmul', (GlobalTheory.T.tateTwist_sections_locally_generated q 1).2.2.2.1, ← hk]
    congr 1
  · have hb : P = ⊥ := le_bot_iff.1 fun p hp => (hP ⟨(⟨p, hp⟩ : P)⟩).elim
    subst hb
    haveI := LateralTheory.E.E8.leafEmptyVanish (ZMod q) (X := E) (tw q 1) 0
    exact ⟨0, Subsingleton.elim _ _⟩

private theorem two {q : ℕ} [NeZero q] {X E : Scheme.{0}} [IsIntegral X] (ζ : Prim q Γ(X, ⊤))
    (j : E ⟶ X) [IsOpenImmersion j] (O₁ O₂ : E.Opens) (hcov : O₁ ⊔ O₂ = ⊤) (y : Ht q (sch.obj E) 1 1)
    (h₁ : pl q 1 O₁.ι 1 y = 0) (h₂ : pl q 1 O₂.ι 1 y = 0) : y = 0 := by
  obtain ⟨d, hd, -⟩ := UpperTheory.Cb.exists_mayerVietoris_connecting_exact (ZMod q) (tw q 1)
  have hc : Cover2 (ZMod q) (sch.map O₁.ι) (sch.map O₂.ι) := LateralTheory.EtaleTrace.LSplitPf.Sch.cover2 (ZMod q) O₁ O₂ hcov
  have : PreservesLimitsOfShape WalkingCospan sch := by
    unfold sch
    infer_instance
  let e := ((isPullback_opens_inf O₁ O₂).map sch).isoPullback
  obtain ⟨-, hz, hx⟩ := hd _ _ hc 0
  obtain ⟨c, hcy⟩ := (hx y).1 ⟨h₁, h₂⟩
  obtain ⟨a, ha⟩ := exists_h0_restriction_eq_of_le_open ζ j (inf_le_left : O₁ ⊓ O₂ ≤ O₁) (pull (ZMod q) e.hom (tw q 1) 0 c)
  have hf : pullback.fst (sch.map O₁.ι) (sch.map O₂.ι) = e.inv ≫ sch.map (E.homOfLE inf_le_left) := by
    simp [e]
  have h0 : d _ _ hc 0 c = 0 := by
    refine (hz c).2 ⟨a, 0, ?_⟩
    rw [map_zero, sub_zero, hf, pull_comp]
    change c = pull _ e.inv _ 0 (pl q 1 _ 0 a)
    rw [ha, ← pull_comp, e.inv_hom_id, pull_id]
  exact hcy.symm.trans h0

private theorem step {q : ℕ} [NeZero q] {X : Scheme.{0}} [IsIntegral X] (ζ : Prim q Γ(X, ⊤))
    (A B : X.Opens) (x : Ht q (sch.obj X) 1 1) (hA : pl q 1 A.ι 1 x = 0) (hB : pl q 1 B.ι 1 x = 0) :
    pl q 1 (A ⊔ B).ι 1 x = 0 := by
  have key : ∀ C : X.Opens, pl q 1 C.ι 1 x = 0 →
      pl q 1 ((A ⊔ B).ι ⁻¹ᵁ C).ι 1 (pl q 1 (A ⊔ B).ι 1 x) = 0 := by
    intro C hC
    have h1 : ((A ⊔ B).ι ⁻¹ᵁ C).ι ≫ (A ⊔ B).ι = ((A ⊔ B).ι ∣_ C) ≫ C.ι := (morphismRestrict_ι _ _).symm
    change pull _ _ _ _ (pull _ _ _ _ x) = 0
    rw [← pull_comp, ← sch.map_comp, h1, sch.map_comp, pull_comp]
    change pull _ _ _ _ (pl q 1 C.ι 1 x) = 0
    rw [hC, map_zero]
  refine two ζ (A ⊔ B).ι ((A ⊔ B).ι ⁻¹ᵁ A) ((A ⊔ B).ι ⁻¹ᵁ B) ?_ _ (key A hA) (key B hB)
  refine eq_top_iff.2 fun p _ => ?_
  have hp : (A ⊔ B).ι p ∈ A ⊔ B := p.2
  exact TopologicalSpace.Opens.mem_sup.2 (TopologicalSpace.Opens.mem_sup.1 hp)

end UpperTheory.Cb.SeparatedH1Cohomology

theorem UpperTheory.h1_pl_eq_zero_of_le_iSup_of_local_zero :
    ∀ (q : ℕ) [NeZero q] (X : Scheme.{0}) [IsIntegral X], Nonempty (Prim q Γ(X, ⊤)) → IsUnit (q : Γ(X, ⊤)) → ∀ (n : ℕ) (U : Fin n → X.Opens) (V : X.Opens), V ≤ ⨆ i, U i → ∀ x : Ht q (sch.obj X) 1 1, (∀ i, pl q 1 (U i).ι 1 x = 0) → pl q 1 V.ι 1 x = 0 := by
  intro q _ X _ hζ _ n
  obtain ⟨ζ⟩ := hζ
  induction n with
  | zero =>
    intro U V hV x _
    have hb : V = ⊥ := le_bot_iff.1 (hV.trans (iSup_of_empty U).le)
    subst hb
    haveI := LateralTheory.E.E8.leafEmptyVanish (ZMod q) (X := X) (tw q 1) 1
    exact Subsingleton.elim _ _
  | succ n ih =>
    intro U V hV x hx
    have hW := ih (fun i => U i.castSucc) (⨆ i : Fin n, U i.castSucc) le_rfl x (fun i => hx _)
    have hS := UpperTheory.Cb.SeparatedH1Cohomology.step ζ _ _ x hW (hx (Fin.last n))
    have hle : V ≤ (⨆ i : Fin n, U i.castSucc) ⊔ U (Fin.last n) := hV.trans (iSup_le fun i => by
      induction i using Fin.lastCases with
      | last => exact le_sup_right
      | cast i => exact le_sup_of_le_left (le_iSup (fun i : Fin n => U i.castSucc) i))
    have hι : V.ι = X.homOfLE hle ≫ ((⨆ i : Fin n, U i.castSucc) ⊔ U (Fin.last n)).ι := by simp
    rw [hι]
    change pull _ (sch.map _) _ _ x = 0
    rw [sch.map_comp, pull_comp]
    change pull _ _ _ _ (pl q 1 _ 1 x) = 0
    rw [hS, map_zero]
end

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

namespace UpperTheory.Cb.MuCohomologyGluing

private theorem sub_empty (q : ℕ) (Y : Scheme.{0}) [IsEmpty Y] (n i : ℤ) :
    Subsingleton (Ht q (sch.obj Y) n i) := by
  have e : Y ≅ ⊥_ Scheme.{0} := (isInitialOfIsEmpty (X := Y)).uniqueUpToIso initialIsInitial
  exact LateralTheory.EtaleTrace.H_sub (ZMod q) Y
    (LateralTheory.EWeil.EmptyVan₂.isZero_free.of_iso ((free (ZMod q)).mapIso (yoneda.mapIso e))) (tw q i) n

private theorem pl_le (q : ℕ) {X : Scheme.{0}} {A B C : X.Opens} (h1 : A ≤ B) (h2 : B ≤ C) (h3 : A ≤ C)
    (z : Ht q (sch.obj C) 1 1) :
    pl q 1 (X.homOfLE h1) 1 (pl q 1 (X.homOfLE h2) 1 z) = pl q 1 (X.homOfLE h3) 1 z := by
  rw [← pl_comp, Scheme.homOfLE_homOfLE]

private theorem van (q : ℕ) [NeZero q] (X : Scheme.{0}) [IsIntegral X] (hζ : Nonempty (Prim q Γ(X, ⊤)))
    (hq : IsUnit (q : Γ(X, ⊤))) (n : ℕ) (A : Fin n → X.Opens) (P : X.Opens) (hP : P ≤ ⨆ i, A i)
    (d : Ht q (sch.obj P) 1 1)
    (hd : ∀ i, pl q 1 (X.homOfLE (inf_le_right : A i ⊓ P ≤ P)) 1 d = 0) : d = 0 := by
  have hmem : ∀ x : P.toScheme, P.ι x ∈ P := fun x => by
    rw [← SetLike.mem_coe, ← P.range_ι]
    exact ⟨x, rfl⟩
  by_cases hne : Nonempty P.toScheme
  · haveI : IsIntegral P.toScheme := isIntegral_of_isOpenImmersion P.ι
    have hζ' : Nonempty (Prim q Γ(P.toScheme, ⊤)) := hζ.map (Prim.map P.ι.appTop.hom)
    have hq' : IsUnit (q : Γ(P.toScheme, ⊤)) := by simpa using hq.map P.ι.appTop.hom
    have key := UpperTheory.h1_pl_eq_zero_of_le_iSup_of_local_zero q P.toScheme hζ' hq' n (fun i => P.ι ⁻¹ᵁ A i) ⊤ (by
      intro x _
      have hx : P.ι x ∈ ⨆ i, A i := hP (hmem x)
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩) d (fun i => by
        have e : P.ι ⁻¹ᵁ A i ≤ P.ι ⁻¹ᵁ (A i ⊓ P) := by
          intro x hx
          exact ⟨hx, hmem x⟩
        have w : P.ι.resLE (A i ⊓ P) (P.ι ⁻¹ᵁ A i) e ≫ X.homOfLE (inf_le_right : A i ⊓ P ≤ P) =
            (P.ι ⁻¹ᵁ A i).ι := by
          rw [← cancel_mono P.ι]
          simp
        rw [← w, pl_comp, hd i, map_zero])
    have w : P.toScheme.topIso.inv ≫ (⊤ : P.toScheme.Opens).ι = 𝟙 _ := P.toScheme.topIso.inv_hom_id
    have := congrArg (pl q 1 P.toScheme.topIso.inv 1) key
    rw [← pl_comp, w, map_zero] at this
    simpa [pl, pull_id] using this
  · haveI : IsEmpty P.toScheme := not_nonempty_iff.1 hne
    haveI := sub_empty q P.toScheme 1 1
    exact Subsingleton.elim _ _

end UpperTheory.Cb.MuCohomologyGluing

open UpperTheory.Cb.MuCohomologyGluing in
theorem UpperTheory.exists_h1Mu_glue_of_compatible :
    ∀ (q : ℕ) [NeZero q] (X : Scheme.{0}) [IsIntegral X], Nonempty (Prim q Γ(X, ⊤)) → IsUnit (q : Γ(X, ⊤)) → ∀ (n : ℕ) (U : Fin n → X.Opens) (x : ∀ i, Ht q (sch.obj (U i)) 1 1), (∀ i j, pl q 1 (X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i)) 1 (x i) = pl q 1 (X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j)) 1 (x j)) → ∃ y : Ht q (sch.obj (⨆ i, U i : X.Opens)) 1 1, ∀ i, pl q 1 (X.homOfLE (le_iSup U i)) 1 y = x i := by
  intro q _ X _ hζ hq n
  induction n with
  | zero =>
    intro U x _
    exact ⟨0, fun i => i.elim0⟩
  | succ n ih =>
    intro U x hx
    set W : X.Opens := ⨆ i : Fin n, U i.castSucc with hW
    have hAW : ∀ i : Fin n, U i.castSucc ≤ W := fun i => le_iSup (fun i : Fin n => U i.castSucc) i
    obtain ⟨y, hy⟩ : ∃ y : Ht q (sch.obj W) 1 1, ∀ i : Fin n, pl q 1 (X.homOfLE (hAW i)) 1 y = x i.castSucc :=
      ih (fun i => U i.castSucc) (fun i => x i.castSucc) (fun i j => hx _ _)
    set B : X.Opens := U (Fin.last n) with hB
    have c : UpperTheory.Cb.OffDiagonalContinuation.Sq W B (W ⊔ B) (W ⊓ B) := ⟨rfl, rfl⟩
    obtain ⟨dd, hdd, -⟩ := UpperTheory.Cb.OffDiagonalContinuation.mv q 1
    have hex := (hdd c 1).2.2
    have d0 : pl q 1 (X.homOfLE (inf_le_left : W ⊓ B ≤ W)) 1 y -
        pl q 1 (X.homOfLE (inf_le_right : W ⊓ B ≤ B)) 1 (x (Fin.last n)) = 0 := by
      refine van q X hζ hq n (fun i => U i.castSucc) (W ⊓ B) inf_le_left _ (fun i => ?_)
      have h1 : U i.castSucc ⊓ (W ⊓ B) ≤ U i.castSucc ⊓ B := inf_le_inf_left _ inf_le_right
      rw [map_sub, pl_le q _ _ (inf_le_right.trans inf_le_left), pl_le q _ _ (inf_le_right.trans inf_le_right),
        ← pl_le q (inf_le_left : U i.castSucc ⊓ (W ⊓ B) ≤ U i.castSucc) (hAW i),
        ← pl_le q h1 (inf_le_right : U i.castSucc ⊓ B ≤ B), hy i, ← hx i.castSucc (Fin.last n),
        pl_le q h1 inf_le_left inf_le_left, sub_self]
    obtain ⟨z, hz⟩ := (hex (y, x (Fin.last n))).1 d0
    have hz1 : pl q 1 (X.homOfLE (le_sup_left : W ≤ W ⊔ B)) 1 z = y := congrArg Prod.fst hz
    have hz2 : pl q 1 (X.homOfLE (le_sup_right : B ≤ W ⊔ B)) 1 z = x (Fin.last n) := congrArg Prod.snd hz
    have hle : (⨆ i, U i : X.Opens) ≤ W ⊔ B := by
      refine iSup_le fun i => ?_
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact le_sup_right
      · exact (hAW j).trans le_sup_left
    refine ⟨pl q 1 (X.homOfLE hle) 1 z, fun i => ?_⟩
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [pl_le q _ _ le_sup_right, hz2]
    · rw [pl_le q _ _ ((hAW j).trans le_sup_left), ← pl_le q (hAW j) (le_sup_left : W ≤ W ⊔ B), hz1]
      exact hy j
end

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

namespace UpperTheory.PicGlue

variable {X : Scheme.{0}}

private theorem top_le (V : X.Opens) : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V := by simp

private theorem top_pre {A B : Scheme.{0}} (f : A ⟶ B) : (⊤ : A.Opens) ≤ f ⁻¹ᵁ (⊤ : B.Opens) :=
  fun _ _ => trivial

private theorem appTop_eq {A B : Scheme.{0}} (f : A ⟶ B) : f.appTop = f.appLE ⊤ ⊤ (top_pre f) :=
  Scheme.Hom.app_eq_appLE f

private noncomputable def rho (V : X.Opens) : Γ(X, V) →+* Γ(V.toScheme, ⊤) :=
  (V.ι.appLE V ⊤ (top_le V)).hom

private theorem appLE_congr' {A B : Scheme.{0}} {g g' : A ⟶ B} (hg : g = g') (V : B.Opens) (W : A.Opens)
    (h : W ≤ g ⁻¹ᵁ V) (h' : W ≤ g' ⁻¹ᵁ V) : g.appLE V W h = g'.appLE V W h' := by
  subst hg; rfl

private theorem rho_res {U V : X.Opens} (e : V ≤ U) (s : Γ(X, U)) :
    (X.homOfLE e).appTop.hom (rho U s) = rho V ((X.presheaf.map (homOfLE e).op).hom s) := by
  have h1 : U.ι.appLE U ⊤ (top_le U) ≫ (X.homOfLE e).appTop =
      X.presheaf.map (homOfLE e).op ≫ V.ι.appLE V ⊤ (top_le V) := by
    rw [Scheme.Hom.map_appLE, appTop_eq, Scheme.Hom.appLE_comp_appLE]
    exact appLE_congr' (X.homOfLE_ι e) _ _ _ _
  exact congr($(h1).hom s)

private theorem rho_generic (U : X.Opens) (x : X) (hx : x ∈ U) (s : Γ(X, U)) :
    (U.fromSpecStalkOfMem x hx).appTop.hom (rho U s) =
      (Scheme.ΓSpecIso (X.presheaf.stalk x)).inv.hom ((X.presheaf.germ U x hx).hom s) := by
  have hp : ⊤ ≤ X.fromSpecStalk x ⁻¹ᵁ U := by
    intro z _
    have hz : X.fromSpecStalk x z ⤳ x := by
      have : X.fromSpecStalk x z ∈ Set.range (X.fromSpecStalk x) := ⟨z, rfl⟩
      rwa [Scheme.range_fromSpecStalk] at this
    exact hz.mem_open U.2 hx
  have h1 : U.ι.appLE U ⊤ (top_le U) ≫ (U.fromSpecStalkOfMem x hx).appTop =
      X.presheaf.germ U x hx ≫ (Scheme.ΓSpecIso (X.presheaf.stalk x)).inv := by
    rw [appTop_eq, Scheme.Hom.appLE_comp_appLE,
      appLE_congr' (Scheme.Opens.fromSpecStalkOfMem_ι U x hx) U ⊤ _ hp,
      Scheme.Hom.appLE, Scheme.fromSpecStalk_app hx]
    simp only [Category.assoc, ← Functor.map_comp]
    have e : ((homOfLE le_top).op ≫ (homOfLE hp).op :
        Opposite.op (⊤ : (Spec (X.presheaf.stalk x)).Opens) ⟶ Opposite.op ⊤) = 𝟙 _ := rfl
    rw [e, CategoryTheory.Functor.map_id, Category.comp_id]
  exact congr($(h1).hom s)

private theorem sec [IsIntegral X] (V : X.Opens) [Nonempty V] (f : X.functionField)
    (h : ∀ x ∈ V, ∃ w : X.presheaf.stalk x, algebraMap _ X.functionField w = f) :
    ∃ s : Γ(X, V), X.germToFunctionField V s = f := by
  have hloc : ∀ x : V, ∃ (W : X.Opens) (hxW : x.1 ∈ W), W ≤ V ∧
      ∃ s : Γ(X, W), X.germToFunctionField W (h := ⟨⟨x.1, hxW⟩⟩) s = f := by
    intro x
    obtain ⟨w, hw⟩ := h x.1 x.2
    obtain ⟨W, hxW, g, hg⟩ := X.presheaf.exists_germ_eq w
    refine ⟨W ⊓ V, ⟨hxW, x.2⟩, inf_le_right, X.presheaf.map (homOfLE inf_le_left).op g, ?_⟩
    have : Nonempty W := ⟨⟨x.1, hxW⟩⟩
    rw [← hw, ← hg, Scheme.algebraMap_germ_eq_germToFunctionField]
    simp
  choose W hxW hWV s hs using hloc
  have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.obj W s := by
    intro i j
    obtain ⟨y, hy⟩ : ((W i : Set X) ∩ W j).Nonempty :=
      nonempty_preirreducible_inter (W i).isOpen (W j).isOpen ⟨_, hxW i⟩ ⟨_, hxW j⟩
    have : Nonempty (W i ⊓ W j : X.Opens) := ⟨⟨y, hy⟩⟩
    have : Nonempty (W i) := ⟨⟨_, hxW i⟩⟩
    have : Nonempty (W j) := ⟨⟨_, hxW j⟩⟩
    apply Scheme.germToFunctionField_injective X (W i ⊓ W j)
    change X.germToFunctionField (W i ⊓ W j) (X.presheaf.map (homOfLE inf_le_left).op (s i)) =
      X.germToFunctionField (W i ⊓ W j) (X.presheaf.map (homOfLE inf_le_right).op (s j))
    simp [hs]
  obtain ⟨t, ht, -⟩ := X.sheaf.existsUnique_gluing' W V (fun i => homOfLE (hWV i))
    (fun x hx => TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxW _⟩) s hcompat
  refine ⟨t, ?_⟩
  obtain ⟨i⟩ := ‹Nonempty V›
  have : Nonempty (W i) := ⟨⟨_, hxW i⟩⟩
  rw [← hs i, ← ht i]
  change _ = X.germToFunctionField (W i) (X.presheaf.map (homOfLE (hWV i)).op t)
  exact (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm

private theorem sec_unit [IsIntegral X] (hn : ∀ y : X, IsIntegrallyClosed (X.presheaf.stalk y)) (q : ℕ) (hq : q ≠ 0)
    (W : X.Opens) [Nonempty W] (g : (X.functionField)ˣ) (c : (Γ(X, W))ˣ)
    (hc : X.germToFunctionField W (c : Γ(X, W)) = (g : X.functionField) ^ q) :
    ∃ w : (Γ(X, W))ˣ, X.germToFunctionField W (w : Γ(X, W)) = g := by
  have key : ∀ (f : X.functionField) (d : Γ(X, W)), X.germToFunctionField W d = f ^ q →
      ∃ s : Γ(X, W), X.germToFunctionField W s = f := by
    intro f d hd
    refine sec W f fun x hx => ?_
    have := hn x
    have h1 : IsIntegral (X.presheaf.stalk x) (f ^ q) := by
      rw [← hd, ← Scheme.algebraMap_germ_eq_germToFunctionField X hx]
      exact isIntegral_algebraMap
    exact (IsIntegrallyClosed.isIntegral_iff (K := X.functionField)).1 (h1.of_pow (Nat.pos_of_ne_zero hq))
  obtain ⟨s, hs⟩ := key g c hc
  obtain ⟨s', hs'⟩ := key (g⁻¹ : (X.functionField)ˣ) ((c⁻¹ : (Γ(X, W))ˣ) : Γ(X, W)) (by
    have h2 : X.germToFunctionField W ((c⁻¹ : (Γ(X, W))ˣ) : Γ(X, W)) * X.germToFunctionField W (c : Γ(X, W)) = 1 := by
      rw [← map_mul]; simp
    rw [hc] at h2
    rw [eq_comm, ← mul_right_inj' (pow_ne_zero q g.ne_zero)]
    rw [← mul_pow]
    simpa [mul_comm] using h2.symm)
  have h3 : s * s' = 1 := Scheme.germToFunctionField_injective X W (by
    rw [map_mul, hs, hs', map_one]; simp)
  have h4 : s' * s = 1 := by rw [mul_comm]; exact h3
  exact ⟨⟨s, s', h3, h4⟩, hs⟩

private theorem spread (y : X) (u : (X.presheaf.stalk y)ˣ) :
    ∃ (W : X.Opens) (hy : y ∈ W) (v : (Γ(X, W))ˣ), (X.presheaf.germ W y hy).hom (v : Γ(X, W)) = u := by
  obtain ⟨W, hW, s, hs⟩ := X.presheaf.exists_germ_eq (u : X.presheaf.stalk y)
  have hb : y ∈ X.basicOpen s := (X.mem_basicOpen s y hW).2 (by rw [hs]; exact u.isUnit)
  refine ⟨X.basicOpen s, hb, (X.toRingedSpace.isUnit_res_basicOpen s).unit, ?_⟩
  rw [IsUnit.unit_spec, ← hs]
  exact X.presheaf.germ_res_apply _ _ _ _

end UpperTheory.PicGlue

namespace UpperTheory.PicGlue

variable {X : Scheme.{0}}

private theorem qU (q : ℕ) (hq : IsUnit (q : Γ(X, ⊤))) (V : X.Opens) : IsUnit (q : Γ(V.toScheme, ⊤)) := by
  simpa using hq.map V.ι.appTop.hom

private noncomputable def tr (V : X.Opens) (v : (Γ(X, V))ˣ) : (Γ(V.toScheme, ⊤))ˣ :=
  Units.map (rho V).toMonoidHom v

private noncomputable def resU {U V : X.Opens} (e : V ≤ U) (v : (Γ(X, U))ˣ) : (Γ(X, V))ˣ :=
  Units.map (X.presheaf.map (homOfLE e).op).hom.toMonoidHom v

private theorem nat_tr (q : ℕ) [NeZero q] (hq : IsUnit (q : Γ(X, ⊤))) {U V : X.Opens} (e : V ≤ U) (v : (Γ(X, U))ˣ) :
    pl q 1 (X.homOfLE e) 1 (kum q (tr U v)) = kum q (tr V (resU e v)) := by
  have h := (GlobalTheory.T.kummerClassOfUnit_cocycle_natural_additive q).2.1 (X.homOfLE e) (tr U v) (qU q hq U)
  have h2 : Units.map (X.homOfLE e).appTop.hom.toMonoidHom (tr U v) = tr V (resU e v) := by
    ext
    exact rho_res e _
  exact h.trans (congrArg _ h2)

private theorem gtf_res [IsIntegral X] {U V : X.Opens} [Nonempty U] [Nonempty V] (e : V ≤ U) (s : Γ(X, U)) :
    X.germToFunctionField V ((X.presheaf.map (homOfLE e).op).hom s) = X.germToFunctionField U s :=
  TopCat.Presheaf.germ_res_apply _ _ _ _ _

private theorem agree [IsIntegral X] (q : ℕ) [NeZero q] (hq : IsUnit (q : Γ(X, ⊤)))
    (hn : ∀ y : X, IsIntegrallyClosed (X.presheaf.stalk y)) (F : X.functionField) {U V W : X.Opens}
    [Nonempty U] [Nonempty V] [Nonempty W] (eU : W ≤ U) (eV : W ≤ V) (v : (Γ(X, U))ˣ) (v' : (Γ(X, V))ˣ)
    (h h' : (X.functionField)ˣ) (hF : F = X.germToFunctionField U (v : Γ(X, U)) * (h : X.functionField) ^ q)
    (hF' : F = X.germToFunctionField V (v' : Γ(X, V)) * (h' : X.functionField) ^ q) :
    pl q 1 (X.homOfLE eU) 1 (kum q (tr U v)) = pl q 1 (X.homOfLE eV) 1 (kum q (tr V v')) := by
  rw [nat_tr q hq, nat_tr q hq]
  have hA : X.germToFunctionField W (resU eU v : Γ(X, W)) = X.germToFunctionField U (v : Γ(X, U)) := gtf_res eU _
  have hB : X.germToFunctionField W (resU eV v' : Γ(X, W)) = X.germToFunctionField V (v' : Γ(X, V)) := gtf_res eV _
  have hb : X.germToFunctionField V (v' : Γ(X, V)) ≠ 0 := (v'.isUnit.map (X.germToFunctionField V).hom).ne_zero
  have hc1 : X.germToFunctionField W ((resU eU v * (resU eV v')⁻¹ : (Γ(X, W))ˣ) : Γ(X, W)) *
      X.germToFunctionField V (v' : Γ(X, V)) = X.germToFunctionField U (v : Γ(X, U)) := by
    rw [← hA, ← hB, ← map_mul]
    simp
  have hh : (h : X.functionField) ^ q ≠ 0 := pow_ne_zero q h.ne_zero
  have hc : X.germToFunctionField W ((resU eU v * (resU eV v')⁻¹ : (Γ(X, W))ˣ) : Γ(X, W)) =
      (((h' / h : (X.functionField)ˣ)) : X.functionField) ^ q := by
    rw [Units.val_div_eq_div_val, div_pow, eq_div_iff hh]
    have h3 : X.germToFunctionField V (v' : Γ(X, V)) *
        (X.germToFunctionField W ((resU eU v * (resU eV v')⁻¹ : (Γ(X, W))ˣ) : Γ(X, W)) * (h : X.functionField) ^ q) =
        X.germToFunctionField V (v' : Γ(X, V)) * (h' : X.functionField) ^ q := by
      rw [← hF', hF, ← hc1]
      ring
    exact mul_left_cancel₀ hb h3
  obtain ⟨w, hw⟩ := sec_unit hn q (NeZero.ne q) W (h' / h) _ hc
  have hrel : resU eU v = resU eV v' * w ^ q := by
    have h4 : resU eU v * (resU eV v')⁻¹ = w ^ q := by
      ext
      apply Scheme.germToFunctionField_injective X W
      rw [hc, Units.val_pow_eq_pow_val, map_pow, hw]
    rw [← h4]
    simp
  have hm : tr W (resU eV v' * w ^ q) = tr W (resU eV v') * (tr W w) ^ q := by
    simp [tr]
  rw [hrel, hm, ((GlobalTheory.T.kummerClassOfUnit_cocycle_natural_additive q).2.2 (tr W (resU eV v')) ((tr W w) ^ q) (qU q hq W)).1,
    ((GlobalTheory.T.kummerClassOfUnit_cocycle_natural_additive q).2.2 (tr W w) (tr W w) (qU q hq W)).2, add_zero]

private theorem isIso_ι (T : X.Opens) (hT : T = ⊤) : IsIso T.ι := by
  subst hT
  exact (inferInstance : IsIso (Scheme.topIso X).hom)

private theorem core (q : ℕ) [NeZero q] [IsIntegral X] (hP : Nonempty (Prim q Γ(X, ⊤))) (hq : IsUnit (q : Γ(X, ⊤)))
    (hn : ∀ y : X, IsIntegrallyClosed (X.presheaf.stalk y)) (F : (X.functionField)ˣ) (n : ℕ) (U : Fin n → X.Opens)
    [∀ i, Nonempty (U i)] (hU : ⨆ i, U i = ⊤) (v : ∀ i, (Γ(X, U i))ˣ) (h : Fin n → (X.functionField)ˣ)
    (hF : ∀ i, (F : X.functionField) = X.germToFunctionField (U i) (v i : Γ(X, U i)) * (h i : X.functionField) ^ q) :
    ∃ x : Ht q (sch.obj X) 1 1, pl q 1 (X.fromSpecStalk (genericPoint X)) 1 x =
      kum q (X := Spec X.functionField) (Units.map (Scheme.ΓSpecIso X.functionField).inv.hom.toMonoidHom F) := by
  have hW : ∀ i j, Nonempty (U i ⊓ U j : X.Opens) := fun i j => by
    obtain ⟨⟨a, ha⟩⟩ := ‹∀ i, Nonempty (U i)› i
    obtain ⟨⟨b, hb⟩⟩ := ‹∀ i, Nonempty (U i)› j
    obtain ⟨y, hy⟩ : ((U i : Set X) ∩ U j).Nonempty :=
      nonempty_preirreducible_inter (U i).isOpen (U j).isOpen ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨⟨y, hy⟩⟩
  obtain ⟨y, hy⟩ := UpperTheory.exists_h1Mu_glue_of_compatible q X hP hq n U (fun i => kum q (tr (U i) (v i))) (fun i j => by
    have := hW i j
    exact agree q hq hn F inf_le_left inf_le_right (v i) (v j) (h i) (h j) (hF i) (hF j))
  have hξ : genericPoint X ∈ (⨆ i, U i : X.Opens) := by
    rw [hU]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hξ
  have := isIso_ι (⨆ i, U i) hU
  have hcomp : X.fromSpecStalk (genericPoint X) ≫ inv (⨆ i, U i : X.Opens).ι =
      (U i).fromSpecStalkOfMem _ hi ≫ X.homOfLE (le_iSup U i) := by
    rw [← cancel_mono (⨆ i, U i : X.Opens).ι, Category.assoc, Category.assoc, IsIso.inv_hom_id, Category.comp_id,
      Scheme.homOfLE_ι, Scheme.Opens.fromSpecStalkOfMem_ι]
  refine ⟨pl q 1 (inv (⨆ i, U i : X.Opens).ι) 1 y, ?_⟩
  rw [← pl_comp, hcomp, pl_comp, hy i]
  have hqS : IsUnit (q : Γ(Spec X.functionField, ⊤)) := by
    simpa using hq.map (X.fromSpecStalk (genericPoint X)).appTop.hom
  have h1 := (GlobalTheory.T.kummerClassOfUnit_cocycle_natural_additive q).2.1 ((U i).fromSpecStalkOfMem _ hi) (tr (U i) (v i)) (qU q hq _)
  have h2 : Units.map (Scheme.ΓSpecIso X.functionField).inv.hom.toMonoidHom F =
      Units.map ((U i).fromSpecStalkOfMem _ hi).appTop.hom.toMonoidHom (tr (U i) (v i)) *
        (Units.map (Scheme.ΓSpecIso X.functionField).inv.hom.toMonoidHom (h i)) ^ q := by
    ext
    have h3 := rho_generic (U i) _ hi (v i : Γ(X, U i))
    have h4 := congrArg (Scheme.ΓSpecIso X.functionField).inv.hom (hF i)
    rw [map_mul, map_pow] at h4
    exact h4.trans (congrArg (· * _) h3.symm)
  refine h1.trans ?_
  have hb := ((GlobalTheory.T.kummerClassOfUnit_cocycle_natural_additive q).2.2 (Units.map (Scheme.ΓSpecIso X.functionField).inv.hom.toMonoidHom (h i))
    (Units.map (Scheme.ΓSpecIso X.functionField).inv.hom.toMonoidHom (h i)) hqS).2
  rw [h2, ((GlobalTheory.T.kummerClassOfUnit_cocycle_natural_additive q).2.2 _ _ hqS).1, hb, add_zero]

end UpperTheory.PicGlue

theorem UpperTheory.exists_h1Mu_of_locally_unit_times_power :
    ∀ (q : ℕ) [NeZero q] (X : Scheme.{0}) [IsIntegral X], Nonempty (Prim q Γ(X, ⊤)) → IsUnit (q : Γ(X, ⊤)) → CompactSpace X → (∀ y : X, IsIntegrallyClosed (X.presheaf.stalk y)) → ∀ F : (X.functionField)ˣ, (∀ y : X, ∃ (u : (X.presheaf.stalk y)ˣ) (h : (X.functionField)ˣ), (F : X.functionField) = algebraMap (X.presheaf.stalk y) X.functionField u * (h : X.functionField) ^ q) → ∃ x : Ht q (sch.obj X) 1 1, pl q 1 (X.fromSpecStalk (genericPoint X)) 1 x = kum q (X := Spec X.functionField) (Units.map (Scheme.ΓSpecIso X.functionField).inv.hom.toMonoidHom F) := by
  intro q _ X _ hP hq hc hn F hF
  choose u h hu using hF
  choose W hy v hv using fun y => UpperTheory.PicGlue.spread y (u y)
  obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover (fun y => (W y : Set X))
    (fun y _ => (W y).isOpen.mem_nhds (hy y))
  let idx : Fin t.card → X := fun i => (t.equivFin.symm i).1
  have : ∀ i, Nonempty (W (idx i)) := fun i => ⟨⟨_, hy _⟩⟩
  refine UpperTheory.PicGlue.core q hP hq hn F t.card (fun i => W (idx i)) ?_ (fun i => v (idx i)) (fun i => h (idx i)) (fun i => ?_)
  · rw [eq_top_iff]
    intro y _
    obtain ⟨z, hz, hyz⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨t.equivFin ⟨z, hz⟩, by simpa [idx] using hyz⟩
  · rw [hu (idx i), ← hv (idx i), Scheme.algebraMap_germ_eq_germToFunctionField X (hy (idx i))]
end

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

namespace UpperTheory.PicRigid

private lemma exists_prim (q : ℕ) [NeZero q] (L : Type) [Field L] [IsAlgClosed L] (hq : IsUnit (q : L)) :
    Nonempty (Prim q L) := by
  have hdeg : (Polynomial.cyclotomic q L).degree ≠ 0 := by
    rw [Polynomial.degree_cyclotomic]
    have := Nat.totient_pos.mpr (NeZero.pos q)
    exact_mod_cast this.ne'
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root _ hdeg
  refine ⟨⟨z, hq, ?_⟩⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
  exact hz

private lemma pl_id (q : ℕ) (i : ℤ) {X : Scheme.{0}} (m : ℤ) (y : Ht q (sch.obj X) m i) :
    pl q i (𝟙 X) m y = y := by
  show pull (ZMod q) (sch.map (𝟙 X)) (tw q i) m y = y
  rw [CategoryTheory.Functor.map_id, pull_id]

private lemma main (hA : LateralTheory.KummerTheory.AlgExt) : Hyps → ∀ (q : ℕ) [NeZero q] (k L : Type) [Field k] [IsAlgClosed k] [Field L] [IsAlgClosed L] [Algebra k L], IsUnit (q : k) → ∀ {C : Scheme.{0}} [IsIntegral C] (c : C ⟶ Sp k), IsCurve c → ∀ {X : Scheme.{0}} [IsIntegral X] (u : X ⟶ C) (x : X ⟶ Sp L), IsPullback u x c (Spec.map (CommRingCat.ofHom (algebraMap k L))) → (∀ y : X, IsIntegrallyClosed (X.presheaf.stalk y)) → ∀ φ : C.functionField →+* X.functionField, Spec.map (CommRingCat.ofHom φ) ≫ (C.fromSpecStalk (genericPoint C)) = (X.fromSpecStalk (genericPoint X)) ≫ u → ∀ F : (X.functionField)ˣ, (∀ y : X, ∃ (u : (X.presheaf.stalk y)ˣ) (h : (X.functionField)ˣ), (F : X.functionField) = algebraMap (X.presheaf.stalk y) X.functionField u * (h : X.functionField) ^ q) → ∃ (f : (C.functionField)ˣ) (h : (X.functionField)ˣ), (F : X.functionField) = φ f * (h : X.functionField) ^ q := by
  intro hy q _ k L _ _ _ _ _ hq C _ c hc X _ u x pb hnorm φ hφ F hF
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, e2, e3⟩ := hy
  have hP : IsProper c := hc.2.1
  have hS1 : SmoothOfRelativeDimension 1 c := hc.2.2
  have hS : Smooth c := SmoothOfRelativeDimension.smooth 1 c
  have hqL : IsUnit (q : L) := by simpa using hq.map (algebraMap k L)
  have hxP : IsProper x := MorphismProperty.of_isPullback (P := @IsProper) pb hP
  have hcpt : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace x
  let ρ : L →+* Γ(X, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫ x.appTop).hom
  have hqX : IsUnit (q : Γ(X, ⊤)) := by simpa using hqL.map ρ
  obtain ⟨ζ⟩ := exists_prim q L hqL
  obtain ⟨xx, hxx⟩ := UpperTheory.exists_h1Mu_of_locally_unit_times_power q X ⟨Prim.map ρ ζ⟩ hqX hcpt hnorm F hF
  have E := hA e2 e3 q k L (algebraMap k L) hq c 1
  obtain ⟨x₀, hx₀⟩ := (E 1).2 (pl q 1 pb.isoPullback.inv 1 xx)
  have hu : pl q 1 u 1 x₀ = xx := by
    rw [← pb.isoPullback_hom_fst, pl_comp]
    have h1 : pl q 1 (pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap k L)))) 1 x₀ =
      pl q 1 pb.isoPullback.inv 1 xx := hx₀
    rw [h1, ← pl_comp, Iso.hom_inv_id, pl_id]

  let gC := C.fromSpecStalk (genericPoint C)
  let hk : k →+* C.functionField := (Spec.preimage (gC ≫ c)).hom
  have hqA : IsUnit (q : C.functionField) := by simpa using hq.map hk
  have hqK : IsUnit (q : X.functionField) := by
    simpa using hqA.map φ
  have hqS : IsUnit (q : Γ(Spec C.functionField, ⊤)) := by
    simpa using hqA.map (Scheme.ΓSpecIso C.functionField).inv.hom
  have hqT : IsUnit (q : Γ(Spec X.functionField, ⊤)) := by
    simpa using hqK.map (Scheme.ΓSpecIso X.functionField).inv.hom
  obtain ⟨w, hw⟩ := UpperTheory.Cb.exists_unit_kummer_eq_of_picard_torsionFree q C.functionField hqA (fun c _ => Subsingleton.elim _ _) (pl q 1 gC 1 x₀)
  have K1 := (GlobalTheory.T.kummerClassOfUnit_cocycle_natural_additive q).2.1 (Spec.map (CommRingCat.ofHom φ)) w hqS
  have K2 : kum q (X := Spec X.functionField) (Units.map (Scheme.ΓSpecIso X.functionField).inv.hom.toMonoidHom F) =
      kum q (Units.map (Spec.map (CommRingCat.ofHom φ)).appTop.hom.toMonoidHom w) := by
    rw [← hxx, ← hu, ← pl_comp, ← hφ, pl_comp]
    have h2 : pl q 1 (C.fromSpecStalk (genericPoint C)) 1 x₀ = kum q w := hw.symm
    rw [h2]
    exact K1
  let iX : (X.functionField)ˣ →* (Γ(Spec X.functionField, ⊤))ˣ :=
    Units.map (Scheme.ΓSpecIso X.functionField).inv.hom.toMonoidHom
  let fK : (C.functionField)ˣ := Units.map (Scheme.ΓSpecIso C.functionField).hom.hom.toMonoidHom w
  let φu : (X.functionField)ˣ := Units.map φ.toMonoidHom fK
  have K3 : Units.map (Spec.map (CommRingCat.ofHom φ)).appTop.hom.toMonoidHom w = iX φu := by
    apply Units.ext
    have e : (Scheme.ΓSpecIso C.functionField).inv.hom
        ((Scheme.ΓSpecIso C.functionField).hom.hom (w : Γ(Spec C.functionField, ⊤))) = (w : Γ(Spec C.functionField, ⊤)) :=
      congrArg (fun m => m.hom (w : Γ(Spec C.functionField, ⊤))) (Scheme.ΓSpecIso C.functionField).hom_inv_id
    have h3 : (Scheme.ΓSpecIso X.functionField).inv.hom (φ ((fK : (C.functionField)ˣ) : C.functionField)) =
        (Spec.map (CommRingCat.ofHom φ)).appTop.hom ((Scheme.ΓSpecIso C.functionField).inv.hom
          ((Scheme.ΓSpecIso C.functionField).hom.hom (w : Γ(Spec C.functionField, ⊤)))) :=
      congrArg (fun m => m.hom ((Scheme.ΓSpecIso C.functionField).hom.hom (w : Γ(Spec C.functionField, ⊤))))
        (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
    rw [e] at h3
    exact h3.symm
  have K4 : kum q (iX (F * φu⁻¹)) = 0 := by
    have h4 := ((GlobalTheory.T.kummerClassOfUnit_cocycle_natural_additive q).2.2 (iX (F * φu⁻¹)) (iX φu) hqT).1
    rw [← map_mul, inv_mul_cancel_right] at h4
    have h5 : kum q (iX F) = kum q (iX φu) := K2.trans (by rw [K3])
    rw [h5] at h4
    exact right_eq_add.mp h4
  obtain ⟨v, hv⟩ := UpperTheory.exists_root_of_kummer_class_eq_zero q (Spec X.functionField) (iX (F * φu⁻¹)) hqT K4
  let h : (X.functionField)ˣ := Units.map (Scheme.ΓSpecIso X.functionField).hom.hom.toMonoidHom v
  have hh : h ^ q = F * φu⁻¹ := by
    have e1 : h ^ q = Units.map (Scheme.ΓSpecIso X.functionField).hom.hom.toMonoidHom (v ^ q) := (map_pow _ v q).symm
    rw [e1, hv]
    apply Units.ext
    exact congrArg (fun m => m.hom (((F * φu⁻¹ : (X.functionField)ˣ)) : X.functionField))
      (Scheme.ΓSpecIso X.functionField).inv_hom_id
  refine ⟨fK, h, ?_⟩
  have h6 : F = φu * h ^ q := by rw [hh, mul_comm F, mul_inv_cancel_left]
  have h7 := congrArg Units.val h6
  rw [Units.val_mul, Units.val_pow_eq_pow_val] at h7
  exact h7

end UpperTheory.PicRigid

theorem UpperTheory.baseChange_curve_functionField_comp_of_normal :
    Hyps → ∀ (q : ℕ) [NeZero q] (k L : Type) [Field k] [IsAlgClosed k] [Field L] [IsAlgClosed L] [Algebra k L], IsUnit (q : k) → ∀ {C : Scheme.{0}} [IsIntegral C] (c : C ⟶ Sp k), IsCurve c → ∀ {X : Scheme.{0}} [IsIntegral X] (u : X ⟶ C) (x : X ⟶ Sp L), IsPullback u x c (Spec.map (CommRingCat.ofHom (algebraMap k L))) → (∀ y : X, IsIntegrallyClosed (X.presheaf.stalk y)) → ∀ φ : C.functionField →+* X.functionField, Spec.map (CommRingCat.ofHom φ) ≫ (C.fromSpecStalk (genericPoint C)) = (X.fromSpecStalk (genericPoint X)) ≫ u → ∀ F : (X.functionField)ˣ, (∀ y : X, ∃ (u : (X.presheaf.stalk y)ˣ) (h : (X.functionField)ˣ), (F : X.functionField) = algebraMap (X.presheaf.stalk y) X.functionField u * (h : X.functionField) ^ q) → ∃ (f : (C.functionField)ˣ) (h : (X.functionField)ˣ), (F : X.functionField) = φ f * (h : X.functionField) ^ q :=
  UpperTheory.PicRigid.main LateralTheory.Fin.AlgExt.intersectionNumber_baseChange
