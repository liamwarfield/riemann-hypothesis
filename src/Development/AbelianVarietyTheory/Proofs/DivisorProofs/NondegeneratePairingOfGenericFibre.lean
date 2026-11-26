module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDualOfIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheaf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechPicardGlueFiniteDisjointCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPointOfSize

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NondegeneratePairingOfGenericFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NondegeneratePairingOfGenericFibre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.NondegSpread
open GlobalTheory.CechPic

theorem pairing_add_and_symm : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
    ∀ (P : LB (A ⊗ A).left) (hP : P.IsLB),
    (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) →
    (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) →
    LBIso P (P.pull (lift (snd A A) (fst A A)).left) →
    Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) →
    (∀ (T : Over S) (x x' y : T ⟶ A), CechPic.pull (lift (x * x') y).left (CechPic.cls P hP) = CechPic.pull (lift x y).left (CechPic.cls P hP) + CechPic.pull (lift x' y).left (CechPic.cls P hP)) ∧
    (∀ (T : Over S) (x y : T ⟶ A), CechPic.pull (lift x y).left (CechPic.cls P hP) = CechPic.pull (lift y x).left (CechPic.cls P hP)) := by
  intro S A _ _ hA P hP r₁ r₂ hs ha
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hD : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  refine ⟨fun T x x' y => ?_, fun T x y => ?_⟩
  · obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S A _ hA hD ha P hP r₁ r₂ T x x' y).1
    have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 ⟨t, ht⟩
    rw [cls_linComb hP, Fin.sum_univ_three] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, one_smul, neg_smul] at e
    rw [← sub_eq_zero, ← e]
    abel
  · have e := (cls_eq_iff hP (pull_isLB hP _)).2 hs
    rw [cls_pull hP] at e
    conv_lhs => rw [e]
    rw [← pull_comp, ← Over.comp_left, comp_lift, lift_fst, lift_snd]

theorem over_hom_ext_of_local : ∀ (S : Scheme.{0}) (T X : Over S) (a b : T ⟶ X),
    (∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧ Out.overResι V ≫ a = Out.overResι V ≫ b) → a = b := by
  intro S T X a b h
  choose V hV e using h
  apply Over.OverMorphism.ext
  exact Scheme.hom_ext_of_forall _ _ fun p => ⟨V p, hV p, congrArg (fun q => q.left) (e p)⟩

theorem hom_ext_of_generic_points : ∀ (O K : Type) [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K] (H X : Over (Sp O))
    [IsSeparated X.hom] (a b : H ⟶ X), IsFinite H.hom → Flat H.hom →
    (∀ (T : Over (Sp O)) (t : T.left ⟶ Sp K), T.hom = t ≫ spMap (algebraMap O K) → ∀ z : T ⟶ H, z ≫ a = z ≫ b) → a = b := by
  intro O K _ _ _ _ _ H X _ a b hfin hflat h
  have := GlobalTheory.schemeTheoreticallyDominant_fractionField O K
  have : IsSchemeTheoreticallyDominant (pullback.fst H.hom (spMap (algebraMap O K))) :=
    .of_isPullback (IsPullback.of_hasPullback H.hom (spMap (algebraMap O K))).flip
  let T : Over (Sp O) := Over.mk (pullback.fst H.hom (spMap (algebraMap O K)) ≫ H.hom)
  let z : T ⟶ H := Over.homMk (pullback.fst _ _) rfl
  refine GlobalTheory.over_ext_of_schemeTheoreticallyDominant (pullback.fst H.hom (spMap (algebraMap O K))) ?_
  exact congrArg (fun q => q.left) (h T (pullback.snd _ _) pullback.condition z)

theorem cls_translDiff : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (P : LB (A ⊗ A).left) (hP : P.IsLB),
    (∀ (T : Over S) (x x' y : T ⟶ A), CechPic.pull (lift (x * x') y).left (CechPic.cls P hP) = CechPic.pull (lift x y).left (CechPic.cls P hP) + CechPic.pull (lift x' y).left (CechPic.cls P hP)) →
    (∀ (T : Over S) (x y : T ⟶ A), CechPic.pull (lift x y).left (CechPic.cls P hP) = CechPic.pull (lift y x).left (CechPic.cls P hP)) →
    ∀ (T : Over S) (x : T ⟶ A) (h : (Out.translDiff A (P.pull (lift (𝟙 A) (𝟙 A)).left) x).IsLB),
    CechPic.cls _ h = CechPic.pull (fst T A).left (CechPic.pull (lift x x).left (CechPic.cls P hP)) + CechPic.pull (lift (fst T A ≫ x ^ 2) (snd T A)).left (CechPic.cls P hP) := by
  intro S A _ P hP hB hS T x h
  have hD : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  have dg : ∀ g : T ⊗ A ⟶ A, CechPic.pull g.left (CechPic.cls _ hD) =
      CechPic.pull (lift g g).left (CechPic.cls P hP) := fun g => by
    rw [cls_pull hP, ← pull_comp, ← Over.comp_left, comp_lift, Category.comp_id]
  have hm : lift (fst T A ≫ x) (snd T A) ≫ μ[A] = (fst T A ≫ x) * snd T A := rfl
  refine (cls_linComb hD (![(lift (fst T A ≫ x) (snd T A) ≫ μ[A]).left, (snd T A).left] : Fin 2 → _) ![1, -1] h).trans ?_
  rw [Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, one_smul, neg_smul]
  rw [hm, dg, dg, hB, hS _ (fst T A ≫ x) (_ * _), hS _ (snd T A) (_ * _), hB, hB, ← pull_comp,
    ← Over.comp_left, comp_lift, MonObj.comp_pow, pow_two, hB, hS _ (snd T A) (fst T A ≫ x)]
  abel

theorem memKL_of_pairing_sq : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (P : LB (A ⊗ A).left) (hP : P.IsLB),
    (∀ (T : Over S) (x x' y : T ⟶ A), CechPic.pull (lift (x * x') y).left (CechPic.cls P hP) = CechPic.pull (lift x y).left (CechPic.cls P hP) + CechPic.pull (lift x' y).left (CechPic.cls P hP)) →
    (∀ (T : Over S) (x y : T ⟶ A), CechPic.pull (lift x y).left (CechPic.cls P hP) = CechPic.pull (lift y x).left (CechPic.cls P hP)) →
    ∀ (T : Over S) (x : T ⟶ A), CechPic.pull (lift (fst T A ≫ x ^ 2) (snd T A)).left (CechPic.cls P hP) = 0 →
    MemKL A (P.pull (lift (𝟙 A) (𝟙 A)).left) x := by
  intro S A _ P hP hB hS T x h0 p
  have hD := pull_isLB hP (lift (𝟙 A) (𝟙 A)).left
  have hM : (Out.translDiff A (P.pull (lift (𝟙 A) (𝟙 A)).left) x).IsLB := LB.isLB_linComb hD _ _
  have e := cls_translDiff S A P hP hB hS T x hM
  rw [h0, add_zero] at e
  obtain ⟨N, hN, hc⟩ := cls_surj (CechPic.pull (lift x x).left (CechPic.cls P hP))
  have e' : cls (N.pull (fst T A).left) (pull_isLB hN _) = cls _ hM := by rw [cls_pull hN, hc, e]
  obtain ⟨u, hu⟩ := (cls_eq_iff _ _).1 e'
  exact GlobalTheory.CubeLawCompare.locally_trivial_of_iso_pull (fst T A).left _ hN u hu p

theorem exists_local_triv_sq_of_memKL : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (P : LB (A ⊗ A).left) (hP : P.IsLB),
    (∀ (T : Over S) (x x' y : T ⟶ A), CechPic.pull (lift (x * x') y).left (CechPic.cls P hP) = CechPic.pull (lift x y).left (CechPic.cls P hP) + CechPic.pull (lift x' y).left (CechPic.cls P hP)) →
    (∀ (T : Over S) (x y : T ⟶ A), CechPic.pull (lift x y).left (CechPic.cls P hP) = CechPic.pull (lift y x).left (CechPic.cls P hP)) →
    (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) →
    ∀ (T : Over S) (x : T ⟶ A), MemKL A (P.pull (lift (𝟙 A) (𝟙 A)).left) x → ∀ p : T.left,
    ∃ V : T.left.Opens, p ∈ V ∧ ∃ t : (P.pull (lift (snd A (Out.overRes V) ≫ Out.overResι V ≫ x ^ 2) (fst A (Out.overRes V))).left).Gen, t.IsGen := by
  intro S A _ P hP hB hS r₂ T x hx p
  obtain ⟨V, hV, c, hc⟩ := hx p
  refine ⟨V, hV, ?_⟩
  have hD := pull_isLB hP (lift (𝟙 A) (𝟙 A)).left
  have hM : (Out.translDiff A (P.pull (lift (𝟙 A) (𝟙 A)).left) x).IsLB := LB.isLB_linComb hD _ _
  have nat : ∀ {Y Z : Over S} (g : Y ⟶ Z) (a b : Z ⟶ A), CechPic.pull g.left (CechPic.pull (lift a b).left (CechPic.cls P hP)) = CechPic.pull (lift (g ≫ a) (g ≫ b)).left (CechPic.cls P hP) :=
    fun g a b => by rw [← pull_comp, ← Over.comp_left, comp_lift]
  have ax : ∀ {Y : Over S} (a : Y ⟶ A), CechPic.pull (lift a (1 : Y ⟶ A)).left (CechPic.cls P hP) = 0 := fun a => by
    have e := (cls_eq_zero_iff (pull_isLB hP _)).2 r₂
    rw [cls_pull hP] at e
    have e' := congrArg (CechPic.pull a.left) e
    rwa [map_zero, ← pull_comp, ← Over.comp_left, comp_lift, MonObj.comp_one, Category.comp_id] at e'
  let Vo := Out.overRes V
  let u : Vo ⟶ T := Out.overResι V
  let W := (fst T A).left ⁻¹ᵁ V
  let U : Vo ⊗ A ⟶ T ⊗ A := lift (fst Vo A ≫ u) (snd Vo A)
  have k₁ : U ≫ fst T A = fst Vo A ≫ u := lift_fst _ _
  have k₂ : U ≫ snd T A = snd Vo A := lift_snd _ _
  obtain ⟨n, hn⟩ : ∃ n : (Vo ⊗ A).left ⟶ W.toScheme, n ≫ W.ι = U.left :=
    ⟨IsOpenImmersion.lift _ U.left (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      show (U ≫ fst T A).left y ∈ V
      rw [k₁]
      show V.ι ((fst Vo A).left y) ∈ V
      have hy := Set.mem_range_self (f := V.ι) ((fst Vo A).left y)
      rwa [Scheme.Opens.range_ι] at hy), IsOpenImmersion.lift_fac _ _ _⟩
  have e0 := (cls_eq_zero_iff (pull_isLB hM _)).2 ⟨c, hc⟩
  rw [cls_pull hM, cls_translDiff S A P hP hB hS T x hM] at e0
  have e1 := congrArg (CechPic.pull n) e0
  rw [map_zero, ← pull_comp, hn, map_add (f := _), ← pull_comp, ← Over.comp_left, nat, nat] at e1
  simp only [← Category.assoc, k₁, k₂] at e1
  simp only [Category.assoc] at e1
  have e2 := congrArg (CechPic.pull (lift (𝟙 Vo) (1 : Vo ⟶ A)).left) e1
  rw [map_zero, map_add (f := _), nat, nat, lift_fst_assoc, lift_snd, Category.id_comp, ax, add_zero] at e2
  have e3 : CechPic.pull (fst Vo A).left (CechPic.pull (lift (u ≫ x) (u ≫ x)).left (CechPic.cls P hP)) = 0 := by rw [e2, map_zero]
  rw [nat] at e3
  rw [e3, zero_add] at e1
  have e4 := congrArg (CechPic.pull (lift (snd A Vo) (fst A Vo)).left) e1
  rw [map_zero, nat, lift_fst_assoc, lift_snd] at e4
  refine (cls_eq_zero_iff (pull_isLB hP _)).1 ?_
  rw [cls_pull hP]
  exact e4

theorem eq_one_of_generic_nondeg : ∀ (O K : Type) [CommRing O] [Field K] [Algebra O K] (A : Over (Sp O)) [GrpObj A] (A' : Over (Sp K)) [GrpObj A']
    (φ : A'.left ⟶ A.left) (φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left),
    IsGrpPullback A' A (spMap (algebraMap O K)) φ → IsSquare φ φ₂ → ∀ (P : LB (A ⊗ A).left) (P' : LB (A' ⊗ A').left),
    P.IsLB → P'.IsLB → LBIso P' (P.pull φ₂) → (∀ (T : Over (Sp K)) (x : T ⟶ A'), (∃ t : (P'.pull (lift (snd A' T ≫ x) (fst A' T)).left).Gen, t.IsGen) → x = 1) →
    ∀ (T : Over (Sp O)) (t : T.left ⟶ Sp K), T.hom = t ≫ spMap (algebraMap O K) → ∀ x : T ⟶ A,
    (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x = 1 := by
  intro O K _ _ _ A _ A' _ φ φ₂ h sq P P' hP hP' H gen T t ht x hx
  obtain ⟨T, ⟨⟨⟩⟩, hT⟩ := T
  change T ⟶ Sp K at t
  change T ⟶ Sp O at hT
  change hT = t ≫ _ at ht
  subst ht
  let T' : Over (Sp K) := Over.mk t
  obtain ⟨x', rfl⟩ := GlobalTheory.SiegelPull.push_surjective h T' x
  rw [← map_one (pushHom h T')]
  congr 1
  apply gen T' x'
  obtain ⟨u, hu⟩ := H
  obtain ⟨c, hc⟩ := hx
  let f := spMap (algebraMap O K)
  let B : Over (Sp O) := Over.mk ((A' ⊗ T').hom ≫ f)
  let a : B ⟶ A := Over.homMk ((fst A' T').left ≫ φ) (by
    show (fst A' T').left ≫ φ ≫ A.hom = (A' ⊗ T').hom ≫ f
    rw [h.1.w, ← Category.assoc, Over.w (fst A' T')])
  let b : B ⟶ Over.mk (t ≫ f) := Over.homMk (snd A' T').left (by
    show (snd A' T').left ≫ t ≫ f = (A' ⊗ T').hom ≫ f
    rw [← Category.assoc]
    exact congrArg (· ≫ f) (Over.w (snd A' T')))
  let χ : (A' ⊗ T').left ⟶ (A ⊗ Over.mk (t ≫ f)).left := (lift a b).left
  have c₁ : χ ≫ (fst A (Over.mk (t ≫ f))).left = (fst A' T').left ≫ φ :=
    congrArg (fun q => q.left) (lift_fst a b)
  have c₂ : χ ≫ (snd A (Over.mk (t ≫ f))).left = (snd A' T').left :=
    congrArg (fun q => q.left) (lift_snd a b)
  have sqr : (lift (snd A' T' ≫ x') (fst A' T')).left ≫ φ₂ =
      χ ≫ (lift (snd A (Over.mk (t ≫ f)) ≫ pushHom h T' x') (fst A (Over.mk (t ≫ f)))).left :=
    (Category.id_comp _).symm.trans (GlobalTheory.SiegelPull.lift_sq sq (T := B) (𝟙 _) _ _ χ _ _
      (by rw [Category.id_comp, Over.comp_left, Over.comp_left, ← Category.assoc χ, c₂, Category.assoc]; rfl)
      (by rw [Category.id_comp, c₁]))
  obtain ⟨c₂', h₂⟩ := gen_chartPull (chartPullSame P (fun _ : PUnit => (lift (snd A' T' ≫ x') (fst A' T')).left ≫ φ₂)
    _ _ χ fun _ => sqr) c hc
  exact exists_down ((isGen_iff u).1 hu) hP hP' c₂' h₂

theorem sq_eq_one_of_memKL_generic : ∀ (O K : Type) [CommRing O] [Field K] [Algebra O K] (A : Over (Sp O)) [GrpObj A] (A' : Over (Sp K)) [GrpObj A']
    (φ : A'.left ⟶ A.left) (φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left),
    IsGrpPullback A' A (spMap (algebraMap O K)) φ → IsSquare φ φ₂ → ∀ (P : LB (A ⊗ A).left) (P' : LB (A' ⊗ A').left)
    (hP : P.IsLB), P'.IsLB → LBIso P' (P.pull φ₂) →
    (∀ (T : Over (Sp O)) (x x' y : T ⟶ A), CechPic.pull (lift (x * x') y).left (CechPic.cls P hP) = CechPic.pull (lift x y).left (CechPic.cls P hP) + CechPic.pull (lift x' y).left (CechPic.cls P hP)) →
    (∀ (T : Over (Sp O)) (x y : T ⟶ A), CechPic.pull (lift x y).left (CechPic.cls P hP) = CechPic.pull (lift y x).left (CechPic.cls P hP)) →
    (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → (∀ (T : Over (Sp K)) (x : T ⟶ A'), (∃ t : (P'.pull (lift (snd A' T ≫ x) (fst A' T)).left).Gen, t.IsGen) → x = 1) →
    ∀ (T : Over (Sp O)) (t : T.left ⟶ Sp K), T.hom = t ≫ spMap (algebraMap O K) → ∀ x : T ⟶ A,
    MemKL A (P.pull (lift (𝟙 A) (𝟙 A)).left) x → x ^ 2 = 1 := by
  intro O K _ _ _ A _ A' _ φ φ₂ h sq P P' hP hP' H hB hS r₂ gen T t ht x hx
  refine over_hom_ext_of_local _ T A (x ^ 2) 1 fun p => ?_
  obtain ⟨V, hV, hg⟩ := exists_local_triv_sq_of_memKL _ A P hP hB hS r₂ T x hx p
  refine ⟨V, hV, ?_⟩
  rw [MonObj.comp_one]
  exact eq_one_of_generic_nondeg O K A A' φ φ₂ h sq P P' hP hP' H gen (Out.overRes V) (V.ι ≫ t)
    (by simp only [Out.overRes, Over.mk_hom, ht, Category.assoc]) _ hg

theorem nondeg_of_generic : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] [Field K] [Algebra O K] [IsFractionRing O K] (A : Over (Sp O)) [GrpObj A] (A' : Over (Sp K)) [GrpObj A'] (φ : A'.left ⟶ A.left) (φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left), IsAbelianScheme A → IsGrpPullback A' A (spMap (algebraMap O K)) φ → IsSquare φ φ₂ → ∀ (P : LB (A ⊗ A).left) (P' : LB (A' ⊗ A').left), P.IsLB → P'.IsLB → LBIso P' (P.pull φ₂) → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → (∀ (T : Over (Sp K)) (x : T ⟶ A'), (∃ t : (P'.pull (lift (snd A' T ≫ x) (fst A' T)).left).Gen, t.IsGen) → x = 1) → ∀ (T : Over (Sp O)) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x = 1 := by
  intro O K _ _ _ _ _ _ A _ A' _ φ φ₂ hA h sq P P' hP hP' H r₁ r₂ hs ha gen T y hy
  haveI := hA.comm
  haveI := hA.proper
  have hL : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  obtain ⟨hB, hS⟩ := pairing_add_and_symm _ A hA P hP r₁ r₂ hs ha
  obtain ⟨H₀, _, i, -, -, hfin, hflat, hZ⟩ := GlobalTheory.kernel_finiteFlat_subgroup O A hA _ hL ha
  have hi : i ^ 2 = 1 := by
    refine hom_ext_of_generic_points O K H₀ A (i ^ 2) 1 hfin hflat fun T t ht z => ?_
    rw [MonObj.comp_pow, MonObj.comp_one]
    exact sq_eq_one_of_memKL_generic O K A A' φ φ₂ h sq P P' hP hP' H hB hS r₂ gen T t ht (z ≫ i) ((hZ T _).2 ⟨z, rfl⟩)
  obtain ⟨-, hfl, hsu⟩ := GlobalTheory.MulAmple.finite_flat_surjective_pow GlobalTheory.abelianSchemeLaws_all.1 O A hA _ hL ha 2
    (by norm_num)
  obtain ⟨T', e, x, he, he', hx⟩ := GlobalTheory.DivisibleHom.exists_lift_point ((𝟙 A) ^ 2) y
  have hx2 : x ^ 2 = e ≫ y := by rw [← hx, MonObj.comp_pow, Category.comp_id]
  have hmem : MemKL A _ x := memKL_of_pairing_sq _ A P hP hB hS T' x (by
    obtain ⟨t, ht⟩ := hy
    have e0 := (cls_eq_zero_iff (pull_isLB hP _)).2 ⟨t, ht⟩
    rw [cls_pull hP] at e0
    have e1 := congrArg (CechPic.pull (lift (snd T' A) (fst T' A ≫ e)).left) e0
    rw [map_zero, ← pull_comp, ← Over.comp_left, comp_lift, lift_snd_assoc, lift_fst] at e1
    rw [hx2]
    exact e1)
  obtain ⟨w, hw⟩ := (hZ T' x).1 hmem
  apply GlobalTheory.DivisibleHom.cancel_of_flat_surjective e
  rw [← hx2, ← hw, ← MonObj.comp_pow, hi, MonObj.comp_one, MonObj.comp_one]

end GlobalTheory.NondegSpread
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NondegeneratePairingOfGenericFibreStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nondegenerate_pairing_of_generic_fibre : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] [Field K] [Algebra O K] [IsFractionRing O K] (A : Over (Sp O)) [GrpObj A] (A' : Over (Sp K)) [GrpObj A'] (φ : A'.left ⟶ A.left) (φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left), IsAbelianScheme A → IsGrpPullback A' A (spMap (algebraMap O K)) φ → IsSquare φ φ₂ → ∀ (P : LB (A ⊗ A).left) (P' : LB (A' ⊗ A').left), P.IsLB → P'.IsLB → LBIso P' (P.pull φ₂) → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → (∀ (T : Over (Sp K)) (x : T ⟶ A'), (∃ t : (P'.pull (lift (snd A' T ≫ x) (fst A' T)).left).Gen, t.IsGen) → x = 1) → ∀ (T : Over (Sp O)) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x = 1 := by
  first | exact @GlobalTheory.NondegSpread.nondeg_of_generic | exact GlobalTheory.NondegSpread.nondeg_of_generic | (intros; apply GlobalTheory.NondegSpread.nondeg_of_generic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymplecticLevelOfPulledBackObject
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymplecticLevelOfPulledBackObject
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover

namespace GlobalTheory.HTSympCover

theorem isSympLev_of_sympCond_pull : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ)
  (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (T : Over S) (t₁ : T.left ⟶ Sp (cycAway M))
  (o' : Obj b N (T.hom ≫ t)) (m : ObjMap o' o T.hom)
  (lv' : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over T.left) ⟶ o'.A)) (lv : (Fin h ⊕ Fin h → ℤ) → (T ⟶ o.A)),
    (∀ a, (lv' a).left ≫ m.φ = (lv a).left) → SympCond o h M T t₁ lv →
      IsSympLev o'.P h M (zetaAway M) t₁ lv' := by
  intro p _ D R _ b N h M S t o T t₁ o' m lv' lv hα hlv
  obtain ⟨hadd, hkill, hgeo⟩ := hlv
  obtain ⟨ρ, eρ⟩ := GlobalTheory.HkSetPull.exists_equiv m.cart (𝟙_ (Over T.left))
  let j : Over.mk ((𝟙_ (Over T.left)).hom ≫ T.hom) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have key : ∀ a, ρ (lv' a) = j ≫ lv a := fun a => Over.OverMorphism.ext (by simp [eρ, hα, j])
  have dg := GlobalTheory.SiegelPull.diag_iso m.sq m.pol
  refine ⟨fun a c => ρ.injective ?_, fun a => ρ.injective ?_, fun k _ _ x β z hx hz => ?_⟩
  · rw [map_mul, key, key, key, hadd, MonObj.comp_mul]
  · rw [map_pow, key, ← MonObj.comp_pow, hkill, MonObj.comp_one, map_one]
  obtain ⟨hker, honto, hw⟩ := hgeo k x β z hx hz
  obtain ⟨σ, eσ⟩ := GlobalTheory.HkSetPull.exists_equiv m.cart (Over.mk x)
  have key' : ∀ a, σ (toUnit (Over.mk x) ≫ lv' a) = (Over.homMk x rfl : Over.mk (x ≫ T.hom) ⟶ T) ≫ lv a :=
    fun a => Over.OverMorphism.ext (by
      rw [eσ, Over.comp_left, Category.assoc, hα, Over.comp_left]
      congr 1)
  refine ⟨fun a => ?_, fun g hg => ?_, fun a c => ?_⟩
  · rw [← hker a, ← key', map_eq_one_iff _ σ.injective]
  · obtain ⟨a, ha⟩ := honto (σ g) (by rw [← map_pow, hg, map_one])
    exact ⟨a, σ.injective (by rw [key', ha])⟩
  · exact (GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ o.A o'.A T.hom m.φ _ _ (pull_isLB o.isLB _)
      (pull_isLB o'.isLB _) m.cart dg (Over.mk x) M _ _ _ _ _ (eσ _) (eσ _)).2 (by rw [key', key']; exact hw a c)

end GlobalTheory.HTSympCover
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymplecticLevelOfPulledBackObjectStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSymplecticLevel_of_pulledBack_object : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ)
  (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (T : Over S) (t₁ : T.left ⟶ Sp (cycAway M))
  (o' : Obj b N (T.hom ≫ t)) (m : ObjMap o' o T.hom)
  (lv' : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over T.left) ⟶ o'.A)) (lv : (Fin h ⊕ Fin h → ℤ) → (T ⟶ o.A)),
    (∀ a, (lv' a).left ≫ m.φ = (lv a).left) → SympCond o h M T t₁ lv →
      IsSympLev o'.P h M (zetaAway M) t₁ lv' := by
  first | exact @GlobalTheory.HTSympCover.isSympLev_of_sympCond_pull | exact GlobalTheory.HTSympCover.isSympLev_of_sympCond_pull | (intros; apply GlobalTheory.HTSympCover.isSympLev_of_sympCond_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PinchedChartsRestrictMatchingOpens
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PinchedChartsRestrictMatchingOpens
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Pinch

theorem restrict_pinched : ∀ (g : ℕ) (S S' Z B' C Y : Scheme.{0}) (s' : S' ⟶ S) (z : Z ⟶ S) (b' : B' ⟶ S') (e : C ⟶ Z) (i : Y ⟶ B') (q : Y ⟶ C), IsPullback i (q ≫ e) (b' ≫ s') z → IsPullback q (i ≫ b') (e ≫ z) s' → ∀ (V' : B'.Opens) (V : C.Opens), i ⁻¹ᵁ V' = q ⁻¹ᵁ V → ∃ (q₀ : (i ⁻¹ᵁ V').toScheme ⟶ V.toScheme), IsPullback (i ∣_ V') (q₀ ≫ V.ι ≫ e) ((V'.ι ≫ b') ≫ s') z ∧ IsPullback q₀ ((i ∣_ V') ≫ V'.ι ≫ b') ((V.ι ≫ e) ≫ z) s' ∧ ∀ x : V'.toScheme, GlobalTheory.Pinch.Pinched g s' z (V'.ι ≫ b') (V.ι ≫ e) (i ∣_ V') q₀ x → GlobalTheory.Pinch.Pinched g s' z b' e i q (V'.ι x) := by
  intro g S S' Z B' C Y s' z b' e i q h₁ h₂ V' V hV
  refine ⟨(Y.isoOfEq hV).hom ≫ (q ∣_ V), ?_, ?_, ?_⟩
  · have hq : ((Y.isoOfEq hV).hom ≫ (q ∣_ V)) ≫ V.ι ≫ e = (i ⁻¹ᵁ V').ι ≫ q ≫ e := by
      simp [morphismRestrict_ι_assoc, Scheme.isoOfEq_hom_ι_assoc]
    rw [hq, Category.assoc]
    exact (isPullback_morphismRestrict i V').paste_vert h₁
  · have P := (isPullback_morphismRestrict q V).paste_vert h₂
    refine IsPullback.of_iso P (Y.isoOfEq hV).symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · simp [morphismRestrict_ι_assoc, Scheme.isoOfEq_inv_ι_assoc]
    · simp
    · simp
  · intro x hx
    obtain ⟨U, U', W₀, u, p, j, n, k, hu, hp, hj, hx, hn, hl⟩ := hx
    refine ⟨U, U', W₀, u, p, j ≫ V'.ι, n, k ≫ V.ι, hu, by simpa using hp, inferInstance, ?_, by simpa using hn, ?_⟩
    · obtain ⟨w, rfl⟩ := hx
      exact ⟨w, rfl⟩
    · intro T a a' haa
      obtain ⟨y, hy₁, hy₂⟩ := hl T a a' haa
      refine ⟨y ≫ (i ⁻¹ᵁ V').ι, ?_, ?_⟩
      · rw [Category.assoc, ← morphismRestrict_ι, ← Category.assoc, hy₁, Category.assoc]
      · have hq : (Y.isoOfEq hV).hom ≫ (q ∣_ V) ≫ V.ι = (i ⁻¹ᵁ V').ι ≫ q := by
          simp [morphismRestrict_ι, Scheme.isoOfEq_hom_ι_assoc]
        rw [Category.assoc, ← hq, reassoc_of% hy₂]

end GlobalTheory.Pinch
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PinchedChartsRestrictMatchingOpensStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pinched_charts_restrict_matching_opens : ∀ (g : ℕ) (S S' Z B' C Y : Scheme.{0}) (s' : S' ⟶ S) (z : Z ⟶ S) (b' : B' ⟶ S') (e : C ⟶ Z) (i : Y ⟶ B') (q : Y ⟶ C), IsPullback i (q ≫ e) (b' ≫ s') z → IsPullback q (i ≫ b') (e ≫ z) s' → ∀ (V' : B'.Opens) (V : C.Opens), i ⁻¹ᵁ V' = q ⁻¹ᵁ V → ∃ (q₀ : (i ⁻¹ᵁ V').toScheme ⟶ V.toScheme), IsPullback (i ∣_ V') (q₀ ≫ V.ι ≫ e) ((V'.ι ≫ b') ≫ s') z ∧ IsPullback q₀ ((i ∣_ V') ≫ V'.ι ≫ b') ((V.ι ≫ e) ≫ z) s' ∧ ∀ x : V'.toScheme, GlobalTheory.Pinch.Pinched g s' z (V'.ι ≫ b') (V.ι ≫ e) (i ∣_ V') q₀ x → GlobalTheory.Pinch.Pinched g s' z b' e i q (V'.ι x) := by
  first | exact @GlobalTheory.Pinch.restrict_pinched | exact GlobalTheory.Pinch.restrict_pinched | (intros; apply GlobalTheory.Pinch.restrict_pinched <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRelationsLiftVanishingConductor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRelationsLiftVanishingConductor
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Pinch

theorem relations_lift_vanishing : (∀ (R R' ν : Type) [CommRing R] [CommRing R'] [Algebra R R'] (c : Ideal R), (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → ∀ G ∈ (c.map (algebraMap R R')).map (MvPolynomial.C : R' →+* MvPolynomial ν R'), ∃ H : MvPolynomial ν R, MvPolynomial.map (Ideal.Quotient.mk c) H = 0 ∧ MvPolynomial.map (algebraMap R R') H = G) → ∀ (R R' C' D E ν : Type) [CommRing R] [CommRing R'] [CommRing C'] [CommRing D] [CommRing E] [Algebra R R'] [Algebra R' C'] (c : Ideal R) [Algebra (R ⧸ c) D], (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → ∀ (π : C' →+* E) (ψ : D →+* E) (ζ : ν → D) (ξ : ν → C'), RingHom.ker π = c.map ((algebraMap R' C').comp (algebraMap R R')) → ψ.comp ((algebraMap (R ⧸ c) D).comp (Ideal.Quotient.mk c)) = (π.comp (algebraMap R' C')).comp (algebraMap R R') → (∀ s, π (ξ s) = ψ (ζ s)) → Function.Surjective (MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C') → ∀ f : MvPolynomial ν (R ⧸ c), MvPolynomial.aeval ζ f = 0 → ∃ F : MvPolynomial ν R, MvPolynomial.map (Ideal.Quotient.mk c) F = f ∧ MvPolynomial.aeval ξ (MvPolynomial.map (algebraMap R R') F) = 0 := by
  intro hH R R' C' D E ν _ _ _ _ _ _ _ c _ hc π ψ ζ ξ hker hcomm hξ hsurj f hf
  obtain ⟨F₀, rfl⟩ := MvPolynomial.map_surjective (Ideal.Quotient.mk c) Ideal.Quotient.mk_surjective f
  have hπ : π (MvPolynomial.aeval ξ (MvPolynomial.map (algebraMap R R') F₀)) = 0 := by
    have h1 : π (MvPolynomial.aeval ξ (MvPolynomial.map (algebraMap R R') F₀))
        = ψ (MvPolynomial.aeval ζ (MvPolynomial.map (Ideal.Quotient.mk c) F₀)) := by
      rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_map, MvPolynomial.eval₂_map,
        MvPolynomial.eval₂_comp_left, MvPolynomial.eval₂_comp_left, ← RingHom.comp_assoc, hcomm]
      congr 1
      funext s
      exact hξ s
    rw [h1, hf, map_zero]
  have hmem : MvPolynomial.aeval ξ (MvPolynomial.map (algebraMap R R') F₀) ∈
      ((c.map (algebraMap R R')).map (MvPolynomial.C : R' →+* MvPolynomial ν R')).map
        (MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C') := by
    rw [Ideal.map_map]
    change _ ∈ Ideal.map ((MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C') : MvPolynomial ν R' →+* C') _
    rw [Ideal.map_map]
    have : ((MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C') : MvPolynomial ν R' →+* C').comp
        ((MvPolynomial.C : R' →+* MvPolynomial ν R').comp (algebraMap R R'))
        = (algebraMap R' C').comp (algebraMap R R') := by
      ext x; simp
    rw [this, ← hker]
    exact hπ
  obtain ⟨G, hG, hGe⟩ := (Ideal.mem_map_iff_of_surjective _ hsurj).1 hmem
  obtain ⟨H, hH0, hHG⟩ := hH R R' ν c hc G hG
  refine ⟨F₀ - H, ?_, ?_⟩
  · rw [map_sub, hH0, sub_zero]
  · rw [map_sub, hHG, map_sub, hGe, sub_self]

end GlobalTheory.Pinch
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRelationsLiftVanishingConductorStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_relations_lift_vanishing_conductor : (∀ (R R' ν : Type) [CommRing R] [CommRing R'] [Algebra R R'] (c : Ideal R), (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → ∀ G ∈ (c.map (algebraMap R R')).map (MvPolynomial.C : R' →+* MvPolynomial ν R'), ∃ H : MvPolynomial ν R, MvPolynomial.map (Ideal.Quotient.mk c) H = 0 ∧ MvPolynomial.map (algebraMap R R') H = G) → ∀ (R R' C' D E ν : Type) [CommRing R] [CommRing R'] [CommRing C'] [CommRing D] [CommRing E] [Algebra R R'] [Algebra R' C'] (c : Ideal R) [Algebra (R ⧸ c) D], (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → ∀ (π : C' →+* E) (ψ : D →+* E) (ζ : ν → D) (ξ : ν → C'), RingHom.ker π = c.map ((algebraMap R' C').comp (algebraMap R R')) → ψ.comp ((algebraMap (R ⧸ c) D).comp (Ideal.Quotient.mk c)) = (π.comp (algebraMap R' C')).comp (algebraMap R R') → (∀ s, π (ξ s) = ψ (ζ s)) → Function.Surjective (MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C') → ∀ f : MvPolynomial ν (R ⧸ c), MvPolynomial.aeval ζ f = 0 → ∃ F : MvPolynomial ν R, MvPolynomial.map (Ideal.Quotient.mk c) F = f ∧ MvPolynomial.aeval ξ (MvPolynomial.map (algebraMap R R') F) = 0 := by
  first | exact @GlobalTheory.Pinch.relations_lift_vanishing | exact GlobalTheory.Pinch.relations_lift_vanishing | (intros; apply GlobalTheory.Pinch.relations_lift_vanishing <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineOpenSaturatedBasicOpenPreimage
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineOpenSaturatedBasicOpenPreimage
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Pinch

theorem exists_affine_basicOpen_nbhd : ∀ (B' C Y : Scheme.{0}) (i : Y ⟶ B') (q : Y ⟶ C), IsClosedImmersion i →
    IsFinite q → FinAff B' → ∀ (y : Y) (O : C.Opens), IsAffineOpen O → q y ∈ O →
    ∃ (V' : B'.Opens) (r : Γ(C, O)), IsAffineOpen V' ∧ i y ∈ V' ∧ i ⁻¹ᵁ V' = q ⁻¹ᵁ (C.basicOpen r) := by
  intro B' C Y i q hi hq hB y O hO hyO
  have hF : (q ⁻¹' {q y}).Finite := q.finite_preimage_singleton (q y)
  classical
  obtain ⟨V₀, hV₀, hFV₀⟩ := hB ((hF.image i).toFinset)
  have hY₀ : IsAffineOpen (i ⁻¹ᵁ V₀) := hV₀.preimage i
  obtain ⟨h, hFh, hhO⟩ := GlobalTheory.exists_basicOpen_le_of_finite hY₀ (q ⁻¹ᵁ O) hF
    (fun x hx ↦ hFV₀ _ (by simpa using ⟨x, hx, rfl⟩)) (fun x hx ↦ by
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx; simp [hx, hyO])
  have hcl : IsClosed (q '' (Y.basicOpen h : Set Y)ᶜ) :=
    q.isClosedMap _ (Y.basicOpen h).isOpen.isClosed_compl
  have hyW : q y ∉ q '' (Y.basicOpen h : Set Y)ᶜ := by
    rintro ⟨x, hx, hxy⟩
    exact hx (hFh (by simpa using hxy))
  let W : C.Opens := ⟨(q '' (Y.basicOpen h : Set Y)ᶜ)ᶜ, hcl.isOpen_compl⟩
  obtain ⟨r, hrW, hyr⟩ := hO.exists_basicOpen_le (V := W) ⟨q y, hyW⟩ hyO
  have hle : q ⁻¹ᵁ C.basicOpen r ≤ Y.basicOpen h := by
    intro x hx
    by_contra hxh
    exact hrW hx ⟨x, hxh, rfl⟩
  have hbo : q ⁻¹ᵁ C.basicOpen r = Y.basicOpen (q.app O r) := Scheme.preimage_basicOpen q r
  obtain ⟨f', hf'⟩ := hY₀.basicOpen_basicOpen_is_basicOpen h
    (Y.presheaf.map (homOfLE hhO).op (q.app O r))
  rw [Scheme.basicOpen_res, ← hbo, inf_eq_right.mpr hle] at hf'
  obtain ⟨t, ht⟩ := i.app_surjective V₀ hV₀ f'
  refine ⟨B'.basicOpen t, r, hV₀.basicOpen t, ?_, ?_⟩
  · have : y ∈ i ⁻¹ᵁ B'.basicOpen t := by
      rw [Scheme.preimage_basicOpen, ht, hf']; exact hyr
    exact this
  · rw [Scheme.preimage_basicOpen, ht, hf']

end GlobalTheory.Pinch
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineOpenSaturatedBasicOpenPreimageStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_open_saturated_basicOpen_preimage : ∀ (B' C Y : Scheme.{0}) (i : Y ⟶ B') (q : Y ⟶ C), IsClosedImmersion i → IsFinite q → FinAff B' → ∀ (y : Y) (O : C.Opens), IsAffineOpen O → q y ∈ O → ∃ (V' : B'.Opens) (r : Γ(C, O)), IsAffineOpen V' ∧ i y ∈ V' ∧ i ⁻¹ᵁ V' = q ⁻¹ᵁ (C.basicOpen r) := by
  first | exact @GlobalTheory.Pinch.exists_affine_basicOpen_nbhd | exact GlobalTheory.Pinch.exists_affine_basicOpen_nbhd | (intros; apply GlobalTheory.Pinch.exists_affine_basicOpen_nbhd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStandardSmoothLocalizationAwayJacobianDvd
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStandardSmoothLocalizationAwayJacobianDvd
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Pinch

theorem isStandardSmoothOfRelativeDimension_localizationAway_of_det_dvd
    (R ν σ : Type) [CommRing R] [Finite ν] [Fintype σ] [DecidableEq σ] (m : σ → ν)
    (hm : Function.Injective m) (F : σ → MvPolynomial ν R) (h : MvPolynomial ν R)
    (hdvd : (Matrix.of fun s t : σ ↦ MvPolynomial.pderiv (m s) (F t)).det ∣ h) :
    Algebra.IsStandardSmoothOfRelativeDimension (Nat.card ν - Nat.card σ) R
      (Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range F)) h)) := by
  classical
  set A := MvPolynomial ν R ⧸ Ideal.span (Set.range F)
  set T := Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range F)) h)
  let P := Algebra.PreSubmersivePresentation.naive (v := F) m hm
  let Q := Algebra.SubmersivePresentation.localizationAway T
    (Ideal.Quotient.mk (Ideal.span (Set.range F)) h)
  have hPjac : P.jacobian = Ideal.Quotient.mk (Ideal.span (Set.range F))
      (Matrix.of fun s t : σ ↦ MvPolynomial.pderiv (m s) (F t)).det := by
    rw [P.jacobian_eq_jacobiMatrix_det, Algebra.Generators.algebraMap_apply]
    have hM : P.jacobiMatrix = Matrix.of fun s t : σ ↦ MvPolynomial.pderiv (m s) (F t) := by
      ext i j
      simp [P]
    rw [hM]
    have : MvPolynomial.aeval P.val = Ideal.Quotient.mkₐ R (Ideal.span (Set.range F)) :=
      MvPolynomial.algHom_ext fun v => by simp [P]
    rw [this]
    rfl
  let P' : Algebra.SubmersivePresentation R T (Unit ⊕ ν) (Unit ⊕ σ) :=
    { __ := Q.toPreSubmersivePresentation.comp P
      jacobian_isUnit := by
        rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
          Algebra.smul_def]
        refine IsUnit.mul ?_ Q.jacobian_isUnit
        rw [hPjac]
        exact isUnit_of_dvd_unit (map_dvd _ (map_dvd _ hdvd))
          (IsLocalization.Away.algebraMap_isUnit _) }
  refine P'.isStandardSmoothOfRelativeDimension ?_
  change (Q.toPreSubmersivePresentation.comp P).dimension = _
  rw [Algebra.PreSubmersivePresentation.dimension_comp_eq_dimension_add_dimension]
  simp [Algebra.Presentation.dimension, P]

end GlobalTheory.Pinch
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStandardSmoothLocalizationAwayJacobianDvdStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isStandardSmooth_localizationAway_jacobian_dvd : ∀ (R ν σ : Type) [CommRing R] [Finite ν] [Fintype σ] [DecidableEq σ] (m : σ → ν), Function.Injective m → ∀ (F : σ → MvPolynomial ν R) (h : MvPolynomial ν R), (Matrix.of fun s t : σ ↦ MvPolynomial.pderiv (m s) (F t)).det ∣ h → Algebra.IsStandardSmoothOfRelativeDimension (Nat.card ν - Nat.card σ) R (Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range F)) h)) := by
  first | exact @GlobalTheory.Pinch.isStandardSmoothOfRelativeDimension_localizationAway_of_det_dvd | exact GlobalTheory.Pinch.isStandardSmoothOfRelativeDimension_localizationAway_of_det_dvd | (intros; apply GlobalTheory.Pinch.isStandardSmoothOfRelativeDimension_localizationAway_of_det_dvd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PushoutQuotientSurjectiveKerEqMap
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PushoutQuotientSurjectiveKerEqMap
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem pushout_quotient_map_eq_quotient_map_ideal : ∀ (R C E : Type) [CommRing R] [CommRing C] [CommRing E] (c : Ideal R) (f : R →+* C) (π : C →+* E) (χ : R ⧸ c →+* E), IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom (Ideal.Quotient.mk c)) (CommRingCat.ofHom π) (CommRingCat.ofHom χ) → Function.Surjective π ∧ RingHom.ker π = c.map f := by
  intro R C E _ _ _ c f π χ h
  have hw' : ∀ r, π (f r) = χ (Ideal.Quotient.mk c r) := fun r => by
    have := congrArg (fun g => g.hom r) h.w
    simpa using this
  have hle : c.map f ≤ RingHom.ker π := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    simp [RingHom.mem_ker, hw', Ideal.Quotient.eq_zero_iff_mem.mpr hr]
  let q : C →+* C ⧸ c.map f := Ideal.Quotient.mk _
  let qm : R ⧸ c →+* C ⧸ c.map f := Ideal.quotientMap (c.map f) f Ideal.le_comap_map
  let φ : C ⧸ c.map f →+* E := Ideal.Quotient.lift _ π (fun x hx => hle hx)
  have hcomm : CommRingCat.ofHom f ≫ CommRingCat.ofHom q =
      CommRingCat.ofHom (Ideal.Quotient.mk c) ≫ CommRingCat.ofHom qm := by
    ext r; rfl
  let ψ := h.desc (CommRingCat.ofHom q) (CommRingCat.ofHom qm) hcomm
  have h1 : CommRingCat.ofHom π ≫ ψ = CommRingCat.ofHom q := h.inl_desc _ _ _
  have h2 : CommRingCat.ofHom χ ≫ ψ = CommRingCat.ofHom qm := h.inr_desc _ _ _
  have hid : ψ ≫ CommRingCat.ofHom φ = 𝟙 _ := by
    apply h.hom_ext
    · rw [← Category.assoc, h1, Category.comp_id]
      ext x; rfl
    · rw [← Category.assoc, h2, Category.comp_id]
      ext r
      change φ (qm (Ideal.Quotient.mk c r)) = χ (Ideal.Quotient.mk c r)
      rw [← hw']
      rfl
  have hφsurj : Function.Surjective φ := fun e =>
    ⟨ψ e, by
      have := congrArg (fun g => g.hom e) hid
      simpa using this⟩
  refine ⟨?_, ?_⟩
  · intro e
    obtain ⟨y, hy⟩ := hφsurj e
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨x, hy⟩
  · refine le_antisymm ?_ hle
    intro x hx
    have hx1 : ψ.hom (π x) = q x := by
      rw [← CommRingCat.hom_ofHom q, ← h1]; rfl
    rw [RingHom.mem_ker] at hx
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change q x = 0
    rw [← hx1, hx, map_zero]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PushoutQuotientSurjectiveKerEqMapStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pushout_quotient_surjective_ker_eq_map : ∀ (R C E : Type) [CommRing R] [CommRing C] [CommRing E] (c : Ideal R) (f : R →+* C) (π : C →+* E) (χ : R ⧸ c →+* E), IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom (Ideal.Quotient.mk c)) (CommRingCat.ofHom π) (CommRingCat.ofHom χ) → Function.Surjective π ∧ RingHom.ker π = c.map f := by
  first | exact @GlobalTheory.pushout_quotient_map_eq_quotient_map_ideal | exact GlobalTheory.pushout_quotient_map_eq_quotient_map_ideal | (intros; apply GlobalTheory.pushout_quotient_map_eq_quotient_map_ideal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsAdditiveLineBundleFamiliesCompare
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsAdditiveLineBundleFamiliesCompare
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.Pinch

variable {S : Scheme.{0}}

theorem isPullback_fst_whiskerRight {X Y : Over S} (f : X ⟶ Y) (W : Over S) :
    IsPullback (fst X W) (f ▷ W) f (fst Y W) := by
  refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => lift s.fst (s.snd ≫ snd _ _)) (fun s => by simp)
    (fun s => ?_) fun s l h1 h2 => ?_⟩⟩
  · ext1
    · simp [s.condition]
    · simp
  · ext1
    · simp [← h1]
    · simp [← h2]

theorem isPullback_snd_whiskerLeft (W : Over S) {X Y : Over S} (f : X ⟶ Y) :
    IsPullback (snd W X) (W ◁ f) f (snd W Y) := by
  refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => lift (s.snd ≫ fst _ _) s.fst) (fun s => by simp)
    (fun s => ?_) fun s l h1 h2 => ?_⟩⟩
  · ext1
    · simp
    · simp [s.condition]
  · ext1
    · simp [← h2]
    · simp [← h1]

theorem rep_cmp (S : Scheme.{0}) (A B' S' C Z : Over S) [GrpObj A] (b' : B' ⟶ S') (P' : LB (A ⊗ B').left)
    (e : C ⟶ Z) (Q : LB (A ⊗ C).left) (h₁ : Rep A b' P') (h₂ : Rep A e Q) :
    ∃ q : B' ⊗ Z ⟶ C, q ≫ e = snd B' Z ∧ IsPullback q.left (fst B' Z ≫ b').left C.hom S'.hom ∧
      Same A P' Q (fst B' Z) q := by
  have r₁ := Rep.baseChange S A B' S' (S' ⊗ Z) (B' ⊗ Z) b' P' (fst S' Z) (fst B' Z) (b' ▷ Z) h₁
    (isPullback_fst_whiskerRight b' Z)
  have r₂ := Rep.baseChange S A C Z (S' ⊗ Z) (S' ⊗ C) e Q (snd S' Z) (snd S' C) (S' ◁ e) h₂
    (isPullback_snd_whiskerLeft S' e)
  obtain ⟨ε, hε, hs⟩ := rep_unique S A (B' ⊗ Z) (S' ⊗ C) (S' ⊗ Z) (b' ▷ Z) _ (S' ◁ e) _ r₁ r₂
  have hf : ε.hom.left ≫ (fst S' C).left = (fst B' Z ≫ b').left := by
    rw [← Over.comp_left, ← whiskerLeft_fst S' e, reassoc_of% hε, whiskerRight_fst]
  refine ⟨ε.hom ≫ snd S' C, ?_, ?_, ?_⟩
  · rw [Category.assoc, ← whiskerLeft_snd, reassoc_of% hε, whiskerRight_snd]
  · have hpb : IsPullback (snd S' C).left (fst S' C).left C.hom S'.hom :=
      (IsPullback.of_hasPullback S'.hom C.hom).flip
    have : IsIso ε.hom.left := ⟨⟨ε.inv.left, by rw [← Over.comp_left, ε.hom_inv_id, Over.id_left],
      by rw [← Over.comp_left, ε.inv_hom_id, Over.id_left]⟩⟩
    have hiso : IsPullback ε.hom.left (fst B' Z ≫ b').left (fst S' C).left (𝟙 S'.left) :=
      IsPullback.of_horiz_isIso ⟨by rw [hf, Category.comp_id]⟩
    have := hiso.paste_horiz hpb
    rwa [Category.id_comp, ← Over.comp_left] at this
  · rw [same_iff h₁.fam.isLB h₂.fam.isLB]
    rw [same_iff r₁.fam.isLB r₂.fam.isLB, evc_ev h₁.fam.isLB, evc_ev h₂.fam.isLB] at hs
    simpa [lift_fst, lift_snd_assoc] using hs

end GlobalTheory.Pinch
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsAdditiveLineBundleFamiliesCompareStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.representsAdditiveLineBundleFamilies_compare : ∀ (S : Scheme.{0}) (A B' S' C Z : Over S) [GrpObj A] (b' : B' ⟶ S') (P' : LB (A ⊗ B').left) (e : C ⟶ Z) (Q : LB (A ⊗ C).left), GlobalTheory.DualCon.Rep A b' P' → GlobalTheory.DualCon.Rep A e Q → ∃ q : B' ⊗ Z ⟶ C, q ≫ e = snd B' Z ∧ IsPullback q.left (fst B' Z ≫ b').left C.hom S'.hom ∧ Same A P' Q (fst B' Z) q := by
  first | exact @GlobalTheory.Pinch.rep_cmp | exact GlobalTheory.Pinch.rep_cmp | (intros; apply GlobalTheory.Pinch.rep_cmp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSubmersivePresentationAddZeroVariables
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSubmersivePresentationAddZeroVariables
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PinchEnl

open MvPolynomial

theorem ker_aeval_zero_eq_span (D κ : Type) [CommRing D] :
    RingHom.ker (aeval (R := D) (fun _ : κ ↦ (0 : D))) = Ideal.span (Set.range X) := by
  apply le_antisymm
  · intro p hp
    rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
    intro m hm
    by_contra h
    push_neg at h
    have hm0 : m = 0 := by ext i; simpa using h i (Set.mem_univ i)
    subst hm0
    rw [RingHom.mem_ker] at hp
    have : aeval (R := D) (fun _ : κ ↦ (0 : D)) p = AddMonoidAlgebra.coeff p 0 := by
      first
        | (show MvPolynomial.eval (0 : κ → D) p = _
           exact congrFun (congrArg DFunLike.coe (MvPolynomial.eval_zero (R := D) (σ := κ))) p)
        | (rw [MvPolynomial.aeval_def]; simp [MvPolynomial.eval₂_eq, MvPolynomial.coeff_zero_eq_constantCoeff])
    exact (mem_support_iff.mp hm) (this ▸ hp)
  · rw [Ideal.span_le]
    rintro _ ⟨k, rfl⟩
    simp

noncomputable def zeroPre (D κ : Type) [CommRing D] :
    Algebra.PreSubmersivePresentation D D κ κ where
  val _ := 0
  σ' x := C x
  aeval_val_σ' x := by simp
  relation k := X k
  span_range_relation_eq_ker := by
    rw [Algebra.Generators.ker_eq_ker_aeval_val]
    exact (ker_aeval_zero_eq_span D κ).symm
  map := id
  map_inj := Function.injective_id

theorem zeroPre_jacobian (D κ : Type) [CommRing D] [Finite κ] : (zeroPre D κ).jacobian = 1 := by
  classical
  have : Fintype κ := Fintype.ofFinite κ
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
  have h1 : (zeroPre D κ).jacobiMatrix = 1 := by
    ext i j
    rw [Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
    simp [zeroPre, Matrix.one_apply, pderiv_X, Pi.single_apply, eq_comm]
  rw [h1]
  simp

end GlobalTheory.PinchEnl

theorem GlobalTheory.PinchEnl.exists_submersivePresentation_sum_zero : ∀ (R D ν σ κ : Type) [CommRing R] [CommRing D] [Algebra R D] [Finite ν] [Finite σ] [Finite κ] (P : Algebra.SubmersivePresentation R D ν σ), ∃ P' : Algebra.SubmersivePresentation R D (κ ⊕ ν) (κ ⊕ σ), P'.val = Sum.elim (fun _ ↦ 0) P.val := by
  intro R D ν σ κ _ _ _ _ _ _ P
  let Q : Algebra.SubmersivePresentation D D κ κ :=
    { __ := GlobalTheory.PinchEnl.zeroPre D κ
      jacobian_isUnit := by rw [GlobalTheory.PinchEnl.zeroPre_jacobian]; exact isUnit_one }
  refine ⟨Q.comp P, ?_⟩
  ext i
  rcases i with k | j
  · rfl
  · rfl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSubmersivePresentationAddZeroVariablesStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_submersivePresentation_add_zero_variables : ∀ (R D ν σ κ : Type) [CommRing R] [CommRing D] [Algebra R D] [Finite ν] [Finite σ] [Finite κ] (P : Algebra.SubmersivePresentation R D ν σ), ∃ P' : Algebra.SubmersivePresentation R D (κ ⊕ ν) (κ ⊕ σ), P'.val = Sum.elim (fun _ ↦ 0) P.val := by
  first | exact @GlobalTheory.PinchEnl.exists_submersivePresentation_sum_zero | exact GlobalTheory.PinchEnl.exists_submersivePresentation_sum_zero | (intros; apply GlobalTheory.PinchEnl.exists_submersivePresentation_sum_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSpanRelationsConductorOfEvalEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSpanRelationsConductorOfEvalEqZero
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PinchKernel

theorem mem_span_of_eval_eq_zero (R R' D E ν σ : Type) [CommRing R] [CommRing R'] [CommRing D] [CommRing E]
    (a : R →+* R') (c : Ideal R) [Algebra (R ⧸ c) D] (χ : R' →+* E) (ψ : D →+* E) (ζ : ν → D)
    (F : σ → MvPolynomial ν R)
    (hsurj : Function.Surjective (MvPolynomial.aeval ζ : MvPolynomial ν (R ⧸ c) →ₐ[R ⧸ c] D))
    (hker : RingHom.ker (MvPolynomial.aeval ζ : MvPolynomial ν (R ⧸ c) →ₐ[R ⧸ c] D) =
      Ideal.span (Set.range fun s ↦ MvPolynomial.map (Ideal.Quotient.mk c) (F s)))
    (hpo : IsPushout (CommRingCat.ofHom ((algebraMap (R ⧸ c) D).comp (Ideal.Quotient.mk c)))
      (CommRingCat.ofHom a) (CommRingCat.ofHom ψ) (CommRingCat.ofHom χ))
    (G : MvPolynomial ν R') (hG : MvPolynomial.eval₂ χ (fun s ↦ ψ (ζ s)) G = 0) :
    G ∈ Ideal.span (Set.range fun s ↦ MvPolynomial.map a (F s)) ⊔
      (c.map a).map (MvPolynomial.C : R' →+* MvPolynomial ν R') := by
  classical
  set J : Ideal (MvPolynomial ν R') := Ideal.span (Set.range fun s ↦ MvPolynomial.map a (F s)) ⊔
      (c.map a).map (MvPolynomial.C : R' →+* MvPolynomial ν R') with hJ
  let mkJ : MvPolynomial ν R' →+* MvPolynomial ν R' ⧸ J := Ideal.Quotient.mk J
  have hc : ∀ r ∈ c, (mkJ.comp ((MvPolynomial.C : R' →+* MvPolynomial ν R').comp a)) r = 0 := by
    intro r hr
    simp only [RingHom.comp_apply, mkJ]
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_right (Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hr))
  let base : R ⧸ c →+* MvPolynomial ν R' ⧸ J :=
    Ideal.Quotient.lift c (mkJ.comp ((MvPolynomial.C : R' →+* MvPolynomial ν R').comp a)) hc
  let φ : MvPolynomial ν (R ⧸ c) →+* MvPolynomial ν R' ⧸ J :=
    MvPolynomial.eval₂Hom base (fun s ↦ mkJ (MvPolynomial.X s))
  have hφC : ∀ r : R, φ (MvPolynomial.C (Ideal.Quotient.mk c r)) = mkJ (MvPolynomial.C (a r)) := by
    intro r
    simp [φ, base]
  have hφmap : ∀ P : MvPolynomial ν R,
      φ (MvPolynomial.map (Ideal.Quotient.mk c) P) = mkJ (MvPolynomial.map a P) := by
    intro P
    have h : φ.comp (MvPolynomial.map (Ideal.Quotient.mk c)) = mkJ.comp (MvPolynomial.map a) := by
      apply MvPolynomial.ringHom_ext
      · intro r
        simp only [RingHom.comp_apply, MvPolynomial.map_C]
        exact hφC r
      · intro s
        simp [φ]
    exact RingHom.congr_fun h P
  let q : MvPolynomial ν (R ⧸ c) →+* D := (MvPolynomial.aeval ζ : MvPolynomial ν (R ⧸ c) →ₐ[R ⧸ c] D)
  have hkerφ : RingHom.ker q ≤ RingHom.ker φ := by
    have hq : RingHom.ker q = Ideal.span (Set.range fun s ↦ MvPolynomial.map (Ideal.Quotient.mk c) (F s)) := by
      rw [← hker]; rfl
    rw [hq, Ideal.span_le]
    rintro _ ⟨s, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, hφmap, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_left (Ideal.subset_span ⟨s, rfl⟩)
  let dA : D →+* MvPolynomial ν R' ⧸ J :=
    q.liftOfRightInverse (Function.surjInv hsurj) (Function.rightInverse_surjInv hsurj) ⟨φ, hkerφ⟩
  have hdA : ∀ p, dA (q p) = φ p := fun p =>
    RingHom.liftOfRightInverse_comp_apply q _ _ ⟨φ, hkerφ⟩ p
  have hqX : ∀ s, q (MvPolynomial.X s) = ζ s := fun s => by simp [q]
  have hqC : ∀ x : R ⧸ c, q (MvPolynomial.C x) = algebraMap (R ⧸ c) D x := fun x => by
    simp [q]
  have w : CommRingCat.ofHom ((algebraMap (R ⧸ c) D).comp (Ideal.Quotient.mk c)) ≫ CommRingCat.ofHom dA =
      CommRingCat.ofHom a ≫ CommRingCat.ofHom (mkJ.comp (MvPolynomial.C : R' →+* MvPolynomial ν R')) := by
    ext r
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    rw [← hqC, hdA, hφC]
  let desc := hpo.desc (CommRingCat.ofHom dA) (CommRingCat.ofHom (mkJ.comp (MvPolynomial.C : R' →+* MvPolynomial ν R'))) w
  have hinl : ∀ x : D, desc.hom (ψ x) = dA x := fun x => by
    have := congrArg (fun f => f.hom x) (hpo.inl_desc (CommRingCat.ofHom dA)
      (CommRingCat.ofHom (mkJ.comp (MvPolynomial.C : R' →+* MvPolynomial ν R'))) w)
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at this
    exact this
  have hinr : ∀ x : R', desc.hom (χ x) = mkJ (MvPolynomial.C x) := fun x => by
    have := congrArg (fun f => f.hom x) (hpo.inr_desc (CommRingCat.ofHom dA)
      (CommRingCat.ofHom (mkJ.comp (MvPolynomial.C : R' →+* MvPolynomial ν R'))) w)
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at this
    exact this
  have hΦ : desc.hom.comp (MvPolynomial.eval₂Hom χ (fun s ↦ ψ (ζ s))) = mkJ := by
    apply MvPolynomial.ringHom_ext
    · intro x
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
      exact hinr x
    · intro s
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
      rw [hinl, ← hqX, hdA]
      simp [φ]
  have h0 : mkJ G = 0 := by
    rw [← hΦ, RingHom.comp_apply, MvPolynomial.coe_eval₂Hom, hG, map_zero]
  exact (Ideal.Quotient.eq_zero_iff_mem).1 h0

end GlobalTheory.PinchKernel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSpanRelationsConductorOfEvalEqZeroStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_relations_conductor_of_eval_eq_zero : ∀ (R R' D E ν σ : Type) [CommRing R] [CommRing R'] [CommRing D] [CommRing E] (a : R →+* R') (c : Ideal R) [Algebra (R ⧸ c) D] (χ : R' →+* E) (ψ : D →+* E) (ζ : ν → D) (F : σ → MvPolynomial ν R), Function.Surjective (MvPolynomial.aeval ζ : MvPolynomial ν (R ⧸ c) →ₐ[R ⧸ c] D) → RingHom.ker (MvPolynomial.aeval ζ : MvPolynomial ν (R ⧸ c) →ₐ[R ⧸ c] D) = Ideal.span (Set.range fun s ↦ MvPolynomial.map (Ideal.Quotient.mk c) (F s)) → IsPushout (CommRingCat.ofHom ((algebraMap (R ⧸ c) D).comp (Ideal.Quotient.mk c))) (CommRingCat.ofHom a) (CommRingCat.ofHom ψ) (CommRingCat.ofHom χ) → ∀ G : MvPolynomial ν R', MvPolynomial.eval₂ χ (fun s ↦ ψ (ζ s)) G = 0 → G ∈ Ideal.span (Set.range fun s ↦ MvPolynomial.map a (F s)) ⊔ (c.map a).map (MvPolynomial.C : R' →+* MvPolynomial ν R') := by
  first | exact @GlobalTheory.PinchKernel.mem_span_of_eval_eq_zero | exact GlobalTheory.PinchKernel.mem_span_of_eval_eq_zero | (intros; apply GlobalTheory.PinchKernel.mem_span_of_eval_eq_zero <;> assumption)
end
end
