module

public import Development.AutomorphicArithmetic.BlowupCategories.AffC
public import Development.AutomorphicArithmetic.CommutativeAlgebra.IsPullbackOfUniqueSimplicesPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMayerVietorisConnectingExact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafSectionsExact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistSectionsLocallyGenerated
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitMpOmjExtIff
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.FaceRes
public import Development.EtaleCohomology.EtaleSheaves.ProperLineCovers.CoverPf

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.MayerVietorisCoverOfMonoOfZariskiLocal
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

namespace UpperTheory.Cover2Loc

private def sumP (A B : PSh) : PSh where
  obj T := A.obj T ⊕ B.obj T
  map h := TypeCat.ofHom (Sum.map (A.map h) (B.map h))
  map_id T := by
    ext x
    cases x <;> simp
  map_comp h k := by
    ext x
    cases x <;> simp

private def sumD {A B C : PSh} (a : A ⟶ C) (b : B ⟶ C) : sumP A B ⟶ C where
  app T := TypeCat.ofHom (Sum.elim (a.app T) (b.app T))
  naturality S T h := by
    ext x
    cases x with
    | inl x => exact NatTrans.naturality_apply a h x
    | inr x => exact NatTrans.naturality_apply b h x

private theorem map_comp_gen (R : Type) [CommRing R] {P C : PSh} (c : P ⟶ C) {M : Shv R}
    (p : (free R).obj C ⟶ M) (T : Scheme.{0}) (x : P.obj (op T)) :
    Sec.map ((free R).map c ≫ p) (freeGen R P T x) = Sec.map p (freeGen R C T (c.app (op T) x)) := by
  have h4 := (GlobalTheory.T.free_sections_ext_res_map R P M).2.2.2 C c T x
  show Sec.map p (Sec.map ((free R).map c) (freeGen R P T x)) = _
  rw [h4]

private theorem epi_desc (R : Type) [CommRing R] {A B C : PSh} (a : A ⟶ C) (b : B ⟶ C)
    (h : ∀ (T : Scheme.{0}) (y : C.obj (op T)), Loc T fun W k =>
      (∃ x, a.app (op W) x = C.map k.op y) ∨ (∃ x, b.app (op W) x = C.map k.op y)) :
    Epi (biprod.desc ((free R).map a) ((free R).map b)) := by
  haveI : Epi ((free R).map (sumD a b)) := by
    refine (GlobalTheory.T.freeEtaleModuleSheaf_map_mono_epi_iso R (sumD a b)).2.1 fun T y => ?_
    obtain ⟨S, hS, hP⟩ := h T y
    refine ⟨S, hS, fun W k hk => ?_⟩
    rcases hP W k hk with ⟨x, hx⟩ | ⟨x, hx⟩
    · exact ⟨Sum.inl x, hx⟩
    · exact ⟨Sum.inr x, hx⟩
  constructor
  intro M p q hpq
  have h1 : (free R).map a ≫ p = (free R).map a ≫ q := by
    simpa using biprod.inl ≫= hpq
  have h2 : (free R).map b ≫ p = (free R).map b ≫ q := by
    simpa using biprod.inr ≫= hpq
  apply (cancel_epi ((free R).map (sumD a b))).1
  apply (GlobalTheory.T.free_sections_ext_res_map R (sumP A B) M).2.1
  intro T x
  rw [map_comp_gen, map_comp_gen]
  cases x with
  | inl x =>
    show Sec.map p (freeGen R C T (a.app (op T) x)) = Sec.map q (freeGen R C T (a.app (op T) x))
    rw [← map_comp_gen, ← map_comp_gen, h1]
  | inr x =>
    show Sec.map p (freeGen R C T (b.app (op T) x)) = Sec.map q (freeGen R C T (b.app (op T) x))
    rw [← map_comp_gen, ← map_comp_gen, h2]

end UpperTheory.Cover2Loc

theorem UpperTheory.mayerVietorisCover_of_mono_of_zariskiLocal :
    ∀ (R : Type) [CommRing R] {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E), Mono f → Mono g →
        (∀ (k : ℕ) (T : Scheme.{0}) (y : Sx E k T), Loc T fun W h => (∃ x : Sx U k W, x.map f = y.res h) ∨ (∃ x : Sx V k W, x.map g = y.res h)) →
        Cover2 R f g := by
  intro R _ U V E f g hf hg hl
  refine ⟨hf, hg, fun n => ?_⟩
  induction n using Opposite.rec with
  | op n =>
    induction n using SimplexCategory.rec with
    | mk k => exact UpperTheory.Cover2Loc.epi_desc R _ _ fun T y => hl k T y
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.LocallyExistsIsUnitOfSpanRangeEqTop
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

private theorem unit_on (T : Scheme.{0}) (f : Γ(T, ⊤)) (W : T.Opens) (h : W ≤ T.basicOpen f) :
    IsUnit ((T.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom f) := by
  apply T.toRingedSpace.isUnit_of_isUnit_germ
  intro x hx
  rw [TopCat.Presheaf.germ_res_apply]
  exact (T.mem_basicOpen f x trivial).1 (h hx)

private theorem unit_cover (T : Scheme.{0}) {M : ℕ} (v : Fin M → Γ(T, ⊤))
    (hv : Ideal.span (Set.range v) = ⊤) (x : T) : ∃ i, x ∈ T.basicOpen (v i) := by
  have hx : x ∈ (⨆ g ∈ Set.range v, T.basicOpen g) := by
    rw [iSup_basicOpen_of_span_eq_top (X := T) ⊤ _ hv]
    trivial
  simpa [TopologicalSpace.Opens.mem_iSup] using hx

theorem UpperTheory.locally_exists_isUnit_of_span_range_eq_top :
    ∀ (T : Scheme.{0}) {M : ℕ} (v : Fin M → Γ(T, ⊤)), Ideal.span (Set.range v) = ⊤ →
        Loc T fun V g => ∃ i, IsUnit (g.appTop.hom (v i)) := by
  intro T M v hv
  let S : Sieve T :=
    { arrows := fun V g => ∃ i, IsUnit (g.appTop.hom (v i))
      downward_closed := by
        rintro Y Z g ⟨i, hi⟩ k
        refine ⟨i, ?_⟩
        rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
        exact hi.map _ }
  refine ⟨S, ?_, fun V g hg => hg⟩
  have hcov : TopologicalSpace.IsOpenCover (fun i : Fin M => T.basicOpen (v i)) :=
    eq_top_iff.2 (fun x _ => TopologicalSpace.Opens.mem_iSup.2 (unit_cover T v hv x))
  apply Scheme.zariskiTopology_le_etaleTopology
  refine GrothendieckTopology.superset_covering _ ?_
    (Scheme.Cover.mem_grothendieckTopology (T.openCoverOfIsOpenCover _ hcov))
  rintro Z g ⟨W, a, b, ⟨i⟩, rfl⟩
  apply S.downward_closed
  have hu := unit_on T (v i) ((T.basicOpen (v i)).ι ''ᵁ ⊤) (by rw [Scheme.Opens.ι_image_top])
  exact ⟨i, hu⟩
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.LerayHirschOfIsoSquare
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

private theorem pull_bij (q : ℕ) {A B : Spc} (f : A ⟶ B) [IsIso f] (n i : ℤ) :
    Function.Bijective (fun x : Ht q B n i => (pull _ f _ _ x : Ht q A n i)) := by
  refine Function.bijective_iff_has_inverse.2 ⟨fun y => pull _ (inv f) _ _ y, fun x => ?_, fun y => ?_⟩
  · show pull _ (inv f) _ _ (pull _ f _ _ x) = x
    rw [← pull_comp, IsIso.inv_hom_id, pull_id]
  · show pull _ f _ _ (pull _ (inv f) _ _ y) = y
    rw [← pull_comp, IsIso.hom_inv_id, pull_id]

private theorem pull_cup (q : ℕ) {A B : Spc} (f : A ⟶ B) {n m i j : ℤ} (a : Ht q B n i) (b : Ht q B m j) :
    pull _ f _ _ (cup q a b) = cup q (pull _ f _ _ a) (pull _ f _ _ b) :=
  GlobalTheory.T.cup_hypercohomologyPullback (ZMod q) (twPair q i j) f rfl a b

private theorem pull_cast' (q : ℕ) {A B : Spc} (f : A ⟶ B) {n i n' i' : ℤ} (hn : n = n') (hi : i = i')
    (x : Ht q B n i) : pull _ f _ _ (x.cast hn hi) = Ht.cast hn hi (pull _ f _ _ x : Ht q A n i) := by
  subst hn; subst hi; rfl

theorem UpperTheory.lerayHirsch_of_iso_square :
    ∀ (q : ℕ) [NeZero q] {X X' E E' : Spc} (π : X ⟶ E) (π' : X' ⟶ E') (u : X' ⟶ X) (b : E' ⟶ E) [IsIso u] [IsIso b], u ≫ π = π' ≫ b →
        ∀ {m : ℕ} (d e : Fin m → ℤ) (c : ∀ j, Ht q X (d j) (e j)), LH q π d e c → LH q π' d e (fun j => pull _ u _ _ (c j)) := by
  intro q _ X X' E E' π π' u b _ _ w m d e c h n i
  have hP : Function.Bijective (fun (a : ∀ j, Ht q E (n - d j) (i - e j)) j =>
      (pull _ b _ _ (a j) : Ht q E' (n - d j) (i - e j))) :=
    ⟨fun a a' haa => funext fun j => (pull_bij q b _ _).1 (congrFun haa j),
      fun y => ⟨fun j => ((pull_bij q b _ _).2 (y j)).choose,
        funext fun j => ((pull_bij q b _ _).2 (y j)).choose_spec⟩⟩
  have hc : ∀ a : ∀ j, Ht q E (n - d j) (i - e j),
      (∑ j, ((cup q (pull _ π' _ _ (pull _ b _ _ (a j) : Ht q E' (n - d j) (i - e j))) (pull _ u _ _ (c j))).cast
        (by ring) (by ring) : Ht q X' n i)) =
      pull _ u _ _ (∑ j, ((cup q (pull _ π _ _ (a j)) (c j)).cast (by ring) (by ring) : Ht q X n i)) := by
    intro a
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pull_cast', pull_cup, ← pull_comp, ← pull_comp, w]
  have hcomp := (pull_bij q u n i).comp (h n i)
  have heq : (fun y : ∀ j, Ht q E' (n - d j) (i - e j) =>
      ∑ j, ((cup q (pull _ π' _ _ (y j)) (pull _ u _ _ (c j))).cast (by ring) (by ring) : Ht q X' n i)) ∘
      (fun (a : ∀ j, Ht q E (n - d j) (i - e j)) j =>
        (pull _ b _ _ (a j) : Ht q E' (n - d j) (i - e j))) =
      (fun x : Ht q X n i => (pull _ u _ _ x : Ht q X' n i)) ∘ (fun a : ∀ j, Ht q E (n - d j) (i - e j) =>
        ∑ j, ((cup q (pull _ π _ _ (a j)) (c j)).cast (by ring) (by ring) : Ht q X n i)) :=
    funext hc
  rw [← heq] at hcomp
  exact (Function.Bijective.of_comp_iff _ hP).1 hcomp
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.IsIsoStackProductMapOfBijective
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

private noncomputable def invFn {a b : Act} (φ : Act.Hom a b) (A : CommRingCat.{0})
    (h1 : Function.Bijective (fun x : a.D.obj A => φ.d.app A x))
    (h2 : Function.Bijective (fun g : a.G.obj A => φ.g.app A g)) : Ob b A ⥤ Ob a A where
  obj y := ⟨(Equiv.ofBijective _ h1).symm y.pt⟩
  map {x y} f := ⟨(Equiv.ofBijective _ h2).symm f.1, h1.1 (by
    have e1 : φ.d.app A ((Equiv.ofBijective _ h1).symm x.pt) = x.pt := (Equiv.ofBijective _ h1).apply_symm_apply _
    have e2 : φ.d.app A ((Equiv.ofBijective _ h1).symm y.pt) = y.pt := (Equiv.ofBijective _ h1).apply_symm_apply _
    have e3 : φ.g.app A ((Equiv.ofBijective _ h2).symm f.1) = f.1 := (Equiv.ofBijective _ h2).apply_symm_apply _
    show φ.d.app A _ = φ.d.app A _
    rw [φ.eq, e1, e2, e3]
    exact f.2)⟩
  map_id x := Subtype.ext (h2.1 (by
    have e3 : φ.g.app A ((Equiv.ofBijective _ h2).symm 1) = 1 := (Equiv.ofBijective _ h2).apply_symm_apply _
    show φ.g.app A _ = φ.g.app A 1
    rw [map_one (φ.g.app A).hom]
    exact e3))
  map_comp {x y z} f g := Subtype.ext (h2.1 (by
    have e : ∀ u : b.G.obj A, φ.g.app A ((Equiv.ofBijective _ h2).symm u) = u := fun u =>
      (Equiv.ofBijective _ h2).apply_symm_apply _
    show φ.g.app A _ = φ.g.app A (_ * _)
    rw [map_mul (φ.g.app A).hom, e, e, e]
    rfl))

private theorem fn_inv {a b : Act} (φ : Act.Hom a b) (A : CommRingCat.{0})
    (h1 : Function.Bijective (fun x : a.D.obj A => φ.d.app A x))
    (h2 : Function.Bijective (fun g : a.G.obj A => φ.g.app A g)) :
    φ.fn A ⋙ invFn φ A h1 h2 = 𝟭 _ := by
  have ho : ∀ x : Ob a A, (φ.fn A ⋙ invFn φ A h1 h2).obj x = (𝟭 _ : Ob a A ⥤ Ob a A).obj x := fun x =>
    congrArg Ob.mk ((Equiv.ofBijective _ h1).symm_apply_apply x.pt)
  refine CategoryTheory.Functor.hext ho (fun x y f => Ob.hom_heq (ho x) (ho y) _ _ ?_)
  exact (Equiv.ofBijective _ h2).symm_apply_apply f.1

private theorem inv_fn {a b : Act} (φ : Act.Hom a b) (A : CommRingCat.{0})
    (h1 : Function.Bijective (fun x : a.D.obj A => φ.d.app A x))
    (h2 : Function.Bijective (fun g : a.G.obj A => φ.g.app A g)) :
    invFn φ A h1 h2 ⋙ φ.fn A = 𝟭 _ := by
  have ho : ∀ x : Ob b A, (invFn φ A h1 h2 ⋙ φ.fn A).obj x = (𝟭 _ : Ob b A ⥤ Ob b A).obj x := fun x =>
    congrArg Ob.mk ((Equiv.ofBijective _ h1).apply_symm_apply x.pt)
  refine CategoryTheory.Functor.hext ho (fun x y f => Ob.hom_heq (ho x) (ho y) _ _ ?_)
  exact (Equiv.ofBijective _ h2).apply_symm_apply f.1

private theorem comp_bij {C D : Type} [SmallCategory C] [SmallCategory D] (F : C ⥤ D) (G : D ⥤ C)
    (h : F ⋙ G = 𝟭 _) (h' : G ⋙ F = 𝟭 _) (k : ℕ) :
    Function.Bijective (fun s : ComposableArrows C k => s ⋙ F) := by
  refine Function.bijective_iff_has_inverse.2 ⟨fun t => t ⋙ G, fun s => ?_, fun t => ?_⟩
  · show (s ⋙ F) ⋙ G = s
    rw [Functor.assoc, h, Functor.comp_id]
  · show (t ⋙ G) ⋙ F = t
    rw [Functor.assoc, h', Functor.comp_id]

theorem UpperTheory.isIso_stackProductMap_of_bijective :
    ∀ (E : Spc) {a b : Act} (φ : Act.Hom a b), (∀ A, Function.Bijective (fun x : a.D.obj A => φ.d.app A x)) →
        (∀ A, Function.Bijective (fun g : a.G.obj A => φ.g.app A g)) → IsIso (Sp.map E φ) := by
  intro E a b φ h1 h2
  apply isIso_of_bijective_on_simplices
  intro k T
  have hb := (Function.bijective_id (α := Sx E k T)).prodMap
    (comp_bij (C := Ob a (Scheme.Γ.obj (op T))) (D := Ob b (Scheme.Γ.obj (op T)))
      (φ.fn _) (invFn φ _ (h1 _) (h2 _)) (fn_inv φ _ (h1 _) (h2 _)) (inv_fn φ _ (h1 _) (h2 _)) k)
  exact hb
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.StackProductIsPullbackOfActionPullback
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

namespace UpperTheory.PbSp

private theorem hom_val {c : Act} {A : CommRingCat.{0}} {J : Type} [SmallCategory J] {F G : J ⥤ Ob c A} (h : F = G)
    {i j : J} (f : i ⟶ j) : (F.map f).1 = (G.map f).1 := by
  subst h
  rfl

private theorem law_id {P a : Act} (φ : Act.Hom P a) {A : CommRingCat.{0}} {J : Type} [SmallCategory J] (x : J ⥤ Ob a A)
    (j : J) : φ.g.app A 1 = (x.map (𝟙 j)).1 := by
  rw [x.map_id]
  exact map_one _

private theorem law_comp {P a : Act} (φ : Act.Hom P a) {A : CommRingCat.{0}} {J : Type} [SmallCategory J] (x : J ⥤ Ob a A)
    {i j k : J} (f : i ⟶ j) (g : j ⟶ k) (p q : P.G.obj A) (hp : φ.g.app A p = (x.map f).1)
    (hq : φ.g.app A q = (x.map g).1) : φ.g.app A (p * q) = (x.map (f ≫ g)).1 := by
  rw [x.map_comp]
  change _ = (x.map f).1 * (x.map g).1
  rw [map_mul, hp, hq]

private theorem fn_square {P a b c : Act} (t : Act.Hom P a) (l : Act.Hom P b) (r : Act.Hom a c) (u : Act.Hom b c)
    (A : CommRingCat.{0})
    (h1 : ∀ z : P.D.obj A, r.d.app A (t.d.app A z) = u.d.app A (l.d.app A z))
    (h2 : ∀ z : P.G.obj A, r.g.app A (t.g.app A z) = u.g.app A (l.g.app A z)) :
    t.fn A ⋙ r.fn A = l.fn A ⋙ u.fn A := by
  have ho : ∀ z : Ob P A, (t.fn A ⋙ r.fn A).obj z = (l.fn A ⋙ u.fn A).obj z :=
    fun z => congrArg Ob.mk (h1 z.pt)
  refine Functor.hext ho (fun z w f => ?_)
  exact Ob.hom_heq (ho z) (ho w) _ _ (h2 f.1)

private theorem lift_chain {P a b c : Act} (t : Act.Hom P a) (l : Act.Hom P b) (r : Act.Hom a c) (u : Act.Hom b c)
    (A : CommRingCat.{0})
    (h3 : ∀ (x : a.D.obj A) (y : b.D.obj A), r.d.app A x = u.d.app A y → ∃! z : P.D.obj A, t.d.app A z = x ∧ l.d.app A z = y)
    (h4 : ∀ (g : a.G.obj A) (h : b.G.obj A), r.g.app A g = u.g.app A h → ∃! z : P.G.obj A, t.g.app A z = g ∧ l.g.app A z = h)
    {J : Type} [SmallCategory J] (x : J ⥤ Ob a A) (y : J ⥤ Ob b A) (h : x ⋙ r.fn A = y ⋙ u.fn A) :
    ∃! z : J ⥤ Ob P A, z ⋙ t.fn A = x ∧ z ⋙ l.fn A = y := by
  have hobj : ∀ j, r.d.app A (x.obj j).pt = u.d.app A (y.obj j).pt :=
    fun j => congrArg (fun F : J ⥤ Ob c A => (F.obj j).pt) h
  have hmap : ∀ (i j : J) (f : i ⟶ j), r.g.app A (x.map f).1 = u.g.app A (y.map f).1 :=
    fun i j f => hom_val h f
  choose zo hzo hzu using fun j => h3 (x.obj j).pt (y.obj j).pt (hobj j)
  choose zg hzg hzgu using fun (i j : J) (f : i ⟶ j) => h4 (x.map f).1 (y.map f).1 (hmap i j f)
  let F : J ⥤ Ob P A :=
    { obj := fun j => Ob.mk (zo j)
      map := fun {i j} f => ⟨zg i j f, by
        refine (hzu i _ ⟨?_, ?_⟩).symm
        · change t.d.app A (P.smul A (zg i j f) (zo j)) = _
          rw [t.eq, (hzg i j f).1, (hzo j).1]
          exact (x.map f).2.symm
        · change l.d.app A (P.smul A (zg i j f) (zo j)) = _
          rw [l.eq, (hzg i j f).2, (hzo j).2]
          exact (y.map f).2.symm⟩
      map_id := fun j => by
        apply Subtype.ext
        exact (hzgu j j (𝟙 j) 1 ⟨law_id t x j, law_id l y j⟩).symm
      map_comp := fun {i j k} f g => by
        apply Subtype.ext
        exact (hzgu i k (f ≫ g) (zg i j f * zg j k g)
          ⟨law_comp t x f g _ _ (hzg i j f).1 (hzg j k g).1,
            law_comp l y f g _ _ (hzg i j f).2 (hzg j k g).2⟩).symm }
  refine ⟨F, ⟨?_, ?_⟩, ?_⟩
  · have ho : ∀ j, (F ⋙ t.fn A).obj j = x.obj j := fun j => congrArg Ob.mk (hzo j).1
    exact Functor.hext ho (fun i j f => Ob.hom_heq (ho i) (ho j) _ _ (hzg i j f).1)
  · have ho : ∀ j, (F ⋙ l.fn A).obj j = y.obj j := fun j => congrArg Ob.mk (hzo j).2
    exact Functor.hext ho (fun i j f => Ob.hom_heq (ho i) (ho j) _ _ (hzg i j f).2)
  · rintro w ⟨hw1, hw2⟩
    have ho : ∀ j, w.obj j = F.obj j := fun j =>
      congrArg Ob.mk (hzu j (w.obj j).pt
        ⟨congrArg (fun G : J ⥤ Ob a A => (G.obj j).pt) hw1,
          congrArg (fun G : J ⥤ Ob b A => (G.obj j).pt) hw2⟩)
    exact Functor.hext ho (fun i j f =>
      Ob.hom_heq (ho i) (ho j) _ _ (hzgu i j f (w.map f).1 ⟨hom_val hw1 f, hom_val hw2 f⟩))

private abbrev Ch (a : Act) (k : ℕ) (T : Scheme.{0}) : Type := Fin (k + 1) ⥤ Ob a (Scheme.Γ.obj (op T))

private def pr1 {E : Spc} {a : Act} {k : ℕ} {T : Scheme.{0}} (s : Sx (Sp E a) k T) : Sx E k T :=
  Prod.fst (α := Sx E k T) (β := Ch a k T) s

private def pr2 {E : Spc} {a : Act} {k : ℕ} {T : Scheme.{0}} (s : Sx (Sp E a) k T) : Ch a k T :=
  Prod.snd (α := Sx E k T) (β := Ch a k T) s

private def mkS {E : Spc} {a : Act} {k : ℕ} {T : Scheme.{0}} (e : Sx E k T) (x : Ch a k T) : Sx (Sp E a) k T :=
  Prod.mk (α := Sx E k T) (β := Ch a k T) e x

end UpperTheory.PbSp

open UpperTheory.PbSp in
theorem UpperTheory.stackProduct_isPullback_of_actionPullback :
    ∀ (E : Spc) {P a b c : Act} (t : Act.Hom P a) (l : Act.Hom P b) (r : Act.Hom a c) (u : Act.Hom b c),
        (∀ A (z : P.D.obj A), r.d.app A (t.d.app A z) = u.d.app A (l.d.app A z)) →
        (∀ A (z : P.G.obj A), r.g.app A (t.g.app A z) = u.g.app A (l.g.app A z)) →
        (∀ A (x : a.D.obj A) (y : b.D.obj A), r.d.app A x = u.d.app A y → ∃! z : P.D.obj A, t.d.app A z = x ∧ l.d.app A z = y) →
        (∀ A (g : a.G.obj A) (h : b.G.obj A), r.g.app A g = u.g.app A h → ∃! z : P.G.obj A, t.g.app A z = g ∧ l.g.app A z = h) →
        IsPullback (Sp.map E t) (Sp.map E l) (Sp.map E r) (Sp.map E u) := by
  intro E P a b c t l r u h1 h2 h3 h4
  have hsq : ∀ A, t.fn A ⋙ r.fn A = l.fn A ⋙ u.fn A := fun A => fn_square t l r u A (h1 A) (h2 A)
  apply isPullback_of_unique_simplices_pullback
  · ext k T s
    refine Prod.ext rfl ?_
    exact congrArg (fun F => s.2 ⋙ F) (hsq _)
  · intro k T x y hxy
    have e1 : pr1 x = pr1 y := congrArg pr1 hxy
    have e2 : pr2 x ⋙ r.fn _ = pr2 y ⋙ u.fn _ := congrArg pr2 hxy
    obtain ⟨z, ⟨hz1, hz2⟩, hzu⟩ := lift_chain t l r u _ (h3 _) (h4 _) (pr2 x) (pr2 y) e2
    refine ⟨mkS (pr1 x) z, ⟨?_, ?_⟩, ?_⟩
    · change mkS (pr1 x) (z ⋙ t.fn _) = x
      rw [hz1]
      rfl
    · change mkS (pr1 x) (z ⋙ l.fn _) = y
      rw [hz2, e1]
      rfl
    · rintro w ⟨hw1, hw2⟩
      have f1 : pr1 w = pr1 x := congrArg pr1 hw1
      have f2 : pr2 w = z := hzu _ ⟨congrArg pr2 hw1, congrArg pr2 hw2⟩
      change mkS (pr1 w) (pr2 w) = mkS (pr1 x) z
      rw [f1, f2]
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.IsIsoStackProductPairOfBijective
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

namespace UpperTheory.InverseDerivation

variable {a b c : Act} (ρ : Act.Hom a b) (σ : Act.Hom a c) (A : CommRingCat.{0})

private abbrev BD : Prop :=
  Function.Bijective (fun x : a.D.obj A => ((ρ.d.app A x, σ.d.app A x) : b.D.obj A × c.D.obj A))

private abbrev BG : Prop :=
  Function.Bijective (fun g : a.G.obj A => ((ρ.g.app A g, σ.g.app A g) : b.G.obj A × c.G.obj A))

variable {ρ σ A}

private noncomputable def invD (hd : BD ρ σ A) (p : b.D.obj A × c.D.obj A) : a.D.obj A :=
  (Equiv.ofBijective _ hd).symm p

private noncomputable def invG (hg : BG ρ σ A) (p : b.G.obj A × c.G.obj A) : a.G.obj A :=
  (Equiv.ofBijective _ hg).symm p

private theorem invD_fst (hd : BD ρ σ A) (p : b.D.obj A × c.D.obj A) : ρ.d.app A (invD hd p) = p.1 := by
  exact congrArg Prod.fst (Equiv.ofBijective_apply_symm_apply _ hd p)

private theorem invD_snd (hd : BD ρ σ A) (p : b.D.obj A × c.D.obj A) : σ.d.app A (invD hd p) = p.2 := by
  exact congrArg Prod.snd (Equiv.ofBijective_apply_symm_apply _ hd p)

private theorem invG_fst (hg : BG ρ σ A) (p : b.G.obj A × c.G.obj A) : ρ.g.app A (invG hg p) = p.1 := by
  exact congrArg Prod.fst (Equiv.ofBijective_apply_symm_apply _ hg p)

private theorem invG_snd (hg : BG ρ σ A) (p : b.G.obj A × c.G.obj A) : σ.g.app A (invG hg p) = p.2 := by
  exact congrArg Prod.snd (Equiv.ofBijective_apply_symm_apply _ hg p)

private theorem invD_eq (hd : BD ρ σ A) {x : a.D.obj A} {p : b.D.obj A × c.D.obj A}
    (h1 : ρ.d.app A x = p.1) (h2 : σ.d.app A x = p.2) : invD hd p = x := by
  apply hd.1
  refine (Equiv.ofBijective_apply_symm_apply _ hd p).trans ?_
  exact Prod.ext h1.symm h2.symm

private theorem invG_eq (hg : BG ρ σ A) {x : a.G.obj A} {p : b.G.obj A × c.G.obj A}
    (h1 : ρ.g.app A x = p.1) (h2 : σ.g.app A x = p.2) : invG hg p = x := by
  apply hg.1
  refine (Equiv.ofBijective_apply_symm_apply _ hg p).trans ?_
  exact Prod.ext h1.symm h2.symm

private noncomputable def lift (hd : BD ρ σ A) (hg : BG ρ σ A)
    {J : Type} [Category.{0} J] (y : J ⥤ Ob b A) (z : J ⥤ Ob c A) : J ⥤ Ob a A where
  obj j := ⟨invD hd ((y.obj j).pt, (z.obj j).pt)⟩
  map {i j} f := ⟨invG hg ((y.map f).1, (z.map f).1), by
    refine hd.1 (Prod.ext ?_ ?_)
    · change ρ.d.app A _ = ρ.d.app A (a.smul A _ _)
      rw [ρ.eq, invD_fst, invD_fst, invG_fst]
      exact (y.map f).2
    · change σ.d.app A _ = σ.d.app A (a.smul A _ _)
      rw [σ.eq, invD_snd, invD_snd, invG_snd]
      exact (z.map f).2⟩
  map_id j := by
    refine Subtype.ext (invG_eq hg ?_ ?_)
    · change ρ.g.app A 1 = (y.map (𝟙 j)).1
      rw [y.map_id]
      exact map_one (ρ.g.app A).hom
    · change σ.g.app A 1 = (z.map (𝟙 j)).1
      rw [z.map_id]
      exact map_one (σ.g.app A).hom
  map_comp {i j l} f g := by
    refine Subtype.ext (invG_eq hg ?_ ?_)
    · change ρ.g.app A (invG hg _ * invG hg _) = (y.map (f ≫ g)).1
      rw [y.map_comp]
      refine (map_mul (ρ.g.app A).hom _ _).trans ?_
      change ρ.g.app A _ * ρ.g.app A _ = _
      rw [invG_fst, invG_fst]
      rfl
    · change σ.g.app A (invG hg _ * invG hg _) = (z.map (f ≫ g)).1
      rw [z.map_comp]
      refine (map_mul (σ.g.app A).hom _ _).trans ?_
      change σ.g.app A _ * σ.g.app A _ = _
      rw [invG_snd, invG_snd]
      rfl

private theorem lift_fst (hd : BD ρ σ A) (hg : BG ρ σ A)
    {J : Type} [Category.{0} J] (y : J ⥤ Ob b A) (z : J ⥤ Ob c A) :
    lift hd hg y z ⋙ ρ.fn A = y := by
  refine Functor.hext (fun j => ?_) (fun i j f => ?_)
  · change (⟨ρ.d.app A (invD hd ((y.obj j).pt, (z.obj j).pt))⟩ : Ob b A) = y.obj j
    rw [invD_fst]
  · refine Ob.hom_heq ?_ ?_ _ _ ?_
    · change (⟨ρ.d.app A (invD hd ((y.obj i).pt, (z.obj i).pt))⟩ : Ob b A) = y.obj i
      rw [invD_fst]
    · change (⟨ρ.d.app A (invD hd ((y.obj j).pt, (z.obj j).pt))⟩ : Ob b A) = y.obj j
      rw [invD_fst]
    · change ρ.g.app A (invG hg ((y.map f).1, (z.map f).1)) = (y.map f).1
      rw [invG_fst]

private theorem lift_snd (hd : BD ρ σ A) (hg : BG ρ σ A)
    {J : Type} [Category.{0} J] (y : J ⥤ Ob b A) (z : J ⥤ Ob c A) :
    lift hd hg y z ⋙ σ.fn A = z := by
  refine Functor.hext (fun j => ?_) (fun i j f => ?_)
  · change (⟨σ.d.app A (invD hd ((y.obj j).pt, (z.obj j).pt))⟩ : Ob c A) = z.obj j
    rw [invD_snd]
  · refine Ob.hom_heq ?_ ?_ _ _ ?_
    · change (⟨σ.d.app A (invD hd ((y.obj i).pt, (z.obj i).pt))⟩ : Ob c A) = z.obj i
      rw [invD_snd]
    · change (⟨σ.d.app A (invD hd ((y.obj j).pt, (z.obj j).pt))⟩ : Ob c A) = z.obj j
      rw [invD_snd]
    · change σ.g.app A (invG hg ((y.map f).1, (z.map f).1)) = (z.map f).1
      rw [invG_snd]

private theorem lift_comp (hd : BD ρ σ A) (hg : BG ρ σ A)
    {J : Type} [Category.{0} J] (w : J ⥤ Ob a A) :
    lift hd hg (w ⋙ ρ.fn A) (w ⋙ σ.fn A) = w := by
  refine Functor.hext (fun j => ?_) (fun i j f => ?_)
  · change (⟨invD hd (ρ.d.app A (w.obj j).pt, σ.d.app A (w.obj j).pt)⟩ : Ob a A) = w.obj j
    rw [invD_eq hd rfl rfl]
  · refine Ob.hom_heq ?_ ?_ _ _ ?_
    · change (⟨invD hd (ρ.d.app A (w.obj i).pt, σ.d.app A (w.obj i).pt)⟩ : Ob a A) = w.obj i
      rw [invD_eq hd rfl rfl]
    · change (⟨invD hd (ρ.d.app A (w.obj j).pt, σ.d.app A (w.obj j).pt)⟩ : Ob a A) = w.obj j
      rw [invD_eq hd rfl rfl]
    · change invG hg (ρ.g.app A (w.map f).1, σ.g.app A (w.map f).1) = (w.map f).1
      exact invG_eq hg rfl rfl

private theorem comp_inj (hd : BD ρ σ A) (hg : BG ρ σ A)
    {J : Type} [Category.{0} J] {w w' : J ⥤ Ob a A}
    (h1 : w ⋙ ρ.fn A = w' ⋙ ρ.fn A) (h2 : w ⋙ σ.fn A = w' ⋙ σ.fn A) : w = w' := by
  calc w = lift hd hg (w ⋙ ρ.fn A) (w ⋙ σ.fn A) := (lift_comp hd hg w).symm
    _ = lift hd hg (w' ⋙ ρ.fn A) (w' ⋙ σ.fn A) := by rw [h1, h2]
    _ = w' := lift_comp hd hg w'

end UpperTheory.InverseDerivation

open UpperTheory.InverseDerivation in
theorem UpperTheory.isIso_stackProductPair_of_bijective :
    ∀ (E : Spc) {a b c : Act} (ρ : Act.Hom a b) (σ : Act.Hom a c),
        (∀ A, Function.Bijective (fun x : a.D.obj A => ((ρ.d.app A x, σ.d.app A x) : b.D.obj A × c.D.obj A))) →
        (∀ A, Function.Bijective (fun g : a.G.obj A => ((ρ.g.app A g, σ.g.app A g) : b.G.obj A × c.G.obj A))) →
        IsIso (Sp.pair E ρ σ) := by
  intro E a b c ρ σ hd hg
  refine isIso_of_bijective_on_simplices _ (fun k T => ?_)
  let A : CommRingCat := Scheme.Γ.obj (op T)
  change Function.Bijective
    (fun p : (E.obj (op (SimplexCategory.mk k))).obj (op T) × (Fin (k+1) ⥤ Ob a A) =>
      (((p.1, p.2 ⋙ ρ.fn A), p.2 ⋙ σ.fn A) :
        ((E.obj (op (SimplexCategory.mk k))).obj (op T) × (Fin (k+1) ⥤ Ob b A)) × (Fin (k+1) ⥤ Ob c A)))
  refine ⟨fun p q h => ?_, fun q => ?_⟩
  · simp only [Prod.mk.injEq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    exact Prod.ext h1 (comp_inj (hd A) (hg A) h2 h3)
  · refine ⟨(q.1.1, lift (hd A) (hg A) q.1.2 q.2), ?_⟩
    simp only [lift_fst, lift_snd]
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.TwistedSectionEqNsmulGeneratorOfConnected
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

private theorem tw_q_nsmul {q : ℕ} {i : ℤ} {U : Scheme.{0}} (a : Sec (tw q i) U) : q • a = 0 := by
  have h : ((q : ℕ) : ULift.{1} (ZMod q)) = 0 := by
    apply ULift.ext
    simp
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q)), h, zero_smul]

private theorem tw_nsmul_mod {q : ℕ} {i : ℤ} {U : Scheme.{0}} (a : Sec (tw q i) U) (n : ℕ) :
    n • a = (n % q) • a := by
  conv_lhs => rw [← Nat.mod_add_div n q]
  rw [add_nsmul, mul_comm, mul_nsmul, tw_q_nsmul, add_zero]

private theorem mod_eq_of_nsmul_eq {q : ℕ} [NeZero q] {i : ℤ} {U : Scheme.{0}} [Nonempty U]
    (ζ : Prim q Γ(U, ⊤)) {c c' : ℕ} (h : c • twGen i ζ = c' • twGen i ζ) : c % q = c' % q := by
  have hq : 1 ≤ q := NeZero.pos q
  have h1 : (q - 1) * c' + c' = q * c' := by
    have : (q - 1) * c' + c' = ((q - 1) + 1) * c' := by ring
    rw [this, Nat.sub_add_cancel hq]
  have h0 : (c + (q - 1) * c') • twGen i ζ = 0 := by
    rw [add_nsmul, h, ← add_nsmul, add_comm, h1, mul_comm, mul_nsmul, tw_q_nsmul]
  obtain ⟨k, hk⟩ := (GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.1 U ζ _ h0
  have h2 : c + q * c' = c' + q * k := by
    rw [← hk, ← h1]
    ring
  calc c % q = (c + q * c') % q := (Nat.add_mul_mod_self_left _ _ _).symm
    _ = (c' + q * k) % q := by rw [h2]
    _ = c' % q := Nat.add_mul_mod_self_left _ _ _

private theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U)
    (a : Sec F U) : Sec.res (k ≫ g) a = Sec.res k (Sec.res g a) := by
  simp [Sec.res]

private theorem res_nsmul {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (k : V ⟶ U) (n : ℕ)
    (a : Sec F U) : Sec.res k (n • a) = n • Sec.res k a :=
  map_nsmul (F.obj.map k.op).hom n a

private theorem res_gen {q : ℕ} [NeZero q] {i : ℤ} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U)
    (ζ : Prim q Γ(U, ⊤)) :
    Sec.res k (twGen i (ζ.map g.appTop.hom)) = twGen i (ζ.map (k ≫ g).appTop.hom) := by
  rw [(GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.2.1]
  congr 1

theorem UpperTheory.twisted_section_eq_nsmul_generator_of_connected :
    ∀ (q : ℕ) [NeZero q] (i : ℤ) (X : Scheme.{0}) [ConnectedSpace X] (ζ : Prim q Γ(X, ⊤)) (y : Sec (tw q i) X), ∃ c : ℕ, y = c • twGen i ζ := by
  intro q _ i X _ ζ y
  obtain ⟨S, hS, hP⟩ := (GlobalTheory.T.tateTwist_sections_locally_generated q i).2.1 X ζ y
  have hpts := (loc_iff_etale_affine_points X (fun V g => S.arrows g)
    (fun V W g k h => S.downward_closed h k)).1 ⟨S, hS, fun _ _ h => h⟩
  choose V g hA hE hx hS' using hpts
  choose c hc using fun x => hP (V x) (g x) (hS' x)
  have hlc : IsLocallyConstant (fun x => c x % q) := by
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    haveI := hE x
    refine ⟨Set.range (g x), (g x).isOpenMap.isOpen_range, hx x, ?_⟩
    rintro x' ⟨v, hv⟩
    obtain ⟨v', hv'⟩ := hx x'
    obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := g x) (g := g x') v v' (hv.trans hv'.symm)
    haveI : Nonempty ↥(pullback (g x) (g x')) := ⟨z⟩
    have e1 := congrArg (Sec.res (pullback.fst (g x) (g x'))) (hc x)
    have e2 := congrArg (Sec.res (pullback.snd (g x) (g x'))) (hc x')
    rw [← res_comp, res_nsmul, res_gen] at e1 e2
    rw [pullback.condition] at e1
    exact (mod_eq_of_nsmul_eq _ (e1.symm.trans e2)).symm
  obtain ⟨x0⟩ : Nonempty X := inferInstance
  have hconst : ∀ x, c x % q = c x0 % q := fun x => hlc.apply_eq_of_preconnectedSpace x x0
  refine ⟨c x0, (GlobalTheory.T.etaleSheafSections_ext_and_glue (ZMod q) (tw q i) X).1 _ _ ?_⟩
  refine (loc_iff_etale_affine_points X _ ?_).2 fun x => ⟨V x, g x, hA x, hE x, hx x, ?_⟩
  · intro V W g k h
    rw [res_comp, res_comp, h]
  · rw [hc, res_nsmul, (GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.2.1, tw_nsmul_mod, hconst x, ← tw_nsmul_mod]
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.MayerVietorisConnectingCupPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlexanderWhitneyCupLeibnizEtale
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlexanderWhitneyCupLeibnizEtale
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem aw_leibniz_rule : ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k) (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) (γ : Cochain ((chains R).obj E) K k) (γ₁ γ₂ : Cochain ((chains R).obj E) K (k + 1)), μ.IsAW hk α β γ → μ.IsAW (by omega) (δ n (n + 1) α) β γ₁ → μ.IsAW (by omega) α (δ m (m + 1) β) γ₂ → δ k (k + 1) γ = γ₁ + n.negOnePow • γ₂ := by
  intro R _ I J K μ E n m k hk α β γ γ₁ γ₂ hc h₁ h₂
  exact CupSpec.aw_leibniz μ rfl rfl rfl hc h₁ h₂

end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlexanderWhitneyCupLeibnizEtaleStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
theorem _root_.GlobalTheory.T.alexanderWhitney_cup_leibniz_etale : ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k) (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) (γ : Cochain ((chains R).obj E) K k) (γ₁ γ₂ : Cochain ((chains R).obj E) K (k + 1)), μ.IsAW hk α β γ → μ.IsAW (by omega) (δ n (n + 1) α) β γ₁ → μ.IsAW (by omega) α (δ m (m + 1) β) γ₂ → δ k (k + 1) γ = γ₁ + n.negOnePow • γ₂ := by
  first | exact @GlobalTheory.EtC.aw_leibniz_rule | exact GlobalTheory.EtC.aw_leibniz_rule | (intros; apply GlobalTheory.EtC.aw_leibniz_rule <;> assumption)
end
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf

namespace UpperTheory.MvLin

variable {R : Type} [CommRing R]

private noncomputable abbrev pb {E' E : Spc} (π : E' ⟶ E) {I : Cx R} {n : ℤ} (a : Cochain ((chains R).obj E) I n) :
    Cochain ((chains R).obj E') I n :=
  (Cochain.ofHom ((chains R).map π)).comp a (zero_add n)

private noncomputable abbrev pbz {E' E : Spc} (π : E' ⟶ E) {I : Cx R} {n : ℤ} (a : Cocycle ((chains R).obj E) I n) :
    Cocycle ((chains R).obj E') I n :=
  zcomp (Cocycle.ofHom ((chains R).map π)) a (zero_add n)

private theorem pb_comp {E'' E' E : Spc} (π : E'' ⟶ E') (ρ : E' ⟶ E) {I : Cx R} {n : ℤ}
    (a : Cochain ((chains R).obj E) I n) : pb (π ≫ ρ) a = pb π (pb ρ a) := by
  simp only [pb, Functor.map_comp]
  rw [Cochain.ofHom_comp]
  exact Cochain.comp_assoc_of_first_is_zero_cochain _ _ _ (zero_add n)

private theorem sub_map {E' E : Spc} (π : E' ⟶ E) {N : ℕ} {U : Scheme.{0}} (x : Sx E' N U) (j l : ℕ) (h : j + l ≤ N) :
    (x.map π).sub j l h = (x.sub j l h).map π :=
  (ConcreteCategory.congr_hom (NatTrans.congr_app (π.naturality (SimplexCategory.subinterval j l h).op) (op U)) x).symm

private theorem ev_pb {E' E : Spc} (π : E' ⟶ E) {I : Cx R} {n : ℤ} (a : Cochain ((chains R).obj E) I n)
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E' p U) :
    ev (pb π a) p s h U x = ev a p s h U (x.map π) := by
  have hp := CupSpec.ev_pull π a p s h U x
  exact hp

private theorem aw_pb {I J K : Cx R} (μ : Pair I J K) {E' E : Spc} (π : E' ⟶ E) {n m k : ℤ} (hk : n + m = k)
    {a : Cochain ((chains R).obj E) I n} {b : Cochain ((chains R).obj E) J m} {c : Cochain ((chains R).obj E) K k}
    (h : μ.IsAW hk a b c) : μ.IsAW hk (pb π a) (pb π b) (pb π c) := by
  intro N w hw U x
  rw [ev_pb, h N w hw U (x.map π)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [ev_pb, ev_pb, sub_map, sub_map]

private theorem aw_unique {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k)
    {a : Cochain ((chains R).obj E) I n} {b : Cochain ((chains R).obj E) J m} {c c' : Cochain ((chains R).obj E) K k}
    (h : μ.IsAW hk a b c) (h' : μ.IsAW hk a b c') : c = c' :=
  ((GlobalTheory.T.isAW_existsUnique_biadditive_etale R μ hk).1 a b).unique h h'

private theorem aw_zero {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k)
    (a : Cochain ((chains R).obj E) I n) : μ.IsAW hk a (0 : Cochain ((chains R).obj E) J m) 0 := by
  obtain ⟨z, hz, -⟩ := (GlobalTheory.T.isAW_existsUnique_biadditive_etale R μ hk).1 a (0 : Cochain ((chains R).obj E) J m)
  have h2 := (GlobalTheory.T.isAW_existsUnique_biadditive_etale R μ hk).2.2 a 0 0 z z hz hz
  rw [add_zero] at h2
  have h3 : z + z = z := aw_unique μ hk h2 hz
  have h4 : z = 0 := by simpa using h3
  exact h4 ▸ hz

private theorem aw_delta {I J K : Cx R} (μ : Pair I J K) {E' E : Spc} (π : E' ⟶ E) {n m : ℤ}
    {a : Cochain ((chains R).obj E') I n} {z : Cocycle ((chains R).obj E) I (n + 1)} {η : Cocycle ((chains R).obj E) J m}
    {a' : Cochain ((chains R).obj E') K (n + m)} {z' : Cochain ((chains R).obj E) K (n + m + 1)}
    (hk : n + 1 + m = n + m + 1) (ha : δ n (n + 1) a = pb π z.1) (h1 : μ.IsAW rfl a (pbz π η).1 a')
    (h2 : μ.IsAW hk z.1 η.1 z') : δ (n + m) (n + m + 1) a' = pb π z' := by
  have h3 : μ.IsAW hk (δ n (n + 1) a) (pbz π η).1 (pb π z') := ha ▸ aw_pb μ π hk h2
  have h4 : μ.IsAW (by omega : n + (m + 1) = n + m + 1) a (δ m (m + 1) (pbz π η).1) 0 := by
    rw [Cocycle.δ_eq_zero]
    exact aw_zero μ _ a
  have h5 := GlobalTheory.T.alexanderWhitney_cup_leibniz_etale R μ rfl a (pbz π η).1 a' (pb π z') 0 h1 h3 h4
  simpa using h5

private theorem mv_core {I J K : Cx R} (μ : Pair I J K) {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) {n m : ℤ}
    (γ : Cocycle ((chains R).obj (pullback f g)) I n) (ζ : Cocycle ((chains R).obj E) I (n + 1))
    (α : Cochain ((chains R).obj U) I n) (β : Cochain ((chains R).obj V) I n)
    (η : Cocycle ((chains R).obj E) J m)
    (hγ : pb (pullback.fst f g) α - pb (pullback.snd f g) β = γ.1)
    (hα : δ n (n + 1) α = pb f ζ.1) (hβ : δ n (n + 1) β = pb g ζ.1) (hk : n + 1 + m = n + m + 1) :
    ∃ (γ' : Cocycle ((chains R).obj (pullback f g)) K (n + m)) (ζ' : Cocycle ((chains R).obj E) K (n + m + 1))
      (α' : Cochain ((chains R).obj U) K (n + m)) (β' : Cochain ((chains R).obj V) K (n + m)),
      μ.IsAW rfl γ.1 (pbz (pullback.fst f g ≫ f) η).1 γ'.1 ∧ μ.IsAW hk ζ.1 η.1 ζ'.1 ∧
      pb (pullback.fst f g) α' - pb (pullback.snd f g) β' = γ'.1 ∧
      δ (n + m) (n + m + 1) α' = pb f ζ'.1 ∧ δ (n + m) (n + m + 1) β' = pb g ζ'.1 := by
  obtain ⟨γ', hγ'⟩ := (GlobalTheory.T.cup_eq_class_of_isAW R μ rfl).1 γ (pbz (pullback.fst f g ≫ f) η)
  obtain ⟨ζ', hζ'⟩ := (GlobalTheory.T.cup_eq_class_of_isAW R μ hk).1 ζ η
  obtain ⟨α', hα', -⟩ := (GlobalTheory.T.isAW_existsUnique_biadditive_etale R μ rfl).1 α (pbz f η).1
  obtain ⟨β', hβ', -⟩ := (GlobalTheory.T.isAW_existsUnique_biadditive_etale R μ rfl).1 β (pbz g η).1
  refine ⟨γ', ζ', α', β', hγ', hζ', ?_, aw_delta μ f hk hα hα' hζ', aw_delta μ g hk hβ hβ' hζ'⟩
  have e1 : pb (pullback.fst f g) (pbz f η).1 = (pbz (pullback.fst f g ≫ f) η).1 := (pb_comp _ _ _).symm
  have e2 : pb (pullback.snd f g) (pbz g η).1 = (pbz (pullback.fst f g ≫ f) η).1 :=
    (pb_comp _ _ _).symm.trans (by rw [pullback.condition]; rfl)
  have a1 := aw_pb μ (pullback.fst f g) rfl hα'
  have a2 := aw_pb μ (pullback.snd f g) rfl hβ'
  rw [e1] at a1
  rw [e2] at a2
  have a3 := (GlobalTheory.T.isAW_existsUnique_biadditive_etale R μ rfl).2.1 _ _ _ _ _ hγ' a2
  have e3 : γ.1 + pb (pullback.snd f g) β = pb (pullback.fst f g) α := by rw [← hγ, sub_add_cancel]
  rw [e3] at a3
  have e4 := aw_unique μ rfl a1 a3
  rw [e4, add_sub_cancel_right]

private theorem cast_cup (q : ℕ) {E : Spc} {n m k i j : ℤ} (hk : n + m = k) (a : Ht q E n i) (b : Ht q E m j) :
    (cup q a b).cast hk rfl = (twPair q i j).cup E hk a b := by
  subst hk
  rfl

end UpperTheory.MvLin

open UpperTheory.MvLin in
theorem UpperTheory.mayerVietorisConnecting_cup_pullback :
    ∀ (q : ℕ) [NeZero q] {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E), Cover2 (ZMod q) f g → ∀ (n m i j : ℤ) (c : Ht q (pullback f g) n i)
        (x : Ht q E (n + 1) i) (y : Ht q E m j), IsMVd f g (tw q i) n c x →
        IsMVd f g (tw q (i + j)) (n + m) (cup q c (pull _ (pullback.fst f g ≫ f) _ _ y)) ((cup q x y).cast (by ring) rfl) := by
  intro q _ U V E f g _ n m i j c x y h
  obtain ⟨γ, ζ, α, β, rfl, rfl, hγ, hα, hβ⟩ := h
  obtain ⟨η, rfl⟩ := y.mk_surjective
  have hk : n + 1 + m = n + m + 1 := by ring
  obtain ⟨γ', ζ', α', β', h1, h2, h3, h4, h5⟩ := mv_core (twPair q i j) f g γ ζ α β η hγ hα hβ hk
  refine ⟨γ', ζ', α', β', ?_, ?_, h3, h4, h5⟩
  · exact ((GlobalTheory.T.cup_eq_class_of_isAW _ (twPair q i j) rfl).2 γ _ γ' h1).symm
  · rw [cast_cup q hk]
    exact ((GlobalTheory.T.cup_eq_class_of_isAW _ (twPair q i j) hk).2 ζ η ζ' h2).symm
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.SubsingletonHypercohomologyFreeOfSubsingletonCoh
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Bc

theorem UpperTheory.subsingleton_hypercohomology_free_of_subsingleton_cohomology :
    ∀ (F : Shv ℤ) (P : PSh) (n : ℤ), Subsingleton (H ℤ (disc.obj P) F n) → Subsingleton (HK ℤ (sgl ((free ℤ).obj P)) F n) := by
  intro F P n hs
  obtain ⟨e, -, -⟩ := GlobalTheory.T.exists_natural_homotopyEquiv_chains_constant_presheaf ℤ
  haveI : (res ℤ F).IsKInjective := (GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties ℤ F).1
  haveI : QuasiIso (e P).hom := (e P).quasiIso_hom
  have hb := GlobalTheory.T.hypercohomologyPullback_bijective_of_quasiIso ℤ (e P).hom (res ℤ F) n
  exact hb.2.subsingleton
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.PicUnit
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC TensorProduct

namespace UpperTheory.PicD

theorem unitSec_mul {U : Scheme.{0}} (u v : (Γ(U, ⊤))ˣ) : unitSec (u * v) = unitSec u + unitSec v := by
  unfold unitSec ofRings.sec
  exact map_add (ModuleCat.Hom.hom ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op U)))
    (⟨Additive.ofMul u⟩ : ULift.{1, 0} (Additive (Γ(U, ⊤))ˣ)) ⟨Additive.ofMul v⟩

theorem unitSec_one {U : Scheme.{0}} : unitSec (1 : (Γ(U, ⊤))ˣ) = 0 := by
  unfold unitSec ofRings.sec
  exact map_zero (ModuleCat.Hom.hom ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op U)))

theorem unitSec_res {V U : Scheme.{0}} (g : V ⟶ U) (u : (Γ(U, ⊤))ˣ) :
    Sec.res g (unitSec u) = unitSec (Units.map g.appTop.hom.toMonoidHom u) := by
  unfold unitSec ofRings.sec
  have h := congrArg (fun f => (ModuleCat.Hom.hom f)
    (⟨Additive.ofMul u⟩ : ULift.{1, 0} (Additive (Γ(U, ⊤))ˣ)))
    ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).naturality g.op)
  exact h.symm

end UpperTheory.PicD
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.IsDedekindDomainAffineSectionsOfIsCurve
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

private theorem not_isField_of_curve {k : Type} [Field k] {C : Scheme.{0}} (c : C ⟶ Sp k) (hc : IsCurve c)
    (W : C.Opens) (hW : IsAffineOpen W) (hWn : (W : Set C).Nonempty) : ¬ IsField Γ(C, W) := by
  intro hF
  have h := CurveCut.CoverPf.krullDim_eq_one c hc W hW hWn
  rw [ringKrullDim_eq_zero_of_isField hF] at h
  norm_num at h

private theorem stalk_isIntegrallyClosed {k : Type} [Field k] [IsAlgClosed k] {C : Scheme.{0}} (c : C ⟶ Sp k)
    (hc : IsCurve c) (y : C) : IsIntegrallyClosed (C.presheaf.stalk y) := by
  haveI := hc.1
  obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := y) (by simp)
  have hne : (U : Set C).Nonempty := ⟨y, hyU⟩
  haveI : Nonempty U := ⟨⟨y, hyU⟩⟩
  haveI : IsIntegrallyClosed Γ(C, U) := CurveCut.CoverPf.leafNormal _ c hc U hU hne
  letI : Algebra Γ(C, U) (C.presheaf.stalk y) := C.presheaf.algebra_section_stalk ⟨y, hyU⟩
  haveI := hU.isLocalization_stalk ⟨y, hyU⟩
  exact isIntegrallyClosed_of_isLocalization _ (hU.primeIdealOf ⟨y, hyU⟩).asIdeal.primeCompl
    (Ideal.primeCompl_le_nonZeroDivisors _)

theorem UpperTheory.isDedekindDomain_affine_sections_of_isCurve :
    ∀ (k : Type) [Field k] [IsAlgClosed k] {C : Scheme.{0}} (c : C ⟶ Sp k), IsCurve c → (∀ W : C.Opens, IsAffineOpen W → (W : Set C).Nonempty → IsDedekindDomain Γ(C, W) ∧ ¬ IsField Γ(C, W)) ∧ ∀ y : C, IsIntegrallyClosed (C.presheaf.stalk y) := by
  intro k _ _ C c hc
  refine ⟨fun W hW hWn => ⟨?_, not_isField_of_curve c hc W hW hWn⟩, stalk_isIntegrallyClosed c hc⟩
  exact LateralTheory.E.E4.CurveCut.CoverPf.LeafDedRing_of LateralTheory.E.E4.CurveCut.CoverPf.leafDim1
    LateralTheory.E.E4.CurveCut.CoverPf.leafNormal k c hc W hW hWn
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.EpiFreeBiprodDescOfZariskiLocallySurjective
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC UpperTheory.Pbf

private def sumP (P₁ P₂ : PSh) : PSh where
  obj U := P₁.obj U ⊕ P₂.obj U
  map h := TypeCat.ofHom (Sum.map (P₁.map h) (P₂.map h))
  map_id U := by
    ext x
    rcases x with x | x <;> simp
  map_comp a b := by
    ext x
    rcases x with x | x <;> simp

private def sumD {P₁ P₂ Q : PSh} (f : P₁ ⟶ Q) (g : P₂ ⟶ Q) : sumP P₁ P₂ ⟶ Q where
  app U := TypeCat.ofHom (Sum.elim (f.app U) (g.app U))
  naturality U V k := by
    ext x
    rcases x with x | x
    · exact congrFun (congrArg (fun t => t.hom) (f.naturality k)) x
    · exact congrFun (congrArg (fun t => t.hom) (g.naturality k)) x

theorem UpperTheory.epi_freeBiprodDesc_of_zariskiLocally_surjective :
    ∀ (R : Type) [CommRing R] {P₁ P₂ Q : PSh} (f : P₁ ⟶ Q) (g : P₂ ⟶ Q), (∀ (U : Scheme.{0}) (y : Q.obj (op U)), Loc U fun V h => (∃ x, f.app (op V) x = Q.map h.op y) ∨ ∃ x, g.app (op V) x = Q.map h.op y) → Epi (biprod.desc ((free R).map f) ((free R).map g)) := by
  intro R _ P₁ P₂ Q f g h
  have mc : ∀ {P : PSh} (c : P ⟶ Q) {M : Shv R} (p : (free R).obj Q ⟶ M) (T : Scheme.{0})
      (x : P.obj (op T)),
      Sec.map ((free R).map c ≫ p) (freeGen R P T x) = Sec.map p (freeGen R Q T (c.app (op T) x)) := by
    intro P c M p T x
    have h4 := (GlobalTheory.T.free_sections_ext_res_map R P M).2.2.2 Q c T x
    show Sec.map p (Sec.map ((free R).map c) (freeGen R P T x)) = _
    rw [h4]
  have hE : Epi ((free R).map (sumD f g)) := by
    apply (GlobalTheory.T.freeEtaleModuleSheaf_map_mono_epi_iso R (sumD f g)).2.1
    intro T y
    obtain ⟨S, hS, hP⟩ := h T y
    refine ⟨S, hS, fun W k hk => ?_⟩
    rcases hP W k hk with ⟨x, hx⟩ | ⟨x, hx⟩
    · exact ⟨Sum.inl x, hx⟩
    · exact ⟨Sum.inr x, hx⟩
  constructor
  intro Z u v huv
  have ha : (free R).map f ≫ u = (free R).map f ≫ v := by
    simpa using congrArg (biprod.inl ≫ ·) huv
  have hb : (free R).map g ≫ u = (free R).map g ≫ v := by
    simpa using congrArg (biprod.inr ≫ ·) huv
  rw [← cancel_epi ((free R).map (sumD f g))]
  apply (GlobalTheory.T.free_sections_ext_res_map R (sumP P₁ P₂) Z).2.1
  intro T z
  rw [mc, mc]
  cases z with
  | inl x =>
    have e := mc f u T x
    have e' := mc f v T x
    rw [ha] at e
    exact e.symm.trans e'
  | inr x =>
    have e := mc g u T x
    have e' := mc g v T x
    rw [hb] at e
    exact e.symm.trans e'
end
