module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivalenceBasicProperties
public import Development.AutomorphicArithmetic.CommutativeAlgebra.MayerVietorisCoverOfMonoOfZariskiLocal
public import Development.AutomorphicArithmetic.CommutativeAlgebra.SupportDoubleComplexTotalRepresentsVanishingCoch
public import Development.EtaleCohomology.EtaleTrace.LocalSplitting.Cover2
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCochainEvEqOfNaturalStatement

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.PullCupPowEqCupPowPull
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

private theorem pull_cast {q : ℕ} {X Y : Spc} (f : X ⟶ Y) {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q Y n i) :
    pull _ f _ _ (x.cast hn hi) = Ht.cast hn hi (pull _ f _ _ x : Ht q X n i) := by
  subst hn hi
  rfl

private theorem pull_cup {q : ℕ} {X Y : Spc} (f : X ⟶ Y) {n m i j : ℤ} (a : Ht q Y n i) (b : Ht q Y m j) :
    pull _ f _ _ (cup q a b) = cup q (pull _ f _ _ a : Ht q X n i) (pull _ f _ _ b : Ht q X m j) :=
  GlobalTheory.T.cup_hypercohomologyPullback (ZMod q) (twPair q i j) f rfl a b

theorem UpperTheory.pull_cupPow_eq_cupPow_pull :
    ∀ (q : ℕ) [NeZero q] {X Y : Spc} (f : X ⟶ Y) (ξ : Ht q Y 2 1) (j : ℕ), Inv q Y → pull _ f _ _ (cpow q ξ j) = cpow q (pull _ f _ _ ξ) j := by
  intro q _ X Y f ξ j hY
  induction j with
  | zero =>
    rw [cpow_zero, cpow_zero, pull_cast, (GlobalTheory.T.tateTwistUnitClass_rootClass_spec q).2.2.1 f hY]
  | succ k ih =>
    rw [cpow_succ, cpow_succ, pull_cast, pull_cup, ih]
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.MayerVietorisStackProductOfInjectiveOfLocallyCov
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

namespace UpperTheory.FullyFaithfulLift

private theorem cancel_comp {J C D : Type} [Category J] [Category C] [Category D] (F : C ⥤ D)
    (hobj : Function.Injective F.obj) [F.Faithful] (c c' : J ⥤ C) (h : c ⋙ F = c' ⋙ F) : c = c' := by
  have hob : ∀ j, c.obj j = c'.obj j := fun j => hobj (congrArg (fun G => G.obj j) h)
  refine CategoryTheory.Functor.ext hob ?_
  intro X Y f
  apply F.map_injective
  have e := CategoryTheory.Functor.congr_hom h f
  simp only [CategoryTheory.Functor.comp_map] at e
  rw [e]
  simp [eqToHom_map]

private theorem lift_comp {J C D : Type} [Category J] [Category C] [Category D] (F : C ⥤ D)
    [F.Full] [F.Faithful] (c : J ⥤ D) (l : J → C) (hl : ∀ j, F.obj (l j) = c.obj j) :
    ∃ c' : J ⥤ C, c' ⋙ F = c := by
  refine ⟨{ obj := l
            map := fun {i j} f => F.preimage (eqToHom (hl i) ≫ c.map f ≫ eqToHom (hl j).symm)
            map_id := fun i => F.map_injective (by simp)
            map_comp := fun f g => F.map_injective (by simp) }, ?_⟩
  refine CategoryTheory.Functor.ext hl (fun i j f => ?_)
  simp

private theorem sp_map_eq {E : Spc} {a b : Act} (φ : Act.Hom a b) {k : ℕ} {T : Scheme.{0}} (x : Sx (Sp E a) k T) :
    Sx.map (Sp.map E φ) x = ((x.1, Sx.map (spcMap φ) x.2) : Sx (Sp E b) k T) := rfl

private theorem fn_obj_inj {a b : Act} (φ : Act.Hom a b) (hi : ∀ A, Function.Injective (fun x : a.D.obj A => φ.d.app A x))
    (A : CommRingCat.{0}) : Function.Injective (φ.fn A).obj := by
  intro x y h
  have e : φ.d.app A x.pt = φ.d.app A y.pt := congrArg Ob.pt h
  cases x
  cases y
  congr
  exact hi A e

private theorem fn_faithful {a b : Act} (φ : Act.Hom a b) (hb : ∀ A, Function.Bijective (fun g : a.G.obj A => φ.g.app A g))
    (A : CommRingCat.{0}) : (φ.fn A).Faithful :=
  ⟨fun {_ _} _ _ h => Subtype.ext ((hb A).1 (congrArg Subtype.val h))⟩

private theorem fn_full {a b : Act} (φ : Act.Hom a b) (hi : ∀ A, Function.Injective (fun x : a.D.obj A => φ.d.app A x))
    (hb : ∀ A, Function.Bijective (fun g : a.G.obj A => φ.g.app A g)) (A : CommRingCat.{0}) : (φ.fn A).Full := by
  constructor
  intro x y u
  obtain ⟨g, hg⟩ := (hb A).2 u.1
  refine ⟨⟨g, ?_⟩, ?_⟩
  · apply hi A
    have e := φ.eq A g y.pt
    have hg' : φ.g.app A g = u.1 := hg
    rw [hg'] at e
    exact u.2.trans e.symm
  · apply Subtype.ext
    exact hg

private theorem mono_sp (E : Spc) {a b : Act} (φ : Act.Hom a b) (hi : ∀ A, Function.Injective (fun x : a.D.obj A => φ.d.app A x))
    (hb : ∀ A, Function.Bijective (fun g : a.G.obj A => φ.g.app A g)) : Mono (Sp.map E φ) := by
  apply UpperTheory.mono_of_injective_on_simplices
  intro k T x y h
  simp only [sp_map_eq] at h
  obtain ⟨h1, h2⟩ := Prod.mk.inj h
  haveI := fn_faithful φ hb Γ(T, ⊤)
  have h2' : (show ComposableArrows (Ob a Γ(T, ⊤)) k from x.2) ⋙ φ.fn Γ(T, ⊤) =
      (show ComposableArrows (Ob a Γ(T, ⊤)) k from y.2) ⋙ φ.fn Γ(T, ⊤) := h2
  exact Prod.ext h1 (cancel_comp (φ.fn Γ(T, ⊤)) (fn_obj_inj φ hi _) _ _ h2')

private theorem lift_sp (E : Spc) {a₁ a : Act} (φ : Act.Hom a₁ a) (hi : ∀ A, Function.Injective (fun x : a₁.D.obj A => φ.d.app A x))
    (hb : ∀ A, Function.Bijective (fun g : a₁.G.obj A => φ.g.app A g)) {k : ℕ} {W : Scheme.{0}} (y : Sx (Sp E a) k W)
    (y₀ : a₁.D.obj Γ(W, ⊤))
    (h0 : φ.d.app _ y₀ = ((show ComposableArrows (Ob a Γ(W, ⊤)) k from y.2).obj 0).pt) :
    ∃ x : Sx (Sp E a₁) k W, Sx.map (Sp.map E φ) x = y := by
  classical
  set c : ComposableArrows (Ob a Γ(W, ⊤)) k := y.2 with hc
  have hl : ∀ j : Fin (k + 1), ∃ o : Ob a₁ Γ(W, ⊤), (φ.fn Γ(W, ⊤)).obj o = c.obj j := by
    intro j
    have hle : (0 : Fin (k + 1)) ≤ j := Fin.zero_le _
    obtain ⟨u, hu⟩ := c.map (homOfLE hle)
    obtain ⟨g, hg⟩ := (hb Γ(W, ⊤)).2 u⁻¹
    refine ⟨⟨a₁.smul _ g y₀⟩, ?_⟩
    have e := φ.eq Γ(W, ⊤) g y₀
    have hg' : φ.g.app Γ(W, ⊤) g = u⁻¹ := hg
    have h0' : φ.d.app Γ(W, ⊤) y₀ = (c.obj 0).pt := h0
    have key : (c.obj j).pt = φ.d.app Γ(W, ⊤) (a₁.smul _ g y₀) := by
      erw [e, hg', h0', hu, ← a.mul_smul, inv_mul_cancel, a.one_smul]
    exact congrArg Ob.mk key.symm
  choose l hl' using hl
  haveI := fn_full φ hi hb Γ(W, ⊤)
  haveI := fn_faithful φ hb Γ(W, ⊤)
  obtain ⟨c', hc'⟩ := lift_comp (φ.fn Γ(W, ⊤)) c l hl'
  refine ⟨((y.1, show Sx (spc a₁) k W from c') : Sx (Sp E a₁) k W), ?_⟩
  refine (sp_map_eq φ _).trans ?_
  exact Prod.ext rfl hc'

end UpperTheory.FullyFaithfulLift

theorem UpperTheory.mayerVietoris_stackProduct_of_injective_of_locally_covered :
    ∀ (R : Type) [CommRing R] (E : Spc) {a₁ a₂ a : Act} (φ₁ : Act.Hom a₁ a) (φ₂ : Act.Hom a₂ a),
        (∀ A, Function.Injective (fun x : a₁.D.obj A => φ₁.d.app A x)) → (∀ A, Function.Injective (fun x : a₂.D.obj A => φ₂.d.app A x)) →
        (∀ A, Function.Bijective (fun g : a₁.G.obj A => φ₁.g.app A g)) → (∀ A, Function.Bijective (fun g : a₂.G.obj A => φ₂.g.app A g)) →
        (∀ (T : Scheme.{0}) (x : a.D.obj Γ(T, ⊤)), Loc T fun V g =>
          (∃ y, φ₁.d.app _ y = a.D.map g.appTop x) ∨ (∃ y, φ₂.d.app _ y = a.D.map g.appTop x)) →
        Cover2 R (Sp.map E φ₁) (Sp.map E φ₂) := by
  intro R _ E a₁ a₂ a φ₁ φ₂ i₁ i₂ b₁ b₂ hl
  refine UpperTheory.mayerVietorisCover_of_mono_of_zariskiLocal R _ _ (UpperTheory.FullyFaithfulLift.mono_sp E φ₁ i₁ b₁) (UpperTheory.FullyFaithfulLift.mono_sp E φ₂ i₂ b₂) (fun k T y => ?_)
  obtain ⟨S, hS, hP⟩ := hl T ((show ComposableArrows (Ob a Γ(T, ⊤)) k from y.2).obj 0).pt
  refine ⟨S, hS, fun W h hh => ?_⟩
  rcases hP W h hh with ⟨y₀, e⟩ | ⟨y₀, e⟩
  · exact Or.inl (UpperTheory.FullyFaithfulLift.lift_sp E φ₁ i₁ b₁ (y.res h) y₀ e)
  · exact Or.inr (UpperTheory.FullyFaithfulLift.lift_sp E φ₂ i₂ b₂ (y.res h) y₀ e)
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.AcyMiddleOfShortExact
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Bc

theorem UpperTheory.acy_middle_of_shortExact :
    ∀ (Q : Scheme.{0} → Prop) (S : ShortComplex (Shv ℤ)), S.ShortExact → Acy Q S.X₁ → Acy Q S.X₃ → Acy Q S.X₂ := by
  intro Q S hS h1 h3 P hP n hn
  obtain ⟨z, hz⟩ := GlobalTheory.T.etaleCohomology_coefficient_longExactSequence ℤ S hS
  have e := (hz (sgl ((free ℤ).obj P)) n).1
  haveI := h1 P hP n hn
  haveI := h3 P hP n hn
  refine ⟨fun y y' => ?_⟩
  have hy : ∀ u : HK ℤ (sgl ((free ℤ).obj P)) S.X₂ n, u = 0 := by
    intro u
    obtain ⟨v, hv⟩ := (e u).1 (Subsingleton.elim _ _)
    rw [← hv, Subsingleton.elim v 0, map_zero]
  rw [hy y, hy y']
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.RelativeCohomologyIsTotalModelOfImage
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut UpperTheory.Et.Prd

namespace UpperTheory.VanishingEvaluation

variable {R : Type} [CommRing R]

private noncomputable abbrev pb {E E' : Spc} (f : E ⟶ E') {K : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E') K n) :
    Cochain ((chains R).obj E) K n :=
  (Cochain.ofHom ((chains R).map f)).comp α (zero_add n)

private theorem pb_sub {E E' : Spc} (f : E ⟶ E') {K : Cx R} {n : ℤ} (α β : Cochain ((chains R).obj E') K n) :
    pb f (α - β) = pb f α - pb f β :=
  Cochain.comp_sub _ _ _ _

private theorem ev_pb {E E' : Spc} (f : E ⟶ E') {K : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E') K n)
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (R := R) (pb f α) p s h U x = ev (R := R) α p s h U (x.map f) :=
  (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R).2.2.2.1 f α p s h U x

private theorem ev_zero {E : Spc} {K : Cx R} {n : ℤ} (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0})
    (x : Sx E p U) : ev (R := R) (0 : Cochain ((chains R).obj E) K n) p s h U x = 0 :=
  ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R).1 0 0 p s h U x).2.2.1

private theorem pb_eq_zero {E E' : Spc} (f : E ⟶ E') {K : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E') K n)
    (h : ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U), ev (R := R) α p s h U (x.map f) = 0) :
    pb f α = 0 :=
  (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R).2.2.1 _ _ fun p s h' U x => by rw [ev_pb, h, ev_zero]

private theorem δ_pb {E E' : Spc} (f : E ⟶ E') {K : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E') K n) (n' : ℤ) :
    δ n n' (pb f α) = pb f (δ n n' α) := by
  by_cases h : n + 1 = n'
  · rw [δ_comp _ _ (zero_add n) 1 n' n' h (zero_add 1) h]; simp
  · simp [δ_shape _ _ h]

private theorem δ_van {E E' : Spc} (f : E ⟶ E') {K : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E') K n) (n' : ℤ)
    (h : ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U), ev (R := R) α p s h U (x.map f) = 0)
    (p : ℕ) (s : ℤ) (h' : -(p : ℤ) + n' = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (R := R) (δ n n' α) p s h' U (x.map f) = 0 := by
  rw [← ev_pb, ← δ_pb, pb_eq_zero f α h, δ_zero, ev_zero]

private theorem dbl_ext (P : Arrow Spc) {K : Cx R} {N : ℤ} (α β : Cochain ((chains R).obj (dbl P)) K N)
    (hl : ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + N = s) (U : Scheme.{0}) (z : Sx P.right p U),
      ev (R := R) α p s h U (z.map (dbl.inl P)) = ev (R := R) β p s h U (z.map (dbl.inl P)))
    (hr : ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + N = s) (U : Scheme.{0}) (z : Sx P.right p U),
      ev (R := R) α p s h U (z.map (dbl.inr P)) = ev (R := R) β p s h U (z.map (dbl.inr P))) : α = β :=
  (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R).2.2.1 α β fun p s h U w => by
    rcases (UpperTheory.doubleMappingCylinder_cochain_extension R P).1 p U w with ⟨z, rfl⟩ | ⟨z, rfl⟩
    · exact hl p s h U z
    · exact hr p s h U z

private theorem map_map {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') {p : ℕ} {U : Scheme.{0}} (x : Sx E p U) :
    (x.map f).map g = x.map (f ≫ g) := rfl

private theorem map_id {E : Spc} {p : ℕ} {U : Scheme.{0}} (x : Sx E p U) : x.map (𝟙 E) = x := rfl

private theorem van_img (P : Arrow Spc) {K : Cx R} {n : ℤ} (α : Cochain ((chains R).obj (dbl P)) K n)
    (h : ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (z : Sx P.right p U),
      ev (R := R) α p s h U (z.map (dbl.inr P)) = 0)
    (p : ℕ) (s : ℤ) (h' : -(p : ℤ) + n = s) (U : Scheme.{0}) (z : Sx P.right p U)
    (hz : (Sub.img P.hom).mem p U z) : ev (R := R) α p s h' U (z.map (dbl.inl P)) = 0 := by
  obtain ⟨y, rfl⟩ := hz
  have e : (y.map P.hom).map (dbl.inl P) = (y.map P.hom).map (dbl.inr P) := by
    rw [map_map, map_map]
    exact congrArg (fun f => Sx.map f y) (pushout.condition : P.hom ≫ pushout.inl P.hom P.hom = P.hom ≫ pushout.inr P.hom P.hom)
  rw [e]
  exact h p s h' U _

private theorem pb_fold (P : Arrow Spc) {K : Cx R} {n : ℤ} (α : Cochain ((chains R).obj P.right) K n) :
    pb (dbl.inr P) (pb (dbl.fold P) α) = α :=
  (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R).2.2.1 _ _ fun p s h U x => by
    rw [ev_pb, ev_pb, map_map, dbl.inr_fold, map_id]

private theorem comp_eq {E E' : Spc} {j : E ⟶ E'} {Z : Sub E} {K : Cx R} {m N : ℤ}
    {γ γ' : Cochain ((chains R).obj E') K N} {x : (famDC Z K m).Tot} (h : Comp j γ x) (h' : Comp j γ' x)
    (p : ℕ) (s : ℤ) (hs : -(p : ℤ) + N = s) (U : Scheme.{0}) (z : Sx E p U) :
    ev (R := R) γ p s hs U (z.map j) = ev (R := R) γ' p s hs U (z.map j) := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + m := ⟨s - m, by omega⟩
  exact (h p t hs U z).symm.trans (h' p t hs U z)

private theorem comp_zero {E E' : Spc} (j : E ⟶ E') (Z : Sub E) (K : Cx R) (m N : ℤ) :
    Comp j (0 : Cochain ((chains R).obj E') K N) (0 : (famDC Z K m).Tot) := by
  intro p s h U z
  exact (ev_zero p _ h U (z.map j)).symm

private theorem pull_inr (q : ℕ) (P : Arrow Spc) (i N : ℤ) (g : Cocycle ((chains (ZMod q)).obj (dbl P)) (res _ (tw q i)) N)
    (h : ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + N = s) (U : Scheme.{0}) (z : Sx P.right p U),
      ev (R := ZMod q) g.1 p s h U (z.map (dbl.inr P)) = 0) :
    pull _ (dbl.inr P) (tw q i) N (CohomologyClass.mk g) = 0 := by
  change CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains (ZMod q)).map (dbl.inr P))) g (zero_add N)) = 0
  have e : zcomp (Cocycle.ofHom ((chains (ZMod q)).map (dbl.inr P))) g (zero_add N) = 0 :=
    Cocycle.ext (pb_eq_zero _ _ h)
  rw [e, CohomologyClass.mk_zero]

end UpperTheory.VanishingEvaluation

open UpperTheory.VanishingEvaluation in
theorem UpperTheory.relativeCohomology_isTotalModel_of_image :
    ∀ (q : ℕ) (P : Arrow Spc) (i m n N : ℤ), n + m = N → TModel (famDC (Sub.img P.hom) (res _ (tw q i)) m) n (fun x (c : Hs q P N i) => SRel (N := N) x c.1) := by
  intro q P i m n N hN
  have C := fun n N h => UpperTheory.supportDoubleComplex_total_represents_vanishing_cochain (ZMod q) (dbl.inl P) (Sub.img P.hom) (res _ (tw q i)) m n N h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx hD
    obtain ⟨γ, hγ, hv⟩ := (UpperTheory.doubleMappingCylinder_cochain_extension (ZMod q) P).2 (res _ (tw q i)) m N x
    have h0 : δ N (N + 1) γ = 0 := by
      have hc := (C n N hN).2.2.1 γ x hγ
      rw [hD] at hc
      refine dbl_ext P _ _ (comp_eq hc (comp_zero _ _ _ _ _)) fun p s h U z => ?_
      rw [δ_van _ _ _ hv, ev_zero]
    refine ⟨⟨CohomologyClass.mk (Cocycle.mk γ (N + 1) rfl h0), ?_⟩, Cocycle.mk γ (N + 1) rfl h0, rfl, hγ, hv⟩
    exact pull_inr q P i N _ hv
  · rintro ⟨c, hc⟩
    obtain ⟨g₀, rfl⟩ := CohomologyClass.mk_surjective c
    have hc' : CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains (ZMod q)).map (dbl.inr P))) g₀ (zero_add N)) = 0 := hc
    rw [CohomologyClass.mk_eq_zero_iff] at hc'
    obtain ⟨N', hN', β, hβ⟩ := hc'
    have hβ' : δ N' N β = pb (dbl.inr P) g₀.1 := hβ
    let e : Cocycle ((chains (ZMod q)).obj (dbl P)) (res _ (tw q i)) N :=
      Cocycle.mk (δ N' N (pb (dbl.fold P) β)) (N + 1) rfl (δ_δ _ _ _ _)
    have he : CohomologyClass.mk e = 0 := by
      rw [CohomologyClass.mk_eq_zero_iff]
      exact ⟨N', hN', _, rfl⟩
    have hm : CohomologyClass.mk (g₀ - e) = CohomologyClass.mk g₀ := by
      rw [CohomologyClass.mk_sub, he, sub_zero]
    have hp : pb (dbl.inr P) (g₀ - e).1 = 0 := by
      change pb (dbl.inr P) (g₀.1 - δ N' N (pb (dbl.fold P) β)) = 0
      rw [pb_sub, ← δ_pb, pb_fold, hβ', sub_self]
    have hv : ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + N = s) (U : Scheme.{0}) (z : Sx P.right p U),
        ev (R := ZMod q) (g₀ - e).1 p s h U (z.map (dbl.inr P)) = 0 := fun p s h U z => by
      rw [← ev_pb, hp, ev_zero]
    obtain ⟨x, hd, hx⟩ := (C n N hN).1 (g₀ - e).1 (van_img P _ hv)
    refine ⟨x, hd, ?_, g₀ - e, hm, hx, hv⟩
    refine (C (n + 1) (N + 1) (by omega)).2.1 (δ N (N + 1) (g₀ - e).1) _ 0 ((C n N hN).2.2.2.2 x hd)
      (fun _ _ _ => rfl) ((C n N hN).2.2.1 _ x hx) ?_
    rw [(g₀ - e).δ_eq_zero]
    exact comp_zero _ _ _ _ _
  · rintro x c x' c' ⟨g, hg, hc, hv⟩ ⟨g', hg', hc', hv'⟩
    refine ⟨g - g', ?_, (C n N hN).2.2.2.1 _ _ _ _ hc hc', fun p s h U z => ?_⟩
    · rw [CohomologyClass.mk_sub, hg, hg']; rfl
    · have := ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).1 g.1 g'.1 p s h U (z.map (dbl.inr P))).2.1
      rw [hv, hv', sub_zero] at this
      exact this
  · rintro x c hd ⟨g, hg, hc, hv⟩
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
    have hN' : n' + m = N' := by omega
    simp only [add_sub_cancel_right]
    constructor
    · intro h0
      have hz : CohomologyClass.mk g = 0 := by rw [hg, h0]; rfl
      rw [CohomologyClass.mk_eq_zero_iff] at hz
      obtain ⟨M, hM, β, hβ⟩ := hz
      obtain rfl : M = N' := by omega
      have hβ' : δ M (M + 1) β = g.1 := hβ
      have hp : pb (dbl.inr P) g.1 = 0 := pb_eq_zero _ _ hv
      have hb : δ M (M + 1) (β - pb (dbl.fold P) (pb (dbl.inr P) β)) = g.1 := by
        rw [δ_sub, δ_pb, δ_pb, hβ', hp]
        simp
      have hp' : pb (dbl.inr P) (β - pb (dbl.fold P) (pb (dbl.inr P) β)) = 0 := by
        rw [pb_sub, pb_fold, sub_self]
      have hv' : ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + M = s) (U : Scheme.{0}) (z : Sx P.right p U),
          ev (R := ZMod q) (β - pb (dbl.fold P) (pb (dbl.inr P) β)) p s h U (z.map (dbl.inr P)) = 0 := fun p s h U z => by
        rw [← ev_pb, hp', ev_zero]
      obtain ⟨y, hy, hcy⟩ := (C n' M hN').1 _ (van_img P _ hv')
      refine ⟨y, hy, ?_⟩
      have h1 := (C n' M hN').2.2.1 _ y hcy
      rw [hb] at h1
      exact (C (n' + 1) (M + 1) (by omega)).2.1 g.1 _ x ((C n' M hN').2.2.2.2 y hy) hd h1 hc
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨β, hβ, hvβ⟩ := (UpperTheory.doubleMappingCylinder_cochain_extension (ZMod q) P).2 (res _ (tw q i)) m N' y
      have e : g.1 = δ N' (N' + 1) β :=
        dbl_ext P _ _ (comp_eq hc ((C n' N' hN').2.2.1 β y hβ)) fun p s h U z => by
          rw [hv, δ_van _ _ _ hvβ]
      apply Subtype.ext
      change c.1 = 0
      rw [← hg, CohomologyClass.mk_eq_zero_iff]
      exact ⟨N', rfl, β, e.symm⟩
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.LeafH0Holds
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

private theorem tw_q_nsmul {q : ℕ} {i : ℤ} {U : Scheme.{0}} (a : Sec (tw q i) U) : q • a = 0 := by
  have h : ((q : ℕ) : ULift.{1} (ZMod q)) = 0 := by
    apply ULift.ext
    simp
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q)), h, zero_smul]

private theorem tw_nsmul_mod {q : ℕ} {i : ℤ} {U : Scheme.{0}} (a : Sec (tw q i) U) (n : ℕ) :
    n • a = (n % q) • a := by
  conv_lhs => rw [← Nat.mod_add_div n q]
  rw [add_smul, mul_smul, tw_q_nsmul, add_zero]

private theorem mod_eq_of_nsmul_eq {q : ℕ} [NeZero q] {i : ℤ} {U : Scheme.{0}} [Nonempty U]
    (ζ : Prim q Γ(U, ⊤)) {c c' : ℕ} (h : c • twGen i ζ = c' • twGen i ζ) : c % q = c' % q := by
  have key : ∀ {c c' : ℕ}, c ≤ c' → c • twGen i ζ = c' • twGen i ζ → c % q = c' % q := by
    intro c c' hle h
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
    rw [add_nsmul] at h
    have h0 : d • twGen i ζ = 0 := by
      have h' := h.symm
      rwa [add_eq_left] at h'
    obtain ⟨k, rfl⟩ := (GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.1 U ζ d h0
    rw [Nat.add_mul_mod_self_left]
  rcases le_total c c' with hle | hle
  · exact key hle h
  · exact (key hle h.symm).symm

private theorem res_nsmul {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (k : V ⟶ U) (n : ℕ)
    (a : Sec F U) : Sec.res k (n • a) = n • Sec.res k a :=
  map_nsmul (F.obj.map k.op).hom n a

private theorem exists_prim (q : ℕ) [NeZero q] (Ω : Type) [Field Ω] [IsAlgClosed Ω] (hq : IsUnit (q : Ω)) :
    Nonempty (Prim q Ω) := by
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic q Ω)
    (Polynomial.degree_cyclotomic_pos q Ω (Nat.pos_of_ne_zero (NeZero.ne q))).ne'
  refine ⟨⟨ζ, hq, ?_⟩⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
  exact hζ

theorem UpperTheory.leafH0_holds :
    LateralTheory.E.E4.H0TwistOverClosedField := by
  intro hyp q _ Ω _ _ hq i
  obtain ⟨-, e, he, -⟩ := hyp.2.2.2.2.2.2.2.1 (ZMod q) (tw q i)
  obtain ⟨ζ0⟩ := exists_prim q Ω hq
  let ζ : Prim q Γ(Sp Ω, ⊤) :=
    Prim.map (CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv) ζ0
  have hsec : ∀ {X : Scheme.{0}} [ConnectedSpace X] (ξ : Prim q Γ(X, ⊤)) (y : Sec (tw q i) X),
      ∃ c < q, y = c • twGen i ξ := by
    intro X _ ξ y
    obtain ⟨c, rfl⟩ := UpperTheory.twisted_section_eq_nsmul_generator_of_connected q i X ξ y
    exact ⟨c % q, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne q)), tw_nsmul_mod _ c⟩
  refine ⟨?_, ?_⟩
  · have hsurj : Function.Surjective (fun k : Fin q => e (Sp Ω) ((k : ℕ) • twGen i ζ)) := by
      intro x
      obtain ⟨c, hc, hy⟩ := hsec ζ ((e (Sp Ω)).symm x)
      refine ⟨⟨c, hc⟩, ?_⟩
      show e (Sp Ω) (c • twGen i ζ) = x
      rw [← hy, AddEquiv.apply_symm_apply]
    exact Finite.of_surjective _ hsurj
  · intro X _ c
    have hcomm : ∀ s, pl q i c 0 (e (Sp Ω) s) = e X (Sec.res c s) := fun s => he c s
    have hres : Function.Bijective (Sec.res (F := tw q i) c) := by
      have ht : Sec.res c (twGen i ζ) =
          twGen i (Prim.map (CommRingCat.Hom.hom (Scheme.Hom.appTop c)) ζ) :=
        (GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.2.1 X (Sp Ω) c ζ
      constructor
      · intro s s' hss
        obtain ⟨c1, -, rfl⟩ := hsec ζ s
        obtain ⟨c2, -, rfl⟩ := hsec ζ s'
        rw [res_nsmul, res_nsmul, ht] at hss
        have hm := mod_eq_of_nsmul_eq _ hss
        rw [tw_nsmul_mod _ c1, tw_nsmul_mod _ c2, hm]
      · intro y
        obtain ⟨c1, -, rfl⟩ := hsec (Prim.map (CommRingCat.Hom.hom (Scheme.Hom.appTop c)) ζ) y
        exact ⟨c1 • twGen i ζ, by rw [res_nsmul, ht]⟩
    have hfun : (pl q i c 0 : _ → _) = (e X) ∘ Sec.res c ∘ (e (Sp Ω)).symm := by
      funext x
      simp only [Function.comp]
      rw [← hcomm, AddEquiv.apply_symm_apply]
    rw [hfun]
    exact (e X).bijective.comp (hres.comp (e (Sp Ω)).symm.bijective)
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.SupportDoubleComplexBotTotalModel
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut UpperTheory.Et.Prd

namespace UpperTheory.ConstantCochains

variable {R : Type} [CommRing R] {E : Spc} {K : Cx R}

private theorem map_id' {p : ℕ} {U : Scheme.{0}} (z : Sx E p U) : Sx.map (𝟙 E) z = z := rfl

private def cst {U : Scheme.{0}} {a b : ℤ} (e : a = b) (v : Sec (K.X a) U) : Sec (K.X b) U := e ▸ v

private theorem res_cst {V U : Scheme.{0}} (g : V ⟶ U) {a b : ℤ} (e : a = b) (v : Sec (K.X a) U) :
    Sec.res g (cst e v) = cst e (Sec.res g v) := by
  subst e; rfl

private theorem cst_fam (x : (famDC (Sub.bot E) K 0).Tot) (p : ℕ) (U : Scheme.{0}) (z : Sx E p U)
    {s t : ℤ} (e : t = s) (e' : t + 0 = s + 0) :
    (show Fam (Sub.bot E) p (K.X (s + 0)) from x p s).1 U z =
      cst e' ((show Fam (Sub.bot E) p (K.X (t + 0)) from x p t).1 U z) := by
  subst e; rfl

private theorem exists_cochain (n : ℤ) (x : (famDC (Sub.bot E) K 0).Tot) :
    ∃ γ : Cochain ((chains R).obj E) K n, Comp (𝟙 E) γ x := by
  let a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (K.X s) U :=
    fun p s _ U z => cst (add_zero s) ((x p s).1 U z)
  have ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (z : Sx E p U),
      Sec.res g (a p s h U z) = a p s h V (z.res g) := by
    intro p s h V U g z
    exact (res_cst g _ _).trans (congrArg (cst (add_zero s)) ((x p s).2.1 V U g z))
  have components : ∀ (i j : ℤ) (hij : i + n = j), ∃ φ : ((chains R).obj E).X i ⟶ K.X j,
      ∀ (p : ℕ) (hp : i = -(p : ℤ)) U z,
        Sec.map ((chainsXIso R E p).inv ≫ eqToHom (congrArg ((chains R).obj E).X hp.symm) ≫ φ)
          (freeGen R _ U z) = a p j (hp ▸ hij) U z := by
    intro i j hij
    by_cases hi : i ≤ 0
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, i = -(k : ℤ) := ⟨(-i).toNat, by omega⟩
      obtain ⟨φ, hφ⟩ := CupSpec.free_exists (R := R) _ _ (a k j hij) (ha k j hij)
      refine ⟨(chainsXIso R E k).hom ≫ φ, fun p hp U z => ?_⟩
      obtain rfl : k = p := by omega
      rw [eqToHom_refl, Category.id_comp, Iso.inv_hom_id_assoc]
      exact hφ U z
    · exact ⟨0, fun p hp => by omega⟩
  choose φ hφ using components
  let γ : Cochain ((chains R).obj E) K n := Cochain.mk φ
  have hγ : ∀ p s h U z, ev γ p s h U z = a p s h U z := by
    intro p s h U z
    have he := hφ _ _ h p rfl U z
    rw [eqToHom_refl, Category.id_comp] at he
    exact he
  refine ⟨γ, ?_⟩
  intro p s h U z
  rw [map_id', hγ]
  exact cst_fam x p U z (add_zero s) (add_zero (s + 0))

private theorem eq_zero_of_comp {N : ℤ} (γ : Cochain ((chains R).obj E) K N)
    (h : Comp (𝟙 E) γ (0 : (famDC (Sub.bot E) K 0).Tot)) : γ = 0 := by
  have hext : ∀ α β : Cochain ((chains R).obj E) K N,
      (∀ p s h U z, ev α p s h U z = ev β p s h U z) → α = β := by
    intro α β H
    ext p s hs : 1
    by_cases hp : p ≤ 0
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, p = -(k : ℤ) := ⟨(-p).toNat, by omega⟩
      rw [← cancel_epi (chainsXIso R E k).inv]
      exact CupSpec.free_ext _ _ (fun U z => H k s hs U z)
    · exact (CupSpec.isZero_chains E p (by omega)).eq_of_src _ _
  apply hext
  intro p s hs U z
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 0 := ⟨s, (add_zero s).symm⟩
  have h1 := h p t hs U z
  rw [map_id'] at h1
  rw [← h1]
  simp [ev]
  rfl

private theorem eq_of_comp {N : ℤ} (γ γ' : Cochain ((chains R).obj E) K N)
    (x : (famDC (Sub.bot E) K 0).Tot) (h : Comp (𝟙 E) γ x) (h' : Comp (𝟙 E) γ' x) : γ = γ' := by
  have h2 := (UpperTheory.supportDoubleComplex_total_represents_vanishing_cochain R (𝟙 E) (Sub.bot E) K 0 N N (add_zero N)).2.2.2.1 γ γ' x x h h'
  rw [sub_self] at h2
  exact sub_eq_zero.1 (eq_zero_of_comp _ h2)

end UpperTheory.ConstantCochains

open UpperTheory.ConstantCochains in
theorem UpperTheory.supportDoubleComplex_bot_totalModel :
    ∀ (R : Type) [CommRing R] (E : Spc) (K : Cx R) (n : ℤ), TModel (famDC (Sub.bot E) K 0) n (HRel (E := E) (K := K) (n := n)) := by
  intro R _ E K n
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have Ik := UpperTheory.supportDoubleComplex_total_represents_vanishing_cochain R (𝟙 E) (Sub.bot E) K 0 k k (add_zero k)
  have I1 := UpperTheory.supportDoubleComplex_total_represents_vanishing_cochain R (𝟙 E) (Sub.bot E) K 0 (k + 1) (k + 1) (add_zero _)
  have I2 := UpperTheory.supportDoubleComplex_total_represents_vanishing_cochain R (𝟙 E) (Sub.bot E) K 0 (k + 1 + 1) (k + 1 + 1) (add_zero _)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx hD
    obtain ⟨γ, hγ⟩ := exists_cochain (k + 1) x
    have h1 := I1.2.2.1 γ x hγ
    rw [hD] at h1
    have h0 := eq_zero_of_comp _ h1
    exact ⟨CohomologyClass.mk (Cocycle.mk γ _ rfl h0), Cocycle.mk γ _ rfl h0, rfl, hγ⟩
  · intro c
    obtain ⟨γ, rfl⟩ := CohomologyClass.mk_surjective c
    obtain ⟨x, hx, hc⟩ := I1.1 γ (fun _ _ _ _ _ hm => False.elim hm)
    refine ⟨x, hx, ?_, γ, rfl, hc⟩
    have h1 := I1.2.2.1 γ x hc
    rw [Cocycle.δ_eq_zero] at h1
    have c00 : Comp (𝟙 E) (0 : Cochain ((chains R).obj E) K (k + 1 + 1))
        (0 : (famDC (Sub.bot E) K 0).Tot) := by
      intro p s h U z
      simp [ev]
      rfl
    exact I2.2.1 0 _ 0 (I1.2.2.2.2 x hx) (fun _ _ _ => rfl) h1 c00
  · rintro x c x' c' ⟨γ, rfl, hγ⟩ ⟨γ', rfl, hγ'⟩
    exact ⟨γ - γ', CohomologyClass.mk_sub _ _, I1.2.2.2.1 _ _ _ _ hγ hγ'⟩
  · rintro x c hx ⟨γ, rfl, hγ⟩
    rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff γ k rfl, add_sub_cancel_right]
    constructor
    · rintro ⟨β, hβ⟩
      obtain ⟨y, hy, hyβ⟩ := Ik.1 β (fun _ _ _ _ _ hm => False.elim hm)
      refine ⟨y, hy, ?_⟩
      have h1 := Ik.2.2.1 β y hyβ
      rw [hβ] at h1
      exact I1.2.1 _ _ _ (Ik.2.2.2.2 y hy) hx h1 hγ
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨β, hβ⟩ := exists_cochain k y
      exact ⟨β, eq_of_comp _ _ _ (Ik.2.2.1 β y hβ) hγ⟩
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.LeafCurveOfLeafH0
section -- merged from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.CurveMayerVietorisOfDegreeZero
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

theorem UpperTheory.Cb.curve_mayer_vietoris_of_degree_zero :
    LateralTheory.E.E4.H0TwistOverClosedField → LateralTheory.E.E4.CurveCut.LeafMV := by
  intro _ _ R _ F X U V hUV n
  obtain ⟨d, hd, -⟩ := mayerVietoris R F
  have hc := LateralTheory.EtaleTrace.LSplitPf.Sch.cover2 R U V hUV
  haveI : PreservesLimitsOfShape WalkingCospan sch := by
    unfold sch; infer_instance
  have P := (isPullback_opens_inf U V).map sch
  refine ⟨(d _ _ hc n).comp (pull R P.isoPullback.inv F n), fun x => ?_⟩
  rw [(hd _ _ hc n).2.2 x]
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨pull R P.isoPullback.hom F n c, ?_⟩
    rw [AddMonoidHom.comp_apply, ← pull_comp, Iso.inv_hom_id, pull_id]
  · rintro ⟨y, rfl⟩
    exact ⟨_, rfl⟩
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsLocalGenerator
theorem UpperTheory.Reformulated.B.ExistsLocalGenerator.exists_local_generator :
    ∀ {B : Type} [inst : CommRing B] [IsDedekindDomain B] (I p : Ideal B) [hp : p.IsPrime],
      ∃ π ∈ I, ∃ s ∉ p, ∀ x ∈ I, s * x ∈ Ideal.span {π} := by
  intro B _ _ I p hp
  by_cases hI : I = ⊥
  · refine ⟨0, I.zero_mem, 1, (Ideal.ne_top_iff_one p).mp hp.ne_top, fun x hx => ?_⟩
    rw [hI, Ideal.mem_bot] at hx
    simp [hx]
  have hne : ¬ I ≤ I * p := by
    intro h
    have h1 : I * p = I * 1 := by
      rw [mul_one]
      exact le_antisymm Ideal.mul_le_left h
    have h2 : p = 1 := mul_left_cancel₀ (show I ≠ 0 from hI) h1
    exact hp.ne_top (by rw [h2, Ideal.one_eq_top])
  obtain ⟨π, hπ, hπ'⟩ := SetLike.not_le_iff_exists.mp hne
  have hle : Ideal.span {π} ≤ I := (Ideal.span_singleton_le_iff_mem I).mpr hπ
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.mpr hle
  have hJp : ¬ J ≤ p := by
    intro h
    apply hπ'
    have : π ∈ I * J := hJ ▸ Ideal.mem_span_singleton_self π
    exact Ideal.mul_mono_right h this
  obtain ⟨s, hs, hs'⟩ := SetLike.not_le_iff_exists.mp hJp
  refine ⟨π, hπ, s, hs', fun x hx => ?_⟩
  rw [hJ, mul_comm s x]
  exact Ideal.mul_mem_mul hx hs
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.DedekindSpecOpenIsAffine
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

private lemma exists_local_generator {B : Type} [CommRing B] [IsDedekindDomain B]
    (I : Ideal B) (p : Ideal B) [hp : p.IsPrime] :
    ∃ π ∈ I, ∃ s, s ∉ p ∧ ∀ x ∈ I, s * x ∈ Ideal.span {π} :=
  _root_.UpperTheory.Reformulated.B.ExistsLocalGenerator.exists_local_generator I p

theorem UpperTheory.dedekind_spec_open_isAffine :
    ∀ (B : Type) [CommRing B] [IsDedekindDomain B] (W : (Spec (CommRingCat.of B)).Opens), IsAffineOpen W := by
  intro B _ _ W
  let S : Set (PrimeSpectrum B) := ((W : Set (Spec (CommRingCat.of B)))ᶜ : Set (Spec (CommRingCat.of B)))
  have hS : IsClosed S := W.isOpen.isClosed_compl
  let I : Ideal B := PrimeSpectrum.vanishingIdeal S
  have hWc : PrimeSpectrum.zeroLocus (I : Set B) = S := by
    rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
    exact hS.closure_eq
  let D : B → (Spec (CommRingCat.of B)).Opens := fun r =>
    PrimeSpectrum.basicOpen (R := CommRingCat.of B) r
  have hbasic : ∀ r : B, IsAffineOpen (D r) := by
    intro r
    have h := (isAffineOpen_top (Spec (CommRingCat.of B))).basicOpen
      ((Scheme.ΓSpecIso (CommRingCat.of B)).inv r)
    rwa [basicOpen_eq_of_affine] at h
  have hmain : IsAffineHom W.ι := by
    refine isAffineHom_of_forall_exists_isAffineOpen _ fun x => ?_
    obtain ⟨π, hπ, s, hs, hsI⟩ := @exists_local_generator B _ _ I x.asIdeal x.isPrime
    refine ⟨D s, hs, hbasic s, ?_⟩
    have hEq : W ⊓ D s = D (s * π) := by
      ext q
      have hq : q ∈ W ↔ ¬ (I : Set B) ⊆ q.asIdeal := by
        have h1 : (I : Set B) ⊆ q.asIdeal ↔ q ∉ W := Set.ext_iff.1 hWc q
        rw [h1, not_not]
      have hDm : ∀ r : B, q ∈ D r ↔ r ∉ q.asIdeal := fun r => Iff.rfl
      change q ∈ W ∧ q ∈ D s ↔ q ∈ D (s * π)
      rw [hDm, hDm, hq]
      have hqp : q.asIdeal.IsPrime := q.isPrime
      constructor
      · rintro ⟨hIq, hsq⟩ hm
        rcases hqp.mem_or_mem hm with h | h
        · exact hsq h
        · refine hIq fun y hy => ?_
          have h2 : s * y ∈ q.asIdeal :=
            (Ideal.span_singleton_le_iff_mem q.asIdeal).2 h (hsI y hy)
          exact (hqp.mem_or_mem h2).resolve_left hsq
      · intro hm
        refine ⟨fun hsub => hm (Ideal.mul_mem_left _ _ (hsub hπ)),
          fun h => hm (Ideal.mul_mem_right _ _ h)⟩
    have h := hbasic (s * π)
    rw [← hEq] at h
    have h2 := h.preimage_of_isOpenImmersion W.ι (by simp)
    have e : W.ι ⁻¹ᵁ (W ⊓ D s) = W.ι ⁻¹ᵁ D s := by
      ext y
      exact ⟨fun hy => hy.2, fun hy => ⟨y.2, hy⟩⟩
    rwa [e] at h2
  have : IsAffine W.toScheme := isAffine_of_isAffineHom W.ι
  exact this
end

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

namespace UpperTheory.Cb.CurveInd

private theorem sp_facts (hH0 : H0TwistOverClosedField) (hH : Hyps) (q : ℕ) [NeZero q] (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    (hq : IsUnit (q : Ω)) (i : ℤ)
    (hB : ∀ (B : Type) [CommRing B] [IsDedekindDomain B] [Algebra Ω B] [Algebra.FiniteType Ω B],
      Finite (Ht q (sp B) 1 i))
    (B : Type) [CommRing B] [IsDedekindDomain B] [Algebra Ω B] [Algebra.FiniteType Ω B] :
    (∀ m : ℤ, Finite (Ht q (sp B) m i)) ∧ ∀ m : ℤ, 2 ≤ m → Subsingleton (Ht q (sp B) m i) := by
  have hH' := hH
  obtain ⟨a1, a2, a3, a4, a5, a7, a8, a9, a10, a11, b1, b2, b3, b4, b5, b7, c1, c2, c3, c4, c5, d1, d2, d3, e1, e2, e3⟩ := hH'
  have hsub : ∀ m : ℤ, 2 ≤ m → Subsingleton (Ht q (sp B) m i) := fun m hm => c2 q Ω B hq m i hm
  refine ⟨fun m => ?_, hsub⟩
  rcases lt_trichotomy m 0 with hm | rfl | hm
  · haveI : Subsingleton (Ht q (sp B) m i) := (a9 (ZMod q) (tw q i)).1 (sp B) m hm
    infer_instance
  · obtain ⟨hfin, hbij⟩ := hH0 hH q Ω hq i
    haveI := hfin
    exact Finite.of_surjective _ (hbij (Spec.map (CommRingCat.ofHom (algebraMap Ω B)))).2
  · rcases (show m = 1 ∨ 2 ≤ m by omega) with rfl | hm2
    · exact hB B
    · haveI := hsub m hm2
      infer_instance

private theorem aff_facts (hH0 : H0TwistOverClosedField) (hH : Hyps) (q : ℕ) [NeZero q] (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    (hq : IsUnit (q : Ω)) (i : ℤ)
    (hB : ∀ (B : Type) [CommRing B] [IsDedekindDomain B] [Algebra Ω B] [Algebra.FiniteType Ω B],
      Finite (Ht q (sp B) 1 i))
    {C : Scheme.{0}} (c : C ⟶ Sp Ω) (hc : IsCurve c) (U : C.Opens) (hU : IsAffineOpen U)
    {Y : Scheme.{0}} (j : Y ⟶ C) [IsOpenImmersion j] (hj : j.opensRange ≤ U) :
    (∀ m : ℤ, Finite (Ht q (sch.obj Y) m i)) ∧ ∀ m : ℤ, 2 ≤ m → Subsingleton (Ht q (sch.obj Y) m i) := by
  by_cases hne : (j.opensRange : Set C).Nonempty
  · have hUne : (U : Set C).Nonempty := hne.mono hj
    have hcur := UpperTheory.isDedekindDomain_affine_sections_of_isCurve Ω c hc
    haveI : IsDedekindDomain (Γ(C, U) : Type) := (hcur.1 U hU hUne).1
    have hWa : IsAffineOpen j.opensRange := by
      have h1 : IsAffineOpen (hU.fromSpec ⁻¹ᵁ j.opensRange) := UpperTheory.dedekind_spec_open_isAffine (Γ(C, U) : Type) _
      have h2 := h1.image_of_isOpenImmersion hU.fromSpec
      rwa [Scheme.Hom.image_preimage_eq_opensRange_inf, IsAffineOpen.opensRange_fromSpec,
        inf_eq_right.mpr hj] at h2
    haveI : IsDedekindDomain (Γ(C, j.opensRange) : Type) := (hcur.1 _ hWa hne).1
    have e : j.opensRange ≤ c ⁻¹ᵁ ⊤ := by simp
    letI : Algebra Ω (Γ(C, j.opensRange) : Type) :=
      ((c.appLE ⊤ j.opensRange e).hom.comp (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom).toAlgebra
    haveI : LocallyOfFiniteType c := by
      haveI : IsProper c := hc.2.1
      infer_instance
    haveI : Algebra.FiniteType Ω (Γ(C, j.opensRange) : Type) := by
      have hft := HasRingHomProperty.appLE @LocallyOfFiniteType c inferInstance
        ⟨⊤, isAffineOpen_top _⟩ ⟨j.opensRange, hWa⟩ e
      exact RingHom.FiniteType.comp hft (RingHom.FiniteType.of_surjective _
        (fun x => ⟨(Scheme.ΓSpecIso (CommRingCat.of Ω)).hom x, by simp⟩))
    obtain ⟨h1, h2⟩ := sp_facts hH0 hH q Ω hq i hB (Γ(C, j.opensRange) : Type)
    have iso : Y ≅ Spec (CommRingCat.of (Γ(C, j.opensRange) : Type)) := j.isoOpensRange ≪≫ hWa.isoSpec
    refine ⟨fun m => ?_, fun m hm => ?_⟩
    · haveI := h1 m
      exact Finite.of_equiv _ (CurveCut.isoH (ZMod q) (tw q i) iso m)
    · haveI := h2 m hm
      exact (CurveCut.isoH (ZMod q) (tw q i) iso m).symm.subsingleton
  · have hr : Set.range j.base = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    have iso : Y ≅ ((⊥ : C.Opens) : Scheme.{0}) := IsOpenImmersion.isoOfRangeEq j (⊥ : C.Opens).ι (by
      rw [Scheme.Opens.range_ι]
      simpa using hr)
    have hs : ∀ m : ℤ, Subsingleton (Ht q (sch.obj Y) m i) := fun m =>
      haveI := LateralTheory.E.E8.leafEmptyVanish (ZMod q) (X := C) (tw q i) m
      (CurveCut.isoH (ZMod q) (tw q i) iso m).symm.subsingleton
    refine ⟨fun m => ?_, fun m _ => hs m⟩
    haveI := hs m
    infer_instance

end UpperTheory.Cb.CurveInd

open UpperTheory.Cb.CurveInd in
theorem UpperTheory.leafCurve_of_leafH0 :
    LateralTheory.E.E4.H0TwistOverClosedField → LateralTheory.E.E4.LeafCurve := by
  intro hH0 hH q _ Ω _ _ hq i hB C c hc
  have hMV := UpperTheory.Cb.curve_mayer_vietoris_of_degree_zero hH0
  haveI : IsProper c := hc.2.1
  haveI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace c
  have key : ∀ (Y : Scheme.{0}) (j : Y ⟶ C) [IsOpenImmersion j], j.opensRange ≤ ⊤ →
      (∀ m : ℤ, Finite (Ht q (sch.obj Y) m i)) ∧ ∀ m : ℤ, 3 ≤ m → Subsingleton (Ht q (sch.obj Y) m i) := by
    refine compact_open_induction_on (P := fun W : C.Opens => ∀ (Y : Scheme.{0}) (j : Y ⟶ C) [IsOpenImmersion j],
      j.opensRange ≤ W →
      (∀ m : ℤ, Finite (Ht q (sch.obj Y) m i)) ∧ ∀ m : ℤ, 3 ≤ m → Subsingleton (Ht q (sch.obj Y) m i)) ⊤ ?_ ?_ ?_
    · simpa using (isCompact_univ : IsCompact (Set.univ : Set C))
    · intro Y j _ hj
      obtain ⟨h1, h2⟩ := aff_facts hH0 hH q Ω hq i hB c hc ⊥ (isAffineOpen_bot C) j hj
      exact ⟨h1, fun m hm => h2 m (by omega)⟩
    · intro S _ U ih Y j _ hj
      have hAB : j ⁻¹ᵁ S ⊔ j ⁻¹ᵁ (U : C.Opens) = ⊤ := by
        refine top_le_iff.mp fun y _ => ?_
        have hy : j.base y ∈ S ⊔ (U : C.Opens) := hj ⟨y, rfl⟩
        rcases (TopologicalSpace.Opens.mem_sup).mp hy with h | h
        · exact (TopologicalSpace.Opens.mem_sup).mpr (Or.inl h)
        · exact (TopologicalSpace.Opens.mem_sup).mpr (Or.inr h)
      obtain ⟨fA, sA⟩ := ih (j ⁻¹ᵁ S) ((j ⁻¹ᵁ S).ι ≫ j) (by
        rintro x ⟨a, rfl⟩
        exact a.2)
      obtain ⟨fB, sB⟩ := aff_facts hH0 hH q Ω hq i hB c hc U U.2 ((j ⁻¹ᵁ (U : C.Opens)).ι ≫ j) (by
        rintro x ⟨a, rfl⟩
        exact a.2)
      obtain ⟨fI, sI⟩ := aff_facts hH0 hH q Ω hq i hB c hc U U.2
        ((j ⁻¹ᵁ S ⊓ j ⁻¹ᵁ (U : C.Opens)).ι ≫ j) (by
        rintro x ⟨a, rfl⟩
        exact a.2.2)
      refine ⟨fun m => ?_, fun m hm => ?_⟩
      · obtain ⟨n, rfl⟩ : ∃ n : ℤ, m = n + 1 := ⟨m - 1, by ring⟩
        exact CurveCut.finite_of_mv hMV hH (ZMod q) (tw q i) Y _ _ hAB n (fI n) (fA (n + 1)) (fB (n + 1))
      · obtain ⟨n, rfl⟩ : ∃ n : ℤ, m = n + 1 := ⟨m - 1, by ring⟩
        exact CurveCut.subsingleton_of_mv hMV hH (ZMod q) (tw q i) Y _ _ hAB n (sI n (by omega))
          (sA (n + 1) hm) (sB (n + 1) (by omega))
  obtain ⟨h1, h2⟩ := key C (𝟙 C) le_top
  exact ⟨h1 1, h1 2, h2⟩
end
