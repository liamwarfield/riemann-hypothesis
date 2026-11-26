module

public import Development.EtaleCohomology.CohomologicalPurity.LeafExcIdentPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafHtpyOnePf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMayerVietorisConnectingExact

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.EtalePurityFreeCover
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

private lemma sec_map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}}
    (g : V ⟶ U) (x : Sec F U) : Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  change (φ.hom.app (op U) ≫ G.obj.map g.op).hom x = (F.obj.map g.op ≫ φ.hom.app (op V)).hom x
  rw [φ.hom.naturality]

private lemma sec_map_comp {R : Type} [CommRing R] {F G H : Shv R} (a : F ⟶ G) (b : G ⟶ H)
    {U : Scheme.{0}} (x : Sec F U) : Sec.map (a ≫ b) x = Sec.map b (Sec.map a x) := rfl

private lemma sec_map_zero {R : Type} [CommRing R] {F G : Shv R} {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (0 : F ⟶ G) x = 0 := rfl

private lemma res_univ_eq_zero {R : Type} [CommRing R] {A W : Scheme.{0}} (i : A ⟶ W) {Z : Shv R}
    (h : (free R).obj (yoneda.obj W) ⟶ Z) (h0 : (free R).map (yoneda.map i) ≫ h = 0) :
    Sec.res i (Sec.map h (freeGen R (yoneda.obj W) W (𝟙 W))) = 0 := by
  rw [sec_map_res, CupSpec.freeGen_res]
  have e : (ConcreteCategory.hom ((yoneda.obj W).map i.op)) (𝟙 W) =
      (ConcreteCategory.hom ((yoneda.map i).app (op A))) (𝟙 A) := by simp
  rw [e, ← CupSpec.freeGen_map, ← sec_map_comp, h0, sec_map_zero]

theorem UpperTheory.etale_purity_free_cover :
    LateralTheory.CohomologicalPurity.Thom.LeafFreeCov := by
  intro R _ X U V
  apply Preadditive.epi_of_cancel_zero
  intro Z g hg
  let ι := {O : X.Opens // O = U ∨ O = V}
  have hle : ∀ i : ι, i.1 ≤ U ⊔ V := by
    rintro ⟨O, rfl | rfl⟩
    · exact le_sup_left
    · exact le_sup_right
  have gz : ∀ i : ι, (free R).map (yoneda.map (X.homOfLE (hle i))) ≫ g = 0 := by
    rintro ⟨O, rfl | rfl⟩
    · have := congrArg (biprod.inl ≫ ·) hg
      simpa using this
    · have := congrArg (biprod.inr ≫ ·) hg
      simpa using this
  have cover : ∀ (O : X.Opens) (hO : O ≤ U ⊔ V) (y : (U ⊔ V : X.Opens).toScheme),
      (U ⊔ V).ι y ∈ O → ∃ z, X.homOfLE hO z = y := by
    intro O hO y hy
    have hy' : (U ⊔ V).ι y ∈ Set.range O.ι := by
      rw [Scheme.Opens.range_ι]
      exact hy
    obtain ⟨z, hz⟩ := hy'
    refine ⟨z, (U ⊔ V).ι.isOpenEmbedding.injective ?_⟩
    change (X.homOfLE hO ≫ (U ⊔ V).ι) z = _
    rw [Scheme.homOfLE_ι, hz]
  refine CupSpec.free_ext g 0 (fun T x => ?_)
  change Sec.map g (freeGen R _ T x) = 0
  let xx : T ⟶ (U ⊔ V : X.Opens).toScheme := x
  obtain ⟨hsep, -⟩ := sec_sep_glue_of_points R Z T ι (fun i => pullback x (X.homOfLE (hle i)))
    (fun i => pullback.fst x (X.homOfLE (hle i))) (fun i => inferInstance) (by
      intro t
      have hy : (U ⊔ V).ι (xx t) ∈ ((U ⊔ V : X.Opens) : Set X) := by
        rw [← Scheme.Opens.range_ι]
        exact ⟨xx t, rfl⟩
      rw [TopologicalSpace.Opens.coe_sup] at hy
      rcases hy with hU | hV
      · obtain ⟨z, hz⟩ := cover U le_sup_left (xx t) hU
        have ht : t ∈ Set.range (pullback.fst x (X.homOfLE (hle ⟨U, Or.inl rfl⟩))) := by
          rw [Scheme.Pullback.range_fst]
          exact ⟨z, hz⟩
        obtain ⟨v, hv⟩ := ht
        exact ⟨⟨U, Or.inl rfl⟩, v, hv⟩
      · obtain ⟨z, hz⟩ := cover V le_sup_right (xx t) hV
        have ht : t ∈ Set.range (pullback.fst x (X.homOfLE (hle ⟨V, Or.inr rfl⟩))) := by
          rw [Scheme.Pullback.range_fst]
          exact ⟨z, hz⟩
        obtain ⟨v, hv⟩ := ht
        exact ⟨⟨V, Or.inr rfl⟩, v, hv⟩)
  apply hsep
  intro i
  have z : Sec.map g (freeGen R (yoneda.obj (U ⊔ V : X.Opens).toScheme) i.1.toScheme (X.homOfLE (hle i))) = 0 := by
    have := res_univ_eq_zero (X.homOfLE (hle i)) g (gz i)
    rwa [sec_map_res, CupSpec.freeGen_res, show (ConcreteCategory.hom ((yoneda.obj (U ⊔ V : X.Opens).toScheme).map
      (X.homOfLE (hle i)).op)) (𝟙 _) = X.homOfLE (hle i) by simp] at this
  rw [sec_map_res, CupSpec.freeGen_res]
  have e : (ConcreteCategory.hom ((yoneda.obj (U ⊔ V : X.Opens).toScheme).map
      (pullback.fst x (X.homOfLE (hle i))).op)) x =
      (ConcreteCategory.hom ((yoneda.obj (U ⊔ V : X.Opens).toScheme).map
      (pullback.snd x (X.homOfLE (hle i))).op)) (X.homOfLE (hle i)) := by
    simp [pullback.condition]
  rw [e, ← CupSpec.freeGen_res, ← sec_map_res, z]
  exact map_zero _
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.CohomologicalPurity

namespace UpperTheory.Cb.OffDiagonalContinuation

universe u

structure Sys (J : Type) [SmallCategory J] where
  G : J → Type u
  [g : ∀ j, AddCommGroup (G j)]
  L : Type u
  [l : AddCommGroup L]
  ρ : ∀ {j k : J}, (j ⟶ k) → G j →+ G k
  ι : ∀ j, G j →+ L
  ι_ρ : ∀ {j k : J} (f : j ⟶ k) (y : G j), ι k (ρ f y) = ι j y
  ρ_comp : ∀ {j k l : J} (f : j ⟶ k) (g : k ⟶ l) (y : G j), ρ (f ≫ g) y = ρ g (ρ f y)

attribute [instance] Sys.g Sys.l

variable {J : Type} [SmallCategory J]

def Sys.prod (S T : Sys.{u} J) : Sys.{u} J where
  G j := S.G j × T.G j
  L := S.L × T.L
  ρ f := (S.ρ f).prodMap (T.ρ f)
  ι j := (S.ι j).prodMap (T.ι j)
  ι_ρ f y := Prod.ext (S.ι_ρ f y.1) (T.ι_ρ f y.2)
  ρ_comp f g y := Prod.ext (S.ρ_comp f g y.1) (T.ρ_comp f g y.2)

structure Sq {X : Scheme.{0}} (U V W P : X.Opens) : Prop where
  hW : W = U ⊔ V
  hP : P = U ⊓ V

section Sq
variable {X : Scheme.{0}} {U V W P : X.Opens}

theorem Sq.uw (c : Sq U V W P) : U ≤ W := c.hW ▸ le_sup_left
theorem Sq.vw (c : Sq U V W P) : V ≤ W := c.hW ▸ le_sup_right
theorem Sq.pu (c : Sq U V W P) : P ≤ U := c.hP ▸ inf_le_left
theorem Sq.pv (c : Sq U V W P) : P ≤ V := c.hP ▸ inf_le_right

theorem Sq.cover (c : Sq U V W P) (R : Type) [CommRing R] :
    Cover2 R (sch.map (X.homOfLE c.uw)) (sch.map (X.homOfLE c.vw)) := by
  obtain ⟨rfl, rfl⟩ := c
  exact ⟨Thom.HtpyMVPf.mono_sch _, Thom.HtpyMVPf.mono_sch _, fun _ => UpperTheory.etale_purity_free_cover R X U V⟩

theorem Sq.pb (c : Sq U V W P) : IsPullback (sch.map (X.homOfLE c.pu)) (sch.map (X.homOfLE c.pv))
    (sch.map (X.homOfLE c.uw)) (sch.map (X.homOfLE c.vw)) := by
  obtain ⟨rfl, rfl⟩ := c
  have := Thom.HtpyMVPf.sch_pres
  exact (isPullback_opens_inf_le (X := X) (le_sup_left : U ≤ U ⊔ V) (le_sup_right : V ≤ U ⊔ V)).map sch

end Sq

def res (q : ℕ) (i n : ℤ) {X : Scheme.{0}} {U W : X.Opens} (h : U ≤ W) :
    Ht q (sch.obj W) n i →+ Ht q (sch.obj U) n i := pull _ (sch.map (X.homOfLE h)) (tw q i) n

def rDiff (q : ℕ) (i n : ℤ) {X : Scheme.{0}} {U V W P : X.Opens} (c : Sq U V W P) :
    Ht q (sch.obj U) n i × Ht q (sch.obj V) n i →+ Ht q (sch.obj P) n i :=
  (res q i n c.pu).comp (AddMonoidHom.fst _ _) - (res q i n c.pv).comp (AddMonoidHom.snd _ _)

def rPair (q : ℕ) (i n : ℤ) {X : Scheme.{0}} {U V W P : X.Opens} (c : Sq U V W P) :
    Ht q (sch.obj W) n i →+ Ht q (sch.obj U) n i × Ht q (sch.obj V) n i :=
  (res q i n c.uw).prod (res q i n c.vw)

private theorem pull_hom_inv (R : Type) [CommRing R] (F : Shv R) {A B : Spc} (e : A ≅ B) (n : ℤ) (x : H R B F n) :
    pull R e.inv F n (pull R e.hom F n x) = x := by
  rw [← pull_comp, e.inv_hom_id, pull_id]

private theorem pull_inv_hom (R : Type) [CommRing R] (F : Shv R) {A B : Spc} (e : A ≅ B) (n : ℤ) (x : H R A F n) :
    pull R e.hom F n (pull R e.inv F n x) = x := by
  rw [← pull_comp, e.hom_inv_id, pull_id]

local instance {A B E : Spc} (f : A ⟶ E) (g : B ⟶ E) : HasPullback f g :=
  HasLimitsOfShape.has_limit (cospan f g)

private theorem res_fst (q : ℕ) (i n : ℤ) {X : Scheme.{0}} {U V W P : X.Opens} (c : Sq U V W P) (a : Ht q (sch.obj U) n i) :
    pull _ c.pb.isoPullback.inv (tw q i) n (res q i n c.pu a) =
      pull _ (pullback.fst (sch.map (X.homOfLE c.uw)) (sch.map (X.homOfLE c.vw))) (tw q i) n a := by
  change pull _ c.pb.isoPullback.inv (tw q i) n (pull _ (sch.map (X.homOfLE c.pu)) (tw q i) n a) = _
  rw [← pull_comp, c.pb.isoPullback_inv_fst]

private theorem res_snd (q : ℕ) (i n : ℤ) {X : Scheme.{0}} {U V W P : X.Opens} (c : Sq U V W P) (a : Ht q (sch.obj V) n i) :
    pull _ c.pb.isoPullback.inv (tw q i) n (res q i n c.pv a) =
      pull _ (pullback.snd (sch.map (X.homOfLE c.uw)) (sch.map (X.homOfLE c.vw))) (tw q i) n a := by
  change pull _ c.pb.isoPullback.inv (tw q i) n (pull _ (sch.map (X.homOfLE c.pv)) (tw q i) n a) = _
  rw [← pull_comp, c.pb.isoPullback_inv_snd]

private theorem pull_inv_inj (q : ℕ) (i n : ℤ) {A B : Spc} (e : A ≅ B) :
    Function.Injective (pull _ e.inv (tw q i) n) := fun x y h => by
  rw [← pull_inv_hom _ _ e n x, h, pull_inv_hom]

section ex
variable {q : ℕ} {i n : ℤ} {X : Scheme.{0}} {U V W P : X.Opens} (c : Sq U V W P)

private theorem ex1 {G : Type 1} [AddCommGroup G]
    (Dd : H (ZMod q) (pullback (sch.map (X.homOfLE c.uw)) (sch.map (X.homOfLE c.vw))) (tw q i) n →+ G)
    (E2 : ∀ z, Dd z = 0 ↔ ∃ a b, z =
      pull _ (pullback.fst (sch.map (X.homOfLE c.uw)) (sch.map (X.homOfLE c.vw))) (tw q i) n a -
      pull _ (pullback.snd (sch.map (X.homOfLE c.uw)) (sch.map (X.homOfLE c.vw))) (tw q i) n b) :
    Function.Exact (rDiff q i n c) (Dd.comp (pull _ c.pb.isoPullback.inv (tw q i) n)) := by
  intro y
  refine (E2 (pull _ c.pb.isoPullback.inv (tw q i) n y)).trans ⟨?_, ?_⟩
  · rintro ⟨a, b, h⟩
    refine ⟨(a, b), pull_inv_inj q i n c.pb.isoPullback ?_⟩
    have : rDiff q i n c (a, b) = res q i n c.pu a - res q i n c.pv b := rfl
    rw [this, map_sub, res_fst q i n c, res_snd q i n c, h]
  · rintro ⟨⟨a, b⟩, rfl⟩
    refine ⟨a, b, ?_⟩
    have : rDiff q i n c (a, b) = res q i n c.pu a - res q i n c.pv b := rfl
    rw [this, map_sub, res_fst q i n c, res_snd q i n c]

private theorem ex2
    (Dd : H (ZMod q) (pullback (sch.map (X.homOfLE c.uw)) (sch.map (X.homOfLE c.vw))) (tw q i) n →+
      Ht q (sch.obj W) (n + 1) i)
    (E3 : ∀ x, (pull _ (sch.map (X.homOfLE c.uw)) (tw q i) (n + 1) x = 0 ∧
      pull _ (sch.map (X.homOfLE c.vw)) (tw q i) (n + 1) x = 0) ↔ ∃ z, Dd z = x) :
    Function.Exact (Dd.comp (pull _ c.pb.isoPullback.inv (tw q i) n)) (rPair q i (n + 1) c) := by
  intro x
  refine Iff.trans Prod.mk_eq_zero ((E3 x).trans ⟨?_, ?_⟩)
  · rintro ⟨y, rfl⟩
    refine ⟨pull _ c.pb.isoPullback.hom (tw q i) n y, ?_⟩
    exact congrArg Dd (pull_hom_inv _ _ c.pb.isoPullback n y)
  · rintro ⟨y, rfl⟩
    exact ⟨_, rfl⟩

private theorem ex3
    (E1 : ∀ a b, pull _ (pullback.fst (sch.map (X.homOfLE c.uw)) (sch.map (X.homOfLE c.vw))) (tw q i) n a =
        pull _ (pullback.snd (sch.map (X.homOfLE c.uw)) (sch.map (X.homOfLE c.vw))) (tw q i) n b ↔
      ∃ x, pull _ (sch.map (X.homOfLE c.uw)) (tw q i) n x = a ∧ pull _ (sch.map (X.homOfLE c.vw)) (tw q i) n x = b) :
    Function.Exact (rPair q i n c) (rDiff q i n c) := by
  rintro ⟨a, b⟩
  have h0 : rDiff q i n c (a, b) = 0 ↔
      pull _ (pullback.fst (sch.map (X.homOfLE c.uw)) (sch.map (X.homOfLE c.vw))) (tw q i) n a =
        pull _ (pullback.snd (sch.map (X.homOfLE c.uw)) (sch.map (X.homOfLE c.vw))) (tw q i) n b := by
    rw [← res_fst q i n c, ← res_snd q i n c]
    have : rDiff q i n c (a, b) = res q i n c.pu a - res q i n c.pv b := rfl
    rw [this, sub_eq_zero]
    exact ⟨fun h => congrArg _ h, fun h => pull_inv_inj q i n c.pb.isoPullback h⟩
  refine h0.trans ((E1 a b).trans ⟨?_, ?_⟩)
  · rintro ⟨x, h1, h2⟩
    exact ⟨x, Prod.ext h1 h2⟩
  · rintro ⟨x, h⟩
    exact ⟨x, congrArg Prod.fst h, congrArg Prod.snd h⟩

end ex

private theorem pb_sq {X' X : Scheme.{0}} (f : X' ⟶ X) {U' V' W' P' : X'.Opens} {U V W P : X.Opens}
    (c' : Sq U' V' W' P') (c : Sq U V W P) (hU : U' ≤ f ⁻¹ᵁ U) (hV : V' ≤ f ⁻¹ᵁ V) (hW : W' ≤ f ⁻¹ᵁ W)
    (hP : P' ≤ f ⁻¹ᵁ P)
    (eu : sch.map (X'.homOfLE c'.uw) ≫ sch.map (f.resLE W W' hW) = sch.map (f.resLE U U' hU) ≫ sch.map (X.homOfLE c.uw))
    (ev : sch.map (X'.homOfLE c'.vw) ≫ sch.map (f.resLE W W' hW) = sch.map (f.resLE V V' hV) ≫ sch.map (X.homOfLE c.vw)) :
    c'.pb.isoPullback.hom ≫ pullback.map _ _ _ _ _ _ _ eu ev = sch.map (f.resLE P P' hP) ≫ c.pb.isoPullback.hom := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, IsPullback.isoPullback_hom_fst_assoc, Category.assoc,
      IsPullback.isoPullback_hom_fst, ← sch.map_comp, ← sch.map_comp]
    congr 1
    simp
  · rw [Category.assoc, pullback.lift_snd, IsPullback.isoPullback_hom_snd_assoc, Category.assoc,
      IsPullback.isoPullback_hom_snd, ← sch.map_comp, ← sch.map_comp]
    congr 1
    simp

private theorem nat_pull (q : ℕ) (i n : ℤ) {A A' B B' : Spc} (e : A ≅ B) (e' : A' ≅ B') (m : B' ⟶ B) (r : A' ⟶ A)
    (hs : e'.hom ≫ m = r ≫ e.hom) (x : Ht q A n i) :
    pull _ m (tw q i) n (pull _ e.inv (tw q i) n x) = pull _ e'.inv (tw q i) n (pull _ r (tw q i) n x) := by
  apply pull_inv_inj q i n e'.symm
  change pull _ e'.hom _ _ _ = pull _ e'.hom _ _ (pull _ e'.inv _ _ _)
  rw [pull_inv_hom, ← pull_comp, hs, pull_comp, pull_inv_hom]

theorem mv (q : ℕ) (i : ℤ) : ∃ d : ∀ {X : Scheme.{0}} {U V W P : X.Opens}, Sq U V W P → ∀ n : ℤ,
    Ht q (sch.obj P) n i →+ Ht q (sch.obj W) (n + 1) i,
    (∀ {X : Scheme.{0}} {U V W P : X.Opens} (c : Sq U V W P) (n : ℤ),
      Function.Exact (rDiff q i n c) (d c n) ∧ Function.Exact (d c n) (rPair q i (n + 1) c) ∧
      Function.Exact (rPair q i n c) (rDiff q i n c)) ∧
    ∀ {X' X : Scheme.{0}} (f : X' ⟶ X) {U' V' W' P' : X'.Opens} {U V W P : X.Opens} (c' : Sq U' V' W' P')
      (c : Sq U V W P) (hU : U' ≤ f ⁻¹ᵁ U) (hV : V' ≤ f ⁻¹ᵁ V) (hW : W' ≤ f ⁻¹ᵁ W) (hP : P' ≤ f ⁻¹ᵁ P) (n : ℤ)
      (x : Ht q (sch.obj P) n i),
      pull _ (sch.map (f.resLE W W' hW)) (tw q i) (n + 1) (d c n x) =
        d c' n (pull _ (sch.map (f.resLE P P' hP)) (tw q i) n x) := by
  obtain ⟨D, hex, hnat⟩ := GlobalTheory.EtC.mayerVietoris (ZMod q) (tw q i)
  refine ⟨fun {X U V W P} c n => (D (sch.map (X.homOfLE c.uw)) (sch.map (X.homOfLE c.vw)) (c.cover _) n).comp
    (pull _ c.pb.isoPullback.inv (tw q i) n), ?_, ?_⟩
  · intro X U V W P c n
    obtain ⟨E1, E2, E3⟩ := hex (sch.map (X.homOfLE c.uw)) (sch.map (X.homOfLE c.vw)) (c.cover _) n
    exact ⟨ex1 c _ E2, ex2 c _ E3, ex3 c E1⟩
  · intro X' X f U' V' W' P' U V W P c' c hU hV hW hP n x
    have eu : sch.map (X'.homOfLE c'.uw) ≫ sch.map (f.resLE W W' hW) =
        sch.map (f.resLE U U' hU) ≫ sch.map (X.homOfLE c.uw) := by
      rw [← sch.map_comp, ← sch.map_comp]; congr 1; simp
    have ev : sch.map (X'.homOfLE c'.vw) ≫ sch.map (f.resLE W W' hW) =
        sch.map (f.resLE V V' hV) ≫ sch.map (X.homOfLE c.vw) := by
      rw [← sch.map_comp, ← sch.map_comp]; congr 1; simp
    refine (hnat _ _ _ _ _ _ _ eu ev (c'.cover _) (c.cover _) n _).trans ?_
    exact congrArg (D _ _ _ n) (nat_pull q i n _ _ _ _ (pb_sq f c' c hU hV hW hP eu ev) x)

section sys
variable {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) {J : Type} [SmallCategory J]
  (D : J ⥤ CommRingCat.{0}) (s : (Functor.const J).obj (CommRingCat.of A) ⟶ D)
  (t : D ⟶ (Functor.const J).obj (CommRingCat.of B))

end sys

section final
variable {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) {J : Type} [SmallCategory J]
  (D : J ⥤ CommRingCat.{0}) (s : (Functor.const J).obj (CommRingCat.of A) ⟶ D)
  (t : D ⟶ (Functor.const J).obj (CommRingCat.of B))

end final

end UpperTheory.Cb.OffDiagonalContinuation
