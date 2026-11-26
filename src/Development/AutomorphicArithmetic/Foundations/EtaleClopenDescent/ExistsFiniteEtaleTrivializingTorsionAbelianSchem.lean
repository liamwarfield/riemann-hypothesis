module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.ClopRepFiniteEtaleOfConstantRank
public import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsClopRepOfClopRepOfRank
public import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsClopRepOfRankOfLocallyNoetherian

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.SubRepPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace UpperTheory.SubRep

variable {S T : Scheme.{0}} {A : Over S} [GrpObj A] {x : T ⟶ S} {A₁ : Over T} [GrpObj A₁]
  {φ₁ : A₁.left ⟶ A.left}

theorem pull_existsUnique (hP : IsGrpPullback A₁ A x φ₁) (T' : Over S) (t : T'.left ⟶ T)
    (ht : t ≫ x = T'.hom) (a : T' ⟶ A) :
    ∃! g : Over.mk t ⟶ A₁, g.left ≫ φ₁ = a.left := by
  have hP' := hP
  unfold IsGrpPullback at hP'
  obtain ⟨hPb, -⟩ := hP'
  have hw : a.left ≫ A.hom = t ≫ x := by rw [Over.w a, ht]
  refine ⟨Over.homMk (hPb.lift a.left t hw) (hPb.lift_snd _ _ _), hPb.lift_fst _ _ _, ?_⟩
  intro g' hg'
  apply Over.OverMorphism.ext
  apply hPb.hom_ext
  · rw [hg']
    exact (hPb.lift_fst _ _ _).symm
  · exact (Over.w g').trans (hPb.lift_snd _ _ _).symm

theorem pull_ext (hP : IsGrpPullback A₁ A x φ₁) {T' : Over T} {g g' : T' ⟶ A₁}
    (h : g.left ≫ φ₁ = g'.left ≫ φ₁) : g = g' := by
  apply Over.OverMorphism.ext
  apply hP.1.hom_ext h
  rw [Over.w g, Over.w g']

theorem pull_mul (hP : IsGrpPullback A₁ A x φ₁) (T' : Over S) (t : T'.left ⟶ T)
    (ht : t ≫ x = T'.hom) {g g' : Over.mk t ⟶ A₁} {a a' : T' ⟶ A}
    (h : g.left ≫ φ₁ = a.left) (h' : g'.left ≫ φ₁ = a'.left) :
    (g * g').left ≫ φ₁ = (a * a').left := by
  have hP' := hP
  unfold IsGrpPullback at hP'
  obtain ⟨-, hPm⟩ := hP'
  let e : Over.mk (t ≫ x) ⟶ T' := Over.homMk (𝟙 _) (by rw [Category.id_comp]; exact ht.symm)
  have key := hPm (Over.mk t) g g' (e ≫ a) (e ≫ a')
    (by rw [Over.comp_left, ← h]; exact Category.id_comp _)
    (by rw [Over.comp_left, ← h']; exact Category.id_comp _)
  rw [← MonObj.comp_mul, Over.comp_left] at key
  rw [← key]
  exact (Category.id_comp _).symm

theorem pull_one (hP : IsGrpPullback A₁ A x φ₁) (T' : Over S) (t : T'.left ⟶ T)
    (ht : t ≫ x = T'.hom) : (1 : Over.mk t ⟶ A₁).left ≫ φ₁ = (1 : T' ⟶ A).left := by
  have hP' := hP
  unfold IsGrpPullback at hP'
  obtain ⟨hPb, -⟩ := hP'
  have hw : ((1 : Over.mk t ⟶ A₁).left ≫ φ₁) ≫ A.hom = T'.hom := by
    rw [Category.assoc, hPb.w, ← Category.assoc, Over.w (1 : Over.mk t ⟶ A₁)]
    exact ht
  let c : T' ⟶ A := Over.homMk _ hw
  have hc := pull_mul hP T' t ht (g := 1) (g' := 1) (a := c) (a' := c) rfl rfl
  rw [_root_.mul_one] at hc
  have hcc : c * c = c := by
    apply Over.OverMorphism.ext
    exact hc.symm
  have h1 : c = 1 := mul_eq_left.mp hcc
  show c.left = _
  rw [h1]

theorem pull_inv (hP : IsGrpPullback A₁ A x φ₁) (T' : Over S) (t : T'.left ⟶ T)
    (ht : t ≫ x = T'.hom) {g : Over.mk t ⟶ A₁} {a : T' ⟶ A}
    (h : g.left ≫ φ₁ = a.left) : (g⁻¹).left ≫ φ₁ = (a⁻¹).left := by
  have hP' := hP
  unfold IsGrpPullback at hP'
  obtain ⟨hPb, -⟩ := hP'
  have hw : ((g⁻¹).left ≫ φ₁) ≫ A.hom = T'.hom := by
    rw [Category.assoc, hPb.w, ← Category.assoc, Over.w (g⁻¹)]
    exact ht
  let c : T' ⟶ A := Over.homMk _ hw
  have hc := pull_mul hP T' t ht (g := g) (g' := g⁻¹) (a := a) (a' := c) h rfl
  rw [_root_.mul_inv_cancel, pull_one hP T' t ht] at hc
  have hac : a * c = 1 := by
    apply Over.OverMorphism.ext
    exact hc.symm
  have h1 : c = a⁻¹ := eq_inv_of_mul_eq_one_right hac
  show c.left = _
  rw [h1]

theorem pull_pow (hP : IsGrpPullback A₁ A x φ₁) (T' : Over S) (t : T'.left ⟶ T)
    (ht : t ≫ x = T'.hom) {g : Over.mk t ⟶ A₁} {a : T' ⟶ A}
    (h : g.left ≫ φ₁ = a.left) (n : ℕ) : (g ^ n).left ≫ φ₁ = (a ^ n).left := by
  induction n with
  | zero => simpa using pull_one hP T' t ht
  | succ n ih => rw [pow_succ, pow_succ]; exact pull_mul hP T' t ht ih h

end UpperTheory.SubRep
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsLiftOfClosedSubgroupLocus
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace UpperTheory.ProductProjectionSubgroup

variable {S : Scheme.{0}}

private noncomputable def pr1 (Y G : Over S) : (Y ⊗ G).left ⟶ Y.left := pullback.fst Y.hom G.hom

private noncomputable def pr2 (Y G : Over S) : (Y ⊗ G).left ⟶ G.left := pullback.snd Y.hom G.hom

private theorem pr_cond (Y G : Over S) : pr1 Y G ≫ Y.hom = pr2 Y G ≫ G.hom := pullback.condition

private theorem pr_ext {Y G : Over S} {Z : Scheme.{0}} {f f' : Z ⟶ (Y ⊗ G).left}
    (h₁ : f ≫ pr1 Y G = f' ≫ pr1 Y G) (h₂ : f ≫ pr2 Y G = f' ≫ pr2 Y G) : f = f' :=
  pullback.hom_ext h₁ h₂

private theorem lift_comp_pr1 {Y G T : Over S} (t : T ⟶ Y) (a : T ⟶ G) :
    (lift t a).left ≫ pr1 Y G = t.left :=
  pullback.lift_fst t.left a.left (by rw [Over.w t, Over.w a])

private theorem lift_comp_pr2 {Y G T : Over S} (t : T ⟶ Y) (a : T ⟶ G) :
    (lift t a).left ≫ pr2 Y G = a.left :=
  pullback.lift_snd t.left a.left (by rw [Over.w t, Over.w a])

private noncomputable abbrev subH {Y G : Over S} (U : (Y ⊗ G).left.Opens) : Over Y.left :=
  Over.mk (U.ι ≫ pr1 Y G)

private theorem sub_sq {Y A G : Over S} (inc : G ⟶ A) (U : (Y ⊗ G).left.Opens) :
    (U.ι ≫ pr2 Y G ≫ inc.left) ≫ A.hom = (U.ι ≫ pr1 Y G) ≫ Y.hom := by
  simp only [Category.assoc, Over.w inc, pr_cond]

variable {Y A G : Over S} [GrpObj A] [GrpObj G] {A₀ : Over Y.left} [GrpObj A₀]
  {φ₀ : A₀.left ⟶ A.left}

private noncomputable def subJ (hP : IsGrpPullback A₀ A Y.hom φ₀) (inc : G ⟶ A)
    (U : (Y ⊗ G).left.Opens) : subH U ⟶ A₀ :=
  Over.homMk (hP.1.lift (U.ι ≫ pr2 Y G ≫ inc.left) (U.ι ≫ pr1 Y G) (sub_sq inc U))
    (hP.1.lift_snd _ _ _)

private theorem subJ_fst (hP : IsGrpPullback A₀ A Y.hom φ₀) (inc : G ⟶ A)
    (U : (Y ⊗ G).left.Opens) : (subJ hP inc U).left ≫ φ₀ = U.ι ≫ pr2 Y G ≫ inc.left :=
  hP.1.lift_fst _ _ _

private theorem subJ_snd (hP : IsGrpPullback A₀ A Y.hom φ₀) (inc : G ⟶ A)
    (U : (Y ⊗ G).left.Opens) : (subJ hP inc U).left ≫ A₀.hom = U.ι ≫ pr1 Y G :=
  hP.1.lift_snd _ _ _

private theorem subJ_mono (hP : IsGrpPullback A₀ A Y.hom φ₀) (inc : G ⟶ A) [Mono inc.left]
    (U : (Y ⊗ G).left.Opens) : Mono (subJ hP inc U) := by
  have : Mono (subJ hP inc U).left := by
    constructor
    intro Z x y e
    rw [← cancel_mono U.ι]
    apply pr_ext
    · have := congrArg (· ≫ A₀.hom) e
      simpa only [Category.assoc, subJ_snd] using this
    · rw [← cancel_mono inc.left]
      have := congrArg (· ≫ φ₀) e
      simpa only [Category.assoc, subJ_fst] using this
  exact Over.mono_of_mono_left _

private theorem subJ_iff (hP : IsGrpPullback A₀ A Y.hom φ₀) (inc : G ⟶ A)
    (U : (Y ⊗ G).left.Opens) (T' : Over S) (t : T' ⟶ Y) (g : Over.mk t.left ⟶ A₀) :
    (∃ h : Over.mk t.left ⟶ subH U, h ≫ subJ hP inc U = g) ↔
      ∃ a : T' ⟶ G, a.left ≫ inc.left = g.left ≫ φ₀ ∧ Set.range (lift t a).left ⊆ U := by
  constructor
  · rintro ⟨h, rfl⟩
    have hh : h.left ≫ U.ι ≫ pr1 Y G = t.left := Over.w h
    have e : (h.left ≫ U.ι ≫ pr2 Y G) ≫ G.hom = T'.hom := by
      have e' : (h.left ≫ U.ι ≫ pr1 Y G) ≫ Y.hom = T'.hom := by rw [hh, Over.w t]
      simpa only [Category.assoc, pr_cond] using e'
    refine ⟨Over.homMk (h.left ≫ U.ι ≫ pr2 Y G) e, ?_, ?_⟩
    · show (h.left ≫ U.ι ≫ pr2 Y G) ≫ inc.left = (h ≫ subJ hP inc U).left ≫ φ₀
      simp only [Over.comp_left, Category.assoc, subJ_fst]
    · have : (lift t (Over.homMk (h.left ≫ U.ι ≫ pr2 Y G) e)).left = h.left ≫ U.ι := by
        apply pr_ext
        · rw [lift_comp_pr1, Category.assoc, hh]
        · rw [lift_comp_pr2]
          simp only [Category.assoc, Over.homMk_left]
      rw [this]
      rintro _ ⟨x, rfl⟩
      show _ ∈ (U : Set (Y ⊗ G).left)
      rw [← U.range_ι]
      exact ⟨h.left x, by simp⟩
  · rintro ⟨a, ha, hr⟩
    have hr' : Set.range (lift t a).left ⊆ Set.range U.ι := by
      rw [U.range_ι]; exact hr
    let s := IsOpenImmersion.lift U.ι (lift t a).left hr'
    have hs : s ≫ U.ι = (lift t a).left := IsOpenImmersion.lift_fac _ _ _
    have h1 : s ≫ U.ι ≫ pr1 Y G = t.left := by
      rw [← Category.assoc, hs, lift_comp_pr1]
    refine ⟨Over.homMk s h1, ?_⟩
    apply SubRep.pull_ext hP
    show (s ≫ (subJ hP inc U).left) ≫ φ₀ = _
    rw [Category.assoc, subJ_fst, ← ha, ← Category.assoc, ← Category.assoc, hs, lift_comp_pr2]

private theorem fac_iff (hP : IsGrpPullback A₀ A Y.hom φ₀) (inc : G ⟶ A)
    (U : (Y ⊗ G).left.Opens) (K : Over Y.left) (g : K ⟶ A₀) :
    (∃ h : K ⟶ subH U, h ≫ subJ hP inc U = g) ↔
      ∃ a : Over.mk (K.hom ≫ Y.hom) ⟶ G, a.left ≫ inc.left = g.left ≫ φ₀ ∧
        Set.range (lift (Over.homMk K.hom : Over.mk (K.hom ≫ Y.hom) ⟶ Y) a).left ⊆ U :=
  subJ_iff hP inc U (Over.mk (K.hom ≫ Y.hom)) (Over.homMk K.hom) g

private theorem fac_one (hP : IsGrpPullback A₀ A Y.hom φ₀) (inc : G ⟶ A) [IsMonHom inc]
    (U : (Y ⊗ G).left.Opens)
    (hc : ∀ (T' : Over S) (t : T' ⟶ Y), Set.range (lift t (1 : T' ⟶ G)).left ⊆ U ∧
      ∀ a b : T' ⟶ G, Set.range (lift t a).left ⊆ U → Set.range (lift t b).left ⊆ U →
        Set.range (lift t (a * b⁻¹)).left ⊆ U) (K : Over Y.left) :
    ∃ h : K ⟶ subH U, h ≫ subJ hP inc U = 1 := by
  refine (fac_iff hP inc U K 1).2 ⟨1, ?_, (hc _ _).1⟩
  have e := SubRep.pull_one hP (Over.mk (K.hom ≫ Y.hom)) K.hom rfl
  refine Eq.trans ?_ e.symm
  show ((1 : Over.mk (K.hom ≫ Y.hom) ⟶ G) ≫ inc).left = _
  rw [one_comp]

private theorem fac_sub (hP : IsGrpPullback A₀ A Y.hom φ₀) (inc : G ⟶ A) [IsMonHom inc]
    (U : (Y ⊗ G).left.Opens)
    (hc : ∀ (T' : Over S) (t : T' ⟶ Y), Set.range (lift t (1 : T' ⟶ G)).left ⊆ U ∧
      ∀ a b : T' ⟶ G, Set.range (lift t a).left ⊆ U → Set.range (lift t b).left ⊆ U →
        Set.range (lift t (a * b⁻¹)).left ⊆ U) (K : Over Y.left) (g g' : K ⟶ A₀)
    (h : ∃ h : K ⟶ subH U, h ≫ subJ hP inc U = g)
    (h' : ∃ h : K ⟶ subH U, h ≫ subJ hP inc U = g') :
    ∃ h : K ⟶ subH U, h ≫ subJ hP inc U = g * g'⁻¹ := by
  obtain ⟨a, ea, ra⟩ := (fac_iff hP inc U K g).1 h
  obtain ⟨b, eb, rb⟩ := (fac_iff hP inc U K g').1 h'
  refine (fac_iff hP inc U K _).2 ⟨a * b⁻¹, ?_, (hc _ _).2 a b ra rb⟩
  have i2 := SubRep.pull_inv hP (Over.mk (K.hom ≫ Y.hom)) K.hom rfl (g := g') (a := b ≫ inc) eb.symm
  have m := SubRep.pull_mul hP (Over.mk (K.hom ≫ Y.hom)) K.hom rfl (g := g) (a := a ≫ inc)
    (a' := (b ≫ inc)⁻¹) ea.symm i2
  refine Eq.trans ?_ m.symm
  show ((a * b⁻¹) ≫ inc).left = _
  have hi : b⁻¹ ≫ inc = (b ≫ inc)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← mul_comp, inv_mul_cancel, one_comp])
  rw [mul_comp, hi]

private theorem fac_inv (hP : IsGrpPullback A₀ A Y.hom φ₀) (inc : G ⟶ A) [IsMonHom inc]
    (U : (Y ⊗ G).left.Opens)
    (hc : ∀ (T' : Over S) (t : T' ⟶ Y), Set.range (lift t (1 : T' ⟶ G)).left ⊆ U ∧
      ∀ a b : T' ⟶ G, Set.range (lift t a).left ⊆ U → Set.range (lift t b).left ⊆ U →
        Set.range (lift t (a * b⁻¹)).left ⊆ U) (K : Over Y.left) (g : K ⟶ A₀)
    (h : ∃ h : K ⟶ subH U, h ≫ subJ hP inc U = g) :
    ∃ h : K ⟶ subH U, h ≫ subJ hP inc U = g⁻¹ := by
  have := fac_sub hP inc U hc K 1 g (fac_one hP inc U hc K) h
  rwa [_root_.one_mul] at this

private theorem fac_mul (hP : IsGrpPullback A₀ A Y.hom φ₀) (inc : G ⟶ A) [IsMonHom inc]
    (U : (Y ⊗ G).left.Opens)
    (hc : ∀ (T' : Over S) (t : T' ⟶ Y), Set.range (lift t (1 : T' ⟶ G)).left ⊆ U ∧
      ∀ a b : T' ⟶ G, Set.range (lift t a).left ⊆ U → Set.range (lift t b).left ⊆ U →
        Set.range (lift t (a * b⁻¹)).left ⊆ U) (K : Over Y.left) (g g' : K ⟶ A₀)
    (h : ∃ h : K ⟶ subH U, h ≫ subJ hP inc U = g)
    (h' : ∃ h : K ⟶ subH U, h ≫ subJ hP inc U = g') :
    ∃ h : K ⟶ subH U, h ≫ subJ hP inc U = g * g' := by
  have := fac_sub hP inc U hc K g g'⁻¹ h (fac_inv hP inc U hc K g' h')
  rwa [inv_inv] at this

end UpperTheory.ProductProjectionSubgroup

open UpperTheory.ProductProjectionSubgroup in
theorem UpperTheory.exists_lift_of_closed_subgroup_locus :
    ∀ {S : Scheme.{0}} (Y A G : Over S) [GrpObj A] [GrpObj G] (inc : G ⟶ A) [IsFinite G.hom] [Etale G.hom] (U : (Y ⊗ G).left.Opens), Mono inc → IsMonHom inc → IsClosed (U : Set (Y ⊗ G).left) → (∀ (T' : Over S) (t : T' ⟶ Y), Set.range (lift t (1 : T' ⟶ G)).left ⊆ U ∧ ∀ a b : T' ⟶ G, Set.range (lift t a).left ⊆ U → Set.range (lift t b).left ⊆ U → Set.range (lift t (a * b⁻¹)).left ⊆ U) → ∀ (A₀ : Over Y.left) [GrpObj A₀] (φ₀ : A₀.left ⟶ A.left), IsGrpPullback A₀ A Y.hom φ₀ → ∃ (H : Over Y.left) (_ : GrpObj H) (j : H ⟶ A₀), IsMonHom j ∧ Mono j ∧ IsFinite H.hom ∧ Etale H.hom ∧ ∀ (T' : Over S) (t : T' ⟶ Y) (g : Over.mk t.left ⟶ A₀), (∃ h : Over.mk t.left ⟶ H, h ≫ j = g) ↔ ∃ a : T' ⟶ G, a.left ≫ inc.left = g.left ≫ φ₀ ∧ Set.range (lift t a).left ⊆ U := by
  intro S Y A G _ _ inc _ _ U hm hmon hU hc A₀ _ φ₀ hP
  have hmL : Mono inc.left := Over.mono_left_of_mono inc
  have hmj := subJ_mono hP inc U
  have hcl : IsClosedImmersion U.ι := .of_isPreimmersion _ (by simpa using hU)
  have hf1 : IsFinite (pr1 Y G) := inferInstanceAs (IsFinite (pullback.fst Y.hom G.hom))
  have he1 : Etale (pr1 Y G) := inferInstanceAs (Etale (pullback.fst Y.hom G.hom))
  have hf : IsFinite (subH U).hom := inferInstanceAs (IsFinite (U.ι ≫ pr1 Y G))
  have he : Etale (subH U).hom := inferInstanceAs (Etale (U.ι ≫ pr1 Y G))
  obtain ⟨m, hm'⟩ := fac_mul hP inc U hc (subH U ⊗ subH U) (fst _ _ ≫ subJ hP inc U)
    (snd _ _ ≫ subJ hP inc U) ⟨_, rfl⟩ ⟨_, rfl⟩
  obtain ⟨e, he'⟩ := fac_one hP inc U hc (𝟙_ (Over Y.left))
  obtain ⟨v, hv⟩ := fac_inv hP inc U hc (subH U) (subJ hP inc U) ⟨𝟙 _, Category.id_comp _⟩
  obtain ⟨gH, hj⟩ := GlobalTheory.T.exists_grpObj_isMonHom_of_mono_factor Y.left A₀ (subH U) (subJ hP inc U) hmj
    ⟨m, by rw [hm', Hom.mul_def, lift_fst_comp_snd_comp]⟩
    ⟨e, by rw [he', Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]⟩
    ⟨v, by rw [hv, Hom.inv_def]⟩
  exact ⟨subH U, gH, subJ hP inc U, hj, hmj, hf, he, subJ_iff hP inc U⟩
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsClosedLocusOfTorsionAbelianScheme
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem UpperTheory.exists_closed_locus_of_torsion_abelianScheme :
    ∀ {S T : Scheme.{0}} (x : T ⟶ S) (A G : Over S) [GrpObj A] (inc : G ⟶ A) (k : ℕ), (∀ (T' : Over S) (a : T' ⟶ G), (a ≫ inc) ^ k = 1) → IsUnit (k : Γ(T, ⊤)) → ∀ (A₁ : Over T) [GrpObj A₁] (φ₁ : A₁.left ⟶ A.left) (B₁ : Over T) [GrpObj B₁] (f : A₁ ⟶ B₁), IsGrpPullback A₁ A x φ₁ → IsAbelianScheme B₁ → IsMonHom f → ∃ V : (Over.mk x ⊗ G).left.Opens, IsClosed (V : Set (Over.mk x ⊗ G).left) ∧ ∀ (T' : Over S) (t : T' ⟶ Over.mk x) (a : T' ⟶ G) (g : Over.mk t.left ⟶ A₁), g.left ≫ φ₁ = a.left ≫ inc.left → (g ≫ f = 1 ↔ Set.range (lift t a).left ⊆ V) := by
  intro S T x A G _ inc k hk hu A₁ _ φ₁ B₁ _ f hP hB hf
  have hfe := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion B₁ (hG := hB) hu
  obtain ⟨hfin, het⟩ := hfe.2
  let pr : (Over.mk x ⊗ G).left ⟶ T := (fst (Over.mk x) G).left
  have hpr : pr ≫ x = (Over.mk x ⊗ G).hom := Over.w (fst (Over.mk x) G)
  obtain ⟨τ, hτ, -⟩ := UpperTheory.SubRep.pull_existsUnique hP (Over.mk x ⊗ G) pr hpr (snd (Over.mk x) G ≫ inc)
  have hτk : τ ^ k = 1 := by
    apply UpperTheory.SubRep.pull_ext hP
    rw [UpperTheory.SubRep.pull_pow hP _ pr hpr hτ k, hk _ (snd (Over.mk x) G), UpperTheory.SubRep.pull_one hP _ pr hpr]
  have hpow : ∀ n : ℕ, (τ ≫ f) ^ n = (τ ^ n) ≫ f := by
    intro n
    induction n with
    | zero => rw [pow_zero, pow_zero, MonObj.one_comp]
    | succ n ih => rw [pow_succ, pow_succ, MonObj.mul_comp, ih]
  have hwk : (τ ≫ f) ^ k = 1 := by
    rw [hpow, hτk, MonObj.one_comp]
  obtain ⟨c, hc, -⟩ := GlobalTheory.LatticeTorsion.existsUnique_torsion B₁ k (τ ≫ f) hwk
  obtain ⟨c₀, hc₀, -⟩ := GlobalTheory.LatticeTorsion.existsUnique_torsion B₁ k (1 : Over.mk pr ⟶ B₁) (one_pow k)
  obtain ⟨V, hV, H⟩ := GlobalTheory.LevCover.clopenCond_eq c c₀
  refine ⟨V, hV, fun T' t a g hg => ?_⟩
  have hl : (lift t a).left ≫ pr = t.left := by
    change ((lift t a) ≫ fst (Over.mk x) G).left = t.left
    rw [lift_fst]
  let h : Over.mk t.left ⟶ Over.mk pr := Over.homMk (lift t a).left hl
  have hhτ : h ≫ τ = g := by
    apply UpperTheory.SubRep.pull_ext hP
    have e : (lift t a).left ≫ (snd (Over.mk x) G ≫ inc).left = a.left ≫ inc.left := by
      change (lift t a ≫ snd (Over.mk x) G ≫ inc).left = _
      rw [lift_snd_assoc]; rfl
    change (lift t a).left ≫ τ.left ≫ φ₁ = _
    rw [hτ, e, hg]
  have hgf : g ≫ f = h ≫ τ ≫ f := by rw [← hhτ, Category.assoc]
  have key : g ≫ f = 1 ↔ h ≫ c = h ≫ c₀ := by
    constructor
    · intro e
      have h1 : (h ≫ c) ≫ torsion.ι B₁ k = 1 := by
        rw [Category.assoc, hc, ← hgf, e]
      have h2 : (h ≫ c₀) ≫ torsion.ι B₁ k = 1 := by
        rw [Category.assoc, hc₀, MonObj.comp_one]
      exact (GlobalTheory.LatticeTorsion.existsUnique_torsion B₁ k (1 : Over.mk t.left ⟶ B₁) (one_pow k)).unique h1 h2
    · intro e
      rw [hgf, ← hc, ← Category.assoc, e, Category.assoc, hc₀, MonObj.comp_one]
  exact key.trans (H _ h)
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ClopenCondOfIsClosedSubgroupLocus
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

private theorem clopen_forall {S : Scheme.{0}} (X F : Over S) [IsFinite F.hom] [Etale F.hom]
    (W : (X ⊗ F).left.Opens) (hW : IsClosed (W : Set (X ⊗ F).left)) :
    GlobalTheory.LevCover.ClopenCond X (fun T h => ∀ (T' : Over S) (t : T' ⟶ T) (a : T' ⟶ F),
      Set.range (lift (t ≫ h) a).left ⊆ W) := by
  have hWo : IsOpen ((W : Set (X ⊗ F).left)ᶜ) := hW.isOpen_compl
  have hWc : IsClosed ((W : Set (X ⊗ F).left)ᶜ) := W.isOpen.isClosed_compl
  have hKc : IsClosed (pullback.fst X.hom F.hom '' (W : Set (X ⊗ F).left)ᶜ) :=
    (pullback.fst X.hom F.hom).isClosedMap _ hWc
  have hKo : IsOpen (pullback.fst X.hom F.hom '' (W : Set (X ⊗ F).left)ᶜ) :=
    (pullback.fst X.hom F.hom).isOpenMap _ hWo
  refine ⟨⟨(pullback.fst X.hom F.hom '' (W : Set (X ⊗ F).left)ᶜ)ᶜ, hKc.isOpen_compl⟩,
    hKo.isClosed_compl, ?_⟩
  intro T h
  constructor
  · intro H
    rintro _ ⟨x, rfl⟩ ⟨z, hz, hzx⟩
    obtain ⟨q, hq1, hq2⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := h.left) (g := pullback.fst X.hom F.hom) x z hzx.symm
    let T' : Over S := Over.mk (pullback.fst h.left (pullback.fst X.hom F.hom) ≫ T.hom)
    let t : T' ⟶ T := Over.homMk (pullback.fst h.left (pullback.fst X.hom F.hom)) rfl
    have ha : (pullback.snd h.left (pullback.fst X.hom F.hom) ≫ pullback.snd X.hom F.hom) ≫ F.hom
        = T'.hom := by
      simp only [T', Over.mk_hom, Category.assoc]
      rw [← pullback.condition (f := X.hom) (g := F.hom), ← Category.assoc,
        ← pullback.condition (f := h.left) (g := pullback.fst X.hom F.hom), Category.assoc, Over.w h]
    let a : T' ⟶ F :=
      Over.homMk (pullback.snd h.left (pullback.fst X.hom F.hom) ≫ pullback.snd X.hom F.hom) ha
    have hl : (lift (t ≫ h) a).left = pullback.snd h.left (pullback.fst X.hom F.hom) := by
      apply pullback.hom_ext
      · change (lift (t ≫ h) a ≫ fst X F).left = _
        rw [lift_fst]
        exact pullback.condition
      · change (lift (t ≫ h) a ≫ snd X F).left = _
        rw [lift_snd]
        rfl
    apply hz
    have hmem := H T' t a ⟨q, rfl⟩
    rw [hl, hq2] at hmem
    exact hmem
  · intro H T' t a
    rintro _ ⟨y, rfl⟩
    by_contra hy
    have e : (lift (t ≫ h) a).left ≫ pullback.fst X.hom F.hom = t.left ≫ h.left := by
      change (lift (t ≫ h) a ≫ fst X F).left = _
      rw [lift_fst]
      rfl
    apply H ⟨t.left y, rfl⟩
    refine ⟨(lift (t ≫ h) a).left y, hy, ?_⟩
    rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply]

private theorem clopen_pre {S : Scheme.{0}} {X Y : Over S} (e : X ⟶ Y) (U : Y.left.Opens)
    (hU : IsClosed (U : Set Y.left)) :
    GlobalTheory.LevCover.ClopenCond X (fun T h => Set.range (h ≫ e).left ⊆ U) := by
  refine ⟨e.left ⁻¹ᵁ U, hU.preimage e.left.continuous, ?_⟩
  intro T h
  simp only [Over.comp_left, Set.range_subset_iff, Scheme.Hom.comp_apply, Scheme.Hom.mem_preimage, SetLike.mem_coe]

theorem UpperTheory.clopenCond_of_isClosed_subgroupLocus :
    ∀ {S : Scheme.{0}} (G X : Over S) [GrpObj G] [IsFinite G.hom] [Etale G.hom] (U : (X ⊗ G).left.Opens), IsClosed (U : Set (X ⊗ G).left) → GlobalTheory.LevCover.ClopenCond X (fun T h => ∀ (T' : Over S) (t : T' ⟶ T), Set.range (lift (t ≫ h) (1 : T' ⟶ G)).left ⊆ U ∧ ∀ a b : T' ⟶ G, Set.range (lift (t ≫ h) a).left ⊆ U → Set.range (lift (t ≫ h) b).left ⊆ U → Set.range (lift (t ≫ h) (a * b⁻¹)).left ⊆ U) := by
  intro S G X _ _ _ U hU
  haveI := (GlobalTheory.LevCover.finiteEtale_tensor G G).1
  haveI := (GlobalTheory.LevCover.finiteEtale_tensor G G).2
  have hUo : IsOpen (U : Set (X ⊗ G).left) := U.isOpen
  let m1 : X ⊗ (G ⊗ G) ⟶ X ⊗ G := lift (fst _ _) (snd _ _ ≫ fst G G)
  let m2 : X ⊗ (G ⊗ G) ⟶ X ⊗ G := lift (fst _ _) (snd _ _ ≫ snd G G)
  let m3 : X ⊗ (G ⊗ G) ⟶ X ⊗ G := lift (fst _ _) (snd _ _ ≫ (fst G G * (snd G G)⁻¹))
  let Ws : Set (X ⊗ (G ⊗ G)).left :=
    (m1.left ⁻¹' U ∩ m2.left ⁻¹' U)ᶜ ∪ m3.left ⁻¹' U
  have hWo : IsOpen Ws :=
    ((hU.preimage m1.left.continuous).inter (hU.preimage m2.left.continuous)).isOpen_compl.union
      (hUo.preimage m3.left.continuous)
  have hWc : IsClosed Ws :=
    ((hUo.preimage m1.left.continuous).inter (hUo.preimage m2.left.continuous)).isClosed_compl.union
      (hU.preimage m3.left.continuous)
  have h1 := clopen_pre (lift (𝟙 X) (1 : X ⟶ G)) U hU
  have h2 := clopen_forall X (G ⊗ G) ⟨Ws, hWo⟩ hWc
  refine (h1.and h2).congr ?_
  intro T h
  have k0 : ∀ (T' : Over S) (t : T' ⟶ T),
      lift (t ≫ h) (1 : T' ⟶ G) = t ≫ h ≫ lift (𝟙 X) (1 : X ⟶ G) := by
    intro T' t
    simp [comp_lift]
  have k1 : ∀ (T' : Over S) (u : T' ⟶ X) (c : T' ⟶ G ⊗ G),
      lift u c ≫ m1 = lift u (c ≫ fst G G) := by
    intro T' u c
    simp [m1, comp_lift]
  have k2 : ∀ (T' : Over S) (u : T' ⟶ X) (c : T' ⟶ G ⊗ G),
      lift u c ≫ m2 = lift u (c ≫ snd G G) := by
    intro T' u c
    simp [m2, comp_lift]
  have k3 : ∀ (T' : Over S) (u : T' ⟶ X) (c : T' ⟶ G ⊗ G),
      lift u c ≫ m3 = lift u ((c ≫ fst G G) * (c ≫ snd G G)⁻¹) := by
    intro T' u c
    simp [m3, comp_lift, MonObj.comp_mul, GrpObj.comp_inv]
  have pt : ∀ {A B C : Over S} (f : A ⟶ B) (g : B ⟶ C) (y : A.left),
      (f ≫ g).left y = g.left (f.left y) := by
    intro A B C f g y
    rw [Over.comp_left, Scheme.Hom.comp_apply]
  constructor
  · intro H
    refine ⟨?_, ?_⟩
    · have := (H T (𝟙 T)).1
      rw [k0, Category.id_comp] at this
      exact this
    · intro T' t c
      rintro _ ⟨y, rfl⟩
      change (lift (t ≫ h) c).left y ∈ Ws
      by_cases hy : (lift (t ≫ h) c).left y ∈ m1.left ⁻¹' U ∩ m2.left ⁻¹' U
      · right
        let V : T'.left.Opens :=
          (lift (t ≫ h) c ≫ m1).left ⁻¹ᵁ U ⊓ (lift (t ≫ h) c ≫ m2).left ⁻¹ᵁ U
        have hyV : y ∈ V := by
          refine ⟨?_, ?_⟩
          · change (lift (t ≫ h) c ≫ m1).left y ∈ (U : Set _)
            rw [pt]
            exact hy.1
          · change (lift (t ≫ h) c ≫ m2).left y ∈ (U : Set _)
            rw [pt]
            exact hy.2
        have hVw : ∀ w, V.ι w ∈ V := by
          intro w
          have hw : V.ι w ∈ Set.range V.ι := ⟨w, rfl⟩
          rwa [Scheme.Opens.range_ι] at hw
        let T'' : Over S := Over.mk (V.ι ≫ T'.hom)
        let j : T'' ⟶ T' := Over.homMk V.ι rfl
        have eq1 : lift ((j ≫ t) ≫ h) (j ≫ c ≫ fst G G) = j ≫ (lift (t ≫ h) c ≫ m1) := by
          rw [k1, comp_lift, Category.assoc]
        have eq2 : lift ((j ≫ t) ≫ h) (j ≫ c ≫ snd G G) = j ≫ (lift (t ≫ h) c ≫ m2) := by
          rw [k2, comp_lift, Category.assoc]
        have eq3 : lift ((j ≫ t) ≫ h) ((j ≫ c ≫ fst G G) * (j ≫ c ≫ snd G G)⁻¹)
            = j ≫ (lift (t ≫ h) c ≫ m3) := by
          rw [k3, comp_lift, MonObj.comp_mul, GrpObj.comp_inv, Category.assoc]
        have hA := (H T'' (j ≫ t)).2 (j ≫ c ≫ fst G G) (j ≫ c ≫ snd G G)
          (by
            rw [eq1]
            rintro _ ⟨w, rfl⟩
            rw [pt]
            exact (hVw w).1)
          (by
            rw [eq2]
            rintro _ ⟨w, rfl⟩
            rw [pt]
            exact (hVw w).2)
        obtain ⟨y', hy'⟩ : y ∈ Set.range V.ι := by
          rw [Scheme.Opens.range_ι]
          exact hyV
        have := hA ⟨y', rfl⟩
        rw [eq3, pt] at this
        change m3.left ((lift (t ≫ h) c).left y) ∈ (U : Set _)
        rw [← pt, ← hy']
        exact this
      · left
        exact hy
  · rintro ⟨H1, H2⟩ T' t
    refine ⟨?_, ?_⟩
    · rw [k0]
      rintro _ ⟨y, rfl⟩
      rw [pt]
      exact H1 ⟨t.left y, rfl⟩
    · intro a b ha hb
      rintro _ ⟨y, rfl⟩
      have hz : (lift (t ≫ h) (lift a b)).left y ∈ Ws := H2 T' t (lift a b) ⟨y, rfl⟩
      have e3 := k3 T' (t ≫ h) (lift a b)
      rw [lift_fst, lift_snd] at e3
      rw [← e3, pt]
      rcases hz with hz | hz
      · exfalso
        apply hz
        refine ⟨?_, ?_⟩
        · change (m1.left ((lift (t ≫ h) (lift a b)).left y)) ∈ (U : Set _)
          rw [← pt, k1, lift_fst]
          exact ha ⟨y, rfl⟩
        · change (m2.left ((lift (t ≫ h) (lift a b)).left y)) ∈ (U : Set _)
          rw [← pt, k2, lift_snd]
          exact hb ⟨y, rfl⟩
      · exact hz
end

section -- merged from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ExistsFiniteEtaleRepresentingClopenSubschemes
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

private theorem UpperTheory.RepresentationRank.finite_etale_of_rep {S : Scheme.{0}} (G Y : Over S) (U : (Y ⊗ G).left.Opens)
    (hf : IsFinite G.hom) (he : Etale G.hom) (hr : UpperTheory.RepresentationRank.Rep G Y U) :
    IsFinite Y.hom ∧ Etale Y.hom := by
  have hfl : Flat G.hom := inferInstance
  have hlc := Scheme.Hom.isLocallyConstant_finrank G.hom
  let W : ℕ → S.Opens := fun n => ⟨G.hom.finrank ⁻¹' {n}, hlc.isOpen_fiber n⟩
  have hW : iSup W = ⊤ := by
    refine top_le_iff.mp fun s _ => ?_
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨G.hom.finrank s, rfl⟩
  have key : ∀ n, IsFinite (pullback.snd Y.hom (W n).ι) ∧ Etale (pullback.snd Y.hom (W n).ι) := by
    intro n
    obtain ⟨U', hU'⟩ := UpperTheory.exists_clopRep_pullback (W n).ι G Y U hr
    have hG' : IsFinite ((Over.pullback (W n).ι).obj G).hom :=
      inferInstanceAs (IsFinite (pullback.snd G.hom (W n).ι))
    have hG'' : Etale ((Over.pullback (W n).ι).obj G).hom :=
      inferInstanceAs (Etale (pullback.snd G.hom (W n).ι))
    refine UpperTheory.clopRep_finite_etale_of_constant_rank _ _ U' n hG' hG'' (fun s => ?_) hU'
    change (pullback.snd G.hom (W n).ι).finrank s = n
    rw [Scheme.Hom.finrank_pullback_snd]
    exact s.2
  constructor
  · have : IsZariskiLocalAtTarget @IsFinite.{0} := by
      set_option backward.isDefEq.respectTransparency.types false in exact inferInstance
    refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsFinite) W hW fun n => ?_
    have h := pullbackRestrictIsoRestrict_hom_morphismRestrict Y.hom (W n)
    have := (key n).1
    have e : Y.hom ∣_ W n = (pullbackRestrictIsoRestrict Y.hom (W n)).inv ≫ pullback.snd Y.hom (W n).ι := by
      rw [← h, Iso.inv_hom_id_assoc]
    rw [e]
    infer_instance
  · have : IsZariskiLocalAtTarget @Etale.{0} :=
      HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Etale.{0})
    refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @Etale) W hW fun n => ?_
    have h := pullbackRestrictIsoRestrict_hom_morphismRestrict Y.hom (W n)
    have := (key n).2
    have e : Y.hom ∣_ W n = (pullbackRestrictIsoRestrict Y.hom (W n)).inv ≫ pullback.snd Y.hom (W n).ι := by
      rw [← h, Iso.inv_hom_id_assoc]
    rw [e]
    infer_instance

theorem UpperTheory.Cb.exists_finite_etale_representing_clopen_subschemes :
    ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (G : Over S), IsFinite G.hom → Etale G.hom → ∃ (Y : Over S) (U : (Y ⊗ G).left.Opens), IsFinite Y.hom ∧ Etale Y.hom ∧ IsClosed (U : Set (Y ⊗ G).left) ∧ ∀ (T : Over S) (V : (T ⊗ G).left.Opens), IsClosed (V : Set (T ⊗ G).left) → ∃! y : T ⟶ Y, (y ▷ G).left ⁻¹ᵁ U = V := by
  intro S _ G hf he
  choose Y U h using UpperTheory.exists_clopRepOfRank_of_locallyNoetherian S G hf he
  obtain ⟨Y', U', hr⟩ := UpperTheory.exists_clopRep_of_clopRepOfRank G hf he Y U h
  obtain ⟨h1, h2⟩ := UpperTheory.RepresentationRank.finite_etale_of_rep G Y' U' hf he hr
  exact ⟨Y', U', h1, h2, hr.1, hr.2⟩
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace UpperTheory.SubRep

private theorem range_pre {S : Scheme.{0}} {T' Z Z' : Over S} (m : T' ⟶ Z) (r : Z ⟶ Z') (U : Z'.left.Opens) :
    Set.range m.left ⊆ (r.left ⁻¹ᵁ U : Z.left.Opens) ↔ Set.range (m ≫ r).left ⊆ U := by
  rw [Over.comp_left]
  simp only [Set.range_subset_iff]
  rfl

private theorem opens_le {S : Scheme.{0}} {X G : Over S} {O O' : (X ⊗ G).left.Opens}
    (h : ∀ (T' : Over S) (t : T' ⟶ X) (a : T' ⟶ G),
      Set.range (lift t a).left ⊆ O → Set.range (lift t a).left ⊆ O') : O ≤ O' := by
  intro x hx
  have h' := h (Over.mk (O.ι ≫ (X ⊗ G).hom)) (Over.homMk O.ι ≫ fst X G) (Over.homMk O.ι ≫ snd X G)
  rw [lift_comp_fst_snd] at h'
  exact h' (by exact (Scheme.Opens.range_ι O).le) (by exact (Scheme.Opens.range_ι O).ge hx)

private theorem opens_ext {S : Scheme.{0}} {X G : Over S} {O O' : (X ⊗ G).left.Opens}
    (h : ∀ (T' : Over S) (t : T' ⟶ X) (a : T' ⟶ G),
      Set.range (lift t a).left ⊆ O ↔ Set.range (lift t a).left ⊆ O') : O = O' :=
  le_antisymm (opens_le fun T' t a => (h T' t a).1) (opens_le fun T' t a => (h T' t a).2)

private theorem core {S : Scheme.{0}} [IsLocallyNoetherian S] (A G : Over S) [GrpObj A] [IsCommMonObj A]
    [GrpObj G] (inc : G ⟶ A) (hm : Mono inc) (hh : IsMonHom inc) [IsFinite G.hom] [Etale G.hom] (k : ℕ)
    (hu : IsUnit (k : Γ(S, ⊤)))
    (htor : ∀ (T' : Over S) (a : T' ⟶ A), a ^ k = 1 → ∃ b : T' ⟶ G, b ≫ inc = a)
    (hk : ∀ (T' : Over S) (b : T' ⟶ G), (b ≫ inc) ^ k = 1) :
    ∃ (Y : Over S), IsFinite Y.hom ∧ Etale Y.hom ∧ ∀ (A₀ : Over Y.left) [GrpObj A₀] [IsCommMonObj A₀] (φ₀ : A₀.left ⟶ A.left), IsGrpPullback A₀ A Y.hom φ₀ → ∃ (H : Over Y.left) (_ : GrpObj H) (i : H ⟶ A₀), IsMonHom i ∧ Mono i ∧ IsFinite H.hom ∧ Etale H.hom ∧ i ^ k = 1 ∧ ∀ (T : Scheme.{0}) (x : T ⟶ S) (A₁ : Over T) [GrpObj A₁] [IsCommMonObj A₁] (φ₁ : A₁.left ⟶ A.left) (B₁ : Over T) [GrpObj B₁] (f : A₁ ⟶ B₁), IsGrpPullback A₁ A x φ₁ → IsAbelianScheme B₁ → IsMonHom f → (∀ (T' : Over T) (g : T' ⟶ A₁), g ≫ f = 1 → g ^ k = 1) → ∃! y : T ⟶ Y.left, y ≫ Y.hom = x ∧ ∀ (T' : Over T) (g : T' ⟶ A₁), g ≫ f = 1 ↔ ∃ h : T'.left ⟶ H.left, h ≫ H.hom = T'.hom ≫ y ∧ h ≫ i.left ≫ φ₀ = g.left ≫ φ₁ := by
  haveI := hm
  haveI := hh
  obtain ⟨Y₀, U, hY₀f, hY₀e, hU, hrep⟩ := UpperTheory.Cb.exists_finite_etale_representing_clopen_subschemes S G inferInstance inferInstance
  obtain ⟨U₁, hU₁, hP⟩ := UpperTheory.clopenCond_of_isClosed_subgroupLocus G Y₀ U hU
  haveI := hY₀f
  haveI := hY₀e
  obtain ⟨Y, i₀, hYf, hYe, hi₀, hsub⟩ := GlobalTheory.LevCover.exists_sub U₁ hU₁
  haveI := hi₀
  obtain ⟨U₂, hU₂def⟩ : ∃ U₂ : (Y ⊗ G).left.Opens, U₂ = (i₀ ▷ G).left ⁻¹ᵁ U := ⟨_, rfl⟩
  have hU₂ : IsClosed (U₂ : Set (Y ⊗ G).left) := by
    rw [hU₂def]
    exact IsClosed.preimage (i₀ ▷ G).left.continuous hU
  have hlift : ∀ {T' : Over S} (t : T' ⟶ Y) (a : T' ⟶ G),
      Set.range (lift t a).left ⊆ ↑U₂ ↔ Set.range (lift (t ≫ i₀) a).left ⊆ ↑U := by
    intro T' t a
    rw [hU₂def, range_pre, lift_whiskerRight]
  have hcond : ∀ (T' : Over S) (t : T' ⟶ Y),
      Set.range (lift t (1 : T' ⟶ G)).left ⊆ ↑U₂ ∧
      ∀ (a b : T' ⟶ G), Set.range (lift t a).left ⊆ ↑U₂ → Set.range (lift t b).left ⊆ ↑U₂ →
        Set.range (lift t (a * b⁻¹)).left ⊆ ↑U₂ := by
    intro T' t
    have hp := (hP T' (t ≫ i₀)).2 ((hsub T' (t ≫ i₀)).2 ⟨t, rfl⟩) T' (𝟙 T')
    simp only [Category.id_comp] at hp
    simp only [hlift]
    exact hp
  refine ⟨Y, hYf, hYe, ?_⟩
  intro A₀ _ _ φ₀ hpb
  obtain ⟨H, instH, j, hjm, hjmono, hHf, hHe, hj⟩ :=
    UpperTheory.exists_lift_of_closed_subgroup_locus Y A G inc U₂ hm hh hU₂ hcond A₀ φ₀ hpb
  obtain ⟨aj, haj1, -⟩ :=
    (hj (Over.mk (H.hom ≫ Y.hom)) (Over.homMk H.hom) j).1 ⟨𝟙 _, Category.id_comp _⟩
  have PW : ∀ (T' : Over S) (z : T' ⟶ Y) (a : T' ⟶ G), Set.range (lift z a).left ⊆ ↑U₂ ↔
      ∃ h : T'.left ⟶ H.left, h ≫ H.hom = z.left ∧ h ≫ j.left ≫ φ₀ = a.left ≫ inc.left := by
    intro T' z a
    obtain ⟨gA, hgA, -⟩ := UpperTheory.SubRep.pull_existsUnique hpb T' z.left (Over.w z) (a ≫ inc)
    rw [Over.comp_left] at hgA
    have H1 := hj T' z gA
    constructor
    · intro hr
      obtain ⟨hh', hhj⟩ := H1.2 ⟨a, hgA.symm, hr⟩
      refine ⟨hh'.left, Over.w hh', ?_⟩
      rw [← hgA, ← hhj, Over.comp_left, Category.assoc]
    · rintro ⟨h, hH, hφ⟩
      obtain ⟨a', ha', hr⟩ := H1.1 ⟨Over.homMk h hH, UpperTheory.SubRep.pull_ext hpb
        (by
          rw [Over.comp_left]
          show (h ≫ j.left) ≫ φ₀ = gA.left ≫ φ₀
          rw [Category.assoc, hφ, hgA])⟩
      have e : a' = a := by
        have e' : a' ≫ inc = a ≫ inc := by
          ext
          rw [Over.comp_left, Over.comp_left, ha', hgA]
        exact (cancel_mono inc).1 e'
      rw [← e]
      exact hr
  refine ⟨H, instH, j, hjm, hjmono, hHf, hHe, ?_, ?_⟩
  · apply UpperTheory.SubRep.pull_ext hpb
    have e1 := UpperTheory.SubRep.pull_pow hpb (Over.mk (H.hom ≫ Y.hom)) H.hom rfl (g := j)
      (a := aj ≫ inc) (by rw [Over.comp_left, haj1]) k
    have e2 := UpperTheory.SubRep.pull_one hpb (Over.mk (H.hom ≫ Y.hom)) H.hom rfl
    refine e1.trans ?_
    rw [hk]
    exact e2.symm
  · intro T x A₁ _ _ φ₁ B₁ _ f hpb1 hB hf hker
    haveI := hf
    have huT : IsUnit ((k : ℕ) : Γ(T, ⊤)) := by
      have h2 := hu.map (Scheme.Hom.appTop x).hom
      rwa [map_natCast] at h2
    obtain ⟨V, hV, hVp⟩ := UpperTheory.exists_closed_locus_of_torsion_abelianScheme x A G inc k hk huT A₁ φ₁ B₁ f hpb1 hB hf
    obtain ⟨y₀, hy₀, hy₀u⟩ := hrep (Over.mk x) V hV
    have PW2 : ∀ (y₁' : Over.mk x ⟶ Y) (T' : Over S) (t : T' ⟶ Over.mk x) (a : T' ⟶ G),
        Set.range (lift t a).left ⊆ ↑(((y₁' ≫ i₀) ▷ G).left ⁻¹ᵁ U) ↔
          ∃ h : T'.left ⟶ H.left, h ≫ H.hom = t.left ≫ y₁'.left ∧
            h ≫ j.left ≫ φ₀ = a.left ≫ inc.left := by
      intro y₁' T' t a
      rw [range_pre, lift_whiskerRight, ← Category.assoc, ← hlift, PW, Over.comp_left]
    have hwt : ∀ {T' : Over S} (t : T' ⟶ Over.mk x), t.left ≫ x = T'.hom := fun t => Over.w t
    have hyU : ∀ (T' : Over S) (t : T' ⟶ Over.mk x) (a : T' ⟶ G),
        Set.range (lift (t ≫ y₀) a).left ⊆ ↑U ↔ Set.range (lift t a).left ⊆ ↑V := by
      intro T' t a
      rw [← hy₀, range_pre, lift_whiskerRight]
    have hPy : ∀ (T' : Over S) (t : T' ⟶ Over.mk x),
        Set.range (lift (t ≫ y₀) (1 : T' ⟶ G)).left ⊆ ↑U ∧
        ∀ (a b : T' ⟶ G), Set.range (lift (t ≫ y₀) a).left ⊆ ↑U →
          Set.range (lift (t ≫ y₀) b).left ⊆ ↑U → Set.range (lift (t ≫ y₀) (a * b⁻¹)).left ⊆ ↑U := by
      intro T' t
      simp only [hyU]
      refine ⟨?_, ?_⟩
      · rw [← hVp T' t 1 1 ?_]
        · exact MonObj.one_comp f
        · rw [UpperTheory.SubRep.pull_one hpb1 T' t.left (hwt t), ← Over.comp_left, MonObj.one_comp inc]
      · intro a b ha hb
        obtain ⟨ga, hga0, -⟩ := UpperTheory.SubRep.pull_existsUnique hpb1 T' t.left (hwt t) (a ≫ inc)
        obtain ⟨gb, hgb0, -⟩ := UpperTheory.SubRep.pull_existsUnique hpb1 T' t.left (hwt t) (b ≫ inc)
        have hga : ga.left ≫ φ₁ = a.left ≫ inc.left := by rw [hga0, Over.comp_left]
        have hgb : gb.left ≫ φ₁ = b.left ≫ inc.left := by rw [hgb0, Over.comp_left]
        have hga' := (hVp T' t a ga hga).2 ha
        have hgb' := (hVp T' t b gb hgb).2 hb
        rw [← hVp T' t (a * b⁻¹) (ga * gb⁻¹) ?_]
        · rw [MonObj.mul_comp, GrpObj.inv_comp, hga', hgb', inv_one, _root_.mul_one]
        · rw [UpperTheory.SubRep.pull_mul hpb1 T' t.left (hwt t) hga0
            (UpperTheory.SubRep.pull_inv hpb1 T' t.left (hwt t) hgb0), ← Over.comp_left,
            MonObj.mul_comp, GrpObj.inv_comp]
    obtain ⟨y₁, hy₁⟩ := (hsub (Over.mk x) y₀).1 ((hP (Over.mk x) y₀).1 hPy)
    have hy₁x : y₁.left ≫ Y.hom = x := Over.w y₁
    refine ⟨y₁.left, ⟨hy₁x, ?_⟩, ?_⟩
    · intro T' g
      have hpre : ((y₁ ≫ i₀) ▷ G).left ⁻¹ᵁ U = V := by rw [hy₁, hy₀]
      have chain : ∀ a : Over.mk (T'.hom ≫ x) ⟶ G, g.left ≫ φ₁ = a.left ≫ inc.left →
          (g ≫ f = 1 ↔ ∃ h : T'.left ⟶ H.left, h ≫ H.hom = T'.hom ≫ y₁.left ∧
            h ≫ j.left ≫ φ₀ = g.left ≫ φ₁) := by
        intro a ha
        rw [ha]
        exact (hVp (Over.mk (T'.hom ≫ x)) (Over.homMk T'.hom) a g ha).trans
          (by rw [← hpre]; exact PW2 y₁ (Over.mk (T'.hom ≫ x)) (Over.homMk T'.hom) a)
      constructor
      · intro hg1
        have htk : g ^ k = 1 := hker T' g hg1
        have w : (g.left ≫ φ₁) ≫ A.hom = (Over.mk (T'.hom ≫ x)).hom := by
          rw [Category.assoc, hpb1.1.w, ← Category.assoc, Over.w g]
          rfl
        have ha₁k : (Over.homMk (g.left ≫ φ₁) w : Over.mk (T'.hom ≫ x) ⟶ A) ^ k = 1 := by
          ext
          have e1 := UpperTheory.SubRep.pull_pow hpb1 (Over.mk (T'.hom ≫ x)) T'.hom rfl (g := g)
            (a := Over.homMk (g.left ≫ φ₁) w) rfl k
          have e2 := UpperTheory.SubRep.pull_one hpb1 (Over.mk (T'.hom ≫ x)) T'.hom rfl
          refine e1.symm.trans ?_
          rw [htk]
          exact e2
        obtain ⟨b, hb⟩ := htor _ _ ha₁k
        have hb' : g.left ≫ φ₁ = b.left ≫ inc.left := by
          rw [← Over.comp_left, hb]
          rfl
        exact (chain b hb').1 hg1
      · rintro ⟨h, hH, hφ⟩
        have w : (h ≫ aj.left) ≫ G.hom = (Over.mk (T'.hom ≫ x)).hom := by
          rw [Category.assoc, Over.w aj]
          show h ≫ H.hom ≫ Y.hom = T'.hom ≫ x
          rw [← Category.assoc, hH, Category.assoc, hy₁x]
        have ha : g.left ≫ φ₁ = (Over.homMk (h ≫ aj.left) w : Over.mk (T'.hom ≫ x) ⟶ G).left ≫ inc.left := by
          rw [← hφ]
          show h ≫ j.left ≫ φ₀ = (h ≫ aj.left) ≫ inc.left
          rw [Category.assoc, haj1]
        exact (chain _ ha).2 ⟨h, hH, hφ⟩
    · rintro y' ⟨hy'x, hQ⟩
      have hpre' : ((Over.homMk y' hy'x ≫ i₀ : Over.mk x ⟶ Y₀) ▷ G).left ⁻¹ᵁ U = V := by
        apply opens_ext
        intro T' t a
        rw [PW2 (Over.homMk y' hy'x) T' t a]
        obtain ⟨ga, hga0, -⟩ := UpperTheory.SubRep.pull_existsUnique hpb1 T' t.left (hwt t) (a ≫ inc)
        have hga : ga.left ≫ φ₁ = a.left ≫ inc.left := by rw [hga0, Over.comp_left]
        rw [← hVp T' t a ga hga, hQ (Over.mk t.left) ga, hga]
        rfl
      have e1 : (Over.homMk y' hy'x : Over.mk x ⟶ Y) ≫ i₀ = y₀ := hy₀u _ hpre'
      have e2 : (Over.homMk y' hy'x : Over.mk x ⟶ Y) = y₁ := by
        rw [← cancel_mono i₀, e1, hy₁]
      rw [← e2]
      rfl

end UpperTheory.SubRep

theorem UpperTheory.Cb.exists_finite_etale_trivializing_torsion_abelianScheme :
    ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A] [IsCommMonObj A] (k : ℕ), IsAbelianScheme A → 0 < k → IsUnit (k : Γ(S, ⊤)) → ∃ (Y : Over S), IsFinite Y.hom ∧ Etale Y.hom ∧ ∀ (A₀ : Over Y.left) [GrpObj A₀] [IsCommMonObj A₀] (φ₀ : A₀.left ⟶ A.left), IsGrpPullback A₀ A Y.hom φ₀ → ∃ (H : Over Y.left) (_ : GrpObj H) (i : H ⟶ A₀), IsMonHom i ∧ Mono i ∧ IsFinite H.hom ∧ Etale H.hom ∧ i ^ k = 1 ∧ ∀ (T : Scheme.{0}) (x : T ⟶ S) (A₁ : Over T) [GrpObj A₁] [IsCommMonObj A₁] (φ₁ : A₁.left ⟶ A.left) (B₁ : Over T) [GrpObj B₁] (f : A₁ ⟶ B₁), IsGrpPullback A₁ A x φ₁ → IsAbelianScheme B₁ → IsMonHom f → (∀ (T' : Over T) (g : T' ⟶ A₁), g ≫ f = 1 → g ^ k = 1) → ∃! y : T ⟶ Y.left, y ≫ Y.hom = x ∧ ∀ (T' : Over T) (g : T' ⟶ A₁), g ≫ f = 1 ↔ ∃ h : T'.left ⟶ H.left, h ≫ H.hom = T'.hom ≫ y ∧ h ≫ i.left ≫ φ₀ = g.left ≫ φ₁ := by
  intro S _ A _ _ k hA hk0 hu
  obtain ⟨-, hfin, het⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion A hu
  have hpow : ∀ (T' : Over S) (b : T' ⟶ torsion A k), (b ≫ torsion.ι A k) ^ k = 1 := by
    intro T' b
    rw [← comp_pow, GlobalTheory.LatticeTorsion.torsionι_pow_eq_one]
    simp
  have hmono : Mono (torsion.ι A k) := by
    constructor
    intro Z g h e
    exact (GlobalTheory.LatticeTorsion.existsUnique_torsion A k (g ≫ torsion.ι A k) (hpow _ g)).unique rfl e.symm
  have hmul : ∃ m, m ≫ torsion.ι A k = (torsion.ι A k ⊗ₘ torsion.ι A k) ≫ μ := by
    refine (GlobalTheory.LatticeTorsion.existsUnique_torsion A k _ ?_).exists
    have e : (torsion.ι A k ⊗ₘ torsion.ι A k) ≫ μ
        = fst _ _ ≫ torsion.ι A k * snd _ _ ≫ torsion.ι A k := by
      rw [Hom.mul_def]
      simp
    rw [e, mul_pow, hpow, hpow]
    simp
  have hone : ∃ e, e ≫ torsion.ι A k = η := by
    refine (GlobalTheory.LatticeTorsion.existsUnique_torsion A k _ ?_).exists
    have e : (η : 𝟙_ (Over S) ⟶ A) = 1 := by
      rw [Hom.one_def]
      simp
    rw [e, one_pow]
  have hinv : ∃ v, v ≫ torsion.ι A k = torsion.ι A k ≫ ι := by
    refine (GlobalTheory.LatticeTorsion.existsUnique_torsion A k _ ?_).exists
    rw [← Hom.inv_def, inv_pow, GlobalTheory.LatticeTorsion.torsionι_pow_eq_one, inv_one]
  obtain ⟨inst, hmon⟩ := GlobalTheory.T.exists_grpObj_isMonHom_of_mono_factor S A (torsion A k) (torsion.ι A k) hmono hmul hone hinv
  haveI := hfin
  haveI := het
  exact UpperTheory.SubRep.core A (torsion A k) (torsion.ι A k) hmono hmon k hu
    (fun T' a ha => (GlobalTheory.LatticeTorsion.existsUnique_torsion A k a ha).exists)
    (fun T' b => hpow T' b)
