module

public import Development.AutomorphicArithmetic.GenericGermInjectivity.CoverGeneric
public import Development.AutomorphicArithmetic.CommutativeAlgebra.AffineLineActionFstTwistEquiv
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteEtaleFunctionFieldIntegralClosureDifferentStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SchemeCechComparisonNaturalRefinement
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CechAbPullApp
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite

universe v v' u u'

noncomputable section

namespace GlobalTheory

structure Cube.PullHom {ι κ : Type} [LinearOrder ι] {R : Type u} [Ring R] {S : Type u'} [Ring S]
    (σ : R →+* S) (τ : κ → ι) (A : Cube.{v} ι R) (B : Cube.{v'} κ S) where

  app : ∀ s : Finset κ, A.obj (s.image τ) →ₛₗ[σ] B.obj s

  app_res : ∀ {s t : Finset κ} (h : s ⊆ t) (x : A.obj (s.image τ)),
    app t (Cube.res A (Finset.image_subset_image h) x) = Cube.res B h (app s x)

namespace Cube.PullHom

variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {R : Type u} [Ring R] {S : Type u'} [Ring S]
  {σ : R →+* S} {τ : κ → ι} {A : Cube.{v} ι R} {B : Cube.{v'} κ S} (ψ : Cube.PullHom σ τ A B)

theorem card_image {p : ℕ} (t : {s : Finset κ // s.card = p}) (h : Set.InjOn τ (t.1 : Set κ)) :
    (t.1.image τ).card = p := by
  rw [Finset.card_image_of_injOn h, t.2]


open Classical in
def term (p : ℕ) : Cube.Term A p →ₛₗ[σ] Cube.Term B p where
  toFun x t := if h : Set.InjOn τ (t.1 : Set κ) then
      PD.sortSign τ t.1 • ψ.app t.1 (x ⟨t.1.image τ, card_image t h⟩) else 0
  map_add' x y := by
    funext t
    by_cases h : Set.InjOn τ (t.1 : Set κ)
    · simp only [dif_pos h, Pi.add_apply, map_add (f := _), smul_add]
    · simp only [dif_neg h, Pi.add_apply, add_zero]
  map_smul' r x := by
    funext t
    by_cases h : Set.InjOn τ (t.1 : Set κ)
    · simp only [dif_pos h, Pi.smul_apply, map_smulₛₗ, smul_comm (PD.sortSign τ t.1) (σ r)]
    · simp only [dif_neg h, Pi.smul_apply, smul_zero]

theorem term_apply_of_injOn {p : ℕ} (x : Cube.Term A p) (t : {s : Finset κ // s.card = p})
    (h : Set.InjOn τ (t.1 : Set κ)) :
    ψ.term p x t = PD.sortSign τ t.1 • ψ.app t.1 (x ⟨t.1.image τ, card_image t h⟩) := by
  unfold term
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [dif_pos h]

theorem term_apply_of_not_injOn {p : ℕ} (x : Cube.Term A p) (t : {s : Finset κ // s.card = p})
    (h : ¬ Set.InjOn τ (t.1 : Set κ)) : ψ.term p x t = 0 := by
  unfold term
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [dif_neg h]

end Cube.PullHom

section Sheaf

open SheafPull

variable {T T' : TopCat.{u}} (f : T' ⟶ T) {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {V : Opens T}
  {U : ι → Opens T} {V' : Opens T'} {U' : κ → Opens T'} (τ : κ → ι)
  (hτ : ∀ s : Finset κ, cechOpen V' U' s ≤ (Opens.map f).obj (cechOpen V U (s.image τ)))
  {F : AbSheaf T} {G : AbSheaf T'}

def cechAbPull (φ : F ⟶ (push f).obj G) :
    Cube.PullHom (RingHom.id ℤ) τ (cechAbCube F.obj V U) (cechAbCube G.obj V' U') where
  app s := (G.obj.map (homOfLE (hτ s)).op).hom.toIntLinearMap ∘ₗ
    (φ.hom.app (op (cechOpen V U (s.image τ)))).hom.toIntLinearMap
  app_res {s t} h x := by
    have e : φ.hom.app (op (cechOpen V U (t.image τ)))
        (F.obj.map (homOfLE (cechOpen_anti V U (Finset.image_subset_image (f := τ) h))).op x) =
        G.obj.map ((Opens.map f).map
          (homOfLE (cechOpen_anti V U (Finset.image_subset_image (f := τ) h)))).op
          (φ.hom.app (op (cechOpen V U (s.image τ))) x) :=
      ConcreteCategory.congr_hom (φ.hom.naturality _) x
    refine (congrArg (G.obj.map (homOfLE (hτ t)).op) e).trans ?_
    refine (ConcreteCategory.congr_hom (G.obj.map_comp _ _) _).symm.trans
      (Eq.trans ?_ (ConcreteCategory.congr_hom (G.obj.map_comp (homOfLE (hτ s)).op
        (homOfLE (cechOpen_anti V' U' h)).op) _))
    rfl

end Sheaf

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ModuleCubePullHomTermCommCechDifferential
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ModuleCubePullHomTermCommCechDifferential
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite GlobalTheory SheafPull

noncomputable section

namespace GlobalTheory.Cube.PullHom

variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {R S : Type} [Ring R] [Ring S]
  {σ : R →+* S} {τ : κ → ι} {A : Cube.{0} ι R} {B : Cube.{0} κ S} (ψ : Cube.PullHom σ τ A B)


open Classical in
def totalPull (y : ∀ s : Finset ι, A.obj s) (s : Finset κ) : B.obj s :=
  if Set.InjOn τ (s : Set κ) then PD.sortSign τ s • ψ.app s (y (s.image τ)) else 0

theorem term_eq_totalPull {p : ℕ} (x : Cube.Term A p) (s : {s : Finset κ // s.card = p}) :
    ψ.term p x s = totalPull ψ (Cube.extend A p x) s.1 := by
  by_cases h : Set.InjOn τ (s.1 : Set κ)
  · rw [term_apply_of_injOn ψ x s h, totalPull, if_pos h, Cube.extend_apply_of_eq A x (card_image s h)]
  · rw [term_apply_of_not_injOn ψ x s h, totalPull, if_neg h]

theorem totalPull_totalD (y : ∀ s : Finset ι, A.obj s) :
    totalPull ψ (Cube.totalD A y) = Cube.totalD B (totalPull ψ y) := by
  funext t
  rw [Cube.totalD_apply B]
  by_cases h : Set.InjOn τ (t : Set κ)
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [totalPull, if_pos h, Cube.totalD_apply A,
      Finset.sum_image (fun x hx y hy hxy => h hx hy hxy), map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : Set.InjOn τ ((t.erase i : Finset κ) : Set κ) :=
        h.mono (Finset.coe_subset.2 (Finset.erase_subset i t))
      rw [totalPull, if_pos hi', map_zsmul, map_zsmul, smul_smul, smul_smul,
        PD.PullMap.sign_inj h hi, ← ψ.app_res]
      congr 2
      exact Cube.res_congr A y (PD.PullMap.image_erase_of_injOn h hi) _ _
  · rw [totalPull, if_neg h]
    obtain ⟨a, ha, b, hb, he, hab⟩ : ∃ a ∈ t, ∃ b ∈ t, τ a = τ b ∧ a ≠ b := by
      by_contra hc
      push_neg at hc
      exact h (fun x hx y hy hxy => hc x hx y hy hxy)
    have zero_of : ∀ s : Finset κ, a ∈ s → b ∈ s → totalPull ψ y s = 0 := fun s has hbs => by
      rw [totalPull, if_neg]
      intro hs
      exact hab (hs has hbs he)
    rw [Finset.sum_eq_add_of_mem a b ha hb hab (fun x _ hne => by
      rw [zero_of _ (Finset.mem_erase.2 ⟨hne.1.symm, ha⟩) (Finset.mem_erase.2 ⟨hne.2.symm, hb⟩),
        map_zero, smul_zero])]
    by_cases hia : Set.InjOn τ ((t.erase a : Finset κ) : Set κ)
    · have hib := PD.PullMap.injOn_erase_swap hb hab he hia
      have key : ∀ c ∈ t, (t.erase c).image τ = t.image τ →
          Cube.res B (Finset.erase_subset c t) (ψ.app (t.erase c) (y ((t.erase c).image τ))) =
            ψ.app t (y (t.image τ)) := by
        intro c _ e
        rw [← ψ.app_res, Cube.res_congr A y e _ (subset_refl _), Cube.res_self]
      rw [totalPull, totalPull, if_pos hia, if_pos hib, map_zsmul, map_zsmul,
        key a ha (PD.PullMap.image_erase_eq hb hab he),
        key b hb (PD.PullMap.image_erase_eq ha hab.symm he.symm), smul_smul, smul_smul, ← add_smul,
        PD.PullMap.sign_pair ha hb hab he hia, neg_add_cancel, zero_smul]
    · have hib : ¬ Set.InjOn τ ((t.erase b : Finset κ) : Set κ) := fun hib =>
        hia (PD.PullMap.injOn_erase_swap ha hab.symm he.symm hib)
      rw [totalPull, totalPull, if_neg hia, if_neg hib, map_zero, map_zero, smul_zero, smul_zero,
        add_zero]

theorem term_d (p : ℕ) (x : Cube.Term A p) :
    ψ.term (p + 1) (Cube.d A p x) = Cube.d B p (ψ.term p x) := by
  funext t
  rw [Cube.d_apply_eq_totalD B (ψ.term p x) (totalPull ψ (Cube.extend A p x))
    (fun s => term_eq_totalPull ψ x s), ← totalPull_totalD]
  by_cases h : Set.InjOn τ (t.1 : Set κ)
  · rw [term_apply_of_injOn ψ _ t h, totalPull, if_pos h, Cube.d_apply_eq_totalD A x (Cube.extend A p x)
      (fun s => (Cube.extend_apply_of_eq A x s.2).symm)]
  · rw [term_apply_of_not_injOn ψ _ t h, totalPull, if_neg h]

end GlobalTheory.Cube.PullHom
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ModuleCubePullHomTermCommCechDifferentialStatement
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite GlobalTheory SheafPull
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moduleCubePullHom_term_comm_cechDifferential : ∀ {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {R S : Type} [Ring R] [Ring S]
    {σ : R →+* S} {τ : κ → ι} {A : Cube.{0} ι R} {B : Cube.{0} κ S}
    (ψ : Cube.PullHom σ τ A B) (p : ℕ) (x : Cube.Term A p),
    ψ.term (p + 1) (Cube.d A p x) = Cube.d B p (ψ.term p x) := by
  first | (exact @GlobalTheory.Cube.PullHom.term_d) | (exact GlobalTheory.Cube.PullHom.term_d) | (intros; apply GlobalTheory.Cube.PullHom.term_d  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CechComparisonDegreeZeroAlternatingPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CechComparisonDegreeZeroAlternatingPullback
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite GlobalTheory SheafPull

namespace GlobalTheory

theorem cechAbPull_degZero : ∀ {T T' : TopCat.{0}} (f : T' ⟶ T) {ι κ : Type} [LinearOrder ι] [LinearOrder κ]
    [Finite ι] [Finite κ] {V : Opens T} {U : ι → Opens T} {V' : Opens T'} {U' : κ → Opens T'}
    (τ : κ → ι) (hτ : ∀ s : Finset κ, cechOpen V' U' s ≤ (Opens.map f).obj (cechOpen V U (s.image τ)))
    (hc : V ≤ ⨆ i, U i) (hc' : V' ≤ ⨆ k, U' k) (hV : V' ≤ (Opens.map f).obj V)
    {F : AbSheaf T} {G : AbSheaf T'} (φ : F ⟶ (push f).obj G) (hF : CechAcyclic V U F)
    (hG : CechAcyclic V' U' G) (x : LinearMap.ker (Cube.d (cechAbCube F.obj V U) (0 + 1)))
    (y : LinearMap.ker (Cube.d (cechAbCube G.obj V' U') (0 + 1))),
    y.1 = (cechAbPull f τ hτ φ).term (0 + 1) x.1 →
    cechAbHEquivH' hc' hG 0 (cechClass _ 0 y) =
      SheafPull.pull f φ 0 (homOfLE hV) (cechAbHEquivH' hc hF 0 (cechClass _ 0 x)) := by
  intro T T' f ι κ _ _ _ _ V U V' U' τ hτ hc hc' hV F G φ hF hG x y hy
  obtain ⟨s, hs⟩ := (cechAbHZeroEquiv F.property hc).symm.surjective (cechClass _ 0 x)
  rw [cechAbHZeroEquiv_symm_apply] at hs
  have h1 : cechClass (cechAbCube F.obj V U) 0
      ⟨presheafCechAug (F.obj ⋙ abToIntModule) V U s,
        LinearMap.mem_ker.2 (d_presheafCechAug (F.obj ⋙ abToIntModule) V U s)⟩ =
      cechClass _ 0 x := (presheafToCechH_apply (F.obj ⋙ abToIntModule) V U s).symm.trans hs
  have hx : x.1 = presheafCechAug (F.obj ⋙ abToIntModule) V U s :=
    (congrArg Subtype.val ((cechClass_zero_bijective _).1 h1)).symm
  obtain ⟨s'', hs''⟩ : ∃ s'', s'' = G.obj.map (homOfLE hV).op (φ.hom.app (op V) s) := ⟨_, rfl⟩
  have hy' : y.1 = presheafCechAug (G.obj ⋙ abToIntModule) V' U' s'' := by
    funext t
    obtain ⟨t, ht⟩ := t
    obtain ⟨k, rfl⟩ := Finset.card_eq_one.1 ht
    rw [hy, Cube.PullHom.term_apply_of_injOn _ _ _ (by simp)]
    have hsg : PD.sortSign τ {k} = 1 := by simp [PD.sortSign]
    rw [hsg, one_smul]
    show G.obj.map (homOfLE (hτ {k})).op (φ.hom.app (op (cechOpen V U (({k} : Finset κ).image τ)))
      (x.1 ⟨({k} : Finset κ).image τ, Cube.PullHom.card_image ⟨{k}, ht⟩ (by simp)⟩)) =
      G.obj.map (homOfLE (cechOpen_le V' U' {k})).op s''
    rw [hx, hs'']
    have nat := ConcreteCategory.congr_hom
      (φ.hom.naturality (homOfLE (cechOpen_le V U (({k} : Finset κ).image τ))).op) s
    change φ.hom.app _ (F.obj.map _ s) = G.obj.map _ (φ.hom.app _ s) at nat
    change G.obj.map _ (φ.hom.app _ (F.obj.map (homOfLE (cechOpen_le V U (({k} : Finset κ).image τ))).op s)) = _
    rw [nat]
    refine (ConcreteCategory.congr_hom (G.obj.map_comp _ _) _).symm.trans
      (Eq.trans ?_ (ConcreteCategory.congr_hom (G.obj.map_comp _ _) _))
    rfl
  have h2 : cechClass _ 0 y = toCechAbH G.obj V' U' s'' :=
    (congrArg (cechClass _ 0) (Subtype.ext hy')).trans
      (presheafToCechH_apply (G.obj ⋙ abToIntModule) V' U' s'').symm
  rw [h2, ← hs, cechAbHEquivH'_toCechAbH, cechAbHEquivH'_toCechAbH]
  apply (SheafLES.equivZero G V').injective
  rw [AddEquiv.apply_symm_apply, SheafPull.equivZero_pull, AddEquiv.apply_symm_apply, hs'']

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CechComparisonDegreeZeroAlternatingPullbackStatement
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite GlobalTheory SheafPull
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechComparison_degreeZero_alternatingPullback : ∀ {T T' : TopCat.{0}} (f : T' ⟶ T) {ι κ : Type} [LinearOrder ι] [LinearOrder κ]
    [Finite ι] [Finite κ] {V : Opens T} {U : ι → Opens T} {V' : Opens T'} {U' : κ → Opens T'}
    (τ : κ → ι) (hτ : ∀ s : Finset κ, cechOpen V' U' s ≤ (Opens.map f).obj (cechOpen V U (s.image τ)))
    (hc : V ≤ ⨆ i, U i) (hc' : V' ≤ ⨆ k, U' k) (hV : V' ≤ (Opens.map f).obj V)
    {F : AbSheaf T} {G : AbSheaf T'} (φ : F ⟶ (push f).obj G) (hF : CechAcyclic V U F)
    (hG : CechAcyclic V' U' G) (x : LinearMap.ker (Cube.d (cechAbCube F.obj V U) (0 + 1)))
    (y : LinearMap.ker (Cube.d (cechAbCube G.obj V' U') (0 + 1))),
    y.1 = (cechAbPull f τ hτ φ).term (0 + 1) x.1 →
    cechAbHEquivH' hc' hG 0 (cechClass _ 0 y) =
      SheafPull.pull f φ 0 (homOfLE hV) (cechAbHEquivH' hc hF 0 (cechClass _ 0 x)) := by
  first | (exact @GlobalTheory.cechAbPull_degZero) | (exact GlobalTheory.cechAbPull_degZero) | (intros; apply GlobalTheory.cechAbPull_degZero  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SchemeCechComparisonNaturalRefinement
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite
open GlobalTheory.PD

noncomputable section

namespace GlobalTheory

open SheafPull

namespace Cube.PullHom

variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {R S : Type} [Ring R] [Ring S]
  {σ : R →+* S} {τ : κ → ι}

theorem termMap_term {A A' : Cube.{0} ι R} {B B' : Cube.{0} κ S} (ψ : Cube.PullHom σ τ A B)
    (ψ' : Cube.PullHom σ τ A' B') (α : A ⟶ A') (β : B ⟶ B')
    (h : ∀ s x, ψ'.app s ((α.app (s.image τ)).hom x) = (β.app s).hom (ψ.app s x)) (q : ℕ)
    (z : Cube.Term A q) :
    Cube.termMap β q (ψ.term q z) = ψ'.term q (Cube.termMap α q z) := by
  funext t
  by_cases hi : Set.InjOn τ (t.1 : Set κ)
  · rw [Cube.termMap_apply, ψ.term_apply_of_injOn _ _ hi, ψ'.term_apply_of_injOn _ _ hi,
      Cube.termMap_apply, map_zsmul, h]
  · rw [Cube.termMap_apply, ψ.term_apply_of_not_injOn _ _ hi, ψ'.term_apply_of_not_injOn _ _ hi,
      map_zero]

theorem term_mem_ker {A : Cube.{0} ι R} {B : Cube.{0} κ S} (ψ : Cube.PullHom σ τ A B) (p : ℕ)
    (x : LinearMap.ker (Cube.d A p)) : ψ.term p x.1 ∈ LinearMap.ker (Cube.d B p) := by
  rw [LinearMap.mem_ker, ← GlobalTheory.T.moduleCubePullHom_term_comm_cechDifferential ψ p x.1, x.2, map_zero]

theorem cechClass_eq {A : Cube.{0} ι R} {B : Cube.{0} κ S} (ψ : Cube.PullHom σ τ A B) (p : ℕ)
    (x x₂ : LinearMap.ker (Cube.d A (p + 1))) (y y₂ : LinearMap.ker (Cube.d B (p + 1)))
    (hy : y.1 = ψ.term (p + 1) x.1) (hy₂ : y₂.1 = ψ.term (p + 1) x₂.1)
    (h : cechClass A p x = cechClass A p x₂) : cechClass B p y = cechClass B p y₂ := by
  rw [← sub_eq_zero, ← map_sub] at h ⊢
  cases p with
  | zero =>
    rw [cechClass_zero_eq_zero_iff] at h ⊢
    refine Subtype.ext ?_
    rw [Submodule.coe_sub, hy, hy₂, ← map_sub, ← Submodule.coe_sub, h, Submodule.coe_zero, map_zero,
      Submodule.coe_zero]
  | succ p =>
    obtain ⟨z, hz⟩ := (cechClass_succ_eq_zero_iff A p _).1 h
    refine (cechClass_succ_eq_zero_iff B p _).2 ⟨ψ.term (p + 1) z, ?_⟩
    rw [← GlobalTheory.T.moduleCubePullHom_term_comm_cechDifferential ψ (p + 1) z, hz, Submodule.coe_sub, Submodule.coe_sub, hy, hy₂, map_sub]

theorem cechClass_δ {S₀ : ShortComplex (Cube.{0} ι R)} {S₁ : ShortComplex (Cube.{0} κ S)}
    (hS₀ : (S₀.map (cechFunctor ι R)).ShortExact) (hS₁ : (S₁.map (cechFunctor κ S)).ShortExact)
    (ψ₁ : Cube.PullHom σ τ S₀.X₁ S₁.X₁) (ψ₂ : Cube.PullHom σ τ S₀.X₂ S₁.X₂)
    (ψ₃ : Cube.PullHom σ τ S₀.X₃ S₁.X₃)
    (hf : ∀ s x, ψ₂.app s ((S₀.f.app (s.image τ)).hom x) = (S₁.f.app s).hom (ψ₁.app s x))
    (hg : ∀ s x, ψ₃.app s ((S₀.g.app (s.image τ)).hom x) = (S₁.g.app s).hom (ψ₂.app s x))
    (p : ℕ) (x₃ : LinearMap.ker (Cube.d S₀.X₃ (p + 1)))
    (y₃ : LinearMap.ker (Cube.d S₁.X₃ (p + 1))) (hy : y₃.1 = ψ₃.term (p + 1) x₃.1) :
    ∃ (x₁ : LinearMap.ker (Cube.d S₀.X₁ (p + 1 + 1)))
      (y₁ : LinearMap.ker (Cube.d S₁.X₁ (p + 1 + 1))),
      y₁.1 = ψ₁.term (p + 1 + 1) x₁.1 ∧
      (hS₀.δ p (p + 1) rfl).hom (cechClass S₀.X₃ p x₃) = cechClass S₀.X₁ (p + 1) x₁ ∧
      (hS₁.δ p (p + 1) rfl).hom (cechClass S₁.X₃ p y₃) = cechClass S₁.X₁ (p + 1) y₁ := by
  obtain ⟨x₂, x₁, h₂, h₁⟩ := exists_lift_cechCocycle hS₀ p x₃
  refine ⟨x₁, ⟨_, ψ₁.term_mem_ker _ x₁⟩, rfl, δ_cechClass hS₀ p x₃ x₂ x₁ h₂ h₁,
    δ_cechClass hS₁ p y₃ (ψ₂.term _ x₂) _ ?_ ?_⟩
  · rw [termMap_term ψ₂ ψ₃ S₀.g S₁.g hg, h₂, hy]
  · show Cube.termMap S₁.f _ (ψ₁.term _ x₁.1) = Cube.d S₁.X₂ (p + 1) (ψ₂.term (p + 1) x₂)
    rw [termMap_term ψ₁ ψ₂ S₀.f S₁.f hf, h₁, GlobalTheory.T.moduleCubePullHom_term_comm_cechDifferential]

end Cube.PullHom

theorem cechAbPull_δ {T T' : TopCat.{0}} (f : T' ⟶ T) {ι κ : Type} [LinearOrder ι] [LinearOrder κ]
    {V : Opens T} {U : ι → Opens T} {V' : Opens T'} {U' : κ → Opens T'}
    (τ : κ → ι) (hτ : ∀ s : Finset κ, cechOpen V' U' s ≤ (Opens.map f).obj (cechOpen V U (s.image τ)))
    {S₀ : ShortComplex (AbSheaf T)} {S₁ : ShortComplex (AbSheaf T')} (hS₀ : S₀.ShortExact)
    (hS₁ : S₁.ShortExact) (h₀ : CechAcyclic V U S₀.X₁) (h₁ : CechAcyclic V' U' S₁.X₁)
    (ψ : S₀ ⟶ S₁.map (push f)) (n : ℕ)
    (x₃ : LinearMap.ker (Cube.d (cechAbCube S₀.X₃.obj V U) (n + 1)))
    (y₃ : LinearMap.ker (Cube.d (cechAbCube S₁.X₃.obj V' U') (n + 1)))
    (hy : y₃.1 = (cechAbPull f τ hτ (G := S₁.X₃) ψ.τ₃).term (n + 1) x₃.1) :
    ∃ (x₁ : LinearMap.ker (Cube.d (cechAbCube S₀.X₁.obj V U) (n + 1 + 1)))
      (y₁ : LinearMap.ker (Cube.d (cechAbCube S₁.X₁.obj V' U') (n + 1 + 1))),
      y₁.1 = (cechAbPull f τ hτ (G := S₁.X₁) ψ.τ₁).term (n + 1 + 1) x₁.1 ∧
      cechAbδ hS₀ h₀ n (cechClass _ n x₃) = cechClass _ (n + 1) x₁ ∧
      cechAbδ hS₁ h₁ n (cechClass _ n y₃) = cechClass _ (n + 1) y₁ := by
  refine Cube.PullHom.cechClass_δ (S₀ := S₀.map (sheafToPresheaf _ _ ⋙ cechAbCubeFunctor V U))
    (S₁ := S₁.map (sheafToPresheaf _ _ ⋙ cechAbCubeFunctor V' U'))
    (cechAbSheafFunctor_shortExact hS₀ h₀) (cechAbSheafFunctor_shortExact hS₁ h₁)
    (cechAbPull f τ hτ ψ.τ₁) (cechAbPull f τ hτ ψ.τ₂) (cechAbPull f τ hτ ψ.τ₃)
    (fun s x => ?_) (fun s x => ?_) n x₃ y₃ hy
  · let x' : S₀.X₁.obj.obj (op (cechOpen V U (s.image τ))) := x
    have e₁ : ψ.τ₂.hom.app (op (cechOpen V U (s.image τ)))
        (S₀.f.hom.app (op (cechOpen V U (s.image τ))) x') =
        S₁.f.hom.app (op ((Opens.map f).obj (cechOpen V U (s.image τ))))
          (ψ.τ₁.hom.app (op (cechOpen V U (s.image τ))) x') :=
      ConcreteCategory.congr_hom
        (congrArg (fun g => g.hom.app (op (cechOpen V U (s.image τ)))) ψ.comm₁₂) x' |>.symm
    have e₂ := ConcreteCategory.congr_hom (S₁.f.hom.naturality (homOfLE (hτ s)).op)
      (ψ.τ₁.hom.app (op (cechOpen V U (s.image τ))) x')
    exact (congrArg (fun z => S₁.X₂.obj.map (homOfLE (hτ s)).op z) e₁).trans e₂.symm
  · let x' : S₀.X₂.obj.obj (op (cechOpen V U (s.image τ))) := x
    have e₁ : ψ.τ₃.hom.app (op (cechOpen V U (s.image τ)))
        (S₀.g.hom.app (op (cechOpen V U (s.image τ))) x') =
        S₁.g.hom.app (op ((Opens.map f).obj (cechOpen V U (s.image τ))))
          (ψ.τ₂.hom.app (op (cechOpen V U (s.image τ))) x') :=
      ConcreteCategory.congr_hom
        (congrArg (fun g => g.hom.app (op (cechOpen V U (s.image τ)))) ψ.comm₂₃) x' |>.symm
    have e₂ := ConcreteCategory.congr_hom (S₁.g.hom.naturality (homOfLE (hτ s)).op)
      (ψ.τ₂.hom.app (op (cechOpen V U (s.image τ))) x')
    exact (congrArg (fun z => S₁.X₃.obj.map (homOfLE (hτ s)).op z) e₁).trans e₂.symm

end GlobalTheory

namespace GlobalTheory

open SheafPull

theorem cechAbHEquivH'_pull {T T' : TopCat.{0}} (f : T' ⟶ T) {ι κ : Type} [LinearOrder ι]
    [LinearOrder κ] [Finite ι] [Finite κ] {V : Opens T} {U : ι → Opens T} {V' : Opens T'}
    {U' : κ → Opens T'} (τ : κ → ι)
    (hτ : ∀ s : Finset κ, cechOpen V' U' s ≤ (Opens.map f).obj (cechOpen V U (s.image τ)))
    (hc : V ≤ ⨆ i, U i) (hc' : V' ≤ ⨆ k, U' k) (hV : V' ≤ (Opens.map f).obj V) (n : ℕ) :
    ∀ {F : AbSheaf T} {G : AbSheaf T'} (φ : F ⟶ (push f).obj G) (hF : CechAcyclic V U F)
      (hG : CechAcyclic V' U' G) (x : LinearMap.ker (Cube.d (cechAbCube F.obj V U) (n + 1)))
      (y : LinearMap.ker (Cube.d (cechAbCube G.obj V' U') (n + 1))),
      y.1 = (cechAbPull f τ hτ φ).term (n + 1) x.1 →
      cechAbHEquivH' hc' hG n (cechClass _ n y) =
        SheafPull.pull f φ n (homOfLE hV) (cechAbHEquivH' hc hF n (cechClass _ n x)) := by
  induction n with
  | zero => exact fun φ hF hG x y h => GlobalTheory.T.cechComparison_degreeZero_alternatingPullback f τ hτ hc hc' hV φ hF hG x y h
  | succ n ih =>
    intro F G φ hF hG x y hy
    have hSF := Flasque.injectiveShortComplex_shortExact F
    have hSG := Flasque.injectiveShortComplex_shortExact G
    obtain ⟨ψ, rfl⟩ := exists_hom_injectiveShortComplex f φ
    have injF : Injective (Flasque.injectiveShortComplex F).X₂ :=
      inferInstanceAs (Injective (Injective.under F))
    have injG : Injective (Flasque.injectiveShortComplex G).X₂ :=
      inferInstanceAs (Injective (Injective.under G))
    have a₃F := CechAcyclic.of_shortExact₃ hSF hF (cechAcyclic_of_injective _)
    have a₃G := CechAcyclic.of_shortExact₃ hSG hG (cechAcyclic_of_injective _)
    obtain ⟨c, hc₃⟩ := cechAbδ_surjective hSF hF n (cechClass _ (n + 1) x)
    obtain ⟨x₃, rfl⟩ := cechClass_surjective _ n c
    let y₃ : LinearMap.ker (Cube.d (cechAbCube (Flasque.injectiveShortComplex G).X₃.obj V' U')
        (n + 1)) :=
      ⟨(cechAbPull f τ hτ (G := (Flasque.injectiveShortComplex G).X₃) ψ.τ₃).term (n + 1) x₃.1, by
        rw [LinearMap.mem_ker, ← GlobalTheory.T.moduleCubePullHom_term_comm_cechDifferential, x₃.2, map_zero]⟩
    obtain ⟨x₁, y₁, hy₁, hx₁, hy₁'⟩ := cechAbPull_δ f τ hτ hSF hSG hF hG ψ n x₃ y₃ rfl
    have hxy : cechClass _ (n + 1) y = cechClass _ (n + 1) y₁ :=
      Cube.PullHom.cechClass_eq _ (n + 1) x x₁ y y₁ hy hy₁ (hc₃.symm.trans hx₁)
    rw [hxy, ← hy₁']
    refine (cechAbHEquivH'_δ hc' hSG hG a₃G n _).trans ?_
    rw [ih ψ.τ₃ a₃F a₃G x₃ y₃ rfl, ← hc₃]
    refine Eq.trans ?_ (congrArg _ (cechAbHEquivH'_δ hc hSF hF a₃F n _).symm)
    exact (SheafPull.pull_δ f n hSF hSG ψ (homOfLE hV) _).symm

end GlobalTheory

namespace GlobalTheory

open SheafPull

theorem cechOpen_le_preimage_image {X X' : Scheme.{0}} (f : X' ⟶ X) {ι κ : Type} [LinearOrder ι] (U : ι → X.Opens)
    (U' : κ → X'.Opens) (τ : κ → ι) (hτ : ∀ k, U' k ≤ f ⁻¹ᵁ U (τ k)) (s : Finset κ) :
    cechOpen ⊤ U' s ≤ f ⁻¹ᵁ cechOpen ⊤ U (s.image τ) := by
  intro x hx
  rw [mem_cechOpen] at hx
  show f.base x ∈ cechOpen ⊤ U (s.image τ)
  rw [mem_cechOpen]
  refine ⟨by simp, fun i hi => ?_⟩
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hi
  exact hτ k (hx.2 k hk)

theorem exists_cechAbCocycle {X : Scheme.{0}} (R : Type) [CommRing R] [Algebra R Γ(X, ⊤)]
    {ι : Type} [LinearOrder ι] (F : X.Modules) (V : X.Opens) (U : ι → X.Opens) (n : ℕ)
    (x : LinearMap.ker (Cube.d (cechCube R F V U) (n + 1))) :
    ∃ xa : LinearMap.ker (Cube.d (cechAbCube F.presheaf V U) (n + 1)),
      (∀ s, xa.1 s = sectionsOn.toΓ F _ (x.1 s)) ∧
      cechAbHEquiv R F V U n (cechClass _ n xa) = cechClass _ n x := by
  have hb : ∀ s : Finset ι, s.Nonempty → Function.Bijective ((cechAbCubeToCube R F V U).app s) :=
    fun _ _ => Function.bijective_id
  obtain ⟨y, hy⟩ := ((cechAbCubeToCube R F V U).term_bijective hb n).2 x.1
  have hk : Cube.d _ (n + 1) y = 0 :=
    ((cechAbCubeToCube R F V U).term_bijective hb (n + 1)).1
      (((cechAbCubeToCube R F V U).term_d _ y).trans ((congrArg _ hy).trans
        (x.2.trans (map_zero _).symm)))
  refine ⟨⟨y, LinearMap.mem_ker.2 hk⟩, fun s => ?_, ?_⟩
  · have := congrFun hy s
    rw [Cube.SemiHom.term_apply] at this
    rw [← this]
    rfl
  · exact ((cechAbCubeToCube R F V U).homology_cechClass n _).trans (congrArg _ (Subtype.ext hy))

theorem cechHEquivCoh_pull : ∀ (X X' : Scheme.{0}) (R : Type) [CommRing R] [Algebra R Γ(X, ⊤)] [Algebra R Γ(X', ⊤)] (f : X' ⟶ X) (hσ : ∀ r, f.appTop (algebraMap R Γ(X, ⊤) r) = algebraMap R Γ(X', ⊤) ((RingHom.id R) r)) (F : X.Modules) (G : X'.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] (φ : F ⟶ (Scheme.Modules.pushforward f).obj G) (ι κ : Type) [LinearOrder ι] [Fintype ι] [LinearOrder κ] [Fintype κ] (U : ι → X.Opens) (U' : κ → X'.Opens) (hc : ⨆ i, U i = ⊤) (hU : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i)) (hc' : ⨆ i, U' i = ⊤) (hU' : ∀ s : Finset κ, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U' i)) (τ : κ → ι), (∀ k, U' k ≤ f ⁻¹ᵁ U (τ k)) → ∀ (n : ℕ) (x : LinearMap.ker (Cube.d (cechCube R F ⊤ U) (n + 1))) (x' : LinearMap.ker (Cube.d (cechCube R G ⊤ U') (n + 1))), (∀ (t : {t : Finset κ // t.card = n + 1}) (s : {s : Finset ι // s.card = n + 1}) (h : cechOpen ⊤ U' t.1 ≤ f ⁻¹ᵁ cechOpen ⊤ U s.1), Set.InjOn τ (t.1 : Set κ) → s.1 = t.1.image τ → x'.1 t = sortSign τ t.1 • sectionsOn.res R G h (sectionsOn.map R φ (cechOpen ⊤ U s.1) (x.1 s))) → (∀ t : {t : Finset κ // t.card = n + 1}, ¬ Set.InjOn τ (t.1 : Set κ) → x'.1 t = 0) → cechHEquivCoh R hc' hU' G n (cechClass (cechCube R G ⊤ U') n x') = cohOn.pull hσ φ (le_top : (⊤ : X'.Opens) ≤ f ⁻¹ᵁ ⊤) n (cechHEquivCoh R hc hU F n (cechClass (cechCube R F ⊤ U) n x)) := by
  intro X X' R _ _ _ f hσ F G _ _ φ ι κ _ _ _ _ U U' hc hU hc' hU' τ hτ n x x' hx' h0
  have hτ' := cechOpen_le_preimage_image f U U' τ hτ
  obtain ⟨xa, hxa, hcx⟩ := exists_cechAbCocycle R F ⊤ U n x
  obtain ⟨ya, hya, hcy⟩ := exists_cechAbCocycle R G ⊤ U' n x'
  have hF := cechAcyclicMod_top_of_isAffineOpen hU F
  have hG := cechAcyclicMod_top_of_isAffineOpen hU' G
  have key : ya.1 = (cechAbPull f.base τ hτ' (toAbSheafPush φ)).term (n + 1) xa.1 := by
    funext t
    rw [hya]
    by_cases hi : Set.InjOn τ (t.1 : Set κ)
    · refine Eq.trans ?_ (Cube.PullHom.term_apply_of_injOn _ xa.1 t hi).symm
      rw [hx' t ⟨t.1.image τ, Cube.PullHom.card_image t hi⟩ (hτ' t.1) hi rfl, hxa]
      exact map_zsmul (sectionsOn.toΓ G _) (sortSign τ t.1) _
    · refine Eq.trans ?_ (Cube.PullHom.term_apply_of_not_injOn _ xa.1 t hi).symm
      rw [h0 t hi]
      exact map_zero (sectionsOn.toΓ G _)
  apply (cohOn.toH' G ⊤ n).injective
  rw [← hcx, ← hcy]
  refine (toH'_cechHEquivCohOn R hc'.ge hG n _).trans ?_
  refine Eq.trans ?_ (cohOn.toH'_pull hσ φ _ _).symm
  refine Eq.trans ?_ (congrArg _ (toH'_cechHEquivCohOn R hc.ge hF n _).symm)
  exact cechAbHEquivH'_pull (T := X.toPresheafedSpace.carrier) f.base τ hτ' hc.ge hc'.ge le_top n
    (toAbSheafPush φ) (cechAcyclicMod_iff.1 hF) (cechAcyclicMod_iff.1 hG) xa ya key

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SchemeCechComparisonNaturalRefinementStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD GlobalTheory.CechDR GlobalTheory.HodgeCoh ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scheme_cechComparison_natural_refinement : ∀ (X X' : Scheme.{0}) (R : Type) [CommRing R] [Algebra R Γ(X, ⊤)] [Algebra R Γ(X', ⊤)] (f : X' ⟶ X) (hσ : ∀ r, f.appTop (algebraMap R Γ(X, ⊤) r) = algebraMap R Γ(X', ⊤) ((RingHom.id R) r)) (F : X.Modules) (G : X'.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] (φ : F ⟶ (Scheme.Modules.pushforward f).obj G) (ι κ : Type) [LinearOrder ι] [Fintype ι] [LinearOrder κ] [Fintype κ] (U : ι → X.Opens) (U' : κ → X'.Opens) (hc : ⨆ i, U i = ⊤) (hU : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i)) (hc' : ⨆ i, U' i = ⊤) (hU' : ∀ s : Finset κ, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U' i)) (τ : κ → ι), (∀ k, U' k ≤ f ⁻¹ᵁ U (τ k)) → ∀ (n : ℕ) (x : LinearMap.ker (Cube.d (cechCube R F ⊤ U) (n + 1))) (x' : LinearMap.ker (Cube.d (cechCube R G ⊤ U') (n + 1))), (∀ (t : {t : Finset κ // t.card = n + 1}) (s : {s : Finset ι // s.card = n + 1}) (h : cechOpen ⊤ U' t.1 ≤ f ⁻¹ᵁ cechOpen ⊤ U s.1), Set.InjOn τ (t.1 : Set κ) → s.1 = t.1.image τ → x'.1 t = sortSign τ t.1 • sectionsOn.res R G h (sectionsOn.map R φ (cechOpen ⊤ U s.1) (x.1 s))) → (∀ t : {t : Finset κ // t.card = n + 1}, ¬ Set.InjOn τ (t.1 : Set κ) → x'.1 t = 0) → cechHEquivCoh R hc' hU' G n (cechClass (cechCube R G ⊤ U') n x') = cohOn.pull hσ φ (le_top : (⊤ : X'.Opens) ≤ f ⁻¹ᵁ ⊤) n (cechHEquivCoh R hc hU F n (cechClass (cechCube R F ⊤ U) n x)) := by
  first | (exact @GlobalTheory.cechHEquivCoh_pull) | (exact GlobalTheory.cechHEquivCoh_pull) | (intros; apply GlobalTheory.cechHEquivCoh_pull  <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ExistsHodgeCohomologyEquivCechDifferentials
section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.IsAffCoverProdCechOpen
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD GlobalTheory.CechDR GlobalTheory.HodgeCoh ReciprocityTheory.ChartRestriction.G.Geo.Tor UpperTheory.GenericCoverClass

theorem UpperTheory.isAffCover_prod_cechOpen :
    ∀ (d : ℕ) (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ) [SmoothOfRelativeDimension d p] [inst : Algebra ℂ Z.functionField] (ι : Type) [LinearOrder ι] [Fintype ι] (U : ι → Z.Opens) (B : Finset ι → Subalgebra ℂ Z.functionField) (hinst : inst = ffAlg p) (hU : IsAffCover p U B)
            (d' : ℕ) (Z' : Scheme.{0}) [IsIntegral Z'] (p' : Z' ⟶ Sp ℂ) [SmoothOfRelativeDimension d' p'] [inst' : Algebra ℂ Z'.functionField] (κ : Type) [LinearOrder κ] [Fintype κ] (U' : κ → Z'.Opens) (B' : Finset κ → Subalgebra ℂ Z'.functionField) (hinst' : inst' = ffAlg p') (hU' : IsAffCover p' U' B')
            (f : Z' ⟶ Z) (hf : f ≫ p = p') (ψ : Z.functionField →ₐ[ℂ] Z'.functionField) (φ : DR ℂ Z.functionField →ₗ[ℂ] DR ℂ Z'.functionField) (τ : κ → ι),
            IsDRMap ℂ ψ φ → (∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Z' ∈ f ⁻¹ᵁ V) (g : Γ(Z, V)), ψ ((Z.presheaf.germ V (genericPoint Z) hV).hom g) = (Z'.presheaf.germ (f ⁻¹ᵁ V) (genericPoint Z') hV').hom (f.app V g)) → (∀ k, U' k ≤ f ⁻¹ᵁ U (τ k)) →
            ∀ (a b : ℕ) (hm : IsMap (cech fun I => omB ℂ Z.functionField (B I) a) (cech fun I => omB ℂ Z'.functionField (B' I) a) (pullC τ φ)) (z : hodgeH p a b),
              cmp d' p' hinst' hU' a b (hodgePull hf a b z) = Cx.hmap _ _ (pullC τ φ) hm b (cmp d p hinst hU a b z) := by
  classical
  intro d Z _ p _ inst ι _ _ U B hinst hU d' Z' _ p' _ inst' κ _ _ U' B' hinst' hU' f hf ψ φ τ hDR hψ hUU' a b hm z
  letI := algΓ p
  letI := algΓ p'
  have hσ := appTop_algebraMap (k := ℂ) hf
  have hcov : ⨆ i, U i = ⊤ := hU.cover
  have haff : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i) := fun s hs => cover_biInf hU s hs
  have hcov' : ⨆ i, U' i = ⊤ := hU'.cover
  have haff' : ∀ s : Finset κ, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U' i) := fun s hs => cover_biInf hU' s hs
  obtain ⟨x, hx⟩ := (cechClass_surjective (cechCube ℂ (Omega p a) ⊤ U) b)
    ((cechHEquivCoh ℂ hcov haff (Omega p a) b).symm z)
  have hz : cechHEquivCoh ℂ hcov haff (Omega p a) b (cechClass (cechCube ℂ (Omega p a) ⊤ U) b x) = z := by
    rw [hx]
    exact LinearEquiv.apply_symm_apply _ _
  obtain ⟨eZ, -, heZ, -⟩ := cube_exists d p hinst hU a b
  obtain ⟨w, hw⟩ := heZ x
  have hle : ∀ t : Finset κ, cechOpen ⊤ U' t ≤ f ⁻¹ᵁ cechOpen ⊤ U (Finset.image τ t) := by
    intro t y hy
    rw [mem_cechOpen] at hy
    show f.base y ∈ cechOpen ⊤ U (Finset.image τ t)
    rw [mem_cechOpen]
    refine ⟨trivial, fun i hi => ?_⟩
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hi
    exact hUU' k (hy.2 k hk)
  have hcard : ∀ t : {s : Finset κ // s.card = b + 1}, Set.InjOn τ t.1 → (Finset.image τ t.1).card = b + 1 :=
    fun t hinj => (Finset.card_image_of_injOn hinj).trans t.2
  let x' : (cechCube ℂ (Omega p' a) ⊤ U').Term (b + 1) := fun t =>
    if hinj : Set.InjOn τ t.1 then
      sortSign τ t.1 • sectionsOn.res ℂ (Omega p' a) (hle t.1)
        (sectionsOn.map ℂ (omegaPull hf a) (cechOpen ⊤ U (Finset.image τ t.1)) (x.1 ⟨_, hcard t hinj⟩))
    else 0
  have hwC := hm b w w.2.1
  have hw'mem : pullC τ φ (w : Finset ι → DR ℂ Z.functionField) ∈
      (cech fun I => omB ℂ Z'.functionField (B' I) a).Z b := by
    have hw0 : (cech fun I => omB ℂ Z.functionField (B I) a).D (w : Finset ι → DR ℂ Z.functionField) = 0 :=
      w.2.2
    have h0 : (cech fun I => omB ℂ Z'.functionField (B' I) a).D (pullC τ φ (w : Finset ι → DR ℂ Z.functionField)) = 0 := by
      rw [← hwC.2, hw0, map_zero]
    exact ⟨hwC.1, h0⟩
  let w' : ↥((cech fun I => omB ℂ Z'.functionField (B' I) a).Z b) := ⟨_, hw'mem⟩
  have hgm : ∀ t : {s : Finset κ // s.card = b + 1},
      (w' : Finset κ → DR ℂ Z'.functionField) t.1 = gm p' hinst' hU' a t.1 (x' t) := by
    intro t
    have ht : t.1.Nonempty := Finset.card_pos.mp (by rw [t.2]; omega)
    rw [gm_pos hinst' hU' a ht]
    by_cases hinj : Set.InjOn τ t.1
    · have hne : (Finset.image τ t.1).Nonempty := ht.image τ
      have e1 : (w' : Finset κ → DR ℂ Z'.functionField) t.1 =
          sortSign τ t.1 • φ ((w : Finset ι → DR ℂ Z.functionField) (Finset.image τ t.1)) := by
        show pullC τ φ (w : Finset ι → DR ℂ Z.functionField) t.1 = _
        simp only [pullC, LinearMap.coe_mk, AddHom.coe_mk, if_pos hinj]
      rw [e1, show x' t = _ from dif_pos hinj]
      refine Eq.trans ?_ (map_zsmul (formGermI p' a _ _ hinst') (sortSign τ t.1) _).symm
      rw [hw ⟨_, hcard t hinj⟩, gm_pos hinst hU a hne]
      congr 1
      exact (T.genericGerm_differentialForm_pullback_dominant Z Z' p p' hinst hinst' f hf ψ φ hDR hψ a _ _ _ _ _ _ (hle t.1) _).symm
    · have e1 : (w' : Finset κ → DR ℂ Z'.functionField) t.1 = 0 := by
        show pullC τ φ (w : Finset ι → DR ℂ Z.functionField) t.1 = _
        simp only [pullC, LinearMap.coe_mk, AddHom.coe_mk, if_neg hinj]
      rw [e1, show x' t = 0 from dif_neg hinj]
      exact (map_zero (formGermI p' a _ _ hinst')).symm
  obtain ⟨eY, -, -, hdY⟩ := cube_exists d' p' hinst' hU' a b
  have hker : x' ∈ ((cechCube ℂ (Omega p' a) ⊤ U').d (b + 1)).ker := hdY x' w' hgm
  have hR : cechHEquivCoh ℂ hcov' haff' (Omega p' a) b
      (cechClass (cechCube ℂ (Omega p' a) ⊤ U') b ⟨x', hker⟩) = hodgePull hf a b z := by
    refine (T.scheme_cechComparison_natural_refinement Z Z' ℂ f hσ _ _ (omegaPull hf a) ι κ U U' hcov haff hcov' haff' τ hUU' b x
      ⟨x', hker⟩ ?_ ?_).trans ?_
    · intro t s h hinj hs
      obtain ⟨s, hsc⟩ := s
      simp only at hs
      subst hs
      exact dif_pos hinj
    · intro t hinj
      exact dif_neg hinj
    · rw [hz]
      rfl
  rw [← hR, cmp_class d' p' hinst' hU' a b ⟨x', hker⟩ w' hgm, ← hz, cmp_class d p hinst hU a b x w hw]
  rfl
end

section -- merged from Development.AutomorphicArithmetic.GenericGermInjectivity.GermInjRangePre
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD GlobalTheory.CechDR GlobalTheory.HodgeCoh ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false

noncomputable section

namespace UpperTheory.GenericCoverClass

section Tr

variable {Z Y : Scheme.{0}} [IsIntegral Z] [IsIntegral Y] {p : Z ⟶ Sp ℂ} {p' : Y ⟶ Sp ℂ}
  [inst' : Algebra ℂ Y.functionField] {c : Y ⟶ Z} {ι : Type} {U : ι → Z.Opens}
  {B' : Finset ι → Subalgebra ℂ Y.functionField}

theorem preimage_cech (s : Finset ι) :
    c ⁻¹ᵁ cechOpen ⊤ U s = cechOpen ⊤ (fun i => c ⁻¹ᵁ U i) s := by
  ext y
  change c.base y ∈ cechOpen ⊤ U s ↔ y ∈ cechOpen ⊤ (fun i => c ⁻¹ᵁ U i) s
  rw [mem_cechOpen, mem_cechOpen]
  rfl

theorem pre_affine (hU' : IsAffCover p' (fun i => c ⁻¹ᵁ U i) B') {s : Finset ι} (h : s.Nonempty) :
    IsAffineOpen (c ⁻¹ᵁ cechOpen ⊤ U s) := by
  rw [preimage_cech]; exact cover_affine hU' h

theorem pre_generic (hU' : IsAffCover p' (fun i => c ⁻¹ᵁ U i) B') (s : Finset ι) :
    genericPoint Y ∈ c ⁻¹ᵁ cechOpen ⊤ U s := by
  rw [preimage_cech]; exact cover_generic hU' s

variable (hc : c ≫ p = p')

def up (a : ℕ) (W : Z.Opens) :
    letI := algΓ p; letI := algΓ p'
    sectionsOn ((Scheme.Modules.pushforward c).obj (Omega p' a)) W →ₗ[ℂ]
      sectionsOn (Omega p' a) (c ⁻¹ᵁ W) :=
  letI := algΓ p; letI := algΓ p'
  sectionsOn.mapOver (appTop_algebraMap hc) (𝟙 _) W

theorem up_bijective (a : ℕ) (W : Z.Opens) :
    letI := algΓ p; letI := algΓ p'
    Function.Bijective (up hc a W) := by
  letI := algΓ p; letI := algΓ p'
  exact ⟨fun x y h => (sectionsOn.toΓ _ _).injective
      ((sectionsOn.toΓ (Omega p' a) (c ⁻¹ᵁ W)).injective.eq_iff.2 h),
    fun y => ⟨(sectionsOn.toΓ _ _).symm (sectionsOn.toΓ (Omega p' a) (c ⁻¹ᵁ W) y), rfl⟩⟩

end Tr

section Gp

variable {Z Y : Scheme.{0}} [IsIntegral Z] [IsIntegral Y] {p : Z ⟶ Sp ℂ} (p' : Y ⟶ Sp ℂ)
  [inst' : Algebra ℂ Y.functionField] {c : Y ⟶ Z} {ι : Type} {U : ι → Z.Opens}
  {B' : Finset ι → Subalgebra ℂ Y.functionField}

def gp (hc : c ≫ p = p') (hinst' : inst' = ffAlg p') (hU' : IsAffCover p' (fun i => c ⁻¹ᵁ U i) B')
    (a : ℕ) (s : Finset ι) :
    letI := algΓ p
    (cechCube ℂ ((Scheme.Modules.pushforward c).obj (Omega p' a)) ⊤ U).obj s →ₗ[ℂ]
      DR ℂ Y.functionField :=
  letI := algΓ p; letI := algΓ p'
  if h : s.Nonempty then
    (formGermI p' a (pre_affine hU' h) (pre_generic hU' s) hinst') ∘ₗ
      up hc a (cechOpen ⊤ U s)
  else 0

theorem gp_pos (hc : c ≫ p = p') (hinst' : inst' = ffAlg p')
    (hU' : IsAffCover p' (fun i => c ⁻¹ᵁ U i) B') (a : ℕ) {s : Finset ι} (h : s.Nonempty) :
    letI := algΓ p; letI := algΓ p'
    gp p' hc hinst' hU' a s =
      (formGermI p' a (pre_affine hU' h) (pre_generic hU' s) hinst') ∘ₗ
        up hc a (cechOpen ⊤ U s) :=
  dif_pos h

theorem germ_inj_range_pre (d : ℕ) [SmoothOfRelativeDimension d p'] (hinst' : inst' = ffAlg p')
    (hU' : IsAffCover p' (fun i => c ⁻¹ᵁ U i) B') (a : ℕ) (s : Finset ι) (hs : s.Nonempty)
    (V : Y.Opens) (e : V = cechOpen ⊤ (fun i => c ⁻¹ᵁ U i) s) (hV : IsAffineOpen V)
    (hη : genericPoint Y ∈ V) :
    letI := algΓ p'
    Function.Injective (formGermI p' a hV hη hinst') ∧
      LinearMap.range (formGermI p' a hV hη hinst') = omB ℂ Y.functionField (B' s) a := by
  subst e
  exact UpperTheory.affineCechOpen_functionField_generic d Y p' ι _ B' hinst' hU' a s hs hV hη

theorem gp_spec (d : ℕ) [SmoothOfRelativeDimension d p'] (hc : c ≫ p = p')
    (hinst' : inst' = ffAlg p') (hU' : IsAffCover p' (fun i => c ⁻¹ᵁ U i) B') (a : ℕ) :
    letI := algΓ p
    (∀ s, s.Nonempty → Function.Injective (gp p' hc hinst' hU' a s)) ∧
    (∀ s, s.Nonempty → LinearMap.range (gp p' hc hinst' hU' a s) = omB ℂ Y.functionField (B' s) a) ∧
    (∀ s t (h : s ⊆ t), s.Nonempty → ∀ y,
      gp p' hc hinst' hU' a t
        (Cube.res (cechCube ℂ ((Scheme.Modules.pushforward c).obj (Omega p' a)) ⊤ U) h y) =
      gp p' hc hinst' hU' a s y) := by
  letI := algΓ p; letI := algΓ p'
  refine ⟨fun s hs => ?_, fun s hs => ?_, fun s t h hs y => ?_⟩
  · rw [gp_pos p' hc hinst' hU' a hs]
    exact (germ_inj_range_pre p' d hinst' hU' a s hs _ (preimage_cech s) _ _).1.comp
      (up_bijective hc a _).1
  · rw [gp_pos p' hc hinst' hU' a hs]
    refine Eq.trans (LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.2 (up_bijective hc a _).2)) ?_
    exact (germ_inj_range_pre p' d hinst' hU' a s hs _ (preimage_cech s) _ _).2
  · rw [gp_pos p' hc hinst' hU' a hs, gp_pos p' hc hinst' hU' a (hs.mono h)]
    exact GlobalTheory.T.genericGerm_differentialForm_restrict_affineOpen Y p' hinst' a _ _ _ _ _ _ (c.preimage_mono (cechOpen_anti ⊤ U h)) _

end Gp

section Main

theorem cmp_trace (d : ℕ) (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ) [SmoothOfRelativeDimension d p] [inst : Algebra ℂ Z.functionField] (Y : Scheme.{0}) [IsIntegral Y] (p' : Y ⟶ Sp ℂ) [SmoothOfRelativeDimension d p'] [inst' : Algebra ℂ Y.functionField] [Algebra Z.functionField Y.functionField] [IsScalarTower ℂ Z.functionField Y.functionField] (c : Y ⟶ Z) (hc : c ≫ p = p') [IsFinite c] [Etale c] (ι : Type) [LinearOrder ι] [Fintype ι] (U : ι → Z.Opens) (B : Finset ι → Subalgebra ℂ Z.functionField) (B' : Finset ι → Subalgebra ℂ Y.functionField) (hinst : inst = ffAlg p) (hinst' : inst' = ffAlg p') (hU : IsAffCover p U B) (hU' : IsAffCover p' (fun i => c ⁻¹ᵁ U i) B')
    (hg : ∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c ⁻¹ᵁ V) (g : Γ(Z, V)), (Y.presheaf.germ (c ⁻¹ᵁ V) (genericPoint Y) hV').hom ((c.app V).hom g) = algebraMap Z.functionField Y.functionField ((Z.presheaf.germ V (genericPoint Z) hV).hom g))
    (a b : ℕ) (hm : IsMap (cech fun I => omB ℂ Y.functionField (B' I) a) (cech fun I => omB ℂ Z.functionField (B I) a) (LinearMap.pi fun s : Finset ι => (GlobalTheory.W1.trDR ℂ Z.functionField Y.functionField).comp (LinearMap.proj s))) (z : hodgeH p' a b) :
    cmp d p hinst hU a b (hodgeTrace hc a b z) = Cx.hmap _ _ (LinearMap.pi fun s : Finset ι => (GlobalTheory.W1.trDR ℂ Z.functionField Y.functionField).comp (LinearMap.proj s)) hm b (cmp d p' hinst' hU' a b z) := by
  letI := algΓ p
  letI := algΓ p'
  have hfin := (GlobalTheory.T.finiteEtale_functionField_integralClosure_differentials Z Y p p' c hc inferInstance inferInstance d hinst hinst' hg).1
  obtain ⟨z1, hz1⟩ := cechClass_surjective
    (cechCube ℂ ((Scheme.Modules.pushforward c).obj (Omega p' a)) ⊤ U) b
    ((cechHEquivCoh ℂ hU.cover (cover_biInf hU) ((Scheme.Modules.pushforward c).obj (Omega p' a)) b).symm
      ((coh.pushforwardEquiv ℂ (appTop_algebraMap hc) (Omega p' a) b).symm z))
  have hs := gp_spec (p := p) (U := U) (B' := B') p' d hc hinst' hU' a
  let w : (GlobalTheory.PD.cech fun I => omB ℂ Y.functionField (B' I) a).Z (b : ℤ) :=
    ⟨GlobalTheory.CechFam.famMap (gp p' hc hinst' hU' a) (b + 1) z1.1,
      by
        refine Submodule.mem_inf.2 ⟨GlobalTheory.CechFam.famMap_mem hs.2.1 b z1.1, ?_⟩
        rw [LinearMap.mem_ker]
        change deltaL ℂ ι (DR ℂ Y.functionField) (GlobalTheory.CechFam.famMap (gp p' hc hinst' hU' a) (b + 1) z1.1) = 0
        rw [← GlobalTheory.CechFam.famMap_d hs.2.2, LinearMap.mem_ker.1 z1.2, map_zero]⟩
  have hw : ∀ t : {s : Finset ι // s.card = b + 1},
      (w : Finset ι → DR ℂ Y.functionField) t.1 = gp p' hc hinst' hU' a t.1 (z1.1 t) := by
    intro t
    exact GlobalTheory.CechFam.famMap_of_eq _ _ t.2
  have hle : ∀ s : Finset ι, cechOpen ⊤ (fun i => c ⁻¹ᵁ U i) s ≤ c ⁻¹ᵁ cechOpen ⊤ U s :=
    fun s => (preimage_cech s).ge
  have hne : ∀ t : {s : Finset ι // s.card = b + 1}, t.1.Nonempty := fun t =>
    Finset.card_pos.1 (by rw [t.2]; omega)
  let x0 : Cube.Term (cechCube ℂ (Omega p' a) ⊤ fun i => c ⁻¹ᵁ U i) (b + 1) := fun t =>
    sectionsOn.res ℂ (Omega p' a) (hle t.1) (up hc a _ (z1.1 t))
  have hx0 : ∀ t : {s : Finset ι // s.card = b + 1},
      (w : Finset ι → DR ℂ Y.functionField) t.1 = gm p' hinst' hU' a t.1 (x0 t) := by
    intro t
    rw [hw t, gp_pos p' hc hinst' hU' a (hne t), gm_pos hinst' hU' a (hne t)]
    exact (GlobalTheory.T.genericGerm_differentialForm_restrict_affineOpen Y p' hinst' a _ _ _ _ _ _ (hle t.1) _).symm
  have hd := (Classical.choose_spec (cube_exists d p' hinst' hU' a b)).2.2 x0 w hx0
  let z0 : LinearMap.ker (Cube.d (cechCube ℂ (Omega p' a) ⊤ fun i => c ⁻¹ᵁ U i) (b + 1)) := ⟨x0, hd⟩
  have key := GlobalTheory.T.scheme_cechComparison_natural_refinement Z Y ℂ c (appTop_algebraMap hc)
    ((Scheme.Modules.pushforward c).obj (Omega p' a)) (Omega p' a) (𝟙 _) ι ι U
    (fun i => c ⁻¹ᵁ U i) hU.cover (cover_biInf hU) hU'.cover (cover_biInf hU') id (fun _ => le_rfl) b
    z1 z0 (fun t s h _ e => by
      obtain rfl : s = t := Subtype.ext (by simpa using e)
      have h1 : sortSign (id : ι → ι) s.1 = 1 := by
        refine Finset.prod_eq_one fun x _ => Finset.prod_eq_one fun y _ => ?_
        exact if_neg fun h => lt_asymm h.1 h.2
      rw [h1, one_smul]
      rfl) (fun t h => absurd Function.injective_id.injOn h)
  have hback : cechHEquivCoh ℂ hU.cover (cover_biInf hU)
      ((Scheme.Modules.pushforward c).obj (Omega p' a)) b (cechClass _ b z1) =
      (coh.pushforwardEquiv ℂ (appTop_algebraMap hc) (Omega p' a) b).symm z := by
    rw [hz1]; exact LinearEquiv.apply_symm_apply _ _
  have hz : cechHEquivCoh ℂ hU'.cover (cover_biInf hU') (Omega p' a) b (cechClass _ b z0) = z := by
    refine key.trans ?_
    rw [hback]
    exact LinearEquiv.apply_symm_apply (coh.pushforwardEquiv ℂ (appTop_algebraMap hc) (Omega p' a) b) z
  let z2 : LinearMap.ker (Cube.d (cechCube ℂ (Omega p a) ⊤ U) (b + 1)) :=
    ⟨Cube.termMap (cechCubeMap ℂ ⊤ U (omegaTrace hc a)) (b + 1) z1.1,
      Cube.termMap_mem_ker _ z1.2⟩
  have hTw := hm b w w.2.1
  have hTw' : (LinearMap.pi fun s : Finset ι => (GlobalTheory.W1.trDR ℂ Z.functionField Y.functionField).comp (LinearMap.proj s)) (w : Finset ι → DR ℂ Y.functionField) ∈
      (GlobalTheory.PD.cech fun I => omB ℂ Z.functionField (B I) a).Z (b : ℤ) := by
    refine ⟨hTw.1, ?_⟩
    have h0 : (GlobalTheory.PD.cech fun I => omB ℂ Y.functionField (B' I) a).D w = 0 := w.2.2
    change _ = 0
    rw [← hTw.2, h0, map_zero]
  let w2 : (GlobalTheory.PD.cech fun I => omB ℂ Z.functionField (B I) a).Z (b : ℤ) := ⟨_, hTw'⟩
  have hw2 : ∀ t : {s : Finset ι // s.card = b + 1},
      (w2 : Finset ι → DR ℂ Z.functionField) t.1 = gm p hinst hU a t.1 (z2.1 t) := by
    intro t
    change GlobalTheory.W1.trDR ℂ Z.functionField Y.functionField ((w : Finset ι → DR ℂ Y.functionField) t.1) = _
    rw [hw t, gp_pos p' hc hinst' hU' a (hne t), gm_pos hinst hU a (hne t)]
    exact (UpperTheory.functionField_of_finite_etale_cover Z Y p p' c hc hinst hinst' hg hfin a _ (cover_affine hU (hne t))
      (cover_generic hU _) (pre_generic hU' _) _).symm
  have htr : hodgeTrace hc a b z =
      cechHEquivCoh ℂ hU.cover (cover_biInf hU) (Omega p a) b (cechClass _ b z2) := by
    change cohOn.map ℂ (omegaTrace hc a) ⊤ b
      ((coh.pushforwardEquiv ℂ (appTop_algebraMap hc) (Omega p' a) b).symm z) = _
    rw [← hback]
    refine (cechHEquivCoh_map ℂ hU.cover (cover_biInf hU) (omegaTrace hc a) b
      (cechClass _ b z1)).symm.trans ?_
    exact congrArg _ (homologyMap_cechClass (cechCubeMap ℂ ⊤ U (omegaTrace hc a)) b z1 z2 rfl)
  have e1 := cmp_class d p' hinst' hU' a b z0 w hx0
  have e2 := cmp_class d p hinst hU a b z2 w2 hw2
  rw [hz] at e1
  rw [htr, e2, e1]
  rfl

end Main

end UpperTheory.GenericCoverClass
end
end

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD GlobalTheory.CechDR GlobalTheory.HodgeCoh ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem UpperTheory.Cb.exists_hodge_cohomology_equiv_cech_differentials :
    ∃ e : ∀ (d : ℕ) (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ) [SmoothOfRelativeDimension d p] [inst : Algebra ℂ Z.functionField] (ι : Type) [LinearOrder ι] [Fintype ι] (U : ι → Z.Opens) (B : Finset ι → Subalgebra ℂ Z.functionField) (hinst : inst = ffAlg p) (hU : IsAffCover p U B) (a b : ℕ), hodgeH p a b ≃ₗ[ℂ] (cech fun I => omB ℂ Z.functionField (B I) a).H b,
      (∀ (d : ℕ) (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ) [SmoothOfRelativeDimension d p] [inst : Algebra ℂ Z.functionField] (ι : Type) [LinearOrder ι] [Fintype ι] (U : ι → Z.Opens) (B : Finset ι → Subalgebra ℂ Z.functionField) (hinst : inst = ffAlg p) (hU : IsAffCover p U B)
        (d' : ℕ) (Z' : Scheme.{0}) [IsIntegral Z'] (p' : Z' ⟶ Sp ℂ) [SmoothOfRelativeDimension d' p'] [inst' : Algebra ℂ Z'.functionField] (κ : Type) [LinearOrder κ] [Fintype κ] (U' : κ → Z'.Opens) (B' : Finset κ → Subalgebra ℂ Z'.functionField) (hinst' : inst' = ffAlg p') (hU' : IsAffCover p' U' B')
        (f : Z' ⟶ Z) (hf : f ≫ p = p') (ψ : Z.functionField →ₐ[ℂ] Z'.functionField) (φ : DR ℂ Z.functionField →ₗ[ℂ] DR ℂ Z'.functionField) (τ : κ → ι),
        IsDRMap ℂ ψ φ → (∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Z' ∈ f ⁻¹ᵁ V) (g : Γ(Z, V)), ψ ((Z.presheaf.germ V (genericPoint Z) hV).hom g) = (Z'.presheaf.germ (f ⁻¹ᵁ V) (genericPoint Z') hV').hom (f.app V g)) → (∀ k, U' k ≤ f ⁻¹ᵁ U (τ k)) →
        ∀ (a b : ℕ) (hm : IsMap (cech fun I => omB ℂ Z.functionField (B I) a) (cech fun I => omB ℂ Z'.functionField (B' I) a) (pullC τ φ)) (z : hodgeH p a b),
          e d' Z' p' κ U' B' hinst' hU' a b (hodgePull hf a b z) = Cx.hmap _ _ (pullC τ φ) hm b (e d Z p ι U B hinst hU a b z)) ∧
      (∀ (d : ℕ) (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ) [SmoothOfRelativeDimension d p] [inst : Algebra ℂ Z.functionField] (Y : Scheme.{0}) [IsIntegral Y] (p' : Y ⟶ Sp ℂ) [SmoothOfRelativeDimension d p'] [inst' : Algebra ℂ Y.functionField] [Algebra Z.functionField Y.functionField] [IsScalarTower ℂ Z.functionField Y.functionField] (c : Y ⟶ Z) (hc : c ≫ p = p') [IsFinite c] [Etale c] (ι : Type) [LinearOrder ι] [Fintype ι] (U : ι → Z.Opens) (B : Finset ι → Subalgebra ℂ Z.functionField) (B' : Finset ι → Subalgebra ℂ Y.functionField) (hinst : inst = ffAlg p) (hinst' : inst' = ffAlg p') (hU : IsAffCover p U B) (hU' : IsAffCover p' (fun i => c ⁻¹ᵁ U i) B'),
        (∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c ⁻¹ᵁ V) (g : Γ(Z, V)), (Y.presheaf.germ (c ⁻¹ᵁ V) (genericPoint Y) hV').hom ((c.app V).hom g) = algebraMap Z.functionField Y.functionField ((Z.presheaf.germ V (genericPoint Z) hV).hom g)) →
        ∀ (a b : ℕ) (hm : IsMap (cech fun I => omB ℂ Y.functionField (B' I) a) (cech fun I => omB ℂ Z.functionField (B I) a) (LinearMap.pi fun s : Finset ι => (GlobalTheory.W1.trDR ℂ Z.functionField Y.functionField).comp (LinearMap.proj s))) (z : hodgeH p' a b),
          e d Z p ι U B hinst hU a b (hodgeTrace hc a b z) = Cx.hmap _ _ (LinearMap.pi fun s : Finset ι => (GlobalTheory.W1.trDR ℂ Z.functionField Y.functionField).comp (LinearMap.proj s)) hm b (e d Y p' ι (fun i => c ⁻¹ᵁ U i) B' hinst' hU' a b z)) := by
  refine ⟨fun d Z _ p _ inst ι _ _ U B hinst hU a b => UpperTheory.GenericCoverClass.cmp d p hinst hU a b, ?_, ?_⟩
  · exact UpperTheory.isAffCover_prod_cechOpen
  · intro d Z _ p _ inst Y _ p' _ inst' _ _ c hc _ _ ι _ _ U B B' hinst hinst' hU hU' hg a b hm z
    exact UpperTheory.GenericCoverClass.cmp_trace d Z p Y p' c hc ι U B B' hinst hinst' hU hU' hg a b hm z
end

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD GlobalTheory.CechDR GlobalTheory.HodgeCoh ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.exists_hodge_cohomology_equiv_cech_differentials : ∃ e : ∀ (d : ℕ) (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ) [SmoothOfRelativeDimension d p] [inst : Algebra ℂ Z.functionField] (ι : Type) [LinearOrder ι] [Fintype ι] (U : ι → Z.Opens) (B : Finset ι → Subalgebra ℂ Z.functionField) (hinst : inst = ffAlg p) (hU : IsAffCover p U B) (a b : ℕ), hodgeH p a b ≃ₗ[ℂ] (cech fun I => omB ℂ Z.functionField (B I) a).H b,
  (∀ (d : ℕ) (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ) [SmoothOfRelativeDimension d p] [inst : Algebra ℂ Z.functionField] (ι : Type) [LinearOrder ι] [Fintype ι] (U : ι → Z.Opens) (B : Finset ι → Subalgebra ℂ Z.functionField) (hinst : inst = ffAlg p) (hU : IsAffCover p U B)
    (d' : ℕ) (Z' : Scheme.{0}) [IsIntegral Z'] (p' : Z' ⟶ Sp ℂ) [SmoothOfRelativeDimension d' p'] [inst' : Algebra ℂ Z'.functionField] (κ : Type) [LinearOrder κ] [Fintype κ] (U' : κ → Z'.Opens) (B' : Finset κ → Subalgebra ℂ Z'.functionField) (hinst' : inst' = ffAlg p') (hU' : IsAffCover p' U' B')
    (f : Z' ⟶ Z) (hf : f ≫ p = p') (ψ : Z.functionField →ₐ[ℂ] Z'.functionField) (φ : DR ℂ Z.functionField →ₗ[ℂ] DR ℂ Z'.functionField) (τ : κ → ι),
    IsDRMap ℂ ψ φ → (∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Z' ∈ f ⁻¹ᵁ V) (g : Γ(Z, V)), ψ ((Z.presheaf.germ V (genericPoint Z) hV).hom g) = (Z'.presheaf.germ (f ⁻¹ᵁ V) (genericPoint Z') hV').hom (f.app V g)) → (∀ k, U' k ≤ f ⁻¹ᵁ U (τ k)) →
    ∀ (a b : ℕ) (hm : IsMap (cech fun I => omB ℂ Z.functionField (B I) a) (cech fun I => omB ℂ Z'.functionField (B' I) a) (pullC τ φ)) (z : hodgeH p a b),
      e d' Z' p' κ U' B' hinst' hU' a b (hodgePull hf a b z) = Cx.hmap _ _ (pullC τ φ) hm b (e d Z p ι U B hinst hU a b z)) ∧
  (∀ (d : ℕ) (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ) [SmoothOfRelativeDimension d p] [inst : Algebra ℂ Z.functionField] (Y : Scheme.{0}) [IsIntegral Y] (p' : Y ⟶ Sp ℂ) [SmoothOfRelativeDimension d p'] [inst' : Algebra ℂ Y.functionField] [Algebra Z.functionField Y.functionField] [IsScalarTower ℂ Z.functionField Y.functionField] (c : Y ⟶ Z) (hc : c ≫ p = p') [IsFinite c] [Etale c] (ι : Type) [LinearOrder ι] [Fintype ι] (U : ι → Z.Opens) (B : Finset ι → Subalgebra ℂ Z.functionField) (B' : Finset ι → Subalgebra ℂ Y.functionField) (hinst : inst = ffAlg p) (hinst' : inst' = ffAlg p') (hU : IsAffCover p U B) (hU' : IsAffCover p' (fun i => c ⁻¹ᵁ U i) B'),
    (∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c ⁻¹ᵁ V) (g : Γ(Z, V)), (Y.presheaf.germ (c ⁻¹ᵁ V) (genericPoint Y) hV').hom ((c.app V).hom g) = algebraMap Z.functionField Y.functionField ((Z.presheaf.germ V (genericPoint Z) hV).hom g)) →
    ∀ (a b : ℕ) (hm : IsMap (cech fun I => omB ℂ Y.functionField (B' I) a) (cech fun I => omB ℂ Z.functionField (B I) a) (LinearMap.pi fun s : Finset ι => (GlobalTheory.W1.trDR ℂ Z.functionField Y.functionField).comp (LinearMap.proj s))) (z : hodgeH p' a b),
      e d Z p ι U B hinst hU a b (hodgeTrace hc a b z) = Cx.hmap _ _ (LinearMap.pi fun s : Finset ι => (GlobalTheory.W1.trDR ℂ Z.functionField Y.functionField).comp (LinearMap.proj s)) hm b (e d Y p' ι (fun i => c ⁻¹ᵁ U i) B' hinst' hU' a b z)) := by
  first | exact @UpperTheory.Cb.exists_hodge_cohomology_equiv_cech_differentials | exact UpperTheory.Cb.exists_hodge_cohomology_equiv_cech_differentials
