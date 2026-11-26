module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntOfIsIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHoloSectionAeEqOfBallCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperH2SumOfCupsExact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosetTwoCocycleEqCechImageAddCoboundary

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderedCechToCatCochainsOneCoboundaryComm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderedCechToCatCochainsOneCoboundaryComm
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CechPosetDegreeOne
variable {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R)


open Classical in
def val {p : ℕ} (c : CC F p) (s : Finset κ) (b : (NE κ)ᵒᵖ) : F.obj b :=
  if h : s.card = p + 1 ∧ s ⊆ sub b then
    mp F (homOf (a := ne s (card_nonempty ⟨s, h.1⟩)) (b := b) h.2) (c ⟨s, h.1⟩) else 0

theorem val_eq {p : ℕ} (c : CC F p) (s : {s : Finset κ // s.card = p + 1}) (b : (NE κ)ᵒᵖ)
    (f : ne s.1 (card_nonempty s) ⟶ b) : mp F f (c s) = val F c s.1 b := by
  unfold val
  obtain ⟨s, hs⟩ := s
  have hsub : s ⊆ sub b := sub_subset f
  rw [dite_eq_left (⟨hs, hsub⟩ : s.card = p + 1 ∧ s ⊆ sub b)]
  exact congrArg (fun φ => mp F φ (c ⟨s, hs⟩)) (Subsingleton.elim _ _)

theorem mp_val {p : ℕ} (c : CC F p) (s : Finset κ) {b d : (NE κ)ᵒᵖ} (g : b ⟶ d)
    (h : s.card = p + 1) (hs : s ⊆ sub b) : mp F g (val F c s b) = val F c s d := by
  rw [← val_eq F c ⟨s, h⟩ b (homOf hs), ← mp_comp, val_eq]

theorem orderedCechToCatCochainsOne_apply_valueAtSubset (c : CC F 1) {a b : (NE κ)ᵒᵖ} (f : a ⟶ b) :
    e1 F c a b f = if mn b < mn a then - val F c {mn b, mn a} b else 0 := by
  simp only [e1, LinearMap.pi_apply]
  split_ifs with h
  · simp only [LinearMap.neg_apply, LinearMap.comp_apply, LinearMap.proj_apply, AlgHom.toLinearMap_apply]
    exact congrArg Neg.neg (val_eq F c ⟨{mn b, mn a}, Finset.card_pair h.ne⟩ b _)
  · rfl

theorem alternatingToOrderedCechDegreeTwo_apply_valueAtSubset (c : CC F 2) {a b d : (NE κ)ᵒᵖ} (f : a ⟶ b) (g : b ⟶ d) :
    e2 F c a b d f g = if mn d < mn b ∧ mn b < mn a then - val F c {mn d, mn b, mn a} d else 0 := by
  simp only [e2, LinearMap.pi_apply]
  split_ifs with h
  · simp only [LinearMap.neg_apply, LinearMap.comp_apply, LinearMap.proj_apply, AlgHom.toLinearMap_apply]
    exact congrArg Neg.neg (val_eq F c ⟨{mn d, mn b, mn a}, card_three h.1 h.2⟩ d _)
  · rfl

theorem val_δ {p : ℕ} (c : CC F p) (t : Finset κ) (d : (NE κ)ᵒᵖ) (h : t.card = p + 1 + 1)
    (ht : t ⊆ sub d) :
    val F (δ F p c) t d = ∑ i ∈ t, GlobalTheory.cubeSign t i • val F c (t.erase i) d := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← val_eq F (δ F p c) ⟨t, h⟩ d (homOf ht), δ_apply, map_sum,
    ← Finset.sum_coe_sort t (fun i => GlobalTheory.cubeSign t i • val F c (t.erase i) d)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, ← mp_comp, val_eq]

theorem val_δ_three (c : CC F 1) {x y z : κ} (h₁ : x < y) (h₂ : y < z) (d : (NE κ)ᵒᵖ)
    (ht : ({x, y, z} : Finset κ) ⊆ sub d) :
    val F (δ F 1 c) {x, y, z} d = val F c {y, z} d - val F c {x, z} d + val F c {x, y} d := by
  have h₃ := h₁.trans h₂
  rw [val_δ F c _ d (card_three h₁ h₂) ht, Finset.sum_insert (by simp [h₁.ne, h₃.ne]),
    Finset.sum_pair h₂.ne]
  have e₁ : ({x, y, z} : Finset κ).erase x = {y, z} := by
    ext w; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · tauto
    · rintro (rfl | rfl) <;> simp [h₁.ne', h₃.ne']
  have e₂ : ({x, y, z} : Finset κ).erase y = {x, z} := by
    ext w; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · tauto
    · rintro (rfl | rfl) <;> simp [h₁.ne, h₂.ne']
  have e₃ : ({x, y, z} : Finset κ).erase z = {x, y} := by
    ext w; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · tauto
    · rintro (rfl | rfl) <;> simp [h₃.ne, h₂.ne]
  have s₁ : GlobalTheory.cubeSign ({x, y, z} : Finset κ) x = 1 := by
    simp [GlobalTheory.cubeSign, Finset.filter_insert, Finset.filter_singleton, h₁.not_gt, h₃.not_gt]
  have s₂ : GlobalTheory.cubeSign ({x, y, z} : Finset κ) y = -1 := by
    simp [GlobalTheory.cubeSign, Finset.filter_insert, Finset.filter_singleton, h₁, h₂.not_gt]
  have s₃ : GlobalTheory.cubeSign ({x, y, z} : Finset κ) z = 1 := by
    simp [GlobalTheory.cubeSign, Finset.filter_insert, Finset.filter_singleton, h₃, h₂, Finset.card_pair h₁.ne]
  rw [e₁, e₂, e₃, s₁, s₂, s₃]
  simp only [one_smul, neg_smul]
  ring

theorem orderedCechToCatCochainsOne_coboundary_comm {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R)
    (c : CC F 1) : d1 F (e1 F c) = e2 F (δ F 1 c) := by
  funext a b d f g
  rw [d1_apply, orderedCechToCatCochainsOne_apply_valueAtSubset, orderedCechToCatCochainsOne_apply_valueAtSubset, orderedCechToCatCochainsOne_apply_valueAtSubset, alternatingToOrderedCechDegreeTwo_apply_valueAtSubset]
  rcases (mn_le_of_hom f).lt_or_eq with h₂ | h₂ <;> rcases (mn_le_of_hom g).lt_or_eq with h₁ | h₁
  · rw [if_pos h₂, if_pos h₁, if_pos (h₁.trans h₂), if_pos ⟨h₁, h₂⟩, map_neg,
      mp_val F c _ g (Finset.card_pair h₂.ne) (pair_subset f),
      val_δ_three F c h₁ h₂ d (triple_subset f g)]
    ring
  · rw [if_pos h₂, if_neg h₁.not_lt, if_pos (h₁ ▸ h₂), if_neg (fun h => h₁.not_lt h.1), map_neg,
      mp_val F c _ g (Finset.card_pair h₂.ne) (pair_subset f), h₁]
    ring
  · rw [if_neg h₂.not_lt, if_pos h₁, if_pos (h₂ ▸ h₁), if_neg (fun h => h₂.not_lt h.2), map_zero, h₂]
    ring
  · rw [if_neg h₂.not_lt, if_neg h₁.not_lt, if_neg (h₁.trans h₂).not_lt,
      if_neg (fun h => h₂.not_lt h.2), map_zero]
    ring

end GlobalTheory.CechPosetDegreeOne
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderedCechToCatCochainsOneCoboundaryCommStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orderedCech_cochainsOne_coboundary_comm : ∀ {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R) (c : CC F 1), d1 F (e1 F c) = e2 F (δ F 1 c) := by
  first | exact @GlobalTheory.CechPosetDegreeOne.orderedCechToCatCochainsOne_coboundary_comm | exact GlobalTheory.CechPosetDegreeOne.orderedCechToCatCochainsOne_coboundary_comm | (intros; apply GlobalTheory.CechPosetDegreeOne.orderedCechToCatCochainsOne_coboundary_comm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderedCechDegreeZeroCocyclesCorrespond
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderedCechDegreeZeroCocyclesCorrespond
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

set_option autoImplicit false

namespace GlobalTheory.CechPoset

variable {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R)

theorem hom_eq_id {a : (NE κ)ᵒᵖ} (f : a ⟶ a) : f = 𝟙 a :=
  Quiver.Hom.unop_inj (Subsingleton.elim _ _)

theorem mp_single (c : CC F 0) (i j : κ) (hij : j = i) (h : sub (ne {j} (Finset.singleton_nonempty j)) ⊆
    sub (ne {i} (Finset.singleton_nonempty i))) (hc : ({j} : Finset κ).card = 0 + 1) :
    mp F (homOf h) (c ⟨{j}, hc⟩) = c ⟨{i}, Finset.card_singleton i⟩ := by
  subst hij
  rw [hom_eq_id (homOf h), mp_id]

theorem sum_cubeSign_two (t : Finset κ) (ht : t.card = 2) : ∑ i ∈ t, GlobalTheory.cubeSign t i = 0 := by
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.1 ht
  rw [Finset.sum_pair hxy]
  rcases lt_or_gt_of_ne hxy with h | h
  · simp [GlobalTheory.cubeSign, Finset.filter_insert, Finset.filter_singleton, h, h.not_gt]
  · simp [GlobalTheory.cubeSign, Finset.filter_insert, Finset.filter_singleton, h, h.not_gt]

theorem orderedCech_degreeZero_cocycles_correspond : (∀ c : CC F 0, δ F 0 c = 0 → e0 F c = 0 → c = 0) ∧
    ∀ g : C0 F, d0 F g = 0 → ∃ c : CC F 0, δ F 0 c = 0 ∧ e0 F c = g := by
  refine ⟨fun c _ he => ?_, fun g hg => ?_⟩
  · funext s
    obtain ⟨s, hs⟩ := s
    obtain ⟨i, rfl⟩ := Finset.card_eq_one.1 hs
    have H := congrFun he (ne {i} (Finset.singleton_nonempty i))
    have hm : mn (ne {i} (Finset.singleton_nonempty i)) = i := Finset.min'_singleton i
    have := mp_single F c i _ hm
    simp only [e0, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply] at H
    exact (this (Finset.singleton_subset_iff.2 (mn_mem _)) (Finset.card_singleton _)).symm.trans H
  · have hg' : ∀ {T T' : (NE κ)ᵒᵖ} (φ : T ⟶ T'), mp F φ (g T) = g T' := by
      intro T T' φ
      have := congrFun (congrFun (congrFun hg T) T') φ
      rw [amitsur_d0_apply] at this
      exact (sub_eq_zero.1 this).symm
    refine ⟨fun s => g (ne s.1 (card_nonempty s)), ?_, ?_⟩
    · funext t
      rw [δ_apply]
      simp only [hg']
      rw [← Finset.sum_smul, Finset.sum_coe_sort t.1 (fun i => GlobalTheory.cubeSign t.1 i),
        sum_cubeSign_two t.1 t.2, zero_smul]
      rfl
    · funext a
      simp only [e0, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply]
      exact hg' _

end GlobalTheory.CechPoset
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderedCechDegreeZeroCocyclesCorrespondStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orderedCechDegreeZero_cocycles_correspond : ∀ {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R), (∀ c : CC F 0, δ F 0 c = 0 → e0 F c = 0 → c = 0) ∧ ∀ g : C0 F, d0 F g = 0 → ∃ c : CC F 0, δ F 0 c = 0 ∧ e0 F c = g := by
  first | exact @GlobalTheory.CechPoset.orderedCech_degreeZero_cocycles_correspond | exact GlobalTheory.CechPoset.orderedCech_degreeZero_cocycles_correspond | (intros; apply GlobalTheory.CechPoset.orderedCech_degreeZero_cocycles_correspond <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechH2PullbackRefinementCompat
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechH2PullbackRefinementCompat
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh

namespace GlobalTheory.CechPoset

theorem restrict_pull2_pullHO2 {R' R'' : Type} [CommRing R'] [CommRing R''] {X' X'' : Scheme.{0}}
    {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {σ : R' →+* R''} {ψ : X'' ⟶ X'}
    (w : ψ ≫ s' = s'' ≫ spMap σ) {κ : Type} [LinearOrder κ] (D' : κ → X'.Opens)
    (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D' i)) (D'' : κ → X''.Opens)
    (hD'' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D'' i))
    (hle : ∀ i, D'' i ≤ ψ ⁻¹ᵁ D' i) (y : HO2 s') :
    (CoefMap.restrict (OAff s'') (cov_mono D'' hD'').functor.op).pull2 (pullHO2 w y) =
      (pullCoef w D' hD' D'' hD'' hle).pull2
        ((CoefMap.restrict (OAff s') (cov_mono D' hD').functor.op).pull2 y) := by
  have hm : Monotone (pr D' hD' D'' hD'' hle) := fun I J h =>
    Subtype.mk_le_mk.2 (Prod.mk_le_mk.2 ⟨cov_mono D'' hD'' h, cov_mono D' hD' h⟩)
  have h1 : (pairRes ψ s'').pull2 (pullHO2 w y) = (pairPull w).pull2 y :=
    (LinearEquiv.ofBijective (pairRes ψ s'').pull2 (pairRes_pull2_bijective ψ s'')).apply_symm_apply _
  have h2 := congrArg (CoefMap.restrict (OPair ψ s'') hm.functor.op).pull2 h1
  generalize pullHO2 w y = z at h2 ⊢
  obtain ⟨z, rfl⟩ := CatCoh.H2.mk_surjective _ z
  obtain ⟨y, rfl⟩ := CatCoh.H2.mk_surjective _ y
  exact h2

end GlobalTheory.CechPoset
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechH2PullbackRefinementCompatStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_h2_pullback_refinement_compat : ∀ {R' R'' : Type} [CommRing R'] [CommRing R''] {X' X'' : Scheme.{0}} {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {σ : R' →+* R''} {ψ : X'' ⟶ X'} (w : ψ ≫ s' = s'' ≫ spMap σ) {κ : Type} [LinearOrder κ] (D' : κ → X'.Opens) (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D' i)) (D'' : κ → X''.Opens) (hD'' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D'' i)) (hle : ∀ i, D'' i ≤ ψ ⁻¹ᵁ D' i) (y : HO2 s'), (CoefMap.restrict (OAff s'') (cov_mono D'' hD'').functor.op).pull2 (pullHO2 w y) = (pullCoef w D' hD' D'' hD'' hle).pull2 ((CoefMap.restrict (OAff s') (cov_mono D' hD').functor.op).pull2 y) := by
  first | exact @GlobalTheory.CechPoset.restrict_pull2_pullHO2 | exact GlobalTheory.CechPoset.restrict_pull2_pullHO2 | (intros; apply GlobalTheory.CechPoset.restrict_pull2_pullHO2 <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechCoboundaryOfDegreeTwoImageCoboundaryAl
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechCoboundaryOfDegreeTwoImageCoboundaryAl
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

namespace GlobalTheory.CechPoset

variable {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R)

private theorem mn_ne (s : Finset κ) (h : s.Nonempty) : mn (ne s h) = s.min' h := rfl

private theorem min'_eq_of {s : Finset κ} (h : s.Nonempty) {m : κ} (hm : m ∈ s) (hle : ∀ x ∈ s, m ≤ x) :
    s.min' h = m :=
  le_antisymm (Finset.min'_le _ _ hm) (Finset.le_min' _ _ _ hle)

private theorem max'_eq_of {s : Finset κ} (h : s.Nonempty) {m : κ} (hm : m ∈ s) (hle : ∀ x ∈ s, x ≤ m) :
    s.max' h = m :=
  le_antisymm (Finset.max'_le _ _ _ hle) (Finset.le_max' _ _ hm)

private theorem mp_homOf_eq {p : ℕ} (y : CC F p) (s t : {s : Finset κ // s.card = p + 1}) (e : s.1 = t.1)
    (h : s.1 ⊆ t.1) :
    mp F (homOf (a := ne s.1 (card_nonempty s)) (b := ne t.1 (card_nonempty t)) h) (y s) = y t := by
  obtain ⟨s, hs⟩ := s
  obtain ⟨t, ht⟩ := t
  simp only at e
  subst e
  exact mp_id F _ _

private theorem e2_of_not (y : CC F 2) {a b d : (NE κ)ᵒᵖ} (φ : a ⟶ b) (ψ : b ⟶ d)
    (h : ¬ (mn d < mn b ∧ mn b < mn a)) : e2 F y a b d φ ψ = 0 := by
  simp [e2, h]

private theorem e2_of_lt (y : CC F 2) (t : {s : Finset κ // s.card = 2 + 1}) {a b : (NE κ)ᵒᵖ} (φ : a ⟶ b)
    (ψ : b ⟶ ne t.1 (card_nonempty t)) (h₁ : mn (ne t.1 (card_nonempty t)) < mn b) (h₂ : mn b < mn a) :
    e2 F y a b _ φ ψ = - y t := by
  simp only [e2, LinearMap.pi_apply, dif_pos (And.intro h₁ h₂), LinearMap.neg_apply,
    LinearMap.comp_apply, LinearMap.proj_apply, AlgHom.toLinearMap_apply]
  congr 1
  exact mp_homOf_eq F y ⟨_, card_three h₁ h₂⟩ t
    (Finset.eq_of_subset_of_card_le (triple_subset φ ψ) (by rw [t.2, card_three h₁ h₂]))
    (triple_subset φ ψ)

private theorem f_single (f : C1 F) {m x : κ} (e : m = x) {T : (NE κ)ᵒᵖ}
    (φ : ne {m} (Finset.singleton_nonempty m) ⟶ T) (hx : ({x} : Finset κ) ⊆ sub T) :
    f _ T φ = f (ne {x} (Finset.singleton_nonempty x)) T (homOf hx) := by
  subst e; rfl

def cechOfPosetOne (f : C1 F) : CC F 1 := fun P =>
  f (ne {P.1.min' (card_nonempty P)} (Finset.singleton_nonempty _)) (ne P.1 (card_nonempty P))
      (homOf (Finset.singleton_subset_iff.2 (Finset.min'_mem _ _))) -
    f (ne {P.1.max' (card_nonempty P)} (Finset.singleton_nonempty _)) (ne P.1 (card_nonempty P))
      (homOf (Finset.singleton_subset_iff.2 (Finset.max'_mem _ _)))

variable {F}

private theorem restrict_of_d1 {y : CC F 2} {f : C1 F} (hf : e2 F y = d1 F f) {a P T : (NE κ)ᵒᵖ}
    (φ : a ⟶ P) (ψ : P ⟶ T) :
    mp F ψ (f a P φ) = f a T (φ ≫ ψ) - f P T ψ + e2 F y a P T φ ψ := by
  have := congrFun (congrFun (congrFun (congrFun (congrFun hf a) P) T) φ) ψ
  rw [d1_apply] at this
  rw [this]; abel

theorem restrict_cechOfPosetOne {y : CC F 2} {f : C1 F} (hf : e2 F y = d1 F f)
    (P : {s : Finset κ // s.card = 1 + 1}) (T : (NE κ)ᵒᵖ) (h : P.1 ⊆ sub T) :
    mp F (homOf (a := ne P.1 (card_nonempty P)) (b := T) h) (cechOfPosetOne F f P) =
      f (ne {P.1.min' (card_nonempty P)} (Finset.singleton_nonempty _)) T
        (homOf (b := ne P.1 (card_nonempty P)) (Finset.singleton_subset_iff.2 (Finset.min'_mem _ _)) ≫ homOf h) -
      f (ne {P.1.max' (card_nonempty P)} (Finset.singleton_nonempty _)) T
        (homOf (b := ne P.1 (card_nonempty P)) (Finset.singleton_subset_iff.2 (Finset.max'_mem _ _)) ≫ homOf h) +
      e2 F y (ne {P.1.min' (card_nonempty P)} (Finset.singleton_nonempty _)) (ne P.1 (card_nonempty P)) T
        (homOf (Finset.singleton_subset_iff.2 (Finset.min'_mem _ _))) (homOf h) -
      e2 F y (ne {P.1.max' (card_nonempty P)} (Finset.singleton_nonempty _)) (ne P.1 (card_nonempty P)) T
        (homOf (Finset.singleton_subset_iff.2 (Finset.max'_mem _ _))) (homOf h) := by
  simp only [cechOfPosetOne, map_sub]
  rw [restrict_of_d1 hf, restrict_of_d1 hf]
  abel

private theorem e2_min_single (y : CC F 2) (P : {s : Finset κ // s.card = 1 + 1}) (T : (NE κ)ᵒᵖ)
    (φ : ne {P.1.min' (card_nonempty P)} (Finset.singleton_nonempty _) ⟶ ne P.1 (card_nonempty P))
    (ψ : ne P.1 (card_nonempty P) ⟶ T) :
    e2 F y _ _ T φ ψ = 0 :=
  e2_of_not F y φ ψ (fun h => (lt_irrefl _) (h.2.trans_eq (Finset.min'_singleton _).symm))

private theorem e2_max_single_of_le (y : CC F 2) (P : {s : Finset κ // s.card = 1 + 1}) (T : (NE κ)ᵒᵖ)
    (φ : ne {P.1.max' (card_nonempty P)} (Finset.singleton_nonempty _) ⟶ ne P.1 (card_nonempty P))
    (ψ : ne P.1 (card_nonempty P) ⟶ T) (h : ¬ mn T < P.1.min' (card_nonempty P)) :
    e2 F y _ _ T φ ψ = 0 :=
  e2_of_not F y φ ψ (fun h' => h h'.1)

private theorem e2_max_single_of_lt (y : CC F 2) (P : {s : Finset κ // s.card = 1 + 1})
    (t : {s : Finset κ // s.card = 2 + 1})
    (φ : ne {P.1.max' (card_nonempty P)} (Finset.singleton_nonempty _) ⟶ ne P.1 (card_nonempty P))
    (ψ : ne P.1 (card_nonempty P) ⟶ ne t.1 (card_nonempty t))
    (h : mn (ne t.1 (card_nonempty t)) < P.1.min' (card_nonempty P)) :
    e2 F y _ _ _ φ ψ = - y t :=
  e2_of_lt F y t φ ψ h (by
    rw [mn_ne, mn_ne, Finset.min'_singleton]
    exact Finset.min'_lt_max'_of_card _ (by rw [P.2]; omega))

theorem delta_cechOfPosetOne_of_eq {y : CC F 2} {f : C1 F} (hf : e2 F y = d1 F f)
    (t : {s : Finset κ // s.card = 2 + 1}) {i j k : κ} (hij : i < j) (hjk : j < k)
    (ht : t.1 = {i, j, k}) : δ F 1 (cechOfPosetOne F f) t = y t := by
  have hik := hij.trans hjk
  have hi : i ∈ t.1 := by rw [ht]; simp
  have hj : j ∈ t.1 := by rw [ht]; simp
  have hk : k ∈ t.1 := by rw [ht]; simp
  have huniv : (Finset.univ : Finset t.1) = {⟨i, hi⟩, ⟨j, hj⟩, ⟨k, hk⟩} := by
    ext ⟨x, hx⟩
    have hx' := hx
    rw [ht] at hx'
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq, true_iff]
    simpa using hx'
  rw [δ_apply, huniv, Finset.sum_insert (by simp [hij.ne, hik.ne]), Finset.sum_insert (by simp [hjk.ne]),
    Finset.sum_singleton]
  erw [restrict_cechOfPosetOne hf, restrict_cechOfPosetOne hf, restrict_cechOfPosetOne hf]
  all_goals first | exact Finset.erase_subset _ _ | skip
  have hle : ∀ x ∈ t.1, i ≤ x := by
    intro x hx
    rw [ht] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    exacts [le_rfl, hij.le, hik.le]
  have tmin : mn (ne t.1 (card_nonempty t)) = i := min'_eq_of _ hi hle
  have mem3 : ∀ {x z : κ}, z ∈ t.1.erase x ↔ z ≠ x ∧ (z = i ∨ z = j ∨ z = k) := by
    intro x z; rw [ht]; simp
  have iMin : ∀ h, (Cube.eraseIdx t ⟨i, hi⟩).1.min' h = j := fun h =>
    min'_eq_of h (mem3.2 ⟨hij.ne', by simp⟩) (fun z hz => by
      obtain ⟨hne, rfl | rfl | rfl⟩ := mem3.1 hz
      exacts [absurd rfl hne, le_rfl, hjk.le])
  have iMax : ∀ h, (Cube.eraseIdx t ⟨i, hi⟩).1.max' h = k := fun h =>
    max'_eq_of h (mem3.2 ⟨hik.ne', by simp⟩) (fun z hz => by
      obtain ⟨hne, rfl | rfl | rfl⟩ := mem3.1 hz
      exacts [absurd rfl hne, hjk.le, le_rfl])
  have jMin : ∀ h, (Cube.eraseIdx t ⟨j, hj⟩).1.min' h = i := fun h =>
    min'_eq_of h (mem3.2 ⟨hij.ne, by simp⟩) (fun z hz => by
      obtain ⟨hne, rfl | rfl | rfl⟩ := mem3.1 hz
      exacts [le_rfl, absurd rfl hne, hik.le])
  have jMax : ∀ h, (Cube.eraseIdx t ⟨j, hj⟩).1.max' h = k := fun h =>
    max'_eq_of h (mem3.2 ⟨hjk.ne', by simp⟩) (fun z hz => by
      obtain ⟨hne, rfl | rfl | rfl⟩ := mem3.1 hz
      exacts [hik.le, absurd rfl hne, le_rfl])
  have kMin : ∀ h, (Cube.eraseIdx t ⟨k, hk⟩).1.min' h = i := fun h =>
    min'_eq_of h (mem3.2 ⟨hik.ne, by simp⟩) (fun z hz => by
      obtain ⟨hne, rfl | rfl | rfl⟩ := mem3.1 hz
      exacts [le_rfl, hij.le, absurd rfl hne])
  have kMax : ∀ h, (Cube.eraseIdx t ⟨k, hk⟩).1.max' h = j := fun h =>
    max'_eq_of h (mem3.2 ⟨hjk.ne, by simp⟩) (fun z hz => by
      obtain ⟨hne, rfl | rfl | rfl⟩ := mem3.1 hz
      exacts [hij.le, le_rfl, absurd rfl hne])
  have hiT : ({i} : Finset κ) ⊆ sub (ne t.1 (card_nonempty t)) := Finset.singleton_subset_iff.2 hi
  have hjT : ({j} : Finset κ) ⊆ sub (ne t.1 (card_nonempty t)) := Finset.singleton_subset_iff.2 hj
  have hkT : ({k} : Finset κ) ⊆ sub (ne t.1 (card_nonempty t)) := Finset.singleton_subset_iff.2 hk
  have lI : mn (ne t.1 (card_nonempty t)) <
      (Cube.eraseIdx t ⟨i, hi⟩).1.min' (card_nonempty (Cube.eraseIdx t ⟨i, hi⟩)) := by
    rw [tmin, iMin]; exact hij
  have lJ : ¬ mn (ne t.1 (card_nonempty t)) <
      (Cube.eraseIdx t ⟨j, hj⟩).1.min' (card_nonempty (Cube.eraseIdx t ⟨j, hj⟩)) := by
    rw [tmin, jMin]; exact lt_irrefl _
  have lK : ¬ mn (ne t.1 (card_nonempty t)) <
      (Cube.eraseIdx t ⟨k, hk⟩).1.min' (card_nonempty (Cube.eraseIdx t ⟨k, hk⟩)) := by
    rw [tmin, kMin]; exact lt_irrefl _
  have sI : cubeSign t.1 i = 1 := cubeSign_eq_one_of_forall_le hle
  have sJ : cubeSign t.1 j = -1 := by
    rw [cubeSign, ht, Finset.filter_insert, Finset.filter_insert, Finset.filter_singleton]
    simp [hij, hjk.not_gt, lt_irrefl]
  have sK : cubeSign t.1 k = 1 := by
    rw [cubeSign, ht, Finset.filter_insert, Finset.filter_insert, Finset.filter_singleton]
    simp [hik, hjk, lt_irrefl, Finset.card_pair hij.ne]
  erw [e2_min_single y (Cube.eraseIdx t ⟨i, hi⟩) (ne t.1 (card_nonempty t)),
    e2_min_single y (Cube.eraseIdx t ⟨j, hj⟩) (ne t.1 (card_nonempty t)),
    e2_min_single y (Cube.eraseIdx t ⟨k, hk⟩) (ne t.1 (card_nonempty t)),
    e2_max_single_of_lt y (Cube.eraseIdx t ⟨i, hi⟩) t _ _ lI,
    e2_max_single_of_le y (Cube.eraseIdx t ⟨j, hj⟩) _ _ _ lJ,
    e2_max_single_of_le y (Cube.eraseIdx t ⟨k, hk⟩) _ _ _ lK,
    f_single F f (iMin _) _ hjT, f_single F f (iMax _) _ hkT,
    f_single F f (jMin _) _ hiT, f_single F f (jMax _) _ hkT,
    f_single F f (kMin _) _ hiT, f_single F f (kMax _) _ hjT]
  erw [sI, sJ, sK]
  simp only [one_smul, neg_smul, sub_zero, add_zero, sub_neg_eq_add]
  abel

end GlobalTheory.CechPoset

namespace GlobalTheory.CechPoset

theorem exists_cech_coboundary_of_degreeTwo_image_coboundary : ∀ {κ : Type} [LinearOrder κ] {R : Type} [CommRing R]
    (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R) (y : CC F 2), δ F 2 y = 0 → ∀ f : C1 F, e2 F y = d1 F f →
      ∃ c : CC F 1, δ F 1 c = y := by
  intro κ _ R _ F y _ f hf
  refine ⟨cechOfPosetOne F f, funext fun (t : {s : Finset κ // s.card = 2 + 1}) => ?_⟩
  obtain ⟨a, b, d, hab, had, hbd, ht⟩ := Finset.card_eq_three.1 t.2
  rcases lt_or_gt_of_ne hab with h₁ | h₁ <;> rcases lt_or_gt_of_ne had with h₂ | h₂ <;>
    rcases lt_or_gt_of_ne hbd with h₃ | h₃
  all_goals first
    | exact delta_cechOfPosetOne_of_eq hf t (by assumption : a < b) (by assumption : b < d)
        (ht.trans (by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; try tauto))
    | exact delta_cechOfPosetOne_of_eq hf t (by assumption : a < d) (by assumption : d < b)
        (ht.trans (by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; try tauto))
    | exact delta_cechOfPosetOne_of_eq hf t (by assumption : b < a) (by assumption : a < d)
        (ht.trans (by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; try tauto))
    | exact delta_cechOfPosetOne_of_eq hf t (by assumption : b < d) (by assumption : d < a)
        (ht.trans (by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; try tauto))
    | exact delta_cechOfPosetOne_of_eq hf t (by assumption : d < a) (by assumption : a < b)
        (ht.trans (by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; try tauto))
    | exact delta_cechOfPosetOne_of_eq hf t (by assumption : d < b) (by assumption : b < a)
        (ht.trans (by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; try tauto))
    | exact (lt_irrefl _ ((h₁.trans h₃).trans h₂)).elim
    | exact (lt_irrefl _ ((h₁.trans h₂).trans h₃)).elim

end GlobalTheory.CechPoset
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechCoboundaryOfDegreeTwoImageCoboundaryAlStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cech_coboundary_of_degreeTwo_image_coboundary' : ∀ {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R) (y : CC F 2), δ F 2 y = 0 → ∀ f : C1 F, e2 F y = d1 F f → ∃ c : CC F 1, δ F 1 c = y := by
  first | exact @GlobalTheory.CechPoset.exists_cech_coboundary_of_degreeTwo_image_coboundary | exact GlobalTheory.CechPoset.exists_cech_coboundary_of_degreeTwo_image_coboundary | (intros; apply GlobalTheory.CechPoset.exists_cech_coboundary_of_degreeTwo_image_coboundary <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeTrivialBundleCechDifferentialComm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeTrivialBundleCechDifferentialComm
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

namespace GlobalTheory.CechPoset

theorem trivCoord_restrict {X X' : Scheme.{0}} {R' : Type} [CommRing R'] (φ : X' ⟶ X) (s' : X' ⟶ Sp R')
    {V W : X'.Opens} (h : W ≤ V) (x : GlobalTheory.AbLaw.SecOnR s' ((LB.triv X).pull φ) V) :
    trivCoord φ s' W (GlobalTheory.AbLaw.SecOnR.restrict s' _ h x) = Sec.res s' h (trivCoord φ s' V x) := by
  simp only [trivCoord, LinearMap.coe_mk, AddHom.coe_mk, GlobalTheory.AbLaw.SecOnR.coord_restrict]
  change (X'.presheaf.map _ ≫ X'.presheaf.map _).hom _ = (X'.presheaf.map _ ≫ X'.presheaf.map _).hom _
  rw [← Functor.map_comp, ← Functor.map_comp]; rfl

theorem Φ_apply {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {X X' : Scheme.{0}} {s : X ⟶ Sp R}
    {s' : X' ⟶ Sp R'} {φ : X' ⟶ X} (w : φ ≫ s = s' ≫ spMap (algebraMap R R')) {κ : Type} [LinearOrder κ]
    (D : κ → X.Opens) (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, φ ⁻¹ᵁ D i)) (q : ℕ)
    (x : R' ⊗[R] (GlobalTheory.AbLaw.cechLB s (LB.triv X) D).X q)
    (t : {s : Finset κ // s.card = q + 1}) :
    Φ w D hD' q x t = trivCoord φ s' (⨅ i ∈ t.1, φ ⁻¹ᵁ D i) (GlobalTheory.AbLaw.secTermBaseChange (LB.triv X) D w (q + 1) x t) :=
  rfl

theorem trivCoord_d {R' : Type} [CommRing R'] {X X' : Scheme.{0}} {s' : X' ⟶ Sp R'} (φ : X' ⟶ X) {κ : Type}
    [LinearOrder κ] (D : κ → X.Opens) (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, φ ⁻¹ᵁ D i))
    (p : ℕ) (y : GlobalTheory.Cube.Term (GlobalTheory.AbLaw.secCube s' ((LB.triv X).pull φ) fun i => φ ⁻¹ᵁ D i) (p + 1))
    (t : {s : Finset κ // s.card = p + 1 + 1}) :
    trivCoord φ s' (⨅ i ∈ t.1, φ ⁻¹ᵁ D i) (GlobalTheory.Cube.d _ (p + 1) y t) =
      δ (covF s' (fun i => φ ⁻¹ᵁ D i) hD') p (fun u => trivCoord φ s' (⨅ i ∈ u.1, φ ⁻¹ᵁ D i) (y u)) t := by
  refine (congrArg (trivCoord φ s' (⨅ i ∈ t.1, φ ⁻¹ᵁ D i)) (GlobalTheory.Cube.d_apply _ (p + 1) y t)).trans ?_
  refine ((map_sum (trivCoord φ s' (⨅ i ∈ t.1, φ ⁻¹ᵁ D i)) _ _)).trans ?_
  refine Eq.trans ?_ (δ_apply (covF s' (fun i => φ ⁻¹ᵁ D i) hD') p _ t).symm
  refine Finset.sum_congr rfl fun i _ => ?_
  refine (map_zsmul (trivCoord φ s' (⨅ i ∈ t.1, φ ⁻¹ᵁ D i)) _ _).trans ?_
  congr 1
  exact trivCoord_restrict φ s' _ _

theorem Φ_dB : ∀ {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X} (w : φ ≫ s = s' ≫ spMap (algebraMap R R')) {κ : Type} [LinearOrder κ] (D : κ → X.Opens) (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, φ ⁻¹ᵁ D i)) (p : ℕ) (x : R' ⊗[R] (GlobalTheory.AbLaw.cechLB s (LB.triv X) D).X p), Φ w D hD' (p + 1) (dB (GlobalTheory.AbLaw.cechLB s (LB.triv X) D) R' p (p + 1) x) = δ _ p (Φ w D hD' p x) := by
  intro R R' _ _ _ X X' s s' φ w κ _ D hD' p x
  have e1 : dB (GlobalTheory.AbLaw.cechLB s (LB.triv X) D) R' p (p + 1) x =
      (GlobalTheory.Cube.d (GlobalTheory.AbLaw.secCube s (LB.triv X) D) (p + 1)).baseChange R' x := by
    simp only [dB, GlobalTheory.AbLaw.cechLB_d]; rfl
  have e2 := GlobalTheory.AbLaw.d_secTermBaseChange (LB.triv X) D w (p + 1) x
  funext t
  refine (Φ_apply w D hD' (p + 1) _ t).trans ?_
  refine (congrArg (fun z => trivCoord φ s' (⨅ i ∈ t.1, φ ⁻¹ᵁ D i)
    (GlobalTheory.AbLaw.secTermBaseChange (LB.triv X) D w (p + 1 + 1) z t)) e1).trans ?_
  refine (congrArg (fun z => trivCoord φ s' (⨅ i ∈ t.1, φ ⁻¹ᵁ D i) (z t)) e2.symm).trans ?_
  exact trivCoord_d φ D hD' p _ t

end GlobalTheory.CechPoset
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeTrivialBundleCechDifferentialCommStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseChangeTrivialBundleCech_differential_comm : ∀ {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X} (w : φ ≫ s = s' ≫ spMap (algebraMap R R')) {κ : Type} [LinearOrder κ] (D : κ → X.Opens) (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, φ ⁻¹ᵁ D i)) (p : ℕ) (x : R' ⊗[R] (GlobalTheory.AbLaw.cechLB s (LB.triv X) D).X p), Φ w D hD' (p + 1) (dB (GlobalTheory.AbLaw.cechLB s (LB.triv X) D) R' p (p + 1) x) = δ _ p (Φ w D hD' p x) := by
  first | exact @GlobalTheory.CechPoset.Φ_dB | exact GlobalTheory.CechPoset.Φ_dB | (intros; apply GlobalTheory.CechPoset.Φ_dB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechH1PullbackRefinementCompat
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechH1PullbackRefinementCompat
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh

namespace GlobalTheory.CechPoset

theorem pr_monotone {κ : Type} [LinearOrder κ] {X' X'' : Scheme.{0}} {ψ : X'' ⟶ X'} (D' : κ → X'.Opens)
    (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D' i)) (D'' : κ → X''.Opens)
    (hD'' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D'' i)) (hle : ∀ i, D'' i ≤ ψ ⁻¹ᵁ D' i) :
    Monotone (pr D' hD' D'' hD'' hle) := fun _ _ h =>
  Subtype.mk_le_mk.2 (Prod.mk_le_mk.2 ⟨cov_mono D'' hD'' h, cov_mono D' hD' h⟩)

theorem restrict_pull1_pullHO1 {R' R'' : Type} [CommRing R'] [CommRing R''] {X' X'' : Scheme.{0}}
    {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {σ : R' →+* R''} {ψ : X'' ⟶ X'}
    (w : ψ ≫ s' = s'' ≫ spMap σ) {κ : Type} [LinearOrder κ] (D' : κ → X'.Opens)
    (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D' i)) (D'' : κ → X''.Opens)
    (hD'' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D'' i)) (hle : ∀ i, D'' i ≤ ψ ⁻¹ᵁ D' i)
    (y : HO1 s') :
    (CoefMap.restrict (OAff s'') (cov_mono D'' hD'').functor.op).pull1 (pullHO1 w y) =
      (pullCoef w D' hD' D'' hD'' hle).pull1
        ((CoefMap.restrict (OAff s') (cov_mono D' hD').functor.op).pull1 y) := by
  have hp : (pairPull w).pull1 y = (pairRes ψ s'').pull1 (pullHO1 w y) := isPullO_pullHO1 w y
  generalize pullHO1 w y = z at hp
  let n := CoefMap.restrict (OPair ψ s'') (pr_monotone D' hD' D'' hD'' hle).functor.op
  have h1 : (CoefMap.restrict (OAff s'') (cov_mono D'' hD'').functor.op).pull1 z =
      n.pull1 ((pairRes ψ s'').pull1 z) := by
    refine Eq.trans ?_ ((pairRes ψ s'').pullCohomologyOne_comp n z)
    exact CoefMap.pullCohomologyOne_eq_of_natTrans _ ((pairRes ψ s'').comp n) { app U := 𝟙 _ }
      (fun U b ↦ mp_id (OAff s'') _ b) z
  rw [h1, ← hp]
  refine ((pairPull w).pullCohomologyOne_comp n y).symm.trans (Eq.trans ?_ (CoefMap.pullCohomologyOne_comp _ _ y))
  exact CoefMap.pullCohomologyOne_eq_of_natTrans _ _ { app U := 𝟙 _ } (fun U b ↦ by erw [mp_id]) y

end GlobalTheory.CechPoset
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechH1PullbackRefinementCompatStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_h1_pullback_refinement_compat : ∀ {R' R'' : Type} [CommRing R'] [CommRing R''] {X' X'' : Scheme.{0}} {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {σ : R' →+* R''} {ψ : X'' ⟶ X'} (w : ψ ≫ s' = s'' ≫ spMap σ) {κ : Type} [LinearOrder κ] (D' : κ → X'.Opens) (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D' i)) (D'' : κ → X''.Opens) (hD'' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D'' i)) (hle : ∀ i, D'' i ≤ ψ ⁻¹ᵁ D' i) (y : HO1 s'), (CoefMap.restrict (OAff s'') (cov_mono D'' hD'').functor.op).pull1 (pullHO1 w y) = (pullCoef w D' hD' D'' hD'' hle).pull1 ((CoefMap.restrict (OAff s') (cov_mono D' hD').functor.op).pull1 y) := by
  first | exact @GlobalTheory.CechPoset.restrict_pull1_pullHO1 | exact GlobalTheory.CechPoset.restrict_pull1_pullHO1 | (intros; apply GlobalTheory.CechPoset.restrict_pull1_pullHO1 <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderedCechFiniteAffineCoverModelsStructureSheaf
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CechPoset

theorem orderedCech_toCat_differential_zero_comm : ∀ {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R) (c : CC F 0), d0 F (e0 F c) = e1 F (δ F 0 c) := GlobalTheory.T.orderedCechToCatCochainsZero_coboundary_comm
theorem orderedCech_toCat_differential_one_comm : ∀ {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R) (c : CC F 1), d1 F (e1 F c) = e2 F (δ F 1 c) := GlobalTheory.T.orderedCech_cochainsOne_coboundary_comm
theorem orderedCech_degreeTwo_cocycle_mem : ∀ {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R) (c : CC F 2), δ F 2 c = 0 → e2 F c ∈ Z2 F := GlobalTheory.T.alternatingToOrderedCechDegreeTwo_mem_cocyclesTwo
theorem ker0 : ∀ {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R), (∀ c : CC F 0, δ F 0 c = 0 → e0 F c = 0 → c = 0) ∧ ∀ g : C0 F, d0 F g = 0 → ∃ c : CC F 0, δ F 0 c = 0 ∧ e0 F c = g := GlobalTheory.T.orderedCechDegreeZero_cocycles_correspond
theorem h1_surj : ∀ {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R) (f : Z1 F), ∃ z : CC F 1, δ F 1 z = 0 ∧ ∃ g : C0 F, f.1 - e1 F z = d0 F g := GlobalTheory.T.exists_cech_cocycle_cohomologous_posetOneCocycle
theorem h1_inj : ∀ {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R) (z : CC F 1), δ F 1 z = 0 → ∀ g : C0 F, e1 F z = d0 F g → ∃ c : CC F 0, δ F 0 c = z := GlobalTheory.T.exists_cech_primitive_of_image_coboundary
theorem h2_surj : ∀ {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R) (w : Z2 F), ∃ y : CC F 2, δ F 2 y = 0 ∧ ∃ f : C1 F, w.1 - e2 F y = d1 F f := GlobalTheory.T.exists_cocycle_sub_e2_eq_d1
theorem h2_inj : ∀ {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R) (y : CC F 2), δ F 2 y = 0 → ∀ f : C1 F, e2 F y = d1 F f → ∃ c : CC F 1, δ F 1 c = y := GlobalTheory.T.exists_cech_coboundary_of_degreeTwo_image_coboundary'
theorem restrictCompatibleFamilyToIntersections_bijective_affine_cover : ∀ {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) {κ : Type} [LinearOrder κ] [Fintype κ] (D : κ → X.Opens) (hD : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D i)), ⨆ i, D i = ⊤ → Function.Bijective (res0 s D hD) := GlobalTheory.T.res0_bijective_of_affine_intersections_of_iSup_eq_top
theorem Φ_δ : ∀ {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X} (w : φ ≫ s = s' ≫ spMap (algebraMap R R')) {κ : Type} [LinearOrder κ] (D : κ → X.Opens) (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, φ ⁻¹ᵁ D i)) (p : ℕ) (x : R' ⊗[R] (GlobalTheory.AbLaw.cechLB s (LB.triv X) D).X p), Φ w D hD' (p + 1) (dB (GlobalTheory.AbLaw.cechLB s (LB.triv X) D) R' p (p + 1) x) = δ _ p (Φ w D hD' p x) := GlobalTheory.T.baseChangeTrivialBundleCech_differential_comm
theorem Φ_bijective : ∀ {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X} (h : IsPullback φ s' s (spMap (algebraMap R R'))) {κ : Type} [LinearOrder κ] [Fintype κ] (D : κ → X.Opens) (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, φ ⁻¹ᵁ D i)), (∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D i)) → ∀ p : ℕ, Function.Bijective (Φ h.w D hD' p) := GlobalTheory.T.baseChangeTrivialBundleCech_bijective_of_affine
theorem Φ_one : ∀ {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X} (w : φ ≫ s = s' ≫ spMap (algebraMap R R')) {κ : Type} [LinearOrder κ] (D : κ → X.Opens) (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, φ ⁻¹ᵁ D i)), Φ w D hD' 0 ((1 : R') ⊗ₜ[R] one s D) = fun _ => 1 := by
  intro R R' _ _ _ X X' s s' φ w κ _ D hD'
  funext t
  have key : GlobalTheory.AbLaw.SecOnR.coord (f := s') (M := (LB.triv X).pull φ) (GlobalTheory.AbLaw.secTermBaseChange (LB.triv X) D w 1 ((1 : R') ⊗ₜ[R] one s D) t) (i0 φ) = 1 := by
    erw [GlobalTheory.AbLaw.secTermBaseChange_tmul, one_smul]
    refine (GlobalTheory.AbLaw.SecOn.coord_pullLE (M := LB.triv X) φ (GlobalTheory.AbLaw.preimage_biInf D φ t.1).ge ((GlobalTheory.AbLaw.secOnTrivEquiv _).symm 1) (i0 φ)).trans ?_
    have hc : GlobalTheory.LB.coord ((GlobalTheory.AbLaw.secOnTrivEquiv (X := X) (⨅ i ∈ t.1, D i)).symm 1) PUnit.unit = 1 := by
      refine (GlobalTheory.AbLaw.SecOn.coord_chart_symm (M := Out.Inh.trivLB X) (Out.Inh.trivLB_isLB X) PUnit.unit PUnit.unit le_top (1 : Γ(X, ⨅ i ∈ t.1, D i))).trans ?_
      rw [map_one]
      exact (_root_.one_mul _).trans (map_one _)
    exact (congrArg _ hc).trans (map_one _)
  change Sec.res s' _ (GlobalTheory.AbLaw.SecOnR.coord (f := s') (M := (LB.triv X).pull φ) (GlobalTheory.AbLaw.secTermBaseChange (LB.triv X) D w 1 ((1 : R') ⊗ₜ[R] one s D) t) (i0 φ)) = 1
  rw [key]
  exact (Sec.res s' _).map_one
theorem Φ_pull : ∀ {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] [Algebra R R'] [Algebra R R''] {X X' X'' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {φ : X' ⟶ X} {φ' : X'' ⟶ X} (w' : φ ≫ s = s' ≫ spMap (algebraMap R R')) (w'' : φ' ≫ s = s'' ≫ spMap (algebraMap R R'')) (α : R' →ₐ[R] R'') (ψ : X'' ⟶ X') (wψ : ψ ≫ s' = s'' ≫ spMap (α : R' →+* R'')), ψ ≫ φ = φ' → ∀ {κ : Type} [LinearOrder κ] (D : κ → X.Opens) (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, φ ⁻¹ᵁ D i)) (hD'' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, φ' ⁻¹ᵁ D i)) (hle : ∀ i, φ' ⁻¹ᵁ D i ≤ ψ ⁻¹ᵁ (φ ⁻¹ᵁ D i)) (p : ℕ) (z : R' ⊗[R] (GlobalTheory.AbLaw.cechLB s (LB.triv X) D).X p) (t : {s : Finset κ // s.card = p + 1}), Φ w'' D hD'' p (GlobalTheory.AbCoh.ext α _ z) t = (pullCoef wψ (fun i => φ ⁻¹ᵁ D i) hD' (fun i => φ' ⁻¹ᵁ D i) hD'' hle).α (ne t.1 (card_nonempty t)) (Φ w' D hD' p z t) := GlobalTheory.T.baseChangeTrivialBundleCech_pullback_comm
theorem pullHO1_cov : ∀ {R' R'' : Type} [CommRing R'] [CommRing R''] {X' X'' : Scheme.{0}} {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {σ : R' →+* R''} {ψ : X'' ⟶ X'} (w : ψ ≫ s' = s'' ≫ spMap σ) {κ : Type} [LinearOrder κ] (D' : κ → X'.Opens) (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D' i)) (D'' : κ → X''.Opens) (hD'' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D'' i)) (hle : ∀ i, D'' i ≤ ψ ⁻¹ᵁ D' i) (y : HO1 s'), (CoefMap.restrict (OAff s'') (cov_mono D'' hD'').functor.op).pull1 (pullHO1 w y) = (pullCoef w D' hD' D'' hD'' hle).pull1 ((CoefMap.restrict (OAff s') (cov_mono D' hD').functor.op).pull1 y) := GlobalTheory.T.cech_h1_pullback_refinement_compat
theorem pullHO2_cov : ∀ {R' R'' : Type} [CommRing R'] [CommRing R''] {X' X'' : Scheme.{0}} {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {σ : R' →+* R''} {ψ : X'' ⟶ X'} (w : ψ ≫ s' = s'' ≫ spMap σ) {κ : Type} [LinearOrder κ] (D' : κ → X'.Opens) (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D' i)) (D'' : κ → X''.Opens) (hD'' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D'' i)) (hle : ∀ i, D'' i ≤ ψ ⁻¹ᵁ D' i) (y : HO2 s'), (CoefMap.restrict (OAff s'') (cov_mono D'' hD'').functor.op).pull2 (pullHO2 w y) = (pullCoef w D' hD' D'' hD'' hle).pull2 ((CoefMap.restrict (OAff s') (cov_mono D' hD').functor.op).pull2 y) := GlobalTheory.T.cech_h2_pullback_refinement_compat

theorem δ_one : ∀ {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R), δ F 0 (fun _ => 1) = 0 := by
  intro κ _ R _ F
  have hsum : ∀ (t : Finset κ), t.card = 2 → ∑ i ∈ t, GlobalTheory.cubeSign t i = 0 := by
    intro t ht
    have key : ∀ x y : κ, x < y → ∑ i ∈ ({x, y} : Finset κ), GlobalTheory.cubeSign {x, y} i = 0 := by
      intro x y hxy
      rw [Finset.sum_pair hxy.ne]
      simp [GlobalTheory.cubeSign, Finset.filter_insert, Finset.filter_singleton, hxy, hxy.not_gt]
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.1 ht
    rcases lt_or_gt_of_ne hxy with h' | h'
    · exact key x y h'
    · rw [Finset.pair_comm]; exact key y x h'
  funext t
  rw [δ_apply]
  simp only [map_one, Pi.zero_apply]
  rw [← Finset.sum_smul, Finset.sum_coe_sort t.1 (fun i => GlobalTheory.cubeSign t.1 i),
    hsum t.1 t.2, zero_smul]

end GlobalTheory.CechPoset

namespace GlobalTheory.CechPoset

section Assembly

def kerEquiv {R : Type} [CommRing R] {M N M' N' : Type} [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N'] (f : M →ₗ[R] N)
    (g : M' →ₗ[R] N') (a : M →ₗ[R] M') (b : N →ₗ[R] N') (ha : Function.Bijective a)
    (hb : Function.Injective b) (h : ∀ x, b (f x) = g (a x)) :
    LinearMap.ker f ≃ₗ[R] LinearMap.ker g :=
  LinearEquiv.ofBijective (a.restrict fun x hx => by
      rw [LinearMap.mem_ker] at hx ⊢; rw [← h, hx, map_zero])
    ⟨fun x y e => Subtype.ext (ha.1 (congrArg Subtype.val e)), fun y => by
      obtain ⟨x, hx⟩ := ha.2 y.1
      refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
      rw [LinearMap.mem_ker]
      apply hb
      rw [h, hx, map_zero, LinearMap.mem_ker.1 y.2]⟩

variable {κ : Type} [LinearOrder κ]

theorem cov_inf {X : Scheme.{0}} (D : κ → X.Opens) (hD : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D i))
    (I J : NE κ) : (cov D hD (I ⊓ J)).1 = (cov D hD I).1 ⊓ (cov D hD J).1 :=
  Finset.iInf_union

theorem cov_sup {X : Scheme.{0}} (D : κ → X.Opens) (hD : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D i))
    (hc : ⨆ i, D i = ⊤) : ⨆ I, (cov D hD I).1 = ⊤ := by
  refine eq_top_iff.2 (hc.symm.le.trans (iSup_le fun i => ?_))
  refine le_trans (le_of_eq ?_) (le_iSup (fun I => (cov D hD I).1) (OrderDual.toDual ⟨{i}, Finset.singleton_nonempty i⟩))
  simp [cov]

variable {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) [Fintype κ] (D : κ → X.Opens)

omit [Fintype κ] in
theorem preimage_sup {X' : Scheme.{0}} (φ : X' ⟶ X) (hc : ⨆ i, D i = ⊤) :
    ⨆ i, φ ⁻¹ᵁ D i = ⊤ := by
  rw [← Scheme.Hom.preimage_iSup, hc]; rfl

variable (hD : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D i)) (hc : ⨆ i, D i = ⊤)

variable {R' : Type} [CommRing R'] [Algebra R R'] {X' : Scheme.{0}} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X}
  (h : IsPullback φ s' s (spMap (algebraMap R R')))

omit [Fintype κ] in
include h hD in
theorem hDp : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, φ ⁻¹ᵁ D i) :=
  fun _ hI => GlobalTheory.AbLaw.isAffineOpen_biInf_preimage h (hD _ hI)

def rst1 : HO1 s' ≃ₗ[R'] CatCoh.H1 (covF s' (fun i => φ ⁻¹ᵁ D i) (hDp s D hD h)) :=
  LinearEquiv.ofBijective (CoefMap.restrict (OAff s') (cov_mono _ (hDp s D hD h)).functor.op).pull1
    (GlobalTheory.T.cech_pull_one_bijective_lattice_cover R' X' s' (NE κ) (cov _ (hDp s D hD h)) (cov_mono _ _) (cov_inf _ _)
      (cov_sup _ _ (preimage_sup D φ hc)))

def rst2 : HO2 s' ≃ₗ[R'] CatCoh.H2 (covF s' (fun i => φ ⁻¹ᵁ D i) (hDp s D hD h)) :=
  LinearEquiv.ofBijective (CoefMap.restrict (OAff s') (cov_mono _ (hDp s D hD h)).functor.op).pull2
    (GlobalTheory.T.restrict_finite_affineCover_infClosed_pull2_bijective R' X' s' (NE κ) (cov _ (hDp s D hD h)) (cov_mono _ _) (cov_inf _ _)
      (cov_sup _ _ (preimage_sup D φ hc)))

abbrev KK := GlobalTheory.AbLaw.cechLB s (LB.triv X) D

def kerΦ (p : ℕ) : LinearMap.ker (dB (KK s D) R' p (p + 1)) ≃ₗ[R']
    LinearMap.ker (δ (covF s' (fun i => φ ⁻¹ᵁ D i) (hDp s D hD h)) p) :=
  kerEquiv _ _ (Φ h.w D (hDp s D hD h) p) (Φ h.w D (hDp s D hD h) (p + 1))
    (Φ_bijective h D _ hD p) (Φ_bijective h D _ hD (p + 1)).1 (Φ_δ h.w D _ p)

def θ0 : LinearMap.ker (dB (KK s D) R' 0 1) ≃ₗ[R'] LinearMap.ker (d0 (OAff s')) :=
  (kerΦ s D hD h 0).trans ((LinearEquiv.ofBijective
    ((e0 _).restrict (p := LinearMap.ker (δ _ 0)) (q := LinearMap.ker (d0 _)) fun c hc => by
      rw [LinearMap.mem_ker] at hc ⊢; rw [orderedCech_toCat_differential_zero_comm, hc, map_zero])
    ⟨fun x y e => by
      have := (ker0 _).1 (x.1 - y.1) (by rw [map_sub, x.2, y.2, sub_zero])
        (by rw [map_sub]; exact sub_eq_zero.2 (congrArg Subtype.val e))
      exact Subtype.ext (sub_eq_zero.1 this),
     fun g => by
      obtain ⟨c, hc, e⟩ := (ker0 _).2 g.1 g.2
      exact ⟨⟨c, hc⟩, Subtype.ext e⟩⟩).trans
    (LinearEquiv.ofBijective (res0 s' _ (hDp s D hD h)) (restrictCompatibleFamilyToIntersections_bijective_affine_cover s' _ _ (preimage_sup D φ hc))).symm)

def θ1 : LinearMap.ker (dB (KK s D) R' 1 2) →ₗ[R'] HO1 s' :=
  (rst1 s D hD hc h).symm.toLinearMap ∘ₗ H1.mk _ ∘ₗ
    ((e1 _ ∘ₗ (LinearMap.ker (δ _ 1)).subtype ∘ₗ (kerΦ s D hD h 1).toLinearMap).codRestrict (Z1 _) fun z => by
      rw [commAlgFunctorCocyclesOne_eq_ker, LinearMap.mem_ker]
      simp only [LinearMap.comp_apply, Submodule.subtype_apply]
      rw [orderedCech_toCat_differential_one_comm]
      exact (congrArg (e2 _) (LinearMap.mem_ker.1 ((kerΦ s D hD h 1) z).2)).trans (map_zero _))

def θ2 : LinearMap.ker (dB (KK s D) R' 2 3) →ₗ[R'] HO2 s' :=
  (rst2 s D hD hc h).symm.toLinearMap ∘ₗ H2.mk _ ∘ₗ
    ((e2 _ ∘ₗ (LinearMap.ker (δ _ 2)).subtype ∘ₗ (kerΦ s D hD h 2).toLinearMap).codRestrict (Z2 _) fun z =>
      orderedCech_degreeTwo_cocycle_mem _ _ (LinearMap.mem_ker.1 ((kerΦ s D hD h 2) z).2))

theorem orderedCech_restrictionOne_comparison (z : LinearMap.ker (dB (KK s D) R' 1 2)) :
    rst1 s D hD hc h (θ1 s D hD hc h z) = H1.mk _ ⟨e1 _ (Φ h.w D (hDp s D hD h) 1 z.1), (by
      rw [commAlgFunctorCocyclesOne_eq_ker, LinearMap.mem_ker, orderedCech_toCat_differential_one_comm]
      exact (congrArg (e2 _) (LinearMap.mem_ker.1 ((kerΦ s D hD h 1) z).2)).trans (map_zero _))⟩ :=
  (rst1 s D hD hc h).apply_symm_apply _

theorem orderedCech_restrictionTwo_comparison (z : LinearMap.ker (dB (KK s D) R' 2 3)) :
    rst2 s D hD hc h (θ2 s D hD hc h z) = H2.mk _ ⟨e2 _ (Φ h.w D (hDp s D hD h) 2 z.1),
      orderedCech_degreeTwo_cocycle_mem _ _ (LinearMap.mem_ker.1 ((kerΦ s D hD h 2) z).2)⟩ :=
  (rst2 s D hD hc h).apply_symm_apply _

theorem θ1_exact : Function.Surjective (θ1 s D hD hc h) ∧
    ∀ z, θ1 s D hD hc h z = 0 ↔ z.1 ∈ LinearMap.range (dB (KK s D) R' 0 1) := by
  have hb := fun p => Φ_bijective h D (hDp s D hD h) hD p
  refine ⟨fun y => ?_, fun z => ?_⟩
  · obtain ⟨f, hf⟩ := H1.mk_surjective _ (rst1 s D hD hc h y)
    obtain ⟨w, hw, g, hg⟩ := h1_surj _ f
    refine ⟨(kerΦ s D hD h 1).symm ⟨w, hw⟩, (rst1 s D hD hc h).injective ?_⟩
    rw [orderedCech_restrictionOne_comparison, ← hf, H1.mk_eq_mk]
    refine ⟨-g, ?_⟩
    have e : Φ h.w D (hDp s D hD h) 1 ((kerΦ s D hD h 1).symm ⟨w, hw⟩).1 = w :=
      congrArg Subtype.val ((kerΦ s D hD h 1).apply_symm_apply ⟨w, hw⟩)
    simp only [e, map_neg, ← hg]; abel
  · rw [← (rst1 s D hD hc h).map_eq_zero_iff, orderedCech_restrictionOne_comparison, H1.mk_eq_zero]
    constructor
    · rintro ⟨g, hg⟩
      obtain ⟨c, hc'⟩ := h1_inj _ _ (LinearMap.mem_ker.1 ((kerΦ s D hD h 1) z).2) g hg.symm
      obtain ⟨x, rfl⟩ := (hb 0).2 c
      refine ⟨x, (hb 1).1 ?_⟩
      rw [Φ_δ, hc']; rfl
    · rintro ⟨x, hx⟩
      refine ⟨e0 _ (Φ h.w D (hDp s D hD h) 0 x), ?_⟩
      rw [orderedCech_toCat_differential_zero_comm, ← Φ_δ, hx]

theorem θ2_exact : Function.Surjective (θ2 s D hD hc h) ∧
    ∀ z, θ2 s D hD hc h z = 0 ↔ z.1 ∈ LinearMap.range (dB (KK s D) R' 1 2) := by
  have hb := fun p => Φ_bijective h D (hDp s D hD h) hD p
  refine ⟨fun y => ?_, fun z => ?_⟩
  · obtain ⟨f, hf⟩ := H2.mk_surjective _ (rst2 s D hD hc h y)
    obtain ⟨w, hw, g, hg⟩ := h2_surj _ f
    refine ⟨(kerΦ s D hD h 2).symm ⟨w, hw⟩, (rst2 s D hD hc h).injective ?_⟩
    rw [orderedCech_restrictionTwo_comparison, ← hf, H2.mk_eq_mk]
    refine ⟨-g, ?_⟩
    have e : Φ h.w D (hDp s D hD h) 2 ((kerΦ s D hD h 2).symm ⟨w, hw⟩).1 = w :=
      congrArg Subtype.val ((kerΦ s D hD h 2).apply_symm_apply ⟨w, hw⟩)
    simp only [e, map_neg, ← hg]; abel
  · rw [← (rst2 s D hD hc h).map_eq_zero_iff, orderedCech_restrictionTwo_comparison, H2.mk_eq_zero]
    constructor
    · rintro ⟨g, hg⟩
      obtain ⟨c, hc'⟩ := h2_inj _ _ (LinearMap.mem_ker.1 ((kerΦ s D hD h 2) z).2) g hg.symm
      obtain ⟨x, rfl⟩ := (hb 1).2 c
      refine ⟨x, (hb 2).1 ?_⟩
      rw [Φ_δ, hc']; rfl
    · rintro ⟨x, hx⟩
      refine ⟨e1 _ (Φ h.w D (hDp s D hD h) 1 x), ?_⟩
      rw [orderedCech_toCat_differential_one_comm, ← Φ_δ, hx]

end Assembly

section Nat

variable {κ : Type} [LinearOrder κ]

theorem orderedCechToCatCochainsOne_natural {R R'' : Type} [CommRing R] [CommRing R''] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R)
    (F'' : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R'') (α : ∀ T, F.obj T →+* F''.obj T)
    (hα : ∀ {T T' : (NE κ)ᵒᵖ} (f : T ⟶ T') (b : F.obj T), α T' (mp F f b) = mp F'' f (α T b))
    (c : CC F 1) (a b : (NE κ)ᵒᵖ) (f : a ⟶ b) :
    e1 F'' (fun t => α _ (c t)) a b f = α b (e1 F c a b f) := by
  simp only [e1, LinearMap.pi_apply]
  split_ifs <;> simp [hα]

theorem alternatingToOrderedCechDegreeTwo_natural {R R'' : Type} [CommRing R] [CommRing R''] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R)
    (F'' : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R'') (α : ∀ T, F.obj T →+* F''.obj T)
    (hα : ∀ {T T' : (NE κ)ᵒᵖ} (f : T ⟶ T') (b : F.obj T), α T' (mp F f b) = mp F'' f (α T b))
    (c : CC F 2) (a b d : (NE κ)ᵒᵖ) (f : a ⟶ b) (g : b ⟶ d) :
    e2 F'' (fun t => α _ (c t)) a b d f g = α d (e2 F c a b d f g) := by
  simp only [e2, LinearMap.pi_apply]
  split_ifs <;> simp [hα]

variable {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) [Fintype κ] (D : κ → X.Opens)
  (hD : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D i)) (hc : ⨆ i, D i = ⊤)
  {R' : Type} [CommRing R'] [Algebra R R'] {X' : Scheme.{0}} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X}
  (h : IsPullback φ s' s (spMap (algebraMap R R')))
  {R'' : Type} [CommRing R''] [Algebra R R''] {X'' : Scheme.{0}} {s'' : X'' ⟶ Sp R''} {φ' : X'' ⟶ X}
  (h' : IsPullback φ' s'' s (spMap (algebraMap R R''))) (α : R' →ₐ[R] R'') (ψ : X'' ⟶ X')
  (w : ψ ≫ s' = s'' ≫ spMap (α : R' →+* R'')) (hcomp : ψ ≫ φ = φ')

include hcomp in
theorem hle : ∀ i, φ' ⁻¹ᵁ D i ≤ ψ ⁻¹ᵁ (φ ⁻¹ᵁ D i) := fun i => by subst hcomp; exact le_rfl

include hcomp in
theorem θ1_nat (z : LinearMap.ker (dB (KK s D) R' 1 2)) (z' : LinearMap.ker (dB (KK s D) R'' 1 2))
    (hz : z'.1 = GlobalTheory.AbCoh.ext α _ z.1) :
    θ1 s D hD hc h' z' = pullHO1 w (θ1 s D hD hc h z) := by
  apply (rst1 s D hD hc h').injective
  rw [orderedCech_restrictionOne_comparison]
  change _ = (CoefMap.restrict _ _).pull1 (pullHO1 w _)
  rw [pullHO1_cov w _ (hDp s D hD h) _ (hDp s D hD h') (hle D ψ hcomp)]
  rw [show (CoefMap.restrict (OAff s') (cov_mono _ (hDp s D hD h)).functor.op).pull1 (θ1 s D hD hc h z) =
    rst1 s D hD hc h (θ1 s D hD hc h z) from rfl, orderedCech_restrictionOne_comparison, CoefMap.pullCohomologyOne_class]
  congr 1
  apply Subtype.ext
  funext a b f
  show e1 _ (Φ h'.w D (hDp s D hD h') 1 z'.1) a b f = (pullCoef w _ (hDp s D hD h) _ (hDp s D hD h')
      (hle D ψ hcomp)).α b (e1 _ (Φ h.w D (hDp s D hD h) 1 z.1) a b f)
  have e : Φ h'.w D (hDp s D hD h') 1 z'.1 = fun t => (pullCoef w _ (hDp s D hD h) _ (hDp s D hD h')
      (hle D ψ hcomp)).α _ (Φ h.w D (hDp s D hD h) 1 z.1 t) := by
    rw [hz]; funext t; exact Φ_pull h.w h'.w α ψ w hcomp D _ _ (hle D ψ hcomp) 1 z.1 t
  rw [e]
  exact orderedCechToCatCochainsOne_natural _ _ _ (fun f b => (pullCoef w _ (hDp s D hD h) _ (hDp s D hD h') (hle D ψ hcomp)).naturality f b) _ a b f

include hcomp in
theorem θ2_nat (z : LinearMap.ker (dB (KK s D) R' 2 3)) (z' : LinearMap.ker (dB (KK s D) R'' 2 3))
    (hz : z'.1 = GlobalTheory.AbCoh.ext α _ z.1) :
    θ2 s D hD hc h' z' = pullHO2 w (θ2 s D hD hc h z) := by
  apply (rst2 s D hD hc h').injective
  rw [orderedCech_restrictionTwo_comparison]
  change _ = (CoefMap.restrict _ _).pull2 (pullHO2 w _)
  rw [pullHO2_cov w _ (hDp s D hD h) _ (hDp s D hD h') (hle D ψ hcomp)]
  rw [show (CoefMap.restrict (OAff s') (cov_mono _ (hDp s D hD h)).functor.op).pull2 (θ2 s D hD hc h z) =
    rst2 s D hD hc h (θ2 s D hD hc h z) from rfl, orderedCech_restrictionTwo_comparison, CoefMap.pullCohomologyTwo_class]
  congr 1
  apply Subtype.ext
  funext a b d f g
  show e2 _ (Φ h'.w D (hDp s D hD h') 2 z'.1) a b d f g = (pullCoef w _ (hDp s D hD h) _ (hDp s D hD h')
      (hle D ψ hcomp)).α d (e2 _ (Φ h.w D (hDp s D hD h) 2 z.1) a b d f g)
  have e : Φ h'.w D (hDp s D hD h') 2 z'.1 = fun t => (pullCoef w _ (hDp s D hD h) _ (hDp s D hD h')
      (hle D ψ hcomp)).α _ (Φ h.w D (hDp s D hD h) 2 z.1 t) := by
    rw [hz]; funext t; exact Φ_pull h.w h'.w α ψ w hcomp D _ _ (hle D ψ hcomp) 2 z.1 t
  rw [e]
  exact alternatingToOrderedCechDegreeTwo_natural _ _ _ (fun f b => (pullCoef w _ (hDp s D hD h) _ (hDp s D hD h') (hle D ψ hcomp)).naturality f b) _ a b d f g

end Nat

end GlobalTheory.CechPoset

namespace GlobalTheory.CechPoset

section Main

variable {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) [Fintype κ]
  (D : κ → X.Opens) (hD : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D i)) (hc : ⨆ i, D i = ⊤)
  {R' : Type} [CommRing R'] [Algebra R R'] {X' : Scheme.{0}} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X}
  (h : IsPullback φ s' s (spMap (algebraMap R R')))

include hD h in
theorem one_mem : (1 : R') ⊗ₜ[R] one s D ∈ LinearMap.ker (dB (KK s D) R' 0 1) := by
  rw [LinearMap.mem_ker]
  apply (Φ_bijective h D (hDp s D hD h) hD 1).1
  rw [Φ_δ, Φ_one, δ_one, map_zero]

theorem θ0_one (T : AffOp X') : (θ0 s D hD hc h ⟨_, one_mem s D hD h⟩).1 T = 1 := by
  have h1 : (fun _ => 1 : C0 (OAff s')) ∈ LinearMap.ker (d0 (OAff s')) := by
    rw [LinearMap.mem_ker]; funext T T' f; simp [amitsur_d0_apply]
  suffices e : θ0 s D hD hc h ⟨_, one_mem s D hD h⟩ = ⟨_, h1⟩ from congrArg (fun g => g.1 T) e
  unfold θ0
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.symm_apply_eq]
  apply Subtype.ext
  funext I
  show e0 _ (Φ h.w D (hDp s D hD h) 0 ((1 : R') ⊗ₜ[R] one s D)) I = 1
  rw [Φ_one]
  simp only [e0, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply, AlgHom.toLinearMap_apply, map_one]

end Main

end GlobalTheory.CechPoset

theorem GlobalTheory.CechPoset.model_cechLB : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (κ : Type)
    [LinearOrder κ] [Fintype κ] (D : κ → X.Opens), IsSeparated s → (∀ i, IsAffineOpen (D i)) →
    ⨆ i, D i = ⊤ → Nonempty (Model s (GlobalTheory.AbLaw.cechLB s (LB.triv X) D)) := by
  intro R _ X s κ _ _ D hs hDa hc
  haveI := hs
  have hD : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D i) := fun I hI =>
    GlobalTheory.MumfordSupport.isAffineOpen_biInf_of_isSeparated s hDa I hI
  exact ⟨{
    θ0 := fun h => GlobalTheory.CechPoset.θ0 s D hD hc h
    one := GlobalTheory.CechPoset.one s D
    θ0_one := fun h => ⟨GlobalTheory.CechPoset.one_mem s D hD h, GlobalTheory.CechPoset.θ0_one s D hD hc h⟩
    θ1 := fun h => GlobalTheory.CechPoset.θ1 s D hD hc h
    θ2 := fun h => GlobalTheory.CechPoset.θ2 s D hD hc h
    exact := fun h => ⟨(GlobalTheory.CechPoset.θ1_exact s D hD hc h).1, (GlobalTheory.CechPoset.θ1_exact s D hD hc h).2,
      (GlobalTheory.CechPoset.θ2_exact s D hD hc h).1, (GlobalTheory.CechPoset.θ2_exact s D hD hc h).2⟩
    nat := fun {R'} _ _ {X'} {s'} {φ} h {R''} _ _ {X''} {s''} {φ'} h' α ψ w hcomp => ⟨fun z z' hz => GlobalTheory.CechPoset.θ1_nat s D hD hc h h' α ψ w hcomp z z' hz,
      fun z z' hz => GlobalTheory.CechPoset.θ2_nat s D hD hc h h' α ψ w hcomp z z' hz⟩ }⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderedCechFiniteAffineCoverModelsStructureSheafStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orderedCech_finiteAffineCover_models_structureSheafCohomology : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → X.Opens), IsSeparated s → (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → Nonempty (Model s (GlobalTheory.AbLaw.cechLB s (LB.triv X) D)) := by
  first | exact @GlobalTheory.CechPoset.model_cechLB | exact GlobalTheory.CechPoset.model_cechLB | (intros; apply GlobalTheory.CechPoset.model_cechLB <;> assumption)
end
