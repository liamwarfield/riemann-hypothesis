module

public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.TwistingSheaf
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.CechOrdered
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjTwistLeray
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.CechNaturality.NaturalLeray
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.CechNaturality.Ordered

@[expose] public section

section -- merged from GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology
section -- merged from GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjCechCompute
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry TopologicalSpace CategoryTheory Opposite MvPolynomial

universe u

noncomputable section

open scoped Classical

namespace ProjSpace

variable {A : Type u} [CommRing A] {n : ℕ}

def filterL (S : (Fin (n + 1) → ℤ) → Prop) : Laurent A n →+ Laurent A n where
  toFun ℓ := AddMonoidAlgebra.ofCoeff (ℓ.coeff.filter S)
  map_zero' := by
    apply AddMonoidAlgebra.coeff_injective
    ext m
    simp [Finsupp.filter_apply]
  map_add' ℓ ℓ' := by
    apply AddMonoidAlgebra.coeff_injective
    ext m
    simp only [AddMonoidAlgebra.coeff_add, Finsupp.filter_add]

lemma coeff_filterL (S : (Fin (n + 1) → ℤ) → Prop) (ℓ : Laurent A n) (m : Fin (n + 1) → ℤ) :
    (filterL S ℓ).coeff m = if S m then ℓ.coeff m else 0 :=
  Finsupp.filter_apply _ _ _

lemma coeff_zsmul' (z : ℤ) (ℓ : Laurent A n) (m : Fin (n + 1) → ℤ) :
    (z • ℓ).coeff m = z • ℓ.coeff m := by
  have := map_zsmul (AddMonoidAlgebra.coeffAddEquiv (R := A) (M := Fin (n + 1) → ℤ)) z ℓ
  exact congrArg (fun f : (Fin (n + 1) → ℤ) →₀ A => f m) this

lemma coeff_sum' {α : Type*} (s : Finset α) (f : α → Laurent A n) (m : Fin (n + 1) → ℤ) :
    (∑ a ∈ s, f a).coeff m = ∑ a ∈ s, (f a).coeff m := by
  rw [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]

def IsSel (j : Fin (n + 1)) (m : Fin (n + 1) → ℤ) : Prop := 0 ≤ m j ∧ ∀ j' < j, m j' < 0

lemma exists_isSel {m : Fin (n + 1) → ℤ} (h : ¬ ∀ j, m j < 0) : ∃ j, IsSel j m := by
  push Not at h
  let S := Finset.univ.filter fun j => 0 ≤ m j
  have hS : S.Nonempty := by
    obtain ⟨j, hj⟩ := h
    exact ⟨j, by simp [S, hj]⟩
  refine ⟨S.min' hS, (Finset.mem_filter.mp (S.min'_mem hS)).2, fun j' hj' => ?_⟩
  by_contra hc
  push Not at hc
  exact absurd (S.min'_le j' (by simp [S, hc])) (not_le.mpr hj')

lemma isSel_unique {m : Fin (n + 1) → ℤ} {j j' : Fin (n + 1)} (h : IsSel j m) (h' : IsSel j' m) :
    j = j' := by
  rcases lt_trichotomy j j' with hlt | heq | hgt
  · exact absurd h.1 (not_le.mpr (h'.2 j hlt))
  · exact heq
  · exact absurd h'.1 (not_le.mpr (h.2 j' hgt))

lemma not_allNeg_of_isSel {m : Fin (n + 1) → ℤ} {j : Fin (n + 1)} (h : IsSel j m) :
    ¬ ∀ j, m j < 0 := fun h' => absurd h.1 (not_le.mpr (h' j))

lemma coeff_lval_eq_zero {k : ℤ} {p : ℕ} (σ : Cochain (twistAb A n k) (cover A n) p)
    {i : Fin (p + 1) → Fin (n + 1)} (hi : ¬ Function.Surjective i) {m : Fin (n + 1) → ℤ}
    (hm : ∀ j, m j < 0) : (lval σ i).coeff m = 0 := by
  by_contra h
  have := (lval_mem σ i) m h
  obtain ⟨j, hj⟩ : ∃ j, j ∉ Set.range i := by
    by_contra! hc
    exact hi fun j => hc j
  exact absurd (this.2 j hj) (not_le.mpr (hm j))

theorem exists_d_eq_of_coeff_allNeg {k : ℤ} {p : ℕ}
    (σ : Cochain (twistAb A n k) (cover A n) (p + 1)) (hσ : d _ _ (p + 1) σ = 0)
    (hneg : ∀ i m, (∀ j, m j < 0) → (lval σ i).coeff m = 0) :
    ∃ τ, d _ _ p τ = σ := by
  have hmem : ∀ i : Fin (p + 1) → Fin (n + 1),
      ∑ j, filterL (IsSel j) (lval σ (Fin.cons j i)) ∈ LDeg A (Set.range i) k := by
    intro i
    refine AddSubgroup.sum_mem _ fun j _ => ?_
    intro m hm
    rw [coeff_filterL] at hm
    by_cases hs : IsSel j m
    swap
    · rw [if_neg hs] at hm
      exact absurd rfl hm
    rw [if_pos hs] at hm
    obtain ⟨hsum, hnn⟩ := lval_mem σ (Fin.cons j i) m hm
    refine ⟨hsum, fun j' hj' => ?_⟩
    by_cases hjj : j' = j
    · exact hjj ▸ hs.1
    · refine hnn j' fun ⟨a, ha⟩ => ?_
      cases a using Fin.cases with
      | zero => exact hjj (by simpa using ha.symm)
      | succ a => exact hj' ⟨a, by simpa using ha⟩
  refine ⟨ofL fun i => ⟨_, hmem i⟩, cochain_ext fun i => ?_⟩
  rw [lval_d]
  simp only [lval_ofL]
  apply AddMonoidAlgebra.coeff_injective
  ext m
  simp only [coeff_sum', coeff_zsmul', coeff_filterL]
  by_cases hm : ∀ j, m j < 0
  · rw [hneg i m hm]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [Finset.sum_eq_zero fun j _ => ?_, smul_zero]
    rw [if_neg fun hs => not_allNeg_of_isSel hs hm]
  · obtain ⟨j₀, hj₀⟩ := exists_isSel hm
    have hsel : ∀ (f : Fin (n + 1) → A),
        (∑ j, if IsSel j m then f j else 0) = f j₀ := fun f => by
      rw [Finset.sum_eq_single j₀ (fun j _ hj => if_neg fun hs => hj (isSel_unique hs hj₀))
        (fun h => absurd (Finset.mem_univ _) h), if_pos hj₀]
    simp_rw [hsel]
    have hc := congrArg (fun ℓ => (ℓ : Laurent A n).coeff m) (lval_d σ (Fin.cons j₀ i))
    simp only [hσ, lval_zero, coeff_sum', coeff_zsmul'] at hc
    change (0 : Laurent A n).coeff m = _ at hc
    rw [Fin.sum_univ_succ, cons_comp_succAbove_zero] at hc
    simp only [cons_comp_succAbove_succ, Fin.val_zero, pow_zero, one_smul, Fin.val_succ,
      pow_succ, mul_neg, mul_one, neg_smul, Finset.sum_neg_distrib] at hc
    rw [AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply] at hc
    linear_combination hc

theorem subsingleton_cechH_of_lt {k : ℤ} {q : ℕ} (hq0 : 0 < q) (hqn : q < n) :
    Subsingleton (cechH (twistAb A n k) (cover A n) q) := by
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
  refine subsingleton_of_forall_eq 0 fun c => ?_
  obtain ⟨σ, hσ, rfl⟩ := exists_cls c
  rw [cls_eq_zero_iff, coboundaries_succ]
  refine exists_d_eq_of_coeff_allNeg σ hσ fun i m hm => coeff_lval_eq_zero σ (fun hi => ?_) hm
  have := Fintype.card_le_of_surjective i hi
  simp only [Fintype.card_fin] at this
  omega

theorem subsingleton_cechH_of_gt {k : ℤ} {q : ℕ} (hq : n < q) :
    Subsingleton (cechH (twistAb A n k) (cover A n) q) :=
  CechOrdered.subsingleton_cechH (by simp; omega) (by omega)


variable (n) in
abbrev NegMon (k : ℤ) : Type := {m : Fin (n + 1) → ℤ // (∀ j, m j < 0) ∧ ∑ j, m j = k}

def topCoeff {k : ℤ} : Cochain (twistAb A n k) (cover A n) n →+ (NegMon n k →₀ A) where
  toFun σ := (lval σ id).coeff.subtypeDomain fun e => (∀ j, e j < 0) ∧ ∑ j, e j = k
  map_zero' := by simp
  map_add' σ τ := by simp [Finsupp.subtypeDomain_add]

lemma topCoeff_apply {k : ℤ} (σ : Cochain (twistAb A n k) (cover A n) n) (e : NegMon n k) :
    topCoeff σ e = (lval σ id).coeff e.1 := rfl

lemma filterL_mem_LDeg {s : Set (Fin (n + 1))} {k : ℤ} (S : (Fin (n + 1) → ℤ) → Prop)
    {ℓ : Laurent A n} (h : ℓ ∈ LDeg A s k) : filterL S ℓ ∈ LDeg A s k := by
  intro m hm
  rw [coeff_filterL] at hm
  by_cases hS : S m
  · rw [if_pos hS] at hm
    exact h m hm
  · rw [if_neg hS] at hm
    exact absurd rfl hm

def posPart {k : ℤ} {q : ℕ} (σ : Cochain (twistAb A n k) (cover A n) q) :
    Cochain (twistAb A n k) (cover A n) q :=
  ofL fun i => ⟨filterL (fun e => ¬ ∀ j, e j < 0) (lval σ i), filterL_mem_LDeg _ (lval_mem σ i)⟩

lemma lval_posPart {k : ℤ} {q : ℕ} (σ : Cochain (twistAb A n k) (cover A n) q) (i) :
    lval (posPart σ) i = filterL (fun e => ¬ ∀ j, e j < 0) (lval σ i) := by
  simp [posPart]

lemma d_posPart {k : ℤ} {q : ℕ} (σ : Cochain (twistAb A n k) (cover A n) q) :
    d _ _ q (posPart σ) = posPart (d _ _ q σ) := by
  refine cochain_ext fun i => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [lval_d, lval_posPart, lval_d, map_sum]
  simp only [lval_posPart, map_zsmul]

lemma topCoeff_d {k : ℤ} {q : ℕ} (hq : q + 1 = n) (τ : Cochain (twistAb A n k) (cover A n) q) :
    topCoeff (hq ▸ d _ _ q τ) = 0 := by
  subst hq
  ext e
  rw [topCoeff_apply, lval_d, coeff_sum', Finsupp.coe_zero, Pi.zero_apply]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [coeff_zsmul', coeff_lval_eq_zero τ ?_ e.2.1, smul_zero]
  intro hs
  obtain ⟨b, hb⟩ := hs a
  exact Fin.succAbove_ne a b hb

lemma posPart_zero {k : ℤ} {q : ℕ} : posPart (0 : Cochain (twistAb A n k) (cover A n) q) = 0 :=
  cochain_ext fun i => by rw [lval_posPart, lval_zero, map_zero]

def topMap {k : ℤ} {m : ℕ} :
    cechH (twistAb A (m + 1) k) (cover A (m + 1)) (m + 1) →+ (NegMon (m + 1) k →₀ A) :=
  QuotientAddGroup.lift _ (topCoeff.comp (cocycles _ _ (m + 1)).subtype) (by
    rintro ⟨σ, hσ⟩ hx
    rw [AddSubgroup.mem_addSubgroupOf, coboundaries_succ] at hx
    obtain ⟨τ, hτ⟩ := hx
    change topCoeff σ = 0
    rw [← show d _ _ m τ = σ from hτ]
    exact topCoeff_d rfl τ)

lemma topMap_cls {k : ℤ} {m : ℕ} (σ : Cochain (twistAb A (m + 1) k) (cover A (m + 1)) (m + 1))
    (hσ : d _ _ (m + 1) σ = 0) : topMap (cls σ hσ) = topCoeff σ := rfl

theorem topMap_bijective {k : ℤ} {m : ℕ} :
    Function.Bijective (topMap (A := A) (k := k) (m := m)) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨σ, hσ, rfl⟩ := exists_cls c
    rw [topMap_cls] at hc
    have hneg0 : ∀ e, (∀ j, e j < 0) → (lval σ id).coeff e = 0 := fun e he => by
      by_cases hs : ∑ j, e j = k
      · exact DFunLike.congr_fun hc ⟨e, he, hs⟩
      · by_contra h
        exact hs (lval_mem σ id e h).1
    have hsame : ∀ t, StrictMono t → σ t = posPart σ t := fun t ht => by
      obtain rfl := ht.eq_id
      rw [← theta_lval σ id, ← theta_lval (posPart σ) id]
      congr 1
      apply Subtype.ext
      change lval σ id = lval (posPart σ) id
      rw [lval_posPart]
      apply AddMonoidAlgebra.coeff_injective
      ext e
      rw [coeff_filterL]
      split_ifs with he
      · exact hneg0 e he
      · rfl
    have hcong := CechOrdered.altProj_congr (m + 1) hsame
    have hσp : d _ _ (m + 1) (posPart σ) = 0 := by rw [d_posPart, hσ, posPart_zero]
    obtain ⟨τ, hτ⟩ := exists_d_eq_of_coeff_allNeg (posPart σ) hσp fun i e he => by
      rw [lval_posPart, coeff_filterL, if_neg (not_not_intro he)]
    rw [← CechOrdered.cls_altProj m σ hσ, cls_eq_zero_iff, coboundaries_succ, hcong, ← hτ,
      ← CechOrdered.d_altProj]
    exact ⟨_, rfl⟩
  · intro ν
    let ℓ : Laurent A (m + 1) := ∑ e ∈ ν.support, AddMonoidAlgebra.single e.1 (ν e)
    have hℓ : ∀ i : Fin (m + 2) → Fin (m + 2), Set.range i = Set.univ →
        ℓ ∈ LDeg A (Set.range i) k := fun i h =>
      AddSubgroup.sum_mem _ fun e _ => single_mem_LDeg ⟨e.2.2, fun j hj => (hj (h ▸ Set.mem_univ j)).elim⟩ _
    let σ₀ : Cochain (twistAb A (m + 1) k) (cover A (m + 1)) (m + 1) :=
      ofL fun i => if h : Set.range i = Set.univ then ⟨ℓ, hℓ i h⟩ else 0
    have hσ : d _ _ (m + 1) (CechOrdered.altProj _ _ (m + 1) σ₀) = 0 := by
      rw [CechOrdered.d_altProj, CechOrdered.altProj_eq_zero (by simp)]
    refine ⟨cls _ hσ, ?_⟩
    rw [topMap_cls]
    ext e
    rw [topCoeff_apply]
    have h1 : lval (CechOrdered.altProj _ _ (m + 1) σ₀) id = lval σ₀ id := by
      unfold lval
      rw [CechOrdered.altProj_apply_of_strictMono _ _ strictMono_id]
    rw [h1, lval_ofL, dite_eq_left Set.range_id]
    change (∑ e ∈ ν.support, AddMonoidAlgebra.single e.1 (ν e)).coeff e.1 = ν e
    rw [coeff_sum']
    simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    rw [Finset.sum_eq_single e]
    · simp
    · intro b _ hb
      rw [if_neg fun h => hb (Subtype.ext h)]
    · intro he
      rw [if_pos rfl]
      exact Finsupp.notMem_support_iff.mp he

def cechHTopEquiv (k : ℤ) (m : ℕ) :
    cechH (twistAb A (m + 1) k) (cover A (m + 1)) (m + 1) ≃+ (NegMon (m + 1) k →₀ A) :=
  AddEquiv.ofBijective topMap topMap_bijective

lemma lval_eq_of_cocycle {k : ℤ} (σ : Cochain (twistAb A n k) (cover A n) 0)
    (hσ : d _ _ 0 σ = 0) (j j' : Fin 1 → Fin (n + 1)) : lval σ j = lval σ j' := by
  have h := congrArg (fun τ => lval τ (Fin.cons (j 0) j' : Fin 2 → Fin (n + 1))) hσ
  simp only [lval_d, lval_zero] at h
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  have e0 : (Fin.cons (j 0) j' : Fin 2 → Fin (n + 1)) ∘ (0 : Fin 2).succAbove = j' := by
    funext a; fin_cases a; rfl
  have e1 : (Fin.cons (j 0) j' : Fin 2 → Fin (n + 1)) ∘ (Fin.succ (0 : Fin 1)).succAbove = j := by
    funext a; fin_cases a; rfl
  rw [e0, e1] at h
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ, zero_add, pow_one, neg_smul] at h
  exact (sub_eq_zero.mp ((sub_eq_add_neg _ _).trans h)).symm

lemma range_const_fin_one (j : Fin 1 → Fin (n + 1)) : Set.range j = {j 0} := by
  ext x
  simp only [Set.mem_range, Set.mem_singleton_iff]
  exact ⟨fun ⟨a, ha⟩ => by rw [← ha, Fin.fin_one_eq_zero a], fun h => ⟨0, h.symm⟩⟩

end ProjSpace

end

end GroundTheory.Arith.SchemeCoh
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry TopologicalSpace CategoryTheory Opposite MvPolynomial

universe w' u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace ProjSpace

variable {A : Type u} [CommRing A] {n : ℕ}
  [HasExt.{w'} (Sheaf (Opens.grothendieckTopology (projectiveSpace A n).toTopCat) AddCommGrpCat.{u})]

theorem nonempty_HTop_equiv (k : ℤ) (hn : 0 < n) :
    Nonempty (Sheaf.H.{w'} (modulesAb (twistingSheaf (grading A n) k)) n ≃+
      (NegMon (n := n) k →₀ A)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hCech := nonempty_cechH_equiv_H_twist (𝒜 := grading A (m + 1))
    (fun j => MvPolynomial.X j) (fun j => X_mem j) iSup_stdOpen k (m + 1)
  obtain ⟨e⟩ := hCech
  exact ⟨e.symm.trans (cechHTopEquiv k m)⟩

theorem subsingleton_H (k : ℤ) {q : ℕ} (hq0 : 0 < q) (hqn : q ≠ n) :
    Subsingleton (Sheaf.H.{w'} (modulesAb (twistingSheaf (grading A n) k)) q) := by
  have hCech := nonempty_cechH_equiv_H_twist (𝒜 := grading A n)
    (fun j => MvPolynomial.X j) (fun j => X_mem j) iSup_stdOpen k q
  obtain ⟨e⟩ := hCech
  have hSubsingleton :
      Subsingleton (cechH (twistAb (A := A) (n := n) k) (cover (A := A) (n := n)) q) := by
    rcases Nat.lt_or_gt_of_ne hqn with h | h
    · exact subsingleton_cechH_of_lt hq0 h
    · have hcard : Fintype.card (Fin (n + 1)) ≤ q := by simpa using h
      exact CechOrdered.subsingleton_cechH hcard hq0
  exact @Equiv.subsingleton _ _ e.symm.toEquiv hSubsingleton

end ProjSpace

end

end GroundTheory.Arith.SchemeCoh
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits MonoidalCategory
  MvPolynomial

universe w' u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

section General

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

lemma ι_appTop_toSpecZero (z : 𝒜 0) :
    (Proj.basicOpen 𝒜 1).ι.appTop ((Proj.toSpecZero 𝒜).appTop ((Scheme.ΓSpecIso _).inv z)) =
      (Proj.basicOpen 𝒜 1).topIso.inv
        (Proj.awayToSection 𝒜 1 (HomogeneousLocalization.fromZeroRingHom 𝒜 _ z)) := by
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]
  have h1 : (Proj.basicOpen 𝒜 1).ι ≫ (Proj 𝒜).topIso.inv ≫
      ((Proj 𝒜).isoOfEq (Proj.basicOpen_one 𝒜)).inv = 𝟙 _ := by
    rw [← cancel_mono (Proj.basicOpen 𝒜 1).ι]
    simp
  have h : (Proj.basicOpen 𝒜 1).ι ≫ Proj.toSpecZero 𝒜 = Proj.basicOpenToSpec 𝒜 1 ≫
      Spec.map (CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom 𝒜 _)) := by
    rw [Proj.toSpecZero, reassoc_of% h1]
  rw [h, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    ← CommRingCat.comp_apply (Scheme.ΓSpecIso _).inv, ← Scheme.ΓSpecIso_inv_naturality,
    CommRingCat.comp_apply, Scheme.Hom.appTop, Proj.basicOpenToSpec_app_top]
  simp
  rfl

def projValue {U : (Proj 𝒜).Opens} (s : Γ(Proj 𝒜, U)) (x : Proj 𝒜) (hx : x ∈ U) :
    ProjTwist.Loc 𝒜 x :=
  ((show (ProjectiveSpectrum.Proj.structureSheaf 𝒜).1.obj (op U) from s).1 ⟨x, hx⟩).val

lemma projValue_toSpecZero (z : 𝒜 0) (x : Proj 𝒜) :
    projValue 𝒜 ((Proj.toSpecZero 𝒜).appTop ((Scheme.ΓSpecIso _).inv z)) x trivial =
      algebraMap A _ (z : A) := by
  have hx : x ∈ Proj.basicOpen 𝒜 1 := by rw [Proj.basicOpen_one]; trivial
  have hx' : x ∈ (Proj.basicOpen 𝒜 1).ι ''ᵁ ⊤ := by rw [Scheme.Opens.ι_image_top]; exact hx
  have e := congrArg (fun s => projValue 𝒜 (U := (Proj.basicOpen 𝒜 1).ι ''ᵁ ⊤) s x hx')
    (ι_appTop_toSpecZero 𝒜 z)
  simp only [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_inv] at e
  have e' : projValue 𝒜 ((Proj.toSpecZero 𝒜).appTop ((Scheme.ΓSpecIso _).inv z)) x trivial =
      projValue 𝒜 (Proj.awayToSection 𝒜 1 (HomogeneousLocalization.fromZeroRingHom 𝒜 _ z)) x hx := e
  refine e'.trans ?_
  unfold projValue
  erw [ProjectiveSpectrum.Proj.awayToSection_apply]
  change (IsLocalization.map _ (RingHom.id A) _) (HomogeneousLocalization.mk _).val = _
  rw [HomogeneousLocalization.val_mk, Localization.mk_eq_mk', IsLocalization.map_mk',
    IsLocalization.mk'_eq_iff_eq_mul]
  simp

end General

namespace ProjSpace

variable {A : Type u} [CommRing A] {n : ℕ}

attribute [local instance] algebraOfOver

lemma algebraMap_eq_toSpecZero (a : A) : algebraMap A Γ(projectiveSpace A n, ⊤) a =
    (Proj.toSpecZero (grading A n)).appTop
      ((Scheme.ΓSpecIso _).inv (algebraMap A (grading A n 0) a)) := by
  change (toSpecBase A n).appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a) = _
  rw [toSpecBase, Scheme.Hom.comp_appTop, ← CommRingCat.comp_apply, ← Category.assoc,
    ← Scheme.ΓSpecIso_inv_naturality]
  rfl

lemma projValue_algebraMap (a : A) (x : projectiveSpace A n) :
    projValue (grading A n) (algebraMap A Γ(projectiveSpace A n, ⊤) a) x trivial =
      algebraMap (MvPolynomial (Fin (n + 1)) A) _ (C a) := by
  rw [algebraMap_eq_toSpecZero, projValue_toSpecZero]
  rfl

def smulLDeg (a : A) {s : Set (Fin (n + 1))} {k : ℤ} (ℓ : LDeg A s k) : LDeg A s k :=
  ⟨a • ℓ.1, fun m hm => ℓ.2 m fun h => hm (by rw [AddMonoidAlgebra.coeff_smul_apply, h, smul_zero])⟩

@[simp] lemma smulLDeg_val (a : A) {s : Set (Fin (n + 1))} {k : ℤ} (ℓ : LDeg A s k) :
    (smulLDeg a ℓ).1 = a • ℓ.1 := rfl

lemma toLaurent_C (a : A) : toLaurent A n (C a) = AddMonoidAlgebra.single 0 a := by
  rw [MvPolynomial.C_apply, toLaurent_monomial, map_zero]

lemma single_zero_mul_eq_smul (a : A) (ℓ : Laurent A n) :
    AddMonoidAlgebra.single 0 a * ℓ = a • ℓ := by
  apply AddMonoidAlgebra.coeff_injective
  ext m
  rw [AddMonoidAlgebra.coeff_single_zero_mul, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul]

lemma algebraMap_C_mem_awayDeg {p : ℕ} (i : Fin (p + 1) → Fin (n + 1)) (a : A) :
    algebraMap (MvPolynomial (Fin (n + 1)) A) (Localization.Away (xprod (A := A) i)) (C a) ∈
      ProjTwist.awayDeg (grading A n) (xprod_mem i) (Nat.succ_pos p) 0 := by
  have h := ProjTwist.mk_mem_awayDeg (xprod_mem i) (Nat.succ_pos p) (k := 0) (n := 0)
    (j := 0) (a := C a) (MvPolynomial.isHomogeneous_C _ a) (by simp)
  have e : ProjTwist.fpow (xprod (A := A) i) 0 = 1 := Subtype.ext (pow_zero _)
  rwa [e, Localization.mk_one_eq_algebraMap] at h

lemma theta_smulLDeg {p : ℕ} (i : Fin (p + 1) → Fin (n + 1)) (k : ℤ) (a : A)
    (ℓ : LDeg A (Set.range i) k) :
    theta i k (smulLDeg a ℓ) =
      (restrictTop (inter (cover A n) i) (algebraMap A Γ(projectiveSpace A n, ⊤) a) •
        (show Γ(twistingSheaf (grading A n) k, inter (cover A n) i) from theta i k ℓ)) := by
  set z := (awayDegEquiv (A := A) i k).symm ℓ with hz
  have hmem : algebraMap (MvPolynomial (Fin (n + 1)) A) (Localization.Away (xprod (A := A) i)) (C a) *
      z.1 ∈ ProjTwist.awayDeg (grading A n) (xprod_mem i) (Nat.succ_pos p) k := by
    have := ProjTwist.mul_mem_awayDeg (xprod_mem i) (Nat.succ_pos p)
      (algebraMap_C_mem_awayDeg i a) z.2
    rwa [zero_add] at this
  have h2 : (awayDegEquiv (A := A) i k).symm (smulLDeg a ℓ) = ⟨_, hmem⟩ := by
    rw [AddEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [awayDegEquiv_apply, map_mul, awayToLaurent_algebraMap, smulLDeg_val, toLaurent_C,
      single_zero_mul_eq_smul]
    congr 1
    rw [← awayDegEquiv_apply, hz, AddEquiv.apply_symm_apply]
  apply Subtype.ext
  funext x
  change ProjTwist.val (theta i k (smulLDeg a ℓ)) x =
    ProjTwist.val (restrictTop (inter (cover A n) i)
      (algebraMap A Γ(projectiveSpace A n, ⊤) a) •
        (show Γ(twistingSheaf (grading A n) k, inter (cover A n) i) from theta i k ℓ)) x
  change ProjTwist.val (theta i k (smulLDeg a ℓ)) x =
    ((restrictTop (inter (cover A n) i)
      (algebraMap A Γ(projectiveSpace A n, ⊤) a)).1 x).val * ProjTwist.val (theta i k ℓ) x
  erw [val_theta, val_theta, h2]
  change ProjTwist.locMap x.1 _ (_ * _) = _
  rw [map_mul]
  congr 1
  exact (ProjTwist.locMap_algebraMap (𝒜 := grading A n) x.1 _ (C a)).trans
    (projValue_algebraMap a x.1).symm

lemma lval_push_smul {k : ℤ} {p : ℕ} (a : A) (σ : Cochain (twistAb A n k) (cover A n) p)
    (i : Fin (p + 1) → Fin (n + 1)) :
    lval (push (cover A n) (smulAbRingHom (twistingSheaf (grading A n) k)
      (algebraMap A Γ(projectiveSpace A n, ⊤) a)).asHom.hom p σ) i = a • lval σ i := by
  have h : push (cover A n) (smulAbRingHom (twistingSheaf (grading A n) k)
      (algebraMap A Γ(projectiveSpace A n, ⊤) a)).asHom.hom p σ i =
      theta i k (smulLDeg a ⟨lval σ i, lval_mem σ i⟩) := by
    rw [theta_smulLDeg, theta_lval]
    rfl
  rw [lval, h, AddEquiv.symm_apply_apply]
  rfl

section Leray

variable [HasExt.{w'} (Sheaf (Opens.grothendieckTopology (projectiveSpace A n).toTopCat) AddCommGrpCat.{u})]

def cechHLinearEquivTwist (k : ℤ) (p : ℕ) :
    cechH (twistAb A n k) (cover A n) p ≃ₗ[A]
      Sheaf.H.{w'} (modulesAb (twistingSheaf (grading A n) k)) p :=
  (cechHEquiv (isCoverSystem_affineUnder (fun j : Fin (n + 1) => (X j : MvPolynomial (Fin (n + 1)) A)))
    (cover A n) iSup_stdOpen (fun {_} i => ⟨isAffineOpen_inter i, i 0, inter_le _ i 0⟩) p _
    (goodAcyclic_twist _ (fun j => X_mem j) k)).toLinearEquiv fun a x => by
      rw [cechH.smul_def, H.smul_def]
      exact cechHEquiv_naturality _ (cover A n) iSup_stdOpen
        (fun {_} i => ⟨isAffineOpen_inter i, i 0, inter_le _ i 0⟩) p _ _
        (smulAbRingHom (twistingSheaf (grading A n) k)
          (algebraMap A Γ(projectiveSpace A n, ⊤) a)).asHom x

end Leray

lemma smul_cls {k : ℤ} {p : ℕ} (a : A) (σ : Cochain (twistAb A n k) (cover A n) p)
    (hσ : d _ _ p σ = 0) :
    a • cls σ hσ = cls (push (cover A n) (smulAbRingHom (twistingSheaf (grading A n) k)
      (algebraMap A Γ(projectiveSpace A n, ⊤) a)).asHom.hom p σ)
        (by rw [← push_d, hσ, map_zero]) :=
  cechHMap_cls (cover A n) _ σ hσ

instance finite_negMon (m : ℕ) (k : ℤ) : Finite (NegMon m k) := by
  refine Finite.of_injective (β := Fin (m + 1) → Set.Icc k (-1))
    (fun e j => ⟨e.1 j, ?_, ?_⟩) fun e e' h => Subtype.ext (funext fun j => ?_)
  · have hsum := Finset.add_sum_erase Finset.univ e.1 (Finset.mem_univ j)
    have hle : ∑ i ∈ Finset.univ.erase j, e.1 i ≤ 0 :=
      Finset.sum_nonpos fun i _ => (e.2.1 i).le
    rw [e.2.2] at hsum
    omega
  · have := e.2.1 j
    omega
  · exact congrArg Subtype.val (congrFun h j)

theorem finite_cechH_top (k : ℤ) (m : ℕ) :
    Module.Finite A (cechH (twistAb A (m + 1) k) (cover A (m + 1)) (m + 1)) := by
  refine Module.Finite.equiv ((AddEquiv.ofBijective _
    (topMap_bijective (A := A) (k := k) (m := m))).toLinearEquiv fun a c => ?_).symm
  obtain ⟨σ, hσ, rfl⟩ := exists_cls c
  change topMap (a • cls σ hσ) = a • topMap (cls σ hσ)
  rw [smul_cls, topMap_cls, topMap_cls]
  ext e
  rw [topCoeff_apply, Finsupp.smul_apply, topCoeff_apply, lval_push_smul,
    AddMonoidAlgebra.coeff_smul_apply]

def zeroL (k : ℤ) : cechH (twistAb A n k) (cover A n) 0 →+ Laurent A n :=
  QuotientAddGroup.lift _
    ((AddMonoidHom.mk' (fun σ : Cochain (twistAb A n k) (cover A n) 0 => lval σ fun _ => 0)
      fun σ τ => lval_add σ τ _).comp (cocycles _ _ 0).subtype) (by
    intro x hx
    rw [AddSubgroup.mem_addSubgroupOf, coboundaries_zero, AddSubgroup.mem_bot] at hx
    simp [hx])

lemma zeroL_cls {k : ℤ} (σ : Cochain (twistAb A n k) (cover A n) 0) (hσ : d _ _ 0 σ = 0) :
    zeroL k (cls σ hσ) = lval σ fun _ => 0 := rfl

lemma zeroL_smul {k : ℤ} (a : A) (c : cechH (twistAb A n k) (cover A n) 0) :
    zeroL k (a • c) = a • zeroL k c := by
  obtain ⟨σ, hσ, rfl⟩ := exists_cls c
  rw [smul_cls, zeroL_cls, zeroL_cls, lval_push_smul]

lemma zeroL_injective {k : ℤ} : Function.Injective (zeroL (A := A) (n := n) k) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨σ, hσ, rfl⟩ := exists_cls c
  rw [zeroL_cls] at hc
  have : σ = 0 := cochain_ext fun j => by
    rw [lval_eq_of_cocycle σ hσ j (fun _ => 0), hc, lval_zero]
  subst this
  exact cls_zero

lemma zeroL_mem {k : ℤ} (c : cechH (twistAb A n k) (cover A n) 0) (j : Fin (n + 1)) :
    zeroL k c ∈ LDeg A {j} k := by
  obtain ⟨σ, hσ, rfl⟩ := exists_cls c
  rw [zeroL_cls, lval_eq_of_cocycle σ hσ (fun _ => 0) (fun _ => j)]
  have := lval_mem σ (fun _ => j)
  rwa [range_const_fin_one] at this

lemma exists_zeroL_eq {k : ℤ} (ℓ : Laurent A n) (hℓ : ∀ j, ℓ ∈ LDeg A {j} k) :
    ∃ c, zeroL k c = ℓ := by
  let σ : Cochain (twistAb A n k) (cover A n) 0 :=
    ofL fun i => ⟨ℓ, by rw [range_const_fin_one]; exact hℓ (i 0)⟩
  have hσ : d _ _ 0 σ = 0 := by
    refine cochain_ext fun i => ?_
    rw [lval_d, lval_zero, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_zero]
    simp [σ]
  exact ⟨cls σ hσ, by rw [zeroL_cls]; simp [σ]⟩

lemma allowed_bound {k : ℤ} {m : Fin (n + 1) → ℤ} (h : ∀ j, Allowed {j} k m) (j : Fin (n + 1)) :
    m j ∈ Set.Icc (-|k|) |k| := by
  by_cases hn : ∃ j', j' ≠ j
  · obtain ⟨j', hj'⟩ := hn
    have hnn : ∀ i, 0 ≤ m i := fun i => by
      by_cases hi : i = j
      · subst hi
        exact (h j').2 i (by simpa [eq_comm] using hj'.symm)
      · exact (h j).2 i (by simpa using hi)
    have hle : m j ≤ ∑ i, m i := Finset.single_le_sum (fun i _ => hnn i) (Finset.mem_univ j)
    rw [(h j).1] at hle
    have := hnn j
    constructor <;> [skip; skip] <;> cases abs_cases k <;> omega
  · push Not at hn
    have hs : ∑ i, m i = m j := Finset.sum_eq_single j (fun i _ hi => absurd (hn i) hi) (by simp)
    rw [(h j).1] at hs
    constructor <;> cases abs_cases k <;> omega

lemma finite_allowed (k : ℤ) : {m : Fin (n + 1) → ℤ | ∀ j, Allowed {j} k m}.Finite :=
  (Set.Finite.pi (t := fun _ : Fin (n + 1) => Set.Icc (-|k|) |k|)
    fun _ => Set.finite_Icc _ _).subset fun m hm => by
      simp only [Set.mem_pi, Set.mem_univ, true_implies]
      exact fun j => allowed_bound hm j

theorem finite_cechH_zero (k : ℤ) : Module.Finite A (cechH (twistAb A n k) (cover A n) 0) := by
  let ζ : cechH (twistAb A n k) (cover A n) 0 →ₗ[A] Laurent A n :=
    { zeroL k with map_smul' := zeroL_smul }
  have hζ : Function.Injective ζ := zeroL_injective
  let T : Set (Laurent A n) :=
    (fun m => AddMonoidAlgebra.single m (1 : A)) '' {m | ∀ j, Allowed {j} k m}
  have hrange : LinearMap.range ζ = Submodule.span A T := by
    apply le_antisymm
    · rintro _ ⟨c, rfl⟩
      have hmem := zeroL_mem (A := A) c
      set ℓ := zeroL k c
      have hℓ : ℓ = ∑ m ∈ ℓ.coeff.support, ℓ.coeff m • AddMonoidAlgebra.single m (1 : A) := by
        apply AddMonoidAlgebra.coeff_injective
        ext m
        rw [coeff_sum']
        simp only [AddMonoidAlgebra.coeff_smul_apply, AddMonoidAlgebra.coeff_single,
          Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
        rw [Finset.sum_ite_eq']
        split_ifs with hm
        · rfl
        · exact Finsupp.notMem_support_iff.mp hm
      change ℓ ∈ _
      rw [hℓ]
      refine Submodule.sum_mem _ fun m hm => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      exact ⟨m, fun j => hmem j m (Finsupp.mem_support_iff.mp hm), rfl⟩
    · rw [Submodule.span_le]
      rintro _ ⟨m, hm, rfl⟩
      obtain ⟨c, hc⟩ := exists_zeroL_eq (A := A) (k := k) _ fun j => single_mem_LDeg (hm j) 1
      exact ⟨c, hc⟩
  have : Module.Finite A (LinearMap.range ζ) := by
    rw [Module.Finite.iff_fg, hrange]
    exact Submodule.fg_span ((finite_allowed k).image _)
  exact Module.Finite.equiv (LinearEquiv.ofInjective ζ hζ).symm

theorem finite_cechH (k : ℤ) (p : ℕ) : Module.Finite A (cechH (twistAb A n k) (cover A n) p) := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · exact finite_cechH_zero k
  rcases lt_trichotomy p n with h | rfl | h
  · have := subsingleton_cechH_of_lt (A := A) (k := k) hp h
    infer_instance
  · obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
    exact finite_cechH_top k m
  · have := subsingleton_cechH_of_gt (A := A) (k := k) h
    infer_instance

end ProjSpace

namespace ProjSpace

variable {A : Type u} [CommRing A] {n : ℕ}
  [HasExt.{w'} (Sheaf (Opens.grothendieckTopology (projectiveSpace A n).toTopCat) AddCommGrpCat.{u})]

attribute [local instance] algebraOfOver

theorem finite_H_twistingSheaf (k : ℤ) (p : ℕ) :
    Module.Finite A (Sheaf.H.{w'} (modulesAb (twistingSheaf (grading A n) k)) p) :=
  have := finite_cechH (A := A) (n := n) k p
  Module.Finite.equiv (cechHLinearEquivTwist k p)

theorem subsingleton_H_twistingSheaf {k : ℤ} (hk : 0 ≤ k) {p : ℕ} (hp : 0 < p) :
    Subsingleton (Sheaf.H.{w'} (modulesAb (twistingSheaf (grading A n) k)) p) := by
  rcases eq_or_ne p n with rfl | hpn
  · obtain ⟨e⟩ := nonempty_HTop_equiv.{w'} (A := A) k hp
    have : IsEmpty (NegMon p k) := ⟨fun m => by
      have hlt : ∑ j, m.1 j < 0 :=
        Finset.sum_neg (fun j _ => m.2.1 j) Finset.univ_nonempty
      rw [m.2.2] at hlt
      omega⟩
    exact e.toEquiv.subsingleton
  · exact subsingleton_H.{w'} k hp hpn

theorem subsingleton_H_of_lt (G : (projectiveSpace A n).Modules) [G.IsQuasicoherent] {p : ℕ}
    (hp : n < p) : Subsingleton (Sheaf.H.{w'} (modulesAb G) p) := by
  obtain ⟨e⟩ : Nonempty (cechH (modulesAb G).obj (stdOpen A n) p ≃+ Sheaf.H.{w'} (modulesAb G) p) :=
    SchemeCoh.nonempty_cechH_equiv_H G (stdOpen A n) iSup_stdOpen
      (fun _ i => by rw [← inter_eq_iInf]; exact isAffineOpen_inter i) p
  have : Subsingleton (cechH (modulesAb G).obj (stdOpen A n) p) :=
    cechH_subsingleton _ _ (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
  exact e.symm.toEquiv.subsingleton

end ProjSpace

end

end GroundTheory.Arith.SchemeCoh
