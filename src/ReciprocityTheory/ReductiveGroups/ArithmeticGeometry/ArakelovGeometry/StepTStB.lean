module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsBergDensity

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.StepTStB
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

theorem ringKrullDim_le_of_isIntegral' {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] : ringKrullDim S ≤ ringKrullDim R := by
  unfold ringKrullDim
  refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S)) ?_
  intro P Q hPQ
  exact Ideal.IsIntegral.comap_lt_comap (I := P.asIdeal) (J := Q.asIdeal) hPQ

section Arith

variable {Ω : Type*} [Field Ω] [CharZero Ω]

theorem X_mem_coordIdeal_iff {J : Type} (v : J → Ω) (i : J) :
    (X i : MvPolynomial J ℤ) ∈ coordIdeal ℤ v ↔ v i = 0 := by
  rw [coordIdeal, RingHom.mem_ker, coneMap, aeval_X, mul_eq_zero, Polynomial.C_eq_zero]
  simp [Polynomial.X_ne_zero]

theorem isHorizontal_coordIdeal {κ : Type} (v : Ix κ → Ω) :
    IsHorizontal (ι := GlobalTheory κ) (coordIdeal ℤ v) := by
  rw [IsHorizontal, eq_bot_iff]
  intro n hn
  rw [Ideal.mem_comap, coordIdeal, RingHom.mem_ker, coneMap, aeval_C] at hn
  rw [Submodule.mem_bot]
  simpa using hn

theorem isMultiHomogIdeal_coordIdeal {κ : Type} [Fintype κ] (v : Ix κ → Ω) :
    IsMultiHomogIdeal (ι := GlobalTheory κ) (coordIdeal ℤ v) := by
  refine ⟨{f | f ∈ coordIdeal ℤ v ∧ ∃ n, f.IsHomogeneous n}, ?_, ?_⟩
  · rintro f ⟨_, n, hn⟩
    refine ⟨fun _ => n, fun m hm k => ?_⟩
    have h1 : Finsupp.degree m = n := by
      rw [Finsupp.degree_eq_weight_one]
      exact hn (mem_support_iff.mp hm)
    rw [Finsupp.degree_eq_sum, Fintype.sum_sigma] at h1
    cases k
    simpa using h1
  · apply le_antisymm
    · intro f hf
      rw [← sum_homogeneousComponent f]
      exact Ideal.sum_mem _ fun d _ => Ideal.subset_span
        ⟨coordIdeal_isHomogIdeal ℤ v f hf d, d, homogeneousComponent_isHomogeneous d f⟩
    · exact Ideal.span_le.mpr fun f hf => hf.1

theorem coneMap_rename {J J' : Type} (v : J → Ω) (e : J' → J) (p : MvPolynomial J' ℤ) :
    coneMap ℤ v (rename e p) = coneMap ℤ (v ∘ e) p := by
  rw [coneMap, coneMap, aeval_rename]
  rfl

end Arith

section Dim

variable {Ω : Type*} [Field Ω] [CharZero Ω] {J : Type} [Fintype J] {D : ℕ}

theorem isIntegralElem_of_comp {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (val : S →+* T) (hval : Function.Injective val) {s : S}
    (h : (val.comp f).IsIntegralElem (val s)) : f.IsIntegralElem s := by
  obtain ⟨p, hp, he⟩ := h
  refine ⟨p, hp, hval ?_⟩
  rw [map_zero, ← he, Polynomial.hom_eval₂]

theorem isIntegralElem_coneMap (v : J → Ω) (e : Fin (D + 1) → J) (hf : IsProjFrame v e)
    (q : MvPolynomial J ℤ) :
    (coneMap ℤ (v ∘ e) : MvPolynomial (Fin (D + 1)) ℤ →+* Polynomial Ω).IsIntegralElem
      (coneMap ℤ v q) := by
  have hinj : Function.Injective (coneMap ℤ (v ∘ e)) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro p hp
    have : p ∈ coordIdeal ℤ (v ∘ e) := by simpa [coordIdeal, RingHom.mem_ker] using hp
    rw [hf.free] at this
    exact (Ideal.mem_bot).mp this
  set φ := AlgEquiv.ofInjective (coneMap ℤ (v ∘ e)) hinj
  have hgen : ∀ i, (coneMap ℤ (v ∘ e) : MvPolynomial (Fin (D + 1)) ℤ →+* Polynomial Ω).IsIntegralElem
      (Polynomial.C (v i) * Polynomial.X) := by
    intro i
    have hi : IsIntegral (coneMap ℤ (v ∘ e)).range (Polynomial.C (v i) * Polynomial.X : Polynomial Ω) :=
      hf.integral i
    obtain ⟨p, hp, hps⟩ := hi
    refine ⟨p.map φ.symm.toRingEquiv.toRingHom,
      hp.map _, ?_⟩
    have hcomp : ((coneMap ℤ (v ∘ e) : MvPolynomial (Fin (D + 1)) ℤ →+* Polynomial Ω).comp
        φ.symm.toRingEquiv.toRingHom) = algebraMap (coneMap ℤ (v ∘ e)).range (Polynomial Ω) := by
      refine RingHom.ext fun r => ?_
      have h1 : ((φ (φ.symm r) : (coneMap ℤ (v ∘ e)).range) : Polynomial Ω) =
          coneMap ℤ (v ∘ e) (φ.symm r) := rfl
      rw [AlgEquiv.apply_symm_apply] at h1
      exact h1.symm
    rw [Polynomial.eval₂_map, hcomp]
    exact hps
  induction q using MvPolynomial.induction_on with
  | C a =>
    have : coneMap ℤ v (C a) = coneMap ℤ (v ∘ e) (C a) := by simp
    rw [this]
    exact RingHom.isIntegralElem_map _
  | add p q hp hq =>
    rw [map_add (f := _)]
    exact RingHom.IsIntegralElem.add _ hp hq
  | mul_X p i hp =>
    rw [map_mul]
    refine RingHom.IsIntegralElem.mul _ hp ?_
    simpa [coneMap] using hgen i

theorem coneMap_injective_of_frame (v : J → Ω) (e : Fin (D + 1) → J) (hf : IsProjFrame v e) :
    Function.Injective (coneMap ℤ (v ∘ e)) := by
  exact (injective_iff_map_eq_zero _).2 fun p hp => by
    have h : p ∈ coordIdeal ℤ (v ∘ e) := (RingHom.mem_ker).2 hp
    rwa [hf.free, Ideal.mem_bot] at h

theorem ringKrullDim_mvPoly_fin_int :
    ringKrullDim (MvPolynomial (Fin (D + 1)) ℤ) = ((D + 2 : ℕ) : WithBot ℕ∞) := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField,
    Nat.card_eq_fintype_card, Fintype.card_fin]
  rw [show ((D + 2 : ℕ) : WithBot ℕ∞) = 1 + ((D + 1 : ℕ) : WithBot ℕ∞) by norm_cast; omega]

theorem ringKrullDim_quot_of_frame (v : J → Ω) (e : Fin (D + 1) → J) (hf : IsProjFrame v e) :
    ringKrullDim (MvPolynomial J ℤ ⧸ coordIdeal ℤ v) = ((D + 2 : ℕ) : WithBot ℕ∞) := by
  have hq : ringKrullDim (MvPolynomial J ℤ ⧸ coordIdeal ℤ v) =
      ringKrullDim (coneMap ℤ v).range :=
    ringKrullDim_eq_of_ringEquiv (Ideal.quotientKerEquivRange (coneMap ℤ v)).toRingEquiv
  let f : MvPolynomial (Fin (D + 1)) ℤ →+* (coneMap ℤ v).range :=
    ((coneMap ℤ v).rangeRestrict.comp (rename e)).toRingHom
  have hvalf : ((coneMap ℤ v).range.val : (coneMap ℤ v).range →+* Polynomial Ω).comp f =
      (coneMap ℤ (v ∘ e) : MvPolynomial (Fin (D + 1)) ℤ →+* Polynomial Ω) := by
    refine RingHom.ext fun p => ?_
    simp [f, coneMap_rename]
  have hinj : Function.Injective f := by
    intro a b hab
    apply coneMap_injective_of_frame v e hf
    have := congrArg ((coneMap ℤ v).range.val : (coneMap ℤ v).range →+* Polynomial Ω) hab
    rw [← RingHom.comp_apply, ← RingHom.comp_apply, hvalf] at this
    exact this
  have hint : f.IsIntegral := fun s => by
    obtain ⟨q, hq⟩ := s.2
    apply isIntegralElem_of_comp f ((coneMap ℤ v).range.val : (coneMap ℤ v).range →+* Polynomial Ω)
      Subtype.val_injective
    rw [hvalf]
    change RingHom.IsIntegralElem _ (s : Polynomial Ω)
    rw [← hq]
    exact isIntegralElem_coneMap v e hf q
  rw [hq]
  apply le_antisymm
  · let _ := f.toAlgebra
    have : Algebra.IsIntegral (MvPolynomial (Fin (D + 1)) ℤ) (coneMap ℤ v).range := ⟨hint⟩
    rw [← ringKrullDim_mvPoly_fin_int]
    exact ringKrullDim_le_of_isIntegral'
  · exact le_ringKrullDim_of_isIntegral f hint hinj _ ringKrullDim_mvPoly_fin_int.ge

end Dim

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.EqSumMultihomogeneousComponents
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def i2bdeg (m : (Σ k, ι k) →₀ ℕ) : K → ℕ := fun k => ∑ i, m ⟨k, i⟩

theorem i2bdeg_add (m n : (Σ k, ι k) →₀ ℕ) : i2bdeg (m + n) = i2bdeg m + i2bdeg n := by
  funext k
  simp [i2bdeg, Finset.sum_add_distrib]


open Classical in
def i2comp (a : K → ℕ) (h : MRing ι) : MRing ι :=
  ∑ m ∈ h.support.filter (fun m => i2bdeg m = a), monomial m (AddMonoidAlgebra.coeff h m)

open Classical in
theorem coeff_i2comp (a : K → ℕ) (h : MRing ι) (m : (Σ k, ι k) →₀ ℕ) :
    AddMonoidAlgebra.coeff (i2comp a h) m = if i2bdeg m = a then AddMonoidAlgebra.coeff h m else 0 := by
  unfold i2comp
  rw [coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  by_cases h0 : AddMonoidAlgebra.coeff h m = 0 <;> by_cases e : i2bdeg m = a <;> simp [Finset.mem_filter, mem_support_iff, h0, e]

theorem isMultiHomog_iff_coeff (s : MRing ι) (a : K → ℕ) :
    IsMultiHomog s a ↔ ∀ m, AddMonoidAlgebra.coeff s m ≠ 0 → i2bdeg m = a := by
  constructor
  · intro h m hm
    funext k
    exact h m (mem_support_iff.mpr hm) k
  · intro h m hm k
    exact congrFun (h m (mem_support_iff.mp hm)) k

def i2compHom (a : K → ℕ) : MRing ι →+ MRing ι where
  toFun := i2comp a
  map_zero' := by
    classical
    ext m
    rw [coeff_i2comp]
    simp
  map_add' x y := by
    classical
    ext m
    change AddMonoidAlgebra.coeff (i2comp a (x + y)) m =
      AddMonoidAlgebra.coeff (i2comp a x) m + AddMonoidAlgebra.coeff (i2comp a y) m
    rw [coeff_i2comp, coeff_i2comp, coeff_i2comp, AddMonoidAlgebra.coeff_add]
    change (if i2bdeg m = a then AddMonoidAlgebra.coeff x m + AddMonoidAlgebra.coeff y m else 0) = _
    split_ifs <;> simp

theorem i2comp_add (a : K → ℕ) (x y : MRing ι) : i2comp a (x + y) = i2comp a x + i2comp a y :=
  (i2compHom a).map_add x y

theorem i2comp_zero (a : K → ℕ) : i2comp a (0 : MRing ι) = 0 := (i2compHom a).map_zero

theorem isMultiHomog_i2comp (a : K → ℕ) (h : MRing ι) : IsMultiHomog (i2comp a h) a := by
  classical
  rw [isMultiHomog_iff_coeff]
  intro m hm
  rw [coeff_i2comp] at hm
  by_contra e
  exact hm (ite_eq_right e)

theorem i2comp_of_homog {a b : K → ℕ} {h : MRing ι} (hh : IsMultiHomog h b) :
    i2comp a h = if b = a then h else 0 := by
  classical
  rw [isMultiHomog_iff_coeff] at hh
  ext m
  rw [coeff_i2comp]
  by_cases hm : AddMonoidAlgebra.coeff h m = 0
  · split_ifs <;> simp [hm]
  · have := hh m hm
    subst this
    split_ifs <;> simp_all

theorem i2comp_self {a : K → ℕ} {h : MRing ι} (hh : IsMultiHomog h a) : i2comp a h = h := by
  rw [i2comp_of_homog hh, ite_eq_left rfl]

theorem eq_sum_multihomogeneous_components (r : MRing ι) :
    r = ∑ b ∈ r.support.image i2bdeg, i2comp b r := by
  classical
  ext m
  rw [coeff_sum]
  simp_rw [coeff_i2comp]
  rw [Finset.sum_ite_eq]
  split_ifs with hm
  · rfl
  · by_contra hne
    exact hm (Finset.mem_image_of_mem _ (mem_support_iff.mpr hne))

theorem mem_mHom_iff (s : MRing ι) (a : K → ℕ) : s ∈ mHom ι a ↔ IsMultiHomog s a := by
  constructor
  · intro hs
    induction hs using Submodule.span_induction with
    | mem x hx => exact hx
    | zero => intro m hm; simp at hm
    | add x y _ _ hx hy =>
      rw [isMultiHomog_iff_coeff] at hx hy ⊢
      intro m hm
      rw [AddMonoidAlgebra.coeff_add] at hm
      change AddMonoidAlgebra.coeff x m + AddMonoidAlgebra.coeff y m ≠ 0 at hm
      by_cases h0 : AddMonoidAlgebra.coeff x m = 0
      · rw [h0, zero_add] at hm
        exact hy m hm
      · exact hx m h0
    | smul n x _ hx =>
      rw [isMultiHomog_iff_coeff] at hx ⊢
      intro m hm
      rw [coeff_smul] at hm
      exact hx m (fun h0 => hm (by rw [h0, smul_zero]))
  · intro hs
    exact Submodule.subset_span hs

theorem isMultiHomog_mul' {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a)
    (hg : IsMultiHomog g b) : IsMultiHomog (f * g) (a + b) := by
  classical
  rw [isMultiHomog_iff_coeff] at hf hg ⊢
  intro m hm
  rw [coeff_mul] at hm
  obtain ⟨x, hx, hx0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  rw [← hx, i2bdeg_add, hf x.1 (left_ne_zero_of_mul hx0), hg x.2 (right_ne_zero_of_mul hx0)]

theorem i2bdeg_apply_add (m n : (Σ k, ι k) →₀ ℕ) (k : K) :
    i2bdeg (m + n) k = i2bdeg m k + i2bdeg n k := by
  simp [i2bdeg, Finset.sum_add_distrib]

open Classical in
theorem i2comp_mul_right {f : MRing ι} {c : K → ℕ} (hf : IsMultiHomog f c) (a : K → ℕ)
    (g : MRing ι) : i2comp a (g * f) = if c ≤ a then i2comp (a - c) g * f else 0 := by
  rw [isMultiHomog_iff_coeff] at hf
  ext m
  rw [coeff_i2comp]
  split_ifs with hm hca hca
  · rw [coeff_mul, coeff_mul]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    rw [coeff_i2comp]
    by_cases h0 : AddMonoidAlgebra.coeff f x.2 = 0
    · simp [h0]
    · have e2 := hf x.2 h0
      have e : i2bdeg x.1 = a - c := by
        funext k
        have h1 := i2bdeg_apply_add x.1 x.2 k
        rw [hx] at h1
        have h2 := congrFun hm k
        have h3 := congrFun e2 k
        simp only [Pi.sub_apply]
        rw [← h2, h1, h3, Nat.add_sub_cancel]
      rw [ite_eq_left e]
  · simp only [AddMonoidAlgebra.coeff_zero, coeff_mul]
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    by_cases h0 : AddMonoidAlgebra.coeff f x.2 = 0
    · simp [h0]
    · exfalso
      apply hca
      have e2 := hf x.2 h0
      intro k
      have h1 := i2bdeg_apply_add x.1 x.2 k
      rw [hx] at h1
      have h2 := congrFun hm k
      have h3 := congrFun e2 k
      rw [← h2, h1, h3]
      exact Nat.le_add_left _ _
  · rw [coeff_mul]
    refine (Finset.sum_eq_zero fun x hx => ?_).symm
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    rw [coeff_i2comp]
    by_cases h0 : AddMonoidAlgebra.coeff f x.2 = 0
    · simp [h0]
    · by_cases e : i2bdeg x.1 = a - c
      · exfalso
        apply hm
        funext k
        have h1 := i2bdeg_apply_add x.1 x.2 k
        rw [hx] at h1
        have h2 := congrFun e k
        have h3 := congrFun (hf x.2 h0) k
        have h4 := hca k
        simp only [Pi.sub_apply] at h2
        rw [h1, h2, h3, Nat.sub_add_cancel h4]
      · simp [e]
  · simp

open Classical in
theorem i2comp_mem {F : Ideal (MRing ι)} (hF : IsMultiHomogIdeal F) (a : K → ℕ) {u : MRing ι}
    (hu : u ∈ F) : i2comp a u ∈ F := by
  classical
  obtain ⟨S, hS, rfl⟩ := hF
  revert a
  induction hu using Submodule.span_induction with
  | mem x hx =>
    intro a
    obtain ⟨b, hb⟩ := hS x hx
    rw [i2comp_of_homog hb]
    split_ifs
    · exact Ideal.subset_span hx
    · exact zero_mem _
  | zero => intro a; rw [i2comp_zero]; exact zero_mem _
  | add x y _ _ hx hy => intro a; rw [i2comp_add]; exact add_mem (hx a) (hy a)
  | smul r x _ hx =>
    intro a
    rw [smul_eq_mul, eq_sum_multihomogeneous_components r, Finset.sum_mul]
    have : i2comp a (∑ b ∈ r.support.image i2bdeg, i2comp b r * x) =
        ∑ b ∈ r.support.image i2bdeg, i2comp a (i2comp b r * x) := map_sum (i2compHom a) _ _
    rw [this]
    refine Ideal.sum_mem _ fun b _ => ?_
    rw [mul_comm, i2comp_mul_right (isMultiHomog_i2comp b r)]
    split_ifs
    · exact Ideal.mul_mem_right _ _ (hx _)
    · exact zero_mem _

theorem isMultiHomogIdeal_sup_span {F : Ideal (MRing ι)} (hF : IsMultiHomogIdeal F) {f : MRing ι}
    {c : K → ℕ} (hf : IsMultiHomog f c) : IsMultiHomogIdeal (F ⊔ Ideal.span {f}) := by
  obtain ⟨S, hS, rfl⟩ := hF
  refine ⟨S ∪ {f}, fun g hg => ?_, (Ideal.span_union S {f}).symm⟩
  rcases hg with hg | hg
  · exact hS g hg
  · rw [Set.mem_singleton_iff] at hg
    exact ⟨c, hg ▸ hf⟩

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ABridgeStA
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module

variable {Ω : Type} [Field Ω] [CharZero Ω] {J : Type} [Fintype J]

theorem aeval_map_int (x : J → Ω) (f : MvPolynomial J ℤ) :
    aeval x (map (Int.castRingHom ℚ) f) = aeval x f := by
  rw [aeval_def, eval₂_map, aeval_def]
  congr 1 <;> exact RingHom.ext_int _ _

theorem eval_smul_of_homog {R : Type*} [CommRing R] {φ : MvPolynomial J R} {d : ℕ}
    (hφ : φ.IsHomogeneous d) (c : R) (z : J → R) : eval (c • z) φ = c ^ d * eval z φ := by
  conv_lhs => rw [φ.as_sum]
  conv_rhs => rw [φ.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, Finset.mul_sum, eval_monomial]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hd : ∑ i ∈ s.support, s i = d := by
    have := hφ (mem_support_iff.mp hs)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  simp only [Finsupp.prod, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, hd]
  ring

theorem secFun_smul {b : MvPolynomial J ℚ} {n : ℕ}
    (hb : ∃ f : MvPolynomial J ℤ, f.IsHomogeneous n ∧ b = map (Int.castRingHom ℚ) f)
    (c : ℂ) (z : J → ℂ) : secFun b (c • z) = c ^ n * secFun b z := by
  obtain ⟨f, hf, rfl⟩ := hb
  have hmap : map (algebraMap ℚ ℂ) (map (Int.castRingHom ℚ) f) = map (Int.castRingHom ℂ) f := by
    rw [map_map]
    congr 1 <;> exact RingHom.ext_int _ _
  simp only [secFun, hmap]
  exact eval_smul_of_homog (hf.map _) c z

theorem continuous_secFun (b : MvPolynomial J ℚ) : Continuous (secFun b) := by
  unfold secFun
  exact MvPolynomial.continuous_eval _

theorem secFun_map_int (f : MvPolynomial J ℤ) (z : J → ℂ) :
    secFun (map (Int.castRingHom ℚ) f) z = eval z (map (Int.castRingHom ℂ) f) := by
  unfold secFun
  rw [map_map]
  congr 2 <;> exact RingHom.ext_int _ _

theorem secFun_eq_zero_of_pts {x : J → Ω} {n : ℕ} {d : MvPolynomial J ℤ} (hd : d.IsHomogeneous n)
    (h0 : aeval x d = 0) {z : J → ℂ} (hz : z ∈ pts (coordIdeal ℤ x)) :
    secFun (map (Int.castRingHom ℚ) d) z = 0 := by
  have hmem : d ∈ coordIdeal ℤ x := by
    unfold coordIdeal coneMap
    rw [RingHom.mem_ker, aeval_def, ← eval_map]
    have hpt : (fun i => Polynomial.C (x i) * Polynomial.X) =
        (Polynomial.X : Polynomial Ω) • fun i => Polynomial.C (x i) := by
      funext i
      exact mul_comm _ _
    have hC : eval (fun i => Polynomial.C (x i)) (map (algebraMap ℤ (Polynomial Ω)) d) =
        Polynomial.C (aeval x d) := by
      rw [eval_map, aeval_def, hom_eval₂]
      congr 1 <;> exact RingHom.ext_int _ _
    rw [hpt, eval_smul_of_homog (hd.map _), hC, h0, map_zero, mul_zero]
  rw [secFun_map_int]
  exact hz.2 d hmem

theorem secFun_conjPt (b : MvPolynomial J ℚ) (z : J → ℂ) :
    secFun b (conjPt z) = starRingEnd ℂ (secFun b z) := by
  simp only [secFun, eval_map, hom_eval₂]
  rw [RingHom.ext_rat ((starRingEnd ℂ).comp (algebraMap ℚ ℂ)) (algebraMap ℚ ℂ)]
  rfl

theorem continuous_conjPt : Continuous (conjPt : (J → ℂ) → J → ℂ) := by
  exact continuous_pi fun i => Complex.continuous_conj.comp (continuous_apply i)

def conjEquiv (J : Type) [Fintype J] : (J → ℂ) ≃ᵐ (J → ℂ) where
  toFun := conjPt
  invFun := conjPt
  left_inv z := by funext i; simp [conjPt]
  right_inv z := by funext i; simp [conjPt]
  measurable_toFun := continuous_conjPt.measurable
  measurable_invFun := continuous_conjPt.measurable

theorem wgt_conjPt {m : ConeMetric (C := ℂ) (ι := J)} (hm : IsConjInvariant m) (n : ℕ) (z : J → ℂ) :
    wgt m n (conjPt z) = wgt m n z := by
  unfold wgt conjPt
  rw [hm z]

theorem conj_bGram {m : ConeMetric (C := ℂ) (ι := J)} {μ : Measure (J → ℂ)} (hm : IsConjInvariant m)
    (hμ : μ.map conjPt = μ) (n : ℕ) {r : ℕ} (b : Fin r → MvPolynomial J ℚ) (i j : Fin r) :
    starRingEnd ℂ (bGram μ (fun k => secFun (b k)) (wgt m n) i j) =
      bGram μ (fun k => secFun (b k)) (wgt m n) i j := by
  have hμ' : μ.map (conjEquiv J) = μ := hμ
  have he : ∀ x, conjEquiv J x = conjPt x := fun x => rfl
  simp only [bGram, Matrix.of_apply]
  rw [← integral_conj]
  conv_rhs => rw [← hμ']
  rw [integral_map_equiv (conjEquiv J)]
  congr 1
  funext x
  simp [he, secFun_conjPt, wgt_conjPt hm]
  try ring

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ABridgeStB
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial TensorProduct

theorem isReduced_tensor_finite (Ω E : Type*) [Field Ω] [CharZero Ω] [Field E] [Algebra ℚ E]
    [FiniteDimensional ℚ E] : IsReduced (E ⊗[ℚ] Ω) := by
  haveI : Algebra.FormallyUnramified ℚ E := Algebra.FormallyUnramified.of_isSeparable ℚ E
  haveI : IsReduced (Ω ⊗[ℚ] E) := Algebra.FormallyUnramified.isReduced_of_field Ω (Ω ⊗[ℚ] E)
  exact isReduced_of_injective (Algebra.TensorProduct.comm ℚ E Ω).toRingHom
    (Algebra.TensorProduct.comm ℚ E Ω).injective

theorem eq_zero_of_sum_tmul {Ω E : Type*} [Field Ω] [CharZero Ω] [Field E] [Algebra ℚ E] {r : ℕ}
    {s : Fin r → Ω} (hs : LinearIndependent ℚ s) {e : Fin r → E}
    (h : ∑ k, e k ⊗ₜ[ℚ] s k = 0) : e = 0 := by
  classical
  let W := Submodule.span ℚ (Set.range s)
  let 𝒞 : Module.Basis (Fin r) ℚ W := Module.Basis.span hs
  have hinj : Function.Injective (LinearMap.lTensor E W.subtype) :=
    Module.Flat.lTensor_preserves_injective_linearMap W.subtype Subtype.val_injective
  have h0 : (∑ k, e k ⊗ₜ[ℚ] 𝒞 k : E ⊗[ℚ] W) = 0 := by
    apply hinj
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_zero]
    have hc : ∀ k, ((𝒞 k : W) : Ω) = s k := fun k => by
      show ((Module.Basis.span hs k : W) : Ω) = s k
      rw [Module.Basis.span_apply]
    simp only [LinearMap.lTensor_tmul, Submodule.subtype_apply, hc]
    exact h
  have hb := TensorProduct.sum_tmul_basis_right_eq_zero 𝒞 (Finsupp.equivFunOnFinite.symm e) (by
    rw [Finsupp.sum_fintype _ _ (by intros; simp)]
    simpa using h0)
  funext k
  have hk := congrArg (fun b => b k) hb
  simpa using hk

theorem nilp_coeff_eq_zero {Ω : Type} [Field Ω] [CharZero Ω] {r : ℕ} {s : Fin r → Ω}
    (hs : LinearIndependent ℚ s) {c : Fin r → ℂ}
    (h : IsNilpotent (∑ k, c k ⊗ₜ[ℚ] s k : ℂ ⊗[ℚ] Ω)) : c = 0 := by
  classical
  let A : Subalgebra ℚ ℂ := Algebra.adjoin ℚ ((Finset.univ.image c : Finset ℂ) : Set ℂ)
  haveI : Algebra.FiniteType ℚ A := (Subalgebra.fg_iff_finiteType A).1 (Subalgebra.fg_adjoin_finset _)
  haveI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := ℚ) (B := A)
  have hcA : ∀ k, c k ∈ A := fun k => Algebra.subset_adjoin (by simp)
  let cA : Fin r → A := fun k => ⟨c k, hcA k⟩
  let tA : A ⊗[ℚ] Ω := ∑ k, cA k ⊗ₜ[ℚ] s k
  let ι : A ⊗[ℚ] Ω →ₐ[ℚ] ℂ ⊗[ℚ] Ω := Algebra.TensorProduct.map A.val (AlgHom.id ℚ Ω)
  have hι : Function.Injective ι := by
    have hinj := Module.Flat.rTensor_preserves_injective_linearMap (M := Ω) (A.val.toLinearMap)
      Subtype.val_injective
    have heq : ∀ x, ι x = LinearMap.rTensor Ω A.val.toLinearMap x := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [ι, Algebra.TensorProduct.map_tmul]
      | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
    intro x y hxy
    apply hinj
    rw [← heq, ← heq, hxy]
  have hιt : ι tA = ∑ k, c k ⊗ₜ[ℚ] s k := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [tA, ι, map_sum, Algebra.TensorProduct.map_tmul, cA]
  have hnA : IsNilpotent tA := by
    obtain ⟨m, hm⟩ := h
    refine ⟨m, hι ?_⟩
    rw [map_pow, hιt, hm, map_zero]
  have key : ∀ (E : Type) [Field E] [Algebra ℚ E] [FiniteDimensional ℚ E] (φ : A →ₐ[ℚ] E),
      ∀ k, φ (cA k) = 0 := by
    intro E _ _ _ φ
    let π : A ⊗[ℚ] Ω →ₐ[ℚ] E ⊗[ℚ] Ω := Algebra.TensorProduct.map φ (AlgHom.id ℚ Ω)
    haveI : IsReduced (E ⊗[ℚ] Ω) := isReduced_tensor_finite Ω E
    have h0 : π tA = 0 := (hnA.map π).eq_zero
    have h1 : ∑ k, φ (cA k) ⊗ₜ[ℚ] s k = 0 := by
      rw [← h0]
      set_option synthInstance.maxHeartbeats 100000 in
        simp [tA, π, map_sum, Algebra.TensorProduct.map_tmul]
    exact congrFun (eq_zero_of_sum_tmul hs h1)
  have hmax : ∀ M : Ideal A, M.IsMaximal → ∀ k, cA k ∈ M := by
    intro M hM k
    letI hF : Field (A ⧸ M) := Ideal.Quotient.field M
    haveI : Algebra.FiniteType ℚ (A ⧸ M) :=
      Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℚ M) Ideal.Quotient.mk_surjective
    haveI : Module.Finite ℚ (A ⧸ M) := finite_of_finite_type_of_isJacobsonRing ℚ (A ⧸ M)
    exact Ideal.Quotient.eq_zero_iff_mem.1 (key (A ⧸ M) (Ideal.Quotient.mkₐ ℚ M) k)
  have hjac : (⊥ : Ideal A).jacobson = ⊥ := IsJacobsonRing.out inferInstance Ideal.isPrime_bot.isRadical
  funext k
  have hk : cA k ∈ (⊥ : Ideal A).jacobson := Ideal.mem_sInf.2 (fun J hJ => hmax J hJ.2 k)
  rw [hjac] at hk
  have h0 : cA k = 0 := (Submodule.mem_bot _).1 hk
  exact congrArg Subtype.val h0

section Poly

variable {Ω : Type} [Field Ω] [CharZero Ω] {J : Type} [Fintype J]

theorem aeval_eq_zero_of_mem_coordIdeal {x : J → Ω} {f : MvPolynomial J ℤ}
    (hf : f ∈ coordIdeal ℤ x) : aeval x f = 0 := by
  have h0 : (aeval fun i => Polynomial.C (x i) * Polynomial.X : MvPolynomial J ℤ →ₐ[ℤ] Polynomial Ω) f = 0 :=
    RingHom.mem_ker.1 hf
  have h1 := MvPolynomial.comp_aeval_apply (fun i => Polynomial.C (x i) * Polynomial.X)
    ((Polynomial.aeval (1 : Ω)).restrictScalars ℤ) f
  rw [h0, map_zero] at h1
  simpa using h1.symm

def evalT (x : J → Ω) : MvPolynomial J ℂ →ₐ[ℂ] ℂ ⊗[ℚ] Ω :=
  aeval fun j => (1 : ℂ) ⊗ₜ[ℚ] x j

theorem evalT_map_rat (x : J → Ω) (b : MvPolynomial J ℚ) :
    evalT x (map (algebraMap ℚ ℂ) b) = (1 : ℂ) ⊗ₜ[ℚ] aeval x b := by
  unfold evalT
  rw [MvPolynomial.aeval_map_algebraMap]
  have h := MvPolynomial.comp_aeval_apply x (Algebra.TensorProduct.includeRight : Ω →ₐ[ℚ] ℂ ⊗[ℚ] Ω) b
  simpa [Algebra.TensorProduct.includeRight_apply] using h.symm

theorem evalT_map_int (x : J → Ω) (f : MvPolynomial J ℤ) :
    evalT x (map (Int.castRingHom ℂ) f) = (1 : ℂ) ⊗ₜ[ℚ] aeval x f := by
  unfold evalT
  rw [← algebraMap_int_eq, MvPolynomial.aeval_map_algebraMap]
  have h := MvPolynomial.comp_aeval_apply x
    ((Algebra.TensorProduct.includeRight : Ω →ₐ[ℚ] ℂ ⊗[ℚ] Ω).restrictScalars ℤ) f
  simpa [Algebra.TensorProduct.includeRight_apply] using h.symm

theorem coeff_eq_zero_of_vanish {x : J → Ω} {r : ℕ} {b : Fin r → MvPolynomial J ℚ}
    (hs : LinearIndependent ℚ fun k => aeval x (b k)) {c : Fin r → ℂ}
    (h : ∀ z : J → ℂ, (∀ f ∈ coordIdeal ℤ x, eval z (map (Int.castRingHom ℂ) f) = 0) →
      ∑ k, c k * secFun (b k) z = 0) : c = 0 := by
  classical
  set I : Ideal (MvPolynomial J ℂ) := Ideal.map (MvPolynomial.map (Int.castRingHom ℂ)) (coordIdeal ℤ x) with hI
  set P : MvPolynomial J ℂ := ∑ k, MvPolynomial.C (c k) * MvPolynomial.map (algebraMap ℚ ℂ) (b k) with hP
  have hPmem : P ∈ MvPolynomial.vanishingIdeal ℂ (MvPolynomial.zeroLocus ℂ I) := by
    rw [MvPolynomial.mem_vanishingIdeal_iff]
    intro z hz
    rw [MvPolynomial.mem_zeroLocus_iff] at hz
    have hz' : ∀ f ∈ coordIdeal ℤ x, eval z (map (Int.castRingHom ℂ) f) = 0 := by
      intro f hf
      have hf' := hz _ (Ideal.mem_map_of_mem _ hf)
      exact hf'
    have hsum := h z hz'
    change eval z P = 0
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hP, map_sum]
    simpa [secFun] using hsum
  rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical] at hPmem
  obtain ⟨n, hn⟩ := hPmem
  have hker : I ≤ RingHom.ker (evalT x : MvPolynomial J ℂ →+* ℂ ⊗[ℚ] Ω) := by
    rw [hI, Ideal.map_le_iff_le_comap]
    intro f hf
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change evalT x (map (Int.castRingHom ℂ) f) = 0
    rw [evalT_map_int, aeval_eq_zero_of_mem_coordIdeal hf, TensorProduct.tmul_zero]
  have hnil : IsNilpotent (evalT x P) := ⟨n, by
    rw [← map_pow]
    exact hker hn⟩
  have hev : evalT x P = ∑ k, c k ⊗ₜ[ℚ] aeval x (b k) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hP, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, evalT_map_rat, ← MvPolynomial.algebraMap_eq, AlgHom.commutes,
      Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    simp
  rw [hev] at hnil
  exact nilp_coeff_eq_zero hs hnil

end Poly

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ComplexHessianTransposeIsHermitian
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.HasFDerivAtMvPolynomialEval
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Complex Filter Topology Finset Matrix

open MvPolynomial Complex Filter Topology

section

variable {D : ℕ}

theorem bilinear_real_imag_expand {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (B : V →L[ℝ] V →L[ℝ] ℝ)
    (a b : Fin D → ℝ) (e f : Fin D → V) :
    B (∑ i, (a i • e i + b i • f i)) (∑ j, (a j • e j + b j • f j)) =
      ∑ i, ∑ j, (a i * a j * B (e i) (e j) + a i * b j * B (e i) (f j) +
        b i * a j * B (f i) (e j) + b i * b j * B (f i) (f j)) := by
  have key : ∀ (u w : Fin D → V), B (∑ i, u i) (∑ j, w j) = ∑ i, ∑ j, B (u i) (w j) := by
    intro u w
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, ContinuousLinearMap.sum_apply]
    first
      | rfl
      | exact Finset.sum_comm
  rw [key]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [map_add (f := _), map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem decompose_real_imag_basis (v : Fin D → ℂ) :
    v = ∑ i, ((v i).re • (Pi.single i (1 : ℂ) : Fin D → ℂ) +
      (v i).im • (I • (Pi.single i (1 : ℂ) : Fin D → ℂ))) := by
  funext k
  rw [Finset.sum_apply]
  simp only [Pi.add_apply, Pi.smul_apply, Pi.single_apply, Finset.sum_add_distrib]
  apply Complex.ext <;> simp

theorem leviForm_eq_complexHessian (φ : (Fin D → ℂ) → ℝ) (y w : Fin D → ℂ) :
    (fderiv ℝ (fderiv ℝ φ) y w w + fderiv ℝ (fderiv ℝ φ) y (I • w) (I • w)) / 4 =
      (∑ i, ∑ j, starRingEnd ℂ (w i) * cxHessian φ y j i * w j).re := by
  have hw := decompose_real_imag_basis w
  have hIw : I • w = ∑ i, ((-(w i).im) • (Pi.single i (1 : ℂ) : Fin D → ℂ) +
      (w i).re • (I • (Pi.single i (1 : ℂ) : Fin D → ℂ))) := by
    rw [decompose_real_imag_basis (I • w)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, Complex.I_mul_re, Complex.I_mul_im]
  have e1 := bilinear_real_imag_expand (fderiv ℝ (fderiv ℝ φ) y) (fun i => (w i).re) (fun i => (w i).im)
      (fun i => (Pi.single i (1 : ℂ) : Fin D → ℂ)) (fun i => I • (Pi.single i (1 : ℂ) : Fin D → ℂ))
  have e2 := bilinear_real_imag_expand (fderiv ℝ (fderiv ℝ φ) y) (fun i => -(w i).im) (fun i => (w i).re)
      (fun i => (Pi.single i (1 : ℂ) : Fin D → ℂ)) (fun i => I • (Pi.single i (1 : ℂ) : Fin D → ℂ))
  simp only [← hw] at e1
  simp only [← hIw] at e2
  rw [e1, e2, ← Finset.sum_add_distrib]
  simp only [Complex.re_sum]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin D))) (t := Finset.univ)
    (f := fun i j => ((starRingEnd ℂ) (w i) * cxHessian φ y j i * w j).re)]
  rw [div_eq_iff (by norm_num : (4 : ℝ) ≠ 0), Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [cxHessian]
  simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.div_re, Complex.div_im, Complex.conj_re,
    Complex.conj_im, Complex.normSq]
  ring

end

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Complex Filter Topology Finset Matrix
open scoped ComplexOrder

section

variable {D : ℕ}

theorem mixedDiscriminant_constant (A : Matrix (Fin D) (Fin D) ℂ) :
    mixedDisc (fun _ => A) = A.det := by
  show (1 / (D.factorial : ℂ)) * ∑ S : Finset (Fin D), (-1) ^ (D - S.card) * (∑ _k ∈ S, A).det = A.det
  have h1 : ∀ S : Finset (Fin D), (-1 : ℂ) ^ (D - S.card) * (∑ _k ∈ S, A).det =
      ((-1 : ℂ) ^ (D - S.card) * (S.card : ℂ) ^ D) * A.det := by
    intro S
    rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ, Matrix.det_smul, Fintype.card_fin]
    ring
  simp_rw [h1]
  rw [← Finset.sum_mul]
  have h2 : ∑ S : Finset (Fin D), (-1 : ℂ) ^ (D - S.card) * (S.card : ℂ) ^ D = D.factorial := by
    have h3 := congrFun (fwdDiff_iter_eq_factorial (R := ℂ) (n := D)) 0
    rw [fwdDiff_iter_eq_sum_shift] at h3
    rw [← Finset.powerset_univ,
      Finset.sum_powerset_apply_card (fun k => (-1 : ℂ) ^ (D - k) * (k : ℂ) ^ D),
      Finset.card_univ, Fintype.card_fin]
    simp only [Pi.natCast_apply, zero_add, nsmul_eq_mul, mul_one, zsmul_eq_mul] at h3
    rw [← h3]
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast
    ring
  rw [h2]
  have : (D.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero D)
  field_simp

theorem complexHessian_transpose_isHermitian {φ : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ} (h : IsSymmSndFDerivAt ℝ φ y) (c : ℝ) :
    ((c : ℂ) • (cxHessian φ y).transpose).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.smul_apply, cxHessian,
    smul_eq_mul]
  rw [h (Pi.single j 1) (Pi.single i 1), h (I • Pi.single j 1) (I • Pi.single i 1),
    h (Pi.single j 1) (I • Pi.single i 1), h (I • Pi.single j 1) (Pi.single i 1)]
  apply Complex.ext <;> simp

theorem im_hermitian_quadraticForm {n : Type*} [Fintype n] {M : Matrix n n ℂ} (hM : M.IsHermitian)
    (w : n → ℂ) : (star w ⬝ᵥ M *ᵥ w).im = 0 := by
  have h := hM.im_star_dotProduct_mulVec_self w
  simpa using h

theorem complexHessian_posSemidef {φ : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ} (h : IsSymmSndFDerivAt ℝ φ y)
    {c : ℝ} (hc : 0 ≤ c) (hL : ∀ w, 0 ≤ leviForm φ y w) :
    ((c : ℂ) • (cxHessian φ y).transpose).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (complexHessian_transpose_isHermitian h c) fun w => ?_
  rw [Complex.nonneg_iff]
  refine ⟨?_, (im_hermitian_quadraticForm (complexHessian_transpose_isHermitian h c) w).symm⟩
  have e : (star w ⬝ᵥ ((c : ℂ) • (cxHessian φ y).transpose) *ᵥ w) =
      (c : ℂ) * ∑ i, ∑ j, starRingEnd ℂ (w i) * cxHessian φ y j i * w j := by
    simp only [dotProduct, mulVec, Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul,
      Pi.star_apply, Finset.mul_sum, Complex.star_def]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e, Complex.re_ofReal_mul, ← leviForm_eq_complexHessian]
  exact mul_nonneg hc (hL w)

end

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.AMDefs
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def unitDeg [DecidableEq K] (k₀ : K) : K → ℤ := fun k => if k = k₀ then 1 else 0

def blockDeg [DecidableEq K] (k₀ : K) (n : ℕ) : K → ℕ := fun k => if k = k₀ then n else 0

variable {Ω : Type} [Field Ω] [CharZero Ω]

def IsSecBasisM [DecidableEq K] (y : (Σ k, ι k) → Ω) (k₀ : K) (n : ℕ) {r : ℕ}
    (b : Fin r → MvPolynomial (Σ k, ι k) ℚ) : Prop :=
  (∀ j, ∃ f : MRing ι, IsMultiHomog f (blockDeg k₀ n) ∧ b j = map (Int.castRingHom ℚ) f) ∧
    LinearIndependent ℤ (fun j => aeval y (b j)) ∧
    (Submodule.span ℤ (Set.range fun j => aeval y (b j))).toAddSubgroup = secM y (blockDeg k₀ n)


end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end
end
