module

public import GroundTheory.AutomorphicForms.SphericalIntegral
public import GroundTheory.LocalFields.LocalFourierHaar

@[expose] public section

section -- merged from GroundTheory.AutomorphicForms.SatakeSymmetric
noncomputable section

namespace GroundTheory.Automorphic

open AddMonoidAlgebra MvPolynomial

namespace Spherical

variable {n : ℕ}

def permCoord (σ : Equiv.Perm (Fin n)) : (Fin n → ℤ) →+ (Fin n → ℤ) where
  toFun l := l ∘ σ.symm
  map_zero' := rfl
  map_add' _ _ := rfl

theorem permCoord_apply (σ : Equiv.Perm (Fin n)) (l : Fin n → ℤ) : permCoord σ l = l ∘ σ.symm :=
  rfl

def permAct (σ : Equiv.Perm (Fin n)) : LaurentRing (n := n) →ₐ[ℂ] LaurentRing (n := n) :=
  mapDomainAlgHom ℂ ℂ (permCoord σ)

theorem permAct_single (σ : Equiv.Perm (Fin n)) (l : Fin n → ℤ) (c : ℂ) :
    permAct σ (single l c) = single (l ∘ σ.symm) c := by
  simp [permAct, mapDomainAlgHom, mapDomain_single, permCoord_apply]

theorem permAct_mul (σ τ : Equiv.Perm (Fin n)) :
    permAct (σ * τ) = (permAct σ).comp (permAct τ) := by
  refine AddMonoidAlgebra.algHom_ext (fun l => ?_) (Subsingleton.elim _ _)
  rw [AlgHom.comp_apply, permAct_single, permAct_single, permAct_single]
  congr 1

theorem permAct_one : permAct (1 : Equiv.Perm (Fin n)) = AlgHom.id ℂ (LaurentRing (n := n)) := by
  refine AddMonoidAlgebra.algHom_ext (fun l => ?_) (Subsingleton.elim _ _)
  rw [permAct_single, AlgHom.id_apply]
  rfl

theorem evalAt_permAct (w : Fin n → ℂˣ) (σ : Equiv.Perm (Fin n)) (p : LaurentRing (n := n)) :
    evalAt w (permAct σ p) = evalAt (w ∘ σ) p := by
  have : (evalAt w).comp (permAct σ) = evalAt (w ∘ σ) := by
    refine AddMonoidAlgebra.algHom_ext (fun l => ?_) (Subsingleton.elim _ _)
    rw [AlgHom.comp_apply, permAct_single, evalAt_single, evalAt_single, monomialChar_apply,
      monomialChar_apply]
    congr 1
    exact Fintype.prod_equiv σ.symm _ _ fun i => by simp
  exact AlgHom.congr_fun this p


variable (n) in
def symmetricLaurent : Subalgebra ℂ (LaurentRing (n := n)) where
  carrier := {p | ∀ σ, permAct σ p = p}
  mul_mem' {a b} ha hb σ := by
    change permAct σ (a * b) = a * b
    rw [map_mul, ha σ, hb σ]
  add_mem' {a b} ha hb σ := by
    change permAct σ (a + b) = a + b
    rw [map_add (f := _), ha σ, hb σ]
  algebraMap_mem' c σ := AlgHom.commutes _ c

theorem monomial_const_mem (c : ℤ) : monomial (fun _ : Fin n => c) ∈ symmetricLaurent (n := n) := by
  intro σ
  change permAct σ (single (fun _ : Fin n => c) 1) = single (fun _ : Fin n => c) 1
  rw [permAct_single]
  rfl

def natToInt : (Fin n →₀ ℕ) →+ (Fin n → ℤ) where
  toFun s i := s i
  map_zero' := by
    funext i
    simp
  map_add' s t := by
    funext i
    simp

theorem natToInt_apply (s : Fin n →₀ ℕ) (i : Fin n) : natToInt s i = s i :=
  rfl

theorem natToInt_injective : Function.Injective (natToInt (n := n)) := fun s t h => by
  ext i
  exact Int.ofNat_inj.1 (congrFun h i)


variable (n) in
def polyEmb : MvPolynomial (Fin n) ℂ →ₐ[ℂ] LaurentRing (n := n) :=
  mapDomainAlgHom ℂ ℂ natToInt

theorem polyEmb_monomial (s : Fin n →₀ ℕ) (c : ℂ) :
    polyEmb (n := n) (MvPolynomial.monomial s c) = single (natToInt s) c := by
  simp [polyEmb, mapDomainAlgHom, MvPolynomial.monomial, mapDomain_single]

theorem polyEmb_X (i : Fin n) : polyEmb (n := n) (X i) = monomial (Pi.single i 1) := by
  rw [X, polyEmb_monomial]
  congr 1
  funext j
  rw [natToInt_apply, Finsupp.single_apply, Pi.single_apply]
  by_cases h : j = i
  · subst h
    simp
  · simp [h, Ne.symm h]

theorem polyEmb_injective : Function.Injective (polyEmb (n := n)) :=
  mapDomain_injective natToInt_injective

theorem polyEmb_rename (σ : Equiv.Perm (Fin n)) (Q : MvPolynomial (Fin n) ℂ) :
    polyEmb (n := n) (rename σ Q) = permAct σ (polyEmb (n := n) Q) := by
  have : (polyEmb (n := n)).comp (rename σ) = (permAct σ).comp (polyEmb (n := n)) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, rename_X, polyEmb_X, polyEmb_X]
    change single (Pi.single (σ i) 1) 1 = permAct σ (single (Pi.single i 1) 1)
    rw [permAct_single]
    congr 1
    funext j
    simp only [Pi.single_apply, Function.comp_apply]
    by_cases h : j = σ i
    · subst j
      simp
    · have h' : σ.symm j ≠ i := by
        intro hj
        apply h
        simpa using congrArg σ hj
      simp [h, h']
  exact AlgHom.congr_fun this Q

theorem mem_range_polyEmb {q : LaurentRing (n := n)} (hq : ∀ l ∈ q.coeff.support, ∀ i, 0 ≤ l i) :
    q ∈ (polyEmb (n := n)).range := by
  classical
  rw [← AddMonoidAlgebra.sum_coeff_single q]
  refine Subalgebra.sum_mem _ fun l hl => ?_
  refine ⟨MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm fun i => (l i).toNat) (q.coeff l), ?_⟩
  change polyEmb (n := n) _ = _
  rw [polyEmb_monomial]
  congr 1
  funext i
  simp [natToInt_apply, Int.toNat_of_nonneg (hq l hl i)]

theorem symmetricLaurent_le {A : Subalgebra ℂ (LaurentRing n)}
    (he : ∀ k, polyEmb (n := n) (esymm (Fin n) ℂ k) ∈ A) (hinv : monomial (fun _ => (-1 : ℤ)) ∈ A) :
    symmetricLaurent (n := n) ≤ A := by
  classical
  intro p hp
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ l ∈ p.coeff.support, ∀ i, -(N : ℤ) ≤ l i := by
    refine ⟨p.coeff.support.sup fun l => Finset.univ.sup fun i => (l i).natAbs, fun l hl i => ?_⟩
    have h1 : (l i).natAbs ≤ Finset.univ.sup fun i => (l i).natAbs :=
      Finset.le_sup (f := fun i => (l i).natAbs) (Finset.mem_univ i)
    have h2 := Finset.le_sup (f := fun l : Fin n → ℤ => Finset.univ.sup fun i => (l i).natAbs) hl
    have h3 : ((l i).natAbs : ℤ) ≤ _ := Nat.cast_le.2 (h1.trans h2)
    rw [Int.natCast_natAbs] at h3
    have h4 := neg_abs_le (l i)
    linarith
  set c : LaurentRing (n := n) := monomial (fun _ => (N : ℤ))
  set q := c * p
  have hq : q ∈ symmetricLaurent (n := n) := Subalgebra.mul_mem _ (monomial_const_mem _) hp
  have hqs : ∀ l ∈ q.coeff.support, ∀ i, 0 ≤ l i := by
    intro l hl i
    have hsub := AddMonoidAlgebra.support_coeff_mul_subset c p hl
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 hsub
    have ha' : a = fun _ => (N : ℤ) := by
      have := Finsupp.support_single_subset ha
      simpa using this
    subst ha'
    have := hN b hb i
    simp only [Pi.add_apply]
    omega
  obtain ⟨Q, hQ⟩ := mem_range_polyEmb hqs
  change polyEmb (n := n) Q = q at hQ
  have hQsym : Q ∈ symmetricSubalgebra (Fin n) ℂ := by
    rw [mem_symmetricSubalgebra]
    intro σ
    apply polyEmb_injective
    rw [polyEmb_rename, hQ, hq σ]
  obtain ⟨P, hP⟩ := esymmAlgHom_surjective ℂ (σ := Fin n) (n := n) (Fintype.card_fin n).le ⟨Q, hQsym⟩
  have hQP : Q = aeval (fun i : Fin n => esymm (Fin n) ℂ (i + 1)) P := by
    rw [← esymmAlgHom_apply, hP]
  have hqA : q ∈ A := by
    rw [← hQ, hQP, ← AlgHom.comp_apply, comp_aeval]
    have : aeval (fun i : Fin n => polyEmb (n := n) (esymm (Fin n) ℂ (i + 1))) P ∈
        (aeval fun i : Fin n => polyEmb (n := n) (esymm (Fin n) ℂ (i + 1))).range :=
      AlgHom.mem_range_self _ _
    rw [aeval_range] at this
    exact Algebra.adjoin_le (Set.range_subset_iff.2 fun i => he _) this
  have hp' : p = monomial (fun _ => (-1 : ℤ)) ^ N * q := by
    have hz : (N • fun _ : Fin n => (-1 : ℤ)) + (fun _ => (N : ℤ)) = 0 := by
      funext i
      simp
    change p = single (fun _ : Fin n => (-1 : ℤ)) (1 : ℂ) ^ N *
      (single (fun _ : Fin n => (N : ℤ)) 1 * p)
    rw [← mul_assoc, AddMonoidAlgebra.single_pow, one_pow, AddMonoidAlgebra.single_mul_single,
      hz, mul_one, ← AddMonoidAlgebra.one_def, one_mul]
  rw [hp']
  exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hinv _) hqA

def orbitSum (ν : Fin n → ℤ) : LaurentRing (n := n) :=
  ∑ σ : Equiv.Perm (Fin n), monomial (ν ∘ σ.symm)

theorem orbitSum_mem (ν : Fin n → ℤ) : orbitSum ν ∈ symmetricLaurent (n := n) := by
  intro τ
  set_option synthInstance.maxHeartbeats 100000 in
    rw [orbitSum, map_sum]
  simp only [monomial, permAct_single]
  exact Fintype.sum_equiv (Equiv.mulLeft τ) _ _ fun σ => by congr 1

theorem coeff_orbitSum (ν l : Fin n → ℤ) :
    (orbitSum ν).coeff l = ((Finset.univ.filter fun σ : Equiv.Perm (Fin n) =>
      ν ∘ σ.symm = l).card : ℂ) := by
  classical
  rw [orbitSum, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, Finset.card_filter,
    Nat.cast_sum]
  simp only [monomial]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  split_ifs <;> simp

theorem exists_of_coeff_orbitSum_ne_zero {ν l : Fin n → ℤ} (h : (orbitSum ν).coeff l ≠ 0) :
    ∃ σ : Equiv.Perm (Fin n), ν ∘ σ.symm = l := by
  rw [coeff_orbitSum] at h
  obtain ⟨σ, hσ⟩ := Finset.card_ne_zero.1 (fun h' => h (by rw [h', Nat.cast_zero]))
  exact ⟨σ, (Finset.mem_filter.1 hσ).2⟩

theorem coeff_orbitSum_self_ne_zero (ν : Fin n → ℤ) : (orbitSum ν).coeff ν ≠ 0 := by
  rw [coeff_orbitSum, Nat.cast_ne_zero, Finset.card_ne_zero]
  exact ⟨1, Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩⟩

theorem orbitSum_ne_zero (ν : Fin n → ℤ) : orbitSum ν ≠ 0 := fun h =>
  coeff_orbitSum_self_ne_zero ν (by rw [h]; rfl)

theorem comp_eq_of_antitone {ν : Fin n → ℤ} (hν : Antitone ν) (σ : Equiv.Perm (Fin n))
    (hσ : Antitone (ν ∘ σ)) : ν ∘ σ = ν := by
  set f : Fin n → ℤ := fun i => -ν i
  have hf : Monotone (f ∘ σ) := fun i j hij => neg_le_neg (hσ hij)
  have hf1 : Monotone (f ∘ (1 : Equiv.Perm (Fin n))) := fun i j hij => neg_le_neg (hν hij)
  have e1 := (Tuple.comp_sort_eq_comp_iff_monotone (f := f) (σ := σ)).2 hf
  have e2 := (Tuple.comp_sort_eq_comp_iff_monotone (f := f) (σ := 1)).2 hf1
  have : f ∘ σ = f := by
    rw [e1, ← e2]
    rfl
  funext i
  have := congrFun this i
  simpa [f] using this

end Spherical

end GroundTheory.Automorphic
end
end

noncomputable section

namespace GroundTheory.Automorphic

open MeasureTheory GLnLocal Iwasawa Parabolic HeckeAlgebra AddMonoidAlgebra
open scoped NNReal

namespace Spherical

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

theorem prod_zpow_eq_zpow_sum {G₀ : Type*} [CommGroupWithZero G₀] {a : G₀} (ha : a ≠ 0)
    {ι : Type*} (s : Finset ι) (f : ι → ℤ) : ∏ i ∈ s, a ^ f i = a ^ ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.prod_insert hj, Finset.sum_insert hj, ih, zpow_add₀ ha]


variable (F) in
theorem modulus_uniformizer :
    Measures.modulus (GLnLocal.uniformizer F : F) = ((qF F : ℝ≥0))⁻¹ := by
  borelize F
  have h := Measures.modulus_units (uniformizerUnit F)
  rw [coe_uniformizerUnit] at h
  rw [h, GroundTheory.LocalField.distribHaarChar_eq_modulus, coe_uniformizerUnit,
    GroundTheory.LocalField.modulus_of_ne_zero,
    GroundTheory.LocalField.ord_uniformizer (irreducible_uniformizer F)]
  · simp [qF, GroundTheory.LocalField.residueCard]
  · exact (uniformizerUnit F).ne_zero

def rhoPair (l : Fin n → ℤ) : ℤ := ∑ i : Fin n, ((n : ℤ) - 1 - 2 * (i : ℕ)) * l i

theorem rhoPair_single (i : Fin n) :
    rhoPair (Pi.single i 1 : Fin n → ℤ) = (n : ℤ) - 1 - 2 * (i : ℕ) := by
  rw [rhoPair, Finset.sum_eq_single i (fun j _ hj => by simp [hj])
    (fun h => absurd (Finset.mem_univ i) h)]
  simp


variable (F n) in
def torusBorel (l : Fin n → ℤ) : blockUpper F n (id : Fin n → Fin n) :=
  ⟨torusPow F n l, torusPow_mem_borel F n l⟩


variable (F) in
def halfModulus (l : Fin n → ℤ) : ℂ :=
  sqrtModular F n id (torusBorel F n l)

theorem halfModulus_add (l l' : Fin n → ℤ) :
    halfModulus F (l + l') = halfModulus F l * halfModulus F l' := by
  rw [halfModulus, halfModulus, halfModulus, ← map_mul]
  congr 1
  exact Subtype.ext (torusPow_add l l')

theorem halfModulus_zero : halfModulus F (0 : Fin n → ℤ) = 1 := by
  rw [halfModulus, ← map_one (sqrtModular F n id)]
  congr 1
  exact Subtype.ext torusPow_zero


variable (F) in
def sqrtQ : ℂ := ((NNReal.sqrt (qF F : ℝ≥0) : ℝ) : ℂ)

theorem qF_nnreal_ne_zero : ((qF F : ℝ≥0)) ≠ 0 := by
  exact_mod_cast (qF_pos (F := F)).ne'

theorem sqrtQ_ne_zero : sqrtQ F ≠ 0 := by
  rw [sqrtQ, Complex.ofReal_ne_zero, NNReal.coe_ne_zero, Ne, NNReal.sqrt_eq_zero]
  exact qF_nnreal_ne_zero

theorem sqrtQ_sq : sqrtQ F ^ 2 = (qF F : ℂ) := by
  rw [sqrtQ, ← Complex.ofReal_pow, ← NNReal.coe_pow, NNReal.sq_sqrt]
  norm_cast

theorem modularCharacter_torusBorel (l : Fin n → ℤ) :
    Measure.modularCharacter (torusBorel F n l) = ((qF F : ℝ≥0)) ^ (-rhoPair l) := by
  rw [Measures.modularCharacter_borel]
  have hd : ∀ i, (((torusBorel F n l : blockUpper F n (id : Fin n → Fin n)) : GL (Fin n) F) :
      Matrix (Fin n) (Fin n) F) i i = (GLnLocal.uniformizer F : F) ^ l i := fun i => by
    simp [torusBorel, coe_torusPow]
  simp only [hd, map_zpow₀, modulus_uniformizer]
  rw [rhoPair, ← Finset.sum_neg_distrib, ← prod_zpow_eq_zpow_sum qF_nnreal_ne_zero]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [inv_zpow', ← zpow_mul]
  congr 1
  ring

theorem halfModulus_eq (l : Fin n → ℤ) : halfModulus F l = sqrtQ F ^ (-rhoPair l) := by
  have h1 : NNReal.sqrt (Measure.modularCharacter (torusBorel F n l)) =
      NNReal.sqrt (qF F : ℝ≥0) ^ (-rhoPair l) := by
    rw [modularCharacter_torusBorel, NNReal.sqrt_eq_iff_eq_sq, ← zpow_natCast, ← zpow_mul,
      mul_comm, zpow_mul, zpow_natCast, NNReal.sq_sqrt]
  change ((NNReal.sqrt (Measure.modularCharacter (torusBorel F n l)) : ℝ) : ℂ) = _
  rw [h1, NNReal.coe_zpow, Complex.ofReal_zpow]
  rfl

theorem halfModulus_ne_zero (l : Fin n → ℤ) : halfModulus F l ≠ 0 := by
  rw [halfModulus_eq]
  exact zpow_ne_zero _ sqrtQ_ne_zero


variable (F n) in
def halfPoint : Fin n → ℂˣ :=
  fun i => Units.mk0 (halfModulus F (Pi.single i 1)) (halfModulus_ne_zero _)

theorem monomialChar_halfPoint (l : Fin n → ℤ) : monomialChar l (halfPoint F n) = halfModulus F l := by
  rw [monomialChar_apply, halfModulus_eq, rhoPair, ← Finset.sum_neg_distrib,
    ← prod_zpow_eq_zpow_sum sqrtQ_ne_zero]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Units.val_zpow_eq_zpow_val, halfPoint, Units.val_mk0, halfModulus_eq, rhoPair_single,
    ← zpow_mul]
  congr 1
  ring


variable (F n) in
def normHom : Multiplicative (Fin n → ℤ) →* LaurentRing n where
  toFun l := single (Multiplicative.toAdd l) (halfModulus F (Multiplicative.toAdd l))
  map_one' := by
    rw [toAdd_one, halfModulus_zero]
    rfl
  map_mul' a b := by
    rw [toAdd_mul, halfModulus_add, single_mul_single]


variable (F n) in
def normalize : LaurentRing n →ₐ[ℂ] LaurentRing n :=
  AddMonoidAlgebra.lift ℂ (LaurentRing n) (Fin n → ℤ) (normHom F n)

theorem normalize_single (l : Fin n → ℤ) (c : ℂ) :
    normalize F n (single l c) = single l (c * halfModulus F l) := by
  rw [normalize, AddMonoidAlgebra.lift_single]
  change c • single l (halfModulus F l) = _
  rw [smul_single']

theorem coeff_normalize (p : LaurentRing n) (l : Fin n → ℤ) :
    (normalize F n p).coeff l = halfModulus F l * p.coeff l := by
  classical
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p p' hp hp' => rw [map_add (f := _), coeff_add, coeff_add, Finsupp.add_apply, Finsupp.add_apply, hp,
      hp', mul_add]
  | single m c =>
    rw [normalize_single, coeff_single, coeff_single, Finsupp.single_apply, Finsupp.single_apply]
    split_ifs with h
    · subst h
      ring
    · simp

theorem normalize_injective : Function.Injective (normalize F n) := by
  intro p p' h
  apply AddMonoidAlgebra.coeff_injective
  ext l
  have := congrArg (fun r : LaurentRing n => r.coeff l) h
  simp only [coeff_normalize] at this
  exact mul_left_cancel₀ (halfModulus_ne_zero l) this

theorem evalAt_normalize (z : Fin n → ℂˣ) (p : LaurentRing n) :
    evalAt z (normalize F n p) = evalAt (z * halfPoint F n) p := by
  have : (evalAt z).comp (normalize F n) = evalAt (z * halfPoint F n) := by
    refine AddMonoidAlgebra.algHom_ext (fun l => ?_) (Subsingleton.elim _ _)
    rw [AlgHom.comp_apply, normalize_single, evalAt_single, evalAt_single, map_mul,
      monomialChar_halfPoint]
    ring
  exact AlgHom.congr_fun this p


variable (F n) in
def torusLevi (l : Fin n → ℤ) : levi F n (id : Fin n → Fin n) :=
  ⟨torusPow F n l, mem_levi.2 fun i j hij => by
    rw [coe_torusPow, Matrix.diagonal_apply_ne _ (by simpa using hij)]⟩


variable (F) in
def paramChar (z : Fin n → ℂˣ) : levi F n (id : Fin n → Fin n) →* ℂ :=
  unramifiedChar (z * halfPoint F n)

theorem isUnramified_paramChar (z : Fin n → ℂˣ) : IsUnramified (paramChar F z) :=
  isUnramified_unramifiedChar _

theorem paramChar_torusLevi (z : Fin n → ℂˣ) (l : Fin n → ℤ) :
    paramChar F z (torusLevi F n l) = monomialChar l z := by
  change monomialChar (iwasawaExponent F n (torusPow F n l)) (z * halfPoint F n) *
    invSqrtModular F n id (leviIncl (torusLevi F n l)) = _
  have h1 : leviIncl (torusLevi F n l) = torusBorel F n l := Subtype.ext rfl
  rw [iwasawaExponent_torusPow, h1, map_mul, monomialChar_halfPoint]
  have h2 : invSqrtModular F n id (torusBorel F n l) = (halfModulus F l)⁻¹ := rfl
  rw [h2, mul_assoc, mul_inv_cancel₀ (halfModulus_ne_zero l), mul_one]

theorem normalize_yElt (i : Fin n) :
    normalize F n (yElt F i) = sqrtQ F ^ ((n : ℤ) - 1) • monomial (Pi.single i 1) := by
  rw [yElt, normalize_single, smul_single', mul_one, halfModulus_eq, rhoPair_single, ← sqrtQ_sq,
    ← pow_mul, ← zpow_natCast, ← zpow_add₀ sqrtQ_ne_zero]
  congr 2
  have := i.is_lt
  push_cast [Nat.sub_sub, Nat.cast_sub (show 1 + (i : ℕ) ≤ n by omega)]
  ring

theorem normalize_esymm_yElt (k : ℕ) :
    normalize F n ((Finset.univ.val.map (yElt F (n := n))).esymm k) =
      (sqrtQ F ^ ((n : ℤ) - 1)) ^ k • polyEmb (n := n) (MvPolynomial.esymm (Fin n) ℂ k) := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.esymm_map_val, map_sum, MvPolynomial.esymm, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [map_prod, map_prod]
  simp only [normalize_yElt, polyEmb_X, smul_single', mul_one]
  rw [AddMonoidAlgebra.prod_single, AddMonoidAlgebra.prod_single, Finset.prod_const,
    Finset.prod_const_one, smul_single', mul_one, (Finset.mem_powersetCard.1 ht).2]

variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  {μ : Measure (GL (Fin n) F)} [μ.IsHaarMeasure]


variable (μ) in
def satakeTransform : SphericalHecke μ (F := F) (n := n) →ₐ[ℂ] LaurentRing n :=
  (normalize F n).comp (satakeHom μ)

theorem satakeTransform_apply (h : SphericalHecke μ (F := F) (n := n)) :
    satakeTransform μ h = normalize F n (satake μ h) :=
  rfl

theorem coeff_satakeTransform (h : SphericalHecke μ (F := F) (n := n)) (l : Fin n → ℤ) :
    (satakeTransform μ h).coeff l = halfModulus F l * (satake μ h).coeff l :=
  coeff_normalize _ l

theorem satakeTransform_injective : Function.Injective (satakeTransform μ (F := F) (n := n)) :=
  (normalize_injective (F := F)).comp satakeHom_injective

theorem sphericalCharacter_paramChar (z : Fin n → ℂˣ) (h : SphericalHecke μ (F := F) (n := n)) :
    sphericalCharacter μ (isUnramified_paramChar (F := F) z) h = evalAt z (satakeTransform μ h) := by
  rw [satakeTransform_apply, evalAt_normalize, evalAt_satake]
  rfl

theorem symmetricLaurent_le_range :
    symmetricLaurent (n := n) ≤ (satakeTransform μ (F := F) (n := n)).range := by
  have hK : (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2
      (measureReal_compactOpen_pos μ (isCompact_integralGL F n) (isOpen_integralGL F n)).ne'
  refine symmetricLaurent_le (fun k => ?_) ?_
  · obtain ⟨h, hh⟩ := (AlgHom.mem_range _).1 (esymm_yElt_mem (μ := μ) (F := F) (n := n) k)
    have hc : (sqrtQ F ^ ((n : ℤ) - 1)) ^ k ≠ 0 := pow_ne_zero _ (zpow_ne_zero _ sqrtQ_ne_zero)
    have : polyEmb (n := n) (MvPolynomial.esymm (Fin n) ℂ k) =
        ((sqrtQ F ^ ((n : ℤ) - 1)) ^ k)⁻¹ • satakeTransform μ h := by
      rw [satakeTransform_apply, ← satakeHom_apply, hh, normalize_esymm_yElt, smul_smul,
        inv_mul_cancel₀ hc, one_smul]
    rw [this]
    exact Subalgebra.smul_mem _ (AlgHom.mem_range_self _ _) _
  · have : monomial (fun _ => (-1 : ℤ)) = ((μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) *
        halfModulus F (fun _ : Fin n => (-1 : ℤ)))⁻¹ • satakeTransform μ (centralHecke μ) := by
      rw [satakeTransform_apply, satake_centralHecke, map_smul, normalize_single, smul_smul,
        smul_single']
      field_simp [hK, halfModulus_ne_zero (F := F) (fun _ : Fin n => (-1 : ℤ))]
    rw [this]
    exact Subalgebra.smul_mem _ (AlgHom.mem_range_self _ _) _

end Spherical

end GroundTheory.Automorphic
