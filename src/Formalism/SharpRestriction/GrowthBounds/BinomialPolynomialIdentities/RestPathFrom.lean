module

public import Formalism.SharpRestriction.GrowthBounds.StatementOfDegreeAndBound
public import Formalism.ThetaLogCoordinates.JacobiPathWeights.FinalP
public import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.IndexWeightsDominance
public import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.LemmaA2indepOf
public import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.JacobiMinorProof

@[expose] public section

section -- merged from Formalism.ThetaLogCoordinates.JacobiPathWeights.CorA3primeB
noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

def valP {k : Type*} [Field k] {n : ℕ} (isVec : ℕ → Bool) (i : ℕ) (G : MvPolynomial (ℕ × Fin n) k) :
    WithTop ℤ :=
  valS (ζ := Empty) isVec {j : ℕ | j < i} (rename Sum.inl G)

def lamP {k : Type*} [Field k] {n : ℕ} (isVec : ℕ → Bool) (i : ℕ) (G : MvPolynomial (ℕ × Fin n) k) :
    WithBot ℤ :=
  lam1S (ζ := Empty) isVec {j : ℕ | j < i} (rename Sum.inl G)

def geB (x : WithTop ℤ) (θ : WithBot ℤ) : Prop := ∀ t : ℤ, θ = (t : WithBot ℤ) → (t : WithTop ℤ) ≤ x

def leT (y : WithBot ℤ) (M : WithTop ℤ) : Prop := ∀ t : ℤ, M = (t : WithTop ℤ) → y ≤ (t : WithBot ℤ)

def GoodG {k : Type*} [Field k] {n : ℕ} (isVec : ℕ → Bool) (i : ℕ) (θ : WithBot ℤ) (M : WithTop ℤ)
    (G : MvPolynomial (ℕ × Fin n) k) : Prop :=
  geB (valP isVec i G) θ ∧ leT (lamP isVec i G) M

def psiFam (R : Type*) [CommRing R] (n N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (x : PathIdx n N isVec B) :
    MvPolynomial (ℕ × Fin n) R :=
  psiPath R isVec x.1.1 N x.1.2

def FactSplit : Prop :=
  ∀ (k : Type) [Field k] (n N i : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (θ : WithBot ℤ) (M : WithTop ℤ)
    (G : MvPolynomial (ℕ × Fin n) k), i ≤ N → G ∈ polB k n N B →
    ∃ (T : Finset (ℕ × Fin n →₀ ℕ)) (Gc : (ℕ × Fin n →₀ ℕ) → MvPolynomial (ℕ × Fin n) k),
      (∀ β ∈ T, ∀ j, ∑ a, β (j, a) = if i ≤ j ∧ j < N then B j else 0) ∧
      (∀ β ∈ T, Gc β ∈ polB k n i B) ∧
      G = ∑ β ∈ T, Gc β * monomial β 1 ∧
      (GoodG isVec i θ M G → ∀ β ∈ T, GoodG isVec i θ M (Gc β))

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
end
end

section -- merged from Formalism.ThetaLogCoordinates.JacobiPathWeights.PathBasisTheorem
section -- merged from Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.GoodWOfWeight
section -- merged from Formalism.ThetaLogCoordinates.JacobiPathWeights.GenSpaceFacts
noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

def genPoint {k ι ζ : Type*} [Field k] {n : ℕ} (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
    (G : MvPolynomial (LVar ι ζ n) k) : MvPolynomial (LVar ι ζ n) (GenField k n) :=
  sharpHom isVec S (genMat k n) (genMat k n)⁻¹
    (map ((algebraMap (MvPolynomial (Fin n × Fin n) k) (GenField k n)).comp C) G)

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
end
end

section -- merged from Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.GenSpace
noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

namespace GS

section Slices

variable {k : Type*} [Field k] {σ : Type*}
variable {A B D : Type*} [CommRing A] [CommRing B] [CommRing D] [Algebra k A] [Algebra k B] [Algebra k D]

end Slices

section Sharp

variable {ι ζ : Type*} {n : ℕ} (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
variable {A B : Type*} [CommRing A] [CommRing B]

variable {isVec S}

variable (isVec S)

end Sharp

section Universal

variable (k : Type*) [Field k] (n : ℕ)

variable {k n}
variable {B : Type*} [CommRing B] [Algebra k B]

theorem genMat_isUnit : IsUnit (genMat k n).det := isUnit_iff_ne_zero.mpr (genMat_det_ne k n)

end Universal

section Act

variable {k : Type*} [Field k] {ι ζ : Type*} {n : ℕ} (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]

end Act

section Torus

variable {ι ζ : Type*} {n : ℕ} (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]

variable (A : Type*) [CommRing A]

variable {A}

variable {k : Type*} [Field k] [Algebra k A]

end Torus

section Weights

variable {k : Type*} [Field k] {ι ζ : Type*} {n : ℕ} (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]

end Weights

section Exponents

variable {k : Type*} [Field k] {ι ζ : Type*} {n : ℕ} (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]

variable (φ : MvPolynomial (LVar ι ζ n) k →ₗ[k] MvPolynomial (LVar ι ζ n) k)
  (φL : MvPolynomial (LVar ι ζ n) (GenField k n) →ₗ[GenField k n] MvPolynomial (LVar ι ζ n) (GenField k n))
  (h1 : ∀ f, φL (map (genφ k n) f) = map (genφ k n) (φ f))
  (h2 : ∀ f, genPoint isVec S (φ f) = φL (genPoint isVec S f))

include h1 h2

end Exponents

end GS

open GS

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
end
end

noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

namespace DominanceOrderLemmas

theorem domLe_refl {n : ℕ} (ν : Fin n → ℤ) : DomLe ν ν := ⟨rfl, fun _ => le_rfl⟩

theorem domLe_trans {n : ℕ} {a b c : Fin n → ℤ} (h1 : DomLe a b) (h2 : DomLe b c) : DomLe a c :=
  ⟨h1.1.trans h2.1, fun j => (h1.2 j).trans (h2.2 j)⟩

theorem vars_of_polB {R : Type*} [CommRing R] {n N : ℕ} {B : ℕ → ℕ} {G : MvPolynomial (ℕ × Fin n) R}
    (hG : G ∈ polB R n N B) : ∀ x ∈ G.vars, x.1 < N := by
  intro x hx
  by_contra hlt
  push_neg at hlt
  have hGi := (Submodule.mem_iInf _).mp hG x.1
  rw [if_neg (not_lt.mpr hlt), mem_weightedHomogeneousSubmodule] at hGi
  obtain ⟨e, he, hex⟩ := (MvPolynomial.mem_vars_iff_mem_support x).mp hx
  have h0 := hGi (mem_support_iff.mp he)
  have hpos : 0 < e x := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hex)
  rw [Finsupp.weight_apply, Finsupp.sum] at h0
  have hle := Finset.single_le_sum (f := fun y => e y • (if y.1 = x.1 then 1 else 0 : ℕ))
    (fun _ _ => Nat.zero_le _) hex
  simp only [if_true, smul_eq_mul, mul_ite, mul_one, mul_zero] at hle h0
  omega

theorem actAll_X {L : Type*} [CommRing L] {n : ℕ} (isVec : ℕ → Bool) (g gi : Matrix (Fin n) (Fin n) L)
    (i : ℕ) (a : Fin n) :
    actAll isVec g gi (X (i, a)) =
      if isVec i then ∑ b, X (i, b) * C (g b a) else ∑ b, X (i, b) * C (gi a b) := by
  unfold actAll
  rw [aeval_X]
  split_ifs <;> simp [Matrix.vecMul, dotProduct]

theorem vars_actX {L : Type*} [CommRing L] [Nontrivial L] {n : ℕ} (isVec : ℕ → Bool)
    (g gi : Matrix (Fin n) (Fin n) L) (x : ℕ × Fin n) :
    ∀ y ∈ (actAll isVec g gi (X x)).vars, y.1 = x.1 := by
  intro y hy
  rw [actAll_X] at hy
  split_ifs at hy <;>
  · obtain ⟨b, -, hb⟩ := Finset.mem_biUnion.mp (MvPolynomial.vars_sum_subset _ _ hy)
    have h' := MvPolynomial.vars_mul _ _ hb
    rw [Finset.mem_union, vars_X, vars_C] at h'
    simp only [Finset.mem_singleton, Finset.notMem_empty, or_false] at h'
    rw [h']

theorem vars_act {L : Type*} [CommRing L] [Nontrivial L] {n N : ℕ} (isVec : ℕ → Bool)
    (g gi : Matrix (Fin n) (Fin n) L) {P : MvPolynomial (ℕ × Fin n) L} (hv : ∀ x ∈ P.vars, x.1 < N) :
    ∀ y ∈ (actAll isVec g gi P).vars, y.1 < N := by
  intro y hy
  have heq : actAll isVec g gi P = bind₁ (fun x => actAll isVec g gi (X x)) P := by
    simp only [actAll, bind₁, aeval_X]
  rw [heq] at hy
  obtain ⟨x, hx, hyx⟩ := Finset.mem_biUnion.mp (MvPolynomial.vars_bind₁ _ _ hy)
  rw [vars_actX isVec g gi x y hyx]
  exact hv x hx

end DominanceOrderLemmas

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
end
end

section -- merged from Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.FactSplit
noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

namespace LowHighPartSplit

variable {n : ℕ}

def lowP (i : ℕ) (e : ℕ × Fin n →₀ ℕ) : ℕ × Fin n →₀ ℕ := e.filter fun x => x.1 < i

def highP (i : ℕ) (e : ℕ × Fin n →₀ ℕ) : ℕ × Fin n →₀ ℕ := e.filter fun x => ¬ x.1 < i

theorem low_add_high (i : ℕ) (e : ℕ × Fin n →₀ ℕ) : lowP i e + highP i e = e := by
  ext x
  simp only [lowP, highP, Finsupp.add_apply, Finsupp.filter_apply]
  by_cases h : x.1 < i <;> simp [h]

theorem lowerUnipotent_symm_apply (i : ℕ) (e : ℕ × Fin n →₀ ℕ) (j : ℕ) (a : Fin n) :
    lowP i e (j, a) = if j < i then e (j, a) else 0 := by
  simp [lowP, Finsupp.filter_apply]

theorem highPart_apply (i : ℕ) (e : ℕ × Fin n →₀ ℕ) (j : ℕ) (a : Fin n) :
    highP i e (j, a) = if j < i then 0 else e (j, a) := by
  simp only [highP, Finsupp.filter_apply]
  by_cases h : j < i <;> simp [h]

private theorem weight_indicator_eq_degree (d : ℕ × Fin n →₀ ℕ) (j : ℕ) :
    Finsupp.weight (fun x : ℕ × Fin n => if x.1 = j then 1 else 0) d = ∑ a, d (j, a) := by
  rw [Finsupp.weight_apply, Finsupp.sum]
  simp only [smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  refine Finset.sum_bij_ne_zero (fun x _ _ => x.2) (fun _ _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro x hx _ y hy _ hxy
    rw [Finset.mem_filter] at hx hy
    exact Prod.ext (hx.2.trans hy.2.symm) hxy
  · intro a _ ha
    exact ⟨(j, a), Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr ha, rfl⟩, ha, rfl⟩
  · intro x hx _
    rw [Finset.mem_filter] at hx
    rw [← hx.2]

theorem mem_polB {R : Type*} [CommRing R] {N : ℕ} {B : ℕ → ℕ} {f : MvPolynomial (ℕ × Fin n) R} :
    f ∈ polB R n N B ↔ ∀ e ∈ f.support, ∀ j, ∑ a, e (j, a) = if j < N then B j else 0 := by
  simp only [polB, Submodule.mem_iInf, mem_weightedHomogeneousSubmodule, IsWeightedHomogeneous]
  constructor
  · intro h e he j
    have := h j (mem_support_iff.mp he)
    rw [weight_indicator_eq_degree] at this
    exact this
  · intro h j d hd
    rw [weight_indicator_eq_degree]
    exact h d (mem_support_iff.mpr hd) j

def Gc {k : Type*} [CommRing k] (i : ℕ) (G : MvPolynomial (ℕ × Fin n) k) (β : ℕ × Fin n →₀ ℕ) :
    MvPolynomial (ℕ × Fin n) k :=
  ∑ e ∈ G.support.filter (fun e => highP i e = β), monomial (lowP i e) (AddMonoidAlgebra.coeff G e)

theorem decomp {k : Type*} [CommRing k] (i : ℕ) (G : MvPolynomial (ℕ × Fin n) k) :
    G = ∑ β ∈ G.support.image (highP i), Gc i G β * monomial β 1 := by
  symm
  simp only [Gc, Finset.sum_mul, monomial_mul, mul_one]
  have h1 : ∀ β ∈ G.support.image (highP i),
      ∑ e ∈ G.support.filter (fun e => highP i e = β), monomial (lowP i e + β) (AddMonoidAlgebra.coeff G e) =
      ∑ e ∈ G.support.filter (fun e => highP i e = β), monomial e (AddMonoidAlgebra.coeff G e) :=
    fun β _ => Finset.sum_congr rfl fun e he => by rw [← (Finset.mem_filter.mp he).2, low_add_high]
  rw [Finset.sum_congr rfl h1, Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem _ hx)]
  exact G.as_sum.symm

theorem supp_zero {σ L : Type*} [CommRing L] {Lo : Set σ} {P : MvPolynomial σ L} (hP : P ∈ supported L Lo)
    {e : σ →₀ ℕ} (he : e ∈ P.support) {x : σ} (hx : x ∉ Lo) : e x = 0 := by
  by_contra h
  apply hx
  exact (mem_supported.mp hP) (Finset.mem_coe.mpr ((MvPolynomial.mem_vars_iff_mem_support x).mpr ⟨e, he, Finsupp.mem_support_iff.mpr h⟩))

theorem coeff_key {σ τ L : Type*} [CommRing L] (Lo : Set σ) (T : Finset τ) (A : τ → MvPolynomial σ L)
    (m : τ → σ →₀ ℕ) (hA : ∀ β ∈ T, A β ∈ supported L Lo) (hm : ∀ β ∈ T, ∀ x ∈ Lo, m β x = 0)
    (hinj : ∀ β ∈ T, ∀ γ ∈ T, m β = m γ → β = γ) {β : τ} (hβ : β ∈ T) {e : σ →₀ ℕ} (he : e ∈ (A β).support) :
    e + m β ∈ (∑ γ ∈ T, A γ * monomial (m γ) 1).support := by
  rw [mem_support_iff, coeff_sum, Finset.sum_eq_single β]
  · rw [coeff_mul_monomial, mul_one]
    exact mem_support_iff.mp he
  · intro γ hγ hne
    rw [coeff_mul_monomial']
    split_ifs with hle
    · rw [mul_one]
      by_contra hc
      have hf : e + m β - m γ ∈ (A γ).support := mem_support_iff.mpr hc
      apply hne
      apply hinj γ hγ β hβ
      ext x
      by_cases hx : x ∈ Lo
      · rw [hm β hβ x hx, hm γ hγ x hx]
      · have h1 := supp_zero (hA γ hγ) hf hx
        have h2 := supp_zero (hA β hβ) he hx
        have h3 := Finsupp.le_def.mp hle x
        rw [Finsupp.tsub_apply, Finsupp.add_apply, h2] at h1
        rw [Finsupp.add_apply, h2] at h3
        omega
    · rfl
  · intro h
    exact absurd hβ h

variable {k : Type*} [Field k] (isVec : ℕ → Bool) (S : Set ℕ) [DecidablePred (· ∈ S)]

def Psi : MvPolynomial (ℕ × Fin n) k →+* MvPolynomial (LVar ℕ Empty n) (GenField k n) :=
  ((sharpHom isVec S (genMat k n)⁻¹ (genMat k n)).toRingHom.comp (map (genφ k n))).comp
    (rename (R := k) (Sum.inl : ℕ × Fin n → LVar ℕ Empty n)).toRingHom

theorem Psi_apply (G : MvPolynomial (ℕ × Fin n) k) : Psi isVec S G = genH isVec S (rename Sum.inl G) := rfl

def loSet (n : ℕ) (S : Set ℕ) : Set (LVar ℕ Empty n) := {x | ∃ j a, j ∈ S ∧ x = Sum.inl (j, a)}

theorem Psi_X_low {j : ℕ} (hj : j ∈ S) (a : Fin n) :
    Psi isVec S (X (j, a) : MvPolynomial (ℕ × Fin n) k) ∈ supported (GenField k n) (loSet n S) := by
  have hgen : ∀ Mt : Matrix (Fin n) (Fin n) (GenField k n),
      Matrix.vecMul (fun b => (X (Sum.inl (j, b)) : MvPolynomial (LVar ℕ Empty n) (GenField k n)))
        (Mt.map C) a ∈ supported (GenField k n) (loSet n S) := by
    intro Mt
    simp only [Matrix.vecMul, dotProduct, Matrix.map_apply]
    exact Subalgebra.sum_mem _ fun b _ => Subalgebra.mul_mem _ (X_mem_supported.mpr ⟨j, b, hj, rfl⟩)
      (by rw [← algebraMap_eq]; exact Subalgebra.algebraMap_mem _ _)
  simp only [Psi_apply, genH, rename_X, map_X, sharpHom, aeval_X, if_pos hj]
  split_ifs
  · exact hgen _
  · rw [← Matrix.transpose_map]
    exact hgen _

theorem Psi_X_high {j : ℕ} (hj : j ∉ S) (a : Fin n) :
    Psi isVec S (X (j, a) : MvPolynomial (ℕ × Fin n) k) = X (Sum.inl (j, a)) := by
  simp only [Psi_apply, genH, rename_X, map_X, sharpHom, aeval_X, if_neg hj]

theorem Psi_C (c : k) : Psi (n := n) isVec S (C c) = C (genφ k n c) := by
  simp only [Psi_apply, genH, rename_C, map_C, sharpHom, aeval_C, algebraMap_eq]

theorem Psi_monomial (e : ℕ × Fin n →₀ ℕ) (c : k) :
    Psi isVec S (monomial e c) = C (genφ k n c) * ∏ x ∈ e.support, Psi isVec S (X x) ^ e x := by
  rw [monomial_eq, map_mul, Psi_C, Finsupp.prod, map_prod]
  simp only [map_pow]

theorem Psi_low {e : ℕ × Fin n →₀ ℕ} (he : ∀ j a, j ∉ S → e (j, a) = 0) (c : k) :
    Psi isVec S (monomial e c) ∈ supported (GenField k n) (loSet n S) := by
  rw [Psi_monomial]
  refine Subalgebra.mul_mem _ (by rw [← algebraMap_eq]; exact Subalgebra.algebraMap_mem _ _)
    (Subalgebra.prod_mem _ fun x hx => Subalgebra.pow_mem _ ?_ _)
  obtain ⟨j, a⟩ := x
  have hj : j ∈ S := by
    by_contra h
    exact (Finsupp.mem_support_iff.mp hx) (he j a h)
  exact Psi_X_low isVec S hj a

theorem Psi_high {e : ℕ × Fin n →₀ ℕ} (he : ∀ j a, j ∈ S → e (j, a) = 0) :
    Psi isVec S (monomial e (1 : k)) = monomial (e.mapDomain Sum.inl) 1 := by
  rw [Psi_monomial, map_one, map_one, one_mul, ← rename_monomial, monomial_eq, C_1, one_mul,
    Finsupp.prod, map_prod]
  apply Finset.prod_congr rfl
  intro x hx
  rw [map_pow, rename_X]
  obtain ⟨j, a⟩ := x
  have hj : j ∉ S := fun h => (Finsupp.mem_support_iff.mp hx) (he j a h)
  rw [Psi_X_high isVec S hj a]

theorem wExp_add (last : Bool) (e f : LVar ℕ Empty n →₀ ℕ) :
    wExp isVec S last (e + f) = wExp isVec S last e + wExp isVec S last f := by
  simp only [wExp]
  change (e + f).sum (fun x d => (d : ℤ) * wtX isVec S last x) =
    e.sum (fun x d => (d : ℤ) * wtX isVec S last x) + f.sum (fun x d => (d : ℤ) * wtX isVec S last x)
  rw [Finsupp.sum_add_index']
  · intro x
    simp
  · intro x a b
    push_cast
    ring

theorem wExp_high (last : Bool) {e : ℕ × Fin n →₀ ℕ} (he : ∀ j a, j ∈ S → e (j, a) = 0) :
    wExp isVec S last (e.mapDomain Sum.inl : LVar ℕ Empty n →₀ ℕ) = 0 := by
  simp only [wExp]
  change (e.mapDomain Sum.inl).sum (fun x d => (d : ℤ) * wtX isVec S last x) = 0
  rw [Finsupp.sum_mapDomain_index (by simp) (by intros; push_cast; ring)]
  apply Finset.sum_eq_zero
  intro x hx
  obtain ⟨j, a⟩ := x
  have hj : j ∉ S := fun h => (Finsupp.mem_support_iff.mp hx) (he j a h)
  simp [wtX, hj]

theorem Psi_Gc_low {i : ℕ} (hS : ∀ j, j ∈ S ↔ j < i) (G : MvPolynomial (ℕ × Fin n) k) (β : ℕ × Fin n →₀ ℕ) :
    Psi isVec S (Gc i G β) ∈ supported (GenField k n) (loSet n S) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Gc, map_sum]
  exact Subalgebra.sum_mem _ fun e _ =>
    Psi_low isVec S (fun j a hj => by rw [lowerUnipotent_symm_apply, if_neg ((hS j).not.mp hj)]) _

theorem high_zero {i : ℕ} (hS : ∀ j, j ∈ S ↔ j < i) {G : MvPolynomial (ℕ × Fin n) k} {β : ℕ × Fin n →₀ ℕ}
    (hβ : β ∈ G.support.image (highP i)) : ∀ j a, j ∈ S → β (j, a) = 0 := by
  intro j a hj
  obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hβ
  rw [highPart_apply, if_pos ((hS j).mp hj)]

theorem Psi_decomp {i : ℕ} (hS : ∀ j, j ∈ S ↔ j < i) (G : MvPolynomial (ℕ × Fin n) k) :
    Psi isVec S G = ∑ β ∈ G.support.image (highP i),
      Psi isVec S (Gc i G β) * monomial (β.mapDomain Sum.inl) 1 := by
  conv_lhs => rw [decomp i G]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  apply Finset.sum_congr rfl
  intro β hβ
  rw [map_mul, Psi_high isVec S (high_zero S hS hβ)]

theorem supp_sub {i : ℕ} (hS : ∀ j, j ∈ S ↔ j < i) (last : Bool) (G : MvPolynomial (ℕ × Fin n) k)
    {β : ℕ × Fin n →₀ ℕ} (hβ : β ∈ G.support.image (highP i)) :
    (genAct (ζ := Empty) k isVec S last (rename Sum.inl (Gc i G β))).coeff.support ⊆
      (genAct (ζ := Empty) k isVec S last (rename Sum.inl G)).coeff.support := by
  intro j hj
  rw [gen_mem_supp] at hj ⊢
  obtain ⟨e, he, rfl⟩ := hj
  refine ⟨e + β.mapDomain Sum.inl, ?_, ?_⟩
  · rw [← Psi_apply] at he ⊢
    rw [Psi_decomp isVec S hS G]
    refine coeff_key (loSet n S) (G.support.image (highP i)) (fun γ => Psi isVec S (Gc i G γ))
      (fun γ => γ.mapDomain Sum.inl) (fun γ _ => Psi_Gc_low isVec S hS G γ) ?_
      (fun γ _ δ _ h => Finsupp.mapDomain_injective Sum.inl_injective h) hβ he
    intro γ hγ x hx
    obtain ⟨j', a, hj', rfl⟩ := hx
    rw [Finsupp.mapDomain_apply_of_injective Sum.inl_injective]
    exact high_zero S hS hγ j' a hj'
  · rw [wExp_add, wExp_high isVec S last (high_zero S hS hβ), add_zero]

end LowHighPartSplit

open LowHighPartSplit in
theorem factSplit_valid : FactSplit := by
  intro k _ n N i isVec B θ M G hiN hG
  refine ⟨G.support.image (highP i), Gc i G, ?_, ?_, decomp i G, ?_⟩
  · intro β hβ j
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hβ
    have h := (mem_polB.mp hG) e he j
    simp only [highPart_apply]
    by_cases hji : j < i
    · simp only [if_pos hji, Finset.sum_const_zero]
      rw [if_neg (by omega)]
    · simp only [if_neg hji]
      rw [h]
      by_cases hjN : j < N
      · rw [if_pos hjN, if_pos ⟨by omega, hjN⟩]
      · rw [if_neg hjN, if_neg (by omega)]
  · intro β hβ
    rw [mem_polB]
    intro e he j
    have he2 : e ∈ (∑ e ∈ G.support.filter (fun e => highP i e = β),
        monomial (lowP i e) (AddMonoidAlgebra.coeff G e)).support := he
    have hsub := Finset.mem_of_subset support_sum he2
    simp only [Finset.mem_biUnion, Finset.mem_filter] at hsub
    obtain ⟨e', ⟨he', -⟩, hmem⟩ := hsub
    rw [Finset.mem_singleton.mp (support_monomial_subset hmem)]
    simp only [lowerUnipotent_symm_apply]
    have h := (mem_polB.mp hG) e' he' j
    by_cases hji : j < i
    · simp only [if_pos hji]
      rw [h, if_pos (by omega : j < N)]
    · simp only [if_neg hji, Finset.sum_const_zero]
  · intro hgood β hβ
    obtain ⟨h1, h2⟩ := hgood
    have hS : ∀ j, j ∈ {j : ℕ | j < i} ↔ j < i := fun j => Iff.rfl
    exact ⟨fun t ht => le_trans (h1 t ht) (Finset.min_mono (supp_sub isVec {j : ℕ | j < i} hS true G hβ)),
      fun t ht => le_trans (Finset.max_mono (supp_sub isVec {j : ℕ | j < i} hS false G hβ)) (h2 t ht)⟩

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
end
end

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.Top

open Formalism.InvariantFactorPaths.GelfandTsetlinBases

theorem psiWeight : PsiWeight := psi_weight
theorem fact_index_weights : IndexWeightsDominance := index_weights_dominance
theorem polBRank : PolBRank := polynomial_b_rank
theorem pathIdxFinite : PathIdxFinite := path_index_finite
theorem factBrk : FactBrk := fact_break
theorem factEV : FactEV := factEV_of fact_index_weights psiWeight
theorem lemmaA2indep : LemmaA2indep := lemmaA2indep_of factEV factBrk
theorem path_basis_theorem : PathBasisOfCount := path_basis_of_count lemmaA2indep pathIdxFinite polBRank

theorem psiPath_basis (n N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (R : Type) [CommRing R] :
    LinearIndependent R (fun x : PathIdx n N isVec B => psiPath R isVec x.1.1 N x.1.2) ∧
      Submodule.span R (Set.range fun x : PathIdx n N isVec B => psiPath R isVec x.1.1 N x.1.2) =
        polB R n N B := path_basis_theorem n N isVec B (countPAll n N isVec B) R
theorem factSplit : FactSplit := factSplit_valid

end Formalism.InvariantFactorPaths.GelfandTsetlinBases.Top
end

section -- merged from Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.UnitAndFieldPowerLemmas
section -- merged from Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.ValuationProductsComponents
noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

namespace A0

end A0

namespace A0

theorem trunc (R : Type*) [CommRing R] (n i : ℕ) (isVec : ℕ → Bool) (μ : ℕ → Fin n → ℤ) (c : ℤ) (N : ℕ)
    (hN : i ≤ N) : ∀ I : Finset (Fin n),
    ∃ Q : Finset (Fin n) → MvPolynomial (ℕ × Fin n) R,
      (∀ I', Q I' ∈ supported R {x : ℕ × Fin n | i ≤ x.1}) ∧
      pathWord isVec μ c (fun j a => (X (j, a) : MvPolynomial (ℕ × Fin n) R)) N I =
        ∑ I' : Finset (Fin n),
          pathWord isVec μ c (fun j a => (X (j, a) : MvPolynomial (ℕ × Fin n) R)) i I' * Q I' := by
  induction N, hN using Nat.le_induction with
  | base =>
    intro I
    refine ⟨fun I' => if I' = I then 1 else 0, fun I' => ?_, ?_⟩
    · dsimp only
      split
      · exact one_mem _
      · exact zero_mem _
    · simp
  | succ N hN ih =>
    intro I
    by_cases hch : colHeight (μ (N + 1)) c = colHeight (μ N) c
    · rw [pathWord, if_pos hch]
      exact ih I
    · rw [pathWord, if_neg hch]
      choose Q hQ1 hQ2 using ih
      have hX : ∀ m : Fin n, (X (N, m) : MvPolynomial (ℕ × Fin n) R) ∈
          supported R {x : ℕ × Fin n | i ≤ x.1} := fun m => by
        rw [supported_eq_adjoin_X]
        exact Algebra.subset_adjoin ⟨(N, m), hN, rfl⟩
      unfold stepF
      split
      · refine ⟨fun I' => ∑ m ∈ I, ((sg I m : ℤ) : MvPolynomial (ℕ × Fin n) R) * Q (I.erase m) I' * X (N, m),
          fun I' => ?_, ?_⟩
        · exact sum_mem fun m _ => mul_mem (mul_mem (intCast_mem _ _) (hQ1 _ _)) (hX m)
        · unfold wedgeF
          simp only [hQ2, Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun I' _ => Finset.sum_congr rfl fun m _ => ?_
          ring
      · refine ⟨fun I' => ∑ m ∈ Iᶜ, ((sg I m : ℤ) : MvPolynomial (ℕ × Fin n) R) * X (N, m) * Q (insert m I) I',
          fun I' => ?_, ?_⟩
        · exact sum_mem fun m _ => mul_mem (mul_mem (intCast_mem _ _) (hX m)) (hQ1 _ _)
        · unfold contrF
          simp only [hQ2, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun I' _ => Finset.sum_congr rfl fun m _ => ?_
          ring

end A0

namespace A0

end A0

namespace A0

section Weights

variable {ι ζ : Type*} {n : ℕ} {L : Type*} [CommRing L] (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]

variable {isVec S} {last : Bool} {s : ℤ}

end Weights

theorem pathWord_card {R : Type*} [CommRing R] {n N : ℕ} {isVec : ℕ → Bool} {B : ℕ → ℕ} {μ : ℕ → Fin n → ℤ}
    (hp : IsPath n isVec B μ N) (c : ℤ) (Xr : ℕ → Fin n → R) :
    ∀ j ≤ N, ∀ J : Finset (Fin n), pathWord isVec μ c Xr j J ≠ 0 →
      J.card = if 1 ≤ c then colHeight (μ j) c else n - colHeight (μ j) c := by
  intro j
  induction j with
  | zero =>
    intro _ J hJ
    have h0 : J = ∅ := by
      by_contra hne
      exact hJ (if_neg hne)
    rw [h0, hp.1, Paths.colHeight_zero]
    split_ifs <;> simp
  | succ j ih =>
    intro hj J hJ
    have ih' := ih (by omega)
    by_cases hch : colHeight (μ (j + 1)) c = colHeight (μ j) c
    · rw [pathWord, if_pos hch] at hJ
      rw [hch]
      exact ih' J hJ
    · rw [pathWord, if_neg hch] at hJ
      have hh := Paths.path_height hp (show j < N by omega) c
      have hle := Paths.colHeight_le (μ j) c
      have hle' := Paths.colHeight_le (μ (j + 1)) c
      unfold stepF at hJ
      cases hup : (isVec j == decide (1 ≤ c))
      · rw [hup] at hJ
        simp only [Bool.false_eq_true, if_false] at hJ
        unfold contrF at hJ
        obtain ⟨m, hm, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hJ
        have e := ih' _ (right_ne_zero_of_mul hne)
        rw [Finset.card_insert_of_notMem (Finset.mem_compl.1 hm)] at e
        by_cases h1 : 1 ≤ c
        · have hv : isVec j = false := by simpa [h1] using hup
          rw [hv] at hh
          simp only [Bool.false_eq_true, if_false] at hh
          rw [if_pos h1] at e ⊢
          omega
        · have hv : isVec j = true := by simpa [h1] using hup
          rw [hv] at hh
          simp only [if_true] at hh
          rw [if_neg h1] at e ⊢
          omega
      · rw [hup] at hJ
        simp only [if_true] at hJ
        unfold wedgeF at hJ
        obtain ⟨m, hm, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hJ
        have e := ih' _ (right_ne_zero_of_mul (left_ne_zero_of_mul hne))
        have hpos : 0 < J.card := Finset.card_pos.2 ⟨m, hm⟩
        rw [Finset.card_erase_of_mem hm] at e
        by_cases h1 : 1 ≤ c
        · have hv : isVec j = true := by simpa [h1] using hup
          rw [hv] at hh
          simp only [if_true] at hh
          rw [if_pos h1] at e ⊢
          omega
        · have hv : isVec j = false := by simpa [h1] using hup
          rw [hv] at hh
          simp only [Bool.false_eq_true, if_false] at hh
          rw [if_neg h1] at e ⊢
          omega

section Gen

variable (k : Type) [Field k] {n : ℕ} (isVec : ℕ → Bool) (S : Set ℕ) [DecidablePred (· ∈ S)]

variable {k isVec S}

end Gen

end A0

namespace A0

section Jacobi

variable {R : Type} [CommRing R] {n : ℕ}

end Jacobi

end A0

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
end
end

noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

namespace ExponentSetCounting

variable {n : ℕ}

def ContP (i N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (μ₀ : Fin n → ℤ)
    (x : (ℕ → Fin n → ℤ) × (ℤ → Finset (Fin n))) : Prop :=
  x.1 i = μ₀ ∧ (∀ j, j < i ∨ N < j → x.1 j = 0) ∧
    (∀ j, i ≤ j → j < N →
      if isVec j then HStrip (x.1 (j + 1)) (x.1 j) (B j) else HStrip (x.1 j) (x.1 (j + 1)) (B j)) ∧
    IsStd (x.1 N) x.2

def expSet (n i N : ℕ) (B : ℕ → ℕ) : Set (ℕ × Fin n →₀ ℕ) :=
  {β | ∀ j, ∑ a, β (j, a) = if i ≤ j ∧ j < N then B j else 0}

theorem shift_inj (n i : ℕ) : Function.Injective (fun x : ℕ × Fin n => (i + x.1, x.2)) := by
  intro a b h
  simp only [Prod.mk.injEq] at h
  exact Prod.ext (by omega) h.2

theorem expSet_subset (n i N : ℕ) (B : ℕ → ℕ) :
    expSet n i N B ⊆ Finsupp.mapDomain (fun x : ℕ × Fin n => (i + x.1, x.2)) ''
      {e : ℕ × Fin n →₀ ℕ | ∀ j, ∑ a, e (j, a) = if j < N - i then B (i + j) else 0} := by
  intro β hβ
  have hβ' : ∀ j, ∑ a, β (j, a) = if i ≤ j ∧ j < N then B j else 0 := hβ
  have hsupp : ↑β.support ⊆ Set.range (fun x : ℕ × Fin n => (i + x.1, x.2)) := by
    intro p hp
    obtain ⟨j, a⟩ := p
    have hpa : β (j, a) ≠ 0 := Finsupp.mem_support_iff.mp hp
    have hij : i ≤ j := by
      by_contra hlt
      have h0 := hβ' j
      rw [if_neg (fun h => hlt h.1)] at h0
      exact hpa ((Finset.sum_eq_zero_iff.mp h0) a (Finset.mem_univ a))
    exact ⟨(j - i, a), Prod.ext (show i + (j - i) = j by omega) rfl⟩
  refine ⟨Finsupp.comapDomain _ β (fun _ _ _ _ h => shift_inj n i h), ?_, ?_⟩
  · simp only [Set.mem_setOf_eq]
    intro j
    show ∑ a, β (i + j, a) = _
    rw [hβ' (i + j)]
    by_cases h : j < N - i
    · rw [if_pos ⟨by omega, by omega⟩, if_pos h]
    · rw [if_neg (by omega), if_neg h]
  · apply Finsupp.mapDomain_comapDomain
    · exact shift_inj n i
    · exact hsupp

theorem expSet_finite (hR : PolBRank) (n i N : ℕ) (B : ℕ → ℕ) : (expSet n i N B).Finite :=
  ((hR n (N - i) (fun j => B (i + j))).2.1.image _).subset (expSet_subset n i N B)

theorem expSet_card (hR : PolBRank) (n i N : ℕ) (B : ℕ → ℕ) :
    (expSet n i N B).ncard ≤ ∏ l ∈ Finset.Ico i N, (n + B l - 1).choose (B l) := by
  have hfin : {e : ℕ × Fin n →₀ ℕ | ∀ j, ∑ a, e (j, a) = if j < N - i then B (i + j) else 0}.Finite :=
    (hR n (N - i) (fun j => B (i + j))).2.1
  have hcard : {e : ℕ × Fin n →₀ ℕ | ∀ j, ∑ a, e (j, a) = if j < N - i then B (i + j) else 0}.ncard =
      ∏ j ∈ Finset.range (N - i), (n + B (i + j) - 1).choose (B (i + j)) :=
    (hR n (N - i) (fun j => B (i + j))).1
  calc (expSet n i N B).ncard
      ≤ ((Finsupp.mapDomain (fun x : ℕ × Fin n => (i + x.1, x.2))) ''
          {e : ℕ × Fin n →₀ ℕ | ∀ j, ∑ a, e (j, a) = if j < N - i then B (i + j) else 0}).ncard :=
        Set.ncard_le_ncard (expSet_subset n i N B) (hfin.image _)
    _ ≤ {e : ℕ × Fin n →₀ ℕ | ∀ j, ∑ a, e (j, a) = if j < N - i then B (i + j) else 0}.ncard :=
        Set.ncard_image_le hfin
    _ = ∏ j ∈ Finset.range (N - i), (n + B (i + j) - 1).choose (B (i + j)) := hcard
    _ = ∏ l ∈ Finset.Ico i N, (n + B l - 1).choose (B l) :=
        (Finset.prod_Ico_eq_prod_range (fun l => (n + B l - 1).choose (B l)) i N).symm

theorem psiFam_mem (k : Type) [Field k] (N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (x : PathIdx n N isVec B) :
    psiFam k n N isVec B x ∈ polB k n N B := by
  rw [polB, Submodule.mem_iInf]
  intro j
  exact (pathProductDegrees k n N isVec B x.1.1 x.1.2 x.2.1 x.2.2.2.1).2 j

end ExponentSetCounting

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
end
end

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.ColumnFamilies

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def isV {N : ℕ} (LL : Letters (Fin N)) : ℕ → Bool := fun i => if h : i < N then LL.vec ⟨i, h⟩ else true

def Bn {N : ℕ} (B : Fin N → ℕ) : ℕ → ℕ := fun i => if h : i < N then B ⟨i, h⟩ else 0

def ext {N n : ℕ} (mu : Fin (N + 1) → Fin n → ℤ) : ℕ → Fin n → ℤ := fun i => if h : i < N + 1 then mu ⟨i, h⟩ else 0

def res (N : ℕ) {n : ℕ} (μ : ℕ → Fin n → ℤ) : Fin (N + 1) → Fin n → ℤ := fun i => μ i.val

def iv (N n : ℕ) : Fin N × Fin n → ℕ × Fin n := fun x => (x.1.val, x.2)

def RestPathTo : Prop :=
  ∀ (n N : ℕ) (LL : Letters (Fin N)) (B : Fin N → ℕ) (P : PPath n N LL B),
    Formalism.InvariantFactorPaths.GelfandTsetlinBases.IsPath n (isV LL) (Bn B) (ext P.mu) N

def RestPathFrom : Prop :=
  ∀ (n N : ℕ) (LL : Letters (Fin N)) (B : Fin N → ℕ) (μ : ℕ → Fin n → ℤ),
    Formalism.InvariantFactorPaths.GelfandTsetlinBases.IsPath n (isV LL) (Bn B) μ N → ∃ P : PPath n N LL B, P.mu = res N μ

def RestStd : Prop :=
  ∀ (n N : ℕ) (mu : Fin (N + 1) → Fin n → ℤ) (I : ℤ → Finset (Fin n)),
    IsSt mu I ↔ Formalism.InvariantFactorPaths.GelfandTsetlinBases.IsStd (pEnd mu) I

def RestPsi : Prop :=
  ∀ (R : Type) [CommRing R] (n N : ℕ) (LL : Letters (Fin N)) (B : Fin N → ℕ) (P : PPath n N LL B)
    (I : ℤ → Finset (Fin n)), Formalism.InvariantFactorPaths.GelfandTsetlinBases.IsIndex (pEnd P.mu) I →
    rename (iv N n) (Psi R P.mu I) = Formalism.InvariantFactorPaths.GelfandTsetlinBases.psiPath R (isV LL) (ext P.mu) N I

def RestPol : Prop :=
  ∀ (R : Type) [CommRing R] (n N : ℕ) (B : Fin N → ℕ),
    (Pol R n B).map (rename (iv N n) : MvPolynomial (Fin N × Fin n) R →ₐ[R] MvPolynomial (ℕ × Fin n) R).toLinearMap =
      Formalism.InvariantFactorPaths.GelfandTsetlinBases.polB R n N (Bn B)

end Formalism.MainNotions.G.ColumnFamilies
