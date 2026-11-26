module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.MemZpowersIff

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.MemSpanOrderTwoRelationIffCoordsEqZero
open Finset UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5

private theorem single_mul_rel {A : Type} [CommRing A] {Γ : Type} [CommGroup Γ] (c : Γ) (ε : ℤ) (g : Γ) (b : A) :
    MonoidAlgebra.single g b * rel A c ε =
      MonoidAlgebra.single g (-((ε : A) * b)) + MonoidAlgebra.single (c * g) b := by
  rw [rel, MonoidAlgebra.intCast_def, mul_sub, MonoidAlgebra.single_mul_single,
    MonoidAlgebra.single_mul_single, mul_one, mul_one, mul_comm g c, mul_comm b,
    MonoidAlgebra.single_neg, sub_eq_add_neg, add_comm]

private theorem coeff_mul_rel {A : Type} [CommRing A] {Γ : Type} [CommGroup Γ] {c : Γ} (h2 : c * c = 1) (ε : ℤ)
    (u : MonoidAlgebra A Γ) (g : Γ) :
    (u * rel A c ε).coeff g = u.coeff (c * g) - (ε : A) * u.coeff g := by
  classical
  induction u using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [add_mul]
    simp only [MonoidAlgebra.coeff_add, Finsupp.add_apply, hx, hy]
    ring
  | single a b =>
    rw [single_mul_rel]
    have h : (c * a = g) ↔ (a = c * g) := by
      constructor
      · rintro rfl; rw [← mul_assoc, h2, one_mul]
      · rintro rfl; rw [← mul_assoc, h2, one_mul]
    simp only [MonoidAlgebra.coeff_add, Finsupp.add_apply, MonoidAlgebra.coeff_single, Finsupp.single_apply, h]
    split_ifs <;> ring

theorem UpperTheory.V.B5.mem_span_orderTwoRelation_iff_coords_eq_zero :
    ∀ {A : Type} [CommRing A] {Γ : Type} [CommGroup Γ] [Finite Γ] (c : Γ) (ε : ℤ), c * c = 1 → c ≠ 1 → ε * ε = 1 → ∀ w : MonoidAlgebra A Γ, w ∈ Ideal.span {rel A c ε} ↔ coord c ε w = 0 := by
  intro A _ Γ _ _ c ε h2 hc hε w
  classical
  letI := Fintype.ofFinite Γ
  have hε' : (ε : A) * ε = 1 := by
    have := congrArg (fun n : ℤ => (n : A)) hε
    simpa using this
  rw [Ideal.mem_span_singleton']
  constructor
  · rintro ⟨u, rfl⟩
    funext i
    simp only [coord, coeff_mul_rel h2, Pi.zero_apply]
    rw [← mul_assoc c c, h2, one_mul]
    linear_combination (-(u.coeff (c * rep i))) * hε'
  · intro hw
    refine ⟨∑ i : Qc c, MonoidAlgebra.single (rep i) (w.coeff (c * rep i)), ?_⟩
    rw [Finset.sum_mul]
    simp only [single_mul_rel]
    apply MonoidAlgebra.ext
    conv_rhs => rw [← Finsupp.univ_sum_single w.coeff]
    rw [sum_rep h2 hc (fun g => Finsupp.single g (w.coeff g)), MonoidAlgebra.coeff_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hi := congrFun hw i
    simp only [coord, Pi.zero_apply] at hi
    rw [MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_single, MonoidAlgebra.coeff_single,
      show -((ε : A) * w.coeff (c * rep i)) = w.coeff (rep i) by linear_combination -hi]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.ExistsLinearEquivQuotientByOrderTwoCoords
open Finset UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5

theorem UpperTheory.V.B5.exists_linearEquiv_quotientByOrderTwo_coords :
    ∀ {A : Type} [CommRing A] {Γ : Type} [CommGroup Γ] [Finite Γ] (c : Γ) (ε : ℤ), c * c = 1 → c ≠ 1 → ε * ε = 1 → ∃ e : Rq A c ε ≃ₗ[A] (Qc c → A), ∀ w : MonoidAlgebra A Γ, e (cls A c ε w) = coord c ε w := by
  intro A _ Γ _ _ c ε hc hc1 hε
  classical
  haveI : Fintype (Qc c) := Fintype.ofFinite (Qc c)
  let f : MonoidAlgebra A Γ →ₗ[A] (Qc c → A) :=
    { toFun := coord c ε
      map_add' := by
        intro x y
        funext i
        simp only [coord, MonoidAlgebra.coeff_add, Finsupp.add_apply, Pi.add_apply]
        ring
      map_smul' := by
        intro a x
        funext i
        simp only [coord, MonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul,
          RingHom.id_apply, Pi.smul_apply]
        ring }
  have hf : ∀ w, f w = coord c ε w := fun w => rfl
  have hker : LinearMap.ker f = (Ideal.span {rel A c ε}).restrictScalars A := by
    ext w
    rw [LinearMap.mem_ker, Submodule.restrictScalars_mem, mem_span_orderTwoRelation_iff_coords_eq_zero c ε hc hc1 hε, hf]
  have hrepinj : ∀ i i' : Qc c, rep i = rep i' → i = i' := by
    intro i i' h
    rw [← mk_rep i, ← mk_rep i', h]
  have hcrep : ∀ i i' : Qc c, rep i' ≠ c * rep i := by
    intro i i' h
    have e1 : i' = i := by
      rw [← mk_rep i', ← mk_rep i, h]
      exact ((mk_eq_mk hc (rep i) (c * rep i)).mpr (Or.inr rfl)).symm
    subst e1
    have e2 : c * rep i' = 1 * rep i' := by rw [← h, one_mul]
    exact hc1 (mul_right_cancel e2)
  have hsurj : Function.Surjective f := by
    intro v
    refine ⟨∑ i, MonoidAlgebra.single (rep i) (v i), ?_⟩
    funext i0
    rw [hf, coord]
    simp only [MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single, Finsupp.finsetSum_apply,
      Finsupp.single_apply]
    rw [Finset.sum_eq_single i0, Finset.sum_eq_zero]
    · simp
    · intro i _
      rw [if_neg (hcrep i0 i)]
    · intro i _ hi
      rw [if_neg (fun h => hi (hrepinj i i0 h))]
    · intro h
      exact absurd (Finset.mem_univ i0) h
  let e : Rq A c ε ≃ₗ[A] (Qc c → A) :=
    (Submodule.Quotient.restrictScalarsEquiv A (Ideal.span {rel A c ε})).symm ≪≫ₗ
      Submodule.quotEquivOfEq _ _ hker.symm ≪≫ₗ f.quotKerEquivOfSurjective hsurj
  exact ⟨e, fun w => rfl⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.Mulvec
open Finset UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5

private theorem coeff_mul_sum {A : Type} [CommRing A] {Γ : Type} [CommGroup Γ] [Fintype Γ]
    (z w : MonoidAlgebra A Γ) (g : Γ) : (z * w).coeff g = ∑ h, z.coeff (g * h⁻¹) * w.coeff h := by
  rw [MonoidAlgebra.mul_apply_right, Finsupp.sum_fintype]
  intro h
  simp

theorem UpperTheory.V.B5.coords_mul_eq_quotientMatrix_mulVec :
    ∀ {A : Type} [CommRing A] {Γ : Type} [CommGroup Γ] [Finite Γ] (c : Γ) (ε : ℤ), c * c = 1 → c ≠ 1 → ε * ε = 1 → ∀ z w : MonoidAlgebra A Γ, coord c ε (z * w) = (mat c ε z).mulVec (coord c ε w) := by
  intro A _ Γ _ _ c ε hc hc1 hε z w
  haveI := Fintype.ofFinite Γ
  have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc
  have hεA : (ε : A) * ε = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → A) hε
  funext i
  simp only [coord, Matrix.mulVec, dotProduct, mat, Matrix.of_apply, coeff_mul_sum]
  rw [sum_rep hc hc1, sum_rep hc hc1, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e1 : rep i * (c * rep j)⁻¹ = c * (rep i * (rep j)⁻¹) := by
    rw [mul_inv, hci, mul_left_comm]
  have e2 : c * rep i * (c * rep j)⁻¹ = rep i * (rep j)⁻¹ := by
    rw [mul_inv, hci, mul_mul_mul_comm, hc, one_mul]
  have e3 : c * rep i * (rep j)⁻¹ = c * (rep i * (rep j)⁻¹) := mul_assoc _ _ _
  rw [e2, e1, e3]
  linear_combination (-(z.coeff (c * (rep i * (rep j)⁻¹)) * w.coeff (c * rep j))) * hεA
end

open Finset UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5

theorem UpperTheory.V.B5.algebraMap_signedInvolutionQuotientDet_mem_span :
    ∀ {A : Type} [CommRing A] {Γ : Type} [CommGroup Γ] [Finite Γ] (c : Γ) (ε : ℤ), c * c = 1 → c ≠ 1 → ε * ε = 1 → ∀ z : MonoidAlgebra A Γ, algebraMap A (MonoidAlgebra A Γ) (detR c ε z) ∈ Ideal.span {rel A c ε, z} := by
  intro A _ Γ _ _ c ε h1 h2 h3 z
  obtain ⟨e, he⟩ := UpperTheory.V.B5.exists_linearEquiv_quotientByOrderTwo_coords (A := A) c ε h1 h2 h3
  have hsc : ∀ (d : A) (w : MonoidAlgebra A Γ),
      coord c ε (algebraMap A (MonoidAlgebra A Γ) d * w) = d • coord c ε w := by
    intro d w
    funext i
    simp [coord, Algebra.algebraMap_eq_smul_one]
    ring
  obtain ⟨y, hy⟩ := e.surjective ((mat c ε z).adjugate.mulVec (coord c ε 1))
  obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hu : coord c ε u = (mat c ε z).adjugate.mulVec (coord c ε 1) := by
    rw [← he]
    exact hy
  have hcoord : coord c ε (z * u) = coord c ε (algebraMap A _ (detR c ε z) * 1) := by
    rw [UpperTheory.V.B5.coords_mul_eq_quotientMatrix_mulVec c ε h1 h2 h3, hu, Matrix.mulVec_mulVec, Matrix.mul_adjugate, hsc,
      Matrix.smul_mulVec, Matrix.one_mulVec]
    rfl
  rw [mul_one] at hcoord
  have hcls : cls A c ε (algebraMap A _ (detR c ε z)) = cls A c ε (z * u) := by
    apply e.injective
    rw [he, he, hcoord]
  have hmem : algebraMap A _ (detR c ε z) - z * u ∈ Ideal.span {rel A c ε} :=
    Ideal.Quotient.eq.mp hcls
  have hsub : Ideal.span {rel A c ε} ≤ Ideal.span {rel A c ε, z} :=
    Ideal.span_mono (by simp)
  have hz : z * u ∈ Ideal.span {rel A c ε, z} :=
    Ideal.mul_mem_right u _ (Ideal.subset_span (by simp))
  have := Ideal.add_mem _ (hsub hmem) hz
  simpa using this
