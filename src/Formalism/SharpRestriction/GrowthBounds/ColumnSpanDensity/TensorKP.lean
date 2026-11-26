module

public import Mathlib

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.TensorKP
open MvPolynomial

namespace Formalism.MainNotions.flipOneThree.Pf.KP

private theorem tm_comap {S α : Type} [Fintype S] [DecidableEq S] (n : S → α →₀ ℕ) (s : S) :
    (∑ t, Finsupp.mapDomain (fun v => (t, v)) (n t)).comapDomain (fun v => (s, v))
      (Prod.mk_right_injective s).injOn = n s := by
  ext a
  rw [Finsupp.comapDomain_apply, Finsupp.finsetSum_apply, Finset.sum_eq_single s]
  · exact Finsupp.mapDomain_apply_of_injective (Prod.mk_right_injective s) (n s) a
  · intro t _ hts
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨v, hv⟩
    exact hts (congrArg Prod.fst hv)
  · intro h
    exact absurd (Finset.mem_univ s) h

theorem tensorMap {K : Type} [Field K] {S α B : Type} [Fintype S] [DecidableEq S] [CommRing B]
    [Algebra K B] (g : S → MvPolynomial α K →ₗ[K] B) :
    ∃ F : MvPolynomial (S × α) K →ₗ[K] B, ∀ P : S → MvPolynomial α K,
      F (∏ s, rename (fun v => (s, v)) (P s)) = ∏ s, g s (P s) := by
  classical
  let F : MvPolynomial (S × α) K →ₗ[K] B :=
    (MvPolynomial.basisMonomials (S × α) K).constr K
      (fun m => ∏ s, g s (monomial (m.comapDomain (fun v => (s, v))
        (Prod.mk_right_injective s).injOn) 1))
  refine ⟨F, ?_⟩
  have key : F.compMultilinearMap
      ((MultilinearMap.mkPiAlgebra K S (MvPolynomial (S × α) K)).compLinearMap
        (fun s => (rename (R := K) (fun v : α => (s, v))).toLinearMap)) =
      (MultilinearMap.mkPiAlgebra K S B).compLinearMap g := by
    apply Module.Basis.ext_multilinear (fun _ => MvPolynomial.basisMonomials α K)
    intro n
    simp only [LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply,
      MultilinearMap.mkPiAlgebra_apply, AlgHom.toLinearMap_apply, coe_basisMonomials,
      rename_monomial]
    rw [← monomial_sum_one]
    have h := (MvPolynomial.basisMonomials (S × α) K).constr_basis K
      (fun m => ∏ s, g s (monomial (m.comapDomain (fun v => (s, v))
        (Prod.mk_right_injective s).injOn) 1))
      (∑ t, Finsupp.mapDomain (fun v => (t, v)) (n t))
    rw [coe_basisMonomials] at h
    refine h.trans ?_
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [tm_comap]
  intro P
  have := congrArg (fun f => f P) key
  simpa using this

end Formalism.MainNotions.flipOneThree.Pf.KP

open MvPolynomial

namespace Formalism.MainNotions.flipOneThree.Pf.KP

end Formalism.MainNotions.flipOneThree.Pf.KP

open MvPolynomial

namespace Formalism.MainNotions.flipOneThree.Pf.KP

end Formalism.MainNotions.flipOneThree.Pf.KP

open MvPolynomial

namespace Formalism.MainNotions.flipOneThree.Pf.KP

private theorem rg_prod_mem {R A : Type} [CommSemiring R] [CommSemiring A] [Algebra R A]
    {T : Type} [DecidableEq T] (U : Finset T) (M : T → Submodule R A) (z : T → A)
    (hz : ∀ s, z s ∈ M s) : ∏ s ∈ U, z s ∈ ∏ s ∈ U, M s := by
  induction U using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact Submodule.one_le.mp (le_refl (1 : Submodule R A))
  | insert a U ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact Submodule.mul_mem_mul (hz a) ih

theorem regroup {R K : Type} [CommRing R] [CommRing K] [Algebra R K] {T α : Type} [Fintype T]
    [DecidableEq T] (N : T × Bool → Submodule R (MvPolynomial α K))
    (y : T → MvPolynomial (Bool × α) K)
    (hy : ∀ s, y s ∈ Submodule.span R {P | ∃ F : Bool → MvPolynomial α K,
      (∀ b, F b ∈ N (s, b)) ∧ P = ∏ b, rename (fun v => (b, v)) (F b)}) :
    ∏ s, rename (fun v : Bool × α => ((s, v.1), v.2)) (y s) ∈
      Submodule.span R {P | ∃ F : T × Bool → MvPolynomial α K,
        (∀ x, F x ∈ N x) ∧ P = ∏ x, rename (fun v => (x, v)) (F x)} := by
  classical
  set G : T → Set (MvPolynomial (Bool × α) K) := fun s => {P | ∃ F : Bool → MvPolynomial α K,
      (∀ b, F b ∈ N (s, b)) ∧ P = ∏ b, rename (fun v => (b, v)) (F b)} with hG
  let ρ : ∀ s : T, MvPolynomial (Bool × α) K →ₗ[R] MvPolynomial ((T × Bool) × α) K := fun s =>
    ((rename (fun v : Bool × α => ((s, v.1), v.2)) :
      MvPolynomial (Bool × α) K →ₐ[K] MvPolynomial ((T × Bool) × α) K).restrictScalars R).toLinearMap
  have h1 : ∀ s, rename (fun v : Bool × α => ((s, v.1), v.2)) (y s) ∈
      Submodule.span R (ρ s '' G s) := by
    intro s
    rw [← Submodule.map_span]
    exact Submodule.mem_map_of_mem (f := ρ s) (hy s)
  have h2 := rg_prod_mem Finset.univ (fun s => Submodule.span R (ρ s '' G s)) _ h1
  rw [Submodule.prod_span] at h2
  refine Submodule.span_mono ?_ h2
  intro P hP
  rw [Set.mem_fintype_prod] at hP
  obtain ⟨g, hg, rfl⟩ := hP
  choose a ha hag using hg
  choose F hF hFa using ha
  refine ⟨fun x => F x.1 x.2, fun x => hF x.1 x.2, ?_⟩
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [← hag s, hFa s]
  show rename (fun v : Bool × α => ((s, v.1), v.2)) _ = _
  rw [map_prod]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [rename_rename]
  rfl

end Formalism.MainNotions.flipOneThree.Pf.KP
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.LatRetract
namespace Formalism.MainNotions.flipOneThree.Pf.KP

open Submodule

section LatRetract

variable {O K V V' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V]
  [IsScalarTower O K V] [AddCommGroup V'] [Module K V'] [Module O V'] [IsScalarTower O K V']
  {ι ι' : Type} [Fintype ι] [Fintype ι']

omit [IsDiscreteValuationRing O] in
private theorem lrt_am_ne {a : O} (ha : a ≠ 0) : algebraMap O K a ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 ha

private theorem lrt_tf (O K V : Type) [CommRing O] [IsDomain O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] :
    Module.IsTorsionFree O V :=
  ⟨fun r hr x y hxy => by
    have hr0 : r ≠ 0 := hr.ne_zero
    have h1 : algebraMap O K r • x = algebraMap O K r • y := by
      rw [algebraMap_smul, algebraMap_smul]; exact hxy
    exact smul_right_injective V (lrt_am_ne (K := K) hr0) h1⟩


omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] [Fintype ι] in
private theorem lrt_coord (b : Module.Basis ι K V) {y : V}
    (hy : y ∈ span O (Set.range b)) (i : ι) : b.repr y i ∈ Set.range (algebraMap O K) := by
  classical
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    by_cases hji : j = i
    · subst hji; exact ⟨1, by simp⟩
    · exact ⟨0, by simp [hji]⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨u, hu⟩ := hx
    obtain ⟨v, hv⟩ := hy
    exact ⟨u + v, by simp [hu, hv]⟩
  | smul a x _ hx =>
    obtain ⟨u, hu⟩ := hx
    exact ⟨a * u, by
      rw [← algebraMap_smul K a x, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, hu]⟩


omit [IsDiscreteValuationRing O] in
private theorem lrt_den (b : Module.Basis ι K V) (F : V) :
    ∃ a : O, a ≠ 0 ∧ a • F ∈ span O (Set.range b) := by
  obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O)
    (fun i => b.repr F i)
  refine ⟨a, nonZeroDivisors.ne_zero a.2, ?_⟩
  have hF : (a : O) • F = ∑ i, (a : O) • (b.repr F i • b i) := by
    rw [← Finset.smul_sum, b.sum_repr F]
  rw [hF]
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨z, hz⟩ := ha i
  rw [← smul_assoc, ← hz, algebraMap_smul]
  exact Submodule.smul_mem _ _ (subset_span ⟨i, rfl⟩)

private theorem lrt_inj (b : Module.Basis ι K V) (b' : Module.Basis ι' K V') (io : V →ₗ[K] V')
    (h : ∀ F, io F ∈ Submodule.span O (Set.range b') ↔ F ∈ Submodule.span O (Set.range b)) :
    Function.Injective io := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro F hF
  by_contra hne
  have h0 : b.repr F ≠ 0 := by simpa using hne
  obtain ⟨i, hi⟩ := DFunLike.ne_iff.1 h0
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hmem : ((b.repr F i * algebraMap O K ϖ)⁻¹) • F ∈ span O (Set.range b) := by
    rw [← h, map_smul, hF, smul_zero]; exact zero_mem _
  obtain ⟨z, hz⟩ := lrt_coord b hmem i
  have hϖ0 : algebraMap O K ϖ ≠ 0 := lrt_am_ne hϖ.ne_zero
  have hi' : b.repr F i ≠ 0 := by simpa using hi
  have h1 : algebraMap O K (ϖ * z) = algebraMap O K 1 := by
    rw [map_mul, hz, map_one, map_smul, Finsupp.smul_apply, smul_eq_mul]
    field_simp
  have h2 := IsFractionRing.injective O K h1
  exact hϖ.not_isUnit (IsUnit.of_mul_eq_one _ h2)

theorem latRetract {O K V V' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] [AddCommGroup V'] [Module K V'] [Module O V'] [IsScalarTower O K V'] {ι ι' : Type} [Fintype ι] [Fintype ι'] (b : Module.Basis ι K V) (b' : Module.Basis ι' K V') (io : V →ₗ[K] V') (h : ∀ F, io F ∈ Submodule.span O (Set.range b') ↔ F ∈ Submodule.span O (Set.range b)) : ∃ ret : V' →ₗ[K] V, (∀ F, ret (io F) = F) ∧ ∀ G ∈ Submodule.span O (Set.range b'), ret G ∈ Submodule.span O (Set.range b) := by
  classical
  have : Module.IsTorsionFree O V := lrt_tf O K V
  have : Module.IsTorsionFree O V' := lrt_tf O K V'
  let R : Submodule O V := span O (Set.range b)
  let R' : Submodule O V' := span O (Set.range b')
  have : Module.Finite O R := Module.Finite.span_of_finite O (Set.finite_range b)
  have : Module.Finite O R' := Module.Finite.span_of_finite O (Set.finite_range b')
  let ioR : R →ₗ[O] R' := (io.restrictScalars O).restrict (fun F hF => (h F).2 hF)
  have hinj : Function.Injective ioR := fun x y hxy =>
    Subtype.ext (lrt_inj b b' io h (congrArg Subtype.val hxy))
  let N : Submodule O R' := LinearMap.range ioR
  have : Module.IsTorsionFree O (R' ⧸ N) := by
    refine ⟨fun r hr x y hxy => ?_⟩
    obtain ⟨x, rfl⟩ := N.mkQ_surjective x
    obtain ⟨y, rfl⟩ := N.mkQ_surjective y
    have h1 : N.mkQ (r • (x - y)) = 0 := by
      rw [smul_sub, map_sub, map_smul, map_smul, sub_eq_zero]; exact hxy
    rw [mkQ_apply, Quotient.mk_eq_zero] at h1
    obtain ⟨F, hF⟩ := h1
    have hr0 : r ≠ 0 := hr.ne_zero
    rw [← sub_eq_zero, ← map_sub, mkQ_apply, Quotient.mk_eq_zero]
    have hFv : io (F : V) = r • ((x - y : R') : V') := congrArg Subtype.val hF
    have hcalc : io ((algebraMap O K r)⁻¹ • (F : V)) = ((x - y : R') : V') := by
      rw [map_smul, hFv, ← algebraMap_smul K r, smul_smul, inv_mul_cancel₀ (lrt_am_ne hr0),
        one_smul]
    have hmem : (algebraMap O K r)⁻¹ • (F : V) ∈ R := by
      rw [← h, hcalc]
      exact (x - y).2
    exact ⟨⟨_, hmem⟩, Subtype.ext hcalc⟩
  obtain ⟨s, hs⟩ := N.mkQ.exists_rightInverse_of_surjective N.range_mkQ
  let e := LinearEquiv.ofInjective ioR hinj
  let p : R' →ₗ[O] N := (LinearMap.id - s ∘ₗ N.mkQ).codRestrict N (fun y => by
    rw [← Quotient.mk_eq_zero, ← mkQ_apply, LinearMap.sub_apply, map_sub, sub_eq_zero]
    exact (LinearMap.congr_fun hs (N.mkQ y)).symm)
  let retO : R' →ₗ[O] R := e.symm.toLinearMap ∘ₗ p
  have hretO : ∀ x : R, retO (ioR x) = x := by
    intro x
    show e.symm (p (ioR x)) = x
    rw [LinearEquiv.symm_apply_eq]
    apply Subtype.ext
    have h0 : N.mkQ (ioR x) = 0 := by
      rw [mkQ_apply, Quotient.mk_eq_zero]; exact ⟨x, rfl⟩
    show (LinearMap.id - s ∘ₗ N.mkQ : R' →ₗ[O] R') (ioR x) = ioR x
    simp [h0]
  let ret : V' →ₗ[K] V :=
    b'.constr K (fun j => ((retO ⟨b' j, subset_span ⟨j, rfl⟩⟩ : R) : V))
  have hret : ∀ G (hG : G ∈ R'), ret G = retO ⟨G, hG⟩ := by
    intro G hG
    induction hG using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      exact b'.constr_basis K _ j
    | zero =>
      rw [map_zero]
      exact (congrArg Subtype.val (map_zero retO)).symm
    | add x y hx hy ihx ihy =>
      rw [map_add (f := _), ihx, ihy]
      exact (congrArg Subtype.val (map_add retO ⟨x, hx⟩ ⟨y, hy⟩)).symm
    | smul a x hx ih =>
      have h1 : ret (a • x) = a • ret x := by
        rw [← algebraMap_smul K a x, map_smul, algebraMap_smul]
      rw [h1, ih]
      exact (congrArg Subtype.val (map_smul retO a ⟨x, hx⟩)).symm
  refine ⟨ret, fun F => ?_, fun G hG => by rw [hret G hG]; exact (retO _).2⟩
  obtain ⟨a, ha, haF⟩ := lrt_den (O := O) b F
  have h1 : ret (io (a • F)) = a • F := by
    rw [hret _ ((h _).2 haF)]
    exact congrArg Subtype.val (hretO ⟨a • F, haF⟩)
  have h2 : a • ret (io F) = a • F := by
    rw [← h1, ← algebraMap_smul K a F, map_smul, map_smul, algebraMap_smul]
  exact smul_right_injective V ha h2

end LatRetract

end Formalism.MainNotions.flipOneThree.Pf.KP
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.LemmaSMat
namespace Formalism.MainNotions.flipOneThree.Pf.KP

open Module

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

private theorem smt_unit {s ρ : ℕ} (E : Matrix (Fin s) (Fin ρ) O) (C : Matrix (Fin ρ) (Fin s) O)
    (hE : ∀ i j, E i j ∈ IsLocalRing.maximalIdeal O) : IsUnit (1 - E * C).det := by
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
  have hE0 : E.map (IsLocalRing.residue O) = 0 := by
    ext i j
    simpa [Matrix.map_apply, IsLocalRing.residue_eq_zero_iff] using hE i j
  have h : (RingHom.mapMatrix (IsLocalRing.residue O)) (1 - E * C) = 1 := by
    rw [map_sub, map_one, RingHom.mapMatrix_apply, Matrix.map_mul, hE0, Matrix.zero_mul, sub_zero]
  rw [h, Matrix.det_one]
  exact one_ne_zero

private theorem smt_block {s ρ : ℕ} (z1 z2 : O) (E : Matrix (Fin s) (Fin ρ) O)
    (C : Matrix (Fin ρ) (Fin s) O) (hE : ∀ i j, E i j ∈ IsLocalRing.maximalIdeal O) :
    ∃ M : Matrix (Fin s ⊕ Fin ρ) (Fin s ⊕ Fin ρ) O,
      Matrix.fromBlocks (z1 • (1 : Matrix (Fin s) (Fin s) O)) ((z1 * z2) • E) C
        (z2 • (1 : Matrix (Fin ρ) (Fin ρ) O)) * M =
      (z1 * z2) • (1 : Matrix (Fin s ⊕ Fin ρ) (Fin s ⊕ Fin ρ) O) := by
  have hU := smt_unit E C hE
  have hV : IsUnit (1 - C * E).det := by rw [Matrix.det_one_sub_mul_comm]; exact hU
  have hUi : (1 - E * C) * (1 - E * C)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hU
  have hVi : (1 - C * E) * (1 - C * E)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hV
  refine ⟨Matrix.fromBlocks (z2 • (1 - E * C)⁻¹) (-(z1 * z2) • (E * (1 - C * E)⁻¹))
    (-(C * (1 - E * C)⁻¹)) (z1 • (1 - C * E)⁻¹), ?_⟩
  rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, smul_zero,
    Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e : (z1 * z2) • (1 : Matrix (Fin s) (Fin s) O) = (z1 * z2) • ((1 - E * C) * (1 - E * C)⁻¹) := by
      rw [hUi]
    rw [e]
    simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_neg,
      Matrix.mul_assoc, smul_smul]
    module
  · simp only [Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_neg, Matrix.neg_mul,
      Matrix.mul_assoc, smul_smul, neg_smul]
    module
  · simp only [Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_neg, Matrix.neg_mul,
      Matrix.mul_assoc, smul_smul]
    module
  · have e : (z1 * z2) • (1 : Matrix (Fin ρ) (Fin ρ) O) = (z1 * z2) • ((1 - C * E) * (1 - C * E)⁻¹) := by
      rw [hVi]
    rw [e]
    simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_neg,
      Matrix.neg_mul, Matrix.mul_assoc, smul_smul, neg_smul]
    module

theorem lemmaSMat {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (σ ρ : ℕ) (z1 z2 : O) (h1 : z1 ≠ 0) (h2 : z2 ≠ 0) (N : Matrix (Fin σ) (Fin ρ) O) (B : Matrix (Fin ρ) (Fin σ) O) :
  ∃ (r s : ℕ), r + s = σ ∧
    (∃ (P : Matrix (Fin r) (Fin σ) O) (Q : Matrix (Fin ρ) (Fin r) O), P * N * Q = (z1 * z2) • (1 : Matrix (Fin r) (Fin r) O)) ∧
    (∃ (P' : Matrix (Fin s) (Fin σ) O) (P'' : Matrix (Fin σ) (Fin s) O) (M : Matrix (Fin s ⊕ Fin ρ) (Fin s ⊕ Fin ρ) O), P' * P'' = 1 ∧
      Matrix.fromBlocks (z1 • (1 : Matrix (Fin s) (Fin s) O)) (P' * N) (B * P'') (z2 • (1 : Matrix (Fin ρ) (Fin ρ) O)) * M = (z1 * z2) • (1 : Matrix (Fin s ⊕ Fin ρ) (Fin s ⊕ Fin ρ) O)) := by
  classical
  have hz0 : z1 * z2 ≠ 0 := mul_ne_zero h1 h2
  have key : ∀ (n : ℕ) (N : Matrix (Fin n) (Fin ρ) O), ∃ (r s : ℕ), r + s = n ∧
      (∃ (P : Matrix (Fin r) (Fin n) O) (Q : Matrix (Fin ρ) (Fin r) O),
        P * N * Q = (z1 * z2) • (1 : Matrix (Fin r) (Fin r) O)) ∧
      (∃ (P' : Matrix (Fin s) (Fin n) O) (P'' : Matrix (Fin n) (Fin s) O), P' * P'' = 1 ∧
        ∀ i j, ∃ e ∈ IsLocalRing.maximalIdeal O, (P' * N) i j = z1 * z2 * e) := by
    intro n
    induction n with
    | zero =>
      intro N
      refine ⟨0, 0, rfl, ⟨0, 0, ?_⟩, ⟨0, 0, ?_, fun i => i.elim0⟩⟩
      · ext i; exact i.elim0
      · ext i; exact i.elim0
    | succ n ih =>
      intro N
      by_cases hall : ∀ i j, ∃ e ∈ IsLocalRing.maximalIdeal O, N i j = z1 * z2 * e
      · refine ⟨0, n + 1, by omega, ⟨0, 0, ?_⟩, ⟨1, 1, Matrix.one_mul 1, ?_⟩⟩
        · ext i; exact i.elim0
        · intro i j; rw [Matrix.one_mul]; exact hall i j
      obtain ⟨ia, hia⟩ := not_forall.mp hall
      obtain ⟨ja, hna⟩ := not_forall.mp hia
      obtain ⟨⟨i0, j0⟩, -, hmin⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin (n + 1) × Fin ρ))
        (fun p => IsDiscreteValuationRing.addVal O (N p.1 p.2)) ⟨(ia, ja), Finset.mem_univ _⟩
      have hdiv : ∀ p : Fin (n + 1) × Fin ρ, N i0 j0 ∣ N p.1 p.2 := fun p =>
        (IsDiscreteValuationRing.addVal_le_iff_dvd).mp (hmin p (Finset.mem_univ _))
      have haz : N i0 j0 ∣ z1 * z2 := by
        by_contra hnd
        rcases le_total (IsDiscreteValuationRing.addVal O (N i0 j0))
            (IsDiscreteValuationRing.addVal O (z1 * z2)) with h | h
        · exact hnd ((IsDiscreteValuationRing.addVal_le_iff_dvd).mp h)
        · obtain ⟨e, he⟩ := (IsDiscreteValuationRing.addVal_le_iff_dvd).mp h
          have hem : e ∈ IsLocalRing.maximalIdeal O := by
            rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
            rintro ⟨u, rfl⟩
            exact hnd ⟨↑u⁻¹, by rw [he, mul_assoc, Units.mul_inv, mul_one]⟩
          apply hna
          obtain ⟨b, hb⟩ : N i0 j0 ∣ N ia ja := hdiv (ia, ja)
          exact ⟨e * b, Ideal.mul_mem_right _ _ hem, by rw [hb, he, mul_assoc]⟩
      obtain ⟨t, ht⟩ := haz
      choose f hf using hdiv
      have hf' : ∀ i l, N i l = N i0 j0 * f (i, l) := fun i l => hf (i, l)
      have ha0 : N i0 j0 ≠ 0 := by
        intro h0; apply hz0; rw [ht, h0, zero_mul]
      have hf00 : f (i0, j0) = 1 := by
        apply mul_left_cancel₀ ha0
        rw [mul_one]; exact (hf' i0 j0).symm
      let N1 : Matrix (Fin n) (Fin ρ) O :=
        Matrix.of fun k l => N (i0.succAbove k) l - f (i0.succAbove k, j0) * N i0 l
      obtain ⟨r1, s1, hrs, ⟨P1, Q1, hPQ⟩, ⟨P1', P1'', hP1, hgood⟩⟩ := ih N1
      let S : Matrix (Fin n) (Fin (n + 1)) O := Matrix.of fun k i =>
        (if i = i0.succAbove k then 1 else 0) - (if i = i0 then f (i0.succAbove k, j0) else 0)
      let Em : Matrix (Fin (n + 1)) (Fin n) O := Matrix.of fun i k => if i = i0.succAbove k then 1 else 0
      let Ei : Matrix (Fin 1) (Fin (n + 1)) O := Matrix.of fun _ i => if i = i0 then t else 0
      let ej : Matrix (Fin ρ) (Fin 1) O := Matrix.of fun l _ => if l = j0 then 1 else 0
      let dd : Matrix (Fin 1) (Fin ρ) O := Matrix.of fun _ l => f (i0, l)
      let Q1' : Matrix (Fin ρ) (Fin r1) O := Q1 - ej * (dd * Q1)
      have hSN : S * N = N1 := by
        ext k l
        simp [S, N1, Matrix.mul_apply, sub_mul, Finset.sum_sub_distrib, ite_mul]
      have hSE : S * Em = 1 := by
        ext k k'
        have hne : i0 ≠ i0.succAbove k' := Fin.ne_succAbove i0 k'
        have hne' : i0.succAbove k' ≠ i0 := Fin.succAbove_ne i0 k'
        simp only [S, Em, Matrix.mul_apply, Matrix.of_apply, sub_mul, Finset.sum_sub_distrib, ite_mul,
          one_mul, zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true, Matrix.one_apply]
        simp [hne, hne', Fin.succAbove_right_inj]
      have hrow : Ei * N = (z1 * z2) • dd := by
        ext i l
        simp [Ei, dd, Matrix.mul_apply, ite_mul]
        rw [hf' i0 l, ht]; ring
      have hdd : dd * ej = 1 := by
        ext i j
        fin_cases i; fin_cases j
        simp [dd, ej, Matrix.mul_apply, hf00]
      have hN1e : N1 * ej = 0 := by
        ext k j
        simp [N1, ej, Matrix.mul_apply]
        rw [hf' (i0.succAbove k) j0]; ring
      have hblocks : Matrix.fromRows Ei (P1 * S) * N * Matrix.fromCols ej Q1' =
          (z1 * z2) • (1 : Matrix (Fin 1 ⊕ Fin r1) (Fin 1 ⊕ Fin r1) O) := by
        rw [Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols, ← Matrix.fromBlocks_one,
          Matrix.fromBlocks_smul, smul_zero, smul_zero, Matrix.fromBlocks_inj]
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hrow, Matrix.smul_mul, hdd]
        · rw [hrow, Matrix.mul_sub, Matrix.smul_mul, Matrix.smul_mul, ← Matrix.mul_assoc dd ej, hdd,
            Matrix.one_mul, sub_self]
        · rw [Matrix.mul_assoc P1 S N, hSN, Matrix.mul_assoc, hN1e, Matrix.mul_zero]
        · rw [Matrix.mul_assoc P1 S N, hSN, Matrix.mul_sub, ← Matrix.mul_assoc (P1 * N1) ej,
            Matrix.mul_assoc P1 N1 ej, hN1e, Matrix.mul_zero, Matrix.zero_mul, sub_zero, hPQ]
      refine ⟨1 + r1, s1, by omega, ⟨(Matrix.fromRows Ei (P1 * S)).submatrix finSumFinEquiv.symm id,
        (Matrix.fromCols ej Q1').submatrix id finSumFinEquiv.symm, ?_⟩, ⟨P1' * S, Em * P1'', ?_, ?_⟩⟩
      · rw [← Matrix.submatrix_id_id N, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id,
          ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, hblocks]
        ext i j
        simp [Matrix.one_apply]
      · rw [Matrix.mul_assoc, ← Matrix.mul_assoc S Em, hSE, Matrix.one_mul, hP1]
      · intro i j
        rw [Matrix.mul_assoc, hSN]
        exact hgood i j
  obtain ⟨r, s, hrs, hP, P', P'', hP', hg⟩ := key σ N
  refine ⟨r, s, hrs, hP, P', P'', ?_⟩
  choose E hEm hE using hg
  obtain ⟨M, hM⟩ := smt_block z1 z2 (Matrix.of E) (B * P'') (fun i j => hEm i j)
  refine ⟨M, hP', ?_⟩
  have hPN : P' * N = (z1 * z2) • Matrix.of E := by
    ext i j
    simp [hE i j]
  rw [hPN]
  exact hM

end Formalism.MainNotions.flipOneThree.Pf.KP
end
