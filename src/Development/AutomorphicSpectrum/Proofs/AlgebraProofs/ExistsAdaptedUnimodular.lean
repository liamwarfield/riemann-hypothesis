module

public import Mathlib

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsAdaptedUnimodular
open Matrix Filter Topology
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.ToricBasis

private theorem transpose_mul_mul_apply_eq_dot_product_mul_vec {m n R : Type*} [Fintype m]
    [CommSemiring R] (P : Matrix m n R) (A : Matrix m m R) (x y : n) :
    (Pᵀ * A * P) x y = Pᵀ x ⬝ᵥ A *ᵥ Pᵀ y := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem exists_isCompl_ker {g : ℕ} (f : (Fin g → ℤ) →ₗ[ℤ] (Fin g → ℤ)) :
    ∃ M : Submodule ℤ (Fin g → ℤ), IsCompl M (LinearMap.ker f) := by
  haveI : Module.Free ℤ (LinearMap.range f) := Module.free_of_finite_type_torsion_free'
  obtain ⟨t, ht⟩ :=
    LinearMap.exists_rightInverse_of_surjective f.rangeRestrict (LinearMap.range_rangeRestrict f)
  have hft : ∀ y : LinearMap.range f, f (t y) = y := fun y =>
    congrArg Subtype.val (LinearMap.congr_fun ht y)
  refine ⟨LinearMap.range t, ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    rintro x ⟨y, rfl⟩ hy
    rw [LinearMap.mem_ker] at hy
    have hy0 : y = 0 := Subtype.ext ((hft y).symm.trans hy)
    rw [hy0, map_zero]
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    rw [Submodule.mem_sup]
    refine ⟨t (f.rangeRestrict x), LinearMap.mem_range_self _ _, x - t (f.rangeRestrict x), ?_,
      by abel⟩
    rw [LinearMap.mem_ker, map_sub, hft, sub_eq_zero]
    rfl

theorem exists_adapted_basis {g : ℕ} (f : (Fin g → ℤ) →ₗ[ℤ] (Fin g → ℤ)) :
    ∃ (r s : ℕ) (b : Module.Basis (Fin r ⊕ Fin s) ℤ (Fin g → ℤ)),
      (∀ k, f (b (Sum.inr k)) = 0) ∧
      ∀ x : Fin r → ℤ, f (∑ a, x a • b (Sum.inl a)) = 0 → x = 0 := by
  obtain ⟨M, hM⟩ := GlobalTheory.CompanionTheory.ToricBasis.exists_isCompl_ker f
  haveI : Module.Free ℤ M := Module.free_of_finite_type_torsion_free'
  haveI : Module.Free ℤ (LinearMap.ker f) := Module.free_of_finite_type_torsion_free'
  obtain ⟨bM⟩ : Nonempty (Module.Basis (Fin (Module.finrank ℤ M)) ℤ M) :=
    ⟨Module.finBasis ℤ M⟩
  obtain ⟨bK⟩ : Nonempty (Module.Basis (Fin (Module.finrank ℤ (LinearMap.ker f))) ℤ
      (LinearMap.ker f)) := ⟨Module.finBasis ℤ (LinearMap.ker f)⟩
  have hb : ∀ i, (bM.prod bK).map (Submodule.prodEquivOfIsCompl M (LinearMap.ker f) hM) i =
      ((bM.prod bK i).1 : Fin g → ℤ) + ((bM.prod bK i).2 : Fin g → ℤ) := fun i => by
    rw [Module.Basis.map_apply, Submodule.coe_prodEquivOfIsCompl']
  refine ⟨_, _, (bM.prod bK).map (Submodule.prodEquivOfIsCompl M (LinearMap.ker f) hM), ?_, ?_⟩
  · intro k
    rw [hb, Module.Basis.prod_apply]
    simp only [Sum.elim_inr, Function.comp_apply, LinearMap.inr_apply, ZeroMemClass.coe_zero,
      zero_add]
    exact LinearMap.mem_ker.mp (bK k).2
  · intro x hx
    have hinl : ∀ a, (bM.prod bK).map (Submodule.prodEquivOfIsCompl M (LinearMap.ker f) hM)
        (Sum.inl a) = (bM a : Fin g → ℤ) := fun a => by
      rw [hb, Module.Basis.prod_apply]
      simp only [Sum.elim_inl, Function.comp_apply, LinearMap.inl_apply, ZeroMemClass.coe_zero,
        add_zero]
    simp only [hinl] at hx
    have hmem : (∑ a, x a • (bM a : Fin g → ℤ)) ∈ M :=
      Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (bM a).2
    have h0 := Submodule.disjoint_def.mp hM.disjoint _ hmem (LinearMap.mem_ker.mpr hx)
    have h0' : ∑ a, x a • bM a = 0 := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simpa only [Submodule.coe_smul, ZeroMemClass.coe_zero] using h0
    funext a
    exact Fintype.linearIndependent_iff.mp bM.linearIndependent x h0' a

theorem cast_quad {g : ℕ} (A : Matrix (Fin g) (Fin g) ℤ) (v : Fin g → ℤ) :
    star (fun i => (v i : ℝ)) ⬝ᵥ (A.map (fun x : ℤ => (x : ℝ))) *ᵥ (fun i => (v i : ℝ))
      = ((v ⬝ᵥ A *ᵥ v : ℤ) : ℝ) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply, star_trivial,
    Int.cast_sum, Int.cast_mul]

theorem quad_nonneg {g : ℕ} {A : Matrix (Fin g) (Fin g) ℤ}
    (hA : (A.map (fun x : ℤ => (x : ℝ))).PosSemidef) (v : Fin g → ℤ) : 0 ≤ v ⬝ᵥ A *ᵥ v := by
  have h := hA.dotProduct_mulVec_nonneg (fun i => (v i : ℝ))
  rw [GlobalTheory.CompanionTheory.ToricBasis.cast_quad] at h
  exact_mod_cast h

theorem mulVec_eq_zero_of_quad {g : ℕ} {A : Matrix (Fin g) (Fin g) ℤ}
    (hA : (A.map (fun x : ℤ => (x : ℝ))).PosSemidef) (v : Fin g → ℤ) (h : v ⬝ᵥ A *ᵥ v = 0) :
    A *ᵥ v = 0 := by
  have h1 : star (fun i => (v i : ℝ)) ⬝ᵥ (A.map (fun x : ℤ => (x : ℝ))) *ᵥ
      (fun i => (v i : ℝ)) = 0 := by
    rw [GlobalTheory.CompanionTheory.ToricBasis.cast_quad, h, Int.cast_zero]
  have h2 := hA.dotProduct_mulVec_zero_iff.mp h1
  funext i
  have h3 := congrFun h2 i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply] at h3 ⊢
  exact_mod_cast h3

theorem symm_of_posSemidef {g : ℕ} {A : Matrix (Fin g) (Fin g) ℤ}
    (hA : (A.map (fun x : ℤ => (x : ℝ))).PosSemidef) : Aᵀ = A := by
  ext i j
  have h := hA.isHermitian.apply i j
  simp only [Matrix.map_apply, star_trivial] at h
  rw [Matrix.transpose_apply]
  exact_mod_cast h

theorem exists_adapted_unimodular :
    ∀ (g : ℕ) (J : Type) [Fintype J] (B : J → Matrix (Fin g) (Fin g) ℤ), (∀ j, ((B j).map (fun x : ℤ => (x : ℝ))).PosSemidef) → ∃ (r s : ℕ) (e : Fin r ⊕ Fin s ≃ Fin g) (Q : Matrix (Fin g) (Fin g) ℤ), IsUnit Q.det ∧ (∀ j k l, ((Qᵀ * B j * Q).submatrix e e) (Sum.inr k) l = 0 ∧ ((Qᵀ * B j * Q).submatrix e e) l (Sum.inr k) = 0) ∧ ((((Qᵀ * (∑ j, B j) * Q).submatrix e e).toBlocks₁₁).map (fun x : ℤ => (x : ℝ))).PosDef := by
  intro g J _ B hB
  obtain ⟨S, hSdef⟩ : ∃ S : Matrix (Fin g) (Fin g) ℤ, S = ∑ j, B j := ⟨_, rfl⟩
  rw [← hSdef]
  have hSpsd : (S.map (fun x : ℤ => (x : ℝ))).PosSemidef := by
    have hmap : S.map (fun x : ℤ => (x : ℝ)) = ∑ j, (B j).map (fun x : ℤ => (x : ℝ)) := by
      ext i i'
      simp only [hSdef, Matrix.map_apply, Matrix.sum_apply, Int.cast_sum]
    rw [hmap]
    exact Matrix.posSemidef_sum Finset.univ fun j _ => hB j
  obtain ⟨r, s, b, hker, hinj⟩ := GlobalTheory.CompanionTheory.ToricBasis.exists_adapted_basis (Matrix.mulVecLin S)
  have hcard : g = r + s := by
    have h := Module.finrank_eq_card_basis b
    rwa [Module.finrank_fin_fun ℤ, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at h
  obtain ⟨e⟩ : Nonempty (Fin r ⊕ Fin s ≃ Fin g) := ⟨finSumFinEquiv.trans (finCongr hcard.symm)⟩
  obtain ⟨Q, hQdef⟩ : ∃ Q : Matrix (Fin g) (Fin g) ℤ,
      Q = (Pi.basisFun ℤ (Fin g)).toMatrix (b.reindex e) := ⟨_, rfl⟩
  have hQ : ∀ i m, Q i m = b (e.symm m) i := by
    intro i m
    rw [hQdef, Module.Basis.toMatrix_apply, Pi.basisFun_repr, Module.Basis.reindex_apply]
  have hunit : IsUnit Q.det := by
    rw [hQdef]
    letI := Module.Basis.invertibleToMatrix (Pi.basisFun ℤ (Fin g)) (b.reindex e)
    exact Matrix.isUnit_det_of_invertible _
  have hcol : ∀ α, Qᵀ (e α) = b α := fun α => funext fun i => by
    rw [Matrix.transpose_apply, hQ, e.symm_apply_apply]
  have hentry : ∀ (X : Matrix (Fin g) (Fin g) ℤ) (α β : Fin r ⊕ Fin s),
      ((Qᵀ * X * Q).submatrix e e) α β = b α ⬝ᵥ X *ᵥ b β := by
    intro X α β
    rw [Matrix.submatrix_apply, transpose_mul_mul_apply_eq_dot_product_mul_vec, hcol, hcol]
  have hBk : ∀ j k, B j *ᵥ b (Sum.inr k) = 0 := by
    intro j k
    have hSk : S *ᵥ b (Sum.inr k) = 0 := by
      have h := hker k
      rwa [Matrix.mulVecLin_apply] at h
    have hsum : ∑ i, b (Sum.inr k) ⬝ᵥ B i *ᵥ b (Sum.inr k) = 0 := by
      rw [← dotProduct_sum, ← Matrix.sum_mulVec, ← hSdef, hSk, dotProduct_zero]
    have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
      GlobalTheory.CompanionTheory.ToricBasis.quad_nonneg (hB i) _)).mp hsum j
        (Finset.mem_univ _)
    exact GlobalTheory.CompanionTheory.ToricBasis.mulVec_eq_zero_of_quad (hB j) _ hj
  refine ⟨r, s, e, Q, hunit, ?_, ?_⟩
  · intro j k l
    refine ⟨?_, ?_⟩
    · rw [hentry, Matrix.dotProduct_mulVec,
        ← GlobalTheory.CompanionTheory.ToricBasis.symm_of_posSemidef (hB j), Matrix.vecMul_transpose, hBk,
        zero_dotProduct]
    · rw [hentry, hBk, dotProduct_zero]
  · obtain ⟨C, hC⟩ : ∃ C : Matrix (Fin g) (Fin r) ℤ, ∀ i a, C i a = b (Sum.inl a) i :=
      ⟨Matrix.of fun i a => b (Sum.inl a) i, fun _ _ => rfl⟩
    have hCt : ∀ a, Cᵀ a = b (Sum.inl a) := fun a => funext fun i => by
      rw [Matrix.transpose_apply, hC]
    have hMC : ((Qᵀ * S * Q).submatrix e e).toBlocks₁₁ = Cᵀ * S * C := by
      ext a a'
      rw [transpose_mul_mul_apply_eq_dot_product_mul_vec, hCt, hCt, ← hentry]
      rfl
    rw [hMC]
    have hN : (Cᵀ * S * C).map (fun x : ℤ => (x : ℝ)) =
        (C.map (fun x : ℤ => (x : ℝ)))ᴴ * S.map (fun x : ℤ => (x : ℝ)) *
          C.map (fun x : ℤ => (x : ℝ)) := by
      ext a a'
      simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Matrix.transpose_apply, star_trivial, Int.cast_sum, Int.cast_mul]
    have hNpsd : ((Cᵀ * S * C).map (fun x : ℤ => (x : ℝ))).PosSemidef := by
      rw [hN]
      exact hSpsd.conjTranspose_mul_mul_same _
    refine Matrix.PosDef.of_dotProduct_mulVec_pos hNpsd.isHermitian ?_
    intro x hx
    refine lt_of_le_of_ne (hNpsd.dotProduct_mulVec_nonneg x) fun h0 => ?_
    have hNx := hNpsd.dotProduct_mulVec_zero_iff.mp h0.symm
    have hdetN : ((Cᵀ * S * C).map (fun x : ℤ => (x : ℝ))).det = 0 :=
      Matrix.exists_mulVec_eq_zero_iff.mp ⟨x, hx, hNx⟩
    have hdetZ : (Cᵀ * S * C).det = 0 := by
      have h1 : (((Cᵀ * S * C).det : ℤ) : ℝ) = 0 := by
        rw [← hdetN]
        have h2 := RingHom.map_det (Int.castRingHom ℝ) (Cᵀ * S * C)
        rw [RingHom.mapMatrix_apply] at h2
        exact h2
      exact_mod_cast h1
    obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdetZ
    have hquad : (C *ᵥ v) ⬝ᵥ S *ᵥ (C *ᵥ v) = 0 := by
      have h3 : v ⬝ᵥ (Cᵀ * S * C) *ᵥ v = (C *ᵥ v) ⬝ᵥ S *ᵥ (C *ᵥ v) := by
        rw [← Matrix.mulVec_mulVec v (Cᵀ * S) C, ← Matrix.mulVec_mulVec (C *ᵥ v) Cᵀ S,
          Matrix.dotProduct_mulVec v Cᵀ, Matrix.vecMul_transpose C v]
      rw [← h3, hv0, dotProduct_zero]
    have hSw := GlobalTheory.CompanionTheory.ToricBasis.mulVec_eq_zero_of_quad hSpsd
      (C *ᵥ v) hquad
    have hCv : C *ᵥ v = ∑ a, v a • b (Sum.inl a) := by
      ext i
      rw [Finset.sum_apply]
      simp only [Matrix.mulVec, dotProduct, hC, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun a _ => mul_comm _ _
    exact hv (hinj v (by rw [Matrix.mulVecLin_apply, ← hCv]; exact hSw))

end GlobalTheory.CompanionTheory.ToricBasis
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AlgClosedTensorIsDomain
section -- merged from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.TensorAlgebraicallyClosedDomain
open TensorProduct

namespace PositivityTheory.Xgn.TensorDomain

open Polynomial
open scoped IntermediateField

theorem natDegree_minpoly_eq {k F A : Type} [Field k] [Field F] [Field A] [Algebra k F]
    [Algebra F A] [Algebra k A] [IsScalarTower k F A]
    (h : ∀ x : F, IsAlgebraic k x → x ∈ (algebraMap k F).range)
    {θ : A} (hθ : IsIntegral k θ) : (minpoly F θ).natDegree = (minpoly k θ).natDegree := by
  have hF : IsIntegral F θ := hθ.tower_top
  have hd : minpoly F θ ∣ (minpoly k θ).map (algebraMap k F) :=
    minpoly.dvd_map_of_isScalarTower k F θ
  have h1 := integralClosure.mem_lifts_of_monic_of_dvd_map F (minpoly.monic hθ)
    (minpoly.monic hF) hd
  have h2 : minpoly F θ ∈ lifts (algebraMap k F) := by
    rw [lifts_iff_coeff_lifts] at h1 ⊢
    intro n
    obtain ⟨y, hy⟩ := h1 n
    rw [← hy]
    exact h _ (IsIntegral.isAlgebraic y.2)
  obtain ⟨q, hq, hdeg, hm⟩ := lifts_and_natDegree_eq_and_monic h2 (minpoly.monic hF)
  apply le_antisymm
  · have := natDegree_le_of_dvd hd ((minpoly.monic hθ).map _).ne_zero
    rwa [natDegree_map] at this
  · rw [← hdeg]
    refine natDegree_le_of_dvd (minpoly.dvd k θ ?_) hm.ne_zero
    rw [← aeval_map_algebraMap F, hq, minpoly.aeval]

theorem linearDisjoint_algebraicClosure {K Ω L : Type} [Field K] [CharZero K] [Field Ω] [Field L]
    [Algebra K Ω] [Algebra Ω L] [Algebra K L] [IsScalarTower K Ω L]
    (h : ∀ a : Ω, IsAlgebraic K a → a ∈ (algebraMap K Ω).range) :
    (algebraicClosure K L).LinearDisjoint Ω := by
  have : Algebra.IsIntegral K (algebraicClosure K L).toSubalgebra :=
    (algebraicClosure.isAlgebraic K L).isIntegral
  refine Subalgebra.LinearDisjoint.of_linearDisjoint_finite_left _ _ fun B hB _ => ?_
  have halg : B.IsAlgebraic := fun x hx => (mem_algebraicClosure_iff (F := K)).1 (hB hx)
  let M : IntermediateField K L := halg.toIntermediateField
  haveI : FiniteDimensional K M := ‹Module.Finite K B›
  change M.LinearDisjoint Ω
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element K M
  have hi : IsIntegral K (θ : L) := (Algebra.IsIntegral.isIntegral (R := K) θ).map M.val
  have e : K⟮(θ : L)⟯ = M := by
    have := congrArg (IntermediateField.lift (F := M)) hθ
    simpa using this
  rw [← e]
  refine IntermediateField.LinearDisjoint.of_basis_left
    (IntermediateField.adjoin.powerBasis hi).basis ?_
  have hd := natDegree_minpoly_eq (F := Ω) h hi
  have hl := linearIndependent_pow (K := Ω) (θ : L)
  rw [hd] at hl
  have he : (K⟮(θ : L)⟯.val ∘ (IntermediateField.adjoin.powerBasis hi).basis) =
      fun i : Fin (IntermediateField.adjoin.powerBasis hi).dim => (θ : L) ^ (i : ℕ) := by
    funext i
    simp
  rw [he]
  exact hl

theorem exists_point (k A : Type) [Field k] [IsAlgClosed k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] {a : A} (ha : a ≠ 0) : ∃ φ : A →ₐ[k] k, φ a ≠ 0 := by
  let S := Localization.Away a
  haveI : IsDomain S :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors ha)
  haveI : Algebra.FiniteType A S := IsLocalization.finiteType_of_monoid_fg (Submonoid.powers a) S
  haveI : Algebra.FiniteType k S := Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  obtain ⟨m, hm⟩ := Ideal.exists_maximal S
  letI : Field (S ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite k (S ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (S ⧸ m)
  let ψ : (S ⧸ m) →ₐ[k] k := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨(ψ.comp (Ideal.Quotient.mkₐ k m)).comp (IsScalarTower.toAlgHom k A S), ?_⟩
  have hu : IsUnit (algebraMap A S a) := IsLocalization.Away.algebraMap_isUnit a
  exact (hu.map (ψ.comp (Ideal.Quotient.mkₐ k m))).ne_zero

theorem isDomain_tensor_of_isAlgClosed (k A : Type) [Field k] [IsAlgClosed k] [CommRing A]
    [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] (F : Type) [Field F] [Algebra k F] :
    IsDomain (F ⊗[k] A) := by
  let b := Module.Basis.ofVectorSpace k F
  let B := Algebra.TensorProduct.basis A b
  haveI : Nontrivial (A ⊗[k] F) :=
    (Algebra.TensorProduct.includeRight_injective (R := k) (A := A) (B := F)
      (algebraMap k A).injective).nontrivial
  haveI : NoZeroDivisors (A ⊗[k] F) := ⟨fun {x y} hxy => by
    by_contra hc
    rw [not_or] at hc
    obtain ⟨hx, hy⟩ := hc
    obtain ⟨i, hi⟩ : ∃ i, B.repr x i ≠ 0 := by
      by_contra hn
      exact hx (B.repr.map_eq_zero_iff.1 (Finsupp.ext fun i => not_not.1 fun h => hn ⟨i, h⟩))
    obtain ⟨j, hj⟩ : ∃ i, B.repr y i ≠ 0 := by
      by_contra hn
      exact hy (B.repr.map_eq_zero_iff.1 (Finsupp.ext fun i => not_not.1 fun h => hn ⟨i, h⟩))
    obtain ⟨φ, hφ⟩ := exists_point k A (mul_ne_zero hi hj)
    let Φ : A ⊗[k] F →ₐ[k] F :=
      Algebra.TensorProduct.lift ((Algebra.ofId k F).comp φ) (AlgHom.id k F)
        fun _ _ => Commute.all _ _
    have key : ∀ z i, φ (B.repr z i) = b.repr (Φ z) i := by
      intro z i
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add u v hu hv => simp only [map_add (f := _), Finsupp.add_apply, hu, hv]
      | tmul a f =>
        have h1 : Φ (a ⊗ₜ f) = φ a • f := by simp [Φ, Algebra.smul_def]
        rw [h1, map_smul]
        simp [B, Algebra.TensorProduct.basis_repr_tmul]
    have h0 : Φ x * Φ y = 0 := by rw [← map_mul, hxy, map_zero]
    apply hφ
    rw [map_mul, key, key]
    rcases mul_eq_zero.1 h0 with h | h <;> simp [h]⟩
  haveI : IsDomain (A ⊗[k] F) := NoZeroDivisors.to_isDomain _
  exact (Algebra.TensorProduct.comm k F A).toMulEquiv.isDomain

theorem isDomain_tensor_of_closure (k Ω S : Type) [Field k] [Field Ω] [IsAlgClosed Ω] [Algebra k Ω]
    [Algebra.IsAlgebraic k Ω] [CommRing S] [Algebra k S] [Algebra.FiniteType k S]
    [IsDomain (Ω ⊗[k] S)] (F : Type) [Field F] [Algebra k F] : IsDomain (F ⊗[k] S) := by
  let L := AlgebraicClosure F
  let j : Ω →ₐ[k] L := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  letI : Algebra Ω L := j.toRingHom.toAlgebra
  haveI : IsScalarTower k Ω L := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  haveI := isDomain_tensor_of_isAlgClosed Ω (Ω ⊗[k] S) L
  haveI : IsDomain (L ⊗[k] S) :=
    (Algebra.TensorProduct.cancelBaseChange k Ω L L S).symm.toMulEquiv.isDomain _
  let φ := Algebra.TensorProduct.map (IsScalarTower.toAlgHom k F L) (AlgHom.id k S)
  have hφ : Function.Injective φ :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := S)
      (IsScalarTower.toAlgHom k F L).toLinearMap (algebraMap F L).injective
  exact Function.Injective.isDomain φ.toRingHom hφ

theorem isDomain_tensor {K A Ω : Type} [Field K] [CharZero K] [CommRing A] [Field Ω] [Algebra K A]
    [Algebra K Ω] [Algebra.FiniteType K A] (j : A →ₐ[K] Ω) (hj : Function.Injective j)
    (h : ∀ a : Ω, IsAlgebraic K a → a ∈ (algebraMap K Ω).range) (F : Type) [Field F]
    [Algebra K F] : IsDomain (F ⊗[K] A) := by
  let N := algebraicClosure K (AlgebraicClosure Ω)
  haveI : IsDomain (N ⊗[K] Ω) := (linearDisjoint_algebraicClosure h).isDomain
  haveI : IsAlgClosed N := IsAlgClosure.isAlgClosed K
  let φ := Algebra.TensorProduct.map (AlgHom.id K N) j
  have hφ : Function.Injective φ :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := N) j.toLinearMap hj
  haveI : IsDomain (N ⊗[K] A) := Function.Injective.isDomain φ.toRingHom hφ
  exact isDomain_tensor_of_closure K N A F

theorem isDomain_of_algClosed {K L F : Type} [Field K] [Field L] [Field F] [Algebra K L]
    [Algebra K F] [CharZero K] (h : ∀ a : F, IsAlgebraic K a → a ∈ (algebraMap K F).range) :
    IsDomain (L ⊗[K] F) := by
  classical
  haveI : Nontrivial (L ⊗[K] F) :=
    (Algebra.TensorProduct.includeRight_injective (R := K) (A := L) (B := F)
      (algebraMap K L).injective).nontrivial
  haveI : NoZeroDivisors (L ⊗[K] F) := ⟨fun {u v} huv => by
    obtain ⟨Su, rfl⟩ := TensorProduct.exists_finset u
    obtain ⟨Sv, rfl⟩ := TensorProduct.exists_finset v
    let T : Finset F := (Su ∪ Sv).image Prod.snd
    let A := Algebra.adjoin K (T : Set F)
    haveI : Algebra.FiniteType K A :=
      (Subalgebra.fg_iff_finiteType A).1 (Subalgebra.fg_adjoin_finset T)
    haveI := isDomain_tensor A.val Subtype.val_injective h L
    let φ := Algebra.TensorProduct.map (AlgHom.id K L) A.val
    have hφ : Function.Injective φ :=
      Module.Flat.lTensor_preserves_injective_linearMap (M := L) A.val.toLinearMap
        Subtype.val_injective
    have hr : ∀ S : Finset (L × F), S ⊆ Su ∪ Sv → (∑ q ∈ S, q.1 ⊗ₜ[K] q.2) ∈ φ.range :=
      fun S hS => sum_mem fun q hq => ⟨q.1 ⊗ₜ ⟨q.2, Algebra.subset_adjoin
        (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (hS hq)))⟩, rfl⟩
    obtain ⟨a, ha⟩ := hr Su Finset.subset_union_left
    obtain ⟨b, hb⟩ := hr Sv Finset.subset_union_right
    have ha' : φ a = _ := ha
    have hb' : φ b = _ := hb
    rw [← ha', ← hb', ← map_mul, map_eq_zero_iff _ hφ] at huv
    rw [← ha', ← hb']
    rcases mul_eq_zero.1 huv with h0 | h0
    · left; rw [h0, map_zero]
    · right; rw [h0, map_zero]⟩
  exact NoZeroDivisors.to_isDomain _

end PositivityTheory.Xgn.TensorDomain

theorem PositivityTheory.Xgn.tensor_algebraically_closed_domain : ∀ (K Ω C : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [Field C] [Algebra K C], (∀ a : Ω, IsAlgebraic K a → a ∈ (algebraMap K Ω).range) → IsDomain (Ω ⊗[K] C) := by
  intro K Ω C _ _ _ _ _ _ h
  haveI : IsDomain (C ⊗[K] Ω) := PositivityTheory.Xgn.TensorDomain.isDomain_of_algClosed h
  exact (Algebra.TensorProduct.comm K Ω C).toMulEquiv.isDomain
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AlgClosedTensorIsDomain
open TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem isDomain_tensor_of_algebraically_closed_constants :
    ∀ (K Ω C : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [Field C] [Algebra K C],
      (∀ a : Ω, IsAlgebraic K a → a ∈ (algebraMap K Ω).range) → IsDomain (Ω ⊗[K] C) :=
  @PositivityTheory.Xgn.tensor_algebraically_closed_domain

end GlobalTheory.CompanionTheory.Ar.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AlgClosedTensorIsDomainStatement
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.alg_closed_tensor_isDomain : ∀ (K Ω C : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [Field C] [Algebra K C], (∀ a : Ω, IsAlgebraic K a → a ∈ (algebraMap K Ω).range) → IsDomain (Ω ⊗[K] C) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.isDomain_tensor_of_algebraically_closed_constants | exact GlobalTheory.CompanionTheory.Ar.Flat.isDomain_tensor_of_algebraically_closed_constants | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.isDomain_tensor_of_algebraically_closed_constants <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MemMaxSmulTopIff
open Matrix Filter Topology
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.CommAlg.SatOfInj

theorem mem_max_smul_top_iff {R M : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [AddCommGroup M] [Module R M] {π : R} (hπ : Irreducible π) (x : M) :
    x ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) ↔ ∃ z : M, x = π • z := by
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer π |>.mp hπ,
    Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨z, -, rfl⟩
    exact ⟨z, rfl⟩
  · rintro ⟨z, rfl⟩
    exact ⟨z, trivial, rfl⟩

theorem eq_zero_of_smul {R M : Type} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
    [Module.IsTorsionFree R M] {a : R} (ha : a ≠ 0) {z : M} (h : a • z = 0) : z = 0 :=
  (smul_eq_zero.mp h).resolve_left ha

theorem pow_step {R P E : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [AddCommGroup P] [Module R P] [AddCommGroup E] [Module R E] [Module.IsTorsionFree R E]
    (f : P →ₗ[R] E) {π : R} (hπ : Irreducible π)
    (hf : ∀ x : P, f x ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R E) →
      x ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R P))
    (n : ℕ) : ∀ (y : E), π ^ n • y ∈ LinearMap.range f → y ∈ LinearMap.range f := by
  induction n with
  | zero => intro y hy; simpa using hy
  | succ n ih =>
    intro y hy
    obtain ⟨x, hx⟩ := hy
    have hmem : f x ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R E) := by
      rw [mem_max_smul_top_iff hπ]
      exact ⟨π ^ n • y, by rw [hx, pow_succ', mul_smul]⟩
    obtain ⟨x', rfl⟩ := (mem_max_smul_top_iff hπ x).mp (hf x hmem)
    refine ih y ⟨x', ?_⟩
    have h0 : π • (f x' - π ^ n • y) = 0 := by
      rw [smul_sub, ← map_smul, hx, pow_succ', mul_smul, sub_self]
    exact sub_eq_zero.mp (eq_zero_of_smul hπ.ne_zero h0)

theorem sat_of_inj_mod : ∀ (R P E : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [AddCommGroup P] [Module R P] [Module.Finite R P] [AddCommGroup E] [Module R E]
    [Module.IsTorsionFree R E] [Module.IsTorsionFree R P] (f : P →ₗ[R] E),
    (∀ x : P, f x ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R E) →
      x ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R P)) →
    Function.Injective f ∧ ∀ (a : R) (y : E), a ≠ 0 → a • y ∈ LinearMap.range f →
      y ∈ LinearMap.range f := by
  intro R P E _ _ _ _ _ _ _ _ _ _ f hf
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  refine ⟨?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot]
    refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal R) _
      (IsNoetherian.noetherian _) ?_ (IsLocalRing.maximalIdeal_le_jacobson _)
    intro x hx
    have hx0 : f x = 0 := hx
    have hmem : f x ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R E) := by
      rw [hx0]; exact Submodule.zero_mem _
    obtain ⟨x', rfl⟩ := (mem_max_smul_top_iff hπ x).mp (hf x hmem)
    have hx' : f x' = 0 := by
      rw [map_smul] at hx0
      exact eq_zero_of_smul hπ.ne_zero hx0
    exact Submodule.smul_mem_smul
      ((IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ ▸ Ideal.mem_span_singleton_self π)
      (LinearMap.mem_ker.mpr hx')
  · intro a y ha hy
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
    have h1 : π ^ n • ((u : R) • y) ∈ LinearMap.range f := by
      rw [smul_smul, mul_comm]
      exact hy
    have h2 := pow_step f hπ hf n _ h1
    have h3 := Submodule.smul_mem _ ((u⁻¹ : Rˣ) : R) h2
    rwa [smul_smul, Units.inv_mul, one_smul] at h3

end GlobalTheory.CompanionTheory.CommAlg.SatOfInj
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeKernelRankBoundNorm
section -- merged from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.KernelRankNormBound
open NumberField

namespace PositivityTheory.Xgn.AmalgamKernelBound

open Module

theorem det_eq_of_intertwine {M N : Type} [AddCommGroup M] [AddCommGroup N]
    [Module.Free ℤ M] [Module.Finite ℤ M] [Module.Free ℤ N] [Module.Finite ℤ N]
    (ι : N →ₗ[ℤ] M) (hι : Function.Injective ι) (h : finrank ℤ N = finrank ℤ M)
    (f : M →ₗ[ℤ] M) (g : N →ₗ[ℤ] N) (hfg : ∀ x, ι (g x) = f (ι x)) :
    LinearMap.det f = LinearMap.det g := by
  obtain ⟨e⟩ : Nonempty (M ≃ₗ[ℤ] N) := ⟨LinearEquiv.ofFinrankEq M N h.symm⟩
  have hj : Function.Injective ((e : M →ₗ[ℤ] N) ∘ₗ ι) := e.injective.comp hι
  have hdet : LinearMap.det ((e : M →ₗ[ℤ] N) ∘ₗ ι) ≠ 0 := by
    intro h0
    exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp h0) (LinearMap.ker_eq_bot.mpr hj)
  have hcomm : ((e : M →ₗ[ℤ] N) ∘ₗ ι) ∘ₗ g =
      ((e : M →ₗ[ℤ] N) ∘ₗ f ∘ₗ (e.symm : N →ₗ[ℤ] M)) ∘ₗ ((e : M →ₗ[ℤ] N) ∘ₗ ι) := by
    apply LinearMap.ext
    intro x
    simp [hfg]
  have key := congrArg LinearMap.det hcomm
  rw [LinearMap.det_comp ((e : M →ₗ[ℤ] N) ∘ₗ ι) g,
    LinearMap.det_comp ((e : M →ₗ[ℤ] N) ∘ₗ f ∘ₗ (e.symm : N →ₗ[ℤ] M)) ((e : M →ₗ[ℤ] N) ∘ₗ ι),
    LinearMap.det_conj] at key
  exact (mul_left_cancel₀ hdet (key.trans (mul_comm _ _))).symm

theorem det_lsmul (E : Type) [Field E] [NumberField E] (Λ : Type) [AddCommGroup Λ]
    [Module (𝓞 E) Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ] (a : 𝓞 E) :
    LinearMap.det ((LinearMap.lsmul (𝓞 E) Λ a).restrictScalars ℤ) =
      Algebra.norm ℤ a ^ finrank (𝓞 E) Λ := by
  haveI : Module.Finite (𝓞 E) Λ := Module.Finite.of_restrictScalars_finite ℤ (𝓞 E) Λ
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank (R := 𝓞 E) (M := Λ)
    (le_refl (finrank (𝓞 E) Λ))
  let L : (Fin (finrank (𝓞 E) Λ) → 𝓞 E) →ₗ[𝓞 E] Λ := Fintype.linearCombination (𝓞 E) v
  have hL : Function.Injective L :=
    linearIndependent_iff_injective_fintypeLinearCombination.mp hv
  have htors : ∀ x : Λ, ∃ b : 𝓞 E, b ≠ 0 ∧ b • x ∈ LinearMap.range L := by
    have h1 := Submodule.finrank_quotient_add_finrank (LinearMap.range L)
    have h2 : finrank (𝓞 E) (LinearMap.range L) = finrank (𝓞 E) Λ := by
      rw [LinearMap.finrank_range_of_inj hL, Module.finrank_fin_fun]
    have h3 : finrank (𝓞 E) (Λ ⧸ LinearMap.range L) = 0 := by omega
    intro x
    obtain ⟨b, hb, hbx⟩ := Module.finrank_eq_zero_iff.mp h3 (Submodule.Quotient.mk x)
    refine ⟨b, hb, ?_⟩
    rwa [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hbx
  let Lz : (Fin (finrank (𝓞 E) Λ) → 𝓞 E) →ₗ[ℤ] Λ := L.restrictScalars ℤ
  have hLz : Function.Injective Lz := hL
  have htorsZ : ∀ x : Λ, ∃ r : ℤ, r ≠ 0 ∧ r • x ∈ LinearMap.range Lz := by
    intro x
    obtain ⟨b, hb, hbx⟩ := htors x
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hbx
    obtain ⟨r, hr, c, hc⟩ := IsAlgebraic.exists_nonzero_dvd
      (Algebra.IsIntegral.isIntegral (R := ℤ) b).isAlgebraic (mem_nonZeroDivisors_of_ne_zero hb)
    refine ⟨r, hr, LinearMap.mem_range.mpr ⟨c • y, ?_⟩⟩
    show L (c • y) = r • x
    rw [map_smul, hy, ← algebraMap_smul (𝓞 E) r x, hc, mul_comm b c, mul_smul]
  have hrankZ : finrank ℤ (Fin (finrank (𝓞 E) Λ) → 𝓞 E) = finrank ℤ Λ := by
    have h1 := Submodule.finrank_quotient_add_finrank (LinearMap.range Lz)
    have h2 := LinearMap.finrank_range_of_inj hLz
    have h3 : finrank ℤ (Λ ⧸ LinearMap.range Lz) = 0 := by
      rw [Module.finrank_eq_zero_iff]
      intro q
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      obtain ⟨r, hr, hrx⟩ := htorsZ x
      refine ⟨r, hr, ?_⟩
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact hrx
    omega
  have hfg : ∀ y, Lz (((LinearMap.lsmul (𝓞 E) (Fin (finrank (𝓞 E) Λ) → 𝓞 E) a).restrictScalars ℤ) y)
      = ((LinearMap.lsmul (𝓞 E) Λ a).restrictScalars ℤ) (Lz y) := by
    intro y
    simp only [Lz, LinearMap.restrictScalars_apply, LinearMap.lsmul_apply]
    exact map_smul L a y
  have hsmul : LinearMap.lsmul (𝓞 E) (Fin (finrank (𝓞 E) Λ) → 𝓞 E) a = a • LinearMap.id :=
    LinearMap.ext fun y => by simp
  rw [PositivityTheory.Xgn.AmalgamKernelBound.det_eq_of_intertwine Lz hLz hrankZ _ _ hfg,
    LinearMap.det_restrictScalars, hsmul, LinearMap.det_smul, LinearMap.det_id, mul_one,
    Module.finrank_fin_fun, map_pow]

theorem charpoly_lsmul (E : Type) [Field E] [NumberField E] (Λ : Type) [AddCommGroup Λ]
    [Module (𝓞 E) Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ] (a : 𝓞 E) :
    ((LinearMap.lsmul (𝓞 E) Λ a).restrictScalars ℤ).charpoly =
      (Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly ^ finrank (𝓞 E) Λ := by
  apply Polynomial.funext
  intro t
  rw [Polynomial.eval_pow, LinearMap.eval_charpoly, LinearMap.eval_charpoly]
  have h1 : algebraMap ℤ (Module.End ℤ Λ) t - (LinearMap.lsmul (𝓞 E) Λ a).restrictScalars ℤ =
      (LinearMap.lsmul (𝓞 E) Λ (algebraMap ℤ (𝓞 E) t - a)).restrictScalars ℤ := by
    apply LinearMap.ext
    intro x
    simp [sub_smul, Module.algebraMap_end_apply, Int.cast_smul_eq_zsmul]
  have h2 : algebraMap ℤ (Module.End ℤ (𝓞 E)) t - (Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)) =
      Algebra.lmul ℤ (𝓞 E) (algebraMap ℤ (𝓞 E) t - a) := by
    rw [map_sub, AlgHom.commutes]
  rw [h1, h2, PositivityTheory.Xgn.AmalgamKernelBound.det_lsmul, ← Algebra.norm_apply ℤ]

theorem corank_le {M : Type} [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]
    (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (f : M →ₗ[ℤ] M) (hf : LinearMap.det f ≠ 0) :
    finrank k (LinearMap.ker (LinearMap.baseChange k f)) ≤
      padicValNat p (LinearMap.det f).natAbs := by
  classical
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot]
    by_contra h
    exact hf (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr h)
  have hrank : finrank ℤ (LinearMap.range f) = finrank ℤ M := LinearMap.finrank_range_of_inj hinj
  obtain ⟨t, s, d, hst⟩ : ∃ (t : Module.Basis (Fin (finrank ℤ M)) ℤ M)
      (s : Module.Basis (Fin (finrank ℤ M)) ℤ (LinearMap.range f))
      (d : Fin (finrank ℤ M) → ℤ), ∀ i, (s i : M) = d i • t i :=
    ⟨_, _, _, Submodule.smithNormalFormBotBasis_def (Module.finBasis ℤ M) hrank⟩
  obtain ⟨e, he⟩ : ∃ e : M ≃ₗ[ℤ] LinearMap.range f, ∀ x, (e x : M) = f x :=
    ⟨LinearEquiv.ofInjective f hinj, fun x => LinearEquiv.ofInjective_apply f x⟩
  have hfe : f = (LinearMap.range f).subtype ∘ₗ (e : M →ₗ[ℤ] LinearMap.range f) :=
    LinearMap.ext fun x => by simp [he]
  have hD : LinearMap.toMatrix s t (LinearMap.range f).subtype = Matrix.diagonal d := by
    ext i j
    rw [LinearMap.toMatrix_apply, Submodule.subtype_apply, hst j, map_smul,
      Module.Basis.repr_self]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Matrix.diagonal_apply, Finsupp.single_apply, hij, Ne.symm hij]
  have hQ : IsUnit (LinearMap.toMatrix t s (e : M →ₗ[ℤ] LinearMap.range f)).det := by
    have h1 : LinearMap.toMatrix s t (e.symm : LinearMap.range f →ₗ[ℤ] M) *
        LinearMap.toMatrix t s (e : M →ₗ[ℤ] LinearMap.range f) = 1 := by
      rw [← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_id t]
      congr 1
      exact LinearMap.ext fun x => by simp
    have h2 := congrArg Matrix.det h1
    rw [Matrix.det_mul, Matrix.det_one, mul_comm] at h2
    exact isUnit_iff_exists_inv.mpr ⟨_, h2⟩
  have hA : LinearMap.toMatrix t t f =
      Matrix.diagonal d * LinearMap.toMatrix t s (e : M →ₗ[ℤ] LinearMap.range f) := by
    rw [← hD, ← LinearMap.toMatrix_comp, ← hfe]
  have hdvd : (∏ i, d i) ∣ LinearMap.det f := by
    refine ⟨(LinearMap.toMatrix t s (e : M →ₗ[ℤ] LinearMap.range f)).det, ?_⟩
    rw [← LinearMap.det_toMatrix t, hA, Matrix.det_mul, Matrix.det_diagonal]
  have hAk : LinearMap.toMatrix (Algebra.TensorProduct.basis k t) (Algebra.TensorProduct.basis k t)
      (LinearMap.baseChange k f) =
      Matrix.diagonal (fun i => algebraMap ℤ k (d i)) *
        (LinearMap.toMatrix t s (e : M →ₗ[ℤ] LinearMap.range f)).map (algebraMap ℤ k) := by
    rw [LinearMap.toMatrix_baseChange, hA, Matrix.map_mul,
      Matrix.diagonal_map (map_zero (algebraMap ℤ k))]
  have hrange : finrank k (LinearMap.range (LinearMap.baseChange k f)) =
      Fintype.card {i // algebraMap ℤ k (d i) ≠ 0} := by
    rw [← Matrix.toLin_toMatrix (Algebra.TensorProduct.basis k t)
      (Algebra.TensorProduct.basis k t) (LinearMap.baseChange k f),
      ← Matrix.rank_eq_finrank_range_toLin, hAk, Matrix.rank_mul_eq_left_of_isUnit_det]
    · convert Matrix.rank_diagonal (fun i => algebraMap ℤ k (d i))
    · have := hQ.map (algebraMap ℤ k)
      rw [RingHom.map_det] at this
      exact this
  haveI : Module.Finite k (TensorProduct ℤ k M) :=
    Module.Finite.of_basis (Algebra.TensorProduct.basis k t)
  have hsum := LinearMap.finrank_range_add_finrank_ker (LinearMap.baseChange k f)
  rw [Module.finrank_eq_card_basis (Algebra.TensorProduct.basis k t)] at hsum
  have hcongr : Fintype.card {i // algebraMap ℤ k (d i) ≠ 0} =
      Fintype.card {i // ¬ (p : ℤ) ∣ d i} :=
    Fintype.card_congr (Equiv.subtypeEquivRight fun i => by
      rw [eq_intCast, ne_eq, CharP.intCast_eq_zero_iff k p])
  have hcompl : Fintype.card {i // ¬ (p : ℤ) ∣ d i} =
      Fintype.card (Fin (finrank ℤ M)) - Fintype.card {i // (p : ℤ) ∣ d i} :=
    Fintype.card_subtype_compl _
  have hle : Fintype.card {i // (p : ℤ) ∣ d i} ≤ Fintype.card (Fin (finrank ℤ M)) :=
    Fintype.card_subtype_le _
  have hpow : (p : ℤ) ^ Fintype.card {i // (p : ℤ) ∣ d i} ∣ LinearMap.det f := by
    rw [Fintype.card_subtype, ← Finset.prod_const]
    refine dvd_trans ?_ hdvd
    refine dvd_trans (Finset.prod_dvd_prod_of_dvd _ _
      (fun i hi => (Finset.mem_filter.mp hi).2)) ?_
    exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)
  have hne : (LinearMap.det f).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hf
  have hpow' : p ^ Fintype.card {i // (p : ℤ) ∣ d i} ∣ (LinearMap.det f).natAbs := by
    have := Int.natAbs_dvd_natAbs.mpr hpow
    rwa [Int.natAbs_pow, Int.natAbs_natCast] at this
  have hv := ((by simpa only [_root_.Nat.padicValNat_def] using @_root_.multiplicity_dvd_iff_le : ∀ {p : _root_.Nat} [hp : _root_.Fact (_root_.Nat.Prime p)] {a n : _root_.Nat} (ha : a ≠ 0), p ^ n ∣ a ↔ n ≤ _root_.padicValNat p a) hne).mp hpow'
  omega

end PositivityTheory.Xgn.AmalgamKernelBound

theorem PositivityTheory.Xgn.kernel_rank_norm_bound : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ] (a : 𝓞 E), a ≠ 0 → Module.finrank k (LinearMap.ker (LinearMap.baseChange k ((LinearMap.lsmul (𝓞 E) Λ a).restrictScalars ℤ))) ≤ Module.finrank (𝓞 E) Λ * padicValNat p (Algebra.norm ℤ a).natAbs ∧ (LinearMap.baseChange k ((LinearMap.lsmul (𝓞 E) Λ a).restrictScalars ℤ)).charpoly = ((Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly.map (Int.castRingHom k)) ^ Module.finrank (𝓞 E) Λ := by
  intro E _ _ k _ p _ _ Λ _ _ _ _ a ha
  have hdet := PositivityTheory.Xgn.AmalgamKernelBound.det_lsmul E Λ a
  have hN : Algebra.norm ℤ a ≠ 0 := Algebra.norm_ne_zero_iff.mpr ha
  refine ⟨?_, ?_⟩
  · have h := PositivityTheory.Xgn.AmalgamKernelBound.corank_le k p
      ((LinearMap.lsmul (𝓞 E) Λ a).restrictScalars ℤ) (by rw [hdet]; exact pow_ne_zero _ hN)
    rw [hdet, Int.natAbs_pow] at h
    simpa only [Nat.padicValNat_def, Nat.multiplicity_pow] using h
  · rw [LinearMap.charpoly_baseChange, PositivityTheory.Xgn.AmalgamKernelBound.charpoly_lsmul,
      Polynomial.map_pow, algebraMap_int_eq]
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeKernelRankBoundNorm
open NumberField

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem free_extension_kernel_bound_charpoly : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ] (a : 𝓞 E), a ≠ 0 → Module.finrank k (LinearMap.ker (LinearMap.baseChange k ((LinearMap.lsmul (𝓞 E) Λ a).restrictScalars ℤ))) ≤ Module.finrank (𝓞 E) Λ * padicValNat p (Algebra.norm ℤ a).natAbs ∧ (LinearMap.baseChange k ((LinearMap.lsmul (𝓞 E) Λ a).restrictScalars ℤ)).charpoly = ((Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly.map (Int.castRingHom k)) ^ Module.finrank (𝓞 E) Λ := by
  exact @PositivityTheory.Xgn.kernel_rank_norm_bound

end GlobalTheory.CompanionTheory.Ar.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeKernelRankBoundNormStatement
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_kernel_rank_bound_norm : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ] (a : 𝓞 E), a ≠ 0 → Module.finrank k (LinearMap.ker (LinearMap.baseChange k ((LinearMap.lsmul (𝓞 E) Λ a).restrictScalars ℤ))) ≤ Module.finrank (𝓞 E) Λ * padicValNat p (Algebra.norm ℤ a).natAbs ∧ (LinearMap.baseChange k ((LinearMap.lsmul (𝓞 E) Λ a).restrictScalars ℤ)).charpoly = ((Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly.map (Int.castRingHom k)) ^ Module.finrank (𝓞 E) Λ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.free_extension_kernel_bound_charpoly | exact GlobalTheory.CompanionTheory.Ar.Flat.free_extension_kernel_bound_charpoly | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.free_extension_kernel_bound_charpoly <;> assumption)
end
end
