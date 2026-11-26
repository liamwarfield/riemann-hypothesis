module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermForm
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SUnitsNumberFieldFg
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.WithZeroEqOfLeExpIff

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SubgroupPowRelIndexTopOfGroupFg
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

private theorem card_quot_range_nsmul_eq_pow_finrank_mul_card_ker (M : Type) [AddCommGroup M]
    [AddGroup.FG M] (p : ℕ) (hp : 0 < p) :
    Nat.card (nsmulAddMonoidHom (α := M) p).ker ≠ 0 ∧
      (nsmulAddMonoidHom (α := M) p).range.index =
        p ^ Module.finrank ℤ M * Nat.card (nsmulAddMonoidHom (α := M) p).ker := by
  obtain ⟨n, ι, _, q, hq, e, ⟨φ⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod M
  haveI : ∀ i, NeZero (q i ^ e i) := fun i => ⟨pow_ne_zero _ (hq i).ne_zero⟩
  haveI : Finite (DirectSum ι fun i => ZMod (q i ^ e i)) :=
    Finite.of_equiv _ (DirectSum.linearEquivFunOnFintype ℤ ι _).toEquiv.symm
  set D := DirectSum ι fun i => ZMod (q i ^ e i)
  set P := Fin n →₀ ℤ
  have hker : Nat.card (nsmulAddMonoidHom (α := M) p).ker =
      Nat.card (nsmulAddMonoidHom (α := D) p).ker := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(φ x).2, ?_⟩
        invFun := fun y => ⟨φ.symm (0, y), ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · have h := congrArg φ x.2
      rw [nsmulAddMonoidHom_apply, map_nsmul, map_zero] at h
      rw [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply]
      exact congrArg Prod.snd h
    · have h := y.2
      rw [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply] at h ⊢
      rw [← map_nsmul, Prod.smul_mk, smul_zero, h, Prod.mk_zero_zero, map_zero]
    · intro x
      apply Subtype.ext
      apply φ.injective
      have h := congrArg φ x.2
      rw [nsmulAddMonoidHom_apply, map_nsmul, map_zero] at h
      have h1 : p • (φ x).1 = 0 := congrArg Prod.fst h
      have h2 : (φ x).1 = 0 := (smul_eq_zero.mp h1).resolve_left hp.ne'
      simp only [AddEquiv.apply_symm_apply]
      exact Prod.ext h2.symm rfl
    · intro y
      apply Subtype.ext
      simp
  have hrange : (nsmulAddMonoidHom (α := M) p).range =
      AddSubgroup.comap φ.toAddMonoidHom
        ((nsmulAddMonoidHom (α := P) p).range.prod (nsmulAddMonoidHom (α := D) p).range) := by
    ext x
    simp only [AddMonoidHom.mem_range, nsmulAddMonoidHom_apply, AddSubgroup.mem_comap,
      AddSubgroup.mem_prod, AddEquiv.coe_toAddMonoidHom]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨⟨(φ y).1, by rw [map_nsmul]; rfl⟩, ⟨(φ y).2, by rw [map_nsmul]; rfl⟩⟩
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      refine ⟨φ.symm (a, b), φ.injective ?_⟩
      rw [map_nsmul, AddEquiv.apply_symm_apply, Prod.smul_mk, ha, hb]
  have hindexD : (nsmulAddMonoidHom (α := D) p).range.index =
      Nat.card (nsmulAddMonoidHom (α := D) p).ker := by
    haveI : (nsmulAddMonoidHom (α := D) p).ker.FiniteIndex := AddSubgroup.finiteIndex_of_finite
    exact AddSubgroup.index_range
  have hrank : Module.finrank ℤ M = n := by
    rw [φ.toIntLinearEquiv.finrank_eq]
    have h := LinearMap.rank_range_add_rank_ker (LinearMap.fst ℤ P D)
    rw [LinearMap.range_eq_top.mpr fun x => ⟨(x, 0), rfl⟩, LinearMap.ker_fst, rank_top] at h
    have h0 : Module.rank ℤ (LinearMap.inr ℤ P D).range = 0 := by
      rw [rank_eq_zero_iff]
      rintro ⟨x, y, rfl⟩
      refine ⟨(Nat.card D : ℤ), by exact_mod_cast Nat.card_pos.ne', ?_⟩
      apply Subtype.ext
      simp only [SetLike.val_smul, LinearMap.coe_inr, Submodule.coe_zero, natCast_zsmul]
      ext
      · simp
      · simpa using card_nsmul_eq_zero' (x := y)
    rw [h0, add_zero, rank_finsupp_self, Cardinal.mk_fin, Cardinal.lift_natCast] at h
    change Module.finrank ℤ (P × D) = n
    rw [Module.finrank, ← h]
    simp
  refine ⟨?_, ?_⟩
  · rw [hker]
    exact Nat.card_pos.ne'
  · rw [hrange, AddSubgroup.index_comap_of_surjective _ φ.surjective, AddSubgroup.index_prod,
      AddSubgroup.index_range_nsmul, Module.finrank_finsupp_self, Fintype.card_fin, hrank,
      hindexD, hker]

theorem _root_.GlobalTheory.CNorm.pIdx_top_of_fg : ∀ (p : ℕ) (G : Type) [CommGroup G] [Group.FG G],
    0 < p →
    _root_.GlobalTheory.CNorm.pTor p (⊤ : Subgroup G) ≠ 0 ∧
      _root_.GlobalTheory.CNorm.pIdx p (⊤ : Subgroup G) =
        p ^ Module.finrank ℤ (Additive G) * _root_.GlobalTheory.CNorm.pTor p (⊤ : Subgroup G) := by
  intro p G _ _ hp
  obtain ⟨h1, h2⟩ := card_quot_range_nsmul_eq_pow_finrank_mul_card_ker (Additive G) p hp
  have htor : _root_.GlobalTheory.CNorm.pTor p (⊤ : Subgroup G) =
      Nat.card (nsmulAddMonoidHom (α := Additive G) p).ker := by
    unfold _root_.GlobalTheory.CNorm.pTor
    refine Nat.card_congr
      { toFun := fun x => ⟨Additive.ofMul x.1, ?_⟩
        invFun := fun y => ⟨y.1.toMul, Subgroup.mem_top _, ?_⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    · rw [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply, ← ofMul_pow, x.2.2, ofMul_one]
    · have h := y.2
      rw [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply] at h
      rw [← toMul_nsmul, h, toMul_zero]
  have hidx : _root_.GlobalTheory.CNorm.pIdx p (⊤ : Subgroup G) =
      (nsmulAddMonoidHom (α := Additive G) p).range.index := by
    unfold _root_.GlobalTheory.CNorm.pIdx _root_.GlobalTheory.CNorm.pows
    rw [Subgroup.relIndex_top_right, ← Subgroup.index_toAddSubgroup]
    congr 1
    ext x
    change Additive.toMul x ∈ Subgroup.map (powMonoidHom p) ⊤ ↔ _
    rw [Subgroup.mem_map, AddMonoidHom.mem_range]
    constructor
    · rintro ⟨y, -, hy⟩
      exact ⟨Additive.ofMul y, by
        rw [nsmulAddMonoidHom_apply, ← ofMul_pow, ← powMonoidHom_apply, hy, ofMul_toMul]⟩
    · rintro ⟨y, hy⟩
      exact ⟨Additive.toMul y, Subgroup.mem_top _, by
        rw [powMonoidHom_apply, ← toMul_nsmul, ← nsmulAddMonoidHom_apply, hy]⟩
  exact ⟨htor ▸ h1, by rw [hidx, htor]; exact h2⟩

end GlobalTheory.CNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CayleyTransformUnitarySkewInvolutive
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CayleyTransformUnitarySkewInvolutive
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

namespace GlobalTheory.CayleyInv

variable {R : Type} [CommRing R] {n : ℕ}

theorem map_mul_map_inv (σ : R →+* R) (M : Matrix (Fin n) (Fin n) R) (h : IsUnit M.det) :
    M.map σ * (M⁻¹).map σ = 1 := by
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ h, Matrix.map_one σ (map_zero σ) (map_one σ)]

theorem map_one_add (σ : R →+* R) (M : Matrix (Fin n) (Fin n) R) :
    (1 + M).map σ = 1 + M.map σ := by
  rw [Matrix.map_add σ (map_add σ), Matrix.map_one σ (map_zero σ) (map_one σ)]

theorem map_one_sub (σ : R →+* R) (M : Matrix (Fin n) (Fin n) R) :
    (1 - M).map σ = 1 - M.map σ := by
  rw [Matrix.map_sub σ (map_sub σ), Matrix.map_one σ (map_zero σ) (map_one σ)]

theorem one_add_cayley (g : Matrix (Fin n) (Fin n) R) (h : IsUnit (1 + g).det) :
    1 + (1 - g) * (1 + g)⁻¹ = (2 : R) • (1 + g)⁻¹ := by
  have h1 : (1 + g) * (1 + g)⁻¹ = 1 := Matrix.mul_nonsing_inv _ h
  have h2 : (1 + g) + (1 - g) = (2 : R) • (1 : Matrix (Fin n) (Fin n) R) := by
    rw [two_smul]; abel
  calc 1 + (1 - g) * (1 + g)⁻¹ = (1 + g) * (1 + g)⁻¹ + (1 - g) * (1 + g)⁻¹ := by rw [h1]
    _ = ((1 + g) + (1 - g)) * (1 + g)⁻¹ := (Matrix.add_mul _ _ _).symm
    _ = (2 : R) • (1 + g)⁻¹ := by rw [h2, Matrix.smul_mul, Matrix.one_mul]

theorem one_sub_cayley (g : Matrix (Fin n) (Fin n) R) (h : IsUnit (1 + g).det) :
    1 - (1 - g) * (1 + g)⁻¹ = (2 : R) • (g * (1 + g)⁻¹) := by
  have h1 : (1 + g) * (1 + g)⁻¹ = 1 := Matrix.mul_nonsing_inv _ h
  have h2 : (1 + g) - (1 - g) = (2 : R) • g := by
    rw [two_smul]; abel
  calc 1 - (1 - g) * (1 + g)⁻¹ = (1 + g) * (1 + g)⁻¹ - (1 - g) * (1 + g)⁻¹ := by rw [h1]
    _ = ((1 + g) - (1 - g)) * (1 + g)⁻¹ := (Matrix.sub_mul _ _ _).symm
    _ = (2 : R) • (g * (1 + g)⁻¹) := by rw [h2, Matrix.smul_mul]

theorem one_add_cayley_mul (g : Matrix (Fin n) (Fin n) R) (h : IsUnit (1 + g).det) (c : R)
    (hc : 2 * c = 1) : (1 + (1 - g) * (1 + g)⁻¹) * (c • (1 + g)) = 1 := by
  rw [one_add_cayley g h, smul_mul_smul_comm, hc, one_smul, Matrix.nonsing_inv_mul _ h]

private theorem eq_zero_of_mul_mul_eq_zero_of_isUnit_det (A B X : Matrix (Fin n) (Fin n) R)
    (hA : IsUnit A.det) (hB : IsUnit B.det) (h : A * X * B = 0) : X = 0 := by
  calc X = (A⁻¹ * A) * X * (B * B⁻¹) := by
        rw [Matrix.nonsing_inv_mul _ hA, Matrix.mul_nonsing_inv _ hB, Matrix.one_mul,
          Matrix.mul_one]
    _ = A⁻¹ * (A * X * B) * B⁻¹ := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [h, Matrix.mul_zero, Matrix.zero_mul]

private theorem isUnit_det_map_of_isUnit_det (σ : R →+* R) (M : Matrix (Fin n) (Fin n) R)
    (h : IsUnit M.det) : IsUnit (M.map σ).det := by
  simpa [RingHom.map_det, RingHom.mapMatrix_apply] using h.map σ

theorem cayley_transform : ∀ (R : Type) [CommRing R] (σ : R →+* R) (n : ℕ) (G : Matrix (Fin n) (Fin n) R), (∀ x, σ (σ x) = x) → (G.map σ)ᵀ = G → IsUnit G.det → IsUnit (2 : R) → (∀ g : Matrix (Fin n) (Fin n) R, gᵀ * G * g.map σ = G → IsUnit (1 + g).det → ((1 - g) * (1 + g)⁻¹)ᵀ * G + G * ((1 - g) * (1 + g)⁻¹).map σ = 0 ∧ IsUnit (1 + (1 - g) * (1 + g)⁻¹ : Matrix (Fin n) (Fin n) R).det) ∧ (∀ g : Matrix (Fin n) (Fin n) R, IsUnit (1 + g).det → (1 - (1 - g) * (1 + g)⁻¹) * (1 + (1 - g) * (1 + g)⁻¹)⁻¹ = g) ∧ (∀ S : Matrix (Fin n) (Fin n) R, Sᵀ * G + G * S.map σ = 0 → IsUnit (1 + S).det → ((1 - S) * (1 + S)⁻¹)ᵀ * G * ((1 - S) * (1 + S)⁻¹).map σ = G) ∧ ∀ A : Matrix (Fin n) (Fin n) R, (A - (G * A.map σ * G⁻¹)ᵀ)ᵀ * G + G * (A - (G * A.map σ * G⁻¹)ᵀ).map σ = 0 := by
  intro R _ σ n G hσ hG hGu h2
  obtain ⟨c, hc⟩ := h2.exists_right_inv
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g hg hP
    have hSP : (1 - g) * (1 + g)⁻¹ * (1 + g) = 1 - g := by
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hP, Matrix.mul_one]
    refine ⟨?_, ?_⟩
    · apply eq_zero_of_mul_mul_eq_zero_of_isUnit_det ((1 + g)ᵀ) ((1 + g).map σ) _
        (by rwa [Matrix.det_transpose]) (isUnit_det_map_of_isUnit_det σ _ hP)
      have e1 : (1 + g)ᵀ * ((1 - g) * (1 + g)⁻¹)ᵀ = (1 - g)ᵀ := by
        rw [← Matrix.transpose_mul, hSP]
      have e2 : ((1 - g) * (1 + g)⁻¹).map σ * (1 + g).map σ = (1 - g).map σ := by
        rw [← Matrix.map_mul, hSP]
      have e3 : (1 - gᵀ) * G * (1 + g.map σ) + (1 + gᵀ) * G * (1 - g.map σ)
          = (G - gᵀ * G * g.map σ) + (G - gᵀ * G * g.map σ) := by noncomm_ring
      calc (1 + g)ᵀ * (((1 - g) * (1 + g)⁻¹)ᵀ * G + G * ((1 - g) * (1 + g)⁻¹).map σ)
            * (1 + g).map σ
          = ((1 + g)ᵀ * ((1 - g) * (1 + g)⁻¹)ᵀ) * G * (1 + g).map σ
            + (1 + g)ᵀ * G * (((1 - g) * (1 + g)⁻¹).map σ * (1 + g).map σ) := by
            simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
        _ = (1 - g)ᵀ * G * (1 + g).map σ + (1 + g)ᵀ * G * (1 - g).map σ := by rw [e1, e2]
        _ = 0 := by
            rw [Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_one,
              map_one_add, map_one_sub, e3, hg, sub_self, add_zero]
    · rw [one_add_cayley g hP, Matrix.det_smul]
      exact (h2.pow _).mul (Matrix.isUnit_nonsing_inv_det _ hP)
  · intro g hP
    have hinv : (1 + (1 - g) * (1 + g)⁻¹)⁻¹ = c • (1 + g) :=
      Matrix.inv_eq_right_inv (one_add_cayley_mul g hP c hc)
    rw [hinv, one_sub_cayley g hP, smul_mul_smul_comm, hc, one_smul, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hP, Matrix.mul_one]
  · intro S hS hP
    have hgP : (1 - S) * (1 + S)⁻¹ * (1 + S) = 1 - S := by
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hP, Matrix.mul_one]
    rw [← sub_eq_zero]
    apply eq_zero_of_mul_mul_eq_zero_of_isUnit_det ((1 + S)ᵀ) ((1 + S).map σ) _
      (by rwa [Matrix.det_transpose]) (isUnit_det_map_of_isUnit_det σ _ hP)
    have e1 : (1 + S)ᵀ * ((1 - S) * (1 + S)⁻¹)ᵀ = (1 - S)ᵀ := by
      rw [← Matrix.transpose_mul, hgP]
    have e2 : ((1 - S) * (1 + S)⁻¹).map σ * (1 + S).map σ = (1 - S).map σ := by
      rw [← Matrix.map_mul, hgP]
    have e3 : (1 - Sᵀ) * G * (1 - S.map σ) - (1 + Sᵀ) * G * (1 + S.map σ)
        = -((Sᵀ * G + G * S.map σ) + (Sᵀ * G + G * S.map σ)) := by noncomm_ring
    calc (1 + S)ᵀ * (((1 - S) * (1 + S)⁻¹)ᵀ * G * ((1 - S) * (1 + S)⁻¹).map σ - G)
          * (1 + S).map σ
        = ((1 + S)ᵀ * ((1 - S) * (1 + S)⁻¹)ᵀ) * G
            * (((1 - S) * (1 + S)⁻¹).map σ * (1 + S).map σ)
          - (1 + S)ᵀ * G * (1 + S).map σ := by
          simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
      _ = (1 - S)ᵀ * G * (1 - S).map σ - (1 + S)ᵀ * G * (1 + S).map σ := by rw [e1, e2]
      _ = 0 := by
          rw [Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_one,
            map_one_add, map_one_sub, e3, hS, add_zero, neg_zero]
  · intro A
    have hGinvG : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul _ hGu
    have hKG : ((G⁻¹).map σ)ᵀ * G = 1 := by
      calc ((G⁻¹).map σ)ᵀ * G = ((G⁻¹).map σ)ᵀ * (G.map σ)ᵀ := by rw [hG]
        _ = (G.map σ * (G⁻¹).map σ)ᵀ := (Matrix.transpose_mul _ _).symm
        _ = 1 := by rw [map_mul_map_inv σ G hGu, Matrix.transpose_one]
    have hGK : G * ((G⁻¹).map σ)ᵀ = 1 := by
      rw [← Matrix.inv_eq_left_inv hKG]
      exact Matrix.mul_nonsing_inv _ hGu
    have hAA : (A.map σ).map σ = A := by
      ext i j
      simp [hσ]
    have hT : (A - (G * A.map σ * G⁻¹)ᵀ)ᵀ = Aᵀ - G * A.map σ * G⁻¹ := by
      rw [Matrix.transpose_sub, Matrix.transpose_transpose]
    have hTs : (A - (G * A.map σ * G⁻¹)ᵀ).map σ
        = A.map σ - ((G⁻¹).map σ)ᵀ * (Aᵀ * G) := by
      rw [Matrix.map_sub σ (map_sub σ), Matrix.transpose_map, Matrix.map_mul, Matrix.map_mul,
        hAA, Matrix.transpose_mul, Matrix.transpose_mul, hG]
    rw [hT, hTs]
    calc (Aᵀ - G * A.map σ * G⁻¹) * G + G * (A.map σ - ((G⁻¹).map σ)ᵀ * (Aᵀ * G))
        = Aᵀ * G - G * A.map σ * (G⁻¹ * G)
          + (G * A.map σ - (G * ((G⁻¹).map σ)ᵀ) * (Aᵀ * G)) := by
          simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
      _ = 0 := by
          rw [hGinvG, hGK, Matrix.mul_one, Matrix.one_mul]
          abel

end GlobalTheory.CayleyInv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CayleyTransformUnitarySkewInvolutiveStatement
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cayleyTransform_unitary_skew_involutive : ∀ (R : Type) [CommRing R] (σ : R →+* R) (n : ℕ) (G : Matrix (Fin n) (Fin n) R), (∀ x, σ (σ x) = x) → (G.map σ)ᵀ = G → IsUnit G.det → IsUnit (2 : R) → (∀ g : Matrix (Fin n) (Fin n) R, gᵀ * G * g.map σ = G → IsUnit (1 + g).det → ((1 - g) * (1 + g)⁻¹)ᵀ * G + G * ((1 - g) * (1 + g)⁻¹).map σ = 0 ∧ IsUnit (1 + (1 - g) * (1 + g)⁻¹ : Matrix (Fin n) (Fin n) R).det) ∧ (∀ g : Matrix (Fin n) (Fin n) R, IsUnit (1 + g).det → (1 - (1 - g) * (1 + g)⁻¹) * (1 + (1 - g) * (1 + g)⁻¹)⁻¹ = g) ∧ (∀ S : Matrix (Fin n) (Fin n) R, Sᵀ * G + G * S.map σ = 0 → IsUnit (1 + S).det → ((1 - S) * (1 + S)⁻¹)ᵀ * G * ((1 - S) * (1 + S)⁻¹).map σ = G) ∧ ∀ A : Matrix (Fin n) (Fin n) R, (A - (G * A.map σ * G⁻¹)ᵀ)ᵀ * G + G * (A - (G * A.map σ * G⁻¹)ᵀ).map σ = 0 := by
  first | exact @GlobalTheory.CayleyInv.cayley_transform | exact GlobalTheory.CayleyInv.cayley_transform | (intros; apply GlobalTheory.CayleyInv.cayley_transform <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinrankSUnitsNumberFieldAddOne
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinrankSUnitsNumberFieldAddOne
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

noncomputable section

namespace GlobalTheory.QNorm

theorem exists_mem_only (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ a : 𝓞 F, a ≠ 0 ∧ a ∈ v.asIdeal ∧
      ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → a ∉ w.asIdeal := by
  classical
  have hv : v.asIdeal ∈ nonZeroDivisors (Ideal (𝓞 F)) :=
    mem_nonZeroDivisors_of_ne_zero v.ne_bot
  set h := Fintype.card (ClassGroup (𝓞 F)) with hh
  have hpos : h ≠ 0 := Fintype.card_ne_zero
  have h1 : ClassGroup.mk0 ⟨v.asIdeal ^ h, pow_mem hv h⟩ = 1 := by
    have : (⟨v.asIdeal ^ h, pow_mem hv h⟩ : nonZeroDivisors (Ideal (𝓞 F))) =
        ⟨v.asIdeal, hv⟩ ^ h := rfl
    rw [this, map_pow, pow_card_eq_one]
  obtain ⟨a, ha⟩ := (ClassGroup.mk0_eq_one_iff _).1 h1
  have ha' : v.asIdeal ^ h = Ideal.span {a} := ha
  refine ⟨a, ?_, ?_, ?_⟩
  · rintro rfl
    have : v.asIdeal ^ h = ⊥ := by rw [ha']; simp
    exact pow_ne_zero h v.ne_bot this
  · exact Ideal.pow_le_self hpos (ha' ▸ Ideal.mem_span_singleton_self a)
  · intro w hw haw
    have hle : v.asIdeal ^ h ≤ w.asIdeal := by
      rw [ha']; exact (Ideal.span_singleton_le_iff_mem _).2 haw
    have := w.isPrime
    have h2 : v.asIdeal ≤ w.asIdeal := Ideal.IsPrime.le_of_pow_le hle
    exact hw (HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top h2).symm)

theorem sUnits_rank :
    ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))),
      Module.finrank ℤ (Additive (sUnits F S)) + 1 = S.card + Fintype.card (InfinitePlace F) := by
  intro F _ _ S
  classical
  have hunit : ∀ (u : (𝓞 F)ˣ) (v : HeightOneSpectrum (𝓞 F)),
      v.valuation F (algebraMap (𝓞 F) F u) = 1 := by
    intro u v
    rw [HeightOneSpectrum.valuation_eq_one_iff_notMem]
    intro hu
    exact v.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hu u.isUnit)
  let f0 : (𝓞 F)ˣ →* sUnits F S :=
    (Units.map (algebraMap (𝓞 F) F).toMonoidHom).codRestrict _
      (fun u => (mem_sUnits F S _).2 fun v _ => hunit u v)
  let f : Additive (𝓞 F)ˣ →ₗ[ℤ] Additive (sUnits F S) :=
    (MonoidHom.toAdditive f0).toIntLinearMap
  let g0 : Additive (sUnits F S) →+ (S → ℤ) :=
    AddMonoidHom.mk' (fun x v => WithZero.log
      ((v : HeightOneSpectrum (𝓞 F)).valuation F (((Additive.toMul x : sUnits F S) : Fˣ) : F))) (by
      intro a b
      funext v
      simp only [toMul_add, Subgroup.coe_mul, Units.val_mul, map_mul, Pi.add_apply]
      exact WithZero.log_mul (by simp) (by simp))
  let g := g0.toIntLinearMap
  have hker : LinearMap.ker g = LinearMap.range f := by
    apply le_antisymm
    · intro x hx
      set y : Fˣ := ((Additive.toMul x : sUnits F S) : Fˣ) with hy
      have hall : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F (y : F) = 1 := by
        intro v
        by_cases hv : v ∈ S
        · have h : WithZero.log (v.valuation F (y : F)) = 0 :=
            congrFun (LinearMap.mem_ker.1 hx) ⟨v, hv⟩
          have hne : v.valuation F (y : F) ≠ 0 := by simp
          rw [← WithZero.exp_log hne, h, WithZero.exp_zero]
        · exact (mem_sUnits F S _).1 (Additive.toMul x).2 v hv
      obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F (y : F)
        (fun v => (hall v).le)
      obtain ⟨b, hb⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F (y : F)⁻¹
        (fun v => by rw [map_inv₀, hall v, inv_one])
      have hab : a * b = 1 := by
        apply IsFractionRing.injective (𝓞 F) F
        rw [map_mul, ha, hb, map_one, mul_inv_cancel₀ y.ne_zero]
      refine ⟨Additive.ofMul (Units.mkOfMulEqOne a b hab), ?_⟩
      apply Additive.toMul.injective
      apply Subtype.ext
      apply Units.ext
      exact ha
    · rintro _ ⟨u, rfl⟩
      rw [LinearMap.mem_ker]
      funext v
      change WithZero.log ((v : HeightOneSpectrum (𝓞 F)).valuation F
        (algebraMap (𝓞 F) F (Additive.toMul u : (𝓞 F)ˣ))) = 0
      rw [hunit, WithZero.log_one]
  have hinj : Function.Injective f := by
    intro a b hab
    apply Additive.toMul.injective
    apply Units.ext
    apply IsFractionRing.injective (𝓞 F) F
    exact congrArg (fun x : Additive (sUnits F S) => (((Additive.toMul x : sUnits F S) : Fˣ) : F)) hab
  have hfin : Module.Finite ℤ (Additive (sUnits F S)) :=
    Module.Finite.iff_addGroup_fg.2 (GroupFG.iff_add_fg.1 (sUnits_fg F S))
  have hrange : Module.finrank ℤ (LinearMap.range g) = S.card := by
    apply le_antisymm
    · refine (Submodule.finrank_le _).trans ?_
      simp
    · have key : ∀ v : S, ∃ c : ℤ, c ≠ 0 ∧ Pi.single v c ∈ LinearMap.range g := by
        intro v
        obtain ⟨a, ha0, hav, haw⟩ := exists_mem_only F v
        have ha0' : algebraMap (𝓞 F) F a ≠ 0 := by simpa using ha0
        have hw : ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v →
            w.valuation F (algebraMap (𝓞 F) F a) = 1 := fun w hw =>
          (HeightOneSpectrum.valuation_eq_one_iff_notMem w).2 (haw w hw)
        refine ⟨WithZero.log ((v : HeightOneSpectrum (𝓞 F)).valuation F (algebraMap (𝓞 F) F a)),
          ?_, Additive.ofMul ⟨Units.mk0 _ ha0', (mem_sUnits F S _).2 fun w hwS =>
            hw w (fun e => hwS (e ▸ v.2))⟩, ?_⟩
        · intro h0
          have hne : (v : HeightOneSpectrum (𝓞 F)).valuation F (algebraMap (𝓞 F) F a) ≠ 0 := by
            simpa using ha0
          have h1 : (v : HeightOneSpectrum (𝓞 F)).valuation F (algebraMap (𝓞 F) F a) = 1 := by
            rw [← WithZero.exp_log hne, h0, WithZero.exp_zero]
          exact (HeightOneSpectrum.valuation_eq_one_iff_notMem _).1 h1 hav
        · funext w
          change WithZero.log ((w : HeightOneSpectrum (𝓞 F)).valuation F
            (algebraMap (𝓞 F) F a)) = _
          by_cases hwv : w = v
          · subst hwv; simp
          · rw [Pi.single_eq_of_ne hwv, hw w (fun e => hwv (Subtype.ext e)), WithZero.log_one]
      choose c hc0 hc using key
      have hli : LinearIndependent ℤ (fun v : S => (⟨Pi.single v (c v), hc v⟩ : LinearMap.range g)) :=
        LinearIndependent.of_comp (LinearMap.range g).subtype
          (Pi.linearIndependent_single_of_ne_zero hc0)
      simpa using hli.fintype_card_le_finrank
  have h1 := Submodule.finrank_quotient_add_finrank (LinearMap.ker g)
  rw [g.quotKerEquivRange.finrank_eq, hrange, hker, LinearMap.finrank_range_of_inj hinj,
    NumberField.Units.finrank_eq, NumberField.Units.rank] at h1
  have h2 : 0 < Fintype.card (InfinitePlace F) := Fintype.card_pos
  omega

end GlobalTheory.QNorm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinrankSUnitsNumberFieldAddOneStatement
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_sUnitsNumberField_add_one : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))), Module.finrank ℤ (Additive (sUnits F S)) + 1 = S.card + Fintype.card (InfinitePlace F) := by
  first | exact @GlobalTheory.QNorm.sUnits_rank | exact GlobalTheory.QNorm.sUnits_rank | (intros; apply GlobalTheory.QNorm.sUnits_rank <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryTransvectionSubmonoidAdjustIntegralAway
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsTraceZeroAdjustmentOfHermitianLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsNsmulMulVecMem
namespace GlobalTheory.IntegralMultipleClearDenominators

open NumberField

theorem exists_nat_mul_integral {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ K : ℕ, 0 < K ∧ IsIntegral ℤ ((K : E) * c) := by
  have h : IsAlgebraic ℤ c :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic c)
  obtain ⟨y, hy, hint⟩ := h.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy, ?_⟩
  rw [zsmul_eq_mul] at hint
  rcases Int.natAbs_eq y with h1 | h1
  · have : ((y.natAbs : ℕ) : E) = (y : E) := by
      conv_rhs => rw [h1]
      exact (Int.cast_natCast _).symm
    rw [this]; exact hint
  · have : ((y.natAbs : ℕ) : E) = -(y : E) := by
      conv_rhs => rw [h1]
      rw [Int.cast_neg, neg_neg]
      exact (Int.cast_natCast _).symm
    rw [this, neg_mul]; exact hint.neg

theorem exists_nsmul_mem {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (RingOfIntegers E) (Fin n → E))
    (hL : Submodule.span E (↑L : Set (Fin n → E)) = ⊤) (w : Fin n → E) :
    ∃ N : ℕ, 0 < N ∧ N • w ∈ L := by
  have hw : w ∈ Submodule.span E (↑L : Set (Fin n → E)) := by rw [hL]; trivial
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hxa⟩ := hx
    obtain ⟨b, hb, hyb⟩ := hy
    refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact nsmul_mem hxa b
    · rw [mul_smul]; exact nsmul_mem hyb a
  | smul c x _ hx =>
    obtain ⟨a, ha, hxa⟩ := hx
    obtain ⟨K, hK, hint⟩ := exists_nat_mul_integral c
    refine ⟨K * a, Nat.mul_pos hK ha, ?_⟩
    have h := L.smul_mem (⟨(K : E) * c, hint⟩ : RingOfIntegers E) hxa
    convert h using 1
    ext i
    change _ = ((K : E) * c) * (a • x i)
    simp only [Pi.smul_apply, nsmul_eq_mul, smul_eq_mul]
    push_cast
    ring

theorem exists_nsmul_mulVec_mem {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (RingOfIntegers E) (Fin n → E)) (hfg : L.FG)
    (hL : Submodule.span E (↑L : Set (Fin n → E)) = ⊤) (M : Matrix (Fin n) (Fin n) E) :
    ∃ N : ℕ, 0 < N ∧ ∀ v ∈ L, N • Matrix.mulVec M v ∈ L := by
  obtain ⟨s, hs⟩ := hfg
  choose f hf0 hf using exists_nsmul_mem L hL
  refine ⟨∏ x ∈ s, f (M.mulVec x), Finset.prod_pos fun x _ => hf0 _, ?_⟩
  intro v hv
  rw [← hs] at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun x => f (M.mulVec x)) (Finset.mem_coe.1 hx)
    rw [hk, mul_comm, mul_smul]
    exact nsmul_mem (hf _) k
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Matrix.mulVec_add, smul_add]
    exact L.add_mem hx hy
  | smul c x _ hx =>
    rw [Matrix.mulVec_smul, smul_comm]
    exact L.smul_mem c hx

end GlobalTheory.IntegralMultipleClearDenominators
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsTraceZeroAdjustmentOfHermitianLattice
open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct

namespace GlobalTheory.TvAdjust

theorem exists_split (b : ℕ) (N : ℕ) (hN : 0 < N) :
    ∃ A B e : ℕ, N = A * B ∧ A ∣ b ^ e ∧ B.Coprime b := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    by_cases hg : N.Coprime b
    · exact ⟨1, N, 0, by simp, by simp, hg⟩
    · obtain ⟨M, hM⟩ := Nat.gcd_dvd_left N b
      have hg0 : 0 < N.gcd b := Nat.gcd_pos_of_pos_left _ hN
      have hg1 : 1 < N.gcd b := by
        rcases Nat.lt_or_ge 1 (N.gcd b) with h | h
        · exact h
        · exact absurd (show N.gcd b = 1 by omega) hg
      have hM0 : 0 < M := Nat.pos_of_ne_zero (by rintro rfl; omega)
      have hlt : M < N := by nlinarith
      obtain ⟨A, B, e, h1, h2, h3⟩ := ih M hlt hM0
      refine ⟨N.gcd b * A, B, e + 1, by rw [mul_assoc, ← h1]; exact hM, ?_, h3⟩
      rw [pow_succ']
      exact mul_dvd_mul (Nat.gcd_dvd_right N b) h2

theorem exists_nsmul_mulVec_mem {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG)
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (M : Matrix (Fin n) (Fin n) E) :
    ∃ N : ℕ, 0 < N ∧ ∀ v ∈ L, N • (M *ᵥ v) ∈ L := by
  first
  | exact @_root_.GlobalTheory.IntegralMultipleClearDenominators.exists_nsmul_mulVec_mem
  | exact _root_.GlobalTheory.IntegralMultipleClearDenominators.exists_nsmul_mulVec_mem
  | (apply _root_.GlobalTheory.IntegralMultipleClearDenominators.exists_nsmul_mulVec_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralMultipleClearDenominators.exists_nsmul_mulVec_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralMultipleClearDenominators.exists_nsmul_mulVec_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralMultipleClearDenominators.exists_nsmul_mulVec_mem ..)

theorem tv_mul_mulVec {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R) (G : Matrix (Fin n) (Fin n) R)
    (x v : Fin n → R) (t : R) (q : ℤ) :
    tv σ G x (q * t) *ᵥ v = v + q • ((tv σ G x t - 1) *ᵥ v) := by
  have : tv σ G x (q * t) = 1 + q • (tv σ G x t - 1) := by
    ext a b
    simp [tv, mul_assoc]
  rw [this, add_mulVec, one_mulVec, smul_mulVec]

theorem exists_tv_adjust : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), Module.finrank F E = 2 → IsHerm (c : E →+* E) G → ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ (x : Fin n → E) (t : E) (b : ℕ), 0 < b → t + c t = 0 → ∃ (t' : E) (k e : ℕ), t' + c t' = 0 ∧ k.Coprime b ∧ ∀ v ∈ L, (∃ w ∈ L, k • (tv (c : E →+* E) G x t' *ᵥ v - tv (c : E →+* E) G x t *ᵥ v) = b • w) ∧ b ^ e • (tv (c : E →+* E) G x t' *ᵥ v) ∈ L ∧ b ^ e • (tv (c : E →+* E) G x (-t') *ᵥ v) ∈ L := by
  intro F E _ _ _ _ _ c n G _ _ L hfg hL x t b _ ht
  obtain ⟨N, hN0, hN⟩ := exists_nsmul_mulVec_mem L hfg hL (tv (c : E →+* E) G x t - 1)
  obtain ⟨A, B, e, hAB, ⟨r, hr⟩, hB⟩ := exists_split b N hN0
  have hBA : B.Coprime (b * A) := by
    refine Nat.Coprime.mul_right hB ?_
    exact Nat.Coprime.coprime_dvd_right ⟨r, hr⟩ (hB.pow_right e)
  obtain ⟨u, w, huw⟩ := Nat.isCoprime_iff_coprime.mpr hBA
  push_cast at huw
  refine ⟨((u * B : ℤ) : E) * t, B, e, ?_, hB, fun v hv => ?_⟩
  · rw [map_mul, map_intCast, ← mul_add, ht, mul_zero]
  have hz := hN v hv
  have h1 : tv (c : E →+* E) G x t *ᵥ v = v + (tv (c : E →+* E) G x t - 1) *ᵥ v := by
    rw [sub_mulVec, one_mulVec]; abel
  have key : ∀ s : ℤ, b ^ e • (tv (c : E →+* E) G x (((s * B : ℤ) : E) * t) *ᵥ v) ∈ L := by
    intro s
    rw [tv_mul_mulVec, smul_add]
    refine L.add_mem (nsmul_mem hv _) ?_
    have := zsmul_mem hz (s * r)
    convert this using 1
    rw [hr, hAB, ← natCast_zsmul, ← natCast_zsmul, smul_smul, smul_smul]
    congr 1
    push_cast
    ring
  refine ⟨⟨(-w) • N • ((tv (c : E →+* E) G x t - 1) *ᵥ v), zsmul_mem hz _, ?_⟩, key u, ?_⟩
  · rw [tv_mul_mulVec]
    generalize tv (c : E →+* E) G x t *ᵥ v = y at h1 ⊢
    generalize (tv (c : E →+* E) G x t - 1) *ᵥ v = z at h1 ⊢
    subst h1
    have : v + (u * B) • z - (v + z) = (u * B - 1) • z := by
      rw [sub_smul, one_smul]; abel
    rw [this, hAB, ← natCast_zsmul, ← natCast_zsmul, ← natCast_zsmul, smul_smul, smul_smul,
      smul_smul]
    congr 1
    push_cast
    linear_combination (B : ℤ) * huw
  · have := key (-u)
    convert this using 4
    push_cast
    ring

end GlobalTheory.TvAdjust
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsTraceZeroAdjustmentOfHermitianLatticeStatement
open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_traceZero_adjustment_of_hermitian_lattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), Module.finrank F E = 2 → IsHerm (c : E →+* E) G → ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ (x : Fin n → E) (t : E) (b : ℕ), 0 < b → t + c t = 0 → ∃ (t' : E) (k e : ℕ), t' + c t' = 0 ∧ k.Coprime b ∧ ∀ v ∈ L, (∃ w ∈ L, k • (tv (c : E →+* E) G x t' *ᵥ v - tv (c : E →+* E) G x t *ᵥ v) = b • w) ∧ b ^ e • (tv (c : E →+* E) G x t' *ᵥ v) ∈ L ∧ b ^ e • (tv (c : E →+* E) G x (-t') *ᵥ v) ∈ L := by
  first | exact @GlobalTheory.TvAdjust.exists_tv_adjust | exact GlobalTheory.TvAdjust.exists_tv_adjust | (intros; apply GlobalTheory.TvAdjust.exists_tv_adjust <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryTransvectionSubmonoidAdjustIntegralAway
open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct

namespace GlobalTheory.UTrans

theorem tvGen_adjust : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), Module.finrank F E = 2 → IsHerm (c : E →+* E) G → ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ m ∈ TvGen (c : E →+* E) G, ∀ b : ℕ, 0 < b → ∀ N : ℕ, ∃ m' ∈ TvGen (c : E →+* E) G, ∃ k e : ℕ, k.Coprime b ∧ ∀ v ∈ L, (∃ w ∈ L, k • (m' *ᵥ v - m *ᵥ v) = b ^ N • w) ∧ b ^ e • (m' *ᵥ v) ∈ L ∧ b ^ e • (m'⁻¹ *ᵥ v) ∈ L := by
  intro F E _ _ _ _ _ c n G hFE hG L hL hsp m hm b hb
  induction hm using Submonoid.closure_induction with
  | mem m hm =>
    intro N
    obtain ⟨x, t, hx, ht, rfl⟩ := hm
    obtain ⟨t', k, e, ht', hk, H⟩ := GlobalTheory.T.exists_traceZero_adjustment_of_hermitian_lattice F E c n G hFE hG L hL hsp x t (b ^ (N + 1)) (by positivity) ht
    have hinv : (tv (c : E →+* E) G x t')⁻¹ = tv (c : E →+* E) G x (-t') := by
      apply Matrix.inv_eq_right_inv
      rw [(GlobalTheory.T.transvection_identities_unitary E n (c : E →+* E) G hG.invol hG.herm).2.2.1, hx]
      ext i j
      simp [tv]
    refine ⟨_, Submonoid.subset_closure ⟨x, t', hx, ht', rfl⟩, k, (N + 1) * e,
      (Nat.coprime_pow_right_iff (Nat.succ_pos N) _ _).1 hk, fun v hv => ?_⟩
    obtain ⟨⟨w, hw, h1⟩, h2, h3⟩ := H v hv
    refine ⟨⟨b • w, L.smul_of_tower_mem _ hw, ?_⟩, ?_, ?_⟩
    · rw [h1, smul_smul, pow_succ]
    · rwa [pow_mul]
    · rwa [pow_mul, hinv]
  | one =>
    intro N
    refine ⟨1, one_mem _, 1, 0, by simp, fun v hv => ⟨⟨0, zero_mem _, by simp⟩, ?_, ?_⟩⟩ <;> simpa using hv
  | mul m₁ m₂ _ _ ih₁ ih₂ =>
    intro N
    obtain ⟨p, -, k₀, e₀, hk₀, H₀⟩ := ih₁ 0
    have hden : ∀ v ∈ L, (k₀ * b ^ e₀) • (m₁ *ᵥ v) ∈ L := by
      intro v hv
      obtain ⟨⟨w, hw, h1⟩, h2, -⟩ := H₀ v hv
      have : (k₀ * b ^ e₀) • (m₁ *ᵥ v) = k₀ • b ^ e₀ • (p *ᵥ v) - b ^ e₀ • (b ^ 0 • w) := by
        rw [← h1]; module
      rw [this]
      exact sub_mem (L.smul_of_tower_mem _ h2) (L.smul_of_tower_mem _ (L.smul_of_tower_mem _ hw))
    obtain ⟨q₂, hq₂, k₂, e₂, hk₂, H₂⟩ := ih₂ (N + e₀)
    obtain ⟨q₁, hq₁, k₁, e₁, hk₁, H₁⟩ := ih₁ (N + e₂)
    refine ⟨q₁ * q₂, mul_mem hq₁ hq₂, k₀ * k₁ * k₂, e₁ + e₂,
      Nat.Coprime.mul_left (Nat.Coprime.mul_left hk₀ hk₁) hk₂, fun v hv => ⟨?_, ?_, ?_⟩⟩
    · obtain ⟨⟨w₂, hw₂, a1⟩, a2, -⟩ := H₂ v hv
      obtain ⟨⟨w₁, hw₁, b1⟩, -, -⟩ := H₁ _ a2
      have hb' : ((b : E) ^ e₂) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hb.ne')
      have b2 : k₁ • (q₁ *ᵥ (q₂ *ᵥ v) - m₁ *ᵥ (q₂ *ᵥ v)) = b ^ N • w₁ := by
        apply smul_right_injective (Fin n → E) hb'
        simp only [Matrix.mulVec_smul] at b1
        linear_combination (norm := module) b1
      have a3 : k₂ • (m₁ *ᵥ (q₂ *ᵥ v) - m₁ *ᵥ (m₂ *ᵥ v)) = b ^ (N + e₀) • (m₁ *ᵥ w₂) := by
        rw [← Matrix.mulVec_smul, ← a1, Matrix.mulVec_smul, Matrix.mulVec_sub]
      refine ⟨(k₀ * k₂) • w₁ + k₁ • (k₀ * b ^ e₀) • (m₁ *ᵥ w₂),
        add_mem (L.smul_of_tower_mem _ hw₁) (L.smul_of_tower_mem _ (hden _ hw₂)), ?_⟩
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      linear_combination (norm := module) (k₀ * k₂) • b2 + (k₀ * k₁) • a3
    · have := (H₁ _ (H₂ v hv).2.1).2.1
      rwa [Matrix.mulVec_smul, smul_smul, ← pow_add, Matrix.mulVec_mulVec] at this
    · have := (H₂ _ (H₁ v hv).2.2).2.2
      rwa [Matrix.mulVec_smul, smul_smul, ← pow_add, Matrix.mulVec_mulVec, ← Matrix.mul_inv_rev, add_comm] at this

end GlobalTheory.UTrans
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryTransvectionSubmonoidAdjustIntegralAwayStatement
open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryTransvectionSubmonoid_adjust_integral_away : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), Module.finrank F E = 2 → IsHerm (c : E →+* E) G → ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ m ∈ TvGen (c : E →+* E) G, ∀ b : ℕ, 0 < b → ∀ N : ℕ, ∃ m' ∈ TvGen (c : E →+* E) G, ∃ k e : ℕ, k.Coprime b ∧ ∀ v ∈ L, (∃ w ∈ L, k • (m' *ᵥ v - m *ᵥ v) = b ^ N • w) ∧ b ^ e • (m' *ᵥ v) ∈ L ∧ b ^ e • (m'⁻¹ *ᵥ v) ∈ L := by
  first | exact @GlobalTheory.UTrans.tvGen_adjust | exact GlobalTheory.UTrans.tvGen_adjust | (intros; apply GlobalTheory.UTrans.tvGen_adjust <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitsLocalKummerNormsEqTopOfPow
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUnitNormEqOfAlgHom
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem exists_unit_norm_eq_of_algHom : ∀ (K A : Type) [Field K] [CommRing A] [Algebra K A] [Module.Finite K A] [IsReduced A] (ψ : A →ₐ[K] K) (c : K), c ≠ 0 → ∃ y : Aˣ, Algebra.norm K (y : A) = c := by
  intro K A _ _ _ _ _ ψ c hc
  have : IsArtinianRing A := IsArtinianRing.of_finite K A
  have : IsSemisimpleRing A := IsArtinianRing.isSemisimpleRing_of_isReduced A
  obtain ⟨e, he, hI⟩ := IsSemisimpleRing.ideal_eq_span_idempotent (RingHom.ker ψ)
  have he0 : ψ e = 0 := by
    have : e ∈ RingHom.ker ψ := by rw [hI]; exact Ideal.subset_span rfl
    exact this
  set f : A := 1 - e with hf
  have hψf : ψ f = 1 := by simp [hf, he0]
  have hmul : ∀ a : A, f * a = ψ a • f := by
    intro a
    have h1 : a - algebraMap K A (ψ a) ∈ RingHom.ker ψ := by
      simp [RingHom.mem_ker]
    rw [hI, Ideal.mem_span_singleton'] at h1
    obtain ⟨b, hb⟩ := h1
    have h2 : f * (b * e) = 0 := by
      have : e * e = e := he
      rw [hf]; linear_combination (-b) * this
    rw [hb, mul_sub, sub_eq_zero] at h2
    rw [h2, Algebra.smul_def, mul_comm]
  have hff : f * f = f := by rw [hmul, hψf, one_smul]
  have hinv : (1 + (c - 1) • f) * (1 + (c⁻¹ - 1) • f) = 1 := by
    have : (c⁻¹ - 1) + (c - 1) + (c - 1) * (c⁻¹ - 1) = 0 := by field_simp; ring
    rw [mul_add, add_mul, add_mul, smul_mul_smul_comm, hff]
    simp only [one_mul, mul_one]
    rw [add_assoc, ← add_smul, ← add_smul]
    have h3 : c - 1 + (c⁻¹ - 1 + (c - 1) * (c⁻¹ - 1)) = 0 := by linear_combination this
    rw [h3]; simp
  refine ⟨⟨1 + (c - 1) • f, 1 + (c⁻¹ - 1) • f, hinv, by rw [mul_comm, hinv]⟩, ?_⟩
  rw [Algebra.norm_apply]
  have hT : LinearMap.mul K A (1 + (c - 1) • f) = LinearMap.transvection ψ.toLinearMap ((c - 1) • f) := by
    ext a
    simp [LinearMap.transvection.apply, hmul, smul_smul, mul_comm]
  change LinearMap.det (LinearMap.mul K A (1 + (c - 1) • f)) = c
  rw [hT, LinearMap.transvection.det]
  simp [hψf]

end GlobalTheory.CNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitsLocalKummerNormsEqTopOfPow
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem kNorm_eq_top_of_pow : ∀ (p : ℕ) (F L : Type) [Field F] [Field L] [CharZero L] (φ : F →+* L) (δ : F) (r : L), 0 < p → δ ≠ 0 → r ^ p = φ δ → kNorm p φ δ = ⊤ := by
  intro p F L _ _ _ φ δ r hp hδ hr
  have hφ : φ δ ≠ 0 := (map_ne_zero φ).2 hδ
  have hsep : (X ^ p - C (φ δ) : L[X]).Separable :=
    separable_X_pow_sub_C (φ δ) (Nat.cast_ne_zero.2 hp.ne') hφ
  have hm : (X ^ p - C (φ δ) : L[X]).Monic := monic_X_pow_sub_C _ hp.ne'
  have : IsReduced (AdjoinRoot (X ^ p - C (φ δ) : L[X])) :=
    (Ideal.isRadical_iff_quotient_reduced _).1
      (isRadical_iff_span_singleton.1 hsep.squarefree.isRadical)
  have : Module.Finite L (AdjoinRoot (X ^ p - C (φ δ) : L[X])) :=
    (AdjoinRoot.powerBasis' hm).finite
  let ψ : AdjoinRoot (X ^ p - C (φ δ) : L[X]) →ₐ[L] L :=
    AdjoinRoot.liftAlgHom _ (AlgHom.id L L) r (by simp [hr])
  rw [eq_top_iff]
  intro x _
  rw [mem_kNorm]
  exact GlobalTheory.CNorm.exists_unit_norm_eq_of_algHom L _ ψ (φ (x : F)) ((map_ne_zero φ).2 x.ne_zero)

end GlobalTheory.CNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitsLocalKummerNormsEqTopOfPowStatement
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitsLocalKummerNorms_eq_top_of_pow : ∀ (p : ℕ) (F L : Type) [Field F] [Field L] [CharZero L] (φ : F →+* L) (δ : F) (r : L), 0 < p → δ ≠ 0 → r ^ p = φ δ → kNorm p φ δ = ⊤ := by
  first | exact @GlobalTheory.CNorm.kNorm_eq_top_of_pow | exact GlobalTheory.CNorm.kNorm_eq_top_of_pow | (intros; apply GlobalTheory.CNorm.kNorm_eq_top_of_pow <;> assumption)
end
end
