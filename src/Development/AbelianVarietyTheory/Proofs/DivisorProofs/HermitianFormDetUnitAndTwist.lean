module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PhiMulSelf
noncomputable def UpperTheory.Reformulated.B.Yzd3.Phi :
    (n : ℕ) → (R : Type) → [CommRing R] → Matrix (Fin n) (Fin n) R :=
    fun (n : ℕ) (R : Type) [CommRing R] ↦
      (Matrix.of : (Fin n → Fin n → R) → Matrix (Fin n) (Fin n) R) fun (i j : Fin n) ↦
        if (↑i : ℕ) + (↑j : ℕ) + (1 : ℕ) = n then (-1 : R) ^ (↑i : ℕ) else (0 : R)

theorem UpperTheory.Reformulated.B.Yzd3.phi_mul_self :
    ∀ (a : ℕ) {R : Type} [inst : CommRing R],
      UpperTheory.Reformulated.B.Yzd3.Phi a R * UpperTheory.Reformulated.B.Yzd3.Phi a R = (-1 : R) ^ (a - (1 : ℕ)) • (1 : Matrix (Fin a) (Fin a) R) := by
  intro a R _
  ext i k
  have hi := i.2
  have hk := k.2
  have hj : a - 1 - (i : ℕ) < a := by omega
  simp only [Matrix.mul_apply, UpperTheory.Reformulated.B.Yzd3.Phi, Matrix.of_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul]
  rw [Finset.sum_eq_single (⟨a - 1 - (i : ℕ), hj⟩ : Fin a)]
  · have h1 : (i : ℕ) + (a - 1 - (i : ℕ)) + 1 = a := by omega
    dsimp only
    rw [if_pos h1]
    by_cases hik : i = k
    · subst hik
      have h2 : (a - 1 - (i : ℕ)) + (i : ℕ) + 1 = a := by omega
      rw [if_pos h2, if_pos rfl, mul_one, ← pow_add]
      congr 1
      omega
    · have h2 : ¬ ((a - 1 - (i : ℕ)) + (k : ℕ) + 1 = a) := by
        intro h
        exact hik (Fin.ext (by omega))
      rw [if_neg h2, if_neg hik, mul_zero, mul_zero]
  · intro j _ hne
    have h1 : ¬ ((i : ℕ) + (j : ℕ) + 1 = a) := by
      intro h
      exact hne (Fin.ext (by simp only []; omega))
    rw [if_neg h1, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PhiMulTranspose
noncomputable def UpperTheory.Reformulated.B.Yzd2.Phi :
    (n : ℕ) → (R : Type) → [CommRing R] → Matrix (Fin n) (Fin n) R :=
    fun (n : ℕ) (R : Type) [CommRing R] ↦
      (Matrix.of : (Fin n → Fin n → R) → Matrix (Fin n) (Fin n) R) fun (i j : Fin n) ↦
        if (↑i : ℕ) + (↑j : ℕ) + (1 : ℕ) = n then (-1 : R) ^ (↑i : ℕ) else (0 : R)

theorem UpperTheory.Reformulated.B.Yzd2.phi_mul_transpose :
    ∀ (a : ℕ) {R : Type} [inst : CommRing R],
      UpperTheory.Reformulated.B.Yzd2.Phi a R * (UpperTheory.Reformulated.B.Yzd2.Phi a R).transpose = (1 : Matrix (Fin a) (Fin a) R) := by
  intro a R _
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, UpperTheory.Reformulated.B.Yzd2.Phi, Matrix.of_apply,
    Matrix.one_apply]
  by_cases h : i = j
  · subst h
    have hi := i.isLt
    let k : Fin a := ⟨a - 1 - (i : ℕ), by omega⟩
    have hk : (k : ℕ) = a - 1 - (i : ℕ) := rfl
    rw [Finset.sum_eq_single k]
    · have h1 : (i : ℕ) + (k : ℕ) + 1 = a := by omega
      rw [if_pos h1, if_pos rfl, ← mul_pow]
      simp
    · intro b _ hb
      have h1 : ¬ ((i : ℕ) + (b : ℕ) + 1 = a) := by
        intro h2
        apply hb
        ext
        omega
      simp [h1]
    · intro hk'
      exact absurd (Finset.mem_univ k) hk'
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro k _
    by_cases h1 : (i : ℕ) + (k : ℕ) + 1 = a
    · have h2 : ¬ ((j : ℕ) + (k : ℕ) + 1 = a) := by
        intro h2
        apply h
        ext
        omega
      simp [h2]
    · simp [h1]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SigBasisApply
namespace GlobalTheory.ScalarSigmaBasis

open GlobalTheory.UnitLemma

variable {K : UQ} (B : InvAlg K)

theorem sig_smul (r : K.E) (x : B.A) : B.σ (r • x) = K.c r • B.σ x := by
  rw [Algebra.smul_def, map_mul, B.σ_alg, ← Algebra.smul_def]

theorem sig_sum {ι : Type} (s : Finset ι) (f : ι → K.E) (v : ι → B.A) :
    B.σ (∑ i ∈ s, f i • v i) = ∑ i ∈ s, K.c (f i) • B.σ (v i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]; simp only [sig_smul]

noncomputable def sigBasis {n : ℕ} (b : Module.Basis (Fin n) K.E B.A) : Module.Basis (Fin n) K.E B.A :=
  Module.Basis.mk (v := fun i => B.σ (b i))
    (by
      rw [Fintype.linearIndependent_iff]
      intro f hf i
      have h1 : B.σ (∑ k, f k • B.σ (b k)) = 0 := by rw [hf, map_zero]
      rw [sig_sum] at h1
      simp only [B.σ_σ] at h1
      have h2 := (Fintype.linearIndependent_iff.mp b.linearIndependent) _ h1 i
      have : K.c (f i) = K.c 0 := by rw [h2, map_zero]
      exact K.c.injective this)
    (by
      intro x _
      have h := sig_sum B Finset.univ (fun k => b.repr (B.σ x) k) (fun k => b k)
      have hx : x = ∑ k, K.c (b.repr (B.σ x) k) • B.σ (b k) := by
        rw [← h, b.sum_repr, B.σ_σ]
      rw [hx]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))

theorem sigBasis_apply {n : ℕ} (b : Module.Basis (Fin n) K.E B.A) (i : Fin n) :
    sigBasis B b i = B.σ (b i) := by
  simp [sigBasis]

theorem sigBasis_repr {n : ℕ} (b : Module.Basis (Fin n) K.E B.A) (z : B.A) (k : Fin n) :
    (sigBasis B b).repr (B.σ z) k = K.c (b.repr z k) := by
  have hz : B.σ z = ∑ i, K.c (b.repr z i) • sigBasis B b i := by
    conv_lhs => rw [← b.sum_repr z]
    rw [sig_sum]
    simp only [sigBasis_apply]
  rw [hz, Module.Basis.repr_sum_self]

theorem trace_sig (y : B.A) : Algebra.trace K.E B.A (B.σ y) = K.c (Algebra.trace K.E B.A y) := by
  let b := Module.finBasis K.E B.A
  rw [Algebra.trace_eq_matrix_trace (sigBasis B b), Algebra.trace_eq_matrix_trace b]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.trace, Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sigBasis_apply, ← map_mul, sigBasis_repr]

theorem core (a : ℕ) (β : B.A) (hβ : B.σ β = β * ((-1 : B.A) ^ (a - 1) * B.g))
    (b : Module.Basis (Fin a) K.E B.A) (i j : Fin a) :
    K.c (B.herm β (b i) (b j)) = (-1 : K.E) ^ (a - 1) *
      ∑ k, B.herm β (b k) (b i) * LinearMap.toMatrix b b (LinearMap.mulLeft K.E B.g) k j := by
  have hg : B.g * b j = ∑ k, b.repr (B.g * b j) k • b k := (b.sum_repr _).symm
  have e1 : B.σ (β * b i * B.σ (b j)) =
      algebraMap K.E B.A ((-1 : K.E) ^ (a - 1)) * (β * (B.g * b j) * B.σ (b i)) := by
    rw [map_mul, map_mul, B.σ_σ, hβ]
    simp only [map_pow, map_neg, map_one]
    ring
  have e2 : β * (B.g * b j) * B.σ (b i) = ∑ k, b.repr (B.g * b j) k • (β * b k * B.σ (b i)) := by
    conv_lhs => rw [hg]
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_smul_comm, smul_mul_assoc]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [InvAlg.herm, ← trace_sig, e1, e2, ← Algebra.smul_def, LinearMap.map_smul, map_sum, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearMap.map_smul, smul_eq_mul, LinearMap.toMatrix_apply, LinearMap.mulLeft_apply, mul_comm]
  rfl

theorem main : ∀ {K : GlobalTheory.UnitLemma.UQ} (B : GlobalTheory.UnitLemma.InvAlg K) (L : Type) [inst : Field L] (e : GlobalTheory.UnitLemma.UQ.E K ≃+* L) (c : L →+* L), (∀ (x : GlobalTheory.UnitLemma.UQ.E K), (e : GlobalTheory.UnitLemma.UQ.E K → L) ((GlobalTheory.UnitLemma.UQ.c K : GlobalTheory.UnitLemma.UQ.E K → GlobalTheory.UnitLemma.UQ.E K) x) = (c : L → L) ((e : GlobalTheory.UnitLemma.UQ.E K → L) x)) → ∀ (a : ℕ) (β : GlobalTheory.UnitLemma.InvAlg.A B), (GlobalTheory.UnitLemma.InvAlg.σ B : GlobalTheory.UnitLemma.InvAlg.A B → GlobalTheory.UnitLemma.InvAlg.A B) β = β * ((-1 : GlobalTheory.UnitLemma.InvAlg.A B) ^ (a - (1 : ℕ)) * GlobalTheory.UnitLemma.InvAlg.g B) → ∀ (b : Module.Basis (Fin a) (GlobalTheory.UnitLemma.UQ.E K) (GlobalTheory.UnitLemma.InvAlg.A B)), Matrix.map (Matrix.map ((Matrix.of : (Fin a → Fin a → GlobalTheory.UnitLemma.UQ.E K) → Matrix (Fin a) (Fin a) (GlobalTheory.UnitLemma.UQ.E K)) fun (i j : Fin a) ↦ GlobalTheory.UnitLemma.InvAlg.herm B β ((b : Fin a → GlobalTheory.UnitLemma.InvAlg.A B) i) ((b : Fin a → GlobalTheory.UnitLemma.InvAlg.A B) j)) (⇑e : GlobalTheory.UnitLemma.UQ.E K → L)) (⇑c : L → L) = (-1 : L) ^ (a - (1 : ℕ)) • (Matrix.transpose (Matrix.map ((Matrix.of : (Fin a → Fin a → GlobalTheory.UnitLemma.UQ.E K) → Matrix (Fin a) (Fin a) (GlobalTheory.UnitLemma.UQ.E K)) fun (i j : Fin a) ↦ GlobalTheory.UnitLemma.InvAlg.herm B β ((b : Fin a → GlobalTheory.UnitLemma.InvAlg.A B) i) ((b : Fin a → GlobalTheory.UnitLemma.InvAlg.A B) j)) (⇑e : GlobalTheory.UnitLemma.UQ.E K → L)) * Matrix.map ((LinearMap.toMatrix b b : (GlobalTheory.UnitLemma.InvAlg.A B →ₗ[GlobalTheory.UnitLemma.UQ.E K] GlobalTheory.UnitLemma.InvAlg.A B) → Matrix (Fin a) (Fin a) (GlobalTheory.UnitLemma.UQ.E K)) (LinearMap.mulLeft (GlobalTheory.UnitLemma.UQ.E K) (GlobalTheory.UnitLemma.InvAlg.g B))) (⇑e : GlobalTheory.UnitLemma.UQ.E K → L)) := by
  intro K B L _ e c hc a β hβ b
  ext i j
  simp only [Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.transpose_apply,
    smul_eq_mul]
  rw [← hc, core B a β hβ b i j]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_mul, map_sum, map_pow, map_neg, map_one]

end GlobalTheory.ScalarSigmaBasis
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormDetUnitAndTwist
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section

namespace GlobalTheory.GramTwistNorm

open GlobalTheory.UnitLemma

theorem phi_map (a : ℕ) {R : Type} [CommRing R] (c : R →+* R) :
    (GlobalTheory.Tw.Phi a R).map c = GlobalTheory.Tw.Phi a R := by
  ext i j
  simp only [Matrix.map_apply, GlobalTheory.Tw.Phi, Matrix.of_apply]
  split_ifs <;> simp

theorem phi_mul_self (a : ℕ) {R : Type} [CommRing R] :
    GlobalTheory.Tw.Phi a R * GlobalTheory.Tw.Phi a R = ((-1 : R) ^ (a - 1)) • (1 : Matrix (Fin a) (Fin a) R) :=
  _root_.UpperTheory.Reformulated.B.Yzd3.phi_mul_self a

theorem phi_mul_transpose (a : ℕ) {R : Type} [CommRing R] :
    GlobalTheory.Tw.Phi a R * (GlobalTheory.Tw.Phi a R)ᵀ = 1 :=
  _root_.UpperTheory.Reformulated.B.Yzd2.phi_mul_transpose a

theorem herm_sum_left {K : UQ} (B : InvAlg K) (β : B.A) {ι : Type} (s : Finset ι) (v : ι → K.E)
    (x : ι → B.A) (z : B.A) :
    B.herm β (∑ i ∈ s, v i • x i) z = ∑ i ∈ s, v i * B.herm β (x i) z := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [InvAlg.herm, Finset.mul_sum, Finset.sum_mul, map_sum, mul_smul_comm, smul_mul_assoc,
    map_smul, smul_eq_mul]

theorem herm_sum_right {K : UQ} (B : InvAlg K) (β y : B.A) {ι : Type} (s : Finset ι) (r : ι → K.E)
    (x : ι → B.A) :
    B.herm β y (∑ i ∈ s, r i • x i) = ∑ i ∈ s, K.c (r i) * B.herm β y (x i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [InvAlg.herm, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def, RingEquiv.map_mul B.σ, B.σ_alg, ← Algebra.smul_def, mul_smul_comm, map_smul, smul_eq_mul]

theorem gram_det_ne_zero {K : UQ} (B : InvAlg K) (hsep : B.P.Separable) (β : B.Aˣ) {a : ℕ}
    (b : Module.Basis (Fin a) K.E B.A) :
    (Matrix.of fun i j => B.herm β (b i) (b j)).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
  set y := ∑ i, v i • b i with hy
  have hy0 : y ≠ 0 := by
    intro hy'
    apply hv0
    funext i
    exact Fintype.linearIndependent_iff.1 b.linearIndependent v hy' i
  have hyb : ∀ j, B.herm β y (b j) = 0 := by
    intro j
    have := congrFun hv j
    simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Pi.zero_apply] at this
    rw [hy, herm_sum_left]
    exact this
  have hyz : ∀ z, B.herm β y z = 0 := by
    intro z
    rw [← b.sum_repr z, herm_sum_right]
    simp [hyb]
  have hβy : (β : B.A) * y = 0 := by
    apply GlobalTheory.UnitLemma.PairClass.trace_nondeg K.E B.A B.g hsep
    intro w
    have := hyz (B.σ w)
    simp only [InvAlg.herm, B.σ_σ] at this
    exact this
  exact hy0 ((Units.mul_right_eq_zero β).1 hβy)

theorem gram_map_conj {K : UQ} (B : InvAlg K) (L : Type) [Field L] (e : K.E ≃+* L) (c : L →+* L)
    (hec : ∀ x, e (K.c x) = c (e x)) (a : ℕ) (β : B.A)
    (hβ : B.σ β = β * ((-1) ^ (a - 1) * B.g)) (b : Module.Basis (Fin a) K.E B.A) :
    ((Matrix.of fun i j => B.herm β (b i) (b j)).map e).map c =
      ((-1 : L) ^ (a - 1)) • (((Matrix.of fun i j => B.herm β (b i) (b j)).map e)ᵀ *
        (LinearMap.toMatrix b b (LinearMap.mulLeft K.E B.g)).map e) :=
  _root_.GlobalTheory.ScalarSigmaBasis.main B L e c hec a β hβ b

theorem gram_twisted_norm_charpoly : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (L : Type) [Field L] (e : K.E ≃+* L) (c : L →+* L), (∀ x, e (K.c x) = c (e x)) → (∀ x, c (c x) = x) → ∀ (a : ℕ) (Q : L[X]), B.P = Q.map e.symm.toRingHom → Q.Separable → Q.natDegree = a → ∀ β : B.Aˣ, B.σ (β : B.A) = β * ((-1) ^ (a - 1) * B.g) → ∀ b : Module.Basis (Fin a) K.E B.A, IsUnit (Matrix.of fun i j => e (B.herm β (b i) (b j))).det ∧ ∀ δ : GL (Fin a) L, ((δ.val * GlobalTheory.Tw.Phi a L)⁻¹)ᵀ = (Matrix.of fun i j => e (B.herm β (b i) (b j))) → (δ * thetaGL a c δ).val.charpoly = Q := by
  intro K B L _ e c hec hcc a Q hPQ hQs hQd β hβ b
  set S : Matrix (Fin a) (Fin a) K.E := Matrix.of fun i j => B.herm β (b i) (b j) with hS
  have hG : (Matrix.of fun i j => e (B.herm β (b i) (b j))) = S.map e := rfl
  have hsep : B.P.Separable := by rw [hPQ]; exact hQs.map
  rw [hG]
  refine ⟨?_, ?_⟩
  · have hdet : (S.map e).det = e S.det := by
      rw [show S.map e = (e : K.E →+* L).mapMatrix S from rfl, ← RingHom.map_det]
      rfl
    rw [hdet, isUnit_iff_ne_zero]
    exact (map_ne_zero e).2 (gram_det_ne_zero B hsep β b)
  · intro δ hδ
    set G := S.map e with hGdef
    set P := (LinearMap.toMatrix b b (LinearMap.mulLeft K.E B.g)).map e with hP
    set Φ := GlobalTheory.Tw.Phi a L with hΦ
    have hGc : G.map c = ((-1 : L) ^ (a - 1)) • (Gᵀ * P) := gram_map_conj B L e c hec a β hβ b
    have hinv : (δ⁻¹).val = Φ * Gᵀ := by
      have h1 : (δ.val * Φ)⁻¹ = Gᵀ := by rw [← hδ, Matrix.transpose_transpose]
      have hΦinv : Φ⁻¹ = Φᵀ := Matrix.inv_eq_right_inv (phi_mul_transpose a)
      rw [Matrix.mul_inv_rev, hΦinv, ← Matrix.coe_units_inv] at h1
      calc (δ⁻¹).val = Φ * Φᵀ * (δ⁻¹).val := by rw [hΦ, phi_mul_transpose, Matrix.one_mul]
        _ = Φ * Gᵀ := by rw [Matrix.mul_assoc, h1]
    have hθ : (thetaGL a c δ).val = Φ * ((δ⁻¹).val.map c)ᵀ * Φᵀ := rfl
    have hΦΦ : Φᵀ * Φᵀ = ((-1 : L) ^ (a - 1)) • (1 : Matrix (Fin a) (Fin a) L) := by
      rw [← Matrix.transpose_mul, hΦ, phi_mul_self, Matrix.transpose_smul, Matrix.transpose_one]
    have hδΦ : δ.val * Φ * Gᵀ = 1 := by rw [Matrix.mul_assoc, ← hinv, Units.mul_inv]
    have key : (δ * thetaGL a c δ).val = P := by
      rw [Units.val_mul, hθ, hinv, Matrix.map_mul, hΦ, phi_map, ← hΦ, Matrix.transpose_mul,
        Matrix.transpose_map, Matrix.transpose_transpose, hGc]
      calc δ.val * (Φ * ((-1 : L) ^ (a - 1) • (Gᵀ * P) * Φᵀ) * Φᵀ)
          = ((-1 : L) ^ (a - 1)) • ((δ.val * Φ * Gᵀ) * P * (Φᵀ * Φᵀ)) := by
            simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
        _ = P := by
            rw [hδΦ, hΦΦ, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, ← mul_pow,
              neg_one_mul, neg_neg, one_pow, one_smul]
    rw [key, hP, show (LinearMap.toMatrix b b (LinearMap.mulLeft K.E B.g)).map e =
      (LinearMap.toMatrix b b (LinearMap.mulLeft K.E B.g)).map (e : K.E →+* L) from rfl,
      Matrix.charpoly_map, LinearMap.charpoly_toMatrix]
    change B.P.map (e : K.E →+* L) = Q
    rw [hPQ, Polynomial.map_map]
    have : (e : K.E →+* L).comp e.symm.toRingHom = RingHom.id L := by
      ext x; simp
    rw [this, Polynomial.map_id]

end GlobalTheory.GramTwistNorm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormDetUnitAndTwistStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_form_det_unit_and_twist : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (L : Type) [Field L] (e : K.E ≃+* L) (c : L →+* L), (∀ x, e (K.c x) = c (e x)) → (∀ x, c (c x) = x) → ∀ (a : ℕ) (Q : L[X]), B.P = Q.map e.symm.toRingHom → Q.Separable → Q.natDegree = a → ∀ β : B.Aˣ, B.σ (β : B.A) = β * ((-1) ^ (a - 1) * B.g) → ∀ b : Module.Basis (Fin a) K.E B.A, IsUnit (Matrix.of fun i j => e (B.herm β (b i) (b j))).det ∧ ∀ δ : GL (Fin a) L, ((δ.val * GlobalTheory.Tw.Phi a L)⁻¹)ᵀ = (Matrix.of fun i j => e (B.herm β (b i) (b j))) → (δ * thetaGL a c δ).val.charpoly = Q := by
  first | exact @GlobalTheory.GramTwistNorm.gram_twisted_norm_charpoly | exact GlobalTheory.GramTwistNorm.gram_twisted_norm_charpoly | (intros; apply GlobalTheory.GramTwistNorm.gram_twisted_norm_charpoly <;> assumption)
end
