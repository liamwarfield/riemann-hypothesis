module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTripleTrivialOverRealsOfGramCongruent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIsIntegralInCompletedTensorBasisMulExp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjoinLocalOrderTensorPadicMatrixAlmostAll

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntVZero
noncomputable section

open IsDedekindDomain GlobalTheory.LKTrip
open scoped TensorProduct

namespace GlobalTheory.OrbFinAf

variable {p : ℕ} [Fact p.Prime]

def iotaF (G : HTGroup p) (v : AwayP p) : Qv v ⊗[ℚ] G.F →ₐ[Qv v] Qv v ⊗[ℚ] G.C :=
  Algebra.TensorProduct.map (AlgHom.id (Qv v) (Qv v)) (IsScalarTower.toAlgHom ℚ G.F G.C)

theorem iotaF_tmul (G : HTGroup p) (v : AwayP p) (a : Qv v) (x : G.F) :
    iotaF G v (a ⊗ₜ[ℚ] x) = a ⊗ₜ[ℚ] algebraMap G.F G.C x := rfl

theorem isIntV_zero (G : HTGroup p) (v : AwayP p) : IsIntV G v 0 := fun i => by
  rw [map_zero, Finsupp.zero_apply]; exact zero_mem _

theorem isIntV_add' (G : HTGroup p) (v : AwayP p) {a b : Qv v ⊗[ℚ] G.C} (ha : IsIntV G v a)
    (hb : IsIntV G v b) : IsIntV G v (a + b) := fun i => by
  rw [map_add (f := _), Finsupp.add_apply]; exact add_mem (ha i) (hb i)

theorem isIntV_neg (G : HTGroup p) (v : AwayP p) {a : Qv v ⊗[ℚ] G.C} (ha : IsIntV G v a) :
    IsIntV G v (-a) := fun i => by
  rw [map_neg, Finsupp.neg_apply]; exact neg_mem (ha i)

theorem isIntV_sum (G : HTGroup p) (v : AwayP p) {ι : Type*} (s : Finset ι) (f : ι → Qv v ⊗[ℚ] G.C)
    (h : ∀ i ∈ s, IsIntV G v (f i)) : IsIntV G v (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact isIntV_zero G v
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact isIntV_add' G v (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

def intF (G : HTGroup p) (v : AwayP p) (h1 : IsIntV G v 1)
    (hm : ∀ y z : Qv v ⊗[ℚ] G.C, IsIntV G v y → IsIntV G v z → IsIntV G v (y * z)) :
    Subring (Qv v ⊗[ℚ] G.F) where
  carrier := {m | IsIntV G v (iotaF G v m)}
  one_mem' := by simp only [Set.mem_setOf_eq, map_one]; exact h1
  mul_mem' {a b} ha hb := by simp only [Set.mem_setOf_eq, map_mul] at *; exact hm _ _ ha hb
  zero_mem' := by simp only [Set.mem_setOf_eq, map_zero]; exact isIntV_zero G v
  add_mem' {a b} ha hb := by simp only [Set.mem_setOf_eq, map_add (f := _)] at *; exact isIntV_add' G v ha hb
  neg_mem' {a} ha := by simp only [Set.mem_setOf_eq, map_neg] at *; exact isIntV_neg G v ha

theorem mem_intF (G : HTGroup p) (v : AwayP p) (h1 : IsIntV G v 1)
    (hm : ∀ y z : Qv v ⊗[ℚ] G.C, IsIntV G v y → IsIntV G v z → IsIntV G v (y * z)) (m : Qv v ⊗[ℚ] G.F) :
    m ∈ intF G v h1 hm ↔ IsIntV G v (iotaF G v m) := Iff.rfl

end GlobalTheory.OrbFinAf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixUnitsGiveMatrixAlgebraIso
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndefiniteUnitaryHaarBallLowerBound
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

namespace GlobalTheory.MatUnitIso

variable {k K B : Type} [Field k] [CommRing K] [Ring B] [Algebra k K] [Algebra k B]

def phiL {n : ℕ} (ι : K →ₐ[k] B) (E : Fin n → Fin n → B) :
    Matrix (Fin n) (Fin n) K →ₗ[k] B where
  toFun M := ∑ a, ∑ b, ι (M a b) * E a b
  map_add' M N := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' c M := by simp [Finset.smul_sum, smul_mul_assoc]

theorem phiL_apply {n : ℕ} (ι : K →ₐ[k] B) (E : Fin n → Fin n → B) (M) :
    phiL ι E M = ∑ a, ∑ b, ι (M a b) * E a b := rfl

theorem core {n : ℕ} (ι : K →ₐ[k] B) (E : Fin n → Fin n → B)
    (hc : ∀ z x, Commute (ι z) x)
    (hE : ∀ a b c d, E a b * E c d = if b = c then E a d else 0)
    (M : Matrix (Fin n) (Fin n) K) (c a d e : Fin n) :
    E c a * phiL ι E M * E d e = ι (M a d) * E c e := by
  have h : ∀ a' b', E c a * (ι (M a' b') * E a' b') * E d e
      = if a = a' then (if b' = d then ι (M a d) * E c e else 0) else 0 := by
    intro a' b'
    rw [← mul_assoc, ← (hc (M a' b') (E c a)).eq]
    simp only [mul_assoc, hE, mul_ite, mul_zero]
    split_ifs with h1 h2
    · subst h1 h2; rw [mul_assoc, hE, if_pos rfl]
    · rw [mul_assoc, hE, if_neg h2, mul_zero]
    · rw [zero_mul]
  simp only [phiL_apply, Finset.mul_sum, Finset.sum_mul, h]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem extract {n : ℕ} (ι : K →ₐ[k] B) (E : Fin n → Fin n → B)
    (hc : ∀ z x, Commute (ι z) x)
    (hE : ∀ a b c d, E a b * E c d = if b = c then E a d else 0)
    (h1 : ∑ a, E a a = 1) (M : Matrix (Fin n) (Fin n) K) (a b : Fin n) :
    ∑ c, E c a * phiL ι E M * E b c = ι (M a b) := by
  simp only [core ι E hc hE, ← Finset.mul_sum, h1, mul_one]

theorem phiL_injective {n : ℕ} (ι : K →ₐ[k] B) (E : Fin n → Fin n → B)
    (hi : Function.Injective ι) (hc : ∀ z x, Commute (ι z) x)
    (hE : ∀ a b c d, E a b * E c d = if b = c then E a d else 0)
    (h1 : ∑ a, E a a = 1) : Function.Injective (phiL ι E) := by
  intro M N h
  ext a b
  apply hi
  rw [← extract ι E hc hE h1 M a b, ← extract ι E hc hE h1 N a b, h]

theorem phiL_one {n : ℕ} (ι : K →ₐ[k] B) (E : Fin n → Fin n → B)
    (h1 : ∑ a, E a a = 1) : phiL ι E 1 = 1 := by
  simp [phiL_apply, Matrix.one_apply, h1]

theorem phiL_mul {n : ℕ} (ι : K →ₐ[k] B) (E : Fin n → Fin n → B)
    (hc : ∀ z x, Commute (ι z) x)
    (hE : ∀ a b c d, E a b * E c d = if b = c then E a d else 0)
    (M N : Matrix (Fin n) (Fin n) K) :
    phiL ι E (M * N) = phiL ι E M * phiL ι E N := by
  have h : ∀ a b c d, ι (M a b) * E a b * (ι (N c d) * E c d)
      = if b = c then ι (M a b * N b d) * E a d else 0 := by
    intro a b c d
    rw [mul_assoc, ← mul_assoc (E a b), ← (hc (N c d) (E a b)).eq, mul_assoc, hE,
      ← mul_assoc, ← map_mul]
    split_ifs with hbc
    · subst hbc; rfl
    · rw [mul_zero]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [phiL_apply, Finset.sum_mul, Finset.mul_sum, h, Matrix.mul_apply, map_sum]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_comm]

theorem matrixRingEquiv_of_matrixUnits : ∀ (k K B : Type) [Field k] [CommRing K] [Ring B] [Algebra k K] [Algebra k B] [FiniteDimensional k B] (n : ℕ) (ι : K →ₐ[k] B), Function.Injective ι → (∀ z x, Commute (ι z) x) → Module.finrank k B = n ^ 2 * Module.finrank k K → ∀ E : Fin n → Fin n → B, (∀ a b c d, E a b * E c d = if b = c then E a d else 0) → ∑ a, E a a = 1 → ∃ Φ : Matrix (Fin n) (Fin n) K ≃+* B, (∀ M, Φ M = ∑ a, ∑ b, ι (M a b) * E a b) ∧ ∀ x a b, ι (Φ.symm x a b) = ∑ c, E c a * x * E b c := by
  intro k K B _ _ _ _ _ _ n ι hi hc hdim E hE h1
  haveI : FiniteDimensional k K := FiniteDimensional.of_injective (ι : K →ₐ[k] B).toLinearMap hi
  have hinj := phiL_injective ι E hi hc hE h1
  have hrank : Module.finrank k (Matrix (Fin n) (Fin n) K) = Module.finrank k B := by
    rw [Module.finrank_matrix, hdim]; simp [Fintype.card_fin, sq]
  have hsurj : Function.Surjective (phiL ι E) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mp hinj
  let f : Matrix (Fin n) (Fin n) K →+* B :=
    { toFun := phiL ι E
      map_one' := phiL_one ι E h1
      map_mul' := phiL_mul ι E hc hE
      map_zero' := map_zero _
      map_add' := map_add _ }
  let Φ : Matrix (Fin n) (Fin n) K ≃+* B := RingEquiv.ofBijective f ⟨hinj, hsurj⟩
  refine ⟨Φ, fun M => rfl, fun x a b => ?_⟩
  obtain ⟨M, rfl⟩ := hsurj x
  have hx : Φ.symm (phiL ι E M) = M := Φ.symm_apply_apply M
  rw [hx]
  exact (extract ι E hc hE h1 M a b).symm

end GlobalTheory.MatUnitIso
end

open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_units_give_matrix_algebra_iso : ∀ (k K B : Type) [Field k] [CommRing K] [Ring B] [Algebra k K] [Algebra k B] [FiniteDimensional k B] (n : ℕ) (ι : K →ₐ[k] B), Function.Injective ι → (∀ z x, Commute (ι z) x) → Module.finrank k B = n ^ 2 * Module.finrank k K → ∀ E : Fin n → Fin n → B, (∀ a b c d, E a b * E c d = if b = c then E a d else 0) → ∑ a, E a a = 1 → ∃ Φ : Matrix (Fin n) (Fin n) K ≃+* B, (∀ M, Φ M = ∑ a, ∑ b, ι (M a b) * E a b) ∧ ∀ x a b, ι (Φ.symm x a b) = ∑ c, E c a * x * E b c := by
  first | (exact @GlobalTheory.MatUnitIso.matrixRingEquiv_of_matrixUnits) | (exact GlobalTheory.MatUnitIso.matrixRingEquiv_of_matrixUnits) | (intros; apply GlobalTheory.MatUnitIso.matrixRingEquiv_of_matrixUnits  <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowersLinearIndependentOverLocalTensorCenter
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowersLinearIndependentOverLocalTensorCenter
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.OrbFinAf

theorem pow_indep_tensor : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (γ : G.C), (minpoly G.F γ).natDegree = G.n →
    ∀ (v : AwayP p) (c : Fin G.n → Qv v ⊗[ℚ] G.F),
      ∑ i, iotaF G v (c i) * (1 : Qv v) ⊗ₜ[ℚ] γ ^ (i : ℕ) = 0 → c = 0 := by
  intro p _ G γ hn v c hc

  let ψ : (Fin G.n → G.F) →ₗ[ℚ] G.C :=
    { toFun := fun f => ∑ i, f i • γ ^ (i : ℕ)
      map_add' := fun f g => by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun q f => by
        simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum, smul_assoc] }
  have li : LinearIndependent G.F (fun i : Fin G.n => γ ^ (i : ℕ)) := by
    have := linearIndependent_pow (K := G.F) γ
    rw [hn] at this
    exact this
  have hψ : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro f hf
    exact funext ((Fintype.linearIndependent_iff.mp li) f hf)
  have hinj : Function.Injective (ψ.lTensor (Qv v)) :=
    Module.Flat.lTensor_preserves_injective_linearMap ψ hψ
  let e := TensorProduct.piRight ℚ ℚ (Qv v) (fun _ : Fin G.n => G.F)
  have key : ∀ t : Qv v ⊗[ℚ] (Fin G.n → G.F),
      ∑ i, iotaF G v (e t i) * (1 : Qv v) ⊗ₜ[ℚ] γ ^ (i : ℕ) = ψ.lTensor (Qv v) t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
      rw [map_add (f := _), map_add (f := _), ← hx, ← hy, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.add_apply, map_add (f := _), add_mul]
    | tmul q f =>
      rw [LinearMap.lTensor_tmul]
      have : ∀ i, e (q ⊗ₜ[ℚ] f) i = q ⊗ₜ[ℚ] f i := fun i => rfl
      simp only [this, iotaF_tmul, Algebra.TensorProduct.tmul_pow, one_pow, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
      simp only [ψ, LinearMap.coe_mk, AddHom.coe_mk, TensorProduct.tmul_sum, Algebra.smul_def]

  have h0 : ψ.lTensor (Qv v) (e.symm c) = 0 := by
    rw [← key, LinearEquiv.apply_symm_apply]; exact hc
  have : e.symm c = 0 := hinj (by rw [h0, map_zero])
  rw [← e.apply_symm_apply c, this, map_zero]

end GlobalTheory.OrbFinAf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowersLinearIndependentOverLocalTensorCenterStatement
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.powers_linearIndependent_over_localTensorCenter : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (γ : G.C), (minpoly G.F γ).natDegree = G.n → ∀ (v : AwayP p) (c : Fin G.n → Qv v ⊗[ℚ] G.F), ∑ i, iotaF G v (c i) * (1 : Qv v) ⊗ₜ[ℚ] γ ^ (i : ℕ) = 0 → c = 0 := by
  first | (exact @GlobalTheory.OrbFinAf.pow_indep_tensor) | (exact GlobalTheory.OrbFinAf.pow_indep_tensor) | (intros; apply GlobalTheory.OrbFinAf.pow_indep_tensor  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyEqOfMonicAevalPowersLinearIndependent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyEqOfMonicAevalPowersLinearIndependent
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

namespace GlobalTheory

theorem charpoly_eq_of_monic_aeval_linearIndependent :
    ∀ (K : Type) [CommRing K] (n : ℕ) (X : Matrix (Fin n) (Fin n) K) (P : Polynomial K),
      P.Monic → P.natDegree = n → Polynomial.aeval X P = 0 →
      LinearIndependent K (fun i : Fin n => X ^ (i : ℕ)) → X.charpoly = P := by
  intro K _ n X P hP hdeg hX hli
  rcases subsingleton_or_nontrivial K with hK | hK
  · exact Subsingleton.elim _ _
  have hc : X.charpoly.Monic := Matrix.charpoly_monic X
  have hcd : X.charpoly.natDegree = n := by
    simpa using Matrix.charpoly_natDegree_eq_dim X
  have hcdeg : X.charpoly.degree = n := by
    rw [Polynomial.degree_eq_natDegree hc.ne_zero, hcd]
  have hPdeg : P.degree = n := by
    rw [Polynomial.degree_eq_natDegree hP.ne_zero, hdeg]
  have hDdeg : (X.charpoly - P).degree < n := by
    have h := Polynomial.degree_sub_lt (p := X.charpoly) (q := P)
      (by rw [hcdeg, hPdeg]) hc.ne_zero (by rw [hc.leadingCoeff, hP.leadingCoeff])
    rwa [hcdeg] at h
  have hDaeval : Polynomial.aeval X (X.charpoly - P) = 0 := by
    rw [map_sub, Matrix.aeval_self_charpoly, hX, sub_zero]
  rw [← sub_eq_zero]
  by_contra hD0
  have hnat : (X.charpoly - P).natDegree < n :=
    (Polynomial.natDegree_lt_iff_degree_lt hD0).mpr hDdeg
  have hsum : ∑ i : Fin n, (X.charpoly - P).coeff (i : ℕ) • X ^ (i : ℕ) = 0 := by
    have h := Polynomial.aeval_eq_sum_range' hnat X
    rw [hDaeval, Finset.sum_range (fun i => (X.charpoly - P).coeff i • X ^ i)] at h
    exact h.symm
  have hcoeff := Fintype.linearIndependent_iff.mp hli
    (fun i : Fin n => (X.charpoly - P).coeff (i : ℕ)) hsum
  apply hD0
  ext k
  rw [Polynomial.coeff_zero]
  by_cases hk : k < n
  · exact hcoeff ⟨k, hk⟩
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hnat (not_lt.mp hk))

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyEqOfMonicAevalPowersLinearIndependentStatement
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charpoly_eq_of_monic_aeval_powers_linearIndependent : ∀ (K : Type) [CommRing K] (n : ℕ) (X : Matrix (Fin n) (Fin n) K) (P : Polynomial K), P.Monic → P.natDegree = n → Polynomial.aeval X P = 0 → LinearIndependent K (fun i : Fin n => X ^ (i : ℕ)) → X.charpoly = P := by
  first | (exact @GlobalTheory.charpoly_eq_of_monic_aeval_linearIndependent) | (exact GlobalTheory.charpoly_eq_of_monic_aeval_linearIndependent) | (intros; apply GlobalTheory.charpoly_eq_of_monic_aeval_linearIndependent  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTensorCenterInclusionInjectiveCentralFinran
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTensorCenterInclusionInjectiveCentralFinran
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

namespace GlobalTheory.OrbFinAf

theorem iotaF_props : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p), Function.Injective (iotaF G v) ∧ (∀ z x, Commute (iotaF G v z) x) ∧ Module.finrank (Qv v) (Qv v ⊗[ℚ] G.C) = G.n ^ 2 * Module.finrank (Qv v) (Qv v ⊗[ℚ] G.F) := by
  intro p _ G v
  haveI : IsSimpleRing G.C := G.simpleC
  haveI : Nontrivial G.C := inferInstance
  haveI : Module.Finite ℚ G.C := Module.Finite.trans G.F G.C
  refine ⟨?_, ?_, ?_⟩
  · have hf : Function.Injective ((IsScalarTower.toAlgHom ℚ G.F G.C).toLinearMap) :=
      (algebraMap G.F G.C).injective
    have := Module.Flat.lTensor_preserves_injective_linearMap (M := Qv v) _ hf
    exact this
  · intro z x
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => rw [map_add (f := _)]; exact ha.add_left hb
    | tmul a f =>
      induction x using TensorProduct.induction_on with
      | zero => exact Commute.zero_right _
      | add c d hc hd => exact hc.add_right hd
      | tmul b c =>
        rw [iotaF_tmul]
        show (a ⊗ₜ[ℚ] algebraMap G.F G.C f) * (b ⊗ₜ[ℚ] c) = (b ⊗ₜ[ℚ] c) * (a ⊗ₜ[ℚ] algebraMap G.F G.C f)
        rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_comm a b,
          Algebra.commutes]
  · rw [Module.finrank_baseChange, Module.finrank_baseChange, ← Module.finrank_mul_finrank ℚ G.F G.C,
      G.rankC, mul_comm]

end GlobalTheory.OrbFinAf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTensorCenterInclusionInjectiveCentralFinranStatement
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localTensorCenterInclusion_injective_central_finrank : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p), Function.Injective (iotaF G v) ∧ (∀ z x, Commute (iotaF G v z) x) ∧ Module.finrank (Qv v) (Qv v ⊗[ℚ] G.C) = G.n ^ 2 * Module.finrank (Qv v) (Qv v ⊗[ℚ] G.F) := by
  first | (exact @GlobalTheory.OrbFinAf.iotaF_props) | (exact GlobalTheory.OrbFinAf.iotaF_props) | (intros; apply GlobalTheory.OrbFinAf.iotaF_props  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralMatrixUnitsAtPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNsmulMemSpan
namespace GlobalTheory.MultiplierOrders

theorem exists_nsmul_mem_span {C : Type} [AddCommGroup C] [Module ℚ C] (S : Set C) (x : C)
    (hx : x ∈ Submodule.span ℚ S) : ∃ m : ℕ, 0 < m ∧ m • x ∈ Submodule.span ℤ S := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_pos, by rw [one_smul]; exact Submodule.subset_span hy⟩
  | zero => exact ⟨1, one_pos, by rw [smul_zero]; exact Submodule.zero_mem _⟩
  | add y z _ _ hy hz =>
    obtain ⟨m, hm, hy⟩ := hy
    obtain ⟨n, hn, hz⟩ := hz
    refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
    rw [smul_add]
    refine Submodule.add_mem _ ?_ ?_
    · rw [mul_comm, mul_smul]
      exact nsmul_mem hy n
    · rw [mul_smul]
      exact nsmul_mem hz m
  | smul q y _ hy =>
    obtain ⟨m, hm, hy⟩ := hy
    refine ⟨m * q.den, Nat.mul_pos hm q.den_pos, ?_⟩
    have h : (m * q.den) • q • y = q.num • m • y := by
      rw [← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ m, ← Int.cast_smul_eq_zsmul ℚ,
        smul_smul, smul_smul]
      congr 1
      push_cast
      rw [mul_assoc, Rat.den_mul_eq_num, mul_comm]
    rw [h]
    exact Submodule.smul_mem _ _ hy

def multipliers {C : Type} [Ring C] (L : Submodule ℤ C) : Subring C where
  carrier := {x | ∀ y ∈ L, x * y ∈ L}
  mul_mem' := fun {a b} ha hb y hy => by
    rw [mul_assoc]; exact ha _ (hb y hy)
  one_mem' := fun y hy => by rw [one_mul]; exact hy
  add_mem' := fun {a b} ha hb y hy => by
    rw [add_mul]; exact L.add_mem (ha y hy) (hb y hy)
  zero_mem' := fun y _ => by rw [zero_mul]; exact L.zero_mem
  neg_mem' := fun {a} ha y hy => by
    rw [neg_mul]; exact L.neg_mem (ha y hy)

theorem exists_order (C : Type) [Ring C] [Algebra ℚ C] [FiniteDimensional ℚ C] :
    ∃ OB : Subring C, Module.Finite ℤ OB ∧ ∀ b : C, ∃ m : ℕ, 0 < m ∧ (m : C) * b ∈ OB := by
  classical
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := ℚ) (M := C)
  have key : ∀ x : C, ∃ m : ℕ, 0 < m ∧ m • x ∈ Submodule.span ℤ (S : Set C) := fun x =>
    exists_nsmul_mem_span _ x (by rw [hS]; exact Submodule.mem_top)
  set L : Submodule ℤ C := Submodule.span ℤ (S : Set C) with hL
  haveI : Module.Finite ℤ L := Module.Finite.iff_fg.mpr ⟨S, rfl⟩
  refine ⟨multipliers L, ?_, ?_⟩
  · obtain ⟨m, hm, h1⟩ := key 1
    let f : multipliers L →+ L :=
      { toFun := fun x => ⟨x.1 * (m • (1 : C)), x.2 _ h1⟩
        map_zero' := Subtype.ext (by simp)
        map_add' := fun a b => Subtype.ext (by simp [add_mul]) }
    refine Module.Finite.of_injective f.toIntLinearMap ?_
    intro a b hab
    have h : a.1 * (m • (1 : C)) = b.1 * (m • (1 : C)) := congrArg Subtype.val hab
    rw [mul_smul_comm, mul_smul_comm, mul_one, mul_one, ← Nat.cast_smul_eq_nsmul ℚ,
      ← Nat.cast_smul_eq_nsmul ℚ] at h
    have hm' : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
    exact Subtype.ext (smul_right_injective C hm' h)
  · intro b
    choose n hn hmem using fun s : C => key (b * s)
    refine ⟨∏ s ∈ S, n s, Finset.prod_pos fun s _ => hn s, ?_⟩
    intro y hy
    induction hy using Submodule.span_induction with
    | mem s hs =>
      have hs' : s ∈ S := hs
      rw [mul_assoc, ← nsmul_eq_mul, ← Finset.prod_erase_mul S n hs', mul_smul]
      exact nsmul_mem (hmem s) _
    | zero => rw [mul_zero]; exact L.zero_mem
    | add y z _ _ hy hz => rw [mul_add]; exact L.add_mem hy hz
    | smul k y _ hy => rw [mul_smul_comm]; exact L.smul_mem k hy

end GlobalTheory.MultiplierOrders
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralMatrixUnitsAtPlaces
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.OrbFinAf.MatrixUnits₂

theorem exists_order (C : Type) [Ring C] [Algebra ℚ C] [FiniteDimensional ℚ C] :
    ∃ OB : Subring C, Module.Finite ℤ OB ∧ ∀ b : C, ∃ m : ℕ, 0 < m ∧ (m : C) * b ∈ OB := by
  first
  | exact @_root_.GlobalTheory.MultiplierOrders.exists_order
  | exact _root_.GlobalTheory.MultiplierOrders.exists_order
  | (apply _root_.GlobalTheory.MultiplierOrders.exists_order <;> assumption)
  | (intros; apply _root_.GlobalTheory.MultiplierOrders.exists_order <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MultiplierOrders.exists_order <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MultiplierOrders.exists_order ..)

theorem isIntV_order_eventually (p : ℕ) [Fact p.Prime] (G : HTGroup p) (OB : Subring G.C)
    (hfin : Module.Finite ℤ OB) :
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∀ x ∈ OB, IsIntV G v ((1 : Qv v) ⊗ₜ[ℚ] x) := by
  obtain ⟨k, g, hg⟩ := Module.Finite.exists_fin (R := ℤ) (M := OB)
  have H := Filter.eventually_all.2 fun i : Fin k => Filter.eventually_all.2 fun m =>
    ratCast_mem_intV_eventually p ((Module.finBasis ℚ G.C).repr (g i : G.C) m)
  refine H.mono fun v hv x hx => ?_
  have hx' : (⟨x, hx⟩ : OB) ∈ Submodule.span ℤ (Set.range g) := by rw [hg]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hx'
  have e : (1 : Qv v) ⊗ₜ[ℚ] x = ∑ i, ((c i : ℤ) : Qv v) ⊗ₜ[ℚ] (g i : G.C) := by
    have hx2 : x = ∑ i, (c i : ℤ) • (g i : G.C) := by
      have := congrArg Subtype.val hc
      simpa using this.symm
    rw [hx2, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Int.cast_smul_eq_zsmul ℚ, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
    simp
  rw [e]
  exact isIntV_of_eq_sum G v _ _ _ (fun i _ => intCast_mem _ _) (fun i _ m => hv i m)

end GlobalTheory.OrbFinAf.MatrixUnits₂

namespace GlobalTheory.OrbFinAf.MatrixUnits₂

open Rat.HeightOneSpectrum

def theta (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p) [Fact (primesEquiv v.1 : ℕ).Prime] :
    ℚ_[(primesEquiv v.1 : ℕ)] ⊗[ℚ] G.C ≃ₐ[ℚ] Qv v ⊗[ℚ] G.C :=
  Algebra.TensorProduct.congr (adicCompletion.padicEquiv v.1).symm.toAlgEquiv AlgEquiv.refl

theorem theta_tmul (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p) [Fact (primesEquiv v.1 : ℕ).Prime]
    (r : ℚ_[(primesEquiv v.1 : ℕ)]) (c : G.C) :
    theta p G v (r ⊗ₜ c) = (adicCompletion.padicEquiv v.1).symm r ⊗ₜ c := rfl

theorem padicEquiv_symm_coe_mem (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p) [Fact (primesEquiv v.1 : ℕ).Prime]
    (r : ℤ_[(primesEquiv v.1 : ℕ)]) :
    (adicCompletion.padicEquiv v.1).symm (r : ℚ_[(primesEquiv v.1 : ℕ)]) ∈ v.1.adicCompletionIntegers ℚ := by
  obtain ⟨x, hx, hxr⟩ := (adicCompletion.padicEquiv_bijOn v.1).surjOn
    (show (r : ℚ_[(primesEquiv v.1 : ℕ)]) ∈ PadicInt.subring _ from r.2)
  rw [← hxr, ContinuousAlgEquiv.symm_apply_apply]
  exact hx

end GlobalTheory.OrbFinAf.MatrixUnits₂

namespace GlobalTheory.OrbFinAf.MatrixUnits₂

open Rat.HeightOneSpectrum GlobalTheory.LKInvGood

theorem isIntV_theta_locOrder (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p)
    [Fact (primesEquiv v.1 : ℕ).Prime] (OB : Subring G.C)
    (hO : ∀ x ∈ OB, IsIntV G v ((1 : Qv v) ⊗ₜ[ℚ] x)) (h1 : IsIntV G v 1)
    (hmul : ∀ y z : Qv v ⊗[ℚ] G.C, IsIntV G v y → IsIntV G v z → IsIntV G v (y * z))
    (y : ℚ_[(primesEquiv v.1 : ℕ)] ⊗[ℚ] G.C) (hy : y ∈ locOrder (primesEquiv v.1 : ℕ) OB) :
    IsIntV G v (theta p G v y) := by
  induction hy using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨c, hc, rfl⟩ := hx
    rw [theta_tmul, map_one]
    exact hO c hc
  | algebraMap r =>
    rw [Algebra.TensorProduct.algebraMap_apply, theta_tmul]
    intro k
    rw [basV_repr_tmul]
    have h1k := h1 k
    rw [Algebra.TensorProduct.one_def, basV_repr_tmul, one_mul] at h1k
    exact mul_mem (padicEquiv_symm_coe_mem p G v r) h1k
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact isIntV_add' G v hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact hmul _ _ hx hy

theorem finite_dvd (p : ℕ) (N : ℕ) (hN : 0 < N) :
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ¬ (primesEquiv v.1 : ℕ) ∣ N := by
  have hfin : {v : AwayP p | (primesEquiv v.1 : ℕ) ∣ N}.Finite := by
    have hinj : Function.Injective fun v : AwayP p => (primesEquiv v.1 : ℕ) :=
      fun a b h => Subtype.ext (primesEquiv.injective (Subtype.ext h))
    refine Set.Finite.of_finite_image ?_ hinj.injOn
    refine (Set.finite_le_nat N).subset ?_
    rintro _ ⟨v, hv, rfl⟩
    exact Nat.le_of_dvd hN hv
  exact hfin.eventually_cofinite_notMem

theorem matrixUnits_eventually : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p),
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∃ E : Fin G.n → Fin G.n → Qv v ⊗[ℚ] G.C,
      (∀ i j k l, E i j * E k l = if j = k then E i l else 0) ∧ ∑ i, E i i = 1 ∧
      ∀ i j, IsIntV G v (E i j) := by
  intro p _ G
  obtain ⟨OB, hfin, hspan⟩ := exists_order G.C
  obtain ⟨N, hN, hmat⟩ := GlobalTheory.T.adjoinLocalOrderTensorPadic_matrix_almost_all G.F G.C G.n G.rankC OB hfin hspan
  filter_upwards [finite_dvd p N hN, isIntV_order_eventually p G OB hfin, intV_order_eventually p G]
    with v hv hO hord
  haveI : Fact (primesEquiv v.1 : ℕ).Prime := ⟨(primesEquiv v.1).2⟩
  obtain ⟨ψ, -⟩ := hmat (primesEquiv v.1 : ℕ) hv
  let E : Fin G.n → Fin G.n → Qv v ⊗[ℚ] G.C := fun i j =>
    theta p G v ((ψ.symm (Matrix.single i j 1) : locOrder (primesEquiv v.1 : ℕ) OB) :
      ℚ_[(primesEquiv v.1 : ℕ)] ⊗[ℚ] G.C)
  refine ⟨E, fun i j k l => ?_, ?_, fun i j =>
    isIntV_theta_locOrder p G v OB hO hord.1 hord.2.1 _ (ψ.symm _).2⟩
  · simp only [E]
    rw [← map_mul, ← Subalgebra.coe_mul, ← map_mul]
    split_ifs with hjk
    · subst hjk
      rw [Matrix.single_mul_single_same, mul_one]
    · rw [Matrix.single_mul_single_of_ne (h := hjk), map_zero, ZeroMemClass.coe_zero, map_zero]
  · have hs : ∑ i, (Matrix.single i i (1 : cenOrder (primesEquiv v.1 : ℕ) G.F) :
        Matrix (Fin G.n) (Fin G.n) (cenOrder (primesEquiv v.1 : ℕ) G.F)) = 1 := by
      ext a b
      rw [Matrix.sum_apply, Matrix.one_apply, Finset.sum_eq_single a]
      · by_cases h : a = b
        · subst h; simp [Matrix.single_apply]
        · simp [Matrix.single_apply, h]
      · intro c _ hc; simp [Matrix.single_apply, hc]
      · simp
    simp only [E]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum (theta p G v), ← AddSubmonoidClass.coe_finsetSum, ← map_sum ψ.symm, hs, map_one,
      OneMemClass.coe_one, map_one]

end GlobalTheory.OrbFinAf.MatrixUnits₂
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralMatrixUnitsAtPlacesStatement
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_integral_matrix_units_at_places : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∃ E : Fin G.n → Fin G.n → Qv v ⊗[ℚ] G.C, (∀ i j k l, E i j * E k l = if j = k then E i l else 0) ∧ ∑ i, E i i = 1 ∧ ∀ i j, IsIntV G v (E i j) := by
  first | (exact @GlobalTheory.OrbFinAf.MatrixUnits₂.matrixUnits_eventually) | (exact GlobalTheory.OrbFinAf.MatrixUnits₂.matrixUnits_eventually) | (intros; apply GlobalTheory.OrbFinAf.MatrixUnits₂.matrixUnits_eventually  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralLocalCenterFiniteMaximalIdeals
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralLocalCenterFiniteMaximalIdeals
noncomputable section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

namespace GlobalTheory.OrbFinAf

variable {p : ℕ} [Fact p.Prime]

theorem iotaF_injective (G : HTGroup p) (v : AwayP p) : Function.Injective (iotaF G v) := by
  have hf : Function.Injective (IsScalarTower.toAlgHom ℚ G.F G.C).toLinearMap :=
    (algebraMap G.F G.C).injective
  exact Module.Flat.lTensor_preserves_injective_linearMap (M := Qv v) _ hf

def intFAlgMap (G : HTGroup p) (v : AwayP p) (h1 : IsIntV G v 1)
    (hm : ∀ y z : Qv v ⊗[ℚ] G.C, IsIntV G v y → IsIntV G v z → IsIntV G v (y * z)) :
    v.1.adicCompletionIntegers ℚ →+* intF G v h1 hm :=
  ((algebraMap (Qv v) (Qv v ⊗[ℚ] G.F)).comp (v.1.adicCompletionIntegers ℚ).subtype).codRestrict _ fun c => by
    rw [mem_intF]
    intro i
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.commutes, Algebra.algebraMap_eq_smul_one,
      map_smul, Finsupp.smul_apply, smul_eq_mul, map_one]
    exact mul_mem c.2 (h1 i)

def intFCoord (G : HTGroup p) (v : AwayP p) (h1 : IsIntV G v 1)
    (hm : ∀ y z : Qv v ⊗[ℚ] G.C, IsIntV G v y → IsIntV G v z → IsIntV G v (y * z)) :
    letI := (intFAlgMap G v h1 hm).toAlgebra
    intF G v h1 hm →ₗ[v.1.adicCompletionIntegers ℚ] (Fin (Module.finrank ℚ G.C) → v.1.adicCompletionIntegers ℚ) :=
  letI := (intFAlgMap G v h1 hm).toAlgebra
  { toFun := fun m i => ⟨(basV G v).repr (iotaF G v m) i, (mem_intF G v h1 hm m).1 m.2 i⟩
    map_add' := fun a b => by
      funext i; apply Subtype.ext
      simp [map_add (f := _)]
    map_smul' := fun c m => by
      funext i; apply Subtype.ext
      show (basV G v).repr (iotaF G v (algebraMap (Qv v) (Qv v ⊗[ℚ] G.F) (c : Qv v) * m)) i =
        (c : Qv v) * (basV G v).repr (iotaF G v m) i
      rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, map_smul, map_smul]
      rfl }

theorem intFCoord_injective (G : HTGroup p) (v : AwayP p) (h1 : IsIntV G v 1)
    (hm : ∀ y z : Qv v ⊗[ℚ] G.C, IsIntV G v y → IsIntV G v z → IsIntV G v (y * z)) :
    Function.Injective (intFCoord G v h1 hm) := by
  intro a b hab
  apply Subtype.ext
  apply iotaF_injective G v
  apply (basV G v).repr.injective
  refine Finsupp.ext fun i => ?_
  exact congrArg Subtype.val (congrFun hab i)

theorem intF_finite (G : HTGroup p) (v : AwayP p) (h1 : IsIntV G v 1)
    (hm : ∀ y z : Qv v ⊗[ℚ] G.C, IsIntV G v y → IsIntV G v z → IsIntV G v (y * z)) :
    letI := (intFAlgMap G v h1 hm).toAlgebra
    Module.Finite (v.1.adicCompletionIntegers ℚ) (intF G v h1 hm) :=
  letI := (intFAlgMap G v h1 hm).toAlgebra
  Module.Finite.of_injective (intFCoord G v h1 hm) (intFCoord_injective G v h1 hm)

theorem intF_finite_maximal : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p) (h1 : IsIntV G v 1)
    (hm : ∀ y z : Qv v ⊗[ℚ] G.C, IsIntV G v y → IsIntV G v z → IsIntV G v (y * z)),
    Set.Finite {I : Ideal (intF G v h1 hm) | I.IsMaximal} := by
  intro p _ G v h1 hm
  letI := (intFAlgMap G v h1 hm).toAlgebra
  haveI := intF_finite G v h1 hm
  exact ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.finite_maximal_ideals_of_finite (R := v.1.adicCompletionIntegers ℚ) (intF G v h1 hm)

end GlobalTheory.OrbFinAf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralLocalCenterFiniteMaximalIdealsStatement
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralLocalCenter_finite_maximal_ideals : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p) (h1 : IsIntV G v 1) (hm : ∀ y z : Qv v ⊗[ℚ] G.C, IsIntV G v y → IsIntV G v z → IsIntV G v (y * z)), Set.Finite {I : Ideal (intF G v h1 hm) | I.IsMaximal} := by
  first | (exact @GlobalTheory.OrbFinAf.intF_finite_maximal) | (exact GlobalTheory.OrbFinAf.intF_finite_maximal) | (intros; apply GlobalTheory.OrbFinAf.intF_finite_maximal  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyCompletedTensorMatrixSplitSemilocal
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.OrbFinAf

theorem coeff_isIntV_eventually (p : ℕ) [Fact p.Prime] (G : HTGroup p) (f : Polynomial G.F) :
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)),
      ∀ i, IsIntV G v ((1 : Qv v) ⊗ₜ[ℚ] algebraMap G.F G.C (f.coeff i)) := by
  have h := Filter.eventually_all.2 fun i : Fin (f.natDegree + 1) =>
    GlobalTheory.OrbFinAfFixed.isIntV_one_tmul_eventually p G (algebraMap G.F G.C (f.coeff i))
  filter_upwards [h] with v hv i
  by_cases hi : i ≤ f.natDegree
  · exact hv ⟨i, Nat.lt_succ_of_le hi⟩
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (not_le.1 hi), map_zero, TensorProduct.tmul_zero]
    exact isIntV_zero G v

theorem split_eventually : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (γ : G.C), (minpoly G.F γ).natDegree = G.n → (minpoly G.F γ).Separable → ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∃ (K : Type) (_ : CommRing K) (R : Subring K) (Φ : Matrix (Fin G.n) (Fin G.n) K ≃+* Qv v ⊗[ℚ] G.C), Set.Finite {I : Ideal R | I.IsMaximal} ∧ (∀ a : Qv v ⊗[ℚ] G.C, IsIntV G v a ↔ ∀ i j, Φ.symm a i j ∈ R) ∧ ∃ Q : Polynomial R, Q.Separable ∧ Q.map R.subtype = (Φ.symm ((1 : Qv v) ⊗ₜ[ℚ] γ)).charpoly := by
  intro p _ G γ hdeg hsep
  obtain ⟨a, b, hab⟩ := hsep
  filter_upwards [intV_order_eventually p G, GlobalTheory.T.eventually_integral_matrix_units_at_places p G, coeff_isIntV_eventually p G (minpoly G.F γ),
    coeff_isIntV_eventually p G a, coeff_isIntV_eventually p G b] with v hO hEE hP ha hb
  obtain ⟨h1, hm, -⟩ := hO
  obtain ⟨E, hE, hE1, hEi⟩ := hEE
  obtain ⟨hinj, hcen, hdim⟩ := GlobalTheory.T.localTensorCenterInclusion_injective_central_finrank p G v
  obtain ⟨Φ, hΦ, hΦs⟩ := GlobalTheory.T.matrix_units_give_matrix_algebra_iso (Qv v) (Qv v ⊗[ℚ] G.F) (Qv v ⊗[ℚ] G.C) G.n (iotaF G v) hinj hcen hdim E hE hE1
  let φ0 : G.F →+* Qv v ⊗[ℚ] G.F :=
    (Algebra.TensorProduct.includeRight : G.F →ₐ[ℚ] Qv v ⊗[ℚ] G.F).toRingHom
  have hφ : ∀ x, iotaF G v (φ0 x) = (1 : Qv v) ⊗ₜ[ℚ] algebraMap G.F G.C x := fun x => rfl
  have hsub : ∀ f : Polynomial G.F, (∀ i, IsIntV G v ((1 : Qv v) ⊗ₜ[ℚ] algebraMap G.F G.C (f.coeff i))) →
      (↑(f.map φ0).coeffs : Set (Qv v ⊗[ℚ] G.F)) ⊆ (intF G v h1 hm : Set (Qv v ⊗[ℚ] G.F)) := by
    intro f hf c hc
    obtain ⟨i, -, rfl⟩ := Polynomial.mem_coeffs_iff.1 hc
    rw [Polynomial.coeff_map]
    show IsIntV G v (iotaF G v (φ0 (f.coeff i)))
    rw [hφ]; exact hf i
  have hsc : ∀ z : Qv v ⊗[ℚ] G.F,
      Φ (algebraMap (Qv v ⊗[ℚ] G.F) (Matrix (Fin G.n) (Fin G.n) (Qv v ⊗[ℚ] G.F)) z) = iotaF G v z := by
    intro z
    rw [hΦ, ← mul_one (iotaF G v z), ← hE1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · simp [Matrix.algebraMap_matrix_apply]
    · intro j _ hj; simp [Matrix.algebraMap_matrix_apply, Ne.symm hj]
    · simp
  refine ⟨Qv v ⊗[ℚ] G.F, inferInstance, intF G v h1 hm, Φ, GlobalTheory.T.integralLocalCenter_finite_maximal_ideals p G v h1 hm,
    fun x => ⟨fun hx i j => ?_, fun hx => ?_⟩, ?_⟩
  · show IsIntV G v (iotaF G v (Φ.symm x i j))
    rw [hΦs]
    exact isIntV_sum G v _ _ fun c _ => hm _ _ (hm _ _ (hEi c i) hx) (hEi j c)
  · rw [← Φ.apply_symm_apply x, hΦ]
    exact isIntV_sum G v _ _ fun i _ => isIntV_sum G v _ _ fun j _ => hm _ _ (hx i j) (hEi i j)
  · refine ⟨((minpoly G.F γ).map φ0).toSubring _ (hsub _ hP), ?_, ?_⟩
    · refine ⟨(a.map φ0).toSubring _ (hsub _ ha), (b.map φ0).toSubring _ (hsub _ hb), ?_⟩
      apply Polynomial.map_injective (intF G v h1 hm).subtype Subtype.val_injective
      rw [Polynomial.map_add (f := _), Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_one,
        ← Polynomial.derivative_map, Polynomial.map_toSubring, Polynomial.map_toSubring, Polynomial.map_toSubring,
        Polynomial.derivative_map, ← Polynomial.map_mul, ← Polynomial.map_mul, ← Polynomial.map_add, hab,
        Polynomial.map_one]
    · rw [Polynomial.map_toSubring]
      have hmon : (minpoly G.F γ).Monic := minpoly.monic (Algebra.IsIntegral.isIntegral γ)
      have hX : Φ (Φ.symm ((1 : Qv v) ⊗ₜ[ℚ] γ)) = (1 : Qv v) ⊗ₜ[ℚ] γ := Φ.apply_symm_apply _
      symm
      apply GlobalTheory.T.charpoly_eq_of_monic_aeval_powers_linearIndependent
      · exact hmon.map φ0
      · rw [hmon.natDegree_map, hdeg]
      · apply Φ.injective
        rw [map_zero, Polynomial.aeval_def]
        have h3 := Polynomial.hom_eval₂ ((minpoly G.F γ).map φ0)
          (algebraMap (Qv v ⊗[ℚ] G.F) (Matrix (Fin G.n) (Fin G.n) (Qv v ⊗[ℚ] G.F)))
          (Φ : Matrix (Fin G.n) (Fin G.n) (Qv v ⊗[ℚ] G.F) →+* Qv v ⊗[ℚ] G.C) (Φ.symm ((1 : Qv v) ⊗ₜ[ℚ] γ))
        rw [RingEquiv.coe_toRingHom] at h3
        rw [h3, hX, Polynomial.eval₂_map]
        have e : ((Φ : Matrix (Fin G.n) (Fin G.n) (Qv v ⊗[ℚ] G.F) →+* Qv v ⊗[ℚ] G.C).comp
            (algebraMap (Qv v ⊗[ℚ] G.F) _)).comp φ0 =
            (Algebra.TensorProduct.includeRight : G.C →ₐ[ℚ] Qv v ⊗[ℚ] G.C).toRingHom.comp (algebraMap G.F G.C) := by
          ext x
          simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom]
          rw [hsc, hφ]; rfl
        rw [e]
        have h4 := Polynomial.hom_eval₂ (minpoly G.F γ) (algebraMap G.F G.C)
          (Algebra.TensorProduct.includeRight : G.C →ₐ[ℚ] Qv v ⊗[ℚ] G.C).toRingHom γ
        have e2 : Polynomial.eval₂ (algebraMap G.F G.C) γ (minpoly G.F γ) = 0 := minpoly.aeval G.F γ
        rw [e2, map_zero] at h4
        exact h4.symm
      · rw [Fintype.linearIndependent_iff]
        intro g hg
        have := GlobalTheory.T.powers_linearIndependent_over_localTensorCenter p G γ hdeg v g (by
          have h2 := congrArg Φ hg
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sum, map_zero] at h2
          rw [← h2]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Algebra.smul_def, map_mul, map_pow, hsc, hX, Algebra.TensorProduct.tmul_pow, one_pow])
        intro i; rw [this]; rfl

end GlobalTheory.OrbFinAf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyCompletedTensorMatrixSplitSemilocalStatement
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_completedTensor_matrix_split_semilocal : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (γ : G.C), (minpoly G.F γ).natDegree = G.n → (minpoly G.F γ).Separable → ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∃ (K : Type) (_ : CommRing K) (R : Subring K) (Φ : Matrix (Fin G.n) (Fin G.n) K ≃+* Qv v ⊗[ℚ] G.C), Set.Finite {I : Ideal R | I.IsMaximal} ∧ (∀ a : Qv v ⊗[ℚ] G.C, IsIntV G v a ↔ ∀ i j, Φ.symm a i j ∈ R) ∧ ∃ Q : Polynomial R, Q.Separable ∧ Q.map R.subtype = (Φ.symm ((1 : Qv v) ⊗ₜ[ℚ] γ)).charpoly := by
  first | (exact @GlobalTheory.OrbFinAf.split_eventually) | (exact GlobalTheory.OrbFinAf.split_eventually) | (intros; apply GlobalTheory.OrbFinAf.split_eventually  <;> assumption)
end
