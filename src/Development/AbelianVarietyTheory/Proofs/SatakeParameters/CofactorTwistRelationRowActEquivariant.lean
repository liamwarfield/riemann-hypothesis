module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CommuteIsNilpotentOfUnipotent

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CofactorTwistRelationRowActEquivariant
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CofactorTwistRelationRowActEquivariant
open MvPolynomial NumberField IsDedekindDomain Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO GlobalTheory.ValCmp

noncomputable section

namespace GlobalTheory.ValCmp.Eqv

theorem degree_of_colWeight {n : ℕ} {ν : Fin n → ℕ} (m : Fin n × Fin n →₀ ℕ)
    (h : Finsupp.weight (colW n n) m = ν) : (m.sum fun _ k => k) = ∑ j, ν j := by
  classical
  rw [← h, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum]
  simp only [Finset.sum_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [colW, Pi.single_apply]

theorem rowAct_smul_matrix {n : ℕ} {R : Type} [CommRing R] {ν : Fin n → ℕ} (c : R) (g : Matrix (Fin n) (Fin n) R)
    (f : MvPolynomial (Fin n × Fin n) R) (hf : IsWeightedHomogeneous (colW n n) f ν) :
    rowAct R (c • g) f = c ^ (∑ j, ν j) • rowAct R g f := by
  classical
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [← degree_of_colWeight m (hf (mem_support_iff.mp hm))]
  have h1 : ∀ v : Fin n × Fin n, (∑ b : Fin n, C ((c • g) v.1 b) * X (b, v.2) : MvPolynomial (Fin n × Fin n) R) =
      C c * ∑ b : Fin n, C (g v.1 b) * X (b, v.2) := by
    intro v
    simp only [Matrix.smul_apply, smul_eq_mul, C_mul, Finset.mul_sum, mul_assoc]
  simp only [rowAct, aeval_monomial, h1, Finsupp.prod, Finsupp.sum, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, smul_eq_C_mul, C_pow]
  ring

theorem rowAct_genM {n : ℕ} {R : Type} [CommRing R] (g : Matrix (Fin n) (Fin n) R) :
    (rowAct R (n := n) g).mapMatrix (genM R n) = (C : R →+* MP R n).mapMatrix g * genM R n := by
  ext a s : 2
  simp [rowAct, genM, Matrix.mul_apply]

theorem rowAct_det_genM {n : ℕ} {R : Type} [CommRing R] (g : Matrix (Fin n) (Fin n) R) :
    rowAct R (n := n) g (genM R n).det = C g.det * (genM R n).det := by
  rw [AlgHom.map_det, rowAct_genM, Matrix.det_mul, RingHom.map_det]

theorem rowAct_transpose_cofAct {n : ℕ} {R : Type} [CommRing R] (g : Matrix (Fin n) (Fin n) R) (f : MP R n) :
    rowAct R g.transpose (cofAct R n f) = cofAct R n (rowAct R g.adjugate f) := by
  have h : (rowAct R (n := n) g.transpose).comp (cofAct R n) = (cofAct R n).comp (rowAct R g.adjugate) := by
    apply MvPolynomial.algHom_ext
    intro v
    have h1 : (rowAct R (n := n) g.transpose).mapMatrix (genM R n).adjugate =
        (genM R n).adjugate * (C : R →+* MP R n).mapMatrix g.transpose.adjugate := by
      rw [AlgHom.map_adjugate, rowAct_genM, Matrix.adjugate_mul_distrib, RingHom.map_adjugate]
    have h2 := congrFun (congrFun h1 v.2.rev) v.1
    rw [AlgHom.mapMatrix_apply, Matrix.map_apply] at h2
    set_option synthInstance.maxHeartbeats 100000 in
      rw [AlgHom.comp_apply, AlgHom.comp_apply, cofAct, aeval_X, h2, rowAct, aeval_X, map_sum, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_mul, aeval_X, aeval_C, ← Matrix.adjugate_transpose, mul_comm]
    rfl
  exact DFunLike.congr_fun h f

theorem cofRel_rowAct : ∀ (K : Type) [Field K] (m : ℕ) (ν : Fin (m + 1) → ℕ) (h : Matrix (Fin (m + 1)) (Fin (m + 1)) K), IsUnit h.det → ∀ f ∈ dualWeyl K (m + 1) (m + 1) ν, ∀ g : MP K (m + 1), CofRel K m ν f g → CofRel K m ν (rowAct K h⁻¹ f) (h.det ^ (-(ν 0 : ℤ)) • rowAct K h.transpose g) := by
  intro K _ m ν h hh f hf g hfg
  have hd : h.det ≠ 0 := hh.ne_zero
  have hadj : h.adjugate = h.det • h⁻¹ := by
    rw [Matrix.inv_def, smul_smul, Ring.inverse_eq_inv', mul_inv_cancel₀ hd, one_smul]
  have hle : ν 0 ≤ ∑ i, ν i := Finset.single_le_sum (f := ν) (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)
  unfold CofRel at hfg ⊢
  have h1 := congrArg (rowAct K h.transpose) hfg
  rw [rowAct_transpose_cofAct, hadj, rowAct_smul_matrix _ _ _ hf.1, map_smul, map_mul, map_pow, rowAct_det_genM,
    Matrix.det_transpose, mul_pow, ← C_pow, mul_assoc, ← smul_eq_C_mul] at h1
  obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hle
  rw [he, Nat.add_sub_cancel_left] at h1 ⊢
  rw [pow_add, mul_comm (h.det ^ ν 0), mul_smul] at h1
  have h2 : _ = _ := smul_right_injective _ (pow_ne_zero e hd) h1
  rw [mul_smul_comm, h2, smul_smul, zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ hd), one_smul]

end GlobalTheory.ValCmp.Eqv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CofactorTwistRelationRowActEquivariantStatement
open MvPolynomial NumberField IsDedekindDomain Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO GlobalTheory.ValCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cofactorTwistRelation_rowAct_equivariant : ∀ (K : Type) [Field K] (m : ℕ) (ν : Fin (m + 1) → ℕ) (h : Matrix (Fin (m + 1)) (Fin (m + 1)) K), IsUnit h.det → ∀ f ∈ dualWeyl K (m + 1) (m + 1) ν, ∀ g : MP K (m + 1), CofRel K m ν f g → CofRel K m ν (rowAct K h⁻¹ f) (h.det ^ (-(ν 0 : ℤ)) • rowAct K h.transpose g) := by
  first | exact @GlobalTheory.ValCmp.Eqv.cofRel_rowAct | exact GlobalTheory.ValCmp.Eqv.cofRel_rowAct | (intros; apply GlobalTheory.ValCmp.Eqv.cofRel_rowAct <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CofactorTwistRelationDualWeightInvolutive
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CofactorTwistRelationDualWeightInvolutive
open MvPolynomial NumberField IsDedekindDomain Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO GlobalTheory.ValCmp

noncomputable section

namespace GlobalTheory.ValCmp.Invol

theorem aeval_scale {R S : Type} [CommRing R] [CommRing S] [Algebra R S] {r n : ℕ} (ν : Fin n → ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) (hf : IsWeightedHomogeneous (colW r n) f ν) (c : S)
    (x : Fin r × Fin n → S) :
    aeval (fun v => c * x v) f = c ^ (∑ i, ν i) * aeval x f := by
  classical
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hw : Finsupp.weight (colW r n) d = ν := hf (mem_support_iff.mp hd)
  have hs : ∑ i, ν i = ∑ v, d v := by
    rw [← hw, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp only [Finset.sum_apply, colW, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← Finset.mul_sum]
    simp [Pi.single_apply]
  rw [aeval_monomial, aeval_monomial, Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp), hs]
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  ring

def cofM (R : Type) [CommRing R] (n : ℕ) : Matrix (Fin n) (Fin n) (MP R n) :=
  (genM R n).adjugate.transpose.submatrix id Fin.revPerm

theorem map_genM (R : Type) [CommRing R] (n : ℕ) :
    (cofAct R n).mapMatrix (genM R n) = cofM R n := by
  ext1 a s
  simp [cofAct, genM, cofM]

theorem det_cofM (R : Type) [CommRing R] (m : ℕ) :
    (cofM R (m + 1)).det = ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (m + 1))) : ℤ) : MP R (m + 1)) *
      (genM R (m + 1)).det ^ m := by
  rw [cofM, Matrix.det_permute', Matrix.det_transpose, Matrix.det_adjugate]
  simp

theorem cofAct_det (R : Type) [CommRing R] (n : ℕ) :
    cofAct R n (genM R n).det = (cofM R n).det := by
  rw [AlgHom.map_det, map_genM]

theorem det_mul_cofAct_cofAct_X (R : Type) [CommRing R] (n : ℕ) (v : Fin n × Fin n) :
    (genM R n).det * cofAct R n (cofAct R n (X v)) = (cofM R n).det * X v := by
  have h1 : cofM R n * (genM R n).transpose.submatrix Fin.revPerm id = (genM R n).det • (1 : Matrix _ _ _) := by
    rw [cofM, Matrix.submatrix_mul_equiv, ← Matrix.transpose_mul, Matrix.mul_adjugate]
    simp
  have h2 : (cofM R n).det • (genM R n).transpose.submatrix Fin.revPerm id =
      (genM R n).det • (cofM R n).adjugate := by
    have := congrArg (fun M => (cofM R n).adjugate * M) h1
    simpa [← Matrix.mul_assoc, Matrix.adjugate_mul] using this
  have h3 : cofAct R n (cofAct R n (X v)) = (cofM R n).adjugate v.2.rev v.1 := by
    rw [← map_genM, ← AlgHom.map_adjugate]
    simp [cofAct]
  have h4 := congrFun (congrFun h2 v.2.rev) v.1
  rw [h3]
  simpa [genM] using h4.symm

theorem cofAct_cofAct (R : Type) [CommRing R] (n : ℕ) (ν : Fin n → ℕ) (f : MP R n)
    (hf : IsWeightedHomogeneous (colW n n) f ν) :
    (genM R n).det ^ (∑ i, ν i) * cofAct R n (cofAct R n f) = (cofM R n).det ^ (∑ i, ν i) * f := by
  have h1 : cofAct R n (cofAct R n f) = aeval (fun v => cofAct R n (cofAct R n (X v))) f := by
    have : (cofAct R n).comp (cofAct R n) = aeval (fun v => cofAct R n (cofAct R n (X v))) := by
      ext1 v; simp
    exact DFunLike.congr_fun this f
  rw [h1, ← aeval_scale ν f hf]
  simp only [det_mul_cofAct_cofAct_X]
  rw [aeval_scale ν f hf, aeval_X_left_apply]

theorem cofRel_invol (R : Type) [CommRing R] [IsDomain R] (m : ℕ) (ν : Fin (m + 1) → ℕ) (hν : Antitone ν)
    (h0 : ν (Fin.last m) = 0) :
    ∃ ε : ℤˣ, ∀ f ∈ dualWeyl R (m + 1) (m + 1) ν, ∀ g : MP R (m + 1),
      CofRel R m ν f g → CofRel R m (nuDual ν) g ((ε : ℤ) • f) := by
  refine ⟨Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (m + 1))) ^ ν 0, fun f hf g hg => ?_⟩
  have hD : (genM R (m + 1)).det ≠ 0 := Matrix.det_mvPolynomialX_ne_zero (Fin (m + 1)) R
  have hδ : ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (m + 1))) : ℤ) : MP R (m + 1)) ≠ 0 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (m + 1)))) with h | h <;> simp [h]
  have hC : (cofM R (m + 1)).det ≠ 0 := by
    rw [det_cofM]; exact mul_ne_zero hδ (pow_ne_zero _ hD)
  have hle : ν 0 ≤ ∑ i, ν i := Finset.single_le_sum (fun i _ => Nat.zero_le (ν i)) (Finset.mem_univ _)
  have hd0 : nuDual ν 0 = ν 0 := by simp [nuDual, h0]
  have hle' : nuDual ν 0 ≤ ∑ i, nuDual ν i :=
    Finset.single_le_sum (fun i _ => Nat.zero_le (nuDual ν i)) (Finset.mem_univ _)
  have hsum : ∑ i, nuDual ν i + ∑ i, ν i = (m + 1) * ν 0 := by
    rw [← Equiv.sum_comp Fin.revPerm ν, ← Finset.sum_add_distrib]
    have : ∀ i : Fin (m + 1), nuDual ν i + ν (Fin.revPerm i) = ν 0 :=
      fun i => Nat.sub_add_cancel (hν (Fin.zero_le i.rev))
    simp only [this]
    simp
  have hexp : ∑ i, ν i + (∑ i, nuDual ν i - nuDual ν 0) = m * ν 0 := by
    rw [add_mul] at hsum; omega
  have h1 := cofAct_cofAct R (m + 1) ν f hf.1
  unfold CofRel at hg ⊢
  rw [← hg, map_mul, map_pow, cofAct_det] at h1
  obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hle
  have he' : ∑ i, ν i - ν 0 = e := by omega
  rw [he'] at h1
  have h2 : (genM R (m + 1)).det ^ (∑ i, ν i) * cofAct R (m + 1) g = (cofM R (m + 1)).det ^ ν 0 * f := by
    apply mul_left_cancel₀ (pow_ne_zero e hC)
    rw [mul_left_comm, h1, he]
    ring
  apply mul_left_cancel₀ (pow_ne_zero (∑ i, ν i) hD)
  rw [h2, ← mul_assoc, ← pow_add, hexp, det_cofM, mul_pow, pow_mul]
  simp only [Units.val_pow_eq_pow_val, zsmul_eq_mul, Int.cast_pow]
  ring

end GlobalTheory.ValCmp.Invol
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CofactorTwistRelationDualWeightInvolutiveStatement
open MvPolynomial NumberField IsDedekindDomain Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO GlobalTheory.ValCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cofactorTwistRelation_dualWeight_involutive : ∀ (R : Type) [CommRing R] [IsDomain R] (m : ℕ) (ν : Fin (m + 1) → ℕ), Antitone ν → ν (Fin.last m) = 0 → ∃ ε : ℤˣ, ∀ f ∈ dualWeyl R (m + 1) (m + 1) ν, ∀ g : MP R (m + 1), CofRel R m ν f g → CofRel R m (nuDual ν) g ((ε : ℤ) • f) := by
  first | exact @GlobalTheory.ValCmp.Invol.cofRel_invol | exact GlobalTheory.ValCmp.Invol.cofRel_invol | (intros; apply GlobalTheory.ValCmp.Invol.cofRel_invol <;> assumption)
end
end
