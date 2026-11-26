module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IdxDcvFrameAsm

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IdxDChk
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IdxDMatP
noncomputable section

open scoped Classical TensorProduct
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp

namespace PI.UnitaryDimensionFormula

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mat_idem_mul {Rg : Type} [Ring Rg] (E a b : Rg) (hE : E * E = E) (hc : ∀ x : Rg, E * x = x * E) :
    (E * a + (1 - E)) * (E * b + (1 - E)) = E * (a * b) + (1 - E) := by
  have h1 : E * (1 - E) = 0 := by rw [mul_sub, mul_one, hE, sub_self]
  have h2 : (1 - E) * E = 0 := by rw [sub_mul, one_mul, hE, sub_self]
  have h3 : (1 - E) * (1 - E) = 1 - E := by rw [sub_mul, one_mul, h1, sub_zero]
  have e1 : E * a * (E * b) = E * (a * b) := by
    rw [mul_assoc, ← mul_assoc a E b, ← hc a, ← mul_assoc, ← mul_assoc, hE, mul_assoc]
  have e2 : E * a * (1 - E) = 0 := by
    have : a * (1 - E) = (1 - E) * a := by rw [mul_sub, sub_mul, mul_one, one_mul, hc a]
    rw [mul_assoc, this, ← mul_assoc, h1, zero_mul]
  have e3 : (1 - E) * (E * b) = 0 := by rw [← mul_assoc, h2, zero_mul]
  rw [add_mul, mul_add, mul_add, e1, e2, e3, h3, add_zero, zero_add]

theorem mat_lift_core {O : Type} [CommRing O] {k : ℕ} (gO eO wO : O) (he2 : eO * eO = eO) (hw2 : wO * wO = wO)
    (Mo No tt : Matrix (Fin k) (Fin k) O) (htt : ∀ i j, wO * (No * Mo - 1) i j = gO * tt i j)
    (hJ : ∀ m : O, ∃ y : O, eO * (1 + gO * m) * y = eO) :
    ∃ C C' : Matrix (Fin k) (Fin k) O, C' * C = 1 ∧ ∀ i j, (eO * wO) * C i j = (eO * wO) * Mo i j := by
  set Q : Matrix (Fin k) (Fin k) O := 1 + gO • tt with hQdef
  obtain ⟨m, hm⟩ : ∃ m : O, Q.det = 1 + gO * m := by
    have hQ : (Ideal.Quotient.mk (Ideal.span {gO})).mapMatrix Q = 1 := by
      have hπg : Ideal.Quotient.mk (Ideal.span {gO}) gO = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
      rw [hQdef, map_add (f := _), map_one]
      ext i j
      simp [hπg]
    have h1 : Ideal.Quotient.mk (Ideal.span {gO}) (Q.det - 1) = 0 := by
      rw [map_sub, RingHom.map_det, hQ, det_one, map_one, sub_self]
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 h1)
    refine ⟨a, ?_⟩
    rw [mul_comm, ha]; ring
  obtain ⟨yO, hey0⟩ := hJ m
  have hey : eO * Q.det * yO = eO := by rw [hm]; exact hey0
  set εO := eO * wO with hεdef
  set E : Matrix (Fin k) (Fin k) O := εO • 1 with hEdef
  have hEc : ∀ x : Matrix (Fin k) (Fin k) O, E * x = x * E := by
    intro x; simp [hEdef]
  have hε2 : εO * εO = εO := by
    calc εO * εO = (eO * eO) * (wO * wO) := by rw [hεdef]; ring
      _ = εO := by rw [he2, hw2]
  have hE2 : E * E = E := by simp [hEdef, smul_smul, hε2]
  have hEQ : E * (No * Mo) = E * Q := by
    ext i j
    simp only [hEdef, Matrix.smul_mul, one_mul, Matrix.smul_apply, smul_eq_mul, hQdef, Matrix.add_apply]
    have h1 : (No * Mo) i j = (No * Mo - 1) i j + (1 : Matrix (Fin k) (Fin k) O) i j := by
      rw [Matrix.sub_apply]; ring
    have h2 : wO * (gO * tt i j) = gO * tt i j := by
      rw [← htt i j, ← mul_assoc, hw2]
    have key : εO * (No * Mo - 1) i j = εO * (gO • tt) i j := by
     calc εO * (No * Mo - 1) i j = eO * (wO * (No * Mo - 1) i j) := by rw [hεdef]; ring
      _ = eO * (wO * (gO * tt i j)) := by rw [htt i j, h2]
      _ = εO * (gO * tt i j) := by rw [hεdef]; ring
      _ = εO * (gO • tt) i j := by rw [Matrix.smul_apply, smul_eq_mul]
    rw [h1, mul_add, mul_add, key, Matrix.smul_apply, smul_eq_mul]; ring
  set P : Matrix (Fin k) (Fin k) O := yO • Q.adjugate with hPdef
  have hEPQ : E * (P * Q) = E := by
    have : P * Q = (yO * Q.det) • (1 : Matrix (Fin k) (Fin k) O) := by
      rw [hPdef, Matrix.smul_mul, Matrix.adjugate_mul, smul_smul]
    rw [this, hEdef, smul_mul_smul, one_mul]
    congr 1
    calc εO * (yO * Q.det) = wO * (eO * Q.det * yO) := by rw [hεdef]; ring
      _ = εO := by rw [hey, hεdef, mul_comm]
  refine ⟨E * Mo + (1 - E), E * (P * No) + (1 - E), ?_, ?_⟩
  · rw [mat_idem_mul E _ _ hE2 hEc]
    have : E * (P * No * Mo) = E := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc E, hEc P, Matrix.mul_assoc, hEQ, ← Matrix.mul_assoc, ← hEc P,
        Matrix.mul_assoc, hEPQ]
    rw [this, add_sub_cancel]
  · intro i j
    have hEC : E * (E * Mo + (1 - E)) = E * Mo := by
      rw [Matrix.mul_add, ← Matrix.mul_assoc, hE2, Matrix.mul_sub, Matrix.mul_one, hE2, sub_self, add_zero]
    have := congrFun (congrFun hEC i) j
    simpa [hEdef, Matrix.smul_mul] using this

theorem idxDMat_of (hJ : IdxDJacE) : IdxDMat := by
  intro D X TR e he A
  have heO : ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] e) ∈ IntAf X.B.I.F X.B.I.E :=
    Subring.subset_closure (Set.mem_union_right _ ⟨⟨e, he.1⟩, rfl⟩)
  obtain ⟨t, ht, het⟩ := he.2.2.1
  have htO : ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] t) ∈ IntAf X.B.I.F X.B.I.E :=
    Subring.subset_closure (Set.mem_union_right _ ⟨⟨t, ht⟩, rfl⟩)
  let eO : IntAf X.B.I.F X.B.I.E := ⟨_, heO⟩
  let wO : IntAf X.B.I.F X.B.I.E := ⟨X.ew, X.ew_int⟩
  let tO : IntAf X.B.I.F X.B.I.E := ⟨_, htO⟩
  let gO : IntAf X.B.I.F X.B.I.E := X.B.g
  have hgO : ((gO : IntAf X.B.I.F X.B.I.E) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) =
      (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) := by
    simp [gO]
  have kerZ : ∀ x : IntAf X.B.I.F X.B.I.E, (∀ v, TR.res v x = 0) →
      ∃ t : IntAf X.B.I.F X.B.I.E, wO * x = gO * t := by
    intro x hx
    obtain ⟨t, ht, he'⟩ := (TR.res_ker x).1 hx
    refine ⟨⟨t, ht⟩, Subtype.ext ?_⟩
    change X.ew * (x : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) = (gO : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * t
    rw [hgO]; exact he'
  have resG : ∀ v, TR.res v gO = 0 := by
    refine (TR.res_ker gO).2 ⟨X.ew, X.ew_int, ?_⟩
    rw [hgO, mul_comm]
  have heq : eO = 1 - gO * tO := by
    apply Subtype.ext
    change (1 : X.B.I.E) ⊗ₜ[X.B.I.F] e = 1 - (gO : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] t)
    rw [hgO]
    have h1 : e = 1 - (X.B.g : Af X.B.I.F) * t := by rw [← het]; ring
    rw [h1, TensorProduct.tmul_sub]
    congr 1
    rw [← map_natCast (Algebra.TensorProduct.includeRight (R := X.B.I.F) (A := X.B.I.E) (B := Af X.B.I.F)) X.B.g]
    rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  have resE : ∀ v (x : IntAf X.B.I.F X.B.I.E), TR.res v (eO * x) = TR.res v x := by
    intro v x
    rw [heq, sub_mul, one_mul, map_sub, mul_assoc, map_mul, resG, zero_mul, sub_zero]
  have resEps : ∀ v (x : IntAf X.B.I.F X.B.I.E), TR.res v (eO * wO * x) = TR.res v x := by
    intro v x
    rw [mul_assoc, resE]
    exact TR.res_ew v x
  choose a0 ha0 using fun i j => TR.res_joint (fun v => (A v : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) i j)
  choose b0 hb0 using fun i j => TR.res_joint
    (fun v => ((A v)⁻¹ : GL (Fin D.R.k) (TR.Fq v)) i j)
  let Mo : Matrix (Fin D.R.k) (Fin D.R.k) (IntAf X.B.I.F X.B.I.E) := Matrix.of a0
  let No : Matrix (Fin D.R.k) (Fin D.R.k) (IntAf X.B.I.F X.B.I.E) := Matrix.of b0
  have hNM : ∀ v i j, TR.res v ((No * Mo - 1) i j) = 0 := by
    intro v i j
    have hM : (TR.res v).mapMatrix Mo = (A v : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) := by
      ext i j; exact congrFun (ha0 i j) v
    have hN : (TR.res v).mapMatrix No = ((A v)⁻¹ : GL (Fin D.R.k) (TR.Fq v)) := by
      ext i j; exact congrFun (hb0 i j) v
    have : (TR.res v).mapMatrix (No * Mo - 1) = 0 := by
      rw [map_sub, map_mul, map_one, hM, hN, ← Units.val_mul, inv_mul_cancel, Units.val_one, sub_self]
    exact congrFun (congrFun this i) j
  choose tt htt using fun i j => kerZ _ (fun v => hNM v i j)
  have hw2 : wO * wO = wO := Subtype.ext X.ew_idem
  have he2 : eO * eO = eO := Subtype.ext (by
    change ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] e) * ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] e) = (1 : X.B.I.E) ⊗ₜ[X.B.I.F] e
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, he.2.1])
  have hJO : ∀ m : IntAf X.B.I.F X.B.I.E, ∃ y : IntAf X.B.I.F X.B.I.E, eO * (1 + gO * m) * y = eO := by
    intro m
    obtain ⟨y, hy, hyeq⟩ := hJ X.B.I.F X.B.I.E X.B.g e he (m : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) m.2
    refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
    change ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] e) * (1 + (gO : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * m) * y =
      (1 : X.B.I.E) ⊗ₜ[X.B.I.F] e
    rw [hgO]; exact hyeq
  obtain ⟨CO, C'O, hCC, hent⟩ := mat_lift_core gO eO wO he2 hw2 Mo No (Matrix.of tt) (fun i j => htt i j) hJO
  refine ⟨CO.map (IntAf X.B.I.F X.B.I.E).subtype, C'O.map (IntAf X.B.I.F X.B.I.E).subtype, ?_,
    fun i j => ⟨(CO i j).2, (C'O i j).2⟩, ?_⟩
  · rw [← Matrix.map_mul, hCC, Matrix.map_one _ (map_zero _) (map_one _)]
  · intro v i j
    have hmem : epsX X e * (CO.map (IntAf X.B.I.F X.B.I.E).subtype) i j ∈ IntAf X.B.I.F X.B.I.E :=
      (eO * wO * CO i j).2
    unfold resT
    rw [dite_eq_left hmem]
    have : (⟨epsX X e * (CO.map (IntAf X.B.I.F X.B.I.E).subtype) i j, hmem⟩ : IntAf X.B.I.F X.B.I.E) =
        eO * wO * Mo i j := by
      rw [← hent i j]; rfl
    rw [this, resEps]
    exact congrFun (ha0 i j) v

end PI.UnitaryDimensionFormula
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IdxKLevi
noncomputable section

open scoped Classical TensorProduct
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp

namespace PI.UnitaryDimensionFormula

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section AlgL

variable {A : Type} [CommRing A] (σ : A →+* A) {n k : ℕ} (J : Matrix (Fin n) (Fin n) A)

end AlgL

section Main

variable {D : D7} {X : HidaSetting D}

theorem tmul_one_mem {e : Af X.B.I.F} (he : e ∈ Formalism.UG.intAd X.B.I.F) :
    ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] e) ∈ IntAf X.B.I.F X.B.I.E :=
  Subring.subset_closure (Or.inr ⟨⟨e, he⟩, rfl⟩)

theorem resT_congr (TR : TypedRed X) (v : TR.Pl) {x y : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F}
    (hy : y ∈ IntAf X.B.I.F X.B.I.E) (hZ : ZMod' X.B.I X.B.g (x - y)) : resT TR v x = resT TR v y := by
  obtain ⟨t, ht, hxy⟩ := hZ
  have hg : ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ∈ IntAf X.B.I.F X.B.I.E :=
    natCast_mem _ _
  have hgt : (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * t ∈ IntAf X.B.I.F X.B.I.E :=
    (IntAf X.B.I.F X.B.I.E).mul_mem hg ht
  have hx : x = y + (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * t := sub_eq_iff_eq_add'.1 hxy
  have hxm : x ∈ IntAf X.B.I.F X.B.I.E := hx ▸ (IntAf X.B.I.F X.B.I.E).add_mem hy hgt
  have h0 : TR.res v ⟨_, hgt⟩ = 0 := by
    refine (TR.res_ker ⟨_, hgt⟩).2 ?_ v
    exact ⟨X.ew * t, (IntAf X.B.I.F X.B.I.E).mul_mem X.ew_int ht, mul_left_comm _ _ _⟩
  have hsplit : (⟨x, hxm⟩ : IntAf X.B.I.F X.B.I.E) = ⟨y, hy⟩ + ⟨_, hgt⟩ := Subtype.ext hx
  simp only [resT, dif_pos hxm, dif_pos hy]
  rw [hsplit, map_add (TR.res v), h0, add_zero]

theorem idxDLevi : IdxDLevi := by
  intro D X TR e he b bs hF hL hC C C' _ hCint v i j
  have hew := X.ew_int
  have hbwd : ∀ l, X.bwd l ∈ X.B.I.Lf := fun l => (X.vectorsInLattice.2.2 l).2
  have he1 : ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] e) ∈ IntAf X.B.I.F X.B.I.E := tmul_one_mem he.1
  have hεint : epsX X e * C i j ∈ IntAf X.B.I.F X.B.I.E := mul_mem (mul_mem he1 hew) (hCint i j).1
  apply resT_congr TR v hεint
  have hh : ∀ x y : VA X.B.I, Formalism.UG.hform (sigA X.B.I) (JA X.B.I) x y = hA X.B.I x y := fun _ _ => rfl
  have hsig1 : sigA X.B.I ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] e) = (1 : X.B.I.E) ⊗ₜ[X.B.I.F] e := by
    rw [unitaryCongruence.sigA_tmul, star_one]
  have hzero : ∀ q, hA X.B.I (b q) (X.bw j) = 0 := by
    intro q
    rw [hF.2.2.1 q, X.bw_w j, unitaryCongruence.hA_smul_left, unitaryCongruence.hA_smul_right]
    unfold epsX
    rw [map_mul, hsig1]
    have := X.ew_orth
    linear_combination ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] e) * hA X.B.I (b q) (X.bw j) * this
  have hexp : hA X.B.I (X.bwd i) (sMat (sigA X.B.I) (JA X.B.I) b bs C (C'.map (sigA X.B.I))ᵀ *ᵥ X.bw j) =
      hA X.B.I (X.bwd i) (X.bw j) +
        ∑ p, ∑ q, (C - 1) p q * hA X.B.I (bs q) (X.bw j) * hA X.B.I (X.bwd i) (b p) := by
    rw [sMat_mulVec]
    simp only [hh]
    rw [← unitaryCongruence.hL_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_add (f := _), map_sum, map_smul, unitaryCongruence.hL_apply, smul_eq_mul, hzero, mul_zero, zero_mul,
      add_zero]
  rw [hexp]
  have hCm : ∀ p q, (C - 1) p q ∈ IntAf X.B.I.F X.B.I.E := by
    intro p q
    rw [Matrix.sub_apply, Matrix.one_apply]
    refine sub_mem (hCint p q).1 ?_
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  set S1 := ∑ p, ∑ q, (C - 1) p q * hA X.B.I (bs q) (X.bw j) * hA X.B.I (X.bwd i) (b p) with hS1
  set S2 := ∑ p, ∑ q, (C - 1) p q * ((if q = j then X.ew else 0) * (if i = p then X.ew else 0)) with hS2
  have key1 : ZMod' X.B.I X.B.g (S1 - S2) := by
    have eq : S1 - S2 = ∑ p, ∑ q, (C - 1) p q * (hA X.B.I (bs q) (X.bw j) * hA X.B.I (X.bwd i) (b p) -
        (if q = j then X.ew else 0) * (if i = p then X.ew else 0)) := by
      rw [hS1, hS2]
      simp only [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
      ring
    rw [eq]
    refine unitaryCongruence.Z_sum X.B.I X.B.g _ _ fun p _ => unitaryCongruence.Z_sum X.B.I X.B.g _ _ fun q _ => ?_
    refine unitaryCongruence.Z_smul X.B.I X.B.g (hCm p q) ?_
    have eq2 : hA X.B.I (bs q) (X.bw j) * hA X.B.I (X.bwd i) (b p) -
        (if q = j then X.ew else 0) * (if i = p then X.ew else 0) =
        hA X.B.I (X.bwd i) (b p) * (hA X.B.I (bs q) (X.bw j) - if q = j then X.ew else 0) +
        (if q = j then X.ew else 0) * (hA X.B.I (X.bwd i) (b p) - if i = p then X.ew else 0) := by ring
    rw [eq2]
    refine unitaryCongruence.Z_add X.B.I X.B.g (unitaryCongruence.Z_smul X.B.I X.B.g
      (unitaryCongruence.hA_int X.B.I (hbwd i) (hL p).1) (hC q j).1) (unitaryCongruence.Z_smul X.B.I X.B.g ?_ (hC i p).2)
    split_ifs
    · exact hew
    · exact zero_mem _
  have hsum : S2 = (C - 1) i j * X.ew := by
    rw [hS2]
    simp [mul_ite, ite_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', X.ew_idem]
  obtain ⟨t, ht, het⟩ := he.2.2.1
  have hlast : ZMod' X.B.I X.B.g ((if i = j then X.ew else 0) + (C - 1) i j * X.ew - epsX X e * C i j) := by
    refine ⟨((1 : X.B.I.E) ⊗ₜ[X.B.I.F] t) * X.ew * C i j,
      mul_mem (mul_mem (tmul_one_mem ht) hew) (hCint i j).1, ?_⟩
    have hg : (1 : X.B.I.E) ⊗ₜ[X.B.I.F] ((X.B.g : Af X.B.I.F)) = (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) := by
      rw [← Algebra.TensorProduct.includeRight_apply (R := X.B.I.F) (A := X.B.I.E), map_natCast]
    have h1 : (1 : X.B.I.E) ⊗ₜ[X.B.I.F] (1 - e) =
        (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] t) := by
      rw [het, ← hg, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    have h2 : (1 : X.B.I.E) ⊗ₜ[X.B.I.F] (1 - e) = 1 - (1 : X.B.I.E) ⊗ₜ[X.B.I.F] e := by
      rw [TensorProduct.tmul_sub, Algebra.TensorProduct.one_def]
    have h3 : (1 : X.B.I.E) ⊗ₜ[X.B.I.F] e =
        1 - (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] t) := by
      rw [← h1, h2]; ring
    unfold epsX
    rw [Matrix.sub_apply, Matrix.one_apply, h3]
    split_ifs <;> ring
  have eqF : hA X.B.I (X.bwd i) (X.bw j) + S1 - epsX X e * C i j =
      (hA X.B.I (X.bwd i) (X.bw j) - if i = j then X.ew else 0) + (S1 - S2) + (S2 - (C - 1) i j * X.ew) +
        ((if i = j then X.ew else 0) + (C - 1) i j * X.ew - epsX X e * C i j) := by ring
  have h0 : S2 - (C - 1) i j * X.ew = 0 := by rw [hsum, sub_self]
  rw [eqF, h0, add_zero]
  exact unitaryCongruence.Z_add X.B.I X.B.g (unitaryCongruence.Z_add X.B.I X.B.g (X.bw_dual i j) key1) hlast

end Main

end PI.UnitaryDimensionFormula
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IdxDAdP
noncomputable section

open scoped Classical TensorProduct
open NumberField IsDedekindDomain

namespace PI.UnitaryDimensionFormula

section
variable {F : Type} [Field F] [NumberField F]

theorem adAd_natCast_apply (g : ℕ) (v : HeightOneSpectrum (𝓞 F)) :
    (g : FiniteAdeleRing (𝓞 F) F) v = (g : v.adicCompletion F) :=
  map_natCast (Formalism.UG.evalV F v) g

theorem adAd_val_g (g : ℕ) (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v (g : v.adicCompletion F) = v.intValuation (g : 𝓞 F) := by
  have e1 : (g : v.adicCompletion F) = ((g : F) : v.adicCompletion F) := by
    exact (map_natCast (algebraMap F (v.adicCompletion F)) g).symm
  rw [e1, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  have e2 : (g : F) = algebraMap (𝓞 F) F (g : 𝓞 F) := (map_natCast _ g).symm
  rw [e2, HeightOneSpectrum.valuation_of_algebraMap]

theorem adAd_val_lt (g : ℕ) (v : HeightOneSpectrum (𝓞 F)) (h : (g : 𝓞 F) ∈ v.asIdeal) :
    Valued.v (g : v.adicCompletion F) < 1 := by
  rw [adAd_val_g]; exact (v.intValuation_lt_one_iff_mem _).2 h

theorem adAd_val_one (g : ℕ) (v : HeightOneSpectrum (𝓞 F)) (h : (g : 𝓞 F) ∉ v.asIdeal) :
    Valued.v (g : v.adicCompletion F) = 1 := by
  rw [adAd_val_g]
  exact (v.intValuation_eq_one_iff_mem_primeCompl _).2 h

def adOfInt (f : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (hf : ∀ v, f v ∈ v.adicCompletionIntegers F) : FiniteAdeleRing (𝓞 F) F :=
  ⟨f, Filter.Eventually.of_forall hf⟩

theorem adOfInt_int (f : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (hf : ∀ v, f v ∈ v.adicCompletionIntegers F) : adOfInt f hf ∈ Formalism.UG.intAd F := hf

end

theorem idxDAd : IdxDAd := by
  intro F _ _ g
  let P : HeightOneSpectrum (𝓞 F) → Prop := fun v => (g : 𝓞 F) ∈ v.asIdeal
  have h01 : ∀ v : HeightOneSpectrum (𝓞 F),
      (if P v then (1 : v.adicCompletion F) else 0) ∈ v.adicCompletionIntegers F := by
    intro v; split_ifs
    · exact one_mem _
    · exact zero_mem _
  let e := adOfInt (fun v => if P v then (1 : v.adicCompletion F) else 0) h01
  refine ⟨e, adOfInt_int _ _, ?_, ?_, ?_⟩
  · refine FiniteAdeleRing.ext _ fun v => ?_
    show (if P v then (1 : v.adicCompletion F) else 0) * (if P v then 1 else 0) = if P v then 1 else 0
    split_ifs <;> simp
  · have ht : ∀ v : HeightOneSpectrum (𝓞 F),
        (if P v then (0 : v.adicCompletion F) else (g : v.adicCompletion F)⁻¹) ∈ v.adicCompletionIntegers F := by
      intro v
      split_ifs with hv
      · exact zero_mem _
      · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, adAd_val_one g v hv, inv_one]
    refine ⟨adOfInt _ ht, adOfInt_int _ _, ?_⟩
    refine FiniteAdeleRing.ext _ fun v => ?_
    show (1 : v.adicCompletion F) - (if P v then 1 else 0) =
      (g : FiniteAdeleRing (𝓞 F) F) v * (if P v then 0 else (g : v.adicCompletion F)⁻¹)
    rw [adAd_natCast_apply]
    split_ifs with hv
    · simp
    · have hne : (g : v.adicCompletion F) ≠ 0 := by
        intro h0
        have := adAd_val_one g v hv
        rw [h0, map_zero] at this
        exact zero_ne_one this
      rw [sub_zero, mul_inv_cancel₀ hne]
  · intro c hc
    have hu : ∀ v : HeightOneSpectrum (𝓞 F), P v →
        Valued.v (1 + (g : v.adicCompletion F) * c v) = 1 := by
      intro v hv
      have hlt : Valued.v ((g : v.adicCompletion F) * c v) < 1 := by
        rw [map_mul]
        have hcv : Valued.v (c v) ≤ 1 := hc v
        calc Valued.v (g : v.adicCompletion F) * Valued.v (c v) ≤ Valued.v (g : v.adicCompletion F) * 1 :=
              mul_le_mul' le_rfl hcv
          _ < 1 := by rw [mul_one]; exact adAd_val_lt g v hv
      rw [Valuation.map_add_eq_of_lt_left _ (by rw [map_one]; exact hlt), map_one]
    have hy : ∀ v : HeightOneSpectrum (𝓞 F),
        (if P v then (1 + (g : v.adicCompletion F) * c v)⁻¹ else 0) ∈ v.adicCompletionIntegers F := by
      intro v
      split_ifs with hv
      · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hu v hv, inv_one]
      · exact zero_mem _
    refine ⟨adOfInt _ hy, adOfInt_int _ _, ?_⟩
    refine FiniteAdeleRing.ext _ fun v => ?_
    show (if P v then (1 : v.adicCompletion F) else 0) * (1 + (g : FiniteAdeleRing (𝓞 F) F) v * c v) *
      (if P v then (1 + (g : v.adicCompletion F) * c v)⁻¹ else 0) = if P v then 1 else 0
    rw [adAd_natCast_apply]
    split_ifs with hv
    · have hne : (1 + (g : v.adicCompletion F) * c v) ≠ 0 := by
        intro h0
        have := hu v hv
        rw [h0, map_zero] at this
        exact zero_ne_one this
      rw [one_mul, mul_inv_cancel₀ hne]
    · simp

end PI.UnitaryDimensionFormula
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IdxADAlg
noncomputable section

open Matrix

namespace PI.UnitaryDimensionFormula

section DAlg

variable {A : Type} [CommRing A] (σ : A →+* A) {n k : ℕ} (J : Matrix (Fin n) (Fin n) A)

def daB (x : Fin k → Fin n → A) : Matrix (Fin n) (Fin k) A := Matrix.of fun p i => x i p

def daP (x y : Fin k → Fin n → A) (M : Matrix (Fin k) (Fin k) A) : Matrix (Fin n) (Fin n) A :=
  daB x * M * (Formalism.UG.cT σ (daB y) * J)

def daT (x y : Fin k → Fin n → A) (M : Matrix (Fin k) (Fin k) A) : Matrix (Fin n) (Fin n) A :=
  J * daB x * M * (Formalism.UG.cT σ (daB y) * J)

theorem da_gram (x y : Fin k → Fin n → A) (i j : Fin k) :
    (Formalism.UG.cT σ (daB x) * J * daB y) i j = Formalism.UG.hform σ J (x i) (y j) := by
  simp only [Matrix.mul_apply, Formalism.UG.cT, Formalism.UG.hform, daB, Matrix.transpose_apply, Matrix.map_apply,
    Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem da_mulVec (y : Fin k → Fin n → A) (v : Fin n → A) (i : Fin k) :
    ((Formalism.UG.cT σ (daB y) * J) *ᵥ v) i = Formalism.UG.hform σ J (y i) v := by
  simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Formalism.UG.cT, Formalism.UG.hform, daB, Matrix.transpose_apply,
    Matrix.map_apply, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem da_row (y : Fin k → Fin n → A) (j : Fin k) (q : Fin n) :
    (Formalism.UG.cT σ (daB y) * J) j q = hrow σ J (y j) q := by
  simp only [Matrix.mul_apply, Formalism.UG.cT, hrow, daB, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply]

theorem da_sum (x y : Fin k → Fin n → A) (M : Matrix (Fin k) (Fin k) A) :
    ∑ i, ∑ j, M i j • Matrix.vecMulVec (x i) (hrow σ J (y j)) = daP σ J x y M := by
  ext p q
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul, daP, Matrix.mul_apply,
    da_row, daB, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by
    simp only [hrow, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply]
    ring

theorem da_sMat (b bs : Fin k → Fin n → A) (C D : Matrix (Fin k) (Fin k) A) :
    sMat σ J b bs C D = 1 + daP σ J b bs (C - 1) + daP σ J bs b (D - 1) := by
  unfold sMat
  simp only [Finset.sum_add_distrib, da_sum, add_assoc]

variable {σ}

theorem da_cT_cT (hσ : ∀ a, σ (σ a) = a) {m p : Type} (M : Matrix m p A) :
    Formalism.UG.cT σ (Formalism.UG.cT σ M) = M := by
  ext i j
  simp [Formalism.UG.cT, hσ]

theorem da_cT_add {m p : Type} (M N : Matrix m p A) :
    Formalism.UG.cT σ (M + N) = Formalism.UG.cT σ M + Formalism.UG.cT σ N := by
  ext i j
  simp [Formalism.UG.cT]

theorem da_cT_sub {m p : Type} (M N : Matrix m p A) :
    Formalism.UG.cT σ (M - N) = Formalism.UG.cT σ M - Formalism.UG.cT σ N := by
  ext i j
  simp [Formalism.UG.cT]

theorem da_herm (hσ : ∀ a, σ (σ a) = a) (hJ : Formalism.UG.IsHerm σ J) (x y : Fin n → A) :
    Formalism.UG.hform σ J x y = σ (Formalism.UG.hform σ J y x) := by
  have hJ' : ∀ i j, σ (J i j) = J j i := fun i j => by
    have h := congrFun (congrFun hJ j) i
    simpa [Formalism.UG.cT] using h
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Formalism.UG.hform, map_sum, map_mul, hσ, hJ']
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem da_smul_l (c : A) (x y : Fin n → A) :
    Formalism.UG.hform σ J (c • x) y = σ c * Formalism.UG.hform σ J x y := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem da_smul_r (c : A) (x y : Fin n → A) :
    Formalism.UG.hform σ J x (c • y) = c * Formalism.UG.hform σ J x y := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem da_smulB (c : A) (x : Fin k → Fin n → A) (hx : ∀ i, x i = c • x i) : c • daB x = daB x := by
  ext p i
  simp only [daB, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  exact (congrFun (hx i) p).symm

theorem da_PP (x y : Fin k → Fin n → A) (c : A) (hm : Formalism.UG.cT σ (daB y) * J * daB x = c • 1)
    (hx : c • daB x = daB x) (M N : Matrix (Fin k) (Fin k) A) :
    daP σ J x y M * daP σ J x y N = daP σ J x y (M * N) := by
  unfold daP
  calc daB x * M * (Formalism.UG.cT σ (daB y) * J) * (daB x * N * (Formalism.UG.cT σ (daB y) * J))
        = daB x * M * (Formalism.UG.cT σ (daB y) * J * daB x) * N * (Formalism.UG.cT σ (daB y) * J) := by
          simp only [Matrix.mul_assoc]
    _ = (c • daB x) * (M * N) * (Formalism.UG.cT σ (daB y) * J) := by
          rw [hm]
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.mul_assoc]
    _ = daB x * (M * N) * (Formalism.UG.cT σ (daB y) * J) := by rw [hx]

theorem parabolic_product_zero (x y x' y' : Fin k → Fin n → A) (hm : Formalism.UG.cT σ (daB y) * J * daB x' = 0)
    (M N : Matrix (Fin k) (Fin k) A) :
    daP σ J x y M * daP σ J x' y' N = 0 := by
  unfold daP
  calc daB x * M * (Formalism.UG.cT σ (daB y) * J) * (daB x' * N * (Formalism.UG.cT σ (daB y') * J))
        = daB x * M * (Formalism.UG.cT σ (daB y) * J * daB x') * N * (Formalism.UG.cT σ (daB y') * J) := by
          simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hm]; simp

theorem da_P_add (x y : Fin k → Fin n → A) (M N : Matrix (Fin k) (Fin k) A) :
    daP σ J x y (M + N) = daP σ J x y M + daP σ J x y N := by
  unfold daP
  simp only [Matrix.mul_add, Matrix.add_mul]

private theorem cT_mul_lemma {m p q : Type} [Fintype p] (X : Matrix m p A) (Y : Matrix p q A) :
    Formalism.UG.cT σ (X * Y) = Formalism.UG.cT σ Y * Formalism.UG.cT σ X := by
  simp only [Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]

theorem da_cTP (hσ : ∀ a, σ (σ a) = a) (hJ : Formalism.UG.IsHerm σ J) (x y : Fin k → Fin n → A)
    (M : Matrix (Fin k) (Fin k) A) :
    Formalism.UG.cT σ (daP σ J x y M) * J = daT σ J y x (Formalism.UG.cT σ M) := by
  unfold daP daT
  simp only [cT_mul_lemma]
  rw [da_cT_cT hσ, show Formalism.UG.cT σ J = J from hJ]
  simp only [Matrix.mul_assoc]

theorem da_JP (x y : Fin k → Fin n → A) (M : Matrix (Fin k) (Fin k) A) :
    J * daP σ J x y M = daT σ J x y M := by
  unfold daP daT
  simp only [Matrix.mul_assoc]

theorem da_TP (x y x' y' : Fin k → Fin n → A) (c : A)
    (hm : Formalism.UG.cT σ (daB x) * J * daB x' = c • 1) (hy : c • daB y = daB y) (M N : Matrix (Fin k) (Fin k) A) :
    daT σ J y x M * daP σ J x' y' N = daT σ J y y' (M * N) := by
  unfold daT daP
  calc J * daB y * M * (Formalism.UG.cT σ (daB x) * J) * (daB x' * N * (Formalism.UG.cT σ (daB y') * J))
        = J * daB y * M * (Formalism.UG.cT σ (daB x) * J * daB x') * N * (Formalism.UG.cT σ (daB y') * J) := by
          simp only [Matrix.mul_assoc]
    _ = J * (c • daB y) * (M * N) * (Formalism.UG.cT σ (daB y') * J) := by
          rw [hm]
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.mul_assoc]
    _ = J * daB y * (M * N) * (Formalism.UG.cT σ (daB y') * J) := by rw [hy]

theorem transfer_product_zero (x y x' y' : Fin k → Fin n → A)
    (hm : Formalism.UG.cT σ (daB x) * J * daB x' = 0) (M N : Matrix (Fin k) (Fin k) A) :
    daT σ J y x M * daP σ J x' y' N = 0 := by
  unfold daT daP
  calc J * daB y * M * (Formalism.UG.cT σ (daB x) * J) * (daB x' * N * (Formalism.UG.cT σ (daB y') * J))
        = J * daB y * M * (Formalism.UG.cT σ (daB x) * J * daB x') * N * (Formalism.UG.cT σ (daB y') * J) := by
          simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hm]; simp

end DAlg

theorem idxDAlg : IdxDAlg := by
  intro A _ σ n k J ε b bs hσ hJ hfr
  obtain ⟨hεε, hεσ, hb, hbs, hbb⟩ := hfr
  have hx1 : ε • daB b = daB b := da_smulB ε b hb
  have hx2 : σ ε • daB bs = daB bs := da_smulB (σ ε) bs hbs
  have hm1 : Formalism.UG.cT σ (daB bs) * J * daB b = ε • (1 : Matrix (Fin k) (Fin k) A) := by
    ext i j
    rw [da_gram, hbb i j, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp
  have hm2 : Formalism.UG.cT σ (daB b) * J * daB bs = σ ε • (1 : Matrix (Fin k) (Fin k) A) := by
    ext i j
    rw [da_gram, da_herm J hσ hJ, hbb j i, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    by_cases h : i = j
    · subst h
      simp
    · simp [h, Ne.symm h]
  have hm3 : Formalism.UG.cT σ (daB bs) * J * daB bs = 0 := by
    ext i j
    rw [da_gram, Matrix.zero_apply, hbs i, hbs j, da_smul_l, da_smul_r, hσ, ← mul_assoc, hεσ, zero_mul]
  have hm4 : Formalism.UG.cT σ (daB b) * J * daB b = 0 := by
    ext i j
    rw [da_gram, Matrix.zero_apply, hb i, hb j, da_smul_l, da_smul_r, ← mul_assoc, mul_comm (σ ε) ε, hεσ,
      zero_mul]
  have hPP : ∀ M N, daP σ J b bs M * daP σ J b bs N = daP σ J b bs (M * N) :=
    fun M N => da_PP J b bs ε hm1 hx1 M N
  have hQQ : ∀ M N, daP σ J bs b M * daP σ J bs b N = daP σ J bs b (M * N) :=
    fun M N => da_PP J bs b (σ ε) hm2 hx2 M N
  have hPQ : ∀ M N, daP σ J b bs M * daP σ J bs b N = 0 := fun M N => parabolic_product_zero J b bs bs b hm3 M N
  have hQP : ∀ M N, daP σ J bs b M * daP σ J b bs N = 0 := fun M N => parabolic_product_zero J bs b b bs hm4 M N
  have hc1 : Formalism.UG.cT σ (1 : Matrix (Fin k) (Fin k) A) = 1 := by
    unfold Formalism.UG.cT
    rw [Matrix.map_one σ (map_zero σ) (map_one σ), Matrix.transpose_one]
  have hc1n : Formalism.UG.cT σ (1 : Matrix (Fin n) (Fin n) A) = 1 := by
    unfold Formalism.UG.cT
    rw [Matrix.map_one σ (map_zero σ) (map_one σ), Matrix.transpose_one]
  have hTadd : ∀ (x y : Fin k → Fin n → A) (M N : Matrix (Fin k) (Fin k) A),
      daT σ J x y (M + N) = daT σ J x y M + daT σ J x y N := by
    intro x y M N
    unfold daT
    simp only [Matrix.mul_add, Matrix.add_mul]
  have hT0 : ∀ x y : Fin k → Fin n → A, daT σ J x y 0 = 0 := by
    intro x y
    unfold daT
    simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro C D y hy
    have h0 : ∀ (x y' : Fin k → Fin n → A) (M : Matrix (Fin k) (Fin k) A),
        (∀ j, Formalism.UG.hform σ J (y' j) y = 0) → daP σ J x y' M *ᵥ y = 0 := by
      intro x y' M hz
      unfold daP
      rw [← Matrix.mulVec_mulVec]
      have hz' : (Formalism.UG.cT σ (daB y') * J) *ᵥ y = 0 := by
        ext i
        rw [da_mulVec]
        exact hz i
      rw [hz', Matrix.mulVec_zero]
    rw [da_sMat, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
      h0 b bs _ (fun j => (hy j).2), h0 bs b _ (fun j => (hy j).1), add_zero, add_zero]
  · intro C₁ D₁ C₂ D₂
    rw [da_sMat, da_sMat, da_sMat]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hPP, hQQ, hPQ, hQP,
      add_zero]
    rw [show C₁ * C₂ - 1 = (C₁ - 1) + (C₂ - 1) + (C₁ - 1) * (C₂ - 1) by noncomm_ring,
      show D₁ * D₂ - 1 = (D₁ - 1) + (D₂ - 1) + (D₁ - 1) * (D₂ - 1) by noncomm_ring,
      da_P_add, da_P_add, da_P_add, da_P_add]
    abel
  · intro C D hC hD
    have hP : daP σ J b bs (C - 1) = 0 := by
      unfold daP
      rw [← hx1, Matrix.smul_mul, ← Matrix.mul_smul, hC]
      simp
    have hQ : daP σ J bs b (D - 1) = 0 := by
      unfold daP
      rw [← hx2, Matrix.smul_mul, ← Matrix.mul_smul, hD]
      simp
    rw [da_sMat, hP, hQ, add_zero, add_zero]
  · intro C C' hCC
    have hDt : (C'.map σ)ᵀ = Formalism.UG.cT σ C' := rfl
    rw [hDt, da_sMat]
    have hZ1 : (C - 1) + Formalism.UG.cT σ (Formalism.UG.cT σ C' - 1) + Formalism.UG.cT σ (Formalism.UG.cT σ C' - 1) * (C - 1) = 0 := by
      rw [da_cT_sub, da_cT_cT hσ, hc1,
        show C - 1 + (C' - 1) + (C' - 1) * (C - 1) = C' * C - 1 by noncomm_ring, hCC, sub_self]
    have hZ2 : (Formalism.UG.cT σ C' - 1) + Formalism.UG.cT σ (C - 1) + Formalism.UG.cT σ (C - 1) * (Formalism.UG.cT σ C' - 1) = 0 := by
      rw [da_cT_sub, hc1,
        show Formalism.UG.cT σ C' - 1 + (Formalism.UG.cT σ C - 1) + (Formalism.UG.cT σ C - 1) * (Formalism.UG.cT σ C' - 1) =
          Formalism.UG.cT σ C * Formalism.UG.cT σ C' - 1 by noncomm_ring,
        ← cT_mul_lemma, hCC, hc1, sub_self]
    calc Formalism.UG.cT σ (1 + daP σ J b bs (C - 1) + daP σ J bs b (Formalism.UG.cT σ C' - 1)) * J *
          (1 + daP σ J b bs (C - 1) + daP σ J bs b (Formalism.UG.cT σ C' - 1))
        = J + daT σ J b bs ((C - 1) + Formalism.UG.cT σ (Formalism.UG.cT σ C' - 1) +
              Formalism.UG.cT σ (Formalism.UG.cT σ C' - 1) * (C - 1)) +
            daT σ J bs b ((Formalism.UG.cT σ C' - 1) + Formalism.UG.cT σ (C - 1) +
              Formalism.UG.cT σ (C - 1) * (Formalism.UG.cT σ C' - 1)) := by
          rw [da_cT_add, da_cT_add, hc1n]
          simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, da_cTP J hσ hJ, da_JP,
            da_TP J b bs bs b (σ ε) hm2 hx2, da_TP J bs b b bs ε hm1 hx1, transfer_product_zero J b bs b bs hm4,
            transfer_product_zero J bs b bs b hm3, add_zero, hTadd]
          abel
      _ = J := by rw [hZ1, hZ2, hT0, hT0, add_zero, add_zero]

end PI.UnitaryDimensionFormula
end
end

namespace PI.UnitaryDimensionFormula

theorem idxSurj_of_frame (hFr : IdxDFrame) : IdxSurj :=
  idxSurj_of idxDAlg idxDAd idxDInt idxDSig hFr (idxDMat_of idxDJacE) idxDLevi

end PI.UnitaryDimensionFormula
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IdxKHom
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.UnitriangularReductionOfMemLevel
noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  PI.UnitaryDimensionFormula.unitaryCongruence

namespace PI.UnitaryDimensionFormula.NormCutK

section NCongS

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

end NCongS

section K2iff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (TR : TypedRed X)

theorem res_ew_one (v : TR.Pl) : TR.res v ⟨X.ew, X.ew_int⟩ = 1 := by
  calc TR.res v ⟨X.ew, X.ew_int⟩
      = TR.res v ⟨X.ew * ((1 : IntAf X.B.I.F X.B.I.E) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F),
          (IntAf X.B.I.F X.B.I.E).mul_mem X.ew_int (1 : IntAf X.B.I.F X.B.I.E).2⟩ := by
        congr 1
        ext
        simp
    _ = TR.res v 1 := TR.res_ew v 1
    _ = 1 := map_one _

theorem res_of_Z_delta (v : TR.Pl) {c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (hc : c ∈ IntAf X.B.I.F X.B.I.E) (b : Prop)
    [Decidable b] (hZ : ZMod' X.B.I X.B.g (c - if b then X.ew else 0)) :
    TR.res v ⟨c, hc⟩ = if b then 1 else 0 := by
  by_cases hb : b
  · rw [if_pos hb] at hZ ⊢
    have hmem : c - X.ew ∈ IntAf X.B.I.F X.B.I.E := sub_mem hc X.ew_int
    have hk := (TR.res_ker ⟨c - X.ew, hmem⟩).mpr (Z_smul X.B.I X.B.g X.ew_int hZ) v
    have e : (⟨c - X.ew, hmem⟩ : IntAf X.B.I.F X.B.I.E) = ⟨c, hc⟩ - ⟨X.ew, X.ew_int⟩ := rfl
    rw [e, map_sub, res_ew_one, sub_eq_zero] at hk
    exact hk
  · rw [if_neg hb, sub_zero] at hZ
    rw [if_neg hb]
    exact (TR.res_ker ⟨c, hc⟩).mpr (Z_smul X.B.I X.B.g X.ew_int hZ) v

theorem unitriangular_reduction_of_mem_level {x : X.B.I.Gf} (hx : Good X x) (hk : x ∈ X.K2) (v : TR.Pl) :
    Formalism.L2.SG.GGMirabolic.IsUni D.R.k (levi TR x v) := by
  obtain ⟨hK, -, -, hc3⟩ := hk
  have hbwd : ∀ i, X.bwd i ∈ X.B.I.Lf := fun i => (X.vectorsInLattice.2.2 i).2
  have hbb : ∀ i j : Fin D.R.k, i ≠ j → ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (X.bw j)) := by
    intro i j hij
    have h := X.bw_dual i j
    rwa [if_neg hij, sub_zero] at h
  have key : ∀ i j : Fin D.R.k, j ≤ i → leviM TR x v i j = if i = j then 1 else 0 := by
    intro i j hji
    have hmv : X.B.I.fmat x *ᵥ X.bw j ∈ X.B.I.Lf := K_mv X.B.I hK (X.vectorsInLattice.2.2 j).1
    have hc : hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw j) ∈ IntAf X.B.I.F X.B.I.E :=
      hA_int X.B.I (hbwd i) hmv
    have hsub : Mo X.B.I X.B.g (Set.range X.e0 ∪ X.bw '' {l | l.1 < j.1}) ≤ Qs X.B.I X.B.g (X.bwd i) :=
      le_trans (Mo_mono X.B.I (Set.union_subset_union_right _
          (Set.image_mono (lt_sub (Fin.le_iff_val_le_val.mp hji)))))
        (Mb_Q X.B.I X.B.g X.e0 X.bw X.bwd hbwd (fun i a => dual_beta_reference_congruence i a) hbb i)
    have h2 : ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) ((X.B.I.fmat x - 1) *ᵥ X.bw j)) := hsub (hc3 j)
    have hZ : ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw j) - if i = j then X.ew else 0) := by
      have e : hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw j) - (if i = j then X.ew else 0) =
          (hA X.B.I (X.bwd i) (X.bw j) - if i = j then X.ew else 0) +
            hA X.B.I (X.bwd i) ((X.B.I.fmat x - 1) *ᵥ X.bw j) := by
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, hA_sub_right]
        ring
      rw [e]
      exact Z_add X.B.I X.B.g (X.bw_dual i j) h2
    show resT TR v (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw j)) = _
    rw [resT_of_mem TR v hc]
    exact res_of_Z_delta TR v hc (i = j) hZ
  show (∀ i : Fin D.R.k, ((levi TR x v : GL (Fin D.R.k) (TR.Fq v)) : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) i i = 1) ∧
    ∀ i j : Fin D.R.k, j < i →
      ((levi TR x v : GL (Fin D.R.k) (TR.Fq v)) : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) i j = 0
  rw [levi_coe TR hx v]
  exact ⟨fun i => by rw [key i i le_rfl, if_pos rfl],
    fun i j hji => by rw [key i j hji.le, if_neg (ne_of_lt hji).symm]⟩

end K2iff

end PI.UnitaryDimensionFormula.NormCutK
end
end

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp
  Formalism.L2.SG.Full Formalism.MainNotions.S.Cnt

namespace PI.UnitaryDimensionFormula

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem cj_good {D : D7} {X : HidaSetting D} (u : D.what₂.Word) (s : Hfin X u) (hs : cj X u s ∈ X.B.I.Kset) :
    NormCutK.Good X (cj X u s) := by
  have hk1 : (((1 : Hfin X u) : X.B.I.Gf) * X.xu u)⁻¹ * ((s : X.B.I.Gf) * X.xu u) ∈ X.B.I.Kset := by
    simpa [cj, mul_assoc] using hs
  have hk2 : ((s : X.B.I.Gf) * X.xu u)⁻¹ * (((1 : Hfin X u) : X.B.I.Gf) * X.xu u) ∈ X.B.I.Kset := by
    have hi := PI.UnitaryDimensionFormula.kset_inv hs
    simpa [cj, mul_assoc, mul_inv_rev] using hi
  have hg := NormCutK.colGood X u 1 s hk1 hk2
  simpa [cj, mul_assoc] using hg

theorem idxHom : IdxHom := by
  intro D X Y u _
  refine ⟨NormCutK.levi_one (TR := Y.TR), fun s t hs ht => ?_, fun s hs hKu v => ?_⟩
  · have hst : cj X u (s * t) = cj X u s * cj X u t := by
      simp [cj, mul_assoc]
    rw [hst, NormCutK.levi_mul (TR := Y.TR) (cj_good u s hs) (cj_good u t ht)]
  · exact NormCutK.unitriangular_reduction_of_mem_level (TR := Y.TR) (cj_good u s hs) hKu v

end PI.UnitaryDimensionFormula
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IdxAUni
namespace PI.UnitaryDimensionFormula

open Matrix

section Core

variable {F : Type} [Field F] {k : ℕ}

theorem uniA_mul_diag (A B : Matrix (Fin k) (Fin k) F) (hA : A.BlockTriangular id)
    (hB : B.BlockTriangular id) (i : Fin k) : (A * B) i i = A i i * B i i := by
  first | exact UpperTheory.Reformulated.B.Qh23.uniA_mul_diag .. | (apply UpperTheory.Reformulated.B.Qh23.uniA_mul_diag <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qh23.uniA_mul_diag <;> assumption) | (apply @UpperTheory.Reformulated.B.Qh23.uniA_mul_diag <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qh23.uniA_mul_diag <;> assumption) | (apply @UpperTheory.Reformulated.B.Qh23.uniA_mul_diag <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qh23.uniA_mul_diag F ‹_› k A B hA hB i | exact @UpperTheory.Reformulated.B.Qh23.uniA_mul_diag F ‹_› k A B hA hB | exact @UpperTheory.Reformulated.B.Qh23.uniA_mul_diag F ‹_› k A B hA | exact @UpperTheory.Reformulated.B.Qh23.uniA_mul_diag F ‹_› k A B | exact @UpperTheory.Reformulated.B.Qh23.uniA_mul_diag F ‹_› k A | exact @UpperTheory.Reformulated.B.Qh23.uniA_mul_diag F ‹_› k | exact @UpperTheory.Reformulated.B.Qh23.uniA_mul_diag F ‹_› | exact @UpperTheory.Reformulated.B.Qh23.uniA_mul_diag F

theorem uniA_tri (x : GL (Fin k) F) (hx : ∀ i j : Fin k, j < i → (x : Matrix (Fin k) (Fin k) F) i j = 0) :
    (x : Matrix (Fin k) (Fin k) F).BlockTriangular id := fun i j h => hx i j h

theorem uniA_mul (x y : GL (Fin k) F) (hx : Formalism.L2.SG.GGMirabolic.IsUni k x)
    (hy : Formalism.L2.SG.GGMirabolic.IsUni k y) : Formalism.L2.SG.GGMirabolic.IsUni k (x * y) := by
  have tx := uniA_tri x hx.2
  have ty := uniA_tri y hy.2
  have txy : ((x : Matrix (Fin k) (Fin k) F) * (y : Matrix (Fin k) (Fin k) F)).BlockTriangular id :=
    tx.mul ty
  refine ⟨fun i => ?_, fun i j h => ?_⟩
  · rw [Units.val_mul, uniA_mul_diag _ _ tx ty, hx.1 i, hy.1 i, one_mul]
  · rw [Units.val_mul]; exact txy h

theorem uniA_inv (x : GL (Fin k) F) (hx : Formalism.L2.SG.GGMirabolic.IsUni k x) :
    Formalism.L2.SG.GGMirabolic.IsUni k x⁻¹ := by
  have tx := uniA_tri x hx.2
  have : Invertible (x : Matrix (Fin k) (Fin k) F) := Units.invertible x
  have tinv : ((x : Matrix (Fin k) (Fin k) F)⁻¹).BlockTriangular id :=
    Matrix.blockTriangular_inv_of_blockTriangular tx
  have hc : ((x⁻¹ : GL (Fin k) F) : Matrix (Fin k) (Fin k) F) = (x : Matrix (Fin k) (Fin k) F)⁻¹ :=
    Matrix.coe_units_inv x
  refine ⟨fun i => ?_, fun i j h => ?_⟩
  · have h1 : ((x : Matrix (Fin k) (Fin k) F)⁻¹ * (x : Matrix (Fin k) (Fin k) F)) i i = 1 := by
      rw [Matrix.inv_mul_of_invertible, Matrix.one_apply_eq]
    rw [uniA_mul_diag _ _ tinv tx, hx.1 i, mul_one] at h1
    rw [hc]; exact h1
  · rw [hc]; exact tinv h

end Core

theorem uniSub : UniSub := by
  intro F _ k x y hx hy
  exact ⟨uniA_mul x y hx hy, uniA_inv x hx⟩

end PI.UnitaryDimensionFormula
end

namespace PI.UnitaryDimensionFormula

theorem indexGe : IndexGe := indexGe_of uniSub idxHom (idxSurj_of_frame idxDFrame)

end PI.UnitaryDimensionFormula
