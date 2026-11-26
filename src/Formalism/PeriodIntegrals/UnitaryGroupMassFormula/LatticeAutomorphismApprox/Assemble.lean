module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismApprox.NatCastTmul
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismApprox.GlueHoldsVar

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismApprox.LocalIdempotentExistence
noncomputable section

namespace PI.UnitaryGroupMassFormula.ScXuExists

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Matrix
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists

def smulLin (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (c : RV I v) :
    (Fin I.n → RV I v) →ₗ[OV I v] (Fin I.n → RV I v) where
  toFun x := c • x
  map_add' x y := smul_add c x y
  map_smul' o x := by
    simp only [RingHom.id_apply]
    rw [PI.FinKW.LocTo.ov_smul_vec, PI.FinKW.LocTo.ov_smul_vec, smul_comm]

theorem idem_kill (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (g : ℕ) (hg : (g : 𝓞 I.F) ∈ v.asIdeal)
    (c : RV I v) (hcc : c * c = c)
    (hc : ∀ x ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)),
      ∃ w ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)), c • x = (g : RV I v) • w) :
    ∀ x ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)), c • x = 0 := by
  have hfg : ((Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E))).map (smulLin I v c)).FG :=
    (latLoc_fg I v).map _
  have hle : (Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E))).map (smulLin I v c) ≤
      Ideal.span {(g : OV I v)} • (Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E))).map (smulLin I v c) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨w, hw, hcw⟩ := hc x hx
    have e : (smulLin I v c) x = (g : OV I v) • (smulLin I v c w) := by
      show c • x = (g : OV I v) • (c • w)
      rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul (RV I v), smul_comm, ← hcw, smul_smul, hcc]
    rw [e]
    exact Submodule.smul_mem_smul (Ideal.subset_span (Set.mem_singleton _)) (Submodule.mem_map_of_mem hw)
  have hjac : Ideal.span {(g : OV I v)} ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, Ideal.span_le, Set.singleton_subset_iff]
    exact natCast_mem_max I.F v g hg
  have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ hfg hle hjac
  intro x hx
  have hm : (smulLin I v c) x ∈ (Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E))).map (smulLin I v c) :=
    Submodule.mem_map_of_mem hx
  rw [hbot, Submodule.mem_bot] at hm
  exact hm

theorem kill_zero (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (hn : 0 < I.n) (c : RV I v)
    (h : ∀ x ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)), c • x = 0) : c = 0 := by
  have key : ∀ x ∈ Submodule.span I.E (I.L : Set (Fin I.n → I.E)),
      c • Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) x = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact h _ (Submodule.subset_span ⟨y, hy, rfl⟩)
    | zero => rw [PI.FinKW.ratV_zero', smul_zero]
    | add y z _ _ hy hz => rw [PI.FinKW.ratV_add', smul_add, hy, hz, add_zero]
    | smul a y _ hy =>
      have e : Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) (a • y) =
          (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) a) •
            Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) y := by
        funext i
        simp only [Formalism.L2.SG.Sub.ratV, Pi.smul_apply, smul_eq_mul, map_mul]
      rw [e, smul_comm, hy, smul_zero]
  have h0 := key (Pi.single ⟨0, hn⟩ 1) (by rw [I.L_span]; exact Submodule.mem_top)
  have e1 : Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) (Pi.single ⟨0, hn⟩ (1 : I.E)) =
      Pi.single ⟨0, hn⟩ 1 := by
    funext i
    by_cases hi : i = ⟨0, hn⟩
    · subst hi
      simp [Formalism.L2.SG.Sub.ratV]
    · simp [Formalism.L2.SG.Sub.ratV, hi]
  rw [e1] at h0
  have h1 := congrFun h0 ⟨0, hn⟩
  simpa using h1

theorem local_idempotent_existence : LocIdem := by
  intro I g r k e f Rf hg hn v hv
  have hb : PI.UnitaryGroupMassFormula.AdIndexEq.sigV I v (PI.FinKW.psiV I v Rf.ew) *
      PI.UnitaryGroupMassFormula.AdIndexEq.sigV I v (PI.FinKW.psiV I v Rf.ew) =
      PI.UnitaryGroupMassFormula.AdIndexEq.sigV I v (PI.FinKW.psiV I v Rf.ew) := by
    rw [← map_mul, eps_idem Rf v]
  have hcc : (1 - PI.FinKW.psiV I v Rf.ew - PI.UnitaryGroupMassFormula.AdIndexEq.sigV I v (PI.FinKW.psiV I v Rf.ew)) *
      (1 - PI.FinKW.psiV I v Rf.ew - PI.UnitaryGroupMassFormula.AdIndexEq.sigV I v (PI.FinKW.psiV I v Rf.ew)) =
      1 - PI.FinKW.psiV I v Rf.ew - PI.UnitaryGroupMassFormula.AdIndexEq.sigV I v (PI.FinKW.psiV I v Rf.ew) := by
    linear_combination eps_idem Rf v + hb + 2 * eps_orth Rf v
  have hkill := idem_kill I v g hv _ hcc (fun x hx => full_loc Rf v x hx)
  have hz := kill_zero I v (by omega) _ hkill
  linear_combination -hz

end PI.UnitaryGroupMassFormula.ScXuExists
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismApprox.LinMain
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismApprox.LinLeg
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismApprox.LinBase
noncomputable section

namespace PI.UnitaryGroupMassFormula.ScXuExists

open Matrix

section Pr

variable {K : Type} [Field K] {n : ℕ} (P : Matrix (Fin n) (Fin n) K)

theorem pr_add_left (β β' x : Fin n → K) : pr P (β + β') x = pr P β x + pr P β' x := by
  first
  | simp [pr]
  | simp [pr, dotProduct, Finset.sum_add_distrib, add_mul]

theorem pr_sub_left (β β' x : Fin n → K) : pr P (β - β') x = pr P β x - pr P β' x := by
  first
  | simp [pr]
  | simp [pr, dotProduct, Finset.sum_sub_distrib, sub_mul]

theorem pr_smul_left (c : K) (β x : Fin n → K) : pr P (c • β) x = c * pr P β x := by
  first
  | simp [pr]
  | simp [pr, dotProduct, Finset.mul_sum, mul_assoc]

theorem pr_add_right (β x y : Fin n → K) : pr P β (x + y) = pr P β x + pr P β y := by
  unfold pr
  rw [Matrix.mulVec_add, dotProduct_add]

theorem pr_sub_right (β x y : Fin n → K) : pr P β (x - y) = pr P β x - pr P β y := by
  unfold pr
  rw [Matrix.mulVec_sub, dotProduct_sub]

theorem pr_smul_right (c : K) (β x : Fin n → K) : pr P β (c • x) = c * pr P β x := by
  unfold pr
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem pr_sum_left {ι : Type} (s : Finset ι) (β : ι → Fin n → K) (x : Fin n → K) :
    pr P (∑ i ∈ s, β i) x = ∑ i ∈ s, pr P (β i) x := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [pr]
  · intro a t ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, pr_add_left, ih]

theorem pr_sum_right {ι : Type} (s : Finset ι) (β : Fin n → K) (x : ι → Fin n → K) :
    pr P β (∑ i ∈ s, x i) = ∑ i ∈ s, pr P β (x i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [pr]
  · intro a t ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, pr_add_right, ih]

theorem pr_eq_vecMul (β x : Fin n → K) : pr P β x = (β ᵥ* P) ⬝ᵥ x := by
  first
  | exact dotProduct_mulVec β P x
  | exact Matrix.dotProduct_mulVec β P x
  | simp [pr, dotProduct_mulVec]

end Pr

section Rk1

variable {R : Type} [CommRing R] {n : ℕ}

theorem one_add_smul_vecMulVec_mul (p q : Fin n → R) (c d : R) :
    (1 + c • vecMulVec p q) * (1 + d • vecMulVec p q) =
      1 + (c + d + c * d * (q ⬝ᵥ p)) • vecMulVec p q := by
  have key : vecMulVec p q * vecMulVec p q = (q ⬝ᵥ p) • vecMulVec p q := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, dotProduct,
      Finset.sum_mul]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  simp only [add_mul, mul_add, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, key, smul_smul]
  first
  | (module; done)
  | (rw [add_smul, add_smul, show c * d * (q ⬝ᵥ p) = d * (c * (q ⬝ᵥ p)) by ring]; abel; done)
  | (rw [add_smul, add_smul, show c * d * (q ⬝ᵥ p) = c * (d * (q ⬝ᵥ p)) by ring]; abel; done)

def rankOneUnitGL (p q : Fin n → R) (c d : R) (h : c + d + c * d * (q ⬝ᵥ p) = 0) : GL (Fin n) R :=
  ⟨1 + c • vecMulVec p q, 1 + d • vecMulVec p q, by rw [one_add_smul_vecMulVec_mul, h, zero_smul, add_zero],
    by rw [one_add_smul_vecMulVec_mul, show d + c + d * c * (q ⬝ᵥ p) = 0 by linear_combination h, zero_smul, add_zero]⟩

theorem coe_rankOneGL (p q : Fin n → R) (c d : R) (h : c + d + c * d * (q ⬝ᵥ p) = 0) :
    ((rankOneUnitGL p q c d h : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = 1 + c • vecMulVec p q := rfl

theorem coe_rankOneGL_inv (p q : Fin n → R) (c d : R) (h : c + d + c * d * (q ⬝ᵥ p) = 0) :
    (((rankOneUnitGL p q c d h)⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = 1 + d • vecMulVec p q := rfl

theorem one_add_smul_vecMulVec_mulVec (p q x : Fin n → R) (c : R) :
    (1 + c • vecMulVec p q) *ᵥ x = x + (c * (q ⬝ᵥ x)) • p := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec]
  ext i
  simp only [Pi.add_apply, add_right_inj, Matrix.mulVec, dotProduct, Matrix.smul_apply,
    Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  all_goals exact Finset.sum_congr rfl (fun j _ => by ring)

theorem vecMul_one_add_smul_vecMulVec (p q y : Fin n → R) (c : R) :
    y ᵥ* (1 + c • vecMulVec p q) = y + (c * (y ⬝ᵥ p)) • q := by
  rw [Matrix.vecMul_add, Matrix.vecMul_one]
  ext j
  simp only [Pi.add_apply, add_right_inj, Matrix.vecMul, dotProduct, Matrix.smul_apply,
    Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  all_goals exact Finset.sum_congr rfl (fun i _ => by ring)

end Rk1

section Good

variable {K : Type} [Field K] (O : ValuationSubring K) {n r : ℕ} (P : Matrix (Fin n) (Fin n) K)
  (Λ1 Λ2 : Submodule O (Fin n → K)) (a a' α α' : Fin r → Fin n → K)

theorem smem {M : Submodule O (Fin n → K)} {c : K} (hc : c ∈ O) {x : Fin n → K} (hx : x ∈ M) :
    c • x ∈ M := by
  first
  | exact M.smul_mem (⟨c, hc⟩ : O) hx
  | (have h := M.smul_mem (⟨c, hc⟩ : O) hx
     simpa [Algebra.smul_def] using h)

def Good (T : GL (Fin n) K) : Prop :=
  (∀ x ∈ Λ1, (T : Matrix (Fin n) (Fin n) K) *ᵥ x ∈ Λ1 ∧
        ((T⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x ∈ Λ1) ∧
      (∀ β ∈ Λ2, (∃ β' ∈ Λ2, β' ᵥ* P = (β ᵥ* P) ᵥ* (T : Matrix (Fin n) (Fin n) K)) ∧
        (∃ β' ∈ Λ2, β' ᵥ* P = (β ᵥ* P) ᵥ* ((T⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) ∧
      (∀ i, (T : Matrix (Fin n) (Fin n) K) *ᵥ a i = a i ∧ (T : Matrix (Fin n) (Fin n) K) *ᵥ a' i = a' i ∧
        (α i ᵥ* P) ᵥ* (T : Matrix (Fin n) (Fin n) K) = α i ᵥ* P ∧
        (α' i ᵥ* P) ᵥ* (T : Matrix (Fin n) (Fin n) K) = α' i ᵥ* P)

private theorem smul_vecMul' (b : K) (v : Fin n → K) (M : Matrix (Fin n) (Fin n) K) :
    (b • v) ᵥ* M = b • (v ᵥ* M) := by
  ext j
  simp only [Matrix.vecMul, dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem good_mul {S T : GL (Fin n) K} (hS : Good O P Λ1 Λ2 a a' α α' S)
    (hT : Good O P Λ1 Λ2 a a' α α' T) : Good O P Λ1 Λ2 a a' α α' (S * T) := by
  unfold Good at hS hT ⊢
  obtain ⟨hS1, hS2, hS3⟩ := hS
  obtain ⟨hT1, hT2, hT3⟩ := hT
  have hmul : ((S * T : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (S : Matrix (Fin n) (Fin n) K) * (T : Matrix (Fin n) (Fin n) K) := Units.val_mul S T
  have hinv : (((S * T)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((T⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((S⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [_root_.mul_inv_rev]
    exact Units.val_mul _ _
  rw [hinv, hmul]
  refine ⟨fun x hx => ?_, fun β hβ => ?_, fun i => ?_⟩
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact ⟨(hS1 _ (hT1 x hx).1).1, (hT1 _ (hS1 x hx).2).2⟩
  · rw [← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul]
    obtain ⟨⟨β1, hβ1, e1⟩, -⟩ := hS2 β hβ
    obtain ⟨⟨β2, hβ2, e2⟩, -⟩ := hT2 β1 hβ1
    obtain ⟨-, ⟨γ1, hγ1, f1⟩⟩ := hT2 β hβ
    obtain ⟨-, ⟨γ2, hγ2, f2⟩⟩ := hS2 γ1 hγ1
    exact ⟨⟨β2, hβ2, by rw [e2, e1]⟩, ⟨γ2, hγ2, by rw [f2, f1]⟩⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hS3 i
    obtain ⟨k1, k2, k3, k4⟩ := hT3 i
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul,
      k1, k2, h1, h2, h3, h4, k3, k4]
    exact ⟨rfl, rfl, rfl, rfl⟩

variable {O P Λ1 Λ2 a a' α α'} in
theorem isAdmissible_rankOneGL (hP : ∀ β ∈ Λ2, ∀ x ∈ Λ1, pr P β x ∈ O) (w γ : Fin n → K) (c d : K)
    (h : c + d + c * d * ((γ ᵥ* P) ⬝ᵥ w) = 0) (hc : c ∈ O) (hd : d ∈ O) (hw : w ∈ Λ1) (hγ : γ ∈ Λ2)
    (hwα : ∀ i, pr P (α i) w = 0 ∧ pr P (α' i) w = 0) (hγa : ∀ i, pr P γ (a i) = 0 ∧ pr P γ (a' i) = 0) :
    Good O P Λ1 Λ2 a a' α α' (rankOneUnitGL w (γ ᵥ* P) c d h) := by
  unfold Good
  rw [coe_rankOneGL_inv, coe_rankOneGL]
  have hm : ∀ {u v : K}, u ∈ O → v ∈ O → u * v ∈ O := by
    intro u v hu hv
    first
    | exact mul_mem hu hv
    | exact O.mul_mem _ _ hu hv
    | exact O.toSubring.mul_mem hu hv
  have hO : ∀ x ∈ Λ1, (γ ᵥ* P) ⬝ᵥ x ∈ O := fun x hx => by
    rw [← pr_eq_vecMul]
    exact hP γ hγ x hx
  have hO' : ∀ β ∈ Λ2, (β ᵥ* P) ⬝ᵥ w ∈ O := fun β hβ => by
    rw [← pr_eq_vecMul]
    exact hP β hβ w hw
  have hvec : ∀ (e : K) (β : Fin n → K),
      (β + (e * ((β ᵥ* P) ⬝ᵥ w)) • γ) ᵥ* P = (β ᵥ* P) ᵥ* (1 + e • vecMulVec w (γ ᵥ* P)) := by
    intro e β
    rw [vecMul_one_add_smul_vecMulVec, Matrix.add_vecMul, smul_vecMul']
  refine ⟨fun x hx => ⟨?_, ?_⟩,
    fun β hβ => ⟨⟨β + (c * ((β ᵥ* P) ⬝ᵥ w)) • γ, ?_, hvec c β⟩,
      ⟨β + (d * ((β ᵥ* P) ⬝ᵥ w)) • γ, ?_, hvec d β⟩⟩, fun i => ?_⟩
  · rw [one_add_smul_vecMulVec_mulVec]
    exact Λ1.add_mem hx (smem O (hm hc (hO x hx)) hw)
  · rw [one_add_smul_vecMulVec_mulVec]
    exact Λ1.add_mem hx (smem O (hm hd (hO x hx)) hw)
  · exact Λ2.add_mem hβ (smem O (hm hc (hO' β hβ)) hγ)
  · exact Λ2.add_mem hβ (smem O (hm hd (hO' β hβ)) hγ)
  · have e1 : (γ ᵥ* P) ⬝ᵥ a i = 0 := by rw [← pr_eq_vecMul]; exact (hγa i).1
    have e2 : (γ ᵥ* P) ⬝ᵥ a' i = 0 := by rw [← pr_eq_vecMul]; exact (hγa i).2
    have e3 : (α i ᵥ* P) ⬝ᵥ w = 0 := by rw [← pr_eq_vecMul]; exact (hwα i).1
    have e4 : (α' i ᵥ* P) ⬝ᵥ w = 0 := by rw [← pr_eq_vecMul]; exact (hwα i).2
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [one_add_smul_vecMulVec_mulVec, e1, mul_zero, zero_smul, add_zero]
    · rw [one_add_smul_vecMulVec_mulVec, e2, mul_zero, zero_smul, add_zero]
    · rw [vecMul_one_add_smul_vecMulVec, e3, mul_zero, zero_smul, add_zero]
    · rw [vecMul_one_add_smul_vecMulVec, e4, mul_zero, zero_smul, add_zero]

end Good

end PI.UnitaryGroupMassFormula.ScXuExists
end
end

noncomputable section

namespace PI.UnitaryGroupMassFormula.ScXuExists

open Matrix

section Leg

variable {K : Type} [Field K] (O : ValuationSubring K) {n r : ℕ} (P : Matrix (Fin n) (Fin n) K)
  (Λ1 Λ2 : Submodule O (Fin n → K)) (a a' α α' : Fin r → Fin n → K)

theorem memO_of_v {x : K} (h : O.valuation x = 1) : x ∈ O :=
  (O.valuation_le_one_iff x).1 h.le

theorem inv_memO_of_v {x : K} (h : O.valuation x = 1) : x⁻¹ ∈ O :=
  memO_of_v O (by rw [map_inv₀, h, inv_one])

theorem ne_zero_of_v {x : K} (h : O.valuation x = 1) : x ≠ 0 := by
  rintro rfl
  simp at h

def Pair (u φ : Fin n → K) : Prop :=
  u ∈ Λ1 ∧ φ ∈ Λ2 ∧ (∀ i, pr P (α i) u = 0 ∧ pr P (α' i) u = 0) ∧
    (∀ i, pr P φ (a i) = 0 ∧ pr P φ (a' i) = 0)

variable {O P Λ1 Λ2 a a' α α'} in
theorem leg (hP : ∀ β ∈ Λ2, ∀ x ∈ Λ1, pr P β x ∈ O) {up φp uq φq : Fin n → K}
    (hp : Pair O P Λ1 Λ2 a a' α α' up φp) (hq : Pair O P Λ1 Λ2 a a' α α' uq φq)
    (hcp : O.valuation (pr P φp up) = 1) (hcq : O.valuation (pr P φq uq) = 1)
    (hd : O.valuation (pr P φp uq) = 1) :
    ∃ T : GL (Fin n) K, Good O P Λ1 Λ2 a a' α α' T ∧ (T : Matrix (Fin n) (Fin n) K) *ᵥ up = uq ∧
      (φq ᵥ* P) ᵥ* (T : Matrix (Fin n) (Fin n) K) = (pr P φq uq / pr P φp up) • (φp ᵥ* P) := by
  unfold Pair at hp hq
  obtain ⟨hup, hφp, hupα, hφpa⟩ := hp
  obtain ⟨huq, hφq, huqα, hφqa⟩ := hq
  have hcp0 : pr P φp up ≠ 0 := ne_zero_of_v O hcp
  have hcq0 : pr P φq uq ≠ 0 := ne_zero_of_v O hcq
  have hd0 : pr P φp uq ≠ 0 := ne_zero_of_v O hd
  have hcpi : (pr P φp up)⁻¹ ∈ O := inv_memO_of_v O hcp
  have hcqi : (pr P φq uq)⁻¹ ∈ O := inv_memO_of_v O hcq
  have hdi : (pr P φp uq)⁻¹ ∈ O := inv_memO_of_v O hd
  have hb : pr P φq up ∈ O := hP φq hφq up hup
  have e1 : pr P φp uq * (pr P φp uq)⁻¹ = 1 := mul_inv_cancel₀ hd0
  have e2 : pr P φp up * (pr P φp up)⁻¹ = 1 := mul_inv_cancel₀ hcp0
  have e3 : pr P φq uq * (pr P φq uq)⁻¹ = 1 := mul_inv_cancel₀ hcq0
  have hXup : (φq ᵥ* P) ⬝ᵥ up = pr P φq up := (pr_eq_vecMul P φq up).symm
  have hYup : (φp ᵥ* P) ⬝ᵥ up = pr P φp up := (pr_eq_vecMul P φp up).symm
  have hD1 : (φq ᵥ* P) ⬝ᵥ (uq - up) = pr P φq uq - pr P φq up := by
    rw [← pr_eq_vecMul, pr_sub_right]
  have hdot : ∀ (V W : Fin n → K) (t : K), (V + t • W) ⬝ᵥ up = V ⬝ᵥ up + t * (W ⬝ᵥ up) := by
    intro V W t
    first
    | (simp only [add_dotProduct, smul_dotProduct, smul_eq_mul]; done)
    | (simp; done)
    | (simp [dotProduct, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]; done)
  obtain ⟨γ2, hγ2⟩ : ∃ γ2 : Fin n → K, γ2 = φq - (pr P φq up * (pr P φp up)⁻¹) • φp := ⟨_, rfl⟩
  have hγ2u : (γ2 ᵥ* P) ⬝ᵥ up = 0 := by
    rw [← pr_eq_vecMul, hγ2, pr_sub_left, pr_smul_left]
    linear_combination (-pr P φq up) * e2
  have hγ2P : γ2 ᵥ* P = φq ᵥ* P - (pr P φq up * (pr P φp up)⁻¹) • (φp ᵥ* P) := by
    subst hγ2
    first
    | (simp only [sub_vecMul, vecMul_smul]; done)
    | (simp only [sub_vecMul, smul_vecMul]; done)
    | (simp [sub_vecMul]; done)
    | (ext j; simp [vecMul, dotProduct, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]; done)
  have hγ2mem : γ2 ∈ Λ2 := by
    have hs : pr P φq up * (pr P φp up)⁻¹ ∈ O := by
      first | exact mul_mem hb hcpi | exact O.mul_mem _ _ hb hcpi
    rw [hγ2]
    exact Λ2.sub_mem hφq (smem O hs hφp)
  have hγ2a : ∀ i, pr P γ2 (a i) = 0 ∧ pr P γ2 (a' i) = 0 := fun i => by
    simp only [hγ2, pr_sub_left, pr_smul_left, (hφqa i).1, (hφqa i).2, (hφpa i).1, (hφpa i).2,
      mul_zero, sub_zero, and_self]
  have hwα1 : ∀ i, pr P (α i) (uq - up) = 0 ∧ pr P (α' i) (uq - up) = 0 := fun i =>
    ⟨by rw [pr_sub_right, (huqα i).1, (hupα i).1, sub_self],
      by rw [pr_sub_right, (huqα i).2, (hupα i).2, sub_self]⟩
  have h1 : (pr P φp up)⁻¹ + -(pr P φp uq)⁻¹ +
      (pr P φp up)⁻¹ * -(pr P φp uq)⁻¹ * ((φp ᵥ* P) ⬝ᵥ (uq - up)) = 0 := by
    rw [← pr_eq_vecMul, pr_sub_right]
    linear_combination (pr P φp uq)⁻¹ * e2 - (pr P φp up)⁻¹ * e1
  have h2 : -(pr P φq uq)⁻¹ + (pr P φq uq)⁻¹ +
      -(pr P φq uq)⁻¹ * (pr P φq uq)⁻¹ * ((γ2 ᵥ* P) ⬝ᵥ up) = 0 := by
    rw [hγ2u]
    ring
  have hn1 : -(pr P φp uq)⁻¹ ∈ O := by
    first | exact neg_mem hdi | exact O.neg_mem _ hdi
  have hn2 : -(pr P φq uq)⁻¹ ∈ O := by
    first | exact neg_mem hcqi | exact O.neg_mem _ hcqi
  have hT1 := isAdmissible_rankOneGL hP (uq - up) φp _ _ h1 hcpi hn1 (Λ1.sub_mem huq hup) hφp hwα1 hφpa
  have hT2 := isAdmissible_rankOneGL hP up γ2 _ _ h2 hn2 hcqi hup hγ2mem hupα hγ2a
  refine ⟨rankOneUnitGL (uq - up) (φp ᵥ* P) _ _ h1 * rankOneUnitGL up (γ2 ᵥ* P) _ _ h2,
    good_mul _ _ _ _ _ _ _ _ hT1 hT2, ?_, ?_⟩
  · simp only [Units.val_mul, ← mulVec_mulVec, coe_rankOneGL, one_add_smul_vecMulVec_mulVec, hγ2u, mul_zero,
      zero_smul, add_zero, hYup, inv_mul_cancel₀ hcp0, one_smul]
    abel
  · simp only [Units.val_mul, ← vecMul_vecMul, coe_rankOneGL, vecMul_one_add_smul_vecMulVec]
    rw [hD1, hdot, hXup, hYup, hγ2P]
    ext j
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination ((φq ᵥ* P) j - pr P φq up * (pr P φp up)⁻¹ * (φp ᵥ* P) j) *
      (-(pr P φq uq)⁻¹ * (pr P φq uq - pr P φq up) * e2 - e3)

end Leg

end PI.UnitaryGroupMassFormula.ScXuExists
end
end

noncomputable section

namespace PI.UnitaryGroupMassFormula.ScXuExists

open Matrix

section Main

variable {K : Type} [Field K] (O : ValuationSubring K)

private theorem valuationSubring_valuation_le_one_of_mem {K : Type} [Field K] (O : ValuationSubring K) {x : K}
    (hx : x ∈ O) : O.valuation x ≤ 1 := by
  first
  | exact (O.valuation_le_one_iff x).mpr hx
  | exact O.valuation_le_one ⟨x, hx⟩
  | exact (ValuationSubring.valuation_le_one_iff O x).2 hx

theorem v_small {g y : K} (hg : O.valuation g < 1) (hy : y ∈ O) : O.valuation (g * y) < 1 := by
  rw [map_mul]
  have h1 : O.valuation y ≤ 1 := valuationSubring_valuation_le_one_of_mem O hy
  calc O.valuation g * O.valuation y ≤ O.valuation g * 1 := by
        first
        | exact mul_le_mul_left' h1 _
        | exact mul_le_mul_of_nonneg_left h1 zero_le'
        | gcongr
    _ = O.valuation g := mul_one _
    _ < 1 := hg

theorem v_add_small {e m : K} (he : O.valuation e = 1) (hm : O.valuation m < 1) :
    O.valuation (e + m) = 1 := by
  have h : O.valuation m < O.valuation e := by rw [he]; exact hm
  first
  | exact (Valuation.map_add_eq_of_lt_left _ h).trans he
  | exact (O.valuation.map_add_eq_of_lt_left h).trans he
  | (rw [add_comm]; exact (Valuation.map_add_eq_of_lt_right _ h).trans he)
  | (rw [add_comm]; exact (O.valuation.map_add_eq_of_lt_right h).trans he)

theorem v_neg_one : O.valuation (-1 : K) = 1 := by
  first
  | simp
  | exact (Valuation.map_neg _ 1).trans (map_one _)
  | rw [Valuation.map_neg, map_one]

end Main

private theorem sub_vecMul_field {K : Type} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K)
    (x y : Fin n → K) : (x - y) ᵥ* M = x ᵥ* M - y ᵥ* M := by
  first
  | exact Matrix.sub_vecMul M x y
  | (funext j; simp [Matrix.vecMul, dotProduct, sub_mul, Finset.sum_sub_distrib])

private theorem add_vecMul_field {K : Type} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K)
    (x y : Fin n → K) : (x + y) ᵥ* M = x ᵥ* M + y ᵥ* M := by
  first
  | exact Matrix.add_vecMul M x y
  | (funext j; simp [Matrix.vecMul, dotProduct, add_mul, Finset.sum_add_distrib])

private theorem smul_vecMul_field {K : Type} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K)
    (c : K) (x : Fin n → K) : (c • x) ᵥ* M = c • (x ᵥ* M) := by
  first
  | exact Matrix.vecMul_smul M c x
  | (funext j; simp [Matrix.vecMul, dotProduct, Finset.mul_sum, mul_assoc])

private theorem exists_mem_sum_smul_eq_smul_of_divisible {K : Type} [Field K] (O : ValuationSubring K) {n r : ℕ}
    (M : Submodule O (Fin n → K)) (g : K) (f f' : Fin r → K) (v v' : Fin r → Fin n → K)
    (hv : ∀ i, v i ∈ M) (hv' : ∀ i, v' i ∈ M)
    (hf : ∀ i, ∃ s ∈ O, f i = g * s) (hf' : ∀ i, ∃ s ∈ O, f' i = g * s) :
    ∃ w ∈ M, ∑ i, (f i • v i + f' i • v' i) = g • w := by
  choose s hs hse using hf
  choose s' hs' hse' using hf'
  refine ⟨∑ i, (s i • v i + s' i • v' i),
    M.sum_mem fun i _ => M.add_mem (smem O (hs i) (hv i))
      (smem O (hs' i) (hv' i)), ?_⟩
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hse i, hse' i, smul_add, mul_smul, mul_smul]

private theorem exists_pr_orthogonal_left_sub_smul_mem {K : Type} [Field K] (O : ValuationSubring K) {n r : ℕ}
    (P : Matrix (Fin n) (Fin n) K) (Λ1 : Submodule O (Fin n → K)) (a a' α α' : Fin r → Fin n → K)
    (g : K) (hg : g ∈ O)
    (hpair : ∀ i j, pr P (α i) (a j) = 0 ∧ pr P (α' i) (a' j) = 0 ∧
      pr P (α i) (a' j) = (if i = j then 1 else 0) ∧ pr P (α' i) (a j) = (if i = j then 1 else 0))
    (ha : ∀ i, a i ∈ Λ1) (ha' : ∀ i, a' i ∈ Λ1) {u0 : Fin n → K} (hu0 : u0 ∈ Λ1)
    (h1 : ∀ i, ∃ s ∈ O, pr P (α i) u0 = g * s) (h2 : ∀ i, ∃ s ∈ O, pr P (α' i) u0 = g * s) :
    ∃ u1 ∈ Λ1, (∀ j, pr P (α j) u1 = 0 ∧ pr P (α' j) u1 = 0) ∧
      ∃ w ∈ Λ1, u1 = u0 - g • w := by
  have e1 : ∀ i j, pr P (α i) (a j) = 0 := fun i j => (hpair i j).1
  have e2 : ∀ i j, pr P (α' i) (a' j) = 0 := fun i j => (hpair i j).2.1
  have e3 : ∀ i j, pr P (α i) (a' j) = if i = j then 1 else 0 := fun i j => (hpair i j).2.2.1
  have e4 : ∀ i j, pr P (α' i) (a j) = if i = j then 1 else 0 := fun i j => (hpair i j).2.2.2
  obtain ⟨w, hw, hS⟩ := exists_mem_sum_smul_eq_smul_of_divisible O Λ1 g (fun i => pr P (α i) u0)
    (fun i => pr P (α' i) u0) a' a ha' ha h1 h2
  refine ⟨u0 - g • w, Λ1.sub_mem hu0 (smem O hg hw), fun j => ?_, w, hw, rfl⟩
  rw [← hS]
  constructor
  · simp [pr_sub_right, pr_sum_right, pr_add_right, pr_smul_right, e1, e2, e3, e4]
  · simp [pr_sub_right, pr_sum_right, pr_add_right, pr_smul_right, e1, e2, e3, e4]

private theorem exists_pr_orthogonal_right_sub_smul_mem {K : Type} [Field K] (O : ValuationSubring K) {n r : ℕ}
    (P : Matrix (Fin n) (Fin n) K) (Λ2 : Submodule O (Fin n → K)) (a a' α α' : Fin r → Fin n → K)
    (g : K) (hg : g ∈ O)
    (hpair : ∀ i j, pr P (α i) (a j) = 0 ∧ pr P (α' i) (a' j) = 0 ∧
      pr P (α i) (a' j) = (if i = j then 1 else 0) ∧ pr P (α' i) (a j) = (if i = j then 1 else 0))
    (hα : ∀ i, α i ∈ Λ2) (hα' : ∀ i, α' i ∈ Λ2) {φ0 : Fin n → K} (hφ0 : φ0 ∈ Λ2)
    (h3 : ∀ i, ∃ s ∈ O, pr P φ0 (a i) = g * s) (h4 : ∀ i, ∃ s ∈ O, pr P φ0 (a' i) = g * s) :
    ∃ φ1 ∈ Λ2, (∀ j, pr P φ1 (a j) = 0 ∧ pr P φ1 (a' j) = 0) ∧
      ∃ w ∈ Λ2, φ1 = φ0 - g • w := by
  have e1 : ∀ i j, pr P (α i) (a j) = 0 := fun i j => (hpair i j).1
  have e2 : ∀ i j, pr P (α' i) (a' j) = 0 := fun i j => (hpair i j).2.1
  have e3 : ∀ i j, pr P (α i) (a' j) = if i = j then 1 else 0 := fun i j => (hpair i j).2.2.1
  have e4 : ∀ i j, pr P (α' i) (a j) = if i = j then 1 else 0 := fun i j => (hpair i j).2.2.2
  obtain ⟨w, hw, hS⟩ := exists_mem_sum_smul_eq_smul_of_divisible O Λ2 g (fun i => pr P φ0 (a i))
    (fun i => pr P φ0 (a' i)) α' α hα' hα h3 h4
  refine ⟨φ0 - g • w, Λ2.sub_mem hφ0 (smem O hg hw), fun j => ?_, w, hw, rfl⟩
  rw [← hS]
  constructor
  · simp [pr_sub_left, pr_sum_left, pr_add_left, pr_smul_left, e1, e2, e3, e4]
  · simp [pr_sub_left, pr_sum_left, pr_add_left, pr_smul_left, e1, e2, e3, e4]

private theorem exists_isAdmissible_of_chain_lemma_8 {K : Type} [Field K] {O : ValuationSubring K} {n r : ℕ}
    {P : Matrix (Fin n) (Fin n) K} {Λ1 Λ2 : Submodule O (Fin n → K)} {a a' α α' : Fin r → Fin n → K}
    (hP : ∀ β ∈ Λ2, ∀ x ∈ Λ1, pr P β x ∈ O) {up φp um φm uq φq : Fin n → K}
    (hp : Pair O P Λ1 Λ2 a a' α α' up φp) (hm : Pair O P Λ1 Λ2 a a' α α' um φm)
    (hq : Pair O P Λ1 Λ2 a a' α α' uq φq)
    (hcp : O.valuation (pr P φp up) = 1) (hcm : O.valuation (pr P φm um) = 1)
    (hcq : O.valuation (pr P φq uq) = 1)
    (hd1 : O.valuation (pr P φp um) = 1) (hd2 : O.valuation (pr P φm uq) = 1) :
    ∃ T : GL (Fin n) K, Good O P Λ1 Λ2 a a' α α' T ∧ (T : Matrix (Fin n) (Fin n) K) *ᵥ up = uq ∧
      (φq ᵥ* P) ᵥ* (T : Matrix (Fin n) (Fin n) K) = (pr P φq uq / pr P φp up) • (φp ᵥ* P) := by
  obtain ⟨T1, hT1, hT1u, hT1φ⟩ := leg hP hp hm hcp hcm hd1
  obtain ⟨T2, hT2, hT2u, hT2φ⟩ := leg hP hm hq hcm hcq hd2
  have hm0 : pr P φm um ≠ 0 := ne_zero_of_v O hcm
  have hp0 : pr P φp up ≠ 0 := ne_zero_of_v O hcp
  have hcoe : ((T2 * T1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (T2 : Matrix (Fin n) (Fin n) K) * (T1 : Matrix (Fin n) (Fin n) K) := by
    first
    | exact Units.val_mul T2 T1
    | rfl
    | simp
  refine ⟨T2 * T1, good_mul _ _ _ _ _ _ _ _ hT2 hT1, ?_, ?_⟩
  · rw [hcoe, ← Matrix.mulVec_mulVec, hT1u, hT2u]
  · rw [hcoe, ← Matrix.vecMul_vecMul, hT2φ, smul_vecMul_field, hT1φ, smul_smul]
    congr 1
    first
    | rw [div_mul_div_comm, mul_comm (pr P φm um) (pr P φp up), mul_div_mul_right _ _ hm0]
    | (field_simp; try ring)

theorem existsLatticeAutomorphismApprox : LocLin := by
  unfold LocLin
  intro K _ O n r P g Λ1 Λ2 a a' α α' u φ u0 φ0 t hg hginv hP hfam hpair hu hφ hu0 hφ0 horth ht htg
    hφu hcong hc0
  obtain ⟨st, hst, hts⟩ := htg
  obtain ⟨s0, hs0, hs0e⟩ := hc0
  have hvg : O.valuation g < 1 := lt_of_le_of_ne (valuationSubring_valuation_le_one_of_mem O hg)
    (fun h => hginv (inv_memO_of_v O h))
  obtain ⟨u1, hu1, hu1o, w1, hw1, hu1e⟩ := exists_pr_orthogonal_left_sub_smul_mem O P Λ1 a a' α α' g hg hpair
    (fun i => (hfam i).1) (fun i => (hfam i).2.1) hu0 (fun i => (hcong i).1) (fun i => (hcong i).2.1)
  obtain ⟨φ1, hφ1, hφ1o, w2, hw2, hφ1e⟩ := exists_pr_orthogonal_right_sub_smul_mem O P Λ2 a a' α α' g hg hpair
    (fun i => (hfam i).2.2.1) (fun i => (hfam i).2.2.2) hφ0 (fun i => (hcong i).2.2.1)
    (fun i => (hcong i).2.2.2)
  have hp1 : Pair O P Λ1 Λ2 a a' α α' u1 φ1 := by
    unfold Pair
    exact ⟨hu1, hφ1, hu1o, hφ1o⟩
  have hq : Pair O P Λ1 Λ2 a a' α α' u φ := by
    unfold Pair
    exact ⟨hu, hφ, fun i => ⟨(horth i).1, (horth i).2.1⟩, fun i => ⟨(horth i).2.2.1, (horth i).2.2.2⟩⟩
  have hk : s0 - pr P φ0 w1 - pr P w2 u0 + g * pr P w2 w1 ∈ O :=
    add_mem (sub_mem (sub_mem hs0 (hP φ0 hφ0 w1 hw1)) (hP w2 hw2 u0 hu0)) (mul_mem hg (hP w2 hw2 w1 hw1))
  have hBe : pr P φ1 u1 =
      -1 + g * (s0 - pr P φ0 w1 - pr P w2 u0 + g * pr P w2 w1) := by
    rw [hφ1e, hu1e]
    simp only [pr_sub_left, pr_sub_right, pr_smul_left, pr_smul_right]
    linear_combination hs0e
  have hB : O.valuation (pr P φ1 u1) = 1 := by
    rw [hBe]
    exact v_add_small O (v_neg_one O) (v_small O hvg hk)
  have hAe : pr P φ u = -1 + g * (-st) := by
    rw [hφu]
    linear_combination -hts
  have hA : O.valuation (pr P φ u) = 1 := by
    rw [hAe]
    exact v_add_small O (v_neg_one O) (v_small O hvg (neg_mem hst))
  have hmid : ∃ um φm, Pair O P Λ1 Λ2 a a' α α' um φm ∧
      O.valuation (pr P φm um) = 1 ∧ O.valuation (pr P φ1 um) = 1 ∧
      O.valuation (pr P φm u) = 1 := by
    rcases (valuationSubring_valuation_le_one_of_mem O (hP φ1 hφ1 u hu)).lt_or_eq with hx | hx
    · rcases (valuationSubring_valuation_le_one_of_mem O (hP φ hφ u1 hu1)).lt_or_eq with hy | hy
      · refine ⟨u + u1, φ, ?_, ?_, ?_, hA⟩
        · unfold Pair
          refine ⟨Λ1.add_mem hu hu1, hφ, fun i => ⟨?_, ?_⟩,
            fun i => ⟨(horth i).2.2.1, (horth i).2.2.2⟩⟩
          · rw [pr_add_right, (horth i).1, (hu1o i).1, add_zero]
          · rw [pr_add_right, (horth i).2.1, (hu1o i).2, add_zero]
        · rw [pr_add_right]
          exact v_add_small O hA hy
        · rw [pr_add_right, add_comm]
          exact v_add_small O hB hx
      · refine ⟨u1, φ, ?_, hy, hB, hA⟩
        unfold Pair
        exact ⟨hu1, hφ, hu1o, fun i => ⟨(horth i).2.2.1, (horth i).2.2.2⟩⟩
    · exact ⟨u, φ, hq, hA, hx, hA⟩
  obtain ⟨um, φm, hm, hcm, hd1, hd2⟩ := hmid
  obtain ⟨T, hT, hTu, hTφ⟩ := exists_isAdmissible_of_chain_lemma_8 hP hp1 hm hq hB hcm hA hd1 hd2
  have hB0 : pr P φ1 u1 ≠ 0 := ne_zero_of_v O hB
  obtain ⟨kc, hkc, hc⟩ : ∃ kc ∈ O, pr P φ u / pr P φ1 u1 = 1 + g * kc := by
    refine ⟨(-st - (s0 - pr P φ0 w1 - pr P w2 u0 + g * pr P w2 w1)) *
      (pr P φ1 u1)⁻¹, mul_mem (sub_mem (neg_mem hst) hk) (inv_memO_of_v O hB), ?_⟩
    rw [div_eq_iff hB0]
    have hinv : (pr P φ1 u1)⁻¹ * pr P φ1 u1 = 1 := inv_mul_cancel₀ hB0
    linear_combination hAe - hBe +
      g * (st + (s0 - pr P φ0 w1 - pr P w2 u0 + g * pr P w2 w1)) * hinv
  have hTinv : ((T⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ u = u1 := by
    rw [← hTu, Matrix.mulVec_mulVec]
    first
    | simp
    | rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hφ0e : φ0 = φ1 + g • w2 := by
    rw [hφ1e]
    abel
  unfold Good at hT
  obtain ⟨h1, h2, h3⟩ := hT
  refine ⟨T, h1, h2, h3, ⟨-w1, Λ1.neg_mem hw1, ?_⟩,
    ⟨kc • φ1 - w2, Λ2.sub_mem (smem O hkc hφ1) hw2, ?_⟩⟩
  · rw [hTinv, hu1e, smul_neg]
    abel
  · rw [hTφ, hc, hφ0e, add_vecMul_field, sub_vecMul_field, smul_vecMul_field, smul_vecMul_field]
    first
    | module
    | (simp only [add_smul, one_smul, smul_sub, mul_smul]; abel)

end PI.UnitaryGroupMassFormula.ScXuExists
end
end

noncomputable section

namespace PI.UnitaryGroupMassFormula.ScXuExists

theorem scXuExists_of (hS : LocSplitP) (hA : BridgeA) (hB : BridgeB) : _root_.PI.ScXuExists.Target :=
  target_of' local_idempotent_existence hS hA hB existsLatticeAutomorphismApprox Gl.glue_holds_var

end PI.UnitaryGroupMassFormula.ScXuExists
