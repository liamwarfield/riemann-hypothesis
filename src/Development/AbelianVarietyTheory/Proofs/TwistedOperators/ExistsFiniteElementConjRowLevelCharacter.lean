module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjCharacterEqProdSymmetricEdgeCharacters

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFrameConjugateLevelSymmetricLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFrameReductionEqFlagBasisOtherInstance
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StandardFrameIntegralityConditions
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StandardFrameIntegralityConditions
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section
namespace GlobalTheory.SeeConjRead.DetUnit

open Classical

section Val
variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)

theorem v_sign_smul {n : ℕ} (s : Equiv.Perm (Fin n)) (x : K) : v (Equiv.Perm.sign s • x) = v x := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign s) with h | h
  · rw [h, one_smul]
  · rw [h, Units.neg_smul, one_smul, Valuation.map_neg]

theorem v_det_le {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (h : ∀ i j, v (M i j) ≤ 1) : v M.det ≤ 1 := by
  rw [Matrix.det_apply]
  refine Valuation.map_sum_le v fun s _ => ?_
  rw [v_sign_smul, map_prod]
  exact Finset.prod_le_one' fun i _ => h _ _

theorem v_det_eq_one {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (d : Fin n → K) (hd : ∀ a, v (d a) = 1)
    (h : ∀ a b, v (M a b - if a = b then d a else 0) < 1) : v M.det = 1 := by
  have hle : ∀ i j, v (M i j) ≤ 1 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      have h1 := h i i
      rw [if_pos rfl] at h1
      have : M i i = (M i i - d i) + d i := by ring
      rw [this]
      exact (Valuation.map_add v _ _).trans (max_le h1.le (hd i).le)
    · have h1 := h i j
      rw [if_neg hij, sub_zero] at h1
      exact h1.le
  have hdiag : ∀ i, v (M i i) = 1 := by
    intro i
    have h1 := h i i
    rw [if_pos rfl] at h1
    have : M i i = (M i i - d i) + d i := by ring
    rw [this, Valuation.map_add_eq_of_lt_right v (by rw [hd i]; exact h1), hd i]
  rw [Matrix.det_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : Equiv.Perm (Fin n)))]
  have hmain : v (Equiv.Perm.sign (1 : Equiv.Perm (Fin n)) • ∏ i, M ((1 : Equiv.Perm (Fin n)) i) i) = 1 := by
    rw [v_sign_smul, map_prod]
    exact Finset.prod_eq_one fun i _ => hdiag i
  have hrest : v (∑ s ∈ Finset.univ.erase (1 : Equiv.Perm (Fin n)), Equiv.Perm.sign s • ∏ i, M (s i) i) < 1 := by
    refine Valuation.map_sum_lt v one_ne_zero fun s hs => ?_
    have hs1 : s ≠ 1 := Finset.ne_of_mem_erase hs
    obtain ⟨i, hi⟩ : ∃ i, s i ≠ i := by
      by_contra hc
      push_neg at hc
      exact hs1 (Equiv.ext hc)
    rw [v_sign_smul, map_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    have h1 := h (s i) i
    rw [if_neg hi, sub_zero] at h1
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (Finset.prod_le_one' fun j _ => hle _ _)) h1
  rw [Valuation.map_add_eq_of_lt_left v (by rw [hmain]; exact hrest), hmain]

end Val

end GlobalTheory.SeeConjRead.DetUnit

namespace GlobalTheory.SeeConjRead.DetUnit

theorem val_le_of_int {D : D7} (Q : Pl D.host.E) (x : EAf D) (hx : x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    Valued.v (GlobalTheory.StdFrames.cpt Q x) ≤ 1 := by
  have := (GlobalTheory.StdFrames.mem_OA_iff x).1 hx Q
  rwa [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] at this

theorem val_det_le {D : D7} {n : ℕ} (Q : Pl D.host.E) (M : Matrix (Fin n) (Fin n) (EAf D))
    (hM : ∀ i j, M i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) : Valued.v (GlobalTheory.StdFrames.cpt Q M.det) ≤ 1 := by
  rw [RingHom.map_det]
  exact v_det_le _ _ fun i j => val_le_of_int Q _ (hM i j)

theorem det_unit : ∀ {D : D7} {n : ℕ} (β₀ : GL (Fin n) (EAf D)) (J U W : Matrix (Fin n) (Fin n) (EAf D)) (Q : Pl D.host.E) (d : Fin n → EAf D), (∀ i j, (Formalism.UG.cT (GlobalTheory.StdFrames.sg D) β₀.val * J * β₀.val) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → (∀ i j, ((β₀⁻¹).val * U) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → (∀ i j, ((β₀⁻¹).val * W) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → (∀ a, Valued.v (GlobalTheory.StdFrames.cpt Q (d a)) = 1) → (∀ a b, SmallAt Q ((Formalism.UG.cT (GlobalTheory.StdFrames.sg D) U * J * W) a b - if a = b then d a else 0)) → Valued.v (GlobalTheory.StdFrames.cpt Q ((β₀⁻¹).val * W).det) = 1 := by
  intro D n β₀ J U W Q d hG hA hB hd hX
  set A := (β₀⁻¹).val * U with hAdef
  set B := (β₀⁻¹).val * W with hBdef
  set G := Formalism.UG.cT (GlobalTheory.StdFrames.sg D) β₀.val * J * β₀.val with hGdef
  have hU : U = β₀.val * A := by rw [hAdef, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  have hW : W = β₀.val * B := by rw [hBdef, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  have hX' : Formalism.UG.cT (GlobalTheory.StdFrames.sg D) U * J * W = Formalism.UG.cT (GlobalTheory.StdFrames.sg D) A * G * B := by
    rw [hGdef, hU, hW, GlobalTheory.StdFrames.cT_mul']
    simp only [Matrix.mul_assoc]
  have h1 : Valued.v (GlobalTheory.StdFrames.cpt Q (Formalism.UG.cT (GlobalTheory.StdFrames.sg D) U * J * W).det) = 1 := by
    rw [RingHom.map_det]
    refine v_det_eq_one _ _ (fun a => GlobalTheory.StdFrames.cpt Q (d a)) hd fun a b => ?_
    have := hX a b
    unfold SmallAt at this
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    split_ifs at this ⊢ with hab
    · rwa [map_sub] at this
    · rwa [sub_zero] at this ⊢
  rw [hX', Matrix.det_mul, Matrix.det_mul] at h1
  simp only [map_mul] at h1
  have ha : Valued.v (GlobalTheory.StdFrames.cpt Q (Formalism.UG.cT (GlobalTheory.StdFrames.sg D) A).det) ≤ 1 :=
    val_det_le Q _ fun i j => Formalism.UG.P.csDual_sig_mem _ (hA j i)
  have hg : Valued.v (GlobalTheory.StdFrames.cpt Q G.det) ≤ 1 := val_det_le Q _ hG
  have hb : Valued.v (GlobalTheory.StdFrames.cpt Q B.det) ≤ 1 := val_det_le Q _ hB
  refine le_antisymm hb ?_
  rw [← h1]
  exact mul_le_of_le_one_left' (mul_le_one' ha hg)

end GlobalTheory.SeeConjRead.DetUnit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StandardFrameIntegralityConditionsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_frame_integrality_conditions : ∀ {D : D7} {n : ℕ} (β₀ : GL (Fin n) (EAf D)) (J U W : Matrix (Fin n) (Fin n) (EAf D)) (Q : Pl D.host.E) (d : Fin n → EAf D), (∀ i j, (Formalism.UG.cT (GlobalTheory.StdFrames.sg D) β₀.val * J * β₀.val) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → (∀ i j, ((β₀⁻¹).val * U) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → (∀ i j, ((β₀⁻¹).val * W) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → (∀ a, Valued.v (GlobalTheory.StdFrames.cpt Q (d a)) = 1) → (∀ a b, SmallAt Q ((Formalism.UG.cT (GlobalTheory.StdFrames.sg D) U * J * W) a b - if a = b then d a else 0)) → Valued.v (GlobalTheory.StdFrames.cpt Q ((β₀⁻¹).val * W).det) = 1 := by
  first | exact @GlobalTheory.SeeConjRead.DetUnit.det_unit | exact GlobalTheory.SeeConjRead.DetUnit.det_unit | (intros; apply GlobalTheory.SeeConjRead.DetUnit.det_unit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFrameLiftingPrescribedReductions
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFrameLiftingPrescribedReductions
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section

namespace GlobalTheory.SeeConjRead.CyclotomicLifting

variable {D : D7}

theorem adj_mem {R : Type} [CommRing R] (T : Subring R) {n : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (h : ∀ i j, A i j ∈ T) (i j : Fin n) : A.adjugate i j ∈ T := by
  let A' : Matrix (Fin n) (Fin n) T := fun a b => ⟨A a b, h a b⟩
  have e : T.subtype.mapMatrix A' = A := by ext a b; rfl
  rw [← e, ← RingHom.map_adjugate]
  exact (A'.adjugate i j).2

theorem loc_inv (Q : Pl D.host.E) {n : ℕ} (A : Matrix (Fin n) (Fin n) (Q.adicCompletion D.host.E))
    (hA : ∀ i j, Valued.v (A i j) ≤ 1) (hd : Valued.v A.det = 1) :
    ∃ A' : Matrix (Fin n) (Fin n) (Q.adicCompletion D.host.E), (∀ i j, Valued.v (A' i j) ≤ 1) ∧ A * A' = 1 := by
  have h0 : A.det ≠ 0 := fun h => by rw [h, map_zero] at hd; exact zero_ne_one hd
  refine ⟨A⁻¹, fun i j => ?_, Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.2 h0)⟩
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv', map_mul, map_inv₀, hd, inv_one, one_mul]
  have := adj_mem (Q.adicCompletionIntegers D.host.E).toSubring A (fun a b => by
    change A a b ∈ Q.adicCompletionIntegers D.host.E
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]; exact hA a b) i j
  change A.adjugate i j ∈ Q.adicCompletionIntegers D.host.E at this
  rwa [HeightOneSpectrum.mem_adicCompletionIntegers] at this

theorem glob {n : ℕ} (c c' : ∀ Q : Pl D.host.E, Matrix (Fin n) (Fin n) (Q.adicCompletion D.host.E))
    (hc : ∀ Q i j, Valued.v (c Q i j) ≤ 1) (hc' : ∀ Q i j, Valued.v (c' Q i j) ≤ 1) (h1 : ∀ Q, c Q * c' Q = 1) :
    ∃ C : GL (Fin n) (EAf D), (∀ i j, C.val i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) ∧
      (∀ i j, (C⁻¹).val i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) ∧
      ∀ Q i j, GlobalTheory.StdFrames.cpt (D := D) Q ((C⁻¹).val i j) = c' Q i j := by
  choose z hzO hz using fun p : Fin n × Fin n => GlobalTheory.AdIsom.exists_of_cpt (D := D) (fun Q => c Q p.1 p.2) (fun Q => hc Q p.1 p.2)
  choose z' hzO' hz' using fun p : Fin n × Fin n => GlobalTheory.AdIsom.exists_of_cpt (D := D) (fun Q => c' Q p.1 p.2) (fun Q => hc' Q p.1 p.2)
  let Z : Matrix (Fin n) (Fin n) (EAf D) := Matrix.of fun i j => z (i, j)
  let Z' : Matrix (Fin n) (Fin n) (EAf D) := Matrix.of fun i j => z' (i, j)
  have hmul : Z * Z' = 1 := by
    ext i j
    refine GlobalTheory.StdFrames.cpt_ext fun Q => ?_
    have e := congrArg (fun M => M i j) (h1 Q)
    simp only [Matrix.mul_apply] at e ⊢
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_mul, Z, Z', Matrix.of_apply, hz, hz']
    rw [e, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  refine ⟨⟨Z, Z', hmul, mul_eq_one_comm.1 hmul⟩, fun i j => hzO (i, j), fun i j => hzO' (i, j),
    fun Q i j => hz' (i, j) Q⟩

theorem col_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) (EAf D)) (w : Fin n → Fin n → EAf D) (i j : Fin n) :
    (A * colMat w) i j = Matrix.mulVec A (w j) i := by
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, colMat]

theorem res_eq (Q : Pl D.host.E) (x : EAf D) (hmem : x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (δ : Formalism.L2.Herm.intAf D.host.F D.host.E) (hcpt : GlobalTheory.StdFrames.cpt Q x = GlobalTheory.StdFrames.cpt Q (δ : EAf D)) :
    Formalism.L2.DIV.resS D.host.F Q ⟨x, hmem⟩ = Formalism.L2.DIV.resS D.host.F Q δ := by
  have e0 : (⟨x, hmem⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = ⟨x - δ, sub_mem hmem δ.2⟩ + δ := Subtype.ext (by simp)
  have e1 := (GlobalTheory.AdIsom.resS_eq_zero_iff_cpt (D := D) Q ⟨x - δ, sub_mem hmem δ.2⟩).2 (by
    change Valued.v (GlobalTheory.StdFrames.cpt Q (x - δ)) < 1
    rw [map_sub, hcpt, sub_self, map_zero]
    exact zero_lt_one)
  rw [e0, (Formalism.L2.DIV.resS D.host.F Q).map_add, e1, zero_add]

end GlobalTheory.SeeConjRead.CyclotomicLifting

namespace GlobalTheory.SeeConjRead


set_option maxHeartbeats 1000000 in
open GlobalTheory.SeeConjRead.CyclotomicLifting in
theorem exists_lift_redIs : ∀ {D : D7} {n : ℕ} (β₀ : GL (Fin n) (EAf D)) (S : Finset (Pl D.host.E)) (W : Pl D.host.E → Fin n → Fin n → EAf D), (∀ Q ∈ S, ∀ i j, ((β₀⁻¹).val * colMat (W Q)) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → (∀ Q ∈ S, Valued.v (GlobalTheory.StdFrames.cpt Q ((β₀⁻¹).val * colMat (W Q)).det) = 1) → ∃ β : GL (Fin n) (EAf D), GlobalTheory.NormSum.AdLattice.lat β = GlobalTheory.NormSum.AdLattice.lat β₀ ∧ ∀ Q ∈ S, RedIs β Q (W Q) := by
  intro D n β₀ S W hint hdet
  have hloc : ∀ Q : Pl D.host.E, ∃ c c' : Matrix (Fin n) (Fin n) (Q.adicCompletion D.host.E),
      (∀ i j, Valued.v (c i j) ≤ 1) ∧ (∀ i j, Valued.v (c' i j) ≤ 1) ∧ c * c' = 1 ∧
      (Q ∈ S → c = ((β₀⁻¹).val * colMat (W Q)).map (GlobalTheory.StdFrames.cpt Q)) := by
    intro Q
    by_cases hQ : Q ∈ S
    · have hA : ∀ i j, Valued.v ((((β₀⁻¹).val * colMat (W Q)).map (GlobalTheory.StdFrames.cpt Q)) i j) ≤ 1 :=
        fun i j => (GlobalTheory.AdIsom.mem_OA _).1 (hint Q hQ i j) Q
      have hd : Valued.v (((β₀⁻¹).val * colMat (W Q)).map (GlobalTheory.StdFrames.cpt Q)).det = 1 := by
        rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
        exact hdet Q hQ
      obtain ⟨A', hA', h1⟩ := loc_inv Q _ hA hd
      exact ⟨_, A', hA, hA', h1, fun _ => rfl⟩
    · refine ⟨1, 1, fun i j => ?_, fun i j => ?_, one_mul _, fun h => absurd h hQ⟩ <;>
      · rw [Matrix.one_apply]; split_ifs <;> simp
  choose c c' hc hc' h1 hS using hloc
  obtain ⟨C, hCi, hCi', hCc⟩ := glob c c' hc hc' h1
  refine ⟨β₀ * C, le_antisymm (GlobalTheory.NormSum.AdLattice.lat_le_of_int fun i j => ?_)
    (GlobalTheory.NormSum.AdLattice.lat_le_of_int fun i j => ?_), fun Q hQ i j => ?_⟩
  · rw [inv_mul_cancel_left]; exact hCi i j
  · rw [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]; exact hCi' i j
  have key : Matrix.mulVec ((β₀ * C)⁻¹).val (W Q j) i = ((C⁻¹).val * ((β₀⁻¹).val * colMat (W Q))) i j := by
    rw [← Matrix.mul_assoc, col_apply, mul_inv_rev, Units.val_mul]
  rw [key]
  have hmem : ((C⁻¹).val * ((β₀⁻¹).val * colMat (W Q))) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    rw [Matrix.mul_apply]
    exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hCi' i k) (hint Q hQ k j)
  refine ⟨hmem, ?_⟩
  have hcpt : GlobalTheory.StdFrames.cpt Q (((C⁻¹).val * ((β₀⁻¹).val * colMat (W Q))) i j) = (1 : Matrix (Fin n) (Fin n) _) i j := by
    have e : c' Q * c Q = 1 := mul_eq_one_comm.1 (h1 Q)
    rw [hS Q hQ] at e
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← e, Matrix.mul_apply, Matrix.mul_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, hCc]
    rfl
  split_ifs with hij
  · have h1' : GlobalTheory.StdFrames.cpt Q (((C⁻¹).val * ((β₀⁻¹).val * colMat (W Q))) i j) =
        GlobalTheory.StdFrames.cpt Q ((1 : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) := by
      rw [hcpt, Matrix.one_apply, if_pos hij]
      exact (map_one _).symm
    exact (res_eq Q _ hmem 1 h1').trans (map_one _)
  · have h0' : GlobalTheory.StdFrames.cpt Q (((C⁻¹).val * ((β₀⁻¹).val * colMat (W Q))) i j) =
        GlobalTheory.StdFrames.cpt Q ((0 : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) := by
      rw [hcpt, Matrix.one_apply, if_neg hij]
      exact (map_zero _).symm
    exact (res_eq Q _ hmem 0 h0').trans (map_zero _)

end GlobalTheory.SeeConjRead
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFrameLiftingPrescribedReductionsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frame_lifting_prescribed_reductions : ∀ {D : D7} {n : ℕ} (β₀ : GL (Fin n) (EAf D)) (S : Finset (Pl D.host.E)) (W : Pl D.host.E → Fin n → Fin n → EAf D), (∀ Q ∈ S, ∀ i j, ((β₀⁻¹).val * colMat (W Q)) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → (∀ Q ∈ S, Valued.v (GlobalTheory.StdFrames.cpt Q ((β₀⁻¹).val * colMat (W Q)).det) = 1) → ∃ β : GL (Fin n) (EAf D), GlobalTheory.NormSum.AdLattice.lat β = GlobalTheory.NormSum.AdLattice.lat β₀ ∧ ∀ Q ∈ S, RedIs β Q (W Q) := by
  first | exact @GlobalTheory.SeeConjRead.exists_lift_redIs | exact GlobalTheory.SeeConjRead.exists_lift_redIs | (intros; apply GlobalTheory.SeeConjRead.exists_lift_redIs <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFrameReductionEqFlagBasisOtherInstance
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section

namespace GlobalTheory.SeeConjRead

theorem cT_mul_entry {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (U J W : Matrix (Fin n) (Fin n) A) (a b : Fin n) :
    (Formalism.UG.cT σ U * J * W) a b = Formalism.UG.hform σ J (fun i => U i a) (fun i => W i b) := by
  unfold Formalism.UG.cT Formalism.UG.hform
  simp only [Matrix.mul_apply, Finset.sum_mul, Matrix.transpose_apply, Matrix.map_apply]
  exact Finset.sum_comm

theorem over_g {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (hL : R.toLevCh.Is A.μ0) {Q : Pl D.host.E}
    (hQ : Q ∈ R.Pg) : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal := by
  obtain ⟨k, hk⟩ := (hL.Pg Q).1 hQ
  have hmem : ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (Q.under (𝓞 D.host.K)).asIdeal := by
    rw [show Q.under (𝓞 D.host.K) = R.C.P.pb k from hk]
    exact R.C.P.pb_over k
  rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast] at hmem
  rw [Nat.cast_mul]
  fin_cases k
  · exact Ideal.mul_mem_right _ _ hmem
  · exact Ideal.mul_mem_left _ _ hmem

theorem exists_frame_redIs : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → ∃ β : GL (Fin (Yc D 0).rank) (EAf D), IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) ∧ ∀ PP ∈ R.Pg, RedIs β PP (flagAt X h PP) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h hL _
  have hn : (Yc D 0).rank = 2 * D.R.rS + D.R.k + 1 := by
    rw [show (Yc D 0).rank = D.R.rankY 0 from D.sp.Y_rank 0 (Nat.zero_le _)]
    have hm := D.R.m_even
    have h2 := D.R.two_le_m
    unfold Formalism.BasicNotions.Ranks.rankY Formalism.BasicNotions.Ranks.rS Formalism.BasicNotions.Ranks.r
    obtain ⟨c, hc⟩ := hm
    omega
  obtain ⟨β₀, hβ₀⟩ := GlobalTheory.StdFrames.exists_base (Yc D 0)
  have hG := (GlobalTheory.StdFrames.unimod_of_isSD (GlobalTheory.StdFrames.isSD_one hβ₀)).1
  have hint : ∀ (PP : Pl D.host.E) (i j : Fin (Yc D 0).rank),
      ((β₀⁻¹).val * colMat (flagAt X h PP)) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧
      ((β₀⁻¹).val * colMat (pairAt X h PP)) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    have cast_fun_mem_Lf {I J : Formalism.MainNotions.S.AutInst} (h : I = J) {m : ℕ}
        (f : Fin m → Formalism.L2.SG.HidaSetting.VA I) (hf : ∀ a, f a ∈ I.Lf) (a : Fin m) :
        (cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Fin m → Formalism.L2.SG.HidaSetting.VA I) h) f) a ∈ J.Lf := by
      subst h
      exact hf a
    have cast_mem_Lf {I J : Formalism.MainNotions.S.AutInst} (h : I = J)
        (v : Formalism.L2.SG.HidaSetting.VA I) (hv : v ∈ I.Lf) :
        cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Formalism.L2.SG.HidaSetting.VA I) h) v ∈ J.Lf := by
      subst h
      exact hv
    have flagV_mem {M : Type} [Zero M] (S : Set M) (h0 : (0 : M) ∈ S) (ρ k n : ℕ)
        (e f : Fin ρ → M) (b : Fin k → M) (z : M) (he : ∀ a, e a ∈ S)
        (hf : ∀ a, f a ∈ S) (hb : ∀ a, b a ∈ S) (hz : z ∈ S) (i : Fin n) :
        flagV ρ k n e f b z i ∈ S := by
      unfold flagV
      split_ifs
      exacts [he _, hb _, hz, hf _, h0]
    intro PP i j
    have hF : IsFrame β₀ (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) := hβ₀ ▸ GlobalTheory.StdFrames.isFrame_lat β₀
    have hLf := GlobalTheory.KgFrame.Lf_eq D
    have key : ∀ v : Fin (Yc D 0).rank → EAf D, v ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf →
        Matrix.mulVec (β₀⁻¹).val v i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
      intro v hv
      rw [hLf] at hv
      exact (hF v).1 hv i
    set S : Set (Fin (Yc D 0).rank → EAf D) := {v | v ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf}
    have h0 : (0 : Fin (Yc D 0).rank → EAf D) ∈ S := by
      show (0 : Fin (Yc D 0).rank → EAf D) ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf
      exact zero_mem _
    obtain ⟨hef, hz, hbw⟩ := X.vectorsInLattice
    have he : ∀ a, e0T X h a ∈ S := cast_fun_mem_Lf h X.e0 (fun a => (hef a).1)
    have hf : ∀ a, f0T X h a ∈ S := cast_fun_mem_Lf h X.f0 (fun a => (hef a).2)
    have hb : ∀ a, bwT X h a ∈ S := cast_fun_mem_Lf h X.bw (fun a => (hbw a).1)
    have hbd : ∀ a, bwdT X h a ∈ S := cast_fun_mem_Lf h X.bwd (fun a => (hbw a).2)
    have hzz : z0T X h ∈ S := cast_mem_Lf h X.z0 hz
    constructor
    · change Matrix.mulVec (β₀⁻¹).val (flagAt X h PP j) i ∈ _
      apply key
      unfold flagAt
      split_ifs
      · exact flagV_mem S h0 _ _ _ _ _ _ _ he hf hb hzz j
      · exact flagV_mem S h0 _ _ _ _ _ _ _ he hf (fun a => hbd _) hzz j
    · change Matrix.mulVec (β₀⁻¹).val (pairAt X h PP j) i ∈ _
      apply key
      unfold pairAt
      split_ifs
      · exact flagV_mem S h0 _ _ _ _ _ _ _ hf he hbd hzz j
      · exact flagV_mem S h0 _ _ _ _ _ _ _ hf he (fun a => hb _) hzz j
  have hdet : ∀ Q ∈ R.Pg,
      Valued.v (GlobalTheory.StdFrames.cpt Q ((β₀⁻¹).val * colMat (flagAt X h Q)).det) = 1 := by
    intro Q hQ
    have hg := over_g R hL hQ
    refine GlobalTheory.T.standard_frame_integrality_conditions β₀ (GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices.ratM (Yc D 0).gram) (colMat (pairAt X h Q))
      (colMat (flagAt X h Q)) Q (fun a => sgnD D.R.rS D.R.k a) hG (fun i j => (hint Q i j).2)
      (fun i j => (hint Q i j).1) ?_ ?_
    · intro a
      unfold sgnD
      split_ifs <;> simp
    · intro a b
      rw [cT_mul_entry]
      change SmallAt Q (hY D (pairAt X h Q a) (flagAt X h Q b) - _)
      by_cases hc : GlobalTheory.StdFrames.cpt Q (ewT X h) = 1
      · rw [pairAt, flagAt, if_pos hc, if_pos hc]
        exact GlobalTheory.T.flagPairingTable_diagonal_modSmall (hY D) (SmallAt Q) D.R.rS D.R.k _ hn _ _ _ _ _ (GlobalTheory.T.flagPairingTable_idempotentComponent_one X h Q hg hc) a b
      · rw [pairAt, flagAt, if_neg hc, if_neg hc]
        exact GlobalTheory.T.flagPairingTable_diagonal_modSmall (hY D) (SmallAt Q) D.R.rS D.R.k _ hn _ _ _ _ _ (GlobalTheory.T.flagPairingTable_idempotentComponent_ne_one X h Q hg hc) a b
  obtain ⟨β, hβ, hred⟩ := GlobalTheory.T.exists_frame_lifting_prescribed_reductions β₀ R.Pg (flagAt X h) (fun Q _ i j => (hint Q i j).1) hdet
  refine ⟨β, ?_, hred⟩
  rw [hβ₀, ← hβ]
  exact GlobalTheory.StdFrames.isFrame_lat β

end GlobalTheory.SeeConjRead

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFrameReductionEqFlagBasisOtherInstanceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frame_reduction_eq_flagBasis_otherInstance : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → ∃ β : GL (Fin (Yc D 0).rank) (EAf D), IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) ∧ ∀ PP ∈ R.Pg, RedIs β PP (flagAt X h PP) := by
  exact @GlobalTheory.SeeConjRead.exists_frame_redIs
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFrameRescaleConjReductionsDiagonalStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frame_rescale_conj_reductions_diagonal : ∀ {D : D7} {n r : ℕ} (hr : r ≤ n) (β : GL (Fin n) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), IsFrame β Λ → ∀ (Pg : Finset (Pl D.host.E)) (d : ∀ PP : Pl D.host.E, Fin r → (kP PP)ˣ), ∃ β' : GL (Fin n) (EAf D), IsFrame β' Λ ∧ (∀ M, M ∈ St β' ↔ M ∈ St β) ∧ ∀ PP ∈ Pg, ∀ M ∈ St β, upperLeftBlock hr (redFn β' PP M) = (diagGL (d PP))⁻¹ * upperLeftBlock hr (redFn β PP M) * diagGL (d PP) := by
  first | exact @GlobalTheory.FrameRescale.exists_rescale | exact GlobalTheory.FrameRescale.exists_rescale | (intros; apply GlobalTheory.FrameRescale.exists_rescale <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSymmetricPositionLevelFirstSpaceIff
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSymmetricPositionLevelFirstSpaceIff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section

namespace GlobalTheory.SeeConjRead

theorem mem_levS_dat0_PsharpSym_iff : ∀ {D : D7} {T : Type} (Lc : LevCh D T) (β : GL (Fin (Yc D 0).rank) (EAf D)) (ψ0 : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) (κ : GA D (Yc D 0)), (κ ∈ levS (Yc D 0) β (Lc.dat0 (PsharpSym Lc.Pg D.R.r D.R.rS D.R.k ψ0)) ↔ κ ∈ GfC (Yc D 0) ∧ finE (Yc D 0) κ ∈ UA D.sp.cm (Yc D 0).gram ∧ finE (Yc D 0) κ ∈ St β ∧ ∀ PP ∈ Lc.Pg, upperLeftBlock (r_le_Y (D := D) 0) (redFn β PP (finE (Yc D 0) κ)) ∈ unipSym (kP PP) D.R.r D.R.rS D.R.k) ∧ (κ ∈ levS (Yc D 0) β (Lc.dat0 (PsharpSym Lc.Pg D.R.r D.R.rS D.R.k ψ0)) → levChi (Yc D 0) β (Lc.dat0 (PsharpSym Lc.Pg D.R.r D.R.rS D.R.k ψ0)) κ = ∏ PP ∈ Lc.Pg, ψ0 PP (edgeSum (symEdge D.R.rS D.R.k) (upperLeftBlock (r_le_Y (D := D) 0) (redFn β PP (finE (Yc D 0) κ))))) := by
  intro D T Lc β ψ0 κ
  have hH : ∀ g : G0 Lc.Pg D.R.r, g ∈ (PsharpSym Lc.Pg D.R.r D.R.rS D.R.k ψ0).H ↔
      ∀ PP : ↥Lc.Pg, g PP ∈ unipSym (kP PP.1) D.R.r D.R.rS D.R.k := by
    intro g
    show g ∈ Subgroup.pi Set.univ _ ↔ _
    rw [Subgroup.mem_pi]
    simp
  refine ⟨?_, fun hκ => ?_⟩
  · rw [GlobalTheory.SeeConjReord.mem_levelSubgroup_principalDatum_iff, hH]
    simp only [GlobalTheory.SeeConjReord.r0]
    constructor
    · rintro ⟨⟨h0, h1, h2⟩, h3⟩
      exact ⟨h0, h1, h2, fun PP hPP => h3 ⟨PP, hPP⟩⟩
    · rintro ⟨h0, h1, h2, h3⟩
      exact ⟨⟨h0, h1, h2⟩, fun PP => h3 PP.1 PP.2⟩
  · have hm := ((GlobalTheory.SeeConjReord.mem_levelSubgroup_principalDatum_iff Lc _ β κ).1 hκ).2
    rw [GlobalTheory.SeeConjReord.principalRowLevelCharacter_trivial, extendOne_of_mem _ hm]
    letI : IsOneApply ((PsharpSym Lc.Pg D.R.r D.R.rS D.R.k ψ0).H →* ℂˣ) := ⟨fun _ => rfl⟩
    letI : IsMulApply ((PsharpSym Lc.Pg D.R.r D.R.rS D.R.k ψ0).H →* ℂˣ) := ⟨fun _ _ _ => rfl⟩
    erw [prod_apply, Units.coe_prod]
    rw [← Finset.prod_coe_sort Lc.Pg]
    rfl

end GlobalTheory.SeeConjRead
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSymmetricPositionLevelFirstSpaceIffStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_symmetricPositionLevel_firstSpace_iff : ∀ {D : D7} {T : Type} (Lc : LevCh D T) (β : GL (Fin (Yc D 0).rank) (EAf D)) (ψ0 : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) (κ : GA D (Yc D 0)), (κ ∈ levS (Yc D 0) β (Lc.dat0 (PsharpSym Lc.Pg D.R.r D.R.rS D.R.k ψ0)) ↔ κ ∈ GfC (Yc D 0) ∧ finE (Yc D 0) κ ∈ UA D.sp.cm (Yc D 0).gram ∧ finE (Yc D 0) κ ∈ St β ∧ ∀ PP ∈ Lc.Pg, upperLeftBlock (r_le_Y (D := D) 0) (redFn β PP (finE (Yc D 0) κ)) ∈ unipSym (kP PP) D.R.r D.R.rS D.R.k) ∧ (κ ∈ levS (Yc D 0) β (Lc.dat0 (PsharpSym Lc.Pg D.R.r D.R.rS D.R.k ψ0)) → levChi (Yc D 0) β (Lc.dat0 (PsharpSym Lc.Pg D.R.r D.R.rS D.R.k ψ0)) κ = ∏ PP ∈ Lc.Pg, ψ0 PP (edgeSum (symEdge D.R.rS D.R.k) (upperLeftBlock (r_le_Y (D := D) 0) (redFn β PP (finE (Yc D 0) κ))))) := by
  first | exact @GlobalTheory.SeeConjRead.mem_levS_dat0_PsharpSym_iff | exact GlobalTheory.SeeConjRead.mem_levS_dat0_PsharpSym_iff | (intros; apply GlobalTheory.SeeConjRead.mem_levS_dat0_PsharpSym_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFrameConjugateLevelSymmetricLevel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

theorem GlobalTheory.SeeConj.exists_frame_symLevel : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → ∀ ψ0 : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ, IsGenericPsi R.Pg ψ0 → ∃ β₃ : GL (Fin (Yc D 0).rank) (EAf D), IsFrame β₃ (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) ∧ ∀ κ : GA D (Yc D 0), (κ ∈ (iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2} ↔ κ ∈ levS (Yc D 0) β₃ (R.dat0 (PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0))) ∧ (κ ∈ levS (Yc D 0) β₃ (R.dat0 (PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0)) → star (X.chi2 ((iotaX X h).toMulEquiv κ).2) = levChi (Yc D 0) β₃ (R.dat0 (PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0)) κ) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h hIs hGrp ψ0 hψ0
  classical
  obtain ⟨β, hβ, hred⟩ := GlobalTheory.T.exists_frame_reduction_eq_flagBasis_otherInstance R F X h hIs hGrp
  obtain ⟨ψ', a, hψ', hchi⟩ := GlobalTheory.T.conjCharacter_eq_prod_symmetricEdge_characters_alt R F X h hIs hGrp β hβ hred
  have hsc : ∀ PP ∈ R.Pg, ∃ d : Fin D.R.r → (kP PP)ˣ, ∀ u : GL (Fin D.R.r) (kP PP), u ∈ unipSym (kP PP) D.R.r D.R.rS D.R.k →
      ψ' PP (∑ i, ∑ j, if symEdge D.R.rS D.R.k i j then (a PP i j : kP PP) * u.val i j else 0) =
        ψ0 PP (edgeSum (symEdge D.R.rS D.R.k) ((diagGL d)⁻¹ * u * diagGL d)) :=
    fun PP hP => GlobalTheory.T.exists_diagonal_conj_edgeSum_addChar_finiteField (κf := kP PP) ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 PP.isMaximal)
      D.R.rS D.R.k (ψ' PP) (ψ0 PP) (hψ' PP hP) (hψ0 PP hP) (a PP)
  choose! dd hdd using hsc
  obtain ⟨β₃, hβ₃, hSt, hconj⟩ := GlobalTheory.T.exists_frame_rescale_conj_reductions_diagonal (r_le_Y (D := D) 0) β _ hβ R.Pg dd
  refine ⟨β₃, hβ₃, fun κ => ?_⟩
  obtain ⟨hR1, hR2, hUA⟩ := GlobalTheory.T.instanceIota_readout_realTrivial_stabilizer_unitary X h β hβ κ
  obtain ⟨hL1, hL2⟩ := GlobalTheory.T.mem_symmetricPositionLevel_firstSpace_iff R.toLevCh β₃ ψ0 κ
  have hgrp := GlobalTheory.T.mem_K2_iff_upperLeftBlock_reductions R F X h hIs hGrp β hβ hred κ
  have key : κ ∈ (iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2} ↔
      κ ∈ levS (Yc D 0) β₃ (R.dat0 (PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0)) := by
    refine Iff.trans ?_ hL1.symm
    show ((iotaX X h).toMulEquiv κ).1 = 1 ∧ ((iotaX X h).toMulEquiv κ).2 ∈ X.K2 ↔ _
    constructor
    · rintro ⟨h1, h2⟩
      have hK : ((iotaX X h).toMulEquiv κ).2 ∈ X.B.I.Kset := (Formalism.L2.SG.Closed.level_subgroup_properties X).2.1 _ h2
      have hS := hR2.1 hK
      have hG' := (hgrp hK hS).1 h2
      refine ⟨hR1.1 h1, hUA, (hSt _).2 hS, fun PP hP => ?_⟩
      rw [hconj PP hP _ hS]
      exact (unipSym_conj_iff _ _ _ _).1 (hG' PP hP)
    · rintro ⟨h1, _, h3, h4⟩
      have hS : finE (Yc D 0) κ ∈ St β := (hSt _).1 h3
      have hK := hR2.2 hS
      refine ⟨hR1.2 h1, (hgrp hK hS).2 fun PP hP => ?_⟩
      have h5 := h4 PP hP
      rw [hconj PP hP _ hS] at h5
      exact (unipSym_conj_iff _ _ _ _).2 h5
  refine ⟨key, fun hk => ?_⟩
  obtain ⟨h1, _, h3, h4⟩ := hL1.1 hk
  have hS : finE (Yc D 0) κ ∈ St β := (hSt _).1 h3
  have hK := hR2.2 hS
  have hK2 : ((iotaX X h).toMulEquiv κ).2 ∈ X.K2 := (key.2 hk).2
  rw [hL2 hk, hchi κ hS hK2]
  refine Finset.prod_congr rfl fun PP hP => ?_
  rw [hconj PP hP _ hS]
  exact hdd PP hP _ ((hgrp hK hS).1 hK2 PP hP)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFrameConjugateLevelSymmetricLevelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frame_conjugate_level_symmetricLevel : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → ∀ ψ0 : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ, IsGenericPsi R.Pg ψ0 → ∃ β₃ : GL (Fin (Yc D 0).rank) (EAf D), IsFrame β₃ (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) ∧ ∀ κ : GA D (Yc D 0), (κ ∈ (iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2} ↔ κ ∈ levS (Yc D 0) β₃ (R.dat0 (PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0))) ∧ (κ ∈ levS (Yc D 0) β₃ (R.dat0 (PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0)) → star (X.chi2 ((iotaX X h).toMulEquiv κ).2) = levChi (Yc D 0) β₃ (R.dat0 (PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0)) κ) := by
  first | exact @GlobalTheory.SeeConj.exists_frame_symLevel | exact GlobalTheory.SeeConj.exists_frame_symLevel | (intros; apply GlobalTheory.SeeConj.exists_frame_symLevel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevSLevChiOfFrames
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevSLevChiOfFrames
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped TensorProduct

namespace GlobalTheory.FrameTransfer

open Formalism.L2.DIV Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem entry_mem {β β' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)}
    (hβ : IsFrame β Λ) (hβ' : IsFrame β' Λ) (i j : Fin n) :
    ((β⁻¹ * β' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _) i j ∈ Formalism.L2.Herm.intAf F E := by
  have key := (hβ (β'.1 *ᵥ Pi.single j 1)).1 ((hβ' _).2 (by
    intro k
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    by_cases h : k = j
    · subst h; simp only [Pi.single_eq_same]; exact Subring.one_mem _
    · rw [Pi.single_eq_of_ne h]; exact Subring.zero_mem _)) i
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, Matrix.mulVec_single_one] at key
  exact key

theorem exists_int {β β' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)}
    (hβ : IsFrame β Λ) (hβ' : IsFrame β' Λ) : ∃ y : GL (Fin n) (Formalism.L2.Herm.intAf F E), intGL F E n y = β⁻¹ * β' := by
  set φ := (Formalism.L2.Herm.intAf F E).subtype
  have hinj : Function.Injective (RingHom.mapMatrix (m := Fin n) φ) := fun a b h => by
    ext i j; exact congrArg Subtype.val (Subtype.ext (congrFun (congrFun h i) j))
  let M : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E) := fun i j => ⟨_, entry_mem hβ hβ' i j⟩
  let M' : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E) := fun i j => ⟨_, entry_mem hβ' hβ i j⟩
  have hM : RingHom.mapMatrix φ M = ((β⁻¹ * β' : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) := rfl
  have hM' : RingHom.mapMatrix φ M' = ((β'⁻¹ * β : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) := rfl
  have e1 : M * M' = 1 := hinj (by
    rw [map_mul, map_one, hM, hM', ← Units.val_mul]
    simp)
  have e2 : M' * M = 1 := hinj (by
    rw [map_mul, map_one, hM, hM', ← Units.val_mul]
    simp)
  exact ⟨⟨M, M', e1, e2⟩, Units.ext hM⟩

theorem st_le {β β' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)}
    (hβ : IsFrame β Λ) (hβ' : IsFrame β' Λ) : St β' ≤ St β := by
  obtain ⟨y, hy⟩ := exists_int hβ hβ'
  rintro x ⟨z, rfl⟩
  refine ⟨y * z * y⁻¹, ?_⟩
  simp only [frGL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv, hy]
  group

theorem st_eq {β β' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)}
    (hβ : IsFrame β Λ) (hβ' : IsFrame β' Λ) : St β = St β' :=
  le_antisymm (st_le hβ' hβ) (st_le hβ hβ')

section Lev

variable [StarRing E] {LL : Type} [CommRing LL]

theorem mem_parLev_iff {hc : CMData F E} {J : Matrix (Fin n) (Fin n) E} {β β' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)}
    {D : LevDat E LL n} (hSt : St β = St β')
    (hg : ∀ PP ∈ D.Pg, ∀ x, redFn β PP x = redFn β' PP x) (hq : ∀ PP ∈ D.Q, ∀ x, redFn β PP x = redFn β' PP x)
    (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : x ∈ parLev hc J β D ↔ x ∈ parLev hc J β' D := by
  simp only [parLev, Subgroup.mem_inf, Subgroup.mem_iInf, mem_parah, hSt]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    refine ⟨⟨⟨h1, h2⟩, fun PP hP => ⟨(h3 PP hP).1, hg PP hP x ▸ (h3 PP hP).2⟩⟩, fun PP hP => ⟨(h4 PP hP).1, hq PP hP x ▸ (h4 PP hP).2⟩⟩
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    refine ⟨⟨⟨h1, h2⟩, fun PP hP => ⟨(h3 PP hP).1, (hg PP hP x).symm ▸ (h3 PP hP).2⟩⟩, fun PP hP => ⟨(h4 PP hP).1, (hq PP hP x).symm ▸ (h4 PP hP).2⟩⟩

theorem rTup_eq {β β' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {D : LevDat E LL n}
    (hg : ∀ PP ∈ D.Pg, ∀ x, redFn β PP x = redFn β' PP x) (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
    rTup β D x = rTup β' D x := by
  funext PP
  simp only [rTup, hg PP.1 PP.2 x]

theorem mem_lev_iff {hc : CMData F E} {J : Matrix (Fin n) (Fin n) E} {β β' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)}
    {D : LevDat E LL n} (hSt : St β = St β')
    (hg : ∀ PP ∈ D.Pg, ∀ x, redFn β PP x = redFn β' PP x) (hq : ∀ PP ∈ D.Q, ∀ x, redFn β PP x = redFn β' PP x)
    (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : x ∈ lev hc J β D ↔ x ∈ lev hc J β' D := by
  show (x ∈ parLev hc J β D ∧ rTup β D x ∈ D.P.H) ↔ (x ∈ parLev hc J β' D ∧ rTup β' D x ∈ D.P.H)
  rw [mem_parLev_iff hSt hg hq, rTup_eq hg]

theorem levFn_eq {β β' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {D : LevDat E LL n}
    (hg : ∀ PP ∈ D.Pg, ∀ x, redFn β PP x = redFn β' PP x) (hq : ∀ PP ∈ D.Q, ∀ x, redFn β PP x = redFn β' PP x)
    (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : levFn β D x = levFn β' D x := by
  unfold levFn
  rw [rTup_eq hg]
  congr 1
  · congr 1
    exact Finset.prod_congr rfl fun PP hP => by rw [hg PP hP x]
  · exact Finset.prod_congr rfl fun PP hP => by rw [hq PP hP x]

end Lev

end GlobalTheory.FrameTransfer

theorem GlobalTheory.levS_levChi_of_frames : ∀ {D : D7} (V : HSp D) (β β' : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (L : LevDat D.host.E ℂ V.rank), IsFrame β Λ → IsFrame β' Λ → (∀ PP ∈ L.Pg, ∀ x, redFn β PP x = redFn β' PP x) → (∀ PP ∈ L.Q, ∀ x, redFn β PP x = redFn β' PP x) → ∀ κ : GA D V, (κ ∈ levS V β L ↔ κ ∈ levS V β' L) ∧ levChi V β L κ = levChi V β' L κ := by
  intro D V β β' Λ L hβ hβ' hg hq κ
  have hSt := GlobalTheory.FrameTransfer.st_eq hβ hβ'
  refine ⟨?_, ?_⟩
  · show κ ∈ levG V β L ↔ κ ∈ levG V β' L
    simp only [levG, levA, Subgroup.mem_inf, Subgroup.mem_comap]
    rw [GlobalTheory.FrameTransfer.mem_lev_iff hSt hg hq]
  · unfold levChi
    rw [GlobalTheory.FrameTransfer.levFn_eq hg hq]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevSLevChiOfFramesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levS_iff_and_levChi_eq_of_redFn_eq : ∀ {D : D7} (V : HSp D) (β β' : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (L : LevDat D.host.E ℂ V.rank), IsFrame β Λ → IsFrame β' Λ → (∀ PP ∈ L.Pg, ∀ x, redFn β PP x = redFn β' PP x) → (∀ PP ∈ L.Q, ∀ x, redFn β PP x = redFn β' PP x) → ∀ κ : GA D V, (κ ∈ levS V β L ↔ κ ∈ levS V β' L) ∧ levChi V β L κ = levChi V β' L κ := by
  first | exact @GlobalTheory.levS_levChi_of_frames | exact GlobalTheory.levS_levChi_of_frames | (intros; apply GlobalTheory.levS_levChi_of_frames <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteElementConjRowLevelCharacter
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.SeeConj.exists_conj_level : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → ∃ t ∈ GfC (Yc D 0), ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) ∧ IsFrame (finE (Yc D 0) t * R.βY 0) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h hIs hGrp _hMod
  obtain ⟨ψ0, hψ0, _hψ, π, _hπ, hmem, hchi⟩ := hGrp.levels
  obtain ⟨β₃, hfr₃, hD1⟩ := GlobalTheory.T.exists_frame_conjugate_level_symmetricLevel R F X h hIs hGrp ψ0 hψ0
  obtain ⟨β₂, hfr₂, hD2⟩ := GlobalTheory.T.exists_frame_reordering_levelData R.toLevCh (R.levR F true) (PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0) π hmem hchi β₃ hfr₃
  obtain ⟨t₀, ht₀, hfr₀⟩ := GlobalTheory.T.exists_finiteUnitary_selfDualFrame_to_baseLatticeFrame (Yc D 0) (R.βY 0) (R.ΛY 0) _ (hIs.βY 0 (by have := D.R.two_le_m; omega))
  obtain ⟨u, hu, hfru, hred⟩ := GlobalTheory.T.exists_unitary_matching_frames_at_nonconjugate_places (Yc D 0) R.Pg (GlobalTheory.T.levelPlaces_not_isConjPlace_realDat R F hIs hGrp) _ β₂ hfr₀ hfr₂
  have hfe : finE (Yc D 0) (u * t₀) * R.βY 0 = finE (Yc D 0) u * (finE (Yc D 0) t₀ * R.βY 0) := by
    rw [map_mul, mul_assoc]
  refine ⟨u * t₀, mul_mem hu ht₀, ?_, by rw [hfe]; exact hfru⟩
  intro (k : GA D (Yc D 0))
  have hA := GlobalTheory.T.levelSubgroup_conj_finite_moves_frame (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true)) (u * t₀) (mul_mem hu ht₀) k
  rw [hfe] at hA
  have hC := GlobalTheory.T.levS_iff_and_levChi_eq_of_redFn_eq (Yc D 0) (finE (Yc D 0) u * (finE (Yc D 0) t₀ * R.βY 0)) β₂ _ (R.dat0 (R.levR F true)) hfru hfr₂
    (fun PP hPP x => hred PP hPP x) (fun PP hPP => absurd hPP (Finset.notMem_empty _)) ((u * t₀) * k * (u * t₀)⁻¹)
  have h2 := hD2 ((u * t₀) * k * (u * t₀)⁻¹)
  have h1 := hD1 ((u * t₀) * k * (u * t₀)⁻¹)
  have hm : ∀ hk : k ∈ levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true)), (u * t₀) * k * (u * t₀)⁻¹ ∈ levS (Yc D 0) β₃ (R.dat0 (PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0)) :=
    fun hk => h2.1.1 (hC.1.1 (hA.1.1 hk))
  have key : (k ∈ levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true)) ↔ (u * t₀) * k * (u * t₀)⁻¹ ∈ (iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) ∧
      (k ∈ levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true)) → star (X.chi2 ((iotaX X h).toMulEquiv ((u * t₀) * k * (u * t₀)⁻¹)).2) = levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true)) k) :=
    ⟨hA.1.trans (hC.1.trans (h2.1.trans h1.1.symm)), fun hk => by rw [h1.2 (hm hk), ← h2.2, ← hC.2, hA.2]⟩
  have e : ((u * t₀)⁻¹⁻¹ : GA D (D.sp.Y 0)) = u * t₀ := inv_inv (G := GA D (D.sp.Y 0)) _
  rw [e]
  exact key
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteElementConjRowLevelCharacterStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_element_conj_rowLevel_character : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → ∃ t ∈ GfC (Yc D 0), ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) ∧ IsFrame (finE (Yc D 0) t * R.βY 0) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) := by
  first | exact @GlobalTheory.SeeConj.exists_conj_level | exact GlobalTheory.SeeConj.exists_conj_level | (intros; apply GlobalTheory.SeeConj.exists_conj_level <;> assumption)
end
