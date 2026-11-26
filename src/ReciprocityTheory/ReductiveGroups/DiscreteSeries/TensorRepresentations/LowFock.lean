module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Transported
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.LowFockB
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PRVComponents
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.WeylPos
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.CFPrimeB

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.LowFockD
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem lfD_cnt (P : Fin n → Prop) [DecidablePred P] {a b : Fin n} (hab : a < b) :
    (univ.filter fun c => a < c ∧ P c).card + (univ.filter fun c => c < b ∧ P c).card =
      (univ.filter fun c => c < a ∧ P c).card + (univ.filter fun c => b < c ∧ P c).card +
        2 * (univ.filter fun c => a < c ∧ c < b ∧ P c).card +
        (univ.filter fun c => c = a ∧ P c).card + (univ.filter fun c => c = b ∧ P c).card := by
  have key : ∀ c : Fin n, ((if a < c ∧ P c then 1 else 0) + (if c < b ∧ P c then 1 else 0) : ℕ) =
      (if c < a ∧ P c then 1 else 0) + (if b < c ∧ P c then 1 else 0) +
        2 * (if a < c ∧ c < b ∧ P c then 1 else 0) + (if c = a ∧ P c then 1 else 0) +
        (if c = b ∧ P c then 1 else 0) := by
    intro c
    rcases lt_trichotomy c a with hca | rfl | hac
    · have h1 : ¬ a < c := not_lt_of_gt hca
      have h2 : c < b := hca.trans hab
      have h3 : ¬ b < c := not_lt_of_gt h2
      have h4 : c ≠ a := hca.ne
      have h5 : c ≠ b := h2.ne
      by_cases hP : P c <;> simp [h1, h2, h3, h4, h5, hca, hP]
    · have h3 : ¬ b < c := not_lt_of_gt hab
      have h5 : c ≠ b := hab.ne
      by_cases hP : P c <;> simp [hab, h3, h5, hP]
    · rcases lt_trichotomy c b with hcb | rfl | hbc
      · have h1 : ¬ c < a := not_lt_of_gt hac
        have h3 : ¬ b < c := not_lt_of_gt hcb
        have h4 : c ≠ a := hac.ne'
        have h5 : c ≠ b := hcb.ne
        by_cases hP : P c <;> simp [hac, hcb, h1, h3, h4, h5, hP]
      · have h1 : ¬ c < a := not_lt_of_gt hac
        have h4 : c ≠ a := hac.ne'
        by_cases hP : P c <;> simp [hac, h1, h4, hP]
      · have h1 : ¬ c < a := not_lt_of_gt hac
        have h2 : ¬ c < b := not_lt_of_gt hbc
        have h4 : c ≠ a := hac.ne'
        have h5 : c ≠ b := hbc.ne'
        by_cases hP : P c <;> simp [hac, hbc, h1, h2, h4, h5, hP]
  simp only [Finset.card_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun c _ => key c)

theorem lfD_single (P : Fin n → Prop) [DecidablePred P] (a : Fin n) :
    (univ.filter fun c => c = a ∧ P c).card = if P a then 1 else 0 := by
  rw [Finset.card_filter, Finset.sum_eq_single a]
  · simp
  · intro c _ hc
    simp [hc]
  · intro h
    exact absurd (Finset.mem_univ a) h

theorem lf_rhoN_sub_nat (ε : Fin n → Bool) {a b : Fin n} (hab : a < b) (he : ε a = ε b) :
    ∃ m : ℕ, rhoN ε a - rhoN ε b = m := by
  refine ⟨(univ.filter fun c => a < c ∧ c < b ∧ ε c ≠ ε a).card, ?_⟩
  have hc := lfD_cnt (fun c => ε c ≠ ε a) hab
  rw [lfD_single, lfD_single, if_neg (fun h => h rfl), if_neg (fun h => h he.symm)] at hc
  have hr := congrArg (Nat.cast : ℕ → ℝ) hc
  push_cast at hr
  simp only [rhoN, ← he]
  linarith

theorem lf_rhoHol_eq (ε : Fin n → Bool) {a b : Fin n} (he : ε a = ε b) : rhoHol ε a = rhoHol ε b := by
  simp only [rhoHol, he]

theorem lf_dom {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : StrictAnti lam) {M : Type*} [AddCommGroup M]
    [Module ℂ M] {F : Fin n → Fin n → Module.End ℂ M} (hF : Formalism.REAL.KRel ε F) {V : Submodule ℂ M}
    (hV : IsKIrrHW ε F (lowK ε lam) V) :
    ∀ a b, a < b → ε a = ε b →
      (lowK ε lam + (rhoHol ε - rhoN ε)) b ≤ (lowK ε lam + (rhoHol ε - rhoN ε)) a := by
  suffices H : ∀ d, ∀ a b : Fin n, b.val - a.val = d → a < b → ε a = ε b →
      (lowK ε lam + (rhoHol ε - rhoN ε)) b ≤ (lowK ε lam + (rhoHol ε - rhoN ε)) a by
    intro a b hab he
    exact H _ a b rfl hab he
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro a b hd hab he
    by_cases hmid : ∃ c, a < c ∧ c < b ∧ ε c = ε a
    · obtain ⟨c, hac, hcb, hce⟩ := hmid
      have hac' := Fin.lt_def.mp hac
      have hcb' := Fin.lt_def.mp hcb
      have h1 := ih (c.val - a.val) (by omega) a c rfl hac hce.symm
      have h2 := ih (b.val - c.val) (by omega) c b rfl hcb (hce.trans he)
      exact h2.trans h1
    · simp only [not_exists, not_and] at hmid
      have hC := HW.rhoC_consec ε hab he hmid
      obtain ⟨m, hm⟩ := HW.kIrrHW_int ε hF hV a b hab he
      obtain ⟨k, hk⟩ := lf_rhoN_sub_nat ε hab he
      have hH := lf_rhoHol_eq ε he
      have hl := hlam hab
      have hlk : lowK ε lam a - lowK ε lam b =
          lam a - lam b + (rhoN ε a - rhoN ε b) - (rhoC ε a - rhoC ε b) := by
        simp only [lowK, Pi.add_apply, Pi.sub_apply]
        ring
      have hkm : (k : ℝ) < m + 1 := by linarith
      have hkm' : k < m + 1 := by exact_mod_cast hkm
      have hkm'' : (k : ℝ) ≤ m := by exact_mod_cast Nat.lt_succ_iff.mp hkm'
      simp only [Pi.add_apply, Pi.sub_apply]
      linarith

end ReciprocityTheory.ChartRestriction.DS
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.LowFockE
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {N : Type*} [AddCommGroup N] [Module ℂ N]

theorem lf_sgE_tensor (ε : Fin n → Bool) (a b : Fin n) :
    sgE ε (cpT (N := N) (n := n)) cmT a b = TensorProduct.map LinearMap.id (sgE ε cpFock cmFock a b) := by
  have hcp : ∀ i c : Fin n, cpT (N := N) i c = LinearMap.lTensor N (cpFock i c) := fun _ _ => rfl
  have hcm : ∀ i c : Fin n, cmT (N := N) i c = LinearMap.lTensor N (cmFock i c) := fun _ _ => rfl
  have hsum : ∀ (s : Finset (Fin n)) (F : Fin n → Module.End ℂ (Fock n)),
      LinearMap.lTensor N (∑ x ∈ s, F x) = ∑ x ∈ s, LinearMap.lTensor N (F x) :=
    fun s F => map_sum (LinearMap.lTensorHom N) F s
  rw [show TensorProduct.map LinearMap.id (sgE ε cpFock cmFock a b) =
    LinearMap.lTensor N (sgE ε cpFock cmFock a b) from rfl]
  unfold sgE
  split_ifs
  · rw [hsum]
    simp only [hcp, hcm, LinearMap.lTensor_mul]
  · rw [LinearMap.lTensor_neg, hsum]
    simp only [hcp, hcm, LinearMap.lTensor_mul]
  · rw [LinearMap.lTensor_zero]

theorem lf_diagE_tensor (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ N) (a b : Fin n) :
    diagE ε (eT E) cpT cmT a b =
      TensorProduct.map (E a b) LinearMap.id + TensorProduct.map LinearMap.id (sgE ε cpFock cmFock a b) := by
  unfold diagE
  rw [lf_sgE_tensor]
  rfl

def lfLift (ε : Fin n → Bool) (x : LfIdx ε → N) : TensorProduct ℂ N (Fock n) :=
  ∑ S, x S ⊗ₜ[ℂ] fockBasis n S.1

theorem lfLift_mem_tensFock (ε : Fin n → Bool) {V : Submodule ℂ N} {x : LfIdx ε → N} (hx : ∀ S, x S ∈ V) :
    lfLift ε x ∈ tensFock (n := n) V := by
  unfold lfLift tensFock
  refine Submodule.sum_mem _ fun S _ => ⟨⟨x S, hx S⟩ ⊗ₜ fockBasis n S.1, ?_⟩
  simp [TensorProduct.map_tmul]

theorem lfLift_mem_physSub (ε : Fin n → Bool) (x : LfIdx ε → N) : lfLift ε x ∈ physicalSubspace (N := N) ε := by
  simp only [physicalSubspace, Submodule.mem_iInf, LinearMap.mem_ker]
  intro i a hia
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [lfLift, map_sum, cmT, TensorProduct.map_tmul, LinearMap.id_apply]
  refine Finset.sum_eq_zero fun S _ => ?_
  have hS : finProdFinEquiv (i, a) ∉ S.1 := by
    intro h
    have := S.2 h
    simp only [lfPhysModes, Finset.mem_filter, Equiv.symm_apply_apply] at this
    exact hia this.2
  rw [lf_cm_basis_of_not_mem (x := (i, a)) hS, TensorProduct.tmul_zero]

theorem lfLift_tcoef (ε : Fin n → Bool) (x : LfIdx ε → N) (S : LfIdx ε) :
    tcoef ((fockBasis n).coord S.1) (lfLift ε x) = x S := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [lfLift, map_sum, tcoef, LinearMap.coe_comp, Function.comp_apply, TensorProduct.map_tmul,
    LinearMap.id_apply, LinearEquiv.coe_coe, TensorProduct.rid_tmul, Module.Basis.coord_apply, Module.Basis.repr_self]
  rw [Finset.sum_eq_single S (fun T _ hT => by
    rw [Finsupp.single_apply, if_neg (fun h => hT (Subtype.ext h)), zero_smul]) (by simp)]
  simp

theorem lfLift_ne_zero (ε : Fin n → Bool) {x : LfIdx ε → N} (hx : x ≠ 0) : lfLift ε x ≠ 0 := by
  intro h0
  apply hx
  funext S
  have h1 := lfLift_tcoef ε x S
  rw [h0, map_zero] at h1
  exact h1.symm

theorem lfLift_diagE (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ N) (a b : Fin n)
    (x : LfIdx ε → N) :
    diagE ε (eT E) cpT cmT a b (lfLift ε x) =
      lfLift ε (fun T => E a b (x T) + ∑ S, lfMat ε a b T S • x S) := by
  rw [lf_diagE_tensor, LinearMap.add_apply]
  unfold lfLift
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum]
  simp only [TensorProduct.map_tmul, LinearMap.id_apply]
  simp only [lfMat_basis, TensorProduct.tmul_sum, TensorProduct.tmul_smul]
  simp only [TensorProduct.add_tmul, Finset.sum_add_distrib, TensorProduct.sum_tmul,
    ← TensorProduct.smul_tmul']
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ) (f := fun S T => lfMat ε a b T S • (x S ⊗ₜ[ℂ] fockBasis n T.1))]

theorem lfLift_smul (ε : Fin n → Bool) (c : ℂ) (x : LfIdx ε → N) :
    lfLift ε (fun T => c • x T) = c • lfLift ε x := by
  simp only [lfLift, Finset.smul_sum, TensorProduct.smul_tmul']

theorem lfLift_isKHWVec (ε : Fin n → Bool) {E : Fin n → Fin n → Module.End ℂ N} {μ : Fin n → ℝ}
    {x : LfIdx ε → N}
    (hw : ∀ a S, E a a (x S) + ∑ T, lfMat ε a a S T • x T = ((μ a : ℝ) : ℂ) • x S)
    (hh : ∀ a b, a < b → ε a = ε b → ∀ S, E a b (x S) + ∑ T, lfMat ε a b S T • x T = 0) :
    IsKHWVec ε (diagE ε (eT E) cpT cmT) μ (lfLift ε x) := by
  refine ⟨fun a => ?_, fun a b hab hε => ?_⟩
  · rw [lfLift_diagE]
    have h1 : (fun T => E a a (x T) + ∑ S, lfMat ε a a T S • x S) = fun T => ((μ a : ℝ) : ℂ) • x T :=
      funext fun T => hw a T
    rw [h1, lfLift_smul]
  · rw [lfLift_diagE]
    have h1 : (fun T => E a b (x T) + ∑ S, lfMat ε a b T S • x S) = fun _ => 0 :=
      funext fun T => hh a b hab hε T
    rw [h1]
    simp [lfLift]

end ReciprocityTheory.ChartRestriction.DS
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.LowFockC
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def lowerWedgeAlt (ε : Fin n → Bool) : LfIdx ε :=
  ⟨(lfPhysModes ε).filter fun m => (finProdFinEquiv.symm m).2 < (finProdFinEquiv.symm m).1, filter_subset _ _⟩

theorem mem_lowerWedge_iff (ε : Fin n → Bool) (x : Fin n × Fin n) :
    finProdFinEquiv x ∈ (lowerWedgeAlt ε).1 ↔ ε x.1 = true ∧ ε x.2 = false ∧ x.2 < x.1 := by
  simp only [lowerWedgeAlt, lfPhysModes, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply,
    and_assoc]

theorem lf_rhoHol_sub_rhoN (ε : Fin n → Bool) (c : Fin n) :
    (rhoHol ε - rhoN ε) c = if ε c = true then ((univ.filter fun a => ε a = false ∧ a < c).card : ℝ)
      else -((univ.filter fun i => ε i = true ∧ c < i).card : ℝ) := by
  rw [cfa_rho_coord]
  cases hc : ε c <;> simp [hc, Finset.sum_boole]

theorem lowerWedge_weight (ε : Fin n → Bool) (c : Fin n) :
    sgE ε cpFock cmFock c c (fockBasis n (lowerWedgeAlt ε).1) =
      (((rhoHol ε - rhoN ε) c : ℝ) : ℂ) • fockBasis n (lowerWedgeAlt ε).1 := by
  have hw : fockWt ε (lowerWedgeAlt ε).1 c = (rhoHol ε - rhoN ε) c := by
    rw [cfa_rho_coord, fockWt, Finset.sum_apply]
    have hS : (lowerWedgeAlt ε).1 = univ.filter fun k => ε (finProdFinEquiv.symm k).1 = true ∧
        ε (finProdFinEquiv.symm k).2 = false ∧ (finProdFinEquiv.symm k).2 < (finProdFinEquiv.symm k).1 := by
      ext k
      simp only [lowerWedgeAlt, lfPhysModes, Finset.mem_filter, Finset.mem_univ, true_and, and_assoc]
    rw [hS, Finset.sum_filter, ← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
    simp only [Equiv.symm_apply_apply]
    have key : ∀ i b : Fin n, (if ε i = true ∧ ε b = false ∧ b < i then modeWt ε (i, b) c else 0) =
        (if c = i then (if ε i = true ∧ ε b = false ∧ b < i then (1 : ℝ) else 0) else 0) -
        (if c = b then (if ε i = true ∧ ε b = false ∧ b < i then (1 : ℝ) else 0) else 0) := by
      intro i b
      by_cases h : ε i = true ∧ ε b = false ∧ b < i
      · simp only [if_pos h]
        simp only [modeWt, if_pos (And.intro h.1 h.2.1), root, Pi.sub_apply, Pi.single_apply]
      · simp only [if_neg h]
        simp
    rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ => key i b]
    simp only [Finset.sum_sub_distrib]
    congr 1
    · rw [Finset.sum_comm]
      simp
    · simp
  rw [fockBasis_wt, hw]

theorem lowerWedge_killed_by_lowering (ε : Fin n → Bool) {a b : Fin n} (hba : b < a) (he : ε a = ε b) :
    sgE ε cpFock cmFock a b (fockBasis n (lowerWedgeAlt ε).1) = 0 := by
  have hab : a ≠ b := (ne_of_lt hba).symm
  unfold sgE
  split_ifs with h1 h2
  · rw [LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun x hx => ?_
    have hxm : ε x = false := (Finset.mem_filter.1 hx).2
    rw [Module.End.mul_apply]
    by_cases hbx : finProdFinEquiv (b, x) ∈ (lowerWedgeAlt ε).1
    · obtain ⟨σ, -, hσ, -⟩ := lf_cm_basis_of_mem (x := (b, x)) hbx
      dsimp only at hσ
      rw [hσ, map_smul]
      have hxb : x < b := ((mem_lowerWedge_iff ε (b, x)).1 hbx).2.2
      have hmem : finProdFinEquiv (a, x) ∈ (lowerWedgeAlt ε).1.erase (finProdFinEquiv (b, x)) := by
        rw [Finset.mem_erase]
        exact ⟨fun h => hab (congrArg Prod.fst (finProdFinEquiv.injective h)),
          (mem_lowerWedge_iff ε (a, x)).2 ⟨h1.1, hxm, hxb.trans hba⟩⟩
      have h0 := lf_cp_basis_of_mem (x := (a, x)) hmem
      dsimp only at h0
      rw [h0, smul_zero]
    · have h0 := lf_cm_basis_of_not_mem (x := (b, x)) hbx
      dsimp only at h0
      rw [h0, map_zero]
  · rw [LinearMap.neg_apply, LinearMap.sum_apply, neg_eq_zero]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hip : ε i = true := (Finset.mem_filter.1 hi).2
    rw [Module.End.mul_apply]
    by_cases hia : finProdFinEquiv (i, a) ∈ (lowerWedgeAlt ε).1
    · obtain ⟨σ, -, hσ, -⟩ := lf_cm_basis_of_mem (x := (i, a)) hia
      dsimp only at hσ
      rw [hσ, map_smul]
      have hai : a < i := ((mem_lowerWedge_iff ε (i, a)).1 hia).2.2
      have hmem : finProdFinEquiv (i, b) ∈ (lowerWedgeAlt ε).1.erase (finProdFinEquiv (i, a)) := by
        rw [Finset.mem_erase]
        exact ⟨fun h => hab (congrArg Prod.snd (finProdFinEquiv.injective h)).symm,
          (mem_lowerWedge_iff ε (i, b)).2 ⟨hip, h2.2, hba.trans hai⟩⟩
      have h0 := lf_cp_basis_of_mem (x := (i, b)) hmem
      dsimp only at h0
      rw [h0, smul_zero]
    · have h0 := lf_cm_basis_of_not_mem (x := (i, a)) hia
      dsimp only at h0
      rw [h0, map_zero]
  · exfalso
    cases hb : ε b <;> simp_all

end ReciprocityTheory.ChartRestriction.DS
end
end

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {N : Type*} [AddCommGroup N] [Module ℂ N]

theorem lowFock_exists (ε : Fin n → Bool) {E : Fin n → Fin n → Module.End ℂ N} (hE : IsGlRep E)
    {lam : Fin n → ℝ} (hlam : StrictAnti lam) {V : Submodule ℂ N} (hV : IsKIrrHW ε E (lowK ε lam) V) :
    ∃ x ∈ tensFock (n := n) V, x ∈ physicalSubspace ε ∧ x ≠ 0 ∧
      IsKHWVec ε (diagE ε (eT E) cpT cmT) (lam - rhoC ε + rhoHol ε) x := by
  have hK : Formalism.REAL.KRel ε E := fun a b c d _ _ => hE a b c d
  set S0 := lowerWedgeAlt ε
  have hw : ∀ a, (lfMat ε a a).mulVec (Pi.single S0 (1 : ℂ)) =
      (((rhoHol ε - rhoN ε) a : ℝ) : ℂ) • Pi.single S0 1 :=
    fun a => lfMat_mulVec_single ε a a S0 _ (lowerWedge_weight ε a)
  have hl : ∀ a b, b < a → ε a = ε b → (lfMat ε a b).mulVec (Pi.single S0 (1 : ℂ)) = 0 := by
    intro a b hba he
    have h0 : sgE ε cpFock cmFock a b (fockBasis n S0.1) = (0 : ℂ) • fockBasis n S0.1 := by
      rw [zero_smul]; exact lowerWedge_killed_by_lowering ε hba he
    simpa using lfMat_mulVec_single ε a b S0 0 h0
  have hne : (Pi.single S0 (1 : ℂ) : LfIdx ε → ℂ) ≠ 0 := by
    intro h
    have := congrFun h S0
    simp at this
  obtain ⟨x, hxV, hx0, hxw, hxh⟩ :=
    HW.parthasarathy_tensor_matrix ε hK hV (lfMat_kRel ε) (fun a b h => lfMat_conjTranspose ε h) hne hw hl
      (lf_dom hlam hK hV)
  have hwt : lowK ε lam + (rhoHol ε - rhoN ε) = lam - rhoC ε + rhoHol ε := by
    funext a
    simp only [lowK, Pi.add_apply, Pi.sub_apply]
    ring
  refine ⟨lfLift ε x, lfLift_mem_tensFock ε hxV, lfLift_mem_physSub ε x, lfLift_ne_zero ε hx0, ?_⟩
  rw [← hwt]
  exact lfLift_isKHWVec ε hxw hxh

end ReciprocityTheory.ChartRestriction.DS
