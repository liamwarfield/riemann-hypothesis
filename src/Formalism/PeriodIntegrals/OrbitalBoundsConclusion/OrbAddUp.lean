module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitJetDegreeBound.JetTdegEqDegree

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitJetDegreeBound.ConstantCoeffZeroOfBoundGeneral
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitJetDegreeBound.UnivEqBiUnion
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitJetDegreeBound.ProdMonomialOne
noncomputable section

open Classical

namespace PI.OrbJet.AU

open Formalism.BasicNotions Formalism.MainNotions.G MvPowerSeries Finsupp PI.OrbJet PI.OrbJet.OrbW PI.OrbShared

variable (D : D7) (p : ℕ) [Fact p.Prime]

theorem subst_rename {β : Type} [Finite β] (ep : ℂ_[p]) (r : Pl D) (F : MvPowerSeries (ZMod (nP D p) × β) ℂ_[p]) :
    subst (fun v : Pl D × β => C ep * logPl D p v) (rename (pE D p r β) F) =
      rename (pE D p r β) (subst (fun w : ZMod (nP D p) × β => C ep * jetLogG p (nP D p) w) F) := by
  haveI : Finite (Pl D × β) := inferInstance
  have hcc1 : ∀ v : Pl D × β, constantCoeff (C ep * logPl D p v) = 0 := by
    intro v
    rw [map_mul]
    have h0 : constantCoeff (logPl D p v) = 0 := by
      rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
      show logPl D p v 0 = 0
      simp [logPl, JetTdeg, eq_comm (a := (0 : Pl D × β →₀ ℕ))]
    rw [h0, mul_zero]
  have hb : HasSubst (fun v : Pl D × β => C ep * logPl D p v) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero hcc1
  have hcc2 : ∀ w : ZMod (nP D p) × β, constantCoeff (C ep * jetLogG p (nP D p) w) = 0 := by
    intro w
    rw [map_mul]
    have h0 : constantCoeff (jetLogG p (nP D p) w) = 0 := by
      rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
      show jetLogG p (nP D p) w 0 = 0
      simp [jetLogG, JetTdeg, eq_comm (a := (0 : ZMod (nP D p) × β →₀ ℕ))]
    rw [h0, mul_zero]
  have ha : HasSubst (fun w : ZMod (nP D p) × β => C ep * jetLogG p (nP D p) w) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero hcc2
  rw [MvPowerSeries.rename_eq_subst, MvPowerSeries.rename_eq_subst,
    MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.HasSubst.X_comp _) hb,
    MvPowerSeries.subst_comp_subst_apply ha (MvPowerSeries.HasSubst.X_comp _)]
  congr 1
  funext w
  rw [Function.comp_apply, MvPowerSeries.subst_X hb, ← MvPowerSeries.rename_eq_subst, map_mul,
    MvPowerSeries.rename_C, rename_jet]

def bsum {N0 N1 : ℕ} (be : MvPowerSeries (ZMod (nP D p)) ℂ_[p]) :
    MvPowerSeries (ZMod (nP D p) × Fin N0 × Fin N1) ℂ_[p] :=
  ∑ a : Fin N0, ∑ b : Fin N1,
    subst (fun s : ZMod (nP D p) => (X (s, a, b) : MvPowerSeries (ZMod (nP D p) × Fin N0 × Fin N1) ℂ_[p])) be

theorem hasSubst_Xs {N0 N1 : ℕ} (a : Fin N0) (b : Fin N1) :
    HasSubst (fun s : ZMod (nP D p) => (X (s, a, b) : MvPowerSeries (ZMod (nP D p) × Fin N0 × Fin N1) ℂ_[p])) := by
  first
  | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => MvPowerSeries.constantCoeff_X _)
  | exact MvPowerSeries.HasSubst.X
  | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (fun s => by rw [MvPowerSeries.constantCoeff_X]; exact IsNilpotent.zero)

theorem cc_bsum {N0 N1 : ℕ} (sg : ℂ_[p]) (be : MvPowerSeries (ZMod (nP D p)) ℂ_[p]) (hbe : constantCoeff be = 0) :
    constantCoeff (sg • bsum D p (N0 := N0) (N1 := N1) be) = 0 := by
  unfold bsum
  set_option synthInstance.maxHeartbeats 100000 in
    rw [MvPowerSeries.smul_eq_C_mul, map_mul, map_sum]
  rw [Finset.sum_eq_zero (fun a _ => ?_), mul_zero]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_eq_zero fun b _ => ?_
  exact MvPowerSeries.constantCoeff_subst_eq_zero (hasSubst_Xs D p a b)
    (fun s => MvPowerSeries.constantCoeff_X _) hbe

theorem beAll_eq {N0 N1 : ℕ} (R : Finset (Pl D)) (sg : Pl D → ℂ_[p])
    (be : Pl D → MvPowerSeries (ZMod (nP D p)) ℂ_[p]) :
    beAll D p (N0 := N0) (N1 := N1) R sg be =
      ∑ r ∈ R, rename (pE D p r (Fin N0 × Fin N1)) (sg r • bsum D p (be r)) := by
  unfold beAll bsum
  refine Finset.sum_congr rfl fun r _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [MvPowerSeries.rename_eq_subst,
    MvPowerSeries.subst_comp_subst_apply (hasSubst_Xs D p a b) (MvPowerSeries.HasSubst.X_comp _)]
  congr 1
  funext s
  rw [MvPowerSeries.subst_X (MvPowerSeries.HasSubst.X_comp _)]
  rfl

def Eorb {N0 N1 : ℕ} (sg : ℂ_[p]) (be : MvPowerSeries (ZMod (nP D p)) ℂ_[p]) :
    MvPowerSeries (ZMod (nP D p) × Fin N0 × Fin N1) ℂ_[p] :=
  subst (jetLogG p (nP D p) (β := Fin N0 × Fin N1)) (OJ.expS ℂ_[p] (sg • bsum D p be))

theorem E_eq {N0 N1 : ℕ} (R : Finset (Pl D)) (sg : Pl D → ℂ_[p])
    (be : Pl D → MvPowerSeries (ZMod (nP D p)) ℂ_[p]) (hcc : ∀ r ∈ R, constantCoeff (be r) = 0) :
    subst (logPl D p (β := Fin N0 × Fin N1)) (OJ.expS ℂ_[p] (beAll D p R sg be)) =
      ∏ r ∈ R, rename (pE D p r (Fin N0 × Fin N1)) (Eorb D p (N0 := N0) (N1 := N1) (sg r) (be r)) := by
  haveI : Finite (Pl D × Fin N0 × Fin N1) := inferInstance
  have hL : HasSubst (logPl D p (β := Fin N0 × Fin N1)) := by
    refine MvPowerSeries.hasSubst_of_constantCoeff_zero fun v => ?_
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    show logPl D p v 0 = 0
    simp [logPl, JetTdeg, eq_comm (a := (0 : Pl D × Fin N0 × Fin N1 →₀ ℕ))]
  have hG : ∀ r ∈ R, constantCoeff (sg r • bsum D p (N0 := N0) (N1 := N1) (be r)) = 0 :=
    fun r hr => cc_bsum D p (sg r) (be r) (hcc r hr)
  have hRG : ∀ r ∈ R, constantCoeff (rename (pE D p r (Fin N0 × Fin N1)) (sg r • bsum D p (N0 := N0) (N1 := N1) (be r))) = 0 := by
    intro r hr
    rw [MvPowerSeries.rename_eq_subst]
    exact MvPowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.HasSubst.X_comp _)
      (fun i => MvPowerSeries.constantCoeff_X _) (hG r hr)
  rw [beAll_eq]
  change subst (logPl D p (β := Fin N0 × Fin N1)) (PI.OrbShared.ExpSum.eS _) = _
  rw [PI.OrbShared.ExpSum.eS_sum _ _ hRG, ← MvPowerSeries.coe_substAlgHom hL, map_prod]
  refine Finset.prod_congr rfl fun r hr => ?_
  rw [MvPowerSeries.coe_substAlgHom]
  have h1 : PI.OrbShared.ExpSum.eS (rename (pE D p r (Fin N0 × Fin N1)) (sg r • bsum D p (N0 := N0) (N1 := N1) (be r))) =
      rename (pE D p r (Fin N0 × Fin N1)) (OJ.expS ℂ_[p] (sg r • bsum D p (N0 := N0) (N1 := N1) (be r))) := by
    rw [MvPowerSeries.rename_eq_subst, MvPowerSeries.rename_eq_subst]
    exact (PI.OrbShared.ExpSum.subst_eS (MvPowerSeries.HasSubst.X_comp _) _ (hG r hr)).symm
  rw [h1]
  have h2 := subst_rename D p 1 r (OJ.expS ℂ_[p] (sg r • bsum D p (N0 := N0) (N1 := N1) (be r)))
  simp only [map_one, one_mul] at h2
  rw [h2]
  rfl

theorem prod_monomial_one {σ ι : Type*} (s : Finset ι) (g : ι → σ →₀ ℕ) :
    (∏ i ∈ s, (monomial (g i) (1 : ℂ_[p]) : MvPowerSeries σ ℂ_[p])) = monomial (∑ i ∈ s, g i) 1 := by
  classical
  refine Finset.induction_on s (by simp [MvPowerSeries.monomial_zero_one]) ?_
  intro i s hi ih
  rw [Finset.prod_insert hi, ih, MvPowerSeries.monomial_mul_monomial, one_mul, Finset.sum_insert hi]

def resM {γ : Type} (r : Pl D) (m : Pl D × γ →₀ ℕ) : ZMod (nP D p) × γ →₀ ℕ :=
  comapDomain (pE D p r γ) m (pE D p r γ).injective.injOn

theorem mem_orbit_unique {R : Finset (Pl D)} (hR : IsReps D p R) {r r' : Pl D} (hr : r ∈ R) (hr' : r' ∈ R)
    (s s' : ZMod (nP D p)) (h : orbMap D p r s = orbMap D p r' s') : r = r' := by
  obtain ⟨r0, -, huniq⟩ := hR (orbMap D p r s)
  have h1 := huniq r ⟨hr, s.val, rfl⟩
  have h2 := huniq r' ⟨hr', s'.val, h.symm⟩
  rw [h1, h2]

theorem sum_resM {γ : Type} {R : Finset (Pl D)} (hR : IsReps D p R) (m : Pl D × γ →₀ ℕ) :
    ∑ r ∈ R, mapDomain (pE D p r γ) (resM D p r m) = m := by
  ext ⟨z, c⟩
  rw [Finsupp.finsetSum_apply]
  obtain ⟨r0, ⟨hr0, e0, he0⟩, huniq⟩ := hR z
  have hx0 : ((z, c) : Pl D × γ) = pE D p r0 γ ((e0 : ZMod (nP D p)), c) := by
    show (z, c) = (orbMap D p r0 (e0 : ZMod (nP D p)), c)
    rw [← posPl_eq_orbMap, he0]
  rw [Finset.sum_eq_single r0]
  · rw [hx0, Finsupp.mapDomain_apply_of_injective (pE D p r0 γ).injective]
    rfl
  · intro r hr hne
    apply Finsupp.mapDomain_notin_range
    rintro ⟨⟨s, c'⟩, hsc⟩
    apply hne
    apply huniq r
    refine ⟨hr, s.val, ?_⟩
    have hsc' : ((orbMap D p r s, c') : Pl D × γ) = (z, c) := hsc
    rw [← (Prod.mk.inj hsc').1]
    rfl
  · intro h
    exact absurd hr0 h

theorem mono_eq {γ : Type} {R : Finset (Pl D)} (hR : IsReps D p R) (m : Pl D × γ →₀ ℕ) :
    (monomial m (1 : ℂ_[p]) : MvPowerSeries (Pl D × γ) ℂ_[p]) =
      ∏ r ∈ R, rename (pE D p r γ) (monomial (resM D p r m) 1) := by
  conv_lhs => rw [← sum_resM D p hR m]
  rw [← prod_monomial_one]
  refine Finset.prod_congr rfl fun r _ => ?_
  rw [MvPowerSeries.rename_monomial]

end PI.OrbJet.AU

end
end

noncomputable section

open Classical

namespace PI.OrbJet.AU

open Formalism.BasicNotions Formalism.MainNotions.G PI.OrbJet PI.OrbJet.OrbW PI.OrbShared PI.OrbJet.OJ

variable (D : D7) (p : ℕ) [Fact p.Prime]

theorem univ_eq_biUnion {R : Finset (Pl D)} (hR : IsReps D p R) :
    (Finset.univ : Finset (Pl D)) = R.biUnion (fun r => Finset.univ.image (orbMap D p r)) := by
  ext z
  simp only [Finset.mem_univ, Finset.mem_biUnion, Finset.mem_image, true_iff]
  obtain ⟨r, ⟨hr, e, he⟩, -⟩ := hR z
  refine ⟨r, hr, ?_⟩
  unfold orbMap
  refine ⟨(e : ZMod (nP D p)), trivial, ?_⟩
  rw [ZMod.val_natCast, ← he]
  have key : ∀ (x : HH D) (n e : ℕ), n • x = 0 → (e % n) • x = e • x := by
    intro x n e h
    conv_rhs => rw [← Nat.mod_add_div e n]
    rw [add_nsmul, mul_comm, ← smul_smul, h, smul_zero, add_zero]
  have hpe : partner D p r.2 (e % nP D p) = partner D p r.2 e := by
    unfold partner nP
    by_cases hs : IsSg D p
    · have h2 : (2 * addOrderOf (2 • hP D p)) • hP D p = 0 := by
        rw [mul_comm, ← smul_smul, addOrderOf_nsmul_eq_zero]
      simp only [if_pos hs]
      rw [key _ _ _ h2]
      simp only [Nat.odd_iff, Nat.mod_mod_of_dvd _ (dvd_mul_right 2 _)]
    · simp only [if_neg hs]
      rw [key _ _ _ (addOrderOf_nsmul_eq_zero _)]
      simp [hs]
  unfold posPl
  rw [hpe]

private theorem orbMap_injective (r : Pl D) : Function.Injective (orbMap D p r) := by
  intro s t hst
  unfold orbMap posPl partner at hst
  simp only [Prod.mk.injEq, add_right_inj] at hst
  obtain ⟨h1, h2⟩ := hst
  have hn : nP D p = if IsSg D p then 2 * addOrderOf (2 • hP D p) else addOrderOf (hP D p) := by
    unfold nP
    rfl
  have hs_lt := lt_of_lt_of_eq (ZMod.val_lt s) hn
  have ht_lt := lt_of_lt_of_eq (ZMod.val_lt t) hn
  apply ZMod.val_injective
  by_cases hsg : IsSg D p
  · rw [if_pos hsg] at hs_lt ht_lt
    have hpar : s.val % 2 = t.val % 2 := by
      have h1' : (s.val % 2 = 1 ↔ t.val % 2 = 1) := by
        have hd : decide (IsSg D p) = true := decide_eq_true hsg
        simpa [hd, Nat.odd_iff] using h1
      rcases Nat.mod_two_eq_zero_or_one s.val with h | h <;>
        rcases Nat.mod_two_eq_zero_or_one t.val with h' | h'
      · rw [h, h']
      · exact absurd (h1'.mpr h') (by omega)
      · exact absurd (h1'.mp h) (by omega)
      · rw [h, h']
    have h3 : (s.val % 2) • hP D p + (2 * (s.val / 2)) • hP D p
        = (t.val % 2) • hP D p + (2 * (t.val / 2)) • hP D p := by
      rw [← add_nsmul, ← add_nsmul, Nat.mod_add_div, Nat.mod_add_div]
      exact h2
    rw [hpar] at h3
    have h4 := add_left_cancel h3
    have hk : (s.val / 2) • (2 • hP D p) = (t.val / 2) • (2 • hP D p) := by
      rw [smul_smul, smul_smul, mul_comm (s.val / 2), mul_comm (t.val / 2)]
      exact h4
    have h5 := nsmul_inj_mod.mp hk
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h5
    omega
  · rw [if_neg hsg] at hs_lt ht_lt
    have h5 := nsmul_inj_mod.mp h2
    rwa [Nat.mod_eq_of_lt hs_lt, Nat.mod_eq_of_lt ht_lt] at h5

theorem prod_orbits {M : Type*} [CommMonoid M] {R : Finset (Pl D)} (hR : IsReps D p R) (g : Pl D → M) :
    ∏ z, g z = ∏ r ∈ R, ∏ s : ZMod (nP D p), g (orbMap D p r s) := by
  rw [univ_eq_biUnion D p hR, Finset.prod_biUnion]
  · refine Finset.prod_congr rfl (fun r _ => ?_)
    rw [Finset.prod_image (fun s _ t _ h => orbMap_injective D p r h)]
  · intro r hr r' hr' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro z hz hz'
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hz hz'
    obtain ⟨s, rfl⟩ := hz
    obtain ⟨s', hs'⟩ := hz'
    apply hne
    obtain ⟨r0, -, huniq⟩ := hR (orbMap D p r s)
    have a := huniq r ⟨hr, s.val, rfl⟩
    have b := huniq r' ⟨hr', s'.val, hs'⟩
    rw [a, b]

theorem Gxz_eq {R : Finset (Pl D)} (hR : IsReps D p R) {N0 N1 : ℕ} (nu : Pl D → YoungDiagram)
    (I : ColChoice N1 nu) :
    Gxz N0 N1 nu I = ∏ r ∈ R, MvPolynomial.rename (xzMap (N0 := N0) (N1 := N1) (orbE D p r))
      (Gxz N0 N1 (fun s => nu (orbMap D p r s)) (fun s => I (orbMap D p r s))) := by
  unfold Gxz
  rw [prod_orbits D p hR]
  refine Finset.prod_congr rfl (fun r _ => ?_)
  rw [map_prod]
  refine Finset.prod_congr rfl (fun s _ => ?_)
  rw [map_prod]
  refine Finset.prod_congr rfl (fun c _ => ?_)
  unfold minorXZ
  rw [AlgHom.map_det]
  congr 1
  refine Matrix.ext fun i k => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    simp [AlgHom.mapMatrix_apply, Matrix.map_apply, map_sum, MvPolynomial.rename_X, xzMap, orbE, pEmb,
    Function.Embedding.coeFn_mk]
  all_goals rfl

theorem Gxz_supported {N0 N1 : ℕ} (r : Pl D) (nu : ZMod (nP D p) → YoungDiagram) (I : ColChoice N1 nu) :
    MvPolynomial.rename (xzMap (N0 := N0) (N1 := N1) (orbE D p r)) (Gxz N0 N1 nu I) ∈
      MvPolynomial.supported ℤ (xzLetter ⁻¹' Set.range (orbMap D p r)) := by
  rw [MvPolynomial.mem_supported]
  intro v hv
  have hv' := MvPolynomial.vars_rename _ _ (Finset.mem_coe.mp hv)
  obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hv'
  rcases w with ⟨s, _⟩ | ⟨s, _⟩ <;>
    exact Set.mem_preimage.mpr (Set.mem_range.mpr ⟨s, by simp [xzLetter, xzMap, orbE, pEmb, orbMap]⟩)

theorem kval_prod {R : Finset (Pl D)} (hR : IsReps D p R) {N0 N1 : ℕ} (nu : Pl D → YoungDiagram)
    (F : Pl D → MvPowerSeries (ZMod (nP D p) × Fin N0 × Fin N1) ℂ_[p]) (β : Pl D → ℝ)
    (hF : ∀ r ∈ R, KvalGe N0 N1 p (fun s => nu (orbMap D p r s)) (F r) (β r)) :
    KvalGe N0 N1 p nu (∏ r ∈ R, MvPowerSeries.rename (pE D p r (Fin N0 × Fin N1)) (F r)) (∑ r ∈ R, β r) := by
  intro I m
  have hdisj : (R : Set (Pl D)).PairwiseDisjoint (fun r => Set.range (orbMap D p r)) := by
    intro r hr r' hr' hne
    rw [Function.onFun, Set.disjoint_left]
    rintro z ⟨s, rfl⟩ ⟨s', hs'⟩
    exact hne (mem_orbit_unique D p hR hr hr' s s' hs'.symm)
  have key := applyAt0_prod p R (fun r => Set.range (orbMap D p r)) hdisj
    (fun r => MvPowerSeries.rename (pE D p r (Fin N0 × Fin N1)) (F r))
    (fun r => MvPolynomial.rename (xzMap (N0 := N0) (N1 := N1) (orbE D p r))
      (Gxz N0 N1 (fun s => nu (orbMap D p r s)) (fun s => I (orbMap D p r s))))
    (fun r _ => serIn_rename (orbE D p r) (F r)) (fun r _ => Gxz_supported D p r _ _)
  beta_reduce at key
  rw [Gxz_eq D p hR, key]
  have hpos : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hsum : (p : ℝ) ^ (-∑ r ∈ R, β r) = ∏ r ∈ R, (p : ℝ) ^ (-β r) := by
    rw [← Finset.sum_neg_distrib, Real.rpow_sum_of_pos hpos]
  rw [hsum]
  refine norm_coeff_prod_le R (fun r _ => Real.rpow_nonneg hpos.le _) (fun r hr m' => ?_) m
  rw [applyAt0_rename]
  exact norm_coeff_rename_le _ _ (Real.rpow_nonneg hpos.le _) (fun m'' => hF r hr _ m'') m'

end PI.OrbJet.AU

end
end

noncomputable section

open Classical

namespace PI.OrbJet.AU

open Formalism.BasicNotions Formalism.MainNotions.G MvPowerSeries PI.OrbJet PI.OrbJet.OrbW PI.OrbShared PI.OrbJet.OJ

section Lin

variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N0 N1 : ℕ} {l : ℕ} [Fact l.Prime]

theorem applyAt0_congr (T T' : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) (P : MvPolynomial (XZ Lt N0 N1) ℤ)
    (h : ∀ μ ∈ P.support, coeff (Finsupp.sumFinsuppEquivProdFinsupp μ).2 T =
      coeff (Finsupp.sumFinsuppEquivProdFinsupp μ).2 T') :
    applyAt0 N0 N1 l T P = applyAt0 N0 N1 l T' P := by
  unfold OJ.applyAt0
  refine Finset.sum_congr rfl fun μ hμ => ?_
  rw [h μ hμ]

theorem applyAt0_zero_left (P : MvPolynomial (XZ Lt N0 N1) ℤ) :
    applyAt0 N0 N1 l (0 : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) P = 0 := by
  unfold applyAt0
  simp

theorem applyAt0_add_left (T T' : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) (P : MvPolynomial (XZ Lt N0 N1) ℤ) :
    applyAt0 N0 N1 l (T + T') P = applyAt0 N0 N1 l T P + applyAt0 N0 N1 l T' P := by
  unfold OJ.applyAt0
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [map_add (f := _), mul_add, map_add (f := _)]

theorem applyAt0_smul_left (c : ℂ_[l]) (T : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l])
    (P : MvPolynomial (XZ Lt N0 N1) ℤ) :
    applyAt0 N0 N1 l (c • T) P = c • applyAt0 N0 N1 l T P := by
  unfold OJ.applyAt0
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [MvPowerSeries.coeff_smul, MvPolynomial.smul_monomial, smul_eq_mul]
  congr 1
  ring

theorem applyAt0_sum_left {ι : Type*} (S : Finset ι) (c : ι → ℂ_[l]) (T : ι → MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l])
    (P : MvPolynomial (XZ Lt N0 N1) ℤ) :
    applyAt0 N0 N1 l (∑ i ∈ S, c i • T i) P = ∑ i ∈ S, c i • applyAt0 N0 N1 l (T i) P := by
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact applyAt0_zero_left P
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, applyAt0_add_left, applyAt0_smul_left, ih]

end Lin

theorem norm_coeff_monomial_one {σ : Type*} {l : ℕ} [Fact l.Prime] (k m : σ →₀ ℕ) :
    ‖coeff m (monomial k (1 : ℂ_[l]))‖ ≤ 1 := by
  rw [MvPowerSeries.coeff_monomial]
  split_ifs <;> simp

theorem constantCoeff_zero_of_bound_general (l d : ℕ) [Fact l.Prime] [NeZero d] (be : MvPowerSeries (ZMod d) ℂ_[l]) (h : OJ.B3 l d be) :
    constantCoeff be = 0 := by
  by_contra hne
  have h1 := (h 0 (by rwa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply])).1
  apply h1
  simp [OJ.bideg]

variable (D : D7) (p : ℕ) [Fact p.Prime]

def Fk (N0 N1 : ℕ) (ep sg : ℂ_[p]) (be : MvPowerSeries (ZMod (nP D p)) ℂ_[p])
    (k : ZMod (nP D p) × Fin N0 × Fin N1 →₀ ℕ) : MvPowerSeries (ZMod (nP D p) × Fin N0 × Fin N1) ℂ_[p] :=
  Tri.sol ep (fun w => C ep * jetLogG p (nP D p) w) (monomial k 1 * Eorb D p (N0 := N0) (N1 := N1) sg be)

def Pm (N0 N1 : ℕ) (ep : ℂ_[p]) (R : Finset (Pl D)) (sg : Pl D → ℂ_[p])
    (be : Pl D → MvPowerSeries (ZMod (nP D p)) ℂ_[p]) (m : Pl D × Fin N0 × Fin N1 →₀ ℕ) :
    MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p] :=
  ∏ r ∈ R, rename (pE D p r (Fin N0 × Fin N1)) (Fk D p N0 N1 ep (sg r) (be r) (resM D p r m))

theorem subst_Pm {N0 N1 : ℕ} (ep : ℂ_[p]) (hep : ep ≠ 0) {R : Finset (Pl D)} (hR : IsReps D p R)
    (sg : Pl D → ℂ_[p]) (be : Pl D → MvPowerSeries (ZMod (nP D p)) ℂ_[p])
    (hcc : ∀ r ∈ R, constantCoeff (be r) = 0) (m : Pl D × Fin N0 × Fin N1 →₀ ℕ) :
    subst (fun v : Pl D × Fin N0 × Fin N1 => C ep * logPl D p v) (Pm D p N0 N1 ep R sg be m) =
      monomial m 1 * subst (logPl D p (β := Fin N0 × Fin N1)) (OJ.expS ℂ_[p] (beAll D p R sg be)) := by
  have hG := (isTri_log D p (β := Fin N0 × Fin N1) ep).hasSubst
  rw [Pm, ← coe_substAlgHom hG, map_prod, E_eq D p R sg be hcc, mono_eq D p hR m, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun r _ => ?_
  rw [coe_substAlgHom, subst_rename, Fk, Tri.subst_sol hep (isTri_jet p (nP D p) ep), map_mul]

theorem orbAddUp_main : ∀ (D : Formalism.BasicNotions.D7) (E : PI.OrbJet.Ent D), PI.OrbJet.OrbitsAddLowerBound E := by
  intro D E p _ h u i hi R hR ep sg be hbe β hβ Th hTh
  obtain ⟨hep, _, hB⟩ := hbe
  have hcc : ∀ r ∈ R, constantCoeff (be r) = 0 := fun r hr => constantCoeff_zero_of_bound_general p (nP D p) (be r) (hB r hr).2.2.1
  have hep0 : ep ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hep
    exact zero_ne_one hep
  obtain ⟨U, hU, hEq⟩ := hTh
  have hTG := isTri_log D p (β := Fin (D.R.N i) × Fin (D.R.N (i + 1))) ep
  have hFk : ∀ r ∈ R, ∀ k, KvalGe (D.R.N i) (D.R.N (i + 1)) p (fun s => E.nu u i (orbMap D p r s))
      (Fk D p (D.R.N i) (D.R.N (i + 1)) ep (sg r) (be r) k) (β r) := by
    intro r hr k
    apply hβ r hr
    refine ⟨monomial k 1, fun m => norm_coeff_monomial_one k m, ?_⟩
    · exact Tri.subst_sol hep0 (isTri_jet p (nP D p) ep) _
  have hPk : ∀ m, KvalGe (D.R.N i) (D.R.N (i + 1)) p (E.nu u i) (Pm D p _ _ ep R sg be m) (∑ r ∈ R, β r) :=
    fun m => kval_prod D p hR _ _ β (fun r hr => hFk r hr _)
  intro I mx
  set G := Gxz (D.R.N i) (D.R.N (i + 1)) (E.nu u i) I with hGdef
  set n := G.support.sup (fun μ => (Finsupp.sumFinsuppEquivProdFinsupp μ).2.degree) + 1 with hn
  set S := (Finsupp.finite_of_degree_lt (σ := Pl D × Fin (D.R.N i) × Fin (D.R.N (i + 1))) n).toFinset with hS
  set Th' := ∑ m ∈ S, coeff m U • Pm D p _ _ ep R sg be m with hTh'
  set Eall := subst (logPl D p (β := Fin (D.R.N i) × Fin (D.R.N (i + 1)))) (OJ.expS ℂ_[p] (beAll D p R sg be))
    with hEall
  have hsub : subst (fun v : Pl D × Fin (D.R.N i) × Fin (D.R.N (i + 1)) => C ep * logPl D p v) (Th - Th') =
      (U - ∑ m ∈ S, monomial m (coeff m U)) * Eall := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [subst_sub hTG.hasSubst, hEq, hTh', ← coe_substAlgHom hTG.hasSubst, map_sum]
    simp_rw [map_smul, coe_substAlgHom, subst_Pm D p ep hep0 hR sg be hcc]
    rw [sub_mul, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [smul_eq_C_mul, ← mul_assoc, ← monomial_zero_eq_C_apply, monomial_mul_monomial, zero_add, mul_one]
  have hagree : ∀ κ : Pl D × Fin (D.R.N i) × Fin (D.R.N (i + 1)) →₀ ℕ, κ.degree < n →
      coeff κ Th = coeff κ Th' := by
    have hv := Tri.vanish_of_subst hep0 hTG (Th - Th') n (by
      intro κ hκ
      rw [hsub, coeff_mul]
      refine Finset.sum_eq_zero fun ab hab => ?_
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hab
      have hdeg : ab.1.degree < n := by
        have : κ.degree = ab.1.degree + ab.2.degree := by rw [← hab, map_add (f := _)]
        omega
      have hmem : ab.1 ∈ S := by
        rw [hS, Set.Finite.mem_toFinset]
        exact hdeg
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_sum, Finset.sum_eq_single ab.1]
      · rw [coeff_monomial, if_pos rfl, sub_self, zero_mul]
      · intro b _ hb
        rw [coeff_monomial, if_neg (Ne.symm hb)]
      · intro h; exact absurd hmem h)
    intro κ hκ
    have := hv κ hκ
    rwa [map_sub, sub_eq_zero] at this
  have hjet : applyAt0 (D.R.N i) (D.R.N (i + 1)) p Th G = applyAt0 (D.R.N i) (D.R.N (i + 1)) p Th' G := by
    refine applyAt0_congr Th Th' G fun μ hμ => hagree _ ?_
    rw [hn]
    exact Nat.lt_succ_of_le (Finset.le_sup (f := fun μ => (Finsupp.sumFinsuppEquivProdFinsupp μ).2.degree) hμ)
  rw [hjet, hTh', applyAt0_sum_left, MvPolynomial.coeff_sum]
  have hpos : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (Real.rpow_nonneg hpos.le _) fun m _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  refine (norm_mul_le _ _).trans ?_
  calc ‖coeff m U‖ * ‖AddMonoidAlgebra.coeff (applyAt0 (D.R.N i) (D.R.N (i + 1)) p (Pm D p _ _ ep R sg be m) G) mx‖
      ≤ 1 * (p : ℝ) ^ (-∑ r ∈ R, β r) :=
        mul_le_mul (hU m) (hPk m I mx) (norm_nonneg _) zero_le_one
    _ = (p : ℝ) ^ (-∑ r ∈ R, β r) := one_mul _

end PI.OrbJet.AU

end
end

theorem PI.OrbAddUp : ∀ (D : Formalism.BasicNotions.D7) (E : PI.OrbJet.Ent D), PI.OrbJet.OrbitsAddLowerBound E :=
  PI.OrbJet.AU.orbAddUp_main
