module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.UnipMemIff

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.SecDec
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.K
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate

section SlopeTestRemainingChoices

variable {K : Type} [Field K] [NumberField K]

private theorem sd_ent {n : ℕ} (h : AdelicGLn.AdelicGL K n) (i j : Fin n) (y : GroundTheory.Global.IdeleGroup K)
    (hy : (y : 𝔸[K]) = (h : Matrix (Fin n) (Fin n) 𝔸[K]) i j) :
    (GroundTheory.Global.IdeleGroup.ideleModule K y : ℝ) ≤ AutomorphicForm.height h := by
  rw [GroundTheory.Global.IdeleGroup.ideleModule_eq, AutomorphicForm.height]
  refine mul_le_mul (Finset.prod_le_prod₀ (fun w _ => by positivity) fun w _ => ?_)
    (finprod_le_finprod_of_nonneg (GroundTheory.Global.IdeleGroup.finite_mulSupport_norm y) (finite_mulSupport_locHeight_finAt h)
      (fun v => norm_nonneg _) fun v => ?_) (finprod_nonneg fun v => norm_nonneg _)
    (Finset.prod_nonneg fun w _ => pow_nonneg (locHeight_pos _).le _)
  · refine pow_le_pow_left₀ (norm_nonneg _) ?_ _
    rw [hy]
    exact norm_apply_le_locHeight (infAt w h) i j
  · rw [hy]
    exact norm_apply_le_locHeight (finAt v h) i j

private theorem mul_upper_triangular_first_col {R : Type} [CommRing R] (S T : Matrix (Fin (2 + 2)) (Fin (2 + 2)) R) (hT : T.IsUpperTriangular)
    (i : Fin (2 + 2)) : (S * T) i 0 = S i 0 * T 0 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single 0 (fun l _ hl => ?_) (fun h => absurd (Finset.mem_univ _) h)
  rw [hT (show (id 0 : Fin (2 + 2)) < id l from Fin.pos_iff_ne_zero.2 hl), mul_zero]

private theorem upper_triangular_mul_last_row {R : Type} [CommRing R] (S T : Matrix (Fin (2 + 2)) (Fin (2 + 2)) R) (hT : T.IsUpperTriangular)
    (j : Fin (2 + 2)) : (T * S) 3 j = T 3 3 * S 3 j := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single 3 (fun l _ hl => ?_) (fun h => absurd (Finset.mem_univ _) h)
  rw [hT (show (id l : Fin (2 + 2)) < id 3 from Fin.lt_last_iff_ne_last.2 hl), zero_mul]

private theorem sd_col (δ : GL (Fin (2 + 2)) K) (T : AdelicGLn.AdelicGL K (2 + 2)) (hT : T ∈ adelicBorel)
    (u : GroundTheory.Global.IdeleGroup K) (hu : (u : 𝔸[K]) = (T : Matrix (Fin (2 + 2)) (Fin (2 + 2)) 𝔸[K]) 0 0) :
    (GroundTheory.Global.IdeleGroup.ideleModule K u : ℝ) ≤ AutomorphicForm.height (AdelicGLn.diagonal K (2 + 2) δ * T) := by
  obtain ⟨i, hi⟩ : ∃ i, (δ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) K) i 0 ≠ 0 := by
    by_contra h
    push Not at h
    have := congrArg (fun M => M 0 0) (Units.inv_mul δ)
    simp only [Matrix.mul_apply, h, mul_zero, Finset.sum_const_zero, Matrix.one_apply_eq] at this
    exact zero_ne_one this
  have h := sd_ent (AdelicGLn.diagonal K (2 + 2) δ * T) i 0 (GroundTheory.Global.IdeleGroup.diagonal K (Units.mk0 _ hi) * u) (by
    rw [Units.val_mul, Units.val_mul, mul_upper_triangular_first_col _ _ hT, hu, GroundTheory.Global.IdeleGroup.coe_diagonal, AdelicGLn.diagonal_apply,
      Units.val_mk0])
  rwa [map_mul, GroundTheory.Global.IdeleGroup.ideleModule_diagonal, one_mul] at h

private theorem sd_row (δ : GL (Fin (2 + 2)) K) (T : AdelicGLn.AdelicGL K (2 + 2)) (hT : T ∈ adelicBorel)
    (u : GroundTheory.Global.IdeleGroup K) (hu : (u : 𝔸[K]) = (T : Matrix (Fin (2 + 2)) (Fin (2 + 2)) 𝔸[K]) 3 3) :
    (GroundTheory.Global.IdeleGroup.ideleModule K u : ℝ) ≤ AutomorphicForm.height (T * AdelicGLn.diagonal K (2 + 2) δ) := by
  obtain ⟨j, hj⟩ : ∃ j, (δ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) K) 3 j ≠ 0 := by
    by_contra h
    push Not at h
    have := congrArg (fun M => M 3 3) (Units.mul_inv δ)
    simp only [Matrix.mul_apply, h, zero_mul, Finset.sum_const_zero, Matrix.one_apply_eq] at this
    exact zero_ne_one this
  have h := sd_ent (T * AdelicGLn.diagonal K (2 + 2) δ) 3 j (u * GroundTheory.Global.IdeleGroup.diagonal K (Units.mk0 _ hj)) (by
    rw [Units.val_mul, Units.val_mul, upper_triangular_mul_last_row _ _ hT, hu, GroundTheory.Global.IdeleGroup.coe_diagonal, AdelicGLn.diagonal_apply,
      Units.val_mk0])
  rwa [map_mul, GroundTheory.Global.IdeleGroup.ideleModule_diagonal, mul_one] at h

private theorem sd_zt (s : ℝ) : ∃ a : GroundTheory.Global.IdeleGroup K, zt K s = diagUnits 2 (fun _ => a) ∧
    (GroundTheory.Global.IdeleGroup.ideleModule K a : ℝ) = Real.exp (s / 2) := by
  obtain ⟨a, ha⟩ : ∃ a : GroundTheory.Global.IdeleGroup K, zt K s = diagUnits 2 (fun _ => a) := ⟨_, rfl⟩
  refine ⟨a, ha, ?_⟩
  have h : (detModule K 2 (zt K s) : ℝ) = Real.exp s := by rw [zt, detModule_centralSection two_pos]
  change (GroundTheory.Global.IdeleGroup.ideleModule K (AdelicGLn.det K 2 (zt K s)) : ℝ) = _ at h
  rw [ha, det_diagUnits, Fin.prod_univ_two, map_mul, Positive.val_mul] at h
  refine (pow_left_inj₀ (GroundTheory.Global.IdeleGroup.ideleModule K a).2.le (Real.exp_pos _).le two_ne_zero).1 ?_
  rw [sq, h, sq, ← Real.exp_add, add_halves]

private theorem sd_lv (s : ℝ) : ∃ a : Fin (2 + 2) → GroundTheory.Global.IdeleGroup K,
    ((lv 1 1 s : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) = diagUnits (2 + 2) a ∧
    (GroundTheory.Global.IdeleGroup.ideleModule K (a 0) : ℝ) = Real.exp (s / 2) ∧
    (GroundTheory.Global.IdeleGroup.ideleModule K (a 3) : ℝ) = Real.exp (-s / 2) := by
  obtain ⟨a, ha, ha'⟩ := sd_zt (K := K) s
  obtain ⟨c, hc, hc'⟩ := sd_zt (K := K) (-s)
  refine ⟨fun i => Sum.elim (fun _ => a) (fun _ => c) (finSumFinEquiv.symm i), ?_, ha', hc'⟩
  rw [blkLaws.1, Subgroup.coe_one, one_mul, one_mul, ha, hc]
  refine Units.ext ?_
  change Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (Matrix.diagonal _) 0 0 (Matrix.diagonal _)) = _
  rw [Matrix.fromBlocks_diagonal, Matrix.reindex_apply, Matrix.submatrix_diagonal_equiv, coe_diagUnits]
  congr 1
  funext i
  dsimp only [Function.comp_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rfl

private theorem sd_key (δ : GL (Fin (2 + 2)) K) (b : AdelicGLn.AdelicGL K (2 + 2)) (hb : b ∈ adelicBorel)
    (a r : Fin (2 + 2) → GroundTheory.Global.IdeleGroup K) :
    (GroundTheory.Global.IdeleGroup.ideleModule K (a 0) : ℝ) * GroundTheory.Global.IdeleGroup.ideleModule K (r 0) ≤ AutomorphicForm.height b *
      AutomorphicForm.height (AdelicGLn.diagonal K (2 + 2) δ * (diagUnits (2 + 2) a * b * diagUnits (2 + 2) r)) ∧
    ((GroundTheory.Global.IdeleGroup.ideleModule K (a 3) : ℝ) * GroundTheory.Global.IdeleGroup.ideleModule K (r 3))⁻¹ ≤ AutomorphicForm.height b *
      AutomorphicForm.height (AdelicGLn.diagonal K (2 + 2) δ * (diagUnits (2 + 2) a * b * diagUnits (2 + 2) r)) := by
  have hT : diagUnits (2 + 2) a * b * diagUnits (2 + 2) r ∈ adelicBorel :=
    mul_mem (mul_mem (diagUnits_mem_adelicBorel _ a) hb) (diagUnits_mem_adelicBorel _ r)
  constructor
  · obtain ⟨β, hβ⟩ := isUnit_apply_self_of_mem_adelicBorel hb 0
    have h1 := sd_col δ _ hT (a 0 * β * r 0) (by
      simp only [Units.val_mul, coe_diagUnits, Matrix.mul_diagonal, Matrix.diagonal_mul, hβ])
    have h2 := sd_ent b⁻¹ 0 0 β⁻¹ (by
      have := mul_upper_triangular_first_col (b⁻¹ : AdelicGLn.AdelicGL K (2 + 2)).val b.val hb 0
      rw [Units.inv_mul, Matrix.one_apply_eq, ← hβ] at this
      exact Units.inv_eq_of_mul_eq_one_left this.symm)
    rw [height_inv, map_inv, Positive.coe_inv] at h2
    rw [map_mul, map_mul, Positive.val_mul, Positive.val_mul] at h1
    have hp := (GroundTheory.Global.IdeleGroup.ideleModule K β).2
    refine le_trans (le_of_eq ?_) (mul_le_mul h2 h1 (le_of_lt (mul_pos (mul_pos (Subtype.prop _) hp) (Subtype.prop _))) (height_pos _).le)
    field_simp
  · obtain ⟨β, hβ⟩ := isUnit_apply_self_of_mem_adelicBorel (inv_mem hb) 3
    have h1 := sd_row δ⁻¹ _ (inv_mem hT) ((r 3)⁻¹ * (β * (a 3)⁻¹)) (by
      rw [show (diagUnits (2 + 2) a * b * diagUnits (2 + 2) r)⁻¹ =
        (diagUnits (2 + 2) r)⁻¹ * (b⁻¹ * (diagUnits (2 + 2) a)⁻¹) by group, ← map_inv, ← map_inv]
      simp only [Units.val_mul, coe_diagUnits, Matrix.mul_diagonal, Matrix.diagonal_mul, hβ, Pi.inv_apply])
    have h2 := sd_ent b 3 3 β⁻¹ (by
      have := upper_triangular_mul_last_row b.val (b⁻¹ : AdelicGLn.AdelicGL K (2 + 2)).val (inv_mem hb : b⁻¹ ∈ adelicBorel) 3
      rw [Units.inv_mul, Matrix.one_apply_eq, ← hβ] at this
      exact Units.inv_eq_of_mul_eq_one_right this.symm)
    rw [map_inv, Positive.coe_inv] at h2
    rw [map_inv (AdelicGLn.diagonal K (2 + 2)) δ] at h1
    rw [← mul_inv_rev (AdelicGLn.diagonal K (2 + 2) δ) (diagUnits (2 + 2) a * b * diagUnits (2 + 2) r)] at h1
    rw [height_inv] at h1
    rw [map_mul, map_mul, map_inv, map_inv, Positive.val_mul, Positive.val_mul, Positive.coe_inv, Positive.coe_inv] at h1
    have hp := (GroundTheory.Global.IdeleGroup.ideleModule K β).2
    have hp1 := (GroundTheory.Global.IdeleGroup.ideleModule K (a 3)).2
    have hp2 := (GroundTheory.Global.IdeleGroup.ideleModule K (r 3)).2
    refine le_trans (le_of_eq ?_) (mul_le_mul h2 h1 (by positivity) (height_pos _).le)
    field_simp

private theorem sd_real {d : ℕ} (hd : 0 < d) {ρ : Fin (2 + 2) → ℝ} (hρ : ∀ i, 0 < ρ i) {h C X : ℝ} (hX : 1 ≤ X) (hC : 0 ≤ C)
    (h1 : |h - (d : ℝ) * Real.log (ρ 0 * ρ 1)| ≤ C) (h2 : |Real.log (ρ 0 * ρ 1 * (ρ 2 * ρ 3))| ≤ C)
    (h3 : Real.exp (-h / 2) * ρ 0 ^ d ≤ X) (h4 : (Real.exp (- -h / 2) * ρ 3 ^ d)⁻¹ ≤ X) :
    inR ρ ≤ Real.exp (3 * C) * X ^ 4 := by
  have p0 := hρ 0
  have p1 := hρ 1
  have p2 := hρ 2
  have p3 := hρ 3
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hL := Real.log_nonneg hX
  have h3' := Real.log_le_log (by positivity) h3
  have h4' := Real.log_le_log (by positivity) h4
  rw [Real.log_mul (by positivity) (by positivity), Real.log_exp, Real.log_pow] at h3'
  rw [Real.log_inv, Real.log_mul (by positivity) (by positivity), Real.log_exp, Real.log_pow] at h4'
  rw [Real.log_mul (by positivity) (by positivity)] at h1
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity)] at h2
  rw [← Real.log_le_log_iff (by unfold inR; positivity) (by positivity), inR, Real.log_mul (by positivity) (by positivity),
    Real.log_div p0.ne' p1.ne', Real.log_div p2.ne' p3.ne', Real.log_mul (by positivity) (by positivity), Real.log_exp,
    Real.log_pow]
  have h5 := (abs_le.1 h1).2
  have h6 := (abs_le.1 h2).2
  have h7 : (d : ℝ) * -(Real.log (ρ 1) + Real.log (ρ 3)) ≤ C + 2 * Real.log X := by linarith
  have h8 : -(Real.log (ρ 1) + Real.log (ρ 3)) ≤ C + 2 * Real.log X := by
    rcases le_total (-(Real.log (ρ 1) + Real.log (ρ 3))) 0 with h | h
    · linarith
    · exact (le_mul_of_one_le_left h hd1).trans h7
  push_cast
  linarith

end SlopeTestRemainingChoices

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.secDec :
    ∀ {K : Type} [Field K] [NumberField K] (ω : Set (AdelicGLn.AdelicGL K (2 + 2))) (t : ℝ), Bor ω → 0 < t → ∀ f : G1 K (2 + 2) → ℂ, SFun f → ∀ N : ℕ, ∃ C : ℝ, ∀ (ρ : Fin (2 + 2) → ℝ) (z : G1 K (2 + 2)), Sg ω ρ z → Rel t ρ →
      ‖f z‖ * inR ρ ^ N ≤ C := by
  intro K _ _ ω t hω _ f hf N
  obtain ⟨C, c, hC, hS⟩ := sgBasics ω hω
  obtain ⟨M, hM⟩ := exists_height_le_of_isCompact hω.1
  obtain ⟨C', hC'⟩ := hf.dec (4 * N) 0
  have hc1 := one_le_heightConst (K := K) (n := 2 + 2)
  refine ⟨(Real.exp (3 * C) * (M * heightConst K (2 + 2)) ^ 4) ^ N * C', fun ρ z hz _ => ?_⟩
  obtain ⟨h1, h2, -⟩ := hS ρ z hz
  obtain ⟨hρ, b, hb, k, hk, e⟩ := hz
  have hy : HH (lv 1 1 (-HH z) * z) = 0 := by
    have := (hpSpec (K := K)).1 0 1 1 (-HH z) z
    rw [show nn (K := K) 0 = 1 from unipOne_zero _, one_mul] at this
    rw [this, neg_add_cancel]
  obtain ⟨γ, hγ, hd⟩ := hC' _ (by rw [hy, abs_zero])
  rw [hf.ray] at hd
  obtain ⟨δ, hδ⟩ : ∃ δ : GL (Fin (2 + 2)) K, AdelicGLn.diagonal K (2 + 2) δ = (γ : AdelicGLn.AdelicGL K (2 + 2)) := by
    obtain ⟨γ', -, rfl⟩ := hγ
    exact γ'.2
  obtain ⟨a, ha, ha0, ha3⟩ := sd_lv (K := K) (-HH z)
  set H := AutomorphicForm.height ((γ * (lv 1 1 (-HH z) * z) : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) with hH
  have hH1 : 1 ≤ H := one_le_height _
  have hbM : AutomorphicForm.height b ≤ M := hM b hb
  have hM1 : 1 ≤ M := (one_le_height b).trans hbM
  obtain ⟨h3, h4⟩ := sd_key δ b (hω.2 hb) a fun i => posIdele (K := K) (ρ i) (hρ i)
  have h5 : AutomorphicForm.height b * AutomorphicForm.height (AdelicGLn.diagonal K (2 + 2) δ *
      (diagUnits (2 + 2) a * b * diagUnits (2 + 2) fun i => posIdele (K := K) (ρ i) (hρ i))) ≤ M * heightConst K (2 + 2) * H := by
    have h6 := height_mul_le ((γ * (lv 1 1 (-HH z) * z) : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) k⁻¹
    rw [height_inv, height_eq_one_of_mem_maxCompact hk, mul_one, ← hH, Subgroup.coe_mul, Subgroup.coe_mul, ha, ← hδ, e] at h6
    simp only [mul_assoc, mul_inv_cancel, mul_one] at h6 ⊢
    exact mul_le_mul hbM h6 (height_pos _).le (by linarith)
  rw [ha0, ideleModule_posIdele] at h3
  rw [ha3, ideleModule_posIdele] at h4
  have h7 := sd_real Module.finrank_pos hρ (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hM1 hc1) hH1)
    (by linarith) h1 h2 (h3.trans h5) (h4.trans h5)
  have h8 : 0 ≤ inR ρ := by
    have := hρ 0
    have := hρ 1
    have := hρ 2
    have := hρ 3
    unfold inR
    positivity
  calc ‖f z‖ * inR ρ ^ N ≤ ‖f z‖ * (Real.exp (3 * C) * (M * heightConst K (2 + 2) * H) ^ 4) ^ N :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h8 h7 N) (norm_nonneg _)
    _ = (Real.exp (3 * C) * (M * heightConst K (2 + 2)) ^ 4) ^ N * (‖f z‖ * H ^ (4 * N)) := by
        rw [mul_pow _ H, ← mul_assoc (Real.exp _), mul_pow _ (H ^ 4), ← pow_mul]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hd (by positivity)
end

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.K
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate

private theorem fs_ratio (ρ : Fin (2 + 2) → ℝ) (hρ : ∀ i, 0 < ρ i) (t C H d : ℝ) (ht : 0 < t) (hd : 1 ≤ d) (hH : 0 ≤ H)
    (hr : Rel t ρ) (h1 : |H - d * Real.log (ρ 0 * ρ 1)| ≤ C) (h2 : |Real.log (ρ 0 * ρ 1 * (ρ 2 * ρ 3))| ≤ C) (i j : Fin (2 + 2)) :
    ρ i / ρ j ≤ Real.exp (2 * C + |Real.log t|) * Real.exp H * max 1 (inR ρ) := by
  have p0 := hρ 0
  have p1 := hρ 1
  have p2 := hρ 2
  have p3 := hρ 3
  have hm : 0 < max 1 (inR ρ) := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hM0 : 0 ≤ Real.log (max 1 (inR ρ)) := Real.log_nonneg (le_max_left _ _)
  have hL : Real.log (ρ 0) - Real.log (ρ 1) + (Real.log (ρ 2) - Real.log (ρ 3)) ≤ Real.log (max 1 (inR ρ)) := by
    rw [← Real.log_div p0.ne' p1.ne', ← Real.log_div p2.ne' p3.ne', ← Real.log_mul (by positivity) (by positivity)]
    exact Real.log_le_log (by positivity) (le_max_right _ _)
  have r1 := Real.log_le_log (by positivity) hr.1
  have r2 := Real.log_le_log (by positivity) hr.2
  rw [Real.log_mul ht.ne' p1.ne'] at r1
  rw [Real.log_mul ht.ne' p3.ne'] at r2
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul p0.ne' p1.ne', Real.log_mul p2.ne' p3.ne', abs_le] at h2
  rw [Real.log_mul p0.ne' p1.ne', abs_le] at h1
  have hτ := neg_abs_le (Real.log t)
  have hτ0 := abs_nonneg (Real.log t)
  have hs : -C ≤ Real.log (ρ 0) + Real.log (ρ 1) ∧ Real.log (ρ 0) + Real.log (ρ 1) ≤ H + C := by
    rcases le_total 0 (Real.log (ρ 0) + Real.log (ρ 1)) with h | h
    · have := mul_le_mul_of_nonneg_right hd h
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    · have := mul_le_mul_of_nonpos_right hd h
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hb : ∀ k : Fin (2 + 2), |Real.log (ρ k)| ≤ (2 * C + |Real.log t| + H + Real.log (max 1 (inR ρ))) / 2 := by
    have hk : ∀ k : Fin (2 + 2), k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by decide
    intro k
    rw [abs_le]
    rcases hk k with rfl | rfl | rfl | rfl <;> constructor <;> linarith [hs.1, hs.2, h2.1, h2.2]
  have e : ρ i / ρ j = Real.exp (Real.log (ρ i) - Real.log (ρ j)) := by
    rw [Real.exp_sub, Real.exp_log (hρ i), Real.exp_log (hρ j)]
  rw [e, ← Real.exp_log hm, ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  linarith [(abs_le.1 (hb i)).2, (abs_le.1 (hb j)).1]

private theorem fs_point {K : Type} [Field K] [NumberField K] (ω : Set (AdelicGLn.AdelicGL K (2 + 2))) (t : ℝ) (hω : Bor ω)
    (ht : 0 < t) (f : G1 K (2 + 2) → ℂ) (hf : SFun f) (N₀ : ℕ) :
    ∃ N₁ : ℕ, ∀ M : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ (ρ : Fin (2 + 2) → ℝ) (z : G1 K (2 + 2)), Sg ω ρ z → Rel t ρ → 0 ≤ HH z →
      Real.exp (2 * HH z) * ‖f z‖ * AutomorphicForm.height (z : AdelicGLn.AdelicGL K (2 + 2)) ^ N₀ * max 1 (inR ρ) ^ M ≤
        D * qht z ^ N₁ := by
  obtain ⟨C, c, hC, hs⟩ := sgBasics ω hω
  obtain ⟨c₀, C₀, hc₀, hq⟩ := hpQht (K := K)
  refine ⟨⌈c₀⌉₊ * (2 + c * N₀), fun M => ?_⟩
  obtain ⟨D₀, hD₀⟩ := secDec ω t hω ht f hf 0
  obtain ⟨D₁, hD₁⟩ := secDec ω t hω ht f hf (c * N₀ + M)
  set A := Real.exp (2 * C + |Real.log t|) with hA
  have hA1 : 1 ≤ A := Real.one_le_exp (by have := abs_nonneg (Real.log t); linarith)
  refine ⟨(C * A ^ c) ^ N₀ * max 0 (max D₀ D₁) * Real.exp C₀ ^ (2 + c * N₀), by positivity, fun ρ z hz hr hH => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hs ρ z hz
  have hd : (1 : ℝ) ≤ (Module.finrank ℚ K : ℝ) := by exact_mod_cast Module.finrank_pos
  set m := max 1 (inR ρ) with hm
  have hm1 : 1 ≤ m := le_max_left _ _
  set E := Real.exp (HH z) with hE
  have hE1 : 1 ≤ E := Real.one_le_exp hH
  have h4 := h3 (A * E * m) (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hA1 hE1) hm1)
    (fs_ratio ρ hz.1 t C (HH z) _ ht hd hH hr h1 h2)
  have hQ : 1 ≤ qht z := (qhtBasic K (2 + 2)).1 z
  have h5 : E ≤ Real.exp C₀ * qht z ^ ⌈c₀⌉₊ := by
    rw [← Real.exp_log (lt_of_lt_of_le one_pos hQ), ← Real.exp_nat_mul, ← Real.exp_add, hE, Real.exp_le_exp]
    have := mul_le_mul_of_nonneg_right (Nat.le_ceil c₀) (Real.log_nonneg hQ)
    linarith [hq z]
  have h6 : ‖f z‖ * m ^ (c * N₀ + M) ≤ max 0 (max D₀ D₁) := by
    refine le_trans ?_ (le_max_right _ _)
    rcases le_total 1 (inR ρ) with h | h
    · rw [hm, max_eq_right h]
      exact (hD₁ ρ z hz hr).trans (le_max_right _ _)
    · rw [hm, max_eq_left h, one_pow, ← pow_zero (inR ρ)]
      exact (hD₀ ρ z hz hr).trans (le_max_left _ _)
  have e2 : Real.exp (2 * HH z) = E ^ 2 := by rw [hE, ← Real.exp_nat_mul]; norm_num
  have hh0 := (height_pos (z : AdelicGLn.AdelicGL K (2 + 2))).le
  calc Real.exp (2 * HH z) * ‖f z‖ * AutomorphicForm.height (z : AdelicGLn.AdelicGL K (2 + 2)) ^ N₀ * m ^ M
      ≤ E ^ 2 * ‖f z‖ * (C * (A * E * m) ^ c) ^ N₀ * m ^ M := by rw [e2]; gcongr
    _ = (C * A ^ c) ^ N₀ * (‖f z‖ * m ^ (c * N₀ + M)) * E ^ (2 + c * N₀) := by ring
    _ ≤ (C * A ^ c) ^ N₀ * max 0 (max D₀ D₁) * (Real.exp C₀ * qht z ^ ⌈c₀⌉₊) ^ (2 + c * N₀) := by gcongr
    _ = _ := by rw [mul_pow (Real.exp C₀), ← pow_mul, mul_assoc _ _ (qht z ^ _)]

private theorem fs_sum {K : Type} [Field K] [NumberField K] : ∃ (N₀ : ℕ) (C : ℝ), ∀ (x : G1 K (2 + 2)) (S : Finset (Cos K))
    (g : Cos K → ℝ) (B : ℝ), 0 ≤ B →
    (∀ q ∈ S, ∃ δ ∈ PK K, g q * AutomorphicForm.height ((δ * qx q x : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) ^ N₀ ≤ B) →
    ∑ q ∈ S, g q ≤ C * B := by
  classical
  obtain ⟨N, C, hC, hs⟩ := sumHt (K := K) (2 + 2)
  refine ⟨N, C.toReal, fun x S g B hB h => ?_⟩
  set φ : Gam K (2 + 2) → ℝ := fun γ =>
    (AutomorphicForm.height (((γ : G1 K (2 + 2)) * x : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) ^ N)⁻¹ with hφ
  have hφ0 : ∀ γ, 0 ≤ φ γ := fun γ => inv_nonneg.2 (pow_nonneg (height_pos _).le _)
  have h' : ∀ q : Cos K, ∃ γ : Gam K (2 + 2), (Quotient.mk _ γ : Cos K) = q ∧ (q ∈ S → g q ≤ φ γ * B) := by
    intro q
    by_cases hq : q ∈ S
    · obtain ⟨_, ⟨δ, hδ, rfl⟩, hb⟩ := h q hq
      refine ⟨δ * q.out, ?_, fun _ => ?_⟩
      · refine Eq.trans (Quotient.sound ?_) (Quotient.out_eq q)
        change QuotientGroup.rightRel _ _ _
        rw [QuotientGroup.rightRel_apply]
        simpa using hδ
      · rw [hφ]
        beta_reduce
        rw [le_inv_mul_iff₀ (pow_pos (height_pos _) _), mul_comm, Subgroup.coe_mul (Gam K (2 + 2)), mul_assoc]
        exact hb
    · exact ⟨q.out, Quotient.out_eq q, fun h => absurd h hq⟩
  choose γ hγ hg using h'
  have hinj : Function.Injective γ := fun a b e => by rw [← hγ a, ← hγ b, e]
  have h1 : ∑ q ∈ S, φ (γ q) ≤ C.toReal := by
    rw [← ENNReal.ofReal_le_iff_le_toReal hC, ENNReal.ofReal_sum_of_nonneg fun q _ => hφ0 _,
      ← Finset.sum_image (f := fun a => ENNReal.ofReal (φ a)) fun a _ b _ e => hinj e]
    exact (ENNReal.sum_le_tsum _).trans (hs x)
  calc ∑ q ∈ S, g q ≤ ∑ q ∈ S, φ (γ q) * B := Finset.sum_le_sum fun q hq => hg q hq
    _ = (∑ q ∈ S, φ (γ q)) * B := (Finset.sum_mul _ _ _).symm
    _ ≤ C.toReal * B := mul_le_mul_of_nonneg_right h1 hB

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.farSum :
    ∀ {K : Type} [Field K] [NumberField K] (ω : Set (AdelicGLn.AdelicGL K (2 + 2))) (t : ℝ), Red ω t → ∀ f : G1 K (2 + 2) → ℂ, SFun f →
      (∃ (C : ℝ) (N : ℕ), ∀ (x : G1 K (2 + 2)) (S : Finset (Cos K)), (∀ q ∈ S, 0 ≤ HH (qx q x)) →
        ∑ q ∈ S, Real.exp (2 * HH (qx q x)) * ‖f (qx q x)‖ ≤ C * qht x ^ N) ∧
      ∀ (ε : ℝ) (N' : ℕ), 0 < ε → ∃ C : ℝ, ∀ (x : G1 K (2 + 2)) (S : Finset (Cos K)), (∀ q ∈ S, 0 ≤ HH (qx q x) ∧ Far ω t ε (qx q x)) →
        ∑ q ∈ S, Real.exp (2 * HH (qx q x)) * ‖f (qx q x)‖ ≤ C * (qht x ^ N')⁻¹ := by
  intro K _ _ ω t hred f hf
  obtain ⟨N₀, C, hsum⟩ := fs_sum (K := K)
  obtain ⟨N₁, hp⟩ := fs_point ω t hred.bor hred.pos f hf N₀
  obtain ⟨hq1, hq2, -⟩ := qhtBasic K (2 + 2)
  have hqx : ∀ (q : Cos K) (x : G1 K (2 + 2)), qht (qx q x) = qht x := fun q x => hq2 _ q.out.2 x
  have hqδ : ∀ δ ∈ PK K, ∀ z : G1 K (2 + 2), qht (δ * z) = qht z := by
    rintro _ ⟨δ, -, rfl⟩ z
    exact hq2 _ δ.2 z
  have hH := (hpSpec (K := K)).2.2.1
  refine ⟨?_, fun ε N' hε => ?_⟩
  · obtain ⟨D, hD, h⟩ := hp 0
    refine ⟨C * D, N₁, fun x S hS => ?_⟩
    rw [mul_assoc]
    refine hsum x S _ _ (mul_nonneg hD (pow_nonneg (zero_le_one.trans (hq1 x)) _)) fun q hq => ?_
    obtain ⟨δ, hδ, ρ, h1, h2⟩ := hred.rel (qx q x)
    have h3 := h ρ _ h1 h2 (by rw [hH δ hδ]; exact hS q hq)
    rw [pow_zero, mul_one, hH δ hδ, hf.rat δ hδ, hqδ δ hδ, hqx] at h3
    exact ⟨δ, hδ, h3⟩
  · obtain ⟨D, hD, h⟩ := hp ⌈((N₁ + N' : ℕ) : ℝ) / ε⌉₊
    refine ⟨C * D, fun x S hS => ?_⟩
    rw [mul_assoc]
    have hx0 : 0 < qht x := one_pos.trans_le (hq1 x)
    refine hsum x S _ _ (by positivity) fun q hq => ?_
    obtain ⟨h0, δ, hδ, ρ, h1, h2, h4⟩ := hS q hq
    have h3 := h ρ _ h1 h2 (by rw [hH δ hδ]; exact h0)
    rw [hH δ hδ, hf.rat δ hδ, hqδ δ hδ, hqx] at h3
    rw [hqx] at h4
    refine ⟨δ, hδ, ?_⟩
    have h5 : qht x ^ (N₁ + N') ≤ max 1 (inR ρ) ^ ⌈((N₁ + N' : ℕ) : ℝ) / ε⌉₊ := by
      refine le_trans ?_ (pow_le_pow_left₀ (Real.rpow_nonneg hx0.le ε) (h4.trans (le_max_right _ _)) _)
      rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
      refine Real.rpow_le_rpow_of_exponent_le (hq1 x) ?_
      rw [mul_comm, ← div_le_iff₀ hε]
      exact Nat.le_ceil _
    have hh0 := (height_pos ((δ * qx q x : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2))).le
    have h6 := (mul_le_mul_of_nonneg_left h5 (by positivity)).trans h3
    rw [pow_add, mul_comm (qht x ^ N₁), ← mul_assoc, mul_le_mul_iff_left₀ (pow_pos hx0 _)] at h6
    rwa [← div_eq_mul_inv, le_div_iff₀ (pow_pos hx0 _)]
