module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

section SlopeTestRemainingChoices

variable {R S : Type} [CommRing R] [CommRing S] {a b : ℕ}

private theorem blk_val (x : GL (Fin a) R) (y : GL (Fin b) R) :
    (blk x y).val = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks x.val 0 0 y.val) := rfl

private theorem blk_inv_val (x : GL (Fin a) R) (y : GL (Fin b) R) :
    (blk x y)⁻¹ = blk x⁻¹ y⁻¹ := Units.ext rfl

private theorem wGL_val :
    (wGL R).val = Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks 0 (1 : Matrix (Fin 2) (Fin 2) R) 1 0) := rfl

private theorem wGL_inv : (wGL R)⁻¹ = wGL R := Units.ext rfl

private theorem blk_mul' (x x' : GL (Fin a) R) (y y' : GL (Fin b) R) :
    blk x y * blk x' y' = blk (x * x') (y * y') := by
  apply Units.ext
  simp only [Units.val_mul, blk_val, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]

private theorem blk_one' : blk (1 : GL (Fin a) R) (1 : GL (Fin b) R) = 1 := by
  apply Units.ext
  simp only [blk_val, Units.val_one, Matrix.fromBlocks_one, Matrix.reindex_apply, Matrix.submatrix_one_equiv]

private theorem w_blk (x y : GL (Fin 2) R) : wGL R * blk x y = blk y x * wGL R := by
  apply Units.ext
  simp only [Units.val_mul, blk_val, wGL_val, Matrix.reindex_apply, Matrix.submatrix_mul_equiv,
    Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul]

private theorem blk_det (x : GL (Fin a) R) (y : GL (Fin b) R) :
    Matrix.GeneralLinearGroup.det (blk x y) = Matrix.GeneralLinearGroup.det x * Matrix.GeneralLinearGroup.det y := by
  apply Units.ext
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.val_det_apply, blk_val, Matrix.det_reindex_self,
    Matrix.det_fromBlocks_zero₂₁]

private theorem blk_map (f : R →+* S) (x : GL (Fin a) R) (y : GL (Fin b) R) :
    (blk x y).val.map f =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (x.val.map f) 0 0 (y.val.map f)) := by
  ext i j
  simp only [blk_val, Matrix.reindex_apply, Matrix.map_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> simp

private theorem w_map (f : R →+* S) : (wGL R).val.map f = (wGL S).val := by
  ext i j
  simp only [wGL_val, Matrix.reindex_apply, Matrix.map_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;>
    simp [Matrix.one_apply, apply_ite f]

private theorem blk_cont [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous fun p : GL (Fin a) R × GL (Fin b) R => blk p.1 p.2 := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (Continuous.matrix_fromBlocks (Units.continuous_val.comp continuous_fst) continuous_const continuous_const
      (Units.continuous_val.comp continuous_snd)).matrix_reindex _ _
  · exact (Continuous.matrix_fromBlocks (Units.continuous_coe_inv.comp continuous_fst) continuous_const continuous_const
      (Units.continuous_coe_inv.comp continuous_snd)).matrix_reindex _ _

private theorem blk_ent (O : Subring S) (x : GL (Fin a) S) (y : GL (Fin b) S) (hx : ∀ i j, x i j ∈ O)
    (hy : ∀ i j, y i j ∈ O) (i j : Fin (a + b)) : blk x y i j ∈ O := by
  change (blk x y).val i j ∈ O
  simp only [blk_val, Matrix.reindex_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> simp [hx, hy]

private theorem w_ent (O : Subring S) (i j : Fin (2 + 2)) : wGL S i j ∈ O := by
  change (wGL S).val i j ∈ O
  simp only [wGL_val, Matrix.reindex_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.one_apply, O.zero_mem] <;>
    split_ifs <;> simp

private theorem vec_l (M : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) S) (y : Fin (a + b) → S) (j : Fin a ⊕ Fin b) :
    Matrix.vecMul y (Matrix.reindex finSumFinEquiv finSumFinEquiv M) (finSumFinEquiv j) =
      ∑ i : Fin a, y (finSumFinEquiv (Sum.inl i)) * M (Sum.inl i) j +
        ∑ i : Fin b, y (finSumFinEquiv (Sum.inr i)) * M (Sum.inr i) j := by
  simp only [Matrix.vecMul, dotProduct, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [Equiv.symm_apply_apply]

end SlopeTestRemainingChoices

variable {K : Type} [Field K] [NumberField K]

omit [NumberField K] in
private theorem blk_arch {a b : ℕ} (w : InfinitePlace K) {x : GL (Fin a) w.Completion} {y : GL (Fin b) w.Completion}
    (hx : x ∈ archCompact w) (hy : y ∈ archCompact w) : blk x y ∈ archCompact (n := a + b) w := by
  intro z
  refine (sq_eq_sq₀ (euclidNorm_nonneg _) (euclidNorm_nonneg _)).1 ?_
  have h1 := congrArg (· ^ 2) (hx fun i => z (finSumFinEquiv (Sum.inl i)))
  have h2 := congrArg (· ^ 2) (hy fun i => z (finSumFinEquiv (Sum.inr i)))
  simp only [euclidNorm_sq, Matrix.vecMul, dotProduct] at h1 h2
  rw [euclidNorm_sq, euclidNorm_sq, ← finSumFinEquiv.sum_comp, ← finSumFinEquiv.sum_comp (fun i => ‖z i‖ ^ 2),
    Fintype.sum_sum_type, Fintype.sum_sum_type, ← h1, ← h2]
  simp only [blk_val, vec_l, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, zero_add]

omit [NumberField K] in
private theorem w_arch (w : InfinitePlace K) : wGL w.Completion ∈ archCompact (n := 2 + 2) w := by
  intro z
  refine (sq_eq_sq₀ (euclidNorm_nonneg _) (euclidNorm_nonneg _)).1 ?_
  rw [euclidNorm_sq, euclidNorm_sq, ← finSumFinEquiv.sum_comp, ← finSumFinEquiv.sum_comp (fun i => ‖z i‖ ^ 2),
    Fintype.sum_sum_type, Fintype.sum_sum_type, add_comm]
  simp only [wGL_val, vec_l, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, zero_add,
      Matrix.one_apply, mul_ite, mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true]

private theorem blk_max {a b : ℕ} {x : AdelicGLn.AdelicGL K a} {y : AdelicGLn.AdelicGL K b}
    (hx : x ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K a)))
    (hy : y ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K b))) :
    blk x y ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K (a + b))) := by
  refine ⟨fun w => ?_, fun v => ?_⟩
  · have : infAt w (blk x y) = blk (infAt w x) (infAt w y) :=
      Units.ext (Matrix.ext fun i j => congrArg (fun N => N i j) (blk_map (infEval w) x y))
    rw [this]
    exact blk_arch w (hx.1 w) (hy.1 w)
  · have : finAt v (blk x y) = blk (finAt v x) (finAt v y) :=
      Units.ext (Matrix.ext fun i j => congrArg (fun N => N i j) (blk_map (finEval v) x y))
    rw [this, GLnLocal.mem_integralGL_iff, blk_inv_val]
    have h1 := (GLnLocal.mem_integralGL_iff _ _).1 (hx.2 v)
    have h2 := (GLnLocal.mem_integralGL_iff _ _).1 (hy.2 v)
    exact ⟨blk_ent _ _ _ h1.1 h2.1, blk_ent _ _ _ h1.2 h2.2⟩

private theorem w_max : wGL 𝔸[K] ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K (2 + 2))) := by
  refine ⟨fun w => ?_, fun v => ?_⟩
  · have : infAt w (wGL 𝔸[K]) = wGL _ :=
      Units.ext (Matrix.ext fun i j => congrArg (fun N => N i j) (w_map (infEval w)))
    rw [this]
    exact w_arch w
  · have : finAt v (wGL 𝔸[K]) = wGL _ :=
      Units.ext (Matrix.ext fun i j => congrArg (fun N => N i j) (w_map (finEval v)))
    rw [this, GLnLocal.mem_integralGL_iff, wGL_inv]
    exact ⟨w_ent _, w_ent _⟩

private theorem det_blk (a b : AdelicGLn.AdelicGL K 2) :
    detModule K (2 + 2) (blk a b) = detModule K 2 a * detModule K 2 b := by
  simp only [detModule, MonoidHom.comp_apply, AdelicGLn.det, blk_det, map_mul]

private theorem coe_ret {n : ℕ} {g : AdelicGLn.AdelicGL K n} (h : g ∈ normOneGL (K := K) (n := n)) :
    (retractOne g : AdelicGLn.AdelicGL K n) = g :=
  congrArg Subtype.val (retractOne_coe (⟨g, h⟩ : normOneGL (K := K) (n := n)))

private theorem zt_add (s t : ℝ) : zt K (s + t) = zt K s * zt K t := by
  rw [zt, zt, zt, ← map_mul]
  exact congrArg _ (Subtype.ext (Real.exp_add s t))

private theorem zt_zero : zt K 0 = 1 := by
  rw [zt, ← map_one (centralSection K 2)]
  exact congrArg _ (Subtype.ext Real.exp_zero)

private theorem lv_coe (m₁ m₂ : G1 K 2) (t : ℝ) :
    ((lv m₁ m₂ t : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) =
      blk ((m₁ : AdelicGLn.AdelicGL K 2) * zt K t) ((m₂ : AdelicGLn.AdelicGL K 2) * zt K (-t)) := by
  refine coe_ret (mem_normOneGL_iff_detModule.2 ?_)
  rw [det_blk, map_mul, map_mul, mem_normOneGL_iff_detModule.1 m₁.2, mem_normOneGL_iff_detModule.1 m₂.2,
    one_mul, one_mul, ← map_mul, ← zt_add, add_neg_cancel, zt_zero, map_one]

private theorem mul_zt (m m' : AdelicGLn.AdelicGL K 2) (s t : ℝ) :
    m * zt K s * (m' * zt K t) = m * m' * zt K (s + t) := by
  rw [zt_add, mul_assoc, ← mul_assoc (zt K s), show zt K s * m' = m' * zt K s from centralSection_mul_comm _ _]
  simp only [mul_assoc]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.blkLaws :
    ∀ {K : Type} [Field K] [NumberField K], (∀ (m₁ m₂ : G1 K 2) (t : ℝ), ((lv m₁ m₂ t : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) = blk ((m₁ : AdelicGLn.AdelicGL K 2) * zt K t) ((m₂ : AdelicGLn.AdelicGL K 2) * zt K (-t))) ∧
      (∀ (m₁ m₂ m₁' m₂' : G1 K 2) (t t' : ℝ), lv m₁ m₂ t * lv m₁' m₂' t' = lv (m₁ * m₁') (m₂ * m₂') (t + t')) ∧ lv (1 : G1 K 2) 1 0 = 1 ∧
      Continuous (fun p : G1 K 2 × G1 K 2 × ℝ => lv p.1 p.2.1 p.2.2) ∧
      (∀ a b : AdelicGLn.AdelicGL K 2, detModule K (2 + 2) (blk a b) = detModule K 2 a * detModule K 2 b) ∧
      (∀ a b a' b' : AdelicGLn.AdelicGL K 2, blk a b * blk a' b' = blk (a * a') (b * b')) ∧
      ((w0 K : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) = wGL 𝔸[K] ∧ w0 K ∈ Gam K (2 + 2) ∧ w0 K ∈ KG K (2 + 2) ∧
      (∀ (m₁ m₂ : G1 K 2) (t : ℝ), w0 K * lv m₁ m₂ t = lv m₂ m₁ (-t) * w0 K) ∧
      (∀ u₁ ∈ KG K 2, ∀ u₂ ∈ KG K 2, lv u₁ u₂ 0 ∈ KG K (2 + 2)) ∧ ∀ n, IsCompact (KG K n : Set (G1 K n)) ∧
        ∀ k ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K n)), k ∈ normOneGL (K := K) (n := n) := by
  intro K _ _
  have hw : ((w0 K : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) = wGL 𝔸[K] :=
    coe_ret (maxCompact_le_normOneGL w_max)
  have hz : Continuous (zt K) := continuous_centralSection.comp (Real.continuous_exp.subtype_mk _)
  refine ⟨lv_coe, ?_, ?_, ?_, det_blk, fun a b a' b' => blk_mul' a a' b b', hw, ?_, ?_, ?_, ?_, fun n => ⟨?_, ?_⟩⟩
  · intro m₁ m₂ m₁' m₂' t t'
    apply Subtype.ext
    rw [Subgroup.coe_mul, lv_coe, lv_coe, lv_coe, blk_mul', mul_zt, mul_zt, neg_add, Subgroup.coe_mul, Subgroup.coe_mul]
  · apply Subtype.ext
    rw [lv_coe, neg_zero, zt_zero, Subgroup.coe_one, Subgroup.coe_one, mul_one, blk_one']
  · exact continuous_retractOne.comp (blk_cont.comp
      (((continuous_subtype_val.comp continuous_fst).mul (hz.comp continuous_snd.snd)).prodMk
        ((continuous_subtype_val.comp continuous_snd.fst).mul (hz.comp continuous_snd.snd.neg))))
  · change ((w0 K : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) ∈ AdelicGLn.rationalGL K (2 + 2)
    rw [hw]
    exact ⟨wGL K, Units.ext (w_map (algebraMap K 𝔸[K]))⟩
  · change ((w0 K : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) ∈ Reduction.maxCompact
    rw [hw]
    exact w_max
  · intro m₁ m₂ t
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, lv_coe, lv_coe, hw, neg_neg, w_blk]
  · intro u₁ h₁ u₂ h₂
    change ((lv u₁ u₂ 0 : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) ∈ Reduction.maxCompact
    rw [lv_coe, neg_zero, zt_zero, mul_one, mul_one]
    exact blk_max h₁ h₂
  · refine Topology.IsInducing.subtypeVal.isCompact_preimage' isCompact_maxCompact ?_
    intro k hk
    exact ⟨⟨k, maxCompact_le_normOneGL hk⟩, rfl⟩
  · exact fun k hk => maxCompact_le_normOneGL hk
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.DenseCc
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem ex_rep (d : ℕ) (β : ℝ → ℂ) (v : Eu d) (hβ : Continuous β) (hc : HasCompactSupport β) :
    ∃ u : L (Eu d), ∀ᵐ x : ℝ, u x = β x • v := by
  have h1 : Continuous fun x => β x • v := hβ.smul continuous_const
  have h2 : HasCompactSupport fun x => β x • v := hc.smul_right (f' := fun _ => v)
  have h3 : MemLp (fun x => β x • v) 2 (volume : Measure ℝ) := h1.memLp_of_hasCompactSupport h2
  exact ⟨h3.toLp _, h3.coeFn_toLp⟩

private theorem orth_zero (d : ℕ) (U : Set ℝ) (hU : IsOpen U) (w : L (Eu d))
    (hw : ∀ (β : ℝ → ℂ) (v : Eu d) (u : L (Eu d)), Continuous β → HasCompactSupport β → (∀ x, x ∉ U → β x = 0) →
      (∀ᵐ x : ℝ, u x = β x • v) → inner ℂ u w = 0) :
    ∀ᵐ x : ℝ, x ∈ U → w x = 0 := by
  have hli : LocallyIntegrable (fun x => w x) (volume : Measure ℝ) :=
    (Lp.memLp w).locallyIntegrable (by norm_num)
  refine hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hli.locallyIntegrableOn U) ?_
  intro g hg hc hs
  have hint : Integrable (fun x => g x • w x) (volume : Measure ℝ) :=
    hli.integrable_smul_left_of_hasCompactSupport hg.continuous hc
  refine ext_inner_left ℂ fun v => ?_
  rw [inner_zero_right, ← integral_inner hint]
  have hβ : Continuous fun x => (g x : ℂ) := Complex.continuous_ofReal.comp hg.continuous
  have hβc : HasCompactSupport fun x => (g x : ℂ) := hc.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  obtain ⟨u, hu⟩ := ex_rep d _ v hβ hβc
  have h0 := hw _ v u hβ hβc (fun x hx => by
    have : g x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hs h)
    simp [this]) hu
  rw [L2.inner_def] at h0
  rw [← h0]
  refine integral_congr_ae ?_
  filter_upwards [hu] with x hx
  rw [hx, inner_smul_left, Complex.conj_ofReal, ← Complex.coe_smul, inner_smul_right]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.denseCc :
    ∀ (d : ℕ), Dense ((Submodule.span ℂ {u : L (Eu d) | ∃ (β : ℝ → ℂ) (v : Eu d), Continuous β ∧ HasCompactSupport β ∧ ∀ᵐ x : ℝ, u x = β x • v} :
        Submodule ℂ (L (Eu d))) : Set (L (Eu d))) ∧
      (∀ (β : ℝ → ℂ) (v : Eu d), Continuous β → HasCompactSupport β → ∃ u : L (Eu d), ∀ᵐ x : ℝ, u x = β x • v) ∧
      ∀ (s : ℝ) (u : L (Eu d)), (∀ᵐ x : ℝ, x ≤ s → u x = 0) → u ∈ closure ((Submodule.span ℂ {u : L (Eu d) | ∃ (β : ℝ → ℂ) (v : Eu d),
        Continuous β ∧ HasCompactSupport β ∧ (∀ x, x ≤ s → β x = 0) ∧ ∀ᵐ x : ℝ, u x = β x • v} : Submodule ℂ (L (Eu d))) : Set (L (Eu d))) := by
  intro d
  refine ⟨?_, ex_rep d, ?_⟩
  · rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff, eq_bot_iff]
    intro w hw
    have h := orth_zero d univ isOpen_univ w fun β v u h1 h2 _ h4 =>
      (Submodule.mem_orthogonal _ _).1 hw u (Submodule.subset_span ⟨β, v, h1, h2, h4⟩)
    rw [Submodule.mem_bot]
    refine Lp.ext ?_
    filter_upwards [h, Lp.coeFn_zero (Eu d) 2 (volume : Measure ℝ)] with x hx h0
    rw [hx (mem_univ x), h0]
    rfl
  · intro s u hu
    rw [← Submodule.topologicalClosure_coe, ← Submodule.orthogonal_orthogonal_eq_closure, SetLike.mem_coe,
      Submodule.mem_orthogonal]
    intro w hw
    have h := orth_zero d (Ioi s) isOpen_Ioi w fun β v u h1 h2 h3 h4 =>
      (Submodule.mem_orthogonal _ _).1 hw u (Submodule.subset_span
        ⟨β, v, h1, h2, fun x hx => h3 x (fun h => not_lt.2 hx h), h4⟩)
    rw [L2.inner_def]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [h, hu] with x h1 h2
    rcases le_or_gt x s with hx | hx
    · simp [h2 hx]
    · simp [h1 hx]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.TensInterp
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem tens_interp {X : Type} (E : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ E] :
    ∃ (a : ℕ) (φ : Fin a → X → ℂ) (x : Fin a → X), (∀ i, φ i ∈ E) ∧
      ∀ f ∈ E, ∀ u, f u = ∑ i, f (x i) * φ i u := by
  classical
  let ev : X → Module.Dual ℂ E := fun u => (LinearMap.proj u).comp E.subtype
  have hspan : Submodule.span ℂ (Set.range ev) = ⊤ := by
    apply Submodule.span_eq_top_of_ne_zero
    intro z hz
    by_contra h
    apply hz
    ext u
    by_contra hu
    exact h ⟨ev u, ⟨u, rfl⟩, hu⟩
  obtain ⟨κ, c, -, hc, hli⟩ := exists_linearIndependent' ℂ ev
  haveI : Finite κ := hli.finite
  obtain ⟨a, ⟨e⟩⟩ := Finite.exists_equiv_fin κ
  let b0 : Module.Basis κ ℂ (Module.Dual ℂ E) := Module.Basis.mk hli (by rw [hc, hspan])
  let b : Module.Basis (Fin a) ℂ (Module.Dual ℂ E) := b0.reindex e
  have hb : ∀ i, b i = ev (c (e.symm i)) := by
    intro i
    simp [b, b0]
  refine ⟨a, fun i => ((Module.evalEquiv ℂ E).symm (b.coord i) : E), fun i => c (e.symm i),
    fun i => Subtype.property _, ?_⟩
  intro f hf u
  have h1 := b.sum_repr (ev u)
  have h2 := congrArg (fun l : Module.Dual ℂ E => l ⟨f, hf⟩) h1
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hb] at h2
  have h3 : ∀ i, (((Module.evalEquiv ℂ E).symm (b.coord i) : E) : X → ℂ) u = b.repr (ev u) i := by
    intro i
    have : ev u ((Module.evalEquiv ℂ E).symm (b.coord i)) = b.coord i (ev u) :=
      Module.apply_evalEquiv_symm_apply ℂ E _ _
    exact this
  change ev u ⟨f, hf⟩ = _
  rw [← h2]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← h3, mul_comm]
  rfl

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.tens :
    ∀ {X Y : Type} (E₁ : Submodule ℂ (X → ℂ)) (E₂ : Submodule ℂ (Y → ℂ)) [FiniteDimensional ℂ E₁] [FiniteDimensional ℂ E₂],
      ∃ (a b : ℕ) (φ : Fin a → X → ℂ) (ψ : Fin b → Y → ℂ) (x : Fin a → Fin a → X) (y : Fin b → Fin b → Y) (s : Fin a → Fin a → ℂ) (t : Fin b → Fin b → ℂ),
        (∀ i, φ i ∈ E₁) ∧ (∀ j, ψ j ∈ E₂) ∧ ∀ Φ : X → Y → ℂ, (∀ v, (fun u => Φ u v) ∈ E₁) → (∀ u, Φ u ∈ E₂) →
          ∀ u v, Φ u v = ∑ i, ∑ j, (∑ p, ∑ q, s i p * t j q * Φ (x i p) (y j q)) * φ i u * ψ j v := by
  intro X Y E₁ E₂ _ _
  obtain ⟨a, φ, x, hφ, hx⟩ := tens_interp E₁
  obtain ⟨b, ψ, y, hψ, hy⟩ := tens_interp E₂
  refine ⟨a, b, φ, ψ, fun _ p => x p, fun _ q => y q, fun i p => if p = i then 1 else 0,
    fun j q => if q = j then 1 else 0, hφ, hψ, ?_⟩
  intro Φ h1 h2 u v
  have hs : ∀ i j, (∑ p, ∑ q, (if p = i then (1 : ℂ) else 0) * (if q = j then (1 : ℂ) else 0) *
      Φ (x p) (y q)) = Φ (x i) (y j) := by
    intro i j
    rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
    · simp
    · intro q _ hq; simp [hq]
    · simp
    · intro p _ hp; simp [hp]
    · simp
  simp only [hs]
  rw [hx _ (h1 v) u]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hy _ (h2 (x i)) v, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.SubDet
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem row_two {K : Type} [Field K] {n : ℕ} {w : InfinitePlace K} {k : GL (Fin n) w.Completion}
    (hk : k ∈ archCompact w) (i : Fin n) {a b : Fin n} (hab : a ≠ b) : ‖k i a‖ ^ 2 + ‖k i b‖ ^ 2 ≤ 1 := by
  classical
  have h := mem_archCompact.1 hk (Pi.single i 1)
  rw [Matrix.single_one_vecMul] at h
  have h1 : euclidNorm (Pi.single i (1 : w.Completion)) = 1 := by
    rw [euclidNorm, Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (by simp)]
    simp only [Pi.single_eq_same, norm_one, one_pow, Real.sqrt_one]
  rw [h1, euclidNorm, Real.sqrt_eq_one] at h
  rw [← h, ← Finset.sum_pair (f := fun j => ‖k i j‖ ^ 2) hab]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => sq_nonneg _

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.subDet :
    ∀ {K : Type} [Field K] [NumberField K] (n : ℕ) (k : AdelicGLn.AdelicGL K n), k ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K n)) → ∀ (r c : Fin 2 → Fin n), Function.Injective r → Function.Injective c →
      (∀ w : InfinitePlace K, ‖(((k : Matrix (Fin n) (Fin n) 𝔸[K]).submatrix r c).det).1 w‖ ≤ 1) ∧
      (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), ‖(((k : Matrix (Fin n) (Fin n) 𝔸[K]).submatrix r c).det).2 v‖ ≤ 1) ∧
      ∀ m : AdelicGLn.AdelicGL K 2, (m : Matrix (Fin 2) (Fin 2) 𝔸[K]) = (k : Matrix (Fin n) (Fin n) 𝔸[K]).submatrix r c → (detModule K 2 m).1 ≤ 1 := by
  intro K _ _ n k hk r c _ hc
  have hc01 : c 0 ≠ c 1 := fun h => absurd (hc h) (by decide)
  have H1 : ∀ w : InfinitePlace K, ‖(((k : Matrix (Fin n) (Fin n) 𝔸[K]).submatrix r c).det).1 w‖ ≤ 1 := by
    intro w
    have h0 := row_two ((mem_maxCompact.1 hk).1 w) (r 0) hc01
    have h1 := row_two ((mem_maxCompact.1 hk).1 w) (r 1) hc01
    have e : (((k : Matrix (Fin n) (Fin n) 𝔸[K]).submatrix r c).det).1 w =
        infAt w k (r 0) (c 0) * infAt w k (r 1) (c 1) - infAt w k (r 0) (c 1) * infAt w k (r 1) (c 0) := by
      rw [← infEval_apply, Matrix.det_fin_two, map_sub, map_mul, map_mul]
      rfl
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    nlinarith [sq_nonneg (‖infAt w k (r 0) (c 0)‖ - ‖infAt w k (r 1) (c 1)‖),
      sq_nonneg (‖infAt w k (r 0) (c 1)‖ - ‖infAt w k (r 1) (c 0)‖)]
  have H2 : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      ‖(((k : Matrix (Fin n) (Fin n) 𝔸[K]).submatrix r c).det).2 v‖ ≤ 1 := by
    intro v
    have hv := (mem_maxCompact.1 hk).2 v
    rw [GLnLocal.mem_integralGL_iff] at hv
    simp only [GroundTheory.Global.mem_valuationInteger_iff] at hv
    have e : (((k : Matrix (Fin n) (Fin n) 𝔸[K]).submatrix r c).det).2 v =
        finAt v k (r 0) (c 0) * finAt v k (r 1) (c 1) - finAt v k (r 0) (c 1) * finAt v k (r 1) (c 0) := by
      rw [← finEval_apply, Matrix.det_fin_two, map_sub, map_mul, map_mul]
      rfl
    rw [e]
    exact norm_le_one_of_mem v (sub_mem (mul_mem (hv.1 _ _) (hv.1 _ _)) (mul_mem (hv.1 _ _) (hv.1 _ _)))
  refine ⟨H1, H2, fun m hm => ?_⟩
  rw [← hm] at H1 H2
  change (GroundTheory.Global.IdeleGroup.ideleModule K (AdelicGLn.det K 2 m) : ℝ) ≤ 1
  rw [GroundTheory.Global.IdeleGroup.ideleModule_eq]
  refine mul_le_one₀ (Finset.prod_le_one₀ (fun _ _ => by positivity)
    fun w _ => pow_le_one₀ (norm_nonneg _) (H1 w)) (finprod_nonneg fun _ => norm_nonneg _) ?_
  exact finprod_induction (fun x : ℝ => 0 ≤ x ∧ x ≤ 1) ⟨zero_le_one, le_rfl⟩
    (fun x y hx hy => ⟨mul_nonneg hx.1 hy.1, mul_le_one₀ hx.2 hy.1 hy.2⟩)
    (fun v => ⟨norm_nonneg _, H2 v⟩) |>.2
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.PluckOne
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem pluck_cb {F : Type} [Field F] (A B : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F)
    (i i' p q : Fin (2 + 2)) :
    (A * B) i p * (A * B) i' q - (A * B) i q * (A * B) i' p =
      ∑ k, ∑ l, (A i k * A i' l - A i l * A i' k) * (B k p * B l q) := by
  simp only [Matrix.mul_apply, Fin.sum_univ_add, Fin.sum_univ_two]
  ring

private theorem pluck_det {F : Type} [Field F] (A : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F)
    (k l : Fin (2 + 2)) :
    (A.submatrix (Fin.natAdd 2) ![k, l]).det =
      A (Fin.natAdd 2 0) k * A (Fin.natAdd 2 1) l - A (Fin.natAdd 2 0) l * A (Fin.natAdd 2 1) k := by
  rw [Matrix.det_fin_two]
  simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one]

private theorem pluck_one {F : Type} [Field F] (γ : GL (Fin (2 + 2)) F) :
    ∃ c : Fin 2 → Fin (2 + 2), Function.Injective c ∧ ((γ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F).submatrix (Fin.natAdd 2) c).det ≠ 0 := by
  by_contra h
  push Not at h
  have hz : ∀ k l : Fin (2 + 2), (γ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F) (Fin.natAdd 2 0) k * (γ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F) (Fin.natAdd 2 1) l -
      (γ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F) (Fin.natAdd 2 0) l * (γ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F) (Fin.natAdd 2 1) k = 0 := by
    intro k l
    by_cases hkl : k = l
    · subst hkl; ring
    · rw [← pluck_det]
      apply h
      intro x y hxy
      fin_cases x <;> fin_cases y <;> simp_all [eq_comm]
  have := pluck_cb (γ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F) ((γ⁻¹ : GL (Fin (2 + 2)) F) : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F)
    (Fin.natAdd 2 0) (Fin.natAdd 2 1) (Fin.natAdd 2 0) (Fin.natAdd 2 1)
  rw [Units.mul_inv] at this
  simp only [hz, zero_mul, Finset.sum_const_zero] at this
  have hne : (Fin.natAdd 2 (0 : Fin 2) : Fin (2 + 2)) ≠ Fin.natAdd 2 1 := by decide
  rw [Matrix.one_apply_eq, Matrix.one_apply_eq, Matrix.one_apply_ne hne] at this
  simp at this

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.pluck :
    ∀ {F : Type} [Field F] (γ γ' : GL (Fin (2 + 2)) F),
      (∃ c : Fin 2 → Fin (2 + 2), Function.Injective c ∧ ((γ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F).submatrix (Fin.natAdd 2) c).det ≠ 0) ∧
      ∀ a : F, (∀ c : Fin 2 → Fin (2 + 2), ((γ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F).submatrix (Fin.natAdd 2) c).det =
          a * ((γ' : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F).submatrix (Fin.natAdd 2) c).det) →
        ∀ i j : Fin (2 + 2), 2 ≤ (i : ℕ) → (j : ℕ) < 2 → ((γ * γ'⁻¹ : GL (Fin (2 + 2)) F) : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F) i j = 0 := by
  intro F _ γ γ'
  refine ⟨pluck_one γ, ?_⟩
  intro a ha i j hi hj
  have ha0 : a ≠ 0 := by
    rintro rfl
    obtain ⟨c, -, hc⟩ := pluck_one γ
    exact hc (by rw [ha, zero_mul])
  rw [Units.val_mul]
  set A : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F := ↑γ with hA
  set A' : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F := ↑γ' with hA'
  set B : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F := ↑(γ'⁻¹) with hB
  have h1 : A' * B = 1 := Units.mul_inv γ'
  set r : Fin (2 + 2) := Fin.natAdd 2 (0 : Fin 2) with hr
  set s : Fin (2 + 2) := Fin.natAdd 2 (1 : Fin 2) with hs
  have key : ∀ p q, (A * B) r p * (A * B) s q - (A * B) r q * (A * B) s p =
      a * ((1 : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F) r p * (1 : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F) s q -
        (1 : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F) r q * (1 : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F) s p) := by
    intro p q
    rw [← h1, pluck_cb, pluck_cb, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    have := ha ![k, l]
    rw [pluck_det, pluck_det] at this
    rw [hr, hs, this, mul_assoc]
  have hrs : r ≠ s := by rw [hr, hs]; decide
  have hrv : (r : ℕ) = 2 := rfl
  have hsv : (s : ℕ) = 3 := rfl
  have hrj : r ≠ j := by intro h; rw [h] at hrv; omega
  have hsj : s ≠ j := by intro h; rw [h] at hsv; omega
  have k1 := key j r
  have k2 := key j s
  have k3 := key r s
  rw [Matrix.one_apply_ne hrj, Matrix.one_apply_ne hsj] at k1 k2
  rw [Matrix.one_apply_eq, Matrix.one_apply_eq, Matrix.one_apply_ne hrs] at k3
  have hi' : i = r ∨ i = s := by
    have := i.isLt
    rcases (by omega : (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h | h
    · left; exact Fin.ext (by omega)
    · right; exact Fin.ext (by omega)
  apply mul_left_cancel₀ ha0
  rcases hi' with h | h
  · rw [h]
    linear_combination (-(A * B) r j) * k3 + (A * B) r r * k2 - (A * B) r s * k1
  · rw [h]
    linear_combination (-(A * B) s j) * k3 + (A * B) s r * k2 - (A * B) s s * k1
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.CtClosed
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private def ctKer {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (r : ℕ) :
    Submodule ℂ (L2 μ) where
  carrier := {w | constantTermL2 μ r w =ᵐ[μ] 0}
  zero_mem' := by
    change constantTermL2 μ r 0 =ᵐ[μ] 0
    filter_upwards [ae_constantTermL2_sub μ r 0 0] with y hy
    rw [sub_self, sub_self] at hy
    exact hy
  add_mem' := fun {φ ψ} hφ hψ => by
    change constantTermL2 μ r (φ + ψ) =ᵐ[μ] 0
    have h1 : constantTermL2 μ r φ =ᵐ[μ] 0 := hφ
    have h2 : constantTermL2 μ r ψ =ᵐ[μ] 0 := hψ
    filter_upwards [ae_constantTermL2_add μ r φ ψ, h1, h2] with y e1 e2 e3
    rw [e1, e2, e3]
    simp
  smul_mem' := fun c φ hφ => by
    change constantTermL2 μ r (c • φ) =ᵐ[μ] 0
    have h1 : constantTermL2 μ r φ =ᵐ[μ] 0 := hφ
    filter_upwards [ae_constantTermL2_smul μ r c φ, h1] with y e1 e2
    rw [e1, e2]
    simp

private theorem ctKer_closed {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure]
    (r : ℕ) : IsClosed (ctKer μ r : Set (L2 μ)) := by
  refine isClosed_of_closure_subset fun φ hφ => ?_
  change constantTermL2 μ r φ =ᵐ[μ] 0
  refine ae_of_forall_isCompact μ fun S hS => ?_
  obtain ⟨C, hC, hCφ⟩ := exists_lintegral_constantTermL2_sq_le μ r hS
  set I := ∫⁻ y in S, ‖constantTermL2 μ r φ y‖ₑ ∂μ
  have hle : ∀ ε : ℝ, 0 < ε → I ^ 2 ≤ C * ENNReal.ofReal ε ^ 2 := by
    intro ε hε
    obtain ⟨ψ, hψ, hdist⟩ := Metric.mem_closure_iff.1 hφ ε hε
    have hψ' : constantTermL2 μ r ψ =ᵐ[μ] 0 := hψ
    have hI : I = ∫⁻ y in S, ‖constantTermL2 μ r (φ - ψ) y‖ₑ ∂μ := by
      refine lintegral_congr_ae (ae_restrict_of_ae ?_)
      filter_upwards [ae_constantTermL2_sub μ r φ ψ, hψ'] with y h1 h2
      rw [h1, h2, Pi.zero_apply, sub_zero]
    rw [hI]
    refine (hCφ (φ - ψ)).trans ?_
    gcongr
    rw [← ofReal_norm, ← dist_eq_norm]
    exact ENNReal.ofReal_le_ofReal hdist.le
  have hI0 : I ^ 2 = 0 := by
    refine le_antisymm ?_ zero_le
    have ht : Tendsto (fun ε : ℝ => C * ENNReal.ofReal ε ^ 2) (𝓝[>] 0) (𝓝 0) := by
      have h1 : Tendsto (fun ε : ℝ => ENNReal.ofReal ε ^ 2) (𝓝[>] 0) (𝓝 0) := by
        have := (((ENNReal.continuous_pow 2).comp ENNReal.continuous_ofReal).tendsto 0).mono_left
          (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
        simpa [Function.comp_def] using this
      simpa using ENNReal.Tendsto.const_mul h1 (Or.inr hC)
    exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun ε hε => hle ε hε)
  have hI' : I = 0 := pow_eq_zero_iff two_ne_zero |>.1 hI0
  have hm : AEMeasurable (fun y => ‖constantTermL2 μ r φ y‖ₑ) (μ.restrict S) :=
    (stronglyMeasurable_ctFun r (Lp.stronglyMeasurable φ)).measurable.eNorm.aemeasurable
  filter_upwards [(lintegral_eq_zero_iff' hm).1 hI'] with y hy
  simpa using hy

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.ctClosed :
    ∀ {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (r : ℕ), ∃ S : Submodule ℂ (L2 μ), IsClosed (S : Set (L2 μ)) ∧
      ∀ w, w ∈ S ↔ constantTermL2 μ r w =ᵐ[μ] 0 := by
  intro K _ _ n μ _ r
  exact ⟨ctKer μ r, ctKer_closed μ r, fun _ => Iff.rfl⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.SumField
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem tsum_fin {α : Type} (f : α → ℝ≥0∞) (k : ℕ) :
    ∑' x : Fin k → α, ∏ i, f (x i) = (∑' a, f a) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← (Fin.consEquiv fun _ : Fin (k + 1) => α).tsum_eq, ENNReal.tsum_prod', pow_succ', ← ih,
      ← ENNReal.tsum_mul_right]
    refine tsum_congr fun a => ?_
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr fun x => ?_
    simp [Fin.prod_univ_succ, Fin.consEquiv]

private theorem tsum_pi {α ι : Type} [Fintype ι] (f : α → ℝ≥0∞) :
    ∑' x : ι → α, ∏ i, f (x i) = (∑' a, f a) ^ Fintype.card ι := by
  rw [← tsum_fin, ← (Equiv.arrowCongr (Fintype.equivFin ι) (Equiv.refl α)).tsum_eq]
  refine tsum_congr fun x => ?_
  rw [← (Fintype.equivFin ι).prod_comp]
  simp

private theorem step {α β ι : Type} [Fintype ι] (e : β → ι → α) (he : Function.Injective e) (f : α → ℝ)
    (hf : ∀ a, 0 < f a) (hs : ∑' a, ENNReal.ofReal (f a)⁻¹ ≠ ⊤) (H : β → ℝ) (hH : ∀ b, 0 < H b) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ b i, f (e b i) ≤ C * H b) : ∑' b, ENNReal.ofReal (H b ^ Fintype.card ι)⁻¹ ≠ ⊤ := by
  have h1 : ∀ b, ENNReal.ofReal (H b ^ Fintype.card ι)⁻¹ ≤
      ENNReal.ofReal (C ^ Fintype.card ι) * ∏ i, ENNReal.ofReal (f (e b i))⁻¹ := by
    intro b
    rw [← ENNReal.ofReal_prod_of_nonneg fun i _ => (inv_pos.2 (hf _)).le, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← inv_pow, ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun _ _ => (inv_pos.2 (hH b)).le) fun i _ => ?_
    rw [← div_eq_mul_inv, le_div_iff₀ (hf _), inv_mul_le_iff₀ (hH b), mul_comm]
    exact h b i
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum h1)
  rw [ENNReal.tsum_mul_left]
  refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_top_of_le_ne_top ?_
    (ENNReal.tsum_comp_le_tsum_of_injective he fun x : ι → α => ∏ i, ENNReal.ofReal (f (x i))⁻¹))
  rw [tsum_pi fun a => ENNReal.ofReal (f a)⁻¹]
  exact ENNReal.pow_ne_top hs

private theorem sum_int : ∑' a : ℤ, ENNReal.ofReal (max 1 ((a : ℝ) ^ 2))⁻¹ ≠ ⊤ := by
  refine Summable.tsum_ofReal_ne_top ?_
  have h : Summable fun a : ℤ => 1 / (a : ℝ) ^ 2 := Real.summable_one_div_int_pow.2 one_lt_two
  refine h.congr_cofinite ?_
  refine (Set.finite_singleton (0 : ℤ)).subset fun a ha => ?_
  by_contra h0
  refine ha ?_
  have h1 : (1 : ℤ) ≤ a ^ 2 := (one_le_sq_iff_one_le_abs a).2 (Int.one_le_abs h0)
  have h2 : (1 : ℝ) ≤ (a : ℝ) ^ 2 := by exact_mod_cast h1
  show 1 / (a : ℝ) ^ 2 = (max 1 ((a : ℝ) ^ 2))⁻¹
  rw [max_eq_right h2, one_div]

private theorem inf_le {K : Type} [Field K] [NumberField K] (x : K) (w : InfinitePlace K) :
    w x ≤ Height.mulHeight₁ x := by
  classical
  rw [mulHeight₁_eq]
  have h1 : (1 : ℝ) ≤ ∏ᶠ v : FinitePlace K, max (v x) 1 :=
    finprod_induction (fun x : ℝ => 1 ≤ x) le_rfl (fun _ _ hx hy => one_le_mul_of_one_le_of_one_le hx hy)
      fun _ => le_max_right _ _
  have h2 : max (w x) 1 ^ w.mult ≤ ∏ v : InfinitePlace K, max (v x) 1 ^ v.mult := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ w)]
    exact le_mul_of_one_le_right (by positivity) (Finset.prod_induction _ (fun x : ℝ => 1 ≤ x)
      (fun _ _ hx hy => one_le_mul_of_one_le_of_one_le hx hy) le_rfl fun _ _ => one_le_pow₀ (le_max_right _ _))
  have h3 : w x ≤ max (w x) 1 ^ w.mult :=
    (le_max_left _ _).trans (le_self_pow₀ (le_max_right _ _) w.mult_ne_zero)
  exact (h3.trans h2).trans (le_mul_of_one_le_right ((apply_nonneg w x).trans (h3.trans h2)) h1)

private theorem sum_field (K : Type) [Field K] [NumberField K] :
    ∃ M : ℕ, ∑' x : K, ENNReal.ofReal (Height.mulHeight₁ x ^ M)⁻¹ ≠ ⊤ := by
  obtain ⟨C, hC, hr⟩ := exists_abs_repr_le K
  choose m hm0 hm hi using fun x : K => exists_nat_le_mulHeight₁ x
  let z : K → 𝓞 K := fun x => ⟨m x * x, hi x⟩
  let e : K → Option (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) → ℤ := fun x o =>
    o.elim (m x) fun i => (RingOfIntegers.basis K).repr (z x) i
  have he : Function.Injective e := by
    intro x y h
    have h1 : m x = m y := Int.natCast_inj.1 (congrFun h none)
    have h2 : z x = z y := (RingOfIntegers.basis K).repr.injective (Finsupp.ext fun i => congrFun h (some i))
    have h3 : (m x : K) * x = m y * y := congrArg Subtype.val h2
    rw [h1] at h3
    exact mul_left_cancel₀ (Nat.cast_ne_zero.2 (hm0 y)) h3
  have := step e he (fun a => max 1 ((a : ℝ) ^ 2)) (fun _ => lt_max_of_lt_left one_pos) sum_int
    (fun x => Height.mulHeight₁ x ^ 4) (fun x => pow_pos (Height.mulHeight₁_pos x) 4)
    (C := (max 1 C) ^ 2) (by positivity) ?_
  · exact ⟨_, by simpa only [← pow_mul] using this⟩
  intro x o
  have hH := Height.one_le_mulHeight₁ x
  have hC1 : 1 ≤ max 1 C := le_max_left _ _
  have hb : |(e x o : ℝ)| ≤ max 1 C * Height.mulHeight₁ x ^ 2 := by
    cases o with
    | none =>
      change |((m x : ℤ) : ℝ)| ≤ _
      rw [Int.cast_natCast, Nat.abs_cast]
      exact ((hm x).trans (le_self_pow₀ hH two_ne_zero)).trans (le_mul_of_one_le_left (by positivity) hC1)
    | some i =>
      refine (hr (z x) i).trans ((mul_le_mul_of_nonneg_left ?_ hC).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)))
      rw [mixedEmbedding.norm_eq_sup'_normAtPlace]
      refine Finset.sup'_le _ _ fun w _ => ?_
      rw [mixedEmbedding.normAtPlace_apply]
      change w ((m x : K) * x) ≤ _
      rw [map_mul, InfinitePlace.map_natCast, sq]
      exact mul_le_mul (hm x) (inf_le x w) (apply_nonneg _ _) (by positivity)
  refine max_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hC1) (one_le_pow₀ hH)) ?_
  calc _ = |(e x o : ℝ)| ^ 2 := (sq_abs _).symm
    _ ≤ (max 1 C * Height.mulHeight₁ x ^ 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hb 2
    _ = _ := by ring

private theorem entry_le {K : Type} [Field K] [NumberField K] {n : ℕ} (γ : GL (Fin n) K) (i j : Fin n) :
    Height.mulHeight₁ (γ.val i j) ≤ AutomorphicForm.height (AdelicGLn.diagonal K n γ) := by
  rw [mulHeight₁_eq, AutomorphicForm.height, ← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]
  have hf : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      max (FinitePlace.equivHeightOneSpectrum.symm v (γ.val i j)) 1 ≤ locHeight (finAt v (AdelicGLn.diagonal K n γ)) :=
    fun v => max_le (norm_apply_le_locHeight (finAt v (AdelicGLn.diagonal K n γ)) i j) (one_le_locHeight _)
  refine mul_le_mul ?_ ?_ (finprod_nonneg fun _ => le_max_of_le_right zero_le_one)
    (zero_le_one.trans (one_le_prod_locHeight _))
  · refine Finset.prod_le_prod₀ (fun _ _ => by positivity) fun w _ => ?_
    refine pow_le_pow_left₀ (by positivity) (max_le ?_ (one_le_locHeight _)) _
    refine le_trans (le_of_eq ?_) (norm_apply_le_locHeight (infAt w (AdelicGLn.diagonal K n γ)) i j)
    rw [infAt_apply, AdelicGLn.diagonal_apply, ← GroundTheory.Global.norm_algebraMap_apply]
    rfl
  · refine finprod_le_finprod₀ ((finite_mulSupport_locHeight_finAt (AdelicGLn.diagonal K n γ)).subset fun v hv h1 => hv ?_)
      (fun _ => le_max_of_le_right zero_le_one) (finite_mulSupport_locHeight_finAt _) hf
    exact le_antisymm ((hf v).trans_eq h1) (le_max_right _ _)

private theorem sum_gam (K : Type) [Field K] [NumberField K] (n : ℕ) : ∃ M : ℕ,
    ∑' γ : Gam K n, ENNReal.ofReal (AutomorphicForm.height ((γ : G1 K n) : AdelicGLn.AdelicGL K n) ^ M)⁻¹ ≠ ⊤ := by
  obtain ⟨M, hM⟩ := sum_field K
  have hγ : ∀ γ : Gam K n, ∃ δ : GL (Fin n) K, AdelicGLn.diagonal K n δ = ((γ : G1 K n) : AdelicGLn.AdelicGL K n) :=
    fun γ => γ.2
  choose δ hδ using hγ
  have := step (fun (γ : Gam K n) (p : Fin n × Fin n) => (δ γ).val p.1 p.2) ?_ (fun x => Height.mulHeight₁ x ^ M)
    (fun x => pow_pos (Height.mulHeight₁_pos x) M) hM
    (fun γ => AutomorphicForm.height ((γ : G1 K n) : AdelicGLn.AdelicGL K n) ^ M) (fun γ => pow_pos (height_pos _) M)
    zero_le_one ?_
  · exact ⟨_, by simpa only [← pow_mul] using this⟩
  · intro γ γ' h
    have : δ γ = δ γ' := Units.ext (Matrix.ext fun i j => congrFun h (i, j))
    exact Subtype.ext (Subtype.ext (by rw [← hδ, ← hδ, this]))
  · intro γ p
    rw [one_mul, ← hδ]
    exact pow_le_pow_left₀ (Height.mulHeight₁_pos _).le (entry_le _ _ _) M

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.sumHt :
    ∀ {K : Type} [Field K] [NumberField K] (n : ℕ), ∃ (N : ℕ) (C : ℝ≥0∞), C ≠ ⊤ ∧ ∀ g : G1 K n,
      ∑' γ : Gam K n, ENNReal.ofReal ((AutomorphicForm.height (((γ : G1 K n) * g : G1 K n) : AdelicGLn.AdelicGL K n) ^ N)⁻¹) ≤ C := by
  intro K _ _ n
  obtain ⟨M, hM⟩ := sum_gam K n
  have hc : 0 < heightConst K n := one_pos.trans_le one_le_heightConst
  refine ⟨2 * M, _, ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := (heightConst K n * 2) ^ M)) hM, fun g => ?_⟩
  set F : Gam K n → ℝ := fun γ => AutomorphicForm.height (((γ : G1 K n) * g : G1 K n) : AdelicGLn.AdelicGL K n) with hF
  have hF1 : ∀ γ, 1 ≤ F γ := fun γ => one_le_height _
  have hb : BddBelow (Set.range F) := ⟨1, Set.forall_mem_range.2 hF1⟩
  have hi : 1 ≤ ⨅ γ, F γ := le_ciInf hF1
  obtain ⟨γ₀, h₀⟩ := exists_lt_of_ciInf_lt (f := F) (b := 2 * ⨅ γ, F γ) (by linarith)
  rw [← (Equiv.mulRight γ₀⁻¹).tsum_eq fun γ : Gam K n =>
    ENNReal.ofReal (AutomorphicForm.height ((γ : G1 K n) : AdelicGLn.AdelicGL K n) ^ M)⁻¹, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun γ => ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  change (F γ ^ (2 * M))⁻¹ ≤ _
  have hp : 0 < F γ := one_pos.trans_le (hF1 γ)
  rw [pow_mul, ← inv_pow _ M, ← inv_pow _ M, ← mul_pow]
  refine pow_le_pow_left₀ (by positivity) ?_ M
  rw [← div_eq_mul_inv, le_div_iff₀ (height_pos _), inv_mul_le_iff₀ (by positivity)]
  have e : (((Equiv.mulRight γ₀⁻¹ γ : Gam K n) : G1 K n) : AdelicGLn.AdelicGL K n) =
      (((γ : G1 K n) * g : G1 K n) : AdelicGLn.AdelicGL K n) *
        ((((γ₀ : G1 K n) * g : G1 K n) : AdelicGLn.AdelicGL K n))⁻¹ := by
    simp [mul_assoc]
  rw [e]
  refine (height_mul_le _ _).trans ?_
  rw [height_inv]
  have h2 : F γ₀ ≤ 2 * F γ := h₀.le.trans (by linarith [ciInf_le hb γ])
  calc heightConst K n * F γ * F γ₀ ≤ heightConst K n * F γ * (2 * F γ) := by gcongr
    _ = _ := by ring
end
