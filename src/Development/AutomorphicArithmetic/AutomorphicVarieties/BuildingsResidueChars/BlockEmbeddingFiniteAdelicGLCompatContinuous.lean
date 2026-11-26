module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BlockEmbeddingFiniteAdelicGLCompatContinuous
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem continuous_emb' {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {a n : ℕ}
    (e : Fin a ↪ Fin n) : Continuous (emb e : GL (Fin a) R → GL (Fin n) R) := by
  refine Continuous.units_map (embM (R := R) e) ?_
  change Continuous fun X : Matrix (Fin a) (Fin a) R => 1 + inc e R * (X - 1) * (inc e R)ᵀ
  exact continuous_const.add
    ((continuous_const.matrix_mul (continuous_id.sub continuous_const)).matrix_mul continuous_const)

private theorem prodEquiv_eq (K : Type) [Field K] [NumberField K] (n : ℕ) (g : AdelicGLn.AdelicGL K n) :
    AdelicGLn.prodEquiv K n g =
      (Matrix.GeneralLinearGroup.map (RingHom.fst (InfiniteAdeleRing K) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) g,
        Matrix.GeneralLinearGroup.map (RingHom.snd (InfiniteAdeleRing K) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) g) := by
  refine Prod.ext ?_ ?_
  · ext i j : 2
    exact AdelicGLn.prodEquiv_apply_fst K n g i j
  · ext i j : 2
    exact AdelicGLn.prodEquiv_apply_snd K n g i j

private theorem prodEquiv_emb (K : Type) [Field K] [NumberField K] {a n : ℕ} (e : Fin a ↪ Fin n)
    (g : AdelicGLn.AdelicGL K a) :
    AdelicGLn.prodEquiv K n (emb e g) =
      (emb e (AdelicGLn.prodEquiv K a g).1, emb e (AdelicGLn.prodEquiv K a g).2) := by
  rw [prodEquiv_eq, prodEquiv_eq]
  exact Prod.ext
    (emb_map e (RingHom.fst (InfiniteAdeleRing K) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) g)
    (emb_map e (RingHom.snd (InfiniteAdeleRing K) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) g)

theorem UpperTheory.blockEmbedding_finiteAdelicGL_compat_continuous :
    ∀ (K : Type) [Field K] [NumberField K] (a n : ℕ) (e : Fin a ↪ Fin n), (∀ y, emb e (finEmb K a y) = finEmb K n (emb e y)) ∧ (∀ γ, emb e (AdelicGLn.diagonal K a γ) = AdelicGLn.diagonal K n (emb e γ)) ∧ Continuous (emb e : AdelicGLn.FiniteAdelicGL K a → AdelicGLn.FiniteAdelicGL K n) := by
  intro K _ _ a n e
  refine ⟨fun y => ?_, fun γ => ?_, continuous_emb' e⟩
  · apply (AdelicGLn.prodEquiv K n).injective
    rw [prodEquiv_emb, prodEquiv_finEmb, prodEquiv_finEmb, map_one]
  · exact (emb_map e (algebraMap K (AdeleRing (𝓞 K) K)) γ).symm
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ConstantTermUnipotentLeftInvariant
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.constantTerm_unipotent_left_invariant :
    ∀ (K : Type) [Field K] [NumberField K] (n r : ℕ) (φ : AdelicGLn.AdelicGL K n → ℂ),
      IsLeftInvariant φ → ∀ (X : UPos n r → AdeleRing (𝓞 K) K) g,
        constantTerm (r := r) φ (unipGL X * g) = constantTerm (r := r) φ g := by
  intro K _ _ n r φ hφ X g
  have hfd := isAddFundamentalDomain_unipFundamentalDomain (K := K) (n := n) (r := r)
  have hfd' := hfd.vadd_of_comm X
  rw [constantTerm_eq_setIntegral hφ hfd, constantTerm_eq_setIntegral hφ hfd' g, ← Set.image_vadd]
  simp only [vadd_eq_add]
  rw [(measurePreserving_add_left (unipMeasure K n r) X).setIntegral_image_emb
      (MeasurableEquiv.addLeft X).measurableEmbedding]
  refine integral_congr_ae (Filter.Eventually.of_forall fun Y => ?_)
  show φ (unipGL Y * (unipGL X * g)) = φ (unipGL (X + Y) * g)
  rw [add_comm X Y, unipGL_add, mul_assoc]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ContinuousConstantTerm
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem cont_setIntegral {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [MeasurableSpace Y]
    (μ : Measure Y) (f : X → Y → ℂ) (hf : Continuous f.uncurry) {s C : Set Y} (hs : MeasurableSet s)
    (hC : IsCompact C) (hsC : s ⊆ C) (hμ : μ s < ⊤) (hi : ∀ x, IntegrableOn (f x) s μ) :
    Continuous fun x => ∫ y in s, f x y ∂μ := by
  refine continuous_iff_continuousAt.2 fun x₀ => Metric.tendsto_nhds.2 fun ε hε => ?_
  have hm : 0 ≤ (μ s).toReal := ENNReal.toReal_nonneg
  have hδ : 0 < ε / ((μ s).toReal + 1) := div_pos hε (by linarith)
  have hc : Continuous fun z : X × Y => f z.1 z.2 - f x₀ z.2 :=
    hf.sub (hf.comp (Continuous.prodMk continuous_const continuous_snd))
  have htube : ∀ᶠ x in nhds x₀, ∀ y ∈ C, ‖f x y - f x₀ y‖ < ε / ((μ s).toReal + 1) := by
    apply hC.eventually_forall_of_forall_eventually
    intro y _
    exact (hc.norm.tendsto (x₀, y)).eventually (gt_mem_nhds (by simpa using hδ))
  filter_upwards [htube] with x hx
  rw [dist_eq_norm, ← integral_sub (hi x) (hi x₀)]
  calc ‖∫ y in s, (f x y - f x₀ y) ∂μ‖ ≤ ε / ((μ s).toReal + 1) * (μ s).toReal :=
        norm_setIntegral_le_of_norm_le_const hμ (fun y hy => (hx y (hsC hy)).le)
    _ < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith

theorem UpperTheory.continuous_constantTerm :
    ∀ (K : Type) [Field K] [NumberField K] (n r : ℕ) (φ : AdelicGLn.AdelicGL K n → ℂ),
      Continuous φ → Continuous (constantTerm (r := r) φ) := by
  intro K _ _ n r φ hφ
  obtain ⟨C, hC, hDC⟩ := exists_isCompact_superset_unipFundamentalDomain (K := K) (n := n) (r := r)
  exact cont_setIntegral (unipMeasure K n r) (fun g X => φ (unipGL X * g))
    (hφ.comp ((continuous_unipGL.comp continuous_snd).mul continuous_fst))
    measurableSet_unipFundamentalDomain hC hDC ((measure_mono hDC).trans_lt hC.measure_lt_top)
    (fun g => integrableOn_constantTerm hφ g)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsOpenLevelNormalizedByIntegralFiniteGL
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem exists_normal_open_level_subgroup {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (H L : Subgroup G) (hHc : IsCompact (H : Set G)) (hHo : IsOpen (H : Set G))
    (hL : IsOpen (L : Set G)) :
    ∃ L' : Subgroup G, IsOpen (L' : Set G) ∧ L' ≤ L ∧ (∀ k ∈ H, ∀ u ∈ L', k⁻¹ * u * k ∈ L') ∧
      ∃ t : Finset G, ∀ k ∈ H, ∃ c ∈ t, c⁻¹ * k ∈ L' := by
  classical
  haveI : CompactSpace H := isCompact_iff_compactSpace.1 hHc
  have hNo : IsOpen ((L.subgroupOf H : Subgroup H) : Set H) := hL.preimage continuous_subtype_val
  haveI : Finite (H ⧸ L.subgroupOf H) := (L.subgroupOf H).quotient_finite_of_isOpen hNo
  haveI : (L.subgroupOf H).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hCo : IsOpen ((L.subgroupOf H).normalCore : Set H) :=
    Subgroup.isOpen_of_isClosed_of_finiteIndex _
      ((L.subgroupOf H).normalCore_isClosed (Subgroup.isClosed_of_isOpen _ hNo))
  refine ⟨(L.subgroupOf H).normalCore.map H.subtype, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.coe_map]
    exact hHo.isOpenMap_subtype_val _ hCo
  · rintro _ ⟨u, hu, rfl⟩
    have := (L.subgroupOf H).normalCore_le hu
    exact this
  · rintro k hk _ ⟨u, hu, rfl⟩
    refine ⟨(⟨k, hk⟩ : H)⁻¹ * u * ⟨k, hk⟩, ?_, by simp⟩
    have := (Subgroup.normalCore_normal (L.subgroupOf H)).conj_mem u hu ((⟨k, hk⟩ : H)⁻¹)
    simpa using this
  · haveI : Finite (H ⧸ (L.subgroupOf H).normalCore) := Subgroup.finite_quotient_of_finiteIndex
    letI := Fintype.ofFinite (H ⧸ (L.subgroupOf H).normalCore)
    refine ⟨Finset.univ.image (fun q : H ⧸ (L.subgroupOf H).normalCore => ((q.out : H) : G)), ?_⟩
    intro k hk
    refine ⟨(((QuotientGroup.mk ⟨k, hk⟩ : H ⧸ (L.subgroupOf H).normalCore).out : H) : G),
      Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
    have := QuotientGroup.eq.1
      (QuotientGroup.out_eq' (QuotientGroup.mk ⟨k, hk⟩ : H ⧸ (L.subgroupOf H).normalCore))
    exact ⟨_, this, by simp⟩

theorem UpperTheory.exists_open_level_normalized_by_integralFiniteGL :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (L : Subgroup (AdelicGLn.FiniteAdelicGL K n)), IsOpen (L : Set (AdelicGLn.FiniteAdelicGL K n)) → ∃ L' : Subgroup (AdelicGLn.FiniteAdelicGL K n), IsOpen (L' : Set (AdelicGLn.FiniteAdelicGL K n)) ∧ L' ≤ L ∧ (∀ k ∈ AdelicGLn.integralFiniteGL K n, ∀ u ∈ L', k⁻¹ * u * k ∈ L') ∧ ∃ t : Finset (AdelicGLn.FiniteAdelicGL K n), ∀ k ∈ AdelicGLn.integralFiniteGL K n, ∃ c ∈ t, c⁻¹ * k ∈ L' := by
  intro K _ _ n L hL
  exact exists_normal_open_level_subgroup _ L (AdelicGLn.isCompact_integralFiniteGL K n)
    (AdelicGLn.isOpen_integralFiniteGL K n) hL
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AlgModBotOfMemAdjoinCommuting
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem adjoin_alg {V : Type} [AddCommGroup V] [Module ℂ V] {R : Type} [CommRing R] [Algebra ℂ R]
    (φ : R →ₐ[ℂ] Module.End ℂ V) (S : Submodule ℂ V) (t : Set R) (ht : ∀ r ∈ t, AlgMod S ⊥ (φ r)) :
    ∀ r ∈ Algebra.adjoin ℂ t, AlgMod S ⊥ (φ r) := by
  let I : Ideal R :=
    { carrier := {r | ∀ x ∈ S, φ r x = 0}
      add_mem' := fun {a b} ha hb x hx => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_add (f := _), LinearMap.add_apply, ha x hx, hb x hx, add_zero]
      zero_mem' := fun x _ => by simp
      smul_mem' := fun c r hr x hx => by
        simp only [Set.mem_setOf_eq] at hr ⊢
        rw [smul_eq_mul, map_mul, Module.End.mul_apply, hr x hx, map_zero] }
  have hint : ∀ r ∈ t, IsIntegral ℂ (Ideal.Quotient.mkₐ ℂ I r) := by
    intro r hr
    obtain ⟨p, hp, hx⟩ := ht r hr
    refine ⟨p, hp, ?_⟩
    rw [← Polynomial.aeval_def, Polynomial.aeval_algHom_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem]
    intro x hxS
    have hx' := hx x hxS
    rw [Polynomial.aeval_algHom_apply, Submodule.mem_bot] at hx'
    exact hx'
  intro r hr
  have h1 : Ideal.Quotient.mkₐ ℂ I r ∈ Algebra.adjoin ℂ (Ideal.Quotient.mkₐ ℂ I '' t) := by
    rw [Algebra.adjoin_image]
    exact ⟨r, hr, rfl⟩
  have h2 : Ideal.Quotient.mkₐ ℂ I r ∈ integralClosure ℂ (R ⧸ I) := by
    refine Algebra.adjoin_le ?_ h1
    rintro _ ⟨r', hr', rfl⟩
    exact hint r' hr'
  obtain ⟨p, hp, hev⟩ := h2
  refine ⟨p, hp, fun x hx => ?_⟩
  rw [← Polynomial.aeval_def, Polynomial.aeval_algHom_apply, Ideal.Quotient.mkₐ_eq_mk,
    Ideal.Quotient.eq_zero_iff_mem] at hev
  rw [Polynomial.aeval_algHom_apply, Submodule.mem_bot]
  exact hev x hx

theorem UpperTheory.algMod_bot_of_mem_adjoin_commuting :
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (S : Submodule ℂ M) (s : Set (Module.End ℂ M)), (∀ x ∈ s, ∀ y ∈ s, x * y = y * x) → (∀ T ∈ s, AlgMod S ⊥ T) → ∀ T ∈ Algebra.adjoin ℂ s, AlgMod S ⊥ T := by
  intro M _ _ S s hcomm hs T hT
  letI : IsMulCommutative (Algebra.adjoin ℂ s) :=
    Algebra.isMulCommutative_adjoin ℂ (fun x hx y hy _ => hcomm x hx y hy)
  open scoped IsMulCommutative in
    have hmem : (⟨T, hT⟩ : Algebra.adjoin ℂ s) ∈
        Algebra.adjoin ℂ (((↑) : Algebra.adjoin ℂ s → Module.End ℂ M) ⁻¹' s) := by
      rw [Algebra.adjoin_adjoin_coe_preimage]
      trivial
    exact adjoin_alg (Algebra.adjoin ℂ s).val S
      (((↑) : Algebra.adjoin ℂ s → Module.End ℂ M) ⁻¹' s)
      (fun r hr => hs r hr) ⟨T, hT⟩ hmem
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HeightBlockEmbeddingLe
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem ent_le {E : Type} [NormedField E] {a n : ℕ} (e : Fin a ↪ Fin n) (g : GL (Fin a) E) {c : ℝ}
    (hc : 1 ≤ c) (h : ∀ i j, ‖g.val i j‖ ≤ c) (i j : Fin n) : ‖(emb e g).val i j‖ ≤ c := by
  have hone : ∀ p q : Fin n, ‖(1 : Matrix (Fin n) (Fin n) E) p q‖ ≤ c := by
    intro p q
    rw [Matrix.one_apply]
    split_ifs <;> simp [hc, zero_le_one.trans hc]
  show ‖((emb e g : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j‖ ≤ c
  rw [coe_emb, Matrix.add_apply]
  by_cases hi : ∃ k, i = e k
  · by_cases hj : ∃ l, j = e l
    · obtain ⟨k, rfl⟩ := hi
      obtain ⟨l, rfl⟩ := hj
      simp only [matrixExtendByZero_apply, Matrix.sub_apply, Matrix.one_apply, e.injective.eq_iff, add_sub_cancel]
      exact h k l
    · push_neg at hj
      rw [matrixExtendByZero_apply_of_outside_col e _ i hj, add_zero]
      exact hone i j
  · push_neg at hi
    rw [extendByZero_apply_eq_zero_of_row_not_mem e _ hi, add_zero]
    exact hone i j

private theorem loc_le {E : Type} [NormedField E] {a n : ℕ} (e : Fin a ↪ Fin n) (g : GL (Fin a) E) :
    locHeight (emb e g) ≤ locHeight g := by
  apply locHeight_le (one_le_locHeight g)
  · exact ent_le e g (one_le_locHeight g) (norm_apply_le_locHeight g)
  · intro i j
    rw [← map_inv]
    exact ent_le e g⁻¹ (one_le_locHeight g) (norm_inv_apply_le_locHeight g) i j

theorem UpperTheory.height_blockEmbedding_le :
    ∀ (K : Type) [Field K] [NumberField K] (a n : ℕ) (e : Fin a ↪ Fin n) (g : AdelicGLn.AdelicGL K a), AutomorphicForm.height (emb e g) ≤ AutomorphicForm.height g := by
  classical
  intro K _ _ a n e g
  have hfin : ∀ v, Reduction.finAt v (emb e g) = emb e (Reduction.finAt v g) := by
    intro v
    show Matrix.GeneralLinearGroup.map (Reduction.finEval v) (emb e g) = _
    rw [emb_map]
    rfl
  have hinf : ∀ w, Reduction.infAt w (emb e g) = emb e (Reduction.infAt w g) := by
    intro w
    show Matrix.GeneralLinearGroup.map (Reduction.infEval w) (emb e g) = _
    rw [emb_map]
    rfl
  unfold AutomorphicForm.height
  simp only [hfin, hinf]
  apply mul_le_mul
  · apply Finset.prod_le_prod₀
    · intro w _
      exact pow_nonneg (locHeight_pos _).le _
    · intro w _
      exact pow_le_pow_left₀ (locHeight_pos _).le (loc_le e _) _
  · have h1 := finite_mulSupport_locHeight_finAt (emb e g)
    have h2 := finite_mulSupport_locHeight_finAt g
    simp only [hfin] at h1
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := h1.toFinset ∪ h2.toFinset)
        (by intro x hx; simp [hx]),
      finprod_eq_prod_of_mulSupport_subset _ (s := h1.toFinset ∪ h2.toFinset)
        (by intro x hx; simp [hx])]
    apply Finset.prod_le_prod₀
    · intro v _
      exact (locHeight_pos _).le
    · intro v _
      exact loc_le e _
  · exact finprod_nonneg fun v => (locHeight_pos _).le
  · exact (zero_lt_one.trans_le (one_le_prod_locHeight g)).le
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GenGlRelationsAndCommuteOfIsLie
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem single_comm {R : Type} [CommRing R] {n : ℕ} (i j k m : Fin n) (x y : R) :
    (Matrix.single i j x * Matrix.single k m y : Matrix (Fin n) (Fin n) R) =
      if j = k then Matrix.single i m (x * y) else 0 := by
  split_ifs with h
  · subst h
    exact Matrix.single_mul_single_same _ _ _ _ _
  · ext a b
    simp only [Matrix.mul_apply, Matrix.single_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun t _ => ?_
    by_cases hj : j = t
    · subst hj
      simp only [Ne.symm h, false_and, if_false, mul_zero]
    · simp [hj]

private theorem unitMap_comm {R : Type} [CommRing R] [Algebra ℝ R] {n : ℕ} {A : Type} [Ring A] [Algebra ℂ A]
    [Algebra ℝ A] [IsScalarTower ℝ ℂ A] (l : Matrix (Fin n) (Fin n) R →ₗ[ℝ] A) (hl : IsLie l) (i j k m : Fin n)
    (a b : ℂ ⊗[ℝ] R) :
    unitMap l i j a * unitMap l k m b - unitMap l k m b * unitMap l i j a =
      (if j = k then unitMap l i m (a * b) else 0) - (if m = i then unitMap l k j (a * b) else 0) := by
  have hmain : ∀ (c d : ℂ) (x y : R),
      unitMap l i j (c ⊗ₜ x) * unitMap l k m (d ⊗ₜ y) - unitMap l k m (d ⊗ₜ y) * unitMap l i j (c ⊗ₜ x) =
        (if j = k then unitMap l i m ((c ⊗ₜ x) * (d ⊗ₜ y)) else 0) -
          (if m = i then unitMap l k j ((c ⊗ₜ x) * (d ⊗ₜ y)) else 0) := by
    intro c d x y
    simp only [unitMap_tmul, Algebra.TensorProduct.tmul_mul_tmul, smul_mul_smul_comm]
    rw [mul_comm d c, ← smul_sub, hl, single_comm, single_comm, mul_comm y x]
    split_ifs <;> simp [map_sub, smul_sub]
  rw [← sub_eq_zero]
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul c x =>
    induction b using TensorProduct.induction_on with
    | zero => simp
    | tmul d y => rw [sub_eq_zero]; exact hmain c d x y
    | add b₁ b₂ h₁ h₂ =>
      have h := congrArg₂ (· + ·) h₁ h₂
      simp only [add_zero] at h
      refine Eq.trans ?_ h
      split_ifs <;> simp only [map_add (f := _), mul_add, add_mul] <;> abel
  | add a₁ a₂ h₁ h₂ =>
    have h := congrArg₂ (· + ·) h₁ h₂
    simp only [add_zero] at h
    refine Eq.trans ?_ h
    split_ifs <;> simp only [map_add (f := _), mul_add, add_mul] <;> abel

theorem UpperTheory.gen_glRelations_and_commute_of_isLie :
    ∀ (R : Type) [CommRing R] [Algebra ℝ R] (ι : Type) [Fintype ι] (n : ℕ) (A : Type) [Ring A] [Algebra ℂ A] [Algebra ℝ A] [IsScalarTower ℝ ℂ A] (D : Idem R ι) (l : Matrix (Fin n) (Fin n) R →ₗ[ℝ] A), IsLie l → (∀ τ, Formalism.REAL.GlRel (gen D l τ)) ∧ ∀ τ σ, τ ≠ σ → ∀ i j k m, Commute (gen D l τ i j) (gen D l σ k m) := by
  intro R _ _ ι _ n A _ _ _ _ D l hl
  have idem : ∀ τ, D.e τ * D.e τ = D.e τ := by
    intro τ
    calc D.e τ * D.e τ = D.e τ * ∑ σ, D.e σ := by
          rw [Finset.mul_sum, Finset.sum_eq_single τ]
          · intro σ _ h
            exact D.orth τ σ (Ne.symm h)
          · simp
      _ = D.e τ := by rw [D.sum, mul_one]
  refine ⟨fun τ => ?_, fun τ σ h i j k m => ?_⟩
  · intro a b c d
    simp only [gen]
    rw [unitMap_comm l hl, idem]
  · unfold Commute SemiconjBy
    rw [← sub_eq_zero]
    simp only [gen]
    rw [unitMap_comm l hl, D.orth τ σ h]
    simp
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BlockEmbeddingCommInfEmbAndExp
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem exp_block_extension (K : Type) [Field K] [NumberField K] {a n : ℕ} (e : Fin a ↪ Fin n) (Y : ArchMatrix K a) :
    (1 : ArchMatrix K n) + (show ArchMatrix K n from ext0 (R := mixedSpace K) e (NormedSpace.exp Y - 1 : ArchMatrix K a)) =
      NormedSpace.exp (show ArchMatrix K n from ext0 (R := mixedSpace K) e Y) := by
  have hsm : ∀ (c : ℝ) (Z : Matrix (Fin a) (Fin a) (mixedSpace K)), ext0 e (c • Z) = c • ext0 e Z := by
    intro c Z
    simp only [ext0, Matrix.mul_smul, Matrix.smul_mul]
  let g : ArchMatrix K a →ₗ[ℝ] ArchMatrix K n :=
    { toFun := fun X => ext0 (R := mixedSpace K) e X
      map_add' := fun X Z => matrixExtendByZero_add e X Z
      map_smul' := fun c X => hsm c X }
  have hg : Continuous g := LinearMap.continuous_of_finiteDimensional g
  have hpow : ∀ k : ℕ, (g Y) ^ (k + 1) = g (Y ^ (k + 1)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ih, pow_succ Y (k + 1)]
      exact matrixExtendByZero_mul e _ _
  have h1 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) Y).map g hg
  have h2 := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (g Y)
  have h3 : HasSum (fun k : ℕ => if k = 0 then (1 - g 1 : ArchMatrix K n) else 0) (1 - g 1) :=
    hasSum_ite_eq 0 _
  have h4 := h1.add h3
  have heq : (fun k : ℕ => ((k.factorial : ℝ)⁻¹) • (g Y) ^ k) =
      fun k : ℕ => g (((k.factorial : ℝ)⁻¹) • Y ^ k) + if k = 0 then (1 - g 1) else 0 := by
    funext k
    cases k with
    | zero => simp
    | succ k => rw [if_neg (Nat.succ_ne_zero k), add_zero, map_smul, hpow]
  rw [heq] at h2
  have h5 := h2.unique h4
  have hsub : g (NormedSpace.exp Y - 1) = g (NormedSpace.exp Y) - g 1 := map_sub g _ _
  change (1 : ArchMatrix K n) + g (NormedSpace.exp Y - 1) = NormedSpace.exp (g Y)
  rw [hsub, h5]
  abel

private theorem UpperTheory.prodEquiv_apply_eq_map_fst_snd (K : Type) [Field K] [NumberField K] (m : ℕ)
    (g : AdelicGLn.AdelicGL K m) :
    AdelicGLn.prodEquiv K m g =
      (GeneralLinearGroup.map (RingHom.fst (InfiniteAdeleRing K) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) g,
        GeneralLinearGroup.map (RingHom.snd (InfiniteAdeleRing K) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) g) := by
  ext i j <;> rfl

private theorem UpperTheory.archEquiv_symm_apply_eq_map_mixedSpace (K : Type) [Field K] [NumberField K] (m : ℕ) (x : archGroup K m) :
    (archEquiv K m).symm x =
      GeneralLinearGroup.map (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom
        (show GL (Fin m) (mixedSpace K) from (x : (ArchMatrix K m)ˣ)) := by
  ext i j
  rfl

theorem UpperTheory.blockEmbedding_comm_infEmb_and_exp :
    ∀ (K : Type) [Field K] [NumberField K] (a n : ℕ) (e : Fin a ↪ Fin n), (∀ x, emb e (infEmb K a x) = infEmb K n (embArch e x)) ∧ ∀ Y : Matrix (Fin a) (Fin a) (mixedSpace K), embArch e ((isExpLieAlgebra K a).expG ((isExpLieAlgebra K a).ofLie (toLie K a Y))) = (isExpLieAlgebra K n).expG ((isExpLieAlgebra K n).ofLie (toLie K n (ext0 e Y))) := by
  intro K _ _ a n e
  refine ⟨fun x => ?_, fun Y => ?_⟩
  · apply (AdelicGLn.prodEquiv K n).injective
    have hx := prodEquiv_infEmb (K := K) (n := a) x
    rw [UpperTheory.prodEquiv_apply_eq_map_fst_snd] at hx
    rw [Prod.mk.injEq] at hx
    rw [UpperTheory.prodEquiv_apply_eq_map_fst_snd, prodEquiv_infEmb]
    refine Prod.ext ?_ ?_
    · refine (emb_map e (RingHom.fst (InfiniteAdeleRing K) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K))
        (infEmb K a x)).trans ((congrArg (emb e) hx.1).trans ?_)
      rw [UpperTheory.archEquiv_symm_apply_eq_map_mixedSpace, UpperTheory.archEquiv_symm_apply_eq_map_mixedSpace]
      exact (emb_map e _ _).symm
    · exact (emb_map e (RingHom.snd (InfiniteAdeleRing K) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K))
        (infEmb K a x)).trans ((congrArg (emb e) hx.2).trans (map_one _))
  · apply Subtype.ext
    apply Units.ext
    exact exp_block_extension K e Y
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BlockDiagConjUnipotentLinear
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private def LowZ {n : ℕ} {R : Type} [CommRing R] (r : ℕ) (M : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ i j : Fin n, r ≤ (i : ℕ) → (j : ℕ) < r → M i j = 0

private theorem LowZ.mul {n r : ℕ} {R : Type} [CommRing R] {M N : Matrix (Fin n) (Fin n) R}
    (hM : LowZ r M) (hN : LowZ r N) : LowZ r (M * N) := fun i j hi hj => by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases lt_or_ge (k : ℕ) r with hk | hk
  · rw [hM i k hi hk, zero_mul]
  · rw [hN k j hk hj, mul_zero]

private theorem lower_zero_first_block_embedding {r s : ℕ} {R : Type} [CommRing R] (g : GL (Fin r) R) :
    LowZ r (emb (e1 r s) g).val := fun i j hi hj => by
  have hij : i ≠ j := fun h => by subst h; omega
  rw [coe_emb, Matrix.add_apply, Matrix.one_apply_ne hij, extendByZero_apply_eq_zero_of_row_not_mem, add_zero]
  intro k hk
  have := congrArg Fin.val hk
  simp at this
  omega

private theorem lower_zero_second_block_embedding {r s : ℕ} {R : Type} [CommRing R] (g : GL (Fin s) R) :
    LowZ r (emb (e2 r s) g).val := fun i j hi hj => by
  have hij : i ≠ j := fun h => by subst h; omega
  rw [coe_emb, Matrix.add_apply, Matrix.one_apply_ne hij, matrixExtendByZero_apply_of_outside_col, add_zero]
  intro k hk
  have := congrArg Fin.val hk
  simp at this
  omega

private theorem blockEntry_eq_sum {n r : ℕ} {S : Type} [CommRing S] (Y : UPos n r → S) :
    blockEntry Y = ∑ q : UPos n r, Matrix.single q.1.1 q.1.2 (Y q) := by
  ext i j
  rw [blockEntry_apply, Matrix.sum_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single (⟨(i, j), h⟩ : UPos n r)]
    · simp
    · intro q _ hq
      rw [Matrix.single_apply, if_neg]
      rintro ⟨rfl, rfl⟩
      exact hq rfl
    · simp
  · symm
    refine Finset.sum_eq_zero fun q _ => ?_
    rw [Matrix.single_apply, if_neg]
    rintro ⟨rfl, rfl⟩
    exact h q.2

private theorem conj_blockEntry {n r : ℕ} {S : Type} [CommRing S] {M N : Matrix (Fin n) (Fin n) S}
    (hM : LowZ r M) (hN : LowZ r N) (Y : UPos n r → S) :
    M * blockEntry Y * N = blockEntry (fun p : UPos n r => ∑ q : UPos n r, M p.1.1 q.1.1 * N q.1.2 p.1.2 * Y q) := by
  ext i j
  have h0 : (M * blockEntry Y * N) i j = ∑ q : UPos n r, M i q.1.1 * N q.1.2 j * Y q := by
    rw [blockEntry_eq_sum, Matrix.mul_sum, Matrix.sum_mul, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [Matrix.mul_apply, Matrix.single_apply, mul_ite, mul_zero, ite_and, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, ite_mul, zero_mul]
    ring
  rw [h0, blockEntry_apply]
  split_ifs with h
  · rfl
  · refine Finset.sum_eq_zero fun q _ => ?_
    rcases lt_or_ge (i : ℕ) r with hi | hi
    · rw [hN _ j q.2.2 (by omega), mul_zero, zero_mul]
    · rw [hM i _ hi q.2.1, zero_mul, zero_mul]

theorem UpperTheory.blockDiag_conj_unipotent_linear :
    ∀ (R : Type) [CommRing R] (r s : ℕ) (m₁ : GL (Fin r) R) (m₂ : GL (Fin s) R), ∃ c : UPos (r + s) r → UPos (r + s) r → R, ∀ (S : Type) [CommRing S] (f : R →+* S) (Y : UPos (r + s) r → S), Matrix.GeneralLinearGroup.map f (blk m₁ m₂) * unipGL Y = unipGL (fun p => ∑ q, f (c p q) * Y q) * Matrix.GeneralLinearGroup.map f (blk m₁ m₂) := by
  intro R _ r s m₁ m₂
  have h1 : LowZ r (blk m₁ m₂).val := (lower_zero_first_block_embedding m₁).mul (lower_zero_second_block_embedding m₂)
  have h2 : LowZ r ((blk m₁ m₂)⁻¹).val := by
    rw [blk, _root_.mul_inv_rev, ← map_inv, ← map_inv]
    exact (lower_zero_second_block_embedding _).mul (lower_zero_first_block_embedding _)
  generalize blk m₁ m₂ = m at h1 h2
  refine ⟨fun p q => m.val p.1.1 q.1.1 * (m⁻¹).val q.1.2 p.1.2, fun S _ f Y => ?_⟩
  rw [← mul_inv_eq_iff_eq_mul, ← map_inv]
  refine Units.ext ?_
  have hmm : m.val.map f * (m⁻¹).val.map f = 1 := by
    rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero f) (map_one f)]
  have h1' : LowZ r (m.val.map f) := fun i j hi hj => by rw [Matrix.map_apply, h1 i j hi hj, map_zero]
  have h2' : LowZ r ((m⁻¹).val.map f) := fun i j hi hj => by rw [Matrix.map_apply, h2 i j hi hj, map_zero]
  change m.val.map f * (1 + blockEntry Y) * (m⁻¹).val.map f = 1 + blockEntry _
  rw [mul_add, add_mul, mul_one, hmm, conj_blockEntry h1' h2']
  simp only [Matrix.map_apply, map_mul]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.UpperTriangularEqUnipotentMulLevi
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem cn_ne {r s : ℕ} (i : Fin r) (j : Fin s) : Fin.castAdd s i ≠ Fin.natAdd r j := fun h => by
  have := congrArg Fin.val h
  simp at this
  omega

private theorem block_embedding_first_val {R : Type} [CommRing R] {r s : ℕ} (m : GL (Fin r) R) :
    (emb (e1 r s) m).val = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks m.val 0 0 1) := by
  rw [coe_emb]
  ext i j
  induction i using Fin.addCases with
  | left a =>
    induction j using Fin.addCases with
    | left c =>
      have h0 : ext0 (e1 r s) ((m : Matrix (Fin r) (Fin r) R) - 1) (Fin.castAdd s a) (Fin.castAdd s c) =
          ((m : Matrix (Fin r) (Fin r) R) - 1) a c :=
        matrixExtendByZero_apply (e1 r s) _ a c
      simp only [Matrix.add_apply, h0, Matrix.reindex_apply, Matrix.submatrix_apply,
        finSumFinEquiv_symm_apply_castAdd, Matrix.fromBlocks_apply₁₁, Matrix.sub_apply,
        Matrix.one_apply, Fin.castAdd_inj]
      ring
    | right d =>
      have := matrixExtendByZero_apply_of_outside_col (e1 r s) ((m : Matrix (Fin r) (Fin r) R) - 1) (Fin.castAdd s a)
        (j := Fin.natAdd r d) (fun k h => cn_ne k d (by simpa [e1] using h.symm))
      simp [Matrix.reindex_apply, this, Matrix.one_apply, cn_ne]
  | right b =>
    have := extendByZero_apply_eq_zero_of_row_not_mem (e1 r s) ((m : Matrix (Fin r) (Fin r) R) - 1) (i := Fin.natAdd r b)
      (fun k h => cn_ne k b (by simpa [e1] using h.symm)) j
    induction j using Fin.addCases with
    | left c => simp [Matrix.reindex_apply, this, Matrix.one_apply, (cn_ne c b).symm]
    | right d => simp [Matrix.reindex_apply, this, Matrix.one_apply]

private theorem block_embedding_second_val {R : Type} [CommRing R] {r s : ℕ} (m : GL (Fin s) R) :
    (emb (e2 r s) m).val = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 1 0 0 m.val) := by
  rw [coe_emb]
  ext i j
  induction i using Fin.addCases with
  | right a =>
    induction j using Fin.addCases with
    | right c =>
      have h0 : ext0 (e2 r s) ((m : Matrix (Fin s) (Fin s) R) - 1) (Fin.natAdd r a) (Fin.natAdd r c) =
          ((m : Matrix (Fin s) (Fin s) R) - 1) a c :=
        matrixExtendByZero_apply (e2 r s) _ a c
      simp only [Matrix.add_apply, h0, Matrix.reindex_apply, Matrix.submatrix_apply,
        finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₂₂, Matrix.sub_apply,
        Matrix.one_apply, Fin.natAdd_inj]
      ring
    | left d =>
      have := matrixExtendByZero_apply_of_outside_col (e2 r s) ((m : Matrix (Fin s) (Fin s) R) - 1) (Fin.natAdd r a)
        (j := Fin.castAdd s d) (fun k h => cn_ne d k (by simpa [e2] using h))
      simp [Matrix.reindex_apply, this, Matrix.one_apply, (cn_ne d a).symm]
  | left b =>
    have := extendByZero_apply_eq_zero_of_row_not_mem (e2 r s) ((m : Matrix (Fin s) (Fin s) R) - 1) (i := Fin.castAdd s b)
      (fun k h => cn_ne b k (by simpa [e2] using h)) j
    induction j using Fin.addCases with
    | right c => simp [Matrix.reindex_apply, this, Matrix.one_apply, cn_ne b c]
    | left d => simp [Matrix.reindex_apply, this, Matrix.one_apply]

private theorem unip_val {R : Type} [CommRing R] {r s : ℕ} (Y : Matrix (Fin r) (Fin s) R) :
    ∃ X : UPos (r + s) r → R,
      unipMatrix X = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 1 Y 0 1) := by
  refine ⟨fun p => Y ⟨p.1.1, p.2.1⟩ ⟨p.1.2 - r, by have := p.1.2.isLt; have := p.2.2; omega⟩, ?_⟩
  ext i j
  simp only [unipMatrix, Matrix.add_apply, blockEntry_apply]
  induction i using Fin.addCases with
  | left a =>
    induction j using Fin.addCases with
    | left c =>
      have : ¬ (r ≤ ((Fin.castAdd s c : Fin (r + s)) : ℕ)) := by simp
      simp [this, Matrix.reindex_apply, Matrix.one_apply]
    | right d =>
      have h : ((Fin.castAdd s a : Fin (r + s)) : ℕ) < r ∧ r ≤ ((Fin.natAdd r d : Fin (r + s)) : ℕ) := by
        simp
      rw [dite_eq_left h]
      simp [Matrix.reindex_apply, Matrix.one_apply, cn_ne]
  | right b =>
    have : ¬ (((Fin.natAdd r b : Fin (r + s)) : ℕ) < r) := by simp
    induction j using Fin.addCases with
    | left c => simp [this, Matrix.reindex_apply, Matrix.one_apply, (cn_ne c b).symm]
    | right d => simp [this, Matrix.reindex_apply, Matrix.one_apply]

theorem UpperTheory.upperTriangular_eq_unipotent_mul_levi :
    ∀ (R : Type) [CommRing R] (r s : ℕ) (b : GL (Fin (r + s)) R), b.val.IsUpperTriangular → ∃ (X : UPos (r + s) r → R) (m₁ : GL (Fin r) R) (m₂ : GL (Fin s) R), b = unipGL X * blk m₁ m₂ := by
  intro R _ r s b hb
  set M : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) R :=
    Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm b.val with hMdef
  have hC : M.toBlocks₂₁ = 0 := by
    ext i j
    simp only [hMdef, Matrix.toBlocks₂₁, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
      Matrix.of_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Matrix.zero_apply]
    apply hb
    simp [Fin.lt_def]
    omega
  have hM : M = Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ 0 M.toBlocks₂₂ := by
    rw [← hC]
    exact (Matrix.fromBlocks_toBlocks M).symm
  have hbM : b.val = Matrix.reindex finSumFinEquiv finSumFinEquiv M := by
    simp [hMdef]
  have hdet : IsUnit (Matrix.det M) := by
    rw [hMdef, Matrix.det_reindex_self]
    exact (Matrix.GeneralLinearGroup.det b).isUnit
  rw [hM, Matrix.det_fromBlocks_zero₂₁] at hdet
  have hA : IsUnit M.toBlocks₁₁.det := isUnit_of_mul_isUnit_left hdet
  have hD : IsUnit M.toBlocks₂₂.det := isUnit_of_mul_isUnit_right hdet
  obtain ⟨X, hX⟩ := unip_val (M.toBlocks₁₂ * M.toBlocks₂₂⁻¹)
  refine ⟨X, Matrix.nonsingInvUnit _ hA, Matrix.nonsingInvUnit _ hD, ?_⟩
  have hmul : ∀ P Q : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) R,
      Matrix.reindex finSumFinEquiv finSumFinEquiv P * Matrix.reindex finSumFinEquiv finSumFinEquiv Q =
        Matrix.reindex finSumFinEquiv finSumFinEquiv (P * Q) := by
    intro P Q
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  apply Units.ext
  rw [Units.val_mul, coe_unipGL, hX, blk, Units.val_mul, block_embedding_first_val, block_embedding_second_val, hbM, ← mul_assoc, hmul, hmul]
  congr 1
  conv_lhs => rw [hM]
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  have h1 : (Matrix.nonsingInvUnit _ hA : Matrix (Fin r) (Fin r) R) = M.toBlocks₁₁ := rfl
  have h2 : (Matrix.nonsingInvUnit _ hD : Matrix (Fin s) (Fin s) R) = M.toBlocks₂₂ := rfl
  rw [h1, h2]
  simp [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hD]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.LieMapEqSumIdempotentGen
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.lieMap_eq_sum_idempotent_gen :
    ∀ (R : Type) [CommRing R] [Algebra ℝ R] (ι : Type) [Fintype ι] (n : ℕ) (A : Type) [Ring A] [Algebra ℂ A] [Algebra ℝ A] [IsScalarTower ℝ ℂ A] (D : Idem R ι) (l : Matrix (Fin n) (Fin n) R →ₗ[ℝ] A) (X : Matrix (Fin n) (Fin n) R), l X = ∑ τ, ∑ i, ∑ j, D.ch τ (X i j) • gen D l τ i j := by
  intro R _ _ ι _ n A _ _ _ _ D l X
  have key : ∀ i j, ∑ τ, D.ch τ (X i j) • gen D l τ i j = l (Matrix.single i j (X i j)) := by
    intro i j
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [gen, ← map_smul, ← map_sum, ← D.mul_e, ← Finset.mul_sum, D.sum, mul_one,
      unitMap_tmul, one_smul]
  conv_rhs =>
    rw [Finset.sum_comm]
    arg 2
    ext i
    rw [Finset.sum_comm]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [key, ← map_sum]
  congr 1
  exact Matrix.matrix_eq_sum_single X
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HasModerateGrowthConstantTerm
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.hasModerateGrowth_constantTerm :
    ∀ (K : Type) [Field K] [NumberField K] (n r : ℕ) (φ : AdelicGLn.AdelicGL K n → ℂ), HasModerateGrowth φ → HasModerateGrowth (constantTerm r φ) := by
  intro K _ _ n r φ ⟨C, N, hφ⟩
  obtain ⟨D, hD, hsub⟩ := exists_isCompact_superset_unipFundamentalDomain (K := K) (n := n) (r := r)
  obtain ⟨M, hM⟩ := CuspidalSpectrum.exists_height_le_of_isCompact (hD.image continuous_unipGL)
  have hc0 : 0 ≤ heightConst K n := le_trans zero_le_one one_le_heightConst
  have hfin : unipMeasure K n r (unipFundamentalDomain K n r) < ⊤ :=
    (measure_mono hsub).trans_lt hD.measure_lt_top
  refine ⟨|C| * (heightConst K n * |M|) ^ N * (unipMeasure K n r).real (unipFundamentalDomain K n r), N, fun g => ?_⟩
  have hg := (height_pos g).le
  have hb : ∀ X ∈ unipFundamentalDomain K n r,
      ‖φ (unipGL X * g)‖ ≤ |C| * (heightConst K n * |M| * AutomorphicForm.height g) ^ N := by
    intro X hX
    have h1 : AutomorphicForm.height (unipGL X * g) ≤ heightConst K n * |M| * AutomorphicForm.height g :=
      (height_mul_le _ _).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left ((hM _ ⟨X, hsub hX, rfl⟩).trans (le_abs_self M)) hc0) hg)
    exact (hφ _).trans (mul_le_mul (le_abs_self C) (pow_le_pow_left₀ (height_pos _).le h1 N)
      (pow_nonneg (height_pos _).le N) (abs_nonneg C))
  refine (norm_setIntegral_le_of_norm_le_const hfin hb).trans (le_of_eq ?_)
  rw [mul_pow (heightConst K n * |M|)]
  ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AlgModOfInjectiveIntertwining
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem UpperTheory.quantum_determinant_map {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (f : A →ₐ[ℂ] B) {n : ℕ}
    (X : Fin n → Fin n → A) (u : ℂ) : f (Formalism.REAL.qdet X u) = Formalism.REAL.qdet (fun i j => f (X i j)) u := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Formalism.REAL.qdet, Formalism.REAL.qminor, Formalism.REAL.Tm, map_sum, map_mul, map_intCast, map_list_prod, List.map_ofFn,
    Function.comp_def, map_add, apply_ite f, AlgHom.commutes, map_zero]

theorem UpperTheory.algMod_of_injective_intertwining :
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (N : Type) [AddCommGroup N] [Module ℂ N] (n : ℕ) (f : M →ₗ[ℂ] N) (E : Fin n → Fin n → Module.End ℂ M) (E' : Fin n → Fin n → Module.End ℂ N), (∀ i j x, f (E i j x) = E' i j (f x)) → ∀ u x, f (Formalism.REAL.qdet E u x) = Formalism.REAL.qdet E' u (f x) := by
  intro M _ _ N _ _ n f E E' h u x
  let S : Subalgebra ℂ (Module.End ℂ M × Module.End ℂ N) :=
    { carrier := {p | ∀ y, f (p.1 y) = p.2 (f y)}
      mul_mem' := fun {a b} ha hb y => (ha _).trans (congrArg a.2 (hb y))
      add_mem' := fun {a b} ha hb y => by
        simp only [Prod.fst_add, Prod.snd_add, LinearMap.add_apply, map_add (f := _), ha y, hb y]
      algebraMap_mem' := fun c y => map_smul f c y }
  let Z : Fin n → Fin n → S := fun i j => ⟨(E i j, E' i j), h i j⟩
  have h1 : (Formalism.REAL.qdet Z u).1.1 = Formalism.REAL.qdet E u :=
    UpperTheory.quantum_determinant_map ((AlgHom.fst ℂ _ _).comp S.val) Z u
  have h2 : (Formalism.REAL.qdet Z u).1.2 = Formalism.REAL.qdet E' u :=
    UpperTheory.quantum_determinant_map ((AlgHom.snd ℂ _ _).comp S.val) Z u
  rw [← h1, ← h2]
  exact (Formalism.REAL.qdet Z u).2 x
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.LocallyFiniteOfAlgModCriterion
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.locallyFinite_of_algMod_criterion :
    ∀ (X Y : Type) [MeasurableSpace X] (μ : Measure X) (V : Submodule ℂ (Y → ℂ)), FiniteDimensional ℂ V → ∀ F : X → Y → ℂ, (∀ x, F x ∈ V) → (∀ y, Integrable (fun x => F x y) μ) → (fun y => ∫ x, F x y ∂μ) ∈ V := by
  intro X Y _ μ V hV F hF hI
  classical
  let ev : Y → (V →ₗ[ℂ] ℂ) := fun y => (LinearMap.proj y).comp V.subtype
  have hspan : Submodule.span ℂ (Set.range ev) = ⊤ := by
    apply Submodule.span_eq_top_of_ne_zero
    intro z hz
    by_contra h
    apply hz
    ext y
    by_contra hy
    exact h ⟨ev y, ⟨y, rfl⟩, hy⟩
  have hint : ∀ φ : V →ₗ[ℂ] ℂ, Integrable (fun x => φ ⟨F x, hF x⟩) μ := by
    intro φ
    have hφ : φ ∈ Submodule.span ℂ (Set.range ev) := hspan ▸ Submodule.mem_top
    induction hφ using Submodule.span_induction with
    | mem f hf => obtain ⟨y, rfl⟩ := hf; exact hI y
    | zero => simp
    | add f g _ _ hf hg => exact hf.add hg
    | smul c f _ hf => exact hf.const_mul c
  let b := Module.finBasis ℂ V
  have key : (fun y => ∫ x, F x y ∂μ)
      = ∑ i, (∫ x, b.coord i ⟨F x, hF x⟩ ∂μ) • ((b i : V) : Y → ℂ) := by
    funext y
    have h1 : ∀ x, F x y = ∑ i, b.coord i ⟨F x, hF x⟩ * ((b i : V) : Y → ℂ) y := by
      intro x
      have h := congrArg (ev y) (b.sum_repr ⟨F x, hF x⟩)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum] at h
      simp only [map_smul] at h
      exact h.symm
    simp only [h1, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [integral_finsetSum _ (fun i _ => (hint (b.coord i)).mul_const _)]
    exact Finset.sum_congr rfl fun i _ => integral_mul_const _ _
  rw [key]
  exact V.sum_mem fun i _ => V.smul_mem _ (b i).2
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IntegralUnipFundamentalDomainCompLatticePreservi
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.integral_unipFundamentalDomain_comp_lattice_preserving :
    ∀ (K : Type) [Field K] [NumberField K] (n r : ℕ) (α : (UPos n r → AdeleRing (𝓞 K) K) ≃ₜ+ (UPos n r → AdeleRing (𝓞 K) K)), (∀ X, α X ∈ unipLattice K n r ↔ X ∈ unipLattice K n r) → ∀ F : (UPos n r → AdeleRing (𝓞 K) K) → ℂ, (∀ ξ ∈ unipLattice K n r, ∀ X, F (ξ + X) = F X) → ∫ X in unipFundamentalDomain K n r, F (α X) ∂unipMeasure K n r = ∫ X in unipFundamentalDomain K n r, F X ∂unipMeasure K n r := by
  intro K _ _ n r α hα F hF
  haveI : TopologicalSpace.MetrizableSpace (UPos n r → AdeleRing (𝓞 K) K) :=
    TopologicalSpace.metrizableSpace_of_t3_secondCountable _
  haveI : (unipMeasure K n r).Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  have hfd : IsAddFundamentalDomain (unipLattice K n r) (unipFundamentalDomain K n r) (unipMeasure K n r) :=
    isAddFundamentalDomain_unipFundamentalDomain
  have hsm := addEquivAddHaarChar_smul_map (unipMeasure K n r) α.symm
  have hpos := addEquivAddHaarChar_pos α.symm
  have hmap : (unipMeasure K n r).map α.symm = (addEquivAddHaarChar α.symm)⁻¹ • unipMeasure K n r := by
    conv_rhs => rw [← hsm]
    rw [smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]
  have hqmp : Measure.QuasiMeasurePreserving α.symm (unipMeasure K n r) (unipMeasure K n r) :=
    ⟨α.symm.continuous.measurable.aemeasurable, by rw [hmap]; exact Measure.smul_absolutelyContinuous⟩
  let e : unipLattice K n r → unipLattice K n r := fun g => ⟨α g, (hα g).2 g.2⟩
  have he : Function.Bijective e := by
    refine ⟨fun g h hgh => ?_, fun g => ⟨⟨α.symm g, (hα (α.symm g)).1 (by simpa using g.2)⟩, ?_⟩⟩
    · apply Subtype.ext
      apply α.injective
      exact congrArg Subtype.val hgh
    · apply Subtype.ext
      simp [e]
  have hfd' : IsAddFundamentalDomain (unipLattice K n r) (α.symm ⁻¹' unipFundamentalDomain K n r)
      (unipMeasure K n r) :=
    hfd.preimage_of_equiv hqmp he (fun g x => by
      show α.symm (α g + x) = g + α.symm x
      simp [map_add (f := _)])
  have hmeas := hfd'.measure_eq hfd
  have hpre := addEquivAddHaarChar_smul_preimage (unipMeasure K n r) (X := unipFundamentalDomain K n r) α.symm
  rw [hmeas, unipMeasure_unipFundamentalDomain, ENNReal.smul_def, smul_eq_mul, mul_one,
    ENNReal.coe_eq_one] at hpre
  have hmp : MeasurePreserving α.symm (unipMeasure K n r) (unipMeasure K n r) :=
    ⟨α.symm.continuous.measurable, by rw [hmap, hpre, inv_one, one_smul]⟩
  have key := hmp.setIntegral_preimage_emb α.symm.toHomeomorph.measurableEmbedding
    (fun y => F (α y)) (unipFundamentalDomain K n r)
  simp only [ContinuousAddEquiv.apply_symm_apply] at key
  rw [← key]
  exact hfd'.setIntegral_eq hfd (fun g x => hF g g.2 x)
end
