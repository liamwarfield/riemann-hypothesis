module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BlockEmbeddingFiniteAdelicGLCompatContinuous
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteCohomology
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
public import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfJumpsBdd

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsRestrictionBlockEmbeddingIntertwinesLie
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private noncomputable def extL (K : Type) [Field K] [NumberField K] {a n : ℕ} (e : Fin a ↪ Fin n) :
    archLie K a →ₗ[ℝ] archLie K n where
  toFun Y := (isExpLieAlgebra K n).ofLie (toLie K n (ext0 e (mat Y.1)))
  map_add' X Y := Subtype.ext (matrixExtendByZero_add e (mat X.1) (mat Y.1))
  map_smul' c X := Subtype.ext (by
    change ext0 e (c • mat X.1) = c • ext0 e (mat X.1)
    simp only [ext0, Matrix.mul_smul, Matrix.smul_mul])

private theorem key (K : Type) [Field K] [NumberField K] {a n : ℕ} (e : Fin a ↪ Fin n)
    (g : AdelicGLn.AdelicGL K n) (ψ : AdelicGLn.AdelicGL K n → ℂ) (m : AdelicGLn.AdelicGL K a) (x : archGroup K a)
    (Y : archLie K a) :
    archSlice (fun m => ψ (g * emb e m)) m (x * (isExpLieAlgebra K a).expG Y) =
      archSlice ψ (g * emb e m) (embArch e x * (isExpLieAlgebra K n).expG (extL K e Y)) := by
  obtain ⟨h1, h2⟩ := UpperTheory.blockEmbedding_comm_infEmb_and_exp K a n e
  have h3 : embArch e ((isExpLieAlgebra K a).expG Y) = (isExpLieAlgebra K n).expG (extL K e Y) := h2 (mat Y.1)
  rw [← h3, ← map_mul, archSlice_apply, archSlice_apply, ← h1, map_mul (emb e) m, mul_assoc]

theorem UpperTheory.exists_restriction_blockEmbedding_intertwines_lie :
    ∀ (K : Type) [Field K] [NumberField K] (a n : ℕ) (e : Fin a ↪ Fin n) (g : AdelicGLn.AdelicGL K n), ∃ f : archSmooth K n →ₗ[ℂ] archSmooth K a, (∀ ψ m, (f ψ).1 m = ψ.1 (g * emb e m)) ∧ ∀ X ψ, f (lam K n (ext0 e X) ψ) = lam K a X (f ψ) := by
  intro K _ _ a n e g
  have hs : ∀ ψ : archSmooth K n, (fun m => ψ.1 (g * emb e m)) ∈ archSmooth K a := fun ψ m => by
    rw [IsExpLieAlgebra.isSmoothFun_iff]
    intro x
    simp only [key]
    exact (((isExpLieAlgebra K n).isSmoothFun_iff).1 (ψ.2 (g * emb e m)) (embArch e x)).comp
      (LinearMap.toContinuousLinearMap (extL K e)).contDiff
  refine ⟨{ toFun := fun ψ => ⟨_, hs ψ⟩, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl },
    fun _ _ => rfl, fun X ψ => Subtype.ext (funext fun m => ?_)⟩
  have h1 := (isExpLieAlgebra K a).hasDerivAt_rightDeriv (hs ψ m) ((isExpLieAlgebra K a).ofLie (toLie K a X)) 1
  have h2 := (isExpLieAlgebra K n).hasDerivAt_rightDeriv (ψ.2 (g * emb e m))
    (extL K e ((isExpLieAlgebra K a).ofLie (toLie K a X))) 1
  simp only [key, map_one, map_smul] at h1
  exact (uAction_ι_apply (toLie K n (ext0 e X)) ψ (g * emb e m)).trans
    ((h2.unique h1).trans (uAction_ι_apply (toLie K a X) ⟨_, hs ψ⟩ m).symm)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.DdRLeFilAndInfFilEqBotOfHodgeTateMult
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain TensorProduct Module GlobalTheory.WeilDeligne GlobalTheory.Pst Polynomial

section Gen

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

private theorem step_of_mult [CharZero Qp] (PD : PeriodData G Qp K₀ K B BdR)
    [Fintype (K →ₐ[Qp] LL)] (hcard : Fintype.card (K →ₐ[Qp] LL) = finrank Qp K)
    (ρ : Representation LL G V) (hfin : FiniteDimensional LL ↥(DdR PD ρ)) (c : ℤ)
    (h : ∀ τ : K →ₐ[Qp] LL, multV PD ρ τ c = 0) :
    DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) (c + 1) = DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) c := by
  rw [JsetEmb.de_rham_filtration_eq_iSup_embeddings PD hcard ρ (c + 1), JsetEmb.de_rham_filtration_eq_iSup_embeddings PD hcard ρ c]
  refine iSup_congr fun τ => ?_
  have hle : FildR PD ρ τ c ≤ DdR PD ρ := fun x hx => hx.1.1
  have : FiniteDimensional LL ↥(FildR PD ρ τ c) := Submodule.finiteDimensional_of_le hle
  have h0 := h τ
  unfold multV at h0
  refine Submodule.eq_of_le_of_finrank_eq (Ln03.Pf.jb_FildR_anti PD ρ τ (by omega)) ?_
  omega

private theorem gen_fil [CharZero Qp] (PD : PeriodData G Qp K₀ K B BdR)
    [Fintype (K →ₐ[Qp] LL)] (hcard : Fintype.card (K →ₐ[Qp] LL) = finrank Qp K)
    (ρ : Representation LL G V) (hfin : FiniteDimensional LL ↥(DdR PD ρ)) :
    (∀ a : ℤ, (∀ (τ : K →ₐ[Qp] LL) (c : ℤ), c < a → multV PD ρ τ c = 0) →
      DdR PD ρ ≤ FilV PD (LL := LL) (V := V) a) ∧
    ∀ b : ℤ, (∀ (τ : K →ₐ[Qp] LL) (c : ℤ), b < c → multV PD ρ τ c = 0) →
      DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) (b + 1) = ⊥ := by
  refine ⟨fun a ha x hx => ?_, fun b hb => ?_⟩
  · obtain ⟨c, hc⟩ := Ln03.Pf.jb_FilV_exh PD (LL := LL) (V := V) x
    rcases le_total a c with h | h
    · exact Ln03.Pf.jb_FilV_anti PD (LL := LL) (V := V) h hc
    · have key : ∀ d, c ≤ d → d ≤ a → x ∈ FilV PD (LL := LL) (V := V) d := by
        intro d hd
        induction d, hd using Int.leInduction with
        | base => exact fun _ => hc
        | succ d hd ih =>
          intro hda
          have hm : x ∈ DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) d := ⟨hx, ih (by omega)⟩
          rw [← step_of_mult PD hcard ρ hfin d fun τ => ha τ d (by omega)] at hm
          exact hm.2
      exact key a h le_rfl
  · rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_bot]
    refine Ln03.Pf.jb_FilV_sep PD (LL := LL) (V := V) x fun d => ?_
    rcases le_total d (b + 1) with h | h
    · exact Ln03.Pf.jb_FilV_anti PD (LL := LL) (V := V) h hx.2
    · induction d, h using Int.leInduction with
      | base => exact hx.2
      | succ d hd ih =>
        have hm : x ∈ DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) d := ⟨hx.1, ih⟩
        rw [← step_of_mult PD hcard ρ hfin d fun τ => hb τ d (by omega)] at hm
        exact hm.2

end Gen

theorem UpperTheory.ddR_le_fil_and_inf_fil_eq_bot_of_hodgeTate_mult :
    ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K LL : FinExt l}, (∀ (τ : ↥K.1 →ₐ[ℚ_[l]] Om l) (x : ↥K.1), τ x ∈ LL.1) → ∀ {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), FiniteDimensional ↥LL.1 ↥(DdR (P.PD K) ρ) → (∀ a : ℤ, (∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (c : ℤ), c < a → multV (P.PD K) ρ τ c = 0) → DdR (P.PD K) ρ ≤ FilV (P.PD K) (LL := ↥LL.1) (V := V) a) ∧ ∀ b : ℤ, (∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (c : ℤ), b < c → multV (P.PD K) ρ τ c = 0) → DdR (P.PD K) ρ ⊓ FilV (P.PD K) (LL := ↥LL.1) (V := V) (b + 1) = ⊥ := by
  intro l _ P K LL key V _ _ _ _ _ ρ hfin
  have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have hc : Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = finrank ℚ_[l] ↥K.1 := by
    let e : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) ≃ (↥K.1 →ₐ[ℚ_[l]] Om l) :=
      { toFun := fun f => LL.1.val.comp f
        invFun := fun g => g.codRestrict LL.1.toSubalgebra (key g)
        left_inv := fun f => by ext; rfl
        right_inv := fun g => by ext; rfl }
    rw [Nat.card_congr e]
    exact AlgHom.natCard_of_splits _ _ _ (fun _ => IsAlgClosed.splits _)
  have : Finite (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact Module.finrank_pos.ne')
  letI := Fintype.ofFinite (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)
  exact gen_fil (P.PD K) (by rw [Fintype.card_eq_nat_card, hc]) ρ hfin
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsFiniteDimensionalCompactTranslatesOfLevelT
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.exists_finiteDimensional_compact_translates_of_level_types :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (S : Submodule ℂ (archSmooth K n)), Level S → Types S → ∃ V : Submodule ℂ (Reduction.maxCompact (K := K) (n := n) → ℂ), FiniteDimensional ℂ V ∧ ∀ φ ∈ S, ∀ g, (fun k : Reduction.maxCompact (K := K) (n := n) => φ.1 (g * k.1)) ∈ V := by
  intro K _ _ n S hLev hTyp
  obtain ⟨L, hL, hinv⟩ := hLev
  obtain ⟨V₀, hV₀, -, hφV⟩ := hTyp
  obtain ⟨L', -, hL'L, -, t, ht⟩ := UpperTheory.exists_open_level_normalized_by_integralFiniteGL K n L hL
  have hk : ∀ k : Reduction.maxCompact (K := K) (n := n), ∃ c ∈ t, c⁻¹ * finPart k.1 ∈ L' :=
    fun k => ht _ (finPart_mem_integralFiniteGL k.2)
  let Ψ : (↥t → ↥V₀) →ₗ[ℂ] (Reduction.maxCompact (K := K) (n := n) → ℂ) :=
    { toFun := fun h k =>
        (h ⟨Classical.choose (hk k), (Classical.choose_spec (hk k)).1⟩ : archCompact K n → ℂ)
          ⟨archPart k.1, archPart_mem_archCompact k.2⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  refine ⟨LinearMap.range Ψ, inferInstance, ?_⟩
  intro φ hφ g
  refine ⟨fun c => ⟨fun k' => φ.1 (g * finEmb K n c.1 * infEmb K n k'.1), hφV φ hφ _⟩, ?_⟩
  funext k
  show φ.1 (g * finEmb K n (Classical.choose (hk k)) * infEmb K n (archPart k.1)) = φ.1 (g * k.1)
  have hu : (Classical.choose (hk k))⁻¹ * finPart k.1 ∈ L := hL'L (Classical.choose_spec (hk k)).2
  have e : g * k.1 = g * finEmb K n (Classical.choose (hk k)) * infEmb K n (archPart k.1) *
      finEmb K n ((Classical.choose (hk k))⁻¹ * finPart k.1) := by
    conv_lhs => rw [← infEmb_archPart_mul_finEmb_finPart k.1]
    rw [map_mul, map_inv, mul_assoc g (finEmb K n _), ← infEmb_mul_finEmb_comm]
    simp only [mul_assoc, mul_inv_cancel_left]
  rw [e, hinv φ hφ _ hu]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ConstantTermArchSmooth
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ConstantTermConvolutionArch
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.constantTerm_convolution_arch :
    ∀ (K : Type) [Field K] [NumberField K] (n r : ℕ) [MeasurableSpace (archGroup K n)] [BorelSpace (archGroup K n)] (μ : Measure (archGroup K n)) [μ.IsHaarMeasure] (φ ψ : AdelicGLn.AdelicGL K n → ℂ) (D : archGroup K n → ℂ), Continuous φ → Continuous D → HasCompactSupport D → (∀ g, ψ g = ∫ y, φ (g * infEmb K n y) * D y ∂μ) → ∀ g, constantTerm r ψ g = ∫ y, constantTerm r φ (g * infEmb K n y) * D y ∂μ := by
  intro K _ _ n r _ _ μ _ φ ψ D hφ hD hDc hψ g
  obtain ⟨C, hC, hFC⟩ := exists_isCompact_superset_unipFundamentalDomain (K := K) (n := n) (r := r)
  let f : (UPos n r → AdeleRing (𝓞 K) K) × archGroup K n → ℂ :=
    fun p => φ (unipGL p.1 * g * infEmb K n p.2) * D p.2
  have hfc : Continuous f := by
    refine Continuous.mul (hφ.comp ?_) (hD.comp continuous_snd)
    exact ((continuous_unipGL.comp continuous_fst).mul continuous_const).mul
      (continuous_infEmb.comp continuous_snd)
  have hint : Integrable f (((unipMeasure K n r).restrict (unipFundamentalDomain K n r)).prod μ) := by
    have h1 : IntegrableOn f (C ×ˢ tsupport D) ((unipMeasure K n r).prod μ) :=
      hfc.continuousOn.integrableOn_compact (hC.prod hDc)
    have h2 : IntegrableOn f (unipFundamentalDomain K n r ×ˢ Set.univ) ((unipMeasure K n r).prod μ) := by
      refine h1.of_forall_diff_eq_zero (measurableSet_unipFundamentalDomain.prod MeasurableSet.univ) ?_
      rintro ⟨X, y⟩ ⟨⟨hX, -⟩, hn⟩
      have hy : y ∉ tsupport D := fun hy => hn ⟨hFC hX, hy⟩
      show φ (unipGL X * g * infEmb K n y) * D y = 0
      rw [image_eq_zero_of_notMem_tsupport hy, mul_zero]
    have h3 : ((unipMeasure K n r).restrict (unipFundamentalDomain K n r)).prod μ
        = ((unipMeasure K n r).prod μ).restrict (unipFundamentalDomain K n r ×ˢ Set.univ) := by
      rw [← Measure.prod_restrict, Measure.restrict_univ]
    rw [h3]
    exact h2
  have key := integral_integral_swap (f := fun X y => φ (unipGL X * g * infEmb K n y) * D y) hint
  show ∫ X in unipFundamentalDomain K n r, ψ (unipGL X * g) ∂unipMeasure K n r
    = ∫ y, (∫ X in unipFundamentalDomain K n r, φ (unipGL X * (g * infEmb K n y)) ∂unipMeasure K n r) * D y ∂μ
  simp_rw [hψ]
  refine key.trans ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show ∫ X in unipFundamentalDomain K n r, φ (unipGL X * g * infEmb K n y) * D y ∂unipMeasure K n r
    = (∫ X in unipFundamentalDomain K n r, φ (unipGL X * (g * infEmb K n y)) ∂unipMeasure K n r) * D y
  rw [← integral_mul_const]
  simp_rw [mul_assoc]
end

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.constantTerm_archSmooth :
    ∀ (K : Type) [Field K] [NumberField K] (n r : ℕ) (φ : archSmooth K n), IsAutomorphicForm φ.1 → ∃ hs : IsArchSmooth (constantTerm r φ.1), ∀ X : (isExpLieAlgebra K n).lieSubalgebra, (uAction (UniversalEnvelopingAlgebra.ι ℝ X) ⟨constantTerm r φ.1, hs⟩).1 = constantTerm r (uAction (UniversalEnvelopingAlgebra.ι ℝ X) φ).1 := by
  intro K _ _ n r φ hφ
  let μ : Measure (archGroup K n) := Measure.haar
  obtain ⟨d, b, ε, B, h1, h2, h3, h4, h5⟩ := exists_archCartanData K n
  obtain ⟨P, hPm, hPd, hP⟩ :=
    hφ.isSmoothKZ.exists_aeval_laplacian_sliceL_eq_zero b ε B h1 h2 h3 h4 h5
  obtain ⟨κ, hκs, hκc, -, hκ⟩ :=
    (isExpLieAlgebra K n).exists_kernel_eq_conv_of_aeval_laplacian μ b P hPm hPd
      (U := Set.univ) Filter.univ_mem
  have hκcont : Continuous κ :=
    IsExpLieAlgebra.IsTestFunction.continuous (isExpLieAlgebra K n) ⟨hκs, hκc⟩
  have rep : ∀ g y, archSlice φ.1 g y = ∫ z, archSlice φ.1 g (y * z) * κ z ∂μ :=
    fun g y => hκ _ (hP g) y
  have repφ : ∀ g, φ.1 g = ∫ z, φ.1 (g * infEmb K n z) * κ z ∂μ := by
    intro g
    have := rep g 1
    simpa [archSlice_apply] using this
  have hc : Continuous φ.1 := hφ.continuous
  have hct := UpperTheory.constantTerm_convolution_arch K n r μ φ.1 φ.1 κ hc hκcont hκc repφ
  have hctc := UpperTheory.continuous_constantTerm K n r φ.1 hc
  have hsliceC : ∀ g, Continuous (archSlice (constantTerm r φ.1) g) := by
    intro g
    show Continuous fun x => constantTerm r φ.1 (g * infEmb K n x)
    exact hctc.comp (continuous_const.mul continuous_infEmb)
  have repct : ∀ g y, archSlice (constantTerm r φ.1) g y
      = ∫ z, archSlice (constantTerm r φ.1) g (y * z) * κ z ∂μ := by
    intro g y
    simp only [archSlice_apply]
    rw [hct (g * infEmb K n y)]
    simp [mul_assoc, map_mul]
  have hs : IsArchSmooth (constantTerm r φ.1) := by
    intro g
    have hfun : archSlice (constantTerm r φ.1) g
        = fun y => ∫ z, archSlice (constantTerm r φ.1) g (y * z) * κ z ∂μ := funext (repct g)
    rw [hfun]
    exact (isExpLieAlgebra K n).isSmoothFun_integral_mul μ (hsliceC g) ⟨hκs, hκc⟩
  refine ⟨hs, fun X => ?_⟩
  funext g
  have hD := (isExpLieAlgebra K n).continuous_convDeriv hκs ((isExpLieAlgebra K n).ofLie X)
  have hDc := (isExpLieAlgebra K n).hasCompactSupport_convDeriv hκc ((isExpLieAlgebra K n).ofLie X)
  have repU : ∀ h, (uAction (UniversalEnvelopingAlgebra.ι ℝ X) φ).1 h
      = ∫ y, φ.1 (h * infEmb K n y)
          * (isExpLieAlgebra K n).convDeriv ((isExpLieAlgebra K n).ofLie X) κ y ∂μ := by
    intro h
    rw [uAction_ι_apply,
      IsExpLieAlgebra.rightDeriv_eq_integral_convDeriv hκs hκc (φ.2 h) (rep h)]
    simp [archSlice_apply]
  rw [uAction_ι_apply,
    IsExpLieAlgebra.rightDeriv_eq_integral_convDeriv hκs hκc (hs g) (repct g),
    UpperTheory.constantTerm_convolution_arch K n r μ φ.1 _ _ hc hD hDc repU g]
  simp [archSlice_apply]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ConstantTermLeviRationalLeftInvariant
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem blk_mul_blk_inv {r s : ℕ} {R : Type} [CommRing R] (m₁ : GL (Fin r) R) (m₂ : GL (Fin s) R) :
    blk m₁ m₂ * blk m₁⁻¹ m₂⁻¹ = 1 := by
  simp only [blk]
  rw [emb_comm m₁⁻¹ m₂⁻¹, map_inv, map_inv]
  group

theorem UpperTheory.constantTerm_levi_rational_left_invariant :
    ∀ (K : Type) [Field K] [NumberField K] (r s : ℕ) (φ : AdelicGLn.AdelicGL K (r + s) → ℂ),
      IsLeftInvariant φ → ∀ (γ₁ : GL (Fin r) K) (γ₂ : GL (Fin s) K) g,
        constantTerm (r := r) φ (AdelicGLn.diagonal K (r + s) (blk γ₁ γ₂) * g) =
          constantTerm (r := r) φ g := by
  intro K _ _ r s φ hφ γ₁ γ₂ g
  have hdiag : ∀ γ : GL (Fin (r + s)) K, AdelicGLn.diagonal K (r + s) γ =
      GeneralLinearGroup.map (algebraMap K (AdeleRing (𝓞 K) K)) γ := fun _ => rfl
  obtain ⟨c, hc⟩ := UpperTheory.blockDiag_conj_unipotent_linear K r s γ₁ γ₂
  obtain ⟨c', hc'⟩ := UpperTheory.blockDiag_conj_unipotent_linear K r s γ₁⁻¹ γ₂⁻¹
  have hDD : AdelicGLn.diagonal K (r + s) (blk γ₁⁻¹ γ₂⁻¹) = (AdelicGLn.diagonal K (r + s) (blk γ₁ γ₂))⁻¹ := by
    rw [← map_inv]
    congr 1
    exact eq_inv_of_mul_eq_one_right (blk_mul_blk_inv γ₁ γ₂)
  have hu : ∀ Y : UPos (r + s) r → AdeleRing (𝓞 K) K,
      unipGL (fun p => ∑ q, algebraMap K (AdeleRing (𝓞 K) K) (c' p q) * Y q) =
        (AdelicGLn.diagonal K (r + s) (blk γ₁ γ₂))⁻¹ * unipGL Y * AdelicGLn.diagonal K (r + s) (blk γ₁ γ₂) := by
    intro Y
    have h := hc' (AdeleRing (𝓞 K) K) (algebraMap K (AdeleRing (𝓞 K) K)) Y
    rw [← hdiag, hDD] at h
    rw [h]
    group
  have hv : ∀ Y : UPos (r + s) r → AdeleRing (𝓞 K) K,
      unipGL (fun p => ∑ q, algebraMap K (AdeleRing (𝓞 K) K) (c p q) * Y q) =
        AdelicGLn.diagonal K (r + s) (blk γ₁ γ₂) * unipGL Y * (AdelicGLn.diagonal K (r + s) (blk γ₁ γ₂))⁻¹ := by
    intro Y
    have h := hc (AdeleRing (𝓞 K) K) (algebraMap K (AdeleRing (𝓞 K) K)) Y
    rw [← hdiag] at h
    rw [h]
    group
  have hmem : ∀ (d : UPos (r + s) r → UPos (r + s) r → K) (X : UPos (r + s) r → AdeleRing (𝓞 K) K),
      X ∈ unipLattice K (r + s) r →
        (fun p => ∑ q, algebraMap K (AdeleRing (𝓞 K) K) (d p q) * X q) ∈ unipLattice K (r + s) r := by
    intro d X hX
    obtain ⟨y, rfl⟩ := AddMonoidHom.mem_range.mp hX
    refine AddMonoidHom.mem_range.mpr ⟨fun p => ∑ q, d p q * y q, ?_⟩
    funext p
    set_option synthInstance.maxHeartbeats 100000 in
      simp [AddMonoidHom.compLeft_apply, map_sum, map_mul]
  have hcont : ∀ d : UPos (r + s) r → UPos (r + s) r → K,
      Continuous (fun (X : UPos (r + s) r → AdeleRing (𝓞 K) K) p =>
        ∑ q, algebraMap K (AdeleRing (𝓞 K) K) (d p q) * X q) := by
    intro d
    refine continuous_pi fun p => ?_
    exact continuous_finsetSum _ fun q _ => continuous_const.mul (continuous_apply q)
  have hinv1 : ∀ Y : UPos (r + s) r → AdeleRing (𝓞 K) K,
      (fun p => ∑ q, algebraMap K (AdeleRing (𝓞 K) K) (c p q) *
        (∑ q', algebraMap K (AdeleRing (𝓞 K) K) (c' q q') * Y q')) = Y := by
    intro Y
    apply unipGL_injective
    rw [hv, hu]
    group
  have hinv2 : ∀ Y : UPos (r + s) r → AdeleRing (𝓞 K) K,
      (fun p => ∑ q, algebraMap K (AdeleRing (𝓞 K) K) (c' p q) *
        (∑ q', algebraMap K (AdeleRing (𝓞 K) K) (c q q') * Y q')) = Y := by
    intro Y
    apply unipGL_injective
    rw [hu, hv]
    group
  let α : (UPos (r + s) r → AdeleRing (𝓞 K) K) ≃ₜ+ (UPos (r + s) r → AdeleRing (𝓞 K) K) :=
    { toFun := fun X p => ∑ q, algebraMap K (AdeleRing (𝓞 K) K) (c' p q) * X q
      invFun := fun X p => ∑ q, algebraMap K (AdeleRing (𝓞 K) K) (c p q) * X q
      left_inv := fun X => hinv1 X
      right_inv := fun X => hinv2 X
      map_add' := by
        intro X Y
        funext p
        simp [mul_add, Finset.sum_add_distrib]
      continuous_toFun := hcont c'
      continuous_invFun := hcont c }
  have hα : ∀ X, α X ∈ unipLattice K (r + s) r ↔ X ∈ unipLattice K (r + s) r := by
    intro X
    constructor
    · intro h
      have h2 := hmem c (fun p => ∑ q, algebraMap K (AdeleRing (𝓞 K) K) (c' p q) * X q) h
      rwa [hinv1] at h2
    · exact hmem c' X
  have hper : ∀ ξ ∈ unipLattice K (r + s) r, ∀ X : UPos (r + s) r → AdeleRing (𝓞 K) K,
      φ (unipGL (ξ + X) * g) = φ (unipGL X * g) :=
    fun ξ hξ X => hφ.unipGL_vadd g ⟨ξ, hξ⟩ X
  have hstep : ∀ X : UPos (r + s) r → AdeleRing (𝓞 K) K,
      φ (unipGL X * (AdelicGLn.diagonal K (r + s) (blk γ₁ γ₂) * g)) = φ (unipGL (α X) * g) := by
    intro X
    rw [← hφ (blk γ₁⁻¹ γ₂⁻¹), hDD]
    change _ = φ (unipGL (fun p => ∑ q, algebraMap K (AdeleRing (𝓞 K) K) (c' p q) * X q) * g)
    rw [hu]
    group
  unfold constantTerm
  simp_rw [hstep]
  exact UpperTheory.integral_unipFundamentalDomain_comp_lattice_preserving K (r + s) r α hα (fun X => φ (unipGL X * g)) hper
end
