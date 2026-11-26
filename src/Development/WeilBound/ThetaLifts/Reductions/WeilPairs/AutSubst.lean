module

public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutDef
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurLemmaHeisenbergCommutingThetaOperator

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFdPosFin
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
open MeasureTheory

noncomputable section

namespace GlobalTheory.ThetaSchurUnitF


open scoped TensorProduct Matrix in
open NumberField IsDedekindDomain in
open MeasureTheory in
theorem _root_.GlobalTheory.ThetaSchurUnitF.exists_fd_pos_fin {F E : Type} [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E}
    {ψ : AddChar (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) ℂ} (hψ : ∀ a, ‖ψ a‖ = 1) {f : _root_.Formalism.IndefR.DatumF.WOF F E nS nT → ℂ}
    (hf : _root_.Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ ψ f)
    {y : _root_.Formalism.IndefR.DatumF.WOF F E nS nT} (hy : f y ≠ 0) :
    ∃ (μ : Measure (_root_.Formalism.IndefR.DatumF.WOF F E nS nT)) (𝓕 : Set (_root_.Formalism.IndefR.DatumF.WOF F E nS nT)), μ.IsAddHaarMeasure ∧
      IsAddFundamentalDomain (_root_.Formalism.IndefR.DatumF.ratLF F E nS nT) 𝓕 μ ∧
      (∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ) ≠ 0 ∧ (∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ) ≠ ⊤ := by
  obtain ⟨h1, h2, h3, h4, h5, K, hK, hcov⟩ := _root_.GlobalTheory.AdelicMatrixLatticeF.lattice F E nS nT
  haveI : BorelSpace (_root_.Formalism.IndefR.DatumF.WOF F E nS nT) := ⟨rfl⟩
  obtain ⟨⟨μ, 𝓕, hμ, h𝓕, -⟩, hN⟩ :=
    _root_.GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact _ (_root_.Formalism.IndefR.DatumF.ratLF F E nS nT) K hK hcov
  have hper : ∀ γ ∈ _root_.Formalism.IndefR.DatumF.ratLF F E nS nT, ∀ w, ‖f (γ + w)‖ = ‖f w‖ := by
    intro γ hγ w
    have h := _root_.GlobalTheory.ThetaSchurF.prod_periodic hψ hf hf hγ w
    simp only [← starRingEnd_apply, RCLike.mul_conj] at h
    have h' : ‖f (γ + w)‖ ^ 2 = ‖f w‖ ^ 2 := by exact_mod_cast h
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h'
  obtain ⟨N, hN⟩ := hN f hf.cont hper
  obtain ⟨-, htop, hl, -⟩ := hN μ 𝓕 hμ h𝓕
  haveI : Countable (_root_.Formalism.IndefR.DatumF.ratLF F E nS nT) :=
    (TopologicalSpace.separableSpace_iff_countable).1 inferInstance
  refine ⟨μ, 𝓕, hμ, h𝓕, ?_, ?_⟩
  · intro hz
    have hall : ∫⁻ w, ‖f w‖ₑ ^ 2 ∂μ = 0 := by
      rw [h𝓕.lintegral_eq_tsum']
      refine ENNReal.tsum_eq_zero.2 fun γ => ?_
      rw [← hz]
      refine lintegral_congr fun w => ?_
      rw [AddSubgroup.vadd_def, vadd_eq_add, ← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm,
        hper _ (-γ).2 w]
    have hcont : Continuous fun w => ‖f w‖ₑ ^ 2 :=
      (ENNReal.continuous_pow 2).comp (continuous_enorm.comp hf.cont)
    have hae := (lintegral_eq_zero_iff hcont.measurable).1 hall
    have heq := (Continuous.ae_eq_iff_eq μ hcont continuous_const).1 hae
    have hfy := congrFun heq y
    simp [hy] at hfy
  · rw [hl]
    exact ENNReal.mul_ne_top htop (by simp)

end GlobalTheory.ThetaSchurUnitF
end
end

section -- merged from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutSubstA
noncomputable section

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF

namespace PositivityTheory.ThKW.SubstA

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E}

theorem exists_mtF_eq {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {γ : GAF σ J} (h : γ ∈ GQF σ J) :
    ∃ m : Matrix (Fin n) (Fin n) E, mtF σ J γ = m.map (incAF F E) := by
  obtain ⟨γ', -, e⟩ := h
  exact ⟨γ'.1, (congrArg Units.val e).symm⟩

theorem actOF_inv_actOF (g : GAF σ JS) (h : GAF σ JT) (x : WOF F E nS nT) :
    actOF σ JS JT g⁻¹ h⁻¹ (actOF σ JS JT g h x) = x := by
  rw [← GlobalTheory.WeilPartsF.actOF_mul, inv_mul_cancel, inv_mul_cancel, GlobalTheory.FinLatF.actOF_one]

theorem continuous_actOF (g : GAF σ JS) (h : GAF σ JT) : Continuous (actOF (nS := nS) (nT := nT) σ JS JT g h) := by
  unfold actOF
  exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

theorem exists_actOF_ratWF {γ : GAF σ JS} (hγ : γ ∈ GQF σ JS) {γ' : GAF σ JT} (hγ' : γ' ∈ GQF σ JT)
    (x : Matrix (Fin nT) (Fin nS) E) : ∃ y, actOF σ JS JT γ γ' (ratWF (F := F) x) = ratWF y := by
  obtain ⟨m, hm⟩ := exists_mtF_eq ((GQF σ JS).inv_mem hγ)
  obtain ⟨m', hm'⟩ := exists_mtF_eq hγ'
  refine ⟨m' * x * m, ?_⟩
  unfold actOF ratWF
  rw [hm, hm', Matrix.map_mul, Matrix.map_mul]

theorem actOF_mem_ratLF {γ : GAF σ JS} (hγ : γ ∈ GQF σ JS) {γ' : GAF σ JT} (hγ' : γ' ∈ GQF σ JT) {x : WOF F E nS nT}
    (hx : x ∈ ratLF F E nS nT) : actOF σ JS JT γ γ' x ∈ ratLF F E nS nT := by
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨z, hz⟩ := exists_actOF_ratWF hγ hγ' y
  exact ⟨z, hz.symm⟩

theorem symplOHF_actOF (hS : IsHermND σ JS) (g : GAF σ JS) (h : GAF σ JT) (x y : WOF F E nS nT) :
    symplOHF σ JS JT ξ₀ (actOF σ JS JT g h x) (actOF σ JS JT g h y) = symplOHF σ JS JT ξ₀ x y := by
  unfold symplOHF
  rw [PositivityTheory.ThKW.LatA.symplOF_actOF hS]

theorem isThetaFunOF_comp (hS : IsHermND σ JS) {ψ : AddChar (AF F) ℂ} {f : WOF F E nS nT → ℂ}
    (hf : IsThetaFunOF σ JS JT ξ₀ ψ f) {γ : GAF σ JS} (hγ : γ ∈ GQF σ JS) {γ' : GAF σ JT} (hγ' : γ' ∈ GQF σ JT) :
    IsThetaFunOF σ JS JT ξ₀ ψ fun w => f (actOF σ JS JT γ γ' w) := by
  let A : WOF F E nS nT →+ WOF F E nS nT := AddMonoidHom.mk' (actOF σ JS JT γ γ') (GlobalTheory.FinLatF.actOF_add γ γ')
  have hA : Continuous (actOF (nS := nS) (nT := nT) σ JS JT γ γ') := continuous_actOF γ γ'
  refine ⟨fun x w => ?_, ?_, hf.cont.comp hA, fun k L h1 h2 w => ?_⟩
  · obtain ⟨y, e⟩ := exists_actOF_ratWF hγ hγ' x
    show f (actOF σ JS JT γ γ' (ratWF x + w)) = _
    rw [GlobalTheory.FinLatF.actOF_add, ← symplOHF_actOF hS γ γ', e, hf.quasi]
  · obtain ⟨U, hU, h⟩ := hf.level
    refine ⟨U.comap A, hU.preimage hA, fun u hu h0 => ?_⟩
    funext w
    have e := congrFun (h _ hu (GlobalTheory.FinLatF.actOF_mem_finSubF γ γ' h0)) (actOF σ JS JT γ γ' w)
    unfold heisOF at e ⊢
    rw [← e, ← symplOHF_actOF hS γ γ' w u]
    exact congrArg (fun x => _ * f x) (GlobalTheory.FinLatF.actOF_add γ γ' w u)
  · have h3 : ∀ t, (actOF σ JS JT γ γ' (L t)).map (finPartF F E) = 0 := fun t => by
      unfold actOF
      rw [Matrix.map_mul, Matrix.map_mul, h2, Matrix.mul_zero, Matrix.zero_mul]
    have := hf.smooth k (A.comp L) (hA.comp h1) h3 (actOF σ JS JT γ γ' w)
    simp only [GlobalTheory.FinLatF.actOF_add]
    exact this

theorem setLIntegral_comp (e : WOF F E nS nT ≃+ WOF F E nS nT) (he : Continuous e) (hes : Continuous e.symm)
    (hΓ : ∀ x, e x ∈ ratLF F E nS nT ↔ x ∈ ratLF F E nS nT) (μ : Measure (WOF F E nS nT)) (hμ : μ.IsAddHaarMeasure)
    {𝓕 : Set (WOF F E nS nT)} (h𝓕 : IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 μ) (φ : WOF F E nS nT → ENNReal)
    (hφ : ∀ γ ∈ ratLF F E nS nT, ∀ x, φ (γ + x) = φ x) : ∫⁻ w in 𝓕, φ (e w) ∂μ = ∫⁻ w in 𝓕, φ w ∂μ := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  have : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  have : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨e'⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  have : LocallyCompactSpace (AF F ⊗[F] E) := e'.isClosedEmbedding.locallyCompactSpace
  have : SecondCountableTopology (AF F ⊗[F] E) := e'.secondCountableTopology
  have : T2Space (AF F ⊗[F] E) := e'.isEmbedding.t2Space
  have : LocallyCompactSpace (WOF F E nS nT) :=
    inferInstanceAs (LocallyCompactSpace (Fin nT → Fin nS → AF F ⊗[F] E))
  have : SecondCountableTopology (WOF F E nS nT) :=
    inferInstanceAs (SecondCountableTopology (Fin nT → Fin nS → AF F ⊗[F] E))
  have : T2Space (WOF F E nS nT) := inferInstanceAs (T2Space (Fin nT → Fin nS → AF F ⊗[F] E))
  haveI : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  haveI tZ : IsTopologicalAddGroup (WOF F E nS nT) := inferInstance
  have hdisc : DiscreteTopology (ratLF F E nS nT) := by
    obtain ⟨U, hU, hx⟩ := GlobalTheory.AdelicMatrixLattice.discrete_tensor (F := F) (E := E) (AF F)
      (GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero F)
    have hN : (Set.univ.pi fun _ : Fin nT => Set.univ.pi fun _ : Fin nS => U) ∈
        nhds (0 : WOF F E nS nT) :=
      set_pi_mem_nhds Set.finite_univ fun _ _ => set_pi_mem_nhds Set.finite_univ fun _ _ => hU
    refine discreteTopology_of_isOpen_singleton_zero ?_
    rw [isOpen_singleton_iff_nhds_eq_pure]
    refine le_antisymm (Filter.le_pure_iff.2 ?_) (pure_le_nhds _)
    have hc : ContinuousAt (fun x : ratLF F E nS nT => (x : WOF F E nS nT)) 0 :=
      continuous_subtype_val.continuousAt
    refine Filter.mem_of_superset (hc.preimage_mem_nhds hN) ?_
    rintro ⟨_, y, rfl⟩ hy
    have hy0 : y = 0 := by
      funext i j
      exact hx _ (hy i (Set.mem_univ i) j (Set.mem_univ j))
    subst hy0
    exact Subtype.ext (map_zero _)
  haveI : Countable (ratLF F E nS nT) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  obtain ⟨K, hK, hx⟩ := GlobalTheory.AdelicMatrixLattice.cocompact_tensor (F := F) (E := E) (AF F)
    (GlobalTheory.AdeleCocompact.exists_compact_adele F)
  choose c hc using hx
  have hcov : ∀ x : WOF F E nS nT, ∃ γ ∈ ratLF F E nS nT, γ + x ∈
      (Set.univ.pi fun _ : Fin nT => Set.univ.pi fun _ : Fin nS => K) :=
    fun x => ⟨_, ⟨Matrix.of fun i j => c (x i j), rfl⟩, fun i _ j _ => hc (x i j)⟩
  have hKc : IsCompact (Set.univ.pi (fun _ : Fin nT => Set.univ.pi fun _ : Fin nS => K) :
      Set (WOF F E nS nT)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hK
  have hfin := @GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (WOF F E nS nT) _ _ tZ _ _ (ratLF F E nS nT) _ _
    hKc hcov μ hμ 𝓕 h𝓕
  exact @GlobalTheory.RatSubst.setLIntegral_comp_addEquiv (WOF F E nS nT) _ _ tZ _ _ _ _ (ratLF F E nS nT) _ e he hes hΓ μ hμ 𝓕 h𝓕
    hfin.ne φ hφ

end PositivityTheory.ThKW.SubstA

end
end

noncomputable section

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF

namespace PositivityTheory.ThKW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {B : Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}
  {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)} {hc : HeisClosedF σ JS JT ξ₀ B.ψ} {w : 𝓞 E} {lam : ℕ →* ℂ}
  {Om : GAF σ JS × GAF σ JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ)}
  {s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ}

theorem rat_subst (C : Ctx σ B JS JT ξ₀ θ ι) {γ : GAF σ JS} (hγ : γ ∈ GQF σ JS) {γ' : GAF σ JT} (hγ' : γ' ∈ GQF σ JT)
    {f : WOF F E nS nT → ℂ} (hf : IsThetaFunOF σ JS JT ξ₀ B.ψ f) :
    IsThetaFunOF σ JS JT ξ₀ B.ψ (fun x => f (actOF σ JS JT γ⁻¹ γ'⁻¹ x)) ∧
    (∀ w₀, (fun x => heisOF σ JS JT ξ₀ B.ψ w₀ f (actOF σ JS JT γ⁻¹ γ'⁻¹ x)) =
      heisOF σ JS JT ξ₀ B.ψ (actOF σ JS JT γ γ' w₀) (fun x => f (actOF σ JS JT γ⁻¹ γ'⁻¹ x))) ∧
    ∀ (μ : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), μ.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 μ →
        ∫⁻ x in 𝓕, ‖f (actOF σ JS JT γ⁻¹ γ'⁻¹ x)‖ₑ ^ 2 ∂μ = ∫⁻ x in 𝓕, ‖f x‖ₑ ^ 2 ∂μ := by
  have hψ : ∀ a, ‖B.ψ a‖ = 1 := (GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood F E σ B C.good).1.2.1
  have hi := (GQF σ JS).inv_mem hγ
  have hi' := (GQF σ JT).inv_mem hγ'
  have hinv : ∀ x, actOF σ JS JT γ γ' (actOF σ JS JT γ⁻¹ γ'⁻¹ x) = x := fun x => by
    have := SubstA.actOF_inv_actOF (σ := σ) (JS := JS) (JT := JT) γ⁻¹ γ'⁻¹ x
    rwa [inv_inv, inv_inv] at this
  refine ⟨SubstA.isThetaFunOF_comp C.hS hf hi hi', fun w₀ => ?_, fun μ 𝓕 hμ h𝓕 => ?_⟩
  · funext x
    unfold heisOF
    beta_reduce
    rw [GlobalTheory.FinLatF.actOF_add, SubstA.actOF_inv_actOF, ← SubstA.symplOHF_actOF C.hS γ⁻¹ γ'⁻¹ x,
      SubstA.actOF_inv_actOF]
  · let e : WOF F E nS nT ≃+ WOF F E nS nT :=
      { toFun := actOF σ JS JT γ⁻¹ γ'⁻¹
        invFun := actOF σ JS JT γ γ'
        left_inv := hinv
        right_inv := SubstA.actOF_inv_actOF γ γ'
        map_add' := GlobalTheory.FinLatF.actOF_add _ _ }
    refine SubstA.setLIntegral_comp e (SubstA.continuous_actOF _ _) (SubstA.continuous_actOF _ _)
      (fun x => ⟨fun hx => ?_, SubstA.actOF_mem_ratLF hi hi'⟩) μ hμ h𝓕 (fun w => ‖f w‖ₑ ^ 2) ?_
    · rw [← hinv x]
      exact SubstA.actOF_mem_ratLF hγ hγ' hx
    · rintro _ ⟨y, rfl⟩ x
      have h7 : ‖f (ratWF y + x)‖ = ‖f x‖ := by
        rw [hf.quasi y x, norm_mul, hψ, one_mul]
      show ‖f (ratWF y + x)‖ₑ ^ 2 = ‖f x‖ₑ ^ 2
      rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, h7]

theorem schur_norm (C : Ctx σ B JS JT ξ₀ θ ι) (M : Module.End ℂ (WOF F E nS nT → ℂ))
    (h1 : ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → IsThetaFunOF σ JS JT ξ₀ B.ψ (M f))
    (h2 : ∀ u f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → M (heisOF σ JS JT ξ₀ B.ψ u f) = heisOF σ JS JT ξ₀ B.ψ u (M f))
    (h3 : ∀ (μ : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), μ.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 μ → ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f →
        ∫⁻ x in 𝓕, ‖M f x‖ₑ ^ 2 ∂μ = ∫⁻ x in 𝓕, ‖f x‖ₑ ^ 2 ∂μ) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → M f = c • f := by
  obtain ⟨c, hc⟩ := GlobalTheory.T.schur_lemma_heisenberg_commuting_thetaOperator F E σ B C.good nS nT JS JT C.hS C.hT ξ₀ C.h0 C.hξ M h1 h2 h3
  have hψ : ∀ a, ‖B.ψ a‖ = 1 := (GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood F E σ B C.good).1.2.1
  by_cases h0 : ∃ f y, IsThetaFunOF σ JS JT ξ₀ B.ψ f ∧ f y ≠ 0
  · obtain ⟨f, y, hf, hy⟩ := h0
    obtain ⟨μ, 𝓕, hμ, h𝓕, hI0, hIt⟩ := GlobalTheory.ThetaSchurUnitF.exists_fd_pos_fin hψ hf hy
    have h := h3 μ 𝓕 hμ h𝓕 f hf
    rw [hc f hf] at h
    simp only [Pi.smul_apply, smul_eq_mul, enorm_mul, mul_pow] at h
    rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top enorm_ne_top)] at h
    have e1 : ‖c‖ₑ ^ 2 = 1 := by
      have := congrArg (· / ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ) h
      rwa [ENNReal.mul_div_cancel_right hI0 hIt, ENNReal.div_self hI0 hIt] at this
    have e2 : (‖c‖₊ : ENNReal) ^ 2 = 1 := by rwa [enorm_eq_nnnorm] at e1
    have e3 : ‖c‖₊ ^ 2 = 1 := by exact_mod_cast e2
    have e4 : ‖c‖ ^ 2 = 1 := by
      have := congrArg (fun t : NNReal => (t : ℝ)) e3
      simpa using this
    exact ⟨c, (pow_eq_one_iff_of_nonneg (norm_nonneg c) two_ne_zero).1 e4, hc⟩
  · push_neg at h0
    refine ⟨1, norm_one, fun f hf => ?_⟩
    have : f = 0 := funext fun y => h0 f y hf
    subst this
    simp

end PositivityTheory.ThKW

end
