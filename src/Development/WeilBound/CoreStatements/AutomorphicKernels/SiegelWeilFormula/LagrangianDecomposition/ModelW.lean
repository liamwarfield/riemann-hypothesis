module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.ModelPf
public import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLActs
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SubSplitOf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.DiagonalColumnInclusion.IncMDiagCols
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.BilinearFormExamples.AdelicCoordinatesEvalZeroFormMemAdmissible

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzPointValuesAdmitted
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzPointValuesAdmitted
open scoped TensorProduct NNReal ENNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.TowU

namespace GlobalTheory.TowU.PointVal

theorem adelicSchwartz_pointValues_admitted_alt : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ], (∀ x : κ → AF F, (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (adeleClass F).adm κ) ∧ (∃ φ ∈ schA F κ, φ 0 = 1) ∧ (∀ w, ∀ φ ∈ schA F κ, schr ψ w φ ∈ schA F κ) ∧ ∀ (w w' : (κ → AF F) × (κ → AF F)) (φ : (κ → AF F) → ℂ), schr ψ w (schr ψ w' φ) = ψ (⅟(2 : AF F) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)) • schr ψ (w + w') φ := by
  intro F _ _ ψ hψ κ _
  have h3 : ∀ w, ∀ φ ∈ schA F κ, schr ψ w φ ∈ schA F κ := fun w φ hφ => GlobalTheory.ConeMeasV.schr_mem_schA hψ w hφ
  refine ⟨?_, ?_, h3, ?_⟩
  · intro x g _
    refine ⟨g (fun i => (x i).2) • ((BoundedContinuousFunction.evalCLM ℂ
      (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1)).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)), fun f => ?_⟩
    simp [pureA, mul_comm]
  · obtain ⟨φ, hφ, hne⟩ := GlobalTheory.ThetaSumNe.exists_mem_schA_thetaSum_ne_zero F κ
    have : ∃ ξ : κ → F, φ (fun i => algebraMap F (AF F) (ξ i)) ≠ 0 := by
      by_contra h
      push_neg at h
      exact hne (by simp [thetaSum, h])
    obtain ⟨ξ, hξ⟩ := this
    refine ⟨(φ (fun i => algebraMap F (AF F) (ξ i)))⁻¹ • schr ψ ((fun i => algebraMap F (AF F) (ξ i)), 0) φ,
      Submodule.smul_mem _ _ (h3 _ φ hφ), ?_⟩
    simp [schr, hξ]
  · intro w w' φ
    funext x
    simp only [schr, Pi.smul_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add]
    rw [← mul_assoc, ← AddChar.map_add_eq_mul, ← mul_assoc, ← AddChar.map_add_eq_mul, add_assoc x w.1 w'.1]
    congr 2
    simp only [add_dotProduct, dotProduct_add]
    have h2 : (2 : AF F) * ⅟(2 : AF F) = 1 := mul_invOf_self 2
    linear_combination (-(w.1 ⬝ᵥ w'.2)) * h2

end GlobalTheory.TowU.PointVal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzPointValuesAdmittedStatement
open scoped TensorProduct NNReal ENNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.TowU

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicSchwartz_pointValues_admitted : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ], (∀ x : κ → AF F, (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (adeleClass F).adm κ) ∧ (∃ φ ∈ schA F κ, φ 0 = 1) ∧ (∀ w, ∀ φ ∈ schA F κ, schr ψ w φ ∈ schA F κ) ∧ ∀ (w w' : (κ → AF F) × (κ → AF F)) (φ : (κ → AF F) → ℂ), schr ψ w (schr ψ w' φ) = ψ (⅟(2 : AF F) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)) • schr ψ (w + w') φ := by
  first | exact @GlobalTheory.TowU.PointVal.adelicSchwartz_pointValues_admitted_alt | exact GlobalTheory.TowU.PointVal.adelicSchwartz_pointValues_admitted_alt | (intros; apply GlobalTheory.TowU.PointVal.adelicSchwartz_pointValues_admitted_alt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzTensorLeftFactor
noncomputable section
namespace GlobalTheory.SchwartzBox

theorem box_pow_mul_iteratedFDeriv_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {κ κ' : Type}
    [Fintype κ] [Fintype κ'] (f₁ : SchwartzMap (κ → V) ℂ) (f₂ : SchwartzMap (κ' → V) ℂ) (k n : ℕ)
    (x : κ ⊕ κ' → V) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y : κ ⊕ κ' → V => f₁ (y ∘ Sum.inl) * f₂ (y ∘ Sum.inr)) x‖ ≤
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (SchwartzMap.seminorm ℂ k i f₁ * SchwartzMap.seminorm ℂ 0 (n - i) f₂ +
          SchwartzMap.seminorm ℂ 0 i f₁ * SchwartzMap.seminorm ℂ k (n - i) f₂) := by
  have hs₁ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : κ ⊕ κ' → V => f₁ (y ∘ Sum.inl)) :=
    (f₁.smooth ⊤).comp (restr V (Sum.inl : κ → κ ⊕ κ')).contDiff
  have hs₂ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : κ ⊕ κ' → V => f₂ (y ∘ Sum.inr)) :=
    (f₂.smooth ⊤).comp (restr V (Sum.inr : κ' → κ ⊕ κ')).contDiff
  have hx : ‖x‖ ^ k ≤ ‖x ∘ Sum.inl‖ ^ k + ‖x ∘ Sum.inr‖ ^ k := by
    have h0 : ‖x‖ ^ k ≤ (max ‖x ∘ Sum.inl‖ ‖x ∘ Sum.inr‖) ^ k :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_le_max_comp x) k
    refine h0.trans ?_
    have p1 := pow_nonneg (norm_nonneg (x ∘ Sum.inl)) k
    have p2 := pow_nonneg (norm_nonneg (x ∘ Sum.inr)) k
    rcases le_total ‖x ∘ Sum.inl‖ ‖x ∘ Sum.inr‖ with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have hL := norm_iteratedFDeriv_mul_le hs₁ hs₂ x (n := n) (by exact_mod_cast le_top)
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => f₁ (y ∘ Sum.inl) * f₂ (y ∘ Sum.inr)) x‖
      ≤ (‖x ∘ Sum.inl‖ ^ k + ‖x ∘ Sum.inr‖ ^ k) * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i f₁ (x ∘ Sum.inl)‖ * ‖iteratedFDeriv ℝ (n - i) f₂ (x ∘ Sum.inr)‖ := by
        refine mul_le_mul hx (hL.trans ?_) (norm_nonneg _) (by positivity)
        refine Finset.sum_le_sum fun i _ => ?_
        gcongr
        · exact norm_iteratedFDeriv_restr_le Sum.inl f₁ i x
        · exact norm_iteratedFDeriv_restr_le Sum.inr f₂ (n - i) x
    _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ((‖x ∘ Sum.inl‖ ^ k * ‖iteratedFDeriv ℝ i f₁ (x ∘ Sum.inl)‖) *
              ‖iteratedFDeriv ℝ (n - i) f₂ (x ∘ Sum.inr)‖ +
           ‖iteratedFDeriv ℝ i f₁ (x ∘ Sum.inl)‖ *
              (‖x ∘ Sum.inr‖ ^ k * ‖iteratedFDeriv ℝ (n - i) f₂ (x ∘ Sum.inr)‖)) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ _ := by
        refine Finset.sum_le_sum fun i _ => ?_
        gcongr
        · exact SchwartzMap.le_seminorm ℂ k i f₁ _
        · exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ f₂ _ _
        · exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ f₁ _ _
        · exact SchwartzMap.le_seminorm ℂ k (n - i) f₂ _

theorem exists_boxCLM : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (κ κ' : Type) [Fintype κ]
    [Fintype κ'] (f₁ : SchwartzMap (κ → V) ℂ),
    ∃ T : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ ⊕ κ' → V) ℂ,
      ∀ f x, T f x = f₁ (x ∘ Sum.inl) * f (x ∘ Sum.inr) := by
  intro V _ _ κ κ' _ _ f₁
  refine ⟨SchwartzMap.mkCLM (σ := RingHom.id ℂ)
    (fun (f : SchwartzMap (κ' → V) ℂ) (x : κ ⊕ κ' → V) => f₁ (x ∘ Sum.inl) * f (x ∘ Sum.inr))
    (fun f g x => by simp [mul_add]) (fun a f x => by simp; ring) (fun f => ?_) ?_, fun _ _ => rfl⟩
  · exact ((f₁.smooth ⊤).comp (restr V (Sum.inl : κ → κ ⊕ κ')).contDiff).mul
      ((f.smooth ⊤).comp (restr V (Sum.inr : κ' → κ ⊕ κ')).contDiff)
  · rintro ⟨k, n⟩
    refine ⟨Finset.range (k + 1) ×ˢ Finset.range (n + 1),
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (SchwartzMap.seminorm ℂ k i f₁ + SchwartzMap.seminorm ℂ 0 i f₁), by positivity, fun f x => ?_⟩
    refine (box_pow_mul_iteratedFDeriv_le f₁ f k n x).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    have hb : ∀ a, a ≤ k → SchwartzMap.seminorm ℂ a (n - i) f ≤
        (Finset.range (k + 1) ×ˢ Finset.range (n + 1)).sup (schwartzSeminormFamily ℂ (κ' → V) ℂ) f := by
      intro a ha
      have hm : (a, n - i) ∈ Finset.range (k + 1) ×ˢ Finset.range (n + 1) := by
        simp only [Finset.mem_product, Finset.mem_range]; omega
      exact Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℂ (κ' → V) ℂ) hm
    rw [mul_assoc, add_mul]
    gcongr
    · exact hb 0 (Nat.zero_le _)
    · exact hb k le_rfl

end GlobalTheory.SchwartzBox
end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.ExistsSchwartzOneCpt
noncomputable section

open scoped TensorProduct NNReal ENNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

namespace SliceP

def injL (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (κ' κ'' : Type) :
    (κ' → V) →L[ℝ] (κ' ⊕ κ'' → V) :=
  ContinuousLinearMap.pi fun i => Sum.elim (fun a => (ContinuousLinearMap.proj a : (κ' → V) →L[ℝ] V))
    (fun _ => (0 : (κ' → V) →L[ℝ] V)) i

theorem injL_apply (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (κ' κ'' : Type) (x : κ' → V) :
    injL V κ' κ'' x = Sum.elim x 0 := by
  funext i
  cases i <;> rfl

theorem norm_le_injL (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (κ' κ'' : Type) [Fintype κ'] [Fintype κ'']
    (x : κ' → V) : ‖x‖ ≤ ‖injL V κ' κ'' x‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun a => ?_
  rw [injL_apply]
  exact norm_le_pi_norm (Sum.elim x 0 : κ' ⊕ κ'' → V) (Sum.inl a)

def sliceCLM (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (κ' κ'' : Type) [Fintype κ'] [Fintype κ''] :
    SchwartzMap (κ' ⊕ κ'' → V) ℂ →L[ℂ] SchwartzMap (κ' → V) ℂ :=
  SchwartzMap.compCLM ℂ (injL V κ' κ'').hasTemperateGrowth ⟨1, 1, fun x => by
    have := norm_le_injL V κ' κ'' x
    have h0 := norm_nonneg (injL V κ' κ'' x)
    simp only [pow_one, one_mul]
    linarith⟩

theorem sliceCLM_apply (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (κ' κ'' : Type) [Fintype κ'] [Fintype κ'']
    (f : SchwartzMap (κ' ⊕ κ'' → V) ℂ) (x : κ' → V) : sliceCLM V κ' κ'' f x = f (Sum.elim x 0) := by
  simp [sliceCLM, injL_apply]

variable {F : Type} [Field F] [NumberField F]

theorem continuous_sumElim_zero (X : Type) [TopologicalSpace X] [Zero X] (κ' κ'' : Type) :
    Continuous fun x : κ' → X => (Sum.elim x 0 : κ' ⊕ κ'' → X) := by
  refine continuous_pi fun i => ?_
  cases i with
  | inl a => exact continuous_apply a
  | inr b => exact continuous_const

theorem sb_slice {κ' κ'' : Type} {g : (κ' ⊕ κ'' → Af F) → ℂ} (hg : g ∈ SB (κ' ⊕ κ'' → Af F)) :
    (fun x : κ' → Af F => g (Sum.elim x 0)) ∈ SB (κ' → Af F) := by
  haveI : T2Space (Af F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  have hc := continuous_sumElim_zero (Af F) κ' κ''
  have hemb : IsClosedEmbedding fun x : κ' → Af F => (Sum.elim x 0 : κ' ⊕ κ'' → Af F) :=
    Function.LeftInverse.isClosedEmbedding (f := fun y : κ' ⊕ κ'' → Af F => y ∘ Sum.inl)
      (fun x => rfl) (continuous_pi fun a => continuous_apply (Sum.inl a)) hc
  exact ⟨hg.1.comp_continuous hc, hg.2.comp_isClosedEmbedding hemb⟩

theorem slice0_pureA {κ' κ'' : Type} [Fintype κ'] [Fintype κ''] (f : SchwartzMap (κ' ⊕ κ'' → mixedEmbedding.mixedSpace F) ℂ)
    (g : (κ' ⊕ κ'' → Af F) → ℂ) :
    slice0 κ' κ'' (pureA F f g) = pureA F (sliceCLM _ κ' κ'' f) (fun x => g (Sum.elim x 0)) := by
  funext x
  simp only [slice0, LinearMap.coe_mk, AddHom.coe_mk, pureA, sliceCLM_apply]
  congr 2
  · funext i
    cases i with
    | inl a => rfl
    | inr b => exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  · funext i
    cases i <;> rfl

theorem slice_mem {κ' κ'' : Type} [Fintype κ'] [Fintype κ''] :
    ∀ Ψ ∈ schA F (κ' ⊕ κ''), slice0 κ' κ'' Ψ ∈ schA F κ' := by
  intro Ψ hΨ
  induction hΨ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    rw [slice0_pureA]
    exact GlobalTheory.CharInvForm.mem_schA _ (sb_slice hg)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem slice_adm {κ' κ'' : Type} [Fintype κ'] [Fintype κ''] :
    ∀ l ∈ (adeleClass F).adm κ', l ∘ₗ slice0 κ' κ'' ∈ (adeleClass F).adm (κ' ⊕ κ'') := by
  intro l hl g hg
  obtain ⟨T, hT⟩ := hl _ (sb_slice hg)
  refine ⟨T.comp (sliceCLM _ κ' κ''), fun f => ?_⟩
  rw [LinearMap.comp_apply, slice0_pureA, ContinuousLinearMap.comp_apply, hT]

theorem exists_schwartz_one_cpt (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] :
    ∃ f₀ : SchwartzMap V ℂ, f₀ 0 = 1 ∧ HasCompactSupport f₀ := by
  obtain ⟨f, -, hc, hs, -, h1⟩ :=
    exists_contDiff_tsupport_subset (x := (0 : V)) (s := Set.univ) (n := ⊤) Filter.univ_mem
  have hc' : HasCompactSupport (fun x => (f x : ℂ)) := hc.comp_left Complex.ofReal_zero
  have hs' : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (f x : ℂ)) := Complex.ofRealCLM.contDiff.comp hs
  exact ⟨hc'.toSchwartzMap hs', by simp [h1], hc'⟩

theorem exists_sb_one (κ : Type) [Fintype κ] : ∃ g ∈ SB (κ → Af F), g 0 = 1 := by
  obtain ⟨g, hg, y, hy⟩ := PositivityTheory.RL.SeminormBoundRestriction.exists_SB (F := F) (κ := κ)
  have hc : Continuous fun x : κ → Af F => x + y := (Homeomorph.addRight y).continuous
  refine ⟨fun x => g (x + y), ⟨hg.1.comp_continuous hc, ?_⟩, by simpa using hy⟩
  exact hg.2.comp_homeomorph (Homeomorph.addRight y)

theorem continuous_of_mem {κ : Type} [Fintype κ] {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) : Continuous Φ := by
  have h := GlobalTheory.WeilAdm.HaarSplit.continuous_comp_splitE F κ Φ hΦ
  have e : Φ = fun x => Φ (GlobalTheory.WeilAdm.HaarSplit.splitE F κ ((GlobalTheory.WeilAdm.HaarSplit.splitE F κ).symm x)) :=
    funext fun x => by rw [AddEquiv.apply_symm_apply]
  rw [e]
  exact h.comp (GlobalTheory.WeilAdm.HaarSplit.continuous_splitE_symm F κ)

theorem exists_one (κ'' : Type) [Fintype κ''] : ∃ φ₀ ∈ schA F κ'', φ₀ 0 = 1 ∧
    ∀ μ'' : @Measure (κ'' → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ'' →
      ∫⁻ x, ‖φ₀ x‖ₑ ^ 2 ∂μ'' ≠ 0 ∧ ∫⁻ x, ‖φ₀ x‖ₑ ^ 2 ∂μ'' ≠ ⊤ := by
  obtain ⟨f₀, hf₀, hf₀c⟩ := exists_schwartz_one_cpt (κ'' → mixedEmbedding.mixedSpace F)
  obtain ⟨g₀, hg₀, hg₀1⟩ := exists_sb_one (F := F) κ''
  have hmem : pureA F f₀ g₀ ∈ schA F κ'' := GlobalTheory.CharInvForm.mem_schA f₀ hg₀
  have h0 : pureA F f₀ g₀ 0 = 1 := by rw [GlobalTheory.CharInvForm.pureA_zero, hf₀, hg₀1, one_mul]
  refine ⟨pureA F f₀ g₀, hmem, h0, fun μ'' hμ => ?_⟩
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  letI m2 : MeasurableSpace (κ'' → AF F) := borel _
  haveI : BorelSpace (κ'' → AF F) := ⟨rfl⟩
  haveI := hμ
  set φ₀ := pureA F f₀ g₀ with hφ₀
  have hc : Continuous φ₀ := continuous_of_mem hmem

  set sp := GlobalTheory.WeilAdm.HaarSplit.splitE F κ'' with hsp
  have hK : IsCompact (sp '' (tsupport f₀ ×ˢ tsupport g₀)) :=
    (hf₀c.isCompact.prod hg₀.2.isCompact).image (GlobalTheory.WeilAdm.HaarSplit.continuous_splitE F κ'')
  have hzero : ∀ x, x ∉ sp '' (tsupport f₀ ×ˢ tsupport g₀) → φ₀ x = 0 := by
    intro x hx
    have e : φ₀ x = f₀ (sp.symm x).1 * g₀ (sp.symm x).2 := by
      rw [hφ₀, show x = sp (sp.symm x) from (AddEquiv.apply_symm_apply _ _).symm,
        GlobalTheory.WeilAdm.HaarSplit.pureA_splitE, AddEquiv.apply_symm_apply]
    rw [e]
    by_cases h1 : (sp.symm x).1 ∈ tsupport f₀
    · by_cases h2 : (sp.symm x).2 ∈ tsupport g₀
      · exact absurd ⟨sp.symm x, ⟨h1, h2⟩, AddEquiv.apply_symm_apply _ _⟩ hx
      · rw [image_eq_zero_of_notMem_tsupport h2, mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport h1, zero_mul]
  have hcs : HasCompactSupport φ₀ := by
    refine HasCompactSupport.intro hK hzero
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hcs
  constructor
  ·
    set U : Set (κ'' → AF F) := {x | (1 / 2 : ℝ) < ‖φ₀ x‖} with hU
    have hUo : IsOpen U := isOpen_lt continuous_const hc.norm
    have hU0 : (0 : κ'' → AF F) ∈ U := by
      show (1 / 2 : ℝ) < ‖φ₀ 0‖
      rw [h0, norm_one]
      norm_num
    have hpos : 0 < μ'' U := hUo.measure_pos μ'' ⟨0, hU0⟩
    refine ne_of_gt (lt_of_lt_of_le ?_ (lintegral_mono (g := fun x => ‖φ₀ x‖ₑ ^ 2)
      (f := U.indicator fun _ => ENNReal.ofReal (1 / 2) ^ 2) fun x => ?_))
    · rw [lintegral_indicator_const hUo.measurableSet]
      exact ENNReal.mul_pos (pow_ne_zero 2 (ENNReal.ofReal_pos.2 (by norm_num)).ne') hpos.ne'
    · by_cases hx : x ∈ U
      · rw [Set.indicator_of_mem hx]
        have : (1 / 2 : ℝ) < ‖φ₀ x‖ := hx
        have hle : ENNReal.ofReal (1 / 2) ≤ ‖φ₀ x‖ₑ := by
          rw [← ofReal_norm_eq_enorm]
          exact ENNReal.ofReal_le_ofReal this.le
        exact pow_le_pow_left₀ bot_le hle 2
      · rw [Set.indicator_of_notMem hx]
        exact bot_le
  ·
    set K := sp '' (tsupport f₀ ×ˢ tsupport g₀)
    have hKm : MeasurableSet K := hK.isClosed.measurableSet
    refine ne_of_lt (lt_of_le_of_lt (lintegral_mono (g := K.indicator fun _ => ENNReal.ofReal C ^ 2) fun x => ?_) ?_)
    · by_cases hx : x ∈ K
      · rw [Set.indicator_of_mem hx, ← ofReal_norm_eq_enorm]
        exact pow_le_pow_left₀ bot_le (ENNReal.ofReal_le_ofReal (hC x)) 2
      · rw [Set.indicator_of_notMem hx, hzero x hx]
        simp
    · rw [lintegral_indicator_const hKm]
      exact ENNReal.mul_lt_top (by simp) hK.measure_lt_top

theorem box_norm {κ' κ'' : Type} [Fintype κ'] [Fintype κ''] (μ' : @Measure (κ' → AF F) (borel _))
    (μ'' : @Measure (κ'' → AF F) (borel _)) (h' : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ')
    (h'' : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ'') :
    ∃ μ : @Measure (κ' ⊕ κ'' → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ ∧
      ∀ φ' ∈ schA F κ', ∀ φ'' ∈ schA F κ'',
        ∫⁻ x, ‖boxFun φ' φ'' x‖ₑ ^ 2 ∂μ = (∫⁻ x, ‖φ' x‖ₑ ^ 2 ∂μ') * ∫⁻ x, ‖φ'' x‖ₑ ^ 2 ∂μ'' := by
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  letI m1 : MeasurableSpace (κ' → AF F) := borel _
  haveI : BorelSpace (κ' → AF F) := ⟨rfl⟩
  letI m2 : MeasurableSpace (κ'' → AF F) := borel _
  haveI : BorelSpace (κ'' → AF F) := ⟨rfl⟩
  letI m3 : MeasurableSpace (κ' ⊕ κ'' → AF F) := borel _
  haveI : BorelSpace (κ' ⊕ κ'' → AF F) := ⟨rfl⟩
  haveI : MeasurableAdd (κ' → AF F) := ContinuousAdd.measurableAdd
  haveI : MeasurableAdd (κ'' → AF F) := ContinuousAdd.measurableAdd
  haveI := h'
  haveI := h''
  haveI : (μ'.prod μ'').IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure μ' μ''
  let e : ((κ' → AF F) × (κ'' → AF F)) ≃+ (κ' ⊕ κ'' → AF F) :=
    { toFun := fun p => Sum.elim p.1 p.2
      invFun := fun x => (x ∘ Sum.inl, x ∘ Sum.inr)
      left_inv := fun p => rfl
      right_inv := fun x => Sum.elim_comp_inl_inr x
      map_add' := fun p q => by funext i; cases i <;> rfl }
  have hc : Continuous e := continuous_pi fun i => by
    cases i with
    | inl a => exact (continuous_apply a).comp continuous_fst
    | inr b => exact (continuous_apply b).comp continuous_snd
  have hc' : Continuous e.symm :=
    (continuous_pi fun a => continuous_apply (Sum.inl a)).prodMk (continuous_pi fun b => continuous_apply (Sum.inr b))
  refine ⟨(μ'.prod μ'').map e, e.isAddHaarMeasure_map _ hc hc', fun φ' hφ' φ'' hφ'' => ?_⟩
  let em : ((κ' → AF F) × (κ'' → AF F)) ≃ᵐ (κ' ⊕ κ'' → AF F) := (Homeomorph.mk e.toEquiv hc hc').toMeasurableEquiv
  have hint : ∀ h : (κ' ⊕ κ'' → AF F) → ℝ≥0∞, ∫⁻ x, h x ∂((μ'.prod μ'').map e) = ∫⁻ p, h (e p) ∂(μ'.prod μ'') :=
    fun h => lintegral_map_equiv h em
  rw [hint]
  have e1 : ∀ p : (κ' → AF F) × (κ'' → AF F), ‖boxFun φ' φ'' (e p)‖ₑ ^ 2 = ‖φ' p.1‖ₑ ^ 2 * ‖φ'' p.2‖ₑ ^ 2 := by
    intro p
    rw [show boxFun φ' φ'' (e p) = φ' p.1 * φ'' p.2 from rfl, enorm_mul, mul_pow]
  simp_rw [e1]
  exact lintegral_prod_mul ((continuous_of_mem hφ').measurable.enorm.pow_const 2).aemeasurable
    ((continuous_of_mem hφ'').measurable.enorm.pow_const 2).aemeasurable

end SliceP

theorem sliceFacts : SliceFacts := fun F _ _ κ' κ'' _ _ =>
  ⟨SliceP.slice_mem, SliceP.slice_adm, SliceP.exists_one κ'', fun μ' μ'' h' h'' => SliceP.box_norm μ' μ'' h' h''⟩

end PositivityTheory.SiegelWeilFormula.Ald

end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SchrTransl
noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

variable {F : Type} [Field F] [NumberField F]

theorem schr_char {κ' κ'' : Type} [Fintype κ'] [Fintype κ''] (ψ : AddChar (AF F) ℂ) (v : κ'' → AF F)
    (Ψ : (κ' ⊕ κ'' → AF F) → ℂ) :
    schr ψ ((0 : κ' ⊕ κ'' → AF F), Sum.elim (0 : κ' → AF F) v) Ψ = fun z => ψ ((z ∘ Sum.inr) ⬝ᵥ v) * Ψ z := by
  funext z
  have hz : z = Sum.elim (z ∘ Sum.inl) (z ∘ Sum.inr) := (Sum.elim_comp_inl_inr z).symm
  simp only [schr, zero_dotProduct, mul_zero, add_zero]
  congr 2
  conv_lhs => rw [hz]
  rw [sumElim_dotProduct_sumElim]
  simp

theorem schr_transl {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ) (u : κ → AF F) (φ : (κ → AF F) → ℂ) (z : κ → AF F) :
    schr ψ (u, 0) φ z = φ (z + u) := by
  simp [schr]

theorem box_transl {κ' κ'' : Type} [Fintype κ'] [Fintype κ''] (ψ : AddChar (AF F) ℂ) (u : κ'' → AF F)
    (φ' : (κ' → AF F) → ℂ) (φ'' : (κ'' → AF F) → ℂ) :
    boxFun φ' (schr ψ (u, 0) φ'') = schr ψ (Sum.elim (0 : κ' → AF F) u, 0) (boxFun φ' φ'') := by
  funext x
  rw [schr_transl]
  simp only [boxFun]
  rw [schr_transl]
  congr 2
  funext i
  simp

theorem opBox_of (hP : PartCharInv) (hS : SliceFacts) : OpBox := by
  intro F _ _ ψ hψ κ' κ'' _ _ W _ _ B dd G _ act om hsp hw x hfix φ₀ hφ₀ h0
  have hcomm : ∀ w : W, (dd.e w).1 ∘ Sum.inl = 0 → (dd.e w).2 ∘ Sum.inl = 0 →
      ∀ Φ ∈ schA F (κ' ⊕ κ''), om x (schr ψ (dd.e w) Φ) = schr ψ (dd.e w) (om x Φ) := by
    intro w h1 h2 Φ hΦ
    have := hsp.impl x w Φ hΦ
    simpa only [Darboux.rho, hfix w h1 h2] using this
  have hvan : ∀ Δ ∈ schA F (κ' ⊕ κ''), (∀ a : κ' → AF F, Δ (a ⊕ᵥ 0) = 0) →
      ∀ a : κ' → AF F, om x Δ (a ⊕ᵥ 0) = 0 := by
    intro Δ hΔ hz a
    have hl := hsp.adm x _ ((GlobalTheory.T.adelicSchwartz_pointValues_admitted F ψ hψ (κ' ⊕ κ'')).1 (a ⊕ᵥ 0))
    have key := hP F ψ hψ κ' κ'' _ hl ?_ Δ hΔ hz
    · simpa using key
    · intro y Ψ hΨ
      obtain ⟨w, hw'⟩ := hw 0 y
      have e0 : ((0 : κ' → AF F) ⊕ᵥ (0 : κ'' → AF F)) = 0 := Sum.elim_zero_zero
      have hw0 : dd.e w = ((0 : κ' ⊕ κ'' → AF F), Sum.elim (0 : κ' → AF F) y) := by
        rw [hw', e0]
      have hrho : (fun z : κ' ⊕ κ'' → AF F => ψ ((z ∘ Sum.inr) ⬝ᵥ y) * Ψ z) = schr ψ (dd.e w) Ψ := by
        rw [hw0, schr_char]
      have h1 : (dd.e w).1 ∘ Sum.inl = 0 := by rw [hw0]; rfl
      have h2 : (dd.e w).2 ∘ Sum.inl = 0 := by rw [hw0]; rfl
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.proj_apply]
      rw [hrho, hcomm w h1 h2 Ψ hΨ, hw0, schr_char]
      simp
  refine ⟨?_, ?_⟩
  · intro Ψ hΨ
    have hs : slice0 κ' κ'' Ψ ∈ schA F κ' := (hS F κ' κ'').1 Ψ hΨ
    have hB := GlobalTheory.SchwartzBox.boxFun_mem_schA F κ' κ'' _ hs φ₀ hφ₀
    have hD := hvan (Ψ - boxFun (slice0 κ' κ'' Ψ) φ₀) (Submodule.sub_mem _ hΨ hB) (by
      intro a
      simp [slice0, boxFun, h0])
    funext a
    have := hD a
    rw [map_sub, Pi.sub_apply, sub_eq_zero] at this
    simpa [slice0] using this
  · intro φ' hφ' φ'' hφ''
    funext z
    obtain ⟨w, hw'⟩ := hw (z ∘ Sum.inr) 0
    have e0 : ((0 : κ' → AF F) ⊕ᵥ (0 : κ'' → AF F)) = 0 := Sum.elim_zero_zero
    have hw0 : dd.e w = (Sum.elim (0 : κ' → AF F) (z ∘ Sum.inr), (0 : κ' ⊕ κ'' → AF F)) := by
      rw [hw', e0]
    have h1 : (dd.e w).1 ∘ Sum.inl = 0 := by rw [hw0]; rfl
    have h2 : (dd.e w).2 ∘ Sum.inl = 0 := by rw [hw0]; rfl
    have hzs : z = (z ∘ Sum.inl ⊕ᵥ 0) + Sum.elim (0 : κ' → AF F) (z ∘ Sum.inr) := by
      funext i
      cases i <;> simp
    have hbox := GlobalTheory.SchwartzBox.boxFun_mem_schA F κ' κ'' _ hφ' φ'' hφ''
    set η := schr ψ (z ∘ Sum.inr, 0) φ'' with hη
    have hηm : η ∈ schA F κ'' := (GlobalTheory.T.adelicSchwartz_pointValues_admitted F ψ hψ κ'').2.2.1 _ φ'' hφ''
    have hη0 : η 0 = φ'' (z ∘ Sum.inr) := by
      rw [hη, schr_transl, zero_add]
    have hL : om x (boxFun φ' φ'') z = om x (boxFun φ' η) (z ∘ Sum.inl ⊕ᵥ 0) := by
      rw [hη, box_transl, ← hw0, hcomm w h1 h2 _ hbox, hw0, schr_transl, ← hzs]
    have hB1 := GlobalTheory.SchwartzBox.boxFun_mem_schA F κ' κ'' _ hφ' η hηm
    have hB2 := GlobalTheory.SchwartzBox.boxFun_mem_schA F κ' κ'' _ hφ' φ₀ hφ₀
    have hD := hvan (boxFun φ' η - η 0 • boxFun φ' φ₀)
      (Submodule.sub_mem _ hB1 (Submodule.smul_mem _ _ hB2)) (by
        intro a
        simp [boxFun, h0]
        ring)
      (z ∘ Sum.inl)
    rw [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, sub_eq_zero, smul_eq_mul] at hD
    rw [hL, hD, hη0]
    simp [boxFun, slice0, mul_comm]

end PositivityTheory.SiegelWeilFormula.Ald

end
end

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

theorem modelEx_wired (hD : SDarb) (hP : PartCharInv) (hC : ChartFacts) (hG : SiegelSmall) (hS : SmallS) : ModelEx :=
  modelEx_of hD PositivityTheory.SiegelWeilFormula.Ldexa.sEv bigT sliceFacts (opBox_of hP sliceFacts) (subSplit_of sliceFacts) hC hG hS

end PositivityTheory.SiegelWeilFormula.Ald

end
