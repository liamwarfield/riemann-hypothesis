module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothConeFaceOfInteriorCommonPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormClearDenominatorsAwayFromPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticChangeOfGoodModelsIntertwines
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordinateChangeRealisedWithDouble
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureTranslateLevelRealBoxLeIndexMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerInvariantFunctionalsLagrangian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenBijectiveSchwartz

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelMapIntegrableDistribution
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackMemSB
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

namespace GlobalTheory.FinPull

theorem pullback_mem_SB : ∀ (F : Type) [Field F] [NumberField F] (ι κ : Type) [Fintype ι] [Fintype κ] (D : Matrix κ ι F),
    (∀ z : ι → F, D *ᵥ z = 0 → z = 0) →
    ∀ g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F),
      (fun w : ι → FiniteAdeleRing (𝓞 F) F => g (D.map (algebraMap F (FiniteAdeleRing (𝓞 F) F)) *ᵥ w)) ∈
        SB (ι → FiniteAdeleRing (𝓞 F) F) := by
  intro F _ _ ι κ _ _ D hD g hg
  haveI : T2Space (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  set A := algebraMap F (FiniteAdeleRing (𝓞 F) F)
  have hinj : Function.Injective (Matrix.toLin' D) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    exact hD z (by simpa using hz)
  obtain ⟨G, hG⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' D) (LinearMap.ker_eq_bot.mpr hinj)
  set L := LinearMap.toMatrix' G
  have hLD : L * D = 1 := by
    have : LinearMap.toMatrix' (G ∘ₗ Matrix.toLin' D) = LinearMap.toMatrix' LinearMap.id := by rw [hG]
    simpa [L, LinearMap.toMatrix'_comp] using this
  have hM : Continuous fun w : ι → FiniteAdeleRing (𝓞 F) F => D.map A *ᵥ w :=
    continuous_const.matrix_mulVec continuous_id
  have hN : Continuous fun w : κ → FiniteAdeleRing (𝓞 F) F => L.map A *ᵥ w :=
    continuous_const.matrix_mulVec continuous_id
  have hinv : Function.LeftInverse (fun w : κ → FiniteAdeleRing (𝓞 F) F => L.map A *ᵥ w)
      (fun w : ι → FiniteAdeleRing (𝓞 F) F => D.map A *ᵥ w) := fun w => by
    simp only [Matrix.mulVec_mulVec, ← Matrix.map_mul, hLD, Matrix.map_one A (map_zero A) (map_one A), Matrix.one_mulVec]
  exact ⟨hg.1.comp_continuous hM, hg.2.comp_isClosedEmbedding (hinv.isClosedEmbedding hN hM)⟩

end GlobalTheory.FinPull
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinMApply
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section
namespace GlobalTheory.ArchPull

variable {F : Type} [Field F] [NumberField F] {ι κ : Type} [Fintype ι] [Fintype κ]

def linM (D : Matrix κ ι F) :
    (ι → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) where
  toFun a := fun k => ∑ i, mixedEmbedding F (D k i) * a i
  map_add' a b := by funext k; simp [mul_add, Finset.sum_add_distrib]
  map_smul' c a := by funext k; simp [Finset.smul_sum, mul_smul_comm]

theorem linM_apply (D : Matrix κ ι F) (a : ι → mixedEmbedding.mixedSpace F) (k : κ) :
    linM D a k = ∑ i, mixedEmbedding F (D k i) * a i := rfl

theorem linM_mul (L : Matrix ι κ F) (D : Matrix κ ι F) (a : ι → mixedEmbedding.mixedSpace F) :
    linM L (linM D a) = linM (L * D) a := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [linM_apply, Finset.mul_sum, Matrix.mul_apply, map_sum, Finset.sum_mul, map_mul, mul_assoc]
  exact Finset.sum_comm

theorem linM_one (a : ι → mixedEmbedding.mixedSpace F) : linM (1 : Matrix ι ι F) a = a := by
  funext i
  simp [linM_apply, Matrix.one_apply]

theorem exists_leftInv (D : Matrix κ ι F) (hD : ∀ z : ι → F, D *ᵥ z = 0 → z = 0) :
    ∃ L : Matrix ι κ F, L * D = 1 := by
  have hinj : Function.Injective (Matrix.toLin' D) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz; exact hD z (by simpa using hz)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' D)
    (LinearMap.ker_eq_bot.2 hinj)
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  rw [← LinearMap.toMatrix'_toLin' D, ← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]

end GlobalTheory.ArchPull

open GlobalTheory.ArchPull in
theorem GlobalTheory.ArchPull.exists_pull : ∀ (F : Type) [Field F] [NumberField F] (ι κ : Type) [Fintype ι] [Fintype κ] (D : Matrix κ ι F),
    (∀ z : ι → F, D *ᵥ z = 0 → z = 0) →
    ∃ T : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] SchwartzMap (ι → mixedEmbedding.mixedSpace F) ℂ,
      ∀ (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (a : ι → mixedEmbedding.mixedSpace F),
        T f a = f (fun k => ∑ i, mixedEmbedding F (D k i) * a i) := by
  intro F _ _ ι κ _ _ D hD
  obtain ⟨L, hL⟩ := exists_leftInv D hD
  let M := LinearMap.toContinuousLinearMap (linM D)
  let N := LinearMap.toContinuousLinearMap (linM L)
  have hb : ∀ a, ‖a‖ ≤ ‖N‖₊ * ‖M a‖ := fun a => by
    have e : N (M a) = a := by
      change linM L (linM D a) = a
      rw [linM_mul, hL, linM_one]
    calc ‖a‖ = ‖N (M a)‖ := by rw [e]
      _ ≤ ‖N‖ * ‖M a‖ := N.le_opNorm _
      _ = _ := rfl
  have hl : AntilipschitzWith ‖N‖₊ M := ContinuousLinearMap.antilipschitz_of_bound M hb
  exact ⟨SchwartzMap.compCLMOfAntilipschitz ℂ M.hasTemperateGrowth hl, fun f a => rfl⟩
end
end

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section

namespace GlobalTheory.HaarPull

open GlobalTheory.DiagForm GlobalTheory.DiagUniq

attribute [local instance] GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele
  GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField
  GlobalTheory.DiagForm.measAf GlobalTheory.DiagForm.borelAf

variable {F : Type} [Field F] [NumberField F] {ι κ : Type} [Fintype ι] [Fintype κ]

theorem pureA_mulVec_glue (D : Matrix κ ι F) (f : (κ → mixedEmbedding.mixedSpace F) → ℂ)
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (p : Vi F ι × Vf F ι) :
    pureA F f g (D.map (algebraMap F (AF F)) *ᵥ glue p) =
      f (fun k => ∑ i, mixedEmbedding F (D k i) * eI F ι p.1 i) *
      g (D.map (algebraMap F (FiniteAdeleRing (𝓞 F) F)) *ᵥ p.2) := by
  unfold pureA
  congr 2 <;> funext k
  · refine ((map_sum ((InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp
        (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)))
        (fun i => algebraMap F (AF F) (D k i) * glue p i) Finset.univ)).trans ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    refine (map_mul _ _ _).trans ?_
    change InfiniteAdeleRing.ringEquiv_mixedSpace F (algebraMap F (InfiniteAdeleRing F) (D k i)) *
      InfiniteAdeleRing.ringEquiv_mixedSpace F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (eI F ι p.1 i)) = _
    rw [RingEquiv.apply_symm_apply, InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
  · exact (map_sum (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))
        (fun i => algebraMap F (AF F) (D k i) * glue p i) Finset.univ)

theorem integrable_SB {g : Vf F ι → ℂ} (hg : g ∈ SB (Vf F ι)) : Integrable g Measure.addHaar :=
  hg.1.continuous.integrable_of_hasCompactSupport hg.2

theorem pureA_glue_eq (D : Matrix κ ι F)
    (T : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] SchwartzMap (ι → mixedEmbedding.mixedSpace F) ℂ)
    (hT : ∀ (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (a : ι → mixedEmbedding.mixedSpace F),
        T f a = f (fun k => ∑ i, mixedEmbedding F (D k i) * a i))
    (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    (fun p : Vi F ι × Vf F ι => pureA F f g (D.map (algebraMap F (AF F)) *ᵥ glue p)) =
      fun p => SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (eI F ι) (T f) p.1 *
        g (D.map (algebraMap F (FiniteAdeleRing (𝓞 F) F)) *ᵥ p.2) := by
  funext p
  rw [pureA_mulVec_glue, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, hT]

theorem integrable_glue (D : Matrix κ ι F) (hD : ∀ z : ι → F, D *ᵥ z = 0 → z = 0)
    {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    Integrable (fun p : Vi F ι × Vf F ι => Φ (D.map (algebraMap F (AF F)) *ᵥ glue p)) (mu F ι) := by
  obtain ⟨T, hT⟩ := GlobalTheory.ArchPull.exists_pull F ι κ D hD
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    rw [pureA_glue_eq D T hT f g]
    exact (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (eI F ι) (T f)).integrable.mul_prod
      (integrable_SB (GlobalTheory.FinPull.pullback_mem_SB F ι κ D hD g hg))
  | zero => exact integrable_zero _ _ _
  | add x y _ _ hx hy => exact hx.add hy
  | smul c x _ hx => exact hx.smul c

end GlobalTheory.HaarPull

namespace GlobalTheory

open GlobalTheory.DiagForm GlobalTheory.DiagUniq GlobalTheory.HaarPull

theorem integral_pull_injective : ∀ (F : Type) [Field F] [NumberField F] (ι κ : Type) [Fintype ι] [Fintype κ] (D : Matrix κ ι F),
    (∀ z : ι → F, D *ᵥ z = 0 → z = 0) →
    ∀ ν : @Measure (ι → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
      (∀ Φ ∈ schA F κ, (letI : MeasurableSpace (ι → AF F) := borel _;
        Integrable (fun w => Φ (D.map (algebraMap F (AF F)) *ᵥ w)) ν)) ∧
      ∀ g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F), ∃ T : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] ℂ,
        ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, (letI : MeasurableSpace (ι → AF F) := borel _;
          ∫ w, pureA F f g (D.map (algebraMap F (AF F)) *ᵥ w) ∂ν) = T f := by
  intro F _ _ ι κ _ _ D hD ν hν
  letI : MeasurableSpace (ι → AF F) := borel _
  haveI : BorelSpace (ι → AF F) := ⟨rfl⟩
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := hν
  haveI : ((mu F ι).map (glueE F ι)).IsAddHaarMeasure := (glueE F ι).isAddHaarMeasure_map _
  have h := Measure.isAddLeftInvariant_eq_smul ν ((mu F ι).map (glueE F ι))
  set c := Measure.addHaarScalarFactor ν ((mu F ι).map (glueE F ι))
  have me := (glueE F ι).toHomeomorph.measurableEmbedding
  refine ⟨fun Φ hΦ => ?_, fun g hg => ?_⟩
  · rw [h]
    refine Integrable.smul_measure_nnreal ?_
    exact me.integrable_map_iff.2 (integrable_glue D hD hΦ)
  · obtain ⟨T, hT⟩ := GlobalTheory.ArchPull.exists_pull F ι κ D hD
    refine ⟨(((c : ℝ) : ℂ) * ∫ v, g (D.map (algebraMap F (FiniteAdeleRing (𝓞 F) F)) *ᵥ v) ∂(Measure.addHaar : Measure (Vf F ι))) •
      ((SchwartzMap.integralCLM ℂ (volume : Measure (Vi F ι))).comp
        ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (eI F ι)).comp T)), fun f => ?_⟩
    rw [h, integral_smul_nnreal_measure]
    change c • ∫ x, pureA F f g (D.map (algebraMap F (AF F)) *ᵥ x) ∂((mu F ι).map (glueE F ι).toHomeomorph) = _
    rw [me.integral_map]
    have e := pureA_glue_eq D T hT f g
    change c • ∫ p, (fun p : Vi F ι × Vf F ι => pureA F f g (D.map (algebraMap F (AF F)) *ᵥ glue p)) p ∂(mu F ι) = _
    rw [e, mu, integral_prod_mul (fun u : Vi F ι => SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (eI F ι) (T f) u)
      (fun v : Vf F ι => g (D.map (algebraMap F (FiniteAdeleRing (𝓞 F) F)) *ᵥ v))]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, SchwartzMap.integralCLM_apply,
      smul_eq_mul, NNReal.smul_def, Complex.real_smul]
    ring

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerLatticeIntegralNonvanishing
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section

namespace GlobalTheory.LagrFormNZ

theorem exists_leftInv {F : Type} [Field F] {κ : Type} [Fintype κ] {r : ℕ} (a : Fin r → κ → F)
    (ha : LinearIndependent F a) : ∃ C : Matrix (Fin r) κ F, ∀ j, C *ᵥ a j = Pi.single j 1 := by
  have hinj : Function.Injective (Fintype.linearCombination F a) :=
    linearIndependent_iff_injective_fintypeLinearCombination.mp ha
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective (Fintype.linearCombination F a)
    (LinearMap.ker_eq_bot.2 hinj)
  refine ⟨LinearMap.toMatrix' L, fun j => ?_⟩
  rw [LinearMap.toMatrix'_mulVec]
  have := LinearMap.congr_fun hL (Pi.single j 1)
  simpa [Fintype.linearCombination_apply_single] using this

theorem mulVec_sum_eq {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {r : ℕ} (a : Fin r → κ → F)
    (C : Matrix (Fin r) κ F) (hC : ∀ j, C *ᵥ a j = Pi.single j 1) (x : Fin r → AF F) :
    C.map (algebraMap F (AF F)) *ᵥ (∑ j, x j • fun k => algebraMap F (AF F) (a j k)) = x := by
  funext i
  have h1 : ∀ j, (C.map (algebraMap F (AF F)) *ᵥ fun k => algebraMap F (AF F) (a j k)) i =
      algebraMap F (AF F) ((Pi.single j (1 : F) : Fin r → F) i) := fun j => by
    rw [← hC j, RingHom.map_mulVec]; rfl
  rw [Matrix.mulVec_sum, Finset.sum_apply]
  simp only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, h1]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [Pi.single_apply, Ne.symm hj]
  · simp

end GlobalTheory.LagrFormNZ

namespace GlobalTheory.LagrFormNZ

theorem lagrForm_ne_zero : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    (r : ℕ) (u : Fin r → (κ → F) × (κ → F)), LinearIndependent F (fun j => (u j).1) →
    ∀ μ : @Measure (Fin r → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∃ φ ∈ schA F κ, ∫ x, schr ψ (∑ j, x j • ((fun k => algebraMap F (AF F) ((u j).1 k)),
      (fun k => algebraMap F (AF F) ((u j).2 k)))) φ 0 ∂μ ≠ 0 := by
  intro F _ _ ψ hψ κ _ r u hu μ hμ
  letI : MeasurableSpace (Fin r → AF F) := borel _
  haveI : BorelSpace (Fin r → AF F) := ⟨rfl⟩
  haveI := hμ
  obtain ⟨C, hC⟩ := exists_leftInv (fun j => (u j).1) hu
  set U : Fin r → (κ → AF F) × (κ → AF F) := fun j => ((fun k => algebraMap F (AF F) ((u j).1 k)),
    (fun k => algebraMap F (AF F) ((u j).2 k))) with hU
  set Cm : Matrix (Fin r) κ (AF F) := C.map (algebraMap F (AF F)) with hCm
  have hfst : ∀ x : Fin r → AF F, (∑ j, x j • U j).1 = ∑ j, x j • fun k => algebraMap F (AF F) ((u j).1 k) := by
    intro x; simp [U, Prod.fst_sum]
  have hleft : ∀ x : Fin r → AF F, Cm *ᵥ (∑ j, x j • U j).1 = x := fun x => by
    rw [hfst]; exact mulVec_sum_eq (fun j => (u j).1) C hC x
  have hXc : Continuous fun x : Fin r → AF F => ∑ j, x j • U j :=
    continuous_finsetSum _ fun j _ => (continuous_apply j).smul continuous_const
  set H : (Fin r → AF F) → ℂ := fun x => ψ (0 ⬝ᵥ (∑ j, x j • U j).2 +
    ⅟(2 : AF F) * ((∑ j, x j • U j).1 ⬝ᵥ (∑ j, x j • U j).2)) with hH
  have hHc : Continuous H := hψ.1.comp ((continuous_const.dotProduct (continuous_snd.comp hXc)).add
    (continuous_const.mul ((continuous_fst.comp hXc).dotProduct (continuous_snd.comp hXc))))
  set G : (κ → AF F) → ℂ := fun y => H (Cm *ᵥ y) with hGdef
  have hGc : Continuous G := hHc.comp (Continuous.matrix_mulVec continuous_const continuous_id)
  have hG0 : G 0 = 1 := by simp [G, H]
  have hV : {y | 0 < (G y).re} ∈ 𝓝 (0 : κ → AF F) :=
    (isOpen_lt continuous_const (Complex.continuous_re.comp hGc)).mem_nhds (by simp [hG0])
  set e := GlobalTheory.ArchimedeanL2.splitEquiv F κ with he
  have he0 : e.symm (0, 0) = 0 := map_zero e.symm
  have hW : e.symm ⁻¹' {y | 0 < (G y).re} ∈ 𝓝 ((0 : κ → mixedEmbedding.mixedSpace F), (0 : κ → Af F)) := by
    have hV' : {y | 0 < (G y).re} ∈ 𝓝 (e.symm (0, 0)) := by rw [he0]; exact hV
    exact e.symm.continuous.tendsto (0, 0) hV'
  obtain ⟨U1, hU1, U2, hU2, hsub⟩ := mem_nhds_prod_iff.1 hW
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hU1
  obtain ⟨c, hc0, hcs⟩ := GlobalTheory.EvAdm.exists_scaledInt_subset_of_mem_nhds F κ U2 hU2
  let b : ContDiffBump (0 : κ → mixedEmbedding.mixedSpace F) := ⟨δ / 2, δ, half_pos hδ, half_lt_self hδ⟩
  have h1 : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) :=
    b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  let f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ :=
    h1.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff)
  have hf : ∀ x, f x = ((b x : ℝ) : ℂ) := fun x => rfl
  set S : Set (κ → Af F) := {y | y - 0 ∈ GlobalTheory.EvAdm.scaledInt F κ c} with hS
  set g : (κ → Af F) → ℂ := S.indicator (fun _ => (1 : ℂ)) with hg
  have hgSB : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) := GlobalTheory.EvAdm.indicator_coset_scaledInt_mem_SB F κ c hc0 0
  set φ := pureA F f g with hφ
  have hφmem : φ ∈ schA F κ := Submodule.subset_span ⟨f, g, hgSB, rfl⟩
  have hφe : ∀ y, φ y = f (e y).1 * g (e y).2 := fun y => rfl
  refine ⟨φ, hφmem, ?_⟩
  have hφcases : ∀ y, φ y = ((b (e y).1 : ℝ) : ℂ) ∧ (e y).2 ∈ S ∨ φ y = 0 ∧ (e y).2 ∉ S := by
    intro y
    rw [hφe, hf]
    by_cases hq : (e y).2 ∈ S
    · left; simp [g, Set.indicator_of_mem hq, hq]
    · right; simp [g, Set.indicator_of_notMem hq, hq]
  have hφim : ∀ y, (φ y).im = 0 := fun y => by
    rcases hφcases y with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h]
  have hφre : ∀ y, 0 ≤ (φ y).re := fun y => by
    rcases hφcases y with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h, b.nonneg]
  have hφmemK : ∀ y, φ y ≠ 0 → (e y).1 ∈ Metric.ball (0 : κ → mixedEmbedding.mixedSpace F) δ ∧
      (e y).2 ∈ (GlobalTheory.EvAdm.scaledInt F κ c : Set (κ → Af F)) := by
    intro y hy
    rcases hφcases y with ⟨h, hq⟩ | ⟨h, _⟩
    · refine ⟨?_, by simpa [S] using hq⟩
      have : b (e y).1 ≠ 0 := by
        intro h0; apply hy; rw [h, h0]; simp
      have hs : (e y).1 ∈ Function.support b := this
      rw [b.support_eq] at hs
      exact hs
    · exact absurd h hy
  have hφV : ∀ y, φ y ≠ 0 → 0 < (G y).re := by
    intro y hy
    obtain ⟨h1, h2⟩ := hφmemK y hy
    have : e y ∈ U1 ×ˢ U2 := ⟨hball h1, hcs h2⟩
    have := hsub this
    simpa using this
  have hφ0 : φ 0 = 1 := by
    have e0 : e 0 = (0, 0) := map_zero e
    rw [hφe, e0, hf]
    have hb : b 0 = 1 := b.one_of_mem_closedBall (Metric.mem_closedBall_self (half_pos hδ).le)
    have h0S : (0 : κ → Af F) ∈ S := by simp [S]
    simp [g, Set.indicator_of_mem h0S, hb]
  have hφc : Continuous φ := by
    have hg : Continuous g := hgSB.1.continuous
    exact (f.continuous.comp (continuous_fst.comp e.continuous)).mul (hg.comp (continuous_snd.comp e.continuous))
  set I : (Fin r → AF F) → ℂ := fun x => schr ψ (∑ j, x j • U j) φ 0 with hIdef
  have hI : ∀ x, I x = G (∑ j, x j • U j).1 * φ (∑ j, x j • U j).1 := by
    intro x
    show ψ _ * φ (0 + _) = H (Cm *ᵥ _) * _
    rw [hleft, zero_add]
  have hIc : Continuous I := by
    have : I = fun x => G (∑ j, x j • U j).1 * φ (∑ j, x j • U j).1 := funext hI
    rw [this]
    exact (hGc.comp (continuous_fst.comp hXc)).mul (hφc.comp (continuous_fst.comp hXc))

  set K : Set ((κ → mixedEmbedding.mixedSpace F) × (κ → Af F)) :=
    Metric.closedBall 0 δ ×ˢ (GlobalTheory.EvAdm.scaledInt F κ c : Set (κ → Af F)) with hK
  have hKc : IsCompact K := (isCompact_closedBall _ _).prod (GlobalTheory.EvAdm.isCompact_scaledInt_of_ne_zero hc0)
  have hKcl : IsClosed K := Metric.isClosed_closedBall.prod
    ((GlobalTheory.EvAdm.scaledInt F κ c).isClosed_of_isOpen (GlobalTheory.EvAdm.isOpen_scaledInt c))
  set T : Set (Fin r → AF F) := {x | e (∑ j, x j • U j).1 ∈ K} with hT
  have hTcl : IsClosed T := hKcl.preimage (e.continuous.comp (continuous_fst.comp hXc))
  have hTsub : T ⊆ (fun p => Cm *ᵥ e.symm p) '' K := by
    intro x hx
    exact ⟨_, hx, by simp only [e.symm_apply_apply, hleft]⟩
  have hes : Continuous (e.symm : _ → _) := e.symm.continuous
  have hcm : Continuous fun p => Cm *ᵥ e.symm p := Continuous.matrix_mulVec continuous_const hes
  have hTc : IsCompact T := (hKc.image hcm).of_isClosed_subset hTcl hTsub
  have hsupp : Function.support I ⊆ T := by
    intro x hx
    have hne : φ (∑ j, x j • U j).1 ≠ 0 := by
      intro h0; apply hx; rw [hI, h0, mul_zero]
    obtain ⟨h1, h2⟩ := hφmemK _ hne
    exact ⟨Metric.ball_subset_closedBall h1, h2⟩
  have hIcs : HasCompactSupport I := hTc.of_isClosed_subset (isClosed_tsupport I) (closure_minimal hsupp hTcl)
  have hIint : Integrable I μ := hIc.integrable_of_hasCompactSupport hIcs
  have hre : ∀ x, (I x).re = (G (∑ j, x j • U j).1).re * (φ (∑ j, x j • U j).1).re := by
    intro x; rw [hI, Complex.mul_re, hφim, mul_zero, sub_zero]
  have hnn : 0 ≤ fun x => (I x).re := by
    intro x
    show 0 ≤ (I x).re
    rw [hre]
    by_cases h0 : φ (∑ j, x j • U j).1 = 0
    · simp [h0]
    · exact mul_nonneg (hφV _ h0).le (hφre _)
  have hI0 : (I 0).re = 1 := by
    rw [hre]
    have : (∑ j, (0 : Fin r → AF F) j • U j).1 = 0 := by simp
    rw [this, hG0, hφ0]; simp
  have hpos : 0 < ∫ x, (I x).re ∂μ := by
    rw [integral_pos_iff_support_of_nonneg hnn hIint.re]
    exact (Complex.continuous_re.comp hIc).isOpen_support.measure_pos μ ⟨0, by simp [Function.mem_support, hI0]⟩
  intro hzero
  have := integral_re hIint
  change ∫ x, (I x).re ∂μ = (∫ x, I x ∂μ).re at this
  rw [show (∫ x, I x ∂μ) = 0 from hzero, Complex.zero_re] at this
  exact hpos.ne' this

end GlobalTheory.LagrFormNZ
end
end

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling
open GlobalTheory.SWLit
namespace GlobalTheory.StdRescale

theorem exists_isStd_mulShift : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
    ∃ a : F, a ≠ 0 ∧ IsStd (ψ.mulShift (algebraMap F (AF F) a)) := by
  intro F _ _ hF ψ h
  haveI := hF
  obtain ⟨a₀, ha₀, hinf⟩ := GlobalTheory.AdeleCharConductor.exists_scaling h
  have him : ∀ (w : InfinitePlace F) (x : F), (w.embedding x).im = 0 := fun w x => by
    have := congrArg Complex.im (GlobalTheory.AdeleCharConductor.embedding_re w x)
    simpa using this.symm
  have hkey : ∀ w : InfinitePlace F, (w.embedding a₀).re * (w.embedding (-a₀⁻¹)).re = -1 := fun w => by
    have := congrArg Complex.re
      (show w.embedding (a₀ * -a₀⁻¹) = -1 by rw [mul_neg, mul_inv_cancel₀ ha₀, map_neg, map_one])
    rw [map_mul, Complex.mul_re, him, him, mul_zero, sub_zero] at this
    simpa using this
  refine ⟨-a₀⁻¹, neg_ne_zero.2 (inv_ne_zero ha₀), ?_, ?_, ?_⟩
  · exact h.1.comp (continuous_const.mul continuous_id)
  · intro x
    rw [AddChar.mulShift_apply, ← map_mul]
    exact h.2.2.1 _
  · intro b hb
    have hu : evI F (pairA F 0 1) = 0 := by
      show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
      exact map_zero _
    have hb2 : b.2 = 0 := by
      have h0 := congrArg Prod.snd (hb (pairA F 0 1) hu)
      change (1 : Af F) * b.2 = 0 at h0
      rwa [one_mul] at h0
    have e1 : algebraMap F (AF F) (-a₀⁻¹) * b = pairA F (algebraMap F (Ainf F) (-a₀⁻¹) * b.1) 0 := by
      refine Prod.ext rfl ?_
      change (algebraMap F (AF F) (-a₀⁻¹)).2 * b.2 = 0
      rw [hb2, mul_zero]
    have hterm : ∀ w : InfinitePlace F, (w.embedding a₀).re *
        (InfinitePlace.Completion.extensionEmbedding w ((algebraMap F (Ainf F) (-a₀⁻¹) * b.1) w)).re =
        -(InfinitePlace.Completion.extensionEmbedding w (b.1 w)).re := fun w => by
      rw [show (algebraMap F (Ainf F) (-a₀⁻¹) * b.1) w = algebraMap F (Ainf F) (-a₀⁻¹) w * b.1 w from rfl, map_mul, GlobalTheory.AdeleCharConductor.extensionEmbedding_algebraMap, Complex.mul_re, him,
        zero_mul, sub_zero, ← mul_assoc, hkey, neg_one_mul]
    rw [AddChar.mulShift_apply, e1]
    show psiInf F ψ _ = _
    rw [hinf, GlobalTheory.WrongSignPair.trace_evI]
    simp only [hterm, Finset.sum_neg_distrib]
    push_cast
    ring_nf

end GlobalTheory.StdRescale
