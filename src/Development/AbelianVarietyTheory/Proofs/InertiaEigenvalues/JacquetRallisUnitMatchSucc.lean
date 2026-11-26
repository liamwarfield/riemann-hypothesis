module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisUnitMatchStepOfOneLeNorm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdelicAbsDetPowDiagonalUniformizerMul
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PartialFourierPreservesTestFixesUnit
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeilRepSL2HermitianBlock

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowMap
open Matrix MeasureTheory

noncomputable section

namespace GlobalTheory.JR.WeilMix

variable {r : ℕ} {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [StarRing E]

def ptrB (M : Meas r F E) (ψ : AddChar F ℂ) (f : Gl r F → ℂ) (Y : Gl r F) : ℂ :=
  letI := M.mF
  ∫ b, f (Y.1, b, Y.2.2.1, Y.2.2.2) * ψ (b ⬝ᵥ Y.2.1) ∂(Measure.pi fun _ : Fin r => M.μF)

def rowMap (g : SpecialLinearGroup (Fin 2) F) (Y : Gl r F) : Gl r F :=
  (Y.1, fun i => Y.2.2.1 i * (g : Matrix (Fin 2) (Fin 2) F) 0 1 + Y.2.1 i * (g : Matrix (Fin 2) (Fin 2) F) 1 1,
    fun i => Y.2.2.1 i * (g : Matrix (Fin 2) (Fin 2) F) 0 0 + Y.2.1 i * (g : Matrix (Fin 2) (Fin 2) F) 1 0, Y.2.2.2)

def rowAct (g : SpecialLinearGroup (Fin 2) F) (h : Gl r F → ℂ) (Y : Gl r F) : ℂ := h (rowMap g Y)

def weil (M : Meas r F E) (ψ : AddChar F ℂ) (g : SpecialLinearGroup (Fin 2) F) (f : Gl r F → ℂ) : Gl r F → ℂ :=
  ptrB M ψ (ptrB M ψ (ptrB M ψ (rowAct g (ptrB M ψ f))))

def negB (f : Gl r F → ℂ) (Y : Gl r F) : ℂ := f (Y.1, -Y.2.1, Y.2.2.1, Y.2.2.2)

end GlobalTheory.JR.WeilMix
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeilRepSL2GlBorderedBlock
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MixedModelPartialFourierColumnTwiceNegColumn
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MixedModelPartialFourierColumnTwiceNegColumn
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.PartialInv

def intLat (F : Type) [NormedField F] [IsUltrametricDist F] (r : ℕ) : AddSubgroup (Fin r → F) where
  carrier := Set.univ.pi fun _ => Metric.closedBall (0 : F) 1
  zero_mem' := by intro i _; simp
  add_mem' := by
    intro a b ha hb i _
    have h1 := ha i trivial
    have h2 := hb i trivial
    simp only [mem_closedBall_zero_iff] at h1 h2 ⊢
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)
  neg_mem' := by
    intro a ha i _
    have h1 := ha i trivial
    simpa using h1

theorem mem_intLat {F : Type} [NormedField F] [IsUltrametricDist F] {r : ℕ} (x : Fin r → F) :
    x ∈ intLat F r ↔ ∀ i, ‖x i‖ ≤ 1 := by
  change x ∈ Set.univ.pi (fun _ => Metric.closedBall (0 : F) 1) ↔ _
  simp [Set.mem_pi]

theorem isTest_slice {F : Type} [NormedField F] {r : ℕ} {f : Gl r F → ℂ} (hf : IsTest f)
    (A : Matrix (Fin r) (Fin r) F) (c : Fin r → F) (l : F) : IsTest fun v : Fin r → F => f (A, v, c, l) := by
  have hc : Continuous fun v : Fin r → F => ((A, v, c, l) : Gl r F) := by fun_prop
  refine ⟨hf.1.comp_continuous hc, ?_⟩
  have he : IsClosedEmbedding fun v : Fin r → F => ((A, v, c, l) : Gl r F) := by
    refine Function.LeftInverse.isClosedEmbedding (f := fun Y : Gl r F => Y.2.1) (fun _ => rfl) (by fun_prop) hc
  exact hf.2.comp_isClosedEmbedding he

theorem selfDual_pi (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) :
    letI := M.mF
    SelfDual (Measure.pi fun _ : Fin r => M.μF) (fun x y : Fin r → F => ψ (x ⬝ᵥ y)) := by
  letI := M.mF
  haveI := M.bF
  haveI := M.haarF
  haveI : IsUltrametricDist F := Unram.ultraF E
  haveI : LocallyCompactSpace F := Unram.lcF E
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  have hcond := ((GlobalTheory.T.unramifiedStandardAddChar_conductor_properties F E).2 ψ hψ).2.2.1
  have hsymm : LinearMap.BilinForm.IsSymm (dotProductBilin F F : LinearMap.BilinForm F (Fin r → F)) :=
    ⟨fun x y => by simp [dotProduct_comm]⟩
  have hnd : LinearMap.BilinForm.Nondegenerate (dotProductBilin F F : LinearMap.BilinForm F (Fin r → F)) := by
    constructor
    · intro x hx
      ext i
      simpa using hx (Pi.single i 1)
    · intro x hx
      ext i
      simpa using hx (Pi.single i 1)
  have hopen : IsOpen (intLat F r : Set (Fin r → F)) :=
    isOpen_set_pi Set.finite_univ fun _ _ => IsUltrametricDist.isOpen_closedBall _ one_ne_zero
  have hcpt : IsCompact (intLat F r : Set (Fin r → F)) :=
    isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hvol : (Measure.pi fun _ : Fin r => M.μF) (intLat F r : Set (Fin r → F)) = 1 := by
    change (Measure.pi fun _ : Fin r => M.μF) (Set.univ.pi fun _ => Metric.closedBall (0 : F) 1) = 1
    rw [Measure.pi_pi]
    simp [M.volF]
  have hdual : {y : Fin r → F | ∀ x ∈ intLat F r,
      ψ ((dotProductBilin F F : LinearMap.BilinForm F (Fin r → F)) x y) = 1} = (intLat F r : Set (Fin r → F)) := by
    ext y
    simp only [Set.mem_setOf_eq, SetLike.mem_coe, mem_intLat, dotProductBilin_apply_apply]
    constructor
    · intro h i
      refine (hcond (y i)).1 fun e he => ?_
      have := h (Pi.single i e) (fun j => by
        by_cases hj : j = i
        · subst hj; simpa using he
        · simp [hj])
      simpa using this
    · intro h x hx
      refine hψ.1 _ ?_
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
      rw [norm_mul]
      exact mul_le_one₀ (hx i) (norm_nonneg _) (h i)
  have key := ((GlobalTheory.T.selfDual_iff_lattice_volume_and_plancherel_alt F E ψ hψ (Fin r → F) (dotProductBilin F F) hsymm hnd
    (Measure.pi fun _ : Fin r => M.μF) inferInstance).1 (intLat F r) hopen hcpt).1
  rw [hdual, hvol] at key
  exact key.2 (mul_one 1)

theorem ptrB_ptrB (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ)
    (f : Gl r F → ℂ) (hf : IsTest f) : WeilMix.ptrB M ψ (WeilMix.ptrB M ψ f) = WeilMix.negB f := by
  funext Y
  exact (selfDual_pi F E r M ψ hψ).2 _ (isTest_slice hf Y.1 Y.2.2.1 Y.2.2.2) Y.2.1

end GlobalTheory.JR.PartialInv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MixedModelPartialFourierColumnTwiceNegColumnStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedModelPartialFourierColumn_twice_neg_column : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ f : Gl r F → ℂ, IsTest f → WeilMix.ptrB M ψ (WeilMix.ptrB M ψ f) = WeilMix.negB f := by
  first | exact @GlobalTheory.JR.PartialInv.ptrB_ptrB | exact GlobalTheory.JR.PartialInv.ptrB_ptrB | (intros; apply GlobalTheory.JR.PartialInv.ptrB_ptrB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MixedModelPartialFourierLinear
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MixedModelPartialFourierLinear
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.WeilMix

theorem integrable_mixedModel_partialFourier_integrand {F : Type} [NontriviallyNormedField F] [LocallyCompactSpace F]
    [MeasurableSpace F] [BorelSpace F] {r : ℕ} (μ : Measure F) [μ.IsAddHaarMeasure]
    (ψ : AddChar F ℂ) (hψ : IsLocallyConstant (fun x => ψ x))
    (f : Gl r F → ℂ) (hf : IsTest f) (Y : Gl r F) :
    Integrable (fun b : Fin r → F => f (Y.1, b, Y.2.2.1, Y.2.2.2) * ψ (b ⬝ᵥ Y.2.1))
      (Measure.pi fun _ : Fin r => μ) := by
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  have hc : Continuous (fun b : Fin r → F => f (Y.1, b, Y.2.2.1, Y.2.2.2) * ψ (b ⬝ᵥ Y.2.1)) := by
    refine Continuous.mul ?_ ?_
    · exact hf.1.continuous.comp (by fun_prop)
    · exact hψ.continuous.comp (by fun_prop)
  refine hc.integrable_of_hasCompactSupport ?_
  have hK : IsCompact ((fun Z : Gl r F => Z.2.1) '' tsupport f) := hf.2.isCompact.image (by fun_prop)
  refine HasCompactSupport.intro hK ?_
  intro b hb
  have : (Y.1, b, Y.2.2.1, Y.2.2.2) ∉ tsupport f := fun h => hb ⟨_, h, rfl⟩
  simp [image_eq_zero_of_notMem_tsupport this]

end GlobalTheory.JR.WeilMix

theorem GlobalTheory.JR.WeilMix.ptrB_linear : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (c : ℂ) (f f' : Gl r F → ℂ), IsTest f → IsTest f' → WeilMix.ptrB M ψ (c • f + f') = c • WeilMix.ptrB M ψ f + WeilMix.ptrB M ψ f' := by
  intro F E _ _ _ _ hU r M ψ hψ c f f' hf hf'
  letI := M.mF
  haveI := M.bF
  haveI := M.haarF
  haveI : LocallyCompactSpace F := hU.lcF
  have hlc : IsLocallyConstant (fun x => ψ x) := ((GlobalTheory.T.unramifiedStandardAddChar_conductor_properties F E).2 ψ hψ).1
  funext Y
  have h1 := WeilMix.integrable_mixedModel_partialFourier_integrand M.μF ψ hlc f hf Y
  have h2 := WeilMix.integrable_mixedModel_partialFourier_integrand M.μF ψ hlc f' hf' Y
  simp only [WeilMix.ptrB, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_assoc]
  rw [integral_add (h1.const_mul c) h2, integral_const_mul]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MixedModelPartialFourierLinearStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedModelPartialFourier_linear : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (c : ℂ) (f f' : Gl r F → ℂ), IsTest f → IsTest f' → WeilMix.ptrB M ψ (c • f + f') = c • WeilMix.ptrB M ψ f + WeilMix.ptrB M ψ f' := by
  first | exact @GlobalTheory.JR.WeilMix.ptrB_linear | exact GlobalTheory.JR.WeilMix.ptrB_linear | (intros; apply GlobalTheory.JR.WeilMix.ptrB_linear <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MixedModelWeylElementEqPartialFourier
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MixedModelWeylElementEqPartialFourier
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem GlobalTheory.JR.WeilMix.negB_ptrB_wS_ptrB : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ f : Gl r F → ℂ, IsTest f → WeilMix.negB (WeilMix.ptrB M ψ (WeilMix.rowAct (wS F) (WeilMix.ptrB M ψ f))) = fourG M ψ f := by
  intro F E _ _ _ _ hU r M ψ hψ f hf
  letI := M.mF
  haveI := M.bF
  haveI := M.haarF
  haveI : LocallyCompactSpace F := hU.lcF
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  have hψc : Continuous (fun x => ψ x) := ((GlobalTheory.T.unramifiedStandardAddChar_conductor_properties F E).2 ψ hψ).1.continuous
  funext Y
  obtain ⟨A, b, c, l⟩ := Y
  have hw : ((wS F : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; -1, 0] := rfl
  simp only [WeilMix.negB, WeilMix.ptrB, WeilMix.rowAct, WeilMix.rowMap, fourG, hw]
  simp
  set μ : Measure (Fin r → F) := Measure.pi fun _ : Fin r => M.μF with hμ
  haveI : μ.IsNegInvariant := Measure.IsAddHaarMeasure.isNegInvariant_of_regular μ
  set G : (Fin r → F) → ℂ := fun x => (∫ b', f (A, b', x, l) * ψ (b' ⬝ᵥ c) ∂μ) * ψ (x ⬝ᵥ b) with hG
  set H : (Fin r → F) → (Fin r → F) → ℂ := fun x b' => f (A, b', x, l) * ψ (b' ⬝ᵥ c) * ψ (x ⬝ᵥ b) with hH
  have hHc : Continuous (Function.uncurry H) := by
    have h1 : Continuous (fun p : (Fin r → F) × (Fin r → F) => f (A, p.2, p.1, l)) :=
      hf.1.continuous.comp (by fun_prop)
    have h2 : Continuous (fun p : (Fin r → F) × (Fin r → F) => ψ (p.2 ⬝ᵥ c)) :=
      hψc.comp (continuous_snd.dotProduct continuous_const)
    have h3 : Continuous (fun p : (Fin r → F) × (Fin r → F) => ψ (p.1 ⬝ᵥ b)) :=
      hψc.comp (continuous_fst.dotProduct continuous_const)
    exact (h1.mul h2).mul h3
  have hHs : HasCompactSupport (Function.uncurry H) := by
    refine HasCompactSupport.intro ((hf.2.isCompact).image
      (show Continuous (fun Y : Gl r F => (Y.2.2.1, Y.2.1)) by fun_prop)) ?_
    intro p hp
    by_contra hne
    apply hp
    refine ⟨(A, p.2, p.1, l), subset_tsupport _ ?_, rfl⟩
    intro h0
    apply hne
    simp [Function.uncurry, H, h0]
  have hint : Integrable (Function.uncurry H) (μ.prod μ) := hHc.integrable_of_hasCompactSupport hHs
  calc _ = ∫ x, G (-x) ∂μ := by
        congr 1; funext x; simp only [G, neg_dotProduct, neg_neg]; rfl
    _ = ∫ x, G x ∂μ := integral_neg_eq_self G μ
    _ = ∫ x, ∫ b', H x b' ∂μ ∂μ := by
        congr 1; funext x; simp only [G, H]; rw [integral_mul_const]
    _ = ∫ b', ∫ x, H x b' ∂μ ∂μ := integral_integral_swap hint
    _ = _ := by
        congr 1; funext b'; congr 1; funext x
        simp only [H]
        rw [mul_assoc, ← AddChar.map_add_eq_mul, dotProduct_comm b' c, add_comm]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MixedModelWeylElementEqPartialFourierStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedModel_weylElement_eq_partialFourier : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ f : Gl r F → ℂ, IsTest f → WeilMix.negB (WeilMix.ptrB M ψ (WeilMix.rowAct (wS F) (WeilMix.ptrB M ψ f))) = fourG M ψ f := by
  first | exact @GlobalTheory.JR.WeilMix.negB_ptrB_wS_ptrB | exact GlobalTheory.JR.WeilMix.negB_ptrB_wS_ptrB | (intros; apply GlobalTheory.JR.WeilMix.negB_ptrB_wS_ptrB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantCompactSupportMixedModelPartial
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantCompactSupportMixedModelPartial
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.WeilMix

theorem psi_isLocallyConstant {F : Type} [NontriviallyNormedField F] (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) :
    IsLocallyConstant (fun x => ψ x) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  filter_upwards [Metric.ball_mem_nhds x one_pos] with y hy
  have h1 : ψ (y - x) = 1 := hψ.1 _ (by rw [← dist_eq_norm]; exact (Metric.mem_ball.1 hy).le)
  calc ψ y = ψ (x + (y - x)) := by rw [add_sub_cancel]
    _ = ψ x := by rw [AddChar.map_add_eq_mul, h1, mul_one]

theorem isOpen_setOf_eq_of_isLocallyConstant {Y : Type} [TopologicalSpace Y] {g h : Y → ℂ}
    (hg : IsLocallyConstant g) (hh : IsLocallyConstant h) : IsOpen {p | g p = h p} := by
  rw [isOpen_iff_mem_nhds]
  intro p hp
  filter_upwards [(IsLocallyConstant.iff_eventually_eq g).1 hg p,
    (IsLocallyConstant.iff_eventually_eq h).1 hh p] with q h1 h2
  show g q = h q
  rw [h1, h2]; exact hp

theorem isTest_partialFourier {X F : Type} [TopologicalSpace X] [T2Space X] [NontriviallyNormedField F]
    [ProperSpace F] {r : ℕ} [MeasurableSpace (Fin r → F)] (μ : Measure (Fin r → F))
    (hμ : ∀ (g : (Fin r → F) → ℂ) (w : Fin r → F), ∫ b, g (b + w) ∂μ = ∫ b, g b ∂μ)
    (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) (f : X × (Fin r → F) → ℂ) (hf : IsTest f) :
    IsTest (fun p : X × (Fin r → F) => ∫ b, f (p.1, b) * ψ (b ⬝ᵥ p.2) ∂μ) := by
  obtain ⟨hfl, hfc⟩ := hf
  have hK : IsCompact (tsupport f) := hfc
  have hψl := psi_isLocallyConstant ψ hψ

  have hn1 : IsOpen {q : (X × (Fin r → F)) × (Fin r → F) | f (q.1.1, q.1.2 + q.2) = f q.1} :=
    isOpen_setOf_eq_of_isLocallyConstant (hfl.comp_continuous (by fun_prop))
      (hfl.comp_continuous continuous_fst)
  obtain ⟨u1, v1, -, hv1, hKu, h0v, huv⟩ :=
    generalized_tube_lemma hK (isCompact_singleton (x := (0 : Fin r → F))) hn1 (by
      rintro ⟨p, w⟩ ⟨-, hw⟩
      simp only [Set.mem_singleton_iff] at hw
      subst hw
      simp)
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hv1 0 (h0v rfl)
  have inv1 : ∀ x b (w : Fin r → F), ‖w‖ < δ → f (x, b + w) = f (x, b) := by
    intro x b w hw
    have hwv : w ∈ v1 := hball (by simpa using hw)
    by_cases hxb : (x, b) ∈ tsupport f
    · exact huv (⟨hKu hxb, hwv⟩ : ((x, b), w) ∈ u1 ×ˢ v1)
    · by_cases hxbw : (x, b + w) ∈ tsupport f
      · have hmw : -w ∈ v1 := hball (by simpa using hw)
        have := huv (⟨hKu hxbw, hmw⟩ : ((x, b + w), -w) ∈ u1 ×ˢ v1)
        simp only [Set.mem_setOf_eq, add_neg_cancel_right] at this
        exact this.symm
      · rw [image_eq_zero_of_notMem_tsupport hxb, image_eq_zero_of_notMem_tsupport hxbw]
  have hzero : ∀ x b, b ∉ Prod.snd '' tsupport f → f (x, b) = 0 := fun x b hb =>
    image_eq_zero_of_notMem_tsupport (fun h => hb ⟨_, h, rfl⟩)
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    rintro ⟨x0, u0⟩
    have hdot : Continuous fun q : (X × (Fin r → F)) × (Fin r → F) => q.2 ⬝ᵥ q.1.2 := by
      unfold dotProduct; fun_prop
    have hdot0 : Continuous fun q : (X × (Fin r → F)) × (Fin r → F) => q.2 ⬝ᵥ u0 := by
      unfold dotProduct; fun_prop
    have hn2 : IsOpen {q : (X × (Fin r → F)) × (Fin r → F) |
        f (q.1.1, q.2) * ψ (q.2 ⬝ᵥ q.1.2) = f (x0, q.2) * ψ (q.2 ⬝ᵥ u0)} :=
      isOpen_setOf_eq_of_isLocallyConstant
        ((hfl.comp_continuous (by fun_prop)).comp₂ (hψl.comp_continuous hdot) (· * ·))
        ((hfl.comp_continuous (by fun_prop)).comp₂ (hψl.comp_continuous hdot0) (· * ·))
    obtain ⟨u2, v2, hu2, -, hxu, hKv, hu2n⟩ :=
      generalized_tube_lemma (isCompact_singleton (x := (x0, u0))) (hK.image continuous_snd) hn2 (by
        rintro ⟨p, b⟩ ⟨hp, -⟩
        simp only [Set.mem_singleton_iff] at hp
        subst hp
        simp)
    filter_upwards [hu2.mem_nhds (hxu rfl)] with p hp
    refine integral_congr_ae (Eventually.of_forall fun b => ?_)
    by_cases hb : b ∈ Prod.snd '' tsupport f
    · exact hu2n (⟨hp, hKv hb⟩ : (p, b) ∈ u2 ×ˢ v2)
    · simp only [hzero _ _ hb, zero_mul]
  · obtain ⟨a, ha, -⟩ := hψ.2
    refine HasCompactSupport.intro
      ((hK.image continuous_fst).prod (isCompact_closedBall (0 : Fin r → F) (‖a‖ / δ))) ?_
    rintro ⟨x, u⟩ hxu
    rw [Set.mem_prod, not_and_or] at hxu
    rcases hxu with hx | hu
    · have h0 : ∀ b, f (x, b) = 0 := fun b =>
        image_eq_zero_of_notMem_tsupport (fun h => hx ⟨_, h, rfl⟩)
      simp [h0]
    · rw [mem_closedBall_zero_iff, not_le] at hu
      obtain ⟨i, hi⟩ : ∃ i, ‖a‖ / δ < ‖u i‖ := by
        by_contra h
        push_neg at h
        exact (not_le.2 hu) ((pi_norm_le_iff_of_nonneg (by positivity)).2 h)
      have hui : u i ≠ 0 := by
        intro h
        rw [h, norm_zero] at hi
        exact (not_lt.2 (by positivity)) hi
      classical
      have hw : ‖(Pi.single i (a / u i) : Fin r → F)‖ < δ := by
        rw [Pi.norm_single, norm_div, div_lt_iff₀ (norm_pos_iff.2 hui)]
        rw [div_lt_iff₀ hδ] at hi
        linarith
      have hwu : (Pi.single i (a / u i) : Fin r → F) ⬝ᵥ u = a := by
        rw [single_dotProduct]; field_simp
      have key := hμ (fun b => f (x, b) * ψ (b ⬝ᵥ u)) (Pi.single i (a / u i))
      have hsh : ∀ b, f (x, b + Pi.single i (a / u i)) * ψ ((b + Pi.single i (a / u i)) ⬝ᵥ u) =
          (f (x, b) * ψ (b ⬝ᵥ u)) * ψ a := by
        intro b
        rw [inv1 x b _ hw, add_dotProduct, AddChar.map_add_eq_mul, hwu]
        ring
      simp only [hsh, integral_mul_const] at key
      show ∫ b, f (x, b) * ψ (b ⬝ᵥ u) ∂μ = 0
      by_contra hI
      exact ha (mul_left_cancel₀ hI (key.trans (mul_one _).symm))

end GlobalTheory.JR.WeilMix

namespace GlobalTheory.JR.WeilMix

theorem ptrB_isTest : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ f : Gl r F → ℂ,
    IsTest f → IsTest (WeilMix.ptrB M ψ f) := by
  intro F E _ _ _ _ hU r M ψ hψ f hf
  letI := M.mF
  haveI := M.bF
  haveI := M.haarF
  haveI : LocallyCompactSpace F := hU.lcF
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  let eH : Gl r F ≃ₜ (Matrix (Fin r) (Fin r) F × (Fin r → F) × F) × (Fin r → F) :=
    { toFun := fun Y => ((Y.1, Y.2.2.1, Y.2.2.2), Y.2.1)
      invFun := fun p => (p.1.1, p.2, p.1.2.1, p.1.2.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hμ : ∀ (g : (Fin r → F) → ℂ) (w : Fin r → F),
      ∫ b, g (b + w) ∂(Measure.pi fun _ : Fin r => M.μF) = ∫ b, g b ∂(Measure.pi fun _ : Fin r => M.μF) :=
    fun g w => integral_add_right_eq_self g w
  have hg : IsTest (f ∘ eH.symm) := ⟨hf.1.comp_continuous eH.symm.continuous, hf.2.comp_homeomorph eH.symm⟩
  have h1 := isTest_partialFourier (Measure.pi fun _ : Fin r => M.μF) hμ ψ hψ (f ∘ eH.symm) hg
  exact ⟨h1.1.comp_continuous eH.continuous, h1.2.comp_homeomorph eH⟩

end GlobalTheory.JR.WeilMix
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantCompactSupportMixedModelPartialStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLocallyConstantCompactSupport_mixedModelPartialFourierColumn : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ f : Gl r F → ℂ, IsTest f → IsTest (WeilMix.ptrB M ψ f) := by
  first | exact @GlobalTheory.JR.WeilMix.ptrB_isTest | exact GlobalTheory.JR.WeilMix.ptrB_isTest | (intros; apply GlobalTheory.JR.WeilMix.ptrB_isTest <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeilRepSL2GlBorderedBlock
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.WeilMix

variable {r : ℕ} {F : Type} [NontriviallyNormedField F]

theorem rowMap_mul (g h : SpecialLinearGroup (Fin 2) F) (Y : Gl r F) :
    rowMap (g * h) Y = rowMap h (rowMap g Y) := by
  obtain ⟨A, u, c, l⟩ := Y
  simp only [rowMap, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, Prod.mk.injEq, true_and, and_true]
  constructor <;> funext i <;> ring

theorem rowMap_one (Y : Gl r F) : rowMap (1 : SpecialLinearGroup (Fin 2) F) Y = Y := by
  obtain ⟨A, u, c, l⟩ := Y
  simp [rowMap]

theorem continuous_rowMap (g : SpecialLinearGroup (Fin 2) F) : Continuous (rowMap (r := r) g) := by
  unfold rowMap
  fun_prop

theorem isTest_rowAct (g : SpecialLinearGroup (Fin 2) F) (h : Gl r F → ℂ) (hh : IsTest h) : IsTest (rowAct g h) := by
  let e : Gl r F ≃ₜ Gl r F :=
    { toFun := rowMap g, invFun := rowMap g⁻¹
      left_inv := fun Y => by simp [← rowMap_mul, rowMap_one]
      right_inv := fun Y => by simp [← rowMap_mul, rowMap_one]
      continuous_toFun := continuous_rowMap g, continuous_invFun := continuous_rowMap g⁻¹ }
  exact ⟨hh.1.comp_continuous (continuous_rowMap g), hh.2.comp_homeomorph e⟩

end GlobalTheory.JR.WeilMix

open GlobalTheory.JR.WeilMix in
theorem GlobalTheory.JR.weil_repG : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∃ W : SpecialLinearGroup (Fin 2) F → (Gl r F → ℂ) → Gl r F → ℂ, IsTestRep W ∧ ∀ f, IsTest f → (∀ t Y, W (nS t) f Y = ψ (t * mom Y 0) * f Y) ∧ W (wS F) f = fourG M ψ f := by
  intro F E _ _ _ _ _ r M ψ hψ
  have hT := GlobalTheory.T.isLocallyConstantCompactSupport_mixedModelPartialFourierColumn F E r M ψ hψ
  have hI := GlobalTheory.T.mixedModelPartialFourierColumn_twice_neg_column F E r M ψ hψ
  have hL := GlobalTheory.T.mixedModelPartialFourier_linear F E r M ψ hψ
  have hW := GlobalTheory.T.mixedModel_weylElement_eq_partialFourier F E r M ψ hψ
  have hψc : IsLocallyConstant (fun x : F => ψ x) := ((GlobalTheory.T.unramifiedStandardAddChar_conductor_properties F E).2 ψ hψ).1
  have h4 : ∀ f, IsTest f → ptrB M ψ (ptrB M ψ (ptrB M ψ (ptrB M ψ f))) = f := by
    intro f hf
    rw [hI _ (hT _ (hT _ hf)), hI _ hf]
    funext Y; simp [negB]
  refine ⟨weil M ψ, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro g f hf
    exact hT _ (hT _ (hT _ (isTest_rowAct g _ (hT _ hf))))
  · intro f hf
    have : rowAct (1 : SpecialLinearGroup (Fin 2) F) (ptrB M ψ f) = ptrB M ψ f := by
      funext Y; simp [rowAct, rowMap_one]
    simp only [weil, this]
    exact h4 f hf
  · intro g h f hf
    simp only [weil]
    rw [h4 _ (isTest_rowAct h _ (hT _ hf))]
    congr 3
    funext Y; simp [rowAct, rowMap_mul]
  · intro g c f f' hf hf'
    have hR : ∀ (a b : Gl r F → ℂ), rowAct g (c • a + b) = c • rowAct g a + rowAct g b := by
      intro a b; funext Y; simp [rowAct]
    simp only [weil]
    rw [hL c f f' hf hf', hR, hL _ _ _ (isTest_rowAct g _ (hT _ hf)) (isTest_rowAct g _ (hT _ hf')),
      hL _ _ _ (hT _ (isTest_rowAct g _ (hT _ hf))) (hT _ (isTest_rowAct g _ (hT _ hf'))),
      hL _ _ _ (hT _ (hT _ (isTest_rowAct g _ (hT _ hf)))) (hT _ (hT _ (isTest_rowAct g _ (hT _ hf'))))]
  · intro f hf
    refine ⟨fun t Y => ?_, ?_⟩
    · let ft : Gl r F → ℂ := fun Y => ψ (t * mom Y 0) * f Y
      have hft : IsTest ft := by
        refine ⟨IsLocallyConstant.mul (hψc.comp_continuous ?_) hf.1, hf.2.mul_left⟩
        simp only [mom, pow_zero, Matrix.one_mulVec]
        fun_prop
      have key : rowAct (nS t) (ptrB M ψ f) = ptrB M ψ ft := by
        funext Y
        obtain ⟨A, u, c, l⟩ := Y
        simp only [rowAct, rowMap, ptrB, nS, ft]
        congr 1
        funext b
        change f (A, b, (fun i => c i * 1 + u i * 0), l) *
          ψ (b ⬝ᵥ (fun i => c i * t + u i * 1)) = _
        simp only [mul_one, mul_zero, add_zero, mom, pow_zero, Matrix.one_mulVec]
        have hu : (fun i => c i * t + u i) = t • c + u := by funext i; simp [mul_comm]
        rw [hu, dotProduct_add, dotProduct_smul, smul_eq_mul, dotProduct_comm b c,
          AddChar.map_add_eq_mul]
        ring
      show ptrB M ψ (ptrB M ψ (ptrB M ψ (rowAct (nS t) (ptrB M ψ f)))) Y = _
      rw [key, h4 ft hft]
    · show ptrB M ψ (ptrB M ψ (ptrB M ψ (rowAct (wS F) (ptrB M ψ f)))) = _
      rw [hI _ (hT _ (isTest_rowAct _ _ (hT _ hf)))]
      exact hW f hf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeilRepSL2GlBorderedBlockStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weilRepSL2_glBorderedBlock : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∃ W : SpecialLinearGroup (Fin 2) F → (Gl r F → ℂ) → Gl r F → ℂ, IsTestRep W ∧ ∀ f, IsTest f → (∀ t Y, W (nS t) f Y = ψ (t * mom Y 0) * f Y) ∧ W (wS F) f = fourG M ψ f := by
  first | exact @GlobalTheory.JR.weil_repG | exact GlobalTheory.JR.weil_repG | (intros; apply GlobalTheory.JR.weil_repG <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisMatchingAdd
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisMatchingAdd
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem GlobalTheory.JR.MatchAdd.integrable_of_isTest {X : Type} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ] {f : X → ℂ} (hf : IsTest f) :
    Integrable f μ :=
  hf.1.continuous.integrable_of_hasCompactSupport hf.2

theorem GlobalTheory.JR.match_add : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (f₁' f₂' : Gl r F → ℂ) (f₁ f₂ : Hn r F E → ℂ), IsTest f₁' → IsTest f₂' → IsTest f₁ → IsTest f₂ → Match M f₁' f₁ → Match M f₂' f₂ → Match M (f₁' + f₂') (f₁ + f₂) := by
  intro F E _ _ _ _ _ r M f₁' f₂' f₁ f₂ h₁' h₂' h₁ h₂ m₁ m₂ a ha
  obtain ⟨hG, hU⟩ := GlobalTheory.T.jacquetRallis_orbitalIntegrand_isLocallyConstantCompactSupport F E r M
  obtain ⟨-, hsec, -⟩ := GlobalTheory.T.jacquetRallis_borderedMatrix_normalForm_invariants F r
  have ha' : Delta (inv (sec a)) ≠ 0 := by rw [hsec]; exact ha
  have eG : orbG M (f₁' + f₂') (sec a) = orbG M f₁' (sec a) + orbG M f₂' (sec a) := by
    letI := M.mG
    haveI := M.bG
    haveI := M.haarG
    unfold orbG
    simp only [Pi.add_apply, add_mul]
    exact integral_add (MatchAdd.integrable_of_isTest _ (hG _ h₁' _ ha'))
      (MatchAdd.integrable_of_isTest _ (hG _ h₂' _ ha'))
  have eU : ∀ X : Hn r F E, HasInv X a → orbU M (f₁ + f₂) X = orbU M f₁ X + orbU M f₂ X := by
    intro X hX
    letI := M.mU
    haveI := M.bU
    haveI := M.haarU
    unfold orbU
    simp only [Pi.add_apply]
    exact integral_add (MatchAdd.integrable_of_isTest _ (hU _ h₁ a X ha hX))
      (MatchAdd.integrable_of_isTest _ (hU _ h₂ a X ha hX))
  refine ⟨fun X hX => ?_, fun hn => ?_⟩
  · rw [eG, eU X hX, (m₁ a ha).1 X hX, (m₂ a ha).1 X hX]
  · rw [eG, (m₁ a ha).2 hn, (m₂ a ha).2 hn, add_zero]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisMatchingAddStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquetRallis_matching_add : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (f₁' f₂' : Gl r F → ℂ) (f₁ f₂ : Hn r F E → ℂ), IsTest f₁' → IsTest f₂' → IsTest f₁ → IsTest f₂ → Match M f₁' f₁ → Match M f₂' f₂ → Match M (f₁' + f₂') (f₁ + f₂) := by
  first | exact @GlobalTheory.JR.match_add | exact GlobalTheory.JR.match_add | (intros; apply GlobalTheory.JR.match_add <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Sl2GeneratedWeylUnipotent
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Sl2GeneratedWeylUnipotent
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.SLGen

theorem exists_unif (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [LocallyCompactSpace F] :
    ∃ ϖ : F, ϖ ≠ 0 ∧ ‖ϖ‖ < 1 ∧ ∀ y : F, ‖y‖ < 1 → ‖y‖ ≤ ‖ϖ‖ := by
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  have hK : IsCompact (Metric.ball (0 : F) 1) :=
    (isCompact_closedBall (0 : F) 1).of_isClosed_subset (IsUltrametricDist.isClosed_ball 0 1)
      Metric.ball_subset_closedBall
  obtain ⟨ϖ, hϖ, hmax⟩ := hK.exists_isMaxOn ⟨0, by simp⟩ continuous_norm.continuousOn
  have hϖ1 : ‖ϖ‖ < 1 := by simpa using hϖ
  have hle : ∀ y : F, ‖y‖ < 1 → ‖y‖ ≤ ‖ϖ‖ := fun y hy => hmax (by simpa using hy)
  obtain ⟨x, hx0, hx1⟩ := NormedField.exists_norm_lt_one F
  refine ⟨ϖ, ?_, hϖ1, hle⟩
  intro h
  have := hle x hx1
  rw [h, norm_zero] at this
  linarith

variable {F : Type} [Field F]

theorem nS_coe (z : F) : ((nS z : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1, z; 0, 1] := rfl

theorem wS_coe : ((wS F : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; -1, 0] := rfl

theorem wS_inv_coe :
    (((wS F)⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![0, -1; 1, 0] := by
  rw [Matrix.SpecialLinearGroup.coe_inv, wS_coe, Matrix.adjugate_fin_two]; simp

theorem diag_coe {ϖ : F} (hϖ : ϖ ≠ 0) :
    ((nS ϖ * ((wS F)⁻¹ * nS ϖ⁻¹ * wS F) * nS ϖ * (wS F)⁻¹ : SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = !![ϖ, 0; 0, ϖ⁻¹] := by
  simp only [Matrix.SpecialLinearGroup.coe_mul, nS_coe, wS_coe, wS_inv_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hϖ] <;> field_simp <;> ring

theorem conj_step {ϖ : F} (hϖ : ϖ ≠ 0) (t : F) :
    (nS ϖ * ((wS F)⁻¹ * nS ϖ⁻¹ * wS F) * nS ϖ * (wS F)⁻¹)⁻¹ * nS t *
      (nS ϖ * ((wS F)⁻¹ * nS ϖ⁻¹ * wS F) * nS ϖ * (wS F)⁻¹) = nS (ϖ⁻¹ ^ 2 * t) := by
  rw [mul_assoc, inv_mul_eq_iff_eq_mul]
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, diag_coe hϖ, nS_coe]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

theorem decomp (g : SpecialLinearGroup (Fin 2) F) (hc : (g : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0) :
    g = nS (((g : Matrix (Fin 2) (Fin 2) F) 0 0 - 1) / (g : Matrix (Fin 2) (Fin 2) F) 1 0) *
      ((wS F)⁻¹ * nS (-(g : Matrix (Fin 2) (Fin 2) F) 1 0) * wS F) *
      nS (((g : Matrix (Fin 2) (Fin 2) F) 1 1 - 1) / (g : Matrix (Fin 2) (Fin 2) F) 1 0) := by
  have hdet := g.2
  rw [Matrix.det_fin_two] at hdet
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, nS_coe, wS_coe, wS_inv_coe]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;>
    first | ring1 | linear_combination -hdet | linear_combination -2 * hdet | linear_combination hdet |
      linear_combination 2 * hdet

theorem eq_top_of (H : Subgroup (SpecialLinearGroup (Fin 2) F)) (hw : wS F ∈ H) (hn : ∀ t, nS t ∈ H) :
    H = ⊤ := by
  have hl : ∀ c : F, (wS F)⁻¹ * nS (-c) * wS F ∈ H := fun c =>
    H.mul_mem (H.mul_mem (H.inv_mem hw) (hn _)) hw
  have key : ∀ g : SpecialLinearGroup (Fin 2) F, (g : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 → g ∈ H := by
    intro g hc
    rw [decomp g hc]
    exact H.mul_mem (H.mul_mem (hn _) (hl _)) (hn _)
  rw [eq_top_iff]
  intro g _
  by_cases hc : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
  · have hdet := g.2
    rw [Matrix.det_fin_two, hc] at hdet
    have ha : (g : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := by
      intro h; rw [h] at hdet; simp at hdet
    set L1 : SpecialLinearGroup (Fin 2) F := (wS F)⁻¹ * nS (-(1 : F)) * wS F
    have h1 : L1 * g ∈ H := by
      apply key
      simp only [L1, Matrix.SpecialLinearGroup.coe_mul, nS_coe, wS_coe, wS_inv_coe]
      simp [Matrix.mul_apply, Fin.sum_univ_two, hc, ha]
    have : g = L1⁻¹ * (L1 * g) := by group
    rw [this]
    exact H.mul_mem (H.inv_mem (hl 1)) h1
  · exact key g hc

end GlobalTheory.JR.SLGen


open GlobalTheory.JR.SLGen in
theorem GlobalTheory.JR.sl2_closure_weyl_unipotent_eq_top :
    ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
      [Unram F E], Subgroup.closure ({wS F} ∪ {g | ∃ t : F, (∀ y : F, ‖y‖ < 1 → ‖t * y‖ ≤ 1) ∧ g = nS t}) = ⊤ := by
  intro F E _ _ _ _ hU
  haveI : IsUltrametricDist F := hU.ultraF
  haveI : LocallyCompactSpace F := hU.lcF
  set H := Subgroup.closure ({wS F} ∪ {g | ∃ t : F, (∀ y : F, ‖y‖ < 1 → ‖t * y‖ ≤ 1) ∧ g = nS t})
  obtain ⟨ϖ, hϖ0, hϖ1, hmax⟩ := exists_unif F
  have hw : wS F ∈ H := Subgroup.subset_closure (Or.inl rfl)
  have hS : ∀ t : F, (∀ y : F, ‖y‖ < 1 → ‖t * y‖ ≤ 1) → nS t ∈ H := fun t ht =>
    Subgroup.subset_closure (Or.inr ⟨t, ht, rfl⟩)
  have hball : ∀ t : F, ‖t‖ ≤ 1 → nS t ∈ H := fun t ht => hS t fun y hy => by
    rw [norm_mul]; nlinarith [norm_nonneg t, norm_nonneg y]
  have hinv : nS ϖ⁻¹ ∈ H := hS _ fun y hy => by
    have hp : 0 < ‖ϖ‖ := norm_pos_iff.2 hϖ0
    rw [norm_mul, norm_inv, inv_mul_le_iff₀ hp, mul_one]
    exact hmax y hy
  have hD : nS ϖ * ((wS F)⁻¹ * nS ϖ⁻¹ * wS F) * nS ϖ * (wS F)⁻¹ ∈ H :=
    H.mul_mem (H.mul_mem (H.mul_mem (hball _ hϖ1.le)
      (H.mul_mem (H.mul_mem (H.inv_mem hw) hinv) hw)) (hball _ hϖ1.le)) (H.inv_mem hw)
  have hstep : ∀ t, nS t ∈ H → nS (ϖ⁻¹ ^ 2 * t) ∈ H := fun t ht => by
    rw [← conj_step hϖ0 t]
    exact H.mul_mem (H.mul_mem (H.inv_mem hD) ht) hD
  have hpow : ∀ k : ℕ, ∀ t, nS t ∈ H → nS ((ϖ⁻¹ ^ 2) ^ k * t) ∈ H := by
    intro k
    induction k with
    | zero => intro t ht; simpa using ht
    | succ k ih => intro t ht; rw [pow_succ', mul_assoc]; exact hstep _ (ih t ht)
  have hall : ∀ x : F, nS x ∈ H := by
    intro x
    have hq : ‖ϖ ^ 2‖ < 1 := by rw [norm_pow]; nlinarith [norm_nonneg ϖ]
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / (‖x‖ + 1) by positivity) hq
    have h1 : ‖(ϖ ^ 2) ^ k * x‖ ≤ 1 := by
      rw [norm_mul, norm_pow]
      rw [lt_div_iff₀ (by positivity)] at hk
      nlinarith [norm_nonneg x, pow_nonneg (norm_nonneg (ϖ ^ 2)) k]
    have e : x = (ϖ⁻¹ ^ 2) ^ k * ((ϖ ^ 2) ^ k * x) := by
      rw [← mul_assoc, ← mul_pow, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hϖ0), one_pow, one_mul]
    rw [e]
    exact hpow k _ (hball _ h1)
  exact eq_top_of H hw hall
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Sl2GeneratedWeylUnipotentStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closure_weyl_and_integral_unipotents_eq_univ : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E], Subgroup.closure ({wS F} ∪ {g | ∃ t : F, (∀ y : F, ‖y‖ < 1 → ‖t * y‖ ≤ 1) ∧ g = nS t}) = ⊤ := by
  first | exact @GlobalTheory.JR.sl2_closure_weyl_unipotent_eq_top | exact GlobalTheory.JR.sl2_closure_weyl_unipotent_eq_top | (intros; apply GlobalTheory.JR.sl2_closure_weyl_unipotent_eq_top <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisUnitMatchSucc
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.UnitStep

section Basic
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

def qU {r : ℕ} (X : Hn r F E) : F := Algebra.trace F E (star X.2.1 ⬝ᵥ X.2.1) / 2

theorem mom_act_zero {r : ℕ} (g : GL (Fin r) F) (Y : Gl r F) : mom (act g Y) 0 = mom Y 0 := by
  simp only [mom, act, pow_zero, one_mulVec]
  rw [dotProduct_mulVec, vecMul_vecMul]
  have : ((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * (g : Matrix (Fin r) (Fin r) F) = 1 := by
    simp
  rw [this, vecMul_one]

theorem qU_actU {r : ℕ} (g : Matrix.unitaryGroup (Fin r) E) (X : Hn r F E) : qU (actU g X) = qU X := by
  simp only [qU, actU]
  congr 2
  rw [Matrix.star_mulVec, dotProduct_mulVec, vecMul_vecMul]
  have : (g.1)ᴴ * g.1 = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact (Matrix.mem_unitaryGroup_iff').1 g.2
  rw [this, vecMul_one]

theorem mom_sec_zero {r : ℕ} (a : Inv (r + 1) F) : mom (sec a) 0 = a.2.1 0 := by
  simp [mom, sec, dotProduct]

theorem qU_of_hasInv [Unram F E] {r : ℕ} {X : Hn (r + 1) F E} {a : Inv (r + 1) F} (h : HasInv X a) :
    qU X = mom (sec a) 0 := by
  have h1 := congrArg (fun p => p.2.1 0) h
  simp only [inv, Inv.map, Hn.toGl, mom] at h1
  rw [show ((0 : Fin (r + 1)) : ℕ) = 0 from rfl, pow_zero, one_mulVec] at h1
  rw [mom_sec_zero, qU, h1, Algebra.trace_algebraMap, Unram.finrank_eq]
  haveI := (Unram.charZero (F := F) (E := E))
  rw [nsmul_eq_mul]; push_cast; field_simp

theorem orbG_mul {r : ℕ} (M : Meas r F E) (φ : F → ℂ) (f' : Gl r F → ℂ) (Y : Gl r F) :
    orbG M (fun Y => φ (mom Y 0) * f' Y) Y = φ (mom Y 0) * orbG M f' Y := by
  simp only [orbG, mom_act_zero, mul_assoc]
  exact integral_const_mul _ _

theorem orbU_mul {r : ℕ} (M : Meas r F E) (φ : F → ℂ) (f : Hn r F E → ℂ) (X : Hn r F E) :
    orbU M (fun X => φ (qU X) * f X) X = φ (qU X) * orbU M f X := by
  simp only [orbU, qU_actU]
  exact integral_const_mul _ _

theorem matchAt_mul [Unram F E] {r : ℕ} (M : Meas (r + 1) F E) (φ : F → ℂ) {f' : Gl (r + 1) F → ℂ}
    {f : Hn (r + 1) F E → ℂ} {a : Inv (r + 1) F} (h : MatchAt M f' f a) :
    MatchAt M (fun Y => φ (mom Y 0) * f' Y) (fun X => φ (qU X) * f X) a :=
  ⟨fun X hX => by rw [orbG_mul, orbU_mul, h.1 X hX, qU_of_hasInv hX],
    fun hn => by rw [orbG_mul, h.2 hn, mul_zero]⟩

theorem matchAt_mul_zero [Unram F E] {r : ℕ} (M : Meas (r + 1) F E) (φ : F → ℂ) (f' : Gl (r + 1) F → ℂ)
    (f : Hn (r + 1) F E → ℂ) {a : Inv (r + 1) F} (h0 : φ (mom (sec a) 0) = 0) :
    MatchAt M (fun Y => φ (mom Y 0) * f' Y) (fun X => φ (qU X) * f X) a :=
  ⟨fun X hX => by rw [orbG_mul, orbU_mul, qU_of_hasInv hX, h0, zero_mul, zero_mul],
    fun _ => by rw [orbG_mul, h0, zero_mul]⟩

theorem matchAt_of_mul [Unram F E] {r : ℕ} (M : Meas (r + 1) F E) (φ : F → ℂ) {f' : Gl (r + 1) F → ℂ}
    {f : Hn (r + 1) F E → ℂ} {a : Inv (r + 1) F} (h0 : φ (mom (sec a) 0) ≠ 0)
    (h : MatchAt M (fun Y => φ (mom Y 0) * f' Y) (fun X => φ (qU X) * f X) a) : MatchAt M f' f a := by
  refine ⟨fun X hX => ?_, fun hn => ?_⟩
  · have := h.1 X hX
    rw [orbG_mul, orbU_mul, qU_of_hasInv hX] at this
    exact mul_left_cancel₀ h0 this
  · have := h.2 hn
    rw [orbG_mul] at this
    exact (mul_eq_zero.1 this).resolve_left h0

theorem match_zero {r : ℕ} (M : Meas r F E) : Match M (0 : Gl r F → ℂ) (0 : Hn r F E → ℂ) := by
  intro a _
  refine ⟨fun X _ => ?_, fun _ => ?_⟩ <;> simp [orbG, orbU]

theorem isTest_sub {X : Type} [TopologicalSpace X] {f g : X → ℂ} (hf : IsTest f) (hg : IsTest g) :
    IsTest (f - g) :=
  ⟨hf.1.sub hg.1, hf.2.sub hg.2⟩

theorem wS_inv : (wS F)⁻¹ = wS F * wS F * wS F := by
  refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  simp [wS, Matrix.mul_fin_two, Matrix.one_fin_two]

theorem nS_inv (t : F) : (nS t)⁻¹ = nS (-t) := by
  refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
  show (!![1, t; 0, 1] : Matrix (Fin 2) (Fin 2) F) * !![1, -t; 0, 1] = 1
  simp [Matrix.mul_fin_two, Matrix.one_fin_two]


variable (E) in
theorem submonoid_eq_top [Unram F E] (S : Submonoid (SpecialLinearGroup (Fin 2) F)) (hw : wS F ∈ S)
    (hn : ∀ t : F, (∀ y : F, ‖y‖ < 1 → ‖t * y‖ ≤ 1) → nS t ∈ S) (x : SpecialLinearGroup (Fin 2) F) : x ∈ S := by
  have hgen := GlobalTheory.T.closure_weyl_and_integral_unipotents_eq_univ F E
  have hx : x ∈ Subgroup.closure ({wS F} ∪ {g | ∃ t : F, (∀ y : F, ‖y‖ < 1 → ‖t * y‖ ≤ 1) ∧ g = nS t}) := by
    rw [hgen]; trivial
  rw [← Subgroup.mem_toSubmonoid, Subgroup.closure_toSubmonoid] at hx
  refine (Submonoid.closure_le (S := S)).2 ?_ hx
  rintro g ((hg | ⟨t, ht, rfl⟩) | hg)
  · rw [Set.mem_singleton_iff.1 hg]; exact hw
  · exact hn t ht
  · rcases hg with hg | ⟨t, ht, hg⟩
    · rw [Set.mem_singleton_iff] at hg
      rw [← inv_inv g, hg, wS_inv]; exact S.mul_mem (S.mul_mem hw hw) hw
    · rw [← inv_inv g, hg, nS_inv]
      exact hn (-t) (fun y hy => by rw [neg_mul, norm_neg]; exact ht y hy)

end Basic
end GlobalTheory.JR.UnitStep

namespace GlobalTheory.JR.UnitStep

theorem unitMatch_succ : WeilEt → GammaOne → ∀ r : ℕ, FourierMatch (r + 1) → UnitMatch r → UnitMatch (r + 1) := by
  intro hWe hGo r hF hU F E _ _ _ _ _ M
  obtain ⟨ψ, hψ⟩ := (GlobalTheory.T.unramifiedStandardAddChar_conductor_properties F E).1
  obtain ⟨W1, hW1r, hW1⟩ := GlobalTheory.T.exists_weilRepSL2_glBorderedBlock F E (r + 1) M ψ hψ
  obtain ⟨W2, hW2r, hW2⟩ := GlobalTheory.T.exists_weilRepSL2_hermitianBlock hWe hGo F E (r + 1) M ψ hψ
  obtain ⟨hTG, hTU, htG, htU, hfG, hfU⟩ := GlobalTheory.T.partialFourier_preserves_test_fixes_unit F E (r + 1) M ψ hψ

  have hN1 : ∀ f, IsTest f → ∀ t : F, W1 (nS t) f = fun Y => (fun z => ψ (t * z)) (mom Y 0) * f Y :=
    fun f hf t => funext fun Y => (hW1 f hf).1 t Y
  have hN2 : ∀ f, IsTest f → ∀ t : F, W2 (nS t) f = fun X => (fun z => ψ (t * z)) (qU X) * f X :=
    fun f hf t => funext fun X => by
      rw [(hW2 f hf).1 t X, qU, mul_div_assoc]

  let S : Submonoid (SpecialLinearGroup (Fin 2) F) :=
    { carrier := {g | ∀ f' f, IsTest f' → IsTest f → Match M f' f → Match M (W1 g f') (W2 g f)}
      one_mem' := fun f' f hf' hf hm => by rw [hW1r.2.1 f' hf', hW2r.2.1 f hf]; exact hm
      mul_mem' := fun {g h} hg hh f' f hf' hf hm => by
        rw [hW1r.2.2.1 g h f' hf', hW2r.2.2.1 g h f hf]
        exact hg _ _ (hW1r.1 h f' hf') (hW2r.1 h f hf) (hh f' f hf' hf hm) }
  have hS : ∀ g, g ∈ S := submonoid_eq_top E S
    (fun f' f hf' hf hm => by rw [(hW1 f' hf').2, (hW2 f hf).2]; exact hF F E M ψ hψ f' f hf' hf hm)
    (fun t _ f' f hf' hf hm => by
      rw [hN1 f' hf' t, hN2 f hf t]
      exact fun a ha => matchAt_mul M (fun z => ψ (t * z)) (hm a ha))

  let u' := unitG (r + 1) F
  let u := unitU (r + 1) F E
  let S' : Submonoid (SpecialLinearGroup (Fin 2) F) :=
    { carrier := {g | Match M (W1 g u' - u') (W2 g u - u)}
      one_mem' := by
        show Match M (W1 1 u' - u') (W2 1 u - u)
        rw [hW1r.2.1 u' htG, hW2r.2.1 u htU, sub_self, sub_self]; exact match_zero M
      mul_mem' := fun {g h} hg hh => by
        show Match M (W1 (g * h) u' - u') (W2 (g * h) u - u)
        have e1 : W1 (g * h) u' - u' = W1 g (W1 h u' - u') + (W1 g u' - u') := by
          have hs : W1 h u' - u' = (-1 : ℂ) • u' + W1 h u' := by
            funext Y; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
          rw [hW1r.2.2.1 g h u' htG, hs, hW1r.2.2.2 g (-1) u' (W1 h u') htG (hW1r.1 h u' htG)]
          funext Y; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
        have e2 : W2 (g * h) u - u = W2 g (W2 h u - u) + (W2 g u - u) := by
          have hs : W2 h u - u = (-1 : ℂ) • u + W2 h u := by
            funext X; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
          rw [hW2r.2.2.1 g h u htU, hs, hW2r.2.2.2 g (-1) u (W2 h u) htU (hW2r.1 h u htU)]
          funext X; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
        have d1 : IsTest (W1 h u' - u') := isTest_sub (hW1r.1 h u' htG) htG
        have d2 : IsTest (W2 h u - u) := isTest_sub (hW2r.1 h u htU) htU
        rw [e1, e2]
        exact GlobalTheory.T.jacquetRallis_matching_add F E (r + 1) M _ _ _ _ (hW1r.1 g _ d1) (isTest_sub (hW1r.1 g u' htG) htG)
          (hW2r.1 g _ d2) (isTest_sub (hW2r.1 g u htU) htU) (hS g _ _ d1 d2 hh) hg }
  have hD1 : ∀ t : F, W1 (nS t) u' - u' = fun Y => (fun z => ψ (t * z) - 1) (mom Y 0) * u' Y := by
    intro t; rw [hN1 u' htG t]; funext Y; simp only [Pi.sub_apply]; ring
  have hD2 : ∀ t : F, W2 (nS t) u - u = fun X => (fun z => ψ (t * z) - 1) (qU X) * u X := by
    intro t; rw [hN2 u htU t]; funext X; simp only [Pi.sub_apply]; ring
  have hS' : ∀ g, g ∈ S' := submonoid_eq_top E S'
    (by
      show Match M (W1 (wS F) u' - u') (W2 (wS F) u - u)
      rw [(hW1 u' htG).2, (hW2 u htU).2, hfG, hfU, sub_self, sub_self]; exact match_zero M)
    (fun t ht => by
      show Match M (W1 (nS t) u' - u') (W2 (nS t) u - u)
      rw [hD1 t, hD2 t]
      intro a ha
      by_cases h1 : 1 ≤ ‖mom (sec a) 0‖
      · exact matchAt_mul M (fun z => ψ (t * z) - 1) (GlobalTheory.T.jacquetRallisUnitMatch_step_of_one_le_norm r hU F E M a ha h1)
      · refine matchAt_mul_zero M (fun z => ψ (t * z) - 1) u' u ?_
        have : ‖t * mom (sec a) 0‖ ≤ 1 := ht _ (lt_of_not_ge h1)
        simp [hψ.1 _ this])

  refine (GlobalTheory.T.jacquetRallis_match_of_dense_separable F E (r + 1) M u' u htG htU).2 (Nat.succ_pos r) ?_
  intro a ha ha0
  obtain ⟨x, hx, -⟩ := hψ.2
  have hm := hS' (nS (x / mom (sec a) 0))
  change Match M (W1 (nS _) u' - u') (W2 (nS _) u - u) at hm
  rw [hD1, hD2] at hm
  refine matchAt_of_mul M (fun z => ψ (x / mom (sec a) 0 * z) - 1) ?_ (hm a ha)
  simp only [div_mul_cancel₀ x ha0]
  exact sub_ne_zero.2 hx

end GlobalTheory.JR.UnitStep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisUnitMatchSuccStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquetRallisUnitMatch_succ : WeilEt → GammaOne → ∀ r : ℕ, FourierMatch (r + 1) → UnitMatch r → UnitMatch (r + 1) := by
  first | exact @GlobalTheory.JR.UnitStep.unitMatch_succ | exact GlobalTheory.JR.UnitStep.unitMatch_succ | (intros; apply GlobalTheory.JR.UnitStep.unitMatch_succ <;> assumption)
end
