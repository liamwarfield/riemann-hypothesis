module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FiniteAndFinrankLeOfPointwise
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedFrameSumPositive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfIsSmoothModerate
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TamePartRight

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxChangeRealisedCompAndReindex
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxChangeRealisedCompAndReindex
open scoped TensorProduct NNReal ENNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.TowU

noncomputable section

namespace GlobalTheory.TowU.RealComp

variable {F : Type} [Field F] [NumberField F]

theorem isOp_comp {ψ : AddChar (AF F) ℂ} {κ κ' κ'' : Type} [Fintype κ] [Fintype κ'] [Fintype κ'']
    {s : (κ → AF F) × (κ → AF F) → (κ' → AF F) × (κ' → AF F)}
    {t : (κ' → AF F) × (κ' → AF F) → (κ'' → AF F) × (κ'' → AF F)}
    {S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)} {S' : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)}
    {T : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ'' → AF F) → ℂ)} {T' : ((κ'' → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)}
    (hs : IsOp ψ s S S') (ht : IsOp ψ t T T') : IsOp ψ (t ∘ s) (T ∘ₗ S) (S' ∘ₗ T') := by
  exact
    { pres φ h := ht.pres _ (hs.pres φ h)
      pres' φ h := hs.pres' _ (ht.pres' φ h)
      left φ h := by simp only [LinearMap.comp_apply]; rw [ht.left _ (hs.pres φ h), hs.left φ h]
      right φ h := by simp only [LinearMap.comp_apply]; rw [hs.right _ (ht.pres' φ h), ht.right φ h]
      adm l hl := by rw [← LinearMap.comp_assoc]; exact hs.adm _ (ht.adm l hl)
      adm' l hl := by rw [← LinearMap.comp_assoc]; exact ht.adm' _ (hs.adm' l hl)
      Heisenberg₂ w φ h := by
        simp only [LinearMap.comp_apply, Function.comp_apply]
        rw [hs.Heisenberg₂ w φ h, ht.Heisenberg₂ _ _ (hs.pres φ h)]
      theta := by
        obtain ⟨c₁, hc₁, e₁⟩ := hs.theta
        obtain ⟨c₂, hc₂, e₂⟩ := ht.theta
        exact ⟨c₂ * c₁, mul_ne_zero hc₂ hc₁, fun φ h => by
          simp only [LinearMap.comp_apply]; rw [e₂ _ (hs.pres φ h), e₁ φ h, mul_assoc]⟩
      norm μ μ'' hμ hμ'' := by
        letI : MeasurableSpace (κ' → AF F) := borel _
        haveI : BorelSpace (κ' → AF F) := ⟨rfl⟩
        haveI : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
        obtain ⟨c₁, h1, h1', e₁⟩ := hs.norm μ Measure.addHaar hμ inferInstance
        obtain ⟨c₂, h2, h2', e₂⟩ := ht.norm Measure.addHaar μ'' inferInstance hμ''
        exact ⟨c₂ * c₁, mul_ne_zero h2 h1, ENNReal.mul_ne_top h2' h1', fun φ h => by
          simp only [LinearMap.comp_apply]; rw [e₂ _ (hs.pres φ h), e₁ φ h, mul_assoc]⟩ }

theorem dblAct_comp {κ κ' κ'' : Type} (s : (κ → AF F) × (κ → AF F) → (κ' → AF F) × (κ' → AF F))
    (t : (κ' → AF F) × (κ' → AF F) → (κ'' → AF F) × (κ'' → AF F)) :
    dblAct (t ∘ s) = dblAct t ∘ dblAct s := by
  funext w
  refine Prod.ext ?_ ?_ <;> funext a <;> rcases a with a | a <;> simp [dblAct]

end GlobalTheory.TowU.RealComp

namespace GlobalTheory.TowU.RealComp

open IsDedekindDomain

variable {F : Type} [Field F] [NumberField F]

theorem isOp2_comp {ψ : AddChar (AF F) ℂ} {κ κ' κ'' : Type} [Fintype κ] [Fintype κ'] [Fintype κ'']
    {s : (κ → AF F) × (κ → AF F) → (κ' → AF F) × (κ' → AF F)}
    {t : (κ' → AF F) × (κ' → AF F) → (κ'' → AF F) × (κ'' → AF F)}
    {S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)} {S' : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)}
    {T : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ'' → AF F) → ℂ)} {T' : ((κ'' → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)}
    (hs : IsOp2 ψ s S S') (ht : IsOp2 ψ t T T') : IsOp2 ψ (t ∘ s) (T ∘ₗ S) (S' ∘ₗ T') := by
  obtain ⟨hs1, Sd, Sd', hsd, hsb⟩ := hs
  obtain ⟨ht1, Td, Td', htd, htb⟩ := ht
  have hc : ∀ {ι : Type} [Fintype ι], ∀ φ ∈ schA F ι, star φ ∈ schA F ι := fun φ h => GlobalTheory.ConjSch.conj_mem_schA φ h
  refine ⟨isOp_comp hs1 ht1, Td ∘ₗ Sd, Sd' ∘ₗ Td', ?_, fun φ₁ h₁ φ₂ h₂ => ?_⟩
  · rw [dblAct_comp]; exact isOp_comp hsd htd
  · simp only [LinearMap.comp_apply]
    rw [hsb φ₁ h₁ φ₂ h₂, htb _ (hs1.pres _ h₁) _ (hc _ (hs1.pres _ (hc _ h₂))), star_star]

variable {κ κ' : Type} [Fintype κ] [Fintype κ']

def addRe {X : Type} [TopologicalSpace X] [AddCommGroup X] (e : κ' ≃ κ) : (κ' → X) ≃ₜ+ (κ → X) where
  toFun x := x ∘ e.symm
  invFun y := y ∘ e
  left_inv x := by funext i; simp
  right_inv y := by funext i; simp
  map_add' _ _ := rfl
  continuous_toFun := continuous_pi fun i => continuous_apply _
  continuous_invFun := continuous_pi fun i => continuous_apply _

def reix {R : Type} (e : κ' ≃ κ) : ((κ → R) → ℂ) →ₗ[ℂ] ((κ' → R) → ℂ) :=
  LinearMap.funLeft ℂ ℂ (fun x : κ' → R => x ∘ e.symm)

theorem reix_apply {R : Type} (e : κ' ≃ κ) (φ : (κ → R) → ℂ) (x : κ' → R) : reix e φ x = φ (x ∘ e.symm) := rfl

theorem reix_symm_reix {R : Type} (e : κ' ≃ κ) (φ : (κ → R) → ℂ) : reix e.symm (reix e φ) = φ := by
  funext x; simp only [reix_apply, Equiv.symm_symm]; congr 1; funext i; simp

def linRe (e : κ' ≃ κ) : (κ' → mixedEmbedding.mixedSpace F) ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F) :=
  (LinearEquiv.funCongrLeft ℝ (mixedEmbedding.mixedSpace F) e.symm).toContinuousLinearEquiv

theorem sb_reix (e : κ' ≃ κ) {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    (fun y : κ' → FiniteAdeleRing (𝓞 F) F => g (y ∘ e.symm)) ∈ SB (κ' → FiniteAdeleRing (𝓞 F) F) :=
  ⟨hg.1.comp_continuous (addRe e).continuous, hg.2.comp_homeomorph (addRe e).toHomeomorph⟩

theorem reix_pureA (e : κ' ≃ κ) (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    reix e (pureA F f g) = pureA F (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (linRe e) f)
      (fun y => g (y ∘ e.symm)) := by
  funext x
  rfl

theorem reix_mem_schA (e : κ' ≃ κ) {φ : (κ → AF F) → ℂ} (h : φ ∈ schA F κ) : reix e φ ∈ schA F κ' := by
  have hle : schA F κ ≤ (schA F κ').comap (reix e) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨f, g, hg, rfl⟩
    exact Submodule.subset_span ⟨_, _, sb_reix e hg, reix_pureA e f g⟩
  exact hle h

theorem reix_adm (e : κ' ≃ κ) {l : ((κ' → AF F) → ℂ) →ₗ[ℂ] ℂ} (hl : l ∈ (adeleClass F).adm κ') :
    l ∘ₗ reix e ∈ (adeleClass F).adm κ := by
  intro g hg
  obtain ⟨T, hT⟩ := hl _ (sb_reix e hg)
  exact ⟨T.comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (linRe e)), fun f => by
    rw [LinearMap.comp_apply, reix_pureA]; exact hT _⟩

theorem reix_theta (e : κ' ≃ κ) (φ : (κ → AF F) → ℂ) : thetaSum F (reix e φ) = thetaSum F φ :=
  (Equiv.arrowCongr e (Equiv.refl F)).tsum_eq (fun ξ : κ → F => φ (fun i => algebraMap F (AF F) (ξ i)))

theorem reix_heis (ψ : AddChar (AF F) ℂ) (e : κ' ≃ κ) (w : (κ → AF F) × (κ → AF F)) (φ : (κ → AF F) → ℂ) :
    reix e (schr ψ w φ) = schr ψ (w.1 ∘ e, w.2 ∘ e) (reix e φ) := by
  have hd : ∀ u v : κ → AF F, (u ∘ e) ⬝ᵥ (v ∘ e) = u ⬝ᵥ v := fun u v => by
    simp only [dotProduct, Function.comp_apply]; exact Equiv.sum_comp e (fun i => u i * v i)
  funext x
  simp only [reix_apply, schr]
  have h1 : (x ∘ e.symm) ⬝ᵥ w.2 = x ⬝ᵥ (w.2 ∘ e) := by
    rw [← hd]; congr 1; funext i; simp
  have h2 : x ∘ e.symm + w.1 = (x + w.1 ∘ e) ∘ e.symm := by funext i; simp
  rw [h1, h2, hd]

theorem reix_norm (e : κ' ≃ κ) (μ : @Measure (κ → AF F) (borel _)) (μ' : @Measure (κ' → AF F) (borel _))
    (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) (hμ' : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ') :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ φ : (κ → AF F) → ℂ,
      ∫⁻ x, ‖reix e φ x‖ₑ ^ 2 ∂μ' = c * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ := by
  letI : MeasurableSpace (κ → AF F) := borel _
  letI : MeasurableSpace (κ' → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  haveI : BorelSpace (κ' → AF F) := ⟨rfl⟩
  haveI : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := hμ
  haveI := hμ'
  let L : (κ' → AF F) ≃ₜ+ (κ → AF F) := addRe e
  haveI : (μ'.map L).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map μ' L
  have heq := Measure.isAddLeftInvariant_eq_smul (μ'.map L) μ
  refine ⟨(Measure.addHaarScalarFactor (μ'.map L) μ : ℝ≥0∞),
    ENNReal.coe_ne_zero.mpr (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne', ENNReal.coe_ne_top,
    fun φ => ?_⟩
  have hm := lintegral_map_equiv (fun y => ‖φ y‖ₑ ^ 2) L.toHomeomorph.toMeasurableEquiv (μ := μ')
  have hL : (⇑L.toHomeomorph.toMeasurableEquiv : (κ' → AF F) → (κ → AF F)) = ⇑L := rfl
  rw [hL, heq, lintegral_smul_measure] at hm
  rw [ENNReal.smul_def, smul_eq_mul] at hm
  exact hm.symm

end GlobalTheory.TowU.RealComp

namespace GlobalTheory.TowU.RealComp

variable {F : Type} [Field F] [NumberField F] {κ κ' : Type} [Fintype κ] [Fintype κ']

theorem isOp_reix (ψ : AddChar (AF F) ℂ) (e : κ' ≃ κ) :
    IsOp ψ (fun w : (κ → AF F) × (κ → AF F) => (w.1 ∘ e, w.2 ∘ e)) (reix e) (reix e.symm) := by
  exact
    { pres _ h := reix_mem_schA e h
      pres' _ h := reix_mem_schA e.symm h
      left φ _ := reix_symm_reix e φ
      right φ _ := by simpa using reix_symm_reix e.symm φ
      adm _ hl := reix_adm e hl
      adm' _ hl := reix_adm e.symm hl
      Heisenberg₂ w φ _ := reix_heis ψ e w φ
      theta := ⟨1, one_ne_zero, fun φ _ => by rw [reix_theta, one_mul]⟩
      norm μ μ' hμ hμ' := by
        obtain ⟨c, h0, h1, h⟩ := reix_norm e μ μ' hμ hμ'
        exact ⟨c, h0, h1, fun φ _ => h φ⟩ }

theorem dblAct_reix (e : κ' ≃ κ) :
    dblAct (fun w : (κ → AF F) × (κ → AF F) => (w.1 ∘ e, w.2 ∘ e)) =
      fun w => (w.1 ∘ Equiv.sumCongr e e, w.2 ∘ Equiv.sumCongr e e) := by
  funext w
  refine Prod.ext ?_ ?_ <;> funext a <;> rcases a with a | a <;> simp [dblAct]

theorem isOp2_reix (ψ : AddChar (AF F) ℂ) (e : κ' ≃ κ) :
    IsOp2 ψ (fun w : (κ → AF F) × (κ → AF F) => (w.1 ∘ e, w.2 ∘ e)) (reix e) (reix e.symm) := by
  refine ⟨isOp_reix ψ e, reix (Equiv.sumCongr e e), reix (Equiv.sumCongr e e).symm, ?_, fun φ₁ _ φ₂ _ => ?_⟩
  · rw [dblAct_reix]; exact isOp_reix ψ _
  · funext x
    simp only [reix_apply, boxFun, Pi.star_apply, star_star]
    congr 2 <;> funext i <;> simp

theorem realised_comp_reix : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → (∀ (κ κ' κ'' : Type) [Fintype κ] [Fintype κ'] [Fintype κ''] (s : (κ → AF F) × (κ → AF F) → (κ' → AF F) × (κ' → AF F)) (t : (κ' → AF F) × (κ' → AF F) → (κ'' → AF F) × (κ'' → AF F)) (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)) (S' : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (T : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ'' → AF F) → ℂ)) (T' : ((κ'' → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)), IsOp2 ψ s S S' → IsOp2 ψ t T T' → IsOp2 ψ (t ∘ s) (T ∘ₗ S) (S' ∘ₗ T')) ∧ ∀ (κ κ' : Type) [Fintype κ] [Fintype κ'] (e : κ' ≃ κ), ∃ (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)) (S' : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)), IsOp2 ψ (fun w => (w.1 ∘ e, w.2 ∘ e)) S S' :=
  fun _ _ _ ψ _ => ⟨fun _ _ _ _ _ _ _ _ _ _ _ _ hs ht => isOp2_comp hs ht, fun _ _ _ _ e => ⟨_, _, isOp2_reix ψ e⟩⟩

end GlobalTheory.TowU.RealComp

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxChangeRealisedCompAndReindexStatement
open scoped TensorProduct NNReal ENNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.TowU

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.darbouxChange_realised_comp_and_reindex : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → (∀ (κ κ' κ'' : Type) [Fintype κ] [Fintype κ'] [Fintype κ''] (s : (κ → AF F) × (κ → AF F) → (κ' → AF F) × (κ' → AF F)) (t : (κ' → AF F) × (κ' → AF F) → (κ'' → AF F) × (κ'' → AF F)) (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)) (S' : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (T : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ'' → AF F) → ℂ)) (T' : ((κ'' → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)), IsOp2 ψ s S S' → IsOp2 ψ t T T' → IsOp2 ψ (t ∘ s) (T ∘ₗ S) (S' ∘ₗ T')) ∧ ∀ (κ κ' : Type) [Fintype κ] [Fintype κ'] (e : κ' ≃ κ), ∃ (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)) (S' : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)), IsOp2 ψ (fun w => (w.1 ∘ e, w.2 ∘ e)) S S' := by
  first | exact @GlobalTheory.TowU.RealComp.realised_comp_reix | exact GlobalTheory.TowU.RealComp.realised_comp_reix | (intros; apply GlobalTheory.TowU.RealComp.realised_comp_reix <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffDerivHeisenbergCMRealLineTheta
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffDerivHeisenbergCMRealLineTheta
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff

noncomputable section

namespace GlobalTheory.ThetaLineSmoothF

open Formalism.IndefR.DatumF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

section Form

variable (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ : E)

theorem symplOHF_add_left (x x' y : WOF F E nS nT) :
    symplOHF σ JS JT ξ (x + x') y = symplOHF σ JS JT ξ x y + symplOHF σ JS JT ξ x' y := by
  unfold symplOHF symplOF hOF
  simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib, map_add (f := _)]

theorem symplOHF_add_right (x y y' : WOF F E nS nT) :
    symplOHF σ JS JT ξ x (y + y') = symplOHF σ JS JT ξ x y + symplOHF σ JS JT ξ x y' := by
  unfold symplOHF symplOF hOF
  simp only [Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib, map_add (f := _)]

theorem symplOHF_zero_right (y : WOF F E nS nT) : symplOHF σ JS JT ξ y 0 = 0 := by
  have := symplOHF_add_right σ JS JT ξ y 0 0
  rw [add_zero] at this
  exact left_eq_add.1 this

theorem symplOHF_zero_left (y : WOF F E nS nT) : symplOHF σ JS JT ξ 0 y = 0 := by
  have := symplOHF_add_left σ JS JT ξ 0 0 y
  rw [add_zero] at this
  exact left_eq_add.1 this

theorem sum_reorder {A : Type} [CommRing A] {m n : ℕ} (c : A → A) (P : Fin m → Fin m → A)
    (Q : Fin n → Fin n → A) (x y : Matrix (Fin n) (Fin m) A) :
    ∑ a, ∑ b, ∑ c', ∑ d, P a b * c (y c' b) * Q c' d * x d a =
      ∑ i, ∑ j, ∑ k, ∑ l, c (yᵀ i j) * P k i * Q j l * xᵀ k l := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by
    simp only [Matrix.transpose_apply]; ring

theorem snd_symplOHF (x y : WOF F E nS nT) (h : y.map (finPartF F E) = 0) :
    sndA F (symplOHF σ JS JT ξ x y) = 0 := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have h1 : sndA F (symplOF σ JS JT ξ x y) = 0 := by
    unfold symplOF hOF
    rw [sum_reorder (cAF σ) (fun k i => incAF F E (JS⁻¹ k i)) (fun j l => incAF F E (JT j l)) x y]
    refine GlobalTheory.FockCompare.map_trace_sesq_eq_zero (sndA F) σ _ (fun k i => incAF F E (JS⁻¹ k i))
      (fun j l => incAF F E (JT j l)) xᵀ yᵀ (Or.inr ?_)
    ext i j
    exact congrFun (congrFun h j) i
  unfold symplOHF
  rw [map_mul, h1, mul_zero]

theorem continuous_symplOHF {X : Type} [TopologicalSpace X] {x y : X → WOF F E nS nT} (hx : Continuous x)
    (hy : Continuous y) : Continuous fun t => symplOHF σ JS JT ξ (x t) (y t) := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hconj : Continuous (cAF σ : AEF F E → AEF F E) := by
    refine IsModuleTopology.continuous_of_ringHom (R := AF F) (cAF σ) ?_
    have h : (cAF σ).comp (algebraMap (AF F) (AF F ⊗[F] E)) = algebraMap (AF F) (AF F ⊗[F] E) := by
      ext a
      show (Algebra.TensorProduct.map (AlgHom.id F (AF F)) σ) (a ⊗ₜ[F] (1 : E)) = a ⊗ₜ[F] (1 : E)
      rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
    rw [h]
    exact continuous_algebraMap _ _
  have hy' : ∀ i j, Continuous fun t => cAF σ (y t i j) := fun i j =>
    hconj.comp ((continuous_apply j).comp ((continuous_apply i).comp hy))
  have hx' : ∀ i j, Continuous fun t => x t i j := fun i j =>
    (continuous_apply j).comp ((continuous_apply i).comp hx)
  have hh : Continuous fun t => hOF σ JS JT (x t) (y t) :=
    continuous_finsetSum _ fun _ _ => continuous_finsetSum _ fun _ _ => continuous_finsetSum _ fun _ _ =>
      continuous_finsetSum _ fun _ _ => ((continuous_const.mul (hy' _ _)).mul continuous_const).mul (hx' _ _)
  have ht : Continuous (Algebra.trace (AF F) (AEF F E)) := IsModuleTopology.continuous_of_linearMap _
  exact continuous_const.mul (ht.comp (continuous_const.mul hh))

end Form

theorem exists_log {ψ : AddChar (AF F) ℂ} {Tau : Type} [Fintype Tau] {tauE : Tau → (E →+* ℂ)}
    (hψ : IsStdCharF tauE ψ (-1)) :
    ∃ lam : AF F →+ ℂ, Continuous lam ∧ ∀ a, sndA F a = 0 → ψ a = Complex.exp (lam a) := by
  obtain ⟨θ, hθ⟩ := hψ.2.1
  let lam : AF F →+ ℂ :=
    { toFun := fun a => 2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) * ∑ ρ, θ ρ (fstA F a ⊗ₜ[F] (1 : E))
      map_zero' := by simp only [map_zero, TensorProduct.zero_tmul, Finset.sum_const_zero, mul_zero]
      map_add' := fun a b => by
        simp only [map_add (f := _), TensorProduct.add_tmul, Finset.sum_add_distrib, mul_add] }
  refine ⟨lam, ?_, fun a ha => ?_⟩
  · exact continuous_const.mul (continuous_finsetSum _ fun ρ _ => (hθ ρ).2.comp continuous_fst)
  · have hc := hψ.2.2 θ hθ (fstA F a)
    have e : pairA F (fstA F a) 0 = a := Prod.ext rfl ha.symm
    rw [psiInf, e] at hc
    exact hc

theorem contDiff_deriv_heisOF_line : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ f : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ, Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f → ∀ L : ℝ →+ Formalism.IndefR.DatumF.WOF F E nS nT, Continuous L → (∀ t, (L t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
      ∀ (k : ℕ) (L' : (Fin k → ℝ) →+ Formalism.IndefR.DatumF.WOF F E nS nT), Continuous L' → (∀ t, (L' t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
      ∀ w : Formalism.IndefR.DatumF.WOF F E nS nT, ContDiff ℝ ∞ fun x => deriv (fun t : ℝ => Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f (w + L' x)) 0 := by
  intro F E _ _ _ _ _ σ B _ nS nT JS JT _ _ ξ₀ _ _ hψ f hf L hL hL0 k L' hL' hL0' w
  obtain ⟨lam, hl, hlam⟩ := exists_log hψ
  have hi : Continuous (fun v : Fin (k + 1) → ℝ => Fin.init v) := continuous_pi fun i => continuous_apply _
  let M : (Fin (k + 1) → ℝ) →+ WOF F E nS nT :=
    { toFun := fun v => L' (Fin.init v) + L (v (Fin.last k))
      map_zero' := by
        show L' (Fin.init (0 : Fin (k + 1) → ℝ)) + L ((0 : Fin (k + 1) → ℝ) (Fin.last k)) = 0
        rw [show Fin.init (0 : Fin (k + 1) → ℝ) = (0 : Fin k → ℝ) from rfl, Pi.zero_apply, map_zero, map_zero, add_zero]
      map_add' := fun u v => by
        show L' (Fin.init (u + v)) + L (u (Fin.last k) + v (Fin.last k)) = _
        rw [show Fin.init (u + v) = Fin.init u + Fin.init v from rfl, map_add (f := _), map_add (f := _)]
        abel }
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : ContinuousAdd (WOF F E nS nT) := inferInstanceAs (ContinuousAdd (Fin nT → Fin nS → AF F ⊗[F] E))
  have hM : Continuous M := (hL'.comp hi).add (hL.comp (continuous_apply _))
  have hM0 : ∀ v, (M v).map (finPartF F E) = 0 := fun v => by
    show (L' (Fin.init v) + L (v (Fin.last k))).map (finPartF F E) = 0
    rw [Matrix.map_add _ (map_add _), hL0', hL0, add_zero]
  have hg : ContDiff ℝ ∞ fun v => f (w + M v) := hf.smooth (k + 1) M hM hM0 w
  have hsnoc : ContDiff ℝ ∞ (fun p : (Fin k → ℝ) × ℝ => (Fin.snoc (α := fun _ => ℝ) p.1 p.2 : Fin (k + 1) → ℝ)) := by
    refine contDiff_pi.2 fun i => ?_
    induction i using Fin.lastCases with
    | last => simp only [Fin.snoc_last]; exact contDiff_snd
    | cast j => simp only [Fin.snoc_castSucc]; exact (contDiff_apply ℝ (fun _ => ℝ) j).comp contDiff_fst
  let h : (Fin k → ℝ) × ℝ → ℂ := fun p => f (w + M (Fin.snoc (α := fun _ => ℝ) p.1 p.2))
  have hh : ContDiff ℝ ∞ h := hg.comp hsnoc
  have hfe : ∀ x t, f (w + L' x + L t) = h (x, t) := by
    intro x t
    show _ = f (w + (L' (Fin.init (Fin.snoc (α := fun _ => ℝ) x t)) + L (Fin.snoc (α := fun _ => ℝ) x t (Fin.last k))))
    rw [Fin.init_snoc, Fin.snoc_last, add_assoc]
  have hpsi : ∀ y (t : ℝ), B.ψ (symplOHF σ JS JT ξ₀ y (L t)) =
      Complex.exp (t * lam (symplOHF σ JS JT ξ₀ y (L 1))) := by
    intro y t
    rw [hlam _ (snd_symplOHF σ JS JT ξ₀ y _ (hL0 t))]
    congr 1
    let φ : ℝ →+ ℂ :=
      { toFun := fun t => lam (symplOHF σ JS JT ξ₀ y (L t))
        map_zero' := by rw [map_zero L, symplOHF_zero_right, map_zero]
        map_add' := fun a b => by rw [map_add L, symplOHF_add_right, map_add (f := _)] }
    have hφ : Continuous φ := hl.comp (continuous_symplOHF σ JS JT ξ₀ continuous_const hL)
    have := (φ.toRealLinearMap hφ).map_smul t 1
    rw [smul_eq_mul, mul_one, Complex.real_smul] at this
    exact this
  have hd : ∀ x, HasDerivAt (fun t : ℝ => heisOF σ JS JT ξ₀ B.ψ (L t) f (w + L' x))
      (lam (symplOHF σ JS JT ξ₀ (w + L' x) (L 1)) * h (x, 0) + fderiv ℝ h (x, 0) (0, 1)) 0 := by
    intro x
    have e : (fun t : ℝ => heisOF σ JS JT ξ₀ B.ψ (L t) f (w + L' x)) = fun t : ℝ =>
        Complex.exp (t * lam (symplOHF σ JS JT ξ₀ (w + L' x) (L 1))) * h (x, t) := by
      funext t
      show B.ψ (symplOHF σ JS JT ξ₀ (w + L' x) (L t)) * f (w + L' x + L t) = _
      rw [hpsi, hfe]
    rw [e]
    have h0 : HasDerivAt (fun t : ℝ => (t : ℂ) * lam (symplOHF σ JS JT ξ₀ (w + L' x) (L 1)))
        (lam (symplOHF σ JS JT ξ₀ (w + L' x) (L 1))) 0 := by
      simpa using (HasDerivAt.ofReal_comp (hasDerivAt_id (0 : ℝ))).mul_const
        (lam (symplOHF σ JS JT ξ₀ (w + L' x) (L 1)))
    have hp : HasDerivAt (fun t : ℝ => (x, t)) ((0 : Fin k → ℝ), (1 : ℝ)) 0 :=
      (hasDerivAt_const (0 : ℝ) x).prodMk (hasDerivAt_id 0)
    have h2 : HasDerivAt (fun t : ℝ => h (x, t)) (fderiv ℝ h (x, 0) (0, 1)) 0 :=
      ((hh.differentiable (by simp)).differentiableAt.hasFDerivAt).comp_hasDerivAt (0 : ℝ) hp
    have h3 : HasDerivAt (fun t : ℝ => Complex.exp (t * lam (symplOHF σ JS JT ξ₀ (w + L' x) (L 1))) * h (x, t))
        (Complex.exp (((0 : ℝ) : ℂ) * lam (symplOHF σ JS JT ξ₀ (w + L' x) (L 1))) *
          lam (symplOHF σ JS JT ξ₀ (w + L' x) (L 1)) * h (x, 0) +
          Complex.exp (((0 : ℝ) : ℂ) * lam (symplOHF σ JS JT ξ₀ (w + L' x) (L 1))) * fderiv ℝ h (x, 0) (0, 1)) 0 :=
      h0.cexp.mul h2
    refine h3.congr_deriv ?_
    simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul]
  let φ' : (Fin k → ℝ) →+ ℂ :=
    { toFun := fun x => lam (symplOHF σ JS JT ξ₀ (L' x) (L 1))
      map_zero' := by rw [map_zero L', symplOHF_zero_left, map_zero]
      map_add' := fun a b => by rw [map_add L', symplOHF_add_left, map_add (f := _)] }
  have hφ' : ContDiff ℝ ∞ φ' :=
    (φ'.toRealLinearMap (hl.comp (continuous_symplOHF σ JS JT ξ₀ hL' continuous_const))).contDiff
  have e : (fun x => deriv (fun t : ℝ => heisOF σ JS JT ξ₀ B.ψ (L t) f (w + L' x)) 0) = fun x =>
      (lam (symplOHF σ JS JT ξ₀ w (L 1)) + φ' x) * h (x, 0) + fderiv ℝ h (x, 0) (0, 1) := by
    funext x
    rw [(hd x).deriv, symplOHF_add_left, map_add (f := _)]
    rfl
  rw [e]
  have hin : ContDiff ℝ ∞ (fun x : Fin k → ℝ => (x, (0 : ℝ))) := contDiff_id.prodMk contDiff_const
  exact ((contDiff_const.add hφ').mul (hh.comp hin)).add
    (((hh.fderiv_right (m := ∞) (by simp)).comp hin).clm_apply contDiff_const)

end GlobalTheory.ThetaLineSmoothF
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffDerivHeisenbergCMRealLineThetaStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiff_deriv_heisenbergCM_real_line_theta : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ f : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ, Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f → ∀ L : ℝ →+ Formalism.IndefR.DatumF.WOF F E nS nT, Continuous L → (∀ t, (L t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
      ∀ (k : ℕ) (L' : (Fin k → ℝ) →+ Formalism.IndefR.DatumF.WOF F E nS nT), Continuous L' → (∀ t, (L' t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
      ∀ w : Formalism.IndefR.DatumF.WOF F E nS nT, ContDiff ℝ ∞ fun x => deriv (fun t : ℝ => Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f (w + L' x)) 0 := by
  first | exact @GlobalTheory.ThetaLineSmoothF.contDiff_deriv_heisOF_line | exact GlobalTheory.ThetaLineSmoothF.contDiff_deriv_heisOF_line | (intros; apply GlobalTheory.ThetaLineSmoothF.contDiff_deriv_heisOF_line <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormsFiniteDimensional
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal

noncomputable section

namespace GlobalTheory.LevGeo.RankBd

theorem supConst_nonneg (E : Type) [Field E] [NumberField E] (r d M : ℕ) (w : ℝ) : 0 ≤ supConst E r d M w := by
  unfold supConst locConst massLev GlobalTheory.UCls.massBd multBd
  have h1 : 0 ≤ rdE E := Real.rpow_nonneg (abs_nonneg _) _
  have h2 : Even (2 * fdeg E * r ^ 2) := by rw [mul_assoc]; exact even_two_mul _
  refine mul_nonneg (mul_nonneg (div_nonneg (by positivity) (pow_nonneg (mul_nonneg Real.pi_pos.le (sq_nonneg _)) _))
    (h2.pow_nonneg _)) ?_
  have := Real.rpow_nonneg h1 ((fdeg E : ℝ) * ((r : ℝ) ^ 2 - 1) / 2)
  positivity

variable {D : D7} {r : ℕ} {Comp : Type} [Fintype Comp] {X : Comp → Data D.host.E r}

theorem pnorm_fac_pos (Y : Data D.host.E r) (la : Wt Y.Ψ r) {x : Frame Y.Ψ r} (hx : x ∈ Y.dom) :
    0 < ∏ τ, ∏ i : Fin r, ‖dmin Y.Gm x τ i.succ / dmin Y.Gm x τ i.castSucc‖ ^ (-(la τ i : ℝ) / 2) := by
  have hne : ∀ τ i, dmin Y.Gm x τ i ≠ 0 := fun τ i h => by
    have := (hx τ).2 i
    rw [h] at this
    simp at this
  refine Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => Real.rpow_pos_of_pos ?_ _
  exact norm_pos_iff.2 (div_ne_zero (hne τ _) (hne τ _))

theorem eLpNorm_sq_eq {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ] {f : α → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hm : AEStronglyMeasurable f μ) {B : ℝ} (hB : ∀ x, f x ≤ B) :
    eLpNorm f 2 μ ^ 2 = ENNReal.ofReal (∫ x, f x ^ 2 ∂μ) := by
  have hint : Integrable (fun x => f x ^ 2) μ :=
    Integrable.of_bound (hm.pow 2) (B ^ 2) (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (hf0 x) (hB x) 2)
  rw [ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun x => by positivity),
    eLpNorm_eq_eLpNorm' two_ne_zero ENNReal.ofNat_ne_top hm, ENNReal.toReal_ofNat,
    ← ENNReal.rpow_two, ← lintegral_rpow_eNorm_eq_rpow_eLpNorm' (by norm_num : (0 : ℝ) < 2)]
  refine lintegral_congr fun x => ?_
  rw [Real.eNorm_eq_ofReal (hf0 x), ENNReal.rpow_two, ← ENNReal.ofReal_pow (hf0 x)]

open scoped TensorProduct

open scoped TensorProduct

variable {D : D7} {r : ℕ} {Comp : Type} [Fintype Comp] {X : Comp → Data D.host.E r}

theorem finrank_le_of_sup (V : HSp D) (dict : GA D V → Σ k, Frame (X k).Ψ r) (la : ∀ k, Wt (X k).Ψ r)
    {Kf : Subgroup (GA D V)} {th : ∀ k, (X k).Ψ → (GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}
    {hr : V.rank = r} {N : ℕ} (hN : 0 < N) (hth : ∀ k τ, StandardLattice.IsInfEmb τ.1 (th k τ))
    (hd : DictIsUnif V dict Kf th hr) (hK : IsLevelK V N Kf)
    (hu : ∀ g τ i, ‖dmin (X (dict g).1).Gm (dict g).2 τ i‖ = 1)
    (S : Submodule ℂ (FDSec X))
    (hS : ∀ P ∈ S, P ∈ holSub X la ∧ (∀ k, ContinuousOn (P k) (X k).dom) ∧
      (∀ k, ∀ γ ∈ (X k).Γ, ∀ x ∈ (X k).dom, P k (lact γ x) = P k x) ∧ (∀ k x, x ∉ (X k).dom → P k x = 0))
    {C : ℝ} (hC : 0 ≤ C)
    (hsup : ∀ P ∈ S, supE X la P ^ 2 ≤ ENNReal.ofReal C * petE V dict (muQ1 V) la P ^ 2) :
    FiniteDimensional ℂ S ∧ (Module.finrank ℂ S : ℝ) ≤ C := by

  have hpt : ∀ (P : FDSec X) (g : GA D V), ptN la P (dict g) = ‖P (dict g).1 (dict g).2‖ := fun P g =>
    pnorm_eq_of_unit _ _ _ _ (hu g)
  have hdom : ∀ g, (dict g).2 ∈ (X (dict g).1).dom := hd.2.2.2.1
  have hle : ∀ (P : FDSec X) (g : GA D V), ENNReal.ofReal ‖P (dict g).1 (dict g).2‖ ≤ supE X la P := fun P g => by
    rw [← hpt]
    exact le_iSup (fun p : FPt X => ENNReal.ofReal ((X p.1).pnorm (la p.1) (P p.1) p.2)) ⟨(dict g).1, ⟨_, hdom g⟩⟩
  have hmeas : ∀ P ∈ S, AEStronglyMeasurable (fun q : AutQ V => ‖P (dict q.out).1 (dict q.out).2‖) (muQ1 V) := by
    intro P hP
    obtain ⟨-, hc, hΓ, -⟩ := hS P hP
    have hmu : MuUnit V dict (fun _ => 1) := ⟨fun _ _ => (mul_one 1).symm, fun _ => norm_one, fun _ _ => rfl, hu⟩
    have h := GlobalTheory.PeterssonCompare.measurable_onQ_adel V hN hth hd hK hmu continuous_const P hc hΓ
    have e : (fun q : AutQ V => ‖P (dict q.out).1 (dict q.out).2‖) = fun q => ‖onQ V (adel V dict (fun _ => 1) P) q‖ := by
      funext q
      simp [onQ, adel]
    rw [e]
    exact h.norm.aestronglyMeasurable
  have hpet : ∀ P ∈ S, petE V dict (muQ1 V) la P ^ 2 =
      ENNReal.ofReal (∫ q, ‖P (dict q.out).1 (dict q.out).2‖ ^ 2 ∂(muQ1 V)) := by
    intro P hP
    have hfin := supE_ne_top X la (hS P hP).1
    have e : petE V dict (muQ1 V) la P = eLpNorm (fun q : AutQ V => ‖P (dict q.out).1 (dict q.out).2‖) 2 (muQ1 V) := by
      rw [eLpNorm_eq_eLpNorm' two_ne_zero ENNReal.ofNat_ne_top (hmeas P hP), ENNReal.toReal_ofNat]
      simp only [petE, hpt]
    rw [e]
    exact eLpNorm_sq_eq (fun _ => norm_nonneg _) (hmeas P hP) (B := (supE X la P).toReal) fun q =>
      (ENNReal.ofReal_le_iff_le_toReal hfin).1 (hle P _)
  refine GlobalTheory.Bergman.finite_and_finrank_le_of_pointwise (μ := muQ1 V)
    (fun q (P : S) => ‖(P : FDSec X) (dict q.out).1 (dict q.out).2‖)
    (fun q => ⟨(LinearMap.proj (R := ℂ) (φ := fun _ : Frame (X (dict q.out).1).Ψ r => ℂ) (dict q.out).2 ∘ₗ
      LinearMap.proj (R := ℂ) (φ := fun k => Frame (X k).Ψ r → ℂ) (dict q.out).1) ∘ₗ S.subtype, fun P => rfl⟩)
    (fun P => hmeas P P.2) ?_ hC ?_
  · intro P hP0
    have h0 : petE V dict (muQ1 V) la (P : FDSec X) = 0 := by
      have e : (fun q : AutQ V => ptN la (P : FDSec X) (dict q.out)) = fun _ => 0 := by
        funext q
        rw [hpt]
        exact hP0 q
      unfold petE
      rw [e]
      exact eLpNorm'_zero (by norm_num)
    have hs := hsup P P.2
    rw [h0] at hs
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, nonpos_iff_eq_zero,
      pow_eq_zero_iff] at hs
    obtain ⟨-, -, -, hoff⟩ := hS P P.2
    refine Subtype.ext (funext fun k => funext fun x => ?_)
    by_cases hx : x ∈ (X k).dom
    · have h1 : ENNReal.ofReal ((X k).pnorm (la k) ((P : FDSec X) k) x) ≤ supE X la P :=
        le_iSup (fun p : FPt X => ENNReal.ofReal ((X p.1).pnorm (la p.1) ((P : FDSec X) p.1) p.2)) ⟨k, ⟨x, hx⟩⟩
      rw [hs, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at h1
      have h2 : ‖(P : FDSec X) k x‖ * _ ≤ 0 := h1
      have h3 := pnorm_fac_pos (X k) (la k) hx
      have h4 : ‖(P : FDSec X) k x‖ ≤ 0 := nonpos_of_mul_nonpos_left h2 h3
      simpa using h4
    · simpa using hoff k x hx
  · intro P q
    have h1 := hle (P : FDSec X) q.out
    have h2 := hsup P P.2
    rw [hpet P P.2] at h2
    have h3 : ENNReal.ofReal (‖(P : FDSec X) (dict q.out).1 (dict q.out).2‖ ^ 2) ≤
        ENNReal.ofReal (C * ∫ q, ‖(P : FDSec X) (dict q.out).1 (dict q.out).2‖ ^ 2 ∂(muQ1 V)) := by
      rw [ENNReal.ofReal_pow (norm_nonneg _), ENNReal.ofReal_mul hC]
      exact (pow_le_pow_left' h1 2).trans h2
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC (integral_nonneg fun _ => by positivity))).1 h3

open Module


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem finrank_cuspW_le : GlobalTheory.UCls.MassBound → GlobalTheory.UCls.TorusBound → ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → FiniteDimensional c.F (cuspW Xo c U (wtZ a n)) ∧ (Module.finrank c.F (cuspW Xo c U (wtZ a n)) : ℝ) ≤ supConst D.host.E D.R.r D.host.d l.M (((absA Dw a : ℕ) : ℝ) + ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) + 1) := by
  intro hM hT D j H Dw l Xo c U dict hL a n hDom
  obtain ⟨σ, hσ⟩ : ∃ σ : c.F →+* ℂ, GoodEmb c σ := ⟨_, goodEmb_goodOf c c.F.val.toRingHom⟩
  obtain ⟨Kf, th, hr, hK, hth, hd, hu⟩ := hL.dictU σ hσ
  have hU : IsUnf (U σ) := hL.unf σ hσ
  obtain ⟨w, hw_def⟩ : ∃ w : ℝ, w = ((absA Dw a : ℕ) : ℝ) + ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) + 1 := ⟨_, rfl⟩
  rw [← hw_def]
  have hw : 0 < w := by rw [hw_def]; positivity
  have hspread : ∀ k, (∑ τ, ((U σ).X k).spread (laU (U σ) a n k) τ) ≤ w := fun k =>
    (GlobalTheory.T.sum_weightSpread_le_exponentNorm_add D j H Dw l Xo c U dict hL σ hσ a n k).trans (by rw [hw_def]; linarith)
  have hχ := hL.chiTriv σ hσ a n hDom
  have hsup := GlobalTheory.T.weighted_frame_sum_positive hM hT D j H Dw l Xo c U dict hL σ hσ (laU (U σ) a n) w hw hspread hχ
  obtain ⟨Cw, hCw⟩ : ∃ Cw, Cw = cuspW Xo c U (wtZ a n) := ⟨_, rfl⟩
  rw [← hCw]
  have hsecOf : ∀ f ∈ Cw, f ∈ sec Xo c a n := fun f hf => by
    rw [hCw, cuspW_wtZ] at hf
    exact cusp_le_sec Xo c U a n hf

  have hgen : ∀ f ∈ Cw, rdU (U σ) f ∈ holSub (U σ).X (laU (U σ) a n) ∧
      (∀ k, ContinuousOn (rdU (U σ) f k) ((U σ).X k).dom) ∧
      (∀ k, ∀ γ ∈ ((U σ).X k).Γ, ∀ x ∈ ((U σ).X k).dom, rdU (U σ) f k (lact γ x) = rdU (U σ) f k x) ∧
      (∀ k x, x ∉ ((U σ).X k).dom → rdU (U σ) f k x = 0) := by
    intro f hf
    have hs := hU.2.2.2.2.1 a n hDom f (hsecOf f hf)
    refine ⟨?_, fun k => (hs k).1.continuousOn, fun k γ hγ x hx => ?_, fun k x hx => ?_⟩
    · rw [hCw] at hf
      have := (mem_cuspW.1 hf).2 σ hσ
      rwa [modelWt_wtZ] at this
    · rw [(hs k).2.2 γ hγ x hx, hχ k γ hγ, one_mul]
    · classical
      show (if h : x ∈ ((U σ).X k).dom then _ else 0) = 0
      rw [dite_eq_right hx]
  obtain ⟨S, hS_def⟩ : ∃ S : Submodule ℂ (FDSec (U σ).X), S = Submodule.span ℂ (rdU (U σ) '' (Cw : Set (Rul Xo c))) :=
    ⟨_, rfl⟩
  have hS : ∀ P ∈ S, P ∈ holSub (U σ).X (laU (U σ) a n) ∧ (∀ k, ContinuousOn (P k) ((U σ).X k).dom) ∧
      (∀ k, ∀ γ ∈ ((U σ).X k).Γ, ∀ x ∈ ((U σ).X k).dom, P k (lact γ x) = P k x) ∧
      (∀ k x, x ∉ ((U σ).X k).dom → P k x = 0) := by
    intro P hP
    rw [hS_def] at hP
    induction hP using Submodule.span_induction with
    | mem P hP =>
      obtain ⟨f, hf, rfl⟩ := hP
      exact hgen f hf
    | zero => exact ⟨Submodule.zero_mem _, fun k => continuousOn_const, fun _ _ _ _ _ => rfl, fun _ _ _ => rfl⟩
    | add P Q _ _ hP hQ =>
      refine ⟨Submodule.add_mem _ hP.1 hQ.1, fun k => (hP.2.1 k).add (hQ.2.1 k), fun k γ hγ x hx => ?_,
        fun k x hx => ?_⟩
      · simp only [Pi.add_apply]
        rw [hP.2.2.1 k γ hγ x hx, hQ.2.2.1 k γ hγ x hx]
      · simp only [Pi.add_apply]
        rw [hP.2.2.2 k x hx, hQ.2.2.2 k x hx, add_zero]
    | smul z P _ hP =>
      refine ⟨Submodule.smul_mem _ z hP.1, fun k => (hP.2.1 k).const_smul z, fun k γ hγ x hx => ?_,
        fun k x hx => ?_⟩
      · simp only [Pi.smul_apply]
        rw [hP.2.2.1 k γ hγ x hx]
      · simp only [Pi.smul_apply]
        rw [hP.2.2.2 k x hx, smul_zero]
  obtain ⟨hSfin, hSle⟩ := finrank_le_of_sup (D.sp.W j) (dict σ) (laU (U σ) a n) (Nat.pos_of_ne_zero (by
      have := l.three_le; omega)) hth hd hK hu S hS (supConst_nonneg _ _ _ _ _) fun P hP => hsup P (hS P hP).1

  have hind : ∀ (m : ℕ) (b : Fin m → Rul Xo c), (∀ i, b i ∈ Cw) → LinearIndependent c.F b →
      LinearIndependent ℂ (fun i => rdU (U σ) (b i)) := fun m b hb hli =>
    (GlobalTheory.reading_linearIndependent_and_injective GlobalTheory.lawsFieldsSeparately.2.1 _ H Dw l Xo c σ _
      (Formalism.L2.PjFree.Unf.ofPj (U σ)) ((Formalism.L2.PjFree.isUnf_ofPj _).2 hU) a n).1 m b (fun i => hsecOf _ (hb i)) hli
  have hcard : ∀ s : Finset Cw, LinearIndependent c.F (fun i : s => (i : Cw)) → s.card ≤ finrank ℂ S := by
    intro s hs
    let e : Fin s.card ≃ s := s.equivFin.symm
    let b : Fin s.card → Rul Xo c := fun i => ((e i : Cw) : Rul Xo c)
    have hb : LinearIndependent c.F b :=
      ((hs.comp e e.injective).map' Cw.subtype (Submodule.ker_subtype _))
    have hrd := hind s.card b (fun i => (e i : Cw).2) hb
    let v : Fin s.card → S := fun i => ⟨rdU (U σ) (b i), hS_def ▸ Submodule.subset_span ⟨b i, (e i : Cw).2, rfl⟩⟩
    have hv : LinearIndependent ℂ v := LinearIndependent.of_comp S.subtype hrd
    simpa using hv.fintype_card_le_finrank
  have : Module.Free c.F Cw := Module.Free.of_divisionRing c.F Cw
  have hrank : Module.rank c.F Cw ≤ ((finrank ℂ S : ℕ) : Cardinal) := rank_le hcard
  have hfin : FiniteDimensional c.F Cw :=
    Module.rank_lt_aleph0_iff.1 (hrank.trans_lt Cardinal.natCast_lt_aleph0)
  have h2 : finrank c.F Cw ≤ finrank ℂ S := finrank_le_of_rank_le hrank
  refine ⟨hfin, le_trans ?_ hSle⟩
  exact Nat.cast_le.2 h2

end GlobalTheory.LevGeo.RankBd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUnitaryGLBlockEmbeddingPolynomialEntri
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUnitaryGLBlockEmbeddingPolynomialEntri
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open scoped TensorProduct

namespace GlobalTheory.BlockForms


open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes in
theorem isBlockEmb_continuous : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf →
    ∀ (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      Continuous ι := by
  intro F E _ _ _ _ _ _ σ hσ n J _ r Xf Yf _ l d h ι hι
  obtain ⟨Φ, j, _, hΦs, -, -, hform⟩ := hι
  haveI : Module.Finite F E := Module.finite_of_finrank_eq_succ hσ.2.2.1
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hsig : Continuous (sigR (AF F) σ) := by
    have hc := IsModuleTopology.continuous_of_linearMap (R := AF F) (LinearMap.baseChange (AF F) σ.toLinearMap)
    refine hc.congr fun x => ?_
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a y => simp [LinearMap.baseChange_tmul, sigR]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have h1 : Continuous fun g : GlobalTheory.CuspRep.GA E d => g.1.map Φ.symm :=
    Units.continuous_val.matrix_map hΦs
  have h2 : Continuous fun g : GlobalTheory.CuspRep.GA E d => (g⁻¹).1.map Φ.symm :=
    Units.continuous_coe_inv.matrix_map hΦs
  have h3 : Continuous fun g : GlobalTheory.CuspRep.GA E d => Matrix.transpose (((g⁻¹).1.map Φ.symm).map (sigR (AF F) σ)) :=
    (h2.matrix_map hsig).matrix_transpose
  have hM : Continuous fun g : GlobalTheory.CuspRep.GA E d => (matHom _ σ J (ι g)).1 := by
    refine Continuous.congr ?_ fun g => (hform g).symm
    exact (continuous_const.add ((continuous_const.matrix_mul (h1.sub continuous_const)).matrix_mul continuous_const)).add
      ((continuous_const.matrix_mul (h3.sub continuous_const)).matrix_mul continuous_const)
  have hMi : Continuous fun g : GlobalTheory.CuspRep.GA E d => ((matHom _ σ J (ι g))⁻¹ : GL (Fin n) (AF F ⊗[F] E)).1 := by
    refine (hM.comp continuous_inv).congr fun g => ?_
    simp only [Function.comp_apply, map_inv]
  exact (isEmbedding_matHom (AF F) σ J).continuous_iff.2 (Units.continuous_iff.2 ⟨hM, hMi⟩)

end GlobalTheory.BlockForms
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUnitaryGLBlockEmbeddingPolynomialEntriStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_unitaryGLBlockEmbedding_polynomial_entries : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf →
    ∀ (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      Continuous ι := by
  first | exact @GlobalTheory.BlockForms.isBlockEmb_continuous | exact GlobalTheory.BlockForms.isBlockEmb_continuous | (intros; apply GlobalTheory.BlockForms.isBlockEmb_continuous <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHolomorphicChartsGenericPointProjective
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

namespace GlobalTheory.GenericCharts

theorem exists_etale_coords (F : Type) [Field F] [CharZero F] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp F) (D : ℕ) (hp : IsProjOver p) (hd : topologicalKrullDim X = (D : ℕ)) :
    ∃ (U : X.Opens) (x : Fin D → Γ(X, U)), IsAffineOpen U ∧ genericPoint X ∈ U ∧
      (MvPolynomial.eval₂Hom (algX p U) x).Etale := by
  obtain ⟨N, i, hi, hcomp⟩ := hp
  haveI : IsProper (PSpace.str F N) := isProper_str F N
  haveI : LocallyOfFiniteType p := by rw [← hcomp]; infer_instance
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (genericPoint X)) isOpen_univ
  have hU : IsAffineOpen U := hU
  haveI : Nonempty U := ⟨⟨_, hxU⟩⟩
  let ψ := Spec.preimage (hU.fromSpec ≫ p)
  have hψ : Spec.map ψ = hU.fromSpec ≫ p := Spec.map_preimage _
  letI : Algebra F Γ(X, U) := ψ.hom.toAlgebra
  haveI hft : Algebra.FiniteType F Γ(X, U) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := ψ)).mp (hψ ▸ inferInstance)
  have hA : Algebra.trdeg F Γ(X, U) = D :=
    GlobalTheory.GenFinite.trdeg_affineOpen_eq F p hU ⟨_, hxU⟩ D hd
  haveI : FaithfulSMul F Γ(X, U) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap F Γ(X, U)).injective
  obtain ⟨f, hf, hs⟩ := GlobalTheory.GenericEtale.exists_away F Γ(X, U) hA
  let B := Localization.Away f
  have : IsDomain B := IsLocalization.isDomain_of_le_nonZeroDivisors (M := Submonoid.powers f) _
    (powers_le_nonZeroDivisors_of_noZeroDivisors hf)
  have : IsOpenImmersion (spMap (algebraMap Γ(X, U) B)) := IsOpenImmersion.of_isLocalization f
  let i' : Sp Γ(X, U) ⟶ X := hU.fromSpec
  haveI : IsOpenImmersion i' := inferInstanceAs (IsOpenImmersion hU.fromSpec)
  have hi' : i' ≫ p = spMap (algebraMap F Γ(X, U)) := hψ.symm
  let j : Sp B ⟶ X := spMap (algebraMap Γ(X, U) B) ≫ i'
  have hj : j ≫ p = spMap (algebraMap F B) := by
    rw [Category.assoc, hi', IsScalarTower.algebraMap_eq F Γ(X, U) B, ← Spec.map_comp]
    rfl
  have h₁ : SmoothOfRelativeDimension D (j ≫ p) := by
    rw [hj]
    refine (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension D)).mpr ?_
    exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
      ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap D).mpr hs)
  have h₂ : SmoothOfRelativeDimension D (j.opensRange.ι ≫ p) := by
    rw [← j.isoOpensRange_inv_comp, Category.assoc]
    have : SmoothOfRelativeDimension (0 + D) (j.isoOpensRange.inv ≫ j ≫ p) := inferInstance
    rwa [zero_add] at this
  refine ModelCharts.exists_etale_coords_of_opens p D j.opensRange ?_
  exact ⟨genericPoint _, genericPoint_eq_of_isOpenImmersion j⟩

theorem exists_generic_charts : ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (D : ℕ), IsProjOver p → topologicalKrullDim X = (D : ℕ) → ∃ U : X.Opens, genericPoint X ∈ U ∧ ∀ y ∈ ptsIn p σ U, ∃ c : AlgChart p σ D, y ∈ c.e.source := by
  intro F _ X _ _ p σ D hp hd
  haveI : CharZero F := σ.charZero
  obtain ⟨U, x, hU, hη, hx⟩ := exists_etale_coords F X p D hp hd
  exact ⟨U, hη, fun y hy => (AlgChart.exists_of_etale hU x hx hy).imp fun c h => h.1⟩

end GlobalTheory.GenericCharts
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TamePartLeft
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TamePartLeft
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DoublingEv

noncomputable section

namespace GlobalTheory.DoublingEv.PartLTame

open scoped Classical

variable {F : Type} [Field F] [NumberField F]

def reindexFun {R : Type} {ι ι' : Type} (e : ι ≃ ι') : ((ι → R) → ℂ) →ₗ[ℂ] ((ι' → R) → ℂ) :=
  LinearMap.funLeft ℂ ℂ (fun y : ι' → R => y ∘ e)

theorem reindexFun_apply {R : Type} {ι ι' : Type} (e : ι ≃ ι') (Φ : (ι → R) → ℂ) (y : ι' → R) :
    reindexFun e Φ y = Φ (y ∘ e) := rfl

theorem isTame_reindexFun {ι ι' : Type} [Fintype ι] [Fintype ι'] (e : ι ≃ ι') :
    IsTame F (reindexFun (R := AF F) e) := by
  intro g hg
  let L : (ι' → mixedEmbedding.mixedSpace F) ≃L[ℝ] (ι → mixedEmbedding.mixedSpace F) :=
    (LinearEquiv.funCongrLeft ℝ (mixedEmbedding.mixedSpace F) e).toContinuousLinearEquiv
  let H : (ι' → FiniteAdeleRing (𝓞 F) F) ≃ₜ (ι → FiniteAdeleRing (𝓞 F) F) :=
    { toFun := fun y => y ∘ e
      invFun := fun z => z ∘ e.symm
      left_inv := fun y => by funext i; simp
      right_inv := fun z => by funext i; simp
      continuous_toFun := continuous_pi fun i => continuous_apply (e i)
      continuous_invFun := continuous_pi fun i => continuous_apply (e.symm i) }
  refine ⟨Unit, inferInstance, fun _ => SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L, fun _ => g ∘ H,
    fun _ => ⟨hg.1.comp_continuous H.continuous, hg.2.comp_homeomorph H⟩, fun f => ?_⟩
  funext y
  simp only [Finset.univ_unique, Finset.sum_singleton]
  rfl

theorem isTame_partL : ∀ (F : Type) [Field F] [NumberField F] (κ κ₁ κ' : Type) [Fintype κ] [Fintype κ₁] [Fintype κ']
    (T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ₁ → AF F) → ℂ)), IsTame F T → IsTame F (partL (κ' := κ') T) := by
  intro F _ _ κ κ₁ κ' _ _ _ T hT
  have h : partL (κ' := κ') T = reindexFun (Equiv.sumComm κ' κ₁) ∘ₗ partR (κ := κ') T ∘ₗ
      reindexFun (Equiv.sumComm κ κ') := by
    refine LinearMap.ext fun Φ => funext fun s => ?_
    simp only [LinearMap.comp_apply, reindexFun_apply, partR_apply, partL_apply]
    exact congrArg₂ (fun φ t => T φ t) (funext fun x => congrArg Φ (funext fun i => by cases i <;> rfl)) rfl
  rw [h]
  exact ((isTame_reindexFun _).comp (GlobalTheory.T.tame_part_right F κ' κ κ₁ T hT)).comp (isTame_reindexFun _)

end GlobalTheory.DoublingEv.PartLTame
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TamePartLeftStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DoublingEv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tame_part_left : ∀ (F : Type) [Field F] [NumberField F] (κ κ₁ κ' : Type) [Fintype κ] [Fintype κ₁] [Fintype κ']
    (T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ₁ → AF F) → ℂ)), IsTame F T → IsTame F (partL (κ' := κ') T) := by
  first | exact @GlobalTheory.DoublingEv.PartLTame.isTame_partL | exact GlobalTheory.DoublingEv.PartLTame.isTame_partL | (intros; apply GlobalTheory.DoublingEv.PartLTame.isTame_partL <;> assumption)
end
end
