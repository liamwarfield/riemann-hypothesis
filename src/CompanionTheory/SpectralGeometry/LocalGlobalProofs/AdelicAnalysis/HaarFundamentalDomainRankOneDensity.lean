module

public import CompanionTheory.AutomorphicTheory.ThetaDilations.BoundedA
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GlobalProductGramFiberRankOne
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilArchimedeanDensity
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ArchimedeanLocalDensityFormula

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.PositiveMajorantGaussian
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.PositiveMajorantGaussian
open NumberField IsDedekindDomain MeasureTheory Matrix
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SW.Core

theorem core_estimate : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ), Fintype.card ι = 2 * M → 3 ≤ M → ∀ (B : Matrix ι ι F), B.IsSymm → B.det ≠ 0 → ∀ (ρ : InfinitePlace F → (F →+* ℝ)), (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) → ∀ (Pm : InfinitePlace F → Matrix ι ι ℝ), (∀ w, (Pm w).PosDef) → (∀ w, Pm w * (B.map (ρ w))⁻¹ * Pm w = B.map (ρ w)) → ∀ [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)] (lf : Measure (FiniteAdeleRing (𝓞 F) F)), lf.IsAddHaarMeasure → lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1 → ∀ (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr] (ginf : Ω → InfinitePlace F → Matrix ι ι ℝ) (gf : Ω → Matrix ι ι (FiniteAdeleRing (𝓞 F) F)), (∀ w i j, Measurable fun ω => ginf ω w i j) → (∀ i j, Measurable fun ω => gf ω i j) → (∀ ω w, (ginf ω w)ᵀ * B.map (ρ w) * ginf ω w = B.map (ρ w)) → (∀ ω, (gf ω)ᵀ * B.map (algebraMap F (FiniteAdeleRing (𝓞 F) F)) * gf ω = B.map (algebraMap F (FiniteAdeleRing (𝓞 F) F))) → (∀ N : ℕ, 0 < N → ∃ C : ℝ, ∀ R : ℝ, 0 < R → ∫⁻ ω, ∑' x : {x : ι → F // x ≠ 0}, Set.indicator {x : ι → F | (∀ i v, ((N : FiniteAdeleRing (𝓞 F) F) * (gf ω *ᵥ fun j => algebraMap F (FiniteAdeleRing (𝓞 F) F) (x j)) i) v ∈ v.adicCompletionIntegers F) ∧ ∀ w, ‖ginf ω w *ᵥ fun j => ρ w (x j)‖ ≤ R} (fun _ => (1 : ℝ≥0∞)) x.1 ∂Pr ≤ ENNReal.ofReal (C * (R ^ (Module.finrank ℚ F * M) + R ^ (2 * Module.finrank ℚ F * M)))) → ∃ (C : ℝ) (Df : ℕ → FiniteAdeleRing (𝓞 F) F → ℝ) (Dinf : (InfinitePlace F → ℝ) → ℝ), (∀ a : ℕ, 0 < a → Continuous (Df a) ∧ (∀ y, 0 ≤ Df a y) ∧ ∀ U : Set (FiniteAdeleRing (𝓞 F) F), MeasurableSet U → (Measure.pi fun _ : ι => lf) {x | (∀ i v, ((a : FiniteAdeleRing (𝓞 F) F) * x i) v ∈ v.adicCompletionIntegers F) ∧ algebraMap F (FiniteAdeleRing (𝓞 F) F) (1 / 2) * (x ⬝ᵥ (B.map (algebraMap F (FiniteAdeleRing (𝓞 F) F)) *ᵥ x)) ∈ U} = ∫⁻ y in U, ENNReal.ofReal (Df a y) ∂lf) ∧ (Continuous Dinf ∧ (∀ y, 0 ≤ Dinf y) ∧ ∀ U : Set (InfinitePlace F → ℝ), MeasurableSet U → ∫⁻ x in {x : InfinitePlace F → ι → ℝ | (fun w => (1 / 2 : ℝ) * (x w ⬝ᵥ (B.map (ρ w) *ᵥ x w))) ∈ U}, ENNReal.ofReal (Real.exp (-Real.pi * ∑ w, x w ⬝ᵥ (Pm w *ᵥ x w))) = ∫⁻ y in U, ENNReal.ofReal (Dinf y)) ∧ ∀ a : ℕ, 0 < a → ∀ β : F, β ≠ 0 → ∃ I : ℝ≥0, ∫⁻ ω, ∑' x : {x : ι → F // (1 / 2 : F) * (x ⬝ᵥ (B *ᵥ x)) = β}, Set.indicator {x : ι → F | ∀ i v, ((a : FiniteAdeleRing (𝓞 F) F) * (gf ω *ᵥ fun j => algebraMap F (FiniteAdeleRing (𝓞 F) F) (x j)) i) v ∈ v.adicCompletionIntegers F} (fun x => ENNReal.ofReal (Real.exp (-Real.pi * ∑ w, (ginf ω w *ᵥ fun j => ρ w (x j)) ⬝ᵥ (Pm w *ᵥ (ginf ω w *ᵥ fun j => ρ w (x j)))))) x.1 ∂Pr = (I : ℝ≥0∞) ∧ |(I : ℝ) - (Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (2 * M - 1) * Df a (algebraMap F (FiniteAdeleRing (𝓞 F) F) β) * Dinf (fun w => ρ w β)| ≤ C * (a : ℝ) ^ (Module.finrank ℚ F * M) :=
  CompanionTheory.PlacePermOperatorBicommutantSpan.core

end GlobalTheory.CompanionTheory.SW.Core
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.PositiveMajorantGaussianStatement
open NumberField IsDedekindDomain MeasureTheory Matrix
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.positive_majorant_gaussian : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ), Fintype.card ι = 2 * M → 3 ≤ M → ∀ (B : Matrix ι ι F), B.IsSymm → B.det ≠ 0 → ∀ (ρ : InfinitePlace F → (F →+* ℝ)), (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) → ∀ (Pm : InfinitePlace F → Matrix ι ι ℝ), (∀ w, (Pm w).PosDef) → (∀ w, Pm w * (B.map (ρ w))⁻¹ * Pm w = B.map (ρ w)) → ∀ [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)] (lf : Measure (FiniteAdeleRing (𝓞 F) F)), lf.IsAddHaarMeasure → lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1 → ∀ (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr] (ginf : Ω → InfinitePlace F → Matrix ι ι ℝ) (gf : Ω → Matrix ι ι (FiniteAdeleRing (𝓞 F) F)), (∀ w i j, Measurable fun ω => ginf ω w i j) → (∀ i j, Measurable fun ω => gf ω i j) → (∀ ω w, (ginf ω w)ᵀ * B.map (ρ w) * ginf ω w = B.map (ρ w)) → (∀ ω, (gf ω)ᵀ * B.map (algebraMap F (FiniteAdeleRing (𝓞 F) F)) * gf ω = B.map (algebraMap F (FiniteAdeleRing (𝓞 F) F))) → (∀ N : ℕ, 0 < N → ∃ C : ℝ, ∀ R : ℝ, 0 < R → ∫⁻ ω, ∑' x : {x : ι → F // x ≠ 0}, Set.indicator {x : ι → F | (∀ i v, ((N : FiniteAdeleRing (𝓞 F) F) * (gf ω *ᵥ fun j => algebraMap F (FiniteAdeleRing (𝓞 F) F) (x j)) i) v ∈ v.adicCompletionIntegers F) ∧ ∀ w, ‖ginf ω w *ᵥ fun j => ρ w (x j)‖ ≤ R} (fun _ => (1 : ℝ≥0∞)) x.1 ∂Pr ≤ ENNReal.ofReal (C * (R ^ (Module.finrank ℚ F * M) + R ^ (2 * Module.finrank ℚ F * M)))) → ∃ (C : ℝ) (Df : ℕ → FiniteAdeleRing (𝓞 F) F → ℝ) (Dinf : (InfinitePlace F → ℝ) → ℝ), (∀ a : ℕ, 0 < a → Continuous (Df a) ∧ (∀ y, 0 ≤ Df a y) ∧ ∀ U : Set (FiniteAdeleRing (𝓞 F) F), MeasurableSet U → (Measure.pi fun _ : ι => lf) {x | (∀ i v, ((a : FiniteAdeleRing (𝓞 F) F) * x i) v ∈ v.adicCompletionIntegers F) ∧ algebraMap F (FiniteAdeleRing (𝓞 F) F) (1 / 2) * (x ⬝ᵥ (B.map (algebraMap F (FiniteAdeleRing (𝓞 F) F)) *ᵥ x)) ∈ U} = ∫⁻ y in U, ENNReal.ofReal (Df a y) ∂lf) ∧ (Continuous Dinf ∧ (∀ y, 0 ≤ Dinf y) ∧ ∀ U : Set (InfinitePlace F → ℝ), MeasurableSet U → ∫⁻ x in {x : InfinitePlace F → ι → ℝ | (fun w => (1 / 2 : ℝ) * (x w ⬝ᵥ (B.map (ρ w) *ᵥ x w))) ∈ U}, ENNReal.ofReal (Real.exp (-Real.pi * ∑ w, x w ⬝ᵥ (Pm w *ᵥ x w))) = ∫⁻ y in U, ENNReal.ofReal (Dinf y)) ∧ ∀ a : ℕ, 0 < a → ∀ β : F, β ≠ 0 → ∃ I : ℝ≥0, ∫⁻ ω, ∑' x : {x : ι → F // (1 / 2 : F) * (x ⬝ᵥ (B *ᵥ x)) = β}, Set.indicator {x : ι → F | ∀ i v, ((a : FiniteAdeleRing (𝓞 F) F) * (gf ω *ᵥ fun j => algebraMap F (FiniteAdeleRing (𝓞 F) F) (x j)) i) v ∈ v.adicCompletionIntegers F} (fun x => ENNReal.ofReal (Real.exp (-Real.pi * ∑ w, (ginf ω w *ᵥ fun j => ρ w (x j)) ⬝ᵥ (Pm w *ᵥ (ginf ω w *ᵥ fun j => ρ w (x j)))))) x.1 ∂Pr = (I : ℝ≥0∞) ∧ |(I : ℝ) - (Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (2 * M - 1) * Df a (algebraMap F (FiniteAdeleRing (𝓞 F) F) β) * Dinf (fun w => ρ w β)| ≤ C * (a : ℝ) ^ (Module.finrank ℚ F * M) := by
  first | exact @GlobalTheory.CompanionTheory.SW.Core.core_estimate | exact GlobalTheory.CompanionTheory.SW.Core.core_estimate | (intros; apply GlobalTheory.CompanionTheory.SW.Core.core_estimate <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ArchimedeanGramFiberContinuousDensity
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SizeFunctionRapidDecayIntegrable
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SizeFunctionRapidDecayIntegrable
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.SizeInt

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def compReal (hF : IsTotallyReal F) (v : InfinitePlace F) : v.Completion ≃+* ℝ :=
  InfinitePlace.Completion.ringEquivRealOfIsReal (hF.isReal v)

theorem continuous_compReal (hF : IsTotallyReal F) (v : InfinitePlace F) :
    Continuous (compReal hF v) :=
  (InfinitePlace.Completion.isometryEquivRealOfIsReal (hF.isReal v)).continuous

theorem continuous_compReal_symm (hF : IsTotallyReal F) (v : InfinitePlace F) :
    Continuous (compReal hF v).symm :=
  (InfinitePlace.Completion.isometryEquivRealOfIsReal (hF.isReal v)).symm.continuous

theorem norm_compReal (hF : IsTotallyReal F) (v : InfinitePlace F) (x : v.Completion) :
    ‖compReal hF v x‖ = ‖x‖ :=
  (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal (hF.isReal v)).norm_map_of_map_zero
    (map_zero _) x

theorem secondCountable_Ainf (hF : IsTotallyReal F) : SecondCountableTopology (Ainf F) := by
  haveI : ∀ v : InfinitePlace F, SecondCountableTopology v.Completion := fun v =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (hF.isReal v)).toHomeomorph.secondCountableTopology
  exact inferInstanceAs (SecondCountableTopology (∀ v : InfinitePlace F, v.Completion))

section Coord

variable {d : ℕ} (hF : IsTotallyReal F) (b : Module.Basis (Fin d) F E)

def ainfEquiv : Ainf F ≃+ (InfinitePlace F → ℝ) where
  toFun x v := compReal hF v (x v)
  invFun w := (fun v => (compReal hF v).symm (w v) : ∀ v : InfinitePlace F, v.Completion)
  left_inv x := by funext v; exact (compReal hF v).symm_apply_apply _
  right_inv w := by funext v; exact (compReal hF v).apply_symm_apply _
  map_add' x y := by funext v; exact map_add (compReal hF v) (x v) (y v)

theorem continuous_ainfEquiv : Continuous (ainfEquiv hF) :=
  continuous_pi fun v => (continuous_compReal hF v).comp (continuous_apply (A := fun v : InfinitePlace F => v.Completion) v)

theorem continuous_ainfEquiv_symm : Continuous (ainfEquiv hF).symm := by
  have h : Continuous fun (w : InfinitePlace F → ℝ) (v : InfinitePlace F) =>
      ((compReal hF v).symm (w v) : v.Completion) :=
    continuous_pi fun v => (continuous_compReal_symm hF v).comp (continuous_apply v)
  exact h

def coordEquiv : Ainf F ⊗[F] E ≃+ (Fin d → InfinitePlace F → ℝ) :=
  (Algebra.TensorProduct.basis (Ainf F) b).equivFun.toAddEquiv.trans
    (AddEquiv.piCongrRight fun _ => ainfEquiv hF)

theorem abs_coordEquiv (y : Ainf F ⊗[F] E) (k : Fin d) (v : InfinitePlace F) :
    ‖coordEquiv hF b y k v‖ = ‖(Algebra.TensorProduct.basis (Ainf F) b).repr y k v‖ :=
  norm_compReal hF v _

def tupEquiv (n M : ℕ) :
    (Fin n → Fin M → Ainf F ⊗[F] E) ≃+ (Fin n → Fin M → Fin d → InfinitePlace F → ℝ) :=
  AddEquiv.piCongrRight fun _ => AddEquiv.piCongrRight fun _ => coordEquiv hF b

theorem tupEquiv_apply (n M : ℕ) (X : Fin n → Fin M → Ainf F ⊗[F] E) (a : Fin n) (i : Fin M) :
    tupEquiv hF b n M X a i = coordEquiv hF b (X a i) := rfl

theorem norm_tupEquiv_le (n M : ℕ) (X : Fin n → Fin M → Ainf F ⊗[F] E) :
    ‖tupEquiv hF b n M X‖ ≤ sizeTup b X := by
  have h0 : ∀ (y : Ainf F ⊗[F] E) (k : Fin d) (v : InfinitePlace F),
      0 ≤ ‖(Algebra.TensorProduct.basis (Ainf F) b).repr y k v‖ := fun _ _ _ => norm_nonneg _
  have hI : ∀ y : Ainf F ⊗[F] E, 0 ≤ sizeInf b y := fun y =>
    Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun v _ => h0 y k v
  have hT : 0 ≤ sizeTup b X := Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun i _ => hI _
  refine (pi_norm_le_iff_of_nonneg hT).2 fun a => (pi_norm_le_iff_of_nonneg hT).2 fun i =>
    (pi_norm_le_iff_of_nonneg hT).2 fun k => (pi_norm_le_iff_of_nonneg hT).2 fun v => ?_
  rw [tupEquiv_apply, abs_coordEquiv]
  calc ‖(Algebra.TensorProduct.basis (Ainf F) b).repr (X a i) k v‖
      ≤ ∑ v', ‖(Algebra.TensorProduct.basis (Ainf F) b).repr (X a i) k v'‖ :=
        Finset.single_le_sum (f := fun v' => ‖(Algebra.TensorProduct.basis (Ainf F) b).repr (X a i) k v'‖)
          (fun v' _ => norm_nonneg _) (Finset.mem_univ v)
    _ ≤ sizeInf b (X a i) :=
        Finset.single_le_sum (f := fun k' => ∑ v', ‖(Algebra.TensorProduct.basis (Ainf F) b).repr (X a i) k' v'‖)
          (fun k' _ => Finset.sum_nonneg fun v' _ => norm_nonneg _) (Finset.mem_univ k)
    _ ≤ ∑ i', sizeInf b (X a i') :=
        Finset.single_le_sum (f := fun i' => sizeInf b (X a i')) (fun i' _ => hI _) (Finset.mem_univ i)
    _ ≤ sizeTup b X :=
        Finset.single_le_sum (f := fun a' => ∑ i', sizeInf b (X a' i'))
          (fun a' _ => Finset.sum_nonneg fun i' _ => hI _) (Finset.mem_univ a)

theorem continuous_coordEquiv
    (hc : IsHomeomorph fun (y : Ainf F ⊗[F] E) (k : Fin d) =>
      (Algebra.TensorProduct.basis (Ainf F) b).repr y k) :
    Continuous (coordEquiv hF b) :=
  continuous_pi fun k => (continuous_ainfEquiv hF).comp ((continuous_apply k).comp hc.continuous)

theorem continuous_coordEquiv_symm
    (hc : IsHomeomorph fun (y : Ainf F ⊗[F] E) (k : Fin d) =>
      (Algebra.TensorProduct.basis (Ainf F) b).repr y k) :
    Continuous (coordEquiv hF b).symm := by
  have h1 : Continuous fun w : Fin d → InfinitePlace F → ℝ => fun k => (ainfEquiv hF).symm (w k) :=
    continuous_pi fun k => (continuous_ainfEquiv_symm hF).comp (continuous_apply k)
  have h2 := (hc.homeomorph _).symm.continuous.comp h1
  convert h2 using 1
  funext w
  apply (hc.homeomorph _).injective
  rw [Function.comp_apply, Homeomorph.apply_symm_apply]
  funext k
  show (Algebra.TensorProduct.basis (Ainf F) b).repr ((coordEquiv hF b).symm w) k = _
  apply (ainfEquiv hF).injective
  rw [AddEquiv.apply_symm_apply]
  have := congrFun ((coordEquiv hF b).apply_symm_apply w) k
  exact this

end Coord

theorem size_neg_pow_integrable : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ (n M : ℕ) (μ : Measure (Fin n → Fin M → Ainf F ⊗[F] E)), μ.IsAddHaarMeasure → Continuous (sizeTup b : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ) ∧ (∀ X : Fin n → Fin M → Ainf F ⊗[F] E, 0 ≤ sizeTup b X) ∧ ∃ N : ℕ, ∫⁻ X, ENNReal.ofReal (((1 + sizeTup b X) ^ N)⁻¹) ∂μ < ⊤ := by
  intro F E _ _ _ _ _ σ hCM d b n M μ hμ
  have hF : IsTotallyReal F := hCM.1
  haveI : SecondCountableTopology (Ainf F) := secondCountable_Ainf hF
  haveI : T2Space (Ainf F) := inferInstanceAs (T2Space (∀ v : InfinitePlace F, v.Completion))
  obtain ⟨hring, -, -, -, -, -, hhom, hborel, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (Ainf F)
  haveI := hring
  haveI := hborel n M
  have hc := hhom d b
  have hce := continuous_coordEquiv hF b hc
  have hcs := continuous_coordEquiv_symm hF b hc
  have hnorm : ∀ y : Ainf F ⊗[F] E, sizeInf b y = ∑ k, ∑ v, ‖coordEquiv hF b y k v‖ := fun y => by
    simp only [abs_coordEquiv, sizeInf]
  have hcontI : Continuous (sizeInf b : Ainf F ⊗[F] E → ℝ) := by
    have : (sizeInf b : Ainf F ⊗[F] E → ℝ) = fun y => ∑ k, ∑ v, ‖coordEquiv hF b y k v‖ := funext hnorm
    rw [this]
    refine continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun v _ => ?_
    exact ((continuous_apply v).comp ((continuous_apply k).comp hce)).norm
  have hcontT : Continuous (sizeTup b : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ) := by
    unfold sizeTup
    refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun i _ => ?_
    exact hcontI.comp ((continuous_apply i).comp (continuous_apply a))
  have hI0 : ∀ y : Ainf F ⊗[F] E, 0 ≤ sizeInf b y := fun y =>
    Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun v _ => norm_nonneg _
  have hT0 : ∀ X : Fin n → Fin M → Ainf F ⊗[F] E, 0 ≤ sizeTup b X := fun X =>
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun i _ => hI0 _
  refine ⟨hcontT, hT0, ?_⟩
  let e := tupEquiv hF b n M
  have he : Continuous e :=
    continuous_pi fun a => continuous_pi fun i => hce.comp ((continuous_apply i).comp (continuous_apply a))
  have hes : Continuous e.symm :=
    continuous_pi fun a => continuous_pi fun i => hcs.comp ((continuous_apply i).comp (continuous_apply a))
  let W := Fin n → Fin M → Fin d → InfinitePlace F → ℝ
  haveI b1 : BorelSpace (Fin d → InfinitePlace F → ℝ) := inferInstance
  haveI s1 : SecondCountableTopology (Fin d → InfinitePlace F → ℝ) := inferInstance
  haveI b2 : BorelSpace (Fin M → Fin d → InfinitePlace F → ℝ) := Pi.borelSpace
  haveI s2 : SecondCountableTopology (Fin M → Fin d → InfinitePlace F → ℝ) := inferInstance
  haveI b3 : BorelSpace W := Pi.borelSpace
  haveI : (Measure.map e μ).IsAddHaarMeasure := e.isAddHaarMeasure_map μ he hes
  obtain ⟨N, hN⟩ := exists_nat_gt (Module.finrank ℝ W : ℝ)
  refine ⟨N, ?_⟩
  have hfin := finite_integral_one_add_norm (μ := Measure.map e μ) (E := W) (r := (N : ℝ)) hN
  have hmeas : Measurable fun y : W => ENNReal.ofReal ((1 + ‖y‖) ^ (-(N : ℝ))) := by
    refine ENNReal.measurable_ofReal.comp ?_
    exact (Continuous.rpow_const (by fun_prop) fun y => Or.inl (by positivity)).measurable
  rw [lintegral_map hmeas he.measurable] at hfin
  refine lt_of_le_of_lt (lintegral_mono fun X => ?_) hfin
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : (0 : ℝ) < 1 + ‖e X‖ := by positivity
  rw [Real.rpow_neg h1.le, Real.rpow_natCast]
  have h2 : 1 + ‖e X‖ ≤ 1 + sizeTup b X := by
    have := norm_tupEquiv_le hF b n M X
    linarith
  exact inv_anti₀ (pow_pos h1 N) (pow_le_pow_left₀ h1.le h2 N)

end GlobalTheory.CompanionTheory.SW.SizeInt
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SizeFunctionRapidDecayIntegrableStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.size_function_rapid_decay_integrable : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ (n M : ℕ) (μ : Measure (Fin n → Fin M → Ainf F ⊗[F] E)), μ.IsAddHaarMeasure → Continuous (sizeTup b : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ) ∧ (∀ X : Fin n → Fin M → Ainf F ⊗[F] E, 0 ≤ sizeTup b X) ∧ ∃ N : ℕ, ∫⁻ X, ENNReal.ofReal (((1 + sizeTup b X) ^ N)⁻¹) ∂μ < ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.SW.SizeInt.size_neg_pow_integrable | exact GlobalTheory.CompanionTheory.SW.SizeInt.size_neg_pow_integrable | (intros; apply GlobalTheory.CompanionTheory.SW.SizeInt.size_neg_pow_integrable <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsSizeMulLe
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.SizeScale

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}

theorem continuous_size (b : Module.Basis (Fin d) F E) :
    Continuous (sizeInf b : Ainf F ⊗[F] E → ℝ) := by
  have : IsModuleTopology (Ainf F) (Ainf F ⊗[F] E) := ⟨rfl⟩
  unfold sizeInf
  refine continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun v _ => ?_
  have hk : Continuous fun y : Ainf F ⊗[F] E =>
      (Algebra.TensorProduct.basis (Ainf F) b).coord k y :=
    IsModuleTopology.continuous_of_linearMap _
  simp only [← Module.Basis.coord_apply]
  exact continuous_norm.comp ((continuous_apply v).comp hk)

theorem size_nonneg (b : Module.Basis (Fin d) F E) (y : Ainf F ⊗[F] E) : 0 ≤ sizeInf b y :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem tup_nonneg {M n : ℕ} (b : Module.Basis (Fin d) F E) (X : Fin n → Fin M → Ainf F ⊗[F] E) :
    0 ≤ sizeTup b X :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => size_nonneg b _

theorem size_add_le (b : Module.Basis (Fin d) F E) (x y : Ainf F ⊗[F] E) :
    sizeInf b (x + y) ≤ sizeInf b x + sizeInf b y := by
  unfold sizeInf
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun v _ => ?_
  rw [map_add (f := _)]
  exact norm_add_le _ _

theorem size_zero (b : Module.Basis (Fin d) F E) : sizeInf b (0 : Ainf F ⊗[F] E) = 0 := by
  unfold sizeInf
  refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun v _ => ?_
  have h0 : ((0 : Fin d →₀ Ainf F) k) v = 0 := rfl
  rw [map_zero, h0, norm_zero]

theorem size_sum_le {ι : Type} (b : Module.Basis (Fin d) F E) (s : Finset ι)
    (f : ι → Ainf F ⊗[F] E) : sizeInf b (∑ c ∈ s, f c) ≤ ∑ c ∈ s, sizeInf b (f c) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [size_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (size_add_le b _ _).trans (by gcongr)

theorem coord_le_size (b : Module.Basis (Fin d) F E) (y : Ainf F ⊗[F] E) (j : Fin d)
    (v : InfinitePlace F) :
    ‖(Algebra.TensorProduct.basis (Ainf F) b).repr y j v‖ ≤ sizeInf b y := by
  unfold sizeInf
  calc ‖(Algebra.TensorProduct.basis (Ainf F) b).repr y j v‖
      ≤ ∑ w, ‖(Algebra.TensorProduct.basis (Ainf F) b).repr y j w‖ :=
        Finset.single_le_sum
          (f := fun w => ‖(Algebra.TensorProduct.basis (Ainf F) b).repr y j w‖)
          (fun _ _ => norm_nonneg _) (Finset.mem_univ v)
    _ ≤ _ := Finset.single_le_sum
        (f := fun k => ∑ w, ‖(Algebra.TensorProduct.basis (Ainf F) b).repr y k w‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ j)

theorem repr_mul (b : Module.Basis (Fin d) F E) (x y : Ainf F ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis (Ainf F) b).repr (x * y) k =
      ∑ i, ∑ j, (Algebra.TensorProduct.basis (Ainf F) b).repr x i *
        (Algebra.TensorProduct.basis (Ainf F) b).repr y j *
          algebraMap F (Ainf F) (b.repr (b i * b j) k) := by
  set B := Algebra.TensorProduct.basis (Ainf F) b with hB
  have hBB : ∀ i j, B.repr (B i * B j) k = algebraMap F (Ainf F) (b.repr (b i * b j) k) := by
    intro i j
    simp [hB, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.TensorProduct.basis_repr_tmul]
  conv_lhs => rw [← B.sum_repr x, ← B.sum_repr y, Finset.sum_mul_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, Finsupp.coe_finsetSum, Finset.sum_apply, smul_mul_smul_comm, map_smul,
    Finsupp.smul_apply, hBB, smul_eq_mul]

theorem exists_size_mul_le (b : Module.Basis (Fin d) F E) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x y : Ainf F ⊗[F] E, sizeInf b (x * y) ≤ K * sizeInf b x * sizeInf b y := by
  obtain ⟨S₀, hS₀⟩ := (Set.finite_range (fun p : Fin d × Fin d × Fin d × InfinitePlace F =>
    ‖(algebraMap F (Ainf F) (b.repr (b p.1 * b p.2.1) p.2.2.1)) p.2.2.2‖)).bddAbove
  set S := |S₀| with hS
  have hS0 : 0 ≤ S := abs_nonneg _
  have hs : ∀ i j k v, ‖(algebraMap F (Ainf F) (b.repr (b i * b j) k)) v‖ ≤ S := fun i j k v =>
    (hS₀ ⟨(i, j, k, v), rfl⟩).trans (le_abs_self _)
  refine ⟨(d : ℝ) * d * S, by positivity, fun x y => ?_⟩
  set B := Algebra.TensorProduct.basis (Ainf F) b with hB
  have hpt : ∀ k (v : InfinitePlace F), ‖B.repr (x * y) k v‖ ≤
      (d : ℝ) * S * sizeInf b y * ∑ i, ‖B.repr x i v‖ := by
    intro k v
    have hev : B.repr (x * y) k v =
        ∑ i, ∑ j, B.repr x i v * B.repr y j v * (algebraMap F (Ainf F) (b.repr (b i * b j) k)) v := by
      rw [repr_mul b x y k]
      have := map_sum (Pi.evalRingHom (fun w : InfinitePlace F => w.Completion) v)
        (fun i => ∑ j, B.repr x i * B.repr y j * algebraMap F (Ainf F) (b.repr (b i * b j) k))
        Finset.univ
      refine this.trans (Finset.sum_congr rfl fun i _ => ?_)
      exact map_sum (Pi.evalRingHom (fun w : InfinitePlace F => w.Completion) v) _ _
    rw [hev]
    calc ‖∑ i, ∑ j, B.repr x i v * B.repr y j v * (algebraMap F (Ainf F) (b.repr (b i * b j) k)) v‖
        ≤ ∑ i, ∑ j : Fin d, ‖B.repr x i v‖ * sizeInf b y * S := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          rw [norm_mul, norm_mul]
          exact mul_le_mul (mul_le_mul_of_nonneg_left (coord_le_size b y j v) (norm_nonneg _))
            (hs i j k v) (norm_nonneg _) (mul_nonneg (norm_nonneg _) (size_nonneg b y))
      _ = (d : ℝ) * S * sizeInf b y * ∑ i, ‖B.repr x i v‖ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
  calc sizeInf b (x * y) = ∑ k, ∑ v : InfinitePlace F, ‖B.repr (x * y) k v‖ := rfl
    _ ≤ ∑ k : Fin d, ∑ v : InfinitePlace F, (d : ℝ) * S * sizeInf b y * ∑ i, ‖B.repr x i v‖ :=
        Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun v _ => hpt k v
    _ = (d : ℝ) * ((d : ℝ) * S * sizeInf b y * ∑ v : InfinitePlace F, ∑ i, ‖B.repr x i v‖) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Finset.mul_sum]
    _ = (d : ℝ) * d * S * sizeInf b x * sizeInf b y := by
        have : sizeInf b x = ∑ v : InfinitePlace F, ∑ i, ‖B.repr x i v‖ := Finset.sum_comm
        rw [this]; ring

end

theorem size_rmul_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ (n M : ℕ) (C : Set (Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E))), IsCompact C → ∃ c : ℝ, 0 < c ∧ ∀ g ∈ C, ∀ X : Fin n → Fin M → Ainf F ⊗[F] E, sizeTup b (rmul (Ainf F) X g) ≤ c * sizeTup b X := by
  intro F E _ _ _ _ _ σ _ d b n M C hC
  obtain ⟨K, hK0, hK⟩ := exists_size_mul_le b
  have hcont : Continuous fun g : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E) =>
      ∑ c, ∑ a, sizeInf b (g c a) :=
    continuous_finsetSum _ fun c _ => continuous_finsetSum _ fun a _ =>
      (continuous_size b).comp (continuous_id.matrix_elem c a)
  obtain ⟨D, hD⟩ := (hC.image hcont).bddAbove
  refine ⟨K * |D| + 1, by positivity, fun g hg X => ?_⟩
  have hg' : ∀ c, ∑ a, sizeInf b (g c a) ≤ |D| := fun c =>
    (Finset.single_le_sum (f := fun c => ∑ a, sizeInf b (g c a))
      (fun _ _ => Finset.sum_nonneg fun _ _ => size_nonneg b _) (Finset.mem_univ c)).trans
      ((hD ⟨g, hg, rfl⟩).trans (le_abs_self _))
  calc sizeTup b (rmul (Ainf F) X g)
      = ∑ a, ∑ i, sizeInf b (∑ c, X c i * g c a) := rfl
    _ ≤ ∑ a, ∑ i, ∑ c, K * sizeInf b (X c i) * sizeInf b (g c a) :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun i _ =>
          (size_sum_le b _ _).trans (Finset.sum_le_sum fun c _ => hK _ _)
    _ = ∑ i, ∑ c, K * sizeInf b (X c i) * ∑ a, sizeInf b (g c a) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun c _ => (Finset.mul_sum _ _ _).symm
    _ ≤ ∑ i, ∑ c, K * sizeInf b (X c i) * |D| :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun c _ =>
          mul_le_mul_of_nonneg_left (hg' c) (mul_nonneg hK0 (size_nonneg b _))
    _ = K * |D| * sizeTup b X := by
        unfold sizeTup
        rw [Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ (K * |D| + 1) * sizeTup b X := by
        nlinarith [tup_nonneg b X]

end GlobalTheory.CompanionTheory.SW.SizeScale
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ArchimedeanGramFiberContinuousDensity
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.LocGauss

theorem fibre_lintegral_eq_density {V X Y : Type}
    [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V]
    [MeasurableSpace V] [BorelSpace V]
    [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure V) (ν : Measure X) [IsLocallyFiniteMeasure ν] [ν.IsOpenPosMeasure]
    (f : V → Y) (g : V → X) (ι : X → Y) (hι : Function.Injective ι) (hg : Continuous g)
    (hf : ∀ v, f v = ι (g v)) (B : Set X) (fib : X → Measure V)
    (hfib : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B) ν B fib)
    (b₀ : X) (O : Set X) (hO : IsOpen O) (hOB : O ⊆ B) (hb₀ : b₀ ∈ O)
    (T : X → V → V) (κ : X → ℝ≥0)
    (hT : ContinuousOn (fun p : X × V => T p.1 p.2) (O ×ˢ Set.univ))
    (hκ : ContinuousOn κ O) (hκ0 : ∀ b ∈ O, κ b ≠ 0)
    (hm : ∀ b ∈ O, fib b = (κ b : ℝ≥0∞) • (fib b₀).map (T b))
    (w u : V → ℝ≥0∞) (hw : Measurable w) (hu : Continuous u) (hwμ : ∫⁻ v, w v ∂μ < ∞)
    (C : ℝ≥0) (huw : ∀ v, u v ≤ C * w v)
    (hwT : ∀ L : Set X, IsCompact L → L ⊆ O → ∃ c : ℝ≥0, ∀ b ∈ L, ∀ v,
      w (T b v) ≤ c * w v ∧ w v ≤ c * w (T b v))
    (d : X → ℝ≥0∞) (hd : ContinuousOn d O)
    (hdens : ∀ L : Set X, IsCompact L → L ⊆ O → ∫⁻ v in g ⁻¹' L, u v ∂μ = ∫⁻ b in L, d b ∂ν) :
    ∫⁻ v, u v ∂(fib b₀) = d b₀ := by
  have hum : Measurable u := hu.measurable
  have hAt : ∀ b ∈ O, ∀ v, ContinuousAt (fun p : X × V => T p.1 p.2) (b, v) := fun b hb v =>
    hT.continuousAt ((hO.prod isOpen_univ).mem_nhds ⟨hb, Set.mem_univ v⟩)
  have hTc : ∀ b ∈ O, Continuous (T b) := fun b hb =>
    continuous_iff_continuousAt.2 fun v =>
      ContinuousAt.comp (f := fun v : V => (b, v)) (g := fun p : X × V => T p.1 p.2)
        (hAt b hb v) (by fun_prop)
  have hTm : ∀ b ∈ O, Measurable (T b) := fun b hb => (hTc b hb).measurable

  have hint : ∀ b ∈ O, ∀ h : V → ℝ≥0∞, Measurable h →
      ∫⁻ v, h v ∂(fib b) = (κ b : ℝ≥0∞) * ∫⁻ v, h (T b v) ∂(fib b₀) := by
    intro b hb h hh
    rw [hm b hb, lintegral_smul_measure, lintegral_map hh (hTm b hb), smul_eq_mul]
  obtain ⟨L, hLn, hLO, hLc⟩ := local_compact_nhds (hO.mem_nhds hb₀)
  obtain ⟨c, hc⟩ := hwT L hLc hLO
  have hLB : L ⊆ B := hLO.trans hOB

  have hex : ∃ b₁ ∈ L, ∫⁻ v, w v ∂(fib b₁) < ∞ := by
    by_contra hcon
    push_neg at hcon
    have h1 : ∫⁻ v in g ⁻¹' L, w v ∂μ = ∫⁻ b in L, ∫⁻ v, w v ∂(fib b) ∂ν :=
      FibreDensity.lintegral_preimage hι hf hg hfib hLc hLB hw
    have h2 : ∫⁻ b in L, ∫⁻ v, w v ∂(fib b) ∂ν = ∞ := by
      rw [setLIntegral_congr_fun hLc.measurableSet (g := fun _ => ∞)
        (fun b hb => top_le_iff.1 (hcon b hb)), setLIntegral_const,
        ENNReal.top_mul (Measure.measure_pos_of_mem_nhds ν hLn).ne']
    have h3 : ∫⁻ v in g ⁻¹' L, w v ∂μ ≤ ∫⁻ v, w v ∂μ := setLIntegral_le_lintegral _ _
    rw [h1, h2] at h3
    exact absurd (h3.trans_lt hwμ) (lt_irrefl _)
  obtain ⟨b₁, hb₁, hb₁f⟩ := hex

  have hI : ∫⁻ v, w v ∂(fib b₀) < ∞ := by
    have h1 := hint b₁ (hLO hb₁) w hw
    have hk : (κ b₁ : ℝ≥0∞) ≠ 0 := by exact_mod_cast hκ0 b₁ (hLO hb₁)
    have h2 : ∫⁻ v, w (T b₁ v) ∂(fib b₀) < ∞ := by
      by_contra hcon
      rw [not_lt, top_le_iff] at hcon
      rw [h1, hcon, ENNReal.mul_top hk] at hb₁f
      exact lt_irrefl _ hb₁f
    calc ∫⁻ v, w v ∂(fib b₀) ≤ ∫⁻ v, (c : ℝ≥0∞) * w (T b₁ v) ∂(fib b₀) :=
          lintegral_mono fun v => (hc b₁ hb₁ v).2
      _ = (c : ℝ≥0∞) * ∫⁻ v, w (T b₁ v) ∂(fib b₀) :=
          lintegral_const_mul _ (hw.comp (hTm b₁ (hLO hb₁)))
      _ < ∞ := ENNReal.mul_lt_top ENNReal.coe_lt_top h2

  have hbound : ∀ b ∈ L, ∀ v, u (T b v) ≤ ((C : ℝ≥0∞) * c) * w v := by
    intro b hb v
    calc u (T b v) ≤ C * w (T b v) := huw _
      _ ≤ C * (c * w v) := by gcongr; exact (hc b hb v).1
      _ = _ := by rw [mul_assoc]
  have hbfin : ∫⁻ v, ((C : ℝ≥0∞) * c) * w v ∂(fib b₀) ≠ ∞ := by
    rw [lintegral_const_mul _ hw]
    exact (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.coe_lt_top) hI).ne
  set H : X → ℝ≥0∞ := fun b => ∫⁻ v, u (T b v) ∂(fib b₀) with hH
  have hHfin : ∀ b ∈ L, H b ≠ ∞ := fun b hb =>
    ne_top_of_le_ne_top hbfin (lintegral_mono fun v => hbound b hb v)
  have hHc : ∀ b ∈ interior L, ContinuousAt H b := by
    intro b hb
    have hbL : L ∈ 𝓝 b := mem_interior_iff_mem_nhds.1 hb
    have hbO : b ∈ O := hLO (interior_subset hb)
    refine tendsto_lintegral_filter_of_dominated_convergence (fun v => ((C : ℝ≥0∞) * c) * w v)
      ?_ ?_ hbfin ?_
    · filter_upwards [hbL] with b' hb'
      exact hum.comp (hTm b' (hLO hb'))
    · filter_upwards [hbL] with b' hb'
      exact Filter.Eventually.of_forall fun v => hbound b' hb' v
    · refine Filter.Eventually.of_forall fun v => ?_
      have h1 : ContinuousAt (fun b' : X => T b' v) b :=
        ContinuousAt.comp (f := fun b' : X => (b', v)) (g := fun p : X × V => T p.1 p.2)
          (hAt b hbO v) (by fun_prop)
      exact (hu.continuousAt.comp h1).tendsto
  set G : X → ℝ≥0∞ := fun b => ∫⁻ v, u v ∂(fib b) with hG
  have hGc : ContinuousOn G (interior L) := by
    intro b hb
    have hbL : L ∈ 𝓝 b := mem_interior_iff_mem_nhds.1 hb
    have hbO : b ∈ O := hLO (interior_subset hb)
    have h1 : ContinuousAt (fun b' => (κ b' : ℝ≥0∞) * H b') b := by
      have hk : ContinuousAt (fun b' => (κ b' : ℝ≥0∞)) b :=
        ENNReal.continuous_coe.continuousAt.comp (hκ.continuousAt (hO.mem_nhds hbO))
      exact ENNReal.Tendsto.mul hk (Or.inr (hHfin b (interior_subset hb))) (hHc b hb)
        (Or.inr ENNReal.coe_ne_top)
    refine (h1.congr ?_).continuousWithinAt
    filter_upwards [hbL] with b' hb'
    exact (hint b' (hLO hb') u hum).symm
  have key := eq_of_setLIntegral_compact_eq X ν (interior L) isOpen_interior G d hGc
    (hd.mono (interior_subset.trans hLO)) (fun S hS hSL => ?_) b₀ (mem_interior_iff_mem_nhds.2 hLn)
  · exact key
  · have hSO : S ⊆ O := hSL.trans (interior_subset.trans hLO)
    rw [← hdens S hS hSO]
    exact (FibreDensity.lintegral_preimage hι hf hg hfib hS (hSO.trans hOB) hum).symm

end GlobalTheory.CompanionTheory.SW.LocGauss

namespace GlobalTheory.CompanionTheory.SW.LocGauss

theorem ofReal_inv_pow_le {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c) (hab : a ≤ c * b)
    (N : ℕ) : ENNReal.ofReal ((b ^ N)⁻¹) ≤
      ((c ^ N).toNNReal : ℝ≥0∞) * ENNReal.ofReal ((a ^ N)⁻¹) := by
  have h1 : (b ^ N)⁻¹ ≤ c ^ N * (a ^ N)⁻¹ := by
    have h2 : a ^ N ≤ c ^ N * b ^ N := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ ha.le hab N
    rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  calc ENNReal.ofReal ((b ^ N)⁻¹) ≤ ENNReal.ofReal (c ^ N * (a ^ N)⁻¹) :=
        ENNReal.ofReal_le_ofReal h1
    _ = _ := ENNReal.ofReal_mul (by positivity)


set_option maxHeartbeats 400000 in
theorem fibre_rapid_eq_density : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (μ : Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)) (ν : Measure (HermR (Ainf F) σ 1)) m, μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib (Ainf F) σ J 1 μ ν m → ∀ φ : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℝ, Continuous φ → (∀ X, 0 ≤ φ X) → RapidDecay b (fun X => (φ X : ℂ)) → ∀ D : HermR (Ainf F) σ 1 → ℝ, Continuous D → (∀ U : Set (HermR (Ainf F) σ 1), MeasurableSet U → ∫⁻ X in gramR (Ainf F) σ J ⁻¹' (Subtype.val '' U), ENNReal.ofReal (φ X) ∂μ = ∫⁻ S in U, ENNReal.ofReal (D S) ∂ν) → ∀ S : HermR (Ainf F) σ 1, IsUnit (S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)).det → ∫⁻ X, ENNReal.ofReal (φ X) ∂(m S) = ENNReal.ofReal (D S) := by
  intro F E _ _ _ _ _ σ hσ M J hJ d b μ ν m hμ hν hfib φ hφc hφ0 hφr D hDc hD S hS
  have hLoc : IsLocR (Ainf F) := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hσ.1
  obtain ⟨hTR, hLC, hSC, hT2, -, -, -, -⟩ := id hLoc
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨hKr, hKl, hKs, hK2, -, -, -, hVb, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Ainf F)
  haveI := hKr
  haveI := hKl
  haveI := hKs
  haveI := hK2
  haveI := hVb 1 M
  obtain ⟨hXl, hXs, hX2, hXb, hlift⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hσ (Ainf F) 1
  haveI := hXl
  haveI := hXs
  haveI := hX2
  haveI := hXb
  obtain ⟨g, hgc, hgf⟩ := hlift M J hJ
  have hKU := GlobalTheory.T.units_open_embedding_local_tensor F E σ hσ (Ainf F) hLoc

  set B : Set (HermR (Ainf F) σ 1) :=
    {S | IsUnit (S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)).det} with hBdef
  have hB : IsOpen B := by
    have hdet : Continuous fun S : HermR (Ainf F) σ 1 =>
        (S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)).det :=
      Continuous.matrix_det continuous_subtype_val
    have : B = (fun S : HermR (Ainf F) σ 1 =>
        (S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)).det) ⁻¹' Set.range Units.val := by
      ext S
      simp [hBdef, IsUnit]
    rw [this]
    exact hKU.isOpen_range.preimage hdet
  have hfib' : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ (gramR (Ainf F) σ J) Subtype.val (g ⁻¹' B) ν B m := by
    have e : g ⁻¹' B = {X | IsUnit (gramR (Ainf F) σ J X).det} := by
      ext X
      simp [hBdef, hgf]
    rw [e]
    exact hfib
  obtain ⟨B₁, s, hB₁, hSB₁, hsc, hs1, hsS⟩ := GlobalTheory.T.hermitian_local_continuous_congruence_section F E σ hσ (Ainf F) hLoc 1 S hS
  obtain ⟨κ, hκc, hκ0, -, hκ⟩ := GlobalTheory.T.gram_fiber_measures_gl_equivariant F E σ hσ M J hJ (Ainf F) hLoc 1 μ ν m hμ hν hfib
  obtain ⟨-, hsz0, N, hN⟩ := GlobalTheory.T.size_function_rapid_decay_integrable F E σ hσ d b 1 M μ hμ
  have hszc : Continuous (sizeTup b : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℝ) :=
    (GlobalTheory.T.size_function_rapid_decay_integrable F E σ hσ d b 1 M μ hμ).1
  obtain ⟨hg1, hg2, hg3, -, -⟩ := GlobalTheory.CompanionTheory.SW.GramAlg.gram_algebra F E σ hσ M J hJ (Ainf F) 1
  set w : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞ :=
    fun X => ENNReal.ofReal (((1 + sizeTup b X) ^ N)⁻¹) with hw
  have hwm : Measurable w := by
    refine ENNReal.measurable_ofReal.comp (Continuous.measurable ?_)
    refine Continuous.inv₀ ((continuous_const.add hszc).pow N) fun X => ?_
    have := hsz0 X
    positivity
  obtain ⟨C₀, hC₀⟩ := hφr N
  have huw : ∀ X, ENNReal.ofReal (φ X) ≤ (C₀.toNNReal : ℝ≥0∞) * w X := by
    intro X
    have h1 : 0 < (1 + sizeTup b X) ^ N := by
      have := hsz0 X
      positivity
    have h2 := hC₀ X
    rw [Complex.norm_real, Real.norm_of_nonneg (hφ0 X)] at h2
    have h3 : φ X ≤ C₀.toNNReal * ((1 + sizeTup b X) ^ N)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ h1]
      exact h2.trans (Real.le_coe_toNNReal _)
    calc ENNReal.ofReal (φ X) ≤ ENNReal.ofReal (C₀.toNNReal * ((1 + sizeTup b X) ^ N)⁻¹) :=
          ENNReal.ofReal_le_ofReal h3
      _ = _ := by
        rw [ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal]
  have hrmulc : Continuous fun q : (Fin 1 → Fin M → Ainf F ⊗[F] E) ×
      Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E) => rmul (Ainf F) q.1 q.2 := by
    refine continuous_pi fun a => continuous_pi fun i => ?_
    refine continuous_finsetSum _ fun c _ => ?_
    refine Continuous.mul ?_ ?_
    · exact (continuous_apply i).comp ((continuous_apply c).comp continuous_fst)
    · exact continuous_snd.matrix_elem c a
  have hvalc : ContinuousOn (fun S' => ((s S' : GL (Fin 1) (Ainf F ⊗[F] E)) :
      Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E))) B₁ := Units.continuous_val.comp_continuousOn hsc
  have hinvc : ContinuousOn (fun S' => (((s S')⁻¹ : GL (Fin 1) (Ainf F ⊗[F] E)) :
      Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E))) B₁ :=
    Units.continuous_val.comp_continuousOn (continuous_inv.comp_continuousOn hsc)
  refine fibre_lintegral_eq_density μ ν (gramR (Ainf F) σ J) g Subtype.val Subtype.val_injective
    hgc hgf B m hfib' S (B₁ ∩ B) (hB₁.inter hB) Set.inter_subset_right ⟨hSB₁, hS⟩
    (fun S' X => rmul (Ainf F) X (s S' : GL (Fin 1) (Ainf F ⊗[F] E)))
    (fun S' => κ (s S')) ?_ ?_ ?_ ?_ w (fun X => ENNReal.ofReal (φ X)) hwm
    (ENNReal.continuous_ofReal.comp hφc) hN C₀.toNNReal huw ?_
    (fun S' => ENNReal.ofReal (D S')) (ENNReal.continuous_ofReal.comp hDc).continuousOn ?_
  · refine hrmulc.comp_continuousOn (continuous_snd.continuousOn.prodMk ?_)
    exact hvalc.comp (continuous_fst.continuousOn) fun p hp => hp.1.1
  · exact hκc.comp_continuousOn (hsc.mono Set.inter_subset_left)
  · exact fun S' _ => hκ0 _
  · exact fun S' hS' => hκ _ S S' (hsS S' hS'.1)
  · intro L hL hLO
    have hLB₁ : L ⊆ B₁ := hLO.trans Set.inter_subset_left
    have hC : IsCompact ((fun S' => ((s S' : GL (Fin 1) (Ainf F ⊗[F] E)) :
        Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E))) '' L ∪
        (fun S' => (((s S')⁻¹ : GL (Fin 1) (Ainf F ⊗[F] E)) :
        Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E))) '' L) :=
      (hL.image_of_continuousOn (hvalc.mono hLB₁)).union
        (hL.image_of_continuousOn (hinvc.mono hLB₁))
    obtain ⟨c, hc0, hc⟩ := GlobalTheory.CompanionTheory.SW.SizeScale.size_rmul_le F E σ hσ d b 1 M _ hC
    have h1c : ∀ X Y : Fin 1 → Fin M → Ainf F ⊗[F] E, sizeTup b Y ≤ c * sizeTup b X →
        1 + sizeTup b Y ≤ max c 1 * (1 + sizeTup b X) := by
      intro X Y h
      have hX := hsz0 X
      have h1 : c ≤ max c 1 := le_max_left _ _
      have h2 : 1 ≤ max c 1 := le_max_right _ _
      nlinarith
    refine ⟨((max c 1) ^ N).toNNReal, fun S' hS' X => ?_⟩
    have hup := hc _ (Or.inl ⟨S', hS', rfl⟩) X
    have hdown := hc _ (Or.inr ⟨S', hS', rfl⟩)
      (rmul (Ainf F) X (s S' : GL (Fin 1) (Ainf F ⊗[F] E)))
    have hcancel : rmul (Ainf F) (rmul (Ainf F) X (s S' : GL (Fin 1) (Ainf F ⊗[F] E)))
        (((s S')⁻¹ : GL (Fin 1) (Ainf F ⊗[F] E)) : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)) = X := by
      rw [hg2, ← Units.val_mul, mul_inv_cancel, Units.val_one, hg3]
    rw [hcancel] at hdown
    have p1 : 0 < 1 + sizeTup b X := by
      have := hsz0 X
      positivity
    have p2 : 0 < 1 + sizeTup b (rmul (Ainf F) X (s S' : GL (Fin 1) (Ainf F ⊗[F] E))) := by
      have := hsz0 (rmul (Ainf F) X (s S' : GL (Fin 1) (Ainf F ⊗[F] E)))
      positivity
    have hm0 : 0 ≤ max c 1 := hc0.le.trans (le_max_left _ _)
    exact ⟨ofReal_inv_pow_le p1 p2 hm0 (h1c _ _ hdown) N,
      ofReal_inv_pow_le p2 p1 hm0 (h1c _ _ hup) N⟩
  · intro L hL hLO
    have e : gramR (Ainf F) σ J ⁻¹' (Subtype.val '' L) = g ⁻¹' L := by
      ext X
      simp only [Set.mem_preimage, Set.mem_image, hgf]
      constructor
      · rintro ⟨x, hx, hxv⟩
        exact Subtype.val_injective hxv ▸ hx
      · exact fun hv => ⟨g X, hv, rfl⟩
    rw [← e]
    exact hD L hL.measurableSet

end GlobalTheory.CompanionTheory.SW.LocGauss
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ArchimedeanGramFiberContinuousDensityStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_gram_fiber_continuous_density : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (μ : Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)) (ν : Measure (HermR (Ainf F) σ 1)) m, μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib (Ainf F) σ J 1 μ ν m → ∀ φ : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℝ, Continuous φ → (∀ X, 0 ≤ φ X) → RapidDecay b (fun X => (φ X : ℂ)) → ∀ D : HermR (Ainf F) σ 1 → ℝ, Continuous D → (∀ U : Set (HermR (Ainf F) σ 1), MeasurableSet U → ∫⁻ X in gramR (Ainf F) σ J ⁻¹' (Subtype.val '' U), ENNReal.ofReal (φ X) ∂μ = ∫⁻ S in U, ENNReal.ofReal (D S) ∂ν) → ∀ S : HermR (Ainf F) σ 1, IsUnit (S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)).det → ∫⁻ X, ENNReal.ofReal (φ X) ∂(m S) = ENNReal.ofReal (D S) := by
  first | exact @GlobalTheory.CompanionTheory.SW.LocGauss.fibre_rapid_eq_density | exact GlobalTheory.CompanionTheory.SW.LocGauss.fibre_rapid_eq_density | (intros; apply GlobalTheory.CompanionTheory.SW.LocGauss.fibre_rapid_eq_density <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ScalarHermitianTraceAndUnit
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ScalarHermitianTraceAndUnit
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.BB.ScalTrace

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem hermScal_entry {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (R : Type) [CommRing R] [Algebra F R] (s : R) :
    (hermScal R σ s : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0 = algebraMap R (R ⊗[F] E) s := by
  rw [Algebra.TensorProduct.algebraMap_apply]
  rfl

theorem trace_det : ∀ (F E : Type) [Field F] [Field E] [Algebra F E], (1 / 2 : F) ≠ 0 → Module.finrank F E = 2 → ∀ (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] (β : F), algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) ((hermScal R σ (algebraMap F R β) : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0) = algebraMap F R β ∧ (β ≠ 0 → IsUnit ((hermScal R σ (algebraMap F R β) : Matrix (Fin 1) (Fin 1) (R ⊗[F] E))).det) := by
  intro F E _ _ _ h2 hf σ R _ _ β
  have hfin : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  let b : Module.Basis (Fin 2) F E := Module.finBasisOfFinrankEq F E hf
  have hent := hermScal_entry σ R (algebraMap F R β)
  refine ⟨?_, fun hβ => ?_⟩
  · rw [hent, Algebra.trace_algebraMap_of_basis (Algebra.TensorProduct.basis R b) (algebraMap F R β)]
    have h20 : (2 : F) ≠ 0 := by
      intro h
      apply h2
      simp [h]
    have hhalf : algebraMap F R (1 / 2) * algebraMap F R 2 = 1 := by
      rw [← map_mul, one_div, inv_mul_cancel₀ h20, map_one]
    rw [Fintype.card_fin, nsmul_eq_mul]
    have h2R : ((2 : ℕ) : R) = algebraMap F R 2 := by
      rw [map_ofNat]
      norm_num
    rw [h2R, ← mul_assoc, hhalf, one_mul]
  · rw [Matrix.det_fin_one, hent]
    exact ((isUnit_iff_ne_zero.2 hβ).map (algebraMap F R)).map (algebraMap R (R ⊗[F] E))

end GlobalTheory.CompanionTheory.SW.BB.ScalTrace
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ScalarHermitianTraceAndUnitStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scalar_hermitian_trace_and_unit : ∀ (F E : Type) [Field F] [Field E] [Algebra F E], (1 / 2 : F) ≠ 0 → Module.finrank F E = 2 → ∀ (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] (β : F), algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) ((hermScal R σ (algebraMap F R β) : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0) = algebraMap F R β ∧ (β ≠ 0 → IsUnit ((hermScal R σ (algebraMap F R β) : Matrix (Fin 1) (Fin 1) (R ⊗[F] E))).det) := by
  first | exact @GlobalTheory.CompanionTheory.SW.BB.ScalTrace.trace_det | exact GlobalTheory.CompanionTheory.SW.BB.ScalTrace.trace_det | (intros; apply GlobalTheory.CompanionTheory.SW.BB.ScalTrace.trace_det <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarFundamentalDomainRankOneDensity
namespace GlobalTheory.CompanionTheory.SW.BB

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem bound_hermitian : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf laminf → (∀ v, IsStdV v (lam v)) → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (minf : HermR (Ainf F) σ 1 → Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)), IsGramFib (Ainf F) σ J 1 (coordW (Ainf F) b laminf 1 M) (coordHerm (Ainf F) σ b laminf 1) minf → ∀ (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)), (∀ v, IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b (lam v) 1 M) (coordHerm (Fv F v) σ b (lam v) 1) (m v)) → ∀ β : F, β ≠ 0 → ∃ (φ : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℝ) (C : ℝ), Continuous φ ∧ (∀ X, 0 < φ X) ∧ ∫⁻ X, ENNReal.ofReal (φ X) ∂(minf (hermScal (Ainf F) σ (algebraMap F _ β))) < ⊤ ∧ ∀ a : ℕ, 0 < a → ∃ I : ℝ≥0, ∫⁻ X in {X | ∀ v, projV v (projFin X) ∈ {X : (Fin 1 → Fin M → Fv F v ⊗[F] E) | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v}}, ENNReal.ofReal (φ (projInf X)) ∂(thetaMeas σ J μ 𝓕 {X : Fin 1 → Fin M → E | gramE σ J X = fun _ _ => algebraMap F E β}) = (I : ℝ≥0∞) ∧ |(I : ℝ) - (∫⁻ X, ENNReal.ofReal (φ X) ∂(minf (hermScal (Ainf F) σ (algebraMap F _ β)))).toReal * ∏' v, (m v (hermScal (Fv F v) σ (algebraMap F _ β)) {X : (Fin 1 → Fin M → Fv F v ⊗[F] E) | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v}).toReal| ≤ C * (a : ℝ) ^ (Module.finrank ℚ F * M) := by
  intro F E _ _ _ _ _ σ hCM M J hJ hM d b laminf lam hinf hlam μ 𝓕 hμ h𝓕 minf hminf m hm β hβ
  obtain ⟨hF, hEc, hfin, hconj⟩ := id hCM
  have hd : d = 2 := by
    have h := Module.finrank_eq_card_basis b
    simpa [hfin] using h.symm
  obtain ⟨B, hBs, hBd, hBE, hBR⟩ := GlobalTheory.T.exists_trace_form_gram_matrix_in_basis F E σ hCM M J hJ d b
  obtain ⟨ρ, e, hρ, he, heρ, hen, hem⟩ := GlobalTheory.T.infinite_adele_haar_map_eq_scaled_volume F hF
  have hP : ∀ w, ∃ P : Matrix (Fin M × Fin d) (Fin M × Fin d) ℝ,
      P.PosDef ∧ P * (B.map (ρ w))⁻¹ * P = B.map (ρ w) := by
    intro w
    refine GlobalTheory.T.symmetric_invertible_exists_posdef_congruence _ _ ?_ ?_
    · exact hBs.map _
    · have h := RingHom.map_det (ρ w) B
      rw [RingHom.mapMatrix_apply] at h
      rw [← h]
      exact (map_ne_zero _).2 hBd
  choose Pm hPd hPm using hP
  obtain ⟨lf, hlf, hlf1⟩ := GlobalTheory.T.exists_finite_adele_haar_normalized F
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  haveI := GlobalTheory.T.quotient_probability_measure F E σ hCM M J hJ μ 𝓕 hμ h𝓕
  obtain ⟨hgi, hgf⟩ := GlobalTheory.T.gram_coordinates_measurable F E σ hCM M J hJ d b e he
  obtain ⟨hii, hif⟩ := GlobalTheory.T.trace_form_invariance_under_unitary F E σ M J d b B ρ e heρ
    (fun h => ((hBR (AF F)).2 h _ (fun p q => rfl)).1)
  have hcard : Fintype.card (Fin M × Fin d) = 2 * M := by simp [hd, mul_comm]
  obtain ⟨C, Df, Dinf, hDf, ⟨hDc, hD0, hDd⟩, hmain⟩ :=
    GlobalTheory.T.positive_majorant_gaussian F hF (Fin M × Fin d) M hcard hM B hBs hBd ρ hρ Pm hPd hPm lf hlf hlf1
      (HA (AF F) σ J) (prH μ 𝓕) (ginf e σ J b) (gfin σ J b) hgi hgf hii hif
      (fun N hN => GlobalTheory.T.average_rational_vector_count_ball_bound F E σ hCM M J hJ hM d b ρ e he heρ hen μ 𝓕 hμ h𝓕 N hN)
  obtain ⟨hgc, hgr⟩ := GlobalTheory.T.gaussian_continuous_rapid_decay F E σ hCM M d b e he hen Pm
  have h2 : (1 / 2 : F) ≠ 0 := by norm_num
  have hinfint : ∫⁻ X, ENNReal.ofReal (gaussQ e b Pm X)
      ∂(minf (hermScal (Ainf F) σ (algebraMap F _ β))) =
      ENNReal.ofReal ((Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (2 * M - 1) * Dinf (fun w => ρ w β)) := by
    obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hF
    haveI : BorelSpace (Ainf F) := ⟨rfl⟩
    obtain ⟨hK1, hK2, hK3⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hCM (Ainf F) d b laminf hinf.1
    obtain ⟨t1, t2, t3, t4, t5, t6, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (Ainf F)
    have hs := GlobalTheory.T.scalar_hermitian_trace_and_unit F E h2 hfin σ (Ainf F) β
    have hDcont : Continuous fun S : HermR (Ainf F) σ 1 =>
        (Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (2 * M - 1) * Dinf (e (algebraMap F (Ainf F) (1 / 2) *
          Algebra.trace (Ainf F) (Ainf F ⊗[F] E) ((S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)) 0 0))) := by
      refine continuous_const.mul (hDc.comp (he.continuous.comp (continuous_const.mul (t6.comp ?_))))
      exact (continuous_apply_apply 0 0).comp continuous_subtype_val
    have h := GlobalTheory.T.archimedean_gram_fiber_continuous_density F E σ hCM M J hJ d b (coordW (Ainf F) b laminf 1 M)
      (coordHerm (Ainf F) σ b laminf 1) minf (hK2 1 M) (hK3 1) hminf (gaussQ e b Pm) hgc
      (fun X => (Real.exp_pos _).le) (hgr hPd) _ hDcont
      (GlobalTheory.T.archimedean_local_density_formula F E σ hCM M J hJ hM d b B (hBR (Ainf F)).1 ρ e he heρ Pm laminf hinf.1
        (hem laminf hinf) Dinf hDc hD0 hDd) (hermScal (Ainf F) σ (algebraMap F _ β)) (hs.2 hβ)
    rw [h, hs.1]
    have : (e (algebraMap F (Ainf F) β)) = fun w => ρ w β := funext fun w => heρ β w
    rw [this]
  have hκ : 0 ≤ (Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (2 * M - 1) * Dinf (fun w => ρ w β) :=
    mul_nonneg (pow_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _)) _) (hD0 _)
  refine ⟨gaussQ e b Pm, C, hgc, fun X => Real.exp_pos _, ?_, ?_⟩
  · rw [hinfint]; exact ENNReal.ofReal_lt_top
  · intro a ha
    obtain ⟨I, hI, hIb⟩ := hmain a ha β hβ
    obtain ⟨c1, c2, c3⟩ := hDf a ha
    have hprod := GlobalTheory.T.global_product_gram_fiber_rank_one F E σ hCM M J hJ d b lam hlam m hm lf hlf hlf1 a ha (Df a) c1 c2
      (fun U hU => by
        rw [GlobalTheory.T.finite_adelic_trace_form_coordinates F E σ hCM M J hJ d b B (hBR (Af F)).1 lf hlf a U]
        exact c3 U hU) β hβ
    refine ⟨I, ?_, ?_⟩
    · rw [GlobalTheory.T.trace_form_rational_theta_identity F E σ hCM M J hJ d b B hBE ρ e he heρ Pm μ 𝓕 hμ h𝓕 a ha β]
      exact hI
    · rw [hinfint, hprod.tprod_eq, ENNReal.toReal_ofReal hκ]
      convert hIb using 3
      ring

end GlobalTheory.CompanionTheory.SW.BB
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarFundamentalDomainRankOneDensityStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaMeas_rank_one_sub_density_product_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf laminf → (∀ v, IsStdV v (lam v)) → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (minf : HermR (Ainf F) σ 1 → Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)), IsGramFib (Ainf F) σ J 1 (coordW (Ainf F) b laminf 1 M) (coordHerm (Ainf F) σ b laminf 1) minf → ∀ (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)), (∀ v, IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b (lam v) 1 M) (coordHerm (Fv F v) σ b (lam v) 1) (m v)) → ∀ β : F, β ≠ 0 → ∃ (φ : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℝ) (C : ℝ), Continuous φ ∧ (∀ X, 0 < φ X) ∧ ∫⁻ X, ENNReal.ofReal (φ X) ∂(minf (hermScal (Ainf F) σ (algebraMap F _ β))) < ⊤ ∧ ∀ a : ℕ, 0 < a → ∃ I : ℝ≥0, ∫⁻ X in {X | ∀ v, projV v (projFin X) ∈ {X : (Fin 1 → Fin M → Fv F v ⊗[F] E) | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v}}, ENNReal.ofReal (φ (projInf X)) ∂(thetaMeas σ J μ 𝓕 {X : Fin 1 → Fin M → E | gramE σ J X = fun _ _ => algebraMap F E β}) = (I : ℝ≥0∞) ∧ |(I : ℝ) - (∫⁻ X, ENNReal.ofReal (φ X) ∂(minf (hermScal (Ainf F) σ (algebraMap F _ β)))).toReal * ∏' v, (m v (hermScal (Fv F v) σ (algebraMap F _ β)) {X : (Fin 1 → Fin M → Fv F v ⊗[F] E) | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v}).toReal| ≤ C * (a : ℝ) ^ (Module.finrank ℚ F * M) := by
  first | exact @GlobalTheory.CompanionTheory.SW.BB.bound_hermitian | exact GlobalTheory.CompanionTheory.SW.BB.bound_hermitian | (intros; apply GlobalTheory.CompanionTheory.SW.BB.bound_hermitian <;> assumption)
end
