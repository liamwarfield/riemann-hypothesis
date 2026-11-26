module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GlobalUnitScalingHaarProductFormula
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductUnfold
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductScaling

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresIntegralFormula
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresIntegralFormula
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.ScaleCont

section Actions

variable {K : Type} [CommRing K] {n M : ℕ}

def tupR (X : Fin n → Fin M → K) (g : Matrix (Fin n) (Fin n) K) : Fin n → Fin M → K :=
  fun a i => ∑ c, X c i * g c a

theorem tupR_tupR (X : Fin n → Fin M → K) (g h : Matrix (Fin n) (Fin n) K) :
    tupR (tupR X g) h = tupR X (g * h) := by
  funext a i
  simp only [tupR, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_assoc _ _ _

theorem tupR_one (X : Fin n → Fin M → K) : tupR X 1 = X := by
  funext a i
  simp [tupR, Matrix.one_apply]

def tupAction : DistribMulAction (GL (Fin n) K) (Fin n → Fin M → K) where
  smul q X := tupR X ((q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  one_smul X := by
    show tupR X (((1 : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = X
    simp [tupR_one]
  mul_smul q q' X := by
    show tupR X (((q * q')⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      tupR (tupR X ((q'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
        ((q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    rw [tupR_tupR, mul_inv_rev, Units.val_mul]
  smul_zero q := by
    show tupR 0 _ = 0
    funext a i
    simp [tupR]
  smul_add q X Y := by
    show tupR (X + Y) _ = tupR X _ + tupR Y _
    funext a i
    simp [tupR, add_mul, Finset.sum_add_distrib]

theorem cT_one' (s : K →+* K) : cT s (1 : Matrix (Fin n) (Fin n) K) = 1 := by
  simp [cT, Matrix.map_one]

theorem cT_mul' (s : K →+* K) (A B : Matrix (Fin n) (Fin n) K) :
    cT s (A * B) = cT s B * cT s A := by
  simp [cT, Matrix.map_mul, Matrix.transpose_mul]

def hermAction (s : K →+* K) (H : AddSubgroup (Matrix (Fin n) (Fin n) K))
    (hmem : ∀ (S : H) (g : Matrix (Fin n) (Fin n) K),
      cT s g * (S : Matrix (Fin n) (Fin n) K) * g ∈ H) :
    DistribMulAction (GL (Fin n) K) H where
  smul q S := ⟨cT s ((q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (S : Matrix (Fin n) (Fin n) K) * ((q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K), hmem S _⟩
  one_smul S := by
    apply Subtype.ext
    show cT s (((1 : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (S : Matrix (Fin n) (Fin n) K) * (((1 : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = S
    simp [cT_one']
  mul_smul q q' S := by
    apply Subtype.ext
    show cT s (((q * q')⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (S : Matrix (Fin n) (Fin n) K) * (((q * q')⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      cT s ((q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (cT s ((q'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          (S : Matrix (Fin n) (Fin n) K) * ((q'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
        ((q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    rw [mul_inv_rev, Units.val_mul, cT_mul']
    simp only [Matrix.mul_assoc]
  smul_zero q := by
    apply Subtype.ext
    show cT s _ * ((0 : H) : Matrix (Fin n) (Fin n) K) * _ = 0
    simp
  smul_add q S T := by
    apply Subtype.ext
    show cT s _ * ((S + T : H) : Matrix (Fin n) (Fin n) K) * _ =
      cT s _ * (S : Matrix (Fin n) (Fin n) K) * _ + cT s _ * (T : Matrix (Fin n) (Fin n) K) * _
    simp [Matrix.mul_add, Matrix.add_mul]

variable [TopologicalSpace K] [IsTopologicalRing K]

theorem continuous_inv_val :
    Continuous fun q : GL (Fin n) K => ((q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
  Units.continuous_val.comp continuous_inv

theorem tup_continuousSMul :
    @ContinuousSMul (GL (Fin n) K) (Fin n → Fin M → K) (tupAction (K := K)).toSMul _ _ := by
  letI := tupAction (K := K) (n := n) (M := M)
  refine ⟨?_⟩
  show Continuous fun p : GL (Fin n) K × (Fin n → Fin M → K) =>
    tupR p.2 ((p.1⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  refine continuous_pi fun a => continuous_pi fun i => ?_
  simp only [tupR]
  refine continuous_finsetSum _ fun c _ => ?_
  refine Continuous.mul ?_ ?_
  · exact (continuous_apply i).comp ((continuous_apply c).comp continuous_snd)
  · exact (continuous_apply a).comp ((continuous_apply c).comp (continuous_inv_val.comp continuous_fst))

theorem herm_continuousSMul (s : K →+* K) (hs : Continuous s)
    (H : AddSubgroup (Matrix (Fin n) (Fin n) K))
    (hmem : ∀ (S : H) (g : Matrix (Fin n) (Fin n) K),
      cT s g * (S : Matrix (Fin n) (Fin n) K) * g ∈ H) :
    @ContinuousSMul (GL (Fin n) K) H (hermAction s H hmem).toSMul _ _ := by
  letI := hermAction s H hmem
  refine ⟨?_⟩
  have hq : Continuous fun p : GL (Fin n) K × H =>
      ((p.1⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := continuous_inv_val.comp continuous_fst
  have hS : Continuous fun p : GL (Fin n) K × H => (p.2 : Matrix (Fin n) (Fin n) K) :=
    continuous_subtype_val.comp continuous_snd
  have hc : Continuous fun p : GL (Fin n) K × H =>
      cT s ((p.1⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    simp only [cT]
    exact (hq.matrix_map hs).matrix_transpose
  exact ((hc.matrix_mul hS).matrix_mul hq).subtype_mk _

end Actions

theorem fibre_scale_continuous : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ), ∀ (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)) (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib R σ J n μ ν m → ∃ κ : GL (Fin n) (R ⊗[F] E) → ℝ≥0, Continuous κ ∧ (∀ g, κ g ≠ 0) ∧ κ 1 = 1 ∧ ∀ (g : GL (Fin n) (R ⊗[F] E)) (S S' : HermR R σ n), (S' : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = cT (sigR R σ) (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) → m S' = κ g • (m S).map (fun X => rmul R X (g : Matrix (Fin n) (Fin n) (R ⊗[F] E))) := by
  intro F E _ _ _ _ _ σ hCM M J hJ R _ _ _ _ _ hR n μ ν m hμ hν hm
  obtain ⟨r1, r2, r3, r4, -⟩ := id hR
  haveI := r1
  haveI := r2
  haveI := r3
  haveI := r4
  obtain ⟨k1, k2, k3, k4, k5, -, -, k8, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM R
  haveI := k1
  haveI := k2
  haveI := k3
  haveI := k4
  obtain ⟨h1, h2, h3, h4, -⟩ := GlobalTheory.T.hermitian_matrices_locally_compact_borel F E σ hCM R n
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  haveI : BorelSpace (Fin n → Fin M → R ⊗[F] E) := k8 n M
  have hmem := (GlobalTheory.T.gram_right_action_identities F E σ hCM M J hJ R n).2.2.2.1
  letI a1 : DistribMulAction (GL (Fin n) (R ⊗[F] E)) (Fin n → Fin M → R ⊗[F] E) := tupAction
  haveI c1 : ContinuousSMul (GL (Fin n) (R ⊗[F] E)) (Fin n → Fin M → R ⊗[F] E) := tup_continuousSMul
  obtain ⟨χ₁, hχ₁c, hχ₁⟩ := GlobalTheory.T.haar_modular_character_of_continuous_action (Fin n → Fin M → R ⊗[F] E) μ (GL (Fin n) (R ⊗[F] E))
  letI a2 : DistribMulAction (GL (Fin n) (R ⊗[F] E)) (HermR R σ n) :=
    hermAction (sigR R σ) (HermR R σ n) hmem
  haveI c2 : ContinuousSMul (GL (Fin n) (R ⊗[F] E)) (HermR R σ n) :=
    herm_continuousSMul (sigR R σ) k5 (HermR R σ n) hmem
  obtain ⟨χ₂, hχ₂c, hχ₂⟩ := GlobalTheory.T.haar_modular_character_of_continuous_action (HermR R σ n) ν (GL (Fin n) (R ⊗[F] E))
  have hne : ∀ (χ : GL (Fin n) (R ⊗[F] E) →* ℝ≥0) (g), χ g ≠ 0 := by
    intro χ g h0
    have : χ (g * g⁻¹) = 1 := by simp
    rw [map_mul, h0, zero_mul] at this
    exact zero_ne_one this
  refine ⟨fun g => χ₁ g * χ₂ g⁻¹, hχ₁c.mul (hχ₂c.comp continuous_inv), ?_, ?_, ?_⟩
  · exact fun g => mul_ne_zero (hne χ₁ g) (hne χ₂ g⁻¹)
  · simp
  · intro g S S' hS'
    let τ : HermR R σ n → HermR R σ n := fun S => g⁻¹ • S
    have hτ : ∀ S : HermR R σ n, (τ S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) =
        cT (sigR R σ) (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * S *
          (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) := by
      intro S
      show cT (sigR R σ) (((g⁻¹)⁻¹ : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * S *
        (((g⁻¹)⁻¹ : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = _
      rw [inv_inv]
    have hS'τ : S' = τ S := Subtype.ext (hS'.trans (hτ S).symm)
    have hmap₁ : μ.map (fun X => rmul R X (g : Matrix (Fin n) (Fin n) (R ⊗[F] E))) = χ₁ g⁻¹ • μ := by
      have := hχ₁ g⁻¹
      have e : (fun v : Fin n → Fin M → R ⊗[F] E => g⁻¹ • v) =
          fun X => rmul R X (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) := by
        funext X
        show tupR X (((g⁻¹)⁻¹ : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = _
        rw [inv_inv]
        rfl
      rwa [e] at this
    have hmap₂ : ν.map τ = χ₂ g⁻¹ • ν := hχ₂ g⁻¹
    have key := GlobalTheory.T.gram_fiber_measures_rmul_equivariant F E σ hCM M J hJ R hR n μ ν m hμ hν hm
      (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (Matrix.isUnits_det_units g) τ hτ
      (χ₁ g⁻¹) (χ₂ g⁻¹) hmap₁ hmap₂ S
    rw [hS'τ]
    have hinv : χ₁ g * χ₁ g⁻¹ = 1 := by rw [← map_mul]; simp
    calc m (τ S) = (χ₁ g * χ₁ g⁻¹) • m (τ S) := by rw [hinv, one_smul]
      _ = χ₁ g • (χ₁ g⁻¹ • m (τ S)) := by rw [mul_smul]
      _ = χ₁ g • (χ₂ g⁻¹ • (m S).map fun X => rmul R X (g : Matrix (Fin n) (Fin n) (R ⊗[F] E))) := by
        rw [key]
      _ = _ := by rw [mul_smul]

end GlobalTheory.CompanionTheory.SW.ScaleCont
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresIntegralFormulaStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_fiber_measures_gl_equivariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ), ∀ (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)) (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib R σ J n μ ν m → ∃ κ : GL (Fin n) (R ⊗[F] E) → ℝ≥0, Continuous κ ∧ (∀ g, κ g ≠ 0) ∧ κ 1 = 1 ∧ ∀ (g : GL (Fin n) (R ⊗[F] E)) (S S' : HermR R σ n), (S' : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = cT (sigR R σ) (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) → m S' = κ g • (m S).map (fun X => rmul R X (g : Matrix (Fin n) (Fin n) (R ⊗[F] E))) := by
  first | exact @GlobalTheory.CompanionTheory.SW.ScaleCont.fibre_scale_continuous | exact GlobalTheory.CompanionTheory.SW.ScaleCont.fibre_scale_continuous | (intros; apply GlobalTheory.CompanionTheory.SW.ScaleCont.fibre_scale_continuous <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductDensity
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductDensity
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂.Unfold

theorem measurable_vec {K : Type} [Zero K] [MeasurableSpace K] {M n : ℕ} (α : K) :
    Measurable (fun p : (Fin n → K) × (Fin n → Fin M → K) => vec α p.1 p.2) := by
  refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
  refine Fin.cases ?_ (fun i' => ?_) i
  · simp only [vec, Fin.cons_zero]
    exact measurable_const
  · refine Fin.cases ?_ (fun j' => ?_) j
    · simp only [vec, Fin.cons_succ, Fin.cons_zero]
      exact (measurable_pi_apply i').comp measurable_fst
    · simp only [vec, Fin.cons_succ]
      exact (measurable_pi_apply j').comp ((measurable_pi_apply i').comp measurable_snd)

theorem swap_through_fibres {Y C X H : Type} [MeasurableSpace Y] [MeasurableSpace C] [MeasurableSpace X]
    [MeasurableSpace H] (μ₁ : Measure Y) (μc : Measure C) (μ : Measure X) (ν : Measure H)
    [SFinite μ₁] [SFinite μc] [SFinite μ] (U : Set X) (W : Set H) (hW : MeasurableSet W)
    (m : H → Measure X) (hm : ∀ S, SFinite (m S)) (hoff : ∀ S, S ∉ W → m S = 0)
    (hfib : ∀ ψ : X → ℝ≥0∞, Measurable ψ → ∫⁻ v in U, ψ v ∂μ = ∫⁻ S, ∫⁻ v, ψ v ∂(m S) ∂ν)
    (f : Y → C → X → ℝ≥0∞) (hf : Measurable fun p : Y × C × X => f p.1 p.2.1 p.2.2) :
    ∫⁻ y, ∫⁻ c, ∫⁻ S in W, ∫⁻ v, f y c v ∂(m S) ∂ν ∂μc ∂μ₁ =
      ∫⁻ c, ∫⁻ S in W, ∫⁻ y, ∫⁻ v, f y c v ∂(m S) ∂μ₁ ∂ν ∂μc := by
  have restr : ∀ G : H → ℝ≥0∞, (∀ S, S ∉ W → G S = 0) → ∫⁻ S in W, G S ∂ν = ∫⁻ S, G S ∂ν := by
    intro G hG
    rw [← lintegral_indicator hW]
    refine lintegral_congr fun S => ?_
    by_cases hS : S ∈ W
    · simp [hS]
    · simp [hS, hG S hS]
  have hfyc : ∀ y c, Measurable (f y c) := fun y c =>
    hf.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have hfc : ∀ c, Measurable fun p : Y × X => f p.1 c p.2 := fun c =>
    hf.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
  have e1 : ∀ y c, ∫⁻ S in W, ∫⁻ v, f y c v ∂(m S) ∂ν = ∫⁻ v in U, f y c v ∂μ := by
    intro y c
    rw [hfib _ (hfyc y c)]
    refine restr _ fun S hS => ?_
    simp [hoff S hS]
  have hyc : Measurable fun q : Y × C => ∫⁻ v in U, f q.1 q.2 v ∂μ := by
    have : Measurable fun r : (Y × C) × X => f r.1.1 r.1.2 r.2 :=
      hf.comp ((measurable_fst.comp measurable_fst).prodMk
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
    exact this.lintegral_prod_right'
  calc ∫⁻ y, ∫⁻ c, ∫⁻ S in W, ∫⁻ v, f y c v ∂(m S) ∂ν ∂μc ∂μ₁
      = ∫⁻ y, ∫⁻ c, ∫⁻ v in U, f y c v ∂μ ∂μc ∂μ₁ := by simp only [e1]
    _ = ∫⁻ c, ∫⁻ y, ∫⁻ v in U, f y c v ∂μ ∂μ₁ ∂μc :=
        lintegral_lintegral_swap (f := fun y c => ∫⁻ v in U, f y c v ∂μ) hyc.aemeasurable
    _ = ∫⁻ c, ∫⁻ v in U, ∫⁻ y, f y c v ∂μ₁ ∂μ ∂μc := by
        refine lintegral_congr fun c => ?_
        exact lintegral_lintegral_swap (f := fun y v => f y c v) (hfc c).aemeasurable
    _ = ∫⁻ c, ∫⁻ S in W, ∫⁻ y, ∫⁻ v, f y c v ∂(m S) ∂μ₁ ∂ν ∂μc := by
        refine lintegral_congr fun c => ?_
        rw [hfib _ (hfc c).lintegral_prod_left']
        rw [restr]
        · refine lintegral_congr fun S => ?_
          haveI := hm S
          exact lintegral_lintegral_swap (f := fun v y => f y c v)
            ((hfc c).comp measurable_swap).aemeasurable
        · intro S hS
          simp [hoff S hS]

end GlobalTheory.CompanionTheory.SW.PiLocalization₂.Unfold

namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂

theorem lintegral_Uset_eq_Mid : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∫⁻ v in (Uset σ J t B₀ a : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)), φ v ∂(coordW R b lam (n + 1) (M + 1)) = Mid σ J t m₁ m' s B₀ a κ₁ b lam φ := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D φ hφ
  have hCM := D.hCM
  have hlam := D.hlam
  obtain ⟨i₁, i₂, i₃, i₄, -⟩ := id D.hR
  obtain ⟨k₁, k₂, k₃, k₄, -, -, -, hBorel, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM R
  obtain ⟨hK, hW, hH⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hCM R d b lam hlam
  have hJ' := GlobalTheory.CompanionTheory.SW.PiLocalization₂.isHermND_blockOne_algebraMap F E σ M J D.hJ t D.ht
  obtain ⟨-, hlf1, -, -, -, hae1⟩ := GlobalTheory.T.gram_fiber_measure_locally_finite_measurable_supported F E σ hCM (M + 1) 1 _ hJ' R D.hR d b lam hlam m₁ D.hm₁
  obtain ⟨hUo, hlf, hoff, -, -, -⟩ := GlobalTheory.T.gram_fiber_measure_locally_finite_measurable_supported F E σ hCM M n J D.hJ R D.hR d b lam hlam m' D.hm'
  obtain ⟨-, -, h₃, -, h₅, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hCM (M + 1) _ hJ' R
  have hc := (hact (n + 1)).1
  haveI := hBorel n M
  haveI := hBorel (n + 1) (M + 1)
  haveI := hBorel 1 (M + 1)
  haveI : SigmaFinite (coordK R b lam) := inferInstance
  haveI : SigmaFinite (coordW R b lam n M) := inferInstance
  haveI : SigmaFinite (m₁ (hermScal R σ (algebraMap F R t))) := inferInstance
  haveI : BorelSpace (HermR R σ n) := ⟨rfl⟩
  haveI : SFinite (Measure.pi fun _ : Fin n => coordK R b lam) := inferInstance
  have hm : ∀ S, SFinite (m' S) := fun S => inferInstance
  have hUm : MeasurableSet (Unt σ R n) := hUo.measurableSet
  have hB : MeasurableSet B₀ := D.hB₀.measurableSet
  rw [GlobalTheory.T.gram_fiber_cons_product_unfold F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D φ hφ]
  unfold Mid
  refine setLIntegral_congr_fun hB fun x hx => ?_
  refine congrArg _ ?_
  set f : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → (Fin n → R ⊗[F] E) → (Fin n → Fin M → R ⊗[F] E) → ℝ≥0∞ :=
    fun y₀ c X => φ (actW R σ (blockOne (algebraMap F E t) J) (s y₀) (vec (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E)) c X)) with hfdef
  have hf : Measurable fun p : (Fin 1 → Fin (M + 1) → R ⊗[F] E) × (Fin n → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) =>
      f p.1 p.2.1 p.2.2 := by
    have hcm : Measurable (fun p : HA R σ (blockOne (algebraMap F E t) J) × (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) =>
        actW R σ (blockOne (algebraMap F E t) J) p.1 p.2) := by
      haveI : SecondCountableTopology (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) := inferInstance
      haveI : OpensMeasurableSpace (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) := inferInstance
      haveI : OpensMeasurableSpace (HA R σ (blockOne (algebraMap F E t) J)) := inferInstance
      haveI : OpensMeasurableSpace (HA R σ (blockOne (algebraMap F E t) J) × (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)) :=
        Prod.opensMeasurableSpace
      exact hc.measurable
    have hg : Measurable (fun p : (Fin 1 → Fin (M + 1) → R ⊗[F] E) × (Fin n → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) =>
        ((s p.1, vec (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E)) p.2.1 p.2.2) :
          HA R σ (blockOne (algebraMap F E t) J) × (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E))) :=
      (D.hs.comp measurable_fst).prodMk
        ((Unfold.measurable_vec (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E))).comp measurable_snd)
    exact hφ.comp (hcm.comp hg)
  have hae : ∀ᵐ y₀ ∂(m₁ (hermScal R σ (algebraMap F R t))),
      chi σ J t s a b lam ((Uset σ J t B₀ a : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)).indicator φ)
          (scl (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E)) y₀) =
        ∫⁻ c : Fin n → R ⊗[F] E, ∫⁻ S' in Unt σ R n, ∫⁻ X, f y₀ c X ∂(m' S') ∂(coordHerm R σ b lam n)
          ∂(Measure.pi fun _ => coordK R b lam) := by
    filter_upwards [hae1 (hermScal R σ (algebraMap F R t))] with y₀ hy₀
    exact GlobalTheory.T.gram_fiber_cons_product_fold F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D φ hφ x hx y₀ hy₀
  rw [lintegral_congr_ae hae]
  exact Unfold.swap_through_fibres (m₁ (hermScal R σ (algebraMap F R t)))
    (Measure.pi fun _ => coordK R b lam) (coordW R b lam n M) (coordHerm R σ b lam n)
    {X | IsUnit (gramR R σ J X).det} (Unt σ R n) hUm m' hm hoff D.hm'.2.1 f hf

end GlobalTheory.CompanionTheory.SW.PiLocalization₂
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductDensityStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.setLIntegral_Uset_coordW_eq_Mid : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∫⁻ v in (Uset σ J t B₀ a : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)), φ v ∂(coordW R b lam (n + 1) (M + 1)) = Mid σ J t m₁ m' s B₀ a κ₁ b lam φ := by
  first | exact @GlobalTheory.CompanionTheory.SW.PiLocalization₂.lintegral_Uset_eq_Mid | exact GlobalTheory.CompanionTheory.SW.PiLocalization₂.lintegral_Uset_eq_Mid | (intros; apply GlobalTheory.CompanionTheory.SW.PiLocalization₂.lintegral_Uset_eq_Mid <;> assumption)
end
end
