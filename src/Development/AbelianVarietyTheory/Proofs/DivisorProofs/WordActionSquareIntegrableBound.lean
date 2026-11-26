module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordOperatorL2BoundPolynomial
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordOperatorL2BoundPolynomial
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
open GlobalTheory.ArchDecay

noncomputable section

namespace GlobalTheory.ArchDecay.WordL2Estimates

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

abbrev Dir (F : Type) [Field F] [NumberField F] (κ : Type) : Type :=
  (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)

theorem real_smul_fun {X : Type} (r : ℝ) (f : X → ℂ) : r • f = (r : ℂ) • f := by
  funext x
  simp only [Pi.smul_apply, Complex.real_smul, smul_eq_mul]

theorem dD_add_fun (v : κ → mixedEmbedding.mixedSpace F) {Φ Ψ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ)
    (hΨ : Ψ ∈ schA F κ) : dD F v (Φ + Ψ) = dD F v Φ + dD F v Ψ := by
  funext x
  simp only [dD, Pi.add_apply]
  exact deriv_add ((SchAStab.archimedeanDirectionalDerivative_mem_adelicSchwartz F v hΦ).1 x) ((SchAStab.archimedeanDirectionalDerivative_mem_adelicSchwartz F v hΨ).1 x)

theorem dD_pureA_apply (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (v : κ → mixedEmbedding.mixedSpace F) (x : κ → AF F) :
    dD F v (pureA F f g) x = fderiv ℝ f (arch F x) v * g (fun i => (x i).2) := by
  rw [dD, (SchAStab.hasDerivAt_line F f g x v).deriv]

theorem dD_dir {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    (∀ v w : κ → mixedEmbedding.mixedSpace F, dD F (v + w) Φ = dD F v Φ + dD F w Φ) ∧
      ∀ (r : ℝ) (v : κ → mixedEmbedding.mixedSpace F), dD F (r • v) Φ = (r : ℂ) • dD F v Φ := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    refine ⟨fun v w => funext fun x => ?_, fun r v => funext fun x => ?_⟩
    · simp only [Pi.add_apply, dD_pureA_apply, map_add (f := _), add_mul]
    · simp only [Pi.smul_apply, dD_pureA_apply, map_smul, smul_eq_mul, Complex.real_smul]
      ring
  | zero =>
    have h0 : ∀ u : κ → mixedEmbedding.mixedSpace F, dD F u (0 : (κ → AF F) → ℂ) = 0 := fun u => by
      funext x; simp [dD]
    exact ⟨fun v w => by rw [h0, h0, h0, add_zero], fun r v => by rw [h0, h0, smul_zero]⟩
  | add Φ Ψ hΦ hΨ h1 h2 =>
    refine ⟨fun v w => ?_, fun r v => ?_⟩
    · rw [dD_add_fun _ hΦ hΨ, dD_add_fun _ hΦ hΨ, dD_add_fun _ hΦ hΨ, h1.1, h2.1]
      abel
    · rw [dD_add_fun _ hΦ hΨ, dD_add_fun _ hΦ hΨ, h1.2, h2.2, smul_add]
  | smul a Φ hΦ h =>
    refine ⟨fun v w => ?_, fun r v => ?_⟩
    · rw [dD_smul, dD_smul, dD_smul, h.1, smul_add]
    · rw [dD_smul, dD_smul, h.2, smul_comm]

theorem mM_add_l (l l' : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ) (f : (κ → AF F) → ℂ) :
    mM F (l + l') f = mM F l f + mM F l' f := by
  funext x
  simp only [mM, ContinuousLinearMap.add_apply, Complex.ofReal_add, Pi.add_apply, add_mul]

theorem mM_smul_l (r : ℝ) (l : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ) (f : (κ → AF F) → ℂ) :
    mM F (r • l) f = (r : ℂ) • mM F l f := by
  funext x
  simp only [mM, ContinuousLinearMap.smul_apply, smul_eq_mul, Complex.ofReal_mul, Pi.smul_apply, mul_assoc]

theorem mM_add_f (l : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ) (f g : (κ → AF F) → ℂ) :
    mM F l (f + g) = mM F l f + mM F l g := by
  funext x
  simp only [mM, Pi.add_apply, mul_add]

variable (T : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ((κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ)) (c : ℂ)

theorem dR_add_dir {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) (ζ ζ' : Dir F κ) :
    dR F T c (ζ + ζ') Φ = dR F T c ζ Φ + dR F T c ζ' Φ := by
  unfold dR
  rw [Prod.fst_add, Prod.snd_add, (dD_dir hΦ).1, map_add T, mM_add_l, smul_add]
  abel

theorem dR_smul_dir {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) (r : ℝ) (ζ : Dir F κ) :
    dR F T c (r • ζ) Φ = r • dR F T c ζ Φ := by
  unfold dR
  rw [Prod.smul_fst, Prod.smul_snd, (dD_dir hΦ).2, map_smul T, mM_smul_l, smul_comm c, ← smul_add, real_smul_fun]

theorem dR_add_fun (ζ : Dir F κ) {Φ Ψ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) (hΨ : Ψ ∈ schA F κ) :
    dR F T c ζ (Φ + Ψ) = dR F T c ζ Φ + dR F T c ζ Ψ := by
  unfold dR
  rw [dD_add_fun _ hΦ hΨ, mM_add_f, smul_add]
  abel

theorem dR_smul_fun (ζ : Dir F κ) (a : ℂ) (f : (κ → AF F) → ℂ) : dR F T c ζ (a • f) = a • dR F T c ζ f := by
  unfold dR
  rw [dD_smul, mM_smul, smul_comm c a, ← smul_add]

theorem dR_mem (ζ : Dir F κ) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) : dR F T c ζ Φ ∈ schA F κ :=
  Submodule.add_mem _ (SchAStab.archimedeanDirectionalDerivative_mem_adelicSchwartz F ζ.1 hΦ).2 (Submodule.smul_mem _ c (SchAStab.mem_schA_mM F _ hΦ))

theorem wordR_mem (zs : List (Dir F κ)) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) : wordR F T c zs Φ ∈ schA F κ := by
  induction zs with
  | nil => exact hΦ
  | cons ζ zs ih => exact dR_mem T c ζ ih

theorem wordR_add (zs : List (Dir F κ)) {Φ Ψ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) (hΨ : Ψ ∈ schA F κ) :
    wordR F T c zs (Φ + Ψ) = wordR F T c zs Φ + wordR F T c zs Ψ := by
  induction zs with
  | nil => rfl
  | cons ζ zs ih =>
    show dR F T c ζ (wordR F T c zs (Φ + Ψ)) = dR F T c ζ (wordR F T c zs Φ) + dR F T c ζ (wordR F T c zs Ψ)
    rw [ih, dR_add_fun T c ζ (wordR_mem T c zs hΦ) (wordR_mem T c zs hΨ)]

theorem wordR_smul (zs : List (Dir F κ)) (a : ℂ) (f : (κ → AF F) → ℂ) :
    wordR F T c zs (a • f) = a • wordR F T c zs f := by
  induction zs with
  | nil => rfl
  | cons ζ zs ih =>
    show dR F T c ζ (wordR F T c zs (a • f)) = a • dR F T c ζ (wordR F T c zs f)
    rw [ih, dR_smul_fun]

theorem wordR_concat (zs : List (Dir F κ)) (ζ : Dir F κ) (Φ : (κ → AF F) → ℂ) :
    wordR F T c (zs ++ [ζ]) Φ = wordR F T c zs (dR F T c ζ Φ) := by
  unfold wordR
  rw [List.foldr_append]
  rfl

def wordRL (zs : List (Dir F κ)) : schA F κ →ₗ[ℂ] ((κ → AF F) → ℂ) where
  toFun Φ := wordR F T c zs Φ
  map_add' Φ Ψ := wordR_add T c zs Φ.2 Ψ.2
  map_smul' a Φ := wordR_smul T c zs a Φ

theorem wordR_sum {ι : Type} [Fintype ι] (zs : List (Dir F κ)) (a : ι → ℂ) (Φ : ι → (κ → AF F) → ℂ)
    (h : ∀ i, Φ i ∈ schA F κ) : wordR F T c zs (∑ i, a i • Φ i) = ∑ i, a i • wordR F T c zs (Φ i) := by
  have e : (∑ i, a i • Φ i) = ((∑ i, a i • (⟨Φ i, h i⟩ : schA F κ) : schA F κ) : (κ → AF F) → ℂ) := by
    simp only [Submodule.coe_sum, Submodule.coe_smul]
  rw [e]
  exact (map_sum (wordRL T c zs) _ _).trans (Finset.sum_congr rfl fun i _ => map_smul (wordRL T c zs) _ _)

def dRL {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) : Dir F κ →ₗ[ℝ] ((κ → AF F) → ℂ) where
  toFun ζ := dR F T c ζ Φ
  map_add' := dR_add_dir T c hΦ
  map_smul' := dR_smul_dir T c hΦ

theorem dR_expand {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ (Dir F κ)) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ)
    (ζ : Dir F κ) : dR F T c ζ Φ = ∑ i, ((b.repr ζ i : ℝ) : ℂ) • dR F T c (b i) Φ := by
  calc dR F T c ζ Φ = dRL T c hΦ ζ := rfl
    _ = dRL T c hΦ (∑ i, b.repr ζ i • b i) := by rw [b.sum_repr]
    _ = ∑ i, b.repr ζ i • dRL T c hΦ (b i) := by rw [map_sum]; simp only [map_smul]
    _ = _ := Finset.sum_congr rfl fun i _ => real_smul_fun _ _

theorem lintegral_enorm_sq {X : Type} {m : MeasurableSpace X} (μ : Measure X) (f : X → ℂ) (hf : AEStronglyMeasurable f μ) :
    ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ = eLpNorm f 2 μ ^ 2 := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (f := f) (μ := μ) (p := 2) (by norm_num) hf
  simpa only [NNReal.coe_ofNat, ENNReal.coe_ofNat, ENNReal.rpow_ofNat] using h.symm

end GlobalTheory.ArchDecay.WordL2Estimates

namespace GlobalTheory.ArchDecay.WordL2Estimates

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
variable (T : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ((κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ)) (c : ℂ)

theorem eLpNorm_wordR_le (μ : @Measure (κ → AF F) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ)
    (P : ℕ) : ∀ Φ ∈ schA F κ, ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : ℝ, 1 ≤ ρ → ∀ zs : List (Dir F κ), zs.length ≤ P →
      (∀ ζ ∈ zs, ‖ζ‖ ≤ ρ) → eLpNorm (wordR F T c zs Φ) 2 μ ≤ ENNReal.ofReal (C * ρ ^ P) := by
  letI : MeasurableSpace (κ → AF F) := borel _
  have hL2 : ∀ Φ ∈ schA F κ, MemLp Φ 2 μ := fun Φ hΦ => GlobalTheory.WeilM.schA_memLp_two F κ μ hμ Φ hΦ
  induction P with
  | zero =>
    intro Φ hΦ
    refine ⟨(eLpNorm Φ 2 μ).toReal, ENNReal.toReal_nonneg, fun ρ _ zs hl _ => ?_⟩
    rw [List.length_eq_zero_iff.1 (Nat.le_zero.1 hl), pow_zero, mul_one,
      ENNReal.ofReal_toReal (hL2 Φ hΦ).eLpNorm_lt_top.ne]
    rfl
  | succ P ih =>
    intro Φ hΦ
    let b := Module.finBasis ℝ (Dir F κ)
    obtain ⟨C₀, h₀, hC₀⟩ := ih Φ hΦ
    choose C h1 hC using fun i => ih (dR F T c (b i) Φ) (dR_mem T c (b i) hΦ)
    let κ₀ := ‖b.equivFunL.toContinuousLinearMap‖
    have hκ₀ : 0 ≤ κ₀ := norm_nonneg _
    have hs : 0 ≤ ∑ i, κ₀ * C i := Finset.sum_nonneg fun i _ => mul_nonneg hκ₀ (h1 i)
    refine ⟨C₀ + ∑ i, κ₀ * C i, add_nonneg h₀ hs, fun ρ hρ zs hl hu => ?_⟩
    have hρ0 : 0 ≤ ρ := zero_le_one.trans hρ
    have hρp : 0 ≤ ρ ^ P := pow_nonneg hρ0 P
    rcases List.eq_nil_or_concat' zs with rfl | ⟨zs', ζ, rfl⟩
    · refine (hC₀ ρ hρ [] (Nat.zero_le _) (by simp)).trans (ENNReal.ofReal_le_ofReal ?_)
      exact mul_le_mul (le_add_of_nonneg_right hs) (pow_le_pow_right₀ hρ P.le_succ) hρp (add_nonneg h₀ hs)
    · have hl' : zs'.length ≤ P := by simpa using hl
      have hu' : ∀ z ∈ zs', ‖z‖ ≤ ρ := fun z hz => hu z (List.mem_append_left _ hz)
      have hζ : ‖ζ‖ ≤ ρ := hu ζ (List.mem_append_right _ (List.mem_singleton_self _))
      have a2 : ∀ i, ‖b.repr ζ i‖ ≤ κ₀ * ρ := fun i =>
        (norm_le_pi_norm (b.equivFunL.toContinuousLinearMap ζ) i).trans
          ((b.equivFunL.toContinuousLinearMap.le_opNorm ζ).trans (mul_le_mul_of_nonneg_left hζ hκ₀))
      rw [wordR_concat, dR_expand T c b hΦ ζ, wordR_sum T c zs' _ _ fun i => dR_mem T c (b i) hΦ]
      calc eLpNorm (∑ i, ((b.repr ζ i : ℝ) : ℂ) • wordR F T c zs' (dR F T c (b i) Φ)) 2 μ
          ≤ ∑ i, eLpNorm (((b.repr ζ i : ℝ) : ℂ) • wordR F T c zs' (dR F T c (b i) Φ)) 2 μ :=
            eLpNorm_sum_le one_le_two
        _ ≤ ∑ i, ENNReal.ofReal (κ₀ * ρ * (C i * ρ ^ P)) := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [eLpNorm_const_smul, ← ofReal_norm_eq_enorm, Complex.norm_real,
              ENNReal.ofReal_mul (mul_nonneg hκ₀ hρ0)]
            exact mul_le_mul' (ENNReal.ofReal_le_ofReal (a2 i)) (hC i ρ hρ zs' hl' hu')
        _ = ENNReal.ofReal (∑ i, κ₀ * ρ * (C i * ρ ^ P)) :=
            (ENNReal.ofReal_sum_of_nonneg fun i _ => mul_nonneg (mul_nonneg hκ₀ hρ0) (mul_nonneg (h1 i) hρp)).symm
        _ ≤ ENNReal.ofReal ((C₀ + ∑ i, κ₀ * C i) * ρ ^ (P + 1)) := by
            refine ENNReal.ofReal_le_ofReal ?_
            have e : ∑ i, κ₀ * ρ * (C i * ρ ^ P) = (∑ i, κ₀ * C i) * ρ ^ (P + 1) := by
              rw [Finset.sum_mul]
              exact Finset.sum_congr rfl fun i _ => by ring
            rw [e]
            exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left h₀) (pow_nonneg hρ0 _)

end GlobalTheory.ArchDecay.WordL2Estimates

namespace GlobalTheory.ArchDecay

theorem wordR_L2_le : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (T : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ((κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ)) (c : ℂ), ∀ Φ ∈ schA F κ, ∀ (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∀ P : ℕ, ∃ C : ℝ, ∀ ρ : ℝ, 1 ≤ ρ → ∀ zs : List ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)), zs.length ≤ P → (∀ ζ ∈ zs, ‖ζ‖ ≤ ρ) → ∫⁻ x, ‖wordR F T c zs Φ x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal (C * ρ ^ (2 * P)) := by
  intro F _ _ κ _ T c Φ hΦ μ hμ P
  obtain ⟨C, hC0, hC⟩ := WordL2Estimates.eLpNorm_wordR_le T c μ hμ P Φ hΦ
  refine ⟨C ^ 2, fun ρ hρ zs hl hu => ?_⟩
  have h := hC ρ hρ zs hl hu
  letI : MeasurableSpace (κ → AF F) := borel _
  have hf := (GlobalTheory.WeilM.schA_memLp_two F κ μ hμ _
    (WordL2Estimates.wordR_mem T c zs hΦ)).aestronglyMeasurable
  rw [WordL2Estimates.lintegral_enorm_sq μ _ hf]
  calc eLpNorm (wordR F T c zs Φ) 2 μ ^ 2 ≤ ENNReal.ofReal (C * ρ ^ P) ^ 2 := pow_le_pow_left' h 2
    _ = ENNReal.ofReal (C ^ 2 * ρ ^ (2 * P)) := by
      rw [← ENNReal.ofReal_pow (mul_nonneg hC0 (pow_nonneg (zero_le_one.trans hρ) _))]
      congr 1
      ring

end GlobalTheory.ArchDecay
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordOperatorL2BoundPolynomialStatement
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
open GlobalTheory.ArchDecay

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.word_operator_L2_bound_polynomial : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (T : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ((κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ)) (c : ℂ), ∀ Φ ∈ schA F κ, ∀ (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∀ P : ℕ, ∃ C : ℝ, ∀ ρ : ℝ, 1 ≤ ρ → ∀ zs : List ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)), zs.length ≤ P → (∀ ζ ∈ zs, ‖ζ‖ ≤ ρ) → ∫⁻ x, ‖wordR F T c zs Φ x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal (C * ρ ^ (2 * P)) := by
  exact @GlobalTheory.ArchDecay.wordR_L2_le
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepMovedArchimedeanCoordsPolynomialHeight
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepMovedArchimedeanCoordsPolynomialHeight
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
open GlobalTheory.ArchDecay

noncomputable section

namespace GlobalTheory.ArchDecay.MovSize

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

abbrev Zs (F : Type) [Field F] [NumberField F] (n d : ℕ) : Type :=
  (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)

theorem infAd_add (a b : mixedEmbedding.mixedSpace F) : infAd F (a + b) = infAd F a + infAd F b := by
  unfold infAd
  rw [map_add (f := _), map_add (f := _)]

theorem infAd_smul (t : ℝ) (a : mixedEmbedding.mixedSpace F) : infAd F (t • a) = realAd F t * infAd F a := by
  refine Prod.ext ?_ ?_
  · show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t • a) =
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ t) * (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a
    rw [← map_mul, Algebra.smul_def]
  · show (0 : FiniteAdeleRing (𝓞 F) F) = 0 * 0
    rw [mul_zero]

theorem liftI_add (M : Model σ X W) (ζ ζ' : Zs F n d) : liftI M (ζ + ζ') = liftI M ζ + liftI M ζ' := by
  unfold liftI
  rw [← map_add (f := _)]
  congr 1
  refine Prod.ext ?_ ?_ <;> funext i <;> simp [infAd_add]

theorem liftI_smul (M : Model σ X W) (t : ℝ) (ζ : Zs F n d) : liftI M (t • ζ) = realAd F t • liftI M ζ := by
  unfold liftI
  rw [← LinearEquiv.map_smul]
  congr 1
  refine Prod.ext ?_ ?_ <;> funext i <;> simp [infAd_smul]

theorem arch_e_liftI (M : Model σ X W) (ζ : Zs F n d) :
    (arch F (M.co.e (liftI M ζ)).1, arch F (M.co.e (liftI M ζ)).2) = ζ := by
  unfold liftI arch
  rw [LinearEquiv.apply_symm_apply]
  refine Prod.ext ?_ ?_ <;> funext i <;>
    exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply _

variable (τ : ∀ w : InfinitePlace F, EmbOver E w)

def readC (M : Model σ X W) : Zs F n d →ₗ[ℝ] (InfinitePlace F → Fin n → Fin d → ℂ) where
  toFun ζ w i j := piInf (τ w) (liftI M ζ i j)
  map_add' ζ ζ' := by funext w i j; simp [liftI_add, map_add (f := _)]
  map_smul' t ζ := by
    funext w i j
    simp only [liftI_smul, Matrix.smul_apply, RingHom.id_apply, Pi.smul_apply]
    rw [GlobalTheory.RealScalar.piInf_realAd_smul, Complex.real_smul]

theorem readC_injective (hCM : IsCMExt F E σ) (M : Model σ X W) : Function.Injective (readC τ M) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro ζ hζ
  have hA := (liftI_at_movI F E σ n d X W M 1 ζ).1
  have h0 : liftI M ζ = 0 := by
    ext i j
    refine GlobalTheory.ArchInj.eq_zero_of_at_of_piInf F E σ hCM τ _ ?_ ?_
    · intro a ha
      have := congrFun (congrFun (hA a ha) i) j
      simpa [Matrix.smul_apply] using this
    · intro w
      exact congrFun (congrFun (congrFun hζ w) i) j
  rw [← arch_e_liftI M ζ, h0, map_zero]
  refine Prod.ext ?_ ?_ <;> funext i <;> exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)

theorem norm_piInf_eq (hCM : IsCMExt F E σ) {w : InfinitePlace F} (τ₀ τ' : EmbOver E w) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    ‖piInf τ' z‖ = ‖piInf τ₀ z‖ := by
  unfold piInf
  rcases infEmb_eq_or_conj hCM τ₀ τ' with e | e
  · rw [RingHom.comp_apply, RingHom.comp_apply, e]
  · rw [RingHom.comp_apply, RingHom.comp_apply, e, RingHom.comp_apply, Complex.norm_conj]

end GlobalTheory.ArchDecay.MovSize


open GlobalTheory.ArchDecay.MovSize in
theorem GlobalTheory.ArchDecay.movI_size : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∃ (C : ℝ) (k : ℕ), ∀ (g : UA σ X.J) (h : UA σ W.J) (ζ : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)), ‖movI M (g, h) ζ‖ ≤ C * ((ht g : ℝ) * ht h) ^ k * ‖ζ‖ := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP
  have hCM : IsCMExt F E σ := hP.base.cm
  set L := readC B.emb M with hL
  obtain ⟨K, -, hK⟩ := L.exists_antilipschitzWith (LinearMap.ker_eq_bot.2 (readC_injective B.emb hCM M))
  set Lc := LinearMap.toContinuousLinearMap L with hLc
  refine ⟨K * (n * d) * ‖Lc‖, 1, fun g h ζ => ?_⟩
  have h1 : ‖movI M (g, h) ζ‖ ≤ K * ‖L (movI M (g, h) ζ)‖ := by
    have := hK.le_mul_dist (movI M (g, h) ζ) 0
    simpa [dist_eq_norm] using this
  have hB : ∀ (w : InfinitePlace F) (τ' : EmbOver E w) k l, ‖piInf τ' (liftI M ζ k l)‖ ≤ ‖L ζ‖ := by
    intro w τ' k l
    rw [norm_piInf_eq hCM (B.emb w) τ']
    exact (norm_le_pi_norm (L ζ w k) l).trans ((norm_le_pi_norm (L ζ w) k).trans (norm_le_pi_norm (L ζ) w))
  have hg : (ht (((g, h)⁻¹ : UA σ X.J × UA σ W.J)).1 : ℝ) = ht g := by
    show ((heightGL F ((g⁻¹ : UA σ X.J) : GL (Fin n) (AE F E))) : ℝ) = heightGL F (g : GL (Fin n) (AE F E))
    rw [Subgroup.coe_inv, heightGL_inv]
  have hh : (ht (((g, h)⁻¹ : UA σ X.J × UA σ W.J)).2 : ℝ) = ht h := by
    show ((heightGL F ((h⁻¹ : UA σ W.J) : GL (Fin d) (AE F E))) : ℝ) = heightGL F (h : GL (Fin d) (AE F E))
    rw [Subgroup.coe_inv, heightGL_inv]
  have hgh : (0 : ℝ) ≤ n * d * ((ht g : ℝ) * ht h) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (mul_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _))
  have hpos : (0 : ℝ) ≤ n * d * ((ht g : ℝ) * ht h) * ‖L ζ‖ := mul_nonneg hgh (norm_nonneg _)
  have h2 : ‖L (movI M (g, h) ζ)‖ ≤ n * d * ((ht g : ℝ) * ht h) * ‖L ζ‖ := by
    refine (pi_norm_le_iff_of_nonneg hpos).2 fun w => ?_
    refine (pi_norm_le_iff_of_nonneg hpos).2 fun i => ?_
    refine (pi_norm_le_iff_of_nonneg hpos).2 fun j => ?_
    show ‖piInf (B.emb w) (liftI M (movI M (g, h) ζ) i j)‖ ≤ _
    rw [(liftI_at_movI F E σ n d X W M (g, h) ζ).2]
    have := GlobalTheory.WeilDirBound.norm_piInf_actAB_le σ n d X.J W.J (g, h)⁻¹ (liftI M ζ) ‖L ζ‖ (norm_nonneg _) hB w
      (B.emb w) i j
    rwa [hg, hh] at this
  have h3 : ‖L ζ‖ ≤ ‖Lc‖ * ‖ζ‖ := Lc.le_opNorm ζ
  have hK0 : (0 : ℝ) ≤ K := K.2
  calc ‖movI M (g, h) ζ‖ ≤ K * (n * d * ((ht g : ℝ) * ht h) * (‖Lc‖ * ‖ζ‖)) :=
        h1.trans (mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left h3 hgh)) hK0)
    _ = K * (n * d) * ‖Lc‖ * ((ht g : ℝ) * ht h) ^ 1 * ‖ζ‖ := by ring
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepMovedArchimedeanCoordsPolynomialHeightStatement
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
open GlobalTheory.ArchDecay

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRep_moved_archimedean_coords_polynomial_height : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∃ (C : ℝ) (k : ℕ), ∀ (g : UA σ X.J) (h : UA σ W.J) (ζ : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)), ‖movI M (g, h) ζ‖ ≤ C * ((ht g : ℝ) * ht h) ^ k * ‖ζ‖ := by
  first | exact @GlobalTheory.ArchDecay.movI_size | exact GlobalTheory.ArchDecay.movI_size | (intros; apply GlobalTheory.ArchDecay.movI_size <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergDerivArchimedeanLiftTraceFormula
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergDerivArchimedeanLiftTraceFormula
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
open GlobalTheory.ArchDecay

noncomputable section

namespace GlobalTheory.ArchDecay.HeisArch

variable {F : Type} [Field F] [NumberField F]

def evIr : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst _ _)

theorem evIr_apply (a : AF F) : evIr a = evI F a := rfl

def sndr : AF F →+* Af F := RingHom.snd _ _

theorem sndr_apply (a : AF F) : sndr a = a.2 := rfl

theorem realAd_mul_infAd (t : ℝ) (α : mixedEmbedding.mixedSpace F) :
    realAd F t * infAd F α = infAd F (t • α) := by
  refine Prod.ext ?_ ?_
  · show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ t) *
        (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm α = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t • α)
    rw [← map_mul, Algebra.smul_def]
  · show (0 : Af F) * 0 = 0
    exact mul_zero _

theorem evIr_infAd (α : mixedEmbedding.mixedSpace F) : evIr (infAd F α) = α := by
  show InfiniteAdeleRing.ringEquiv_mixedSpace F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm α) = α
  exact RingEquiv.apply_symm_apply _ _

theorem sndr_infAd (α : mixedEmbedding.mixedSpace F) : sndr (infAd F α) = 0 := rfl

theorem at_of_snd (z : AF F) (h : z.2 = 0) : At (evI F) z := by
  intro u hu
  have h1 : u.1 = 0 := by
    have : InfiniteAdeleRing.ringEquiv_mixedSpace F u.1 = 0 := hu
    exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (this.trans (map_zero _).symm)
  show u * z = 0
  refine Prod.ext ?_ ?_
  · show u.1 * z.1 = 0
    rw [h1, zero_mul]
  · show u.2 * z.2 = 0
    rw [h, mul_zero]

variable (F) in
theorem exists_strictHenselian_absolutely_closed_local_ring (κ : Type) [Fintype κ] :
    ∃ T : (κ → mixedEmbedding.mixedSpace F) ≃L[ℝ] ((κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ),
      ∀ b y, (T : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ((κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ)) b y =
        Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, y i * b i) := by
  let L : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ((κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ) :=
    (LinearMap.toContinuousLinearMap : ((κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℝ) ≃ₗ[ℝ] _).toLinearMap ∘ₗ
      (GlobalTheory.VacLn.trPair F κ).flip
  have hL : ∀ b y, L b y = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, y i * b i) := fun b y => rfl
  have hinj : Function.Injective L := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro b hb
    apply GlobalTheory.VacLn.trPair_nondeg b
    intro y
    have := congrArg (fun φ : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ => φ y) hb
    simpa [hL, GlobalTheory.VacLn.trPair_apply] using this
  have hdim : Module.finrank ℝ (κ → mixedEmbedding.mixedSpace F) =
      Module.finrank ℝ ((κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ) := by
    rw [← LinearEquiv.finrank_eq (LinearMap.toContinuousLinearMap :
      ((κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℝ) ≃ₗ[ℝ] _)]
    exact (Subspace.dual_finrank_eq).symm
  refine ⟨(LinearMap.linearEquivOfInjective L hinj hdim).toContinuousLinearEquiv, fun b y => ?_⟩
  rfl

end GlobalTheory.ArchDecay.HeisArch

noncomputable section

namespace GlobalTheory.ArchDecay.HeisArch

theorem infAd_zero {F : Type} [Field F] [NumberField F] : infAd F (0 : mixedEmbedding.mixedSpace F) = 0 := by
  unfold infAd; rw [map_zero, map_zero]

theorem heisD_liftI : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ), IsStd ψ → ∃ T : (Fin n × Fin d → mixedEmbedding.mixedSpace F) ≃L[ℝ] ((Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ), ∀ (ζ : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)), ∀ f ∈ schA F (Fin n × Fin d), heisD M ψ (liftI M ζ) f = dR F (T : (Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] ((Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ)) (-(2 * Real.pi * Complex.I)) ζ f := by
  intro F E _ _ _ _ _ σ n d X W M ψ hψ
  obtain ⟨T, hT⟩ := exists_strictHenselian_absolutely_closed_local_ring F (Fin n × Fin d)
  refine ⟨T, fun ζ f hf => ?_⟩
  funext x
  set L : ℝ := Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, arch F x i * ζ.2 i) with hLdef
  set c0 : ℝ := Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
    (evIr (⅟(2 : AF F)) * ∑ i, ζ.1 i * ζ.2 i) with hc0
  have hco : ∀ t : ℝ, M.co.e (realAd F t • liftI M ζ) =
      (fun i => infAd F (t • ζ.1 i), fun i => infAd F (t • ζ.2 i)) := by
    intro t
    rw [map_smul, liftI, LinearEquiv.apply_symm_apply]
    refine Prod.ext ?_ ?_ <;> funext i <;>
      simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, realAd_mul_infAd]
  have hline : ∀ t : ℝ, M.heisLine ψ (liftI M ζ) t f x =
      Complex.exp (-(2 * Real.pi * Complex.I) * ((t * L + t ^ 2 * c0 : ℝ) : ℂ)) *
        f (x + fun i => infAd F (t • ζ.1 i)) := by
    intro t
    simp only [Model.heisLine, Darboux.rho, schr, hco t]
    congr 1
    set P : AF F := x ⬝ᵥ (fun i => infAd F (t • ζ.2 i)) +
      ⅟(2 : AF F) * ((fun i => infAd F (t • ζ.1 i)) ⬝ᵥ (fun i => infAd F (t • ζ.2 i))) with hP
    have hAt : At (evI F) P := by
      apply at_of_snd
      rw [← sndr_apply, hP, map_add (f := _), map_mul, RingHom.map_dotProduct, RingHom.map_dotProduct]
      simp [dotProduct, Function.comp_def, sndr_infAd]
    rw [hψ.2.2 P hAt, ← evIr_apply]
    congr 3
    rw [hP, map_add (f := _), map_mul, RingHom.map_dotProduct, RingHom.map_dotProduct]
    simp only [Function.comp_def, evIr_infAd, dotProduct]
    have e1 : (∑ i, evIr (x i) * (t • ζ.2 i)) = t • ∑ i, arch F x i * ζ.2 i := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_smul_comm]; rfl
    have e2 : evIr (⅟(2 : AF F)) * (∑ i, (t • ζ.1 i) * (t • ζ.2 i)) =
        (t ^ 2) • (evIr (⅟(2 : AF F)) * ∑ i, ζ.1 i * ζ.2 i) := by
      rw [show (∑ i, (t • ζ.1 i) * (t • ζ.2 i)) = (t ^ 2) • ∑ i, ζ.1 i * ζ.2 i from by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [smul_mul_smul_comm, sq]]
      exact mul_smul_comm _ _ _
    rw [e1, e2, map_add (f := _), map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have hg : HasDerivAt (fun t : ℝ => Complex.exp (-(2 * Real.pi * Complex.I) * ((t * L + t ^ 2 * c0 : ℝ) : ℂ)))
      (-(2 * Real.pi * Complex.I) * (L : ℂ)) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => t * L + t ^ 2 * c0) L 0 := by
      have h0 : HasDerivAt (fun t : ℝ => t * L + t ^ 2 * c0) (1 * L + ((2 : ℕ) * (0 : ℝ) ^ (2 - 1)) * c0) 0 :=
        ((hasDerivAt_id' (0 : ℝ)).mul_const L).add ((hasDerivAt_pow 2 (0 : ℝ)).mul_const c0)
      exact h0.congr_deriv (by norm_num)
    have h2 := ((h1.ofReal_comp).const_mul (-(2 * Real.pi * Complex.I))).cexp
    convert h2 using 1
    simp
  have hh : HasDerivAt (fun t : ℝ => f (x + fun i => infAd F (t • ζ.1 i))) (dD F ζ.1 f x) 0 :=
    ((SchAStab.archimedeanDirectionalDerivative_mem_adelicSchwartz F ζ.1 hf).1 x).hasDerivAt
  have hx0 : (x + fun i => infAd F ((0 : ℝ) • ζ.1 i)) = x := by
    funext i
    show x i + infAd F ((0 : ℝ) • ζ.1 i) = x i
    rw [zero_smul, infAd_zero, add_zero]
  show deriv (fun t : ℝ => M.heisLine ψ (liftI M ζ) t f x) 0 = _
  have hd : HasDerivAt (fun t : ℝ => M.heisLine ψ (liftI M ζ) t f x)
      (-(2 * Real.pi * Complex.I) * (L : ℂ) * f (x + fun i => infAd F ((0 : ℝ) • ζ.1 i)) +
        Complex.exp (-(2 * Real.pi * Complex.I) * (((0 : ℝ) * L + (0 : ℝ) ^ 2 * c0 : ℝ) : ℂ)) * dD F ζ.1 f x) 0 := by
    rw [show (fun t : ℝ => M.heisLine ψ (liftI M ζ) t f x) = _ from funext hline]
    exact hg.mul hh
  rw [hd.deriv]
  simp only [dR, mM, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hT, hx0]
  rw [← hLdef]
  simp
  ring

end GlobalTheory.ArchDecay.HeisArch
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergDerivArchimedeanLiftTraceFormulaStatement
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
open GlobalTheory.ArchDecay

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergDeriv_archimedeanLift_traceFormula : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ), IsStd ψ → ∃ T : (Fin n × Fin d → mixedEmbedding.mixedSpace F) ≃L[ℝ] ((Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ), ∀ (ζ : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)), ∀ f ∈ schA F (Fin n × Fin d), heisD M ψ (liftI M ζ) f = dR F (T : (Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] ((Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ)) (-(2 * Real.pi * Complex.I)) ζ f := by
  first | exact @GlobalTheory.ArchDecay.HeisArch.heisD_liftI | exact GlobalTheory.ArchDecay.HeisArch.heisD_liftI | (intros; apply GlobalTheory.ArchDecay.HeisArch.heisD_liftI <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergDerivArchimedeanWeilRepIntertwine
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergDerivArchimedeanWeilRepIntertwine
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
open GlobalTheory.ArchDecay

noncomputable section

namespace GlobalTheory.ArchDecay.HeisWeil

variable {R : Type} [CommRing R] [Invertible (2 : R)] {V : Type} [AddCommGroup V] [Module R V] {Bf : V → V → R}
  {κ : Type} [Fintype κ]

theorem rho_add (dc : Darboux Bf κ) (ψ : AddChar R ℂ) (w : V) (f g : (κ → R) → ℂ) :
    dc.rho ψ w (f + g) = dc.rho ψ w f + dc.rho ψ w g := by
  funext x
  simp [Darboux.rho, schr, mul_add]

theorem rho_smul (dc : Darboux Bf κ) (ψ : AddChar R ℂ) (w : V) (c : ℂ) (f : (κ → R) → ℂ) :
    dc.rho ψ w (c • f) = c • dc.rho ψ w f := by
  funext x
  simp only [Darboux.rho, schr, Pi.smul_apply, smul_eq_mul]
  ring

theorem rho_zero (dc : Darboux Bf κ) (ψ : AddChar R ℂ) (w : V) : dc.rho ψ w (0 : (κ → R) → ℂ) = 0 := by
  funext x
  simp [Darboux.rho, schr]

end GlobalTheory.ArchDecay.HeisWeil

open GlobalTheory.ArchDecay.HeisWeil

theorem GlobalTheory.ArchDecay.HeisWeil.exists_hasDerivAt_adm {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {σ : E →ₐ[F] E} {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]
    (ψ : AddChar (AF F) ℂ) {JA : Matrix α α (AE F E)} {JB : Matrix β β (AE F E)}
    (dc : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (hψ : IsStd ψ) (u : Matrix α β (AE F E))
    (hu : At (evI F) u) (f : (κ → AF F) → ℂ) (hf : f ∈ schA F κ) :
    ∃ Df : (κ → AF F) → ℂ, ∀ l ∈ (adeleClass F).adm κ,
      HasDerivAt (fun t : ℝ => l (dc.rho ψ (realAd F t • u) f)) (l Df) 0 := by
  obtain ⟨D, hD⟩ := GlobalTheory.T.archHeisenbergDerivatives_exist F E σ α β κ ψ JA JB dc hψ
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f₀, g, hg, rfl⟩ := hx
    exact ⟨pureA F (D u f₀) g, fun l hl => (hD u hu f₀).1 g hg l hl⟩
  | zero =>
    refine ⟨0, fun l _ => ?_⟩
    simp only [rho_zero, map_zero]
    exact hasDerivAt_const _ _
  | add x y _ _ hx hy =>
    obtain ⟨Dx, hDx⟩ := hx
    obtain ⟨Dy, hDy⟩ := hy
    refine ⟨Dx + Dy, fun l hl => ?_⟩
    simp only [rho_add, map_add (f := _)]
    exact (hDx l hl).add (hDy l hl)
  | smul c x _ hx =>
    obtain ⟨Dx, hDx⟩ := hx
    refine ⟨c • Dx, fun l hl => ?_⟩
    simp only [rho_smul, map_smul, smul_eq_mul]
    exact (hDx l hl).const_mul c

theorem GlobalTheory.ArchDecay.HeisWeil.heisD_weil : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ (p : UA σ X.J × UA σ W.J) (u : Matrix (Fin n) (Fin d) (AE F E)), At (evI F) u → ∀ f ∈ schA F (Fin n × Fin d), heisD M B.ψ u (om p f) = om p (heisD M B.ψ (actAB (cA σ) p⁻¹ u) f) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP p u hu f hf
  have hψ : IsStd B.ψ := hP.base.std
  have hS := IsUWeilPair.isUSplitting hP.weil
  set u' := actAB (cA σ) p⁻¹ u with hu'def
  have hu' : At (evI F) u' := fun a ha => by
    rw [hu'def, actAB, ← Matrix.smul_mul, ← Matrix.mul_smul, hu a ha, Matrix.mul_zero, Matrix.zero_mul]
  have hact : ∀ t : ℝ, actAB (cA σ) p (realAd F t • u') = realAd F t • u := fun t => by
    simp only [hu'def, actAB]
    rw [Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    simp only [Prod.fst_inv, Prod.snd_inv, Subgroup.coe_inv, Matrix.mul_assoc]
    rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one, Matrix.mul_one, ← Matrix.mul_assoc,
      Units.mul_inv, Matrix.one_mul]
  obtain ⟨Df, hDf⟩ := exists_hasDerivAt_adm B.ψ M.co hψ u' hu' f hf
  have hDfx : Df = heisD M B.ψ u' f := by
    funext x
    exact ((hDf _ (GlobalTheory.RealLift.eval_mem_adm x)).deriv).symm
  funext x
  have hl := hS.adm p _ (GlobalTheory.RealLift.eval_mem_adm x)
  have h1 := hDf _ hl
  have e : (fun t : ℝ => M.heisLine B.ψ u t (om p f) x) =
      fun t : ℝ => ((LinearMap.proj x : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ) ∘ₗ om p)
        (M.co.rho B.ψ (realAd F t • u') f) := by
    funext t
    rw [LinearMap.comp_apply, hS.impl p _ f hf, hact t]
    rfl
  show deriv (fun t : ℝ => M.heisLine B.ψ u t (om p f) x) 0 = _
  rw [e, h1.deriv, ← hDfx]
  rfl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergDerivArchimedeanWeilRepIntertwineStatement
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
open GlobalTheory.ArchDecay

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergDeriv_archimedean_weilRep_intertwine : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ (p : UA σ X.J × UA σ W.J) (u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), At (evI F) u → ∀ f ∈ schA F (Fin n × Fin d), heisD M B.ψ u (om p f) = om p (heisD M B.ψ (actAB (cA σ) p⁻¹ u) f) := by
  first | exact @GlobalTheory.ArchDecay.HeisWeil.heisD_weil | exact GlobalTheory.ArchDecay.HeisWeil.heisD_weil | (intros; apply GlobalTheory.ArchDecay.HeisWeil.heisD_weil <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordActionSquareIntegrableBound
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
open GlobalTheory.ArchDecay

theorem GlobalTheory.ArchDecay.word_action_square_integrable : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d), ∀ (μ : @Measure (Fin n × Fin d → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∀ p : ℕ, ∃ (C : ℝ) (k : ℕ), ∀ g h (w : List (Op F (Fin n × Fin d))), w.length ≤ p → (∀ o ∈ w, size F o ≤ 1) → ∫⁻ x, ‖word F w (om (g, h) Φ) x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal (C * ((ht g : ℝ) * ht h) ^ k) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP Φ hΦ μ hμ p
  have S := IsUWeilPair.isUSplitting hP.weil
  obtain ⟨T, hT⟩ := GlobalTheory.T.heisenbergDeriv_archimedeanLift_traceFormula F E σ n d X W M B.ψ hP.base.std
  obtain ⟨C3, k3, hsz⟩ := GlobalTheory.T.weilRep_moved_archimedean_coords_polynomial_height F E σ B n d X W M χX χW om r s r' s' hP
  set c : ℂ := -(2 * Real.pi * Complex.I) with hc
  have hcn : ‖c‖ = 2 * Real.pi := by
    rw [hc, norm_neg, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, mul_one]
    norm_num
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hcn
    linarith [Real.pi_pos]
  obtain ⟨C4, hwb⟩ := GlobalTheory.T.word_operator_L2_bound_polynomial F (Fin n × Fin d)
    (T : (Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] ((Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ))
    c Φ hΦ μ hμ p
  have hcl : ∀ ζ, ∀ f ∈ schA F (Fin n × Fin d), heisD M B.ψ (liftI M ζ) f ∈ schA F (Fin n × Fin d) := by
    intro ζ f hf
    rw [hT ζ f hf, dR]
    exact Submodule.add_mem _ (GlobalTheory.T.archimedeanDecayOperatorApply_mem_adelicSchwartz F _ (Sum.inl ζ.1) f hf)
      (Submodule.smul_mem _ c (GlobalTheory.T.archimedeanDecayOperatorApply_mem_adelicSchwartz F _ (Sum.inr _) f hf))
  have hHcl : ∀ zs f, f ∈ schA F (Fin n × Fin d) → wordH M B.ψ zs f ∈ schA F (Fin n × Fin d) := by
    intro zs f hf
    induction zs with
    | nil => exact hf
    | cons ζ zs ih => exact hcl ζ _ ih
  have hHR : ∀ zs f, f ∈ schA F (Fin n × Fin d) → wordH M B.ψ zs f =
      wordR F (T : (Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] ((Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ))
        c zs f := by
    intro zs f hf
    induction zs with
    | nil => rfl
    | cons ζ zs ih =>
      show heisD M B.ψ (liftI M ζ) (wordH M B.ψ zs f) = dR F _ c ζ (wordR F _ c zs f)
      rw [hT ζ _ (hHcl zs f hf), ih]
  let dirOf : Op F (Fin n × Fin d) →
      (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F) :=
    fun o => Sum.elim (fun v => (v, 0)) (fun l => (0, T.symm l)) o
  let cOf : Op F (Fin n × Fin d) → ℂ := fun o => Sum.elim (fun _ => 1) (fun _ => c⁻¹) o
  have hlet : ∀ o, ∀ f ∈ schA F (Fin n × Fin d), app F o f = cOf o • heisD M B.ψ (liftI M (dirOf o)) f := by
    intro o f hf
    rw [hT _ f hf]
    cases o with
    | inl v =>
      show dD F v f = (1 : ℂ) • (dD F v f + c • mM F ((T : (Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] ((Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ)) 0) f)
      rw [map_zero, mM_zero, smul_zero, add_zero, one_smul]
    | inr l =>
      show mM F l f = c⁻¹ • (dD F 0 f + c • mM F ((T : (Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] ((Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ)) (T.symm l)) f)
      rw [dD_zero, zero_add, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply, smul_smul,
        inv_mul_cancel₀ hc0, one_smul]
  set C0 : ℝ := max 1 ‖(T.symm : ((Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ) →L[ℝ]
    (Fin n × Fin d → mixedEmbedding.mixedSpace F))‖ with hC0
  have hC01 : 1 ≤ C0 := le_max_left _ _
  have hdir : ∀ o, ‖dirOf o‖ ≤ C0 * size F o := by
    intro o
    cases o with
    | inl v =>
      show ‖((v, 0) : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F))‖ ≤
        C0 * ‖v‖
      rw [Prod.norm_def, norm_zero, max_eq_left (norm_nonneg v)]
      exact le_mul_of_one_le_left (norm_nonneg v) hC01
    | inr l =>
      show ‖((0, T.symm l) : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F))‖ ≤
        C0 * ‖l‖
      rw [Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)]
      exact (ContinuousLinearMap.le_opNorm (T.symm : ((Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ) →L[ℝ]
        (Fin n × Fin d → mixedEmbedding.mixedSpace F)) l).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg l))
  have hcOf : ∀ o, ‖cOf o‖ ≤ 1 := by
    intro o
    cases o with
    | inl v => show ‖(1 : ℂ)‖ ≤ 1; rw [norm_one]
    | inr l =>
      show ‖c⁻¹‖ ≤ 1
      rw [norm_inv, hcn]
      exact inv_le_one_of_one_le₀ (by linarith [Real.pi_gt_three])
  refine ⟨max C4 0 * (max 1 (max C3 0 * C0)) ^ (2 * p), k3 * (2 * p), fun g h w hw hw1 => ?_⟩
  set H : ℝ := (ht g : ℝ) * ht h with hH
  have hH1 : 1 ≤ H := one_le_mul_of_one_le_of_one_le (by exact_mod_cast one_le_heightGL F g.1)
    (by exact_mod_cast one_le_heightGL F h.1)
  have hH0 : 0 ≤ H := zero_le_one.trans hH1
  have hΨs : om (g, h) Φ ∈ schA F (Fin n × Fin d) := S.pres _ _ hΦ
  have c1 : ∀ w : List (Op F (Fin n × Fin d)), ∃ a : ℂ, ‖a‖ ≤ 1 ∧
      word F w (om (g, h) Φ) = a • wordH M B.ψ (w.map dirOf) (om (g, h) Φ) := by
    intro w
    induction w with
    | nil => exact ⟨1, by rw [norm_one], by rw [one_smul]; rfl⟩
    | cons o w ih =>
      obtain ⟨a, ha, e⟩ := ih
      refine ⟨a * cOf o, ?_, ?_⟩
      · rw [norm_mul]; exact mul_le_one₀ ha (norm_nonneg _) (hcOf o)
      · rw [word_cons, e, app_smul, hlet o _ (hHcl _ _ hΨs), smul_smul]
        rfl
  have c2 : ∀ zs, wordH M B.ψ zs (om (g, h) Φ) = om (g, h) (wordH M B.ψ (zs.map (movI M (g, h))) Φ) := by
    intro zs
    induction zs with
    | nil => rfl
    | cons ζ zs ih =>
      obtain ⟨hA, hL⟩ := GlobalTheory.T.archimedeanCoords_moved_stay_supported_and_recovered F E σ n d X W M (g, h) ζ
      show heisD M B.ψ (liftI M ζ) (wordH M B.ψ zs (om (g, h) Φ)) =
        om (g, h) (heisD M B.ψ (liftI M (movI M (g, h) ζ)) (wordH M B.ψ (zs.map (movI M (g, h))) Φ))
      rw [ih, GlobalTheory.T.heisenbergDeriv_archimedean_weilRep_intertwine F E σ B n d X W M χX χW om r s r' s' hP (g, h) _ hA _ (hHcl _ _ hΦ), hL]
  obtain ⟨a, ha, e⟩ := c1 w
  have ha' : ‖a‖ₑ ≤ 1 := by
    rw [← ofReal_norm_eq_enorm]
    exact ENNReal.ofReal_le_one.2 ha
  set zs := (w.map dirOf).map (movI M (g, h)) with hzs
  have hG : wordH M B.ψ zs Φ ∈ schA F (Fin n × Fin d) := hHcl _ _ hΦ
  set ρ : ℝ := max 1 (max C3 0 * C0 * H ^ k3) with hρdef
  have hρ : ∀ ζ ∈ zs, ‖ζ‖ ≤ ρ := by
    intro ζ hζ
    obtain ⟨ζ', hζ', rfl⟩ := List.mem_map.1 hζ
    obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hζ'
    refine le_max_of_le_right ((hsz g h _).trans ?_)
    have hk : 0 ≤ H ^ k3 := pow_nonneg hH0 _
    calc C3 * H ^ k3 * ‖dirOf o‖ ≤ max C3 0 * H ^ k3 * (C0 * size F o) :=
          mul_le_mul (mul_le_mul_of_nonneg_right (le_max_left _ _) hk) (hdir o) (norm_nonneg _)
            (mul_nonneg (le_max_right _ _) hk)
      _ ≤ max C3 0 * H ^ k3 * (C0 * 1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hw1 o ho) (zero_le_one.trans hC01))
            (mul_nonneg (le_max_right _ _) hk)
      _ = max C3 0 * C0 * H ^ k3 := by ring
  have hlen : zs.length ≤ p := by rw [hzs, List.length_map, List.length_map]; exact hw
  have hb := hwb ρ (le_max_left _ _) zs hlen hρ
  rw [← hHR zs Φ hΦ] at hb
  have hk1 : 1 ≤ H ^ k3 := one_le_pow₀ hH1
  have hρle : ρ ≤ max 1 (max C3 0 * C0) * H ^ k3 :=
    max_le (one_le_mul_of_one_le_of_one_le (le_max_left _ _) hk1)
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (zero_le_one.trans hk1))
  have hρ0 : 0 ≤ ρ := zero_le_one.trans (le_max_left _ _)
  calc ∫⁻ x, ‖word F w (om (g, h) Φ) x‖ₑ ^ 2 ∂μ
      = ∫⁻ x, ‖a‖ₑ ^ 2 * ‖om (g, h) (wordH M B.ψ zs Φ) x‖ₑ ^ 2 ∂μ := by
        congr 1
        funext x
        rw [e, c2, Pi.smul_apply, smul_eq_mul, enorm_mul, mul_pow]
    _ ≤ ∫⁻ x, ‖om (g, h) (wordH M B.ψ zs Φ) x‖ₑ ^ 2 ∂μ :=
        lintegral_mono fun x => mul_le_of_le_one_left bot_le (pow_le_one₀ bot_le ha')
    _ = ∫⁻ x, ‖wordH M B.ψ zs Φ x‖ₑ ^ 2 ∂μ := S.unit μ hμ _ _ hG
    _ ≤ ENNReal.ofReal (C4 * ρ ^ (2 * p)) := hb
    _ ≤ ENNReal.ofReal (max C4 0 * max 1 (max C3 0 * C0) ^ (2 * p) * H ^ (k3 * (2 * p))) := by
        refine ENNReal.ofReal_le_ofReal ?_
        calc C4 * ρ ^ (2 * p) ≤ max C4 0 * ρ ^ (2 * p) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hρ0 _)
          _ ≤ max C4 0 * (max 1 (max C3 0 * C0) * H ^ k3) ^ (2 * p) :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρ0 hρle _) (le_max_right _ _)
          _ = _ := by rw [mul_pow, ← pow_mul]; ring
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordActionSquareIntegrableBoundStatement
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
open GlobalTheory.ArchDecay
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.word_action_square_integrable_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d), ∀ (μ : @Measure (Fin n × Fin d → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∀ p : ℕ, ∃ (C : ℝ) (k : ℕ), ∀ g h (w : List (Op F (Fin n × Fin d))), w.length ≤ p → (∀ o ∈ w, size F o ≤ 1) → ∫⁻ x, ‖word F w (om (g, h) Φ) x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal (C * ((ht g : ℝ) * ht h) ^ k) := by
  first | exact @GlobalTheory.ArchDecay.word_action_square_integrable | exact GlobalTheory.ArchDecay.word_action_square_integrable | (intros; apply GlobalTheory.ArchDecay.word_action_square_integrable <;> assumption)
end
