module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleTopology
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HyperbolicAndBlockOneNondegenerate

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StandardAdelicCharacter
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StandardAdelicCharacter
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.Core.StdChar

variable (F : Type) [Field F] [NumberField F]

def fieldChar (b : F) : ℂ :=
  Complex.exp (-(2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F b : ℚ) : ℂ))

lemma fieldChar_add (a b : F) : fieldChar F (a + b) = fieldChar F a * fieldChar F b := by
  simp only [fieldChar, map_add (f := _), Rat.cast_add, mul_add, Complex.exp_add]

lemma fieldChar_zero : fieldChar F 0 = 1 := by simp [fieldChar]

lemma norm_fieldChar (b : F) : ‖fieldChar F b‖ = 1 := by
  have : -(2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F b : ℚ) : ℂ) =
      ((-(2 * Real.pi * (Algebra.trace ℚ F b : ℚ)) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [fieldChar, this, Complex.norm_exp_ofReal_mul_I]

lemma trace_integer (r : 𝓞 F) : ∃ n : ℤ, Algebra.trace ℚ F (r : F) = n := by
  have h : IsIntegral ℤ (Algebra.trace ℚ F (r : F)) :=
    Algebra.isIntegral_trace (RingOfIntegers.isIntegral_coe r)
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp h
  exact ⟨n, by rw [← hn, eq_intCast]⟩

lemma fieldChar_eq_one_iff (b : F) :
    fieldChar F b = 1 ↔ ∃ n : ℤ, Algebra.trace ℚ F b = n := by
  rw [fieldChar, Complex.exp_eq_one_iff]
  have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨-n, ?_⟩
    have h3 : -((Algebra.trace ℚ F b : ℚ) : ℂ) = (n : ℂ) :=
      mul_right_cancel₀ h2 (by rw [← hn]; ring)
    have h4 : ((Algebra.trace ℚ F b : ℚ) : ℂ) = ((-n : ℤ) : ℂ) := by
      rw [Int.cast_neg, ← h3]
      ring
    exact_mod_cast h4
  · rintro ⟨n, hn⟩
    refine ⟨-n, ?_⟩
    rw [hn]
    push_cast
    ring

lemma zero_mem_Oh : (0 : A F) ∈ Oh F := by
  intro v
  exact (HeightOneSpectrum.adicCompletionIntegers F v).zero_mem

variable {F} in
lemma add_mem_Oh {x y : A F} (hx : x ∈ Oh F) (hy : y ∈ Oh F) : x + y ∈ Oh F := by
  intro v
  exact add_mem (hx v) (hy v)

variable {F} in
lemma sub_mem_Oh {x y : A F} (hx : x ∈ Oh F) (hy : y ∈ Oh F) : x - y ∈ Oh F := by
  intro v
  exact sub_mem (hx v) (hy v)

lemma exists_rep (x : A F) : ∃ b : F, x - algebraMap F (A F) b ∈ Oh F := by
  obtain ⟨-, -, -, -, hOpen, hDense, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  have hW : IsOpen {y : A F | x - y ∈ Oh F} := hOpen.preimage (continuous_const.sub continuous_id)
  obtain ⟨b, hb⟩ := hDense.exists_mem_open hW ⟨x, by simpa using zero_mem_Oh F⟩
  exact ⟨b, hb⟩

def charFun (x : A F) : ℂ := fieldChar F (Classical.choose (exists_rep F x))

lemma charFun_eq (x : A F) (b : F) (h : x - algebraMap F (A F) b ∈ Oh F) :
    charFun F x = fieldChar F b := by
  obtain ⟨-, -, -, -, -, -, hint, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  have hc := Classical.choose_spec (exists_rep F x)
  set c := Classical.choose (exists_rep F x) with hcdef
  have hbc : algebraMap F (A F) (b - c) ∈ Oh F := by
    have := sub_mem_Oh hc h
    convert this using 1
    rw [map_sub]
    abel
  obtain ⟨r, hr⟩ := (hint (b - c)).1 hbc
  have h1 : fieldChar F (b - c) = 1 := by
    rw [← hr]
    exact (fieldChar_eq_one_iff F _).2 (trace_integer F r)
  have hb : b = (b - c) + c := by ring
  rw [show charFun F x = fieldChar F c from rfl, hb, fieldChar_add, h1, one_mul]

def stdChar : AddChar (A F) ℂ where
  toFun := charFun F
  map_zero_eq_one' := by
    rw [charFun_eq F 0 0 (by simpa using zero_mem_Oh F), fieldChar_zero]
  map_add_eq_mul' x y := by
    obtain ⟨a, ha⟩ := exists_rep F x
    obtain ⟨b, hb⟩ := exists_rep F y
    have h : x + y - algebraMap F (A F) (a + b) ∈ Oh F := by
      have := add_mem_Oh ha hb
      rw [map_add (f := _)]
      convert this using 1
      ring
    rw [charFun_eq F _ _ h, charFun_eq F _ _ ha, charFun_eq F _ _ hb, fieldChar_add]

lemma stdChar_apply (x : A F) : stdChar F x = charFun F x := rfl

lemma continuous_stdChar : Continuous (stdChar F) := by
  obtain ⟨-, -, -, -, hOpen, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  refine continuous_iff_continuousAt.2 fun x => ?_
  obtain ⟨b, hb⟩ := exists_rep F x
  have hW : IsOpen {y : A F | y - x ∈ Oh F} := hOpen.preimage (continuous_id.sub continuous_const)
  have hxW : x ∈ {y : A F | y - x ∈ Oh F} := by simpa using zero_mem_Oh F
  have hev : ∀ᶠ y in 𝓝 x, stdChar F x = stdChar F y := by
    filter_upwards [hW.mem_nhds hxW] with y hy
    have hy' : y - algebraMap F (A F) b ∈ Oh F := by
      have := add_mem_Oh hy hb
      convert this using 1
      abel
    rw [stdChar_apply, stdChar_apply, charFun_eq F x b hb, charFun_eq F y b hy']
  exact (continuousAt_const : ContinuousAt (fun _ : A F => stdChar F x) x).congr hev

lemma Oh_subset_of_isClosed {S : Set (A F)} (hS : IsClosed S)
    (h : ∀ r : 𝓞 F, algebraMap F (A F) (r : F) ∈ S) : Oh F ⊆ S := by
  obtain ⟨-, -, -, -, hOpen, hDense, hint, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  intro x hx
  rw [← hS.closure_eq, mem_closure_iff]
  intro o ho hxo
  obtain ⟨b, hb⟩ := hDense.exists_mem_open (ho.inter hOpen) ⟨x, hxo, hx⟩
  obtain ⟨r, hr⟩ := (hint b).1 hb.2
  exact ⟨algebraMap F (A F) b, hb.1, hr ▸ h r⟩

theorem main : ∀ (F : Type) [Field F] [NumberField F], (∃ ψ : AddChar (A F) ℂ, IsStdChar F ψ) ∧ ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → (∀ x, ‖ψ x‖ = 1) ∧ (∀ x ∈ Oh F, ψ x = 1) ∧ ∀ b : F, (∀ x ∈ Oh F, ψ (algebraMap F (A F) b * x) = 1) ↔ ∀ r : 𝓞 F, ∃ n : ℤ, Algebra.trace ℚ F (b * (r : F)) = n := by
  intro F _ _
  obtain ⟨-, -, -, -, -, -, hint, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  have hψ1 : ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → ∀ x ∈ Oh F, ψ x = 1 := by
    intro ψ hψ x hx
    refine Oh_subset_of_isClosed F (S := {y | ψ y = 1}) (isClosed_eq hψ.1 continuous_const) (fun r => ?_) hx
    show ψ (algebraMap F (A F) (r : F)) = 1
    rw [hψ.2]
    exact (fieldChar_eq_one_iff F _).2 (trace_integer F r)
  refine ⟨⟨stdChar F, continuous_stdChar F, fun b => ?_⟩, fun ψ hψ => ⟨fun x => ?_, hψ1 ψ hψ, fun b => ⟨fun h r => ?_, fun h => ?_⟩⟩⟩
  · rw [stdChar_apply, charFun_eq F _ b (by simp [zero_mem_Oh F])]
    rfl
  · obtain ⟨b, hb⟩ := exists_rep F x
    have hx : x = algebraMap F (A F) b + (x - algebraMap F (A F) b) := by abel
    rw [hx, AddChar.map_add_eq_mul, hψ1 ψ hψ _ hb, mul_one, hψ.2]
    exact norm_fieldChar F b
  · have h1 := h (algebraMap F (A F) (r : F)) ((hint _).2 ⟨r, rfl⟩)
    rw [← map_mul, hψ.2] at h1
    exact (fieldChar_eq_one_iff F (b * (r : F))).1 h1
  · intro x hx
    refine Oh_subset_of_isClosed F (S := {y | ψ (algebraMap F (A F) b * y) = 1})
      (isClosed_eq (hψ.1.comp (continuous_const.mul continuous_id)) continuous_const) (fun r => ?_) hx
    show ψ (algebraMap F (A F) b * algebraMap F (A F) (r : F)) = 1
    rw [← map_mul, hψ.2]
    exact (fieldChar_eq_one_iff F _).2 (h r)

end GlobalTheory.CompanionTheory.SW.Core.StdChar
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StandardAdelicCharacterStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_adelic_character : ∀ (F : Type) [Field F] [NumberField F], (∃ ψ : AddChar (A F) ℂ, IsStdChar F ψ) ∧ ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → (∀ x, ‖ψ x‖ = 1) ∧ (∀ x ∈ Oh F, ψ x = 1) ∧ ∀ b : F, (∀ x ∈ Oh F, ψ (algebraMap F (A F) b * x) = 1) ↔ ∀ r : 𝓞 F, ∃ n : ℤ, Algebra.trace ℚ F (b * (r : F)) = n := by
  first | exact @GlobalTheory.CompanionTheory.SW.Core.StdChar.main | exact GlobalTheory.CompanionTheory.SW.Core.StdChar.main | (intros; apply GlobalTheory.CompanionTheory.SW.Core.StdChar.main <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaIntegralOverCoordinates
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaIntegralOverCoordinates
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.BB.PullCoord

theorem lintegral_thetaMeas_coord : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (S : Set (Fin M × Fin d → F)) (T : Set (Fin 1 → Fin M → E)), (∀ x, ofF b x ∈ T ↔ x ∈ S) → ∀ Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℝ≥0∞, Measurable Φ → ∫⁻ X, Φ X ∂(thetaMeas σ J μ 𝓕 T) = ∫⁻ ω, ∑' x : S, Φ (actW (AF F) σ J ω⁻¹ (ratTup (AF F) (ofF b x.1))) ∂(prH μ 𝓕) := by
  intro F E _ _ _ _ _ σ hσ M J hJ d b μ 𝓕 hμ h𝓕 S T hST Φ hΦ
  rw [GlobalTheory.T.siegel_mean_value_nonnegative F E σ hσ M J hJ μ 𝓕 hμ h𝓕 1 T Φ hΦ]
  have hb := RatCoord.ofF_bijective (M := M) b
  let e : S ≃ T := Equiv.ofBijective (fun x => ⟨ofF b x.1, (hST x.1).2 x.2⟩) (by
    constructor
    · intro x y hxy
      exact Subtype.ext (hb.1 (congrArg Subtype.val hxy))
    · intro y
      obtain ⟨x, hx⟩ := hb.2 y.1
      exact ⟨⟨x, (hST x).1 (hx ▸ y.2)⟩, Subtype.ext hx⟩)
  have hsum : ∀ h : HA (AF F) σ J,
      ∑' X : T, Φ (actW (AF F) σ J h⁻¹ (ratTup (AF F) (X : Fin 1 → Fin M → E)))
        = ∑' x : S, Φ (actW (AF F) σ J h⁻¹ (ratTup (AF F) (ofF b x.1))) := fun h =>
    (e.tsum_eq (fun X : T =>
      Φ (actW (AF F) σ J h⁻¹ (ratTup (AF F) (X : Fin 1 → Fin M → E))))).symm
  simp only [hsum, prH, lintegral_smul_measure, smul_eq_mul]

end GlobalTheory.CompanionTheory.SW.BB.PullCoord
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaIntegralOverCoordinatesStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_integral_over_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (S : Set (Fin M × Fin d → F)) (T : Set (Fin 1 → Fin M → E)), (∀ x, ofF b x ∈ T ↔ x ∈ S) → ∀ Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℝ≥0∞, Measurable Φ → ∫⁻ X, Φ X ∂(thetaMeas σ J μ 𝓕 T) = ∫⁻ ω, ∑' x : S, Φ (actW (AF F) σ J ω⁻¹ (ratTup (AF F) (ofF b x.1))) ∂(prH μ 𝓕) := by
  first | exact @GlobalTheory.CompanionTheory.SW.BB.PullCoord.lintegral_thetaMeas_coord | exact GlobalTheory.CompanionTheory.SW.BB.PullCoord.lintegral_thetaMeas_coord | (intros; apply GlobalTheory.CompanionTheory.SW.BB.PullCoord.lintegral_thetaMeas_coord <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ModulusCharacterUnitActionProduct
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ModulusCharacterUnitActionProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.FChi

theorem continuous_norm_tensor {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsTopologicalRing (R ⊗[F] E)] :
    Continuous (Algebra.norm R : R ⊗[F] E → R) := by
  classical
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  let B := Algebra.TensorProduct.basis R (Module.finBasis F E)
  have h : (fun y : R ⊗[F] E => Algebra.norm R y) = fun y => (Algebra.leftMulMatrix B y).det := by
    funext y; exact Algebra.norm_eq_matrix_det B y
  change Continuous (fun y : R ⊗[F] E => Algebra.norm R y)
  rw [h]
  refine Continuous.matrix_det ?_
  refine continuous_matrix fun i j => ?_
  let L : (R ⊗[F] E) →ₗ[R] R :=
    (Matrix.entryLinearMap R R i j) ∘ₗ (Algebra.leftMulMatrix B).toLinearMap
  exact IsModuleTopology.continuous_of_linearMap L

theorem norm_tmul_one {F E : Type} [Field F] [Field E] [Algebra F E]
    (h2 : Module.finrank F E = 2) (R : Type) [CommRing R] [Nontrivial R] [Algebra F R] (r : R) :
    Algebra.norm R (r ⊗ₜ[F] (1 : E)) = r ^ 2 := by
  classical
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  have e : r ⊗ₜ[F] (1 : E) = algebraMap R (R ⊗[F] E) r := by
    simp [Algebra.TensorProduct.algebraMap_apply]
  rw [e, Algebra.norm_algebraMap, Module.finrank_baseChange, h2]

theorem map_scale_adele {F : Type} [Field F] [NumberField F] (hF : IsTotallyReal F)
    (θ : ℝ →+* Ainf F) (hθ : Continuous θ) (μA : Measure (AF F)) (hA : μA.IsAddHaarMeasure)
    (t : ℝ) (ht : 0 < t) :
    μA.map (fun y => pairA F (θ t) 1 * y) =
      ENNReal.ofReal ((t ^ Module.finrank ℚ F)⁻¹) • μA := by
  obtain ⟨⟨lcA, scA, t2A⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  let μ' : Measure (Unit → AF F) := Measure.pi fun _ => μA
  haveI : μ'.IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have h := GlobalTheory.T.adelic_haar_scaling_by_real_idele F hF θ hθ Unit μ' t ht
  have he : μ'.map (MeasurableEquiv.funUnique Unit (AF F)) = μA :=
    (measurePreserving_funUnique μA Unit).map_eq
  have hf : Measurable (fun y : AF F => pairA F (θ t) 1 * y) :=
    (continuous_const.mul continuous_id).measurable
  have hg : Measurable (fun (x : Unit → AF F) (i : Unit) =>
      (show AdeleRing (𝓞 F) F from (θ t, 1)) * x i) :=
    Measurable.of_eval fun i =>
      (continuous_const.mul (continuous_apply i)).measurable
  have hc : (fun y : AF F => pairA F (θ t) 1 * y) ∘ (MeasurableEquiv.funUnique Unit (AF F)) =
      (MeasurableEquiv.funUnique Unit (AF F)) ∘ (fun (x : Unit → AF F) (i : Unit) =>
        (show AdeleRing (𝓞 F) F from (θ t, 1)) * x i) := rfl
  have hEquiv : AEMeasurable (MeasurableEquiv.funUnique Unit (AF F)) μ' :=
    (MeasurableEquiv.measurable _).aemeasurable
  calc μA.map (fun y => pairA F (θ t) 1 * y)
      = (μ'.map (MeasurableEquiv.funUnique Unit (AF F))).map (fun y => pairA F (θ t) 1 * y) := by
        rw [he]
    _ = (μ'.map (fun (x : Unit → AF F) (i : Unit) =>
          (show AdeleRing (𝓞 F) F from (θ t, 1)) * x i)).map
          (MeasurableEquiv.funUnique Unit (AF F)) := by
        rw [Measure.map_map hf (MeasurableEquiv.measurable _),
          Measure.map_map (MeasurableEquiv.measurable _) hg, hc]
    _ = ENNReal.ofReal ((t ^ Module.finrank ℚ F)⁻¹) • μA := by
        rw [h, Measure.map_smul _ hEquiv, he]
        simp

theorem exists_modulus_chi : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ τ : Multiplicative ℝ →* (AF F ⊗[F] E)ˣ, IsFlow τ →
    ∀ (M : ℕ) (μW : Measure (Fin 1 → Fin M → AF F ⊗[F] E)) (μA : Measure (AF F)),
    μW.IsAddHaarMeasure → μA.IsAddHaarMeasure →
    ∃ χ : (AF F ⊗[F] E)ˣ →* ℝ≥0, Continuous χ ∧
      (∀ a : (AF F ⊗[F] E)ˣ, (μW.prod μA).map (fun p =>
        (sigR (AF F) σ (a : AF F ⊗[F] E) • p.1, Algebra.norm (AF F) (a : AF F ⊗[F] E) * p.2)) =
          χ a • μW.prod μA) ∧
      ∀ x : ℝ, (χ (τ (Multiplicative.ofAdd x)) : ℝ) =
        Real.exp (-(2 * Module.finrank ℚ F * (M + 1) * x)) := by
  intro F E _ _ _ _ _ σ hCM τ hτ M μW μA hW hA
  obtain ⟨⟨lcA, scA, t2A⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  obtain ⟨trK, lcK, scK, t2K, cSig, -, -, bor, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (AF F)
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  haveI : BorelSpace (Fin 1 → Fin M → AF F ⊗[F] E) := bor 1 M
  have h2 : Module.finrank F E = 2 := hCM.2.2.1
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  have cN : Continuous (Algebra.norm (AF F) : AF F ⊗[F] E → AF F) := continuous_norm_tensor (AF F)
  let a : (AF F ⊗[F] E)ˣ →
      ((Fin 1 → Fin M → AF F ⊗[F] E) × AF F) →+ ((Fin 1 → Fin M → AF F ⊗[F] E) × AF F) := fun t =>
    { toFun := fun p => (sigR (AF F) σ (t : AF F ⊗[F] E) • p.1,
        Algebra.norm (AF F) (t : AF F ⊗[F] E) * p.2)
      map_zero' := by simp
      map_add' := by intro p q; simp [smul_add, mul_add] }
  have ha : ∀ t p, a t p = (sigR (AF F) σ (t : AF F ⊗[F] E) • p.1,
      Algebra.norm (AF F) (t : AF F ⊗[F] E) * p.2) := fun _ _ => rfl
  haveI : LocallyCompactSpace (AF F ⊗[F] E)ˣ :=
    (Units.isClosedEmbedding_embedProduct (α := AF F ⊗[F] E)).locallyCompactSpace
  haveI : SecondCountableTopology (AF F ⊗[F] E)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := AF F ⊗[F] E)).symm.secondCountableTopology
  haveI : SecondCountableTopology (AF F ⊗[F] E)ˣ :=
    (Units.isEmbedding_embedProduct (M := AF F ⊗[F] E)).secondCountableTopology
  have hcont : Continuous fun p : (AF F ⊗[F] E)ˣ × ((Fin 1 → Fin M → AF F ⊗[F] E) × AF F) =>
      a p.1 p.2 := by
    have hv : Continuous fun p : (AF F ⊗[F] E)ˣ × ((Fin 1 → Fin M → AF F ⊗[F] E) × AF F) =>
        ((p.1 : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) := Units.continuous_val.comp continuous_fst
    refine Continuous.prodMk ?_ ?_
    · exact (cSig.comp hv).smul (continuous_fst.comp continuous_snd)
    · exact (cN.comp hv).mul (continuous_snd.comp continuous_snd)
  haveI : μW.IsAddHaarMeasure := hW
  haveI : μA.IsAddHaarMeasure := hA
  haveI : IsTopologicalAddGroup (Fin 1 → Fin M → AF F ⊗[F] E) := inferInstance
  haveI : LocallyCompactSpace (Fin 1 → Fin M → AF F ⊗[F] E) := inferInstance
  haveI : SecondCountableTopology (Fin 1 → Fin M → AF F ⊗[F] E) := inferInstance
  haveI : SigmaFinite μW := inferInstance
  haveI : SigmaFinite μA := inferInstance
  haveI : (μW.prod μA).IsAddHaarMeasure := inferInstance
  obtain ⟨χ, hχc, hχ⟩ := GlobalTheory.T.group_action_haar_scaling_continuous ((Fin 1 → Fin M → AF F ⊗[F] E) × AF F) (μW.prod μA)
    (AF F ⊗[F] E)ˣ a hcont continuous_inv
    (by intro y; rw [ha]; simp)
    (by intro s t y; simp only [ha, Units.val_mul, map_mul, smul_smul, mul_assoc])
  refine ⟨χ, hχc, hχ, ?_⟩
  intro x
  have hτ' := hτ
  obtain ⟨-, θ, hθ, hval⟩ := hτ
  have hu := hval x
  have hsig : sigR (AF F) σ ((τ (Multiplicative.ofAdd x) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) =
      ((τ (Multiplicative.ofAdd x) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) := by
    rw [hu]; simp [sigR]
  haveI : Nontrivial (Ainf F) := by
    obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
    unfold Ainf InfiniteAdeleRing
    exact Pi.nontrivial_at v
  haveI : Nontrivial (AF F) := inferInstanceAs (Nontrivial (Ainf F × Af F))
  have hnorm : Algebra.norm (AF F) ((τ (Multiplicative.ofAdd x) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) =
      pairA F (θ (Real.exp (2 * x))) 1 := by
    rw [hu, norm_tmul_one h2, sq]
    have e2 : Real.exp (2 * x) = Real.exp x * Real.exp x := by
      rw [← Real.exp_add]; congr 1; ring
    rw [e2, map_mul]
    change ((θ (Real.exp x) * θ (Real.exp x), (1 : Af F) * 1) : Ainf F × Af F) = (_, 1)
    rw [one_mul]
  have hWm := GlobalTheory.T.haar_scaling_under_flow F E σ hCM τ hτ' 1 M μW hW x
  have hAm := map_scale_adele hCM.1 θ hθ μA hA (Real.exp (2 * x)) (Real.exp_pos _)
  have mW : Measurable (fun X : Fin 1 → Fin M → AF F ⊗[F] E =>
      ((τ (Multiplicative.ofAdd x) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • X) :=
    (continuous_const_smul _).measurable
  have mA : Measurable (fun y : AF F => pairA F (θ (Real.exp (2 * x))) 1 * y) :=
    (continuous_const.mul continuous_id).measurable
  have hmap := Measure.map_prod_map μW μA mW mA
  rw [hWm, hAm, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul] at hmap
  have hfun : (a (τ (Multiplicative.ofAdd x)) : _ → _) = Prod.map
      (fun X : Fin 1 → Fin M → AF F ⊗[F] E =>
        ((τ (Multiplicative.ofAdd x) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • X)
      (fun y : AF F => pairA F (θ (Real.exp (2 * x))) 1 * y) := by
    funext p
    rw [ha, hsig, hnorm]
    rfl
  have hfin := hχ (τ (Multiplicative.ofAdd x))
  rw [hfun, ← hmap] at hfin
  obtain ⟨S, hS, hS0⟩ := exists_compact_mem_nhds (0 : (Fin 1 → Fin M → AF F ⊗[F] E) × AF F)
  have pos : (μW.prod μA) S ≠ 0 := (Measure.measure_pos_of_mem_nhds _ hS0).ne'
  have fin : (μW.prod μA) S ≠ ⊤ := hS.measure_lt_top.ne
  have hS1 := congrArg (fun m : Measure _ => m S) hfin
  simp only [Measure.smul_apply, smul_eq_mul, ENNReal.smul_def] at hS1
  have hS2 := (ENNReal.mul_left_inj pos fin).1 hS1
  have hS3 := congrArg ENNReal.toReal hS2
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le,
    ENNReal.toReal_ofReal (by positivity), ENNReal.coe_toReal] at hS3
  rw [← hS3, ← Real.exp_nat_mul, ← Real.exp_neg, ← Real.exp_add]
  congr 1
  push_cast
  ring

end GlobalTheory.CompanionTheory.SW.FChi
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ModulusCharacterUnitActionProductStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modulus_character_unit_action_product : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ τ : Multiplicative ℝ →* (AF F ⊗[F] E)ˣ, IsFlow τ → ∀ (M : ℕ) (μW : Measure (Fin 1 → Fin M → AF F ⊗[F] E)) (μA : Measure (AF F)), μW.IsAddHaarMeasure → μA.IsAddHaarMeasure → ∃ χ : (AF F ⊗[F] E)ˣ →* ℝ≥0, Continuous χ ∧ (∀ a : (AF F ⊗[F] E)ˣ, (μW.prod μA).map (fun p => (sigR (AF F) σ (a : AF F ⊗[F] E) • p.1, Algebra.norm (AF F) (a : AF F ⊗[F] E) * p.2)) = χ a • μW.prod μA) ∧ ∀ x : ℝ, (χ (τ (Multiplicative.ofAdd x)) : ℝ) = Real.exp (-(2 * Module.finrank ℚ F * (M + 1) * x)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.FChi.exists_modulus_chi | exact GlobalTheory.CompanionTheory.SW.FChi.exists_modulus_chi | (intros; apply GlobalTheory.CompanionTheory.SW.FChi.exists_modulus_chi <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicLevelLatticeCompactOpen
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicLevelLatticeCompactOpen
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.ThW.Lco

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker

theorem latN_coe_eq_pi (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι]
    (N : ℕ) : (latN F ι N : Set (ι → A F)) =
      Set.pi Set.univ (fun _ => {x : A F | ∃ y ∈ Oh F, x = (N : A F) * y}) := by
  ext x
  exact ⟨fun h i _ => h i, fun h i => h i (Set.mem_univ i)⟩

theorem isCompact_mul_oh (F : Type) [Field F] [NumberField F] (N : ℕ) :
    IsCompact {x : A F | ∃ y ∈ Oh F, x = (N : A F) * y} := by
  have hOh : IsCompact (Oh F) := (GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F).2.2.2.1
  have heq : {x : A F | ∃ y ∈ Oh F, x = (N : A F) * y} = (fun y => (N : A F) * y) '' Oh F := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
  rw [heq]
  exact hOh.image (continuous_const.mul continuous_id)

theorem main : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ),
    0 < N → IsCompact (latN F ι N : Set (ι → A F)) ∧ IsOpen (latN F ι N : Set (ι → A F)) ∧
      ∀ a : ι → F, SB (indC N a) := by
  intro F _ _ ι _ _ N hN
  obtain ⟨-, -, hT2, -, -, -, -, -, -, hOpen⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  have hC : IsCompact (latN F ι N : Set (ι → A F)) := by
    rw [latN_coe_eq_pi]
    exact isCompact_univ_pi fun _ => isCompact_mul_oh F N
  have hO : IsOpen (latN F ι N : Set (ι → A F)) := by
    rw [latN_coe_eq_pi]
    exact isOpen_set_pi Set.finite_univ fun _ _ => hOpen N hN
  refine ⟨hC, hO, fun a => ?_⟩
  have hclopen : IsClopen (latN F ι N : Set (ι → A F)) := ⟨hC.isClosed, hO⟩
  have hcont : Continuous fun x : ι → A F => x - toA a := continuous_id.sub continuous_const
  have hS : IsClopen {x : ι → A F | x - toA a ∈ latN F ι N} := hclopen.preimage hcont
  have hK : IsCompact {x : ι → A F | x - toA a ∈ latN F ι N} := by
    have h : {x : ι → A F | x - toA a ∈ latN F ι N} =
        (fun x => x + toA a) '' (latN F ι N : Set (ι → A F)) := by
      ext x
      constructor
      · intro hx
        exact ⟨x - toA a, hx, by simp⟩
      · rintro ⟨y, hy, rfl⟩
        simpa using hy
    rw [h]
    exact hC.image (continuous_id.add continuous_const)
  refine ⟨?_, HasCompactSupport.of_support_subset_isCompact hK Set.support_indicator_subset⟩
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ {x : ι → A F | x - toA a ∈ latN F ι N}
  · filter_upwards [hS.isOpen.mem_nhds hx] with y hy
    have hy' : y ∈ {x : ι → A F | x - toA a ∈ latN F ι N} := hy
    rw [indC, Set.indicator_of_mem hx, Set.indicator_of_mem hy']
  · filter_upwards [hS.compl.isOpen.mem_nhds hx] with y hy
    have hy' : y ∉ {x : ι → A F | x - toA a ∈ latN F ι N} := hy
    rw [indC, Set.indicator_of_notMem hx, Set.indicator_of_notMem hy']

end GlobalTheory.CompanionTheory.SW.ThW.Lco
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicLevelLatticeCompactOpenStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_level_lattice_compact_open : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ), 0 < N → IsCompact (latN F ι N : Set (ι → A F)) ∧ IsOpen (latN F ι N : Set (ι → A F)) ∧ ∀ a : ι → F, SB (indC N a) := by
  first | exact @GlobalTheory.CompanionTheory.SW.ThW.Lco.main | exact GlobalTheory.CompanionTheory.SW.ThW.Lco.main | (intros; apply GlobalTheory.CompanionTheory.SW.ThW.Lco.main <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LatticeCosetParametrization
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LatticeCosetParametrization
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.ThW

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups Kronecker

theorem rational_coset_param : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι]
    [DecidableEq ι] [DecidableEq (InfinitePlace F)] (ρ : InfinitePlace F → (F →+* ℝ))
    (b : Module.Basis (InfinitePlace F) ℤ (𝓞 F)) (a : ι → F) (N : ℕ), 0 < N →
    ∃ e : (ι × InfinitePlace F → ℤ) → ι → F, Function.Injective e ∧
      (∀ x : ι → F, toA x - toA a ∈ latN F ι N ↔ x ∈ Set.range e) ∧
      ∀ n, emb ρ (e n) = emb ρ a + gM ρ (fun v => b v) N *ᵥ fun p => (n p : ℝ) := by
  intro F _ _ ι _ _ _ ρ b a N hN
  have hOh := (GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F).2.2.2.2.2.2.1
  have hN0 : (N : F) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hNu : IsUnit ((N : GlobalTheory.CompanionTheory.SW.Core.A F)) := by
    rw [← map_natCast (algebraMap F (GlobalTheory.CompanionTheory.SW.Core.A F))]
    exact (isUnit_iff_ne_zero.mpr hN0).map _
  have hcoe : ∀ c : InfinitePlace F → ℤ,
      ((b.equivFun.symm c : 𝓞 F) : F) = ∑ v, (c v : F) * (b v : F) := by
    intro c
    rw [Module.Basis.equivFun_symm_apply]
    simp [zsmul_eq_mul]
  refine ⟨fun n i => a i + (N : F) * ∑ v, (n (i, v) : F) * (b v : F), ?_, ?_, ?_⟩
  · intro n m h
    funext p
    obtain ⟨i, v⟩ := p
    have hi := congrFun h i
    simp only [add_right_inj] at hi
    have hi' := mul_left_cancel₀ hN0 hi
    have hO : b.equivFun.symm (fun v => n (i, v)) = b.equivFun.symm (fun v => m (i, v)) := by
      apply RingOfIntegers.ext
      rw [hcoe, hcoe]
      exact hi'
    exact congrFun (b.equivFun.symm.injective hO) v
  · intro x
    constructor
    · intro hx
      have hx' : ∀ i, ∃ y ∈ GlobalTheory.CompanionTheory.SW.Core.Oh F, (toA x - toA a) i = (N : GlobalTheory.CompanionTheory.SW.Core.A F) * y := hx
      have hr : ∀ i, ∃ r : 𝓞 F, (r : F) = (x i - a i) / N := by
        intro i
        obtain ⟨y, hy, hxy⟩ := hx' i
        have hy' : y = algebraMap F (GlobalTheory.CompanionTheory.SW.Core.A F) ((x i - a i) / N) := by
          apply hNu.mul_left_cancel
          rw [← hxy, ← map_natCast (algebraMap F (GlobalTheory.CompanionTheory.SW.Core.A F)), ← map_mul,
            mul_div_cancel₀ _ hN0, map_sub]
          rfl
        exact (hOh _).mp (hy' ▸ hy)
      choose r hr using hr
      refine ⟨fun p => b.equivFun (r p.1) p.2, ?_⟩
      funext i
      show a i + (N : F) * ∑ v, ((b.equivFun (r i) v : ℤ) : F) * (b v : F) = x i
      rw [← hcoe, LinearEquiv.symm_apply_apply, hr i]
      field_simp
      ring
    · rintro ⟨n, rfl⟩
      intro i
      refine ⟨algebraMap F (GlobalTheory.CompanionTheory.SW.Core.A F) (∑ v, (n (i, v) : F) * (b v : F)),
        (hOh _).mpr ⟨b.equivFun.symm (fun v => n (i, v)), hcoe _⟩, ?_⟩
      show algebraMap F (GlobalTheory.CompanionTheory.SW.Core.A F) (a i + (N : F) * ∑ v, (n (i, v) : F) * (b v : F)) -
          algebraMap F (GlobalTheory.CompanionTheory.SW.Core.A F) (a i) = _
      rw [map_add (f := _), map_mul, map_natCast]
      ring
  · intro n
    funext p
    obtain ⟨i, w⟩ := p
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [emb, gM, EM, Matrix.mulVec, dotProduct, Matrix.smul_apply, Matrix.kroneckerMap_apply,
      Matrix.one_apply, Pi.add_apply, map_add, map_mul, map_sum, map_natCast, map_intCast,
      Fintype.sum_prod_type, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      nsmul_eq_mul, Finset.mul_sum]
    congr 1
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [if_pos rfl]
    ring

end GlobalTheory.CompanionTheory.SW.ThW
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LatticeCosetParametrizationStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_coset_parametrization : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι] [DecidableEq (InfinitePlace F)] (ρ : InfinitePlace F → (F →+* ℝ)) (b : Module.Basis (InfinitePlace F) ℤ (𝓞 F)) (a : ι → F) (N : ℕ), 0 < N → ∃ e : (ι × InfinitePlace F → ℤ) → ι → F, Function.Injective e ∧ (∀ x : ι → F, toA x - toA a ∈ latN F ι N ↔ x ∈ Set.range e) ∧ ∀ n, emb ρ (e n) = emb ρ a + gM ρ (fun v => b v) N *ᵥ fun p => (n p : ℝ) := by
  first | exact @GlobalTheory.CompanionTheory.SW.ThW.rational_coset_param | exact GlobalTheory.CompanionTheory.SW.ThW.rational_coset_param | (intros; apply GlobalTheory.CompanionTheory.SW.ThW.rational_coset_param <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SchwartzBruhatSpanIndicators
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SbEqSumCosetIndicators
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

namespace GlobalTheory.CompanionTheory.SW.Span

theorem sb_eq_sum_coset_indicators :
    ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] (χ : V → V → ℂ)
      (μ : Measure V), NADual V χ μ → ∀ φ : V → ℂ, SB φ → ∀ L' : AddSubgroup V,
      IsOpen (L' : Set V) → (∀ x, ∀ l ∈ L', φ (x + l) = φ x) →
      ∃ s : Finset V, ∀ x, φ x = ∑ a ∈ s, φ a * Set.indicator {y | y - a ∈ L'} (fun _ => (1 : ℂ)) x := by
  intro V _ _ _ χ μ h φ hφ L' hL' hinv
  classical
  haveI : IsTopologicalAddGroup V := h.1
  obtain ⟨t, ht⟩ := hφ.2.isCompact.elim_finite_subcover (fun a : V => {y | y - a ∈ L'})
    (fun a => hL'.preimage (continuous_id.sub continuous_const))
    (fun x _ => Set.mem_iUnion.2 ⟨x, by simp [L'.zero_mem]⟩)
  let T : Finset (V ⧸ L') := t.image (QuotientAddGroup.mk : V → V ⧸ L')
  refine ⟨T.image Quotient.out, fun x => ?_⟩
  rw [Finset.sum_image (fun a _ b _ hab => Quotient.out_injective hab)]
  have key : ∀ q : V ⧸ L', x - q.out ∈ L' ↔ q = (x : V ⧸ L') := by
    intro q
    conv_rhs => rw [← QuotientAddGroup.out_eq' q]
    rw [QuotientAddGroup.eq, neg_add_eq_sub]
  have hval : φ ((x : V ⧸ L').out) = φ x := by
    have hm : x - ((x : V ⧸ L')).out ∈ L' := (key _).2 rfl
    have := hinv ((x : V ⧸ L')).out _ hm
    rw [← this]
    congr 1
    abel
  have hterm : ∀ q : V ⧸ L', φ q.out * Set.indicator {y | y - q.out ∈ L'} (fun _ => (1 : ℂ)) x
      = if q = (x : V ⧸ L') then φ x else 0 := by
    intro q
    by_cases hq : q = (x : V ⧸ L')
    · subst hq
      rw [if_pos rfl, Set.indicator_of_mem (show x ∈ {y | y - ((x : V ⧸ L')).out ∈ L'} from (key _).2 rfl),
        hval, mul_one]
    · rw [if_neg hq, Set.indicator_of_notMem (show x ∉ {y | y - q.out ∈ L'} from fun hx => hq ((key _).1 hx)),
        mul_zero]
  simp only [hterm, Finset.sum_ite_eq']
  split_ifs with hx
  · rfl
  · by_contra hne
    have hmem : x ∈ tsupport φ := subset_tsupport φ hne
    obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.1 (ht hmem)
    apply hx
    refine Finset.mem_image.2 ⟨a, ha, ?_⟩
    rw [QuotientAddGroup.eq, neg_add_eq_sub]
    exact hxa

end GlobalTheory.CompanionTheory.SW.Span
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompactSubgroupAndLevel
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

namespace GlobalTheory.CompanionTheory.SW.Core

theorem compact_open_sup {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    {L₁ L₂ : AddSubgroup V} (h₁ : IsCompact (L₁ : Set V)) (o₁ : IsOpen (L₁ : Set V))
    (h₂ : IsCompact (L₂ : Set V)) :
    IsCompact ((L₁ ⊔ L₂ : AddSubgroup V) : Set V) ∧ IsOpen ((L₁ ⊔ L₂ : AddSubgroup V) : Set V) := by
  refine ⟨?_, AddSubgroup.isOpen_mono le_sup_left o₁⟩
  rw [AddSubgroup.add_normal]
  exact h₁.add h₂

theorem compact_subgroup_and_level :
    ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] (χ : V → V → ℂ) (μ : Measure V), NADual V χ μ → (∀ K : Set V, IsCompact K → ∃ L : AddSubgroup V, IsCompact (L : Set V) ∧ IsOpen (L : Set V) ∧ K ⊆ L) ∧ ∀ φ : V → ℂ, SB φ → ∃ L L' : AddSubgroup V, IsCompact (L : Set V) ∧ IsOpen (L : Set V) ∧ IsCompact (L' : Set V) ∧ IsOpen (L' : Set V) ∧ L' ≤ L ∧ (∀ x, x ∉ L → φ x = 0) ∧ ∀ x, ∀ l ∈ L', φ (x + l) = φ x := by
  intro V _ _ _ χ μ h
  obtain ⟨hG, hT, -, -, -, -, hnb, hcov, -⟩ := h
  haveI := hG
  haveI := hT
  have cover : ∀ K : Set V, IsCompact K →
      ∃ L : AddSubgroup V, IsCompact (L : Set V) ∧ IsOpen (L : Set V) ∧ K ⊆ L := by
    intro K hK
    refine hK.induction_on (p := fun s => ∃ L : AddSubgroup V, IsCompact (L : Set V) ∧
      IsOpen (L : Set V) ∧ s ⊆ L) ?_ ?_ ?_ ?_
    · obtain ⟨L, c, o, -⟩ := hcov 0
      exact ⟨L, c, o, Set.empty_subset _⟩
    · rintro s t hst ⟨L, c, o, hL⟩
      exact ⟨L, c, o, hst.trans hL⟩
    · rintro s t ⟨L₁, c₁, o₁, h₁⟩ ⟨L₂, c₂, o₂, h₂⟩
      obtain ⟨c, o⟩ := compact_open_sup c₁ o₁ c₂
      refine ⟨L₁ ⊔ L₂, c, o, Set.union_subset ?_ ?_⟩
      · exact h₁.trans (SetLike.coe_subset_coe.2 le_sup_left)
      · exact h₂.trans (SetLike.coe_subset_coe.2 le_sup_right)
    · intro x _
      obtain ⟨L, c, o, hx⟩ := hcov x
      exact ⟨L, mem_nhdsWithin_of_mem_nhds (o.mem_nhds hx), L, c, o, subset_rfl⟩
  refine ⟨cover, ?_⟩
  rintro φ ⟨hlc, hcs⟩
  obtain ⟨L, c, o, hL⟩ := cover _ hcs
  have hzero : ∀ x, x ∉ L → φ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun hm => hx (hL hm))
  have hg : IsLocallyConstant (fun p : V × V => (φ (p.1 + p.2), φ p.1)) :=
    (hlc.comp_continuous continuous_add).prodMk (hlc.comp_continuous continuous_fst)
  have hW : IsOpen {p : V × V | φ (p.1 + p.2) = φ p.1} := hg {q : ℂ × ℂ | q.1 = q.2}
  have hsub : (L : Set V) ×ˢ ({0} : Set V) ⊆ {p : V × V | φ (p.1 + p.2) = φ p.1} := by
    rintro ⟨x, y⟩ ⟨-, hy⟩
    have hy' : y = 0 := hy
    simp [hy']
  obtain ⟨u, v, -, ov, hu, hv, huv⟩ := generalized_tube_lemma c isCompact_singleton hW hsub
  obtain ⟨L₀, c₀, o₀, h₀⟩ := hnb v (ov.mem_nhds (hv rfl))
  refine ⟨L, L₀ ⊓ L, c, o, ?_, ?_, inf_le_right, hzero, ?_⟩
  · have := c₀.inter_right c.isClosed
    simpa using this
  · simpa using o₀.inter o
  · intro x l hl
    have hl₀ : l ∈ L₀ := hl.1
    have hlL : l ∈ L := hl.2
    by_cases hx : x ∈ L
    · exact huv (Set.mk_mem_prod (hu hx) (h₀ hl₀))
    · rw [hzero x hx, hzero _ (fun hm => hx ?_)]
      simpa using L.sub_mem hm hlL

end GlobalTheory.CompanionTheory.SW.Core
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SchwartzBruhatSpanIndicators
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker

namespace GlobalTheory.CompanionTheory.SW.ThW

theorem sb_eq_sum_rational_coset_indicators :
    ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)] [BorelSpace (A F)] (ι : Type)
      [Fintype ι] [DecidableEq ι] (χ : (ι → A F) → (ι → A F) → ℂ) (μ : Measure (ι → A F)),
      NADual (ι → A F) χ μ → (∀ N : ℕ, 0 < N → IsOpen (latN F ι N : Set (ι → A F))) →
      ∀ φ : (ι → A F) → ℂ, SB φ →
        ∃ N : ℕ, 0 < N ∧ ∃ (s : Finset (ι → F)) (c : (ι → F) → ℂ),
          φ = ∑ a ∈ s, c a • indC N a := by
  intro F _ _ _ _ ι _ _ χ μ h hopen φ hφ
  classical
  obtain ⟨-, -, -, -, -, hdense, -, hU, -, hNopen⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  obtain ⟨-, hlev⟩ := GlobalTheory.CompanionTheory.SW.Core.compact_subgroup_and_level (ι → A F) χ μ h
  obtain ⟨L, L', -, -, -, oL', -, -, hinv⟩ := hlev φ hφ

  have h0 : (L' : Set (ι → A F)) ∈ 𝓝 (0 : ι → A F) := oL'.mem_nhds L'.zero_mem
  rw [nhds_pi, Filter.mem_pi] at h0
  obtain ⟨I, -, t, ht, hsub⟩ := h0
  have hU0 : (⋂ i, t i) ∈ 𝓝 (0 : A F) := Filter.iInter_mem.2 ht
  obtain ⟨N, hN, hNU⟩ := hU _ hU0
  have hle : latN F ι N ≤ L' := by
    intro x hx
    apply hsub
    intro i _
    obtain ⟨y, hy, e⟩ := hx i
    rw [e]
    exact Set.mem_iInter.1 (hNU y hy) i

  have happ : ∀ (a : ι → A F) (i : ι), ∃ b : F,
      ∃ y ∈ Oh F, a i - algebraMap F (A F) b = (N : A F) * y := by
    intro a i
    have ho : IsOpen {b : A F | ∃ y ∈ Oh F, a i - b = (N : A F) * y} :=
      (hNopen N hN).preimage (continuous_const.sub continuous_id)
    have hne : {b : A F | ∃ y ∈ Oh F, a i - b = (N : A F) * y}.Nonempty :=
      ⟨a i, 0, fun _ => zero_mem _, by simp⟩
    obtain ⟨b, hb⟩ := hdense.exists_mem_open ho hne
    exact ⟨b, hb⟩
  choose r hr using happ
  have hrl : ∀ a : ι → A F, a - toA (r a) ∈ latN F ι N := fun a i => hr a i
  obtain ⟨s, hs⟩ := GlobalTheory.CompanionTheory.SW.Span.sb_eq_sum_coset_indicators (ι → A F) χ μ h φ hφ (latN F ι N)
    (hopen N hN) (fun x l hl => hinv x l (hle hl))
  have hind : ∀ (a x : ι → A F),
      Set.indicator {y | y - a ∈ latN F ι N} (fun _ => (1 : ℂ)) x = indC N (r a) x := by
    intro a x
    have hset : {y | y - a ∈ latN F ι N} = {y | y - toA (r a) ∈ latN F ι N} := by
      ext y
      have e : y - toA (r a) = (y - a) + (a - toA (r a)) := by abel
      simp only [Set.mem_setOf_eq]
      rw [e]
      exact (AddSubgroup.add_mem_cancel_right _ (hrl a)).symm
    rw [hset]
    rfl
  refine ⟨N, hN, s.image r, fun b => ∑ a ∈ s with r a = b, φ a, ?_⟩
  funext x
  rw [hs x, Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, hind, Finset.sum_mul]
  rw [← Finset.sum_fiberwise_of_maps_to (s := s) (t := s.image r) (g := r)
    (fun a ha => Finset.mem_image_of_mem r ha)]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a ha => ?_
  rw [(Finset.mem_filter.1 ha).2]

end GlobalTheory.CompanionTheory.SW.ThW
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SchwartzBruhatSpanIndicatorsStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_bruhat_span_indicators : ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)] [BorelSpace (A F)] (ι : Type) [Fintype ι] [DecidableEq ι] (χ : (ι → A F) → (ι → A F) → ℂ) (μ : Measure (ι → A F)), NADual (ι → A F) χ μ → (∀ N : ℕ, 0 < N → IsOpen (latN F ι N : Set (ι → A F))) → ∀ φ : (ι → A F) → ℂ, SB φ → ∃ N : ℕ, 0 < N ∧ ∃ (s : Finset (ι → F)) (c : (ι → F) → ℂ), φ = ∑ a ∈ s, c a • indC N a := by
  first | exact @GlobalTheory.CompanionTheory.SW.ThW.sb_eq_sum_rational_coset_indicators | exact GlobalTheory.CompanionTheory.SW.ThW.sb_eq_sum_rational_coset_indicators | (intros; apply GlobalTheory.CompanionTheory.SW.ThW.sb_eq_sum_rational_coset_indicators <;> assumption)
end
end
