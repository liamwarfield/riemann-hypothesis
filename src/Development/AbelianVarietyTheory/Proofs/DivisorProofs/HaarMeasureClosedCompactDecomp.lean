module

public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralConjInnerMulInnerOfIsEmptyEquiv
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOfLocallyFiniteFreeLocalizations
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenConnectedComponentOfIsLocallyNoetherian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleCosetSumFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzSeminormTranslateSubLineDerivLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FgIntOfForallIsIntegral
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.MulConjTransposeEqOneOfOrthonormal
public import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzContinuousAtOfPointwiseOfBounded
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrimeIdealsCountingBounds

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarMeasureClosedCompactDecomp
open MeasureTheory MeasureTheory.Measure Topology Pointwise
open scoped ENNReal NNReal

namespace GlobalTheory.HaarQK

theorem lintegral_mul_right_modular {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [T2Space H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (ν : Measure H) [ν.IsHaarMeasure] {f : H → ℝ≥0∞} (hf : Measurable f) (h : H) :
    ∫⁻ x, f (x * h) ∂ν = (modularCharacterFun h : ℝ≥0∞) * ∫⁻ x, f x ∂ν := by
  rw [← lintegral_map hf (measurable_mul_const h), map_right_mul_eq_modularCharacterFun_smul,
    lintegral_smul_measure]
  rfl

theorem secondCountable_subgroup {G : Type} [Group G] [TopologicalSpace G]
    [SecondCountableTopology G] (Q : Subgroup G) : SecondCountableTopology Q :=
  TopologicalSpace.Subtype.secondCountableTopology (Q : Set G)

attribute [local instance] secondCountable_subgroup

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  {Q K : Subgroup G} [LocallyCompactSpace Q] [CompactSpace K]
  (ν : Measure Q) (κ : Measure K) [ν.IsHaarMeasure] [κ.IsHaarMeasure]

theorem iter_right (u : G → ℝ≥0∞) (hu : Measurable u) (q₀ : Q) (k₀ : K) :
    ∫⁻ k, ∫⁻ q, u (q.1 * (q₀.1 * k₀.1) * k.1) ∂ν ∂κ =
      (modularCharacterFun q₀ : ℝ≥0∞) * ∫⁻ k, ∫⁻ q, u (q.1 * k.1) ∂ν ∂κ := by
  have e1 : ∀ k : K, ∫⁻ q, u (q.1 * (q₀.1 * k₀.1) * k.1) ∂ν =
      (modularCharacterFun q₀ : ℝ≥0∞) * ∫⁻ q, u (q.1 * (k₀ * k).1) ∂ν := by
    intro k
    have hf : Measurable fun q : Q => u (q.1 * (k₀ * k).1) :=
      hu.comp ((continuous_subtype_val.mul continuous_const).measurable)
    rw [← lintegral_mul_right_modular ν hf q₀]
    congr 1
    ext q
    congr 1
    simp only [Subgroup.coe_mul]
    group
  simp_rw [e1]
  rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  congr 1
  exact lintegral_mul_left_eq_self (fun k : K => ∫⁻ q, u (q.1 * k.1) ∂ν) k₀

theorem iter_left (v : G → ℝ≥0∞) (q₀ : Q) (k₀ : K) :
    ∫⁻ k, ∫⁻ q, v ((q.1)⁻¹ * (q₀.1 * k₀.1) * (k.1)⁻¹) ∂ν ∂κ =
      ∫⁻ k, ∫⁻ q, v ((q.1)⁻¹ * k.1) ∂ν ∂κ := by
  haveI := GlobalTheory.isInvInvariant_of_compactSpace κ
  have e1 : ∀ k : K, ∫⁻ q, v ((q.1)⁻¹ * (q₀.1 * k₀.1) * (k.1)⁻¹) ∂ν =
      ∫⁻ q, v ((q.1)⁻¹ * (k₀ * k⁻¹).1) ∂ν := by
    intro k
    have := lintegral_mul_left_eq_self
      (μ := ν) (fun q : Q => v ((q.1)⁻¹ * (q₀.1 * k₀.1) * (k.1)⁻¹)) q₀
    rw [← this]
    congr 1
    ext q
    congr 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  simp_rw [e1]
  have e2 := lintegral_inv_eq_self (μ := κ) (fun k : K => ∫⁻ q, v ((q.1)⁻¹ * (k₀ * k).1) ∂ν)
  rw [e2]
  exact lintegral_mul_left_eq_self (fun k : K => ∫⁻ q, v ((q.1)⁻¹ * k.1) ∂ν) k₀

end GlobalTheory.HaarQK

namespace GlobalTheory.HaarQK
attribute [local instance] secondCountable_subgroup

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  {Q K : Subgroup G} [LocallyCompactSpace Q] [CompactSpace K]
  (ν : Measure Q) (κ : Measure K) [ν.IsHaarMeasure] [κ.IsHaarMeasure]

theorem weil_exchange (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (u v : G → ℝ≥0∞) (hu : Measurable u) (hv : Measurable v) :
    ∫⁻ g, u g * ∫⁻ k, ∫⁻ q, v ((q.1)⁻¹ * g * (k.1)⁻¹) ∂ν ∂κ ∂μ =
      ∫⁻ g, v g * ∫⁻ k, ∫⁻ q, u (q.1 * g * k.1) ∂ν ∂κ ∂μ := by
  have cF : Continuous fun x : G × (Q × K) => (x.2.1.1)⁻¹ * x.1 * (x.2.2.1)⁻¹ := by fun_prop
  have cH : Continuous fun x : G × (Q × K) => x.2.1.1 * x.1 * x.2.2.1 := by fun_prop
  have mF : Measurable fun x : G × (Q × K) => u x.1 * v ((x.2.1.1)⁻¹ * x.1 * (x.2.2.1)⁻¹) :=
    (hu.comp measurable_fst).mul (hv.comp cF.measurable)
  have mH : Measurable fun x : G × (Q × K) => u (x.2.1.1 * x.1 * x.2.2.1) * v x.1 :=
    (hu.comp cH.measurable).mul (hv.comp measurable_fst)
  have mv : ∀ g : G, Measurable fun p : Q × K => v ((p.1.1)⁻¹ * g * (p.2.1)⁻¹) := fun g =>
    hv.comp (Continuous.measurable (by fun_prop))
  have mu : ∀ g : G, Measurable fun p : Q × K => u (p.1.1 * g * p.2.1) := fun g =>
    hu.comp (Continuous.measurable (by fun_prop))
  have p1 : ∀ g : G, ∫⁻ k, ∫⁻ q, v ((q.1)⁻¹ * g * (k.1)⁻¹) ∂ν ∂κ =
      ∫⁻ p : Q × K, v ((p.1.1)⁻¹ * g * (p.2.1)⁻¹) ∂(ν.prod κ) := fun g =>
    (lintegral_prod_symm (μ := ν) (ν := κ) (fun p : Q × K => v ((p.1.1)⁻¹ * g * (p.2.1)⁻¹))
      (mv g).aemeasurable).symm
  have p2 : ∀ g : G, ∫⁻ k, ∫⁻ q, u (q.1 * g * k.1) ∂ν ∂κ =
      ∫⁻ p : Q × K, u (p.1.1 * g * p.2.1) ∂(ν.prod κ) := fun g =>
    (lintegral_prod_symm (μ := ν) (ν := κ) (fun p : Q × K => u (p.1.1 * g * p.2.1))
      (mu g).aemeasurable).symm
  simp_rw [p1, p2]
  calc ∫⁻ g, u g * ∫⁻ p : Q × K, v ((p.1.1)⁻¹ * g * (p.2.1)⁻¹) ∂(ν.prod κ) ∂μ
      = ∫⁻ g, ∫⁻ p : Q × K, u g * v ((p.1.1)⁻¹ * g * (p.2.1)⁻¹) ∂(ν.prod κ) ∂μ := by
        congr 1; ext g
        exact (lintegral_const_mul _ (mv g)).symm
    _ = ∫⁻ p : Q × K, ∫⁻ g, u g * v ((p.1.1)⁻¹ * g * (p.2.1)⁻¹) ∂μ ∂(ν.prod κ) :=
        lintegral_lintegral_swap mF.aemeasurable
    _ = ∫⁻ p : Q × K, ∫⁻ g, u (p.1.1 * g * p.2.1) * v g ∂μ ∂(ν.prod κ) := by
        congr 1; ext p
        set F : G → ℝ≥0∞ := fun g => u (p.1.1 * g * p.2.1) * v g with hF
        have h1 : ∫⁻ g, F ((p.1.1)⁻¹ * g * (p.2.1)⁻¹) ∂μ = ∫⁻ g, F (g * (p.2.1)⁻¹) ∂μ :=
          lintegral_mul_left_eq_self (fun g => F (g * (p.2.1)⁻¹)) _
        have h2 : ∫⁻ g, F (g * (p.2.1)⁻¹) ∂μ = ∫⁻ g, F g ∂μ := lintegral_mul_right_eq_self F _
        rw [← h2, ← h1]
        congr 1; ext g
        simp only [hF]
        congr 1
        congr 1; group
    _ = ∫⁻ g, ∫⁻ p : Q × K, u (p.1.1 * g * p.2.1) * v g ∂(ν.prod κ) ∂μ :=
        lintegral_lintegral_swap (mH.comp measurable_swap).aemeasurable
    _ = ∫⁻ g, v g * ∫⁻ p : Q × K, u (p.1.1 * g * p.2.1) ∂(ν.prod κ) ∂μ := by
        congr 1; ext g
        rw [lintegral_mul_const _ (mu g), mul_comm]

end GlobalTheory.HaarQK

namespace GlobalTheory.HaarQK
attribute [local instance] secondCountable_subgroup

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  {Q K : Subgroup G} [LocallyCompactSpace Q] [CompactSpace K]
  (ν : Measure Q) (κ : Measure K) [ν.IsHaarMeasure] [κ.IsHaarMeasure]

theorem iter_indicator_pos_finite (hQ : IsClosed (Q : Set G)) {S : Set G} (hS : IsCompact S)
    (m : Q × K → G) (hm : Continuous m) (h1 : m 1 ∈ interior S) {C : Set G} (hC : IsCompact C)
    (hmC : ∀ p, m p ∈ S → (p.1 : G) ∈ C) :
    ∫⁻ k, ∫⁻ q, S.indicator 1 (m (q, k)) ∂ν ∂κ ≠ 0 ∧
      ∫⁻ k, ∫⁻ q, S.indicator 1 (m (q, k)) ∂ν ∂κ ≠ ⊤ := by
  have hmeas : Measurable fun p : Q × K => S.indicator (1 : G → ℝ≥0∞) (m p) :=
    (measurable_one.indicator hS.measurableSet).comp hm.measurable
  rw [← lintegral_prod_symm (μ := ν) (ν := κ) (fun p : Q × K => S.indicator (1 : G → ℝ≥0∞) (m p))
    hmeas.aemeasurable]
  have e : (fun p : Q × K => S.indicator (1 : G → ℝ≥0∞) (m p)) = (m ⁻¹' S).indicator 1 := by
    ext p; by_cases hp : m p ∈ S <;> simp [Set.indicator, hp]
  rw [e, lintegral_indicator_one (hm.measurable hS.measurableSet)]
  constructor
  · refine (lt_of_lt_of_le ?_ (measure_mono (Set.preimage_mono interior_subset))).ne'
    exact (hm.isOpen_preimage _ isOpen_interior).measure_pos (ν.prod κ) ⟨1, h1⟩
  · have hcpt : IsCompact ((Subtype.val ⁻¹' C : Set Q) ×ˢ (Set.univ : Set K)) :=
      (hQ.isClosedEmbedding_subtypeVal.isCompact_preimage hC).prod isCompact_univ
    refine (lt_of_le_of_lt (measure_mono ?_) hcpt.measure_lt_top).ne
    intro p hp
    exact ⟨hmC p hp, trivial⟩

end GlobalTheory.HaarQK

namespace GlobalTheory


open GlobalTheory.HaarQK in
attribute [local instance] secondCountable_subgroup in
theorem lintegral_haar_eq_mul_iterated_closed_compact :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (Q K : Subgroup G), IsClosed (Q : Set G) → IsCompact (K : Set G) → (∀ g, ∃ q ∈ Q, ∃ k ∈ K, g = q * k) →
    ∀ (ν : Measure Q) (κ : Measure K) [ν.IsHaarMeasure] [κ.IsHaarMeasure], ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
      ∀ φ : G → ENNReal, Measurable φ → ∫⁻ g, φ g ∂μ = c * ∫⁻ k, ∫⁻ q, φ (q.1 * k.1) ∂ν ∂κ := by
  intro G _ _ _ _ _ _ _ _ μ _ _ Q K hQ hK hdec ν κ _ _
  haveI : LocallyCompactSpace Q := hQ.locallyCompactSpace
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨S, hS, hS1⟩ := exists_compact_mem_nhds (1 : G)
  have hS1' : (1 : G) ∈ interior S := mem_interior_iff_mem_nhds.mpr hS1
  set w : G → ℝ≥0∞ := S.indicator 1 with hw_def
  have hw : Measurable w := measurable_one.indicator hS.measurableSet

  obtain ⟨hσ0, hσT⟩ := iter_indicator_pos_finite ν κ hQ hS (fun p : Q × K => p.1.1 * p.2.1)
    (by fun_prop) (by simpa using hS1') (hS.mul hK) (by
      intro p hp
      have : (p.1 : G) = (p.1.1 * p.2.1) * (p.2.1)⁻¹ := by group
      rw [this]; exact Set.mul_mem_mul hp (K.inv_mem p.2.2))

  obtain ⟨hE0, hET⟩ := iter_indicator_pos_finite ν κ hQ hS (fun p : Q × K => (p.1.1)⁻¹ * p.2.1)
    (by fun_prop) (by simpa using hS1') (hK.mul hS.inv) (by
      intro p hp
      have : (p.1 : G) = p.2.1 * ((p.1.1)⁻¹ * p.2.1)⁻¹ := by group
      rw [this]; exact Set.mul_mem_mul p.2.2 (by simpa using hp))
  change ∫⁻ k, ∫⁻ q, w (q.1 * k.1) ∂ν ∂κ ≠ 0 at hσ0
  change ∫⁻ k, ∫⁻ q, w (q.1 * k.1) ∂ν ∂κ ≠ ⊤ at hσT
  change ∫⁻ k, ∫⁻ q, w ((q.1)⁻¹ * k.1) ∂ν ∂κ ≠ 0 at hE0
  change ∫⁻ k, ∫⁻ q, w ((q.1)⁻¹ * k.1) ∂ν ∂κ ≠ ⊤ at hET
  set σw := ∫⁻ k, ∫⁻ q, w (q.1 * k.1) ∂ν ∂κ with hσw
  set E := ∫⁻ k, ∫⁻ q, w ((q.1)⁻¹ * k.1) ∂ν ∂κ with hE
  have hμw0 : ∫⁻ g, w g ∂μ ≠ 0 := by
    rw [hw_def, lintegral_indicator_one hS.measurableSet]
    exact (measure_pos_of_mem_nhds μ hS1).ne'
  have hμwT : ∫⁻ g, w g ∂μ ≠ ⊤ := by
    rw [hw_def, lintegral_indicator_one hS.measurableSet]
    exact hS.measure_lt_top.ne

  have key1 : ∀ u : G → ℝ≥0∞, Measurable u →
      (∫⁻ g, u g ∂μ) * E = ∫⁻ g, w g * ∫⁻ k, ∫⁻ q, u (q.1 * g * k.1) ∂ν ∂κ ∂μ := by
    intro u hu
    rw [← weil_exchange ν κ μ u w hu hw, ← lintegral_mul_const _ hu]
    congr 1; ext g
    obtain ⟨q₀, hq₀, k₀, hk₀, rfl⟩ := hdec g
    rw [iter_left ν κ w ⟨q₀, hq₀⟩ ⟨k₀, hk₀⟩]
  have key2 : ∀ u : G → ℝ≥0∞, Measurable u → ∀ g : G,
      (∫⁻ k, ∫⁻ q, u (q.1 * g * k.1) ∂ν ∂κ) * σw =
        (∫⁻ k, ∫⁻ q, w (q.1 * g * k.1) ∂ν ∂κ) * ∫⁻ k, ∫⁻ q, u (q.1 * k.1) ∂ν ∂κ := by
    intro u hu g
    obtain ⟨q₀, hq₀, k₀, hk₀, rfl⟩ := hdec g
    rw [iter_right ν κ u hu ⟨q₀, hq₀⟩ ⟨k₀, hk₀⟩, iter_right ν κ w hw ⟨q₀, hq₀⟩ ⟨k₀, hk₀⟩]
    ring
  have mA : Measurable fun g => ∫⁻ k, ∫⁻ q, w (q.1 * g * k.1) ∂ν ∂κ := by
    have mf : Measurable fun x : G × (Q × K) => w (x.2.1.1 * x.1 * x.2.2.1) :=
      hw.comp (Continuous.measurable (by fun_prop))
    have e : (fun g => ∫⁻ k, ∫⁻ q, w (q.1 * g * k.1) ∂ν ∂κ) =
        fun g => ∫⁻ p : Q × K, w (p.1.1 * g * p.2.1) ∂(ν.prod κ) := by
      funext g
      exact (lintegral_prod_symm (μ := ν) (ν := κ) (fun p : Q × K => w (p.1.1 * g * p.2.1))
        (mf.comp (measurable_const.prodMk measurable_id)).aemeasurable).symm
    rw [e]
    exact mf.lintegral_prod_right'
  have key : ∀ u : G → ℝ≥0∞, Measurable u →
      (∫⁻ g, u g ∂μ) * σw = (∫⁻ g, w g ∂μ) * ∫⁻ k, ∫⁻ q, u (q.1 * k.1) ∂ν ∂κ := by
    intro u hu
    have mwA : Measurable fun g => w g * ∫⁻ k, ∫⁻ q, w (q.1 * g * k.1) ∂ν ∂κ := hw.mul mA
    have h : (∫⁻ g, u g ∂μ) * E * σw = (∫⁻ g, w g ∂μ) * E * ∫⁻ k, ∫⁻ q, u (q.1 * k.1) ∂ν ∂κ := by
      rw [key1 u hu, key1 w hw, ← lintegral_mul_const' _ _ hσT,
        ← lintegral_mul_const _ mwA]
      congr 1; ext g
      rw [mul_assoc, key2 u hu g, ← mul_assoc]
    rw [mul_right_comm, mul_right_comm (∫⁻ g, w g ∂μ)] at h
    exact (ENNReal.mul_left_inj hE0 hET).mp h
  refine ⟨(∫⁻ g, w g ∂μ) / σw, ?_, ?_, ?_⟩
  · exact ENNReal.div_ne_zero.mpr ⟨hμw0, hσT⟩
  · exact ENNReal.div_ne_top hμwT hσ0
  · intro φ hφ
    rw [← ENNReal.mul_div_cancel_right (a := ∫⁻ g, φ g ∂μ) hσ0 hσT, key φ hφ, ENNReal.mul_div_right_comm]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardSubtypeEqOfMultiset
open Matrix GlobalTheory.LKTrip Finset

namespace GlobalTheory.SigDiag

theorem eigenvalues_multiset_eq {n : ℕ} (r : Fin n → ℝ)
    (hA : (Matrix.diagonal (fun i => ((r i : ℝ) : ℂ))).IsHermitian) :
    Multiset.map hA.eigenvalues univ.val = Multiset.map r univ.val := by
  have h3 := hA.roots_charpoly_eq_eigenvalues
  rw [Matrix.charpoly_diagonal, Polynomial.roots_prod] at h3
  · have h4 := congrArg (Multiset.map Complex.re) h3
    simp only [Polynomial.roots_X_sub_C, Multiset.map_map] at h4
    simpa [Function.comp_def, Multiset.bind_singleton] using h4.symm
  · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]

theorem card_subtype_eq_of_multiset {n : ℕ} {f g : Fin n → ℝ}
    (h : Multiset.map f univ.val = Multiset.map g univ.val) (P : ℝ → Prop) [DecidablePred P] :
    Fintype.card {i // P (f i)} = Fintype.card {i // P (g i)} := by
  rw [Fintype.card_subtype, Fintype.card_subtype]
  have e : ∀ k : Fin n → ℝ, (univ.filter fun i => P (k i)).card =
      Multiset.countP P (Multiset.map k univ.val) := by
    intro k
    rw [Multiset.countP_map, Finset.card_def, Finset.filter_val]
  rw [e f, e g, h]

end GlobalTheory.SigDiag

namespace GlobalTheory.LKTrip

theorem sigPosH_sigNegH_diagonal : ∀ (n : ℕ) (r : Fin n → ℝ)
    (hA : (Matrix.diagonal (fun i => ((r i : ℝ) : ℂ))).IsHermitian),
    sigPosH hA = Fintype.card {i // 0 < r i} ∧ sigNegH hA = Fintype.card {i // r i < 0} := by
  intro n r hA
  have h := GlobalTheory.SigDiag.eigenvalues_multiset_eq r hA
  exact ⟨GlobalTheory.SigDiag.card_subtype_eq_of_multiset h (fun x => 0 < x),
    GlobalTheory.SigDiag.card_subtype_eq_of_multiset h (fun x => x < 0)⟩

end GlobalTheory.LKTrip
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClmSupBound
open GlobalTheory.SliceSchwartz
open scoped ContDiff

noncomputable section

namespace GlobalTheory.SliceOp

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def padL {κ κ' : Type} (h : κ → V) : κ ⊕ κ' → V := Sum.elim h 0

def qOp {κ κ' κ₁' : Type} [Fintype κ] [Fintype κ'] [Fintype κ₁']
    (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ) (f : SchwartzMap (κ ⊕ κ' → V) ℂ)
    (s : κ ⊕ κ₁' → V) : ℂ :=
  P (sliceR f (s ∘ Sum.inl)) (s ∘ Sum.inr)

abbrev pd {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] (w : X) :
    SchwartzMap X ℂ →L[ℂ] SchwartzMap X ℂ :=
  LineDeriv.lineDerivOpCLM ℂ (SchwartzMap X ℂ) w

theorem pd_apply {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] (w : X) (f : SchwartzMap X ℂ) (x : X) :
    pd w f x = fderiv ℝ f x w := by
  simp [pd, LineDeriv.lineDerivOpCLM_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]

theorem clm_sup_bound {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (T : SchwartzMap X ℂ →L[ℂ] SchwartzMap Y ℂ) (s : Finset (ℕ × ℕ)) :
    ∃ (s' : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ f : SchwartzMap X ℂ,
      s.sup (schwartzSeminormFamily ℂ Y ℂ) (T f) ≤ C * s'.sup (schwartzSeminormFamily ℂ X ℂ) f := by
  have hp : Continuous ((s.sup (schwartzSeminormFamily ℂ Y ℂ)).comp T.toLinearMap) :=
    (Seminorm.continuous_finsetSup fun i _ => (schwartz_withSeminorms ℂ Y ℂ).continuous_seminorm i).comp
      T.continuous
  obtain ⟨s', C, -, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ X ℂ) _ hp
  refine ⟨s', C, C.2, fun f => ?_⟩
  have := hC f
  simpa [Seminorm.smul_apply, NNReal.smul_def] using this

end GlobalTheory.SliceOp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CycleListPermInvariant
open scoped TensorProduct
open GlobalTheory.LKInvGood

namespace GlobalTheory.SepModel

theorem tmul_mem_cenOrder {F : Type} [Field F] [NumberField F] (ℓ : ℕ) [Fact ℓ.Prime] {N : ℕ}
    (hN : ¬ ℓ ∣ N) {c : F} (hc : IsIntegral ℤ ((N : F) * c)) :
    (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] c ∈ cenOrder ℓ F := by
  have hu : IsUnit (N : ℤ_[ℓ]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2 hN
  obtain ⟨u, hu⟩ := hu
  have hmem : (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] ((N : F) * c) ∈ cenOrder ℓ F :=
    Algebra.subset_adjoin ⟨⟨_, hc⟩, rfl⟩
  have heq : (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] c = (↑u⁻¹ : ℤ_[ℓ]) • ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] ((N : F) * c)) := by
    have h1 : (u : ℤ_[ℓ]) • ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] c) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] ((N : F) * c) := by
      rw [hu, Nat.cast_smul_eq_nsmul, ← TensorProduct.tmul_smul, nsmul_eq_mul]
    rw [← h1, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  rw [heq]
  exact Subalgebra.smul_mem _ hmem _

theorem exists_nat_integral {F : Type} [Field F] [NumberField F] (s : Finset F) :
    ∃ N : ℕ, 0 < N ∧ ∀ c ∈ s, IsIntegral ℤ ((N : F) * c) := by
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := F) s
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy0, fun c hc => ?_⟩
  have h := hy c hc
  rw [zsmul_eq_mul] at h
  rcases Int.natAbs_eq y with e | e
  · rw [e] at h; simpa using h
  · rw [e] at h
    have := h.neg
    simpa [neg_mul] using this

end GlobalTheory.SepModel

namespace GlobalTheory.SepModel

end GlobalTheory.SepModel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomSpecProdSelfPreimageEqClopen
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomSpecProdSelfPreimageEqClopen
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.AlgConn

namespace GlobalTheory

theorem exists_hom_spec_prod_self_preimage_eq_clopen :
    ∀ (O : Type) [CommRing O] (T : Scheme.{0}) (p : T ⟶ Spec (.of O)) (U : Set T), IsClopen U →
      ∃ h : T ⟶ Spec (.of (O × O)), h ≫ twoπ O = p ∧
        ((h ⁻¹ᵁ (Spec (.of (O × O))).basicOpen (fst1 O) : T.Opens) : Set T) = U := by
  intro O _ T p U hU
  obtain ⟨ε, he, hεU⟩ := exists_idempotent_basicOpen_eq_of_isClopen T U hU
  let φ : O →+* Γ(T, ⊤) := ((Scheme.ΓSpecIso (.of O)).inv ≫ p.appTop).hom
  let ψ : O × O →+* Γ(T, ⊤) :=
    { toFun := fun x => φ x.1 * ε + φ x.2 * (1 - ε)
      map_one' := by simp
      map_mul' := fun x y => by
        simp only [Prod.fst_mul, Prod.snd_mul, map_mul]
        linear_combination -(φ x.1 * φ y.1 - φ x.1 * φ y.2 - φ x.2 * φ y.1 + φ x.2 * φ y.2) * he
      map_zero' := by simp
      map_add' := fun x y => by
        simp only [Prod.fst_add, Prod.snd_add, map_add (f := _)]
        ring }
  have hψ : ψ.comp (algebraMap O (O × O)) = φ := by
    ext a
    change φ a * ε + φ a * (1 - ε) = φ a
    ring
  refine ⟨T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ), ?_, ?_⟩
  · have : CommRingCat.ofHom φ = (Scheme.ΓSpecIso (.of O)).inv ≫ p.appTop := rfl
    rw [Category.assoc, twoπ, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ, this, Spec.map_comp,
      ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  · rw [Scheme.preimage_basicOpen_top, ← hεU]
    congr 2
    have h1 : (T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ)).appTop (fst1 O) = ψ ((1, 0) : O × O) := by
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, Scheme.toSpecΓ_appTop]
      have := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ψ)
      have h2 := congrArg (fun f => f.hom (fst1 O)) this
      simp only [CommRingCat.comp_apply, CommRingCat.hom_ofHom] at h2
      refine h2.trans ?_
      simp [fst1]
    rw [h1]
    change φ 1 * ε + φ 0 * (1 - ε) = ε
    simp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomSpecProdSelfPreimageEqClopenStatement
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.AlgConn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hom_specProdSelf_preimage_eq_clopen : ∀ (O : Type) [CommRing O] (T : Scheme.{0}) (p : T ⟶ Spec (.of O)) (U : Set T), IsClopen U → ∃ h : T ⟶ Spec (.of (O × O)), h ≫ twoπ O = p ∧ ((h ⁻¹ᵁ (Spec (.of (O × O))).basicOpen (fst1 O) : T.Opens) : Set T) = U := by
  first | exact @GlobalTheory.exists_hom_spec_prod_self_preimage_eq_clopen | exact GlobalTheory.exists_hom_spec_prod_self_preimage_eq_clopen | (intros; apply GlobalTheory.exists_hom_spec_prod_self_preimage_eq_clopen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurePreservingOfNormSqEqSumComplexCoords
open MeasureTheory

namespace GlobalTheory

private theorem measurePreserving_piCurry_symm_fin_two (ι : Type) [Fintype ι] :
    MeasurePreserving (MeasurableEquiv.piCurry (fun (_ : ι) (_ : Fin 2) => ℝ)).symm
      volume volume := by
  classical
  refine ⟨(MeasurableEquiv.piCurry _).symm.measurable, ?_⟩
  symm
  rw [volume_pi]
  refine Measure.pi_eq fun s hs => ?_
  rw [(MeasurableEquiv.piCurry _).symm.map_apply]
  have hpre : (MeasurableEquiv.piCurry (fun (_ : ι) (_ : Fin 2) => ℝ)).symm ⁻¹' Set.univ.pi s =
      Set.univ.pi fun i => Set.univ.pi fun k => s ⟨i, k⟩ := by
    ext x
    simp [Set.mem_pi, Sigma.forall, MeasurableEquiv.coe_piCurry_symm, Sigma.uncurry]
  rw [hpre, volume_pi_pi]
  simp only [volume_pi_pi]
  rw [← Finset.univ_sigma_univ, Finset.prod_sigma]

theorem measurePreserving_of_norm_sq_eq_sum_complex_coords
    (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (ι : Type) [Fintype ι] (e : V ≃L[ℝ] (ι → ℂ))
    (he : ∀ v, ‖v‖ ^ 2 = ∑ i, ‖e v i‖ ^ 2) : MeasurePreserving e volume volume := by
  classical
  let Φ : (ι → ℂ) ≃ₗ[ℝ] EuclideanSpace ℝ (Σ _ : ι, Fin 2) :=
    (LinearEquiv.piCongrRight fun _ => Complex.basisOneI.equivFun).trans
      ((LinearEquiv.piCurry ℝ fun (_ : ι) (_ : Fin 2) => ℝ).symm.trans
        (WithLp.linearEquiv 2 ℝ _).symm)
  have hΦ : ∀ z, ‖Φ z‖ ^ 2 = ∑ i, ‖z i‖ ^ 2 := by
    intro z
    rw [EuclideanSpace.norm_sq_eq, ← Finset.univ_sigma_univ, Finset.sum_sigma]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hc : ∀ k, Φ z ⟨i, k⟩ = Complex.basisOneI.repr (z i) k := fun k => rfl
    simp only [hc, Fin.sum_univ_two, Complex.coe_basisOneI_repr, Matrix.cons_val_zero,
      Matrix.cons_val_one, Real.norm_eq_abs, sq_abs]
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  let F : V ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Σ _ : ι, Fin 2) :=
    { toLinearEquiv := e.toLinearEquiv.trans Φ
      norm_map' := fun v => by
        have h : ‖Φ (e v)‖ ^ 2 = ‖v‖ ^ 2 := by rw [hΦ, he]
        exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h }
  let G : (ι → ℂ) ≃ᵐ EuclideanSpace ℝ (Σ _ : ι, Fin 2) :=
    (MeasurableEquiv.piCongrRight fun _ => Complex.measurableEquivPi).trans
      ((MeasurableEquiv.piCurry fun (_ : ι) (_ : Fin 2) => ℝ).symm.trans
        (MeasurableEquiv.toLp 2 _))
  have hG : MeasurePreserving G volume volume :=
    (PiLp.volume_preserving_toLp _).comp ((measurePreserving_piCurry_symm_fin_two ι).comp
      (volume_preserving_pi fun _ => Complex.volume_preserving_equiv_pi))
  have hFG : (F : V → EuclideanSpace ℝ (Σ _ : ι, Fin 2)) = G ∘ e := by
    funext v
    rfl
  have hF : MeasurePreserving (G ∘ e) volume volume := hFG ▸ F.measurePreserving
  exact hG.comp_left_iff.1 hF

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOnComplexHessianOfContDiffOnTwo
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOnComplexHessianOfContDiffOnTwo
open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder

namespace GlobalTheory

theorem contDiffOn_one_wdb_of_contDiffOn_two_isOpen {n : ℕ} {U : Set (V n)} {g : V n → ℂ}
    (hU : IsOpen U) (hg : ContDiffOn ℝ 2 g U) (l : Fin n) :
    ContDiffOn ℝ 1 (wdb n l g) U := by
  have hD : ContDiffOn ℝ 1 (fun y => fderiv ℝ g y) U :=
    hg.fderiv_of_isOpen hU (by norm_num)
  have h1 : ContDiffOn ℝ 1 (fun y => fderiv ℝ g y (bas n l)) U :=
    hD.clm_apply contDiffOn_const
  have h2 : ContDiffOn ℝ 1 (fun y => fderiv ℝ g y (Complex.I • bas n l)) U :=
    hD.clm_apply contDiffOn_const
  have h3 : ContDiffOn ℝ 1
      (fun y => (fderiv ℝ g y (bas n l) + Complex.I * fderiv ℝ g y (Complex.I • bas n l)) / 2) U :=
    (h1.add (contDiffOn_const.mul h2)).div_const 2
  have e : wdb n l g = fun y =>
      (fderiv ℝ g y (bas n l) + Complex.I * fderiv ℝ g y (Complex.I • bas n l)) / 2 :=
    funext fun y => rfl
  rw [e]
  exact h3

theorem continuousOn_wd_of_contDiffOn_one_isOpen {n : ℕ} {U : Set (V n)} {g : V n → ℂ}
    (hU : IsOpen U) (hg : ContDiffOn ℝ 1 g U) (j : Fin n) :
    ContinuousOn (wd n j g) U := by
  have hD : ContinuousOn (fun y => fderiv ℝ g y) U :=
    hg.continuousOn_fderiv_of_isOpen hU le_rfl
  have h1 : ContinuousOn (fun y => fderiv ℝ g y (bas n j)) U :=
    hD.clm_apply continuousOn_const
  have h2 : ContinuousOn (fun y => fderiv ℝ g y (Complex.I • bas n j)) U :=
    hD.clm_apply continuousOn_const
  have h3 : ContinuousOn
      (fun y => (fderiv ℝ g y (bas n j) - Complex.I * fderiv ℝ g y (Complex.I • bas n j)) / 2) U :=
    (h1.sub (continuousOn_const.mul h2)).div_const 2
  have e : wd n j g = fun y =>
      (fderiv ℝ g y (bas n j) - Complex.I * fderiv ℝ g y (Complex.I • bas n j)) / 2 :=
    funext fun y => rfl
  rw [e]
  exact h3

theorem continuousOn_cHess_of_contDiffOn_two :
    ∀ (n : ℕ) (U : Set (V n)) (φ : V n → ℝ), IsOpen U → ContDiffOn ℝ 2 φ U → ∀ j l,
      ContinuousOn (fun z => cHess n (fun v => (φ v : ℂ)) z j l) U := by
  intro n U φ hU hφ j l
  have hc : ContDiffOn ℝ 2 (fun v => (φ v : ℂ)) U :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hφ
  have hb := contDiffOn_one_wdb_of_contDiffOn_two_isOpen hU hc l
  simpa only [cHess, Matrix.of_apply] using continuousOn_wd_of_contDiffOn_one_isOpen hU hb j

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOnComplexHessianOfContDiffOnTwoStatement
open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuousOn_complex_hessian_of_contDiffOn_two : ∀ (n : ℕ) (U : Set (V n)) (φ : V n → ℝ), IsOpen U → ContDiffOn ℝ 2 φ U → ∀ j l, ContinuousOn (fun z => cHess n (fun v => (φ v : ℂ)) z j l) U := by
  first | exact @GlobalTheory.continuousOn_cHess_of_contDiffOn_two | exact GlobalTheory.continuousOn_cHess_of_contDiffOn_two | (intros; apply GlobalTheory.continuousOn_cHess_of_contDiffOn_two <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumOrbitsInvStabilizerCardMass
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumOrbitsInvStabilizerCardMass
namespace GlobalTheory

open MulAction Function

theorem finsum_orbits_stabilizer_mass {K Z : Type} [Group K] [Finite K] [MulAction K Z]
    (f : Z → ℂ) (hf : ∀ (k : K) (z : Z), f (k • z) = f z) (hs : (Function.support f).Finite) :
    ∑ᶠ o : MulAction.orbitRel.Quotient K Z,
        ((Nat.card (MulAction.stabilizer K (Quotient.out o)) : ℕ) : ℂ)⁻¹ * f (Quotient.out o) =
      ((Nat.card K : ℕ) : ℂ)⁻¹ * ∑ᶠ z, f z := by
  classical
  let ρ : Z → orbitRel.Quotient K Z := fun z => Quotient.mk'' z

  have hmem : ∀ (o : orbitRel.Quotient K Z) (a : Z), ρ a = o ↔ a ∈ orbit K (Quotient.out o) := by
    intro o a
    constructor
    · intro h
      have : ρ a = ρ (Quotient.out o) := by rw [h]; exact (Quotient.out_eq' o).symm
      exact Quotient.exact this
    · intro h
      have : ρ a = ρ (Quotient.out o) := Quotient.sound h
      rw [this]; exact Quotient.out_eq' o
  have hfib : ∀ o : orbitRel.Quotient K Z,
      (∑ᶠ a : {a // ρ a = o}, f a.1) = (Nat.card (orbit K (Quotient.out o)) : ℂ) * f (Quotient.out o) := by
    intro o
    let e : {a // ρ a = o} ≃ orbit K (Quotient.out o) := Equiv.subtypeEquivRight (hmem o)
    haveI : Finite (orbit K (Quotient.out o)) := (Set.finite_range fun k : K => k • Quotient.out o).to_subtype
    haveI : Finite {a // ρ a = o} := Finite.of_equiv _ e.symm
    letI : Fintype {a // ρ a = o} := Fintype.ofFinite _
    have hc : ∀ a : {a // ρ a = o}, f a.1 = f (Quotient.out o) := by
      intro a
      obtain ⟨k, hk⟩ := (hmem o a.1).1 a.2
      rw [← hk]; exact hf _ _
    rw [finsum_eq_sum_of_fintype, Finset.sum_congr rfl (fun a _ => hc a), Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card, Nat.card_congr e]
  have hcard : ∀ z : Z, Nat.card (orbit K z) * Nat.card (stabilizer K z) = Nat.card K := by
    intro z
    letI : Fintype K := Fintype.ofFinite K
    rw [← (stabilizer K z).index_mul_card, MulAction.index_stabilizer, Nat.card_coe_set_eq]
  rw [finsum_fiberwise_of_finite_support ρ f hs]
  simp_rw [hfib]
  rw [mul_finsum]
  apply finsum_congr
  intro o
  have h := hcard (Quotient.out o)
  haveI : Finite (orbit K (Quotient.out o)) := (Set.finite_range fun k : K => k • Quotient.out o).to_subtype
  haveI : Nonempty (orbit K (Quotient.out o)) := ⟨⟨_, mem_orbit_self _⟩⟩
  have h1 : (Nat.card (orbit K (Quotient.out o)) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := orbit K (Quotient.out o))).ne'
  have h2 : (Nat.card (stabilizer K (Quotient.out o)) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := stabilizer K (Quotient.out o))).ne'
  rw [← h]; push_cast
  field_simp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumOrbitsInvStabilizerCardMassStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_orbits_inv_stabilizer_card_mass : ∀ {K Z : Type} [Group K] [Finite K] [MulAction K Z] (f : Z → ℂ), (∀ (k : K) (z : Z), f (k • z) = f z) → (Function.support f).Finite → ∑ᶠ o : MulAction.orbitRel.Quotient K Z, ((Nat.card (MulAction.stabilizer K (Quotient.out o)) : ℕ) : ℂ)⁻¹ * f (Quotient.out o) = ((Nat.card K : ℕ) : ℂ)⁻¹ * ∑ᶠ z, f z := by
  first | exact @GlobalTheory.finsum_orbits_stabilizer_mass | exact GlobalTheory.finsum_orbits_stabilizer_mass | (intros; apply GlobalTheory.finsum_orbits_stabilizer_mass <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomExtSpecProdSelfOfBasicOpenPreimageEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomExtSpecProdSelfOfBasicOpenPreimageEq
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.AlgConn

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AlgConn

theorem hom_eq_toSpecΓ_comp {T : Scheme.{0}} {A : CommRingCat.{0}} (h : T ⟶ Spec A) :
    h = T.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso A).inv ≫ h.appTop) := by
  rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

theorem hom_ext_of_twoπ_of_basicOpen : ∀ (O : Type) [CommRing O] (T : Scheme.{0})
    (h h' : T ⟶ Spec (.of (O × O))), h ≫ twoπ O = h' ≫ twoπ O →
    h ⁻¹ᵁ (Spec (.of (O × O))).basicOpen (fst1 O) = h' ⁻¹ᵁ (Spec (.of (O × O))).basicOpen (fst1 O) →
    h = h' := by
  intro O _ T h h' hπ hb
  rw [hom_eq_toSpecΓ_comp h, hom_eq_toSpecΓ_comp h']
  congr 2

  have h1 : ∀ a : O, ((Scheme.ΓSpecIso (.of (O × O))).inv ≫ h.appTop).hom (algebraMap O (O × O) a) =
      ((Scheme.ΓSpecIso (.of (O × O))).inv ≫ h'.appTop).hom (algebraMap O (O × O) a) := by
    intro a
    have key : ∀ g : T ⟶ Spec (.of (O × O)),
        ((Scheme.ΓSpecIso (.of (O × O))).inv ≫ g.appTop).hom (algebraMap O (O × O) a) =
          ((Scheme.ΓSpecIso (.of O)).inv ≫ (g ≫ twoπ O).appTop).hom a := by
      intro g
      rw [Scheme.Hom.comp_appTop, ← Category.assoc]
      have n := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap O (O × O)))
      have n' : CommRingCat.ofHom (algebraMap O (O × O)) ≫ (Scheme.ΓSpecIso (.of (O × O))).inv =
          (Scheme.ΓSpecIso (.of O)).inv ≫ (Spec.map (CommRingCat.ofHom (algebraMap O (O × O)))).appTop := by
        rw [Iso.eq_inv_comp, ← Category.assoc, ← n, Category.assoc, Iso.hom_inv_id, Category.comp_id]
      rw [← n']
      rfl
    rw [key h, key h', hπ]

  have h2 : ((Scheme.ΓSpecIso (.of (O × O))).inv ≫ h.appTop).hom ((1, 0) : O × O) =
      ((Scheme.ΓSpecIso (.of (O × O))).inv ≫ h'.appTop).hom ((1, 0) : O × O) := by
    change h.appTop (fst1 O) = h'.appTop (fst1 O)
    have hid : fst1 O * fst1 O = fst1 O := by
      rw [fst1, ← map_mul]; congr 1; ext <;> simp
    apply GlobalTheory.idempotent_eq_of_basicOpen_eq T
    · rw [← map_mul, hid]
    · rw [← map_mul, hid]
    · rw [← Scheme.preimage_basicOpen_top, ← Scheme.preimage_basicOpen_top, hb]

  ext1
  ext x
  obtain ⟨a, b⟩ := x
  have hx : ((a, b) : O × O) = algebraMap O (O × O) a * (1, 0) + algebraMap O (O × O) b * (1 - (1, 0)) := by
    ext <;> simp
  rw [hx, map_add (f := _), map_mul, map_mul, map_sub, map_one, map_add (f := _), map_mul, map_mul, map_sub, map_one, h1 a, h1 b, h2]

end GlobalTheory.AlgConn
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomExtSpecProdSelfOfBasicOpenPreimageEqStatement
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.AlgConn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hom_ext_specProdSelf_of_basicOpen_preimage_eq : ∀ (O : Type) [CommRing O] (T : Scheme.{0}) (h h' : T ⟶ Spec (.of (O × O))), h ≫ twoπ O = h' ≫ twoπ O → h ⁻¹ᵁ (Spec (.of (O × O))).basicOpen (fst1 O) = h' ⁻¹ᵁ (Spec (.of (O × O))).basicOpen (fst1 O) → h = h' := by
  first | exact @GlobalTheory.AlgConn.hom_ext_of_twoπ_of_basicOpen | exact GlobalTheory.AlgConn.hom_ext_of_twoπ_of_basicOpen | (intros; apply GlobalTheory.AlgConn.hom_ext_of_twoπ_of_basicOpen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetaplecticQuadraticOperatorEqSumSymplecticDual
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetaplecticQuadraticOperatorEqSumSymplecticDual
open scoped Matrix
open MeasureTheory GlobalTheory.RealWeil

namespace GlobalTheory

theorem quad_eq_sum_symplDual (l κ : Type) [Fintype l] [DecidableEq l] [Fintype κ]
    (X : Matrix (l ⊕ l) (l ⊕ l) ℝ) (u v : κ → (l ⊕ l → ℝ))
    (h : ∀ w, ∑ i, sympl (v i) w • u i = w) :
    quad X = (4 * Real.pi * Complex.I : ℂ)⁻¹ • ∑ i, (1 / 2 : ℂ) •
      (dRho (X *ᵥ u i) * dRho (v i) + dRho (v i) * dRho (X *ᵥ u i)) := by
  have hJ : ∀ (x : l ⊕ l → ℝ) (b : l ⊕ l), sympl x (Matrix.J l ℝ *ᵥ Pi.single b 1) = x b := by
    intro x b
    rcases b with b | b <;>
      simp [sympl, pPart, qPart, PiLp.inner_apply, Matrix.J, Matrix.mulVec, dotProduct, Pi.single_apply,
        Matrix.one_apply]
  have hcol : ∀ b, ∑ i, v i b • u i = Matrix.J l ℝ *ᵥ Pi.single b 1 := by
    intro b
    have := h (Matrix.J l ℝ *ᵥ Pi.single b 1)
    simp only [hJ] at this
    exact this
  have hcoef : ∀ a b, ∑ i, (X *ᵥ u i) a * v i b = (X * Matrix.J l ℝ) a b := by
    intro a b
    have := congrArg (fun w => (X *ᵥ w) a) (hcol b)
    simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.mulVec_mulVec] at this
    have e : ((X * Matrix.J l ℝ) *ᵥ Pi.single b 1) a = (X * Matrix.J l ℝ) a b := by
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [← e, ← this]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hT : ∀ i, dRho (X *ᵥ u i) * dRho (v i) + dRho (v i) * dRho (X *ᵥ u i) =
      ∑ a, ∑ b, (((X *ᵥ u i) a * v i b : ℝ) : ℂ) •
        (dRho (Pi.single a 1) * dRho (Pi.single b 1) + dRho (Pi.single b 1) * dRho (Pi.single a 1)) := by
    intro i
    rw [dRho_eq_sum (X *ᵥ u i), dRho_eq_sum (v i)]
    simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm]
    conv_lhs => arg 1; rw [Finset.sum_comm]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    push_cast
    module
  rw [quad]
  congr 1
  simp_rw [hT, ← hcoef, Finset.sum_div, Complex.ofReal_sum, Finset.sum_smul, Finset.smul_sum]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul]
  congr 1
  push_cast
  ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetaplecticQuadraticOperatorEqSumSymplecticDualStatement
open scoped Matrix
open MeasureTheory GlobalTheory.RealWeil
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.metaplecticQuadraticOperator_eq_sum_symplectic_dual : ∀ (l κ : Type) [Fintype l] [DecidableEq l] [Fintype κ] (X : Matrix (l ⊕ l) (l ⊕ l) ℝ) (u v : κ → (l ⊕ l → ℝ)),
    (∀ w, ∑ i, sympl (v i) w • u i = w) →
    quad X = (4 * Real.pi * Complex.I : ℂ)⁻¹ • ∑ i, (1 / 2 : ℂ) •
      (dRho (X *ᵥ u i) * dRho (v i) + dRho (v i) * dRho (X *ᵥ u i)) := by
  first | exact @GlobalTheory.quad_eq_sum_symplDual | exact GlobalTheory.quad_eq_sum_symplDual | (intros; apply GlobalTheory.quad_eq_sum_symplDual <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSubgroupAddCharDotProductTrivialOnCompact
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSubgroupAddCharDotProductTrivialOnCompact
open Matrix

namespace GlobalTheory.CharDotKill

theorem pow_near_one {z : ℂ} (h : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2) : z = 1 := by
  first
  | exact @_root_.GlobalTheory.KeyLemmaTwo.main
  | exact _root_.GlobalTheory.KeyLemmaTwo.main
  | (apply _root_.GlobalTheory.KeyLemmaTwo.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.KeyLemmaTwo.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.KeyLemmaTwo.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.KeyLemmaTwo.main ..)

theorem exists_open_ker {K : Type} [AddCommGroup K] [TopologicalSpace K] [NonarchimedeanAddGroup K]
    (ψ : AddChar K ℂ) (hψ : Continuous ψ) : ∃ U : OpenAddSubgroup K, ∀ t ∈ U, ψ t = 1 := by
  have hV : {t : K | ‖ψ t - 1‖ < 1 / 2} ∈ nhds (0 : K) :=
    (isOpen_lt (hψ.sub continuous_const).norm continuous_const).mem_nhds (by simp)
  obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ hV
  refine ⟨V, fun t ht => pow_near_one fun n => ?_⟩
  rw [← AddChar.map_nsmul_eq_pow]
  exact hV (V.toAddSubgroup.nsmul_mem ht n)

theorem nonarchimedean_pi {κ K : Type} [Finite κ] [AddCommGroup K] [TopologicalSpace K]
    [NonarchimedeanAddGroup K] : NonarchimedeanAddGroup (κ → K) where
  is_nonarchimedean S hS := by
    rw [nhds_pi, Filter.mem_pi] at hS
    obtain ⟨I, -, t, ht, hsub⟩ := hS
    choose M hM using fun i => NonarchimedeanAddGroup.is_nonarchimedean _ (ht i)
    refine ⟨⟨AddSubgroup.pi Set.univ fun i => (M i).toAddSubgroup, ?_⟩, ?_⟩
    · change IsOpen ((AddSubgroup.pi Set.univ fun i => (M i).toAddSubgroup : AddSubgroup (κ → K)) : Set (κ → K))
      rw [AddSubgroup.coe_pi]; exact isOpen_set_pi Set.finite_univ fun i _ => (M i).isOpen
    · intro x hx
      apply hsub
      intro i _
      exact hM i (hx i (Set.mem_univ i))

theorem charDot_kill : ∀ {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
    [NonarchimedeanAddGroup K] (χ : AddChar K ℂ), Continuous χ → ∀ (κ : Type) [Fintype κ]
    (C : Set (κ → K)), IsCompact C → ∃ H : OpenAddSubgroup (κ → K),
      ∀ z ∈ C, ∀ a ∈ H, ∀ b ∈ H, χ (z ⬝ᵥ b + a ⬝ᵥ b) = 1 := by
  intro K _ _ _ _ χ hχ κ _ C hC
  obtain ⟨K₀, hK₀⟩ := exists_open_ker χ hχ
  have hdot : Continuous fun p : (κ → K) × (κ → K) => p.1 ⬝ᵥ p.2 :=
    continuous_fst.dotProduct continuous_snd
  have hO : IsOpen {p : (κ → K) × (κ → K) | p.1 ⬝ᵥ p.2 ∈ (K₀ : Set K)} :=
    K₀.isOpen.preimage hdot

  have hW : ∀ᶠ b in nhds (0 : κ → K), ∀ z ∈ C, z ⬝ᵥ b ∈ (K₀ : Set K) := by
    refine hC.eventually_forall_of_forall_eventually fun z _ => ?_
    have hO' : IsOpen {p : (κ → K) × (κ → K) | p.2 ⬝ᵥ p.1 ∈ (K₀ : Set K)} :=
      K₀.isOpen.preimage (continuous_snd.dotProduct continuous_fst)
    filter_upwards [hO'.mem_nhds (x := ((0 : κ → K), z)) (by simp [K₀.zero_mem])] with p hp
    exact hp

  have hP : {p : (κ → K) × (κ → K) | p.1 ⬝ᵥ p.2 ∈ (K₀ : Set K)} ∈ nhds ((0 : κ → K), (0 : κ → K)) :=
    hO.mem_nhds (by simp [K₀.zero_mem])
  rw [nhds_prod_eq, Filter.mem_prod_iff] at hP
  obtain ⟨U, hU, V, hV, hUV⟩ := hP
  haveI : NonarchimedeanAddGroup (κ → K) := nonarchimedean_pi
  obtain ⟨H, hH⟩ := NonarchimedeanAddGroup.is_nonarchimedean _
    (Filter.inter_mem (Filter.inter_mem hU hV) hW)
  refine ⟨H, fun z hz a ha b hb => hK₀ _ (K₀.add_mem ?_ ?_)⟩
  · exact (hH hb).2 z hz
  · exact hUV (Set.mk_mem_prod (hH ha).1.1 (hH hb).1.2)

end GlobalTheory.CharDotKill
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSubgroupAddCharDotProductTrivialOnCompactStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_subgroup_addChar_dotProduct_trivial_on_compact : ∀ {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] [NonarchimedeanAddGroup K] (χ : AddChar K ℂ), Continuous χ → ∀ (κ : Type) [Fintype κ] (C : Set (κ → K)), IsCompact C → ∃ H : OpenAddSubgroup (κ → K), ∀ z ∈ C, ∀ a ∈ H, ∀ b ∈ H, χ (z ⬝ᵥ b + a ⬝ᵥ b) = 1 := by
  first | exact @GlobalTheory.CharDotKill.charDot_kill | exact GlobalTheory.CharDotKill.charDot_kill | (intros; apply GlobalTheory.CharDotKill.charDot_kill <;> assumption)
end
end
