module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothIntegralLinearChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormClearDenominatorsAwayFromPlace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LimitBlockTypes

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CarriesInducedNode
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CarriesInducedNode
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.LimV.NodeCarry

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N r s : ℕ}

theorem mul_mem_Sm {e φ : GA E N → ℂ} (he : e ∈ Sm E N) (hφ : φ ∈ Sm E N) :
    (fun x => e x * φ x) ∈ Sm E N := by
  intro g
  refine ((he g).mul (hφ g)).congr fun x hx => ?_
  have hx' : IsUnit (Matrix.of x) := hx
  simp [chart, hx']

theorem memInd2_of_mem {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {φ : Sm E (r + s)}
    (h : φ ∈ indSpan U₁ U₂) : MemInd2 U₁ U₂ φ := by
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ⟨fun _ _ => rfl, fun _ _ => zero_mem _⟩
  | add x y _ _ hx hy =>
    refine ⟨fun u g => ?_, fun k g => add_mem (hx.2 k g) (hy.2 k g)⟩
    change x.1 _ + y.1 _ = x.1 g + y.1 g
    rw [hx.1, hy.1]
  | smul c x _ hx =>
    refine ⟨fun u g => ?_, fun k g => Submodule.smul_mem _ c (hx.2 k g)⟩
    change c • x.1 _ = c • x.1 g
    rw [hx.1]

theorem carries_translate {e : GA E N → ℂ} {U U' : Submodule ℂ (Sm E N)} (hU : FinStable U) (hU' : FinStable U')
    (hc : Carries e U U') (P : GL (Fin N) (Af E)) {a : Sm E N} (ha : a ∈ U) :
    ∃ a' ∈ U', ∀ m, a'.1 m = e (m * finGL E N P) * a.1 m := by
  obtain ⟨b, hb, hbe⟩ := hc _ (hU P⁻¹ a ha)
  refine ⟨act (.fin P) b, hU' P b hb, fun m => ?_⟩
  have e1 : (act (.fin P) b).1 m = b.1 (m * finGL E N P) := rfl
  have e2 : (act (.fin P⁻¹) a).1 (m * finGL E N P) = a.1 (m * finGL E N P * finGL E N P⁻¹) := rfl
  rw [e1, hbe, e2, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]

theorem finGL_unip (x : BlockIx (r + s) r → Af E) : finGL E (r + s) (unip x) = unip fun p => sFin E (x p) := by
  refine ga_ext ?_ ?_
  · rw [pInf_finGL, IwaAd.map_unip]
    have : (fun p => pInf E (sFin E (x p))) = 0 := funext fun p => map_zero (infEq E).symm
    rw [this]
    exact unip_zero.symm
  · rw [pFin_finGL, IwaAd.map_unip]
    rfl

theorem finGL_lev (p : GL (Fin r) (Af E) × GL (Fin s) (Af E)) :
    finGL E (r + s) (lev (Af E) r s p) = lev (Ad E) r s (finGL E r p.1, finGL E s p.2) := by
  refine ga_ext ?_ ?_
  · rw [pInf_finGL, IwaAd.map_lev, pInf_finGL, pInf_finGL]
    exact (map_one (lev (Cinf E) r s)).symm
  · rw [pFin_finGL, IwaAd.map_lev, pFin_finGL, pFin_finGL]

theorem nodeFn_slice {e₁ : GA E r → ℂ} {e₂ : GA E s → ℂ} (h₁ : FlatFn e₁) (h₂ : FlatFn e₂) (k : Kinf E (r + s))
    (g : GL (Fin (r + s)) (Af E)) : ∃ p : GL (Fin r) (Af E) × GL (Fin s) (Af E), ∀ m : GA E r × GA E s,
      nodeFn e₁ e₂ (lev (Ad E) r s m * cf (r + s) k g) = e₁ (m.1 * finGL E r p.1) * e₂ (m.2 * finGL E s p.2) := by
  obtain ⟨xf, p, c, hc, hg⟩ := IwaFin.exists_unip_lev_integral E r s g
  refine ⟨p, fun m => ?_⟩
  obtain ⟨v, hv⟩ := lev_mul_unip m fun q => sFin E (xf q)
  have e1 : cf (r + s) k g = unip (fun q => sFin E (xf q)) * lev (Ad E) r s (finGL E r p.1, finGL E s p.2) *
      cf (r + s) k c := by
    rw [hg, cf, cf, map_mul _ (unip xf * _) c, ← mul_assoc, infGL_comm, mul_assoc (finGL _ _ _), map_mul, finGL_unip,
      finGL_lev]
  rw [e1, ← mul_assoc, ← mul_assoc, hv, mul_assoc (unip v), ← map_mul]
  exact GlobalTheory.T.node_function_levi_decomposition e₁ e₂ h₁ h₂ v _ k c hc

theorem carries_nodeFn : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ} (e₁ : GA E r → ℂ) (e₂ : GA E s → ℂ) (U₁ U₁' : Submodule ℂ (Sm E r)) (U₂ U₂' : Submodule ℂ (Sm E s)), FlatFn e₁ → FlatFn e₂ → FinStable U₁ → FinStable U₁' → FinStable U₂ → FinStable U₂' → Carries e₁ U₁ U₁' → Carries e₂ U₂ U₂' → Carries (nodeFn e₁ e₂) (indSpan U₁ U₂) (indSpan U₁' U₂') := by
  intro E _ _ _ r s e₁ e₂ U₁ U₁' U₂ U₂' h₁ h₂ s₁ s₁' s₂ s₂' c₁ c₂ φ hφ
  have hF := GlobalTheory.T.flat_node_function e₁ e₂ h₁ h₂
  have hI := memInd2_of_mem hφ
  refine ⟨⟨fun x => nodeFn e₁ e₂ x * φ.1 x, mul_mem_Sm hF.sm φ.2⟩,
    Submodule.subset_span ⟨fun u g => ?_, fun k g => ?_⟩, fun _ => rfl⟩
  · change nodeFn e₁ e₂ (unip u * g) * φ.1 (unip u * g) = nodeFn e₁ e₂ g * φ.1 g
    rw [hI.1]
    obtain ⟨v, m, k, c, hc, rfl⟩ := exists_iw g
    rw [← mul_assoc, ← mul_assoc, ← D.unip_add', GlobalTheory.T.node_function_levi_decomposition e₁ e₂ h₁ h₂ _ _ _ _ hc,
      GlobalTheory.T.node_function_levi_decomposition e₁ e₂ h₁ h₂ _ _ _ _ hc]
  · obtain ⟨p, hp⟩ := nodeFn_slice h₁ h₂ k g
    obtain ⟨n, ψ₁, ψ₂, u₁, u₂, hs⟩ := tensor_pair_finite_sum (hI.2 k g)
    choose a ha hae using fun i => carries_translate s₁ s₁' c₁ p.1 (u₁ i)
    choose b hb hbe using fun i => carries_translate s₂ s₂' c₂ p.2 (u₂ i)
    convert A.sum_mem ha hb using 1
    funext m
    have hm : φ.1 (lev (Ad E) r s m * cf (r + s) k g) = ∑ i, (ψ₁ i).1 m.1 * (ψ₂ i).1 m.2 := congrFun hs m
    change nodeFn e₁ e₂ (lev (Ad E) r s m * cf (r + s) k g) * φ.1 (lev (Ad E) r s m * cf (r + s) k g) = _
    rw [hm, hp, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hae, hbe]
    ring

end GlobalTheory.CompanionTheory.LimV.NodeCarry
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CarriesInducedNodeStatement
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.carries_induced_node : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ} (e₁ : GA E r → ℂ) (e₂ : GA E s → ℂ) (U₁ U₁' : Submodule ℂ (Sm E r)) (U₂ U₂' : Submodule ℂ (Sm E s)), FlatFn e₁ → FlatFn e₂ → FinStable U₁ → FinStable U₁' → FinStable U₂ → FinStable U₂' → Carries e₁ U₁ U₁' → Carries e₂ U₂ U₂' → Carries (nodeFn e₁ e₂) (indSpan U₁ U₂) (indSpan U₁' U₂') := by
  first | exact @GlobalTheory.CompanionTheory.LimV.NodeCarry.carries_nodeFn | exact GlobalTheory.CompanionTheory.LimV.NodeCarry.carries_nodeFn | (intros; apply GlobalTheory.CompanionTheory.LimV.NodeCarry.carries_nodeFn <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TamagawaFourierIntegrable
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TamagawaFourierIntegrable
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.NoFrame

theorem pair_abs {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) [SFinite μ]
    (ν : Measure Y) [SFinite ν] (k : X → Y → ℂ) (e : X → X → ℂ)
    (hk : Measurable (Function.uncurry k)) (he : Measurable (Function.uncurry e))
    (hkn : ∀ v y, ‖k v y‖ = 1) (hen : ∀ v z, ‖e v z‖ = 1)
    (φ : Y → ℂ) (hφ : Integrable φ ν) (hJ : Integrable (fun v => ∫ y, φ y * k v y ∂ν) μ)
    (Φ : X → ℂ) (hΦ : Integrable Φ μ) (H : X → ℂ) (hHi : Integrable H μ)
    (hH : ∀ v, H v = ∫ z, Φ z * e v z ∂μ) (hinv : ∀ y, ∫ v, H v * k v y ∂μ = 0) :
    ∫ z, (∫ v, (∫ y, φ y * k v y ∂ν) * e v z ∂μ) * Φ z ∂μ = 0 := by
  have h1 : Integrable (Function.uncurry fun (z v : X) =>
      (∫ y, φ y * k v y ∂ν) * e v z * Φ z) (μ.prod μ) := by
    refine Integrable.mono (hΦ.mul_prod hJ) ?_ ?_
    · have hm1 : AEStronglyMeasurable (fun p : X × X => ∫ y, φ y * k p.2 y ∂ν) (μ.prod μ) :=
        hJ.aestronglyMeasurable.comp_snd
      have hm2 : AEStronglyMeasurable (fun p : X × X => e p.2 p.1) (μ.prod μ) :=
        (he.comp measurable_swap).aestronglyMeasurable
      have hm3 : AEStronglyMeasurable (fun p : X × X => Φ p.1) (μ.prod μ) :=
        hΦ.aestronglyMeasurable.comp_fst
      exact (hm1.mul hm2).mul hm3
    · refine Filter.Eventually.of_forall ?_
      rintro ⟨z, v⟩
      simp only [Function.uncurry_apply_pair, norm_mul, hen, mul_one]
      exact le_of_eq (mul_comm _ _)
  have h2 : Integrable (Function.uncurry fun (v : X) (y : Y) => φ y * k v y * H v) (μ.prod ν) := by
    refine Integrable.mono (hHi.mul_prod hφ) ?_ ?_
    · have hm1 : AEStronglyMeasurable (fun p : X × Y => φ p.2) (μ.prod ν) :=
        hφ.aestronglyMeasurable.comp_snd
      have hm2 : AEStronglyMeasurable (fun p : X × Y => k p.1 p.2) (μ.prod ν) :=
        hk.aestronglyMeasurable
      have hm3 : AEStronglyMeasurable (fun p : X × Y => H p.1) (μ.prod ν) :=
        hHi.aestronglyMeasurable.comp_fst
      exact (hm1.mul hm2).mul hm3
    · refine Filter.Eventually.of_forall ?_
      rintro ⟨v, y⟩
      simp only [Function.uncurry_apply_pair, norm_mul, hkn, mul_one]
      exact le_of_eq (mul_comm _ _)
  calc ∫ z, (∫ v, (∫ y, φ y * k v y ∂ν) * e v z ∂μ) * Φ z ∂μ
      = ∫ z, ∫ v, (∫ y, φ y * k v y ∂ν) * e v z * Φ z ∂μ ∂μ := by
        congr 1; funext z
        exact (integral_mul_const (Φ z) _).symm
    _ = ∫ v, ∫ z, (∫ y, φ y * k v y ∂ν) * e v z * Φ z ∂μ ∂μ := integral_integral_swap h1
    _ = ∫ v, (∫ y, φ y * k v y ∂ν) * H v ∂μ := by
        congr 1; funext v
        rw [hH v, ← integral_const_mul]
        congr 1; funext z; ring
    _ = ∫ v, ∫ y, φ y * k v y * H v ∂ν ∂μ := by
        congr 1; funext v
        exact (integral_mul_const (H v) _).symm
    _ = ∫ y, ∫ v, φ y * k v y * H v ∂μ ∂ν := integral_integral_swap h2
    _ = ∫ y, φ y * ∫ v, H v * k v y ∂μ ∂ν := by
        congr 1; funext y
        rw [← integral_const_mul]
        congr 1; funext v; ring
    _ = 0 := by simp [hinv]

theorem haar_facts {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddHaarMeasure] :
    SFinite μ ∧ μ.IsNegInvariant :=
  ⟨inferInstance, inferInstance⟩

theorem pair_ring {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [SecondCountableTopology R]
    {κ : Type} [Fintype κ] [MeasurableSpace (κ → R)] [BorelSpace (κ → R)] (μ : Measure (κ → R)) [SFinite μ]
    [μ.IsNegInvariant] (ψ : AddChar R ℂ) (hc : Continuous ψ) (hn : ∀ x, ‖ψ x‖ = 1)
    {Y : Type} [MeasurableSpace Y] (ν : Measure Y) [SFinite ν] (φ : Y → ℂ) (g : Y → κ → R)
    (hφ : Integrable φ ν) (hg : Measurable g)
    (hJ : Integrable (fun v : κ → R => ∫ y, φ y * ψ (v ⬝ᵥ g y) ∂ν) μ)
    (Φ : (κ → R) → ℂ) (hΦi : Integrable Φ μ)
    (hHi : Integrable (fun w : κ → R => ∫ z, Φ z * ψ (z ⬝ᵥ w) ∂μ) μ)
    (hinv : ∀ x, ∫ y, (∫ z, Φ z * ψ (z ⬝ᵥ y) ∂μ) * ψ (y ⬝ᵥ x) ∂μ = Φ (-x))
    (h0 : ∀ y, Φ (g y) = 0) :
    ∫ z, (∫ v, (∫ y, φ y * ψ (v ⬝ᵥ g y) ∂ν) * ψ (-(v ⬝ᵥ z)) ∂μ) * Φ z ∂μ = 0 := by
  have hdot : Continuous (fun p : (κ → R) × (κ → R) => p.1 ⬝ᵥ p.2) :=
    continuous_fst.dotProduct continuous_snd
  have hk : Measurable (Function.uncurry fun (v : κ → R) (y : Y) => ψ (v ⬝ᵥ g y)) := by
    have hm : Measurable (fun p : (κ → R) × (κ → R) => ψ (p.1 ⬝ᵥ p.2)) :=
      (hc.comp hdot).measurable
    exact hm.comp (measurable_fst.prodMk (hg.comp measurable_snd))
  have he : Measurable (Function.uncurry fun (v z : κ → R) => ψ (-(v ⬝ᵥ z))) :=
    (hc.comp hdot.neg).measurable
  have hHi' : Integrable (fun w : κ → R => ∫ z, Φ z * ψ (-(w ⬝ᵥ z)) ∂μ) μ := by
    refine hHi.comp_neg.congr (Filter.Eventually.of_forall fun w => ?_)
    simp only [dotProduct_neg]
    congr 1; funext z
    rw [dotProduct_comm]
  have hinv' : ∀ y, ∫ v, (∫ z, Φ z * ψ (-(v ⬝ᵥ z)) ∂μ) * ψ (v ⬝ᵥ g y) ∂μ = 0 := by
    intro y
    have h1 := hinv (-(g y))
    rw [neg_neg, h0 y] at h1
    refine (integral_neg_eq_self
      (fun v => (∫ z, Φ z * ψ (-(v ⬝ᵥ z)) ∂μ) * ψ (v ⬝ᵥ g y)) μ).symm.trans (Eq.trans ?_ h1)
    congr 1; funext v
    simp only [neg_dotProduct, neg_neg, dotProduct_neg]
    congr 1; congr 1; funext z
    rw [dotProduct_comm]
  exact pair_abs μ ν (fun v y => ψ (v ⬝ᵥ g y)) (fun v z => ψ (-(v ⬝ᵥ z))) hk he
    (fun v y => hn _) (fun v z => hn _) φ hφ hJ Φ hΦi _ hHi' (fun v => rfl) hinv'

theorem pair_vanish : ∀ (F : Type) [Field F] [NumberField F], NumberField.IsTotallyReal F → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ (κ : Type) [Fintype κ] [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)), GlobalTheory.SWLit.IsTamagawa F κ μ → ∀ (Y : Type) [MeasurableSpace Y] (ν : Measure Y) [SFinite ν] (φ : Y → ℂ) (g : Y → κ → AF F), Integrable φ ν → Measurable g → Integrable (fun v : κ → AF F => ∫ y, φ y * ψ (v ⬝ᵥ g y) ∂ν) μ → ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, (∀ y, Φ (g y) = 0) → ∫ z, (∫ v, (∫ y, φ y * ψ (v ⬝ᵥ g y) ∂ν) * ψ (-(v ⬝ᵥ z)) ∂μ) * Φ z ∂μ = 0 := by
  intro F _ _ hF ψ hψ κ _ _ _ μ hμ Y _ ν _ φ g hφ hg hJ Φ hΦ h0
  have hH : μ.IsAddHaarMeasure := hμ.1
  obtain ⟨hS, hN⟩ := haar_facts μ
  have hc : Continuous ψ := hψ.1
  have hn : ∀ x, ‖ψ x‖ = 1 := hψ.2.1
  obtain ⟨-, -, hint⟩ := GlobalTheory.SplitSvN.schA_facts hF hΦ
  have hinv := GlobalTheory.TamFourier.fourier_inversion_tamagawa F hF ψ hψ κ μ hμ Φ hΦ
  have hHi : Integrable (fun w => ∫ z, Φ z * ψ (z ⬝ᵥ w) ∂μ) μ := by
    by_contra hni
    have hzero : ∀ x, Φ x = 0 := by
      intro x
      have h1 := hinv (-x)
      rw [neg_neg] at h1
      rw [← h1]
      apply integral_undef
      intro hi
      apply hni
      exact integrable_of_mul_unimodular μ (fun y => ∫ z, Φ z * ψ (z ⬝ᵥ y) ∂μ)
        (fun y => ψ (y ⬝ᵥ -x)) hi
        ((hc.comp (continuous_id.dotProduct continuous_const)).aestronglyMeasurable) (fun y => hn _)
    apply hni
    have hfun : (fun w => ∫ z, Φ z * ψ (z ⬝ᵥ w) ∂μ) = fun _ => (0 : ℂ) := by
      funext w; simp [hzero]
    rw [hfun]
    exact integrable_zero _ _ _
  exact pair_ring μ ψ hc hn ν φ g hφ hg hJ Φ (hint μ hH) hHi hinv h0

end GlobalTheory.CompanionTheory.WeilSiegel.NoFrame
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TamagawaFourierIntegrableStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tamagawa_fourier_integrable : ∀ (F : Type) [Field F] [NumberField F], NumberField.IsTotallyReal F → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ (κ : Type) [Fintype κ] [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)), GlobalTheory.SWLit.IsTamagawa F κ μ → ∀ (Y : Type) [MeasurableSpace Y] (ν : Measure Y) [SFinite ν] (φ : Y → ℂ) (g : Y → κ → AF F), Integrable φ ν → Measurable g → Integrable (fun v : κ → AF F => ∫ y, φ y * ψ (v ⬝ᵥ g y) ∂ν) μ → ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, (∀ y, Φ (g y) = 0) → ∫ z, (∫ v, (∫ y, φ y * ψ (v ⬝ᵥ g y) ∂ν) * ψ (-(v ⬝ᵥ z)) ∂μ) * Φ z ∂μ = 0 := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.pair_vanish | exact GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.pair_vanish | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.pair_vanish <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairSecondStep
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairSecondStep
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation
open GlobalTheory.CompanionTheory.EGlue

namespace GlobalTheory.CompanionTheory.EGlue.PairT₂

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem sl₂_eq {F : H E a b → ℂ} {m : GA E a} {φ : Sm E b} (h : φ.1 = fun x => F (m, x)) : sl₂ F m = φ := by
  have hx : ∃ φ : Sm E b, φ.1 = fun x => F (m, x) := ⟨φ, h⟩
  unfold sl₂
  rw [dite_eq_left hx]
  exact Subtype.ext (hx.choose_spec.trans h.symm)

variable {U₁ : Submodule ℂ (Sm E a)} {U₂ : Submodule ℂ (Sm E b)} {F G : H E a b → ℂ}

theorem sl₂_val (hS : PairSlices) (hF : F ∈ pairSpace U₁ U₂) (m : GA E a) (x : GA E b) :
    (sl₂ F m).1 x = F (m, x) :=
  congrFun ((hS E a b U₁ U₂ F hF).2 m).2 x

theorem sl₂_mem (hS : PairSlices) (hF : F ∈ pairSpace U₁ U₂) (m : GA E a) : sl₂ F m ∈ U₂ :=
  ((hS E a b U₁ U₂ F hF).2 m).1

theorem ap₂_add (hS : PairSlices) (T : Sm E b →ₗ[ℂ] Sm E b) (hF : F ∈ pairSpace U₁ U₂)
    (hG : G ∈ pairSpace U₁ U₂) : ap₂ T (F + G) = ap₂ T F + ap₂ T G := by
  funext x
  have e : sl₂ (F + G) x.1 = sl₂ F x.1 + sl₂ G x.1 := sl₂_eq (by
    funext y
    exact congrArg₂ (· + ·) (sl₂_val hS hF x.1 y) (sl₂_val hS hG x.1 y))
  change (T (sl₂ (F + G) x.1)).1 x.2 = _
  rw [e, map_add (f := _)]
  rfl

theorem ap₂_smul (hS : PairSlices) (T : Sm E b →ₗ[ℂ] Sm E b) (c : ℂ) (hF : F ∈ pairSpace U₁ U₂) :
    ap₂ T (c • F) = c • ap₂ T F := by
  funext x
  have e : sl₂ (c • F) x.1 = c • sl₂ F x.1 := sl₂_eq (by
    funext y
    exact congrArg (c * ·) (sl₂_val hS hF x.1 y))
  change (T (sl₂ (c • F) x.1)).1 x.2 = _
  rw [e, map_smul]
  rfl

theorem ap₂_zero (hS : PairSlices) (T : Sm E b →ₗ[ℂ] Sm E b) (U₁ : Submodule ℂ (Sm E a))
    (U₂ : Submodule ℂ (Sm E b)) : ap₂ T (0 : H E a b → ℂ) = 0 := by
  have h := ap₂_smul hS T (0 : ℂ) (Submodule.zero_mem (pairSpace U₁ U₂))
  simpa using h

theorem ap₂_sum (hS : PairSlices) (T : Sm E b →ₗ[ℂ] Sm E b) {α : Type} (s : Finset α)
    (f : α → H E a b → ℂ) (hf : ∀ j ∈ s, f j ∈ pairSpace U₁ U₂) :
    ap₂ T (∑ j ∈ s, f j) = ∑ j ∈ s, ap₂ T (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ap₂_zero hS T U₁ U₂
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj,
      ap₂_add hS T (hf j (Finset.mem_insert_self j s))
        (Submodule.sum_mem _ fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

theorem ap₂_rt (hS : PairSlices) (T : Sm E b →ₗ[ℂ] Sm E b)
    (hT : ∀ o, ∀ ψ ∈ U₂, T (act o ψ) = act o (T ψ)) (hF : F ∈ pairSpace U₁ U₂) (g : Hf E a b)
    (x : H E a b) : ap₂ T (fun y => F (y * finH g)) x = ap₂ T F (x * finH g) := by
  have e : sl₂ (fun y => F (y * finH g)) x.1 = act (.fin g.2) (sl₂ F (x.1 * finGL E a g.1)) :=
    sl₂_eq (by
      funext y
      exact (sl₂_val hS hF _ _).trans rfl)
  change (T (sl₂ _ x.1)).1 x.2 = (T (sl₂ F (x.1 * finGL E a g.1))).1 (x.2 * finGL E b g.2)
  rw [e, hT _ _ (sl₂_mem hS hF _)]
  rfl

theorem rt_mem (hU : _root_.GlobalTheory.CuspRep.IsStable U₂) (hF : F ∈ pairSpace U₁ U₂) (g : Hf E a b) :
    (fun y => F (y * finH g)) ∈ pairSpace (⊤ : Submodule ℂ (Sm E a)) U₂ := by
  induction hF using Submodule.span_induction with
  | mem F h =>
    obtain ⟨φ₁, -, φ₂, h₂, rfl⟩ := h
    exact Submodule.subset_span ⟨act (.fin g.1) φ₁, trivial, act (.fin g.2) φ₂, hU _ _ h₂, rfl⟩
  | zero => exact Submodule.zero_mem _
  | add F G _ _ h₁ h₂ => exact Submodule.add_mem _ h₁ h₂
  | smul r F _ h => exact Submodule.smul_mem _ r h

theorem ap₂_mem (hS : PairSlices) {U₂' : Submodule ℂ (Sm E b)} (T : Sm E b →ₗ[ℂ] Sm E b)
    (hTU : ∀ ψ ∈ U₂, T ψ ∈ U₂') (hF : F ∈ pairSpace U₁ U₂) : ap₂ T F ∈ pairSpace U₁ U₂' := by
  induction hF using Submodule.span_induction with
  | mem F h =>
    obtain ⟨φ₁, h₁, φ₂, h₂, rfl⟩ := h
    refine Submodule.subset_span ⟨φ₁, h₁, T φ₂, hTU _ h₂, ?_⟩
    funext x
    have e : sl₂ (fun x : H E a b => φ₁.1 x.1 * φ₂.1 x.2) x.1 = φ₁.1 x.1 • φ₂ := sl₂_eq rfl
    change (T (sl₂ _ x.1)).1 x.2 = _
    rw [e, map_smul]
    rfl
  | zero =>
    rw [ap₂_zero hS T U₁ U₂]
    exact Submodule.zero_mem _
  | add F G hF hG h₁ h₂ =>
    rw [ap₂_add hS T hF hG]
    exact Submodule.add_mem _ h₁ h₂
  | smul r F hF h =>
    rw [ap₂_smul hS T r hF]
    exact Submodule.smul_mem _ r h

theorem ap₂_type (hS : PairSlices) {K₁ : Subgroup (GL (Fin a) (Af E))} {K₂ : Subgroup (GL (Fin b) (Af E))}
    {W₁ : Submodule ℂ (Kinf E a → ℂ)} {W₂ : Submodule ℂ (Kinf E b → ℂ)} (fd₁ : FiniteDimensional ℂ W₁)
    (fd₂ : FiniteDimensional ℂ W₂) (T : Sm E b →ₗ[ℂ] Sm E b)
    (hT : ∀ o, ∀ ψ ∈ U₂, T (act o ψ) = act o (T ψ)) (hF : F ∈ pairSpace U₁ U₂)
    (hty : TypeH K₁ K₂ W₁ W₂ F) : TypeH K₁ K₂ W₁ W₂ (ap₂ T F) := by
  refine ⟨fun u₁ h₁ u₂ h₂ x => ?_, fun x => ?_⟩
  · have e : (fun y => F (y * finH ((u₁, u₂) : Hf E a b))) = F := funext (hty.1 u₁ h₁ u₂ h₂)
    have h := ap₂_rt hS T hT hF (u₁, u₂) x
    rw [e] at h
    exact h.symm
  · haveI : FiniteDimensional ℂ (Submodule.span ℂ {f : Kinf E a × Kinf E b → ℂ |
        ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, f = fun k => w₁ k.1 * w₂ k.2}) :=
      GlobalTheory.CompanionTheory.LimV.finiteDimensional_prodSpan_of_fd W₁ W₂ fd₁ fd₂
    let ev : GA E b → Sm E b →ₗ[ℂ] ℂ := fun y =>
      (LinearMap.proj y : (GA E b → ℂ) →ₗ[ℂ] ℂ) ∘ₗ (Sm E b).subtype
    have h := GlobalTheory.CompanionTheory.LimV.BlockTy.mem_of_separating
      (Submodule.span ℂ {f : Kinf E a × Kinf E b → ℂ | ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, f = fun k => w₁ k.1 * w₂ k.2})
      (fun k : Kinf E a × Kinf E b =>
        act (.cpt k.2) (sl₂ F (x.1 * infGL E a (Unitary.toUnits k.1)))) ev
      (fun m hm => Subtype.ext (funext hm)) (ev x.2 ∘ₗ T) (fun y => by
        have e : (fun k : Kinf E a × Kinf E b =>
            ev y (act (.cpt k.2) (sl₂ F (x.1 * infGL E a (Unitary.toUnits k.1))))) =
            fun k => F ((x.1, y) * (infGL E a (Unitary.toUnits k.1), infGL E b (Unitary.toUnits k.2))) :=
          funext fun k => (sl₂_val hS hF _ _).trans rfl
        rw [e]
        exact hty.2 (x.1, y))
    convert h using 2 with k
    have e := hT (.cpt k.2) _ (sl₂_mem hS hF (x.1 * infGL E a (Unitary.toUnits k.1)))
    change _ = (T (act (.cpt k.2) (sl₂ F (x.1 * infGL E a (Unitary.toUnits k.1))))).1 x.2
    rw [e]
    rfl

theorem ap₂_hecke (hS : PairSlices) {ι : Type} [Fintype ι] (hU : _root_.GlobalTheory.CuspRep.IsStable U₂) (T : Sm E b →ₗ[ℂ] Sm E b)
    (hT : ∀ o, ∀ ψ ∈ U₂, T (act o ψ) = act o (T ψ)) {f : ι → H E a b → ℂ}
    (hf : ∀ i, f i ∈ pairSpace U₁ U₂) (h : HeckeM E a b ι) (c : ℂ) (hh : heckeAct h f = c • f) :
    heckeAct h (fun i => ap₂ T (f i)) = c • fun i => ap₂ T (f i) := by
  funext i x
  have e : heckeAct h f i = ∑ j, ∑ g ∈ (h i j).support, (h i j g) • fun y => f j (y * finH g) := by
    funext y
    simp [heckeAct, Finsupp.sum, Finset.sum_apply]
  have e₁ : ap₂ T (heckeAct h f i) = c • ap₂ T (f i) := by
    rw [hh]
    exact ap₂_smul hS T c (hf i)
  have e₂ : ap₂ T (heckeAct h f i) x = ∑ j, ∑ g ∈ (h i j).support, h i j g * ap₂ T (f j) (x * finH g) := by
    rw [e, ap₂_sum (U₁ := ⊤) (U₂ := U₂) hS T _ _ fun j _ =>
      Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (rt_mem hU (hf j) g), Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ap₂_sum (U₁ := ⊤) (U₂ := U₂) hS T _ _ fun g _ => Submodule.smul_mem _ _ (rt_mem hU (hf j) g),
      Finset.sum_apply]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [ap₂_smul (U₁ := ⊤) (U₂ := U₂) hS T _ (rt_mem hU (hf j) g), Pi.smul_apply, smul_eq_mul,
      ap₂_rt hS T hT (hf j) g x]
  have e₃ : heckeAct h (fun i => ap₂ T (f i)) i x =
      ∑ j, ∑ g ∈ (h i j).support, h i j g * ap₂ T (f j) (x * finH g) := rfl
  rw [e₃, ← e₂, e₁]
  rfl

end GlobalTheory.CompanionTheory.EGlue.PairT₂

namespace GlobalTheory.CompanionTheory.EGlue

theorem pairStep₂ : PairSlices → PairStep₂ := by
  intro hS E _ _ _ a b ι _ K₁ K₂ W₁ W₂ U₁ U₂ U₂' T f fd₁ fd₂ hU hT hTU hf hty hne
  refine ⟨?_, fun i => PairT₂.ap₂_mem hS T hTU (hf i), fun i => PairT₂.ap₂_type hS fd₁ fd₂ T hT (hf i) (hty i),
    fun h c hh => PairT₂.ap₂_hecke hS hU T hT hf h c hh⟩
  obtain ⟨i, m, φ, hφ, hTφ⟩ := hne
  intro h0
  apply hTφ
  refine Subtype.ext (funext fun y => ?_)
  have e : sl₂ (f i) m = φ := PairT₂.sl₂_eq hφ
  have h1 : ap₂ T (f i) (m, y) = 0 := congrFun (congrFun h0 i) (m, y)
  change (T (sl₂ (f i) m)).1 y = 0 at h1
  rw [e] at h1
  exact h1

end GlobalTheory.CompanionTheory.EGlue

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairSecondStepStatement
open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_second_step : GlobalTheory.CompanionTheory.EGlue.PairSlices → GlobalTheory.CompanionTheory.EGlue.PairStep₂ := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.pairStep₂ | exact GlobalTheory.CompanionTheory.EGlue.pairStep₂ | (intros; apply GlobalTheory.CompanionTheory.EGlue.pairStep₂ <;> assumption)
end
end
