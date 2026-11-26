module

public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsArchEquivEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Foundations.AnalyticOnNhdTsumNpow
noncomputable section

namespace GlobalTheory.Eis

open scoped NNReal
open Filter Topology Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Cont

section Sums

variable {G : Type} [Group G] (P Γ : Subgroup G)

abbrev Cosets : Type := Quot (P.subgroupOf Γ)

def term {X : Type} (Φ : G → X) (g : G) (q : Cosets P Γ) : X := Φ ((q.out : Γ) * g)

def cosetSum (Φ : G → ℂ) (g : G) : ℂ := ∑' q, term P Γ Φ g q

def CosetConv (Φ : G → ℂ) (g : G) : Prop := Summable fun q => ‖term P Γ Φ g q‖

def rmulEquiv (γ : Γ) : Cosets P Γ ≃ Cosets P Γ :=
  ⟨rmul _ γ, rmul _ γ⁻¹, fun q => by rw [← rmul_mul, mul_inv_cancel, rmul_one],
    fun q => by rw [← rmul_mul, inv_mul_cancel, rmul_one]⟩

variable {P Γ} {X : Type} {Φ Ψ : G → ℂ} {g : G}

theorem term_mk {Φ : G → X} (h : LeftInv (P ⊓ Γ) Φ) (g : G) (γ : Γ) : term P Γ Φ g (mk _ γ) = Φ (γ * g) :=
  LeftInv.descend_mk (Γ := P.subgroupOf Γ) (φ := fun x : Γ => Φ (x * g))
    (fun δ hδ x => (congrArg Φ (mul_assoc _ _ _)).trans (h δ ⟨hδ, δ.2⟩ _)) γ

theorem term_mul_left {Φ : G → X} (h : LeftInv (P ⊓ Γ) Φ) (γ : Γ) (g : G) (q : Cosets P Γ) :
    term P Γ Φ (γ * g) q = term P Γ Φ g (rmulEquiv P Γ γ q) :=
  Quotient.inductionOn q fun x => (term_mk h _ x).trans (((term_mk h g (x * γ)).trans (by simp [mul_assoc])).symm)

theorem leftInv_cosetSum (h : LeftInv (P ⊓ Γ) Φ) : LeftInv Γ (cosetSum P Γ Φ) := fun γ hγ g =>
  (tsum_congr (term_mul_left h ⟨γ, hγ⟩ g)).trans ((rmulEquiv P Γ ⟨γ, hγ⟩).tsum_eq _)

theorem cosetConv_mul_left (h : LeftInv (P ⊓ Γ) Φ) {γ : G} (hγ : γ ∈ Γ) : CosetConv P Γ Φ (γ * g) ↔ CosetConv P Γ Φ g := by
  rw [CosetConv, CosetConv, ← (rmulEquiv P Γ ⟨γ, hγ⟩).summable_iff (f := fun q => ‖term P Γ Φ g q‖)]
  exact summable_congr fun q => congrArg norm (term_mul_left h ⟨γ, hγ⟩ g q)

theorem cosetSum_mul_right (Φ : G → ℂ) (k g : G) : cosetSum P Γ (fun x => Φ (x * k)) g = cosetSum P Γ Φ (g * k) := by
  simp only [cosetSum, term, mul_assoc]

theorem cosetSum_eq_tsum (h : LeftInv (P ⊓ Γ) Φ) {ι : Type} {r : ι → Γ}
    (hr : Function.Bijective fun i => mk (P.subgroupOf Γ) (r i)) (g : G) : cosetSum P Γ Φ g = ∑' i, Φ (r i * g) :=
  ((Equiv.ofBijective _ hr).tsum_eq _).symm.trans (tsum_congr fun i => term_mk h g (r i))

theorem cosetConv_iff (h : LeftInv (P ⊓ Γ) Φ) {ι : Type} {r : ι → Γ}
    (hr : Function.Bijective fun i => mk (P.subgroupOf Γ) (r i)) : CosetConv P Γ Φ g ↔ Summable fun i => ‖Φ (r i * g)‖ :=
  (Equiv.ofBijective _ hr).summable_iff.symm.trans (summable_congr fun i => congrArg norm (term_mk h g (r i)))

theorem CosetConv.hasSum (h : CosetConv P Γ Φ g) : HasSum (term P Γ Φ g) (cosetSum P Γ Φ g) := h.of_norm.hasSum

theorem CosetConv.of_norm_le (h : CosetConv P Γ Ψ g) {C : ℝ} (e : ∀ x, ‖Φ x‖ ≤ C * ‖Ψ x‖) : CosetConv P Γ Φ g :=
  .of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => e _) (h.mul_left C)

theorem CosetConv.add (h : CosetConv P Γ Φ g) (h' : CosetConv P Γ Ψ g) : CosetConv P Γ (Φ + Ψ) g :=
  .of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => norm_add_le _ _) (Summable.add h h')

theorem CosetConv.smul (h : CosetConv P Γ Φ g) (c : ℂ) : CosetConv P Γ (c • Φ) g :=
  h.of_norm_le fun x => (norm_smul c (Φ x)).le

theorem cosetSum_add (h : CosetConv P Γ Φ g) (h' : CosetConv P Γ Ψ g) :
    cosetSum P Γ (Φ + Ψ) g = cosetSum P Γ Φ g + cosetSum P Γ Ψ g := (h.hasSum.add h'.hasSum).tsum_eq

theorem cosetSum_smul (c : ℂ) (Φ : G → ℂ) (g : G) : cosetSum P Γ (c • Φ) g = c * cosetSum P Γ Φ g := tsum_mul_left

theorem cosetSum_of_le (e : Γ ≤ P) (h : LeftInv (P ⊓ Γ) Φ) (g : G) : CosetConv P Γ Φ g ∧ cosetSum P Γ Φ g = Φ g := by
  have hr : Function.Bijective fun _ : Unit => mk (P.subgroupOf Γ) 1 := ⟨fun _ _ _ => rfl, fun q =>
    Quotient.inductionOn q fun x => ⟨(), mk_eq_iff.2 ⟨⟨x, e x.2⟩, mul_one _⟩⟩⟩
  exact ⟨(cosetConv_iff h hr).2 .of_finite, by simpa using cosetSum_eq_tsum h hr g⟩

theorem cosetSum_indicator (g : G) : LeftInv (P ⊓ Γ) (indicator ((P ⊓ Γ : Subgroup G) : Set G) (1 : G → ℂ)) ∧
    CosetConv P Γ (indicator ((P ⊓ Γ : Subgroup G) : Set G) 1) g ∧
    cosetSum P Γ (indicator ((P ⊓ Γ : Subgroup G) : Set G) 1) g = indicator (Γ : Set G) 1 g := by
  have h : LeftInv (P ⊓ Γ) (indicator ((P ⊓ Γ : Subgroup G) : Set G) (1 : G → ℂ)) := fun γ hγ x => by
    classical simp only [indicator, SetLike.mem_coe, Subgroup.mul_mem_cancel_left _ hγ, Pi.one_apply]
  by_cases hg : g ∈ Γ
  · have h0 : ∀ q ≠ mk (P.subgroupOf Γ) 1, term P Γ (indicator ((P ⊓ Γ : Subgroup G) : Set G) (1 : G → ℂ)) 1 q = 0 :=
      fun q => Quotient.inductionOn q fun x hx => (term_mk h 1 x).trans (indicator_of_notMem
        (fun e => hx (mk_eq_iff.2 ⟨⟨x, Subgroup.mem_subgroupOf.2 (by simpa using e.1)⟩, mul_one _⟩).symm) _)
    rw [← mul_one g, cosetConv_mul_left h hg, leftInv_cosetSum h g hg, mul_one, indicator_of_mem hg]
    refine ⟨h, summable_of_ne_finset_zero (s := {mk _ 1}) fun q hq => by rw [h0 q (by simpa using hq), norm_zero], ?_⟩
    rw [cosetSum, tsum_eq_single _ h0, term_mk h]
    exact indicator_of_mem (by simp) _
  · have h0 : term P Γ (indicator ((P ⊓ Γ : Subgroup G) : Set G) (1 : G → ℂ)) g = 0 := funext fun q =>
      indicator_of_notMem (fun (e : ((q.out : Γ) : G) * g ∈ ((P ⊓ Γ : Subgroup G) : Set G)) =>
        hg ((Γ.mul_mem_cancel_left q.out.2).1 (show ((q.out : Γ) : G) * g ∈ P ∧ ((q.out : Γ) : G) * g ∈ Γ from e).2)) _
    rw [CosetConv, cosetSum, h0, indicator_of_notMem hg]
    exact ⟨h, by simpa using summable_zero, tsum_zero⟩

end Sums

theorem rpow_le_add {x a b t : ℝ} (hx : 0 < x) (h1 : a ≤ t) (h2 : t ≤ b) : x ^ t ≤ x ^ a + x ^ b := by
  rcases le_total x 1 with h | h
  · exact (Real.rpow_le_rpow_of_exponent_ge hx h h1).trans (le_add_of_nonneg_right (by positivity))
  · exact (Real.rpow_le_rpow_of_exponent_le h h2).trans (le_add_of_nonneg_left (by positivity))

theorem differentiable_npow {r : ℝ≥0} (hr : 0 < r) : Differentiable ℂ (npow r) := by
  rw [funext (npow_eq_exp hr)]; fun_prop

theorem analyticOnNhd_tsum_npow {ι : Type} {f : ι → ℂ} {a : ι → ℝ≥0} (ha : ∀ i, 0 < a i) {σ : ℝ} {s₀ : ℂ}
    (h : ∀ s : ℂ, σ < s.re → Summable fun i => ‖f i * npow (a i) (s - s₀)‖) :
    AnalyticOnNhd ℂ (fun s => ∑' i, f i * npow (a i) (s - s₀)) (rightOf σ) := fun s hs => by
  obtain ⟨τ, h1, h2⟩ := exists_between (mem_rightOf.1 hs)
  have ho : IsOpen {z : ℂ | τ < z.re ∧ z.re < s.re + 1} :=
    (isOpen_rightOf τ).inter (isOpen_lt Complex.continuous_re continuous_const)
  refine (Complex.differentiableOn_tsum_of_summable_norm ((h τ h1).add (h (s.re + 1 : ℝ) (by simp; linarith)))
    (fun i => ?_) ho fun i z hz => ?_).analyticAt (ho.mem_nhds ⟨h2, lt_add_one _⟩)
  · exact (((differentiable_npow (ha i)).comp (differentiable_id.sub_const s₀)).const_mul _).differentiableOn
  · simp only [norm_mul, norm_npow (ha i), ← mul_add, Complex.sub_re, Complex.ofReal_re]
    exact mul_le_mul_of_nonneg_left (rpow_le_add (ha i) (by linarith [hz.1]) (by linarith [hz.2])) (norm_nonneg _)

section Family

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {P Γ K : Subgroup G} {δ : P →* ℝ≥0}
  {χ : P →* Circle} {ρ σ : ℝ} {Φ : ℂ → G → ℂ} (hI : IsIwasawa δ K) (hK : IsCompact (K : Set G))
  (hc : ContinuousOn (fun x : ℂ × G => Φ x.1 x.2) (rightOf σ ×ˢ univ)) (hl : ∀ s ∈ rightOf σ, IndLaw δ χ (s + ρ) (Φ s))
  (hs : ∀ τ, σ < τ → Summable fun q => ((term P Γ (iwAbs δ K) 1 q : ℝ≥0) : ℝ) ^ (τ + ρ))
include hI hK hc hl hs

theorem exists_majorant {S : Set ℂ} {C : Set G} (hS : IsCompact S) (hσ : S ⊆ rightOf σ) (hC : IsCompact C) :
    ∃ u : Cosets P Γ → ℝ, Summable u ∧ ∀ q, ∀ s ∈ S, ∀ g ∈ C, ‖term P Γ (Φ s) g q‖ ≤ u q := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, summable_zero, fun _ _ h => h.elim⟩
  obtain ⟨a, ha, h1⟩ := hS.exists_isMinOn hne Complex.continuous_re.continuousOn
  obtain ⟨b, hb, h2⟩ := hS.exists_isMaxOn hne Complex.continuous_re.continuousOn
  obtain ⟨M, hM⟩ := (hS.prod (hK.mul hC)).exists_bound_of_continuousOn (hc.mono (prod_mono hσ (subset_univ _)))
  refine ⟨_, ((hs _ (hσ ha)).add (hs _ (hσ hb))).mul_right M, fun q s h g hg => ?_⟩
  obtain ⟨p, k, hk, e⟩ := hI.1 (q.out : Γ)
  have h3 := hM (s, k * g) ⟨h, mul_mem_mul hk hg⟩
  simp only [term, e, mul_one, hI.iwAbs_mul p hk]
  rw [mul_assoc, hl s (hσ h), norm_mul, norm_mul, Circle.norm_coe, one_mul, norm_npow (hom_pos δ p), Complex.add_re,
    Complex.ofReal_re]
  exact mul_le_mul (rpow_le_add (hom_pos δ p) (add_le_add_left (h1 h) _) (add_le_add_left (h2 h) _)) h3 (norm_nonneg _)
    (by positivity)

theorem cosetConv_of_spherical {s : ℂ} (h : σ < s.re) (g : G) : CosetConv P Γ (Φ s) g :=
  let ⟨_, hu, e⟩ := exists_majorant hI hK hc hl hs isCompact_singleton (singleton_subset_iff.2 h) (isCompact_singleton (x := g))
  .of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => e q s rfl g rfl) hu

theorem continuousOn_cosetSum [WeaklyLocallyCompactSpace G] :
    ContinuousOn (fun x : ℂ × G => cosetSum P Γ (Φ x.1) x.2) (rightOf σ ×ˢ univ) := fun x hx => by
  obtain ⟨S, hS, h1, h2⟩ := local_compact_nhds ((isOpen_rightOf σ).mem_nhds hx.1)
  obtain ⟨C, hC, h3⟩ := exists_compact_mem_nhds x.2
  obtain ⟨u, hu, e⟩ := exists_majorant hI hK hc hl hs h2 h1 hC
  refine ((continuousOn_tsum (s := S ×ˢ C) (fun q => ?_) hu fun q y hy => e q _ hy.1 _ hy.2).continuousAt
    (prod_mem_nhds hS h3)).continuousWithinAt
  exact hc.comp (f := fun y : ℂ × G => (y.1, ((q.out : Γ) : G) * y.2)) (by fun_prop) fun y hy => ⟨h1 hy.1, trivial⟩

theorem analyticOnNhd_cosetSum (hd : ∀ g, DifferentiableOn ℂ (Φ · g) (rightOf σ)) (g : G) :
    AnalyticOnNhd ℂ (fun s => cosetSum P Γ (Φ s) g) (rightOf σ) := fun s h => by
  obtain ⟨S, hS, h1, h2⟩ := local_compact_nhds ((isOpen_rightOf σ).mem_nhds h)
  obtain ⟨u, hu, e⟩ := exists_majorant hI hK hc hl hs h2 h1 (isCompact_singleton (x := g))
  exact (Complex.differentiableOn_tsum_of_summable_norm hu (fun q => (hd _).mono (interior_subset.trans h1)) isOpen_interior
    fun q z hz => e q z (interior_subset hz) g rfl).analyticAt (interior_mem_nhds.2 hS)

end Family

end GlobalTheory.Eis

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary
open scoped ENNReal Pointwise

noncomputable section

namespace GlobalTheory.Cusp

variable {G : Type} [Group G] [TopologicalSpace G] (Γ N : Subgroup G)

def Cocompact : Prop := ∃ K : Set N, IsCompact K ∧ ∀ n : N, ∃ γ ∈ Γ.subgroupOf N, γ * n ∈ K

instance discreteTopology_subgroupOf [DiscreteTopology Γ] : DiscreteTopology (Γ.subgroupOf N) :=
  .of_continuous_injective (f := fun x : Γ.subgroupOf N => (⟨x.1.1, x.2⟩ : Γ))
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
    fun _ _ h => Subtype.ext (Subtype.ext (congrArg (fun z : Γ => z.1) h))

instance secondCountable_subgroup [SecondCountableTopology G] : SecondCountableTopology N :=
  TopologicalSpace.Subtype.secondCountableTopology _

variable [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [DiscreteTopology Γ]
  [LocallyCompactSpace N]

def probMeasure : Measure (Quot (Γ.subgroupOf N)) :=
  (AutomorphicL2Unitary.quotMeasure (Γ.subgroupOf N) Measure.haar univ)⁻¹ • AutomorphicL2Unitary.quotMeasure (Γ.subgroupOf N) Measure.haar

def constTermOn (φ : G → ℂ) (x : G) : ℂ := ∫ q, φ ((q.out : N) * x) ∂probMeasure Γ N

variable {Γ N} {φ ψ : G → ℂ} {μ : Measure N} {𝓕 : Set N}


omit [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [DiscreteTopology Γ] [LocallyCompactSpace N] in
theorem leftInv_integrand (hφ : LeftInv Γ φ) (x : G) : LeftInv (Γ.subgroupOf N) fun n : N => φ (n * x) :=
  fun γ hγ n => by simp only [Subgroup.coe_mul, mul_assoc]; exact hφ _ hγ _

theorem probMeasure_eq (μ : Measure N) [μ.IsHaarMeasure] :
    probMeasure Γ N = (AutomorphicL2Unitary.quotMeasure (Γ.subgroupOf N) μ univ)⁻¹ • AutomorphicL2Unitary.quotMeasure (Γ.subgroupOf N) μ := by
  have h0 : ((Measure.haarScalarFactor μ Measure.haar : NNReal) : ℝ≥0∞) ≠ 0 :=
    ENNReal.coe_ne_zero.2 (Measure.haarScalarFactor_pos_of_isHaarMeasure μ Measure.haar).ne'
  conv_rhs => rw [Measure.isMulLeftInvariant_eq_smul μ Measure.haar]
  rw [ENNReal.smul_def, quotMeasure_smul, smul_smul, Measure.smul_apply, smul_eq_mul,
    ENNReal.mul_inv (Or.inl h0) (Or.inl ENNReal.coe_ne_top), mul_right_comm, ENNReal.inv_mul_cancel h0 ENNReal.coe_ne_top,
    one_mul, probMeasure]

theorem constTermOn_eq [μ.IsHaarMeasure] (h : IsFundamentalDomain (Γ.subgroupOf N) 𝓕 μ) (hφ : LeftInv Γ φ) (x : G) :
    constTermOn Γ N φ x = (μ.real 𝓕)⁻¹ • ∫ n in 𝓕, φ (n * x) ∂μ := by
  rw [constTermOn, probMeasure_eq μ, integral_smul_measure, quotMeasure_univ h, integral_quotMeasure h,
    ENNReal.toReal_inv, measureReal_def]
  exact congrArg _ (integral_congr_ae (.of_forall (leftInv_integrand hφ x).descend_mk))

theorem constTermOn_eq_of_measure_eq_one [μ.IsHaarMeasure] (h : IsFundamentalDomain (Γ.subgroupOf N) 𝓕 μ)
    (h1 : μ 𝓕 = 1) (hφ : LeftInv Γ φ) (x : G) : constTermOn Γ N φ x = ∫ n in 𝓕, φ (n * x) ∂μ := by
  simp [constTermOn_eq h hφ, measureReal_def, h1]

theorem constTermOn_mul_right (φ : G → ℂ) (x g : G) :
    constTermOn Γ N (fun y => φ (y * g)) x = constTermOn Γ N φ (x * g) := by
  simp only [constTermOn, mul_assoc]

theorem constTermOn_smul (c : ℂ) (φ : G → ℂ) (x : G) : constTermOn Γ N (c • φ) x = c * constTermOn Γ N φ x :=
  integral_const_mul c _

theorem constTermOn_mul_left_of_normalizer (hφ : LeftInv Γ φ) {γ : G} (hγ : γ ∈ Γ)
    (hN : ∀ n, n ∈ N ↔ γ * n * γ⁻¹ ∈ N) (x : G) : constTermOn Γ N φ (γ * x) = constTermOn Γ N φ x := by
  let e : N ≃ₜ* N :=
    { toFun := fun n => ⟨γ * n * γ⁻¹, (hN _).1 n.2⟩
      invFun := fun n => ⟨γ⁻¹ * n * γ, (hN _).2 (by simp [mul_assoc])⟩
      left_inv := fun n => by simp [mul_assoc]
      right_inv := fun n => by simp [mul_assoc]
      map_mul' := fun a b => by simp [mul_assoc]
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let m := e.toHomeomorph.toMeasurableEquiv
  have h := isFundamentalDomain_stdDom (Γ.subgroupOf N) (Measure.haar.map e)
  have hp : MeasurePreserving m Measure.haar (Measure.haar.map e) := ⟨m.measurable, rfl⟩
  have h' : IsFundamentalDomain (Γ.subgroupOf N) (m ⁻¹' stdDom (Γ.subgroupOf N)) Measure.haar :=
    h.preimage_of_equiv hp.quasiMeasurePreserving
      (e := fun δ => ⟨e.symm δ, mul_mem (mul_mem (inv_mem hγ) δ.2) hγ⟩)
      ⟨fun a b hab => Subtype.ext (e.symm.injective (congrArg Subtype.val hab)),
        fun δ => ⟨⟨e δ, mul_mem (mul_mem hγ δ.2) (inv_mem hγ)⟩, Subtype.ext (e.symm_apply_apply _)⟩⟩
      fun δ n => (map_mul e _ _).trans (congrArg (· * e n) (e.apply_symm_apply _))
  rw [constTermOn_eq h hφ, constTermOn_eq h' hφ, ← hp.setIntegral_preimage_emb m.measurableEmbedding,
    measureReal_def, measureReal_def, hp.measure_preimage h.nullMeasurableSet]
  refine congrArg _ (integral_congr_ae (.of_forall fun n => ?_))
  change φ (γ * n * γ⁻¹ * (γ * x)) = φ (n * x)
  rw [mul_assoc, inv_mul_cancel_left, mul_assoc, hφ γ hγ]

namespace Cocompact

variable (hc : Cocompact Γ N)
include hc


omit [LocallyCompactSpace N] in
theorem integrableOn [μ.IsHaarMeasure] (h : IsFundamentalDomain (Γ.subgroupOf N) 𝓕 μ) (hφ : LeftInv Γ φ)
    (hφc : Continuous φ) (x : G) : IntegrableOn (fun n : N => φ (n * x)) 𝓕 μ :=
  let ⟨K, hK, hs⟩ := hc
  GlobalTheory.integrableOn_fundamentalDomain_of_cocompact N _ K hK hs μ inferInstance 𝓕 h _ (by fun_prop)
    (leftInv_integrand hφ x)


omit [LocallyCompactSpace N] in
theorem measure_ne_top [μ.IsHaarMeasure] (h : IsFundamentalDomain (Γ.subgroupOf N) 𝓕 μ) : μ 𝓕 ≠ ⊤ :=
  ((integrableOn_const_iff (C := (1 : ℂ))).1
    (hc.integrableOn h (φ := fun _ => 1) (fun _ _ _ => rfl) continuous_const 1)).elim (by simp) LT.lt.ne

theorem isProbabilityMeasure : IsProbabilityMeasure (probMeasure Γ N) :=
  ⟨ENNReal.inv_mul_cancel (NeZero.ne _) (by
    rw [quotMeasure_univ (isFundamentalDomain_stdDom _ _)]; exact hc.measure_ne_top (isFundamentalDomain_stdDom _ _))⟩

theorem integrable (hφ : LeftInv Γ φ) (hφc : Continuous φ) (x : G) :
    Integrable (fun q : Quot (Γ.subgroupOf N) => φ ((q.out : N) * x)) (probMeasure Γ N) := by
  have h := isFundamentalDomain_stdDom (Γ.subgroupOf N) Measure.haar
  refine Integrable.smul_measure (memLp_one_iff_integrable.1 ((memLp_quotMeasure_iff h).2 ?_))
    (ENNReal.inv_ne_top.2 (NeZero.ne _))
  rw [show lift _ (fun q : Quot (Γ.subgroupOf N) => φ ((q.out : N) * x)) = _ from
    (leftInv_integrand (N := N) hφ x).lift_descend]
  exact memLp_one_iff_integrable.2 (hc.integrableOn h hφ hφc x)

theorem constTermOn_const (c : ℂ) (x : G) : constTermOn Γ N (fun _ => c) x = c := by
  have := hc.isProbabilityMeasure
  simp [constTermOn]

theorem constTermOn_add (hφ : LeftInv Γ φ) (hφc : Continuous φ) (hψ : LeftInv Γ ψ) (hψc : Continuous ψ) (x : G) :
    constTermOn Γ N (φ + ψ) x = constTermOn Γ N φ x + constTermOn Γ N ψ x :=
  integral_add (hc.integrable hφ hφc x) (hc.integrable hψ hψc x)

theorem constTermOn_eq_zero_iff [μ.IsHaarMeasure] (h : IsFundamentalDomain (Γ.subgroupOf N) 𝓕 μ) (hφ : LeftInv Γ φ)
    (x : G) : constTermOn Γ N φ x = 0 ↔ ∫ n in 𝓕, φ (n * x) ∂μ = 0 :=
  (constTermOn_eq h hφ x).symm ▸ smul_eq_zero_iff_right (inv_ne_zero
    (ENNReal.toReal_ne_zero.2 ⟨h.measure_ne_zero (NeZero.ne μ), hc.measure_ne_top h⟩))

theorem isMulRightInvariant (μ : Measure N) [μ.IsHaarMeasure] : μ.IsMulRightInvariant := ⟨fun g => by
  have h := isFundamentalDomain_stdDom (Γ.subgroupOf N) μ
  have e := Measure.isMulLeftInvariant_eq_smul (μ.map (· * g)) μ
  have h' : IsFundamentalDomain (Γ.subgroupOf N) ((· * g) ⁻¹' stdDom (Γ.subgroupOf N)) μ :=
    h.preimage_of_equiv ⟨(measurable_mul_const g).aemeasurable, e ▸ Measure.smul_absolutelyContinuous⟩ Function.bijective_id
      fun γ x => mul_assoc _ _ _
  have h1 := h'.measure_eq h
  rw [← Measure.map_apply (measurable_mul_const g) (measurableSet_stdDom _), e, Measure.smul_apply, ENNReal.smul_def,
    smul_eq_mul, ENNReal.mul_eq_right (h.measure_ne_zero (NeZero.ne μ)) (hc.measure_ne_top h), ENNReal.coe_eq_one] at h1
  rw [e, h1, one_smul]⟩

theorem constTermOn_mul_left (hφ : LeftInv Γ φ) {n : G} (hn : n ∈ N) (x : G) :
    constTermOn Γ N φ (n * x) = constTermOn Γ N φ x := by
  have := hc.isMulRightInvariant Measure.haar
  have h := isFundamentalDomain_stdDom (Γ.subgroupOf N) Measure.haar
  have hp := measurePreserving_mul_right (Measure.haar : Measure N) ⟨n, hn⟩
  have h' := h.preimage_of_equiv hp.quasiMeasurePreserving Function.bijective_id fun γ x => mul_assoc _ _ _
  rw [constTermOn_eq h' hφ, constTermOn_eq h hφ, ← hp.setIntegral_preimage_emb (measurableEmbedding_mulRight _) _
    (stdDom _), measureReal_def, measureReal_def, hp.measure_preimage h.nullMeasurableSet]
  simp only [Subgroup.coe_mul, mul_assoc]

theorem continuous_constTermOn [LocallyCompactSpace G] (hφ : LeftInv Γ φ) (hφc : Continuous φ) :
    Continuous (constTermOn Γ N φ) := by
  have := hc.isProbabilityMeasure
  obtain ⟨K, hK, hs⟩ := id hc
  refine continuous_iff_continuousAt.2 fun x => ?_
  obtain ⟨U, hU, hx⟩ := exists_compact_mem_nhds x
  obtain ⟨C, hC⟩ := (hK.prod hU).exists_bound_of_continuousOn (f := fun p : N × G => φ (p.1 * p.2)) (by fun_prop)
  refine continuousAt_of_dominated (bound := fun _ => C) (.of_forall fun y => (hc.integrable hφ hφc y).1)
    (Filter.Eventually.mono hx fun y hy => .of_forall fun q => ?_) (integrable_const C) (.of_forall fun q => by fun_prop)
  obtain ⟨γ, hγ, hk⟩ := hs q.out
  exact (congrArg norm (leftInv_integrand hφ y γ hγ q.out)).ge.trans (hC (_, y) ⟨hk, hy⟩)

end Cocompact

end GlobalTheory.Cusp

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUniqueIsProdMeasureFinAway
noncomputable section

namespace GlobalTheory.AdelicU

open scoped TensorProduct NNReal ENNReal Pointwise
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

section Generic

variable {G ι κ : Type} {H : ι → Type} {P : κ → Type} [Group G] [∀ i, Group (H i)] [∀ k, Group (P k)]
  (p : ∀ i, G →* H i) (q : ∀ k, G →* P k) (K : ∀ k, Subgroup (P k))

def cyl (S : Finset κ) (A : ∀ i, Set (H i)) (B : ∀ k, Set (P k)) : Set G :=
  {g | (∀ i, p i g ∈ A i) ∧ (∀ k ∈ S, q k g ∈ B k) ∧ ∀ k ∉ S, q k g ∈ K k}

theorem mem_cyl {S : Finset κ} {A : ∀ i, Set (H i)} {B : ∀ k, Set (P k)} {g : G} :
    g ∈ cyl p q K S A B ↔ (∀ i, p i g ∈ A i) ∧ (∀ k ∈ S, q k g ∈ B k) ∧ ∀ k ∉ S, q k g ∈ K k := Iff.rfl


variable [TopologicalSpace G] [∀ i, TopologicalSpace (H i)] [∀ k, TopologicalSpace (P k)]

structure IsRestrGroup : Prop where
  cont_p : ∀ i, Continuous (p i)
  cont_q : ∀ k, Continuous (q k)
  isOpen_K : ∀ k, IsOpen (K k : Set (P k))
  isOpen_all : IsOpen {g | ∀ k, q k g ∈ K k}
  isCompact_cyl : ∀ S A B, (∀ i, IsCompact (A i)) → (∀ k ∈ S, IsCompact (B k)) → IsCompact (cyl p q K S A B)
  exists_comp : ∀ (S : Finset κ) (x : ∀ i, H i) (y : ∀ k : S, P k),
    ∃ g, (∀ i, p i g = x i) ∧ (∀ k : S, q k g = y k) ∧ ∀ k ∉ S, q k g ∈ K k

variable [Fintype ι] [MeasurableSpace G] [∀ i, MeasurableSpace (H i)] [∀ k, MeasurableSpace (P k)]

structure IsRestrProd (μi : ∀ i, Measure (H i)) (μf : ∀ k, Measure (P k)) (μ : Measure G) : Prop where
  haar_inf : ∀ i, (μi i).IsHaarMeasure
  haar_fin : ∀ k, (μf k).IsHaarMeasure
  vol_one : ∀ᶠ k in cofinite, μf k (K k) = 1
  haar : μ.IsHaarMeasure
  measure_cyl : ∀ S : Finset κ, (∀ k ∉ S, μf k (K k) = 1) → ∀ A B, (∀ i, MeasurableSet (A i)) →
    (∀ k ∈ S, MeasurableSet (B k)) → μ (cyl p q K S A B) = (∏ i, μi i (A i)) * ∏ k ∈ S, μf k (B k)

variable {p q K} {μi : ∀ i, Measure (H i)} {μf : ∀ k, Measure (P k)} {μ : Measure G}


omit [∀ k, TopologicalSpace (P k)] in
theorem exists_finset_vol_one (h : ∀ᶠ k in cofinite, μf k (K k) = 1) : ∃ S : Finset κ, ∀ k ∉ S, μf k (K k) = 1 :=
  ⟨(eventually_cofinite.1 h).toFinset, fun k hk => by simpa using hk⟩

theorem IsRestrProd.smul_inf [DecidableEq ι] [MeasurableConstSMul G G]
    (h : IsRestrProd p q K μi μf μ) (i : ι) [MeasurableConstSMul (H i) (H i)] {c : ℝ≥0} (hc : c ≠ 0) :
    IsRestrProd p q K (Function.update μi i (c • μi i)) μf (c • μ) := by
  have := h.haar
  have := h.haar_inf
  refine ⟨fun j => ?_, h.haar_fin, h.vol_one, .nnreal_smul _ hc, fun S hS A B hA hB => ?_⟩
  · by_cases e : j = i
    · subst j; rw [Function.update_self]; exact .nnreal_smul _ hc
    · rw [Function.update_of_ne e]; exact h.haar_inf j
  · rw [Measure.smul_apply, h.measure_cyl S hS A B hA hB, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
      ← Finset.mul_prod_erase _ (fun j => Function.update μi i (c • μi i) j (A j)) (Finset.mem_univ i),
      Function.update_self, Finset.prod_congr (f := fun j => Function.update μi i (c • μi i) j (A j))
        (g := fun j => μi j (A j)) rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]]
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, mul_assoc]

variable [IsTopologicalGroup G] [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [∀ i, IsTopologicalGroup (H i)] [∀ i, BorelSpace (H i)] [∀ i, LocallyCompactSpace (H i)]
  [∀ i, SecondCountableTopology (H i)] [∀ i, T2Space (H i)]
  [∀ k, IsTopologicalGroup (P k)] [∀ k, BorelSpace (P k)] [∀ k, LocallyCompactSpace (P k)]
  [∀ k, SecondCountableTopology (P k)] [∀ k, T2Space (P k)]


omit [IsTopologicalGroup G] [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [∀ i, SecondCountableTopology (H i)] [∀ k, SecondCountableTopology (P k)] [MeasurableSpace G] [Group G]
  [TopologicalSpace G] in
theorem exists_box_pos (μi : ∀ i, Measure (H i)) (μf : ∀ k, Measure (P k))
    [∀ i, (μi i).IsHaarMeasure] [∀ k, (μf k).IsHaarMeasure] (S : Finset κ) :
    ∃ (A : ∀ i, Set (H i)) (B : ∀ k, Set (P k)), (∀ i, MeasurableSet (A i)) ∧ (∀ k, MeasurableSet (B k)) ∧
      (∏ i, μi i (A i)) * ∏ k ∈ S, μf k (B k) ≠ 0 ∧ (∏ i, μi i (A i)) * ∏ k ∈ S, μf k (B k) ≠ ∞ := by
  let A := fun i => (Classical.arbitrary (TopologicalSpace.PositiveCompacts (H i)))
  let B := fun k => (Classical.arbitrary (TopologicalSpace.PositiveCompacts (P k)))
  exact ⟨fun i => A i, fun k => B k, fun i => (A i).isCompact.measurableSet, fun k => (B k).isCompact.measurableSet,
    mul_ne_zero (Finset.prod_ne_zero_iff.2 fun i _ => (Measure.measure_pos_of_nonempty_interior _ (A i).interior_nonempty).ne')
      (Finset.prod_ne_zero_iff.2 fun k _ => (Measure.measure_pos_of_nonempty_interior _ (B k).interior_nonempty).ne'),
    ENNReal.mul_ne_top (ENNReal.prod_ne_top fun i _ => (A i).isCompact.measure_lt_top.ne)
      (ENNReal.prod_ne_top fun k _ => (B k).isCompact.measure_lt_top.ne)⟩



omit [∀ i, SecondCountableTopology (H i)] [∀ k, SecondCountableTopology (P k)] in
theorem IsRestrProd.unique {μ' : Measure G} (h : IsRestrProd p q K μi μf μ) (h' : IsRestrProd p q K μi μf μ') :
    μ = μ' := by
  have := h.haar
  have := h'.haar
  have := h.haar_inf
  have := h.haar_fin
  obtain ⟨S, hS⟩ := exists_finset_vol_one h.vol_one
  obtain ⟨A, B, hA, hB, h0, ht⟩ := exists_box_pos μi μf S
  have e := Measure.isMulLeftInvariant_eq_smul μ μ'
  have e1 := h.measure_cyl S hS A B hA fun k _ => hB k
  rw [e, Measure.smul_apply, h'.measure_cyl S hS A B hA fun k _ => hB k, ENNReal.smul_def, smul_eq_mul] at e1
  have e2 : Measure.haarScalarFactor μ μ' = 1 := by
    exact_mod_cast (ENNReal.mul_left_inj h0 ht).1 (e1.trans (one_mul _).symm)
  rw [e, e2, one_smul]

end Generic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E))

def IsProdMeasure (μi : ∀ w, Measure (GArch σ J w)) (μf : ∀ v, Measure (GLoc σ J v)) (μ : Measure (GAd σ J)) : Prop :=
  IsRestrProd (projArch σ J) (proj σ J) (stabLoc σ J L) μi μf μ

def IsProdMeasureFin (μf : ∀ v, Measure (GLoc σ J v)) (μ : Measure (GFin σ J)) : Prop :=
  IsRestrProd (H := fun _ : Empty => Unit) (fun _ => 1) (projFinLoc σ J) (stabLoc σ J L) (fun e => e.elim) μf μ

section Unfold

omit [NumberField E]

variable {σ J L}

theorem isRestrProd_empty_iff {G κ : Type} {P : κ → Type} [Group G] [∀ k, Group (P k)] [TopologicalSpace G]
    [∀ k, TopologicalSpace (P k)] [MeasurableSpace G] [∀ k, MeasurableSpace (P k)] {q : ∀ k, G →* P k}
    {K : ∀ k, Subgroup (P k)} {μf : ∀ k, Measure (P k)} {μ : Measure G} :
    IsRestrProd (H := fun _ : Empty => Unit) (fun _ => 1) q K (fun e => e.elim) μf μ ↔
      (∀ k, (μf k).IsHaarMeasure) ∧ (∀ᶠ k in cofinite, μf k (K k) = 1) ∧ μ.IsHaarMeasure ∧
      ∀ S : Finset κ, (∀ k ∉ S, μf k (K k) = 1) → ∀ B : ∀ k, Set (P k), (∀ k ∈ S, MeasurableSet (B k)) →
        μ {g | (∀ k ∈ S, q k g ∈ B k) ∧ ∀ k ∉ S, q k g ∈ K k} = ∏ k ∈ S, μf k (B k) :=
  ⟨fun h => ⟨h.2, h.3, h.4, fun S hS B hB => by
      have : IsEmpty Empty := ⟨Empty.elim⟩
      simpa [cyl] using h.5 S hS (fun _ => Set.univ) B (fun e => e.elim) hB⟩,
    fun h => ⟨fun e => e.elim, h.1, h.2.1, h.2.2.1, fun S hS A B _ hB => by
      have : IsEmpty Empty := ⟨Empty.elim⟩
      simpa [cyl] using h.2.2.2 S hS B hB⟩⟩

theorem isProdMeasureFin_iff {μf : ∀ v, Measure (GLoc σ J v)} {μ : Measure (GFin σ J)} :
    IsProdMeasureFin σ J L μf μ ↔ (∀ v, (μf v).IsHaarMeasure) ∧
      (∀ᶠ v in cofinite, μf v (stabLoc σ J L v) = 1) ∧ μ.IsHaarMeasure ∧
      ∀ S : Finset (HeightOneSpectrum (𝓞 F)), (∀ v ∉ S, μf v (stabLoc σ J L v) = 1) →
        ∀ B : ∀ v, Set (GLoc σ J v), (∀ v ∈ S, MeasurableSet (B v)) →
          μ {g | (∀ v ∈ S, projFinLoc σ J v g ∈ B v) ∧ ∀ v ∉ S, projFinLoc σ J v g ∈ stabLoc σ J L v} =
            ∏ v ∈ S, μf v (B v) := isRestrProd_empty_iff

theorem comp_glue {S : Finset (HeightOneSpectrum (𝓞 F))} (a : ∀ w, GArch σ J w) (b : ∀ v : S, GLoc σ J v) :
    (∀ w, projArch σ J w (ofInf σ J (embArchPi σ J a) * embAt σ J S b) = a w) ∧
    (∀ v : S, proj σ J v (ofInf σ J (embArchPi σ J a) * embAt σ J S b) = b v) ∧
    ∀ v ∉ S, proj σ J v (ofInf σ J (embArchPi σ J a) * embAt σ J S b) = 1 := by
  have h := mem_atPts.1 (embAt_mem σ J S b)
  exact ⟨fun w => by simp [mem_finPts_iff_forall.1 h.1 w], fun v => by simp, fun v hv => by simp [h.2 v hv]⟩

end Unfold

theorem isCompact_of_ext {X : Type} [TopologicalSpace X] {s t : Set X} (h : IsCompact t) (e : ∀ x, x ∈ s ↔ x ∈ t) :
    IsCompact s := (Set.ext e : s = t) ▸ h

variable [Submodule.IsFullLattice E L]

theorem isRestrGroup_GAd : IsRestrGroup (projArch σ J) (proj σ J) (stabLoc σ J L) := by
  refine {
    cont_p := continuous_projArch σ J
    cont_q := continuous_proj σ J
    isOpen_K := isOpen_stabLoc σ J L
    isOpen_all := ?_
    isCompact_cyl := ?_
    exists_comp := ?_ }
  · convert isOpen_levelOpen σ J L using 1
    exact Set.ext fun _ => mem_levelOpen.symm
  · intro S A B hA hB
    have hc := ((((isCompact_univ_pi hA).image (continuous_embArchPi σ J)).image (continuous_ofInf σ J)).mul
      ((isCompact_univ_pi fun v : S => hB v v.2).image (continuous_embAt σ J S))).mul (isCompact_levelOff σ J L S)
    refine isCompact_of_ext hc fun g => ?_
    constructor
    · rintro ⟨h1, h2, h3⟩
      obtain ⟨e1, e2, e3⟩ := comp_glue (fun w => projArch σ J w g) (projAt σ J S g)
      refine ⟨_, ⟨_, ⟨_, ⟨fun w => projArch σ J w g, fun w _ => h1 w, rfl⟩, rfl⟩, _,
        ⟨projAt σ J S g, fun v _ => h2 v v.2, rfl⟩, rfl⟩, _⁻¹ * g,
        mem_levelOff.2 ⟨mem_finPts_iff_forall.2 fun w => ?_, fun v hv => ?_, fun v hv => ?_⟩, mul_inv_cancel_left _ _⟩
      · rw [map_mul, map_inv, e1, inv_mul_cancel]
      · rw [map_mul, map_inv, e2 ⟨v, hv⟩, projAt_apply, inv_mul_cancel]
      · rw [map_mul, map_inv, e3 v hv, inv_one, one_mul]; exact h3 v hv
    · rintro ⟨_, ⟨_, ⟨_, ⟨a, ha, rfl⟩, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩, k, hk, rfl⟩
      obtain ⟨e1, e2, e3⟩ := comp_glue a b
      obtain ⟨k1, k2, k3⟩ := mem_levelOff.1 hk
      refine ⟨fun w => ?_, fun v hv => ?_, fun v hv => ?_⟩
      · rw [map_mul, e1, mem_finPts_iff_forall.1 k1, mul_one]; exact ha w trivial
      · rw [map_mul, e2 ⟨v, hv⟩, k2 v hv, mul_one]; exact hb ⟨v, hv⟩ trivial
      · rw [map_mul, e3 v hv, one_mul]; exact k3 v hv
  · intro S x y
    exact ⟨_, (comp_glue x y).1, (comp_glue x y).2.1, fun v hv => by
      rw [(comp_glue x y).2.2 v hv]; exact one_mem _⟩

theorem isRestrGroup_GFin :
    IsRestrGroup (H := fun _ : Empty => Unit) (fun _ => 1) (projFinLoc σ J) (stabLoc σ J L) := by
  refine {
    cont_p := fun e => e.elim
    cont_q := continuous_projFinLoc σ J
    isOpen_K := isOpen_stabLoc σ J L
    isOpen_all := ?_
    isCompact_cyl := ?_
    exists_comp := ?_ }
  · simpa using (isRestrGroup_GAd σ J L).isOpen_all.preimage (continuous_ofFin σ J)
  · intro S A B _ hB
    have := (Function.LeftInverse.isClosedEmbedding (projFin_ofFin σ J) (continuous_projFin σ J)
      (continuous_ofFin σ J)).isCompact_preimage
      ((isRestrGroup_GAd σ J L).isCompact_cyl S (fun _ => {1}) B (fun _ => isCompact_singleton) hB)
    convert this using 1
    ext g
    have : IsEmpty Empty := ⟨Empty.elim⟩
    simp [mem_cyl]
  · intro S _ y
    obtain ⟨g, -, h2, h3⟩ := (isRestrGroup_GAd σ J L).exists_comp S 1 y
    exact ⟨projFin σ J g, fun e => e.elim, by simpa using h2, by simpa using h3⟩

section Away

variable (T : Finset (HeightOneSpectrum (𝓞 F)))

omit [NumberField E] [Submodule.IsFullLattice E L] in
theorem exists_away (S : Finset {v // v ∉ T}) (x : ∀ w, GArch σ J w) (y : ∀ v : S, GLoc σ J v.1) :
    ∃ g ∈ awayPts σ J T, (∀ w, projArch σ J w g = x w) ∧ (∀ v : S, proj σ J v.1 g = y v) ∧
      ∀ v ∉ S, proj σ J v.1 g ∈ stabLoc σ J L v := by
  classical
  obtain ⟨e1, e2, e3⟩ := comp_glue (S := S.map (Function.Embedding.subtype _)) x fun v =>
    y ⟨⟨v.1, Finset.property_of_mem_map_subtype S v.2⟩, by
      obtain ⟨u, hu, e⟩ := Finset.mem_map.1 v.2
      convert hu using 1
      exact Subtype.ext e.symm⟩
  exact ⟨_, mem_awayPts.2 fun v hv => e3 v fun h => Finset.property_of_mem_map_subtype S h hv, e1,
    fun v => e2 ⟨v.1.1, Finset.mem_map_of_mem _ v.2⟩, fun v hv => by
      rw [e3 v (by simpa [v.2] using hv)]; exact one_mem _⟩

instance (U : Subgroup (GAd σ J)) : SecondCountableTopology U := TopologicalSpace.Subtype.secondCountableTopology _

end Away

def stabCompacts (v : HeightOneSpectrum (𝓞 F)) : TopologicalSpace.PositiveCompacts (GLoc σ J v) :=
  ⟨⟨stabLoc σ J L v, isCompact_stabLoc σ J L v⟩, by
    rw [(isOpen_stabLoc σ J L v).interior_eq]; exact ⟨1, one_mem _⟩⟩

def haarLoc (v : HeightOneSpectrum (𝓞 F)) : Measure (GLoc σ J v) := Measure.haarMeasure (stabCompacts σ J L v)

instance (v : HeightOneSpectrum (𝓞 F)) : (haarLoc σ J L v).IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _

@[simp] theorem haarLoc_stabLoc (v : HeightOneSpectrum (𝓞 F)) : haarLoc σ J L v (stabLoc σ J L v) = 1 :=
  Measure.haarMeasure_self (K₀ := stabCompacts σ J L v)

variable {σ J L}


end GlobalTheory.AdelicU

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Foundations.NotHasParamOfSubsingleton
noncomputable section

namespace GlobalTheory.LFun.Model

open NumberField IsDedekindDomain Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)

def constMap (G : Type) : ℂ →ₗ[ℂ] (G → ℂ) := LinearMap.pi fun _ => LinearMap.id

theorem constMap_injective (G : Type) [Group G] : Function.Injective (constMap G) := fun _ _ h => congrFun h 1

section Linear

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ)

def rhoGL (i : Fin n) : ℂˣ := npowU w (((n : ℂ) - 1) / 2 - (i : ℕ))

theorem chiDelta_rhoGL (b : GL (Fin n) (w.adicCompletion E)) : chiDelta E w (fun i => (rhoGL w n i : ℂ)) b = 1 := by
  refine Finset.prod_eq_one fun i _ => ?_
  have hq : ((qV E w : ℕ) : ℂ) ≠ 0 := by exact_mod_cast qV_ne_zero w
  change (((qV E w : ℕ) : ℂ) ^ (((n : ℂ) - 1) / 2 - (i : ℕ))) ^ _ * _ = 1
  rw [← Complex.cpow_mul_int, ← Complex.cpow_add _ _ hq]
  convert Complex.cpow_zero _ using 2
  ring

theorem hasSatGL_trivial : HasSatGL w (Representation.trivial ℂ (GL (Fin n) (w.adicCompletion E)) ℂ) (seg w 1 n) := by
  have e : seg w 1 n = Finset.univ.val.map (rhoGL w n) := by
    rw [seg, Finset.range_val, ← Multiset.coe_range, ← List.map_coe_finRange_eq_range, Multiset.map_coe, List.map_map]
    simp only [one_mul]
    rfl
  rw [e]
  refine ⟨(Submodule.ne_bot_iff _).2 ⟨1, GlobalTheory.LGrp.mem_fixed.2 fun _ _ => rfl, one_ne_zero⟩, fun x _ h0 => ?_⟩
  refine IsSatVecGL.of_map (constMap _) (fun _ _ => rfl) (constMap_injective _)
    (isSatVecGL_of_isSpherical (fun b g k _ _ => ?_) fun h => h0 (congrFun h 1))
  rw [chiDelta_rhoGL, one_mul]; rfl

end Linear

section U

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] {σ : L →+* L} {ϖ : L} {q : ℕ}

def rhoU {q : ℕ} (hq : q ≠ 0) (n : ℕ) (i : Fin (n / 2)) : ℂˣ :=
  Units.mk0 (q : ℂ) (by exact_mod_cast hq) ^ ((n : ℤ) - 1 - 2 * (i.val : ℤ))

theorem hasSatU_trivial (hU : IsUnramInv ϖ σ q) (hq : q ≠ 0) (n : ℕ) :
    HasSatU ϖ q (Representation.trivial ℂ (GU σ n) ℂ) (rhoU hq n) := by
  refine ⟨(Submodule.ne_bot_iff _).2 ⟨1, GlobalTheory.LGrp.mem_fixed.2 fun _ _ => rfl, one_ne_zero⟩, fun x _ h0 => ?_⟩
  refine IsSatVecU.of_map hU (constMap _) (fun _ _ => rfl) (constMap_injective _)
    (isSatVecU_of_isSphericalU hU (fun b g k _ _ => ?_) fun h => h0 (congrFun h 1))
  have : chiDeltaU q (fun i => (rhoU hq n i : ℂ)) b = 1 := by
    refine Finset.prod_eq_one fun i _ => ?_
    have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq
    split_ifs
    · simp only [rhoU, Units.val_zpow_eq_zpow_val, Units.val_mk0]
      rw [← zpow_mul, ← zpow_add₀ hq']
      convert zpow_zero _ using 2
      ring
    · rfl
  rw [this, one_mul]; rfl

end U

section Global

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)}
  {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} {h : w.under (𝓞 F) = v}


end Global

end GlobalTheory.LFun.Model

end
end
