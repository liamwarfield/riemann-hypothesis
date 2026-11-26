module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountable
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarMapLinearScalingByDeterminant
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GlobalUnitScalingHaarProductFormula
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitaryGroupFiniteVolume

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.EulerProductMeasureZero
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.EulerProductMeasureZero
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.EulerZero

theorem exists_tail_pos {ι : Type} {a : ι → ℝ} (h : Summable (fun v => |a v - 1|)) (S₀ : Finset ι) :
    ∃ S : Finset ι, S₀ ⊆ S ∧ 0 < ∏' v : {v // v ∉ S}, a v.1 := by
  classical
  have hev : ∀ᶠ v in Filter.cofinite, |a v - 1| < 1 :=
    h.tendsto_cofinite_zero.eventually (gt_mem_nhds one_pos)
  have hfin : {v | ¬ |a v - 1| < 1}.Finite := Filter.eventually_cofinite.1 hev
  refine ⟨S₀ ∪ hfin.toFinset, Finset.subset_union_left, ?_⟩
  have hs : Summable (fun v : {v // v ∉ S₀ ∪ hfin.toFinset} => |a v.1 - 1|) :=
    h.comp_injective Subtype.val_injective
  refine (AbsTprod.abs_tprod _ (fun v : {v // v ∉ S₀ ∪ hfin.toFinset} => a v.1) hs).2.2.1 ?_
  rintro ⟨v, hv⟩
  have hv' : |a v - 1| < 1 := by
    by_contra hc
    exact hv (Finset.mem_union_right _ (hfin.mem_toFinset.2 hc))
  have := (abs_lt.1 hv').1
  show 0 < a v
  linarith

theorem countable_places (F : Type) [Field F] [NumberField F] :
    Countable (HeightOneSpectrum (𝓞 F)) := by
  haveI : Countable (𝓞 F) := by
    haveI : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
    exact RingOfIntegers.coe_injective.countable
  haveI : Countable (Ideal (𝓞 F)) := by
    refine Function.Surjective.countable
      (f := fun s : Finset (𝓞 F) => Ideal.span (s : Set (𝓞 F))) ?_
    intro I
    exact (IsNoetherian.noetherian I : I.FG)
  exact Function.Injective.countable (f := fun la : HeightOneSpectrum (𝓞 F) => la.asIdeal)
    fun a b h => HeightOneSpectrum.ext h

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem exists_measure_intOff {d M n : ℕ} {b : Module.Basis (Fin d) F E}
    {I : Measure (Fin n → Fin M → AF F ⊗[F] E)} {c : ℝ≥0}
    {minf : Measure (Fin n → Fin M → Ainf F ⊗[F] E)}
    {m : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)}
    (h : IsEulerProd b I c minf m)
    (hmeas : ∀ S, MeasurableSet (intOff (n := n) (M := M) b S)) :
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₀ ⊆ S →
      I (intOff b S) = (c : ℝ≥0∞) * (minf Set.univ * ∏ v ∈ S, m v Set.univ) *
        ENNReal.ofReal (∏' v : {v // v ∉ S}, (m v.1 (latV b v.1)).toReal) := by
  obtain ⟨-, -, S₀, hS₀⟩ := h
  refine ⟨S₀, fun S hS => ?_⟩
  have key := hS₀ S hS (fun _ => 1) (fun _ _ => 1) measurable_const (fun _ => measurable_const)
  have hp : pureL b S (fun _ => 1) (fun _ _ => 1) = (intOff (n := n) (M := M) b S).indicator 1 := by
    funext X
    simp [pureL, Set.indicator]
  rw [hp, lintegral_indicator_one (hmeas S)] at key
  simpa using key

end GlobalTheory.CompanionTheory.SW.EulerZero


open GlobalTheory.CompanionTheory.SW.EulerZero in
theorem GlobalTheory.CompanionTheory.SW.EulerZero.euler_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (I : Measure (Fin n → Fin M → AF F ⊗[F] E)) (c : ℝ≥0) (minf : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (m : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)), (IsEulerProd b I c minf m → I = 0 → c = 0 ∨ minf = 0 ∨ ∃ v, m v = 0) ∧ (IsEulerProd b I c minf m → (minf = 0 ∨ ∃ v, m v = 0) → I = 0) ∧ ((∀ v, m v (latV b v) < ⊤) → Summable (fun v => |(m v (latV b v)).toReal - 1|) → (minf = 0 ∨ ∃ v, m v = 0) → IsEulerProd b 0 c minf m) := by
  intro F E _ _ _ _ _ σ hσ d b n M I c minf m
  obtain ⟨-, -, -, -, hopen, hcof, -⟩ := GlobalTheory.T.adelic_tuple_projections F E σ hσ d b n M
  obtain ⟨⟨hlc, hsc, ht2⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  obtain ⟨-, -, -, -, -, -, -, hborel, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (AF F)
  haveI := hborel n M
  have hmeas : ∀ S, MeasurableSet (intOff (n := n) (M := M) b S) := fun S => (hopen S).measurableSet
  refine ⟨fun h hI => ?_, fun h hz => ?_, fun hfin hsum hz => ?_⟩
  · by_contra hcon
    push_neg at hcon
    obtain ⟨hc, hminf, hm⟩ := hcon
    obtain ⟨S₀, hS₀⟩ := exists_measure_intOff h hmeas
    obtain ⟨S, hS, hpos⟩ := exists_tail_pos h.2.1 S₀
    have key := hS₀ S hS
    rw [hI] at key
    have h1 : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc
    have h2 : minf Set.univ ≠ 0 := by simpa using hminf
    have h3 : ∏ v ∈ S, m v Set.univ ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun v _ => by simpa using hm v
    have h4 : ENNReal.ofReal (∏' v : {v // v ∉ S}, (m v.1 (latV b v.1)).toReal) ≠ 0 := by
      simpa using hpos
    exact (mul_ne_zero (mul_ne_zero h1 (mul_ne_zero h2 h3)) h4) (by simpa using key.symm)
  · obtain ⟨S₀, hS₀⟩ := exists_measure_intOff h hmeas
    classical
    obtain ⟨S₁, hS₁, hzero⟩ : ∃ S₁ : Finset (HeightOneSpectrum (𝓞 F)), S₀ ⊆ S₁ ∧
        ∀ S, S₁ ⊆ S → minf Set.univ * ∏ v ∈ S, m v Set.univ = 0 := by
      rcases hz with hz | ⟨v, hv⟩
      · exact ⟨S₀, subset_rfl, fun S _ => by simp [hz]⟩
      · refine ⟨insert v S₀, Finset.subset_insert _ _, fun S hS => ?_⟩
        rw [Finset.prod_eq_zero (hS (Finset.mem_insert_self v S₀)) (by simp [hv]), mul_zero]
    haveI := countable_places F
    have hcover : (Set.univ : Set (Fin n → Fin M → AF F ⊗[F] E)) ⊆
        ⋃ T : Finset (HeightOneSpectrum (𝓞 F)), intOff b (S₁ ∪ T) := by
      intro X _
      have hT := Filter.eventually_cofinite.1 (hcof (projFin X))
      refine Set.mem_iUnion.2 ⟨hT.toFinset, fun v hv => ?_⟩
      by_contra hc
      exact hv (Finset.mem_union_right _ (hT.mem_toFinset.2 hc))
    have hnull : I Set.univ = 0 := by
      refine measure_mono_null hcover (measure_iUnion_null fun T => ?_)
      rw [hS₀ _ (hS₁.trans Finset.subset_union_left), hzero _ Finset.subset_union_left]
      simp
    exact Measure.measure_univ_eq_zero.1 hnull
  · refine ⟨hfin, hsum, ?_⟩
    classical
    obtain ⟨S₀, hS₀⟩ : ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)), minf = 0 ∨ ∃ v ∈ S₀, m v = 0 := by
      rcases hz with hz | ⟨v, hv⟩
      · exact ⟨∅, Or.inl hz⟩
      · exact ⟨{v}, Or.inr ⟨v, by simp, hv⟩⟩
    refine ⟨S₀, fun S hS φinf φ _ _ => ?_⟩
    rcases hS₀ with hz | ⟨v, hv, hmv⟩
    · simp [hz]
    · rw [Finset.prod_eq_zero (hS hv) (by simp [hmv])]
      simp
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.EulerProductMeasureZeroStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.euler_product_measure_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (I : Measure (Fin n → Fin M → AF F ⊗[F] E)) (c : ℝ≥0) (minf : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (m : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)), (IsEulerProd b I c minf m → I = 0 → c = 0 ∨ minf = 0 ∨ ∃ v, m v = 0) ∧ (IsEulerProd b I c minf m → (minf = 0 ∨ ∃ v, m v = 0) → I = 0) ∧ ((∀ v, m v (latV b v) < ⊤) → Summable (fun v => |(m v (latV b v)).toReal - 1|) → (minf = 0 ∨ ∃ v, m v = 0) → IsEulerProd b 0 c minf m) := by
  first | exact @GlobalTheory.CompanionTheory.SW.EulerZero.euler_zero | exact GlobalTheory.CompanionTheory.SW.EulerZero.euler_zero | (intros; apply GlobalTheory.CompanionTheory.SW.EulerZero.euler_zero <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LinearChangeEulerProduct
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LinearChangeEulerProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.ProdFormula

theorem modulus_matrix : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F), A.det ≠ 0 → ∃ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c ∧ (∀ μ : Measure (ι → Ainf F), μ.IsAddHaarMeasure → μ.map (fun x => A.map (algebraMap F (Ainf F)) *ᵥ x) = cinf • μ) ∧ ∀ v : HeightOneSpectrum (𝓞 F), (∀ μ : Measure (ι → Fv F v), μ.IsAddHaarMeasure → μ.map (fun x => A.map (algebraMap F (Fv F v)) *ᵥ x) = c v • μ) := by
  intro F _ _ ι _ _ A hA
  obtain ⟨cinf, c, hU, hinf, hv⟩ := GlobalTheory.T.global_unit_scaling_haar_product_formula F A.det hA
  refine ⟨cinf, c, hU, ?_, ?_⟩
  · intro μ hμ
    haveI : BorelSpace (Ainf F) := ⟨rfl⟩
    exact GlobalTheory.T.haar_map_linear_scaling_by_determinant F (Ainf F) ι A hA Measure.addHaar inferInstance cinf
      (hinf Measure.addHaar inferInstance) μ hμ
  · intro v μ hμ
    haveI : BorelSpace (Fv F v) := ⟨rfl⟩
    haveI : SecondCountableTopology (Fv F v) := (GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v).2.2.1
    exact GlobalTheory.T.haar_map_linear_scaling_by_determinant F (Fv F v) ι A hA Measure.addHaar inferInstance (c v)
      (hv v Measure.addHaar inferInstance) μ hμ

end GlobalTheory.CompanionTheory.SW.ProdFormula
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LinearChangeEulerProductStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.addHaar_map_mulVec_eq_smul_at_all_places : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F), A.det ≠ 0 → ∃ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c ∧ (∀ μ : Measure (ι → Ainf F), μ.IsAddHaarMeasure → μ.map (fun x => A.map (algebraMap F (Ainf F)) *ᵥ x) = cinf • μ) ∧ ∀ v : HeightOneSpectrum (𝓞 F), (∀ μ : Measure (ι → Fv F v), μ.IsAddHaarMeasure → μ.map (fun x => A.map (algebraMap F (Fv F v)) *ᵥ x) = c v • μ) := by
  first | exact @GlobalTheory.CompanionTheory.SW.ProdFormula.modulus_matrix | exact GlobalTheory.CompanionTheory.SW.ProdFormula.modulus_matrix | (intros; apply GlobalTheory.CompanionTheory.SW.ProdFormula.modulus_matrix <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarFundamentalDomainExistsUnitary
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarFundamentalDomainExistsUnitary
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW

theorem haar_fundamental_exist : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → (∃ μ, IsHaarH F E σ M J μ) ∧ ∀ μ, IsHaarH F E σ M J μ → (∃ 𝓕, IsFDH F E σ M J μ 𝓕) ∧ (∃ 𝓕, MeasurableSet 𝓕 ∧ IsFDH F E σ M J μ 𝓕 ∧ ∀ h : HA (AF F) σ J, ∃ γ : HA (AF F) σ J, HA.mat (AF F) σ J γ ∈ HFin (AF F) σ J ∧ γ * h ∈ 𝓕) ∧ ∀ 𝓕, IsFDH F E σ M J μ 𝓕 → μ 𝓕 ≠ 0 := by
  intro F E _ _ _ _ _ σ hσ M J hJ
  obtain ⟨⟨hlc, hsc, ht2⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI := hlc
  haveI := hsc
  haveI := ht2
  obtain ⟨htg, hlcH, hscH, ht2H, hbH, -⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hσ M J hJ (AF F)
  haveI := htg
  haveI := hlcH
  haveI := hscH
  haveI := ht2H
  haveI := hbH
  obtain ⟨hcount, U, hU, hUd⟩ := rational_countable_discrete F E σ hσ M J hJ
  haveI := hcount
  let Γ : Subgroup (HA (AF F) σ J) := HFinIn (AF F) σ J
  have hmem : ∀ γ : HA (AF F) σ J, γ ∈ Γ → HA.mat (AF F) σ J γ ∈ HFin (AF F) σ J :=
    fun γ hγ => Subgroup.mem_subgroupOf.1 hγ
  obtain ⟨-, D, hD, hDs⟩ := GlobalTheory.exists_strict_measurable_fundamental_set_of_discrete
    (HA (AF F) σ J) Γ ⟨U, hU, fun γ hγ hγU => hUd γ hγU (hmem γ hγ)⟩
  have hfd : ∀ μ : Measure (HA (AF F) σ J), IsFDH F E σ M J μ D := fun μ =>
    IsFundamentalDomain.mk' hD.nullMeasurableSet hDs
  refine ⟨⟨Measure.haar, inferInstanceAs (Measure.IsHaarMeasure _)⟩, fun μ hμ => ?_⟩
  haveI : μ.IsHaarMeasure := hμ
  refine ⟨⟨D, hfd μ⟩, ⟨D, hD, hfd μ, fun h => ?_⟩, fun 𝓕 h𝓕 => ?_⟩
  · obtain ⟨γ, hγ, -⟩ := hDs h
    exact ⟨γ, hmem _ γ.2, hγ⟩
  · haveI : MeasurableConstSMul (HFinIn (AF F) σ J) (HA (AF F) σ J) :=
      ⟨fun c => (continuous_const.mul continuous_id :
        Continuous fun x : HA (AF F) σ J => (show HA (AF F) σ J from c.1) * x).measurable⟩
    haveI : SMulInvariantMeasure (HFinIn (AF F) σ J) (HA (AF F) σ J) μ :=
      ⟨fun c s hs => measure_preimage_mul μ (show HA (AF F) σ J from c.1) s⟩
    have h𝓕' : IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕 μ := h𝓕
    exact h𝓕'.measure_ne_zero (NeZero.ne μ)

end GlobalTheory.CompanionTheory.SW
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarFundamentalDomainExistsUnitaryStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_fundamental_domain_exists_unitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → (∃ μ, IsHaarH F E σ M J μ) ∧ ∀ μ, IsHaarH F E σ M J μ → (∃ 𝓕, IsFDH F E σ M J μ 𝓕) ∧ (∃ 𝓕, MeasurableSet 𝓕 ∧ IsFDH F E σ M J μ 𝓕 ∧ ∀ h : HA (AF F) σ J, ∃ γ : HA (AF F) σ J, HA.mat (AF F) σ J γ ∈ HFin (AF F) σ J ∧ γ * h ∈ 𝓕) ∧ ∀ 𝓕, IsFDH F E σ M J μ 𝓕 → μ 𝓕 ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.SW.haar_fundamental_exist | exact GlobalTheory.CompanionTheory.SW.haar_fundamental_exist | (intros; apply GlobalTheory.CompanionTheory.SW.haar_fundamental_exist <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleHaarPiRestrictedProduct
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleHaarPiRestrictedProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.AfBox

theorem eq_of_invariant_of_open {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ ν : Measure G) [ν.IsAddHaarMeasure] [μ.IsAddLeftInvariant] {C : Set G} (hC : IsOpen C)
    (h0 : (0 : G) ∈ C) (hμ : μ C = 1) (hν : ν C = 1) : μ = ν := by
  haveI : IsFiniteMeasureOnCompacts μ := by
    refine ⟨fun K hK => ?_⟩
    have hU : ∀ k : G, IsOpen ((fun x => -k + x) ⁻¹' C) := fun k =>
      hC.preimage (continuous_const.add continuous_id)
    obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover (fun k => (fun x => -k + x) ⁻¹' C)
      (fun k _ => (hU k).mem_nhds (by simpa using h0))
    have hm : ∀ k : G, μ ((fun x => -k + x) ⁻¹' C) = 1 := fun k => by
      rw [measure_preimage_add, hμ]
    calc μ K ≤ μ (⋃ k ∈ t, (fun x => -k + x) ⁻¹' C) := measure_mono ht
      _ ≤ ∑ k ∈ t, μ ((fun x => -k + x) ⁻¹' C) := measure_biUnion_finset_le _ _
      _ = t.card := by simp [hm]
      _ < ⊤ := by simp
  have h := Measure.isAddLeftInvariant_eq_smul μ ν
  have hc : Measure.addHaarScalarFactor μ ν = 1 := by
    have h2 : μ C = (Measure.addHaarScalarFactor μ ν • ν) C := by rw [← h]
    rw [Measure.smul_apply, hμ, hν] at h2
    simpa [ENNReal.smul_def, eq_comm] using h2
  rw [hc, one_smul] at h
  exact h

theorem map_restrict_invariant {G T : Type} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd G]
    [AddCommGroup T] [MeasurableSpace T] [MeasurableAdd T]
    (m : Measure G) [m.IsAddLeftInvariant] (H : AddSubgroup G) (hH : MeasurableSet (H : Set G))
    (ρ : G →+ T) (hρ : Measurable ρ) (hs : ∀ t, ∃ h ∈ H, ρ h = t) :
    ((m.restrict H).map ρ).IsAddLeftInvariant := by
  constructor
  intro g
  obtain ⟨h, hh, rfl⟩ := hs g
  have e : (m.restrict H).map (fun x => h + x) = m.restrict H := by
    have hp : (fun x => h + x) ⁻¹' (H : Set G) = H := by
      ext x
      simp [H.add_mem_cancel_left hh]
    have := Measure.restrict_map (μ := m) (measurable_const_add h) hH
    rw [map_add_left_eq_self, hp] at this
    exact this.symm
  rw [Measure.map_map (measurable_const_add _) hρ]
  have hc : (fun x => ρ h + x) ∘ ρ = ρ ∘ (fun x => h + x) := by
    ext x
    simp
  rw [hc, ← Measure.map_map hρ (measurable_const_add _), e]

theorem measure_inter_preimage {G T : Type} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd G]
    [AddCommGroup T] [TopologicalSpace T] [IsTopologicalAddGroup T] [LocallyCompactSpace T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T]
    (m : Measure G) [m.IsAddLeftInvariant] (H : AddSubgroup G) (hH : MeasurableSet (H : Set G))
    (ρ : G →+ T) (hρ : Measurable ρ) (hs : ∀ t, ∃ h ∈ H, ρ h = t)
    (ν : Measure T) [ν.IsAddHaarMeasure] {C : Set T} (hC : IsOpen C) (h0 : (0 : T) ∈ C)
    (hm : m ((H : Set G) ∩ ρ ⁻¹' C) = 1) (hν : ν C = 1) {B : Set T} (hB : MeasurableSet B) :
    m ((H : Set G) ∩ ρ ⁻¹' B) = ν B := by
  haveI := map_restrict_invariant m H hH ρ hρ hs
  have hmap : ∀ D : Set T, MeasurableSet D → ((m.restrict H).map ρ) D = m ((H : Set G) ∩ ρ ⁻¹' D) := by
    intro D hD
    rw [Measure.map_apply hρ hD, Measure.restrict_apply (hρ hD), Set.inter_comm]
  have he := eq_of_invariant_of_open ((m.restrict H).map ρ) ν hC h0
    (by rw [hmap C hC.measurableSet, hm]) hν
  rw [← he, hmap B hB]

variable {F : Type} [Field F] [NumberField F]

def offS (ι : Type) (S : Finset (HeightOneSpectrum (𝓞 F))) : AddSubgroup (ι → Af F) where
  carrier := {x | ∀ v, v ∉ S → ∀ i, evalV F v (x i) ∈ v.adicCompletionIntegers F}
  add_mem' := fun {a b} ha hb v hv i => by
    simpa using add_mem (ha v hv i) (hb v hv i)
  zero_mem' := fun v _ i => by simp
  neg_mem' := fun {a} ha v hv i => by
    simpa using neg_mem (ha v hv i)

def compS (ι : Type) (S : Finset (HeightOneSpectrum (𝓞 F))) :
    (ι → Af F) →+ ∀ v : S, ι → Fv F v.1 where
  toFun x := fun v i => evalV F v.1 (x i)
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

theorem continuous_compS (ι : Type) (S : Finset (HeightOneSpectrum (𝓞 F))) :
    Continuous (compS (F := F) ι S) :=
  continuous_pi fun v => continuous_pi fun i =>
    (RestrictedProduct.continuous_eval v.1).comp (continuous_apply i)


open Classical in
def liftS {S : Finset (HeightOneSpectrum (𝓞 F))} (t : ∀ v : S, Fv F v.1) : Af F :=
  ⟨fun w => if hw : w ∈ S then t ⟨w, hw⟩ else (0 : Fv F w), by
    filter_upwards [S.finite_toSet.compl_mem_cofinite] with w hw
    have : w ∉ S := by simpa using hw
    simp [this]⟩

open Classical in
theorem evalV_liftS_of_mem {S : Finset (HeightOneSpectrum (𝓞 F))} (t : ∀ v : S, Fv F v.1) (v : S) :
    evalV F v.1 (liftS t) = t v := by
  have : evalV F v.1 (liftS t) = dite (v.1 ∈ S) (fun hw => t ⟨v.1, hw⟩) (fun _ => (0 : Fv F v.1)) := rfl
  rw [this, dite_eq_left v.2]

open Classical in
theorem evalV_liftS_of_notMem {S : Finset (HeightOneSpectrum (𝓞 F))} (t : ∀ v : S, Fv F v.1)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) : evalV F v (liftS t) = 0 := by
  have : evalV F v (liftS t) = dite (v ∈ S) (fun hw => t ⟨v, hw⟩) (fun _ => (0 : Fv F v)) := rfl
  rw [this, dite_eq_right hv]

theorem exists_offS_compS (ι : Type) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (t : ∀ v : S, ι → Fv F v.1) : ∃ h ∈ offS (F := F) ι S, compS ι S h = t := by
  refine ⟨fun i => liftS fun v => t v i, fun v hv i => ?_, ?_⟩
  · rw [evalV_liftS_of_notMem _ hv]
    exact zero_mem (v.adicCompletionIntegers F)
  · funext v i
    exact evalV_liftS_of_mem (fun v => t v i) v

theorem isOpen_integral : IsOpen {x : Af F | ∀ v, x v ∈ v.adicCompletionIntegers F} :=
  RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring _)

theorem isOpen_offS (ι : Type) [Finite ι] (S : Finset (HeightOneSpectrum (𝓞 F))) :
    IsOpen (offS (F := F) ι S : Set (ι → Af F)) := by
  refine AddSubgroup.isOpen_of_mem_nhds _ (g := 0) ?_
  have ho : IsOpen (Set.pi Set.univ fun _ : ι => {x : Af F | ∀ v, x v ∈ v.adicCompletionIntegers F}) :=
    isOpen_set_pi Set.finite_univ fun _ _ => isOpen_integral
  refine Filter.mem_of_superset (ho.mem_nhds ?_) ?_
  · intro i _ v
    exact zero_mem (v.adicCompletionIntegers F)
  · intro x hx v _ i
    exact hx i (Set.mem_univ i) v

theorem pi_box : ∀ (F : Type) [Field F] [NumberField F] (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), (∀ v, IsStdV v (lam v)) → ∀ (lf : Measure (Af F)), lf.IsAddHaarMeasure → lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1 → ∀ (ι : Type) [Fintype ι] (S : Finset (HeightOneSpectrum (𝓞 F))) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (ι → Fv F v)), (∀ v, MeasurableSet (A v)) → (Measure.pi fun _ : ι => lf) {x | (∀ v ∈ S, (fun i => evalV F v (x i)) ∈ A v) ∧ ∀ v, v ∉ S → ∀ i, evalV F v (x i) ∈ v.adicCompletionIntegers F} = ∏ v ∈ S, (Measure.pi fun _ : ι => lam v) (A v) := by
  intro F _ _ lam hlam lf hlf h1 ι _ S A hA
  obtain ⟨-, hAfLC, hAfSC, hAfT2⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  have hloc := fun v => GlobalTheory.T.completion_is_local_ring F v
  haveI : ∀ v, IsTopologicalRing (Fv F v) := fun v => (hloc v).1
  haveI : ∀ v, LocallyCompactSpace (Fv F v) := fun v => (hloc v).2.1
  haveI : ∀ v, SecondCountableTopology (Fv F v) := fun v => (hloc v).2.2.1
  haveI : ∀ v, BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  haveI : ∀ v, (lam v).IsAddHaarMeasure := fun v => (hlam v).1
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  let ν : Measure (∀ v : S, ι → Fv F v.1) := Measure.pi fun v : S => Measure.pi fun _ : ι => lam v.1
  let O : Set (∀ v : S, ι → Fv F v.1) :=
    Set.pi Set.univ fun v : S => Set.pi Set.univ fun _ : ι => (v.1.adicCompletionIntegers F : Set (Fv F v.1))
  have hOo : IsOpen O := isOpen_set_pi Set.finite_univ fun v _ =>
    isOpen_set_pi Set.finite_univ fun _ _ => Valued.isOpen_valuationSubring _
  have hO0 : (0 : ∀ v : S, ι → Fv F v.1) ∈ O := fun v _ i _ => zero_mem (v.1.adicCompletionIntegers F)
  have hνO : ν O = 1 := by
    simp only [ν, O]
    rw [Measure.pi_pi]
    refine Finset.prod_eq_one fun v _ => ?_
    rw [Measure.pi_pi]
    exact Finset.prod_eq_one fun _ _ => (hlam v.1).2
  have hmO : (Measure.pi fun _ : ι => lf) ((offS (F := F) ι S : Set (ι → Af F)) ∩ compS ι S ⁻¹' O) = 1 := by
    have : ((offS (F := F) ι S : Set (ι → Af F)) ∩ compS ι S ⁻¹' O) =
        Set.pi Set.univ fun _ : ι => {x : Af F | ∀ v, x v ∈ v.adicCompletionIntegers F} := by
      ext x
      constructor
      · rintro ⟨hx1, hx2⟩ i _ v
        by_cases hv : v ∈ S
        · exact hx2 ⟨v, hv⟩ (Set.mem_univ _) i (Set.mem_univ _)
        · exact hx1 v hv i
      · intro hx
        exact ⟨fun v _ i => hx i (Set.mem_univ i) v, fun v _ i _ => hx i (Set.mem_univ i) v.1⟩
    rw [this, Measure.pi_pi]
    exact Finset.prod_eq_one fun _ _ => h1
  have hset : {x : ι → Af F | (∀ v ∈ S, (fun i => evalV F v (x i)) ∈ A v) ∧ ∀ v, v ∉ S → ∀ i, evalV F v (x i) ∈ v.adicCompletionIntegers F} =
      (offS (F := F) ι S : Set (ι → Af F)) ∩ compS ι S ⁻¹' (Set.pi Set.univ fun v : S => A v.1) := by
    ext x
    constructor
    · rintro ⟨hx1, hx2⟩
      exact ⟨hx2, fun v _ => hx1 v.1 v.2⟩
    · rintro ⟨hx1, hx2⟩
      exact ⟨fun v hv => hx2 ⟨v, hv⟩ (Set.mem_univ _), hx1⟩
  rw [hset, measure_inter_preimage (Measure.pi fun _ : ι => lf) (offS (F := F) ι S)
    (isOpen_offS ι S).measurableSet (compS ι S) (continuous_compS ι S).measurable
    (exists_offS_compS ι S) ν hOo hO0 hmO hνO (MeasurableSet.univ_pi fun v => hA v.1)]
  simp only [ν]
  rw [Measure.pi_pi]
  exact Finset.prod_coe_sort S fun v => (Measure.pi fun _ : ι => lam v) (A v)

end GlobalTheory.CompanionTheory.SW.AfBox
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleHaarPiRestrictedProductStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_adele_haar_pi_restricted_product : ∀ (F : Type) [Field F] [NumberField F] (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), (∀ v, IsStdV v (lam v)) → ∀ (lf : Measure (Af F)), lf.IsAddHaarMeasure → lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1 → ∀ (ι : Type) [Fintype ι] (S : Finset (HeightOneSpectrum (𝓞 F))) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (ι → Fv F v)), (∀ v, MeasurableSet (A v)) → (Measure.pi fun _ : ι => lf) {x | (∀ v ∈ S, (fun i => evalV F v (x i)) ∈ A v) ∧ ∀ v, v ∉ S → ∀ i, evalV F v (x i) ∈ v.adicCompletionIntegers F} = ∏ v ∈ S, (Measure.pi fun _ : ι => lam v) (A v) := by
  first | exact @GlobalTheory.CompanionTheory.SW.AfBox.pi_box | exact GlobalTheory.CompanionTheory.SW.AfBox.pi_box | (intros; apply GlobalTheory.CompanionTheory.SW.AfBox.pi_box <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.MeasurableFiniteLevelLatticeSet
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.MeasurableFiniteLevelLatticeSet
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.BB

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem measurableSet_natMul_int : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d M : ℕ) (b : Module.Basis (Fin d) F E) (N : ℕ),
    MeasurableSet {X : Fin 1 → Fin M → AF F ⊗[F] E | ∀ v, projV v (projFin X) ∈
      {X : (Fin 1 → Fin M → Fv F v ⊗[F] E) | (fun p i => (N : Fv F v ⊗[F] E) * X p i) ∈ latV b v}} := by
  intro F E _ _ _ _ _ σ hσ d M b N
  obtain ⟨⟨h1, h2, h3⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  obtain ⟨hR, -, -, -, -, -, -, hB, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (AF F)
  have hO := (GlobalTheory.T.adelic_tuple_projections F E σ hσ d b 1 M).2.2.2.2.1 ∅
  have := hB 1 M
  have hc : Continuous (fun (X : Fin 1 → Fin M → AF F ⊗[F] E) (p : Fin 1) (i : Fin M) =>
      (N : AF F ⊗[F] E) * X p i) := by
    fun_prop
  have key : {X : Fin 1 → Fin M → AF F ⊗[F] E | ∀ v, projV v (projFin X) ∈
      {X : (Fin 1 → Fin M → Fv F v ⊗[F] E) | (fun p i => (N : Fv F v ⊗[F] E) * X p i) ∈ latV b v}} =
      (fun (X : Fin 1 → Fin M → AF F ⊗[F] E) (p : Fin 1) (i : Fin M) =>
        (N : AF F ⊗[F] E) * X p i) ⁻¹' intOff b ∅ := by
    ext X
    simp only [Set.mem_setOf_eq, Set.mem_preimage, intOff, Finset.notMem_empty, not_false_eq_true,
      forall_const]
    refine forall_congr' fun v => ?_
    have : projV v (projFin (fun (p : Fin 1) (i : Fin M) => (N : AF F ⊗[F] E) * X p i)) =
        fun p i => (N : Fv F v ⊗[F] E) * projV v (projFin X) p i := by
      funext p i
      simp only [projV, projFin, map_mul, map_natCast]
    rw [this]
  rw [key]
  exact (hO.preimage hc).measurableSet

end GlobalTheory.CompanionTheory.SW.BB
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.MeasurableFiniteLevelLatticeSetStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurable_finite_level_lattice_set : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d M : ℕ) (b : Module.Basis (Fin d) F E) (N : ℕ), MeasurableSet {X : Fin 1 → Fin M → AF F ⊗[F] E | ∀ v, projV v (projFin X) ∈ {X : (Fin 1 → Fin M → Fv F v ⊗[F] E) | (fun p i => (N : Fv F v ⊗[F] E) * X p i) ∈ latV b v}} := by
  first | exact @GlobalTheory.CompanionTheory.SW.BB.measurableSet_natMul_int | exact GlobalTheory.CompanionTheory.SW.BB.measurableSet_natMul_int | (intros; apply GlobalTheory.CompanionTheory.SW.BB.measurableSet_natMul_int <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.QuotientProbabilityMeasure
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.QuotientProbabilityMeasure
noncomputable section
namespace GlobalTheory.CompanionTheory.SW.BB

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem isProbabilityMeasure_prH : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → IsProbabilityMeasure (prH μ 𝓕) := by
  intro F E _ _ _ _ _ σ hσ M J hJ μ 𝓕 hμ h𝓕
  have hfin : μ 𝓕 < ⊤ := ((GlobalTheory.T.unitary_group_finite_volume F E σ hσ M J hJ).2 μ hμ).2 𝓕 h𝓕
  obtain ⟨hlc, hsc, ht2⟩ := (GlobalTheory.CompanionTheory.AdeleTop.adele_top F).1
  obtain ⟨htg, hlcH, hscH, ht2H, hbor, -⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hσ M J hJ (AF F)
  have hcount : Countable (HFinIn (AF F) σ J) := (GlobalTheory.T.arithmetic_unitary_group_discrete F E σ hσ M J hJ).1
  have hne : μ 𝓕 ≠ 0 :=
    (@GlobalTheory.CompanionTheory.SW.LatticeUnimod.unimodular_of_isFundamentalDomain (HA (AF F) σ J) _ _ htg ht2H hlcH hscH _ hbor
      (HFinIn (AF F) σ J) hcount μ hμ 𝓕 h𝓕 hfin).1
  refine ⟨?_⟩
  simp only [prH, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hne hfin.ne

end GlobalTheory.CompanionTheory.SW.BB
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.QuotientProbabilityMeasureStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_probability_measure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → IsProbabilityMeasure (prH μ 𝓕) := by
  first | exact @GlobalTheory.CompanionTheory.SW.BB.isProbabilityMeasure_prH | exact GlobalTheory.CompanionTheory.SW.BB.isProbabilityMeasure_prH | (intros; apply GlobalTheory.CompanionTheory.SW.BB.isProbabilityMeasure_prH <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdelicTraceFormCoordinates
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdelicTraceFormCoordinates
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.BB

theorem finDensity_coord : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (B : Matrix (Fin M × Fin d) (Fin M × Fin d) F), (∀ x y : Fin M → Af F ⊗[F] E, Algebra.trace (Af F) (Af F ⊗[F] E) (hR (Af F) σ J x y) = cv (Af F) b x ⬝ᵥ (B.map (algebraMap F (Af F)) *ᵥ cv (Af F) b y)) → ∀ (lf : Measure (Af F)), lf.IsAddHaarMeasure → ∀ (a : ℕ) (U : Set (Af F)), coordW (Af F) b lf 1 M {X | (∀ v, projV v X ∈ {X : (Fin 1 → Fin M → Fv F v ⊗[F] E) | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v}) ∧ algebraMap F (Af F) (1 / 2) * Algebra.trace (Af F) (Af F ⊗[F] E) (gramR (Af F) σ J X 0 0) ∈ U} = (Measure.pi fun _ : Fin M × Fin d => lf) {x | (∀ i v, ((a : Af F) * x i) v ∈ v.adicCompletionIntegers F) ∧ algebraMap F (Af F) (1 / 2) * (x ⬝ᵥ (B.map (algebraMap F (Af F)) *ᵥ x)) ∈ U} := by
  intro F E _ _ _ _ _ σ hCM M J hJ d b B hB lf hlf a U
  obtain ⟨-, h1, h2, h3⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  obtain ⟨-, hme, hmap⟩ := GlobalTheory.T.coordinate_homeomorph_rank_one_tuples F E σ hCM (Af F) d b lf hlf M
  rw [← hmap, hme.map_apply]
  congr 1
  ext X
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  have hl := GlobalTheory.T.finite_adelic_lattice_membership_iff F E d M b a X
  have ht : gramR (Af F) σ J X 0 0 = hR (Af F) σ J (X 0) (X 0) := rfl
  rw [ht, hB, ← hl]

end GlobalTheory.CompanionTheory.SW.BB
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdelicTraceFormCoordinatesStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_adelic_trace_form_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (B : Matrix (Fin M × Fin d) (Fin M × Fin d) F), (∀ x y : Fin M → Af F ⊗[F] E, Algebra.trace (Af F) (Af F ⊗[F] E) (hR (Af F) σ J x y) = cv (Af F) b x ⬝ᵥ (B.map (algebraMap F (Af F)) *ᵥ cv (Af F) b y)) → ∀ (lf : Measure (Af F)), lf.IsAddHaarMeasure → ∀ (a : ℕ) (U : Set (Af F)), coordW (Af F) b lf 1 M {X | (∀ v, projV v X ∈ {X : (Fin 1 → Fin M → Fv F v ⊗[F] E) | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v}) ∧ algebraMap F (Af F) (1 / 2) * Algebra.trace (Af F) (Af F ⊗[F] E) (gramR (Af F) σ J X 0 0) ∈ U} = (Measure.pi fun _ : Fin M × Fin d => lf) {x | (∀ i v, ((a : Af F) * x i) v ∈ v.adicCompletionIntegers F) ∧ algebraMap F (Af F) (1 / 2) * (x ⬝ᵥ (B.map (algebraMap F (Af F)) *ᵥ x)) ∈ U} := by
  first | exact @GlobalTheory.CompanionTheory.SW.BB.finDensity_coord | exact GlobalTheory.CompanionTheory.SW.BB.finDensity_coord | (intros; apply GlobalTheory.CompanionTheory.SW.BB.finDensity_coord <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramCoordinatesMeasurable
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramCoordinatesMeasurable
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.BB

theorem continuous_gmat_entry {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R]
    (p q : Fin M × Fin d) :
    Continuous fun h : HA R σ J => gmat R σ J b h p q := by
  classical
  have hact := ((GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hσ M J hJ R).2.2.2.2.2 1).1
  have hco : IsHomeomorph fun (y : R ⊗[F] E) (k : Fin d) =>
      (Algebra.TensorProduct.basis R b).repr y k :=
    (GlobalTheory.T.tensor_locally_compact_ring F E σ hσ R).2.2.2.2.2.2.1 d b
  let X : Fin 1 → Fin M → R ⊗[F] E := fun _ => Pi.single q.1 (inclR R (b q.2))
  have h1 : Continuous fun h : HA R σ J => actW R σ J h X :=
    hact.comp (continuous_id.prodMk continuous_const)
  have h2 : Continuous fun h : HA R σ J => actW R σ J h X 0 p.1 :=
    (continuous_apply p.1).comp ((continuous_apply (0 : Fin 1)).comp h1)
  have h3 : Continuous fun h : HA R σ J =>
      (Algebra.TensorProduct.basis R b).repr (actW R σ J h X 0 p.1) p.2 :=
    (continuous_apply p.2).comp (hco.continuous.comp h2)
  refine h3.congr fun h => ?_
  simp [gmat, actW, actTup, X, Matrix.mulVec_single]

theorem ginf_gfin_measurable : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), IsHomeomorph e → (∀ w p q, Measurable fun ω => ginf e σ J b ω w p q) ∧ (∀ p q, Measurable fun ω => gfin σ J b ω p q) := by
  intro F E _ _ _ _ _ σ hσ M J hJ d b e he
  obtain ⟨⟨hlc, hsc, ht2⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  obtain ⟨htg, -, -, -, hbor, -⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hσ M J hJ (AF F)
  have hinv : ∀ p q, Continuous fun ω : HA (AF F) σ J => gmat (AF F) σ J b ω⁻¹ p q := fun p q =>
    (continuous_gmat_entry σ hσ J hJ b (AF F) p q).comp continuous_inv
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  refine ⟨fun w p q => ?_, fun p q => ?_⟩
  · have hf : Continuous fun t : AF F => e (fstA F t) w :=
      (continuous_apply w).comp (he.continuous.comp continuous_fst)
    exact (hf.comp (hinv p q)).measurable
  · have hf : Continuous fun t : AF F => sndA F t := continuous_snd
    exact (hf.comp (hinv p q)).measurable

end GlobalTheory.CompanionTheory.SW.BB
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramCoordinatesMeasurableStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_coordinates_measurable : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), IsHomeomorph e → (∀ w p q, Measurable fun ω => ginf e σ J b ω w p q) ∧ (∀ p q, Measurable fun ω => gfin σ J b ω p q) := by
  first | exact @GlobalTheory.CompanionTheory.SW.BB.ginf_gfin_measurable | exact GlobalTheory.CompanionTheory.SW.BB.ginf_gfin_measurable | (intros; apply GlobalTheory.CompanionTheory.SW.BB.ginf_gfin_measurable <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicHaarScalingByRealIdele
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicHaarScalingByRealIdele
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.AdelicFlow

theorem map_eq_smul_of_scale {V W G : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    [AddCommGroup W] [TopologicalSpace W] [IsTopologicalAddGroup W] [LocallyCompactSpace W]
    [SecondCountableTopology W] [MeasurableSpace W] [BorelSpace W]
    [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [MeasurableSpace G]
    [BorelSpace G]
    (Φ : G ≃ₜ+ V × W) (φ : G → G) (t : ℝ) (ht : t ≠ 0)
    (h : ∀ x, Φ (φ x) = (t • (Φ x).1, (Φ x).2))
    (μ : Measure G) [μ.IsAddHaarMeasure] :
    μ.map φ = ENNReal.ofReal |(t ^ Module.finrank ℝ V)⁻¹| • μ := by
  set k := ENNReal.ofReal |(t ^ Module.finrank ℝ V)⁻¹| with hk
  have hΦ : Measurable Φ := Φ.continuous.measurable
  have hΦs : Measurable Φ.symm := Φ.symm.continuous.measurable
  let ν : Measure V := Measure.addHaar
  let ρ : Measure W := Measure.addHaar
  let ψ : V × W → V × W := Prod.map (fun v => t • v) id
  have hψ : Measurable ψ := (measurable_const_smul t).prodMap measurable_id
  haveI : (μ.map Φ).IsAddHaarMeasure := Φ.isAddHaarMeasure_map μ
  have hc := Measure.isAddLeftInvariant_eq_smul (μ.map Φ) (ν.prod ρ)
  set c := Measure.addHaarScalarFactor (μ.map Φ) (ν.prod ρ) with hcdef
  have hπ : (μ.map Φ).map ψ = k • μ.map Φ := by
    have h1 : (ν.prod ρ).map ψ = k • ν.prod ρ := by
      have := Measure.map_prod_map ν ρ (f := fun v : V => t • v) (g := (id : W → W))
        (measurable_const_smul t) measurable_id
      rw [show (ν.prod ρ).map ψ = (ν.map fun v => t • v).prod (ρ.map id) from this.symm,
        Measure.map_addHaar_smul ν ht, Measure.map_id, Measure.prod_smul_left]
    rw [hc, Measure.map_smul c hψ.aemeasurable, h1, smul_comm]
  have hφ : φ = Φ.symm ∘ ψ ∘ Φ := by
    funext x
    apply Φ.injective
    simp [h]
    rfl
  have hμ : (μ.map Φ).map Φ.symm = μ := by
    rw [Measure.map_map hΦs hΦ]
    simp
  calc μ.map φ = ((μ.map Φ).map ψ).map Φ.symm := by
        rw [Measure.map_map hΦs hψ, Measure.map_map (hΦs.comp hψ) hΦ, hφ]; rfl
    _ = k • μ := by rw [hπ, Measure.map_smul k hΦs.aemeasurable, hμ]

section Adelic

variable (F : Type) [Field F] [NumberField F]

noncomputable def coords [IsTotallyReal F] (ι : Type) :
    (ι → AdeleRing (𝓞 F) F) ≃ₜ+
      (ι → InfinitePlace F → ℝ) × (ι → FiniteAdeleRing (𝓞 F) F) where
  toFun x := (fun i w => InfinitePlace.Completion.ringEquivRealOfIsReal
      (IsTotallyReal.isReal w) ((x i).1 w), fun i => (x i).2)
  invFun p := fun i => (show AdeleRing (𝓞 F) F from
    (fun w => (InfinitePlace.Completion.ringEquivRealOfIsReal
      (IsTotallyReal.isReal w)).symm (p.1 i w), p.2 i))
  left_inv x := by
    funext i
    refine Prod.ext ?_ rfl
    funext w
    exact RingEquiv.symm_apply_apply _ _
  right_inv p := by
    refine Prod.ext ?_ rfl
    funext i w
    exact RingEquiv.apply_symm_apply _ _
  map_add' x y := by
    refine Prod.ext ?_ rfl
    funext i w
    exact map_add (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)) _ _
  continuous_toFun := by
    refine Continuous.prodMk (continuous_pi fun i => continuous_pi fun w => ?_)
      (continuous_pi fun i => ?_)
    · exact (InfinitePlace.Completion.isometryEquivRealOfIsReal
        (IsTotallyReal.isReal w)).continuous.comp
        ((continuous_apply w).comp (continuous_fst.comp (continuous_apply i)))
    · exact continuous_snd.comp (continuous_apply i)
  continuous_invFun := by
    refine continuous_pi fun i => Continuous.prodMk (continuous_pi fun w => ?_) ?_
    · exact (InfinitePlace.Completion.isometryEquivRealOfIsReal
        (IsTotallyReal.isReal w)).symm.continuous.comp
        ((continuous_apply w).comp ((continuous_apply i).comp continuous_fst))
    · exact (continuous_apply i).comp continuous_snd

theorem coord_theta [IsTotallyReal F] (θ : ℝ →+* InfiniteAdeleRing F) (t : ℝ)
    (w : InfinitePlace F) :
    InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w) (θ t w) = t := by
  have h : ((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w) :
      w.Completion →+* ℝ).comp ((Pi.evalRingHom (fun v : InfinitePlace F => v.Completion) w).comp θ))
      = RingHom.id ℝ := Subsingleton.elim _ _
  exact DFunLike.congr_fun h t

theorem card_places [IsTotallyReal F] :
    Fintype.card (InfinitePlace F) = Module.finrank ℚ F := by
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyReal.nrComplexPlaces_eq_zero, add_zero, IsTotallyReal.finrank]

end Adelic

theorem map_scalar : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F →
    ∀ θ : ℝ →+* InfiniteAdeleRing F, Continuous θ →
    ∀ [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)] (ι : Type)
      [Fintype ι] (μ : Measure (ι → AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure] (t : ℝ), 0 < t →
      μ.map (fun x i => (show AdeleRing (𝓞 F) F from (θ t, 1)) * x i) =
        ENNReal.ofReal ((t ^ (Module.finrank ℚ F * Fintype.card ι))⁻¹) • μ := by
  intro F _ _ hF θ _ _ _ ι _ μ _ t ht
  haveI := hF
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  letI : MeasurableSpace (FiniteAdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  have key := map_eq_smul_of_scale (coords F ι)
    (fun x i => (show AdeleRing (𝓞 F) F from (θ t, 1)) * x i) t ht.ne' ?_ μ
  · have hd : Module.finrank ℝ (ι → InfinitePlace F → ℝ) =
        Module.finrank ℚ F * Fintype.card ι := by
      rw [Module.finrank_pi_fintype]
      simp [Module.finrank_fintype_fun_eq_card, card_places F, mul_comm]
    rw [key, hd, abs_of_pos (inv_pos.2 (pow_pos ht _))]
  · intro x
    refine Prod.ext ?_ ?_
    · funext i w
      show InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)
        (θ t w * (x i).1 w) = t * _
      rw [map_mul, coord_theta]
      rfl
    · funext i
      exact one_mul _

end GlobalTheory.CompanionTheory.AdelicFlow
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicHaarScalingByRealIdeleStatement
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_haar_scaling_by_real_idele : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ θ : ℝ →+* InfiniteAdeleRing F, Continuous θ → ∀ [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)] (ι : Type) [Fintype ι] (μ : Measure (ι → AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure] (t : ℝ), 0 < t → μ.map (fun x i => (show AdeleRing (𝓞 F) F from (θ t, 1)) * x i) = ENNReal.ofReal ((t ^ (Module.finrank ℚ F * Fintype.card ι))⁻¹) • μ := by
  first | exact @GlobalTheory.CompanionTheory.AdelicFlow.map_scalar | exact GlobalTheory.CompanionTheory.AdelicFlow.map_scalar | (intros; apply GlobalTheory.CompanionTheory.AdelicFlow.map_scalar <;> assumption)
end
end
