module

public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductSupport

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitHomeoApply
open MeasureTheory Topology
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SplitExtLat

variable {P G₁ : Type} [Group P] [Group G₁]

def splitMap (ι : G₁ →* P) (π : P →* G₁) : π.ker × G₁ → P := fun z => (z.1 : P) * ι z.2

def kerPart (ι : G₁ →* P) (π : P →* G₁) (h : ∀ u, π (ι u) = u) (p : P) : π.ker :=
  ⟨p * (ι (π p))⁻¹, by simp [MonoidHom.mem_ker, h]⟩

def splitEquiv (ι : G₁ →* P) (π : P →* G₁) (h : ∀ u, π (ι u) = u) : π.ker × G₁ ≃ P where
  toFun := splitMap ι π
  invFun p := (kerPart ι π h p, π p)
  left_inv z := by
    obtain ⟨⟨m, hm⟩, u⟩ := z
    have hm' : π m = 1 := hm
    ext <;> simp [splitMap, kerPart, hm', h]
  right_inv p := by simp [splitMap, kerPart]

def splitHomeo [TopologicalSpace P] [IsTopologicalGroup P] [TopologicalSpace G₁]
    (ι : G₁ →* P) (π : P →* G₁) (hι : Continuous ι) (hπ : Continuous π)
    (h : ∀ u, π (ι u) = u) : π.ker × G₁ ≃ₜ P where
  toEquiv := splitEquiv ι π h
  continuous_toFun := by
    change Continuous fun z : π.ker × G₁ => (z.1 : P) * ι z.2
    fun_prop
  continuous_invFun := by
    change Continuous fun p => (kerPart ι π h p, π p)
    refine Continuous.prodMk (Continuous.subtype_mk ?_ _) hπ
    fun_prop

@[simp] theorem splitHomeo_apply [TopologicalSpace P] [IsTopologicalGroup P] [TopologicalSpace G₁]
    (ι : G₁ →* P) (π : P →* G₁) (hι : Continuous ι) (hπ : Continuous π)
    (h : ∀ u, π (ι u) = u) (z : π.ker × G₁) :
    splitHomeo ι π hι hπ h z = (z.1 : P) * ι z.2 := rfl

theorem mul_split (ι : G₁ →* P) (π : P →* G₁) (h : ∀ u, π (ι u) = u) (g : P) (m : π.ker) (u : G₁) :
    g * ((m : P) * ι u) =
      ((kerPart ι π h g * MulAut.conjNormal (ι (π g)) m : π.ker) : P) * ι (π g * u) := by
  simp only [kerPart, Subgroup.coe_mul, MulAut.conjNormal_apply, map_mul]
  group

theorem continuous_conj [TopologicalSpace P] [IsTopologicalGroup P] [TopologicalSpace G₁]
    (ι : G₁ →* P) (π : P →* G₁) (hι : Continuous ι) :
    Continuous fun z : G₁ × π.ker => MulAut.conjNormal (ι z.1) z.2 := by
  refine Continuous.subtype_mk (f := fun z : G₁ × π.ker => ι z.1 * (z.2 : P) * (ι z.1)⁻¹) ?_ _
  fun_prop

end GlobalTheory.CompanionTheory.SplitExtLat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModularCharacterTrivialFiniteCovolume
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModularCharacterTrivialFiniteCovolume
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix Pointwise

namespace GlobalTheory.CompanionTheory.SW.CharacterTrivial

theorem eq_one_of_isFundamentalDomain :
    ∀ (G₁ : Type) [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁]
      [SecondCountableTopology G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁]
      (Γ₁ : Subgroup G₁) [Countable Γ₁] (μ₁ : Measure G₁) [μ₁.IsHaarMeasure] (𝓕₁ : Set G₁),
      IsFundamentalDomain Γ₁ 𝓕₁ μ₁ → μ₁ 𝓕₁ < ⊤ → ∀ δ : G₁ →* ℝ≥0, Measurable δ →
        (∀ γ ∈ Γ₁, δ γ = 1) → ∀ u, δ u = 1 := by
  intro G₁ _ _ _ _ _ _ _ _ Γ₁ _ μ₁ _ 𝓕₁ h𝓕₁ hfin δ hδ hγ
  obtain ⟨h0, hR, -⟩ :=
    GlobalTheory.CompanionTheory.SW.LatticeUnimod.unimodular_of_isFundamentalDomain G₁ Γ₁ μ₁ 𝓕₁ h𝓕₁ hfin
  have hinv : ∀ u, δ u * δ u⁻¹ = 1 := fun u => by rw [← map_mul, mul_inv_cancel, map_one]
  have hpos : ∀ u, 0 < (δ u : ℝ) := by
    intro u
    have h : δ u ≠ 0 := left_ne_zero_of_mul_eq_one (hinv u)
    exact_mod_cast pos_iff_ne_zero.2 h
  have hδr : Measurable (fun u => (δ u : ℝ)) := measurable_coe_nnreal_real.comp hδ
  have hind : ∀ (A B : Set G₁) (x y : G₁), (x ∈ A ↔ y ∈ B) →
      A.indicator (1 : G₁ → ℝ≥0∞) x = B.indicator (1 : G₁ → ℝ≥0∞) y := by
    intro A B x y h
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (h.1 hx)]; rfl
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun hy => hx (h.2 hy))]
  have hbig : ∀ u₀, 1 < δ u₀ → False := by
    intro u₀ ht
    obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = δ u₀ := ⟨_, rfl⟩
    have ht1 : 1 < t := by rw [htdef]; exact_mod_cast ht
    have ht0 : 0 < t := by linarith
    let C : ℤ → Set G₁ := fun n => (fun u => (δ u : ℝ)) ⁻¹' Set.Ico (t ^ n) (t ^ (n + 1))
    have hCm : ∀ n, MeasurableSet (C n) := fun n => hδr measurableSet_Ico
    have hmem : ∀ n u, u * u₀ ∈ C (n + 1) ↔ u ∈ C n := by
      intro n u
      have e : (δ (u * u₀) : ℝ) = δ u * t := by rw [map_mul, htdef]; push_cast; rfl
      simp only [C, Set.mem_preimage, Set.mem_Ico, e]
      rw [zpow_add_one₀ ht0.ne' n, zpow_add_one₀ ht0.ne' (n + 1),
        mul_le_mul_iff_of_pos_right ht0, mul_lt_mul_iff_of_pos_right ht0, zpow_add_one₀ ht0.ne' n]
    have hshift : ∀ n, (μ₁.restrict 𝓕₁) (C n) = (μ₁.restrict 𝓕₁) (C (n + 1)) := by
      intro n
      have hinvar : ∀ γ ∈ Γ₁, ∀ u, (C (n + 1)).indicator (1 : G₁ → ℝ≥0∞) (γ * u) =
          (C (n + 1)).indicator (1 : G₁ → ℝ≥0∞) u := by
        intro γ hg u
        have e : γ * u ∈ C (n + 1) ↔ u ∈ C (n + 1) := by
          simp only [C, Set.mem_preimage, map_mul, hγ γ hg, one_mul]
        exact hind _ _ _ _ e
      have e := GlobalTheory.CompanionTheory.SW.Averaging.setLIntegral_mul_right_eq μ₁ Γ₁ 𝓕₁ h𝓕₁
        ((C (n + 1)).indicator 1) hinvar u₀
      have e' : (fun u => (C (n + 1)).indicator (1 : G₁ → ℝ≥0∞) (u * u₀)) =
          (C n).indicator 1 := by
        funext u
        exact hind _ _ _ _ (hmem n u)
      rw [e', lintegral_indicator_one (hCm n), lintegral_indicator_one (hCm (n + 1))] at e
      exact e
    have hconst : ∀ n, (μ₁.restrict 𝓕₁) (C n) = (μ₁.restrict 𝓕₁) (C 0) := by
      intro n
      induction n using Int.induction_on with
      | zero => rfl
      | succ i ih => rw [← hshift]; exact ih
      | pred i ih =>
        rw [← ih, hshift (-(i : ℤ) - 1)]
        congr 2
        ring
    have hU : ⋃ n, C n = Set.univ := by
      refine Set.eq_univ_of_forall fun u => Set.mem_iUnion.2 ?_
      obtain ⟨n, hn⟩ := exists_mem_Ico_zpow (hpos u) ht1
      exact ⟨n, hn⟩
    have hdisj : Pairwise (Function.onFun Disjoint C) := by
      intro m n hmn
      refine Set.disjoint_left.2 fun u h₁ h₂ => hmn ?_
      have a : t ^ n < t ^ (m + 1) := lt_of_le_of_lt h₂.1 h₁.2
      have b : t ^ m < t ^ (n + 1) := lt_of_le_of_lt h₁.1 h₂.2
      have a' := (zpow_lt_zpow_iff_right₀ ht1).1 a
      have b' := (zpow_lt_zpow_iff_right₀ ht1).1 b
      omega
    have hsum : μ₁ 𝓕₁ = ∑' _ : ℤ, (μ₁.restrict 𝓕₁) (C 0) := by
      rw [← Measure.restrict_apply_univ 𝓕₁, ← hU, measure_iUnion hdisj hCm]
      exact tsum_congr hconst
    by_cases hz : (μ₁.restrict 𝓕₁) (C 0) = 0
    · rw [hz, tsum_zero] at hsum
      exact h0 hsum
    · rw [ENNReal.tsum_const_eq_top_of_ne_zero hz] at hsum
      exact hfin.ne hsum
  intro u
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · refine hbig u⁻¹ ?_
    by_contra hle
    have h1 : δ u * δ u⁻¹ < 1 * 1 :=
      mul_lt_mul'' hlt (lt_of_le_of_ne (not_lt.1 hle) ?_) zero_le zero_le
    · rw [hinv u, one_mul] at h1
      exact lt_irrefl _ h1
    · intro e
      have := hinv u
      rw [e, mul_one] at this
      exact hne this
  · exact hbig u hgt

end GlobalTheory.CompanionTheory.SW.CharacterTrivial
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModularCharacterTrivialFiniteCovolumeStatement
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix Pointwise
alias GlobalTheory.T.modular_character_trivial_finite_covolume := GlobalTheory.CompanionTheory.SW.CharacterTrivial.eq_one_of_isFundamentalDomain
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicFundamentalDomainSplit
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicFundamentalDomainSplit
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix Pointwise

namespace GlobalTheory.CompanionTheory.SplitExtLat

theorem exists_borel_section_ker :
    ∀ (P G₁ : Type) [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [LocallyCompactSpace P] [SecondCountableTopology P] [T2Space P] [MeasurableSpace P] [BorelSpace P] [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁] (ι : G₁ →* P) (π : P →* G₁) (hι : Continuous ι) (hπ : Continuous π) (hπι : ∀ u, π (ι u) = u) (Γ : Subgroup P) [Countable Γ], (∃ U ∈ 𝓝 (1 : P), ∀ γ ∈ Γ, γ ∈ U → γ = 1) → (∃ K : Set P, IsCompact K ∧ ∀ m ∈ π.ker, ∃ γ ∈ Γ, π γ = 1 ∧ γ * m ∈ K) → ∃ D : Set π.ker, MeasurableSet D ∧ (∀ x : π.ker, ∃! g : Γ.subgroupOf π.ker, g • x ∈ D) ∧ ∀ (ν : Measure π.ker) [ν.IsHaarMeasure], IsFundamentalDomain (Γ.subgroupOf π.ker) D ν ∧ ν D ≠ 0 ∧ ν D < ⊤ := by
  intro P G₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ι π hι hπ hπι Γ _ hU hK
  obtain ⟨U, hU, hU1⟩ := hU
  obtain ⟨K, hKc, hK⟩ := hK
  have hcl : IsClosed (π.ker : Set P) := by
    have : (π.ker : Set P) = π ⁻¹' {1} := by
      ext x
      simp [MonoidHom.mem_ker]
    rw [this]
    exact isClosed_singleton.preimage hπ
  have hemb : IsClosedEmbedding (Subtype.val : π.ker → P) := hcl.isClosedEmbedding_subtypeVal
  haveI : LocallyCompactSpace π.ker := hemb.locallyCompactSpace
  haveI : SecondCountableTopology π.ker := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : BorelSpace π.ker := Subtype.borelSpace _
  haveI : Countable (Γ.subgroupOf π.ker) :=
    Function.Injective.countable (f := fun h : Γ.subgroupOf π.ker =>
      (⟨((h : π.ker) : P), h.2⟩ : Γ)) (fun a b hab => by
        have h1 : ((a : π.ker) : P) = ((b : π.ker) : P) := congrArg (fun x : Γ => (x : P)) hab
        exact Subtype.ext (Subtype.ext h1))
  haveI : DiscreteTopology (Γ.subgroupOf π.ker) := by
    refine discreteTopology_of_isOpen_singleton_one ?_
    have hc : Continuous fun h : Γ.subgroupOf π.ker => ((h : π.ker) : P) :=
      continuous_subtype_val.comp continuous_subtype_val
    have : ({1} : Set (Γ.subgroupOf π.ker)) =
        (fun h : Γ.subgroupOf π.ker => ((h : π.ker) : P)) ⁻¹' interior U := by
      ext h
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      constructor
      · rintro rfl
        exact mem_interior_iff_mem_nhds.2 hU
      · intro hh
        have h1 : ((h : π.ker) : P) = 1 :=
          hU1 _ (Subgroup.mem_subgroupOf.1 h.2) (interior_subset hh)
        exact Subtype.ext (Subtype.ext h1)
    rw [this]
    exact isOpen_interior.preimage hc
  obtain ⟨D, hDm, hDu, hDf⟩ := GlobalTheory.exists_isFundamentalDomain_subgroup (Γ.subgroupOf π.ker)
  refine ⟨D, hDm, hDu, fun ν _ => ⟨hDf ν, (hDf ν).measure_ne_zero (NeZero.ne ν), ?_⟩⟩
  have hKc' : IsCompact ((Subtype.val : π.ker → P) ⁻¹' K) := hemb.isCompact_preimage hKc
  refine lt_of_le_of_lt
    (GlobalTheory.measure_le_of_isFundamentalDomain_of_ae_covers (hDf ν)
      (D' := (Subtype.val : π.ker → P) ⁻¹' K) (.of_forall fun m => ?_)) hKc'.measure_lt_top
  obtain ⟨γ, hγ, hπγ, hmem⟩ := hK m m.2
  have hγk : γ ∈ π.ker := hπγ
  refine ⟨⟨⟨γ, hγk⟩, Subgroup.mem_subgroupOf.2 hγ⟩, ?_⟩
  exact hmem

end GlobalTheory.CompanionTheory.SplitExtLat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicFundamentalDomainSplitStatement
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix Pointwise
alias GlobalTheory.T.parabolic_fundamental_domain_split := GlobalTheory.CompanionTheory.SplitExtLat.exists_borel_section_ker
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicHaarDecomposition
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicHaarDecomposition
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix Pointwise

namespace GlobalTheory.CompanionTheory.SplitExtLat

theorem conj_haar_character :
    ∀ (P G₁ : Type) [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [LocallyCompactSpace P] [SecondCountableTopology P] [T2Space P] [MeasurableSpace P] [BorelSpace P] [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁] (ι : G₁ →* P) (π : P →* G₁) (hι : Continuous ι) (hπ : Continuous π) (hπι : ∀ u, π (ι u) = u) (Γ : Subgroup P) (Γ₁ : Subgroup G₁) [Countable Γ] [Countable Γ₁], (∀ u ∈ Γ₁, ι u ∈ Γ) → ∀ (ν : Measure π.ker) [ν.IsHaarMeasure] (D : Set π.ker), MeasurableSet D → IsFundamentalDomain (Γ.subgroupOf π.ker) D ν → ν D ≠ 0 → ν D < ⊤ → ∃ δ : G₁ →* ℝ≥0, Measurable δ ∧ (∀ γ ∈ Γ₁, δ γ = 1) ∧ ∀ u, Measure.map (fun m : π.ker => MulAut.conjNormal (ι u) m) ν = δ u • ν := by
  intro P G₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ι π hι hπ hπι Γ Γ₁ _ _ hΓ ν _ D hDm hD hD0 hDtop
  classical
  have hKc : IsClosed (π.ker : Set P) := by
    rw [MonoidHom.coe_ker]
    exact isClosed_singleton.preimage hπ
  haveI : LocallyCompactSpace π.ker := hKc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology π.ker :=
    TopologicalSpace.Subtype.secondCountableTopology (π.ker : Set P)
  have hcont : ∀ g : P, Continuous (fun m : π.ker => MulAut.conjNormal g m) := by
    intro g
    apply continuous_induced_rng.2
    have h1 : (Subtype.val ∘ fun m : π.ker => MulAut.conjNormal g m) = fun m : π.ker => g * (m : P) * g⁻¹ := by
      funext m
      simp only [Function.comp_apply, MulAut.conjNormal_apply]
    rw [h1]
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const
  have hsymm : ∀ g : P, ⇑(MulEquiv.symm (MulAut.conjNormal g : MulAut π.ker)) =
      fun m => MulAut.conjNormal g⁻¹ m := by
    intro g
    funext m
    rw [MulEquiv.symm_apply_eq]
    apply Subtype.ext
    simp only [MulAut.conjNormal_apply]
    group
  have hex : ∀ u : G₁, ∃ c : ℝ≥0,
      Measure.map (fun m : π.ker => MulAut.conjNormal (ι u) m) ν = c • ν := by
    intro u
    haveI : (Measure.map (fun m : π.ker => MulAut.conjNormal (ι u) m) ν).IsHaarMeasure :=
      MulEquiv.isHaarMeasure_map ν (MulAut.conjNormal (ι u) : MulAut π.ker) (hcont _)
        (by convert hcont (ι u)⁻¹ using 1; exact hsymm _)
    exact ⟨_, Measure.isMulLeftInvariant_eq_smul _ ν⟩
  choose a ha using hex
  have hcancel : ∀ b c : ℝ≥0, (b : ℝ≥0∞) * ν D = (c : ℝ≥0∞) * ν D → b = c := by
    intro b c h
    exact_mod_cast (ENNReal.mul_left_inj hD0 hDtop.ne).mp h
  have hpre : ∀ v (S : Set π.ker), MeasurableSet S →
      ν ((fun m : π.ker => MulAut.conjNormal (ι v) m) ⁻¹' S) = (a v : ℝ≥0∞) * ν S := by
    intro v S hS
    rw [← Measure.map_apply (hcont _).measurable hS, ha v, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  have hcomp : ∀ u v, (fun m : π.ker => MulAut.conjNormal (ι (u * v)) m) ⁻¹' D =
      (fun m : π.ker => MulAut.conjNormal (ι v) m) ⁻¹'
        ((fun m : π.ker => MulAut.conjNormal (ι u) m) ⁻¹' D) := by
    intro u v
    ext m
    simp only [Set.mem_preimage, map_mul, MulAut.mul_apply]
  have hmul : ∀ u v, a (u * v) = a u * a v := by
    intro u v
    apply hcancel
    rw [← hpre (u * v) D hDm, hcomp, hpre v _ ((hcont _).measurable hDm), hpre u D hDm,
      ENNReal.coe_mul]
    ring
  haveI : Countable (Γ.subgroupOf π.ker) := by
    have hinj : Function.Injective (fun x : Γ.subgroupOf π.ker =>
        (⟨((x : π.ker) : P), Subgroup.mem_subgroupOf.1 x.2⟩ : Γ)) := by
      intro x y h
      apply Subtype.ext
      apply Subtype.ext
      simp only [Subtype.mk.injEq] at h
      exact h
    exact hinj.countable
  haveI : MeasurableConstSMul (Γ.subgroupOf π.ker) π.ker :=
    ⟨fun c => by
      show Measurable (fun x : π.ker => (c : π.ker) * x)
      exact measurable_id'.const_mul _⟩
  haveI : SMulInvariantMeasure (Γ.subgroupOf π.ker) π.ker ν :=
    ⟨fun c s _ => by
      show ν ((fun x : π.ker => (c : π.ker) * x) ⁻¹' s) = ν s
      exact measure_preimage_mul ν _ s⟩
  have hΓ1 : ∀ γ ∈ Γ₁, a γ = 1 := by
    intro γ hγ
    have hg : ι γ ∈ Γ := hΓ γ hγ
    have hqmp : Measure.QuasiMeasurePreserving
        (fun m : π.ker => MulAut.conjNormal (ι γ) m) ν ν := by
      refine ⟨(hcont _).measurable.aemeasurable, ?_⟩
      rw [ha γ]
      intro s hs
      rw [Measure.smul_apply, hs, smul_zero]
    obtain ⟨e, he⟩ : ∃ e : Γ.subgroupOf π.ker → Γ.subgroupOf π.ker,
        ∀ s, ((e s : π.ker) : P) = (ι γ)⁻¹ * ((s : π.ker) : P) * ι γ := by
      refine ⟨fun s => ⟨⟨(ι γ)⁻¹ * ((s : π.ker) : P) * ι γ, ?_⟩, ?_⟩, fun s => rfl⟩
      · rw [MonoidHom.mem_ker]
        simp [MonoidHom.mem_ker.1 (s : π.ker).2]
      · exact Subgroup.mem_subgroupOf.2
          (Γ.mul_mem (Γ.mul_mem (Γ.inv_mem hg) (Subgroup.mem_subgroupOf.1 s.2)) hg)
    have hebij : Function.Bijective e := by
      constructor
      · intro s t hst
        have h1 := congrArg (fun x : Γ.subgroupOf π.ker => ((x : π.ker) : P)) hst
        simp only [he, mul_left_inj, mul_right_inj] at h1
        apply Subtype.ext
        apply Subtype.ext
        exact h1
      · intro t
        obtain ⟨s, hs⟩ : ∃ s : Γ.subgroupOf π.ker,
            ((s : π.ker) : P) = ι γ * ((t : π.ker) : P) * (ι γ)⁻¹ := by
          refine ⟨⟨⟨ι γ * ((t : π.ker) : P) * (ι γ)⁻¹, ?_⟩, ?_⟩, rfl⟩
          · rw [MonoidHom.mem_ker]
            simp [MonoidHom.mem_ker.1 (t : π.ker).2]
          · exact Subgroup.mem_subgroupOf.2
              (Γ.mul_mem (Γ.mul_mem hg (Subgroup.mem_subgroupOf.1 t.2)) (Γ.inv_mem hg))
        refine ⟨s, Subtype.ext (Subtype.ext ?_)⟩
        rw [he, hs]
        group
    have hsemi : ∀ s : Γ.subgroupOf π.ker, Function.Semiconj
        (fun m : π.ker => MulAut.conjNormal (ι γ) m) (fun x => e s • x) (fun x => s • x) := by
      intro s x
      apply Subtype.ext
      simp only [MulAut.conjNormal_apply, Subgroup.smul_def, smul_eq_mul, Subgroup.coe_mul, he]
      group
    have hfd := hD.preimage_of_equiv hqmp hebij hsemi
    have hmeq : ν D = ν ((fun m : π.ker => MulAut.conjNormal (ι γ) m) ⁻¹' D) :=
      hD.measure_eq hfd
    apply hcancel
    rw [← hpre γ D hDm, ← hmeq, ENNReal.coe_one, one_mul]
  have hFc : Continuous (fun p : G₁ × π.ker => MulAut.conjNormal (ι p.1) p.2) := by
    apply continuous_induced_rng.2
    have h1 : (Subtype.val ∘ fun p : G₁ × π.ker => MulAut.conjNormal (ι p.1) p.2) =
        fun p => ι p.1 * (p.2 : P) * (ι p.1)⁻¹ := by
      funext p
      simp only [Function.comp_apply, MulAut.conjNormal_apply]
    rw [h1]
    exact ((hι.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)).mul
      (hι.comp continuous_fst).inv
  have hE : MeasurableSet ((fun p : G₁ × π.ker => MulAut.conjNormal (ι p.1) p.2) ⁻¹' D) :=
    hFc.measurable hDm
  have ha_eq : a = fun u =>
      (ν ((fun m : π.ker => MulAut.conjNormal (ι u) m) ⁻¹' D) / ν D).toNNReal := by
    funext u
    rw [hpre u D hDm, ENNReal.mul_div_cancel_right hD0 hDtop.ne, ENNReal.toNNReal_coe]
  have hmeas : Measurable a := by
    rw [ha_eq]
    exact ((measurable_measure_prodMk_left hE).div_const _).ennreal_toNNReal
  exact ⟨{ toFun := a, map_one' := hΓ1 1 Γ₁.one_mem, map_mul' := hmul }, hmeas, hΓ1,
    fun u => ha u⟩

end GlobalTheory.CompanionTheory.SplitExtLat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicHaarDecompositionStatement
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix Pointwise
alias GlobalTheory.T.parabolic_haar_decomposition := GlobalTheory.CompanionTheory.SplitExtLat.conj_haar_character
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicFundamentalDomainVolume
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicFundamentalDomainVolume
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix Pointwise

namespace GlobalTheory.CompanionTheory.SplitExtLat

theorem ae_exists_smul_mem_image_prod :
    ∀ (P G₁ : Type) [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [LocallyCompactSpace P] [SecondCountableTopology P] [T2Space P] [MeasurableSpace P] [BorelSpace P] [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁] (ι : G₁ →* P) (π : P →* G₁) (hι : Continuous ι) (hπ : Continuous π) (hπι : ∀ u, π (ι u) = u) (Γ : Subgroup P) (Γ₁ : Subgroup G₁) [Countable Γ₁], (∀ u ∈ Γ₁, ι u ∈ Γ) → ∀ (ν : Measure π.ker) [ν.IsHaarMeasure] (μ₁ : Measure G₁) [μ₁.IsHaarMeasure] (D : Set π.ker) (𝓕₁ : Set G₁), (∀ x : π.ker, ∃! g : Γ.subgroupOf π.ker, g • x ∈ D) → IsFundamentalDomain Γ₁ 𝓕₁ μ₁ → ∀ᵐ p ∂(Measure.map (GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι) (ν.prod μ₁)), ∃ γ : Γ, γ • p ∈ (GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι '' (D ×ˢ 𝓕₁)) := by
  intro P G₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ι π hι hπ hπι Γ Γ₁ _ hΓ ν _ μ₁ _ D 𝓕₁ hD h𝓕
  rw [(GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι).measurableEmbedding.ae_map_iff]
  have hcov : ∀ᵐ z ∂(ν.prod μ₁), ∃ γ₁ : Γ₁, γ₁ • z.2 ∈ 𝓕₁ :=
    Measure.quasiMeasurePreserving_snd.ae h𝓕.ae_covers
  filter_upwards [hcov] with z hz
  obtain ⟨m, u⟩ := z
  obtain ⟨γ₁, hγ₁⟩ := hz
  obtain ⟨δ, hδ, -⟩ := hD (GlobalTheory.CompanionTheory.SplitExtLat.kerPart ι π hπι (ι γ₁) *
    MulAut.conjNormal (ι (π (ι γ₁))) m)
  have hδΓ : ((δ : π.ker) : P) ∈ Γ := Subgroup.mem_subgroupOf.mp δ.2
  refine ⟨⟨((δ : π.ker) : P) * ι γ₁, Γ.mul_mem hδΓ (hΓ γ₁ γ₁.2)⟩,
    ⟨(δ • (GlobalTheory.CompanionTheory.SplitExtLat.kerPart ι π hπι (ι γ₁) * MulAut.conjNormal (ι (π (ι γ₁))) m),
      γ₁ • u), ⟨hδ, hγ₁⟩, ?_⟩⟩
  simp only [GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo_apply, Subgroup.smul_def, smul_eq_mul,
    Subgroup.coe_mul]
  rw [mul_assoc (((δ : π.ker) : P)) (ι (γ₁ : G₁)), GlobalTheory.CompanionTheory.SplitExtLat.mul_split ι π hπι (ι γ₁) m u,
    hπι, Subgroup.coe_mul, mul_assoc]

end GlobalTheory.CompanionTheory.SplitExtLat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicFundamentalDomainVolumeStatement
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix Pointwise
alias GlobalTheory.T.parabolic_fundamental_domain_volume := GlobalTheory.CompanionTheory.SplitExtLat.ae_exists_smul_mem_image_prod
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicIntegralUnfolding
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicIntegralUnfolding
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix Pointwise

namespace GlobalTheory.CompanionTheory.SplitExtLat

theorem aedisjoint_smul_image_prod : ∀ (P G₁ : Type) [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [LocallyCompactSpace P] [SecondCountableTopology P] [T2Space P] [MeasurableSpace P] [BorelSpace P] [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁] (ι : G₁ →* P) (π : P →* G₁) (hι : Continuous ι) (hπ : Continuous π) (hπι : ∀ u, π (ι u) = u) (Γ : Subgroup P) (Γ₁ : Subgroup G₁) [Countable Γ₁], (∀ γ ∈ Γ, π γ ∈ Γ₁) → ∀ (ν : Measure π.ker) [ν.IsHaarMeasure] (μ₁ : Measure G₁) [μ₁.IsHaarMeasure] (D : Set π.ker) (𝓕₁ : Set G₁), (∀ x : π.ker, ∃! g : Γ.subgroupOf π.ker, g • x ∈ D) → IsFundamentalDomain Γ₁ 𝓕₁ μ₁ → ∀ γ : Γ, γ ≠ 1 → AEDisjoint (Measure.map (GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι) (ν.prod μ₁)) (γ • (GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι '' (D ×ˢ 𝓕₁))) (GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι '' (D ×ˢ 𝓕₁)) := by
  intro P G₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ι π hι hπ hπι Γ Γ₁ _ hΓ ν _ μ₁ _ D 𝓕₁ hD h𝓕 γ hγ
  have hker : ∀ z : π.ker, π (z : P) = 1 := fun z => MonoidHom.mem_ker.1 z.2
  have hfa : ∀ z : π.ker × G₁, GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι z = (z.1 : P) * ι z.2 :=
    GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo_apply ι π hι hπ hπι
  set f := GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι with hf
  have hπx : ∀ z : π.ker × G₁, π (f z) = z.2 := by
    intro z
    rw [hfa, map_mul, hker, one_mul, hπι]
  let g : Γ₁ := ⟨π γ, hΓ γ γ.2⟩
  have hsub : γ • (f '' (D ×ˢ 𝓕₁)) ∩ f '' (D ×ˢ 𝓕₁) ⊆ π ⁻¹' (g • 𝓕₁ ∩ 𝓕₁) := by
    rintro x ⟨⟨y, ⟨z, ⟨-, hz⟩, rfl⟩, rfl⟩, ⟨z', ⟨-, hz'⟩, hzx⟩⟩
    dsimp only at hzx ⊢
    have hγπ : π (γ • f z) = π γ * z.2 := by
      rw [Subgroup.smul_def, smul_eq_mul, map_mul, hπx]
    refine ⟨⟨z.2, hz, ?_⟩, ?_⟩
    · dsimp only
      rw [hγπ, Subgroup.smul_def, smul_eq_mul]
    · rw [← hzx, hπx]
      exact hz'
  by_cases hg : g = 1
  · have hγk : (γ : P) ∈ π.ker := MonoidHom.mem_ker.2 (congrArg Subtype.val hg)
    suffices hempty : γ • (f '' (D ×ˢ 𝓕₁)) ∩ f '' (D ×ˢ 𝓕₁) = ∅ by
      show Measure.map f (ν.prod μ₁) _ = 0
      rw [hempty, measure_empty]
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨⟨y, ⟨z, ⟨hz1, hz2⟩, rfl⟩, rfl⟩, ⟨z', ⟨hz1', hz2'⟩, hzx⟩⟩
    dsimp only at hzx
    have h2 : z'.2 = z.2 := by
      have := congrArg π hzx
      rw [hπx, Subgroup.smul_def, smul_eq_mul, map_mul, hπx, MonoidHom.mem_ker.1 hγk, one_mul] at this
      exact this
    have h1 : (z'.1 : P) = (γ : P) * z.1 := by
      have := hzx
      rw [hfa, Subgroup.smul_def, smul_eq_mul, hfa, h2, ← mul_assoc] at this
      exact mul_right_cancel this
    let γk : Γ.subgroupOf π.ker := ⟨⟨γ, hγk⟩, Subgroup.mem_subgroupOf.2 γ.2⟩
    obtain ⟨g₀, -, huniq⟩ := hD z.1
    have e1 : (1 : Γ.subgroupOf π.ker) = g₀ := huniq 1 (by show (1 : Γ.subgroupOf π.ker) • z.1 ∈ D; rw [one_smul]; exact hz1)
    have e2 : γk = g₀ := huniq γk (by
      show γk • z.1 ∈ D
      have : γk • z.1 = z'.1 := Subtype.ext (by rw [Subgroup.smul_def, smul_eq_mul, Subgroup.coe_mul]; exact h1.symm)
      rw [this]
      exact hz1')
    apply hγ
    have := congrArg (fun t : Γ.subgroupOf π.ker => ((t : π.ker) : P)) (e2.trans e1.symm)
    exact Subtype.ext this
  · have hN : μ₁ (g • 𝓕₁ ∩ 𝓕₁) = 0 := by
      have := h𝓕.aedisjoint hg
      simp only [Function.onFun, one_smul] at this
      exact this
    have hpre : f ⁻¹' (π ⁻¹' (g • 𝓕₁ ∩ 𝓕₁)) = Set.univ ×ˢ (g • 𝓕₁ ∩ 𝓕₁) := by
      ext z
      simp only [Set.mem_preimage, hπx, Set.mem_prod, Set.mem_univ, true_and]
    have hmap : Measure.map f (ν.prod μ₁) (π ⁻¹' (g • 𝓕₁ ∩ 𝓕₁)) = 0 := by
      rw [show Measure.map f (ν.prod μ₁) (π ⁻¹' (g • 𝓕₁ ∩ 𝓕₁)) = (ν.prod μ₁) (f ⁻¹' (π ⁻¹' (g • 𝓕₁ ∩ 𝓕₁))) from
        f.toMeasurableEquiv.map_apply _, hpre, Measure.prod_prod, hN, mul_zero]
    exact measure_mono_null hsub hmap

end GlobalTheory.CompanionTheory.SplitExtLat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicIntegralUnfoldingStatement
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix Pointwise
alias GlobalTheory.T.parabolic_integral_unfolding := GlobalTheory.CompanionTheory.SplitExtLat.aedisjoint_smul_image_prod
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicLeviIntegralFormula
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicLeviIntegralFormula
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix Pointwise

namespace GlobalTheory.CompanionTheory.SplitExtLat

theorem setLIntegral_splitHomeo_image_prod
    (P G₁ : Type) [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [LocallyCompactSpace P]
    [SecondCountableTopology P] [T2Space P] [MeasurableSpace P] [BorelSpace P]
    [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁]
    [SecondCountableTopology G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁]
    (ι : G₁ →* P) (π : P →* G₁) (hι : Continuous ι) (hπ : Continuous π)
    (hπι : ∀ u, π (ι u) = u) (ν : Measure π.ker) [ν.IsHaarMeasure]
    (μ₁ : Measure G₁) [μ₁.IsHaarMeasure] (D : Set π.ker) (𝓕₁ : Set G₁) :
    MeasurableSet D → NullMeasurableSet 𝓕₁ μ₁ →
      NullMeasurableSet (GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι '' (D ×ˢ 𝓕₁))
        (Measure.map (GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι) (ν.prod μ₁)) ∧
      ∀ f : P → ℝ≥0∞, Measurable f →
        ∫⁻ p in (GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι '' (D ×ˢ 𝓕₁)), f p
            ∂(Measure.map (GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι) (ν.prod μ₁)) =
          ∫⁻ u in 𝓕₁, ∫⁻ m in D, f ((m : P) * ι u) ∂ν ∂μ₁ := by
  intro hD h𝓕
  have hker : IsClosed ((π.ker : Set P)) := by
    rw [MonoidHom.coe_ker]
    exact isClosed_singleton.preimage hπ
  have hsc : SecondCountableTopology π.ker :=
    TopologicalSpace.Subtype.secondCountableTopology (π.ker : Set P)
  have hlc : LocallyCompactSpace π.ker := hker.locallyCompactSpace
  have hσc : SigmaCompactSpace π.ker := sigmaCompactSpace_of_locallyCompact_secondCountable
  have hνσ : SigmaFinite ν := Measure.IsHaarMeasure.sigmaFinite ν
  set e := GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι with he
  have hemb : MeasurableEmbedding e := e.measurableEmbedding
  refine ⟨?_, ?_⟩
  · rw [e.image_eq_preimage_symm]
    exact (hD.nullMeasurableSet.prod h𝓕).preimage
      (MeasurableEquiv.quasiMeasurePreserving_symm (ν.prod μ₁) e.toMeasurableEquiv)
  · intro f hf
    rw [hemb.restrict_map, Set.preimage_image_eq _ e.injective, hemb.lintegral_map,
      ← Measure.prod_restrict, lintegral_prod_symm']
    · rfl
    · exact hf.comp hemb.measurable

end GlobalTheory.CompanionTheory.SplitExtLat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicLeviIntegralFormulaStatement
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix Pointwise
alias GlobalTheory.T.parabolic_levi_integral_formula := GlobalTheory.CompanionTheory.SplitExtLat.setLIntegral_splitHomeo_image_prod
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicQuotientMeasure
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicQuotientMeasure
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix Pointwise

namespace GlobalTheory.CompanionTheory.SplitExtLat

theorem isHaarMeasure_map_splitHomeo :
    ∀ (P G₁ : Type) [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [LocallyCompactSpace P] [SecondCountableTopology P] [T2Space P] [MeasurableSpace P] [BorelSpace P] [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁] (ι : G₁ →* P) (π : P →* G₁) (hι : Continuous ι) (hπ : Continuous π) (hπι : ∀ u, π (ι u) = u) (ν : Measure π.ker) [ν.IsHaarMeasure] (μ₁ : Measure G₁) [μ₁.IsHaarMeasure], (∀ u, Measure.map (fun m : π.ker => MulAut.conjNormal (ι u) m) ν = ν) → (Measure.map (GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι) (ν.prod μ₁)).IsHaarMeasure := by
  intro P G₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ι π hι hπ hπι ν _ μ₁ _ hconj
  have hclosed : IsClosed (π.ker : Set P) := by
    have hk : (π.ker : Set P) = π ⁻¹' {1} := by
      ext p
      simp
    rw [hk]
    exact isClosed_singleton.preimage hπ
  have : LocallyCompactSpace π.ker := hclosed.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology π.ker :=
    TopologicalSpace.Subtype.secondCountableTopology (π.ker : Set P)
  have : SigmaCompactSpace π.ker := inferInstance
  have : SigmaFinite ν := inferInstance
  set Φ := splitHomeo ι π hι hπ hπι with hΦdef
  have hΦm : Measurable Φ := Φ.continuous.measurable
  have hinv : (Measure.map Φ (ν.prod μ₁)).IsMulLeftInvariant := by
    refine ⟨fun g => ?_⟩
    set k₀ := kerPart ι π hπι g
    have hcm : Measurable (fun m : π.ker => MulAut.conjNormal (ι (π g)) m) :=
      ((continuous_conj ι π hι).comp (Continuous.prodMk_right (π g))).measurable
    have hfm : Measurable (fun m : π.ker => k₀ * MulAut.conjNormal (ι (π g)) m) :=
      (measurable_const_mul k₀).comp hcm
    have hhm : Measurable (fun u : G₁ => π g * u) := measurable_const_mul _
    have e1 : Measure.map (fun m : π.ker => k₀ * MulAut.conjNormal (ι (π g)) m) ν = ν := by
      have hsplit : (fun m : π.ker => k₀ * MulAut.conjNormal (ι (π g)) m) =
          (fun x => k₀ * x) ∘ (fun m : π.ker => MulAut.conjNormal (ι (π g)) m) := rfl
      rw [hsplit, ← Measure.map_map (measurable_const_mul k₀) hcm, hconj, map_mul_left_eq_self]
    have e2 : Measure.map (fun u : G₁ => π g * u) μ₁ = μ₁ := map_mul_left_eq_self μ₁ _
    have hcomp : (fun x => g * x) ∘ Φ =
        Φ ∘ Prod.map (fun m : π.ker => k₀ * MulAut.conjNormal (ι (π g)) m) (fun u : G₁ => π g * u) := by
      funext z
      simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, hΦdef, splitHomeo_apply]
      exact mul_split ι π hπι g z.1 z.2
    rw [Measure.map_map (measurable_const_mul g) hΦm, hcomp, ← Measure.map_map hΦm (hfm.prodMap hhm),
      ← Measure.map_prod_map ν μ₁ hfm hhm, e1, e2]
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : P)
  have hKm : MeasurableSet K := hK.measurableSet
  refine Measure.isHaarMeasure_of_isCompact_nonempty_interior _ K hK ⟨1, mem_interior_iff_mem_nhds.mpr hK1⟩ ?_ ?_
  · rw [Measure.map_apply hΦm hKm]
    have hopen : IsOpen (Φ ⁻¹' interior K) := isOpen_interior.preimage Φ.continuous
    have hne : (Φ ⁻¹' interior K).Nonempty := by
      obtain ⟨z, hz⟩ := Φ.surjective 1
      refine ⟨z, ?_⟩
      show Φ z ∈ interior K
      rw [hz]
      exact mem_interior_iff_mem_nhds.mpr hK1
    exact ((hopen.measure_pos _ hne).trans_le (measure_mono (Set.preimage_mono interior_subset))).ne'
  · rw [Measure.map_apply hΦm hKm]
    exact (Φ.isCompact_preimage.mpr hK).measure_lt_top.ne

end GlobalTheory.CompanionTheory.SplitExtLat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicQuotientMeasureStatement
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix Pointwise
alias GlobalTheory.T.parabolic_quotient_measure := GlobalTheory.CompanionTheory.SplitExtLat.isHaarMeasure_map_splitHomeo
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitExtensionFundamentalDomain
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix Pointwise

namespace GlobalTheory.CompanionTheory.SplitExtLat

theorem exists_haar_fundamentalDomain : ∀ (P G₁ : Type) [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [LocallyCompactSpace P] [SecondCountableTopology P] [T2Space P] [MeasurableSpace P] [BorelSpace P] [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁] (ι : G₁ →* P) (π : P →* G₁), Continuous ι → Continuous π → (∀ u, π (ι u) = u) → ∀ (Γ : Subgroup P) (Γ₁ : Subgroup G₁) [Countable Γ] [Countable Γ₁], (∃ U ∈ 𝓝 (1 : P), ∀ γ ∈ Γ, γ ∈ U → γ = 1) → (∀ u ∈ Γ₁, ι u ∈ Γ) → (∀ γ ∈ Γ, π γ ∈ Γ₁) → ∀ (μ₁ : Measure G₁) [μ₁.IsHaarMeasure] (𝓕₁ : Set G₁), IsFundamentalDomain Γ₁ 𝓕₁ μ₁ → μ₁ 𝓕₁ < ⊤ → (∃ K : Set P, IsCompact K ∧ ∀ m ∈ π.ker, ∃ γ ∈ Γ, π γ = 1 ∧ γ * m ∈ K) → ∃ (ν : Measure π.ker) (𝓕N : Set π.ker) (μP : Measure P) (𝓕P : Set P), ν.IsHaarMeasure ∧ IsFundamentalDomain (Γ.subgroupOf π.ker) 𝓕N ν ∧ ν 𝓕N ≠ 0 ∧ ν 𝓕N < ⊤ ∧ μP.IsHaarMeasure ∧ IsFundamentalDomain Γ 𝓕P μP ∧ μP 𝓕P < ⊤ ∧ ∀ f : P → ℝ≥0∞, Measurable f → ∫⁻ p in 𝓕P, f p ∂μP = ∫⁻ u in 𝓕₁, ∫⁻ m in 𝓕N, f ((m : P) * ι u) ∂ν ∂μ₁ := by
  intro P G₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ι π hι hπ hπι Γ Γ₁ _ _ hU hΓ₁ hΓ μ₁ _ 𝓕₁ h𝓕₁ hfin hK
  have hcl : IsClosed (π.ker : Set P) := by
    have : (π.ker : Set P) = π ⁻¹' {1} := by ext; simp [MonoidHom.mem_ker]
    rw [this]; exact isClosed_singleton.preimage hπ
  haveI : LocallyCompactSpace π.ker := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  obtain ⟨D, hDm, hDu, hD⟩ := GlobalTheory.T.parabolic_fundamental_domain_split P G₁ ι π hι hπ hπι Γ hU hK
  let ν : Measure π.ker := Measure.haar
  obtain ⟨hνF, hν0, hνfin⟩ := hD ν
  obtain ⟨δ, hδm, hδΓ, hδ⟩ := GlobalTheory.T.parabolic_haar_decomposition P G₁ ι π hι hπ hπι Γ Γ₁ hΓ₁ ν D hDm hνF hν0 hνfin
  have hδ1 := GlobalTheory.T.modular_character_trivial_finite_covolume G₁ Γ₁ μ₁ 𝓕₁ h𝓕₁ hfin δ hδm hδΓ
  have hmap : ∀ u, Measure.map (fun m : π.ker => MulAut.conjNormal (ι u) m) ν = ν := by
    intro u; rw [hδ u, hδ1 u, one_smul]
  have hH := GlobalTheory.T.parabolic_quotient_measure P G₁ ι π hι hπ hπι ν μ₁ hmap
  obtain ⟨hnull, hint⟩ := GlobalTheory.T.parabolic_levi_integral_formula P G₁ ι π hι hπ hπι ν μ₁ D 𝓕₁ hDm h𝓕₁.nullMeasurableSet
  have hcov := GlobalTheory.T.parabolic_fundamental_domain_volume P G₁ ι π hι hπ hπι Γ Γ₁ hΓ₁ ν μ₁ D 𝓕₁ hDu h𝓕₁
  have hdis := GlobalTheory.T.parabolic_integral_unfolding P G₁ ι π hι hπ hπι Γ Γ₁ hΓ ν μ₁ D 𝓕₁ hDu h𝓕₁
  refine ⟨ν, D, _, _, inferInstance, hνF, hν0, hνfin, hH,
    IsFundamentalDomain.mk'' hnull hcov hdis (fun γ => (measurePreserving_smul γ _).quasiMeasurePreserving), ?_, hint⟩
  have h1 := hint (fun _ => 1) measurable_const
  simp only [lintegral_const, one_mul, Measure.restrict_apply_univ, setLIntegral_one] at h1
  rw [h1]
  exact ENNReal.mul_lt_top hνfin hfin

end GlobalTheory.CompanionTheory.SplitExtLat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitExtensionFundamentalDomainStatement
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix
alias GlobalTheory.T.split_extension_fundamental_domain := GlobalTheory.CompanionTheory.SplitExtLat.exists_haar_fundamentalDomain
end
