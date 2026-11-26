module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.StdChar
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovolumeFrames.StepSize
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.FrameStd
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.HermitianMeasureSplitting
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFrameStabilizerHaarNormalisedFibreMeasure
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CocompactOfMemIffAdelic

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicTorusMeasureStabiliserHaar
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicTorusMeasureStabiliserHaar
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory

theorem omT_stab_exist : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → Formalism.MainNotions.UnusedSlot34.SWa1 F E σ n J → Formalism.L2.SG.Pf.NcWeil.StabilizerFirstChernCompatibility F E σ n J → ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ a : ℕ, 1 ≤ a → 2 * a < n → ∀ (X0 : Fin a → Fin n → E) (hT : ∀ i j, σ (gramE σ J X0 j i) = gramE σ J X0 i j), (gramE σ J X0).det ≠ 0 → ∀ μ : Measure (HA (AF F) σ J), μ.IsHaarMeasure → ∃ (νX : Measure (Fin a → Fin n → AF F ⊗[F] E)) (μ' : Measure (stabT (AF F) σ J X0)), Formalism.L2.SG.Volumes.IsOmT F E σ n J ψ (gramE σ J X0) hT νX ∧ μ'.IsHaarMeasure ∧ Formalism.L2.SG.Volumes.IsCompatT F E σ n J X0 μ μ' νX := by
  intro F E _ _ _ _ _ σ hE n J hJ ha hc ψ hψ a ha1 ha2 X0 hT hdet μ hμ
  obtain ⟨νX, hν⟩ := PI.VolStabS.Assembly.exOmT_holds F E σ hE n J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ
  obtain ⟨μ', hμ'H, hμ'C⟩ := PI.VolStabS.exStab_of_nu PI.VolStabS.Assembly.nuInv_holds
    PI.VolStabS.nuFin_holds
    (PI.VolStabS.nuNeZero_of_dens PI.VolStabS.archPos_holds PI.VolStabS.locPos_holds
      (PI.VolStabS.densAA_of_open PI.VolStabS.volAA_holds PI.VolStabS.hensAA_holds
        PI.VolStabS.idxH_holds PI.VolStabS.cntAA_holds) PI.VolStabS.qvSum_holds)
    F E σ hE n J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μ hμ νX hν
  exact ⟨νX, μ', hν, hμ'H, hμ'C⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicTorusMeasureStabiliserHaarStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelicTorusMeasure_stabiliserHaar : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → Formalism.MainNotions.UnusedSlot34.SWa1 F E σ n J → Formalism.L2.SG.Pf.NcWeil.StabilizerFirstChernCompatibility F E σ n J → ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ a : ℕ, 1 ≤ a → 2 * a < n → ∀ (X0 : Fin a → Fin n → E) (hT : ∀ i j, σ (gramE σ J X0 j i) = gramE σ J X0 i j), (gramE σ J X0).det ≠ 0 → ∀ μ : Measure (HA (AF F) σ J), μ.IsHaarMeasure → ∃ (νX : Measure (Fin a → Fin n → AF F ⊗[F] E)) (μ' : Measure (stabT (AF F) σ J X0)), Formalism.L2.SG.Volumes.IsOmT F E σ n J ψ (gramE σ J X0) hT νX ∧ μ'.IsHaarMeasure ∧ Formalism.L2.SG.Volumes.IsCompatT F E σ n J X0 μ μ' νX := by
  first | exact @GlobalTheory.omT_stab_exist | exact GlobalTheory.omT_stab_exist | (intros; apply GlobalTheory.omT_stab_exist <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsHaarMeasureUnipotentRadicalCovolumeOne
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FundamentalDomainCovol
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFundamentalDomainSmulIff
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct ENNReal

namespace GlobalTheory.ClosedSubgroupCovol

section General

variable {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [MeasurableSpace K]
  [BorelSpace K] (Γ : Subgroup K) (μ : Measure K)

theorem measure_eq [Countable Γ] [μ.IsMulLeftInvariant] {s t : Set K}
    (hs : IsFundamentalDomain Γ s μ) (ht : IsFundamentalDomain Γ t μ) : μ s = μ t := hs.measure_eq ht


theorem measure_ne_zero [Countable Γ] [μ.IsHaarMeasure] {s : Set K}
    (hs : IsFundamentalDomain Γ s μ) : μ s ≠ 0 :=
  hs.measure_ne_zero (NeZero.ne μ)

theorem measure_le_of_cover [Countable Γ] [μ.IsMulLeftInvariant] {s : Set K}
    (hs : IsFundamentalDomain Γ s μ) {C : Set K}
    (hcov : ∀ m : K, ∃ γ ∈ Γ, ∃ k ∈ C, m = γ * k) : μ s ≤ μ C := by
  open Pointwise in
  calc μ s ≤ μ (⋃ g : Γ, g • toMeasurable μ C ∩ s) := by
          refine measure_mono fun m hm => ?_
          obtain ⟨γ, hγ, k, hk, rfl⟩ := hcov m
          refine Set.mem_iUnion.2 ⟨⟨γ, hγ⟩, ?_, hm⟩
          exact ⟨k, subset_toMeasurable μ C hk, rfl⟩
      _ ≤ ∑' g : Γ, μ (g • toMeasurable μ C ∩ s) := measure_iUnion_le _
      _ = μ (toMeasurable μ C) := (hs.measure_eq_tsum _).symm
      _ = μ C := measure_toMeasurable C


omit [TopologicalSpace K] [IsTopologicalGroup K] [BorelSpace K] in
theorem isFundamentalDomain_smul_iff {c : NNReal} (hc : c ≠ 0) (s : Set K) :
    IsFundamentalDomain Γ s (c • μ) ↔ IsFundamentalDomain Γ s μ := by
  have hc' : (c : ENNReal) ≠ 0 := by exact_mod_cast hc
  constructor
  · intro h
    refine h.mono fun t ht => ?_
    rw [smul_apply, ENNReal.smul_def, smul_eq_mul, mul_eq_zero] at ht
    exact ht.resolve_left hc'
  · intro h
    refine h.mono fun t ht => ?_
    rw [smul_apply, ht, smul_zero]

private theorem exists_measurableSet_unique_smul_mem_of_discrete {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G]
    [OpensMeasurableSpace G] (Γ : Subgroup G) {V : Set G} (hV : IsOpen V) (h1 : (1 : G) ∈ V)
    (hΓV : ∀ γ ∈ Γ, γ ∈ V → γ = 1) :
    ∃ s : Set G, MeasurableSet s ∧ ∀ x : G, ∃! g : Γ, g • x ∈ s := by
  classical

  obtain ⟨U, hUo, hU1, hUV⟩ := exists_open_nhds_one_split (hV.mem_nhds h1)
  let W : Set G := U ∩ (fun u => u⁻¹) ⁻¹' U
  have hWo : IsOpen W := hUo.inter (hUo.preimage continuous_inv)
  have hW1 : (1 : G) ∈ W := ⟨hU1, by simp only [Set.mem_preimage, inv_one]; exact hU1⟩
  have hWW : ∀ a ∈ W, ∀ b ∈ W, a * b⁻¹ ∈ V := fun a ha b hb => hUV a ha.1 b⁻¹ hb.2

  let A : G → Set G := fun g => (fun x => x * g⁻¹) ⁻¹' W
  have hAo : ∀ g, IsOpen (A g) := fun g => hWo.preimage (continuous_mul_const _)
  have hcov : ⋃ g, A g = Set.univ := Set.eq_univ_of_forall fun x =>
    Set.mem_iUnion.2 ⟨x, by simp only [A, Set.mem_preimage, mul_inv_cancel]; exact hW1⟩
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable A hAo
  have hmemT : ∀ x, ∃ g ∈ T, x ∈ A g := fun x => by
    have hx : x ∈ ⋃ g ∈ T, A g := by rw [hTU, hcov]; exact Set.mem_univ x
    obtain ⟨g, hg, hx'⟩ := Set.mem_iUnion₂.1 hx
    exact ⟨g, hg, hx'⟩
  have hTne : T.Nonempty := by
    obtain ⟨g, hg, -⟩ := hmemT 1
    exact ⟨g, hg⟩
  obtain ⟨f, hf⟩ := hTc.exists_eq_range hTne
  let B : ℕ → Set G := fun i => A (f i)
  have hBo : ∀ i, IsOpen (B i) := fun i => hAo _
  have hBcov : ∀ x, ∃ i, x ∈ B i := by
    intro x
    obtain ⟨g, hgT, hx⟩ := hmemT x
    rw [hf] at hgT
    obtain ⟨i, rfl⟩ := hgT
    exact ⟨i, hx⟩

  have hinj : ∀ i y (δ : Γ), y ∈ B i → δ • y ∈ B i → δ = 1 := by
    intro i y δ hy hδy
    have hm := hWW (δ • y * (f i)⁻¹) hδy (y * (f i)⁻¹) hy
    have he : δ • y * (f i)⁻¹ * (y * (f i)⁻¹)⁻¹ = (δ : G) := by
      simp only [Subgroup.smul_def, smul_eq_mul]
      group
    rw [he] at hm
    exact Subtype.ext (hΓV _ δ.2 hm)

  let E : ℕ → Set G := fun j => ⋃ γ : Γ, (fun x => γ • x) ⁻¹' B j
  have hEo : ∀ j, IsOpen (E j) := fun j => isOpen_iUnion fun γ => (hBo j).preimage
    (by simpa only [Subgroup.smul_def, smul_eq_mul] using continuous_const_mul (γ : G))
  have hE : ∀ j y, y ∈ E j ↔ ∃ δ : Γ, δ • y ∈ B j := fun j y => by
    simp only [E, Set.mem_iUnion, Set.mem_preimage]

  let s : Set G := ⋃ i, (B i \ ⋃ (j : ℕ) (_ : j < i), E j)
  have hs : ∀ y, y ∈ s ↔ ∃ i, y ∈ B i ∧ ∀ j < i, ∀ δ : Γ, δ • y ∉ B j := by
    intro y
    simp only [s, Set.mem_iUnion, Set.mem_sdiff, not_exists]
    constructor
    · rintro ⟨i, hi, hn⟩
      exact ⟨i, hi, fun j hj δ hδ => hn j hj ((hE j y).2 ⟨δ, hδ⟩)⟩
    · rintro ⟨i, hi, hn⟩
      refine ⟨i, hi, fun j hj hy => ?_⟩
      obtain ⟨δ, hδ⟩ := (hE j y).1 hy
      exact hn j hj δ hδ
  refine ⟨s, MeasurableSet.iUnion fun i => (hBo i).measurableSet.diff
    (isOpen_iUnion fun j => isOpen_iUnion fun _ => hEo j).measurableSet, fun x => ?_⟩
  have hP : ∃ i, ∃ γ : Γ, γ • x ∈ B i := by
    obtain ⟨i, hi⟩ := hBcov x
    exact ⟨i, 1, by simpa only [one_smul] using hi⟩
  obtain ⟨γ, hγ⟩ := Nat.find_spec hP
  refine ⟨γ, (hs _).2 ⟨_, hγ, fun j hj δ hδ => Nat.find_min hP hj ⟨δ * γ, by rwa [mul_smul]⟩⟩,
    fun γ' hγ' => ?_⟩
  obtain ⟨i', hi', hmin'⟩ := (hs _).1 hγ'
  have hle : Nat.find hP ≤ i' := Nat.find_min' hP ⟨γ', hi'⟩
  have hge : i' ≤ Nat.find hP := by
    by_contra hlt
    exact hmin' _ (not_le.1 hlt) (γ * γ'⁻¹) (by rw [mul_smul, inv_smul_smul]; exact hγ)
  rw [le_antisymm hge hle] at hi'
  have h1' := hinj _ (γ • x) (γ' * γ⁻¹) hγ (by rw [mul_smul, inv_smul_smul]; exact hi')
  exact mul_inv_eq_one.1 h1'

end General

theorem countable_and_exists_domain (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E)
    (K : Subgroup (HA (AF F) σ J)) :
    IsTopologicalGroup K ∧ BorelSpace K ∧
    Countable (Subgroup.subgroupOf (G := HA (AF F) σ J) (HFinIn (AF F) σ J) K) ∧
    ∀ μ : Measure K, ∃ 𝓕 : Set K,
      IsFundamentalDomain (Subgroup.subgroupOf (G := HA (AF F) σ J) (HFinIn (AF F) σ J) K) 𝓕 μ := by
  obtain ⟨hc, hd, -⟩ := GlobalTheory.RationalUnitaryDomains.isDiscreteWithDomains_ratPts' F E σ n J
  change Countable (HFinIn (AF F) σ J) at hc
  change DiscreteTopology (HFinIn (AF F) σ J) at hd

  obtain ⟨t, ht, hteq⟩ := isOpen_induced_iff.1 (isOpen_discrete ({1} : Set (HFinIn (AF F) σ J)))
  have ht1 : (1 : HA (AF F) σ J) ∈ t := by
    have h : (1 : HFinIn (AF F) σ J) ∈ Subtype.val ⁻¹' t := by rw [hteq]; exact Set.mem_singleton _
    exact h
  have htone : ∀ h ∈ HFinIn (AF F) σ J, h ∈ t → h = 1 := by
    intro h hh hht
    have h' : (⟨h, hh⟩ : HFinIn (AF F) σ J) ∈ Subtype.val ⁻¹' t := hht
    rw [hteq] at h'
    exact congrArg Subtype.val (Set.mem_singleton_iff.1 h')
  have hcnt : Countable (Subgroup.subgroupOf (G := HA (AF F) σ J) (HFinIn (AF F) σ J) K) := by
    refine Function.Injective.countable
      (f := fun x => (⟨((x : K) : HA (AF F) σ J), Subgroup.mem_subgroupOf.1 x.2⟩ :
        HFinIn (AF F) σ J)) ?_
    intro x y hxy
    have h2 := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext h2)

  have : SecondCountableTopology (AF F) := AdelicUnitaryTop.secondCountable_adele F
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isModTop
  obtain ⟨m, φ, hφ⟩ := Module.Finite.exists_fin' (AF F) (AF F ⊗[F] E)
  have hq := IsModuleTopology.isOpenQuotientMap_of_surjective hφ
  have : SecondCountableTopology (AF F ⊗[F] E) :=
    Topology.IsOpenQuotientMap.secondCountableTopology hq
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → AF F ⊗[F] E))
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) (AF F ⊗[F] E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
  have : SecondCountableTopology (GL (Fin n) (AF F ⊗[F] E)) :=
    Units.isInducing_embedProduct.secondCountableTopology
  have : SecondCountableTopology (HA (AF F) σ J) :=
    (Topology.IsInducing.subtypeVal :
      Topology.IsInducing (Subtype.val : HR (AF F) σ J → GL (Fin n) (AF F ⊗[F] E))).secondCountableTopology
  have : IsTopologicalGroup (HA (AF F) σ J) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA σ J
  have : BorelSpace (HA (AF F) σ J) := ⟨rfl⟩
  refine ⟨inferInstance, inferInstance, hcnt, fun μ => ?_⟩
  have hK1 : IsTopologicalGroup K := inferInstance
  have hK2 : SecondCountableTopology K := Topology.IsInducing.subtypeVal.secondCountableTopology
  have hK3 : OpensMeasurableSpace K := inferInstance
  obtain ⟨s, hs, hex⟩ := @exists_measurableSet_unique_smul_mem_of_discrete K _ _ hK1 hK2 _ hK3
    (Subgroup.subgroupOf (G := HA (AF F) σ J) (HFinIn (AF F) σ J) K)
    ((Subtype.val : K → HA (AF F) σ J) ⁻¹' t) (ht.preimage continuous_subtype_val) ht1
    (fun γ hγ hγV => Subtype.ext (htone _ (Subgroup.mem_subgroupOf.1 hγ) hγV))
  exact ⟨s, IsFundamentalDomain.mk' hs.nullMeasurableSet hex⟩

theorem domains_and_covolume (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E)
    (K : Subgroup (HA (AF F) σ J)) (Γ : Subgroup K)
    (hΓ : Γ = Subgroup.subgroupOf (G := HA (AF F) σ J) (HFinIn (AF F) σ J) K)
    (cov : Measure K → ℝ)
    (hcov : ∀ ν : Measure K, (∃ 𝓕 : Set K, IsFundamentalDomain Γ 𝓕 ν) →
      ∃ 𝓕 : Set K, IsFundamentalDomain Γ 𝓕 ν ∧ cov ν = (ν 𝓕).toReal)
    (μ : Measure K) (hμ : μ.IsHaarMeasure) :
    (∃ 𝓕 : Set K, IsFundamentalDomain Γ 𝓕 μ) ∧
    (∀ 𝓕 : Set K, IsFundamentalDomain Γ 𝓕 μ → cov μ = (μ 𝓕).toReal ∧ μ 𝓕 ≠ 0 ∧
      ∀ C : Set K, MeasurableSet C → (∀ m : K, ∃ γ ∈ Γ, ∃ k ∈ C, m = γ * k) → μ 𝓕 ≤ μ C) ∧
    ∀ c : NNReal, c ≠ 0 → cov (c • μ) = (c : ℝ) * cov μ := by
  obtain ⟨hTG, hB, hcnt, hex⟩ := countable_and_exists_domain F E σ n J K
  rw [← hΓ] at hcnt hex
  have := hμ
  refine ⟨hex μ, fun 𝓕 h𝓕 => ?_, fun c hc => ?_⟩
  · obtain ⟨𝓕', h𝓕', hcv⟩ := hcov μ ⟨𝓕, h𝓕⟩
    refine ⟨?_, @GlobalTheory.ClosedSubgroupCovol.measure_ne_zero _ _ _ hTG _ hB Γ μ hcnt _ _ h𝓕,
      fun C _ hC => @GlobalTheory.ClosedSubgroupCovol.measure_le_of_cover _ _ _ hTG _ hB Γ μ hcnt _ _ h𝓕 _ hC⟩
    rw [hcv, @GlobalTheory.ClosedSubgroupCovol.measure_eq _ _ _ hTG _ hB Γ μ hcnt _ _ _ h𝓕' h𝓕]
  · obtain ⟨𝓕, h𝓕⟩ := hex μ
    obtain ⟨𝓕', h𝓕', hcv⟩ := hcov μ ⟨𝓕, h𝓕⟩
    obtain ⟨𝓖, h𝓖, hcv'⟩ := hcov (c • μ) ⟨𝓕, (isFundamentalDomain_smul_iff Γ μ hc 𝓕).2 h𝓕⟩
    have h𝓖μ := (isFundamentalDomain_smul_iff Γ μ hc 𝓖).1 h𝓖
    rw [hcv', hcv, smul_apply,
      @GlobalTheory.ClosedSubgroupCovol.measure_eq _ _ _ hTG _ hB Γ μ hcnt _ _ _ h𝓖μ h𝓕', ENNReal.smul_def,
      smul_eq_mul, ENNReal.toReal_mul, ENNReal.coe_toReal]

end GlobalTheory.ClosedSubgroupCovol
end

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.ClosedSubgroupCovol

theorem fundamentalDomain_covol : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ K : Subgroup (HA (AF F) σ J), IsClosed (K : Set (HA (AF F) σ J)) → ∀ μ : Measure K, μ.IsHaarMeasure → (∃ 𝓕 : Set K, IsFundamentalDomain (ratOf (K := K)) 𝓕 μ) ∧ (∀ 𝓕 : Set K, IsFundamentalDomain (ratOf (K := K)) 𝓕 μ → covol μ = (μ 𝓕).toReal ∧ μ 𝓕 ≠ 0 ∧ ∀ C : Set K, MeasurableSet C → (∀ m : K, ∃ γ ∈ ratOf (K := K), ∃ k ∈ C, m = γ * k) → μ 𝓕 ≤ μ C) ∧ ∀ c : NNReal, c ≠ 0 → covol (c • μ) = (c : ℝ) * covol μ := by
  intro F E _ _ _ _ _ σ _ n J _ K _ μ hμ

  refine domains_and_covolume F E σ n J K (ratOf (K := K)) rfl covol ?_ μ hμ
  intro ν hν
  refine ⟨hν.choose, hν.choose_spec, ?_⟩
  rw [covol, dite_eq_left hν]

end GlobalTheory.ClosedSubgroupCovol
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NsubCocompact
noncomputable section

namespace GlobalTheory.UnipFlagCore

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Matrix
open scoped TensorProduct ENNReal

theorem mem_spanR_iff {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] {n r : ℕ}
    (e : Fin r → Fin n → E) (s : Set (Fin r)) (w : Fin n → R ⊗[F] E) :
    w ∈ spanR (F := F) R e s ↔
      ∃ c : Fin r → R ⊗[F] E, (∀ b, b ∉ s → c b = 0) ∧ w = ∑ b, c b • ratTup (F := F) R e b := by
  classical
  constructor
  · intro hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      refine ⟨Pi.single a 1, fun b hb => ?_, ?_⟩
      · exact Pi.single_eq_of_ne (by rintro rfl; exact hb ha) _
      · rw [Finset.sum_eq_single a]
        · simp only [Pi.single_eq_same, one_smul]; rfl
        · intro b _ hb; rw [Pi.single_eq_of_ne hb, zero_smul]
        · simp
    | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, rfl⟩ := hx
      obtain ⟨d, hd, rfl⟩ := hy
      refine ⟨c + d, fun b hb => by simp [hc b hb, hd b hb], ?_⟩
      simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
    | smul t x _ hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      refine ⟨t • c, fun b hb => by simp [hc b hb], ?_⟩
      simp only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, mul_smul]
  · rintro ⟨c, hc, rfl⟩
    refine Submodule.sum_mem _ fun b _ => ?_
    by_cases hb : b ∈ s
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, hb, rfl⟩)
    · rw [hc b hb, zero_smul]; exact Submodule.zero_mem _

theorem hE_swap {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (x y : Fin n → E) : hE σ J y x = σ (hE σ J x y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hE, Formalism.UG.hform, map_sum, map_mul, RingHom.coe_coe, hσ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ.1 j i]; ring

theorem nsub_cocompact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (P : Frame E n r) (T : F),
    P.IsStd σ J T → ∃ K : Set (Nsub (AF F) σ J P), IsCompact K ∧
      ∀ m : Nsub (AF F) σ J P, ∃ γ ∈ ratOf (K := Nsub (AF F) σ J P), ∃ k ∈ K, m = γ * k := by
  intro F E _ _ _ _ _ σ hCM n J hJ r P T hP
  have hσ := conj_invol hCM
  obtain ⟨h0, -, hef, -, -, -, -⟩ := hP
  have he : LinearIndependent E P.e := linearIndependent_of_dual P.e P.f fun a b => by
    rw [hE_swap hσ hJ (P.e b) (P.f a), hef]
    split_ifs with h1 h2 h2
    · simp
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · simp
  have hlin : ∀ (g : HA (AF F) σ J) (x : Fin n → AF F ⊗[F] E),
      lin (AF F) σ J g x - x = ((HA.mat _ σ J g).1 - 1) *ᵥ x := fun g x => by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]; rfl
  obtain ⟨K, hK, hm⟩ := cocompact_of_mem_iff_adelic hσ hJ P.e he h0 (Nsub (AF F) σ J P) fun g => by
    refine and_congr (forall_congr' fun a => ?_) (forall_congr' fun x => imp_congr Iff.rfl ?_)
    · have := mem_spanR_iff (F := F) (AF F) P.e {b | b < a} (lin (AF F) σ J g (ratV (F := F) (AF F) (P.e a)) - ratV (F := F) (AF F) (P.e a))
      rw [this, hlin]
      simp only [Set.mem_setOf_eq, not_lt]
      rfl
    · have := mem_spanR_iff (F := F) (AF F) P.e Set.univ (lin (AF F) σ J g x - x)
      rw [this, hlin]
      simp only [Set.mem_univ, not_true_eq_false, false_imp_iff, implies_true, true_and]
  refine ⟨K, hK, fun m => ?_⟩
  obtain ⟨γ, hγ, k, hk, rfl⟩ := hm m
  exact ⟨γ, hγ, k, hk, rfl⟩

end GlobalTheory.UnipFlagCore
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsHaarMeasureUnipotentRadicalCovolumeOne
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.NsubHaarCovol

theorem exists_haar_covol_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → ∃ μ : Measure (Nsub (AF F) σ J P), μ.IsHaarMeasure ∧ covol μ = 1 := by
  intro F E _ _ _ _ _ σ hCM n J hJ r P T hP
  have hcl : IsClosed (Nsub (AF F) σ J P : Set (HA (AF F) σ J)) :=
    PI.UnitaryGroupMassFormula.MeasWCore.isClosed_Nsub (AF F) σ J P
  let μ0 : Measure (Nsub (AF F) σ J P) := Measure.haar
  have hμ0 : μ0.IsHaarMeasure := inferInstance
  obtain ⟨⟨𝓕, h𝓕⟩, hall, hscale⟩ :=
    GlobalTheory.ClosedSubgroupCovol.fundamentalDomain_covol F E σ hCM n J hJ _ hcl μ0 hμ0
  obtain ⟨Kc, hKc, hcov⟩ := GlobalTheory.UnipFlagCore.nsub_cocompact F E σ hCM n J hJ r P T hP
  obtain ⟨hcv, hne, hle⟩ := hall 𝓕 h𝓕
  have hfin : μ0 𝓕 ≠ ∞ :=
    ((hle Kc hKc.isClosed.measurableSet hcov).trans_lt hKc.measure_lt_top).ne
  have hpos : 0 < (μ0 𝓕).toReal := ENNReal.toReal_pos hne hfin
  have hc0 : ((μ0 𝓕).toNNReal)⁻¹ ≠ 0 := inv_ne_zero (by
    intro h; rw [ENNReal.toNNReal_eq_zero_iff] at h; exact h.elim hne hfin)
  refine ⟨((μ0 𝓕).toNNReal)⁻¹ • μ0, Measure.IsHaarMeasure.nnreal_smul _ hc0, ?_⟩
  rw [hscale _ hc0, hcv, NNReal.coe_inv, ENNReal.coe_toNNReal_eq_toReal]
  exact inv_mul_cancel₀ hpos.ne'

end GlobalTheory.NsubHaarCovol
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsHaarMeasureUnipotentRadicalCovolumeOneStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_haarMeasure_unipotentRadical_covolume_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → ∃ μ : Measure (Nsub (AF F) σ J P), μ.IsHaarMeasure ∧ covol μ = 1 := by
  first | exact @GlobalTheory.NsubHaarCovol.exists_haar_covol_one | exact GlobalTheory.NsubHaarCovol.exists_haar_covol_one | (intros; apply GlobalTheory.NsubHaarCovol.exists_haar_covol_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FourMulAddFiveLeRank
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.CmHermitianRankFrames

theorem four_mul_add_five_le_rank (D : Formalism.BasicNotions.D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) :
    4 * D.R.rS + 5 ≤ X.B.I.n := by

  rw [X.n_eq]
  have hk := D.R.m_add_three_le_k
  have h2 := D.R.two_le_m
  obtain ⟨j, hj⟩ := D.R.m_even
  simp only [Formalism.BasicNotions.Ranks.r, Formalism.BasicNotions.Ranks.rS]
  omega

theorem cm_herm_rank_frames : ∀ (D : Formalism.BasicNotions.D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D), IsCMExt X.B.I.F X.B.I.E X.B.I.cm.sig ∧ IsHermND X.B.I.cm.sig X.B.I.J ∧ 4 * D.R.rS + 5 ≤ X.B.I.n ∧ ∀ u, ∃ T : X.B.I.F, (Formalism.L2.SG.TypedSets.frameOf X u).IsStd X.B.I.cm.sig X.B.I.J T :=
  fun D X => ⟨MassDataVolumesW.stepCM X, MassDataVolumesW.stepHerm X, four_mul_add_five_le_rank D X,
    fun u => MassDataLevelSSteps.frameStd_holds X u⟩

end GlobalTheory.CmHermitianRankFrames
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMeasWPrescribed
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.St.MeasWord

theorem exists_measW_prescribed :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
      IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (P : Frame E n r)
      (T : F), P.IsStd σ J T → ∀ (μNinf : Measure (Nsub (Ainf F) σ J P))
      (μHinf : Measure (Hsub (Ainf F) σ J P)) (μN : Measure (Nsub (AF F) σ J P))
      (μH : Measure (Hsub (AF F) σ J P))
      (μSv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Ssub (Fv F v) σ J P)),
      μNinf.IsHaarMeasure → μHinf.IsHaarMeasure → μN.IsHaarMeasure → μH.IsHaarMeasure →
      (∀ v, (μSv v).IsHaarMeasure) →
      ∃ W : MeasW σ J P, W.IsTextNorm ∧ W.μNinf = μNinf ∧ W.μHinf = μHinf ∧ W.μN = μN ∧ W.μH = μH ∧
        W.μSv = μSv := by
  intro F E _ _ _ _ _ σ hCM n J hJ r P T hP μNinf μHinf μN μH μSv hNinf hHinf hN hH hSv
  have : Module.Finite F E := PI.VolSemiDirect.W.Lc.finite_nf F E
  obtain ⟨eH, heH⟩ := PI.UnitaryGroupMassFormula.MeasWCore.hermitian_measure_splitting F E σ n J r P T hCM hJ hP
  obtain ⟨eN, heN⟩ := PI.UnitaryGroupMassFormula.MeasWCore.nilpotent_measure_splitting F E σ n J r P T hCM hJ hP
  have hsm : Measurable (splitA σ J) := (PI.UnitaryGroupMassFormula.MeasWCore.continuous_measure_splitting F E σ n J hCM).measurable
  have : SecondCountableTopology (Hsub (AF F) σ J P) :=
    eH.toHomeomorph.symm.isEmbedding.secondCountableTopology
  have : SecondCountableTopology (Nsub (AF F) σ J P) :=
    eN.toHomeomorph.symm.isEmbedding.secondCountableTopology
  obtain ⟨μHf, hHf, hHeq⟩ := GlobalTheory.St.HaarSplit.exists_haar_map_prod_eq eH μHinf μH
  obtain ⟨μNf, hNf, hNeq⟩ := GlobalTheory.St.HaarSplit.exists_haar_map_prod_eq eN μNinf μN
  obtain ⟨μSf, hSH, hSeq⟩ := PI.UnitaryGroupMassFormula.MeasWCore.product_decomposition_holds F E σ n J r P T hCM hJ hP μNf μHf hNf hHf
  have : SigmaCompactSpace (Hsub (Ainf F) σ J P) := inferInstance
  have : SigmaCompactSpace (Nsub (Ainf F) σ J P) := inferInstance
  have : SigmaCompactSpace (Hsub (Af F) σ J P) := inferInstance
  have : SigmaCompactSpace (Nsub (Af F) σ J P) := inferInstance
  have : SigmaFinite μHinf := inferInstance
  have : SigmaFinite μNinf := inferInstance
  have : SigmaFinite μHf := inferInstance
  have : SigmaFinite μNf := inferInstance
  refine ⟨{ μH := μH, μHinf := μHinf, μHf := μHf, μN := μN, μNinf := μNinf, μNf := μNf, μSf := μSf,
            μSv := μSv }, ?_, rfl, rfl, rfl, rfl, rfl⟩
  refine ⟨hH, hHinf, hHf, hN, hNinf, hNf, hSH, hSv, ?_, ?_, hSeq⟩
  · show (μH.map Subtype.val).map (splitA σ J) = _
    rw [← hHeq]
    exact PI.UnitaryGroupMassFormula.MeasWCore.map_split_eq (splitA σ J) hsm eH eH.continuous.measurable heH μHinf μHf
  · show (μN.map Subtype.val).map (splitA σ J) = _
    rw [← hNeq]
    exact PI.UnitaryGroupMassFormula.MeasWCore.map_split_eq (splitA σ J) hsm eN eN.continuous.measurable heN μNinf μNf

end GlobalTheory.St.MeasWord
end

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.St.Rescale

theorem rescaleStep3 :
    HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → ∀ D : Formalism.BasicNotions.D7, GlobalTheory.St.RescaleStep3 D := by
  intro hSW D X hb hM
  obtain ⟨hCM, hH, hsize, hfr⟩ := GlobalTheory.CmHermitianRankFrames.cm_herm_rank_frames D X
  obtain ⟨hA, hC⟩ := GlobalTheory.St.siegelWeil_volumes hSW X.B.I.F X.B.I.E X.B.I.cm.sig hCM X.B.I.n X.B.I.J hH
  obtain ⟨ψ, hψ, hstd⟩ := Formalism.L2.SG.Pf.standard_character_exists X.B.I.F hCM.1
  have hstd' : Formalism.L2.SG.LocVol.IsStdChar ψ := hstd
  have hG := X.measG_norm
  have hμG : X.measG.μG.IsHaarMeasure := hG.1
  have hherm : ∀ {a : ℕ} (X0 : Fin a → Fin X.B.I.n → X.B.I.E) (i j : Fin a),
      X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J X0 j i) = gramE X.B.I.cm.sig X.B.I.J X0 i j :=
    fun X0 i j => GlobalTheory.FrameGram.hE_swap (GlobalTheory.FrameGram.conj_invol hCM) hH.1 _ _

  have hB : ∀ X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E,
      ∃ μ' : Measure (stabT (AF X.B.I.F) X.B.I.cm.sig X.B.I.J X0), μ'.IsHaarMeasure ∧
        ((gramE X.B.I.cm.sig X.B.I.J X0).det ≠ 0 →
          ∃ (hTB : ∀ i j, X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J X0 j i) =
              gramE X.B.I.cm.sig X.B.I.J X0 i j) (νB : Measure _),
            Formalism.L2.SG.Volumes.IsOmT X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J ψ _ hTB νB ∧
            Formalism.L2.SG.Volumes.IsCompatT X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J X0 X.measG.μG μ' νB) := by
    intro X0
    by_cases hdet : (gramE X.B.I.cm.sig X.B.I.J X0).det ≠ 0
    · obtain ⟨νX, μ', h1, h2, h3⟩ := GlobalTheory.T.exists_adelicTorusMeasure_stabiliserHaar X.B.I.F X.B.I.E X.B.I.cm.sig hCM X.B.I.n X.B.I.J hH hA hC ψ hψ
        (2 * D.R.rS + 2) (by omega) (by omega) X0 (hherm X0) hdet X.measG.μG hμG
      exact ⟨μ', h2, fun _ => ⟨hherm X0, νX, h1, h3⟩⟩
    · exact ⟨X.measG.μB X0, hG.2.2.2.2.1 X0, fun h => absurd h hdet⟩
  choose μB' hμB' hBc using hB

  have hW : ∀ u, ∃ W : MeasW X.B.I.cm.sig X.B.I.J (Formalism.L2.SG.TypedSets.frameOf X u), W.IsTextNorm ∧
      W.μNinf = (X.measW u).μNinf ∧ W.μHinf = (X.measW u).μHinf ∧
      (∃ (hT1 : ∀ i j, X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J (tupH (Formalism.L2.SG.TypedSets.frameOf X u)) j i) =
            gramE X.B.I.cm.sig X.B.I.J (tupH (Formalism.L2.SG.TypedSets.frameOf X u)) i j) (νH : Measure _),
        Formalism.L2.SG.Volumes.IsOmT X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J ψ _ hT1 νH ∧
        Formalism.L2.SG.Volumes.IsCompatT X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J
          (tupH (Formalism.L2.SG.TypedSets.frameOf X u)) X.measG.μG W.μH νH) ∧
      covol W.μN = 1 ∧
      ∀ v, Formalism.L2.SG.LocVol.LocTieW X.B.I.cm.sig X.B.I.J ψ v (Formalism.L2.SG.TypedSets.frameOf X u)
        (X.measG.μGv v) (W.μSv v) := by
    intro u
    obtain ⟨T, hP⟩ := hfr u
    obtain ⟨hdet, hT1, -⟩ := GlobalTheory.FrameGram.std_frame_gram X.B.I.F X.B.I.E X.B.I.cm.sig hCM X.B.I.n X.B.I.J hH
      D.R.rS (Formalism.L2.SG.TypedSets.frameOf X u) T hP
    obtain ⟨νH, μH, h1, h2, h3⟩ := GlobalTheory.T.exists_adelicTorusMeasure_stabiliserHaar X.B.I.F X.B.I.E X.B.I.cm.sig hCM X.B.I.n X.B.I.J hH hA hC ψ hψ
      (D.R.rS + 1 + D.R.rS) (by omega) (by omega) (tupH (Formalism.L2.SG.TypedSets.frameOf X u)) hT1 hdet
      X.measG.μG hμG
    obtain ⟨μN, hN, hN1⟩ := GlobalTheory.T.exists_haarMeasure_unipotentRadical_covolume_one X.B.I.F X.B.I.E X.B.I.cm.sig hCM X.B.I.n X.B.I.J hH D.R.rS
      (Formalism.L2.SG.TypedSets.frameOf X u) T hP
    have hS : ∀ v : HeightOneSpectrum (𝓞 X.B.I.F),
        ∃ μS : Measure (Ssub (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (Formalism.L2.SG.TypedSets.frameOf X u)),
          μS.IsHaarMeasure ∧ Formalism.L2.SG.LocVol.LocTieW X.B.I.cm.sig X.B.I.J ψ v
            (Formalism.L2.SG.TypedSets.frameOf X u) (X.measG.μGv v) μS := fun v =>
      GlobalTheory.T.exists_frameStabilizerHaar_normalised_fibreMeasure X.B.I.F X.B.I.E X.B.I.cm.sig hCM X.B.I.n X.B.I.J hH hA hC ψ hψ hstd' v D.R.rS
        (Formalism.L2.SG.TypedSets.frameOf X u) T hP (by omega) (X.measG.μGv v) (hG.2.2.2.1 v)
    choose μSv hSv hSt using hS
    have hWn := X.measW_norm u
    obtain ⟨W, hWt, e1, e2, e3, e4, e5⟩ := GlobalTheory.St.MeasWord.exists_measW_prescribed X.B.I.F X.B.I.E X.B.I.cm.sig hCM
      X.B.I.n X.B.I.J hH D.R.rS (Formalism.L2.SG.TypedSets.frameOf X u) T hP
      (X.measW u).μNinf (X.measW u).μHinf μN μH μSv hWn.2.2.2.2.1 hWn.2.1 hN h2 hSv
    refine ⟨W, hWt, e1, e2, ⟨hT1, νH, h1, ?_⟩, ?_, ?_⟩
    · rw [e4]; exact h3
    · rw [e3]; exact hN1
    · intro v; rw [e5]; exact hSt v
  choose mw hw hNinf hHinf hOm hCov hLoc using hW
  let mg : MeasG X.B.I.cm.sig X.B.I.J D.R.rS := { X.measG with μB := μB' }
  have hg : mg.IsTextNorm := ⟨hG.1, hG.2.1, hG.2.2.1, hG.2.2.2.1, hμB', hG.2.2.2.2.2⟩
  refine ⟨mg, hg, mw, hw, ?_, ψ, hψ, hstd', ?_, ?_⟩
  · refine ⟨hM.1, hM.2.1, hM.2.2.1, fun u => ?_⟩
    have h := hM.2.2.2 u
    constructor
    · show amb (mw u).μNinf = _
      rw [hNinf u]; exact h.1
    · show amb (mw u).μHinf = _
      rw [hHinf u]; exact h.2
  · exact ⟨fun u => ⟨hOm u, hCov u⟩, hBc⟩
  · intro w v
    exact hLoc w v

end GlobalTheory.St.Rescale
