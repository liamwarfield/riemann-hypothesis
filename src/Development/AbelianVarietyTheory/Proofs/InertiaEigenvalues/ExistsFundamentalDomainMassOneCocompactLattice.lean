module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoAnnihilatorOfIntegralLocalDuality
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPartCOfPartAPartBFiniteLevelStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankH1fDeRham

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFundamentalDomainMassOneCocompactLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFundamentalDomainMassOneCocompactLattice
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

theorem exists_fundamentalDomain_mass_one : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] (Γ : AddSubgroup G), IsCoLat Γ → ∀ [MeasurableSpace G] [BorelSpace G], ∃ (μ : Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure ∧ IsAddFundamentalDomain Γ 𝓕 μ ∧ μ 𝓕 = 1 := by
  intro G _ _ _ _ _ _ Γ hΓ _ _
  obtain ⟨hdisc, K, hK, hKc⟩ := hΓ
  have : DiscreteTopology Γ := hdisc
  have : Countable Γ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance

  obtain ⟨U, hUo, hU⟩ := isOpen_induced_iff.1 (isOpen_discrete ({0} : Set Γ))
  have hU0 : ∀ γ ∈ Γ, γ ∈ U → γ = 0 := by
    intro γ hγ hγU
    have h : (⟨γ, hγ⟩ : Γ) ∈ (Subtype.val ⁻¹' U : Set Γ) := hγU
    rw [hU] at h
    exact congrArg Subtype.val (Set.mem_singleton_iff.1 h)
  have hUn : U ∈ nhds (0 : G) := by
    have h : (0 : Γ) ∈ (Subtype.val ⁻¹' U : Set Γ) := by rw [hU]; rfl
    exact hUo.mem_nhds h

  obtain ⟨V, hV, hVU⟩ := exists_nhds_zero_half hUn
  set V₀ := interior (V ∩ (fun x => -x) ⁻¹' V) with hV₀
  have hV₀o : IsOpen V₀ := isOpen_interior
  have hV₀0 : (0 : G) ∈ V₀ := by
    rw [hV₀, mem_interior_iff_mem_nhds]
    refine Filter.inter_mem hV ?_
    exact continuous_neg.continuousAt.preimage_mem_nhds (by simpa using hV)
  have hsub : ∀ a ∈ V₀, ∀ b ∈ V₀, a - b ∈ U := by
    intro a ha b hb
    have ha' := (interior_subset ha).1
    have hb' : -b ∈ V := (interior_subset hb).2
    rw [sub_eq_add_neg]
    exact hVU a ha' (-b) hb'

  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun k : G => (fun x => x - k) ⁻¹' V₀)
    (fun k => hV₀o.preimage (continuous_id.sub continuous_const))
    (fun x _ => Set.mem_iUnion.2 ⟨x, by simpa using hV₀0⟩)
  set l := t.toList with hl
  let c : ℕ → G := fun n => l.getD n 0
  let W : ℕ → Set G := fun n => (fun x => x - c n) ⁻¹' V₀ ∩ K ∩ {_x | n < l.length}
  let S : ℕ → Set G := fun n => ⋃ γ : Γ, (fun x => (γ : G) + x) ⁻¹' W n
  let F : Set G := ⋃ n, (W n ∩ ⋂ m, ⋂ (_ : m < n), (S m)ᶜ)
  have hWm : ∀ n, MeasurableSet (W n) := fun n =>
    ((hV₀o.preimage (continuous_id.sub continuous_const)).measurableSet.inter
      hK.isClosed.measurableSet).inter (MeasurableSet.const _)
  have hSm : ∀ n, MeasurableSet (S n) := fun n =>
    MeasurableSet.iUnion fun γ => (hWm n).preimage (measurable_const_add _)
  have hFm : MeasurableSet F :=
    MeasurableSet.iUnion fun n => (hWm n).inter
      (MeasurableSet.iInter fun m => MeasurableSet.iInter fun _ => (hSm m).compl)
  have hFK : F ⊆ K := by
    intro x hx
    obtain ⟨n, hn, -⟩ := Set.mem_iUnion.1 hx
    exact hn.1.2

  have hSinv : ∀ n, ∀ γ ∈ Γ, ∀ x, γ + x ∈ S n ↔ x ∈ S n := by
    intro n γ hγ x
    simp only [S, Set.mem_iUnion, Set.mem_preimage]
    constructor
    · rintro ⟨δ, hδ⟩
      exact ⟨⟨(δ : G) + γ, Γ.add_mem δ.2 hγ⟩, by simpa [add_assoc] using hδ⟩
    · rintro ⟨δ, hδ⟩
      refine ⟨⟨(δ : G) - γ, Γ.sub_mem δ.2 hγ⟩, ?_⟩
      rw [show (δ : G) - γ + (γ + x) = δ + x by abel]
      exact hδ

  have hcov : ∀ y ∈ K, ∃ n, y ∈ W n := by
    intro y hy
    obtain ⟨k, hk, hyk⟩ := Set.mem_iUnion₂.1 (ht hy)
    have hkl : k ∈ l := by rw [hl]; exact Finset.mem_toList.2 hk
    obtain ⟨n, hn, rfl⟩ := List.mem_iff_getElem.1 hkl
    refine ⟨n, ⟨?_, hy⟩, hn⟩
    have hc : c n = l[n] := List.getD_eq_getElem _ _ hn
    simpa [hc] using hyk
  have hex : ∀ x : G, ∃! γ : Γ, γ +ᵥ x ∈ F := by
    intro x
    have hne : ∃ n, x ∈ S n := by
      obtain ⟨γ, hγ, hγK⟩ := hKc x
      obtain ⟨n, hn⟩ := hcov _ hγK
      exact ⟨n, Set.mem_iUnion.2 ⟨⟨γ, hγ⟩, hn⟩⟩
    classical
    obtain ⟨δ, hδ⟩ := Set.mem_iUnion.1 (Nat.find_spec hne)
    have hδF : δ +ᵥ x ∈ F := by
      refine Set.mem_iUnion.2 ⟨Nat.find hne, hδ, ?_⟩
      simp only [Set.mem_iInter, Set.mem_compl_iff]
      intro m hm
      change ¬ ((δ : G) + x ∈ S m)
      rw [hSinv m δ δ.2 x]
      exact Nat.find_min hne hm
    refine ⟨δ, hδF, ?_⟩
    intro γ hγ
    change (γ : G) + x ∈ F at hγ
    have hγ' : (δ : G) + x ∈ F := hδF
    obtain ⟨n, hn, hnS⟩ := Set.mem_iUnion.1 hγ
    obtain ⟨n', hn', hnS'⟩ := Set.mem_iUnion.1 hγ'
    simp only [Set.mem_iInter, Set.mem_compl_iff] at hnS hnS'
    have hxn : x ∈ S n := Set.mem_iUnion.2 ⟨γ, hn⟩
    have hxn' : x ∈ S n' := Set.mem_iUnion.2 ⟨δ, hn'⟩
    rcases lt_trichotomy n n' with h | rfl | h
    · exact absurd ((hSinv n δ δ.2 x).2 hxn) (hnS' n h)
    · have hd := hsub _ hn.1.1 _ hn'.1.1
      have hmem : (γ : G) - δ ∈ Γ := Γ.sub_mem γ.2 δ.2
      have h0 := hU0 _ hmem (by simpa [sub_sub_sub_cancel_right, add_sub_add_right_eq_sub] using hd)
      exact Subtype.ext (sub_eq_zero.1 h0)
    · exact absurd ((hSinv n' γ γ.2 x).2 hxn') (hnS n' h)

  let μ₀ : Measure G := Measure.addHaar
  have hF₀ : IsAddFundamentalDomain Γ F μ₀ := IsAddFundamentalDomain.mk' hFm.nullMeasurableSet hex
  have h0 : μ₀ F ≠ 0 := hF₀.measure_ne_zero (NeZero.ne μ₀)
  have htop : μ₀ F ≠ ⊤ := ((measure_mono hFK).trans_lt hK.measure_lt_top).ne
  refine ⟨(μ₀ F)⁻¹ • μ₀, F, Measure.IsAddHaarMeasure.smul μ₀ (ENNReal.inv_ne_zero.2 htop) (ENNReal.inv_ne_top.2 h0),
    IsAddFundamentalDomain.mk' hFm.nullMeasurableSet hex, ?_⟩
  rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel h0 htop]

end GlobalTheory.CuspGeneric
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFundamentalDomainMassOneCocompactLatticeStatement
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fundamentalDomain_mass_one_cocompactLattice : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] (Γ : AddSubgroup G), IsCoLat Γ → ∀ [MeasurableSpace G] [BorelSpace G], ∃ (μ : Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure ∧ IsAddFundamentalDomain Γ 𝓕 μ ∧ μ 𝓕 = 1 := by
  first | exact @GlobalTheory.CuspGeneric.exists_fundamentalDomain_mass_one | exact GlobalTheory.CuspGeneric.exists_fundamentalDomain_mass_one | (intros; apply GlobalTheory.CuspGeneric.exists_fundamentalDomain_mass_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetIntegralFundamentalDomainEqMassMulAverage
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetIntegralFundamentalDomainEqMassMulAverage
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

theorem setIntegral_eq_mass_mul_avg : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] (Γ : AddSubgroup G), IsCoLat Γ → ∀ [MeasurableSpace G] [BorelSpace G] (μ : Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure → IsAddFundamentalDomain Γ 𝓕 μ → ∀ Φ : G → ℂ, Per Γ Φ → μ 𝓕 ≠ 0 ∧ μ 𝓕 ≠ ⊤ ∧ IntegrableOn Φ 𝓕 μ ∧ ∫ x in 𝓕, Φ x ∂μ = ((μ 𝓕).toReal : ℂ) * avg Γ Φ := by
  intro G _ _ _ _ _ _ Γ hΓ mG hB μ 𝓕 hμ h𝓕 Φ hΦ
  obtain ⟨hd, K, hK, hcov⟩ := hΓ
  have e := hB.measurable_eq
  subst e
  letI : MeasurableSpace G := borel G
  haveI : Countable Γ := countable_of_discrete_addSubgroup Γ
  have hne : μ 𝓕 ≠ 0 := h𝓕.measure_ne_zero (NeZero.ne μ)
  have hfin : μ 𝓕 ≠ ⊤ := (GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact Γ hK hcov μ h𝓕).ne
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hΦ.1.continuousOn
  have hb : ∀ x, ‖Φ x‖ ≤ C := fun x => by
    obtain ⟨γ, hγ, hk⟩ := hcov x
    have := hC _ hk
    rwa [hΦ.2 γ hγ] at this
  have hint : IntegrableOn Φ 𝓕 μ :=
    Measure.integrableOn_of_bounded hfin hΦ.1.aestronglyMeasurable (M := C) (Filter.Eventually.of_forall hb)
  refine ⟨hne, hfin, hint, ?_⟩
  have hex := (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact G Γ K hK hcov).1
  have hex' : ∃ p : Measure G × Set G, p.1.IsAddHaarMeasure ∧ IsAddFundamentalDomain Γ p.2 p.1 ∧ p.1 p.2 = 1 := by
    obtain ⟨μ₀, F₀, h⟩ := hex
    exact ⟨(μ₀, F₀), h⟩
  have hav : avg Γ Φ = ∫ x in hex'.choose.2, Φ x ∂hex'.choose.1 := by
    simp only [avg]
    rw [dite_eq_left hex']
  rw [hav]
  obtain ⟨hμ₀, hF₀, h1⟩ := hex'.choose_spec
  generalize hex'.choose = p at hμ₀ hF₀ h1 ⊢
  obtain ⟨μ₀, F₀⟩ := p
  simp only at hμ₀ hF₀ h1 ⊢
  obtain ⟨c, hc⟩ : ∃ c : NNReal, μ = c • μ₀ := ⟨_, Measure.isAddLeftInvariant_eq_smul μ μ₀⟩
  have hac : μ ≪ μ₀ := hc ▸ Measure.smul_absolutelyContinuous
  have hF₀' : IsAddFundamentalDomain Γ F₀ μ := hF₀.mono hac
  have e1 : μ 𝓕 = μ F₀ := h𝓕.measure_eq hF₀'
  have e2 : ∫ x in 𝓕, Φ x ∂μ = ∫ x in F₀, Φ x ∂μ :=
    h𝓕.setIntegral_eq hF₀' fun g x => hΦ.2 g g.2 x
  rw [e1, e2, hc, Measure.restrict_smul, integral_smul_nnreal_measure, Measure.smul_apply, h1]
  simp [ENNReal.smul_def, NNReal.smul_def]

end GlobalTheory.CuspGeneric
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetIntegralFundamentalDomainEqMassMulAverageStatement
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.setIntegral_fundamentalDomain_eq_mass_mul_average : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] (Γ : AddSubgroup G), IsCoLat Γ → ∀ [MeasurableSpace G] [BorelSpace G] (μ : Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure → IsAddFundamentalDomain Γ 𝓕 μ → ∀ Φ : G → ℂ, Per Γ Φ → μ 𝓕 ≠ 0 ∧ μ 𝓕 ≠ ⊤ ∧ IntegrableOn Φ 𝓕 μ ∧ ∫ x in 𝓕, Φ x ∂μ = ((μ 𝓕).toReal : ℂ) * avg Γ Φ := by
  first | exact @GlobalTheory.CuspGeneric.setIntegral_eq_mass_mul_avg | exact GlobalTheory.CuspGeneric.setIntegral_eq_mass_mul_avg | (intros; apply GlobalTheory.CuspGeneric.setIntegral_eq_mass_mul_avg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoLocalAllPrimesOfBlochKato
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoAnnihilatorOfRationalLocalDuality
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoAnnihilatorOfRationalLocalDuality
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.BkCoeff

open GlobalTheory.PstCoeff

variable {l : ℕ} [Fact l.Prime]

section Cob

variable {G : Type} [Group G] [TopologicalSpace G] {K₀ K : Type} [Field K₀] [Field K]
    [Algebra ℚ_[l] K₀] [Algebra ℚ_[l] K] [Algebra K₀ K] [IsScalarTower ℚ_[l] K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra ℚ_[l] B] [Algebra K₀ B] [IsScalarTower ℚ_[l] K₀ B]
    [Algebra ℚ_[l] BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower ℚ_[l] K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower ℚ_[l] K₀ BdR]
    (PD : PeriodData G ℚ_[l] K₀ K B BdR)

theorem cyclotomicTwist_differential_apply {LL : Type} [Field LL] [Algebra ℚ_[l] LL] (f : G → LL) (x : G × G) :
    ReciprocityTheory.Def.d1 (charRep (cycLL PD LL)) f x =
      algebraMap ℚ_[l] LL (PD.χ x.1 : ℚ_[l]) * f x.2 - f (x.1 * x.2) + f x.1 := by
  simp [ReciprocityTheory.Def.d1, charRep, cycLL, Algebra.smul_def]

theorem cobL_iff_trace {LL : Type} [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL]
    [FiniteDimensional ℚ_[l] LL] [IsModuleTopology ℚ_[l] LL] (z : G × G → LL) :
    CobL PD z ↔ ∀ c : LL, CobL PD (fun x => Algebra.trace ℚ_[l] LL (c * z x)) := by
  haveI : ContinuousAdd LL := IsModuleTopology.toContinuousAdd ℚ_[l] LL
  haveI : ContinuousSMul ℚ_[l] LL := IsModuleTopology.toContinuousSMul ℚ_[l] LL
  constructor
  · rintro ⟨f, hf, rfl⟩ c
    refine ⟨fun g => Algebra.trace ℚ_[l] LL (c * f g), ?_, ?_⟩
    · exact (IsModuleTopology.continuous_of_linearMap
        ((Algebra.trace ℚ_[l] LL).comp (LinearMap.mulLeft ℚ_[l] c))).comp hf
    · funext x
      rw [cyclotomicTwist_differential_apply, cyclotomicTwist_differential_apply]
      have e1 : c * (algebraMap ℚ_[l] LL (PD.χ x.1 : ℚ_[l]) * f x.2 - f (x.1 * x.2) + f x.1) =
          (PD.χ x.1 : ℚ_[l]) • (c * f x.2) - c * f (x.1 * x.2) + c * f x.1 := by
        rw [Algebra.smul_def]; ring
      rw [e1, map_add (f := _), map_sub, map_smul, smul_eq_mul]
      simp
  · intro h
    choose f hf using h
    have hB := traceForm_nondegenerate ℚ_[l] LL
    let b := Module.finBasis ℚ_[l] LL
    let d := (Algebra.traceForm ℚ_[l] LL).dualBasis hB b
    refine ⟨fun g => ∑ i, f (b i) g • d i, ?_, ?_⟩
    · exact continuous_finsetSum _ fun i _ => ((hf (b i)).1).smul continuous_const
    · funext x
      rw [cyclotomicTwist_differential_apply]
      have hz : z x = ∑ i, (d.repr (z x) i) • d i := (d.sum_repr (z x)).symm
      have hc : ∀ i, d.repr (z x) i = (PD.χ x.1 : ℚ_[l]) * f (b i) x.2 - f (b i) (x.1 * x.2) + f (b i) x.1 := by
        intro i
        rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply, mul_comm,
          ← congrFun (hf (b i)).2 x, cyclotomicTwist_differential_apply]
        simp
      rw [hz]
      simp_rw [hc, add_smul, sub_smul, mul_smul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.smul_sum, Algebra.smul_def]

end Cob

section Main

variable (P : LocPrime l) {K : FinExt l}

def trPair {LL V V' : Type} [Field LL] [Algebra ℚ_[l] LL]
    [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL V']
    (Pr : V →ₗ[LL] V' →ₗ[LL] LL) : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l] :=
  LinearMap.mk₂ ℚ_[l] (fun x y => Algebra.trace ℚ_[l] LL (Pr x y))
    (fun x x' y => by simp)
    (fun c x y => by simp [LinearMap.map_smul_of_tower])
    (fun x y y' => by simp)
    (fun c x y => by simp [LinearMap.map_smul_of_tower])

theorem trPair_apply {LL V V' : Type} [Field LL] [Algebra ℚ_[l] LL]
    [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL V']
    (Pr : V →ₗ[LL] V' →ₗ[LL] LL) (x : V) (y : V') :
    trPair Pr x y = Algebra.trace ℚ_[l] LL (Pr x y) := rfl

theorem isDual1_trPair {LL : Type} [Field LL] [Algebra ℚ_[l] LL] [FiniteDimensional ℚ_[l] LL]
    {V V' : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL V']
    {ρ : Representation LL ↥(GK K) V} {ρ' : Representation LL ↥(GK K) V'} {Pr : V →ₗ[LL] V' →ₗ[LL] LL}
    (hP : IsDual1 (P.PD K) ρ ρ' Pr) : IsDual1 (P.PD K) (resQ ρ) (resQ ρ') (trPair Pr) := by
  have hB := traceForm_nondegenerate ℚ_[l] LL
  obtain ⟨h1, h2, h3, h4⟩ := hP
  refine ⟨fun g x y => ?_, fun x hx => h2 x fun y => ?_, fun y hy => h3 y fun x => ?_, ?_⟩
  · rw [resQ_apply, resQ_apply, trPair_apply, trPair_apply, h1]
    have e : ((cycLL (P.PD K) LL g : LLˣ) : LL) * Pr x y = ((P.PD K).χ g : ℚ_[l]) • Pr x y := by
      simp [cycLL, Algebra.smul_def]
    rw [e, map_smul, smul_eq_mul]
    simp [cycLL]
  · refine hB.1 _ fun c => ?_
    rw [Algebra.traceForm_apply, mul_comm, ← smul_eq_mul, ← map_smul]
    exact hx (c • y)
  · refine hB.1 _ fun c => ?_
    rw [Algebra.traceForm_apply, mul_comm, ← smul_eq_mul, ← LinearMap.smul_apply, ← map_smul]
    exact hy (c • x)
  · rw [← Module.finrank_mul_finrank ℚ_[l] LL V, ← Module.finrank_mul_finrank ℚ_[l] LL V', h4]

end Main

end GlobalTheory.BkCoeff

namespace GlobalTheory

open GlobalTheory.PstCoeff GlobalTheory.BkCoeff

theorem bkACore_of_rationalDuality (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l)
    (h : GlobalTheory.Published.BlochKato.RationalDuality (P.PD K)) : bkACore (P.PD K) := by
  intro LL _ _ _ O _ _ hO A A' Pr hdR hP
  obtain ⟨-, hfin, hmt, htr, -⟩ := hO
  haveI := hfin
  haveI := hmt
  haveI := htr
  haveI : FiniteDimensional ℚ_[l] A.V := Module.Finite.trans LL A.V
  haveI : FiniteDimensional ℚ_[l] A'.V := Module.Finite.trans LL A'.V
  haveI : IsModuleTopology ℚ_[l] A.V := isModuleTopology_of_tower ℚ_[l] LL A.V
  haveI : IsModuleTopology ℚ_[l] A'.V := isModuleTopology_of_tower ℚ_[l] LL A'.V
  haveI : ContinuousConstSMul ℚ_[l] A.V := ⟨fun c => by
    have hc : Continuous fun x : A.V => algebraMap ℚ_[l] LL c • x := continuous_const_smul _
    simpa only [algebraMap_smul] using hc⟩
  haveI : ContinuousConstSMul ℚ_[l] A'.V := ⟨fun c => by
    have hc : Continuous fun x : A'.V => algebraMap ℚ_[l] LL c • x := continuous_const_smul _
    simpa only [algebraMap_smul] using hc⟩
  have key := h A.V A'.V (resQ A.ρ) (resQ A'.ρ) (trPair Pr) A.cont A'.cont
    ((isDR_resQ_iff P A.ρ).mpr hdR) (isDual1_trPair P hP)
  have cupS : ∀ (c : LL) (a : ↥(GK K) → A.V) (b : ↥(GK K) → A'.V),
      cupL (resQ A'.ρ) (trPair Pr) a (c • b) = fun x => Algebra.trace ℚ_[l] LL (c * cupL A'.ρ Pr a b x) := by
    intro c a b; funext x
    simp [cupL, trPair_apply]
  have cupS' : ∀ (c : LL) (a : ↥(GK K) → A.V) (b : ↥(GK K) → A'.V),
      cupL (resQ A'.ρ) (trPair Pr) (c • a) b = fun x => Algebra.trace ℚ_[l] LL (c * cupL A'.ρ Pr a b x) := by
    intro c a b; funext x
    simp [cupL, trPair_apply]
  have cup1 : ∀ (a : ↥(GK K) → A.V) (b : ↥(GK K) → A'.V),
      cupL (resQ A'.ρ) (trPair Pr) a b = fun x => Algebra.trace ℚ_[l] LL (1 * cupL A'.ρ Pr a b x) := by
    intro a b; funext x
    simp [cupL, trPair_apply]
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · rw [← mem_finiteCocycles_restrictScalars_Ql P, (key.1 a ha)]
    constructor
    · intro H b hb
      rw [cobL_iff_trace]
      intro c
      rw [← cupS]
      exact H (c • b) ((mem_finiteCocycles_restrictScalars_Ql P _ _).mpr ((finiteCocycles (P.PD K) A'.ρ).smul_mem c hb))
    · intro H b hb
      have := (cobL_iff_trace (P.PD K) _).mp (H b ((mem_finiteCocycles_restrictScalars_Ql P _ _).mp hb)) 1
      rwa [← cup1] at this
  · rw [← mem_finiteCocycles_restrictScalars_Ql P, (key.2 b hb)]
    constructor
    · intro H a ha
      rw [cobL_iff_trace]
      intro c
      rw [← cupS']
      exact H (c • a) ((mem_finiteCocycles_restrictScalars_Ql P _ _).mpr ((finiteCocycles (P.PD K) A.ρ).smul_mem c ha))
    · intro H a ha
      have := (cobL_iff_trace (P.PD K) _).mp (H a ((mem_finiteCocycles_restrictScalars_Ql P _ _).mp ha)) 1
      rwa [← cup1] at this

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoAnnihilatorOfRationalLocalDualityStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blochKatoAnnihilator_of_rationalLocalDuality : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l), GlobalTheory.Published.BlochKato.RationalDuality (P.PD K) → bkACore (P.PD K) := by
  first | exact @GlobalTheory.bkACore_of_rationalDuality | exact GlobalTheory.bkACore_of_rationalDuality | (intros; apply GlobalTheory.bkACore_of_rationalDuality <;> assumption)
end
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.BlochKatoLocalOfHyp

theorem bkAll_of_blochKatoLocal (hBK : GlobalTheory.Published.BlochKatoLocal) (hTD : Formalism.GaloisCohomology.LocalTateDualityK)
    (hEC : Formalism.GaloisCohomology.LocalEulerCharK) (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (hT : LocTied l P AI) (K : FinExt l) : Formalism.MainNotions.LocalSituation.bkAll (P.PD K) := by
  obtain ⟨hDim, hRat, hInt⟩ := hBK l P AI hT K
  have hA : bkACore (P.PD K) := GlobalTheory.T.blochKatoAnnihilator_of_rationalLocalDuality l P K hRat
  have hB : bkBCore (P.PD K) := GlobalTheory.T.blochKato_annihilator_of_integralLocalDuality l P K hInt
  exact ⟨hA, GlobalTheory.T.blochKatoDim_of_Ql_dimensionFormula l P K hDim, GlobalTheory.BKRightExact.bkARightExact_of_tied l P AI hT K, hB,
    GlobalTheory.T.breuilKisin_partC_of_partA_partB_finite_level hTD hEC l P AI hT K hA hB⟩

theorem blochKatoLocal_allPrimes_of_blochKato : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK →
    Formalism.GaloisCohomology.LocalEulerCharK → ∀ D : Formalism.BasicNotions.D7, Formalism.MainNotions.LocalSituation.Conclusion5 D := by
  intro hBK hTD hEC D l _ K
  exact bkAll_of_blochKatoLocal hBK hTD hEC l (D.loc l) (D.locA l) (D.locT l) K

end GlobalTheory.BlochKatoLocalOfHyp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSatAtConstOne
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.Mem.Chr GlobalTheory.LFun

namespace GlobalTheory.UnitaryBC

variable {E : Type} [Field E] [NumberField E]

theorem pLoc_conjFin_eq (c : E ≃+* E) (w : HeightOneSpectrum (𝓞 E)) (s : w.adicCompletion E →+* w.adicCompletion E)
    (hs : ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (c x)) (hv : ∀ x, Valued.v (s x) = Valued.v x) (x : Af E) :
    pLoc E w (conjFin c x) = s (pLoc E w x) := by
  have hw : ConjPl c w w := fun k => by
    have h1 : Valued.v (algebraMap E (w.adicCompletion E) k) = w.valuation E k :=
      w.valuedAdicCompletion_eq_valuation' k
    have h2 : Valued.v (algebraMap E (w.adicCompletion E) (c k)) = w.valuation E (c k) :=
      w.valuedAdicCompletion_eq_valuation' _
    rw [← h1, ← h2, ← hs, hv]
  have key : ∀ (u : HeightOneSpectrum (𝓞 E)) (_ : w = u) (φ : u.adicCompletion E →+* w.adicCompletion E),
      Continuous φ → (∀ k : E, φ (algebraMap E _ k) = algebraMap E _ (c k)) → φ (pLoc E u x) = s (pLoc E w x) := by
    rintro _ rfl φ h1 h2
    exact congrFun ((HeightOneSpectrum.denseRange_algebraMap E w).equalizer h1
      (continuous_of_valued_eq (w.valuedAdicCompletion_surjective E) s hv)
      (funext fun k => (h2 k).trans (hs k).symm)) _
  rw [pLoc_conjFin]
  exact key _ (eq_conjSrc hw) _ (conjLoc_spec c w).1 (conjLoc_spec c w).2.1

variable [IsCMField E]

theorem cT_cLoc {n : ℕ} (w : HeightOneSpectrum (𝓞 E)) (s : w.adicCompletion E →+* w.adicCompletion E)
    (hs : ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x))
    (hv : ∀ x, Valued.v (s x) = Valued.v x) (g : UA E n) : cT s (cLoc w g).val * (cLoc w g).val = 1 := by
  have hg : cT (conjAd E) g.1.val * 1 * g.1.val = 1 := g.2
  rw [Matrix.mul_one] at hg
  have h := congrArg ((pLoc E w).comp (pFin E)).mapMatrix hg
  rw [map_mul, map_one] at h
  rw [← h]
  congr 1
  refine Matrix.ext fun i j => ?_
  exact (pLoc_conjFin_eq (IsCMField.complexConj E).toRingEquiv w s hs hv (pFin E (g.1.val j i))).symm

end GlobalTheory.UnitaryBC

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoDimensionFormulaConcretePeriodRings
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoDimOfBkADimOfFontCore
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N TensorProduct

namespace GlobalTheory

theorem blochKatoDim_of_bkADim_of_fontCore (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l)
    [Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)] (h1 : LocalSituation.bkADim (P.PD K)) (h2 : LocalSituation.fontCore (P.PD K))
    (hO : GoodO (Qp := ℚ_[l]) ↥LL.1 ↥(OL LL)) : BlochKatoDim (P.PD K) ↥LL.1 := by
  unfold LocalSituation.bkADim at h1
  unfold LocalSituation.fontCore at h2
  unfold BlochKatoDim
  intro hs V _ _ _ _ _ _ _ _ _ ρ hc hcrys
  let A : GRep ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL) :=
    { V := V, ρ := ρ, cont := hc, modO := Module.compHom V (algebraMap ↥(OL LL) ↥LL.1),
      towO := by
        letI : Module ↥(OL LL) V := Module.compHom V (algebraMap ↥(OL LL) ↥LL.1)
        exact ⟨fun a b x => by rw [Algebra.smul_def, mul_smul]; rfl⟩ }
  have hF := h2 ↥LL.1 ↥(OL LL) hO A
  have hE := h1 ↥LL.1 ↥(OL LL) hO A (hF.2.2 hcrys)
  have hfin := hF.2.1.1
  dsimp only [A] at hE hfin
  obtain ⟨e1, e2⟩ := DeRhamSplit.main l P K LL hs V ρ hfin
  rw [hE, e1, e2 0]
  push_cast [Finset.sum_sub_distrib]
  ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoDimensionFormulaConcretePeriodRings
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.BlochKatoTied

theorem blochKatoDim_of_tied : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P),
    LocTied l P AI → ∀ (K LL : FinExt l) [Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)],
    BlochKatoDim (P.PD K) ↥LL.1 := by
  intro l _ P AI hT K LL _
  refine GlobalTheory.blochKatoDim_of_bkADim_of_fontCore l P K LL ?_
    (GlobalTheory.Per.FontaineTied.fontCore_all_of_tied l P AI hT K)
    (GlobalTheory.LocalIntegers.good_integers l LL).1
  intro LL' _ _ _ O _ _ hO A hdr
  exact (GlobalTheory.SeqDim.h1f_finrank l P AI hT K LL' O hO A hdr).2

end GlobalTheory.BlochKatoTied
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoDimensionFormulaConcretePeriodRingsStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blochKatoDimensionFormula_concretePeriodRings : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) [Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)], BlochKatoDim (P.PD K) ↥LL.1 := by
  first | exact @GlobalTheory.BlochKatoTied.blochKatoDim_of_tied | exact GlobalTheory.BlochKatoTied.blochKatoDim_of_tied | (intros; apply GlobalTheory.BlochKatoTied.blochKatoDim_of_tied <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRationalMirabolicMovingRowToLast
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRationalMirabolicMovingRowToLast
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

theorem mir_exists_row : ∀ (E : Type) [Field E] [NumberField E] (a m : ℕ), m + 1 < a →
    ∀ ξ : UnipotentBlockColumnIndex a (m + 1) (m + 1) → E, ξ ≠ 0 → ∃ γ : GL (Fin a) E, IsMir (m + 1) γ ∧
      ∀ t : UnipotentBlockColumnIndex a (m + 1) (m + 1), ∑ s : UnipotentBlockColumnIndex a (m + 1) (m + 1), eLast a (m + 1) s * γ.val s.1.1 t.1.1 = ξ t := by
  intro E _ _ a m hma ξ hξ
  classical
  set mm : Fin a := ⟨m, by omega⟩ with hmm
  set c : Fin a := ⟨m + 1, hma⟩ with hc
  let v : Fin a → E := fun k => if h : (k : ℕ) ≤ m then ξ ⟨(k, c), by simp [hc]; omega⟩ else 0
  have hv : ∀ t : UnipotentBlockColumnIndex a (m + 1) (m + 1), v t.1.1 = ξ t := by
    intro t
    have h1 := t.2
    have hle : (t.1.1 : ℕ) ≤ m := by omega
    simp only [v, dif_pos hle]
    congr 1
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Fin.ext; simp [hc]; omega
  obtain ⟨t₀, ht₀⟩ := Function.ne_iff.1 hξ
  set i₀ : Fin a := t₀.1.1 with hi₀
  have hi₀m : (i₀ : ℕ) ≤ m := by have := t₀.2; omega
  have hvi₀ : v i₀ ≠ 0 := by rw [hi₀, hv]; exact ht₀
  let M : Matrix (Fin a) (Fin a) E := Matrix.of fun i k =>
    if i = mm then v k else if i = i₀ then (if k = mm then 1 else 0) else (1 : Matrix (Fin a) (Fin a) E) i k
  have hdet : M.det ≠ 0 := by
    intro h0
    obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have hrow : ∀ j, (M *ᵥ x) j = 0 := fun j => by rw [hx]; rfl
    have hoff : ∀ j, j ≠ i₀ → x j = 0 := by
      intro j hj
      by_cases hjm : j = mm
      · have hi₀ne : i₀ ≠ mm := hjm ▸ Ne.symm hj
        have := hrow i₀
        simpa [M, Matrix.mulVec, dotProduct, hi₀ne, hjm] using this
      · have := hrow j
        simpa [M, Matrix.mulVec, dotProduct, hjm, hj, Matrix.one_apply] using this
    apply hx0
    funext j
    by_cases hj : j = i₀
    · subst hj
      have := hrow mm
      simp only [M, Matrix.mulVec, dotProduct, Matrix.of_apply, if_true] at this
      rw [Finset.sum_eq_single i₀ (fun k _ hk => by rw [hoff k hk, mul_zero]) (by simp)] at this
      exact (mul_eq_zero.1 this).resolve_left hvi₀
    · exact hoff j hj
  have hu : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).2 (isUnit_iff_ne_zero.2 hdet)
  refine ⟨hu.unit, ?_, ?_⟩
  · intro i k hik
    rw [IsUnit.unit_spec]
    simp only [M, Matrix.of_apply]
    rcases hik with hi | hk
    · have h1 : i ≠ mm := fun e => by rw [e] at hi; simp [hmm] at hi
      have h2 : i ≠ i₀ := fun e => by rw [e] at hi; omega
      simp [h1, h2]
    · have h1 : k ≠ mm := fun e => by rw [e] at hk; simp [hmm] at hk
      have h2 : k ≠ i₀ := fun e => by rw [e] at hk; omega
      split_ifs with e1 e2
      · subst e1
        simp only [v, Matrix.one_apply, h1.symm, if_false]
        rw [dite_eq_right (by omega)]
      · simp [e2, Matrix.one_apply, Ne.symm h2]
      · rfl
  · intro t
    rw [IsUnit.unit_spec]
    have hs : ∃ s : UnipotentBlockColumnIndex a (m + 1) (m + 1), s.1.1 = mm := ⟨⟨(mm, c), by simp [hmm, hc]⟩, rfl⟩
    obtain ⟨s₀, hs₀⟩ := hs
    rw [Finset.sum_eq_single s₀]
    · simp only [eLast, hs₀, hmm, M, Matrix.of_apply, if_true, one_mul]
      exact hv t
    · intro s _ hs
      have : ¬ ((s.1.1 : ℕ) + 1 = m + 1) := by
        intro e
        apply hs
        apply Subtype.ext
        have h1 := s.2; have h2 := s₀.2
        apply Prod.ext
        · apply Fin.ext; rw [hs₀]; simp [hmm]; omega
        · apply Fin.ext; omega
      simp only [eLast, if_neg this, zero_mul]
    · simp

end GlobalTheory.CuspGeneric
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRationalMirabolicMovingRowToLastStatement
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rationalMirabolic_moving_row_to_last : ∀ (E : Type) [Field E] [NumberField E] (a m : ℕ), m + 1 < a → ∀ ξ : UnipotentBlockColumnIndex a (m + 1) (m + 1) → E, ξ ≠ 0 → ∃ γ : GL (Fin a) E, IsMir (m + 1) γ ∧ ∀ t : UnipotentBlockColumnIndex a (m + 1) (m + 1), ∑ s : UnipotentBlockColumnIndex a (m + 1) (m + 1), eLast a (m + 1) s * γ.val s.1.1 t.1.1 = ξ t := by
  first | exact @GlobalTheory.CuspGeneric.mir_exists_row | exact GlobalTheory.CuspGeneric.mir_exists_row | (intros; apply GlobalTheory.CuspGeneric.mir_exists_row <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ColumnWhittakerTransformKeepsLaterLaw
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ColumnWhittakerTransformKeepsLaterLaw
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

noncomputable section

namespace GlobalTheory.CuspGeneric

section Mat

variable {R : Type} [CommRing R] {a : ℕ}

theorem posM_blk_apply {r m : ℕ} (x : UnipotentBlockColumnIndex a r m → R) (i l : Fin a) :
    posM (Subtype.val : UnipotentBlockColumnIndex a r m → Fin a × Fin a) x i l =
      if h : (i : ℕ) < r ∧ r ≤ (l : ℕ) ∧ (l : ℕ) ≤ m then x ⟨(i, l), h⟩ else 0 := by
  simp only [posM, Matrix.sum_apply, Matrix.single_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨(i, l), h⟩]
    · simp
    · rintro ⟨⟨i', l'⟩, h'⟩ _ hne
      rw [if_neg]
      rintro ⟨rfl, rfl⟩
      exact hne rfl
    · simp
  · refine Finset.sum_eq_zero fun t _ => ?_
    rw [if_neg]
    rintro ⟨e1, e2⟩
    apply h
    rw [← e1, ← e2]
    exact t.2

theorem posM_mul_posM_eq_zero {ι κ : Type} [Fintype ι] [Fintype κ] {p : ι → Fin a × Fin a}
    {q : κ → Fin a × Fin a} (h : ∀ s t, (p s).2 ≠ (q t).1) (x : ι → R) (y : κ → R) :
    posM p x * posM q y = 0 := by
  simp only [posM, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun t _ => ?_
  exact Matrix.single_mul_single_of_ne _ _ _ _ (h _ _) _

theorem blk_mul_support {j k : ℕ} (x : UnipotentBlockColumnIndex a j j → R) (y : UnipotentBlockColumnIndex a k k → R) (i l : Fin a)
    (h : (posM (Subtype.val : UnipotentBlockColumnIndex a j j → Fin a × Fin a) x *
      posM (Subtype.val : UnipotentBlockColumnIndex a k k → Fin a × Fin a) y) i l ≠ 0) :
    (i : ℕ) < j ∧ (l : ℕ) = k ∧ j < k := by
  rw [Matrix.mul_apply] at h
  obtain ⟨n, -, hn⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  simp only [posM_blk_apply] at hn
  split_ifs at hn with h1 h2
  all_goals first
    | (refine ⟨?_, ?_, ?_⟩ <;> omega)
    | simp at hn

theorem posM_blk_of_support {r m : ℕ} (M : Matrix (Fin a) (Fin a) R)
    (hM : ∀ i l, M i l ≠ 0 → (i : ℕ) < r ∧ r ≤ (l : ℕ) ∧ (l : ℕ) ≤ m) :
    posM (Subtype.val : UnipotentBlockColumnIndex a r m → Fin a × Fin a) (fun t => M t.1.1 t.1.2) = M := by
  ext i l
  rw [posM_blk_apply]
  split_ifs with h
  · rfl
  · by_contra h'
    exact h (hM i l fun e => h' e.symm)

theorem blkU_mul_blkU {j k : ℕ} (hjk : j < k) (x : UnipotentBlockColumnIndex a j j → R) (y : UnipotentBlockColumnIndex a k k → R) :
    (blkU x : GL (Fin a) R) * blkU y =
      blkU (fun t : UnipotentBlockColumnIndex a k k => y t + (posM (Subtype.val : UnipotentBlockColumnIndex a j j → Fin a × Fin a) x *
        posM (Subtype.val : UnipotentBlockColumnIndex a k k → Fin a × Fin a) y) t.1.1 t.1.2) * blkU x := by
  have key : ∀ X Y Y' : Matrix (Fin a) (Fin a) R, Y' = Y + X * Y → Y' * X = 0 →
      (1 + X) * (1 + Y) = (1 + Y') * (1 + X) := by
    intro X Y Y' h1 h2
    have e : (1 + Y') * (1 + X) = 1 + X + Y' + Y' * X := by noncomm_ring
    rw [e, h2, h1]
    noncomm_ring
  apply Units.ext
  refine key _ _ _ ?_ ?_
  · change posM _ (y + fun t : UnipotentBlockColumnIndex a k k => _) = _
    rw [posM_add, posM_blk_of_support]
    intro i l hne
    obtain ⟨h1, h2, h3⟩ := blk_mul_support x y i l hne
    refine ⟨?_, ?_, ?_⟩ <;> omega
  · refine posM_mul_posM_eq_zero (fun s t e => ?_) _ _
    have h1 := s.2.2.1
    have h2 := t.2.1
    have h3 := congrArg Fin.val e
    omega

end Mat

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem dot_eLast_shift {j k : ℕ} (hjk : j < k) (x : UnipotentBlockColumnIndex a j j → Ad E) (y : UnipotentBlockColumnIndex a k k → Ad E) :
    dot (eLast a k) (fun t : UnipotentBlockColumnIndex a k k => y t + (posM (Subtype.val : UnipotentBlockColumnIndex a j j → Fin a × Fin a) x *
        posM (Subtype.val : UnipotentBlockColumnIndex a k k → Fin a × Fin a) y) t.1.1 t.1.2) = dot (eLast a k) y := by
  have h0 : ∀ t : UnipotentBlockColumnIndex a k k, algebraMap E (Ad E) (eLast a k t) *
      (posM (Subtype.val : UnipotentBlockColumnIndex a j j → Fin a × Fin a) x *
        posM (Subtype.val : UnipotentBlockColumnIndex a k k → Fin a × Fin a) y) t.1.1 t.1.2 = 0 := by
    intro t
    unfold eLast
    split_ifs with h
    · have hz : (posM (Subtype.val : UnipotentBlockColumnIndex a j j → Fin a × Fin a) x *
          posM (Subtype.val : UnipotentBlockColumnIndex a k k → Fin a × Fin a) y) t.1.1 t.1.2 = 0 := by
        by_contra hne
        have := (blk_mul_support x y _ _ hne).1
        omega
      rw [hz, mul_zero]
    · simp
  simp only [dot, mul_add, Finset.sum_add_distrib, h0, Finset.sum_const_zero, add_zero]

theorem colT_law_of_good (E : Type) [Field E] [NumberField E] (a : ℕ) (ψ : AddChar (Ad E) ℂ) (m : ℕ)
    (f : GA E a → ℂ) (hf : Good ψ (m + 1) f) (k : ℕ) (hk : m + 1 < k) (y : UnipotentBlockColumnIndex a k k → Ad E)
    (g : GA E a) : colT ψ (m + 1) f (blkU y * g) = ψ (dot (eLast a k) y) * colT ψ (m + 1) f g := by
  simp only [colT, coefF]
  rw [← avg_const_mul]
  congr 1
  funext x
  have e1 : f (blkU x * (blkU y * g)) = ψ (dot (eLast a k) y) * f (blkU x * g) := by
    rw [← mul_assoc, blkU_mul_blkU hk x y, mul_assoc, hf.law k hk, dot_eLast_shift hk x y]
  rw [e1]
  ring

end GlobalTheory.CuspGeneric
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ColumnWhittakerTransformKeepsLaterLawStatement
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnWhittakerTransform_keeps_later_law : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ψ : AddChar (Ad E) ℂ) (m : ℕ) (f : GA E a → ℂ), Good ψ (m + 1) f → ∀ k, m + 1 < k → ∀ (y : UnipotentBlockColumnIndex a k k → Ad E) (g : GA E a), colT ψ (m + 1) f (blkU y * g) = ψ (dot (eLast a k) y) * colT ψ (m + 1) f g := by
  first | exact @GlobalTheory.CuspGeneric.colT_law_of_good | exact GlobalTheory.CuspGeneric.colT_law_of_good | (intros; apply GlobalTheory.CuspGeneric.colT_law_of_good <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSplitAdelicMatrixLocalComponent
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSplitAdelicMatrixLocalComponent
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

theorem exists_split_loc : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (w : HeightOneSpectrum (𝓞 E)) (g : GA E a), ∃ (h : GA E a) (gw : GL (Fin a) (w.adicCompletion E)),
      g = h * finGL E a (locGL E a w gw) ∧
        ∀ u : GL (Fin a) (w.adicCompletion E),
          h * finGL E a (locGL E a w u) = finGL E a (locGL E a w u) * h := by
  intro E _ _ _ a w g
  obtain ⟨gw, hgw⟩ : ∃ gw, gw = GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) g) := ⟨_, rfl⟩
  refine ⟨g * (finGL E a (locGL E a w gw))⁻¹, gw, by rw [inv_mul_cancel_right], fun u => ?_⟩
  have hk : GeneralLinearGroup.map (pLoc E w)
      (GeneralLinearGroup.map (pFin E) (g * (finGL E a (locGL E a w gw))⁻¹)) = 1 := by
    rw [map_mul, map_inv, pFin_finGL, map_mul, map_inv, pLoc_locGL, hgw, mul_inv_cancel]
  generalize g * (finGL E a (locGL E a w gw))⁻¹ = k at hk ⊢
  refine ga_ext ?_ ?_
  · rw [map_mul, map_mul, pInf_finGL, one_mul, mul_one]
  · rw [map_mul, map_mul, pFin_finGL]
    exact LocUniq.comm_locGL w hk u

end GlobalTheory.CuspGeneric
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSplitAdelicMatrixLocalComponentStatement
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_split_adelicMatrix_localComponent : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (w : HeightOneSpectrum (𝓞 E)) (g : GA E a), ∃ (h : GA E a) (gw : GL (Fin a) (w.adicCompletion E)), g = h * finGL E a (locGL E a w gw) ∧ ∀ u : GL (Fin a) (w.adicCompletion E), h * finGL E a (locGL E a w u) = finGL E a (locGL E a w u) * h := by
  first | exact @GlobalTheory.CuspGeneric.exists_split_loc | exact GlobalTheory.CuspGeneric.exists_split_loc | (intros; apply GlobalTheory.CuspGeneric.exists_split_loc <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalUpperUnipotentAdelicUpperUnipotent
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalUpperUnipotentAdelicUpperUnipotent
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspRep

theorem cornerGL_apply_loctri {R S : Type} [CommRing R] [CommRing S] {a : ℕ} (s : R →ₙ+* S)
    (g : GL (Fin a) R) (i j : Fin a) :
    (cornerGL a s g).val i j = (1 : Matrix (Fin a) (Fin a) S) i j - s ((1 : Matrix (Fin a) (Fin a) R) i j) + s (g.val i j) :=
  rfl

theorem cornerGL_apply_ne_loctri {R S : Type} [CommRing R] [CommRing S] {a : ℕ} (s : R →ₙ+* S)
    (g : GL (Fin a) R) {i j : Fin a} (h : i ≠ j) :
    (cornerGL a s g).val i j = s (g.val i j) := by
  rw [cornerGL_apply_loctri]
  simp [Matrix.one_apply_ne h]

theorem cornerGL_apply_diag_loctri {R S : Type} [CommRing R] [CommRing S] {a : ℕ} (s : R →ₙ+* S)
    (g : GL (Fin a) R) {j : Fin a} (h : g.val j j = 1) :
    (cornerGL a s g).val j j = 1 := by
  rw [cornerGL_apply_loctri, h]
  simp

theorem locTri_adelic : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (w : HeightOneSpectrum (𝓞 E)) (u : GL (Fin a) (w.adicCompletion E)), (∀ i j : Fin a, j < i → u.val i j = 0) → (∀ j : Fin a, u.val j j = 1) → (∀ i j : Fin a, j < i → (finGL E a (locGL E a w u)).val i j = 0) ∧ (∀ j : Fin a, (finGL E a (locGL E a w u)).val j j = 1) ∧ ∑ p : Fin a × Fin a with (p.2 : ℕ) = p.1 + 1, (finGL E a (locGL E a w u)).val p.1 p.2 = sFin E (sLoc E w (∑ p : Fin a × Fin a with (p.2 : ℕ) = p.1 + 1, u.val p.1 p.2)) := by
  intro E _ _ _ a w u hlow hdiag
  have hoff : ∀ i j : Fin a, i ≠ j → (finGL E a (locGL E a w u)).val i j = sFin E (sLoc E w (u.val i j)) := by
    intro i j h
    rw [finGL, cornerGL_apply_ne_loctri _ _ h, locGL, cornerGL_apply_ne_loctri _ _ h]
  refine ⟨?_, ?_, ?_⟩
  · intro i j h
    rw [hoff i j (ne_of_gt h), hlow i j h, map_zero, map_zero]
  · intro j
    exact cornerGL_apply_diag_loctri _ _ (cornerGL_apply_diag_loctri _ _ (hdiag j))
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_sum, map_sum]
      refine Finset.sum_congr rfl fun p hp => ?_
      have hp' : (p.2 : ℕ) = p.1 + 1 := (Finset.mem_filter.mp hp).2
      have hne : p.1 ≠ p.2 := by
        intro h; rw [h] at hp'; omega
      exact hoff p.1 p.2 hne

end GlobalTheory.CuspRep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalUpperUnipotentAdelicUpperUnipotentStatement
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localUpperUnipotent_adelic_upperUnipotent : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (w : HeightOneSpectrum (𝓞 E)) (u : GL (Fin a) (w.adicCompletion E)), (∀ i j : Fin a, j < i → u.val i j = 0) → (∀ j : Fin a, u.val j j = 1) → (∀ i j : Fin a, j < i → (finGL E a (locGL E a w u)).val i j = 0) ∧ (∀ j : Fin a, (finGL E a (locGL E a w u)).val j j = 1) ∧ ∑ p : Fin a × Fin a with (p.2 : ℕ) = p.1 + 1, (finGL E a (locGL E a w u)).val p.1 p.2 = sFin E (sLoc E w (∑ p : Fin a × Fin a with (p.2 : ℕ) = p.1 + 1, u.val p.1 p.2)) := by
  first | exact @GlobalTheory.CuspRep.locTri_adelic | exact GlobalTheory.CuspRep.locTri_adelic | (intros; apply GlobalTheory.CuspRep.locTri_adelic <;> assumption)
end
end
