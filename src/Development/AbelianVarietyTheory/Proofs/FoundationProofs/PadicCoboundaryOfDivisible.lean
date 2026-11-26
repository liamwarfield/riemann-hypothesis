module

public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveRootPowUnitSubProdProperties
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitInTowerAnEqSiegelUnitOnComplex
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDerivationTowerLevelAlgebraPrescribed
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmallTracesSubgroupGaloisTowerTop
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimitiveHahnSeriesInvertibleModPrimePow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueMeasUnivNeTopOfCompact
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueNormalizedCyclotomicTrace

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicCoboundaryOfDivisible
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicCoboundaryOfDivisible
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

namespace GlobalTheory.PadicH2Separated

theorem toZModPow_eq_iff {l : ℕ} [Fact l.Prime] (r : ℕ) (x y : ℤ_[l]) :
    PadicInt.toZModPow r x = PadicInt.toZModPow r y ↔ ‖x - y‖ ≤ (l : ℝ) ^ (-(r : ℤ)) := by
  rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub,
    sub_eq_zero]

theorem continuous_reduction {l : ℕ} [Fact l.Prime] (r : ℕ) :
    Continuous (PadicInt.toZModPow r : ℤ_[l] → ZMod (l ^ r)) := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 (fun x => ?_) |>.continuous
  have hl : (0 : ℝ) < (l : ℝ) ^ (-(r : ℤ)) :=
    zpow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) _
  filter_upwards [Metric.closedBall_mem_nhds x hl] with y hy
  rw [toZModPow_eq_iff]
  simpa [dist_eq_norm] using hy

theorem continuous_of_reductions {l : ℕ} [Fact l.Prime] {X : Type} [TopologicalSpace X]
    (b : X → ℤ_[l]) (hb : ∀ s : ℕ, Continuous fun x => PadicInt.toZModPow (s + 1) (b x)) :
    Continuous b := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [Metric.continuousAt_iff']
  intro ε hε
  obtain ⟨k, hk⟩ := PadicInt.exists_pow_neg_lt l hε
  have h1 : (1 : ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).one_le
  have hk' : (l : ℝ) ^ (-((k + 1 : ℕ) : ℤ)) ≤ (l : ℝ) ^ (-(k : ℤ)) :=
    zpow_le_zpow_right₀ h1 (by push_cast; omega)
  have hlc := ((IsLocallyConstant.iff_continuous _).2 (hb k)).eventually_eq x
  filter_upwards [hlc] with y hy
  rw [toZModPow_eq_iff] at hy
  rw [dist_eq_norm]
  exact lt_of_le_of_lt (hy.trans hk') hk

theorem finite_cocycles_compact_ultrametric_rep {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G] [AddCommGroup M]
    [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
    [Finite M] (rho : Representation R G M) [Finite (H1 rho)] : Finite (Z1 rho) := by
  have hB : Finite (B1 rho) :=
    Finite.of_surjective _ (LinearMap.surjective_rangeRestrict (d0 rho))
  have hB' : Finite ((B1 rho).comap (Z1 rho).subtype) :=
    Finite.of_injective (fun x => (⟨x.1.1, x.2⟩ : B1 rho)) (fun x y h => by
      apply Subtype.ext; apply Subtype.ext
      exact congrArg (fun t : B1 rho => (t : G → M)) h)
  have h1 : Finite ((B1 rho).comap (Z1 rho).subtype).toAddSubgroup := hB'
  have h2 : Finite (Z1 rho ⧸ ((B1 rho).comap (Z1 rho).subtype).toAddSubgroup) :=
    inferInstanceAs (Finite (H1 rho))
  exact Finite.of_addSubgroup_quotient ((B1 rho).comap (Z1 rho).subtype).toAddSubgroup

theorem finite_primitives {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousConstSMul R M] [Finite M] (rho : Representation R G M) [Finite (H1 rho)]
    (z : G × G → M) : {β : G → M | Continuous β ∧ d1 rho β = z}.Finite := by
  rcases Set.eq_empty_or_nonempty {β : G → M | Continuous β ∧ d1 rho β = z} with h | ⟨c, hc⟩
  · rw [h]; exact Set.finite_empty
  have hZ : (Z1 rho : Set (G → M)).Finite := finite_cocycles_compact_ultrametric_rep rho
  refine (hZ.image (fun f => f + c)).subset ?_
  rintro β ⟨hβ, hd⟩
  refine ⟨β - c, ⟨hβ.sub hc.1, fun g h => ?_⟩, by simp⟩
  have e : d1 rho (β - c) (g, h) = 0 := by rw [map_sub, hd, hc.2, sub_self]; rfl
  rw [d1_apply] at e
  have : (β - c) g + rho g ((β - c) h) - (β - c) (g * h) = 0 := by rw [← e]; abel
  exact (sub_eq_zero.1 this).symm

theorem mem_coboundaries_of_forall_pow : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (ρ : Representation ℤ_[l] Γ ℤ_[l]) (ρr : ∀ r : ℕ, Representation (ZMod (l ^ r)) Γ (ZMod (l ^ r))), (∀ r g x, PadicInt.toZModPow r (ρ g x) = ρr r g (PadicInt.toZModPow r x)) → (∀ r, 0 < r → Finite (H1 (ρr r))) → ∀ z ∈ Z2 ρ, (∀ r : ℕ, ∃ w ∈ Z2 ρ, z - (l : ℤ_[l]) ^ r • w ∈ B2 ρ) → z ∈ B2 ρ := by
  intro l _ Γ _ _ ρ ρr hρ hfin z _ hz
  have hd : ∀ (s : ℕ) (b : Γ → ℤ_[l]), d1 (ρr s) (fun g => PadicInt.toZModPow s (b g)) =
      fun p => PadicInt.toZModPow s (d1 ρ b p) := by
    intro s b
    funext ⟨g, h⟩
    simp only [d1_apply, map_add (f := _), map_sub, hρ]
  let α : ∀ s : ℕ, Set (Γ → ZMod (l ^ s)) := fun s =>
    {β | Continuous β ∧ d1 (ρr s) β = fun p => PadicInt.toZModPow s (z p)}
  have hα : ∀ s, (α (s + 1)).Finite := by
    intro s
    haveI : NeZero (l ^ (s + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    haveI := hfin (s + 1) (Nat.succ_pos s)
    exact finite_primitives (ρr (s + 1)) _
  let T : ℕ → Set (Γ → ℤ_[l]) := fun r =>
    ⋂ s, ⋂ (_ : s ≤ r), (fun (b : Γ → ℤ_[l]) g => PadicInt.toZModPow (s + 1) (b g)) ⁻¹' α (s + 1)
  have hcl : ∀ r, IsClosed (T r) := fun r =>
    isClosed_iInter fun s => isClosed_iInter fun _ => (hα s).isClosed.preimage
      (continuous_pi fun g => (continuous_reduction _).comp (continuous_apply g))
  have hne : ∀ r, (T r).Nonempty := by
    intro r
    obtain ⟨w, -, c, hc, hcd⟩ := hz (r + 1)
    refine ⟨c, Set.mem_iInter₂.2 fun s hs => ⟨(continuous_reduction _).comp hc, ?_⟩⟩
    rw [hd, hcd]
    funext p
    have h0 : PadicInt.toZModPow (s + 1) ((l : ℤ_[l]) ^ (r + 1)) = 0 := by
      rw [map_pow, map_natCast, ← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
      exact pow_dvd_pow _ (by omega)
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul, h0, zero_mul, sub_zero]
  have hdec : ∀ r, T (r + 1) ⊆ T r := fun r b hb =>
    Set.mem_iInter₂.2 fun s hs => Set.mem_iInter₂.1 hb s (hs.trans (Nat.le_succ r))
  obtain ⟨b, hb⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed T hdec hne
    (hcl 0).isCompact hcl
  have hb' : ∀ s, (fun g => PadicInt.toZModPow (s + 1) (b g)) ∈ α (s + 1) := fun s =>
    Set.mem_iInter₂.1 (Set.mem_iInter.1 hb s) s le_rfl
  refine ⟨b, continuous_of_reductions b fun s => (hb' s).1, ?_⟩
  funext p
  rw [← PadicInt.ext_of_toZModPow]
  intro n
  cases n with
  | zero =>
    haveI : Subsingleton (ZMod (l ^ 0)) := by rw [pow_zero]; infer_instance
    exact Subsingleton.elim _ _
  | succ n =>
    have := (hb' n).2
    rw [hd] at this
    exact congrFun this p

end GlobalTheory.PadicH2Separated
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicCoboundaryOfDivisibleStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padic_coboundary_of_divisible : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (ρ : Representation ℤ_[l] Γ ℤ_[l]) (ρr : ∀ r : ℕ, Representation (ZMod (l ^ r)) Γ (ZMod (l ^ r))), (∀ r g x, PadicInt.toZModPow r (ρ g x) = ρr r g (PadicInt.toZModPow r x)) → (∀ r, 0 < r → Finite (H1 (ρr r))) → ∀ z ∈ Z2 ρ, (∀ r : ℕ, ∃ w ∈ Z2 ρ, z - (l : ℤ_[l]) ^ r • w ∈ B2 ρ) → z ∈ B2 ρ := by
  first | exact @GlobalTheory.PadicH2Separated.mem_coboundaries_of_forall_pow | exact GlobalTheory.PadicH2Separated.mem_coboundaries_of_forall_pow | (intros; apply GlobalTheory.PadicH2Separated.mem_coboundaries_of_forall_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.JTLevelOne
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.JTLevelOne
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem jT_invariant (γ : SL(2, ℤ)) (τ : ℍ) : jT (γ • τ) = jT τ :=
  ReciprocityTheory.ChartRestriction.L1.jT_smul γ τ

theorem DD_mul_jT_smul (γ : SL(2, ℤ)) (τ : ℍ) : DD τ * jT (γ • τ) = E₄ τ ^ 3 := by
  rw [jT_invariant, jT, ReciprocityTheory.ChartRestriction.L1.AA, mul_div_cancel₀ _ (ReciprocityTheory.ChartRestriction.L1.DD_ne_zero τ)]

theorem jT_level_one : ∀ E : Subring ℂ, Lv E 1 1 jT ∧ ∀ (γ : SL(2, ℤ)) (τ : ℍ), jT (γ • τ) = jT τ := by
  intro E
  refine ⟨⟨fun γ _ τ => jT_invariant γ τ, fun γ => ?_⟩, jT_invariant⟩
  have hE4 : QAll (· ∈ E) 1 ⇑E₄ := ((eis_q 1 one_pos _ (Or.inl rfl)).2.1) E
  have h3 : QAll (· ∈ E) 1 fun τ => E₄ τ ^ 3 := (QAllSubring.ring_closed E 1 one_pos).2.2.2.2.1 _ 3 hE4
  have hfun : (fun τ => DD τ ^ 1 * jT (γ • τ)) = fun τ => E₄ τ ^ 3 := by
    funext τ; rw [pow_one, DD_mul_jT_smul]
  rw [hfun]; exact h3

end GlobalTheory.FN
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.JTLevelOneStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lv_jT_one_and_jT_smul_eq : ∀ E : Subring ℂ, Lv E 1 1 jT ∧ ∀ (γ : SL(2, ℤ)) (τ : ℍ), jT (γ • τ) = jT τ := by
  first | exact @GlobalTheory.FN.jT_level_one | exact GlobalTheory.FN.jT_level_one | (intros; apply GlobalTheory.FN.jT_level_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIntTwoCocycleEqPowSmulOfReductionCoboundary
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIntTwoCocycleEqPowSmulOfReductionCoboundary
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

namespace GlobalTheory

theorem padicInt_two_cocycle_eq_pow_smul_of_reduction_coboundary :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [ContinuousMul Γ] (ρ : Representation ℤ_[l] Γ ℤ_[l]), ContAction ρ → ∀ (r : ℕ) (ρr : Representation (ZMod (l ^ r)) Γ (ZMod (l ^ r))), (∀ g x, PadicInt.toZModPow r (ρ g x) = ρr g (PadicInt.toZModPow r x)) → ∀ z ∈ Z2 ρ, (fun p => PadicInt.toZModPow r (z p)) ∈ B2 ρr → ∃ w ∈ Z2 ρ, z - (l : ℤ_[l]) ^ r • w ∈ B2 ρ := by
  intro l _ Γ _ _ _ ρ hρ r ρr hc z hz hB
  obtain ⟨c, hcc, hcd⟩ := (separated_dvr_second_cohomology_mem _ _).1 hB
  have hsurj : Function.Surjective (PadicInt.toZModPow (p := l) r) := ZMod.ringHom_surjective _
  choose s hs using hsurj
  have hsc : Continuous s := continuous_of_discreteTopology
  have hb : d1 ρ (s ∘ c) ∈ B2 ρ := (separated_dvr_second_cohomology_mem _ _).2 ⟨s ∘ c, hsc.comp hcc, rfl⟩
  have hy : z - d1 ρ (s ∘ c) ∈ Z2 ρ := (Z2 ρ).sub_mem hz (coboundaries2_le_cocycles2 ρ hρ hb)
  have hdiv : ∀ p, ∃ a : ℤ_[l], (l : ℤ_[l]) ^ r * a = (z - d1 ρ (s ∘ c)) p := by
    rintro ⟨g, h⟩
    have h1 : (z - d1 ρ (s ∘ c)) (g, h) ∈ RingHom.ker (PadicInt.toZModPow (p := l) r) := by
      have h2 := congrFun hcd (g, h)
      rw [d1_apply] at h2
      rw [RingHom.mem_ker, Pi.sub_apply, d1_apply, map_sub, map_add (f := _), map_sub, hc]
      simp only [Function.comp_apply, hs]
      rw [h2, sub_self]
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at h1
    obtain ⟨a, ha⟩ := h1
    exact ⟨a, ha.symm⟩
  choose w hw using hdiv
  have hne : (l : ℤ_[l]) ^ r ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have hemb : Topology.IsClosedEmbedding (fun x : ℤ_[l] => (l : ℤ_[l]) ^ r * x) :=
    Continuous.isClosedEmbedding (continuous_const.mul continuous_id)
      (mul_right_injective₀ hne)
  have hw' : (l : ℤ_[l]) ^ r • w = z - d1 ρ (s ∘ c) := funext hw
  refine ⟨w, (mem_cocycles2 _ _).2 ⟨?_, fun g h k => ?_⟩, ?_⟩
  · refine hemb.isInducing.continuous_iff.2 ?_
    have : (fun x : ℤ_[l] => (l : ℤ_[l]) ^ r * x) ∘ w = z - d1 ρ (s ∘ c) := funext hw
    rw [this]
    exact hy.1
  · have e := ((mem_cocycles2 _ _).1 hy).2 g h k
    rw [← hw'] at e
    simp only [Pi.smul_apply, map_smul] at e
    rw [← smul_sub, ← smul_add, ← smul_sub, smul_eq_mul] at e
    exact (mul_eq_zero.1 e).resolve_left hne
  · rw [hw', sub_sub_cancel]
    exact hb

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIntTwoCocycleEqPowSmulOfReductionCoboundaryStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_z2_sub_pow_smul_mem_b2_of_reduction : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [ContinuousMul Γ] (ρ : Representation ℤ_[l] Γ ℤ_[l]), ContAction ρ → ∀ (r : ℕ) (ρr : Representation (ZMod (l ^ r)) Γ (ZMod (l ^ r))), (∀ g x, PadicInt.toZModPow r (ρ g x) = ρr g (PadicInt.toZModPow r x)) → ∀ z ∈ Z2 ρ, (fun p => PadicInt.toZModPow r (z p)) ∈ B2 ρr → ∃ w ∈ Z2 ρ, z - (l : ℤ_[l]) ^ r • w ∈ B2 ρ := by
  first | exact @GlobalTheory.padicInt_two_cocycle_eq_pow_smul_of_reduction_coboundary | exact GlobalTheory.padicInt_two_cocycle_eq_pow_smul_of_reduction_coboundary | (intros; apply GlobalTheory.padicInt_two_cocycle_eq_pow_smul_of_reduction_coboundary <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCuspExpansionDiscriminantIntegerLeadingOne
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCuspExpansionDiscriminantIntegerLeadingOne
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FNExpD

theorem hasQ_DD_int : HasQ 1 DD fun n => ((PowerSeries.coeff n ReciprocityTheory.ChartRestriction.L1.dZ : ℤ) : ℂ) := by
  rw [hasQ_iff]
  intro τ
  have := ReciprocityTheory.ChartRestriction.L1.isMF_DD.hasSum τ
  rw [← ReciprocityTheory.ChartRestriction.L1.dC_eq] at this
  simpa [ReciprocityTheory.ChartRestriction.L1.qm, ReciprocityTheory.ChartRestriction.L1.dC, PowerSeries.coeff_map] using this

theorem expD : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ), ∃ h : HahnSeries ℚ Ω, IsExp ε DD h ∧ h ≠ 0 ∧
    h.leadingCoeff = 1 ∧ ∀ r : ℚ, ∃ n : ℤ, h.coeff r = n := by
  intro Ω _ ε
  have hD : HasQ 1 DD fun n => ε ((PowerSeries.coeff n ReciprocityTheory.ChartRestriction.L1.dZ : ℤ) : Ω) := by
    simpa only [map_intCast] using hasQ_DD_int
  obtain ⟨h, hexp, hk, hz⟩ := GlobalTheory.T.exists_hahnSeries_isExp_of_hasQ Ω ε 1 DD
    (fun n => ((PowerSeries.coeff n ReciprocityTheory.ChartRestriction.L1.dZ : ℤ) : Ω)) one_pos hD
  have h1 : h.coeff 1 = 1 := by
    have := hk 1
    simpa [ReciprocityTheory.ChartRestriction.L1.dZ_coeff_one] using this
  have hlow : ∀ r : ℚ, r < 1 → h.coeff r = 0 := by
    intro r hr
    by_cases hr' : ∃ k : ℕ, r = (k : ℚ) / ((1 : ℕ) : ℚ)
    · obtain ⟨k, rfl⟩ := hr'
      have hk1 : (k : ℚ) < 1 := by simpa using hr
      have hk0 : k = 0 := by
        have : k < 1 := by exact_mod_cast hk1
        omega
      subst hk0
      rw [hk 0]
      simp [ReciprocityTheory.ChartRestriction.L1.dZ_coeff_zero]
    · push_neg at hr'
      exact hz r hr'
  have hne : h ≠ 0 := HahnSeries.ne_zero_of_coeff_ne_zero (h1 ▸ one_ne_zero)
  have hord : h.order = 1 := by
    refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero (h1 ▸ one_ne_zero)) ?_
    by_contra hlt
    push_neg at hlt
    exact (HahnSeries.coeff_order_eq_zero.not.mpr hne) (hlow _ hlt)
  refine ⟨h, hexp, hne, ?_, ?_⟩
  · rw [HahnSeries.leadingCoeff_eq, hord, h1]
  · intro r
    by_cases hr : ∃ k : ℕ, r = (k : ℚ) / ((1 : ℕ) : ℚ)
    · obtain ⟨k, rfl⟩ := hr
      exact ⟨_, hk k⟩
    · push_neg at hr
      exact ⟨0, by simpa using hz r hr⟩

end GlobalTheory.FNExpD
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCuspExpansionDiscriminantIntegerLeadingOneStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cuspExpansion_discriminant_integer_leading_one : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ), ∃ h : HahnSeries ℚ Ω, IsExp ε DD h ∧ h ≠ 0 ∧ h.leadingCoeff = 1 ∧ ∀ r : ℚ, ∃ n : ℤ, h.coeff r = n := by
  first | exact @GlobalTheory.FNExpD.expD | exact GlobalTheory.FNExpD.expD | (intros; apply GlobalTheory.FNExpD.expD <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContCohomologyTransportMulEquiv
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContCohomologyTransportMulEquiv
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

namespace GlobalTheory

theorem dn_comp_monoidHom {R Γ Γ' M : Type*} [CommRing R] [Group Γ] [Group Γ'] [AddCommGroup M]
    [Module R M] (φ : Γ' →* Γ) (ρ : Representation R Γ M) (ρ' : Representation R Γ' M)
    (h : ∀ g m, ρ' g m = ρ (φ g) m) (n : ℕ) (f : (Fin n → Γ) → M) (g : Fin (n + 1) → Γ') :
    dn ρ' n (fun x => f (fun i => φ (x i))) g = dn ρ n f (fun i => φ (g i)) := by
  show ρ' (g 0) (f fun i => φ (g i.succ)) + (Finset.univ.sum fun j : Fin (n + 1) =>
      (-1 : R) ^ ((j : ℕ) + 1) • f (fun i => φ (Fin.contractNth j (· * ·) g i))) =
    ρ (φ (g 0)) (f fun i => φ (g i.succ)) + Finset.univ.sum fun j : Fin (n + 1) =>
      (-1 : R) ^ ((j : ℕ) + 1) • f (Fin.contractNth j (· * ·) fun i => φ (g i))
  rw [h]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 2
  exact Fin.comp_contractNth (· * ·) (· * ·) (map_mul φ) j g

theorem contCohomology_transport_mulEquiv :
    ∀ (R : Type) [CommRing R] (Γ Γ' : Type) [Group Γ] [TopologicalSpace Γ] [Group Γ'] [TopologicalSpace Γ'] (M : Type) [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (e : Γ' ≃* Γ), Continuous e → Continuous e.symm → ∀ (ρ : Representation R Γ M) (ρ' : Representation R Γ' M), (∀ g m, ρ' g m = ρ (e g) m) → Nonempty (H1 ρ ≃ H1 ρ') ∧ Nonempty (H2 ρ ≃ H2 ρ') ∧ (Subsingleton (Hn ρ 3) → Subsingleton (Hn ρ' 3)) := by
  intro R _ Γ Γ' _ _ _ _ M _ _ _ _ e he he' ρ ρ' h
  have h' : ∀ g m, ρ g m = ρ' (e.symm g) m := fun g m => by rw [h, e.apply_symm_apply]
  refine ⟨⟨⟨pairH1DecompositionMap ρ ρ' e.toMonoidHom he LinearMap.id continuous_id (fun g m => (h g m).symm),
      pairH1DecompositionMap ρ' ρ e.symm.toMonoidHom he' LinearMap.id continuous_id (fun g m => (h' g m).symm),
      ?_, ?_⟩⟩,
    ⟨⟨compatiblePairH2 ρ ρ' e.toMonoidHom he LinearMap.id continuous_id (fun g m => (h g m).symm),
      compatiblePairH2 ρ' ρ e.symm.toMonoidHom he' LinearMap.id continuous_id (fun g m => (h' g m).symm),
      ?_, ?_⟩⟩, ?_⟩
  · intro x
    induction x using Submodule.Quotient.induction_on with
    | H f =>
      refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun g => ?_))
      exact congrArg f.1 (e.apply_symm_apply g)
  · intro x
    induction x using Submodule.Quotient.induction_on with
    | H f =>
      refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun g => ?_))
      exact congrArg f.1 (e.symm_apply_apply g)
  · intro x
    induction x using Submodule.Quotient.induction_on with
    | H f =>
      refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun g => ?_))
      exact congrArg f.1 (Prod.ext (e.apply_symm_apply g.1) (e.apply_symm_apply g.2))
  · intro x
    induction x using Submodule.Quotient.induction_on with
    | H f =>
      refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun g => ?_))
      exact congrArg f.1 (Prod.ext (e.symm_apply_apply g.1) (e.symm_apply_apply g.2))
  · intro hs
    rw [GlobalTheory.Published.subsingleton_Hn_succ_iff] at hs ⊢
    intro f hf hd
    obtain ⟨c, hc, hcf⟩ := hs (fun x => f (fun i => e.symm (x i)))
      (hf.comp (continuous_pi fun i => he'.comp (continuous_apply i))) (by
        funext g
        have := dn_comp_monoidHom e.symm.toMonoidHom ρ' ρ h' 3 f g
        rw [hd] at this
        exact this)
    refine ⟨fun x => c (fun i => e (x i)),
      hc.comp (continuous_pi fun i => he.comp (continuous_apply i)), ?_⟩
    funext g
    have := dn_comp_monoidHom e.toMonoidHom ρ ρ' h 2 c g
    rw [hcf] at this
    refine this.trans ?_
    exact congrArg f (funext fun i => e.symm_apply_apply _)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContCohomologyTransportMulEquivStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_H1_H2_equiv_of_continuous_mulEquiv : ∀ (R : Type) [CommRing R] (Γ Γ' : Type) [Group Γ] [TopologicalSpace Γ] [Group Γ'] [TopologicalSpace Γ'] (M : Type) [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (e : Γ' ≃* Γ), Continuous e → Continuous e.symm → ∀ (ρ : Representation R Γ M) (ρ' : Representation R Γ' M), (∀ g m, ρ' g m = ρ (e g) m) → Nonempty (H1 ρ ≃ H1 ρ') ∧ Nonempty (H2 ρ ≃ H2 ρ') ∧ (Subsingleton (Hn ρ 3) → Subsingleton (Hn ρ' 3)) := by
  first | exact @GlobalTheory.contCohomology_transport_mulEquiv | exact GlobalTheory.contCohomology_transport_mulEquiv | (intros; apply GlobalTheory.contCohomology_transport_mulEquiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardDualZmodModuleEqCardStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_dual_zmod_module_eq_card : ∀ (n : ℕ) [NeZero n] (A : Type) [AddCommGroup A] [Module (ZMod n) A] [Finite A], Nat.card (Module.Dual (ZMod n) A) = Nat.card A := by
  first | exact @GlobalTheory.ZModDual.card_dual_eq | exact GlobalTheory.ZModDual.card_dual_eq | (intros; apply GlobalTheory.ZModDual.card_dual_eq <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDerivationTowerLevelAlgebraPrescribedStatement
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_derivation_towerLevelAlgebra_prescribed : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (n : ℕ), 1 ≤ n → ∀ (M : Type) [AddCommGroup M] [Module (integralClosure (O0 p) Ω) M] (μ ν : M), (Polynomial.aeval (zS T n) (Polynomial.derivative (Polynomial.cyclotomic (p ^ n) (O0 p)))) • μ = 0 → ((p : (integralClosure (O0 p) Ω)) ^ n * qS T n ^ (p ^ n - 1)) • ν = 0 → ∃ D : (integralClosure (O0 p) Ω) → M, IsDerOn (levelAlg T n) D ∧ D (zS T n) = μ ∧ D (qS T n) = ν := by
  first | exact @GlobalTheory.AlmostEt.LevDer.exists_derOn_levelAlg | exact GlobalTheory.AlmostEt.LevDer.exists_derOn_levelAlg | (intros; apply GlobalTheory.AlmostEt.LevDer.exists_derOn_levelAlg <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegralTraceEqZetaSubOneTop
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegralTraceEqZetaSubOneTop
open GlobalTheory.K5

theorem GlobalTheory.exists_integral_trace_eq_zeta_sub_one_top : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (S : Finset Ω), (∀ s ∈ S, IsInt (p := p) s) → ∀ j : ℕ, 1 ≤ j →
  ∃ (y : Ω) (E : Finset (Gal p Ω)), IsInt (p := p) y ∧ (∀ g ∈ E, g ∈ ⨅ n, Gn T n) ∧
    (∀ h ∈ ⨅ n, Gn T n, ∃! g, g ∈ E ∧ h y = g y ∧ ∀ s ∈ S, h s = g s) ∧
    ∑ g ∈ E, g y = T.ζ j - 1 :=
  fun p _ hp Ω _ _ hc T S _ j hj => GlobalTheory.T.smallTraces_subgroup_galois_towerTop p Ω hp hc T _ le_rfl S j hj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegralTraceEqZetaSubOneTopStatement
open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_sum_conj_eq_zeta_sub_one : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (S : Finset Ω), (∀ s ∈ S, IsInt (p := p) s) → ∀ j : ℕ, 1 ≤ j →
  ∃ (y : Ω) (E : Finset (Gal p Ω)), IsInt (p := p) y ∧ (∀ g ∈ E, g ∈ ⨅ n, Gn T n) ∧
    (∀ h ∈ ⨅ n, Gn T n, ∃! g, g ∈ E ∧ h y = g y ∧ ∀ s ∈ S, h s = g s) ∧
    ∑ g ∈ E, g y = T.ζ j - 1 := by
  first | exact @GlobalTheory.exists_integral_trace_eq_zeta_sub_one_top | exact GlobalTheory.exists_integral_trace_eq_zeta_sub_one_top | (intros; apply GlobalTheory.exists_integral_trace_eq_zeta_sub_one_top <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimitiveHahnSeriesNotZeroDivisorModPrimePow
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimitiveHahnSeriesNotZeroDivisorModPrimePow
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory

theorem primCan_mul_dvd {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (c : Ω) (a b : HahnSeries ℚ Ω)
    (ha : ∀ r, a.coeff r ∈ A) (hb : ∀ r, ∃ z ∈ A, b.coeff r = c * z) :
    ∀ r, ∃ z ∈ A, (a * b).coeff r = c * z := by
  intro r
  rw [HahnSeries.coeff_mul]
  refine Finset.sum_induction _ (fun x => ∃ z ∈ A, x = c * z) ?_ ?_ ?_
  · rintro x y ⟨z, hz, rfl⟩ ⟨w, hw, rfl⟩
    exact ⟨z + w, A.add_mem _ _ hz hw, by ring⟩
  · exact ⟨0, A.zero_mem, by simp⟩
  · intro ij _
    obtain ⟨z, hz, e⟩ := hb ij.2
    exact ⟨a.coeff ij.1 * z, A.mul_mem _ _ (ha _) hz, by rw [e]; ring⟩

theorem primCan : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω),
    ((l : ℕ) : Ω) ∈ A.nonunits → ∀ (n L : ℕ) (P φ : HahnSeries ℚ Ω), 0 < L → Prim A P →
    (∀ r : ℚ, P.coeff r ≠ 0 → (r * L).den = 1) → (∀ r, φ.coeff r ∈ A) →
    (∀ r, CgA A l n ((φ * P).coeff r) 0) → ∀ r, CgA A l n (φ.coeff r) 0 := by
  intro Ω _ _ _ l _ A hl n L P φ hL hP hden hφ hφP
  obtain ⟨Q, hQ, -, hQP⟩ := GlobalTheory.T.primitive_hahnSeries_invertible_mod_prime_pow l A hl n L P hL hP hden
  have h1 : ∀ r, ∃ z ∈ A, (Q * P - 1).coeff r = (l : Ω) ^ n * z := by
    intro r
    obtain ⟨z, hz, e⟩ := hQP r
    exact ⟨z, hz, by rw [HahnSeries.coeff_sub]; exact e⟩
  have h2 := primCan_mul_dvd A _ φ _ hφ h1
  have h3 : ∀ r, ∃ z ∈ A, (Q * (φ * P)).coeff r = (l : Ω) ^ n * z := by
    refine primCan_mul_dvd A _ Q _ hQ ?_
    intro r
    obtain ⟨z, hz, e⟩ := hφP r
    exact ⟨z, hz, by rw [← e, sub_zero]⟩
  intro r
  obtain ⟨z, hz, ez⟩ := h3 r
  obtain ⟨w, hw, ew⟩ := h2 r
  have hid : φ = Q * (φ * P) - φ * (Q * P - 1) := by ring
  refine ⟨z - w, sub_mem hz hw, ?_⟩
  rw [sub_zero, hid, HahnSeries.coeff_sub, ez, ew]
  ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimitiveHahnSeriesNotZeroDivisorModPrimePowStatement
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitiveHahnSeries_not_zeroDivisor_modPrimePow : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), ((l : ℕ) : Ω) ∈ A.nonunits → ∀ (n L : ℕ) (P φ : HahnSeries ℚ Ω), 0 < L → Prim A P → (∀ r : ℚ, P.coeff r ≠ 0 → (r * L).den = 1) → (∀ r, φ.coeff r ∈ A) → (∀ r, CgA A l n ((φ * P).coeff r) 0) → ∀ r, CgA A l n (φ.coeff r) 0 := by
  first | exact @GlobalTheory.primCan | exact GlobalTheory.primCan | (intros; apply GlobalTheory.primCan <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralOverJInvariantOfHasSomeLevelOver
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralOverJInvariantOfHasSomeLevelOver
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

noncomputable section
namespace GlobalTheory.FN

theorem gact_one_bij (N : ℕ) : ActBij (gact N 1) := by
  intro γ
  simp only [gact, one_mul, inv_one, mul_one]
  exact (Group.mulRight_bijective _)

theorem redGL_one (N : ℕ) : redGL N 1 = 1 := by
  ext i j; simp [redGL]

theorem rel_div (w n : ℕ) (D x J : ℂ) (hD : D ≠ 0) (s : Fin n → ℂ) (P : Fin n → Polynomial ℂ)
    (hs : ∀ j : Fin n, s j = D ^ (w * (n - j)) * (P j).eval J)
    (h : (D ^ w * x) ^ n + ∑ j, s j * (D ^ w * x) ^ (j : ℕ) = 0) :
    x ^ n + ∑ j, (P j).eval J * x ^ (j : ℕ) = 0 := by
  have hD' : D ^ (w * n) ≠ 0 := pow_ne_zero _ hD
  refine (mul_eq_zero.mp ?_).resolve_left hD'
  rw [← h, mul_add, Finset.mul_sum]
  congr 1
  · rw [mul_pow, pow_mul]
  · refine Finset.sum_congr rfl fun j _ => ?_
    have hj : (j : ℕ) ≤ n := j.2.le
    have e : w * n = w * (n - j) + w * j := by rw [← mul_add, Nat.sub_add_cancel hj]
    rw [hs, e, mul_pow, pow_add, ← pow_mul]
    ring

theorem integral_over_jT : ∀ (E : Subring ℂ) (f : ℍ → ℂ), InR E f → ∃ (n : ℕ) (c : Fin n → Polynomial ℂ), (∀ i k, (c i).coeff k ∈ E) ∧ ∀ τ, f τ ^ n + ∑ i, (c i).eval (jT τ) * f τ ^ (i : ℕ) = 0 := by
  intro E f ⟨N, w, hN, hinv, hq⟩
  haveI : NeZero N := ⟨hN.ne'⟩
  have hslash : ∀ γ : SL(2, ℤ), (fun τ => DD τ ^ w * f τ) ∣[((12 * w : ℕ) : ℤ)] γ = fun τ => DD τ ^ w * f (γ • τ) :=
    fun γ => GlobalTheory.T.modularDiscriminant_pow_mul_slash_twelve_mul w f γ
  have hΓ : ∀ γ ∈ CongruenceSubgroup.Gamma N, (fun τ => DD τ ^ w * f τ) ∣[((12 * w : ℕ) : ℤ)] γ = (fun τ => DD τ ^ w * f τ) := by
    intro γ hγ
    rw [hslash]; funext τ; rw [hinv γ hγ τ]
  obtain ⟨F, hFam, hFγ, hF0⟩ := GlobalTheory.T.exists_slTwoPermutedModularFamily_of_level N ((12 * w : ℕ) : ℤ) _ hΓ
  have hQ : ∀ α, QAll (· ∈ E) N (F α) := by
    intro α
    rcases hF0 α with ⟨γ, rfl⟩ | h0
    · rw [hFγ, hslash]; exact hq γ
    · rw [h0]
      refine ⟨fun _ => 0, fun τ => ?_, fun _ => E.zero_mem⟩
      simpa using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0)
  have h1 : F 1 = fun τ => DD τ ^ w * f τ := by
    rw [← redGL_one N, hFγ]; exact SlashAction.slash_one _ _
  obtain ⟨s, hs, hpoly⟩ := GlobalTheory.T.permutedModularFamily_monic_poly_coeff_invariant (GL (Fin 2) (ZMod N)) (gact N 1) (12 * w) N F E hN
    (gact_one_bij N) hFam hQ
  have key := hpoly 1
  rw [h1] at key
  clear hpoly hFam hF0 hFγ hQ h1 hslash hΓ
  revert s
  generalize Fintype.card (GL (Fin 2) (ZMod N)) = n
  intro s hs key
  have hP : ∀ j : Fin n, ∃ P : Polynomial ℂ, (∀ i, P.coeff i ∈ E) ∧
      ∀ τ, s j τ = DD τ ^ (w * (n - j)) * P.eval (jT τ) := by
    intro j
    refine GlobalTheory.QFam.exists_eq_DD_pow_mul_eval_jT E N (w * (n - j)) (s j) hN (fun γ => ?_) (hs j).2
    have := (hs j).1 γ
    convert this using 3
    push_cast; ring
  choose P hPc hPe using hP
  exact ⟨n, P, hPc, fun τ => rel_div w n (DD τ) (f τ) (jT τ) (ReciprocityTheory.ChartRestriction.L1.DD_ne_zero τ)
    (fun j => s j τ) P (fun j => hPe j τ) (key τ)⟩

end GlobalTheory.FN
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralOverJInvariantOfHasSomeLevelOverStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_over_jInvariant_of_hasSomeLevelOver : ∀ (E : Subring ℂ) (f : ℍ → ℂ), InR E f → ∃ (n : ℕ) (c : Fin n → Polynomial ℂ), (∀ i k, (c i).coeff k ∈ E) ∧ ∀ τ, f τ ^ n + ∑ i, (c i).eval (jT τ) * f τ ^ (i : ℕ) = 0 := by
  first | exact @GlobalTheory.FN.integral_over_jT | exact GlobalTheory.FN.integral_over_jT | (intros; apply GlobalTheory.FN.integral_over_jT <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.QzTorsionZmodEmbedding
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.QzTorsionZmodEmbedding
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

namespace GlobalTheory

section

variable (l : ℕ) [Fact l.Prime]

private theorem qzTor_smul_mk (x : ℤ_[l]) (q : ℚ_[l]) :
    x • QZ.mk l q = QZ.mk l ((x : ℚ_[l]) * q) := rfl

private theorem qzTor_mk_eq_zero (q : ℚ_[l]) :
    QZ.mk l q = 0 ↔ ∃ z : ℤ_[l], (z : ℚ_[l]) = q :=
  Submodule.Quotient.mk_eq_zero (ZlSub l)

private theorem qzTor_mk_surj (a : QZ l) : ∃ q, QZ.mk l q = a :=
  Submodule.Quotient.mk_surjective (ZlSub l) a

private theorem qzTor_key (r : ℕ) (x : ℤ_[l]) :
    x • QZ.mk l (((l : ℚ_[l]) ^ r)⁻¹) = 0 ↔ PadicInt.toZModPow r x = 0 := by
  have hl : ((l : ℚ_[l]) ^ r) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero)
  rw [qzTor_smul_mk, qzTor_mk_eq_zero, ← RingHom.mem_ker, PadicInt.ker_toZModPow,
    Ideal.mem_span_singleton']
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, Subtype.ext ?_⟩
    have : ((z * (l : ℤ_[l]) ^ r : ℤ_[l]) : ℚ_[l]) = (z : ℚ_[l]) * (l : ℚ_[l]) ^ r := by
      push_cast; rfl
    rw [this, hz]
    field_simp
  · rintro ⟨z, rfl⟩
    refine ⟨z, ?_⟩
    push_cast
    field_simp

end

theorem qz_torsion_zmod_embedding (l : ℕ) [Fact l.Prime] :
    (∀ a : QZ l, ∃ r : ℕ, (l : ℤ_[l]) ^ r • a = 0) ∧
    ∀ r : ℕ, ∃ ι : ZMod (l ^ r) →+ QZ l, Function.Injective ι ∧
      (∀ a : QZ l, (l : ℤ_[l]) ^ r • a = 0 ↔ a ∈ Set.range ι) ∧
      ∀ (x : ℤ_[l]) (y : ZMod (l ^ r)), ι (PadicInt.toZModPow r x * y) = x • ι y := by
  have hp : l.Prime := Fact.out
  refine ⟨fun a => ?_, fun r => ?_⟩
  · obtain ⟨q, rfl⟩ := qzTor_mk_surj l a
    have hlt : ‖(l : ℚ_[l])‖ < 1 := Padic.norm_p_lt_one
    have hpos : (0 : ℝ) < (‖q‖ + 1)⁻¹ := by positivity
    obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one hpos hlt
    refine ⟨r, ?_⟩
    rw [qzTor_smul_mk, qzTor_mk_eq_zero]
    have hle : ‖(l : ℚ_[l]) ^ r * q‖ ≤ 1 := by
      rw [norm_mul, norm_pow]
      calc ‖(l : ℚ_[l])‖ ^ r * ‖q‖ ≤ (‖q‖ + 1)⁻¹ * (‖q‖ + 1) :=
            mul_le_mul hr.le (by linarith) (norm_nonneg _) hpos.le
        _ = 1 := inv_mul_cancel₀ (by positivity)
    refine ⟨⟨_, hle⟩, ?_⟩
    push_cast
    rfl
  · have hl : ((l : ℚ_[l]) ^ r) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.ne_zero)
    set e : QZ l := QZ.mk l (((l : ℚ_[l]) ^ r)⁻¹) with he
    have hs : Function.Surjective (PadicInt.toZModPow (p := l) r) := by
      haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ hp.ne_zero⟩
      exact ZMod.ringHom_surjective _
    have hwd : ∀ x x' : ℤ_[l], PadicInt.toZModPow r x = PadicInt.toZModPow r x' →
        x • e = x' • e := by
      intro x x' h
      rw [← sub_eq_zero, ← sub_smul, he, qzTor_key, map_sub, h, sub_self]
    have hinv := Function.surjInv_eq hs
    let ι : ZMod (l ^ r) →+ QZ l := AddMonoidHom.mk' (fun y => Function.surjInv hs y • e) (by
      intro y y'
      rw [← add_smul]
      apply hwd
      rw [map_add (f := _), hinv, hinv, hinv])
    have hι : ∀ x : ℤ_[l], ι (PadicInt.toZModPow r x) = x • e := fun x =>
      hwd _ _ (hinv _)
    refine ⟨ι, ?_, fun a => ⟨fun ha => ?_, ?_⟩, fun x y => ?_⟩
    · rw [injective_iff_map_eq_zero]
      intro y hy
      obtain ⟨x, rfl⟩ := hs y
      rw [hι, he, qzTor_key] at hy
      exact hy
    · obtain ⟨q, rfl⟩ := qzTor_mk_surj l a
      rw [qzTor_smul_mk, qzTor_mk_eq_zero] at ha
      obtain ⟨z, hz⟩ := ha
      refine ⟨PadicInt.toZModPow r z, ?_⟩
      rw [hι, he, qzTor_smul_mk, hz]
      congr 1
      push_cast
      field_simp
    · rintro ⟨y, rfl⟩
      obtain ⟨x, rfl⟩ := hs y
      rw [hι, smul_smul, he, qzTor_key, ← RingHom.mem_ker, PadicInt.ker_toZModPow]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    · obtain ⟨x', rfl⟩ := hs y
      rw [← map_mul, hι, hι, mul_smul]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.QzTorsionZmodEmbeddingStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.qz_torsion_and_exists_zmod_pow_embedding : ∀ (l : ℕ) [Fact l.Prime], (∀ a : QZ l, ∃ r : ℕ, (l : ℤ_[l]) ^ r • a = 0) ∧ ∀ r : ℕ, ∃ ι : ZMod (l ^ r) →+ QZ l, Function.Injective ι ∧ (∀ a : QZ l, (l : ℤ_[l]) ^ r • a = 0 ↔ a ∈ Set.range ι) ∧ ∀ (x : ℤ_[l]) (y : ZMod (l ^ r)), ι (PadicInt.toZModPow r x * y) = x • ι y := by
  first | exact @GlobalTheory.qz_torsion_zmod_embedding | exact GlobalTheory.qz_torsion_zmod_embedding | (intros; apply GlobalTheory.qz_torsion_zmod_embedding <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerPotentialRelationLinearHeckeStable
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsKummerPotentialIncrementLinearLaws
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsKummerPotentialIncrementLinearLaws
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.KZ.H3

theorem gamma_mem_of_dvd {M N : ℕ} (hMN : M ∣ N) {δ : SL(2, ℤ)} (hδ : δ ∈ CongruenceSubgroup.Gamma N) :
    δ ∈ CongruenceSubgroup.Gamma M := by
  rw [CongruenceSubgroup.Gamma_mem] at hδ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hδ
  have key : ∀ k : ℤ, ((k : ZMod N) = 1 → (k : ZMod M) = 1) ∧ ((k : ZMod N) = 0 → (k : ZMod M) = 0) := by
    intro k
    constructor
    · intro h
      have := congrArg (ZMod.castHom hMN (ZMod M)) h
      rwa [map_intCast, map_one] at this
    · intro h
      have := congrArg (ZMod.castHom hMN (ZMod M)) h
      rwa [map_intCast, map_zero] at this
  exact ⟨(key _).1 h1, (key _).2 h2, (key _).2 h3, (key _).1 h4⟩

theorem isKummerPotentialIncrement_linear_laws : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], (∀ (x x' : X.Khat l) (h h' : ℂ → ℤ_[l]), R1 X l x h → R1 X l x' h' → R1 X l (x + x') (h + h')) ∧ R1 X l 0 0 ∧ (∀ (c : ℤ_[l]) (x : X.Khat l) (h : ℂ → ℤ_[l]), R1 X l x h → R1 X l (c • x) (c • h)) ∧ (∀ (m : Matrix (Fin 2) (Fin 2) ℤ) (x : X.Khat l) (h : ℂ → ℤ_[l]), 0 < m.det → R1 X l x h → R1 X l (X.kmap l (X.sl (toGQ m)).toRingEquiv x) (fun z => h (mob (toGQ m) z))) := by
  intro Ω _ _ ε X l _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x x' h h' hx hx' n
    obtain ⟨χ, hK, M, hM, hI⟩ := hx n
    obtain ⟨χ', hK', M', hM', hI'⟩ := hx' n
    refine ⟨χ + χ', ((GlobalTheory.T.isKummerCharacterAtLevel_add_zero_congr Ω ε X l n).1 x x' χ χ' hK hK'), M * M', Nat.mul_pos hM hM', ?_⟩
    intro δ hδ z hz
    have e1 := hI δ (gamma_mem_of_dvd (dvd_mul_right M M') hδ) z hz
    have e2 := hI' δ (gamma_mem_of_dvd (dvd_mul_left M' M) hδ) z hz
    have : (h + h') (mob (ofSL δ) z) - (h + h') z = (h (mob (ofSL δ) z) - h z) + (h' (mob (ofSL δ) z) - h' z) := by
      simp only [Pi.add_apply]; ring
    rw [this, map_add (f := _), e1, e2, Pi.add_apply]
  · intro n
    refine ⟨0, (GlobalTheory.T.isKummerCharacterAtLevel_add_zero_congr Ω ε X l n).2.1, 1, Nat.one_pos, ?_⟩
    intro δ _ z _
    simp
  · intro c x h hx n
    obtain ⟨χ, hK, M, hM, hI⟩ := hx n
    refine ⟨fun δ => PadicInt.toZModPow n c * χ δ, GlobalTheory.T.isKummerCharacterAtLevel_padicInt_smul Ω ε X l n c x χ hK, M, hM, ?_⟩
    intro δ hδ z hz
    have : (c • h) (mob (ofSL δ) z) - (c • h) z = c * (h (mob (ofSL δ) z) - h z) := by
      simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [this, map_mul, hI δ hδ z hz]
  · intro m x h hm hx n
    obtain ⟨χ, hK, M, hM, hI⟩ := hx n
    refine ⟨fun δ => χ (cj m δ), GlobalTheory.T.isKummerCharacterAtLevel_integral_matrix_conj Ω ε X l n m x χ hm hK, M * m.det.natAbs,
      Nat.mul_pos hM (Int.natAbs_pos.mpr hm.ne'), ?_⟩
    intro δ hδ z hz
    obtain ⟨hc1, hc2⟩ := GlobalTheory.T.integralConjugateSL2Int_laws.1 m M hm δ hδ
    have hmz : mob (toGQ m) z ∈ Hs := GlobalTheory.T.glTwoPosRatMobius_basic_laws.1 (toGQ m) z hz
    have hcomm := GlobalTheory.T.integralConjugateSL2Int_laws.2.2 m δ (cj m δ) hm hc1 z hz
    show PadicInt.toZModPow n (h (mob (toGQ m) (mob (ofSL δ) z)) - h (mob (toGQ m) z)) = χ (cj m δ)
    rw [hcomm]
    exact hI (cj m δ) hc2 (mob (toGQ m) z) hmz

end GlobalTheory.KZ.H3
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsKummerPotentialIncrementLinearLawsStatement
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.r1_smul_and_kmap_of_r1_linear_laws : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], (∀ (x x' : X.Khat l) (h h' : ℂ → ℤ_[l]), R1 X l x h → R1 X l x' h' → R1 X l (x + x') (h + h')) ∧ R1 X l 0 0 ∧ (∀ (c : ℤ_[l]) (x : X.Khat l) (h : ℂ → ℤ_[l]), R1 X l x h → R1 X l (c • x) (c • h)) ∧ (∀ (m : Matrix (Fin 2) (Fin 2) ℤ) (x : X.Khat l) (h : ℂ → ℤ_[l]), 0 < m.det → R1 X l x h → R1 X l (X.kmap l (X.sl (toGQ m)).toRingEquiv x) (fun z => h (mob (toGQ m) z))) := by
  first | exact @GlobalTheory.KZ.H3.isKummerPotentialIncrement_linear_laws | exact GlobalTheory.KZ.H3.isKummerPotentialIncrement_linear_laws | (intros; apply GlobalTheory.KZ.H3.isKummerPotentialIncrement_linear_laws <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerPotentialRelationLinearHeckeStable
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

noncomputable section

namespace GlobalTheory.KZ.H3.RelOp

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem kmap_eq_self (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (φ : X.K ≃+* X.K) (hφ : ∀ f, φ f = f)
    (x : X.Khat l) : X.kmap l φ x = x := by
  have h1 : Units.map φ.toMonoidHom = MonoidHom.id X.Kˣ := by
    ext u; simp [hφ]
  have h2 : (AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Units.map φ.toMonoidHom)) :
      Additive X.Kˣ →ₗ[ℤ] Additive X.Kˣ) = LinearMap.id := by
    rw [h1]; ext u; rfl
  unfold Tower.kmap
  rw [h2, LinearMap.baseChange_id, AdicCompletion.map_id]
  rfl

theorem mob_one' (z : ℂ) : mob 1 z = z := by
  simp [mob, ent]

section Main

variable (X : Tower Ω ε) (l : ℕ) [Fact l.Prime]

theorem rel_add {b b' : X.Fn l} {F F' : ℂ → MvPolynomial (Fin 2) ℤ_[l]} (h : Rel X l b F) (h' : Rel X l b' F') :
    Rel X l (b + b') (F + F') := by
  intro u
  have := (GlobalTheory.T.r1_smul_and_kmap_of_r1_linear_laws Ω ε X l).1 _ _ _ _ (h u) (h' u)
  convert this using 1 <;> first | rfl | (funext z; simp)

theorem rel_zero : Rel X l 0 0 := by
  intro u
  convert (GlobalTheory.T.r1_smul_and_kmap_of_r1_linear_laws Ω ε X l).2.1 using 1 <;> first | rfl | (funext z; simp)

theorem rel_smul (c : ℤ_[l]) {b : X.Fn l} {F : ℂ → MvPolynomial (Fin 2) ℤ_[l]} (h : Rel X l b F) :
    Rel X l (c • b) (c • F) := by
  intro u
  have := (GlobalTheory.T.r1_smul_and_kmap_of_r1_linear_laws Ω ε X l).2.2.1 c _ _ (h u)
  convert this using 1 <;> first | rfl | (funext z; simp)

theorem rel_act (m : Matrix (Fin 2) (Fin 2) ℤ) {b : X.Fn l} {F : ℂ → MvPolynomial (Fin 2) ℤ_[l]} (h : Rel X l b F) :
    Rel X l (X.act l m b) (opP ℤ_[l] m F) := by
  intro u
  have e : (fun z => MvPolynomial.eval u (opP ℤ_[l] m F z)) =
      fun z => (fun z => MvPolynomial.eval (mZl l m *ᵥ u) (F z)) (mob (toGQ m) z) := by
    funext z
    simp only [opP, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Betti.eval_slP]; rfl
  show R1 X l (X.kmap l (X.sl (toGQ m)).toRingEquiv (b (mZl l m *ᵥ u))) _
  rw [e]
  by_cases hm : 0 < m.det
  · exact (GlobalTheory.T.r1_smul_and_kmap_of_r1_linear_laws Ω ε X l).2.2.2 m _ _ hm (h _)
  · have h1 : toGQ m = 1 := by unfold toGQ; rw [dite_eq_right hm]
    rw [h1, kmap_eq_self X l _ (fun f => X.sl_one f)]
    simp only [mob_one']
    exact h _

theorem rel_sum {ι : Type} (s : Finset ι) (m : ι → Matrix (Fin 2) (Fin 2) ℤ) {b : X.Fn l}
    {F : ℂ → MvPolynomial (Fin 2) ℤ_[l]} (h : Rel X l b F) :
    Rel X l ((∑ j ∈ s, X.act l (m j)) b) ((∑ j ∈ s, opP ℤ_[l] (m j)) F) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using rel_zero X l
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, LinearMap.add_apply, LinearMap.add_apply]
    exact rel_add X l (rel_act X l _ h) ih

end Main

end GlobalTheory.KZ.H3.RelOp


open GlobalTheory.KZ.H3.RelOp in
theorem GlobalTheory.KZ.H3.rel_ops : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime],
    (∀ b b' F F', Rel X l b F → Rel X l b' F' → Rel X l (b + b') (F + F')) ∧ Rel X l 0 0 ∧
    (∀ (c : ℤ_[l]) b F, Rel X l b F → Rel X l (c • b) (c • F)) ∧
    (∀ (m : Matrix (Fin 2) (Fin 2) ℤ) b F, Rel X l b F → Rel X l (X.act l m b) (opP ℤ_[l] m F)) ∧
    (∀ (N : ℕ) (T : Letter) b F, Rel X l b F → Rel X l (X.op N l T b) (opL ℤ_[l] N l T F)) := by
  intro Ω _ _ ε X l _
  refine ⟨fun b b' F F' h h' => rel_add X l h h', rel_zero X l, fun c b F h => rel_smul X l c h,
    fun m b F h => rel_act X l m h, fun N T b F h => ?_⟩
  cases T with
  | T q =>
    simp only [Tower.op, Tower.heckeT, opL, LinearMap.add_apply]
    exact rel_add X l (rel_sum X l _ _ h) (rel_act X l _ h)
  | U =>
    simp only [Tower.op, Tower.heckeU, opL]
    exact rel_sum X l _ _ h
  | D d =>
    simp only [Tower.op, Tower.diam, opL]
    exact rel_act X l _ h
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerPotentialRelationLinearHeckeStableStatement
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerPotentialRelation_linear_hecke_stable : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], (∀ b b' F F', Rel X l b F → Rel X l b' F' → Rel X l (b + b') (F + F')) ∧ Rel X l 0 0 ∧ (∀ (c : ℤ_[l]) b F, Rel X l b F → Rel X l (c • b) (c • F)) ∧ (∀ (m : Matrix (Fin 2) (Fin 2) ℤ) b F, Rel X l b F → Rel X l (X.act l m b) (opP ℤ_[l] m F)) ∧ (∀ (N : ℕ) (T : Letter) b F, Rel X l b F → Rel X l (X.op N l T b) (opL ℤ_[l] N l T F)) := by
  first | exact @GlobalTheory.KZ.H3.rel_ops | exact GlobalTheory.KZ.H3.rel_ops | (intros; apply GlobalTheory.KZ.H3.rel_ops <;> assumption)
end
end
