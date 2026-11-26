module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.BaseEx

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RationalVectorsAdelesFundamentalDomainMassOne
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RationalVectorsAdelesFundamentalDomainMassOne
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.SWQ.RatLattice

variable {F : Type} [Field F] [NumberField F]

theorem closure_range_rat (N : ℕ) :
    AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F))) =
      AddSubgroup.pi Set.univ fun _ : Fin N => (algebraMap F (AF F)).range.toAddSubgroup := by
  apply le_antisymm
  · rw [AddSubgroup.closure_le]
    rintro _ ⟨ξ, rfl⟩ l _
    exact ⟨ξ l, rfl⟩
  · intro u hu
    choose ξ hξ using fun l => hu l trivial
    have : u = rat ξ := funext fun l => (hξ l).symm
    rw [this]
    exact AddSubgroup.subset_closure ⟨ξ, rfl⟩

theorem mem_closure_iff (N : ℕ) (u : Fin N → AF F) :
    u ∈ AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F))) ↔ ∃ ξ, u = rat ξ := by
  rw [closure_range_rat]
  constructor
  · intro hu
    choose ξ hξ using fun l => hu l trivial
    exact ⟨ξ, funext fun l => (hξ l).symm⟩
  · rintro ⟨ξ, rfl⟩ l _
    exact ⟨ξ l, rfl⟩

theorem rat_injective (N : ℕ) : Function.Injective (rat : (Fin N → F) → (Fin N → AF F)) := by
  haveI : Nontrivial (AF F) := by
    show Nontrivial (AdeleRing (𝓞 F) F)
    unfold AdeleRing
    infer_instance
  intro ξ η h
  funext l
  exact (algebraMap F (AF F)).injective (congrFun h l)

theorem isFD_pi {Y : Type} [AddCommGroup Y] [MeasurableSpace Y] (ν : Measure Y) [SigmaFinite ν]
    {A : AddSubgroup Y} {D : Set Y} (hF : IsAddFundamentalDomain A D ν) (n : ℕ) :
    IsAddFundamentalDomain (AddSubgroup.pi Set.univ fun _ : Fin n => A) (Set.univ.pi fun _ : Fin n => D)
      (Measure.pi fun _ : Fin n => ν) := by
  have hq (i : Fin n) := Measure.quasiMeasurePreserving_eval (fun _ : Fin n => ν) i
  refine ⟨?_, ?_, ?_⟩
  · rw [Set.univ_pi_eq_iInter]
    exact NullMeasurableSet.iInter fun i => hF.nullMeasurableSet.preimage (hq i)
  · have := (ae_all_iff (μ := (Measure.pi fun _ : Fin n => ν))).2 fun i => (hq i).ae hF.ae_covers
    filter_upwards [this] with z hz
    choose a ha using hz
    exact ⟨⟨fun i => a i, fun i _ => (a i).2⟩, fun i _ => ha i⟩
  · intro a b hab
    obtain ⟨i, hi⟩ : ∃ i, a.1 i ≠ b.1 i := by
      by_contra! h
      exact hab (Subtype.ext (funext h))
    have h := hF.aedisjoint (i := ⟨a.1 i, a.2 i trivial⟩) (j := ⟨b.1 i, b.2 i trivial⟩)
      fun e => hi (congrArg Subtype.val e)
    refine measure_mono_null ?_ ((hq i).preimage_null h)
    rintro z ⟨⟨u, hu, hu'⟩, ⟨v, hv, hv'⟩⟩
    exact ⟨⟨u i, hu i trivial, congrFun hu' i⟩, ⟨v i, hv i trivial, congrFun hv' i⟩⟩

end GlobalTheory.SWQ.RatLattice

open GlobalTheory.SWQ.RatLattice in
theorem GlobalTheory.SWQ.rat_lattice_fundamentalDomain : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (ν : Measure (AF F)), IsCov1 ν → (muV N ν).IsAddHaarMeasure ∧ (∀ u : (Fin N → AF F), u ∈ (AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F)))) ↔ ∃ ξ, u = rat ξ) ∧ Function.Injective (rat : (Fin N → F) → (Fin N → AF F)) ∧ (∃ K : Set (Fin N → AF F), IsCompact K ∧ ∀ u, ∃ ξ, u - rat ξ ∈ K) ∧ ∃ D : Set (Fin N → AF F), MeasurableSet D ∧ IsAddFundamentalDomain (AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F)))) D (muV N ν) ∧ muV N ν D = 1 := by
  intro F _ _ N ν hν
  obtain ⟨hH, D₀, hD₀m, hD₀, hD₀1⟩ := hν
  haveI := hH
  refine ⟨?_, mem_closure_iff N, rat_injective N, ?_, ?_⟩
  · unfold muV
    infer_instance
  · obtain ⟨K, hK, hKc⟩ := GlobalTheory.AdeleCocompact.exists_compact_adele F
    refine ⟨Set.univ.pi fun _ => K, isCompact_univ_pi fun _ => hK, fun u => ?_⟩
    choose ξ hξ using fun l => hKc (u l)
    exact ⟨ξ, fun l _ => hξ l⟩
  · refine ⟨Set.univ.pi fun _ => D₀, MeasurableSet.univ_pi fun _ => hD₀m, ?_, ?_⟩
    · rw [closure_range_rat]
      exact isFD_pi ν hD₀ N
    · unfold muV
      rw [Measure.pi_pi]
      simp [hD₀1]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RationalVectorsAdelesFundamentalDomainMassOneStatement
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalVectors_adeles_fundamentalDomain_mass_one : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (ν : Measure (AF F)), IsCov1 ν → (muV N ν).IsAddHaarMeasure ∧ (∀ u : (Fin N → AF F), u ∈ (AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F)))) ↔ ∃ ξ, u = rat ξ) ∧ Function.Injective (rat : (Fin N → F) → (Fin N → AF F)) ∧ (∃ K : Set (Fin N → AF F), IsCompact K ∧ ∀ u, ∃ ξ, u - rat ξ ∈ K) ∧ ∃ D : Set (Fin N → AF F), MeasurableSet D ∧ IsAddFundamentalDomain (AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F)))) D (muV N ν) ∧ muV N ν D = 1 := by
  first | exact @GlobalTheory.SWQ.rat_lattice_fundamentalDomain | exact GlobalTheory.SWQ.rat_lattice_fundamentalDomain | (intros; apply GlobalTheory.SWQ.rat_lattice_fundamentalDomain <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsAdelesHaarMeasureCovolumeOne
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsAdelesHaarMeasureCovolumeOne
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal Pointwise

namespace GlobalTheory.SWQ

theorem exists_adeles_haarMeasure_covolume_one : ∀ (F : Type) [Field F] [NumberField F], ∃ ν : Measure (AF F), IsCov1 ν := by
  intro F _ _
  let Γ : AddSubgroup (AF F) := (algebraMap F (AF F)).range.toAddSubgroup
  have hdisc : DiscreteTopology Γ := by
    obtain ⟨U, hU, hU0⟩ := GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero F
    obtain ⟨V, hVU, hVo, h0V⟩ := mem_nhds_iff.1 hU
    rw [discreteTopology_iff_isOpen_singleton_zero]
    have : ({0} : Set Γ) = ((↑) : Γ → AF F) ⁻¹' V := by
      ext ⟨x, hx⟩
      obtain ⟨y, rfl⟩ := hx
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      constructor
      · intro h
        have : algebraMap F (AF F) y = 0 := congrArg Subtype.val h
        rw [this]; exact h0V
      · intro h
        have := hU0 y (hVU h)
        subst this
        ext; simp
    rw [this]
    exact hVo.preimage continuous_subtype_val
  letI : MeasurableSpace (Multiplicative (AF F)) := borel _
  haveI : BorelSpace (Multiplicative (AF F)) := ⟨rfl⟩
  haveI : SecondCountableTopology (Multiplicative (AF F)) := inferInstanceAs (SecondCountableTopology (AF F))
  haveI : DiscreteTopology (AddSubgroup.toSubgroup Γ) := hdisc
  obtain ⟨hc, D, hDm, hD⟩ := GlobalTheory.discreteSubgroup_countable_and_exists_strict_fundamentalDomain (AddSubgroup.toSubgroup Γ)
  haveI : Countable Γ := hc
  let D' : Set (AF F) := Multiplicative.ofAdd ⁻¹' D
  have hDm' : MeasurableSet D' := hDm
  have hfd : ∀ m : Measure (AF F), IsAddFundamentalDomain Γ D' m := by
    intro m
    refine IsAddFundamentalDomain.mk' hDm'.nullMeasurableSet ?_
    intro x
    obtain ⟨γ, hγ, huniq⟩ := hD (Multiplicative.ofAdd x)
    refine ⟨⟨γ.1.toAdd, γ.2⟩, hγ, ?_⟩
    intro g hg
    have := huniq ⟨Multiplicative.ofAdd g.1, g.2⟩ hg
    ext
    exact congrArg (fun s => Multiplicative.toAdd s.1) this
  let μ : Measure (AF F) := Measure.addHaar
  have hμD := hfd μ
  obtain ⟨K, hK, hKx⟩ := GlobalTheory.AdeleCocompact.exists_compact_adele F
  have hfin : μ D' < ∞ := by
    calc μ D' ≤ μ (⋃ γ : Γ, (γ +ᵥ K) ∩ D') := by
          apply measure_mono
          intro d hd
          obtain ⟨x, hx⟩ := hKx d
          refine Set.mem_iUnion.2 ⟨⟨algebraMap F (AF F) x, x, rfl⟩, ?_, hd⟩
          refine ⟨_, hx, ?_⟩
          show algebraMap F (AF F) x + (d - algebraMap F (AF F) x) = d
          abel
      _ ≤ ∑' γ : Γ, μ ((γ +ᵥ K) ∩ D') := measure_iUnion_le _
      _ = μ K := (hμD.measure_eq_tsum K).symm
      _ < ∞ := hK.measure_lt_top
  have hpos : μ D' ≠ 0 := by
    intro h0
    have := hμD.measure_eq_tsum' Set.univ
    simp only [Set.univ_inter] at this
    have h2 : ∀ g : Γ, μ (g +ᵥ D') = 0 := fun g => by
      rw [measure_vadd]; exact h0
    simp only [h2, tsum_zero] at this
    exact (Measure.measure_univ_ne_zero.2 (NeZero.ne μ)) this
  refine ⟨(μ D')⁻¹ • μ, ?_, D', hDm', hfd _, ?_⟩
  · exact Measure.IsAddHaarMeasure.smul (μ := μ) (ENNReal.inv_ne_zero.2 hfin.ne) (ENNReal.inv_ne_top.2 hpos)
  · rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hpos hfin.ne]

end GlobalTheory.SWQ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsAdelesHaarMeasureCovolumeOneStatement
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_measure_isCov1 : ∀ (F : Type) [Field F] [NumberField F], ∃ ν : Measure (AF F), IsCov1 ν := by
  first | exact @GlobalTheory.SWQ.exists_adeles_haarMeasure_covolume_one | exact GlobalTheory.SWQ.exists_adeles_haarMeasure_covolume_one | (intros; apply GlobalTheory.SWQ.exists_adeles_haarMeasure_covolume_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsSquareOneAddFourMul
open NumberField IsDedekindDomain GlobalTheory.UnitaryBC

namespace GlobalTheory.HenselSquare

open IsDedekindDomain.HeightOneSpectrum IsLocalRing Polynomial

theorem isAdicComplete_integers (F : Type) [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F)) :
    IsAdicComplete (maximalIdeal (u.adicCompletionIntegers F)) (u.adicCompletionIntegers F) := by
  letI := GlobalTheory.LocalData.complRel u
  haveI := GlobalTheory.LocalData.isLocalField u
  haveI := Valuation.Compatible.ofValuation
    (Valued.v : Valuation (u.adicCompletion F) (WithZero (Multiplicative ℤ)))
  have hE : (ValuativeRel.valuation (u.adicCompletion F)).IsEquiv
      (Valued.v : Valuation (u.adicCompletion F) (WithZero (Multiplicative ℤ))) :=
    ValuativeRel.isEquiv _ _
  have hmem : ∀ x : u.adicCompletion F,
      x ∈ (ValuativeRel.valuation (u.adicCompletion F)).integer ↔
        x ∈ u.adicCompletionIntegers F := fun x => by
    rw [mem_adicCompletionIntegers, Valuation.mem_integer_iff]
    exact hE.le_one_iff_le_one
  let e : (ValuativeRel.valuation (u.adicCompletion F)).integer ≃+* u.adicCompletionIntegers F :=
    { toFun := fun x => ⟨x.1, (hmem x.1).1 x.2⟩
      invFun := fun x => ⟨x.1, (hmem x.1).2 x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  have hm : (maximalIdeal (ValuativeRel.valuation (u.adicCompletion F)).integer).map e =
      maximalIdeal (u.adicCompletionIntegers F) := by
    ext y
    rw [← Ideal.comap_symm, Ideal.mem_comap, mem_maximalIdeal, mem_maximalIdeal,
      mem_nonunits_iff, mem_nonunits_iff]
    exact not_congr (isUnit_map_iff e.symm y)
  rw [← hm]
  exact (IsAdicComplete.congr_ringEquiv _ e).2 inferInstance

theorem exists_sq_add_eq {O : Type} [CommRing O] [Nontrivial O] (I : Ideal O) [HenselianRing O I]
    (z : O) (hz : z ∈ I) : ∃ s : O, s ^ 2 + s = z := by
  obtain ⟨s, hs, -⟩ := HenselianRing.is_henselian (I := I) (X ^ 2 + X - C z) (by monicity!) 0
    (by simpa using hz) (by simp)
  refine ⟨s, ?_⟩
  have h2 : eval s (X ^ 2 + X - C z) = 0 := hs
  simp only [eval_sub, eval_add, eval_pow, eval_X, eval_C] at h2
  linear_combination h2

theorem isSquare_one_add_four_mul : ∀ (F : Type) [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F))
    (z : 𝓞 F), z ∈ u.asIdeal → IsSquare (algebraMap F (u.adicCompletion F) ((1 + 4 * z : 𝓞 F) : F)) := by
  intro F _ _ u z hz
  haveI := isAdicComplete_integers F u
  set z' : u.adicCompletionIntegers F := algebraMap (𝓞 F) (u.adicCompletionIntegers F) z with hz'
  have hcoe : (z' : u.adicCompletion F) = algebraMap F (u.adicCompletion F) (z : F) := by
    rw [hz', algebraMap_adicCompletionIntegers_apply]
    rfl
  have hv : Valued.v (algebraMap F (u.adicCompletion F) (z : F)) < 1 := by
    have h1 : u.valuation F (algebraMap (𝓞 F) F z) < 1 := by
      rw [valuation_of_algebraMap]
      exact (intValuation_lt_one_iff_mem (v := u) z).2 hz
    have h2 : Valued.v (((z : F) : u.adicCompletion F)) = u.valuation F (z : F) :=
      valuedAdicCompletion_eq_valuation' (v := u) (z : F)
    exact (h2.trans_lt h1 :)
  have hzm : z' ∈ maximalIdeal (u.adicCompletionIntegers F) := by
    rw [mem_maximalIdeal, mem_nonunits_iff, adicCompletionIntegers.isUnit_iff_valued_eq_one]
    rw [show (z'.1 : u.adicCompletion F) = (z' : u.adicCompletion F) from rfl, hcoe]
    exact ne_of_lt hv
  obtain ⟨s, hs⟩ := exists_sq_add_eq (maximalIdeal (u.adicCompletionIntegers F)) z' hzm
  have hsK : (s : u.adicCompletion F) ^ 2 + (s : u.adicCompletion F) =
      algebraMap F (u.adicCompletion F) (z : F) := by
    rw [← hcoe, ← hs]
    norm_cast
  have hL : algebraMap F (u.adicCompletion F) ((1 + 4 * z : 𝓞 F) : F) =
      1 + 4 * algebraMap F (u.adicCompletion F) (z : F) := by
    have e1 : ((1 + 4 * z : 𝓞 F) : F) = 1 + 4 * (z : F) := by
      rw [show (4 : 𝓞 F) = 1 + 1 + 1 + 1 by norm_num]
      push_cast
      ring
    rw [e1]
    simp only [map_add (f := _), map_one, map_mul, map_ofNat]
  refine ⟨1 + 2 * (s : u.adicCompletion F), ?_⟩
  rw [hL]
  linear_combination (-4 : u.adicCompletion F) * hsK

end GlobalTheory.HenselSquare
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsUnramifiedAtOfIsSplitAt
open NumberField IsDedekindDomain GlobalTheory.UnitaryBC

namespace GlobalTheory.SplitUnram


set_option maxHeartbeats 800000 in
theorem isUnramifiedAt_of_isSplitAt : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L]
    (w : HeightOneSpectrum (𝓞 L)), IsSplitAt w →
    Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield L)) w.asIdeal := by
  intro L _ _ _ w hw
  obtain ⟨u, hne, hu⟩ := hw
  set K := maximalRealSubfield L
  set p : Ideal (𝓞 K) := w.asIdeal.under (𝓞 K) with hpdef
  have hup : u.asIdeal.under (𝓞 K) = p := by
    have := congrArg HeightOneSpectrum.asIdeal hu
    exact this
  haveI : w.asIdeal.LiesOver p := ⟨rfl⟩
  haveI : u.asIdeal.LiesOver p := ⟨hup.symm⟩
  have hp0 : p ≠ ⊥ := (w.under (𝓞 K)).ne_bot
  haveI hpm : p.IsMaximal := (w.under (𝓞 K)).isMaximal
  have hwmem : w.asIdeal ∈ IsDedekindDomain.primesOverFinset p (𝓞 L) :=
    (IsDedekindDomain.mem_primesOverFinset_iff hp0 (𝓞 L)).2 ⟨w.isPrime, inferInstance⟩
  have humem : u.asIdeal ∈ IsDedekindDomain.primesOverFinset p (𝓞 L) :=
    (IsDedekindDomain.mem_primesOverFinset_iff hp0 (𝓞 L)).2 ⟨u.isPrime, inferInstance⟩
  have hneI : u.asIdeal ≠ w.asIdeal := fun h => hne (HeightOneSpectrum.ext h)
  have hsum := Ideal.sum_ramification_inertia (𝓞 L) K L (p := p) hp0
  rw [Algebra.IsQuadraticExtension.finrank_eq_two K L] at hsum
  have hterm : ∀ P ∈ IsDedekindDomain.primesOverFinset p (𝓞 L), 1 ≤ p.ramificationIdx' P * p.inertiaDeg' P := by
    intro P hP
    obtain ⟨hPp, hPl⟩ := (IsDedekindDomain.mem_primesOverFinset_iff hp0 (𝓞 L)).1 hP
    haveI := hPp; haveI := hPl
    have h1 : 0 < p.ramificationIdx' P := by
      rw [Ideal.ramificationIdx'_eq_ramificationIdx p P hp0]
      exact Ideal.ramificationIdx_pos (R := 𝓞 K) P
    have h2 : 0 < p.inertiaDeg' P := Ideal.inertiaDeg'_pos p P
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero h1.ne' h2.ne')
  have hpair : ({w.asIdeal, u.asIdeal} : Finset (Ideal (𝓞 L))) ⊆ IsDedekindDomain.primesOverFinset p (𝓞 L) := by
    intro P hP
    simp only [Finset.mem_insert, Finset.mem_singleton] at hP
    rcases hP with rfl | rfl
    · exact hwmem
    · exact humem
  have hle := Finset.sum_le_sum_of_subset (f := fun P => p.ramificationIdx' P * p.inertiaDeg' P) hpair
  rw [Finset.sum_pair hneI.symm, hsum] at hle
  have hu1 := hterm _ humem
  have hw1 : p.ramificationIdx' w.asIdeal * p.inertiaDeg' w.asIdeal = 1 := by
    have := hterm _ hwmem
    omega
  have he : p.ramificationIdx' w.asIdeal = 1 := Nat.eq_one_of_mul_eq_one_right hw1
  rw [Ideal.ramificationIdx'_eq_ramificationIdx p w.asIdeal hp0] at he
  exact (Algebra.isUnramifiedAt_iff_of_isDedekindDomain).2 he

end GlobalTheory.SplitUnram
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsSqrtTotallyNegative
open NumberField IsDedekindDomain GlobalTheory.UnitaryBC
open scoped ComplexConjugate

namespace GlobalTheory.CMGen

theorem exists_integer_not_mem (K : Type) [Field K] [NumberField K] [IsCMField K] :
    ∃ x : 𝓞 K, (x : K) ∉ maximalRealSubfield K := by
  by_contra h
  push_neg at h
  apply NumberField.IsCMField.complexConj_ne_one K
  ext y
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) y
  have ha : NumberField.IsCMField.complexConj K (algebraMap (𝓞 K) K a) = algebraMap (𝓞 K) K a :=
    (NumberField.IsCMField.complexConj_eq_self_iff K _).mpr (h a)
  have hb : NumberField.IsCMField.complexConj K (algebraMap (𝓞 K) K b) = algebraMap (𝓞 K) K b :=
    (NumberField.IsCMField.complexConj_eq_self_iff K _).mpr (h b)
  rw [map_div₀, ha, hb, AlgEquiv.one_apply]

theorem exists_extension (K : Type) [Field K] [NumberField K] (φ : maximalRealSubfield K →+* ℝ) :
    ∃ ψ : K →+* ℂ, ∀ x : maximalRealSubfield K,
      ψ (algebraMap (maximalRealSubfield K) K x) = (φ x : ℂ) := by
  letI : Algebra (maximalRealSubfield K) ℂ := (Complex.ofRealHom.comp φ).toAlgebra
  haveI : Algebra.IsAlgebraic (maximalRealSubfield K) K := Algebra.IsAlgebraic.tower_top (K := ℚ) _
  let f : K →ₐ[maximalRealSubfield K] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  exact ⟨f.toRingHom, fun x => f.commutes x⟩

theorem exists_sqrt_totallyNegative : ∀ (K : Type) [Field K] [NumberField K] [IsCMField K],
    ∃ (d : 𝓞 (maximalRealSubfield K)) (δ : K), δ ^ 2 = algebraMap (maximalRealSubfield K) K d ∧
      δ ∉ maximalRealSubfield K ∧
      ∀ φ : maximalRealSubfield K →+* ℝ, φ (d : maximalRealSubfield K) < 0 := by
  intro K _ _ _
  obtain ⟨x, hx⟩ := exists_integer_not_mem K
  let y : 𝓞 K := x - NumberField.IsCMField.ringOfIntegersComplexConj K x
  have hy : (y : K) = (x : K) - NumberField.IsCMField.complexConj K (x : K) := by
    simp [y, NumberField.IsCMField.coe_ringOfIntegersComplexConj]
  have hconj : NumberField.IsCMField.complexConj K (y : K) = -(y : K) := by
    rw [hy, map_sub, NumberField.IsCMField.complexConj_apply_apply, neg_sub]
  have hy0 : (y : K) ≠ 0 := by
    intro h0
    apply hx
    rw [← NumberField.IsCMField.complexConj_eq_self_iff]
    rw [hy, sub_eq_zero] at h0
    exact h0.symm
  have hsq : (y : K) ^ 2 ∈ maximalRealSubfield K := by
    rw [← NumberField.IsCMField.complexConj_eq_self_iff, map_pow, hconj, neg_sq]
  have hint : IsIntegral ℤ (⟨(y : K) ^ 2, hsq⟩ : maximalRealSubfield K) := by
    refine (isIntegral_algebraMap_iff (B := K)).mp ?_
    change IsIntegral ℤ ((y : K) ^ 2)
    exact (RingOfIntegers.isIntegral_coe y).pow 2
  refine ⟨⟨⟨(y : K) ^ 2, hsq⟩, hint⟩, (y : K), rfl, ?_, ?_⟩
  · intro hmem
    apply hy0
    have h2 := hconj
    rw [(NumberField.IsCMField.complexConj_eq_self_iff K _).mpr hmem] at h2
    have h3 : (2 : K) * (y : K) = 0 := by rw [two_mul]; nth_rewrite 1 [h2]; ring
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd h two_ne_zero
    · exact h
  · intro φ
    obtain ⟨ψ, hψ⟩ := exists_extension K φ
    have hval := hψ ⟨(y : K) ^ 2, hsq⟩
    have hψy : ψ (y : K) = ψ (x : K) - conj (ψ (x : K)) := by
      rw [hy, map_sub, NumberField.IsCMField.complexEmbedding_complexConj]
    have hne : ψ (y : K) ≠ 0 := by
      rw [map_ne_zero]; exact hy0
    have him : (ψ (x : K)).im ≠ 0 := by
      intro h0
      apply hne
      rw [hψy, Complex.sub_conj, h0]
      simp
    have key : ((φ ⟨(y : K) ^ 2, hsq⟩ : ℝ) : ℂ) = ((-(2 * (ψ (x : K)).im) ^ 2 : ℝ) : ℂ) := by
      rw [← hval]
      change ψ ((y : K) ^ 2) = _
      rw [map_pow, hψy, Complex.sub_conj]
      push_cast
      ring_nf
      rw [Complex.I_sq]
      ring
    have key' : φ ⟨(y : K) ^ 2, hsq⟩ = -(2 * (ψ (x : K)).im) ^ 2 := by exact_mod_cast key
    show φ ⟨(y : K) ^ 2, hsq⟩ < 0
    rw [key']
    have : 0 < (2 * (ψ (x : K)).im) ^ 2 := by positivity
    linarith

end GlobalTheory.CMGen
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AlgebraMapMemMaximalRealSubfieldIff
open NumberField IsDedekindDomain GlobalTheory.UnitaryBC

namespace GlobalTheory

theorem algebraMap_mem_maximalRealSubfield_iff {K L : Type} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] (x : K) :
    algebraMap K L x ∈ maximalRealSubfield L ↔ x ∈ maximalRealSubfield K := by
  simp only [mem_maximalRealSubfield_iff]
  constructor
  · intro hL ψ
    let : Algebra K ℂ := ψ.toAlgebra
    let φ : L →ₐ[K] ℂ := (by
      refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
      solve_by_elim* (maxDepth := 2) only [*,
        @_root_.DivisionSemiring.to_moduleIsTorsionFree,
        @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
    have hφ : φ (algebraMap K L x) = ψ x := φ.commutes x
    rw [← hφ]
    exact hL φ.toRingHom
  · intro hK φ
    exact hK (φ.comp (algebraMap K L))

theorem isCMField_of_sq_eq_totallyPositive :
    ∀ (K L : Type) [Field K] [NumberField K] [IsCMField K] [Field L] [NumberField L] [Algebra K L], Module.finrank K L = 2 → ∀ (d : maximalRealSubfield K) (t : L), t ^ 2 = algebraMap K L d → t ∉ Set.range (algebraMap K L) → (∀ φ : maximalRealSubfield K →+* ℝ, 0 < φ d) → IsCMField L ∧ t ∈ maximalRealSubfield L ∧ ∀ x : K, algebraMap K L x ∈ maximalRealSubfield L ↔ x ∈ maximalRealSubfield K := by
  intro K L _ _ _ _ _ _ hKL d t ht2 htK hpos
  have : Module.Finite K L := Module.finite_of_finrank_pos (by omega)
  have : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L

  have htR : t ∈ maximalRealSubfield L := by
    rw [mem_maximalRealSubfield_iff]
    intro φ
    let ρ : maximalRealSubfield K →+* ℂ :=
      (φ.comp (algebraMap K L)).comp (maximalRealSubfield K).subtype
    have hρ : ComplexEmbedding.IsReal ρ := IsTotallyReal.complexEmbedding_isReal ρ
    have hr : (0 : ℝ) < hρ.embedding d := hpos _
    have hsq : φ t * φ t = ((hρ.embedding d : ℝ) : ℂ) := by
      rw [ComplexEmbedding.IsReal.coe_embedding_apply, ← map_mul, ← pow_two, ht2]
      rfl
    have him : (φ t).im = 0 := by
      have h1 := congrArg Complex.re hsq
      have h2 := congrArg Complex.im hsq
      simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] at h1 h2
      by_contra hne
      have hre : (φ t).re = 0 := by
        have h3 : (φ t).re * (φ t).im = 0 := by linarith
        rcases mul_eq_zero.mp h3 with h | h
        · exact h
        · exact absurd h hne
      rw [hre] at h1
      nlinarith [sq_nonneg (φ t).im]
    exact Complex.conj_eq_iff_im.mpr him

  have : IsScalarTower (maximalRealSubfield K) K L := inferInstance
  have hKp : Module.finrank (maximalRealSubfield K) K = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have h4 : Module.finrank (maximalRealSubfield K) L = 4 := by
    rw [← Module.finrank_mul_finrank (maximalRealSubfield K) K L, hKp, hKL]
  have : Module.Finite (maximalRealSubfield K) L := Module.finite_of_finrank_pos (by omega)
  have hint : IsIntegral (maximalRealSubfield K) t := IsIntegral.of_finite _ t

  have hmin : (minpoly (maximalRealSubfield K) t).natDegree = 2 := by
    have hle : (minpoly (maximalRealSubfield K) t).degree ≤ ((2 : ℕ) : WithBot ℕ) := by
      have h := minpoly.degree_le_of_ne_zero (maximalRealSubfield K) t
        (Polynomial.X_pow_sub_C_ne_zero (n := 2) (by norm_num) d)
        (by rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, ht2]; exact sub_self _)
      rwa [Polynomial.degree_X_pow_sub_C (by norm_num)] at h
    have hne1 : (minpoly (maximalRealSubfield K) t).natDegree ≠ 1 := by
      rw [Ne, minpoly.natDegree_eq_one_iff]
      rintro ⟨y, hy⟩
      exact htK ⟨(y : K), hy⟩
    have hpos' := minpoly.natDegree_pos hint
    have h2 := Polynomial.natDegree_le_of_degree_le hle
    omega
  have hbase : ∀ y : maximalRealSubfield K,
      algebraMap (maximalRealSubfield K) L y ∈ maximalRealSubfield L :=
    fun y => (algebraMap_mem_maximalRealSubfield_iff (L := L) (y : K)).mpr y.2

  have hFdeg : Module.finrank (maximalRealSubfield K)
      (IntermediateField.adjoin (maximalRealSubfield K) ({t} : Set L)) = 2 := by
    rw [IntermediateField.adjoin.finrank hint, hmin]
  have hFle' : IntermediateField.adjoin (maximalRealSubfield K) ({t} : Set L) ≤
      (maximalRealSubfield L).toIntermediateField hbase :=
    IntermediateField.adjoin_simple_le_iff.mpr htR
  have hFle : ∀ y ∈ IntermediateField.adjoin (maximalRealSubfield K) ({t} : Set L),
      y ∈ maximalRealSubfield L := fun y hy => hFle' hy
  generalize IntermediateField.adjoin (maximalRealSubfield K) ({t} : Set L) = F at hFdeg hFle
  have hFL : Module.finrank F L = 2 := by
    have h := Module.finrank_mul_finrank (maximalRealSubfield K) F L
    rw [hFdeg, h4] at h
    omega
  have : Module.Finite F L := Module.finite_of_finrank_pos (by omega)
  let ι : F →+* maximalRealSubfield L :=
    { toFun := fun y => ⟨y.1, hFle y.1 y.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let : Algebra F (maximalRealSubfield L) := ι.toAlgebra
  have : IsScalarTower F (maximalRealSubfield L) L := IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.IsAlgebraic F L := Algebra.IsAlgebraic.of_finite F L
  have : Algebra.IsAlgebraic F (maximalRealSubfield L) :=
    Algebra.IsAlgebraic.tower_bot F (maximalRealSubfield L) L
  have : IsTotallyReal F := IsTotallyReal.of_algebra F (maximalRealSubfield L)
  have : Algebra.IsQuadraticExtension F L := ⟨hFL⟩
  have : IsTotallyComplex L := ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.mp fun h =>
    InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex _)
      (InfinitePlace.IsReal.comap (algebraMap K L) h)⟩
  exact ⟨IsCMField.ofCMExtension F L, htR, fun x => algebraMap_mem_maximalRealSubfield_iff x⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsConjPolynomialDefiniteUnitaryRational
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsConjPolynomialDefiniteUnitaryRational
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace GlobalTheory.UnitaryBC

private theorem polyConj_coord_pInf {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (τ : E →+* ℂ) (x : E) :
    coord τ (pInf E (algebraMap E (Ad E) x)) = τ x := by
  have h : ∀ w : InfinitePlace E, pInf E (algebraMap E (Ad E) x) w = w.embedding x := fun w => by
    first | exact pInf_algebraMap _ _ | exact pInf_algebraMap _ _ _ | simp [pInf_algebraMap]
  unfold coord
  split_ifs with hτ
  · simp only [Pi.evalRingHom_apply, h, hτ]
  · rcases InfinitePlace.embedding_mk_eq τ with h' | h'
    · exact absurd h' hτ
    · simp [h, h']

theorem exists_cEmb_entry_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {γ : UA E n}
    (hγ : γ ∈ ratU E n) {k : UA E n} (hk : cInf k = cInf γ) (i j : Fin n) :
    ∃ x : E, ∀ τ : E →+* ℂ, (cEmb τ k).val i j = τ x := by
  obtain ⟨γ₀, h₀⟩ := Subgroup.mem_subgroupOf.1 hγ
  refine ⟨γ₀.val i j, fun τ => ?_⟩
  have h1 : (cEmb τ k).val i j = coord τ ((cInf k).val i j) := rfl
  have h2 : (cInf γ).val i j = pInf E ((γ : GA E n).val i j) := rfl
  rw [h1, hk, h2, ← h₀]
  exact polyConj_coord_pInf τ _

theorem exists_conj_polyFun : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (σ : ℂ ≃+* ℂ), ∀ p ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}, ∃ p' ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}, ∀ γ ∈ ratU E n, ∀ k : infU E n, cInf k.1 = cInf γ → p' k = σ (p k) := by
  intro E _ _ _ n σ p hp
  induction hp using Algebra.adjoin_induction with
  | mem f hf =>
    obtain ⟨τ, i, j, rfl⟩ := hf
    refine ⟨_, Algebra.subset_adjoin ⟨σ.toRingHom.comp τ, i, j, rfl⟩, fun γ hγ k hk => ?_⟩
    obtain ⟨x, hx⟩ := exists_cEmb_entry_eq hγ hk i j
    simp only [hx]
    rfl
  | algebraMap c => exact ⟨_, Subalgebra.algebraMap_mem _ (σ c), fun _ _ _ _ => rfl⟩
  | add f g _ _ hf hg =>
    obtain ⟨f', hf', hf⟩ := hf
    obtain ⟨g', hg', hg⟩ := hg
    refine ⟨f' + g', add_mem hf' hg', fun γ hγ k hk => ?_⟩
    rw [Pi.add_apply, Pi.add_apply, map_add (f := _), hf γ hγ k hk, hg γ hγ k hk]
  | mul f g _ _ hf hg =>
    obtain ⟨f', hf', hf⟩ := hf
    obtain ⟨g', hg', hg⟩ := hg
    refine ⟨f' * g', mul_mem hf' hg', fun γ hγ k hk => ?_⟩
    rw [Pi.mul_apply, Pi.mul_apply, map_mul, hf γ hγ k hk, hg γ hγ k hk]

end GlobalTheory.UnitaryBC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsConjPolynomialDefiniteUnitaryRationalStatement
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conj_polynomial_definiteUnitary_rational : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (σ : ℂ ≃+* ℂ), ∀ p ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}, ∃ p' ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}, ∀ γ ∈ ratU E n, ∀ k : infU E n, cInf k.1 = cInf γ → p' k = σ (p k) := by
  first | exact @GlobalTheory.UnitaryBC.exists_conj_polyFun | exact GlobalTheory.UnitaryBC.exists_conj_polyFun | (intros; apply GlobalTheory.UnitaryBC.exists_conj_polyFun <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnramifiedAdjoinSqrtOfNotMem
open NumberField IsDedekindDomain GlobalTheory.UnitaryBC Polynomial

theorem GlobalTheory.unramified_adjoin_sqrt_of_not_mem : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (a : 𝓞 (maximalRealSubfield L)) (δ : L), δ ^ 2 = ((a : maximalRealSubfield L) : L) → δ ∉ maximalRealSubfield L → ∀ w : HeightOneSpectrum (𝓞 L), 2 * a ∉ (w.under (𝓞 (maximalRealSubfield L))).asIdeal → Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield L)) w.asIdeal := by
  intro L _ _ _ a δ hδ hδK w ha

  have hint : IsIntegral ℤ δ := by
    refine IsIntegral.of_pow two_pos ?_
    rw [hδ]
    exact (RingOfIntegers.isIntegral_coe a).algebraMap
  let d : 𝓞 L := ⟨δ, hint⟩
  have hd : algebraMap (𝓞 L) L d = δ := rfl
  have hdA : IsIntegral (𝓞 (maximalRealSubfield L)) d := Algebra.IsIntegral.isIntegral d
  have hδR : IsIntegral (maximalRealSubfield L) δ := Algebra.IsIntegral.isIntegral δ
  have hsq : d ^ 2 = algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) a := by
    apply FaithfulSMul.algebraMap_injective (𝓞 L) L
    rw [map_pow, hd, hδ, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply (𝓞 (maximalRealSubfield L)) (maximalRealSubfield L) L]
    rfl

  have hfin : Module.finrank (maximalRealSubfield L) L = 2 :=
    Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have hdegK : (minpoly (maximalRealSubfield L) δ).natDegree = 2 := by
    refine le_antisymm (hfin ▸ minpoly.natDegree_le δ) ?_
    rw [minpoly.two_le_natDegree_iff hδR]
    rintro ⟨x, hx⟩
    exact hδK (hx ▸ x.2)
  have hdeg : (minpoly (𝓞 (maximalRealSubfield L)) d).natDegree = 2 := by
    rw [← hdegK, ← hd, minpoly.isIntegrallyClosed_eq_field_fractions (maximalRealSubfield L) L hdA,
      (minpoly.monic hdA).natDegree_map]

  have hpoly : minpoly (𝓞 (maximalRealSubfield L)) d = X ^ 2 - C a := by
    have hm : (X ^ 2 - C a : (𝓞 (maximalRealSubfield L))[X]).Monic := monic_X_pow_sub_C a two_ne_zero
    have hroot : aeval d (X ^ 2 - C a) = 0 := by
      rw [map_sub, aeval_X_pow, aeval_C, hsq, sub_self]
    refine (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hdA) hm
      (minpoly.isIntegrallyClosed_dvd hdA hroot) ?_).symm
    rw [hdeg, natDegree_X_pow_sub_C _]

  have hadj : Algebra.adjoin (maximalRealSubfield L) {algebraMap (𝓞 L) L d} = ⊤ := by
    have htop : IntermediateField.adjoin (maximalRealSubfield L) {δ} = ⊤ :=
      IntermediateField.eq_of_le_of_finrank_le le_top (by
        rw [IntermediateField.finrank_top', hfin, IntermediateField.adjoin.finrank hδR, hdegK])
    rw [hd, ← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hδR.isAlgebraic, htop,
      IntermediateField.top_toSubalgebra]

  have hmem : 2 * d ∈ differentIdeal (𝓞 (maximalRealSubfield L)) (𝓞 L) := by
    have := aeval_derivative_mem_differentIdeal (𝓞 (maximalRealSubfield L)) (maximalRealSubfield L) L d hadj
    simpa [hpoly, derivative_X_pow, one_add_one_eq_two, map_ofNat] using this

  rw [← not_dvd_differentIdeal_iff]
  intro hdvd
  have h2d : 2 * d ∈ w.asIdeal := Ideal.dvd_iff_le.mp hdvd hmem
  have h4a : algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) (2 * (2 * a)) ∈ w.asIdeal := by
    have := w.asIdeal.mul_mem_left (2 * d) h2d
    convert this using 1
    rw [map_mul, map_mul, map_ofNat, ← hsq]
    ring
  have h4a' : 2 * (2 * a) ∈ (w.under (𝓞 (maximalRealSubfield L))).asIdeal := h4a
  rcases (w.under (𝓞 (maximalRealSubfield L))).isPrime.mem_or_mem h4a' with h | h
  · exact ha (Ideal.mul_mem_right a _ h)
  · exact ha h
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IntegralAdelicVectorsCharacterOrthogonality
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IntegralAdelicVectorsCharacterOrthogonality
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal Pointwise

namespace GlobalTheory.SWQ

variable {F : Type} [Field F] [NumberField F] {N : ℕ}

theorem Bd_add_left_AF (a : Fin N → F) (u v w : Fin N → AF F) :
    Bd (AF F) a (u + v) w = Bd (AF F) a u w + Bd (AF F) a v w := by
  simp only [Bd, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

theorem Bd_rat_rat (a : Fin N → F) (η ξ : Fin N → F) :
    Bd (AF F) a (rat η) (rat ξ) = algebraMap F (AF F) (Bd F a η ξ) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Bd, rat, map_sum, map_mul, Algebra.algebraMap_self, RingHom.id_apply]

theorem charOrth : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)) (a : Fin N → F), Ctx ψ lam ν a → ∀ D : Set (Fin N → AF F), IsAddFundamentalDomain (AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F)))) D (muV N ν) → muV N ν D = 1 → ∀ ξ : Fin N → F, ξ ≠ 0 → ∫ u in D, ψ (Bd (AF F) a u (rat ξ)) ∂(muV N ν) = 0 := by
  intro F _ _ N ψ lam ν a hC D hD _ ξ hξ
  haveI := hC.2.2.2.1.1
  have hmem : ∀ u : Fin N → AF F, u ∈ AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F))) →
      ∃ η, u = rat η := by
    let φ : (Fin N → F) →+ (Fin N → AF F) :=
      AddMonoidHom.mk' rat (fun x y => by funext l; simp only [rat, Pi.add_apply, map_add (f := _)])
    intro u hu
    have hle : AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F))) ≤ φ.range :=
      (AddSubgroup.closure_le _).mpr (by rintro _ ⟨η, rfl⟩; exact ⟨η, rfl⟩)
    obtain ⟨η, hη⟩ := hle hu
    exact ⟨η, hη.symm⟩
  haveI : (muV N ν).IsAddLeftInvariant := by unfold muV; infer_instance
  haveI : Countable F := Countable.of_equiv _ (Module.finBasis ℚ F).equivFun.toEquiv.symm
  haveI : Countable (AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F)))) := by
    have hs : (AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F))) :
        Set (Fin N → AF F)).Countable :=
      (Set.countable_range (rat : (Fin N → F) → (Fin N → AF F))).mono fun u hu => by
        obtain ⟨η, rfl⟩ := hmem u hu
        exact ⟨η, rfl⟩
    exact hs.to_subtype
  obtain ⟨_, ⟨_, _, hF, x, hx⟩, _, _, ha⟩ := hC
  have hadd : ∀ u v : Fin N → AF F, ψ (Bd (AF F) a (u + v) (rat ξ)) =
      ψ (Bd (AF F) a u (rat ξ)) * ψ (Bd (AF F) a v (rat ξ)) := fun u v => by
    rw [Bd_add_left_AF, AddChar.map_add_eq_mul]
  have hper : ∀ g ∈ AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F))),
      ∀ u, ψ (Bd (AF F) a (g + u) (rat ξ)) = ψ (Bd (AF F) a u (rat ξ)) := by
    intro g hg u
    obtain ⟨η, rfl⟩ := hmem g hg
    rw [hadd, Bd_rat_rat, hF, one_mul]
  obtain ⟨l, hl⟩ : ∃ l, ξ l ≠ 0 := by
    by_contra h
    push_neg at h
    exact hξ (funext h)
  have hc : (2 * a l * ξ l) ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero (ha l)) hl
  set u₀ : Fin N → AF F := Pi.single l (algebraMap F (AF F) (2 * a l * ξ l)⁻¹ * x) with hu₀def
  have hu₀ : ψ (Bd (AF F) a u₀ (rat ξ)) = ψ x := by
    congr 1
    simp only [Bd, rat]
    rw [Finset.sum_eq_single l]
    · rw [hu₀def, Pi.single_eq_same]
      have e : algebraMap F (AF F) (2 * a l) * (algebraMap F (AF F) (2 * a l * ξ l)⁻¹ * x) *
          algebraMap F (AF F) (ξ l) = algebraMap F (AF F) (2 * a l * ξ l * (2 * a l * ξ l)⁻¹) * x := by
        simp only [map_mul]; ring
      rw [e, mul_inv_cancel₀ hc, map_one, one_mul]
    · intro b _ hb
      rw [hu₀def, Pi.single_eq_of_ne hb]
      simp
    · intro h; exact absurd (Finset.mem_univ l) h
  have hD' := hD.vadd_of_comm u₀
  have h1 := hD.setIntegral_eq hD' (f := fun u => ψ (Bd (AF F) a u (rat ξ))) (fun g s => by
    show ψ (Bd (AF F) a ((g : Fin N → AF F) + s) (rat ξ)) = _
    exact hper g g.2 s)
  have h2 := (measurePreserving_add_left (muV N ν) u₀).setIntegral_image_emb
    (measurableEmbedding_addLeft u₀) (fun u => ψ (Bd (AF F) a u (rat ξ))) D
  have e : u₀ +ᵥ D = (fun s => u₀ + s) '' D := rfl
  rw [e, h2] at h1
  simp only [hadd, hu₀] at h1
  rw [integral_const_mul] at h1
  have hx1 : (1 : ℂ) - ψ x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have : ((1 : ℂ) - ψ x) * ∫ u in D, ψ (Bd (AF F) a u (rat ξ)) ∂(muV N ν) = 0 := by
    rw [sub_mul, one_mul, ← h1, sub_self]
  exact (mul_eq_zero.mp this).resolve_left hx1

end GlobalTheory.SWQ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IntegralAdelicVectorsCharacterOrthogonalityStatement
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_adelicVectors_character_orthogonality : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)) (a : Fin N → F), Ctx ψ lam ν a → ∀ D : Set (Fin N → AF F), IsAddFundamentalDomain (AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F)))) D (muV N ν) → muV N ν D = 1 → ∀ ξ : Fin N → F, ξ ≠ 0 → ∫ u in D, ψ (Bd (AF F) a u (rat ξ)) ∂(muV N ν) = 0 := by
  first | exact @GlobalTheory.SWQ.charOrth | exact GlobalTheory.SWQ.charOrth | (intros; apply GlobalTheory.SWQ.charOrth <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ComplexPadicNormKappaSplitPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ComplexPadicNormKappaSplitPrime
noncomputable section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.L2.Ker

namespace GlobalTheory.KapSplitNorm

theorem norm_le_one_of_isIntegral {q : ℕ} [Fact q.Prime] {x : ℂ_[q]} (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  have h1 : IsIntegral (NormedField.valuation (K := ℂ_[q])).integer x := hx.tower_top
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := ℂ_[q]))).mem_of_integral h1
  have h3 : ‖x‖₊ ≤ 1 := h2
  exact_mod_cast h3

theorem norm_natCast_eq_one (q : ℕ) [Fact q.Prime] (n : ℕ) (hn : ¬ q ∣ n) : ‖((n : ℕ) : ℂ_[q])‖ = 1 := by
  have e : ((n : ℕ) : ℂ_[q]) = ((algebraMap ℚ_[q] (PadicAlgCl q) (n : ℚ_[q]) : PadicAlgCl q) : ℂ_[q]) := by simp
  rw [e, PadicComplex.norm_extends']
  exact Padic.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hn)

theorem norm_iota_le_one (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (z : ℂ) (hz : IsIntegral ℤ z) : ‖ι z‖ ≤ 1 :=
  norm_le_one_of_isIntegral (by
    convert map_isIntegral_int (ι : ℂ →+* ℂ_[q]) hz using 1 <;> first | exact Subsingleton.elim _ _ | rfl)

theorem norm_iota_unit (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (n : ℕ) (hn : ¬ q ∣ n) {x w : ℂ} (hx : IsIntegral ℤ x)
    (hw : IsIntegral ℤ w) (hm : (n : ℂ) = x * w) : ‖ι x‖ = 1 := by
  have e1 := norm_iota_le_one q ι x hx
  have e2 := norm_iota_le_one q ι w hw
  have e3 : ‖ι x‖ * ‖ι w‖ = 1 := by
    rw [← norm_mul, ← map_mul, ← hm, map_natCast, norm_natCast_eq_one q n hn]
  refine le_antisymm e1 ?_
  nlinarith [norm_nonneg (ι x), norm_nonneg (ι w)]

theorem norm_rt_eq_one {D : D7} {γ₀ : IsoK D} (k : KapChoice γ₀) (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (p : ℕ)
    (hp : p.Prime) (hs : SplitK D p) (hpq : p ≠ q) : ‖ι (k.rt p)‖ = 1 := by
  have hh := k.rt_pow p hp hs
  obtain ⟨w, hw⟩ : ∃ w : 𝓞 D.host.K, w * k.pi p = (p : 𝓞 D.host.K) ^ classNumber D.host.K := by
    have hmem : (p : 𝓞 D.host.K) ^ classNumber D.host.K ∈ (k.pp p).asIdeal ^ classNumber D.host.K :=
      Ideal.pow_mem_pow (k.pp_over p hp hs) _
    rw [k.pi_gen p hp hs, Ideal.mem_span_singleton'] at hmem
    exact hmem
  have hpq' : ¬ q ∣ p ^ classNumber D.host.K := by
    intro h
    have h1 : q ∣ p := (Fact.out : q.Prime).dvd_of_dvd_pow h
    exact hpq (((Nat.prime_dvd_prime_iff_eq Fact.out hp).1 h1).symm)
  have hwK : (w : D.host.K) * (k.pi p : D.host.K) = ((p ^ classNumber D.host.K : ℕ) : D.host.K) := by
    have := congrArg (algebraMap (𝓞 D.host.K) D.host.K) hw
    simpa using this
  let fK : D.host.K →+* ℂ := D.host.φ₀.comp (algebraMap D.host.K D.host.E)
  let fK' : D.host.K →+* ℂ := D.host.φ₀.comp ((D.host.conj : D.host.E →+* D.host.E).comp (algebraMap D.host.K D.host.E))
  have hint : ∀ (g : D.host.K →+* ℂ) (x : 𝓞 D.host.K), IsIntegral ℤ (g (x : D.host.K)) := fun g x =>
    map_isIntegral_int g (NumberField.RingOfIntegers.isIntegral_coe x)
  have e : ∀ g : D.host.K →+* ℂ, ((p ^ classNumber D.host.K : ℕ) : ℂ) = g (k.pi p : D.host.K) * g (w : D.host.K) := by
    intro g
    rw [← map_natCast g, ← hwK, map_mul, mul_comm]
  have h1 : ‖ι (D.host.φ₀ (((k.pi p : 𝓞 D.host.K) : D.host.K) : D.host.E))‖ = 1 :=
    norm_iota_unit q ι _ hpq' (hint fK (k.pi p)) (hint fK w) (e fK)
  have h2 : ‖ι (D.host.φ₀ (D.host.conj (((k.pi p : 𝓞 D.host.K) : D.host.K) : D.host.E)))‖ = 1 :=
    norm_iota_unit q ι _ hpq' (hint fK' (k.pi p)) (hint fK' w) (e fK')
  have hpow : ‖ι (k.rt p)‖ ^ (2 * classNumber D.host.K) = 1 := by
    rw [← norm_pow, ← map_pow, hh, map_div₀, norm_div, h1, h2, div_one]
  have hc := NumberField.classNumber_pos D.host.K
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by omega)).1 hpow

theorem norm_kappa_split : ∀ (D : D7) (γ₀ : IsoK D) (k : KapChoice γ₀) (q : ℕ) [Fact q.Prime], SplitK D q →
    ∀ ι : ℂ ≃+* ℂ_[q], ‖ι k.kappa‖ = ‖ι (k.rt q)‖ ^ (-(k.yP q)) := by
  intro D γ₀ k q _ hsq ι
  have hfin := yFinite D γ₀ k
  have hfinS : (Function.mulSupport
      (fun p : {p : ℕ // p.Prime ∧ SplitK D p} => k.rt p ^ (-(k.yP p)))).Finite := by
    refine (hfin.preimage Subtype.val_injective.injOn).subset ?_
    intro p hp
    refine ⟨p.2.1, p.2.2, ?_⟩
    intro h0
    apply hp
    simp [h0]
  let F : ℂ →* ℝ :=
    { toFun := fun z => ‖ι z‖
      map_one' := by simp
      map_mul' := fun x y => by simp [norm_mul] }
  have hF : ∀ z, F z = ‖ι z‖ := fun _ => rfl
  rw [KapChoice.kappa, ← hF, MonoidHom.map_finprod F hfinS,
    finprod_eq_single _ (⟨q, Fact.out, hsq⟩ : {p : ℕ // p.Prime ∧ SplitK D p})]
  · rw [hF, map_zpow₀, norm_zpow]
  · intro p hp
    have hpq : (p : ℕ) ≠ q := fun h => hp (Subtype.ext h)
    rw [hF, map_zpow₀, norm_zpow, norm_rt_eq_one k q ι p p.2.1 p.2.2 hpq, one_zpow]

end GlobalTheory.KapSplitNorm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ComplexPadicNormKappaSplitPrimeStatement
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.L2.Ker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexPadic_norm_kappa_splitPrime : ∀ (D : D7) (γ₀ : IsoK D) (k : KapChoice γ₀) (q : ℕ) [Fact q.Prime], SplitK D q → ∀ ι : ℂ ≃+* ℂ_[q], ‖ι k.kappa‖ = ‖ι (k.rt q)‖ ^ (-(k.yP q)) := by
  first | exact @GlobalTheory.KapSplitNorm.norm_kappa_split | exact GlobalTheory.KapSplitNorm.norm_kappa_split | (intros; apply GlobalTheory.KapSplitNorm.norm_kappa_split <;> assumption)
end
end
