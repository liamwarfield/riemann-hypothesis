module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorFixesCosetVector
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilFixesCosetVectorCongruentOneModIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.UnitaryGroupSecondCountableT2
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddCharHalfTraceTensorLatticeHeisenbergCocycle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixMulVecBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormBlockEmbLeftInvariant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryHeckeCharacterPhaseTypeCm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryHeckeCharacterExtendingBaseCharacteStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentCoprimeAtGoodPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableAtZeroHeisenbergCMRealLineTheta

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualSkewIdealLatticeIsSelfDual
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualSkewIdealLatticeIsSelfDual
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField Polynomial
open scoped Pointwise nonZeroDivisors
open Formalism.L2.Host (HChar embTau)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FunObj GlobalTheory.FunObj.SqNum

noncomputable section

namespace GlobalTheory.SkewLatSD

variable (D : D7)

theorem star_eq_conj' (x : D.host.E) : (letI := D.host.cmStar; star x) = D.host.conj x := by
  have := D.host.isCMField_hostE
  exact D.host.φ₀.injective ((NumberField.IsCMField.complexEmbedding_complexConj _ D.host.φ₀ x).trans
    (D.host.conjE_apply D.host.φ₀ x).symm)

theorem conj_conj' (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  letI := D.host.cmStar
  rw [← star_eq_conj', ← star_eq_conj', star_star]

theorem conj_mul_conj : D.host.conj * D.host.conj = 1 :=
  AlgEquiv.ext fun x => conj_conj' D x

theorem conj_smul_conj_smul (I : Ideal (𝓞 D.host.E)) : D.host.conj • D.host.conj • I = I := by
  rw [smul_smul, conj_mul_conj, one_smul]

variable {D}

theorem smul_ne_bot (g : Gal(D.host.E/ℚ)) {I : Ideal (𝓞 D.host.E)} (h : I ≠ ⊥) : g • I ≠ ⊥ := by
  obtain ⟨j, hj, hj0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  intro e
  have := Ideal.smul_mem_pointwise_smul g j I hj
  rw [e, Ideal.mem_bot, smul_eq_zero_iff_eq] at this
  exact hj0 this

theorem coe_ne_zero {I : Ideal (𝓞 D.host.E)} (h : I ≠ ⊥) : (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
  rwa [Ne, FractionalIdeal.coeIdeal_eq_zero]

theorem map_mem_div (g : Gal(D.host.E/ℚ)) {I J : Ideal (𝓞 D.host.E)} (hJ : J ≠ ⊥) {x : D.host.E}
    (hx : x ∈ (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) / (J : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)) : g x ∈ ((g • I : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) / ((g • J : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
  rw [FractionalIdeal.mem_div_iff_of_ne_zero (coe_ne_zero hJ)] at hx
  rw [FractionalIdeal.mem_div_iff_of_ne_zero (coe_ne_zero (smul_ne_bot g hJ))]
  intro c hc
  obtain ⟨c', hc', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hc
  have h1 : g⁻¹ • c' ∈ J := Ideal.mem_pointwise_smul_iff_inv_smul_mem.1 hc'
  obtain ⟨i, hi, e⟩ := (FractionalIdeal.mem_coeIdeal _).1 (hx _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨_, h1, rfl⟩))
  refine (FractionalIdeal.mem_coeIdeal _).2 ⟨g • i, Ideal.smul_mem_pointwise_smul g i I hi, ?_⟩
  have e' : ((i : 𝓞 D.host.E) : D.host.E) = x * ((g⁻¹ • c' : 𝓞 D.host.E) : D.host.E) := e
  show ((g • i : 𝓞 D.host.E) : D.host.E) = g x * (c' : D.host.E)
  have e2 : ((g • i : 𝓞 D.host.E) : D.host.E) = g (i : D.host.E) := rfl
  have e3 : ((g⁻¹ • c' : 𝓞 D.host.E) : D.host.E) = g⁻¹ (c' : D.host.E) := rfl
  rw [e2, e', e3, map_mul, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

end GlobalTheory.SkewLatSD

namespace GlobalTheory.SkewLatSD

variable {D : D7}

theorem mem_skewLat_iff {𝔪 : Ideal (𝓞 D.host.E)} {N : ℕ} (y : Fin N → D.host.E) :
    y ∈ GlobalTheory.FunObj.SqNum.skewLat D 𝔪 N ↔ ∀ i, y i ∈ (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) / ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
  simp only [GlobalTheory.FunObj.SqNum.skewLat, Submodule.mem_pi, Set.mem_univ, true_implies]
  rfl

theorem skewLat_sd : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (N : ℕ), 𝔪 ≠ ⊥ → SD D (GlobalTheory.FunObj.SqNum.skewLat D 𝔪 N) := by
  intro D 𝔪 N h𝔪
  letI := D.host.cmStar
  set σ := D.host.conj
  set 𝔫 : Ideal (𝓞 D.host.E) := σ • 𝔪 with h𝔫
  have h𝔫0 : 𝔫 ≠ ⊥ := smul_ne_bot σ h𝔪
  have hA0 : (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) / (𝔫 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := div_ne_zero (coe_ne_zero h𝔪) (coe_ne_zero h𝔫0)
  have hB0 : (𝔫 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) / (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := div_ne_zero (coe_ne_zero h𝔫0) (coe_ne_zero h𝔪)
  have hBA : (𝔫 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) / (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) * ((𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) / (𝔫 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)) = 1 := by
    rw [div_mul_div_comm, mul_comm (𝔫 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E), div_self (mul_ne_zero (coe_ne_zero h𝔪) (coe_ne_zero h𝔫0))]
  have hσ𝔫 : σ • 𝔫 = 𝔪 := conj_smul_conj_smul D 𝔪

  have toB : ∀ x ∈ (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) / (𝔫 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E), σ x ∈ (𝔫 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) / (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := fun x hx => by
    simpa only [← h𝔫, hσ𝔫] using (map_mem_div σ h𝔫0 hx)
  have toA : ∀ x ∈ (𝔫 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) / (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E), σ x ∈ (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) / (𝔫 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := fun x hx => by
    simpa only [← h𝔫, hσ𝔫] using (map_mem_div σ h𝔪 hx)
  have hmem := fun y => mem_skewLat_iff (D := D) (𝔪 := 𝔪) (N := N) y
  refine ⟨?_, ?_, ?_⟩
  · unfold GlobalTheory.FunObj.SqNum.skewLat
    rw [← Submodule.iSup_map_single]
    exact Submodule.fg_iSup _ fun i => (FractionalIdeal.fg_of_isNoetherianRing le_rfl _).map _
  · obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (show (((𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) / (𝔫 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Submodule (𝓞 D.host.E) D.host.E) ≠ ⊥ from fun e =>
        hA0 (FractionalIdeal.coeToSubmodule_injective (e.trans FractionalIdeal.coe_zero.symm)))
    have hs : ∀ i, (Pi.single i a : Fin N → D.host.E) ∈ GlobalTheory.FunObj.SqNum.skewLat D 𝔪 N := fun i => by
      rw [hmem]
      intro j
      by_cases hj : j = i
      · subst hj; simpa using ha
      · rw [Pi.single_eq_of_ne hj]; exact FractionalIdeal.zero_mem _
    rw [Submodule.eq_top_iff']
    intro v
    have hv : v = ∑ i, (v i * a⁻¹) • (Pi.single i a : Fin N → D.host.E) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply, ha0]
    rw [hv]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (hs i))
  · intro y
    constructor
    · intro hy x hx
      rw [hmem] at hx hy
      unfold Formalism.BasicNotions.stdH
      refine Subring.sum_mem _ fun i _ => ?_
      rw [star_eq_conj']
      have := FractionalIdeal.mul_mem_mul (toB _ (hx i)) (hy i)
      rw [hBA, FractionalIdeal.mem_one_iff] at this
      obtain ⟨r, hr⟩ := this
      exact ⟨r, hr⟩
    · intro h
      rw [hmem]
      intro i
      rw [← one_div_div, FractionalIdeal.mem_div_iff_of_ne_zero hB0]
      intro b hb
      have ha := toA b hb
      have hx : (Pi.single i (σ b) : Fin N → D.host.E) ∈ GlobalTheory.FunObj.SqNum.skewLat D 𝔪 N := by
        rw [hmem]
        intro j
        by_cases hj : j = i
        · subst hj; simpa using ha
        · rw [Pi.single_eq_of_ne hj]; exact FractionalIdeal.zero_mem _
      have := h _ hx
      unfold Formalism.BasicNotions.stdH at this
      rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj])
        (fun hi => absurd (Finset.mem_univ i) hi)] at this
      rw [Pi.single_eq_same, star_eq_conj', conj_conj'] at this
      obtain ⟨r, hr⟩ := this
      rw [FractionalIdeal.mem_one_iff]
      exact ⟨r, by rw [hr, mul_comm]⟩

end GlobalTheory.SkewLatSD
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualSkewIdealLatticeIsSelfDualStatement
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField Polynomial
open scoped Pointwise nonZeroDivisors
open Formalism.L2.Host (HChar embTau)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDualSkewIdealLattice_isSelfDual : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (N : ℕ), 𝔪 ≠ ⊥ → SD D (GlobalTheory.FunObj.SqNum.skewLat D 𝔪 N) := by
  first | exact @GlobalTheory.SkewLatSD.skewLat_sd | exact GlobalTheory.SkewLatSD.skewLat_sd | (intros; apply GlobalTheory.SkewLatSD.skewLat_sd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPeriodicMeasurableSchwartzBoundStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPeriodicMeasurableSchwartzBound
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open IsDedekindDomain NumberField MeasureTheory
open GlobalTheory.WeilM GlobalTheory.AdelicU
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical Topology ContDiff

noncomputable section

namespace GlobalTheory.Cofactor

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

private theorem cont_toMixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  change Continuous fun x : InfiniteAdeleRing F =>
    ((fun (v : {w : InfinitePlace F // w.IsReal}) => InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
     (fun (v : {w : InfinitePlace F // w.IsComplex}) => InfinitePlace.Completion.extensionEmbedding v.1 (x v)))
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)

private theorem cont_ofMixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
  refine continuous_pi fun v => ?_
  rcases v.isReal_or_isComplex with hv | hv
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_fst).congr fun y =>
      (congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_snd).congr fun y =>
      (congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm

theorem continuous_pureA {f : (κ → mixedEmbedding.mixedSpace F) → ℂ} {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hf : Continuous f) (hg : Continuous g) : Continuous (pureA F f g) :=
  (hf.comp (continuous_pi fun i => cont_toMixed.comp (continuous_fst.comp (continuous_apply i)))).mul
    (hg.comp (continuous_pi fun i => continuous_snd.comp (continuous_apply i)))

theorem hasCompactSupport_pureA {f : (κ → mixedEmbedding.mixedSpace F) → ℂ} {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hf : HasCompactSupport f) (hg : HasCompactSupport g) : HasCompactSupport (pureA F f g) := by
  let H : (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F) → (κ → AdeleRing (𝓞 F) F) :=
    fun p i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 i), p.2 i)
  have hH : Continuous H := continuous_pi fun i =>
    (cont_ofMixed.comp ((continuous_apply i).comp continuous_fst)).prodMk ((continuous_apply i).comp continuous_snd)
  refine HasCompactSupport.intro ((hf.isCompact.prod hg.isCompact).image hH) fun x hx => ?_
  by_contra h
  apply hx
  refine ⟨(fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1, fun i => (x i).2),
    ⟨subset_tsupport _ (left_ne_zero_of_mul h), subset_tsupport _ (right_ne_zero_of_mul h)⟩, ?_⟩
  funext i
  exact Prod.ext ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm_apply_apply _) rfl


variable (F κ) in
theorem exists_bump : ∃ f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ, HasCompactSupport f ∧ f 0 = 1 := by
  let b : ContDiffBump (0 : κ → mixedEmbedding.mixedSpace F) := ⟨1, 2, one_pos, one_lt_two⟩
  have h1 : HasCompactSupport fun x => (b x : ℂ) :=
    b.hasCompactSupport.comp_left (g := fun t : ℝ => (t : ℂ)) Complex.ofReal_zero
  have h2 : ContDiff ℝ ∞ fun x => (b x : ℂ) := Complex.ofRealCLM.contDiff.comp b.contDiff
  refine ⟨h1.toSchwartzMap h2, h1, ?_⟩
  show (b 0 : ℂ) = 1
  rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one), Complex.ofReal_one]


variable (κ) in
def intPts (κ : Type)
    (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) :
    Set (κ → Fv F v) := {x | ∀ i, x i ∈ v.adicCompletionIntegers F}

theorem intPts_eq (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) :
    intPts κ v = Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (Fv F v)) := by
  ext x; simp [intPts]

theorem isCompact_intPts (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) : IsCompact (intPts κ v) := by
  rw [intPts_eq]
  exact isCompact_univ_pi fun _ => ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v

theorem isOpen_intPts (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) : IsOpen (intPts κ v) := by
  rw [intPts_eq]
  exact isOpen_set_pi Set.finite_univ fun _ _ => Valued.isOpen_valuationSubring _

theorem indicator_mem_SB {X : Type} [TopologicalSpace X] [T2Space X] {U : Set X} (hc : IsCompact U) (ho : IsOpen U) :
    U.indicator (1 : X → ℂ) ∈ GlobalTheory.WeilM.SB X := by
  refine ⟨?_, HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _⟩
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ U
  · filter_upwards [ho.mem_nhds hx] with y hy
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy]; rfl
  · filter_upwards [hc.isClosed.isOpen_compl.mem_nhds hx] with y hy
    rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hy]

theorem exists_cofactor : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)),
    ∃ (r : (κ → AF F) → ℂ) (K : Set (κ → Fv F v)), @Measurable _ _ (borel _) _ r ∧
      (∀ x z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z → r (x + z) = r x) ∧
      (∀ φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ r ∈ GlobalTheory.WeilM.schA F κ) ∧
      IsCompact K ∧ (interior K).Nonempty ∧
      ∀ μA : @MeasureTheory.Measure (κ → AF F) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μA →
        ∫⁻ x, K.indicator 1 (fun i => evFin F v (x i)) * ‖r x‖ₑ ^ 2 ∂μA ≠ 0 ∧
        ∫⁻ x, K.indicator 1 (fun i => evFin F v (x i)) * ‖r x‖ₑ ^ 2 ∂μA ≠ ⊤ := by
  intro F _ _ κ _ v
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  obtain ⟨f, hfc, hf0⟩ := exists_bump F κ
  let φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F w) → ℂ := fun w => (intPts κ w).indicator 1
  have hφ : ∀ w, φ w ∈ GlobalTheory.WeilM.SB _ := fun w => indicator_mem_SB (isCompact_intPts w) (isOpen_intPts w)
  have hstd : ∀ᶠ w in Filter.cofinite, φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 :=
    Filter.Eventually.of_forall fun _ => rfl
  obtain ⟨r, hr, hrt⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φ hstd
  have key : ∀ ψ ∈ GlobalTheory.WeilM.SB (κ → Fv F v), ∃ g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) ψ r = pureA F f g := by
    intro ψ hψ
    have h1 : ∀ w, Function.update φ v ψ w ∈ GlobalTheory.WeilM.SB _ := fun w => by
      by_cases hw : w = v
      · subst hw; rw [Function.update_self]; exact hψ
      · rw [Function.update_of_ne hw]; exact hφ w
    have h2 := GlobalTheory.PureFactor.update_eventually φ v ψ hstd
    exact ⟨_, ⟨isLocallyConstant_finprod_evalV _ h1 h2, GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod _ h1 h2⟩,
      hrt ψ⟩
  have hev : Continuous fun x : κ → AF F => fun i => evFin F v (x i) :=
    continuous_pi fun i => (RestrictedProduct.continuous_eval v).comp (continuous_snd.comp (continuous_apply i))
  have h0 : (0 : κ → Fv F v) ∈ intPts κ v := fun _ => zero_mem _
  have hrc : Continuous r := by
    rw [continuous_iff_continuousAt]
    intro x
    let y : κ → Fv F v := fun i => evFin F v (x i)
    let U : Set (κ → Fv F v) := Homeomorph.addRight y '' intPts κ v
    have hUo : IsOpen U := (Homeomorph.addRight y).isOpenMap _ (isOpen_intPts v)
    have hUc : IsCompact U := (isCompact_intPts v).image (Homeomorph.addRight y).continuous
    have hy : y ∈ U := ⟨0, h0, by simp⟩
    obtain ⟨g, hg, e⟩ := key _ (indicator_mem_SB hUc hUo)
    refine (continuous_pureA f.continuous hg.1.continuous).continuousAt.congr ?_
    filter_upwards [hev.continuousAt.preimage_mem_nhds (hUo.mem_nhds hy)] with z hz
    rw [← e]
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens
    rw [Set.indicator_of_mem (show (fun i => evFin F v (z i)) ∈ U from hz), Pi.one_apply, one_mul]
  refine ⟨r, intPts κ v, hrc.measurable, hr, fun ψ hψ => ?_, isCompact_intPts v,
    ⟨0, by rw [(isOpen_intPts v).interior_eq]; exact h0⟩, fun μ hμ => ?_⟩
  · obtain ⟨g, hg, e⟩ := key ψ hψ
    exact Submodule.subset_span ⟨f, g, hg, e⟩
  obtain ⟨g, hg, e⟩ := key _ (hφ v)
  set P := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) (φ v) r with hP
  have hPc : Continuous P := e ▸ continuous_pureA f.continuous hg.1.continuous
  have hPs : HasCompactSupport P := e ▸ hasCompactSupport_pureA hfc hg.2
  have hP0 : P 0 = 1 := by
    rw [hP, hrt (φ v), Function.update_eq_self]
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure
    have a1 : (fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F ((0 : κ → AF F) i)) = 0 := by
      funext i
      exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
    rw [a1, hf0, one_mul]
    refine finprod_eq_one_of_forall_eq_one fun w => ?_
    have : (fun i => evFin F w ((0 : κ → AF F) i)) ∈ intPts κ w := by
      intro i
      show evFin F w 0 ∈ _
      rw [map_zero]; exact zero_mem _
    exact Set.indicator_of_mem this _
  have hI : (fun x : κ → AF F => (intPts κ v).indicator 1 (fun i => evFin F v (x i)) * ‖r x‖ₑ ^ 2) =
      fun x => ‖(P * P) x‖ₑ := by
    funext x
    simp only [hP, Pi.mul_apply, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, φ]
    by_cases hx : (fun i => evFin F v (x i)) ∈ intPts κ v
    · simp [Set.indicator_of_mem hx, sq]
    · simp [Set.indicator_of_notMem hx]
  rw [hI]
  have hPP : Continuous (P * P) := hPc.mul hPc
  refine ⟨fun h => ?_, (hPP.integrable_of_hasCompactSupport hPs.mul_left).2.ne⟩
  rw [lintegral_eq_zero_iff hPP.measurable.enorm] at h
  have h3 : (P * P) =ᵐ[μ] 0 := h.mono fun x hx => by simpa using hx
  have h4 := congrFun ((hPP.ae_eq_iff_eq μ continuous_zero).1 h3) 0
  simp [hP0] at h4

end GlobalTheory.Cofactor

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_periodic_measurable_schwartz_bound : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)),
    ∃ (r : (κ → AF F) → ℂ) (K : Set (κ → Fv F v)), @Measurable _ _ (borel _) _ r ∧
      (∀ x z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z → r (x + z) = r x) ∧
      (∀ φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ r ∈ GlobalTheory.WeilM.schA F κ) ∧
      IsCompact K ∧ (interior K).Nonempty ∧
      ∀ μA : @MeasureTheory.Measure (κ → AF F) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μA →
        ∫⁻ x, K.indicator 1 (fun i => evFin F v (x i)) * ‖r x‖ₑ ^ 2 ∂μA ≠ 0 ∧
        ∫⁻ x, K.indicator 1 (fun i => evFin F v (x i)) * ‖r x‖ₑ ^ 2 ∂μA ≠ ⊤ := by
  first | exact @GlobalTheory.Cofactor.exists_cofactor | exact GlobalTheory.Cofactor.exists_cofactor | (intros; apply GlobalTheory.Cofactor.exists_cofactor <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilActionCosetVectorFixedPrincipalCongruence
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilActionCosetVectorFixedPrincipalCongruence
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

open GlobalTheory.FunObj.StdDatum

namespace GlobalTheory.BotPairSmall.CvFix

theorem om_cvec_of_congOne : ∀ (D : D7) (δ t0 : ℂ) (hc : Crv D ⊤ δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0) (a d : ℕ) (hd : Even d) (e0 : VC D a d → ℂ) (hv : oddE0 D ⊤ δ t0 a d e0) (W : WeilO D ⊤ δ a d e0) (hep : W.ep = 1) (hep' : W.ep' = 1) (𝔪 : Ideal (𝓞 D.host.E)) (hm : 𝔪 ≠ ⊥) (hcop : 𝔪 ⊔ D.host.conj • 𝔪 = ⊤) (hcond : ∀ u : (AE D)ˣ, IntU D u → (u : AE D) - 1 ∈ hatId D (𝔪 * D.host.conj • 𝔪) → W.chV'.f u = 1) (o : ℕ) (ho : o + a = d), ∀ k ∈ intG D a, CongOne D (D.host.conj • 𝔪) k → W.Om k 1 (GlobalTheory.BotPairSmall.cvec D δ (D.host.conj • 𝔪) o a d e0) = GlobalTheory.BotPairSmall.cvec D δ (D.host.conj • 𝔪) o a d e0 := by
  intro D δ t0 hc ht a d hd e0 hv W hep hep' 𝔪 hm hcop hcond o ho k hk hkc
  have hcc : D.host.conj • D.host.conj • 𝔪 = 𝔪 := by
    rw [smul_smul, GlobalTheory.GaloisTwist.conj_mul_conj, one_smul]
  have h := GlobalTheory.T.weil_fixes_cosetVector_congruent_one_mod_ideal D δ t0 hc e0 hv W (D.host.conj • 𝔪) (GlobalTheory.BotPairSmall.conj_smul_ne_bot D hm) ?_ ?_ o (by omega) k hk hkc
  · exact h
  · rw [hcc, Ideal.isCoprime_iff_sup_eq, sup_comm]; exact hcop
  · intro u hu hu1
    apply hcond u hu
    rwa [hcc, mul_comm] at hu1

end GlobalTheory.BotPairSmall.CvFix
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilActionCosetVectorFixedPrincipalCongruenceStatement
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilAction_cosetVector_fixed_principalCongruence : ∀ (D : D7) (δ t0 : ℂ) (hc : Crv D ⊤ δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0) (a d : ℕ) (hd : Even d) (e0 : VC D a d → ℂ) (hv : oddE0 D ⊤ δ t0 a d e0) (W : WeilO D ⊤ δ a d e0) (hep : W.ep = 1) (hep' : W.ep' = 1) (𝔪 : Ideal (𝓞 D.host.E)) (hm : 𝔪 ≠ ⊥) (hcop : 𝔪 ⊔ D.host.conj • 𝔪 = ⊤) (hcond : ∀ u : (AE D)ˣ, IntU D u → (u : AE D) - 1 ∈ hatId D (𝔪 * D.host.conj • 𝔪) → W.chV'.f u = 1) (o : ℕ) (ho : o + a = d), ∀ k ∈ intG D a, CongOne D (D.host.conj • 𝔪) k → W.Om k 1 (GlobalTheory.BotPairSmall.cvec D δ (D.host.conj • 𝔪) o a d e0) = GlobalTheory.BotPairSmall.cvec D δ (D.host.conj • 𝔪) o a d e0 := by
  first | exact @GlobalTheory.BotPairSmall.CvFix.om_cvec_of_congOne | exact GlobalTheory.BotPairSmall.CvFix.om_cvec_of_congOne | (intros; apply GlobalTheory.BotPairSmall.CvFix.om_cvec_of_congOne <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanTraceSymplecticOrthonormalFrames
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanTraceSymplecticOrthonormalFrames
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

noncomputable section

namespace GlobalTheory.SympFramesD

theorem symp_framesD : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {α β : Type}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {P Q R S : InfinitePlace F → ℕ} (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ), IsCMExt F E σ → FramedD τ JA JB a b A C →
    ∀ (u u' : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (c c' : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ), At (evI F) u → At (evI F) u' →
    (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) → (∀ w, u'.map (piInf (τ w)) = A w * c' w * (C w)ᵀ) →
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (symp (R := AF F) (cA σ) (-1) JA JB u u')) =
      -2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im := by
  intro F E _ _ _ _ _ σ α β _ _ _ _ P Q R S τ JA JB a b A C hCM hF u u' c c' _ _ hu hu'
  have key : ∀ w, a * b * piInf (τ w) (hTens (cA σ) JA JB u u') =
      ∑ x, ∑ y, lineSign x y * c w x y * star (c' w x y) := by
    intro w
    have e : piInf (τ w) (hTens (cA σ) JA JB u u') = ∑ i, ∑ j, ∑ k, ∑ l, u.map (piInf (τ w)) i j *
        JA.map (piInf (τ w)) i k * JB.map (piInf (τ w)) j l * star (u'.map (piInf (τ w)) k l) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hTens, map_sum, map_mul, GlobalTheory.WrongSignPair.piInf_cA hCM, Matrix.map_apply]
    rw [e, hu w, hu' w, GlobalTheory.SympFrames.quad_eq_trace]
    exact GlobalTheory.SympFrames.frame_trace _ _ a b (A w) (C w) (hF.2.1 w).1 (hF.2.2 w).1 (c w) (c' w)
  rw [symp, GlobalTheory.WrongSignPair.trace_evI_trace hCM τ, Complex.im_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have h2 := key w
  rw [hF.1] at h2
  rw [← h2, map_mul, map_neg, map_one]
  simp only [Complex.neg_re, Complex.mul_im, Complex.I_re, Complex.I_im, neg_one_mul, zero_mul, one_mul, zero_add]
  ring

end GlobalTheory.SympFramesD
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanTraceSymplecticOrthonormalFramesStatement
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_trace_symplectic_orthonormal_frames : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {α β : Type}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {P Q R S : InfinitePlace F → ℕ} (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ), IsCMExt F E σ → FramedD τ JA JB a b A C →
    ∀ (u u' : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (c c' : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ), At (evI F) u → At (evI F) u' →
    (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) → (∀ w, u'.map (piInf (τ w)) = A w * c' w * (C w)ᵀ) →
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (symp (R := AF F) (cA σ) (-1) JA JB u u')) =
      -2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im := by
  first | exact @GlobalTheory.SympFramesD.symp_framesD | exact GlobalTheory.SympFramesD.symp_framesD | (intros; apply GlobalTheory.SympFramesD.symp_framesD <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetIntegralConjugateScaledUnitaryGroupEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetIntegralConjugateScaledUnitaryGroupEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ConjUIntegral

theorem setIntegral_conjU_eq : ∀ {D : D7} (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E), c ≠ 0 →
    ∀ (h : J = c • V.gram) (ν : Measure (GA D V)) (fd : Set (GA D V)), ν.IsHaarMeasure → IsFundamentalDomain (GQ V) fd ν →
    ∀ dom : Set (UB J), IsFundamentalDomain (ratU D.sp.cm.sig J) dom (ν.map (conjU V c h)) →
    ∀ f : UB J → ℂ, (∀ γ ∈ ratU D.sp.cm.sig J, ∀ x, f (γ * x) = f x) →
      ∫ u in fd, f (conjU V c h u) ∂ν = ∫ x in dom, f x ∂(ν.map (conjU V c h)) := by
  intro D V J c hc h ν fd hν hfd dom hdom f hf
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  have : IsTopologicalRing (AE D) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing
  have : BorelSpace (UB J) := ⟨rfl⟩
  let φ := GlobalTheory.ConjUTransport.conjEquiv V c hc h
  have c1 : Continuous φ := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.continuous_conjU V c h
  have c2 : Continuous φ.symm := GlobalTheory.ConjUTransport.continuous_conjUInv V c hc h
  let H : GA D V ≃ₜ UB J := ⟨φ.toEquiv, c1, c2⟩
  have hme : MeasurableEmbedding (conjU V c h) := H.measurableEmbedding
  obtain ⟨hH, hfd'⟩ := GlobalTheory.ConjUTransport.map_isHaar_isFundamentalDomain V c hc h ν fd hν hfd
  have e1 : ∫ x in conjU V c h '' fd, f x ∂(ν.map (conjU V c h)) = ∫ u in fd, f (conjU V c h u) ∂ν := by
    rw [hme.setIntegral_map, Set.preimage_image_eq _ hme.injective]
  rw [← e1]
  haveI := GlobalTheory.UnitaryVol.countable_ratU D.sp.cm.sig J
  haveI := hH
  haveI : SMulInvariantMeasure (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ratU D.sp.cm.sig J) (UB J) (ν.map (conjU V c h)) :=
    ⟨fun γ A _ => measure_preimage_mul (ν.map (conjU V c h)) γ.1 A⟩
  exact hfd'.setIntegral_eq hdom fun γ x => hf γ.1 γ.2 x

end GlobalTheory.ConjUIntegral
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetIntegralConjugateScaledUnitaryGroupEqStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.setIntegral_conjugate_scaled_unitaryGroup_eq : ∀ {D : D7} (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E), c ≠ 0 →
    ∀ (h : J = c • V.gram) (ν : Measure (GA D V)) (fd : Set (GA D V)), ν.IsHaarMeasure → IsFundamentalDomain (GQ V) fd ν →
    ∀ dom : Set (UB J), IsFundamentalDomain (ratU D.sp.cm.sig J) dom (ν.map (conjU V c h)) →
    ∀ f : UB J → ℂ, (∀ γ ∈ ratU D.sp.cm.sig J, ∀ x, f (γ * x) = f x) →
      ∫ u in fd, f (conjU V c h u) ∂ν = ∫ x in dom, f x ∂(ν.map (conjU V c h)) := by
  first | exact @GlobalTheory.ConjUIntegral.setIntegral_conjU_eq | exact GlobalTheory.ConjUIntegral.setIntegral_conjU_eq | (intros; apply GlobalTheory.ConjUIntegral.setIntegral_conjU_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationL2Isometry
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationL2Isometry
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.WeilL2Isometry

open MeasureTheory GlobalTheory.WeilAdm.HaarSplit
open scoped ENNReal Classical

theorem l2A_eq_of_isUnitaryOn : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] {G : Type} [Group G]
    (om : G →* Module.End ℂ ((κ → AF F) → ℂ)), (∀ p, ∀ φ ∈ schA F κ, om p φ ∈ schA F κ) → IsUnitaryOn (adeleClass F) om →
    ∃ μ : @MeasureTheory.Measure (κ → FiniteAdeleRing (𝓞 F) F) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ ∧
      ∀ p, ∀ Φ ∈ schA F κ, GlobalTheory.WeilL2Words.l2A F μ (om p Φ) = GlobalTheory.WeilL2Words.l2A F μ Φ := by
  intro F _ _ κ _ G _ om hpres hU
  haveI := volume_isAddHaar F κ
  haveI : LocallyCompactSpace (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI : SecondCountableTopology (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI : T2Space (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  letI mY : MeasurableSpace (κ → FiniteAdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (κ → FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  letI mA : MeasurableSpace (κ → AdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (κ → AdeleRing (𝓞 F) F) := ⟨rfl⟩
  haveI : SigmaCompactSpace (κ → FiniteAdeleRing (𝓞 F) F) := sigmaCompactSpace_of_locallyCompact_secondCountable
  set ν : Measure (κ → FiniteAdeleRing (𝓞 F) F) := Measure.addHaar with hν
  haveI : SFinite ν := inferInstance
  haveI : MeasurableAdd (κ → mixedEmbedding.mixedSpace F) := ContinuousAdd.measurableAdd
  haveI : MeasurableAdd (κ → FiniteAdeleRing (𝓞 F) F) := ContinuousAdd.measurableAdd
  haveI hνH : ν.IsAddHaarMeasure := by rw [hν]; infer_instance
  haveI : ((MeasureTheory.MeasureSpace.volume : Measure (κ → mixedEmbedding.mixedSpace F)).prod ν).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  have hμH : Measure.IsAddHaarMeasure (((MeasureTheory.MeasureSpace.volume : Measure (κ → mixedEmbedding.mixedSpace F)).prod ν).map (splitE F κ)) :=
    (splitE F κ).isAddHaarMeasure_map _ (continuous_splitE F κ) (continuous_splitE_symm F κ)
  let em : ((κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F)) ≃ᵐ (κ → AdeleRing (𝓞 F) F) :=
    (Homeomorph.mk (splitE F κ).toEquiv (continuous_splitE F κ) (continuous_splitE_symm F κ)).toMeasurableEquiv
  have hint : ∀ h : (κ → AdeleRing (𝓞 F) F) → ℝ≥0∞,
      ∫⁻ x, h x ∂(((MeasureTheory.MeasureSpace.volume : Measure (κ → mixedEmbedding.mixedSpace F)).prod ν).map (splitE F κ)) = ∫⁻ p, h (splitE F κ p) ∂((MeasureTheory.MeasureSpace.volume : Measure (κ → mixedEmbedding.mixedSpace F)).prod ν) :=
    fun h => lintegral_map_equiv h em
  have key : ∀ Ψ ∈ GlobalTheory.WeilM.schA F κ,
      GlobalTheory.WeilL2Words.l2A F ν Ψ = ∫⁻ x, ‖Ψ x‖ₑ ^ 2 ∂(((MeasureTheory.MeasureSpace.volume : Measure (κ → mixedEmbedding.mixedSpace F)).prod ν).map (splitE F κ)) := by
    intro Ψ hΨ
    rw [hint]
    have hHm : Measurable fun p => ‖Ψ (splitE F κ p)‖ₑ ^ 2 :=
      (continuous_comp_splitE F κ Ψ hΨ).measurable.enorm.pow_const 2
    rw [lintegral_prod_symm _ hHm.aemeasurable]
    rfl
  refine ⟨ν, hνH, fun p Φ hΦ => ?_⟩
  rw [key _ (hpres p Φ hΦ), key _ hΦ]
  exact hU _ hμH p Φ hΦ

end GlobalTheory.WeilL2Isometry
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationL2IsometryStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_representation_l2_isometry : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] {G : Type} [Group G]
    (om : G →* Module.End ℂ ((κ → AF F) → ℂ)), (∀ p, ∀ φ ∈ schA F κ, om p φ ∈ schA F κ) → IsUnitaryOn (adeleClass F) om →
    ∃ μ : @MeasureTheory.Measure (κ → FiniteAdeleRing (𝓞 F) F) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ ∧
      ∀ p, ∀ Φ ∈ schA F κ, GlobalTheory.WeilL2Words.l2A F μ (om p Φ) = GlobalTheory.WeilL2Words.l2A F μ Φ := by
  first | exact @GlobalTheory.WeilL2Isometry.l2A_eq_of_isUnitaryOn | exact GlobalTheory.WeilL2Isometry.l2A_eq_of_isUnitaryOn | (intros; apply GlobalTheory.WeilL2Isometry.l2A_eq_of_isUnitaryOn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockEmbeddingRationalGLMemRationalPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockEmbeddingRationalGLMemRationalPoints
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open Matrix
open Formalism.UG (cT)
open scoped TensorProduct

namespace GlobalTheory.CuspBlockRat

theorem blockEmb_ratGL_mem_ratPts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf →
    ∀ (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      ∀ γ : GL (Fin d) E, ι (GlobalTheory.CuspRep.ratGL E d γ) ∈ ratPts σ J := by
  intro F E _ _ _ _ _ _ σ _ n J _ r Xf Yf _ l d h ι hι γ
  obtain ⟨Φ, j, -, -, hj, hΦ, hmat⟩ := hι
  have hΦE : ∀ x : E, Φ (inclR (F := F) (AF F) x) = algebraMap E (AdeleRing (𝓞 E) E) x := fun x => by
    rw [hΦ]
    refine Prod.ext ?_ ?_
    · show j (GlobalTheory.LFun.infTens F E ((1 : AF F) ⊗ₜ[F] x)) = algebraMap E (InfiniteAdeleRing E) x
      rw [← hj x]
      congr 1
    · show GlobalTheory.LFun.finAdEquiv F E (GlobalTheory.LFun.finTens F E ((1 : AF F) ⊗ₜ[F] x)) =
        algebraMap E (FiniteAdeleRing (𝓞 E) E) x
      have e : GlobalTheory.LFun.finTens F E ((1 : AF F) ⊗ₜ[F] x) = (1 : Af F) ⊗ₜ[F] x := by simp [GlobalTheory.LFun.finTens]
      rw [e, show GlobalTheory.LFun.finAdEquiv F E ((1 : Af F) ⊗ₜ[F] x) = _ from GlobalTheory.LFun.toFinAd_tmul 1 x, map_one, one_mul]
  have hΦs : ∀ x : E, Φ.symm (algebraMap E (AdeleRing (𝓞 E) E) x) = inclR (F := F) (AF F) x := fun x => by
    rw [RingEquiv.symm_apply_eq, hΦE]
  have hinj : Function.Injective (inclR (F := F) (E := E) (AF F)) := by
    intro x y hxy
    obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
    have := congrArg (fun z => (Φ z).1 w) hxy
    simp only [hΦE] at this
    exact (algebraMap E w.Completion).injective this
  have hrat : ∀ δ : GL (Fin d) E, (GlobalTheory.CuspRep.ratGL E d δ).1.map Φ.symm = δ.1.map (inclR (F := F) (AF F)) :=
    fun δ => by
      ext a b
      exact hΦs (δ.1 a b)
  refine GlobalTheory.CuspBlockLeft.mem_ratPts_of _ (1 + GlobalTheory.BlockForms.blkCols h Xf * (γ.1 - 1) *
      (cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h Yf) * J) +
    GlobalTheory.BlockForms.blkCols h Yf * (cT (σ : E →+* E) (γ⁻¹).1 - 1) *
      (cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h Xf) * J)) ?_ hinj
  rw [hmat, ← map_inv, hrat, hrat, GlobalTheory.CuspBlockLeft.cT_inclR]
  simp [Matrix.map_add (f := _), Matrix.map_sub, Matrix.map_mul, Matrix.map_one]

end GlobalTheory.CuspBlockRat

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockEmbeddingRationalGLMemRationalPointsStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockEmbedding_rationalGL_mem_rationalPoints : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf →
    ∀ (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      ∀ γ : GL (Fin d) E, ι (GlobalTheory.CuspRep.ratGL E d γ) ∈ ratPts σ J := by
  first | exact @GlobalTheory.CuspBlockRat.blockEmb_ratGL_mem_ratPts | exact GlobalTheory.CuspBlockRat.blockEmb_ratGL_mem_ratPts | (intros; apply GlobalTheory.CuspBlockRat.blockEmb_ratGL_mem_ratPts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaCmType
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.EtaCMType

theorem idFF_rat {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (a : Fˣ) :
    idFF F E (Units.map (algebraMap F (AF F)).toMonoidHom a) =
      Units.map (incAF F E).toMonoidHom (Units.map (algebraMap F E).toMonoidHom a) := by
  apply Units.ext
  change algebraMap (AF F) (AF F ⊗[F] E) (algebraMap F (AF F) (a : F)) =
    (Algebra.TensorProduct.includeRight : E →ₐ[F] AF F ⊗[F] E) (algebraMap F E (a : F))
  rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply]

theorem continuous_idFF {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    Continuous (idFF F E) := by
  haveI := IsModuleTopology.toContinuousAdd (AF F) (AF F ⊗[F] E)
  exact Continuous.units_map _
    (IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AF F) (AF F ⊗[F] E)))

theorem at_idFF {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (a : (AF F)ˣ)
    (h : At (evI F) ((a : AF F) - 1)) :
    At (evI F) (((idFF F E a : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1) := by
  intro u hu
  have e : ((idFF F E a : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1 = algebraMap (AF F) (AF F ⊗[F] E) ((a : AF F) - 1) := by
    rw [map_sub, map_one]; rfl
  rw [e, Algebra.smul_def, ← map_mul, ← smul_eq_mul, h u hu, map_zero]

theorem exists_eta_cmType : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∃ η : (AF F ⊗[F] E)ˣ →* Circle, IsHeckeCharF η ∧ ResEtaF η 1 ∧ HasExp B.emb η (fun _ => 1) := by
  intro F E _ _ _ _ _ σ B hB
  obtain ⟨ξ, hξ, hξe⟩ := GlobalTheory.T.exists_unitary_heckeCharacter_phase_type_cm F E σ B hB
  obtain ⟨η₀, hη₀, huniq⟩ := GlobalTheory.IdeleNormChar.globalNormIndexTwo F E hB.cm.2.2.1
  have hη₀' : IsEtaF E η₀ := hη₀
  let lam : (AF F)ˣ →* Circle := ξ.comp (idFF F E) * η₀⁻¹
  have hlam : ∀ a, lam a = ξ (idFF F E a) * (η₀ a)⁻¹ := fun a => rfl
  have hlc : Continuous lam := by
    have : Continuous fun a => ξ (idFF F E a) * (η₀ a)⁻¹ :=
      (hξ.1.comp continuous_idFF).mul (hη₀.1.inv)
    exact this
  have hlF : ∀ a : Fˣ, lam (Units.map (algebraMap F (AF F)).toMonoidHom a) = 1 := by
    intro a
    rw [hlam, idFF_rat, hξ.2, hη₀.2.1, inv_one, one_mul]
  have hlinf : ∀ a : (AF F)ˣ, At (evI F) ((a : AF F) - 1) → lam a = 1 := by
    intro a ha
    have e1 := hξe _ (at_idFF a ha)
    have e2 := GlobalTheory.T.cmQuadraticCharacter_eq_prod_realSigns F E σ B hB η₀ hη₀' a ha
    have e3 : ξ (idFF F E a) = η₀ a := by
      apply Circle.ext
      rw [e1, e2]
      refine Finset.prod_congr rfl fun w _ => ?_
      rw [zpow_one]
    rw [hlam, e3, mul_inv_cancel]
  obtain ⟨lam', hl'H, hl'inf, hl'res⟩ := GlobalTheory.T.exists_unitaryHeckeCharacter_extending_baseCharacter F E σ B hB lam hlc hlF hlinf
  refine ⟨ξ * lam'⁻¹, ⟨hξ.1.mul hl'H.1.inv, fun x => ?_⟩, ⟨⟨η₀, hη₀'⟩, fun η hη a => ?_⟩, fun z hz => ?_⟩
  · change ξ _ * (lam' _)⁻¹ = 1
    rw [hξ.2, hl'H.2, inv_one, one_mul]
  · change ξ _ * (lam' _)⁻¹ = _
    rw [huniq η hη, hl'res, hlam, pow_one, mul_inv_rev, inv_inv, ← mul_assoc, mul_inv_cancel_comm]
  · change ((ξ z * (lam' z)⁻¹ : Circle) : ℂ) = _
    rw [hl'inf z hz, inv_one, mul_one]
    exact hξe z hz

end GlobalTheory.EtaCMType
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsometryPosDefHermitianSameRank
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsometryPosDefHermitianSameRank
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BottomIsom

theorem hasSignature_map_star {n p q : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : Formalism.UG.HasSignature M p q) :
    Formalism.UG.HasSignature (M.map (starRingEnd ℂ)) p q := by
  obtain ⟨e, P, hP⟩ := h
  refine ⟨e, Matrix.GeneralLinearGroup.map (starRingEnd ℂ) P, ?_⟩
  have := congrArg (fun A => Matrix.map A (starRingEnd ℂ)) hP
  simp only [Matrix.map_mul] at this
  have hJ : (Formalism.UG.Jpq p q : Matrix _ _ ℂ).map (starRingEnd ℂ) = Formalism.UG.Jpq p q := by
    ext (a | a) (b | b) <;> simp [Formalism.UG.Jpq, Matrix.one_apply, apply_ite]
  rw [hJ] at this
  exact this

theorem hasSignature_all {D : D7} {V : HSp D} (h : NegIdx V 0) (σ : D.host.E →+* ℂ) :
    Formalism.UG.HasSignature (V.gram.map σ) V.rank 0 := by
  obtain ⟨τ, hσ | hσ⟩ := GlobalTheory.DefiniteMult.exists_tauE_or_conj D σ
  · subst hσ
    simpa [gramAt] using h τ
  · subst hσ
    have h1 := hasSignature_map_star (by simpa [gramAt] using h τ)
    rw [Matrix.map_map] at h1
    exact h1

def posResign {D : D7} (V : HSp D) : HSp D := { V with sig := fun _ => (V.rank, 0) }

theorem posResign_sigOK {D : D7} {V : HSp D} (h : NegIdx V 0) : (posResign V).SigOK := fun σ =>
  hasSignature_all h σ

theorem isoMat_of_posDef : ∀ {D : D7} {V V' : HSp D}, V.rank = V'.rank → NegIdx V 0 → NegIdx V' 0 →
    Nonempty (GlobalTheory.Mem.Isom.IsoMat V V') := by
  intro D V V' hr h h'
  obtain ⟨φ, hφ⟩ := GlobalTheory.LandherrSignature.exists_isometry_host D (posResign V) (posResign V')
    (posResign_sigOK h) (posResign_sigOK h') hr (fun _ => by simp [posResign, hr])
  exact ⟨GlobalTheory.Mem.Isom.IsoMat.ofEquiv φ hφ⟩

end GlobalTheory.BottomIsom
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsometryPosDefHermitianSameRankStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isometry_posDef_hermitian_same_rank : ∀ {D : D7} {V V' : HSp D}, V.rank = V'.rank → NegIdx V 0 → NegIdx V' 0 → Nonempty (GlobalTheory.Mem.Isom.IsoMat V V') := by
  first | exact @GlobalTheory.BottomIsom.isoMat_of_posDef | exact GlobalTheory.BottomIsom.isoMat_of_posDef | (intros; apply GlobalTheory.BottomIsom.isoMat_of_posDef <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepFinitePeriodicityPolynomialHeight
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepFinitePeriodicityPolynomialHeight
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
open GlobalTheory.ArchDecay

namespace GlobalTheory.ArchDecay

theorem per_om_level : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d), ∃ (C : ℝ) (k : ℕ), ∀ g h, ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ C * ((ht g : ℝ) * ht h) ^ k ∧ Per F m (om (g, h) Φ) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP Φ hΦ
  obtain ⟨C, k, hCk⟩ := GlobalTheory.ThetaLevel.periodic_level F E σ B n d X W M χX χW om r s r' s' hP Φ hΦ
  refine ⟨C, k, fun g h => ?_⟩
  obtain ⟨m, hm1, hmle, hper⟩ := hCk g h
  refine ⟨m, hm1, hmle, fun x z hz => ?_⟩
  choose a ha0 haI haz using hz
  have hz' : z = (m : AF F) • a := by
    funext i; simp [haz i]
  rw [hz']
  exact hper x a fun i => ⟨ha0 i, haI i⟩

end GlobalTheory.ArchDecay
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepFinitePeriodicityPolynomialHeightStatement
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
open GlobalTheory.ArchDecay
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRep_finite_periodicity_polynomial_height : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d), ∃ (C : ℝ) (k : ℕ), ∀ g h, ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ C * ((ht g : ℝ) * ht h) ^ k ∧ Per F m (om (g, h) Φ) := by
  first | exact @GlobalTheory.ArchDecay.per_om_level | exact GlobalTheory.ArchDecay.per_om_level | (intros; apply GlobalTheory.ArchDecay.per_om_level <;> assumption)
end
end
