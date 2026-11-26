module

public import ReciprocityTheory.GaloisValuations.ArithOfA
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.LocalGramMatrixFrame
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LinearIndependentOrth
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.VolUTr

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.VolULeaf
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.VolUHaar
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.VolTUnit
noncomputable section

namespace Formalism.L2.SG.Pf.NcVal

open Formalism.L2.SG.LocVol Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain
open scoped TensorProduct

namespace VolTU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

def OS : Submodule (v.adicCompletionIntegers F) (Fv F v ⊗[F] E) :=
  Submodule.span (v.adicCompletionIntegers F)
    ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ)

theorem mem_OEv (x : Fv F v ⊗[F] E) : x ∈ OEv (E := E) v ↔ x ∈ OS (E := E) v := Iff.rfl

theorem sc_mul (a b : Fv F v) : sc (E := E) v (a * b) = sc (E := E) v a * sc (E := E) v b := by
  simp [sc, Algebra.TensorProduct.tmul_mul_tmul]

theorem sc_one : sc (E := E) v (1 : Fv F v) = 1 := rfl

theorem sc_mul_eq_smul (c : Fv F v) (x : Fv F v ⊗[F] E) : sc (E := E) v c * x = c • x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sc, Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.smul_tmul']
  | add x y hx hy => rw [mul_add, hx, hy, smul_add]

theorem sc_mul_mem {c : Fv F v} (hc : c ∈ v.adicCompletionIntegers F) {x : Fv F v ⊗[F] E}
    (hx : x ∈ OEv (E := E) v) : sc (E := E) v c * x ∈ OEv (E := E) v := by
  rw [mem_OEv] at hx ⊢
  rw [sc_mul_eq_smul]
  have := (OS (E := E) v).smul_mem (⟨c, hc⟩ : v.adicCompletionIntegers F) hx
  exact this

theorem val_le_one_mem {c : Fv F v} (hc : Valued.v c ≤ 1) : c ∈ v.adicCompletionIntegers F :=
  (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 F) (K := F) (v := v)).mpr hc

theorem unit_mul_mem_iff {c : Fv F v} (hc : Valued.v c = 1) (x : Fv F v ⊗[F] E) :
    sc (E := E) v c * x ∈ OEv (E := E) v ↔ x ∈ OEv (E := E) v := by
  have hc0 : c ≠ 0 := by
    intro h; rw [h, map_zero] at hc; exact zero_ne_one hc
  constructor
  · intro h
    have hi : Valued.v c⁻¹ ≤ 1 := by rw [map_inv₀, hc, inv_one]
    have := sc_mul_mem (E := E) v (val_le_one_mem v hi) h
    rwa [← mul_assoc, ← sc_mul, inv_mul_cancel₀ hc0, sc_one, one_mul] at this
  · intro h
    exact sc_mul_mem (E := E) v (val_le_one_mem v hc.le) h

theorem val_alp (hd : Valued.v (dV v) = 1) (r : ℕ) (a : Fin (r + 1)) : Valued.v (alp v r a) = 1 := by
  unfold alp
  split_ifs
  · rw [map_pow, map_inv₀, hd, inv_one, one_pow]
  · exact map_one _

theorem natCast_ne_zero {g : ℕ} (hg : g ≠ 0) : (g : Fv F v) ≠ 0 := Nat.cast_ne_zero.mpr hg

theorem natCast_memO (g : ℕ) : (g : Fv F v) ∈ v.adicCompletionIntegers F :=
  _root_.natCast_mem (v.adicCompletionIntegers F) g

theorem one_lt_absNorm : 1 < Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  omega

theorem val_eq_one_of_absV {x : Fv F v} (h : absV v x = 1) : Valued.v x = 1 := by
  unfold absV at h
  split_ifs at h with h0
  · exact absurd h zero_ne_one
  · have hN : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by exact_mod_cast one_lt_absNorm v
    have hk : Multiplicative.toAdd (WithZero.unzero h0) = 0 :=
      (zpow_eq_one_iff_right₀ (by positivity) hN.ne').mp h
    have hu : WithZero.unzero h0 = 1 := by
      rw [← ofAdd_toAdd (WithZero.unzero h0), hk, ofAdd_zero]
    rw [← WithZero.coe_unzero h0, hu, WithZero.coe_one]

end VolTU


open VolTU in
theorem volTUOEq_of {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (hd : Valued.v (dV v) = 1) {g : ℕ} (hg : g ≠ 0) (r : ℕ) :
    VolTUOEq (E := E) v g r := by
  have key : ∀ (q : UIdx r) (y : Fv F v ⊗[F] E),
      sc (E := E) v ((alp v r q.1.1)⁻¹ * alp v r q.1.2) * y ∈ OEv (E := E) v ↔ y ∈ OEv (E := E) v := by
    intro q y
    apply VolTU.unit_mul_mem_iff
    simp only [map_mul, map_inv₀, VolTU.val_alp v hd, inv_one, one_mul]
  have e : ∀ (a b : Fv F v) (y : Fv F v ⊗[F] E),
      sc (E := E) v (a * b * (g : Fv F v)⁻¹) * y = sc (E := E) v (a * b) * (sc (E := E) v (g : Fv F v)⁻¹ * y) := by
    intro a b y
    rw [VolTU.sc_mul, mul_assoc]
  have hg0 := VolTU.natCast_ne_zero v hg
  have hgO := VolTU.natCast_memO v g
  have sw : ∀ y : Fv F v ⊗[F] E,
      y * sc (E := E) v (g : Fv F v)⁻¹ ∈ VolTU.OS (E := E) v ↔
        sc (E := E) v (g : Fv F v)⁻¹ * (-y) ∈ VolTU.OS (E := E) v := by
    intro y
    rw [mul_neg, Submodule.neg_mem_iff, mul_comm]
  unfold VolTUOEq
  ext p
  simp only [deepCongruenceVolume, VolTUSet, UO, Set.mem_setOf_eq, e, key]
  simp only [VolTU.mem_OEv]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, fun q => ?_⟩
    rw [sw, neg_sub]
    exact h3 q
  · rintro ⟨h1, h3⟩
    have h3' : ∀ q, sc (E := E) v (g : Fv F v)⁻¹ * (p.1 q - p.2 q) ∈ VolTU.OS (E := E) v := fun q => by
      rw [← neg_sub, ← sw]
      exact h3 q
    refine ⟨h1, fun q => ?_, h3'⟩
    have h4 := (VolTU.OS (E := E) v).smul_mem (⟨(g : Fv F v), hgO⟩ : v.adicCompletionIntegers F) (h3' q)
    have h5 : p.1 q - p.2 q ∈ VolTU.OS (E := E) v := by
      have h6 : (g : Fv F v) • (sc (E := E) v (g : Fv F v)⁻¹ * (p.1 q - p.2 q)) ∈ VolTU.OS (E := E) v := h4
      rwa [← VolTU.sc_mul_eq_smul, ← mul_assoc, ← VolTU.sc_mul, mul_inv_cancel₀ hg0, VolTU.sc_one, one_mul] at h6
    have h7 : p.2 q = p.1 q - (p.1 q - p.2 q) := by abel
    rw [h7]
    exact (VolTU.OS (E := E) v).sub_mem (h1 q) h5

end Formalism.L2.SG.Pf.NcVal
end
end

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.VolUH

open Formalism.L2.SG.LocVol Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal NNReal TensorProduct

theorem haar_pre {G : Type*} [AddCommGroup G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    (μ : Measure G) [μ.IsAddHaarMeasure] (φ : G ≃ₜ+ G) (K : Set G) (hK : μ K = 1) (S : Set G) :
    μ (φ ⁻¹' S) = μ (φ ⁻¹' K) * μ S := by
  have he : MeasurableEmbedding φ := φ.toHomeomorph.measurableEmbedding
  haveI : (μ.map φ).IsAddHaarMeasure :=
    μ.isAddHaarMeasure_map (φ : G →+ G) φ.continuous φ.surjective
      φ.toHomeomorph.isClosedEmbedding.tendsto_cocompact
  have h := Measure.isAddLeftInvariant_eq_smul (μ.map φ) μ
  have key : ∀ T : Set G, μ (φ ⁻¹' T) = (μ.map φ).addHaarScalarFactor μ * μ T := by
    intro T
    rw [← he.map_apply]
    conv_lhs => rw [h]
    simp
  rw [key S, key K, hK, mul_one]

section R

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

theorem top_facts (ι : Type) [Fintype ι] :
    IsTopologicalAddGroup (ι → Fv F v ⊗[F] E) ∧ LocallyCompactSpace (ι → Fv F v ⊗[F] E) ∧
      SecondCountableTopology (ι → Fv F v ⊗[F] E) ∧ BorelSpace (ι → Fv F v ⊗[F] E) ∧
      IsModuleTopology (Fv F v) (ι → Fv F v ⊗[F] E) := by
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩

def scMul {ι : Type} [Fintype ι] (z : ι → Fv F v) (hz : ∀ i, z i ≠ 0) :
    (ι → Fv F v ⊗[F] E) ≃ₜ+ (ι → Fv F v ⊗[F] E) where
  toFun w i := sc (E := E) v (z i) * w i
  invFun w i := sc (E := E) v (z i)⁻¹ * w i
  left_inv w := by
    funext i
    simp only
    rw [← mul_assoc, ← VolTU.sc_mul, inv_mul_cancel₀ (hz i), VolTU.sc_one, one_mul]
  right_inv w := by
    funext i
    simp only
    rw [← mul_assoc, ← VolTU.sc_mul, mul_inv_cancel₀ (hz i), VolTU.sc_one, one_mul]
  map_add' w w' := by
    funext i
    simp only [Pi.add_apply, mul_add]
  continuous_toFun := by
    obtain ⟨-, -, -, -, h⟩ := top_facts (E := E) v ι
    haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
    haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
    haveI : ContinuousAdd (Fv F v ⊗[F] E) := IsModuleTopology.toContinuousAdd (Fv F v) _
    exact IsModuleTopology.continuous_of_linearMap
      (PI.UnitaryGroupMassFormula.LocJacTyp.BM.mulL v fun i => sc (E := E) v (z i))
  continuous_invFun := by
    obtain ⟨-, -, -, -, h⟩ := top_facts (E := E) v ι
    haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
    haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
    haveI : ContinuousAdd (Fv F v ⊗[F] E) := IsModuleTopology.toContinuousAdd (Fv F v) _
    exact IsModuleTopology.continuous_of_linearMap
      (PI.UnitaryGroupMassFormula.LocJacTyp.BM.mulL v fun i => sc (E := E) v (z i)⁻¹)

theorem sc_pre (ι : Type) [Fintype ι] (μ : Measure (ι → Fv F v ⊗[F] E)) [μ.IsAddHaarMeasure]
    (hK : μ (VolTO (E := E) v ι) = 1) (z : ι → Fv F v) (hz : ∀ i, z i ≠ 0) (S : Set (ι → Fv F v ⊗[F] E)) :
    μ {w | (fun i => sc (E := E) v (z i) * w i) ∈ S} =
      μ {w | ∀ i, sc (E := E) v (z i) * w i ∈ OEv (E := E) v} * μ S := by
  exact haar_pre μ (scMul (E := E) v z hz) _ hK S

theorem sub_pre (ι : Type) [Fintype ι] (μ : Measure (ι → Fv F v ⊗[F] E)) [μ.IsAddHaarMeasure]
    (b : ι → Fv F v ⊗[F] E) (S : Set (ι → Fv F v ⊗[F] E)) :
    μ {w | (fun i => w i - b i) ∈ S} = μ S := by
  have h : {w | (fun i => w i - b i) ∈ S} = (fun w => w + -b) ⁻¹' S := by
    ext w
    simp [sub_eq_add_neg]
    rfl
  rw [h, measure_preimage_add_right]

end R

end Formalism.L2.SG.Pf.NcVal.VolUH
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.VolTProd
noncomputable section

namespace Formalism.L2.SG.Pf.NcVal

open Formalism.L2.SG.LocVol Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory
open scoped ENNReal TensorProduct

theorem volTProdU_of {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (g r : ℕ)
    [SFinite (sdE (E := E) ψ v (UIdx r))]
    (hM : MeasurableSet (VolTUSet (E := E) v g r)) (hMO : MeasurableSet (VolTO (E := E) v (UIdx r)))
    (hA : VolTAff (E := E) ψ v g (UIdx r)) (hO : VolTOne (E := E) ψ v (UIdx r)) :
    VolTProdU (E := E) ψ v g r := by
  unfold VolTProdU
  rw [Measure.prod_apply hM]
  have hsec : ∀ x : UIdx r → Fv F v ⊗[F] E,
      sdE (E := E) ψ v (UIdx r) (Prod.mk x ⁻¹' VolTUSet (E := E) v g r) =
        (VolTO (E := E) v (UIdx r)).indicator (fun _ => ((g : ℝ≥0∞) ^ (2 * Fintype.card (UIdx r)))⁻¹) x := by
    intro x
    by_cases hx : x ∈ VolTO (E := E) v (UIdx r)
    · rw [Set.indicator_of_mem hx]
      have hpre : Prod.mk x ⁻¹' VolTUSet (E := E) v g r =
          {w | (fun i => (w i - x i) * sc (E := E) v (g : Fv F v)⁻¹) ∈ VolTO (E := E) v (UIdx r)} := by
        ext y
        simp only [Set.mem_preimage, VolTUSet, VolTO, Set.mem_ofPred_eq]
        exact ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩
      rw [hpre, hA, hO, mul_one]
    · rw [Set.indicator_of_notMem hx]
      have hpre : Prod.mk x ⁻¹' VolTUSet (E := E) v g r = ∅ := by
        ext y
        simp only [Set.mem_preimage, VolTUSet, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        exact fun h => hx h.1
      rw [hpre, measure_empty]
  simp_rw [hsec]
  rw [lintegral_indicator_const hMO, mul_comm]

end Formalism.L2.SG.Pf.NcVal
end
end

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.VolUL

open Formalism.L2.SG.Pf.NcVal Formalism.L2.SG.LocVol Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal NNReal TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F))

def AnnAt : Prop :=
  ∀ y : Fv F v ⊗[F] E,
    (∀ x ∈ OEv (E := E) v, psiV F ψ v (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (x * y)) = 1) ↔
      sc (E := E) v (dV v) * y ∈ OEv (E := E) v

theorem volTO_eq (ι : Type) : VolTO (E := E) v ι = Set.univ.pi fun _ => OEv (E := E) v := by
  ext x
  simp [VolTO]

theorem sd_facts (hψ : IsCharAF F ψ) (hfin : Module.finrank F E = 2) (hann : AnnAt (E := E) ψ v)
    (hd : absV v (dV v) = 1) (ι : Type) [Fintype ι] :
    (sdE (E := E) ψ v ι).IsAddHaarMeasure ∧ SFinite (sdE (E := E) ψ v ι) ∧ VolTOne (E := E) ψ v ι := by
  classical
  obtain ⟨h1, h2, h3, h4, h5⟩ := Formalism.L2.SG.Pf.NcVal.VolUH.top_facts (E := E) v ι
  have hunit : Valued.v (dV v) = 1 := Formalism.L2.SG.Pf.NcVal.VolTU.val_eq_one_of_absV v hd
  have hD1 : PI.UnitaryGroupMassFormula.LocJacTyp.Sd.D1 (E := E) v ψ = OEv (E := E) v := by
    ext y
    show (∀ x ∈ OEv (E := E) v, _) ↔ _
    rw [hann y, Formalism.L2.SG.Pf.NcVal.VolTU.unit_mul_mem_iff v hunit]
  have hone : (1 : Fv F v ⊗[F] E) ∈ OEv (E := E) v := by
    have := PI.UnitaryGroupMassFormula.LocJacTyp.Sd.inclR_mem (E := E) v 1
    simp only [OneMemClass.coe_one, map_one] at this
    exact this
  have htr1 : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) 1 = 2 := by
    have := PI.UnitaryGroupMassFormula.LocJacTyp.Sd.trace_inclR (E := E) v 1
    simp only [map_one] at this
    rw [this, show (1 : E) = algebraMap F E 1 from (map_one _).symm, Algebra.trace_algebraMap, hfin]
    simp
    exact map_ofNat _ 2
  have hOK : PI.UnitaryGroupMassFormula.LocJacTyp.Sd.OpenKer v ψ := by
    refine PI.UnitaryGroupMassFormula.LocJacTyp.Sd.openKer_of v ψ 2 two_ne_zero ?_
    intro c hc
    have hy : sc (E := E) v c * 1 ∈ OEv (E := E) v :=
      Formalism.L2.SG.Pf.NcVal.VolTU.sc_mul_mem v hc hone
    have hmem : sc (E := E) v c * 1 ∈ PI.UnitaryGroupMassFormula.LocJacTyp.Sd.D1 (E := E) v ψ := by rw [hD1]; exact hy
    have := hmem 1 hone
    rw [one_mul, Formalism.L2.SG.Pf.NcVal.VolTU.sc_mul_eq_smul, map_smul, htr1, smul_eq_mul] at this
    exact this
  have hnt : ∃ r : Fv F v, psiV F ψ v r ≠ 1 := by
    obtain ⟨t0, ht0⟩ := PI.UnitaryGroupMassFormula.LocJacTyp.Sd.exists_not_mem_oev (E := E) v
    have : t0 ∉ PI.UnitaryGroupMassFormula.LocJacTyp.Sd.D1 (E := E) v ψ := by rw [hD1]; exact ht0
    simp only [PI.UnitaryGroupMassFormula.LocJacTyp.Sd.D1, Set.mem_setOf_eq, not_forall] at this
    obtain ⟨x, _, hx⟩ := this
    exact ⟨_, hx⟩
  have hex := PI.UnitaryGroupMassFormula.LocJacTyp.Sd.exists_sd (E := E) v ψ hOK hnt ι
  have hsd : SelfDual (sdE (E := E) ψ v ι) (PI.UnitaryGroupMassFormula.LocJacTyp.Sd.chi v ψ ι) := by
    have hex' : ∃ μ : Measure (ι → Fv F v ⊗[F] E), SelfDual μ fun x y : ι → Fv F v ⊗[F] E =>
        psiV F ψ v (∑ i : ι, Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (x i * y i)) := hex
    unfold sdE
    rw [dite_eq_left hex']
    exact hex'.choose_spec
  haveI : (sdE (E := E) ψ v ι).IsAddHaarMeasure := hsd.1
  refine ⟨inferInstance, inferInstance, ?_⟩
  have hDO : PI.UnitaryGroupMassFormula.LocJacTyp.Sd.Dbox (E := E) v ψ ι = PI.UnitaryGroupMassFormula.LocJacTyp.Obox v ι := by
    simp only [PI.UnitaryGroupMassFormula.LocJacTyp.Sd.Dbox, PI.UnitaryGroupMassFormula.LocJacTyp.Obox, hD1]
    rfl
  have hOc := PI.UnitaryGroupMassFormula.LocJacTyp.Sd.isCompact_obox (E := E) v ι
  have hOo := PI.UnitaryGroupMassFormula.LocJacTyp.Sd.isOpen_obox (E := E) v ι
  have hfin' : sdE (E := E) ψ v ι (PI.UnitaryGroupMassFormula.LocJacTyp.Obox v ι) < ⊤ := hOc.measure_lt_top
  have ht := PI.UnitaryGroupMassFormula.LocJacTyp.Sd.sd_test (E := E) v ψ ι _ hsd (by rw [hDO]; exact hOo.measurableSet)
    (by rw [hDO]; exact hfin')
  rw [hDO] at ht
  have hpos : 0 ≤ (sdE (E := E) ψ v ι).real (PI.UnitaryGroupMassFormula.LocJacTyp.Obox v ι) := measureReal_nonneg
  have hr : (sdE (E := E) ψ v ι).real (PI.UnitaryGroupMassFormula.LocJacTyp.Obox v ι) = 1 := by
    nlinarith [sq_nonneg ((sdE (E := E) ψ v ι).real (PI.UnitaryGroupMassFormula.LocJacTyp.Obox v ι) - 1)]
  show sdE (E := E) ψ v ι (VolTO (E := E) v ι) = 1
  rw [volTO_eq]
  change sdE (E := E) ψ v ι (PI.UnitaryGroupMassFormula.LocJacTyp.Obox v ι) = 1
  rw [← ENNReal.ofReal_toReal hfin'.ne]
  simpa [measureReal_def] using congrArg ENNReal.ofReal hr

theorem volTAff_of (hψ : IsCharAF F ψ) (hfin : Module.finrank F E = 2) (hann : AnnAt (E := E) ψ v)
    (hd : absV v (dV v) = 1) {g : ℕ} (hg0 : g ≠ 0) (hg : absV v (g : Fv F v) = (g : ℝ)⁻¹)
    (ι : Type) [Fintype ι] : VolTAff (E := E) ψ v g ι := by
  classical
  intro b S
  obtain ⟨hH, hS, hV⟩ := sd_facts (E := E) ψ v hψ hfin hann hd ι
  set μ := sdE (E := E) ψ v ι with hμ
  have hgne : ((g : Fv F v))⁻¹ ≠ 0 := inv_ne_zero (Formalism.L2.SG.Pf.NcVal.VolTU.natCast_ne_zero v hg0)
  set T : Set (ι → Fv F v ⊗[F] E) := {u | (fun i => sc (E := E) v ((g : Fv F v))⁻¹ * u i) ∈ S} with hT
  have h1 : μ {w : ι → Fv F v ⊗[F] E | (fun i => (w i - b i) * sc (E := E) v ((g : Fv F v))⁻¹) ∈ S} = μ T := by
    have := Formalism.L2.SG.Pf.NcVal.VolUH.sub_pre (E := E) v ι μ b T
    rw [← this]
    congr 1
    ext w
    simp only [hT, Set.mem_setOf_eq, mul_comm]
  have h2 := Formalism.L2.SG.Pf.NcVal.VolUH.sc_pre (E := E) v ι μ hV (fun _ => ((g : Fv F v))⁻¹) (fun _ => hgne) S
  rw [h1, hT, h2]
  congr 1
  have hset : {w : ι → Fv F v ⊗[F] E | ∀ i, sc (E := E) v ((g : Fv F v))⁻¹ * w i ∈ OEv (E := E) v} =
      Set.univ.pi fun _ : ι => {c : Fv F v ⊗[F] E | sc (E := E) v ((g : Fv F v))⁻¹ * c ∈ OEv (E := E) v} := by
    ext w
    simp
  rw [hset]
  have hbs := PI.UnitaryGroupMassFormula.LocJacTyp.boxScale (E := E) v hfin μ (fun _ => ((g : Fv F v))⁻¹) (fun _ => hgne)
  have hO : μ (PI.UnitaryGroupMassFormula.LocJacTyp.Obox v ι) = 1 := by
    have := hV
    simp only [VolTOne, volTO_eq] at this
    exact this
  have hsub : (Set.univ.pi fun _ : ι => {c : Fv F v ⊗[F] E | sc (E := E) v ((g : Fv F v))⁻¹ * c ∈ OEv (E := E) v})
      ⊆ PI.UnitaryGroupMassFormula.LocJacTyp.Obox v ι := by
    intro w hw
    simp only [Set.mem_pi, Set.mem_univ, Set.mem_setOf_eq, forall_true_left] at hw
    simp only [PI.UnitaryGroupMassFormula.LocJacTyp.Obox, Set.mem_pi, Set.mem_univ, forall_true_left]
    intro i
    have := Formalism.L2.SG.Pf.NcVal.VolTU.sc_mul_mem (E := E) v (Formalism.L2.SG.Pf.NcVal.VolTU.natCast_memO v g) (hw i)
    rw [← mul_assoc, ← Formalism.L2.SG.Pf.NcVal.VolTU.sc_mul, mul_inv_cancel₀ (Formalism.L2.SG.Pf.NcVal.VolTU.natCast_ne_zero v hg0),
      Formalism.L2.SG.Pf.NcVal.VolTU.sc_one, one_mul] at this
    exact this
  have hfin' : μ (Set.univ.pi fun _ : ι => {c : Fv F v ⊗[F] E | sc (E := E) v ((g : Fv F v))⁻¹ * c ∈ OEv (E := E) v}) ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [hO]; exact ENNReal.one_ne_top) (measure_mono hsub)
  rw [← ENNReal.ofReal_toReal hfin']
  change ENNReal.ofReal (μ (Set.univ.pi fun i : ι => {c : Fv F v ⊗[F] E | PI.LocJacTyp.sc v ((fun _ => ((g : Fv F v))⁻¹) i) * c ∈ PI.LocJacTyp.OEv v})).toReal = _
  rw [hbs, hO]
  have habs : PI.LocJacTyp.absV v ((g : Fv F v))⁻¹ = (g : ℝ) := by
    rw [PI.UnitaryGroupMassFormula.LocJacTyp.absV_inv]
    change (absV v (g : Fv F v))⁻¹ = _
    rw [hg, inv_inv]
  simp only [habs, ENNReal.toReal_one, one_mul, Finset.prod_const, Finset.card_univ]
  rw [← inv_pow, ← pow_mul, ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_inv_of_pos (by positivity)]
  rw [ENNReal.ofReal_natCast, ← ENNReal.inv_pow, mul_comm]

theorem volTLocPres_of (hψ : IsCharAF F ψ) (hfin : Module.finrank F E = 2) (hann : AnnAt (E := E) ψ v)
    (hd : absV v (dV v) = 1) (r : ℕ) : VolTLocPres (E := E) ψ v r := by
  classical
  intro S
  obtain ⟨hH, hS, hV⟩ := sd_facts (E := E) ψ v hψ hfin hann hd (Fin (r + 1) × Fin (r + 1))
  have hunit : Valued.v (dV v) = 1 := Formalism.L2.SG.Pf.NcVal.VolTU.val_eq_one_of_absV v hd
  have hz : ∀ p : Fin (r + 1) × Fin (r + 1), alp v r p.1 * alp v r p.2 ≠ 0 := by
    intro p h
    have h1 := Formalism.L2.SG.Pf.NcVal.VolTU.val_alp v hunit r p.1
    have h2 := Formalism.L2.SG.Pf.NcVal.VolTU.val_alp v hunit r p.2
    have : Valued.v (alp v r p.1 * alp v r p.2) = 1 := by rw [map_mul, h1, h2, one_mul]
    rw [h, map_zero] at this
    exact zero_ne_one this
  have key := Formalism.L2.SG.Pf.NcVal.VolUH.sc_pre (E := E) v (Fin (r + 1) × Fin (r + 1)) (sdE (E := E) ψ v _) hV
    (fun p => alp v r p.1 * alp v r p.2) hz S
  have hset : {w : Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E |
      ∀ i, sc (E := E) v (alp v r i.1 * alp v r i.2) * w i ∈ OEv (E := E) v} = VolTO (E := E) v _ := by
    ext w
    simp only [Set.mem_setOf_eq, VolTO]
    refine forall_congr' fun i => ?_
    apply Formalism.L2.SG.Pf.NcVal.VolTU.unit_mul_mem_iff
    rw [map_mul, Formalism.L2.SG.Pf.NcVal.VolTU.val_alp v hunit, Formalism.L2.SG.Pf.NcVal.VolTU.val_alp v hunit, one_mul]
  rw [hset, hV, one_mul] at key
  exact key

theorem volTO_meas (ι : Type) [Fintype ι] : MeasurableSet (VolTO (E := E) v ι) := by
  rw [volTO_eq]
  exact MeasurableSet.univ_pi fun _ => (PI.UnitaryGroupMassFormula.LocJacTyp.Sd.isOpen_oev (E := E) v).measurableSet

theorem volTUSet_meas {g : ℕ} (hg0 : g ≠ 0) (r : ℕ) : MeasurableSet (VolTUSet (E := E) v g r) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := Formalism.L2.SG.Pf.NcVal.VolUH.top_facts (E := E) v (UIdx r)
  have hO := PI.UnitaryGroupMassFormula.LocJacTyp.Sd.isOpen_oev (E := E) v
  have hc : Continuous fun x : Fv F v ⊗[F] E => x * sc (E := E) v ((g : Fv F v))⁻¹ := by
    simp_rw [mul_comm _ (sc (E := E) v _), Formalism.L2.SG.Pf.NcVal.VolTU.sc_mul_eq_smul]
    exact continuous_const_smul _
  apply IsOpen.measurableSet
  simp only [VolTUSet, Set.setOf_and]
  apply IsOpen.inter
  · simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun q => hO.preimage ((continuous_apply q).comp continuous_fst)
  · simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun q => hO.preimage
      (hc.comp (((continuous_apply q).comp continuous_snd).sub ((continuous_apply q).comp continuous_fst)))

theorem volTProdU_of' (hψ : IsCharAF F ψ) (hfin : Module.finrank F E = 2) (hann : AnnAt (E := E) ψ v)
    (hd : absV v (dV v) = 1) {g : ℕ} (hg0 : g ≠ 0) (hg : absV v (g : Fv F v) = (g : ℝ)⁻¹) (r : ℕ) :
    VolTProdU (E := E) ψ v g r := by
  obtain ⟨-, hS, hO⟩ := sd_facts ψ v hψ hfin hann hd (UIdx r)
  exact volTProdU_of ψ v g r (volTUSet_meas v hg0 r) (volTO_meas v (UIdx r))
    (volTAff_of ψ v hψ hfin hann hd hg0 hg (UIdx r)) hO

end Formalism.L2.SG.Pf.NcVal.VolUL
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.VolumeDeepCongruenceOfFubini
noncomputable section

namespace Formalism.L2.SG.Pf.NcVal

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.LocVol Formalism.L2.SG.MassDataConc Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
  NumberField IsDedekindDomain
open scoped ENNReal TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem volU_two_card_uidx (r : ℕ) : 2 * Fintype.card (UIdx r) = r * (r + 1) := by
  classical
  have hlt : Fintype.card (UIdx r) =
      (Finset.univ.filter (fun p : Fin (r + 1) × Fin (r + 1) => p.1 < p.2)).card :=
    Fintype.card_subtype _
  have hgt : (Finset.univ.filter (fun p : Fin (r + 1) × Fin (r + 1) => p.1 < p.2)).card =
      (Finset.univ.filter (fun p : Fin (r + 1) × Fin (r + 1) => p.2 < p.1)).card := by
    refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
    · intro p hp; simpa using hp
    · intro p _ q _ h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.2 h.1
    · intro q hq
      exact ⟨(q.2, q.1), by simpa using hq, rfl⟩
  have heq : (Finset.univ.filter (fun p : Fin (r + 1) × Fin (r + 1) => p.1 = p.2)).card = r + 1 := by
    have : Finset.univ.filter (fun p : Fin (r + 1) × Fin (r + 1) => p.1 = p.2) =
        Finset.univ.map ⟨fun a : Fin (r + 1) => (a, a), fun a b h => by simpa using h⟩ := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
      constructor
      · intro h; exact ⟨p.1, Prod.ext rfl h⟩
      · rintro ⟨a, rfl⟩; rfl
    rw [this, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  have h1 := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin (r + 1) × Fin (r + 1)))) (fun p => p.1 < p.2)
  have h2 := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun p : Fin (r + 1) × Fin (r + 1) => ¬ p.1 < p.2)) (fun p => p.2 < p.1)
  rw [Finset.filter_filter, Finset.filter_filter] at h2
  have e1 : Finset.univ.filter (fun p : Fin (r + 1) × Fin (r + 1) => ¬ p.1 < p.2 ∧ p.2 < p.1) =
      Finset.univ.filter (fun p : Fin (r + 1) × Fin (r + 1) => p.2 < p.1) :=
    Finset.filter_congr (fun p _ => ⟨fun h => h.2, fun h => ⟨not_lt.mpr h.le, h⟩⟩)
  have e2 : Finset.univ.filter (fun p : Fin (r + 1) × Fin (r + 1) => ¬ p.1 < p.2 ∧ ¬ p.2 < p.1) =
      Finset.univ.filter (fun p : Fin (r + 1) × Fin (r + 1) => p.1 = p.2) :=
    Finset.filter_congr (fun p _ => ⟨fun h => le_antisymm (not_lt.mp h.2) (not_lt.mp h.1),
      fun h => ⟨by rw [h]; exact lt_irrefl _, by rw [h]; exact lt_irrefl _⟩⟩)
  rw [e1, e2, heq] at h2
  rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at h1
  have hsq : (r + 1) * (r + 1) = r * (r + 1) + (r + 1) := by ring
  omega

section OfX

variable {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem volU_gAt_pos (v : PlX X) : 0 < gAt X v := by
  unfold gAt
  split_ifs
  · exact (D.host.g_prime 0).pos
  · exact (D.host.g_prime 1).pos

def VolUHyp : Prop :=
  IsCharAF X.B.I.F ψ ∧ IsStdChar ψ ∧ (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2]

theorem volU_ratio (v : PlX X) (hZ : VolTZZAt X u u' ψ v) (hU : VolumeDeepCongruenceSubgroup X ψ v) :
    localVolumeUnit X ψ v / ZZX X u u' ψ v = (gAt X v : ℝ) ^ ((D.R.rS + 1) * (2 * D.R.rS + 3)) := by
  rw [hU, hZ]
  have hg : (gAt X v : ℝ) ≠ 0 := by exact_mod_cast (volU_gAt_pos X v).ne'
  rw [← zpow_sub₀ hg, ← zpow_natCast]
  congr 1
  push_cast
  ring

theorem volTypV_of' (h : VolUHyp X u u' ψ → ∀ v, TypAt X v → VolTZZAt X u u' ψ v ∧ VolumeDeepCongruenceSubgroup X ψ v) :
    VolTypV X u u' ψ := by
  intro h1 h2 h3 v hv
  obtain ⟨hZ, hU⟩ := h ⟨h1, h2, h3⟩ v hv
  exact volU_ratio X u u' ψ v hZ hU

theorem volUZZAt_of (v : PlX X) (hv : TypAt X v)
    (hA : VolTAff (E := X.B.I.E) ψ v (gAt X v) (Fin (D.R.rS + 1) × Fin (D.R.rS + 1)))
    (hL : VolTLocPres (E := X.B.I.E) ψ v D.R.rS)
    (hH : VolTHermCnt X.B.I.cm.sig ψ v (gAt X v) D.R.rS)
    (hC : VolTTFCong X u u' v) : VolTZZAt X u u' ψ v := by
  unfold VolTZZAt ZZX volS
  rw [if_pos hv]
  have hset : ZZTyp X.B.I.cm.sig v (gAt X v) D.R.rS (TFv X u v) (TFv X u' v) =
      {z | (fun p => locZ (E := X.B.I.E) v z p.1 p.2) ∈
        {w | (fun p => (w p - TFv X u v p.1 p.2) * sc (E := X.B.I.E) v (gAt X v : Fv X.B.I.F v)⁻¹) ∈
          VolTW X.B.I.cm.sig v (gAt X v) D.R.rS
            (fun i j => (TFv X u' v i j - TFv X u v i j) * sc (E := X.B.I.E) v (gAt X v : Fv X.B.I.F v)⁻¹)}} := by
    rfl
  rw [hset, hL, hA, hH _ hC]
  simp only [Fintype.card_prod, Fintype.card_fin]
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_pow,
    ENNReal.toReal_natCast, zpow_neg, zpow_natCast, ← mul_inv, ← pow_add]
  congr 2
  ring

theorem volume_deep_congruence_of_fubini (v : PlX X) (hv : TypAt X v)
    (hE : VolTUOEq (E := X.B.I.E) v (gAt X v) D.R.rS)
    (hP : VolTProdU (E := X.B.I.E) ψ v (gAt X v) D.R.rS)
    (hO : VolTOne (E := X.B.I.E) ψ v (UIdx D.R.rS)) : VolumeDeepCongruenceSubgroup X ψ v := by
  unfold VolumeDeepCongruenceSubgroup localVolumeUnit volU
  rw [if_pos hv, hE, hP, hO, one_mul, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_natCast,
    volU_two_card_uidx, zpow_neg, zpow_natCast]

def VolUSteps (v : PlX X) : Prop :=
  VolTAff (E := X.B.I.E) ψ v (gAt X v) (Fin (D.R.rS + 1) × Fin (D.R.rS + 1)) ∧
      VolTLocPres (E := X.B.I.E) ψ v D.R.rS ∧ VolTHermCnt X.B.I.cm.sig ψ v (gAt X v) D.R.rS ∧
      VolTTFCong X u u' v ∧ VolTUOEq (E := X.B.I.E) v (gAt X v) D.R.rS ∧
      VolTProdU (E := X.B.I.E) ψ v (gAt X v) D.R.rS ∧ VolTOne (E := X.B.I.E) ψ v (UIdx D.R.rS)

theorem volTypV_of_steps' (h : VolUHyp X u u' ψ → ∀ v, TypAt X v → VolUSteps X u u' ψ v) :
    VolTypV X u u' ψ :=
  volTypV_of' X u u' ψ fun hh v hv =>
    ⟨volUZZAt_of X u u' ψ v hv (h hh v hv).1 (h hh v hv).2.1 (h hh v hv).2.2.1 (h hh v hv).2.2.2.1,
      volume_deep_congruence_of_fubini X ψ v hv (h hh v hv).2.2.2.2.1 (h hh v hv).2.2.2.2.2.1 (h hh v hv).2.2.2.2.2.2⟩

end OfX

end Formalism.L2.SG.Pf.NcVal
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.VolUArith
noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.VolUAr

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Ideal

section V

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem val_natCast_of (g : ℕ) (hg1 : (g : 𝓞 F) ∈ v.asIdeal) (hg2 : (g : 𝓞 F) ∉ v.asIdeal ^ 2) :
    Valued.v (((g : v.adicCompletionIntegers F) : v.adicCompletion F)) = WithZero.exp (-1 : ℤ) := by
  have e : (((g : v.adicCompletionIntegers F) : v.adicCompletion F)) = (((g : 𝓞 F) : F) : v.adicCompletion F) := by
    push_cast
    exact (map_natCast (algebraMap F (v.adicCompletion F)) g).symm
  rw [e, valuedAdicCompletion_eq_valuation', valuation_of_algebraMap]
  have hg0 : (g : 𝓞 F) ≠ 0 := by
    rintro h
    exact hg2 (h ▸ Ideal.zero_mem _)
  have h1 := (intValuation_le_pow_iff_dvd v (g : 𝓞 F) 1).mpr (by rwa [pow_one, Ideal.dvd_span_singleton])
  have h2 : ¬ v.intValuation (g : 𝓞 F) ≤ WithZero.exp (-((2 : ℕ) : ℤ)) := by
    rw [intValuation_le_pow_iff_dvd, Ideal.dvd_span_singleton]
    exact hg2
  rw [intValuation_eq_exp_neg_multiplicity v hg0] at h1 h2 ⊢
  rw [WithZero.exp_le_exp] at h1 h2
  congr 1
  omega

end V

theorem split_transport {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] (e : K ≃+* L)
    (l : ℕ) (h : {w : HeightOneSpectrum (𝓞 L) | ((l : ℕ) : 𝓞 L) ∈ w.asIdeal}.ncard = Module.finrank ℚ L) :
    {w : HeightOneSpectrum (𝓞 K) | ((l : ℕ) : 𝓞 K) ∈ w.asIdeal}.ncard = Module.finrank ℚ K := by
  set φ : 𝓞 K ≃+* 𝓞 L := NumberField.RingOfIntegers.mapRingEquiv e with hφ
  rw [(e.toRatAlgEquiv).toLinearEquiv.finrank_eq, ← h]
  refine Set.ncard_congr
    (fun w _ => (⟨w.asIdeal.map φ, Ideal.map_isPrime_of_equiv φ,
      fun hb => w.ne_bot ((Ideal.map_eq_bot_iff_of_injective φ.injective).mp hb)⟩ : HeightOneSpectrum (𝓞 L)))
    ?_ ?_ ?_
  · intro w hw
    have h1 := Ideal.mem_map_of_mem φ hw
    rw [map_natCast] at h1
    exact h1
  · intro a b _ _ hab
    have h1 : a.asIdeal.map φ = b.asIdeal.map φ := congrArg HeightOneSpectrum.asIdeal hab
    have h2 := congrArg (Ideal.comap φ) h1
    rw [Ideal.comap_map_of_bijective φ φ.bijective, Ideal.comap_map_of_bijective φ φ.bijective] at h2
    exact HeightOneSpectrum.ext h2
  · intro w' hw'
    have hne : w'.asIdeal.comap φ ≠ ⊥ := by
      intro hb
      apply w'.ne_bot
      rw [← Ideal.map_comap_of_surjective φ φ.surjective w'.asIdeal, hb, Ideal.map_bot]
    refine ⟨⟨w'.asIdeal.comap φ, Ideal.IsPrime.comap φ, hne⟩, ?_, ?_⟩
    · show _ ∈ Ideal.comap φ w'.asIdeal
      rw [Ideal.mem_comap, map_natCast]
      exact hw'
    · exact HeightOneSpectrum.ext (Ideal.map_comap_of_surjective φ φ.surjective w'.asIdeal)

section K

variable {K : Type} [Field K] [NumberField K]

private theorem liesOver_span_of_natCast_mem' (l : ℕ) [Fact l.Prime] (w : Ideal (𝓞 K)) [w.IsPrime]
    (hw : ((l : ℕ) : 𝓞 K) ∈ w) : w.LiesOver (Ideal.span {((l : ℕ) : ℤ)}) := by
  refine ⟨(Int.ideal_span_isMaximal_of_prime l).eq_of_le (Ideal.IsPrime.ne_top (Ideal.IsPrime.under ℤ w)) ?_⟩
  rw [Ideal.span_le, Set.singleton_subset_iff]
  show _ ∈ Ideal.comap (algebraMap ℤ (𝓞 K)) w
  rw [Ideal.mem_comap]
  simpa using hw

theorem locDeg_one (l : ℕ) [hl : Fact l.Prime]
    (h : {w : HeightOneSpectrum (𝓞 K) | ((l : ℕ) : 𝓞 K) ∈ w.asIdeal}.ncard = Module.finrank ℚ K)
    (w : HeightOneSpectrum (𝓞 K)) (hw : ((l : ℕ) : 𝓞 K) ∈ w.asIdeal) :
    w.asIdeal.ramificationIdx ℤ = 1 ∧ w.asIdeal.inertiaDeg ℤ = 1 := by
  have hmaxl := Int.ideal_span_isMaximal_of_prime l
  have hl0 : ((l : ℕ) : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.mpr hl.out.ne_zero
  have hsum := Ideal.sum_ramification_inertia_eq_finrank (Ideal.span {((l : ℕ) : ℤ)}) (𝓞 K)
  rw [NumberField.RingOfIntegers.rank] at hsum
  have hcard : Fintype.card ((Ideal.span {((l : ℕ) : ℤ)}).primesOver (𝓞 K)) = Module.finrank ℚ K := by
    rw [← h, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    symm
    refine Set.ncard_congr (fun w _ => w.asIdeal) (fun w hw => ⟨w.isPrime, liesOver_span_of_natCast_mem' l w.asIdeal hw⟩)
      (fun a b _ _ hab => HeightOneSpectrum.ext hab) ?_
    intro Q hQ
    haveI := hQ.1
    haveI := hQ.2
    have hmem : ((l : ℕ) : 𝓞 K) ∈ Q := by
      have h3 : ((l : ℕ) : ℤ) ∈ Q.under ℤ := by
        rw [← Ideal.over_def Q (Ideal.span {((l : ℕ) : ℤ)})]
        exact Ideal.mem_span_singleton_self _
      have h4 := Ideal.mem_comap.mp h3
      simpa using h4
    refine ⟨⟨Q, hQ.1, ?_⟩, hmem, rfl⟩
    intro hb
    rw [hb, Ideal.mem_bot] at hmem
    exact hl0 hmem
  have hpos : ∀ q ∈ (Finset.univ : Finset ((Ideal.span {((l : ℕ) : ℤ)}).primesOver (𝓞 K))),
      (fun _ => 1) q ≤ q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ := by
    intro q _
    exact Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (Ideal.ramificationIdx_pos (R := ℤ) q.1).ne' (Ideal.inertiaDeg_pos q.1 ℤ).ne')
  have hall := (Finset.sum_eq_sum_iff_of_le hpos).mp (by rw [hsum]; simp [hcard])
  have hw' := hall ⟨w.asIdeal, w.isPrime, liesOver_span_of_natCast_mem' l w.asIdeal hw⟩ (Finset.mem_univ _)
  exact mul_eq_one.mp hw'.symm

end K

section FE

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem locDeg_one_below (l : ℕ) [hl : Fact l.Prime]
    (h : {w : HeightOneSpectrum (𝓞 E) | ((l : ℕ) : 𝓞 E) ∈ w.asIdeal}.ncard = Module.finrank ℚ E)
    (p : HeightOneSpectrum (𝓞 F)) (hp : ((l : ℕ) : 𝓞 F) ∈ p.asIdeal) :
    p.asIdeal.ramificationIdx ℤ = 1 ∧ p.asIdeal.inertiaDeg ℤ = 1 := by
  haveI := p.isPrime
  obtain ⟨Q, -, hQ, hc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 E) p.asIdeal ⊥
    (by rw [(show Ideal.under _ ⊥ = ⊥ from Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _))]; exact bot_le)
  haveI := hQ
  haveI : Q.LiesOver p.asIdeal := ⟨hc.symm⟩
  have hQ0 : Q ≠ ⊥ := by
    intro hb
    apply p.ne_bot
    rw [← hc, hb]
    change Ideal.comap (algebraMap (𝓞 F) (𝓞 E)) ⊥ = ⊥
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
  have hw : ((l : ℕ) : 𝓞 E) ∈ Q := by
    rw [← hc] at hp
    simpa using Ideal.mem_comap.mp hp
  obtain ⟨he, hf⟩ := locDeg_one (K := E) l h ⟨Q, hQ, hQ0⟩ hw
  have he' := Ideal.ramificationIdx_tower (R := ℤ) p.asIdeal Q
  have hf' := Ideal.inertiaDeg_tower (R := ℤ) p.asIdeal Q
  exact ⟨(mul_eq_one.mp (he'.symm.trans he)).1, (mul_eq_one.mp (hf'.symm.trans hf)).1⟩

end FE

section Arith

variable {F : Type} [Field F] [NumberField F]

theorem arith_of_loc (l : ℕ) [hl : Fact l.Prime] (p : HeightOneSpectrum (𝓞 F))
    (hp : ((l : ℕ) : 𝓞 F) ∈ p.asIdeal) (he : p.asIdeal.ramificationIdx ℤ = 1)
    (hf : p.asIdeal.inertiaDeg ℤ = 1) :
    Nat.card (𝓞 F ⧸ p.asIdeal) = l ∧ ((l : ℕ) : 𝓞 F) ∉ p.asIdeal ^ 2 := by
  have hmaxl := Int.ideal_span_isMaximal_of_prime l
  haveI := p.isMaximal
  have hunder : Ideal.span {((l : ℕ) : ℤ)} = p.asIdeal.under ℤ := by
    refine hmaxl.eq_of_le (Ideal.IsPrime.ne_top (Ideal.IsPrime.under ℤ p.asIdeal)) ?_
    rw [Ideal.span_le, Set.singleton_subset_iff]
    show _ ∈ Ideal.comap (algebraMap ℤ (𝓞 F)) p.asIdeal
    rw [Ideal.mem_comap]
    simpa using hp
  haveI : p.asIdeal.LiesOver (Ideal.span {((l : ℕ) : ℤ)}) := ⟨hunder⟩
  constructor
  · have h := Ideal.cardQuot_pow_inertiaDeg (Ideal.span {((l : ℕ) : ℤ)}) p.asIdeal
    rw [hf, pow_one, Submodule.cardQuot_apply, Submodule.cardQuot_apply] at h
    rw [← h, Nat.card_congr (Int.quotientSpanNatEquivZMod l).toEquiv, Nat.card_zmod]
  · have hne : Ideal.span {((l : ℕ) : ℤ)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact_mod_cast hl.out.ne_zero
    have h1 : (Ideal.span {((l : ℕ) : ℤ)}).ramificationIdx' p.asIdeal = 1 := by
      rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ hne]
      exact he
    intro hmem
    have hle : Ideal.map (algebraMap ℤ (𝓞 F)) (Ideal.span {((l : ℕ) : ℤ)}) ≤ p.asIdeal ^ 2 := by
      rw [Ideal.map_span, Set.image_singleton, Ideal.span_le, Set.singleton_subset_iff]
      simpa using hmem
    unfold Ideal.ramificationIdx' at h1
    have hbdd : BddAbove {n | Ideal.map (algebraMap ℤ (𝓞 F)) (Ideal.span {((l : ℕ) : ℤ)}) ≤ p.asIdeal ^ n} := by
      by_contra hb
      rw [Nat.sSup_of_not_bddAbove hb] at h1
      exact zero_ne_one h1
    have h2 := le_csSup hbdd hle
    omega

end Arith

end Formalism.L2.SG.Pf.NcVal.VolUAr
end
end

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
  NumberField IsDedekindDomain
open scoped ENNReal TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace VolUT

section V

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem val_int (x : 𝓞 F) : Valued.v (algebraMap F (Fv F v) (x : F)) ≤ 1 := by
  have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 F) v (algebraMap (𝓞 F) F x)
  rw [HeightOneSpectrum.valuation_of_algebraMap] at h
  have h' : Valued.v (algebraMap F (Fv F v) (x : F)) = v.intValuation x := h
  rw [h']
  exact v.intValuation_le_one x

theorem val_unit (x : 𝓞 F) (hx : x ∉ v.asIdeal) : Valued.v (algebraMap F (Fv F v) (x : F)) = 1 := by
  have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 F) v (algebraMap (𝓞 F) F x)
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.2 hx] at h
  exact h

theorem val_dV (h : ¬ (differentIdeal ℤ (𝓞 F) ≤ v.asIdeal)) : Valued.v (dV v) = 1 := by
  obtain ⟨y, hy, hyv⟩ := Set.not_subset.1 h
  unfold dV
  split_ifs with hd
  · obtain ⟨-, hle, x, hx, hxe⟩ := hd.choose_spec
    have h1 := hle y hy
    rw [val_unit v y hyv] at h1
    rw [← hxe] at h1 ⊢
    exact le_antisymm (val_int v x) h1
  · exact map_one _

theorem absV_of_val_one {x : Fv F v} (h : Valued.v x = 1) : absV v x = 1 := by
  unfold absV
  rw [dite_eq_right (by rw [h]; exact one_ne_zero)]
  have : WithZero.unzero (show Valued.v x ≠ 0 by rw [h]; exact one_ne_zero) = 1 := by
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero, h]
    rfl
  rw [this]
  simp

theorem absV_g (g : ℕ) (hcard : Nat.card (𝓞 F ⧸ v.asIdeal) = g) (hg1 : (g : 𝓞 F) ∈ v.asIdeal)
    (hg2 : (g : 𝓞 F) ∉ v.asIdeal ^ 2) : absV v (g : Fv F v) = (g : ℝ)⁻¹ := by
  have hv := VolUAr.val_natCast_of v g hg1 hg2
  have e1 : ((g : v.adicCompletionIntegers F) : v.adicCompletion F) = (g : Fv F v) := by simp
  rw [e1] at hv
  unfold absV
  rw [dite_eq_right (by rw [hv]; exact WithZero.coe_ne_zero)]
  have hu : WithZero.unzero (show Valued.v (g : Fv F v) ≠ 0 by rw [hv]; exact WithZero.coe_ne_zero) =
      Multiplicative.ofAdd (-1 : ℤ) := by
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero, hv]
    rfl
  rw [hu, toAdd_ofAdd, Ideal.absNorm_apply, Submodule.cardQuot_apply, hcard, zpow_neg, zpow_one]

end V

section X

variable {D : D7} (X : HidaSetting D)

theorem gAt_mem (v : PlX X) (hv : TypAt X v) : ((gAt X v : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal := by
  have hty := (mem_typSet X.B.I.F (D.host.g 0) (D.host.g 1) (D.host.g_prime 0).ne_zero
    (D.host.g_prime 1).ne_zero v).1 hv
  unfold gAt
  split_ifs with h
  · exact h
  · exact hty.resolve_left h

theorem gAt_split (v : PlX X) : {w : HeightOneSpectrum (𝓞 X.B.I.E) |
    ((gAt X v : ℕ) : 𝓞 X.B.I.E) ∈ w.asIdeal}.ncard = Module.finrank ℚ X.B.I.E := by
  unfold gAt
  split_ifs
  · exact VolUAr.split_transport X.ιE _ (D.nd.g_split 0)
  · exact VolUAr.split_transport X.ιE _ (D.nd.g_split 1)

theorem typ_arith (v : PlX X) (hv : TypAt X v) :
    absV v (gAt X v : Fv X.B.I.F v) = (gAt X v : ℝ)⁻¹ ∧ Valued.v (dV v) = 1 ∧ absV v (dV v) = 1 := by
  haveI : Fact (gAt X v).Prime := ⟨gAt_prime X v⟩
  have hmem := gAt_mem X v hv
  obtain ⟨he, hf⟩ := VolUAr.locDeg_one_below (F := X.B.I.F) (E := X.B.I.E) (gAt X v) (gAt_split X v) v hmem
  obtain ⟨hc, hn⟩ := VolUAr.arith_of_loc (gAt X v) v hmem he hf
  have hun : Algebra.IsUnramifiedAt ℤ v.asIdeal :=
    (Algebra.isUnramifiedAt_iff_of_isDedekindDomain (R := ℤ) (S := 𝓞 X.B.I.F) (p := v.asIdeal)).2 he
  have hnd : ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 X.B.I.F) := not_dvd_differentIdeal_iff.mpr hun
  rw [Ideal.dvd_iff_le] at hnd
  have hval := val_dV v hnd
  exact ⟨absV_g v (gAt X v) hc hmem hn, hval, absV_of_val_one v hval⟩

end X

end VolUT

section OfX

variable {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem volU_steps_of (hC : CondAll) (hψ : IsCharAF X.B.I.F ψ) (hs : IsStdChar ψ) (v : PlX X) (hv : TypAt X v)
    (hH : VolTHermCnt X.B.I.cm.sig ψ v (gAt X v) D.R.rS) (hT : VolTTFCong X u u' v) : VolUSteps X u u' ψ v := by
  obtain ⟨hg, hdv, hd⟩ := VolUT.typ_arith X v hv
  have hann : VolUL.AnnAt (E := X.B.I.E) ψ v := VolUTr.annX_of X ψ hC hψ hs v
  have hfin := X.B.I.cm.deg2
  have hg0 : gAt X v ≠ 0 := (gAt_prime X v).ne_zero
  exact ⟨VolUL.volTAff_of ψ v hψ hfin hann hd hg0 hg _, VolUL.volTLocPres_of ψ v hψ hfin hann hd _, hH, hT,
    volTUOEq_of v hdv hg0 _, VolUL.volTProdU_of' ψ v hψ hfin hann hd hg0 hg _,
    (VolUL.sd_facts ψ v hψ hfin hann hd _).2.2⟩

theorem volTypV_of_cnt (hC : CondAll)
    (hH : VolUHyp X u u' ψ → ∀ v, TypAt X v → VolTHermCnt X.B.I.cm.sig ψ v (gAt X v) D.R.rS)
    (hT : VolUHyp X u u' ψ → ∀ v, TypAt X v → VolTTFCong X u u' v) : VolTypV X u u' ψ :=
  volTypV_of_steps' X u u' ψ fun hh v hv =>
    volU_steps_of X u u' ψ hC hh.1 hh.2.1 v hv (hH hh v hv) (hT hh v hv)

end OfX

end Formalism.L2.SG.Pf.NcVal
