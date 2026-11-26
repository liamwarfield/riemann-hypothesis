module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsReductionActionChosenPlaces
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothVectorsDenseInvariant
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsometryOfUnimodularLatticesAtPlace
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SymmMemOfMem
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SameRowSameCosetScalarCorankOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LandherrHasse
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IotaDictAll

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmFieldSplitPlaceEqOfPlaceEq
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmFieldSplitPlaceEqOfPlaceEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

noncomputable section

namespace GlobalTheory.SplitUniq

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

theorem le_one_iff_frac {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (ν : Valuation K Γ) (P : Ideal R)
    [P.IsPrime] (hP0 : P ≠ ⊥) (hle : ∀ r : R, ν (algebraMap R K r) ≤ 1)
    (hlt : ∀ r : R, ν (algebraMap R K r) < 1 ↔ r ∈ P) (x : K) :
    ν x ≤ 1 ↔ ∃ y s : R, s ∉ P ∧ x = algebraMap R K y / algebraMap R K s := by
  have hunit : ∀ s : R, s ∉ P → ν (algebraMap R K s) = 1 := fun s hs =>
    le_antisymm (hle s) (not_lt.mp fun h => hs ((hlt s).1 h))
  constructor
  · intro hx
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := R) x
    have hq0 : algebraMap R K q ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hq
    haveI := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R hP0 (Localization.AtPrime P)
    have hinj : Function.Injective (algebraMap R (Localization.AtPrime P)) :=
      IsLocalization.injective (Localization.AtPrime P) P.primeCompl_le_nonZeroDivisors
    have key : ∀ a b : R, ∀ (y : R) (s : P.primeCompl),
        algebraMap R (Localization.AtPrime P) a * IsLocalization.mk' (Localization.AtPrime P) y s =
          algebraMap R (Localization.AtPrime P) b → a * y = b * s := by
      intro a b y s h
      apply hinj
      have h2 := congrArg (· * algebraMap R (Localization.AtPrime P) (s : R)) h
      simp only [mul_assoc, IsLocalization.mk'_spec] at h2
      simpa [map_mul] using h2
    obtain ⟨c, hc⟩ := ValuationRing.cond (algebraMap R (Localization.AtPrime P) p)
      (algebraMap R (Localization.AtPrime P) q)
    obtain ⟨⟨y, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl c
    rcases hc with hc | hc
    ·
      have e := key p q y s hc
      by_cases hy : y ∈ P
      · by_cases hp : p = 0
        · exact ⟨0, 1, P.ne_top_iff_one.mp (Ideal.IsPrime.ne_top inferInstance), by simp [hp]⟩
        · exfalso
          have hp0 : ν (algebraMap R K p) ≠ 0 := by
            rw [Valuation.ne_zero_iff]
            exact (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hp
          have hq' : ν (algebraMap R K q) ≠ 0 := (Valuation.ne_zero_iff _).mpr hq0
          have e2 : ν (algebraMap R K p) * ν (algebraMap R K y) = ν (algebraMap R K q) := by
            rw [← map_mul, ← map_mul, e, map_mul, map_mul, hunit _ s.2, mul_one]
          rw [map_div₀, div_le_one₀ (zero_lt_iff.mpr hq')] at hx
          have : ν (algebraMap R K p) * ν (algebraMap R K y) < ν (algebraMap R K p) * 1 :=
            mul_lt_mul_of_pos_left ((hlt y).2 hy) (zero_lt_iff.mpr hp0)
          rw [e2, mul_one] at this
          exact absurd hx (not_le.mpr this)
      · refine ⟨s, y, hy, ?_⟩
        have hy0 : algebraMap R K y ≠ 0 := by
          intro h0
          apply hy
          rw [(map_eq_zero_iff _ (IsFractionRing.injective R K)).mp h0]
          exact P.zero_mem
        rw [div_eq_div_iff hq0 hy0, ← map_mul, ← map_mul, e, mul_comm]
    ·
      have e := key q p y s hc
      refine ⟨y, s, s.2, ?_⟩
      have hs0 : algebraMap R K (s : R) ≠ 0 := by
        intro h0
        apply s.2
        rw [(map_eq_zero_iff _ (IsFractionRing.injective R K)).mp h0]
        exact P.zero_mem
      rw [div_eq_div_iff hq0 hs0, ← map_mul, ← map_mul, ← e, mul_comm]
  · rintro ⟨y, s, hs, rfl⟩
    rw [map_div₀, hunit s hs, div_one]
    exact hle y

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

local notation3 "L⁺" => NumberField.maximalRealSubfield L

theorem exists_approx (v : HeightOneSpectrum (𝓞 L⁺)) (y d : v.adicCompletion L⁺) (hd : d ≠ 0) :
    ∃ a : L⁺, Valued.v (y - algebraMap L⁺ (v.adicCompletion L⁺) a) < Valued.v d := by
  have hU : IsOpen {z : v.adicCompletion L⁺ | Valued.v (z - y) < Valued.v d} := by
    have h := (Valued.isOpen_ball (v.adicCompletion L⁺) (Valued.v.restrict d)).preimage (continuous_sub_right y)
    convert h using 2 with z
    simp [Valuation.restrict_lt_iff]
  have hy : y ∈ {z : v.adicCompletion L⁺ | Valued.v (z - y) < Valued.v d} := by
    simp only [Set.mem_setOf_eq, sub_self, map_zero]
    exact zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hd)
  obtain ⟨z, hz, a, rfl⟩ := mem_closure_iff_nhds.mp (denseRange_algebraMap L⁺ v y) _ (hU.mem_nhds hy)
  refine ⟨a, ?_⟩
  rw [← Valuation.map_neg, neg_sub]
  exact hz

theorem eq_of_le_one_iff (v : HeightOneSpectrum (𝓞 L⁺)) (i i' : L →ₐ[L⁺] v.adicCompletion L⁺)
    (h : ∀ x : L, Valued.v (i x) ≤ 1 ↔ Valued.v (i' x) ≤ 1) : i = i' := by
  refine AlgHom.ext fun x => ?_
  by_contra hne
  set δ := i x - i' x with hδ
  have hδ0 : Valued.v δ ≠ 0 := (Valuation.ne_zero_iff _).mpr (sub_ne_zero.mpr hne)
  obtain ⟨a, ha⟩ := exists_approx v (i x) δ (sub_ne_zero.mpr hne)
  obtain ⟨b, hb⟩ := exists_approx v δ δ (sub_ne_zero.mpr hne)
  set b' := algebraMap L⁺ (v.adicCompletion L⁺) b
  set a' := algebraMap L⁺ (v.adicCompletion L⁺) a
  have hbv : Valued.v b' = Valued.v δ := by
    have : b' = δ - (δ - b') := by ring
    rw [this, Valuation.map_sub_eq_of_lt_left _ hb]
  have hb0 : Valued.v b' ≠ 0 := hbv ▸ hδ0
  have hbne : b' ≠ 0 := (Valuation.ne_zero_iff _).mp hb0
  set z : L := (x - algebraMap L⁺ L a) / algebraMap L⁺ L b
  have hiz : i z = (i x - a') / b' := by simp [z, a', b', map_div₀, map_sub, AlgHom.commutes]
  have hi'z : i' z = (i' x - a') / b' := by simp [z, a', b', map_div₀, map_sub, AlgHom.commutes]
  have hlt : Valued.v (i z) < 1 := by
    rw [hiz, map_div₀, div_lt_one₀ (zero_lt_iff.mpr hb0), hbv]
    exact ha
  have heq : Valued.v (i' z) = 1 := by
    have : i' x - a' = (i x - a') - δ := by rw [hδ]; ring
    rw [hi'z, map_div₀, this, Valuation.map_sub_eq_of_lt_right _ ha, hbv, div_self hδ0]
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0, map_zero, map_zero] at heq
    exact zero_ne_one heq
  have hinv : Valued.v (i' z⁻¹) ≤ 1 := by rw [map_inv₀, map_inv₀, heq, inv_one]
  have h2 := (h z⁻¹).2 hinv
  have h3 : Valued.v (i z) * Valued.v (i z⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ hz0, map_one, map_one]
  have h4 : Valued.v (i z) * Valued.v (i z⁻¹) < 1 := mul_lt_one_of_lt_of_le hlt h2
  rw [h3] at h4
  exact lt_irrefl _ h4

theorem splitPlace_eq_of_w_eq : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L]
    (s s' : ReciprocityTheory.Aut.SplitPlace L), s.w = s'.w → s = s' := by
  intro L _ _ _ s s' h
  have hv : s.v = s'.v := by
    apply HeightOneSpectrum.ext
    rw [← s.w_under, ← s'.w_under, h]
  have hid : s.ideal = s'.ideal := congrArg HeightOneSpectrum.asIdeal h
  obtain ⟨v, i⟩ := s
  obtain ⟨v', i'⟩ := s'
  simp only at hv
  subst hv
  congr 1
  haveI : (ReciprocityTheory.Aut.SplitPlace.ideal ⟨v, i⟩).IsPrime := ReciprocityTheory.Aut.SplitPlace.ideal_isPrime _
  have hP0 := ReciprocityTheory.Aut.SplitPlace.ideal_ne_bot (⟨v, i⟩ : ReciprocityTheory.Aut.SplitPlace L)
  have H := fun (j : L →ₐ[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L))
      (hj : ReciprocityTheory.Aut.SplitPlace.ideal ⟨v, j⟩ = ReciprocityTheory.Aut.SplitPlace.ideal ⟨v, i⟩) (x : L) =>
    le_one_iff_frac (R := 𝓞 L) (Valued.v.comap (j : L →+* v.adicCompletion (maximalRealSubfield L)))
      (ReciprocityTheory.Aut.SplitPlace.ideal ⟨v, i⟩) hP0
      (fun r => ReciprocityTheory.Aut.SplitPlace.split_le_one ⟨v, j⟩ r)
      (fun r => by rw [← hj]; exact (ReciprocityTheory.Aut.SplitPlace.split_mem_ideal ⟨v, j⟩ r).symm) x
  apply eq_of_le_one_iff v i i'
  intro x
  have h1 := H i rfl x
  have h2 := H i' hid.symm x
  simp only [Valuation.comap_apply] at h1 h2
  exact h1.trans h2.symm

end GlobalTheory.SplitUniq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmFieldSplitPlaceEqOfPlaceEqStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmField_splitPlace_eq_of_place_eq : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s s' : ReciprocityTheory.Aut.SplitPlace L), s.w = s'.w → s = s' := by
  first | exact @GlobalTheory.SplitUniq.splitPlace_eq_of_w_eq | exact GlobalTheory.SplitUniq.splitPlace_eq_of_w_eq | (intros; apply GlobalTheory.SplitUniq.splitPlace_eq_of_w_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSplitPlaceEqFixedTypePrimePlace
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSplitPlaceEqFixedTypePrimePlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

namespace GlobalTheory.SplitPlaceOfFixed

theorem exists_splitPlace_plGw : ∀ (D : D7) (kv : Σ k : Fin 2, D.nd.PlG k), ∃ s : ReciprocityTheory.Aut.SplitPlace D.host.E, s.w = D.naut.plGw kv.1 kv.2 := by
  intro D kv
  obtain ⟨s, -, h, -⟩ := GlobalTheory.SplitConjPlace.splitEx_all D _ (GlobalTheory.FixedPlaceSplit.isSplitPl_plGw D kv.1 kv.2)
  refine ⟨GlobalTheory.SplitConjPlace.conjSP s, IsDedekindDomain.HeightOneSpectrum.ext (Ideal.ext fun x => ?_)⟩
  have hm : x ∈ (GlobalTheory.SplitConjPlace.conjSP s).w.asIdeal ↔
      IsCMField.ringOfIntegersComplexConj D.host.E x ∈ s.w.asIdeal := by
    show Valued.v ((GlobalTheory.SplitConjPlace.conjSP s).i (x : D.host.E)) < 1 ↔
      Valued.v (s.i ((IsCMField.ringOfIntegersComplexConj D.host.E x : 𝓞 D.host.E) : D.host.E)) < 1
    rw [IsCMField.coe_ringOfIntegersComplexConj]
    rfl
  rw [hm]
  refine (h x _ ?_).symm
  rw [IsCMField.coe_ringOfIntegersComplexConj]
  exact D.host.φ₀.injective (by
    rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply])

end GlobalTheory.SplitPlaceOfFixed
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSplitPlaceEqFixedTypePrimePlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_splitPlace_eq_fixedTypePrimePlace : ∀ (D : D7) (kv : Σ k : Fin 2, D.nd.PlG k), ∃ s : ReciprocityTheory.Aut.SplitPlace D.host.E, s.w = D.naut.plGw kv.1 kv.2 := by
  first | exact @GlobalTheory.SplitPlaceOfFixed.exists_splitPlace_plGw | exact GlobalTheory.SplitPlaceOfFixed.exists_splitPlace_plGw | (intros; apply GlobalTheory.SplitPlaceOfFixed.exists_splitPlace_plGw <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SwxsOfSiegelWeil
namespace GlobalTheory.St

theorem swxs_of_siegelWeil :
    HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → PI.VolStabS.MassDataS.SWXS :=
  fun h _ X => GlobalTheory.St.siegelWeil_volumes h _ _ _ (MassDataVolumesW.stepCM X) _ _ (MassDataVolumesW.stepHerm X)

end GlobalTheory.St
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.WBEqPrimeComap
noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.FixedConj

def adeleEquiv (D : Formalism.BasicNotions.D7) (hF : D.host.F = maximalRealSubfield D.host.E) :
    ReciprocityTheory.Aut.AL D.host.E ≃+* Formalism.IndefR.Lev.EAf D :=
  (GlobalTheory.StdFrame.tensCastR hF).symm.trans
    (Algebra.TensorProduct.comm (↥D.host.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af ↥D.host.F) D.host.E).toRingEquiv

def primeComap {E E' : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] (ι : E ≃+* E')
    (w : HeightOneSpectrum (𝓞 E')) : HeightOneSpectrum (𝓞 E) where
  asIdeal := Ideal.comap (RingOfIntegers.mapRingEquiv ι) w.asIdeal
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    intro h
    apply w.ne_bot
    have := congrArg (Ideal.map (RingOfIntegers.mapRingEquiv ι)) h
    rwa [Ideal.map_comap_of_surjective _ (RingOfIntegers.mapRingEquiv ι).surjective, Ideal.map_bot] at this

end GlobalTheory.FixedConj

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFiniteAdelicPointLatticeEqSelfDual
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFiniteAdelicPointLatticeEqSelfDual
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.SelfDualPoint

open Formalism.HermitianLatticesTheory Formalism.UG Formalism.UG.CS

theorem mem_genus {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hK : IsCMUnram K) (hs : h.IsSymm) (hn : h.Nondegenerate) {L L' : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hL' : Submodule.IsLattice K L') (hd : dual h L = L) (hd' : dual h L' = L') :
    L' ∈ genus h L := by
  have hstar : ∀ r : 𝓞 K, star (algebraMap (𝓞 K) K r) ∈ Set.range (algebraMap (𝓞 K) K) :=
    fun r => ⟨RingOfIntegers.mapRingHom (starRingEnd K) r, rfl⟩
  have key : ∀ M : Submodule (𝓞 K) V, M.FG → dual h M = M → ∀ P : Ideal (𝓞 K), P.IsPrime →
      IsUnimodularAt h P M := fun M hM hdM P hP => by
    have a := (locDual (𝓞 K) K V h hs hstar M hM).1 P hP
    have b := a.2.trans a.1.symm
    rwa [hdM] at b
  have full : ∀ M : Submodule (𝓞 K) V, Submodule.IsLattice K M → dual h M = M →
      Submodule.IsFullLattice K M := by
    intro M hM hdM
    classical
    let b := Module.finBasis K V
    let B : Submodule (𝓞 K) V := Submodule.span (𝓞 K) (Set.range b)
    let N := M ⊔ B
    have hNfg : N.FG := hM.fg.sup (Submodule.fg_span (Set.finite_range b))
    have hNspan : Submodule.span K (N : Set V) = ⊤ := by
      apply eq_top_iff.mpr
      rw [← b.span_eq]
      apply Submodule.span_mono
      rintro x ⟨i, rfl⟩
      exact (show B ≤ N from le_sup_right) (Submodule.subset_span ⟨i, rfl⟩)
    have hN : Submodule.IsFullLattice K N :=
      { toIsLattice := Submodule.IsLattice.of_fg K hNfg, span_eq_top := hNspan }
    have hNd := (Formalism.HermitianLatticesTheory.dualLattice (𝓞 K) K V h hs hn hstar N hN).1
    have hle : dual h N ≤ M := by
      rw [← hdM]
      exact (dualBasic (𝓞 K) K V h hs hstar).1 M N le_sup_left
    letI : Submodule.IsFullLattice K (dual h N) := hNd
    letI : Submodule.IsLattice K M := hM
    exact Submodule.IsFullLattice.of_le K hle
  have hLf := full L hL hd
  have hL'f := full L' hL' hd'
  exact ⟨hL'f, fun P hP => GlobalTheory.Mass.UnimodLoc.exists_isom_of_isUnimodularAt K V h hK hs hn L L' hLf hL'f P hP
    (key L hL.fg hd P hP.isPrime) (key L' hL'.fg hd' P hP.isPrime)⟩

theorem lamX_eq_globLat (I : AutInst) (xf : I.Gf) : lamX I (1, xf) = globLat xf.1 I.L := by
  have e : I.Lf = latS (F := I.F) (Af I.F) (IntAf I.F I.E) I.L := by
    unfold AutInst.Lf lamAf latS
    congr 1
    ext u
    exact ⟨fun ⟨x, hx⟩ => ⟨x, x.2, hx⟩, fun ⟨x, hx, hx'⟩ => ⟨⟨x, hx⟩, hx'⟩⟩
  unfold lamX
  rw [e]
  exact Submodule.span_eq (globLat xf.1 I.L)

theorem exists_lamX_eq : ∀ (I : AutInst) (Λ : Submodule (𝓞 I.E) (Fin I.n → I.E)), Submodule.IsLattice I.E Λ → (∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, Formalism.UG.hform (starRingEnd I.E) I.J y x ∈ (algebraMap (𝓞 I.E) I.E).range) → ∃ xf : I.Gf, lamX I (1, xf) = Λ := by
  intro I Λ hΛ hd
  have hs : ∀ e, (I.cm.sig : I.E →+* I.E) ((I.cm.sig : I.E →+* I.E) e) = e := fun e => star_star e
  have hfix : ∀ e : I.E, I.cm.sig e = e → ∃ a : I.F, algebraMap I.F I.E a = e := fun e he => (I.cm.fixed e).1 he
  let h : (Fin I.n → I.E) →ₗ⋆[I.E] (Fin I.n → I.E) →ₗ[I.E] I.E := formJ (I.cm.sig : I.E →+* I.E) hs I.J 1
  obtain ⟨hsym, hap⟩ := Formalism.UG.P.hermitian_form_symmetry_holds I.E _ hs (Fin I.n) I.J 1 (map_one _) I.J_herm
  replace hsym : h.IsSymm := hsym
  replace hap : ∀ x y, h x y = hform (starRingEnd I.E) I.J x y := fun x y => (hap x y).trans (one_mul _)
  have hr : ∀ y, (∀ x, h x y = 0) → y = 0 := fun y hy => by
    refine Matrix.eq_zero_of_mulVec_eq_zero I.J_det (funext fun i => ?_)
    have := hy (Pi.single i 1)
    rw [hap, hform, Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (by simp)] at this
    simpa [Matrix.mulVec, dotProduct] using this
  have hn : h.Nondegenerate := ⟨fun x hx => hr x fun y => by rw [← hsym.eq, hx, map_zero], hr⟩
  have hdual : ∀ M : Submodule (𝓞 I.E) (Fin I.n → I.E),
      (∀ x, x ∈ M ↔ ∀ y ∈ M, hform (starRingEnd I.E) I.J y x ∈ (algebraMap (𝓞 I.E) I.E).range) →
      dual h M = M := fun M hM => by
    ext x
    rw [dualBasic_mem_dual, hM x]
    simp only [hap, Submodule.mem_one, RingHom.mem_range]
  obtain ⟨g, hg, e⟩ := GlobalTheory.Mass.Genus.exists_globLat_eq (J := I.J) hs hfix (Module.Finite.iff_fg.2 I.L_fg)
    I.L_span Λ (mem_genus h I.cm.cmUnram hsym hn (Submodule.IsLattice.of_fg I.E I.L_fg) hΛ (hdual _ I.L_dual) (hdual _ hd))
  exact ⟨⟨g, hg⟩, (lamX_eq_globLat I _).trans e⟩

end GlobalTheory.SelfDualPoint
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFiniteAdelicPointLatticeEqSelfDualStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteAdelicPoint_lattice_eq_selfDual : ∀ (I : AutInst) (Λ : Submodule (𝓞 I.E) (Fin I.n → I.E)), Submodule.IsLattice I.E Λ → (∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, Formalism.UG.hform (starRingEnd I.E) I.J y x ∈ (algebraMap (𝓞 I.E) I.E).range) → ∃ xf : I.Gf, lamX I (1, xf) = Λ := by
  first | exact @GlobalTheory.SelfDualPoint.exists_lamX_eq | exact GlobalTheory.SelfDualPoint.exists_lamX_eq | (intros; apply GlobalTheory.SelfDualPoint.exists_lamX_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagTermInvariantsConstOnRationalDoubleCoset
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagTermInvariantsConstOnRationalDoubleCoset
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp
  Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HL.CosetConst

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem mem_orth_iff' {U : Submodule E S.V} {v : S.V} : v ∈ orth S U ↔ ∀ x ∈ U, S.hT x v = 0 := by
  simp [orth, Submodule.mem_iInf]

theorem frame_mapLF {T : E} {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T)
    (a : Fin (r + 1)) : frame (mapLF γ F) a = γ (frame F a) := by
  unfold mapLF; rw [dite_eq_left hγ]
  induction a using Fin.lastCases with
  | last => simp [frame, FlagG.fvec, mapFlag]
  | cast i => simp [frame, FlagG.fvec, mapFlag]

theorem zt_mapLF {T : E} {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) :
    (mapLF γ F).zt = γ F.zt := by
  unfold mapLF; rw [dite_eq_left hγ]

theorem Xflag_mapLF {T : E} {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) (j : ℕ) :
    Xflag (mapLF γ F) j = (Xflag F j).map (γ : S.V →ₗ[E] S.V) := by
  unfold mapLF; rw [dite_eq_left hγ]
  show Submodule.span E ((fun a => γ (F.fl.e a)) '' {i | i.1 < j}) =
    (Submodule.span E (F.fl.e '' {i | i.1 < j})).map (γ : S.V →ₗ[E] S.V)
  rw [Submodule.map_span, Set.image_image]
  rfl

theorem Xsp_mapLF {T : E} {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) :
    Xsp (mapLF γ F) = (Xsp F).map (γ : S.V →ₗ[E] S.V) := by
  unfold mapLF; rw [dite_eq_left hγ]
  show Submodule.span E (Set.range fun a => γ (F.fl.e a)) =
    (Submodule.span E (Set.range F.fl.e)).map (γ : S.V →ₗ[E] S.V)
  rw [Submodule.map_span, ← Set.range_comp]
  rfl

theorem gmap_top (γ : S.V ≃ₗ[E] S.V) : Formalism.HermitianLatticesTheory.gmap γ (⊤ : Submodule (𝓞 E) S.V) = ⊤ := by
  unfold Formalism.HermitianLatticesTheory.gmap
  rw [Submodule.map_top, LinearMap.range_eq_top]
  intro y
  exact ⟨γ.symm y, by simp⟩

end Gen

section D

variable {D : D7}

theorem nlam_top_of_nrat {T : D.host.E} {F : LFlag (D.sp.Y 0) D.R.rS T} {n : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hn : n ∈ NRat F) : n ∈ NLam (⊤ : Submodule (𝓞 D.host.E) (VS D).V) F :=
  ⟨⟨hn.1, gmap_top n⟩, hn.2.1, hn.2.2⟩

theorem conj_nlam_top {T : D.host.E} {G : LFlag (D.sp.Y 0) D.R.rS T} {γ m : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (hm : m ∈ NRat G) :
    γ * m * γ⁻¹ ∈ NLam (⊤ : Submodule (𝓞 D.host.E) (VS D).V) (mapLF γ G) := by
  obtain ⟨hi, hf, hp⟩ := hm
  have happ : ∀ y, (γ * m * γ⁻¹) (γ y) = γ (m y) := fun y => by
    show γ (m (γ.symm (γ y))) = γ (m y)
    rw [γ.symm_apply_apply]
  refine ⟨⟨(Formalism.HermitianLatticesTheory.isom _).mul_mem ((Formalism.HermitianLatticesTheory.isom _).mul_mem hγ hi) ((Formalism.HermitianLatticesTheory.isom _).inv_mem hγ),
    gmap_top _⟩, ?_, ?_⟩
  · intro j x hx
    rw [Xflag_mapLF hγ] at hx ⊢
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hx
    have e : (γ * m * γ⁻¹) ((γ : (VS D).V →ₗ[D.host.E] (VS D).V) y) - (γ : (VS D).V →ₗ[D.host.E] (VS D).V) y =
        (γ : (VS D).V →ₗ[D.host.E] (VS D).V) (m y - y) := by
      rw [map_sub]
      exact congrArg (· - _) (happ y)
    rw [e]
    exact Submodule.mem_map_of_mem (hf j y hy)
  · intro x hx
    have hXs := Xsp_mapLF hγ G
    have hy : γ.symm x ∈ orth (VS D) (Xsp G) := by
      rw [mem_orth_iff'] at hx ⊢
      intro w hw
      have h1 := hx (γ w) (by rw [hXs]; exact Submodule.mem_map_of_mem hw)
      have h2 := hγ w (γ.symm x)
      rw [γ.apply_symm_apply] at h2
      rw [← h2]
      exact h1
    have h3 := hp _ hy
    have e : (γ * m * γ⁻¹) x - x = (γ : (VS D).V →ₗ[D.host.E] (VS D).V) (m (γ.symm x) - γ.symm x) := by
      show γ (m (γ.symm x)) - x = γ (m (γ.symm x) - γ.symm x)
      rw [map_sub, γ.apply_symm_apply]
    rw [e, hXs]
    exact Submodule.mem_map_of_mem h3

end D

end GlobalTheory.HL.CosetConst

namespace GlobalTheory.HL.CosetConst

section Terms

variable {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word}

theorem dcrel_of_coset (t₀ t : TauC Y u u') {n m : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hn : n ∈ NRat (lf D (X.Fu u))) (hm : m ∈ NRat (lf D (X.Fu u'))) (h : t.lin = n⁻¹ * t₀.lin * m) :
    Formalism.L2.SG.TermDef.DCRel (⊤ : Submodule (𝓞 D.host.E) (VS D).V) (lf D (X.Fu u)) t₀.frame t.frame := by
  have h0 : t₀.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t₀.rep.2.2.1
  have h1 : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  have hn' : n⁻¹ ∈ NRat (lf D (X.Fu u)) := Formalism.L2.SG.NGCut.NormalVectorPairings.NRat_inv _ hn
  refine ⟨n⁻¹, nlam_top_of_nrat hn', t₀.lin * m * t₀.lin⁻¹, conj_nlam_top h0 hm, fun a => ?_, ?_⟩
  · show frame (mapLF t.lin (lf D (X.Fu u'))) a =
      n⁻¹ ((t₀.lin * m * t₀.lin⁻¹) (frame (mapLF t₀.lin (lf D (X.Fu u'))) a))
    rw [frame_mapLF h1, frame_mapLF h0, h]
    show n.symm (t₀.lin (m _)) = n.symm (t₀.lin (m (t₀.lin.symm (t₀.lin _))))
    rw [LinearEquiv.symm_apply_apply]
  · show (mapLF t.lin (lf D (X.Fu u'))).zt =
      n⁻¹ ((t₀.lin * m * t₀.lin⁻¹) (mapLF t₀.lin (lf D (X.Fu u'))).zt)
    rw [zt_mapLF h1, zt_mapLF h0, h]
    show n.symm (t₀.lin (m _)) = n.symm (t₀.lin (m (t₀.lin.symm (t₀.lin _))))
    rw [LinearEquiv.symm_apply_apply]

theorem relevant_iff (s : TauC Y u u') :
    s.relevant ↔ Relevant D.host.F (lf D (X.Fu u)).fl s.frame.fl :=
  Formalism.L2.SG.TermDef.isRel_mk D.host.F
    (PI.TermAttrConst.UnitaryGroupMassFormula.relFun_all D.host.F s.lam (lf D (X.Fu u))
      (Formalism.L2.SG.TermDef.PD D s.lam (lf D (X.Fu u)) u')) ⟨s.frame, s.rep.2.2.2.2⟩

theorem atPt_iff (s : TauC Y u u') (w : Point D.host.E (D.R.rS + 1)) :
    s.toTerm.atPt w ↔ Gval (lf D (X.Fu u)) s.frame ≠ 0 ∧
      IsInCell (ZhatOM (ZhatL (lf D (X.Fu u)) s.frame)) w :=
  Formalism.L2.SG.TermDef.atPt_mk (PI.TermAttrConst.UnitaryGroupMassFormula.gFun_all _ _ _) (PI.TermAttrConst.UnitaryGroupMassFormula.cellFun_all _ _ _)
    ⟨s.frame, s.rep.2.2.2.2⟩ w

end Terms

end GlobalTheory.HL.CosetConst

namespace GlobalTheory.HL.CosetConst

variable {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word}

theorem nml_eq (t₀ t : TauC Y u u') {n m : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hn : n ∈ NRat (lf D (X.Fu u))) (hm : m ∈ NRat (lf D (X.Fu u'))) (h : t.lin = n⁻¹ * t₀.lin * m) :
    nmlOf Y u u' t = nmlOf Y u u' t₀ := by
  have hni : n⁻¹ ∈ NRat (lf D (X.Fu u)) := Formalism.L2.SG.NGCut.NormalVectorPairings.NRat_inv _ hn
  have hmi : m⁻¹ ∈ NRat (lf D (X.Fu u')) := Formalism.L2.SG.NGCut.NormalVectorPairings.NRat_inv _ hm
  ext δ
  simp only [nmlOf, Set.mem_setOf_eq]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨a * n⁻¹, Formalism.L2.SG.NGCut.NormalVectorPairings.NRat_mul _ ha hni, m * b,
      Formalism.L2.SG.NGCut.NormalVectorPairings.NRat_mul _ hm hb, ?_⟩
    rw [h]; simp only [mul_assoc, inv_mul_cancel_left]
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨a * n, Formalism.L2.SG.NGCut.NormalVectorPairings.NRat_mul _ ha hn, m⁻¹ * b,
      Formalism.L2.SG.NGCut.NormalVectorPairings.NRat_mul _ hmi hb, ?_⟩
    rw [h]; simp only [mul_assoc, mul_inv_cancel_left]

theorem G_eq_frames (t₀ t : TauC Y u u') {n m : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hn : n ∈ NRat (lf D (X.Fu u))) (hm : m ∈ NRat (lf D (X.Fu u'))) (h : t.lin = n⁻¹ * t₀.lin * m) :
    Gval (lf D (X.Fu u)) t₀.frame = Gval (lf D (X.Fu u)) t.frame :=
  PI.TermAttrConst.UnitaryGroupMassFormula.gFun_all (⊤ : Submodule (𝓞 D.host.E) (VS D).V) (lf D (X.Fu u))
    (fun _ => True) ⟨t₀.frame, trivial⟩ ⟨t.frame, trivial⟩ (dcrel_of_coset t₀ t hn hm h)

theorem cell_iff_frames (t₀ t : TauC Y u u') {n m : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hn : n ∈ NRat (lf D (X.Fu u))) (hm : m ∈ NRat (lf D (X.Fu u'))) (h : t.lin = n⁻¹ * t₀.lin * m)
    (w : Point D.host.E (D.R.rS + 1)) :
    IsInCell (ZhatOM (ZhatL (lf D (X.Fu u)) t₀.frame)) w ↔ IsInCell (ZhatOM (ZhatL (lf D (X.Fu u)) t.frame)) w :=
  PI.TermAttrConst.UnitaryGroupMassFormula.cellFun_all (⊤ : Submodule (𝓞 D.host.E) (VS D).V) (lf D (X.Fu u))
    (fun _ => True) ⟨t₀.frame, trivial⟩ ⟨t.frame, trivial⟩ (dcrel_of_coset t₀ t hn hm h) w

theorem rel_iff_frames (t₀ t : TauC Y u u') {n m : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hn : n ∈ NRat (lf D (X.Fu u))) (hm : m ∈ NRat (lf D (X.Fu u'))) (h : t.lin = n⁻¹ * t₀.lin * m) :
    Relevant D.host.F (lf D (X.Fu u)).fl t₀.frame.fl ↔ Relevant D.host.F (lf D (X.Fu u)).fl t.frame.fl :=
  PI.TermAttrConst.UnitaryGroupMassFormula.relFun_all D.host.F (⊤ : Submodule (𝓞 D.host.E) (VS D).V) (lf D (X.Fu u))
    (fun _ => True) ⟨t₀.frame, trivial⟩ ⟨t.frame, trivial⟩ (dcrel_of_coset t₀ t hn hm h)

theorem pt_eq (t₀ t : TauC Y u u') (hrl : t.relevant ↔ t₀.relevant) (hat : ∀ w, t.toTerm.atPt w ↔ t₀.toTerm.atPt w) :
    Formalism.L2.SG.PairVal.ptOf t.toTerm = Formalism.L2.SG.PairVal.ptOf t₀.toTerm := by
  have hCP := Formalism.L2.SG.Pf.cell_point_unique_of_term_fun (Formalism.L2.SG.Closed.TermFun_holds D u u') (Y.rowsOK u)
  by_cases hx : ∃ w, t₀.toTerm.atPt w ∧ t₀.toTerm.relevant
  · have hx' : ∃ w, t.toTerm.atPt w ∧ t.toTerm.relevant := by
      obtain ⟨w, hw, hr⟩ := hx
      exact ⟨w, (hat w).2 hw, hrl.2 hr⟩
    exact hCP t₀.toTerm _ _ ((hat _).1 (Formalism.L2.SG.PairVal.ptOf_spec t.toTerm hx'))
      (Formalism.L2.SG.PairVal.ptOf_spec t₀.toTerm hx)
  · have hx' : ¬ ∃ w, t.toTerm.atPt w ∧ t.toTerm.relevant := by
      rintro ⟨w, hw, hr⟩
      exact hx ⟨w, (hat w).1 hw, hrl.1 hr⟩
    unfold Formalism.L2.SG.PairVal.ptOf
    rw [dite_eq_right hx, dite_eq_right hx']

end GlobalTheory.HL.CosetConst

theorem GlobalTheory.HL.CosetConst.coset_const : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    Formalism.MainNotions.S.Cnt.Stand D u u' →
    ∀ (t₀ t : TauC Y u u') (n m : ((VS D).V ≃ₗ[D.host.E] (VS D).V)), t₀.relevant → t₀.G ≠ 0 →
      n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m →
      t.relevant ∧ t.G = t₀.G ∧ Formalism.L2.SG.PairVal.ptOf t.toTerm = Formalism.L2.SG.PairVal.ptOf t₀.toTerm ∧
        nmlOf Y u u' t = nmlOf Y u u' t₀ ∧
        ((Y.tO u u').rowOf t = (Y.tO u u').rowOf t₀ → (Y.tO u u').s0 t₀ t = 1 ∧ (Y.tO u u').scal t₀ t) := by
  intro D X Y u u' _ t₀ t n m hrel hG hnm
  obtain ⟨hn, hm, h⟩ := hnm
  have eG := GlobalTheory.HL.CosetConst.G_eq_frames t₀ t hn hm h
  have hrl : t.relevant ↔ t₀.relevant := by
    rw [GlobalTheory.HL.CosetConst.relevant_iff, GlobalTheory.HL.CosetConst.relevant_iff]
    exact (GlobalTheory.HL.CosetConst.rel_iff_frames t₀ t hn hm h).symm
  have hat : ∀ w, t.toTerm.atPt w ↔ t₀.toTerm.atPt w := fun w => by
    rw [GlobalTheory.HL.CosetConst.atPt_iff, GlobalTheory.HL.CosetConst.atPt_iff, eG,
      GlobalTheory.HL.CosetConst.cell_iff_frames t₀ t hn hm h w]
  have hnml := GlobalTheory.HL.CosetConst.nml_eq t₀ t hn hm h
  refine ⟨hrl.2 hrel, ?_, GlobalTheory.HL.CosetConst.pt_eq t₀ t hrl hat, hnml,
    fun hr => GlobalTheory.T.same_row_same_coset_scalar_corank_one D X Y u u' t₀ t hG hr.symm hnml.symm⟩
  rw [Formalism.L2.SG.Pf.SatGram.gterm_G (X := X) (Y := Y) (t := t),
    Formalism.L2.SG.Pf.SatGram.gterm_G (X := X) (Y := Y) (t := t₀), eG]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagTermInvariantsConstOnRationalDoubleCosetStatement
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagTerm_invariants_const_on_rationalDoubleCoset : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → ∀ (t₀ t : TauC Y u u') (n m : ((VS D).V ≃ₗ[D.host.E] (VS D).V)), t₀.relevant → t₀.G ≠ 0 → n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m → t.relevant ∧ t.G = t₀.G ∧ Formalism.L2.SG.PairVal.ptOf t.toTerm = Formalism.L2.SG.PairVal.ptOf t₀.toTerm ∧ nmlOf Y u u' t = nmlOf Y u u' t₀ ∧ ((Y.tO u u').rowOf t = (Y.tO u u').rowOf t₀ → (Y.tO u u').s0 t₀ t = 1 ∧ (Y.tO u u').scal t₀ t) := by
  first | exact @GlobalTheory.HL.CosetConst.coset_const | exact GlobalTheory.HL.CosetConst.coset_const | (intros; apply GlobalTheory.HL.CosetConst.coset_const <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsCMFieldOfStar
noncomputable section

open NumberField GlobalTheory.DegCnt

namespace GlobalTheory.OrthoLattice

theorem isCMField_of_star (K : Type) [Field K] [NumberField K] [StarRing K] (htc : IsTotallyComplex K)
    (hst : ∀ (φ : K →+* ℂ) (a : K), φ (star a) = starRingEnd ℂ (φ a)) : IsCMField K := by
  let φ : K →+* ℂ := Classical.choice (inferInstance : Nonempty _)
  have hmem : ∀ x : K, star x = x → x ∈ maximalRealSubfield K := fun x hx ψ => by
    have := hst ψ x
    rw [hx] at this
    exact this.symm
  have hfix : ∀ x : maximalRealSubfield K, star (x : K) = x := fun x =>
    φ.injective (by rw [hst]; exact x.2 φ)
  obtain ⟨a, ha⟩ : ∃ a : K, star a ≠ a := by
    by_contra h
    push Not at h
    apply IsTotallyComplex.complexEmbedding_not_isReal φ
    rw [ComplexEmbedding.isReal_iff]
    ext x
    rw [ComplexEmbedding.conjugate_coe_eq, ← hst, h]
  set d : K := a - star a with hd
  have hd0 : d ≠ 0 := sub_ne_zero.2 ha.symm
  have hds : star d = -d := by simp [hd]
  have hli : LinearIndependent (maximalRealSubfield K) ![(1 : K), d] := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have h1 : (s : K) + (t : K) * d = 0 := by simpa [Subfield.smul_def] using h
    have h2 := congrArg star h1
    rw [star_add, star_mul, hfix, hfix, hds, star_zero] at h2
    have h3 : (s : K) = 0 := by linear_combination (h1 + h2) / 2
    have h4 : (t : K) * d = 0 := by linear_combination h1 - h3
    exact ⟨Subtype.ext h3, Subtype.ext ((mul_eq_zero.1 h4).resolve_right hd0)⟩
  have hsp : ⊤ ≤ Submodule.span (maximalRealSubfield K) (Set.range ![(1 : K), d]) := by
    intro x _
    have h1 : star ((x + star x) / 2) = (x + star x) / 2 := by
      rw [star_div₀, star_add, star_star, star_ofNat, add_comm]
    have h2 : star ((x - star x) / (2 * d)) = (x - star x) / (2 * d) := by
      rw [star_div₀, star_sub, star_star, star_mul, star_ofNat, hds]
      field_simp
      ring
    have h3 : x = (⟨_, hmem _ h1⟩ : maximalRealSubfield K) • (1 : K) +
        (⟨_, hmem _ h2⟩ : maximalRealSubfield K) • d := by
      simp only [Subfield.smul_def, smul_eq_mul]
      field_simp
      ring
    rw [h3]
    exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  have : Algebra.IsQuadraticExtension (maximalRealSubfield K) K :=
    { finrank_eq_two' := by simpa using Module.finrank_eq_card_basis (Module.Basis.mk hli hsp) }
  exact ⟨⟩

theorem hasOrtho : ∀ (K : Type) [Field K] [NumberField K] [StarRing K],
    Formalism.HermitianLatticesTheory.IsCMUnram K → HasOrtho K := by
  intro K _ _ st hc
  have := isCMField_of_star K hc.1 hc.2.1
  have hs : st = IsCMField.starRing K := by
    let φ : K →+* ℂ := Classical.choice (inferInstance : Nonempty _)
    have h : ∀ x, st.star x = IsCMField.complexConj K x := fun x =>
      φ.injective (by rw [IsCMField.complexEmbedding_complexConj]; exact hc.2.1 φ x)
    obtain @⟨@⟨@⟨@⟨f⟩, _⟩, _⟩, _⟩ := st
    obtain rfl : f = IsCMField.complexConj K := funext h
    rfl
  subst hs
  let := IsCMField.starRing K
  intro W _ _ _ _ _ k hk hp ⟨L, hL, hU⟩
  let φ : K →+* ℂ := Classical.choice (inferInstance : Nonempty _)
  have hnd : k.Nondegenerate := by
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩ <;>
    · by_contra h0
      have := hp φ x h0
      rw [hx x] at this
      simp at this
  let S : Formalism.BasicNotions.HSpace K := Formalism.BasicNotions.HSpace.mk W k hk hnd (Module.finrank K W) rfl (Module.finBasis K W)
    (fun _ => (Module.finrank K W, 0)) L hL hU
  have hsig : S.SigOK := fun τ => GlobalTheory.Proof.GenusMassSignature.hasSignature_of_posDef
    ((GlobalTheory.Proof.GenusMassSignature.pos_iff_posDef hc.1 hc.2.1 S τ).1 (hp τ))
  obtain ⟨b, hb, ho⟩ := GlobalTheory.DefiniteOrthonormal.exists_orthonormal hc S hsig fun _ => rfl
  exact ⟨_, b, hb, hb.span_eq_top_of_card_eq_finrank' (Fintype.card_fin _), rfl, ho⟩

end GlobalTheory.OrthoLattice
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowDictGoodOpNonempty
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace GlobalTheory

theorem rowDict_goodOp_nonempty :
    ∀ (D : D7) (X : HidaSetting D), Nonempty (Formalism.L2.SG.RowDict.GoodOp X) :=
  fun _ X => Formalism.L2.SG.Pf.rowDictGoodOp_exists X

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermsOverRowCompatible
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermsOverRowCompatible
noncomputable section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
namespace GlobalTheory.TypeAsm.CompatPf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {X : HidaSetting D} {u : D.what₂.Word}

theorem fixedFrameOfWord_isotropic_eq_flag : (F0 X u).X = (X.Fu u).X := by
  unfold Formalism.HermitianLatticeCounting.S6.FlagD.X Formalism.HermitianLatticeCounting.S6.FlagD.Xa FlagG.X
  congr 1
  ext x
  constructor
  · rintro ⟨b, -, rfl⟩; exact ⟨b, (fv_cast _ b).symm⟩
  · rintro ⟨b, rfl⟩; exact ⟨b, b.2, fv_cast _ b⟩

theorem compatC : CompatC := by
  rintro D X Y u ⟨s₁, s₂⟩ ⟨-, -, hp⟩
  have hp' : rowOf Y.TR (Y.cs u) (Y.cs u) s₁ = rowOf Y.TR (Y.cs u) (Y.cs u) s₂ := hp
  have hl : s₁.lam = s₂.lam := congrArg (fun r => r.1.1) hp'
  have hl' : s₁.lam' = s₂.lam' := congrArg (fun r => r.2.1.1) hp'
  have hi : iotaOf Y.TR (Y.cs u) (Y.cs u) s₁ = iotaOf Y.TR (Y.cs u) (Y.cs u) s₂ := congrArg (fun r => r.2.2) hp'
  have h := (Formalism.L2.SG.Pf.Act.ratIotaC' Y u u s₁ s₂ hl hl').1 (Formalism.L2.SG.Pf.iotaDict_fwd Y s₁ s₂ hl hl' hi)
  refine ⟨hl, hl', fun x hx => ?_⟩
  have hx2 : x ∈ GlobalTheory.HermLat.perp (HV D) (F0 X u).X := hx.2
  rw [GlobalTheory.HermLat.mem_perp_iff, fixedFrameOfWord_isotropic_eq_flag] at hx2
  have hx' : x ∈ Lrep s₁.lam (lf D (X.Fu u)) := by
    refine ⟨hx.1, ?_⟩
    show x ∈ orth (VS D) (X.Fu u).X
    simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
    exact hx2
  have h2 := h x hx'
  unfold NgX at h2
  rw [sup_assoc, sup_idem] at h2
  rw [fixedFrameOfWord_isotropic_eq_flag]
  refine SetLike.le_def.1 (sup_le_sup ?_ le_rfl) h2
  rw [Submodule.ideal_span_singleton_smul]
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨y, hy, rfl⟩
end GlobalTheory.TypeAsm.CompatPf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermsOverRowCompatibleStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.termsOverRow_compatible : GlobalTheory.TypeAsm.CompatC := by
  first | exact @GlobalTheory.TypeAsm.CompatPf.compatC | exact GlobalTheory.TypeAsm.CompatPf.compatC | (intros; apply GlobalTheory.TypeAsm.CompatPf.compatC <;> assumption)
end
end
