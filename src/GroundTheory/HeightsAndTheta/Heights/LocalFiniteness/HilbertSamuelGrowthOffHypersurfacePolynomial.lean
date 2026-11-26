module

public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PGreenMassError
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PGreenMassReplace
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PGreenMassStep
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StRegSectionParts
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PPlaceCentredSum
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitChartMax
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitConjSum
public import GroundTheory.GlobalFields.ComplexMultiplication.ClassGroupAction
public import GroundTheory.GlobalFields.AnalyticClassNumber.DirichletHecke
public import GroundTheory.GlobalFields.Artin.OneDim
public import GroundTheory.GlobalFields.Artin.Series
public import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.PConstants
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PSemilocalLengthSum
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PSemilocalLength
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PSemilocalIntegral
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PLocalIntegralClosureFinite
public import GroundTheory.HeightsAndTheta.Heights.LocalDensities.PHermitianDetMono
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PAvoidFormFinite
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPullSectionIntegralInt
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenNearCover
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHSMTransport
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PModulePieceHilbert
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPowerBlockPointNorm
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PProjAvoidingForm
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwoBlockPieceIndex
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Assembly
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPushDown
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHodgeFlagMinorTrdeg
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHodgeFlagRatioFieldEq
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PTpIntegrandLimit
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PDominatingDVRScheme
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.HasFiniteBiproductsModules
public import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.PDifferentExtNorm
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDimTwoSumReading
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagClosurePullback
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpLocalChart
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingNoetherian
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PJoinDivCycle
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PJoinIntNum
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PJoinPointIdeal
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PLocalizedQuotLength
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagConeAlg
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpanBundleTrdegLe
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagPairJoinLeft
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagPairJoinRight
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagCutChartSection
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.PBoundedChartComparison
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.PPuncturedExpOrder
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMinimalPrimesSpanSingleton
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

theorem MinimalPrimesSpanSingleton.proof : MinimalPrimesSpanSingleton.Statement.{u} := by
  intro A _ _ _ x hx W
  constructor
  · intro hW
    have hWp : W.IsPrime := hW.isPrime
    have hxW : x ∈ W := hW.1.2 (Ideal.mem_span_singleton_self x)
    refine ⟨hWp, ?_, hxW⟩
    have hle : W.height ≤ 1 :=
      Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {x}) W hW
    have hne : W.height ≠ 0 := by
      rw [Ne, Ideal.height_eq_zero_iff_eq_bot]
      intro hbot
      rw [hbot, Ideal.mem_bot] at hxW
      exact hx hxW
    exact le_antisymm hle (Order.one_le_iff_ne_zero.mpr hne)
  · rintro ⟨hWp, hh, hxW⟩
    refine ⟨⟨hWp, (Ideal.span_singleton_le_iff_mem W).mpr hxW⟩, ?_⟩
    rintro Q ⟨hQp, hxQ⟩ hQW
    by_contra hWQ
    have hlt : Q < W := lt_of_le_of_ne hQW (fun h => hWQ (h ▸ le_refl Q))
    have hfin : W.FiniteHeight := W.finiteHeight_iff.mpr (Or.inr (by rw [hh]; exact ENat.one_ne_top))
    have hQh : Q.height < 1 := hh ▸ Ideal.height_strict_mono_of_isPrime_of_isPrime hlt
    have hQ0 : Q.height = 0 := Order.lt_one_iff.mp hQh
    rw [Ideal.height_eq_zero_iff_eq_bot] at hQ0
    have hx0 : x ∈ (⊥ : Ideal A) := hQ0 ▸ (Ideal.span_singleton_le_iff_mem Q).mp hxQ
    exact hx ((Ideal.mem_bot).mp hx0)

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PLocalDomainDimTwo
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

private theorem enat_eq_two_of_le_of_lt {x : ℕ∞} (h2 : 2 ≤ x) (h3 : x < 3) : x = 2 := by
  induction x using ENat.recTopCoe with
  | top => exact absurd h3 (by simp)
  | coe n =>
    have a : 2 ≤ n := by exact_mod_cast h2
    have b : n < 3 := by exact_mod_cast h3
    have : n = 2 := by omega
    subst this; rfl

private theorem enat_le_one_of_add_one_le_two {x : ℕ∞} (h : x + 1 ≤ 2) : x ≤ 1 := by
  induction x using ENat.recTopCoe with
  | top => exact absurd h (by simp)
  | coe n =>
    have : n + 1 ≤ 2 := by exact_mod_cast h
    exact_mod_cast (by omega : n ≤ 1)

theorem LocalDomainDimTwo.proof : LocalDomainDimTwo.Statement := by
  intro A _ _ _ _ hno hQ
  obtain ⟨Q, hQp, h0, hQm⟩ := hQ
  have := hQp
  have e1 := Ideal.height_add_one_le_of_lt_of_isPrime h0
  have e2 := Ideal.height_add_one_le_of_lt_of_isPrime hQm
  have hm2 : (2 : ℕ∞) ≤ (IsLocalRing.maximalIdeal A).height :=
    le_trans (by rw [← one_add_one_eq_two]; exact add_le_add (le_trans le_add_self e1) le_rfl) e2
  have hm3 : (IsLocalRing.maximalIdeal A).height < 3 := by
    by_contra h3
    have hle : ((3 : ℕ) : ℕ∞) ≤ Order.height (IsLocalRing.closedPoint A) := by
      rw [← PrimeSpectrum.height_eq_orderHeight]
      exact not_lt.mp h3
    obtain ⟨p, hlast, hlen⟩ := Order.exists_series_of_le_height _ hle
    have s0 := p.step ⟨0, by omega⟩
    have s1 := p.step ⟨1, by omega⟩
    have s2 := p.step ⟨2, by omega⟩
    have e01 : (Fin.succ (⟨0, by omega⟩ : Fin p.length)) = Fin.castSucc ⟨1, by omega⟩ := Fin.ext rfl
    have e12 : (Fin.succ (⟨1, by omega⟩ : Fin p.length)) = Fin.castSucc ⟨2, by omega⟩ := Fin.ext rfl
    have e2l : (Fin.succ (⟨2, by omega⟩ : Fin p.length)) = Fin.last p.length := Fin.ext (by simp [hlen])
    rw [e01] at s0
    rw [e12] at s1
    rw [e2l] at s2
    have hl : p.toFun (Fin.last p.length) = IsLocalRing.closedPoint A := hlast
    rw [hl] at s2
    refine hno (p.toFun (Fin.castSucc ⟨1, by omega⟩)).asIdeal (p.toFun (Fin.castSucc ⟨2, by omega⟩)).asIdeal
      (p.toFun _).isPrime (p.toFun _).isPrime ?_ ((PrimeSpectrum.asIdeal_lt_asIdeal _ _).mpr s1)
      ((PrimeSpectrum.asIdeal_lt_asIdeal _ _).mpr s2)
    exact lt_of_le_of_lt bot_le ((PrimeSpectrum.asIdeal_lt_asIdeal _ _).mpr s0)
  have hm : (IsLocalRing.maximalIdeal A).height = 2 := enat_eq_two_of_le_of_lt hm2 hm3
  refine ⟨?_, hm, ?_⟩
  · rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, hm]
    rfl
  · intro Q' hQ' h0' hQm'
    have := hQ'
    have f1 := Ideal.height_add_one_le_of_lt_of_isPrime h0'
    have f2 := Ideal.height_add_one_le_of_lt_of_isPrime hQm'
    rw [hm] at f2
    exact le_antisymm (enat_le_one_of_add_one_le_two f2) (le_trans le_add_self f1)

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpHorizontalMinimal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

noncomputable section

theorem BlowUpHorizontalMinimal.full : BlowUpHorizontalMinimal.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hex hloc c x hx hxP W hW hϖW
  classical
  have hPp : P.IsPrime := hP.multiProj.isPrime

  have hmin : W ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes := by
    unfold divCycle at hW
    split_ifs at hW with h
    · exact h.1
    · exact absurd rfl hW
  obtain ⟨hWp, hBW, hWrel⟩ := le_and_isRelevant_of_divCycle_ne_zero hW
  set W₀ := W.comap (liftForm (ι := ι) (J := J) (R := O)) with hW₀
  obtain ⟨hW₀p, hPW₀, hrel₀, -⟩ := comap_liftForm_facts hWp hBW hWrel
  have hϖW₀ : (C ϖ : MRing ι O) ∉ W₀ := by rw [Ideal.mem_comap, liftForm_C]; exact hϖW
  obtain ⟨j₀, hj₀⟩ := hloc W₀ hW₀p hPW₀ hrel₀ hϖW₀
  choose v w hv hvw using hj₀

  have huj₀ : u j₀ ∉ P := by
    intro h
    obtain ⟨j, hj⟩ := hex
    have h1 : v j * u j ∈ P := by
      have := P.add_mem (hvw j) (P.mul_mem_left (w j) h)
      rwa [sub_add_cancel] at this
    exact hj ((hPp.mem_or_mem h1).resolve_left fun h' => hv j (hPW₀ h'))

  obtain ⟨u₀, a, hu₀W, hrelP⟩ : ∃ (u₀ : MRing ι O) (a : J → MRing ι O), u₀ ∉ W₀ ∧
      ∀ j, u₀ * u j - u j₀ * a j ∈ P := by
    have := hW₀p
    refine ⟨∏ j, v j, fun j => w j * ∏ j' ∈ Finset.univ.erase j, v j',
      fun h => W₀.primeCompl.prod_mem (fun j _ => hv j) h, fun j => ?_⟩
    have e : (∏ j, v j) * u j - u j₀ * (w j * ∏ j' ∈ Finset.univ.erase j, v j') =
        (∏ j' ∈ Finset.univ.erase j, v j') * (v j * u j - w j * u j₀) := by
      rw [← Finset.mul_prod_erase Finset.univ v (Finset.mem_univ j)]; ring
    rw [e]
    exact P.mul_mem_left _ (hvw j)
  have hu₀P : u₀ ∉ P := fun h => hu₀W (hPW₀ h)
  have ha₀ : a j₀ ∉ W₀ := by
    intro h
    have h1 : u j₀ * (u₀ - a j₀) ∈ P := by
      have := hrelP j₀
      rwa [show u₀ * u j₀ - u j₀ * a j₀ = u j₀ * (u₀ - a j₀) by ring] at this
    have h2 : u₀ - a j₀ ∈ W₀ := hPW₀ ((hPp.mem_or_mem h1).resolve_left huj₀)
    exact hu₀W (by simpa using W₀.add_mem h2 h)

  have hrelB : ∀ j, newVar j * liftForm (a j₀) - newVar j₀ * liftForm (a j) ∈ blowUpOf P u := by
    intro j
    apply mem_blowUpOf_of_sub
    have e : u₀ * (u j * a j₀ - u j₀ * a j) =
        a j₀ * (u₀ * u j - u j₀ * a j) - a j * (u₀ * u j₀ - u j₀ * a j₀) := by ring
    have h1 : u₀ * (u j * a j₀ - u j₀ * a j) ∈ P := by
      rw [e]; exact P.sub_mem (P.mul_mem_left _ (hrelP j)) (P.mul_mem_left _ (hrelP j₀))
    exact (hPp.mem_or_mem h1).resolve_left hu₀P

  have hxW : liftForm x ∈ W := hmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  refine ⟨⟨hW₀p, sup_le hPW₀ ((Ideal.span_singleton_le_iff_mem _).mpr hxW)⟩, fun P' hP' hP'W₀ => ?_⟩
  have := hP'.1
  have hxP' : x ∈ P' := hP'.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x))

  let Q' := (Ideal.map (Polynomial.C : MRing ι O →+* Polynomial (MRing ι O)) P').comap
    (aeval (R := O) (chartSubst a))
  have hQ'p : Q'.IsPrime := Ideal.comap_isPrime _ _
  have hBQ' : blowUpOf P u ⊔ Ideal.span {liftForm x} ≤ Q' := by
    refine sup_le (fun G hG => ?_) ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
    · exact Ideal.map_mono (le_sup_left.trans hP'.2)
        (aeval_chartSubst_mem_of_mem_blowUpOf hPp huj₀ hrelP hG)
    · rw [Ideal.mem_comap, aeval_chartSubst_liftForm]
      exact Ideal.mem_map_of_mem _ hxP'
  have hQ'W : Q' ≤ W := fun G hG =>
    mem_of_aeval_chartSubst_mem hWp hP'W₀ j₀ ha₀ (fun j => hBW (hrelB j)) hG

  have hWQ' : W ≤ Q' := hmin.2 ⟨hQ'p, hBQ'⟩ hQ'W
  intro p hp
  have h5 : Polynomial.C p ∈ Ideal.map (Polynomial.C : MRing ι O →+* Polynomial (MRing ι O)) P' := by
    rw [← aeval_chartSubst_liftForm a p]
    exact hWQ' hp
  simpa using Ideal.mem_map_C_iff.mp h5 0

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PLengthMapIdealLe
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

open IsLocalRing

theorem LengthMapIdealLe.proof : LengthMapIdealLe.Statement.{u} := by
  intro C D _ _ _ φ hφ
  suffices key : ∀ n : ℕ, ∀ I : Ideal C, Module.length C (C ⧸ I) = n →
      Module.length D (D ⧸ I.map φ) ≤ n by
    intro I
    cases h : Module.length C (C ⧸ I) with
    | top => exact le_top
    | coe n => exact key n I h
  intro n
  induction n with
  | zero =>
    intro I hI
    have hs : Subsingleton (C ⧸ I) := Module.length_eq_zero_iff.mp (by exact_mod_cast hI)
    have hItop : I = ⊤ := Ideal.Quotient.subsingleton_iff.mp hs
    subst hItop
    rw [Ideal.map_top]
    have : Subsingleton (D ⧸ (⊤ : Ideal D)) := Ideal.Quotient.subsingleton_iff.mpr rfl
    simp [Module.length_eq_zero]
  | succ n ih =>
    intro I hI
    have hfin : IsFiniteLength C (C ⧸ I) :=
      Module.length_ne_top_iff.mp (by rw [hI]; exact ENat.natCast_ne_top _)
    have : IsArtinian C (C ⧸ I) := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfin).2
    have : Nontrivial (C ⧸ I) :=
      Module.length_pos_iff.mp (by rw [hI]; exact_mod_cast Nat.succ_pos n)
    have : IsAtomic (Submodule C (C ⧸ I)) := isAtomic_of_orderBot_wellFounded_lt wellFounded_lt
    obtain ⟨N, hN, -⟩ := (eq_bot_or_exists_atom_le (⊤ : Submodule C (C ⧸ I))).resolve_left top_ne_bot
    have hNs : IsSimpleModule C N := isSimpleModule_iff_isAtom.mpr hN

    have hlen : Module.length C (C ⧸ I) = Module.length C N + Module.length C ((C ⧸ I) ⧸ N) :=
      Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
        (LinearMap.exact_subtype_mkQ N)
    rw [Module.length_eq_one (R := C) (M := N), hI] at hlen
    have hq : Module.length C ((C ⧸ I) ⧸ N) = n := by
      have hx : Module.length C ((C ⧸ I) ⧸ N) ≠ ⊤ := by
        intro h
        rw [h, add_top] at hlen
        exact ENat.natCast_ne_top _ hlen
      obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hx
      rw [← hk] at hlen ⊢
      norm_cast at hlen ⊢
      omega

    obtain ⟨v, hvN, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN.1
    have hspan : Submodule.span C {v} = N :=
      (hN.le_iff.mp ((Submodule.span_singleton_le_iff_mem _ _).mpr hvN)).resolve_left
        (by simpa using hv0)
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective v

    set I' : Ideal C := N.comap (Submodule.mkQ I) with hI'def
    have hII' : I ≤ I' := by
      intro x hx
      show Submodule.mkQ I x ∈ N
      rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero I).mpr hx]
      exact N.zero_mem
    have hI'N : Submodule.map (Submodule.mkQ I) I' = N :=
      Submodule.map_comap_eq_of_surjective (Submodule.mkQ_surjective I) N
    have hlenI' : Module.length C (C ⧸ I') = n := by
      rw [← (Submodule.quotientQuotientEquivQuotient I I' hII').length_eq, hI'N, hq]
    have ih' := ih I' hlenI'

    set m : Ideal C := Module.annihilator C N
    have hm : m.IsMaximal := IsSimpleModule.annihilator_isMaximal
    have hmc : ∀ x ∈ m, x * c ∈ I := by
      intro x hx
      have h1 := Module.mem_annihilator.mp hx ⟨_, hvN⟩
      have h2 : x • (Ideal.Quotient.mk I c) = 0 := congrArg Subtype.val h1
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul]
      simpa [Algebra.smul_def] using h2

    have hI'le : I' ≤ I ⊔ Ideal.span {c} := by
      intro x hx
      have hx' : Submodule.mkQ I x ∈ Submodule.span C {Ideal.Quotient.mk I c} := hspan ▸ hx
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hx'
      have hxa : Ideal.Quotient.mk I x = Ideal.Quotient.mk I (a * c) := by
        rw [map_mul]
        simpa [Algebra.smul_def] using ha.symm
      have hd : x - a * c ∈ I := Ideal.Quotient.eq.mp hxa
      rw [show x = (x - a * c) + a * c by ring]
      exact Submodule.add_mem_sup hd (Ideal.mul_mem_left _ a (Ideal.subset_span rfl))

    set J : Ideal D := I.map φ
    set J' : Ideal D := I'.map φ
    have hJJ' : J ≤ J' := Ideal.map_mono hII'
    have hJ'le : J' ≤ J ⊔ Ideal.span {φ c} := by
      calc J' ≤ (I ⊔ Ideal.span {c}).map φ := Ideal.map_mono hI'le
        _ = J ⊔ Ideal.span {φ c} := by rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
    set w : D ⧸ J := Submodule.Quotient.mk (p := J) (φ c)
    set K : Submodule D (D ⧸ J) := Submodule.map (Submodule.mkQ J) J'
    have hK : K ≤ Submodule.span D {w} := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨p, hp, q, hq', rfl⟩ := Submodule.mem_sup.mp (hJ'le hy)
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp hq'
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero J).mpr hp,
        zero_add, ← smul_eq_mul, Submodule.Quotient.mk_smul]
      exact Submodule.smul_mem _ b (Submodule.mem_span_singleton_self w)
    have hlenD : Module.length D (D ⧸ J) = Module.length D K + Module.length D (D ⧸ J') := by
      rw [Module.length_eq_add_of_exact K.subtype K.mkQ K.injective_subtype K.mkQ_surjective
        (LinearMap.exact_subtype_mkQ K), (Submodule.quotientQuotientEquivQuotient J J' hJJ').length_eq]

    have hmX : m.map φ ≤ LinearMap.ker (LinearMap.toSpanSingleton D (D ⧸ J) w) := by
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      rw [Ideal.mem_comap, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, ← Submodule.Quotient.mk_smul,
        smul_eq_mul, ← map_mul, Submodule.Quotient.mk_eq_zero]
      exact Ideal.mem_map_of_mem φ (hmc x hx)
    have hKle1 : Module.length D K ≤ 1 := by
      rcases hφ m hm with htop | hle
      · have hw : w = 0 := by
          have h1 : (1 : D) ∈ LinearMap.ker (LinearMap.toSpanSingleton D (D ⧸ J) w) :=
            hmX (htop ▸ Submodule.mem_top)
          simpa using h1
        have hK0 : K = ⊥ := le_bot_iff.mp (hK.trans (by simp [hw]))
        rw [hK0, Module.length_bot]
        exact zero_le
      · have h1 : maximalIdeal D ≤ LinearMap.ker (LinearMap.toSpanSingleton D (D ⧸ J) w) :=
          hle.trans hmX
        let f := (maximalIdeal D).liftQ (LinearMap.toSpanSingleton D (D ⧸ J) w) h1
        have hrange : LinearMap.range f = Submodule.span D {w} := by
          rw [Submodule.range_liftQ, LinearMap.range_toSpanSingleton]
        have : IsSimpleModule D (D ⧸ maximalIdeal D) :=
          isSimpleModule_iff_quot_maximal.mpr ⟨_, inferInstance, ⟨LinearEquiv.refl _ _⟩⟩
        calc Module.length D K ≤ Module.length D (Submodule.span D {w}) :=
              Module.length_le_of_injective (Submodule.inclusion hK) (Submodule.inclusion_injective hK)
          _ = Module.length D (LinearMap.range f) := by rw [hrange]
          _ ≤ Module.length D (D ⧸ maximalIdeal D) :=
              Module.length_le_of_surjective f.rangeRestrict f.surjective_rangeRestrict
          _ = 1 := Module.length_eq_one _ _
    calc Module.length D (D ⧸ I.map φ) = Module.length D K + Module.length D (D ⧸ J') := hlenD
      _ ≤ 1 + n := add_le_add hKle1 ih'
      _ = ((n + 1 : ℕ) : ℕ∞) := by push_cast; ring

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpOrderLe
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

noncomputable section

theorem subring_map_maximal_cases {D : Type*} [CommRing D] [IsLocalRing D] (C : Subring D)
    (hC : IsLocalRing.maximalIdeal D ≤ ((IsLocalRing.maximalIdeal D).comap C.subtype).map C.subtype)
    (m : Ideal C) (hm : m.IsMaximal) :
    m.map C.subtype = ⊤ ∨ IsLocalRing.maximalIdeal D ≤ m.map C.subtype := by
  by_cases h : m ≤ (IsLocalRing.maximalIdeal D).comap C.subtype
  · right
    rw [hm.eq_of_le (Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal D).ne_top) h]
    exact hC
  · left
    obtain ⟨c, hcm, hc⟩ := Set.not_subset.mp h
    have hu : IsUnit (C.subtype c) := by
      by_contra hnu
      exact hc (IsLocalRing.mem_maximalIdeal _ |>.mpr hnu)
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hcm) hu

theorem length_quot_le_of_subring (h₂ : LengthMapIdealLe.Statement.{u})
    (h₃ : IntermediateRingQuotLength.Statement.{u}) {A D : Type u} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [CommRing D] [IsDomain D] [IsLocalRing D] (hdim : ringKrullDim A = 1)
    (C : Subring D) (f : A →+* C) (hfinj : Function.Injective f)
    (hfrac : ∀ c : C, ∃ a, a ≠ 0 ∧ f a * c ∈ Set.range f)
    (hmax : IsLocalRing.maximalIdeal D ≤
      ((IsLocalRing.maximalIdeal D).comap C.subtype).map C.subtype)
    (a : A) (ha : a ≠ 0) :
    Module.length D (D ⧸ Ideal.span {(f a : D)}) ≤ Module.length A (A ⧸ Ideal.span {a}) := by
  let _ : Algebra A C := f.toAlgebra
  have s3 := h₃ A C hdim hfinj
    (fun c => by
      obtain ⟨b, hb, hbc⟩ := hfrac c
      exact ⟨b, hb, by rw [Algebra.smul_def]; exact hbc⟩) a ha
  have s2 : Module.length C (C ⧸ Ideal.span {algebraMap A C a}) ≤
      Module.length A (C ⧸ Ideal.span {algebraMap A C a}) := by
    have h := Submodule.length_le_length_restrictScalars A
      (⊤ : Submodule C (C ⧸ Ideal.span {algebraMap A C a}))
    rwa [Submodule.restrictScalars_top, Module.length_top, Module.length_top] at h
  have s1 := h₂ C D C.subtype (subring_map_maximal_cases C hmax) (Ideal.span {algebraMap A C a})
  rw [Ideal.map_span, Set.image_singleton] at s1
  exact s1.trans (s2.trans s3)

theorem BlowUpOrderLe.proof (h₁ : LocalizedQuotLength.Statement.{u})
    (h₂ : LengthMapIdealLe.Statement.{u}) (h₃ : IntermediateRingQuotLength.Statement.{u})
    (h₄ : BlowUpLocalChart.Statement.{u}) : BlowUpOrderLe.Statement.{u} := by
  intro R _ _ K _ ι _ J _ P hP u G' y hy hG' hrel x hx hG z hz
  have hGp : G'.IsPrime := hG'.1.1
  obtain ⟨G₀, W₀, hG₀p, hW₀p, hG₀, hW₀⟩ := BlowUpLocalChart.exists_quotient_primes hGp
    (le_sup_left.trans hG'.1.2) (le_sup_left.trans hG.1.2)
  have hRHS0 : (0 : ℤ) ≤ divCycle P z (G'.comap (liftForm (J := J))) := by
    unfold divCycle
    split_ifs <;> positivity
  by_cases hL : G' ∈ (blowUpOf P u ⊔ Ideal.span {liftForm z}).minimalPrimes ∧ IsRelevant G'
  swap
  · have h0 : divCycle (blowUpOf P u) (liftForm z) G' = 0 := by
      unfold divCycle
      rw [dite_eq_right hL]
    rw [h0]
    exact hRHS0
  have hzG : z ∈ G'.comap (liftForm (J := J)) :=
    hL.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hcp : (G'.comap (liftForm (J := J))).IsPrime := hG.1.1
  have hRmin : G'.comap (liftForm (J := J)) ∈ (P ⊔ Ideal.span {z}).minimalPrimes := by
    have h := mem_minimalPrimes_sup_span_mul (P := P) (W := G'.comap (liftForm (J := J))) hz hG
    refine ⟨⟨hcp, sup_le (le_sup_left.trans hG.1.2) ((Ideal.span_singleton_le_iff_mem _).mpr hzG)⟩, ?_⟩
    intro q hq hqG
    refine h.2 ⟨hq.1, sup_le (le_sup_left.trans hq.2) ((Ideal.span_singleton_le_iff_mem _).mpr ?_)⟩ hqG
    exact q.mul_mem_left x (hq.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self z)))
  have hRrel : IsRelevant (G'.comap (liftForm (J := J))) := by
    intro k
    obtain ⟨i, hi⟩ := hL.2 (some k)
    refine ⟨i, fun hmem => hi ?_⟩
    rw [Ideal.mem_comap] at hmem
    simpa [liftForm, rename_X] using hmem
  have hfin := length_localizedQuot_ne_top (P ⊔ Ideal.span {z}) (G'.comap (liftForm (J := J))) hRmin
  unfold divCycle
  rw [dite_eq_left hL, dite_eq_left ⟨hRmin, hRrel⟩]
  suffices key : multAt (blowUpOf P u ⊔ Ideal.span {liftForm z}) G' ≤
      multAt (P ⊔ Ideal.span {z}) (G'.comap (liftForm (J := J))) by
    exact_mod_cast ENat.toNat_le_toNat key hfin

  obtain ⟨C, f, hfinj, hfrac, hfcompat, hmax⟩ := h₄ R K ι J P hP u G' y hy hG' hrel x hx hG G₀ hG₀ W₀ hW₀
  have hQp : (blowUpOf P u).IsPrime := RingHom.ker_isPrime _
  have hSn : IsNoetherianRing (MRing ι R ⧸ P) := inferInstance
  have hAn : IsNoetherianRing (Localization.AtPrime G₀) :=
    IsLocalization.isNoetherianRing G₀.primeCompl _ hSn
  have hAinj : Function.Injective (algebraMap (MRing ι R ⧸ P) (Localization.AtPrime G₀)) :=
    IsLocalization.injective (Localization.AtPrime G₀) (Ideal.primeCompl_le_nonZeroDivisors G₀)
  have hdim : ringKrullDim (Localization.AtPrime G₀) = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height G₀ (Localization.AtPrime G₀)]
    have hmap : (G'.comap (liftForm (J := J))).map (Ideal.Quotient.mk P) = G₀ := by
      rw [← hG₀, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
    have hle : G₀.height ≤ 1 := hmap ▸ Ideal.map_height_le_one_of_mem_minimalPrimes hG
    have hne : G₀.height ≠ 0 := by
      rw [Ne, Ideal.height_eq_zero_iff_eq_bot]
      intro hbot
      have hxG : Ideal.Quotient.mk P x ∈ G₀ := by
        rw [← Ideal.mem_comap, hG₀]
        exact hG.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x))
      rw [hbot, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hxG
      exact hx hxG
    have h1 : G₀.height = 1 := le_antisymm hle (Order.one_le_iff_ne_zero.mpr hne)
    rw [h1]
    rfl
  set a : Localization.AtPrime G₀ :=
    algebraMap (MRing ι R ⧸ P) (Localization.AtPrime G₀) (Ideal.Quotient.mk P z) with ha_def
  have ha : a ≠ 0 := by
    intro h0
    rw [ha_def, ← map_zero (algebraMap (MRing ι R ⧸ P) (Localization.AtPrime G₀))] at h0
    exact hz (Ideal.Quotient.eq_zero_iff_mem.mp (hAinj h0))
  have hDom : IsDomain (Localization.AtPrime W₀) := inferInstance
  have hchain := length_quot_le_of_subring h₂ h₃ hdim C f hfinj hfrac hmax a ha
  rw [ha_def, hfcompat z] at hchain
  have e₁ := h₁ (MRing (extIdx ι J) R) (blowUpOf P u) W₀ (liftForm z)
  have e₂ := h₁ (MRing ι R) P G₀ z
  have key : ∀ (H : Ideal (MRing (extIdx ι J) R)) [H.IsPrime] (G : Ideal (MRing ι R)) [G.IsPrime],
      W₀.comap (Ideal.Quotient.mk (blowUpOf P u)) = H → G₀.comap (Ideal.Quotient.mk P) = G →
      multAt (blowUpOf P u ⊔ Ideal.span {liftForm z}) H ≤ multAt (P ⊔ Ideal.span {z}) G := by
    intro H _ G _ hH hGG
    subst hH
    subst hGG
    unfold multAt
    exact e₁.le.trans (hchain.trans e₂.ge)
  exact key _ _ hW₀ hG₀

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PIntermediateRingQuotLength
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

open Module Submodule
open scoped Pointwise

namespace IntermediateRingQuotLength

theorem smul_top_eq_span {A : Type*} [CommRing A] (a : A) :
    (a • ⊤ : Submodule A A) = Ideal.span {a} := by
  rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top]

theorem length_quot_smul_le {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [Ring.KrullDimLE 1 A] {M : Type*} [AddCommGroup M] [Module A M] (φ : A →ₗ[A] M)
    (hφ : Function.Injective φ) (htor : ∀ x : M, ∃ c : A, c ≠ 0 ∧ c • x ∈ LinearMap.range φ)
    {a : A} (ha : a ≠ 0) (hreg : Function.Injective fun x : M => a • x) :
    Module.length A (M ⧸ (a • ⊤ : Submodule A M)) ≤ Module.length A (A ⧸ Ideal.span {a}) := by
  rw [← smul_top_eq_span]
  have hLtop : Module.length A (A ⧸ (a • ⊤ : Submodule A A)) ≠ ⊤ := by
    rw [smul_top_eq_span]
    exact Module.length_ne_top_iff.mpr
      (isFiniteLength_quotient_span_singleton A (mem_nonZeroDivisors_of_ne_zero ha))
  let T : Submodule A M := a • ⊤
  have hfg : ∀ N : Submodule A M, N.FG → LinearMap.range φ ≤ N →
      Module.length A (N.map T.mkQ) ≤ Module.length A (A ⧸ (a • ⊤ : Submodule A A)) := by
    intro N hN hφN
    have : Module.Finite A N := Module.Finite.iff_fg.mpr hN
    let φN : A →ₗ[A] N := φ.codRestrict N fun y => hφN (LinearMap.mem_range_self φ y)
    have hφN' : Function.Injective φN := fun y z h => hφ (congrArg Subtype.val h)
    have hregN : Function.Injective fun x : N => a • x := fun x y h =>
      Subtype.ext (hreg (congrArg Subtype.val h))
    have hfin : IsFiniteLength A (N ⧸ LinearMap.range φN) := by
      refine GroundTheory.Heights₂.Heights.Model.TorsionFreeQuotientLength.isFiniteLength_of_torsion _
        fun q => ?_
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      obtain ⟨c, hc, y, hy⟩ := htor x
      refine ⟨c, hc, ?_⟩
      rw [← Quotient.mk_smul, Quotient.mk_eq_zero]
      exact ⟨y, Subtype.ext hy⟩
    have hle : (a • ⊤ : Submodule A N) ≤ LinearMap.ker (T.mkQ ∘ₗ N.subtype) := fun x hx => by
      obtain ⟨b, -, rfl⟩ := (mem_smul_pointwise_iff_exists _ _ _).mp hx
      simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, mkQ_apply,
        Quotient.mk_eq_zero, Submodule.coe_smul, Submodule.subtype_apply]
      exact smul_mem_pointwise_smul _ a ⊤ mem_top
    have hmap : N.map T.mkQ = LinearMap.range ((a • ⊤ : Submodule A N).liftQ _ hle) := by
      rw [range_liftQ, LinearMap.range_comp, range_subtype]
    rw [hmap, ← GroundTheory.Heights₂.Heights.Model.TorsionFreeQuotientLength.length_quot_smul_eq φN hφN'
      hregN hfin]
    exact Module.length_le_of_surjective _ (LinearMap.surjective_rangeRestrict _)
  let S : Set ℕ := {n | ∃ N : Submodule A M, N.FG ∧ LinearMap.range φ ≤ N ∧
    Module.length A (N.map T.mkQ) = n}
  have hSb : BddAbove S := ⟨(Module.length A (A ⧸ (a • ⊤ : Submodule A A))).toNat, by
    rintro n ⟨N, hN, hφN, hn⟩
    have := hfg N hN hφN
    rw [hn] at this
    simpa using ENat.toNat_le_toNat this hLtop⟩
  have hφfg : (LinearMap.range φ).FG := by
    rw [LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map φ
  have hne0 : Module.length A ((LinearMap.range φ).map T.mkQ) ≠ ⊤ :=
    ne_top_of_le_ne_top hLtop (hfg _ hφfg le_rfl)
  have hSne : S.Nonempty := ⟨_, LinearMap.range φ, hφfg, le_rfl, (ENat.natCast_toNat hne0).symm⟩
  obtain ⟨N₀, hN₀, hφN₀, hm⟩ := Nat.sSup_mem hSne hSb
  have htop : N₀.map T.mkQ = ⊤ := by
    refine eq_top_iff.mpr fun q _ => ?_
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    by_contra hx
    have hN₁ : (N₀ ⊔ span A {x}).FG := hN₀.sup (fg_span_singleton x)
    have hx1 : Submodule.Quotient.mk x ∈ (N₀ ⊔ span A {x}).map T.mkQ :=
      mem_map_of_mem (mem_sup_right (mem_span_singleton_self x))
    have hlt : N₀.map T.mkQ < (N₀ ⊔ span A {x}).map T.mkQ :=
      lt_of_le_of_ne (map_mono le_sup_left) fun h => hx (by rw [h]; exact hx1)
    have hne : Module.length A ((N₀ ⊔ span A {x}).map T.mkQ) ≠ ⊤ :=
      ne_top_of_le_ne_top hLtop (hfg _ hN₁ (hφN₀.trans le_sup_left))
    have h1 := le_csSup hSb ⟨_, hN₁, hφN₀.trans le_sup_left, (ENat.natCast_toNat hne).symm⟩
    have h2 : Module.length A (N₀.map T.mkQ) < Module.length A ((N₀ ⊔ span A {x}).map T.mkQ) := by
      rw [Module.length_submodule, Module.length_submodule]
      refine Order.height_strictMono hlt ?_
      rw [← Module.length_submodule, hm]
      exact ENat.natCast_lt_top _
    rw [hm, ← ENat.natCast_toNat hne] at h2
    exact absurd (ENat.natCast_lt_natCast.mp h2) (not_lt.mpr h1)
  calc Module.length A (M ⧸ T) = Module.length A (N₀.map T.mkQ) := by
        rw [htop, Module.length_top]
    _ ≤ Module.length A (A ⧸ (a • ⊤ : Submodule A A)) := hfg N₀ hN₀ hφN₀

end IntermediateRingQuotLength

theorem IntermediateRingQuotLength.proof : IntermediateRingQuotLength.Statement.{u} := by
  intro A C _ _ _ _ _ _ hdim hinj hfrac a ha
  have : Ring.KrullDimLE 1 A := Ring.krullDimLE_iff.mpr (by rw [hdim]; rfl)
  have hI : (Ideal.span {algebraMap A C a}).restrictScalars A = (a • ⊤ : Submodule A C) := by
    ext x
    simp only [Submodule.restrictScalars_mem, Ideal.mem_span_singleton',
      mem_smul_pointwise_iff_exists, mem_top, true_and, Algebra.smul_def, mul_comm]
  have hreg : Function.Injective fun x : C => a • x := fun x y h => by
    simp only [Algebra.smul_def] at h
    exact mul_left_cancel₀ (by simpa using (map_ne_zero_iff _ hinj).mpr ha) h
  have htor : ∀ x : C, ∃ c : A, c ≠ 0 ∧ c • x ∈ LinearMap.range (Algebra.linearMap A C) := by
    intro x
    obtain ⟨c, hc, y, hy⟩ := hfrac x
    exact ⟨c, hc, y, by simpa using hy⟩
  rw [← (Submodule.Quotient.restrictScalarsEquiv A (Ideal.span {algebraMap A C a})).length_eq, hI]
  exact IntermediateRingQuotLength.length_quot_smul_le (Algebra.linearMap A C) hinj htor ha hreg

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PLocalQuotFinsum
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem LocalQuotFinsum.proof (h : LocalQuotPrimes.Statement.{u}) : LocalQuotFinsum.Statement.{u} := by
  intro R _ P U _ hPU F F' hF hF' hFF'
  have hP := h R P U hPU
  set S : Set (Ideal R) := {G | G.IsPrime ∧ P ≤ G ∧ G ≤ U} with hS
  set T : Set (Ideal (localQuot P U)) := {p | p.IsPrime} with hT
  have h1 : ∑ᶠ G, F G = ∑ᶠ G ∈ S, F G := by
    rw [← finsum_mem_univ]
    apply finsum_mem_inter_support_eq'
    intro G hG
    exact ⟨fun _ => hF G hG, fun _ => Set.mem_univ G⟩
  have h2 : ∑ᶠ p, F' p = ∑ᶠ p ∈ T, F' p := by
    rw [← finsum_mem_univ]
    apply finsum_mem_inter_support_eq'
    intro p hp
    exact ⟨fun _ => hF' p hp, fun _ => Set.mem_univ p⟩
  have hbij : S.BijOn (fun G => G.map (localQuotMap P U)) T := by
    refine ⟨fun G hG => (hP.1 G hG.1 hG.2.1 hG.2.2).1, ?_, ?_⟩
    · intro G₁ hG₁ G₂ hG₂ he
      have e₁ := (hP.1 G₁ hG₁.1 hG₁.2.1 hG₁.2.2).2
      have e₂ := (hP.1 G₂ hG₂.1 hG₂.2.1 hG₂.2.2).2
      simp only at he
      rw [← e₁, ← e₂, he]
    · intro p hp
      obtain ⟨hle, hleU, hmap⟩ := hP.2 p hp
      exact ⟨p.comap (localQuotMap P U), ⟨by have : p.IsPrime := hp; exact Ideal.comap_isPrime _ p, hle, hleU⟩, hmap⟩
  rw [h1, h2]
  exact finsum_mem_eq_of_bijOn _ hbij fun G hG => hFF' G hG.1 hG.2.1 hG.2.2

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PLocCycleLocalQuot
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

private theorem length_self_eq_of_ringEquiv {S T : Type*} [CommRing S] [CommRing T] (e : S ≃+* T) :
    Module.length S S = Module.length T T := by
  rw [Module.length_eq_coheight, Module.length_eq_coheight]
  have := Ideal.coheight_comap_of_surjective (e : S →+* T) e.surjective ⊥
  have hb : Ideal.comap (e : S →+* T) ⊥ = ⊥ := Ideal.comap_bot_of_injective _ e.injective
  rw [hb] at this
  exact this

private theorem length_localizedModule_quot {R : Type*} [CommRing R] (J W : Ideal R) [W.IsPrime] :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (R ⧸ J)) =
      Module.length (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W)))
        (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W))) := by
  let S := Localization.AtPrime W
  have hJ : (J : Submodule R R).localized' S W.primeCompl (Algebra.linearMap R S) =
      J.map (algebraMap R S) := by
    rw [Submodule.localized'_eq_span, Ideal.map]
    rfl
  let e := (IsLocalizedModule.linearEquiv W.primeCompl
    ((J : Submodule R R).toLocalizedQuotient' S W.primeCompl (Algebra.linearMap R S))
    (LocalizedModule.mkLinearMap W.primeCompl (R ⧸ J))).extendScalarsOfIsLocalization W.primeCompl S
  rw [← e.length_eq, (Submodule.quotEquivOfEq _ _ hJ).length_eq]
  exact Module.length_eq_of_surjective Ideal.Quotient.mk_surjective

theorem LocCycleLocalQuot.proof (h₂ : LocalQuotPrimes.Statement.{u}) : LocCycleLocalQuot.Statement.{u} := by
  intro R _ P U _ J W hPJ hW hPW hWU
  obtain ⟨hup, hdown⟩ := h₂ R P U (hPW.trans hWU)
  obtain ⟨hpW, hcW⟩ := hup W hW hPW hWU

  have hmin : W ∈ J.minimalPrimes ↔ W.map (localQuotMap P U) ∈ (J.map (localQuotMap P U)).minimalPrimes := by
    constructor
    · rintro ⟨⟨-, hJW⟩, hm⟩
      refine ⟨⟨hpW, Ideal.map_mono hJW⟩, fun q hq hqW => ?_⟩
      have := hq.1
      obtain ⟨hPq, hqU, hqe⟩ := hdown q hq.1
      have h := hm ⟨Ideal.comap_isPrime _ q, Ideal.le_comap_map.trans (Ideal.comap_mono hq.2)⟩
        ((Ideal.comap_mono hqW).trans hcW.le)
      rw [← hqe]
      exact Ideal.map_mono h
    · rintro ⟨⟨-, hJW⟩, hm⟩
      refine ⟨⟨hW, Ideal.le_comap_map.trans ((Ideal.comap_mono hJW).trans hcW.le)⟩, fun Q hQ hQW => ?_⟩
      obtain ⟨hQp, hQc⟩ := hup Q hQ.1 (hPJ.trans hQ.2) (hQW.trans hWU)
      have h := hm ⟨hQp, Ideal.map_mono hQ.2⟩ (Ideal.map_mono hQW)
      rw [← hcW, ← hQc]
      exact Ideal.comap_mono h
  unfold locCycle
  by_cases h : W ∈ J.minimalPrimes
  swap
  · rw [dite_eq_right h, dite_eq_right (mt hmin.2 h)]
  rw [dite_eq_left h, dite_eq_left (hmin.1 h)]
  have := hW
  have := hpW
  set φ := localQuotMap P U with hφ
  obtain ⟨p, hp⟩ : ∃ p, W.map φ = p := ⟨_, rfl⟩
  rw [hp] at hpW hcW
  have := hpW
  have hφp : ∀ x : R, φ x ∈ p ↔ x ∈ W := fun x => by rw [← Ideal.mem_comap, hcW]

  have hrep : ∀ a : localQuot P U, ∃ r u : R, u ∉ U ∧ a * φ u = φ r := by
    intro a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨⟨r, u⟩, rfl⟩ := IsLocalization.mk'_surjective U.primeCompl b
    refine ⟨r, u, u.2, ?_⟩
    simp only [hφ, localQuotMap, RingHom.comp_apply, ← map_mul, IsLocalization.mk'_spec]
  have hnum : ∀ (t : localQuot P U) (r' u' : R), t ∉ p → u' ∉ U → t * φ u' = φ r' → r' ∉ W := by
    intro t r' u' ht hu' hr' hmem
    rw [← hφp, ← hr'] at hmem
    rcases hpW.mem_or_mem hmem with h | h
    · exact ht h
    · exact hu' (hWU ((hφp u').1 h))
  let ψ : (Localization.AtPrime W) →+* (Localization.AtPrime p) := Localization.localRingHom W p φ hcW.symm
  have hψ : Function.Surjective ψ := by
    intro z
    obtain ⟨⟨a, t⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl z
    obtain ⟨r, u, hu, hr⟩ := hrep a
    obtain ⟨r', u', hu', hr'⟩ := hrep t
    have hs : r' * u ∈ W.primeCompl :=
      W.primeCompl.mul_mem (hnum t r' u' t.2 hu' hr') fun h => hu (hWU h)
    refine ⟨IsLocalization.mk' _ (r * u') ⟨r' * u, hs⟩, ?_⟩
    rw [Localization.localRingHom_mk', IsLocalization.mk'_eq_iff_eq]
    congr 1
    simp only [map_mul]
    linear_combination (φ r) * hr' - (φ r') * hr

  have hker : Ideal.comap ψ ⊥ ≤ J.map (algebraMap R (Localization.AtPrime W)) := by
    intro x hx
    rw [Ideal.mem_comap, Ideal.mem_bot] at hx
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective W.primeCompl x
    rw [Localization.localRingHom_mk', IsLocalization.mk'_eq_zero_iff] at hx
    obtain ⟨⟨t, ht⟩, htr⟩ := hx
    obtain ⟨r', u', hu', hr'⟩ := hrep t
    have hr'W := hnum t r' u' ht hu' hr'
    have h0 : φ (r' * r) = 0 := by
      rw [map_mul, ← hr', mul_right_comm, htr, zero_mul]
    rw [hφ, localQuotMap, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem,
      IsLocalization.mem_map_algebraMap_iff U.primeCompl] at h0
    obtain ⟨⟨⟨i, hi⟩, v⟩, hv⟩ := h0
    rw [← map_mul, IsLocalization.eq_iff_exists U.primeCompl] at hv
    obtain ⟨c, hc⟩ := hv
    have hcW : (c : R) * r' * v ∈ W.primeCompl :=
      W.primeCompl.mul_mem (W.primeCompl.mul_mem (fun h => c.2 (hWU h)) hr'W) fun h => v.2 (hWU h)
    have hmemP : (c : R) * r' * v * r ∈ P := by
      have : (c : R) * (r' * r * v) = c * r' * v * r := by ring
      rw [← this, hc]
      exact P.mul_mem_left _ hi
    have hrJ : algebraMap R (Localization.AtPrime W) r ∈ J.map (algebraMap R (Localization.AtPrime W)) := by
      rw [← Ideal.unit_mul_mem_iff_mem _ (IsLocalization.map_units (Localization.AtPrime W) ⟨_, hcW⟩), ← map_mul]
      exact Ideal.mem_map_of_mem _ (hPJ hmemP)
    show IsLocalization.mk' (Localization.AtPrime W) r s ∈ _
    rw [IsLocalization.mk'_eq_mul_mk'_one]
    exact Ideal.mul_mem_right _ _ hrJ

  let : CommRing (Localization.AtPrime p) := inferInstance
  have hcomp : ψ.comp (algebraMap R (Localization.AtPrime W)) = (algebraMap (localQuot P U) (Localization.AtPrime p)).comp φ :=
    RingHom.ext fun x => Localization.localRingHom_to_map W p φ hcW.symm x
  have hI : (J.map φ).map (algebraMap (localQuot P U) (Localization.AtPrime p)) = (J.map (algebraMap R (Localization.AtPrime W))).map ψ := by
    rw [Ideal.map_map, Ideal.map_map, hcomp]
  let g := (Ideal.Quotient.mk ((J.map φ).map (algebraMap (localQuot P U) (Localization.AtPrime p)))).comp ψ
  have hg : Function.Surjective g := Ideal.Quotient.mk_surjective.comp hψ
  have hgk : J.map (algebraMap R (Localization.AtPrime W)) = RingHom.ker g := by
    rw [← RingHom.comap_ker, Ideal.mk_ker, hI, Ideal.comap_map_of_surjective _ hψ, sup_eq_left.mpr hker]
  have key := length_self_eq_of_ringEquiv ((Ideal.quotEquivOfEq hgk).trans (RingHom.quotientKerEquivOfSurjective hg))
  rw [← length_localizedModule_quot, ← length_localizedModule_quot] at key
  subst hp
  exact congrArg (fun n : ℕ∞ => ((n.toNat : ℕ) : ℤ)) key

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IrreducibleConnected.PGrowthOffHypersurfacePolynomial
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

theorem exists_eval_ne_zero_of_isOpen {d : ℕ} {Q : MvPolynomial (Fin d) ℂ} (hQ : Q ≠ 0)
    {V : Set (Fin d → ℂ)} (hV : IsOpen V) (hne : V.Nonempty) : ∃ t ∈ V, eval t Q ≠ 0 := by
  by_contra hall
  simp only [not_exists, not_and, not_not] at hall
  obtain ⟨t, ht⟩ := hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hV t ht
  apply hQ
  refine MvPolynomial.funext_set (fun i => Metric.ball (t i) ε) (fun i => ?_) (fun x hx => ?_)
  · exact infinite_of_mem_nhds (t i) (Metric.ball_mem_nhds (t i) hε)
  · rw [map_zero]
    apply hall
    apply hball
    rw [ball_pi t hε]
    exact hx

theorem dense_eval_ne_zero {d : ℕ} {Q : MvPolynomial (Fin d) ℂ} (hQ : Q ≠ 0) :
    Dense {y : Fin d → ℂ | eval y Q ≠ 0} := by
  rw [dense_iff_inter_open]
  intro V hV hne
  obtain ⟨t, htV, ht⟩ := exists_eval_ne_zero_of_isOpen hQ hV hne
  exact ⟨t, htV, ht⟩

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.MatrixCharts.StatementsCusp
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

def leadMinor {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) (i : ℕ) : ℝ :=
  (Matrix.of fun a b : Fin i =>
    if h : (a : ℕ) < d ∧ (b : ℕ) < d then S ⟨a, h.1⟩ ⟨b, h.2⟩ else 0).det

def periodBasis {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) : Fin (g + g) → Fin g → ℂ :=
  Fin.append (fun k => Pi.single k 1) (fun k => τ *ᵥ Pi.single k 1)

def periodGram {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) : Matrix (Fin (g + g)) (Fin (g + g)) ℝ :=
  Matrix.of fun i j => hermPair (τ.map Complex.im)⁻¹ (periodBasis τ i) (periodBasis τ j)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PChartImagMean
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Metric Real

noncomputable section

end

end GroundTheory.Heights₂.Heights
end

set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.Inter_ChartSpecCount : GroundTheory.Heights₂.Heights.Inter.ChartSpecCount.Statement :=
  @GroundTheory.Heights₂.Heights.Inter.ChartSpecCount.proof GroundTheory.Heights₂.Heights.Inter.ChartPrimElt.proof GroundTheory.Heights₂.Heights.Inter.LocAwaySpec.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.Inter_R1RegMaxSurj : GroundTheory.Heights₂.Heights.Inter.RegularityMaximalSurjective.Statement :=
  @GroundTheory.Heights₂.Heights.Inter.RegularityMaximalSurjective.proof GroundTheory.Heights₂.Heights.Inter.RegularityOrder.full GroundTheory.Heights₂.Heights.Inter.RegularityLocalPrime.full

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_MChartLocDim.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.MChartLocDim.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.MChartLocDim.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocQuot.proof GroundTheory.Heights₂.Heights.FieldNumbers.MChartDehomog.proof GroundTheory.Heights₂.Heights.FieldNumbers.MChartHomog.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_DegZeroLocNoetherian.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocNoetherian.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocNoetherian.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocQuot.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_ConeVarNumerator.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.ConeVarNumerator.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.ConeVarNumerator.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocQuot.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_MChartTrdeg.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.MChartTrdeg.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.MChartTrdeg.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.MChartHomog.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_DegZeroLocLocal.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocLocal.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocLocal.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocQuot.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalIntegral.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.SemilocalIntegral.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.SemilocalIntegral.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.ValuativeCentre.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_HomLocRingIsLocal.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingIsLocal.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingIsLocal.proof.{u} GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingMem.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_LocalCoeffLocal.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.LocalCoeffLocal.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.LocalCoeffLocal.proof.{u} GroundTheory.Heights₂.Heights.NumbersDVR.LocCycleSpanMul.proof GroundTheory.Heights₂.Heights.NumbersDVR.LocCyclePos.proof GroundTheory.Heights₂.Heights.NumbersDVR.MinimalPrimesSpanSingleton.proof GroundTheory.Heights₂.Heights.NumbersDVR.LocalDomainDimTwo.proof GroundTheory.Heights₂.Heights.NumbersDVR.DimTwoSumReading.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_SegreFlagClosureTrdeg : GroundTheory.Heights₂.Heights.NumbersDVR.SegreFlagClosureTrdeg.Statement :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.SegreFlagClosureTrdeg.proof GroundTheory.Heights₂.Heights.NumbersDVR.SegreFlagConeAlg.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_HomLocRingNoetherian.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingNoetherian.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingNoetherian.proof.{u} GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingMem.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_LocCycleLocalQuot.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.LocCycleLocalQuot.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.LocCycleLocalQuot.proof.{u} GroundTheory.Heights₂.Heights.NumbersDVR.LocalQuotPrimes.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_C3BlowUpPieces.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpDecomposition.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpDecomposition.proof.{u} GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpModel.full GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpStrictTransform.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_BlowUpOrderLe.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpOrderLe.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpOrderLe.proof.{u} GroundTheory.Heights₂.Heights.NumbersDVR.LocalizedQuotLength.proof GroundTheory.Heights₂.Heights.NumbersDVR.LengthMapIdealLe.proof GroundTheory.Heights₂.Heights.NumbersDVR.IntermediateRingQuotLength.proof GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpLocalChart.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_BlowUpHorizontalMult.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpHorizontalMult.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpHorizontalMult.proof.{u} GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpHorizontalMinimal.full GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpHorizontalChartLength.full

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_LocalQuotFinsum.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.LocalQuotFinsum.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.LocalQuotFinsum.proof.{u} GroundTheory.Heights₂.Heights.NumbersDVR.LocalQuotPrimes.proof
