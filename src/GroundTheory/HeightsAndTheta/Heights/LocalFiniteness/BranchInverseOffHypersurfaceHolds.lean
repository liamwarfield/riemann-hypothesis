module

public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.ParametrisationSheetsConnectedHolds
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRegLogDensNonneg
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSectionCountDropTerm

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PUniformiserLocallyInjective
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Topology

theorem UniformiserLocallyInjective.proof (hgrad : UniformiserGradientIndependent.Statement)
    (hchart : PolynomialChartInjective.Statement) : UniformiserLocallyInjective.Statement := by
  intro σ _ I w t hI hic hdim hw ht
  obtain ⟨k, f, hk, hfI, hli⟩ := hgrad σ I w t hI hic hdim hw ht
  obtain ⟨U, hU, hinj⟩ := hchart σ k t f w hk hli
  refine ⟨U, hU, hinj.mono ?_⟩
  rintro z ⟨hz, hzU⟩
  exact ⟨hzU, fun j ↦ hz (f j) (hfI j)⟩

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalModelDisc
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem NormalModelDisc.proof (hreg : NormalCurveRegularPoint.Statement) : NormalModelDisc.Statement := by
  intro n J M w _ hdim hw
  have hdim' : ringKrullDim (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal) = (1 : ℕ) := by
    rw [M.ringKrullDim_eq, hdim]
  obtain ⟨A, O, V, g, hO, -, hwV, hg, hAg, hZV⟩ :=
    hreg (Fin n ⊕ Fin M.m) M.ideal w M.isPrime M.isIntegrallyClosed hdim' hw
  have hwg : w ∈ g '' O := hZV ▸ ⟨hw, hwV⟩
  obtain ⟨y₀, hy₀, hgy₀⟩ := hwg
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hO y₀ hy₀
  have hmem : ∀ τ ∈ Metric.ball (0 : Fin 1 → ℂ) r, y₀ + τ ∈ O := fun τ hτ ↦ hball (by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
    simpa using hτ)
  refine ⟨r, hr, fun τ ↦ g (y₀ + τ), ?_, ?_, ?_, ?_⟩
  · intro τ hτ
    exact ((hg _ (hmem τ hτ)).differentiableAt.comp τ
      (differentiableAt_const y₀ |>.add differentiableAt_id)).differentiableWithinAt
  · intro s hs t ht hst
    have h := congrArg A hst
    simp only at h
    rw [hAg _ (hmem s hs), hAg _ (hmem t ht)] at h
    exact add_left_cancel h
  · intro τ hτ
    have h : g (y₀ + τ) ∈ g '' O := ⟨_, hmem τ hτ, rfl⟩
    rw [← hZV] at h
    exact h.1
  · simp [hgy₀]

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCMLengthParameters
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing

universe u

theorem mem_nonZeroDivisors_of_notMem_of_minimalPrimes_eq (hCM : CMRegularElement.Statement.{u})
    {B : Type u} [CommRing B] [IsCohenMacaulayLocalRing B] {P : Ideal B} (hmin : minimalPrimes B = {P})
    {s : B} (hs : s ∉ P) : s ∈ nonZeroDivisors B := by
  by_cases hsm : s ∈ maximalIdeal B
  · refine (hCM B s hsm fun p hp => ?_).1
    rw [hmin, Set.mem_singleton_iff] at hp
    rwa [hp]
  · exact ((IsLocalRing.notMem_maximalIdeal.1 hsm)).mem_nonZeroDivisors

theorem length_localization_maximalIdeal (B : Type u) [CommRing B] [IsLocalRing B] :
    Module.length (Localization.AtPrime (maximalIdeal B)) (Localization.AtPrime (maximalIdeal B)) =
      Module.length B B := by
  have hU : (maximalIdeal B).primeCompl ≤ IsUnit.submonoid B := fun s hs =>
    IsLocalRing.notMem_maximalIdeal.1 hs
  let e := IsLocalization.atUnits B (maximalIdeal B).primeCompl
    (S := Localization.AtPrime (maximalIdeal B)) hU
  have hsurj : Function.Surjective (algebraMap B (Localization.AtPrime (maximalIdeal B))) :=
    e.surjective
  rw [← Module.length_eq_of_surjective (S := B) hsurj]
  exact e.toLinearEquiv.length_eq.symm

theorem withBot_natCast_le_of_add_one_le {k : ℕ} {D : WithBot ℕ∞}
    (h : ((k + 1 : ℕ) : WithBot ℕ∞) ≤ D + 1) : ((k : ℕ) : WithBot ℕ∞) ≤ D := by
  induction D using WithBot.recBotCoe with
  | bot => exact absurd h (by simp)
  | coe e =>
    induction e using ENat.recTopCoe with
    | top => exact WithBot.coe_le_coe.2 le_top
    | coe n =>
      have h' : k + 1 ≤ n + 1 := by exact_mod_cast h
      exact_mod_cast (by omega : k ≤ n)

theorem spanFinrank_span_range_le {R : Type*} [CommRing R] {k : ℕ} (z : Fin k → R) :
    (Ideal.span (Set.range z)).spanFinrank ≤ k := by
  classical
  refine (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range z)).trans ?_
  have hz : Set.range z = ((Finset.univ.image z : Finset R) : Set R) := by simp
  rw [hz, Set.ncard_coe_finset]
  exact Finset.card_image_le.trans (by simp)

theorem span_range_eq_span_range_succ {R : Type*} [CommRing R] {k : ℕ} (z : Fin (k + 1) → R) (h0 : z 0 = 0) :
    Ideal.span (Set.range z) = Ideal.span (Set.range fun j : Fin k => z j.succ) := by
  refine le_antisymm (Ideal.span_le.2 ?_) (Ideal.span_mono ?_)
  · rintro _ ⟨i, rfl⟩
    cases i using Fin.cases with
    | zero => rw [h0]; exact Ideal.zero_mem _
    | succ j => exact Ideal.subset_span ⟨j, rfl⟩
  · rintro _ ⟨j, rfl⟩
    exact ⟨j.succ, rfl⟩

theorem maximalIdeal_quotient_eq_span {B : Type u} [CommRing B] [IsLocalRing B] {I : Ideal B} {k : ℕ}
    (x : Fin k → B) (hI : Ideal.span (Set.range x) ⊔ I = maximalIdeal B) [IsLocalRing (B ⧸ I)] :
    maximalIdeal (B ⧸ I) = Ideal.span (Set.range fun i => Ideal.Quotient.mk I (x i)) := by
  rw [← map_maximalIdeal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective, ← hI, Ideal.map_sup,
    Ideal.map_span, ← Set.range_comp, Ideal.map_quotient_self, sup_bot_eq]
  rfl

theorem notMem_and_isPrime_sup_span {B : Type u} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    {P : Ideal B} [hP : P.IsPrime] {k : ℕ} (x : Fin (k + 1) → B)
    (hdim : ringKrullDim (B ⧸ P) = ((k + 1 : ℕ) : WithBot ℕ∞))
    (hmax : Ideal.span (Set.range x) ⊔ P = maximalIdeal B) :
    x 0 ∉ P ∧ (P ⊔ Ideal.span {x 0}).IsPrime ∧
      ringKrullDim (B ⧸ (P ⊔ Ideal.span {x 0})) = ((k : ℕ) : WithBot ℕ∞) := by
  have hPm : P ≤ maximalIdeal B := hmax ▸ le_sup_right
  have hxm : ∀ i, x i ∈ maximalIdeal B := fun i => hmax ▸ Ideal.mem_sup_left (Ideal.subset_span ⟨i, rfl⟩)
  have : Nontrivial (B ⧸ P) := Ideal.Quotient.nontrivial_iff.2 hP.ne_top
  have : IsLocalRing (B ⧸ P) := IsLocalRing.of_surjective' (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  have hA := maximalIdeal_quotient_eq_span x hmax
  have hy : x 0 ∉ P := by
    intro hyP
    have h0 : Ideal.Quotient.mk P (x 0) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hyP
    have hle := ringKrullDim_le_spanFinrank_maximalIdeal (B ⧸ P)
    rw [hA, span_range_eq_span_range_succ (fun i => Ideal.Quotient.mk P (x i)) h0, hdim] at hle
    have hk := spanFinrank_span_range_le (fun j : Fin k => Ideal.Quotient.mk P (x j.succ))
    have h2 : ((k + 1 : ℕ) : WithBot ℕ∞) ≤ ((k : ℕ) : WithBot ℕ∞) := hle.trans (by exact_mod_cast hk)
    have h3 : k + 1 ≤ k := by exact_mod_cast h2
    omega
  set Q₀ := P ⊔ Ideal.span {x 0} with hQ₀
  have hQ₀m : Q₀ ≤ maximalIdeal B := sup_le hPm ((Ideal.span_singleton_le_iff_mem _).2 (hxm 0))
  have hmaxQ : Ideal.span (Set.range x) ⊔ Q₀ = maximalIdeal B :=
    le_antisymm (sup_le (hmax ▸ le_sup_left) hQ₀m) (hmax ▸ sup_le_sup_left le_sup_left _)
  have : Nontrivial (B ⧸ Q₀) := Ideal.Quotient.nontrivial_iff.2 fun h =>
    (IsLocalRing.maximalIdeal.isMaximal B).ne_top (top_le_iff.1 (h ▸ hQ₀m))
  have : IsLocalRing (B ⧸ Q₀) := IsLocalRing.of_surjective' (Ideal.Quotient.mk Q₀) Ideal.Quotient.mk_surjective
  have hA' := maximalIdeal_quotient_eq_span x hmaxQ
  have h0' : Ideal.Quotient.mk Q₀ (x 0) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  rw [span_range_eq_span_range_succ (fun i => Ideal.Quotient.mk Q₀ (x i)) h0'] at hA'
  have hfin : (maximalIdeal (B ⧸ Q₀)).spanFinrank ≤ k := hA' ▸ spanFinrank_span_range_le _
  have hge : ((k : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (B ⧸ Q₀) := by
    have e : (B ⧸ P) ⧸ Ideal.span {Ideal.Quotient.mk P (x 0)} ≃+* B ⧸ Q₀ :=
      (Ideal.quotEquivOfEq (by rw [Ideal.map_span, Set.image_singleton])).trans
        (DoubleQuot.quotQuotEquivQuotSup P (Ideal.span {x 0}))
    have hj : ({Ideal.Quotient.mk P (x 0)} : Set (B ⧸ P)) ⊆ Ring.jacobson (B ⧸ P) := by
      rw [Set.singleton_subset_iff, IsLocalRing.ringJacobson_eq_maximalIdeal, hA]
      exact Ideal.subset_span ⟨0, rfl⟩
    have h := ringKrullDim_le_ringKrullDim_quotient_add_encard _ hj
    rw [hdim, Set.encard_singleton, ringKrullDim_eq_of_ringEquiv e] at h
    exact withBot_natCast_le_of_add_one_le (by exact_mod_cast h)
  have hle : ringKrullDim (B ⧸ Q₀) ≤ ((k : ℕ) : WithBot ℕ∞) :=
    (ringKrullDim_le_spanFinrank_maximalIdeal _).trans (by exact_mod_cast hfin)
  have : IsRegularLocalRing (B ⧸ Q₀) :=
    IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ ((by exact_mod_cast hfin :
      ((maximalIdeal (B ⧸ Q₀)).spanFinrank : WithBot ℕ∞) ≤ ((k : ℕ) : WithBot ℕ∞)).trans hge)
  have := GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.isDomain (R := B ⧸ Q₀)
  exact ⟨hy, (Ideal.Quotient.isDomain_iff_prime Q₀).1 inferInstance, le_antisymm hle hge⟩

theorem CMLengthParameters.proof (hCM : CMRegularElement.Statement.{u})
    (hLen : LengthLocalizedQuotient.Statement.{u}) : CMLengthParameters.Statement.{u} := by
  suffices h : ∀ d : ℕ, ∀ (B : Type u) [CommRing B] [IsCohenMacaulayLocalRing B] (P : Ideal B) [P.IsPrime]
      (x : Fin d → B), minimalPrimes B = {P} → ringKrullDim (B ⧸ P) = (d : ℕ) →
      Ideal.span (Set.range x) ⊔ P = maximalIdeal B →
        Module.length B (B ⧸ Ideal.span (Set.range x)) =
          Module.length (Localization.AtPrime P) (Localization.AtPrime P) from
    fun B _ _ P _ d x => h d B P x
  intro d
  induction d with
  | zero =>
    intro B _ _ P _ x _ _ hmax
    have hx : Ideal.span (Set.range x) = ⊥ := by rw [Set.range_eq_empty, Ideal.span_empty]
    rw [hx, bot_sup_eq] at hmax
    subst hmax
    rw [hx, length_localization_maximalIdeal]
    exact (Submodule.quotEquivOfEqBot ⊥ rfl).length_eq
  | succ k ih =>
    intro B _ _ P _ x hmin hdim hmax
    obtain ⟨hyP, hQ₀, hdimQ⟩ := notMem_and_isPrime_sup_span x hdim hmax
    set y := x 0 with hy
    set Q₀ := P ⊔ Ideal.span {y} with hQ₀def
    have hxm : ∀ i, x i ∈ maximalIdeal B := fun i => hmax ▸ Ideal.mem_sup_left (Ideal.subset_span ⟨i, rfl⟩)
    have hnzd : ∀ s ∉ P, s ∈ nonZeroDivisors B := fun s hs =>
      mem_nonZeroDivisors_of_notMem_of_minimalPrimes_eq hCM hmin hs
    have hyQ : Ideal.span {y} ≤ Q₀ := le_sup_right

    have hB'CM : IsCohenMacaulayLocalRing (B ⧸ Ideal.span {y}) := (hCM B y (hxm 0) fun p hp => by
      rw [hmin, Set.mem_singleton_iff] at hp
      rwa [hp]).2
    set f := Ideal.Quotient.mk (Ideal.span {y}) with hf
    have hfs : Function.Surjective f := Ideal.Quotient.mk_surjective
    have hker : RingHom.ker f ≤ Q₀ := by rw [hf, Ideal.mk_ker]; exact hyQ
    set P' := Q₀.map f with hP'def
    have hP' : P'.IsPrime := Ideal.map_isPrime_of_surjective hfs hker
    have hcomap : P'.comap f = Q₀ := by
      rw [hP'def, Ideal.comap_map_of_surjective' f hfs, sup_eq_left.2 hker]

    have hall : ∀ q : Ideal (B ⧸ Ideal.span {y}), q.IsPrime → P' ≤ q := by
      intro q hq
      have hqc : (q.comap f).IsPrime := Ideal.comap_isPrime f q
      obtain ⟨p, hp, hpq⟩ := Ideal.exists_minimalPrimes_le (bot_le : ⊥ ≤ q.comap f)
      have hpP : p = P := by
        have : p ∈ minimalPrimes B := hp
        rw [hmin, Set.mem_singleton_iff] at this
        exact this
      subst hpP
      have hyq : Ideal.span {y} ≤ q.comap f := fun z hz => by
        rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hz]
        exact q.zero_mem
      rw [hP'def, Ideal.map_le_iff_le_comap]
      exact sup_le hpq hyq
    have hmin' : minimalPrimes (B ⧸ Ideal.span {y}) = {P'} := by
      ext q
      rw [Set.mem_singleton_iff]
      constructor
      · intro hq
        exact le_antisymm (hq.2 ⟨hP', bot_le⟩ (hall q hq.1.1)) (hall q hq.1.1)
      · rintro rfl
        exact ⟨⟨hP', bot_le⟩, fun q hq _ => hall q hq.1⟩
    have hdim' : ringKrullDim ((B ⧸ Ideal.span {y}) ⧸ P') = (k : ℕ) := by
      rw [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hyQ)]
      exact hdimQ

    set x' : Fin k → B ⧸ Ideal.span {y} := fun j => f (x j.succ) with hx'
    have hmB' : (maximalIdeal B).map f = maximalIdeal (B ⧸ Ideal.span {y}) :=
      map_maximalIdeal_of_surjective f hfs
    have hmax' : Ideal.span (Set.range x') ⊔ P' = maximalIdeal (B ⧸ Ideal.span {y}) := by
      apply le_antisymm
      · refine sup_le (Ideal.span_le.2 ?_) (IsLocalRing.le_maximalIdeal hP'.ne_top)
        rintro _ ⟨j, rfl⟩
        rw [← hmB']
        exact Ideal.mem_map_of_mem f (hxm _)
      · rw [← hmB', Ideal.map_le_iff_le_comap, ← hmax]
        refine sup_le (Ideal.span_le.2 ?_) fun p hp => ?_
        · rintro _ ⟨i, rfl⟩
          cases i using Fin.cases with
          | zero =>
            exact Ideal.mem_sup_right (Ideal.mem_map_of_mem f (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
          | succ j => exact Ideal.mem_sup_left (Ideal.subset_span ⟨j, rfl⟩)
        · exact Ideal.mem_sup_right (Ideal.mem_map_of_mem f (Ideal.mem_sup_left hp))
    have key := ih (B ⧸ Ideal.span {y}) P' x' hmin' hdim' hmax'
    rw [hLen B P y hmin hnzd hyP P' hcomap] at key
    rw [← key]

    have hyx : Ideal.span {y} ≤ Ideal.span (Set.range x) :=
      (Ideal.span_singleton_le_iff_mem _).2 (Ideal.subset_span ⟨0, rfl⟩)
    have hJ : (Ideal.span (Set.range x)).map (Ideal.Quotient.mkₐ B (Ideal.span {y})) = Ideal.span (Set.range x') := by
      rw [Ideal.map_span, ← Set.range_comp]
      refine span_range_eq_span_range_succ _ ?_
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
    calc Module.length B (B ⧸ Ideal.span (Set.range x))
        = Module.length B ((B ⧸ Ideal.span {y}) ⧸
            (Ideal.span (Set.range x)).map (Ideal.Quotient.mkₐ B (Ideal.span {y}))) :=
          (DoubleQuot.quotQuotEquivQuotOfLEₐ B hyx).toLinearEquiv.length_eq.symm
      _ = Module.length (B ⧸ Ideal.span {y}) ((B ⧸ Ideal.span {y}) ⧸
            (Ideal.span (Set.range x)).map (Ideal.Quotient.mkₐ B (Ideal.span {y}))) :=
          Module.length_eq_of_surjective Ideal.Quotient.mk_surjective
      _ = Module.length (B ⧸ Ideal.span {y}) ((B ⧸ Ideal.span {y}) ⧸ Ideal.span (Set.range x')) := by
          rw [hJ]

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCMLocusOpen
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem CMLocusOpen.proof (hcrit : CMProjDimCriterion.Statement) (hpd : ProjDimSpread.Statement)
    (hht : IdealHeightSpread.Statement) : CMLocusOpen.Statement := by
  intro n I P _ hIP hCM
  obtain ⟨ℓ, hℓ, hℓht⟩ := (hcrit n I P hIP).mp hCM
  obtain ⟨g₁, hg₁P, hg₁⟩ := hpd (MvPolynomial (Fin n) ℂ) I P ℓ hℓ
  obtain ⟨g₂, hg₂P, hg₂⟩ := hht (MvPolynomial (Fin n) ℂ) I P hIP
  refine ⟨g₁ * g₂, fun h => (‹P.IsPrime›.mem_or_mem h).elim hg₁P hg₂P, fun Q _ hIQ hgQ => ?_⟩
  have h₁ : g₁ ∉ Q := fun h => hgQ (Q.mul_mem_right g₂ h)
  have h₂ : g₂ ∉ Q := fun h => hgQ (Q.mul_mem_left g₁ h)
  exact (hcrit n I Q hIQ).mpr ⟨ℓ, hg₁ Q h₁, hℓht.trans (hg₂ Q hIQ h₂)⟩

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCurveNormalisationLength
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

variable {n : ℕ}

theorem length_quotient_sup_span {L : Type} [CommRing L] (J : Ideal L) (g : L) :
    Module.length L (L ⧸ (J ⊔ Ideal.span {g})) =
      Module.length (L ⧸ J) ((L ⧸ J) ⧸ Ideal.span {Ideal.Quotient.mk J g}) := by
  have hK : (Ideal.span {g}).map (Ideal.Quotient.mkₐ L J) = Ideal.span {Ideal.Quotient.mk J g} := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  rw [← (DoubleQuot.quotQuotEquivQuotSupₐ L J (Ideal.span {g})).toLinearEquiv.length_eq, hK]
  exact Module.length_eq_of_surjective Ideal.Quotient.mk_surjective

theorem length_localization_eq_length_curveLocalRing (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ)
    (f : MvPolynomial (Fin n) ℂ) :
    Module.length (Localization.AtPrime (RingHom.ker (eval q)))
        (Localization.AtPrime (RingHom.ker (eval q)) ⧸ (I ⊔ Ideal.span {f}).map
          (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q))))) =
      Module.length (curveLocalRing I q)
        (curveLocalRing I q ⧸ Ideal.span {algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f}) := by
  rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  exact length_quotient_sup_span _ _

theorem length_quotient_ne_top {O : Type} [CommRing O] [IsNoetherianRing O] [IsLocalRing O]
    (hdim : ringKrullDim O = 1) {x : O} (hx : x ∈ nonZeroDivisors O) :
    Module.length O (O ⧸ Ideal.span {x}) ≠ ⊤ := by
  by_cases hm : x ∈ IsLocalRing.maximalIdeal O
  · have h := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors hx hm
    rw [hdim] at h
    have h0 : ringKrullDim (O ⧸ Ideal.span {x}) ≤ (0 : ℕ) := by
      generalize ringKrullDim (O ⧸ Ideal.span {x}) = d at h ⊢
      induction d using WithBot.recBotCoe with
      | bot => exact bot_le
      | coe k =>
        have h' : k + 1 = 1 := by exact_mod_cast h
        induction k using ENat.recTopCoe with
        | top => simp at h'
        | coe m =>
          have hm : m + 1 = 1 := by exact_mod_cast h'
          have : m = 0 := by omega
          subst this
          simp
    have : Ring.KrullDimLE 0 (O ⧸ Ideal.span {x}) := Ring.krullDimLE_iff.2 h0
    have := IsNoetherianRing.isArtinianRing_of_krullDimLE_zero (R := O ⧸ Ideal.span {x})
    rw [Module.length_eq_of_surjective (R := O ⧸ Ideal.span {x}) Ideal.Quotient.mk_surjective]
    exact Module.length_ne_top
  · have hu : IsUnit x := by simpa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hm
    rw [Ideal.span_singleton_eq_top.2 hu,
      Module.length_eq_zero_iff.2 (Ideal.Quotient.subsingleton_iff.2 rfl)]
    exact ENat.zero_ne_top

theorem CurveNormalisationLength.proof (hFin : CurveNormalisationFinite.Statement)
    (hQ : CurveNormalisationQuotientLength.Statement) (hE : ExtensionQuotientLength.Statement) :
    CurveNormalisationLength.Statement := by
  intro n I q f hrad hdim hf
  set O := curveLocalRing I q
  set f' := algebraMap (MvPolynomial (Fin n) ℂ) O f
  have : Nontrivial O := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    rw [ringKrullDim_eq_bot_of_subsingleton] at hdim
    exact WithBot.bot_ne_coe hdim
  have : IsLocalRing O := IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have : Module.Finite O (curveNormalisation I q) := hFin n I q hrad
  have hfin := length_quotient_ne_top hdim hf

  have hnzd : algebraMap O (curveNormalisation I q) f' ∈ nonZeroDivisors (curveNormalisation I q) := by
    let ι : curveNormalisation I q →+* FractionRing O :=
      (integralClosure O (FractionRing O)).val.toRingHom
    refine mem_nonZeroDivisors_of_injective (f := ι) Subtype.val_injective ?_
    exact (IsLocalization.map_units (FractionRing O) (⟨f', hf⟩ : nonZeroDivisors O)).mem_nonZeroDivisors
  have hEq := hE O (curveNormalisation I q) f' (algebraMap_curveNormalisation_injective I q) hnzd
    (hQ n I q hrad hdim)
  rw [localMult, dite_eq_left (isPrime_ker_eval q), length_localization_eq_length_curveLocalRing,
    ENat.natCast_toNat hfin, hEq]
  exact GroundTheory.Heights₂.Heights.Vertical.LengthDecomp.proof O (curveNormalisation I q) _ (hEq ▸ hfin)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCurveRegularOffFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

theorem CurveRegularOffFinite.proof (hG : FrameGraphGeneric.Statement)
    (hP : CurveProperClosedFinite.Statement) : CurveRegularOffFinite.Statement := by
  intro n W hW hdim
  have hd : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = ((1 : ℕ) : WithBot ℕ∞) := by
    rw [hdim]; rfl
  let b := EuclideanSpace.basisFun (Fin n) ℂ
  obtain ⟨I₀, q, hcard, hqW, hreg⟩ := hG n 1 W hW hd b
  obtain ⟨i₀, hI₀⟩ := Finset.card_eq_one.mp hcard
  have hi₀ : i₀ ∈ I₀ := by rw [hI₀]; exact Finset.mem_singleton_self i₀
  have hsub : ∀ j : I₀, j = ⟨i₀, hi₀⟩ := fun j => Subtype.ext (Finset.mem_singleton.mp (hI₀ ▸ j.2))
  have hKW : ¬ Ideal.span {q} ≤ W := fun h => hqW (h (Ideal.subset_span rfl))
  refine ⟨zeroSet W ∩ zeroSet (Ideal.span {q}), hP n W _ hW hdim hKW, ?_⟩
  intro x hx hxF
  have hqx : eval x q ≠ 0 := by
    intro h0
    refine hxF ⟨hx, fun p hp => ?_⟩
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hp
    simp [h0]

  let T : (Fin n → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    ((EuclideanSpace.equiv (Fin n) ℂ).symm : (Fin n → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n))
  let S : EuclideanSpace ℂ (Fin n) →L[ℂ] (Fin n → ℂ) :=
    ((EuclideanSpace.equiv (Fin n) ℂ) : EuclideanSpace ℂ (Fin n) →L[ℂ] (Fin n → ℂ))
  have hST : ∀ y, S (T y) = y := fun y => rfl
  have hTS : ∀ w, T (S w) = w := fun w => rfl
  have hZ : ∀ y : Fin n → ℂ, y ∈ zeroSet W ↔ T y ∈ zeroSetEuc W := fun y => Iff.rfl
  obtain ⟨Ω, V, g, hΩ, hV, hxV, hg, hproj, hgraph⟩ := hreg (T x) ((hZ x).mp hx) hqx

  let ι : ℂ →L[ℂ] (I₀ → ℂ) := ContinuousLinearMap.pi fun _ : I₀ => ContinuousLinearMap.id ℂ ℂ
  let A : (Fin n → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) i₀
  have hO : IsOpen (ι ⁻¹' Ω) := hΩ.preimage ι.continuous
  refine ⟨A, ι ⁻¹' Ω, T ⁻¹' V, fun y => S (g (ι y)), hO, hV.preimage T.continuous, hxV, ?_, ?_, ?_⟩
  · exact (S.differentiable.comp_differentiableOn
      (hg.comp ι.differentiable.differentiableOn fun y hy => hy)).analyticOnNhd hO
  · intro y hy
    have h1 := congrFun (hproj (ι y) hy) ⟨i₀, hi₀⟩
    simp only [frameProj, b, EuclideanSpace.basisFun_inner] at h1
    exact h1
  · ext x'
    constructor
    · rintro ⟨hx'Z, hx'V⟩
      have hmem : T x' ∈ zeroSetEuc W ∩ V := ⟨(hZ x').mp hx'Z, hx'V⟩
      rw [hgraph] at hmem
      obtain ⟨u, hu, hgu⟩ := hmem
      have hιu : ι (u ⟨i₀, hi₀⟩) = u := funext fun j => by rw [hsub j]; rfl
      refine ⟨u ⟨i₀, hi₀⟩, ?_, ?_⟩
      · show ι _ ∈ Ω
        rwa [hιu]
      · simp only [hιu, hgu, hST]
    · rintro ⟨y, hy, rfl⟩
      have hmem : g (ι y) ∈ zeroSetEuc W ∩ V := hgraph ▸ Set.mem_image_of_mem g hy
      exact ⟨(hZ _).mpr (by rw [hTS]; exact hmem.1), by show T (S (g (ι y))) ∈ V; rw [hTS]; exact hmem.2⟩

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDivisorRegularGeneric
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology ComplexSets

noncomputable section

theorem DivisorRegularGeneric.proof (hG : FrameGraphGeneric.Statement) : DivisorRegularGeneric.Statement := by
  classical
  intro n d J u hJ hdim hu
  set L : Ideal (MvPolynomial (Fin n) ℂ) := J ⊔ Ideal.span {linForm u} with hL
  have hfinM : L.minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ L
  set T := hfinM.toFinset with hT
  have hmemT : ∀ W, W ∈ T ↔ W ∈ L.minimalPrimes := fun W => hfinM.mem_toFinset
  have hevL : ∀ x : Fin n → ℂ, eval x (linForm u) = linEval u x := fun x => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [linForm, linEval, map_sum]

  have hdimW : ∀ W ∈ L.minimalPrimes, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = (d : ℕ) := by
    intro W hW
    have key := ringKrullDim_quotient_minimalPrime_add_one hu hW (fun h => by
      rw [hdim] at h
      exact ENat.natCast_ne_top _ (WithBot.coe_injective h))
    rw [hdim] at key
    exact ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_withBot_eq_of_add_one key
  choose! hh hhW hhchart using fun W (hW : W ∈ L.minimalPrimes) =>
    graphChart_of_frameGraphGeneric hG W hW.1.1 (hdimW W hW)

  have hsep : ∀ W ∈ L.minimalPrimes, ∀ V ∈ L.minimalPrimes, W ≠ V → ∃ g ∈ V, g ∉ W := by
    intro W hW V hV hne
    by_contra hcon
    push Not at hcon
    exact hne (le_antisymm (hW.2 hV.1 hcon) hcon)
  choose! gg hggV hggW using hsep
  set e : Ideal (MvPolynomial (Fin n) ℂ) → MvPolynomial (Fin n) ℂ := fun W => ∏ V ∈ T.erase W, gg W V with he
  have heW : ∀ W ∈ L.minimalPrimes, e W ∉ W := by
    intro W hW hmem
    have : W.IsPrime := hW.1.1
    obtain ⟨V, hV, hgV⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    exact hggW W hW V ((hmemT V).mp (Finset.mem_of_mem_erase hV)) (Finset.ne_of_mem_erase hV).symm hgV
  have heV : ∀ W ∈ L.minimalPrimes, ∀ V ∈ L.minimalPrimes, W ≠ V → e W ∈ V := by
    intro W hW V hV hne
    have : V.IsPrime := hV.1.1
    exact Ideal.IsPrime.prod_mem_iff.mpr
      ⟨V, Finset.mem_erase.mpr ⟨hne.symm, (hmemT V).mpr hV⟩, hggV W hW V hV hne⟩
  set f : MvPolynomial (Fin n) ℂ := ∑ W ∈ T, hh W * e W with hf
  have hsplit : ∀ W ∈ T, f = hh W * e W + ∑ V ∈ T.erase W, hh V * e V := fun W hW =>
    (Finset.add_sum_erase T _ hW).symm
  have hrest : ∀ W ∈ L.minimalPrimes, ∑ V ∈ T.erase W, hh V * e V ∈ W := by
    intro W hW
    refine Ideal.sum_mem _ fun V hV => Ideal.mul_mem_left _ _ ?_
    exact heV V ((hmemT V).mp (Finset.mem_of_mem_erase hV)) W hW (Finset.ne_of_mem_erase hV)
  have hfW : ∀ W ∈ L.minimalPrimes, f ∉ W := by
    intro W hW hmem
    rw [hsplit W ((hmemT W).mpr hW), Ideal.add_mem_iff_left _ (hrest W hW)] at hmem
    rcases hW.1.1.mem_or_mem hmem with h | h
    · exact hhW W hW h
    · exact heW W hW h

  have hcomp : ∀ x ∈ zeroSet J, linEval u x = 0 → ∃ W ∈ L.minimalPrimes, x ∈ zeroSet W := by
    intro x hxJ hxu
    have hxL : L ≤ RingHom.ker (eval x) := sup_le (fun p hp => RingHom.mem_ker.mpr (hxJ p hp))
      (Ideal.span_le.mpr (by simpa [hevL] using hxu))
    have : (RingHom.ker (eval x)).IsPrime := RingHom.ker_isPrime _
    obtain ⟨W, hW, hWx⟩ := Ideal.exists_minimalPrimes_le hxL
    exact ⟨W, hW, fun p hp => RingHom.mem_ker.mp (hWx hp)⟩
  have hcompInv : ∀ W ∈ L.minimalPrimes, ∀ x ∈ zeroSet W, x ∈ zeroSet J ∧ linEval u x = 0 := by
    intro W hW x hx
    refine ⟨fun p hp => hx p (hW.1.2 (Ideal.mem_sup_left hp)), ?_⟩
    rw [← hevL]
    exact hx _ (hW.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
  refine ⟨L ⊔ Ideal.span {f}, le_sup_left, ringKrullDim_quotient_sup_span_lt hfW hdimW, ?_⟩
  intro q hqJ hqu hqI
  obtain ⟨W, hW, hqW⟩ := hcomp q hqJ hqu
  have hfq : eval q f ≠ 0 := by
    intro h0
    refine hqI fun p hp => ?_
    have hle : L ⊔ Ideal.span {f} ≤ RingHom.ker (eval q) := by
      refine sup_le (fun p hp => ?_) (Ideal.span_le.mpr (by simpa using h0))
      obtain ⟨V, hV, hqV⟩ := hcomp q hqJ hqu
      exact RingHom.mem_ker.mpr (hqV p (hV.1.2 hp))
    exact RingHom.mem_ker.mp (hle hp)
  rw [hsplit W ((hmemT W).mpr hW), map_add (f := _), hqW _ (hrest W hW), add_zero, map_mul] at hfq
  refine graphChart_of_eq_on_open (U := {x | eval x (e W) ≠ 0})
    (isOpen_ne_fun (MvPolynomial.continuous_eval _) continuous_const) (right_ne_zero_of_mul hfq) ?_
    (hhchart W hW q hqW (left_ne_zero_of_mul hfq))
  ext x
  constructor
  · rintro ⟨⟨hxJ, hxu⟩, hxe⟩
    refine ⟨?_, hxe⟩
    obtain ⟨V, hV, hxV⟩ := hcomp x hxJ hxu
    by_cases hVW : V = W
    · exact hVW ▸ hxV
    · exact absurd (hxV _ (heV W hW V hV (Ne.symm hVW))) hxe
  · rintro ⟨hxW, hxe⟩
    exact ⟨hcompInv W hW x hxW, hxe⟩

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGenericFibreRadical
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem map_inf_eq_of_sup_inf_ker_le {R R' : Type*} [CommRing R] [CommRing R'] (φ : R →+* R')
    (hφ : Function.Surjective φ) (I J : Ideal R)
    (h : (I ⊔ J) ⊓ RingHom.ker φ ≤ RingHom.ker φ * (I ⊔ J)) :
    (I ⊓ J).map φ = I.map φ ⊓ J.map φ := by
  refine le_antisymm (Ideal.map_inf_le φ) ?_
  rintro y ⟨hyI, hyJ⟩
  obtain ⟨a, ha, rfl⟩ := (Ideal.mem_map_iff_of_surjective φ hφ).1 hyI
  obtain ⟨b, hb, hab⟩ := (Ideal.mem_map_iff_of_surjective φ hφ).1 hyJ
  have hmem : a - b ∈ (I ⊔ J) ⊓ RingHom.ker φ :=
    ⟨Ideal.sub_mem _ (Ideal.mem_sup_left ha) (Ideal.mem_sup_right hb),
      RingHom.mem_ker.2 (by rw [map_sub, hab, sub_self])⟩
  have h2 : a - b ∈ RingHom.ker φ * I ⊔ RingHom.ker φ * J := by
    rw [← Ideal.mul_sup]; exact h hmem
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 h2
  have hu' : u ∈ RingHom.ker φ ⊓ I := Ideal.mul_le_inf hu
  have hv' : v ∈ RingHom.ker φ ⊓ J := Ideal.mul_le_inf hv
  refine (Ideal.mem_map_iff_of_surjective φ hφ).2 ⟨a - u, ⟨Ideal.sub_mem _ ha hu'.2, ?_⟩, ?_⟩
  · have e : a - u = b + v := by linear_combination -huv
    rw [e]
    exact Ideal.add_mem _ hb hv'.2
  · rw [map_sub, RingHom.mem_ker.1 hu'.1, sub_zero]

theorem GenericFibreRadical.proof (hT : GenericFibreTor.Statement)
    (hP : GenericFibreRadicalPrime.Statement) : GenericFibreRadical.Statement := by
  intro σ _ ι _ K hK
  have hsurj : ∀ t : σ → ℂ, Function.Surjective
      (MvPolynomial.map (eval t) : MvPolynomial ι (MvPolynomial σ ℂ) →+* MvPolynomial ι ℂ) :=
    fun t => MvPolynomial.map_surjective _ (fun c => ⟨C c, eval_C c⟩)
  classical
  have key : ∀ s : Finset (Ideal (MvPolynomial ι (MvPolynomial σ ℂ))), (∀ p ∈ s, p.IsPrime) →
      ∃ F : MvPolynomial σ ℂ, F ≠ 0 ∧ ∀ t : σ → ℂ, eval t F ≠ 0 →
        ((s.inf id).map (MvPolynomial.map (eval t))).IsRadical := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨1, one_ne_zero, fun t _ => ?_⟩
      rw [Finset.inf_empty, Ideal.map_top]
      exact fun _ _ => Submodule.mem_top
    | insert p s hps ih =>
      intro hs
      obtain ⟨F₁, hF₁, h₁⟩ := ih (fun q hq => hs q (Finset.mem_insert_of_mem hq))
      obtain ⟨F₂, hF₂, h₂⟩ := hP σ ι p (hs p (Finset.mem_insert_self p s))
      obtain ⟨F₃, hF₃, h₃⟩ := hT σ ι (p ⊔ s.inf id)
      refine ⟨F₁ * F₂ * F₃, mul_ne_zero (mul_ne_zero hF₁ hF₂) hF₃, fun t ht => ?_⟩
      simp only [map_mul, ne_eq, mul_eq_zero, not_or] at ht
      obtain ⟨⟨ht₁, ht₂⟩, ht₃⟩ := ht
      rw [Finset.inf_insert, id, map_inf_eq_of_sup_inf_ker_le _ (hsurj t) _ _ (h₃ t ht₃)]
      exact (h₂ t ht₂).inf (h₁ t ht₁)
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing _ K
  obtain ⟨F, hF, hFt⟩ := key hfin.toFinset (fun p hp => ((hfin.mem_toFinset).1 hp).1.1)
  refine ⟨F, hF, fun t ht => ?_⟩
  have hK' : K = hfin.toFinset.inf id := by
    rw [Finset.inf_id_eq_sInf, Set.Finite.coe_toFinset, Ideal.sInf_minimalPrimes]
    exact le_antisymm Ideal.le_radical hK
  rw [hK']
  exact hFt t ht

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PExtensionQuotientLength
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem ExtensionQuotientLength.proof : ExtensionQuotientLength.Statement := by
  intro R B _ _ _ r hinj hr hfin
  set a := Algebra.linearMap R B
  set P : Submodule R B := LinearMap.range a
  set rP : Submodule R B := Submodule.map a (Ideal.span {r})
  set rB : Submodule R B := (Ideal.span {algebraMap R B r}).restrictScalars R
  have hrPP : rP ≤ P := by
    rintro _ ⟨y, -, rfl⟩
    exact ⟨y, rfl⟩
  have hrPrB : rP ≤ rB := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    exact Ideal.mem_span_singleton'.2 ⟨algebraMap R B c, by simp [a]⟩
  have hPr : P ≤ rP.comap (r • LinearMap.id) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨r * x, Ideal.mem_span_singleton'.2 ⟨x, mul_comm _ _⟩, by simp [a, Algebra.smul_def]⟩

  let f₁ := (Ideal.span {r}).mapQ rP a (Submodule.le_comap_map _ _)
  let g₁ := rP.mapQ P LinearMap.id hrPP
  have hf₁ : Function.Injective f₁ := by
    refine (injective_iff_map_eq_zero _).2 fun q hq ↦ ?_
    induction q using Submodule.Quotient.induction_on with | _ x => ?_
    simp only [f₁, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hq ⊢
    obtain ⟨y, hy, hyx⟩ := hq
    rwa [← hinj hyx]
  have hg₁ : Function.Surjective g₁ := fun q ↦ by
    induction q using Submodule.Quotient.induction_on with | _ b => exact ⟨Submodule.Quotient.mk b, rfl⟩
  have he₁ : Function.Exact f₁ g₁ := by
    intro q
    induction q using Submodule.Quotient.induction_on with | _ b => ?_
    simp only [g₁, f₁, Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.mk_eq_zero,
      Set.mem_range]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨Submodule.Quotient.mk x, rfl⟩
    · rintro ⟨q, hq⟩
      induction q using Submodule.Quotient.induction_on with | _ x => ?_
      rw [Submodule.mapQ_apply, Submodule.Quotient.eq] at hq
      simpa using P.sub_mem (hrPP hq) ⟨x, rfl⟩

  let f₂ := P.mapQ rP (r • LinearMap.id) hPr
  let g₂ := rP.mapQ rB LinearMap.id hrPrB
  have hf₂ : Function.Injective f₂ := by
    refine (injective_iff_map_eq_zero _).2 fun q hq ↦ ?_
    induction q using Submodule.Quotient.induction_on with | _ b => ?_
    simp only [f₂, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, LinearMap.smul_apply,
      LinearMap.id_apply] at hq ⊢
    obtain ⟨y, hy, hyb⟩ := hq
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    refine ⟨c, (mul_cancel_left_mem_nonZeroDivisors hr).1 ?_⟩
    simpa [a, Algebra.smul_def, mul_comm] using hyb
  have hg₂ : Function.Surjective g₂ := fun q ↦ by
    induction q using Submodule.Quotient.induction_on with | _ b => exact ⟨Submodule.Quotient.mk b, rfl⟩
  have he₂ : Function.Exact f₂ g₂ := by
    intro q
    induction q using Submodule.Quotient.induction_on with | _ b => ?_
    simp only [g₂, f₂, Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.mk_eq_zero,
      Set.mem_range]
    constructor
    · intro hb
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 (show b ∈ Ideal.span {algebraMap R B r} from hb)
      exact ⟨Submodule.Quotient.mk c, by simp [Algebra.smul_def, mul_comm]⟩
    · rintro ⟨q, hq⟩
      induction q using Submodule.Quotient.induction_on with | _ c => ?_
      rw [Submodule.mapQ_apply, Submodule.Quotient.eq] at hq
      have hc : r • c ∈ rB := Ideal.mem_span_singleton'.2 ⟨c, by simp [Algebra.smul_def, mul_comm]⟩
      simpa using rB.sub_mem hc (hrPrB hq)
  have h₁ := Module.length_eq_add_of_exact f₁ g₁ hf₁ hg₁ he₁
  have h₂ := Module.length_eq_add_of_exact f₂ g₂ hf₂ hg₂ he₂
  rw [← (Submodule.Quotient.restrictScalarsEquiv R (Ideal.span {algebraMap R B r})).length_eq]
  rw [h₁, add_comm] at h₂
  exact (WithTop.add_left_inj hfin).1 h₂

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PProjDimSpread
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open CategoryTheory

variable {R : Type} [CommRing R]

noncomputable def ProjDimSpread.localizedModuleEquiv (M : ModuleCat.{0} R) (S : Submonoid R) :
    M.localizedModule S ≃ₗ[Localization S] LocalizedModule S M :=
  LinearEquiv.extendScalarsOfIsLocalization S (Localization S)
    (IsLocalizedModule.linearEquiv S (M.localizedModuleMkLinearMap S)
      (LocalizedModule.mkLinearMap S M))

theorem ProjDimSpread.hasProjectiveDimensionLE_zero_iff (M : ModuleCat.{0} R) (S : Submonoid R) :
    HasProjectiveDimensionLE (M.localizedModule S) 0 ↔
      Module.Projective (Localization S) (LocalizedModule S M) := by
  rw [HasProjectiveDimensionLE, zero_add, ← projective_iff_hasProjectiveDimensionLT_one,
    ← IsProjective.iff_projective]
  exact ⟨fun _ ↦ Module.Projective.of_equiv (localizedModuleEquiv M S),
    fun _ ↦ Module.Projective.of_equiv (localizedModuleEquiv M S).symm⟩

theorem ProjDimSpread.spread_zero [IsNoetherianRing R] (P : Ideal R) [P.IsPrime]
    (M : ModuleCat.{0} R) [Module.Finite R M]
    (h : HasProjectiveDimensionLE (M.localizedModule P.primeCompl) 0) :
    ∃ g : R, g ∉ P ∧ ∀ (Q : Ideal R) [Q.IsPrime], g ∉ Q →
      HasProjectiveDimensionLE (M.localizedModule Q.primeCompl) 0 := by
  rw [hasProjectiveDimensionLE_zero_iff] at h
  have : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  have : Module.Flat (Localization.AtPrime P) (LocalizedModule P.primeCompl M) :=
    Module.Flat.of_projective
  have hfree : Module.Free (Localization.AtPrime P) (LocalizedModule P.primeCompl M) :=
    Module.free_of_flat_of_isLocalRing
  have hP : (⟨P, inferInstance⟩ : PrimeSpectrum R) ∈ Module.freeLocus R M :=
    Module.mem_freeLocus.mpr hfree
  obtain ⟨_, ⟨g, rfl⟩, hPg, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hP
      Module.isOpen_freeLocus
  refine ⟨g, (PrimeSpectrum.mem_basicOpen g _).mp hPg, fun Q _ hQ ↦ ?_⟩
  have : Module.Free (Localization.AtPrime Q) (LocalizedModule Q.primeCompl M) :=
    Module.mem_freeLocus.mp (hsub ((PrimeSpectrum.mem_basicOpen g ⟨Q, inferInstance⟩).mpr hQ))
  exact (hasProjectiveDimensionLE_zero_iff M Q.primeCompl).mpr Module.Projective.of_free

theorem ProjDimSpread.spread [IsNoetherianRing R] (P : Ideal R) [P.IsPrime] (n : ℕ) :
    ∀ (M : ModuleCat.{0} R) [Module.Finite R M],
      HasProjectiveDimensionLE (M.localizedModule P.primeCompl) n →
      ∃ g : R, g ∉ P ∧ ∀ (Q : Ideal R) [Q.IsPrime], g ∉ Q →
        HasProjectiveDimensionLE (M.localizedModule Q.primeCompl) n := by
  induction n with
  | zero => exact fun M _ h ↦ spread_zero P M h
  | succ n ih =>
    intro M _ h
    rcases Module.exists_finite_presentation R M with ⟨F, _, _, _, _, f, surjf⟩
    let S := f.shortComplexKer
    have S_exact := LinearMap.shortExact_shortComplexKer surjf
    have proj := ModuleCat.projective_of_categoryTheory_projective S.X₂
    have Sp_exact (T : Submonoid R) : (S.map (ModuleCat.localizedModuleFunctor T)).ShortExact :=
      S_exact.map_of_exact (ModuleCat.localizedModuleFunctor T)
    have projp (T : Submonoid R) : Projective (S.map (ModuleCat.localizedModuleFunctor T)).X₂ :=
      (ModuleCat.localizedModuleFunctor.{0} T).projective_obj_of_projective proj
    have hK : HasProjectiveDimensionLE
        ((ModuleCat.of R (LinearMap.ker f)).localizedModule P.primeCompl) n :=
      ((Sp_exact P.primeCompl).hasProjectiveDimensionLT_X₃_iff n (projp _)).mp h
    obtain ⟨g, hg, hQ⟩ := ih (ModuleCat.of R (LinearMap.ker f)) hK
    exact ⟨g, hg, fun Q _ hgQ ↦
      ((Sp_exact Q.primeCompl).hasProjectiveDimensionLT_X₃_iff n (projp _)).mpr (hQ Q hgQ)⟩

noncomputable def ProjDimSpread.quotientEquiv (I Q : Ideal R) [Q.IsPrime] :
    (ModuleCat.of R (R ⧸ I)).localizedModule Q.primeCompl ≃ₗ[Localization.AtPrime Q]
      (Localization.AtPrime Q ⧸ I.map (algebraMap R (Localization.AtPrime Q))) :=
  ((ProjDimSpread.localizedModuleEquiv (ModuleCat.of R (R ⧸ I)) Q.primeCompl).trans
    (LinearEquiv.extendScalarsOfIsLocalization Q.primeCompl (Localization.AtPrime Q)
      (IsLocalizedModule.linearEquiv Q.primeCompl (LocalizedModule.mkLinearMap Q.primeCompl (R ⧸ I))
        (I.toLocalizedQuotient' (Localization.AtPrime Q) Q.primeCompl
          (Algebra.linearMap R (Localization.AtPrime Q)))))).trans
    (Submodule.quotEquivOfEq _ _
      (Ideal.localized'_eq_map (Localization.AtPrime Q) Q.primeCompl I))

theorem ProjDimSpread.proof : ProjDimSpread.Statement := by
  intro R _ _ I P _ ℓ h
  have e : ∀ (Q : Ideal R) [Q.IsPrime], (ModuleCat.of R (R ⧸ I)).localizedModule Q.primeCompl ≅
      ModuleCat.of (Localization.AtPrime Q)
        (Localization.AtPrime Q ⧸ I.map (algebraMap R (Localization.AtPrime Q))) :=
    fun Q _ ↦ (ProjDimSpread.quotientEquiv I Q).toModuleIso
  have hP : HasProjectiveDimensionLE
      ((ModuleCat.of R (R ⧸ I)).localizedModule P.primeCompl) ℓ :=
    hasProjectiveDimensionLT_of_iso (e P).symm (ℓ + 1)
  obtain ⟨g, hg, hQ⟩ := ProjDimSpread.spread P ℓ (ModuleCat.of R (R ⧸ I)) hP
  refine ⟨g, hg, fun Q _ hgQ ↦ ?_⟩
  have := hQ Q hgQ
  exact hasProjectiveDimensionLT_of_iso (e Q) (ℓ + 1)

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PIdealHeightSpread
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem IdealHeightSpread.proof : IdealHeightSpread.Statement := by
  intro R _ _ I P _ _
  classical
  have hF := I.finite_minimalPrimes_of_isNoetherianRing R

  let a : Ideal R → R := fun p =>
    if h : ¬ (p : Set R) ⊆ P then Classical.choose (Set.not_subset.mp h) else 1
  have ha : ∀ p : Ideal R, ¬ p ≤ P → a p ∈ p ∧ a p ∉ P := by
    intro p h
    have h' : ¬ (p : Set R) ⊆ P := h
    simp only [a, dif_pos h']
    exact Classical.choose_spec (Set.not_subset.mp h')
  let s : Finset (Ideal R) := hF.toFinset.filter (fun p => ¬ p ≤ P)
  refine ⟨∏ p ∈ s, a p, ?_, ?_⟩
  · rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨p, hp, hpP⟩
    exact (ha p (Finset.mem_filter.mp hp).2).2 hpP
  · intro Q _ _ hgQ
    rw [Ideal.height_eq_inf_minimalPrimes (I.map (algebraMap R (Localization.AtPrime Q)))]
    refine le_iInf₂ fun J hJ => ?_
    have hJp : J.IsPrime := hJ.isPrime
    have hmin : J.comap (algebraMap R (Localization.AtPrime Q)) ∈ I.minimalPrimes := by
      rw [IsLocalization.minimalPrimes_map Q.primeCompl] at hJ
      exact hJ
    set p := J.comap (algebraMap R (Localization.AtPrime Q)) with hpdef
    have hpp : p.IsPrime := hmin.1.1

    have hpQ : p ≤ Q := by
      intro x hx
      by_contra hxQ
      have hu := IsLocalization.map_units (Localization.AtPrime Q) (⟨x, hxQ⟩ : Q.primeCompl)
      exact hJp.ne_top (Ideal.eq_top_of_isUnit_mem J hx hu)

    have hpP : p ≤ P := by
      by_contra hnot
      apply hgQ
      apply hpQ
      have hps : p ∈ s := Finset.mem_filter.mpr ⟨hF.mem_toFinset.mpr hmin, hnot⟩
      exact Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem a hps) (ha p hnot).1
    have hdisj : Disjoint (P.primeCompl : Set R) (p : Set R) := by
      rw [Set.disjoint_left]
      intro x hx hxp
      exact hx (hpP hxp)
    have hJh : J.height = p.height := (IsLocalization.height_under Q.primeCompl J).symm
    rw [hJh, ← IsLocalization.height_map_of_disjoint P.primeCompl (S := Localization.AtPrime P) p hdisj]
    exact Ideal.height_mono (Ideal.map_mono hmin.1.2)

end GroundTheory.Heights₂.Heights
end

set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.DivisorRegularGeneric : GroundTheory.Heights₂.Heights.DivisorRegularGeneric.Statement :=
  @GroundTheory.Heights₂.Heights.DivisorRegularGeneric.proof GroundTheory.Heights₂.Heights.AutoClose.FrameGraphGeneric

theorem GroundTheory.Heights₂.Heights.AutoClose.CMLengthParameters.{u} : GroundTheory.Heights₂.Heights.CMLengthParameters.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.CMLengthParameters.proof.{u} GroundTheory.Heights₂.Heights.CMRegularElement.proof GroundTheory.Heights₂.Heights.AutoClose.LengthLocalizedQuotient

theorem GroundTheory.Heights₂.Heights.AutoClose.CurveRegularOffFinite : GroundTheory.Heights₂.Heights.CurveRegularOffFinite.Statement :=
  @GroundTheory.Heights₂.Heights.CurveRegularOffFinite.proof GroundTheory.Heights₂.Heights.AutoClose.FrameGraphGeneric GroundTheory.Heights₂.Heights.CurveProperClosedFinite.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.regular_off_hypersurface_holds : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.RegularOffHypersurface.Statement :=
  @GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.RegularOffHypersurface.proof GroundTheory.Heights₂.Heights.AutoClose.FrameGraphGeneric

theorem GroundTheory.Heights₂.Heights.AutoClose.CurveNormalisationLength : GroundTheory.Heights₂.Heights.CurveNormalisationLength.Statement :=
  @GroundTheory.Heights₂.Heights.CurveNormalisationLength.proof GroundTheory.Heights₂.Heights.AutoClose.CurveNormalisationFinite GroundTheory.Heights₂.Heights.AutoClose.CurveNormalisationQuotientLength GroundTheory.Heights₂.Heights.ExtensionQuotientLength.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.SliceCMUnmixed : GroundTheory.Heights₂.Heights.SliceCMUnmixed.Statement :=
  @GroundTheory.Heights₂.Heights.SliceCMUnmixed.proof GroundTheory.Heights₂.Heights.AutoClose.CMQuotientUnmixed

theorem GroundTheory.Heights₂.Heights.AutoClose.UniformiserLocallyInjective : GroundTheory.Heights₂.Heights.UniformiserLocallyInjective.Statement :=
  @GroundTheory.Heights₂.Heights.UniformiserLocallyInjective.proof GroundTheory.Heights₂.Heights.AutoClose.UniformiserGradientIndependent GroundTheory.Heights₂.Heights.PolynomialChartInjective.full

theorem GroundTheory.Heights₂.Heights.AutoClose.CMLocusOpen : GroundTheory.Heights₂.Heights.CMLocusOpen.Statement :=
  @GroundTheory.Heights₂.Heights.CMLocusOpen.proof GroundTheory.Heights₂.Heights.AutoClose.CMProjDimCriterion GroundTheory.Heights₂.Heights.ProjDimSpread.proof GroundTheory.Heights₂.Heights.IdealHeightSpread.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.NormalModelDisc : GroundTheory.Heights₂.Heights.NormalModelDisc.Statement :=
  @GroundTheory.Heights₂.Heights.NormalModelDisc.proof GroundTheory.Heights₂.Heights.AutoClose.NormalCurveRegularPoint

theorem GroundTheory.Heights₂.Heights.AutoClose.GenericFibreRadical : GroundTheory.Heights₂.Heights.GenericFibreRadical.Statement :=
  @GroundTheory.Heights₂.Heights.GenericFibreRadical.proof GroundTheory.Heights₂.Heights.AutoClose.GenericFibreTor GroundTheory.Heights₂.Heights.AutoClose.GenericFibreRadicalPrime

theorem GroundTheory.Heights₂.Heights.AutoClose.injective_holomorphic_open_holds : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.InjectiveHolomorphicOpen.Statement :=
  @GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.InjectiveHolomorphicOpen.proof GroundTheory.Heights₂.Heights.AutoClose.invariance_of_domain_holds

theorem GroundTheory.Heights₂.Heights.AutoClose.branch_inverse_off_hypersurface_holds : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.BranchInverseOffHypersurface.Statement :=
  @GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.BranchInverseOffHypersurface.proof GroundTheory.Heights₂.Heights.AutoClose.injective_holomorphic_inverse_holds GroundTheory.Heights₂.Heights.AutoClose.projection_injective_off_hypersurface_holds
