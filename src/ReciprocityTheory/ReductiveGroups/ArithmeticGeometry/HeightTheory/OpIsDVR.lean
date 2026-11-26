module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.LaTIsPrime
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.RegAVpt
public import ReciprocityTheory.SemistableReduction.AeBlockSphereEvalNeZero

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.OpIsDVR
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField IsLocalRing

theorem Op_isDVR {K : Type} [Field K] [NumberField K] (D N : ℕ)
    (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : IsDiscreteValuationRing (Op D N la) := by
  classical
  set P := laT D N la with hP
  have hp0 : la.asIdeal ≠ ⊥ := la.ne_bot
  have hp1 : la.asIdeal ≠ ⊤ := la.isPrime.ne_top

  obtain ⟨π, hπp, hπ2⟩ : ∃ π ∈ la.asIdeal, π ∉ la.asIdeal ^ 2 := by
    have hlt : la.asIdeal ^ 2 < la.asIdeal ^ 1 :=
      Ideal.pow_right_strictAnti la.asIdeal hp0 hp1 (by norm_num : 1 < 2)
    rw [pow_one] at hlt
    obtain ⟨x, hx, hx2⟩ := SetLike.exists_of_lt hlt
    exact ⟨x, hx, hx2⟩
  have hmemP : ∀ t : 𝓞 K, MvPolynomial.C t ∈ P ↔ t ∈ la.asIdeal := by
    intro t
    rw [hP, laT, MvPolynomial.mem_map_C_iff]
    constructor
    · intro h
      simpa using h 0
    · intro h m
      rw [MvPolynomial.coeff_C]
      split_ifs
      · exact h
      · exact zero_mem _

  have hdiv : ∀ a ∈ la.asIdeal, ∃ t c : 𝓞 K, t ∉ la.asIdeal ∧ t * a = π * c := by
    intro a ha
    have hle : Ideal.span {π} ≤ la.asIdeal := (Ideal.span_singleton_le_iff_mem _).mpr hπp
    obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.mpr hle
    have hJp : ¬ J ≤ la.asIdeal := by
      intro hJle
      apply hπ2
      have hsq : Ideal.span {π} ≤ la.asIdeal ^ 2 := by
        rw [hJ, pow_two]
        exact Ideal.mul_mono_right hJle
      exact hsq (Ideal.mem_span_singleton_self π)
    obtain ⟨t, htJ, htp⟩ := SetLike.not_le_iff_exists.mp hJp
    have hta : t * a ∈ Ideal.span {π} := by
      rw [hJ, mul_comm t a]
      exact Ideal.mul_mem_mul ha htJ
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hta
    exact ⟨t, c, htp, by rw [← hc, mul_comm]⟩
  haveI : IsNoetherianRing (Op D N la) :=
    IsLocalization.isNoetherianRing P.primeCompl (Op D N la) inferInstance
  let f : 𝓞 K →+* Op D N la := (algebraMap (OT K D N) (Op D N la)).comp MvPolynomial.C
  have hmax : IsLocalRing.maximalIdeal (Op D N la) = Ideal.map f la.asIdeal := by
    have e : Ideal.map f la.asIdeal =
        Ideal.map (algebraMap (OT K D N) (Op D N la)) (laT D N la) :=
      (Ideal.map_map (MvPolynomial.C : 𝓞 K →+* OT K D N) (algebraMap (OT K D N) (Op D N la))).symm
    rw [e]
    exact (Localization.AtPrime.map_eq_maximalIdeal).symm
  have hπm : IsLocalRing.maximalIdeal (Op D N la) = Ideal.span {f π} := by
    apply le_antisymm
    · rw [hmax, Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap]
      obtain ⟨t, c, htp, htc⟩ := hdiv a ha
      have hu : IsUnit (f t) :=
        (IsLocalization.AtPrime.isUnit_to_map_iff (Op D N la) P (MvPolynomial.C t)).mpr
          (fun h => htp ((hmemP t).mp h))
      obtain ⟨u, hu'⟩ := hu
      rw [Ideal.mem_span_singleton']
      refine ⟨↑u⁻¹ * f c, ?_⟩
      have hfm : f t * f a = f π * f c := by rw [← map_mul, ← map_mul, htc]
      calc ↑u⁻¹ * f c * f π = ↑u⁻¹ * (f π * f c) := by ring
        _ = ↑u⁻¹ * (f t * f a) := by rw [hfm]
        _ = f a := by rw [← hu', ← mul_assoc, Units.inv_mul, one_mul]
    · rw [Ideal.span_le, Set.singleton_subset_iff, hmax]
      exact Ideal.mem_map_of_mem f hπp
  have hnf : ¬ IsField (Op D N la) := by
    intro hF
    have hb := IsLocalRing.isField_iff_maximalIdeal_eq.mp hF
    rw [hπm, Ideal.span_singleton_eq_bot] at hb
    have hπ0 : π ≠ 0 := fun h => hπ2 (h ▸ zero_mem _)
    have hinj : Function.Injective (algebraMap (OT K D N) (Op D N la)) :=
      IsLocalization.injective (Op D N la) (Ideal.primeCompl_le_nonZeroDivisors P)
    exact hπ0 (MvPolynomial.C_injective _ _ ((hinj (hb.trans (map_zero _).symm)).trans
      (map_zero _).symm))
  have hprin : (IsLocalRing.maximalIdeal (Op D N la)).IsPrincipal := ⟨⟨f π, hπm⟩⟩
  exact ((IsDiscreteValuationRing.TFAE (Op D N la) hnf).out 1 5).mpr hprin

end ReciprocityTheory.ChartRestriction.G.T0
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HeightIntegralEstimates
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]

namespace Data

variable (d : Data K ι Ω WT A) (𝒜 : (c : ι) → WT → Submodule (Ω c) (A c))

structure AxH : Type where
  nonempty : Nonempty ι
  tower : ∀ c, IsScalarTower K (Ω c) (A c)
  towerO : ∀ c, IsScalarTower (𝓞 K) K (A c)
  D_ge : 3 ≤ d.D
  fg : ∀ c, (⊤ : IntermediateField K (Ω c)).FG
  trdeg : ∀ c, Algebra.trdeg K (Ω c) = d.D
  algClosed : ∀ c (a : Ω c), IsAlgebraic K a → a ∈ (algebraMap K (Ω c)).range
  graded : ∀ c, SetLike.GradedMonoid (𝒜 c)
  finrank_one : ∀ c G, Module.finrank (Ω c) (𝒜 c G) = 1
  mul_ne_zero : ∀ c {G G' : WT} {f g : A c}, f ∈ 𝒜 c G → g ∈ 𝒜 c G' → f ≠ 0 → g ≠ 0 →
    f * g ≠ 0
  WW_span : d.WW = Submodule.span (𝓞 K) (Set.range d.w)
  w_mem : ∀ j c, d.w j c ∈ 𝒜 c d.wL
  w_base : ∀ c, d.w (d.jc c) c ≠ 0
  Thp_span : d.Thp = Submodule.span (𝓞 K) (Set.range d.thp)
  thp_mem : ∀ k c, d.thp k c ∈ 𝒜 c d.wF
  et_mem : ∀ c, d.et c ∈ 𝒜 c (d.n1 • d.wde)
  firstSectionMem : ∀ c, d.ta1 c ∈ 𝒜 c ((2 : ℕ) • d.G1)
  secondSectionMem : ∀ c, d.ta2 c ∈ 𝒜 c d.G2
  et_ne : ∀ c, d.et c ≠ 0
  firstSectionNeZero : ∀ c, d.ta1 c ≠ 0
  secondSectionNeZero : ∀ c, d.ta2 c ≠ 0
  ord_mul : ∀ c v, d.admitted c v → ∀ {G G' : WT} {f g : A c}, f ∈ 𝒜 c G → g ∈ 𝒜 c G' →
    f ≠ 0 → g ≠ 0 → d.ord c v (G + G') (f * g) = d.ord c v G f + d.ord c v G' g
  ord_smul : ∀ c v, d.admitted c v → ∀ {G : WT} {f : A c} (a : Ω c), f ∈ 𝒜 c G → f ≠ 0 → a ≠ 0 →
    ((d.ord c v G (a • f) : ℤ) : WithTop ℤ) = v a + (d.ord c v G f : WithTop ℤ)
  nrm_pos : ∀ c {G : WT} {f : A c} (P : Ω c →+* ℂ), f ∈ 𝒜 c G → f ≠ 0 → 0 < d.nrm c G f P
  nrm_zero : ∀ c (G : WT) (P : Ω c →+* ℂ), d.nrm c G 0 P = 0
  nrm_mul : ∀ c {G G' : WT} {f g : A c} (P : Ω c →+* ℂ), f ∈ 𝒜 c G → g ∈ 𝒜 c G' →
    f ≠ 0 → g ≠ 0 → d.nrm c (G + G') (f * g) P = d.nrm c G f P * d.nrm c G' g P
  nrm_smul : ∀ c {G : WT} {f : A c} (P : Ω c →+* ℂ) (a : Ω c), f ∈ 𝒜 c G → f ≠ 0 → a ≠ 0 →
    d.nrm c G (a • f) P = ‖P a‖ * d.nrm c G f P
  nrm_conj : ∀ c (G : WT) (f : A c) (P : Ω c →+* ℂ),
    d.nrm c G f ((starRingEnd ℂ).comp P) = d.nrm c G f P
  bdd : ∀ (sg : K →+* ℂ) (G : WT) (f : ∀ c, A c),
    ((f ∈ d.WW ∧ G = d.wL) ∨ (f ∈ d.Thp ∧ G = d.wF) ∨ (f = d.et ∧ G = d.n1 • d.wde) ∨
      (f = d.ta1 ∧ G = (2 : ℕ) • d.G1) ∨ (f = d.ta2 ∧ G = d.G2)) →
    BddAbove (Set.range fun p : (Σ c, PT (Ω := Ω c) sg) => d.nrm p.1 G (f p.1) p.2)
  a1 : ∀ c, ∃ J : Fin d.D → Fin d.N,
    LinearIndependent (Ω c) fun k => KaehlerDifferential.D K (Ω c) (d.x c (J k))
  ord_nonneg_WW : ∀ c v, d.admitted c v → ∀ f ∈ d.WW, f c ≠ 0 → 0 ≤ d.ord c v d.wL (f c)
  ord_nonneg_Thp : ∀ c v, d.admitted c v → ∀ f ∈ d.Thp, f c ≠ 0 → 0 ≤ d.ord c v d.wF (f c)
  ord_nonneg_et : ∀ c v, d.admitted c v → 0 ≤ d.ord c v (d.n1 • d.wde) (d.et c)
  ordDoubleFirstSection_nonneg : ∀ c v, d.admitted c v → 0 ≤ d.ord c v ((2 : ℕ) • d.G1) (d.ta1 c)
  ordSecondSectionNonneg : ∀ c v, d.admitted c v → 0 ≤ d.ord c v d.G2 (d.ta2 c)
  a3' : ∀ c {G : WT} {f : A c}, f ∈ 𝒜 c G → f ≠ 0 → {v | d.admitted c v ∧ d.ord c v G f ≠ 0}.Finite
  sel : Fin d.del → Fin d.np
  a4 : ∃ e : ∀ c, A c, (∀ c, e c ∈ 𝒜 c d.wF ∧ e c ≠ 0) ∧
    (∀ p : Fin d.del → MvPolynomial (TVar d.D d.N) K,
      (∀ c, ∑ k, d.sH c (p k) *
        algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.thp (sel k) c) (e c)) = 0) →
      ∀ k, p k = 0) ∧
    (∀ y : ∀ c, OmS (Ω c) d.D d.N, ∃ q : MvPolynomial (TVar d.D d.N) K, (∀ c, d.sH c q ≠ 0) ∧
      ∃ p : Fin d.del → MvPolynomial (TVar d.D d.N) K, ∀ c, d.sH c q * y c = ∑ k, d.sH c (p k) *
        algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.thp (sel k) c) (e c)))
  i_ge : 1 ≤ d.i
  g_zero_ge_ask_sum : 1 ≤ d.g0
  cc_nonneg : 0 ≤ d.cc
  cc_le : d.cc ≤ 1
  ccg0 : d.cc * d.g0 ≤ 1 / 2
  size_L : 1 ≤ d.wsize d.wL
  DF_le : d.DF ≤ d.wsize d.wL
  rw_le : Real.log (d.N + 1 : ℕ) + 1 / 2 ≤ d.Prw * (d.wsize d.wL - 1)
  nK_le : Real.log (Module.finrank ℚ K) ≤ d.PO
  rd_le : Real.log (|(NumberField.discr K : ℝ)| ^ (1 / (Module.finrank ℚ K : ℝ))) ≤ d.PO
  P_ge : 1 ≤ d.PN ∧ 1 ≤ d.PQ ∧ 1 ≤ d.tableDegreeThreeBase ∧ 1 ≤ d.PP0' ∧ 1 ≤ d.Pd ∧ 1 ≤ d.Gc ∧ 1 ≤ d.PI4 ∧
    1 ≤ d.Pet ∧ 1 ≤ d.tableLineDegreeFive ∧ 1 ≤ d.tableLineDegreeTwo ∧ 1 ≤ d.Prw ∧ 1 ≤ d.PO
  a13 : ∀ c (sg : K →+* ℂ) {G : WT} {f : A c}, f ∈ 𝒜 c G → f ≠ 0 →
    AEMeasurable (fun t : Fin d.D → Metric.sphere (0 : EuclideanSpace ℂ (Fin (d.N + 1))) 1 =>
      ∑ᶠ P ∈ d.ST c sg (fun i j => (t i : EuclideanSpace ℂ (Fin (d.N + 1))) j),
        Real.log (d.nrm c G f P)) d.sphMeasure

variable {𝒜}

def FinitePlaceHyp : Prop :=
  (∀ la, 0 ≤ d.nu la) ∧
  ((Function.support d.nu).Finite) ∧
  ((∑ᶠ la, d.nu la * logNorm la) / (Module.finrank ℚ K : ℝ) ≤ d.PN * d.wsize d.wL) ∧
  (∀ c v la, d.admitted c v → IsOver (K := K) v la →
      ((⨅ j : {j // d.w j c ≠ 0}, d.ord c v d.wL (d.w j c) : ℤ) : ℝ) ≤
        (ramIdx (K := K) v la : ℝ) * d.nu la +
          d.cc / (2 * d.i) * d.ord c v (d.n1 • d.wde) (d.et c))

def TrivialPlaceHyp : Prop :=
  (∀ c v, d.admitted c v → IsTrivOn K v →
      ((⨅ j : {j // d.w j c ≠ 0}, d.ord c v d.wL (d.w j c) : ℤ) : ℝ) ≤
        d.cc / (2 * d.i) * d.ord c v (d.n1 • d.wde) (d.et c))

def HtLAM : Prop :=
  (∀ c, ∀ g ∈ Submodule.span (𝓞 K)
        (Set.range fun s : Fin d.n96 → Fin (d.N + 1) => ∏ k, d.w (s k)), g c ≠ 0 →
      -(d.PP0' * d.n96 * d.wsize d.wL) ≤
        meanK fun sg => Real.log (d.supNc c sg (d.n96 • d.wL) (g c)))

def HtSup : Prop :=
  (meanK (fun sg => ⨆ j, Real.log (d.supN sg d.wL (d.w j))) ≤ d.Gc * d.wsize d.wL) ∧
  (∀ k, meanK (fun sg => Real.log (d.supN sg d.wF (d.thp k))) ≤ d.Gc * d.wsize d.wF) ∧
  (meanK (fun sg => Real.log (d.supN sg ((2 : ℕ) • d.G1) d.ta1)) ≤
      2 * d.PI4 * d.D * d.wsize d.wL) ∧
  (meanK (fun sg => Real.log (d.supN sg d.G2 d.ta2)) ≤ d.PI4 * d.D * d.wsize d.wL)

def HeightIntegralEstimateTrivialPlace : Prop :=
  (meanK (fun sg => Real.log (d.supN sg (d.n1 • d.wde) d.et)) / d.i ≤ d.Pet)

def HeightIntegralBoundEstimate : Prop :=
  (∀ c (P : Ω c →+* ℂ),
      -Real.log (d.be c P) ≤
        d.tableLineDegreeFive * d.DF + d.cc / d.i * (-Real.log (d.nrm c (d.n1 • d.wde) (d.et c) P)) + d.cc * d.tableLineDegreeTwo)

def PHc : ℝ := 2 * d.PH + d.Gc

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.RegVert
namespace ReciprocityTheory.ChartRestriction.G.T0

open IsLocalRing

theorem regVert_eq_of_le_height_one {A : Type*} [CommRing A] [IsDomain A] {Q P : Ideal A} [Q.IsPrime]
    [P.IsPrime] (hQ : Q ≠ ⊥) (hQP : Q ≤ P) (hP : P.height = 1) : Q = P := by
  by_contra hne
  have hlt : Q < P := lt_of_le_of_ne hQP hne
  have hbot : (⊥ : Ideal A) < Q := bot_lt_iff_ne_bot.mpr hQ
  have hQle : Q.height ≤ 1 := hP ▸ Ideal.height_mono hQP
  have hQfin : Q.height ≠ ⊤ := ne_top_of_le_ne_top (by simp) hQle
  haveI : Q.FiniteHeight := ⟨Or.inr hQfin⟩
  haveI : (⊥ : Ideal A).FiniteHeight := ⟨Or.inr (by simp)⟩
  have h1 : (⊥ : Ideal A).height + 1 ≤ Q.height := by
    first
    | exact ENat.add_one_le_of_lt (Ideal.height_strict_mono_of_isPrime hbot)
    | exact Order.add_one_le_of_lt (Ideal.height_strict_mono_of_isPrime hbot)
  have h2 : Q.height + 1 ≤ P.height := by
    first
    | exact ENat.add_one_le_of_lt (Ideal.height_strict_mono_of_isPrime hlt)
    | exact Order.add_one_le_of_lt (Ideal.height_strict_mono_of_isPrime hlt)
  rw [hP] at h2
  have h3 : (2 : ℕ∞) ≤ 1 := by
    calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
      _ ≤ (⊥ : Ideal A).height + 1 + 1 := by gcongr; simp
      _ ≤ Q.height + 1 := by gcongr
      _ ≤ 1 := h2
  exact absurd h3 (by norm_num)

theorem regVert_valuationRing {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] (P : Ideal A) [P.IsPrime] (hP : P.height = 1) :
    ValuationRing (Localization.AtPrime P) := by
  have hPne : P ≠ ⊥ := by
    rintro rfl
    have h0 : (⊥ : Ideal A).height = 0 := by
      first
      | exact Ideal.height_bot
      | simp
    rw [h0] at hP
    exact zero_ne_one hP
  haveI : IsNoetherianRing (Localization.AtPrime P) :=
    IsLocalization.isNoetherianRing P.primeCompl _ inferInstance
  have hinj : Function.Injective (algebraMap A (Localization.AtPrime P)) :=
    IsLocalization.injective _ P.primeCompl_le_nonZeroDivisors
  have hmax : Ideal.map (algebraMap A (Localization.AtPrime P)) P =
      IsLocalRing.maximalIdeal (Localization.AtPrime P) :=
    Localization.AtPrime.map_eq_maximalIdeal
  have hcm : Ideal.comap (algebraMap A (Localization.AtPrime P))
      (IsLocalRing.maximalIdeal (Localization.AtPrime P)) = P := by
    first
    | exact Localization.AtPrime.under_maximalIdeal
    | exact IsLocalization.AtPrime.comap_maximalIdeal _ P
  have hmne : IsLocalRing.maximalIdeal (Localization.AtPrime P) ≠ ⊥ := by
    rw [← hmax]
    intro h
    exact hPne ((Ideal.map_eq_bot_iff_of_injective hinj).mp h)
  have hnf : ¬ IsField (Localization.AtPrime P) := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq]
    exact hmne
  haveI : IsDomain (Localization.AtPrime P) := by
    first
    | infer_instance
    | exact IsLocalization.isDomain_localization P.primeCompl_le_nonZeroDivisors
  haveI hic : IsIntegrallyClosed (Localization.AtPrime P) := by
    first
    | exact isIntegrallyClosed_of_isLocalization P.primeCompl P.primeCompl_le_nonZeroDivisors
    | exact isIntegrallyClosed_of_isLocalization (S := Localization.AtPrime P) P.primeCompl
        P.primeCompl_le_nonZeroDivisors
    | exact IsIntegrallyClosed.of_isLocalization (Localization.AtPrime P) P.primeCompl
        P.primeCompl_le_nonZeroDivisors
    | exact isIntegrallyClosed_of_isLocalization (Localization.AtPrime P) P.primeCompl
        P.primeCompl_le_nonZeroDivisors
  have huniq : ∃! Q' : Ideal (Localization.AtPrime P), Q' ≠ ⊥ ∧ Q'.IsPrime := by
    refine ⟨IsLocalRing.maximalIdeal _, ⟨hmne, inferInstance⟩, ?_⟩
    rintro Q' ⟨hQ'ne, hQ'p⟩
    haveI := hQ'p
    have hc : Q'.under A ≤ P := by
      exact (Ideal.comap_mono (IsLocalRing.le_maximalIdeal hQ'p.ne_top)).trans hcm.le
    have hcne : Q'.under A ≠ ⊥ := by
      intro h
      apply hQ'ne
      rw [← IsLocalization.map_under P.primeCompl (Localization.AtPrime P) Q', h, Ideal.map_bot]
    have heq := regVert_eq_of_le_height_one hcne hc hP
    rw [← IsLocalization.map_under P.primeCompl (Localization.AtPrime P) Q', heq, hmax]
  first
  | exact ((IsDiscreteValuationRing.TFAE (Localization.AtPrime P) hnf).out 1 3).mpr (And.intro hic huniq)
  | exact ((IsDiscreteValuationRing.TFAE (Localization.AtPrime P) hnf).out 1 4).mpr (And.intro hic huniq)
  | exact ((IsDiscreteValuationRing.TFAE (Localization.AtPrime P) hnf).out 1 2).mpr (And.intro hic huniq)
  | exact ((IsDiscreteValuationRing.TFAE (Localization.AtPrime P) hnf).out 1 5).mpr (And.intro hic huniq)
  | exact @ValuationRing.of_isDiscreteValuationRing _ _ _ (((IsDiscreteValuationRing.TFAE (Localization.AtPrime P) hnf).out 1 4).mpr (And.intro hic huniq))
  | exact @ValuationRing.of_isDiscreteValuationRing _ _ _ (((IsDiscreteValuationRing.TFAE (Localization.AtPrime P) hnf).out 1 5).mpr (And.intro hic huniq))
  | exact @ValuationRing.of_isDiscreteValuationRing _ _ _ (((IsDiscreteValuationRing.TFAE (Localization.AtPrime P) hnf).out 1 3).mpr (And.intro hic huniq))
  | exact @ValuationRing.of_isDiscreteValuationRing _ _ _ (((IsDiscreteValuationRing.TFAE (Localization.AtPrime P) hnf).out 1 6).mpr (And.intro hic huniq))
  | exact ((IsDiscreteValuationRing.TFAE (Localization.AtPrime P) hnf).out 2 3).mpr (And.intro hic huniq)
  | exact ((IsDiscreteValuationRing.TFAE (Localization.AtPrime P) hnf).out 2 4).mpr (And.intro hic huniq)
  | exact ((IsDiscreteValuationRing.TFAE (Localization.AtPrime P) hnf).out 2 5).mpr (And.intro hic huniq)

end ReciprocityTheory.ChartRestriction.G.T0
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.CastAddNeNatAdd
namespace ReciprocityTheory.ChartRestriction.G.T0.NPB

open MvPolynomial MeasureTheory ReciprocityTheory.MultiplicativeHeights

section MH

variable {R : Type*} [CommSemiring R] {B n : ℕ}

theorem isMH_zero (a : Fin B → ℕ) : IsMultiHomogeneous a (0 : MvPolynomial (Fin B × Fin n) R) := by
  intro s hs; simp at hs

theorem isMH_C (r : R) : IsMultiHomogeneous (0 : Fin B → ℕ) (C r : MvPolynomial (Fin B × Fin n) R) := by
  intro s hs b
  rw [mem_support_iff, coeff_C] at hs
  have : (0 : Fin B × Fin n →₀ ℕ) = s := by
    by_contra h; exact hs (if_neg h)
  subst this; simp

theorem isMH_add {a : Fin B → ℕ} {f g : MvPolynomial (Fin B × Fin n) R}
    (hf : IsMultiHomogeneous a f) (hg : IsMultiHomogeneous a g) : IsMultiHomogeneous a (f + g) := by
  classical
  intro s hs
  rcases Finset.mem_union.1 (support_add hs) with h | h
  exacts [hf s h, hg s h]

theorem isMH_mul_X {a : Fin B → ℕ} {f : MvPolynomial (Fin B × Fin n) R}
    (hf : IsMultiHomogeneous a f) (i : Fin B) (j : Fin n) :
    IsMultiHomogeneous (a + Pi.single i 1) (f * X (i, j)) := by
  classical
  intro s hs b
  rw [support_mul_X, Finset.mem_map] at hs
  obtain ⟨s', hs', rfl⟩ := hs
  simp only [addRightEmbedding_apply, Finsupp.add_apply, Finset.sum_add_distrib, hf s' hs' b,
    Pi.add_apply]
  congr 1
  by_cases hb : b = i
  · subst hb; simp [Finsupp.single_apply]
  · simp [hb]

end MH

theorem countable_mvPoly {σ R : Type*} [Countable σ] [CommSemiring R] [Countable R] :
    Countable (MvPolynomial σ R) := by
  classical
  refine Function.Surjective.countable (f := fun f : (σ →₀ ℕ) →₀ R => f.sum fun m a => monomial m a) ?_
  intro p
  refine ⟨Finsupp.onFinset p.support (fun m => AddMonoidAlgebra.coeff p m) (fun m hm => mem_support_iff.2 hm), ?_⟩
  dsimp only
  rw [Finsupp.onFinset_sum _ (fun m => by simp)]
  exact (MvPolynomial.as_sum p).symm

variable {K : Type} [Field K] {D N : ℕ}

noncomputable def hImg (p : Fin (D + 1) × Fin (N + 1)) :
    MvPolynomial (Fin (N + 1 + D)) (MvPolynomial (Fin D × Fin (N + 1)) K) :=
  Fin.cases (motive := fun _ => Fin (N + 1) → MvPolynomial (Fin (N + 1 + D))
      (MvPolynomial (Fin D × Fin (N + 1)) K))
    (fun j => X (Fin.castAdd D j)) (fun i j => X (Fin.natAdd (N + 1) i) * C (X (i, j))) p.1 p.2

@[simp] theorem hImg_zero (j : Fin (N + 1)) :
    hImg (K := K) (D := D) ((0 : Fin (D + 1)), j) = X (Fin.castAdd D j) := by
  simp [hImg]

@[simp] theorem hImg_succ (i : Fin D) (j : Fin (N + 1)) :
    hImg (K := K) (i.succ, j) = X (Fin.natAdd (N + 1) i) * C (X (i, j)) := by
  simp [hImg]

noncomputable def homog : MvPolynomial (Fin (D + 1) × Fin (N + 1)) K →ₐ[K]
    MvPolynomial (Fin (N + 1 + D)) (MvPolynomial (Fin D × Fin (N + 1)) K) :=
  aeval hImg

noncomputable def back : MvPolynomial (Fin (N + 1 + D)) (MvPolynomial (Fin D × Fin (N + 1)) K) →+*
    MvPolynomial (Fin (D + 1) × Fin (N + 1)) K :=
  eval₂Hom (rename fun p : Fin D × Fin (N + 1) => (p.1.succ, p.2)).toRingHom
    (Fin.addCases (fun j => X (0, j)) (fun _ => 1))

theorem back_homog (q : MvPolynomial (Fin (D + 1) × Fin (N + 1)) K) : back (homog q) = q := by
  have : (back (K := K) (D := D) (N := N)).comp (homog (K := K)).toRingHom = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp [back, homog, MvPolynomial.algebraMap_eq]
    · rintro ⟨i, j⟩
      cases i using Fin.cases with
      | zero => simp [back, homog]
      | succ i => simp [back, homog]
  exact congrArg (fun f => f q) this

theorem homog_injective : Function.Injective (homog (K := K) (D := D) (N := N)) :=
  Function.LeftInverse.injective back_homog

theorem castAdd_ne_natAdd (j : Fin (N + 1)) (i : Fin D) : Fin.castAdd D j ≠ Fin.natAdd (N + 1) i := by
  intro h; have := congrArg Fin.val h; simp at this; omega

theorem homog_coeff_isMH (q : MvPolynomial (Fin (D + 1) × Fin (N + 1)) K) :
    ∀ γ : Fin (N + 1 + D) →₀ ℕ,
    IsMultiHomogeneous (fun i => γ (Fin.natAdd (N + 1) i)) (AddMonoidAlgebra.coeff (homog q) γ) := by
  classical
  induction q using MvPolynomial.induction_on
  · rename_i a
    intro γ
    rw [show homog (C a) = C (C a) from by simp [homog, MvPolynomial.algebraMap_eq], coeff_C]
    split_ifs with h
    · subst h
      intro s hs b
      simpa using isMH_C (B := D) (n := N + 1) a s hs b
    · exact isMH_zero _
  · rename_i p q hp hq
    intro γ
    rw [map_add (f := _), MvPolynomial.coeff_add]; exact isMH_add (hp γ) (hq γ)
  · rename_i p v hp
    intro γ
    obtain ⟨i, j⟩ := v
    rw [map_mul, show homog (X (i, j)) = hImg (K := K) (i, j) from aeval_X _ _]
    cases i using Fin.cases with
    | zero =>
      rw [hImg_zero, coeff_mul_X']
      split_ifs with h
      · have := hp (γ - Finsupp.single (Fin.castAdd D j) 1)
        convert this using 2 with b
        simp [castAdd_ne_natAdd j b]
      · exact isMH_zero _
    | succ i =>
      rw [hImg_succ, ← mul_assoc, mul_comm _ (C (X (i, j))), coeff_C_mul, coeff_mul_X']
      split_ifs with h
      · rw [mul_comm]
        have := isMH_mul_X (hp (γ - Finsupp.single (Fin.natAdd (N + 1) i) 1)) i j
        convert this using 1
        funext b
        have hpos : 1 ≤ γ (Fin.natAdd (N + 1) i) := by
          rw [Finsupp.mem_support_iff] at h; omega
        by_cases hb : b = i
        · subst hb; simp [Finsupp.single_apply]; omega
        · simp [Finsupp.single_apply, Pi.single_apply, hb, Ne.symm hb]
      · rw [mul_zero]; exact isMH_zero _

noncomputable def psi (sg : K →+* ℂ) (tt : Fin D × Fin (N + 1) → ℂ) :
    MvPolynomial (Fin (D + 1) × Fin (N + 1)) K →+* MvPolynomial (Fin (N + 1 + D)) ℂ :=
  (MvPolynomial.map (eval₂Hom sg tt)).comp (homog (K := K)).toRingHom

noncomputable def gpt (tt : Fin D × Fin (N + 1) → ℂ) (y : Fin (N + 1 + D) → ℂ) :
    Fin (D + 1) × Fin (N + 1) → ℂ :=
  fun p => Fin.cases (motive := fun _ => Fin (N + 1) → ℂ) (fun j => y (Fin.castAdd D j))
    (fun i j => y (Fin.natAdd (N + 1) i) * tt (i, j)) p.1 p.2

@[simp] theorem gpt_zero (tt : Fin D × Fin (N + 1) → ℂ) (y : Fin (N + 1 + D) → ℂ) (j : Fin (N + 1)) :
    gpt tt y (0, j) = y (Fin.castAdd D j) := by simp [gpt]

@[simp] theorem gpt_succ (tt : Fin D × Fin (N + 1) → ℂ) (y : Fin (N + 1 + D) → ℂ) (i : Fin D)
    (j : Fin (N + 1)) : gpt tt y (i.succ, j) = y (Fin.natAdd (N + 1) i) * tt (i, j) := by simp [gpt]

theorem eval_psi (sg : K →+* ℂ) (tt : Fin D × Fin (N + 1) → ℂ) (y : Fin (N + 1 + D) → ℂ)
    (q : MvPolynomial (Fin (D + 1) × Fin (N + 1)) K) :
    eval y (psi sg tt q) = eval₂ sg (gpt tt y) q := by
  have : (eval y).comp (psi sg tt) = eval₂Hom sg (gpt tt y) := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp [psi, homog, MvPolynomial.algebraMap_eq]
    · rintro ⟨i, j⟩
      cases i using Fin.cases with
      | zero => simp [psi, homog]
      | succ i => simp [psi, homog]
  exact congrArg (fun f => f q) this

theorem psi_injective (sg : K →+* ℂ) (tt : Fin D × Fin (N + 1) → ℂ)
    (hG : ∀ (a : Fin D → ℕ) (p : MvPolynomial (Fin D × Fin (N + 1)) K),
      IsMultiHomogeneous a p → p ≠ 0 → eval₂ sg tt p ≠ 0) :
    Function.Injective (psi sg tt) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro q hq
  apply homog_injective (K := K) (D := D) (N := N)
  rw [map_zero]
  refine MvPolynomial.ext _ _ fun γ => ?_
  simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  by_contra hne
  have h0 : AddMonoidAlgebra.coeff (psi sg tt q) γ = 0 := by rw [hq]; simp
  rw [psi, RingHom.comp_apply, coeff_map] at h0
  exact hG _ _ (homog_coeff_isMH q γ) hne (by simpa using h0)

theorem ae_gen (sg : K →+* ℂ) [Countable K] :
    ∀ᵐ z ∂(blockSphereProb D (N + 1)), ∀ (a : Fin D → ℕ) (p : MvPolynomial (Fin D × Fin (N + 1)) K),
      IsMultiHomogeneous a p → p ≠ 0 → eval₂ sg (blockPoint z) p ≠ 0 := by
  have := countable_mvPoly (σ := Fin D × Fin (N + 1)) (R := K)
  rw [ae_all_iff]; intro a
  rw [ae_all_iff]; intro p
  by_cases hp : IsMultiHomogeneous a p ∧ p ≠ 0
  · have hm : IsMultiHomogeneous a (MvPolynomial.map sg p) :=
      fun s hs => hp.1 s (support_map_subset _ _ hs)
    have hm0 : MvPolynomial.map sg p ≠ 0 := fun h0 =>
      hp.2 (map_injective sg sg.injective (by rw [h0, map_zero]))
    filter_upwards [ae_blockSphere_eval_ne_zero D (N + 1) a _ hm0 hm] with z hz _ _
    rwa [eval_map] at hz
  · exact Filter.Eventually.of_forall fun z h1 h2 => absurd ⟨h1, h2⟩ hp

theorem exists_gen (sg : K →+* ℂ) [Countable K] (tt : Fin D × Fin (N + 1) → ℂ)
    (hG : ∀ (a : Fin D → ℕ) (p : MvPolynomial (Fin D × Fin (N + 1)) K),
      IsMultiHomogeneous a p → p ≠ 0 → eval₂ sg tt p ≠ 0)
    (Q : MvPolynomial (Fin (N + 1 + D)) ℂ) (hQ : Q ≠ 0) :
    ∃ y : Fin (N + 1 + D) → ℂ, eval y Q ≠ 0 ∧
      ∀ q : MvPolynomial (Fin (D + 1) × Fin (N + 1)) K, q ≠ 0 → eval₂ sg (gpt tt y) q ≠ 0 := by
  have := countable_mvPoly (σ := Fin (D + 1) × Fin (N + 1)) (R := K)
  have h1 := ae_eval_ne_zero_of_ne_zero_fin _ Q hQ
  have h2 : ∀ᵐ y ∂(volume : Measure (Fin (N + 1 + D) → ℂ)),
      ∀ q : MvPolynomial (Fin (D + 1) × Fin (N + 1)) K, q ≠ 0 → eval y (psi sg tt q) ≠ 0 := by
    rw [ae_all_iff]; intro q
    by_cases hq : q = 0
    · exact Filter.Eventually.of_forall fun y h => absurd hq h
    · have hq' : psi sg tt q ≠ 0 := fun h0 => hq (psi_injective sg tt hG (by rw [h0, map_zero]))
      filter_upwards [ae_eval_ne_zero_of_ne_zero_fin _ _ hq'] with y hy _ using hy
  have : (ae (volume : Measure (Fin (N + 1 + D) → ℂ))).NeBot := ae_neBot.2 (NeZero.ne _)
  obtain ⟨y, hy1, hy2⟩ := (h1.and h2).exists
  exact ⟨y, hy1, fun q hq => by rw [← eval_psi]; exact hy2 q hq⟩

end ReciprocityTheory.ChartRestriction.G.T0.NPB
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.RegHor
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.RegHorPf
namespace ReciprocityTheory.ChartRestriction.G.T0

open IsLocalRing

theorem not_isUnit_algebraMap_of_finite {O V : Type} [CommRing O] [IsLocalRing O] [CommRing V]
    [Nontrivial V] [Algebra O V] [Module.Finite O V] (π : O) (hπ : π ∈ maximalIdeal O) :
    ¬ IsUnit (algebraMap O V π) := by
  intro hu
  have htop : (⊤ : Submodule O V) ≤ maximalIdeal O • ⊤ := by
    intro v _
    obtain ⟨w, hw⟩ : ∃ w : V, algebraMap O V π * w = v :=
      ⟨hu.unit⁻¹ * v, by rw [← mul_assoc, IsUnit.mul_val_inv, one_mul]⟩
    rw [← hw, ← Algebra.smul_def]
    exact Submodule.smul_mem_smul hπ Submodule.mem_top
  have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal O) ⊤
    Module.Finite.fg_top htop (IsLocalRing.maximalIdeal_le_jacobson _)
  have h1 : (1 : V) ∈ (⊥ : Submodule O V) := hbot ▸ Submodule.mem_top
  exact one_ne_zero ((Submodule.mem_bot O).mp h1)

theorem reg_horizontal_pf {O A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [CharZero O]
    [CommRing A] [IsDomain A] [Algebra O A] [Algebra.FiniteType O A] [Module.Flat O A]
    (P : Ideal A) [P.IsPrime] (hh : ¬ Ideal.map (algebraMap O A) (maximalIdeal O) ≤ P)
    (hmeet : P ⊔ Ideal.map (algebraMap O A) (maximalIdeal O) ≠ ⊤) (e : A) (he : e ≠ 0)
    (f : FractionRing A)
    (hdvr : (¬ ∃ a s : A, s ∉ P ∧ f * algebraMap A (FractionRing A) s = algebraMap A (FractionRing A) a) →
      ∃ a s : A, a ∈ P ∧ s ∉ P ∧ f⁻¹ * algebraMap A (FractionRing A) s = algebraMap A (FractionRing A) a)
    (hf : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra O V]
      [Module.Finite O V] (φ : A →ₐ[O] V) (a b : A),
      f * algebraMap A (FractionRing A) b = algebraMap A (FractionRing A) a → φ b ≠ 0 → φ e ≠ 0 →
      ∃ v : V, φ a = v * φ b) :
    ∃ a s : A, s ∉ P ∧ f * algebraMap A (FractionRing A) s = algebraMap A (FractionRing A) a := by
  classical
  by_contra hno
  obtain ⟨a, s, haP, hsP, hfas⟩ := hdvr hno
  have hinj : Function.Injective (algebraMap A (FractionRing A)) :=
    IsFractionRing.injective A (FractionRing A)
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hno ⟨0, 1, (Ideal.ne_top_iff_one P).mp (Ideal.IsPrime.ne_top ‹_›), by simp⟩
  have hs0 : algebraMap A (FractionRing A) s ≠ 0 := by
    rw [map_ne_zero_iff _ hinj]; rintro rfl; exact hsP P.zero_mem
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, mul_eq_zero] at hfas
    rcases hfas with h | h
    · exact hf0 (inv_eq_zero.mp h)
    · exact hs0 h
  have hfa : f * algebraMap A (FractionRing A) a = algebraMap A (FractionRing A) s := by
    rw [← hfas, ← mul_assoc, mul_inv_cancel₀ hf0, one_mul]

  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hmax : maximalIdeal O = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  have hϖm : ϖ ∈ maximalIdeal O := (mem_maximalIdeal _).mpr hϖ.not_isUnit
  have hmapw : Ideal.map (algebraMap O A) (maximalIdeal O) = Ideal.span {algebraMap O A ϖ} := by
    rw [hmax, Ideal.map_span, Set.image_singleton]
  have hwP : algebraMap O A ϖ ∉ P := fun h =>
    hh (by rw [hmapw, Ideal.span_le, Set.singleton_subset_iff]; exact h)
  have hws : algebraMap O A ϖ * s ∉ P := fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hwP hsP
  have hws0 : algebraMap A (FractionRing A) (algebraMap O A ϖ * s) ≠ 0 := by
    rw [map_ne_zero_iff _ hinj]; rintro h; exact hws (h ▸ P.zero_mem)

  have hOA : Function.Injective (algebraMap O A) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hx0
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
    rw [map_mul, map_pow, mul_eq_zero] at hx
    rcases hx with h | h
    · exact (u.isUnit.map (algebraMap O A)).ne_zero h
    · exact hwP (pow_eq_zero_iff'.mp h |>.1 ▸ P.zero_mem)

  set y : FractionRing A := algebraMap A (FractionRing A) a /
    algebraMap A (FractionRing A) (algebraMap O A ϖ * s) with hy
  let B : Subalgebra A (FractionRing A) := Algebra.adjoin A {y}
  have hyB : y ∈ B := Algebra.subset_adjoin rfl

  let S : Subalgebra A (FractionRing A) :=
    { carrier := {x | ∃ a' p t : A, p ∈ P ∧ t ∉ P ∧
        x * algebraMap A (FractionRing A) t = algebraMap A (FractionRing A) (a' * t + p)}
      mul_mem' := by
        rintro x1 x2 ⟨a1, p1, t1, hp1, ht1, h1⟩ ⟨a2, p2, t2, hp2, ht2, h2⟩
        refine ⟨a1 * a2, a1 * t1 * p2 + a2 * t2 * p1 + p1 * p2, t1 * t2,
          P.add_mem (P.add_mem (P.mul_mem_left _ hp2) (P.mul_mem_left _ hp1)) (P.mul_mem_left _ hp2),
          fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim ht1 ht2, ?_⟩
        have : x1 * x2 * algebraMap A (FractionRing A) (t1 * t2) =
            (x1 * algebraMap A (FractionRing A) t1) * (x2 * algebraMap A (FractionRing A) t2) := by
          rw [map_mul]; ring
        rw [this, h1, h2, ← map_mul]
        congr 1
        ring
      add_mem' := by
        rintro x1 x2 ⟨a1, p1, t1, hp1, ht1, h1⟩ ⟨a2, p2, t2, hp2, ht2, h2⟩
        refine ⟨a1 + a2, p1 * t2 + p2 * t1, t1 * t2,
          P.add_mem (P.mul_mem_right _ hp1) (P.mul_mem_right _ hp2),
          fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim ht1 ht2, ?_⟩
        have : (x1 + x2) * algebraMap A (FractionRing A) (t1 * t2) =
            (x1 * algebraMap A (FractionRing A) t1) * algebraMap A (FractionRing A) t2 +
              (x2 * algebraMap A (FractionRing A) t2) * algebraMap A (FractionRing A) t1 := by
          rw [map_mul]; ring
        rw [this, h1, h2, ← map_mul, ← map_mul, ← map_add (f := _)]
        congr 1
        ring
      algebraMap_mem' := fun r => ⟨r, 0, 1, P.zero_mem, (Ideal.ne_top_iff_one P).mp
        (Ideal.IsPrime.ne_top ‹_›), by simp⟩ }
  have hyS : y ∈ S := ⟨0, a, algebraMap O A ϖ * s, haP, hws, by
    rw [hy, div_mul_cancel₀ _ hws0]; simp⟩
  have hBS : B ≤ S := Algebra.adjoin_le (Set.singleton_subset_iff.mpr hyS)

  have hcoe : ∀ r : O, ((algebraMap O B r : B) : FractionRing A) =
      algebraMap A (FractionRing A) (algebraMap O A r) := fun r => by
    rw [← IsScalarTower.algebraMap_apply O A (FractionRing A)]
    rfl
  have hOB : Function.Injective (algebraMap O B) := by
    intro r1 r2 h
    apply hOA; apply hinj
    rw [← hcoe, ← hcoe, h]
  have : Module.Flat O B := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout]
    refine eq_bot_iff.mpr fun x hx => ?_
    obtain ⟨r, hr⟩ := (Submodule.mem_torsion_iff x).mp hx
    rw [Submonoid.smul_def, Algebra.smul_def] at hr
    rcases mul_eq_zero.mp hr with h | h
    · exact absurd (hOB (h.trans (map_zero _).symm)) (nonZeroDivisors.coe_ne_zero r)
    · rw [h]; exact Submodule.zero_mem _
  have : Algebra.FiniteType A B :=
    (Subalgebra.fg_iff_finiteType B).mp (by simpa using Subalgebra.fg_adjoin_finset ({y} : Finset _))
  have : Algebra.FiniteType O B := Algebra.FiniteType.trans (S := A) inferInstance inferInstance

  have hsp : Ideal.map (algebraMap O B) (maximalIdeal O) ≠ ⊤ := by
    rw [hmax, Ideal.map_span, Set.image_singleton, Ne, Ideal.span_singleton_eq_top]
    rintro ⟨u, hu⟩
    obtain ⟨a', p, t, hp, ht, h⟩ := hBS (↑u⁻¹ : B).2
    apply hmeet
    rw [eq_top_iff, hmapw]
    have hwb : algebraMap A (FractionRing A) (algebraMap O A ϖ) * ((↑u⁻¹ : B) : FractionRing A) = 1 := by
      rw [← hcoe, ← hu, ← Subalgebra.coe_mul, Units.mul_inv, Subalgebra.coe_one]
    have hkey : algebraMap A (FractionRing A) (t - algebraMap O A ϖ * (a' * t + p)) = 0 := by
      rw [map_sub, map_mul, ← h]
      calc algebraMap A (FractionRing A) t - algebraMap A (FractionRing A) (algebraMap O A ϖ) *
            (((↑u⁻¹ : B) : FractionRing A) * algebraMap A (FractionRing A) t)
          = algebraMap A (FractionRing A) t - (algebraMap A (FractionRing A) (algebraMap O A ϖ) *
            ((↑u⁻¹ : B) : FractionRing A)) * algebraMap A (FractionRing A) t := by ring
        _ = 0 := by rw [hwb, one_mul, sub_self]
    have hk := hinj (hkey.trans (map_zero _).symm)
    have htw : t * (1 - algebraMap O A ϖ * a') ∈ P := by
      have : t * (1 - algebraMap O A ϖ * a') = algebraMap O A ϖ * p := by
        linear_combination hk
      rw [this]; exact P.mul_mem_left _ hp
    have h1 : 1 - algebraMap O A ϖ * a' ∈ P :=
      (Ideal.IsPrime.mem_or_mem ‹_› htw).resolve_left ht
    have : (1 : A) = (1 - algebraMap O A ϖ * a') + algebraMap O A ϖ * a' := by ring
    intro z _
    rw [← mul_one z, this, mul_add]
    exact Submodule.add_mem _ (Ideal.mem_sup_left (P.mul_mem_left _ h1))
      (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _
        (Ideal.subset_span rfl))))

  have heas : algebraMap A B (e * a * s) ≠ 0 := by
    intro h
    have h' := congrArg (fun x : B => (x : FractionRing A)) h
    simp only [Subalgebra.coe_algebraMap, ZeroMemClass.coe_zero] at h'
    have := hinj (h'.trans (map_zero _).symm)
    rcases mul_eq_zero.mp this with h2 | h2
    · rcases mul_eq_zero.mp h2 with h3 | h3
      · exact he h3
      · exact ha0 h3
    · exact hsP (h2 ▸ P.zero_mem)
  obtain ⟨V, _, _, _, _, _, φ, hφ⟩ := av_point hsp _ heas
  let φA : A →ₐ[O] V := φ.comp (IsScalarTower.toAlgHom O A B)
  have hφA : ∀ x : A, φA x = φ (algebraMap A B x) := fun x => rfl
  rw [map_mul, map_mul, map_mul, map_mul] at hφ
  have hφe : φA e ≠ 0 := by rw [hφA]; intro h; apply hφ; rw [h]; ring
  have hφa : φA a ≠ 0 := by rw [hφA]; intro h; apply hφ; rw [h]; ring
  have hφs : φA s ≠ 0 := by rw [hφA]; intro h; apply hφ; rw [h]; ring
  obtain ⟨v, hv⟩ := hf V φA s a hfa hφa hφe

  have hab : algebraMap A B a = algebraMap O B ϖ * algebraMap A B s * ⟨y, hyB⟩ := by
    apply Subtype.ext
    simp only [Subalgebra.coe_mul, Subalgebra.coe_algebraMap]
    rw [IsScalarTower.algebraMap_apply O A (FractionRing A) ϖ, hy, ← map_mul]
    field_simp
  have hφab : φA a = algebraMap O V ϖ * φA s * φ ⟨y, hyB⟩ := by
    rw [hφA, hab, map_mul, map_mul, AlgHom.commutes]
    rfl
  rw [hφab] at hv
  have hunit : algebraMap O V ϖ * (v * φ ⟨y, hyB⟩) = 1 := by
    have h2 : φA s * (1 - algebraMap O V ϖ * (v * φ ⟨y, hyB⟩)) = 0 := by
      linear_combination hv
    have h3 := (mul_eq_zero.mp h2).resolve_left hφs
    linear_combination -h3
  exact not_isUnit_algebraMap_of_finite ϖ hϖm
    ⟨⟨algebraMap O V ϖ, v * φ ⟨y, hyB⟩, hunit, by rw [mul_comm]; exact hunit⟩, rfl⟩

end ReciprocityTheory.ChartRestriction.G.T0
end

namespace ReciprocityTheory.ChartRestriction.G.T0

open IsLocalRing

theorem reg_horizontal {O A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [CharZero O]
    [CommRing A] [IsDomain A] [Algebra O A] [Algebra.FiniteType O A] [Module.Flat O A]
    (P : Ideal A) [P.IsPrime] (hh : ¬ Ideal.map (algebraMap O A) (maximalIdeal O) ≤ P)
    (hmeet : P ⊔ Ideal.map (algebraMap O A) (maximalIdeal O) ≠ ⊤) (e : A) (he : e ≠ 0)
    (f : FractionRing A)
    (hdvr : (¬ ∃ a s : A, s ∉ P ∧ f * algebraMap A (FractionRing A) s = algebraMap A (FractionRing A) a) →
      ∃ a s : A, a ∈ P ∧ s ∉ P ∧ f⁻¹ * algebraMap A (FractionRing A) s = algebraMap A (FractionRing A) a)
    (hf : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra O V]
      [Module.Finite O V] (φ : A →ₐ[O] V) (a b : A),
      f * algebraMap A (FractionRing A) b = algebraMap A (FractionRing A) a → φ b ≠ 0 → φ e ≠ 0 →
      ∃ v : V, φ a = v * φ b) :
    ∃ a s : A, s ∉ P ∧ f * algebraMap A (FractionRing A) s = algebraMap A (FractionRing A) a := by
  exact reg_horizontal_pf P hh hmeet e he f hdvr hf

end ReciprocityTheory.ChartRestriction.G.T0
end
