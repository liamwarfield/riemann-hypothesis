module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCompletionEqLatticeVectorAddNsmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupIsogenyHeightEqDualSameDegree
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTestDivisorsKltLcPencilBoundaries
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotGlobalHolds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectExtendsOverDvrOfAbelianModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPotentialBlockDecomposition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransgressionCorrectionIsTopDegreeForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoTraitUniformisationsMatchingData
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologyLaurentAbsIntClosedLocalDomai
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramedTorsionPointTorusExtensionEqOfLiesOver

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneFrobeniusTwistBijectiveRelFrobenius
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneFrobeniusTwistBijectiveRelFrobenius
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.Dieu

theorem wittMap_frobRing_bijective (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] : Function.Bijective (WittVector.map (p := p) (frobRing (p_eq_zero p k))) := by
  have hb : Function.Bijective (frobRing (p_eq_zero p k)) := by
    have e : ⇑(frobRing (p_eq_zero p k)) = ⇑(frobenius k p) :=
      funext fun r => by rw [frobRing_apply, frobenius_def]
    rw [e]
    exact bijective_frobenius k p
  exact ⟨WittVector.map_injective _ hb.1, WittVector.map_surjective _ hb.2⟩

theorem bijective_of_basis {R R' M M' : Type} [CommRing R] [CommRing R'] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R' M'] (σ : R →+* R') (hσ : Function.Bijective σ) (f : M →+ M')
    (hf : ∀ (a : R) (m : M), f (a • m) = σ a • f m) {ι : Type} [Fintype ι] (b : Module.Basis ι R M)
    (b' : Module.Basis ι R' M') (hb : ∀ i, b' i = f (b i)) : Function.Bijective f := by
  have key : ∀ c : ι → R, f (∑ i, c i • b i) = ∑ i, σ (c i) • b' i := fun c => by
    rw [map_sum f]
    exact Finset.sum_congr rfl fun i _ => by rw [hf, hb]
  refine ⟨(injective_iff_map_eq_zero f).2 fun m hm => ?_, fun x => ?_⟩
  · rw [← b.sum_repr m, key] at hm
    have : ∀ i, b.repr m i = 0 := fun i => by
      have := Fintype.linearIndependent_iff.1 b'.linearIndependent _ hm i
      exact hσ.1 (this.trans (map_zero σ).symm)
    rw [← b.sum_repr m]
    simp [this]
  · obtain ⟨c, hc⟩ : ∃ c : ι → R, ∀ i, σ (c i) = b'.repr x i :=
      ⟨fun i => Function.surjInv hσ.2 (b'.repr x i), fun i => Function.surjInv_eq hσ.2 _⟩
    refine ⟨∑ i, c i • b i, ?_⟩
    rw [key]
    simp only [hc]
    exact b'.sum_repr x

theorem frobTwist_module (p : ℕ) [Fact p.Prime] (B : Base p fun _ _ _ => True)
    (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k) :
    Function.Bijective (B.smap trivial trivial (frobProj (p_eq_zero p k) G)) ∧
    (∀ m, B.map trivial trivial (relFrob (p_eq_zero p k) G)
      (B.smap trivial trivial (frobProj (p_eq_zero p k) G) m) = B.F G trivial m) ∧
    ∀ m n, B.smap trivial trivial (frobProj (p_eq_zero p k) G) n =
      B.map trivial trivial (verschiebung (p_eq_zero p k) G) m → B.F G trivial n = p • m := by
  have h2 : ∀ m, B.map trivial trivial (relFrob (p_eq_zero p k) G)
      (B.smap trivial trivial (frobProj (p_eq_zero p k) G) m) = B.F G trivial m := fun m =>
    (B.smap_comp trivial trivial trivial (frobProj (p_eq_zero p k) G)
      (SemiHom.ofHom (relFrob (p_eq_zero p k) G)) (absFrob (p_eq_zero p k) G)
      (fun n a => by rw [SemiHom.ofHom_app, relFrob_app_frobProj, absFrob_app]) m).symm
  refine ⟨?_, h2, fun m n e => ?_⟩
  · haveI := B.free G trivial
    haveI := B.finite G trivial
    letI := (frobRing (p_eq_zero p k)).toAlgebra
    obtain ⟨b', hb'⟩ := GlobalTheory.T.dieudonne_baseChange_basis p (fun _ _ _ => True) B k k G trivial trivial _
      (Module.Free.chooseBasis (WittVector p k) (B.M G trivial))
    exact bijective_of_basis _ (wittMap_frobRing_bijective p k) _
      (fun a m => B.smap_smul trivial trivial _ a m) _ b' hb'
  · obtain ⟨-, hc, -⟩ := GlobalTheory.T.dieudonneFunctorBase_functor_properties p (fun _ _ _ => True) B k G
      (frobTwist (p_eq_zero p k) G) G trivial trivial trivial
    obtain ⟨hid, -, -, -, hp, -⟩ := GlobalTheory.T.dieudonneFunctorBase_functor_properties p (fun _ _ _ => True) B k G G G trivial trivial trivial
    rw [← h2, e, ← LinearMap.comp_apply, ← hc, relFrob_comp_verschiebung, ← pow_one (p : ℤ_[p]), hp,
      pow_one, hid, LinearMap.id_apply]

end GlobalTheory.Dieu
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneFrobeniusTwistBijectiveRelFrobeniusStatement
open GlobalTheory.PDivGroup GlobalTheory.Dieu

theorem _root_.GlobalTheory.T.dieudonne_frobeniusTwist_bijective_relFrobenius :
    ∀ (p : ℕ) [Fact p.Prime] (B : GlobalTheory.Dieu.Base p fun _ _ _ => True)
      (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : GlobalTheory.PDivGroup p k),
      Function.Bijective (B.smap trivial trivial (frobProj (p_eq_zero p k) G)) ∧
      (∀ m, B.map trivial trivial (relFrob (p_eq_zero p k) G)
        (B.smap trivial trivial (frobProj (p_eq_zero p k) G) m) = B.F G trivial m) ∧
      ∀ m n, B.smap trivial trivial (frobProj (p_eq_zero p k) G) n =
        B.map trivial trivial (verschiebung (p_eq_zero p k) G) m →
        B.F G trivial n = p • m :=
  @GlobalTheory.Dieu.frobTwist_module
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalLogCanonicalThresholdAtPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalLogCanonicalThresholdAtPoint
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem exists_threshold_lcAt_not_kltAt : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X) (D B : X → ℚ) (x : X), 0 < m → IsLogCanonicalMultiple p n Δ m G → IsQCart D → IsQCart B → KltAt p n (Δ + D) x → ¬ KltAt p n (Δ + D + B) x → ∃ c : ℚ, 0 < c ∧ c ≤ 1 ∧ LcAt p n (Δ + D + c • B) x ∧ ¬ KltAt p n (Δ + D + c • B) x := by
  intro hP X _ _ _ p n hp hn Δ m G D B x hm hG hD hB hk hnk
  haveI : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp).1
  obtain ⟨mD, D₀, hmD, -, rfl⟩ := hD
  obtain ⟨m', B₀, hm', -, rfl⟩ := hB
  obtain ⟨η, hη, hG₁⟩ := isLogCanonicalMultiple_add_qWeil X p n Δ m mD G D₀ hm hmD hG
  have hm₁ : 0 < m * mD := Nat.mul_pos hm hmD
  obtain ⟨S, hSf, hS⟩ :=
    GlobalTheory.T.finite_test_divisors_klt_lc_pencil_boundaries hP X p n hp hn η (m * mD) (mD • G + m • D₀) B₀ hη hm₁
  obtain ⟨g, hg⟩ := (mD • G + m • D₀).exists_isEqn x
  obtain ⟨f, hf⟩ := B₀.exists_isEqn x
  have hL := hG₁ x g hg
  have hBf : ∀ z, z ⤳ x → ∀ E : DivOver p, E.IsAt z → qWeil B₀ m' z = (E.ord f : ℚ) / m' := by
    intro z hz E hE
    obtain ⟨V, hV, hfV⟩ := hf.exists_nhds
    rw [qWeil, (hfV z (hz.mem_open V.isOpen hV)).mult_eq, ← hE.ord_eq]
  have hm'0 : (m' : ℚ) ≠ 0 := by exact_mod_cast hm'.ne'
  obtain ⟨a, ha⟩ : ∃ a : DivOver p → ℚ, ∀ E, a E = discrep E η (m * mD) g := ⟨_, fun _ => rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : DivOver p → ℚ, ∀ E, t E = (E.ord f : ℚ) / m' := ⟨_, fun _ => rfl⟩
  have hrw (c : ℚ) (E : DivOver p) :
      a E - c * t E = discrep E η (m * mD) g - c / m' * E.ord f := by
    rw [ha, ht]; ring
  have step (c : ℚ) : ∃ (m'' : ℕ) (g'' : X.functionFieldˣ), 0 < m'' ∧
      IsLogEqn p (Δ + qWeil D₀ mD + c • qWeil B₀ m') η x m'' g'' ∧
      ∀ E : DivOver p, discrep E η m'' g'' = a E - c * t E := by
    obtain ⟨m'', g'', h1, h2, h3⟩ :=
      GlobalTheory.T.isLogCanonicalLocalEquation_add_smul_divisor X p n (Δ + qWeil D₀ mD) (qWeil B₀ m') η x (m * mD) m' g f c hm₁ hm' hL hBf
    exact ⟨m'', g'', h1, h2, fun E => by rw [h3, ha, ht]⟩
  have hka : ∀ E : DivOver p, E.Through x → -1 < a E := fun E hE => by
    rw [ha]; exact (hL.kltAt_iff hn hη hm₁).1 hk E hE

  obtain ⟨E₀, hE₀S, hE₀x, hE₀⟩ : ∃ E ∈ S, E.Through x ∧ a E - 1 * t E ≤ -1 := by
    by_contra hc
    push_neg at hc
    obtain ⟨m₁', g₁, hm₁', hL₁, hd₁⟩ := step 1
    rw [one_smul] at hL₁
    refine hnk ((hL₁.kltAt_iff hn hη hm₁').2 fun E hE => ?_)
    rw [hd₁, hrw]
    refine (hS x g f (1 / m') hg hf).1 (fun E' hE' hE'x => ?_) E hE
    rw [← hrw]
    exact hc E' hE' hE'x
  have hT0 : E₀ ∈ {E | E ∈ S ∧ E.Through x ∧ 0 < t E} :=
    ⟨hE₀S, hE₀x, by have := hka E₀ hE₀x; linarith⟩
  obtain ⟨E₁, ⟨hE₁S, hE₁x, hE₁t⟩, hmin⟩ :=
    Set.exists_min_image {E | E ∈ S ∧ E.Through x ∧ 0 < t E} (fun E => (1 + a E) / t E)
      (hSf.subset fun E hE => hE.1) ⟨E₀, hT0⟩
  have hE₁a := hka E₁ hE₁x
  refine ⟨(1 + a E₁) / t E₁, div_pos (by linarith) hE₁t, ?_, ?_⟩
  · refine (hmin E₀ hT0).trans ?_
    rw [div_le_one hT0.2.2]
    linarith
  obtain ⟨m'', g'', hm'', hL'', hd''⟩ := step ((1 + a E₁) / t E₁)
  refine ⟨(lcAt_iff_of_isLogEqn X p n hp hn _ η x m'' g'' hη hm'' hL'').2 fun E hE => ?_,
    fun hk' => ?_⟩
  · rw [hd'', hrw]
    refine (hS x g f ((1 + a E₁) / t E₁ / m') hg hf).2 (fun E' hE' hE'x => ?_) E hE
    rw [← hrw]
    by_cases htE : 0 < t E'
    · have := hmin E' ⟨hE', hE'x, htE⟩
      rw [le_div_iff₀ htE] at this
      linarith
    · have h0 : 0 ≤ (1 + a E₁) / t E₁ := (div_pos (by linarith) hE₁t).le
      have := hka E' hE'x
      nlinarith
  · have := (hL''.kltAt_iff hn hη hm'').1 hk' E₁ hE₁x
    rw [hd'', div_mul_cancel₀ _ hE₁t.ne'] at this
    linarith

end GlobalTheory.PairStep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalLogCanonicalThresholdAtPointStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_logCanonicalThreshold_at_point : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X) (D B : X → ℚ) (x : X), 0 < m → IsLogCanonicalMultiple p n Δ m G → IsQCart D → IsQCart B → KltAt p n (Δ + D) x → ¬ KltAt p n (Δ + D + B) x → ∃ c : ℚ, 0 < c ∧ c ≤ 1 ∧ LcAt p n (Δ + D + c • B) x ∧ ¬ KltAt p n (Δ + D + c • B) x := by
  first | exact @GlobalTheory.PairStep.exists_threshold_lcAt_not_kltAt | exact GlobalTheory.PairStep.exists_threshold_lcAt_not_kltAt | (intros; apply GlobalTheory.PairStep.exists_threshold_lcAt_not_kltAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardBoundedHomogeneousIntFormFamilies
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardBoundedHomogeneousIntFormFamilies
open Filter Topology MvPolynomial GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp.Count

theorem abs_intCast_le_iff (c : ℤ) {R : ℝ} (hR : 0 ≤ R) :
    |(c : ℝ)| ≤ R ↔ c ∈ Finset.Icc (-(⌊R⌋₊ : ℤ)) (⌊R⌋₊ : ℤ) := by
  rw [Finset.mem_Icc, ← abs_le, ← Int.cast_abs, ← Int.le_floor, Int.natCast_floor_eq_floor hR]

theorem coeff_sum_monomial {D q : ℕ} [Fintype {α : Fin (D + 1) →₀ ℕ // α.degree = q}]
    (g : {α : Fin (D + 1) →₀ ℕ // α.degree = q} → ℤ) (β : Fin (D + 1) →₀ ℕ) :
    AddMonoidAlgebra.coeff (∑ a, monomial a.1 (g a)) β = if h : β.degree = q then g ⟨β, h⟩ else 0 := by
  classical
  rw [coeff_sum]
  simp only [coeff_monomial]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨β, h⟩]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro e
      exact hb (Subtype.ext e)
    · simp
  · refine Finset.sum_eq_zero fun a _ => ?_
    rw [if_neg]
    rintro rfl
    exact h a.2

theorem coeff_eq_zero_of_isHomogeneous {D q : ℕ} {P : MvPolynomial (Fin (D + 1)) ℤ}
    (hP : P.IsHomogeneous q) {β : Fin (D + 1) →₀ ℕ} (hβ : β.degree ≠ q) : AddMonoidAlgebra.coeff P β = 0 := by
  by_contra hc
  exact hβ (by rw [Finsupp.degree_eq_weight_one]; exact hP hc)

end GlobalTheory.HSAmp.Count

open GlobalTheory.HSAmp.Count in
theorem GlobalTheory.HSAmp.card_bounded_forms : ∀ (D q δ : ℕ) (R : ℝ), 0 ≤ R → {T : Fin δ → MvPolynomial (Fin (D + 1)) ℤ | (∀ i, (T i).IsHomogeneous q) ∧ ∀ i α, |((AddMonoidAlgebra.coeff (T i) α : ℤ) : ℝ)| ≤ R}.Finite ∧ {T : Fin δ → MvPolynomial (Fin (D + 1)) ℤ | (∀ i, (T i).IsHomogeneous q) ∧ ∀ i α, |((AddMonoidAlgebra.coeff (T i) α : ℤ) : ℝ)| ≤ R}.ncard = (2 * ⌊R⌋₊ + 1) ^ (δ * (q + D).choose D) ∧ Nat.card {α : Fin (D + 1) →₀ ℕ // α.degree = q} = (q + D).choose D ∧ Module.finrank ℤ (homogeneousSubmodule (Fin (D + 1)) ℤ q) = (q + D).choose D ∧ Module.Finite ℤ (homogeneousSubmodule (Fin (D + 1)) ℤ q) := by
  intro D q δ R hR
  classical
  have hAcard : Nat.card {α : Fin (D + 1) →₀ ℕ // α.degree = q} = (q + D).choose D := by
    rw [GlobalTheory.natCard_degree_eq, Fintype.card_fin, show q + (D + 1) - 1 = q + D by omega,
      Nat.choose_symm_add]
  haveI : Finite {α : Fin (D + 1) →₀ ℕ // α.degree = q} := (Finsupp.finite_of_degree_eq q).to_subtype
  letI : Fintype {α : Fin (D + 1) →₀ ℕ // α.degree = q} := Fintype.ofFinite _
  set S := {T : Fin δ → MvPolynomial (Fin (D + 1)) ℤ | (∀ i, (T i).IsHomogeneous q) ∧
    ∀ i α, |((AddMonoidAlgebra.coeff (T i) α : ℤ) : ℝ)| ≤ R} with hS
  let F : S → (Fin δ → {α : Fin (D + 1) →₀ ℕ // α.degree = q} →
      Finset.Icc (-(⌊R⌋₊ : ℤ)) (⌊R⌋₊ : ℤ)) :=
    fun T i a => ⟨AddMonoidAlgebra.coeff (T.1 i) a.1, (abs_intCast_le_iff _ hR).1 (T.2.2 i a.1)⟩
  have hF : Function.Bijective F := by
    constructor
    · rintro ⟨T, hT⟩ ⟨T', hT'⟩ h
      apply Subtype.ext
      funext i
      ext β
      by_cases hβ : β.degree = q
      · have := congrArg Subtype.val (congrFun (congrFun h i) ⟨β, hβ⟩)
        simpa [F] using this
      · rw [coeff_eq_zero_of_isHomogeneous (hT.1 i) hβ, coeff_eq_zero_of_isHomogeneous (hT'.1 i) hβ]
    · intro f
      refine ⟨⟨fun i => ∑ a, monomial a.1 ((f i a : ℤ)), fun i => ?_, fun i β => ?_⟩, ?_⟩
      · exact IsHomogeneous.sum _ _ _ fun a _ => isHomogeneous_monomial _ a.2
      · rw [coeff_sum_monomial]
        split_ifs with h
        · exact (abs_intCast_le_iff _ hR).2 (f i ⟨β, h⟩).2
        · simpa using hR
      · funext i a
        apply Subtype.ext
        change AddMonoidAlgebra.coeff (∑ b, monomial b.1 (f i b : ℤ)) a.1 = (f i a : ℤ)
        rw [coeff_sum_monomial, dif_pos a.2]
  let e := Equiv.ofBijective F hF
  have hfin : S.Finite := Set.finite_coe_iff.1 (Finite.of_equiv _ e.symm)
  refine ⟨hfin, ?_, hAcard, ?_, ?_⟩
  · rw [← Nat.card_coe_set_eq, Nat.card_congr e, Nat.card_fun, Nat.card_fun, hAcard,
      Nat.card_eq_fintype_card, Fintype.card_coe, Int.card_Icc, Nat.card_eq_fintype_card,
      Fintype.card_fin, ← pow_mul, mul_comm]
    congr 1
    omega
  · rw [homogeneousSubmodule_eq_finsupp_supported]
    exact (Module.finrank_eq_nat_card_basis
      (basisRestrictSupport ℤ {d : Fin (D + 1) →₀ ℕ | d.degree = q})).trans hAcard
  · rw [homogeneousSubmodule_eq_finsupp_supported]
    haveI : Finite {d : Fin (D + 1) →₀ ℕ | d.degree = q} := (Finsupp.finite_of_degree_eq q).to_subtype
    exact Module.Finite.of_basis (basisRestrictSupport ℤ {d : Fin (D + 1) →₀ ℕ | d.degree = q})
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardBoundedHomogeneousIntFormFamiliesStatement
open Filter Topology MvPolynomial GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_bounded_homogeneous_int_form_families : ∀ (D q δ : ℕ) (R : ℝ), 0 ≤ R → {T : Fin δ → MvPolynomial (Fin (D + 1)) ℤ | (∀ i, (T i).IsHomogeneous q) ∧ ∀ i α, |((AddMonoidAlgebra.coeff (T i) α : ℤ) : ℝ)| ≤ R}.Finite ∧ {T : Fin δ → MvPolynomial (Fin (D + 1)) ℤ | (∀ i, (T i).IsHomogeneous q) ∧ ∀ i α, |((AddMonoidAlgebra.coeff (T i) α : ℤ) : ℝ)| ≤ R}.ncard = (2 * ⌊R⌋₊ + 1) ^ (δ * (q + D).choose D) ∧ Nat.card {α : Fin (D + 1) →₀ ℕ // α.degree = q} = (q + D).choose D ∧ Module.finrank ℤ (homogeneousSubmodule (Fin (D + 1)) ℤ q) = (q + D).choose D ∧ Module.Finite ℤ (homogeneousSubmodule (Fin (D + 1)) ℤ q) := by
  first | exact @GlobalTheory.HSAmp.card_bounded_forms | exact GlobalTheory.HSAmp.card_bounded_forms | (intros; apply GlobalTheory.HSAmp.card_bounded_forms <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackKernelOfKernelPair
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES GlobalTheory.IwLevel
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)
open scoped CategoryTheory.Obj

namespace GlobalTheory.UPel.HT.ES.IsogDVR

theorem isPullback_kernel_of_kernelPair {S : Scheme.{0}} {A H B : Over S} [GrpObj A] [GrpObj B] (i : H ⟶ A)
    [Mono i] (q : A ⟶ B) [IsMonHom q] (h : IsPullback ((fst H A ≫ i) * snd H A) (snd H A) q q) :
    IsPullback i (toUnit H) q η[B] := by
  have hi : i ≫ q = 1 := by
    have := congrArg (fun u => lift (𝟙 H) (1 : H ⟶ A) ≫ u) h.w
    simp only [← Category.assoc, MonObj.comp_mul, lift_fst, lift_snd, Category.id_comp, _root_.mul_one,
      MonObj.one_comp] at this
    exact this
  refine ⟨⟨by rw [hi, Hom.one_def]⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => h.lift s.fst 1 (by rw [s.condition, MonObj.one_comp, Hom.one_def, toUnit_unique s.snd (toUnit _)])
      ≫ fst H A) (fun s => ?_) (fun s => toUnit_unique _ _) (fun s l h1 _ => ?_)⟩⟩
  · have h1 := h.lift_fst s.fst 1
      (by rw [s.condition, MonObj.one_comp, Hom.one_def, toUnit_unique s.snd (toUnit _)])
    have h2 := h.lift_snd s.fst 1
      (by rw [s.condition, MonObj.one_comp, Hom.one_def, toUnit_unique s.snd (toUnit _)])
    rw [MonObj.comp_mul, h2, _root_.mul_one] at h1
    rw [Category.assoc, h1]
  · have h1' := h.lift_fst s.fst 1
      (by rw [s.condition, MonObj.one_comp, Hom.one_def, toUnit_unique s.snd (toUnit _)])
    have h2 := h.lift_snd s.fst 1
      (by rw [s.condition, MonObj.one_comp, Hom.one_def, toUnit_unique s.snd (toUnit _)])
    rw [MonObj.comp_mul, h2, _root_.mul_one] at h1'
    rw [← cancel_mono i, Category.assoc, h1', h1]


open GlobalTheory.TorsionKernelModel in
theorem exists_model (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A)
    (A₀ B₀ : Over (Sp K)) [GrpObj A₀] [GrpObj B₀] (φ : A₀.left ⟶ A.left) (ψ : A₀ ⟶ B₀) (n : ℕ)
    (hφ : IsGrpPullback A₀ A (spMap (algebraMap R K)) φ) (hB : IsAbelianScheme B₀) [IsMonHom ψ] [IsFinite ψ.left]
    [Flat ψ.left] [Surjective ψ.left] (hn : 1 ≤ n)
    (hker : ∀ (T : Over (Sp K)) (x : T ⟶ A₀), x ≫ ψ = 1 → x ^ n = 1) :
    ∃ (B : Over (Sp R)) (_ : GrpObj B) (φB : B₀.left ⟶ B.left), IsAbelianScheme B ∧
      IsGrpPullback B₀ B (spMap (algebraMap R K)) φB := by
  obtain ⟨_, _⟩ := ExtUnique.spec_fractionRing R K
  have := hA.proper
  have := hB.proper
  obtain ⟨a, ha, ha'⟩ := grpPullback_iso (isGrpPullback_pullback A _) hφ
  have : IsIso a.hom.left := inferInstanceAs (IsIso ((Over.forget _).map a.hom))
  obtain ⟨Z, _, i, _, hi, hZ⟩ := exists_kernel (a.hom ≫ ψ)
  obtain ⟨Ga, io, e, _, _, he⟩ := IsogenyModel.exists_flat_closure R K A Z i hi
  obtain ⟨_, _, -⟩ := exists_grpObj_of_flat_closed _ A Ga io Z i e he
  have hkill : (Over.pullback (spMap (algebraMap R K))).map io ≫ a.hom ≫ ψ = toUnit _ ≫ η[B₀] := by
    rw [← he, Category.assoc, hZ.w, comp_toUnit_assoc]
  have hpow : io ^ n = 1 := by
    apply ExtUnique.pullback_map_injective (spMap (algebraMap R K))
    have h₁ := hker _ ((Over.pullback (spMap (algebraMap R K))).map io ≫ a.hom) (by
      rw [Category.assoc, hkill, Hom.one_def])
    rw [← MonObj.pow_comp, ← MonObj.one_comp a.hom, cancel_mono] at h₁
    exact (map_pow (Over.pullback (spMap (algebraMap R K))).homMonoidHom io n).trans
      (h₁.trans (map_one (Over.pullback (spMap (algebraMap R K))).homMonoidHom).symm)
  have := (GlobalTheory.MulFiniteFlat.isFinite_and_flat_mul _ A hA n hn).1
  have hfin : IsFinite Ga.hom := isFinite_of_pow_eq_one io n hpow
  have hm : Mono io := (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono io.left))
  obtain ⟨B, _, q, hab, _, hq₁, hq₂, hq₃, hq⟩ := GlobalTheory.IwLevel.quotGlobal_holds _ A Ga io hA ‹_› hm hfin ‹_›
  have hq' := isPullback_kernel_baseChange (spMap (algebraMap R K)) (isPullback_kernel_of_kernelPair io q hq)
  have hqc : QuasiCompact q.left := inferInstance
  obtain ⟨β, _, hβ⟩ := flatQuotient_iso_of_same_kernel _ _ _ _ _ _
    ((Over.pullback (spMap (algebraMap R K))).map q) ((Over.pullback (spMap (algebraMap R K))).map io) (a.hom ≫ ψ) i
    inferInstance inferInstance
    (MorphismProperty.overPullbackMap (P := @Flat) _ q hq₂)
    (MorphismProperty.overPullbackMap (P := @Surjective) _ q hq₃)
    (MorphismProperty.overPullbackMap (P := @QuasiCompact) _ q hqc) hq' inferInstance inferInstance
    (by rw [Over.comp_left]; infer_instance) (by rw [Over.comp_left]; infer_instance)
    (by rw [Over.comp_left]; infer_instance) hZ
    (by rw [← e.inv_hom_id_assoc i, he, Category.assoc, hq'.w, comp_toUnit_assoc]) hkill
  exact ⟨B, _, β.hom.left ≫ pullback.fst B.hom (spMap (algebraMap R K)), hab,
    ((isGrpPullback_of_iso β).comp (isGrpPullback_pullback B _)).congr (Category.id_comp _) rfl⟩

theorem exists_obj {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
    (v : Sp V ⟶ Sp R) (s : Sp K ⟶ Sp R) (hs : s = spMap (algebraMap V K) ≫ v) (o : Obj b N s)
    (G : Over (Sp V)) [GrpObj G] (φ : o.A.left ⟶ G.left) (hG : IsAbelianScheme G)
    (h : IsGrpPullback o.A G (spMap (algebraMap V K)) φ) :
    ∃ o' : Obj b N v, Nonempty (ObjMap o o' (spMap (algebraMap V K))) := by
  obtain ⟨g, rfl⟩ : ∃ g : R →+* V, v = spMap g := ⟨(Spec.preimage v).hom, (Spec.map_preimage v).symm⟩
  have e : s = spMap ((algebraMap V K).comp g) := by
    rw [hs, ← Spec.map_comp]; rfl
  subst e
  exact GlobalTheory.HTObjExt.extends_obj p D R b N V K g o G φ hG h

theorem exists_isPIsog_extend_dvr : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (c : ℕ) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (v : Sp V ⟶ Sp R) (o : Obj b N v) (o₀ o₀' : Obj b N (spMap (algebraMap V (FractionRing V)) ≫ v)) (m : ObjMap o₀ o (spMap (algebraMap V (FractionRing V)))) (ψ₀ : o₀.A ⟶ o₀'.A), IsPIsog c o₀ o₀' ψ₀ → ∃ (o' : Obj b N v) (m' : ObjMap o₀' o' (spMap (algebraMap V (FractionRing V)))) (ψ : o.A ⟶ o'.A), IsPIsog c o o' ψ ∧ m.φ ≫ ψ.left = ψ₀.left ≫ m'.φ := by
  intro p _ D R _ b N hN hNp c V _ _ _ v o o₀ o₀' m ψ₀ h
  have hc := h.pos
  obtain ⟨⟨k, hk⟩, hhom, -, -, -, ψ', hhom', h1, h2⟩ := id h
  obtain ⟨hf, hfl⟩ := GlobalTheory.IsogFiniteFlat.isFinite_and_flat_of_quasiInverse _ o₀.A o₀'.A o₀.ab o₀'.ab ψ₀ ψ' c hc.ne'
    hhom hhom' h1 h2
  have hsc : Surjective (ψ'.left ≫ ψ₀.left) := by
    rw [← Over.comp_left, h2]; exact GlobalTheory.AbelianLimit.surjective_pow o₀'.A o₀'.ab c hc
  have hs : Surjective ψ₀.left := Surjective.of_comp ψ'.left ψ₀.left
  obtain ⟨B, _, φB, hB, hφB⟩ := exists_model V (FractionRing V) o.A o.ab o₀.A o₀'.A m.φ ψ₀ c m.cart o₀'.ab hc
    (fun T x hx => by
      have : x ≫ ψ₀ ≫ ψ' = 1 := by rw [← Category.assoc, hx, MonObj.one_comp]
      rwa [h1, MonObj.comp_pow, Category.comp_id] at this)
  obtain ⟨o', ⟨m'⟩⟩ := exists_obj V (FractionRing V) v _ rfl o₀' B φB hB hφB
  have hopen : IsOpenImmersion (spMap (algebraMap V (FractionRing V))) :=
    GlobalTheory.isOpenImmersion_spMap_of_isDiscreteValuationRing V (FractionRing V)
  obtain ⟨_, _⟩ := ExtUnique.spec_fractionRing V (FractionRing V)
  have hdom : IsDominant (spMap (algebraMap V (FractionRing V))) := inferInstance
  obtain ⟨ψ, hψ, hm⟩ := GlobalTheory.UPel.HT.ES.PIsogExt.exists_isPIsog_extend p D R b N hN hNp 0 c
    ⟨k, hk, fun h => absurd h (lt_irrefl 0)⟩ _ _ (spMap (algebraMap V (FractionRing V))) _ v hopen hdom inferInstance
    (fun y => (GlobalTheory.isDomain_and_isIntegrallyClosed_stalk_Sp V y).2) (fun y => inferInstance) o o' o₀ o₀' m m' ψ₀ h
  exact ⟨o', m', ψ, hψ, hm⟩

end GlobalTheory.UPel.HT.ES.IsogDVR
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChernTopPowerVolumeDensityRatio
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChernTopPowerVolumeDensityRatio
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
open GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CechPic
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ENNReal

namespace GlobalTheory.HSAmp

theorem exists_isRatio_chernInt : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → GenSmooth p D → ∀ (L : HermLB p), L.SemiPos D → ∀ (σ : k →+* ℂ) (ω : VolDens p σ D),
    ∃ ρ : CxPts p σ → ℝ, ω.IsRatio (L.φ σ) ρ ∧ (∀ y, 0 ≤ ρ y) ∧ ∀ f : CxPts p σ → ℝ, Continuous f →
      (L.φ σ).chernInt D Set.univ f = ∫ y, f y * ρ y ∂ω.meas := by
  intro k _ X _ p D hX hG L hL σ ω
  haveI : SecondCountableTopology (CxPts p σ) := CxPts.secondCountableTopology_of_isProjOver σ hX.isProjOver
  obtain ⟨R⟩ := hG σ
  have hcov : ∀ y, ∃ c : AlgChart p σ D, y ∈ c.e.source := fun y =>
    have ⟨i, hi⟩ := R.cover y
    ⟨R.chart i, hi⟩
  choose c₀ hc₀ using hcov
  let ρ : CxPts p σ → ℝ := fun y => (c₀ y).chernDens (L.φ σ) y / ω.dens (c₀ y) y
  have key : ∀ (c : AlgChart p σ D), ∀ y ∈ c.e.source, c.chernDens (L.φ σ) y = ρ y * ω.dens c y := by
    intro c y hy
    have hpos := ω.pos (c₀ y) y (hc₀ y)
    rw [c.chernDens_trans (c₀ y) (L.cInf σ) hy (hc₀ y), ω.trans c (c₀ y) y hy (hc₀ y)]
    simp only [ρ]
    field_simp
  have hρ0 : ∀ y, 0 ≤ ρ y := fun y =>
    div_nonneg ((c₀ y).chernDens_nonneg (L.cInf σ) (hL σ) (hc₀ y)) (ω.pos _ _ (hc₀ y)).le

  have hρc : Continuous ρ := by
    refine continuous_iff_continuousAt.2 fun y => ?_
    set c := c₀ y
    set i := pick (L.φ σ).isLB y
    have hyi : y ∈ ptsIn p σ (L.B.U i) := mem_pick _ y
    set O : Set (CxPts p σ) := c.e.source ∩ ptsIn p σ (L.B.U i) with hO
    have hOo : IsOpen O := c.e.open_source.inter (isOpen_ptsIn _)
    have hyO : y ∈ O := ⟨hc₀ y, hyi⟩
    set U' : Set (V D) := c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ (L.B.U i)
    have hU' : IsOpen U' := isOpen_over c.e (isOpen_ptsIn _)
    have h2 : ContDiffOn ℝ 2 (fun v => (L.φ σ).φ i (c.e.symm v)) U' :=
      (contDiffOn_chart ((L.cInf σ) i) c).of_le (by norm_cast)
    have hmap : Set.MapsTo c.e O U' := fun z hz => mem_over c.e hz.1 hz.2
    have hent : ∀ a b, ContinuousOn (fun z => c.hess (L.φ σ) i z a b) O := fun a b =>
      (continuousOn_cHess_of_contDiffOn_two D U' _ hU' h2 a b).comp (c.e.continuousOn.mono fun z hz => hz.1) hmap
    have hdet : ContinuousOn (fun z => c.chernDens (L.φ σ) z) O := by
      have hm : ContinuousOn (fun z => c.hess (L.φ σ) i z) O :=
        continuousOn_pi.2 fun a => continuousOn_pi.2 fun b => hent a b
      have hc : Continuous fun M : Matrix (Fin D) (Fin D) ℂ => (D.factorial / Real.pi ^ D : ℝ) * M.det.re :=
        continuous_const.mul (Complex.continuous_re.comp continuous_id.matrix_det)
      refine (hc.comp_continuousOn hm).congr fun z hz => ?_
      exact c.chernDens_eq (L.cInf σ) hz.1 hz.2
    have hq : ContinuousOn (fun z => c.chernDens (L.φ σ) z / ω.dens c z) O :=
      hdet.div ((ω.cont c).mono fun z hz => hz.1) fun z hz => (ω.pos c z hz.1).ne'
    refine (hq.congr fun z hz => ?_).continuousAt (hOo.mem_nhds hyO)
    rw [key c z hz.1, mul_div_cancel_right₀ _ (ω.pos c z hz.1).ne']
  have hm : Measurable fun y => ENNReal.ofReal (ρ y) := hρc.measurable.ennreal_ofReal
  have hneg : (L.φ σ).chernPart D (-1) = 0 := Weight.chernPart_neg_eq_zero (L.cInf σ) (hL σ)
  have hmeas : (L.φ σ).chernPart D 1 = ω.meas.withDensity fun y => ENNReal.ofReal (ρ y) := by
    refine ext_of_cover (fun c : AlgChart p σ D => c.e.source) (fun c => c.e.open_source)
      (fun y => ⟨c₀ y, hc₀ y⟩) fun c A hA hAc => ?_
    have hr : ω.meas.restrict A = (chartMeas c.e fun y => ENNReal.ofReal (ω.dens c y)).restrict A := by
      ext T hT
      rw [Measure.restrict_apply hT, Measure.restrict_apply hT, VolDens.meas,
        glueMeas_apply _ _ (fun a a' => a.holo_trans a') (fun a a' z hz hz' => by
          rw [ω.trans a a' z hz hz', ENNReal.ofReal_mul (sq_nonneg _)]) c (hT.inter hA)
          (Set.inter_subset_right.trans hAc)]
    have hsy : AEMeasurable c.e.symm (volume.restrict c.e.target) :=
      c.e.continuousOn_symm.aemeasurable c.e.open_target.measurableSet
    have hdm : AEMeasurable ((fun y => ENNReal.ofReal (ω.dens c y)) ∘ c.e.symm) (volume.restrict c.e.target) :=
      (ENNReal.continuous_ofReal.comp_continuousOn ((ω.cont c).comp c.e.continuousOn_symm
        fun v hv => c.e.map_target hv)).aemeasurable c.e.open_target.measurableSet
    have hI := measurableSet_image c.e hA hAc
    have hIt : c.e '' A ⊆ c.e.target := by rintro _ ⟨z, hz, rfl⟩; exact c.e.map_source (hAc hz)
    rw [Weight.chernPart_apply (L.cInf σ) 1 c hA hAc, withDensity_apply _ hA, hr, ← lintegral_indicator hA, chartMeas,
      lintegral_map' (hm.indicator hA).aemeasurable (hsy.mono_ac (withDensity_absolutelyContinuous _ _)),
      lintegral_withDensity_eq_lintegral_mul₀ hdm (g := fun v => A.indicator (fun y => ENNReal.ofReal (ρ y)) (c.e.symm v))
        ((hm.indicator hA).comp_aemeasurable hsy),
      ← Set.inter_eq_left.2 hIt, ← Measure.restrict_restrict hI, ← lintegral_indicator hI]
    refine setLIntegral_congr_fun c.e.open_target.measurableSet fun v hv => ?_
    by_cases hvA : c.e.symm v ∈ A
    · have hvI : v ∈ c.e '' A := ⟨_, hvA, c.e.right_inv hv⟩
      simp only [Set.indicator_of_mem hvI, Pi.mul_apply, Set.indicator_of_mem hvA, Function.comp_apply,
        Units.val_one, Int.cast_one, one_mul]
      rw [key c _ (hAc hvA), ENNReal.ofReal_mul (hρ0 _), mul_comm]
    · have hvI : v ∉ c.e '' A := by
        rintro ⟨z, hz, rfl⟩
        exact hvA (by rwa [c.e.left_inv (hAc hz)])
      simp only [Set.indicator_of_notMem hvI, Pi.mul_apply, Set.indicator_of_notMem hvA, mul_zero]
  refine ⟨ρ, ⟨hρc, key⟩, hρ0, fun f _ => ?_⟩
  have hn : Measurable fun y => (ρ y).toNNReal := hρc.measurable.real_toNNReal
  rw [Weight.chernInt, hneg, Measure.restrict_univ, Measure.restrict_univ, integral_zero_measure, sub_zero, hmeas]
  change ∫ y, f y ∂ω.meas.withDensity (fun y => ((ρ y).toNNReal : ℝ≥0∞)) = _
  rw [integral_withDensity_eq_integral_smul hn]
  refine integral_congr_ae (.of_forall fun y => ?_)
  simp only [NNReal.smul_def, Real.coe_toNNReal _ (hρ0 y), smul_eq_mul]
  exact mul_comm _ _

end GlobalTheory.HSAmp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChernTopPowerVolumeDensityRatioStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_chernTopPower_volumeDensity_ratio : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ (L : HermLB p), L.SemiPos D → ∀ (σ : k →+* ℂ) (ω : VolDens p σ D), ∃ ρ : CxPts p σ → ℝ, ω.IsRatio (L.φ σ) ρ ∧ (∀ y, 0 ≤ ρ y) ∧ ∀ f : CxPts p σ → ℝ, Continuous f → (L.φ σ).chernInt D Set.univ f = ∫ y, f y * ρ y ∂ω.meas := by
  first | exact @GlobalTheory.HSAmp.exists_isRatio_chernInt | exact GlobalTheory.HSAmp.exists_isRatio_chernInt | (intros; apply GlobalTheory.HSAmp.exists_isRatio_chernInt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPullbacksMatchTorsionPairs
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointSiegelFibreEqLevelSection
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointSiegelFibreEqLevelSection
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

namespace GlobalTheory.TInj

theorem torsion_isLev : ∀ {X : Scheme.{0}} {g n : ℕ} {B : Type} [CommRing B] {ζ : B} {sX : X ⟶ Sp B} (c : SiegPre g n ζ sX), IsUnit ζ → ∀ {S : Scheme.{0}} (A : Over S) [GrpObj A] (y : S ⟶ X) (α : A.left ⟶ c.A.left), IsGrpPullback A c.A y α → ∀ (F : Type) [Field F] [IsAlgClosed F] (t : Sp F ⟶ S) (x : Over.mk t ⟶ A), x ^ n = 1 → ∃ l, x.left ≫ α = t ≫ y ≫ (c.lev l).left := by
  intro X g n B _ ζ sX c hζ S A _ y α hα F _ _ t x hx
  let β : B →+* F := (Spec.preimage ((t ≫ y) ≫ sX)).hom
  obtain ⟨-, hs, -⟩ := c.geom F (t ≫ y) β (hζ.map β).unit (Spec.map_preimage _).symm rfl
  have hx₁ : pushHom hα (Over.mk t) x ^ n = 1 := by rw [← map_pow, hx, map_one]
  obtain ⟨a, ha⟩ := hs _ hx₁
  have hu : (toUnit (Over.mk (t ≫ y))).left = t ≫ y := (Category.comp_id _).symm.trans (Over.w (toUnit _))
  have e : (t ≫ y) ≫ (c.lev a).left = x.left ≫ α := by
    rw [← hu]
    exact congrArg (fun q => q.left) ha
  exact ⟨a, by rw [← e, Category.assoc]⟩

end GlobalTheory.TInj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointSiegelFibreEqLevelSectionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionPoint_siegelFibre_eq_levelSection : ∀ {X : Scheme.{0}} {g n : ℕ} {B : Type} [CommRing B] {ζ : B} {sX : X ⟶ Sp B} (c : SiegPre g n ζ sX), IsUnit ζ → ∀ {S : Scheme.{0}} (A : Over S) [GrpObj A] (y : S ⟶ X) (α : A.left ⟶ c.A.left), IsGrpPullback A c.A y α → ∀ (F : Type) [Field F] [IsAlgClosed F] (t : Sp F ⟶ S) (x : Over.mk t ⟶ A), x ^ n = 1 → ∃ l, x.left ≫ α = t ≫ y ≫ (c.lev l).left := by
  first | exact @GlobalTheory.TInj.torsion_isLev | exact GlobalTheory.TInj.torsion_isLev | (intros; apply GlobalTheory.TInj.torsion_isLev <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPullbacksMatchTorsionPairs
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

namespace GlobalTheory.TInj.Pair

theorem exists_ext {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (f : R →+* V)
    (hf : Function.Injective f) :
    ∃ j : AlgebraicClosure (FractionRing R) →+* AlgebraicClosure (FractionRing V), Ext f j := by
  let g : R →+* AlgebraicClosure (FractionRing V) :=
    (algebraMap (FractionRing V) _).comp ((algebraMap V (FractionRing V)).comp f)
  have hg : Function.Injective g :=
    (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).injective.comp
      ((IsFractionRing.injective V (FractionRing V)).comp hf)
  letI : Algebra (FractionRing R) (AlgebraicClosure (FractionRing V)) := (IsFractionRing.lift hg).toAlgebra
  refine ⟨(IsAlgClosed.lift : AlgebraicClosure (FractionRing R) →ₐ[FractionRing R]
    AlgebraicClosure (FractionRing V)).toRingHom, fun r => ?_⟩
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes, RingHom.algebraMap_toAlgebra,
    IsFractionRing.lift_algebraMap]
  rfl

theorem sq {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (f : R →+* V)
    {F₀ F : Type} [Field F₀] [Algebra (FractionRing R) F₀] [Field F] [Algebra (FractionRing V) F]
    (j : F₀ →+* F) (hj : Ext f j) (κ : Sp (FractionRing V) ⟶ Sp (FractionRing R))
    (hκ : κ ≫ jK R = jK V ≫ spMap f) :
    spMap j ≫ jFK (R := R) F₀ = jFK (R := V) F ≫ κ := by
  haveI : Mono (jK R) :=
    haveI := IsPreimmersion.of_isLocalization (R := CommRingCat.of R) (S := CommRingCat.of (FractionRing R))
      (nonZeroDivisors R)
    inferInstanceAs (Mono (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))
  rw [← cancel_mono (jK R), Category.assoc, Category.assoc, hκ]
  simp only [jFK, jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext r
  exact hj r

end GlobalTheory.TInj.Pair

theorem GlobalTheory.TInj.pull_pair_match : ∀ {X : Scheme.{0}} {g n : ℕ} {B : Type} [CommRing B] {ζ : B} {sX : X ⟶ Sp B} (c : SiegPre g n ζ sX), IsUnit ζ → 1 ≤ n → ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (J : Ideal R), AdmBase R J → ∀ (D₀ : DegData R J) (A₀ : PolAV (Sp (FractionRing R))) (G₀ : Over (Sp R)) [GrpObj G₀] [IsCommMonObj G₀] (U₀ : Unif J D₀ A₀ G₀), IsSemiAbelian G₀ → ∀ (y₀ : Sp (FractionRing R) ⟶ X) (α₀ : A₀.A.left ⟶ c.A.left), OverPt c A₀ y₀ α₀ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ f₁ f₂ : R →+* V, Function.Injective f₁ → Function.Injective f₂ → J.map f₁ ≤ maximalIdeal V → J.map f₂ ≤ maximalIdeal V → ∀ κ₁ κ₂ : Sp (FractionRing V) ⟶ Sp (FractionRing R), κ₁ ≫ jK R = jK V ≫ spMap f₁ → κ₂ ≫ jK R = jK V ≫ spMap f₂ → κ₁ ≫ y₀ = κ₂ ≫ y₀ → ∃ (D₁ D₂ : DegData V (maximalIdeal V)) (hD₁ : IsPullDeg f₁ D₀.toPre D₁.toPre) (hD₂ : IsPullDeg f₂ D₀.toPre D₂.toPre) (j₁ j₂ : (AlgebraicClosure (FractionRing R)) →+* (AlgebraicClosure (FractionRing V))) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (φ : D₁.toPre.X ≃+ D₂.toPre.X), Ext f₁ j₁ ∧ Ext f₂ j₂ ∧ Match D₁.toPre D₂.toPre b φ (AlgebraicClosure (FractionRing V)) ∧ (∀ p₀ : QkPt D₀.toPre (AlgebraicClosure (FractionRing R)) n, ∃ (p₁ : QkPt D₁.toPre (AlgebraicClosure (FractionRing V)) n) (p₂ : QkPt D₂.toPre (AlgebraicClosure (FractionRing V)) n), p₁.y = hD₁.xe.symm p₀.y ∧ Tr f₁ hD₁ j₁ p₀.g p₁.g ∧ p₂.y = hD₂.xe.symm p₀.y ∧ Tr f₂ hD₂ j₂ p₀.g p₂.g ∧ QImg b φ p₁ p₂) := by
  intro X g n B _ ζ sX c hζ hn R _ _ _ J hJ D₀ A₀ G₀ _ _ U₀ hG₀ y₀ α₀ hO V _ _ _ _ hV f₁ f₂ hf₁ hf₂ hJ₁ hJ₂
    κ₁ κ₂ hκ₁ hκ₂ hy
  obtain ⟨D₁, hD₁, A₁, U₁, hG₁, hU₁, tr₁⟩ := GlobalTheory.T.uniformisation_pullback_dvr_torsionPoints R J hJ D₀ A₀ G₀ U₀ hG₀ V hV f₁ hf₁ hJ₁
  obtain ⟨D₂, hD₂, A₂, U₂, hG₂, hU₂, tr₂⟩ := GlobalTheory.T.uniformisation_pullback_dvr_torsionPoints R J hJ D₀ A₀ G₀ U₀ hG₀ V hV f₂ hf₂ hJ₂
  obtain ⟨α₁, hO₁, hα₁⟩ := GlobalTheory.T.uniformisation_genericFibre_eq_siegelFibre_pullback c R V J (maximalIdeal V) D₀ A₀ G₀ U₀ f₁ D₁ hD₁ A₁ U₁ hU₁ y₀ α₀ hO κ₁ hκ₁
  obtain ⟨α₂, hO₂, hα₂⟩ := GlobalTheory.T.uniformisation_genericFibre_eq_siegelFibre_pullback c R V J (maximalIdeal V) D₀ A₀ G₀ U₀ f₂ D₂ hD₂ A₂ U₂ hU₂ y₀ α₀ hO κ₂ hκ₂
  rw [← hy] at hO₂
  obtain ⟨b, φ, hM, hQ⟩ := GlobalTheory.T.two_trait_uniformisations_matching_data c V hV D₁ A₁ _ U₁ D₂ A₂ _ U₂ hG₁ hG₂ (κ₁ ≫ y₀) α₁ α₂ hO₁ hO₂
  obtain ⟨j₁, hj₁⟩ := GlobalTheory.TInj.Pair.exists_ext f₁ hf₁
  obtain ⟨j₂, hj₂⟩ := GlobalTheory.TInj.Pair.exists_ext f₂ hf₂
  refine ⟨D₁, D₂, hD₁, hD₂, j₁, j₂, b, φ, hj₁, hj₂, hM, fun p₀ => ?_⟩
  obtain ⟨x₀, hx₀, hpow⟩ := (GlobalTheory.T.torsionPointOfPair_exists_torsion_injective_upToEquiv R J hJ D₀ A₀ G₀ U₀ hG₀ (AlgebraicClosure (FractionRing R)) n hn).1 p₀
  obtain ⟨l, hl⟩ := GlobalTheory.T.torsionPoint_siegelFibre_eq_levelSection c hζ A₀.A y₀ α₀ hO.1 (AlgebraicClosure (FractionRing R))
    (jFK (R := R) (AlgebraicClosure (FractionRing R))) x₀ hpow
  obtain ⟨p₁, x₁, hy₁, hT₁, hq₁, hc₁⟩ := tr₁ (AlgebraicClosure (FractionRing R)) (AlgebraicClosure (FractionRing V))
    j₁ hj₁ n hn p₀ x₀ hx₀
  obtain ⟨p₂, x₂, hy₂, hT₂, hq₂, hc₂⟩ := tr₂ (AlgebraicClosure (FractionRing R)) (AlgebraicClosure (FractionRing V))
    j₂ hj₂ n hn p₀ x₀ hx₀
  have e₁ := hα₁ _ x₁.left (spMap j₁ ≫ x₀.left) (hc₁.trans (Category.assoc _ _ _).symm)
  have e₂ := hα₂ _ x₂.left (spMap j₂ ≫ x₀.left) (hc₂.trans (Category.assoc _ _ _).symm)
  have s₁ := GlobalTheory.TInj.Pair.sq f₁ j₁ hj₁ κ₁ hκ₁
  have s₂ := GlobalTheory.TInj.Pair.sq f₂ j₂ hj₂ κ₂ hκ₂
  have key : x₁.left ≫ α₁ = x₂.left ≫ α₂ := by
    rw [e₁, e₂, Category.assoc, Category.assoc, hl, ← Category.assoc, ← Category.assoc (spMap j₂), s₁, s₂,
      Category.assoc, Category.assoc, ← Category.assoc κ₁, ← Category.assoc κ₂, hy]
  exact ⟨p₁, p₂, hy₁, hT₁, hy₂, hT₂, hQ n hn p₁ p₂ x₁ x₂ hq₁ hq₂ key⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPullbacksMatchTorsionPairsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisation_pullbacks_match_torsionPairs : ∀ {X : Scheme.{0}} {g n : ℕ} {B : Type} [CommRing B] {ζ : B} {sX : X ⟶ Sp B} (c : SiegPre g n ζ sX), IsUnit ζ → 1 ≤ n → ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (J : Ideal R), AdmBase R J → ∀ (D₀ : DegData R J) (A₀ : PolAV (Sp (FractionRing R))) (G₀ : Over (Sp R)) [GrpObj G₀] [IsCommMonObj G₀] (U₀ : Unif J D₀ A₀ G₀), IsSemiAbelian G₀ → ∀ (y₀ : Sp (FractionRing R) ⟶ X) (α₀ : A₀.A.left ⟶ c.A.left), OverPt c A₀ y₀ α₀ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ f₁ f₂ : R →+* V, Function.Injective f₁ → Function.Injective f₂ → J.map f₁ ≤ maximalIdeal V → J.map f₂ ≤ maximalIdeal V → ∀ κ₁ κ₂ : Sp (FractionRing V) ⟶ Sp (FractionRing R), κ₁ ≫ jK R = jK V ≫ spMap f₁ → κ₂ ≫ jK R = jK V ≫ spMap f₂ → κ₁ ≫ y₀ = κ₂ ≫ y₀ → ∃ (D₁ D₂ : DegData V (maximalIdeal V)) (hD₁ : IsPullDeg f₁ D₀.toPre D₁.toPre) (hD₂ : IsPullDeg f₂ D₀.toPre D₂.toPre) (j₁ j₂ : (AlgebraicClosure (FractionRing R)) →+* (AlgebraicClosure (FractionRing V))) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (φ : D₁.toPre.X ≃+ D₂.toPre.X), Ext f₁ j₁ ∧ Ext f₂ j₂ ∧ Match D₁.toPre D₂.toPre b φ (AlgebraicClosure (FractionRing V)) ∧ (∀ p₀ : QkPt D₀.toPre (AlgebraicClosure (FractionRing R)) n, ∃ (p₁ : QkPt D₁.toPre (AlgebraicClosure (FractionRing V)) n) (p₂ : QkPt D₂.toPre (AlgebraicClosure (FractionRing V)) n), p₁.y = hD₁.xe.symm p₀.y ∧ Tr f₁ hD₁ j₁ p₀.g p₁.g ∧ p₂.y = hD₂.xe.symm p₀.y ∧ Tr f₂ hD₂ j₂ p₀.g p₂.g ∧ QImg b φ p₁ p₂) := by
  first | exact @GlobalTheory.TInj.pull_pair_match | exact GlobalTheory.TInj.pull_pair_match | (intros; apply GlobalTheory.TInj.pull_pair_match <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsCohomologyBijective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicAndBlockOneNondegenerate
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.EtC.GmAicDeg1

theorem cast_eq_zero_iff {q : ℕ} {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E n i) :
    x.cast hn hi = 0 ↔ x = 0 := by
  subst hn; subst hi; exact Iff.rfl

theorem cast_nsmul {q : ℕ} {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (k : ℕ) (x : Ht q E n i) :
    (k • x).cast hn hi = k • x.cast hn hi := by
  subst hn; subst hi; rfl

theorem inv_sp (q : ℕ) (A : Type) [CommRing A] (hq : IsUnit (q : A)) : Inv q (sp A) := fun U ⟨x⟩ => by
  have h := (hq.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom).map
    (show U ⟶ Spec (CommRingCat.of A) from x).appTop.hom
  simpa only [map_natCast] using h

theorem dvd_of_T_eq_pow {T : Type} [CommRing T] [IsDomain T] (q n : ℕ) (w : LaurentPolynomial T)
    (hw : (LaurentPolynomial.T (n : ℤ) : LaurentPolynomial T) = w ^ q) : q ∣ n := by
  obtain ⟨k, f, hf⟩ := LaurentPolynomial.exists_T_pow w
  have h : Polynomial.toLaurent (f ^ q) = Polynomial.toLaurent (Polynomial.X ^ (n + k * q) : Polynomial T) := by
    rw [map_pow, hf, mul_pow, ← hw, Polynomial.toLaurent_X_pow, LaurentPolynomial.T_pow, ← LaurentPolynomial.T_add]
    congr 1
    push_cast
    ring
  have h2 := congrArg Polynomial.natDegree (Polynomial.toLaurent_injective h)
  rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_pow] at h2
  have h3 : q ∣ n + k * q := ⟨f.natDegree, h2.symm⟩
  exact (Nat.dvd_add_left (dvd_mul_left q k)).mp h3

theorem kum_pow (q : ℕ) [NeZero q] {X : Scheme.{0}} (hX : IsUnit (q : Γ(X, ⊤))) (u : (Γ(X, ⊤))ˣ) (m : ℕ) :
    kum q (u ^ m) = m • kum q u := by
  have hadd : ∀ u v : (Γ(X, ⊤))ˣ, IsUnit (q : Γ(X, ⊤)) → kum q (u * v) = kum q u + kum q v ∧ kum q (u ^ q) = 0 :=
    fun u v h => (GlobalTheory.T.chernClass_kummerClass_additive q).2 u v h
  have h1 : kum q (1 : (Γ(X, ⊤))ˣ) = 0 := by
    have h := (hadd 1 1 hX).1
    rw [mul_one] at h
    simpa using h
  induction m with
  | zero => rw [pow_zero, zero_smul, h1]
  | succ m ih => rw [pow_succ, (hadd _ _ hX).1, ih, succ_nsmul]

theorem laurentVar_val (T : Type) [CommRing T] :
    (Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial T))).hom.hom ((laurentVar T : Γ(Spec (CommRingCat.of (LaurentPolynomial T)), ⊤))) =
      LaurentPolynomial.T 1 := by
  simp [laurentVar, laurentVarUnit]

end GlobalTheory.EtC.GmAicDeg1

namespace GlobalTheory.EtC.GmAicDeg1

theorem eq_zero_of_cup_kum (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T] (hT : AIC T)
    (hq : IsUnit (q : T)) (b : Ht q (sp T) 0 0)
    (hb : cup q (pull _ (spMap (LaurentPolynomial.C : T →+* LaurentPolynomial T)) (tw q 0) 0 b) (kum q (laurentVar T)) = 0) :
    b = 0 := by
  obtain ⟨e⟩ := GlobalTheory.T.nonempty_ht_zero_addEquiv_zmod_of_sh q T (GlobalTheory.GenusTwoPureComparison.Cmp.sh_of_aic hT) hq 0
  have hrep : ∀ x : Ht q (sp T) 0 0, x = (e x).val • e.symm 1 := fun x => by
    apply e.injective
    rw [map_nsmul, AddEquiv.apply_symm_apply, nsmul_one, ZMod.natCast_zmod_val]
  have hqL : IsUnit (q : LaurentPolynomial T) := by simpa using hq.map (LaurentPolynomial.C : T →+* LaurentPolynomial T)
  have hqΓ := GmPhiNat.isUnit_gamma q T hq
  have hκ : ∀ (m : ℕ) (x : Ht q (sp T) 0 0),
      cup q (pull _ (spMap (LaurentPolynomial.C : T →+* LaurentPolynomial T)) (tw q 0) 0 (m • x)) (kum q (laurentVar T)) =
        m • cup q (pull _ (spMap (LaurentPolynomial.C : T →+* LaurentPolynomial T)) (tw q 0) 0 x) (kum q (laurentVar T)) := by
    intro m x
    rw [map_nsmul, map_nsmul, AddMonoidHom.nsmul_apply]
  have hone : pull _ (spMap (LaurentPolynomial.C : T →+* LaurentPolynomial T)) (tw q 0) 0 (one q (sp T)) =
      one q (sp (LaurentPolynomial T)) := (GlobalTheory.T.cup_chern_kummer_pullback_naturality q).2.1 _ (inv_sp q T hq)
  have hunit := (GlobalTheory.T.cupProduct_gradedCommRingAxioms_hold q (sp (LaurentPolynomial T))).1 (inv_sp q _ hqL) (kum q (laurentVar T))
  have h1 := hκ (e (one q (sp T))).val (e.symm 1)
  rw [← hrep, hone, hunit] at h1
  have h2 := hκ (e b).val (e.symm 1)
  rw [← hrep, hb] at h2
  have h3 : (e b).val • (kum q (laurentVar T)).cast (by ring) (by ring) = (0 : Ht q (sp (LaurentPolynomial T)) (0 + 1) (0 + 1)) := by
    rw [h1, smul_smul, mul_comm, ← smul_smul, ← h2, smul_zero]
  rw [← cast_nsmul, cast_eq_zero_iff] at h3
  have h5 : kum q (laurentVar T ^ (e b).val) = 0 := by rw [kum_pow q hqΓ, h3]
  obtain ⟨v, hv⟩ := GlobalTheory.T.eq_pow_of_kummerClassOfUnit_eq_zero q (LaurentPolynomial T) hqL _ h5
  have h6 := congrArg (fun u : (Γ(Spec (CommRingCat.of (LaurentPolynomial T)), ⊤))ˣ =>
    (Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial T))).hom.hom (u : Γ(Spec (CommRingCat.of (LaurentPolynomial T)), ⊤))) hv
  simp only [Units.val_pow_eq_pow_val, map_pow] at h6
  rw [laurentVar_val, LaurentPolynomial.T_pow, mul_one] at h6
  have h7 := dvd_of_T_eq_pow q (e b).val _ h6
  have h8 : (e b).val = 0 := Nat.eq_zero_of_dvd_of_lt h7 (ZMod.val_lt _)
  rw [ZMod.val_eq_zero] at h8
  exact e.map_eq_zero_iff.1 h8

theorem main : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) →
    ∀ i : ℤ, Function.Bijective (gmPhi q T i) := by
  intro q _ T _ _ _ hT hq i
  have hinj : Function.Injective (gmPhi q T i) := by
    refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
    simp only [gmPhi, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at ha
    rw [cast_eq_zero_iff] at ha
    obtain ⟨z, hz⟩ : ∃ z : T, Polynomial.aeval z (Polynomial.cyclotomic q ℤ) = 0 := by
      obtain ⟨a, ha⟩ := hT (Polynomial.cyclotomic q T) (Polynomial.cyclotomic.monic q T)
        (by rw [Polynomial.natDegree_cyclotomic]; exact Nat.totient_pos.2 (NeZero.pos q))
      exact ⟨a, by rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]; exact ha⟩
    let ζ : Prim q Γ(Spec (CommRingCat.of T), ⊤) := Prim.map (Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom ⟨z, hq, hz⟩
    let τ := Untwist.twistEquiv ζ (inv_sp q T hq) 0 (i - 1) 0
    have hτ : τ a = 0 := by
      apply eq_zero_of_cup_kum q T hT hq
      show cup q (pull _ _ _ 0 ((cup q (rootClass (0 - (i - 1)) ζ) a).cast (zero_add 0) (by ring))) (kum q (laurentVar T)) = 0
      rw [GmPhiNat.pull_cast, Untwist.cup_cast_left, cast_eq_zero_iff, (GlobalTheory.T.cup_chern_kummer_pullback_naturality q).1,
        (GlobalTheory.T.cupProduct_gradedCommRingAxioms_hold q _).2.1, cast_eq_zero_iff, ha, map_zero]
    exact τ.map_eq_zero_iff.1 hτ
  obtain ⟨e0⟩ := GlobalTheory.T.nonempty_ht_zero_addEquiv_zmod_of_sh q T (GlobalTheory.GenusTwoPureComparison.Cmp.sh_of_aic hT) hq (i - 1)
  obtain ⟨e1⟩ := (GlobalTheory.T.tateTwistCohomology_laurent_absIntClosedLocalDomain q T hT hq 1 i).2
  haveI : Finite (Ht q (sp (LaurentPolynomial T)) 1 i) := Finite.of_equiv _ e1.symm.toEquiv
  exact hinj.bijective_of_nat_card_le (by rw [Nat.card_congr e0.toEquiv, Nat.card_congr e1.toEquiv])

end GlobalTheory.EtC.GmAicDeg1

theorem GlobalTheory.EtC.gmPhi_bijective_of_aic : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T],
    AIC T → IsUnit (q : T) → ∀ i : ℤ, Function.Bijective (gmPhi q T i) :=
  GlobalTheory.EtC.GmAicDeg1.main
end
end

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.units_cohomology_bijective : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) → ∀ i : ℤ, Function.Bijective (gmPhi q T i) := by
  first | (exact @GlobalTheory.EtC.gmPhi_bijective_of_aic) | (exact GlobalTheory.EtC.gmPhi_bijective_of_aic) | (intros; apply GlobalTheory.EtC.gmPhi_bijective_of_aic  <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCellCoordinatesContDiffAtEtaleChart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCellCoordinatesContDiffAtEtaleChart
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.FlagCell2

open GlobalTheory.Points GlobalTheory.ChartGlue

theorem contDiffAt_chart_of_eqOn_ev {F : Type} [Field F] {Y : Var F} {σ : F →+* ℂ} {D : ℕ} (c' : AlgChart Y.str σ D)
    {g : CxPts Y.str σ → ℂ} {S : Set (CxPts Y.str σ)} (hS : IsOpen S) {W : Y.X.Opens} (a : Γ(Y.X, W))
    (hg : ∀ z ∈ S, g z = ev Y.str σ W a z) {y : CxPts Y.str σ} (hy : y ∈ c'.e.source) (hyS : y ∈ S)
    (hyW : y ∈ ptsIn Y.str σ W) : ContDiffAt ℂ 2 (g ∘ c'.e.symm) (c'.e y) := by
  have hO := isOpen_over c'.e (hS.inter (isOpen_ptsIn (p := Y.str) (σ := σ) W))
  have hm := mem_over c'.e (S := S ∩ ptsIn Y.str σ W) hy ⟨hyS, hyW⟩
  have hd : DifferentiableOn ℂ (ev Y.str σ W a ∘ c'.e.symm) (c'.e.target ∩ c'.e.symm ⁻¹' (S ∩ ptsIn Y.str σ W)) :=
    (c'.holo W a).mono fun v hv => ⟨hv.1, hv.2.2⟩
  have h1 : ContDiffAt ℂ 2 (ev Y.str σ W a ∘ c'.e.symm) (c'.e y) := ((ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn D _ _ hO hd).contDiffAt (hO.mem_nhds hm)).of_le
    (by norm_cast)
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [hO.mem_nhds hm] with v hv
  exact hg _ hv.2.1

theorem cellMap_contDiffAt : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → ∀ (c : AlgChart X.str σ X.dim) (A : Mat m X.Fn) (u : Cell m → Y.Fn), ∀ (n : ℕ) (ε : Fin n ≃ Fin X.dim ⊕ Cell m) (x : (atlas Y σ).Pt), x.pt ∈ cellSet E E' φ f hf c A u → ContDiffAt ℂ 2 (cellMap ε f hf c u ∘ x.ch.symm) x.crd := by
  intro F _ σ X Y ι _ m E E' φ f hf hR c A u n ε x hx
  obtain ⟨hcell, hsrc⟩ := hx
  have hreg := (isOpen_inCell_and_regAt F X Y ι m E E' φ f hR A u).2 _ hcell
  set c' : AlgChart Y.str σ Y.dim := x.1.1
  have hy : x.pt ∈ c'.e.source := x.2
  change ContDiffAt ℂ 2 (cellMap ε f hf c u ∘ c'.e.symm) (c'.e x.pt)
  refine contDiffAt_euclidean.2 fun a => ?_
  change ContDiffAt ℂ 2 ((fun z => cellMap ε f hf c u z a) ∘ c'.e.symm) (c'.e x.pt)
  rcases hε : ε a with b | j
  · have hS : IsOpen (ptMap σ f hf ⁻¹' c.e.source) :=
      c.e.open_source.preimage (PtsOver.continuous_map f hf _)
    refine contDiffAt_chart_of_eqOn_ev c' hS (f.app c.U (c.x b)) (fun z hz => ?_) hy hsrc ?_
    · simp only [cellMap, pt, hε, Sum.elim_inl]
      rw [c.apply_eq _ hz b, ev_app f hf]
      rfl
    · rw [mem_ptsIn]
      exact mem_ptsIn.1 (c.source_subset hsrc)
  · obtain ⟨U, hU, w, hw⟩ := (hreg j).exists_fnOf
    refine contDiffAt_chart_of_eqOn_ev c' (isOpen_ptsIn U) w (fun z hz => ?_) hy (mem_ptsIn.2 hU) (mem_ptsIn.2 hU)
    simp only [cellMap, pt, hε, Sum.elim_inr]
    rw [← hw, ratVal_fnOf hz]

end GlobalTheory.FlagCell2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCellCoordinatesContDiffAtEtaleChartStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagCellCoordinates_contDiffAt_etaleChart : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → ∀ (c : AlgChart X.str σ X.dim) (A : Mat m X.Fn) (u : Cell m → Y.Fn), ∀ (n : ℕ) (ε : Fin n ≃ Fin X.dim ⊕ Cell m) (x : (atlas Y σ).Pt), x.pt ∈ cellSet E E' φ f hf c A u → ContDiffAt ℂ 2 (cellMap ε f hf c u ∘ x.ch.symm) x.crd := by
  first | exact @GlobalTheory.FlagCell2.cellMap_contDiffAt | exact GlobalTheory.FlagCell2.cellMap_contDiffAt | (intros; apply GlobalTheory.FlagCell2.cellMap_contDiffAt <;> assumption)
end
end
