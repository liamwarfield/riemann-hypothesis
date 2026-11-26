module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableQuadraticGaussIntegralTransformWeil
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuadraticWeilFourierPreservesTestAdditive
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterPadicBasicProperties

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableQuadraticGaussNegOneEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableQuadraticGaussNegOneEqOne
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.WeilQuad

theorem absK_units_neg_one {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] (A : Et F E) : A.absK ((-1 : A.Kˣ) : A.K) = 1 := by
  have hu : IsUnit ((-1 : A.Kˣ) : A.K) := Units.isUnit _
  have he : hu.unit = -1 := Units.ext rfl
  unfold Et.absK
  rw [dite_eq_left hu, he]
  have h2 : (distribHaarChar A.K (-1 : A.Kˣ)) ^ 2 = 1 := by
    rw [← map_pow]; simp
  have h3 : distribHaarChar A.K (-1 : A.Kˣ) = 1 :=
    (pow_eq_one_iff_of_nonneg zero_le two_ne_zero).1 h2
  rw [h3]; simp

theorem stableGauss_neg_one : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ)
    (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ G₁ : ℂ, IsStableGauss A ψ x μ 1 G₁ →
    IsStableGauss A ψ x μ (-1) G₁ := by
  intro F E _ _ _ _ _ A ψ x μ ω h G₁ h1
  obtain ⟨G, hG⟩ := GlobalTheory.T.exists_stable_quadraticGaussIntegral F E A ψ x μ ω h (-1)
  have hω := (GlobalTheory.T.normGroupSign_mul_and_neg_one F E A ψ x μ ω h).2
  have h1' : IsStableGauss A ψ x μ ((1 : A.Kˣ) : A.K) G₁ := by simpa using h1
  have key := GlobalTheory.T.stableQuadraticGaussIntegral_transform_weil F E A ψ x μ ω h (-1) G G₁ hG h1'
  rw [hω, absK_units_neg_one] at key
  simp at key
  subst key
  simpa using hG

end GlobalTheory.JR.WeilQuad
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableQuadraticGaussNegOneEqOneStatement
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stableQuadraticGauss_neg_one_eq_one : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ G₁ : ℂ, IsStableGauss A ψ x μ 1 G₁ → IsStableGauss A ψ x μ (-1) G₁ := by
  first | exact @GlobalTheory.JR.WeilQuad.stableGauss_neg_one | exact GlobalTheory.JR.WeilQuad.stableGauss_neg_one | (intros; apply GlobalTheory.JR.WeilQuad.stableGauss_neg_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussIntegralOneMulGaussIntegralNegOneEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussIntegralOneMulGaussIntegralNegOneEqOne
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.WeilQuad.GaussProd

open GlobalTheory.JR.WeilQuad.FourierTest

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem NL_add [Unram F E] (A : Et F E) (hK : IsField A.K) (hL : IsField A.L) (t u : A.L) :
    A.NL (t + u) = A.NL t + A.NL u + Algebra.trace A.K A.L (star t * u) := by
  apply algMap_inj A hK hL
  rw [map_add (f := _), map_add (f := _), (GlobalTheory.T.etaleHermitianPair_structure_facts F E A).1, (GlobalTheory.T.etaleHermitianPair_structure_facts F E A).1, (GlobalTheory.T.etaleHermitianPair_structure_facts F E A).1,
    (GlobalTheory.T.etaleHermitianPair_structure_facts F E A).2.1, star_add, star_mul, star_star]
  ring

theorem two_trace_NL [Unram F E] (A : Et F E) (hK : IsField A.K) (hL : IsField A.L) (x : A.K) (y : A.L) :
    2 * Algebra.trace F A.K (x * A.NL y) = beta A x y y := by
  rw [beta_apply]
  have h : Algebra.trace A.K A.L (star y * y) = A.NL y + A.NL y := by
    apply algMap_inj A hK hL
    rw [(GlobalTheory.T.etaleHermitianPair_structure_facts F E A).2.1, map_add (f := _), (GlobalTheory.T.etaleHermitianPair_structure_facts F E A).1, star_mul, star_star]
    ring
  rw [h, mul_add, map_add (f := _), two_mul]

theorem trace_NL_add [Unram F E] (A : Et F E) (hK : IsField A.K) (hL : IsField A.L) (x : A.K) (t u : A.L) :
    Algebra.trace F A.K (x * A.NL (t + u)) =
      Algebra.trace F A.K (x * A.NL t) + Algebra.trace F A.K (x * A.NL u) + beta A x t u := by
  rw [NL_add A hK hL, mul_add, mul_add, map_add (f := _), map_add (f := _), beta_apply]

theorem continuous_trace_NL [Unram F E] (A : Et F E) (hK : IsField A.K) (hL : IsField A.L) (x : A.K) :
    Continuous fun y : A.L => Algebra.trace F A.K (x * A.NL y) := by
  haveI := finite_F_L A
  haveI : CharZero F := Unram.charZero (F := F) (E := E)
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  have hβc : Continuous (fun p : A.L × A.L => beta A x p.1 p.2) :=
    IsModuleTopology.continuous_bilinear_of_finite_left (beta A x)
  have hdiag : Continuous (fun y : A.L => (y, y)) := continuous_id.prodMk continuous_id
  have hcomp : Continuous ((fun p : A.L × A.L => beta A x p.1 p.2) ∘ (fun y : A.L => (y, y))) :=
    hβc.comp hdiag
  have hd : Continuous (fun y : A.L => (2 : F)⁻¹ * beta A x y y) := continuous_const.mul hcomp
  refine hd.congr (fun y => ?_)
  show (2 : F)⁻¹ * beta A x y y = Algebra.trace F A.K (x * A.NL y)
  rw [← two_trace_NL A hK hL x y, ← mul_assoc, inv_mul_cancel₀ h2, one_mul]

end GlobalTheory.JR.WeilQuad.GaussProd


open GlobalTheory.JR.WeilQuad.FourierTest GlobalTheory.JR.WeilQuad.GaussProd in
theorem GlobalTheory.JR.WeilQuad.gaussInt_one_mul_neg_one : ∀ (F E : Type) [NontriviallyNormedField F]
    [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ)
    (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ Λ : AddSubgroup A.L, IsOpen (Λ : Set A.L) →
    IsCompact (Λ : Set A.L) → {y : A.L | ∀ w ∈ (Λ : Set A.L), A.kerL ψ x w y = 1} ⊆ Λ →
    (∀ y ∈ {y : A.L | ∀ w ∈ (Λ : Set A.L), A.kerL ψ x w y = 1}, A.psiK ψ ((x : A.K) * A.NL y) = 1) →
    gaussInt A ψ x μ 1 Λ * gaussInt A ψ x μ (-1) Λ = 1 := by
  intro F E _ _ _ _ _ A ψ x μ ω h Λ hΛo hΛc hPS hQ
  obtain ⟨hK, hL, hψ, hsd, -⟩ := h
  haveI := hsd.1
  haveI := finite_F_L A
  obtain ⟨hLC, hSC, hT2, hTG⟩ := GlobalTheory.JR.SelfDualLat.topo F E A.L
  haveI := hLC; haveI := hSC; haveI := hT2; haveI := hTG
  have hψ' := (GlobalTheory.T.unramifiedStandardAddChar_conductor_properties F E).2 ψ hψ
  have hψc : Continuous (fun t : F => ψ t) := cont_psi hψ
  set β := beta A (x : A.K) with hβdef
  have hβc : Continuous (fun p : A.L × A.L => β p.1 p.2) :=
    IsModuleTopology.continuous_bilinear_of_finite_left β
  set q : A.L → F := fun y => Algebra.trace F A.K ((x : A.K) * A.NL y) with hqdef
  have hqc : Continuous q := continuous_trace_NL A hK hL (x : A.K)
  have hqa : ∀ t u, q (t + u) = q t + q u + β t u := fun t u => trace_NL_add A hK hL (x : A.K) t u
  set S : Set A.L := (Λ : Set A.L) with hSdef
  set P : Set A.L := {y : A.L | ∀ w ∈ S, ψ (β w y) = 1} with hPdef
  have hSm : MeasurableSet S := hΛo.measurableSet
  have hPc : IsClosed P := by
    have : P = ⋂ w ∈ S, (fun y => ψ (β w y)) ⁻¹' {1} := by ext y; simp [hPdef]
    rw [this]
    exact isClosed_biInter fun w _ =>
      isClosed_singleton.preimage (hψc.comp (hβc.comp (continuous_const.prodMk continuous_id)))
  have hPm : MeasurableSet P := hPc.measurableSet
  have hI := GlobalTheory.T.selfDual_iff_lattice_volume_and_plancherel_alt F E ψ hψ A.L β (beta_isSymm A hK hL (x : A.K)) (beta_nondeg A hK hL x) μ hsd.1
  have hvol : μ S * μ P = 1 := ((hI.1 Λ hΛo hΛc).1).1 hsd
  have horth : ∀ u, ∫ t in S, ψ (β t u) ∂μ = P.indicator (fun _ => ((μ S).toReal : ℂ)) u :=
    (hI.1 Λ hΛo hΛc).2
  have hPS' : P ⊆ S := hPS
  have hQ' : ∀ y ∈ P, ψ (q y) = 1 := hQ
  have hG1 : gaussInt A ψ x μ 1 Λ = ∫ y in S, ψ (q y) ∂μ := by
    unfold gaussInt
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show ψ (Algebra.trace F A.K (1 * (x : A.K) * A.NL y)) = ψ (Algebra.trace F A.K ((x : A.K) * A.NL y))
    rw [one_mul]
  have hG2 : gaussInt A ψ x μ (-1) Λ = ∫ y in S, ψ (-q y) ∂μ := by
    unfold gaussInt
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show ψ (Algebra.trace F A.K (-1 * (x : A.K) * A.NL y)) = ψ (-Algebra.trace F A.K ((x : A.K) * A.NL y))
    rw [neg_one_mul, neg_mul, map_neg]
  have hne : ∀ a : F, ψ (-a) * ψ a = 1 := by
    intro a; rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  have htr : ∀ t ∈ S, (∫ u in S, ψ (q u) ∂μ) = ψ (q t) * ∫ u in S, ψ (q u) * ψ (β t u) ∂μ := by
    intro t ht
    rw [← integral_indicator hSm, ← integral_add_left_eq_self (S.indicator fun u => ψ (q u)) t,
      ← integral_const_mul, ← integral_indicator hSm]
    congr 1; ext u
    by_cases hu : u ∈ S
    · have htu : t + u ∈ S := Λ.add_mem ht hu
      rw [Set.indicator_of_mem htu, Set.indicator_of_mem hu, hqa, AddChar.map_add_eq_mul,
        AddChar.map_add_eq_mul]
      ring
    · have htu : t + u ∉ S := fun h' => hu (by
        have := Λ.sub_mem h' ht
        rwa [add_sub_cancel_left] at this)
      simp [Set.indicator_of_notMem htu, Set.indicator_of_notMem hu]
  haveI : IsFiniteMeasure (μ.restrict S) := isFiniteMeasure_restrict.2 hΛc.measure_lt_top.ne
  have hint : Integrable (Function.uncurry fun t u => ψ (q u) * ψ (β t u))
      ((μ.restrict S).prod (μ.restrict S)) := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) ?_ ?_
    · exact ((hψc.comp (hqc.comp continuous_snd)).mul (hψc.comp hβc)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun z => ?_)
      simp only [Function.uncurry, norm_mul, hψ'.2.1, mul_one, le_refl]
  rw [hG1, hG2]
  calc (∫ y in S, ψ (q y) ∂μ) * ∫ y in S, ψ (-q y) ∂μ
      = ∫ t in S, (∫ y in S, ψ (q y) ∂μ) * ψ (-q t) ∂μ := (integral_const_mul _ _).symm
    _ = ∫ t in S, ∫ u in S, ψ (q u) * ψ (β t u) ∂μ ∂μ := by
        refine setIntegral_congr_fun hSm (fun t ht => ?_)
        rw [htr t ht, mul_comm, ← mul_assoc, hne, one_mul]
    _ = ∫ u in S, ∫ t in S, ψ (q u) * ψ (β t u) ∂μ ∂μ := integral_integral_swap hint
    _ = ∫ u in S, ψ (q u) * P.indicator (fun _ => ((μ S).toReal : ℂ)) u ∂μ := by
        congr 1; ext u
        rw [integral_const_mul, horth u]
    _ = ∫ u in S, P.indicator (fun _ => ((μ S).toReal : ℂ)) u ∂μ := by
        refine setIntegral_congr_fun hSm (fun u _ => ?_)
        by_cases hp : u ∈ P
        · simp only [Set.indicator_of_mem hp, hQ' u hp, one_mul]
        · simp only [Set.indicator_of_notMem hp, mul_zero]
    _ = (μ P).toReal * (μ S).toReal := by
        rw [setIntegral_indicator hPm, Set.inter_eq_right.2 hPS', setIntegral_const]
        simp [Measure.real]
    _ = 1 := by
        have h1 : (μ S).toReal * (μ P).toReal = 1 := by
          rw [← ENNReal.toReal_mul, hvol, ENNReal.toReal_one]
        rw [mul_comm]; exact_mod_cast h1
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussIntegralOneMulGaussIntegralNegOneEqOneStatement
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussIntegral_one_mul_gaussIntegral_neg_one_eq_one : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ Λ : AddSubgroup A.L, IsOpen (Λ : Set A.L) → IsCompact (Λ : Set A.L) → {y : A.L | ∀ w ∈ (Λ : Set A.L), A.kerL ψ x w y = 1} ⊆ Λ → (∀ y ∈ {y : A.L | ∀ w ∈ (Λ : Set A.L), A.kerL ψ x w y = 1}, A.psiK ψ ((x : A.K) * A.NL y) = 1) → gaussInt A ψ x μ 1 Λ * gaussInt A ψ x μ (-1) Λ = 1 := by
  first | exact @GlobalTheory.JR.WeilQuad.gaussInt_one_mul_neg_one | exact GlobalTheory.JR.WeilQuad.gaussInt_one_mul_neg_one | (intros; apply GlobalTheory.JR.WeilQuad.gaussInt_one_mul_neg_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLargeCompactOpenSubgroupWithSmallDual
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLargeCompactOpenSubgroupWithSmallDual
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.WeilQuad.LargeLattice

theorem main : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ),
    Hyp A ψ x μ ω → ∀ C : Set A.L, IsCompact C → ∀ V ∈ 𝓝 (0 : A.L), ∃ Λ : AddSubgroup A.L,
      IsOpen (Λ : Set A.L) ∧ IsCompact (Λ : Set A.L) ∧ C ⊆ Λ ∧
      {y : A.L | ∀ w ∈ (Λ : Set A.L), A.kerL ψ x w y = 1} ⊆ Λ ∧
      {y : A.L | ∀ w ∈ (Λ : Set A.L), A.kerL ψ x w y = 1} ⊆ V := by
  intro F E _ _ _ _ _ A ψ x μ ω h C hC V hV
  obtain ⟨hK, hL, hψ, -, -⟩ := h
  haveI := FourierTest.finite_F_L A
  haveI : IsUltrametricDist F := Unram.ultraF (F := F) (E := E)
  haveI : LocallyCompactSpace F := Unram.lcF (F := F) (E := E)
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : ContinuousAdd A.L := IsModuleTopology.toContinuousAdd F A.L
  haveI : ContinuousSMul F A.L := IsModuleTopology.toContinuousSMul F A.L
  have hcond := ((GlobalTheory.T.unramifiedStandardAddChar_conductor_properties F E).2 ψ hψ).2.2.1
  let β := FourierTest.beta A (x : A.K)
  have hker : ∀ w y, A.kerL ψ x w y = ψ (β w y) := fun _ _ => rfl
  let e := Module.finBasis F A.L
  let Φ : A.L →ₗ[F] (Fin (Module.finrank F A.L) → F) := LinearMap.pi (fun i => β (e i))
  have hΦ : ∀ y i, Φ y i = β (e i) y := fun _ _ => rfl
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    apply FourierTest.beta_sepLeft A hK hL x y
    intro w
    have h0 : β.flip y = 0 := e.ext (fun i => by
      simpa [hΦ] using congrFun hy i)
    rw [FourierTest.beta_symm A hK hL]
    simpa using LinearMap.congr_fun h0 w
  have hsurj : Function.Surjective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).1 hinj
  let Φe := LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩
  have hΦe : ∀ y, Φe y = Φ y := fun _ => rfl
  have hΦc : Continuous Φ := IsModuleTopology.continuous_of_linearMap Φ
  have hΨc : Continuous Φe.symm :=
    IsModuleTopology.continuous_of_linearMap (Φe.symm : (Fin (Module.finrank F A.L) → F) →ₗ[F] A.L)

  have hV' : Φe.symm ⁻¹' V ∈ 𝓝 (0 : Fin (Module.finrank F A.L) → F) :=
    hΨc.continuousAt.preimage_mem_nhds (by simpa using hV)
  obtain ⟨ε, hε0, hεV⟩ := Metric.mem_nhds_iff.1 hV'
  obtain ⟨t, ht⟩ := NormedField.exists_lt_norm F (1 / ε)
  have ht0 : 0 < ‖t‖ := lt_trans (by positivity) ht
  obtain ⟨b, hb⟩ := hC.exists_bound_of_continuousOn hΦc.continuousOn
  let Km : ℝ := ∑ i, ‖Φ (e i)‖
  have hKm : ∀ i j, ‖Φ (e i) j‖ ≤ Km := fun i j =>
    (norm_le_pi_norm (Φ (e i)) j).trans
      (Finset.single_le_sum (f := fun i => ‖Φ (e i)‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i))
  let R : ℝ := max (max b (‖t‖ * Km)) (max ε 1)
  have hR1 : 1 ≤ R := le_trans (le_max_right _ _) (le_max_right _ _)
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR1
  have hRε : ε ≤ R := le_trans (le_max_left _ _) (le_max_right _ _)
  have hRb : b ≤ R := le_trans (le_max_left _ _) (le_max_left _ _)
  have hRt : ‖t‖ * Km ≤ R := le_trans (le_max_right _ _) (le_max_left _ _)
  let Λ : AddSubgroup A.L :=
    { carrier := {y | ∀ i, ‖Φ y i‖ ≤ R}
      add_mem' := by
        intro a c ha hc i
        simp only [Set.mem_setOf_eq, map_add (f := _), Pi.add_apply] at *
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha i) (hc i))
      zero_mem' := by intro i; simp [hR0.le]
      neg_mem' := by
        intro a ha i
        simp only [Set.mem_setOf_eq, map_neg, Pi.neg_apply, norm_neg] at *
        exact ha i }
  have hmem : ∀ y, y ∈ Λ ↔ ∀ i, ‖Φ y i‖ ≤ R := fun _ => Iff.rfl

  have hperp : ∀ y ∈ {y : A.L | ∀ w ∈ (Λ : Set A.L), A.kerL ψ x w y = 1}, ∀ i, ‖Φ y i‖ < ε := by
    intro y hy i
    have h1 : ‖t * Φ y i‖ ≤ 1 := by
      refine (hcond (t * Φ y i)).1 fun e' he' => ?_
      have hw : (e' * t) • e i ∈ Λ := by
        rw [hmem]; intro j
        rw [map_smul, Pi.smul_apply, smul_eq_mul, norm_mul, norm_mul]
        calc ‖e'‖ * ‖t‖ * ‖Φ (e i) j‖ ≤ 1 * ‖t‖ * Km := by gcongr; exact hKm i j
          _ ≤ R := by rw [one_mul]; exact hRt
      have := hy _ hw
      rw [hker, map_smul, LinearMap.smul_apply, smul_eq_mul] at this
      rw [← hΦ] at this
      rwa [← mul_assoc]
    rw [norm_mul] at h1
    have h2 : ‖Φ y i‖ ≤ 1 / ‖t‖ := by rw [le_div_iff₀ ht0]; linarith
    have h3 : 1 / ‖t‖ < ε := by
      rw [div_lt_iff₀ ht0]
      rw [div_lt_iff₀ hε0] at ht
      linarith
    exact lt_of_le_of_lt h2 h3
  refine ⟨Λ, ?_, ?_, ?_, ?_, ?_⟩
  · have : (Λ : Set A.L) = ⋂ i, (fun y => Φ y i) ⁻¹' Metric.closedBall 0 R := by
      ext y; simp [hmem, mem_closedBall_zero_iff]
    rw [this]
    exact isOpen_iInter_of_finite fun i =>
      (IsUltrametricDist.isOpen_closedBall 0 hR0.ne').preimage ((continuous_apply i).comp hΦc)
  · have : (Λ : Set A.L) = Φe.symm '' Metric.closedBall 0 R := by
      ext y
      rw [SetLike.mem_coe, hmem, Set.mem_image]
      constructor
      · intro hy
        refine ⟨Φe y, ?_, by simp⟩
        rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hR0.le, hΦe]; exact hy
      · rintro ⟨z, hz, rfl⟩
        rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hR0.le] at hz
        intro i
        have : Φ (Φe.symm z) = z := by rw [← hΦe]; simp
        rw [this]; exact hz i
    rw [this]
    exact (isCompact_closedBall 0 R).image hΨc
  · intro y hy
    rw [SetLike.mem_coe, hmem]
    intro i
    exact ((norm_le_pi_norm (Φ y) i).trans (hb y hy)).trans hRb
  · intro y hy
    rw [SetLike.mem_coe, hmem]
    intro i
    exact (hperp y hy i).le.trans hRε
  · intro y hy
    have hb' : Φe y ∈ Metric.ball (0 : Fin (Module.finrank F A.L) → F) ε := by
      rw [mem_ball_zero_iff, pi_norm_lt_iff hε0, hΦe]; exact hperp y hy
    have := hεV hb'
    simpa using this

end GlobalTheory.JR.WeilQuad.LargeLattice
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLargeCompactOpenSubgroupWithSmallDualStatement
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_large_compactOpen_subgroup_with_small_dual : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ C : Set A.L, IsCompact C → ∀ V ∈ 𝓝 (0 : A.L), ∃ Λ : AddSubgroup A.L, IsOpen (Λ : Set A.L) ∧ IsCompact (Λ : Set A.L) ∧ C ⊆ Λ ∧ {y : A.L | ∀ w ∈ (Λ : Set A.L), A.kerL ψ x w y = 1} ⊆ Λ ∧ {y : A.L | ∀ w ∈ (Λ : Set A.L), A.kerL ψ x w y = 1} ⊆ V := by
  first | exact @GlobalTheory.JR.WeilQuad.LargeLattice.main | exact GlobalTheory.JR.WeilQuad.LargeLattice.main | (intros; apply GlobalTheory.JR.WeilQuad.LargeLattice.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleTraceAddCharNormEqOneNearZero
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleTraceAddCharNormEqOneNearZero
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.WeilQuad.NearZero
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem finite_E_L [Unram F E] (A : Et F E) : Module.Finite E A.L := by
  have hE : Module.Finite F E := Module.finite_of_finrank_pos (by rw [Unram.finrank_eq (F := F) (E := E)]; norm_num)
  have h := A.push.out
  exact Module.Finite.equiv h.equiv

theorem finite_F_L [Unram F E] (A : Et F E) : Module.Finite F A.L := by
  have hE : Module.Finite F E := Module.finite_of_finrank_pos (by rw [Unram.finrank_eq (F := F) (E := E)]; norm_num)
  have := finite_E_L A
  exact Module.Finite.trans E A.L

theorem finite_K_L [Unram F E] (A : Et F E) : Module.Finite A.K A.L := by
  have := finite_F_L A
  exact Module.Finite.of_restrictScalars_finite F A.K A.L

theorem continuous_NL [Unram F E] (A : Et F E) (hK : IsField A.K) :
    Continuous (fun y : A.L => A.NL y) := by
  letI : Field A.K := hK.toField
  have := finite_K_L A
  let b := Module.Free.chooseBasis A.K A.L
  have hfun : (fun y : A.L => A.NL y) = fun y => (Algebra.leftMulMatrix b y).det := by
    funext y; exact Algebra.norm_eq_matrix_det b y
  rw [hfun]
  refine Continuous.matrix_det (continuous_matrix fun i j => ?_)
  let φ : A.L →ₗ[A.K] A.K := (LinearMap.proj j : (_ → A.K) →ₗ[A.K] A.K) ∘ₗ
    (LinearMap.proj i : (_ → _ → A.K) →ₗ[A.K] _) ∘ₗ (Algebra.leftMulMatrix b).toLinearMap
  have hφ : Continuous (φ.restrictScalars F) := IsModuleTopology.continuous_of_linearMap _
  exact hφ

theorem NL_zero [Unram F E] (A : Et F E) (hK : IsField A.K) (hL : IsField A.L) : A.NL (0 : A.L) = 0 := by
  letI : Field A.K := hK.toField
  have := finite_K_L A
  haveI : Nontrivial A.L := ⟨hL.exists_pair_ne⟩
  exact Algebra.norm_zero

end GlobalTheory.JR.WeilQuad.NearZero

theorem GlobalTheory.JR.WeilQuad.psiK_norm_eq_one_near_zero : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L)
    (ω : A.K → ℂ), Hyp A ψ x μ ω → {y : A.L | A.psiK ψ ((x : A.K) * A.NL y) = 1} ∈ 𝓝 (0 : A.L) := by
  intro F E _ _ _ _ _ A ψ x μ ω h
  obtain ⟨hK, hL, hψ, -, -⟩ := h
  let g : A.L → F := fun y => Algebra.trace F A.K ((x : A.K) * A.NL y)
  have hg : Continuous g := by
    have ht : Continuous (Algebra.trace F A.K) := IsModuleTopology.continuous_of_linearMap _
    exact ht.comp (continuous_const.mul (NearZero.continuous_NL A hK))
  have hg0 : g 0 = 0 := by simp [g, NearZero.NL_zero A hK hL]
  have hmem : g ⁻¹' Metric.ball 0 1 ∈ 𝓝 (0 : A.L) :=
    hg.continuousAt.preimage_mem_nhds (by rw [hg0]; exact Metric.ball_mem_nhds 0 one_pos)
  refine Filter.mem_of_superset hmem fun y hy => ?_
  have hy' : ‖g y‖ < 1 := by simpa using hy
  exact hψ.1 _ hy'.le
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleTraceAddCharNormEqOneNearZeroStatement
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleTraceAddChar_norm_eq_one_near_zero : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → {y : A.L | A.psiK ψ ((x : A.K) * A.NL y) = 1} ∈ 𝓝 (0 : A.L) := by
  first | exact @GlobalTheory.JR.WeilQuad.psiK_norm_eq_one_near_zero | exact GlobalTheory.JR.WeilQuad.psiK_norm_eq_one_near_zero | (intros; apply GlobalTheory.JR.WeilQuad.psiK_norm_eq_one_near_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableQuadraticGaussIntegralSqEqOne
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.WeilQuad

theorem stableGauss_sq_eq_one : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L)
    (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ G₁ : ℂ, IsStableGauss A ψ x μ 1 G₁ → G₁ ^ 2 = 1 := by
  intro F E _ _ _ _ _ A ψ x μ ω hH G₁ hG
  have hG' := GlobalTheory.T.stableQuadraticGauss_neg_one_eq_one F E A ψ x μ ω hH G₁ hG
  obtain ⟨Λ₀, -, hc₀, h₀⟩ := hG
  obtain ⟨Λ₁, -, hc₁, h₁⟩ := hG'
  obtain ⟨Λ, ho, hc, hsub, hperp, hV⟩ := GlobalTheory.T.exists_large_compactOpen_subgroup_with_small_dual F E A ψ x μ ω hH ((Λ₀ : Set A.L) ∪ Λ₁) (hc₀.union hc₁)
    _ (GlobalTheory.T.etaleTraceAddChar_norm_eq_one_near_zero F E A ψ x μ ω hH)
  have e0 := h₀ Λ ho hc (fun y hy => hsub (Or.inl hy))
  have e1 := h₁ Λ ho hc (fun y hy => hsub (Or.inr hy))
  have hp := GlobalTheory.T.gaussIntegral_one_mul_gaussIntegral_neg_one_eq_one F E A ψ x μ ω hH Λ ho hc hperp (fun y hy => hV hy)
  rw [e0, e1] at hp
  rw [sq]; exact hp

end GlobalTheory.JR.WeilQuad
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableQuadraticGaussIntegralSqEqOneStatement
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stableQuadraticGaussIntegral_sq_eq_one : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ G₁ : ℂ, IsStableGauss A ψ x μ 1 G₁ → G₁ ^ 2 = 1 := by
  first | exact @GlobalTheory.JR.WeilQuad.stableGauss_sq_eq_one | exact GlobalTheory.JR.WeilQuad.stableGauss_sq_eq_one | (intros; apply GlobalTheory.JR.WeilQuad.stableGauss_sq_eq_one <;> assumption)
end
