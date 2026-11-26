module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualMeasureExistsUniqueFourierInversion
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleHermitianPairStructureFacts
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PiExteriorTensorFlattenedIndexEquivNested

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuadraticWeilFourierPreservesTestAdditive
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuadraticWeilFourierPreservesTestAdditive
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.WeilQuad.FourierTest

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem finite_F_L [Unram F E] (A : Et F E) : Module.Finite F A.L := by
  haveI : Module.Finite F E :=
    Module.finite_of_finrank_pos (by rw [Unram.finrank_eq (F := F) (E := E)]; norm_num)
  haveI : Module.Finite A.K A.L := Module.Finite.equiv A.push.symm.out.equiv
  exact Module.Finite.trans A.K A.L

theorem star_smul_F (A : Et F E) (c : F) (y : A.L) : star (c • y) = c • star y := by
  rw [Algebra.smul_def, Algebra.smul_def, star_mul, mul_comm, IsScalarTower.algebraMap_apply F A.K A.L, A.star_K]

def beta (A : Et F E) (x : A.K) : LinearMap.BilinForm F A.L :=
  LinearMap.mk₂ F (fun y' y => Algebra.trace F A.K (x * Algebra.trace A.K A.L (star y' * y)))
    (by intro a b c; simp only [star_add, add_mul, map_add (f := _), mul_add])
    (by intro c a b
        rw [star_smul_F, smul_mul_assoc, LinearMap.map_smul_of_tower, mul_smul_comm, LinearMap.map_smul])
    (by intro a b c; simp only [mul_add, map_add (f := _)])
    (by intro c a b
        rw [mul_smul_comm, LinearMap.map_smul_of_tower, mul_smul_comm, LinearMap.map_smul])

theorem beta_apply (A : Et F E) (x : A.K) (y' y : A.L) :
    beta A x y' y = Algebra.trace F A.K (x * Algebra.trace A.K A.L (star y' * y)) := rfl

theorem algMap_inj (A : Et F E) (hK : IsField A.K) (hL : IsField A.L) :
    Function.Injective (algebraMap A.K A.L) := by
  haveI : Nontrivial A.L := ⟨hL.exists_pair_ne⟩
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro k hk
  by_contra hne
  obtain ⟨k', hk'⟩ := hK.mul_inv_cancel hne
  have h : algebraMap A.K A.L (k * k') = 0 := by rw [map_mul, hk, zero_mul]
  rw [hk', map_one] at h
  exact one_ne_zero h

theorem beta_symm [Unram F E] (A : Et F E) (hK : IsField A.K) (hL : IsField A.L) (x : A.K) :
    ∀ a b, beta A x a b = beta A x b a := by
  intro a b
  rw [beta_apply, beta_apply]
  congr 2
  apply algMap_inj A hK hL
  rw [(GlobalTheory.T.etaleHermitianPair_structure_facts F E A).2.1, (GlobalTheory.T.etaleHermitianPair_structure_facts F E A).2.1, star_mul, star_mul, star_star, star_star]
  ring

theorem trace_algMap [Unram F E] (A : Et F E) (hK : IsField A.K) (hL : IsField A.L) (c : A.K) :
    Algebra.trace A.K A.L (algebraMap A.K A.L c) = 2 * c := by
  apply algMap_inj A hK hL
  rw [(GlobalTheory.T.etaleHermitianPair_structure_facts F E A).2.1, A.star_K, map_mul, map_ofNat]
  ring

theorem beta_sepLeft [Unram F E] (A : Et F E) (hK : IsField A.K) (hL : IsField A.L) (x : A.Kˣ) :
    (beta A x).SeparatingLeft := by
  haveI : Nontrivial A.K := ⟨hK.exists_pair_ne⟩
  haveI : CharZero F := Unram.charZero (F := F) (E := E)
  intro a ha
  by_contra hne
  have hsa : star a ≠ 0 := by
    intro h; apply hne; simpa using congrArg star h
  obtain ⟨u, hu⟩ := hL.mul_inv_cancel hsa
  have h2 : (2 : A.K) ≠ 0 := by
    have : (2 : A.K) = algebraMap F A.K 2 := by rw [map_ofNat]
    rw [this]
    intro h
    exact two_ne_zero ((injective_iff_map_eq_zero (algebraMap F A.K)).1 (algebraMap F A.K).injective _ h)
  obtain ⟨t, ht⟩ := hK.mul_inv_cancel h2
  have htr : ∀ k : A.K, Algebra.trace F A.K k = 0 := by
    intro k
    have := ha (u * algebraMap A.K A.L (((x⁻¹ : A.Kˣ) : A.K) * t * k))
    rw [beta_apply, ← mul_assoc, hu, one_mul, trace_algMap A hK hL] at this
    have e : (x : A.K) * (2 * (((x⁻¹ : A.Kˣ) : A.K) * t * k)) = k := by
      calc (x : A.K) * (2 * (((x⁻¹ : A.Kˣ) : A.K) * t * k))
          = ((x : A.K) * ((x⁻¹ : A.Kˣ) : A.K)) * (2 * t) * k := by ring
        _ = k := by rw [Units.mul_inv, ht, one_mul, one_mul]
    rwa [e] at this
  have h1 : (1 : A.K) = 0 :=
    (GlobalTheory.T.etaleHermitianPair_structure_facts F E A).2.2.1.1 1 (fun n => by rw [Algebra.traceForm_apply, one_mul]; exact htr n)
  exact one_ne_zero h1

theorem beta_isSymm [Unram F E] (A : Et F E) (hK : IsField A.K) (hL : IsField A.L) (x : A.K) :
    (beta A x).IsSymm := LinearMap.BilinForm.isSymm_def.2 (beta_symm A hK hL x)

theorem beta_nondeg [Unram F E] (A : Et F E) (hK : IsField A.K) (hL : IsField A.L) (x : A.Kˣ) :
    (beta A x).Nondegenerate :=
  ((beta_isSymm A hK hL x).isRefl.nondegenerate_iff_separatingLeft).2 (beta_sepLeft A hK hL x)

theorem cont_psi {ψ : AddChar F ℂ} (hψ : IsStdChar ψ) : Continuous ψ := by
  refine continuous_iff_continuousAt.2 fun a => ?_
  have h : (fun b => ψ b) =ᶠ[𝓝 a] fun _ => ψ a := by
    filter_upwards [Metric.ball_mem_nhds a one_pos] with b hb
    have h1 : ψ (b - a) = 1 := hψ.1 _ (by rw [← dist_eq_norm]; exact le_of_lt hb)
    calc ψ b = ψ (a + (b - a)) := by rw [add_sub_cancel]
      _ = ψ a * ψ (b - a) := AddChar.map_add_eq_mul ψ _ _
      _ = ψ a := by rw [h1, mul_one]
  exact continuousAt_const.congr h.symm

end GlobalTheory.JR.WeilQuad.FourierTest


open GlobalTheory.JR.WeilQuad.FourierTest in
theorem GlobalTheory.JR.WeilQuad.fOp_isTest_add : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L)
    (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ φ : A.L → ℂ, IsTest φ → IsTest (fOp A ψ x μ φ) ∧
      ∀ φ' : A.L → ℂ, IsTest φ' → fOp A ψ x μ (φ + φ') = fOp A ψ x μ φ + fOp A ψ x μ φ' := by
  intro F E _ _ _ _ _ A ψ x μ ω h φ hφ
  obtain ⟨hK, hL, hψ, hsd, -⟩ := h
  haveI := hsd.1
  haveI := finite_F_L A
  have hker : A.kerL ψ (x : A.K) = fun a b => ψ (beta A x a b) := rfl
  have hint : ∀ f : A.L → ℂ, IsTest f → ∀ y, Integrable (fun y' => f y' * A.kerL ψ (x : A.K) y' y) μ := by
    intro f hf y
    rw [hker]
    refine Continuous.integrable_of_hasCompactSupport ?_ (hf.2.mul_right)
    exact hf.1.continuous.mul
      ((cont_psi hψ).comp (IsModuleTopology.continuous_of_linearMap ((beta A x).flip y)))
  refine ⟨?_, fun φ' hφ' => ?_⟩
  · have := (GlobalTheory.JR.SelfDualUniq.selfDual_exists_unique_isTest F E ψ hψ A.L (beta A x)
      (beta_isSymm A hK hL x) (beta_nondeg A hK hL x)).2 μ hsd.1 φ hφ
    unfold fOp
    rw [hker]
    exact this
  · funext y
    simp only [fOp, fourB, Pi.add_apply, add_mul]
    exact integral_add (hint φ hφ y) (hint φ' hφ' y)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuadraticWeilFourierPreservesTestAdditiveStatement
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadraticWeilFourier_preserves_test_additive : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ φ : A.L → ℂ, IsTest φ → IsTest (fOp A ψ x μ φ) ∧ ∀ φ' : A.L → ℂ, IsTest φ' → fOp A ψ x μ (φ + φ') = fOp A ψ x μ φ + fOp A ψ x μ φ' := by
  first | exact @GlobalTheory.JR.WeilQuad.fOp_isTest_add | exact GlobalTheory.JR.WeilQuad.fOp_isTest_add | (intros; apply GlobalTheory.JR.WeilQuad.fOp_isTest_add <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStableQuadraticGaussIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStableQuadraticGaussIntegral
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.WeilQuad.GaussStable

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem NL_add [Unram F E] (A : Et F E) (y m : A.L) :
    A.NL (y + m) = A.NL y + Algebra.trace A.K A.L (star m * y) + A.NL m := by
  obtain ⟨-, hinj, hN, htr, -⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
  apply hinj
  rw [map_add (f := _), map_add (f := _), hN, hN, hN, htr, star_add, star_mul, star_star]
  ring

theorem NL_zero [Unram F E] (A : Et F E) : A.NL 0 = 0 := by
  obtain ⟨-, hinj, hN, -, -⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
  apply hinj
  rw [hN, zero_mul, map_zero]

theorem formL_symm_nondeg [U : Unram F E] (A : Et F E) (v : A.Kˣ) :
    (EtMeas.formL A v).IsSymm ∧ (EtMeas.formL A v).Nondegenerate := by
  have := U.charZero
  have := EtMeas.finite_L A
  obtain ⟨-, hinj, -, htr, hnd⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
  have hs : (EtMeas.formL A v).IsSymm := ⟨fun y y' => by
    rw [EtMeas.formL_apply, EtMeas.formL_apply]
    congr 2
    apply hinj
    rw [htr, htr]; simp [add_comm, mul_comm]⟩
  have hl : ∀ y', (∀ y, EtMeas.formL A v y' y = 0) → y' = 0 := fun y' h => hnd y' fun y => by
    have h1 : (v : A.K) * Algebra.trace A.K A.L (star y' * y) = 0 := EtMeas.eq_zero_of_trace F A.K _ fun k => by
      have := h (k • y)
      rw [EtMeas.formL_apply, mul_smul_comm, map_smul, smul_eq_mul] at this
      rw [← this]; congr 1; ring
    simpa using h1
  exact ⟨hs, ⟨hl, fun y h => hl y fun y' => by rw [hs.eq]; exact h y'⟩⟩


open scoped Classical in
open Classical in
theorem integral_indicator_char {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (M : AddSubgroup V)
    (hMo : IsOpen (M : Set V)) (χ : V → ℂ) (hχ : ∀ a b, χ (a + b) = χ a * χ b) :
    ∫ m, (M : Set V).indicator χ m ∂μ = if ∀ m ∈ M, χ m = 1 then (μ.real (M : Set V) : ℂ) else 0 := by
  classical
  split_ifs with h
  · rw [show (M : Set V).indicator χ = (M : Set V).indicator (fun _ => (1 : ℂ)) from
      Set.indicator_congr (fun m hm => h m hm), integral_indicator_const _ hMo.measurableSet]
    simp
  · push Not at h
    obtain ⟨m0, hm0, h1⟩ := h
    refine AbsInv.integral_eq_zero_of_translate μ _ m0 (χ m0) h1 fun m => ?_
    by_cases hm : m ∈ M
    · rw [Set.indicator_of_mem (by exact M.add_mem hm hm0), Set.indicator_of_mem (by exact hm), hχ, mul_comm]
    · have h2 : m + m0 ∉ M := fun h' => hm (by simpa using M.sub_mem h' hm0)
      rw [Set.indicator_of_notMem (by exact h2), Set.indicator_of_notMem (by exact hm), mul_zero]

end GlobalTheory.JR.WeilQuad.GaussStable


open GlobalTheory.JR.WeilQuad.GaussStable in
theorem GlobalTheory.JR.WeilQuad.exists_stableGauss : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L)
    (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ u : A.Kˣ, ∃ G, IsStableGauss A ψ x μ u G := by
  intro F E _ _ _ _ hU A ψ x μ ω h u
  classical
  obtain ⟨-, -, hψ, hsd, -⟩ := h
  haveI := hsd.1
  haveI : IsUltrametricDist F := hU.ultraF
  haveI : LocallyCompactSpace F := hU.lcF
  haveI := EtMeas.finite_L A
  haveI : IsTopologicalAddGroup A.L := IsModuleTopology.topologicalAddGroup F A.L
  set β := EtMeas.formL A ((u * x : A.Kˣ) : A.K) with hβ
  set f : A.L → ℂ := fun y => A.psiK ψ ((u : A.K) * x * A.NL y) with hf
  have htr : Continuous (Algebra.trace F A.K) := IsModuleTopology.continuous_of_linearMap _
  have hin : Continuous fun y : A.L => Algebra.trace F A.K ((u : A.K) * x * A.NL y) :=
    htr.comp (continuous_const.mul (GlobalTheory.JR.EtMeas.continuous_NL A))
  have hflc : IsLocallyConstant f := (isLocallyConstant_of_stdChar hψ).comp_continuous hin
  have hfc : Continuous f := hflc.continuous
  have hkey : ∀ y m, f (y + m) = f y * ψ (β m y) * f m := by
    intro y m
    simp only [hf, hβ, EtMeas.formL_apply, Units.val_mul, NL_add A, Et.psiK, mul_add, map_add (f := _),
      AddChar.map_add_eq_mul]
  have hf0 : f 0 = 1 := by simp [hf, NL_zero A, Et.psiK]
  obtain ⟨-, hsmall⟩ := GlobalTheory.JR.exists_small_dual_lattices F ψ hψ A.L β
    (formL_symm_nondeg A (u * x)).1 (formL_symm_nondeg A (u * x)).2
  obtain ⟨M, N, hMU, hMo, hMc, hNo, hNc, hN, -⟩ :=
    hsmall {y | f y = 1} ((hflc.isOpen_fiber 1).mem_nhds hf0)
  have hfM : ∀ m ∈ M, f m = 1 := fun m hm => hMU hm
  have hMpos : μ.real (M : Set A.L) ≠ 0 :=
    (ENNReal.toReal_pos (hMo.measure_pos μ ⟨0, M.zero_mem⟩).ne' hMc.measure_lt_top.ne).ne'
  refine ⟨∫ y in (N : Set A.L), f y ∂μ, M ⊔ N, AddSubgroup.isOpen_mono le_sup_left hMo, ?_, ?_⟩
  · refine (hMc.add hNc).of_isClosed_subset
      (AddSubgroup.isClosed_of_isOpen _ (AddSubgroup.isOpen_mono le_sup_left hMo)) ?_
    intro z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := AddSubgroup.mem_sup.1 hz
    exact Set.add_mem_add ha hb
  intro Λ hΛo hΛc hle
  have hMΛ : M ≤ Λ := le_sup_left.trans hle
  have hNΛ : N ≤ Λ := le_sup_right.trans hle
  set iM : A.L → ℂ := (M : Set A.L).indicator (fun _ => 1) with hiM
  set iΛ : A.L → ℂ := (Λ : Set A.L).indicator (fun _ => 1) with hiΛ
  have hiMc : Continuous iM :=
    IsClopen.continuous_indicator ⟨AddSubgroup.isClosed_of_isOpen _ hMo, hMo⟩ continuous_const
  have hiΛc : Continuous iΛ :=
    IsClopen.continuous_indicator ⟨AddSubgroup.isClosed_of_isOpen _ hΛo, hΛo⟩ continuous_const
  let g : A.L → A.L → ℂ := fun m y => iM m * (iΛ y * f (y + m))
  have hgc : Continuous (Function.uncurry g) :=
    (hiMc.comp continuous_fst).mul ((hiΛc.comp continuous_snd).mul (hfc.comp (continuous_snd.add continuous_fst)))
  have hgs : HasCompactSupport (Function.uncurry g) := by
    refine HasCompactSupport.intro (hMc.prod hΛc) ?_
    rintro ⟨m, y⟩ hp
    simp only [Set.mem_prod, not_and_or] at hp
    rcases hp with hp | hp
    · have : iM m = 0 := by rw [hiM, Set.indicator_of_notMem hp]
      simp [Function.uncurry, g, this]
    · have : iΛ y = 0 := by rw [hiΛ, Set.indicator_of_notMem hp]
      simp [Function.uncurry, g, this]
  have hswap := integral_integral_swap_of_hasCompactSupport hgc hgs (μ := μ) (ν := μ)
  have hA : ∀ m, ∫ y, g m y ∂μ = iM m * ∫ y in (Λ : Set A.L), f y ∂μ := by
    intro m
    by_cases hm : m ∈ M
    · have e : ∀ y, iΛ y * f (y + m) = (Λ : Set A.L).indicator f (y + m) := by
        intro y
        by_cases hy : y ∈ Λ
        · rw [hiΛ, Set.indicator_of_mem (by exact hy), Set.indicator_of_mem (by exact Λ.add_mem hy (hMΛ hm)), one_mul]
        · have h2 : y + m ∉ Λ := fun h' => hy (by simpa using Λ.sub_mem h' (hMΛ hm))
          rw [hiΛ, Set.indicator_of_notMem (by exact hy), Set.indicator_of_notMem (by exact h2), zero_mul]
      simp only [g]
      rw [integral_const_mul]
      congr 1
      simp_rw [e]
      rw [integral_add_right_eq_self (μ := μ) ((Λ : Set A.L).indicator f) m,
        integral_indicator hΛo.measurableSet]
    · have h1 : iM m = 0 := by rw [hiM, Set.indicator_of_notMem (by exact hm)]
      simp [g, h1]
  have hB : ∀ y, ∫ m, g m y ∂μ = (N : Set A.L).indicator (fun y => (μ.real (M : Set A.L) : ℂ) * f y) y := by
    intro y
    have e : ∀ m, g m y = iΛ y * f y * (M : Set A.L).indicator (fun m => ψ (β m y)) m := by
      intro m
      by_cases hm : m ∈ M
      · have h1 : iM m = 1 := by rw [hiM, Set.indicator_of_mem (by exact hm)]
        have h2 : (M : Set A.L).indicator (fun m => ψ (β m y)) m = ψ (β m y) :=
          Set.indicator_of_mem (by exact hm) _
        simp only [g]
        rw [h1, h2, hkey, hfM m hm]; ring
      · have h1 : iM m = 0 := by rw [hiM, Set.indicator_of_notMem (by exact hm)]
        have h2 : (M : Set A.L).indicator (fun m => ψ (β m y)) m = 0 :=
          Set.indicator_of_notMem (by exact hm) _
        simp only [g]
        rw [h1, h2]; ring
    simp_rw [e]
    rw [integral_const_mul, integral_indicator_char μ M hMo (fun m => ψ (β m y))
      (fun a b => by simp [map_add (f := _), AddChar.map_add_eq_mul])]
    by_cases hy : y ∈ N
    · rw [if_pos ((hN y).1 hy), Set.indicator_of_mem (by exact hy), hiΛ, Set.indicator_of_mem (by exact hNΛ hy)]
      ring
    · rw [if_neg (fun h' => hy ((hN y).2 h')), Set.indicator_of_notMem (by exact hy), mul_zero]
  have h1 : ∫ m, ∫ y, g m y ∂μ ∂μ = (μ.real (M : Set A.L) : ℂ) * ∫ y in (Λ : Set A.L), f y ∂μ := by
    simp_rw [hA]
    rw [integral_mul_const, hiM, integral_indicator_const _ hMo.measurableSet]
    simp
  have h2 : ∫ y, ∫ m, g m y ∂μ ∂μ = (μ.real (M : Set A.L) : ℂ) * ∫ y in (N : Set A.L), f y ∂μ := by
    simp_rw [hB]
    rw [integral_indicator hNo.measurableSet, integral_const_mul]
  have hmain := h1.symm.trans (hswap.trans h2)
  unfold gaussInt
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.2 hMpos) hmain
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStableQuadraticGaussIntegralStatement
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_stable_quadraticGaussIntegral : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ u : A.Kˣ, ∃ G, IsStableGauss A ψ x μ u G := by
  first | exact @GlobalTheory.JR.WeilQuad.exists_stableGauss | exact GlobalTheory.JR.WeilQuad.exists_stableGauss | (intros; apply GlobalTheory.JR.WeilQuad.exists_stableGauss <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMatrixFrobenius
open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.NB GlobalTheory.CycFr GlobalTheory.WachTie

namespace GlobalTheory.WachTie.MatF

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) {l : ℕ}

open PowerSeries in
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : _root_.Formalism.BasicNotions.LocWach PD LL O v n) {l : ℕ} in
theorem _root_.GlobalTheory.WachTie.MatF.φD_smulA (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O) (a : _root_.Formalism.BasicNotions.LetA O n)
    (x : W.DD T) : W.φD T (a • x) = W.φA a • W.φD T x := by
  rw [← algebraMap_smul W.EE a x, W.φD_smul, W.φE_ext, algebraMap_smul]
  rfl

open PowerSeries in
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : _root_.Formalism.BasicNotions.LocWach PD LL O v n) {l : ℕ} in
theorem _root_.GlobalTheory.WachTie.MatF.γD_smulA (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O) (g : W.Gam) (a : _root_.Formalism.BasicNotions.LetA O n) (x : W.DD T) :
    W.γD T g (a • x) = W.γA g a • W.γD T g x := by
  rw [← algebraMap_smul W.EE a x, W.γD_smul, W.γE_ext, algebraMap_smul]
  rfl


open PowerSeries in
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : _root_.Formalism.BasicNotions.LocWach PD LL O v n) {l : ℕ} in
theorem _root_.GlobalTheory.WachTie.MatF.coord_unique (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O) {r : ℕ}
    (b : Module.Basis (Fin r) (_root_.Formalism.BasicNotions.LetA O n) ↥(W.N T)) (c d : Fin r → _root_.Formalism.BasicNotions.LetA O n)
    (h : ∑ m, c m • (b m : W.DD T) = ∑ m, d m • (b m : W.DD T)) : c = d := by
  have h' : ∑ m, c m • b m = ∑ m, d m • b m := Subtype.ext (by simpa [Submodule.coe_sum] using h)
  exact b.equivFun.symm.injective (by rw [b.equivFun_symm_apply, b.equivFun_symm_apply]; exact h')

open PowerSeries in
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : _root_.Formalism.BasicNotions.LocWach PD LL O v n) {l : ℕ} in
theorem _root_.GlobalTheory.WachTie.MatF.exists_coord (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O) {r : ℕ}
    (b : Module.Basis (Fin r) (_root_.Formalism.BasicNotions.LetA O n) ↥(W.N T)) (x : W.DD T) (hx : x ∈ W.N T) :
    ∃ c : Fin r → _root_.Formalism.BasicNotions.LetA O n, x = ∑ m, c m • (b m : W.DD T) := by
  refine ⟨b.equivFun ⟨x, hx⟩, ?_⟩
  have h := congrArg Subtype.val (b.sum_equivFun ⟨x, hx⟩)
  rw [Submodule.coe_sum] at h
  simpa only [Submodule.coe_smul] using h.symm

open PowerSeries in
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : _root_.Formalism.BasicNotions.LocWach PD LL O v n) {l : ℕ} in
theorem _root_.GlobalTheory.WachTie.MatF.exists_matrix_frobenius (R : _root_.GlobalTheory.NB.Fr l O) (j : O⟦X⟧ →ₐ[O] O⟦X⟧)
    (jE : (ZMod n → R.EE) →ₐ[O] W.EE) (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O) {r : ℕ}
    (b : Module.Basis (Fin r) (_root_.Formalism.BasicNotions.LetA O n) ↥(W.N T)) (hF : _root_.GlobalTheory.WachTie.FrTie W R j)
    (_hE : _root_.GlobalTheory.WachTie.EETie W R j jE)
    (hb : ∀ k, (b k : W.DD T) ∈ W.NΔ T) (hs : W.s = 1) (hu : IsUnit (W.DelF.card : O)) :
    ∃ (M : ℕ) (Φ : ZMod n → Matrix (Fin r) (Fin r) O⟦X⟧),
      (∀ i, ∃ (k : ℕ) (Ψ : Matrix (Fin r) (Fin r) O⟦X⟧),
        Φ i * Ψ = R.E ^ k • (1 : Matrix (Fin r) (Fin r) O⟦X⟧)) ∧
      (∀ k, (fun _ => j R.E : _root_.Formalism.BasicNotions.LetA O n) ^ M • W.φD T (b k : W.DD T) =
        ∑ m, (fun i => j (Φ i m k) : _root_.Formalism.BasicNotions.LetA O n) • (b m : W.DD T)) := by
  classical
  obtain ⟨hj, hrange, -, -, -, -, -, u, hu'⟩ := hF
  set q : _root_.Formalism.BasicNotions.LetA O n := fun _ => W.q₀ with hq
  set e : _root_.Formalism.BasicNotions.LetA O n := fun _ => j R.E with he
  set w : _root_.Formalism.BasicNotions.LetA O n := fun _ => ((u⁻¹ : O⟦X⟧ˣ) : O⟦X⟧) with hw
  have hqe : e = w * q := by
    funext i
    simp only [he, hw, hq, Pi.mul_apply]
    rw [← hu', mul_left_comm, Units.inv_mul, mul_one]
  have hpow : ∀ k (x : W.DD T), ((_root_.Formalism.BasicNotions.letφ (n := n) W.φ₀ ^ (W.s - 1)) fun _ => W.q₀) ^ k • x = q ^ k • x := by
    intro k x
    rw [hs, Nat.sub_self, pow_zero]
    rfl
  have hinv : ∀ y : O⟦X⟧, (∀ δ ∈ W.DelF, W.γ₀ δ y = y) → j (Function.invFun j y) = y :=
    fun y hy => Function.invFun_eq ((hrange y).2 hy)
  have hγe : ∀ δ ∈ W.DelF, W.γA δ e = e := by
    intro δ hδ
    funext i
    exact (hrange _).1 ⟨_, rfl⟩ δ hδ
  have hbN : ∀ k, (b k : W.DD T) ∈ W.N T := fun k => (b k).2
  have hbΔ : ∀ k, ∀ δ ∈ W.DelF, W.γD T δ (b k) = b k := fun k => (hb k).2
  have hlift : ∀ (f : Fin r → ℕ) (k : Fin r) (x : W.DD T), q ^ f k • x ∈ W.N T →
      e ^ (∑ m, f m) • x ∈ W.N T := by
    intro f k x hx
    have h1 := (W.N T).smul_mem (w ^ (∑ m, f m) * q ^ (∑ m, f m - f k)) hx
    rwa [smul_smul, mul_assoc, ← pow_add,
      Nat.sub_add_cancel (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)),
      ← mul_pow, ← hqe] at h1
  choose nφ hnφ using fun k => W.N_φ T _ (hbN k)
  have hyN : ∀ k, e ^ (∑ m, nφ m) • W.φD T (b k) ∈ W.N T := fun k =>
    hlift nφ k _ (by rw [← hpow]; exact hnφ k)
  set M := ∑ m, nφ m with hM
  choose C hC using fun k => _root_.GlobalTheory.WachTie.MatF.exists_coord W T b _ (hyN k)
  have hCinv : ∀ k m, ∀ δ ∈ W.DelF, W.γA δ (C k m) = C k m := by
    intro k m δ hδ
    have h := congrArg (W.γD T δ) (hC k)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [_root_.GlobalTheory.WachTie.MatF.γD_smulA, map_pow, hγe δ hδ, ← W.φγ_comm, hbΔ k δ hδ, hC k, map_sum] at h
    simp only [_root_.GlobalTheory.WachTie.MatF.γD_smulA, hbΔ _ δ hδ] at h
    exact congrFun (_root_.GlobalTheory.WachTie.MatF.coord_unique W T b _ _ h.symm) m

  choose kk hkk using fun m => W.N_φinv T _ (hbN m)
  have hspan : Submodule.span (_root_.Formalism.BasicNotions.LetA O n) (W.φD T '' W.N T) ≤
      Submodule.span (_root_.Formalism.BasicNotions.LetA O n) (Set.range fun t => W.φD T (b t)) := by
    rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨c, rfl⟩ := _root_.GlobalTheory.WachTie.MatF.exists_coord W T b y hy
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Submodule.sum_mem _ fun t _ => ?_
    rw [_root_.GlobalTheory.WachTie.MatF.φD_smulA]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)
  have hA : ∀ m, ∃ a : Fin r → _root_.Formalism.BasicNotions.LetA O n,
      ∑ t, a t • W.φD T (b t) = e ^ (∑ m', kk m') • (b m : W.DD T) := by
    intro m
    rw [← Submodule.mem_span_range_iff_exists_fun]
    apply hspan
    have h1 := (Submodule.span (_root_.Formalism.BasicNotions.LetA O n) (W.φD T '' W.N T)).smul_mem
      (w ^ (∑ m', kk m') * q ^ (∑ m', kk m' - kk m)) (hkk m)
    rw [hpow] at h1
    rwa [smul_smul, mul_assoc, ← pow_add,
      Nat.sub_add_cancel (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ m)),
      ← mul_pow, ← hqe] at h1
  choose a ha using hA
  set K := ∑ m', kk m' with hK
  set c := e ^ (M + K) with hc
  set P : Matrix (Fin r) (Fin r) (_root_.Formalism.BasicNotions.LetA O n) := Matrix.of fun m k => C k m with hP
  set A : Matrix (Fin r) (Fin r) (_root_.Formalism.BasicNotions.LetA O n) := Matrix.of fun t m => a m t with hAdef
  have hPA : P * A = c • 1 := by
    refine Matrix.ext fun m' m => ?_
    have h : ∑ m'', (∑ t, a m t * C t m'') • (b m'' : W.DD T) =
        ∑ m'', (Pi.single m c : Fin r → _root_.Formalism.BasicNotions.LetA O n) m'' • (b m'' : W.DD T) := by
      simp only [Pi.single_apply, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [hc, pow_add, mul_smul, ← ha m, Finset.smul_sum]
      simp_rw [smul_comm (e ^ M) (a m _), hC, Finset.smul_sum, smul_smul, Finset.sum_smul]
      exact Finset.sum_comm
    have h2 := congrFun (_root_.GlobalTheory.WachTie.MatF.coord_unique W T b _ _ h) m'
    simp only [Matrix.mul_apply, hP, hAdef, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul]
    rw [Finset.sum_congr rfl fun t _ => mul_comm _ _, h2, Pi.single_apply]
    split_ifs <;> simp

  have hγP : ∀ δ ∈ W.DelF, P.map (W.γA δ) = P := by
    intro δ hδ
    refine Matrix.ext fun m k => ?_
    exact hCinv k m δ hδ
  have hγc : ∀ δ ∈ W.DelF, W.γA δ c = c := by
    intro δ hδ
    rw [hc, map_pow, hγe δ hδ]
  have hdet : P.det * A.det = c ^ r := by
    rw [← Matrix.det_mul, hPA, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  have hγdetP : ∀ δ ∈ W.DelF, W.γA δ P.det = P.det := by
    intro δ hδ
    have h := RingHom.map_det (W.γA δ : _root_.Formalism.BasicNotions.LetA O n →+* _root_.Formalism.BasicNotions.LetA O n) P
    rw [show (W.γA δ : _root_.Formalism.BasicNotions.LetA O n →+* _root_.Formalism.BasicNotions.LetA O n).mapMatrix P = P from hγP δ hδ] at h
    exact h
  have hγadj : ∀ δ ∈ W.DelF, ∀ x y, W.γA δ (P.adjugate x y) = P.adjugate x y := by
    intro δ hδ x y
    have h := RingHom.map_adjugate (W.γA δ : _root_.Formalism.BasicNotions.LetA O n →+* _root_.Formalism.BasicNotions.LetA O n) P
    rw [show (W.γA δ : _root_.Formalism.BasicNotions.LetA O n →+* _root_.Formalism.BasicNotions.LetA O n).mapMatrix P = P from hγP δ hδ] at h
    exact congrFun (congrFun h x) y
  set v := c ^ r * A.det with hv
  have hγv : ∀ δ ∈ W.DelF, W.γA δ v = v := by
    intro δ hδ
    have h1 : P.det * W.γA δ A.det = P.det * A.det := by
      rw [hdet, ← hγdetP δ hδ, ← map_mul, hdet, map_pow, hγc δ hδ]
    rw [hv, map_mul, map_pow, hγc δ hδ]
    calc c ^ r * W.γA δ A.det = A.det * (P.det * W.γA δ A.det) := by rw [← hdet]; ring
      _ = c ^ r * A.det := by rw [h1, ← hdet]; ring
  set Ψf := v • P.adjugate with hΨf
  have hPΨ : P * Ψf = c ^ (r + r) • 1 := by
    rw [hΨf, Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, pow_add, hv, ← hdet]
    congr 1
    ring
  have hγΨ : ∀ δ ∈ W.DelF, ∀ x y, W.γA δ (Ψf x y) = Ψf x y := by
    intro δ hδ x y
    rw [hΨf, Matrix.smul_apply, smul_eq_mul, map_mul, hγv δ hδ, hγadj δ hδ]
  have hjP : ∀ i m k, j (Function.invFun j (P m k i)) = P m k i := fun i m k =>
    hinv _ fun δ hδ => congrFun (hCinv k m δ hδ) i
  have hjΨ : ∀ i x y, j (Function.invFun j (Ψf x y i)) = Ψf x y i := fun i x y =>
    hinv _ fun δ hδ => congrFun (hγΨ δ hδ x y) i
  refine ⟨M, fun i => Matrix.of fun m k => Function.invFun j (P m k i), fun i =>
    ⟨(M + K) * (r + r), Matrix.of fun x y => Function.invFun j (Ψf x y i), ?_⟩, fun k => ?_⟩
  · refine Matrix.ext fun x y => ?_
    apply hj
    have h := congrFun (congrFun (congrFun hPΨ x) y) i
    simp only [Matrix.mul_apply, Finset.sum_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul, Pi.mul_apply] at h
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, Matrix.of_apply, map_sum, map_mul, hjP, hjΨ, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul]
    rw [h]
    split_ifs <;> simp [hc, he, pow_mul]
  · rw [hC k]
    refine Finset.sum_congr rfl fun m _ => ?_
    congr 1
    funext i
    exact (hjP i m k).symm

end GlobalTheory.WachTie.MatF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetTracePowAddMulUnitNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetTracePowAddMulUnitNeZero
open GlobalTheory.UnitLemma Matrix MeasureTheory

namespace GlobalTheory.UnitLemma.TraceDet

theorem det_trace_pow_mul_ne_zero : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → ∀ u : B.A, IsUnit u →
    (Matrix.of fun k l : Fin (Module.finrank K.E B.A) =>
      Algebra.trace K.E B.A (B.g ^ ((k : ℕ) + (l : ℕ)) * u)).det ≠ 0 := by
  intro K B hsep u hu hdet
  classical
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_power_basis_of_charpoly_separable K B hsep
  obtain ⟨v, hv0, hv⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 hdet
  set w : B.A := ∑ l, v l • e l with hw
  have hk : ∀ k, Algebra.trace K.E B.A ((w * u) * e k) = 0 := by
    intro k
    have := congrFun hv k
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at this
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← this, hw, Finset.sum_mul, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_mul_assoc, smul_mul_assoc, map_smul, smul_eq_mul, he, he, pow_add]
    rw [mul_comm (v l)]
    congr 1
    congr 1
    ring
  have hz : w * u = 0 := by
    apply GlobalTheory.UnitLemma.Centraliser.eq_zero_of_trace_mul B hsep
    intro y
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← e.sum_repr y, Finset.mul_sum, map_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [mul_smul_comm, map_smul, hk k, smul_zero]
  have hw0 : w = 0 := (hu.mul_left_eq_zero).1 hz
  apply hv0
  exact (Fintype.linearIndependent_iff.1 e.linearIndependent) v hw0 |> funext

end GlobalTheory.UnitLemma.TraceDet
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetTracePowAddMulUnitNeZeroStatement
open GlobalTheory.UnitLemma Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_trace_pow_add_mul_unit_ne_zero : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → ∀ u : B.A, IsUnit u → (Matrix.of fun k l : Fin (Module.finrank K.E B.A) => Algebra.trace K.E B.A (B.g ^ ((k : ℕ) + (l : ℕ)) * u)).det ≠ 0 := by
  first | exact @GlobalTheory.UnitLemma.TraceDet.det_trace_pow_mul_ne_zero | exact GlobalTheory.UnitLemma.TraceDet.det_trace_pow_mul_ne_zero | (intros; apply GlobalTheory.UnitLemma.TraceDet.det_trace_pow_mul_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuadraticWeilFourierCompSmul
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuadraticWeilFourierCompSmul
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
open scoped NNReal

noncomputable section

namespace GlobalTheory.JR.WeilQuad

theorem fOp_comp_smul : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ),
    Hyp A ψ x μ ω → ∀ (s : A.Kˣ) (φ : A.L → ℂ), IsTest φ → ∀ y,
      fOp A ψ x μ (fun y' => φ ((s : A.K) • y')) y =
        ((A.absK s : ℂ) ^ 2)⁻¹ * fOp A ψ x μ φ (((s⁻¹ : A.Kˣ) : A.K) • y) := by
  intro F E _ _ _ _ U A ψ x μ ω hH s φ _ y
  have := U.charZero; have := U.ultraF; have := U.lcF
  have := EtMeas.finite_L A
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.L
  have : IsTopologicalRing A.L := IsModuleTopology.isTopologicalRing F A.L
  have hN : distribHaarChar A.L (MeasScale.unitL A s) = distribHaarChar A.K s ^ 2 := by
    obtain ⟨⟨b⟩, -, -, -, -⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
    obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.K
    have : ContinuousStar A.L := ⟨IsModuleTopology.continuous_of_linearMap (EtMeas.starF A)⟩
    rw [← map_pow]
    refine GlobalTheory.JR.ModuleNorm.distribHaarChar_eq_norm A.K A.L b.equivFun.symm
        (IsModuleTopology.continuous_of_linearMap (b.equivFun.symm.toLinearMap.restrictScalars F))
        (IsModuleTopology.continuous_of_linearMap (b.equivFun.toLinearMap.restrictScalars F)) _ _ ?_
    simp [MeasScale.unitL, A.star_K, pow_two]
  have hμ : μ.IsAddHaarMeasure := hH.2.2.2.1.1
  have hinv : algebraMap A.K A.L (s : A.K) * algebraMap A.K A.L ((s⁻¹ : A.Kˣ) : A.K) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have key : ∀ y', φ ((s : A.K) • y') * A.kerL ψ x y' y =
      (fun u => φ u * A.kerL ψ x u (((s⁻¹ : A.Kˣ) : A.K) • y)) (MeasScale.unitL A s • y') := by
    intro y'
    simp only [MeasScale.unitL_smul, Et.kerL]
    rw [Algebra.smul_def, Algebra.smul_def, star_mul', A.star_K]
    congr 4
    linear_combination (star y' * y) * hinv.symm
  simp only [fOp, fourB]
  rw [integral_congr_ae (Eventually.of_forall key),
    MeasScale.integral_units_smul μ (MeasScale.unitL A s)
      (fun u => φ u * A.kerL ψ x u (((s⁻¹ : A.Kˣ) : A.K) • y)), hN, EtMeas.absK_unit]
  push_cast
  rfl

end GlobalTheory.JR.WeilQuad
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuadraticWeilFourierCompSmulStatement
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadraticWeilFourier_comp_smul : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ (s : A.Kˣ) (φ : A.L → ℂ), IsTest φ → ∀ y, fOp A ψ x μ (fun y' => φ ((s : A.K) • y')) y = ((A.absK s : ℂ) ^ 2)⁻¹ * fOp A ψ x μ φ (((s⁻¹ : A.Kˣ) : A.K) • y) := by
  first | exact @GlobalTheory.JR.WeilQuad.fOp_comp_smul | exact GlobalTheory.JR.WeilQuad.fOp_comp_smul | (intros; apply GlobalTheory.JR.WeilQuad.fOp_comp_smul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMatrixGamma
open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.NB GlobalTheory.CycFr GlobalTheory.WachTie

noncomputable section

namespace GlobalTheory.WachTie

theorem exists_matrix_gamma : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n) {l : ℕ} (R : Fr l O) (j : O⟦X⟧ →ₐ[O] O⟦X⟧) (jE : (ZMod n → R.EE) →ₐ[O] W.EE) (T : LocLat G Qp LL O) {r : ℕ} (b : Module.Basis (Fin r) (LetA O n) ↥(W.N T)), FrTie W R j → EETie W R j jE → (∀ k, (b k : W.DD T) ∈ W.NΔ T) → ∃ Gm : ZMod n → Matrix (Fin r) (Fin r) O⟦X⟧, (∀ i, ∃ B : Matrix (Fin r) (Fin r) O⟦X⟧, Gm i = 1 + (X : O⟦X⟧) • B) ∧ (∀ k, W.γD T W.gam (b k : W.DD T) = ∑ m, (fun i => j (Gm i m k) : LetA O n) • (b m : W.DD T)) := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL O _ _ _ _ _ v n W l R j jE T r b
    hF _ hb
  classical
  obtain ⟨-, hinv, -, -, -, hs, hX, -⟩ := hF
  have hsm : ∀ (g : W.Gam) (a : LetA O n) (x : W.DD T),
      W.γD T g (a • x) = letγ (W.γ₀ g) a • W.γD T g x := fun g a x => by
    have := W.γD_smul T g (algebraMap (LetA O n) W.EE a) x
    rw [algebraMap_smul, W.γE_ext, algebraMap_smul] at this
    exact this
  have hXj : (X : O⟦X⟧) ∣ j X := by
    have h1 : (1 : W.Gam) ∈ W.DelF := (W.DelF_def 1).2 ⟨1, one_pos, one_pow _⟩
    have h2 : R.s ≠ 0 := by rw [hs]; exact (Finset.card_pos.2 ⟨1, h1⟩).ne'
    exact (dvd_pow_self _ h2).trans hX.symm.dvd
  let z : Fin r → ↥(W.N T) := fun k => ⟨W.γD T W.gam (b k : W.DD T), W.N_Γ T _ _ (b k).2⟩
  have hexp : ∀ y : ↥(W.N T), (y : W.DD T) = ∑ m, b.repr y m • (b m : W.DD T) := fun y => by
    conv_lhs => rw [← b.sum_repr y]
    simp only [Submodule.coe_sum, Submodule.coe_smul]
  have hc : ∀ k m i, ∃ c, j c = b.repr (z k) m i := by
    intro k m i
    refine (hinv _).2 fun δ hδ => ?_
    have h1 : W.γD T δ (z k : W.DD T) = z k := by
      change W.γD T δ (W.γD T W.gam (b k : W.DD T)) = W.γD T W.gam (b k : W.DD T)
      rw [← W.γD_mul, mul_comm, W.γD_mul, (hb k).2 δ hδ]
    have h2 : z k = ∑ m, letγ (W.γ₀ δ) (b.repr (z k) m) • b m := by
      apply Subtype.ext
      rw [← h1]
      conv_lhs => rw [hexp (z k)]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, hsm, Submodule.coe_sum, Submodule.coe_smul]
      exact Finset.sum_congr rfl fun m _ => by rw [(hb m).2 δ hδ]
    have h3 : b.repr (z k) m = letγ (W.γ₀ δ) (b.repr (z k) m) := by
      conv_lhs => rw [h2]
      rw [b.repr_sum_self]
    exact (congrFun h3 i).symm
  choose c hc using hc
  refine ⟨fun i => Matrix.of fun m k => c k m i, fun i => ?_, fun k => ?_⟩
  · have hd : ∀ m k, (X : O⟦X⟧) ∣ c k m i - (1 : Matrix (Fin r) (Fin r) O⟦X⟧) m k := by
      intro m k
      obtain ⟨y, hy, hy'⟩ := W.N_π T W.gam _ (b k).2
      have h1 : z k - b k = (letπ : LetA O n) • (⟨y, hy⟩ : ↥(W.N T)) := Subtype.ext hy'
      have h2 := congrArg (fun w => b.repr w m i) h1
      simp only [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, Pi.sub_apply,
        smul_eq_mul, Pi.mul_apply, b.repr_self, letπ] at h2
      rw [X_dvd_iff, ← constantCoeff_algHom j hXj, ← X_dvd_iff, map_sub, hc]
      have h3 : j ((1 : Matrix (Fin r) (Fin r) O⟦X⟧) m k) =
          (Finsupp.single k (1 : LetA O n) : Fin r →₀ LetA O n) m i := by
        by_cases h : m = k
        · subst h; simp
        · rw [Matrix.one_apply_ne h, Finsupp.single_eq_of_ne h]; simp
      rw [h3, h2]
      exact dvd_mul_right _ _
    choose d hd using hd
    refine ⟨Matrix.of d, ?_⟩
    ext1 m k
    simp only [Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rw [← hd]; ring
  · simp only [Matrix.of_apply, hc]
    exact hexp (z k)

end GlobalTheory.WachTie
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumMulVecSmul
noncomputable section

open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.NB GlobalTheory.CycFr GlobalTheory.WachTie

namespace GlobalTheory.WachTie

theorem sum_mulVec_smul {ι E EE D O : Type} [CommRing O] [CommRing E] [CommRing EE] [Algebra O E]
    [Algebra O EE] [AddCommGroup D] [Module EE D] (jE : (ι → E) →ₐ[O] EE) {r : ℕ} (b : Fin r → D)
    (A : ι → Matrix (Fin r) (Fin r) E) (y : ι → Fin r → E) :
    ∑ m, jE (fun i => (A i).mulVec (y i) m) • b m =
      ∑ k, jE (fun i => y i k) • ∑ m, jE (fun i => A i m k) • b m := by
  have h : ∀ m, (fun i => (A i).mulVec (y i) m) =
      ∑ k, ((fun i => y i k) * (fun i => A i m k) : ι → E) := by
    intro m
    funext i
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [h, map_sum, map_mul, Finset.sum_smul, Finset.smul_sum, mul_smul]
  exact Finset.sum_comm

theorem isUnit_ι_E {l : ℕ} {O : Type} [CommRing O] (R : Fr l O) : IsUnit (R.ι R.E) := by
  have hs : R.s ≠ 0 := by
    intro h
    have h1 := R.es
    have h2 := R.prime.two_le
    rw [h] at h1
    omega
  have h := R.EE_X.map R.φE
  rw [R.φE_ext, R.φ_X, map_mul, map_pow] at h
  exact (isUnit_pow_iff hs).1 (isUnit_of_mul_isUnit_right h)

theorem coord_comm_φ_γ : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n) {l : ℕ} (R : Fr l O) (j : O⟦X⟧ →ₐ[O] O⟦X⟧) (jE : (ZMod n → R.EE) →ₐ[O] W.EE) (T : LocLat G Qp LL O) {r : ℕ} (b : Module.Basis (Fin r) (LetA O n) ↥(W.N T)), FrTie W R j → EETie W R j jE → (∀ k, (b k : W.DD T) ∈ W.NΔ T) → ∀ S : Sys R n r, (∀ k, W.γD T W.gam (b k : W.DD T) = ∑ m, (fun i => j (S.G i m k) : LetA O n) • (b m : W.DD T)) → (∀ k, (fun _ => j R.E : LetA O n) ^ S.M • W.φD T (b k : W.DD T) = ∑ m, (fun i => j (S.Φ i m k) : LetA O n) • (b m : W.DD T)) → (∀ x, coord W R jE T (fun k => (b k : W.DD T)) (S.φD x) = W.φD T (coord W R jE T (fun k => (b k : W.DD T)) x)) ∧ ∀ x, coord W R jE T (fun k => (b k : W.DD T)) (S.γD x) = W.γD T W.gam (coord W R jE T (fun k => (b k : W.DD T)) x) := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL O _ _ _ _ _ v n W l R j jE T r b
    _ hE _ S hγ hφ
  obtain ⟨hext, -, -, hφE, hγE⟩ := hE
  refine ⟨fun x => ?_, fun x => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [coord_apply, coord_apply, map_sum]
      refine (sum_mulVec_smul jE (fun k => (b k : W.DD T))
        (fun i => Ring.inverse (R.ι R.E) ^ S.M • (S.Φ i).map R.ι)
        (fun i k => R.φE (x (i - 1) k))).trans ?_
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [W.φD_smul, ← hφE]
      congr 1
      have h1 : ∀ m, jE (fun i => (Ring.inverse (R.ι R.E) ^ S.M • (S.Φ i).map R.ι) m k) =
          jE (fun _ => Ring.inverse (R.ι R.E)) ^ S.M *
            algebraMap (LetA O n) W.EE (fun i => j (S.Φ i m k)) := by
        intro m
        rw [← hext, ← map_pow, ← map_mul]
        rfl
      have h2 : jE (fun _ => Ring.inverse (R.ι R.E)) *
          algebraMap (LetA O n) W.EE (fun _ => j R.E) = 1 := by
        rw [← hext (fun _ => R.E), ← map_mul, ← map_one jE]
        congr 1
        funext i
        exact Ring.inverse_mul_cancel _ (isUnit_ι_E R)
      simp only [h1, mul_smul, algebraMap_smul]
      rw [← Finset.smul_sum, ← hφ, ← algebraMap_smul W.EE ((fun _ => j R.E : LetA O n) ^ S.M),
        smul_smul, map_pow, ← mul_pow, h2, one_pow,
        one_smul]
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [coord_apply, coord_apply, map_sum]
      refine (sum_mulVec_smul jE (fun k => (b k : W.DD T))
        (fun i => (S.G i).map R.ι) (fun i k => R.γE (x i k))).trans ?_
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [W.γD_smul, ← hγE, hγ]
      congr 1
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [← algebraMap_smul W.EE (fun i => j (S.G i m k) : LetA O n), ← hext]
      rfl

end GlobalTheory.WachTie
end
end
