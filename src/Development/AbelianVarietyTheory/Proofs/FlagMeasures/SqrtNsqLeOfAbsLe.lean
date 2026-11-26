module

public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.CenteredPerpendicularSets

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RhoNNormLeAndCasimirArith
open Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants

namespace GlobalTheory

theorem rpow_three_halves_sq_eq_cube {x : ℝ} (hx : 0 ≤ x) : (x ^ ((3 : ℝ) / 2)) ^ 2 = x ^ 3 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

theorem rhoN_norm_le_and_casimir_arith :
    (∀ (n : ℕ) (ε : Fin n → Bool), Real.sqrt (nsq (rhoN ε)) ≤ 0.58 * (n : ℝ) ^ ((3 : ℝ) / 2)) ∧
    ∀ (L a n : ℝ), 0 ≤ L → 0 ≤ a → 0 ≤ n →
      2 * (L + a) ^ 2 - L ^ 2 + n ^ 3 / 12 ≤ (L + 2 * a + 0.3 * n ^ ((3 : ℝ) / 2)) ^ 2 := by
  refine ⟨fun n ε => ?_, fun L a n hL ha hn => ?_⟩
  · have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hs := rpow_three_halves_sq_eq_cube hn
    have hp : 0 ≤ (n : ℝ) ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hn _
    have h1 : nsq (rhoN ε) ≤ (n : ℝ) * ((n : ℝ) / 2) ^ 2 := by
      have : ∑ a : Fin n, (rhoN ε a) ^ 2 ≤ ∑ _a : Fin n, ((n : ℝ) / 2) ^ 2 := by
        refine Finset.sum_le_sum fun a _ => ?_
        obtain ⟨h1, h2⟩ := rho_rhoN_bound ε a
        exact sq_le_sq' h1 h2
      simpa [nsq, dot, sq] using this
    refine Real.sqrt_le_iff.mpr ⟨by positivity, h1.trans ?_⟩
    rw [mul_pow, hs]
    have : (0 : ℝ) ≤ (n : ℝ) ^ 3 := by positivity
    nlinarith
  · have hs := rpow_three_halves_sq_eq_cube hn
    have hp : 0 ≤ n ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hn _
    generalize n ^ ((3 : ℝ) / 2) = s at hs hp
    rw [← hs]
    nlinarith [mul_nonneg hL hp, mul_nonneg ha hp, sq_nonneg a, sq_nonneg s]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.KtypesWithinSteps
open Formalism.REAL
open scoped InnerProductSpace

namespace GlobalTheory.KTypeSteps

theorem sqrt_nsq_eq {n : ℕ} (v : Fin n → ℝ) :
    Real.sqrt (nsq v) = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖ := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  simp [nsq, dot, sq]

theorem sqrt_nsq_add_le {n : ℕ} (v w : Fin n → ℝ) :
    Real.sqrt (nsq (v + w)) ≤ Real.sqrt (nsq v) + Real.sqrt (nsq w) := by
  rw [sqrt_nsq_eq, sqrt_nsq_eq, sqrt_nsq_eq, WithLp.toLp_add]
  exact norm_add_le _ _

theorem nsq_root {n : ℕ} {a b : Fin n} (hab : a ≠ b) : nsq (root a b) = 2 := by
  have h : ∀ c, root a b c * root a b c =
      (if c = a then (1 : ℝ) else 0) + (if c = b then (1 : ℝ) else 0) := by
    intro c
    by_cases h1 : c = a
    · subst h1
      simp [root, hab]
    · by_cases h2 : c = b
      · subst h2
        simp [root, h1]
      · simp [root, h1, h2]
  simp only [nsq, dot, h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  norm_num

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}

theorem kSpan_le_ker {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V}
    (hg : GlRel E) (hu : IsUnitary ε E) {μ ν : Fin n → ℝ} {x y : V}
    (hx : KHighest ε E μ x) (hy : KHighest ε E ν y) (hne : μ ≠ ν) :
    kSpan ε E y ≤ LinearMap.ker (innerₛₗ ℂ x) := by
  intro z hz
  rw [LinearMap.mem_ker, innerₛₗ_apply_apply]
  exact kOrth V n ε E μ ν x y (glRel_kRel ε E hg) (isUnitary_kUnit ε E hu) hx hy hne x
    (mem_compact_span_self_general x) z hz

theorem pfil_one_le_ker {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V}
    (hg : GlRel E) (hu : IsUnitary ε E) {μ ν : Fin n → ℝ} {x y : V}
    (hx : KHighest ε E μ x) (hy : KHighest ε E ν y) (hfd : FiniteDimensional ℂ (kSpan ε E y))
    (hne : μ ≠ ν) (hne' : ∀ a b, ε a ≠ ε b → μ ≠ ν + root a b) :
    pfil ε E y 1 ≤ LinearMap.ker (innerₛₗ ℂ x) := by
  refine le_trans ((thetaFil V n ε E y hg).2.1 0) (sup_le ?_ ?_)
  · obtain ⟨hA, hθ⟩ := (arrModule V n ε E 1).1 hg
    have hKU := (arrModule V n ε E 1).2 hu
    have := noncompact_arr_finite_dimensional (j := 1) hfd
    obtain ⟨m, F, lam, hF, -, hsup⟩ := kDecomp (Arr V n 1) n ε (arrE E 1) (arrV0 ε E y 1)
      inferInstance (glRel_kRel ε _ hA) hKU noncompact_arr_one_compact_stable
    change (arrV0 ε E y 1).map (thetaA E 1) ≤ _
    rw [← hsup, Submodule.map_le_iff_le_comap]
    refine iSup_le fun i => ?_
    obtain ⟨hmem, h0, hhi⟩ := hF i
    obtain ⟨a, b, hab, hlam⟩ := hVCoeff V n ε E ν (lam i) y (F i) hg hu hy hmem hhi h0
    have hθhi : KHighest ε E (lam i) (thetaA E 1 (F i)) := by
      refine ⟨fun c => ?_, fun c d hcd he => ?_⟩
      · rw [← hθ, hhi.1 c, map_smul]
      · rw [← hθ, hhi.2 c d hcd he, map_zero]
    have hle : kSpan ε (arrE E 1) (F i) ≤ (kSpan ε E (thetaA E 1 (F i))).comap (thetaA E 1) := by
      refine compact_span_le_of_stable ?_ (mem_compact_span_self_general _)
      intro c d hcd G hG
      rw [Submodule.mem_comap] at hG ⊢
      rw [hθ]
      exact compact_span_stable_general _ c d hcd _ hG
    exact hle.trans (Submodule.comap_mono
      (kSpan_le_ker hg hu hx hθhi (hlam ▸ hne' a b hab)))
  · rw [(pfilFacts V n ε E y hg).1]
    exact kSpan_le_ker hg hu hx hy hne

theorem ew_mem_pfil {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V} {u : V} {j : ℕ}
    {w : List (Fin n × Fin n)} (hw : w.length ≤ j) (hp : ∀ p ∈ w, ε p.1 ≠ ε p.2) {y : V}
    (hy : y ∈ kSpan ε E u) : ew E w y ∈ pfil ε E u j :=
  Submodule.subset_span ⟨w, hw, hp, y, hy, rfl⟩

theorem ktypes_within_steps :
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
      (E : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ) (u : V), GlRel E → IsUnitary ε E →
      KHighest ε E Λ u → FiniteDimensional ℂ (kSpan ε E u) →
      ∀ (j : ℕ) (μ : Fin n → ℝ), ∀ x ∈ pfil ε E u j, x ≠ 0 → KHighest ε E μ x →
        Real.sqrt (nsq (μ - Λ)) ≤ Real.sqrt 2 * j := by
  intro V _ _ n ε E Λ u hg hu hΛ hfd j
  obtain ⟨h0, -, hst, -, -, -, hfin⟩ := pfilFacts V n ε E u hg
  induction j with
  | zero =>
    intro μ x hx hx0 hhi
    rw [h0] at hx
    have := compact_highest_weight_unique kLow kWtOrth hg hu hΛ hx hhi hx0
    subst this
    simp [nsq, dot]
  | succ j ih =>
    intro μ x hx hx0 hhi
    by_contra hlt
    rw [not_le] at hlt
    push_cast at hlt
    have hs2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    have := hfin hfd j
    obtain ⟨m, y, lam, hy, -, hsup⟩ := kDecomp V n ε E (pfil ε E u j) inferInstance
      (glRel_kRel ε E hg) (isUnitary_kUnit ε E hu) (hst j)
    have hone : ∀ i, pfil ε E (y i) 1 ≤ LinearMap.ker (innerₛₗ ℂ x) := by
      intro i
      obtain ⟨hmem, hy0, hyh⟩ := hy i
      have hb := ih (lam i) (y i) hmem hy0 hyh
      refine pfil_one_le_ker hg hu hhi hyh
        (Submodule.finiteDimensional_of_le (compact_span_le_of_stable (hst j) hmem)) ?_ ?_
      · intro h
        rw [h] at hlt
        nlinarith
      · intro a b hab h
        have hab' : a ≠ b := fun h => hab (h ▸ rfl)
        have ht := sqrt_nsq_add_le (lam i - Λ) (root a b)
        rw [nsq_root hab'] at ht
        have he : μ - Λ = lam i - Λ + root a b := by rw [h]; abel
        rw [he] at hlt
        nlinarith
    have hA : pfil ε E u j ≤ LinearMap.ker (innerₛₗ ℂ x) := by
      rw [← hsup]
      refine iSup_le fun i => le_trans ?_ (hone i)
      obtain ⟨g0, g1, -⟩ := pfilFacts V n ε E (y i) hg
      rw [← g0]
      exact g1 0
    have hB : ∀ a b, pfil ε E u j ≤ (LinearMap.ker (innerₛₗ ℂ x)).comap (E a b) := by
      intro a b
      rw [← hsup]
      refine iSup_le fun i z hz => hone i ?_
      obtain ⟨g0, -, -, g3, -⟩ := pfilFacts V n ε E (y i) hg
      rw [← g0] at hz
      exact g3 0 a b z hz
    have hC : pfil ε E u (j + 1) ≤ LinearMap.ker (innerₛₗ ℂ x) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨w, hw, hp, z, hz, rfl⟩
      cases w with
      | nil => exact hA (ew_mem_pfil (Nat.zero_le j) hp hz)
      | cons p w =>
        have hw' : w.length ≤ j := by simpa using hw
        exact hB p.1 p.2 (ew_mem_pfil hw' (fun q hq => hp q (List.mem_cons_of_mem _ hq)) hz)
    have := hC hx
    rw [LinearMap.mem_ker, innerₛₗ_apply_apply] at this
    exact hx0 (inner_self_eq_zero.mp this)

end GlobalTheory.KTypeSteps
end

open Formalism.REAL Finset
open scoped InnerProductSpace

namespace GlobalTheory.AlgStep

theorem sqrt_nsq_eq_norm {n : ℕ} (u : Fin n → ℝ) :
    Real.sqrt (nsq u) = ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ := by
  rw [EuclideanSpace.norm_eq]
  simp [nsq, dot, sq]

theorem sqrt_nsq_add_le {n : ℕ} (u v : Fin n → ℝ) :
    Real.sqrt (nsq (u + v)) ≤ Real.sqrt (nsq u) + Real.sqrt (nsq v) := by
  simp only [sqrt_nsq_eq_norm, WithLp.toLp_add]
  exact norm_add_le _ _

theorem nsq_nonneg' {n : ℕ} (u : Fin n → ℝ) : 0 ≤ nsq u := by
  unfold nsq dot
  exact Finset.sum_nonneg fun a _ => mul_self_nonneg (u a)

theorem sum_range_sub_sq (c : ℝ) (n : ℕ) :
    ∑ i ∈ range n, (c - (i : ℝ)) * (c - (i : ℝ)) =
      n * c ^ 2 - c * n * (n - 1) + (n - 1) * n * (2 * n - 1) / 6 := by
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

theorem nsq_rho_le {n : ℕ} (ε : Fin n → Bool) : nsq (rhoC ε + rhoN ε) ≤ (n : ℝ) ^ 3 / 12 := by
  have h : nsq (rhoC ε + rhoN ε) =
      ∑ i ∈ range n, (((n : ℝ) - 1) / 2 - (i : ℝ)) * (((n : ℝ) - 1) / 2 - (i : ℝ)) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i : ℕ => (((n : ℝ) - 1) / 2 - (i : ℝ)) * (((n : ℝ) - 1) / 2 - (i : ℝ)))]
    unfold nsq dot
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Pi.add_apply, half_sum_roots_standard n ε a]
  rw [h, sum_range_sub_sq]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

theorem casK_form_le (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (F : Fin n → Fin n → Module.End ℂ V) (S : Submodule ℂ V) (M : ℝ) (hfin : FiniteDimensional ℂ S)
    (hr : KRel ε F) (hu : KUnit ε F) (hS : KStable ε F S)
    (hw : ∀ (μ : Fin n → ℝ), ∀ x ∈ S, x ≠ 0 → KHighest ε F μ x → ckv ε μ ≤ M) :
    ∀ y ∈ S, (⟪y, CasK ε F y⟫_ℂ).re ≤ M * ‖y‖ ^ 2 := by
  intro y hy
  obtain ⟨m, x, μ, h1, h2, h3⟩ := kDecomp V n ε F S hfin hr hu hS
  have hy' : y ∈ ⨆ i ∈ (univ : Finset (Fin m)), kSpan ε F (x i) := by simpa [h3] using hy
  obtain ⟨v, hv⟩ := (Submodule.mem_iSup_finset_iff_exists_sum _ y).1 hy'
  have hC : CasK ε F y = ∑ i, ((ckv ε (μ i) : ℝ) : ℂ) • (v i : V) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hv, map_sum]
    exact Finset.sum_congr rfl fun i _ => kCasSpan V n ε F (μ i) (x i) hr (h1 i).2.2 _ (v i).2
  have key : ∀ c : Fin m → ℂ,
      ⟪y, ∑ i, c i • (v i : V)⟫_ℂ = ∑ i, c i * ⟪(v i : V), (v i : V)⟫_ℂ := by
    intro c
    rw [← hv, sum_inner]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_sum, Finset.sum_eq_single j]
    · rw [inner_smul_right]
    · intro i _ hij
      rw [inner_smul_right, h2 j i (Ne.symm hij) _ (v j).2 _ (v i).2, mul_zero]
    · simp
  have hvv : ∀ i, ⟪(v i : V), (v i : V)⟫_ℂ = ((‖(v i : V)‖ ^ 2 : ℝ) : ℂ) := fun i => by
    rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
  have hn : ‖y‖ ^ 2 = ∑ i, ‖(v i : V)‖ ^ 2 := by
    have h := key (fun _ => 1)
    simp only [one_smul, one_mul, hv, inner_self_eq_norm_sq_to_K] at h
    apply Complex.ofReal_injective
    push_cast
    exact h
  have key2 := key (fun i => ((ckv ε (μ i) : ℝ) : ℂ))
  rw [hC, key2]
  simp only [hvv]
  have hre : (∑ i, ((ckv ε (μ i) : ℝ) : ℂ) * ((‖(v i : V)‖ ^ 2 : ℝ) : ℂ)).re =
      ∑ i, ckv ε (μ i) * ‖(v i : V)‖ ^ 2 := by
    simp only [← Complex.ofReal_mul, ← Complex.ofReal_sum, Complex.ofReal_re]
  rw [hre, hn, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact hw (μ i) (x i) (h1 i).1 (h1 i).2.1 (h1 i).2.2

theorem sqrt_nsq_le_of_abs_le {n : ℕ} (lam : Fin n → ℝ) (b : ℝ) (h : ∀ a, |lam a| ≤ b ^ 2) :
    Real.sqrt (nsq lam) ≤ (n : ℝ) ^ (1 / 2 : ℝ) * b ^ 2 := by
  have h1 : nsq lam ≤ (n : ℝ) * (b ^ 2) ^ 2 := by
    have : ∑ a : Fin n, lam a * lam a ≤ ∑ _a : Fin n, (b ^ 2) ^ 2 := by
      refine Finset.sum_le_sum fun a _ => ?_
      rw [← sq, ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (h a) 2
    simpa [nsq, dot] using this
  rw [← Real.sqrt_eq_rpow]
  refine (Real.sqrt_le_sqrt h1).trans (le_of_eq ?_)
  rw [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq (sq_nonneg b)]

end GlobalTheory.AlgStep

namespace GlobalTheory

open GlobalTheory.AlgStep

theorem algebraic_step_bound : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ)
    (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (lam : Fin n → ℝ) (u : V) (b : ℝ),
    GlRel E → IsUnitary ε E → KindA ε E lam u → (∀ a, |lam a| ≤ b ^ 2) →
    ∀ (j : ℕ), ∀ x ∈ pfil ε E u j,
      ∑ a, ∑ c, ‖E a c x‖ ^ 2 ≤ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst n b j ^ 2 * ‖x‖ ^ 2 := by
  intro V _ _ n ε E lam u b hg hu hk hb j x hx
  obtain ⟨hhi, hcas, hfin⟩ := hk
  obtain ⟨-, -, hst, -, hcyc, -, hfd⟩ := pfilFacts V n ε E u hg
  set L := Real.sqrt (nsq lam) with hL
  set A := Real.sqrt (nsq (rhoN ε)) + Real.sqrt 2 * j with hA
  have hL0 : 0 ≤ L := Real.sqrt_nonneg _
  have hA0 : 0 ≤ A := by positivity
  have hK := casK_form_le V n ε E (pfil ε E u j) ((L + A) ^ 2) (hfd hfin j) (glRel_kRel ε E hg)
    (isUnitary_kUnit ε E hu) (hst j) (by
      intro μ y hy hy0 hyh
      have h1 := GlobalTheory.KTypeSteps.ktypes_within_steps V n ε E (LamOf ε lam) u hg hu hhi hfin j μ y hy hy0 hyh
      have h2 : μ + rhoC ε = (lam + rhoN ε) + (μ - LamOf ε lam) := by
        unfold LamOf; ring
      have h3 : Real.sqrt (nsq (μ + rhoC ε)) ≤ L + A := by
        rw [h2]
        have := sqrt_nsq_add_le (lam + rhoN ε) (μ - LamOf ε lam)
        have := sqrt_nsq_add_le lam (rhoN ε)
        linarith
      have h4 := (Real.sqrt_le_iff.mp h3).2
      have h5 := nsq_nonneg' (rhoC ε)
      unfold ckv
      linarith) x hx
  have hC : Cas E x = ((cvalR ε lam : ℝ) : ℂ) • x := casOnCyc V n E _ u hg hcas x (hcyc j hx)
  have hS := congrArg Complex.re (sumOfSquaresIdentity_holds V n ε E x hu)
  have hxx : ⟪x, x⟫_ℂ = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
  rw [Complex.ofReal_re, LinearMap.sub_apply, two_smul, LinearMap.add_apply, hC, inner_sub_right,
    inner_add_right, inner_smul_right, hxx, ← Complex.ofReal_mul, Complex.sub_re, Complex.add_re,
    Complex.ofReal_re] at hS
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have har := rhoN_norm_le_and_casimir_arith.2 L A n hL0 hA0 hn
  have hr := rhoN_norm_le_and_casimir_arith.1 n ε
  have hp : 0 ≤ (n : ℝ) ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hn _
  have hLb := sqrt_nsq_le_of_abs_le lam b hb
  have h2 : Real.sqrt 2 ≤ 3 / 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hj : Real.sqrt 2 * j ≤ 3 / 2 * j := mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg j)
  have hle : L + 2 * A + 0.3 * (n : ℝ) ^ ((3 : ℝ) / 2) ≤ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst n b j := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst
    linarith
  have hsq : (L + 2 * A + 0.3 * (n : ℝ) ^ ((3 : ℝ) / 2)) ^ 2 ≤ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst n b j ^ 2 :=
    pow_le_pow_left₀ (by positivity) hle 2
  have hL2 : L ^ 2 = nsq lam := Real.sq_sqrt (nsq_nonneg' lam)
  have hrho := nsq_rho_le ε
  have hc : 2 * (L + A) ^ 2 - cvalR ε lam ≤ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst n b j ^ 2 := by
    unfold cvalR
    linarith
  have := mul_le_mul_of_nonneg_right hc (sq_nonneg ‖x‖)
  rw [hS]
  linarith

end GlobalTheory
