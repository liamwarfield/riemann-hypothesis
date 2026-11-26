module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PImplicitCurve
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRegularLocusDense
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PHolomorphicZeroSetDimH
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Metric Filter
open scoped ENNReal NNReal

noncomputable section

namespace HolomorphicZeroSetDimH

def partialDeriv {k : ℕ} (h : (Fin k → ℂ) → ℂ) (n : ℕ) (m : Fin n → Fin k) (v : Fin k → ℂ) : ℂ :=
  iteratedFDeriv ℂ n h v (fun j => Pi.basisFun ℂ (Fin k) (m j))

theorem dimH_le_of_local {X : Type*} [EMetricSpace X] [SecondCountableTopology X] {S : Set X}
    {c : ℝ≥0∞} (hS : ∀ x ∈ S, ∃ N ∈ 𝓝 x, dimH (S ∩ N) ≤ c) : dimH S ≤ c := by
  by_contra hlt
  obtain ⟨x, hx, hall⟩ := exists_mem_nhdsWithin_lt_dimH_of_lt_dimH (not_le.1 hlt)
  obtain ⟨N, hN, hc⟩ := hS x hx
  exact (not_le.2 (hall _ (inter_mem_nhdsWithin S hN))) hc

theorem dimH_image_le_of_analyticOnNhd {d : ℕ} {σ : Type*} [Fintype σ] {O : Set (Fin d → ℂ)}
    {g : (Fin d → ℂ) → σ → ℂ} (hg : AnalyticOnNhd ℂ g O) : dimH (g '' O) ≤ 2 * (d : ℝ≥0∞) := by
  refine (dimH_image_le_of_locally_lipschitzOn fun y hy => ?_).trans ?_
  · obtain ⟨K, t, ht, hK⟩ := ((hg y hy).contDiffAt (n := 1)).exists_lipschitzOnWith
    exact ⟨K, t, mem_nhdsWithin_of_mem_nhds ht, hK⟩
  · have hfin : Module.finrank ℝ (Fin d → ℂ) = 2 * d := by
      rw [Module.finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_comm]
    calc dimH O ≤ dimH (Set.univ : Set (Fin d → ℂ)) := dimH_mono (Set.subset_univ _)
      _ = Module.finrank ℝ (Fin d → ℂ) := Real.dimH_univ_eq_finrank _
      _ = 2 * (d : ℝ≥0∞) := by rw [hfin]; push_cast; ring

theorem dimH_regular_zeros_le {k : ℕ} {U : Set (Fin k → ℂ)} {g : (Fin k → ℂ) → ℂ}
    (hg : AnalyticOnNhd ℂ g U) :
    dimH {v | v ∈ U ∧ g v = 0 ∧ fderiv ℂ g v ≠ 0} ≤ 2 * ((k - 1 : ℕ) : ℝ≥0∞) := by
  refine dimH_le_of_local fun p hp => ?_
  obtain ⟨d, A, O, V, φ, hd, hO, hV, hpV, -, hφ, -, hZ⟩ :=
    AnalyticImplicitChart.proof (Fin k) (Fin 1) (fun _ => g) p Set.univ (fun _ => hg p hp.1)
      (fun _ => hp.2.1) (linearIndependent_unique_iff.2 hp.2.2) univ_mem
  refine ⟨V, hV.mem_nhds hpV, ?_⟩
  have hk : k - 1 = d := by simp only [Fintype.card_fin] at hd; omega
  rw [hk]
  refine (dimH_mono ?_).trans (dimH_image_le_of_analyticOnNhd hφ)
  rw [← hZ]
  rintro z ⟨hz, hzV⟩
  exact ⟨hzV, fun _ => hz.2.1⟩

theorem exists_partialDeriv {k : ℕ} {U : Set (Fin k → ℂ)} {h : (Fin k → ℂ) → ℂ} (hU : IsOpen U)
    (hh : AnalyticOnNhd ℂ h U) (hW : ∀ W ⊆ U, IsOpen W → W.Nonempty → ∃ w ∈ W, h w ≠ 0)
    {v : Fin k → ℂ} (hv : v ∈ U) (h0 : h v = 0) :
    ∃ n m, partialDeriv h n m v = 0 ∧ fderiv ℂ (partialDeriv h n m) v ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hdiff : ∀ n, DifferentiableAt ℂ (iteratedFDeriv ℂ n h) v := fun n =>
    ((hh.iteratedFDeriv n) v hv).differentiableAt
  have hall : ∀ n m, partialDeriv h n m v = 0 := by
    intro n
    induction n with
    | zero => intro m; simp [partialDeriv, iteratedFDeriv_zero_apply, h0]
    | succ n ih =>
      intro m
      have h1 := hcon n (Fin.tail m) (ih _)
      have h2 := congrArg (fun L => L (Pi.basisFun ℂ (Fin k) (m 0))) h1
      simp only [zero_apply] at h2
      unfold partialDeriv at h2 ⊢
      rw [fderiv_continuousMultilinear_apply_const_apply (hdiff n)] at h2
      rw [iteratedFDeriv_succ_apply_left]
      exact h2
  have hzero : ∀ n, iteratedFDeriv ℂ n h v = 0 := fun n =>
    ContinuousMultilinearMap.toMultilinearMap_injective
      (Module.Basis.ext_multilinear (fun _ => Pi.basisFun ℂ (Fin k)) fun m => by
        simpa [partialDeriv] using hall n m)
  obtain ⟨p, r, hp⟩ := hh v hv
  have hev : ∀ᶠ x in 𝓝 v, h x = 0 := by
    have h1 : Tendsto (fun x => x - v) (𝓝 v) (𝓝 0) := by
      simpa using (continuous_sub_right v).tendsto v
    filter_upwards [h1.eventually (Metric.eball_mem_nhds 0 hp.r_pos)] with x hx
    have hs := hp.hasSum_iteratedFDeriv hx
    simp only [hzero, zero_apply, smul_zero, add_sub_cancel] at hs
    exact hs.unique hasSum_zero
  obtain ⟨W, hWsub, hWo, hvW⟩ := _root_.mem_nhds_iff.1 (hev.and (hU.mem_nhds hv))
  obtain ⟨w, hw, hw0⟩ := hW W (fun x hx => (hWsub hx).2) hWo ⟨v, hvW⟩
  exact hw0 (hWsub hw).1

theorem proof : HolomorphicZeroSetDimH.Statement := by
  intro k U h hU hh hW
  have ha : AnalyticOnNhd ℂ h U :=
    analyticOnNhd_pi_iff.1 (ProperHolomorphicSurjective.analyticOnNhd_of_differentiableOn (m := 1)
      (f := fun v _ => h v) hU (differentiableOn_pi.2 fun _ => hh)) 0
  have hpd : ∀ n m, AnalyticOnNhd ℂ (partialDeriv h n m) U := fun n m x hx =>
    ((ContinuousMultilinearMap.apply ℂ (fun _ : Fin n => Fin k → ℂ) ℂ
      (fun j => Pi.basisFun ℂ (Fin k) (m j))).analyticAt _).comp (ha.iteratedFDeriv n x hx)
  calc dimH {v | v ∈ U ∧ h v = 0}
      ≤ dimH (⋃ nm : (Σ n, Fin n → Fin k),
          {v | v ∈ U ∧ partialDeriv h nm.1 nm.2 v = 0 ∧ fderiv ℂ (partialDeriv h nm.1 nm.2) v ≠ 0}) := by
        refine dimH_mono fun v hv => ?_
        obtain ⟨n, m, h1, h2⟩ := exists_partialDeriv hU ha hW hv.1 hv.2
        exact Set.mem_iUnion.2 ⟨⟨n, m⟩, hv.1, h1, h2⟩
    _ ≤ 2 * ((k - 1 : ℕ) : ℝ≥0∞) := by
        rw [dimH_iUnion]
        exact iSup_le fun nm => dimH_regular_zeros_le (hpd nm.1 nm.2)

end HolomorphicZeroSetDimH

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPrimeGermNullstellensatz
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

namespace PrimeGermNullstellensatz

variable {σ : Type} [Fintype σ] {w : σ → ℂ}

theorem exists_of_mem_holGermIdeal {k : ℕ} (p : Fin k → (σ → ℂ) → ℂ) {φ : holGerms w}
    (hφ : φ ∈ holGermIdeal w p) :
    ∃ h : Fin k → (σ → ℂ) → ℂ, (∀ i, AnalyticAt ℂ (h i) w) ∧
      (φ : Germ (𝓝 w) ℂ) = ((fun z => ∑ i, h i z * p i z : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) := by
  induction hφ using Submodule.span_induction with
  | mem φ hφ =>
    obtain ⟨i, hi⟩ := hφ
    refine ⟨fun j _ => if j = i then 1 else 0, fun j => analyticAt_const, ?_⟩
    rw [hi]
    congr 1
    funext z
    simp
  | zero =>
    refine ⟨fun _ _ => 0, fun _ => analyticAt_const, ?_⟩
    rw [show (fun z => ∑ i, (fun (_ : Fin k) (_ : σ → ℂ) => (0 : ℂ)) i z * p i z) = (0 : (σ → ℂ) → ℂ) by
      funext z; simp]
    rfl
  | add x y _ _ hx hy =>
    obtain ⟨h₁, hh₁, e₁⟩ := hx
    obtain ⟨h₂, hh₂, e₂⟩ := hy
    refine ⟨fun i z => h₁ i z + h₂ i z, fun i => (hh₁ i).add (hh₂ i), ?_⟩
    show (x : Germ (𝓝 w) ℂ) + y = _
    rw [e₁, e₂, ← Germ.coe_add]
    congr 1
    funext z
    simp [add_mul, Finset.sum_add_distrib]
  | smul a x _ hx =>
    obtain ⟨h, hh, e⟩ := hx
    obtain ⟨fa, hfa, efa⟩ : ∃ f : (σ → ℂ) → ℂ, AnalyticAt ℂ f w ∧ (f : Germ (𝓝 w) ℂ) = a := a.2
    refine ⟨fun i z => fa z * h i z, fun i => hfa.mul (hh i), ?_⟩
    show (a : Germ (𝓝 w) ℂ) * x = _
    rw [e, ← efa, ← Germ.coe_mul]
    congr 1
    funext z
    simp [Finset.mul_sum, mul_assoc]

theorem mem_holGermIdeal_of_eq {k : ℕ} {p : Fin k → (σ → ℂ) → ℂ} (hp : ∀ i, AnalyticAt ℂ (p i) w)
    {h : Fin k → (σ → ℂ) → ℂ} (hh : ∀ i, AnalyticAt ℂ (h i) w) (φ : holGerms w)
    (hφ : (φ : Germ (𝓝 w) ℂ) = ((fun z => ∑ i, h i z * p i z : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ)) :
    φ ∈ holGermIdeal w p := by
  have hsum : φ = ∑ i, (⟨(h i : Germ (𝓝 w) ℂ), h i, hh i, rfl⟩ : holGerms w) *
      ⟨(p i : Germ (𝓝 w) ℂ), p i, hp i, rfl⟩ := by
    apply Subtype.ext
    rw [hφ, show (fun z => ∑ i, h i z * p i z : (σ → ℂ) → ℂ) = ∑ i, h i * p i by
      funext z; simp [Finset.sum_apply]]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [show ((∑ i, h i * p i : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) = Germ.coeRingHom (𝓝 w) (∑ i, h i * p i) from rfl,
      map_sum, AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul]
    rfl
  rw [hsum]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

theorem coeff_eq_zero_of_distinct_roots {N : ℕ} (c t : Fin N → ℂ) (ht : Function.Injective t)
    (hroot : ∀ m, ∑ j, c j * t m ^ (j : ℕ) = 0) : ∀ j, c j = 0 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    exact fun j => j.elim0
  set Q : Polynomial ℂ := ∑ j : Fin N, Polynomial.C (c j) * Polynomial.X ^ (j : ℕ)
  have hQe : ∀ s, Q.eval s = ∑ j, c j * s ^ (j : ℕ) := by
    intro s
    simp [Q, Polynomial.eval_finsetSum]
  have hdeg : Q.natDegree < Fintype.card (Fin N) := by
    rw [Fintype.card_fin]
    refine lt_of_le_of_lt (Polynomial.natDegree_sum_le_of_forall_le _ _ (n := N - 1) fun j _ => ?_)
      (Nat.sub_lt hN Nat.one_pos)
    exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.le_sub_one_of_lt j.isLt)
  have hQ : Q = 0 := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero Q ht
    (fun m => by rw [hQe]; exact hroot m) hdeg
  intro j
  have hj := congrArg (fun q : Polynomial ℂ => q.coeff (j : ℕ)) hQ
  simp only [Q, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero,
    Fin.val_inj] at hj
  simpa using hj

theorem proof (hCover : PrimeGermCanonicalCover.Statement) : PrimeGermNullstellensatz.Statement := by
  intro σ _ w k p g hp hg hP hvan
  obtain ⟨d, A, ℓ, N, δ, hδ, hδP, hdiv, hsheet⟩ := hCover σ w k p hp hP
  obtain ⟨M, a, h, ha, hh, hrel⟩ := hdiv g hg

  have hoff : ∀ᶠ y in 𝓝 (A w), δ y ≠ 0 → ∀ j, a j y = 0 := by
    filter_upwards [hsheet _ (hrel.and hvan)] with y hy hδy
    obtain ⟨x, hx, hinj⟩ := hy hδy
    refine coeff_eq_zero_of_distinct_roots (fun j => a j y) (fun m => ℓ (x m)) hinj fun m => ?_
    obtain ⟨⟨hr, hv⟩, hpx, hAx⟩ := hx m
    have hg0 : g (x m) = 0 := hv hpx
    have h0 : δ (A (x m)) ^ M * g (x m) - ∑ j, a j (A (x m)) * ℓ (x m) ^ (j : ℕ) = 0 := by
      rw [hr]
      simp [hpx]
    rw [hg0, mul_zero, zero_sub, neg_eq_zero, hAx] at h0
    exact h0

  have hδne : ¬ (δ =ᶠ[𝓝 (A w)] 0) := by
    intro h0
    apply hδP
    refine ⟨fun _ _ => 0, fun _ => analyticAt_const, ?_⟩
    filter_upwards [(A.continuous.tendsto w).eventually h0] with z hz
    simpa using hz

  have hzero : ∀ᶠ y in 𝓝 (A w), ∀ j, a j y = 0 := by
    have hall : ∀ᶠ y in 𝓝 (A w), AnalyticAt ℂ δ y ∧ (∀ j, AnalyticAt ℂ (a j) y) ∧
        (δ y ≠ 0 → ∀ j, a j y = 0) :=
      hδ.eventually_analyticAt.and ((eventually_all.2 fun j => (ha j).eventually_analyticAt).and hoff)
    obtain ⟨r, hr0, hrB⟩ := Metric.eventually_nhds_iff_ball.1 hall
    filter_upwards [Metric.ball_mem_nhds (A w) hr0] with y₀ hy₀ j
    by_contra hne
    apply hδne
    have hnear : δ =ᶠ[𝓝 y₀] 0 := by
      have hcont : ContinuousAt (a j) y₀ := ((hrB y₀ hy₀).2.1 j).continuousAt
      filter_upwards [hcont.eventually_ne hne, Metric.isOpen_ball.mem_nhds hy₀] with y hy hyB
      by_contra hδy
      exact hy ((hrB y hyB).2.2 hδy j)
    have hon : AnalyticOnNhd ℂ δ (Metric.ball (A w) r) := fun y hy => (hrB y hy).1
    have hEq := hon.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball _ _).isPreconnected hy₀ hnear
    filter_upwards [Metric.ball_mem_nhds (A w) hr0] with y hy using hEq hy

  have hrel' : ∀ᶠ z in 𝓝 w, δ (A z) ^ M * g z = ∑ i, h i z * p i z := by
    filter_upwards [hrel, (A.continuous.tendsto w).eventually hzero] with z hz hz0
    rw [← hz]
    simp [hz0]
  have hδA : AnalyticAt ℂ (fun z => δ (A z)) w := hδ.comp (A.analyticAt w)
  let G : holGerms w := ⟨(g : Germ (𝓝 w) ℂ), g, hg, rfl⟩
  let Dg : holGerms w := ⟨((fun z => δ (A z) : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ), _, hδA, rfl⟩
  have hmem : Dg ^ M * G ∈ holGermIdeal w p := by
    refine mem_holGermIdeal_of_eq hp hh _ ?_
    rw [show ((Dg ^ M * G : holGerms w) : Germ (𝓝 w) ℂ) =
        (((fun z => δ (A z)) ^ M * g : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) by
      rw [Germ.coe_mul, Germ.coe_pow]
      rfl]
    exact Germ.coe_eq.2 (hrel'.mono fun z hz => by simpa using hz)
  have hDg : Dg ∉ holGermIdeal w p := by
    intro hD
    obtain ⟨h', hh', e⟩ := exists_of_mem_holGermIdeal p hD
    exact hδP ⟨h', hh', Germ.coe_eq.1 e⟩
  have hG : G ∈ holGermIdeal w p := by
    rcases hP.mem_or_mem hmem with h1 | h1
    · exact absurd (hP.mem_of_pow_mem M h1) hDg
    · exact h1
  obtain ⟨h', hh', e⟩ := exists_of_mem_holGermIdeal p hG
  exact ⟨h', hh', Germ.coe_eq.1 e⟩

end PrimeGermNullstellensatz

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PIsolatedFibreLocalUnbranched
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

private theorem germ_zero_of_mul_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : E → ℂ} {y : E}
    (hf : AnalyticAt ℂ f y) (hg : AnalyticAt ℂ g y) (hfg : ∀ᶠ z in 𝓝 y, f z * g z = 0) :
    (∀ᶠ z in 𝓝 y, f z = 0) ∨ (∀ᶠ z in 𝓝 y, g z = 0) := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1
    ((hf.eventually_analyticAt.and hg.eventually_analyticAt).and hfg)
  by_cases hf0 : ∀ z ∈ Metric.ball y r, f z = 0
  · exact Or.inl (Filter.mem_of_superset (Metric.ball_mem_nhds y hr) hf0)
  · right
    push Not at hf0
    obtain ⟨p, hp, hfp⟩ := hf0
    have hgp : g =ᶠ[𝓝 p] 0 := by
      filter_upwards [(hball hp).1.1.continuousAt.eventually_ne hfp, Metric.isOpen_ball.mem_nhds hp]
        with z hz1 hz2
      exact (mul_eq_zero.1 (hball hz2).2).resolve_left hz1
    have hgan : AnalyticOnNhd ℂ g (Metric.ball y r) := fun z hz => (hball hz).1.2
    have hzero := hgan.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball y r).isPreconnected hp hgp
    exact Filter.mem_of_superset (Metric.ball_mem_nhds y hr) fun z hz => by simpa using hzero hz

private theorem germ_factor_zero_of_prod_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {ι : Type*}
    (h : ι → E → ℂ) {y : E} (s : Finset ι) (han : ∀ i ∈ s, AnalyticAt ℂ (h i) y)
    (hprod : ∀ᶠ z in 𝓝 y, ∏ i ∈ s, h i z = 0) : ∃ i ∈ s, ∀ᶠ z in 𝓝 y, h i z = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨z, hz⟩ := hprod.exists
    simp at hz
  | insert a s ha ih =>
    have hg : AnalyticAt ℂ (fun z => ∏ i ∈ s, h i z) y :=
      Finset.analyticAt_fun_prod s fun i hi => han i (Finset.mem_insert_of_mem hi)
    have hprod' : ∀ᶠ z in 𝓝 y, h a z * ∏ i ∈ s, h i z = 0 := by
      filter_upwards [hprod] with z hz
      rwa [Finset.prod_insert ha] at hz
    rcases germ_zero_of_mul_zero (han a (Finset.mem_insert_self a s)) hg hprod' with h1 | h1
    · exact ⟨a, Finset.mem_insert_self a s, h1⟩
    · obtain ⟨i, hi, h2⟩ := ih (fun i hi => han i (Finset.mem_insert_of_mem hi)) h1
      exact ⟨i, Finset.mem_insert_of_mem hi, h2⟩

private theorem isOpen_diff_of_zeroSet {σ : Type} [Fintype σ] {Y N : Set (σ → ℂ)} {k : ℕ}
    {φ : Fin k → (σ → ℂ) → ℂ} (hN : IsOpen N) (hφ : ∀ m, AnalyticOnNhd ℂ (φ m) N)
    (hY : Y ∩ N = {z | z ∈ N ∧ ∀ m, φ m z = 0}) : IsOpen (N \ Y) := by
  have hEq : N \ Y = ⋃ m, N ∩ φ m ⁻¹' {0}ᶜ := by
    ext z
    simp only [Set.mem_sdiff, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨hzN, hzY⟩
      by_contra hcon
      push Not at hcon
      have hz : z ∈ Y ∩ N := by
        rw [hY]
        exact ⟨hzN, fun m => hcon m hzN⟩
      exact hzY hz.1
    · rintro ⟨m, hzN, hzm⟩
      refine ⟨hzN, fun hzY => hzm ?_⟩
      have hz : z ∈ Y ∩ N := ⟨hzY, hzN⟩
      rw [hY] at hz
      exact hz.2 m
  rw [hEq]
  exact isOpen_iUnion fun m => (hφ m).continuousOn.isOpen_inter_preimage hN isOpen_compl_singleton

theorem IsolatedFibreLocalUnbranched.proof (hcomp : OpenProjectionDominantComponents.Statement)
    (hmeet : IrreducibleGermMeetOverHypersurface.Statement)
    (hprim : IrreducibleGermPrimitiveForm.Statement)
    (hsheet : PrimitiveFormSheetedOffDiscriminant.Statement) :
    IsolatedFibreLocalUnbranched.Statement := by
  classical
  intro σ _ X B k f d A hB hf hXB hopen w hw hiso
  obtain ⟨n, Y, hY, hsepY, W0, hW0, hXW0⟩ := hcomp σ X B k f d A hB hf hXB hopen w hw
  obtain ⟨W, hW, hWiso⟩ := hiso

  have hisoY : ∀ i, ∃ W' ∈ 𝓝 w, ∀ x ∈ Y i ∩ W', A x = A w → x = w := fun i =>
    ⟨W ∩ W0, inter_mem hW hW0, fun x hx hAx => by
      have hxX : x ∈ X ∩ B ∩ W0 := by
        rw [hXW0]
        exact ⟨Set.mem_iUnion.2 ⟨i, hx.1⟩, hx.2.2⟩
      exact hWiso x ⟨hxX.1, hx.2.1⟩ hAx⟩

  have hsh : ∀ i, ∃ δ : (Fin d → ℂ) → ℂ, AnalyticAt ℂ δ (A w) ∧ (¬ ∀ᶠ y in 𝓝 (A w), δ y = 0) ∧
      ∃ M ∈ 𝓝 w, ∀ y ∈ Y i ∩ M, δ (A y) ≠ 0 → ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ))
        (g : (Fin d → ℂ) → σ → ℂ), IsOpen O ∧ IsOpen V ∧ y ∈ V ∧ AnalyticOnNhd ℂ g O ∧
          (∀ t ∈ O, A (g t) = t) ∧ Y i ∩ V = g '' O := by
    intro i
    obtain ⟨ℓ, N, a, δ, q, ha, hδ, hq, hδ0, hP, hsep, hQ⟩ :=
      hprim σ (Y i) w d A (hY i).1 (hY i).2.1 (hisoY i) (hY i).2.2
    exact ⟨δ, hδ, hδ0,
      hsheet σ (Y i) w d A (hY i).1 (hY i).2.1 (hisoY i) (hY i).2.2 ℓ N a δ q ha hδ hq hδ0 hP hsep hQ⟩
  choose δ hδa hδ0 M hM hMsh using hsh

  have hsp : ∀ i j, ∃ e : (Fin d → ℂ) → ℂ, AnalyticAt ℂ e (A w) ∧ (¬ ∀ᶠ y in 𝓝 (A w), e y = 0) ∧
      (i ≠ j → ∀ᶠ z in 𝓝 w, z ∈ Y i → z ∈ Y j → e (A z) = 0) := by
    intro i j
    by_cases hij : i = j
    · refine ⟨fun _ => 1, analyticAt_const, fun h => ?_, fun h => absurd hij h⟩
      obtain ⟨y, hy⟩ := h.exists
      exact one_ne_zero hy
    · obtain ⟨e, he, he0, hez⟩ :=
        hmeet σ (Y i) (Y j) w d A (hY i).1 (hY i).2.1 (hisoY i) (hY j).1 (hsepY i j hij)
      exact ⟨e, he, he0, fun _ => hez⟩
  choose e hea he0 hez using hsp

  have hYa : ∀ j, ∃ (N : Set (σ → ℂ)) (kk : ℕ) (φ : Fin kk → (σ → ℂ) → ℂ), IsOpen N ∧ w ∈ N ∧
      (∀ m, AnalyticOnNhd ℂ (φ m) N) ∧ Y j ∩ N = {z | z ∈ N ∧ ∀ m, φ m z = 0} := fun j => (hY j).1
  choose N kk φ hNo hwN hφ hYN using hYa
  have hfac : ∀ i, AnalyticAt ℂ (fun y => δ i y * ∏ j, e i j y) (A w) := fun i =>
    (hδa i).mul (Finset.analyticAt_fun_prod _ fun j _ => hea i j)
  refine ⟨interior W0 ∩ (⋂ i, M i) ∩ (⋂ j, N j) ∩
      {z | ∀ i j, i ≠ j → z ∈ Y i → z ∈ Y j → e i j (A z) = 0},
    fun y => ∏ i, (δ i y * ∏ j, e i j y), ?_, Finset.analyticAt_fun_prod _ fun i _ => hfac i, ?_, ?_⟩
  · refine inter_mem (inter_mem (inter_mem (interior_mem_nhds.2 hW0) (iInter_mem.2 hM))
      (iInter_mem.2 fun j => (hNo j).mem_nhds (hwN j))) ?_
    have hev : ∀ i j, ∀ᶠ z in 𝓝 w, i ≠ j → z ∈ Y i → z ∈ Y j → e i j (A z) = 0 := fun i j => by
      by_cases hij : i = j
      · exact Eventually.of_forall fun _ h => absurd hij h
      · filter_upwards [hez i j hij] with z hz _ using hz
    exact eventually_all.2 fun i => eventually_all.2 fun j => hev i j
  · intro hg0
    obtain ⟨i, -, hi⟩ := germ_factor_zero_of_prod_zero (fun i y => δ i y * ∏ j, e i j y) Finset.univ
      (fun i _ => hfac i) hg0
    rcases germ_zero_of_mul_zero (hδa i) (Finset.analyticAt_fun_prod _ fun j _ => hea i j) hi with h1 | h1
    · exact hδ0 i h1
    · obtain ⟨j, -, hj⟩ := germ_factor_zero_of_prod_zero (e i) Finset.univ (fun j _ => hea i j) h1
      exact he0 i j hj
  · intro x hx hgx
    obtain ⟨hxXB, ⟨⟨hxW0, hxM⟩, hxN⟩, hxe⟩ := hx
    simp only [Set.mem_iInter] at hxM hxN
    have hgx' : ∀ i, δ i (A x) ≠ 0 ∧ ∀ j, e i j (A x) ≠ 0 := by
      intro i
      have hi := (Finset.prod_ne_zero_iff.1 hgx) i (Finset.mem_univ i)
      exact ⟨left_ne_zero_of_mul hi,
        fun j => (Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hi)) j (Finset.mem_univ j)⟩
    have hxU : x ∈ (⋃ i, Y i) ∩ W0 := by
      rw [← hXW0]
      exact ⟨hxXB, interior_subset hxW0⟩
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hxU.1
    have hxnot : ∀ j, j ≠ i → x ∉ Y j := fun j hji hxj =>
      (hgx' i).2 j (hxe i j (Ne.symm hji) hxi hxj)

    let U : Set (σ → ℂ) := interior W0 ∩ ⋂ j, (if j = i then Set.univ else N j \ Y j)
    have hUo : IsOpen U := by
      refine isOpen_interior.inter (isOpen_iInter_of_finite fun j => ?_)
      split_ifs
      · exact isOpen_univ
      · exact isOpen_diff_of_zeroSet (hNo j) (hφ j) (hYN j)
    have hxUm : x ∈ U := by
      refine ⟨hxW0, Set.mem_iInter.2 fun j => ?_⟩
      split_ifs with hji
      · trivial
      · exact ⟨hxN j, hxnot j hji⟩
    have hXU : X ∩ B ∩ U = Y i ∩ U := by
      ext z
      constructor
      · rintro ⟨hzXB, hzU⟩
        have hzW : z ∈ (⋃ i, Y i) ∩ W0 := by
          rw [← hXW0]
          exact ⟨hzXB, interior_subset hzU.1⟩
        obtain ⟨j, hzj⟩ := Set.mem_iUnion.1 hzW.1
        by_cases hji : j = i
        · rw [hji] at hzj
          exact ⟨hzj, hzU⟩
        · have hzj' := Set.mem_iInter.1 hzU.2 j
          rw [if_neg hji] at hzj'
          exact absurd hzj hzj'.2
      · rintro ⟨hzi, hzU⟩
        have hzW : z ∈ X ∩ B ∩ W0 := by
          rw [hXW0]
          exact ⟨Set.mem_iUnion.2 ⟨i, hzi⟩, interior_subset hzU.1⟩
        exact ⟨hzW.1, hzU⟩

    obtain ⟨O, V, h, hO, hV, hxV, hh, hAh, hYV⟩ := hMsh i x ⟨hxi, hxM i⟩ (hgx' i).1
    refine ⟨O ∩ h ⁻¹' U, V ∩ U, h, hh.continuousOn.isOpen_inter_preimage hO hUo, hV.inter hUo,
      ⟨hxV, hxUm⟩, hh.mono Set.inter_subset_left, fun t ht => hAh t ht.1, ?_⟩
    rw [Set.image_inter_preimage, ← hYV]
    ext z
    constructor
    · rintro ⟨hzXB, hzV, hzU⟩
      have hz : z ∈ Y i ∩ U := by
        rw [← hXU]
        exact ⟨hzXB, hzU⟩
      exact ⟨⟨hz.1, hzV⟩, hzU⟩
    · rintro ⟨⟨hzi, hzV⟩, hzU⟩
      have hz : z ∈ X ∩ B ∩ U := by
        rw [hXU]
        exact ⟨hzi, hzU⟩
      exact ⟨hz.1, hzV, hzU⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteProjectionSheetedClosureEquations
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

theorem FiniteProjectionSheetedClosureEquations.surjective_of_no_germ {σ : Type} [Fintype σ] {d : ℕ}
    {w : σ → ℂ} {X : Set (σ → ℂ)} (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ))
    (hA : ∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A w) → (∀ᶠ z in 𝓝 w, z ∈ X → h (A z) = 0) →
        ∀ᶠ y in 𝓝 (A w), h y = 0) : Function.Surjective A := by
  by_contra hns
  have hlt : LinearMap.range (A : (σ → ℂ) →ₗ[ℂ] (Fin d → ℂ)) < ⊤ :=
    lt_top_iff_ne_top.2 fun htop => hns (by simpa using LinearMap.range_eq_top.1 htop)
  obtain ⟨f, hf0, hfmap⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hlt inferInstance
  have hfA : ∀ z, f (A z) = 0 := fun z => by
    have : f (A z) ∈ (LinearMap.range (A : (σ → ℂ) →ₗ[ℂ] (Fin d → ℂ))).map f := ⟨A z, ⟨z, rfl⟩, rfl⟩
    rw [hfmap] at this
    exact this
  have hev := hA (fun y => LinearMap.toContinuousLinearMap f y)
    ((LinearMap.toContinuousLinearMap f).analyticAt _)
    (Eventually.of_forall fun z _ => by simpa using hfA z)
  apply hf0
  have hker : LinearMap.ker f = ⊤ := by
    apply Submodule.eq_top_of_nonempty_interior'
    refine ⟨A w, mem_interior_iff_mem_nhds.2 ?_⟩
    filter_upwards [hev] with y hy
    simpa using hy
  exact LinearMap.ker_eq_top.1 hker

theorem FiniteProjectionSheetedClosureEquations.prod_sub_eq_sum_esymm (m : Multiset ℂ) (a : ℂ) :
    (m.map fun x => a - x).prod =
      ∑ j ∈ Finset.range (Multiset.card m + 1), (-1) ^ j * m.esymm j * a ^ (Multiset.card m - j) := by
  have key := congrArg (Polynomial.eval a) (Multiset.prod_X_sub_X_eq_sum_esymm m)
  rw [Polynomial.eval_multiset_prod, Polynomial.eval_finsetSum] at key
  simp only [Multiset.map_map, Function.comp_def, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_neg, Polynomial.eval_one] at key
  rw [key]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem FiniteProjectionSheetedClosureEquations.proof
    (hball : FiniteProjectionProperBall.Statement)
    (hcount : UnbranchedProperCountConstant.Statement)
    (hesymm : ProperSheetedFibreEsymm.Statement)
    (hgrid : GridProductLowerBound.Statement) :
    FiniteProjectionSheetedClosureEquations.Statement := by
  intro σ _ X w d A hX hiso hA δ hδ hsh
  classical
  have hsurj := FiniteProjectionSheetedClosureEquations.surjective_of_no_germ A hA
  by_cases hz : ∀ᶠ t in 𝓝 (A w), δ t = 0
  · have hz' : ∀ᶠ z in 𝓝 w, δ (A z) = 0 := (A.continuous.tendsto w).eventually hz
    refine ⟨1, fun _ _ => 1, fun _ => analyticAt_const, ?_,
      Eventually.of_forall fun z _ h => absurd (h 0) one_ne_zero⟩
    filter_upwards [hz'] with z hz0 _ hne
    exact absurd hz0 hne
  obtain ⟨M, hM, hMsh⟩ := hsh
  obtain ⟨ρ, hρ, r, hr, hρM, hK⟩ := hball σ X w d A hX hiso M hM
  obtain ⟨r₂, hr₂, hδr⟩ := Metric.eventually_nhds_iff_ball.1 hδ.eventually_analyticAt
  set D : Set (Fin d → ℂ) := Metric.ball (A w) (min r r₂) with hDdef
  set Y : Set (σ → ℂ) := {x | x ∈ X ∩ Metric.ball w ρ ∧ A x ∈ D} with hYdef
  have hDo : IsOpen D := Metric.isOpen_ball
  have hDc : IsPreconnected D := (convex_ball _ _).isPreconnected
  have hwD : A w ∈ D := Metric.mem_ball_self (lt_min hr hr₂)
  have hmap : Set.MapsTo A Y D := fun x hx => hx.2
  have hprop : ∀ K ⊆ D, IsCompact K → IsCompact {x | x ∈ Y ∧ A x ∈ K} := by
    intro K hKD hKc
    have hKr : K ⊆ Metric.ball (A w) r := hKD.trans (Metric.ball_subset_ball (min_le_left _ _))
    have heq : {x | x ∈ Y ∧ A x ∈ K} = {x | x ∈ X ∩ Metric.ball w ρ ∧ A x ∈ K} := by
      ext x
      exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hKD h.2⟩, h.2⟩⟩
    rw [heq]
    exact hK K hKr hKc
  have hδD : AnalyticOnNhd ℂ δ D := fun t ht => hδr t (Metric.ball_subset_ball (min_le_right _ _) ht)
  have hne : ∀ W : Set (Fin d → ℂ), IsOpen W → W ⊆ D → W.Nonempty → ∃ t ∈ W, δ t ≠ 0 := by
    rintro W hWo hWD ⟨t, ht⟩
    by_contra hall
    push Not at hall
    have hev : δ =ᶠ[𝓝 t] 0 := by
      filter_upwards [hWo.mem_nhds ht] with s hs
      exact hall s hs
    have h0 := hδD.eqOn_zero_of_preconnected_of_eventuallyEq_zero hDc (hWD ht) hev
    apply hz
    filter_upwards [hDo.mem_nhds hwD] with s hs
    exact h0 hs
  have hsec : ∀ x ∈ Y, δ (A x) ≠ 0 → ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (g : (Fin d → ℂ) → σ → ℂ),
      IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ AnalyticOnNhd ℂ g O ∧ (∀ y ∈ O, A (g y) = y) ∧ Y ∩ V = g '' O := by
    intro x hx hδx
    obtain ⟨O, V, g, hO, hV, hxV, hg, hAg, hXV⟩ := hMsh x ⟨hx.1.1, hρM hx.1.2⟩ hδx
    refine ⟨O ∩ g ⁻¹' Metric.ball w ρ ∩ D, V ∩ Metric.ball w ρ ∩ A ⁻¹' D, g,
      (hg.continuousOn.isOpen_inter_preimage hO Metric.isOpen_ball).inter hDo,
      (hV.inter Metric.isOpen_ball).inter (hDo.preimage A.continuous), ⟨⟨hxV, hx.1.2⟩, hx.2⟩,
      hg.mono fun t ht => ht.1.1, fun y hy => hAg y hy.1.1, ?_⟩
    ext z
    constructor
    · rintro ⟨⟨⟨hzX, hzb⟩, hzD⟩, ⟨⟨hzV, -⟩, -⟩⟩
      have hzg : z ∈ g '' O := by
        rw [← hXV]
        exact ⟨hzX, hzV⟩
      obtain ⟨t, ht, rfl⟩ := hzg
      refine ⟨t, ⟨⟨ht, hzb⟩, ?_⟩, rfl⟩
      rw [hAg t ht] at hzD
      exact hzD
    · rintro ⟨t, ⟨⟨ht, htb⟩, htD⟩, rfl⟩
      have hmem : g t ∈ X ∩ V := by
        rw [hXV]
        exact ⟨t, ht, rfl⟩
      have hA' : A (g t) ∈ D := by
        rw [hAg t ht]
        exact htD
      exact ⟨⟨⟨hmem.1, htb⟩, hA'⟩, ⟨⟨hmem.2, htb⟩, hA'⟩⟩
  obtain ⟨N, hN⟩ := hcount σ Y d A D δ hDo hDc hmap hprop hδD fun x hx hx' => by
    obtain ⟨O, V, g, hO, hV, hxV, hg, hAg, hYV⟩ := hsec x hx hx'
    exact ⟨O, V, g, hO, hV, hxV, hg.continuousOn, hAg, hYV⟩
  let l : (σ → Fin (N + 1)) → (σ → ℂ) →L[ℂ] ℂ := fun u =>
    ∑ i, ((u i : ℕ) : ℂ) • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) i
  have hl : ∀ u z, l u z = ∑ i, ((u i : ℕ) : ℂ) * z i := by
    intro u z
    simp [l]
  choose F hFan hFeq using fun u j => hesymm σ Y d A D δ (l u) j hDo hmap hprop hδD hne hsec
  let c : (σ → Fin (N + 1)) → (σ → ℂ) → ℂ := fun u z =>
    ∑ j ∈ Finset.range (N + 1), (-1) ^ j * F u j (A z) * l u z ^ (N - j)
  have hfib : ∀ z, A z ∈ D → δ (A z) ≠ 0 → ∃ s : Finset (σ → ℂ),
      (↑s : Set (σ → ℂ)) = {x | x ∈ Y ∧ A x = A z} ∧ s.card = N := by
    intro z hzD hδz
    have h := hN (A z) hzD hδz
    have hfin := Set.finite_of_encard_eq_coe h
    refine ⟨hfin.toFinset, hfin.coe_toFinset, ?_⟩
    have h' : ((hfin.toFinset : Finset (σ → ℂ)) : Set (σ → ℂ)).encard = N := by
      rw [hfin.coe_toFinset]
      exact h
    rw [Set.encard_coe_eq_coe_finsetCard] at h'
    exact_mod_cast h'
  have hprod : ∀ u z, A z ∈ D → δ (A z) ≠ 0 → ∀ s : Finset (σ → ℂ),
      (↑s : Set (σ → ℂ)) = {x | x ∈ Y ∧ A x = A z} → s.card = N →
      c u z = ∏ x ∈ s, (l u z - l u x) := by
    intro u z hzD hδz s hs hcard
    have hm : Multiset.card (s.val.map (l u)) = N := by simp [hcard]
    have key := FiniteProjectionSheetedClosureEquations.prod_sub_eq_sum_esymm (s.val.map (l u)) (l u z)
    rw [hm, Multiset.map_map] at key
    rw [Finset.prod_eq_multiset_prod]
    refine Eq.trans ?_ key.symm
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hFeq u j (A z) hzD hδz s hs]
  have hcan : ∀ u z, A z ∈ D → AnalyticAt ℂ (c u) z := by
    intro u z hzD
    refine Finset.analyticAt_fun_sum (𝕜 := ℂ)
      (f := fun j z => (-1 : ℂ) ^ j * F u j (A z) * l u z ^ (N - j)) _ fun j _ => ?_
    have h1 : AnalyticAt ℂ (F u j ∘ A) z := (hFan u j (A z) hzD).comp (ContinuousLinearMap.analyticAt A z)
    have h2 : AnalyticAt ℂ (fun z => l u z ^ (N - j)) z := ((l u).analyticAt z).pow _
    have h0 : AnalyticAt ℂ (fun _ : σ → ℂ => ((-1 : ℂ) ^ j)) z := analyticAt_const
    exact (h0.mul h1).mul h2
  let e := (Fintype.equivFin (σ → Fin (N + 1))).symm
  have hBw : Metric.ball w ρ ∩ A ⁻¹' D ∈ 𝓝 w :=
    (Metric.isOpen_ball.inter (hDo.preimage A.continuous)).mem_nhds ⟨Metric.mem_ball_self hρ, hwD⟩
  refine ⟨Fintype.card (σ → Fin (N + 1)), fun k => c (e k), fun k => hcan _ w hwD, ?_, ?_⟩
  · filter_upwards [hBw] with z hz hzX hδz k
    obtain ⟨s, hs, hcard⟩ := hfib z hz.2 hδz
    rw [hprod _ z hz.2 hδz s hs hcard]
    have hzs : z ∈ (↑s : Set (σ → ℂ)) := by
      rw [hs]
      exact ⟨⟨⟨hzX, hz.1⟩, hz.2⟩, rfl⟩
    exact Finset.prod_eq_zero hzs (sub_self _)
  · filter_upwards [hBw] with z₀ hz₀ hz₀X hall
    by_contra hcl
    set Z : Set (σ → ℂ) := {x | x ∈ Y ∧ δ (A x) ≠ 0} with hZdef
    have hZb : Bornology.IsBounded Z := Metric.isBounded_ball.subset fun x hx => hx.1.1.2
    have hZsub : Z ⊆ {x | x ∈ X ∧ δ (A x) ≠ 0} := fun x hx => ⟨hx.1.1.1, hx.2⟩
    have hZcl : z₀ ∉ closure Z := fun h => hcl (closure_mono hZsub h)
    obtain ⟨μ, hμ, U, hU, hbound⟩ := hgrid σ N Z z₀ hZb hZcl
    have hsmall : ∀ᶠ z in 𝓝 z₀, ∀ u, ‖c u z‖ < μ := by
      rw [Filter.eventually_all]
      intro u
      have h0 : c u z₀ = 0 := by
        have := hall (e.symm u)
        simpa only [Equiv.apply_symm_apply] using this
      have hcont : Tendsto (fun x => ‖c u x‖) (𝓝 z₀) (𝓝 ‖c u z₀‖) :=
        (hcan u z₀ hz₀.2).continuousAt.norm.tendsto
      rw [h0, norm_zero] at hcont
      exact hcont.eventually (gt_mem_nhds hμ)
    obtain ⟨W, hWsub, hWo, hz₀W⟩ :=
      mem_nhds_iff.1 (inter_mem (inter_mem hU hsmall) ((hDo.preimage A.continuous).mem_nhds hz₀.2))
    obtain ⟨t, ⟨z, hzW, rfl⟩, hδt⟩ := hne (A '' W) (A.isOpenMap hsurj W hWo)
      (by rintro t ⟨z, hz, rfl⟩; exact (hWsub hz).2) ⟨A z₀, z₀, hz₀W, rfl⟩
    obtain ⟨⟨hzU, hzc⟩, hzD⟩ := hWsub hzW
    obtain ⟨s, hs, hcard⟩ := hfib z hzD hδt
    have hsZ : (↑s : Set (σ → ℂ)) ⊆ Z := by
      rw [hs]
      rintro x ⟨hxY, hxA⟩
      exact ⟨hxY, by rw [hxA]; exact hδt⟩
    obtain ⟨u, hu⟩ := hbound z hzU s hsZ hcard.le
    have hlt := hzc u
    rw [hprod u z hzD hδt s hs hcard] at hlt
    have heq : ∏ x ∈ s, (l u z - l u x) = ∏ x ∈ s, ∑ i, ((u i : ℕ) : ℂ) * (z i - x i) := by
      refine Finset.prod_congr rfl fun x _ => ?_
      rw [hl, hl, ← Finset.sum_sub_distrib]
      simp [mul_sub]
    rw [heq] at hlt
    linarith

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end
