module

public import Development.WeilBound.CoreStatements.CentralCharts.PshAt0
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelAnalyticDataExists
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothContinuous
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsTorsionQuasiFiniteGroup

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.CentralCharts.SmoothOnOfTame
section -- merged from Development.WeilBound.CoreStatements.CentralCharts.ExistsPermFirst
noncomputable section

namespace AnalyticReference.An

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo Filter Topology Metric
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.PB

variable {n : ℕ} {X : Type} [TopologicalSpace X]

theorem holoAt_compat {A : FinHolAtlas n X} {ψ : OpenPartialHomeomorph X (Fin n → ℂ)} (hψ : IsCompatChart A ψ)
    {U : Set X} {g : X → ℂ} (hg : A.HoloOn U g) {t : Fin n → ℂ} (ht : t ∈ ψ.target) (hU : ψ.symm t ∈ U) :
    AnalyticAt ℂ (fun t' => g (ψ.symm t')) t := by
  obtain ⟨j, hj⟩ := A.cover (ψ.symm t)
  have h1 : AnalyticAt ℂ (A.chart j ∘ ψ.symm) t := (hψ j).2 t ⟨ht, hj⟩
  have h2 : AnalyticAt ℂ (g ∘ (A.chart j).symm) ((A.chart j ∘ ψ.symm) t) := by
    refine hg j _ ⟨(A.chart j).map_source hj, ?_⟩
    simp only [Function.comp, Set.mem_preimage, (A.chart j).left_inv hj]
    exact hU
  refine (h2.comp h1).congr ?_
  filter_upwards [(ψ.continuousAt_symm ht).preimage_mem_nhds ((A.chart j).open_source.mem_nhds hj)] with t' ht'
  have h3 : ψ.symm t' ∈ (A.chart j).source := ht'
  simp only [Function.comp, (A.chart j).left_inv h3]

def NChart (A : FinHolAtlas n X) (U : Set X) (L : LocPot X) (s : X → X → ℂ) (x₀ : X)
    (ψ : OpenPartialHomeomorph X (Fin n → ℂ)) (a : ℕ) (M : ℝ) : Prop :=
  IsCompatChart A ψ ∧ x₀ ∈ ψ.source ∧ ψ x₀ = 0 ∧ a ≤ n ∧ ∀ t ∈ ball (0 : Fin n → ℂ) 1, t ∈ ψ.target ∧ ψ.symm t ∈ U ∧
    (ψ.symm t ∈ bdry s ↔ ∃ i : Fin n, (i : ℕ) < a ∧ t i = 0) ∧
    (ψ.symm t ∉ bdry s → logR a t ≤ rW L s (ψ.symm t) + M)

theorem exists_perm_first (S : Finset (Fin n)) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, i ∈ S ↔ ((σ i : Fin n) : ℕ) < S.card := by
  classical
  have hle : S.card ≤ n := by simpa using S.card_le_univ
  have hcard : Fintype.card {i : Fin n // i ∈ S} = Fintype.card {i : Fin n // (i : ℕ) < S.card} := by
    rw [Fintype.card_coe, ← Fintype.card_congr (Fin.castLEquiv hle), Fintype.card_fin]
  have hcard' : Fintype.card {i : Fin n // ¬ i ∈ S} = Fintype.card {i : Fin n // ¬ (i : ℕ) < S.card} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, hcard]
  let e := Fintype.equivOfCardEq hcard
  let f := Fintype.equivOfCardEq hcard'
  refine ⟨Equiv.subtypeCongr e f, fun i => ?_⟩
  by_cases hi : i ∈ S
  · have h1 : Equiv.subtypeCongr e f i = e ⟨i, hi⟩ := by
      simp [Equiv.subtypeCongr, Equiv.sumCompl_symm_apply_of_pos hi]
    rw [h1]
    exact ⟨fun _ => (e ⟨i, hi⟩).2, fun _ => hi⟩
  · have h1 : Equiv.subtypeCongr e f i = f ⟨i, hi⟩ := by
      simp [Equiv.subtypeCongr, Equiv.sumCompl_symm_apply_of_neg hi]
    rw [h1]
    exact ⟨fun h => absurd h hi, fun h => absurd h (f ⟨i, hi⟩).2⟩

def scalePerm (δ : ℝ) (hδ : 0 < δ) (σ : Equiv.Perm (Fin n)) : (Fin n → ℂ) ≃L[ℂ] (Fin n → ℂ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun t i => (δ : ℂ) * t (σ i)
      invFun := fun y i => (δ : ℂ)⁻¹ * y (σ.symm i)
      map_add' := fun t t' => by funext i; simp [mul_add]
      map_smul' := fun c t => by funext i; simp; ring
      left_inv := fun t => by
        have h : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
        funext i; simp [h]
      right_inv := fun t => by
        have h : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
        funext i; simp [h] }

theorem scalePerm_apply (δ : ℝ) (hδ : 0 < δ) (σ : Equiv.Perm (Fin n)) (t : Fin n → ℂ) (i : Fin n) :
    scalePerm δ hδ σ t i = (δ : ℂ) * t (σ i) := rfl

theorem exists_nchart (A : FinHolAtlas n X) (L : LocPot X) (s : X → X → ℂ) {nb : ℕ} {m : Fin nb → ℕ}
    {W : Fin nb → Set X} (hL : IsPotential A L) (hs : IsSection A L s) (snc : IsSNC A L s m W) (x₀ : X) (U : Set X)
    (hU : IsOpen U) (hx : x₀ ∈ U) : ∃ ψ a M, NChart A U L s x₀ ψ a M := by
  classical
  obtain ⟨φ, S, μ, v, hφ, hx0, hball2, hφ0, hsrc, hμ, hv, hv0, hsv⟩ :=
    GlobalTheory.T.exists_snc_adapted_chart_at_point n X A L s nb m W snc x₀
  obtain ⟨hbd, M, hM⟩ := GlobalTheory.T.snc_adapted_chart_section_form n X A L s hL hs x₀ φ S μ v hφ hball2 hsrc hμ hv hv0 hsv
  have h0t : (0 : Fin n → ℂ) ∈ φ.target := hball2 (by simp)
  have hs0 : φ.symm 0 = x₀ := by rw [← hφ0]; exact φ.left_inv hx0
  have hnhds : φ.target ∩ φ.symm ⁻¹' U ∈ 𝓝 (0 : Fin n → ℂ) := by
    refine Filter.inter_mem (φ.open_target.mem_nhds h0t) ?_
    exact (φ.continuousAt_symm h0t).preimage_mem_nhds (by rw [hs0]; exact hU.mem_nhds hx)
  obtain ⟨δ', hδ', hδball⟩ := Metric.mem_nhds_iff.1 hnhds
  have hδ : 0 < min δ' 1 := lt_min hδ' one_pos
  have hδ1 : min δ' 1 ≤ 1 := min_le_right _ _
  have hδδ' : min δ' 1 ≤ δ' := min_le_left _ _
  obtain ⟨σ, hσ⟩ := exists_perm_first S
  let Lδ := scalePerm (min δ' 1) hδ σ
  let ψ := φ.transHomeomorph Lδ.toHomeomorph.symm
  have hψs : ∀ t, ψ.symm t = φ.symm (Lδ t) := fun t => rfl
  have hψ : ∀ x, ψ x = Lδ.symm (φ x) := fun x => rfl
  have hψtgt : ∀ t, t ∈ ψ.target ↔ Lδ t ∈ φ.target := fun t => Iff.rfl
  have hnorm : ∀ t : Fin n → ℂ, ‖t‖ < 1 → ‖Lδ t‖ < min δ' 1 := by
    intro t ht
    refine (pi_norm_lt_iff hδ).2 fun i => ?_
    rw [scalePerm_apply, norm_mul, Complex.norm_real, Real.norm_of_nonneg hδ.le]
    have : ‖t (σ i)‖ < 1 := (norm_le_pi_norm t (σ i)).trans_lt ht
    nlinarith [norm_nonneg (t (σ i))]
  refine ⟨ψ, S.card, M, ?_, ?_, ?_, by simpa using S.card_le_univ, ?_⟩
  · intro j
    constructor
    · intro y hy
      have hy' : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' φ.source := hy
      exact ((Lδ.symm : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)).analyticAt _).comp ((hφ j).1 y hy')
    · intro y hy
      have hy' : Lδ y ∈ φ.target ∩ φ.symm ⁻¹' (A.chart j).source := hy
      exact ((hφ j).2 _ hy').comp ((Lδ : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)).analyticAt y)
  · exact hx0
  · rw [hψ, hφ0, map_zero]
  · intro t ht
    have ht1 : ‖t‖ < 1 := by simpa using ht
    have hz : ‖Lδ t‖ < min δ' 1 := hnorm t ht1
    have hzb : Lδ t ∈ ball (0 : Fin n → ℂ) δ' := by simpa using hz.trans_le hδδ'
    have hzmem := hδball hzb
    have hz2 : Lδ t ∈ closedBall (0 : Fin n → ℂ) 2 := by
      rw [mem_closedBall_zero_iff]; linarith
    have hzero : ∀ i, Lδ t i = 0 ↔ t (σ i) = 0 := by
      intro i
      rw [scalePerm_apply]
      simp [hδ.ne']
    have hbdry : ψ.symm t ∈ bdry s ↔ ∃ i : Fin n, (i : ℕ) < S.card ∧ t i = 0 := by
      rw [hψs, hbd _ hzmem.1]
      constructor
      · rintro ⟨i, hi, h0⟩
        exact ⟨σ i, (hσ i).1 hi, (hzero i).1 h0⟩
      · rintro ⟨j, hj, h0⟩
        exact ⟨σ.symm j, (hσ _).2 (by simpa using hj), (hzero _).2 (by simpa using h0)⟩
    refine ⟨(hψtgt t).2 hzmem.1, by rw [hψs]; exact hzmem.2, hbdry, ?_⟩
    intro hnb
    have hall : ∀ i ∈ S, t (σ i) ≠ 0 := fun i hi h0 => hnb (hbdry.2 ⟨σ i, (hσ i).1 hi, h0⟩)
    have hrw : |rW L s (ψ.symm t) - rLoc S μ (Lδ t)| ≤ M := hM _ hz2 hnb
    have hloc : logR S.card t ≤ rLoc S μ (Lδ t) := by
      unfold logR rLoc
      have hsum : (∑ i : Fin n, if (i : ℕ) < S.card then Real.log (1 / ‖t i‖ ^ 2) else 0) =
          ∑ i ∈ S, Real.log (1 / ‖t (σ i)‖ ^ 2) := by
        calc (∑ i : Fin n, if (i : ℕ) < S.card then Real.log (1 / ‖t i‖ ^ 2) else 0)
            = ∑ i : Fin n, (if ((σ i : Fin n) : ℕ) < S.card then Real.log (1 / ‖t (σ i)‖ ^ 2) else 0) :=
              (Equiv.sum_comp σ (fun i : Fin n =>
                if (i : ℕ) < S.card then Real.log (1 / ‖t i‖ ^ 2) else 0)).symm
          _ = ∑ i : Fin n, (if i ∈ S then Real.log (1 / ‖t (σ i)‖ ^ 2) else 0) :=
              Finset.sum_congr rfl fun i _ => by
                by_cases hi : i ∈ S
                · rw [if_pos ((hσ i).1 hi), if_pos hi]
                · rw [if_neg (fun h => hi ((hσ i).2 h)), if_neg hi]
          _ = ∑ i ∈ S, Real.log (1 / ‖t (σ i)‖ ^ 2) := by
              rw [Finset.sum_ite_mem, Finset.univ_inter]
      rw [hsum]
      gcongr with i hi
      have hx : 0 < ‖t (σ i)‖ := norm_pos_iff.2 (hall i hi)
      have hx1 : ‖t (σ i)‖ < 1 := (norm_le_pi_norm t (σ i)).trans_lt ht1
      have hLi : ‖Lδ t i‖ = min δ' 1 * ‖t (σ i)‖ := by
        rw [scalePerm_apply, norm_mul, Complex.norm_real, Real.norm_of_nonneg hδ.le]
      have hpos : 0 < min δ' 1 * ‖t (σ i)‖ := mul_pos hδ hx
      have hA : 0 ≤ Real.log (1 / ‖t (σ i)‖ ^ 2) := by
        apply Real.log_nonneg
        rw [le_div_iff₀ (by positivity)]
        nlinarith
      have hB : Real.log (1 / ‖t (σ i)‖ ^ 2) ≤ Real.log (4 / ‖Lδ t i‖ ^ 2) := by
        rw [hLi]
        apply Real.log_le_log (by positivity)
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have : min δ' 1 ^ 2 ≤ 1 := by nlinarith
        nlinarith [sq_nonneg ‖t (σ i)‖]
      have hμ1 : (1 : ℝ) ≤ μ i := by exact_mod_cast hμ i hi
      nlinarith
    have := (abs_le.1 hrw).1
    linarith

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem not_mem_top (z : (Σ k, J k) → ℂ) : z ∉ mcPts (⊤ : Ideal (MRing J)) := by
  intro h
  have := h.2 1 trivial
  simp at this

theorem analyticAt_lift {P Q : Ideal (MRing J)} (R : AnLogRes P Q n) {ψ : OpenPartialHomeomorph R.X (Fin n → ℂ)}
    (hψ : IsCompatChart R.A ψ) (x₀ : R.X) {t : Fin n → ℂ} (ht : t ∈ ψ.target) (hU : ψ.symm t ∈ R.U x₀) :
    AnalyticAt ℂ (fun t' => R.lift x₀ (ψ.symm t')) t :=
  analyticAt_pi_iff.2 fun q => holoAt_compat hψ (R.holo x₀ q) ht hU

def NChart.snc {P : Ideal (MRing J)} (R : AnLogRes P ⊤ n) {L : LocPot R.X} {s : R.X → R.X → ℂ} {x₀ : R.X}
    {ψ : OpenPartialHomeomorph R.X (Fin n → ℂ)} {a : ℕ} {M : ℝ} (h : NChart R.A (R.U x₀) L s x₀ ψ a M)
    (Bd : Set ((Σ k, J k) → ℂ)) (hBd : ∀ x ∈ R.U x₀, R.lift x₀ x ∈ Bd ↔ x ∈ bdry s) : SncChart P n Bd where
  γ t := R.lift x₀ (ψ.symm t)
  a := a
  a_le := h.2.2.2.1
  analytic t ht := analyticAt_lift R h.1 x₀ (h.2.2.2.2 t ht).1 (h.2.2.2.2 t ht).2.1
  mem t ht := R.mem _ _ (h.2.2.2.2 t ht).2.1
  immersion t ht v := by
    rintro ⟨c, hc⟩
    obtain ⟨htt, hxU, -⟩ := h.2.2.2.2 t ht
    have hγ := analyticAt_lift R h.1 x₀ htt hxU
    obtain ⟨j, hj⟩ := R.A.cover (ψ.symm t)
    choose p hp using (R.mem _ _ (R.mem_U (ψ.symm t))).1
    have himm := R.immersion _ (not_mem_top _) p hp j hj
    have hpγ : ∀ k, R.lift x₀ (ψ.symm t) ⟨k, p k⟩ ≠ 0 := by
      intro k
      obtain ⟨c', hc', h'⟩ := R.compat _ x₀ _ ⟨R.mem_U _, hxU⟩
      have := hp k
      rw [h'] at this
      exact right_ne_zero_of_mul this
    have hk := PosFs.fderiv_affCoord_torus p hγ.differentiableAt hpγ hc
    have hτ : AnalyticAt ℂ (R.A.chart j ∘ ψ.symm) t := (h.1 j).2 t ⟨htt, hj⟩
    have hF : DifferentiableAt ℂ (fun y => affCoord p (R.lift (ψ.symm t) ((R.A.chart j).symm y)))
        ((R.A.chart j ∘ ψ.symm) t) := by
      refine differentiableAt_pi.2 fun q => ?_
      have hmem : (R.A.chart j) (ψ.symm t) ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U (ψ.symm t) :=
        ⟨(R.A.chart j).map_source hj, by
          simp only [Set.mem_preimage, (R.A.chart j).left_inv hj]; exact R.mem_U _⟩
      have hd := (R.holo _ q j _ hmem).div (R.holo _ ⟨q.1, p q.1⟩ j _ hmem) (by
        simp only [Function.comp, (R.A.chart j).left_inv hj]
        exact hp q.1)
      exact hd.differentiableAt
    have hev : (fun t' => affCoord p (R.lift x₀ (ψ.symm t'))) =ᶠ[𝓝 t]
        (fun y => affCoord p (R.lift (ψ.symm t) ((R.A.chart j).symm y))) ∘ (R.A.chart j ∘ ψ.symm) := by
      filter_upwards [(ψ.continuousAt_symm htt).preimage_mem_nhds
        ((((R.isOpen_U x₀).inter (R.isOpen_U (ψ.symm t))).inter (R.A.chart j).open_source).mem_nhds
          ⟨⟨hxU, R.mem_U _⟩, hj⟩)] with t' ht'
      obtain ⟨c', hc', h'⟩ := R.compat x₀ (ψ.symm t) _ ht'.1
      have h3 : ψ.symm t' ∈ (R.A.chart j).source := ht'.2
      funext q
      simp only [affCoord, Function.comp, (R.A.chart j).left_inv h3]
      rw [h']
      exact mul_div_mul_left _ _ (hc' q.1)
    rw [hev.fderiv_eq, fderiv_comp t hF hτ.differentiableAt] at hk
    have hmem : fderiv ℂ (R.A.chart j ∘ ψ.symm) t v ∈
        (fderiv ℂ (fun y => affCoord p (R.lift (ψ.symm t) ((R.A.chart j).symm y))) (R.A.chart j (ψ.symm t))).ker := hk
    rw [himm] at hmem
    have h0 : fderiv ℂ (R.A.chart j ∘ ψ.symm) t v = 0 := (Submodule.mem_bot _).1 hmem
    have hσ : AnalyticAt ℂ (ψ ∘ (R.A.chart j).symm) ((R.A.chart j ∘ ψ.symm) t) :=
      (h.1 j).1 _ ⟨(R.A.chart j).map_source hj, by
        simp only [Set.mem_preimage, Function.comp, (R.A.chart j).left_inv hj]; exact ψ.map_target htt⟩
    have hid : (ψ ∘ (R.A.chart j).symm) ∘ (R.A.chart j ∘ ψ.symm) =ᶠ[𝓝 t] id := by
      filter_upwards [(ψ.continuousAt_symm htt).preimage_mem_nhds ((R.A.chart j).open_source.mem_nhds hj),
        ψ.open_target.mem_nhds htt] with t' h1 h2
      have h3 : ψ.symm t' ∈ (R.A.chart j).source := h1
      simp only [Function.comp, (R.A.chart j).left_inv h3, ψ.right_inv h2, id]
    have hcc := fderiv_comp t hσ.differentiableAt hτ.differentiableAt
    rw [hid.fderiv_eq, fderiv_id] at hcc
    have := congrArg (fun f : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) => f v) hcc
    simpa [h0] using this
  injective t ht t' ht' c hc he := by
    obtain ⟨h1, h2, -⟩ := h.2.2.2.2 t ht
    obtain ⟨h1', h2', -⟩ := h.2.2.2.2 t' ht'
    have o : SameOrbit (R.lift x₀ (ψ.symm t)) (R.lift x₀ (ψ.symm t')) := ⟨c, hc, he⟩
    have := R.inj (ψ.symm t) (ψ.symm t') (not_mem_top _)
      (Cj.sameOrbit_trans (R.compat _ x₀ _ ⟨R.mem_U _, h2⟩) (Cj.sameOrbit_trans o (R.compat x₀ _ _ ⟨h2', R.mem_U _⟩)))
    rw [← ψ.right_inv h1, this, ψ.right_inv h1']
  boundary t ht := (hBd _ (h.2.2.2.2 t ht).2.1).trans (h.2.2.2.2 t ht).2.2.1

end AnalyticReference.An
end
end

noncomputable section

namespace AnalyticReference.An

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo Filter Topology Metric

variable {n : ℕ} {X : Type} [TopologicalSpace X]

theorem exp_le_logR (a : ℕ) {t : Fin n → ℂ} (ht : ‖t‖ < 1) : Real.exp 1 ≤ logR a t := by
  unfold logR
  have hs : 0 ≤ ∑ i : Fin n, (if (i : ℕ) < a then Real.log (1 / ‖t i‖ ^ 2) else 0) := by
    refine Finset.sum_nonneg fun i _ => ?_
    split_ifs
    · have h1 := norm_le_pi_norm t i
      have h2 : ‖t i‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (t i)]
      rw [one_div, Real.log_inv, neg_nonneg]
      exact Real.log_nonpos (by positivity) h2
    · exact le_rfl
  linarith

theorem one_le_of_exp_le {r : ℝ} (h : Real.exp 1 ≤ r) : 1 ≤ r ∧ 1 ≤ Real.log r := by
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp zero_le_one
  have hr : 0 < r := by linarith
  exact ⟨le_trans he h, (Real.le_log_iff_exp_le hr).mpr h⟩

theorem tame_smooth (a : ℕ) {g : (Fin n → ℂ) → ℝ}
    (hg : ∀ t ∈ ball (0 : Fin n → ℂ) 1, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g t) : Tame a g := by
  have hon : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g (ball 0 1) := fun t ht => (hg t ht).contDiffWithinAt
  have hK : IsCompact (closedBall (0 : Fin n → ℂ) (1 / 2)) := isCompact_closedBall _ _
  have hsub : closedBall (0 : Fin n → ℂ) (1 / 2) ⊆ ball 0 1 := closedBall_subset_ball (by norm_num)
  obtain ⟨B1, hB1⟩ := hK.exists_bound_of_continuousOn (hon.continuousOn.mono hsub)
  obtain ⟨B2, hB2⟩ := hK.exists_bound_of_continuousOn
    ((hon.continuousOn_fderiv_of_isOpen isOpen_ball (by exact_mod_cast le_top)).mono hsub)
  refine ⟨1 / 2, max (max B1 B2) 0, by norm_num, by norm_num, le_max_right _ _, fun t ht _ => ?_⟩
  have htK : t ∈ closedBall (0 : Fin n → ℂ) (1 / 2) := by
    rw [mem_closedBall, dist_zero_right]
    exact ht.le
  have hR := exp_le_logR a (t := t) (by linarith)
  obtain ⟨hR1, hL1⟩ := one_le_of_exp_le hR
  have hC : 0 ≤ max (max B1 B2) 0 := le_max_right _ _
  refine ⟨hg t (hsub htK), ?_, ?_⟩
  · have h1 := hB1 t htK
    rw [Real.norm_eq_abs] at h1
    calc |g t| ≤ max (max B1 B2) 0 := le_trans h1 (le_trans (le_max_left _ _) (le_max_left _ _))
      _ = max (max B1 B2) 0 * 1 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hL1 hC
  · have h1 := hB2 t htK
    have h2 : 1 ≤ logR a t ^ max (max B1 B2) 0 := Real.one_le_rpow hR1 hC
    have h3 : 1 ≤ Real.exp (logR a t / 2) := Real.one_le_exp (by linarith)
    calc ‖fderiv ℝ g t‖ ≤ max (max B1 B2) 0 :=
          le_trans h1 (le_trans (le_max_right _ _) (le_max_left _ _))
      _ = max (max B1 B2) 0 * 1 * 1 := by ring
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left h2 hC) h3 zero_le_one (by positivity)

theorem exp_le_rW {L : LocPot X} {s : X → X → ℂ} (hn : ∀ y, logNormSec L s y ≤ 0) (y : X) :
    Real.exp 1 ≤ rW L s y := by
  have := hn y
  unfold rW
  linarith

variable {A : FinHolAtlas n X} {L : LocPot X} {s : X → X → ℂ} {U : X → Set X} {ph : X → ℝ}

theorem NChart.symm_zero {V : Set X} {x₀ : X} {ψ : OpenPartialHomeomorph X (Fin n → ℂ)} {a : ℕ} {M : ℝ}
    (h : NChart A V L s x₀ ψ a M) : ψ.symm 0 = x₀ := by
  rw [← h.2.2.1]
  exact ψ.left_inv h.2.1

theorem NChart.zero_of_not_mem {V : Set X} {x₀ : X} {ψ : OpenPartialHomeomorph X (Fin n → ℂ)} {a : ℕ} {M : ℝ}
    (h : NChart A V L s x₀ ψ a M) (hx : x₀ ∉ bdry s) : a = 0 := by
  by_contra ha
  have h0 := (h.2.2.2.2 0 (mem_ball_self one_pos)).2.2.1
  rw [NChart.symm_zero h] at h0
  have hpos : 0 < a := Nat.pos_of_ne_zero ha
  exact hx (h0.mpr ⟨⟨0, lt_of_lt_of_le hpos h.2.2.2.1⟩, hpos, rfl⟩)

theorem smoothOn_of_tame (hT : ∀ x, ∃ ψ a M, NChart A (U x) L s x ψ a M ∧ Tame a fun t => ph (ψ.symm t)) :
    A.SmoothOn (bdry s)ᶜ ph := by
  intro j y hy
  obtain ⟨hyt, hyb⟩ := hy
  obtain ⟨ψ, a, M, hN, hTm⟩ := hT ((A.chart j).symm y)
  have ha : a = 0 := hN.zero_of_not_mem hyb
  subst ha
  obtain ⟨ε, C, hε, -, -, hTt⟩ := hTm
  have hxs : (A.chart j).symm y ∈ ψ.source := hN.2.1
  have hs0 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => ph (ψ.symm t)) (ψ ((A.chart j).symm y)) := by
    rw [hN.2.2.1]
    exact (hTt 0 (by simpa using hε) (fun i hi => absurd hi (Nat.not_lt_zero _))).1
  have hcomp : AnalyticAt ℂ (ψ ∘ (A.chart j).symm) y := (hN.1 j).1 y ⟨hyt, hxs⟩
  have hsm : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ψ ∘ (A.chart j).symm) y :=
    (hcomp.contDiffAt).restrict_scalars ℝ
  have heq : (fun t => ph (ψ.symm t)) ∘ (ψ ∘ (A.chart j).symm) =ᶠ[𝓝 y] ph ∘ (A.chart j).symm := by
    have hopen : (A.chart j).target ∩ (A.chart j).symm ⁻¹' ψ.source ∈ 𝓝 y :=
      ((A.chart j).isOpen_inter_preimage_symm ψ.open_source).mem_nhds ⟨hyt, hxs⟩
    filter_upwards [hopen] with w hw
    simp [Function.comp, ψ.left_inv hw.2]
  exact ((hs0.comp y hsm).congr_of_eventuallyEq heq.symm).contDiffWithinAt

theorem local_of_tame (hn : ∀ y, logNormSec L s y ≤ 0) {V : Set X} {x : X}
    {ψ : OpenPartialHomeomorph X (Fin n → ℂ)} {a : ℕ} {M : ℝ} (h : NChart A V L s x ψ a M)
    (hT : Tame a fun t => ph (ψ.symm t)) :
    ∃ (V' : Set X) (c : ℝ), IsOpen V' ∧ x ∈ V' ∧ V' ⊆ ψ.source ∧ ∀ x' ∈ V', x' ∉ bdry s →
      |ph x'| ≤ c * Real.log (rW L s x') ∧
      ‖fderiv ℝ (ph ∘ ψ.symm) (ψ x')‖ ≤ c * rW L s x' ^ c * Real.exp (rW L s x' / 2) := by
  obtain ⟨ε, C, hε, hε1, hC, hTt⟩ := hT
  set K : ℝ := 1 + max M 0 with hK
  have hM0 : 0 ≤ max M 0 := le_max_right _ _
  have hMM : M ≤ max M 0 := le_max_left _ _
  have hK1 : 1 ≤ K := by rw [hK]; linarith
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK1
  set c1 := C * (1 + Real.log K) with hc1d
  set c2 := C * K ^ C * Real.exp (K / 2) with hc2d
  have hKC : 1 ≤ K ^ C := Real.one_le_rpow hK1 hC
  have heK : 1 ≤ Real.exp (K / 2) := Real.one_le_exp (by linarith)
  have hCc2 : C ≤ c2 := by
    have h1 : 1 ≤ K ^ C * Real.exp (K / 2) := by nlinarith
    calc C = C * 1 := by ring
      _ ≤ C * (K ^ C * Real.exp (K / 2)) := mul_le_mul_of_nonneg_left h1 hC
      _ = c2 := by rw [hc2d]; ring
  have hc1 : c1 ≤ max c1 c2 := le_max_left _ _
  have hc2 : c2 ≤ max c1 c2 := le_max_right _ _
  refine ⟨ψ.source ∩ ψ ⁻¹' ball 0 ε, max c1 c2, ψ.isOpen_inter_preimage isOpen_ball,
    ⟨h.2.1, by simp [h.2.2.1, hε]⟩, Set.inter_subset_left, ?_⟩
  rintro x' ⟨hxs, hxb⟩ hxbd
  have htb : ‖ψ x'‖ < ε := by simpa using hxb
  have ht1 : ψ x' ∈ ball (0 : Fin n → ℂ) 1 := by
    rw [mem_ball_zero_iff]
    linarith
  have hsy : ψ.symm (ψ x') = x' := ψ.left_inv hxs
  have hN := h.2.2.2.2 (ψ x') ht1
  rw [hsy] at hN
  have hnz : ∀ i : Fin n, (i : ℕ) < a → ψ x' i ≠ 0 := fun i hi h0 => hxbd (hN.2.2.1.mpr ⟨i, hi, h0⟩)
  have hRb : logR a (ψ x') ≤ rW L s x' + M := hN.2.2.2 hxbd
  obtain ⟨-, hbd1, hbd2⟩ := hTt (ψ x') htb hnz
  have hrW := exp_le_rW hn x'
  obtain ⟨hrW1, hlrW⟩ := one_le_of_exp_le hrW
  obtain ⟨hR1, hlR⟩ := one_le_of_exp_le (exp_le_logR a (t := ψ x') (by linarith))
  have hRK : logR a (ψ x') ≤ rW L s x' * K := by
    rw [hK]
    nlinarith
  have hlog : Real.log (logR a (ψ x')) ≤ (1 + Real.log K) * Real.log (rW L s x') := by
    have h1 : Real.log (logR a (ψ x')) ≤ Real.log (rW L s x' * K) := Real.log_le_log (by linarith) hRK
    rw [Real.log_mul (by linarith) (by linarith)] at h1
    nlinarith
  refine ⟨?_, ?_⟩
  · have hb1 : |ph x'| ≤ C * Real.log (logR a (ψ x')) := by simpa [hsy] using hbd1
    calc |ph x'| ≤ C * Real.log (logR a (ψ x')) := hb1
      _ ≤ C * ((1 + Real.log K) * Real.log (rW L s x')) := mul_le_mul_of_nonneg_left hlog hC
      _ = c1 * Real.log (rW L s x') := by rw [hc1d]; ring
      _ ≤ max c1 c2 * Real.log (rW L s x') := mul_le_mul_of_nonneg_right hc1 (by linarith)
  · have hp1 : logR a (ψ x') ^ C ≤ rW L s x' ^ C * K ^ C := by
      rw [← Real.mul_rpow (by linarith) (by linarith)]
      exact Real.rpow_le_rpow (by linarith) hRK hC
    have hp2 : Real.exp (logR a (ψ x') / 2) ≤ Real.exp (rW L s x' / 2) * Real.exp (K / 2) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      rw [hK]
      linarith
    have hp3 : rW L s x' ^ C ≤ rW L s x' ^ max c1 c2 :=
      Real.rpow_le_rpow_of_exponent_le hrW1 (le_trans hCc2 hc2)
    have hfd : ‖fderiv ℝ (ph ∘ ψ.symm) (ψ x')‖ ≤ C * logR a (ψ x') ^ C * Real.exp (logR a (ψ x') / 2) :=
      hbd2
    have hE0 : 0 ≤ Real.exp (rW L s x' / 2) := (Real.exp_pos _).le
    have hrC : 0 ≤ rW L s x' ^ C := by positivity
    calc ‖fderiv ℝ (ph ∘ ψ.symm) (ψ x')‖ ≤ C * logR a (ψ x') ^ C * Real.exp (logR a (ψ x') / 2) := hfd
      _ ≤ C * (rW L s x' ^ C * K ^ C) * (Real.exp (rW L s x' / 2) * Real.exp (K / 2)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hp1 hC) hp2 (Real.exp_pos _).le (by positivity)
      _ = c2 * rW L s x' ^ C * Real.exp (rW L s x' / 2) := by rw [hc2d]; ring
      _ ≤ max c1 c2 * rW L s x' ^ max c1 c2 * Real.exp (rW L s x' / 2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul hc2 hp3 hrC (le_trans (le_trans hC hCc2) hc2)) hE0

theorem size_of_tame [CompactSpace X] (hn : ∀ y, logNormSec L s y ≤ 0)
    (hT : ∀ x, ∃ ψ a M, NChart A (U x) L s x ψ a M ∧ Tame a fun t => ph (ψ.symm t)) :
    ∃ C : ℝ, ∀ y ∉ bdry s, |ph y| ≤ C * Real.log (rW L s y) := by
  have key : ∀ x, ∃ (V' : Set X) (c : ℝ), IsOpen V' ∧ x ∈ V' ∧ ∀ x' ∈ V', x' ∉ bdry s →
      |ph x'| ≤ c * Real.log (rW L s x') := fun x => by
    obtain ⟨ψ, a, M, h, ht⟩ := hT x
    obtain ⟨V', c, h1, h2, -, h3⟩ := local_of_tame hn h ht
    exact ⟨V', c, h1, h2, fun x' a b => (h3 x' a b).1⟩
  choose V c h1 h2 h3 using key
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover V h1 fun x _ => Set.mem_iUnion.2 ⟨x, h2 x⟩
  refine ⟨∑ x ∈ F, |c x|, fun y hy => ?_⟩
  obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 (hF (Set.mem_univ y))
  have := (one_le_of_exp_le (exp_le_rW hn y)).2
  refine (h3 x y hyx hy).trans (mul_le_mul_of_nonneg_right ((le_abs_self _).trans ?_) (by linarith))
  exact Finset.single_le_sum (f := fun x => |c x|) (fun _ _ => abs_nonneg _) hx

theorem pshOn_of_local {V : Set X} (P : LocPot X)
    (hP : ∀ x z, z ∈ P.U x → ∃ W : Set X, IsOpen W ∧ z ∈ W ∧ ∃ G : X → ℂ, A.HoloOn W G ∧
      ∀ w ∈ W ∩ P.U x ∩ P.U z, P.φ x w - P.φ z w = (G w).re)
    (h : ∀ z ∈ V, ∃ ψ : OpenPartialHomeomorph X (Fin n → ℂ), IsCompatChart A ψ ∧ z ∈ ψ.source ∧ ψ z = 0 ∧
      PshAt0 fun t => P.φ z (ψ.symm t)) : IsPshOn A V P := by
  intro x j y hy w
  obtain ⟨hyt, hyU, hyV⟩ := hy
  obtain ⟨ψ, hψc, hzs, hz0, hpsh⟩ := h _ hyV
  obtain ⟨Wd, hWo, hzW, G, hG, hdiff⟩ := hP x _ hyU
  have hτ : AnalyticAt ℂ (ψ ∘ (A.chart j).symm) y := (hψc j).1 y ⟨hyt, hzs⟩
  have hτy : (ψ ∘ (A.chart j).symm) y = 0 := hz0
  have hGa : AnalyticAt ℂ (G ∘ (A.chart j).symm) y := hG j y ⟨hyt, hzW⟩
  have hg2 : ContDiffAt ℝ 2 (fun t => P.φ ((A.chart j).symm y) (ψ.symm t)) ((ψ ∘ (A.chart j).symm) y) := by
    rw [hτy]
    exact hpsh.1
  have hgc : ContDiffAt ℝ 2 ((fun t => P.φ ((A.chart j).symm y) (ψ.symm t)) ∘ (ψ ∘ (A.chart j).symm)) y :=
    hg2.comp y ((hτ.contDiffAt).restrict_scalars ℝ)
  have hre : ContDiffAt ℝ 2 (fun y' => ((G ∘ (A.chart j).symm) y').re) y :=
    (Complex.reCLM.contDiff.contDiffAt).comp y ((hGa.contDiffAt).restrict_scalars ℝ)
  have hN : (A.chart j).target ∩ (A.chart j).symm ⁻¹'
      (Wd ∩ P.U x ∩ P.U ((A.chart j).symm y) ∩ ψ.source) ∈ 𝓝 y :=
    ((A.chart j).isOpen_inter_preimage_symm
      (((hWo.inter (P.isOpen_U x)).inter (P.isOpen_U _)).inter ψ.open_source)).mem_nhds
      ⟨hyt, ⟨⟨hzW, hyU⟩, P.mem_U _⟩, hzs⟩
  have heq : (P.φ x ∘ (A.chart j).symm) =ᶠ[𝓝 y] fun y' =>
      ((fun t => P.φ ((A.chart j).symm y) (ψ.symm t)) ∘ (ψ ∘ (A.chart j).symm)) y' +
        1 * ((G ∘ (A.chart j).symm) y').re := by
    filter_upwards [hN] with y' hy'
    obtain ⟨-, ⟨⟨hW', hx'⟩, hz'⟩, hs'⟩ := hy'
    have := hdiff _ ⟨⟨hW', hx'⟩, hz'⟩
    simp only [Function.comp, ψ.left_inv hs', one_mul]
    linarith
  rw [levi_congr heq, levi_add_smul 1 hgc hre, levi_re_analytic hGa, levi_comp w hτ hg2, hτy]
  simpa using hpsh.2 _

end AnalyticReference.An
end
end

noncomputable section

namespace AnalyticReference.An

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo Filter Topology Metric
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.PB

variable {n : ℕ} {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {P : Ideal (MRing J)}

theorem isLiftSys (R : AnLogRes P ⊤ n) : Cj.IsLiftSys R.A P R.U R.lift :=
  ⟨R.isOpen_U, R.mem_U, R.holo, R.mem, R.compat, fun z hz => R.surj z hz (not_mem_top _),
    fun x x' h => R.inj x x' (not_mem_top _) h, fun x p hp j hj => R.immersion x (not_mem_top _) p hp j hj⟩

def IsMember (R : AnLogRes P ⊤ n) (L : LocPot R.X) (s : R.X → R.X → ℂ) (d : K → ℤ) (u : R.X → ℝ) (cen : Prop)
    (ph : R.X → ℝ) (phT : ℝ → R.X → ℝ) (line : ℝ → HermLine J) (C₅ C t₀ : ℝ) : Prop :=
  IsSingWeight R.A L s (potOf R (fsHerm J d)) ph C₅ ∧
  IsRegFamily R.A (potOf R (fsHerm J fun _ => 1)) L s (potOf R (fsHerm J d)) ph phT C t₀ ∧
  IsRegFamilyC2 R.A s ph phT ∧ (∀ x ∉ bdry s, ph x = u x) ∧
  (∀ t, (line t).a = d ∧ IsSmoothHerm (line t) ∧ IsConjInvariantH (line t)) ∧
  (∀ t, 0 < t → t ≤ t₀ → ∀ x, Real.log ((line t).h (R.lift x x)) =
    Real.log ((fsHerm J d).h (R.lift x x)) + phT t x) ∧
  (cen → ∀ t, IsPsh R.A ((potOf R (fsHerm J d) + LocPot.ofFun (phT t)).rsmul (-1)) ∧
    IsPsh R.A (potOf R (fsHerm J d) + LocPot.ofFun (phT t)))

theorem exists_line (R : AnLogRes P ⊤ n) (c : R.X → R.X)
    (hc : ∀ x, SameOrbit (R.lift (c x) (c x)) (Cj.cj (R.lift x x))) (d : K → ℤ) (f : R.X → ℝ) (hf : R.A.Smooth f)
    (hfc : ∀ x, f (c x) = f x) : ∃ B : HermLine J, B.a = d ∧ IsSmoothHerm B ∧ IsConjInvariantH B ∧
      ∀ x, Real.log (B.h (R.lift x x)) = Real.log ((fsHerm J d).h (R.lift x x)) + f x := by
  obtain ⟨B, a0, hs, hl⟩ := exists_hermLine_log_eq_of_smooth _ _ _ n R f hf
  have hfs : IsSmoothHerm (fsHerm J d) := StepW.fsHerm_isSmoothHerm K J d
  have hmem : ∀ x, ∀ k, ∃ i, R.lift x x ⟨k, i⟩ ≠ 0 := fun x => (R.mem x x (R.mem_U x)).1
  have hB : ∀ x, Real.log ((Cj.conjAvg B).h (R.lift x x)) = f x := fun x => by
    rw [Cj.conjAvg_log _ (hmem x), ← FA.deg0_orbit B a0 (hc x), hl, hl, hfc]
    ring
  refine ⟨(fsHerm J d).tensor (Cj.conjAvg B), ?_, ?_, fun z => ?_, fun x => ?_⟩
  · show d + B.a = d
    rw [a0, add_zero]
  · exact ContDiffOn.mul hfs (Cj.conjAvg_smooth hs)
  · show (fsHerm J d).h _ * (Cj.conjAvg B).h _ = (fsHerm J d).h _ * (Cj.conjAvg B).h _
    rw [Cj.fs_conj d z, Cj.conjAvg_conj B z]
  · show Real.log ((fsHerm J d).h _ * (Cj.conjAvg B).h _) = _
    rw [Real.log_mul ((fsHerm J d).pos _ (hmem x)).ne' ((Cj.conjAvg B).pos _ (hmem x)).ne', hB]

theorem exists_member (hR : RegGlobalStatement) (R : AnLogRes P ⊤ n) (L : LocPot R.X) (s : R.X → R.X → ℂ) {nb : ℕ}
    (m : Fin nb → ℕ) (W : Fin nb → Set R.X) (hL : IsPotential R.A L) (hs : IsSection R.A L s)
    (snc : IsSNC R.A L s m W) (hn : ∀ y, logNormSec L s y ≤ 0)
    (hcb : ∀ x x', SameOrbit (R.lift x' x') (Cj.cj (R.lift x x)) → (x' ∈ bdry s ↔ x ∈ bdry s) ∧ rW L s x' = rW L s x)
    (d : K → ℤ) (u : R.X → ℝ) (cen : Prop)
    (huc : ∀ x x', SameOrbit (R.lift x' x') (Cj.cj (R.lift x x)) → u x' = u x)
    (hT : ∀ x, ∃ ψ a M, NChart R.A (R.U x) L s x ψ a M ∧ Tame a fun t => u (ψ.symm t))
    (hP : ∀ x ∉ bdry s, ∃ ψ : OpenPartialHomeomorph R.X (Fin n → ℂ), IsCompatChart R.A ψ ∧ x ∈ ψ.source ∧ ψ x = 0 ∧
      PshAt0 (fun t => Real.log ((fsHerm J d).h (R.lift x (ψ.symm t))) + u (ψ.symm t)) ∧
      (cen → PshAt0 fun t => -1 * (Real.log ((fsHerm J d).h (R.lift x (ψ.symm t))) + u (ψ.symm t)))) :
    ∃ ph phT line C₅ C t₀, IsMember R L s d u cen ph phT line C₅ C t₀ := by
  obtain ⟨hA, hfs, hΘ⟩ := fs_pos_potential K J P n R
  have hfd : IsSmoothHerm (fsHerm J d) := StepW.fsHerm_isSmoothHerm K J d
  have hth := hA _ hfd
  have hsys := isLiftSys R
  obtain ⟨c, hspec, hcont, hinv⟩ := GlobalTheory.T.lift_system_complex_conjugation hsys
  have hanal := GlobalTheory.T.conjugation_antiholomorphic_charts hsys c hspec hcont
  have hsm := smoothOn_of_tame hT
  obtain ⟨C₁, hC₁⟩ := size_of_tame hn hT
  have hpsh : IsPshOn R.A (bdry s)ᶜ (potOf R (fsHerm J d) + LocPot.ofFun u) := by
    refine pshOn_of_local _ (fun x z hz => ?_) fun z hz => ?_
    · obtain ⟨V, h1, h2, G, h3, h4⟩ := hth.2 x z z ⟨hz.1, R.mem_U z⟩
      refine ⟨V, h1, h2, G, h3, fun w hw => ?_⟩
      have := h4 w ⟨⟨hw.1.1, hw.1.2.1⟩, hw.2.1⟩
      show (potOf R (fsHerm J d)).φ x w + u w - ((potOf R (fsHerm J d)).φ z w + u w) = _
      linarith
    · obtain ⟨ψ, h1, h2, h3, h4, -⟩ := hP z hz
      exact ⟨ψ, h1, h2, h3, h4⟩
  obtain ⟨C₅, hsw⟩ := GlobalTheory.T.singular_potential_log_growth_psh n R.X R.A L s nb m W hL hs snc hn _ u C₁ hth hsm hpsh hC₁
  have hlines : ∀ (phT : ℝ → R.X → ℝ) (t₀ : ℝ), (∀ t, 0 < t → t ≤ t₀ → R.A.Smooth (phT t)) →
      (∀ t x, phT t (c x) = phT t x) → ∃ line : ℝ → HermLine J,
      (∀ t, (line t).a = d ∧ IsSmoothHerm (line t) ∧ IsConjInvariantH (line t)) ∧
      (∀ t, 0 < t → t ≤ t₀ → ∀ x, Real.log ((line t).h (R.lift x x)) =
        Real.log ((fsHerm J d).h (R.lift x x)) + phT t x) := by
    intro phT t₀ h1 h2
    have : ∀ t, ∃ B : HermLine J, (B.a = d ∧ IsSmoothHerm B ∧ IsConjInvariantH B) ∧ (0 < t → t ≤ t₀ → ∀ x,
        Real.log (B.h (R.lift x x)) = Real.log ((fsHerm J d).h (R.lift x x)) + phT t x) := fun t => by
      by_cases ht : 0 < t ∧ t ≤ t₀
      · obtain ⟨B, b1, b2, b3, b4⟩ := exists_line R c hspec d (phT t) (h1 t ht.1 ht.2) (h2 t)
        exact ⟨B, ⟨b1, b2, b3⟩, fun _ _ => b4⟩
      · exact ⟨fsHerm J d, ⟨rfl, hfd, Cj.fs_conj d⟩, fun a b => absurd ⟨a, b⟩ ht⟩
    choose line h3 h4 using this
    exact ⟨line, h3, h4⟩
  by_cases hcen : cen
  · have hneg : IsPshOn R.A (bdry s)ᶜ ((potOf R (fsHerm J d) + LocPot.ofFun u).rsmul (-1)) := by
      refine pshOn_of_local _ (fun x z hz => ?_) fun z hz => ?_
      · obtain ⟨V, h1, h2, G, h3, h4⟩ := hth.2 x z z ⟨hz.1, R.mem_U z⟩
        refine ⟨V, h1, h2, fun w => -G w, fun j y hy => (h3 j y hy).neg, fun w hw => ?_⟩
        have := h4 w ⟨⟨hw.1.1, hw.1.2.1⟩, hw.2.1⟩
        show -1 * ((potOf R (fsHerm J d)).φ x w + u w) - -1 * ((potOf R (fsHerm J d)).φ z w + u w) = _
        rw [Complex.neg_re]
        linarith
      · obtain ⟨ψ, h1, h2, h3, -, h4⟩ := hP z hz
        exact ⟨ψ, h1, h2, h3, h4 hcen⟩
    obtain ⟨u', C₀, hu', heq, p1, p2, s1, r1, c1⟩ := FA.central_regular R.A (potOf R (fsHerm J fun _ => 1)) L s m W
      hL hs snc hn (hA _ hfs) hΘ _ u C₅ hsw hneg
    have hc1 := Cj.smooth_continuous hu'
    have hd : Dense (bdry s)ᶜ := interior_eq_empty_iff_dense_compl.1 (LeviFormBoundaryTopology.interior_bdry_eq_empty hs snc)
    have hcp : ∀ y, u' (c y) = u' y :=
      congrFun (Continuous.ext_on hd (hc1.comp hcont) hc1 fun y hy => by
        have hy' : c y ∉ bdry s := fun h => hy ((hcb _ _ (hspec y)).1.1 h)
        show u' (c y) = u' y
        rw [heq _ hy', heq _ hy, huc _ _ (hspec y)])
    obtain ⟨line, l1, l2⟩ := hlines (fun _ => u') (Real.exp (-Real.exp 1)) (fun _ _ _ => hu') fun _ => hcp
    exact ⟨u', fun _ => u', line, C₀, C₀, _, s1, r1, c1, heq, l1, l2, fun _ _ => ⟨p2, p1⟩⟩
  · obtain ⟨B, hB⟩ := GlobalTheory.T.adapted_atlas_snc_section R.A L s m W hL hs snc hn
    obtain ⟨C₆, hg⟩ := GlobalTheory.T.adapted_atlas_smooth_potential_local n R.X R.A B L s nb m W hL hs snc hn hB u hsm fun x => by
      obtain ⟨ψ, a, M, h, ht⟩ := hT x
      obtain ⟨V', c, h1, h2, h3, h4⟩ := local_of_tame hn h ht
      exact ⟨ψ, V', c, h.1, h1, h2, h3, fun x' a b => (h4 x' a b).2⟩
    obtain ⟨m₁, -, -⟩ := enlarging_constants_smooth_members n R.X R.A (potOf R (fsHerm J fun _ => 1)) L s nb m W
      hL hs snc hn (hA _ hfs) hΘ
    have hsw' := m₁ _ _ _ _ (le_max_left C₅ C₆) hsw
    obtain ⟨C, t₀, phT, r, c2⟩ := hR R.A B _ L s m W (hA _ hfs) hΘ hL hs snc hn hB _ u _ hsw' (hg _ (le_max_right _ _))
    have hthc := GlobalTheory.T.lift_system_real_structure hsys c hspec hcont hanal (fsHerm J d) (Cj.fs_conj d) (potOf R (fsHerm J d)) fun x =>
      ⟨Set.univ, isOpen_univ, trivial, fun _ => 0, fun _ => analyticOnNhd_const,
        fun z _ => (sub_self _).trans Complex.zero_re.symm⟩
    obtain ⟨C', t', r', c'⟩ := GlobalTheory.T.conjugation_invariant_singular_potential n R.X R.A _ L s nb m W hL hs snc hn (hA _ hfs) hΘ c hcont hinv hanal
      (fun y => (hcb _ _ (hspec y)).1) (fun y => (hcb _ _ (hspec y)).2) _ u phT C t₀ hth hthc
      (fun y _ => huc _ _ (hspec y)) r c2
    obtain ⟨line, l1, l2⟩ := hlines (fun t y => (phT t y + phT t (c y)) / 2) t' (fun t h0 h1 => (r'.2.2 t h0 h1).1)
      fun t x => by rw [hinv, add_comm]
    exact ⟨u, _, line, C₅, C', t', hsw, r', c', fun _ _ => rfl, l1, l2, fun h => absurd h hcen⟩

theorem IsMember.mono {R : AnLogRes P ⊤ n} {L : LocPot R.X} {s : R.X → R.X → ℂ} {nb : ℕ}
    {m : Fin nb → ℕ} {W : Fin nb → Set R.X} (hL : IsPotential R.A L) (hs : IsSection R.A L s)
    (snc : IsSNC R.A L s m W) (hn : ∀ y, logNormSec L s y ≤ 0) {d : K → ℤ} {u : R.X → ℝ} {cen : Prop}
    {ph : R.X → ℝ} {phT : ℝ → R.X → ℝ} {line : ℝ → HermLine J} {C₅ C t₀ D₅ D T : ℝ}
    (h : IsMember R L s d u cen ph phT line C₅ C t₀) (h₅ : C₅ ≤ D₅) (hD : |C| ≤ D) (hT0 : 0 < T) (hT : T ≤ t₀)
    (hT1 : T ≤ Real.exp (-1)) : IsMember R L s d u cen ph phT line D₅ D T := by
  obtain ⟨hA, hfs, hΘ⟩ := fs_pos_potential K J P n R
  obtain ⟨m₁, m₂, -⟩ := enlarging_constants_smooth_members n R.X R.A (potOf R (fsHerm J fun _ => 1)) L s nb m W
    hL hs snc hn (hA _ hfs) hΘ
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := h
  exact ⟨m₁ _ _ _ _ h₅ a1, m₂ _ _ _ _ _ _ _ hD hT0 hT hT1 a2 a1.1, a3, a4, a5, fun t h0 h1 => a6 t h0 (h1.trans hT), a7⟩

theorem member_zero (R : AnLogRes P ⊤ n) {L : LocPot R.X} {s : R.X → R.X → ℂ} {nb : ℕ}
    {m : Fin nb → ℕ} {W : Fin nb → Set R.X} (hL : IsPotential R.A L) (hs : IsSection R.A L s)
    (snc : IsSNC R.A L s m W) (hn : ∀ y, logNormSec L s y ≤ 0) (d : K → ℤ)
    (hd : IsPosPot R.A (potOf R (fsHerm J d))) :
    ∃ C₅ C t₀, IsMember R L s d 0 False 0 (fun _ => 0) (fun _ => fsHerm J d) C₅ C t₀ := by
  obtain ⟨hA, hfs, hΘ⟩ := fs_pos_potential K J P n R
  have hfd : IsSmoothHerm (fsHerm J d) := StepW.fsHerm_isSmoothHerm K J d
  obtain ⟨-, -, m₃⟩ := enlarging_constants_smooth_members n R.X R.A (potOf R (fsHerm J fun _ => 1)) L s nb m W
    hL hs snc hn (hA _ hfs) hΘ
  have hsm0 : R.A.Smooth (0 : R.X → ℝ) := fun jj => by
    show ContDiffOn ℝ _ (fun _ => (0 : ℝ)) _
    exact contDiffOn_const
  have hpsh0 : IsPsh R.A (potOf R (fsHerm J d) + LocPot.ofFun (0 : R.X → ℝ)) := by
    intro x jj z hz w
    have e1 : (potOf R (fsHerm J d) + LocPot.ofFun (0 : R.X → ℝ)).φ x ∘ (R.A.chart jj).symm =
        (potOf R (fsHerm J d)).φ x ∘ (R.A.chart jj).symm := by
      funext u
      show (potOf R (fsHerm J d)).φ x _ + (0 : ℝ) = _
      rw [add_zero]
      rfl
    rw [e1]
    by_cases hw : w = 0
    · rw [hw, levi_zero]
    · exact (hd x jj z ⟨hz.1, hz.2.1⟩ w hw).le
  obtain ⟨C₀, s0, r0, c0⟩ := m₃ _ 0 (hA _ hfd) hsm0 hpsh0
  exact ⟨C₀, C₀, _, s0, r0, c0, fun _ _ => rfl, fun _ => ⟨rfl, hfd, Cj.fs_conj d⟩,
    fun _ _ _ _ => (add_zero _).symm, False.elim⟩

theorem common_members {σ : Type} [Finite σ] {R : AnLogRes P ⊤ n} {L : LocPot R.X} {s : R.X → R.X → ℂ} {nb : ℕ}
    {m : Fin nb → ℕ} {W : Fin nb → Set R.X} (hL : IsPotential R.A L) (hs : IsSection R.A L s)
    (snc : IsSNC R.A L s m W) (hn : ∀ y, logNormSec L s y ≤ 0) {d : σ → K → ℤ} {u : σ → R.X → ℝ} {cen : σ → Prop}
    {ph : σ → R.X → ℝ} {phT : σ → ℝ → R.X → ℝ} {line : σ → ℝ → HermLine J}
    (h : ∀ a, ∃ C₅ C t₀, IsMember R L s (d a) (u a) (cen a) (ph a) (phT a) (line a) C₅ C t₀) :
    ∃ C₅ C t₀, ∀ a, IsMember R L s (d a) (u a) (cen a) (ph a) (phT a) (line a) C₅ C t₀ := by
  choose C₅ C t₀ hm using h
  obtain ⟨D₅, hD₅⟩ := FA.common_bound C₅
  obtain ⟨D, hD⟩ := FA.common_bound fun a => |C a|
  obtain ⟨T, hT0, hT⟩ := FA.common_scale (fun o : Option σ => o.elim (Real.exp (-1)) t₀) (by
    rintro (_ | p)
    · exact Real.exp_pos _
    · exact (hm p).2.1.1)
  exact ⟨D₅, D, T, fun a => (hm a).mono hL hs snc hn (hD₅ a) (hD a) hT0 (hT (some a)) (hT none)⟩

end AnalyticReference.An
