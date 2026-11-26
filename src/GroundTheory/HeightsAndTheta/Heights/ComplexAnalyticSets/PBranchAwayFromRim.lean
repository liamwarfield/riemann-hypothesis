module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetSumMeasurable
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveRegularOffFinite
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLelongLimit
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTubeFormCompare

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchAwayFromRim
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Filter Topology

theorem BranchAwayFromRim.proof (hex : NormalModelExists.Statement)
    (hprop : NormalModelProper.Statement) (hlift : BranchLift.Statement)
    (hirr : NormalLocallyIrreducible.Statement) (hext : BranchContainsNormalPoint.Statement) :
    BranchAwayFromRim.Statement := by
  intro n k J u p x m γ hJ hdim hu hcov hdisj b
  obtain ⟨N, hN, hcovN⟩ := hcov
  obtain ⟨M⟩ := hex n J hJ
  set Z' := zeroSetIn M.ideal with hZ'
  have hcontν : Continuous (firstCoords : (Fin n ⊕ Fin M.m → ℂ) → Fin n → ℂ) :=
    continuous_pi fun i => continuous_apply _
  have hZc : IsClosed Z' := by
    have hZ'eq : Z' = ⋂ q ∈ M.ideal, {z | eval z q = 0} := by ext z; simp [Z', zeroSetIn]
    rw [hZ'eq]
    exact isClosed_biInter fun q _ => isClosed_eq (MvPolynomial.continuous_eval q) continuous_const
  have hνZ : ∀ w ∈ Z', firstCoords w ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet J := by
    intro w hw q hq
    have hq' : rename Sum.inl q ∈ M.ideal := by rw [← M.comap_eq] at hq; exact hq
    have := hw _ hq'
    rwa [eval_rename] at this

  choose Γ hΓd hΓZ hΓopen using fun c => hlift n k J p M (γ c) hJ hdim
  have hΓinj : ∀ c, Set.InjOn (Γ c) (Metric.ball 0 (γ c).radius) := by
    intro c s hs t ht hst
    apply (γ c).injOn hs ht
    rw [← (hΓZ c s hs).2, ← (hΓZ c t ht).2, hst]
  choose O hOo hOeq using fun c => hΓopen c (Metric.ball 0 (γ c).radius) subset_rfl Metric.isOpen_ball

  choose a bd hbJ hab using M.birational
  set g : MvPolynomial (Fin n) ℂ := GroundTheory.Heights₂.Heights.linForm u * ∏ i, bd i with hg
  have hgJ : g ∉ J := by
    have := hJ
    intro hgm
    rcases hJ.mem_or_mem hgm with h1 | h2
    · exact hu h1
    · obtain ⟨i, -, hi⟩ := Ideal.IsPrime.prod_mem_iff.mp h2
      exact hbJ i hi
  set h : MvPolynomial (Fin n ⊕ Fin M.m) ℂ := rename Sum.inl g with hh_def
  have hh : h ∉ M.ideal := by
    intro hm
    apply hgJ
    rw [← M.comap_eq]
    exact hm
  have heval : ∀ w : Fin n ⊕ Fin M.m → ℂ,
      eval w h = GroundTheory.Heights₂.Heights.linEval u (firstCoords w) *
        ∏ i, eval (firstCoords w) (bd i) := by
    intro w
    simp only [h, g, eval_rename, map_mul, map_prod]
    congr 1
    simp [GroundTheory.Heights₂.Heights.linForm, GroundTheory.Heights₂.Heights.linEval, firstCoords, Function.comp_def]
  have hinj : ∀ w ∈ Z', ∀ w' ∈ Z', firstCoords w = firstCoords w' → eval w h ≠ 0 → w = w' := by
    intro w hw w' hw' hνw hne
    rw [heval] at hne
    have hb : ∀ i, eval (firstCoords w) (bd i) ≠ 0 := fun i hi =>
      hne (by rw [Finset.prod_eq_zero (Finset.mem_univ i) hi, mul_zero])
    funext s
    rcases s with j | i
    · exact congrFun hνw j
    · have e1 := hw _ (hab i)
      have e2 := hw' _ (hab i)
      simp only [map_sub, map_mul, eval_rename, eval_X] at e1 e2
      have c1 : w ∘ Sum.inl = firstCoords w := rfl
      have c2 : w' ∘ Sum.inl = firstCoords w := by rw [hνw]; rfl
      rw [c1] at e1
      rw [c2] at e2
      apply mul_left_cancel₀ (hb i)
      linear_combination e1 - e2

  by_contra hcon
  push Not at hcon
  set r := (γ b).radius with hr
  have hseq : ∀ j : ℕ, ∃ τ ∈ Metric.ball (0 : Fin k → ℂ) r,
      (γ b).toFun τ ∈ Metric.ball x (1 / ((j : ℝ) + 1)) ∧ r - 1 / ((j : ℝ) + 1) < ‖τ‖ := by
    intro j
    have hpos : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
    exact hcon _ hpos _ (by linarith)
  choose τ hτr hτx hτn using hseq
  have hmem : ∀ j, Γ b (τ j) ∈ {w | w ∈ Z' ∧ firstCoords w ∈ Metric.closedBall x 1} := by
    intro j
    refine ⟨(hΓZ b (τ j) (hτr j)).1, ?_⟩
    rw [(hΓZ b (τ j) (hτr j)).2, Metric.mem_closedBall]
    have h1 := Metric.mem_ball.mp (hτx j)
    have h2 : 1 / ((j : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    linarith
  obtain ⟨xh, hxcl, φ, hφ, hlim⟩ :=
    tendsto_subseq_of_bounded (hprop n J M _ Metric.isBounded_closedBall) hmem
  have hlim' : Tendsto (fun j => Γ b (τ (φ j))) atTop (𝓝 xh) := hlim
  have hxZ : xh ∈ Z' := hZc.closure_subset_iff.mpr (by exact fun w hw => hw.1) hxcl
  have h1j : Tendsto (fun j => 1 / ((φ j : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
  have hγlim : Tendsto (fun j => (γ b).toFun (τ (φ j))) atTop (𝓝 x) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun j => dist_nonneg) (fun j => (Metric.mem_ball.mp (hτx (φ j))).le) h1j
  have hνx : firstCoords xh = x := by
    refine tendsto_nhds_unique ((hcontν.tendsto xh).comp hlim') ?_
    refine hγlim.congr fun j => ?_
    exact ((hΓZ b _ (hτr _)).2).symm

  have hUN : firstCoords ⁻¹' N ∈ 𝓝 xh :=
    hcontν.continuousAt.preimage_mem_nhds (by rw [hνx]; exact hN)
  obtain ⟨B, hBo, hxB, hBU, hpre, hdense⟩ :=
    hirr (Fin n ⊕ Fin M.m) M.ideal h xh M.isPrime M.isIntegrallyClosed hh hxZ _ hUN
  set P := (Z' ∩ B) \ {z | eval z h = 0} with hP

  have hPcov : ∀ q ∈ P, ∃ c, q ∈ Γ c '' Metric.ball 0 (γ c).radius := by
    rintro q ⟨⟨hqZ, hqB⟩, hqh⟩
    obtain ⟨c, hc⟩ := Set.mem_iUnion.mp (hcovN ⟨hνZ q hqZ, hBU hqB⟩)
    obtain ⟨t, ht, hteq⟩ := hc
    refine ⟨c, t, ht, ?_⟩
    have hν : firstCoords (Γ c t) = firstCoords q := by rw [(hΓZ c t ht).2, hteq]
    refine hinj _ (hΓZ c t ht).1 q hqZ hν ?_
    rw [heval, hν, ← heval]
    exact hqh
  have hPdisj : ∀ q ∈ P, ∀ c c', c ≠ c' → q ∈ Γ c '' Metric.ball 0 (γ c).radius →
      q ∉ Γ c' '' Metric.ball 0 (γ c').radius := by
    rintro q ⟨-, hqh⟩ c c' hcc' ⟨t, ht, rfl⟩ ⟨t', ht', hteq⟩
    have h1 : firstCoords (Γ c t) ∈ (γ c).image := ⟨t, ht, ((hΓZ c t ht).2).symm⟩
    have h2 : firstCoords (Γ c t) ∈ (γ c').image :=
      ⟨t', ht', by rw [← (hΓZ c' t' ht').2, hteq]⟩
    have h3 := hdisj c c' hcc' ⟨h1, h2⟩
    apply hqh
    show eval (Γ c t) h = 0
    rw [heval]
    rw [show GroundTheory.Heights₂.Heights.linEval u (firstCoords (Γ c t)) = 0 from h3, zero_mul]

  have hPsub : P ⊆ Γ b '' Metric.ball 0 r := by
    have hsplit := isPreconnected_iff_subset_of_disjoint.mp hpre (O b) (⋃ c ∈ {c | c ≠ b}, O c)
      (hOo b) (isOpen_biUnion fun c _ => hOo c) ?_ ?_
    · rcases hsplit with hs | hs
      · intro q hq
        rw [hOeq b]
        exact ⟨hq.1.1, hs hq⟩
      · exfalso
        obtain ⟨j, hjB⟩ := (hlim'.eventually (hBo.mem_nhds hxB)).exists
        have hw0 : Γ b (τ (φ j)) ∈ Γ b '' Metric.ball 0 r := ⟨_, hτr _, rfl⟩
        have hw0O : Γ b (τ (φ j)) ∈ O b := by
          have := hw0
          rw [hOeq b] at this
          exact this.2
        have hw0P := hdense ⟨(hΓZ b _ (hτr _)).1, hjB⟩
        obtain ⟨q, hqO, hqP⟩ := mem_closure_iff.mp hw0P (O b) (hOo b) hw0O
        obtain ⟨c, hc, hqc⟩ := Set.mem_iUnion₂.mp (hs hqP)
        have hqb : q ∈ Γ b '' Metric.ball 0 r := by rw [hOeq b]; exact ⟨hqP.1.1, hqO⟩
        have hqc' : q ∈ Γ c '' Metric.ball 0 (γ c).radius := by rw [hOeq c]; exact ⟨hqP.1.1, hqc⟩
        exact hPdisj q hqP b c (Ne.symm hc) hqb hqc'
    · intro q hq
      obtain ⟨c, hc⟩ := hPcov q hq
      rw [hOeq c] at hc
      by_cases hcb : c = b
      · subst hcb
        exact Or.inl hc.2
      · exact Or.inr (Set.mem_biUnion hcb hc.2)
    · ext q
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      intro hqP hqb hqv
      obtain ⟨c, hc, hqc⟩ := Set.mem_iUnion₂.mp hqv
      have h1 : q ∈ Γ b '' Metric.ball 0 r := by rw [hOeq b]; exact ⟨hqP.1.1, hqb⟩
      have h2 : q ∈ Γ c '' Metric.ball 0 (γ c).radius := by rw [hOeq c]; exact ⟨hqP.1.1, hqc⟩
      exact hPdisj q hqP b c (Ne.symm hc) h1 h2

  obtain ⟨σ0, hσ0, hσx⟩ := hext (Fin n ⊕ Fin M.m) M.ideal h xh k r (Γ b) B M.isPrime
    M.isIntegrallyClosed hh hxZ (hΓd b) (hΓinj b) (fun t ht => (hΓZ b t ht).1)
    (hBo.mem_nhds hxB) hPsub

  have hσ0' : ‖σ0‖ < r := mem_ball_zero_iff.mp hσ0
  set δ := (r - ‖σ0‖) / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hVsub : Metric.ball σ0 δ ⊆ Metric.ball 0 r := by
    intro t ht
    rw [mem_ball_zero_iff]
    have h1 : ‖t‖ ≤ ‖σ0‖ + dist t σ0 := by
      rw [dist_eq_norm]
      calc ‖t‖ = ‖σ0 + (t - σ0)‖ := by rw [add_sub_cancel]
        _ ≤ ‖σ0‖ + ‖t - σ0‖ := norm_add_le _ _
    have h2 := Metric.mem_ball.mp ht
    linarith
  obtain ⟨O', hO'o, hO'eq⟩ := hΓopen b (Metric.ball σ0 δ) hVsub Metric.isOpen_ball
  have hxO' : xh ∈ O' := by
    have : xh ∈ Γ b '' Metric.ball σ0 δ := ⟨σ0, Metric.mem_ball_self hδpos, hσx⟩
    rw [hO'eq] at this
    exact this.2
  obtain ⟨j, hjO, hjδ⟩ :=
    ((hlim'.eventually (hO'o.mem_nhds hxO')).and (h1j.eventually (gt_mem_nhds hδpos))).exists
  have hjV : Γ b (τ (φ j)) ∈ Γ b '' Metric.ball σ0 δ := by
    rw [hO'eq]
    exact ⟨(hΓZ b _ (hτr _)).1, hjO⟩
  obtain ⟨t, ht, hteq⟩ := hjV
  have htτ : t = τ (φ j) := hΓinj b (hVsub ht) (hτr _) hteq
  have hn1 : ‖τ (φ j)‖ < ‖σ0‖ + δ := by
    rw [← htτ]
    have h2 := Metric.mem_ball.mp ht
    rw [dist_eq_norm] at h2
    calc ‖t‖ = ‖σ0 + (t - σ0)‖ := by rw [add_sub_cancel]
      _ ≤ ‖σ0‖ + ‖t - σ0‖ := norm_add_le _ _
      _ < ‖σ0‖ + δ := by linarith
  have hn2 := hτn (φ j)
  linarith

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPrimitiveFormSheetedLocusCutOut
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

theorem PrimitiveFormSheetedLocusCutOut.proof (hfac : PrimitiveFormFullRootFactor.Statement)
    (hiff : PrimitiveFormSheetedIffRootFull.Statement) : PrimitiveFormSheetedLocusCutOut.Statement := by
  intro σ _ X w d A hX hiso ℓ N a δ q ha hδ hq hδ0 hP hsep hQ
  obtain ⟨W, B, C, E, hW, hwW, hB, hwB, han, hCE, hroot⟩ :=
    hfac σ X w d A hX hiso ℓ N a δ q ha hδ hq hδ0 hP hsep hQ
  have hBn : ∀ᶠ z in 𝓝 w, A z ∈ B := A.continuous.continuousAt.preimage_mem_nhds (hB.mem_nhds hwB)
  have hc : ∀ F : (Fin d → ℂ) → ℂ → ℂ, AnalyticAt ℂ (fun u : (Fin d → ℂ) × ℂ => F u.1 u.2) (A w, ℓ w) →
      AnalyticAt ℂ (fun z => F (A z) (ℓ z)) w := fun F hF =>
    (show AnalyticAt ℂ (fun u : (Fin d → ℂ) × ℂ => F u.1 u.2) ((A.prod ℓ) w) from hF).comp
      ((A.prod ℓ).analyticAt w)
  refine ⟨fun z => C (A z) (ℓ z), fun z => E (A z) (ℓ z), hc C (han _ hwB _).1, hc E (han _ hwB _).2, ?_, ?_⟩
  · filter_upwards [hBn, hP] with z hz hPz hzX
    rw [hCE _ hz]
    exact hPz hzX
  · filter_upwards [hBn, hP, hiff σ X w d A ℓ N a δ q ha hδ hq hP hsep hQ, hW.mem_nhds hwW] with
      z hz hPz hsh hzW hzX hzδ
    have hr := hroot _ hz hzδ (ℓ z) (hPz hzX)
    have hs := hsh hzX hzδ W hW hzW
    exact ⟨hs.trans hr.1.symm, fun h h0 => hr.2.mp h0 (hs.mp h)⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPrimitiveFormFullRootFactor
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

theorem PrimitiveFormFullRootFactor.proof (hWin : PrimitiveFormWindow.Statement)
    (hBr : AnalyticRootBranch.Statement) (hConst : PrimitiveFormFullBranchConstant.Statement)
    (hFac : PolynomialRootPredicateFactor.Statement) : PrimitiveFormFullRootFactor.Statement := by
  intro σ _ X w d A hX hiso ℓ N a δ q ha hδ hq hδne hP hsep hQ
  obtain ⟨W, B, N', k, f, hWo, hwW, hBo, hBc, hAwB, hN'o, hcl, hf, hXN, hsph, hPW, -, haB, hδB, hqB,
    hsepB⟩ := hWin σ X w d A hX hiso ℓ N a δ q ha hδ hq hP hsep hQ
  have hex : ∃ t ∈ B, δ t ≠ 0 := by
    by_contra h
    push Not at h
    exact hδne (Filter.mem_of_superset (hBo.mem_nhds hAwB) h)
  have hloc : ∀ t₀ ∈ B, δ t₀ ≠ 0 → ∀ τ₀ : ℂ, τ₀ ^ N + ∑ j, a j t₀ * τ₀ ^ (j : ℕ) = 0 →
      ∃ (O : Set (Fin d → ℂ)) (r : (Fin d → ℂ) → ℂ), IsOpen O ∧ t₀ ∈ O ∧ ContinuousOn r O ∧ r t₀ = τ₀ ∧
        ∀ s ∈ O, r s ^ N + ∑ j, a j s * r s ^ (j : ℕ) = 0 ∧
          (PrimitiveFormRootFull X W A ℓ δ q s (r s) ↔ PrimitiveFormRootFull X W A ℓ δ q t₀ τ₀) := by
    intro t₀ ht₀ hδt₀ τ₀ hτ₀
    obtain ⟨O, r, hOo, ht₀O, hr, hrt₀, hroot⟩ :=
      hBr d N a t₀ τ₀ (fun j => haB j t₀ ht₀) (hsepB t₀ ht₀ hδt₀) hτ₀
    have hU : IsOpen (O ∩ (B ∩ δ ⁻¹' {0}ᶜ)) :=
      hOo.inter (hδB.continuousOn.isOpen_inter_preimage hBo isOpen_compl_singleton)
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU t₀ ⟨ht₀O, ht₀, hδt₀⟩
    have hsub : ∀ s ∈ Metric.ball t₀ ε, s ∈ O ∧ s ∈ B ∧ δ s ≠ 0 := fun s hs =>
      ⟨(hball hs).1, (hball hs).2.1, (hball hs).2.2⟩
    have hc := hConst σ X W N' k f d A ℓ N a δ q B (Metric.ball t₀ ε) r hWo hN'o hcl hf hXN hsph hPW hBo
      haB hδB hqB Metric.isOpen_ball (convex_ball t₀ ε).isPreconnected (fun s hs => (hsub s hs).2.1)
      (fun s hs => (hsub s hs).2.2) (fun s hs => hsepB s (hsub s hs).2.1 (hsub s hs).2.2)
      (hr.mono fun s hs => (hsub s hs).1) (fun s hs => hroot s (hsub s hs).1)
    refine ⟨Metric.ball t₀ ε, r, Metric.isOpen_ball, Metric.mem_ball_self hε,
      hr.continuousOn.mono fun s hs => (hsub s hs).1, hrt₀, fun s hs => ⟨hroot s (hsub s hs).1, ?_⟩⟩
    rw [← hrt₀]
    exact hc s hs t₀ (Metric.mem_ball_self hε)
  obtain ⟨C, E, hCE, hprod, hzero⟩ :=
    hFac d N B a δ (PrimitiveFormRootFull X W A ℓ δ q) hBo hBc haB hδB hex hsepB hloc
  exact ⟨W, B, C, E, hWo, hwW, hBo, hAwB, hCE, hprod, hzero⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRegLelongMono
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

namespace RegLelongMono

variable {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin (d + 1)) (Fin n) ℂ}

theorem chartDens_annulus_nonneg (hL : RegLogDensNonneg.Statement) (u : Fin n → ℂ) {ε : ℝ} (hε : 0 < ε)
    (x : Fin n → ℂ) {r s : ℝ} (hr : 0 < r) (y : Fin (d + 1) → ℂ) :
    0 ≤ chartDens J A ((euclBall x s \ euclBall x r).indicator fun _ => 1)
      (vecCons (logReg u ε) fun _ => logDistSq x) y := by
  unfold chartDens sheetSum
  refine finsum_nonneg fun z => finsum_nonneg fun hz => ?_
  split_ifs with h
  · beta_reduce
    by_cases hza : z ∈ euclBall x s \ euclBall x r
    · rw [Set.indicator_of_mem hza, one_mul]
      have := hL n d J A u ε x z h.choose hε (ne_of_mem_euclBall_diff hr hza) h.choose_spec
      rwa [hz.2] at this
    · rw [Set.indicator_of_notMem hza, zero_mul]
  · exact le_rfl

end RegLelongMono


open RegLelongMono in
theorem RegLelongMono.proof (hA : RegLelongAnnulus.Statement) (hL : RegLogDensNonneg.Statement) :
    RegLelongMono.Statement := by
  intro n d J A u ε x r s hJ hdim hAf hε hr hrs
  have heq := hA n d J A u ε x r s hJ hdim hAf hε hr hrs
  have hτ : 0 ≤ ∫ y, chartDens J A ((euclBall x s \ euclBall x r).indicator fun _ => 1)
      (vecCons (logReg u ε) fun _ => logDistSq x) y :=
    integral_nonneg fun y => chartDens_annulus_nonneg hL u hε x hr y
  have hrs0 : 0 ≤ r ^ (2 * d) * s ^ (2 * d) :=
    mul_nonneg (pow_nonneg hr.le _) (pow_nonneg (hr.le.trans hrs) _)
  have := mul_nonneg hrs0 hτ
  linarith

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchIntDecompose
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

noncomputable section

theorem BranchIntDecompose.proof (hPr : IndefiniteRowSideFullHecke.ComplexSets.BranchProperAtPoint.Statement)
    (hGen : ComplexSets.GenericProjectionFinite.Statement) (hSum : ChartIntSumOffHyperplane.Statement)
    (hBr : BranchChartInt.Statement) : BranchIntDecompose.Statement := by
  intro n d J u q m γ ord hJ hdim hu hcov hdisj _
  obtain ⟨N₀, hN₀, hcovN⟩ := hcov
  have hpr : ∀ b, ∃ e > 0, ∀ τ ∈ Metric.ball 0 (γ b).radius, (γ b).toFun τ ∈ Metric.ball q e →
      τ ∈ Metric.ball 0 ((γ b).radius / 2) := fun b =>
    hPr n (d + 1) J u q q m γ hJ hdim hu ⟨N₀, hN₀, hcovN⟩ hdisj b 0
      (Metric.mem_ball_self (γ b).radius_pos) (γ b).map_zero _
      (Metric.ball_mem_nhds _ (half_pos (γ b).radius_pos))
  choose e he hpe using hpr
  refine ⟨N₀ ∩ ⋂ b, Metric.ball q (e b),
    inter_mem hN₀ (iInter_mem.2 fun b => Metric.ball_mem_nhds q (he b)),
    fun f ψ hf _ hfN hψ => ?_⟩
  have hex : ∃ A : Matrix (Fin (d + 1)) (Fin n) ℂ, IsFiniteProjection J A :=
    (hGen n (d + 1) J hJ hdim).2.1
  have hAf : IsFiniteProjection J hex.choose := hex.choose_spec
  have hvar : varInt J (d + 1) f ψ = chartInt J hex.choose f ψ := by
    rw [varInt, dite_eq_left hex]
  have hbr : ∀ b, Integrable (chartDens J hex.choose ((γ b).image.indicator f) ψ) ∧
      chartInt J hex.choose ((γ b).image.indicator f) ψ =
        ReciprocityTheory.AnForm.maInt (fun k => ψ k ∘ (γ b).toFun) (f ∘ (γ b).toFun)
          (Metric.ball 0 (γ b).radius) := by
    intro b
    refine hBr n (d + 1) J hex.choose q (γ b) f ψ hJ hdim hAf hf.continuous hψ
      ⟨Metric.closedBall 0 ((γ b).radius / 2), isCompact_closedBall _ _,
        Metric.closedBall_subset_ball (half_lt_self (γ b).radius_pos), fun t ht htK => ?_⟩
    by_contra hne
    have hx := hfN (subset_tsupport f hne)
    exact htK (Metric.ball_subset_closedBall (hpe b t ht (Set.mem_iInter.1 hx.2 b)))
  have hpt : ∀ x ∈ zeroSet J, linEval u x ≠ 0 → f x = ∑ b, (γ b).image.indicator f x := by
    intro x hxZ hux
    by_cases hfx : f x = 0
    · rw [hfx]
      exact (Finset.sum_eq_zero fun b _ => by by_cases hb : x ∈ (γ b).image <;> simp [hb, hfx]).symm
    · have hxN := hfN (subset_tsupport f hfx)
      obtain ⟨b₀, hb₀⟩ := Set.mem_iUnion.1 (hcovN ⟨hxZ, hxN.1⟩)
      rw [Finset.sum_eq_single b₀
        (fun b _ hb => Set.indicator_of_notMem (fun hxb => hux (hdisj b b₀ hb ⟨hxb, hb₀⟩)) _)
        (fun h => absurd (Finset.mem_univ b₀) h), Set.indicator_of_mem hb₀]
  rw [hvar, hSum n (d + 1) J hex.choose u m f (fun b => (γ b).image.indicator f) ψ hJ hdim hAf hu hpt
    (fun b => (hbr b).1)]
  exact Finset.sum_congr rfl fun b _ => (hbr b).2

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCurveBranchLength
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

theorem localMult_ker_eval_eq_zero {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ}
    {g : MvPolynomial (Fin n) ℂ} (hg : g ∈ J) (hgq : eval q g ≠ 0) :
    localMult J (RingHom.ker (eval q)) = 0 := by
  have htop : J.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q)))) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hg)
      (IsLocalization.map_units _ (⟨g, fun h ↦ hgq (RingHom.mem_ker.1 h)⟩ : (RingHom.ker (eval q)).primeCompl))
  have hs := Ideal.Quotient.subsingleton_iff.2 htop
  rw [localMult, dite_eq_left (isPrime_ker_eval q), Module.length_eq_zero_iff.2 hs]
  rfl

theorem CurveBranchLength.proof (hN : CurveNormalisationLength.Statement)
    (hB : BranchNormalisation.Statement) : CurveBranchLength.Statement := by
  intro n I u q m c ord hrad hcov hdisj hord
  have hlin : ∀ x, eval x (linForm u) = linEval u x := fun x ↦ by simp [linForm, linEval]
  have hq0 : ∀ b, linEval u q = 0 ↔ 0 < ord b := by
    intro b
    obtain ⟨H, -, hH, hF⟩ := hord b
    have h0 := hF 0 (Metric.mem_ball_self (c b).radius_pos)
    simp only [(c b).map_zero] at h0
    rw [h0]
    simp [hH 0 (Metric.mem_ball_self (c b).radius_pos), Nat.pos_iff_ne_zero]
  by_cases hmain : linEval u q = 0 ∧ 0 < m
  swap
  · have hsum : ∑ b, ord b = 0 := Finset.sum_eq_zero fun b _ ↦ by
      by_contra hb
      exact hmain ⟨(hq0 b).2 (Nat.pos_of_ne_zero hb), Fin.pos_iff_nonempty.2 ⟨b⟩⟩
    rw [hsum]
    by_cases hu : linEval u q = 0
    · have hm : m = 0 := by by_contra hm; exact hmain ⟨hu, Nat.pos_of_ne_zero hm⟩
      subst hm
      obtain ⟨N, hNq, hsub⟩ := hcov
      have hq : q ∉ zeroSet I := fun hq ↦ by simpa using hsub ⟨hq, mem_of_mem_nhds hNq⟩
      obtain ⟨g, hg, hgq⟩ : ∃ g ∈ I, eval q g ≠ 0 := by
        by_contra h
        push Not at h
        exact hq h
      exact localMult_ker_eval_eq_zero (Ideal.mem_sup_left hg) hgq
    · exact localMult_ker_eval_eq_zero (Ideal.mem_sup_right (Ideal.subset_span rfl)) (by rwa [hlin])
  obtain ⟨hu0, hm⟩ := hmain
  have hpt : ∀ b, ∀ x ∈ (c b).image, linEval u x = 0 → x = q := by
    rintro b _ ⟨t, ht, rfl⟩ hx
    obtain ⟨H, -, hH, hF⟩ := hord b
    rw [show linEval u ((c b).toFun t) = t 0 ^ ord b * H t from hF t ht, mul_eq_zero] at hx
    have ht0 : t 0 = 0 := hx.elim eq_zero_of_pow_eq_zero fun h ↦ absurd h (hH t ht)
    have ht' : t = 0 := funext fun i ↦ by rw [Subsingleton.elim i 0]; exact ht0
    rw [ht', (c b).map_zero]
  obtain ⟨hdim, hnzd, e, he⟩ := hB n I q m c hrad hm hcov
    fun b b' hbb x hx ↦ hpt b x hx.1 (hdisj b b' hbb hx)
  have hordb : ∀ b, branchOrder (c b) (linForm u) = ord b := fun b ↦
    branchOrder_eq_of_vanishesToOrder (c b) _ _ (by simpa only [hlin] using hord b)
  have hL := hN n I q (linForm u) hrad hdim (hnzd _ fun b ↦ by rw [hordb b]; exact ENat.natCast_ne_top _)
  rw [← finsum_comp_equiv e, finsum_eq_sum_of_fintype] at hL
  simp only [(he _).1, mul_one, (he _).2, hordb] at hL
  exact_mod_cast hL

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PVarietyLelongMono
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets
open scoped ENNReal

noncomputable section

theorem zeroSetEuc_subsingleton_of_dim_zero {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (hJ : J.IsPrime)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = ((0 : ℕ) : WithBot ℕ∞))
    {z : EuclideanSpace ℂ (Fin n)} (hz : z ∈ zeroSetEuc J) :
    ∀ y ∈ zeroSetEuc J, y = z := by
  have : Ring.KrullDimLE 0 (MvPolynomial (Fin n) ℂ ⧸ J) := Ring.krullDimLE_iff.2 (le_of_eq hdim)
  have hmax : J.IsMaximal := Ideal.Quotient.maximal_of_isField _ Ring.KrullDimLE.isField_of_isDomain
  obtain ⟨p, hp⟩ := (MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton (K := ℂ)).1 hmax
  have hcoord : ∀ w ∈ zeroSetEuc J, ∀ i, w i = p i := by
    intro w hw i
    have hmem : (X i - C (p i) : MvPolynomial (Fin n) ℂ) ∈ J := by
      rw [hp, MvPolynomial.mem_vanishingIdeal_singleton_iff]
      simp
    have := hw _ hmem
    simp only [map_sub, eval_X, eval_C] at this
    exact sub_eq_zero.1 this
  intro y hy
  ext i
  rw [hcoord y hy i, hcoord z hz i]

theorem VarietyLelongMono.proof (hN : ComplexSets.LinearNoetherNormalization.Statement)
    (hW : VarWirtinger.Statement) (hM : VarLelongMono.Statement) : VarietyLelongMono.Statement := by
  intro n d J hJ hdim z hz r s hr hrs
  rcases d with _ | d
  · have hsub := zeroSetEuc_subsingleton_of_dim_zero J hJ hdim hz
    have hpt : ∀ ρ : ℝ, 0 < ρ → zeroSetEuc J ∩ Metric.ball z ρ = {z} := by
      intro ρ hρ
      ext y
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
      constructor
      · exact fun h => hsub y h.1
      · rintro rfl
        exact ⟨hz, Metric.mem_ball_self hρ⟩
    rw [hpt r hr, hpt s (hr.trans_le hrs)]
    simp [Measure.hausdorffMeasure_zero_singleton]
  · obtain ⟨A, hA⟩ := hN n (d + 1) J hdim
    obtain ⟨c, hc, hWc⟩ := hW d
    have hball : ∀ ρ : ℝ, (fun x : Fin n → ℂ => WithLp.toLp 2 x) ⁻¹' Metric.ball z ρ =
        euclBall (WithLp.ofLp z) ρ := by
      intro ρ
      ext y
      rw [Set.mem_preimage, mem_euclBall_iff, Metric.mem_ball]
    have hμ : ∀ ρ : ℝ, μH[((2 * (d + 1) : ℕ) : ℝ)] (zeroSetEuc J ∩ Metric.ball z ρ) =
        ENNReal.ofReal (c * ∫ y, chartDens J A ((euclBall (WithLp.ofLp z) ρ).indicator fun _ => 1)
          (fun _ => euclPot) y) := by
      intro ρ
      rw [← hball ρ]
      exact (hWc n J A hJ hdim hA _ measurableSet_ball Metric.isBounded_ball).2
    have key := hM n d J A (WithLp.ofLp z) r s hJ hdim hA hr hrs
    rw [hμ r, hμ s, ← ENNReal.ofReal_mul (pow_nonneg (hr.le.trans hrs) _),
      ← ENNReal.ofReal_mul (pow_nonneg hr.le _)]
    apply ENNReal.ofReal_le_ofReal
    calc s ^ (2 * (d + 1)) * (c * ∫ y, chartDens J A ((euclBall (WithLp.ofLp z) r).indicator fun _ => 1)
          (fun _ => euclPot) y)
        = c * (s ^ (2 * (d + 1)) * ∫ y, chartDens J A ((euclBall (WithLp.ofLp z) r).indicator fun _ => 1)
          (fun _ => euclPot) y) := by ring
      _ ≤ c * (r ^ (2 * (d + 1)) * ∫ y, chartDens J A ((euclBall (WithLp.ofLp z) s).indicator fun _ => 1)
          (fun _ => euclPot) y) := mul_le_mul_of_nonneg_left key hc.le
      _ = r ^ (2 * (d + 1)) * (c * ∫ y, chartDens J A ((euclBall (WithLp.ofLp z) s).indicator fun _ => 1)
          (fun _ => euclPot) y) := by ring

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPrimitiveFormFullBranchConstant
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Filter Topology

theorem monic_root_branch_eventuallyEq {d N : ℕ} (a : Fin N → (Fin d → ℂ) → ℂ) (s : Fin d → ℂ)
    (u v : (Fin d → ℂ) → ℂ) (ha : ∀ j, ContinuousAt (a j) s) (hu : ContinuousAt u s)
    (hv : ContinuousAt v s) (huv : u s = v s)
    (hsep : (Polynomial.X ^ N + ∑ j, Polynomial.C (a j s) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).Separable)
    (hru : ∀ᶠ t in 𝓝 s, u t ^ N + ∑ j, a j t * u t ^ (j : ℕ) = 0)
    (hrv : ∀ᶠ t in 𝓝 s, v t ^ N + ∑ j, a j t * v t ^ (j : ℕ) = 0) : u =ᶠ[𝓝 s] v := by
  set Q : (Fin d → ℂ) → ℂ → ℂ → ℂ := fun t x y =>
    ∑ i ∈ Finset.range N, x ^ i * y ^ (N - 1 - i) +
      ∑ j : Fin N, a j t * ∑ i ∈ Finset.range j, x ^ i * y ^ ((j : ℕ) - 1 - i) with hQdef
  have hQ : ∀ t x y, (x ^ N + ∑ j, a j t * x ^ (j : ℕ)) - (y ^ N + ∑ j, a j t * y ^ (j : ℕ)) =
      Q t x y * (x - y) := by
    intro t x y
    rw [hQdef, add_mul, geom_sum₂_mul, Finset.sum_mul]
    simp_rw [mul_assoc, geom_sum₂_mul, mul_sub, Finset.sum_sub_distrib]
    ring
  have hQs : Q s (u s) (u s) ≠ 0 := by
    have h := hsep.eval₂_derivative_ne_zero (RingHom.id ℂ) (x := u s)
      (by simpa [Polynomial.eval₂_id, Polynomial.eval_finsetSum] using hru.self_of_nhds)
    convert h using 1
    simp [hQdef, Polynomial.eval₂_id, Polynomial.eval_finsetSum, geom_sum₂_self, Polynomial.derivative_X_pow]
  have hc : ContinuousAt (fun t => Q t (u t) (v t)) s := by
    simp only [hQdef]
    fun_prop
  have hne : ∀ᶠ t in 𝓝 s, Q t (u t) (v t) ≠ 0 := hc.eventually_ne (by rw [← huv]; exact hQs)
  filter_upwards [hru, hrv, hne] with t h1 h2 h3
  have h := hQ t (u t) (v t)
  rw [h1, h2, sub_self] at h
  exact sub_eq_zero.1 ((mul_eq_zero.1 h.symm).resolve_left h3)

theorem PrimitiveFormFullBranchConstant.proof : PrimitiveFormFullBranchConstant.Statement := by
  intro σ _ X W N' k f d A ℓ N a δ q B O r hW hN' hWN' hf hXN' hXW hP hB ha hδ hq hO hOc hOB hδO hsep hr hrO
  set G : (Fin d → ℂ) → σ → ℂ := fun s i => (∑ j, q i j s * r s ^ (j : ℕ)) / δ s with hGdef
  set P : (Fin d → ℂ) → Prop := fun u => G u ∈ X ∩ W ∧ A (G u) = u ∧ ℓ (G u) = r u with hPdef
  have hG : AnalyticOnNhd ℂ G O := fun u hu => analyticAt_pi_iff.2 fun i =>
    (Finset.analyticAt_fun_sum _ fun j _ => (hq i j u (hOB hu)).mul ((hr u hu).pow _)).div
      (hδ u (hOB hu)) (hδO u hu)

  have hfull : ∀ s ∈ O, (PrimitiveFormRootFull X W A ℓ δ q s (r s) ↔ ∀ᶠ u in 𝓝 s, P u) := by
    intro s hs
    constructor
    · rintro ⟨O', r', hO', hsO', hr', hrs, hw⟩
      have hroot' : ∀ᶠ u in 𝓝 s, r' u ^ N + ∑ j, a j u * r' u ^ (j : ℕ) = 0 := by
        filter_upwards [hO'.mem_nhds hsO'] with u hu
        obtain ⟨hX, hA, hℓ⟩ := hw u hu
        have h := hP _ hX
        rwa [hA, hℓ] at h
      have heq : r' =ᶠ[𝓝 s] r := monic_root_branch_eventuallyEq a s r' r
        (fun j => (ha j s (hOB hs)).continuousAt) (hr' s hsO').continuousAt (hr s hs).continuousAt hrs
        (hsep s hs) hroot' (Filter.mem_of_superset (hO.mem_nhds hs) hrO)
      filter_upwards [hO'.mem_nhds hsO', heq] with u hu hru
      have h := hw u hu
      simp only [hru] at h
      exact h
    · intro hev
      obtain ⟨U, hUs, hUo, hsU⟩ := mem_nhds_iff.1 hev
      exact ⟨U ∩ O, r, hUo.inter hO, ⟨hsU, hs⟩, hr.mono Set.inter_subset_right, rfl, fun u hu => hUs hu.1⟩

  set S : Set (Fin d → ℂ) := {s | ∀ᶠ u in 𝓝 s, P u} with hSdef
  have hSo : IsOpen S := isOpen_setOfPred_eventually_nhds
  have hSc : closure S ∩ O ⊆ S := by
    rintro s ⟨hsc, hs⟩
    have hGs : ContinuousAt G s := (hG s hs).continuousAt
    have hGW : G s ∈ closure W := closure_mono (by rintro _ ⟨u, hu, rfl⟩; exact hu.self_of_nhds.1.2)
      (mem_closure_image hGs hsc)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1
      (Filter.inter_mem (hO.mem_nhds hs) (hGs.preimage_mem_nhds (hN'.mem_nhds (hWN' hGW))))

    set Φ : (Fin d → ℂ) → (Fin k → ℂ) × (Fin d → ℂ) × ℂ :=
      fun u => (fun i => f i (G u), A (G u) - u, ℓ (G u) - r u) with hΦdef
    have hΦ : AnalyticOnNhd ℂ Φ (Metric.ball s ε) := fun u hu => by
      have hu' := hball hu
      exact (analyticAt_pi_iff.2 fun i => (hf i _ hu'.2).comp (hG u hu'.1)).prod
        ((((A.analyticAt _).comp (hG u hu'.1)).sub analyticAt_id).prod
          (((ℓ.analyticAt _).comp (hG u hu'.1)).sub (hr u hu'.1)))
    obtain ⟨u₀, hu₀U, hu₀S⟩ := mem_closure_iff.1 hsc _ Metric.isOpen_ball (Metric.mem_ball_self hε)
    have hΦ0 : Set.EqOn Φ 0 (Metric.ball s ε) :=
      hΦ.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball s ε).isPreconnected hu₀U (by
        filter_upwards [hu₀S] with u hu
        obtain ⟨⟨hX, hWu⟩, hA, hℓ⟩ := hu
        have hXN : G u ∈ X ∩ N' := ⟨hX, hWN' (subset_closure hWu)⟩
        rw [hXN'] at hXN
        simp only [hΦdef, Pi.zero_apply, Prod.mk_eq_zero, hA, hℓ, sub_self, and_true]
        exact funext fun i => hXN.2 i)
    have hU : ∀ u ∈ Metric.ball s ε, G u ∈ X ∧ A (G u) = u ∧ ℓ (G u) = r u := by
      intro u hu
      have h := hΦ0 hu
      simp only [hΦdef, Pi.zero_apply, Prod.mk_eq_zero, sub_eq_zero] at h
      refine ⟨?_, h.2.1, h.2.2⟩
      have hXN : G u ∈ X ∩ N' := by rw [hXN']; exact ⟨(hball hu).2, fun i => congr_fun h.1 i⟩
      exact hXN.1
    obtain ⟨hXs, hAs, -⟩ := hU s (Metric.mem_ball_self hε)
    have hGsW : G s ∈ W := hXW _ ⟨hXs, hGW⟩ (by rw [hAs]; exact hOB hs)
    filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε),
      hGs.preimage_mem_nhds (hW.mem_nhds hGsW)] with u hu hu'
    obtain ⟨h1, h2, h3⟩ := hU u hu
    exact ⟨⟨h1, hu'⟩, h2, h3⟩

  have key : ∀ s ∈ O, ∀ s' ∈ O, PrimitiveFormRootFull X W A ℓ δ q s (r s) →
      PrimitiveFormRootFull X W A ℓ δ q s' (r s') := by
    intro s hs s' hs' h
    have hsub : O ⊆ S := hOc.subset_of_closure_inter_subset hSo ⟨s, hs, (hfull s hs).1 h⟩ hSc
    exact (hfull s' hs').2 (hsub hs')
  intro s hs s' hs'
  exact ⟨key s hs s' hs', key s' hs' s hs⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTubeCollarCompare
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix Filter Topology ReciprocityTheory.AnForm ComplexSets
open scoped ContDiff ComplexOrder

noncomputable section

namespace TubeCollarComparison

theorem contDiffAt_logSq_comp {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (P : MvPolynomial (Fin m) ℂ)
    (x : Fin n → ℂ) (hP : eval (A *ᵥ x) P ≠ 0) :
    ContDiffAt ℝ 2 (fun x => logAbsSq P (A *ᵥ x) ^ 2 / 2) x := by
  have h1 : ContDiffAt ℝ 2 (fun z => ‖eval z P‖ ^ 2) (A *ᵥ x) :=
    (((TubeFormComparison.analyticAt_eval P _).contDiffAt (n := 2)).restrict_scalars ℝ).norm_sq ℝ
  have hv : ContDiffAt ℝ 2 (logAbsSq P) (A *ᵥ x) := h1.log (pow_ne_zero 2 (norm_ne_zero_iff.2 hP))
  have hA : ContDiff ℝ 2 (fun x : Fin n → ℂ => A *ᵥ x) :=
    (LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)).contDiff.restrict_scalars ℝ
  exact ((hv.comp x hA.contDiffAt).pow 2).div_const 2

theorem abs_maDens_collar_le {n d : ℕ} (g : (Fin n → ℂ) → ℝ) (s : (Fin (d + 1) → ℂ) → Fin n → ℂ)
    (y : Fin (d + 1) → ℂ) (hs : AnalyticAt ℂ s y) (hg : ContDiffAt ℝ 2 g (s y)) {c : ℝ}
    (hb : (hessC g (s y) + (c : ℂ) • 1).PosSemidef ∧ (-hessC g (s y) + (c : ℂ) • 1).PosSemidef) :
    |maDens (fun k => vecCons g (fun _ => euclPot) k ∘ s) y| ≤
      3 ^ (d + 1) * c * maDens (fun _ : Fin (d + 1) => euclPot ∘ s) y := by
  set Jc := ReciprocityTheory.AnForm.A.jacC s y with hJc
  set B := Jc.map (starRingEnd ℂ) with hB
  have hBJ : Bᴴ = Jcᵀ := by
    ext a b
    simp [hB]
  have hE2 : ContDiffAt ℝ 2 (euclPot : (Fin n → ℂ) → ℝ) (s y) :=
    ((contDiff_euclPot n).of_le (WithTop.coe_le_coe.2 le_top)).contDiffAt
  have hH : hessC (g ∘ s) y = Bᴴ * hessC g (s y) * B := by
    rw [hBJ]
    exact ReciprocityTheory.AnForm.A.hessC_comp _ s y hs hg
  have hG : hessC (euclPot ∘ s) y = Bᴴ * B := by
    rw [ReciprocityTheory.AnForm.A.hessC_comp _ s y hs hE2, TubeFormComparison.hessC_euclPot, hBJ, Matrix.mul_one]
  have hGp : (Bᴴ * B).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self B
  set Av : Fin (d + 1) → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
    fun k => hessC (vecCons g (fun _ => euclPot) k ∘ s) y with hAv
  set a : Fin (d + 1) → ℂ := Fin.cons (c : ℂ) (fun _ => 1) with ha
  set Bv : Fin (d + 1) → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ := fun k => a k • (Bᴴ * B) with hBv
  have hle : ∀ k, (Bv k - Av k).PosSemidef := by
    intro k
    refine Fin.cases ?_ (fun i => ?_) k
    · simp only [hAv, hBv, ha, Fin.cons_zero, Matrix.cons_val_zero, hH]
      have e : (c : ℂ) • (Bᴴ * B) - Bᴴ * hessC g (s y) * B = Bᴴ * (-hessC g (s y) + (c : ℂ) • 1) * B := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul,
          Matrix.smul_mul, Matrix.mul_one]
        abel
      rw [e]
      exact hb.2.conjTranspose_mul_mul_same B
    · simp only [hAv, hBv, ha, Fin.cons_succ, Matrix.cons_val_succ, hG, one_smul, sub_self]
      exact Matrix.PosSemidef.zero
  have hge : ∀ k, (Av k + Bv k).PosSemidef := by
    intro k
    refine Fin.cases ?_ (fun i => ?_) k
    · simp only [hAv, hBv, ha, Fin.cons_zero, Matrix.cons_val_zero, hH]
      have e : Bᴴ * hessC g (s y) * B + (c : ℂ) • (Bᴴ * B) = Bᴴ * (hessC g (s y) + (c : ℂ) • 1) * B := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
      rw [e]
      exact hb.1.conjTranspose_mul_mul_same B
    · simp only [hAv, hBv, ha, Fin.cons_succ, Matrix.cons_val_succ, hG, one_smul]
      exact hGp.add hGp
  have hmain := ReciprocityTheory.AnForm.A.norm_mdisc_le_of_abs_le Av Bv hle hge
  have hscale : mdisc Bv = (c : ℂ) * mdisc (fun _ : Fin (d + 1) => hessC (euclPot ∘ s) y) := by
    obtain ⟨L, hL⟩ := (by
      show ∃ F : MultilinearMap (RingHom.id ℂ)
          (fun _ : Fin (d + 1) => Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) ℂ,
          ⇑F = _root_.ReciprocityTheory.AnForm.mdisc
      refine ⟨MultilinearMap.mk' _root_.ReciprocityTheory.AnForm.mdisc
        _root_.ReciprocityTheory.AnForm.A.mdisc_update_add ?_, rfl⟩
      intro A k c B
      simpa only [RingHom.id_apply, smul_eq_mul] using
        (_root_.ReciprocityTheory.AnForm.A.mdisc_update_smul A k c B))
    rw [hG, ← hL, hBv, L.map_smul_univ, smul_eq_mul, Fin.prod_univ_succ]
    simp [ha]
  rw [hscale, Complex.re_ofReal_mul] at hmain
  have hm : ∀ Φ : Fin (d + 1) → (Fin (d + 1) → ℂ) → ℝ, maDens Φ y =
      ((d + 1).factorial : ℝ) * (2 / Real.pi) ^ (d + 1) * (mdisc fun k => hessC (Φ k) y).re :=
    fun Φ => rfl
  rw [hm, hm, abs_mul]
  have hK0 : 0 ≤ ((d + 1).factorial : ℝ) * (2 / Real.pi) ^ (d + 1) := by positivity
  rw [abs_of_nonneg hK0]
  calc ((d + 1).factorial : ℝ) * (2 / Real.pi) ^ (d + 1) * |(mdisc Av).re|
      ≤ ((d + 1).factorial : ℝ) * (2 / Real.pi) ^ (d + 1) * ‖mdisc Av‖ := by
        gcongr
        exact Complex.abs_re_le_norm _
    _ ≤ ((d + 1).factorial : ℝ) * (2 / Real.pi) ^ (d + 1) *
        (3 ^ (d + 1) * (c * (mdisc fun _ : Fin (d + 1) => hessC (euclPot ∘ s) y).re)) := by
        gcongr
    _ = _ := by ring

end TubeCollarComparison


open TubeFormComparison TubeCollarComparison in
theorem TubeCollarCompare.proof : TubeCollarCompare.Statement := by
  intro n d J A P R _hJ _hdim hA _hP
  set g : (Fin n → ℂ) → ℝ := fun x => logAbsSq P (A *ᵥ x) ^ 2 / 2 with hgdef
  set U : Set (Fin n → ℂ) := {x | eval (A *ᵥ x) P ≠ 0} with hUdef
  set K : Set (Fin n → ℂ) :=
    Metric.closedBall 0 R ∩ {x | Real.exp (-Real.exp 1) ≤ ‖eval (A *ᵥ x) P‖ ^ 2} with hKdef
  have hcont : Continuous fun x : Fin n → ℂ => eval (A *ᵥ x) P :=
    (MvPolynomial.continuous_eval P).comp (LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)).continuous
  have hU : IsOpen U := isOpen_ne_fun hcont continuous_const
  have hK : IsCompact K :=
    (isCompact_closedBall 0 R).inter_right (isClosed_le continuous_const (hcont.norm.pow 2))
  have hKU : K ⊆ U := fun x hx h0 => by
    have h : Real.exp (-Real.exp 1) ≤ ‖eval (A *ᵥ x) P‖ ^ 2 := hx.2
    rw [h0, norm_zero] at h
    linarith [Real.exp_pos (-Real.exp 1), show (0 : ℝ) ^ 2 = 0 by norm_num]
  have hgU : ContDiffOn ℝ 2 g U := fun x hx => (contDiffAt_logSq_comp A P x hx).contDiffWithinAt
  obtain ⟨c, hc, hb⟩ := exists_hessC_bound (fun _ : Fin 1 => g) K hK (fun _ => U) (fun _ => hU)
    (fun _ => hKU) (fun _ => hgU)
  have hC : 0 ≤ (3 : ℝ) ^ (d + 1) * c := by positivity
  refine ⟨3 ^ (d + 1) * c, fun y => ?_⟩
  by_cases hy : y ∈ {y | -Real.exp 1 ≤ logAbsSq P y}
  swap
  · rw [Set.indicator_of_notMem hy]
    exact mul_nonneg hC (finsum_nonneg fun _ => finsum_nonneg fun _ => by split_ifs <;> positivity)
  rw [Set.indicator_of_mem hy]
  unfold tubeDens chartAbsDens sheetSum
  rw [finsum_mem_eq_finite_toFinset_sum _ (IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y),
    finsum_mem_eq_finite_toFinset_sum _ (IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y), Finset.mul_sum]
  refine Finset.sum_le_sum fun x hx => ?_
  rw [Set.Finite.mem_toFinset] at hx
  obtain ⟨hxZ, hxy⟩ := hx
  subst hxy
  split_ifs with hsx
  swap
  · simp
  dsimp only
  obtain ⟨V, hV, hyV, hsd, hsx', hsec, -⟩ := hsx.choose_spec
  set s := hsx.choose with hsdef
  set f := (Metric.closedBall (0 : Fin n → ℂ) R).indicator fun x => tubeWeight P (A *ᵥ x) with hfdef
  by_cases hf : f x = 0
  · rw [hf, zero_mul, abs_zero]
    exact mul_nonneg hC (abs_nonneg _)
  have hxB : x ∈ Metric.closedBall (0 : Fin n → ℂ) R := by
    by_contra h
    exact hf (Set.indicator_of_notMem h _)
  have hv1 : logAbsSq P (A *ᵥ x) ≤ -1 := by
    by_contra h
    exact hf (by simp [hfdef, Set.indicator_of_mem hxB, tubeWeight, h])
  have hP : eval (A *ᵥ x) P ≠ 0 := by
    intro h0
    simp [logAbsSq, h0] at hv1
    linarith
  have hxK : x ∈ K := by
    refine ⟨hxB, ?_⟩
    have h2 : 0 < ‖eval (A *ᵥ x) P‖ ^ 2 := by positivity
    have h3 := Real.exp_le_exp.2 (show -Real.exp 1 ≤ logAbsSq P (A *ᵥ x) from hy)
    rwa [logAbsSq, Real.exp_log h2] at h3
  have hw : |f x| ≤ 1 := by
    rw [hfdef, Set.indicator_of_mem hxB]
    simp only [tubeWeight, if_pos hv1]
    rw [abs_of_nonneg (by positivity)]
    exact inv_le_one_of_one_le₀ (by nlinarith)
  have hsa : AnalyticAt ℂ s (A *ᵥ x) :=
    analyticAt_pi_iff.2 fun i =>
      ReciprocityTheory.AnForm.Osgood.osgood _ V (fun z => s z i) hV (differentiableOn_pi.1 hsd i) _ hyV
  have hg2 : ContDiffAt ℝ 2 g (s (A *ᵥ x)) := by
    rw [hsx']
    exact contDiffAt_logSq_comp A P x hP
  have hbx := hb 0 (s (A *ᵥ x)) (by rw [hsx']; exact hxK)
  have key := abs_maDens_collar_le g s (A *ᵥ x) hsa hg2 hbx
  rw [abs_mul, abs_mul, Set.indicator_of_mem hxB, abs_one, one_mul]
  calc |f x| * |maDens (fun k => vecCons g (fun _ => euclPot) k ∘ s) (A *ᵥ x)|
      ≤ 1 * (3 ^ (d + 1) * c * maDens (fun _ : Fin (d + 1) => euclPot ∘ s) (A *ᵥ x)) :=
        mul_le_mul hw key (abs_nonneg _) zero_le_one
    _ ≤ 3 ^ (d + 1) * c * |maDens (fun k => (fun _ : Fin (d + 1) => euclPot) k ∘ s) (A *ᵥ x)| := by
        rw [one_mul]
        exact mul_le_mul_of_nonneg_left (le_abs_self _) hC

end

end GroundTheory.Heights₂.Heights
end
