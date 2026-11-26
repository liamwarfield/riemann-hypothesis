module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandSeriesShiftIdentity
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZOpSmooth
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowSubSuccLe

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PoincareValueBoundOnCube
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PoincareValueBoundOnCube
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ENNReal
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.SobGL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.SobCube

theorem norm_sq_left_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {ε : ℝ} (hε : 0 < ε) (h h' : ℝ → V)
    (hd : ∀ s ∈ Set.Icc (0 : ℝ) ε, HasDerivAt h (h' s) s)
    (hc : ContinuousOn h' (Set.Icc 0 ε)) :
    ‖h 0‖ ^ 2 ≤ (2 / ε) * (∫ s in Set.Icc (0 : ℝ) ε, ‖h s‖ ^ 2)
      + (2 * ε) * ∫ s in Set.Icc (0 : ℝ) ε, ‖h' s‖ ^ 2 := by
  have hε' : (0 : ℝ) ≤ ε := hε.le
  have hu : Set.uIcc (0 : ℝ) ε = Set.Icc 0 ε := Set.uIcc_of_le hε'
  have hcu : ContinuousOn (fun s => ‖h' s‖) (Set.uIcc (0 : ℝ) ε) := by
    rw [hu]; exact hc.norm
  have hhc : ContinuousOn h (Set.Icc 0 ε) := fun s hs => (hd s hs).continuousAt.continuousWithinAt
  set A : ℝ := ∫ s in (0 : ℝ)..ε, ‖h' s‖ with hA
  set B : ℝ := ∫ s in (0 : ℝ)..ε, ‖h' s‖ ^ 2 with hB
  have hAnn : 0 ≤ A := intervalIntegral.integral_nonneg hε' (fun _ _ => norm_nonneg _)

  have step1 : ∀ s ∈ Set.Icc (0 : ℝ) ε, ‖h 0‖ ≤ ‖h s‖ + A := by
    intro s hs
    have hsub : Set.uIcc (0 : ℝ) s ⊆ Set.Icc 0 ε := by
      rw [Set.uIcc_of_le hs.1]; exact Set.Icc_subset_Icc le_rfl hs.2
    have hint : IntervalIntegrable h' volume 0 s := (hc.mono hsub).intervalIntegrable
    have hftc : ∫ y in (0 : ℝ)..s, h' y = h s - h 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y hy => hd y (hsub hy)) hint
    have h1 : ‖h s - h 0‖ ≤ ∫ y in (0 : ℝ)..s, ‖h' y‖ := by
      rw [← hftc]; exact intervalIntegral.norm_integral_le_integral_norm hs.1
    have h2 : ∫ y in (0 : ℝ)..s, ‖h' y‖ ≤ A :=
      intervalIntegral.integral_mono_interval le_rfl hs.1 hs.2
        (Filter.Eventually.of_forall fun _ => norm_nonneg _) hcu.intervalIntegrable
    have h3 : ‖h 0‖ ≤ ‖h s‖ + ‖h s - h 0‖ := by
      have := norm_sub_le (h s) (h s - h 0)
      simpa using this
    linarith

  have step2 : A ^ 2 ≤ ε * B := by
    have hnn : 0 ≤ ∫ s in (0 : ℝ)..ε, (‖h' s‖ - A / ε) ^ 2 :=
      intervalIntegral.integral_nonneg hε' (fun _ _ => sq_nonneg _)
    have hi1 : IntervalIntegrable (fun s => ‖h' s‖ ^ 2) volume 0 ε :=
      (hcu.pow 2).intervalIntegrable
    have hi2 : IntervalIntegrable (fun s => ‖h' s‖) volume 0 ε := hcu.intervalIntegrable
    have hexp : ∫ s in (0 : ℝ)..ε, (‖h' s‖ - A / ε) ^ 2 = B - 2 * (A / ε) * A + (A / ε) ^ 2 * ε := by
      have : ∀ s, (‖h' s‖ - A / ε) ^ 2 = ‖h' s‖ ^ 2 - 2 * (A / ε) * ‖h' s‖ + (A / ε) ^ 2 := by
        intro s; ring
      simp_rw [this]
      rw [intervalIntegral.integral_add (hi1.sub (hi2.const_mul _)) (by simp),
        intervalIntegral.integral_sub hi1 (hi2.const_mul _),
        intervalIntegral.integral_const_mul]
      simp [hA, hB]
      ring
    rw [hexp] at hnn
    have h4 : B - 2 * (A / ε) * A + (A / ε) ^ 2 * ε = B - A ^ 2 / ε := by
      field_simp
      ring
    rw [h4] at hnn
    have h5 : A ^ 2 / ε ≤ B := by linarith
    rw [div_le_iff₀ hε] at h5
    linarith

  have hi3 : IntervalIntegrable (fun s => ‖h s‖ ^ 2) volume 0 ε := by
    have : ContinuousOn (fun s => ‖h s‖ ^ 2) (Set.uIcc (0 : ℝ) ε) := by
      rw [hu]; exact hhc.norm.pow 2
    exact this.intervalIntegrable
  have step3 : ε * ‖h 0‖ ^ 2 ≤ 2 * (∫ s in (0 : ℝ)..ε, ‖h s‖ ^ 2) + ε * (2 * A ^ 2) := by
    have hmono : ∫ _s in (0 : ℝ)..ε, ‖h 0‖ ^ 2 ≤ ∫ s in (0 : ℝ)..ε, (2 * ‖h s‖ ^ 2 + 2 * A ^ 2) := by
      refine intervalIntegral.integral_mono_on hε' (by simp)
        ((hi3.const_mul 2).add (by simp)) ?_
      intro s hs
      have h6 := step1 s hs
      have h7 : ‖h 0‖ ^ 2 ≤ (‖h s‖ + A) ^ 2 := by gcongr
      nlinarith [sq_nonneg (‖h s‖ - A)]
    rw [intervalIntegral.integral_add (hi3.const_mul 2) (by simp),
      intervalIntegral.integral_const_mul] at hmono
    simp at hmono
    linarith
  have conv : ∀ f : ℝ → ℝ, ∫ s in Set.Icc (0 : ℝ) ε, f s = ∫ s in (0 : ℝ)..ε, f s := by
    intro f
    rw [intervalIntegral.integral_of_le hε', integral_Icc_eq_integral_Ioc]
  rw [conv, conv, ← hB]
  have h8 : ‖h 0‖ ^ 2 ≤ (2 * (∫ s in (0 : ℝ)..ε, ‖h s‖ ^ 2) + ε * (2 * A ^ 2)) / ε := by
    rw [le_div_iff₀ hε]; linarith
  have h9 : (2 * (∫ s in (0 : ℝ)..ε, ‖h s‖ ^ 2) + ε * (2 * A ^ 2)) / ε
      = 2 / ε * (∫ s in (0 : ℝ)..ε, ‖h s‖ ^ 2) + 2 * A ^ 2 := by
    field_simp
  nlinarith

def Tl {ι : Type} [DecidableEq ι] (l : List ι) : Finset (List ι) :=
  l.foldr (fun i T => T ∪ T.image (fun M => M ++ [i])) {[]}

theorem Tl_nil {ι : Type} [DecidableEq ι] : Tl ([] : List ι) = {[]} := rfl

theorem Tl_cons {ι : Type} [DecidableEq ι] (i : ι) (l : List ι) :
    Tl (i :: l) = Tl l ∪ (Tl l).image (fun M => M ++ [i]) := rfl

theorem marg_bound {ι : Type} [Fintype ι] [DecidableEq ι] (ε : ℝ) (c : ℝ≥0∞)
    (Gf : List ι → (ι → ℝ) → ℝ≥0∞) (hm : ∀ L, Measurable (Gf L))
    (K : Set (ι → ℝ))
    (hK : ∀ x ∈ K, ∀ i, ∀ s ∈ Set.Icc (0 : ℝ) ε, Function.update x i s ∈ K)
    (H : ∀ (L : List ι) (i : ι) (x : ι → ℝ), x ∈ K → x i = 0 →
      Gf L x ≤ c * (∫⁻ s in Set.Icc (0 : ℝ) ε, Gf L (Function.update x i s))
        + c * ∫⁻ s in Set.Icc (0 : ℝ) ε, Gf (i :: L) (Function.update x i s))
    (l : List ι) (hl : l.Nodup) :
    ∀ (L : List ι) (x : ι → ℝ), x ∈ K → (∀ i ∈ l, x i = 0) →
      Gf L x ≤ (2 * c) ^ l.length * ∑ M ∈ Tl l,
        (∫⋯∫⁻_l.toFinset, Gf (M ++ L) ∂(fun _ : ι => (volume : Measure ℝ).restrict (Set.Icc 0 ε))) x := by
  induction l with
  | nil =>
    intro L x _ _
    simp [Tl_nil]
  | cons i l ih =>
    intro L x hx hz
    have hil : i ∉ l := (List.nodup_cons.mp hl).1
    have ih' := ih (List.nodup_cons.mp hl).2
    have hiS : i ∉ l.toFinset := by simpa using hil
    set μ : ι → Measure ℝ := fun _ : ι => (volume : Measure ℝ).restrict (Set.Icc 0 ε) with hμ
    set D : ℝ≥0∞ := (2 * c) ^ l.length with hD
    set Q : List ι → ℝ≥0∞ := fun N => (∫⋯∫⁻_insert i l.toFinset, Gf N ∂μ) x with hQ
    have key : ∀ N₀ : List ι,
        (∫⁻ s in Set.Icc (0 : ℝ) ε, Gf N₀ (Function.update x i s)) ≤ D * ∑ M ∈ Tl l, Q (M ++ N₀) := by
      intro N₀
      have hmeas : ∀ M : List ι, Measurable fun s : ℝ =>
          (∫⋯∫⁻_l.toFinset, Gf (M ++ N₀) ∂μ) (Function.update x i s) := fun M =>
        ((hm _).lmarginal μ).comp (measurable_update x)
      calc (∫⁻ s in Set.Icc (0 : ℝ) ε, Gf N₀ (Function.update x i s))
          ≤ ∫⁻ s in Set.Icc (0 : ℝ) ε, D * ∑ M ∈ Tl l,
              (∫⋯∫⁻_l.toFinset, Gf (M ++ N₀) ∂μ) (Function.update x i s) := by
            refine setLIntegral_mono' measurableSet_Icc ?_
            intro s hs
            refine ih' N₀ _ (hK x hx i s hs) ?_
            intro j hj
            have hji : j ≠ i := fun e => hil (e ▸ hj)
            rw [Function.update_of_ne hji]
            exact hz j (List.mem_cons_of_mem _ hj)
        _ = D * ∑ M ∈ Tl l, Q (M ++ N₀) := by
            rw [lintegral_const_mul _ (Finset.measurable_sum _ fun M _ => hmeas M),
              lintegral_finsetSum _ fun M _ => hmeas M]
            congr 1
            refine Finset.sum_congr rfl fun M _ => ?_
            simp only [hQ]
            rw [lmarginal_insert _ (hm _) hiS]
    have hsum1 : ∑ M ∈ Tl l, Q (M ++ L) ≤ ∑ N ∈ Tl (i :: l), Q (N ++ L) := by
      refine Finset.sum_le_sum_of_subset ?_
      intro M hM
      simp only [Tl_cons, Finset.mem_union]
      exact Or.inl hM
    have hsum2 : ∑ M ∈ Tl l, Q (M ++ i :: L) ≤ ∑ N ∈ Tl (i :: l), Q (N ++ L) := by
      have hinj : Set.InjOn (fun M : List ι => M ++ [i]) (Tl l : Set (List ι)) :=
        fun a _ b _ hab => List.append_cancel_right hab
      have himg : ∑ M ∈ Tl l, Q (M ++ i :: L) = ∑ N ∈ (Tl l).image (fun M => M ++ [i]), Q (N ++ L) := by
        rw [Finset.sum_image hinj]
        refine Finset.sum_congr rfl fun M _ => ?_
        simp
      rw [himg]
      refine Finset.sum_le_sum_of_subset ?_
      intro M hM
      simp only [Tl_cons, Finset.mem_union]
      exact Or.inr hM
    have hx0 : x i = 0 := hz i List.mem_cons_self
    calc Gf L x ≤ c * (∫⁻ s in Set.Icc (0 : ℝ) ε, Gf L (Function.update x i s))
          + c * ∫⁻ s in Set.Icc (0 : ℝ) ε, Gf (i :: L) (Function.update x i s) := H L i x hx hx0
      _ ≤ c * (D * ∑ N ∈ Tl (i :: l), Q (N ++ L)) + c * (D * ∑ N ∈ Tl (i :: l), Q (N ++ L)) := by
          gcongr
          · exact (key L).trans (by gcongr)
          · exact (key (i :: L)).trans (by gcongr)
      _ = (2 * c) ^ (i :: l).length * ∑ N ∈ Tl (i :: l), Q (N ++ L) := by
          simp only [List.length_cons, pow_succ, hD]
          ring
      _ = _ := by
          simp only [hQ, List.toFinset_cons]

theorem contDiffOn_pd {ι V : Type} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup V]
    [NormedSpace ℝ V] {U : Set (ι → ℝ)} {F : (ι → ℝ) → V} (hU : IsOpen U)
    (hF : ContDiffOn ℝ ∞ F U) (L : List ι) : ContDiffOn ℝ ∞ (pd L F) U := by
  induction L with
  | nil => simpa [pd_nil] using hF
  | cons i L ih =>
    rw [pd_cons]
    have h1 : ContDiffOn ℝ ∞ (fderiv ℝ (pd L F)) U := ih.fderiv_of_isOpen hU (by simp)
    exact h1.clm_apply contDiffOn_const

theorem update_mem_cube {ι : Type} [DecidableEq ι] {ε : ℝ} {x : ι → ℝ}
    (hx : x ∈ Set.Icc (0 : ι → ℝ) (fun _ => ε)) (i : ι) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) ε) :
    Function.update x i s ∈ Set.Icc (0 : ι → ℝ) (fun _ => ε) := by
  constructor
  · intro j
    by_cases h : j = i
    · subst h; simpa using hs.1
    · simpa [Function.update_of_ne h] using hx.1 j
  · intro j
    by_cases h : j = i
    · subst h; simpa using hs.2
    · simpa [Function.update_of_ne h] using hx.2 j

theorem line_bound {ι V : Type} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup V]
    [NormedSpace ℝ V] [CompleteSpace V] {ε : ℝ} (hε : 0 < ε) {U : Set (ι → ℝ)} {F : (ι → ℝ) → V}
    (hU : IsOpen U) (hKU : Set.Icc (0 : ι → ℝ) (fun _ => ε) ⊆ U) (hF : ContDiffOn ℝ ∞ F U)
    (L : List ι) (i : ι) (x : ι → ℝ) (hx : x ∈ Set.Icc (0 : ι → ℝ) (fun _ => ε)) (hxi : x i = 0) :
    ‖pd L F x‖ ^ 2 ≤ (2 / ε) * (∫ s in Set.Icc (0 : ℝ) ε, ‖pd L F (Function.update x i s)‖ ^ 2)
      + (2 * ε) * ∫ s in Set.Icc (0 : ℝ) ε, ‖pd (i :: L) F (Function.update x i s)‖ ^ 2 := by
  have hup : ∀ s ∈ Set.Icc (0 : ℝ) ε, Function.update x i s ∈ U := fun s hs =>
    hKU (update_mem_cube hx i hs)
  have h0 : Function.update x i 0 = x := by
    rw [← hxi]; exact Function.update_eq_self i x
  have hcu : Continuous fun s : ℝ => Function.update x i s :=
    continuous_const.update i continuous_id
  have key := norm_sq_left_le hε (fun s => pd L F (Function.update x i s))
    (fun s => pd (i :: L) F (Function.update x i s)) ?_ ?_
  · simpa only [h0] using key
  · intro s hs
    have hdiff : DifferentiableAt ℝ (pd L F) (Function.update x i s) :=
      ((contDiffOn_pd hU hF L).contDiffAt (hU.mem_nhds (hup s hs))).differentiableAt (by simp)
    have := hdiff.hasFDerivAt.comp_hasDerivAt s (hasDerivAt_update x i s)
    show HasDerivAt _ (fderiv ℝ (pd L F) (Function.update x i s) (Pi.single i 1)) s
    exact this
  · exact (contDiffOn_pd hU hF (i :: L)).continuousOn.comp hcu.continuousOn hup

theorem sobolev_cube : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (ε : ℝ), 0 < ε →
    ∃ (T : Finset (List ι)) (C : ℝ), 0 ≤ C ∧ ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
      (U : Set (ι → ℝ)) (F : (ι → ℝ) → V), IsOpen U → Set.Icc (0 : ι → ℝ) (fun _ => ε) ⊆ U → ContDiffOn ℝ ∞ F U →
        ‖F 0‖ ^ 2 ≤ C * ∑ L ∈ T, ∫ t in Set.Icc (0 : ι → ℝ) (fun _ => ε), ‖pd L F t‖ ^ 2 := by
  intro ι _ _ ε hε
  have hc0 : 0 ≤ 2 / ε + 2 * ε := by positivity
  refine ⟨Tl (Finset.univ : Finset ι).toList,
    (2 * (2 / ε + 2 * ε)) ^ (Finset.univ : Finset ι).toList.length, by positivity, ?_⟩
  intro V _ _ _ U F hU hKU hF
  set c0 : ℝ := 2 / ε + 2 * ε with hc0def
  set K : Set (ι → ℝ) := Set.Icc (0 : ι → ℝ) (fun _ => ε) with hKdef
  have hKm : MeasurableSet K := measurableSet_Icc
  have hKc : IsCompact K := isCompact_Icc
  have hcont : ∀ L, ContinuousOn (pd L F) K := fun L =>
    (contDiffOn_pd hU hF L).continuousOn.mono hKU
  set Gf : List ι → (ι → ℝ) → ℝ≥0∞ :=
    fun L => K.indicator (fun t => ENNReal.ofReal (‖pd L F t‖ ^ 2)) with hGf
  have hm : ∀ L, Measurable (Gf L) := by
    intro L
    classical
    have h1 : ContinuousOn (fun t => ENNReal.ofReal (‖pd L F t‖ ^ 2)) K :=
      ENNReal.continuous_ofReal.comp_continuousOn ((hcont L).norm.pow 2)
    have h2 := h1.measurable_piecewise (continuousOn_const (c := (0 : ℝ≥0∞))) hKm
    have h3 : (fun _ : ι → ℝ => (0 : ℝ≥0∞)) = 0 := rfl
    rw [h3, Set.piecewise_eq_indicator] at h2
    exact h2
  have H : ∀ (L : List ι) (i : ι) (x : ι → ℝ), x ∈ K → x i = 0 →
      Gf L x ≤ ENNReal.ofReal c0 * (∫⁻ s in Set.Icc (0 : ℝ) ε, Gf L (Function.update x i s))
        + ENNReal.ofReal c0 * ∫⁻ s in Set.Icc (0 : ℝ) ε, Gf (i :: L) (Function.update x i s) := by
    intro L i x hx hxi
    have h1 := line_bound hε hU hKU hF L i x hx hxi
    have hcu : Continuous fun s : ℝ => Function.update x i s :=
      continuous_const.update i continuous_id
    have hA : ∀ N, ContinuousOn (fun s => ‖pd N F (Function.update x i s)‖ ^ 2) (Set.Icc (0 : ℝ) ε) :=
      fun N => (((hcont N).comp hcu.continuousOn fun s hs => update_mem_cube hx i hs).norm).pow 2
    have hconv : ∀ N, ENNReal.ofReal (∫ s in Set.Icc (0 : ℝ) ε, ‖pd N F (Function.update x i s)‖ ^ 2)
        = ∫⁻ s in Set.Icc (0 : ℝ) ε, Gf N (Function.update x i s) := by
      intro N
      rw [ofReal_integral_eq_lintegral_ofReal ((hA N).integrableOn_compact isCompact_Icc)
        (Filter.Eventually.of_forall fun _ => by positivity)]
      refine setLIntegral_congr_fun measurableSet_Icc ?_
      intro s hs
      simp only [hGf]
      rw [Set.indicator_of_mem (update_mem_cube hx i hs)]
    have hGx : Gf L x = ENNReal.ofReal (‖pd L F x‖ ^ 2) := by
      simp only [hGf]
      rw [Set.indicator_of_mem hx]
    have hAnn : ∀ N, 0 ≤ ∫ s in Set.Icc (0 : ℝ) ε, ‖pd N F (Function.update x i s)‖ ^ 2 :=
      fun N => integral_nonneg fun _ => by positivity
    rw [hGx, ← hconv, ← hconv]
    calc ENNReal.ofReal (‖pd L F x‖ ^ 2)
        ≤ ENNReal.ofReal ((2 / ε) * (∫ s in Set.Icc (0 : ℝ) ε, ‖pd L F (Function.update x i s)‖ ^ 2)
          + (2 * ε) * ∫ s in Set.Icc (0 : ℝ) ε, ‖pd (i :: L) F (Function.update x i s)‖ ^ 2) :=
          ENNReal.ofReal_le_ofReal h1
      _ ≤ ENNReal.ofReal (c0 * (∫ s in Set.Icc (0 : ℝ) ε, ‖pd L F (Function.update x i s)‖ ^ 2)
          + c0 * ∫ s in Set.Icc (0 : ℝ) ε, ‖pd (i :: L) F (Function.update x i s)‖ ^ 2) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have e1 : 2 / ε ≤ c0 := by simp only [hc0def]; have : 0 < 2 * ε := by positivity
                                     linarith
          have e2 : 2 * ε ≤ c0 := by simp only [hc0def]; have : 0 < 2 / ε := by positivity
                                     linarith
          have := mul_le_mul_of_nonneg_right e1 (hAnn L)
          have := mul_le_mul_of_nonneg_right e2 (hAnn (i :: L))
          linarith
      _ = _ := by
          rw [ENNReal.ofReal_add (mul_nonneg hc0 (hAnn _)) (mul_nonneg hc0 (hAnn _)),
            ENNReal.ofReal_mul hc0, ENNReal.ofReal_mul hc0]
  have hb := marg_bound ε (ENNReal.ofReal c0) Gf hm K
    (fun x hx i s hs => update_mem_cube hx i hs) H (Finset.univ : Finset ι).toList
    (Finset.nodup_toList _) [] 0 ⟨le_rfl, fun _ => hε.le⟩ (by simp)
  have hpi : Measure.pi (fun _ : ι => (volume : Measure ℝ).restrict (Set.Icc 0 ε))
      = (volume : Measure (ι → ℝ)).restrict K := by
    have hK' : K = Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) ε) :=
      (Set.pi_univ_Icc (0 : ι → ℝ) (fun _ => ε)).symm
    rw [hK', volume_pi, Measure.restrict_pi_pi]
  have hnn : ∀ M : List ι, 0 ≤ ∫ t in K, ‖pd M F t‖ ^ 2 :=
    fun M => integral_nonneg fun _ => by positivity
  have hmarg : ∀ M : List ι,
      (∫⋯∫⁻_(Finset.univ : Finset ι).toList.toFinset, Gf (M ++ [])
        ∂(fun _ : ι => (volume : Measure ℝ).restrict (Set.Icc 0 ε))) 0
      = ENNReal.ofReal (∫ t in K, ‖pd M F t‖ ^ 2) := by
    intro M
    have hint : IntegrableOn (fun t => ‖pd M F t‖ ^ 2) K :=
      (((hcont M).norm).pow 2).integrableOn_compact hKc
    rw [Finset.toList_toFinset, ← lintegral_eq_lmarginal_univ, hpi, List.append_nil,
      ofReal_integral_eq_lintegral_ofReal hint
        (Filter.Eventually.of_forall fun _ => by positivity)]
    simp only [hGf]
    rw [lintegral_indicator hKm, Measure.restrict_restrict hKm, Set.inter_self]
  have hG0 : Gf [] 0 = ENNReal.ofReal (‖F 0‖ ^ 2) := by
    simp only [hGf]
    rw [Set.indicator_of_mem (show (0 : ι → ℝ) ∈ K from ⟨le_rfl, fun _ => hε.le⟩), pd_nil]
  simp_rw [hmarg] at hb
  rw [hG0, ← ENNReal.ofReal_sum_of_nonneg (fun M _ => hnn M)] at hb
  have h2c : (2 * ENNReal.ofReal c0) ^ (Finset.univ : Finset ι).toList.length
      = ENNReal.ofReal ((2 * c0) ^ (Finset.univ : Finset ι).toList.length) := by
    rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul (by norm_num)]
    simp
  rw [h2c, ← ENNReal.ofReal_mul (by positivity)] at hb
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (by positivity) (Finset.sum_nonneg fun M _ => hnn M))).mp hb

end GlobalTheory.CompanionTheory.SobCube
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PoincareValueBoundOnCubeStatement
open MeasureTheory Matrix Finset
open scoped ContDiff
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.SobGL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poincare_value_bound_on_cube : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (ε : ℝ), 0 < ε →
    ∃ (T : Finset (List ι)) (C : ℝ), 0 ≤ C ∧ ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
      (U : Set (ι → ℝ)) (F : (ι → ℝ) → V), IsOpen U → Set.Icc (0 : ι → ℝ) (fun _ => ε) ⊆ U → ContDiffOn ℝ ∞ F U →
        ‖F 0‖ ^ 2 ≤ C * ∑ L ∈ T, ∫ t in Set.Icc (0 : ι → ℝ) (fun _ => ε), ‖pd L F t‖ ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.SobCube.sobolev_cube | exact GlobalTheory.CompanionTheory.SobCube.sobolev_cube | (intros; apply GlobalTheory.CompanionTheory.SobCube.sobolev_cube <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftTranslateRightDerivative
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftTranslateRightDerivative
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.SobGL

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.SobGL.LeftTr

variable {n : ℕ}

theorem isOpen_gls (n : ℕ) : IsOpen (GLs n) := by
  have h : Continuous (fun g : Mat n => g.det) := Continuous.matrix_det continuous_id
  exact isOpen_ne.preimage h

def lmul (x : Mat n) : Mat n →L[ℝ] Mat n :=
  LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ x)

def rmul (x : Mat n) : Mat n →L[ℝ] Mat n :=
  LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ x)

theorem lmul_apply (x y : Mat n) : lmul x y = x * y := rfl

theorem mul_mem_gls {x y : Mat n} (hx : x ∈ GLs n) (hy : y ∈ GLs n) : x * y ∈ GLs n := by
  simp only [GLs, Set.mem_setOf_eq, Matrix.det_mul] at *
  exact mul_ne_zero hx hy

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem contDiffOn_along {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {U : Set E} (hU : IsOpen U) {f : E → F}
    (hf : ContDiffOn ℝ ∞ f U) (A : E →L[ℝ] E) :
    ContDiffOn ℝ ∞ (fun g => fderiv ℝ f g (A g)) U := by
  have h1 : ContDiffOn ℝ ∞ (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by simp)
  exact h1.clm_apply A.contDiff.contDiffOn

theorem contDiffOn_Rd {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (X : Mat n) :
    ContDiffOn ℝ ∞ (Rd X f) (GLs n) :=
  contDiffOn_along (isOpen_gls n) hf (rmul X)

theorem contDiffOn_Rw {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n))
    (w : List (Idx n)) : ContDiffOn ℝ ∞ (Rw w f) (GLs n) := by
  induction w with
  | nil => exact hf
  | cons p w ih => exact contDiffOn_Rd ih (bs p)

theorem Rw_left (n : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V)
    (hf : ContDiffOn ℝ ∞ f (GLs n)) (x : Mat n) (hx : x ∈ GLs n) :
    ContDiffOn ℝ ∞ (fun y => f (x * y)) (GLs n) ∧
      ∀ (w : List (Idx n)), ∀ y ∈ GLs n, Rw w (fun y => f (x * y)) y = Rw w f (x * y) := by
  have hmaps : Set.MapsTo (fun y : Mat n => x * y) (GLs n) (GLs n) :=
    fun y hy => mul_mem_gls hx hy
  refine ⟨hf.comp (lmul x).contDiff.contDiffOn hmaps, fun w => ?_⟩
  induction w with
  | nil => intro y _; rfl
  | cons p w ih =>
    intro y hy
    have hev : Rw w (fun y => f (x * y)) =ᶠ[nhds y] (Rw w f) ∘ (lmul x) :=
      Filter.eventually_of_mem ((isOpen_gls n).mem_nhds hy) ih
    have hd : DifferentiableAt ℝ (Rw w f) (lmul x y) :=
      ((contDiffOn_Rw hf w).contDiffAt ((isOpen_gls n).mem_nhds (mul_mem_gls hx hy))).differentiableAt
        (by simp)
    have hc : HasFDerivAt ((Rw w f) ∘ (lmul x))
        ((fderiv ℝ (Rw w f) (lmul x y)).comp (lmul x)) y :=
      hd.hasFDerivAt.comp y (lmul x).hasFDerivAt
    change fderiv ℝ (Rw w (fun y => f (x * y))) y (y * bs p) =
      fderiv ℝ (Rw w f) (x * y) (x * y * bs p)
    rw [hev.fderiv_eq, hc.fderiv]
    simp only [ContinuousLinearMap.comp_apply, lmul_apply, Matrix.mul_assoc]

end GlobalTheory.CompanionTheory.SobGL.LeftTr
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftTranslateRightDerivativeStatement
open MeasureTheory Matrix Finset
open scoped ContDiff
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.SobGL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.left_translate_right_derivative : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V),
    ContDiffOn ℝ ∞ f (GLs n) → ∀ x ∈ GLs n, ContDiffOn ℝ ∞ (fun y => f (x * y)) (GLs n) ∧
      ∀ (w : List (Idx n)), ∀ y ∈ GLs n, Rw w (fun y => f (x * y)) y = Rw w f (x * y) := by
  first | exact @GlobalTheory.CompanionTheory.SobGL.LeftTr.Rw_left | exact GlobalTheory.CompanionTheory.SobGL.LeftTr.Rw_left | (intros; apply GlobalTheory.CompanionTheory.SobGL.LeftTr.Rw_left <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartPartialEqRightWord
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartPartialEqRightWord
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.SobGL

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.SobGL.Chart

def cmL (n : ℕ) : (Idx n → ℝ) →L[ℝ] Mat n :=
  ∑ p, (ContinuousLinearMap.proj p : (Idx n → ℝ) →L[ℝ] ℝ).smulRight (bs p)

theorem cmL_apply {n : ℕ} (t : Idx n → ℝ) : cmL n t = cm t := by
  simp [cmL, cm]

theorem cm_single {n : ℕ} (p : Idx n) : cmL n (Pi.single p 1) = bs p := by
  rw [cmL_apply]
  simp [cm, Pi.single_apply, ite_smul]

theorem hasFDerivAt_chart {n : ℕ} (t : Idx n → ℝ) :
    HasFDerivAt (fun t : Idx n → ℝ => (1 : Mat n) + cm t) (cmL n) t := by
  have h : (fun t : Idx n → ℝ => (1 : Mat n) + cm t) = fun t => 1 + cmL n t := by
    funext s; rw [cmL_apply]
  rw [h]
  exact (cmL n).hasFDerivAt.const_add 1

theorem contDiff_chart {n : ℕ} : ContDiff ℝ ∞ (fun t : Idx n → ℝ => (1 : Mat n) + cm t) := by
  have h : (fun t : Idx n → ℝ => (1 : Mat n) + cm t) = fun t => 1 + cmL n t := by
    funext s; rw [cmL_apply]
  rw [h]
  exact contDiff_const.add (cmL n).contDiff

theorem isOpen_GLs' {n : ℕ} : IsOpen (GLs n) := by
  have : Continuous (fun g : Mat n => g.det) := Continuous.matrix_det continuous_id
  exact isOpen_ne_fun this continuous_const

theorem contDiffOn_fderiv_const {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {U : Set E} (hU : IsOpen U) {f : E → F}
    (hf : ContDiffOn ℝ ∞ f U) (v : E) : ContDiffOn ℝ ∞ (fun g => fderiv ℝ f g v) U := by
  have h1 : ContDiffOn ℝ ∞ (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by simp)
  exact h1.clm_apply contDiffOn_const

theorem contDiffOn_Dw {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V)
    (hf : ContDiffOn ℝ ∞ f (GLs n)) (L : List (Idx n)) : ContDiffOn ℝ ∞ (Dw L f) (GLs n) := by
  induction L with
  | nil => exact hf
  | cons p L ih =>
    rw [Dw_cons]
    exact contDiffOn_fderiv_const isOpen_GLs' ih (bs p)

theorem pd_chart {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V)
    (hf : ContDiffOn ℝ ∞ f (GLs n)) (L : List (Idx n)) :
    ∀ t : Idx n → ℝ, 1 + cm t ∈ GLs n →
      pd L (fun t : Idx n → ℝ => f (1 + cm t)) t = Dw L f (1 + cm t) := by
  induction L with
  | nil => intro t _; rfl
  | cons p L ih =>
    intro t ht
    have hopen : IsOpen {s : Idx n → ℝ | (1 : Mat n) + cm s ∈ GLs n} :=
      isOpen_GLs'.preimage contDiff_chart.continuous
    have hev : pd L (fun t : Idx n → ℝ => f (1 + cm t)) =ᶠ[nhds t]
        fun s => Dw L f (1 + cm s) :=
      Filter.eventuallyEq_of_mem (hopen.mem_nhds ht) (fun s hs => ih s hs)
    have hD : DifferentiableAt ℝ (Dw L f) (1 + cm t) :=
      ((contDiffOn_Dw f hf L).contDiffAt (isOpen_GLs'.mem_nhds ht)).differentiableAt (by simp)
    have hc : HasFDerivAt (fun s : Idx n → ℝ => Dw L f (1 + cm s))
        ((fderiv ℝ (Dw L f) (1 + cm t)).comp (cmL n)) t :=
      hD.hasFDerivAt.comp t (hasFDerivAt_chart t)
    rw [pd_cons, Dw_cons]
    show fderiv ℝ (pd L fun t : Idx n → ℝ => f (1 + cm t)) t (Pi.single p 1) = _
    rw [hev.fderiv_eq, hc.fderiv]
    simp [cm_single]

theorem chart_main : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V),
    ContDiffOn ℝ ∞ f (GLs n) → ContDiffOn ℝ ∞ (fun t : Idx n → ℝ => f (1 + cm t)) {t | 1 + cm t ∈ GLs n} ∧
      ∀ (L : List (Idx n)) (t : Idx n → ℝ), 1 + cm t ∈ GLs n →
        pd L (fun t : Idx n → ℝ => f (1 + cm t)) t = Dw L f (1 + cm t) := by
  intro n V _ _ f hf
  refine ⟨?_, fun L t ht => pd_chart f hf L t ht⟩
  exact hf.comp contDiff_chart.contDiffOn (fun t ht => ht)

end GlobalTheory.CompanionTheory.SobGL.Chart
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartPartialEqRightWordStatement
open MeasureTheory Matrix Finset
open scoped ContDiff
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.SobGL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_partial_eq_right_word : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V),
    ContDiffOn ℝ ∞ f (GLs n) → ContDiffOn ℝ ∞ (fun t : Idx n → ℝ => f (1 + cm t)) {t | 1 + cm t ∈ GLs n} ∧
      ∀ (L : List (Idx n)) (t : Idx n → ℝ), 1 + cm t ∈ GLs n →
        pd L (fun t : Idx n → ℝ => f (1 + cm t)) t = Dw L f (1 + cm t) := by
  first | exact @GlobalTheory.CompanionTheory.SobGL.Chart.chart_main | exact GlobalTheory.CompanionTheory.SobGL.Chart.chart_main | (intros; apply GlobalTheory.CompanionTheory.SobGL.Chart.chart_main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SobolevInequalityOnGroup
noncomputable section
open MeasureTheory Matrix Finset
open scoped ContDiff
namespace GlobalTheory.CompanionTheory.SobGL
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem bound_on_cube (n : ℕ) (Q : Set (Idx n → ℝ)) (hQc : IsCompact Q) (hQ : ∀ t ∈ Q, 1 + cm t ∈ GLs n)
    (L : List (Idx n)) : ∃ (W : Finset (List (Idx n))) (B : ℝ), 0 ≤ B ∧
      ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V), ContDiffOn ℝ ∞ f (GLs n) →
        ∀ t ∈ Q, ‖Dw L f (1 + cm t)‖ ^ 2 ≤ B * ∑ w ∈ W, ‖Rw w f (1 + cm t)‖ ^ 2 := by
  obtain ⟨m, c, w, hc, hrep⟩ := GlobalTheory.T.derivative_as_right_words n L
  obtain ⟨-, hcm, -, -⟩ := GlobalTheory.T.chart_and_right_words_smooth n
  have hK : IsCompact ((fun t => 1 + cm t) '' Q) := hQc.image (continuous_const.add hcm)
  have hKsub : (fun t => 1 + cm t) '' Q ⊆ GLs n := by
    rintro _ ⟨t, ht, rfl⟩
    exact hQ t ht
  have hb : ∀ i, ∃ M, ∀ y ∈ (fun t => 1 + cm t) '' Q, ‖c i y‖ ≤ M := fun i =>
    hK.exists_bound_of_continuousOn ((hc i).continuousOn.mono hKsub)
  choose M hM using hb
  refine ⟨Finset.univ.image w, (∑ i, M i ^ 2) * m, by positivity, ?_⟩
  intro V _ _ f hf t ht
  have hy : 1 + cm t ∈ GLs n := hQ t ht
  have hyK : 1 + cm t ∈ (fun t => 1 + cm t) '' Q := ⟨t, ht, rfl⟩
  rw [hrep V f hf _ hy]
  have h1 : ‖∑ i, c i (1 + cm t) • Rw (w i) f (1 + cm t)‖ ≤
      ∑ i, M i * ‖Rw (w i) f (1 + cm t)‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (hM i _ hyK) (norm_nonneg _)
  have h3 : ∑ i, ‖Rw (w i) f (1 + cm t)‖ ^ 2 ≤
      (m : ℝ) * ∑ u ∈ Finset.univ.image w, ‖Rw u f (1 + cm t)‖ ^ 2 := by
    have hi : ∀ i, ‖Rw (w i) f (1 + cm t)‖ ^ 2 ≤ ∑ u ∈ Finset.univ.image w, ‖Rw u f (1 + cm t)‖ ^ 2 :=
      fun i => Finset.single_le_sum (f := fun u => ‖Rw u f (1 + cm t)‖ ^ 2)
        (fun u _ => by positivity) (Finset.mem_image_of_mem w (Finset.mem_univ i))
    calc ∑ i, ‖Rw (w i) f (1 + cm t)‖ ^ 2
        ≤ ∑ _i : Fin m, ∑ u ∈ Finset.univ.image w, ‖Rw u f (1 + cm t)‖ ^ 2 :=
          Finset.sum_le_sum fun i _ => hi i
      _ = (m : ℝ) * ∑ u ∈ Finset.univ.image w, ‖Rw u f (1 + cm t)‖ ^ 2 := by simp
  calc ‖∑ i, c i (1 + cm t) • Rw (w i) f (1 + cm t)‖ ^ 2
      ≤ (∑ i, M i * ‖Rw (w i) f (1 + cm t)‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (∑ i, M i ^ 2) * ∑ i, ‖Rw (w i) f (1 + cm t)‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ ≤ (∑ i, M i ^ 2) * ((m : ℝ) * ∑ u ∈ Finset.univ.image w, ‖Rw u f (1 + cm t)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = (∑ i, M i ^ 2) * m * ∑ u ∈ Finset.univ.image w, ‖Rw u f (1 + cm t)‖ ^ 2 := by ring

theorem sobG : PositivityTheory.RgBcC.SobG := by
  intro n _ _ μ _
  obtain ⟨hGo, hcm, hcm0, hsm⟩ := GlobalTheory.T.chart_and_right_words_smooth n
  set U0 : Set (Idx n → ℝ) := {t | 1 + cm t ∈ GLs n} with hU0def
  have hU0 : IsOpen U0 := hGo.preimage (continuous_const.add hcm)
  have h0 : (0 : Idx n → ℝ) ∈ U0 := by
    show 1 + cm 0 ∈ GLs n
    rw [hcm0, add_zero]
    show Matrix.det (1 : Mat n) ≠ 0
    simp
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hU0 0 h0
  set ε : ℝ := δ / 2 with hε
  have hεpos : 0 < ε := by positivity
  set Q : Set (Idx n → ℝ) := Set.Icc 0 (fun _ => ε) with hQdef
  have hQc : IsCompact Q := isCompact_Icc
  have hQU : Q ⊆ U0 := by
    intro t ht
    apply hball
    rw [Metric.mem_ball, dist_zero_right]
    refine lt_of_le_of_lt ((pi_norm_le_iff_of_nonneg hεpos.le).mpr fun i => ?_) (by linarith)
    rw [Real.norm_eq_abs, abs_of_nonneg (ht.1 i)]
    exact ht.2 i
  have hQG : ∀ t ∈ Q, 1 + cm t ∈ GLs n := fun t ht => hQU ht
  obtain ⟨T, C1, hC1, hsob⟩ := GlobalTheory.T.poincare_value_bound_on_cube (Idx n) ε hεpos
  have hbd := fun L => bound_on_cube n Q hQc hQG L
  choose W B hB hWB using hbd
  have hK : IsCompact ((fun t => 1 + cm t) '' Q) := hQc.image (continuous_const.add hcm)
  have hKsub : (fun t => 1 + cm t) '' Q ⊆ GLs n := by
    rintro _ ⟨t, ht, rfl⟩
    exact hQG t ht
  obtain ⟨hlg, hlgc⟩ := GlobalTheory.T.length_continuous_proper_sublevel n
  obtain ⟨r, hr⟩ := hK.exists_bound_of_continuousOn (hlg.mono hKsub)
  set S : Set (G n) := {y | lg (y : Mat n) ≤ r} with hSdef
  have hSc : IsCompact S := hlgc r
  have hcov : ∀ t ∈ Q, ∃ y ∈ S, (y : Mat n) = 1 + cm t := by
    intro t ht
    have hdet : IsUnit (1 + cm t).det := isUnit_iff_ne_zero.mpr (hQG t ht)
    refine ⟨Matrix.nonsingInvUnit _ hdet, ?_, rfl⟩
    show lg (1 + cm t) ≤ r
    have h := hr _ ⟨t, ht, rfl⟩
    rw [Real.norm_eq_abs] at h
    exact (le_abs_self _).trans h
  obtain ⟨C2, hC2, hcmp⟩ := GlobalTheory.T.haar_chart_integral_comparison n μ Q S hQc hSc hcov
  refine ⟨T.biUnion W, r, C1 * C2 * ∑ L ∈ T, B L, ?_⟩
  intro V _ _ _ f hf x hx
  obtain ⟨hgs, hgR⟩ := GlobalTheory.T.left_translate_right_derivative n V f hf x hx
  obtain ⟨hFs, hpd⟩ := GlobalTheory.T.chart_partial_eq_right_word n V (fun y => f (x * y)) hgs
  have hxmul : ∀ y ∈ GLs n, x * y ∈ GLs n := by
    intro y hy
    show Matrix.det (x * y) ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero hx hy
  have hRc : ∀ w, ContinuousOn (Rw w f) (GLs n) := fun w => ((hsm V f hf).1 w).continuousOn
  let φ : Mat n → ℝ := fun y => ∑ w ∈ T.biUnion W, ‖Rw w f (x * y)‖ ^ 2
  have hφc : ContinuousOn φ (GLs n) := by
    apply continuousOn_finsetSum
    intro w _
    exact (((hRc w).comp (continuous_const.mul continuous_id).continuousOn
      (fun y hy => hxmul y hy)).norm).pow 2
  have hφ0 : ∀ y, 0 ≤ φ y := fun y => Finset.sum_nonneg fun _ _ => by positivity
  have hmain := hcmp φ hφc hφ0
  have hF := hsob V U0 (fun t => f (x * (1 + cm t))) hU0 hQU hFs
  have hstep : ∀ L ∈ T, ∫ t in Q, ‖pd L (fun t => f (x * (1 + cm t))) t‖ ^ 2 ≤
      B L * (C2 * ∫ y in S, φ (y : Mat n) ∂μ) := by
    intro L hL
    have hcongr : ∫ t in Q, ‖pd L (fun t => f (x * (1 + cm t))) t‖ ^ 2 =
        ∫ t in Q, ‖Dw L (fun y => f (x * y)) (1 + cm t)‖ ^ 2 :=
      setIntegral_congr_fun measurableSet_Icc (fun t ht => by rw [hpd L t (hQG t ht)])
    rw [hcongr]
    have hle : ∀ t ∈ Q, ‖Dw L (fun y => f (x * y)) (1 + cm t)‖ ^ 2 ≤ B L * φ (1 + cm t) := by
      intro t ht
      refine (hWB L V (fun y => f (x * y)) hgs t ht).trans (mul_le_mul_of_nonneg_left ?_ (hB L))
      calc ∑ w ∈ W L, ‖Rw w (fun y => f (x * y)) (1 + cm t)‖ ^ 2
          = ∑ w ∈ W L, ‖Rw w f (x * (1 + cm t))‖ ^ 2 :=
            Finset.sum_congr rfl fun w _ => by rw [hgR w _ (hQG t ht)]
        _ ≤ φ (1 + cm t) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_biUnion_of_mem W hL)
              (fun _ _ _ => by positivity)
    have hint : IntegrableOn (fun t => B L * φ (1 + cm t)) Q volume := by
      refine ContinuousOn.integrableOn_compact hQc ?_
      exact continuousOn_const.mul
        (hφc.comp (continuous_const.add hcm).continuousOn (fun t ht => hQG t ht))
    calc ∫ t in Q, ‖Dw L (fun y => f (x * y)) (1 + cm t)‖ ^ 2
        ≤ ∫ t in Q, B L * φ (1 + cm t) :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => by positivity) hint
            ((ae_restrict_iff' measurableSet_Icc).mpr (Filter.Eventually.of_forall hle))
      _ = B L * ∫ t in Q, φ (1 + cm t) := integral_const_mul _ _
      _ ≤ B L * (C2 * ∫ y in S, φ (y : Mat n) ∂μ) := mul_le_mul_of_nonneg_left hmain (hB L)
  have hsplit : ∫ y in S, φ (y : Mat n) ∂μ =
      ∑ w ∈ T.biUnion W, ∫ y in S, ‖Rw w f (x * (y : Mat n))‖ ^ 2 ∂μ := by
    refine integral_finsetSum _ fun w _ => ?_
    refine ContinuousOn.integrableOn_compact hSc (Continuous.continuousOn ?_)
    have hval : ∀ y : G n, x * (y : Mat n) ∈ GLs n := fun y =>
      hxmul _ ((Matrix.isUnit_iff_isUnit_det _).mp y.isUnit).ne_zero
    exact (((hRc w).comp_continuous (continuous_const.mul Units.continuous_val) hval).norm).pow 2
  have hF0 : f (x * (1 + cm 0)) = f x := by rw [hcm0, add_zero, mul_one]
  calc ‖f x‖ ^ 2 = ‖f (x * (1 + cm 0))‖ ^ 2 := by rw [hF0]
    _ ≤ C1 * ∑ L ∈ T, ∫ t in Q, ‖pd L (fun t => f (x * (1 + cm t))) t‖ ^ 2 := hF
    _ ≤ C1 * ∑ L ∈ T, B L * (C2 * ∫ y in S, φ (y : Mat n) ∂μ) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hstep) hC1
    _ = C1 * C2 * (∑ L ∈ T, B L) * ∫ y in S, φ (y : Mat n) ∂μ := by
        rw [← Finset.sum_mul]
        ring
    _ = C1 * C2 * (∑ L ∈ T, B L) *
        ∑ w ∈ T.biUnion W, ∫ y in S, ‖Rw w f (x * (y : Mat n))‖ ^ 2 ∂μ := by rw [hsplit]

end GlobalTheory.CompanionTheory.SobGL
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SobolevInequalityOnGroupStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sobolev_inequality_on_group : PositivityTheory.RgBcC.SobG := by
  first | exact @GlobalTheory.CompanionTheory.SobGL.sobG | exact GlobalTheory.CompanionTheory.SobGL.sobG | (intros; apply GlobalTheory.CompanionTheory.SobGL.sobG <;> assumption)
end
