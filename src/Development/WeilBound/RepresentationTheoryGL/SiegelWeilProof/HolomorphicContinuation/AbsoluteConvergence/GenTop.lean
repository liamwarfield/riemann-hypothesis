module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.GenCoreP
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.TsGenCOf
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.TsGen
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.FarRightCAlt
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.FarRight
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.BasisM

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.IEqOfSL
noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw GlobalTheory.Cont

section
variable {m n : ℕ} {ε : Fin m → Bool} {c t : ℝ} {p q : ℕ} {e : ℤ} {sL : PX m n →ₗ[ℂ] (GR n → ℂ)}
  {ρ : GR n → PX m n →ₗ[ℂ] PX m n} {G : Type} [Group G] [TopologicalSpace G] {Pp Γ : Subgroup G} {ι : GR n →* G}
  {s₀ : ℂ} {Ht : G → ℝ≥0} {sec I : PX m n →ₗ[ℂ] (G → ℂ)} {Λ : Set ((G → ℂ) → ℂ)}

theorem I_eq_of_sL (hS : SecZero) (hLC : LC) (hL : LocData ε c t p q e sL ρ) (hD : GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ)
    {Q Q' : PX m n} (h : ∀ y, sL Q y = sL Q' y) (g : G) : I Q g = I Q' g := by
  have hnull : NullSec ε c (Q - Q') :=
    (hS m n ε c t p q e sL ρ hL (Q - Q')).2 (fun y => by simp [map_sub, h y])
  have key := hLC m n ε c hL.cpos ((LinearMap.proj g).comp I) (fun a b P => hD.Iinv g a b P) (Q - Q') hnull
  simp only [LinearMap.comp_apply, LinearMap.proj_apply, map_sub, Pi.sub_apply] at key
  exact sub_eq_zero.mp key

theorem hz_comb (hD : GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ) {N : ℕ} {P : PX m n} {QQ : Fin N → PX m n} {cc : Fin N → ℂ}
    (hP : ∀ y, sL P y = ∑ j, cc j * sL (QQ j) y) (z : ℂ) (x : G) :
    hz Ht sec s₀ z P x = ∑ j, cc j * hz Ht sec s₀ z (QQ j) x := by
  obtain ⟨x', y, S, r, hr, hg, hx⟩ := hD.split x
  have hs : ∀ Q : PX m n, sec Q x = S * sL Q y := fun Q => by
    rw [hg]
    exact (hx y).2 Q
  simp only [hz]
  rw [hs P, hP y, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hs (QQ j)]
  ring

end

theorem mulVec_sum {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℂ) (v : Fin N → ℂ) (j : Fin N) :
    ∑ i, A j i * ∑ l, B i l * v l = ∑ l, (A * B) j l * v l := by
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => ?_
  ring

private theorem det_diff_lemma {N : ℕ} {A : ℂ → Matrix (Fin N) (Fin N) ℂ}
    (h : ∀ i j, Differentiable ℂ fun w => A w i j) : Differentiable ℂ fun w => (A w).det := by
  simp only [Matrix.det_apply']
  refine Differentiable.fun_sum fun σ _ => ?_
  refine Differentiable.fun_mul (differentiable_const _) ?_
  classical
  have hp : ∀ s : Finset (Fin N), Differentiable ℂ (fun w => ∏ i ∈ s, A w (σ i) i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using (differentiable_const (1 : ℂ))
    | insert a s ha ih =>
      simp only [Finset.prod_insert ha]
      exact (h (σ a) a).fun_mul ih
  exact hp Finset.univ

private theorem adj_diff_lemma_2 {N : ℕ} {A : ℂ → Matrix (Fin N) (Fin N) ℂ}
    (h : ∀ i j, Differentiable ℂ fun w => A w i j) (a b : Fin N) :
    Differentiable ℂ fun w => (A w).adjugate a b := by
  simp only [Matrix.adjugate_apply]
  refine det_diff_lemma (A := fun w => (A w).updateRow b (Pi.single a 1)) fun i j => ?_
  by_cases hib : i = b
  · subst hib
    simp only [Matrix.updateRow_self]
    exact differentiable_const _
  · simp only [Matrix.updateRow_ne hib]
    exact h i j

private theorem ev_ne_lemma_3 {f : ℂ → ℂ} (hf : Differentiable ℂ f) (ha : ∃ a, f a ≠ 0) (z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z, f w ≠ 0 := by
  rcases (hf.analyticAt z).eventually_eq_zero_or_eventually_ne_zero with h | h
  · exfalso
    obtain ⟨a, ha⟩ := ha
    have hon : AnalyticOnNhd ℂ f univ := fun x _ => hf.analyticAt x
    exact ha (hon.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ z) h (mem_univ a))
  · exact h

private theorem glue_core_lemma_4 (hG : Glue) {N : ℕ} {s₀ : ℂ} {U V : Set ℂ} {σ : ℝ} {D : ℂ → ℂ}
    {M' : ℂ → Matrix (Fin N) (Fin N) ℂ} {B Ah Ej : Fin N → ℂ → ℂ}
    (hUo : IsOpen U) (hUr : IsRightDomain U) (hs₀ : s₀ ∈ U) (hVo : IsOpen V) (hs₀V : s₀ ∈ V)
    (hD : Differentiable ℂ D) (hDne : ∃ a, D a ≠ 0)
    (hM : ∀ i j, Differentiable ℂ fun w => M' w i j) (hM0 : M' s₀ = 1)
    (hB : ∀ i, DifferentiableOn ℂ (B i) U) (hAh : ∀ i, DifferentiableOn ℂ (Ah i) V)
    (hBA : ∀ w ∈ V, w ∈ U → D w ≠ 0 → ∀ i, B i w = D w * Ah i w)
    (hσU : rightOf σ ⊆ U) (hEd : ∀ j, DifferentiableOn ℂ (Ej j) (rightOf σ))
    (hBE : ∀ w ∈ rightOf σ, ∀ i, B i w = D w * ∑ l, M' w i l * Ej l w) (j : Fin N) :
    HolValueAt (Ej j) s₀ (Ah j s₀) := by
  have hdt : Differentiable ℂ fun w => (M' w).det := det_diff_lemma hM
  have hadj : ∀ a b, Differentiable ℂ fun w => (M' w).adjugate a b := adj_diff_lemma_2 hM
  have hdt0 : (M' s₀).det = 1 := by rw [hM0, Matrix.det_one]
  have hgb0 : (∑ i, (M' s₀).adjugate j i * Ah i s₀) / (M' s₀).det = Ah j s₀ := by
    rw [hdt0, div_one, hM0, Matrix.adjugate_one]
    simp [Matrix.one_apply]
  have hDev := ev_ne_lemma_3 hD hDne
  have hdtev := ev_ne_lemma_3 hdt ⟨s₀, by rw [hdt0]; exact one_ne_zero⟩
  have hne : ∀ z, ∀ᶠ w in 𝓝[≠] z, w ≠ s₀ := by
    intro z
    by_cases h : z = s₀
    · subst h
      exact self_mem_nhdsWithin
    · exact nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds h)
  let f : ℂ → ℂ := Function.update
    (fun w => (∑ i, (M' w).adjugate j i * B i w) / (D w * (M' w).det)) s₀
    ((∑ i, (M' s₀).adjugate j i * Ah i s₀) / (M' s₀).det)
  have hnumV : DifferentiableOn ℂ (fun w => ∑ i, (M' w).adjugate j i * Ah i w) V :=
    DifferentiableOn.fun_sum fun i _ => (hadj j i).differentiableOn.mul (hAh i)
  have hgbA : AnalyticAt ℂ (fun w => (∑ i, (M' w).adjugate j i * Ah i w) / (M' w).det) s₀ :=
    (hnumV.analyticAt (hVo.mem_nhds hs₀V)).div (hdt.analyticAt s₀) (by rw [hdt0]; exact one_ne_zero)
  have hf_eq : f =ᶠ[𝓝 s₀] fun w => (∑ i, (M' w).adjugate j i * Ah i w) / (M' w).det := by
    have h1 : ∀ᶠ w in 𝓝[≠] s₀, f w = (∑ i, (M' w).adjugate j i * Ah i w) / (M' w).det := by
      filter_upwards [hDev s₀, hne s₀, nhdsWithin_le_nhds (hUo.mem_nhds hs₀),
        nhdsWithin_le_nhds (hVo.mem_nhds hs₀V)] with w hDw hw hwU hwV
      simp only [f, Function.update_of_ne hw]
      have h2 : ∑ i, (M' w).adjugate j i * B i w = D w * ∑ i, (M' w).adjugate j i * Ah i w := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hBA w hwV hwU hDw i]
        ring
      rw [h2, mul_div_mul_left _ _ hDw]
    filter_upwards [eventually_nhdsWithin_iff.mp h1] with w hw
    by_cases h : w = s₀
    · subst h
      simp only [f, Function.update_self]
    · exact hw h
  have hfA : AnalyticAt ℂ f s₀ := hgbA.congr hf_eq.symm
  have hfM : MeromorphicOn f U := by
    intro w hw
    have hnum : AnalyticAt ℂ (fun w => ∑ i, (M' w).adjugate j i * B i w) w :=
      (DifferentiableOn.fun_sum fun i _ => (hadj j i).differentiableOn.mul (hB i)).analyticAt
        (hUo.mem_nhds hw)
    have hden : AnalyticAt ℂ (fun w => D w * (M' w).det) w := (hD.fun_mul hdt).analyticAt w
    refine (hnum.meromorphicAt.div hden.meromorphicAt).congr ?_
    filter_upwards [hne w] with v hv
    simp only [f, Function.update_of_ne hv, Pi.div_apply]
  have hmain := hG U f (Ej j) σ s₀ hUo hUr hs₀ hfM hfA hσU (hEd j) ?_
  · have hfs : f s₀ = Ah j s₀ := by
      simp only [f, Function.update_self]
      exact hgb0
    rw [hfs] at hmain
    exact hmain
  · intro z hz
    have hzo : rightOf σ ∈ 𝓝 z := (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz
    filter_upwards [hDev z, hdtev z, hne z, nhdsWithin_le_nhds hzo] with w hDw hdw hw hwσ
    simp only [f, Function.update_of_ne hw]
    have h3 : ∑ i, (M' w).adjugate j i * B i w = D w * ((M' w).det * Ej j w) := by
      have h2 : ∑ i, (M' w).adjugate j i * B i w
          = D w * ∑ i, (M' w).adjugate j i * ∑ l, M' w i l * Ej l w := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hBE w hwσ i]
        ring
      rw [h2, mulVec_sum, Matrix.adjugate_mul]
      simp [Matrix.smul_apply, Matrix.one_apply]
    rw [h3, ← mul_assoc, mul_div_cancel_left₀ _ (mul_ne_zero hDw hdw)]

private theorem poly_ev_lemma_5 {d : Polynomial ℂ} (hd : d ≠ 0) :
    ∃ σ : ℝ, ∀ z : ℂ, σ < z.re → d.eval z ≠ 0 := by
  refine ⟨∑ r ∈ d.roots.toFinset, ‖r‖, fun z hz h0 => ?_⟩
  have hmem : z ∈ d.roots.toFinset := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hd]
    exact h0
  have h1 : ‖z‖ ≤ ∑ r ∈ d.roots.toFinset, ‖r‖ :=
    Finset.single_le_sum (f := fun r => ‖r‖) (fun r _ => norm_nonneg r) hmem
  have h2 : z.re ≤ ‖z‖ := Complex.re_le_norm z
  linarith

private theorem hv_sum_lemma_6 {s₀ : ℂ} {ι : Type*} (T : Finset ι) {f : ι → ℂ → ℂ} {z : ι → ℂ}
    (h : ∀ i ∈ T, HolValueAt (f i) s₀ (z i)) :
    HolValueAt (fun s => ∑ i ∈ T, f i s) s₀ (∑ i ∈ T, z i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using holValueAt_const 0 s₀
  | insert a T ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a T)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem absThm_gen (hV : VacOut) (hP : ProjOp) (hT : TSGen) (hB : Basis) (hFar : FarRight) (hS : SecZero) (hLC : LC)
    (hH : HolParam) (hG : Glue) : AbsThm := by
  intro m n ε c t p q e sL ρ hL hGS G _ _ _ _ _ _ Pp Γ ι s₀ Ht sec I Λ hD P g
  letI : MeasurableSpace ↥(KR n) := borel _
  haveI : BorelSpace ↥(KR n) := ⟨rfl⟩
  obtain ⟨W, hWfd, hPW, hWst, -⟩ := hL.kfin P
  obtain ⟨ν, κ, hν, hκ, hproj, hlift⟩ := hP m n ε c t p q e sL ρ hL W hWfd hWst
  haveI := hν
  obtain ⟨N, yy, QQ, cc, M, hQW, hPc, hM0, hMd, hyy, hint⟩ :=
    hB m n ε c t p q e sL ρ hL W hWfd hWst ν κ hν hκ hproj hlift P hPW
  obtain ⟨σf, hEdiff, hsum, hfar⟩ := hFar m n ε c t p q e sL ρ hL G Pp Γ ι s₀ Ht sec I Λ hD
  obtain ⟨r, σv, F, hr, -, hFc, hFd, hF0, -, hFhv⟩ :=
    hV m n ε c t p q e sL ρ hL hGS G Pp Γ ι s₀ Ht sec I Λ hD
  obtain ⟨U, d, Ee, σe, hUo, hUr, hs₀U, hd, hEd, hEc, -, hEeq⟩ := hD.eis
  obtain ⟨σd, hσd⟩ := poly_ev_lemma_5 hd
  obtain ⟨σU, hσU⟩ := hUr.1
  have hdne : ∃ a, d.eval a ≠ 0 := by
    by_contra h
    push_neg at h
    exact hd (Polynomial.funext fun a => by simp [h a])
  have hTS : ∀ i x, ∫ k, κ k * I 1 (x * ι (↑k * yy i)) ∂ν = I (QQ i) x := fun i x =>
    hT m n ε c t p q e sL ρ hL G Pp Γ ι s₀ Ht sec I Λ hD W hWfd hWst ν κ hν hκ hproj hlift x (yy i)
      (QQ i) (hQW i) (hyy i)
  have hmap : ∀ i, Continuous fun k : ↥(KR n) => g * ι (↑k * yy i) := fun i =>
    continuous_const.mul (hD.ιcont.comp ((continuous_mul_const (yy i)).comp continuous_subtype_val))
  have hAh : ∀ i, DifferentiableOn ℂ (fun z => ∫ k, κ k * F z (g * ι (↑k * yy i)) ∂ν) (Metric.ball s₀ r) := by
    intro i
    refine (hH (↥(KR n)) ν univ isCompact_univ (by simp) (Metric.ball s₀ r)
      (fun k z => κ k * F z (g * ι (↑k * yy i))) Metric.isOpen_ball ?_ ?_).1
    · refine ContinuousOn.mul (hκ.comp continuous_fst).continuousOn ?_
      exact hFc.comp (Continuous.continuousOn (continuous_snd.prodMk ((hmap i).comp continuous_fst)))
        (fun y hy => ⟨hy.2, mem_univ _⟩)
    · exact fun k _ => (hFd _).const_mul _
  have hBd : ∀ i, DifferentiableOn ℂ (fun z => ∫ k, κ k * Ee z (g * ι (↑k * yy i)) ∂ν) U := by
    intro i
    refine (hH (↥(KR n)) ν univ isCompact_univ (by simp) U
      (fun k z => κ k * Ee z (g * ι (↑k * yy i))) hUo ?_ ?_).1
    · refine ContinuousOn.mul (hκ.comp continuous_fst).continuousOn ?_
      exact hEc.comp (Continuous.continuousOn (continuous_snd.prodMk ((hmap i).comp continuous_fst)))
        (fun y hy => ⟨hy.2, mem_univ _⟩)
    · exact fun k _ => (hEd _).const_mul _
  have hEF : ∀ w ∈ Metric.ball s₀ r, w ∈ U → d.eval w ≠ 0 → ∀ x, Ee w x = d.eval w * F w x := by
    intro w hwV hwU hdw x
    have hH' : IsExtAt (fun z => GlobalTheory.Eis.cosetSum Pp Γ (fun x' => ↑↑(Ht x') ^ (z - s₀) * sec 1 x') x) w
        (fun z => Ee z x / d.eval z) := by
      refine ⟨U, hwU, hUr, fun z hz => ?_, ⟨max σe σd, fun z hz => ?_⟩⟩
      · exact ((hEd x).analyticAt (hUo.mem_nhds hz)).meromorphicAt.div
          ((Polynomial.differentiable d).analyticAt z).meromorphicAt
      · have hz1 : σe < z.re := lt_of_le_of_lt (le_max_left _ _) hz
        have hz2 : σd < z.re := lt_of_le_of_lt (le_max_right _ _) hz
        simp only
        rw [(hEeq z hz1).2 x, mul_div_cancel_left₀ _ (hσd z hz2)]
    have hv := hFhv x w hwV
    rw [hH'.holValueAt_iff] at hv
    have hcont : ContinuousAt (fun z => Ee z x / d.eval z) w :=
      ((hEd x).continuousOn.continuousAt (hUo.mem_nhds hwU)).div
        (Polynomial.continuous d).continuousAt hdw
    have h1 : F w x = Ee w x / d.eval w :=
      tendsto_nhds_unique hv (hcont.tendsto.mono_left nhdsWithin_le_nhds)
    rw [h1]
    field_simp
  have key : ∀ j, HolValueAt (fun z => GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z (QQ j)) g) s₀
      (∫ k, κ k * F s₀ (g * ι (↑k * yy j)) ∂ν) := by
    intro j
    refine glue_core_lemma_4 (σ := max (max σe σf) σU) (D := fun w => d.eval w)
      (M' := fun w => M (w - s₀)) (B := fun i z => ∫ k, κ k * Ee z (g * ι (↑k * yy i)) ∂ν)
      (Ah := fun i z => ∫ k, κ k * F z (g * ι (↑k * yy i)) ∂ν)
      (Ej := fun j z => GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z (QQ j)) g)
      hG hUo hUr hs₀U Metric.isOpen_ball (Metric.mem_ball_self hr) (Polynomial.differentiable d) hdne
      (fun i j => (hMd i j).comp (differentiable_id.sub_const s₀)) (by simp only [sub_self, hM0])
      hBd hAh ?_ (fun z hz' => hσU (by show σU < z.re; exact lt_of_le_of_lt (le_max_right (max σe σf) σU) hz')) ?_ ?_ j
    · intro w hwV hwU hdw i
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
      simp only
      rw [hEF w hwV hwU hdw]
      ring
    · intro l
      exact (hEdiff (QQ l) g).mono fun z hz =>
        lt_of_le_of_lt (le_trans (le_max_right σe σf) (le_max_left _ σU)) hz
    · intro w hw i
      have hwe : σe < w.re := lt_of_le_of_lt (le_trans (le_max_left σe σf) (le_max_left _ σU)) hw
      have hwf : σf < w.re := lt_of_le_of_lt (le_trans (le_max_right σe σf) (le_max_left _ σU)) hw
      rw [← hfar ν κ N yy QQ M hν hκ hint w hwf g i, ← MeasureTheory.integral_const_mul]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
      simp only
      rw [(hEeq w hwe).2]
      have e1 : hz Ht sec s₀ w 1 = fun x => ↑↑(Ht x) ^ (w - s₀) * sec 1 x := rfl
      rw [e1]
      ring
  have key' : ∀ j, HolValueAt (fun z => GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z (QQ j)) g) s₀
      (I (QQ j) g) := by
    intro j
    have h := key j
    simp only [hF0] at h
    rwa [hTS] at h
  have hIP : I P g = ∑ j, cc j * I (QQ j) g := by
    have h := I_eq_of_sL hS hLC hL hD (Q := P) (Q' := ∑ j, cc j • QQ j)
      (fun y => by simp [map_sum, map_smul, hPc y]) g
    rw [h]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, map_smul]
  have hsumHV := hv_sum_lemma_6 Finset.univ (s₀ := s₀)
    (f := fun j z => cc j * GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z (QQ j)) g)
    (z := fun j => cc j * I (QQ j) g) (fun j _ => (holValueAt_const (cc j) s₀).mul (key' j))
  rw [hIP]
  refine hsumHV.congr ⟨σf, fun z hzr => ?_⟩
  have hc : ∀ qq : GlobalTheory.Eis.Cosets Pp Γ,
      GlobalTheory.Eis.term Pp Γ (fun x => ↑↑(Ht x) ^ (z - s₀) * sec P x) g qq
        = ∑ j, cc j * GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ z (QQ j)) g qq := fun qq =>
    hz_comb hD hPc z _
  have hs := Summable.tsum_finsetSum (s := Finset.univ)
    (f := fun j qq => cc j * GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ z (QQ j)) g qq)
    (fun j _ => (hsum (QQ j) g z hzr).mul_left (cc j))
  simp only [GlobalTheory.Eis.cosetSum]
  rw [tsum_congr hc, hs]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [tsum_mul_left]

end PositivityTheory.Rg.Sw.AbsSt
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ProjOpOf
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.RepKerP
noncomputable section

open MeasureTheory Matrix

namespace PositivityTheory.Rg.Sw.AbsSt.Proj

namespace RK

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H] [T2Space H]
  [MeasurableSpace H] [BorelSpace H] (μ : Measure H) [μ.IsHaarMeasure]

theorem integ {f : H → ℂ} (hf : Continuous f) : Integrable f μ := by
  exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem integ_sm {u w : H → ℂ} (hu : Continuous u) (hw : Continuous w) : Integrable (fun y => star (u y) * w y) μ :=
  integ μ (hu.star.mul hw)

def ip (u w : H → ℂ) : ℂ := ∫ y, star (u y) * w y ∂μ

theorem ip_add {u w w' : H → ℂ} (hu : Continuous u) (hw : Continuous w) (hw' : Continuous w') :
    ip μ u (fun y => w y + w' y) = ip μ u w + ip μ u w' := by
  simp only [ip, mul_add]
  exact integral_add (integ_sm μ hu hw) (integ_sm μ hu hw')

theorem ip_sub {u w w' : H → ℂ} (hu : Continuous u) (hw : Continuous w) (hw' : Continuous w') :
    ip μ u (fun y => w y - w' y) = ip μ u w - ip μ u w' := by
  simp only [ip, mul_sub]
  exact integral_sub (integ_sm μ hu hw) (integ_sm μ hu hw')

theorem ip_sum_right {ι : Type} (s : Finset ι) {u : H → ℂ} (hu : Continuous u) (c : ι → ℂ) (w : ι → H → ℂ)
    (hw : ∀ i, Continuous (w i)) : ip μ u (fun y => ∑ i ∈ s, c i * w i y) = ∑ i ∈ s, c i * ip μ u (w i) := by
  unfold ip
  simp only [Finset.mul_sum]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [← integral_const_mul]
    congr 1
    funext y
    ring
  · intro i _
    exact integ μ ((continuous_star.comp hu).mul (continuous_const.mul (hw i)))

theorem ip_sum_left {ι : Type} (s : Finset ι) {w : H → ℂ} (hw : Continuous w) (c : ι → ℂ) (u : ι → H → ℂ)
    (hu : ∀ i, Continuous (u i)) : ip μ (fun y => ∑ i ∈ s, c i * u i y) w = ∑ i ∈ s, star (c i) * ip μ (u i) w := by
  unfold ip
  have key : ∀ y, star (∑ i ∈ s, c i * u i y) * w y = ∑ i ∈ s, star (c i) * (star (u i y) * w y) := by
    intro y
    rw [star_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [star_mul']
    ring
  simp only [key]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    exact integral_const_mul _ _
  · intro i _
    exact (integ_sm μ (hu i) hw).const_mul _

theorem ip_left (a : H) (u w : H → ℂ) : ip μ u (fun y => w (a * y)) = ip μ (fun y => u (a⁻¹ * y)) w := by
  unfold ip
  rw [← integral_mul_left_eq_self (fun y => star (u (a⁻¹ * y)) * w y) a]
  simp only [inv_mul_cancel_left]

theorem norm_sq_zero {ψ : H → ℂ} (hψ : Continuous ψ) (h : ip μ ψ ψ = 0) : ψ = 0 := by
  have h1 : ∀ y, star (ψ y) * ψ y = ((‖ψ y‖ ^ 2 : ℝ) : ℂ) := by
    intro y
    rw [Complex.star_def, Complex.conj_mul']
    push_cast
    ring
  have h2 : ip μ ψ ψ = ((∫ y, ‖ψ y‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    unfold ip
    simp only [h1]
    exact integral_ofReal
  rw [h2, Complex.ofReal_eq_zero] at h
  have hc2 : Continuous (fun y => ‖ψ y‖ ^ 2) := (continuous_norm.comp hψ).pow 2
  have hae := (integral_eq_zero_iff_of_nonneg (fun y => sq_nonneg _)
    (hc2.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).mp h
  have heq := (Continuous.ae_eq_iff_eq μ hc2 continuous_zero).mp hae
  funext y
  simpa using congrFun heq y

variable {N : ℕ} (φ : Fin N → H → ℂ)

def gram : Matrix (Fin N) (Fin N) ℂ := fun i j => ip μ (φ i) (φ j)

theorem gram_det (hc : ∀ i, Continuous (φ i)) (hli : LinearIndependent ℂ φ) : (gram μ φ).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hGv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hψc : Continuous (fun x => ∑ l, v l * φ l x) :=
    continuous_finsetSum _ fun l _ => continuous_const.mul (hc l)
  have hip : ip μ (fun x => ∑ l, v l * φ l x) (fun x => ∑ l, v l * φ l x) = 0 := by
    rw [ip_sum_left μ Finset.univ hψc v φ hc]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [ip_sum_right μ Finset.univ (hc i) v φ hc]
    have hi := congrFun hGv i
    simp only [Matrix.mulVec, dotProduct, gram, Pi.zero_apply] at hi
    rw [show ∑ l, v l * ip μ (φ i) (φ l) = ∑ l, ip μ (φ i) (φ l) * v l from
      Finset.sum_congr rfl fun l _ => mul_comm _ _, hi, mul_zero]
  have h0 := norm_sq_zero μ hψc hip
  apply hv
  funext i
  refine Fintype.linearIndependent_iff.mp hli v ?_ i
  funext x
  simpa [Finset.sum_apply] using congrFun h0 x

def coef (g : H → ℂ) : Fin N → ℂ := (gram μ φ)⁻¹ *ᵥ fun j => ip μ (φ j) g

def proj (g : H → ℂ) : H → ℂ := fun x => ∑ i, coef μ φ g i * φ i x

theorem coef_comb (hc : ∀ i, Continuous (φ i)) (hli : LinearIndependent ℂ φ) (d : Fin N → ℂ) :
    coef μ φ (fun x => ∑ l, d l * φ l x) = d := by
  have hG : IsUnit (gram μ φ).det := isUnit_iff_ne_zero.mpr (gram_det μ φ hc hli)
  have hw : (fun j => ip μ (φ j) (fun x => ∑ l, d l * φ l x)) = gram μ φ *ᵥ d := by
    funext j
    rw [ip_sum_right μ Finset.univ (hc j) d φ hc]
    simp only [Matrix.mulVec, dotProduct, gram]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  unfold coef
  rw [hw, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hG, Matrix.one_mulVec]

theorem proj_comb (hc : ∀ i, Continuous (φ i)) (hli : LinearIndependent ℂ φ) (d : Fin N → ℂ) :
    proj μ φ (fun x => ∑ l, d l * φ l x) = fun x => ∑ l, d l * φ l x := by
  unfold proj; rw [coef_comb μ φ hc hli d]

theorem ip_resid (hc : ∀ i, Continuous (φ i)) (hli : LinearIndependent ℂ φ) {g : H → ℂ} (hg : Continuous g) (k : Fin N) :
    ip μ (φ k) (fun x => g x - proj μ φ g x) = 0 := by
  have hG : IsUnit (gram μ φ).det := isUnit_iff_ne_zero.mpr (gram_det μ φ hc hli)
  have hpc : Continuous (proj μ φ g) := continuous_finsetSum _ fun i _ => continuous_const.mul (hc i)
  have key : gram μ φ *ᵥ coef μ φ g = fun j => ip μ (φ j) g := by
    unfold coef
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hG, Matrix.one_mulVec]
  have hk := congrFun key k
  simp only [Matrix.mulVec, dotProduct, gram] at hk
  rw [ip_sub μ (hc k) hg hpc]
  have hp : ip μ (φ k) (proj μ φ g) = ∑ i, coef μ φ g i * ip μ (φ k) (φ i) := by
    unfold proj
    exact ip_sum_right μ Finset.univ (hc k) _ φ hc
  rw [hp, ← hk]
  rw [show ∑ i, coef μ φ g i * ip μ (φ k) (φ i) = ∑ i, ip μ (φ k) (φ i) * coef μ φ g i from
    Finset.sum_congr rfl fun i _ => mul_comm _ _]
  ring

theorem proj_add (hc : ∀ i, Continuous (φ i)) {g g' : H → ℂ} (hg : Continuous g) (hg' : Continuous g') :
    proj μ φ (fun x => g x + g' x) = fun x => proj μ φ g x + proj μ φ g' x := by
  have hw : (fun j => ip μ (φ j) (fun x => g x + g' x)) =
      (fun j => ip μ (φ j) g) + (fun j => ip μ (φ j) g') := by
    funext j
    simp only [Pi.add_apply]
    exact ip_add μ (hc j) hg hg'
  have hcoef : coef μ φ (fun x => g x + g' x) = coef μ φ g + coef μ φ g' := by
    unfold coef
    rw [hw, Matrix.mulVec_add]
  funext x
  simp only [proj, hcoef, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem proj_left (hc : ∀ i, Continuous (φ i)) (hli : LinearIndependent ℂ φ)
    (hst : ∀ (i : Fin N) (a : H), ∃ d : Fin N → ℂ, (fun x => φ i (a * x)) = fun x => ∑ l, d l * φ l x)
    {g : H → ℂ} (hg : Continuous g) (a : H) :
    proj μ φ (fun x => g (a * x)) = fun x => proj μ φ g (a * x) := by
  have hpc : Continuous (proj μ φ g) := continuous_finsetSum _ fun i _ => continuous_const.mul (hc i)
  have hcomb : ∃ e : Fin N → ℂ, (fun x => proj μ φ g (a * x)) = fun x => ∑ l, e l * φ l x := by
    choose d hd using fun i => hst i a
    refine ⟨fun l => ∑ i, coef μ φ g i * d i l, ?_⟩
    funext x
    have hx : ∀ i, φ i (a * x) = ∑ l, d i l * φ l x := fun i => congrFun (hd i) x
    simp only [proj, hx, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  obtain ⟨e, he⟩ := hcomb
  have hgp : Continuous (fun x => g x - proj μ φ g x) := hg.sub hpc
  have hr : ∀ k, ip μ (φ k) (fun x => g (a * x) - proj μ φ g (a * x)) = 0 := by
    intro k
    have hl := ip_left μ a (φ k) (fun x => g x - proj μ φ g x)
    rw [hl]
    obtain ⟨d, hd⟩ := hst k a⁻¹
    rw [hd, ip_sum_left μ Finset.univ hgp d φ hc]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [ip_resid μ φ hc hli hg i, mul_zero]
  have hrc : Continuous (fun x => g (a * x) - proj μ φ g (a * x)) :=
    (hg.comp (continuous_const_mul a)).sub (hpc.comp (continuous_const_mul a))
  have hcoef0 : coef μ φ (fun x => g (a * x) - proj μ φ g (a * x)) = 0 := by
    unfold coef
    have hz : (fun j => ip μ (φ j) (fun x => g (a * x) - proj μ φ g (a * x))) = 0 := funext hr
    rw [hz, Matrix.mulVec_zero]
  have hproj0 : proj μ φ (fun x => g (a * x) - proj μ φ g (a * x)) = fun _ => 0 := by
    funext x
    change ∑ i, coef μ φ (fun x => g (a * x) - proj μ φ g (a * x)) i * φ i x = 0
    rw [hcoef0]
    simp
  have hpp : proj μ φ (fun x => proj μ φ g (a * x)) = fun x => proj μ φ g (a * x) := by
    rw [he]
    exact proj_comb μ φ hc hli e
  have hsplit : (fun x => g (a * x)) = fun x => proj μ φ g (a * x) + (g (a * x) - proj μ φ g (a * x)) := by
    funext x
    ring
  have hadd := proj_add μ φ hc (hpc.comp (continuous_const_mul a)) hrc
  simp only [Function.comp_def] at hadd
  rw [hsplit, hadd, hpp, hproj0]
  funext x
  simp

end RK

open RK in
theorem repKer : RepKer := by
  intro H _ _ _ _ _ _ _ μ _ V hfin hcont hinv
  let b := Module.finBasis ℂ V
  let φ : Fin (Module.finrank ℂ V) → H → ℂ := fun i => (b i : H → ℂ)
  have hc : ∀ i, Continuous (φ i) := fun i => hcont _ (b i).2
  have hli : LinearIndependent ℂ φ := b.linearIndependent.map' V.subtype V.ker_subtype
  have hmem : ∀ ψ ∈ V, ∃ d : Fin (Module.finrank ℂ V) → ℂ, ψ = fun x => ∑ l, d l * φ l x := by
    intro ψ hψ
    refine ⟨b.repr ⟨ψ, hψ⟩, ?_⟩
    have h := congrArg (fun v : V => (v : H → ℂ)) (b.sum_repr ⟨ψ, hψ⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    funext x
    have hx := congrFun h x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hx
    exact hx.symm
  have hst : ∀ (i : Fin (Module.finrank ℂ V)) (a : H), ∃ d : Fin (Module.finrank ℂ V) → ℂ,
      (fun x => φ i (a * x)) = fun x => ∑ l, d l * φ l x :=
    fun i a => hmem _ (hinv _ (b i).2 a)
  have hcombV : ∀ c : Fin (Module.finrank ℂ V) → ℂ, (fun x => ∑ l, c l * φ l x) ∈ V := by
    intro c
    have hfun : (fun x => ∑ l, c l * φ l x) = ∑ l, c l • φ l := by
      funext x
      simp [Finset.sum_apply]
    rw [hfun]
    exact V.sum_mem fun l _ => V.smul_mem _ (b l).2
  have key : ∀ f : H → ℂ, Continuous f → ∀ x,
      ∫ v, star (∑ j, star (∑ i, φ i 1 * (gram μ φ)⁻¹ i j) * φ j v) * f (x * v) ∂μ = proj μ φ f x := by
    intro f hf x
    have hfx : Continuous (fun v => f (x * v)) := hf.comp (continuous_const_mul x)
    have h1 : ∫ v, star (∑ j, star (∑ i, φ i 1 * (gram μ φ)⁻¹ i j) * φ j v) * f (x * v) ∂μ =
        ip μ (fun v => ∑ j, star (∑ i, φ i 1 * (gram μ φ)⁻¹ i j) * φ j v) (fun v => f (x * v)) := rfl
    rw [h1, ip_sum_left μ Finset.univ hfx _ φ hc]
    have h3 := congrFun (proj_left μ φ hc hli hst hf x) 1
    simp only [mul_one] at h3
    rw [← h3]
    simp only [proj, coef, Matrix.mulVec, dotProduct, star_star, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  refine ⟨fun v => star (∑ j, star (∑ i, φ i 1 * (gram μ φ)⁻¹ i j) * φ j v), ?_, ?_, ?_⟩
  · exact continuous_star.comp (continuous_finsetSum _ fun j _ => continuous_const.mul (hc j))
  · intro f hf
    have hfun : (fun x => ∫ v, star (∑ j, star (∑ i, φ i 1 * (gram μ φ)⁻¹ i j) * φ j v) * f (x * v) ∂μ) =
        proj μ φ f := funext (key f hf)
    rw [hfun]
    exact hcombV (coef μ φ f)
  · intro ψ hψ x
    obtain ⟨d, hd⟩ := hmem ψ hψ
    rw [key ψ (hcont ψ hψ) x, hd, proj_comb μ φ hc hli d]

end PositivityTheory.Rg.Sw.AbsSt.Proj
end
end

noncomputable section

open MeasureTheory Matrix Set Topology

namespace PositivityTheory.Rg.Sw.AbsSt.Proj

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

theorem cpt_unitary (n : ℕ) : IsCompact (unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) := by
  have hsub : (unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) ⊆
      Set.pi Set.univ (fun _ => Set.pi Set.univ (fun _ => Metric.closedBall (0 : ℂ) 1)) := by
    intro U hU i _ j _
    simpa using entry_norm_bound_of_unitary hU i j
  refine (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
    isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset ?_ hsub
  have hset : (unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) =
      {A | star A * A = 1 ∧ A * star A = 1} := by
    ext A
    exact Iff.rfl
  rw [hset]
  have h1 : Continuous fun A : Matrix (Fin n) (Fin n) ℂ => star A * A := by fun_prop
  have h2 : Continuous fun A : Matrix (Fin n) (Fin n) ℂ => A * star A := by fun_prop
  exact (isClosed_eq h1 continuous_const).inter (isClosed_eq h2 continuous_const)

instance cptU (n : ℕ) : CompactSpace (unitaryGroup (Fin n) ℂ) :=
  isCompact_iff_compactSpace.mp (cpt_unitary n)

variable {n : ℕ}

def kE (hK : KIso) (a b : unitaryGroup (Fin n) ℂ) : GR n := Classical.choose ((hK n).1 a.1 b.1 a.2 b.2)

theorem kE_mem (hK : KIso) (a b : unitaryGroup (Fin n) ℂ) : kE hK a b ∈ KR n :=
  (Classical.choose_spec ((hK n).1 a.1 b.1 a.2 b.2)).1

theorem mR_kE (hK : KIso) (a b : unitaryGroup (Fin n) ℂ) : mR (kE hK a b) = kM a.1 b.1 :=
  (Classical.choose_spec ((hK n).1 a.1 b.1 a.2 b.2)).2

theorem mR_inj {g h : GR n} (e : mR g = mR h) : g = h := Subtype.ext (Units.ext e)

theorem mR_mul (g h : GR n) : mR (g * h) = mR g * mR h := rfl

theorem kE_mul (hK : KIso) (a b a' b' : unitaryGroup (Fin n) ℂ) :
    kE hK a b * kE hK a' b' = kE hK (a * a') (b * b') := by
  apply mR_inj
  rw [mR_mul, mR_kE, mR_kE, mR_kE, (hK n).2.1]
  rfl

theorem mR_inv_kE (hK : KIso) (a b : unitaryGroup (Fin n) ℂ) : mR (kE hK a b)⁻¹ = kM (a⁻¹ : unitaryGroup (Fin n) ℂ).1 (b⁻¹ : unitaryGroup (Fin n) ℂ).1 := by
  have h1 : kE hK a b * kE hK a⁻¹ b⁻¹ = 1 := by
    rw [kE_mul, mul_inv_cancel, mul_inv_cancel]
    apply mR_inj
    rw [mR_kE]
    exact (hK n).2.2.1
  have h2 : (kE hK a b)⁻¹ = kE hK a⁻¹ b⁻¹ := (eq_inv_of_mul_eq_one_right h1).symm
  rw [h2, mR_kE]

theorem continuous_mR : Continuous (fun g : GR n => mR g) :=
  Units.continuous_val.comp continuous_subtype_val

theorem continuous_kM : Continuous (fun ab : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ => kM ab.1 ab.2) := by
  unfold kM
  refine Continuous.matrix_fromBlocks ?_ ?_ ?_ ?_ <;> fun_prop

theorem continuous_kE (hK : KIso) (a : unitaryGroup (Fin n) ℂ) : Continuous (fun b : unitaryGroup (Fin n) ℂ => kE hK a b) := by
  refine continuous_induced_rng.2 ((Units.continuous_iff).2 ⟨?_, ?_⟩)
  · exact (continuous_kM.comp (continuous_const.prodMk continuous_subtype_val)).congr
      fun b => (mR_kE hK a b).symm
  · exact (continuous_kM.comp (continuous_const.prodMk
      (continuous_subtype_val.comp continuous_inv))).congr fun b => (mR_inv_kE hK a b).symm

theorem continuous_second_cayley_block_map : Continuous (fun M : M2 n => u2 M) := by
  have h21 : Continuous (fun M : M2 n => M.toBlocks₂₁) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact (continuous_apply (Sum.inl j)).comp (continuous_apply (Sum.inr i))
  have h22 : Continuous (fun M : M2 n => M.toBlocks₂₂) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact (continuous_apply (Sum.inr j)).comp (continuous_apply (Sum.inr i))
  unfold u2
  exact ((h21.const_smul Complex.I).neg).add h22

theorem lower_left_block_mul {X Y : M2 n} (hX : X.toBlocks₂₁ = 0) (hY : Y.toBlocks₂₁ = 0) : (X * Y).toBlocks₂₁ = 0 := by
  rw [← fromBlocks_toBlocks X, ← fromBlocks_toBlocks Y, fromBlocks_multiply, toBlocks_fromBlocks₂₁, hX, hY]
  simp

theorem projOp_of (hK : KIso) (hR : RepKer) (hI : Iwa) (hM : Mult) : ProjOp := by
  intro m n ε c t p q e sL ρ hL _ _ W hW hWinv
  letI : MeasurableSpace (unitaryGroup (Fin n) ℂ) := borel _
  haveI : BorelSpace (unitaryGroup (Fin n) ℂ) := ⟨rfl⟩
  let μ : Measure (unitaryGroup (Fin n) ℂ) := Measure.haar
  let L : PX m n →ₗ[ℂ] (unitaryGroup (Fin n) ℂ → ℂ) :=
    LinearMap.funLeft ℂ ℂ (fun c : unitaryGroup (Fin n) ℂ => kE hK 1 c) ∘ₗ sL
  have hLapp : ∀ (P : PX m n) (c : unitaryGroup (Fin n) ℂ), L P c = sL P (kE hK 1 c) :=
    fun _ _ => rfl
  have hVfin : FiniteDimensional ℂ (W.map L) := inferInstance
  have hupK : ∀ a : unitaryGroup (Fin n) ℂ, toBlocks₂₁ (mR (kE hK a a)) = 0 := by
    intro a
    rw [mR_kE]
    exact (hK n).2.2.2.2.1 a.1
  have hVcont : ∀ φ ∈ W.map L, Continuous φ := by
    rintro φ ⟨P, -, rfl⟩
    show Continuous fun c => sL P (kE hK 1 c)
    exact (hL.cont P).comp (continuous_kE hK 1)
  have hVinv : ∀ φ ∈ W.map L, ∀ a : unitaryGroup (Fin n) ℂ,
      (fun x : unitaryGroup (Fin n) ℂ => φ (a * x)) ∈ W.map L := by
    rintro φ ⟨P, hP, rfl⟩ a
    refine ⟨F0 p q e (kE hK a a) • ρ (kE hK a⁻¹ 1) P,
      W.smul_mem _ (hWinv _ (kE_mem hK a⁻¹ 1) P hP), ?_⟩
    funext x
    have hx : kE hK 1 (a * x) = kE hK a a * (kE hK 1 x * kE hK a⁻¹ 1) := by
      rw [kE_mul, kE_mul]
      simp
    show sL (F0 p q e (kE hK a a) • ρ (kE hK a⁻¹ 1) P) (kE hK 1 x) = sL P (kE hK 1 (a * x))
    rw [hx, hL.law _ _ _ (hupK a), hL.kact _ _ _ (kE_mem hK a⁻¹ 1), map_smul,
      Pi.smul_apply, smul_eq_mul]
  obtain ⟨κ0, hκ0c, hκ0img, hκ0fix⟩ := hR (unitaryGroup (Fin n) ℂ) μ (W.map L) hVfin hVcont hVinv
  have hu2mem : ∀ k : KR n, u2 (mR (k : GR n)) ∈ unitaryGroup (Fin n) ℂ :=
    fun k => ((hK n).2.2.2.2.2 (k : GR n) k.2).2.1
  let κ : KR n → ℂ := fun k => κ0 ⟨u2 (mR (k : GR n)), hu2mem k⟩
  let eK : unitaryGroup (Fin n) ℂ → KR n := fun v => ⟨kE hK 1 v, kE_mem hK 1 v⟩
  have heK : Continuous eK := (continuous_kE hK 1).subtype_mk _
  have hκe : ∀ v, κ (eK v) = κ0 v := by
    intro v
    show κ0 _ = κ0 v
    congr 1
    apply Subtype.ext
    show u2 (mR (kE hK 1 v)) = v.1
    rw [mR_kE]
    exact ((hK n).2.2.2.1 1 v.1).2
  have hκc : Continuous κ :=
    hκ0c.comp ((continuous_second_cayley_block_map.comp (continuous_mR.comp continuous_subtype_val)).subtype_mk _)
  have hint : ∀ g : KR n → ℂ, Continuous g →
      ∫ k, κ k * g k ∂(μ.map eK) = ∫ v, κ0 v * g (eK v) ∂μ := by
    intro g hg
    have hm : Continuous fun k => κ k * g k := hκc.mul hg
    rw [integral_map (f := fun k => κ k * g k) heK.measurable.aemeasurable hm.aestronglyMeasurable]
    simp only [hκe]
  have hdec : ∀ y : GR n, ∃ (p' : GR n) (c : unitaryGroup (Fin n) ℂ),
      toBlocks₂₁ (mR p') = 0 ∧ y = p' * kE hK 1 c := by
    intro y
    obtain ⟨p0, k0, hp0, hk0, rfl⟩ := hI n y
    obtain ⟨ha, hb, hk⟩ := (hK n).2.2.2.2.2 k0 hk0
    have hk0e : k0 = kE hK ⟨_, ha⟩ ⟨_, hb⟩ := mR_inj (by rw [mR_kE]; exact hk)
    refine ⟨p0 * kE hK ⟨_, ha⟩ ⟨_, ha⟩, (⟨_, ha⟩ : unitaryGroup (Fin n) ℂ)⁻¹ * ⟨_, hb⟩, ?_, ?_⟩
    · rw [mR_mul]
      exact lower_left_block_mul hp0 (hupK _)
    · rw [mul_assoc, kE_mul]
      simp only [mul_one, mul_inv_cancel_left]
      exact congrArg (p0 * ·) hk0e
  refine ⟨μ.map eK, κ, inferInstance, hκc, ?_, ?_⟩
  · intro Q hQ y
    obtain ⟨p', c, hp', rfl⟩ := hdec y
    rw [hint (fun k : KR n => sL Q (p' * kE hK 1 c * (k : GR n)))
      ((hL.cont Q).comp (continuous_const.mul continuous_subtype_val))]
    have h1 : ∀ v, κ0 v * sL Q (p' * kE hK 1 c * ((eK v : KR n) : GR n)) =
        F0 p q e p' * (κ0 v * L Q (c * v)) := by
      intro v
      show κ0 v * sL Q (p' * kE hK 1 c * kE hK 1 v) = F0 p q e p' * (κ0 v * sL Q (kE hK 1 (c * v)))
      rw [mul_assoc, kE_mul, one_mul, hL.law _ _ _ hp']
      ring
    simp only [h1]
    rw [integral_const_mul, hκ0fix (L Q) ⟨Q, hQ, rfl⟩ c, hL.law _ _ _ hp', hLapp]
  · intro w f hf hfeq
    obtain ⟨Q, hQ, hQeq⟩ := hκ0img (fun c => f (kE hK 1 c)) (hf.comp (continuous_kE hK 1))
    refine ⟨Q, hQ, fun y => ?_⟩
    obtain ⟨p', c, hp', rfl⟩ := hdec y
    rw [hint (fun k : KR n => f (p' * kE hK 1 c * (k : GR n)))
      (hf.comp (continuous_const.mul continuous_subtype_val))]
    have h2 : ∀ v, κ0 v * f (p' * kE hK 1 c * ((eK v : KR n) : GR n)) =
        ((hLoc p' : ℂ) ^ w * F0 p q e p') * (κ0 v * f (kE hK 1 (c * v))) := by
      intro v
      show κ0 v * f (p' * kE hK 1 c * kE hK 1 v) = _
      rw [mul_assoc, kE_mul, one_mul, hfeq _ _ hp']
      ring
    simp only [h2]
    have hc := congrFun hQeq c
    rw [integral_const_mul, ← hc, hLapp, hL.law _ _ _ hp',
      ((hM n p q e).1 p' (kE hK 1 c) (kE_mem hK 1 c)).2]
    ring

theorem projOp (hI : Iwa) (hM : Mult) : ProjOp := projOp_of kIso repKer hI hM

end PositivityTheory.Rg.Sw.AbsSt.Proj
end
end

namespace PositivityTheory.Rg.Sw.AbsSt

theorem genCore : Iwa → CayleyBlocksInvertible → KAK → Mult → SecZero → DerivativeVacuumDilations → CycSec → HolParam → Glue → LC → GenCore :=
  fun hI hD hK hM hS hDF hC hH hG hLC =>
    genCore_of (Proj.projOp hI hM) (tsGenC_of hD hK hM hS hDF hH hLC tsbFacts) (basis hI hD hM hC hH)
      (farRightC hI hD hM hH) hS hLC hH hG

theorem absThm_of' (hV : VacOut) (hI : Iwa) (hD : CayleyBlocksInvertible) (hK : KAK) (hM : Mult) (hS : SecZero) (hDF : DerivativeVacuumDilations)
    (hC : CycSec) (_hSph : Sph) (hH : HolParam) (hG : Glue) (hLC : LC) (_hN : NullIff) : AbsThm :=
  absThm_gen hV (Proj.projOp hI hM) (tsGen hI hD hK hM hS hDF hH hLC) (basis hI hD hM hC hH) (farRight hI hD hM hH)
    hS hLC hH hG

end PositivityTheory.Rg.Sw.AbsSt
