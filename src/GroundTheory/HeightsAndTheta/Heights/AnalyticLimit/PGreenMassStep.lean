module

public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.EnergyStep

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PGreenMassStepA
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory Filter Topology
open scoped ContDiff
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsSection IsSNC mInt MIntegrable logNormSec)

noncomputable section

variable {e : ℕ} {W : Type} [TopologicalSpace W] {A : FinHolAtlas e W} {L : LocPot W}
  {s : W → W → ℂ}

theorem secNorm_eq_local (hs : IsSection A L s) {x y : W} (hy : y ∈ L.U x) :
    secNorm L s y = ‖s x y‖ * Real.exp (-L.φ x y) :=
  hs.2 y x y ⟨L.mem_U y, hy⟩

theorem smooth_secNorm_sq (hL : IsPotential A L) (hs : IsSection A L s) :
    A.Smooth fun x => secNorm L s x ^ 2 := by
  intro j
  refine contDiffOn_of_locally_contDiffOn fun y hy => ?_
  refine ⟨(A.chart j).target ∩ (A.chart j).symm ⁻¹' L.U ((A.chart j).symm y),
    (A.chart j).isOpen_inter_preimage_symm (L.isOpen_U _), ⟨hy.1, L.mem_U _⟩, ?_⟩
  set p := (A.chart j).symm y
  have h1 : ContDiffOn ℝ ∞ (fun z => ‖s p ((A.chart j).symm z)‖ ^ 2)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' L.U p) :=
    contDiff_norm_sq ℝ |>.comp_contDiffOn
      (((hs.1 p j).contDiffOn_of_completeSpace (n := ∞)).restrict_scalars ℝ)
  have h2 : ContDiffOn ℝ ∞ (fun z => Real.exp (-L.φ p ((A.chart j).symm z)) ^ 2)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' L.U p) :=
    (Real.contDiff_exp.comp_contDiffOn (hL.1 p j).neg).pow 2
  refine ((h1.mul h2).mono (fun z (hz : z ∈ ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Set.univ) ∩ ((A.chart j).target ∩ (A.chart j).symm ⁻¹' L.U p)) => hz.2)).congr fun z hz => ?_
  simp only [Function.comp_apply]
  rw [secNorm_eq_local hs hz.2.2, mul_pow]

theorem smooth_log_secNorm_sq_add (hL : IsPotential A L) (hs : IsSection A L s) {ε : ℝ}
    (hε : 0 < ε) : A.Smooth fun x => Real.log (secNorm L s x ^ 2 + ε) := by
  intro j
  have h1 : ContDiffOn ℝ ∞ (fun z => secNorm L s ((A.chart j).symm z) ^ 2 + ε)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Set.univ) :=
    (smooth_secNorm_sq hL hs j).add contDiffOn_const
  exact h1.log fun z _ => (add_pos_of_nonneg_of_pos (sq_nonneg _) hε).ne'

def secZero (L : LocPot W) (s : W → W → ℂ) : Set W := {x | secNorm L s x = 0}

theorem mem_secZero_iff_local (hs : IsSection A L s) {x y : W} (hy : y ∈ L.U x) :
    y ∈ secZero L s ↔ s x y = 0 := by
  show secNorm L s y = 0 ↔ _
  rw [secNorm_eq_local hs hy, mul_eq_zero, norm_eq_zero]
  simp [(Real.exp_pos _).ne']

theorem isAnalyticSubset_secZero (hs : IsSection A L s) : A.IsAnalyticSubset (secZero L s) := by
  intro x
  refine ⟨L.U x, L.isOpen_U x, L.mem_U x, 1, fun _ => s x, fun _ => hs.1 x, ?_⟩
  ext y
  simp only [Set.mem_inter_iff, Set.mem_sep_iff]
  constructor
  · rintro ⟨h, hy⟩
    exact ⟨hy, fun _ => (mem_secZero_iff_local hs hy).1 h⟩
  · rintro ⟨hy, h⟩
    exact ⟨(mem_secZero_iff_local hs hy).2 (h 0), hy⟩

theorem interior_secZero {r : ℕ} {m : Fin r → ℕ} {Δ : Fin r → Set W} (hs : IsSection A L s)
    (hsnc : IsSNC A L s m Δ) : interior (secZero L s) = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 fun x hx => ?_
  obtain ⟨U, hUZ, hU, hxU⟩ := mem_interior.1 hx
  obtain ⟨ψ, -, hxψ, hψL, σ, -, -, v, -, hv0, hsx⟩ := hsnc x
  have hcoord : ∀ y ∈ ψ.source, y ∈ U → ∃ i, ψ y i = 0 := by
    intro y hy hyU
    have h0 : s x y = 0 := (mem_secZero_iff_local hs (hψL hy)).1 (hUZ hyU)
    rw [hsx y hy, mul_eq_zero] at h0
    rcases h0 with h0 | h0
    · exact absurd h0 (hv0 y hy)
    · obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.1 h0
      cases hσ : σ k with
      | none => simp [hσ] at hk
      | some i =>
        simp only [hσ] at hk
        exact ⟨i, eq_zero_of_pow_eq_zero hk⟩
  have hO : IsOpen (ψ.target ∩ ψ.symm ⁻¹' U) := ψ.isOpen_inter_preimage_symm hU
  have hxO : ψ x ∈ ψ.target ∩ ψ.symm ⁻¹' U :=
    ⟨ψ.map_source hxψ, by simp [ψ.left_inv hxψ, hxU]⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hO _ hxO
  let w : Fin e → ℂ := fun i => if ψ x i = 0 then ((δ / 2 : ℝ) : ℂ) else ψ x i
  have hw0 : ∀ i, w i ≠ 0 := by
    intro i
    by_cases h : ψ x i = 0
    · simp only [w, if_pos h, ne_eq, Complex.ofReal_eq_zero]
      linarith
    · simp only [w, if_neg h]
      exact h
  have hwb : w ∈ Metric.ball (ψ x) δ := by
    rw [Metric.mem_ball, dist_eq_norm, pi_norm_lt_iff hδ]
    intro i
    by_cases h : ψ x i = 0
    · rw [Pi.sub_apply]
      simp only [w]
      rw [if_pos h, h, sub_zero, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      linarith
    · simp only [w, Pi.sub_apply, if_neg h, sub_self, norm_zero]
      exact hδ
  obtain ⟨hwt, hwU⟩ := hball hwb
  obtain ⟨i, hi⟩ := hcoord _ (ψ.map_target hwt) hwU
  rw [ψ.right_inv hwt] at hi
  exact hw0 i hi

def greenSplit (L : LocPot W) (s : W → W → ℂ) (ε : ℝ) (x : W) : ℝ :=
  (-2) * logNormSec L s x + Real.log (secNorm L s x ^ 2 + ε)

theorem greenEp_eq_split {ε : ℝ} (hε : 0 < ε) {x : W} (hx : x ∉ secZero L s) :
    greenEp L s ε x = greenSplit L s ε x := by
  have hn : secNorm L s x ≠ 0 := hx
  have hn2 : secNorm L s x ^ 2 ≠ 0 := pow_ne_zero 2 hn
  have hlog : logNormSec L s x = Real.log (secNorm L s x) := rfl
  unfold greenEp greenSplit
  rw [hlog, one_add_div hn2, Real.log_div (add_pos_of_nonneg_of_pos (sq_nonneg _) hε).ne' hn2,
    Real.log_pow]
  push_cast
  ring

theorem mIntegrable_greenSplit [CompactSpace W] [T2Space W] {r : ℕ} {m : Fin r → ℕ}
    {Δ : Fin r → Set W} (hL : IsPotential A L) (hs : IsSection A L s) (hsnc : IsSNC A L s m Δ)
    {ε : ℝ} (hε : 0 < ε) (Φ : Fin e → LocPot W) (hΦ : ∀ i, IsPotential A (Φ i)) :
    MIntegrable A Φ (greenSplit L s ε) := by
  have h1 := ReciprocityTheory.AnForm.M.logNormIntegrable A L s m Δ hL hs hsnc Φ hΦ
  have h2 := ReciprocityTheory.AnForm.M.mIntegrableCont A Φ hΦ _
    (ReciprocityTheory.AnForm.M.PLC.continuous_of_smooth A (smooth_log_secNorm_sq_add hL hs hε))
  intro j K hK hc
  have : IntegrableOn (fun y => -2 * (logNormSec L s ((A.chart j).symm y) *
      ReciprocityTheory.AnForm.M.locDens A Φ j y) + Real.log (secNorm L s ((A.chart j).symm y) ^ 2 + ε) *
      ReciprocityTheory.AnForm.M.locDens A Φ j y) K :=
    ((h1 j K hK hc).const_mul (-2)).add (h2 j K hK hc)
  refine this.congr_fun (fun y _ => ?_) hc.measurableSet
  simp only [greenSplit]
  ring

theorem mInt_greenEp_eq_split {r : ℕ} {m : Fin r → ℕ} {Δ : Fin r → Set W} (hs : IsSection A L s)
    (hsnc : IsSNC A L s m Δ) {ε : ℝ} (hε : 0 < ε) (Φ : Fin e → LocPot W) :
    mInt A Φ (greenEp L s ε) = mInt A Φ (greenSplit L s ε) :=
  by
    unfold ReciprocityTheory.AnForm.M.mInt
    split_ifs with h
    · exact ReciprocityTheory.AnForm.M.integralWith_congr_null A h.some Φ
        (isAnalyticSubset_secZero hs) (interior_secZero hs hsnc) (fun _ hx => greenEp_eq_split hε hx)
    · rfl

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PGreenMassStepB
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory Filter Topology
open scoped ContDiff
open ReciprocityTheory.AnForm (levi levi_add_smul levi_zero continuousOn_levi)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPsh isPotential_ofFun)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (ell)

noncomputable section

theorem two_le_top_gms : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top

variable {e : ℕ} {W : Type} [TopologicalSpace W] {A : FinHolAtlas e W}

def formDiff (Om th : LocPot W) : LocPot W := Om + th.rsmul (-1)

theorem isPotential_formDiff {Om th : LocPot W} (hO : IsPotential A Om) (hth : IsPotential A th) :
    IsPotential A (formDiff Om th) :=
  ReciprocityTheory.AnForm.M.isPotentialAdd A _ _ hO (ReciprocityTheory.AnForm.M.isPotentialRsmul A _ _ hth)

theorem isPsh_formDiff {Om th : LocPot W} (hO : IsPotential A Om) (hth : IsPotential A th)
    (hle : LeviLe A Set.univ 1 th 1 Om) : IsPsh A (formDiff Om th) := by
  intro x j y hy w
  have h1 := (ReciprocityTheory.AnForm.M.contDiffAt_of_isPotential A Om hO x j
    ⟨hy.1, hy.2.1⟩).of_le two_le_top_gms
  have h2 := (ReciprocityTheory.AnForm.M.contDiffAt_of_isPotential A th hth x j
    ⟨hy.1, hy.2.2⟩).of_le two_le_top_gms
  have hl := levi_add_smul (-1) h1 h2 w
  have hle' := hle x j y ⟨hy.1, ⟨Set.mem_univ _, hy.2.2⟩, hy.2.1⟩ w
  have heq : (formDiff Om th).φ x ∘ (A.chart j).symm =
      fun z => (Om.φ x ∘ (A.chart j).symm) z + (-1) * (th.φ x ∘ (A.chart j).symm) z := rfl
  rw [heq, hl]
  linarith

theorem add_formDiff_φ (Om th : LocPot W) (x y : W) : (th + formDiff Om th).φ x y = Om.φ x y := by
  show th.φ x y + (Om.φ x y + -1 * th.φ x y) = Om.φ x y
  ring

theorem isPsh_of_formNonneg_dense {P : LocPot W} {Yo : Set W} (hP : IsPotential A P)
    (hd : Dense Yo) (hn : FormNonneg A Yo P) : IsPsh A P := by
  intro x j y hy w
  have hOo : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x) :=
    (A.chart j).isOpen_inter_preimage_symm (P.isOpen_U x)
  obtain ⟨F, hF⟩ : ∃ F, F = P.φ x ∘ (A.chart j).symm := ⟨_, rfl⟩
  have hFs : ContDiffOn ℝ 2 F ((A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x) := by
    rw [hF]
    exact (hP.1 x j).of_le two_le_top_gms
  rw [← hF]
  have hpair : ContinuousAt (fun p : (Fin e → ℂ) × (Fin e → ℂ) => levi F p.1 p.2) (y, w) :=
    (continuousOn_levi hOo hFs).continuousAt (prod_mem_nhds (hOo.mem_nhds hy) Filter.univ_mem)
  have hc : ContinuousAt (fun z => levi F z w) y :=
    hpair.comp (f := fun z => (z, w)) (continuousAt_id.prodMk continuousAt_const)
  by_contra hneg
  rw [not_le] at hneg
  have hN : {z | levi F z w < 0} ∩
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x) ∈ 𝓝 y :=
    Filter.inter_mem (hc.preimage_mem_nhds (Iio_mem_nhds hneg)) (hOo.mem_nhds hy)
  obtain ⟨V, hVN, hVo, hyV⟩ := mem_nhds_iff.1 hN
  have hVt : V ⊆ (A.chart j).target := fun z hz => (hVN hz).2.1
  have himg : IsOpen ((A.chart j).symm '' V) := by
    have := (A.chart j).symm.isOpen_image_source_inter hVo
    rwa [OpenPartialHomeomorph.symm_source, Set.inter_eq_right.2 hVt] at this
  obtain ⟨p, ⟨z, hzV, rfl⟩, hpY⟩ := hd.inter_open_nonempty _ himg ⟨_, y, hyV, rfl⟩
  have h0 := hn x j z ⟨(hVN hzV).2.1, hpY, (hVN hzV).2.2⟩ w
  rw [← hF] at h0
  exact absurd (hVN hzV).1 (not_lt.2 h0)

theorem forall_cons_of {n : ℕ} {p : LocPot W → Prop} {P : LocPot W} {Φ : Fin n → LocPot W}
    (h0 : p P) (h : ∀ i, p (Φ i)) : ∀ i, p ((Fin.cons P Φ : Fin (n + 1) → LocPot W) i) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using h0
  · simpa using h j

namespace UIData

variable {D : ℕ} (S : UIData D W)

theorem T_isPotential {t : ℝ} (ht : 0 < t) (hℓ : S.ell₀ ≤ ell t) (b : Fin (D + 1)) :
    IsPotential S.A (S.T t b) :=
  ReciprocityTheory.AnForm.M.isPotentialAdd S.A _ _ (S.form b t ht hℓ).1.th_pot
    (isPotential_ofFun S.A _ (S.form b t ht hℓ).2)

theorem dense_Yo : Dense S.Yo := by
  have h := interior_eq_empty_iff_dense_compl.1 S.bd_interior
  rwa [compl_compl] at h

theorem T_isPsh {t : ℝ} (ht : 0 < t) (hℓ : S.ell₀ ≤ ell t) (b : Fin (D + 1)) :
    IsPsh S.A (S.T t b) :=
  isPsh_of_formNonneg_dense (S.T_isPotential ht hℓ b) S.dense_Yo (S.form b t ht hℓ).1.nonneg

theorem rest_isPotential {t : ℝ} (ht : 0 < t) (hℓ : S.ell₀ ≤ ell t) (a : ℕ) (i : Fin D) :
    IsPotential S.A (S.rest a t i) := by
  unfold rest restForms
  split_ifs
  · exact S.T_isPotential ht hℓ _
  · exact S.Om.isPot

theorem rest_isPsh {t : ℝ} (ht : 0 < t) (hℓ : S.ell₀ ≤ ell t) (a : ℕ) (i : Fin D) :
    IsPsh S.A (S.rest a t i) := by
  unfold rest restForms
  split_ifs
  · exact S.T_isPsh ht hℓ _
  · exact S.Om.isPsh

end UIData

theorem mixedForms_cycle {D : ℕ} (Om : LocPot W) (T : Fin (D + 1) → LocPot W) (a : ℕ)
    (ha : a < D + 1) (b : ℕ) (hb : b = a ∨ b = a + 1) :
    mixedForms Om T b ∘ (Fin.cycleRange (⟨a, ha⟩ : Fin (D + 1))).symm =
      Fin.cons (mixedForms Om T b ⟨a, ha⟩) (restForms Om T a) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [Fin.cycleRange_symm_zero]
  · simp only [Function.comp_apply, Fin.cons_succ, Fin.cycleRange_symm_succ]
    by_cases hj : (j : ℕ) < a
    · rw [Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_def]; simpa using hj)]
      simp only [mixedForms, restForms, Fin.val_castSucc, hj, if_true]
      rw [if_pos (by omega)]
    · rw [Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_def]; simp; omega)]
      simp only [mixedForms, restForms, Fin.val_succ, hj, if_false]
      rw [if_neg (by omega)]

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPsh MIntegrable mInt logNormSec
  isPotential_ofFun mIntSymm mIntAdd mIntRsmul mIntLinear mIntNonneg mIntegrableCont
  logNormIntegrable poincareLelong byPartsSymm isPotentialRsmul)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (ell)

noncomputable section

theorem GreenMassStep.proof : GreenMassStep.Statement := by
  intro D W _ _ _ S a ha ε t hε ht hℓ
  set a' : Fin (D + 1) := ⟨a, ha⟩ with ha'
  have hform := S.form a' t ht hℓ
  have hu : S.A.Smooth (S.u a' t) := hform.2
  have hΦ : ∀ i, IsPotential S.A (S.rest a t i) := S.rest_isPotential ht hℓ a
  have hth : IsPotential S.A (S.th a') := hform.1.th_pot
  have huP : IsPotential S.A (LocPot.ofFun (S.u a' t)) := isPotential_ofFun S.A _ hu
  have hf : S.A.Smooth fun x => Real.log (secNorm S.L S.s x ^ 2 + ε) :=
    smooth_log_secNorm_sq_add S.L_pot S.s_sec hε
  have hDd : IsPotential S.A (formDiff S.Om.pot (S.th a')) := isPotential_formDiff S.Om.isPot hth
  have hcons := fun (P : LocPot W) (hP : IsPotential S.A P) =>
    forall_cons_of (p := IsPotential S.A) (Φ := S.rest a t) hP hΦ
  have hGi := fun (P : LocPot W) (hP : IsPotential S.A P) =>
    mIntegrable_greenSplit S.L_pot S.s_sec S.s_snc hε _ (hcons P hP)
  have hG := fun Ψ => mInt_greenEp_eq_split (A := S.A) (Φ := Ψ) S.s_sec S.s_snc hε

  have hJ1 : S.J (a + 1) ε t =
      mInt S.A (Fin.cons (S.th a' + LocPot.ofFun (S.u a' t)) (S.rest a t)) (greenSplit S.L S.s ε) := by
    have h := mixedForms_cycle S.Om.pot (S.T t) a ha (a + 1) (Or.inr rfl)
    have h0 : mixedForms S.Om.pot (S.T t) (a + 1) a' = S.th a' + LocPot.ofFun (S.u a' t) := by
      simp [mixedForms, a', UIData.T, curForms, potForm]
    rw [h0] at h
    show mInt S.A (mixedForms S.Om.pot (S.T t) (a + 1)) (greenEp S.L S.s ε) = _
    rw [← mIntSymm S.A (mixedForms S.Om.pot (S.T t) (a + 1)) (Fin.cycleRange a').symm, h, hG]
    rfl
  have hJ0 : S.J a ε t = mInt S.A (Fin.cons S.Om.pot (S.rest a t)) (greenEp S.L S.s ε) := by
    have h := mixedForms_cycle S.Om.pot (S.T t) a ha a (Or.inl rfl)
    have h0 : mixedForms S.Om.pot (S.T t) a a' = S.Om.pot := by simp [mixedForms, a']
    rw [h0] at h
    show mInt S.A (mixedForms S.Om.pot (S.T t) a) (greenEp S.L S.s ε) = _
    rw [← mIntSymm S.A (mixedForms S.Om.pot (S.T t) a) (Fin.cycleRange a').symm, h]
    rfl

  have hOm : mInt S.A (Fin.cons S.Om.pot (S.rest a t)) (greenEp S.L S.s ε) =
      mInt S.A (Fin.cons (S.th a') (S.rest a t)) (greenSplit S.L S.s ε) +
        mInt S.A (Fin.cons (formDiff S.Om.pot (S.th a')) (S.rest a t)) (greenSplit S.L S.s ε) := by
    rw [hG, ReciprocityTheory.AnForm.M.PLC.mInt_congr_phi S.A _
      (Fin.cons (S.th a' + formDiff S.Om.pot (S.th a')) (S.rest a t)) ?_]
    · exact mIntAdd S.A _ _ _ hth hDd hΦ _ (hGi _ hth) (hGi _ hDd)
    · intro i x y
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Fin.cons_zero]
        exact (add_formDiff_φ _ _ x y).symm
      · simp only [Fin.cons_succ]
  have hpos : 0 ≤ mInt S.A (Fin.cons (formDiff S.Om.pot (S.th a')) (S.rest a t))
      (greenSplit S.L S.s ε) := by
    rw [← hG]
    exact mIntNonneg S.A _ (hcons _ hDd)
      (forall_cons_of (p := IsPsh S.A) (isPsh_formDiff S.Om.isPot hth hform.1.th_le)
        (S.rest_isPsh ht hℓ a)) _ (greenEp_nonneg S.L S.s hε.le)

  have hU : mInt S.A (Fin.cons (LocPot.ofFun (S.u a' t)) (S.rest a t)) (greenSplit S.L S.s ε) =
      mInt S.A (Fin.cons (LocPot.ofFun fun x => Real.log (secNorm S.L S.s x ^ 2 + ε)) (S.rest a t))
          (S.u a' t) + 2 * mInt S.A (Fin.cons S.L (S.rest a t)) (S.u a' t) -
        2 * S.divInt (S.rest a t) (S.u a' t) := by
    have hlin := mIntLinear S.A _ (hcons _ huP) (-2) (logNormSec S.L S.s)
      (fun x => Real.log (secNorm S.L S.s x ^ 2 + ε))
      (logNormIntegrable S.A S.L S.s S.mult S.comp S.L_pot S.s_sec S.s_snc _ (hcons _ huP))
      (mIntegrableCont S.A _ (hcons _ huP) _ (ReciprocityTheory.AnForm.M.PLC.continuous_of_smooth S.A hf))
    have hpl := poincareLelong S.A S.L S.s S.mult S.comp S.B S.L_pot S.s_sec S.s_snc S.B_holo
      (S.u a' t) hu (S.rest a t) hΦ
    have hbp := byPartsSymm S.A _ (S.u a' t) hf hu (S.rest a t) hΦ
    have hdiv : S.divInt (S.rest a t) (S.u a' t) = ∑ k, (S.mult k : ℝ) * mInt (S.B k)
        (fun i => (S.rest a t i).pullback Subtype.val continuous_subtype_val)
        (S.u a' t ∘ Subtype.val) := rfl
    show mInt S.A _ (fun x => (-2) * logNormSec S.L S.s x + Real.log (secNorm S.L S.s x ^ 2 + ε)) = _
    rw [hlin, hpl, hbp, hdiv]
    ring

  have hpl : S.plTerm a ha ε t =
      2 * mInt S.A (Fin.cons S.L (S.rest a t)) (S.u a' t) +
        mInt S.A (Fin.cons (LocPot.ofFun fun x => Real.log (secNorm S.L S.s x ^ 2 + ε)) (S.rest a t))
          (S.u a' t) - 2 * S.divInt (S.rest a t) (S.u a' t) := by
    have hcu := ReciprocityTheory.AnForm.M.PLC.continuous_of_smooth S.A hu
    have hL2 : IsPotential S.A (S.L.rsmul 2) := isPotentialRsmul S.A 2 S.L S.L_pot
    have hfP := isPotential_ofFun S.A _ hf
    show mInt S.A (Fin.cons (S.L.rsmul 2 + LocPot.ofFun fun x => Real.log (secNorm S.L S.s x ^ 2 + ε))
      (S.rest a t)) (S.u a' t) - 2 * S.divInt (S.rest a t) (S.u a' t) = _
    rw [mIntAdd S.A _ _ _ hL2 hfP hΦ _ (mIntegrableCont S.A _ (hcons _ hL2) _ hcu)
      (mIntegrableCont S.A _ (hcons _ hfP) _ hcu), mIntRsmul S.A 2 S.L _ S.L_pot hΦ]
  rw [hJ1, hJ0, hOm, mIntAdd S.A _ _ _ hth huP hΦ _ (hGi _ hth) (hGi _ huP), hU, hpl]
  linarith

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
