module

public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.MultivariableReproducingFormula

@[expose] public section

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.EllipticTermsContributionProof
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.EllipticTermsContribution

open UpperTheory.Esk

theorem mk_out {F : Type} [Field F] (q : PG F) : ((q.out : GL (Fin 2) F) : PG F) = q := Quotient.out_eq' q

theorem elliptic_lower_left_ne_zero (h : GL (Fin 2) ℝ) (hh : h.val.trace ^ 2 < 4 * h.val.det) : h 1 0 ≠ 0 := by
  intro e
  rw [Matrix.trace_fin_two, det_eq, e] at hh
  nlinarith [sq_nonneg (h 0 0 - h 1 1)]

def disc (h : GL (Fin 2) ℝ) : ℝ := 4 * h.val.det - h.val.trace ^ 2

def fpC (h : GL (Fin 2) ℝ) : ℂ :=
  (((h 0 0 - h 1 1) / (2 * h 1 0) : ℝ) : ℂ) + Complex.I * ((Real.sqrt (disc h) / (2 * h 1 0) : ℝ) : ℂ)

theorem fpC_im (h : GL (Fin 2) ℝ) (hh : h.val.trace ^ 2 < 4 * h.val.det) : (fpC h).im ≠ 0 := by
  have hr := elliptic_lower_left_ne_zero h hh
  have hd : 0 < disc h := by unfold disc; linarith
  simp only [fpC, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, zero_mul, one_mul, zero_add]
  exact div_ne_zero (Real.sqrt_pos.2 hd).ne' (mul_ne_zero two_ne_zero hr)

def fp (h : GL (Fin 2) ℝ) (hh : h.val.trace ^ 2 < 4 * h.val.det) : P := ⟨fpC h, fpC_im h hh⟩

theorem fp_eq (h : GL (Fin 2) ℝ) (hh : h.val.trace ^ 2 < 4 * h.val.det) :
    ((h 1 0 : ℝ) : ℂ) * fpC h ^ 2 + (((h 1 1 : ℝ) : ℂ) - ((h 0 0 : ℝ) : ℂ)) * fpC h - ((h 0 1 : ℝ) : ℂ) = 0 := by
  have hr := elliptic_lower_left_ne_zero h hh
  have hd : 0 < disc h := by unfold disc; linarith
  have hr' : ((h 1 0 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr
  have hs : ((Real.sqrt (disc h) : ℝ) : ℂ) ^ 2 = ((disc h : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hd.le]
  have hD : ((disc h : ℝ) : ℂ) = 4 * (((h 0 0 : ℝ) : ℂ) * ((h 1 1 : ℝ) : ℂ) - ((h 0 1 : ℝ) : ℂ) * ((h 1 0 : ℝ) : ℂ))
      - (((h 0 0 : ℝ) : ℂ) + ((h 1 1 : ℝ) : ℂ)) ^ 2 := by
    simp only [disc, Matrix.trace_fin_two, det_eq]; push_cast; ring
  have hz : 2 * ((h 1 0 : ℝ) : ℂ) * fpC h = (((h 0 0 : ℝ) : ℂ) - ((h 1 1 : ℝ) : ℂ)) + Complex.I * ((Real.sqrt (disc h) : ℝ) : ℂ) := by
    simp only [fpC]; push_cast; field_simp
  have h4 : (4 * ((h 1 0 : ℝ) : ℂ)) * (((h 1 0 : ℝ) : ℂ) * fpC h ^ 2 + (((h 1 1 : ℝ) : ℂ) - ((h 0 0 : ℝ) : ℂ)) * fpC h - ((h 0 1 : ℝ) : ℂ)) = 0 := by
    rw [show (4 * ((h 1 0 : ℝ) : ℂ)) * (((h 1 0 : ℝ) : ℂ) * fpC h ^ 2 + (((h 1 1 : ℝ) : ℂ) - ((h 0 0 : ℝ) : ℂ)) * fpC h - ((h 0 1 : ℝ) : ℂ))
      = (2 * ((h 1 0 : ℝ) : ℂ) * fpC h) ^ 2 + 2 * (((h 1 1 : ℝ) : ℂ) - ((h 0 0 : ℝ) : ℂ)) * (2 * ((h 1 0 : ℝ) : ℂ) * fpC h)
        - 4 * ((h 1 0 : ℝ) : ℂ) * ((h 0 1 : ℝ) : ℂ) by ring, hz]
    linear_combination ((Real.sqrt (disc h) : ℝ) : ℂ) ^ 2 * Complex.I_sq - hs - hD
  rcases mul_eq_zero.1 h4 with h5 | h5
  · exact absurd h5 (mul_ne_zero (by norm_num : (4 : ℂ) ≠ 0) hr')
  · exact h5

theorem fix_comm (h g : GL (Fin 2) ℝ) (hh : h.val.trace ^ 2 < 4 * h.val.det) (hc : g * h = h * g) :
    g • fp h hh = fp h hh := by
  have hr := elliptic_lower_left_ne_zero h hh
  have hr' : ((h 1 0 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr
  have e00 := congrArg (fun M : GL (Fin 2) ℝ => M 0 0) hc
  have e10 := congrArg (fun M : GL (Fin 2) ℝ => M 1 0) hc
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two] at e00 e10
  have e00' : ((g 0 0 : ℝ) : ℂ) * ((h 0 0 : ℝ) : ℂ) + ((g 0 1 : ℝ) : ℂ) * ((h 1 0 : ℝ) : ℂ)
      = ((h 0 0 : ℝ) : ℂ) * ((g 0 0 : ℝ) : ℂ) + ((h 0 1 : ℝ) : ℂ) * ((g 1 0 : ℝ) : ℂ) := by exact_mod_cast e00
  have e10' : ((g 1 0 : ℝ) : ℂ) * ((h 0 0 : ℝ) : ℂ) + ((g 1 1 : ℝ) : ℂ) * ((h 1 0 : ℝ) : ℂ)
      = ((h 1 0 : ℝ) : ℂ) * ((g 0 0 : ℝ) : ℂ) + ((h 1 1 : ℝ) : ℂ) * ((g 1 0 : ℝ) : ℂ) := by exact_mod_cast e10
  have hQ := fp_eq h hh
  apply Subtype.ext
  rw [coe_smul, div_eq_iff (den_ne g (fp h hh).2)]
  apply mul_left_cancel₀ hr'
  change ((h 1 0 : ℝ) : ℂ) * (((g 0 0 : ℝ) : ℂ) * fpC h + ((g 0 1 : ℝ) : ℂ))
    = ((h 1 0 : ℝ) : ℂ) * (fpC h * (((g 1 0 : ℝ) : ℂ) * fpC h + ((g 1 1 : ℝ) : ℂ)))
  linear_combination e00' - fpC h * e10' - ((g 1 0 : ℝ) : ℂ) * hQ

theorem tr_r {F I Gf : Type} [Field F] [Group Gf] (D : Dat F I Gf) (v : I) (g : GL (Fin 2) F) :
    (D.r v g).val.trace = D.σ v g.val.trace := by
  rw [Matrix.trace_fin_two, Matrix.trace_fin_two, map_add (f := _)]; rfl

theorem det_r {F I Gf : Type} [Field F] [Group Gf] (D : Dat F I Gf) (v : I) (g : GL (Fin 2) F) :
    (D.r v g).val.det = D.σ v g.val.det := by
  rw [Matrix.det_fin_two, Matrix.det_fin_two, map_sub, map_mul, map_mul]; rfl

end UpperTheory.Esk.EllipticTermsContribution

open UpperTheory.Esk.EllipticTermsContribution in
theorem UpperTheory.Esk.elliptic_terms_contribution_proof : UpperTheory.Esk.B1a → UpperTheory.Esk.B1b → UpperTheory.Esk.B1c → UpperTheory.Esk.B4 → UpperTheory.Esk.C1 → UpperTheory.Esk.E0a → UpperTheory.Esk.KernelTermsInvariantBounded → UpperTheory.Esk.E0d → UpperTheory.Esk.Mult → UpperTheory.Esk.Fcen → UpperTheory.Esk.F3 := by
  intro hB1a _ hB1c hB4 hC1 hE0a hE0c _ hMult hFcen F I Gf ι _ _ _ _ D k a hyp γ ω hT hTe
  have : SigmaFinite (volume : Measure P) := hB1a.1
  obtain ⟨_, c2, c3, _, c5, c6⟩ := hE0c F I Gf ι D k a hyp
  have htr : γ.out.val.trace ≠ 0 := by
    obtain ⟨i, hi⟩ := c5 γ ω hTe
    exact (c6 γ ω i hi).1
  have hTv : ∀ v, (D.r v γ.out).val.trace ^ 2 < 4 * (D.r v γ.out).val.det := fun v => by
    rw [tr_r, det_r]; exact hT v
  let z0 : D.Xs := fun v => fp (D.r v γ.out) (hTv v)
  set S := MulAction.stabilizer (PG F) ((γ, ω) : D.Cj × D.Om) with hS
  have memS : ∀ g : PG F, g ∈ S → g * γ * g⁻¹ = γ ∧ g • ω = ω := by
    intro g hg
    rw [hS, MulAction.mem_stabilizer_iff] at hg
    exact ⟨congrArg Prod.fst hg, congrArg Prod.snd hg⟩
  have fixS : ∀ g : PG F, g ∈ S → g • z0 = z0 := by
    intro g hg
    obtain ⟨h1, -⟩ := memS g hg
    have hc : g.out * γ.out = γ.out * g.out := by
      apply hFcen F γ.out g.out htr
      rw [mk_out, mk_out]; exact h1
    rw [← mk_out g, Dat.mk_smulX]
    funext v
    exact fix_comm _ _ (hTv v) (by rw [← map_mul, ← map_mul, hc])
  obtain ⟨c₀, hc₀, hmink⟩ := hyp.ax.mink
  obtain ⟨s, hs, hsc⟩ := hmink z0 (D.rep ω)
  obtain ⟨C, hC⟩ := hMult F I Gf D hyp.ax 1 c₀ one_pos hc₀
  have hfin := (hC (ω, z0) s hs hsc).1
  have hSfin : (S : Set (PG F)).Finite := hfin.subset fun g hg => ⟨(memS g hg).2, fun v => by
      show 1 ≤ kap (z0 v) ((g • z0 : D.Xs) v)
      rw [fixS g hg, hB1c.2.1]⟩
  have hSF : Finite S := hSfin.to_subtype
  refine ⟨hSF, fun β hβ => ?_⟩
  let f : I → P → ℂ := fun v w => q1 (k v) w (D.r v γ.out • w) * j1 (k v) (D.r v γ.out) w
  have hu : ∀ z : D.Xs, D.kk k a γ (ω, z) = D.Te a γ.out (D.rep ω) * ∏ v, f v (z v) := by
    intro z
    show D.Te a γ.out (D.rep ω) * (qq k z (D.act γ.out z) * D.J k γ.out z) =
      D.Te a γ.out (D.rep ω) * ∏ v, (q1 (k v) (z v) (D.r v γ.out • z v) * j1 (k v) (D.r v γ.out) (z v))
    rw [Finset.prod_mul_distrib]; rfl
  have hint : Integrable (fun z : D.Xs => ∏ v, f v (z v)) :=
    Integrable.fintype_prod (f := f) (μ := fun _ => volume) fun v => (hB4 (k v) (hyp.four v) _ (hTv v)).1
  have hval : ∫ z : D.Xs, ∏ v, f v (z v) = D.orb k γ.out := by
    rw [show (∫ z : D.Xs, ∏ v, f v (z v)) = ∫ z : I → P, ∏ v, f v (z v) ∂(Measure.pi fun _ => volume) from rfl,
      integral_fintype_prod_eq_prod]
    unfold Dat.orb
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [(hB4 (k v) (hyp.four v) _ (hTv v)).2, tr_r, det_r]
  haveI : Fintype S := Fintype.ofFinite S
  have hcard : (0 : ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos_iff.2 ⟨1⟩
  let c : ℝ := (Fintype.card S : ℝ)⁻¹
  have hcut : IsCut S (fun _ : D.Xs => c) := ⟨measurable_const, fun _ => inv_nonneg.2 hcard.le, fun _ => by
      have e : ∑ _ : S, c = 1 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ hcard.ne']
      rw [← e]; exact hasSum_fintype _⟩
  have hP : Pres S (volume : Measure D.Xs) := fun g => (hE0a F I Gf D hyp.ax).2.2.1 (g : PG F)
  have hinv : ∀ (g : S) (z : D.Xs), D.kk k a γ (ω, g • z) = D.kk k a γ (ω, z) := by
    intro g z
    obtain ⟨h1, h2⟩ := memS g g.2
    have := c2 g γ (ω, z)
    have e : (g : PG F) • ((ω, z) : D.Y) = (ω, g • z) := Prod.ext h2 rfl
    rw [h1, e] at this
    exact this
  have hmeas : Measurable (fun z : D.Xs => D.kk k a γ (ω, z)) := (c3 γ).comp measurable_prodMk_left
  have hintc : Integrable (fun z : D.Xs => c • D.kk k a γ (ω, z)) := by
    rw [show (fun z : D.Xs => c • D.kk k a γ (ω, z)) = fun z => c • (D.Te a γ.out (D.rep ω) * ∏ v, f v (z v)) from
      funext fun z => by rw [hu]]
    exact (hint.const_mul _).smul c
  obtain ⟨-, heq⟩ := (hC1 (↥S) D.Xs volume hP (fun _ => c) β hcut hβ).2 _ hmeas hinv hintc
  rw [← heq]
  simp_rw [hu]
  rw [integral_smul, integral_const_mul, hval, Nat.card_eq_fintype_card, Complex.real_smul]
  simp only [c, Complex.ofReal_inv, Complex.ofReal_natCast]
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.PfEcut
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.TruncationKernelLemmas

open UpperTheory.Esk

def iN : P := ⟨-Complex.I, by simp⟩

def bs {I : Type} (e : I → Bool) : X I := fun v => if e v then iP else iN

theorem kap_pos (a z : P) (ha : a.1.im = 1 ∨ a.1.im = -1) (h : 0 < a.1.im * z.1.im) : 0 < kap a z := by
  unfold kap
  rw [if_pos h]
  apply div_pos (by linarith)
  apply pow_pos
  apply norm_pos_iff.2
  intro h0
  have h1 := congrArg Complex.im h0
  simp at h1
  rcases ha with ha | ha <;> rw [ha] at h h1 <;> nlinarith

theorem kap_bs_pos {I : Type} (z : X I) (v : I) :
    0 < kap (bs (fun i => decide (0 < (z v).1.im)) v) (z v) := by
  have hz := (z v).2
  unfold bs
  by_cases h : 0 < (z v).1.im
  · simp only [h, decide_true, if_true]
    exact kap_pos _ _ (Or.inl (by simp [iP])) (by simpa [iP] using h)
  · simp only [h, decide_false, Bool.false_eq_true, if_false]
    have h' : (z v).1.im < 0 := lt_of_le_of_ne (not_lt.1 h) hz
    exact kap_pos _ _ (Or.inr (by simp [iN])) (by simp [iN]; linarith)

theorem Kap_nonneg {I : Type} [Fintype I] (hk0 : ∀ z w : P, 0 ≤ kap z w) (k : I → ℕ) (z w : X I) : 0 ≤ Kap k z w :=
  Finset.prod_nonneg fun v _ => Real.rpow_nonneg (hk0 _ _) _


open Classical in
def uX {I : Type} [Fintype I] (z : X I) : ℝ := by
  classical
  exact ∑ e : I → Bool, Kap (fun _ => 4) (bs e) z

theorem uX_nonneg {I : Type} [Fintype I] (hk0 : ∀ z w : P, 0 ≤ kap z w) (z : X I) : 0 ≤ uX z :=
  Finset.sum_nonneg fun e _ => Kap_nonneg hk0 _ _ _

theorem uX_pos {I : Type} [Fintype I] (hk0 : ∀ z w : P, 0 ≤ kap z w) (z : X I) : 0 < uX z := by
  classical
  unfold uX
  refine Finset.sum_pos' (fun e _ => Kap_nonneg hk0 _ _ _) ⟨fun v => decide (0 < (z v).1.im), Finset.mem_univ _, ?_⟩
  exact Finset.prod_pos fun v _ => Real.rpow_pos_of_pos (kap_bs_pos z v) _

theorem uX_cont {I : Type} [Fintype I] (hkc : Continuous fun p : P × P => kap p.1 p.2) :
    Continuous (uX : X I → ℝ) := by
  unfold uX Kap
  refine continuous_finsetSum _ fun _ _ => continuous_finsetProd _ fun v _ => ?_
  exact (hkc.comp (continuous_const.prodMk (continuous_apply v))).rpow_const fun _ => Or.inr (by positivity)

theorem tsum_le_fiber {G Ω : Type} (φ : G → Ω) (w : Ω → ℝ≥0∞) (K : G → ℝ≥0∞) (M : ℝ≥0∞)
    (hK : ∀ ω', ∑' g : {g // φ g = ω'}, K g.1 ≤ M) : ∑' g, w (φ g) * K g ≤ (∑' ω', w ω') * M := by
  rw [← ENNReal.tsum_fiberwise _ φ, ← ENNReal.tsum_mul_right]
  refine ENNReal.tsum_le_tsum fun ω' => ?_
  calc ∑' b : φ ⁻¹' {ω'}, w (φ b) * K b = ∑' b : φ ⁻¹' {ω'}, w ω' * K b :=
        tsum_congr fun b => by rw [show φ b = ω' from b.2]
    _ = w ω' * ∑' b : φ ⁻¹' {ω'}, K b := ENNReal.tsum_mul_left
    _ ≤ w ω' * M := by gcongr; exact hK ω'

end UpperTheory.Esk.TruncationKernelLemmas

open UpperTheory.Esk in
open UpperTheory.Esk in
open Classical in
theorem UpperTheory.Esk.pf_Ecut : UpperTheory.Esk.B1b → UpperTheory.Esk.B1c → UpperTheory.Esk.C2 → UpperTheory.Esk.E0a → UpperTheory.Esk.E0d → UpperTheory.Esk.KapSum → UpperTheory.Esk.Ecut := by
  classical
  intro _ hB hC hE _ hK F I Gf _ _ _ D hax
  obtain ⟨hcount, -, hpres, -⟩ := hE F I Gf D hax
  have : Countable (PG F) := hcount
  have : Countable D.Om := hax.cO
  obtain ⟨hk0', -, -, -, hkc, -⟩ := hB
  have hk0 : ∀ z w : P, 0 ≤ kap z w := fun z w => (hk0' z w).1
  obtain ⟨c₀, hc₀, hmk⟩ := hax.mink
  obtain ⟨C, hCK⟩ := hK F I Gf D hax (fun _ => 4) (fun _ => le_rfl) c₀ hc₀
  have hmX : ∀ g : PG F, Measurable fun z : D.Xs => g • z := fun g => (hpres g).measurable
  have hfib : ∀ y : D.Y, ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ (e : I → Bool) (ω' : D.Om),
      ∑' γ : {γ : PG F // γ • y.1 = ω'}, ENNReal.ofReal (Kap (fun _ => 4) (TruncationKernelLemmas.bs e) (γ.1 • y.2 : D.Xs)) ≤ M := by
    intro y
    obtain ⟨s, hs, hsy⟩ := hmk y.2 (D.rep y.1)
    exact ⟨_, ENNReal.ofReal_ne_top, fun e ω' => hCK y s hs hsy ω' (TruncationKernelLemmas.bs e)⟩
  have hucont : Continuous (TruncationKernelLemmas.uX : X I → ℝ) := TruncationKernelLemmas.uX_cont hkc
  have hsplit : ∀ z : X I, ENNReal.ofReal (TruncationKernelLemmas.uX z) =
      ∑ e : I → Bool, ENNReal.ofReal (Kap (fun _ => 4) (TruncationKernelLemmas.bs e) z) := by
    intro z
    rw [TruncationKernelLemmas.uX, ENNReal.ofReal_sum_of_nonneg (fun e _ => TruncationKernelLemmas.Kap_nonneg hk0 _ _ _)]
  obtain ⟨f, hf⟩ := Countable.exists_injective_nat D.Om
  set w : D.Om → ℝ := fun ω => (1 / 2 : ℝ) ^ f ω with hw
  have hW : ∑' ω, ENNReal.ofReal (w ω) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := ∑' n : ℕ, (1 / 2 : ℝ) ^ n))
      ((ENNReal.tsum_comp_le_tsum_of_injective hf (fun n => ENNReal.ofReal ((1 / 2 : ℝ) ^ n))).trans (le_of_eq ?_))
    exact (ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) summable_geometric_two).symm
  refine ⟨?_, ?_⟩
  · refine (hC (PG F) D.Y).1 ?_ (fun y => w y.1 * TruncationKernelLemmas.uX y.2) ?_ ?_ ?_ ?_
    · intro g
      exact (Measurable.of_discrete.comp measurable_fst).prodMk ((hmX g).comp measurable_snd)
    · have h1 : Measurable fun y : D.Y => w y.1 := (Measurable.of_discrete (f := w)).comp measurable_fst
      have h2 : Measurable fun y : D.Y => TruncationKernelLemmas.uX (y.2 : X I) := hucont.measurable.comp measurable_snd
      exact h1.mul h2
    · exact fun y => mul_nonneg (by positivity) (TruncationKernelLemmas.uX_nonneg hk0 _)
    · exact fun y => ⟨1, by simpa using mul_pos (by positivity : (0 : ℝ) < w y.1) (TruncationKernelLemmas.uX_pos hk0 y.2)⟩
    · intro y
      obtain ⟨M, hM, hMb⟩ := hfib y
      have hle : ∑' g : PG F, ENNReal.ofReal (w (g • y).1 * TruncationKernelLemmas.uX (g • y).2) ≤
          ∑ e : I → Bool, (∑' ω, ENNReal.ofReal (w ω)) * M := by
        calc ∑' g : PG F, ENNReal.ofReal (w (g • y).1 * TruncationKernelLemmas.uX (g • y).2)
            = ∑' g : PG F, ∑ e : I → Bool, ENNReal.ofReal (w (g • y.1)) *
                ENNReal.ofReal (Kap (fun _ => 4) (TruncationKernelLemmas.bs e) (g • y.2 : D.Xs)) := by
              refine tsum_congr fun g => ?_
              exact (ENNReal.ofReal_mul (by positivity)).trans
                ((congrArg (fun t => ENNReal.ofReal (w (g • y.1)) * t) (hsplit _)).trans (by rw [Finset.mul_sum]; rfl))
          _ = ∑ e : I → Bool, ∑' g : PG F, ENNReal.ofReal (w (g • y.1)) *
                ENNReal.ofReal (Kap (fun _ => 4) (TruncationKernelLemmas.bs e) (g • y.2 : D.Xs)) :=
              Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)
          _ ≤ _ := Finset.sum_le_sum fun e _ => TruncationKernelLemmas.tsum_le_fiber (fun g : PG F => g • y.1)
                (fun ω => ENNReal.ofReal (w ω))
                (fun g : PG F => ENNReal.ofReal (Kap (fun _ => 4) (TruncationKernelLemmas.bs e) (g • y.2 : D.Xs))) M (hMb e)
      have hfin : ∑' g : PG F, ENNReal.ofReal (w (g • y).1 * TruncationKernelLemmas.uX (g • y).2) ≠ ⊤ :=
        ne_top_of_le_ne_top (ENNReal.sum_lt_top.2 fun e _ => ENNReal.mul_lt_top hW.lt_top hM.lt_top).ne hle
      refine (ENNReal.summable_toReal hfin).congr fun g => ?_
      exact ENNReal.toReal_ofReal (mul_nonneg (by positivity) (TruncationKernelLemmas.uX_nonneg hk0 _))
  · intro ω S hS
    refine (hC S D.Xs).1 ?_ TruncationKernelLemmas.uX ?_ ?_ ?_ ?_
    · intro g
      exact hmX (g : PG F)
    · exact hucont.measurable
    · exact TruncationKernelLemmas.uX_nonneg hk0
    · exact fun z => ⟨1, by simpa using TruncationKernelLemmas.uX_pos hk0 z⟩
    · intro z
      obtain ⟨M, hM, hMb⟩ := hfib ((ω, z) : D.Y)
      have hinj : Function.Injective (fun g : S => (⟨(g : PG F), hS g.2⟩ : {γ : PG F // γ • ((ω, z) : D.Y).1 = ω})) := by
        intro a b h
        apply Subtype.ext
        exact congrArg (fun x : {γ : PG F // γ • ((ω, z) : D.Y).1 = ω} => x.1) h
      have hle : ∑' g : S, ENNReal.ofReal (TruncationKernelLemmas.uX (g • z : D.Xs)) ≤ ∑ e : I → Bool, M := by
        calc ∑' g : S, ENNReal.ofReal (TruncationKernelLemmas.uX (g • z : D.Xs))
            = ∑' g : S, ∑ e : I → Bool, ENNReal.ofReal (Kap (fun _ => 4) (TruncationKernelLemmas.bs e) (g • z : D.Xs)) :=
              tsum_congr fun g => hsplit _
          _ = ∑ e : I → Bool, ∑' g : S, ENNReal.ofReal (Kap (fun _ => 4) (TruncationKernelLemmas.bs e) (g • z : D.Xs)) :=
              Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)
          _ ≤ _ := Finset.sum_le_sum fun e _ =>
              (ENNReal.tsum_comp_le_tsum_of_injective hinj
                (fun γ : {γ : PG F // γ • ((ω, z) : D.Y).1 = ω} =>
                  ENNReal.ofReal (Kap (fun _ => 4) (TruncationKernelLemmas.bs e) (γ.1 • ((ω, z) : D.Y).2 : D.Xs)))).trans (hMb e ω)
      have hfin : ∑' g : S, ENNReal.ofReal (TruncationKernelLemmas.uX (g • z : D.Xs)) ≠ ⊤ :=
        ne_top_of_le_ne_top (ENNReal.sum_lt_top.2 fun e _ => hM.lt_top).ne hle
      refine (ENNReal.summable_toReal hfin).congr fun g => ?_
      exact ENNReal.toReal_ofReal (TruncationKernelLemmas.uX_nonneg hk0 _)
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.MultivariableReproducingFormulaProof
noncomputable section

open MeasureTheory
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.MultivariableReproducingLemmas

theorem kap_nonneg (z w : P) : 0 ≤ kap z w := by
  unfold kap
  split_ifs with h
  · exact div_nonneg (by linarith) (sq_nonneg _)
  · exact le_rfl

theorem nrm_pos {I : Type} [Fintype I] (k : I → ℕ) (z : X I) : 0 < nrm k z :=
  Finset.prod_pos fun v _ => Real.rpow_pos_of_pos (abs_pos.2 (z v).2) _

theorem Kap_nonneg {I : Type} [Fintype I] (k : I → ℕ) (z w : X I) : 0 ≤ Kap k z w :=
  Finset.prod_nonneg fun _ _ => Real.rpow_nonneg (kap_nonneg _ _) _

theorem norm_qq {I : Type} [Fintype I] (hb : B1b) (k : I → ℕ) (hk : ∀ v, 1 ≤ k v) (z w : X I) :
    ‖qq k z w‖ * nrm k z = (∏ v, (((k v : ℝ) - 1) / (4 * Real.pi))) * Kap k z w * nrm k w := by
  simp only [qq, nrm, Kap, norm_prod, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun v _ => hb.2.2.2.2.2.1 (k v) (z v) (w v) (hk v)

theorem cont_qq {I : Type} [Fintype I] (hb : B1b) (k : I → ℕ) (z : X I) : Continuous (qq k z) := by
  unfold qq
  exact continuous_finsetProd _ fun v _ =>
    (hb.2.2.2.2.2.2.2.1 (k v)).comp (continuous_const.prodMk (continuous_apply v))

theorem integrable {I : Type} [Fintype I] (hb : B1b) (hK : KapInt) (k : I → ℕ)
    (hk : ∀ v, 4 ≤ k v) (f : X I → ℂ) (hf : Continuous f) (C : ℝ) (hC : ∀ z, ‖f z‖ * nrm k z ≤ C)
    (z : X I) : Integrable (fun w => qq k z w * f w) := by
  obtain ⟨C1, A, h⟩ := hK I k hk
  obtain ⟨hm, hl, -⟩ := h z
  have hKi : Integrable (Kap k z) := by
    refine ⟨hm.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    calc ∫⁻ w, ‖Kap k z w‖ₑ = ∫⁻ w, ENNReal.ofReal (Kap k z w) := by
          congr 1; funext w; exact Real.enorm_eq_ofReal (Kap_nonneg k z w)
      _ ≤ C1 := hl
      _ < ⊤ := ENNReal.coe_lt_top
  have hc : 0 ≤ ∏ v, (((k v : ℝ) - 1) / (4 * Real.pi)) := Finset.prod_nonneg fun v _ => by
    have h4 : (4 : ℝ) ≤ k v := by exact_mod_cast hk v
    exact div_nonneg (by linarith) (by positivity)
  refine (hKi.const_mul ((∏ v, (((k v : ℝ) - 1) / (4 * Real.pi))) * C / nrm k z)).mono'
    ((cont_qq hb k z).mul hf).aestronglyMeasurable (Filter.Eventually.of_forall fun w => ?_)
  have h1 := norm_qq hb k (fun v => le_trans (by norm_num) (hk v)) z w
  have hn := nrm_pos k z
  rw [norm_mul, div_mul_eq_mul_div, le_div_iff₀ hn]
  calc ‖qq k z w‖ * ‖f w‖ * nrm k z = (‖qq k z w‖ * nrm k z) * ‖f w‖ := by ring
    _ = (∏ v, (((k v : ℝ) - 1) / (4 * Real.pi))) * Kap k z w * (‖f w‖ * nrm k w) := by rw [h1]; ring
    _ ≤ (∏ v, (((k v : ℝ) - 1) / (4 * Real.pi))) * Kap k z w * C :=
        mul_le_mul_of_nonneg_left (hC w) (mul_nonneg hc (Kap_nonneg k z w))
    _ = (∏ v, (((k v : ℝ) - 1) / (4 * Real.pi))) * C * Kap k z w := by ring

theorem symm_eq (n : ℕ) (p : P × (Fin n → P)) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => P) 0).symm p = Fin.cons p.1 p.2 := by
  funext j
  induction j using Fin.cases <;> simp [MeasurableEquiv.piFinSuccAbove_symm_apply]

theorem qq_cons {n : ℕ} (k : Fin (n + 1) → ℕ) (z : X (Fin (n + 1))) (t : P) (w : Fin n → P) :
    qq k z (Fin.cons t w) = q1 (k 0) (z 0) t * qq (fun j => k j.succ) (fun j => z j.succ) w := by
  simp only [qq, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]

theorem nrm_cons {n : ℕ} (k : Fin (n + 1) → ℕ) (t : P) (w : Fin n → P) :
    nrm k (Fin.cons t w : X (Fin (n + 1))) = |t.1.im| ^ ((k 0 : ℝ) / 2) * nrm (fun j => k j.succ) w := by
  simp only [nrm, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]

theorem fin_case (ha : B1a) (hb : B1b) (h3 : B3) (hK : KapInt) : ∀ (n : ℕ) (k : Fin n → ℕ), (∀ v, 4 ≤ k v) →
    ∀ f : X (Fin n) → ℂ, SepHol f → ∀ C, (∀ z, ‖f z‖ * nrm k z ≤ C) → ∀ z, ∫ w, qq k z w * f w = f z := by
  have : SigmaFinite (volume : Measure P) := ha.1
  intro n
  induction n with
  | zero =>
    intro k hk f hf C hC z
    have hF : (fun w => qq k z w * f w) = fun _ => f z := funext fun w => by
      rw [Subsingleton.elim w z]; simp [qq]
    rw [hF, show (volume : Measure (X (Fin 0))) = Measure.dirac z from Measure.pi_of_empty _ z,
      integral_const]
    simp
  | succ n ih =>
    intro k hk f hf C hC z
    have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => (volume : Measure P)) 0
    have hI := integrable hb hK k hk f hf.1 C hC z
    have hG : Integrable (fun p : P × (Fin n → P) =>
        q1 (k 0) (z 0) p.1 * qq (fun j => k j.succ) (fun j => z j.succ) p.2 * f (Fin.cons p.1 p.2))
        ((volume : Measure P).prod (Measure.pi fun _ : Fin n => (volume : Measure P))) := by
      have := (hmp.symm.integrable_comp_emb
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => P) 0).symm.measurableEmbedding).2 hI
      refine this.congr (Filter.Eventually.of_forall fun p => ?_)
      simp only [Function.comp_apply, symm_eq, qq_cons]
    have hin : ∀ w : Fin n → P, ∫ t, q1 (k 0) (z 0) t * qq (fun j => k j.succ) (fun j => z j.succ) w *
        f (Fin.cons t w) = qq (fun j => k j.succ) (fun j => z j.succ) w * f (Fin.cons (z 0) w) := by
      intro w
      have hol : Hol1 fun t => f (Fin.cons t w) := by
        have h := hf.2 (Fin.cons (z 0) w) 0
        convert h using 3 with t
        funext j
        induction j using Fin.cases <;> simp
      have hbd : ∃ C', ∀ t : P, ‖f (Fin.cons t w)‖ * |t.1.im| ^ ((k 0 : ℝ) / 2) ≤ C' := by
        refine ⟨C / nrm (fun j => k j.succ) w, fun t => ?_⟩
        rw [le_div_iff₀ (nrm_pos _ _), mul_assoc, ← nrm_cons]
        exact hC _
      have h := (h3 (k 0) (hk 0) (fun t => f (Fin.cons t w)) hol hbd (z 0)).2
      calc ∫ t, q1 (k 0) (z 0) t * qq (fun j => k j.succ) (fun j => z j.succ) w * f (Fin.cons t w)
          = ∫ t, qq (fun j => k j.succ) (fun j => z j.succ) w * (q1 (k 0) (z 0) t * f (Fin.cons t w)) := by
            congr 1; funext t; ring
        _ = _ := by rw [integral_const_mul, h]
    have hsep : SepHol fun w : X (Fin n) => f (Fin.cons (z 0) w) := by
      refine ⟨hf.1.comp (continuous_pi fun j => ?_), fun w v => ?_⟩
      · induction j using Fin.cases
        · simpa using continuous_const
        · simpa using continuous_apply _
      · have h := hf.2 (Fin.cons (z 0) w) v.succ
        convert h using 3 with t
        funext j
        induction j using Fin.cases with
        | zero => simp [(Fin.succ_ne_zero v).symm]
        | succ j =>
          simp only [Fin.cons_succ, Function.update_apply, Fin.succ_inj]
          split_ifs <;> simp_all
    have hbd : ∀ w : X (Fin n), ‖f (Fin.cons (z 0) w)‖ * nrm (fun j => k j.succ) w ≤
        C / |(z 0).1.im| ^ ((k 0 : ℝ) / 2) := by
      intro w
      rw [le_div_iff₀ (Real.rpow_pos_of_pos (abs_pos.2 (z 0).2) _), mul_assoc, mul_comm (nrm _ _), ← nrm_cons]
      exact hC _
    calc ∫ w, qq k z w * f w
        = ∫ p, (fun w => qq k z w * f w)
            ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => P) 0).symm p)
            ∂((volume : Measure P).prod (Measure.pi fun _ : Fin n => (volume : Measure P))) :=
          (hmp.symm.integral_comp' _).symm
      _ = ∫ p : P × (Fin n → P), q1 (k 0) (z 0) p.1 * qq (fun j => k j.succ) (fun j => z j.succ) p.2 *
            f (Fin.cons p.1 p.2) ∂((volume : Measure P).prod (Measure.pi fun _ : Fin n => (volume : Measure P))) := by
          congr 1; funext p; simp only [symm_eq, qq_cons]
      _ = ∫ w : Fin n → P, (∫ t : P, q1 (k 0) (z 0) t * qq (fun j => k j.succ) (fun j => z j.succ) w *
            f (Fin.cons t w)) ∂(Measure.pi fun _ : Fin n => (volume : Measure P)) := integral_prod_symm _ hG
      _ = ∫ w : X (Fin n), qq (fun j => k j.succ) (fun j => z j.succ) w * f (Fin.cons (z 0) w) := by
          congr 1; funext w; exact hin w
      _ = f (Fin.cons (z 0) (fun j => z j.succ)) := ih _ (fun v => hk _) _ hsep _ hbd _
      _ = f z := congrArg f (Fin.cons_self_tail z)

theorem main (ha : B1a) (hb : B1b) (h3 : B3) (hK : KapInt) (I : Type) [Fintype I] (k : I → ℕ)
    (hk : ∀ v, 4 ≤ k v) (f : X I → ℂ) (hf : SepHol f) (C : ℝ) (hC : ∀ z, ‖f z‖ * nrm k z ≤ C) (z : X I) :
    ∫ w, qq k z w * f w = f z := by
  have : SigmaFinite (volume : Measure P) := ha.1
  let σ := Fintype.equivFin I
  let φ := MeasurableEquiv.piCongrLeft (fun _ : Fin (Fintype.card I) => P) σ
  have hφ : ∀ (w : X I) j, φ w j = w (σ.symm j) := by
    intro w j
    have := Equiv.piCongrLeft_apply_apply (fun _ : Fin (Fintype.card I) => P) σ w (σ.symm j)
    rw [Equiv.apply_symm_apply] at this
    rw [MeasurableEquiv.coe_piCongrLeft]
    exact this
  have hmp : MeasurePreserving φ (volume : Measure (X I)) (volume : Measure (X (Fin (Fintype.card I)))) :=
    measurePreserving_piCongrLeft (fun _ : Fin (Fintype.card I) => (volume : Measure P)) σ
  have hsep : SepHol fun w' : X (Fin (Fintype.card I)) => f fun i => w' (σ i) := by
    refine ⟨hf.1.comp (continuous_pi fun i => continuous_apply _), fun w' j => ?_⟩
    have h := hf.2 (fun i => w' (σ i)) (σ.symm j)
    convert h using 3 with t
    funext i
    have heq : σ i = j ↔ i = σ.symm j := by
      constructor
      · intro h; exact σ.injective (by simpa using h)
      · intro h; simpa [h]
    simp only [Function.update_apply]
    rw [heq]
  have hnrm : ∀ w' : X (Fin (Fintype.card I)), nrm (fun j => k (σ.symm j)) w' = nrm k fun i => w' (σ i) := by
    intro w'
    exact Fintype.prod_equiv σ.symm _ _ fun j => by simp
  have hbd : ∀ w' : X (Fin (Fintype.card I)), ‖f fun i => w' (σ i)‖ * nrm (fun j => k (σ.symm j)) w' ≤ C := by
    intro w'; rw [hnrm]; exact hC _
  have hqq : ∀ w : X I, qq (fun j => k (σ.symm j)) (fun j => z (σ.symm j)) (φ w) = qq k z w := by
    intro w
    simp only [qq, hφ]
    exact Fintype.prod_equiv σ.symm _ _ fun _ => rfl
  calc ∫ w, qq k z w * f w
      = ∫ w, (fun w' : X (Fin (Fintype.card I)) => qq (fun j => k (σ.symm j)) (fun j => z (σ.symm j)) w' *
          f fun i => w' (σ i)) (φ w) := by
        congr 1; funext w; simp only [hqq, hφ, Equiv.symm_apply_apply]
    _ = ∫ w', qq (fun j => k (σ.symm j)) (fun j => z (σ.symm j)) w' * f fun i => w' (σ i) :=
        hmp.integral_comp' (fun w' : X (Fin (Fintype.card I)) =>
          qq (fun j => k (σ.symm j)) (fun j => z (σ.symm j)) w' * f fun i => w' (σ i))
    _ = f fun i => z (σ.symm (σ i)) := fin_case ha hb h3 hK _ _ (fun v => hk _) _ hsep C hbd _
    _ = f z := by simp only [Equiv.symm_apply_apply]

end UpperTheory.Esk.MultivariableReproducingLemmas

open UpperTheory.Esk.MultivariableReproducingLemmas in
theorem UpperTheory.Esk.multivariable_reproducing_formula_proof : UpperTheory.Esk.B1a → UpperTheory.Esk.B1b → UpperTheory.Esk.B3 → UpperTheory.Esk.KapInt → UpperTheory.Esk.MultivariableReproducingFormula := by
  intro ha hb h3 hK I _ k hk f hf hC z
  obtain ⟨C, hC⟩ := hC
  exact ⟨integrable hb hK k hk f hf.1 C hC z, main ha hb h3 hK I k hk f hf C hC z⟩
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.KernelInverseSymmetry
noncomputable section

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.KernelInverseSymmetry

open UpperTheory.Esk

variable {F I Gf : Type} [Field F] [Group Gf] [Fintype I] (D : Dat F I Gf)

def cK (k : I → ℕ) : ℝ := ∏ v, ((k v : ℝ) - 1) / (4 * Real.pi)

def T (k : I → ℕ) (p : X I × Gf) (γ : PG F) (y : D.Y) : ℂ :=
  D.ee ((D.rep y.1)⁻¹ * (D.j γ.out)⁻¹ * p.2) * (qq k p.1 (D.act γ.out y.2) * D.J k γ.out y.2)

theorem cK_nonneg (k : I → ℕ) (hk : ∀ v, 4 ≤ k v) : 0 ≤ cK k :=
  Finset.prod_nonneg fun v _ => div_nonneg (by
    have h : (4 : ℝ) ≤ k v := by exact_mod_cast hk v
    linarith) (by positivity)

theorem nrm_pos (k : I → ℕ) (z : X I) : 0 < nrm k z :=
  Finset.prod_pos fun v _ => Real.rpow_pos_of_pos (abs_pos.2 (z v).2) _

theorem act_out (γ : PG F) (z : D.Xs) : D.act γ.out z = γ • z := by
  rw [← D.mk_smulX]
  congr 1
  exact Quotient.out_eq γ

theorem norm_qj (hB : B1b) (k : ℕ) (hk : 1 ≤ k) (g : GL (Fin 2) ℝ) (z w : P) :
    ‖q1 k z (g • w)‖ * ‖j1 k g w‖ * |z.1.im| ^ ((k : ℝ) / 2) =
      ((k : ℝ) - 1) / (4 * Real.pi) * kap z (g • w) ^ ((k : ℝ) / 2) * |w.1.im| ^ ((k : ℝ) / 2) := by
  obtain ⟨-, -, -, -, hj, hq, -⟩ := hB
  have e1 := hq k z (g • w) hk
  have e2 := hj k g w
  calc _ = (‖q1 k z (g • w)‖ * |z.1.im| ^ ((k : ℝ) / 2)) * ‖j1 k g w‖ := by ring
    _ = _ := by rw [e1, ← e2]; ring

theorem norm_term (hB : B1b) (k : I → ℕ) (hk : ∀ v, 1 ≤ k v) (g : GL (Fin 2) F) (z w : X I) :
    ‖qq k z (D.act g w) * D.J k g w‖ * nrm k z = cK k * Kap k z (D.act g w) * nrm k w := by
  simp only [qq, Dat.J, Kap, nrm, cK, norm_mul, norm_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  exact norm_qj hB (k v) (hk v) (D.r v g) (z v) (w v)

theorem Kap_smul (hB : B1b) (k : I → ℕ) (δ : PG F) (z w : D.Xs) :
    Kap k (δ • z : D.Xs) (δ • w : D.Xs) = Kap k z w := by
  obtain ⟨-, -, -, hkap, -⟩ := hB
  rw [← act_out, ← act_out]
  unfold Kap
  refine Finset.prod_congr rfl fun v _ => ?_
  show kap (D.r v δ.out • z v) (D.r v δ.out • w v) ^ _ = _
  rw [hkap]

theorem Kap_symm (hBc : B1c) (k : I → ℕ) (z w : X I) : Kap k z w = Kap k w z := by
  obtain ⟨hsym, -⟩ := hBc
  unfold Kap
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [(hsym _ _).2.2]

theorem Kap_swap (hB : B1b) (hBc : B1c) (k : I → ℕ) (γ : PG F) (z w : D.Xs) :
    Kap k z (γ • w : D.Xs) = Kap k w (γ⁻¹ • z : D.Xs) := by
  rw [← Kap_smul D hB k γ⁻¹ z (γ • w), inv_smul_smul]
  exact Kap_symm hBc k _ _

theorem ee_mem (x : Gf) (h : D.ee x ≠ 0) : x ∈ D.H := by
  unfold Dat.ee at h
  split_ifs at h with hx
  · exact hx
  · exact absurd rfl h

theorem norm_ee (hAx : D.Ax) (x : Gf) : ‖D.ee x‖ ≤ 1 := by
  unfold Dat.ee
  split_ifs with hx
  · rw [hAx.χn]
  · simp

theorem supp (γ : PG F) (ω : D.Om) (x : Gf) (h : D.ee ((D.rep ω)⁻¹ * (D.j γ.out)⁻¹ * x) ≠ 0) :
    γ • ω = (show D.Om from (x : Gf ⧸ D.H)) := by
  have hm := ee_mem D _ h
  rw [mul_assoc] at hm
  have e : ((D.rep ω : Gf) : Gf ⧸ D.H) = (((D.j γ.out)⁻¹ * x : Gf) : Gf ⧸ D.H) := QuotientGroup.eq.2 hm
  have hω : ((D.rep ω : Gf) : Gf ⧸ D.H) = ω := Quotient.out_eq ω
  have hγ : ((γ.out : GL (Fin 2) F) : PG F) = γ := Quotient.out_eq γ
  have key : ((γ.out : GL (Fin 2) F) : PG F) • (show D.Om from (((D.j γ.out)⁻¹ * x : Gf) : Gf ⧸ D.H)) =
      (show D.Om from (x : Gf ⧸ D.H)) := by
    rw [D.mk_smulO, mul_inv_cancel_left]
  rw [← hω, e]
  rw [hγ] at key
  exact key

def xH (_D : Dat F I Gf) (p : X I × Gf) : _D.Om := (p.2 : Gf ⧸ _D.H)

def zX (_D : Dat F I Gf) (p : X I × Gf) : _D.Xs := p.1

def invEquiv (ω x : D.Om) : {γ : PG F // γ • ω = x} ≃ {δ : PG F // δ • x = ω} where
  toFun γ := ⟨γ.1⁻¹, by rw [inv_smul_eq_iff, γ.2]⟩
  invFun δ := ⟨δ.1⁻¹, by rw [inv_smul_eq_iff, δ.2]⟩
  left_inv γ := Subtype.ext (inv_inv _)
  right_inv δ := Subtype.ext (inv_inv _)

theorem T_le (hB : B1b) (hBc : B1c) (hAx : D.Ax) (k : I → ℕ) (hk : ∀ v, 4 ≤ k v) (p : X I × Gf) (γ : PG F) (y : D.Y) :
    ‖T D k p γ y‖ₑ ≤ {γ : PG F | γ • y.1 = (xH D p)}.indicator
      (fun γ => ENNReal.ofReal (cK k / nrm k p.1 * nrm k y.2) *
        ENNReal.ofReal (Kap k y.2 (γ⁻¹ • (zX D p) : D.Xs))) γ := by
  by_cases hγ : γ • y.1 = (xH D p)
  · rw [Set.indicator_of_mem (show γ ∈ {γ : PG F | γ • y.1 = (xH D p)} from hγ)]
    rw [← ENNReal.ofReal_mul (mul_nonneg (div_nonneg (cK_nonneg k hk) (nrm_pos k p.1).le) (nrm_pos k y.2).le),
      ← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    have hn := norm_term D hB k (fun v => le_trans (by norm_num) (hk v)) γ.out p.1 y.2
    have hK : Kap k p.1 (D.act γ.out y.2) = Kap k y.2 (γ⁻¹ • (zX D p) : D.Xs) := by
      rw [act_out]
      exact Kap_swap D hB hBc k γ p.1 y.2
    rw [hK] at hn
    have hN := eq_div_of_mul_eq (nrm_pos k p.1).ne' hn
    have he := norm_ee D hAx ((D.rep y.1)⁻¹ * (D.j γ.out)⁻¹ * p.2)
    unfold T
    rw [norm_mul]
    calc _ ≤ 1 * ‖qq k p.1 (D.act γ.out y.2) * D.J k γ.out y.2‖ := mul_le_mul_of_nonneg_right he (norm_nonneg _)
      _ = _ := by rw [hN]; ring
  · rw [Set.indicator_of_notMem (show γ ∉ {γ : PG F | γ • y.1 = (xH D p)} from hγ)]
    have h0 : D.ee ((D.rep y.1)⁻¹ * (D.j γ.out)⁻¹ * p.2) = 0 := by
      by_contra hne
      exact hγ (supp D γ y.1 p.2 hne)
    simp [T, h0]

theorem tsum_le (hB : B1b) (hBc : B1c) (hAx : D.Ax) (k : I → ℕ) (hk : ∀ v, 4 ≤ k v) (p : X I × Gf) (Bnd : ℝ)
    (hS : ∀ (ω : D.Om) (w : X I), ∑' δ : {δ : PG F // δ • (xH D p) = ω},
      ENNReal.ofReal (Kap k w (δ.1 • (zX D p) : D.Xs)) ≤ ENNReal.ofReal Bnd) (y : D.Y) :
    ∑' γ, ‖T D k p γ y‖ₑ ≤ ENNReal.ofReal (cK k / nrm k p.1 * nrm k y.2) * ENNReal.ofReal Bnd := by
  have h1 := ENNReal.tsum_le_tsum fun γ => T_le D hB hBc hAx k hk p γ y
  rw [← tsum_subtype] at h1
  beta_reduce at h1
  rw [ENNReal.tsum_mul_left] at h1
  refine h1.trans (mul_le_mul' le_rfl (Eq.trans_le ?_ (hS y.1 y.2)))
  exact Equiv.tsum_eq (invEquiv D y.1 (xH D p))
    (fun δ => ENNReal.ofReal (Kap k y.2 (δ.1 • (zX D p) : D.Xs)))

theorem main (hB1a : B1a) (hB : B1b) (hBc : B1c) (hE0a : E0a) (hKS : KapSum) (hAx : D.Ax)
    (k : I → ℕ) (hk : ∀ v, 4 ≤ k v) (p : X I × Gf) :
    (∀ y : D.Y, Summable fun γ : PG F => ‖D.ee ((D.rep y.1)⁻¹ * (D.j γ.out)⁻¹ * p.2) *
      (qq k p.1 (D.act γ.out y.2) * D.J k γ.out y.2)‖) ∧
    Measurable (fun y => D.Kern k y p) ∧ ∃ C, ∀ y, ‖D.Kern k y p‖ ≤ C * nrm k y.2 := by
  obtain ⟨hcount, -, -, -, -, -, hborel, -⟩ := hE0a F I Gf D hAx
  obtain ⟨c₀, hc₀, hmink⟩ := hAx.mink
  obtain ⟨C, hCb⟩ := hKS F I Gf D hAx k hk c₀ hc₀
  obtain ⟨s, hs, hsle⟩ := hmink p.1 (D.rep (xH D p))
  obtain ⟨Bnd, hBnd, hS⟩ : ∃ Bnd : ℝ, 0 ≤ Bnd ∧ ∀ (ω : D.Om) (w : X I),
      ∑' δ : {δ : PG F // δ • (xH D p) = ω},
        ENNReal.ofReal (Kap k w (δ.1 • (zX D p) : D.Xs)) ≤ ENNReal.ofReal Bnd :=
    ⟨max (C * (1 + D.HtY s ((xH D p), p.1))) 0, le_max_right _ _, fun ω w =>
      (hCb ((xH D p), p.1) s hs hsle ω w).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))⟩
  have hT := fun y => tsum_le D hB hBc hAx k hk p Bnd hS y
  have hfin : ∀ y : D.Y, ∑' γ, ‖T D k p γ y‖ₑ ≠ ⊤ := fun y =>
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) (hT y)
  have hsumm : ∀ y : D.Y, Summable fun γ => ‖T D k p γ y‖ := fun y => by
    simpa only [toReal_enorm] using ENNReal.summable_toReal (hfin y)
  have hc0 : 0 ≤ cK k / nrm k p.1 := div_nonneg (cK_nonneg k hk) (nrm_pos k p.1).le
  have hbound : ∀ y : D.Y, ∑' γ, ‖T D k p γ y‖ ≤ cK k / nrm k p.1 * Bnd * nrm k y.2 := fun y => by
    have h1 : ∑' γ, ‖T D k p γ y‖ = (∑' γ, ‖T D k p γ y‖ₑ).toReal := by
      rw [ENNReal.tsum_toReal_eq (fun γ => enorm_ne_top)]
      simp only [toReal_enorm]
    rw [h1]
    refine ENNReal.toReal_le_of_le_ofReal (mul_nonneg (mul_nonneg hc0 hBnd) (nrm_pos k y.2).le) ?_
    calc _ ≤ _ := hT y
      _ = ENNReal.ofReal (cK k / nrm k p.1 * Bnd * nrm k y.2) := by
        rw [← ENNReal.ofReal_mul (mul_nonneg hc0 (nrm_pos k y.2).le)]
        congr 1
        ring
  refine ⟨hsumm, ?_, ⟨cK k / nrm k p.1 * Bnd, fun y => (norm_tsum_le_tsum_norm (hsumm y)).trans (hbound y)⟩⟩
  haveI := hcount
  haveI := hborel
  obtain ⟨-, -, -, -, -, -, hjc, hqc, -⟩ := hB
  have hgc : ∀ g : GL (Fin 2) ℝ, Continuous fun z : P => g • z := fun g => (hB1a.2.2 g).1
  have hTm : ∀ γ : PG F, Measurable (T D k p γ) := fun γ => by
    have hG : Continuous fun w : D.Xs => qq k p.1 (D.act γ.out w) * D.J k γ.out w := by
      refine Continuous.mul ?_ ?_
      · refine continuous_finsetProd _ fun v _ => ?_
        exact (hqc (k v)).comp (continuous_const.prodMk ((hgc (D.r v γ.out)).comp (continuous_apply v)))
      · exact continuous_finsetProd _ fun v _ => (hjc (k v) (D.r v γ.out)).comp (continuous_apply v)
    exact ((Measurable.of_discrete (f := fun ω : D.Om => D.ee ((D.rep ω)⁻¹ * (D.j γ.out)⁻¹ * p.2))).comp
      measurable_fst).mul (hG.measurable.comp measurable_snd)
  have hlim : Tendsto (fun (s : Finset (PG F)) (y : D.Y) => ∑ γ ∈ s, T D k p γ y) atTop
      (𝓝 fun y => ∑' γ, T D k p γ y) :=
    tendsto_pi_nhds.2 fun y => ((hsumm y).of_norm).hasSum
  exact measurable_of_tendsto_metrizable' atTop (fun s => Finset.measurable_sum s fun γ _ => hTm γ) hlim

end UpperTheory.Esk.KernelInverseSymmetry

theorem UpperTheory.Esk.kernel_inverse_symmetry : UpperTheory.Esk.B1a → UpperTheory.Esk.B1b → UpperTheory.Esk.B1c → UpperTheory.Esk.E0a → UpperTheory.Esk.E0d → UpperTheory.Esk.KapSum → UpperTheory.Esk.faceMap_zero_comp_eq_one := by
  intro hB1a hB1b hB1c hE0a _ hKS F I Gf _ _ _ D hAx k hk _ p
  exact UpperTheory.Esk.KernelInverseSymmetry.main D hB1a hB1b hB1c hE0a hKS hAx k hk p
end
end
