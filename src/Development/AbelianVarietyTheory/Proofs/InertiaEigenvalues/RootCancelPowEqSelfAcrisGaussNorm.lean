module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusConstantsPiAdicFiltrationModEll
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PHomogeneousDifferenceLinear
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisValuationAtRadiusConcaveContSlope
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisValuationRadiusLaws

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerPowEqOfFrobeniusRatio
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerPowEqOfFrobeniusRatio
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

namespace GlobalTheory.PMon.Gauss

theorem tc_injective (l : ℕ) [Fact l.Prime] : Function.Injective (tc l) := by
  intro a b hab
  obtain ⟨j, hj⟩ := GlobalTheory.MemLoc.exists_isCrisP l
  have hinj := GlobalTheory.MemLoc.crisP_injective l j hj
  have key : ∀ y : Formalism.Per.Fl l, j (tc l y) =
      algebraMap (Formalism.Per.AinfP l) (Formalism.Per.BdRp l)
        (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.AinfP l) (Formalism.Per.tm y)) := by
    intro y
    have := hj.on0 (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris0 l) (Formalism.Per.tm y))
    rw [Subalgebra.coe_algebraMap, ← GlobalTheory.RingIface.tower] at this
    exact this
  have h1 := congrArg j hab
  rw [key, key] at h1
  have h2 := (GlobalTheory.MemLoc.ainf_isDomain_and_injective l).2.2
    (GlobalTheory.MemLoc.algebraMap_AinfP_BdRp_injective l h1)
  have h3 := congrArg (fun w : Formalism.Per.Ainf l => w.coeff 0) h2
  simpa using h3

theorem teich_eq_of_phi_ratio : ∀ (l : ℕ) [Fact l.Prime] (w' : Formalism.Per.Acris l) (ζ : Formalism.Per.Fl l), w' ≠ 0 →
    φc l (tc l ζ * w') * w' = tc l ζ * w' * φc l w' → ζ ^ l = ζ := by
  intro l _ w' ζ hw h
  have hφ : φc l w' ≠ 0 := ((GlobalTheory.T.acrisValuation_radius_laws l 1 one_pos le_rfl).2.1 w' hw).1
  have hprod : w' * φc l w' ≠ 0 := by
    intro h0
    rcases GlobalTheory.T.acris_eq_zero_or_eq_zero_of_mul_eq_zero l _ _ h0 with h0 | h0
    · exact hw h0
    · exact hφ h0
  rw [map_mul, frob_teich] at h
  have h' : (tc l (ζ ^ l) - tc l ζ) * (w' * φc l w') = 0 := by
    linear_combination h
  rcases GlobalTheory.T.acris_eq_zero_or_eq_zero_of_mul_eq_zero l _ _ h' with h0 | h0
  · exact tc_injective l (sub_eq_zero.1 h0)
  · exact absurd h0 hprod

end GlobalTheory.PMon.Gauss
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerPowEqOfFrobeniusRatioStatement
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.teichmuller_pow_eq_of_frobenius_ratio : ∀ (l : ℕ) [Fact l.Prime] (w' : Formalism.Per.Acris l) (ζ : Formalism.Per.Fl l), w' ≠ 0 → φc l (tc l ζ * w') * w' = tc l ζ * w' * φc l w' → ζ ^ l = ζ := by
  first | exact @GlobalTheory.PMon.Gauss.teich_eq_of_phi_ratio | exact GlobalTheory.PMon.Gauss.teich_eq_of_phi_ratio | (intros; apply GlobalTheory.PMon.Gauss.teich_eq_of_phi_ratio <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussNormAcrisTeichmullerTiltSubEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussNormAcrisTeichmullerTiltSubEqOne
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PMon.Gauss

lemma gA_term_le_one (l : ℕ) [Fact l.Prime] (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (a : Formalism.Per.Ainf l) (n : ℕ) :
    ‖(((a.coeff n).untilt : Formalism.Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) * ρ ^ n ≤ 1 := by
  have hx0 : 0 ≤ ‖(((a.coeff n).untilt : Formalism.Per.OC l) : ℂ_[l])‖ := norm_nonneg _
  have hx1 : ‖(((a.coeff n).untilt : Formalism.Per.OC l) : ℂ_[l])‖ ≤ 1 := (GlobalTheory.RingBasics.mem_OC _).1 ((a.coeff n).untilt).2
  have he : 0 ≤ (1 : ℝ) / (l : ℝ) ^ n := by positivity
  have h2 : ‖(((a.coeff n).untilt : Formalism.Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) ≤ 1 :=
    Real.rpow_le_one hx0 hx1 he
  have h3 : ρ ^ n ≤ 1 := pow_le_one₀ h0 h1
  calc _ ≤ 1 * 1 := mul_le_mul h2 h3 (pow_nonneg h0 n) zero_le_one
    _ = 1 := one_mul 1

theorem gC_teich_sub_eq_one : ∀ (l : ℕ) [Fact l.Prime] (ζ ζ' : Formalism.Per.Fl l),
    ‖(((ζ - ζ').untilt : Formalism.Per.OC l) : ℂ_[l])‖ = 1 →
      ∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ (tc l ζ - tc l ζ') = 1 := by
  intro l _ ζ ζ' hζ ρ hρ hρ1
  have hex : ∃ N, IsGauss l ρ N := GlobalTheory.GaussExt.exists_gauss_acris l ρ hρ hρ1
  have hg : IsGauss l ρ (Classical.choose hex) := Classical.choose_spec hex
  have hC : gC l ρ (tc l ζ - tc l ζ') = Classical.choose hex (tc l ζ - tc l ζ') := by
    unfold gC; rw [dite_eq_left hex]
  have hsub : tc l ζ - tc l ζ' =
      algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) (Formalism.Per.tm ζ - Formalism.Per.tm ζ') := by
    unfold tc; rw [map_sub]
  rw [hC, hsub, hg.2.2.2.2]
  have hl : (0 : ℝ) < (l : ℝ)⁻¹ := by
    have : (0 : ℝ) < (l : ℝ) := by exact_mod_cast (Fact.out : l.Prime).pos
    positivity
  have h0 : 0 ≤ ρ := le_of_lt (lt_of_lt_of_le hl hρ)
  have hc0 : (Formalism.Per.tm ζ - Formalism.Per.tm ζ').coeff 0 = ζ - ζ' := by
    have := map_sub (WittVector.constantCoeff (p := l) (R := Formalism.Per.Fl l)) (Formalism.Per.tm ζ) (Formalism.Per.tm ζ')
    simpa [Formalism.Per.tm] using this
  unfold gA
  apply le_antisymm
  · exact ciSup_le (fun n => gA_term_le_one l ρ h0 hρ1.le _ n)
  · have hb : BddAbove (Set.range fun n : ℕ =>
        ‖((((Formalism.Per.tm ζ - Formalism.Per.tm ζ').coeff n).untilt : Formalism.Per.OC l) : ℂ_[l])‖ ^
          ((1 : ℝ) / (l : ℝ) ^ n) * ρ ^ n) :=
      ⟨1, by rintro _ ⟨n, rfl⟩; exact gA_term_le_one l ρ h0 hρ1.le _ n⟩
    refine le_trans ?_ (le_ciSup hb 0)
    simp [hc0, hζ]

end GlobalTheory.PMon.Gauss

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussNormAcrisTeichmullerTiltSubEqOneStatement
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussNormAcris_teichmuller_tilt_sub_eq_one : ∀ (l : ℕ) [Fact l.Prime] (ζ ζ' : Formalism.Per.Fl l), ‖(((ζ - ζ').untilt : Formalism.Per.OC l) : ℂ_[l])‖ = 1 → ∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ (tc l ζ - tc l ζ') = 1 := by
  first | exact @GlobalTheory.PMon.Gauss.gC_teich_sub_eq_one | exact GlobalTheory.PMon.Gauss.gC_teich_sub_eq_one | (intros; apply GlobalTheory.PMon.Gauss.gC_teich_sub_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormUntiltSubEqOneOfPowFixed
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

namespace GlobalTheory.TiltAbs

theorem norm_untilt_sub_eq_one_of_pow_fixed :
    ∀ (l : ℕ) [Fact l.Prime] (o : ℕ) (ζ ζ' : Formalism.Per.Fl l), 0 < o → ζ ^ (l ^ o) = ζ →
      ζ' ^ (l ^ o) = ζ' → ζ ≠ ζ' → ‖(((ζ - ζ').untilt : Formalism.Per.OC l) : ℂ_[l])‖ = 1 := by
  intro l _ o ζ ζ' ho h1 h2 hne
  have hl : 1 < l := (Fact.out : l.Prime).one_lt
  set d : Formalism.Per.Fl l := ζ - ζ' with hd
  have hdpow : d ^ (l ^ o) = d := by
    rw [hd, sub_pow_char_pow, h1, h2]
  have hd0 : d ≠ 0 := sub_ne_zero.2 hne
  set a : ℝ := ‖((d.untilt : Formalism.Per.OC l) : ℂ_[l])‖ with ha
  have ha0 : a ≠ 0 := by
    intro h
    apply hd0
    refine (untilt_ultrametric_definite l d 0).2 ?_
    have : ((d.untilt : Formalism.Per.OC l) : ℂ_[l]) = 0 := norm_eq_zero.1 h
    exact Subtype.ext this
  have hapow : a ^ (l ^ o) = a := by
    have := congrArg (fun x : Formalism.Per.Fl l => ‖((x.untilt : Formalism.Per.OC l) : ℂ_[l])‖) hdpow
    simp only [map_pow, SubmonoidClass.coe_pow, norm_pow] at this
    exact this
  have hlo : 1 ≤ l ^ o := Nat.one_le_pow _ _ (by omega)
  have hlo' : l ^ o - 1 ≠ 0 := by
    have : 1 < l ^ o := Nat.one_lt_pow (by omega) hl
    omega
  have hsub : a ^ (l ^ o - 1) = 1 := by
    have : a ^ (l ^ o - 1) * a = 1 * a := by
      rw [← pow_succ, Nat.sub_add_cancel hlo, hapow, one_mul]
    exact mul_right_cancel₀ ha0 this
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hlo').1 hsub

end GlobalTheory.TiltAbs
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OrbitClassTrivial
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

namespace GlobalTheory

theorem orbit_class_trivial : ∀ (o : ℕ) (p : ℝ) (f : ℕ → ℝ → ℝ), 0 < o → 1 < p → (∀ i, ContinuousOn (f i) (Set.Ioc 0 1)) → (∀ i, ∀ r ∈ Set.Ioc (0 : ℝ) 1, 0 ≤ f i r) → (∀ i j, ∀ r ∈ Set.Ioc (0 : ℝ) 1, 0 < f i r → 0 < f j r → i % o = j % o) → (∀ r ∈ Set.Ioc (0 : ℝ) 1, ∃ i, 0 < f i r) → (∀ i r, 0 < r → r ≤ 1 / p → 0 < f i r → 0 < f (i + 1) (p * r)) → o = 1 := by
  intro o p f _ho hp hc _ hcl hcov hsh
  classical
  let g : ℝ → ℕ := fun r => if h : ∃ i, 0 < f i r then (Classical.choose h) % o else 0
  have hg : ∀ r ∈ Set.Ioc (0 : ℝ) 1, ∀ i, 0 < f i r → g r = i % o := by
    intro r hr i hi
    have h : ∃ i, 0 < f i r := ⟨i, hi⟩
    simp only [g, dif_pos h]
    exact hcl _ _ r hr (Classical.choose_spec h) hi
  have gcont : ContinuousOn g (Set.Ioc (0 : ℝ) 1) := by
    intro r hr
    obtain ⟨i, hi⟩ := hcov r hr
    rw [ContinuousWithinAt, nhds_discrete, Filter.tendsto_pure]
    have h1 : ∀ᶠ x in nhdsWithin r (Set.Ioc (0 : ℝ) 1), 0 < f i x :=
      ((hc i) r hr).eventually (lt_mem_nhds hi)
    filter_upwards [h1, self_mem_nhdsWithin] with x hx hxs
    rw [hg x hxs i hx, hg r hr i hi]
  have hp0 : 0 < p := by linarith
  have hr1 : 1 / p ∈ Set.Ioc (0 : ℝ) 1 :=
    ⟨by positivity, by rw [div_le_one hp0]; exact hp.le⟩
  have h1 : (1 : ℝ) ∈ Set.Ioc (0 : ℝ) 1 := ⟨one_pos, le_rfl⟩
  have hconst : g (1 / p) = g 1 := isPreconnected_Ioc.constant gcont hr1 h1
  obtain ⟨i, hi⟩ := hcov (1 / p) hr1
  have hi1 : 0 < f (i + 1) 1 := by
    have := hsh i (1 / p) (by positivity) le_rfl hi
    rwa [mul_one_div_cancel hp0.ne'] at this
  have hmod : (i + 1) % o = (i + 0) % o := by
    rw [add_zero, ← hg _ hr1 i hi, ← hg _ h1 (i + 1) hi1, hconst]
  have h10 : 1 ≡ 0 [MOD o] := Nat.ModEq.add_left_cancel' i hmod
  exact Nat.dvd_one.mp (Nat.modEq_zero_iff_dvd.mp h10)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RootCancelPowEqSelfAcrisGaussNorm
noncomputable section

open scoped Formalism.Per

namespace GlobalTheory.PMon.Gauss

theorem rootCancel_radius (l : ℕ) [Fact l.Prime] {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    (l : ℝ)⁻¹ ≤ (l : ℝ) ^ (-r) ∧ (l : ℝ) ^ (-r) < 1 := by
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  constructor
  · rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hl.le (by linarith)
  · exact Real.rpow_lt_one_of_one_lt_of_neg hl (by linarith)

theorem vr_iterate_φc (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Acris l) (hx : x ≠ 0) :
    ∀ k : ℕ, ∀ r ∈ Set.Ioc (0 : ℝ) 1,
      (φc l)^[k] x ≠ 0 ∧ vr l r ((φc l)^[k] x) = (l : ℝ) ^ k * vr l (r / (l : ℝ) ^ k) x := by
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  intro k
  induction k with
  | zero => intro r _; simp [hx]
  | succ k ih =>
    intro r hr
    have hrl : r / l ∈ Set.Ioc (0 : ℝ) 1 :=
      ⟨div_pos hr.1 (by linarith), (div_le_one (by linarith)).2 (by linarith [hr.2])⟩
    obtain ⟨h1, h2⟩ := ih (r / l) hrl
    have V := (GlobalTheory.T.acrisValuation_radius_laws l r hr.1 hr.2).2.1 _ h1
    refine ⟨by rw [Function.iterate_succ_apply']; exact V.1, ?_⟩
    rw [Function.iterate_succ_apply', V.2, h2, div_div, pow_succ, mul_comm ((l : ℝ) ^ k) (l : ℝ)]
    ring

theorem vr_prod_range (l : ℕ) [Fact l.Prime] (x : ℕ → Formalism.Per.Acris l) (hx : ∀ i, x i ≠ 0)
    (h10 : (1 : Formalism.Per.Acris l) ≠ 0) :
    ∀ n : ℕ, (∏ i ∈ Finset.range n, x i) ≠ 0 ∧
      ∀ r ∈ Set.Ioc (0 : ℝ) 1, vr l r (∏ i ∈ Finset.range n, x i) = ∑ i ∈ Finset.range n, vr l r (x i) := by
  intro n
  induction n with
  | zero =>
    refine ⟨by simpa using h10, fun r hr => ?_⟩
    have hρ := rootCancel_radius l hr.1 hr.2
    simp [vr, (gC_basic_values l _ hρ.1 hρ.2).1]
  | succ n ih =>
    have hne : (∏ i ∈ Finset.range (n + 1), x i) ≠ 0 := by
      rw [Finset.prod_range_succ]
      intro h0
      rcases GlobalTheory.T.acris_eq_zero_or_eq_zero_of_mul_eq_zero l _ _ h0 with h | h
      · exact ih.1 h
      · exact hx n h
    refine ⟨hne, fun r hr => ?_⟩
    rw [Finset.prod_range_succ, Finset.sum_range_succ, (GlobalTheory.T.acrisValuation_radius_laws l r hr.1 hr.2).1 _ _ ih.1 (hx n),
      ih.2 r hr]

theorem root_cancel_pow_eq_self : ∀ (l : ℕ) [Fact l.Prime] (h s : ℕ), s < h → ∀ (w w' : Formalism.Per.Acris l) (ζ : Formalism.Per.Fl l) (o : ℕ) (ρ₀ : ℝ), (φc l)^[h] w' = (l : Formalism.Per.Acris l) ^ s * w' → w' ≠ 0 → φc l w * w' = w * φc l w' → (∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ w = gC l ρ w') → 0 < o → ζ ^ (l ^ o) = ζ → ζ ≠ 0 → (l : ℝ)⁻¹ ≤ ρ₀ → ρ₀ < 1 → gC l ρ₀ (w - tc l ζ * w') < gC l ρ₀ w' → ζ ^ l = ζ := by
  intro l _ h s hsh w w' ζ o ρ₀ hh hw' hφ hnorm ho hζo hζ0 hρ₀1 hρ₀2 hlt
  classical
  have hlN : 1 < l := (Fact.out : l.Prime).one_lt
  have hl : (1 : ℝ) < l := by exact_mod_cast hlN
  have hl0 : (0 : ℝ) < l := by linarith
  set F : Formalism.Per.Fl l → Formalism.Per.Fl l := fun y => y ^ l with hF
  have hFit : ∀ i, F^[i] ζ = ζ ^ (l ^ i) := by
    intro i
    induction i with
    | zero => simp
    | succ i ih => rw [Function.iterate_succ_apply', ih, hF, pow_succ, pow_mul]
  have hper : Function.IsPeriodicPt F o ζ := by
    show F^[o] ζ = ζ
    rw [hFit]; exact hζo
  set o' := Function.minimalPeriod F ζ with ho'
  have ho'pos : 0 < o' := Function.IsPeriodicPt.minimalPeriod_pos ho hper
  have hz_eq : ∀ i j, F^[i] ζ = F^[j] ζ → i % o' = j % o' := by
    intro i j hij
    rw [← Function.iterate_mod_minimalPeriod_eq (n := i), ← Function.iterate_mod_minimalPeriod_eq (n := j)] at hij
    exact (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod (Nat.mod_lt _ ho'pos) (Nat.mod_lt _ ho'pos)).1 hij
  have hmod1 : ∀ i, (i + 1) % o' = i % o' → o' = 1 := by
    intro i hi
    have hmod : (i + 1) % o' = (i + 0) % o' := by rw [add_zero]; exact hi
    have h10 : 1 ≡ 0 [MOD o'] := Nat.ModEq.add_left_cancel' i hmod
    exact Nat.dvd_one.mp (Nat.modEq_zero_iff_dvd.mp h10)
  suffices hsuff : o' = 1 by
    have := Function.iterate_minimalPeriod (f := F) (x := ζ)
    rw [← ho', hsuff] at this
    simpa [hF] using this

  have hz0 : ∀ i, F^[i] ζ ≠ 0 := fun i => by rw [hFit]; exact pow_ne_zero _ hζ0
  have hzfix : ∀ i, (F^[i] ζ) ^ (l ^ o) = F^[i] ζ := by
    intro i
    rw [hFit, ← pow_mul, mul_comm, pow_mul, hζo]
  have hzsucc : ∀ i, F^[i + 1] ζ = (F^[i] ζ) ^ l := fun i => Function.iterate_succ_apply' _ _ _
  have hzper : F^[o'] ζ = F^[0] ζ := Function.iterate_minimalPeriod

  have hG : ∀ ρ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → IsGauss l ρ (gC l ρ) := fun ρ h0 h1 => isGauss_gC_target l ρ h0 h1
  have htc1 : ∀ ρ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → ∀ i, gC l ρ (tc l (F^[i] ζ)) = 1 := by
    intro ρ h0 h1 i
    rw [(gC_basic_values l ρ h0 h1).2.2.2.1]
    have h00 : (0 : Formalism.Per.Fl l) ^ (l ^ o) = 0 := zero_pow (pow_ne_zero _ (by omega))
    have := GlobalTheory.TiltAbs.norm_untilt_sub_eq_one_of_pow_fixed l o _ 0 ho (hzfix i) h00 (hz0 i)
    simpa using this
  set x : ℕ → Formalism.Per.Acris l := fun i => w - tc l (F^[i] ζ) * w' with hx
  have hfrob : ∀ i, φc l (x i) * w' = x (i + 1) * φc l w' := by
    intro i
    simp only [hx, map_sub, map_mul, frob_teich, hzsucc]
    linear_combination hφ

  by_cases hA : ∃ i, x i = 0
  · obtain ⟨i, hi⟩ := hA
    have hwi : w = tc l (F^[i] ζ) * w' := sub_eq_zero.1 hi
    rw [hwi] at hφ
    have hfix := GlobalTheory.T.teichmuller_pow_eq_of_frobenius_ratio l w' (F^[i] ζ) hw' hφ
    apply hmod1 i
    apply hz_eq
    rw [hzsucc]; exact hfix
  push_neg at hA

  have h10 : (1 : Formalism.Per.Acris l) ≠ 0 := fun h1 => hw' (by rw [← one_mul w', h1, zero_mul])
  have hrad := fun r (hr : r ∈ Set.Ioc (0 : ℝ) 1) => rootCancel_radius l hr.1 hr.2
  have hpos : ∀ y : Formalism.Per.Acris l, y ≠ 0 → ∀ r ∈ Set.Ioc (0 : ℝ) 1, 0 < gC l ((l : ℝ) ^ (-r)) y :=
    fun y hy r hr => GlobalTheory.T.gaussNormAcrisRadius_pos_definite l y hy _ (hrad r hr).1 (hrad r hr).2
  have hmulw : ∀ r ∈ Set.Ioc (0 : ℝ) 1, ∀ i,
      gC l ((l : ℝ) ^ (-r)) (tc l (F^[i] ζ) * w') = gC l ((l : ℝ) ^ (-r)) w' := by
    intro r hr i
    rw [(hG _ (hrad r hr).1 (hrad r hr).2).2.2.2.1, htc1 _ (hrad r hr).1 (hrad r hr).2, one_mul]
  have hxle : ∀ r ∈ Set.Ioc (0 : ℝ) 1, ∀ i, gC l ((l : ℝ) ^ (-r)) (x i) ≤ gC l ((l : ℝ) ^ (-r)) w' := by
    intro r hr i
    have hGr := hG _ (hrad r hr).1 (hrad r hr).2
    have := hGr.2.1 w (-(tc l (F^[i] ζ) * w'))
    rw [← sub_eq_add_neg, hGr.2.2.1, hmulw r hr i, hnorm _ (hrad r hr).1 (hrad r hr).2, max_self] at this
    exact this
  set fv : ℕ → ℝ → ℝ := fun i r => vr l r (x i) - vr l r w' with hfv
  have hfv_pos : ∀ r ∈ Set.Ioc (0 : ℝ) 1, ∀ i,
      0 < fv i r ↔ gC l ((l : ℝ) ^ (-r)) (x i) < gC l ((l : ℝ) ^ (-r)) w' := by
    intro r hr i
    simp only [hfv, vr, sub_pos, neg_lt_neg_iff]
    exact Real.logb_lt_logb_iff hl (hpos _ (hA i) r hr) (hpos _ hw' r hr)
  have hfv_nonneg : ∀ i, ∀ r ∈ Set.Ioc (0 : ℝ) 1, 0 ≤ fv i r := by
    intro i r hr
    simp only [hfv, vr, sub_nonneg, neg_le_neg_iff]
    exact Real.logb_le_logb_of_le hl (hpos _ (hA i) r hr) (hxle r hr i)
  have hfv_cont : ∀ i, ContinuousOn (fv i) (Set.Ioc 0 1) := fun i =>
    ((GlobalTheory.T.acrisValuationAtRadius_concave_cont_slope l _ (hA i)).2.1).sub (GlobalTheory.T.acrisValuationAtRadius_concave_cont_slope l _ hw').2.1
  have hfv_class : ∀ i j, ∀ r ∈ Set.Ioc (0 : ℝ) 1, 0 < fv i r → 0 < fv j r → i % o' = j % o' := by
    intro i j r hr hi hj
    by_cases hzz : F^[i] ζ = F^[j] ζ
    · exact hz_eq _ _ hzz
    exfalso
    have hGr := hG _ (hrad r hr).1 (hrad r hr).2
    have hd : x j - x i = (tc l (F^[i] ζ) - tc l (F^[j] ζ)) * w' := by simp only [hx]; ring
    have hsep := GlobalTheory.TiltAbs.norm_untilt_sub_eq_one_of_pow_fixed l o _ _ ho (hzfix i) (hzfix j) hzz
    have h1 := GlobalTheory.T.gaussNormAcris_teichmuller_tilt_sub_eq_one l _ _ hsep _ (hrad r hr).1 (hrad r hr).2
    have hle := hGr.2.1 (x j) (-(x i))
    rw [← sub_eq_add_neg, hGr.2.2.1, hd, hGr.2.2.2.1, h1, one_mul] at hle
    have := (hfv_pos r hr i).1 hi
    have := (hfv_pos r hr j).1 hj
    have := le_max_iff.1 hle
    rcases this with h | h <;> linarith
  have hfv_shift : ∀ i r, 0 < r → r ≤ 1 / (l : ℝ) → fv (i + 1) ((l : ℝ) * r) = (l : ℝ) * fv i r := by
    intro i r hr0 hr1
    have hlr : (l : ℝ) * r ∈ Set.Ioc (0 : ℝ) 1 :=
      ⟨by positivity, by rw [le_div_iff₀ hl0] at hr1; linarith⟩
    have V := GlobalTheory.T.acrisValuation_radius_laws l _ hlr.1 hlr.2
    have hrr : (l : ℝ) * r / l = r := by field_simp
    have e := congrArg (vr l ((l : ℝ) * r)) (hfrob i)
    rw [V.1 _ _ (V.2.1 _ (hA i)).1 hw', V.1 _ _ (hA (i + 1)) (V.2.1 _ hw').1, (V.2.1 _ (hA i)).2,
      (V.2.1 _ hw').2, hrr] at e
    simp only [hfv]
    linarith

  have hper_x : x o' = x 0 := by simp only [hx, hzper]
  obtain ⟨hWne, hWvr⟩ := vr_prod_range l x hA h10 o'
  set W := ∏ i ∈ Finset.range o', x i with hW
  have hsum : ∀ r ∈ Set.Ioc (0 : ℝ) 1, vr l r W - (o' : ℝ) * vr l r w' = ∑ i ∈ Finset.range o', fv i r := by
    intro r hr
    simp only [hfv, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, hWvr r hr]
  have hB : ∀ r ∈ Set.Ioc (0 : ℝ) 1, (l : ℝ) ^ h * vr l (r / (l : ℝ) ^ h) w' = vr l r w' + s * r := by
    intro r hr
    have e := (vr_iterate_φc l w' hw' h r hr).2
    rw [hh, (GlobalTheory.T.acrisValuation_radius_laws l r hr.1 hr.2).2.2.1 w' s hw'] at e
    linarith
  have hAB : ∀ r ∈ Set.Ioc (0 : ℝ) (1 / l), vr l ((l : ℝ) * r) W - (o' : ℝ) * vr l ((l : ℝ) * r) w' =
      (l : ℝ) * (vr l r W - (o' : ℝ) * vr l r w') := by
    intro r hr
    have hr1 : r ∈ Set.Ioc (0 : ℝ) 1 :=
      ⟨hr.1, hr.2.trans (by rw [div_le_one hl0]; exact hl.le)⟩
    have hlr : (l : ℝ) * r ∈ Set.Ioc (0 : ℝ) 1 :=
      ⟨mul_pos hl0 hr.1, by have := hr.2; rw [le_div_iff₀ hl0] at this; linarith⟩
    rw [hsum _ hlr, hsum _ hr1, Finset.mul_sum]
    have hcyc : ∑ i ∈ Finset.range o', fv i ((l : ℝ) * r) = ∑ i ∈ Finset.range o', fv (i + 1) ((l : ℝ) * r) := by
      have e1 := Finset.sum_range_succ (fun i => fv i ((l : ℝ) * r)) o'
      have e2 := Finset.sum_range_succ' (fun i => fv i ((l : ℝ) * r)) o'
      have e3 : fv o' ((l : ℝ) * r) = fv 0 ((l : ℝ) * r) := by simp only [hfv, hper_x]
      linarith
    rw [hcyc]
    exact Finset.sum_congr rfl (fun i _ => hfv_shift i r hr.1 hr.2)
  obtain ⟨n, hn⟩ := GlobalTheory.T.exists_int_sub_mul_eq_int_mul_of_homogeneous l h s o' hlN hsh ho'pos (fun r => vr l r W) (fun r => vr l r w')
    (GlobalTheory.T.acrisValuationAtRadius_concave_cont_slope l _ hWne).1 (GlobalTheory.T.acrisValuationAtRadius_concave_cont_slope l _ hw').1 (GlobalTheory.T.acrisValuationAtRadius_concave_cont_slope l _ hWne).2.1 (GlobalTheory.T.acrisValuationAtRadius_concave_cont_slope l _ hw').2.1
    (GlobalTheory.T.acrisValuationAtRadius_concave_cont_slope l _ hWne).2.2 (GlobalTheory.T.acrisValuationAtRadius_concave_cont_slope l _ hw').2.2 hB hAB

  set r₀ := -Real.logb l ρ₀ with hr₀
  have hρ₀pos : 0 < ρ₀ := lt_of_lt_of_le (inv_pos.2 hl0) hρ₀1
  have hr₀ρ : (l : ℝ) ^ (-r₀) = ρ₀ := by rw [hr₀, neg_neg, Real.rpow_logb hl0 hl.ne' hρ₀pos]
  have hr₀mem : r₀ ∈ Set.Ioc (0 : ℝ) 1 := by
    constructor
    · rw [hr₀, neg_pos]; exact Real.logb_neg hl hρ₀pos hρ₀2
    · rw [hr₀, neg_le]
      have := Real.logb_le_logb_of_le hl (inv_pos.2 hl0) hρ₀1
      rwa [Real.logb_inv, Real.logb_self_eq_one hl] at this
  have hf0 : 0 < fv 0 r₀ := by
    rw [hfv_pos r₀ hr₀mem 0, hr₀ρ]
    simpa [hx] using hlt
  have hnpos : (0 : ℝ) < n := by
    have hs := hsum r₀ hr₀mem
    rw [hn r₀ hr₀mem] at hs
    have : fv 0 r₀ ≤ ∑ i ∈ Finset.range o', fv i r₀ :=
      Finset.single_le_sum (fun i _ => hfv_nonneg i r₀ hr₀mem) (Finset.mem_range.2 ho'pos)
    nlinarith [hr₀mem.1]
  have hcover : ∀ r ∈ Set.Ioc (0 : ℝ) 1, ∃ i, 0 < fv i r := by
    intro r hr
    by_contra H
    push_neg at H
    have hs := hsum r hr
    rw [hn r hr] at hs
    have : ∑ i ∈ Finset.range o', fv i r ≤ 0 := Finset.sum_nonpos (fun i _ => H i)
    nlinarith [hr.1]
  exact GlobalTheory.orbit_class_trivial o' (l : ℝ) fv ho'pos hl hfv_cont hfv_nonneg hfv_class hcover
    (fun i r hr0 hr1 hi => by rw [hfv_shift i r hr0 hr1]; positivity)

end GlobalTheory.PMon.Gauss

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RootCancelPowEqSelfAcrisGaussNormStatement
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rootCancel_pow_eq_self_acris_gaussNorm : ∀ (l : ℕ) [Fact l.Prime] (h s : ℕ), s < h → ∀ (w w' : Formalism.Per.Acris l) (ζ : Formalism.Per.Fl l) (o : ℕ) (ρ₀ : ℝ), (φc l)^[h] w' = (l : Formalism.Per.Acris l) ^ s * w' → w' ≠ 0 → φc l w * w' = w * φc l w' → (∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ w = gC l ρ w') → 0 < o → ζ ^ (l ^ o) = ζ → ζ ≠ 0 → (l : ℝ)⁻¹ ≤ ρ₀ → ρ₀ < 1 → gC l ρ₀ (w - tc l ζ * w') < gC l ρ₀ w' → ζ ^ l = ζ := by
  first | exact @GlobalTheory.PMon.Gauss.root_cancel_pow_eq_self | exact GlobalTheory.PMon.Gauss.root_cancel_pow_eq_self | (intros; apply GlobalTheory.PMon.Gauss.root_cancel_pow_eq_self <;> assumption)
end
