module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KummerNotCoboundary

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAcrisLogOneAdd
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAcrisLogOneAdd
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.LogU

variable {l : ℕ} [Fact l.Prime]

theorem acris_lim_pt (s : ℕ → Per.Acris0 l)
    (hs : ∀ r n, l ^ r ≤ n → ∃ z : Per.Acris0 l, s n - s (l ^ r) = ((l : ℕ) : Per.Acris0 l) ^ r * z) :
    ∃ y : Per.Acris l, ∀ r n, l ^ r ≤ n → ∃ z : Per.Acris l,
      y - algebraMap (Per.Acris0 l) (Per.Acris l) (s n) = ((l : ℕ) : Per.Acris l) ^ r * z := by
  obtain ⟨e, he⟩ := GlobalTheory.AdicMaps.exists_acris_completion l
  obtain ⟨y, hy⟩ := Model.pc_lim (l := l) (Per.Acris0 l) s hs
  refine ⟨e.symm y, fun r n hn => ?_⟩
  obtain ⟨z, hz⟩ := hy r n hn
  refine ⟨e.symm z, e.injective ?_⟩
  rw [map_sub, map_mul, map_pow, map_natCast, e.apply_symm_apply, e.apply_symm_apply, he]
  exact hz

theorem frobenius_surjective_modP : Function.Surjective (frobenius (ModP (Per.OC l) l) l) := by
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hl : 0 < l := (Fact.out : l.Prime).pos
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (a : ℂ_[l]) hl
  have hb1 : b ∈ 𝓞_ℂ_[l] := by
    rw [GlobalTheory.RingBasics.mem_OC]
    have := (GlobalTheory.RingBasics.mem_OC _).1 a.2
    rw [← hb, norm_pow] at this
    exact (pow_le_one_iff_of_nonneg (norm_nonneg _) hl.ne').1 this
  refine ⟨Ideal.Quotient.mk _ ⟨b, hb1⟩, ?_⟩
  rw [frobenius_def, ← map_pow]
  exact congrArg _ (Subtype.ext hb)

theorem θ_surjective : Function.Surjective (Per.θ l) :=
  surjective_fontaineTheta frobenius_surjective_modP

theorem exists_divPow {w : Per.Ainf l} (hw : InJ w) (k : ℕ) :
    ∃ g : Per.Acris0 l, ((k.factorial : ℕ) : Per.AinfP l) * (g : Per.AinfP l) =
      algebraMap (Per.Ainf l) (Per.AinfP l) w ^ k := by
  obtain ⟨c, hc⟩ := hw
  obtain ⟨a, ha⟩ := θ_surjective (l := l) c
  have hz : Per.θ l (w - (l : Per.Ainf l) * a) = 0 := by
    rw [map_sub, map_mul, map_natCast, ha, hc, sub_self]
  have hd : ∀ j : ℕ, ∃ d : Per.AinfP l, d ∈ Per.Acris0 l ∧ ((j.factorial : ℕ) : Per.AinfP l) * d =
      algebraMap (Per.Ainf l) (Per.AinfP l) (w - (l : Per.Ainf l) * a) ^ j := by
    intro j
    obtain ⟨u, hu⟩ := (GlobalTheory.RingBasics.isUnit_nat l _ j.factorial_ne_zero).exists_right_inv
    have e : ((j.factorial : ℕ) : Per.AinfP l) *
        (u * algebraMap (Per.Ainf l) (Per.AinfP l) (w - (l : Per.Ainf l) * a) ^ j) =
        algebraMap (Per.Ainf l) (Per.AinfP l) (w - (l : Per.Ainf l) * a) ^ j := by
      rw [← mul_assoc, hu, one_mul]
    exact ⟨_, GlobalTheory.RingIface.dividedPower_mem_Acris0 l _ j _ hz e, e⟩
  choose d hdm hdd using hd
  choose q hq using fun m : ℕ => GlobalTheory.RingBasics.exists_pow_div_factorial l m
  let ζ : ℤ_[l] →+* Per.AinfP l := (algebraMap (Per.Ainf l) (Per.AinfP l)).comp (Per.zA l)
  have hq' : ∀ m : ℕ, ((m.factorial : ℕ) : Per.AinfP l) * ζ (q m) = ((l : ℕ) : Per.AinfP l) ^ m := by
    intro m
    have h := congrArg ζ (hq m)
    rwa [map_mul, map_natCast, map_pow, map_natCast] at h
  have hg : (∑ m ∈ Finset.range (k + 1), ζ (q m) * algebraMap (Per.Ainf l) (Per.AinfP l) a ^ m *
      d (k - m)) ∈ Per.Acris0 l := by
    refine Subalgebra.sum_mem _ fun m _ => mul_mem (mul_mem ?_ (pow_mem (Subalgebra.algebraMap_mem _ _) _))
      (hdm _)
    exact Subalgebra.algebraMap_mem _ (Per.zA l (q m))
  refine ⟨⟨_, hg⟩, ?_⟩
  have hw' : algebraMap (Per.Ainf l) (Per.AinfP l) w = ((l : ℕ) : Per.AinfP l) * algebraMap (Per.Ainf l) (Per.AinfP l) a +
      algebraMap (Per.Ainf l) (Per.AinfP l) (w - (l : Per.Ainf l) * a) := by
    rw [map_sub, map_mul, map_natCast]
    ring
  show _ * ∑ m ∈ Finset.range (k + 1), _ = _
  rw [hw', add_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmk : m ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
  have hf : ((k.factorial : ℕ) : Per.AinfP l) = ((k.choose m : ℕ) : Per.AinfP l) *
      ((m.factorial : ℕ) : Per.AinfP l) * (((k - m).factorial : ℕ) : Per.AinfP l) := by
    rw [← Nat.cast_mul, ← Nat.cast_mul, Nat.choose_mul_factorial_mul_factorial hmk]
  rw [hf, mul_pow, ← hq' m, ← hdd (k - m)]
  ring

theorem exists_isLogJ : ∀ (l : ℕ) [Fact l.Prime] (w : Per.Ainf l), InJ w → ∃ y : Per.Acris l, IsLogJ w y := by
  intro l _ w hw
  have hl : l.Prime := Fact.out
  choose g hg using exists_divPow hw
  let s : ℕ → Per.Acris0 l := fun n =>
    ∑ k ∈ Finset.range n, (-1) ^ k * ((k.factorial : ℕ) : Per.Acris0 l) * g (k + 1)
  obtain ⟨y, hy⟩ := acris_lim_pt s (by
    intro r n hn
    have : ((l : ℕ) : Per.Acris0 l) ^ r ∣ s n - s (l ^ r) := by
      simp only [s]
      rw [← Finset.sum_Ico_eq_sub _ hn]
      refine Finset.dvd_sum fun k hk => ?_
      have h1 : l ^ r ∣ k.factorial := Nat.dvd_factorial (pow_pos hl.pos r) (Finset.mem_Ico.1 hk).1
      have h2 : ((l : ℕ) : Per.Acris0 l) ^ r ∣ ((k.factorial : ℕ) : Per.Acris0 l) := by
        exact_mod_cast Nat.cast_dvd_cast (α := Per.Acris0 l) h1
      exact (h2.mul_left _).mul_right _
    exact this)
  refine ⟨y, fun r => ⟨l ^ r, fun n hn => ⟨s n, ?_, hy r n hn⟩⟩⟩
  simp only [s]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have h1 : n.factorial = n.factorial / (k + 1) * (k + 1) :=
    (Nat.div_mul_cancel (Nat.dvd_factorial k.succ_pos (Finset.mem_range.1 hk))).symm
  have h2 : ((n.factorial : ℕ) : Per.AinfP l) = ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) * (k + 1) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → Per.AinfP l) h1
  rw [← hg (k + 1), Nat.factorial_succ]
  generalize ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) = q at h2 ⊢
  rw [h2]
  push_cast
  ring

end GlobalTheory.LogU
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAcrisLogOneAddStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_acris_log_one_add : ∀ (l : ℕ) [Fact l.Prime] (w : Per.Ainf l), GlobalTheory.LogU.InJ w → ∃ y : Per.Acris l, GlobalTheory.LogU.IsLogJ w y := by
  first | exact @GlobalTheory.LogU.exists_isLogJ | exact GlobalTheory.LogU.exists_isLogJ | (intros; apply GlobalTheory.LogU.exists_isLogJ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AevalLogDefect
noncomputable section

namespace GlobalTheory.LogU

def truncLogF {R : Type} [CommRing R] (n : ℕ) (u : R) : R :=
  ∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : R) * u ^ (k + 1)

theorem map_truncLogF {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (n : ℕ) (u : R) :
    f (truncLogF n u) = truncLogF n (f u) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [truncLogF, map_sum, map_mul, map_pow, map_neg, map_one, map_natCast]

def logDefect (n : ℕ) : MvPolynomial (Fin 2) ℤ :=
  truncLogF n (MvPolynomial.X 0 + MvPolynomial.X 1 + MvPolynomial.X 0 * MvPolynomial.X 1) -
    truncLogF n (MvPolynomial.X 0) - truncLogF n (MvPolynomial.X 1)

theorem aeval_logDefect {R : Type} [CommRing R] (n : ℕ) (a b : R) :
    MvPolynomial.aeval ![a, b] (logDefect n) = truncLogF n (a + b + a * b) - truncLogF n a - truncLogF n b := by
  have h := fun u => map_truncLogF (MvPolynomial.aeval (R := ℤ) ![a, b]).toRingHom n u
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h
  simp [logDefect, h]

end GlobalTheory.LogU
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltUnitTeichmullerPrincipalUnitSplit
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltUnitTeichmullerPrincipalUnitSplit
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.LogU.TeichSplit

variable {l : ℕ} [Fact l.Prime]

def nrm (y : Per.Fl l) : ℝ := ‖((y.untilt : Per.OC l) : ℂ_[l])‖

lemma nrm_mul (y z : Per.Fl l) : nrm (y * z) = nrm y * nrm z := by
  simp only [nrm, map_mul]
  push_cast
  exact norm_mul _ _

lemma nrm_one : nrm (1 : Per.Fl l) = 1 := by
  simp [nrm]

lemma nrm_pow (y : Per.Fl l) (n : ℕ) : nrm (y ^ n) = nrm y ^ n := by
  simp only [nrm, map_pow]
  push_cast
  exact norm_pow _ _

lemma nrm_nonneg (y : Per.Fl l) : 0 ≤ nrm y := norm_nonneg _

lemma nrm_le_one (y : Per.Fl l) : nrm y ≤ 1 := (GlobalTheory.RingBasics.mem_OC _).1 (y.untilt).2

lemma nrm_add (y z : Per.Fl l) : nrm (y + z) ≤ max (nrm y) (nrm z) :=
  (GlobalTheory.TiltAbs.untilt_ultrametric_definite l y z).1

lemma eq_zero_of_nrm (y : Per.Fl l) (h : nrm y = 0) : y = 0 := by
  refine (GlobalTheory.TiltAbs.untilt_ultrametric_definite l y y).2 ?_
  have : ((y.untilt : Per.OC l) : ℂ_[l]) = 0 := norm_eq_zero.1 h
  exact Subtype.ext this

lemma nrm_neg_one : nrm (-1 : Per.Fl l) = 1 := by
  have h : nrm (-1 : Per.Fl l) ^ 2 = 1 := by
    rw [← nrm_pow]; simp [nrm_one]
  exact (pow_eq_one_iff_of_nonneg (nrm_nonneg _) (by norm_num)).1 h

lemma nrm_neg (y : Per.Fl l) : nrm (-y) = nrm y := by
  rw [neg_eq_neg_one_mul, nrm_mul, nrm_neg_one, one_mul]

lemma nrm_sub_tri (a b c : Per.Fl l) : nrm (a - c) ≤ max (nrm (a - b)) (nrm (b - c)) := by
  have : a - c = (a - b) + (b - c) := by ring
  rw [this]; exact nrm_add _ _

lemma norm_l_pos : 0 < ‖((l : ℕ) : ℂ_[l])‖ := norm_pos_iff.2 GlobalTheory.RingBasics.p_ne_zero

lemma nrm_sub_le (y z : Per.Fl l) :
    nrm (y - z) ≤ max ‖((y.untilt : Per.OC l) : ℂ_[l]) - ((z.untilt : Per.OC l) : ℂ_[l])‖
      ‖((l : ℕ) : ℂ_[l])‖ := by
  obtain ⟨t, ht⟩ := GlobalTheory.TiltAbs.untilt_add (y - z) z
  rw [sub_add_cancel] at ht
  have h : (((y - z).untilt : Per.OC l) : ℂ_[l]) =
      (((y.untilt : Per.OC l) : ℂ_[l]) - ((z.untilt : Per.OC l) : ℂ_[l])) +
        (-((l : ℕ) : ℂ_[l]) * ((t : Per.OC l) : ℂ_[l])) := by
    rw [ht]; push_cast; ring
  unfold nrm
  rw [h]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max le_rfl ?_)
  rw [norm_mul, norm_neg]
  exact mul_le_of_le_one_right (norm_nonneg _) (GlobalTheory.TiltAbs.norm_le_one t)

private lemma exists_pow_between_pt {r s c : ℝ} (hr : 0 ≤ r) (hrs : r < s) (hs : s ≤ 1) (hc0 : 0 < c)
    (hc1 : c < 1) : ∃ n k : ℕ, r ^ n < c ^ k ∧ c ^ k < s ^ n := by
  have hs0 : 0 < s := lt_of_le_of_lt hr hrs
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hc0 ((div_lt_one hs0).2 hrs)
  obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near_of_lt_one (pow_pos hs0 n) (pow_le_one₀ hs0.le hs) hc0 hc1
  refine ⟨n, k + 1, ?_, hk1⟩
  rw [div_pow, div_lt_iff₀ (pow_pos hs0 n)] at hn
  calc r ^ n < c * s ^ n := hn
    _ ≤ c * c ^ k := mul_le_mul_of_nonneg_left hk2 hc0.le
    _ = c ^ (k + 1) := by ring

private lemma norm_map_mono_pt (f : Per.OC l →+* Per.OC l) (a b : Per.OC l)
    (h : ‖(a : ℂ_[l])‖ ≤ ‖(b : ℂ_[l])‖) : ‖((f a : Per.OC l) : ℂ_[l])‖ ≤ ‖((f b : Per.OC l) : ℂ_[l])‖ := by
  have hd : ∃ t : Per.OC l, a = b * t := by
    by_cases hb : (b : ℂ_[l]) = 0
    · rw [hb, norm_zero] at h
      have ha : (a : ℂ_[l]) = 0 := norm_le_zero_iff.1 h
      exact ⟨0, by rw [mul_zero]; exact Subtype.ext ha⟩
    · refine ⟨⟨(a : ℂ_[l]) / (b : ℂ_[l]), (GlobalTheory.RingBasics.mem_OC _).2 ?_⟩, Subtype.ext ?_⟩
      · rw [norm_div]; exact div_le_one_of_le₀ h (norm_nonneg _)
      · push_cast
        rw [mul_div_cancel₀ _ hb]
  obtain ⟨t, rfl⟩ := hd
  rw [map_mul]
  push_cast
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (GlobalTheory.TiltAbs.norm_le_one _)

private lemma norm_map_pt (f : Per.OC l →+* Per.OC l) (y : Per.OC l) :
    ‖((f y : Per.OC l) : ℂ_[l])‖ = ‖(y : ℂ_[l])‖ := by
  have hlt := GlobalTheory.TiltAbs.norm_l_lt (l := l)
  have e (z : Per.OC l) (n : ℕ) : ‖((z ^ n : Per.OC l) : ℂ_[l])‖ = ‖(z : ℂ_[l])‖ ^ n := by
    push_cast; exact norm_pow _ _
  have el : ‖((((l : ℕ) : Per.OC l)) : ℂ_[l])‖ = ‖((l : ℕ) : ℂ_[l])‖ := by
    push_cast; rfl
  rcases lt_trichotomy ‖((f y : Per.OC l) : ℂ_[l])‖ ‖(y : ℂ_[l])‖ with h | h | h
  · obtain ⟨n, k, h1, h2⟩ := exists_pow_between_pt (norm_nonneg _) h (GlobalTheory.TiltAbs.norm_le_one y)
      (norm_l_pos (l := l)) hlt
    have h3 := norm_map_mono_pt f (((l : ℕ) : Per.OC l) ^ k) (y ^ n) (by rw [e, e, el]; exact h2.le)
    rw [map_pow, map_pow, map_natCast, e, e, el] at h3
    exact absurd h1 (not_lt.2 h3)
  · exact h
  · obtain ⟨n, k, h1, h2⟩ := exists_pow_between_pt (norm_nonneg _) h (GlobalTheory.TiltAbs.norm_le_one (f y))
      (norm_l_pos (l := l)) hlt
    have h3 := norm_map_mono_pt f (y ^ n) (((l : ℕ) : Per.OC l) ^ k) (by rw [e, e, el]; exact h1.le)
    rw [map_pow, map_pow, map_natCast, e, e, el] at h3
    exact absurd h2 (not_lt.2 h3)

lemma nrm_σF (g : Per.Gq l) (y : Per.Fl l) : nrm (Per.σF g y) = nrm y := by
  unfold nrm
  rw [GlobalTheory.RingBasics.untilt_σF]
  exact norm_map_pt (Per.σO g) _

end GlobalTheory.LogU.TeichSplit

namespace GlobalTheory.LogU.TeichSplit
variable {l : ℕ} [Fact l.Prime]

lemma nrm_eq_one_of_isUnit {x : Per.Fl l} (hx : IsUnit x) : nrm x = 1 := by
  obtain ⟨y, hy⟩ := hx.exists_right_inv
  have h := congrArg nrm hy
  rw [nrm_mul, nrm_one] at h
  nlinarith [nrm_le_one x, nrm_le_one y, nrm_nonneg x, nrm_nonneg y]

lemma eq_zero_of_pow_eq_self {d : Per.Fl l} {q : ℕ} (hq : 2 ≤ q) (hd : d ^ q = d) (h : nrm d < 1) :
    d = 0 := by
  refine eq_zero_of_nrm d ?_
  have h1 : nrm d ^ q = nrm d := by rw [← nrm_pow, hd]
  by_contra hne
  have hpos : 0 < nrm d := lt_of_le_of_ne (nrm_nonneg d) (Ne.symm hne)
  have h2 : nrm d ^ (q - 1) = 1 := by
    have : nrm d ^ (q - 1) * nrm d = 1 * nrm d := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega), h1, one_mul]
    exact mul_right_cancel₀ hpos.ne' this
  have := (pow_eq_one_iff_of_nonneg (nrm_nonneg d) (by omega)).1 h2
  linarith

lemma inJ_of_nrm {y : Per.Fl l} (h : nrm (y - 1) ≤ ‖((l : ℕ) : ℂ_[l])‖) : InJ (Per.tm y - 1) := by
  obtain ⟨t, ht⟩ := GlobalTheory.TiltAbs.untilt_add (y - 1) 1
  rw [sub_add_cancel, map_one] at ht
  have hmem : (y - 1).untilt ∈ (Ideal.span {((l : ℕ) : Per.OC l)}) ^ 1 := by
    rw [GlobalTheory.RingBasics.mem_span_pow_OC, pow_one]; exact h
  rw [pow_one, Ideal.mem_span_singleton'] at hmem
  obtain ⟨s, hs⟩ := hmem
  refine ⟨s + t, ?_⟩
  rw [map_sub, map_one, WittVector.fontaineTheta_teichmuller, ht, ← hs]
  ring

end GlobalTheory.LogU.TeichSplit


open GlobalTheory.LogU.TeichSplit in
theorem GlobalTheory.LogU.teich_split : ∀ (l : ℕ) [Fact l.Prime] (x : Per.Fl l), IsUnit x → ∃ (ω x₁ : Per.Fl l) (N : ℕ), x = ω * x₁ ∧ GlobalTheory.LogU.InJ (Per.tm (x₁ ^ (l ^ N)) - 1) ∧ ∀ (g : Per.Gq l) (e : Per.Fl l), e.untilt = 1 → Per.σF g x = x * e → Per.σF g ω = ω := by
  intro l _ x hx
  have hl : l.Prime := Fact.out
  have hlt := GlobalTheory.TiltAbs.norm_l_lt (l := l)
  have hN1 : nrm x = 1 := nrm_eq_one_of_isUnit hx

  obtain ⟨α, hα⟩ := UniformSpace.Completion.denseRange_coe.exists_dist_lt
    (((x.untilt : Per.OC l) : ℂ_[l])) one_pos
  rw [dist_eq_norm] at hα
  have hαn : ‖α‖ = 1 := by
    rw [← PadicComplex.norm_extends]
    have hx1 : ‖((x.untilt : Per.OC l) : ℂ_[l])‖ = 1 := hN1
    have a1 : ‖((α : PadicAlgCl l) : ℂ_[l])‖ ≤ 1 := by
      have := IsUltrametricDist.norm_add_le_max (((x.untilt : Per.OC l) : ℂ_[l]))
        (((α : PadicAlgCl l) : ℂ_[l]) - ((x.untilt : Per.OC l) : ℂ_[l]))
      rw [add_sub_cancel, norm_sub_rev] at this
      exact this.trans (max_le hx1.le hα.le)
    have a2 := IsUltrametricDist.norm_add_le_max (((α : PadicAlgCl l) : ℂ_[l]))
        (((x.untilt : Per.OC l) : ℂ_[l]) - ((α : PadicAlgCl l) : ℂ_[l]))
    rw [add_sub_cancel, hx1] at a2
    refine le_antisymm a1 ?_
    rcases le_max_iff.1 a2 with h | h
    · exact h
    · exact absurd h (not_le.2 hα)
  obtain ⟨ζ, m, hm, hζ, hαζ⟩ := ReciprocityTheory.DiscreteGroups.LocalClassField.exists_teichmuller_bar α hαn
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; exact hm (dvd_zero l))
  obtain ⟨ω, hωm, hωζ⟩ := GlobalTheory.MemLoc.exists_tilt_root_of_unity l ζ m hm0 hm hζ

  have hxω : nrm (x - ω) < 1 := by
    refine lt_of_le_of_lt (nrm_sub_le x ω) (max_lt ?_ hlt)
    rw [hωζ]
    have e1 : ((x.untilt : Per.OC l) : ℂ_[l]) - ((ζ : Om l) : ℂ_[l]) =
        (((x.untilt : Per.OC l) : ℂ_[l]) - ((α : PadicAlgCl l) : ℂ_[l])) +
          (((α - ζ : PadicAlgCl l)) : ℂ_[l]) := by
      rw [UniformSpace.Completion.coe_sub]; ring
    rw [e1]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hα ?_)
    rw [PadicComplex.norm_extends]; exact hαζ
  set x₁ := x * ω ^ (m - 1) with hx₁
  have hωω : ω * ω ^ (m - 1) = 1 := by
    rw [← pow_succ', Nat.sub_add_cancel hm0, hωm]
  have hx1 : nrm (x₁ - 1) < 1 := by
    have : x₁ - 1 = ω ^ (m - 1) * (x - ω) := by
      rw [hx₁, ← hωω]; ring
    rw [this, nrm_mul]
    calc nrm (ω ^ (m - 1)) * nrm (x - ω) ≤ 1 * nrm (x - ω) :=
          mul_le_mul_of_nonneg_right (nrm_le_one _) (nrm_nonneg _)
      _ < 1 := by rw [one_mul]; exact hxω

  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (norm_l_pos (l := l)) hx1
  refine ⟨ω, x₁, k, ?_, ?_, ?_⟩
  · rw [hx₁, ← mul_assoc, mul_comm ω x, mul_assoc, hωω, mul_one]
  · refine inJ_of_nrm ?_
    have e2 : x₁ ^ l ^ k - 1 = (x₁ - 1) ^ l ^ k := by
      rw [sub_pow_char_pow, one_pow]
    rw [e2, nrm_pow]
    refine le_trans (pow_le_pow_of_le_one (nrm_nonneg _) (nrm_le_one _)
      (Nat.lt_pow_self hl.one_lt).le) hk.le
  · intro g e he hgx
    have f0 : 0 < Nat.totient m := Nat.totient_pos.2 hm0
    have hcop : Nat.Coprime l m := (Nat.Prime.coprime_iff_not_dvd hl).2 hm
    have hmod : l ^ Nat.totient m ≡ 1 [MOD m] := Nat.ModEq.pow_totient hcop
    have hq1 : 1 ≤ l ^ Nat.totient m := Nat.one_le_pow _ _ hl.pos
    obtain ⟨c, hc⟩ := (Nat.modEq_iff_dvd' hq1).1 hmod.symm
    have hωq : ω ^ l ^ Nat.totient m = ω := by
      rw [← Nat.sub_add_cancel hq1, pow_succ, hc, pow_mul, hωm, one_pow, one_mul]
    have hq2 : 2 ≤ l ^ Nat.totient m :=
      le_trans hl.two_le (Nat.le_self_pow f0.ne' l)
    rw [← sub_eq_zero]
    refine eq_zero_of_pow_eq_self hq2 ?_ ?_
    · rw [sub_pow_char_pow, ← map_pow, hωq]
    · have he1 : nrm (e - 1) < 1 := by
        refine lt_of_le_of_lt (nrm_sub_le e 1) (max_lt ?_ hlt)
        rw [he, map_one, sub_self, norm_zero]; exact zero_lt_one
      have h1 : nrm (Per.σF g ω - Per.σF g x) < 1 := by
        rw [← map_sub, nrm_σF, ← neg_sub, nrm_neg]; exact hxω
      have h2 : nrm (Per.σF g x - x) < 1 := by
        have : Per.σF g x - x = x * (e - 1) := by rw [hgx]; ring
        rw [this, nrm_mul, hN1, one_mul]; exact he1
      refine lt_of_le_of_lt (nrm_sub_tri _ (Per.σF g x) _) (max_lt h1 ?_)
      exact lt_of_le_of_lt (nrm_sub_tri _ x _) (max_lt h2 hxω)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltUnitTeichmullerPrincipalUnitSplitStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tilt_unit_teichmuller_principal_unit_split : ∀ (l : ℕ) [Fact l.Prime] (x : Per.Fl l), IsUnit x → ∃ (ω x₁ : Per.Fl l) (N : ℕ), x = ω * x₁ ∧ GlobalTheory.LogU.InJ (Per.tm (x₁ ^ (l ^ N)) - 1) ∧ ∀ (g : Per.Gq l) (e : Per.Fl l), e.untilt = 1 → Per.σF g x = x * e → Per.σF g ω = ω := by
  first | (exact @GlobalTheory.LogU.teich_split) | (exact GlobalTheory.LogU.teich_split) | (intros; apply GlobalTheory.LogU.teich_split  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAcrisLogOneAddAddOfMul
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LogDefectCoeffEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LogDefectCoeffEqZero
open GlobalTheory.LogU

namespace GlobalTheory.LogU

open MvPolynomial

theorem logDefect_coeff_eq_zero : ∀ (n i j : ℕ), i + j < n →
    AddMonoidAlgebra.coeff (GlobalTheory.LogU.logDefect n) (Finsupp.single 0 i + Finsupp.single 1 j) = 0 := by
  intro n i j hij
  let J : Ideal (MvPolynomial (Fin 2) ℚ) := MvPolynomial.idealOfVars (Fin 2) ℚ
  let q : MvPolynomial (Fin 2) ℚ →+* MvPolynomial (Fin 2) ℚ ⧸ J ^ n := Ideal.Quotient.mk _
  have hR : ∀ m : ℕ, m ≠ 0 → IsUnit (m : MvPolynomial (Fin 2) ℚ ⧸ J ^ n) := fun m hm => by
    have hu : IsUnit ((m : ℚ)) := (Nat.cast_ne_zero.2 hm).isUnit
    simpa using hu.map (q.comp MvPolynomial.C)
  have hI : (J.map q) ^ n = ⊥ := by
    rw [← Ideal.map_pow]; exact Ideal.map_quotient_self _
  have hXJ : ∀ k, (X k : MvPolynomial (Fin 2) ℚ) ∈ J := fun k =>
    Ideal.subset_span (Set.mem_range_self k)
  have key := GlobalTheory.MemLoc.LogAdd.trunc_add hR n _ hI (q (X 0)) (q (X 1))
    (Ideal.mem_map_of_mem q (hXJ 0)) (Ideal.mem_map_of_mem q (hXJ 1))
  have h0 : MvPolynomial.aeval ![q (X 0), q (X 1)] (logDefect n) = 0 := by
    refine (aeval_logDefect n (q (X 0)) (q (X 1))).trans ?_
    simp only [truncLogF]; rw [key]; ring
  have hcomp : q.comp (MvPolynomial.map (Int.castRingHom ℚ)) =
      (MvPolynomial.aeval (R := ℤ) ![q (X 0), q (X 1)]).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp
    · intro k; fin_cases k <;> simp
  have hφ : q (MvPolynomial.map (Int.castRingHom ℚ) (logDefect n)) = 0 := by
    have := RingHom.congr_fun hcomp (logDefect n)
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at this
    rw [this, h0]
  rw [Ideal.Quotient.eq_zero_iff_mem, mem_pow_idealOfVars_iff'] at hφ
  have hd : (Finsupp.single (0 : Fin 2) i + Finsupp.single 1 j).degree < n := by
    first
      | simpa [Finsupp.degree_single] using hij
      | simpa [Finsupp.degree, Finsupp.support_single_ne_zero] using hij
  have := hφ _ hd
  rw [MvPolynomial.coeff_map] at this
  simpa using this

end GlobalTheory.LogU
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LogDefectCoeffEqZeroStatement
open GlobalTheory.LogU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_logDefect_eq_zero_of_add_lt : ∀ (n i j : ℕ), i + j < n → AddMonoidAlgebra.coeff (GlobalTheory.LogU.logDefect n) (Finsupp.single 0 i + Finsupp.single 1 j) = 0 := by
  first | (exact @GlobalTheory.LogU.logDefect_coeff_eq_zero) | (exact GlobalTheory.LogU.logDefect_coeff_eq_zero) | (intros; apply GlobalTheory.LogU.logDefect_coeff_eq_zero  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorialTruncatedLogAdditivityDefectCoeffDvd
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorialTruncatedLogAdditivityDefectCoeffDvd
open GlobalTheory.LogU MvPolynomial Finset

namespace GlobalTheory.LogUIntg

lemma single_add_single_eq_iff {i j i' j' : ℕ} :
    (Finsupp.single (0 : Fin 2) i + Finsupp.single 1 j = Finsupp.single 0 i' + Finsupp.single 1 j') ↔
      (i = i' ∧ j = j') := by
  constructor
  · intro h
    have h0 := congrArg (fun f => f 0) h
    have h1 := congrArg (fun f => f 1) h
    simp at h0 h1
    exact ⟨h0, h1⟩
  · rintro ⟨rfl, rfl⟩; rfl

lemma coeff_monomial_two (i j p q : ℕ) (c : ℤ) :
    AddMonoidAlgebra.coeff (monomial (Finsupp.single (0 : Fin 2) p + Finsupp.single 1 q) c)
        (Finsupp.single 0 i + Finsupp.single 1 j) =
      if p = i ∧ q = j then c else 0 := by
  rw [coeff_monomial]
  simp only [single_add_single_eq_iff]

lemma monomial_two_eq (p q : ℕ) (c : ℤ) :
    monomial (Finsupp.single (0 : Fin 2) p + Finsupp.single 1 q) c = C c * X 0 ^ p * X 1 ^ q := by
  rw [X_pow_eq_monomial, X_pow_eq_monomial, C_mul_monomial, monomial_mul]
  simp

lemma factorial_dvd_term (n K s a : ℕ) (hK1 : 1 ≤ K) (hKn : K ≤ n) (hs : s ≤ K) (ha : a ≤ K - s)
    (hn : n ≤ (s + a) + (s + (K - s - a))) :
    n.factorial * ((n - 1) / 2).factorial ∣
      (s + a).factorial * (s + (K - s - a)).factorial *
        (n.factorial / K * (K.choose s * (K - s).choose a)) := by
  have e1 := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right s a)
  rw [Nat.add_sub_cancel_left] at e1
  have e2 := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right s (K - s - a))
  rw [Nat.add_sub_cancel_left] at e2
  have e3 := Nat.choose_mul_factorial_mul_factorial ha
  have e4 := Nat.choose_mul_factorial_mul_factorial hs
  have e5 : n.factorial / K * K.factorial = n.factorial * (K - 1).factorial := by
    rw [← Nat.mul_factorial_pred (by omega : K ≠ 0), ← mul_assoc,
      Nat.div_mul_cancel (Nat.dvd_factorial (by omega) hKn)]
  rw [← e1, ← e2]
  have key : (s + a).choose s * s.factorial * a.factorial *
      ((s + (K - s - a)).choose s * s.factorial * (K - s - a).factorial) *
        (n.factorial / K * (K.choose s * (K - s).choose a)) =
      n.factorial * ((K - 1).factorial * ((s + a).choose s * (s + (K - s - a)).choose s * s.factorial)) := by
    calc _ = (s + a).choose s * (s + (K - s - a)).choose s * s.factorial *
          ((K.choose s * s.factorial * ((K - s).choose a * a.factorial * (K - s - a).factorial)) *
            (n.factorial / K)) := by ring
      _ = (s + a).choose s * (s + (K - s - a)).choose s * s.factorial *
          (n.factorial / K * K.factorial) := by rw [e3, e4]; ring
      _ = _ := by rw [e5]; ring
  rw [key]
  exact mul_dvd_mul (dvd_refl _)
    (dvd_mul_of_dvd_left (Nat.factorial_dvd_factorial (by omega)) _)

def Good (n : ℕ) (f : MvPolynomial (Fin 2) ℤ) : Prop :=
  ∀ i j : ℕ, n ≤ i + j → ((n.factorial * ((n - 1) / 2).factorial : ℕ) : ℤ) ∣
    ((i.factorial * j.factorial : ℕ) : ℤ) * AddMonoidAlgebra.coeff f (Finsupp.single 0 i + Finsupp.single 1 j)

lemma good_sub {n : ℕ} {f g : MvPolynomial (Fin 2) ℤ} (hf : Good n f) (hg : Good n g) :
    Good n (f - g) := by
  intro i j h
  rw [coeff_sub, mul_sub]
  exact dvd_sub (hf i j h) (hg i j h)

lemma good_sum {n : ℕ} {ι : Type} (t : Finset ι) (f : ι → MvPolynomial (Fin 2) ℤ)
    (hf : ∀ x ∈ t, Good n (f x)) : Good n (∑ x ∈ t, f x) := by
  intro i j h
  rw [coeff_sum, Finset.mul_sum]
  exact Finset.dvd_sum fun x hx => hf x hx i j h

lemma good_C_mul {n : ℕ} (c : ℤ) {f : MvPolynomial (Fin 2) ℤ} (hf : Good n f) :
    Good n (C c * f) := by
  intro i j h
  rw [coeff_C_mul, mul_left_comm]
  exact Dvd.dvd.mul_left (hf i j h) c

lemma good_atom (n K s a : ℕ) (hK1 : 1 ≤ K) (hKn : K ≤ n) (hs : s ≤ K) (ha : a ≤ K - s) :
    Good n (monomial (Finsupp.single (0 : Fin 2) (s + a) + Finsupp.single 1 (s + (K - s - a)))
      ((n.factorial / K * (K.choose s * (K - s).choose a) : ℕ) : ℤ)) := by
  intro i j h
  rw [coeff_monomial_two]
  split_ifs with hij
  · obtain ⟨rfl, rfl⟩ := hij
    rw [← Nat.cast_mul]
    exact Int.natCast_dvd_natCast.mpr (factorial_dvd_term n K s a hK1 hKn hs ha h)
  · simp

lemma C_mul_pow_u (m K : ℕ) :
    C (m : ℤ) * (X 0 + X 1 + X 0 * X 1 : MvPolynomial (Fin 2) ℤ) ^ K =
      ∑ s ∈ range (K + 1), ∑ a ∈ range (K - s + 1),
        monomial (Finsupp.single (0 : Fin 2) (s + a) + Finsupp.single 1 (s + (K - s - a)))
          ((m * (K.choose s * (K - s).choose a) : ℕ) : ℤ) := by
  rw [show (X 0 + X 1 + X 0 * X 1 : MvPolynomial (Fin 2) ℤ) = X 0 * X 1 + (X 0 + X 1) by ring,
    add_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [add_pow]
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [monomial_two_eq]
  simp only [Nat.cast_mul, map_mul, map_natCast]
  ring

lemma good_C_mul_pow_u (n K : ℕ) (hK1 : 1 ≤ K) (hKn : K ≤ n) :
    Good n (C ((n.factorial / K : ℕ) : ℤ) * (X 0 + X 1 + X 0 * X 1 : MvPolynomial (Fin 2) ℤ) ^ K) := by
  rw [C_mul_pow_u]
  refine good_sum _ _ fun s hs => good_sum _ _ fun a ha => ?_
  rw [Finset.mem_range] at hs ha
  exact good_atom n K s a hK1 hKn (by omega) (by omega)

lemma logPolynomialDefectDivisible_C_mul_X_zero_pow (n K : ℕ) (hK1 : 1 ≤ K) (hKn : K ≤ n) :
    Good n (C ((n.factorial / K : ℕ) : ℤ) * (X 0 : MvPolynomial (Fin 2) ℤ) ^ K) := by
  have h := good_atom n K 0 K hK1 hKn (by omega) (by omega)
  rw [monomial_two_eq] at h
  simpa using h

lemma logPolynomialDefectDivisible_C_mul_X_one_pow (n K : ℕ) (hK1 : 1 ≤ K) (hKn : K ≤ n) :
    Good n (C ((n.factorial / K : ℕ) : ℤ) * (X 1 : MvPolynomial (Fin 2) ℤ) ^ K) := by
  have h := good_atom n K 0 0 hK1 hKn (by omega) (by omega)
  rw [monomial_two_eq] at h
  simpa using h

lemma good_truncLogF (n : ℕ) (u : MvPolynomial (Fin 2) ℤ)
    (hu : ∀ K, 1 ≤ K → K ≤ n → Good n (C ((n.factorial / K : ℕ) : ℤ) * u ^ K)) :
    Good n (truncLogF n u) := by
  unfold truncLogF
  refine good_sum _ _ fun k hk => ?_
  rw [Finset.mem_range] at hk
  have e : ((-1 : MvPolynomial (Fin 2) ℤ) ^ k * ((n.factorial / (k + 1) : ℕ) : MvPolynomial (Fin 2) ℤ) *
      u ^ (k + 1)) = C ((-1) ^ k) * (C ((n.factorial / (k + 1) : ℕ) : ℤ) * u ^ (k + 1)) := by
    simp only [map_pow, map_neg, map_one, map_natCast]; ring
  rw [e]
  exact good_C_mul _ (hu (k + 1) (by omega) (by omega))

theorem good_logDefect (n : ℕ) : Good n (logDefect n) := by
  unfold logDefect
  refine good_sub (good_sub ?_ ?_) ?_
  · exact good_truncLogF n _ fun K h1 h2 => good_C_mul_pow_u n K h1 h2
  · exact good_truncLogF n _ fun K h1 h2 => logPolynomialDefectDivisible_C_mul_X_zero_pow n K h1 h2
  · exact good_truncLogF n _ fun K h1 h2 => logPolynomialDefectDivisible_C_mul_X_one_pow n K h1 h2

theorem logDefect_coeff_dvd : ∀ (n i j : ℕ), n ≤ i + j → ∃ d : ℤ,
    ((i.factorial * j.factorial : ℕ) : ℤ) *
        AddMonoidAlgebra.coeff (GlobalTheory.LogU.logDefect n) (Finsupp.single 0 i + Finsupp.single 1 j) =
      ((n.factorial * ((n - 1) / 2).factorial : ℕ) : ℤ) * d := by
  intro n i j h
  exact good_logDefect n i j h

end GlobalTheory.LogUIntg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorialTruncatedLogAdditivityDefectCoeffDvdStatement
open GlobalTheory.LogU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.factorialTruncatedLogAdditivityDefect_coeff_dvd : ∀ (n i j : ℕ), n ≤ i + j → ∃ d : ℤ, ((i.factorial * j.factorial : ℕ) : ℤ) * AddMonoidAlgebra.coeff (GlobalTheory.LogU.logDefect n) (Finsupp.single 0 i + Finsupp.single 1 j) = ((n.factorial * ((n - 1) / 2).factorial : ℕ) : ℤ) * d := by
  first | exact @GlobalTheory.LogUIntg.logDefect_coeff_dvd | exact GlobalTheory.LogUIntg.logDefect_coeff_dvd | (intros; apply GlobalTheory.LogUIntg.logDefect_coeff_dvd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAcrisLogOneAddAddOfMul
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.LogU

theorem defect_mem {R : Type} [CommRing R] (S : Subring R) (a b : R)
    (ha : ∀ i : ℕ, ∃ g ∈ S, ((i.factorial : ℕ) : R) * g = a ^ i)
    (hb : ∀ j : ℕ, ∃ g ∈ S, ((j.factorial : ℕ) : R) * g = b ^ j) (n : ℕ) :
    ∃ e ∈ S, truncLogF n (a + b + a * b) - truncLogF n a - truncLogF n b =
      ((n.factorial * ((n - 1) / 2).factorial : ℕ) : R) * e := by
  choose A hAS hA using ha
  choose B hBS hB using hb
  have hD : ∀ d : Fin 2 →₀ ℕ, ∃ D : ℤ, (((d 0).factorial * (d 1).factorial : ℕ) : ℤ) *
      AddMonoidAlgebra.coeff (logDefect n) d = ((n.factorial * ((n - 1) / 2).factorial : ℕ) : ℤ) * D := by
    intro d
    have hd : Finsupp.single 0 (d 0) + Finsupp.single 1 (d 1) = d := by
      ext x; fin_cases x <;> simp
    by_cases h : d 0 + d 1 < n
    · have := GlobalTheory.T.coeff_logDefect_eq_zero_of_add_lt n (d 0) (d 1) h
      rw [hd] at this
      exact ⟨0, by rw [this]; simp⟩
    · obtain ⟨D, hD⟩ := GlobalTheory.T.factorialTruncatedLogAdditivityDefect_coeff_dvd n (d 0) (d 1) (by omega)
      rw [hd] at hD
      exact ⟨D, hD⟩
  choose D hD using hD
  refine ⟨∑ d ∈ (logDefect n).support, (D d : R) * (A (d 0) * B (d 1)),
    Subring.sum_mem _ fun d _ => Subring.mul_mem _ (intCast_mem S _)
      (Subring.mul_mem _ (hAS _) (hBS _)), ?_⟩
  rw [← aeval_logDefect, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  have hc := congrArg (Int.cast : ℤ → R) (hD d)
  push_cast at hc
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, eq_intCast]
  rw [← hA, ← hB]
  push_cast
  linear_combination (A (d 0) * B (d 1)) * hc

theorem isLogJ_add : ∀ (l : ℕ) [Fact l.Prime] (a b : Per.Ainf l) (y y' : Per.Acris l), GlobalTheory.LogU.InJ a →
    GlobalTheory.LogU.InJ b → GlobalTheory.LogU.IsLogJ a y → GlobalTheory.LogU.IsLogJ b y' → GlobalTheory.LogU.IsLogJ (a + b + a * b) (y + y') := by
  intro l _ a b y y' ha hb hy hy' r
  have hl : l.Prime := Fact.out
  obtain ⟨N1, hN1⟩ := hy r
  obtain ⟨N2, hN2⟩ := hy' r
  refine ⟨max (max N1 N2) (2 * l ^ r + 1), fun n hn => ?_⟩
  obtain ⟨sa, hsa, za, hza⟩ := hN1 n (le_of_max_le_left (le_of_max_le_left hn))
  obtain ⟨sb, hsb, zb, hzb⟩ := hN2 n (le_of_max_le_right (le_of_max_le_left hn))
  have hn' : 2 * l ^ r + 1 ≤ n := le_of_max_le_right hn
  have hA : ∀ i : ℕ, ∃ g ∈ (Per.Acris0 l).toSubring, ((i.factorial : ℕ) : Per.AinfP l) * g =
      algebraMap (Per.Ainf l) (Per.AinfP l) a ^ i := fun i => by
    obtain ⟨g, hg⟩ := exists_divPow ha i
    exact ⟨g, g.2, hg⟩
  have hB : ∀ i : ℕ, ∃ g ∈ (Per.Acris0 l).toSubring, ((i.factorial : ℕ) : Per.AinfP l) * g =
      algebraMap (Per.Ainf l) (Per.AinfP l) b ^ i := fun i => by
    obtain ⟨g, hg⟩ := exists_divPow hb i
    exact ⟨g, g.2, hg⟩
  obtain ⟨e, he, hE⟩ := defect_mem _ _ _ hA hB n
  have hdvd : l ^ r ∣ ((n - 1) / 2).factorial := by
    refine Nat.dvd_factorial (pow_pos hl.pos r) ?_
    generalize l ^ r = L at hn' ⊢
    omega
  obtain ⟨q, hq⟩ := hdvd
  let E : Per.Acris0 l := ⟨e, he⟩
  refine ⟨sa + sb + ((l ^ r * q : ℕ) : Per.Acris0 l) * E, ?_,
    za + zb - (q : Per.Acris l) * algebraMap (Per.Acris0 l) (Per.Acris l) E, ?_⟩
  · rw [hq] at hE
    simp only [truncLogF] at hE
    have hEe : ((E : Per.Acris0 l) : Per.AinfP l) = e := rfl
    have hc : (((sa + sb + ((l ^ r * q : ℕ) : Per.Acris0 l) * E : Per.Acris0 l)) : Per.AinfP l) =
        (sa : Per.AinfP l) + (sb : Per.AinfP l) + ((l ^ r * q : ℕ) : Per.AinfP l) * e := by
      simp [hEe]
    rw [hc]
    simp only [map_add (f := _), map_mul]
    push_cast at hE ⊢
    linear_combination hsa + hsb - hE
  · set_option synthInstance.maxHeartbeats 200000 in
    simp only [map_add (f := algebraMap (Per.Acris0 l) (Per.Acris l)), map_mul, map_natCast]
    push_cast
    linear_combination hza + hzb

end GlobalTheory.LogU
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAcrisLogOneAddAddOfMulStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAcrisLogOneAdd_add_of_mul : ∀ (l : ℕ) [Fact l.Prime] (a b : Per.Ainf l) (y y' : Per.Acris l), GlobalTheory.LogU.InJ a → GlobalTheory.LogU.InJ b → GlobalTheory.LogU.IsLogJ a y → GlobalTheory.LogU.IsLogJ b y' → GlobalTheory.LogU.IsLogJ (a + b + a * b) (y + y') := by
  first | (exact @GlobalTheory.LogU.isLogJ_add) | (exact GlobalTheory.LogU.isLogJ_add) | (intros; apply GlobalTheory.LogU.isLogJ_add  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTeichmullerLogUnitBcris
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.LogU
open GlobalTheory.MemLoc

variable {l : ℕ} [Fact l.Prime]

theorem isLogJ_pow {e : Per.Fl l} (hJ : InJ (Per.tm e - 1)) {y : Per.Acris l} (hy : IsLogJ (Per.tm e - 1) y) :
    ∀ m : ℕ, IsLogJ (Per.tm (e ^ m) - 1) ((m : Per.Acris l) * y)
  | 0 => by simpa using (isLogJ_zero : IsLogJ (l := l) 0 0)
  | m + 1 => by
    have h := GlobalTheory.T.isAcrisLogOneAdd_add_of_mul l _ _ _ _ (inJ_pow hJ m) hJ (isLogJ_pow hJ hy m) hy
    have e1 : Per.tm (e ^ (m + 1)) - 1 = (Per.tm (e ^ m) - 1) + (Per.tm e - 1) +
        (Per.tm (e ^ m) - 1) * (Per.tm e - 1) := by
      rw [pow_succ, show Per.tm (e ^ m * e) = Per.tm (e ^ m) * Per.tm e from
        map_mul (WittVector.teichmuller l) _ _]
      ring
    rw [e1]
    convert h using 1
    push_cast
    ring

theorem iter_mul (a b : Per.Fl l) (m : ℕ) : ((frobeniusEquiv (Per.Fl l) l).symm)^[m] (a * b) =
    ((frobeniusEquiv (Per.Fl l) l).symm)^[m] a * ((frobeniusEquiv (Per.Fl l) l).symm)^[m] b := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_mul]

theorem iter_one (m : ℕ) : ((frobeniusEquiv (Per.Fl l) l).symm)^[m] 1 = 1 := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', ih, map_one]

theorem rootT_mul (a b : Per.Fl l) (m : ℕ) : rootT (a * b) m = rootT a m * rootT b m := by
  simp only [rootT, iter_mul, map_mul]

theorem rootT_one (m : ℕ) : rootT (1 : Per.Fl l) m = 1 := by
  simp only [rootT, iter_one, map_one]

theorem exists_gal_log (C : Core l) (x : Per.Fl l) (hx : IsUnit x) (g : GQ l) (c : ℤ_[l])
    (H : ∀ m, rootT (Per.σF g x) m = rootT C.ε m ^ (PadicInt.toZModPow m c).val * rootT x m) :
    ∃ e : Per.Fl l, e.untilt = 1 ∧ Per.σF g x = x * e ∧
      IsLogA e (algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l c) * C.t) := by
  obtain ⟨v, hv⟩ := hx.exists_left_inv
  have hxe : Per.σF g x = x * (v * Per.σF g x) := by rw [← mul_assoc, mul_comm x v, hv, one_mul]
  have hre : ∀ m, rootT (v * Per.σF g x) m = rootT C.ε m ^ (PadicInt.toZModPow m c).val := by
    intro m
    have hu : IsUnit (rootT x m) := by
      have h1 := congrArg (fun z => rootT z m) hv
      simp only [rootT_mul, rootT_one] at h1
      exact ⟨⟨rootT x m, rootT v m, by rw [mul_comm]; exact h1, h1⟩, rfl⟩
    apply hu.mul_left_cancel
    rw [← rootT_mul, ← hxe, H m, mul_comm]
  have he1 : (v * Per.σF g x).untilt = 1 := by
    have := hre 0
    simp only [rootT, Function.iterate_zero, id] at this
    rw [this, TAct.eps_untilt C, one_pow]
  have hr : ∀ m, (rootT (v * Per.σF g x) m : ℂ_[l]) =
      algebraMap (Om l) ℂ_[l] (C.ζ m ^ (PadicInt.toZModPow m c).val) := by
    intro m
    rw [hre m, SubmonoidClass.coe_pow, C.ε_root m, map_pow]
  obtain ⟨y, hy⟩ := Model.exists_isLogA he1
  exact ⟨_, he1, hxe, GlobalTheory.Pst.NoLog.log_eq C _ c y hr hy ▸ hy⟩

theorem map_inv_units {R : Type} [CommRing R] (f : R →+* R) (u : Rˣ) (h : f u = u) :
    f (↑u⁻¹ : R) = ↑u⁻¹ := by
  have h1 := congrArg f (Units.inv_mul u)
  rw [map_mul, h, map_one] at h1
  calc f (↑u⁻¹ : R) = f ↑u⁻¹ * (↑u * ↑u⁻¹) := by rw [Units.mul_inv, mul_one]
    _ = ↑u⁻¹ := by rw [← mul_assoc, h1, one_mul]

theorem exists_log_unit : ∀ (l : ℕ) [Fact l.Prime] (C : Core l) (x : OCb l), IsUnit x → ∃ b : Per.Bcris l, Per.φB l b = (l : Per.Bcris l) * b ∧ ∀ (g : GQ l) (c : ℤ_[l]), (∀ m, rootT (Per.σF g x) m = rootT C.ε m ^ (PadicInt.toZModPow m c).val * rootT x m) → Per.σB g b = b + Per.zB l c * C.tB := by
  intro l _ C x hx
  obtain ⟨ω, x₁, N, hxω, hJ, hω⟩ := GlobalTheory.T.tilt_unit_teichmuller_principal_unit_split l x hx
  obtain ⟨y, hy⟩ := GlobalTheory.T.exists_acris_log_one_add l _ hJ
  have hpow := isLogJ_pow hJ hy
  obtain ⟨u, hu⟩ := (isUnit_l_Bcris l).pow N
  have hωu : IsUnit ω := isUnit_of_mul_isUnit_left (hxω ▸ hx)
  refine ⟨↑u⁻¹ * algebraMap (Per.Acris l) (Per.Bcris l) y, ?_, fun g c H => ?_⟩
  · have h2 := isLogJ_extends (GlobalTheory.CrisMaps.phiA_extends l) hy
    have h3 : Per.φA l (Per.tm (x₁ ^ l ^ N) - 1) = Per.tm ((x₁ ^ l ^ N) ^ l) - 1 := by
      rw [map_sub, map_one, show Per.φA l (Per.tm (x₁ ^ l ^ N)) = Per.tm ((x₁ ^ l ^ N) ^ l) from
        GlobalTheory.RingIface.phiA_teich l _]
    rw [h3] at h2
    have h1 : GlobalTheory.MemLoc.phiA l y = (l : Per.Acris l) * y := isLogJ_unique h2 (hpow l)
    have hφY : Per.φB l (algebraMap (Per.Acris l) (Per.Bcris l) y) =
        (l : Per.Bcris l) * algebraMap (Per.Acris l) (Per.Bcris l) y := by
      have : Per.φB l (algebraMap (Per.Acris l) (Per.Bcris l) y) =
          algebraMap _ _ (GlobalTheory.MemLoc.phiA l y) :=
        GlobalTheory.CrisMaps.φB_phiA l y
      rw [this, h1, map_mul, map_natCast]
    have hφu : Per.φB l (↑u⁻¹ : Per.Bcris l) = ↑u⁻¹ :=
      map_inv_units _ u (by rw [hu, map_pow, map_natCast])
    rw [map_mul, hφu, hφY]
    ring
  · obtain ⟨e, he1, hgx, hle⟩ := exists_gal_log C x hx g c H
    have hgω : Per.σF g ω = ω := hω g e he1 hgx
    have hgx₁ : Per.σF g x₁ = x₁ * e := by
      apply hωu.mul_left_cancel
      rw [← mul_assoc, ← hxω, ← hgx, hxω, map_mul, hgω]
    have hge₁ : Per.σF g (x₁ ^ l ^ N) = x₁ ^ l ^ N * e ^ l ^ N := by rw [map_pow, hgx₁, mul_pow]
    have hle' := TAct.logA_pow C.j_cris he1 hle (l ^ N)
    have hsum := GlobalTheory.T.isAcrisLogOneAdd_add_of_mul l _ _ _ _ hJ (inJ_mu (e := e ^ l ^ N) (by rw [map_pow, he1, one_pow])) hy hle'
    have hσ := isLogJ_extends (GlobalTheory.CrisMaps.sigA_extends g) hy
    have hw : Per.σA g (Per.tm (x₁ ^ l ^ N) - 1) = (Per.tm (x₁ ^ l ^ N) - 1) + mu (e ^ l ^ N) +
        (Per.tm (x₁ ^ l ^ N) - 1) * mu (e ^ l ^ N) := by
      rw [map_sub, map_one, show Per.σA g (Per.tm (x₁ ^ l ^ N)) = Per.tm (Per.σF g (x₁ ^ l ^ N)) from
        GlobalTheory.RingIface.sigA_teich l g _, hge₁, mu,
        show Per.tm (x₁ ^ l ^ N * e ^ l ^ N) = Per.tm (x₁ ^ l ^ N) * Per.tm (e ^ l ^ N) from
        map_mul (WittVector.teichmuller l) _ _]
      ring
    rw [hw] at hσ
    have hy' := isLogJ_unique hσ hsum
    have hσY : Per.σB g (algebraMap (Per.Acris l) (Per.Bcris l) y) =
        algebraMap _ _ (GlobalTheory.MemLoc.sigA g y) :=
      GlobalTheory.CrisMaps.σB_sigA g y
    have hσu : Per.σB g (↑u⁻¹ : Per.Bcris l) = ↑u⁻¹ :=
      map_inv_units _ u (by rw [hu, map_pow, map_natCast])
    have hul : (↑u⁻¹ : Per.Bcris l) * ((l ^ N : ℕ) : Per.Bcris l) = 1 := by
      rw [Nat.cast_pow, ← hu, Units.inv_mul]
    rw [map_mul, hσu, hσY, hy', map_add (f := _), map_mul, map_mul, map_natCast]
    rw [GlobalTheory.RingIface.zB_eq_aB_zA l c, GlobalTheory.RingIface.aB_eq_alg l (Per.zA l c)]
    simp only [Core.tB]
    linear_combination (algebraMap (Per.Acris l) (Per.Bcris l) (algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l c)) *
      algebraMap (Per.Acris l) (Per.Bcris l) C.t) * hul

end GlobalTheory.LogU
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTeichmullerLogUnitBcrisStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_teichmuller_log_unit_bcris : ∀ (l : ℕ) [Fact l.Prime] (C : Core l) (x : OCb l), IsUnit x → ∃ b : Per.Bcris l, Per.φB l b = (l : Per.Bcris l) * b ∧ ∀ (g : GQ l) (c : ℤ_[l]), (∀ m, rootT (Per.σF g x) m = rootT C.ε m ^ (PadicInt.toZModPow m c).val * rootT x m) → Per.σB g b = b + Per.zB l c * C.tB := by
  first | (exact @GlobalTheory.LogU.exists_log_unit) | (exact GlobalTheory.LogU.exists_log_unit) | (intros; apply GlobalTheory.LogU.exists_log_unit  <;> assumption)
end
