module

public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpSeriesCoeffBoundedTaylorEllipticOfPoles
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsOrthogonalFrameNormsCoprimeOfUnimodular
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CmThetaOperatorInvariantOfLiftCongrOne
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCmThetaEqSumProdTranslates
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TorsionLiftPairingInOrthogonalFrame

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DifferentiableU1
noncomputable section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.JetAlg

variable {p : ℕ} [hp : Fact p.Prime]

def ball (p : ℕ) [Fact p.Prime] : Subring ℂ_[p] := GlobalTheory.ClosedBallValuationSubring.closedBallSubring ℂ_[p]

theorem norm_p_lt_one : ‖(p : ℂ_[p])‖ < 1 := by
  have h := PadicComplex.norm_extends' p (p : ℚ_[p])
  have h2 : ‖(p : ℚ_[p])‖ < 1 := Padic.norm_p_lt_one
  rw [← h] at h2
  simpa using h2

theorem norm_sub_one_lt {y : ℂ_[p]} {k : ℕ} (h : y ^ p ^ k = 1) : ‖y - 1‖ < 1 := by
  have hne : p ^ k ≠ 0 := pow_ne_zero _ hp.out.ne_zero
  have hy : ‖y‖ ≤ 1 := by
    have h1 : ‖y‖ ^ p ^ k = 1 := by rw [← norm_pow, h, norm_one]
    exact ((pow_eq_one_iff_of_nonneg (norm_nonneg _) hne).1 h1).le
  let Y : ball p := ⟨y, hy⟩
  obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq hp.out (Y - 1) 1 k
  have hr' := congrArg (fun t : ball p => (t : ℂ_[p])) hr
  simp only [sub_add_cancel, one_pow, mul_one] at hr'
  push_cast at hr'
  have hz : ‖y - 1‖ ≤ 1 := (Y - 1).2
  have hrr : ‖(r : ℂ_[p])‖ ≤ 1 := r.2
  have e : (y - 1) ^ p ^ k = -((p : ℂ_[p]) * (y - 1) * r) := by
    have : (Y : ℂ_[p]) = y := rfl
    rw [this, h] at hr'
    linear_combination -hr'
  have h2 : ‖(y - 1) ^ p ^ k‖ < 1 := by
    rw [e, norm_neg, norm_mul, norm_mul, mul_assoc]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) norm_p_lt_one
      (mul_le_one₀ hz (norm_nonneg _) hrr)
  rw [norm_pow] at h2
  exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) hne).1 h2

theorem bd_derivative {f : ℂ_[p]⟦X⟧} (hf : Bd 1 f) : Bd 1 (PowerSeries.derivative f) := by
  intro n
  rw [coeff_derivative, norm_mul]
  refine mul_le_one₀ (hf _) (norm_nonneg _) ?_
  have := IsUltrametricDist.norm_natCast_le_one ℂ_[p] (n + 1)
  simpa using this

theorem bd_DT {f : ℂ_[p]⟦X⟧} (hf : Bd 1 f) : Bd 1 (DT f) := by
  have h := bd_derivative hf
  intro n
  rw [DT, add_mul, one_mul, map_add (f := _)]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h n) ?_)
  cases n with
  | zero => simp
  | succ n => rw [coeff_succ_X_mul]; exact h n

theorem bd_iterate {f : ℂ_[p]⟦X⟧} (hf : Bd 1 f) (k : ℕ) : Bd 1 (DT^[k] f) := by
  induction k with
  | zero => exact hf
  | succ k ih => rw [Function.iterate_succ_apply']; exact bd_DT ih

theorem differentiable_U1 (d : ℕ) (x : ℂ) {F : ℂ → ℂ} (hF : Differentiable ℂ F) :
    Differentiable ℂ (U1 d x F) := by
  unfold U1 h1
  fun_prop

theorem differentiable_W1 (d : ℕ) (x : ℂ) {F : ℂ → ℂ} (hF : Differentiable ℂ F) :
    Differentiable ℂ (W1 d x F) := by
  have := differentiable_U1 d x hF
  unfold W1
  fun_prop

end GlobalTheory.MomOne.JetAlg

namespace GlobalTheory.MomOne
open JetAlg

theorem jets_algebraic : ∀ (d q : ℕ) [Fact q.Prime] (δ : ℂ) (θ : ℂ → ℂ), d.Prime → d % 16 = 7 → Split d q → IsTh d θ → δ ≠ 0 → (∀ ι : ℂ ≃+* ℂ_[q], ∃ Ω : ℂ_[q], ‖Ω‖ = 1 ∧ ThetaLaws ι d (Ω / ι δ) θ) → ∀ (ι : ℂ ≃+* ℂ_[q]) (t y : ℂ) (n s k : ℕ), Nat.Coprime s q → InOK d ((s : ℂ) * t) → Good ι d n s y → δ⁻¹ ^ k * iteratedDeriv k (W1 d y (U1 d t θ)) 0 ∈ algebraicClosure ℚ ℂ := by
  intro d q hq δ θ hd hd16 hsp hθ hδ hL ι t y n s k hs ht hy
  refine mem_algebraicClosure_of_norm_le q ι _ 1 ?_
  intro ι' hι'
  obtain ⟨Ω, hΩ, h1', h2', -⟩ := hL ι'
  obtain ⟨hA, hB, -⟩ := okArith d q ι hd hd16 hsp
  have hy' : Good ι' d n s y := by
    obtain ⟨v, hv, hn, rfl⟩ := hy
    refine ⟨v, hv, ?_, rfl⟩
    have hc : InOK d (conj v) := (hA.2.2 v v hv hv).2.2.2
    have := hι' ⟨conj v, (hB _ hc).2.2⟩
    simp only at this
    rw [this]; exact hn
  have hs0 : 0 < s := by
    rcases Nat.eq_zero_or_pos s with rfl | h
    · exact absurd (by simpa using hs) hq.out.ne_one
    · exact h
  obtain ⟨hζ, hE⟩ := h2' t y n s hs ht hy'
  have hb := (Shift.shift_laws q _ (norm_sub_one_lt hζ)).1 _ _ (h1' t ⟨s, hs0, hs, ht⟩)
  rw [← hE] at hb
  have han : AnalyticAt ℂ (W1 d y (U1 d t θ)) 0 :=
    (differentiable_W1 d y (differentiable_U1 d t hθ.1)).analyticAt 0
  have hk := (hat_multiplicative_chart q ι' (Ω / ι' δ) _ han).2.1 k
  have hc := bd_iterate hb k 0
  rw [coeff_zero_eq_constantCoeff_apply, hk, div_eq_mul_inv, mul_pow, mul_assoc, norm_mul, norm_pow, hΩ,
    one_pow, one_mul] at hc
  rw [map_mul, map_pow, map_inv₀]
  exact hc

end GlobalTheory.MomOne
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaVectorsSetupExistsEqSmul
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaVectorsSetupExistsEqSmul
open GlobalTheory.MomOne Formalism.L2.Ker.JMB
open scoped ComplexConjugate BigOperators ComplexOrder
open Matrix

namespace GlobalTheory.MomOne.ThetaLine

variable {g : ℕ}

theorem dot_transpose_eq_hf (Hm : Matrix (Fin g) (Fin g) ℂ) (z a : Fin g → ℂ) :
    star a ⬝ᵥ Hmᵀ.mulVec z = hf Hm z a := by
  simp only [dotProduct, mulVec, transpose_apply, hf, Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def]
  ring

theorem im_hf_int {d : ℕ} (hd : 0 < d) (Hm : Matrix (Fin g) (Fin g) ℂ) (x y : Fin g → ℂ)
    (h : beta d Hm x y ∈ OK d) : ∃ k : ℤ, (hf Hm x y).im = k := by
  obtain ⟨u, v, huv⟩ := h
  refine ⟨v, ?_⟩
  have hs : Real.sqrt d / 2 ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
    positivity
  have key : (beta d Hm x y).im = Real.sqrt d / 2 * (hf Hm x y).im := by
    rw [beta, Complex.im_ofReal_mul]
  have hv : (beta d Hm x y).im = Real.sqrt d / 2 * v := by
    rw [huv]
    simp [w0, rtd]
    ring
  exact mul_left_cancel₀ hs (key.symm.trans hv)

theorem transl_of_fixed {d : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} {x : Fin g → ℂ}
    {G : (Fin g → ℂ) → ℂ} (h : opW d Hm x G = G) (z : Fin g → ℂ) :
    G (z + x) = Complex.exp (-((Real.pi : ℂ) * Complex.I * ((beta d Hm x x).re : ℂ))) *
      Complex.exp (Real.pi * hf Hm z x + Real.pi / 2 * hf Hm x x) * G z := by
  have hz := congrFun h z
  simp only [opW, opU] at hz
  have e1 : Complex.exp (-((Real.pi : ℂ) * Complex.I * ((beta d Hm x x).re : ℂ))) *
      Complex.exp ((Real.pi : ℂ) * Complex.I * ((beta d Hm x x).re : ℂ)) = 1 := by
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  have e2 : Complex.exp (Real.pi * hf Hm z x + Real.pi / 2 * hf Hm x x) *
      Complex.exp (-(Real.pi : ℂ) * hf Hm z x - (Real.pi : ℂ) / 2 * hf Hm x x) = 1 := by
    rw [← Complex.exp_add]
    convert Complex.exp_zero using 2
    ring
  rw [← hz]
  linear_combination (-(G (z + x) * Complex.exp (Real.pi * hf Hm z x + Real.pi / 2 * hf Hm x x) *
      Complex.exp (-(Real.pi : ℂ) * hf Hm z x - (Real.pi : ℂ) / 2 * hf Hm x x))) * e1 - G (z + x) * e2

theorem exists_eq_smul : ∀ (g : ℕ) (S : Setup g) (e F : (Fin g → ℂ) → ℂ), S.Ok → S.IsTheta e → S.IsTheta F → F ≠ 0 → ∃ c : ℂ, e = c • F := by
  intro g S e F hS he hF hF0
  obtain ⟨hp, -, hH, hdisc, -, -, hβ, hdual⟩ := hS
  have : DiscreteTopology S.La.toAddSubgroup := hdisc
  have hlaw : ∀ G : (Fin g → ℂ) → ℂ, S.IsTheta G → ∀ a ∈ S.La.toAddSubgroup, ∀ z,
      G (z + a) = Complex.exp (-((Real.pi : ℂ) * Complex.I * ((beta S.d S.Hm a a).re : ℂ))) *
        Complex.exp (Real.pi * (star a ⬝ᵥ S.Hmᵀ.mulVec z) + Real.pi / 2 * (star a ⬝ᵥ S.Hmᵀ.mulVec a)) * G z := by
    intro G hG a ha z
    rw [dot_transpose_eq_hf, dot_transpose_eq_hf]
    exact transl_of_fixed (hG.2 a ha) z
  refine GlobalTheory.ThetaTranslSpan.exists_eq_smul hH.transpose S.La.toAddSubgroup ?_
    (fun a => Complex.exp (-((Real.pi : ℂ) * Complex.I * ((beta S.d S.Hm a a).re : ℂ)))) F e ?_
    (hF.1.differentiable (by simp)) hF0 (hlaw F hF) (he.1.differentiable (by simp)) (hlaw e he)
  · intro v
    simp only [dot_transpose_eq_hf]
    exact ⟨hdual v, fun hv a ha => im_hf_int hp.pos S.Hm a v (hβ a ha v hv)⟩
  · intro a _
    simp [Complex.norm_exp]

end GlobalTheory.MomOne.ThetaLine
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaVectorsSetupExistsEqSmulStatement
open GlobalTheory.MomOne Formalism.L2.Ker.JMB
open scoped ComplexConjugate BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_vectors_setup_exists_eq_smul : ∀ (g : ℕ) (S : Setup g) (e F : (Fin g → ℂ) → ℂ), S.Ok → S.IsTheta e → S.IsTheta F → F ≠ 0 → ∃ c : ℂ, e = c • F := by
  first | exact @GlobalTheory.MomOne.ThetaLine.exists_eq_smul | exact GlobalTheory.MomOne.ThetaLine.exists_eq_smul | (intros; apply GlobalTheory.MomOne.ThetaLine.exists_eq_smul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPadicIntFrameChangeEtaleBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPadicIntFrameChangeEtaleBasis
noncomputable section
open GlobalTheory.MomOne Formalism.L2.Ker.JMB
open scoped ComplexConjugate BigOperators ComplexOrder

namespace GlobalTheory.MomOne.FrameChange

variable {g : ℕ}

theorem beta_sum_left {κ : Type} [Fintype κ] (d : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (c : κ → ℂ)
    (v : κ → Fin g → ℂ) (w : Fin g → ℂ) :
    beta d Hm (∑ k, c k • v k) w = ∑ k, c k * beta d Hm (v k) w := by
  simp only [beta, hf, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm' (t' := Finset.univ) (s' := fun _ => Finset.univ) (h := by simp)]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin g))) (t := (Finset.univ : Finset κ))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem beta_conj (d : ℕ) {Hm : Matrix (Fin g) (Fin g) ℂ} (h : Hm.IsHermitian) (z w : Fin g → ℂ) :
    conj (beta d Hm z w) = beta d Hm w z := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [beta, hf, map_mul, map_sum, Complex.conj_ofReal, Complex.conj_conj]
  rw [Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have : conj (Hm j i) = Hm i j := h.apply i j
  rw [this]; ring

theorem eq_sum_frame (d : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (x : Fin g → Fin g → ℂ) (a : Fin g → ℕ)
    (hx : ∀ i j, beta d Hm (x i) (x j) = if i = j then (a i : ℂ) else 0) (ha : ∀ i, (a i : ℂ) ≠ 0)
    (v : Fin g → ℂ) : v = ∑ i, (beta d Hm v (x i) / (a i : ℂ)) • x i := by
  have key : ∀ (z : Fin g → ℂ) k, beta d Hm (∑ i, z i • x i) (x k) = z k * a k := by
    intro z k
    rw [beta_sum_left]
    simp [hx]
  have hli : LinearIndependent ℂ x := by
    refine Fintype.linearIndependent_iff.2 fun z hz k => ?_
    have h := key z k
    rw [hz] at h
    have h0 : beta d Hm 0 (x k) = 0 := by simp [beta, hf]
    rw [h0] at h
    exact (mul_eq_zero.1 h.symm).resolve_right (ha k)
  have hsp := hli.span_eq_top_of_card_eq_finrank' (by simp)
  have hv : v ∈ Submodule.span ℂ (Set.range x) := by rw [hsp]; trivial
  obtain ⟨z, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hv
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [key, mul_div_cancel_right₀ _ (ha i)]

def zcHom (q : ℕ) [Fact q.Prime] : ℤ_[q] →+* ℂ_[q] := (algebraMap ℚ_[q] ℂ_[q]).comp PadicInt.Coe.ringHom

theorem zcHom_injective (q : ℕ) [Fact q.Prime] : Function.Injective (zcHom q) :=
  (algebraMap ℚ_[q] ℂ_[q]).injective.comp Subtype.val_injective

end GlobalTheory.MomOne.FrameChange

namespace GlobalTheory.MomOne
open FrameChange

theorem frameChange : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (g : ℕ) (S : Setup g) (x : Fin g → Fin g → ℂ) (a : Fin g → ℕ) (r : ℕ) (b : Fin r → Fin g → ℂ), S.Ok → Split S.d q → (∀ i, x i ∈ S.La) → (∀ i j, beta S.d S.Hm (x i) (x j) = if i = j then (a i : ℂ) else 0) → (∀ i, 0 < a i ∧ Nat.Coprime (a i) q) → S.NNBasis q b → ∃ T : (Fin r → ℤ_[q]) ≃ₜ (Fin g → ℤ_[q]), ∀ A i, GlobalTheory.MomOne.zc (T A i) = ∑ j, GlobalTheory.MomOne.zc (A j) * ι (beta S.d S.Hm (x i) (b j)) := by
  intro q _ ι g S x a r b hS hsp hxL hx ha hb
  obtain ⟨hd, hd7, hpos, -, -, -, hβ, -⟩ := hS
  obtain ⟨hbL, hgen, hind⟩ := hb
  have hq : q.Prime := Fact.out
  have hH : S.Hm.IsHermitian := hpos.isHermitian
  obtain ⟨⟨h1, -, hR⟩, hZ, -⟩ := okArith S.d q ι hd hd7 hsp
  let O : Subring ℂ :=
    { carrier := {z | InOK S.d z}
      one_mem' := h1
      zero_mem' := ⟨0, 0, by simp⟩
      mul_mem' := fun {u v} hu hv => (hR u v hu hv).2.1
      add_mem' := fun {u v} hu hv => (hR u v hu hv).1
      neg_mem' := fun {u} hu => (hR u u hu hu).2.2.1 }
  have hconj : ∀ u, InOK S.d u → InOK S.d (conj u) := fun u hu => (hR u u hu hu).2.2.2
  choose s hs c hc hsc using fun i => hgen (x i) (hxL i)
  have hs0 : ∀ i, (s i : ℂ) ≠ 0 := fun i h => by
    have h' : s i = 0 := by exact_mod_cast h
    have := hs i
    rw [h', Nat.coprime_zero_left] at this
    exact hq.one_lt.ne' this
  have ha0 : ∀ i, (a i : ℂ) ≠ 0 := fun i => by exact_mod_cast (ha i).1.ne'

  have hMN : ∀ i k, ∑ j, beta S.d S.Hm (x i) (b j) * (conj (c k j) / (s k * a k)) = if i = k then 1 else 0 := by
    intro i k
    have e := beta_sum_left S.d S.Hm (c k) b (x i)
    have e2 := beta_sum_left S.d S.Hm (fun _ : Unit => (s k : ℂ)) (fun _ => x k) (x i)
    simp only [Finset.univ_unique, Finset.sum_singleton] at e2
    rw [← hsc k, e2] at e
    have e3 := congrArg conj e
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, beta_conj S.d hH, map_natCast] at e3
    simp_rw [← mul_div_assoc, mul_comm (beta _ _ _ _)]
    rw [← Finset.sum_div, ← e3, hx]
    split_ifs with h
    · subst h; exact div_self (mul_ne_zero (hs0 i) (ha0 i))
    · simp
  have hNM : ∀ j l, ∑ i, (conj (c i j) / (s i * a i)) * beta S.d S.Hm (x i) (b l) = if j = l then 1 else 0 := by
    intro j l
    set P : ℂ := ∏ i, ((s i : ℂ) * a i) with hP
    have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => mul_ne_zero (hs0 i) (ha0 i)
    let e : Fin r → ℂ := fun j => ∑ i, c i j / (s i * a i) * beta S.d S.Hm (b l) (x i)
    have hmem : ∀ j, P * (e j - if j = l then 1 else 0) ∈ O := by
      intro j
      have hPO : P ∈ O := O.prod_mem fun i _ => O.mul_mem (natCast_mem O _) (natCast_mem O _)
      rw [mul_sub, Finset.mul_sum]
      refine O.sub_mem (O.sum_mem fun i _ => ?_) (O.mul_mem hPO (by split_ifs; exacts [O.one_mem, O.zero_mem]))
      have : P * (c i j / (s i * a i) * beta S.d S.Hm (b l) (x i)) =
          (∏ k ∈ Finset.univ.erase i, ((s k : ℂ) * a k)) * c i j * beta S.d S.Hm (b l) (x i) := by
        rw [hP, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
        have := hs0 i
        have := ha0 i
        field_simp
      rw [this]
      exact O.mul_mem (O.mul_mem (O.prod_mem fun i _ => O.mul_mem (natCast_mem O _) (natCast_mem O _)) (hc i j))
        (hβ _ (hbL l) _ (hxL i))
    have hsum : ∑ j, e j • b j = b l := by
      conv_rhs => rw [eq_sum_frame S.d S.Hm x a hx ha0 (b l)]
      simp only [e, Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hxi : x i = (s i : ℂ)⁻¹ • ∑ j, c i j • b j := by
        rw [← hsc i, smul_smul, inv_mul_cancel₀ (hs0 i), one_smul]
      generalize beta S.d S.Hm (b l) (x i) = t
      rw [hxi, smul_smul, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_smul]
      congr 1
      have := hs0 i
      have := ha0 i
      field_simp
    have h0 := hind _ hmem (by
      simp only [mul_smul, sub_smul, ← Finset.smul_sum, Finset.sum_sub_distrib, hsum]
      simp [ite_smul]) j
    have h2 : e j = if j = l then 1 else 0 := sub_eq_zero.1 ((mul_eq_zero.1 h0).resolve_left hP0)
    have h3 := congrArg conj h2
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [e, map_sum, map_mul, map_div₀, beta_conj S.d hH, map_natCast] at h3
    rw [h3]
    split_ifs <;> simp

  choose m hm using fun i j => (hZ _ (hβ _ (hxL i) _ (hbL j))).1
  choose n hn using fun i j => (hZ _ (hconj _ (hc i j))).1
  have hu : ∀ i, ∃ u : ℤ_[q], ι ((s i * a i : ℂ)⁻¹) = zcHom q u := by
    intro i
    have hun : IsUnit ((s i * a i : ℕ) : ℤ_[q]) := by
      rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
      exact (Nat.Coprime.mul_left (hs i) (ha i).2).symm
    obtain ⟨u, hu⟩ := hun.exists_left_inv
    refine ⟨u, ?_⟩
    have := congrArg (zcHom q) hu
    rw [map_mul, map_natCast, map_one] at this
    rw [map_inv₀, eq_inv_of_mul_eq_one_left this]
    simp
  choose u hu using hu
  let M : Matrix (Fin g) (Fin r) ℤ_[q] := Matrix.of m
  let N : Matrix (Fin r) (Fin g) ℤ_[q] := Matrix.of fun j i => n i j * u i
  have hM : ∀ i j, zcHom q (M i j) = ι (beta S.d S.Hm (x i) (b j)) := fun i j => (hm i j).symm
  have hN : ∀ j i, zcHom q (N j i) = ι (conj (c i j) / (s i * a i)) := fun j i => by
    rw [div_eq_mul_inv, map_mul, hu, hn]
    exact map_mul (zcHom q) _ _
  have e1 : M * N = 1 := by
    apply Matrix.ext
    intro i k
    apply zcHom_injective q
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.mul_apply, map_sum]
    simp_rw [map_mul, hM, hN, ← map_mul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, hMN, Matrix.one_apply]
    split_ifs <;> simp
  have e2 : N * M = 1 := by
    apply Matrix.ext
    intro i k
    apply zcHom_injective q
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.mul_apply, map_sum]
    simp_rw [map_mul, hM, hN, ← map_mul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, hNM, Matrix.one_apply]
    split_ifs <;> simp
  refine ⟨{ toFun := M.mulVec
            invFun := N.mulVec
            left_inv := fun A => by rw [Matrix.mulVec_mulVec, e2, Matrix.one_mulVec]
            right_inv := fun A => by rw [Matrix.mulVec_mulVec, e1, Matrix.one_mulVec]
            continuous_toFun := continuous_const.matrix_mulVec continuous_id
            continuous_invFun := continuous_const.matrix_mulVec continuous_id }, fun A i => ?_⟩
  show zcHom q (∑ j, M i j * A j) = ∑ j, zcHom q (A j) * _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [map_mul, hM, mul_comm]

end GlobalTheory.MomOne
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPadicIntFrameChangeEtaleBasisStatement
open GlobalTheory.MomOne Formalism.L2.Ker.JMB
open scoped ComplexConjugate BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_padicInt_frame_change_etale_basis : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (g : ℕ) (S : Setup g) (x : Fin g → Fin g → ℂ) (a : Fin g → ℕ) (r : ℕ) (b : Fin r → Fin g → ℂ), S.Ok → Split S.d q → (∀ i, x i ∈ S.La) → (∀ i j, beta S.d S.Hm (x i) (x j) = if i = j then (a i : ℂ) else 0) → (∀ i, 0 < a i ∧ Nat.Coprime (a i) q) → S.NNBasis q b → ∃ T : (Fin r → ℤ_[q]) ≃ₜ (Fin g → ℤ_[q]), ∀ A i, GlobalTheory.MomOne.zc (T A i) = ∑ j, GlobalTheory.MomOne.zc (A j) * ι (beta S.d S.Hm (x i) (b j)) := by
  first | exact @GlobalTheory.MomOne.frameChange | exact GlobalTheory.MomOne.frameChange | (intros; apply GlobalTheory.MomOne.frameChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormSumProdLeOfCoord
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne

theorem norm_sum_prod_le_of_coord {K : Type*} [NormedCommRing K] {g m : ℕ} (F G : Fin m → Fin g → ℕ → K)
    (c : Fin m → K) (B : ℝ)
    (step : ∀ (i : Fin g) (c' : Fin m → K), (∀ n, ‖∑ j, c' j * F j i n‖ ≤ B) → ∀ n, ‖∑ j, c' j * G j i n‖ ≤ B)
    (h : ∀ ν : Fin g → ℕ, ‖∑ j, c j * ∏ i, F j i (ν i)‖ ≤ B) (ν : Fin g → ℕ) :
    ‖∑ j, c j * ∏ i, G j i (ν i)‖ ≤ B := by
  classical
  have key : ∀ I : Finset (Fin g), ∀ ν : Fin g → ℕ,
      ‖∑ j, c j * ∏ i, (if i ∈ I then G j i (ν i) else F j i (ν i))‖ ≤ B := by
    intro I
    induction I using Finset.induction_on with
    | empty => simpa using h
    | insert i₀ I hi ih =>
      intro ν
      have hs := step i₀
        (fun j => c j * ∏ i ∈ Finset.univ.erase i₀, (if i ∈ I then G j i (ν i) else F j i (ν i))) ?_ (ν i₀)
      · convert hs using 3 with j _
        rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i₀), mul_assoc]
        congr 2
        · refine Finset.prod_congr rfl fun i hi' => ?_
          simp [Finset.mem_insert, Finset.ne_of_mem_erase hi']
        · simp
      · intro n
        convert ih (Function.update ν i₀ n) using 3 with j _
        rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i₀), mul_assoc]
        congr 2
        · refine Finset.prod_congr rfl fun i hi' => ?_
          simp [Function.update_of_ne (Finset.ne_of_mem_erase hi')]
        · simp [hi]
  simpa using key Finset.univ ν

theorem translate_norm_prod_le : ∀ (d q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (ω : ℂ_[q]) (θ : ℂ → ℂ), ThetaLaws ι d ω θ → ∀ (g m : ℕ) (a : Fin g → ℕ) (c : Fin m → ℂ_[q]) (t : Fin m → Fin g → ℂ) (τ : Fin g → ℂ) (B : ℝ), (∀ j i, PrimeTo d q (t j i)) → (∀ i, PrimeTo d q (τ i)) → (∀ ν : Fin g → ℕ, ‖∑ j, c j * ∏ i, coeff (ν i) (hat ι (C ω * logS) (U1 d (t j i) θ) ^ a i)‖ ≤ B) → ∀ ν : Fin g → ℕ, ‖∑ j, c j * ∏ i, coeff (ν i) (hat ι (C ω * logS) (U1 d (τ i) (U1 d (t j i) θ)) ^ a i)‖ ≤ B := by
  intro d q _ ι ω θ hθ g m a c t τ B ht hτ h
  refine norm_sum_prod_le_of_coord
    (fun j i n => coeff n (hat ι (C ω * logS) (U1 d (t j i) θ) ^ a i))
    (fun j i n => coeff n (hat ι (C ω * logS) (U1 d (τ i) (U1 d (t j i) θ)) ^ a i)) c B ?_ h
  intro i c' hc n
  have := hθ.2.2 (a i) m c' (fun j => t j i) (τ i) B (fun j => ht j i) (hτ i) (fun k => by
    set_option synthInstance.maxHeartbeats 100000 in
      simpa only [map_sum, coeff_C_mul] using hc k) n
  set_option synthInstance.maxHeartbeats 100000 in
    simpa only [map_sum, coeff_C_mul] using this

end GlobalTheory.MomOne
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IteratedFDerivCombMem
open scoped BigOperators

namespace GlobalTheory.AlgJetComb

theorem pow_mem (δ : ℂ) (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (h : ∀ n, δ ^ n * iteratedDeriv n f 0 ∈ algebraicClosure ℚ ℂ) (a : ℕ) :
    ∀ n, δ ^ n * iteratedDeriv n (fun x => f x ^ a) 0 ∈ algebraicClosure ℚ ℂ := by
  induction a with
  | zero =>
    intro n
    simp only [pow_zero, iteratedDeriv_const]
    split_ifs with hn
    · subst hn; simpa using one_mem _
    · simpa using zero_mem _
  | succ a ih =>
    intro n
    have e : (fun x => f x ^ (a + 1)) = (fun x => f x ^ a) * f := by
      funext x; simp [pow_succ]
    have h1 : ContDiffAt ℂ n (fun x => f x ^ a) 0 := (hf.pow a).contDiff.contDiffAt
    have h2 : ContDiffAt ℂ n f 0 := hf.contDiff.contDiffAt
    rw [e, iteratedDeriv_mul h1 h2, Finset.mul_sum]
    refine sum_mem fun i hi => ?_
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have e2 : δ ^ n * ((n.choose i : ℂ) * iteratedDeriv i (fun x => f x ^ a) 0
        * iteratedDeriv (n - i) f 0) = (n.choose i : ℂ) *
        ((δ ^ i * iteratedDeriv i (fun x => f x ^ a) 0)
          * (δ ^ (n - i) * iteratedDeriv (n - i) f 0)) := by
      have : δ ^ n = δ ^ i * δ ^ (n - i) := by rw [← pow_add, Nat.add_sub_cancel' hi']
      rw [this]; ring
    rw [e2]
    exact mul_mem (natCast_mem _ _) (mul_mem (ih i) (h _))

theorem iteratedFDeriv_comb_mem :
    ∀ (g m k : ℕ) (δ : ℂ) (a : Fin g → ℕ) (c : Fin m → ℂ) (f : Fin m → Fin g → ℂ → ℂ)
      (ys : Fin k → Fin g → ℂ), (∀ j i, Differentiable ℂ (f j i)) →
      (∀ j i n, δ⁻¹ ^ n * iteratedDeriv n (f j i) 0 ∈ algebraicClosure ℚ ℂ) →
      (∀ j, c j ∈ algebraicClosure ℚ ℂ) → (∀ l i, ys l i ∈ algebraicClosure ℚ ℂ) →
      iteratedFDeriv ℂ k (fun z : Fin g → ℂ => ∑ j, c j * ∏ i, f j i (z i) ^ a i) 0
        (fun l => δ⁻¹ • ys l) ∈ algebraicClosure ℚ ℂ := by
  intro g m k δ a c f ys hf hj hc hy
  have hF : ∀ j, ContDiff ℂ k (fun z : Fin g → ℂ => ∏ i, f j i (z i) ^ a i) := fun j =>
    contDiff_prod fun i _ => (((hf j i).contDiff).comp (contDiff_apply ℂ (fun _ => ℂ) i)).pow _
  rw [iteratedFDeriv_fun_sum_apply (f := fun j (z : Fin g → ℂ) => c j * ∏ i, f j i (z i) ^ a i)
    (fun j _ => (contDiff_const.mul (hF j)).contDiffAt), ContinuousMultilinearMap.sum_apply]
  refine sum_mem fun j _ => ?_
  have e := iteratedFDeriv_const_smul_apply' (a := c j) (x := 0) (hF j).contDiffAt
  simp only [smul_eq_mul] at e
  rw [e, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  refine mul_mem (hc j) ?_
  rw [GlobalTheory.CoordProdDeriv.iteratedFDeriv_prod_coord g k (fun i x => f j i x ^ a i) _
    (fun i => (hf j i).pow _)]
  refine sum_mem fun σ _ => ?_
  have hk : ∑ i, (Finset.univ.filter (fun l => σ l = i)).card = k := by
    rw [← Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ) (f := σ)
      (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))]
    simp
  have e2 : (∏ l, (δ⁻¹ • ys l) (σ l)) *
      ∏ i, iteratedDeriv (Finset.univ.filter (fun l => σ l = i)).card
        (fun x => f j i x ^ a i) 0
      = (∏ l, ys l (σ l)) * ∏ i, (δ⁻¹ ^ (Finset.univ.filter (fun l => σ l = i)).card *
        iteratedDeriv (Finset.univ.filter (fun l => σ l = i)).card
        (fun x => f j i x ^ a i) 0) := by
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hk]
    simp only [Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
    ring
  rw [e2]
  exact mul_mem (prod_mem fun l _ => hy _ _)
    (prod_mem fun i _ => pow_mem δ⁻¹ (f j i) (hf j i) (hj j i) _ _)

end GlobalTheory.AlgJetComb
end

open PowerSeries GlobalTheory.MomOne Formalism.L2.Ker.JMB
open scoped ComplexConjugate BigOperators Topology

noncomputable section
namespace GlobalTheory.MomOne.Translates

theorem eq_zero_of_jets {g : ℕ} (Φ : (Fin g → ℂ) → ℂ) (hΦ : ContDiff ℂ ⊤ Φ) (δ : ℂ) (hδ : δ ≠ 0)
    (h : ∀ (k : ℕ) (σ : Fin k → Fin g),
      iteratedFDeriv ℂ k Φ 0 (fun l => δ⁻¹ • (Pi.single (σ l) 1 : Fin g → ℂ)) = 0) : Φ = 0 := by
  have hz : ∀ k, iteratedFDeriv ℂ k Φ 0 = 0 := by
    intro k
    apply ContinuousMultilinearMap.toMultilinearMap_injective
    refine Module.Basis.ext_multilinear (fun _ => Pi.basisFun ℂ (Fin g)) fun σ => ?_
    have := h k σ
    rw [ContinuousMultilinearMap.map_smul_univ] at this
    simp only [smul_eq_mul, mul_eq_zero, Finset.prod_eq_zero_iff, _root_.inv_eq_zero, hδ, and_false, exists_false,
      false_or] at this
    simpa using this
  have ha : AnalyticOnNhd ℂ Φ Set.univ := fun x _ => hΦ.contDiffAt.analyticAt
  obtain ⟨p, r, hp⟩ := ha 0 trivial
  have hev : Φ =ᶠ[𝓝 0] 0 := by
    filter_upwards [Metric.eball_mem_nhds (0 : Fin g → ℂ) hp.r_pos] with y hy
    have := hp.hasSum_iteratedFDeriv hy
    simp only [hz, zero_apply, smul_zero, zero_add] at this
    exact this.unique hasSum_zero
  exact ha.eq_of_eventuallyEq analyticOnNhd_const hev

def compIso {X Y K : Type} [TopologicalSpace X] [CompactSpace X] [TopologicalSpace Y] [CompactSpace Y]
    [NormedField K] (T : X ≃ₜ Y) : C(X, K) ≃ₗᵢ[K] C(Y, K) where
  toFun f := f.comp (T.symm : C(Y, X))
  invFun f := f.comp (T : C(X, Y))
  map_add' f g := rfl
  map_smul' c f := rfl
  left_inv f := by ext x; simp
  right_inv f := by ext x; simp
  norm_map' f := by
    apply le_antisymm
    · exact (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun y => f.norm_coe_le_norm _
    · refine (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun x => ?_
      have := (f.comp (T.symm : C(Y, X))).norm_coe_le_norm (T x)
      simpa using this

theorem inOK_add {d : ℕ} {α β : ℂ} (h : InOK d α) (h' : InOK d β) : InOK d (α + β) := by
  obtain ⟨u, v, rfl⟩ := h
  obtain ⟨u', v', rfl⟩ := h'
  exact ⟨u + u', v + v', by push_cast; ring⟩

theorem inOK_nat_mul {d : ℕ} {α : ℂ} (n : ℕ) (h : InOK d α) : InOK d (n * α) := by
  obtain ⟨u, v, rfl⟩ := h
  exact ⟨n * u, n * v, by push_cast; ring⟩

theorem primeTo_add {d q : ℕ} {α β : ℂ} (h : PrimeTo d q α) (h' : PrimeTo d q β) : PrimeTo d q (α + β) := by
  obtain ⟨s, hs, hc, h⟩ := h
  obtain ⟨s', hs', hc', h'⟩ := h'
  refine ⟨s * s', by positivity, Nat.Coprime.mul_left hc hc', ?_⟩
  have := inOK_add (inOK_nat_mul s' h) (inOK_nat_mul s h')
  convert this using 1
  push_cast; ring

theorem primeTo_neg {d q : ℕ} {α : ℂ} (h : PrimeTo d q α) : PrimeTo d q (-α) := by
  obtain ⟨s, hs, hc, u, v, h⟩ := h
  exact ⟨s, hs, hc, -u, -v, by push_cast; linear_combination -h⟩

theorem primeTo_common {d q : ℕ} {I : Type} [Fintype I] (t : I → ℂ) (h : ∀ i, PrimeTo d q (t i)) :
    ∃ s : ℕ, Nat.Coprime s q ∧ ∀ i, InOK d ((s : ℂ) * t i) := by
  classical
  choose s hs hc h using h
  refine ⟨∏ i, s i, Nat.Coprime.prod_left fun i _ => hc i, fun i => ?_⟩
  obtain ⟨k, hk⟩ : s i ∣ ∏ i, s i := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  have := inOK_nat_mul k (h i)
  rw [hk]
  convert this using 1
  push_cast; ring

def rho (d : ℕ) (x y : ℂ) : ℂ := Complex.exp (-(Real.pi : ℂ) * Complex.I * (((h1 d x y).im : ℝ) : ℂ))

theorem rho_mem {d q : ℕ} (hOK : ∀ x y, InOK d x → InOK d y → ∃ k : ℤ, (h1 d x y).im = k) {x y : ℂ}
    (hx : PrimeTo d q x) (hy : PrimeTo d q y) : rho d x y ∈ algebraicClosure ℚ ℂ := by
  obtain ⟨s, hs, -, hx⟩ := hx
  obtain ⟨s', hs', -, hy⟩ := hy
  obtain ⟨k, hk⟩ := hOK _ _ hx hy
  have e : h1 d (s * x) (s' * y) = ((s * s' : ℝ) : ℂ) * h1 d x y := by
    simp only [h1, map_mul, Complex.conj_natCast]; push_cast; ring
  rw [e, Complex.im_ofReal_mul] at hk
  have hk' : ((s : ℂ) * s') * (((h1 d x y).im : ℝ) : ℂ) = k := by exact_mod_cast hk
  have hp : rho d x y ^ (2 * s * s') = 1 := by
    rw [rho, ← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
    refine ⟨-k, ?_⟩
    push_cast
    linear_combination (-2 * (Real.pi : ℂ) * Complex.I) * hk'
  rw [mem_algebraicClosure_iff]
  refine IsAlgebraic.of_pow (n := 2 * s * s') (by positivity) ?_
  rw [hp]; exact isAlgebraic_one

theorem thetaTranslation_comp_eq_cocycle_mul {d : ℕ} (hd : 0 < d) (x y : ℂ) (F : ℂ → ℂ) :
    U1 d x (U1 d y F) = fun z => rho d x y * U1 d (x + y) F z := (GlobalTheory.T.cmLattice_heisenberg_relations_one_variable d hd).1 x y F

theorem cmLatticeTranslationOperator_eq_phase_mul_neg_comp {d : ℕ} (hd : 0 < d) (x y : ℂ) (F : ℂ → ℂ) :
    U1 d y F = fun z => rho d x y * U1 d (-x) (U1 d (x + y) F) z := by
  have e1 : U1 d (-x) (U1 d x (U1 d y F)) = U1 d y F := by
    rw [thetaTranslation_comp_eq_cocycle_mul hd (-x) x, neg_add_cancel, (GlobalTheory.T.cmLattice_heisenberg_relations_one_variable d hd).2.1]
    have : (h1 d (-x) x).im = 0 := by
      rw [h1, Complex.im_ofReal_mul]; simp [mul_comm]
    simp [rho, this]
  rw [← e1, thetaTranslation_comp_eq_cocycle_mul hd x y]
  funext z
  simp only [U1]; ring

theorem cmLatticeWeylOperator_const_mul (d : ℕ) (y c : ℂ) (F : ℂ → ℂ) :
    W1 d y (fun z => c * F z) = fun z => c * W1 d y F z := by
  funext z; simp only [W1, U1]; ring

variable {q : ℕ} [Fact q.Prime]

theorem family_scale (ι : ℂ ≃+* ℂ_[q]) (ω : ℂ_[q]) {g m : ℕ} (a : Fin g → ℕ) (c : Fin m → ℂ)
    (ρ : Fin m → Fin g → ℂ) (f : Fin m → Fin g → ℂ → ℂ) (hf : ∀ j i, Differentiable ℂ (f j i)) (ν : Fin g → ℕ) :
    ∑ j, ι (c j) * ∏ i, coeff (ν i) (hat ι (C ω * logS) (fun z => ρ j i * f j i z) ^ a i) =
      ∑ j, ι (c j * ∏ i, ρ j i ^ a i) * ∏ i, coeff (ν i) (hat ι (C ω * logS) (f j i) ^ a i) := by
  have h0 : constantCoeff (C ω * logS : ℂ_[q]⟦X⟧) = 0 := by
    rw [map_mul, ← coeff_zero_eq_constantCoeff_apply logS]; simp [logS]
  obtain ⟨H1, H2, -⟩ := GlobalTheory.T.cpTransportedTaylorSeriesInChart_ringHom_laws q ι _ h0
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_prod, mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [(H1 (fun _ => ρ j i) (f j i) analyticAt_const ((hf j i).analyticAt 0)).2.1, H2, mul_pow,
    ← map_pow (C : ℂ_[q] →+* ℂ_[q]⟦X⟧), coeff_C_mul, map_pow ι]

theorem comb_translate {d : ℕ} (hd : 0 < d) {g m : ℕ} (a : Fin g → ℕ) (c : Fin m → ℂ) (t : Fin m → Fin g → ℂ)
    (τ y : Fin g → ℂ) (θ : ℂ → ℂ) :
    (fun z : Fin g → ℂ => ∑ j, c j * ∏ i, W1 d (y i) (U1 d (τ i) (U1 d (t j i) θ)) (z i) ^ a i) =
      fun z => ∑ j, (c j * ∏ i, rho d (τ i) (t j i) ^ a i) * ∏ i, W1 d (y i) (U1 d (τ i + t j i) θ) (z i) ^ a i := by
  funext z
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [thetaTranslation_comp_eq_cocycle_mul hd, cmLatticeWeylOperator_const_mul, mul_pow]

theorem product_measures (d : ℕ) (ι : ℂ ≃+* ℂ_[q]) (δ : ℂ) (Ω : ℂ_[q]) (θ : ℂ → ℂ) (hd : 0 < d) (hδ : δ ≠ 0)
    (hΩ : Ω ≠ 0) (hθ : Differentiable ℂ θ) (hL : ThetaLaws ι d (Ω / ι δ) θ) {g m : ℕ} (a : Fin g → ℕ)
    (c : Fin m → ℂ) (t : Fin m → Fin g → ℂ) (ht : ∀ j i, PrimeTo d q (t j i)) :
    ∃ N : ℝ, ∀ τ : Fin g → ℂ, (∀ i, PrimeTo d q (τ i)) →
      ∃ μ : C(Fin g → ℤ_[q], ℂ_[q]) →L[ℂ_[q]] ℂ_[q], ‖μ‖ = N ∧
        ∀ (n s : ℕ) (y : Fin g → ℂ), Nat.Coprime s q → (∀ j i, InOK d ((s : ℂ) * (τ i + t j i))) →
          (∀ i, Good ι d n s (y i)) → ∀ (k : ℕ) (ys : Fin k → Fin g → ℂ) (F : C(Fin g → ℤ_[q], ℂ_[q])),
          (∀ A, F A = (∏ i, ι (kap1 d 1 (y i)) ^ (PadicInt.toZModPow n (A i)).val) *
            ∏ l, (Ω⁻¹ * ∑ i, ι (ys l i) * GlobalTheory.MomOne.zc (A i))) →
          ι (iteratedFDeriv ℂ k (fun z : Fin g → ℂ =>
            ∑ j, c j * ∏ i, W1 d (y i) (U1 d (τ i) (U1 d (t j i) θ)) (z i) ^ a i) 0 (fun l => δ⁻¹ • ys l)) = μ F := by
  have hU : ∀ x F, Differentiable ℂ F → Differentiable ℂ (U1 d x F) := fun x F h =>
    ((GlobalTheory.T.cmLattice_heisenberg_relations_one_variable d hd).2.2.1 x F h).1
  obtain ⟨μ₀, h₀, -⟩ := ProdMeasure.measure_of_products d q ι δ Ω θ hd hδ hΩ hθ hL g m a c t ht
  refine ⟨‖μ₀‖, fun τ hτ => ?_⟩
  have ht' : ∀ j i, PrimeTo d q (τ i + t j i) := fun j i => primeTo_add (hτ i) (ht j i)
  obtain ⟨μ, h₁, h₂⟩ := ProdMeasure.measure_of_products d q ι δ Ω θ hd hδ hΩ hθ hL g m a
    (fun j => c j * ∏ i, rho d (τ i) (t j i) ^ a i) (fun j i => τ i + t j i) ht'
  refine ⟨μ, le_antisymm ?_ ?_, fun n s y hs hst hy k ys F hF => ?_⟩
  · refine (h₁ _ (norm_nonneg _)).2 fun ν => ?_
    have := translate_norm_prod_le d q ι _ θ hL g m a (fun j => ι (c j)) t τ _ ht hτ
      ((h₀ _ (norm_nonneg _)).1 le_rfl) ν
    simp only [thetaTranslation_comp_eq_cocycle_mul hd] at this
    rwa [family_scale ι _ a c (fun j i => rho d (τ i) (t j i)) (fun j i => U1 d (τ i + t j i) θ)
      (fun j i => hU _ _ hθ)] at this
  · refine (h₀ _ (norm_nonneg _)).2 fun ν => ?_
    have := translate_norm_prod_le d q ι _ θ hL g m a _ (fun j i => τ i + t j i) (fun i => -τ i) _ ht'
      (fun i => primeTo_neg (hτ i)) ((h₁ _ (norm_nonneg _)).1 le_rfl) ν
    rw [← family_scale ι _ a c (fun j i => rho d (τ i) (t j i)) (fun j i => U1 d (-τ i) (U1 d (τ i + t j i) θ))
      (fun j i => hU _ _ (hU _ _ hθ))] at this
    simpa only [← cmLatticeTranslationOperator_eq_phase_mul_neg_comp hd] using this
  · rw [comb_translate hd]
    exact h₂ n s y hs hst hy k ys F hF

theorem product_algebraic (d : ℕ) (ι : ℂ ≃+* ℂ_[q]) (δ : ℂ) (θ : ℂ → ℂ) (hp : d.Prime) (h7 : d % 16 = 7)
    (hS : Split d q) (hθ : IsTh d θ) (hδ : δ ≠ 0)
    (hL : ∀ ι' : ℂ ≃+* ℂ_[q], ∃ Ω' : ℂ_[q], ‖Ω'‖ = 1 ∧ ThetaLaws ι' d (Ω' / ι' δ) θ) {g m : ℕ} (a : Fin g → ℕ)
    (c : Fin m → ℂ) (hc : ∀ j, c j ∈ algebraicClosure ℚ ℂ) (t : Fin m → Fin g → ℂ) (ht : ∀ j i, PrimeTo d q (t j i))
    (τ : Fin g → ℂ) (hτ : ∀ i, PrimeTo d q (τ i)) (n s : ℕ) (y : Fin g → ℂ) (hs : Nat.Coprime s q)
    (hst : ∀ j i, InOK d ((s : ℂ) * (τ i + t j i))) (hy : ∀ i, Good ι d n s (y i)) (k : ℕ)
    (ys : Fin k → Fin g → ℂ) (hys : ∀ l i, ys l i ∈ algebraicClosure ℚ ℂ) :
    iteratedFDeriv ℂ k (fun z : Fin g → ℂ =>
      ∑ j, c j * ∏ i, W1 d (y i) (U1 d (τ i) (U1 d (t j i) θ)) (z i) ^ a i) 0 (fun l => δ⁻¹ • ys l)
      ∈ algebraicClosure ℚ ℂ := by
  have hd := hp.pos
  have H := (GlobalTheory.T.cmLattice_heisenberg_relations_one_variable d hd).2.2.1
  rw [comb_translate hd]
  refine GlobalTheory.AlgJetComb.iteratedFDeriv_comb_mem g m k δ a _ (fun j i => W1 d (y i) (U1 d (τ i + t j i) θ)) ys
    (fun j i => (H _ _ (H _ _ hθ.1).1).2)
    (fun j i k' => jets_algebraic d q δ θ hp h7 hS hθ hδ hL ι _ _ n s k' hs (hst j i) (hy i)) (fun j => ?_) hys
  refine mul_mem (hc j) (prod_mem fun i _ => pow_mem ?_ _)
  exact rho_mem (GlobalTheory.T.imagQuadraticMaximalOrder_arithmetic_at_split_prime d q ι hp h7 hS).2.2.2.2.2.1 (hτ i) (ht j i)

theorem beta_sum_left {g : ℕ} (d : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) {I : Type} [Fintype I] (c : I → ℂ)
    (u : I → Fin g → ℂ) (w : Fin g → ℂ) : beta d Hm (∑ k, c k • u k) w = ∑ k, c k * beta d Hm (u k) w := by
  simp only [beta, hf, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

theorem beta_smul_left {g : ℕ} (d : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (c : ℂ)
    (u w : Fin g → ℂ) : beta d Hm (c • u) w = c * beta d Hm u w := by
  simp only [beta, hf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem good_zero (ι : ℂ ≃+* ℂ_[q]) (d s : ℕ) : Good ι d 0 s 0 :=
  ⟨0, ⟨0, 0, by simp⟩, by simp, by simp⟩

theorem cmLatticeWeylOperator_zero {d : ℕ} (hd : 0 < d) (F : ℂ → ℂ) : W1 d 0 F = F := by
  funext z; simp [W1, (GlobalTheory.T.cmLattice_heisenberg_relations_one_variable d hd).2.1]

theorem lamA_eq (lam : Qbar →+* ℂ_[q]) (ι : ℂ ≃+* ℂ_[q]) (h : ∀ z : Qbar, ι (z : ℂ) = lam z) {z : ℂ}
    (hz : z ∈ Qbar) : lamA lam z = ι z := by
  rw [lamA, dite_eq_left hz]; exact (h ⟨z, hz⟩).symm

theorem contDiff_opU {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (x : Fin g → ℂ) {F : (Fin g → ℂ) → ℂ}
    (hF : ContDiff ℂ ⊤ F) : ContDiff ℂ ⊤ (opU Hm x F) := by
  unfold opU hf
  fun_prop

theorem contDiff_opW {g : ℕ} (d : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (x : Fin g → ℂ) {F : (Fin g → ℂ) → ℂ}
    (hF : ContDiff ℂ ⊤ F) : ContDiff ℂ ⊤ (opW d Hm x F) := by
  have := contDiff_opU Hm x hF
  unfold opW
  fun_prop

theorem theta_in_frame (ι : ℂ ≃+* ℂ_[q]) (δ : ℂ) (θ : ℂ → ℂ) {g : ℕ} (S : Setup g) (hO : S.Ok)
    (hS : Split S.d q) (hθ : IsTh S.d θ) (hδ : δ ≠ 0)
    (hL : ∀ ι' : ℂ ≃+* ℂ_[q], ∃ Ω' : ℂ_[q], ‖Ω'‖ = 1 ∧ ThetaLaws ι' S.d (Ω' / ι' δ) θ)
    (x : Fin g → Fin g → ℂ) (a : Fin g → ℕ) (hx : ∀ i, x i ∈ S.La)
    (hxx : ∀ i j, beta S.d S.Hm (x i) (x j) = if i = j then (a i : ℂ) else 0)
    (ha : ∀ i, 0 < a i ∧ Nat.Coprime (a i) q) (e : (Fin g → ℂ) → ℂ) (he : S.IsTheta e) (hj : S.AlgJets δ e) :
    ∃ (m : ℕ) (r : Fin m → ℂ) (t : Fin m → Fin g → ℂ), (∀ j, r j ∈ Qbar) ∧ (∀ j i, PrimeTo S.d q (t j i)) ∧
      ∀ z : Fin g → ℂ, e (∑ i, z i • x i) = ∑ j, r j * ∏ i, U1 S.d (t j i) θ (z i) ^ a i := by
  have hd := hO.1.pos
  obtain ⟨m, r, t, Θ, hΘ, hne, hr, ht, hz⟩ := GlobalTheory.T.exists_cmTheta_eq_sum_prod_translates q g S x a θ Fact.out hO hx hxx ha hθ
  obtain ⟨c, rfl⟩ := GlobalTheory.T.theta_vectors_setup_exists_eq_smul g S e Θ hO he hΘ hne
  obtain ⟨C1, -, -, C4⟩ := GlobalTheory.T.heisenbergOperators_orthogonalFrame_coords g S x a hd hxx fun i => (ha i).1
  have hc : c ∈ Qbar := by
    by_contra hc
    have hΦ : ContDiff ℂ ⊤ (fun z : Fin g → ℂ => Θ (∑ i, z i • x i)) := hΘ.1.comp (by fun_prop)
    have h0 := eq_zero_of_jets _ hΦ δ hδ fun k σ => by
      obtain ⟨s, hs, hst⟩ := primeTo_common (d := S.d) (q := q) (fun p : Fin m × Fin g => t p.1 p.2)
        fun p => ht _ _
      have h1 := product_algebraic S.d ι δ θ hO.1 hO.2.1 hS hθ hδ hL a r hr t ht 0
        (fun i => ⟨1, one_pos, Nat.coprime_one_left _, 0, 0, by simp⟩) 0 s 0 hs
        (fun j i => by simpa using hst (j, i)) (fun i => good_zero ι _ _) k (fun l => Pi.single (σ l) 1)
        (fun l i => by
          rw [Pi.single_apply]; split_ifs
          exacts [one_mem _, zero_mem _])
      simp only [Pi.zero_apply, cmLatticeWeylOperator_zero hd, (GlobalTheory.T.cmLattice_heisenberg_relations_one_variable S.d hd).2.1, ← hz] at h1
      have h2 := hj k (fun l => x (σ l)) fun l => ⟨1, one_pos, by simpa using hx _⟩
      have e1 : (fun l => δ⁻¹ • x (σ l)) =
          fun l => ∑ i, (δ⁻¹ • (Pi.single (σ l) 1 : Fin g → ℂ)) i • x i := by
        funext l; simp [Pi.single_apply, ite_smul]
      rw [e1, C4 _ he.1] at h2
      have e2 : (fun z : Fin g → ℂ => (c • Θ) (∑ i, z i • x i)) = c • fun z : Fin g → ℂ => Θ (∑ i, z i • x i) := rfl
      rw [e2, iteratedFDeriv_const_smul_apply (hΦ.of_le le_top).contDiffAt, smul_apply, smul_eq_mul] at h2
      by_contra hn
      apply hc
      have := div_mem h2 h1
      rwa [mul_div_cancel_right₀ _ hn] at this
    apply hne
    funext v
    have := congrFun h0 fun i => beta S.d S.Hm v (x i) / (a i : ℂ)
    rw [C1 v]; exact this
  refine ⟨m, fun j => c * r j, t, fun j => mul_mem hc (hr j), ht, fun z => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, hz, Finset.mul_sum, mul_assoc]

theorem moments_of_translates : ∀ (d q : ℕ) [Fact q.Prime] (lam : Qbar →+* ℂ_[q]) (δ : ℂ) (θ : ℂ → ℂ) (ι : ℂ ≃+* ℂ_[q]) (Ω : ℂ_[q]), d.Prime → d % 16 = 7 → Split d q → IsTh d θ → δ ≠ 0 → (∀ ι' : ℂ ≃+* ℂ_[q], ∃ Ω' : ℂ_[q], ‖Ω'‖ = 1 ∧ ThetaLaws ι' d (Ω' / ι' δ) θ) → (∀ z : Qbar, ι (z : ℂ) = lam z) → ‖Ω‖ = 1 → ThetaLaws ι d (Ω / ι δ) θ → ∀ (g : ℕ) (S : Setup g), S.d = d → S.Ok → ∀ (r : ℕ) (b : Fin r → Fin g → ℂ), S.NNBasis q b → ∀ e : (Fin g → ℂ) → ℂ, S.IsTheta e → S.AlgJets δ e → ∃ N : ℝ, ∀ t : Fin g → ℂ, S.PrimeTo q t → ∃ μ : C(Fin r → ℤ_[q], ℂ_[q]) →L[ℂ_[q]] ℂ_[q], ‖μ‖ = N ∧ MomentProperty lam Ω δ S b (fun _ : Fin 1 => t) μ (opU S.Hm t e) := by
  intro d q _ lam δ θ ι Ω hp h7 hS hθ hδ hL hlam hΩ hL0 g S hSd hO r b hb e he hj
  subst hSd
  have hd := hp.pos
  have hq : q.Prime := Fact.out
  obtain ⟨-, K2, -, -, -, -, K7⟩ := GlobalTheory.T.imagQuadraticMaximalOrder_arithmetic_at_split_prime S.d q ι hp h7 hS
  obtain ⟨x, a, hx, hxx, ha⟩ := GlobalTheory.T.exists_orthogonal_frame_norms_coprime_of_unimodular q g S hq hO K7
  obtain ⟨m, c, t, hc, ht, hz⟩ := theta_in_frame ι δ θ S hO hS hθ hδ hL x a hx hxx ha e he hj
  obtain ⟨C1, -, C3, C4⟩ := GlobalTheory.T.heisenbergOperators_orthogonalFrame_coords g S x a hd hxx fun i => (ha i).1
  obtain ⟨T, hT⟩ := GlobalTheory.T.exists_padicInt_frame_change_etale_basis q ι g S x a r b hO hS hx hxx ha hb
  have hΩ0 : Ω ≠ 0 := by rintro rfl; simp at hΩ
  obtain ⟨N, hN⟩ := product_measures S.d ι δ Ω θ hd hδ hΩ0 hθ.1 hL0 a c t ht
  have hβ : ∀ u ∈ S.La, ∀ v ∈ S.La, InOK S.d (beta S.d S.Hm u v) := hO.2.2.2.2.2.2.1
  have hβ' : ∀ v, S.AlgDir v → ∀ w ∈ S.La, beta S.d S.Hm v w ∈ Qbar := by
    rintro v ⟨s, cc, u, hcc, hu, rfl⟩ w hw
    rw [beta_sum_left]
    exact sum_mem fun k _ => mul_mem (hcc k) (K2 _ (hβ _ (hu k) _ hw)).2.2
  refine ⟨N, fun t₀ ht₀ => ?_⟩
  set τ : Fin g → ℂ := fun i => beta S.d S.Hm t₀ (x i) / (a i : ℂ) with hτd
  have hτ : ∀ i, PrimeTo S.d q (τ i) := by
    obtain ⟨s, hs, hsq, hst⟩ := ht₀
    intro i
    have h1 := hβ _ hst _ (hx i)
    have h2 : (a i : ℂ) ≠ 0 := by exact_mod_cast (ha i).1.ne'
    refine ⟨s * a i, Nat.mul_pos hs (ha i).1, Nat.Coprime.mul_left hsq (ha i).2, ?_⟩
    rw [beta_smul_left] at h1
    convert h1 using 1
    simp only [hτd]; push_cast; field_simp
  obtain ⟨μ, hμ, hM⟩ := hN τ hτ
  refine ⟨μ.comp (compIso (K := ℂ_[q]) T).toLinearIsometry.toContinuousLinearMap, ?_, ?_⟩
  · rw [← hμ]; exact μ.opNorm_comp_linearIsometryEquiv (compIso T)
  intro n m' eps hI hnm hint y k ys hys f hf
  obtain ⟨s₀, hs₀, hst⟩ := primeTo_common (d := S.d) (q := q) (fun p : Fin m × Fin g => τ p.2 + t p.1 p.2)
    fun p => primeTo_add (hτ _) (ht _ _)
  have hcop : Nat.Coprime (s₀ * ∏ i, a i) (q ^ n) :=
    (Nat.Coprime.mul_left hs₀ (Nat.Coprime.prod_left fun i _ => (ha i).2)).pow_right n
  set s := (s₀ * ∏ i, a i) ^ Nat.totient (q ^ n) with hsd
  have hs1 : s ≡ 1 [MOD q ^ n] := Nat.ModEq.pow_totient hcop
  have hs2 : (s₀ * ∏ i, a i) ∣ s := dvd_pow_self _ (Nat.totient_pos.2 (pow_pos hq.pos n)).ne'
  obtain ⟨L1, L2⟩ := GlobalTheory.T.cmThetaOperator_invariant_of_lift_congr_one q lam g S r b e t₀ n m' s eps y hO hb.1 he hI hnm (hint 0) hs1
  obtain ⟨G1, G2⟩ := GlobalTheory.T.torsion_lift_pairing_in_orthogonal_frame q lam ι g S x a r b n m' s s₀ eps y hlam hO hS hx hxx ha hb.1 hI hnm hs2
  set y' : Fin g → ℂ := fun i => beta S.d S.Hm ((s : ℂ) • liftY q n eps b y) (x i) / (a i : ℂ) with hy'
  set yc : Fin k → Fin g → ℂ := fun l i => beta S.d S.Hm (ys l) (x i) / (a i : ℂ) with hyc
  have hyc' : ∀ l i, yc l i ∈ Qbar := fun l i => div_mem (hβ' _ (hys l) _ (hx i)) (natCast_mem _ _)
  have e1 : (fun l => δ⁻¹ • ys l) = fun l => ∑ i, (δ⁻¹ • yc l) i • x i := by
    funext l
    conv_lhs => rw [C1 (ys l)]
    simp only [Finset.smul_sum, smul_smul, Pi.smul_apply, smul_eq_mul, hyc]
  have e2 : (fun z : Fin g → ℂ => opW S.d S.Hm ((s : ℂ) • liftY q n eps b y) (opU S.Hm t₀ e) (∑ i, z i • x i)) =
      fun z => ∑ j, c j * ∏ i, W1 S.d (y' i) (U1 S.d (τ i) (U1 S.d (t j i) θ)) (z i) ^ a i := by
    funext z
    rw [C1 ((s : ℂ) • liftY q n eps b y), C1 t₀]
    exact (C3 m c (fun j i => U1 S.d (τ i) (U1 S.d (t j i) θ)) _
      (fun z => (C3 m c (fun j i => U1 S.d (t j i) θ) e hz τ z).1) y' z).2
  rw [← L1, e1, C4 _ (contDiff_opW _ _ _ (contDiff_opU _ _ he.1)), e2]
  have halg := product_algebraic S.d ι δ θ hp h7 hS hθ hδ hL a c hc t ht τ hτ n s₀ y' hs₀
    (fun j i => hst (j, i)) G1 k yc hyc'
  refine ⟨halg, ?_⟩
  rw [lamA_eq lam ι hlam halg]
  refine hM n s₀ y' hs₀ (fun j i => hst (j, i)) G1 k yc (compIso T f) fun A' => ?_
  obtain ⟨A, rfl⟩ := T.surjective A'
  have e3 : compIso (K := ℂ_[q]) T f (T A) = f A := by
    show f (T.symm (T A)) = f A
    rw [T.symm_apply_apply]
  have hv : vecA n b A ∈ S.La := sum_mem fun i _ => by
    rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem (hb.1 i) _
  obtain ⟨G3, G4⟩ := G2 A (T A) (hT A)
  rw [e3, hf, ← L2 _ hv, lamA_eq lam ι hlam G3, G4]
  congr 1
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [pairD]
  congr 1
  simp only [hT, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [lamA_eq lam ι hlam (hβ' _ (hys l) _ (hb.1 j))]
  set_option synthInstance.maxHeartbeats 100000 in
    conv_lhs => rw [C1 (ys l), beta_sum_left, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul]
  show GlobalTheory.MomOne.zc (A j) * (ι (yc l i) * _) = _
  ring

end GlobalTheory.MomOne.Translates
