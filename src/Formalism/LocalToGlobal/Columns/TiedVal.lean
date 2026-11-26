module

public import Formalism.LocalToGlobal.Columns.TiedCls
public import Formalism.LocalToGlobal.HermitianForms.TiedTwGen

@[expose] public section

section -- merged from Formalism.LocalToGlobal.Columns.TiedVal
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def RatSpanG {K : Type} [Field K] (s : K →+* ℂ) {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) :
    AddSubgroup (MvPolynomial (ι × Fin n × Fin n) ℂ) :=
  AddSubgroup.closure {p | ∃ (r : K) (f : ι → MvPolynomial (Fin n × Fin n) ℤ),
    (∀ τ, f τ ∈ delSq ℤ n (lam τ)) ∧
    p = s r • Formalism.L2.Forms.ten (fun τ => MvPolynomial.map (Int.castRingHom ℂ) (f τ))}

section Gen

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)

theorem lamTrue_eq_shW (u : Pr.Word) (i : ℕ) :
    W.lamTrue u i = fun τ => shW (W.lamN u i τ) ((i * (R.t + 1) / 2 : ℕ) : ℤ) := by
  funext τ
  have h : ((i * (R.t + 1) / 2 : ℕ) : ℤ) = (i : ℤ) * (((R.t + 1) / 2 : ℕ) : ℤ) := by
    obtain ⟨b, hb⟩ := R.t_odd
    have h2 : R.t + 1 = 2 * (b + 1) := by omega
    rw [h2, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2), Nat.mul_left_comm, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
    push_cast
    ring
  unfold Wts.lamTrue shiftW shW
  congr 1
  funext x
  rw [h]
  ring

end Gen

section Rec

variable {d : ColDat} (a : ColArgs d)

theorem lamT_eq (u : d.what₂.Word) (i : ℕ) : CF.lamT (D := d.colRec a) u i = d.W.lamTrue u i :=
  (lamTrue_eq_shW (Pr := d.Pr) d.W u i).symm

end Rec

end Formalism.L2.Col
end
end

section -- merged from Formalism.LocalToGlobal.Columns.TiedAtT
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {X : Fields} {Pr : Primes X} (hc : CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word)

include hPr in
theorem att_T_mem_under (P : {P // P ∈ Pr.vT u}) : (Pr.T u : 𝓞 X.F) ∈ (underPl X.F P.1).asIdeal := by
  show (Pr.T u : 𝓞 X.F) ∈ P.1.asIdeal.comap (algebraMap (𝓞 X.F) (𝓞 X.E))
  rw [Ideal.mem_comap, map_natCast]
  exact T_mem hPr u P

def tieEV : {P // P ∈ Pr.vT u} ≃ {v : HeightOneSpectrum (𝓞 X.F) // (Pr.T u : 𝓞 X.F) ∈ v.asIdeal} :=
  Equiv.ofBijective (fun P => ⟨underPl X.F P.1, att_T_mem_under hPr u P⟩) (by
    constructor
    · intro P Q h
      have h1 : underPl X.F P.1 = underPl X.F Q.1 := congrArg Subtype.val h
      have hP : IsOver (underPl X.F P.1) P.1 := rfl
      have hQ : IsOver (underPl X.F P.1) Q.1 := by rw [h1]; rfl
      exact Subtype.ext ((basePi_of_ok hX hPr u).over_unique hc P.2 hP Q.1 Q.2 hQ).symm
    · rintro ⟨v, hv⟩
      obtain ⟨P, hP, hov⟩ := (mem_plUnder_iff_norm hc (rls_vT_iff hX hPr u) (Pr.T u) (hPr.piT_norm u) v).2 hv
      exact ⟨⟨P, hP⟩, Subtype.ext (HeightOneSpectrum.ext hov.symm)⟩)

end Gen

section Val

variable {K : Type} [Field K] [NumberField K] (Pl : Rows.Places K) (pw : Pl.Pl → HeightOneSpectrum (𝓞 K))
  (hval : ∀ w (x : K), x ≠ 0 → Pl.val w x = ((vAdd (pw w) x : ℤ) : WithTop ℤ))


include hval in
theorem att_val_pos (w : Pl.Pl) (x : 𝓞 K) : (0 : WithTop ℤ) < Pl.val w (x : K) ↔ x ∈ (pw w).asIdeal := by
  by_cases hx : x = 0
  · subst hx
    have h0 : Pl.val w (((0 : 𝓞 K) : 𝓞 K) : K) = ⊤ := by
      rw [show (((0 : 𝓞 K) : 𝓞 K) : K) = 0 from rfl]
      exact (Pl.val w).map_zero
    rw [h0]
    exact ⟨fun _ => zero_mem _, fun _ => WithTop.coe_lt_top (0 : ℤ)⟩
  · have hx' : (x : K) ≠ 0 := fun h => hx (RingOfIntegers.ext h)
    have h0 : (pw w).valuation K (x : K) ≠ 0 := (Valuation.ne_zero_iff _).2 hx'
    rw [hval w _ hx', ← (pw w).valuation_lt_one_iff_mem (K := K)]
    unfold Formalism.BasicNotions.vAdd
    rw [← WithTop.coe_zero, WithTop.coe_lt_coe, neg_pos, ← WithZero.log_one, WithZero.log_lt_log h0 one_ne_zero]


include hval in
theorem att_resChar_mem (w : Pl.Pl) : ((Pl.resChar w : ℕ) : 𝓞 K) ∈ (pw w).asIdeal := by
  rw [← att_val_pos Pl pw hval]
  have h := Pl.val_resChar w
  have e : ((((Pl.resChar w : ℕ) : 𝓞 K) : 𝓞 K) : K) = ((Pl.resChar w : ℕ) : K) := map_natCast (algebraMap (𝓞 K) K) _
  rw [e, h, ← WithTop.coe_zero, WithTop.coe_lt_coe]
  exact_mod_cast Pl.ramIdx_pos w

end Val

section Seen

variable {X : Fields} {Pr : Primes X} (hc : CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word)


include hc in
theorem att_mem_conjP (P : Pl X.E) (x : 𝓞 X.F) :
    algebraMap (𝓞 X.F) (𝓞 X.E) x ∈ (conjPrime₂ P).asIdeal ↔ algebraMap (𝓞 X.F) (𝓞 X.E) x ∈ P.asIdeal := by
  rw [mem_conjP, rll_cO_algebraMap hc]

theorem att_tauOf (w : HeightOneSpectrum (𝓞 X.K)) (hw : (Pr.T u : 𝓞 X.K) ∈ w.asIdeal) (P : {P // P ∈ Pr.vT u}) (x : 𝓞 X.F) :
    x ∈ (tieEV hc hX hPr u P).1.asIdeal ↔ X.embO (tauOfR hX hPr u w P) (algebraMap (𝓞 X.F) (𝓞 X.E) x) ∈ w.asIdeal := by
  have := hX.nonempty_Tau
  have e : tauOfR hX hPr u w P = tauOfC w P.1 := by
    unfold tauOfR
    rw [dite_eq_left hw]
    rfl
  rw [e, ← mem_pullW]
  show algebraMap (𝓞 X.F) (𝓞 X.E) x ∈ P.1.asIdeal ↔ _
  rcases tauOfC_spec hX hPr u w hw P with h | h
  · rw [show pullW (tauOfC w P.1) w = P.1 from h]
  · rw [show pullW (tauOfC w P.1) w = conjPrime₂ P.1 from h, att_mem_conjP hc]


end Seen

section Rec

variable {d : ColDat} (a : ColArgs d)

theorem att_star_eq (x : d.host.E) : star x = d.host.conj x := Formalism.BasicNotions.Examples₂.star_eq_conj d.host x


set_option maxHeartbeats 1000000 in
def atTTied (hH : HostHyp d) (u : d.what₂.Word) : CF.AtTTied (D := d.colRec a) u where
  eV := tieEV d.sp.cm d.hX d.hPr u
  piU := d.piT u
  piU_K := hH.piT_K u
  piU_norm := by
    have h := congrArg (algebraMap (𝓞 d.host.E) d.host.E) (d.hPr.piT_norm u)
    rw [map_mul, map_natCast] at h
    rw [← att_star_eq]
    exact h
  piU_cong := by
    rw [Ideal.mem_span_singleton]
    have h := d.hPr.piT_cong u
    have e : d.Pr.cond = d.host.QS * d.host.q * d.host.d := hH.cond_eq
    rw [e] at h
    exact h
  res := fun v => Ideal.Quotient.mk v.1.asIdeal
  res_surj := fun v => Ideal.Quotient.mk_surjective
  res_pi := fun v => Ideal.Quotient.eq_zero_iff_mem.2 ((rls_vT_iff d.hX d.hPr u v.1).1 v.2)
  res_conj := fun v pb hpb h => by
    have h1 : pb = cO d.X.E (d.Pr.piT u) := by
      apply RingOfIntegers.ext
      change algebraMap (𝓞 d.X.E) d.X.E pb = algebraMap (𝓞 d.X.E) d.X.E (cO d.X.E (d.Pr.piT u))
      rw [algebraMap_cO, att_star_eq (d := d)]
      exact hpb
    change Ideal.Quotient.mk v.1.asIdeal pb = 0 at h
    rw [h1] at h
    exact (basePi_of_ok d.hX d.hPr u).conj_notMem v.2 (Ideal.Quotient.eq_zero_iff_mem.mp h)
  res_v := fun v x => (Ideal.Quotient.eq_zero_iff_mem (I := v.1.asIdeal)).symm
  tauOf := fun w hw v x => by
    have hT : (d.Pr.T u : 𝓞 d.X.K) ∈ (d.plEq w).asIdeal := by
      have := att_resChar_mem d.what₂.places d.plEq hH.val_eq w
      rw [hw] at this
      exact this
    exact (att_tauOf d.sp.cm d.hX d.hPr u (d.plEq w) hT v x).trans (att_val_pos d.what₂.places d.plEq hH.val_eq w _).symm
  seenP := fun w hw τ => by
    have hT : (d.Pr.T u : 𝓞 d.X.K) ∈ (d.plEq w).asIdeal := by
      have := att_resChar_mem d.what₂.places d.plEq hH.val_eq w
      rw [hw] at this
      exact this
    have key : ∀ b : Bool, b = (open Classical in decide (seenC d.Pr u (d.plEq w))) →
        (0 : WithTop ℤ) < d.what₂.places.val w (d.embE (d.host.sigmaOf (d.eTau τ : d.R.GG)
          (if b = true then (d.piT u : d.host.E) else d.host.conj (d.piT u : d.host.E)))) := by
      intro b hb
      by_cases hs : seenC d.Pr u (d.plEq w)
      · have hb' : b = true := by rw [hb]; exact @decide_eq_true _ (Classical.propDecidable _) hs
        rw [if_pos hb']
        exact (att_val_pos d.what₂.places d.plEq hH.val_eq w (d.X.embO τ (d.Pr.piT u))).2 (hs τ)
      · have hb' : ¬ b = true := by rw [hb]; simpa using hs
        rw [if_neg hb', ← att_star_eq]
        exact (att_val_pos d.what₂.places d.plEq hH.val_eq w (d.X.embO τ (d.X.conjO (d.Pr.piT u)))).2
          (((seenC_or_seenBarC d.hX d.hPr u (d.plEq w) hT).resolve_left hs) τ)
    exact key _ rfl

end Rec

end Formalism.L2.Col
end
end

section -- merged from Formalism.LocalToGlobal.Columns.TwQCmp
section -- merged from Formalism.LocalToGlobal.Columns.TwQSplit
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.UG Formalism.L2.DIV

section Split

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E)

theorem qsp_exists_pi (P : Pl E) (hP : conjPrime₂ P ≠ P) : ∃ ϖ : 𝓞 E, ϖ ∈ P.asIdeal ∧ cO E ϖ ∉ P.asIdeal := by
  obtain ⟨s, hs, hns⟩ := exists_mem_notMem (Ne.symm hP)
  exact ⟨s, hs, fun h => hns ((mem_conjP P s).2 h)⟩


include hc in
theorem qsp_norm_mem (a : 𝓞 E) : ∃ b : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) b = a * cO E a := by
  have h1 : star (algebraMap (𝓞 E) E (a * cO E a)) = algebraMap (𝓞 E) E (a * cO E a) := by
    rw [map_mul, algebraMap_cO, star_mul', star_star, mul_comm]
  obtain ⟨x, hx⟩ := (hc.fixed _).1 h1
  have hi : IsIntegral ℤ x := by
    have h2 : IsIntegral ℤ (algebraMap F E x) := by rw [hx]; exact RingOfIntegers.isIntegral_coe _
    exact (isIntegral_algebraMap_iff ).1 h2
  obtain ⟨b, hb⟩ : ∃ b : 𝓞 F, algebraMap (𝓞 F) F b = x := ⟨⟨x, hi⟩, rfl⟩
  refine ⟨b, ?_⟩
  apply RingOfIntegers.ext
  change algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) b) = algebraMap (𝓞 E) E (a * cO E a)
  rw [← hx, ← hb, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

theorem qsp_isOver (P : Pl E) : IsOver (underPl F P) P := rfl


include hc in
theorem qsp_exists (P : Pl E) (hP : conjPrime₂ P ≠ P) :
    ∃ ϖ : 𝓞 E, ϖ ∈ P.asIdeal ∧ cO E ϖ ∉ P.asIdeal ∧ Nonempty (Formalism.MainNotions.Gaps.LG.SplitAt hc.sig (underPl F P) (ϖ : E)) := by
  obtain ⟨ϖ, hϖ, hcϖ⟩ := qsp_exists_pi P hP
  obtain ⟨t, ht⟩ := gls_trace_mem hc ϖ
  obtain ⟨N, hN⟩ := qsp_norm_mem hc ϖ
  have hsig : ∀ x : E, hc.sig x = star x := fun _ => rfl
  have hsig0 : hc.sig (ϖ : E) = ((cO E ϖ : 𝓞 E) : E) := by rw [hsig]; exact (algebraMap_cO ϖ).symm
  have hN' : algebraMap F E (N : F) = (ϖ : E) * hc.sig (ϖ : E) := by
    have := congrArg (algebraMap (𝓞 E) E) hN
    rw [map_mul, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E] at this
    rw [hsig0]; exact this
  have ht' : algebraMap F E (t : F) = (ϖ : E) + hc.sig (ϖ : E) := by
    have := congrArg (algebraMap (𝓞 E) E) ht
    rw [map_add (f := _), ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E] at this
    rw [hsig0]; exact this
  have hNv : N ∈ (underPl F P).asIdeal := by
    show algebraMap (𝓞 F) (𝓞 E) N ∈ P.asIdeal
    rw [hN]; exact Ideal.mul_mem_right _ _ hϖ
  have htv : t ∉ (underPl F P).asIdeal := by
    intro h
    have h1 : algebraMap (𝓞 F) (𝓞 E) t ∈ P.asIdeal := h
    rw [ht] at h1
    exact hcϖ (by simpa using P.asIdeal.sub_mem h1 hϖ)
  obtain ⟨s⟩ := Formalism.MainNotions.Gaps.LG.sc_core hc.sig (fun x => by rw [hsig, hsig, star_star])
    (fun x hx => (hc.fixed x).1 hx) hc.deg2 (underPl F P) ϖ t N ht' hN' hNv htv
  have hN2 : ((cO E ϖ : 𝓞 E) : E) * hc.sig ((cO E ϖ : 𝓞 E) : E) = algebraMap F E (N : F) := by
    rw [hN', ← hsig0, mul_comm, hsig, hsig, star_star]
  obtain ⟨sa⟩ := Formalism.MainNotions.Gaps.LG.sc_orient s (cO E ϖ) N hNv hN2
  have e : hc.sig ((cO E ϖ : 𝓞 E) : E) = (ϖ : E) := by rw [← hsig0, hsig, hsig, star_star]
  exact ⟨ϖ, hϖ, hcϖ, ⟨e ▸ sa⟩⟩

end Split

end Formalism.L2.Col
end
end

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Col

section Cmp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : HeightOneSpectrum (𝓞 F)} (P : HeightOneSpectrum (𝓞 E)) (φ : E →+* v.adicCompletion F)
  (hint : ∀ r : 𝓞 E, Valued.v (φ (algebraMap (𝓞 E) E r)) ≤ 1)
  (hPv : ∀ r : 𝓞 E, Valued.v (φ (algebraMap (𝓞 E) E r)) < 1 ↔ r ∈ P.asIdeal)

include hint hPv in
theorem qsp_val_one (t : 𝓞 E) (ht : t ∉ P.asIdeal) : Valued.v (φ (algebraMap (𝓞 E) E t)) = 1 :=
  le_antisymm (hint t) (not_lt.1 fun h => ht ((hPv t).1 h))

theorem qsp_frac (x : E) (hx : P.valuation E x ≤ 1) :
    ∃ (a : 𝓞 E) (t : 𝓞 E), t ∉ P.asIdeal ∧ x * algebraMap (𝓞 E) E t = algebraMap (𝓞 E) E a := by
  obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 E)) x
  simp only at hnd
  have hd0 : (d : 𝓞 E) ≠ 0 := nonZeroDivisors.ne_zero d.2
  have hspan : Ideal.span {(d : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hd0
  have hPu : ¬ IsUnit P.asIdeal := by
    rw [Ideal.isUnit_iff]
    exact P.isPrime.ne_top
  obtain ⟨e, J, hPJ, hJ⟩ := WfDvdMonoid.max_power_factor' hspan hPu
  have hJP : ¬ J ≤ P.asIdeal := fun h => hPJ (Ideal.dvd_iff_le.2 h)
  obtain ⟨t, htJ, htP⟩ := SetLike.not_le_iff_exists.1 hJP
  have hvd : P.intValuation (d : 𝓞 E) ≤ WithZero.exp (-(e : ℤ)) := by
    rw [P.intValuation_le_pow_iff_dvd, hJ]
    exact dvd_mul_right _ _
  have hvn : P.intValuation n ≤ WithZero.exp (-(e : ℤ)) := by
    refine le_trans ?_ hvd
    rw [← HeightOneSpectrum.valuation_of_algebraMap (K := E),
      ← HeightOneSpectrum.valuation_of_algebraMap (K := E)]
    change P.valuation E (algebraMap (𝓞 E) E n) ≤ P.valuation E (algebraMap (𝓞 E) E (d : 𝓞 E))
    rw [← hnd, map_mul]
    exact mul_le_of_le_one_left' hx
  have hnt : n * t ∈ Ideal.span {(d : 𝓞 E)} := by
    rw [hJ]
    exact Ideal.mul_mem_mul ((P.intValuation_le_pow_iff_mem n e).1 hvn) htJ
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hnt
  refine ⟨a, t, htP, ?_⟩
  have hD : algebraMap (𝓞 E) E d ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).2 hd0
  have hat : algebraMap (𝓞 E) E a * algebraMap (𝓞 E) E d =
      algebraMap (𝓞 E) E n * algebraMap (𝓞 E) E t := by
    rw [← map_mul, ← map_mul, ha]
  apply mul_right_cancel₀ hD
  linear_combination (algebraMap (𝓞 E) E t) * hnd - hat


include hint hPv in
theorem qsp_le_of_val (x : E) (hx : P.valuation E x ≤ 1) : Valued.v (φ x) ≤ 1 := by
  obtain ⟨a, t, ht, hxt⟩ := qsp_frac P x hx
  have h1 := qsp_val_one P φ hint hPv t ht
  have h2 := hint a
  rw [← hxt, map_mul, Valuation.map_mul, h1, mul_one] at h2
  exact h2


include hint hPv in
theorem qsp_lt_of_val (x : E) (hx : P.valuation E x < 1) : Valued.v (φ x) < 1 := by
  obtain ⟨a, t, ht, hxt⟩ := qsp_frac P x hx.le
  have h1 := qsp_val_one P φ hint hPv t ht
  have ha : a ∈ P.asIdeal := by
    rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E)]
    change P.valuation E (algebraMap (𝓞 E) E a) < 1
    rw [← hxt, map_mul, (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := E) P).2 ht, mul_one]
    exact hx
  have h2 := (hPv a).2 ha
  rw [← hxt, map_mul, Valuation.map_mul, h1, mul_one] at h2
  exact h2


include hint hPv in
theorem qsp_val_iff (x : E) : Valued.v (φ x) ≤ 1 ↔ P.valuation E x ≤ 1 := by
  refine ⟨fun h => ?_, qsp_le_of_val P φ hint hPv x⟩
  by_contra hc
  rw [not_le] at hc
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hc
  have hinv : P.valuation E x⁻¹ < 1 := (Valuation.one_lt_val_iff _ hx0).1 hc
  have hlt := qsp_lt_of_val P φ hint hPv x⁻¹ hinv
  rw [map_inv₀] at hlt
  have hφ : φ x ≠ 0 := (map_ne_zero φ).2 hx0
  exact absurd h (not_le.2 ((Valuation.one_lt_val_iff _ hφ).2 hlt))


include hint hPv in
theorem qsp_mod (x d : E) (hd : d ≠ 0) (z : v.adicCompletion F) (hz : Valued.v z ≤ 1) (hxz : φ x = φ d * z) :
    P.valuation E x ≤ P.valuation E d := by
  have hφd : φ d ≠ 0 := (map_ne_zero φ).2 hd
  have h1 : φ (x / d) = z := by
    rw [map_div₀, hxz, mul_div_cancel_left₀ _ hφd]
  have h2 : P.valuation E (x / d) ≤ 1 := (qsp_val_iff P φ hint hPv _).1 (by rw [h1]; exact hz)
  have h3 : x = x / d * d := by rw [div_mul_cancel₀ _ hd]
  rw [h3, map_mul]
  exact mul_le_of_le_one_left' h2

end Cmp

end Formalism.L2.Col
end
end

section -- merged from Formalism.LocalToGlobal.Columns.TiedXp
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section GenP

variable {X : Fields} {Pr : Primes X} (hc : CMData X.F X.E) (σ₀ : X.K →+* ℂ) {n : ℕ} [NeZero n]
  (Λ : LevFam X.E X.K n Pr.vGs)

theorem xp_basePi_one : BasePi (∅ : Finset (Pl X.E)) (1 : 𝓞 X.E) :=
  ⟨fun r => ⟨fun _ => one_dvd r, fun _ P hP => absurd hP (Finset.notMem_empty P)⟩,
    isCoprime_one_left⟩

theorem xp_L_eq_N {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {SG : Finset (Pl E)}
    (d : Deco E n (∅ : Finset (Pl E)) SG) : d.L = d.N := by
  unfold Deco.L
  have : {x | x ∈ d.N ∧ ∀ P : (∅ : Finset (Pl E)), d.f P x = 0} = (d.N : Set (Sp E n)) := by
    ext x
    constructor
    · exact fun h => h.1
    · exact fun h => ⟨h, fun P => absurd P.2 (Finset.notMem_empty P.1)⟩
  rw [this, Submodule.span_eq]

def tieLevP : Formalism.L2.Forms.StepLevel X.F X.E hc.sig (1 : Matrix (Fin n) (Fin n) X.E) 1 X.f (plUnder X.F Pr.vGs) :=
  stepOf hc n (ST := ∅) (π := 1) (fun w => (Λ w).H) xp_basePi_one (by rw [map_one, mul_one, Nat.cast_one])
    (fun P => ⟨fun h => absurd h (Finset.notMem_empty P), fun h => absurd h (one_notMem P)⟩)
    (fun P hP => absurd hP (Finset.notMem_empty P))
    (fun v h => absurd (by rwa [Nat.cast_one] at h) ((Ideal.ne_top_iff_one _).1 v.isPrime.ne_top))
    (by rw [baseLb_index hc n ∅ (fun P => absurd P.2 (Finset.notMem_empty P.1))]; simp)
    ((Units.map σ₀.toMonoidHom).comp Λ.chr)

variable (s : DecoCl n (∅ : Finset (Pl X.E)) Pr.vGs Λ.grp → DecoSet (E := X.E) (n := n) (ST := ∅) (SG := Pr.vGs))

def clsPG₁ (hS : DecoPtSurj hc n (∅ : Finset (Pl X.E)) Pr.vGs) (hs : ∀ c, decoCls n ∅ Pr.vGs Λ.grp (s c) = c) :
    ClsG hc.sig (1 : Matrix (Fin n) (Fin n) X.E) 1 X.f (plUnder X.F Pr.vGs)
      (fun c => MulAction.stabilizer (UF X.E n × Λ.grp) (s c)) (fun c => (s c).1.N) where
  lev := tieLevP hc σ₀ Λ
  y := (recCls hc n ∅ Pr.vGs Λ.grp hS 1 s hs).y
  y_bij := (recCls hc n ∅ Pr.vGs Λ.grp hS 1 s hs).y_bij
  y_lat := fun c x => by
    have h := (recCls hc n ∅ Pr.vGs Λ.grp hS 1 s hs).y_lat c x
    rw [xp_L_eq_N] at h
    exact h
  stabI := (recCls hc n ∅ Pr.vGs Λ.grp hS 1 s hs).stabI
  stabI_inj := (recCls hc n ∅ Pr.vGs Λ.grp hS 1 s hs).stabI_inj
  stabI_range := fun c γ => (recCls hc n ∅ Pr.vGs Λ.grp hS 1 s hs).stabI_range c γ.1 γ.2

def clsPG (hS : DecoPtSurj hc n (∅ : Finset (Pl X.E)) Pr.vGs) (hs : ∀ c, decoCls n ∅ Pr.vGs Λ.grp (s c) = c)
    (Q : StepCrd Pr σ₀ n fun c => (s c).1.N) :
    ClsG hc.sig Q.J 1 Q.f Q.bad (fun c => MulAction.stabilizer (UF X.E n × Λ.grp) (s c)) Q.lat := by
  obtain ⟨J, f, bad, emb, lat, l0, rfl, rfl, rfl, rfl, rfl, rfl⟩ := Q
  exact clsPG₁ hc σ₀ Λ s hS hs

end GenP

section Rec

variable {d : ColDat}

abbrev PCl (d : ColDat) : Type := (ptGSD (Pr := d.Pr) d.W d.levP).Cl

def ColDat.reprP (d : ColDat) (c : PCl d) : DecoSet (E := d.X.E) (n := d.R.N d.R.m - 1) (ST := ∅) (SG := d.Pr.vGs) :=
  (ptGSD (Pr := d.Pr) d.W d.levP).outSec.rep c

def crdPr (a : ColArgs d) (hS : SpStd d.toColBase) (hH : HostHyp d) :
    StepCrd d.Pr d.σ₀ (d.R.N d.R.m - 1) fun c : PCl d => (d.reprP c).1.N where
  J := CF.gramP (d.colRec a)
  f := d.R.f
  bad := CF.badG (d.colRec a)
  emb := CF.embT (d.colRec a)
  lat := fun c => (d.reprP c).1.N
  l0 := stdLat d.X.E (d.R.N d.R.m - 1)
  hJ := gramP_eq a hS
  hf := d.f_eq.symm
  hbad := badG_eq a
  hemb := embT_eq a hH
  hlat := rfl
  hl0 := rfl

def PtSurjP (d : ColDat) : Prop := DecoPtSurj d.sp.cm (d.R.N d.R.m - 1) (∅ : Finset (Pl d.X.E)) d.Pr.vGs

def pClsG (a : ColArgs d) (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurjP d) :=
  clsPG d.sp.cm d.σ₀ d.levP.inv d.reprP hP (fun c => (ptGSD (Pr := d.Pr) d.W d.levP).outSec.spec c) (crdPr a hS hH)

def parabolicClassAgreement (a : ColArgs d) (hS : SpStd d.toColBase) (hH : HostHyp d)
    (hP : PtSurjP d) (u : d.what₂.Word) :
    CF.ClsPTied (D := d.colRec a) u where
  lev := (pClsG a hS hH hP).lev
  y := (pClsG a hS hH hP).y
  y_bij := (pClsG a hS hH hP).y_bij
  lat := fun c => (d.reprP c).1.N
  y_lat := (pClsG a hS hH hP).y_lat
  lat_fin := fun c => Module.Finite.iff_fg.2 (d.reprP c).2.lat.fg
  stabI := (pClsG a hS hH hP).stabI
  stabI_inj := (pClsG a hS hH hP).stabI_inj
  stabI_range := (pClsG a hS hH hP).stabI_range

end Rec

end Formalism.L2.Col
end
end

section -- merged from Formalism.LocalToGlobal.Columns.LocalLevelIsKOneAtT
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure HCrd {X : Fields} (Pr : Primes X) (n : ℕ) {cls : Type} (L : cls → Submodule (𝓞 X.E) (Fin n → X.E)) where
  n' : ℕ
  hn : n' = n
  J : Matrix (Fin n') (Fin n') X.E
  hJ : J = 1
  f : ℕ
  hf : f = X.f
  bad : Set (HeightOneSpectrum (𝓞 X.F))
  hbad : bad = plUnder X.F Pr.vGs
  lat : cls → Submodule (𝓞 X.E) (Fin n' → X.E)
  hlat : ∀ c, lat c = Formalism.L2.Forms.reL hn.symm (L c)

structure LevPack {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (gp : Fin 2 → ℕ) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) {cls : Type} (stab : cls → Type)
    [∀ c, Group (stab c)] (lat : cls → Submodule (𝓞 E) (Fin n → E)) where
  lev : Formalism.L2.Forms.StepLevel F E hc.sig J T f bad
  cls : RecCls hc J lev.Lb lev.U stab lat
  bad_iff : ∀ v : HeightOneSpectrum (𝓞 F), v ∈ bad ↔ ((gp 0 : 𝓞 F) ∈ v.asIdeal ∨ (gp 1 : 𝓞 F) ∈ v.asIdeal)
  Uloc_g : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal → ∀ x : GL (Fin n) (E ⊗[F] v.adicCompletion F),
    (x ∈ levelVL hc.sig J v lev.Lb ∧ ∀ y ∈ Formalism.L2.Herm.locL v lev.Lb, ∃ z ∈ Formalism.L2.Herm.locL v lev.Lb,
      (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y = (gp i : E ⊗[F] v.adicCompletion F) • z) → x ∈ lev.Uloc v
  UlocAlt : ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∈ v.asIdeal → ∀ x : GL (Fin n) (E ⊗[F] v.adicCompletion F), x ∈ lev.Uloc v ↔
    (x ∈ levelVL hc.sig J v lev.Lb ∧
      ∀ y ∈ Formalism.L2.Herm.locL v (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) J lev.Lb)),
        (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y ∈ Formalism.L2.Herm.locL v lev.Lb)

section Gen

variable {X : Fields} {Pr : Primes X} (hc : CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (σ₀ : X.K →+* ℂ) (u : Pr.Word)
  {n : ℕ} [NeZero n] (Λ : LevFam X.E X.K n Pr.vGs)

def LocalLevelIsKOneAtT : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 X.F), (Pr.T u : 𝓞 X.F) ∈ v.asIdeal → ∀ x : GL (Fin n) (X.E ⊗[X.F] v.adicCompletion X.F),
    x ∈ levLoc hc n (Pr.vT u) Pr.vGs Λ.grp v ↔
    (x ∈ levelVL hc.sig (1 : Matrix (Fin n) (Fin n) X.E) v (baseLb X.E n (Pr.vT u)) ∧
      ∀ y ∈ Formalism.L2.Herm.locL v (Submodule.span (𝓞 X.E)
          (dualSet (hc.sig : X.E →+* X.E) (1 : Matrix (Fin n) (Fin n) X.E) (baseLb X.E n (Pr.vT u)))),
        (x : Matrix (Fin n) (Fin n) (X.E ⊗[X.F] v.adicCompletion X.F)) *ᵥ y - y ∈ Formalism.L2.Herm.locL v (baseLb X.E n (Pr.vT u)))


include hc hPr in
theorem th_plUnder_vGs (v : HeightOneSpectrum (𝓞 X.F)) :
    v ∈ plUnder X.F Pr.vGs ↔ ((Pr.g 0 : 𝓞 X.F) ∈ v.asIdeal ∨ (Pr.g 1 : 𝓞 X.F) ∈ v.asIdeal) := by
  classical
  have key : ∀ (i : Fin 2), v ∈ plUnder X.F (Pr.vG i) ↔ (Pr.g i : 𝓞 X.F) ∈ v.asIdeal := by
    intro i
    have h0 : X.conjO (Pr.piG i) ≠ 0 := by
      intro h
      have h1 := hPr.piG_norm i
      rw [h, mul_zero] at h1
      exact (Nat.cast_ne_zero.2 (hPr.g_prime i).ne_zero) h1.symm
    refine mem_plUnder_iff_norm hc (fun P => mem_divs h0 P) (Pr.g i) ?_ v
    have h2 : cO X.E (X.conjO (Pr.piG i)) = Pr.piG i := cO_cO _
    rw [h2, mul_comm]
    exact hPr.piG_norm i
  rw [← key 0, ← key 1]
  constructor
  · rintro ⟨P, hP, h⟩
    rcases Finset.mem_union.1 hP with h' | h'
    · exact Or.inl ⟨P, h', h⟩
    · exact Or.inr ⟨P, h', h⟩
  · rintro (⟨P, hP, h⟩ | ⟨P, hP, h⟩)
    · exact ⟨P, Finset.mem_union_left _ hP, h⟩
    · exact ⟨P, Finset.mem_union_right _ hP, h⟩

variable (c₀ : DiaG (E := X.E) (ST := Pr.vT u)) (s : DecoCl n (Pr.vT u) Pr.vGs Λ.grp → DecoSet (E := X.E) (n := n) (ST := Pr.vT u) (SG := Pr.vGs))

def levPack₁ (hS : DecoPtSurj hc n (Pr.vT u) Pr.vGs) (hs : ∀ c, decoCls n (Pr.vT u) Pr.vGs Λ.grp (s c) = c)
    (hK : LocalLevelIsKOneAtT hc u Λ) :
    LevPack hc n (1 : Matrix (Fin n) (Fin n) X.E) Pr.g (Pr.T u) X.f (plUnder X.F Pr.vGs)
      (fun c => MulAction.stabilizer (UF X.E n × Λ.grp) (s c)) (fun c => (s c).1.L) where
  lev := tieLev hc hX hPr σ₀ u Λ
  cls := recCls hc n (Pr.vT u) Pr.vGs Λ.grp hS c₀ s hs
  bad_iff := th_plUnder_vGs hc hPr
  Uloc_g := fun i v hv x hx => by
    refine levLoc_of_princ hc n (Pr.vT u) Pr.vGs Λ.grp v (Pr.g i) ?_ ?_ x hx.1 hx.2
    · intro hT
      have h1 : (Pr.T u : 𝓞 X.F) ∈ v.asIdeal :=
        (mem_plUnder_iff_norm hc (rls_vT_iff hX hPr u) (Pr.T u) (hPr.piT_norm u) v).1 hT
      exact rls_T_notUnder hPr u v h1 ((th_plUnder_vGs hc hPr v).2 (by fin_cases i; exact Or.inl hv; exact Or.inr hv))
    · intro w _ hov
      have : (Pr.g i : 𝓞 X.F) ∈ w.asIdeal.comap (algebraMap (𝓞 X.F) (𝓞 X.E)) := hov ▸ hv
      rwa [Ideal.mem_comap, map_natCast] at this
  UlocAlt := hK

def levPack (hS : DecoPtSurj hc n (Pr.vT u) Pr.vGs) (hs : ∀ c, decoCls n (Pr.vT u) Pr.vGs Λ.grp (s c) = c)
    (hK : LocalLevelIsKOneAtT hc u Λ) (H : HCrd Pr n fun c => (s c).1.L) :
    LevPack hc H.n' H.J Pr.g (Pr.T u) H.f H.bad (fun c => MulAction.stabilizer (UF X.E n × Λ.grp) (s c)) H.lat := by
  obtain ⟨n', hn, J, rfl, f, rfl, bad, rfl, lat, hlat⟩ := H
  subst hn
  obtain rfl : lat = fun c => (s c).1.L := funext fun c => (hlat c).trans (Formalism.L2.Forms.reL_rfl _)
  exact levPack₁ hc hX hPr σ₀ u Λ c₀ s hS hs hK

end Gen

section Repack

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {hc : CMData F E}
  {S : HSpace E} {gp : Fin 2 → ℕ} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} {cls : Type} {stab : cls → Type}
  [∀ c, Group (stab c)] {lat : cls → Submodule (𝓞 E) S.V}

def LevPack.toStep (P : LevPack hc S.rank S.gram gp T f bad stab fun c => Formalism.L2.Herm.crdLat S (lat c)) :
    Formalism.L2.Herm.StepLevel hc S gp T f where
  Lb := P.lev.Lb
  Lb_fin := P.lev.Lb_fin
  Lb_span := P.lev.Lb_span
  Lb_int := fun x hx => Submodule.subset_span (P.lev.Lb_int x hx)
  Lb_dual := fun y hy => by
    refine Submodule.span_induction (p := fun y _ => (T : E) • y ∈ P.lev.Lb) (fun y hy => P.lev.Lb_dual y hy) ?_ ?_ ?_ hy
    · rw [smul_zero]; exact zero_mem _
    · intro a b _ _ ha hb; rw [smul_add]; exact add_mem ha hb
    · intro r a _ ha; rw [smul_comm]; exact Submodule.smul_mem _ _ ha
  Lb_index := P.lev.Lb_index
  Uloc := P.lev.Uloc
  Uloc_lev := P.lev.Uloc_lev
  Uloc_hyp := fun v h0 h1 hT => P.lev.Uloc_hyp v (fun hb => ((P.bad_iff v).1 hb).elim h0 h1) hT
  Uloc_g := P.Uloc_g
  UlocAlt := P.UlocAlt
  U := P.lev.U
  U_eq := P.lev.U_eq

def LevPack.toCls (P : LevPack hc S.rank S.gram gp T f bad stab fun c => Formalism.L2.Herm.crdLat S (lat c)) :
    Formalism.L2.Herm.ClassTie hc S P.toStep.Lb P.toStep.U stab lat where
  y := P.cls.y
  y_bij := P.cls.y_bij
  y_lat := P.cls.y_lat
  stabI := P.cls.stabI
  stabI_inj := P.cls.stabI_inj
  stabI_range := fun c γ => P.cls.stabI_range c γ.1 γ.2

end Repack

end Formalism.L2.Col
end
end

section -- merged from Formalism.LocalToGlobal.Columns.MultiFactorialEqTripleProd
section -- merged from Formalism.LocalToGlobal.Columns.FactorialSumLePowMulProd
open NumberField IsDedekindDomain Module MvPolynomial
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HermitianLatticesTheory Formalism.HN Formalism.HermitianLattices.TraceIntegrality

section Std

variable (K : Type) [Field K] [NumberField K] [StarRing K] {n : ℕ} (lam : DomWeight n)

def extQ (lam : DomWeight n) : ℚ := Formalism.GradedWeylDivisibility.fockQ (extremal ℚ n lam) (extremal ℚ n lam)

end Std

section Std2

variable (K : Type) [Field K] [NumberField K] [StarRing K] {n : ℕ} (lam : DomWeight n)

end Std2

section Deg

variable (K : Type) [Field K] [NumberField K] [StarRing K] {n : ℕ} (lam : DomWeight n)

end Deg

end Formalism.L2.Col
end
end

open NumberField IsDedekindDomain Module MvPolynomial
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HermitianLatticesTheory Formalism.HN Formalism.L2.Forms

section Main

variable (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)

end Main

section Mono

theorem fock_norm_rational_eq {σ : Type} (P : MvPolynomial σ ℚ) : fockN (map (algebraMap ℚ ℂ) P) = ((Formalism.GradedWeylDivisibility.fockQ P P : ℚ) : ℝ) := by
  unfold fockN Formalism.GradedWeylDivisibility.fockQ
  rw [support_map_of_injective _ (algebraMap ℚ ℂ).injective]
  push_cast
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_map, mfact]
  have : ‖(algebraMap ℚ ℂ) (AddMonoidAlgebra.coeff P m)‖ ^ 2 = ((AddMonoidAlgebra.coeff P m : ℚ) : ℝ) * ((AddMonoidAlgebra.coeff P m : ℚ) : ℝ) := by
    rw [eq_ratCast, Complex.norm_ratCast, sq_abs]
    ring
  rw [this]
  push_cast
  rfl

variable {ι : Type} [Fintype ι] {n : ℕ}

end Mono

section Gen

open Formalism.HermitianLattices.TraceIntegrality

variable (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] {ι : Type} [Fintype ι]

end Gen

end Formalism.L2.Col
end
end
