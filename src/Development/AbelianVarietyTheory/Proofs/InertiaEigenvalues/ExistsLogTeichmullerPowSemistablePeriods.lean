module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTeichmullerLogUnitBcris
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinOEModPrimeLaurentField
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoDecompositionInvariantsAuxiliaryPrime

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTruncLogGalModFil
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinApproxRootGaloisSubMemBdRFil
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinApproxRootGaloisSubMemBdRFil
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.RootGal

theorem sub_mem_of_eval_mem {R : Type*} [CommRing R] (J : Ideal R) (P : Polynomial R) (x y : R)
    (hx : P.eval x ∈ J) (hy : P.eval y ∈ J)
    (hu : ∀ k : R, IsUnit ((Polynomial.derivative P).eval x + k * (y - x))) : y - x ∈ J := by
  obtain ⟨k, hk⟩ := Polynomial.binomExpansion P x (y - x)
  have hxy : x + (y - x) = y := by ring
  rw [hxy] at hk
  have hmem : (y - x) * ((Polynomial.derivative P).eval x + k * (y - x)) ∈ J := by
    have e : (y - x) * ((Polynomial.derivative P).eval x + k * (y - x)) = P.eval y - P.eval x := by
      rw [hk]; ring
    rw [e]; exact J.sub_mem hy hx
  obtain ⟨v, hv⟩ := (hu k).exists_right_inv
  have e : y - x = (y - x) * ((Polynomial.derivative P).eval x + k * (y - x)) * v := by
    rw [mul_assoc, hv, mul_one]
  rw [e]; exact J.mul_mem_right _ hmem

variable {l : ℕ} [Fact l.Prime]

theorem ev_algebraMap (n : ℕ) (a : Per.AinfP l) :
    Per.ev l n (algebraMap (Per.AinfP l) (Per.BdRp l) a) = Ideal.Quotient.mk _ a :=
  GlobalTheory.RingIface.ev_alg l n a

theorem mem_filtration_of_dvd (n : ℕ) (a : Per.Ainf l) (ha : Per.θ l a = 0) (z : Per.BdRp l)
    (hz : aDp l a ^ n ∣ z) : z ∈ Per.FilP l n := by
  obtain ⟨w, rfl⟩ := hz
  have h2 : algebraMap (Per.Ainf l) (Per.AinfP l) a ∈ Per.kerP l := GlobalTheory.RingIface.alg_mem_kerP l ha
  rw [GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow, map_mul, map_pow, aDp, RingHom.comp_apply, ev_algebraMap, ← map_pow,
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow h2 n), zero_mul]

end GlobalTheory.BSP.RootGal


open GlobalTheory.BSP.RootGal in
theorem GlobalTheory.BSP.approxRoot_gal_sub_mem_fil : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (n M : ℕ) (q : bk.S),
    bk.E ∣ q - (l : bk.S) ^ M * X →
    bk.E ^ n ∣ Polynomial.eval₂ PowerSeries.C q (bk.Ep.scaleRoots ((l : Wq l bk.a) ^ M)) →
    ∀ g : ↥(GK K), aDp l (Per.σA (g : GQ l) (bk.ev q) - bk.ev q) ∈ Per.FilP l n := by
  intro l _ K bk n M q hq hroot g
  have hP := GlobalTheory.MemLoc.thetaD_props l
  set h : bk.S →+* Per.BdRp l := (aDp l).comp bk.ev with hh
  set h' : bk.S →+* Per.BdRp l := (aDp l).comp ((Per.σA (g : GQ l)).comp bk.ev) with hh'
  set f : Wq l bk.a →+* Per.BdRp l := h.comp PowerSeries.C with hf
  have hf' : h'.comp PowerSeries.C = f := by
    refine RingHom.ext fun w => ?_
    simp only [hh', hf, hh, RingHom.comp_apply, bk.ev_C, bk.gal_w]
  have hE : Per.θ l (bk.ev bk.E) = 0 := by
    rw [← RingHom.mem_ker, ← bk.span_ev]; exact Ideal.mem_span_singleton_self _
  have hE' : Per.θ l (Per.σA (g : GQ l) (bk.ev bk.E)) = 0 := by rw [GlobalTheory.RingBasics.θ_σA, hE, map_zero]
  have hY : Polynomial.eval₂ f (h q) (bk.Ep.scaleRoots ((l : Wq l bk.a) ^ M)) ∈ Per.FilP l n := by
    refine mem_filtration_of_dvd n (bk.ev bk.E) hE _ ?_
    have h1 := map_dvd h hroot
    rw [Polynomial.hom_eval₂, map_pow] at h1
    exact h1
  have hY' : Polynomial.eval₂ f (h' q) (bk.Ep.scaleRoots ((l : Wq l bk.a) ^ M)) ∈ Per.FilP l n := by
    refine mem_filtration_of_dvd n (Per.σA (g : GQ l) (bk.ev bk.E)) hE' _ ?_
    have h1 := map_dvd h' hroot
    rw [Polynomial.hom_eval₂, map_pow, hf'] at h1
    exact h1
  set s : Per.BdRp l := f ((l : Wq l bk.a) ^ M) with hs
  have hs' : s = (l : Per.BdRp l) ^ M := by rw [hs, map_pow, map_natCast]
  have hsu : IsUnit s := hs' ▸ (isUnit_l_BdRp l).pow M
  obtain ⟨r, hr⟩ := hsu.exists_left_inv
  have hsy : ∀ z : Per.BdRp l, z = s * (r * z) := fun z => by rw [← mul_assoc, mul_comm s r, hr, one_mul]

  have hroot' : ∀ z : Per.BdRp l, Polynomial.eval₂ f z (bk.Ep.scaleRoots ((l : Wq l bk.a) ^ M)) ∈ Per.FilP l n →
      (bk.Ep.map f).eval (r * z) ∈ Per.FilP l n := by
    intro z hz
    rw [hsy z, hs, Polynomial.scaleRoots_eval₂_mul, ← hs] at hz
    have h1 := (Per.FilP l n).mul_mem_left (r ^ bk.Ep.natDegree) hz
    rwa [← mul_assoc, ← mul_pow, hr, one_pow, one_mul, ← Polynomial.eval_map] at h1

  have hθh : ∀ x : bk.S, Per.θD l (h x) = ((Per.θ l (bk.ev x) : OC l) : ℂ_[l]) := fun x => hP.2.2.2.1 _
  have hθdiff : Per.θD l (h' q - h q) = 0 := by
    rw [map_sub, hθh, show h' q = aDp l (Per.σA (g : GQ l) (bk.ev q)) from rfl, hP.2.2.2.1,
      GlobalTheory.BKLim.BetaUniq.theta_gal_ev bk g q, sub_self]
  have hθs : Per.θD l s ≠ 0 := (hsu.map (Per.θD l)).ne_zero
  have hθq : Per.θD l (h q) = Per.θD l s * Per.θD l (h X) := by
    obtain ⟨c, hc⟩ := hq
    have h1 : q = (l : bk.S) ^ M * X + bk.E * c := by rw [← hc]; ring
    rw [h1, map_add (f := _), map_mul, map_mul, map_add (f := _), map_mul, map_mul, hθh bk.E, hE, hs', map_pow, map_pow,
      map_natCast, map_natCast]
    simp
  have hθy : Per.θD l (r * h q) = Per.θD l (h X) := by
    have h1 : Per.θD l s * Per.θD l (r * h q) = Per.θD l s * Per.θD l (h X) := by
      rw [← map_mul, ← mul_assoc, mul_comm s r, hr, one_mul, hθq]
    exact mul_left_cancel₀ hθs h1
  have hder : Per.θD l ((Polynomial.derivative (bk.Ep.map f)).eval (r * h q)) ≠ 0 := by
    rw [Polynomial.derivative_map, Polynomial.eval_map, Polynomial.hom_eval₂, hθy, hf, ← RingHom.comp_assoc,
      show Per.θD l (h X) = ((Per.θD l).comp h) X from rfl, ← Polynomial.hom_eval₂, Polynomial.eval₂_C_X_eq_coe,
      RingHom.comp_apply, hθh]
    intro h0
    apply GlobalTheory.BKLim.ZNotRoot.theta_deriv_ne bk
    exact Subtype.ext h0
  have key := sub_mem_of_eval_mem (Per.FilP l n) (bk.Ep.map f) (r * h q) (r * h' q) (hroot' _ hY) (hroot' _ hY')
    (fun k => hP.2.2.1 _ (by
      rw [map_add (f := _), map_mul, ← mul_sub, map_mul, hθdiff, mul_zero, mul_zero, add_zero]; exact hder))
  rw [map_sub, show aDp l (Per.σA (g : GQ l) (bk.ev q)) = h' q from rfl, show aDp l (bk.ev q) = h q from rfl,
    hsy (h' q), hsy (h q), ← mul_sub]
  exact (Per.FilP l n).mul_mem_left s key
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinApproxRootGaloisSubMemBdRFilStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisensteinApproxRoot_galois_sub_mem_bdRFil : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (n M : ℕ) (q : bk.S),
    bk.E ∣ q - (l : bk.S) ^ M * X →
    bk.E ^ n ∣ Polynomial.eval₂ PowerSeries.C q (bk.Ep.scaleRoots ((l : Wq l bk.a) ^ M)) →
    ∀ g : ↥(GK K), aDp l (Per.σA (g : GQ l) (bk.ev q) - bk.ev q) ∈ Per.FilP l n := by
  first | (exact @GlobalTheory.BSP.approxRoot_gal_sub_mem_fil) | (exact GlobalTheory.BSP.approxRoot_gal_sub_mem_fil) | (intros; apply GlobalTheory.BSP.approxRoot_gal_sub_mem_fil  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMulSubPrimePowDvdEPow
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMulSubPrimePowDvdEPow
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.BK

theorem exists_mul_sub_pow_dvd_of_dvd_sub : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (M m : ℕ) (q : bk.S),
    bk.E ∣ q - (l : bk.S) ^ M * X → ∃ (N : ℕ) (r : bk.S), bk.E ^ m ∣ q * r - (l : bk.S) ^ N := by
  intro l _ K bk M m q hq
  obtain ⟨w, hw⟩ := bk.coeff_zero
  obtain ⟨t, ht⟩ := hq
  set P : bk.S := ((bk.Ep.divX : Polynomial (Wq l bk.a)) : (Wq l bk.a)⟦X⟧) with hP
  have hE : bk.E = X * P + (l : bk.S) * C (w : Wq l bk.a) := by
    have h := Polynomial.X_mul_divX_add bk.Ep
    have h2 := congrArg (fun p : Polynomial (Wq l bk.a) => (p : (Wq l bk.a)⟦X⟧)) h
    simp only [Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_X, Polynomial.coe_C, hw, map_mul,
      map_natCast] at h2
    change (bk.Ep : (Wq l bk.a)⟦X⟧) = _
    rw [← h2, hP]
    congr 2
    rw [← map_natCast (Polynomial.C (R := Wq l bk.a)), Polynomial.coe_C, map_natCast]
  have hu : C (w : Wq l bk.a) * C ((w⁻¹ : (Wq l bk.a)ˣ) : Wq l bk.a) = (1 : bk.S) := by
    rw [← map_mul, Units.mul_inv, map_one]
  set c' : bk.S := C ((w⁻¹ : (Wq l bk.a)ˣ) : Wq l bk.a)
  set a : bk.S := (l : bk.S) ^ (M + 1)
  set h₁ : bk.S := -((l : bk.S) ^ M + t * P) * c'
  set b : bk.S := bk.E * h₁
  have hqr : q * (-c' * P) = a + b := by
    simp only [a, b, h₁]
    linear_combination (-c' * P) * ht + (c' * (l : bk.S) ^ M) * hE + (l : bk.S) ^ (M + 1) * hu
  have key := geom_sum₂_mul a (-b) m
  rw [sub_neg_eq_add] at key
  refine ⟨(M + 1) * m, (-c' * P) * ∑ i ∈ Finset.range m, a ^ i * (-b) ^ (m - 1 - i), -((-h₁) ^ m), ?_⟩
  rw [pow_mul, ← mul_assoc, hqr, mul_comm (a + b), key]
  simp only [b]
  rw [neg_pow, mul_pow, neg_pow h₁]
  ring

end GlobalTheory.BSP.BK
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMulSubPrimePowDvdEPowStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mul_sub_prime_pow_dvd_E_pow : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (M m : ℕ) (q : bk.S),
    bk.E ∣ q - (l : bk.S) ^ M * X → ∃ (N : ℕ) (r : bk.S), bk.E ^ m ∣ q * r - (l : bk.S) ^ N := by
  first | (exact @GlobalTheory.BSP.BK.exists_mul_sub_pow_dvd_of_dvd_sub) | (exact GlobalTheory.BSP.BK.exists_mul_sub_pow_dvd_of_dvd_sub) | (intros; apply GlobalTheory.BSP.BK.exists_mul_sub_pow_dvd_of_dvd_sub  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisFactorTiltLogBdRPlus
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisFactorTiltLogBdRPlus
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.InertiaEigenvalues.TiltGalLog

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem zeta_pow_compat {l : ℕ} [Fact l.Prime] (C : Core l) (c : ℤ_[l]) (m : ℕ) :
    C.ζ m ^ (PadicInt.toZModPow (m + 1) c).val = C.ζ m ^ (PadicInt.toZModPow m c).val := by
  have hz : C.ζ m ^ (l ^ m) = 1 := TAct.zeta_pow C m
  have hred : ∀ a : ℕ, C.ζ m ^ a = C.ζ m ^ (a % l ^ m) := fun a => by
    conv_lhs => rw [← Nat.mod_add_div a (l ^ m), pow_add, pow_mul, hz, one_pow, mul_one]
  have hmod : (PadicInt.toZModPow (m + 1) c).val ≡ (PadicInt.toZModPow m c).val [MOD l ^ m] := by
    rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_val, ZMod.natCast_zmod_val]
    have h := congrArg (fun f : ℤ_[l] →+* ZMod (l ^ m) => f c)
      (PadicInt.zmod_cast_comp_toZModPow (p := l) m (m + 1) (Nat.le_succ m))
    simpa using h
  rw [hred, hmod, ← hred]

theorem rootT_mul {l : ℕ} [Fact l.Prime] (a b : Per.Fl l) (m : ℕ) :
    rootT (a * b) m = rootT a m * rootT b m := by
  unfold rootT
  rw [← map_mul]
  congr 1
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      Function.iterate_succ_apply', ih, map_mul]

theorem gal_factor_log : ∀ (l : ℕ) [Fact l.Prime] (C : Core l) (x : Per.Fl l) (g : GQ l) (c : ℤ_[l]),
    (∀ m : ℕ, rootT (Per.σF g x) m = rootT C.ε m ^ (PadicInt.toZModPow m c).val * rootT x m) →
    ∃ e : Per.Fl l, Per.σF g x = x * e ∧ e.untilt = 1 ∧
      Per.IsLog l e (aDp l (Per.zA l c) * C.j C.t) := by
  intro l _ C x g c H
  obtain ⟨e, he⟩ := NoLog.exists_tilt (fun m => C.ζ m ^ (PadicInt.toZModPow m c).val)
    (fun m => by
      show (C.ζ (m + 1) ^ (PadicInt.toZModPow (m + 1) c).val) ^ l = C.ζ m ^ (PadicInt.toZModPow m c).val
      rw [← pow_mul, mul_comm, pow_mul, C.ζ_succ, zeta_pow_compat]) 1 (by simp [C.ζ_zero])
  have he1 : e.untilt = 1 := Subtype.ext (by
    have := he 0
    rw [C.ζ_zero, one_pow, map_one] at this
    exact this)
  have hre : ∀ m, rootT e m = rootT C.ε m ^ (PadicInt.toZModPow m c).val := fun m =>
    Subtype.ext (by rw [he m, SubmonoidClass.coe_pow, C.ε_root m, map_pow])
  have hxe : Per.σF g x = x * e := by
    refine Perfection.ext fun n => ?_
    change PreTilt.coeff n (Per.σF g x) = PreTilt.coeff n (x * e)
    rw [coeff_eq_mk_rootT, coeff_eq_mk_rootT, H n, rootT_mul, hre n, mul_comm]
  obtain ⟨y, -, hy, -⟩ := exists_isLogA l e he1
  have hyeq := NoLog.log_eq C e c y he hy
  refine ⟨e, hxe, he1, ?_⟩
  have h := LogFun.isLog_map he1 hy C.j_cris
  have hj : C.j (algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l c)) = aDp l (Per.zA l c) := by
    rw [GlobalTheory.RingIface.tower, C.j_cris.on0, Subalgebra.coe_algebraMap, aDp, RingHom.comp_apply]
  rwa [hyeq, map_mul, hj] at h

end GlobalTheory.InertiaEigenvalues.TiltGalLog
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisFactorTiltLogBdRPlusStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_factor_tilt_log_bdRPlus : ∀ (l : ℕ) [Fact l.Prime] (C : Core l) (x : Per.Fl l) (g : GQ l) (c : ℤ_[l]),
    (∀ m : ℕ, rootT (Per.σF g x) m = rootT C.ε m ^ (PadicInt.toZModPow m c).val * rootT x m) →
    ∃ e : Per.Fl l, Per.σF g x = x * e ∧ e.untilt = 1 ∧
      Per.IsLog l e (aDp l (Per.zA l c) * C.j C.t) := by
  first | (exact @GlobalTheory.InertiaEigenvalues.TiltGalLog.gal_factor_log) | (exact GlobalTheory.InertiaEigenvalues.TiltGalLog.gal_factor_log) | (intros; apply GlobalTheory.InertiaEigenvalues.TiltGalLog.gal_factor_log  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTruncLogGalModFil
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.BK

theorem exists_truncLog_gal_mod_fil : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l) (c : ↥(GK K) → ℤ_[l]),
    (∀ (g : ↥(GK K)) (m : ℕ), rootT (Per.σF (g : GQ l) bk.flat) m =
      rootT C.ε m ^ (PadicInt.toZModPow m (c g)).val * rootT bk.flat m) →
    ∀ m : ℕ, ∃ (k : ℕ) (s : bk.S), bk.E ∣ s ∧ ∀ g : ↥(GK K),
      aDp l (Per.σA (g : GQ l) (bk.ev s) - bk.ev s) -
        (l : Per.BdRp l) ^ k * (aDp l (Per.zA l ((bk.Ep.natDegree : ℤ_[l]) * c g)) * C.j C.t) ∈ Per.FilP l m := by
  intro l _ K bk C c hc m
  obtain ⟨M, q, hq1, hq2⟩ := GlobalTheory.T.exists_approx_root_eisenstein_away_prime l K bk m
  obtain ⟨N, r, hr⟩ := GlobalTheory.T.exists_mul_sub_prime_pow_dvd_E_pow l K bk M m q hq1
  obtain ⟨d, hd⟩ := GlobalTheory.RingBasics.exists_pow_div_factorial l m
  set w₀ : bk.S := ((l : bk.S) ^ M * X - q) * r with hw₀
  have hE : bk.E ∣ w₀ := by
    have e1 : (l : bk.S) ^ M * X - q = -(q - (l : bk.S) ^ M * X) := by ring
    rw [hw₀, e1]
    exact (dvd_neg.2 hq1).mul_right _
  set s' : bk.S := ∑ j ∈ Finset.range m, (-1) ^ j * ((m.factorial / (j + 1) : ℕ) : bk.S) * w₀ ^ (j + 1) *
    (l : bk.S) ^ (N * (m - (j + 1))) with hs'
  set s : bk.S := (bk.Ep.natDegree : bk.S) * PowerSeries.C (algebraMap ℤ_[l] (Wq l bk.a) d) * s' with hsdef
  refine ⟨m + N * m, s, ?_, fun g => ?_⟩
  · rw [hsdef]
    apply Dvd.dvd.mul_left
    apply Finset.dvd_sum
    intro j _
    exact ((hE.pow (Nat.succ_ne_zero j)).mul_left _).mul_right _

  set R := Per.AinfP l ⧸ Per.kerP l ^ m
  let qm : Per.AinfP l →+* R := Ideal.Quotient.mk _
  let ι : Per.Ainf l →+* Per.AinfP l := algebraMap (Per.Ainf l) (Per.AinfP l)
  have hev : ∀ x, Per.ev l m (aDp l x) = qm (ι x) := fun x => LogFun.ev_alg m (ι x)
  let I : Ideal R := (Per.kerP l).map qm
  have hI : I ^ m = ⊥ := by
    rw [← Ideal.map_pow]
    exact Ideal.map_quotient_self _
  have hnil : ∀ x ∈ I, x ^ m = 0 := fun x hx => by
    have := Ideal.pow_mem_pow hx m
    rwa [hI, Ideal.mem_bot] at this
  have hR : ∀ n : ℕ, n ≠ 0 → IsUnit (n : R) := fun n hn => by
    have := (GlobalTheory.RingBasics.isUnit_nat l n hn).map qm
    rwa [map_natCast] at this
  obtain ⟨lam, hlam⟩ : ∃ lam : R, (l : R) * lam = 1 := by
    have := (GlobalTheory.RingBasics.isUnit_l l).map qm
    rw [map_natCast] at this
    exact this.exists_right_inv
  let f : bk.S →+* R := qm.comp (ι.comp bk.ev)
  let fσ : bk.S →+* R := qm.comp (ι.comp ((Per.σA (g : GQ l)).comp bk.ev))
  have hEm : ι (bk.ev bk.E) ∈ Per.kerP l := by
    have h0 : Per.θ l (bk.ev bk.E) = 0 := by
      have : bk.ev bk.E ∈ RingHom.ker (Per.θ l) := bk.span_ev ▸ Ideal.mem_span_singleton_self _
      exact this
    first | exact GlobalTheory.RingIface.alg_mem_kerP _ h0 | exact GlobalTheory.RingIface.alg_mem_kerP h0
  have hfE : f bk.E ∈ I := Ideal.mem_map_of_mem _ hEm
  have hfσE : fσ bk.E ∈ I := by
    refine Ideal.mem_map_of_mem _ ?_
    have := GlobalTheory.RingBasics.ker_σ (g : GQ l) hEm
    rwa [Ideal.mem_comap, GlobalTheory.RingBasics.awayMap_algebraMap₂] at this
  have hdvd : ∀ (φ : bk.S →+* R), φ bk.E ∈ I → ∀ x : bk.S, bk.E ^ m ∣ x → φ x = 0 := by
    intro φ hφ x ⟨y, hy⟩
    rw [hy, map_mul, map_pow, hnil _ hφ, zero_mul]
  have hfr : f q * f r = (l : R) ^ N := by
    have := hdvd f hfE _ hr
    rw [map_sub, map_mul, map_pow, map_natCast] at this
    exact sub_eq_zero.1 this
  have hfσr : fσ q * fσ r = (l : R) ^ N := by
    have := hdvd fσ hfσE _ hr
    rw [map_sub, map_mul, map_pow, map_natCast] at this
    exact sub_eq_zero.1 this
  have hσq : fσ q = f q := by
    have h := GlobalTheory.T.eisensteinApproxRoot_galois_sub_mem_bdRFil l K bk m M q hq1 hq2 g
    rw [GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow, hev, map_sub, map_sub] at h
    exact sub_eq_zero.1 h
  have hlamN : (l : R) ^ N * lam ^ N = 1 := by rw [← mul_pow, hlam, one_pow]
  have hσr : fσ r = f r := by
    have hu : IsUnit (f q) := isUnit_iff_exists_inv.2 ⟨f r * lam ^ N, by rw [← mul_assoc, hfr, hlamN]⟩
    apply hu.mul_left_cancel
    rw [← hσq, hfσr, hσq, hfr]
  obtain ⟨e, hxe, he1, hlog⟩ := GlobalTheory.T.galois_factor_tilt_log_bdRPlus l C bk.flat (g : GQ l) (c g) (hc g)
  set τ : R := qm (ι (Per.tm e)) with hτ
  have hσX : fσ X = f X * τ := by
    change qm (ι (Per.σA (g : GQ l) (bk.ev X))) = qm (ι (bk.ev X)) * qm (ι (Per.tm e))
    rw [bk.ev_X, ← map_mul, ← map_mul]
    congr 2
    change Per.σA (g : GQ l) (WittVector.teichmuller l _) = _
    rw [GlobalTheory.RingIface.sigA_teich, hxe, map_mul]
  have hσC : ∀ w, fσ (PowerSeries.C w) = f (PowerSeries.C w) := fun w => by
    change qm (ι (Per.σA (g : GQ l) (bk.ev (PowerSeries.C w)))) = qm (ι (bk.ev (PowerSeries.C w)))
    rw [bk.ev_C, bk.gal_w]
  let T : R → R := fun a => ∑ j ∈ Finset.range m, (-1) ^ j * ((m.factorial / (j + 1) : ℕ) : R) * a ^ (j + 1)
  have hT : ∀ (φ : bk.S →+* R) (a : R), φ w₀ = a * (l : R) ^ N → φ s' = (l : R) ^ (N * m) * T a := by
    intro φ a ha
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hs', map_sum, map_mul, map_pow, map_neg, map_one, map_natCast, ha, T, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjm : N * m = N * (j + 1) + N * (m - (j + 1)) := by
      rw [← mul_add]; congr 1; have := Finset.mem_range.1 hj; omega
    rw [hjm]
    ring
  set A : R := f w₀ * lam ^ N with hAdef
  set B : R := fσ w₀ * lam ^ N with hBdef
  have hA : f w₀ = A * (l : R) ^ N := by rw [hAdef]; linear_combination (-(f w₀)) * hlamN
  have hB' : fσ w₀ = B * (l : R) ^ N := by rw [hBdef]; linear_combination (-(fσ w₀)) * hlamN
  have hAI : A ∈ I := by
    obtain ⟨u, hu⟩ := hE
    rw [hAdef, hu, map_mul]
    exact I.mul_mem_right _ (I.mul_mem_right _ hfE)
  have hbI : τ - 1 ∈ I := by
    have := Ideal.mem_map_of_mem qm (LogFun.mu_mem he1)
    simpa [GlobalTheory.MemLoc.mu, hτ] using this
  have hB : B = A + (τ - 1) + A * (τ - 1) := by
    rw [hBdef, hAdef]
    simp only [hw₀, map_mul, map_sub, map_pow, map_natCast, hσX, hσq, hσr]
    linear_combination (τ - 1) * lam ^ N * hfr + (τ - 1) * hlamN
  have htr : T B = T A + T (τ - 1) := by
    rw [hB]
    exact LogAdd.trunc_add hR m I hI A (τ - 1) hAI hbI
  have hl := GlobalTheory.CrisIncl.factorial_mul_ev l e _ he1 hlog m
  have hl2 : (m.factorial : R) * Per.ev l m (aDp l (Per.zA l (c g)) * C.j C.t) = T (τ - 1) := by
    rw [hl]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [T, map_sum, map_mul, map_pow, map_sub, map_one, map_natCast, map_neg, hτ]
    rfl
  have hfC : (m.factorial : R) * f (PowerSeries.C (algebraMap ℤ_[l] (Wq l bk.a) d)) = (l : R) ^ m := by
    have := congrArg (f.comp (PowerSeries.C.comp (algebraMap ℤ_[l] (Wq l bk.a)))) hd
    simpa only [map_mul, map_natCast, map_pow, RingHom.comp_apply] using this
  have hfs' := hT f A hA
  have hfσs' := hT fσ B hB'
  rw [GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow]
  have e1 : Per.ev l m (aDp l (Per.σA (g : GQ l) (bk.ev s) - bk.ev s)) = fσ s - f s := by
    rw [hev, map_sub, map_sub]; rfl
  have e2 : Per.ev l m ((l : Per.BdRp l) ^ (m + N * m) *
      (aDp l (Per.zA l ((bk.Ep.natDegree : ℤ_[l]) * c g)) * C.j C.t)) =
      (l : R) ^ (m + N * m) * ((bk.Ep.natDegree : R) * Per.ev l m (aDp l (Per.zA l (c g)) * C.j C.t)) := by
    simp only [map_mul, map_pow, map_natCast]; ring
  rw [map_sub, e1, e2]
  have e3 : fσ s = (bk.Ep.natDegree : R) * f (PowerSeries.C (algebraMap ℤ_[l] (Wq l bk.a) d)) * fσ s' := by
    rw [hsdef, map_mul, map_mul, map_natCast, hσC]
  have e4 : f s = (bk.Ep.natDegree : R) * f (PowerSeries.C (algebraMap ℤ_[l] (Wq l bk.a) d)) * f s' := by
    rw [hsdef, map_mul, map_mul, map_natCast]
  rw [e3, e4, hfs', hfσs']
  apply (hR _ m.factorial_ne_zero).mul_left_cancel
  rw [mul_zero]
  linear_combination ((bk.Ep.natDegree : R) * (l : R) ^ (N * m) * (T B - T A)) * hfC -
    ((l : R) ^ (m + N * m) * (bk.Ep.natDegree : R)) * hl2 + ((bk.Ep.natDegree : R) * (l : R) ^ (N * m) * (l : R) ^ m) * htr

end GlobalTheory.BSP.BK
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTruncLogGalModFilStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_truncLog_gal_mod_filP : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l) (c : ↥(GK K) → ℤ_[l]),
    (∀ (g : ↥(GK K)) (m : ℕ), rootT (Per.σF (g : GQ l) bk.flat) m =
      rootT C.ε m ^ (PadicInt.toZModPow m (c g)).val * rootT bk.flat m) →
    ∀ m : ℕ, ∃ (k : ℕ) (s : bk.S), bk.E ∣ s ∧ ∀ g : ↥(GK K),
      aDp l (Per.σA (g : GQ l) (bk.ev s) - bk.ev s) -
        (l : Per.BdRp l) ^ k * (aDp l (Per.zA l ((bk.Ep.natDegree : ℤ_[l]) * c g)) * C.j C.t) ∈ Per.FilP l m := by
  first | (exact @GlobalTheory.BSP.BK.exists_truncLog_gal_mod_fil) | (exact GlobalTheory.BSP.BK.exists_truncLog_gal_mod_fil) | (intros; apply GlobalTheory.BSP.BK.exists_truncLog_gal_mod_fil  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKummerCocycleTiltUniformizer
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKummerCocycleTiltUniformizer
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
noncomputable section

namespace GlobalTheory.FlatKummer

theorem isPrimitiveRoot_of_seq {Ω : Type*} [Field Ω] (l : ℕ) [Fact l.Prime] (ζ : ℕ → Ω) (h0 : ζ 0 = 1)
    (hs : ∀ m, ζ (m + 1) ^ l = ζ m) (h1 : ζ 1 ≠ 1) (m : ℕ) : IsPrimitiveRoot (ζ m) (l ^ m) := by
  have hp : ∀ k, ζ k ^ l ^ k = 1 := by
    intro k
    induction k with
    | zero => simp [h0]
    | succ k ih => rw [pow_succ', pow_mul, hs, ih]
  have h1' : ∀ k, ζ (k + 1) ^ l ^ k = ζ 1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', pow_mul, hs, ih]
  cases m with
  | zero => simp [h0]
  | succ m =>
    have h := orderOf_eq_prime_pow (x := ζ (m + 1)) (p := l) (n := m) (by rw [h1']; exact h1) (hp _)
    rw [← h]
    exact IsPrimitiveRoot.orderOf _

theorem exists_exponent_of_seq {Ω : Type*} [Field Ω] (l : ℕ) [Fact l.Prime] (ζ : ℕ → Ω) (h0 : ζ 0 = 1)
    (hs : ∀ m, ζ (m + 1) ^ l = ζ m) (h1 : ζ 1 ≠ 1) (z w : ℕ → Ω) (hz : ∀ m, z (m + 1) ^ l = z m)
    (hw : ∀ m, w (m + 1) ^ l = w m) (hwz : w 0 = z 0) :
    ∃ c : ℤ_[l], ∀ m, w m = ζ m ^ (PadicInt.toZModPow m c).val * z m := by
  have hne : ∀ m, NeZero (l ^ m) := fun m => ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hiter : ∀ (x : ℕ → Ω), (∀ m, x (m + 1) ^ l = x m) → ∀ m, x m ^ l ^ m = x 0 := by
    intro x hx m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ', pow_mul, hx, ih]
  by_cases hz0 : z 0 = 0
  · refine ⟨0, fun m => ?_⟩
    have a : z m = 0 := pow_eq_zero_iff (pow_ne_zero _ (Fact.out : l.Prime).ne_zero) |>.1 ((hiter z hz m).trans hz0)
    have b : w m = 0 := pow_eq_zero_iff (pow_ne_zero _ (Fact.out : l.Prime).ne_zero) |>.1
      ((hiter w hw m).trans (hwz.trans hz0))
    rw [a, b, mul_zero]
  have hzm : ∀ m, z m ≠ 0 := fun m h => hz0 (by rw [← hiter z hz m, h, zero_pow (hne m).out])
  have hprim := isPrimitiveRoot_of_seq l ζ h0 hs h1
  have hpow : ∀ m a b : ℕ, ζ m ^ a = ζ m ^ b ↔ (a : ZMod (l ^ m)) = (b : ZMod (l ^ m)) := by
    intro m a b
    have hf : IsOfFinOrder (ζ m) := (hprim m).isOfFinOrder (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)
    rw [hf.pow_eq_pow_iff_modEq, ← (hprim m).eq_orderOf, ZMod.natCast_eq_natCast_iff]
  have e1 : ∀ m, ∃ a : ℕ, w m = ζ m ^ a * z m := by
    intro m
    obtain ⟨a, -, ha⟩ := (hprim m).eq_pow_of_pow_eq_one (ξ := w m / z m) (by
      rw [div_pow, hiter w hw, hiter z hz, hwz, div_self hz0])
    exact ⟨a, by rw [ha, div_mul_cancel₀ _ (hzm m)]⟩
  choose a ha using e1
  have hd : ∀ i, (l : ℤ) ^ i ∣ (a (i + 1) : ℤ) - (a i : ℤ) := by
    intro i
    have h2 := congrArg (· ^ l) (ha (i + 1))
    simp only [mul_pow, hw, hz] at h2
    rw [← pow_mul, mul_comm (a (i + 1)), pow_mul, hs, ha i] at h2
    have h3 := (hpow i _ _).mp (mul_right_cancel₀ (hzm i) h2)
    rw [ZMod.natCast_eq_natCast_iff] at h3
    exact_mod_cast h3.dvd
  refine ⟨PadicInt.ofIntSeq (fun i => (a i : ℤ)) (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub _ l hd),
    fun m => ?_⟩
  rw [PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub _ l hd, ha m]
  congr 1
  rw [hpow]
  simp

theorem rootT_succ_pow_l {l : ℕ} [Fact l.Prime] (e : Per.Fl l) (m : ℕ) : rootT e (m + 1) ^ l = rootT e m := by
  rw [rootT, rootT, Function.iterate_succ_apply', ← map_pow, frobeniusEquiv_symm_pow_p]

theorem exists_kummer_flat : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l), ∃ c : ↥(GK K) → ℤ_[l],
    (∀ (g : ↥(GK K)) (m : ℕ), rootT (Per.σF (g : GQ l) bk.flat) m =
      rootT C.ε m ^ (PadicInt.toZModPow m (c g)).val * rootT bk.flat m) ∧ ∀ g, bk.FixFlat g → c g = 0 := by
  intro l _ K bk C
  obtain ⟨hz, -⟩ := GlobalTheory.BSP.rootT_flat_alg_and_fix l K bk
  choose z hz using hz
  have hinj : Function.Injective (algebraMap (Om l) ℂ_[l]) := (algebraMap (Om l) ℂ_[l]).injective
  have hz' : ∀ n, ((rootT bk.flat n : Per.OC l) : ℂ_[l]) = algebraMap (Om l) ℂ_[l] (z n) := hz
  have hzs : ∀ m, z (m + 1) ^ l = z m := by
    intro m
    apply hinj
    rw [map_pow, ← hz', ← hz', ← rootT_succ_pow_l bk.flat m]
    push_cast
    rfl
  set r : ↥(OL K) := bk.str.symm (Ideal.Quotient.mk _ X) with hr
  have hθ : rootT bk.flat 0 = intToOC K r := by
    show bk.flat.untilt = _
    rw [← WittVector.fontaineTheta_teichmuller, ← bk.ev_X]
    exact bk.θ_ev r X (by rw [hr, RingEquiv.apply_symm_apply])
  have hz0 : z 0 = (((r : ↥K.1) : Om l)) := by
    apply hinj
    rw [← hz', hθ, coe_intToOC]
    rfl
  have good : ∀ g : ↥(GK K), ∃ c : ℤ_[l], ∀ m, rootT (Per.σF (g : GQ l) bk.flat) m =
      rootT C.ε m ^ (PadicInt.toZModPow m c).val * rootT bk.flat m := by
    intro g
    have hfix : (g : GQ l) (z 0) = z 0 := by
      rw [hz0]
      exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 _ (r : ↥K.1).2
    obtain ⟨c, hc⟩ := exists_exponent_of_seq l C.ζ C.ζ_zero C.ζ_succ C.ζ_one z (fun m => (g : GQ l) (z m)) hzs
      (fun m => by rw [← map_pow, hzs]) hfix
    refine ⟨c, fun m => ?_⟩
    have hit : ∀ k : ℕ, ((frobeniusEquiv (Per.Fl l) l).symm)^[k] (Per.σF (g : GQ l) bk.flat) =
        Per.σF (g : GQ l) (((frobeniusEquiv (Per.Fl l) l).symm)^[k] bk.flat) := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, RingHom.map_frobeniusEquiv_symm]
    have hsig : rootT (Per.σF (g : GQ l) bk.flat) m = Per.σO (g : GQ l) (rootT bk.flat m) := by
      rw [rootT, hit, GlobalTheory.RingBasics.untilt_σF]; rfl
    rw [hsig]
    apply Subtype.ext
    have h1 : ((Per.σO (g : GQ l) (rootT bk.flat m) : Per.OC l) : ℂ_[l]) = Per.σC (g : GQ l) (rootT bk.flat m : ℂ_[l]) :=
      by apply GlobalTheory.RingIface.sigO_coe
    have h2 : Per.σC (g : GQ l) (algebraMap (Om l) ℂ_[l] (z m)) = algebraMap (Om l) ℂ_[l] ((g : GQ l) (z m)) :=
      GlobalTheory.RingBasics.σC_coe (g : GQ l) _
    push_cast
    rw [h1, hz', h2, hc m, map_mul, map_pow, C.ε_root]
  classical
  refine ⟨fun g => if bk.FixFlat g then 0 else (good g).choose, fun g m => ?_, fun g hg => by simp [hg]⟩
  by_cases hg : bk.FixFlat g
  · simp only [hg, if_true, map_zero, ZMod.val_zero, pow_zero, one_mul]
    rw [show Per.σF (g : GQ l) bk.flat = bk.flat from hg]
  · simp only [hg, if_false]
    exact (good g).choose_spec m

end GlobalTheory.FlatKummer

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKummerCocycleTiltUniformizerStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_kummer_cocycle_tilt_uniformizer : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l), ∃ c : ↥(GK K) → ℤ_[l],
    (∀ (g : ↥(GK K)) (m : ℕ), rootT (Per.σF (g : GQ l) bk.flat) m =
      rootT C.ε m ^ (PadicInt.toZModPow m (c g)).val * rootT bk.flat m) ∧ ∀ g, bk.FixFlat g → c g = 0 := by
  first | (exact @GlobalTheory.FlatKummer.exists_kummer_flat) | (exact GlobalTheory.FlatKummer.exists_kummer_flat) | (intros; apply GlobalTheory.FlatKummer.exists_kummer_flat  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltUniformizerPowEqMulUnit
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltUniformizerPowEqMulUnit
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
noncomputable section

namespace GlobalTheory.TiltDiv

variable {l : ℕ} [Fact l.Prime]

theorem norm_OC_le_one (x : Per.OC l) : ‖(x : ℂ_[l])‖ ≤ 1 := (GlobalTheory.RingBasics.mem_OC _).1 x.2

theorem mk_untilt_iterate (x : OCb l) (n : ℕ) :
    Ideal.Quotient.mk (Ideal.span {((l : ℕ) : Per.OC l)})
      (PreTilt.untilt ((frobeniusEquiv (OCb l) l).symm^[n] x)) = PreTilt.coeff n x := by
  rw [PreTilt.mk_untilt_eq_coeff_zero, PreTilt.coeff_iterate_frobeniusEquiv_symm, zero_add]

theorem untilt_zero : PreTilt.untilt (0 : OCb l) = 0 := Perfection.teichmuller_zero

theorem untilt_eq_zero_iff {x : OCb l} : PreTilt.untilt x = 0 ↔ x = 0 := by
  refine ⟨fun h => Perfection.ext fun n => ?_, fun h => h ▸ untilt_zero⟩
  have h1 := PreTilt.untilt_iterate_frobeniusEquiv_symm_pow x n
  rw [h, pow_eq_zero_iff (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)] at h1
  change PreTilt.coeff n x = PreTilt.coeff n 0
  rw [← mk_untilt_iterate, h1, map_zero, map_zero]

def ofCompatible (y : ℕ → Per.OC l) (hy : ∀ n, y (n + 1) ^ l = y n) : OCb l :=
  (⟨fun n => Ideal.Quotient.mk _ (y n), fun n => by rw [← map_pow, hy]⟩ :
    Perfection (ModP (Per.OC l) l) l)

theorem dvd_of_norm_untilt_le {a b : OCb l} (hb : b ≠ 0)
    (h : ‖((PreTilt.untilt a : Per.OC l) : ℂ_[l])‖ ≤ ‖((PreTilt.untilt b : Per.OC l) : ℂ_[l])‖) :
    b ∣ a := by
  set φ := (frobeniusEquiv (OCb l) l).symm
  have hnorm : ∀ (x : OCb l) (n : ℕ), ‖((PreTilt.untilt (φ^[n] x) : Per.OC l) : ℂ_[l])‖ ^ l ^ n =
      ‖((PreTilt.untilt x : Per.OC l) : ℂ_[l])‖ := by
    intro x n
    rw [← norm_pow, ← SubmonoidClass.coe_pow, PreTilt.untilt_iterate_frobeniusEquiv_symm_pow]
  have hbn : ∀ n, ((PreTilt.untilt (φ^[n] b) : Per.OC l) : ℂ_[l]) ≠ 0 := by
    intro n h0
    apply hb
    have h0' : PreTilt.untilt (φ^[n] b) = 0 := Subtype.ext h0
    rw [← untilt_eq_zero_iff, ← PreTilt.untilt_iterate_frobeniusEquiv_symm_pow b n, h0',
      zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)]
  have hle : ∀ n,
      ‖((PreTilt.untilt (φ^[n] a) : Per.OC l) : ℂ_[l])‖ ≤ ‖((PreTilt.untilt (φ^[n] b) : Per.OC l) : ℂ_[l])‖ := by
    intro n
    have hpn : l ^ n ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
    rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) hpn, hnorm, hnorm]
    exact h
  have hstep : ∀ (x : OCb l) (n : ℕ), PreTilt.untilt (φ^[n + 1] x) ^ l = PreTilt.untilt (φ^[n] x) := by
    intro x n
    rw [Function.iterate_succ_apply', ← map_pow, frobeniusEquiv_symm_pow_p]
  let y : ℕ → Per.OC l := fun n =>
    ⟨((PreTilt.untilt (φ^[n] a) : Per.OC l) : ℂ_[l]) / PreTilt.untilt (φ^[n] b), (GlobalTheory.RingBasics.mem_OC _).2 (by
      rw [norm_div]; exact div_le_one_of_le₀ (hle n) (norm_nonneg _))⟩
  have hy : ∀ n, y (n + 1) ^ l = y n := by
    intro n
    ext
    simp only [y, SubmonoidClass.coe_pow, div_pow]
    rw [← SubmonoidClass.coe_pow, ← SubmonoidClass.coe_pow, hstep, hstep]
  refine ⟨ofCompatible y hy, Perfection.ext fun n => ?_⟩
  change PreTilt.coeff n a = PreTilt.coeff n (b * ofCompatible y hy)
  rw [map_mul]
  change _ = _ * Ideal.Quotient.mk _ (y n)
  rw [← mk_untilt_iterate, ← mk_untilt_iterate, ← map_mul]
  congr 1
  ext
  rw [MulMemClass.coe_mul]
  change _ = _ * (_ / _)
  rw [mul_div_cancel₀ _ (hbn n)]

end GlobalTheory.TiltDiv

end

noncomputable section

namespace GlobalTheory.TiltDiv

variable {l : ℕ} [Fact l.Prime]

theorem norm_pow_natDegree_eq_of_eisenstein {R : Type*} [CommRing R] (P : Polynomial R) (hm : P.Monic)
    (hpos : 0 < P.natDegree) (hdvd : ∀ i < P.natDegree, ((l : ℕ) : R) ∣ P.coeff i)
    (w : Rˣ) (h0 : P.coeff 0 = ((l : ℕ) : R) * w) (Ψ : R →+* ℂ_[l]) (hΨ : ∀ y, ‖Ψ y‖ ≤ 1)
    (z : ℂ_[l]) (hz1 : ‖z‖ ≤ 1) (hz : P.eval₂ Ψ z = 0) :
    ‖z ^ P.natDegree‖ = ‖((l : ℕ) : ℂ_[l])‖ := by
  obtain ⟨m, hm'⟩ : ∃ m, P.natDegree = m + 1 := ⟨P.natDegree - 1, by omega⟩
  have hl0 : 0 < ‖((l : ℕ) : ℂ_[l])‖ :=
    norm_pos_iff.2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have hl1 : ‖((l : ℕ) : ℂ_[l])‖ < 1 := GlobalTheory.RingBasics.norm_p_lt
  have hc : ∀ i < P.natDegree, ‖Ψ (P.coeff i)‖ ≤ ‖((l : ℕ) : ℂ_[l])‖ := by
    intro i hi
    obtain ⟨y, hy⟩ := hdvd i hi
    rw [hy, map_mul, map_natCast, norm_mul]
    calc _ ≤ ‖((l : ℕ) : ℂ_[l])‖ * 1 := by gcongr; exact hΨ y
      _ = _ := mul_one _
  have hw : ‖Ψ w‖ = 1 := by
    have h1 : Ψ w * Ψ ↑w⁻¹ = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    have ha := hΨ w
    have hb := hΨ ↑w⁻¹
    have h2 := congrArg norm h1
    rw [norm_mul, norm_one] at h2
    nlinarith [norm_nonneg (Ψ w), norm_nonneg (Ψ ↑w⁻¹)]
  have hc0 : ‖Ψ (P.coeff 0)‖ = ‖((l : ℕ) : ℂ_[l])‖ := by
    rw [h0, map_mul, map_natCast, norm_mul, hw, mul_one]
  have htop : P.coeff (m + 1) = 1 := by rw [← hm']; exact hm.coeff_natDegree
  rw [Polynomial.eval₂_eq_sum_range, hm', Finset.sum_range_succ, Finset.sum_range_succ', htop,
    map_one, one_mul, pow_zero, mul_one] at hz
  set S := ∑ i ∈ Finset.range m, Ψ (P.coeff (i + 1)) * z ^ (i + 1) with hSdef
  have hS : ‖S‖ ≤ ‖((l : ℕ) : ℂ_[l])‖ * ‖z‖ := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi => ?_
    rw [norm_mul, norm_pow]
    have hi' : i + 1 < P.natDegree := by rw [hm']; simpa using Finset.mem_range.1 hi
    have hp : ‖z‖ ^ (i + 1) ≤ ‖z‖ := pow_le_of_le_one (norm_nonneg _) hz1 (by omega)
    exact mul_le_mul (hc _ hi') hp (by positivity) (norm_nonneg _)
  have hzpow : z ^ (m + 1) = -(Ψ (P.coeff 0) + S) := by linear_combination hz
  have hSl : ‖S‖ ≤ ‖((l : ℕ) : ℂ_[l])‖ := hS.trans (by nlinarith [norm_nonneg z])
  have hup : ‖z ^ (m + 1)‖ ≤ ‖((l : ℕ) : ℂ_[l])‖ := by
    rw [hzpow, norm_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hc0.le hSl)
  have hzlt : ‖z‖ < 1 := by
    by_contra hge
    push_neg at hge
    have : 1 ≤ ‖z‖ ^ (m + 1) := one_le_pow₀ hge
    rw [norm_pow] at hup
    linarith
  have hSlt : ‖S‖ < ‖((l : ℕ) : ℂ_[l])‖ := hS.trans_lt (by nlinarith [norm_nonneg z])
  have hlow : ‖((l : ℕ) : ℂ_[l])‖ ≤ ‖z ^ (m + 1)‖ := by
    have h3 : Ψ (P.coeff 0) = -(z ^ (m + 1) + S) := by linear_combination hz
    have h4 := IsUltrametricDist.norm_add_le_max (z ^ (m + 1)) S
    rw [← norm_neg (z ^ (m + 1) + S), ← h3, hc0] at h4
    rcases le_max_iff.1 h4 with h5 | h5
    · exact h5
    · linarith
  rw [hm']
  exact le_antisymm hup hlow

end GlobalTheory.TiltDiv

end

noncomputable section

namespace GlobalTheory.TiltDiv

theorem flat_pow_natDegree_eq_mul_unit : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ϖ : OCb l),
    ϖ.untilt = ((l : ℕ) : Per.OC l) →
    ∃ x : OCb l, IsUnit x ∧ bk.flat ^ bk.Ep.natDegree = ϖ * x := by
  intro l _ K bk ϖ hϖ
  set r : ↥(OL K) := bk.str.symm (Ideal.Quotient.mk _ X) with hr
  have h1 : bk.flat.untilt = intToOC K r := by
    rw [← WittVector.fontaineTheta_teichmuller, ← bk.ev_X]
    exact bk.θ_ev r X (by rw [hr, RingEquiv.apply_symm_apply])
  let Ψ0 : (Wq l bk.a)⟦X⟧ →+* ℂ_[l] := (PadicComplexInt l).subtype.comp
    ((intToOC K).comp (bk.str.symm.toRingHom.comp (Ideal.Quotient.mk _)))
  let Ψ : Wq l bk.a →+* ℂ_[l] := Ψ0.comp (Polynomial.coeToPowerSeries.ringHom.comp Polynomial.C)
  have hΨ : ∀ y, ‖Ψ y‖ ≤ 1 := fun y => norm_OC_le_one _
  set z : ℂ_[l] := Ψ0 (Polynomial.coeToPowerSeries.ringHom Polynomial.X) with hzdef
  have hzX : z = ((bk.flat.untilt : Per.OC l) : ℂ_[l]) := by
    rw [h1, hzdef, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]
    rfl
  have hz1 : ‖z‖ ≤ 1 := by rw [hzX]; exact norm_OC_le_one _
  have hE : Ψ0 (bk.Ep : (Wq l bk.a)⟦X⟧) = 0 := by
    have : Ideal.Quotient.mk (Ideal.span {(bk.Ep : (Wq l bk.a)⟦X⟧)}) (bk.Ep : (Wq l bk.a)⟦X⟧) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
    simp only [Ψ0, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, this, map_zero]
  have hz : bk.Ep.eval₂ Ψ z = 0 := by
    rw [← hE, hzdef, ← Polynomial.hom_eval₂, ← Polynomial.hom_eval₂, Polynomial.eval₂_C_X]
    rfl
  have hnorm := norm_pow_natDegree_eq_of_eisenstein bk.Ep bk.monic bk.deg_pos bk.dvd_coeff
    bk.coeff_zero.choose bk.coeff_zero.choose_spec Ψ hΨ z hz1 hz
  rw [hzX, ← SubmonoidClass.coe_pow, ← map_pow] at hnorm
  have hl0 : 0 < ‖((l : ℕ) : ℂ_[l])‖ :=
    norm_pos_iff.2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have hϖn : ‖((ϖ.untilt : Per.OC l) : ℂ_[l])‖ = ‖((l : ℕ) : ℂ_[l])‖ := by
    rw [hϖ]; norm_cast
  rw [← hϖn] at hnorm
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    rw [untilt_zero] at hϖn
    simp at hϖn
    linarith
  obtain ⟨x, hx⟩ := dvd_of_norm_untilt_le hϖ0 hnorm.le
  refine ⟨x, ?_, hx⟩
  have hxn : ‖((x.untilt : Per.OC l) : ℂ_[l])‖ = 1 := by
    have h2 := hnorm
    rw [hx, map_mul, MulMemClass.coe_mul, norm_mul, hϖn] at h2
    have h3 : ‖((l : ℕ) : ℂ_[l])‖ * ‖((x.untilt : Per.OC l) : ℂ_[l])‖ = ‖((l : ℕ) : ℂ_[l])‖ * 1 := by
      rw [mul_one]; exact h2
    exact mul_left_cancel₀ hl0.ne' h3
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [untilt_zero] at hxn
    simp at hxn
  refine isUnit_of_dvd_one (dvd_of_norm_untilt_le hx0 ?_)
  rw [map_one, OneMemClass.coe_one, norm_one, hxn]

end GlobalTheory.TiltDiv

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltUniformizerPowEqMulUnitStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tilt_uniformizer_pow_eq_mul_unit : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ϖ : OCb l), ϖ.untilt = ((l : ℕ) : Per.OC l) →
    ∃ x : OCb l, IsUnit x ∧ bk.flat ^ bk.Ep.natDegree = ϖ * x := by
  first | (exact @GlobalTheory.TiltDiv.flat_pow_natDegree_eq_mul_unit) | (exact GlobalTheory.TiltDiv.flat_pow_natDegree_eq_mul_unit) | (intros; apply GlobalTheory.TiltDiv.flat_pow_natDegree_eq_mul_unit  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLogTeichmullerPowSemistablePeriods
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.LogFlat

theorem rootT_cocycle_of_pow_eq_mul : ∀ (l : ℕ) [Fact l.Prime] (C : Core l) (g : GQ l) (y ϖ x : Per.Fl l) (n : ℕ) (a b : ℤ_[l]),
    y ^ n = ϖ * x → ϖ.untilt ≠ 0 →
    (∀ m, rootT (Per.σF g y) m = rootT C.ε m ^ (PadicInt.toZModPow m a).val * rootT y m) →
    (∀ m, rootT (Per.σF g ϖ) m = rootT C.ε m ^ (PadicInt.toZModPow m b).val * rootT ϖ m) →
    ∀ m, rootT (Per.σF g x) m = rootT C.ε m ^ (PadicInt.toZModPow m ((n : ℤ_[l]) * a - b)).val * rootT x m := by
  intro l _ C g y ϖ x n a b hyx hϖ ha hb m
  have hmul : ∀ u v : Per.Fl l, rootT (u * v) m = rootT u m * rootT v m := by
    intro u v; simp only [rootT, iterate_map_mul, map_mul]
  have hpow : ∀ u : Per.Fl l, rootT (u ^ n) m = rootT u m ^ n := by
    intro u; simp only [rootT, iterate_map_pow, map_pow]
  have hζ : rootT C.ε m ^ (l ^ m) = 1 := by
    rw [rootT_pow_eq_untilt]; exact (core_isEps l C).1
  have hϖm : rootT ϖ m ≠ 0 := by
    intro h0; apply hϖ; rw [← rootT_pow_eq_untilt, h0, zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)]
  have hζ0 : ∀ k : ℕ, rootT C.ε m ^ k ≠ 0 := by
    intro k h0
    have : rootT C.ε m = 0 := pow_eq_zero_iff'.mp h0 |>.1
    rw [this, zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)] at hζ
    exact zero_ne_one hζ
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  set A := (PadicInt.toZModPow m a).val
  set B := (PadicInt.toZModPow m b).val
  set Cc := (PadicInt.toZModPow m ((n : ℤ_[l]) * a - b)).val
  have hexp : rootT C.ε m ^ (n * A) = rootT C.ε m ^ (B + Cc) := by
    rw [pow_eq_pow_mod (n * A) hζ, pow_eq_pow_mod (B + Cc) hζ]
    congr 1
    rw [← ZMod.natCast_eq_natCast_iff']
    simp only [A, B, Cc, Nat.cast_mul, Nat.cast_add, ZMod.natCast_val, ZMod.cast_id', id, map_sub, map_mul,
      map_natCast]
    ring
  have h1 : rootT ((Per.σF g y) ^ n) m = rootT (Per.σF g ϖ * Per.σF g x) m := by
    rw [← map_pow, ← map_mul, hyx]
  rw [hpow, hmul, ha, hb, mul_pow, ← pow_mul, ← hpow y, hyx, hmul, mul_comm A n, hexp] at h1
  have h2 : rootT C.ε m ^ B * (rootT ϖ m * rootT ((Per.σF g) x) m) =
      rootT C.ε m ^ B * (rootT ϖ m * (rootT C.ε m ^ Cc * rootT x m)) := by
    rw [pow_add] at h1; linear_combination -h1
  have h3 := mul_left_cancel₀ (hζ0 B) h2
  exact mul_left_cancel₀ hϖm h3

theorem rootT_σF_tilt_l : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (C : Core l), C.ζ = P.ζQ → ∀ ϖ : Per.Fl l,
    (∀ m : ℕ, (rootT ϖ m : ℂ_[l]) = algebraMap (Om l) ℂ_[l] (lRoot l m)) → ∀ (g : GQ l) (m : ℕ),
    rootT (Per.σF g ϖ) m = rootT C.ε m ^ (PadicInt.toZModPow m (kummer P g)).val * rootT ϖ m := by
  intro l _ P C hζ ϖ hr g m
  have hit : ∀ k : ℕ, ((frobeniusEquiv (Per.Fl l) l).symm)^[k] (Per.σF g ϖ) =
      Per.σF g (((frobeniusEquiv (Per.Fl l) l).symm)^[k] ϖ) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, RingHom.map_frobeniusEquiv_symm]
  have hsig : rootT (Per.σF g ϖ) m = Per.σO g (rootT ϖ m) := by
    rw [rootT, hit, GlobalTheory.RingBasics.untilt_σF]; rfl
  rw [hsig]
  apply Subtype.ext
  have h1 : ((Per.σO g (rootT ϖ m) : Per.OC l) : ℂ_[l]) = Per.σC g (rootT ϖ m : ℂ_[l]) :=
    GlobalTheory.RingIface.sigO_coe l g _
  have h2 : Per.σC g (algebraMap (Om l) ℂ_[l] (lRoot l m)) = algebraMap (Om l) ℂ_[l] (g (lRoot l m)) :=
    GlobalTheory.RingBasics.σC_coe g _
  push_cast
  rw [h1, hr, h2, isKummer_kummer P g m, map_mul, map_pow, C.ε_root, hζ]

theorem exists_log_flat_pow_Bst : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (_ : True), ∃ (b : P.R.B) (c : ↥(GK K) → ℤ_[l]), ((∀ g : ↥(GK K), actSt P (g : GQ l) (Polynomial.X + Polynomial.C b) = Polynomial.X + Polynomial.C b + Polynomial.C ((c g : ℚ_[l]) • P.tB)) ∧ phiSt P (Polynomial.X + Polynomial.C b) = (l : Bst P) * (Polynomial.X + Polynomial.C b)) ∧ (∀ g, bk.FixFlat g → c g = 0) ∧ ∀ m : ℕ, ∃ (k : ℕ) (s : bk.S), bk.E ∣ s ∧ ∀ g : ↥(GK K), aDp l (Per.σA (g : GQ l) (bk.ev s) - bk.ev s) - (l : Per.BdRp l) ^ k * (aDp l (Per.zA l (c g)) * C.j C.t) ∈ Per.FilP l m := by
  intro l _ K bk P AI T C hF _
  obtain ⟨ϖ, hr⟩ := GlobalTheory.Pst.NoLog.exists_tilt (lRoot l) (lRoot_succ l) l (lRoot_zero l)
  have hϖ : ϖ.untilt = ((l : ℕ) : Per.OC l) := Subtype.ext (by
    have := hr 0
    rw [lRoot_zero, map_natCast] at this
    exact this.trans (SubringClass.coe_natCast _ _).symm)
  obtain ⟨x, hxu, hx⟩ := GlobalTheory.T.tilt_uniformizer_pow_eq_mul_unit l K bk ϖ hϖ
  obtain ⟨cπ, hcπ, hfix⟩ := GlobalTheory.T.exists_kummer_cocycle_tilt_uniformizer l K bk C
  obtain ⟨bx, hφ, hgal⟩ := GlobalTheory.T.exists_teichmuller_log_unit_bcris l C x hxu
  have hϖ0 : ϖ.untilt ≠ 0 := by
    rw [hϖ]; exact_mod_cast (Fact.out : l.Prime).ne_zero
  refine ⟨T.eB.symm bx, fun g => (bk.Ep.natDegree : ℤ_[l]) * cπ g, ⟨fun g => ?_, ?_⟩,
    fun g hg => by simp [hfix g hg], GlobalTheory.T.exists_truncLog_gal_mod_filP l K bk C cπ hcπ⟩
  · have hx' := rootT_cocycle_of_pow_eq_mul l C (g : GQ l) bk.flat ϖ x bk.Ep.natDegree (cπ g) (kummer P g) hx hϖ0 (hcπ g)
      (rootT_σF_tilt_l l P C hF.ζ ϖ hr g)
    have h1 := hgal (g : GQ l) _ hx'
    have h2 : P.actQ (g : GQ l) (T.eB.symm bx) = T.eB.symm bx +
        (((bk.Ep.natDegree : ℤ_[l]) * cπ g - kummer P g : ℤ_[l]) : ℚ_[l]) • P.tB := by
      apply T.eB.injective
      rw [T.actB, RingEquiv.apply_symm_apply, h1, map_add (f := _), RingEquiv.apply_symm_apply, Algebra.smul_def, map_mul,
        T.zB, hF.t]
    rw [map_add (f := _), actSt_X, actSt_C, h2, Polynomial.C_add]
    have key : ((kummer P (g : GQ l) : ℤ_[l]) : ℚ_[l]) • P.tB +
        (((bk.Ep.natDegree : ℤ_[l]) * cπ g - kummer P g : ℤ_[l]) : ℚ_[l]) • P.tB =
        (((bk.Ep.natDegree : ℤ_[l]) * cπ g : ℤ_[l]) : ℚ_[l]) • P.tB := by
      rw [← add_smul]; congr 1; push_cast; ring
    show _ = _ + Polynomial.C ((((bk.Ep.natDegree : ℤ_[l]) * cπ g : ℤ_[l]) : ℚ_[l]) • P.tB)
    rw [← key, Polynomial.C_add]; ring
  · have h2 : P.φB (T.eB.symm bx) = (l : P.R.B) * T.eB.symm bx := by
      apply T.eB.injective
      rw [T.frob, RingEquiv.apply_symm_apply, hφ, map_mul, map_natCast, RingEquiv.apply_symm_apply]
    rw [map_add (f := _), phiSt_X, phiSt_C, h2, mul_add, Polynomial.C_mul, map_natCast]

end GlobalTheory.LogFlat

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLogTeichmullerPowSemistablePeriodsStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_log_teichmuller_pow_semistablePeriods : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (_ : True), ∃ (b : P.R.B) (c : ↥(GK K) → ℤ_[l]), ((∀ g : ↥(GK K), actSt P (g : GQ l) (Polynomial.X + Polynomial.C b) = Polynomial.X + Polynomial.C b + Polynomial.C ((c g : ℚ_[l]) • P.tB)) ∧ phiSt P (Polynomial.X + Polynomial.C b) = (l : Bst P) * (Polynomial.X + Polynomial.C b)) ∧ (∀ g, bk.FixFlat g → c g = 0) ∧ ∀ m : ℕ, ∃ (k : ℕ) (s : bk.S), bk.E ∣ s ∧ ∀ g : ↥(GK K), aDp l (Per.σA (g : GQ l) (bk.ev s) - bk.ev s) - (l : Per.BdRp l) ^ k * (aDp l (Per.zA l (c g)) * C.j C.t) ∈ Per.FilP l m := by
  first | (exact @GlobalTheory.LogFlat.exists_log_flat_pow_Bst) | (exact GlobalTheory.LogFlat.exists_log_flat_pow_Bst) | (intros; apply GlobalTheory.LogFlat.exists_log_flat_pow_Bst  <;> assumption)
end
