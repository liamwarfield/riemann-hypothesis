module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralHilbert90FiniteIdelesTrivialWhereTrivial

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntUnitRoot
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IntegralHilbertNinety

theorem conj_sig (D : D7) : Formalism.L2.DIV.IsConjOf D.sp.cm.sig := by
  refine ⟨fun h0 => ?_, fun e => star_star e, fun e he => ?_⟩
  · have hs : Function.Surjective (algebraMap D.host.F D.host.E) := fun e => (D.sp.cm.fixed e).1 (AlgHom.congr_fun h0 e)
    have h1 : Module.finrank D.host.F D.host.E = 1 :=
      (LinearEquiv.finrank_eq (LinearEquiv.ofBijective (Algebra.linearMap D.host.F D.host.E)
        ⟨(algebraMap D.host.F D.host.E).injective, hs⟩)).symm.trans (Module.finrank_self _)
    have := D.sp.cm.deg2
    omega
  · exact (D.sp.cm.fixed e).1 he

theorem swap_sig (D : D7) (w : Af D.host.F ⊗[D.host.F] D.host.E) :
    Formalism.IndefR.Lev.swapAE D (sigR (Af D.host.F) D.sp.cm.sig w) =
      Formalism.UG.sigR D.sp.cm.sig _ (Formalism.IndefR.Lev.swapAE D w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add a b ha hb => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), ha, hb, RingHom.map_add (f := _), RingHom.map_add (f := _)]

abbrev swapEquiv (D : D7) : Af D.host.F ⊗[D.host.F] D.host.E ≃+* Formalism.IndefR.Lev.EAf D :=
  (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).toRingEquiv

theorem swapEquiv_apply (D : D7) (w : Af D.host.F ⊗[D.host.F] D.host.E) :
    swapEquiv D w = Formalism.IndefR.Lev.swapAE D w := rfl


set_option maxHeartbeats 2000000 in
theorem exists_int_unit_root : ∀ (D : D7) (z : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ),
    (z : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D →
    (∃ y₀ : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ, (y₀ : Af D.host.F ⊗[D.host.F] D.host.E) =
      z * sigR (Af D.host.F) D.sp.cm.sig (y₀ : Af D.host.F ⊗[D.host.F] D.host.E)) →
    ∃ y : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ, (y : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D ∧
      ((y⁻¹ : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D ∧
      (y : Af D.host.F ⊗[D.host.F] D.host.E) = z * sigR (Af D.host.F) D.sp.cm.sig (y : Af D.host.F ⊗[D.host.F] D.host.E) := by
  intro D z hz ⟨y₀, hy₀⟩
  have hss : ∀ w, sigR (Af D.host.F) D.sp.cm.sig (sigR (Af D.host.F) D.sp.cm.sig w) = w := fun w => by
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      show a ⊗ₜ[D.host.F] (D.sp.cm.sig (D.sp.cm.sig x)) = a ⊗ₜ[D.host.F] x
      rw [(conj_sig D).2.1 x]
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]

  have hzs : (z : Af D.host.F ⊗[D.host.F] D.host.E) * sigR (Af D.host.F) D.sp.cm.sig z = 1 := by
    have h1 : sigR (Af D.host.F) D.sp.cm.sig (y₀ : Af D.host.F ⊗[D.host.F] D.host.E) =
        sigR (Af D.host.F) D.sp.cm.sig z * y₀ := by
      conv_lhs => rw [hy₀]
      rw [map_mul, hss]
    have h2 : (y₀ : Af D.host.F ⊗[D.host.F] D.host.E) = z * sigR (Af D.host.F) D.sp.cm.sig z * y₀ := by
      rw [mul_assoc, ← h1]; exact hy₀
    have h3 := congrArg (· * ((y₀⁻¹ : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E)) h2
    simp only [Units.mul_inv, mul_assoc, mul_one] at h3
    exact h3.symm
  have hzinv : ((z⁻¹ : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) =
      sigR (Af D.host.F) D.sp.cm.sig z := Units.inv_eq_of_mul_eq_one_right hzs

  obtain ⟨z', hz'⟩ : ∃ z' : (Formalism.L2.DIV.AfE D.host.F D.host.E)ˣ,
      (z' : Formalism.L2.DIV.AfE D.host.F D.host.E) = Formalism.IndefR.Lev.swapAE D z :=
    ⟨Units.map (Formalism.IndefR.Lev.swapAE D).toMonoidHom z, Units.coe_map _ _⟩
  have hconj : ∀ u : (Formalism.L2.DIV.AfE D.host.F D.host.E)ˣ,
      ((Formalism.L2.DIV.conjId D.sp.cm.sig u : (Formalism.L2.DIV.AfE D.host.F D.host.E)ˣ) : Formalism.L2.DIV.AfE D.host.F D.host.E) =
        Formalism.UG.sigR D.sp.cm.sig (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (u : Formalism.L2.DIV.AfE D.host.F D.host.E) := by
    intro u
    rw [Formalism.L2.DIV.conjId, Units.coe_map]
    rfl
  have hU1 : z' ∈ Formalism.L2.DIV.U1 D.sp.cm.sig := by
    rw [Formalism.L2.DIV.U1, MonoidHom.mem_ker, MonoidHom.mul_apply, MonoidHom.id_apply]
    apply Units.ext
    rw [Units.val_mul, Units.val_one, hconj, hz', ← swap_sig, ← map_mul, hzs, map_one]
  have hz'inv : ((z'⁻¹ : (Formalism.L2.DIV.AfE D.host.F D.host.E)ˣ) : Formalism.L2.DIV.AfE D.host.F D.host.E) =
      Formalism.IndefR.Lev.swapAE D ((z⁻¹ : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) :=
    Units.inv_eq_of_mul_eq_one_right (by rw [hz', ← map_mul, Units.mul_inv, map_one])
  have hint : z' ∈ Formalism.L2.DIV.intU D.host.F D.host.E := by
    rw [Formalism.L2.DIV.intU, Submonoid.mem_units_iff]
    refine ⟨?_, ?_⟩
    · rw [hz']
      exact (GlobalTheory.IdemSupport.mem_intAE_iff _).1 hz
    · rw [hz'inv]
      refine (GlobalTheory.IdemSupport.mem_intAE_iff _).1 ?_
      rw [hzinv]
      exact GlobalTheory.DetOnto.sigR_mem_intAE D hz
  obtain ⟨x, hx, hxz, -⟩ := GlobalTheory.TwU.IntegralHilbert90Unramified.exists_integral_h90_preimage_trivial_where_trivial D.host.F D.host.E D.sp.cm.sig (conj_sig D)
    (GlobalTheory.HeckeAdjoint.unramified_host D) z' hU1 hint
  have hx' := (Submonoid.mem_units_iff _ _).1 hx
  have hxe : (x : Formalism.L2.DIV.AfE D.host.F D.host.E) =
      (z' : Formalism.L2.DIV.AfE D.host.F D.host.E) * Formalism.UG.sigR D.sp.cm.sig _ (x : Formalism.L2.DIV.AfE D.host.F D.host.E) := by
    have h := congrArg (fun u : (Formalism.L2.DIV.AfE D.host.F D.host.E)ˣ =>
      ((u * Formalism.L2.DIV.conjId D.sp.cm.sig x : (Formalism.L2.DIV.AfE D.host.F D.host.E)ˣ) : Formalism.L2.DIV.AfE D.host.F D.host.E)) hxz
    simp only [Formalism.L2.DIV.h90, MonoidHom.div_apply, MonoidHom.id_apply, div_mul_cancel] at h
    rw [Units.val_mul, hconj] at h
    exact h
  refine ⟨Units.map (swapEquiv D).symm.toRingHom.toMonoidHom x, ?_, ?_, ?_⟩
  · rw [GlobalTheory.IdemSupport.mem_intAE_iff, ← swapEquiv_apply]
    change swapEquiv D ((swapEquiv D).symm (x : Formalism.L2.DIV.AfE D.host.F D.host.E)) ∈ _
    rw [RingEquiv.apply_symm_apply]
    exact hx'.1
  · rw [GlobalTheory.IdemSupport.mem_intAE_iff, ← swapEquiv_apply, ← map_inv]
    change swapEquiv D ((swapEquiv D).symm ((x⁻¹ : (Formalism.L2.DIV.AfE D.host.F D.host.E)ˣ) : Formalism.L2.DIV.AfE D.host.F D.host.E)) ∈ _
    rw [RingEquiv.apply_symm_apply]
    exact hx'.2
  · apply (swapEquiv D).injective
    change swapEquiv D ((swapEquiv D).symm (x : Formalism.L2.DIV.AfE D.host.F D.host.E)) =
      swapEquiv D ((z : Af D.host.F ⊗[D.host.F] D.host.E) *
        sigR (Af D.host.F) D.sp.cm.sig ((swapEquiv D).symm (x : Formalism.L2.DIV.AfE D.host.F D.host.E)))
    rw [RingEquiv.apply_symm_apply, map_mul, swapEquiv_apply, swapEquiv_apply, swap_sig, ← swapEquiv_apply D
      ((swapEquiv D).symm _), RingEquiv.apply_symm_apply, ← hz']
    exact hxe

end GlobalTheory.IntegralHilbertNinety
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdeleUnitCongrOne
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnitRootCong

open Formalism.MainNotions.StandardLattice

section Gen

variable {F : Type} [Field F] [NumberField F]

def mkAf (g : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (hg : ∀ v, g v ∈ v.adicCompletionIntegers F) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F :=
  ⟨g, Filter.Eventually.of_forall hg⟩

theorem evalV_mkAf (g : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (hg : ∀ v, g v ∈ v.adicCompletionIntegers F) (v : HeightOneSpectrum (𝓞 F)) :
    evalV F v (mkAf g hg) = g v := rfl

theorem mkAf_mem (g : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (hg : ∀ v, g v ∈ v.adicCompletionIntegers F) : mkAf g hg ∈ intAf F := fun v => by
  rw [evalV_mkAf]; exact hg v

theorem val_eq_one_of_mul (v : HeightOneSpectrum (𝓞 F)) {a b : v.adicCompletion F}
    (ha : Valued.v a ≤ 1) (hb : Valued.v b ≤ 1) (hab : Valued.v (a * b) = 1) : Valued.v a = 1 := by
  refine le_antisymm ha ?_
  calc (1 : _) = Valued.v a * Valued.v b := by rw [← map_mul, hab]
    _ ≤ Valued.v a * 1 := mul_le_mul_right hb (Valued.v a)
    _ = Valued.v a := mul_one _

theorem val_le_one {v : HeightOneSpectrum (𝓞 F)} {a : v.adicCompletion F}
    (ha : a ∈ v.adicCompletionIntegers F) : Valued.v a ≤ 1 :=
  (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).1 ha

theorem mem_of_val {v : HeightOneSpectrum (𝓞 F)} {a : v.adicCompletion F}
    (ha : Valued.v a ≤ 1) : a ∈ v.adicCompletionIntegers F :=
  (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).2 ha

theorem val_natCast_le (v : HeightOneSpectrum (𝓞 F)) (k : ℕ) : Valued.v (k : v.adicCompletion F) ≤ 1 :=
  val_le_one (natCast_mem (HeightOneSpectrum.adicCompletionIntegers F v) k)

theorem val_unit_of_rel (v : HeightOneSpectrum (𝓞 F)) (k : ℕ) {t q r : v.adicCompletion F}
    (hm : Valued.v (((2 * k + 1 : ℕ) : v.adicCompletion F)) < 1)
    (ht : Valued.v t ≤ 1) (hq : Valued.v q ≤ 1) (hr : Valued.v r ≤ 1)
    (h4 : (4 : v.adicCompletion F) = t * q + ((2 * k + 1 : ℕ) : v.adicCompletion F) * r) :
    Valued.v (-(k : v.adicCompletion F) * t) = 1 := by
  set M : v.adicCompletion F := ((2 * k + 1 : ℕ) : v.adicCompletion F) with hM
  have hk : Valued.v (k : v.adicCompletion F) ≤ 1 := val_natCast_le v k
  have h2k : Valued.v (2 * (k : v.adicCompletion F)) = 1 := by
    have e : 2 * (k : v.adicCompletion F) = -1 + M := by rw [hM]; push_cast; ring
    rw [e, Valuation.map_add_eq_of_lt_left Valued.v (by rw [Valuation.map_neg, map_one]; exact hm),
      Valuation.map_neg, map_one]
  have hsq : (2 * (k : v.adicCompletion F)) ^ 2 = (-(k : v.adicCompletion F) * t) * (-(k : v.adicCompletion F) * q) +
      M * ((k : v.adicCompletion F) ^ 2 * r) := by
    linear_combination (k : v.adicCompletion F) ^ 2 * h4
  have hsmall : Valued.v (M * ((k : v.adicCompletion F) ^ 2 * r)) < 1 := by
    rw [map_mul]
    calc Valued.v M * Valued.v ((k : v.adicCompletion F) ^ 2 * r) ≤ Valued.v M * 1 := by
          refine mul_le_mul_right ?_ _
          rw [map_mul, map_pow]
          calc Valued.v (k : v.adicCompletion F) ^ 2 * Valued.v r ≤ 1 * 1 := by
                gcongr
                exact pow_le_one₀ zero_le' hk
            _ = 1 := one_mul 1
      _ < 1 := by rw [mul_one]; exact hm
  have hprod : Valued.v ((-(k : v.adicCompletion F) * t) * (-(k : v.adicCompletion F) * q)) = 1 := by
    have e : (-(k : v.adicCompletion F) * t) * (-(k : v.adicCompletion F) * q) =
        (2 * (k : v.adicCompletion F)) ^ 2 + -(M * ((k : v.adicCompletion F) ^ 2 * r)) := by
      rw [hsq]; ring
    have hv1 : Valued.v ((2 * (k : v.adicCompletion F)) ^ 2) = 1 := by rw [map_pow, h2k, one_pow]
    rw [e, Valuation.map_add_eq_of_lt_left Valued.v (by rw [Valuation.map_neg, hv1]; exact hsmall), hv1]
  refine val_eq_one_of_mul v ?_ ?_ hprod
  · rw [map_mul, Valuation.map_neg]
    calc Valued.v (k : v.adicCompletion F) * Valued.v t ≤ 1 * 1 := by gcongr
      _ = 1 := one_mul 1
  · rw [map_mul, Valuation.map_neg]
    calc Valued.v (k : v.adicCompletion F) * Valued.v q ≤ 1 * 1 := by gcongr
      _ = 1 := one_mul 1

end Gen

end GlobalTheory.UnitRootCong

namespace GlobalTheory.UnitRootCong

open Formalism.MainNotions.StandardLattice


set_option maxHeartbeats 2000000 in
theorem exists_adele_unit_congr_one : ∀ (D : D7) (m : ℕ), Odd m → ∀ (z y : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ), (y : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D → ((y⁻¹ : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D → (y : Af D.host.F ⊗[D.host.F] D.host.E) = z * sigR (Af D.host.F) D.sp.cm.sig (y : Af D.host.F ⊗[D.host.F] D.host.E) → (∃ w ∈ intAE D, (z : Af D.host.F ⊗[D.host.F] D.host.E) - 1 = m • w) → ∃ (b : (Af D.host.F)ˣ) (y' : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ), (y' : Af D.host.F ⊗[D.host.F] D.host.E) = (y : Af D.host.F ⊗[D.host.F] D.host.E) * ((b : Af D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E)) ∧ (y' : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D ∧ ((y'⁻¹ : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D ∧ ∃ w ∈ intAE D, (y' : Af D.host.F ⊗[D.host.F] D.host.E) - 1 = m • w := by
  classical
  intro D m hm z y hyI hyiI hyz hzw
  obtain ⟨w, hwI, hw⟩ := hzw
  obtain ⟨k, rfl⟩ := hm
  have hE := GlobalTheory.AdelicU.isCMExt_host D
  set M : ℕ := 2 * k + 1 with hMdef
  set yv : Af D.host.F ⊗[D.host.F] D.host.E := (y : Af D.host.F ⊗[D.host.F] D.host.E) with hyv
  set yi : Af D.host.F ⊗[D.host.F] D.host.E := ((y⁻¹ : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) with hyi
  have hyy : yv * yi = 1 := y.mul_inv
  set s := sigR (Af D.host.F) D.sp.cm.sig yv with hs
  have hsI : s ∈ intAE D := GlobalTheory.PlaceIdem.sig_mem D hyI
  set T := Algebra.trace (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) with hT
  set ι := algebraMap (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) with hι
  have ht : yv + s = ι (T yv) := GlobalTheory.GaussMean.OneVec.add_sigR _ hE yv
  have hw' : (z : Af D.host.F ⊗[D.host.F] D.host.E) - 1 = (M : Af D.host.F ⊗[D.host.F] D.host.E) * w := by
    rw [hw, nsmul_eq_mul]
  have E3 : 2 * yv = ι (T yv) + (M : Af D.host.F ⊗[D.host.F] D.host.E) * (w * s) := by
    linear_combination ht + hyz + s * hw'

  have hιI : ∀ a ∈ intAf D.host.F, ι a ∈ intAE D := fun a ha =>
    AddSubgroup.subset_closure ⟨a, ha, 1, by simp [hι, Algebra.TensorProduct.algebraMap_apply]⟩
  have hmulI : ∀ {a b}, a ∈ intAE D → b ∈ intAE D → a * b ∈ intAE D := fun ha hb =>
    GlobalTheory.HostAdeleIso.intAE_mul_mem D ha hb
  have hoI : (1 : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D := by
    simpa using hιI 1 GlobalTheory.SplitHeckeLabel.one_mem_intAf
  have hnI : ∀ n : ℕ, (n : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D := fun n => by
    rw [← nsmul_one]; exact nsmul_mem hoI n
  have hrI : w * s * yi ∈ intAE D := hmulI (hmulI hwI hsI) hyiI

  have hTl : ∀ (a : Af D.host.F) x, T (ι a * x) = a * T x := fun a x => by
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  have hT2 : T (ι 2) = 4 := by
    have h1 := GlobalTheory.GaussMean.OneVec.half_trace (Af D.host.F) hE (2 : Af D.host.F)
    have h2 := GlobalTheory.GaussMean.OneVec.half_two (F := D.host.F) (Af D.host.F)
    linear_combination 2 * h1 - T (ι 2) * h2
  have R1 : (4 : Af D.host.F) = T yv * T yi + (M : Af D.host.F) * T (w * s * yi) := by
    have e : ι 2 = ι (T yv) * yi + ι (M : Af D.host.F) * (w * s * yi) := by
      rw [map_ofNat, map_natCast]
      linear_combination yi * E3 - 2 * hyy
    rw [← hT2, e, map_add (f := _), hTl, hTl]

  let P : HeightOneSpectrum (𝓞 D.host.F) → Prop := fun v => Valued.v ((M : v.adicCompletion D.host.F)) < 1
  have hunit : ∀ v, P v → Valued.v (-(k : v.adicCompletion D.host.F) * evalV D.host.F v (T yv)) = 1 := fun v hv => by
    refine val_unit_of_rel v k hv (val_le_one (GlobalTheory.SplitHeckeLabel.trace_mem_intAf hyI v))
      (val_le_one (GlobalTheory.SplitHeckeLabel.trace_mem_intAf hyiI v))
      (val_le_one (GlobalTheory.SplitHeckeLabel.trace_mem_intAf hrI v)) ?_
    have := congrArg (evalV D.host.F v) R1
    simp only [map_add (f := _), map_mul, map_natCast, map_ofNat] at this
    exact this
  have hMone : ∀ v, ¬ P v → Valued.v ((M : v.adicCompletion D.host.F)) = 1 := fun v hv =>
    le_antisymm (val_natCast_le v M) (not_lt.1 hv)
  have hMne : ∀ v, ¬ P v → (M : v.adicCompletion D.host.F) ≠ 0 := fun v hv h => by
    have := hMone v hv; rw [h, map_zero] at this; exact zero_ne_one this
  let eg : ∀ v : HeightOneSpectrum (𝓞 D.host.F), v.adicCompletion D.host.F := fun v => if P v then 1 else 0
  let fg : ∀ v : HeightOneSpectrum (𝓞 D.host.F), v.adicCompletion D.host.F :=
    fun v => if P v then 0 else (M : v.adicCompletion D.host.F)⁻¹
  let cg : ∀ v : HeightOneSpectrum (𝓞 D.host.F), v.adicCompletion D.host.F :=
    fun v => if P v then -(k : v.adicCompletion D.host.F) * evalV D.host.F v (T yv) else 1
  let dg : ∀ v : HeightOneSpectrum (𝓞 D.host.F), v.adicCompletion D.host.F :=
    fun v => if P v then (-(k : v.adicCompletion D.host.F) * evalV D.host.F v (T yv))⁻¹ else 1
  have heg : ∀ v, eg v ∈ v.adicCompletionIntegers D.host.F := fun v => by
    by_cases hv : P v <;> simp only [eg, hv, if_true, if_false] <;> [exact one_mem _; exact zero_mem _]
  have hfg : ∀ v, fg v ∈ v.adicCompletionIntegers D.host.F := fun v => by
    by_cases hv : P v <;> simp only [fg, hv, if_true, if_false]
    · exact zero_mem _
    · exact mem_of_val (by rw [map_inv₀, hMone v hv, inv_one])
  have hcg : ∀ v, cg v ∈ v.adicCompletionIntegers D.host.F := fun v => by
    by_cases hv : P v <;> simp only [cg, hv, if_true, if_false]
    · exact mem_of_val (hunit v hv).le
    · exact one_mem _
  have hdg : ∀ v, dg v ∈ v.adicCompletionIntegers D.host.F := fun v => by
    by_cases hv : P v <;> simp only [dg, hv, if_true, if_false]
    · exact mem_of_val (by rw [map_inv₀, hunit v hv, inv_one])
    · exact one_mem _
  set e := mkAf eg heg
  set f := mkAf fg hfg
  set c := mkAf cg hcg
  set d := mkAf dg hdg
  have hcd : c * d = 1 := GlobalTheory.SplitHeckeLabel.af_ext fun v => by
    rw [map_mul, map_one, evalV_mkAf, evalV_mkAf]
    by_cases hv : P v <;> simp only [cg, dg, hv, if_true, if_false, mul_one]
    refine mul_inv_cancel₀ fun h0 => ?_
    have := hunit v hv; rw [h0, map_zero] at this; exact zero_ne_one this
  have hef : e + (M : Af D.host.F) * f = 1 := GlobalTheory.SplitHeckeLabel.af_ext fun v => by
    rw [map_add (f := _), map_mul, map_one, map_natCast, evalV_mkAf, evalV_mkAf]
    by_cases hv : P v <;> simp only [eg, fg, hv, if_true, if_false, mul_zero, add_zero, zero_add]
    exact mul_inv_cancel₀ (hMne v hv)
  have hce : c = e * (-(k : Af D.host.F) * T yv) + (M : Af D.host.F) * f := GlobalTheory.SplitHeckeLabel.af_ext fun v => by
    rw [map_add (f := _), map_mul, map_mul, map_mul, map_neg, map_natCast, map_natCast, evalV_mkAf, evalV_mkAf, evalV_mkAf]
    by_cases hv : P v <;> simp only [eg, fg, cg, hv, if_true, if_false, mul_zero, add_zero, zero_add, one_mul, zero_mul]
    exact (mul_inv_cancel₀ (hMne v hv)).symm
  have E1 : ι e + (M : Af D.host.F ⊗[D.host.F] D.host.E) * ι f = 1 := by
    have := congrArg ι hef; rwa [map_add, map_mul, map_natCast, map_one] at this
  have E2 : ι c = ι e * (-(k : Af D.host.F ⊗[D.host.F] D.host.E) * ι (T yv)) + (M : Af D.host.F ⊗[D.host.F] D.host.E) * ι f := by
    rw [hce, map_add (f := _), map_mul, map_mul, map_mul, map_neg, map_natCast, map_natCast]
  have E4 : ι c * ι d = 1 := by rw [← map_mul, hcd, map_one]
  set W := ι e * (yv - (k : Af D.host.F ⊗[D.host.F] D.host.E) * (w * s)) + ι f * (yv - 1) with hW
  have hmain : yv - ι c = (M : Af D.host.F ⊗[D.host.F] D.host.E) * W := by
    have hM : (M : Af D.host.F ⊗[D.host.F] D.host.E) = 2 * (k : Af D.host.F ⊗[D.host.F] D.host.E) + 1 := by
      rw [hMdef]; push_cast; ring
    rw [hW]
    linear_combination (-1 : Af D.host.F ⊗[D.host.F] D.host.E) * E2 - yv * E1 - (k : Af D.host.F ⊗[D.host.F] D.host.E) * ι e * E3 - ι e * yv * hM
  have hWI : W ∈ intAE D := by
    rw [hW]
    refine add_mem (hmulI (hιI _ (mkAf_mem eg heg)) (sub_mem hyI (hmulI (hnI k) (hmulI hwI hsI))))
      (hmulI (hιI _ (mkAf_mem fg hfg)) (sub_mem hyI hoI))
  let b : (Af D.host.F)ˣ := ⟨d, c, by rw [mul_comm]; exact hcd, hcd⟩
  refine ⟨b, y * Units.map ι.toMonoidHom b, ?_, ?_, ?_, W * ι d, ?_, ?_⟩
  · rw [Units.val_mul, Units.coe_map]
    rfl
  · exact hmulI hyI (hιI _ (mkAf_mem dg hdg))
  · rw [mul_inv_rev, Units.val_mul, ← map_inv, Units.coe_map]
    exact hmulI (hιI _ (mkAf_mem cg hcg)) hyiI
  · exact hmulI hWI (hιI _ (mkAf_mem dg hdg))
  · rw [Units.val_mul, Units.coe_map, nsmul_eq_mul]
    show yv * ι d - 1 = _
    linear_combination ι d * hmain + E4

end GlobalTheory.UnitRootCong
end
end

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistRat.Right
variable {D : D7}

def iI (F : Type) [Field F] [NumberField F] : Ainf F →ₗ[F] AF F where
  toFun x := ((x, 0) : Ainf F × Af F)
  map_add' x y := by
    show ((x + y, 0) : Ainf F × Af F) = ((x, 0) : Ainf F × Af F) + ((y, 0) : Ainf F × Af F)
    rw [Prod.mk_add_mk, add_zero]
  map_smul' c x := by
    apply Prod.ext
    · show c • x = (c • ((x, 0) : AF F)).1
      rfl
    · show (0 : Af F) = (c • ((x, 0) : AF F)).2
      show (0 : Af F) = algebraMap F (Af F) c * 0
      simp

def iF (F : Type) [Field F] [NumberField F] : Af F →ₗ[F] AF F where
  toFun x := ((0, x) : Ainf F × Af F)
  map_add' x y := by
    show ((0, x + y) : Ainf F × Af F) = ((0, x) : Ainf F × Af F) + ((0, y) : Ainf F × Af F)
    rw [Prod.mk_add_mk, add_zero]
  map_smul' c x := by
    apply Prod.ext
    · show (0 : Ainf F) = (c • ((0, x) : AF F)).1
      first
        | (show (0 : Ainf F) = c • (0 : Ainf F); simp)
        | (show (0 : Ainf F) = algebraMap F (Ainf F) c * 0; simp)
        | (show (0 : Ainf F) = (algebraMap F (AF F) c * ((0, x) : AF F)).1; show (0 : Ainf F) = (algebraMap F (AF F) c).1 * 0; simp)
    · show c • x = (c • ((0, x) : AF F)).2
      rfl

def jI (D : D7) : Ainf D.host.F ⊗[D.host.F] D.host.E →ₗ[D.host.F] AE D := TensorProduct.map (iI D.host.F) LinearMap.id
def jF (D : D7) : Af D.host.F ⊗[D.host.F] D.host.E →ₗ[D.host.F] AE D := TensorProduct.map (iF D.host.F) LinearMap.id

theorem recon (x : AE D) : jI D (infPart D x) + jF D (finPart D x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul p q =>
    show iI D.host.F (fstA D.host.F p) ⊗ₜ q + iF D.host.F (sndA D.host.F p) ⊗ₜ q = p ⊗ₜ q
    rw [← TensorProduct.add_tmul]
    congr 1
    show ((p.1, 0) : Ainf D.host.F × Af D.host.F) + ((0, p.2) : Ainf D.host.F × Af D.host.F) = p
    rw [Prod.mk_add_mk, add_zero, zero_add]
    rfl
  | add p q hp hq =>
    rw [RingHom.map_add (f := _), RingHom.map_add (f := _), LinearMap.map_add (f := _), LinearMap.map_add (f := _)]
    conv_rhs => rw [← hp, ← hq]
    abel

theorem infPart_jI (a : Ainf D.host.F ⊗[D.host.F] D.host.E) : infPart D (jI D a) = a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul p q => rfl
  | add p q hp hq => rw [LinearMap.map_add (f := _), RingHom.map_add (f := _), hp, hq]

theorem finPart_jI (a : Ainf D.host.F ⊗[D.host.F] D.host.E) : finPart D (jI D a) = 0 := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul p q =>
    show (sndA D.host.F (iI D.host.F p)) ⊗ₜ[D.host.F] q = 0
    show (0 : Af D.host.F) ⊗ₜ[D.host.F] q = 0
    exact TensorProduct.zero_tmul _ _
  | add p q hp hq => rw [LinearMap.map_add (f := _), RingHom.map_add (f := _), hp, hq, add_zero]

theorem infPart_jF (b : Af D.host.F ⊗[D.host.F] D.host.E) : infPart D (jF D b) = 0 := by
  induction b using TensorProduct.induction_on with
  | zero => simp
  | tmul p q =>
    show (fstA D.host.F (iF D.host.F p)) ⊗ₜ[D.host.F] q = 0
    show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] q = 0
    exact TensorProduct.zero_tmul _ _
  | add p q hp hq => rw [LinearMap.map_add (f := _), RingHom.map_add (f := _), hp, hq, add_zero]

theorem finPart_jF (b : Af D.host.F ⊗[D.host.F] D.host.E) : finPart D (jF D b) = b := by
  induction b using TensorProduct.induction_on with
  | zero => simp
  | tmul p q => rfl
  | add p q hp hq => rw [LinearMap.map_add (f := _), RingHom.map_add (f := _), hp, hq]

theorem ext_parts {a b : AE D} (h1 : infPart D a = infPart D b) (h2 : finPart D a = finPart D b) : a = b := by
  rw [← recon a, ← recon b, h1, h2]

theorem exists_unit_parts (a : (Ainf D.host.F ⊗[D.host.F] D.host.E)ˣ) (b : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) :
    ∃ Y : (AE D)ˣ, infPart D (Y : AE D) = a ∧ finPart D (Y : AE D) = b := by
  have hI : ∀ a' b', infPart D (jI D a' + jF D b') = a' := fun a' b' => by
    rw [RingHom.map_add (f := _), infPart_jI, infPart_jF, add_zero]
  have hF : ∀ a' b', finPart D (jI D a' + jF D b') = b' := fun a' b' => by
    rw [RingHom.map_add (f := _), finPart_jI, finPart_jF, zero_add]
  have h1 : (jI D (a : _) + jF D (b : _)) * (jI D ((a⁻¹ : (Ainf D.host.F ⊗[D.host.F] D.host.E)ˣ) : _) +
      jF D ((b⁻¹ : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : _)) = 1 := by
    apply ext_parts
    · rw [RingHom.map_mul, hI, hI, Units.mul_inv, RingHom.map_one]
    · rw [RingHom.map_mul, hF, hF, Units.mul_inv, RingHom.map_one]
  exact ⟨⟨_, _, h1, by rw [mul_comm]; exact h1⟩, hI _ _, hF _ _⟩

end GlobalTheory.TwistRat.Right

namespace GlobalTheory.TwistRat.Right
variable {D : D7}

theorem char_arch_one {c : (AE D)ˣ →* Circle} {χ : Formalism.L2.Host.HChar D.host.E} (h : ChrEq c χ) {n : ℕ} (hn : 0 < n)
    (ho : χ.OrderDvd n) (x : (AE D)ˣ) (hx : finPart D (x : AE D) = 1) : c x = 1 := by
  have key := GlobalTheory.HeckeFinTrivial.eq_one_of_trivial_on_finite D (c ^ n)
    ⟨h.1.1.pow n, fun x => by rw [MonoidHom.pow_apply, h.1.2 x, one_pow]⟩
    (GlobalTheory.CharOrderFin.char_pow_eq_one_of_orderDvd D c χ h n ho)
  obtain ⟨y, rfl⟩ := GlobalTheory.IdeleDiv.exists_pow_eq_of_finPart_eq_one D n hn x hx
  rw [map_pow]
  exact key y

theorem isDetRoot_mul {V : HSp D} {g g' : GA D V} {x x' : (AE D)ˣ} (h : IsDetRoot V g x) (h' : IsDetRoot V g' x') :
    IsDetRoot V (g * g') (x * x') := by
  unfold IsDetRoot at *
  rw [map_mul, Units.val_mul, Units.val_mul, Matrix.det_mul, RingHom.map_mul]
  conv_lhs => rw [h, h']
  ring

end GlobalTheory.TwistRat.Right

namespace GlobalTheory.TwistRat.Right
variable {D : D7}
theorem infPart_sigR (x : AE D) : infPart D (sigR (AF D.host.F) D.sp.cm.sig x) = sigR (Ainf D.host.F) D.sp.cm.sig (infPart D x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul p q => rfl
  | add p q hp hq => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), hp, hq, RingHom.map_add (f := _), RingHom.map_add (f := _)]
theorem finPart_sigR (x : AE D) : finPart D (sigR (AF D.host.F) D.sp.cm.sig x) = sigR (Af D.host.F) D.sp.cm.sig (finPart D x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul p q => rfl
  | add p q hp hq => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), hp, hq, RingHom.map_add (f := _), RingHom.map_add (f := _)]
theorem sigR_tmul_one (b : Af D.host.F) : sigR (Af D.host.F) D.sp.cm.sig (b ⊗ₜ[D.host.F] (1 : D.host.E)) = b ⊗ₜ[D.host.F] (1 : D.host.E) := by
  show b ⊗ₜ[D.host.F] D.sp.cm.sig 1 = _
  rw [map_one]
theorem adelicCompletion_integers_le_intAE (w) (hw : w ∈ GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E))) : w ∈ intAE D := by
  refine (AddSubgroup.closure_le _).2 ?_ hw
  rintro _ ⟨a, ha, _, ⟨r, rfl⟩, rfl⟩
  exact AddSubgroup.subset_closure ⟨a, ha, r, rfl⟩
theorem one_mem_intAE : (1 : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D :=
  AddSubgroup.subset_closure ⟨1, fun v => by simp [evalV], 1, by simp; rfl⟩
theorem finPart_det (V : HSp D) (u : GA D V) :
    finPart D (matHom V u).1.det = (finHom V u).1.det := by
  rw [RingHom.map_det]
  rfl
end GlobalTheory.TwistRat.Right

namespace GlobalTheory.TwistRat.Right


set_option maxHeartbeats 1600000 in
theorem exists_root_one {D : D7} {V : HSp D} {M pd : ℕ} {k : Type} [Field k] {σ : k →+* ℂ}
    {δ : Formalism.L2.Host.HChar D.host.E} {δc : (AE D)ˣ →* Circle} (hA : IsAuxiliarySplitSquarefreeLevel D M pd) (hT : IsTwist pd σ δ δc)
    {u : GA D V} (hu : GlobalTheory.Member.FinCong V (M * pd) u) (y₀ : (AE D)ˣ) (hy₀ : IsDetRoot V u y₀) :
    ∃ y, IsDetRoot V u y ∧ δc y = 1 := by
  obtain ⟨hc, ⟨n, hn, ho⟩, -, ht, hunr, -⟩ := hT
  have hpd : pd ≠ 0 := fun h => by simpa [h] using hA.1
  have hu' : GlobalTheory.Member.FinCong V pd u := fun z hz => by
    obtain ⟨y, hy, e⟩ := hu z hz
    exact ⟨M • y, AddSubgroup.nsmul_mem _ hy M, by rw [e, mul_comm, mul_nsmul]; exact smul_comm M pd y⟩
  obtain ⟨w, hw, hzw⟩ := GlobalTheory.DetFibre.det_cong_of_finCong V pd hpd u hu'
  have hw' := adelicCompletion_integers_le_intAE w hw
  obtain ⟨zf, hzf⟩ : ∃ zf : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ, (zf : Af D.host.F ⊗[D.host.F] D.host.E) = (finHom V u).1.det :=
    ⟨Units.map (finPart D).toMonoidHom (Matrix.GeneralLinearGroup.det (matHom V u)), finPart_det V u⟩
  have hcong : (zf : Af D.host.F ⊗[D.host.F] D.host.E) - 1 = pd • w := by rw [hzf]; exact hzw
  have hzint : (zf : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D := by
    rw [← sub_add_cancel (zf : Af D.host.F ⊗[D.host.F] D.host.E) 1, hcong]
    exact add_mem (AddSubgroup.nsmul_mem _ hw' pd) one_mem_intAE
  have hroot : (Units.map (finPart D).toMonoidHom y₀ : Af D.host.F ⊗[D.host.F] D.host.E) =
      zf * sigR (Af D.host.F) D.sp.cm.sig (Units.map (finPart D).toMonoidHom y₀ : Af D.host.F ⊗[D.host.F] D.host.E) := by
    show finPart D (y₀ : AE D) = _ * sigR (Af D.host.F) D.sp.cm.sig (finPart D (y₀ : AE D))
    rw [hzf, ← finPart_det, ← finPart_sigR, ← RingHom.map_mul]
    exact congrArg (finPart D) hy₀
  obtain ⟨y₁, hy₁, hy₁', hy₁r⟩ := GlobalTheory.IntegralHilbertNinety.exists_int_unit_root D zf hzint ⟨_, hroot⟩
  obtain ⟨b, y₂, hy₂, hy₂i, hy₂i', w₂, hw₂, hy₂c⟩ := GlobalTheory.UnitRootCong.exists_adele_unit_congr_one D pd hA.1 zf y₁ hy₁ hy₁' hy₁r ⟨w, hw', hcong⟩
  obtain ⟨Yf, hYf1, hYf2⟩ := exists_unit_parts (D := D) 1 y₂
  obtain ⟨Yi, hYi1, hYi2⟩ := exists_unit_parts (D := D) (Units.map (infPart D).toMonoidHom y₀) 1
  have hYI : infPart D ((Yf * Yi : (AE D)ˣ) : AE D) = infPart D (y₀ : AE D) := by
    simp only [Units.val_mul, RingHom.map_mul, hYf1, hYi1, Units.val_one, one_mul]
    rfl
  have hYF : finPart D ((Yf * Yi : (AE D)ˣ) : AE D) = (y₂ : Af D.host.F ⊗[D.host.F] D.host.E) := by
    simp only [Units.val_mul, RingHom.map_mul, hYf2, hYi2, Units.val_one, mul_one]
  refine ⟨Yf * Yi, ?_, ?_⟩
  · unfold IsDetRoot
    generalize ((Yf * Yi : (AE D)ˣ) : AE D) = Y at hYI hYF ⊢
    apply ext_parts
    · calc infPart D Y = infPart D (y₀ : AE D) := hYI
        _ = infPart D ((matHom V u).1.det * sigR (AF D.host.F) D.sp.cm.sig (y₀ : AE D)) := congrArg (infPart D) hy₀
        _ = infPart D (matHom V u).1.det * infPart D (sigR (AF D.host.F) D.sp.cm.sig (y₀ : AE D)) := (infPart D).map_mul _ _
        _ = infPart D (matHom V u).1.det * sigR (Ainf D.host.F) D.sp.cm.sig (infPart D (y₀ : AE D)) :=
          congrArg (infPart D (matHom V u).1.det * ·) (infPart_sigR _)
        _ = infPart D (matHom V u).1.det * sigR (Ainf D.host.F) D.sp.cm.sig (infPart D Y) :=
          congrArg (fun t => infPart D (matHom V u).1.det * sigR (Ainf D.host.F) D.sp.cm.sig t) hYI.symm
        _ = infPart D (matHom V u).1.det * infPart D (sigR (AF D.host.F) D.sp.cm.sig Y) :=
          congrArg (infPart D (matHom V u).1.det * ·) (infPart_sigR _).symm
        _ = infPart D ((matHom V u).1.det * sigR (AF D.host.F) D.sp.cm.sig Y) := ((infPart D).map_mul _ _).symm
    · have e2 : (y₂ : Af D.host.F ⊗[D.host.F] D.host.E) = zf * sigR (Af D.host.F) D.sp.cm.sig (y₂ : Af D.host.F ⊗[D.host.F] D.host.E) := by
        rw [hy₂, (sigR (Af D.host.F) D.sp.cm.sig).map_mul, sigR_tmul_one, ← mul_assoc, ← hy₁r]
      calc finPart D Y = (y₂ : Af D.host.F ⊗[D.host.F] D.host.E) := hYF
        _ = zf * sigR (Af D.host.F) D.sp.cm.sig (y₂ : Af D.host.F ⊗[D.host.F] D.host.E) := e2
        _ = finPart D (matHom V u).1.det * sigR (Af D.host.F) D.sp.cm.sig (finPart D Y) := by
          rw [hzf, ← finPart_det, hYF]
        _ = finPart D (matHom V u).1.det * finPart D (sigR (AF D.host.F) D.sp.cm.sig Y) :=
          congrArg (finPart D (matHom V u).1.det * ·) (finPart_sigR _).symm
        _ = finPart D ((matHom V u).1.det * sigR (AF D.host.F) D.sp.cm.sig Y) := ((finPart D).map_mul _ _).symm
  · have h1 : δc Yf = 1 := by
      refine GlobalTheory.tame_heckeChar_eq_one_of_finUnit D δc δ hc ht pd hunr Yf ⟨?_, ?_, ?_⟩ ⟨w₂, hw₂, by rw [hYf2]; exact hy₂c⟩
      · rw [hYf1]; rfl
      · rw [hYf2]; exact hy₂i
      · have hU : Units.map (finPart D).toMonoidHom Yf = y₂ := Units.ext hYf2
        have e : finPart D ((Yf⁻¹ : (AE D)ˣ) : AE D) = ((y₂⁻¹ : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : _) := by
          rw [← hU, ← MonoidHom.map_inv]
          rfl
        rw [e]; exact hy₂i'
    have h2 : δc Yi = 1 := char_arch_one hc hn ho Yi (by rw [hYi2]; rfl)
    rw [map_mul, h1, h2, mul_one]

theorem dd_mul_right : ∀ (D : D7) (V : HSp D) (M pd : ℕ) (k : Type) [Field k] (σ : k →+* ℂ) (δ : Formalism.L2.Host.HChar D.host.E) (δc : (AE D)ˣ →* Circle), IsAuxiliarySplitSquarefreeLevel D M pd → IsTwist pd σ δ δc → ∀ dd : GA D V → ℂ, (MuVal V δc dd ∨ MuVal V δc⁻¹ dd) → ∀ u : GA D V, Formalism.L2.Pj.gLat V u = ↑(Formalism.L2.Pj.latHat V) → GlobalTheory.Member.FinCong V (M * pd) u → ∀ h : GA D V, dd (h * u) = dd h := by
  intro D V M pd k _ σ δ δc hA hT dd hdd u _ hu h
  have main : ∀ χ : (AE D)ˣ →* Circle, MuVal V χ dd → (∀ y, δc y = 1 → χ y = 1) → dd (h * u) = dd h := by
    intro χ hχ hχδ
    obtain ⟨x, hx⟩ := hχ.1 h
    obtain ⟨y₀, hy₀⟩ := hχ.1 u
    obtain ⟨y, hy, hy1⟩ := exists_root_one hA hT hu y₀ hy₀
    rw [hχ.2 _ _ (isDetRoot_mul hx hy), hχ.2 h x hx, map_mul, hχδ y hy1, mul_one]
  rcases hdd with hd | hd
  · exact main δc hd fun y hy => hy
  · exact main δc⁻¹ hd fun y hy => by rw [MonoidHom.inv_apply, hy, inv_one]

end GlobalTheory.TwistRat.Right
