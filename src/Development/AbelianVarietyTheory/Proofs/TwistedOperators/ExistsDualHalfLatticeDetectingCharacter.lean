module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteThetaLiftLocalVector
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNsmulMemStdHom

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDualElementStandardCharSplitPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDualElementStandardCharSplitPrime
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical

noncomputable section

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.SplitDualElt

open GlobalTheory.IdemModTwo GlobalTheory.SplitChart

variable {D : D7}

def lift (D : D7) (r : Formalism.IndefR.Datum.EAf D) : AE D :=
  GlobalTheory.LatticeStable.liftFin D ((Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).symm r)

theorem toEAf_lift (r : Formalism.IndefR.Datum.EAf D) : toEAf D (lift D r) = r := GlobalTheory.AdForm.toEAf_liftFin r

theorem lift_add (r s : Formalism.IndefR.Datum.EAf D) : lift D (r + s) = lift D r + lift D s := by
  unfold lift
  rw [map_add (f := _), map_add (f := _)]

theorem finPart_eq_zero_of_toEAf {z : AE D} (h : toEAf D z = 0) : finPart D z = 0 := by
  rw [GlobalTheory.AdForm.toEAf_eq_comm] at h
  exact (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).injective (h.trans (map_zero _).symm)

theorem eq_of_toEAf {x y : AE D} (hx : infPart D x = 0) (hy : infPart D y = 0) (h : toEAf D x = toEAf D y) : x = y := by
  refine sub_eq_zero.1 (GlobalTheory.LatVac.eq_zero_of_parts _ ?_ ?_)
  · rw [RingHom.map_sub, hx, hy, sub_zero]
  · exact finPart_eq_zero_of_toEAf (by rw [RingHom.map_sub, h, sub_self])

theorem infPart_fj (α : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) : infPart D (fj D α) = 0 := by
  show (fstA D.host.F (pairA D.host.F 0 α)) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
  have : fstA D.host.F (pairA D.host.F 0 α) = 0 := rfl
  rw [this, TensorProduct.zero_tmul]

variable {v : HeightOneSpectrum (𝓞 D.host.F)} {e : AE D}

theorem infPart_idem (he : SplitAt D v e) : infPart D e = 0 := by
  rw [← he.pl_mul, map_mul, infPart_fj, zero_mul]

theorem comp_eq_of_toEAf (he : SplitAt D v e) {x y : AE D} (h : toEAf D x = toEAf D y) :
    comp he x = comp he y := by
  rw [← sub_eq_zero, ← RingHom.map_sub]
  refine ((chart_comp he).2.1 _).2 ?_
  refine GlobalTheory.LatVac.eq_zero_of_parts _ ?_ ?_
  · rw [RingHom.map_mul, infPart_idem he, zero_mul]
  · rw [RingHom.map_mul, finPart_eq_zero_of_toEAf (z := x - y) (by rw [RingHom.map_sub, h, sub_self]), mul_zero]

theorem infPart_sec (a : Fv D.host.F v) : infPart D (GlobalTheory.FinPl.SplitPoint.sec D v e a) = 0 := by
  rw [GlobalTheory.FinPl.SplitPoint.sec_apply, map_mul, infPart_fj, zero_mul]

theorem comp_sec (he : SplitAt D v e) (a : Fv D.host.F v) : comp he (GlobalTheory.FinPl.SplitPoint.sec D v e a) = a := by
  rw [GlobalTheory.FinPl.SplitPoint.sec_apply, map_mul, comp_fj, comp_self, mul_one, GlobalTheory.SplitIdem.evalV_singleV_same]

theorem sec_comp (he : SplitAt D v e) (z : AE D) : GlobalTheory.FinPl.SplitPoint.sec D v e (comp he z) = e * z := by
  rw [GlobalTheory.FinPl.SplitPoint.sec_apply, sc_spec he z]
  rfl

theorem le_exp_neg_one {x : WithZero (Multiplicative ℤ)} (hx : x < 1) : x ≤ WithZero.exp (-1) := by
  rcases eq_or_ne x 0 with rfl | h0
  · exact zero_le'
  · rw [← WithZero.exp_log h0] at hx ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hx
    exact WithZero.exp_le_exp.2 (by omega)

end GlobalTheory.SplitDualElt

namespace GlobalTheory.SplitDualElt

open GlobalTheory.IdemModTwo GlobalTheory.SplitChart

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {e : AE D}

theorem comp_lift_mul (he : SplitAt D v e) (r s : Formalism.IndefR.Datum.EAf D) :
    comp he (lift D (r * s)) = comp he (lift D r) * comp he (lift D s) := by
  rw [← RingHom.map_mul]
  exact comp_eq_of_toEAf he (by rw [RingHom.map_mul, toEAf_lift, toEAf_lift, toEAf_lift])

theorem comp_lift_add (he : SplitAt D v e) (r s : Formalism.IndefR.Datum.EAf D) :
    comp he (lift D (r + s)) = comp he (lift D r) + comp he (lift D s) := by
  rw [lift_add, RingHom.map_add (f := _)]

theorem val_lt_one (PP : Pl D.host.E) (hI : Formalism.L2.NTheta.IsIdemAt e PP) (he : SplitAt D v e)
    (r : Formalism.L2.Herm.intAf D.host.F D.host.E) (hr : Formalism.L2.DIV.resS D.host.F PP r = 0) :
    Valued.v (comp he (lift D (r : Formalism.IndefR.Datum.EAf D))) < 1 := by
  have hmem : r ∈ Formalism.L2.DIV.idS D.host.F PP.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact (map_eq_zero_iff _ (RingEquiv.ofBijective (Formalism.L2.DIV.cmpS D.host.F PP.asIdeal)
      (Formalism.L2.DIV.cmpS_bij (F := D.host.F) PP.asIdeal PP.ne_bot)).symm.injective).1 hr
  have he1 : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := (GlobalTheory.IdemRes.resS_idem_eq_one D e PP hI).1
  have hint : ∀ s : Formalism.L2.Herm.intAf D.host.F D.host.E,
      comp he (lift D (s : Formalism.IndefR.Datum.EAf D)) ∈ v.adicCompletionIntegers D.host.F := by
    intro s
    refine GlobalTheory.SplitHecke.isInt_Ov.1 (((chart_comp he).2.2.2 _).1 ?_)
    refine GlobalTheory.PlaceDatum.finPart_mem_of_toEAf ?_
    rw [RingHom.map_mul, toEAf_lift]
    exact mul_mem he1 s.2
  let I : Ideal (Formalism.L2.Herm.intAf D.host.F D.host.E) :=
    { carrier := {s | Valued.v (comp he (lift D (s : Formalism.IndefR.Datum.EAf D))) < 1}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq, Subring.coe_add, comp_lift_add] at ha hb ⊢
        exact Valuation.map_add_lt _ ha hb
      zero_mem' := by
        simp only [Set.mem_setOf_eq, ZeroMemClass.coe_zero]
        have : lift D (0 : Formalism.IndefR.Datum.EAf D) = 0 := by
          have h := lift_add (D := D) 0 0
          rw [add_zero] at h
          exact left_eq_add.1 h
        rw [this, RingHom.map_zero, Valuation.map_zero]
        exact zero_lt_one
      smul_mem' := by
        intro c a ha
        simp only [Set.mem_setOf_eq, smul_eq_mul, Subring.coe_mul, comp_lift_mul] at ha ⊢
        rw [Valuation.map_mul]
        have hc := hint c
        rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hc
        exact (mul_le_of_le_one_left' hc).trans_lt ha }
  have hle : Formalism.L2.DIV.idS D.host.F PP.asIdeal ≤ I := by
    refine Ideal.map_le_iff_le_comap.2 fun p hp => ?_
    show Valued.v (comp he (lift D ((Formalism.L2.DIV.oToS D.host.F D.host.E p : Formalism.L2.Herm.intAf D.host.F D.host.E) :
      Formalism.IndefR.Datum.EAf D))) < 1
    rcases eq_or_ne p 0 with rfl | hp0
    · rw [map_zero]
      have : lift D (0 : Formalism.IndefR.Datum.EAf D) = 0 := by
        have h := lift_add (D := D) 0 0
        rw [add_zero] at h
        exact left_eq_add.1 h
      rw [ZeroMemClass.coe_zero, this, RingHom.map_zero, Valuation.map_zero]
      exact zero_lt_one
    have hx : comp he (lift D ((Formalism.L2.DIV.oToS D.host.F D.host.E p : Formalism.L2.Herm.intAf D.host.F D.host.E) :
        Formalism.IndefR.Datum.EAf D)) = comp he (incA D (p : D.host.E)) :=
      comp_eq_of_toEAf he (by rw [toEAf_lift, Formalism.L2.DIV.oToS_coe]; rfl)
    rw [hx]
    have hx0 : (p : D.host.E) ≠ 0 := fun h => hp0 (RingOfIntegers.coe_eq_zero_iff.1 h)
    have h1 : comp he (incA D (p : D.host.E)) ∈ v.adicCompletionIntegers D.host.F := by
      refine GlobalTheory.SplitHecke.isInt_Ov.1 (((chart_comp he).2.2.2 _).1 ?_)
      refine GlobalTheory.PlaceDatum.finPart_mem_of_toEAf ?_
      rw [RingHom.map_mul]
      refine mul_mem he1 ?_
      have : toEAf D (incA D (p : D.host.E)) = ((Formalism.L2.DIV.oToS D.host.F D.host.E p : Formalism.L2.Herm.intAf D.host.F D.host.E) :
        Formalism.IndefR.Datum.EAf D) := by rw [Formalism.L2.DIV.oToS_coe]; rfl
      rw [this]
      exact Subtype.prop _
    have h2 : comp he (incA D (p : D.host.E)⁻¹) ∉ v.adicCompletionIntegers D.host.F := by
      intro h
      exact (hI.2 p hp0).1 hp (((chart_comp he).2.2.2 _).2 (GlobalTheory.SplitHecke.isInt_Ov.2 h))
    have h3 : comp he (incA D (p : D.host.E)) * comp he (incA D (p : D.host.E)⁻¹) = 1 := by
      rw [← RingHom.map_mul, ← RingHom.map_mul, mul_inv_cancel₀ hx0, RingHom.map_one, RingHom.map_one]
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h1 h2
    by_contra hn
    have ha : Valued.v (comp he (incA D (p : D.host.E))) = 1 := le_antisymm h1 (not_lt.1 hn)
    have hb := congrArg Valued.v h3
    rw [Valuation.map_mul, ha, one_mul, Valuation.map_one] at hb
    exact h2 hb.le
  exact hle hmem

end GlobalTheory.SplitDualElt

namespace GlobalTheory.SplitDualElt

open GlobalTheory.IdemModTwo GlobalTheory.SplitChart

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {e : AE D}


set_option maxHeartbeats 1000000 in
theorem trace_generator_split_section (he : SplitAt D v e) (a : Fv D.host.F v) :
    Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * GlobalTheory.FinPl.SplitPoint.sec D v e a) =
      pairA D.host.F 0 (singleV D.host.F v (comp he (incA D D.host.xi0) * a)) := by
  apply tmul_one_inj (F := D.host.F) (A := AF D.host.F) (E := D.host.E)
  change algebraMap (AF D.host.F) (AE D) (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * GlobalTheory.FinPl.SplitPoint.sec D v e a)) =
    fj D (singleV D.host.F v (comp he (incA D D.host.xi0) * a))
  rw [GlobalTheory.FockCompare.SymplVal.trace_AE, GlobalTheory.FinPl.SplitPoint.sec_apply]
  have h1 : e * incA D D.host.xi0 = fj D (singleV D.host.F v (comp he (incA D D.host.xi0))) * e := sc_spec he _
  have h2 : singleV D.host.F v a * singleV D.host.F v (comp he (incA D D.host.xi0)) * singleV D.host.F v 1 =
      singleV D.host.F v (comp he (incA D D.host.xi0) * a) := by
    rw [singleV_mul D v _ (singleV D.host.F v a), GlobalTheory.SplitIdem.evalV_singleV_same, singleV_mul D v 1,
      GlobalTheory.SplitIdem.evalV_singleV_same, mul_one, mul_comm]
  calc incA D D.host.xi0 * (fj D (singleV D.host.F v a) * e) + cA D (incA D D.host.xi0 * (fj D (singleV D.host.F v a) * e))
      = fj D (singleV D.host.F v a) * (e * incA D D.host.xi0) +
          cA D (fj D (singleV D.host.F v a) * (e * incA D D.host.xi0)) := by
        rw [mul_comm (incA D D.host.xi0), mul_assoc]
    _ = fj D (singleV D.host.F v a) * fj D (singleV D.host.F v (comp he (incA D D.host.xi0))) * (e + cA D e) := by
        rw [h1, RingHom.map_mul, RingHom.map_mul, cA_fj, cA_fj, ← mul_add, ← mul_add, ← mul_assoc]
    _ = fj D (singleV D.host.F v (comp he (incA D D.host.xi0) * a)) := by
        have h3 : e + cA D e = fj D (singleV D.host.F v 1) := he.2.2
        rw [h3, ← map_mul (fj D) (singleV D.host.F v a), ← map_mul (fj D) (singleV D.host.F v a * singleV D.host.F v (comp he (incA D D.host.xi0))) (singleV D.host.F v 1), h2]

end GlobalTheory.SplitDualElt

namespace GlobalTheory.SplitDualElt

open GlobalTheory.IdemModTwo GlobalTheory.SplitChart

theorem exists_edge {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (χ : AddChar (v.adicCompletion F) ℂ)
    (hχ : Continuous χ) (hne : ∃ a, χ a ≠ 1) :
    ∃ c₀ : v.adicCompletion F, χ c₀ ≠ 1 ∧ ∀ m : v.adicCompletion F, Valued.v m < 1 → χ (c₀ * m) = 1 := by
  obtain ⟨n, hn⟩ := GlobalTheory.CharConductor.exists_exponent_of_valued χ hχ hne
  obtain ⟨ϖ, hϖ⟩ := HeightOneSpectrum.valuation_exists_uniformizer F v
  have hv : Valued.v (ϖ : v.adicCompletion F) = WithZero.exp (-1) := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hϖ]
  set t₀ : v.adicCompletion F := (ϖ : v.adicCompletion F) ^ (-(n + 1)) with ht₀
  have hvt : Valued.v t₀ = WithZero.exp (n + 1) := by
    rw [ht₀, map_zpow₀, hv, ← WithZero.exp_zsmul]
    congr 1
    simp
  have hnot : ¬ Valued.v t₀ ≤ WithZero.exp n := by
    rw [hvt, WithZero.exp_le_exp]
    omega
  obtain ⟨s, hs1, hs⟩ : ∃ s : v.adicCompletion F, Valued.v s ≤ 1 ∧ χ (t₀ * s) ≠ 1 := by
    by_contra h
    push_neg at h
    exact hnot ((hn t₀).1 h)
  refine ⟨t₀ * s, hs, fun m hm => ?_⟩
  have hm' := le_exp_neg_one hm
  have hle : Valued.v (t₀ * s * m) ≤ WithZero.exp n := by
    rw [map_mul, map_mul, hvt]
    calc WithZero.exp (n + 1) * Valued.v s * Valued.v m ≤ WithZero.exp (n + 1) * 1 * WithZero.exp (-1) :=
          mul_le_mul' (mul_le_mul' le_rfl hs1) hm'
      _ = WithZero.exp n := by rw [mul_one, ← WithZero.exp_add]; congr 1; ring
  have := (hn (t₀ * s * m)).2 hle 1 (by rw [map_one])
  rwa [mul_one] at this

end GlobalTheory.SplitDualElt

namespace GlobalTheory.SplitDualElt

open GlobalTheory.IdemModTwo GlobalTheory.SplitChart


set_option maxHeartbeats 1000000 in
theorem exists_dual_elt : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (e₁ : AE D) (PP : Pl D.host.E), Formalism.L2.NTheta.IsIdemAt e₁ PP → ∃ c : Datum.EAf D, (∀ Z : AE D, infPart D Z = 0 → ∀ r : Formalism.L2.Herm.intAf D.host.F D.host.E, resS D.host.F PP r = 0 → toEAf D Z = c * r → ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * Z)) = 1) ∧ (∀ Z : AE D, infPart D Z = 0 → toEAf D Z = c → ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * Z)) ≠ 1) := by
  intro D ψ hψ e PP hI
  obtain ⟨v, he⟩ := (isSplitIdem_iff e).1 hI.1
  let T : AE D →+ AF D.host.F :=
    (Algebra.trace (AF D.host.F) (AE D)).toAddMonoidHom.comp (AddMonoidHom.mulLeft (incA D D.host.xi0))
  let χ : AddChar (Fv D.host.F v) ℂ := ψ.compAddMonoidHom (T.comp (GlobalTheory.FinPl.SplitPoint.sec D v e))
  have hχa : ∀ a, χ a = ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * GlobalTheory.FinPl.SplitPoint.sec D v e a)) :=
    fun a => rfl
  have hχ : Continuous χ :=
    hψ.1.1.comp ((GlobalTheory.Core.Rk.SplitPsi.continuous_trace_mul D (incA D D.host.xi0)).comp
      GlobalTheory.FinPl.SplitPoint.continuous_sec)
  have hκ : comp he (incA D D.host.xi0) ≠ 0 := by
    intro h0
    have h1 : comp he (incA D D.host.xi0) * comp he (incA D D.host.xi0⁻¹) = 1 := by
      rw [← RingHom.map_mul, ← RingHom.map_mul, mul_inv_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), RingHom.map_one,
        RingHom.map_one]
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  have hne : ∃ a, χ a ≠ 1 := by
    obtain ⟨y, hy⟩ := GlobalTheory.StdCharLocal.psiV_ne_one D ψ hψ v
    refine ⟨(comp he (incA D D.host.xi0))⁻¹ * y, ?_⟩
    rw [hχa, trace_generator_split_section he, mul_inv_cancel_left₀ hκ]
    exact hy
  obtain ⟨c₀, hc₀, hc₀m⟩ := exists_edge v χ hχ hne
  refine ⟨toEAf D (GlobalTheory.FinPl.SplitPoint.sec D v e c₀), ?_, ?_⟩
  · intro Z hZ r hr hZr
    have hZ' : Z = GlobalTheory.FinPl.SplitPoint.sec D v e c₀ * lift D (r : Formalism.IndefR.Datum.EAf D) :=
      eq_of_toEAf hZ (by rw [RingHom.map_mul, infPart_sec, zero_mul])
        (by rw [hZr, RingHom.map_mul, toEAf_lift])
    have heZ : e * Z = Z := by
      rw [hZ', GlobalTheory.FinPl.SplitPoint.sec_apply]
      generalize fj D (singleV D.host.F v c₀) = f
      generalize lift D (r : Formalism.IndefR.Datum.EAf D) = R
      rw [← mul_assoc, ← mul_assoc, mul_comm e f, mul_assoc f e e, he.1]
    have hsec : GlobalTheory.FinPl.SplitPoint.sec D v e (comp he Z) = Z := by
      rw [sec_comp he, heZ]
    have hcomp : comp he Z = c₀ * comp he (lift D (r : Formalism.IndefR.Datum.EAf D)) := by
      rw [hZ', RingHom.map_mul, comp_sec he]
    have h := hc₀m _ (val_lt_one PP hI he r hr)
    rw [← hcomp, hχa, hsec] at h
    exact h
  · intro Z hZ hZc
    have hZ' : Z = GlobalTheory.FinPl.SplitPoint.sec D v e c₀ := eq_of_toEAf hZ (infPart_sec c₀) hZc
    rw [hZ', ← hχa]
    exact hc₀

end GlobalTheory.SplitDualElt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDualElementStandardCharSplitPrimeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dualElement_standardChar_splitPrime : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (e₁ : AE D) (PP : Pl D.host.E), Formalism.L2.NTheta.IsIdemAt e₁ PP → ∃ c : Datum.EAf D, (∀ Z : AE D, infPart D Z = 0 → ∀ r : Formalism.L2.Herm.intAf D.host.F D.host.E, resS D.host.F PP r = 0 → toEAf D Z = c * r → ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * Z)) = 1) ∧ (∀ Z : AE D, infPart D Z = 0 → toEAf D Z = c → ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * Z)) ≠ 1) := by
  first | exact @GlobalTheory.SplitDualElt.exists_dual_elt | exact GlobalTheory.SplitDualElt.exists_dual_elt | (intros; apply GlobalTheory.SplitDualElt.exists_dual_elt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDualHalfLatticeDetectingCharacter
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical

namespace GlobalTheory.HalfDuality

variable {D : D7}

theorem exists_lift (t : Datum.EAf D) : ∃ Z : AE D, infPart D Z = 0 ∧ toEAf D Z = t :=
  ⟨GlobalTheory.LatticeStable.liftFin D ((Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).symm t),
   GlobalTheory.AdForm.infPart_liftFin _, GlobalTheory.AdForm.toEAf_liftFin t⟩

theorem trace_id (S T : HSp D) (βS : GL (Fin S.rank) (Datum.EAf D)) (βT : GL (Fin T.rank) (Datum.EAf D)) (k y : WO S T) :
    toEAf D (hO S T y k) = Matrix.trace (frMapAdj S T βS βT k * frMapO S T βS βT y) :=
  GlobalTheory.T.toEAf_orientedHermitianForm_eq_trace_frames S T βS βT k y

theorem local_dual (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (e₁ : AE D) (PP : Pl D.host.E)
    (he₁ : Formalism.L2.NTheta.IsIdemAt e₁ PP) :
    ∃ c : Datum.EAf D,
      (∀ Z : AE D, infPart D Z = 0 → ∀ r : Formalism.L2.Herm.intAf D.host.F D.host.E, resS D.host.F PP r = 0 →
        toEAf D Z = c * r → ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * Z)) = 1) ∧
      (∀ Z : AE D, infPart D Z = 0 → toEAf D Z = c →
        ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * Z)) ≠ 1) :=
  GlobalTheory.T.exists_dualElement_standardChar_splitPrime ψ hψ e₁ PP he₁

theorem psi_trace_split (ψ : AddChar (AF D.host.F) ℂ) (a Z Z₁ : AE D) :
    ψ (Algebra.trace (AF D.host.F) (AE D) (a * Z)) =
      ψ (Algebra.trace (AF D.host.F) (AE D) (a * Z₁)) * ψ (Algebra.trace (AF D.host.F) (AE D) (a * (Z - Z₁))) := by
  rw [← AddChar.map_add_eq_mul, ← map_add (f := _), ← mul_add, add_sub_cancel Z₁ Z]

theorem redM_apply_of_mem (PP : Pl D.host.E) {b a : ℕ} (N : Matrix (Fin b) (Fin a) (Datum.EAf D)) (i : Fin b) (j : Fin a)
    (h : N i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) : redM PP N i j = resS D.host.F PP ⟨N i j, h⟩ := by
  simp only [redM]
  exact dif_pos h


set_option maxHeartbeats 800000 in
theorem local_dual_unit (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (e₁ : AE D) (PP : Pl D.host.E)
    (he₁ : Formalism.L2.NTheta.IsIdemAt e₁ PP) (u : Formalism.L2.Herm.intAf D.host.F D.host.E) (hu : resS D.host.F PP u ≠ 0) :
    ∃ c : Datum.EAf D,
      (∀ Z : AE D, infPart D Z = 0 → ∀ r : Formalism.L2.Herm.intAf D.host.F D.host.E, resS D.host.F PP r = 0 →
        toEAf D Z = c * r → ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * Z)) = 1) ∧
      (∀ Z : AE D, infPart D Z = 0 → toEAf D Z = c * u →
        ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * Z)) ≠ 1) := by
  obtain ⟨c, h1, h2⟩ := local_dual ψ hψ e₁ PP he₁
  haveI := PP.isMaximal
  obtain ⟨b, hb⟩ := Ideal.Quotient.exists_inv (I := PP.asIdeal) hu
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective b
  have hra : resS D.host.F PP (oToS D.host.F D.host.E a) * resS D.host.F PP u = 1 := by
    rw [resS_oToS, ha, mul_comm, hb]
  refine ⟨c * ((oToS D.host.F D.host.E a : Formalism.L2.Herm.intAf D.host.F D.host.E) : Datum.EAf D),
    fun Z hZ r hr hZr => ?_, fun Z hZ hZu => ?_⟩
  · refine h1 Z hZ (oToS D.host.F D.host.E a * r) (by rw [map_mul, hr, mul_zero]) ?_
    rw [hZr, MulMemClass.coe_mul, mul_assoc]
  · obtain ⟨Z₁, hZ₁, hZ₁c⟩ := exists_lift (D := D) c
    have hr : resS D.host.F PP (oToS D.host.F D.host.E a * u - 1) = 0 := by
      rw [map_sub, map_mul, hra, map_one, sub_self]
    have h0 := h1 (Z - Z₁) (by rw [map_sub, hZ, hZ₁, sub_zero]) (oToS D.host.F D.host.E a * u - 1) hr (by
      rw [map_sub, hZu, hZ₁c, AddSubgroupClass.coe_sub, MulMemClass.coe_mul, OneMemClass.coe_one, mul_sub, mul_one,
        mul_assoc])
    intro hc
    apply h2 Z₁ hZ₁ hZ₁c
    rw [psi_trace_split ψ _ Z Z₁, h0, mul_one] at hc
    exact hc


set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem exists_half_frMapO (S T : HSp D) (βS : GL (Fin S.rank) (Datum.EAf D)) (βT : GL (Fin T.rank) (Datum.EAf D))
    (e : AE D) (hee : e * e = e) (z : Matrix (Fin T.rank) (Fin S.rank) (Datum.EAf D))
    (hz : ∀ i j, toEAf D e * z i j = z i j) :
    ∃ y : WO S T, IsHalf e y ∧ (∀ i j, infPart D (y i j) = 0) ∧ frMapO S T βS βT y = z := by
  choose L hL0 hL using fun t : Datum.EAf D => exists_lift (D := D) t
  let Y : Matrix (Fin T.rank) (Fin S.rank) (Datum.EAf D) := HMul.hMul (HMul.hMul βT.val z) (βS⁻¹).val
  refine ⟨Matrix.of fun i j => e * L (Y i j), fun i j => ?_, fun i j => ?_, ?_⟩
  · simp only [Matrix.of_apply, ← mul_assoc, hee]
  · simp only [Matrix.of_apply, map_mul, hL0, mul_zero]
  · have hz' : toEAf D e • z = z := Matrix.ext fun i j => hz i j
    have h3 : toEAf D e • Y = Y := by
      show toEAf D e • HMul.hMul (HMul.hMul βT.val z) (βS⁻¹).val = HMul.hMul (HMul.hMul βT.val z) (βS⁻¹).val
      rw [← Matrix.smul_mul, ← Matrix.mul_smul, hz']
    have hY : (Matrix.of fun i j => e * L (Y i j) : WO S T).map (toEAf D) = Y := by
      ext i j
      simp only [Matrix.map_apply, Matrix.of_apply, map_mul, hL]
      exact congrFun (congrFun h3 i) j
    unfold frMapO
    rw [hY]
    have e1 : HMul.hMul (HMul.hMul (βT⁻¹).val Y) βS.val =
        HMul.hMul (HMul.hMul (HMul.hMul ((βT⁻¹).val) βT.val) z) (HMul.hMul (βS⁻¹).val βS.val) := by
      simp only [Y, Matrix.mul_assoc]
    rw [e1, Units.inv_mul, Units.inv_mul, Matrix.one_mul, Matrix.mul_one]

theorem trace_mul_single {m n : ℕ} (M : Matrix (Fin m) (Fin n) (Datum.EAf D)) (b : Fin n) (a : Fin m) (t0 : Datum.EAf D) :
    Matrix.trace (M * Matrix.single b a t0) = M a b * t0 := by
  rw [Matrix.trace, Finset.sum_eq_single a]
  · simp [Matrix.mul_apply, Matrix.single_apply]
  · intro j _ hj
    simp [Matrix.mul_apply, Matrix.single_apply, Ne.symm hj]
  · intro h
    exact absurd (Finset.mem_univ a) h

end GlobalTheory.HalfDuality

set_option maxHeartbeats 1600000 in
theorem GlobalTheory.HalfDuality.exists_dual_half : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.PlaceModels D → ∀ i t σ s P cμ cη m ω BW f₀ f c io, GlobalTheory.LiftRows.IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → ∀ e : AE D, IsIdemSum e (R.Pg ∪ R.Q t) → ∀ x : WO (Vc D i) (Wc D i), IsHalf (cA D e) x → IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) →
  (∃ PP ∈ R.Pg ∪ R.Q t, redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) ≠ 0) →
  ∃ y : WO (Vc D i) (Wc D i), IsHalf (cA D (cA D e)) y ∧
    (∀ k : WO (Vc D i) (Wc D i), IsHalf (cA D e) k → IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) k) → (∀ PP ∈ R.Pg ∪ R.Q t, redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) k) = 0) →
      R.ψ (symplO (Vc D i) (Wc D i) k y) = 1) ∧
    R.ψ (symplO (Vc D i) (Wc D i) x y) ≠ 1 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F _ i t σ s P cμ cη m ω BW f₀ f c io hL e he x hx hint hex
  obtain ⟨PP, hPP, hred⟩ := hex
  have hψ : IsStdChar D R.ψ (-1) := hL.2.2.2.2.2.1.std
  have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
  obtain ⟨⟨es, hes, -⟩, -⟩ := he
  obtain ⟨a, b, hab⟩ : ∃ a b, redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) a b ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hred (Matrix.ext hn)
  have hu : resS D.host.F PP ⟨_, hint a b⟩ ≠ 0 := by
    rw [← GlobalTheory.HalfDuality.redM_apply_of_mem]
    exact hab
  obtain ⟨c₀, h1, h2⟩ := GlobalTheory.HalfDuality.local_dual_unit R.ψ hψ (es PP) PP (hes PP hPP) _ hu
  obtain ⟨y, hyh, hy0, hyz⟩ := GlobalTheory.HalfDuality.exists_half_frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) e hee
    (Matrix.single b a (toEAf D e * c₀)) (fun i' j' => by
      rw [Matrix.single_apply]
      split_ifs
      · rw [← mul_assoc, ← map_mul, hee]
      · rw [mul_zero])
  have hinf : ∀ k, infPart D (hO (Vc D i) (Wc D i) y k) = 0 := fun k => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hO, map_sum, map_mul, hy0, mul_zero, Finset.sum_const_zero]
  have hfin : ∀ k, IsHalf (cA D e) k → toEAf D (hO (Vc D i) (Wc D i) y k) =
      c₀ * frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) k a b := fun k hk => by
    rw [GlobalTheory.HalfDuality.trace_id _ _ (R.βV i) (R.βW i), hyz, GlobalTheory.HalfDuality.trace_mul_single, mul_comm (toEAf D e) c₀, mul_left_comm,
      mul_comm _ (toEAf D e), GlobalTheory.AdjVecLocal.frMapAdj_half _ _ _ _ hk]
  have hs : ∀ k, R.ψ (symplO (Vc D i) (Wc D i) k y) =
      (R.ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * hO (Vc D i) (Wc D i) y k)))⁻¹ := fun k => by
    rw [GlobalTheory.OrientedHeis.symplO_skew y k, AddChar.map_neg_eq_inv]
    rfl
  refine ⟨y, by rw [Formalism.L2.Theta.cA_cA]; exact hyh, fun k hk hki hkr => ?_, ?_⟩
  · rw [hs, h1 _ (hinf k) ⟨_, hki a b⟩ (by rw [← GlobalTheory.HalfDuality.redM_apply_of_mem]; exact congrFun (congrFun (hkr PP hPP) a) b) (hfin k hk), inv_one]
  · rw [hs]
    exact fun h => h2 _ (hinf x) (hfin x hx) (inv_eq_one.1 h)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDualHalfLatticeDetectingCharacterStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dual_half_lattice_detecting_character : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.PlaceModels D → ∀ i t σ s P cμ cη m ω BW f₀ f c io, GlobalTheory.LiftRows.IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → ∀ e : AE D, IsIdemSum e (R.Pg ∪ R.Q t) → ∀ x : WO (Vc D i) (Wc D i), IsHalf (cA D e) x → IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) →
  (∃ PP ∈ R.Pg ∪ R.Q t, redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) ≠ 0) →
  ∃ y : WO (Vc D i) (Wc D i), IsHalf (cA D (cA D e)) y ∧
    (∀ k : WO (Vc D i) (Wc D i), IsHalf (cA D e) k → IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) k) → (∀ PP ∈ R.Pg ∪ R.Q t, redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) k) = 0) →
      R.ψ (symplO (Vc D i) (Wc D i) k y) = 1) ∧
    R.ψ (symplO (Vc D i) (Wc D i) x y) ≠ 1 := by
  first | exact @GlobalTheory.HalfDuality.exists_dual_half | exact GlobalTheory.HalfDuality.exists_dual_half | (intros; apply GlobalTheory.HalfDuality.exists_dual_half <;> assumption)
end
