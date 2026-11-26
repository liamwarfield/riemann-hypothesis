module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftWeightParamEqInfinitesimalCharacterOfHalfInt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExpDivMulEqStdAddCharMulOfCoprime
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExpDivMulEqStdAddCharMulOfCoprime
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem exp_two_pi_I_div_mul_eq_stdAddChar_mul (p q : ℕ) [NeZero p] [NeZero q] (hpq : Nat.Coprime p q) (T : ℤ) :
    Complex.exp (2 * Real.pi * Complex.I * (T : ℂ) / ((p * q : ℕ) : ℂ)) =
      ZMod.stdAddChar (((q : ZMod p))⁻¹ * (T : ZMod p)) *
        ZMod.stdAddChar (((p : ZMod q))⁻¹ * (T : ZMod q)) := by
  set A : ℤ := Nat.gcdA q p
  set B : ℤ := Nat.gcdB q p
  have hb : (1 : ℤ) = (q : ℤ) * A + (p : ℤ) * B := by
    have h := Nat.gcd_eq_gcd_ab q p
    rw [Nat.Coprime.gcd_eq_one hpq.symm] at h
    simpa using h
  have hA : ((q : ZMod p))⁻¹ = ((A : ℤ) : ZMod p) := by
    apply ZMod.inv_eq_of_mul_eq_one
    have := congrArg (fun z : ℤ => (z : ZMod p)) hb
    simp only [Int.cast_one, Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self,
      zero_mul, add_zero] at this
    exact this.symm
  have hB : ((p : ZMod q))⁻¹ = ((B : ℤ) : ZMod q) := by
    apply ZMod.inv_eq_of_mul_eq_one
    have := congrArg (fun z : ℤ => (z : ZMod q)) hb
    simp only [Int.cast_one, Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self,
      zero_mul, zero_add] at this
    exact this.symm
  have e1 : ((q : ZMod p))⁻¹ * (T : ZMod p) = ((A * T : ℤ) : ZMod p) := by
    rw [hA]; push_cast; ring
  have e2 : ((p : ZMod q))⁻¹ * (T : ZMod q) = ((B * T : ℤ) : ZMod q) := by
    rw [hB]; push_cast; ring
  rw [e1, e2, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe, ← Complex.exp_add]
  congr 1
  have hp : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
  have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hbC : (1 : ℂ) = (q : ℂ) * (A : ℂ) + (p : ℂ) * (B : ℂ) := by exact_mod_cast hb
  push_cast
  field_simp
  linear_combination (T : ℂ) * hbC

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExpDivMulEqStdAddCharMulOfCoprimeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exp_div_mul_eq_stdAddChar_mul_of_coprime : ∀ (p q : ℕ) [NeZero p] [NeZero q], Nat.Coprime p q → ∀ T : ℤ, Complex.exp (2 * Real.pi * Complex.I * (T : ℂ) / ((p * q : ℕ) : ℂ)) = ZMod.stdAddChar (((q : ZMod p))⁻¹ * (T : ZMod p)) * ZMod.stdAddChar (((p : ZMod q))⁻¹ * (T : ZMod q)) := by
  first | exact @GlobalTheory.exp_two_pi_I_div_mul_eq_stdAddChar_mul | exact GlobalTheory.exp_two_pi_I_div_mul_eq_stdAddChar_mul | (intros; apply GlobalTheory.exp_two_pi_I_div_mul_eq_stdAddChar_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarFiniteAddCharDivNatEqExpTrace
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarFiniteAddCharDivNatEqExpTrace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.CharRat

theorem star_psiEf_divN_inclE : ∀ (D : D7) (X : HidaSetting D) (α : 𝓞 D.host.E), star (X.psiEf (divN X.B.I X.B.g (Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (X.ιE.symm (α : D.host.E))))) = Complex.exp (2 * Real.pi * Complex.I * ((Algebra.intTrace ℤ (𝓞 D.host.E) α : ℤ) : ℂ) / ((X.B.g : ℕ) : ℂ)) := by
  intro D X α
  set y : X.B.I.E := X.ιE.symm (α : D.host.E) with hy
  set q : X.B.I.E := algebraMap X.B.I.F X.B.I.E ((X.B.g : X.B.I.F)⁻¹) * y with hq
  have hdiv : divN X.B.I X.B.g (Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) y) =
      Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) q := by
    unfold divN
    rw [hq, map_mul, Algebra.TensorProduct.algebraMap_apply]
    rfl
  have hgq : algebraMap X.B.I.F X.B.I.E ((X.B.g : X.B.I.F)⁻¹) = algebraMap ℚ X.B.I.E ((X.B.g : ℚ)⁻¹) := by
    rw [map_inv₀, map_inv₀, map_natCast, map_natCast]
  have htrq : Algebra.trace ℚ X.B.I.E q = (X.B.g : ℚ)⁻¹ * Algebra.trace ℚ X.B.I.E y := by
    rw [hq, hgq, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]
  have htr : Algebra.trace ℚ X.B.I.E y = Algebra.trace ℚ D.host.E (α : D.host.E) := by
    conv_rhs => rw [← X.ιE.apply_symm_apply (α : D.host.E)]
    exact (Algebra.trace_eq_of_algEquiv X.ιE.toRatAlgEquiv y).symm
  have hint : ((Algebra.intTrace ℤ (𝓞 D.host.E) α : ℤ) : ℚ) = Algebra.trace ℚ D.host.E (α : D.host.E) :=
    Algebra.algebraMap_intTrace (A := ℤ) (K := ℚ) (L := D.host.E) (B := 𝓞 D.host.E) α
  rw [hdiv, eq_inv_of_mul_eq_one_left (X.psiEf_rat q), GlobalTheory.St.G.psiEinf_eq_exp_trace, htrq, htr, ← hint,
    ← Complex.exp_neg]
  change (starRingEnd ℂ) _ = _
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat, map_ratCast]
  push_cast
  ring

end GlobalTheory.Mem.CharRat

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarFiniteAddCharDivNatEqExpTraceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.star_finiteAddChar_div_nat_eq_exp_trace : ∀ (D : D7) (X : HidaSetting D) (α : 𝓞 D.host.E), star (X.psiEf (divN X.B.I X.B.g (Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (X.ιE.symm (α : D.host.E))))) = Complex.exp (2 * Real.pi * Complex.I * ((Algebra.intTrace ℤ (𝓞 D.host.E) α : ℤ) : ℂ) / ((X.B.g : ℕ) : ℂ)) := by
  first | exact @GlobalTheory.Mem.CharRat.star_psiEf_divN_inclE | exact GlobalTheory.Mem.CharRat.star_psiEf_divN_inclE | (intros; apply GlobalTheory.Mem.CharRat.star_psiEf_divN_inclE <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntegerLiftModNatIntegralAdeleTensor
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntegerLiftModNatIntegralAdeleTensor
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.LiftModG

theorem exists_lift_mod_g : ∀ (D : D7) (X : HidaSetting D) (s : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F), s ∈ Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E → ∃ α : 𝓞 D.host.E, ZMod' X.B.I X.B.g (s - Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (X.ιE.symm (α : D.host.E))) := by
  intro D X s hs
  have hg : X.B.g ≠ 0 := by
    rw [X.g_eq]; exact Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
  set I : Ideal (𝓞 X.B.I.E) := Ideal.span {((X.B.g : ℕ) : 𝓞 X.B.I.E)} with hI
  have hI0 : I ≠ ⊥ := by
    rw [hI, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hg
  obtain ⟨q, hq⟩ := cmpS_surj (F := X.B.I.F) I hI0 (Ideal.Quotient.mk _ ⟨s, hs⟩)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  have h1 : Ideal.Quotient.mk (idS X.B.I.F I) (oToS X.B.I.F X.B.I.E a) = Ideal.Quotient.mk _ ⟨s, hs⟩ := hq
  rw [Ideal.Quotient.eq] at h1
  have h2 : (⟨s, hs⟩ - oToS X.B.I.F X.B.I.E a) ∈ Ideal.span {oToS X.B.I.F X.B.I.E ((X.B.g : ℕ) : 𝓞 X.B.I.E)} := by
    have := (Ideal.neg_mem_iff _).2 h1
    rw [neg_sub] at this
    simpa [idS, hI, Ideal.map_span] using this
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 h2
  refine ⟨RingOfIntegers.mapRingEquiv X.ιE a, t, t.2, ?_⟩
  have e1 : X.ιE.symm ((RingOfIntegers.mapRingEquiv X.ιE a : 𝓞 D.host.E) : D.host.E) = (a : X.B.I.E) := by
    rw [RingOfIntegers.mapRingEquiv_apply]; exact X.ιE.symm_apply_apply _
  rw [e1]
  have := congrArg (fun y : Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E => (y : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)) ht
  simp only [Subring.coe_mul, AddSubgroupClass.coe_sub, map_natCast, Subring.coe_natCast] at this
  rw [mul_comm] at this
  exact this.symm

end GlobalTheory.Mem.LiftModG
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntegerLiftModNatIntegralAdeleTensorStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integer_lift_mod_nat_integralAdeleTensor : ∀ (D : D7) (X : HidaSetting D) (s : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F), s ∈ Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E → ∃ α : 𝓞 D.host.E, ZMod' X.B.I X.B.g (s - Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (X.ιE.symm (α : D.host.E))) := by
  first | exact @GlobalTheory.Mem.LiftModG.exists_lift_mod_g | exact GlobalTheory.Mem.LiftModG.exists_lift_mod_g | (intros; apply GlobalTheory.Mem.LiftModG.exists_lift_mod_g <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemPrimeOfInclEMemPlaceIdealIntegralAdelicSpan
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemPrimeOfInclEMemPlaceIdealIntegralAdelicSpan
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SymChar

theorem mem_of_inclE_mem_wInt : ∀ (D : D7) (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (α : 𝓞 D.host.E),
    Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (X.ιE.symm (α : D.host.E)) ∈ GlobalTheory.Mem.SymChar.wInt X w →
      α ∈ w.asIdeal := by
  intro D X w α hα
  set e : 𝓞 X.B.I.E ≃+* 𝓞 D.host.E := RingOfIntegers.mapRingEquiv X.ιE with he
  set Wx : Ideal (𝓞 X.B.I.E) := w.asIdeal.comap (e : 𝓞 X.B.I.E →+* 𝓞 D.host.E) with hWx
  have hWx0 : Wx ≠ ⊥ := by
    intro h0
    apply w.ne_bot
    rw [eq_bot_iff]
    intro b hb
    have : e.symm b ∈ Wx := by
      show e (e.symm b) ∈ w.asIdeal
      simpa using hb
    rw [h0, Ideal.mem_bot] at this
    rw [Ideal.mem_bot]
    simpa using congrArg e this

  have key : ∀ c ∈ GlobalTheory.Mem.SymChar.wInt X w,
      ∃ h : c ∈ Formalism.L2.Herm.intAf X.B.I.F X.B.I.E,
        (⟨c, h⟩ : Formalism.L2.Herm.intAf X.B.I.F X.B.I.E) ∈ Formalism.L2.DIV.idS X.B.I.F Wx := by
    intro c hc
    induction hc using Submodule.span_induction with
    | mem c hc =>
      obtain ⟨a, ⟨b, hb, hab⟩, rfl⟩ := hc
      refine ⟨(Formalism.L2.DIV.oToS X.B.I.F X.B.I.E a).2, ?_⟩
      have ha : a ∈ Wx := by
        show e a ∈ w.asIdeal
        have : e a = b := Subtype.ext hab
        rw [this]; exact hb
      exact Ideal.mem_map_of_mem _ ha
    | zero => exact ⟨zero_mem _, zero_mem _⟩
    | add x y _ _ hx hy =>
      obtain ⟨hx1, hx2⟩ := hx
      obtain ⟨hy1, hy2⟩ := hy
      exact ⟨add_mem hx1 hy1, add_mem hx2 hy2⟩
    | smul r x _ hx =>
      obtain ⟨hx1, hx2⟩ := hx
      refine ⟨mul_mem r.2 hx1, ?_⟩
      have : (⟨r • x, mul_mem r.2 hx1⟩ : Formalism.L2.Herm.intAf X.B.I.F X.B.I.E) = ⟨r.1, r.2⟩ * ⟨x, hx1⟩ := rfl
      rw [this]
      exact Ideal.mul_mem_left _ _ hx2
  obtain ⟨h1, h2⟩ := key _ hα
  set c : 𝓞 X.B.I.E := e.symm α with hc
  have hoc : (⟨_, h1⟩ : Formalism.L2.Herm.intAf X.B.I.F X.B.I.E) = Formalism.L2.DIV.oToS X.B.I.F X.B.I.E c := rfl
  rw [hoc] at h2
  have hz : Formalism.L2.DIV.cmpS X.B.I.F Wx (Ideal.Quotient.mk Wx c) = Formalism.L2.DIV.cmpS X.B.I.F Wx 0 := by
    rw [map_zero]
    show Ideal.Quotient.mk _ (Formalism.L2.DIV.oToS X.B.I.F X.B.I.E c) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.2 h2
  have hcW : c ∈ Wx := Ideal.Quotient.eq_zero_iff_mem.1 (Formalism.L2.DIV.cmpS_inj Wx hWx0 hz)
  have : e c = α := by rw [hc]; exact e.apply_symm_apply α
  rw [← this]
  exact hcW

end GlobalTheory.Mem.SymChar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemPrimeOfInclEMemPlaceIdealIntegralAdelicSpanStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_prime_of_inclE_mem_placeIdealIntegralAdelicSpan : ∀ (D : D7) (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (α : 𝓞 D.host.E), Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (X.ιE.symm (α : D.host.E)) ∈ GlobalTheory.Mem.SymChar.wInt X w → α ∈ w.asIdeal := by
  first | exact @GlobalTheory.Mem.SymChar.mem_of_inclE_mem_wInt | exact GlobalTheory.Mem.SymChar.mem_of_inclE_mem_wInt | (intros; apply GlobalTheory.Mem.SymChar.mem_of_inclE_mem_wInt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntTraceModEqSumResiduesSplitPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntTraceModEqSumResiduesSplitPrime
noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.SplitTrace

variable {K : Type} [Field K] [NumberField K]

theorem absNorm_span_natCast (p : ℕ) :
    Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = p ^ Module.finrank ℚ K := by
  rw [Ideal.absNorm_span_singleton, show ((p : 𝓞 K)) = algebraMap ℤ (𝓞 K) (p : ℤ) by simp,
    Algebra.norm_algebraMap, RingOfIntegers.rank, Int.natAbs_pow, Int.natAbs_natCast]

theorem split_of_card (p : ℕ) (hp : p.Prime) {ι : Type} [Fintype ι] (e : ι → HeightOneSpectrum (𝓞 K))
    (he : Function.Injective e) (hmem : ∀ i, (p : 𝓞 K) ∈ (e i).asIdeal)
    (hcard : Fintype.card ι = Module.finrank ℚ K) :
    (∀ i, Ideal.absNorm (e i).asIdeal = p) ∧ Ideal.span {(p : 𝓞 K)} = ⨅ i, (e i).asIdeal := by
  classical
  set n := Module.finrank ℚ K
  have hcop : ∀ i ∈ (Finset.univ : Finset ι), ∀ j ∈ (Finset.univ : Finset ι), i ≠ j →
      IsCoprime (e i).asIdeal (e j).asIdeal := fun i _ j _ hij =>
    HeightOneSpectrum.isCoprime_of_ne _ _ (fun h => hij (he h))
  have hJ : ∏ i, (e i).asIdeal = ⨅ i, (e i).asIdeal := by
    rw [Ideal.prod_eq_iInf_of_pairwise_isCoprime hcop]; simp
  have hle : Ideal.span {(p : 𝓞 K)} ≤ ∏ i, (e i).asIdeal := by
    rw [hJ, Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_iInf.2 hmem
  have hdvd_i : ∀ i, Ideal.absNorm (e i).asIdeal ∣ p ^ n := fun i => by
    rw [← absNorm_span_natCast]
    exact Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 (hmem i))
  choose k hkn hk using fun i => (Nat.dvd_prime_pow hp).1 (hdvd_i i)
  have hk1 : ∀ i, 1 ≤ k i := fun i => by
    rcases Nat.eq_zero_or_pos (k i) with h | h
    · exfalso
      have h1 := hk i
      rw [h, pow_zero, Ideal.absNorm_eq_one_iff] at h1
      exact (e i).isPrime.ne_top h1
    · exact h
  have hprod : Ideal.absNorm (∏ i, (e i).asIdeal) = p ^ ∑ i, k i := by
    rw [map_prod, ← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_congr rfl fun i _ => hk i
  have hsum_le : ∑ i, k i ≤ n := by
    have h := Ideal.absNorm_dvd_absNorm_of_le hle
    rw [hprod, absNorm_span_natCast] at h
    exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 h
  have hsum_eq : ∑ i, k i = ∑ _i : ι, 1 := by
    refine le_antisymm ?_ (Finset.sum_le_sum fun i _ => hk1 i)
    simpa [hcard] using hsum_le
  have hkeq : ∀ i, k i = 1 := fun i =>
    ((Finset.sum_eq_sum_iff_of_le (fun j _ => hk1 j)).1 hsum_eq.symm i (Finset.mem_univ i)).symm
  refine ⟨fun i => by rw [hk i, hkeq i, pow_one], ?_⟩
  rw [← hJ]
  obtain ⟨L, hL⟩ := Ideal.dvd_iff_le.2 hle
  have hnL : Ideal.absNorm L = 1 := by
    have h := congrArg Ideal.absNorm hL
    rw [map_mul, hprod, absNorm_span_natCast, show ∑ i, k i = n by simpa [hcard] using hsum_eq] at h
    have hpn : 0 < p ^ n := pow_pos hp.pos n
    exact Nat.eq_of_mul_eq_mul_left hpn (by rw [mul_one]; exact h.symm)
  rw [hL, Ideal.absNorm_eq_one_iff.1 hnL, Ideal.mul_top]

theorem trace_pi {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : ι → Type) [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)] [∀ i, Module.Free R (A i)]
    [∀ i, Module.Finite R (A i)] (z : ∀ i, A i) :
    Algebra.trace R (∀ i, A i) z = ∑ i, Algebra.trace R (A i) (z i) := by
  classical
  let b := fun i => Module.Free.chooseBasis R (A i)
  rw [Algebra.trace_eq_matrix_trace (Pi.basis b), Matrix.trace, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.trace_eq_matrix_trace (b i), Matrix.trace]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, Pi.basis_apply, Pi.basis_repr]
  rw [show z * Pi.single i (b i k) = Pi.single i (z i * b i k) by
    funext j; by_cases h : j = i
    · subst h; simp
    · simp [h]]
  simp

theorem intTrace_modEq_sum : ∀ {K : Type} [Field K] [NumberField K] (p : ℕ), p.Prime → ∀ {ι : Type} [Fintype ι] (e : ι → HeightOneSpectrum (𝓞 K)), Function.Injective e → (∀ W : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ W.asIdeal ↔ ∃ i, e i = W) → Fintype.card ι = Module.finrank ℚ K → ∀ (x : 𝓞 K) (b : ι → ℤ), (∀ i, x - (b i : 𝓞 K) ∈ (e i).asIdeal) → ((Algebra.intTrace ℤ (𝓞 K) x : ℤ) : ZMod p) = ∑ i, (b i : ZMod p) := by
  intro K _ _ p hp ι _ e he hW hcard x b hxb
  classical
  have hmem : ∀ i, (p : 𝓞 K) ∈ (e i).asIdeal := fun i => (hW (e i)).2 ⟨i, rfl⟩
  obtain ⟨hnorm, hspan⟩ := split_of_card p hp e he hmem hcard
  set P : Ideal ℤ := Ideal.span {(p : ℤ)} with hPdef
  haveI hPm : P.IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  letI := Ideal.Quotient.field P
  have hmap : Ideal.map (algebraMap ℤ (𝓞 K)) P = ⨅ i, (e i).asIdeal := by
    rw [hPdef, Ideal.map_span, Set.image_singleton, map_natCast]; exact hspan
  have hPv : ∀ i, P ≤ (e i).asIdeal.comap (algebraMap ℤ (𝓞 K)) := fun i => by
    rw [← Ideal.map_le_iff_le_comap, hmap]; exact iInf_le _ i
  letI : ∀ i, Algebra (ℤ ⧸ P) (𝓞 K ⧸ (e i).asIdeal) := fun i => Ideal.Quotient.algebraQuotientOfLEComap (hPv i)
  haveI : ∀ i, IsScalarTower ℤ (ℤ ⧸ P) (𝓞 K ⧸ (e i).asIdeal) := fun i => .of_algebraMap_eq' rfl
  haveI : ∀ i, Module.Finite (ℤ ⧸ P) (𝓞 K ⧸ (e i).asIdeal) := fun i => Module.Finite.of_restrictScalars_finite ℤ _ _
  letI : ∀ i, Field (𝓞 K ⧸ (e i).asIdeal) := fun i => Ideal.Quotient.field _
  have hcop : Pairwise (Function.onFun IsCoprime fun i => (e i).asIdeal) := fun i j hij =>
    HeightOneSpectrum.isCoprime_of_ne _ _ (fun h => hij (he h))
  let φ : (𝓞 K ⧸ Ideal.map (algebraMap ℤ (𝓞 K)) P) ≃ₐ[ℤ ⧸ P] (∀ i, 𝓞 K ⧸ (e i).asIdeal) :=
    { __ := (Ideal.quotEquivOfEq hmap).trans (Ideal.quotientInfRingEquivPiQuotient _ hcop),
      commutes' := Quotient.ind fun _ ↦ rfl }
  have hφ : φ (Ideal.Quotient.mk _ x) = fun i => Ideal.Quotient.mk (e i).asIdeal x := rfl
  have hx1 : ∀ i, Ideal.Quotient.mk (e i).asIdeal x =
      algebraMap (ℤ ⧸ P) (𝓞 K ⧸ (e i).asIdeal) (Ideal.Quotient.mk P (b i)) := fun i => by
    rw [Ideal.Quotient.eq.mpr (hxb i)]
    show _ = Ideal.Quotient.mk (e i).asIdeal (algebraMap ℤ (𝓞 K) (b i))
    rw [algebraMap_int_eq, eq_intCast]
  have hcardP : Nat.card (ℤ ⧸ P) = p := by
    rw [Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv, Nat.card_zmod]
  have hfr : ∀ i, Module.finrank (ℤ ⧸ P) (𝓞 K ⧸ (e i).asIdeal) = 1 := fun i => by
    have hcardv : Nat.card (𝓞 K ⧸ (e i).asIdeal) = p := by
      rw [← hnorm i, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    have h := Module.natCard_eq_pow_finrank (K := ℤ ⧸ P) (V := 𝓞 K ⧸ (e i).asIdeal)
    rw [hcardP, hcardv] at h
    exact (Nat.pow_right_injective hp.two_le (h.symm.trans (pow_one p).symm))
  have key : Ideal.Quotient.mk P (Algebra.intTrace ℤ (𝓞 K) x) = Ideal.Quotient.mk P (∑ i, b i) := by
    rw [← Algebra.trace_quotient_eq_of_isDedekindDomain, ← Algebra.trace_eq_of_algEquiv φ, hφ, trace_pi]
    simp_rw [hx1, Algebra.trace_algebraMap, hfr, one_smul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
  rw [Ideal.Quotient.eq, hPdef, Ideal.mem_span_singleton] at key
  rw [← Int.cast_sum, ZMod.intCast_eq_intCast_iff_dvd_sub]
  obtain ⟨m, hm⟩ := key
  exact ⟨-m, by linear_combination -hm⟩

end GlobalTheory.SplitTrace
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntTraceModEqSumResiduesSplitPrimeStatement
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intTrace_modEq_sum_residues_split_prime : ∀ {K : Type} [Field K] [NumberField K] (p : ℕ), p.Prime → ∀ {ι : Type} [Fintype ι] (e : ι → HeightOneSpectrum (𝓞 K)), Function.Injective e → (∀ W : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ W.asIdeal ↔ ∃ i, e i = W) → Fintype.card ι = Module.finrank ℚ K → ∀ (x : 𝓞 K) (b : ι → ℤ), (∀ i, x - (b i : 𝓞 K) ∈ (e i).asIdeal) → ((Algebra.intTrace ℤ (𝓞 K) x : ℤ) : ZMod p) = ∑ i, (b i : ZMod p) := by
  first | exact @GlobalTheory.SplitTrace.intTrace_modEq_sum | exact GlobalTheory.SplitTrace.intTrace_modEq_sum | (intros; apply GlobalTheory.SplitTrace.intTrace_modEq_sum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteAddCharConjEqProdPlaceResidueChars
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.SymChar.CharProd
open Classical

theorem wInt_le {D : D7} (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E))
    {c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F} (hc : c ∈ GlobalTheory.Mem.SymChar.wInt X w) :
    c ∈ Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E := by
  induction hc using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, _, rfl⟩ := hx
    exact Formalism.L2.SG.Pf.unitaryCongruence.inclE_mem X.B.I ⟨a, rfl⟩
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul c x _ hx => exact mul_mem c.2 hx

theorem addChar_sum {ι A M : Type} [AddCommMonoid A] [CommMonoid M] (ψ : AddChar A M) (s : Finset ι)
    (f : ι → A) : ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

instance neZeroG (D : D7) (k : Fin 2) : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩

def cK (D : D7) (k : Fin 2) : ZMod (D.host.g k) := ((D.host.g (k + 1) : ℕ) : ZMod (D.host.g k))⁻¹

def psiK (D : D7) (k : Fin 2) : AddChar (ZMod (D.host.g k)) ℂ :=
  (ZMod.stdAddChar (N := D.host.g k)).mulShift (cK D k)

theorem cK_ne_zero (D : D7) (k : Fin 2) : cK D k ≠ 0 := by
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  unfold cK
  refine inv_ne_zero ?_
  rw [Ne, CharP.cast_eq_zero_iff (ZMod (D.host.g k)) (D.host.g k)]
  intro hd
  have h := (Nat.prime_dvd_prime_iff_eq (D.host.g_prime k) (D.host.g_prime (k + 1))).1 hd
  have hne := D.host.g_ne
  fin_cases k
  · exact hne h
  · exact hne h.symm

theorem psiK_ne_one (D : D7) (k : Fin 2) : psiK D k ≠ 1 :=
  ZMod.isPrimitive_stdAddChar _ (cK_ne_zero D k)

theorem psiEf_conj_eq_prod : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal) → ∃ ψ' : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ, (∀ kv, ψ' kv ≠ 1) ∧ ∀ (s : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) (t u : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1)), (∀ kv, GlobalTheory.Mem.SymChar.ModW X (D.naut.plGw kv.1 kv.2) s (t kv)) → (∀ kv, GlobalTheory.Mem.SymChar.ModW X (D.naut.plGw kv.1 kv.2) (sigA X.B.I s) (u kv)) → star (X.psiEf (divN X.B.I X.B.g s)) = ∏ kv, ψ' kv (t kv + u kv) := by
  intro D X _h _hι hg
  refine ⟨fun kv => psiK D kv.1, fun kv => psiK_ne_one D kv.1, ?_⟩
  intro s t u ht hu
  obtain ⟨_, _, hcard0⟩ := GlobalTheory.T.places_over_typePrime_chosen_and_conj D 0
  obtain ⟨v0⟩ : Nonempty (D.nd.PlG 0) := by
    by_contra hc
    rw [not_nonempty_iff] at hc
    have h0 : Module.finrank ℚ D.host.E = 0 := by rw [← hcard0]; simp
    exact (Module.finrank_pos (R := ℚ) (M := D.host.E)).ne' h0
  have hs : s ∈ Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E := by
    have h1 := wInt_le X _ (ht ⟨0, v0⟩)
    have h2 : (((t ⟨0, v0⟩).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ∈ Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E :=
      natCast_mem _ _
    simpa using add_mem h1 h2
  obtain ⟨α, hα⟩ := GlobalTheory.T.exists_integer_lift_mod_nat_integralAdeleTensor D X s hs
  set a := Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (X.ιE.symm (α : D.host.E)) with ha
  have hg0 : X.B.g ≠ 0 := by
    rw [X.g_eq]; exact mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
  have hstep : X.psiEf (divN X.B.I X.B.g s) = X.psiEf (divN X.B.I X.B.g a) := by
    conv_lhs => rw [show s = a + (s - a) by ring]
    rw [Formalism.L2.SG.Pf.unitaryCongruence.divN_add, X.psiEf_add,
      Formalism.L2.SG.Pf.unitaryCongruence.psi_Z X.B.I X.B.g X.psiEf_add X.psiEf_int hg0 hα, mul_one]
  rw [hstep, GlobalTheory.T.star_finiteAddChar_div_nat_eq_exp_trace D X α]
  have hres : ∀ kv : (Σ k : Fin 2, D.nd.PlG k),
      α - (((t kv).val : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal ∧
      α - (((u kv).val : ℕ) : 𝓞 D.host.E) ∈ (GlobalTheory.IdemSupport.cP (D := D) (D.naut.plGw kv.1 kv.2)).asIdeal := by
    intro kv
    have hZ : s - a ∈ GlobalTheory.Mem.SymChar.wInt X (D.naut.plGw kv.1 kv.2) :=
      GlobalTheory.Mem.SymChar.wInt_of_zmod X kv.1 (hg kv) hα
    constructor
    · apply GlobalTheory.T.mem_prime_of_inclE_mem_placeIdealIntegralAdelicSpan D X
      have e : Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F)
          (X.ιE.symm (((α - (((t kv).val : ℕ) : 𝓞 D.host.E) : 𝓞 D.host.E)) : D.host.E)) =
          (s - (((t kv).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)) - (s - a) := by
        rw [ha]; push_cast; rw [map_sub, map_natCast, map_sub, map_natCast]; ring
      rw [e]; exact sub_mem (ht kv) hZ
    · rw [GlobalTheory.IdemSupport.mem_cP, map_sub, map_natCast]
      apply GlobalTheory.T.mem_prime_of_inclE_mem_placeIdealIntegralAdelicSpan D X
      have hZ' : sigA X.B.I s - sigA X.B.I a ∈ GlobalTheory.Mem.SymChar.wInt X (D.naut.plGw kv.1 kv.2) := by
        rw [← map_sub]
        exact GlobalTheory.Mem.SymChar.wInt_of_zmod X kv.1 (hg kv) (Formalism.L2.SG.Pf.unitaryCongruence.Z_sig X.B.I X.B.g hα)
      have hsa : sigA X.B.I a = Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F)
          (X.ιE.symm ((GlobalTheory.IdemSupport.cO D α : 𝓞 D.host.E) : D.host.E)) := by
        rw [ha, Formalism.L2.SG.Pf.unitaryCongruence.sigA_inclE]
        congr 1
        apply X.ιE.injective
        rw [X.ιE_conj, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, GlobalTheory.IdemSupport.cO_coe]
        exact (Formalism.BasicNotions.bridge_star_holds D.R D.host _).symm
      have e : Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F)
          (X.ιE.symm (((GlobalTheory.IdemSupport.cO D α - (((u kv).val : ℕ) : 𝓞 D.host.E) : 𝓞 D.host.E)) : D.host.E)) =
          (sigA X.B.I s - (((u kv).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)) -
            (sigA X.B.I s - sigA X.B.I a) := by
        rw [hsa]; push_cast; rw [map_sub, map_natCast, map_sub, map_natCast]; ring
      rw [e]; exact sub_mem (hu kv) hZ'
  have htr : ∀ k : Fin 2, ((Algebra.intTrace ℤ (𝓞 D.host.E) α : ℤ) : ZMod (D.host.g k)) =
      ∑ v : D.nd.PlG k, (t ⟨k, v⟩ + u ⟨k, v⟩) := by
    intro k
    obtain ⟨hinj, hcov, hcard⟩ := GlobalTheory.T.places_over_typePrime_chosen_and_conj D k
    rw [GlobalTheory.T.intTrace_modEq_sum_residues_split_prime (D.host.g k) (D.host.g_prime k) _ hinj hcov hcard α
      (Sum.elim (fun v => (((t ⟨k, v⟩).val : ℕ) : ℤ)) (fun v => (((u ⟨k, v⟩).val : ℕ) : ℤ))) ?_]
    · rw [Fintype.sum_sum_type, Finset.sum_add_distrib]; simp
    · rintro (v | v)
      · simpa using (hres ⟨k, v⟩).1
      · simpa using (hres ⟨k, v⟩).2
  rw [Fintype.prod_sigma]
  have hk : ∀ k : Fin 2, ∏ v : D.nd.PlG k, psiK D k (t ⟨k, v⟩ + u ⟨k, v⟩) =
      psiK D k ((Algebra.intTrace ℤ (𝓞 D.host.E) α : ℤ) : ZMod (D.host.g k)) := by
    intro k; rw [htr k, addChar_sum]
  simp only [hk, Fin.prod_univ_two]
  simp only [psiK, cK, AddChar.mulShift_apply]
  have hcop : Nat.Coprime (D.host.g 0) (D.host.g 1) :=
    (Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne
  rw [X.g_eq]
  exact GlobalTheory.T.exp_div_mul_eq_stdAddChar_mul_of_coprime (D.host.g 0) (D.host.g 1) hcop _

end GlobalTheory.Mem.SymChar.CharProd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteAddCharConjEqProdPlaceResidueCharsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteAddChar_conj_eq_prod_placeResidueChars : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal) → ∃ ψ' : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ, (∀ kv, ψ' kv ≠ 1) ∧ ∀ (s : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) (t u : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1)), (∀ kv, GlobalTheory.Mem.SymChar.ModW X (D.naut.plGw kv.1 kv.2) s (t kv)) → (∀ kv, GlobalTheory.Mem.SymChar.ModW X (D.naut.plGw kv.1 kv.2) (sigA X.B.I s) (u kv)) → star (X.psiEf (divN X.B.I X.B.g s)) = ∏ kv, ψ' kv (t kv + u kv) := by
  first | exact @GlobalTheory.Mem.SymChar.CharProd.psiEf_conj_eq_prod | exact GlobalTheory.Mem.SymChar.CharProd.psiEf_conj_eq_prod | (intros; apply GlobalTheory.Mem.SymChar.CharProd.psiEf_conj_eq_prod <;> assumption)
end
