module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteFourierExpansionHalfSplitPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorConjugateHalfVacuumEqSemichara
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SemicharacterSqEqOneOnHalfA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetCConstMul

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DatumReadingSplitPlacesEqClassicalTheta
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorHalfComponentOnVacuumTranslate
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorFinitePartRestActsBySemicharac
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HalfASignTraceIsInteger
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HalfASignTraceIsInteger
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TraceInt
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SemiTrace

theorem alV_embH_eq_exp_trace (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (δ : ℂ) (sc : ℝ)
    (hP : StdPair θ S T δ sc ψ) (y : Formalism.L2.Col.HomE D.host.E S.rank T.rank) :
    alV D.host.d sc (embH (tauE D) δ y) = Complex.exp (-(Real.pi : ℂ) * Complex.I *
      ((Algebra.trace ℚ D.host.E (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 *
        GlobalTheory.LatVac.hRat S T (LinearMap.toMatrix' y) (LinearMap.toMatrix' y)) : ℚ) : ℂ)) := by
  have hd : 0 < Real.sqrt D.host.d :=
    Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero D.host.hyp.2.1.ne_zero))
  set t : ℚ := Algebra.trace ℚ D.host.E (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 *
        GlobalTheory.LatVac.hRat S T (LinearMap.toMatrix' y) (LinearMap.toMatrix' y)) with htdef
  set M := LinearMap.toMatrix' y with hMdef
  have hMij : ∀ i j, M i j = y (Pi.single j 1) i := by
    intro i j; simp [M, LinearMap.toMatrix'_apply]
  set s : D.what₂.Tau → ℝ := fun τ => ∑ i, ∑ j, Complex.normSq (tauE D τ (M i j)) with hs
  have hh : ∀ τ, tauE D τ (GlobalTheory.LatVac.hRat S T M M) = ((s τ : ℝ) : ℂ) := by
    intro τ
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [GlobalTheory.LatVac.hRat, hP.gS, hP.gT, inv_one, Matrix.one_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, map_sum, map_mul, tauE_star, hs]
    simp only [apply_ite (⇑(tauE D τ)), map_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, map_mul, tauE_star]
    push_cast
    rw [Finset.sum_comm]
    calc _ = ∑ j, ∑ i, ((Complex.normSq (tauE D τ (M i j)) : ℝ) : ℂ) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_comm]
          simp only [Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Complex.normSq_eq_conj_mul_self]
      _ = _ := Finset.sum_comm
  have hτ : ∀ τ, (tauE D τ (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 * GlobalTheory.LatVac.hRat S T M M)).re = -(s τ) / 2 := by
    intro τ
    rw [map_mul, map_mul, map_pow, map_div₀, map_add (f := _), map_one, map_ofNat, hh, hP.xi, Formalism.L2.Theta.tauE_sqrtMinusD,
      Complex.re_mul_ofReal, re_xi_mul_sq _ hd]
    ring
  have hk' : (t : ℂ) = ((-(∑ τ, s τ) : ℝ) : ℂ) := by
    have e1 := sum_two_re_tauE D (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 * GlobalTheory.LatVac.hRat S T M M)
    rw [← htdef] at e1
    rw [← e1]
    simp only [hτ]
    push_cast
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun τ _ => ?_
    ring
  have hsc : sc * Complex.normSq δ = 2 * (Real.sqrt D.host.d)⁻¹ := by
    rw [← Complex.sq_norm]; exact hP.scale
  have hq : Formalism.L2.Th1.H.qOf (Real.sqrt D.host.d / 2) (HV sc) (embH (tauE D) δ y) = ∑ τ, s τ := by
    simp only [Formalism.L2.Th1.H.qOf, HV, LinearMap.mk₂'ₛₗ_apply, embH, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Complex.mul_conj]
    rw [show ((sc : ℂ) * ∑ x, ∑ x_1, ∑ x_2, ((Complex.normSq (δ * tauE D x (y (Pi.single x_2 1) x_1)) : ℝ) : ℂ)) =
        ((sc * ∑ x, ∑ x_1, ∑ x_2, Complex.normSq (δ * tauE D x (y (Pi.single x_2 1) x_1)) : ℝ) : ℂ) by push_cast; rfl,
      Complex.ofReal_re]
    simp_rw [Complex.normSq_mul, ← Finset.mul_sum]
    simp only [hs, hMij]
    rw [← mul_assoc sc, hsc]
    field_simp
  have hsum : ((∑ τ, s τ : ℝ) : ℂ) = -(t : ℂ) := by rw [hk']; push_cast; ring
  rw [alV, Formalism.L2.Th1.H.alphaQ, hq, hsum]
  congr 1
  ring

theorem trace_int : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S N → IsSelfDualC T N' → ∀ (c : ℕ), 0 < c → Odd c → ∀ x' ∈ halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, ∃ k : ℤ, (k : ℚ) = Algebra.trace ℚ D.host.E (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 * GlobalTheory.LatVac.hRat S T (LinearMap.toMatrix' x') (LinearMap.toMatrix' x')) := by
  intro D ψ θ S T δ sc hP e SS hSS hSS2 N N' hN hN' c hc hcS x' hx'
  have h2 := GlobalTheory.T.semicharacter_sq_eq_one_on_halfA D ψ θ S T δ sc hP e SS hSS hSS2 N N' hN hN' c hc hcS x' hx'
  rw [alV_embH_eq_exp_trace D ψ θ S T δ sc hP, ← Complex.exp_add] at h2
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h2
  refine ⟨-n, ?_⟩
  set t : ℚ := Algebra.trace ℚ D.host.E (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 *
        GlobalTheory.LatVac.hRat S T (LinearMap.toMatrix' x') (LinearMap.toMatrix' x')) with htdef
  have hpi : (Real.pi : ℂ) * Complex.I ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.2 Real.pi_ne_zero) Complex.I_ne_zero
  have : ((t : ℚ) : ℂ) = (((-n : ℤ) : ℚ) : ℂ) := by
    apply mul_left_cancel₀ hpi
    push_cast
    linear_combination (-1/2 : ℂ) * hn
  exact_mod_cast this.symm
end GlobalTheory.TraceInt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HalfASignTraceIsIntegerStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.halfA_signTrace_isInteger : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S N → IsSelfDualC T N' → ∀ (c : ℕ), 0 < c → Odd c → ∀ x' ∈ halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, ∃ k : ℤ, (k : ℚ) = Algebra.trace ℚ D.host.E (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 * GlobalTheory.LatVac.hRat S T (LinearMap.toMatrix' x') (LinearMap.toMatrix' x')) := by
  first | exact @GlobalTheory.TraceInt.trace_int | exact GlobalTheory.TraceInt.trace_int | (intros; apply GlobalTheory.TraceInt.trace_int <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorFinitePartRestActsBySemicharac
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.HalfARest

section Tw

variable {E : Type} [Field E] [NumberField E] [StarRing E] {W : Type} [AddCommGroup W] [Module E W] [Module (𝓞 E) W]
  [IsScalarTower (𝓞 E) E W]

theorem natsmul_mem_twO' (L : Submodule (𝓞 E) W) (c : ℕ) (e e' : HeightOneSpectrum (𝓞 E) → ℤ) (he : ∀ Q, e' Q ≤ e Q + 1)
    {x : W} (hx : x ∈ Formalism.L2.Ker.twist₂ L c e) : (c : 𝓞 E) • x ∈ Formalism.L2.Ker.twist₂ L c e' := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · rw [Nat.cast_zero, zero_smul]; exact Submodule.zero_mem _
  have hcE : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  rw [Formalism.L2.Ker.mem_twO] at hx ⊢
  intro Q
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = e Q + 1 - e' Q := ⟨(e Q + 1 - e' Q).toNat, Int.toNat_of_nonneg (by linarith [he Q])⟩
  have key : ((c : E) ^ e' Q)⁻¹ • ((c : 𝓞 E) • x) = ((c : 𝓞 E) ^ n) • (((c : E) ^ e Q)⁻¹ • x) := by
    rw [← IsScalarTower.algebraMap_smul E ((c : 𝓞 E) ^ n), ← IsScalarTower.algebraMap_smul E (c : 𝓞 E) x, smul_smul, smul_smul]
    congr 1
    simp only [map_pow, map_natCast]
    rw [← _root_.zpow_neg, ← _root_.zpow_neg, ← zpow_natCast, hn, ← zpow_add_one₀ hcE, ← zpow_add₀ hcE]
    congr 1; ring
  rw [key]
  exact Submodule.smul_mem _ _ (hx Q)

theorem mem_twO_zero' (M : Submodule (𝓞 E) W) (c : ℕ) (x : W) : x ∈ Formalism.L2.Ker.twist₂ M c (fun _ => 0) ↔ x ∈ M := by
  rw [Formalism.L2.Ker.mem_twO]
  simp only [zpow_zero, inv_one, one_smul]
  exact ⟨fun h => Formalism.L2.Ker.mem_of_forall_locP M h, fun h Q => Formalism.L2.Ker.le_locP' M Q h⟩

end Tw


open GlobalTheory.LatVac in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem heisO_rest_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S N → IsSelfDualC T N' → ∀ (c : ℕ), 0 < c → Odd c → ∀ f₀, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) f₀ → ∀ x' ∈ halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, heisO ψ S T ((GlobalTheory.VacUnique.finRat S T (LinearMap.toMatrix' x')) - ((LinearMap.toMatrix' x').map fun r => e * incA D r)) f₀ = alV D.host.d sc (embH (tauE D) δ x') • f₀ := by
  intro D ψ θ S T δ sc hP e SS hE h2qd N N' hSd hTd c hc hcP f₀ hV x' hx
  set X := LinearMap.toMatrix' x' with hXdef
  set Y := GlobalTheory.VacUnique.finRat S T X with hY
  set Λ := latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True with hΛ
  have hvac : IsLatVac (heisO ψ S T) Λ f₀ := hV.2.lat
  have hstab : ∀ w : AE D, finPart D w ∈ intAE D → ∀ u ∈ Λ, w • u ∈ Λ :=
    fun w hw u hu => GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ w hw u hu
  have hsmM : ∀ (r : D.host.E) (Z : Matrix (Fin T.rank) (Fin S.rank) D.host.E),
      GlobalTheory.VacUnique.finRat S T (r • Z) = incA D r • GlobalTheory.VacUnique.finRat S T Z := by
    intro r Z
    ext i j
    change (pairA D.host.F 0 1) ⊗ₜ[D.host.F] (r * Z i j) = incA D r * ((pairA D.host.F 0 1) ⊗ₜ[D.host.F] Z i j)
    rw [show incA D r = (1 : AF D.host.F) ⊗ₜ[D.host.F] r from rfl, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  have hnat : ∀ (n : ℕ) (u : WO S T), n • u = incA D (n : D.host.E) • u := by
    intro n u; rw [map_natCast, Nat.cast_smul_eq_nsmul]
  have hc0 : (c : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'

  have hcx : (c : 𝓞 D.host.E) • x' ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' :=
    (mem_twO_zero' _ c _).1 (natsmul_mem_twO' _ c _ _ (fun Q => by
      rcases Formalism.L2.Ker.expS_cases SS Q with h | h | h <;> rw [h] <;> norm_num) hx)
  have ha : c • Y ∈ Λ := by
    rw [hnat, ← hsmM]
    have e1 : (c : D.host.E) • X = LinearMap.toMatrix' ((c : 𝓞 D.host.E) • x') := by
      rw [Nat.cast_smul_eq_nsmul (𝓞 D.host.E), ← Nat.cast_smul_eq_nsmul D.host.E, LinearEquiv.map_smul]
    rw [e1, GlobalTheory.LatVacSign.finRat_eq]
    exact finTens_mem_latO (one_mem_intAf _) (GlobalTheory.AdForm.HalfPairing.toMatrix_mem_latRat hP.cc hSd hcx)

  have h0 : infPart D e = 0 := GlobalTheory.PlaceDatum.infPart_idemSum hE
  have hXt : X.map (fun r => e * incA D r) = e • Y := by
    ext i j
    change e * incA D (X i j) = e * ((pairA D.host.F 0 1) ⊗ₜ[D.host.F] X i j)
    rw [show (pairA D.host.F 0 1) ⊗ₜ[D.host.F] X i j = ((pairA D.host.F 0 1) ⊗ₜ[D.host.F] (1 : D.host.E)) * incA D (X i j) by
      rw [show incA D (X i j) = (1 : AF D.host.F) ⊗ₜ[D.host.F] X i j from rfl, Algebra.TensorProduct.tmul_mul_tmul,
        mul_one, one_mul], ← mul_assoc, GlobalTheory.PlaceDatum.mul_pair_one h0]
  set R := (1 - e) • Y with hRdef
  have hYR : Y - e • Y = R := by rw [hRdef, sub_smul, one_smul]
  have hR : R ∈ Λ := by
    have h := GlobalTheory.T.halfA_components_mem_completedLattice_offPrimes D ψ θ S T δ sc hP e SS hE h2qd N N' hSd hTd c hc hcP x' hx
    rw [← hXdef, ← hY, hXt, hYR] at h
    exact h
  have he2 : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self hE

  have hbil : ∀ (x y : WO S T) (k : ℕ), symplOH S T (k • x) (k • y) = (k * k) • symplOH S T x y := by
    intro x y k
    have h1 : symplO S T (k • x) (k • y) = (k * k) • symplO S T x y := by
      rw [← symplHom_apply, map_nsmul, map_nsmul, AddMonoidHom.nsmul_apply, symplHom_apply, smul_smul]
    rw [symplOH, symplOH, h1]
    simp only [nsmul_eq_mul]
    ring
  have hcc : c • c • Y ∈ Λ := nsmul_mem ha c
  obtain ⟨k, hk, hsign⟩ := GlobalTheory.LatVacSign.heisO_finRat_sign ψ S T N N' hV.1 hSd hTd f₀ hvac
    (-(((c : D.host.E) ^ 2) • X)) (by
      rw [neg_neg, hsmM, ← hY, pow_two, map_mul, mul_smul, ← hnat, ← hnat]; exact hcc)
  rw [neg_neg, hsmM, ← hY, pow_two, map_mul, mul_smul, ← hnat, ← hnat] at hsign
  set X1 := e • (c • c • Y) with hX1
  have hY1 : e • Y + R = Y := by rw [hRdef, ← add_smul, add_sub_cancel, one_smul]
  have hdec : c • c • Y = X1 + c • c • R := by
    calc c • c • Y = c • c • (e • Y + R) := by rw [hY1]
      _ = X1 + c • c • R := by rw [hX1, smul_add, smul_add, smul_comm e c, smul_comm e c]
  have hfixXn : heisO ψ S T (-X1) f₀ = f₀ := by
    have h := (GlobalTheory.IdemSumVac.heisO_idemSum_fix D ψ S T Λ f₀ hvac hstab e SS hE _ (neg_mem hcc)).1
    rwa [smul_neg] at h
  have hzero : symplOH S T (-X1) X1 = 0 := by
    have h0' : hO S T (-X1) X1 = 0 := by
      rw [hX1, ← smul_neg, GlobalTheory.LatVacSign.hO_smul_smul, hE.2, zero_mul]
    rw [symplOH, symplO, h0', mul_zero, map_zero, mul_zero]
  have hinv : ∀ g, heisO ψ S T (-X1) (heisO ψ S T X1 g) = g := by
    intro g
    rw [GlobalTheory.LatVac.heisO_heisO, hzero, AddChar.map_zero_eq_one, one_smul, neg_add_cancel, GlobalTheory.LatVac.heisO_zero]
  have hcR : c • c • R ∈ Λ := nsmul_mem (nsmul_mem hR c) c
  have hcoc4 : ψ (symplOH S T X1 (c • c • R)) = 1 := by
    have h := GlobalTheory.T.halfCocycle_isotropic_idempotentHalves_trivial D ψ θ S T δ sc hP e SS hE h2qd N N' hSd hTd _ hcc _ hcR
    have e1 : symplOH S T X1 (c • c • R) = symplOH S T (e • (c • c • Y)) (cA D e • (c • c • R)) := by
      rw [hX1, symplOH, symplOH, ← GlobalTheory.SplitScalar.symplO_smul, smul_smul e e, he2]
    rw [e1]; exact h
  obtain ⟨m, hm⟩ := id hcP
  have hR2eq : c • c • R = R + 2 • ((2 * m * m + 2 * m) • R) := by
    have h1 : R + 2 • ((2 * m * m + 2 * m) • R) = (1 + 2 * (2 * m * m + 2 * m)) • R := by
      rw [add_smul 1 (2 * (2 * m * m + 2 * m)) R, one_smul, mul_smul]
    rw [h1, smul_smul]
    congr 1; subst hm; ring
  have hRR : heisO ψ S T (c • c • R) f₀ = heisO ψ S T R f₀ := by
    have hmR : (2 * m * m + 2 * m) • R ∈ Λ := nsmul_mem hR _
    have h1 := GlobalTheory.LatVac.heisO_heisO ψ R (2 • ((2 * m * m + 2 * m) • R)) f₀
    have hs : symplOH S T R (2 • ((2 * m * m + 2 * m) • R)) = symplO S T R ((2 * m * m + 2 * m) • R) := by
      rw [symplOH, ← symplHom_apply, map_nsmul, symplHom_apply, nsmul_eq_mul, ← mul_assoc]
      have h12 : algebraMap D.host.F (AF D.host.F) (1 / 2) * ((2 : ℕ) : AF D.host.F) = 1 := by
        rw [← map_natCast (algebraMap D.host.F (AF D.host.F)), ← map_mul]; norm_num
      rw [h12, one_mul]
    rw [hvac.1 _ hmR, hs, GlobalTheory.LatVac.char_sympl_eq_one hV.1 hSd hTd hR hmR, one_smul, ← hR2eq] at h1
    exact h1.symm
  have hRk : heisO ψ S T R f₀ = ((-1 : ℂ) ^ k) • f₀ := by
    have h1 := GlobalTheory.LatVac.heisO_heisO ψ X1 (c • c • R) f₀
    rw [hcoc4, one_smul, ← hdec, hsign, hRR] at h1
    have h2' := congrArg (heisO ψ S T (-X1)) h1
    rw [hinv, GlobalTheory.LatVac.heisO_smul, hfixXn] at h2'
    exact h2'

  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℤ, (k₀ : ℚ) = Algebra.trace ℚ D.host.E (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 *
      GlobalTheory.LatVac.hRat S T X X) :=
    GlobalTheory.T.halfA_signTrace_isInteger D ψ θ S T δ sc hP e SS hE h2qd N N' hSd hTd c hc hcP x' hx
  have hα : alV D.host.d sc (embH (tauE D) δ x') = (-1 : ℂ) ^ k₀ := by
    have h := GlobalTheory.SemiTrace.alV_embH_eq_neg_one_zpow D ψ θ S T S.rank T.rank rfl rfl δ sc hP x' k₀ (by simpa using hk₀)
    exact h
  have hkk : k = (c : ℤ) ^ 4 * k₀ := by
    have e1 : GlobalTheory.LatVac.hRat S T (-(((c : D.host.E) ^ 2) • X)) (-(((c : D.host.E) ^ 2) • X)) =
        ((c : ℚ) ^ 4 : ℚ) • GlobalTheory.LatVac.hRat S T X X := by
      rw [← neg_smul, GlobalTheory.LatVacSign.hRat_smul_smul, star_neg, star_pow, star_natCast, Algebra.smul_def]
      push_cast; ring
    have e2 : (k : ℚ) = (c : ℚ) ^ 4 * k₀ := by
      rw [hk, e1, mul_smul_comm, map_smul, hk₀, smul_eq_mul]
    exact_mod_cast e2
  have hodd : Odd ((c : ℤ) ^ 4) := by
    obtain ⟨m', hm'⟩ := id hcP
    exact (show Odd (c : ℤ) from ⟨m', by exact_mod_cast hm'⟩).pow
  have hsgn : ((-1 : ℂ) ^ k) = alV D.host.d sc (embH (tauE D) δ x') := by
    rw [hα, hkk, _root_.zpow_mul, hodd.neg_one_zpow]
  rw [hXt, hYR, hRk, hsgn]

end GlobalTheory.HalfARest
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorFinitePartRestActsBySemicharacStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergOperator_finitePartRest_acts_by_semicharacter : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S N → IsSelfDualC T N' → ∀ (c : ℕ), 0 < c → Odd c → ∀ f₀, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) f₀ → ∀ x' ∈ halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, heisO ψ S T ((GlobalTheory.VacUnique.finRat S T (LinearMap.toMatrix' x')) - ((LinearMap.toMatrix' x').map fun r => e * incA D r)) f₀ = alV D.host.d sc (embH (tauE D) δ x') • f₀ := by
  first | exact @GlobalTheory.HalfARest.heisO_rest_eq | exact GlobalTheory.HalfARest.heisO_rest_eq | (intros; apply GlobalTheory.HalfARest.heisO_rest_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HalfAIdempotentComponentCocycleTrivial
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HalfAIdempotentComponentCocycleTrivial
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.CocycleSS
open GlobalTheory.LatVac

variable {D : D7}

theorem natCast_smul_mem_of_halfAO {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}
    {SS : Finset (HeightOneSpectrum (𝓞 E))} {M : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b)} {c : ℕ} (hc : 0 < c)
    {x : Formalism.L2.Col.HomE E a b} (hx : x ∈ halfAO SS M c) : (c : E) • x ∈ M := by
  refine GlobalTheory.ThetaMove.mem_of_locP fun Q => ?_
  have h : ((c : E) ^ (-expS SS Q))⁻¹ • x ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M := (Submodule.mem_iInf _).1 hx Q
  have hc' : (c : E) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  have key : ∀ k : ℕ, (c : E) = (c : E) ^ k * ((c : E) ^ (-expS SS Q))⁻¹ →
      (c : E) • x ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M := fun k hk => by
    have := nsmul_mem h (c ^ k)
    rwa [← Nat.cast_smul_eq_nsmul E, smul_smul, Nat.cast_pow, ← hk] at this
  unfold expS at key
  split_ifs at key
  · exact key 0 (by simp)
  · exact key 2 (by rw [neg_neg, zpow_one]; field_simp)
  · exact key 1 (by simp)

theorem conjP_conjP (Q : HeightOneSpectrum (𝓞 D.host.E)) : Formalism.L2.Col.conjPrime₂ (Formalism.L2.Col.conjPrime₂ Q) = Q := by
  apply HeightOneSpectrum.ext
  ext r
  rw [Formalism.L2.Col.mem_conjP, Formalism.L2.Col.mem_conjP, Formalism.L2.Col.cO_cO]

theorem conjP_not_mem {e : AE D} {SS : Finset (Formalism.L2.DIV.Pl D.host.E)} (h : IsIdemSum e SS)
    {PP : HeightOneSpectrum (𝓞 D.host.E)} (hPP : PP ∈ SS) : Formalism.L2.Col.conjPrime₂ PP ∉ SS := fun h' =>
  GlobalTheory.ChainOnto.FlagAct.not_isConjPl_of_idemSum h PP hPP _ h' fun r hr =>
    ⟨Formalism.L2.Col.cO D.host.E r, by rw [Formalism.L2.Col.mem_conjP, Formalism.L2.Col.cO_cO]; exact hr, rfl⟩

end GlobalTheory.AdForm.CocycleSS

namespace GlobalTheory.AdForm.CocycleSS
open GlobalTheory.LatVac

variable {D : D7} {S T : HSp D}

theorem smul_tmul_fin {a : AE D} (ha : infPart D a = 0) (r : D.host.E) :
    a * ((pairA D.host.F 0 1) ⊗ₜ[D.host.F] r) = a * incA D r :=
  GlobalTheory.SplitScalar.adele_ext (by rw [RingHom.map_mul, RingHom.map_mul, ha, zero_mul, zero_mul])
    (by rw [RingHom.map_mul, RingHom.map_mul]; rfl)

theorem symplOH_smul (a : AE D) (x y : WO S T) : symplOH S T (a • x) y = symplOH S T x (cA D a • y) := by
  rw [symplOH, symplOH, GlobalTheory.SplitScalar.symplO_smul]

theorem lhs_eq {e : AE D} (hinf : infPart D (cA D e) = 0) (hec : e * cA D e = 0)
    (X : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    symplOH S T (X.map fun r => e * incA D r) (GlobalTheory.VacUnique.finRat S T X - X.map fun r => e * incA D r) =
      symplOH S T (X.map (incA D)) (cA D e • X.map (incA D)) := by
  have hXt : (X.map fun r => e * incA D r : WO S T) = e • (X.map (incA D) : WO S T) := by ext i j; rfl
  have hF : cA D e • GlobalTheory.VacUnique.finRat S T X = cA D e • (X.map (incA D) : WO S T) := by
    ext i j; exact smul_tmul_fin hinf _
  rw [hXt, symplOH_smul, smul_sub, hF, smul_smul, mul_comm, hec, zero_smul, sub_zero]

theorem smul_finRat_natCast {e : AE D} (hinf : infPart D e = 0) (c : ℕ) (X : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    e • GlobalTheory.VacUnique.finRat S T ((c : D.host.E) • X) = (e * incA D (c : D.host.E)) • (X.map (incA D) : WO S T) := by
  ext i j
  show e * ((pairA D.host.F 0 1) ⊗ₜ[D.host.F] ((c : D.host.E) * X i j)) = (e * incA D (c : D.host.E)) * incA D (X i j)
  rw [smul_tmul_fin hinf, map_mul, mul_assoc]

theorem smul_map_inv {e : AE D} (hcc : cA D e * cA D e = cA D e) (c : ℕ) (X : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    cA D e • (((c : D.host.E)⁻¹ • X).map fun r => cA D e * incA D r : WO S T) =
      (cA D e * incA D ((c : D.host.E)⁻¹)) • (X.map (incA D) : WO S T) := by
  ext i j
  show cA D e * (cA D e * incA D ((c : D.host.E)⁻¹ * X i j)) = (cA D e * incA D ((c : D.host.E)⁻¹)) * incA D (X i j)
  rw [map_mul, ← mul_assoc, hcc, mul_assoc]

theorem cA_incA_natCast (c : ℕ) : cA D (incA D (c : D.host.E)) = incA D (c : D.host.E) := by
  show incA D (star (c : D.host.E)) = _
  rw [star_natCast]

theorem rhs_eq {e : AE D} (hinf : infPart D e = 0) (hcc : cA D e * cA D e = cA D e) {c : ℕ} (hc : 0 < c)
    (X : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    symplOH S T (e • GlobalTheory.VacUnique.finRat S T ((c : D.host.E) • X))
        (cA D e • (((c : D.host.E)⁻¹ • X).map fun r => cA D e * incA D r : WO S T)) =
      symplOH S T (X.map (incA D)) (cA D e • X.map (incA D)) := by
  have hcE : (c : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  have hs : cA D e * incA D (c : D.host.E) * (cA D e * incA D ((c : D.host.E)⁻¹)) = cA D e := by
    rw [mul_mul_mul_comm, hcc, ← map_mul, mul_inv_cancel₀ hcE, map_one, mul_one]
  rw [smul_finRat_natCast hinf, smul_map_inv hcc, symplOH_smul, smul_smul, RingHom.map_mul, cA_incA_natCast, hs]

theorem finRat_mem {N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hcc : D.host.ccK = ⊤) (hN : IsSelfDualC S N) {SS : Finset (HeightOneSpectrum (𝓞 D.host.E))} {c : ℕ} (hc : 0 < c)
    {x' : Formalism.L2.Col.HomE D.host.E S.rank T.rank}
    (hx : x' ∈ halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c) :
    GlobalTheory.VacUnique.finRat S T (LinearMap.toMatrix' ((c : D.host.E) • x')) ∈
      latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True := by
  have e1 : GlobalTheory.VacUnique.finRat S T (LinearMap.toMatrix' ((c : D.host.E) • x')) =
      finTens 1 (LinearMap.toMatrix' ((c : D.host.E) • x')) := by ext i j; rfl
  rw [e1]
  exact finTens_mem_latO (one_mem_intAf _)
    (GlobalTheory.AdForm.HalfPairing.toMatrix_mem_latRat hcc hN (natCast_smul_mem_of_halfAO hc hx))

theorem conjHalf_mem {N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hcc : D.host.ccK = ⊤) (hN : IsSelfDualC S N) {e : AE D} {SS : Finset (Formalism.L2.DIV.Pl D.host.E)} (hE : IsIdemSum e SS)
    {c : ℕ} {x' : Formalism.L2.Col.HomE D.host.E S.rank T.rank}
    (hx : x' ∈ halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c) :
    ((LinearMap.toMatrix' ((c : D.host.E)⁻¹ • x')).map fun r => cA D e * incA D r : WO S T) ∈
      latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True := by
  have hno : ∀ PP ∈ SS, Formalism.L2.Col.conjPrime₂ PP ∉ SS := fun PP hPP => conjP_not_mem hE hPP
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := hE
  have e1 : ((LinearMap.toMatrix' ((c : D.host.E)⁻¹ • x')).map fun r => cA D (∑ PP ∈ SS, es PP) * incA D r : WO S T) =
      ∑ PP ∈ SS, ((LinearMap.toMatrix' ((c : D.host.E)⁻¹ • x')).map fun r => cA D (es PP) * incA D r : WO S T) := by
    ext i j
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.map_apply, Matrix.sum_apply, map_sum, Finset.sum_mul]
    rfl
  rw [e1]
  refine sum_mem fun PP hPP => GlobalTheory.AdForm.HalfPairing.conj_comp_mem hcc hN (hes PP hPP) ?_ ?_
  · refine GlobalTheory.PlaceVec.idemSum_infPart (P := {PP}) ⟨⟨es, fun Q hQ => ?_, (Finset.sum_singleton _ _).symm⟩, (hes PP hPP).1.2.1⟩
    rw [Finset.mem_singleton.1 hQ]
    exact hes PP hPP
  · have h : ((c : D.host.E) ^ (-expS SS (Formalism.L2.Col.conjPrime₂ PP)))⁻¹ • x' ∈
        Formalism.HermitianLatticesTheory.localization₂ (Formalism.L2.Col.conjPrime₂ PP).asIdeal (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') :=
      (Submodule.mem_iInf _).1 hx _
    have hexp : expS SS (Formalism.L2.Col.conjPrime₂ PP) = -1 := by
      unfold expS
      rw [if_neg (hno PP hPP), conjP_conjP, if_pos hPP]
    rw [hexp, neg_neg, zpow_one] at h
    exact h

theorem cocycle_trivial : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S N → IsSelfDualC T N' → ∀ (c : ℕ), 0 < c → Odd c → ∀ x' ∈ halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, ψ (symplOH S T ((LinearMap.toMatrix' x').map fun r => e * incA D r) ((GlobalTheory.VacUnique.finRat S T (LinearMap.toMatrix' x')) - ((LinearMap.toMatrix' x').map fun r => e * incA D r))) = 1 := by
  intro D ψ θ S T δ sc hP e SS hE h2 N N' hN hN' c hc _hodd x' hx
  have hinf : infPart D e = 0 := GlobalTheory.PlaceDatum.infPart_idemSum hE
  have hinfc : infPart D (cA D e) = 0 := GlobalTheory.PlaceDatum.infPart_cA hinf
  have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self hE
  have hcc : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, hee]
  have H := GlobalTheory.HalfCocycle.char_symplOH_idem_conj D ψ θ S T δ sc hP e SS hE h2 N N' hN hN' _ (finRat_mem hP.cc hN hc hx) _
    (conjHalf_mem hP.cc hN hE hx)
  have e1 : ∀ r : D.host.E, (LinearMap.toMatrix' (r • x') : Matrix (Fin T.rank) (Fin S.rank) D.host.E) =
      r • LinearMap.toMatrix' x' := fun r => LinearEquiv.map_smul LinearMap.toMatrix' r x'
  rw [e1, e1, rhs_eq hinf hcc hc] at H
  rw [lhs_eq hinfc hE.2]
  exact H

end GlobalTheory.AdForm.CocycleSS
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HalfAIdempotentComponentCocycleTrivialStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.halfA_idempotent_component_cocycle_trivial : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S N → IsSelfDualC T N' → ∀ (c : ℕ), 0 < c → Odd c → ∀ x' ∈ halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, ψ (symplOH S T ((LinearMap.toMatrix' x').map fun r => e * incA D r) ((GlobalTheory.VacUnique.finRat S T (LinearMap.toMatrix' x')) - ((LinearMap.toMatrix' x').map fun r => e * incA D r))) = 1 := by
  first | exact @GlobalTheory.AdForm.CocycleSS.cocycle_trivial | exact GlobalTheory.AdForm.CocycleSS.cocycle_trivial | (intros; apply GlobalTheory.AdForm.CocycleSS.cocycle_trivial <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorHalfComponentOnVacuumTranslate
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.AdForm.HalfHeis.heisO_halfA_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (c : ℕ), 0 < c → Odd c → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → LaFacts (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → (ΛS : Set (Fin S.rank → D.host.E)) = latFr S hS N → (ΛT : Set (Fin T.rank → D.host.E)) = latFr T hT N' → ∀ f₀, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (latFr S hS N) (latFr T hT N') f₀ → ∀ x' ∈ halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, ∀ y' ∈ halfBO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, heisO ψ S T (((LinearMap.toMatrix' (x')).reindex (finCongr hT.symm) (finCongr hS.symm)).map fun r => e * incA D r) (heisO ψ S T (GlobalTheory.VacUnique.finRat S T ((LinearMap.toMatrix' (y')).reindex (finCongr hT.symm) (finCongr hS.symm))) f₀) = alV D.host.d sc (embH (tauE D) δ x') • heisO ψ S T (GlobalTheory.VacUnique.finRat S T ((LinearMap.toMatrix' (x')).reindex (finCongr hT.symm) (finCongr hS.symm))) (heisO ψ S T (GlobalTheory.VacUnique.finRat S T ((LinearMap.toMatrix' (y')).reindex (finCongr hT.symm) (finCongr hS.symm))) f₀) := by
  intro D ψ θ S T a b hS hT δ sc hP e SS hE N N' c hc hcP h2 _ ΛS ΛT dS dT eS eT f₀ hV x' hx y' hy
  subst hS hT
  obtain rfl : ΛS = N := SetLike.coe_injective eS
  obtain rfl : ΛT = N' := SetLike.coe_injective eT
  rw [← eS, ← eT] at hV
  change heisO ψ S T ((LinearMap.toMatrix' x').map fun r => e * incA D r)
      (heisO ψ S T (GlobalTheory.VacUnique.finRat S T (LinearMap.toMatrix' y')) f₀) =
    alV D.host.d sc (embH (tauE D) δ x') • heisO ψ S T (GlobalTheory.VacUnique.finRat S T (LinearMap.toMatrix' x'))
      (heisO ψ S T (GlobalTheory.VacUnique.finRat S T (LinearMap.toMatrix' y')) f₀)
  set Xt : WO S T := (LinearMap.toMatrix' x').map fun r => e * incA D r with hXt
  set FX := GlobalTheory.VacUnique.finRat S T (LinearMap.toMatrix' x') with hFX
  set FY := GlobalTheory.VacUnique.finRat S T (LinearMap.toMatrix' y') with hFY
  set α := alV D.host.d sc (embH (tauE D) δ x') with hα
  have hact := GlobalTheory.T.heisenbergOperator_finitePartRest_acts_by_semicharacter D ψ θ S T δ sc hP e SS hE h2 ΛS ΛT dS dT c hc hcP f₀ hV x' hx
  have hcomm := GlobalTheory.T.addChar_symplectic_finitePartRest_eq_one D ψ θ S T δ sc hP e SS hE h2 ΛS ΛT dS dT c hc hcP x' hx y' hy
  have hcoc := GlobalTheory.T.halfA_idempotent_component_cocycle_trivial D ψ θ S T δ sc hP e SS hE h2 ΛS ΛT dS dT c hc hcP x' hx
  have hsq := GlobalTheory.T.semicharacter_sq_eq_one_on_halfA D ψ θ S T δ sc hP e SS hE h2 ΛS ΛT dS dT c hc hcP x' hx
  have hZ : heisO ψ S T (FX - Xt) (heisO ψ S T FY f₀) = α • heisO ψ S T FY f₀ := by
    rw [GlobalTheory.SplitScalar.heisO_comm, hcomm, one_smul, hact, GlobalTheory.SplitScalar.heisO_smul]
  have hX := GlobalTheory.SplitScalar.heisO_heisO ψ S T Xt (FX - Xt) (heisO ψ S T FY f₀)
  rw [hcoc, one_smul, add_sub_cancel, hZ, GlobalTheory.SplitScalar.heisO_smul] at hX
  rw [← hX, smul_smul, hsq, one_smul]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorHalfComponentOnVacuumTranslateStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergOperator_halfComponent_on_vacuumTranslates : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (c : ℕ), 0 < c → Odd c → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → LaFacts (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → (ΛS : Set (Fin S.rank → D.host.E)) = latFr S hS N → (ΛT : Set (Fin T.rank → D.host.E)) = latFr T hT N' → ∀ f₀, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (latFr S hS N) (latFr T hT N') f₀ → ∀ x' ∈ halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, ∀ y' ∈ halfBO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, heisO ψ S T (((LinearMap.toMatrix' (x')).reindex (finCongr hT.symm) (finCongr hS.symm)).map fun r => e * incA D r) (heisO ψ S T (GlobalTheory.VacUnique.finRat S T ((LinearMap.toMatrix' (y')).reindex (finCongr hT.symm) (finCongr hS.symm))) f₀) = alV D.host.d sc (embH (tauE D) δ x') • heisO ψ S T (GlobalTheory.VacUnique.finRat S T ((LinearMap.toMatrix' (x')).reindex (finCongr hT.symm) (finCongr hS.symm))) (heisO ψ S T (GlobalTheory.VacUnique.finRat S T ((LinearMap.toMatrix' (y')).reindex (finCongr hT.symm) (finCongr hS.symm))) f₀) := by
  first | exact @GlobalTheory.AdForm.HalfHeis.heisO_halfA_eq | exact GlobalTheory.AdForm.HalfHeis.heisO_halfA_eq | (intros; apply GlobalTheory.AdForm.HalfHeis.heisO_halfA_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFourierSumEqSumHeisenbergTranslates
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFourierSumEqSumHeisenbergTranslates
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfFourier

theorem thetaAt_eq_sum_heis_translates : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (e : AE D) (Λ : AddSubgroup (WO S T)) (f₀ Φ f : WO S T → ℂ) (ι : Type) (s : Finset ι) (K : ι → ℂ) (xs ys : ι → WO S T) (k : ℕ), 0 < k → IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Φ f → (∀ i ∈ s, IsHalf e (xs i)) → (∀ i ∈ s, IsHalf (cA D e) (ys i)) → (∀ i ∈ s, ∀ u ∈ Λ, ψ (symplO S T (k • u) (ys i)) = 1) → (∀ t, Φ t = ∑ i ∈ s, K i * (ψ (symplO S T (t + xs i) (ys i)) * halfInd e Λ (t + xs i))) → f = ∑ i ∈ s, K i • heisO ψ S T (xs i) (heisO ψ S T (ys i) f₀) := by
  intro D ψ S T e Λ f₀ Φ f ι s K xs ys k hk hθ hx hy hΛ hΦ
  classical
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hθ
  have hvac : Tm (halfInd e Λ) = f₀ := by simpa using hTm.vac

  set g : ι → WO S T → ℂ := fun i t => ψ (symplO S T t (ys i)) * halfInd e Λ t with hg
  have hhalf : ∀ t, halfInd e Λ t ≠ 0 → t ∈ Λ ∧ IsHalf e t := by
    intro t ht
    by_contra h
    exact ht (by simp [halfInd, h])
  have hSB : ∀ i ∈ s, IsSBHalf e Λ (g i) := by
    intro i hi
    refine ⟨fun t ht => ?_, k, hk, fun u hu hh t => ?_, fun t ht => ?_⟩
    · exact (hhalf t (right_ne_zero_of_mul ht)).2
    · have hku : k • u ∈ Λ := Λ.nsmul_mem hu k
      have hkh : IsHalf e (k • u) := by
        intro a b
        change e * ((k • u : Matrix _ _ (AE D)) a b) = (k • u : Matrix _ _ (AE D)) a b
        rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, hh a b]
      have hind : halfInd e Λ (t + k • u) = halfInd e Λ t := by
        have : (t + k • u ∈ Λ ∧ IsHalf e (t + k • u)) ↔ (t ∈ Λ ∧ IsHalf e t) := by
          rw [Λ.add_mem_cancel_right hku]
          refine and_congr_right fun _ => forall_congr' fun a => forall_congr' fun b => ?_
          rw [Matrix.add_apply, mul_add, hkh a b, add_left_inj]
        simp only [halfInd, this]
      simp only [hg, hind, GlobalTheory.LatVac.symplO_add_left, AddChar.map_add_eq_mul, hΛ i hi u hu, mul_one]
    · exact Λ.nsmul_mem (hhalf t (right_ne_zero_of_mul ht)).1 k
  have hΦ' : Φ = ∑ i ∈ s, K i • fun t => g i (t + xs i) := by
    funext t
    rw [hΦ t, Finset.sum_apply]
    rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hall Tm hTm, hΦ', map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [map_smul, hTm.trans _ (hSB i hi) (xs i) (hx i hi)]
  congr 2
  have : g i = fun t => ψ (symplO S T t (ys i)) * halfInd e Λ t := rfl
  rw [this, hTm.modul _ (GlobalTheory.isSBHalf_halfInd e Λ) (ys i) (hy i hi), hvac]

end GlobalTheory.HalfFourier
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFourierSumEqSumHeisenbergTranslatesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFourierSum_eq_sum_heisenberg_translates : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (e : AE D) (Λ : AddSubgroup (WO S T)) (f₀ Φ f : WO S T → ℂ) (ι : Type) (s : Finset ι) (K : ι → ℂ) (xs ys : ι → WO S T) (k : ℕ), 0 < k → IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Φ f → (∀ i ∈ s, IsHalf e (xs i)) → (∀ i ∈ s, IsHalf (cA D e) (ys i)) → (∀ i ∈ s, ∀ u ∈ Λ, ψ (symplO S T (k • u) (ys i)) = 1) → (∀ t, Φ t = ∑ i ∈ s, K i * (ψ (symplO S T (t + xs i) (ys i)) * halfInd e Λ (t + xs i))) → f = ∑ i ∈ s, K i • heisO ψ S T (xs i) (heisO ψ S T (ys i) f₀) := by
  first | exact @GlobalTheory.HalfFourier.thetaAt_eq_sum_heis_translates | exact GlobalTheory.HalfFourier.thetaAt_eq_sum_heis_translates | (intros; apply GlobalTheory.HalfFourier.thetaAt_eq_sum_heis_translates <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodLatticeHalvesRepsFiniteIndex
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodLatticeHalvesRepsFiniteIndex
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.PeriodReps
open _root_.Formalism.L2.Th1.H

section General
variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℝ V] [IsScalarTower ℝ ℂ V] [FiniteDimensional ℝ V]

theorem altE_add_left' (H : Sesq V) (x y z : V) : altE H (x + y) z = altE H x z + altE H y z := by
  simp [altE, map_add (f := _)]

theorem altE_add_right' (H : Sesq V) (x y z : V) : altE H x (y + z) = altE H x y + altE H x z := by
  simp [altE, map_add (f := _)]

theorem real_smul_eq (r : ℝ) (x : V) : r • x = (r : ℂ) • x := by
  rw [← algebraMap_smul ℂ r x]; rfl

theorem altE_smul_left' (H : Sesq V) (r : ℝ) (x y : V) : altE H (r • x) y = r * altE H x y := by
  rw [real_smul_eq]; simp [altE]

theorem altE_smul_right' (H : Sesq V) (r : ℝ) (x y : V) : altE H x (r • y) = r * altE H x y := by
  rw [real_smul_eq]; unfold altE; rw [(H x).map_smulₛₗ]; simp

theorem fg_of_selfDual (H : Sesq V) (Λ : AddSubgroup V) (hc : Countable Λ) (hΛ : IsSelfDual H Λ) : Λ.FG := by
  classical
  have hK : ∀ x : V, (∀ y ∈ Λ, altE H x y = 0) → x = 0 := by
    intro x hx
    by_contra hx0
    have hmem : ∀ t : ℝ, t • x ∈ Λ := fun t => by
      have h1 : t • x ∈ dualLat H Λ := fun y hy => ⟨0, by rw [altE_smul_left', hx y hy]; simp⟩
      rwa [hΛ] at h1
    let f : ℝ → Λ := fun t => ⟨t • x, hmem t⟩
    have hf : Function.Injective f := fun s t h => by
      have : s • x = t • x := congrArg Subtype.val h
      exact smul_left_injective ℝ hx0 this
    exact not_countable (α := ℝ) hf.countable
  obtain ⟨b, hbΛ, hbspan, hbli⟩ := exists_linearIndependent ℝ (Λ : Set V)
  haveI : Finite b := hbli.setFinite.to_subtype
  have hint : ∀ x ∈ Λ, ∀ e ∈ b, ((⌊altE H x e⌋ : ℤ) : ℝ) = altE H x e := by
    intro x hx e he
    have hx' : x ∈ dualLat H Λ := by rw [hΛ]; exact hx
    obtain ⟨m, hm⟩ := hx' e (hbΛ he)
    rw [hm, Int.floor_intCast]
  let g : Λ →+ (b → ℤ) :=
    { toFun := fun x e => ⌊altE H (x : V) e⌋
      map_zero' := by funext e; simp [altE]
      map_add' := fun x y => by
        funext e
        apply Int.cast_injective (α := ℝ)
        simp only [Pi.add_apply, Int.cast_add]
        rw [hint _ (x + y).2 _ e.2, hint _ x.2 _ e.2, hint _ y.2 _ e.2]
        simp [altE_add_left'] }
  have hg : Function.Injective g := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    have h0 : ∀ e ∈ b, altE H (x : V) e = 0 := fun e he => by
      have h2 : ⌊altE H (x : V) e⌋ = 0 := congrFun hx ⟨e, he⟩
      rw [← hint _ x.2 _ he, h2]; simp
    have hspan : ∀ y ∈ Submodule.span ℝ b, altE H (x : V) y = 0 := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy => exact h0 y hy
      | zero => simp [altE]
      | add y z _ _ hy hz => rw [altE_add_right', hy, hz, add_zero]
      | smul r y _ hy => rw [altE_smul_right', hy, mul_zero]
    exact Subtype.ext (hK x fun y hy => hspan y (hbspan ▸ Submodule.subset_span hy))
  haveI : IsNoetherian ℤ Λ := isNoetherian_of_injective g.toIntLinearMap hg
  have : AddGroup.FG Λ := Module.Finite.iff_addGroup_fg.1 inferInstance
  exact (AddGroup.fg_iff_addSubgroup_fg Λ).1 this

end General
end GlobalTheory.PeriodReps

namespace GlobalTheory.PeriodReps
open _root_.Formalism.L2.Th1.H

theorem countable_lamC {E : Type} [Field E] [NumberField E] {ι : Type} [Fintype ι] {a b : ℕ} (emb : ι → E →+* ℂ) (δ : ℂ)
    (AA0 : Submodule (𝓞 E) E) (N : Submodule (𝓞 E) (Formalism.L2.Col.Sp E a)) (N' : Submodule (𝓞 E) (Formalism.L2.Col.Sp E b)) :
    Countable (Formalism.L2.Ker.LamC emb δ AA0 N N') := by
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin b) (Fin a) E) := inferInstanceAs (Countable (Fin b → Fin a → E))
  haveI : Countable (Formalism.L2.Col.HomE E a b) :=
    (LinearMap.toMatrix' : ((Fin a → E) →ₗ[E] (Fin b → E)) ≃ₗ[E] Matrix (Fin b) (Fin a) E).injective.countable
  have hsub : ((Formalism.L2.Ker.LamC emb δ AA0 N N' : AddSubgroup _) : Set (Formalism.L2.Ker.VV ι a b)) ⊆
      Set.range (Formalism.L2.Ker.embH emb δ) := by
    intro y hy
    simp only [Formalism.L2.Ker.LamC, Formalism.L2.Ker.laV, SetLike.mem_coe, AddSubgroup.mem_map] at hy
    obtain ⟨x, -, rfl⟩ := hy
    exact ⟨x, rfl⟩
  exact ((Set.countable_range _).mono hsub).to_subtype

theorem reps_genuine : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (c : ℕ), 0 < c → Odd c → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → LaFacts (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' → Formalism.L2.Th1.H.IsReps (LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') (AC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c) (repsOf (LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') (AC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c)) ∧ Formalism.L2.Th1.H.IsReps (BC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c) ((LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') ⊓ (AC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c)) (repsOf (BC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c) ((LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') ⊓ (AC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c))) ∧ Formalism.L2.Th1.H.IsReps (LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') (BC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c) (repsOf (LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') (BC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c)) := by
  intro D ψ θ S T a b hS hT δ sc hSP e SS hSS N N' c hc hcS hSS2 hLa
  have hfg := fg_of_selfDual _ _ (countable_lamC _ _ _ _ _) hLa.1
  obtain ⟨i1, i2, i3⟩ := Formalism.L2.Ker.finite_index_of_fg _ _ _ _ (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c hc hfg
  exact ⟨Formalism.L2.Ker.repsOf_spec _ _ i1, Formalism.L2.Ker.repsOf_spec _ _ i2, Formalism.L2.Ker.repsOf_spec _ _ i3⟩

end GlobalTheory.PeriodReps
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodLatticeHalvesRepsFiniteIndexStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodLatticeHalves_reps_finite_index : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (c : ℕ), 0 < c → Odd c → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → LaFacts (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' → Formalism.L2.Th1.H.IsReps (LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') (AC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c) (repsOf (LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') (AC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c)) ∧ Formalism.L2.Th1.H.IsReps (BC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c) ((LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') ⊓ (AC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c)) (repsOf (BC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c) ((LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') ⊓ (AC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c))) ∧ Formalism.L2.Th1.H.IsReps (LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') (BC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c) (repsOf (LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') (BC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c)) := by
  first | exact @GlobalTheory.PeriodReps.reps_genuine | exact GlobalTheory.PeriodReps.reps_genuine | (intros; apply GlobalTheory.PeriodReps.reps_genuine <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DatumReadingSplitPlacesEqClassicalTheta
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.DatumRead

theorem reads_datum_eq_thC : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ e (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (c : ℕ), 0 < c → Odd c → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → LaFacts (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' → (∃ ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E), IsSelfDualC S ΛS ∧ (ΛS : Set (Fin S.rank → D.host.E)) = latFr S hS N) → (∃ ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E), IsSelfDualC T ΛT ∧ (ΛT : Set (Fin T.rank → D.host.E)) = latFr T hT N') → ∀ f₀ Φ f (Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ), IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (latFr S hS N) (latFr T hT N') f₀ → IsSBHalf e (latO S T (latFr S hS N) (latFr T hT N') fun _ => True) Φ → IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T (latFr S hS N) (latFr T hT N') fun _ => True) 1 f₀ Φ f → (∀ γ, Φ (γ.map fun r => e * incA D r) = Ξ (toHom S T hS hT γ)) → (∀ x, Ξ x ≠ 0 → (c : D.host.E) • x ∈ Formalism.L2.Col.homAt SS N N') → (∀ x, ∀ y ∈ Formalism.L2.Col.homAt SS N N', Ξ (x + (c : D.host.E) • y) = Ξ x) → IsHol θ S T ψ f ∧ xiN θ S T hS hT δ sc f = thC (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c Ξ (xiN θ S T hS hT δ sc f₀) := by
  intro D ψ θ S T a b hS hT δ sc hP e SS hE N N' c hc hcP h2 hLa hdS hdT f₀ Φ f Ξ hV hSB hTh hΦ hΞ1 hΞ2
  classical
  obtain ⟨ΛS, hΛS, hΛS'⟩ := id hdS
  obtain ⟨ΛT, hΛT, hΛT'⟩ := id hdT
  obtain ⟨hRX, hRA, hRB⟩ := GlobalTheory.T.periodLatticeHalves_reps_finite_index D ψ θ S T a b hS hT δ sc hP e SS hE N N' c hc hcP h2 hLa
  set SX := repsOf (LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N')
    (AC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c) with hSXd
  set SA := repsOf (BC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c)
    (LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' ⊓
      AC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c) with hSAd
  set SB := repsOf (LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N')
    (BC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c) with hSBd
  set MA := halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c
  set MB := halfBO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c
  have hpx : ∀ x ∈ SX, ∃ x', x' ∈ MA ∧ embH (tauE D) δ x' = x := fun x hx => by
    obtain ⟨x', hx', h⟩ := AddSubgroup.mem_map.1 (hRX.1 x hx)
    exact ⟨x', hx', h⟩
  have hpy : ∀ y ∈ SB, ∃ y', y' ∈ MB ∧ embH (tauE D) δ y' = y := fun y hy => by
    obtain ⟨y', hy', h⟩ := AddSubgroup.mem_map.1 (hRB.1 y hy)
    exact ⟨y', hy', h⟩
  let px : VV D.what₂.Tau a b → Formalism.L2.Col.HomE D.host.E a b := fun x =>
    if h : ∃ x', x' ∈ MA ∧ embH (tauE D) δ x' = x then h.choose else 0
  let py : VV D.what₂.Tau a b → Formalism.L2.Col.HomE D.host.E a b := fun y =>
    if h : ∃ y', y' ∈ MB ∧ embH (tauE D) δ y' = y then h.choose else 0
  have hpx' : ∀ x ∈ SX, px x ∈ MA ∧ embH (tauE D) δ (px x) = x := fun x hx => by
    simp only [px, dif_pos (hpx x hx)]; exact (hpx x hx).choose_spec
  have hpy' : ∀ y ∈ SB, py y ∈ MB ∧ embH (tauE D) δ (py y) = y := fun y hy => by
    simp only [py, dif_pos (hpy y hy)]; exact (hpy y hy).choose_spec
  let mt : Formalism.L2.Col.HomE D.host.E a b → Matrix (Fin T.rank) (Fin S.rank) D.host.E := fun x =>
    (LinearMap.toMatrix' x).reindex (finCongr hT.symm) (finCongr hS.symm)
  have hmt : ∀ x, toHom S T hS hT (mt x) = x := fun x => by
    simp only [mt]
    unfold toHom
    have h : ((LinearMap.toMatrix' x).reindex (finCongr hT.symm) (finCongr hS.symm)).reindex (finCongr hT) (finCongr hS) =
        LinearMap.toMatrix' x := by
      ext i j; simp [Matrix.reindex_apply]
    rw [h, Matrix.toLin'_toMatrix']
  let K : VV D.what₂.Tau a b × VV D.what₂.Tau a b → ℂ := fun p =>
    ((SA.card : ℂ))⁻¹ * ∑ s ∈ SA, onV (tauE D) δ Ξ (s - p.1) * (brk (HV sc) p.2 s)⁻¹
  have hF := GlobalTheory.T.finite_fourier_expansion_half_split_places D ψ θ S T a b hS hT δ sc hP e SS hE N N' c hc hcP h2 hLa hdS hdT Φ Ξ hSB hΦ hΞ1 hΞ2 SX SA SB hRX hRA hRB px py hpx' hpy'
  have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self hE
  have hf1 : f = ∑ p ∈ SX ×ˢ SB, K p • heisO ψ S T ((mt (px p.1)).map fun r => e * incA D r)
      (heisO ψ S T ((mt (py p.2)).map fun r => cA D e * incA D r) f₀) := by
    refine GlobalTheory.T.thetaFourierSum_eq_sum_heisenberg_translates D ψ S T e _ f₀ Φ f _ (SX ×ˢ SB) K (fun p => (mt (px p.1)).map fun r => e * incA D r)
      (fun p => (mt (py p.2)).map fun r => cA D e * incA D r) c hc hTh ?_ ?_ ?_ ?_
    · intro p _ i j
      simp only [Matrix.map_apply, ← mul_assoc, hee]
    · intro p _ i j
      simp only [Matrix.map_apply, ← mul_assoc, ← map_mul, hee]
    · intro p hp u hu
      exact GlobalTheory.T.stdChar_symplectic_halfPeriodLattice_eq_one D ψ θ S T a b hS hT δ sc hP e SS hE N N' c hc hcP h2 hLa hdS hdT (py p.2) (hpy' _ (Finset.mem_product.1 hp).2).1 u hu
    · intro t
      rw [hF t, Finset.sum_product]

  have hV' := hV
  obtain ⟨hstd, hvac⟩ := hV'
  have h0 : IsThetaFunO ψ S T f₀ := hvac.theta
  have hψ : IsCharAF D.host.F ψ := hstd.1
  set G : VV D.what₂.Tau a b × VV D.what₂.Tau a b → WO S T := fun p =>
    GlobalTheory.VacUnique.finRat S T (mt (px p.1)) + GlobalTheory.VacUnique.finRat S T (mt (py p.2)) with hG
  set C : VV D.what₂.Tau a b × VV D.what₂.Tau a b → ℂ := fun p =>
    K p * (alV D.host.d sc p.1 * alV D.host.d sc p.2) with hC
  have hf2 : f = ∑ p ∈ SX ×ˢ SB, C p • heisO ψ S T (GlobalTheory.VacUnique.finRat S T (mt (px p.1)))
      (heisO ψ S T (GlobalTheory.VacUnique.finRat S T (mt (py p.2))) f₀) := by
    rw [hf1]
    refine Finset.sum_congr rfl fun p hp => ?_
    obtain ⟨h1, h2'⟩ := Finset.mem_product.1 hp
    rw [GlobalTheory.T.heisenbergOperator_conjugateHalf_vacuum_eq_semicharacter D ψ θ S T a b hS hT δ sc hP e SS hE N N' c hc hcP h2 hLa ΛS ΛT hΛS hΛT hΛS' hΛT' f₀ hV (py p.2) (hpy' _ h2').1,
      GlobalTheory.LatVac.heisO_smul,
      GlobalTheory.T.heisenbergOperator_halfComponent_on_vacuumTranslates D ψ θ S T a b hS hT δ sc hP e SS hE N N' c hc hcP h2 hLa ΛS ΛT hΛS hΛT hΛS' hΛT' f₀ hV (px p.1) (hpx' _ h1).1 (py p.2) (hpy' _ h2').1,
      (hpx' _ h1).2, (hpy' _ h2').2, smul_smul, smul_smul, hC]
    congr 1
    ring
  have hf3 : f = ∑ p ∈ SX ×ˢ SB, (C p * ψ (symplOH S T (GlobalTheory.VacUnique.finRat S T (mt (px p.1)))
      (GlobalTheory.VacUnique.finRat S T (mt (py p.2))))) • heisO ψ S T (G p) f₀ := by
    rw [hf2]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [GlobalTheory.LatVac.heisO_heisO, smul_smul]
  have hGi : ∀ p ∈ SX ×ˢ SB, (G p).map (infPart D) = 0 := fun p _ => by
    simp only [hG, ← map_add (f := _)]
    exact GlobalTheory.VacUnique.finRat_inf S T _
  refine ⟨⟨?_, fun τ => ?_⟩, ?_⟩
  · rw [hf3]
    exact GlobalTheory.FinTranslate.isTheta_sum_heisO_fin D ψ S T hψ f₀ h0 _ _ G _ hGi
  · rw [hf3]
    exact GlobalTheory.FockTranslate.isFockVacAt_sum D ψ θ S T hψ hP.inf f₀ h0 τ _ (hvac.fock τ) _ _ G _ hGi
  · have hread : ∀ p ∈ SX ×ˢ SB, xiN θ S T hS hT δ sc (heisO ψ S T (GlobalTheory.VacUnique.finRat S T (mt (px p.1)))
        (heisO ψ S T (GlobalTheory.VacUnique.finRat S T (mt (py p.2))) f₀)) =
        Formalism.L2.Th1.H.opU (HV sc) p.1 (Formalism.L2.Th1.H.opU (HV sc) p.2 (xiN θ S T hS hT δ sc f₀)) := by
      intro p hp
      obtain ⟨h1, h2'⟩ := Finset.mem_product.1 hp
      have hfin : ∀ γ, GlobalTheory.AdTh.IsFinOf S T γ (GlobalTheory.VacUnique.finRat S T γ) := fun γ =>
        ⟨GlobalTheory.VacUnique.finRat_inf S T γ, GlobalTheory.VacUnique.finRat_fin S T γ⟩
      have ht1 : IsThetaFunO ψ S T (heisO ψ S T (GlobalTheory.VacUnique.finRat S T (mt (py p.2))) f₀) :=
        GlobalTheory.FinTranslate.isTheta_heisO_fin hψ (GlobalTheory.VacUnique.finRat_inf S T _) h0
      rw [GlobalTheory.T.gaussianReading_finiteRationalHeisenbergTranslate D ψ θ S T a b hS hT δ sc hP _ ht1 _ _ (hfin _), GlobalTheory.T.gaussianReading_finiteRationalHeisenbergTranslate D ψ θ S T a b hS hT δ sc hP _ h0 _ _ (hfin _),
        hmt, hmt, (hpx' _ h1).2, (hpy' _ h2').2]
    funext z
    have hlin : xiN θ S T hS hT δ sc f z = ∑ p ∈ SX ×ˢ SB, C p * xiN θ S T hS hT δ sc
        (heisO ψ S T (GlobalTheory.VacUnique.finRat S T (mt (px p.1)))
          (heisO ψ S T (GlobalTheory.VacUnique.finRat S T (mt (py p.2))) f₀)) z := by
      rw [hf2]
      simp only [xiN, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      ring
    rw [hlin]
    rw [Finset.sum_congr rfl fun p hp => by rw [hread p hp]]
    show _ = xiL (HV sc) (alV D.host.d sc) 1 SX SA SB (onV (tauE D) δ Ξ) (xiN θ S T hS hT δ sc f₀) z
    rw [GlobalTheory.ThetaCosetSum.xiL_eq_kernel, Finset.sum_product]
    simp only [hC, K, Formalism.L2.Th1.H.opU, Real.sqrt_one, Complex.ofReal_one, inv_one, one_mul, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun t _ => ?_
    ring

end GlobalTheory.AdForm.DatumRead
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DatumReadingSplitPlacesEqClassicalThetaStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.datumReading_splitPlaces_eq_classicalTheta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ e (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (c : ℕ), 0 < c → Odd c → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → LaFacts (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' → (∃ ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E), IsSelfDualC S ΛS ∧ (ΛS : Set (Fin S.rank → D.host.E)) = latFr S hS N) → (∃ ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E), IsSelfDualC T ΛT ∧ (ΛT : Set (Fin T.rank → D.host.E)) = latFr T hT N') → ∀ f₀ Φ f (Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ), IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (latFr S hS N) (latFr T hT N') f₀ → IsSBHalf e (latO S T (latFr S hS N) (latFr T hT N') fun _ => True) Φ → IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T (latFr S hS N) (latFr T hT N') fun _ => True) 1 f₀ Φ f → (∀ γ, Φ (γ.map fun r => e * incA D r) = Ξ (toHom S T hS hT γ)) → (∀ x, Ξ x ≠ 0 → (c : D.host.E) • x ∈ Formalism.L2.Col.homAt SS N N') → (∀ x, ∀ y ∈ Formalism.L2.Col.homAt SS N N', Ξ (x + (c : D.host.E) • y) = Ξ x) → IsHol θ S T ψ f ∧ xiN θ S T hS hT δ sc f = thC (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c Ξ (xiN θ S T hS hT δ sc f₀) := by
  first | exact @GlobalTheory.AdForm.DatumRead.reads_datum_eq_thC | exact GlobalTheory.AdForm.DatumRead.reads_datum_eq_thC | (intros; apply GlobalTheory.AdForm.DatumRead.reads_datum_eq_thC <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelSplitPlacesEqJetClassicalTheta
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker

namespace GlobalTheory.KJInf.CoreG

theorem om_inv_om {D : D7} (S T : HSp D) (om : Om S T) (g : GA D S) (h : GA D T) (f : WO S T → ℂ) :
    om (g⁻¹, h⁻¹) (om (g, h) f) = f := by
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel, ← Prod.one_eq_mk, map_one]
  rfl

theorem selfDual_latFr {D : D7} (V : HSp D) (hV : V.gram = 1) {n : ℕ} (hn : V.rank = n) (g : GA D V)
    (N : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (hN : Moves V hn g N) :
    ∃ Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E), IsSelfDualC V Λ ∧
      (Λ : Set (Fin V.rank → D.host.E)) = latFr V hn N := by
  subst hn
  exact ⟨N, GlobalTheory.SplitMove.selfDual_move V hV g N hN, rfl⟩

theorem thC_const_mul (D : D7) {a b : ℕ} (δ : ℂ) (sc : ℝ) (SS : Finset (Formalism.L2.DIV.Pl D.host.E))
    (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (c : ℕ)
    (Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ) (κ : ℂ) (E : VCx D.what₂.Tau a b → ℂ) :
    thC (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c Ξ (fun z => κ * E z) =
      fun z => κ * thC (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c Ξ E z := by
  funext z
  simp only [thC, xiV, xiL, xiS, Formalism.L2.Th1.H.sumU, Formalism.L2.Th1.H.opU, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

end GlobalTheory.KJInf.CoreG

namespace GlobalTheory.KJInf.CoreG

theorem thetaKernel_eq_jet_thC : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ s : ℂ, (∀ f, IsHol θ S T ψ f → ∀ P, pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) f P 0 = jetP S T hS hT s (xiN θ S T hS hT δ sc f) P) → ∀ (μ : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T μ μ om → ∀ e (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ vac Φ w, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (intVec D _) (intVec D _) vac → IsSBHalf e (stdHom S T) Φ → IsThetaAt ψ (symplO S T) (heisO ψ S T) e (stdHom S T) 1 vac Φ w → ∀ g ∈ GfC S, ∀ h ∈ GfC T, ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), Moves S hS g N → Moves T hT h N' → ∀ c : ℕ, 0 < c → Odd c → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → LaFacts (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' → ∀ Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ, (∀ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E, Φ (actO S T g⁻¹ h⁻¹ (γ.map fun r => e * incA D r)) = Ξ (toHom S T hS hT γ)) → (∀ x, Ξ x ≠ 0 → (c : D.host.E) • x ∈ Formalism.L2.Col.homAt SS N N') → (∀ x, ∀ y ∈ Formalism.L2.Col.homAt SS N N', Ξ (x + (c : D.host.E) • y) = Ξ x) → ∀ (κ : ℂ) (E : VCx D.what₂.Tau a b → ℂ), (xiN θ S T hS hT δ sc (om (g, h) vac) = fun z => κ * E z) → ∀ P, thetaKO om g h (pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) w P) = κ * jetP S T hS hT s (thC (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c Ξ E) P := by
  intro D ψ θ S T a b hS hT δ sc hP s hs μ om hW e SS hE vac Φ w hV hSB hTh g hg h hh N N' hN hN' c hc hcP h2 hLa Ξ hΦ hΞ1 hΞ2 κ E hκ P
  obtain ⟨hSBm, hThm⟩ := GlobalTheory.SplitMove.isThetaAt_move D ψ θ S T a b hS hT δ sc hP μ om hW e SS hE vac Φ w hV.2.theta hV.2.lat
    hSB hTh g hg h hh N N' hN hN'
  obtain ⟨hVm, -, -⟩ := GlobalTheory.MovedVac.vac_moved D ψ θ S T a b hS hT δ sc hP μ om hW vac hV g hg h hh N N' hN hN'
  have hD : IsHol θ S T ψ (om (g, h) w) ∧ xiN θ S T hS hT δ sc (om (g, h) w) =
      thC (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c Ξ (xiN θ S T hS hT δ sc (om (g, h) vac)) := by
    exact GlobalTheory.T.datumReading_splitPlaces_eq_classicalTheta D ψ θ S T a b hS hT δ sc hP e SS hE N N' c hc hcP h2 hLa (selfDual_latFr S hP.gS hS g N hN)
        (selfDual_latFr T hP.gT hT h N' hN') _ _ _ Ξ hVm hSBm hThm hΦ hΞ1 hΞ2
  obtain ⟨hHolm, hxi⟩ := hD
  have hHolw : IsHol θ S T ψ w := by
    have := (GlobalTheory.AdForm.FinComm.finite_comm_creation D ψ θ S T a b hS hT δ sc hP μ om hW g⁻¹ (inv_mem hg) h⁻¹ (inv_mem hh)
      _ hHolm).1
    rwa [om_inv_om] at this
  have hcomm := ((GlobalTheory.AdForm.FinComm.finite_comm_creation D ψ θ S T a b hS hT δ sc hP μ om hW g hg h hh w hHolw).2 P).2
  have hdiff : Differentiable ℂ fun z =>
      κ * thC (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c Ξ E z := by
    rw [← thC_const_mul, ← hκ, ← hxi]
    exact (GlobalTheory.AdForm.VacRead.xiN_entire_and_injective D ψ θ S T a b hS hT δ sc hP).1 _ hHolm
  unfold thetaKO
  rw [hcomm, hs _ hHolm P, hxi, hκ, thC_const_mul]
  unfold jetP
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [GlobalTheory.ColNorms.jetC_const_mul _ _ _ hdiff]
  ring

end GlobalTheory.KJInf.CoreG
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelSplitPlacesEqJetClassicalThetaStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaKernel_splitPlaces_eq_jet_classicalTheta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ s : ℂ, (∀ f, IsHol θ S T ψ f → ∀ P, pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) f P 0 = jetP S T hS hT s (xiN θ S T hS hT δ sc f) P) → ∀ (μ : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T μ μ om → ∀ e (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ vac Φ w, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (intVec D _) (intVec D _) vac → IsSBHalf e (stdHom S T) Φ → IsThetaAt ψ (symplO S T) (heisO ψ S T) e (stdHom S T) 1 vac Φ w → ∀ g ∈ GfC S, ∀ h ∈ GfC T, ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), Moves S hS g N → Moves T hT h N' → ∀ c : ℕ, 0 < c → Odd c → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → LaFacts (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' → ∀ Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ, (∀ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E, Φ (actO S T g⁻¹ h⁻¹ (γ.map fun r => e * incA D r)) = Ξ (toHom S T hS hT γ)) → (∀ x, Ξ x ≠ 0 → (c : D.host.E) • x ∈ Formalism.L2.Col.homAt SS N N') → (∀ x, ∀ y ∈ Formalism.L2.Col.homAt SS N N', Ξ (x + (c : D.host.E) • y) = Ξ x) → ∀ (κ : ℂ) (E : VCx D.what₂.Tau a b → ℂ), (xiN θ S T hS hT δ sc (om (g, h) vac) = fun z => κ * E z) → ∀ P, thetaKO om g h (pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) w P) = κ * jetP S T hS hT s (thC (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c Ξ E) P := by
  first | exact @GlobalTheory.KJInf.CoreG.thetaKernel_eq_jet_thC | exact GlobalTheory.KJInf.CoreG.thetaKernel_eq_jet_thC | (intros; apply GlobalTheory.KJInf.CoreG.thetaKernel_eq_jet_thC <;> assumption)
end
