module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JetMapFrameEqApplyQAdaptedCoordinates
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPosRatMultipleOfPosRealMultipleIntForm

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConstantCoeffJetLSubR
open MvPolynomial Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.KFormCore

section Generic

variable {K : Type} [Field K] {σ σ' δ δ' : Type}

def jetL (J : (δ →₀ ℕ) → K) : MvPolynomial (σ ⊕ δ) K →ₗ[K] MvPolynomial σ K :=
  (basisMonomials (σ ⊕ δ) K).constr K fun m =>
    monomial (m.comapDomain Sum.inl Sum.inl_injective.injOn) (J (m.comapDomain Sum.inr Sum.inr_injective.injOn))

theorem jetL_monomial (J : (δ →₀ ℕ) → K) (m : σ ⊕ δ →₀ ℕ) (c : K) :
    jetL J (monomial m c) = monomial (m.comapDomain Sum.inl Sum.inl_injective.injOn)
      (c * J (m.comapDomain Sum.inr Sum.inr_injective.injOn)) := by
  have h1 : (monomial m c : MvPolynomial (σ ⊕ δ) K) = c • basisMonomials (σ ⊕ δ) K m := by
    simp [smul_monomial]
  rw [h1, map_smul, jetL, Module.Basis.constr_basis, smul_monomial, smul_eq_mul]

end Generic

section Main

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem applyAt0_eq (l : ℕ) [Fact l.Prime] (a b : ℕ) (Th : MvPowerSeries (ι × Fin a × Fin b) ℂ_[l])
    (Q : MvPolynomial (KM.XZ ι a b) ℤ) :
    KM.applyAt0 a b l Th Q = jetL (fun m => (m.prod fun _ k => (k.factorial : ℂ_[l])) * MvPowerSeries.coeff m Th)
      (MvPolynomial.map (Int.castRingHom ℂ_[l]) Q) := by
  set_option synthInstance.maxHeartbeats 100000 in
    conv_rhs => rw [Q.as_sum, map_sum, map_sum]
  unfold KM.applyAt0
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [map_monomial, jetL_monomial, mul_assoc]
  rfl

end Main

end GlobalTheory.KFormCore
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelFormComplexPolynomialIdentity
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelFormComplexPolynomialIdentity
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.KerForm

open Classical

theorem frInv_leftInv {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} (O : GL3Theta.LiftObj D C) {i : ℕ}
    (hi : i ≤ D.R.m) (Q : MvPolynomial (GL3Theta.FrV D (D.R.N i)) ℂ) : frInv O i (frPoly O i Q) = Q := by
  have hs : frInv O i ∘ₗ frPoly O i = LinearMap.id :=
    Classical.epsilon_spec (p := fun g => g ∘ₗ frPoly O i = LinearMap.id)
      (LinearMap.exists_leftInverse_of_injective _ (LinearMap.ker_eq_bot.2 (Formalism.L2.Ker.frobenius_poly_injective D u C O i hi)))
  exact LinearMap.congr_fun hs Q

theorem sharp_evC (D : D7) (O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)) (u : D.what₂.Word) (μ : D.what₂.Tup) (i : ℕ) (hi : i < D.R.m)
    (v : ValQ O u μ i) :
    (D.chTw u μ).sharp i (evC O u μ i v) = frPoly (O u μ) i
      (MvPolynomial.map D.what₂.embLL (srcPol u μ i (secC O u μ i v : MvPolynomial (GL3Theta.FrV D (D.R.N i)) D.what₂.LL))) := by
  funext y
  rw [evC_sec]
  show (∏ τ, ((D.chTw u μ).de i y τ) ^ ((D.chTw u μ).sSharp i τ)) * ((∏ τ, ((D.chTw u μ).de i y τ) ^ (-(twB D u μ i τ))) *
    GL3Theta.evFr D (MvPolynomial.map D.what₂.embLL (secC O u μ i v : MvPolynomial (GL3Theta.FrV D (D.R.N i)) D.what₂.LL)) ((O u μ).frm i y)) = _
  show _ = GL3Theta.evFr D _ ((O u μ).frm i y)
  unfold srcPol GL3Theta.evFr
  rw [map_mul, map_mul, map_prod, map_prod, ← mul_assoc, ← Finset.prod_mul_distrib, mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_pow, map_pow, eval_detP, ← (O u μ).frm_de i hi.le y τ, ← zpow_add₀ ((D.chTw u μ).de_ne i y τ), ← zpow_natCast,
    Int.toNat_of_nonneg (sub_nonneg.2 (twLe D u μ i hi τ)), sub_eq_add_neg]

theorem complex_kform : ∀ (D : D7) (O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)) (u : D.what₂.Word) (μ : D.what₂.Tup) (i : ℕ) (hi : i < D.R.m)
    (hU : UnfIsAll (O u μ) i) (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)) (v : ValQ O u μ i) (v' : ValQ O u μ (i + 1))
    (h : evC O u μ (i + 1) v' = (D.chTw u μ).Kmap i c c' (evC O u μ i v)), MvPolynomial.map D.what₂.embLL (secC O u μ (i + 1) v' : MvPolynomial (GL3Theta.FrV D (D.R.N (i + 1))) D.what₂.LL) =
      MvPolynomial.C (((GL3Theta.rhoOf D (O u μ).mt i ((O u μ).dt i c) : ℂˣ) : ℂ) * ((GL3Theta.rhoOf' D (O u μ).mt i ((O u μ).dt (i + 1) c') : ℂˣ) : ℂ)) *
        jetMap (jetC (O u μ).dgen ((O u μ).Th i c c')) (fun _ => 0)
          (MvPolynomial.map D.what₂.embLL (srcPol u μ i (secC O u μ i v : MvPolynomial (GL3Theta.FrV D (D.R.N i)) D.what₂.LL))) := by
  intro D O u μ i hi hU c c' v v' h
  set Q := MvPolynomial.map D.what₂.embLL (srcPol u μ i (secC O u μ i v : MvPolynomial (GL3Theta.FrV D (D.R.N i)) D.what₂.LL)) with hQ
  set Q' := MvPolynomial.map D.what₂.embLL (secC O u μ (i + 1) v' : MvPolynomial (GL3Theta.FrV D (D.R.N (i + 1))) D.what₂.LL) with hQ'
  set ρ : ℂ := ((GL3Theta.rhoOf D (O u μ).mt i ((O u μ).dt i c) : ℂˣ) : ℂ) * ((GL3Theta.rhoOf' D (O u μ).mt i ((O u μ).dt (i + 1) c') : ℂˣ) : ℂ) with hρ
  have hunf : (D.chTw u μ).unf i c c' (frPoly (O u μ) i Q) =
      frPoly (O u μ) (i + 1) (jetMap (ι := D.what₂.Tau) (jetC (O u μ).dgen ((O u μ).Th i c c')) (fun _ => 0) Q) := by
    rw [hU c c' Q]
    unfold unfC
    rw [LinearMap.comp_apply, LinearMap.comp_apply, frInv_leftInv (O u μ) hi.le]
  have hrho : (D.chTw u μ).rhoDet i c * (D.chTw u μ).rhoDet' i c' = ρ := by
    rw [((O u μ).c13 i hi).1 c, ((O u μ).c13 i hi).2 c']
  apply Formalism.L2.Ker.frobenius_poly_injective D u (D.chTw u μ) (O u μ) (i + 1) hi
  funext y'
  have h1 := congrFun h y'
  rw [ColumnChain.Kmap, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.comp_apply, sharp_evC D O u μ i hi v, hunf, hrho] at h1
  rw [evC_sec] at h1
  change (∏ τ, ((D.chTw u μ).de (i + 1) y' τ) ^ (-((D.chTw u μ).sDiv i τ))) * GL3Theta.evFr D Q' ((O u μ).frm (i + 1) y') =
    ρ * ((∏ τ, ((D.chTw u μ).de (i + 1) y' τ) ^ ((D.chTw u μ).sDiv i τ))⁻¹ *
      frPoly (O u μ) (i + 1) (jetMap (ι := D.what₂.Tau) (jetC (O u μ).dgen ((O u μ).Th i c c')) (fun _ => 0) Q) y') at h1
  have hne : (∏ τ, ((D.chTw u μ).de (i + 1) y' τ) ^ ((D.chTw u μ).sDiv i τ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _ ((D.chTw u μ).de_ne (i + 1) y' τ)
  have hinv : (∏ τ, ((D.chTw u μ).de (i + 1) y' τ) ^ (-((D.chTw u μ).sDiv i τ))) =
      (∏ τ, ((D.chTw u μ).de (i + 1) y' τ) ^ ((D.chTw u μ).sDiv i τ))⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun τ _ => zpow_neg _ _
  rw [hinv] at h1
  have h2 : GL3Theta.evFr D Q' ((O u μ).frm (i + 1) y') =
      ρ * frPoly (O u μ) (i + 1) (jetMap (ι := D.what₂.Tau) (jetC (O u μ).dgen ((O u μ).Th i c c')) (fun _ => 0) Q) y' := by
    have := inv_ne_zero hne
    apply mul_left_cancel₀ this
    rw [h1]; ring
  show GL3Theta.evFr D Q' ((O u μ).frm (i + 1) y') = GL3Theta.evFr D _ ((O u μ).frm (i + 1) y')
  rw [h2]
  simp [frPoly, GL3Theta.evFr]

end GlobalTheory.Mem.KerForm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelFormComplexPolynomialIdentityStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelForm_complex_polynomial_identity : ∀ (D : D7) (O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)) (u : D.what₂.Word) (μ : D.what₂.Tup) (i : ℕ) (hi : i < D.R.m)
    (hU : UnfIsAll (O u μ) i) (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)) (v : ValQ O u μ i) (v' : ValQ O u μ (i + 1))
    (h : evC O u μ (i + 1) v' = (D.chTw u μ).Kmap i c c' (evC O u μ i v)), MvPolynomial.map D.what₂.embLL (secC O u μ (i + 1) v' : MvPolynomial (GL3Theta.FrV D (D.R.N (i + 1))) D.what₂.LL) =
      MvPolynomial.C (((GL3Theta.rhoOf D (O u μ).mt i ((O u μ).dt i c) : ℂˣ) : ℂ) * ((GL3Theta.rhoOf' D (O u μ).mt i ((O u μ).dt (i + 1) c') : ℂˣ) : ℂ)) *
        jetMap (jetC (O u μ).dgen ((O u μ).Th i c c')) (fun _ => 0)
          (MvPolynomial.map D.what₂.embLL (srcPol u μ i (secC O u μ i v : MvPolynomial (GL3Theta.FrV D (D.R.N i)) D.what₂.LL))) := by
  first | exact @GlobalTheory.Mem.KerForm.complex_kform | exact GlobalTheory.Mem.KerForm.complex_kform | (intros; apply GlobalTheory.Mem.KerForm.complex_kform <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportDegreeEqOfMemWeightPolynomials
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportDegreeEqOfMemWeightPolynomials
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.WtHomog

open MvPolynomial

theorem coeff_aeval_diag {K : Type} [Field K] {σ : Type} (c : σ → K) (Q : MvPolynomial σ K)
    (e : σ →₀ ℕ) :
    AddMonoidAlgebra.coeff (aeval (fun v => C (c v) * X v) Q : MvPolynomial σ K) e
      = (e.prod fun v k => c v ^ k) * AddMonoidAlgebra.coeff Q e := by
  classical
  induction Q using MvPolynomial.induction_on' generalizing e with
  | monomial u a =>
    have h : (aeval (fun v => C (c v) * X v) (monomial u a) : MvPolynomial σ K)
        = monomial u ((u.prod fun v k => c v ^ k) * a) := by
      rw [aeval_monomial]
      simp only [mul_pow, Finsupp.prod_mul, ← map_pow]
      rw [show (u.prod fun v k => (C (c v ^ k) : MvPolynomial σ K))
            = C (u.prod fun v k => c v ^ k) from (map_finsuppProd C _ _).symm]
      rw [show (u.prod fun v k => (X v : MvPolynomial σ K) ^ k) = monomial u 1 from
        (monomial_eq (s := u) (a := (1 : K))).symm ▸ by simp]
      rw [algebraMap_eq, ← mul_assoc, ← C_mul, C_mul_monomial]
      simp [mul_comm]
    rw [h, coeff_monomial, coeff_monomial]
    by_cases hue : u = e
    · subst hue; simp
    · simp [hue]
  | add p q hp hq =>
    rw [map_add (f := _), MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, mul_add]

theorem deg_eq_of_mem_wtPol : ∀ {K : Type} [Field K] [CharZero K] {ι : Type} [Fintype ι] {n : ℕ} (ν : ι → Fin n → ℕ)
    (Q : MvPolynomial (ι × Fin n × Fin n) K) (hQ : Q ∈ WtPol K ν), ∀ e ∈ Q.support, ∀ τ, ∑ α, ∑ s, e (τ, α, s) = ∑ r, ν τ r := by
  intro K _ _ ι _ n ν Q hQ e he τ
  classical
  set c : ι → K := fun σ => if σ = τ then 2 else 1 with hc
  set β : ι → Matrix (Fin n) (Fin n) K := fun σ => c σ • (1 : Matrix (Fin n) (Fin n) K) with hβ
  have hc0 : ∀ σ, c σ ≠ 0 := by
    intro σ; simp only [hc]; split_ifs <;> norm_num
  have hbor : IsBor β := by
    intro σ
    refine ⟨fun r s hsr => ?_, fun r => ?_⟩
    · simp [hβ, Matrix.one_apply, (ne_of_lt hsr).symm]
    · simpa [hβ] using hc0 σ
  have hsub : colSub β = aeval (fun v : ι × Fin n × Fin n => C (c v.1) * X v) := by
    unfold colSub
    congr 1
    funext v
    obtain ⟨σ, α, s⟩ := v
    simp only [hβ, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single s]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  have hw := hQ β hbor
  rw [hsub] at hw
  have hcoef := congrArg (AddMonoidAlgebra.coeff · e) hw
  rw [coeff_aeval_diag, coeff_smul] at hcoef
  have hne : AddMonoidAlgebra.coeff Q e ≠ 0 := mem_support_iff.mp he
  have hL : (e.prod fun v k => c v.1 ^ k) = (2 : K) ^ (∑ α, ∑ s, e (τ, α, s)) := by
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type,
      Finset.prod_eq_single τ]
    · rw [Fintype.prod_prod_type]
      simp only [hc, if_true, Finset.prod_pow_eq_pow_sum]
    · intro σ _ hσ
      simp [hc, hσ]
    · simp
  have hR : (∏ σ, ∏ r, β σ r r ^ ν σ r) = (2 : K) ^ (∑ r, ν τ r) := by
    rw [Finset.prod_eq_single τ]
    · simp [hβ, hc, Finset.prod_pow_eq_pow_sum]
    · intro σ _ hσ
      simp [hβ, hc, hσ]
    · simp
  rw [hL, hR, smul_eq_mul] at hcoef
  have heq := mul_right_cancel₀ hne hcoef
  have h2 : ((2 : ℕ) ^ (∑ α, ∑ s, e (τ, α, s))) = (2 : ℕ) ^ (∑ r, ν τ r) := by
    exact_mod_cast heq
  exact Nat.pow_right_injective (le_refl 2) h2

end GlobalTheory.Mem.WtHomog
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportDegreeEqOfMemWeightPolynomialsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.support_degree_eq_of_mem_weightPolynomials : ∀ {K : Type} [Field K] [CharZero K] {ι : Type} [Fintype ι] {n : ℕ} (ν : ι → Fin n → ℕ)
    (Q : MvPolynomial (ι × Fin n × Fin n) K) (hQ : Q ∈ WtPol K ν), ∀ e ∈ Q.support, ∀ τ, ∑ α, ∑ s, e (τ, α, s) = ∑ r, ν τ r := by
  first | exact @GlobalTheory.Mem.WtHomog.deg_eq_of_mem_wtPol | exact GlobalTheory.Mem.WtHomog.deg_eq_of_mem_wtPol | (intros; apply GlobalTheory.Mem.WtHomog.deg_eq_of_mem_wtPol <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MinorProductPairingDeterminedByCanonicalMap
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MinorProductPairingDeterminedByCanonicalMap
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KForm.WWUnique

theorem aeval_map_nablaX {Lt : Type} [Fintype Lt] [DecidableEq Lt] (l : ℕ) [Fact l.Prime] (N0 N1 : ℕ)
    (nu : Lt → YoungDiagram) (I : KM.ColChoice N1 nu) :
    MvPolynomial.aeval (R := ℂ_[l]) (fun v : Lt × ℕ × Fin N1 => ∑ a : Fin N0,
        (MvPolynomial.X (Sum.inl (v.1, v.2.1, a)) * MvPolynomial.X (Sum.inr (v.1, a, v.2.2)) :
          MvPolynomial (KM.XZ Lt N0 N1) ℂ_[l]))
      (MvPolynomial.map (Int.castRingHom ℂ_[l]) (KM.nablaX N1 nu I)) =
    MvPolynomial.map (Int.castRingHom ℂ_[l]) (KM.Gxz N0 N1 nu I) := by
  simp only [KM.nablaX, KM.Gxz, KM.minorXZ, map_prod]
  refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => ?_
  rw [RingHom.map_det, RingHom.map_det, AlgHom.map_det]
  congr 1
  ext i k
  set_option synthInstance.maxHeartbeats 100000 in
    simp [MvPolynomial.map_X, MvPolynomial.aeval_X, map_sum, map_mul]

theorem ww_unique : ∀ (D : D7) {p : ℕ} [Fact p.Prime] (N0 N1 : ℕ) (hN : N0 ≤ N1) (nu : Bool × HH D → YoungDiagram)
    (hnu : ∀ z, (nu z).colLen 0 ≤ N0) (Th : MvPowerSeries ((Bool × HH D) × Fin N0 × Fin N1) ℂ_[p])
    (ph : Module.Dual ℂ_[p] (MvPolynomial ((Bool × HH D) × ℕ × Fin N0) ℂ_[p]))
    (ph' : Module.Dual ℂ_[p] (MvPolynomial ((Bool × HH D) × ℕ × Fin N1) ℂ_[p]))
    (κ : ℂ_[p]) (Q : MvPolynomial ((Bool × HH D) × Fin N0 × ℕ) ℂ_[p])
    (hQ : ∀ y : Bool × HH D → Fin N0 → ℕ → ℂ_[p], MvPolynomial.eval (fun v => y v.1 v.2.1 v.2.2) Q = ph (GL3Columns.DeX N0 nu y))
    (h : ∀ y' : D.what₂.Tau → Matrix (Fin N1) (Fin N1) ℂ_[p],
      ph' (GL3Columns.DeX N1 nu fun s => GL3Columns.colsOf (y' (tauPl D s))) = κ * GL3Columns.applyQ p N0 N1 Th Q (fun s => GL3Columns.colsOf (y' (tauPl D s))))
    (I : KM.ColChoice N1 nu), ph' (MvPolynomial.map (Int.castRingHom _) (KM.nablaX N1 nu I)) = κ * ph (KM.applyAt0 N0 N1 p Th (KM.Gxz N0 N1 nu I)) := by
  intro D p _ N0 N1 hN nu hnu Th ph ph' κ Q hQ h I
  classical
  haveI : Finite (KM.ColChoice N1 nu) := by
    unfold KM.ColChoice
    infer_instance
  letI : Fintype (KM.ColChoice N1 nu) := Fintype.ofFinite _
  let J : ((Bool × HH D) × Fin N0 × Fin N1 →₀ ℕ) → ℂ_[p] :=
    fun m => (m.prod fun _ k => (k.factorial : ℂ_[p])) * MvPowerSeries.coeff m Th
  let σ : (Bool × HH D) × ℕ × Fin N1 → MvPolynomial (KM.XZ (Bool × HH D) N0 N1) ℂ_[p] :=
    fun v => ∑ a : Fin N0, MvPolynomial.X (Sum.inl (v.1, v.2.1, a)) * MvPolynomial.X (Sum.inr (v.1, a, v.2.2))
  let L : Module.Dual ℂ_[p] (MvPolynomial ((Bool × HH D) × ℕ × Fin N1) ℂ_[p]) :=
    ph ∘ₗ GlobalTheory.KFormCore.jetL J ∘ₗ (MvPolynomial.aeval (R := ℂ_[p]) σ).toLinearMap
  have hL : ∀ J' : KM.ColChoice N1 nu, L (MvPolynomial.map (Int.castRingHom _) (KM.nablaX N1 nu J')) =
      ph (KM.applyAt0 N0 N1 p Th (KM.Gxz N0 N1 nu J')) := by
    intro J'
    simp only [L, LinearMap.comp_apply, AlgHom.toLinearMap_apply, σ]
    rw [aeval_map_nablaX, GlobalTheory.KFormCore.applyAt0_eq]
  have hLD : ∀ y, L (GL3Columns.DeX N1 nu y) = GL3Columns.applyQ p N0 N1 Th Q y := by
    intro y
    set_option synthInstance.maxHeartbeats 100000 in
      rw [GL3Columns.ww_holds D p N0 N1 nu Th ph Q hQ y, GL3Columns.wwCB_holds D ℂ_[p] N1 nu y, finsum_eq_sum_of_fintype,
      finsum_eq_sum_of_fintype, map_sum]
    refine Finset.sum_congr rfl fun J' _ => ?_
    rw [← MvPolynomial.smul_eq_C_mul, map_smul, hL, smul_eq_mul]
  let ψ : Module.Dual ℂ_[p] (MvPolynomial ((Bool × HH D) × ℕ × Fin N1) ℂ_[p]) := ph' - κ • L
  have hψ : ∀ y, ψ (GL3Columns.DeX N1 nu y) = 0 := by
    intro y
    let e := Equiv.ofBijective (tauPl D) (tauPl_bij D)
    let y' : D.what₂.Tau → Matrix (Fin N1) (Fin N1) ℂ_[p] := fun τ => Matrix.of fun a b => y (e.symm τ) a b
    have hy : GL3Columns.DeX N1 nu y = GL3Columns.DeX N1 nu (fun s => GL3Columns.colsOf (y' (tauPl D s))) := by
      unfold GL3Columns.DeX
      refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => ?_
      congr 1
      ext i j
      have hj : (j : ℕ) < N1 :=
        lt_of_lt_of_le j.2 ((YoungDiagram.colLen_anti _ 0 c (Nat.zero_le _)).trans ((hnu s).trans hN))
      have hs : e.symm (tauPl D s) = s := e.symm_apply_apply s
      simp [GL3Columns.colsOf, hj, y', hs]
    rw [hy]
    simp only [ψ, LinearMap.sub_apply, LinearMap.smul_apply, h, hLD, smul_eq_mul, sub_self]
  have h4 := GL3Columns.wwInj_holds D p N1 nu ψ hψ I
  simp only [ψ, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hL] at h4
  exact sub_eq_zero.mp h4

end GlobalTheory.KForm.WWUnique
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MinorProductPairingDeterminedByCanonicalMapStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.minorProductPairing_determined_by_canonicalMap : ∀ (D : D7) {p : ℕ} [Fact p.Prime] (N0 N1 : ℕ) (hN : N0 ≤ N1) (nu : Bool × HH D → YoungDiagram)
    (hnu : ∀ z, (nu z).colLen 0 ≤ N0) (Th : MvPowerSeries ((Bool × HH D) × Fin N0 × Fin N1) ℂ_[p])
    (ph : Module.Dual ℂ_[p] (MvPolynomial ((Bool × HH D) × ℕ × Fin N0) ℂ_[p]))
    (ph' : Module.Dual ℂ_[p] (MvPolynomial ((Bool × HH D) × ℕ × Fin N1) ℂ_[p]))
    (κ : ℂ_[p]) (Q : MvPolynomial ((Bool × HH D) × Fin N0 × ℕ) ℂ_[p])
    (hQ : ∀ y : Bool × HH D → Fin N0 → ℕ → ℂ_[p], MvPolynomial.eval (fun v => y v.1 v.2.1 v.2.2) Q = ph (GL3Columns.DeX N0 nu y))
    (h : ∀ y' : D.what₂.Tau → Matrix (Fin N1) (Fin N1) ℂ_[p],
      ph' (GL3Columns.DeX N1 nu fun s => GL3Columns.colsOf (y' (tauPl D s))) = κ * GL3Columns.applyQ p N0 N1 Th Q (fun s => GL3Columns.colsOf (y' (tauPl D s))))
    (I : KM.ColChoice N1 nu), ph' (MvPolynomial.map (Int.castRingHom _) (KM.nablaX N1 nu I)) = κ * ph (KM.applyAt0 N0 N1 p Th (KM.Gxz N0 N1 nu I)) := by
  first | exact @GlobalTheory.KForm.WWUnique.ww_unique | exact GlobalTheory.KForm.WWUnique.ww_unique | (intros; apply GlobalTheory.KForm.WWUnique.ww_unique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JetMapIdentityTransportComplexToPadic
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JetMapIdentityTransportComplexToPadic
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.JetTransport

open MvPolynomial Finsupp

variable {ι : Type} [Fintype ι] {a b : ℕ}


open Classical in
noncomputable def wD (ι : Type) (a b : ℕ) : ((ι × Fin b × Fin b) ⊕ DVar ι a b) → (ι → ℕ) :=
  Sum.elim 0 fun x => Pi.single x.1 1


open Classical in
noncomputable def wF (ι : Type) (a : ℕ) : (ι × Fin a × Fin a) → (ι → ℕ) := fun v => Pi.single v.1 1

lemma weight_wF (e : (ι × Fin a × Fin a) →₀ ℕ) (τ : ι) :
    weight (wF ι a) e τ = ∑ α, ∑ s, e (τ, α, s) := by
  classical
  rw [weight_apply, Finsupp.sum_fintype _ _ (by intro; simp)]
  simp [wF, Finset.sum_apply, Pi.single_apply, Fintype.sum_prod_type]
  rw [Fintype.sum_eq_single τ (fun x hx => by simp [Ne.symm hx])]
  simp

lemma weight_wD (u : ((ι × Fin b × Fin b) ⊕ DVar ι a b) →₀ ℕ) (τ : ι) :
    weight (wD ι a b) u τ = ∑ β, ∑ α, u (Sum.inr (τ, β, α)) := by
  classical
  rw [weight_apply, Finsupp.sum_fintype _ _ (by intro; simp)]
  simp [wD, Finset.sum_apply, Pi.single_apply, Fintype.sum_prod_type, Fintype.sum_sum_type]
  rw [Fintype.sum_eq_single τ (fun x hx => by simp [Ne.symm hx])]
  simp

lemma jetMap_zero {K : Type} [Field K] (J : (DVar ι a b →₀ ℕ) → K) (P : Formalism.L2.DIV.Pol K ι a) :
    jetMap J (fun _ => 0) P = jetLin J (subD K ι a b P) := by
  simp [jetMap]

lemma jetLin_monomial {K : Type} [Field K] (J : (DVar ι a b →₀ ℕ) → K)
    (u : ((ι × Fin b × Fin b) ⊕ DVar ι a b) →₀ ℕ) (c : K) :
    jetLin J (monomial u c) = monomial (u.comapDomain Sum.inl Sum.inl_injective.injOn)
      (c * J (u.comapDomain Sum.inr Sum.inr_injective.injOn)) := by
  have : (monomial u c : MvPolynomial _ K) = c • basisMonomials _ K u := by
    rw [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
  rw [this]
  unfold jetLin
  rw [LinearMap.map_smul, Module.Basis.constr_basis, smul_monomial, smul_eq_mul]

lemma jetLin_map {K K' : Type} [Field K] [Field K'] (f : K →+* K') (J : (DVar ι a b →₀ ℕ) → K)
    (Q : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K) :
    jetLin (f ∘ J) (map f Q) = map f (jetLin J Q) := by
  induction Q using MvPolynomial.induction_on' with
  | monomial u c => simp [jetLin_monomial, map_monomial]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]

lemma subD_map {K K' : Type} [Field K] [Field K'] (f : K →+* K') (P : Formalism.L2.DIV.Pol K ι a) :
    subD K' ι a b (map f P) = map f (subD K ι a b P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [subD]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    rw [map_mul, map_X, map_mul, hp, map_mul, map_mul]
    congr 1
    simp only [subD, aeval_X]
    split_ifs <;> simp [map_sum]

lemma subD_X_hom {K : Type} [Field K] (v : ι × Fin a × Fin a) :
    IsWeightedHomogeneous (wD ι a b) (subD K ι a b (X v)) (wF ι a v) := by
  simp only [subD, aeval_X]
  split_ifs with h
  · apply IsWeightedHomogeneous.sum
    intro β _
    have := (isWeightedHomogeneous_X K (wD ι a b) (Sum.inl (v.1, β, (⟨v.2.2.1, h⟩ : Fin b)))).mul
      (isWeightedHomogeneous_X K (wD ι a b) (Sum.inr (v.1, β, v.2.1)))
    simpa [wD, wF] using this
  · exact isWeightedHomogeneous_zero _ _ _

lemma subD_hom {K : Type} [Field K] (P : Formalism.L2.DIV.Pol K ι a) (n : ι → ℕ)
    (hP : IsWeightedHomogeneous (wF ι a) P n) :
    IsWeightedHomogeneous (wD ι a b) (subD K ι a b P) n := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [P.as_sum, map_sum]
  apply IsWeightedHomogeneous.sum
  intro e he
  have hw : weight (wF ι a) e = n := hP (MvPolynomial.mem_support_iff.mp he)
  rw [subD, aeval_monomial, algebraMap_eq]
  apply IsWeightedHomogeneous.C_mul
  rw [← hw, weight_apply]
  apply IsWeightedHomogeneous.prod
  intro v _
  simpa only [subD, aeval_X] using (subD_X_hom (b := b) (K := K) v).pow (e v)

lemma jetLin_congr {K : Type} [Field K] (J₁ J₂ : (DVar ι a b →₀ ℕ) → K) (n : ι → ℕ)
    (Q : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K) (hQ : IsWeightedHomogeneous (wD ι a b) Q n)
    (hJ : ∀ m : DVar ι a b →₀ ℕ, (∀ τ, ∑ β, ∑ α, m (τ, β, α) = n τ) → J₁ m = J₂ m) :
    jetLin J₁ Q = jetLin J₂ Q := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Q.as_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [jetLin_monomial, jetLin_monomial, hJ]
  intro τ
  have hw := congrFun (hQ (MvPolynomial.mem_support_iff.mp hu)) τ
  rw [weight_wD] at hw
  simpa [Finsupp.comapDomain_apply] using hw

end GlobalTheory.JetTransport

theorem GlobalTheory.jetMapTransport : ∀ (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {a b : ℕ}
    (J : (DVar D.what₂.Tau a b →₀ ℕ) → ℂ) (J' : (DVar D.what₂.Tau a b →₀ ℕ) → ℂ_[p]) (n : D.what₂.Tau → ℕ) (r : Qbar)
    (A : MvPolynomial (GL3Theta.FrV D b) Qbar) (P : MvPolynomial (GL3Theta.FrV D a) Qbar)
    (hJ : ∀ m : DVar D.what₂.Tau a b →₀ ℕ, (∀ τ, ∑ β, ∑ α, m (τ, β, α) = n τ) → ∃ x : Qbar, (x : ℂ) = J m ∧ lam x = J' m)
    (hP : ∀ e ∈ P.support, ∀ τ, ∑ α, ∑ s, e (τ, α, s) = n τ)
    (h : MvPolynomial.map (algebraMap Qbar ℂ) A = MvPolynomial.C (r : ℂ) * jetMap J (fun _ => 0) (MvPolynomial.map (algebraMap Qbar ℂ) P)), MvPolynomial.map lam A = MvPolynomial.C (lam r) * jetMap J' (fun _ => 0) (MvPolynomial.map lam P) := by
  intro D p _ lam a b J J' n r A P hJ hP h
  classical
  let x : (DVar D.what₂.Tau a b →₀ ℕ) → Qbar := fun m =>
    if hm : ∀ τ, ∑ β, ∑ α, m (τ, β, α) = n τ then (hJ m hm).choose else 0
  have hx1 : ∀ m : DVar D.what₂.Tau a b →₀ ℕ, (∀ τ, ∑ β, ∑ α, m (τ, β, α) = n τ) →
      J m = (algebraMap Qbar ℂ ∘ x) m := by
    intro m hm
    simp only [x, Function.comp_apply, dif_pos hm]
    exact (hJ m hm).choose_spec.1.symm
  have hx2 : ∀ m : DVar D.what₂.Tau a b →₀ ℕ, (∀ τ, ∑ β, ∑ α, m (τ, β, α) = n τ) →
      J' m = (lam ∘ x) m := by
    intro m hm
    simp only [x, Function.comp_apply, dif_pos hm]
    exact (hJ m hm).choose_spec.2.symm
  have hPw : ∀ {K : Type} [Field K] (f : Qbar →+* K),
      MvPolynomial.IsWeightedHomogeneous (GlobalTheory.JetTransport.wF D.what₂.Tau a) (MvPolynomial.map f P) n := by
    intro K _ f d hd
    funext τ
    rw [GlobalTheory.JetTransport.weight_wF]
    refine hP d (MvPolynomial.mem_support_iff.mpr fun h0 => hd ?_) τ
    rw [MvPolynomial.coeff_map, h0, map_zero]
  have key : ∀ {K : Type} [Field K] (f : Qbar →+* K) (JK : (DVar D.what₂.Tau a b →₀ ℕ) → K),
      (∀ m : DVar D.what₂.Tau a b →₀ ℕ, (∀ τ, ∑ β, ∑ α, m (τ, β, α) = n τ) → JK m = (f ∘ x) m) →
      jetMap JK (fun _ => 0) (MvPolynomial.map f P) = MvPolynomial.map f (jetMap x (fun _ => 0) P) := by
    intro K _ f JK hJK
    rw [GlobalTheory.JetTransport.jetMap_zero, GlobalTheory.JetTransport.jetMap_zero, ← GlobalTheory.JetTransport.jetLin_map,
      ← GlobalTheory.JetTransport.subD_map]
    exact GlobalTheory.JetTransport.jetLin_congr _ _ n _ (GlobalTheory.JetTransport.subD_hom _ n (hPw f)) hJK
  have hA : A = MvPolynomial.C r * jetMap x (fun _ => 0) P := by
    apply MvPolynomial.map_injective (algebraMap Qbar ℂ) (algebraMap Qbar ℂ).injective
    rw [h, key (algebraMap Qbar ℂ) J hx1, map_mul, MvPolynomial.map_C]
    rfl
  rw [hA, map_mul, MvPolynomial.map_C, key lam J' hx2]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JetMapIdentityTransportComplexToPadicStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jetMap_identity_transport_complex_to_padic : ∀ (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {a b : ℕ}
    (J : (DVar D.what₂.Tau a b →₀ ℕ) → ℂ) (J' : (DVar D.what₂.Tau a b →₀ ℕ) → ℂ_[p]) (n : D.what₂.Tau → ℕ) (r : Qbar)
    (A : MvPolynomial (GL3Theta.FrV D b) Qbar) (P : MvPolynomial (GL3Theta.FrV D a) Qbar)
    (hJ : ∀ m : DVar D.what₂.Tau a b →₀ ℕ, (∀ τ, ∑ β, ∑ α, m (τ, β, α) = n τ) → ∃ x : Qbar, (x : ℂ) = J m ∧ lam x = J' m)
    (hP : ∀ e ∈ P.support, ∀ τ, ∑ α, ∑ s, e (τ, α, s) = n τ)
    (h : MvPolynomial.map (algebraMap Qbar ℂ) A = MvPolynomial.C (r : ℂ) * jetMap J (fun _ => 0) (MvPolynomial.map (algebraMap Qbar ℂ) P)), MvPolynomial.map lam A = MvPolynomial.C (lam r) * jetMap J' (fun _ => 0) (MvPolynomial.map lam P) := by
  first | exact @GlobalTheory.jetMapTransport | exact GlobalTheory.jetMapTransport | (intros; apply GlobalTheory.jetMapTransport <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelEntriesFormTrueChains
namespace GlobalTheory.KForm.KerJ

open GlobalTheory.KerJ

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR _root_.Formalism.L2.Host
open GlobalTheory.Mem.Chr (finPartI finPartI_eq_self unitIdl)

theorem mtType_of_hecke {D : D7} {C : CharFrame D} (Dt : DtTied D C) (ξ : HChar D.host.E) {n : ℕ} (hn : 0 < n) (hord : ξ.OrderDvd n)
    (mt : ℕ → D.Dt →* ℂˣ) (h : ∀ (j : Fin D.R.m) a, IsFinIdele a → mt (j.1 + 1) (Dt.eDt a) = (C.mu0 j * ξ).1 a) (u : D.what₂.Word) :
    MtType u mt := by
  letI := D.host.cmStar
  have hcm : IsCMField D.host.E := D.host.isCMField_hostE
  intro i hi
  have hun : (C.mu0 ⟨i, hi⟩ * ξ).IsUnitary := fun x => by
    have e : (C.mu0 ⟨i, hi⟩ * ξ).1 x = (C.mu0 ⟨i, hi⟩).1 x * ξ.1 x := rfl
    rw [e, Units.val_mul, norm_mul, (C.isMu0 ⟨i, hi⟩).unitary x, CharModel.isUnitary_of_orderDvd hn hord x, one_mul]
  refine ⟨fun k hk => ?_, ?_⟩
  · obtain ⟨a, ha, rfl⟩ := (Dt.UO_eq k).1 hk
    obtain ⟨m, hm, hu⟩ := GlobalTheory.UnUnitCmp.Val.finUnit_pow _ hun
    refine ⟨m, hm, Units.ext ?_⟩
    rw [← CharModel.eDt_finPart Dt a, h ⟨i, hi⟩ _ (CharModel.isFin_finPart a), Units.val_pow_eq_pow_val]
    exact hu _ (CharModel.isFin_finPart a) ha
  · choose e he using fun τ => (D.hcW u τ).e_int ⟨i, hi⟩
    refine ⟨e, fun τ => (he τ).symm, fun z => ?_⟩
    obtain ⟨k, hk⟩ := GlobalTheory.Mem.Col2.exists_eq_div_conj D.host z
    obtain ⟨m, hm, hinf⟩ := (C.isMu0 ⟨i, hi⟩).inf
    rw [← Dt.rat k z hk, ← CharModel.eDt_finPart Dt, h ⟨i, hi⟩ _ (CharModel.isFin_finPart _),
      show diagUnits D.host.E k = GlobalTheory.Mem.Chr.diagUnits D.host.E k from rfl,
      GlobalTheory.Mem.Chr.DetGroupModel.fin_diag,
      HChar.inf_mul, GlobalTheory.TypeValues.inf_eq_one _ hn hord, mul_one, Units.val_inv_eq_inv_val, hinf k,
      ← Finset.prod_inv_distrib, ← D.eTau.prod_comp]
    refine Finset.prod_congr rfl fun τ _ => ?_
    have hme : m (D.eTau τ) = 2 * -e τ := by
      have h1 := hm (D.eTau τ)
      have h2 : eExp D ⟨i, hi⟩ (D.eTau τ) = e τ := by
        rw [← he τ, D.hcW_e]; simp [eExp]
      simp only [h2] at h1
      exact_mod_cast h1
    have h1 := congrArg (embPsi D.host (D.eTau τ)) hk
    rw [map_mul, GlobalTheory.Mem.Chr.DetGroupModel.emb_conj] at h1
    have h0 : embPsi D.host (D.eTau τ) (k : D.host.E) ≠ 0 := by simp
    show _ = embPsi D.host (D.eTau τ) z.1 ^ e τ
    generalize embPsi D.host (D.eTau τ) (k : D.host.E) = a at *
    generalize embPsi D.host (D.eTau τ) z.1 = b at *
    have hn' : ((‖a‖ : ℝ) : ℂ) ≠ 0 := by simpa using h0
    have h2 : a * star a = ((‖a‖ : ℝ) : ℂ) ^ 2 := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl
    have h3 : (a / ((‖a‖ : ℝ) : ℂ)) ^ (2 : ℤ) = b := by
      rw [zpow_ofNat, div_pow, div_eq_iff (pow_ne_zero _ hn'), ← h2]
      linear_combination (-a) * h1
    rw [hme, zpow_mul, h3, zpow_neg, inv_inv]

end GlobalTheory.KForm.KerJ

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KForm.EntTrue

open Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR _root_.Formalism.L2.Host GlobalTheory.KerJ GlobalTheory.KForm.KerJ

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

theorem powRatAll_true (l : TC.Laws I) (Z : TC.Later B (TC.cols I l)) : GL3Theta.PowRatAll (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) := by
  obtain ⟨idl, h⟩ := GlobalTheory.Mem.NormOneIdeal.pinned_of_finer (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) I.SQ (MulEquiv.refl _)
    (by
      show UOQ B.host I.SQ = _
      ext x
      constructor
      · intro h
        exact ⟨x, h, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact hy)
    (fun z => rfl)
    (fun N L L' t ht => by
      exact (trueDtPackQ_relDet I.SQ I.C N L L').trans ht)
  exact GL3Theta.powRatAll_of _ idl h (GlobalTheory.KernelScalarUnit.normOne_pow _)

theorem mtType_std (hok : ColIn.Ok I) (hp : TC.Pins B X) (l : TC.Laws I) (Z : TC.Later B (TC.cols I l)) {Qp : I.ι → Finset ℕ}
    {O : ∀ u a, GL3Theta.LiftObj (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).chTw u a)} (hO : TC.StdO I l Z Qp O) (u : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.Word) (a : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.Tup) :
    MtType u (O u a).mt := by
  have hDt : ∃ T : DtTied (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) (TC.cf I l Z),
      ∀ a, T.eDt a = (QuotientGroup.mk a : DtQ B.host I.SQ) := by
    refine ⟨GlobalTheory.Mem.Col2.dtIsoRational _ _ I.SQ (MulEquiv.refl _)
      (fun _ => rfl) rfl ?_ (fun _ => rfl), fun _ => rfl⟩
    show UOQ B.host I.SQ = _
    ext x
    constructor
    · intro h
      exact ⟨x, h, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact hy
  obtain ⟨T, hT⟩ := hDt
  have ht : IsOfFinOrder (I.tup a : Chr B.fields.F B.fields.E B.fields.K) :=
    (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (I.tup a).2).1).1).1).2
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.1 ht
  have hk : KDq B.host I.SQ ≤ ((I.xi a).1.comp (finPartI B.host.E)).ker := by
    classical
    obtain ⟨⟨_, hTame, hAt, -⟩, hQ, -⟩ :=
      ReadTwist.isTwist_of_reads B.R B.host B.LL B.embLL I.S (I.tup a) (I.xi a) (hok.xi_reads a)
    refine (KDq_anti B.host (I.Q_subset_SQ a)).trans
      (KDq_le_ker_of_tame _ hTame hAt fun w hw => by_contra fun hr => hw (Or.inr ?_))
    have hfin : (Qprime (I.tup a : Chr B.fields.F B.fields.E B.fields.K)).Finite :=
      ((UnrAe.finite_ramified (I.xi a)).image (·.under (𝓞 B.host.F))).subset fun v hv => by
        obtain ⟨P, e, hP⟩ := (hQ v).1 hv
        exact ⟨P, hP, e⟩
    have hmem : I.sel (w.under (𝓞 B.host.F)) ∈ I.Q a := by
      unfold ColIn.Q QE
      rw [dite_eq_left hfin]
      exact Finset.mem_image_of_mem I.sel (hfin.mem_toFinset.2 ((hQ _).2 ⟨w, rfl, hr⟩))
    have hund : (I.sel (w.under (𝓞 B.host.F))).under (𝓞 B.host.F) = w.under (𝓞 B.host.F) :=
      HeightOneSpectrum.ext (hok.sel_ok _)
    rcases (under_eq_iff B.host _ w).1 hund.symm with e | e
    · exact Or.inl (e ▸ hmem)
    · exact Or.inr ⟨_, hmem, (isConjPl_iff B.host _ _).2 e⟩
  refine mtType_of_hecke T (I.xi a) hn ((hok.xi_reads a).orderDvd hpow) _ (fun j x hx => ?_) u
  have hm : 1 ≤ j.1 + 1 ∧ j.1 + 1 ≤ B.R.m := ⟨by omega, j.2⟩
  have e1 : (O u a).mt (j.1 + 1) = (I.rec7 l Z).muTil (j.1 + 1) * (show (I.rec7 l Z).Dt →* ℂˣ from tildeQ B.host I.SQ (I.xi a)) := by
    rw [hO.mt u a]
    exact if_pos hm
  rw [e1, MonoidHom.mul_apply, T.muTil_eq j x hx, hT x]
  have e2 : (tildeQ B.host I.SQ (I.xi a)) (QuotientGroup.mk x) = (I.xi a).1 x :=
    (tildeQ_mk B.host I.SQ hk x).trans (congrArg _ (finPartI_eq_self hx))
  exact congrArg _ e2

theorem rhoAlg_std (hok : ColIn.Ok I) (hp : TC.Pins B X) (l : TC.Laws I) (Z : TC.Later B (TC.cols I l)) {Qp : I.ι → Finset ℕ}
    {O : ∀ u a, GL3Theta.LiftObj (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).chTw u a)} (hO : TC.StdO I l Z Qp O) (u : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.Word) (a : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.Tup) :
    GL3Columns.RhoAlg (O u a) := by
  have h3 := GlobalTheory.KerJ.RhoThree.rhoThreeOf_of_mtType _ u ((I.rec7 l Z).chTw u a) (O u a).mt (mtType_std I hok hp l Z hO u a)
  have hq := powRatAll_true I l Z
  intro i hi
  refine ⟨fun c => ?_, fun c' => ?_⟩
  · obtain ⟨h, z, hz⟩ := hq ((O u a).dt i c)
    exact ((h3 i hi).1 _ h z hz).1.1
  · obtain ⟨h, z, hz⟩ := hq ((O u a).dt (i + 1) c')
    exact ((h3 i hi).1 _ h z hz).2.1

end GlobalTheory.KForm.EntTrue

noncomputable section

namespace GlobalTheory.KForm

open Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric

def tauE (D : D7) : (Bool × HH D) ≃ D.what₂.Tau := Equiv.ofBijective _ (tauPl_bij D)

theorem deX_cols (D : D7) {k : Type} [CommRing k] (N : ℕ) (nu : Bool × HH D → YoungDiagram) (hnu : ∀ z, (nu z).colLen 0 ≤ N)
    (y : Bool × HH D → Fin N → ℕ → k) :
    GL3Columns.DeX N nu y = GL3Columns.DeX N nu (fun s => GL3Columns.colsOf ((fun τ => Matrix.of fun a (b : Fin N) => y ((tauE D).symm τ) a b) (tauPl D s))) := by
  unfold GL3Columns.DeX
  refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => ?_
  refine congrArg Matrix.det (Matrix.ext fun i j => ?_)
  simp only [Matrix.of_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hj : (j : ℕ) < N := lt_of_lt_of_le j.2 (le_trans ((nu s).colLen_anti 0 c (Nat.zero_le _)) (hnu s))
  have he : (tauE D).symm (tauPl D s) = s := (tauE D).symm_apply_apply s
  simp [GL3Columns.colsOf, hj, he]

theorem lamC_coe {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (x : Qbar) : lamC lam (x : ℂ) = lam x := by
  unfold lamC
  rw [dite_eq_left x.2]

theorem lamC_jetC (D : D7) {N N' p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (cD : D.what₂.Tau → ℂ) (hc : ∀ τ, cD τ ∈ Qbar)
    (G : VC D N N' → ℂ) (m : DVar D.what₂.Tau N N' →₀ ℕ) (hm : jetC cD G m ∈ Qbar) :
    lamC lam (jetC cD G m) = (m.prod fun k n => lamC lam (cD k.1) ^ n) * (m.prod fun _ n => (n.factorial : ℂ_[p])) *
      lamC lam (Formalism.MainNotions.TaylorLogMetric.taylor D G m) := by
  set c' : D.what₂.Tau → Qbar := fun τ => ⟨cD τ, hc τ⟩
  set a : Qbar := m.prod fun k n => c' k.1 ^ n
  set f : Qbar := m.prod fun _ n => (n.factorial : Qbar)
  have ha : (a : ℂ) = m.prod fun k n => cD k.1 ^ n := by
    simp only [a, c', Finsupp.prod]
    rw [show ((∏ k ∈ m.support, (⟨cD k.1, hc k.1⟩ : Qbar) ^ m k : Qbar) : ℂ) = algebraMap Qbar ℂ (∏ k ∈ m.support, (⟨cD k.1, hc k.1⟩ : Qbar) ^ m k) from rfl,
      map_prod]
    rfl
  have hf : (f : ℂ) = m.prod fun _ n => (n.factorial : ℂ) := by
    simp only [f, Finsupp.prod]
    rw [show ((∏ k ∈ m.support, ((m k).factorial : Qbar) : Qbar) : ℂ) = algebraMap Qbar ℂ (∏ k ∈ m.support, ((m k).factorial : Qbar)) from rfl,
      map_prod]
    simp
  have hf0 : (f : ℂ) ≠ 0 := by
    rw [hf, Finsupp.prod]
    exact Finset.prod_ne_zero_iff.2 fun k _ => by exact_mod_cast Nat.factorial_ne_zero (m k)
  have hd : derivAt0 G m = (f : ℂ) * Formalism.MainNotions.TaylorLogMetric.taylor D G m := by
    unfold Formalism.MainNotions.TaylorLogMetric.taylor
    rw [← hf, mul_div_cancel₀ _ hf0]
    rfl
  have hj : jetC cD G m = (a : ℂ) * (f : ℂ) * Formalism.MainNotions.TaylorLogMetric.taylor D G m := by
    unfold jetC
    rw [hd, ha, mul_assoc]
  have hla : (m.prod fun k n => lamC lam (cD k.1) ^ n) = lam a := by
    simp only [a, Finsupp.prod, map_prod, map_pow]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← lamC_coe]
  have hlf : (m.prod fun _ n => (n.factorial : ℂ_[p])) = lam f := by
    simp only [f, Finsupp.prod, map_prod, map_natCast]
  rw [hla, hlf]
  by_cases ha0 : a = 0
  · have : jetC cD G m = ((0 : Qbar) : ℂ) := by rw [hj, ha0]; simp
    rw [this, lamC_coe, ha0]
    simp
  · have ha0' : (a : ℂ) ≠ 0 := fun h => ha0 (Subtype.ext h)
    have ht : Formalism.MainNotions.TaylorLogMetric.taylor D G m ∈ Qbar := by
      have : Formalism.MainNotions.TaylorLogMetric.taylor D G m = jetC cD G m / ((a : ℂ) * (f : ℂ)) := by
        rw [hj]; field_simp
      rw [this]
      exact div_mem hm (mul_mem a.2 f.2)
    have e : jetC cD G m = ((a * f * ⟨_, ht⟩ : Qbar) : ℂ) := hj
    rw [e, lamC_coe, map_mul, map_mul, show lamC lam (Formalism.MainNotions.TaylorLogMetric.taylor D G m) = lam ⟨_, ht⟩ from lamC_coe lam ⟨_, ht⟩]

theorem applyQ_C_mul {Lt : Type} (l : ℕ) [Fact l.Prime] (N0 N1 : ℕ) (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l])
    (d : ℂ_[l]) (hd : d ≠ 0) (Q : MvPolynomial (Lt × Fin N0 × ℕ) ℂ_[l]) (y' : Lt → Fin N1 → ℕ → ℂ_[l]) :
    GL3Columns.applyQ l N0 N1 Th (MvPolynomial.C d * Q) y' = d * GL3Columns.applyQ l N0 N1 Th Q y' := by
  unfold GL3Columns.applyQ
  simp only [map_mul, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
  rw [← MvPolynomial.smul_eq_C_mul, MvPolynomial.support_smul_eq hd, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  ring

theorem eval_aeval' {σ τ R : Type} [CommRing R] (f : τ → R) (g : σ → MvPolynomial τ R) (P : MvPolynomial σ R) :
    MvPolynomial.eval f (MvPolynomial.aeval g P) = MvPolynomial.eval (fun k => MvPolynomial.eval f (g k)) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p k hp => simp only [map_mul, hp, MvPolynomial.aeval_X, MvPolynomial.eval_X]

theorem qbar_of_numberField (M : IntermediateField ℚ ℂ) [NumberField M] (s : M) : (s : ℂ) ∈ Qbar :=
  mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) s).algHom M.val)

end GlobalTheory.KForm


open GlobalTheory.KForm.EntTrue Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.G in
theorem GlobalTheory.Mem.Col2.TC.kerEnt_kform_true : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), ColIn.Ok I → TC.Pins B X → ∀ (l : TC.Laws I) (Z : TC.Later B (TC.cols I l)), ∀ (l0 : TC.Law0 I l) (Y : DivX (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)) (O : ∀ u a, GL3Theta.LiftObj (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).chTw u a)) (Pl : Examples₂.EntPl (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)) (Bs : PlaceMatrixFamily (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)), TC.QpIs I Y.Qp → TC.StdO I l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → ColIn.JetsIn I → ∀ u μ w, LevFree Y u μ w → ∀ i, i < (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.m → ∀ (c : ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).chTw u μ).cls i) (c' : ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).chTw u μ).cls (i + 1)) (v : ValQ O u μ i) (v' : ValQ O u μ (i + 1)), evC O u μ (i + 1) v' = ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).chTw u μ).Kmap i c c' (evC O u μ i v) → ∀ J, prTC Pl O Bs u μ w i c' v' J = unC Pl O Bs u μ w i c c' * prSC Pl O Bs u μ w i c v (KM.applyAt0 ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.N i) ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.N (i + 1)) ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.places.resChar w) (thAtW Pl O Bs u μ w i c c') (KM.Gxz ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.N i) ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.N (i + 1)) (nuD (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u i) J)) := by
  intro B X I hok hp l Z l0 Y O Pl Bs hq hs hB hent hU hJ u μ w hw i hi c c' v v' hK J
  have hR := GlobalTheory.KForm.EntTrue.rhoAlg_std I hok hp l Z hs u μ
  have hCo := GlobalTheory.T.toy_entPl_canOnto (I.rec7 l Z) Pl
  have hS := canS_of Pl Bs hCo
  have hT := canT_of Pl Bs hCo
  have hdg : ∀ τ, (O u μ).dgen τ ∈ Qbar := by
    obtain ⟨M, hM, -, hs'⟩ := (O u μ).dgen_gen
    intro τ
    obtain ⟨s, hs1, -⟩ := hs' τ
    rw [← hs1]
    exact GlobalTheory.KForm.qbar_of_numberField M s
  have hdet : ∀ τ, (Bs u μ w i c τ).det ≠ 0 := fun τ => (hB u μ w i hi.le c τ).1
  change tgtPh Pl O Bs u μ w i c' v' (MvPolynomial.map (Int.castRingHom _) (KM.nablaX _ (nuD (I.rec7 l Z) u i) J)) = _
  refine GlobalTheory.T.minorProductPairing_determined_by_canonicalMap (I.rec7 l Z) _ _ (N_le_succ _ i) (nuD (I.rec7 l Z) u i) (fun z => nuD_rows _ u i z)
    (thAtW Pl O Bs u μ w i c c') (prSC Pl O Bs u μ w i c v) (tgtPh Pl O Bs u μ w i c' v') (unC Pl O Bs u μ w i c c')
    (MvPolynomial.C (∏ τ, (Bs u μ w i c τ).det ^ (-((I.rec7 l Z).chTw u μ).sSharp i τ)) *
      MvPolynomial.aeval (fun k : GL3Theta.FrV (I.rec7 l Z) ((I.rec7 l Z).R.N i) => ∑ a : Fin ((I.rec7 l Z).R.N i),
          MvPolynomial.C (Bs u μ w i c k.1 k.2.1 a) * MvPolynomial.X ((GlobalTheory.KForm.tauE _).symm k.1, a, (k.2.2 : ℕ)))
        (MvPolynomial.map (Pl.iL w) (srcPol u μ i (secC O u μ i v : MvPolynomial (GL3Theta.FrV (I.rec7 l Z) ((I.rec7 l Z).R.N i)) (I.rec7 l Z).what₂.LL))))
    ?_ ?_ J
  · intro y
    rw [GlobalTheory.KForm.deX_cols (I.rec7 l Z) _ (nuD (I.rec7 l Z) u i) (fun z => nuD_rows _ u i z) y]
    have h1 := congrFun (canInv_spec (I.rec7 l Z) w _ (nuD (I.rec7 l Z) u i) _ (hS u μ w i hi c (secC O u μ i v)))
      (fun τ => Matrix.of fun a (b : Fin ((I.rec7 l Z).R.N i)) => y ((GlobalTheory.KForm.tauE _).symm τ) a b)
    refine Eq.trans ?_ h1.symm
    rw [map_mul, MvPolynomial.eval_C, GlobalTheory.KForm.eval_aeval']
    show _ = (∏ τ, (Bs u μ w i c τ).det ^ (-((I.rec7 l Z).chTw u μ).sSharp i τ)) *
      MvPolynomial.eval (fun k : GL3Theta.FrV (I.rec7 l Z) ((I.rec7 l Z).R.N i) =>
          (Bs u μ w i c k.1 * (fun τ => Matrix.of fun a (b : Fin ((I.rec7 l Z).R.N i)) => y ((GlobalTheory.KForm.tauE _).symm τ) a b) k.1) k.2.1 k.2.2)
        (MvPolynomial.map (Pl.iL w) (srcPol u μ i (secC O u μ i v : MvPolynomial (GL3Theta.FrV (I.rec7 l Z) ((I.rec7 l Z).R.N i)) (I.rec7 l Z).what₂.LL)))
    congr 2
    exact congrArg MvPolynomial.eval (funext fun k => by simp [Matrix.mul_apply, MvPolynomial.eval_X])
  · intro y'
    have h1 := congrFun (canInv_spec (I.rec7 l Z) w _ (nuD (I.rec7 l Z) u i) _ (hT u μ w i hi c' (secC O u μ (i + 1) v'))) y'
    refine h1.trans ?_
    have hmap : ∀ {N : ℕ} (Q : MvPolynomial (GL3Theta.FrV (I.rec7 l Z) N) (I.rec7 l Z).what₂.LL),
        MvPolynomial.map (Pl.iL w) Q = MvPolynomial.map (Pl.lam w) (MvPolynomial.map (jL w) Q) := by
      intro N Q
      rw [MvPolynomial.map_map, lam_jL]
    have hρ : ((GL3Theta.rhoOf (I.rec7 l Z) (O u μ).mt i ((O u μ).dt i c) : ℂˣ) : ℂ) *
        ((GL3Theta.rhoOf' (I.rec7 l Z) (O u μ).mt i ((O u μ).dt (i + 1) c') : ℂˣ) : ℂ) ∈ Qbar :=
      mul_mem ((hR i hi).1 c) ((hR i hi).2 c')
    have htr := GlobalTheory.T.jetMap_identity_transport_complex_to_padic (I.rec7 l Z) (Pl.lam w) (jetC (O u μ).dgen ((O u μ).Th i c c'))
      (fun m => (m.prod fun k n => lamC (Pl.lam w) ((O u μ).dgen k.1) ^ n) * (m.prod fun _ n => (n.factorial : ℂ_[(I.rec7 l Z).what₂.places.resChar w])) *
        MvPowerSeries.coeff m (pSer (I.rec7 l Z) (Pl.lam w) ((O u μ).Th i c c')))
      (fun τ => ∑ r, nuT (I.rec7 l Z) u i τ r) ⟨_, hρ⟩
      (MvPolynomial.map (jL w) (secC O u μ (i + 1) v' : MvPolynomial (GL3Theta.FrV (I.rec7 l Z) ((I.rec7 l Z).R.N (i + 1))) (I.rec7 l Z).what₂.LL))
      (MvPolynomial.map (jL w) (srcPol u μ i (secC O u μ i v : MvPolynomial (GL3Theta.FrV (I.rec7 l Z) ((I.rec7 l Z).R.N i)) (I.rec7 l Z).what₂.LL)))
      (fun m hm => ⟨⟨_, GlobalTheory.T.trueKernelJets_liftDegrees_algebraic I hok hp l Z Y.Qp O hs hJ u μ i hi c c' m hm⟩, rfl,
        (GlobalTheory.KForm.lamC_coe _ _).symm.trans
          (GlobalTheory.KForm.lamC_jetC (I.rec7 l Z) (Pl.lam w) _ hdg _ m (GlobalTheory.T.trueKernelJets_liftDegrees_algebraic I hok hp l Z Y.Qp O hs hJ u μ i hi c c' m hm))⟩)
      (fun e he τ => GlobalTheory.T.support_degree_eq_of_mem_weightPolynomials (nuT (I.rec7 l Z) u i) _ (srcPol_mem u μ i hi _) e (MvPolynomial.support_map_subset _ _ he) τ)
      (by
        rw [MvPolynomial.map_map, MvPolynomial.map_map, alg_jL]
        exact GlobalTheory.T.kernelForm_complex_polynomial_identity (I.rec7 l Z) O u μ i hi (hU u μ i hi) c c' v v' hK)
    have hd0 : (∏ τ, (Bs u μ w i c τ).det ^ (-((I.rec7 l Z).chTw u μ).sSharp i τ)) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _ (hdet τ)
    show (∏ τ, (Bs u μ w (i + 1) c' τ).det ^ (-((I.rec7 l Z).chTw u μ).sDiv i τ)) *
      MvPolynomial.eval (fun k : GL3Theta.FrV (I.rec7 l Z) ((I.rec7 l Z).R.N (i + 1)) => (Bs u μ w (i + 1) c' k.1 * y' k.1) k.2.1 k.2.2)
        (MvPolynomial.map (Pl.iL w) (secC O u μ (i + 1) v' : MvPolynomial (GL3Theta.FrV (I.rec7 l Z) ((I.rec7 l Z).R.N (i + 1))) (I.rec7 l Z).what₂.LL)) = _
    rw [hmap, htr, map_mul, MvPolynomial.eval_C, ← hmap,
      GlobalTheory.T.jetMap_frame_eq_applyQ_adapted_coordinates (I.rec7 l Z) _ _ (N_le_succ _ i) (pSer (I.rec7 l Z) (Pl.lam w) ((O u μ).Th i c c'))
        (fun τ => lamC (Pl.lam w) ((O u μ).dgen τ)) (Bs u μ w i c) (Bs u μ w (i + 1) c') hdet, GlobalTheory.KForm.applyQ_C_mul _ _ _ _ _ hd0]
    have hl : (Pl.lam w) ⟨_, hρ⟩ = lamC (Pl.lam w) ((GL3Theta.rhoOf (I.rec7 l Z) (O u μ).mt i ((O u μ).dt i c) : ℂˣ) : ℂ) *
        lamC (Pl.lam w) ((GL3Theta.rhoOf' (I.rec7 l Z) (O u μ).mt i ((O u μ).dt (i + 1) c') : ℂˣ) : ℂ) := by
      rw [show (⟨_, hρ⟩ : Qbar) = ⟨_, (hR i hi).1 c⟩ * ⟨_, (hR i hi).2 c'⟩ from rfl, map_mul, ← GlobalTheory.KForm.lamC_coe, ← GlobalTheory.KForm.lamC_coe]
    have hp : (∏ τ, (Bs u μ w i c τ).det ^ (((I.rec7 l Z).chTw u μ).sSharp i τ)) *
        (∏ τ, (Bs u μ w i c τ).det ^ (-((I.rec7 l Z).chTw u μ).sSharp i τ)) = 1 := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one fun τ _ => by rw [← zpow_add₀ (hdet τ), add_neg_cancel, zpow_zero]
    have hun : unC Pl O Bs u μ w i c c' = unF Pl O Bs u μ w i c c' := by
      unfold unC
      rw [if_neg (unF_ne Pl O Bs hB u μ hR w i hi c c')]
    have key : ∀ A : ℂ_[(I.rec7 l Z).what₂.places.resChar w],
        (∏ τ, (Bs u μ w (i + 1) c' τ).det ^ (-((I.rec7 l Z).chTw u μ).sDiv i τ)) * ((Pl.lam w) ⟨_, hρ⟩ * A) =
          unC Pl O Bs u μ w i c c' * ((∏ τ, (Bs u μ w i c τ).det ^ (-((I.rec7 l Z).chTw u μ).sSharp i τ)) * A) := by
      intro A
      rw [hun, hl]
      unfold unF
      linear_combination (-(lamC (Pl.lam w) ((GL3Theta.rhoOf (I.rec7 l Z) (O u μ).mt i ((O u μ).dt i c) : ℂˣ) : ℂ) *
        lamC (Pl.lam w) ((GL3Theta.rhoOf' (I.rec7 l Z) (O u μ).mt i ((O u μ).dt (i + 1) c') : ℂˣ) : ℂ) *
        (∏ τ, (Bs u μ w (i + 1) c' τ).det ^ (-((I.rec7 l Z).chTw u μ).sDiv i τ)) * A)) * hp
    exact key _
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelEntriesFormTrueChainsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelEntries_form_true_chains : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → ColIn.JetsIn I → ∀ u μ w, LevFree Y u μ w → ∀ i, i < (I.rec7 l Z).R.m → ∀ (c : ((I.rec7 l Z).chTw u μ).cls i) (c' : ((I.rec7 l Z).chTw u μ).cls (i + 1)) (v : ValQ O u μ i) (v' : ValQ O u μ (i + 1)), evC O u μ (i + 1) v' = ((I.rec7 l Z).chTw u μ).Kmap i c c' (evC O u μ i v) → ∀ J, prTC Pl O Bs u μ w i c' v' J = unC Pl O Bs u μ w i c c' * prSC Pl O Bs u μ w i c v (KM.applyAt0 ((I.rec7 l Z).R.N i) ((I.rec7 l Z).R.N (i + 1)) ((I.rec7 l Z).what₂.places.resChar w) (thAtW Pl O Bs u μ w i c c') (KM.Gxz ((I.rec7 l Z).R.N i) ((I.rec7 l Z).R.N (i + 1)) (nuD (I.rec7 l Z) u i) J)) := by
  first | exact @GlobalTheory.Mem.Col2.TC.kerEnt_kform_true | exact GlobalTheory.Mem.Col2.TC.kerEnt_kform_true | (intros; apply GlobalTheory.Mem.Col2.TC.kerEnt_kform_true <;> assumption)
end
