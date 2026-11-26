module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MaxVSpanSingleton
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsNormalFormLattice
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentRadicalsActAffineUnfoldingSpaces
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TensorMapDescent

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalCharacterNeZeroOfNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalCharacterNeZeroOfNeZero
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

namespace GlobalTheory.Proof.localCharacter_ne_zero_of_ne_zero

variable {E : Type} [Field E] [NumberField E]

theorem isUnit_reduction_of_valuation_eq_one (P : HeightOneSpectrum (𝓞 E)) {b : E} (hb : P.valuation E b = 1) :
    IsUnit (redP P b) := by
  have hb0 : b ≠ 0 := by
    rintro rfl
    simp at hb
  have h1 : IntAt P b := (IntegralPowerExpansion.intAt_iff_val P b).2 hb.le
  have h2 : IntAt P b⁻¹ := (IntegralPowerExpansion.intAt_iff_val P _).2 (by rw [map_inv₀, hb, inv_one])
  have h3 := reduction_mul h1 h2
  have h4 : redP P (1 : E) = 1 := by simpa using reduction_coe P 1
  rw [mul_inv_cancel₀ hb0, h4] at h3
  exact IsUnit.of_mul_eq_one _ h3.symm

theorem exists_isUnit_reduction_div_pow {P : HeightOneSpectrum (𝓞 E)} (hP : GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P) {a : E} (ha : a ≠ 0) :
    ∃ z : ℤ, IsUnit (redP P (a / (qOf P : E) ^ z)) := by
  have hv : P.valuation E a ≠ 0 := (Valuation.ne_zero_iff _).2 ha
  refine ⟨-WithZero.log (P.valuation E a), isUnit_reduction_of_valuation_eq_one P ?_⟩
  rw [map_div₀, map_zpow₀, IntegralPowerExpansion.val_q hP, ← WithZero.exp_zsmul]
  simp only [smul_neg, neg_smul, neg_neg, smul_eq_mul, mul_one, mul_neg, neg_mul]
  rw [WithZero.exp_log hv, div_self hv]

theorem locChar_ne_zero : ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] (P : HeightOneSpectrum (𝓞 E)),
    GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P → ∀ (cq : K) (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (a : E), cq ≠ 0 → a ≠ 0 →
      LocE.locChar (qOf P) cq χ a ≠ 0 := by
  intro E _ _ K _ P hP cq χ a hcq ha
  have h : IsUnit (redP P (a / (qOf P : E) ^ LocE.vP P (qOf P) a)) :=
    Classical.epsilon_spec (exists_isUnit_reduction_div_pow hP ha)
  unfold LocE.locChar LocE.unitV
  rw [dite_eq_left h]
  exact mul_ne_zero (zpow_ne_zero _ hcq) (Units.ne_zero _)

end GlobalTheory.Proof.localCharacter_ne_zero_of_ne_zero
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalCharacterNeZeroOfNeZeroStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localCharacter_ne_zero_of_ne_zero : ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] (P : HeightOneSpectrum (𝓞 E)), GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P → ∀ (cq : K) (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (a : E), cq ≠ 0 → a ≠ 0 → LocE.locChar (qOf P) cq χ a ≠ 0 := by
  first | exact @GlobalTheory.Proof.localCharacter_ne_zero_of_ne_zero.locChar_ne_zero | exact GlobalTheory.Proof.localCharacter_ne_zero_of_ne_zero.locChar_ne_zero | (intros; apply GlobalTheory.Proof.localCharacter_ne_zero_of_ne_zero.locChar_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SumCosetRepsNeZeroIffCommensurableStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_coset_reps_ne_zero_iff_commensurable : ∀ (V K : Type) [AddCommGroup V] [Field K] [CharZero K] (f : V → K) (N N' : AddSubgroup V) (S S' : Finset V), N'.relIndex N ≠ 0 → N.relIndex N' ≠ 0 → (∀ v, ∀ u ∈ N, f (v + u) = f v) → (∀ v, ∀ u ∈ N', f (v + u) = f v) → (∀ s ∈ S, ∀ s' ∈ S, s - s' ∈ N → s = s') → (∀ v, f v ≠ 0 → ∃ s ∈ S, v - s ∈ N) → (∀ s ∈ S', ∀ s' ∈ S', s - s' ∈ N' → s = s') → (∀ v, f v ≠ 0 → ∃ s ∈ S', v - s ∈ N') → (∑ s ∈ S, f s ≠ 0 ↔ ∑ s ∈ S', f s ≠ 0) := by
  first | exact @GlobalTheory.Proof.sum_coset_reps_ne_zero_iff_commensurable.sum_reps_ne_zero_iff | exact GlobalTheory.Proof.sum_coset_reps_ne_zero_iff_commensurable.sum_reps_ne_zero_iff | (intros; apply GlobalTheory.Proof.sum_coset_reps_ne_zero_iff_commensurable.sum_reps_ne_zero_iff <;> assumption)
end

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.QNormal

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

section General

variable {E : Type} [Field E] [NumberField E] {K : Type} [Field K] {P : HeightOneSpectrum (𝓞 E)}

theorem IntHom.comp {a b c : ℕ} {x : (Fin b → E) →ₗ[E] (Fin c → E)} {y : (Fin a → E) →ₗ[E] (Fin b → E)}
    (hx : IntHom P x) (hy : IntHom P y) : IntHom P (x ∘ₗ y) := fun v hv => hx _ (hy v hv)

theorem IntHom.pow_mono {a b : ℕ} {x : (Fin a → E) →ₗ[E] (Fin b → E)} {N N' : ℕ} (h : N ≤ N')
    (hx : IntHom P (((qOf P : E) ^ N) • x)) : IntHom P (((qOf P : E) ^ N') • x) :=
  fun v hv l => Proof.NormalFormAtPrime.intAt_pow_mono h (hx v hv l)

theorem intV_eN (P : HeightOneSpectrum (𝓞 E)) (N i : ℕ) : IntV P (Loc.eN E N i) := by
  intro l
  unfold Loc.eN
  split_ifs
  · exact intAt_one P
  · exact IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P

theorem intAt_chArg {n' c' n c : ℕ} {x : (Fin (n' + c') → E) →ₗ[E] (Fin (n + c) → E)} {u : E} (hx : IntHom P (u • x)) :
    IntAt P (u * Loc.chArg x) := by
  unfold Loc.chArg
  rw [Finset.mul_sum]
  refine intAt_sum _ _ fun i _ => ?_
  unfold Loc.atN
  split_ifs with h
  · exact hx _ (intV_eN P _ _) _
  · simpa using IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P

theorem unfNe_transfer [CharZero K] (hP : IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P) {n' c' n c : ℕ} (hc : 1 ≤ c) (hc' : c' = c + 1)
    {psi : E → K} {D N : ℕ} (hN : N ≤ D) (hpsi : CharTo P D psi) {Psi Psi' : Loc.SF E K (n' + c') (n + c)}
    (h1 : HomBdd P N Psi) (h2 : HomBdd P N Psi') {C : K} (hC : C ≠ 0)
    {r : (Fin (n + c) → E) ≃ₗ[E] (Fin (n + c) → E)} {r' : (Fin (n' + c') → E) ≃ₗ[E] (Fin (n' + c') → E)}
    (hr : r ∈ Loc.R1 E n c) (hr' : r' ∈ Loc.R1 E n' c')
    (hrel : ∀ x, Psi' x = C * Psi (r.toLinearMap ∘ₗ x ∘ₗ r'.toLinearMap)) (H : UnfNe P psi Psi) : UnfNe P psi Psi' := by
  obtain ⟨A₀, B₀, H⟩ := H
  obtain ⟨xj', hx⟩ := Function.ne_iff.1 (H (max A₀ N) (max B₀ N) (le_max_left _ _) (le_max_left _ _))
  obtain ⟨xj, T, b, hT⟩ := GlobalTheory.T.unipotentRadicals_act_affine_unfoldingSpaces GlobalTheory.T.exists_xx1_eq_iff_inX_eN_Ufl_conditions E n' c' n c hc hc' r hr r' hr' xj'
  obtain ⟨d, hd⟩ := GlobalTheory.T.unfoldingCharacterArgument_comp_unipotentRadicals GlobalTheory.T.exists_xx1_eq_iff_inX_eN_Ufl_conditions E n' c' n c hc hc' r hr r' hr'
  have I1 := GlobalTheory.T.localUnfoldingIntegrand_boundedSchwartz E K P n' c' n c psi D N Psi hN hpsi h1 xj'
  have I2 := GlobalTheory.T.localUnfoldingIntegrand_boundedSchwartz E K P n' c' n c psi D N Psi' hN hpsi h2 xj
  obtain ⟨A₁, B₁, hA⟩ := GlobalTheory.T.boxSum_ne_zero_invariant_affineChange GlobalTheory.T.vectors_linearMaps_bounded_denominators_atPrime GlobalTheory.T.sum_coset_reps_ne_zero_iff_commensurable GlobalTheory.T.rationalFractions_represent_primeNormQuotient E K P hP _ (integrand psi Psi xj') N I1.1 T b
  refine ⟨max A₁ N, max B₁ N, fun A B hA' hB' => Function.ne_iff.2 ⟨xj, ?_⟩⟩
  have h3 : boxSum P A B (integrand psi Psi xj') ≠ 0 := by
    rw [GlobalTheory.T.weightedBoxSumAtPrime_eq_of_boundedSchwartz E K P hP.1 _ _ N I1.1 A B (le_of_max_le_right hA') (le_of_max_le_right hB'),
      ← GlobalTheory.T.weightedBoxSumAtPrime_eq_of_boundedSchwartz E K P hP.1 _ _ N I1.1 (max A₀ N) (max B₀ N) (le_max_right _ _) (le_max_right _ _)]
    exact hx
  have h4 := (hA A B (le_of_max_le_left hA') (le_of_max_le_left hB')).2 h3
  have hdep : ∀ t, Psi (Loc.xx1 xj' (T t + b)) ≠ 0 → IntAt P ((qOf P : E) ^ D * d) ∧
      IntAt P ((qOf P : E) ^ D * -Loc.chArg (Loc.xx1 xj' (T t + b))) := by
    intro t ht
    have a1 := Proof.NormalFormAtPrime.intAt_pow_mono hN (I1.2 _ ht)
    have a2 := Proof.NormalFormAtPrime.intAt_pow_mono hN (I2.2 t (by rw [hrel, hT]; exact mul_ne_zero hC ht))
    refine ⟨?_, by simpa using IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_neg a1⟩
    have := a1.add (IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_neg a2)
    rw [← hT, hd] at this
    convert this using 1
    ring
  have hpt : ∀ t, integrand psi Psi' xj t = C * psi d * integrand psi Psi xj' (T t + b) := by
    intro t
    unfold integrand
    rw [hrel, hT]
    by_cases ht : Psi (Loc.xx1 xj' (T t + b)) = 0
    · simp [ht]
    · have e : -Loc.chArg (Loc.xx1 xj t) = d + -Loc.chArg (Loc.xx1 xj' (T t + b)) := by
        rw [← hT, hd]
        ring
      rw [e, hpsi.1 _ _ (hdep t ht).1 (hdep t ht).2]
      ring
  have hd0 : psi d ≠ 0 := by
    obtain ⟨t, -, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero (right_ne_zero_of_mul h4)
    have a := (hdep t (left_ne_zero_of_mul ht)).1
    have := hpsi.1 d (-d) a (by simpa using IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_neg a)
    rw [add_neg_cancel, hpsi.2 0 (IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P)] at this
    exact left_ne_zero_of_mul (this ▸ one_ne_zero)
  change boxSum P A B (integrand psi Psi' xj) ≠ 0
  have e : boxSum P A B (integrand psi Psi' xj) =
      C * psi d * boxSum P A B (fun t => integrand psi Psi xj' (T t + b)) := by
    unfold boxSum
    simp only [hpt, ← Finset.mul_sum]
    ring
  rw [e]
  exact mul_ne_zero (mul_ne_zero hC hd0) h4

theorem homBdd_translate {a b i : ℕ} {Φ Psi : Loc.SF E K a b} {C : K} {g : (Fin a → E) ≃ₗ[E] (Fin a → E)}
    {h : (Fin b → E) ≃ₗ[E] (Fin b → E)} (hΦ : ∀ x, Φ x ≠ 0 → IntHom P x)
    (hΦ' : ∀ x y, IntHom P y → Φ (x + (qOf P : E) • y) = Φ x)
    (g1 : IntHom P g.symm.toLinearMap) (g2 : IntHom P (((qOf P : E) ^ i) • g.toLinearMap))
    (h1 : IntHom P h.symm.toLinearMap) (h2 : IntHom P (((qOf P : E) ^ (i + 1)) • h.toLinearMap))
    (e : ∀ x, Psi x = C * Φ (h.symm.toLinearMap ∘ₗ x ∘ₗ g.toLinearMap)) : HomBdd P (i + 1) Psi := by
  refine ⟨fun x hx v hv => ?_, fun x y hy => ?_⟩
  · rw [e] at hx
    have := h2 _ (hΦ _ (right_ne_zero_of_mul hx) _ (g1 v hv))
    simpa using this
  · rw [e, e, ← hΦ' (h.symm.toLinearMap ∘ₗ x ∘ₗ g.toLinearMap) _ (h1.comp (hy.comp g2))]
    congr 2
    refine LinearMap.ext fun v => ?_
    simp [pow_succ', mul_smul]

end General

section Chain

open IndefiniteRowSideFullHecke.SandwichNormalForm

variable {X : Fields} {Pr : Primes X} {R : Ranks}

def Between (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) (h : AutY X R j) : Prop :=
  IntHom P h.symm.toLinearMap ∧ IntHom P (((qOf P : X.E) ^ j) • h.toLinearMap)

theorem between_iff {j : ℕ} {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∉ Pr.vGs) (h : AutY X R j) :
    (∀ x ∈ lamYat (Pr := Pr) (R := R) j P, h⁻¹ x ∈ lamYat (Pr := Pr) (R := R) j P ∧
      ((qOf P : X.E) ^ j) • h x ∈ lamYat (Pr := Pr) (R := R) j P) ↔ Between j P h := by
  simp only [mem_lamYat hP]
  exact ⟨fun H => ⟨fun v hv => (H v hv).1, fun v hv => (H v hv).2⟩, fun H v hv => ⟨H.1 v hv, H.2 v hv⟩⟩

theorem between_of_nf {j : ℕ} {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∉ Pr.vGs) {h : AutY X R j} (H : NF Pr j P h) :
    Between j P h := by
  obtain ⟨h1, h2⟩ := GlobalTheory.T.latticeSandwich_of_latticeNormalForm X Pr R j P hP h 1 H (one_mem _)
  rw [mul_one] at h1 h2
  refine (between_iff hP h).1 fun x hx => ⟨?_, h2 x hx⟩
  obtain ⟨y, hy, rfl⟩ := h1 x hx
  rwa [show h⁻¹ (h y) = y from h.symm_apply_apply y]

theorem sameDC_symm {sharp : Bool} {j : ℕ} {P : HeightOneSpectrum (𝓞 X.E)} {h h' : AutY X R j}
    (a : SameDC (Pr := Pr) sharp j P h h') : SameDC (Pr := Pr) sharp j P h' h := by
  obtain ⟨r, hr, k, hk, rfl⟩ := a
  exact ⟨r⁻¹, inv_mem hr, k⁻¹, inv_mem hk, by group⟩

theorem sameDC_mul (sharp : Bool) {j : ℕ} (P : HeightOneSpectrum (𝓞 X.E)) (h : AutY X R j) {r : AutY X R j}
    (hr : r ∈ Loc.R1 X.E (R.N j) (cOf R j)) : SameDC (Pr := Pr) sharp j P h (r * h) :=
  ⟨r, hr, 1, one_mem _, (mul_one _).symm⟩

variable (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

def omScal (i : ℕ) (P : rowSG Pr sel mu) (hal : AutY X R i) (h : AutY X R (i + 1)) : X.K :=
  muAt Ch sel mu cst i P (LinearEquiv.det hal : X.Eˣ) * (muAt Ch sel mu cst i P (LinearEquiv.det h : X.Eˣ))⁻¹ *
    cst.sq P ^ (-(LocE.vP P.1 (qOf P.1) (LinearEquiv.det hal : X.Eˣ)) * (R.N (i + 1) + cOf R (i + 1) : ℕ)) *
    cst.sq P ^ (LocE.vP P.1 (qOf P.1) (LinearEquiv.det h : X.Eˣ) * (R.N i + cOf R i : ℕ))

theorem omPhi_eq (i : ℕ) (P : rowSG Pr sel mu) (hal : AutY X R i) (h : AutY X R (i + 1))
    (x : HomE X.E (R.N i + cOf R i) (R.N (i + 1) + cOf R (i + 1))) :
    omPhi Ch sel mu cst i P hal h x =
      omScal Ch sel mu cst i P hal h * PhiAt Ch mu cst.sharp i P.1 (h.symm.toLinearMap ∘ₗ x ∘ₗ hal.toLinearMap) := rfl

theorem localUnfoldingNonvanishing_iff_eventuallyNonzero (i : ℕ) (P : rowSG Pr sel mu) (hal : AutY X R i) (h : AutY X R (i + 1)) :
    FiniteSumNonzeroLargeDepth Ch sel mu cst i P hal h ↔ UnfNe P.1 (cst.psi P) (omPhi Ch sel mu cst i P hal h) := Iff.rfl

variable {Ch sel mu cst}

theorem omScal_ne_zero (hc : cst.Ok) {i : ℕ} {P : rowSG Pr sel mu} (hd : DegOne P.1) (hm : cst.muq (i + 1) P ≠ 0)
    (hal : AutY X R i) (h : AutY X R (i + 1)) : omScal Ch sel mu cst i P hal h ≠ 0 := by
  have hq : cst.sq P ≠ 0 := by
    intro e
    have := hc.sq_sq P
    rw [e, zero_pow two_ne_zero] at this
    exact hd.1.ne_zero (by exact_mod_cast this.symm)
  have hmu : ∀ a : X.Eˣ, muAt Ch sel mu cst i P a ≠ 0 := fun a => GlobalTheory.T.localCharacter_ne_zero_of_ne_zero X.E X.K P.1 hd _ _ _ hm a.ne_zero
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (hmu _) (inv_ne_zero (hmu _))) (zpow_ne_zero _ hq)) (zpow_ne_zero _ hq)

theorem rank_le (R : Ranks) (j : ℕ) : R.k ≤ R.N j ∧ R.r ≤ R.N j + cOf R j := by
  have : j ≤ j * (R.t + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  unfold Ranks.N Ranks.r cOf
  omega

theorem phiAt_prop {sharp : Bool} {i : ℕ} {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∉ Pr.vGs) :
    (∀ x, PhiAt Ch mu sharp i P x ≠ 0 → IntHom P x) ∧
      ∀ x y, IntHom P y → PhiAt Ch mu sharp i P (x + (qOf P : X.E) • y) = PhiAt Ch mu sharp i P x := by
  unfold PhiAt
  rw [if_neg hP]
  exact GlobalTheory.T.twistPrimeDatum_integral_support_and_invariant X.E X.K P _ _ _ _ _ _ _ (rank_le R i).1 (rank_le R (i + 1)).1 (rank_le R i).2 (rank_le R (i + 1)).2

theorem omPhi_bdd {i : ℕ} {P : rowSG Pr sel mu} (hP : P.1 ∉ Pr.vGs) {hal : AutY X R i} {h : AutY X R (i + 1)}
    (h1 : Between i P.1 hal) (h2 : Between (i + 1) P.1 h) : HomBdd P.1 (i + 1) (omPhi Ch sel mu cst i P hal h) :=
  homBdd_translate (phiAt_prop hP).1 (phiAt_prop hP).2 h1.1 h1.2 h2.1 h2.2 (omPhi_eq Ch sel mu cst i P hal h)

theorem omPhi_mul {i : ℕ} {P : rowSG Pr sel mu} {hal : AutY X R i} {h : AutY X R (i + 1)}
    (h0 : omScal Ch sel mu cst i P hal h ≠ 0) (ρ' : AutY X R i) (ρ : AutY X R (i + 1))
    (x : HomE X.E (R.N i + cOf R i) (R.N (i + 1) + cOf R (i + 1))) :
    omPhi Ch sel mu cst i P (ρ' * hal) (ρ * h) x =
      omScal Ch sel mu cst i P (ρ' * hal) (ρ * h) / omScal Ch sel mu cst i P hal h *
        omPhi Ch sel mu cst i P hal h ((ρ⁻¹).toLinearMap ∘ₗ x ∘ₗ ρ'.toLinearMap) := by
  rw [omPhi_eq, omPhi_eq, ← mul_assoc, div_mul_cancel₀ _ h0]
  rfl

theorem first_unipotent_class_transfer (hc : cst.Ok) {i : ℕ} (hi : i + 1 ≤ R.m - 2) {P : rowSG Pr sel mu} (hP : P.1 ∉ Pr.vGs) (hd : DegOne P.1)
    (hm : cst.muq (i + 1) P ≠ 0) (hD : i + 1 ≤ cst.D P) {hal hal' ρ' : AutY X R i} {h h' ρ : AutY X R (i + 1)}
    (hρ' : ρ' ∈ Loc.R1 X.E _ _) (hρ : ρ ∈ Loc.R1 X.E _ _) (e' : hal' = ρ' * hal) (e : h' = ρ * h)
    (a1 : Between i P.1 hal) (a2 : Between i P.1 hal') (b1 : Between (i + 1) P.1 h) (b2 : Between (i + 1) P.1 h')
    (H : FiniteSumNonzeroLargeDepth Ch sel mu cst i P hal h) : FiniteSumNonzeroLargeDepth Ch sel mu cst i P hal' h' := by
  rw [localUnfoldingNonvanishing_iff_eventuallyNonzero] at H ⊢
  subst e e'
  exact unfNe_transfer hd (by unfold cOf; omega) (by unfold cOf; omega) hD ⟨hc.psi_add P, hc.psi_int P⟩
    (omPhi_bdd hP a1 b1) (omPhi_bdd hP a2 b2)
    (div_ne_zero (omScal_ne_zero hc hd hm _ _) (omScal_ne_zero hc hd hm _ _)) (inv_mem hρ) hρ'
    (omPhi_mul (omScal_ne_zero hc hd hm _ _) ρ' ρ) H

theorem lamYat_coe {j : ℕ} {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∉ Pr.vGs) :
    (lamYat (Pr := Pr) (R := R) j P : Set (Sp X.E (R.N j + cOf R j))) = {v | IntV P v} :=
  Set.ext fun v => mem_lamYat hP v

variable {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}

end Chain

end GlobalTheory.QNormal
