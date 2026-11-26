module

public import Formalism.SharpRestriction.LevelLetterCocycles.ModelKStep
public import Formalism.SharpRestriction.LevelLetterCocycles.LevelClauseOfOpenTool

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.InvariantLetterPolynomialDerivation
noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

section Op

variable (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

def uniformizerInverse : W.EE := Ring.inverse (algebraMap (LetA O n) W.EE W.π₀)

def derivationOnWachModule : W.DD T →ₗ[O] W.DD T := Formalism.MainNotions.LiftingTheory.lifta_δ W T (uniformizerInverse W)

theorem derivation_on_wach_module_apply (x : W.DD T) : derivationOnWachModule W T x = uniformizerInverse W • (W.γ T x - x) := rfl

variable {W} in
theorem algebraMap_uniformizer_mul_inverse (hU : IsUnit (algebraMap (LetA O n) W.EE W.π₀)) :
    algebraMap (LetA O n) W.EE W.π₀ * uniformizerInverse W = 1 :=
  Ring.mul_inverse_cancel _ hU

theorem uniformizer_smul_derivation (hU : IsUnit (algebraMap (LetA O n) W.EE W.π₀)) (x : W.DD T) :
    W.π₀ • derivationOnWachModule W T x = W.γ T x - x := by
  rw [derivation_on_wach_module_apply, ← smul_assoc, Algebra.smul_def, algebraMap_uniformizer_mul_inverse hU, one_smul]

theorem inverse_smul_uniformizer_smul (hU : IsUnit (algebraMap (LetA O n) W.EE W.π₀)) (x : W.DD T) :
    uniformizerInverse W • (W.π₀ • x) = x := by
  rw [← algebraMap_smul W.EE W.π₀ x, smul_smul, mul_comm, algebraMap_uniformizer_mul_inverse hU, one_smul]

theorem smul_comm_letA_EE (a : LetA O n) (e : W.EE) (x : W.DD T) : a • (e • x) = e • (a • x) := by
  rw [← smul_assoc a e x, Algebra.smul_def a e, mul_comm, mul_smul, algebraMap_smul W.EE a x]

theorem gammaA_idempotent (g : W.Gam) (c : ZMod n) : W.γA g (letE c : LetA O n) = letE c := by
  funext i
  show W.γ₀ g ((Pi.single c (1 : PowerSeries O) : LetA O n) i) = (Pi.single c (1 : PowerSeries O) : LetA O n) i
  rw [Pi.single_apply]
  split_ifs <;> simp

theorem idempotent_smul_gamma (c : ZMod n) (x : W.DD T) :
    (letE c : LetA O n) • W.γ T x = W.γ T ((letE c : LetA O n) • x) := by
  show (letE c : LetA O n) • W.γD T W.gam x = W.γD T W.gam ((letE c : LetA O n) • x)
  rw [← algebraMap_smul W.EE (letE c : LetA O n) x, W.γD_smul, W.γE_ext,
    show letγ (W.γ₀ W.gam) (letE c : LetA O n) = letE c from gammaA_idempotent W W.gam c, algebraMap_smul]

theorem gammaD_gamma_comm (δ : W.Gam) (x : W.DD T) : W.γD T δ (W.γ T x) = W.γ T (W.γD T δ x) := by
  show W.γD T δ (W.γD T W.gam x) = W.γD T W.gam (W.γD T δ x)
  rw [← W.γD_mul, ← W.γD_mul, mul_comm]

theorem delta_fixes_inverse (a : LetA O n) (ha : a ∈ W.AΔ) (hU : IsUnit (algebraMap (LetA O n) W.EE a))
    (δ : W.Gam) (hδ : δ ∈ W.DelF) :
    W.γE δ (Ring.inverse (algebraMap (LetA O n) W.EE a)) = Ring.inverse (algebraMap (LetA O n) W.EE a) := by
  have ha' : ∀ δ ∈ W.DelF, W.γA δ a = a := ha
  have hfix : W.γE δ (algebraMap (LetA O n) W.EE a) = algebraMap (LetA O n) W.EE a := by
    rw [W.γE_ext]
    exact congrArg (algebraMap (LetA O n) W.EE) (ha' δ hδ)
  obtain ⟨u, hu⟩ := hU
  rw [← hu] at hfix ⊢
  rw [Ring.inverse_unit]
  have h1 : (u : W.EE) * W.γE δ ↑u⁻¹ = 1 := by
    rw [← hfix, ← map_mul, Units.mul_inv, map_one]
  exact (Units.inv_eq_of_mul_eq_one_right h1).symm

theorem invariantLetter_fixed_smul {c : ZMod n} (e : W.EE) (he : ∀ δ ∈ W.DelF, W.γE δ e = e) {x : W.DD T}
    (h : Formalism.MainNotions.CrystallineLiftingInputs.DL W T c x) : Formalism.MainNotions.CrystallineLiftingInputs.DL W T c (e • x) := by
  refine ⟨?_, fun δ hδ => ?_⟩
  · rw [smul_comm_letA_EE, h.1]
  · rw [W.γD_smul, he δ hδ, h.2 δ hδ]

theorem invariantLetter_gamma_sub {c : ZMod n} {x : W.DD T} (h : Formalism.MainNotions.CrystallineLiftingInputs.DL W T c x) :
    Formalism.MainNotions.CrystallineLiftingInputs.DL W T c (W.γ T x - x) := by
  refine ⟨?_, fun δ hδ => ?_⟩
  · rw [smul_sub, idempotent_smul_gamma, h.1]
  · rw [map_sub, gammaD_gamma_comm, h.2 δ hδ]

theorem invariantLetter_derivation (hπΔ : W.π₀ ∈ W.AΔ) (hU : IsUnit (algebraMap (LetA O n) W.EE W.π₀))
    {c : ZMod n} {x : W.DD T} (h : Formalism.MainNotions.CrystallineLiftingInputs.DL W T c x) :
    Formalism.MainNotions.CrystallineLiftingInputs.DL W T c (derivationOnWachModule W T x) := by
  rw [derivation_on_wach_module_apply]
  exact invariantLetter_fixed_smul W T (uniformizerInverse W)
    (fun δ hδ => delta_fixes_inverse W W.π₀ hπΔ hU δ hδ) (invariantLetter_gamma_sub W T h)

theorem invariantLetter_derivation_pow (hπΔ : W.π₀ ∈ W.AΔ) (hU : IsUnit (algebraMap (LetA O n) W.EE W.π₀))
    {c : ZMod n} (k : ℕ) {x : W.DD T} (h : Formalism.MainNotions.CrystallineLiftingInputs.DL W T c x) :
    Formalism.MainNotions.CrystallineLiftingInputs.DL W T c ((derivationOnWachModule W T ^ k) x) := by
  induction k with
  | zero => rw [pow_zero, Module.End.one_apply]; exact h
  | succ k ih => rw [pow_succ', Module.End.mul_apply]; exact invariantLetter_derivation W T hπΔ hU ih

theorem invariantLetter_polynomial_derivation (hπΔ : W.π₀ ∈ W.AΔ) (hU : IsUnit (algebraMap (LetA O n) W.EE W.π₀))
    {c : ZMod n} (P : Polynomial O) {x : W.DD T} (h : Formalism.MainNotions.CrystallineLiftingInputs.DL W T c x) :
    Formalism.MainNotions.CrystallineLiftingInputs.DL W T c (Polynomial.aeval (derivationOnWachModule W T) P x) := by
  induction P using Polynomial.induction_on'
  next p q hp hq =>
    rw [map_add (f := _), LinearMap.add_apply]
    exact ⟨by rw [smul_add, hp.1, hq.1], fun δ hδ => by rw [map_add (f := _), hp.2 δ hδ, hq.2 δ hδ]⟩
  next k a =>
    rw [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    have hk := invariantLetter_derivation_pow W T hπΔ hU k h
    exact ⟨by rw [smul_comm _ a, hk.1], fun δ hδ => by rw [map_smul, hk.2 δ hδ]⟩

def DerivationPreservesQLattice [NeZero n] : Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W → ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (i : ZMod n) (k : ℤ) (x : W.DD T),
    Formalism.MainNotions.CrystallineLiftingInputs.InQN W T i k x → Formalism.MainNotions.CrystallineLiftingInputs.InQN W T i k (Formalism.MainNotions.CrystallineLiftingInputs.dOp W T x)

def QLattice (c : ZMod n) (k : ℕ) (x : W.DD T) : Prop :=
  Formalism.MainNotions.CrystallineLiftingInputs.DL W T c x ∧ Formalism.MainNotions.LiftingTheory.qp W ^ k • x ∈ W.N T

theorem qLattice_iff (c : ZMod n) (k : ℕ) (x : W.DD T) :
    Formalism.MainNotions.CrystallineLiftingInputs.InQN W T c (k : ℤ) x ↔ QLattice W T c k x := by
  unfold Formalism.MainNotions.CrystallineLiftingInputs.InQN QLattice
  simp

theorem qLattice_add {c : ZMod n} {k : ℕ} {x y : W.DD T} (hx : QLattice W T c k x)
    (hy : QLattice W T c k y) : QLattice W T c k (x + y) := by
  refine ⟨⟨?_, fun δ hδ => ?_⟩, ?_⟩
  · rw [smul_add, hx.1.1, hy.1.1]
  · rw [map_add (f := _), hx.1.2 δ hδ, hy.1.2 δ hδ]
  · rw [smul_add]
    exact add_mem hx.2 hy.2

theorem qLattice_smul {c : ZMod n} {k : ℕ} (a : O) {x : W.DD T} (hx : QLattice W T c k x) :
    QLattice W T c k (a • x) := by
  refine ⟨⟨?_, fun δ hδ => ?_⟩, ?_⟩
  · rw [smul_comm _ a, hx.1.1]
  · rw [map_smul, hx.1.2 δ hδ]
  · rw [smul_comm _ a, ← algebraMap_smul (LetA O n) a]
    exact Submodule.smul_mem _ _ hx.2

theorem qLattice_mono {c : ZMod n} {k k' : ℕ} (hk : k ≤ k') {x : W.DD T} (hx : QLattice W T c k x) :
    QLattice W T c k' x := by
  refine ⟨hx.1, ?_⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [pow_add, mul_comm, mul_smul]
  exact Submodule.smul_mem _ _ hx.2

theorem qLattice_derivation [NeZero n] (hDS : DerivationPreservesQLattice W) (hA : Formalism.MainNotions.LiftingTheory.CaseA W)
    (hT : IsCrys PD T.ρ) (c : ZMod n) (k : ℕ)
    {x : W.DD T} (h : QLattice W T c k x) : QLattice W T c k (derivationOnWachModule W T x) := by
  rw [← qLattice_iff] at h ⊢
  rw [derivation_on_wach_module_apply]
  exact hDS hA T hT c (k : ℤ) x h

theorem qLattice_polynomial_derivation [NeZero n] (hDS : DerivationPreservesQLattice W) (hA : Formalism.MainNotions.LiftingTheory.CaseA W)
    (hT : IsCrys PD T.ρ) (c : ZMod n) (k : ℕ)
    (P : Polynomial O) {x : W.DD T} (h : QLattice W T c k x) :
    QLattice W T c k (Polynomial.aeval (derivationOnWachModule W T) P x) := by
  have hpow : ∀ j : ℕ, QLattice W T c k ((derivationOnWachModule W T ^ j) x) := by
    intro j
    induction j with
    | zero => rw [pow_zero, Module.End.one_apply]; exact h
    | succ j ih => rw [pow_succ', Module.End.mul_apply]; exact qLattice_derivation W T hDS hA hT c k ih
  induction P using Polynomial.induction_on'
  next p q hp hq =>
    rw [map_add (f := _), LinearMap.add_apply]
    exact qLattice_add W T hp hq
  next j a =>
    rw [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    exact qLattice_smul W T a (hpow j)

end Op

end Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

end
end

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

open Polynomial

section Kill

variable (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

def step1Kill_roots (c : ZMod n) (M h a : ℕ) : Finset ℤ :=
  ((jumpSetL W T c M h) ×ˢ Finset.Icc (((0 : ℕ) : ℤ) + 1) (a : ℤ)).image (fun p : ℤ × ℤ => p.1 + p.2)

theorem step1Kill_xList (c : ZMod n) (M h a : ℕ) :
    xListL W T c M h 0 a = (step1Kill_roots W T c M h a).sort (· ≤ ·) := rfl

theorem step1Kill_cO (hV : Formalism.MainNotions.WachCoordinates.Br.ValRing O v) (hRN : Formalism.MainNotions.CrystallineLiftingInputs.RToolNum W) :
    ∃ cO : ℤ → O, (∀ x : ℤ, ((PD.p : ℕ) : O) * cO x = 1 - (((W.χΓ W.gam) ^ (-x) : Oˣ) : O)) ∧
      cO 0 = 0 ∧ ∀ x : ℤ, x ≠ 0 → v (algebraMap O LL (cO x)) = ((padicValInt PD.p x : ℕ) : WithTop ℚ) := by
  classical
  have hc : ∀ j : ℤ, ((PD.p : ℕ) : LL) = 0 → Formalism.MainNotions.CrystallineLiftingInputs.cR W j = 0 := by
    intro j h0
    unfold Formalism.MainNotions.CrystallineLiftingInputs.cR
    simp [h0]
  have hp0 : ((PD.p : ℕ) : LL) ≠ 0 := by
    intro h0
    have h1 := hRN.2 1 0 (by norm_num)
    rw [hc 1 h0, hc 0 h0, sub_zero, AddValuation.map_zero] at h1
    exact WithTop.top_ne_coe h1
  have hnn : ∀ x : ℤ, 0 ≤ v (Formalism.MainNotions.CrystallineLiftingInputs.cR W x) := by
    intro x
    by_cases hx : x = 0
    · rw [hx, hRN.1, AddValuation.map_zero]
      exact le_top
    · have h := hRN.2 x 0 hx
      rw [hRN.1, sub_zero] at h
      rw [h]
      first
        | exact WithTop.coe_nonneg.mpr (by positivity)
        | (rw [← WithTop.coe_zero]; exact WithTop.coe_le_coe.mpr (by positivity))
  have hex : ∀ x : ℤ, ∃ o : O, algebraMap O LL o = Formalism.MainNotions.CrystallineLiftingInputs.cR W x := fun x => hV.2.1 _ (hnn x)
  refine ⟨fun x => Classical.choose (hex x), ?_, ?_, ?_⟩
  · intro x
    apply hV.1
    rw [map_mul, map_natCast, Classical.choose_spec (hex x), map_sub, map_one]
    unfold Formalism.MainNotions.CrystallineLiftingInputs.cR
    first
      | (rw [div_neg, mul_neg, mul_div_assoc', mul_div_cancel_left₀ _ hp0, neg_sub])
      | (field_simp; ring)
      | field_simp
  · apply hV.1
    rw [Classical.choose_spec (hex 0), hRN.1, map_zero]
  · intro x hx
    have h := hRN.2 x 0 hx
    rw [hRN.1, sub_zero] at h
    rw [Classical.choose_spec (hex x), h]
    first
      | exact WithTop.coe_natCast _
      | (norm_cast; done)
      | (simp; done)
      | (push_cast; rfl)

theorem step1Kill_kill [NeZero n] (hR : Formalism.MainNotions.LiftingTheory.lifta_Ring W) (hDS : DerivationPreservesQLattice W)
    (hD : Formalism.MainNotions.RamifiedCoefficientChains.DssLet W) (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (hT : IsCrys PD T.ρ) (Mi hi : ZMod n → ℕ)
    (hJ : Formalism.MainNotions.LiftingTheory.JumpsLet W T Mi hi) (c : ZMod n) (cO : ℤ → O)
    (hcO : ∀ x : ℤ, ((PD.p : ℕ) : O) * cO x = 1 - (((W.χΓ W.gam) ^ (-x) : Oˣ) : O)) (hc0 : cO 0 = 0)
    (a : ℕ) {y₀ : W.DD T} (hy : QLattice W T c a y₀) :
    Polynomial.aeval (derivationOnWachModule W T)
      (X * ∏ x ∈ (step1Kill_roots W T c (Mi c) (hi c) a).filter (· ≠ 0), (X - C (cO x))) y₀ ∈ W.N T := by
  have hU := hR.πU
  have hπΔ := hR.πΔ
  have hv : v (algebraMap O LL (((W.χΓ W.gam : Oˣ) : O) - 1)) = 1 := by
    rw [map_sub, map_one, W.gam_gen, hA.2.1]
    simp
  have hyNl : Formalism.MainNotions.LiftingTheory.qp W ^ a • y₀ ∈ W.Nl T c := by
    have h1 : Formalism.MainNotions.LiftingTheory.qp W ^ a • y₀ = (letE c : LetA O n) • (Formalism.MainNotions.LiftingTheory.qp W ^ a • y₀) := by
      rw [smul_smul, mul_comm, ← smul_smul, hy.1.1]
    rw [h1]
    exact Formalism.MainNotions.LiftingTheory.liftb_letE_mem W T c hy.2
  obtain ⟨seq, h0, hstep, hN⟩ := hD hA T Mi hi hT hJ (W.χΓ W.gam) rfl hv cO hcO c 0 a y₀
    (Nat.zero_le a) hyNl hy.1.2
  have hseq := Formalism.MainNotions.LiftingTheory.lifta_seq W T (uniformizerInverse W) (algebraMap_uniformizer_mul_inverse hU) cO _ seq hstep
  rw [h0] at hseq
  have hNs : seq (xListL W T c (Mi c) (hi c) 0 a).length ∈ W.N T :=
    Formalism.MainNotions.LiftingTheory.liftb_Nl_le W T c (by simpa using hN)
  rw [hseq] at hNs
  have hprod : ((xListL W T c (Mi c) (hi c) 0 a).map
      fun x => (X - C (cO x) : Polynomial O)).prod =
      ∏ x ∈ step1Kill_roots W T c (Mi c) (hi c) a, (X - C (cO x)) := by
    rw [step1Kill_xList, ← List.prod_toFinset _ (Finset.sort_nodup _ _), Finset.sort_toFinset]
  rw [hprod, ← Finset.prod_filter_mul_prod_filter_not _ (fun x => x ≠ 0)] at hNs
  by_cases h0m : (0 : ℤ) ∈ step1Kill_roots W T c (Mi c) (hi c) a
  · have hf : (step1Kill_roots W T c (Mi c) (hi c) a).filter (fun x => ¬ x ≠ 0) = {0} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_singleton, not_not]
      constructor
      · exact fun h => h.2
      · rintro rfl; exact ⟨h0m, rfl⟩
    rw [hf, Finset.prod_singleton, hc0, map_zero, sub_zero, mul_comm] at hNs
    exact hNs
  · have hf : (step1Kill_roots W T c (Mi c) (hi c) a).filter (fun x => ¬ x ≠ 0) = ∅ := by
      ext x
      simp only [Finset.mem_filter, Finset.notMem_empty, not_not, iff_false, not_and]
      rintro hx rfl
      exact h0m hx
    rw [hf, Finset.prod_empty, mul_one] at hNs
    rw [map_mul, Module.End.mul_apply, Polynomial.aeval_X]
    have hQ : QLattice W T c 0 (Polynomial.aeval (derivationOnWachModule W T)
        (∏ x ∈ (step1Kill_roots W T c (Mi c) (hi c) a).filter (· ≠ 0), (X - C (cO x))) y₀) :=
      ⟨invariantLetter_polynomial_derivation W T hπΔ hU _ hy.1, by simpa [derivationOnWachModule] using hNs⟩
    simpa using (qLattice_derivation W T hDS hA hT c 0 hQ).2

theorem step1Kill_norm (hV : Formalism.MainNotions.WachCoordinates.Br.ValRing O v) (hvp : v (PD.p : LL) = 1) (cO : ℤ → O)
    (hcv : ∀ x : ℤ, x ≠ 0 → v (algebraMap O LL (cO x)) = ((padicValInt PD.p x : ℕ) : WithTop ℚ))
    (Sx : Finset ℤ) (hS0 : (0 : ℤ) ∉ Sx) (s : ℕ) (hs : ∑ x ∈ Sx, padicValInt PD.p x ≤ s) :
    ∃ w : O, (C w * ∏ x ∈ Sx, (X - C (cO x))).coeff 0 = ((PD.p : ℕ) : O) ^ s := by
  classical
  have hcoef : ∀ w : O, (C w * ∏ x ∈ Sx, (X - C (cO x))).coeff 0 = w * ∏ x ∈ Sx, -(cO x) := by
    intro w
    rw [Polynomial.mul_coeff_zero, Polynomial.coeff_C_zero, Polynomial.coeff_zero_eq_eval_zero,
      Polynomial.eval_prod]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, zero_sub]
  have hval : ∀ S : Finset ℤ, (0 : ℤ) ∉ S →
      v (algebraMap O LL (∏ x ∈ S, -(cO x))) = ((∑ x ∈ S, padicValInt PD.p x : ℕ) : WithTop ℚ) := by
    intro S
    refine Finset.induction_on S ?_ ?_
    · intro _
      simp
    · intro a S ha ih h0
      have ha0 : a ≠ 0 := fun h => h0 (by rw [← h]; exact Finset.mem_insert_self a S)
      have hS0' : (0 : ℤ) ∉ S := fun h => h0 (Finset.mem_insert_of_mem h)
      rw [Finset.prod_insert ha, Finset.sum_insert ha, map_mul, AddValuation.map_mul, map_neg,
        AddValuation.map_neg, hcv a ha0, ih hS0', Nat.cast_add]
  have hvc := hval Sx hS0
  have hc0 : algebraMap O LL (∏ x ∈ Sx, -(cO x)) ≠ 0 := by
    intro h
    rw [h, AddValuation.map_zero] at hvc
    exact WithTop.natCast_ne_top _ hvc.symm
  have hvps : v (((PD.p : ℕ) : LL) ^ s) = ((s : ℕ) : WithTop ℚ) := by
    rw [AddValuation.map_pow, hvp, nsmul_one]
  have aux : ∀ r : WithTop ℚ, r + ((∑ x ∈ Sx, padicValInt PD.p x : ℕ) : WithTop ℚ) = ((s : ℕ) : WithTop ℚ) →
      0 ≤ r := by
    intro r hr
    induction r using WithTop.recTopCoe with
    | top => exact le_top
    | coe q =>
      rw [← WithTop.coe_natCast, ← WithTop.coe_natCast, ← WithTop.coe_add, WithTop.coe_inj] at hr
      have hq : ((∑ x ∈ Sx, padicValInt PD.p x : ℕ) : ℚ) ≤ (s : ℚ) := by exact_mod_cast hs
      first
        | exact WithTop.coe_nonneg.mpr (by linarith)
        | (rw [← WithTop.coe_zero]; exact WithTop.coe_le_coe.mpr (by linarith))
  have hw'0 : 0 ≤ v (((PD.p : ℕ) : LL) ^ s / algebraMap O LL (∏ x ∈ Sx, -(cO x))) := by
    apply aux
    rw [← hvc, ← AddValuation.map_mul, div_mul_cancel₀ _ hc0, hvps]
  obtain ⟨w, hw⟩ := hV.2.1 _ hw'0
  refine ⟨w, ?_⟩
  rw [hcoef]
  apply hV.1
  rw [map_mul, hw, div_mul_cancel₀ _ hc0, map_pow, map_natCast]

end Kill

end Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

end
