module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JetLL
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslateGaloisRationalityCmPoints
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTaylorCoeffsAlgebraicAtComplexMultiplicatio
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSumTaylorCoordinateSpaceEntire
public import Formalism.LocalToGlobal.KernelLattices.KerStd
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaZJetsThree
public import Formalism.LocalRingCardinality.FactDelDualNabla
public import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.KerJet
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FieldIsoSelfDualAndPeriodLatticesAgree
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelAtPrimeEqSumTorsionTranslates

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueWeightConsecutiveStepsPartition
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueWeightConsecutiveStepsPartition
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.KerJ NumberField Classical

noncomputable section

namespace GlobalTheory.KerWtStep

open Formalism.MainNotions.GL3Columns

theorem half_cast (R : Ranks) (j : ℕ) :
    (((j * (R.t + 1) / 2 : ℕ) : ℤ) : ℚ) = (j : ℚ) * ((R.t : ℚ) + 1) / 2 := by
  obtain ⟨c, hc⟩ := R.t_odd
  have h2 : j * (R.t + 1) = 2 * (j * (c + 1)) := by rw [hc]; ring
  rw [h2, Nat.mul_div_cancel_left _ two_pos]
  push_cast
  rw [hc]
  push_cast
  ring

variable {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {Pm : PeriodMap D.R C}

theorem lamTG_w (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A Pm) (j : ℕ) (hj : j ≤ D.R.m)
    (τ : D.what₂.Tau) (r : Fin (D.R.N j)) : (((lamTG M j τ).w r : ℤ) : ℚ) = lamTr D u τ j r := by
  have h1 := M.lam_eq j hj τ r
  have h2 := lamNo_eq D u τ j r r.2
  show (((M.lam j τ).w r - ((j * (D.R.t + 1) / 2 : ℕ) : ℤ) : ℤ) : ℚ) = _
  push_cast
  rw [h1]
  have h3 := half_cast D.R j
  push_cast at h3
  rw [h3]
  unfold lamNo at h2
  suffices e : (if h : r.1 < D.R.k then hcToWeightQ (D.hcW u τ).u ⟨r.1, h⟩
      else -wG D.R ((D.hcW u τ).e ⟨(r.1 - D.R.k) / (D.R.t + 1), D.R.blk_lt hj r h⟩) ((r.1 - D.R.k) / (D.R.t + 1) + 1)) =
      (if r.1 < D.R.k then lamZ D u τ r else -wJ D u τ ((r.1 - D.R.k) / (D.R.t + 1))) by
    rw [e, ← h2]; ring
  split_ifs with hk
  · simp only [hcToWeightQ, rhoVec, lamZ, dif_pos hk]
    push_cast
    ring
  · simp only [wJ, eJ, dif_pos (D.R.blk_lt hj r hk)]

theorem detShift_eq {N : ℕ} (l : DomWeight N) (hN : 0 < N) : l.detShift = l.w ⟨N - 1, by omega⟩ := dif_pos hN

theorem trueWt_step : ∀ (D : D7) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (A : ColumnsAtT D.R C) (Pm : PeriodMap D.R C)
    (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A Pm) (i : ℕ), i < D.R.m →
    ∃ n : D.what₂.Tau → ℕ, (∀ τ r, (lamTG M i τ).natW r + n τ = nuT D u i τ r) ∧
      (∀ τ, (lamTG M i τ).detShift + C.sSharp i τ = n τ) ∧
      (∀ τ r, (lamTG M (i + 1) τ).natW r = extNu (D.R.N (i + 1)) (fun τ r => (lamTG M i τ).natW r + n τ) τ r) ∧
      ∀ τ, (lamTG M (i + 1) τ).detShift = -C.sDiv i τ := by
  intro D u C A Pm M i hi
  have hN := D.R.N_pos i
  have hlt : D.R.N i < D.R.N (i + 1) := by unfold Ranks.N; rw [Nat.succ_mul]; omega
  have hS : ∀ τ, (C.sSharp i τ : ℚ) = sJ' D u τ i := fun τ => ((wtRec_thm D u τ i hi).1 C).1
  have hD : ∀ τ, (C.sDiv i τ : ℚ) = sJ D u τ i := fun τ => ((wtRec_thm D u τ i hi).1 C).2
  have hnu : ∀ τ r, r < D.R.N i → DV.nuRow D u (i + 1) τ r = ((nuTr D u τ i r : ℚ) : ℝ) :=
    fun τ => (wtRec_thm D u τ i hi).2
  have wi := fun τ (r : Fin (D.R.N i)) => lamTG_w M i hi.le τ r
  have wi1 := fun τ (r : Fin (D.R.N (i + 1))) => lamTG_w M (i + 1) hi τ r
  have ds0 := fun τ => detShift_eq (lamTG M i τ) hN
  have ds1 := fun τ => detShift_eq (lamTG M (i + 1) τ) (D.R.N_pos (i + 1))
  have anti0 : ∀ τ (r : Fin (D.R.N i)), (lamTG M i τ).w ⟨D.R.N i - 1, by omega⟩ ≤ (lamTG M i τ).w r :=
    fun τ r => (lamTG M i τ).anti (show r ≤ ⟨D.R.N i - 1, by omega⟩ from Fin.le_def.2 (by simp; omega))
  have dq1 : ∀ τ, (((lamTG M (i + 1) τ).detShift : ℤ) : ℚ) = -sJ D u τ i := by
    intro τ
    rw [ds1, wi1]
    simp only [lamTr, if_neg (show ¬ (D.R.N (i + 1) - 1 < D.R.N i) by omega),
      if_pos (show D.R.N (i + 1) - 1 < D.R.N (i + 1) by omega)]
  have hpos : ∀ τ, 0 < (lamTG M i τ).detShift + C.sSharp i τ := by
    intro τ
    have h := RowWeightLemmas.nuRow_last_pos D u i hi τ
    rw [hnu τ _ (by omega)] at h
    have e : (((lamTG M i τ).detShift + C.sSharp i τ : ℤ) : ℚ) = nuTr D u τ i (D.R.N i - 1) := by
      rw [ds0]; push_cast; rw [wi, hS]; rfl
    have h' : (0 : ℚ) < nuTr D u τ i (D.R.N i - 1) := by exact_mod_cast h
    rw [← e] at h'
    exact_mod_cast h'
  refine ⟨fun τ => ((lamTG M i τ).detShift + C.sSharp i τ).toNat, ?_, ?_, ?_, ?_⟩
  · intro τ r
    have key : DV.nuRow D u (i + 1) τ r = ((((lamTG M i τ).w r + C.sSharp i τ : ℤ)) : ℝ) := by
      rw [hnu τ r r.2]
      have e : ((((lamTG M i τ).w r + C.sSharp i τ : ℤ)) : ℚ) = nuTr D u τ i r := by
        push_cast; rw [wi, hS]; rfl
      rw [← e, Rat.cast_intCast]
    unfold nuT
    rw [key, ← Int.floor_toNat, Int.floor_intCast]
    have a := anti0 τ r
    have d := ds0 τ
    have p := hpos τ
    unfold DomWeight.natW
    dsimp only
    omega
  · intro τ
    exact (Int.toNat_of_nonneg (hpos τ).le).symm
  · intro τ r
    unfold DomWeight.natW extNu
    by_cases h : r.1 < D.R.N i
    · rw [dif_pos h]
      have e : (lamTG M (i + 1) τ).w r - (lamTG M (i + 1) τ).detShift = (lamTG M i τ).w ⟨r.1, h⟩ + C.sSharp i τ := by
        have : (((lamTG M (i + 1) τ).w r - (lamTG M (i + 1) τ).detShift : ℤ) : ℚ) =
            (((lamTG M i τ).w ⟨r.1, h⟩ + C.sSharp i τ : ℤ) : ℚ) := by
          push_cast
          rw [wi1, dq1, wi, hS]
          simp only [lamTr, if_pos h]
          ring
        exact_mod_cast this
      rw [e]
      have a := anti0 τ ⟨r.1, h⟩
      have d := ds0 τ
      have p := hpos τ
      dsimp only
      omega
    · rw [dite_eq_right h]
      have e : (lamTG M (i + 1) τ).w r - (lamTG M (i + 1) τ).detShift = 0 := by
        have : (((lamTG M (i + 1) τ).w r - (lamTG M (i + 1) τ).detShift : ℤ) : ℚ) = ((0 : ℤ) : ℚ) := by
          push_cast
          rw [wi1, dq1]
          simp only [lamTr, if_neg h, if_pos r.2]
          ring
        exact_mod_cast this
      rw [e]
      rfl
  · intro τ
    have : (((lamTG M (i + 1) τ).detShift : ℤ) : ℚ) = ((-C.sDiv i τ : ℤ) : ℚ) := by
      push_cast; rw [dq1, hD]
    exact_mod_cast this

end GlobalTheory.KerWtStep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueWeightConsecutiveStepsPartitionStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.KerJ NumberField Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trueWeight_consecutive_steps_partition : ∀ (D : D7) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (A : ColumnsAtT D.R C) (Pm : PeriodMap D.R C) (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A Pm) (i : ℕ), i < D.R.m → ∃ n : D.what₂.Tau → ℕ, (∀ τ r, (lamTG M i τ).natW r + n τ = nuT D u i τ r) ∧ (∀ τ, (lamTG M i τ).detShift + C.sSharp i τ = n τ) ∧ (∀ τ r, (lamTG M (i + 1) τ).natW r = extNu (D.R.N (i + 1)) (fun τ r => (lamTG M i τ).natW r + n τ) τ r) ∧ ∀ τ, (lamTG M (i + 1) τ).detShift = -C.sDiv i τ := by
  first | exact @GlobalTheory.KerWtStep.trueWt_step | exact GlobalTheory.KerWtStep.trueWt_step | (intros; apply GlobalTheory.KerWtStep.trueWt_step <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoefInTranslate
open Formalism.MainNotions.G Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric NumberField

noncomputable section

namespace GlobalTheory.AlgTranslate

open GlobalTheory.GalTheta

theorem taylor_sum (D : D7) {N N' : ℕ} {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → VC D N N' → ℂ)
    (hf : ∀ i, Differentiable ℂ (f i)) (α : Mono D N N') :
    TaylorLogMetric.taylor D (fun z => ∑ i ∈ s, c i * f i z) α = ∑ i ∈ s, c i * TaylorLogMetric.taylor D (f i) α := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact GlobalTheory.ThetaConj.taylor_zero D α
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [← ih, ← GlobalTheory.ThetaConj.taylor_mul D _ (hf i)]
    exact GlobalTheory.ThetaConj.taylor_add D ((hf i).const_mul _) (by fun_prop) α

theorem exists_alg_comb (D : D7) {N N' k : ℕ} (c : Fin k → ℂ) (f : Fin k → VC D N N' → ℂ)
    (hf : ∀ i, Differentiable ℂ (f i)) (ha : ∀ i, CoefIn D (f i) Qbar)
    (h : CoefIn D (fun z => ∑ i, c i * f i z) Qbar) :
    ∃ c' : Fin k → ℂ, (∀ i, c' i ∈ Qbar) ∧ (fun z => ∑ i, c i * f i z) = fun z => ∑ i, c' i * f i z := by
  obtain ⟨pr, hpr⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap Qbar ℂ)
    (LinearMap.ker_eq_bot.2 Subtype.val_injective)
  have hp : ∀ a : Qbar, pr (a : ℂ) = a := fun a => LinearMap.congr_fun hpr a
  refine ⟨fun i => pr (c i), fun i => (pr (c i)).2, ?_⟩
  have ht : ∀ α, TaylorLogMetric.taylor D (fun z => ∑ i, c i * f i z) α =
      TaylorLogMetric.taylor D (fun z => ∑ i, (pr (c i) : ℂ) * f i z) α := by
    intro α
    have h1 : (pr (TaylorLogMetric.taylor D (fun z => ∑ i, c i * f i z) α) : ℂ) =
        TaylorLogMetric.taylor D (fun z => ∑ i, c i * f i z) α := congrArg Subtype.val (hp ⟨_, h α⟩)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← h1, taylor_sum D _ _ _ hf, taylor_sum D _ _ _ hf, map_sum]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    have : c i * TaylorLogMetric.taylor D (f i) α = (⟨_, ha i α⟩ : Qbar) • c i := mul_comm _ _
    rw [this, map_smul, mul_comm]
    rfl
  funext z
  have e1 := GlobalTheory.EntireTaylor.hasSum_taylor_mono D N N' (fun z => ∑ i, c i * f i z) (by fun_prop) z
  have e2 := GlobalTheory.EntireTaylor.hasSum_taylor_mono D N N' (fun z => ∑ i, (pr (c i) : ℂ) * f i z) (by fun_prop) z
  simp only [ht] at e1
  exact e1.unique e2

theorem coefIn_translate : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), StandardLatticesGL3.Crv D cc δ → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), StandardLatticesGL3.SD D L → StandardLatticesGL3.SD D L' → ∀ e ∈ Th D (tor0 D cc δ) L L', CoefIn D e Qbar → ∀ x, StandardLatticesGL3.LaQ D (tor0 D cc δ) L L' x → CoefIn D (U D (tor0 D cc δ) x e) Qbar := by
  intro D cc δ hc N N' L L' hL hL' e he hq x hx
  have hG : StandardLatticesGL3.admG1 D := (GlobalTheory.InducedType.induced_type D).1
  obtain ⟨-, -, -, -, hfg, -, -⟩ :=
    GlobalTheory.T.theta_space_selfDual_pair_at_most_line D hG cc δ hc N N' (La D (tor0 D cc δ) L L') (Or.inr ⟨L, L', hL, hL', rfl⟩)
  obtain ⟨m, r, B, hB⟩ := GlobalTheory.T.exists_orthonormal_frame_var D N N'
  obtain ⟨R, hR, hRA⟩ := GlobalTheory.T.exists_nsmul_padded_lattice_mem_basis_product D hG cc δ hc N N' m r L L' B hB hfg
  have hee : IsTr D (tor0 D cc δ) (La D (tor0 D cc δ) L L') e e := by
    have := IsTr.single D (tor0 D cc δ) (A := La D (tor0 D cc δ) L L') e 1 0 1 one_pos (by simp)
    simpa [U_zero] using this
  obtain ⟨G₁, ⟨k, c, t, n, hn, ht, rfl⟩, hGG⟩ := exists_restriction D cc δ hc L L' hL hL' B hB e e he hee
  have hS := GlobalTheory.ThetaAlgebraic.good_sigma hG (GlobalTheory.T.forall_use1 D) hc hB
  set S := StandardLatticesGL3.pullB D (tor0 D cc δ) B (sgStar (lamOf D cc δ))
  have hT := fun i => hS.transl hG hc hB (t := t i) ⟨n, hn, ht i⟩
  have hd : ∀ i, Differentiable ℂ (U D (tor0 D cc δ) (t i) S) := fun i => (hS _ ⟨n, hn, ht i⟩).differentiable
  obtain ⟨c', hc', he'⟩ := exists_alg_comb D c (fun i z => U D (tor0 D cc δ) (t i) S (pad D m z))
    (fun i => (hd i).comp (differentiable_pad D m))
    (fun i α => by
      rw [GlobalTheory.ConjRestrict.taylor_pad D m (hd i)]
      exact (hT i).coefIn _)
    (by rw [hGG] at hq; exact hq)
  have hg := GlobalTheory.ThetaAlgebraic.Good.sum Finset.univ _ fun i _ => (hT i).const_mul (hc' i)
  have hpx : pad D m x ∈ GlobalTheory.ThetaAlgebraic.sat (StandardLatticesGL3.LaB D (tor0 D cc δ) B) := by
    obtain ⟨j, hj, hx⟩ := hx
    refine ⟨R * j, mul_pos hR hj, ?_⟩
    rw [mul_smul, ← pad_nsmul]
    exact hRA _ hx
  have hgen := hg _ hpx
  have e1 : e = fun z => (fun w => ∑ i, c' i * U D (tor0 D cc δ) (t i) S w) (pad D m z) := hGG.trans he'
  intro α
  rw [e1, U_pad D _ m x (fun w => ∑ i, c' i * U D (tor0 D cc δ) (t i) S w),
    GlobalTheory.ConjRestrict.taylor_pad D m hgen.differentiable]
  exact hgen.coefIn _

end GlobalTheory.AlgTranslate
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertiaInvolutionRealPlacePairs
section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.FixedIod
open NumberField Formalism.BasicNotions

namespace UpperTheory.Ram

theorem image_mem_of_fixed_iod {R : Ranks} (H : Host R) {Ω : Type} [Field Ω] [IsAlgClosed Ω] (J : H.E →+* Ω) (M : Subfield Ω)
    (hM : ∀ y : Ω, y ^ (H.QS * H.q) = 1 → y ∈ M) (x : H.E) (hx : H.sigmaOf R.toFrame.iod x = x) : J x ∈ M := by
  refine H.toHostRaw.image_mem_of_fixed J M (Dvd.intro _ rfl) hM x fun u hu => ?_
  rcases H.art_d u hu with h | h
  · rw [h, map_one]; rfl
  · rw [h]; exact hx

end UpperTheory.Ram
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertiaInvolutionRealPlacePairs
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)

namespace GlobalTheory.InertiaPairs

open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition

section HostLemmas

variable {R : Ranks} (H : Host R)

theorem sigmaOf_mul (g h : R.GG) : H.sigmaOf (g * h) = H.sigmaOf g * H.sigmaOf h := by
  unfold Host.sigmaOf
  exact map_mul _ g h

theorem sigmaOf_one : H.sigmaOf 1 = 1 := by
  unfold Host.sigmaOf
  exact map_one _

theorem galE_sigmaOf (g : R.GG) : H.galE (H.sigmaOf g) = g := by
  unfold Host.sigmaOf
  exact MulEquiv.apply_symm_apply _ _

theorem sigmaOf_sqrt_neg (g : R.GG) (h : g.1.2 = -1) : H.sigmaOf g H.sqrtMinusD = -H.sqrtMinusD := by
  have := H.galE_bE (H.sigmaOf g)
  rw [galE_sigmaOf, h] at this
  unfold Host.sqrtMinusD
  rw [this]
  simp

theorem sigmaOf_sqrt_pos (g : R.GG) (h : g.1.2 = 1) : H.sigmaOf g H.sqrtMinusD = H.sqrtMinusD := by
  have := H.galE_bE (H.sigmaOf g)
  rw [galE_sigmaOf, h] at this
  unfold Host.sqrtMinusD
  rw [this]
  simp

theorem sqrt_sq : H.sqrtMinusD ^ 2 = -(H.d : H.E) := by
  exact H.sqd_sq

theorem emb_sigmaOf (g h : R.GG) (x : H.E) : H.emb g (H.sigmaOf h x) = H.emb (g * h) x := by
  unfold Host.emb
  rw [sigmaOf_mul]
  rfl

end HostLemmas

end GlobalTheory.InertiaPairs

namespace GlobalTheory.InertiaPairs

open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition Polynomial
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)

section KurLemmas

variable {p : ℕ} [Fact p.Prime]

theorem mem_Kur_of_pow {x : ℂ_[p]} (n : ℕ) (hn : 0 < n) (hd : ¬ p ∣ n) (hx : x ^ n = 1) : x ∈ MaximalUnramifiedExtension p :=
  Subfield.le_topologicalClosure _ (Subfield.subset_closure ⟨n, hn, hd, hx⟩)

variable {R : Ranks} (H : Host R) (J : H.E →+* ℂ_[p])

end KurLemmas

end GlobalTheory.InertiaPairs

namespace GlobalTheory.InertiaPairs

open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)

section Fixed

variable {R : Ranks} (H : Host R)

def sInv (R : Ranks) : R.GG := ((1, -1), 1)

end Fixed

end GlobalTheory.InertiaPairs

namespace GlobalTheory.InertiaPairs

open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.MainNotions.G (plGG)

theorem embT_tauPl (D : D7) (z : Bool × HH D) : TaylorLogMetric.embT D (tauPl D z) = D.host.emb (plGG D z) := by
  unfold TaylorLogMetric.embT tauPl
  rw [Equiv.apply_symm_apply]

theorem eTau_tauPl (D : D7) (z : Bool × HH D) : (D.eTau (tauPl D z) : D.R.GG) = plGG D z := by
  unfold tauPl
  rw [Equiv.apply_symm_apply]

theorem tauSg_tauPl (D : D7) (b : Bool) (t : HH D) : TaylorLogMetric.tauSg D (tauPl D (b, t)) = tauPl D (!b, t) := by
  have hm : plGG D (b, t) * TaylorLogMetric.sgm D = plGG D (!b, t) := by
    cases b <;> refine Prod.ext (Prod.ext ?_ ?_) ?_ <;> simp [plGG, Formalism.HC.Frame.tau1, Formalism.HC.Frame.tau2, TaylorLogMetric.sgm]
  have hmem : (D.eTau (tauPl D (b, t)) : D.R.GG) * TaylorLogMetric.sgm D ∈ D.R.Psi := by
    rw [eTau_tauPl, hm]; exact plGG_mem_Psi D _
  rw [show TaylorLogMetric.tauSg D (tauPl D (b, t)) = D.eTau.symm ⟨_, hmem⟩ from dif_pos hmem]
  refine (Equiv.symm_apply_eq _).2 (Subtype.ext ?_)
  simp only [eTau_tauPl, hm]

theorem inertia_pairs : ∀ (D : D7) (p : ℕ) [Fact p.Prime], p = D.host.d → ∀ ι : ℂ ≃+* ℂ_[p],
    ∃ (cE s : D.host.E ≃+* D.host.E) (δ : D.host.E), (∀ y, cE y = D.host.conj y) ∧ δ ^ 2 = -(p : D.host.E) ∧
    cE δ = -δ ∧ s δ = -δ ∧ (∀ y, s (s y) = y) ∧ (∀ y, s (cE y) = cE (s y)) ∧
    Function.Injective (fun z : Bool × HH D => TaylorLogMetric.embT D (tauPl D z)) ∧
    (∀ τ ρ, TaylorLogMetric.embT D τ δ = TaylorLogMetric.embT D ρ δ) ∧
    (∀ (t : HH D) y, TaylorLogMetric.embT D (tauPl D (true, t)) y = TaylorLogMetric.embT D (tauPl D (false, t)) (s (cE y))) ∧
    (∀ τ y, s y = y → ι (TaylorLogMetric.embT D τ y) ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p) ∧ Function.Bijective (tauPl D) ∧
    ∀ t : HH D, TaylorLogMetric.tauSg D (tauPl D (false, t)) = tauPl D (true, t) ∧
      TaylorLogMetric.tauSg D (tauPl D (true, t)) = tauPl D (false, t) := by
  intro D p _ hp ι
  have hp2 : p ≠ 2 := by rw [hp]; exact D.host.hypOdd.2.2.2.2
  have hpq : D.host.q ≠ p := by rw [hp]; exact D.host.hypOdd.2.2.1
  refine ⟨D.host.conj.toRingEquiv, (D.host.sigmaOf (sInv D.R)).toRingEquiv, D.host.sqrtMinusD, fun y => rfl, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, tauPl_bij D, fun t => ⟨tauSg_tauPl D false t, tauSg_tauPl D true t⟩⟩
  · rw [sqrt_sq, hp]
  · exact sigmaOf_sqrt_neg D.host (D.R.cc) rfl
  · exact sigmaOf_sqrt_neg D.host (sInv D.R) rfl
  · intro y
    change D.host.sigmaOf (sInv D.R) (D.host.sigmaOf (sInv D.R) y) = y
    rw [← AlgEquiv.mul_apply, ← sigmaOf_mul]
    have : sInv D.R * sInv D.R = 1 := by
      refine Prod.ext (Prod.ext ?_ ?_) ?_ <;> simp [sInv]
    rw [this, sigmaOf_one]
    rfl
  · intro y
    change D.host.sigmaOf (sInv D.R) (D.host.sigmaOf (D.R.cc) y) = D.host.sigmaOf (D.R.cc) (D.host.sigmaOf (sInv D.R) y)
    rw [← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply, ← sigmaOf_mul, ← sigmaOf_mul, mul_comm]
  · intro z z' h
    have h' : ∀ x, D.host.φ₀ (D.host.sigmaOf (plGG D z) x) = D.host.φ₀ (D.host.sigmaOf (plGG D z') x) := fun x => by
      have := RingHom.congr_fun h x
      simp only [embT_tauPl] at this
      exact this
    have hs : D.host.sigmaOf (plGG D z) = D.host.sigmaOf (plGG D z') :=
      AlgEquiv.ext fun x => D.host.φ₀.injective (h' x)
    have hg : plGG D z = plGG D z' := by
      unfold Host.sigmaOf at hs
      exact (D.host.gal).symm.injective hs
    apply (tauPl_bij D).1
    unfold tauPl
    congr 1
    exact Subtype.ext hg
  · intro τ ρ
    change D.host.φ₀ (D.host.sigmaOf (D.eTau τ : D.R.GG) D.host.sqrtMinusD) =
      D.host.φ₀ (D.host.sigmaOf (D.eTau ρ : D.R.GG) D.host.sqrtMinusD)
    rw [sigmaOf_sqrt_pos D.host _ (D.eTau τ).2, sigmaOf_sqrt_pos D.host _ (D.eTau ρ).2]
  · intro t y
    change D.host.emb _ y = D.host.emb _ (D.host.sigmaOf (sInv D.R) (D.host.sigmaOf (D.R.cc) y))
    rw [eTau_tauPl, eTau_tauPl, emb_sigmaOf, emb_sigmaOf]
    have hg : plGG D (false, t) * sInv D.R * D.R.cc = plGG D (true, t) := by
      refine Prod.ext (Prod.ext ?_ ?_) ?_ <;> simp [plGG, Formalism.HC.Frame.tau1, Formalism.HC.Frame.tau2, sInv, Formalism.HC.Frame.cc, c0]
    rw [hg]
  · intro τ y hy
    have hy' : D.host.sigmaOf (sInv D.R) y = y := hy
    exact UpperTheory.Ram.image_mem_of_fixed_iod D.host ((ι : ℂ →+* ℂ_[p]).comp (TaylorLogMetric.embT D τ)) (MaximalUnramifiedExtension p)
      (fun z hz => mem_Kur_of_pow _ (Nat.mul_pos D.host.QS_pos D.host.hyp.1.pos)
        (by rw [hp]; exact D.host.toHostRaw.d_not_dvd_QSq) hz) y hy'

end GlobalTheory.InertiaPairs
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertiaInvolutionRealPlacePairsStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertiaInvolution_realPlacePairs : ∀ (D : D7) (p : ℕ) [Fact p.Prime], p = D.host.d → ∀ ι : ℂ ≃+* ℂ_[p], ∃ (cE s : D.host.E ≃+* D.host.E) (δ : D.host.E), (∀ y, cE y = D.host.conj y) ∧ δ ^ 2 = -(p : D.host.E) ∧ cE δ = -δ ∧ s δ = -δ ∧ (∀ y, s (s y) = y) ∧ (∀ y, s (cE y) = cE (s y)) ∧ Function.Injective (fun z : Bool × HH D => TaylorLogMetric.embT D (tauPl D z)) ∧ (∀ τ ρ, TaylorLogMetric.embT D τ δ = TaylorLogMetric.embT D ρ δ) ∧ (∀ (t : HH D) y, TaylorLogMetric.embT D (tauPl D (true, t)) y = TaylorLogMetric.embT D (tauPl D (false, t)) (s (cE y))) ∧ (∀ τ y, s y = y → ι (TaylorLogMetric.embT D τ y) ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p) ∧ Function.Bijective (tauPl D) ∧ ∀ t : HH D, TaylorLogMetric.tauSg D (tauPl D (false, t)) = tauPl D (true, t) ∧ TaylorLogMetric.tauSg D (tauPl D (true, t)) = tauPl D (false, t) := by
  first | exact @GlobalTheory.InertiaPairs.inertia_pairs | exact GlobalTheory.InertiaPairs.inertia_pairs | (intros; apply GlobalTheory.InertiaPairs.inertia_pairs <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PadicSeriesLinearCoordsEqFlatTaylor
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PadicSeriesLinearCoordsEqFlatTaylor
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

noncomputable section

namespace GlobalTheory.FlatTaylorBridge

open MvPowerSeries

theorem coeff_taylorMv_flatV (D : D7) (X : Fields) (s : Seam D X) (N N' : ℕ) (G : TaylorLogMetric.VC D N N' → ℂ)
    (hG : AnalyticOnNhd ℂ G Set.univ) (m : DVar X.Tau N N' →₀ ℕ) :
    coeff m (taylorMv fun z => G (s.flatV N N' z)) =
      TaylorLogMetric.taylor D G (m.mapDomain fun v => (s.iT v.1, v.2)) := by
  have hc : ∀ k : ℕ, ContDiff ℂ k G := fun k => hG.contDiff
  let G' : VCx X.Tau N N' → ℂ := fun w => G fun τ => w (s.iT.symm τ)
  let L : VCx X.Tau N N' →L[ℂ] TaylorLogMetric.VC D N N' :=
    ContinuousLinearMap.pi fun τ => ContinuousLinearMap.proj (s.iT.symm τ)
  have hG' : AnalyticOnNhd ℂ G' Set.univ := by
    have : G' = G ∘ L := rfl
    rw [this]
    exact hG.comp (L.analyticOnNhd _) (fun _ _ => trivial)
  have h1 := Formalism.L2.AlgTh.taylor_jet_expansion X.Tau N N' G' hG' m
  have h2 := GlobalTheory.SeamTransport.deriv_transport s.iT G hc m
  rw [GlobalTheory.SeamTransport.taylor_eq] at h2
  have hfl : (fun z => G (s.flatV N N' z)) = fun z => G' (Formalism.L2.AlgTh.flat X.Tau N N' z) := rfl
  have hne : ((m.mapDomain fun v => (s.iT v.1, v.2)).prod fun _ n => (n.factorial : ℂ)) ≠ 0 := by
    rw [Finsupp.prod]
    exact Finset.prod_ne_zero_iff.2 fun _ _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have hpr : ((m.mapDomain fun v => (s.iT v.1, v.2)).prod fun _ n => (n.factorial : ℂ)) =
      ((Formalism.DworkPowerSeriesWeights.mfact m : ℕ) : ℂ) := by
    rw [Finsupp.prod_mapDomain_index_inj]
    · simp [Formalism.DworkPowerSeriesWeights.mfact, Finsupp.prod]
    · intro v w h
      exact Prod.ext (s.iT.injective (Prod.ext_iff.1 h).1) (Prod.ext_iff.1 h).2
  apply mul_left_cancel₀ hne
  rw [← h2, hpr, hfl]
  convert h1 using 3

end GlobalTheory.FlatTaylorBridge

namespace GlobalTheory.FlatTaylorBridge
open MvPowerSeries

theorem subst_rename_lin {σ τ γ : Type} [Finite σ] [Finite τ] {R : Type} [CommRing R] (f : σ → τ)
    (a : τ → MvPowerSeries γ R) (ha : ∀ t, constantCoeff (a t) = 0) (Φ : MvPowerSeries σ R) :
    subst a (rename f Φ) = subst (fun s => a (f s)) Φ := by
  have hs := hasSubst_of_constantCoeff_zero ha
  rw [rename_eq_subst, subst_comp_subst_apply (HasSubst.X_comp f) hs Φ]
  congr 1
  funext x
  exact subst_X hs (f x)

theorem bridge : ∀ (D : D7) (X : Fields) (s : Seam D X) (N N' : ℕ) (p : ℕ) [Fact p.Prime] (lm : TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : ℂ ≃+* ℂ_[p]), Formalism.L2.KerInert.IotaExt lm ι → ∀ G : TaylorLogMetric.VC D N N' → ℂ, AnalyticOnNhd ℂ G Set.univ → TaylorLogMetric.CoefIn D G TaylorLogMetric.Qbar → ∀ (ν : Type) [Fintype ν] (M : D.what₂.Tau × Fin N' × Fin N → ν → ℂ_[p]), TaylorLogMetric.atLin M (fun j => MvPowerSeries.X j) (TaylorLogMetric.pSer D lm G) = Formalism.L2.Th1.G.linSub (fun (i : DVar X.Tau N N') x => M (s.iT i.1, i.2) x) (MvPowerSeries.map (ι : ℂ →+* ℂ_[p]) (taylorMv fun z => G (s.flatV N N' z))) := by
  intro D X s N N' p _ lm ι hι G hG hC ν _ M
  let eE : DVar X.Tau N N' ≃ D.what₂.Tau × Fin N' × Fin N := s.iT.prodCongr (Equiv.refl _)
  have hP : TaylorLogMetric.pSer D lm G =
      rename (eE : DVar X.Tau N N' → D.what₂.Tau × Fin N' × Fin N)
        (map (ι : ℂ →+* ℂ_[p]) (taylorMv fun z => G (s.flatV N N' z))) := by
    ext α
    obtain ⟨m, rfl⟩ := Finsupp.mapDomain_surjective eE.surjective α
    have h := coeff_embDomain_rename eE.toEmbedding
      (map (ι : ℂ →+* ℂ_[p]) (taylorMv fun z => G (s.flatV N N' z))) m
    rw [Finsupp.embDomain_eq_mapDomain] at h
    refine Eq.trans ?_ h.symm
    rw [coeff_map, coeff_taylorMv_flatV D X s N N' G hG m]
    change TaylorLogMetric.lamC lm (TaylorLogMetric.taylor D G _) = _
    unfold TaylorLogMetric.lamC
    rw [dite_eq_left (hC _)]
    exact (hι ⟨_, hC _⟩).symm
  rw [hP]
  unfold TaylorLogMetric.atLin Formalism.L2.Th1.G.linSub
  rw [subst_rename_lin]
  · congr 1
  · intro t
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [map_mul, constantCoeff_X, mul_zero]

end GlobalTheory.FlatTaylorBridge
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PadicSeriesLinearCoordsEqFlatTaylorStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padicSeries_linearCoords_eq_flatTaylor : ∀ (D : D7) (X : Fields) (s : Seam D X) (N N' : ℕ) (p : ℕ) [Fact p.Prime] (lm : TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : ℂ ≃+* ℂ_[p]), Formalism.L2.KerInert.IotaExt lm ι → ∀ G : TaylorLogMetric.VC D N N' → ℂ, AnalyticOnNhd ℂ G Set.univ → TaylorLogMetric.CoefIn D G TaylorLogMetric.Qbar → ∀ (ν : Type) [Fintype ν] (M : D.what₂.Tau × Fin N' × Fin N → ν → ℂ_[p]), TaylorLogMetric.atLin M (fun j => MvPowerSeries.X j) (TaylorLogMetric.pSer D lm G) = Formalism.L2.Th1.G.linSub (fun (i : DVar X.Tau N N') x => M (s.iT i.1, i.2) x) (MvPowerSeries.map (ι : ℂ →+* ℂ_[p]) (taylorMv fun z => G (s.flatV N N' z))) := by
  first | exact @GlobalTheory.FlatTaylorBridge.bridge | exact GlobalTheory.FlatTaylorBridge.bridge | (intros; apply GlobalTheory.FlatTaylorBridge.bridge <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormTwelveCubedEqOneOfFiveLePrime
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

namespace GlobalTheory.GoodModelFive

theorem norm_nat_twelve (p : ℕ) [Fact p.Prime] (h5 : 5 ≤ p) {N k : ℕ} (hN : N ∣ 12 ^ k) : ‖(N : ℂ_[p])‖ = 1 := by
  refine Formalism.L2.Th1.E.ScaledModelNorms.norm_nat p fun h => ?_
  have hp : p.Prime := Fact.out
  have h12 : p ∣ 12 := hp.dvd_of_dvd_pow (h.trans hN)
  have hle : p ≤ 12 := Nat.le_of_dvd (by norm_num) h12
  interval_cases p <;> first | omega | exact absurd hp (by norm_num)

theorem norm_twelve_cubed_eq_one_of_five_le_prime (p : ℕ) [Fact p.Prime] (h5 : 5 ≤ p) : ‖(1728 : ℂ_[p])‖ = 1 := by
  simpa using norm_nat_twelve p h5 (N := 1728) (k := 3) (by norm_num)

theorem norm_27 (p : ℕ) [Fact p.Prime] (h5 : 5 ≤ p) : ‖(27 : ℂ_[p])‖ = 1 := by
  simpa using norm_nat_twelve p h5 (N := 27) (k := 3) (by norm_num)

theorem lamOf_eq_map (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) :
    TaylorLogMetric.lamOf D cc δ = (TaylorLogMetric.lamOf D cc 1).map (AddMonoidHom.mulLeft δ) := by
  unfold TaylorLogMetric.lamOf
  rw [AddMonoidHom.map_closure]
  congr 1
  ext w
  simp only [Set.mem_setOf_eq, Set.mem_image, AddMonoidHom.coe_mulLeft, one_mul]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨_, ⟨c, hc, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    exact ⟨c, hc, rfl⟩

theorem omega1_ne_zero (L : PeriodPair) : L.ω₁ ≠ 0 := by
  have := L.indep.ne_zero 0
  simpa using this

theorem intCurve_of_disc_one (hIn : GlobalTheory.ThLoc.Inputs) (d : ℕ) (L : PeriodPair) (hsq : Squarefree d) (hd4 : d % 4 = 3)
    (hcm : Formalism.L2.Th1.CM.HasCMBy d L) (hΔ : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = 1) (p : ℕ) [Fact p.Prime] (h5 : 5 ≤ p)
    (ι : ℂ ≃+* ℂ_[p]) : IntCurve (curveL p L ι) := by
  set a : ℂ := L.g₂ with ha
  set b : ℂ := L.g₃ with hb
  have hj : 1728 * a ^ 3 = Formalism.L2.Th1.CM.jInv L := by
    unfold Formalism.L2.Th1.CM.jInv
    rw [← ha, ← hb, hΔ, div_one]
  have hJ : ‖ι (Formalism.L2.Th1.CM.jInv L)‖ ≤ 1 :=
    GlobalTheory.NormSum.KernelAt.norm_le_one_of_isIntegral (by convert map_isIntegral_int ι (hIn.jInt d L hsq hd4 hcm); exact Subsingleton.elim _ _)
  have ha3 : ‖ι a‖ ^ 3 ≤ 1 := by
    have h := congrArg ι hj
    rw [map_mul, map_pow, map_ofNat] at h
    rw [← h, norm_mul, norm_twelve_cubed_eq_one_of_five_le_prime p h5, one_mul, norm_pow] at hJ
    exact hJ
  have ha1 : ‖ι a‖ ≤ 1 := (pow_le_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 ha3
  have hb2 : ‖ι b‖ ^ 2 ≤ 1 := by
    have h : 27 * ι b ^ 2 = ι a ^ 3 - 1 := by
      have h := congrArg ι hΔ
      rw [map_sub, map_mul, map_pow, map_pow, map_ofNat, map_one] at h
      linear_combination -h
    have h' := congrArg norm h
    rw [norm_mul, norm_27 p h5, one_mul, norm_pow] at h'
    rw [h', sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (by simp))
    rw [norm_pow]; exact ha3
  have hb1 : ‖ι b‖ ≤ 1 := (pow_le_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 hb2
  unfold curveL
  refine Formalism.L2.Th1.E.ScaledModelNorms.intCurve_short p h5 _ _ ha1 hb1 ?_
  have h := congrArg ι hΔ
  rw [map_sub, map_mul, map_pow, map_pow, map_ofNat, map_one] at h
  rw [h, norm_one]

end GlobalTheory.GoodModelFive

namespace GlobalTheory.GoodModelFive

theorem goodModel_five : GlobalTheory.ThLoc.Inputs → ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), TaylorLogMetric.IsCurveIdeal D cc →
    TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0),
    CmOK a₀ b₀ c₀ D.host.d → (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ →
    ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ ι : ℂ ≃+* ℂ_[p], IntCurve (curveL p (cmL a₀ b₀ D.host.d ha hd lam hlam) ι) := by
  intro hIn D cc δ _hcc hδ a₀ b₀ c₀ ha hd lam hlam hok hlat p _ h5 ι
  set L := cmL a₀ b₀ D.host.d ha hd lam hlam with hL
  obtain ⟨h4, _hodd, h8, hprime⟩ := hok
  have hmem : ∀ z, z ∈ TaylorLogMetric.lamOf D cc δ ↔ z ∈ L.lattice := fun z => by
    rw [← hlat]; rfl

  have hδ0 : δ ≠ 0 := by
    rintro rfl
    have h1 : L.ω₁ ∈ TaylorLogMetric.lamOf D cc 0 := (hmem _).2 (L.mem_lattice.2 ⟨1, 0, by simp⟩)
    have hle : TaylorLogMetric.lamOf D cc 0 ≤ ⊥ := by
      unfold TaylorLogMetric.lamOf
      rw [AddSubgroup.closure_le]
      rintro w ⟨c, -, rfl⟩
      simp
    exact omega1_ne_zero L (by simpa using hle h1)

  set L' := Formalism.L2.Th1.F.scalePair L δ⁻¹ (inv_ne_zero hδ0) with hL'
  have hH := Formalism.L2.Th1.F.homogeneity L δ⁻¹ (inv_ne_zero hδ0)
  have hmem' : ∀ z, z ∈ TaylorLogMetric.lamOf D cc 1 ↔ z ∈ L'.lattice := fun z => by
    rw [hH.1, inv_inv, ← hmem, lamOf_eq_map D cc δ]
    exact (AddSubgroup.mem_map_iff_mem (f := AddMonoidHom.mulLeft δ) (mul_right_injective₀ hδ0)).symm
  have hdict := GlobalTheory.LatticeInvariants.invariants_dictionary L' (TaylorLogMetric.lamOf D cc 1) hmem'
  have e2 : TaylorLogMetric.g2 (TaylorLogMetric.lamOf D cc 1) = δ ^ 4 * L.g₂ := by
    rw [hdict.1, hH.2.2.2.2.2.2.2.2.2.1, inv_pow, inv_inv]
  have e3 : TaylorLogMetric.g3 (TaylorLogMetric.lamOf D cc 1) = δ ^ 6 * L.g₃ := by
    rw [hdict.2.1, hH.2.2.2.2.2.2.2.2.2.2, inv_pow, inv_inv]

  have hΔ : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = 1 := by
    have h : δ ^ 12 = δ ^ 12 * (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) := by
      conv_lhs => rw [hδ]
      unfold TaylorLogMetric.discr
      rw [e2, e3]
      ring
    have h12 : δ ^ 12 ≠ 0 := pow_ne_zero _ hδ0
    exact (mul_left_cancel₀ h12 (h.symm.trans (mul_one _).symm))

  have hbodd : Odd b₀ := by
    rcases Int.even_or_odd b₀ with ⟨k, hk⟩ | h
    · exfalso
      have e : (D.host.d : ℤ) = 4 * ((a₀ : ℤ) * c₀ - k * k) := by rw [hk] at h4; linear_combination -h4
      generalize (a₀ : ℤ) * c₀ - k * k = m at e
      omega
    · exact h
  have hcm : Formalism.L2.Th1.CM.HasCMBy D.host.d L :=
    Formalism.L2.Th1.F.hasCMByScale D.host.d _ lam hlam
      (Formalism.L2.Th1.F.cmPairHasCMBy a₀ b₀ c₀ D.host.d ha hd h4 hbodd)
  exact intCurve_of_disc_one hIn D.host.d L hprime.prime.squarefree (by omega) hcm hΔ p h5 ι

end GlobalTheory.GoodModelFive
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColR
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)

noncomputable section

namespace GlobalTheory.DFrame

variable (D : D7)

def rho {p : ℕ} [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (z : Bool × HH D) : D.host.E →+* ℂ_[p] :=
  (ι : ℂ →+* ℂ_[p]).comp (TaylorLogMetric.embT D (tauPl D z))

abbrev JJ (n : Bool × HH D → ℕ) (N N' : ℕ) : Type :=
  (Σ z : Bool × HH D, Fin (n z)) × ((Bool × HH D) × Fin N) × ((Bool × HH D) × Fin N')

def rowL {N : ℕ} (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (σ : Bool × HH D → 𝓞 D.host.E)
    (l : (Bool × HH D) × Fin N) : Fin N → D.host.E :=
  fun j => (σ l.1 : D.host.E) * (P (tauPl D l.1))⁻¹ l.2 j

def colR {N' : ℕ} (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E) (σ' : Bool × HH D → 𝓞 D.host.E)
    (r : (Bool × HH D) × Fin N') : Fin N' → D.host.E :=
  fun i => (σ' r.1 : D.host.E) * P' (tauPl D r.1) i r.2

def mat {n : Bool × HH D → ℕ} {N N' : ℕ} (a : ∀ z, Fin (n z) → D.host.E)
    (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E)
    (σ σ' : Bool × HH D → 𝓞 D.host.E) (j : JJ D n N N') : Matrix (Fin N') (Fin N) D.host.E :=
  Matrix.of fun i k => a j.1.1 j.1.2 * colR D P' σ' j.2.2 i * rowL D P σ j.2.1 k

def vecF {X : Fields} (s : Seam D X) {N N' : ℕ} (M : Matrix (Fin N') (Fin N) D.host.E) : DVar X.Tau N N' → ℂ :=
  fun k => TaylorLogMetric.embT D (s.iT k.1) (M k.2.1 k.2.2)

def act {X : Fields} (s : Seam D X) (N N' : ℕ) (e : 𝓞 D.host.E) : (DVar X.Tau N N' → ℂ) →ₗ[ℂ] (DVar X.Tau N N' → ℂ) where
  toFun x := fun k => TaylorLogMetric.embT D (s.iT k.1) (e : D.host.E) * x k
  map_add' x y := by funext k; simp [mul_add]
  map_smul' c x := by funext k; simp; ring

def gc {p : ℕ} [Fact p.Prime] {n : Bool × HH D → ℕ} (cκ : Bool × HH D → ℂ_[p]) (r : ∀ z, Fin (n z) → ℂ_[p])
    (z : Bool × HH D) (α : Σ z : Bool × HH D, Fin (n z)) : ℂ_[p] :=
  if α.1 = z then cκ z * r α.1 α.2 else 0

def pc {p : ℕ} [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) {N : ℕ} (σ : Bool × HH D → 𝓞 D.host.E) (z : Bool × HH D)
    (l : (Bool × HH D) × Fin N) (a : Fin N) : ℂ_[p] :=
  if l = (z, a) then (rho D ι z (σ z : D.host.E))⁻¹ else 0

def coef {p : ℕ} [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) {n : Bool × HH D → ℕ} {N N' : ℕ} (cκ : Bool × HH D → ℂ_[p])
    (r : ∀ z, Fin (n z) → ℂ_[p]) (σ σ' : Bool × HH D → 𝓞 D.host.E) (j : JJ D n N N')
    (x : (Bool × HH D) × Fin N × Fin N') : ℂ_[p] :=
  gc D cκ r x.1 j.1 * pc D ι σ x.1 j.2.1 x.2.1 * pc D ι σ' x.1 j.2.2 x.2.2

def uu {p : ℕ} [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) {n : Bool × HH D → ℕ} (cκ : Bool × HH D → ℂ_[p])
    (r : ∀ z, Fin (n z) → ℂ_[p]) (a : ∀ z, Fin (n z) → D.host.E) (t : HH D) : ℂ_[p] :=
  ∑ α, ∑ α', gc D cκ r (false, t) α * rho D ι (false, t) (a α.1 α.2 * D.host.conj (a α'.1 α'.2)) *
    gc D cκ r (true, t) α'

end GlobalTheory.DFrame
end
end
