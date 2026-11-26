module

public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NabValPullbackMonomial
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsGoodReductionAlgebraicWeierstrassModel
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.CayleyEndomorphismsModular

@[expose] public section

section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselCayleySideBound
section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselCayleySideBound
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.MomentPointwise

theorem sum_sq_eq_trace {n : Type} [Fintype n] (A : Matrix n n ℂ) :
    ((∑ i, ∑ j, ‖A i j‖ ^ 2 : ℝ) : ℂ) = (Aᴴ * A).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.conj_mul']

theorem sum_sq_conj {n : Type} [Fintype n] [DecidableEq n] (Q X : Matrix n n ℂ)
    (hQ : Q ∈ Matrix.unitaryGroup n ℂ) :
    ∑ i, ∑ j, ‖(Q * X * Q⁻¹) i j‖ ^ 2 = ∑ i, ∑ j, ‖X i j‖ ^ 2 := by
  have h1 : Qᴴ * Q = 1 := Matrix.mem_unitaryGroup_iff'.1 hQ
  have hinv : Q⁻¹ = Qᴴ := Matrix.inv_eq_left_inv h1
  apply Complex.ofReal_injective
  rw [sum_sq_eq_trace, sum_sq_eq_trace, hinv]
  have : (Q * X * Qᴴ)ᴴ * (Q * X * Qᴴ) = Q * (Xᴴ * X * Qᴴ) := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Qᴴ Q, h1, Matrix.one_mul]
  rw [this, Matrix.trace_mul_comm, Matrix.mul_assoc, h1, Matrix.mul_one]

theorem exp_mem {k r : ℕ} {X : Mx k r} (hX : PI.UpqRep.InLieHpk k r X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ GG k r := by
  refine CCRuleCW.exp_mem_UH (Formalism.QuantumDeterminants.Hpk k r) _ ?_
  have hL : Xᴴ * Formalism.QuantumDeterminants.Hpk k r + Formalism.QuantumDeterminants.Hpk k r * X = 0 := hX
  rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
      Matrix.mul_smul, ← smul_add, hL, smul_zero]

theorem one_mem_UW (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : (1 : Mx k r) ∈ Formalism.QuantumDeterminants.UWset k r z := by
  refine ⟨?_, fun a => ⟨Matrix.one_mulVec _, Matrix.one_mulVec _⟩, Matrix.one_mulVec _⟩
  show (1 : Mx k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r * 1 = Formalism.QuantumDeterminants.Hpk k r
  simp

theorem pointwise : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (l : R.H → Wp) (Q : Mx k r) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub), R.IsDG ε mu → SideG k r z π u μW μN μG νq → IsBes R z π l → PI.UpqRep.IsCayleyU k r ε Q → R.IsE Q E → ∀ g ∈ GG k r, ∀ (a : Fin r) (w : R.smSub), (lenA k r z g a.succ / lenA k r z g a.castSucc) ^ 2 * ‖l (R.σ g w)‖ ^ 2 ≤ ∑ c, ∑ e, ‖l (R.σ g (E c e w))‖ ^ 2 := by
  intro hK k r ε mu R Wp _ _ _ _ z π u μW μN μG νq l Q E hR hS hl hQ hE g hg a w
  obtain ⟨hz, hT, ⟨u₀, hπ⟩, -⟩ := hS
  have hπ1 : π 1 = 1 := (Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_facts hT hπ).1
  obtain ⟨hmul, -, -, hsm, -⟩ := GlobalTheory.T.discreteSeries_unitary_smooth_basic hK k r ε mu R hR
  obtain ⟨hact, -, -, hcomp⟩ := GlobalTheory.T.smooth_maps_closure hK k r ε mu mu mu R R R hR hR hR
  obtain ⟨X, hX, hXn, hXt⟩ := GlobalTheory.T.exists_lie_unitary_element_simple_root k r z hz hT g hg a
  obtain ⟨-, -, hexp⟩ := GlobalTheory.T.derivedAction_expand_matrixUnits hK k r ε mu R hR Q E hQ.1.1 hE
  obtain ⟨ladd, lsmul, leq, lcont⟩ := hl
  have hla : 0 ≤ lenA k r z g a.castSucc := Metric.infDist_nonneg
  have hla1 : 0 ≤ lenA k r z g a.succ := Metric.infDist_nonneg
  rcases hla.eq_or_lt with h0 | hpos
  · rw [← h0]
    simp only [div_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
    positivity
  set L := lenA k r z g a.succ with hL
  have badd : ∀ v ∈ R.sm, ∀ v' ∈ R.sm, l (R.σ g (v + v')) = l (R.σ g v) + l (R.σ g v') := by
    intro v hv v' hv'
    rw [map_add (f := _)]; exact ladd _ (hsm g hg v hv) _ (hsm g hg v' hv')
  have bsmul : ∀ (c : ℂ), ∀ v ∈ R.sm, l (R.σ g (c • v)) = c • l (R.σ g v) := by
    intro c v hv
    rw [map_smul]; exact lsmul _ _ (hsm g hg v hv)
  have hder := (GlobalTheory.T.frechetContinuous_continuousOn_orbit_hasDerivAt hK k r ε mu R hR Wp (fun v => l (R.σ g v)) badd bsmul
    (hcomp Wp _ l (hact g hg) lcont) w w.2).2 X hX
  have hfun : (fun t : ℝ => l (R.σ g (R.σ (NormedSpace.exp ((t : ℂ) • X)) w))) =
      fun t : ℝ => Complex.exp (-(2 * (L : ℂ) * (t : ℂ)) * Complex.I) • l (R.σ g w) := by
    funext t
    obtain ⟨m, hm, hgm, hψ⟩ := hXt t
    rw [← hmul g hg _ (exp_mem hX t), hgm, hmul m hm.1 g hg, ← hψ]
    have := leq 1 (one_mem_UW k r z) m hm _ (hsm g hg w w.2)
    rw [Matrix.one_mul, hπ1] at this
    exact this
  have hd2 : HasDerivAt (fun t : ℝ => Complex.exp (-(2 * (L : ℂ) * (t : ℂ)) * Complex.I) • l (R.σ g w))
      ((-(2 * (L : ℂ)) * Complex.I) • l (R.σ g w)) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => -(2 * (L : ℂ) * (t : ℂ)) * Complex.I) (-(2 * (L : ℂ)) * Complex.I) 0 := by
      have := (((Complex.ofRealCLM.hasDerivAt (x := 0)).const_mul (2 * (L : ℂ))).neg).mul_const Complex.I
      simpa using this
    have h2 := h1.cexp.smul_const (l (R.σ g w))
    simpa using h2
  rw [hfun] at hder
  have heq := hd2.unique hder
  let B : R.smSub →ₗ[ℂ] Wp :=
    { toFun := fun v => l (R.σ g v)
      map_add' := fun v v' => badd v v.2 v' v'.2
      map_smul' := fun c v => bsmul c v v.2 }
  have hsum : l (R.σ g (PI.UpqRep.dsig (k := k) (r := r) R.σ X w)) =
      ∑ p : Fin (2 * r + k + 1) × Fin (2 * r + k + 1), (Q * X * Q⁻¹) p.1 p.2 • l (R.σ g (E p.1 p.2 w)) := by
    have h1 : B (∑ c, ∑ e, (Q * X * Q⁻¹) c e • E c e w) = ∑ c, ∑ e, (Q * X * Q⁻¹) c e • B (E c e w) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul]
    rw [Fintype.sum_prod_type, hexp X hX w]
    refine Eq.trans ?_ h1
    show _ = l (R.σ g ((∑ c, ∑ e, (Q * X * Q⁻¹) c e • E c e w : R.smSub) : R.H))
    simp only [Submodule.coe_sum, Submodule.coe_smul]
  have key := Formalism.HermitianLatticeCounting.P.majorant_cauchy_schwarz_holds Wp (Fin (2 * r + k + 1) × Fin (2 * r + k + 1))
    (fun p => (Q * X * Q⁻¹) p.1 p.2) (fun p => l (R.σ g (E p.1 p.2 w))) (l (R.σ g w))
    (-(2 * (L : ℂ)) * Complex.I) 1 _ L hpos (by simp [abs_of_nonneg hla1]) (heq.trans hsum)
    (by rw [Fintype.sum_prod_type, sum_sq_conj Q X hQ.2]; exact hXn)
  rw [Fintype.sum_prod_type, one_mul] at key
  exact key

end GlobalTheory.MomentPointwise
end
end Gp91
end

section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselCayleySideBoundStatement
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.Gp91.GlobalTheory.T.bessel_cayley_side_bound : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (l : R.H → Wp) (Q : Mx k r) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub), R.IsDG ε mu → SideG k r z π u μW μN μG νq → IsBes R z π l → PI.UpqRep.IsCayleyU k r ε Q → R.IsE Q E → ∀ g ∈ GG k r, ∀ (a : Fin r) (w : R.smSub), (lenA k r z g a.succ / lenA k r z g a.castSucc) ^ 2 * ‖l (R.σ g w)‖ ^ 2 ≤ ∑ c, ∑ e, ‖l (R.σ g (E c e w))‖ ^ 2 := by
  first | exact @GlobalTheory.MomentPointwise.pointwise | exact GlobalTheory.MomentPointwise.pointwise | (intros; apply GlobalTheory.MomentPointwise.pointwise <;> assumption)
end Gp91
end
end

section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.FamilySetupCayleyBound
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.RatioMoment

theorem iterate_bound {X M ι : Type} [MeasurableSpace X] [NormedAddCommGroup M] [Fintype ι] (μ : Measure X)
    (κ : X → ℝ) (f : M → X → ℝ) (T : ι → ι → M → M) (L : ℕ → M → Prop) (N : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hκ : AEMeasurable κ μ) (hf : ∀ w, AEMeasurable (f w) μ) (hf0 : ∀ w x, 0 ≤ f w x)
    (hpt : ∀ᵐ x ∂μ, ∀ w, κ x ^ 2 * f w x ≤ ∑ c, ∑ e, f (T c e w) x)
    (hL : ∀ j w, L j w → ∀ c e, L (j + 2) (T c e w))
    (hs : ∀ j w, j ≤ N → L j w → ∑ c, ∑ e, ‖T c e w‖ ^ 2 ≤ B ^ 2 * ‖w‖ ^ 2)
    (h0 : ∀ w, ∫⁻ x, ENNReal.ofReal (1 * f w x) ∂μ ≤ ENNReal.ofReal (‖w‖ ^ 2)) :
    ∀ q j, j + 2 * q ≤ N → ∀ w, L j w →
      ∫⁻ x, ENNReal.ofReal (κ x ^ (2 * q) * f w x) ∂μ ≤ ENNReal.ofReal (B ^ (2 * q) * ‖w‖ ^ 2) := by
  intro q
  induction q with
  | zero =>
    intro j _ w _
    simpa using h0 w
  | succ q ih =>
    intro j hj w hw
    have hN : j ≤ N := by omega
    have hpos : ∀ x, 0 ≤ κ x ^ (2 * q) := fun x => (even_two_mul q).pow_nonneg _
    have hm : ∀ v, AEMeasurable (fun x => ENNReal.ofReal (κ x ^ (2 * q) * f v x)) μ :=
      fun v => ENNReal.measurable_ofReal.comp_aemeasurable ((hκ.pow_const _).mul (hf v))
    calc ∫⁻ x, ENNReal.ofReal (κ x ^ (2 * (q + 1)) * f w x) ∂μ
        ≤ ∫⁻ x, ∑ c, ∑ e, ENNReal.ofReal (κ x ^ (2 * q) * f (T c e w) x) ∂μ := by
          apply lintegral_mono_ae
          filter_upwards [hpt] with x hx
          have h1 : κ x ^ (2 * (q + 1)) * f w x ≤ ∑ c, ∑ e, κ x ^ (2 * q) * f (T c e w) x := by
            calc κ x ^ (2 * (q + 1)) * f w x = κ x ^ (2 * q) * (κ x ^ 2 * f w x) := by ring
              _ ≤ κ x ^ (2 * q) * ∑ c, ∑ e, f (T c e w) x := mul_le_mul_of_nonneg_left (hx w) (hpos x)
              _ = ∑ c, ∑ e, κ x ^ (2 * q) * f (T c e w) x := by simp_rw [Finset.mul_sum]
          calc ENNReal.ofReal (κ x ^ (2 * (q + 1)) * f w x)
              ≤ ENNReal.ofReal (∑ c, ∑ e, κ x ^ (2 * q) * f (T c e w) x) := ENNReal.ofReal_le_ofReal h1
            _ = ∑ c, ∑ e, ENNReal.ofReal (κ x ^ (2 * q) * f (T c e w) x) := by
              rw [ENNReal.ofReal_sum_of_nonneg
                (fun c _ => Finset.sum_nonneg (fun e _ => mul_nonneg (hpos x) (hf0 _ x)))]
              refine Finset.sum_congr rfl (fun c _ => ?_)
              exact ENNReal.ofReal_sum_of_nonneg (fun e _ => mul_nonneg (hpos x) (hf0 _ x))
      _ = ∑ c, ∑ e, ∫⁻ x, ENNReal.ofReal (κ x ^ (2 * q) * f (T c e w) x) ∂μ := by
          rw [lintegral_finsetSum' _ (fun c _ => Finset.aemeasurable_fun_sum _ (fun e _ => hm _))]
          refine Finset.sum_congr rfl (fun c _ => ?_)
          exact lintegral_finsetSum' _ (fun e _ => hm _)
      _ ≤ ∑ c, ∑ e, ENNReal.ofReal (B ^ (2 * q) * ‖T c e w‖ ^ 2) := by
          gcongr with c _ e _
          exact ih (j + 2) (by omega) _ (hL j w hw c e)
      _ = ENNReal.ofReal (B ^ (2 * q) * ∑ c, ∑ e, ‖T c e w‖ ^ 2) := by
          simp_rw [Finset.mul_sum]
          rw [ENNReal.ofReal_sum_of_nonneg (fun c _ => Finset.sum_nonneg
            (fun e _ => mul_nonneg (pow_nonneg hB _) (sq_nonneg _)))]
          refine Finset.sum_congr rfl (fun c _ => ?_)
          rw [ENNReal.ofReal_sum_of_nonneg (fun e _ => mul_nonneg (pow_nonneg hB _) (sq_nonneg _))]
      _ ≤ ENNReal.ofReal (B ^ (2 * (q + 1)) * ‖w‖ ^ 2) := by
          apply ENNReal.ofReal_le_ofReal
          calc B ^ (2 * q) * ∑ c, ∑ e, ‖T c e w‖ ^ 2 ≤ B ^ (2 * q) * (B ^ 2 * ‖w‖ ^ 2) :=
                mul_le_mul_of_nonneg_left (hs j w hN hw) (pow_nonneg hB _)
            _ = B ^ (2 * (q + 1)) * ‖w‖ ^ 2 := by ring

theorem ratio_moment : HypsG → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (l : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ) (Q : Mx k r) (E : ∀ ν, Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (R ν).smSub), SetupG lam u b bv ga h q0 z π μW μN μG νq R l dg → PI.UpqRep.IsCayleyU k r (PI.BesselPeriodGGP.eps48 k r) Q → (∀ ν, n1 ν ≤ q0 → (R ν).IsE Q (E ν) ∧ Formalism.REAL.GlRel (E ν)) → ∀ ν, n1 ν ≤ q0 → ∀ (j q : ℕ), j + 2 * q ≤ 4 * (2 * r + k + 1) ^ 2 → ∀ (a : Fin r) (w : (R ν).smSub), Lev (PI.BesselPeriodGGP.eps48 k r) (E ν) (fun a => lam a + ((ν : Fin (2 * r + k + 1) → ℤ) a : ℝ)) j w → ∫⁻ x, ENNReal.ofReal ((lenA k r z (Matrix.of x) a.succ / lenA k r z (Matrix.of x) a.castSucc) ^ (2 * q) * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal ((b ^ 2) ^ (2 * q) * ‖w‖ ^ 2) := by
  intro hH k r Wp _ _ _ _ lam u b bv ga h q0 z π μW μN μG νq R l dg Q E hS hQ hE ν hn j q hjq a w hw
  have h0all := (Gp91.GlobalTheory.T.bessel_functional_l2_bound_and_isometry hH k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg hS ν hn).1
  obtain ⟨hnum, hfam, hside, hsf⟩ := hS
  have hk : 1 ≤ k := hnum.1
  have hDG := hfam ν hn
  obtain ⟨hE1, hGl⟩ := hE ν hn
  have hMod := Gp91.GlobalTheory.T.cayley_endomorphisms_modular hH k r _ _ (R ν) hk hDG Q (E ν) hQ hE1
  obtain ⟨hBeL, hdg, -⟩ := hsf ν hn
  have hKF : PI.KFinSmooth := hH.1.2.2.1
  obtain ⟨hae, -, hlen, hmeas⟩ :=
    Gp91.GlobalTheory.T.quotientMeasure_ae_mem_and_measurable_besselModel hKF k r _ _ (R ν) Wp z π u μW μN μG νq hDG hside
  have hν : ∀ i, |((ν i : ℤ) : ℝ)| ≤ q0 := by
    intro i
    have h1 : (ν i).natAbs ≤ n1 ν :=
      Finset.single_le_sum (f := fun i => (ν i).natAbs) (fun i _ => Nat.zero_le _) (Finset.mem_univ i)
    have h2 : ((ν i).natAbs : ℝ) ≤ q0 := by exact_mod_cast h1.trans hn
    rwa [Nat.cast_natAbs, Int.cast_abs] at h2
  obtain ⟨-, -, -, -, -, hlo, hhi, hbd, -, hga, hgap, -, hq0ga, hq0h, hbv⟩ := hnum
  have i0 : k - 1 < 2 * r + k + 1 := by omega
  have i1 : k < 2 * r + k + 1 := by omega
  have hbvq : 100 * ((q0 : ℝ) + 1) ≤ bv := by
    have e1 : k - (k - 1) = 1 := by omega
    have e2 : ¬ k < k - 1 := by omega
    have hne : PI.BesselPeriodGGP.eps48 k r ⟨k - 1, i0⟩ ≠ PI.BesselPeriodGGP.eps48 k r ⟨k, i1⟩ := by
      simp [PI.BesselPeriodGGP.eps48, e1, e2]
    have g1 := hgap _ _ hne
    have a1 := hhi ⟨k - 1, i0⟩ (show k ≤ k - 1 + 1 by omega)
    have a2 := hhi ⟨k, i1⟩ (show k ≤ k + 1 by omega)
    have : |lam ⟨k - 1, i0⟩ - lam ⟨k, i1⟩| ≤ bv := by
      rw [abs_le]; constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]
    have hq0h' : 100 * ((q0 : ℝ) + 1) ≤ h := by exact_mod_cast hq0h
    linarith
  have hbvb : bv ≤ b := by
    have a1 := hhi ⟨k - 1, i0⟩ (show k ≤ k - 1 + 1 by omega)
    have := hbd ⟨k - 1, i0⟩
    rw [abs_le] at this
    linarith [a1.2]
  have hShape : BranchingSupport.Shape (PI.BesselPeriodGGP.eps48 k r) k
      (fun i => lam i + ((ν i : ℤ) : ℝ)) bv := by
    obtain ⟨h', hgap', hgok'⟩ := hDG.gap
    have hmuA := hDG.hc.1
    have hh' : 2 ≤ h' := by
      have := hgok'.2.1
      have : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ 2 * r + k + 1))
      nlinarith
    have hq0 : ((q0 : ℝ)) ≤ bv / 100 := by linarith
    refine ⟨hk, by omega, ?_, ?_, ?_, hbv⟩
    · intro x c hxc
      have hpos : ∀ y y' : Fin (2 * r + k + 1), y < y' →
          0 < (lam y + ((ν y : ℤ) : ℝ)) - (lam y' + ((ν y' : ℤ) : ℝ)) :=
        fun y y' hyy => sub_pos.2 (hmuA hyy)
      have hdiff : ∀ y y' : Fin (2 * r + k + 1), y < y' →
          PI.BesselPeriodGGP.eps48 k r y ≠ PI.BesselPeriodGGP.eps48 k r y' →
          2 ≤ (lam y + ((ν y : ℤ) : ℝ)) - (lam y' + ((ν y' : ℤ) : ℝ)) := by
        intro y y' hyy hne
        have g := hgap' y y' hne
        rw [abs_of_pos (hpos y y' hyy)] at g
        linarith
      by_cases hε : PI.BesselPeriodGGP.eps48 k r x = PI.BesselPeriodGGP.eps48 k r c
      · have hxc' : (x : ℕ) < c := hxc
        have nx := hν x
        have nc := hν c
        rw [abs_le] at nx nc
        by_cases hc : (c : ℕ) + 1 < k
        · have := hga x c hxc hc
          have hq0ga' : 100 * ((q0 : ℝ) + 1) ≤ ga := by exact_mod_cast hq0ga
          linarith
        · by_cases hc' : (c : ℕ) = k - 1
          · have l1 := hlo x (by omega)
            have l2 := hhi c (by omega)
            linarith [l1.1, l2.2]
          · have hb' : (c : ℕ) - 1 < 2 * r + k + 1 := by omega
            let y : Fin (2 * r + k + 1) := ⟨c - 1, hb'⟩
            have hyc : y < c := by show (c : ℕ) - 1 < c; omega
            have hεy : PI.BesselPeriodGGP.eps48 k r y ≠ PI.BesselPeriodGGP.eps48 k r c := by
              have n1' : ¬ ((c : ℕ) - 1 < k - 1) := by omega
              have n2' : ¬ ((c : ℕ) < k - 1) := by omega
              simp only [PI.BesselPeriodGGP.eps48, y, n1', n2', if_false]
              rcases Nat.mod_two_eq_zero_or_one ((c : ℕ) - (k - 1)) with h0 | h1
              · have : ((c : ℕ) - 1 - (k - 1)) % 2 = 1 := by omega
                simp [h0, this]
              · have : ((c : ℕ) - 1 - (k - 1)) % 2 = 0 := by omega
                simp [h1, this]
            have hxy : x < y := by
              have hle : (x : ℕ) ≤ (c : ℕ) - 1 := by omega
              rcases Nat.lt_or_ge (x : ℕ) ((c : ℕ) - 1) with hlt | hge
              · exact hlt
              · exfalso
                have hxeq : x = y := Fin.ext (by show (x : ℕ) = (c : ℕ) - 1; omega)
                exact hεy (hxeq ▸ hε)
            have d1 := hpos x y hxy
            have d2 := hdiff y c hyc hεy
            linarith
      · exact hdiff x c hxc hε
    · intro x hx
      have hx' : (x : ℕ) < k - 1 := by omega
      refine ⟨by simp [PI.BesselPeriodGGP.eps48, hx'], ?_, ?_⟩ <;>
      · have l1 := hlo x hx
        have nx := hν x
        rw [abs_le] at nx
        linarith [l1.1, l1.2]
    · intro x hx
      have l1 := hhi x hx
      have nx := hν x
      rw [abs_le] at nx
      constructor <;> linarith [l1.1, l1.2]
  refine iterate_bound νq
    (fun x => lenA k r z (Matrix.of x) a.succ / lenA k r z (Matrix.of x) a.castSucc)
    (fun (w : ↥(R ν).smSub) x => dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)
    (fun c e w => E ν c e w)
    (fun j w => Lev (PI.BesselPeriodGGP.eps48 k r) (E ν) (fun i => lam i + ((ν i : ℤ) : ℝ)) j w)
    (4 * (2 * r + k + 1) ^ 2) (b ^ 2) (sq_nonneg b) ?_ ?_ ?_ ?_ ?_ ?_ ?_ q j hjq w hw
  · exact (hlen a.succ).div (hlen a.castSucc)
  · intro v
    exact (((hmeas (l ν) hBeL.1 v v.2).norm).aemeasurable.pow_const 2).const_mul (dg ν)
  · intro v x
    exact mul_nonneg hdg.le (sq_nonneg _)
  · filter_upwards [hae] with x hx
    intro v
    have h1 := Gp91.GlobalTheory.T.bessel_cayley_side_bound hKF k r _ _ (R ν) Wp z π u μW μN μG νq (l ν) Q (E ν) hDG hside
      hBeL.1 hQ hE1 (Matrix.of x) hx a v
    have h2 := mul_le_mul_of_nonneg_left h1 hdg.le
    simp only [Finset.mul_sum] at h2
    beta_reduce
    calc _ = dg ν * ((lenA k r z (Matrix.of x) a.succ / lenA k r z (Matrix.of x) a.castSucc) ^ 2 *
          ‖l ν ((R ν).σ (Matrix.of x) v)‖ ^ 2) := by ring
      _ ≤ _ := h2
  · intro j' v hv c e
    exact _root_.GlobalTheory.lev_E_add_two _ _ _ _ _ j' v hGl hMod.2.1 hv c e
  · intro j' v hj' hv
    have := _root_.GlobalTheory.T.unitaryGlModule_level_sum_norm_sq_le _ _ _ _ _ k j' bv b v hMod hShape hbvb hj' hv
    calc _ ≤ b ^ 4 * ‖v‖ ^ 2 := this
      _ = (b ^ 2) ^ 2 * ‖v‖ ^ 2 := by ring
  · intro v
    exact h0all v v.2

end GlobalTheory.RatioMoment
end Gp91
end

section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.FamilySetupCayleyBoundStatement
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.Gp91.GlobalTheory.T.family_setup_cayley_bound : HypsG → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (l : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ) (Q : Mx k r) (E : ∀ ν, Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (R ν).smSub), SetupG lam u b bv ga h q0 z π μW μN μG νq R l dg → PI.UpqRep.IsCayleyU k r (PI.BesselPeriodGGP.eps48 k r) Q → (∀ ν, n1 ν ≤ q0 → (R ν).IsE Q (E ν) ∧ Formalism.REAL.GlRel (E ν)) → ∀ ν, n1 ν ≤ q0 → ∀ (j q : ℕ), j + 2 * q ≤ 4 * (2 * r + k + 1) ^ 2 → ∀ (a : Fin r) (w : (R ν).smSub), Lev (PI.BesselPeriodGGP.eps48 k r) (E ν) (fun a => lam a + ((ν : Fin (2 * r + k + 1) → ℤ) a : ℝ)) j w → ∫⁻ x, ENNReal.ofReal ((lenA k r z (Matrix.of x) a.succ / lenA k r z (Matrix.of x) a.castSucc) ^ (2 * q) * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal ((b ^ 2) ^ (2 * q) * ‖w‖ ^ 2) := by
  first | exact @GlobalTheory.RatioMoment.ratio_moment | exact GlobalTheory.RatioMoment.ratio_moment | (intros; apply GlobalTheory.RatioMoment.ratio_moment <;> assumption)
end Gp91
end
