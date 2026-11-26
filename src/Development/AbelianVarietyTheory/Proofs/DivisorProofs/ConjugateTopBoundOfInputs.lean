module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientModelTopClassesMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstJetOperatorNormCauchyBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupDividingLabelPersistsDeeperLevel
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnderEqOfConj
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmulMemLatOIdem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaLiftMultiplicitySpacesOfPublishedStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftDatumConjugateHalfFiniteFourierSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8ThetaSetupGenericPointExists
public import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateTopBoundOfInputs
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean

noncomputable section

namespace GlobalTheory.KerConjMean

theorem pow_le_exp_posLog (x : ℝ) (g : ℕ) : x ^ g ≤ Real.exp (g * Real.posLog x) := by
  rcases eq_or_ne x 0 with rfl | hx
  · rcases g with _ | g
    · simp
    · rw [zero_pow (Nat.succ_ne_zero g)]; exact (Real.exp_pos _).le
  · calc x ^ g ≤ |x ^ g| := le_abs_self _
      _ = |x| ^ g := abs_pow x g
      _ = Real.exp (g * Real.log |x|) := by
          rw [← Real.log_pow, Real.exp_log (pow_pos (abs_pos.2 hx) g)]
      _ ≤ Real.exp (g * Real.posLog x) := by
          gcongr
          rw [Real.log_abs]; unfold Real.posLog; exact le_max_right _ _

theorem max_pow_le_exp_posLog (A : ℝ) (hA : 0 < A) (d : ℕ) :
    max 1 A⁻¹ ^ d ≤ Real.exp (d * Real.posLog A⁻¹) := by
  have h1 : max 1 A⁻¹ ≤ Real.exp (Real.posLog A⁻¹) := by
    refine max_le ?_ ?_
    · exact Real.one_le_exp (by unfold Real.posLog; exact le_max_left _ _)
    · calc A⁻¹ = Real.exp (Real.log A⁻¹) := (Real.exp_log (inv_pos.2 hA)).symm
        _ ≤ Real.exp (Real.posLog A⁻¹) := by gcongr; unfold Real.posLog; exact le_max_right _ _
  calc max 1 A⁻¹ ^ d ≤ Real.exp (Real.posLog A⁻¹) ^ d := pow_le_pow_left₀ (by positivity) h1 d
    _ = Real.exp (d * Real.posLog A⁻¹) := (Real.exp_nat_mul _ d).symm

theorem size_bound (K f N b rd Kx W1 W2 a bb c : ℝ) (g : ℕ) (hK0 : 0 ≤ K) (hc0 : 0 ≤ c) (hcf : c ≤ f) (hb3 : 3 ≤ b) (hN1 : 1 ≤ N) (hNb : N ≤ b)
    (hf1 : 1 ≤ f) (hfb : f ≤ b) (hrd0 : 0 ≤ rd) (hrd : rd ≤ b) (ha0 : 0 ≤ a) (haN : a ≤ N) (hbb0 : 0 ≤ bb)
    (hbN : bb ≤ N) (hW1 : W1 ≤ f * N * (8 * b)) (hW2 : W2 ≤ f * N * (8 * b)) (hW10 : 0 ≤ W1) (hW20 : 0 ≤ W2)
    (hg : (g : ℝ) = f * a * bb) (hKx : 0 < Kx)
    (hlogKx : Real.log Kx ≤ K * (W1 + W2 + c * (a + bb) ^ 2 + 1) * Real.log (2 + W1 + W2 + a + bb + c)) :
    Real.log (3 * (2 * (g : ℝ) * rd + 1) ^ g * Kx) ≤ (6 + 126 * K) * f * N * b * Real.log b ∧
      (g : ℝ) ≤ f * N * b := by
  have hb0 : 0 < b := by linarith
  have hf0 : 0 ≤ f := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hlogb : 1 ≤ Real.log b := by
    have : Real.exp 1 ≤ b := by linarith [Real.exp_one_lt_d9]
    simpa using Real.log_le_log (Real.exp_pos 1) this
  have hfN1 : 1 ≤ f * N := one_le_mul_of_one_le_of_one_le hf1 hN1
  have hfNb : 1 ≤ f * N * b := by nlinarith
  have hab : a * bb ≤ N * N := mul_le_mul haN hbN hbb0 hN0
  have hfNN : f * a * bb ≤ f * N * N := by
    have := mul_le_mul_of_nonneg_left hab hf0
    linarith
  have hNN : f * N * N ≤ f * N * b := mul_le_mul_of_nonneg_left hNb (by positivity)
  have hgG : (g : ℝ) ≤ f * N * b := by rw [hg]; linarith
  have hfNb3 : f * N * b ≤ b ^ 3 := by
    have h1 := mul_le_mul hfb hNb hN0 hb0.le
    have h2 := mul_le_mul_of_nonneg_right h1 hb0.le
    calc f * N * b ≤ b * b * b := h2
      _ = _ := by ring
  have hg3 : (g : ℝ) ≤ b ^ 3 := hgG.trans hfNb3
  have hg0 : (0 : ℝ) ≤ g := Nat.cast_nonneg g
  have hrdpos : 0 < 2 * (g : ℝ) * rd + 1 := by have := mul_nonneg (mul_nonneg zero_le_two hg0) hrd0; linarith
  have hq : 2 * (g : ℝ) * rd + 1 ≤ 3 * b ^ 4 := by
    have h1 := mul_le_mul hg3 hrd hrd0 (by positivity)
    have h2 : (1 : ℝ) ≤ b ^ 4 := one_le_pow₀ (by linarith)
    have h3 : b ^ 3 * b = b ^ 4 := by ring
    linarith
  have hl3 : Real.log 3 ≤ Real.log b := Real.log_le_log (by norm_num) hb3
  have hlq : Real.log (2 * (g : ℝ) * rd + 1) ≤ 5 * Real.log b := by
    calc _ ≤ Real.log (3 * b ^ 4) := Real.log_le_log hrdpos hq
      _ = Real.log 3 + 4 * Real.log b := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
      _ ≤ _ := by linarith
  have hlq0 : 0 ≤ Real.log (2 * (g : ℝ) * rd + 1) := Real.log_nonneg (by
    have := mul_nonneg (mul_nonneg zero_le_two hg0) hrd0; linarith)
  have hY0 : 0 ≤ f * N * b * Real.log b := by positivity
  have hgl : (g : ℝ) * Real.log (2 * (g : ℝ) * rd + 1) ≤ 5 * (f * N * b * Real.log b) := by
    have := mul_le_mul hgG hlq hlq0 (by positivity); linarith
  have hKb : Real.log Kx ≤ 126 * K * (f * N * b * Real.log b) := by
    have hsq : (a + bb) ^ 2 ≤ (2 * N) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
    have hab2 : c * (a + bb) ^ 2 ≤ 4 * (f * N * b) := by
      have := mul_le_mul hcf hsq (by positivity) hf0
      have e : f * (2 * N) ^ 2 = 4 * (f * N * N) := by ring
      linarith
    have hQ1 : W1 + W2 + c * (a + bb) ^ 2 + 1 ≤ 21 * (f * N * b) := by linarith
    have hQ1' : 0 ≤ W1 + W2 + c * (a + bb) ^ 2 + 1 := by positivity
    have hArg0 : 0 < 2 + W1 + W2 + a + bb + c := by linarith
    have hb27 : (27 : ℝ) ≤ b ^ 3 := by
      have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hb3 3; norm_num at this; linarith
    have hbb3 : b ≤ b ^ 3 := le_self_pow₀ (by linarith) (by norm_num)
    have hArg : 2 + W1 + W2 + a + bb + c ≤ 27 * b ^ 3 := by linarith
    have hQ2 : Real.log (2 + W1 + W2 + a + bb + c) ≤ 6 * Real.log b := by
      calc _ ≤ Real.log (27 * b ^ 3) := Real.log_le_log hArg0 hArg
        _ = 3 * Real.log 3 + 3 * Real.log b := by
            rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow,
              show (27 : ℝ) = 3 ^ 3 by norm_num, Real.log_pow]; push_cast; ring
        _ ≤ _ := by linarith
    have hQ20 : 0 ≤ Real.log (2 + W1 + W2 + a + bb + c) := Real.log_nonneg (by linarith)
    have := mul_le_mul (mul_le_mul_of_nonneg_left hQ1 hK0) hQ2 hQ20 (by positivity)
    refine hlogKx.trans (this.trans (le_of_eq ?_))
    ring
  refine ⟨?_, hgG⟩
  rw [Real.log_mul (by positivity) hKx.ne', Real.log_mul (by norm_num) (pow_pos hrdpos g).ne', Real.log_pow]
  have hlY : Real.log b ≤ f * N * b * Real.log b := le_mul_of_one_le_left (by linarith) hfNb
  have e : (6 + 126 * K) * f * N * b * Real.log b =
      f * N * b * Real.log b + 5 * (f * N * b * Real.log b) + 126 * K * (f * N * b * Real.log b) := by ring
  rw [e]; linarith

end GlobalTheory.KerConjMean

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaDieudonneModFrobeniusDifferentials
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneHodgeFiltrationPerfectField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneHodgeFiltrationPerfectField
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu.Theory

theorem frobProj_omega_surjective {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p]
    (G : PDivGroup p k) : Function.Surjective (frobProj (p_eq_zero p k) G).omega := by
  letI := (frobRing (p_eq_zero p k)).toAlgebra
  intro t
  obtain ⟨x, rfl⟩ := (omega_baseChange_bijective G k (p_eq_zero p k)).2 t
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, (map_add _ a b).trans ((congrArg₂ (· + ·) ha hb).trans (map_add _ x y).symm)⟩
  | tmul r w =>
    refine ⟨(frobeniusEquiv k p).symm r • w, ?_⟩
    rw [liftSemi_tmul, map_smulₛₗ]
    congr 1
    show frobRing (p_eq_zero p k) _ = r
    rw [frobRing_apply, frobeniusEquiv_symm_pow_p]

theorem hodge_filtration : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k), (∀ x : ((G.cocycles × G.omega) ⧸ _root_.LinearMap.range (G.cob.prod (_root_.LinearMap.codRestrict G.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G.A i))).domRestrict G.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n)))))), (∃ m, T.red G (T.V G m) = x) ↔ x ∈ LinearMap.range G.rigOfOmega) ∧ (∀ m, T.red G (T.V G m) = 0 ↔ ∃ n, m = T.F G n) ∧ (∀ m, G.rigToLie (p_eq_zero p k) (T.red G m) = 0 ↔ ∃ n, m = T.V G n) ∧ Function.Injective G.rigOfOmega := by
  intro p _ T k _ _ _ G
  obtain ⟨-, hVinj, hVsm, -, -⟩ := GlobalTheory.T.dieudonneTheory_V_eq_verschiebung_injective p T k G
  obtain ⟨hbij, -, -⟩ := GlobalTheory.T.dieudonne_frobeniusTwist_bijective_relFrobenius p T.base k G
  obtain ⟨-, -, -, hver, -, -, -⟩ := rigExt_field_of_charP p k (p_eq_zero p k) G
  have key : ∀ m, SemiHom.rig (frobProj (p_eq_zero p k) G) (T.red G (T.V G m)) =
      rigExtMap (verschiebung (p_eq_zero p k) G) (T.red G m) := by
    intro m
    rw [← T.base.red_smap trivial trivial (frobProj (p_eq_zero p k) G), hVsm]
    rw [← SemiHom.ofHom_rig]
    exact T.base.red_smap trivial trivial (SemiHom.ofHom _) m
  have rinj : Function.Injective (frobProj (p_eq_zero p k) G).rig := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨m, rfl⟩ := T.base.red_surjective G trivial x
    rw [← T.base.red_smap trivial trivial (frobProj (p_eq_zero p k) G)] at hx
    have hx' := (T.base.red_eq_zero (frobTwist (p_eq_zero p k) G) trivial _).1 hx
    clear hx
    obtain ⟨n, hn⟩ := hx'
    obtain ⟨n', rfl⟩ := hbij.2 n
    have hm : m = p • n' := hbij.1 (by rw [hn, map_nsmul])
    exact (T.base.red_eq_zero G trivial m).2 ⟨n', hm⟩
  have osurj := frobProj_omega_surjective G
  have h1 : ∀ x : G.RigExt, (∃ m, T.red G (T.V G m) = x) ↔ x ∈ LinearMap.range G.rigOfOmega := by
    intro x
    constructor
    · rintro ⟨m, rfl⟩
      have hm : SemiHom.rig (frobProj (p_eq_zero p k) G) (T.red G (T.V G m)) ∈
          LinearMap.range (frobTwist (p_eq_zero p k) G).rigOfOmega := by
        rw [key, ← hver]; exact ⟨_, rfl⟩
      obtain ⟨w', hw'⟩ := hm
      obtain ⟨w, rfl⟩ := osurj w'
      exact ⟨w, rinj ((SemiHom.rig_rigOfOmega _ w).trans hw')⟩
    · rintro ⟨w, rfl⟩
      have hw : (frobTwist (p_eq_zero p k) G).rigOfOmega (SemiHom.omega (frobProj (p_eq_zero p k) G) w) ∈
          LinearMap.range (rigExtMap (verschiebung (p_eq_zero p k) G)) := by
        rw [hver]; exact ⟨_, rfl⟩
      obtain ⟨y, hy⟩ := hw
      obtain ⟨m, rfl⟩ := T.base.red_surjective G trivial y
      exact ⟨m, rinj ((key m).trans (hy.trans (SemiHom.rig_rigOfOmega _ w).symm))⟩
  have h2 : ∀ m, T.red G (T.V G m) = 0 ↔ ∃ n, m = T.F G n := by
    intro m
    refine (T.base.red_eq_zero G trivial _).trans ⟨fun ⟨n, hn⟩ => ⟨n, hVinj ?_⟩, fun ⟨n, hn⟩ => ⟨n, ?_⟩⟩
    · rw [hn]; exact (T.V_F G n).symm
    · rw [hn]; exact T.V_F G n
  refine ⟨h1, h2, fun m => ?_, G.rigOfOmega_injective_of_eq_zero (p_eq_zero p k)⟩
  rw [G.exact_rigOfOmega_rigToLie (p_eq_zero p k) (T.red G m)]
  constructor
  · intro hm
    obtain ⟨m', hm'⟩ := (h1 _).2 hm
    have h0 : T.red G (m - T.V G m') = 0 := by rw [map_sub, hm', sub_self]
    obtain ⟨n, hn⟩ := (T.base.red_eq_zero G trivial _).1 h0
    refine ⟨m' + T.F G n, ?_⟩
    rw [map_add (f := _), T.V_F G n, ← hn, add_sub_cancel]
  · rintro ⟨n, rfl⟩
    obtain ⟨w, hw⟩ := (h1 (T.red G (T.V G n))).1 ⟨n, rfl⟩
    exact ⟨w, hw⟩

end GlobalTheory.Dieu.Theory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneHodgeFiltrationPerfectFieldStatement
open GlobalTheory GlobalTheory.PDivGroup

theorem GlobalTheory.T.dieudonne_hodgeFiltration_perfectField :
    ∀ (p : ℕ) [Fact p.Prime] (T : GlobalTheory.Dieu.Theory p)
      (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k),
      (∀ x : G.RigExt, (∃ m, T.red G (T.V G m) = x) ↔ x ∈ LinearMap.range G.rigOfOmega) ∧
      (∀ m, T.red G (T.V G m) = 0 ↔ ∃ n, m = T.F G n) ∧
      (∀ m, G.rigToLie (GlobalTheory.Dieu.p_eq_zero p k) (T.red G m) = 0 ↔ ∃ n, m = T.V G n) ∧
      Function.Injective G.rigOfOmega :=
  @GlobalTheory.Dieu.Theory.hodge_filtration
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaDieudonneModFrobeniusDifferentials
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Dieu.Theory

variable {p : ℕ} [Fact p.Prime] (T : GlobalTheory.Dieu.Theory p)
  {k : Type} [Field k] [CharP k p] [PerfectRing k p]

def redVToRange (G : PDivGroup p k) : T.M G →+ LinearMap.range G.rigOfOmega :=
  AddMonoidHom.codRestrict ((T.red G).toAddMonoidHom.comp (T.V G).toAddMonoidHom)
    (LinearMap.range G.rigOfOmega) fun m =>
      ((GlobalTheory.T.dieudonne_hodgeFiltration_perfectField p T k G).1 (T.red G (T.V G m))).1 ⟨m, rfl⟩

def theta (G : PDivGroup p k) : T.M G →+ G.omega :=
  (LinearEquiv.ofInjective G.rigOfOmega (GlobalTheory.T.dieudonne_hodgeFiltration_perfectField p T k G).2.2.2).symm.toLinearMap.toAddMonoidHom.comp
    (T.redVToRange G)

theorem rigOfOmega_theta (G : PDivGroup p k) (m : T.M G) :
    G.rigOfOmega (T.theta G m) = T.red G (T.V G m) := by
  have inj := (GlobalTheory.T.dieudonne_hodgeFiltration_perfectField p T k G).2.2.2
  exact LinearEquiv.ofInjective_symm_apply G.rigOfOmega (h := inj) (T.redVToRange G m)

theorem theta_spec (G : PDivGroup p k) :
    (∀ m, G.rigOfOmega (T.theta G m) = T.red G (T.V G m)) ∧ Function.Surjective (T.theta G) ∧
      (∀ m, T.theta G m = 0 ↔ ∃ n, m = T.F G n) ∧
      (∀ (a : WittVector p k) (m : T.M G), T.theta G (WittVector.frobenius a • m) =
        WittVector.constantCoeff a • T.theta G m) ∧
      ∀ (H : PDivGroup p k) (f : G ⟶ H) (m : T.M H),
        T.theta G (T.map f m) = omegaMap G H f (T.theta H m) := by
  have hG := GlobalTheory.T.dieudonne_hodgeFiltration_perfectField p T k G
  have inj := hG.2.2.2
  refine ⟨T.rigOfOmega_theta G, fun w => ?_, fun m => ?_, fun a m => ?_, fun H f m => ?_⟩
  · obtain ⟨m, hm⟩ := (hG.1 (G.rigOfOmega w)).2 ⟨w, rfl⟩
    exact ⟨m, inj ((T.rigOfOmega_theta G m).trans hm)⟩
  · calc
      T.theta G m = 0 ↔ G.rigOfOmega (T.theta G m) = 0 :=
        ⟨fun h => (congrArg G.rigOfOmega h).trans (map_zero G.rigOfOmega),
          fun h => inj (h.trans (map_zero G.rigOfOmega).symm)⟩
      _ ↔ ∃ n, m = T.F G n := (congrArg (· = 0) (T.rigOfOmega_theta G m)).to_iff.trans (hG.2.1 m)
  · apply inj
    have hV : T.V G (WittVector.frobenius a • m) = a • T.V G m := by
      rw [(T.V G).map_smulₛₗ]
      change (WittVector.frobeniusEquiv p k).symm (WittVector.frobeniusEquiv p k a) • T.V G m = _
      rw [RingEquiv.symm_apply_apply]
    simpa only [T.rigOfOmega_theta, G.rigOfOmega.map_smul, hV] using!
      (T.red G).map_smulₛₗ a (T.V G m)
  · apply inj
    have hV := (GlobalTheory.T.dieudonneTheory_V_eq_verschiebung_injective p T k G).2.2.2.2 H f m
    have hred : T.red G (T.map f (T.V H m)) = rigExtMap f (T.red H (T.V H m)) :=
      T.base.red_map trivial trivial f (T.V H m)
    rw [T.rigOfOmega_theta, ← hV, hred, ← T.rigOfOmega_theta H m, rigExtMap_rigOfOmega]

end GlobalTheory.Dieu.Theory

theorem GlobalTheory.Dieu.theta_exists :
    ∀ (p : ℕ) [Fact p.Prime] (T : GlobalTheory.Dieu.Theory p) (k : Type)
      [Field k] [CharP k p] [PerfectRing k p],
      ∃ θ : ∀ G : PDivGroup p k, T.M G →+ G.omega, ∀ G : PDivGroup p k,
        (∀ m, G.rigOfOmega (θ G m) = T.red G (T.V G m)) ∧ Function.Surjective (θ G) ∧
        (∀ m, θ G m = 0 ↔ ∃ n, m = T.F G n) ∧
        (∀ (a : WittVector p k) (m : T.M G),
          θ G (WittVector.frobenius a • m) = WittVector.constantCoeff a • θ G m) ∧
        ∀ (H : PDivGroup p k) (f : G ⟶ H) (m : T.M H),
          θ G (T.map f m) = omegaMap G H f (θ H m) :=
  fun _ _ T _ _ _ _ => ⟨fun G => T.theta G, fun G => T.theta_spec G⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaDieudonneModFrobeniusDifferentialsStatement
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

theorem _root_.GlobalTheory.T.exists_theta_dieudonne_mod_frobenius_differentials :
    ∀ (p : ℕ) [Fact p.Prime] (T : GlobalTheory.Dieu.Theory p)
      (k : Type) [Field k] [CharP k p] [PerfectRing k p],
      ∃ θ : ∀ G : PDivGroup p k, T.M G →+ G.omega,
        ∀ G : PDivGroup p k,
          (∀ m, G.rigOfOmega (θ G m) = T.red G (T.V G m)) ∧
          Function.Surjective (θ G) ∧
          (∀ m, θ G m = 0 ↔ ∃ n, m = T.F G n) ∧
          (∀ (a : WittVector p k) m,
            θ G (WittVector.frobenius a • m) = WittVector.constantCoeff a • θ G m) ∧
          ∀ (H : PDivGroup p k) (f : G ⟶ H) (m : T.M H),
            θ G (T.map f m) = omegaMap G H f (θ H m) :=
  @GlobalTheory.Dieu.theta_exists
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TameKernelVectorUnitMulDilatedFlat
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TameKernelVectorUnitMulDilatedFlat
set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BaseCmp


open Classical in
theorem kerDat_twoStep {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} (hC : GlobalTheory.Hk3.Core R F)
    {i : Fin D.R.m} {ξ : Formalism.L2.Host.HChar D.host.E} {χ : (AE D)ˣ →* Circle} {ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ}
    {Q : Finset (Pl D.host.E)} {ω : WeilRep D i} {φ : WO (Vc D i) (Wc D i) → ℂ} (hK : KerDat R i ξ χ ξR Q ω φ)
    (hQ : ∃ t, Q ⊆ R.Q t) {eg eQ : AE D} {fg : WO (Vc D i) (Wc D i) → ℂ} (hg : IsIdemSum eg R.Pg) (hq : IsIdemSum eQ Q)
    (hfg : IsTypeVec R i eg fg) :
    IsThetaAt R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) (cA D eQ) (lattice₂ R i) 1 fg
      (fun x => if IsHalf (cA D eQ) x ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then
        omegaQ Q (Wc D i).rank ξR (-1) (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) else 0) φ := by
  obtain ⟨⟨hψ, -⟩, e, he, hTe⟩ := hK.vec
  have hSV := GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hC.lev.βV i))
  have hSW := GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hC.lev.βW i))
  obtain ⟨t, ht⟩ := hQ
  have hd : Disjoint R.Pg Q := Disjoint.mono_right ht (GlobalTheory.TwistPlaces.typePlaces_disjoint_twistPlaces R F hC t)
  have hsum : e = eg + eQ := by
    rw [← GlobalTheory.ExportSeries.idem_eq he, ← GlobalTheory.ExportSeries.idem_eq hg, ← GlobalTheory.ExportSeries.idem_eq hq]
    exact Finset.sum_union hd
  subst hsum
  have heg := GlobalTheory.PlaceVec.idemSum_mul_self hg
  have heQ := GlobalTheory.PlaceVec.idemSum_mul_self hq
  have hee := GlobalTheory.PlaceVec.idemSum_mul_self he
  have hgQ : eg * eQ = 0 := by
    refine GlobalTheory.PlaceVec.natCast_mul_eq_zero 2 _ two_pos ?_
    push_cast
    linear_combination hee - heg - heQ
  have hcg : cA D eg * cA D eg = cA D eg := by rw [← map_mul, heg]
  have hcQ : cA D eQ * cA D eQ = cA D eQ := by rw [← map_mul, heQ]
  have hQg : cA D eQ * cA D eg = 0 := by rw [← map_mul, mul_comm, hgQ, map_zero]
  have hgQ' : cA D eg * cA D eQ = 0 := by rw [mul_comm, hQg]
  have hΛ : ∀ a : AE D, a * a = a → ∀ u ∈ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True),
      a • u ∈ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) :=
    fun a ha u hu => GlobalTheory.PlaceModelSum.idem_smul_latO ha hu
  have hinfg : infPart D (cA D eg) = 0 := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart hg)
  have hinfQ : infPart D (cA D eQ) = 0 := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart hq)
  have hSBg := GlobalTheory.PlaceVec.isSBHalf_of_red (GlobalTheory.PlaceVec.selfDual_isFullLattice _ _ hSV) (GlobalTheory.PlaceVec.selfDual_isFullLattice _ _ hSW) hinfg (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i))
    (GlobalTheory.PlaceVec.frMapAdj_add _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_up _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_down _ _ _ _)
    R.Pg (fun y => omegaK R.Pg y) fun y y' h => GlobalTheory.PlaceVec.omegaK_congr R.Pg h
  have hSBQ := GlobalTheory.PlaceVec.isSBHalf_of_red (GlobalTheory.PlaceVec.selfDual_isFullLattice _ _ hSV) (GlobalTheory.PlaceVec.selfDual_isFullLattice _ _ hSW) hinfQ (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i))
    (GlobalTheory.PlaceVec.frMapAdj_add _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_up _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_down _ _ _ _)
    Q (fun y => omegaQ Q (Wc D i).rank ξR (-1) y) fun y y' h => GlobalTheory.PlaceVec.omegaQ_congr _ _ _ _ h
  obtain ⟨⟨Te, hTe1⟩, hTe2⟩ := hTe
  have hc : cA D (eg + eQ) = cA D eQ + cA D eg := by rw [map_add (f := _), add_comm]
  have hc' : cA D (eg + eQ) = cA D eg + cA D eQ := map_add _ _ _
  have hm1 := GlobalTheory.TwoStepModel.isPlaceModel_comp_tensorHalf hcQ hcg hQg hΛ hSBg (hc ▸ hTe1)
  have hm2 := GlobalTheory.ExportSeries.isPlaceModel_comp_restrictHalf hcg hcQ hgQ' hΛ (hc' ▸ hTe1)
  have hbase := hfg.2 _ hm2
  simp only [LinearMap.comp_apply] at hbase
  rw [← hbase] at hm1
  refine ⟨⟨_, hm1⟩, fun T' hT' => ?_⟩
  rw [hTe2 Te hTe1, GlobalTheory.TwoStepModel.datum_eq_tensorHalf (R.βV i) (R.βW i) hg hq hd he ξR]
  exact GlobalTheory.PlaceVec.placeModel_unique hψ hSV hSW hcQ hinfQ hm1 hT' hSBQ

end GlobalTheory.BaseCmp

namespace GlobalTheory.BaseCmp


open GlobalTheory.ChainOnto in
theorem kerDat_xiR_ne : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (ξ : Formalism.L2.Host.HChar D.host.E) (χ : (AE D)ˣ →* Circle)
    (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (ω : WeilRep D i) (φ : WO (Vc D i) (Wc D i) → ℂ),
    KerDat R i ξ χ ξR Q ω φ → ∀ PP ∈ Q, ξR PP ≠ 1 := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F _ i ξ χ ξR Q ω φ hK
  intro PP hP h1
  refine (hK.ram PP).2 (Or.inl hP) fun x hx => ?_
  have hc := hK.res PP hP
  rw [h1] at hc
  have hU : IsOpen {z : PP.adicCompletion D.host.E | Valued.v (z - x) < 1} :=
    (GlobalTheory.ChainOnto.TameRes.isOpen_ltOne PP).preimage (continuous_sub_right _)
  obtain ⟨k, hk⟩ := (HeightOneSpectrum.denseRange_algebraMap D.host.E PP).exists_mem_open hU ⟨x, by simp⟩
  have hk' : Valued.v (algebraMap D.host.E (PP.adicCompletion D.host.E) k - x) < Valued.v (x : PP.adicCompletion D.host.E) := by
    rw [hx]; exact hk
  have hv : Valued.v (algebraMap D.host.E (PP.adicCompletion D.host.E) k) = 1 := by
    rw [Valuation.map_eq_of_sub_lt _ hk']; exact hx
  have hv1 : PP.valuation D.host.E k = 1 := by rw [← GlobalTheory.ChainOnto.TameRes.val_alg]; exact hv
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at hv1
  obtain ⟨a, s, h⟩ := PP.exists_primeCompl_mul_eq_of_integer k hv1.le
  have hs : (s : 𝓞 D.host.E) ∉ PP.asIdeal := s.2
  have hsv := GlobalTheory.ChainOnto.TameRes.valuation_eq_one_of_not_mem PP _ hs
  have hav : PP.valuation D.host.E (algebraMap (𝓞 D.host.E) D.host.E a) = 1 := by
    rw [← h, map_mul, hv1, hsv, one_mul]
  have ha : a ∉ PP.asIdeal := fun hm =>
    absurd hav (ne_of_lt ((PP.valuation_lt_one_iff_mem (K := D.host.E) a).mpr hm))
  haveI : PP.asIdeal.IsMaximal := PP.isMaximal
  have key : ∀ (b : 𝓞 D.host.E), b ∉ PP.asIdeal → ∀ y : D.host.Eˣ, (y : D.host.E) = b → ξ.locK PP y = 1 := by
    intro b hb y hy
    have hms : (Ideal.Quotient.mk PP.asIdeal b : kP PP) ≠ 0 := by
      rw [Ne, Ideal.Quotient.eq_zero_iff_mem]; exact hb
    obtain ⟨b', hb'⟩ := Ideal.Quotient.exists_inv hms
    exact (hc b y (Units.mkOfMulEqOne _ b' hb') hy rfl).symm
  have hs0 : algebraMap (𝓞 D.host.E) D.host.E s ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hsv; exact zero_ne_one hsv
  have ha0 : algebraMap (𝓞 D.host.E) D.host.E a ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hav; exact zero_ne_one hav
  have hkk : Units.mk0 k hk0 * Units.mk0 _ hs0 = Units.mk0 _ ha0 := Units.ext h
  have hk1 : ξ.locK PP (Units.mk0 k hk0) = 1 := by
    have := congrArg (ξ.locK PP) hkk
    rwa [map_mul, key _ hs (Units.mk0 _ hs0) rfl, key _ ha (Units.mk0 _ ha0) rfl, mul_one] at this
  set y := Formalism.L2.Host.atFin PP (Units.mk0 k hk0) with hy
  have hyv : (y : PP.adicCompletion D.host.E) = algebraMap D.host.E (PP.adicCompletion D.host.E) k := rfl
  have ht := hK.tame PP (y * x⁻¹) (by
    unfold Formalism.L2.Host.IsUnitAt at *
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hyv, hv, hx, inv_one, mul_one]) (by
    have e : ((y * x⁻¹ : (PP.adicCompletion D.host.E)ˣ) : PP.adicCompletion D.host.E) - 1 =
        (algebraMap D.host.E (PP.adicCompletion D.host.E) k - x) * (x : PP.adicCompletion D.host.E)⁻¹ := by
      rw [Units.val_mul, Units.val_inv_eq_inv_val, hyv, sub_mul, mul_inv_cancel₀ x.ne_zero]
    unfold Formalism.L2.Host.IsUnitAt at hx
    rw [e, map_mul, map_inv₀, hx, inv_one, mul_one]
    have hlt : Valued.v (algebraMap D.host.E (PP.adicCompletion D.host.E) k - x) < 1 := hk
    generalize Valued.v (algebraMap D.host.E (PP.adicCompletion D.host.E) k - x) = z at hlt
    rcases eq_or_ne z 0 with rfl | hz
    · exact zero_le'
    · rw [← WithZero.exp_log hz] at hlt ⊢
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
      rw [WithZero.exp_le_exp]
      push_cast
      omega)
  have hk2 : ξ.loc PP y = 1 := hk1
  rw [map_mul, hk2, one_mul, map_inv, inv_eq_one] at ht
  exact ht

end GlobalTheory.BaseCmp

namespace GlobalTheory.BaseCmp


open Classical in
theorem liftKer_of_ne : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F →
    QGuard R → ∀ (i : Fin D.R.m), VStd D i → ∀ (ξ : Formalism.L2.Host.HChar D.host.E) (χ : (AE D)ˣ →* Circle)
    (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (ω : WeilRep D i) (φ : WO (Vc D i) (Wc D i) → ℂ),
    KerDat R i ξ χ ξR Q ω φ → (∃ t, Q ⊆ R.Q t) → ∀ N : ℕ, N ≠ 0 → (∀ PP ∈ Q, (N : 𝓞 D.host.E) ∈ PP.asIdeal) →
    ∀ (eg eQ : AE D) (fg : WO (Vc D i) (Wc D i) → ℂ), IsIdemSum eg R.Pg → IsIdemSum eQ Q → IsTypeVec R i eg fg →
    ∀ ϖ : 𝓞 D.host.E, ϖ ≠ 0 → (∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) →
      ∃ Gc : ℂ, UnitOff N Gc ∧ IsSBHalf eQ (lattice₂ R i) (fun x => Gc * flatDat R i Q ξR eQ (dil i (ϖ : D.host.E) x)) ∧
        ∀ Tm, IsModel R i eQ fg Tm → φ = Tm (fun x => Gc * flatDat R i Q ξR eQ (dil i (ϖ : D.host.E) x)) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC hG i hV ξ χ ξR Q ω φ hK hQ N hN hNQ eg eQ fg hg hq hfg ϖ hϖ0 hϖ
  have hθ := kerDat_twoStep hC hK hQ hg hq hfg
  obtain ⟨Y, a, Gc, hU, hY, hΦ, hS⟩ := GlobalTheory.T.lift_datum_conjugate_half_finite_fourier_sum D G Pl0 T0 A Ks R F hC hG i hV ξR Q hQ
    (kerDat_xiR_ne D G Pl0 T0 A Ks R F hC i ξ χ ξR Q ω φ hK) N hN hNQ eQ hq ϖ hϖ0 hϖ
  refine ⟨Gc, hU, GlobalTheory.T.dilatedFlatDatum_isSBHalf_tameKernel D G Pl0 T0 A Ks R F hC hG i hV ξR Q hQ eQ hq ϖ hϖ0 hϖ Gc, fun Tm hTm => ?_⟩
  have h1 := GlobalTheory.DatumFourier.thetaAt_eq_sum (fun q : Y => q.1) (fun q : Y => a q.1) hθ
    (fun q => by rw [GlobalTheory.LatVac.cA_cA]; exact hY q.1 q.2)
    (fun t => by rw [hΦ t]; congr 1; exact (Finset.sum_coe_sort Y fun y => a y * R.ψ (symplO (Vc D i) (Wc D i) t y)).symm)
  have h2 : (fun x => Gc * flatDat R i Q ξR eQ (dil i (ϖ : D.host.E) x)) =
      ∑ y ∈ Y, a y • fun t => halfInd eQ (lattice₂ R i) (t + y) := by
    funext t
    rw [← hS t, Finset.sum_apply]
    rfl
  have hvac : Tm (halfInd eQ (lattice₂ R i)) = fg := by simpa using hTm.vac
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h1, h2, map_sum, ← Finset.sum_coe_sort Y]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_smul, hTm.trans _ (GlobalTheory.isSBHalf_halfInd eQ (lattice₂ R i)) _ (hY q.1 q.2), hvac]

end GlobalTheory.BaseCmp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TameKernelVectorUnitMulDilatedFlatStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tameKernel_vector_unit_mul_dilated_flat : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F →
    QGuard R → ∀ (i : Fin D.R.m), VStd D i → ∀ (ξ : Formalism.L2.Host.HChar D.host.E) (χ : (AE D)ˣ →* Circle)
    (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (ω : WeilRep D i) (φ : WO (Vc D i) (Wc D i) → ℂ),
    KerDat R i ξ χ ξR Q ω φ → (∃ t, Q ⊆ R.Q t) → ∀ N : ℕ, N ≠ 0 → (∀ PP ∈ Q, (N : 𝓞 D.host.E) ∈ PP.asIdeal) →
    ∀ (eg eQ : AE D) (fg : WO (Vc D i) (Wc D i) → ℂ), IsIdemSum eg R.Pg → IsIdemSum eQ Q → IsTypeVec R i eg fg →
    ∀ ϖ : 𝓞 D.host.E, ϖ ≠ 0 → (∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) →
      ∃ Gc : ℂ, UnitOff N Gc ∧ IsSBHalf eQ (lattice₂ R i) (fun x => Gc * flatDat R i Q ξR eQ (dil i (ϖ : D.host.E) x)) ∧
        ∀ Tm, IsModel R i eQ fg Tm → φ = Tm (fun x => Gc * flatDat R i Q ξR eQ (dil i (ϖ : D.host.E) x)) := by
  first | exact @GlobalTheory.BaseCmp.liftKer_of_ne | exact GlobalTheory.BaseCmp.liftKer_of_ne | (intros; apply GlobalTheory.BaseCmp.liftKer_of_ne <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticLevelExtendsNoetherianNormalDomain
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticLevelExtendsNoetherianNormalDomain
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.SympLevelExt

theorem lbIso_pull_comp {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (a : Y ⟶ X) (b : Z ⟶ Y) :
    LBIso (L.pull (b ≫ a)) ((L.pull a).pull b) :=
  LBIso.symm (LBIso.chartPull (chartPullLinComb L a (fun _ : PUnit => b)
      (fun _ => b ≫ a) (fun _ => 1) (𝟙 _) fun _ => (Category.id_comp _).symm)
      (chartPullId _) (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hL _)))

theorem map_linComb {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {T : Over S}
    {T' : Over S'} (ρ : (T ⟶ A) →* (T' ⟶ A')) {n : ℕ} (y : Fin n → (T ⟶ A)) (a : Fin n → ℕ) :
    ρ (linComb y a) = linComb (fun i => ρ (y i)) a := by
  unfold linComb
  rw [map_list_prod, List.map_ofFn]
  congr 1
  refine congrArg List.ofFn (funext fun i => ?_)
  exact map_pow ρ (y i) (a i)

theorem dense_of_bot_mem {R : Type} [CommRing R] [IsDomain R] (D : Set (Sp R))
    (hD : (⊥ : PrimeSpectrum R) ∈ D) : Dense D := by
  intro p
  have hs : (⊥ : PrimeSpectrum R) ⤳ p := (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
  exact closure_mono (Set.singleton_subset_iff.2 hD) (specializes_iff_mem_closure.1 hs)

theorem extend_torsion {R F : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    [Field F] [Algebra R F] [IsFractionRing R F] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    [IsProper G.hom] (n : ℕ) (hn : IsUnit (n : R))
    (x : Over.mk ((baseOver (Sp F)).hom ≫ spMap (algebraMap R F)) ⟶ G) (hx : x ^ n = 1) :
    ∃ σ : baseOver (Sp R) ⟶ G, σ ^ n = 1 ∧ spMap (algebraMap R F) ≫ σ.left = x.left := by
  have hn' : IsUnit (n : Γ(Sp R, ⊤)) := by
    have := hn.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    rwa [map_natCast] at this
  have hT : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp R) := fun p => by
    refine ⟨inferInstance, ?_⟩
    have : (PrimeSpectrum.asIdeal p).IsPrime := PrimeSpectrum.isPrime p
    have h := StructureSheaf.IsLocalization.to_stalk R p
    exact @isIntegrallyClosed_of_isLocalization R ((Spec.structureSheaf R).presheaf.stalk p) _ _ (_) _ _
      (PrimeSpectrum.asIdeal p).primeCompl (Ideal.primeCompl_le_nonZeroDivisors _) h
  have j₁ : IsPreimmersion (spMap (algebraMap R F)) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have j₂ : Flat (spMap (algebraMap R F)) :=
    (HasRingHomProperty.Spec_iff (P := @Flat)).2 (RingHom.flat_algebraMap_iff.2 (IsLocalization.flat F (nonZeroDivisors R)))
  have j₃ : IsDominant (spMap (algebraMap R F)) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
    intro a ha
    have : a = 0 := IsFractionRing.injective R F (ha.trans (map_zero _).symm)
    rw [this]; exact Ideal.zero_mem _)⟩
  obtain ⟨σ, hσ₁, hσ₂⟩ := exists_section_of_pow_eq_one hT (spMap (algebraMap R F)) G n hn' _ x hx (𝟙 _)
    (by simp)
  let σ' : baseOver (Sp R) ⟶ G := Over.homMk σ (by simpa using hσ₁)
  have hσ : spMap (algebraMap R F) ≫ σ'.left = x.left := by
    show spMap (algebraMap R F) ≫ σ = x.left
    simpa using hσ₂
  refine ⟨σ', ?_, hσ⟩
  let U : Over.mk ((baseOver (Sp F)).hom ≫ spMap (algebraMap R F)) ⟶ baseOver (Sp R) :=
    Over.homMk (spMap (algebraMap R F)) (by simp)
  have hU : U ≫ σ' = x := Over.OverMorphism.ext hσ
  have e : U ≫ σ' ^ n = U ≫ 1 := by rw [MonObj.comp_pow, MonObj.comp_one, hU, hx]
  exact over_points_ext_of_injective _ G R F (algebraMap R F) (IsFractionRing.injective R F) _ _ _
    (congrArg (fun q => q.left) e)

end GlobalTheory.SympLevelExt

namespace GlobalTheory.SympLevelExt

theorem generic_basis {R F : Type} [CommRing R] [IsDomain R] [Field F] [Algebra R F]
    {Q : PolAV (Sp F)} (G : Over (Sp R)) [GrpObj G] (φ : Q.A.left ⟶ G.left)
    (hp : IsGrpPullback Q.A G (spMap (algebraMap R F)) φ) (k : ℕ) [NeZero k] (ze₀ : Γ(Sp F, ⊤)ˣ)
    (lev₀ : Out.Level Q k ze₀) (y : Fin (2 * Q.g) → (baseOver (Sp R) ⟶ G))
    (hy : ∀ i, (lev₀.pt i).left ≫ φ = spMap (algebraMap R F) ≫ (y i).left)
    (z : Over.mk (spMap (algebraMap F (AlgebraicClosure F)) ≫ spMap (algebraMap R F)) ⟶ G) (hz : z ^ k = 1) :
    ∃! c : Fin (2 * Q.g) → ZMod k,
      linComb (fun i => (Over.homMk (spMap (algebraMap F (AlgebraicClosure F)) ≫ spMap (algebraMap R F))
        (by simp) : Over.mk (spMap (algebraMap F (AlgebraicClosure F)) ≫ spMap (algebraMap R F)) ⟶
          baseOver (Sp R)) ≫ y i) (fun i => (c i).val) = z := by
  let s : Sp (AlgebraicClosure F) ⟶ Sp F := spMap (algebraMap F (AlgebraicClosure F))
  let T : Over (Sp F) := Over.mk s
  let ρ := pushHom hp T
  have hinj : Function.Injective ρ := fun a b hab => by
    apply Over.OverMorphism.ext
    apply hp.1.hom_ext
    · exact congrArg (fun q => q.left) hab
    · rw [Over.w a, Over.w b]
  have hsurj : ∀ w : Over.mk (T.hom ≫ spMap (algebraMap R F)) ⟶ G, ∃ a, ρ a = w := fun w =>
    ⟨Over.homMk (hp.1.lift w.left T.hom (Over.w w)) (hp.1.lift_snd _ _ _),
      Over.OverMorphism.ext (hp.1.lift_fst _ _ _)⟩
  have hcomp : ∀ i, ρ ((Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp F)) ≫ lev₀.pt i) =
      (Over.homMk (s ≫ spMap (algebraMap R F)) (by simp) :
        Over.mk (s ≫ spMap (algebraMap R F)) ⟶ baseOver (Sp R)) ≫ y i := fun i => by
    apply Over.OverMorphism.ext
    show (s ≫ (lev₀.pt i).left) ≫ φ = (s ≫ spMap (algebraMap R F)) ≫ (y i).left
    rw [Category.assoc, hy, Category.assoc]
  have hlin : ∀ d : Fin (2 * Q.g) → ℕ,
      ρ (linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp F)) ≫ lev₀.pt i) d) =
      linComb (fun i => (Over.homMk (s ≫ spMap (algebraMap R F)) (by simp) :
        Over.mk (s ≫ spMap (algebraMap R F)) ⟶ baseOver (Sp R)) ≫ y i) d := fun d => by
    rw [map_linComb]
    simp only [hcomp]
  obtain ⟨a, rfl⟩ := hsurj z
  have ha : a ^ k = 1 := hinj (by rw [map_pow, hz, map_one])
  obtain ⟨c, hc⟩ := lev₀.span (AlgebraicClosure F) s a ha
  refine ⟨fun i => ((c i : ℕ) : ZMod k), ?_, ?_⟩
  · show linComb _ (fun i => (((c i : ℕ) : ZMod k)).val) = ρ a
    simp only [ZMod.val_natCast_of_lt (Fin.is_lt _)]
    rw [← hlin, hc]
  · intro c' hc'
    have e : ρ (linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp F)) ≫ lev₀.pt i)
        (fun i => ((⟨(c' i).val, ZMod.val_lt (c' i)⟩ : Fin k) : ℕ))) = ρ a := by
      rw [hlin]; exact hc'
    have e' := lev₀.indep (AlgebraicClosure F) s _ c ((hinj e).trans hc.symm)
    funext i
    have := congrArg (fun f => ((f i : ℕ) : ZMod k)) e'
    simpa using this

end GlobalTheory.SympLevelExt

namespace GlobalTheory.SympLevelExt

theorem level_extends : ∀ {R₁ : Type} [CommRing R₁] (P₁ : PolAV (Sp R₁)) (R F : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Field F] [Algebra R F] [IsFractionRing R F] (h : R₁ →+* R) (Q : PolAV (Sp F)) (φ : Q.A.left ⟶ P₁.A.left) (K : ℕ) (ze : Rˣ), 0 < K → IsUnit (K : R) → Q.g = P₁.g → IsGrpPullback Q.A P₁.A (spMap ((algebraMap R F).comp h)) φ → LBIso Q.L (P₁.L.pull φ) → Nonempty (Out.Level Q K (unitOn (Units.map (algebraMap R F).toMonoidHom ze))) → ∃ (P : PolAV (Sp R)) (ψ : P.A.left ⟶ P₁.A.left), P.g = P₁.g ∧ IsGrpPullback P.A P₁.A (spMap h) ψ ∧ LBIso P.L (P₁.L.pull ψ) ∧ Nonempty (Out.Level P K (unitOn ze)) := by
  intro R₁ _ P₁ R F _ _ _ _ _ _ _ h Q φ K ze hK hKu hg hpb hQL hlev
  obtain ⟨lev₀⟩ := hlev
  cases Q with
  | mk QA QisAb Qg Qsm QL QisLB Qrig Qsym Qamp Qkt =>
  dsimp only at hg
  subst hg
  have hL := abelianSchemeLaws_all.1
  haveI : NeZero K := ⟨hK.ne'⟩
  let j := spMap (algebraMap R F)
  let P : PolAV (Sp R) :=
    { A := (Over.pullback (spMap h)).obj P₁.A
      isAb := TLinPf.isAb_pullback (spMap h) P₁.A P₁.isAb
      g := P₁.g
      smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
        (isGrpPullback_pullback P₁.A (spMap h)).1 P₁.smoothDim
      L := P₁.L.pull (pullback.fst P₁.A.hom (spMap h))
      isLB := pull_isLB P₁.isLB _
      rigid := PolBaseChange.rigidified_pull (isGrpPullback_pullback P₁.A (spMap h)) P₁.rigid
      sym := PolBaseChange.sym_pull (isGrpPullback_pullback P₁.A (spMap h)) P₁.sym
      ample := by
        haveI := P₁.isAb.proper
        exact AmpleBaseChange.relAmple_of_isPullback P₁.isLB P₁.ample (IsPullback.of_hasPullback P₁.A.hom (spMap h))
      ktriv := by
        obtain ⟨w, hw⟩ := PolBaseChange.lbIso_refl (pull_isLB P₁.isLB (pullback.fst P₁.A.hom (spMap h)))
        exact kTriv_pull (isGrpPullback_pullback P₁.A (spMap h)) P₁.isLB (pull_isLB P₁.isLB _) ((isGen_iff w).1 hw) P₁.ktriv }
  let ψ : P.A.left ⟶ P₁.A.left := pullback.fst P₁.A.hom (spMap h)
  have hψ : IsGrpPullback P.A P₁.A (spMap h) ψ := isGrpPullback_pullback P₁.A (spMap h)
  have hc : spMap ((algebraMap R F).comp h) = j ≫ spMap h := by
    simp only [spMap, j, CommRingCat.ofHom_comp, Spec.map_comp]
  have hw : φ ≫ P₁.A.hom = (QA.hom ≫ j) ≫ spMap h := by rw [hpb.1.w, hc, Category.assoc]
  let φ' : QA.left ⟶ P.A.left := hψ.1.lift φ (QA.hom ≫ j) hw
  have e₁ : φ' ≫ ψ = φ := hψ.1.lift_fst _ _ _
  have e₂ : φ' ≫ P.A.hom = QA.hom ≫ j := hψ.1.lift_snd _ _ _
  have hpb' : IsGrpPullback QA P.A j φ' := hψ.cancel (by rw [e₁, ← hc]; exact hpb) e₂
  have hQL' : LBIso QL (P.L.pull φ') := by
    refine LBIso.trans QisLB (pull_isLB P₁.isLB _) (pull_isLB P.isLB _) hQL ?_
    have := lbIso_pull_comp P₁.isLB ψ φ'
    rw [e₁] at this
    exact this
  have hP : IsProper P.A.hom := P.isAb.proper
  have := P.isAb.comm
  choose y hy₁ hy₂ using fun i : Fin (2 * P₁.g) =>
    extend_torsion (R := R) (F := F) P.A K hKu (pushHom hpb' (baseOver (Sp F)) (lev₀.pt i))
      (by rw [← map_pow, lev₀.torsion, map_one])
  have hy : ∀ i, (lev₀.pt i).left ≫ φ' = j ≫ (y i).left := fun i => (hy₂ i).symm
  have hKu' : IsUnit (K : Γ(Sp R, ⊤)) := by
    have := hKu.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    rwa [map_natCast] at this
  let x : Sp (AlgebraicClosure F) ⟶ Sp R := spMap (algebraMap F (AlgebraicClosure F)) ≫ j
  have hx : (⊥ : PrimeSpectrum R) ∈ Set.range x := by
    obtain ⟨w⟩ : Nonempty (Sp (AlgebraicClosure F)) := inferInstance
    refine ⟨w, ?_⟩
    apply PrimeSpectrum.ext
    show Ideal.comap (algebraMap R F) (Ideal.comap (algebraMap F (AlgebraicClosure F)) (PrimeSpectrum.asIdeal w)) = ⊥
    rw [@Ideal.eq_bot_of_prime _ _ (PrimeSpectrum.asIdeal w) (PrimeSpectrum.isPrime w),
      Ideal.comap_bot_of_injective _ (algebraMap F (AlgebraicClosure F)).injective,
      Ideal.comap_bot_of_injective _ (IsFractionRing.injective R F)]
  have hbasis := torsion_basis_of_dense (Sp R) P.A K (2 * P₁.g) y (Set.range x) P.isAb hK hKu' hy₁
    (dense_of_bot_mem _ hx) (fun p hp => ⟨AlgebraicClosure F, inferInstance, inferInstance, x, hp,
      fun z hz => generic_basis (Q := ⟨QA, QisAb, P₁.g, Qsm, QL, QisLB, Qrig, Qsym, Qamp, Qkt⟩) P.A φ' hpb' K _ lev₀ y hy z hz⟩)
  have hind : ∀ (F' : Type) [Field F'] [IsAlgClosed F'] (s : Spec (CommRingCat.of F') ⟶ Sp R)
      (c c' : Fin (2 * P.g) → Fin K),
      linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp R)) ≫ y i) (fun i => (c i : ℕ)) =
        linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp R)) ≫ y i) (fun i => (c' i : ℕ)) →
      c = c' := by
    intro F' _ _ s c c' hcc
    obtain ⟨d, -, hd⟩ := hbasis F' s
      (linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp R)) ≫ y i) (fun i => (c i : ℕ)))
      (DenseBasis.linComb_pow_eq_one _ (fun i => by rw [← MonObj.comp_pow, hy₁, MonObj.comp_one]) _)
    have h₁ := hd (fun i => ((c i : ℕ) : ZMod K)) (by simp only [ZMod.val_natCast_of_lt (Fin.is_lt _)])
    have h₂ := hd (fun i => ((c' i : ℕ) : ZMod K)) (by simp only [ZMod.val_natCast_of_lt (Fin.is_lt _)]; exact hcc.symm)
    funext i
    apply Fin.ext
    have := congrArg (fun f => (f i).val) (h₁.trans h₂.symm)
    simpa only [ZMod.val_natCast_of_lt (Fin.is_lt _)] using this
  obtain ⟨lev, -⟩ := level_of_generic_of_indep hL R F P ⟨QA, QisAb, P₁.g, Qsm, QL, QisLB, Qrig, Qsym, Qamp, Qkt⟩ φ'
    hpb' hQL' rfl K ze _ hKu rfl lev₀ y (fun i₀ i hi => by
      obtain rfl : i₀ = i := Fin.ext hi
      exact hy i₀) hind
  exact ⟨P, ψ, rfl, hψ, GlobalTheory.PolBaseChange.lbIso_refl P.isLB, ⟨lev⟩⟩

end GlobalTheory.SympLevelExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticLevelExtendsNoetherianNormalDomainStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplecticLevel_extends_noetherian_normalDomain : ∀ {R₁ : Type} [CommRing R₁] (P₁ : PolAV (Sp R₁)) (R F : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Field F] [Algebra R F] [IsFractionRing R F] (h : R₁ →+* R) (Q : PolAV (Sp F)) (φ : Q.A.left ⟶ P₁.A.left) (K : ℕ) (ze : Rˣ), 0 < K → IsUnit (K : R) → Q.g = P₁.g → IsGrpPullback Q.A P₁.A (spMap ((algebraMap R F).comp h)) φ → LBIso Q.L (P₁.L.pull φ) → Nonempty (Out.Level Q K (unitOn (Units.map (algebraMap R F).toMonoidHom ze))) → ∃ (P : PolAV (Sp R)) (ψ : P.A.left ⟶ P₁.A.left), P.g = P₁.g ∧ IsGrpPullback P.A P₁.A (spMap h) ψ ∧ LBIso P.L (P₁.L.pull ψ) ∧ Nonempty (Out.Level P K (unitOn ze)) := by
  first | exact @GlobalTheory.SympLevelExt.level_extends | exact GlobalTheory.SympLevelExt.level_extends | (intros; apply GlobalTheory.SympLevelExt.level_extends <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDeRhamStructureOfCubeDualPoincare
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDeRhamStructureOfCubeDualPoincare
namespace GlobalTheory

theorem abelianDeRham_of_hodge_cube_dual_poincare :
    GlobalTheory.Published.AbelianHodgeDeRham → GlobalTheory.Published.CubeTheorem → GlobalTheory.Published.DualAbelianScheme →
      GlobalTheory.Published.PoincareDeRhamDuality → GlobalTheory.Published.AbelianDeRham :=
  by
    intro hH hC hD hP
    obtain ⟨⟨hfree, hhodge, hbc⟩, hcrys⟩ :=
      GlobalTheory.T.crystallineDeRham_abelianStructure_of_statements
        GlobalTheory.SmoothLift.crystallineSmoothLift_of_relations hH
    have hF : GlobalTheory.Published.AbelianDeRham.Free :=
      GlobalTheory.AbelianPrim.abelianDeRham_free hfree
    exact ⟨hF, hhodge, hbc,
      GlobalTheory.Published.AbelianDeRham.rigid_of_free_of_crystallineDeRham hF hcrys,
      GlobalTheory.T.abelianDeRham_poincareDuality_of_cube_dual hC hD hP hF⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDeRhamStructureOfCubeDualPoincareStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianSchemeDeRhamStructure_of_cube_dual_poincare : GlobalTheory.Published.AbelianHodgeDeRham → GlobalTheory.Published.CubeTheorem → GlobalTheory.Published.DualAbelianScheme → GlobalTheory.Published.PoincareDeRhamDuality → GlobalTheory.Published.AbelianDeRham := by
  first | exact @GlobalTheory.abelianDeRham_of_hodge_cube_dual_poincare | exact GlobalTheory.abelianDeRham_of_hodge_cube_dual_poincare | (intros; apply GlobalTheory.abelianDeRham_of_hodge_cube_dual_poincare <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBoundFittedIdentity
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField

namespace GlobalTheory.BigTop.Fun.ThbTie

theorem sqRank_half {D : D7} (ij : Sq D) : sqRank D ij / 2 = GlobalTheory.FunObj.SqNum.halfRank D ij.1 ij.2 := by
  unfold sqRank GlobalTheory.FunObj.SqNum.halfRank GlobalTheory.ChiGrid.rankV
  congr 1
  ring

theorem htLe_nonneg {K : Type} [Field K] [NumberField K] [StarRing K] {g : Formalism.PairingDivisionLocalBalance.Pl K → ℤ} {z : K} {B : ℝ}
    (h : Formalism.PairingDivisionLocalBalance.HtLe g z B) : 0 ≤ B :=
  (finsum_nonneg fun w => mul_nonneg (div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)) (abs_nonneg _)).trans h.2

theorem htLe_one_zero {K : Type} [Field K] [NumberField K] [StarRing K] {B : ℝ} (hB : 0 ≤ B) :
    Formalism.PairingDivisionLocalBalance.HtLe (fun _ => (0 : ℤ)) (1 : K) B := by
  have e : (fun w : Formalism.PairingDivisionLocalBalance.Pl K => Formalism.DivisionValues.lw w * |((Formalism.DivisionValues.vw w (1 : K) + 0 : ℤ) : ℝ)|) = fun _ => 0 := by
    funext w
    simp [Formalism.DivisionValues.ValuationRepresentative.vw_one]
  refine ⟨?_, ?_⟩
  · rw [e]
    simp
  · rw [e, finsum_zero]
    exact hB

end GlobalTheory.BigTop.Fun.ThbTie


end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralityFittedIdentity
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField
open Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts

namespace GlobalTheory.BigTop.Fun.IntTie

theorem gBig_dep {Q : GP} (h : GBig @Q) :
    GBig fun {D} {T} {Lc} {sc} G μ₀ C x b => 1 ≤ sc.cDep ∧ sc.cDep ≤ C ∧ @Q D T Lc sc G μ₀ C x b := by
  obtain ⟨CF0, h⟩ := h
  refine ⟨max CF0 1, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x0, h⟩ := h ε CF (le_of_max_le_left hCF)
  exact ⟨max C0 CF, x0, fun C hC D large₂ he hx hR T Lc μ hL G =>
    ⟨le_of_max_le_right hCF, le_of_max_le_right hC, h C (le_of_max_le_left hC) D large₂ he hx hR T Lc μ hL G⟩⟩

theorem gBig_and {Q Q' : GP} (h : GBig @Q) (h' : GBig @Q') :
    GBig fun {D} {T} {Lc} {sc} G μ₀ C x b => @Q D T Lc sc G μ₀ C x b ∧ @Q' D T Lc sc G μ₀ C x b := by
  obtain ⟨a, h⟩ := h
  obtain ⟨a', h'⟩ := h'
  refine ⟨max a a', fun ε CF hCF => ?_⟩
  obtain ⟨C0, x0, h⟩ := h ε CF (le_of_max_le_left hCF)
  obtain ⟨C1, x1, h'⟩ := h' ε CF (le_of_max_le_right hCF)
  exact ⟨max C0 C1, max x0 x1, fun C hC D large₂ he hx hR T Lc μ hL G =>
    ⟨h C (le_of_max_le_left hC) D large₂ he (le_of_max_le_left hx) hR T Lc μ hL G,
     h' C (le_of_max_le_right hC) D large₂ he (le_of_max_le_right hx) hR T Lc μ hL G⟩⟩

theorem integralNormBound_mono {K : Type} [Field K] [NumberField K] {ι : Type} {dl : Formalism.PairingDivisionLocalBalance.Pl K → ℝ} {zA zA' : ι → K}
    {B B' : ℝ} (h : NonArchimedeanDefectBound dl zA zA' B) (hB : B ≤ B') : NonArchimedeanDefectBound dl zA zA' B' :=
  ⟨h.1, fun F => (h.2.1 F).trans hB, h.2.2⟩

end GlobalTheory.BigTop.Fun.IntTie
end
end
