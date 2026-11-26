module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceCohomologyPresheafClassesAsCocycles
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinXiExtMemRigidTensorIffStatement
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinIntegralityComputation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MaxFrobeniusOrbitLengthDiffBoundsZmod
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorMemCocyclesPowQuot
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SSAscent
public import GroundTheory.PAdicHodge.TiltValuation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinZetaFineBoundSecondBasis

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ColRepSemisimple
noncomputable section

namespace GlobalTheory.TraceConj

variable {Γ k : Type} [Group Γ] [Field k] {a : ℕ}

def colRep (ρ : Γ →* GL (Fin a) k) : Representation k Γ (Fin a → k) where
  toFun g := Matrix.toLin' ((ρ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)
  map_one' := by
    rw [map_one, Units.val_one, Matrix.toLin'_one]
    rfl
  map_mul' g h := by
    rw [map_mul, Units.val_mul, Matrix.toLin'_mul]
    rfl

theorem colRep_apply (ρ : Γ →* GL (Fin a) k) (g : Γ) :
    colRep ρ g = Matrix.toLin' ((ρ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) := rfl

theorem colRep_semisimple (ρ : Γ →* GL (Fin a) k) (h : Formalism.MainNotions.N.IsSSRep ρ) :
    (colRep ρ).IsSemisimpleRepresentation := by
  refine ⟨fun P => ?_⟩
  obtain ⟨W', h1, h2⟩ := h P.toSubmodule fun g v hv => P.apply_mem_toSubmodule g hv
  refine ⟨⟨W', fun g v hv => h1 g v hv⟩, ?_⟩
  rw [isCompl_iff, disjoint_iff, codisjoint_iff,
    ← Subrepresentation.toSubmodule_injective.eq_iff, ← Subrepresentation.toSubmodule_injective.eq_iff]
  rw [isCompl_iff, disjoint_iff, codisjoint_iff] at h2
  exact h2

theorem conj_of_trace_eq : ∀ (Γ k : Type) [Group Γ] [Field k] [CharZero k] (a : ℕ)
    (ρ ρ' : Γ →* GL (Fin a) k), Formalism.MainNotions.N.IsSSRep ρ → Formalism.MainNotions.N.IsSSRep ρ' →
    (∀ g, ((ρ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).trace =
      ((ρ' g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).trace) →
    ∃ h : GL (Fin a) k, ∀ g, ρ' g = h * ρ g * h⁻¹ := by
  intro Γ k _ _ _ a ρ ρ' hρ hρ' ht
  obtain ⟨e, he⟩ := GlobalTheory.TraceIso.exists_equiv_of_trace_eq (colRep ρ) (colRep ρ')
    (colRep_semisimple ρ hρ) (colRep_semisimple ρ' hρ') fun g => by
      rw [colRep_apply, colRep_apply, Matrix.trace_toLin'_eq, Matrix.trace_toLin'_eq, ht]
  let h : GL (Fin a) k :=
    ⟨LinearMap.toMatrix' e.toLinearMap, LinearMap.toMatrix' e.symm.toLinearMap,
      by rw [← LinearMap.toMatrix'_comp]; simp,
      by rw [← LinearMap.toMatrix'_comp]; simp⟩
  refine ⟨h, fun g => ?_⟩
  rw [eq_mul_inv_iff_mul_eq]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul]
  have hh : Matrix.toLin' (h : Matrix (Fin a) (Fin a) k) = e.toLinearMap :=
    Matrix.toLin'_toMatrix' _
  rw [hh]
  exact LinearMap.ext fun v => (he g v).symm

end GlobalTheory.TraceConj

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinSectionTrivialisesInvertPrimeTensor
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemInvLSIffTendsto
open GlobalTheory.BK PowerSeries Filter Topology

namespace GlobalTheory.BK

theorem mem_invL_S_iff_tendsto (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e]
    [CompleteSpace K] (f : K⟦X⟧) :
    f ∈ invL l (S O K e) ↔ Tendsto (fun n => ‖coeff n f‖ * wS K e n) atTop (𝓝 0) := by
  have h2 : (((l : S O K e) : K⟦X⟧)) = C (l : K) := by simp
  have hl : 0 < ‖(l : K)‖ := norm_pos_iff.2 (l_ne_zero l)
  have key : ∀ m n : ℕ, ‖coeff n ((((l : S O K e) : K⟦X⟧)) ^ m * f)‖ * wS K e n =
      ‖(l : K)‖ ^ m * (‖coeff n f‖ * wS K e n) := fun m n => by
    rw [h2, ← map_pow, coeff_C_mul, norm_mul, norm_pow, mul_assoc]
  constructor
  · rintro ⟨m, hm⟩
    have h := (mem_S.1 hm).2.const_mul (‖(l : K)‖ ^ m)⁻¹
    rw [mul_zero] at h
    refine h.congr fun n => ?_
    rw [key, inv_mul_cancel_left₀ (pow_pos hl m).ne']
  · intro hf
    obtain ⟨b, hb⟩ := hf.bddAbove_range
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _)
      (norm_l_lt_one (K := K) l)).mul_const b
    rw [zero_mul] at h
    obtain ⟨m, hm⟩ := (h.eventually (gt_mem_nhds zero_lt_one)).exists
    refine ⟨m, mem_S.2 ⟨fun n => ?_, ?_⟩⟩
    · rw [key]
      exact (mul_le_mul_of_nonneg_left (hb ⟨n, rfl⟩) (pow_pos hl m).le).trans hm.le
    · have h3 := hf.const_mul (‖(l : K)‖ ^ m)
      rw [mul_zero] at h3
      exact h3.congr fun n => (key m n).symm

end GlobalTheory.BK
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinSectionTrivialisesInvertPrimeTensor
open PowerSeries GlobalTheory.BK Filter Topology

namespace GlobalTheory.BK

theorem norm_natCast_eq_rpow_padicValNat (l : ℕ) [Fact l.Prime] (K : Type) [NormedField K]
    [NormedAlgebra ℚ_[l] K] (N : ℕ) (hN : N ≠ 0) :
    ‖(N : K)‖ = (l : ℝ) ^ (-(padicValNat l N : ℝ)) := by
  rw [← map_natCast (algebraMap ℚ_[l] K), norm_algebraMap',
    Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast hN), Padic.valuation_natCast,
    ← Real.rpow_intCast]
  congr 1
  push_cast
  simp [padicValRat.of_nat, Nat.padicValNat_def]

theorem wS_le_rpow (K : Type) [NormedField K] [IsUltrametricDist K] (l e : ℕ) [Fact l.Prime]
    [NormedAlgebra ℚ_[l] K] [NeZero e] (n : ℕ) :
    wS K e n ≤ (l : ℝ) ^ (1 / ((l : ℝ) - 1)) * ((n : ℝ) + 1) *
      (l : ℝ) ^ (-(n : ℝ) * (1 / ((e : ℝ) * ((l : ℝ) - 1)))) := by
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  have hq : (0 : ℝ) < (l : ℝ) - 1 := by linarith
  have he : (0 : ℝ) < e := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne e)
  set m := n / e with hmdef
  have hv := GlobalTheory.DetPowContent.padicValNat_factorial_ge l (Fact.out : l.Prime) m
  have hm : (n : ℝ) / e - 1 ≤ m := by
    have h1 : n < (m + 1) * e := by
      have := Nat.lt_div_mul_add (a := n) (Nat.pos_of_ne_zero (NeZero.ne e))
      rw [hmdef]; linarith
    have h2 : (n : ℝ) < ((m : ℝ) + 1) * e := by exact_mod_cast h1
    rw [div_sub_one he.ne', div_le_iff₀ he]; linarith
  have hm1 : ((m : ℝ) + 1) ≤ (n : ℝ) + 1 := by
    have : m ≤ n := Nat.div_le_self n e
    exact_mod_cast Nat.add_le_add_right this 1
  unfold wS
  rw [← hmdef, norm_natCast_eq_rpow_padicValNat l K _ (Nat.factorial_ne_zero m)]
  have hexp : -(padicValNat l m.factorial : ℝ) ≤ Real.logb l ((m : ℝ) + 1) + 1 / ((l : ℝ) - 1) +
      -(n : ℝ) * (1 / ((e : ℝ) * ((l : ℝ) - 1))) := by
    have h3 : (n : ℝ) * (1 / ((e : ℝ) * ((l : ℝ) - 1))) = ((n : ℝ) / e) / ((l : ℝ) - 1) := by
      field_simp
    have h4 : ((n : ℝ) / e) / ((l : ℝ) - 1) ≤ (m : ℝ) / ((l : ℝ) - 1) + 1 / ((l : ℝ) - 1) := by
      rw [← add_div]; exact div_le_div_of_nonneg_right (by linarith) hq.le
    nlinarith
  calc (l : ℝ) ^ (-(padicValNat l m.factorial : ℝ))
      ≤ (l : ℝ) ^ (Real.logb l ((m : ℝ) + 1) + 1 / ((l : ℝ) - 1) +
          -(n : ℝ) * (1 / ((e : ℝ) * ((l : ℝ) - 1)))) := Real.rpow_le_rpow_of_exponent_le hl.le hexp
    _ = ((m : ℝ) + 1) * (l : ℝ) ^ (1 / ((l : ℝ) - 1)) *
          (l : ℝ) ^ (-(n : ℝ) * (1 / ((e : ℝ) * ((l : ℝ) - 1)))) := by
      rw [Real.rpow_add hl0, Real.rpow_add hl0, Real.rpow_logb hl0 hl.ne' (by positivity)]
    _ ≤ _ := by
      rw [mul_comm ((m : ℝ) + 1)]
      gcongr

end GlobalTheory.BK

open Matrix

namespace GlobalTheory.BK

theorem R_le_invL_S (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [Algebra O K] [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e]
    (k : ℝ) (hk : k < 1 / ((e : ℝ) * (l - 1))) : R O K l k ≤ invL l (S O K e) := by
  intro f hf
  rw [mem_invL_S_iff_tendsto O K l e f]
  have hR := mem_R.1 hf
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  set k0 := 1 / ((e : ℝ) * (l - 1)) with hk0
  set q := (l : ℝ) ^ (k - k0) with hqdef
  have hq0 : 0 ≤ q := Real.rpow_nonneg hl0.le _
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg hl (by linarith)
  set C := (l : ℝ) ^ (1 / ((l : ℝ) - 1)) with hC
  have hg : Tendsto (fun n : ℕ => C * (((n : ℝ) + 1) * q ^ n)) atTop (𝓝 0) := by
    have h1 := (tendsto_self_mul_const_pow_of_lt_one hq0 hq1).add
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1)
    rw [add_zero] at h1
    have h2 := h1.const_mul C
    rw [mul_zero] at h2
    exact h2.congr fun n => by ring
  have hprod := hR.mul hg
  rw [zero_mul] at hprod
  refine squeeze_zero (fun n => mul_nonneg (norm_nonneg _) (wS_nonneg e n)) (fun n => ?_) hprod
  have hw := wS_le_rpow K l e n
  have hrad : rad l k ^ n * q ^ n = (l : ℝ) ^ (-(n : ℝ) * k0) := by
    rw [rad, hqdef, ← Real.rpow_mul_natCast hl0.le, ← Real.rpow_mul_natCast hl0.le,
      ← Real.rpow_add hl0]
    congr 1; ring
  calc ‖coeff n f‖ * wS K e n ≤ ‖coeff n f‖ * (C * ((n : ℝ) + 1) * (l : ℝ) ^ (-(n : ℝ) * k0)) :=
        mul_le_mul_of_nonneg_left hw (norm_nonneg _)
    _ = ‖coeff n f‖ * rad l k ^ n * (C * (((n : ℝ) + 1) * q ^ n)) := by
        rw [← hrad]; ring

theorem mulVec_mem_vecs {ι : Type} [Fintype ι] {O K : Type} [CommRing O] [NormedField K] [Algebra O K]
    {B : Subalgebra O K⟦X⟧} {M : Matrix ι ι K⟦X⟧} (hM : ∀ i j, M i j ∈ B) {v : ι → K⟦X⟧}
    (hv : v ∈ vecs ι B) : M *ᵥ v ∈ vecs ι B := fun i =>
  Subalgebra.sum_mem _ fun j _ => B.mul_mem (hM i j) (hv j)

end GlobalTheory.BK

theorem GlobalTheory.BK.xi_trivialises_invL_S : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] (P : PhiMod O K l e a ι), (∀ k : ℝ, k < 1 / ((e : ℝ) * (l - 1)) → R O K l k ≤ invL l (S O K e)) ∧ ∀ w : Vec K a ι, P.xiExt w ∈ P.MMl ↔ w ∈ P.Mext (invL l (S O K e)) := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ P
  refine ⟨fun k hk => R_le_invL_S O K l e k hk, fun w => ?_⟩
  have hl : (2 : ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).two_le
  have he : (0 : ℝ) < e := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne e)
  set k : ℝ := (1 / ((e : ℝ) * l) + 1 / ((e : ℝ) * (l - 1))) / 2 with hkdef
  have hlt : 1 / ((e : ℝ) * l) < 1 / ((e : ℝ) * (l - 1)) :=
    one_div_lt_one_div_of_lt (by nlinarith) (by nlinarith)
  have hk1 : 1 / ((e : ℝ) * l) < k := by rw [hkdef]; linarith
  have hk2 : k < 1 / ((e : ℝ) * (l - 1)) := by rw [hkdef]; linarith
  have hRB := R_le_invL_S O K l e k hk2
  have hT := GlobalTheory.T.breuilKisin_xiExt_mem_rigidTensor_iff O K l e a ι P k hk1
  set Y : ZMod a → Matrix ι ι K⟦X⟧ := fun τ => P.mxInv τ * P.xiMat τ with hY
  have hext : ∀ (B : Subalgebra O K⟦X⟧) (v : Vec K a ι),
      P.xiExt v ∈ P.ext B ↔ ∀ τ, Y τ *ᵥ v τ ∈ vecs ι B := by
    intro B v
    simp only [PhiMod.ext, mem_tot, PhiMod.mem_extc_iff, PhiMod.xiExt_apply, Matrix.mulVec_mulVec, hY]
  have hM : ∀ (B : Subalgebra O K⟦X⟧) (v : Vec K a ι), v ∈ P.Mext B ↔ ∀ τ, v τ ∈ vecs ι B := by
    intro B v
    simp only [PhiMod.Mext, mem_tot]
  have hYu : ∀ τ, IsUnit (Y τ).det := by
    intro τ
    rw [hY, Matrix.det_mul]
    exact (Matrix.isUnit_det_of_left_inverse (P.mx_mul_mxInv τ)).mul (P.isUnit_det_xiMat τ)

  have hYR : ∀ τ i j, Y τ i j ∈ R O K l k := by
    intro τ i j
    have h0 : (fun _ : ZMod a => (Pi.single j 1 : ι → K⟦X⟧)) ∈ P.Mext (R O K l k) := by
      rw [hM]; intro τ' i'
      rw [Pi.single_apply]; split_ifs
      exacts [one_mem _, zero_mem _]
    have h1 := (hext _ _).1 ((hT _).2 h0) τ i
    simpa [Matrix.mulVec_single_one] using h1

  have hZR : ∀ τ i j, (Y τ)⁻¹ i j ∈ R O K l k := by
    intro τ i j
    have h0 : P.xiExt (fun τ' => (Y τ')⁻¹ *ᵥ (Pi.single j 1 : ι → K⟦X⟧)) ∈ P.Lk k := by
      rw [PhiMod.Lk, hext]; intro τ' i'
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hYu τ'), Matrix.one_mulVec, Pi.single_apply]
      split_ifs
      exacts [one_mem _, zero_mem _]
    have h1 := (hM _ _).1 ((hT _).1 h0) τ i
    simpa [Matrix.mulVec_single_one] using h1
  rw [PhiMod.MMl, hext, hM]
  constructor
  · intro h τ
    have := mulVec_mem_vecs (fun i j => hRB (hZR τ i j)) (h τ)
    rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (hYu τ), Matrix.one_mulVec] at this
  · intro h τ
    exact mulVec_mem_vecs (fun i j => hRB (hYR τ i j)) (h τ)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinSectionTrivialisesInvertPrimeTensorStatement
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_section_trivialises_invertPrime_tensor : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] (P : PhiMod O K l e a ι), (∀ k : ℝ, k < 1 / ((e : ℝ) * (l - 1)) → R O K l k ≤ invL l (S O K e)) ∧ ∀ w : Vec K a ι, P.xiExt w ∈ P.MMl ↔ w ∈ P.Mext (invL l (S O K e)) := by
  exact @GlobalTheory.BK.xi_trivialises_invL_S
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusLaurentSeriesHasSumBoundFrobenius
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusLaurentSeriesHasSumBoundFrobenius
noncomputable section

open Formalism.Per Filter Topology
open scoped Formalism.Per

namespace GlobalTheory.PSer.Laws

variable {l : ℕ} [Fact l.Prime]

theorem pw_zero (x : Fl l) : pw 0 x = x := by simp [pw]

theorem pw_succ (k : ℤ) (x : Fl l) : pw (k + 1) x = pw k x ^ l := by
  unfold pw
  rw [add_comm, zpow_add, zpow_one]
  rfl

theorem pw_add (a b : ℤ) (x : Fl l) : pw (a + b) x = pw a (pw b x) := by
  unfold pw
  rw [zpow_add]
  rfl

theorem pw_nat (n : ℕ) (x : Fl l) : pw (n : ℤ) x = x ^ l ^ n := by
  induction n with
  | zero => simp [pw_zero]
  | succ n ih => rw [Nat.cast_succ, pw_succ, ih, ← pow_mul, pow_succ]

theorem sh_pow (x : Fl l) (n : ℕ) : sh (x ^ n) = sh x ^ n := by
  unfold sh
  rw [map_pow]; push_cast; rfl

theorem l_pos : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
theorem two_le_l : (2 : ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).two_le

theorem norm_sh_pw (k : ℤ) (x : Fl l) : ‖sh (pw k x)‖ = ‖sh x‖ ^ ((l : ℝ) ^ k) := by
  have hl := l_pos (l := l)
  induction k using Int.induction_on with
  | zero => simp [pw_zero]
  | succ k ih =>
    rw [pw_succ, sh_pow, norm_pow, ih, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _),
      zpow_add_one₀ hl.ne']
  | pred k ih =>
    have h1 : pw (-(k : ℤ)) x = pw (-(k : ℤ) - 1) x ^ l := by
      rw [← pw_succ]; congr 1; ring
    rw [h1, sh_pow, norm_pow] at ih
    have h2 : (‖sh x‖ ^ ((l : ℝ) ^ (-(k : ℤ) - 1))) ^ l = ‖sh x‖ ^ ((l : ℝ) ^ (-(k : ℤ))) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), ← zpow_add_one₀ hl.ne']
      congr 2; ring
    rw [← h2] at ih
    exact (pow_left_inj₀ (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _)
      (Fact.out : l.Prime).ne_zero).1 ih

theorem norm_l : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
  rw [GlobalTheory.RingBasics.norm_eq_val, PadicComplex.valuation_p]; simp

def sz (l : ℕ) [Fact l.Prime] (h j : ℕ) (r : ℝ) (n : ℤ) : ℝ :=
  ‖(l : ℂ_[l])‖ ^ (-n) * r ^ ((l : ℝ) ^ (n * h + j : ℤ))

theorem norm_term (h j : ℕ) (x : Fl l) (n : ℤ) :
    ‖(l : ℂ_[l]) ^ (-n) * sh (pw (n * h + j) x)‖ = sz l h j ‖sh x‖ n := by
  rw [norm_mul, norm_zpow, norm_sh_pw]; rfl

theorem sz_nonneg (h j : ℕ) {r : ℝ} (hr : 0 ≤ r) (n : ℤ) : 0 ≤ sz l h j r n :=
  mul_nonneg (zpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg hr _)

theorem sz_mono (h j : ℕ) {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) (n : ℤ) :
    sz l h j r n ≤ sz l h j s n :=
  mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hr hrs (zpow_nonneg l_pos.le _))
    (zpow_nonneg (norm_nonneg _) _)

theorem tendsto_sz {h : ℕ} (hh : 1 ≤ h) (j : ℕ) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    Tendsto (sz l h j r) cofinite (𝓝 0) := by
  have hl := l_pos (l := l)
  have hl2 := two_le_l (l := l)
  rw [Int.cofinite_eq, tendsto_sup]
  constructor
  · have hb : Tendsto (fun n : ℤ => (l : ℝ) ^ n) atBot (𝓝 0) := by
      have := (tendsto_rpow_atBot_of_base_gt_one (l : ℝ) (by linarith)).comp
        ((tendsto_intCast_atBot_iff (R := ℝ)).2 (tendsto_id (α := ℤ) (x := atBot)))
      refine this.congr fun n => ?_
      simp
    refine squeeze_zero (sz_nonneg h j hr) (fun n => ?_) hb
    unfold sz
    rw [norm_l, inv_zpow', neg_neg]
    exact mul_le_of_le_one_right (zpow_nonneg hl.le _)
      (Real.rpow_le_one hr hr1.le (zpow_nonneg hl.le _))
  · rw [← Nat.map_cast_int_atTop, tendsto_map'_iff]
    have h1 : Tendsto (fun n : ℕ => l ^ n) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (Fact.out : l.Prime).one_lt
    have h2 := (tendsto_self_mul_const_pow_of_lt_one hr hr1).comp h1
    refine squeeze_zero (fun n => sz_nonneg h j hr _) (fun n => ?_) h2
    simp only [Function.comp, sz]
    rw [norm_l, inv_zpow', neg_neg, zpow_natCast, Nat.cast_pow]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hl.le _)
    have : ((n : ℤ) * h + j : ℤ) = ((n * h + j : ℕ) : ℤ) := by push_cast; ring
    rw [this, zpow_natCast, ← Nat.cast_pow, Real.rpow_natCast]
    refine pow_le_pow_of_le_one hr hr1.le (Nat.pow_le_pow_right (Fact.out : l.Prime).pos ?_)
    nlinarith

theorem summable_lam {h : ℕ} (hh : 1 ≤ h) (j : ℕ) {x : Fl l} (hx : ‖sh x‖ < 1) :
    Summable fun n : ℤ => (l : ℂ_[l]) ^ (-n) * sh (pw (n * h + j) x) := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp only [norm_term]
  exact tendsto_sz hh j (norm_nonneg _) hx

theorem bdd_sz {h : ℕ} (hh : 1 ≤ h) (j : ℕ) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    BddAbove (Set.range (sz l h j r)) :=
  (tendsto_sz hh j hr hr1).bddAbove_range_of_cofinite

theorem gam_nonneg (h j : ℕ) {r : ℝ} (hr : 0 ≤ r) : 0 ≤ gam l h j r :=
  Real.iSup_nonneg (sz_nonneg h j hr)

theorem norm_lam_le {h : ℕ} (hh : 1 ≤ h) (j : ℕ) {x : Fl l} {r : ℝ} (hx : ‖sh x‖ ≤ r) (hr : r < 1) :
    ‖lam h j x‖ ≤ gam l h j r := by
  have h0 : 0 ≤ r := (norm_nonneg _).trans hx
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (gam_nonneg h j h0) fun n => ?_
  rw [norm_term]
  exact (sz_mono h j (norm_nonneg _) hx n).trans (le_ciSup (bdd_sz hh j h0 hr) n)

theorem lam_shift (h j : ℕ) (x : Fl l) : lam h (j + h) x = l * lam h j x := by
  unfold lam
  rw [← tsum_mul_left, ← (Equiv.addRight (1 : ℤ)).tsum_eq
    (fun n : ℤ => (l : ℂ_[l]) * ((l : ℂ_[l]) ^ (-n) * sh (pw (n * h + j) x)))]
  refine tsum_congr fun n => ?_
  have h1 : (n * h + ((j + h : ℕ) : ℤ)) = (n + 1) * h + j := by push_cast; ring
  simp only [Equiv.coe_addRight]
  rw [h1, ← mul_assoc, ← zpow_one_add₀ GlobalTheory.RingBasics.p_ne_zero]
  congr 2; ring

theorem lam_pow (h j k : ℕ) (x : Fl l) : lam h j (x ^ l ^ k) = lam h (j + k) x := by
  unfold lam
  refine tsum_congr fun n => ?_
  rw [← pw_nat, ← pw_add]
  congr 3
  push_cast; ring

end GlobalTheory.PSer.Laws

namespace GlobalTheory.PSer

open Laws

theorem lam_hasSum_norm_le_frob : ∀ (l : ℕ) [Fact l.Prime] (h j : ℕ) (r : ℝ) (x : Fl l), 1 ≤ h → r < 1 →
    ‖sh x‖ ≤ r → HasSum (fun n : ℤ => (l : ℂ_[l]) ^ (-n) * sh (pw (n * h + j) x)) (lam h j x) ∧
      ‖lam h j x‖ ≤ gam l h j r ∧ lam h j (x ^ l ^ h) = (l : ℂ_[l]) * lam h j x ∧
      lam h j (x ^ l) = lam h (j + 1) x := by
  intro l _ h j r x hh hr hx
  refine ⟨(summable_lam hh j (hx.trans_lt hr)).hasSum, norm_lam_le hh j hx hr, ?_, ?_⟩
  · rw [lam_pow, lam_shift]
  · have := lam_pow (l := l) h j 1 x
    rwa [pow_one] at this

end GlobalTheory.PSer

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusLaurentSeriesHasSumBoundFrobeniusStatement
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.untiltFrobeniusLaurentSeries_hasSum_bound_frobenius : ∀ (l : ℕ) [Fact l.Prime] (h j : ℕ) (r : ℝ) (x : Fl l), 1 ≤ h → r < 1 → ‖sh x‖ ≤ r → HasSum (fun n : ℤ => (l : ℂ_[l]) ^ (-n) * sh (pw (n * h + j) x)) (lam h j x) ∧ ‖lam h j x‖ ≤ gam l h j r ∧ lam h j (x ^ l ^ h) = (l : ℂ_[l]) * lam h j x ∧ lam h j (x ^ l) = lam h (j + 1) x := by
  first | exact @GlobalTheory.PSer.lam_hasSum_norm_le_frob | exact GlobalTheory.PSer.lam_hasSum_norm_le_frob | (intros; apply GlobalTheory.PSer.lam_hasSum_norm_le_frob <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinZetaFineBoundSecondBasisStatement
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_zeta_fine_bound_second_basis : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), 1 ≤ η → η < H → 14 * H < l → ∀ y ∈ D.Y', ∃ p ∈ D.L, ∃ f ∈ D.FilMM (10 * H), D.zeta y = (l : K) ^ (l - 14 * H) • p + ((l : K) ^ (3 * H))⁻¹ • f := by
  first | exact @GlobalTheory.BK.zeta_Y'_fine_bound | exact GlobalTheory.BK.zeta_Y'_fine_bound | (intros; apply GlobalTheory.BK.zeta_Y'_fine_bound <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterCongrRootOfUnityPow
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterCongrRootOfUnityPow
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)

namespace GlobalTheory.LocDualInt

theorem exists_root_pow_cyclotomicCharacter_congr {p : ℕ} [Fact p.Prime]
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (g : Formalism.GaloisCohomology.GK p K) (k : ℕ) :
    ∃ ζ : PadicAlgCl p, ζ ^ (p ^ k) = 1 ∧ ∀ a : ℕ, g ζ = ζ ^ a → (a : ZMod (p ^ k)) =
      PadicInt.toZModPow k ((cyclotomicCharacter (PadicAlgCl p) p
        (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK p K) (PadicAlgCl p) g) : ℤ_[p]ˣ) : ℤ_[p]) := by
  classical
  haveI : ∀ i : ℕ, HasEnoughRootsOfUnity (PadicAlgCl p) (p ^ i) := fun i => by
    haveI : NeZero ((p ^ i : ℕ) : PadicAlgCl p) :=
      ⟨by exact_mod_cast pow_ne_zero i (Fact.out : p.Prime).ne_zero⟩
    infer_instance
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl p) (p ^ k)
  refine ⟨ζ, hζ.pow_eq_one, fun a ha => ?_⟩
  set c : ZMod (p ^ k) := PadicInt.toZModPow k ((cyclotomicCharacter (PadicAlgCl p) p
    (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK p K) (PadicAlgCl p) g) : ℤ_[p]ˣ) : ℤ_[p]) with hc
  have hspec := cyclotomicCharacter.spec (L := PadicAlgCl p) p
    (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK p K) (PadicAlgCl p) g) ζ hζ.pow_eq_one
  have hg : (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK p K) (PadicAlgCl p) g) ζ = g ζ := rfl
  rw [hg, ha] at hspec
  have hpos : 0 < p ^ k := pow_pos (Fact.out : p.Prime).pos k
  have hfin : IsOfFinOrder ζ := isOfFinOrder_iff_pow_eq_one.mpr ⟨p ^ k, hpos, hζ.pow_eq_one⟩
  have hmod : a ≡ c.val [MOD orderOf ζ] := hfin.pow_eq_pow_iff_modEq.mp hspec
  rw [← hζ.eq_orderOf] at hmod
  exact ((ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod).trans (ZMod.natCast_zmod_val c)

end GlobalTheory.LocDualInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterCongrRootOfUnityPowStatement
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclotomicCharacter_congr_root_of_unity_pow : ∀ {p : ℕ} [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (g : Formalism.GaloisCohomology.GK p K) (k : ℕ), ∃ ζ : PadicAlgCl p, ζ ^ (p ^ k) = 1 ∧ ∀ a : ℕ, g ζ = ζ ^ a → (a : ZMod (p ^ k)) = PadicInt.toZModPow k ((cyclotomicCharacter (PadicAlgCl p) p (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK p K) (PadicAlgCl p) g) : ℤ_[p]ˣ) : ℤ_[p]) := by
  first | exact @GlobalTheory.LocDualInt.exists_root_pow_cyclotomicCharacter_congr | exact GlobalTheory.LocDualInt.exists_root_pow_cyclotomicCharacter_congr | (intros; apply GlobalTheory.LocDualInt.exists_root_pow_cyclotomicCharacter_congr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinDescentOperatorPreservesLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinDescentOperatorPreservesLattice
noncomputable section

open PowerSeries GlobalTheory.BK

namespace GlobalTheory.Proof.breuilKisin_descent_operator_preserves_lattice

theorem integral : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), η < H → 10 * H + 2 ≤ l → GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction.Integral D := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D hηH hl
  obtain ⟨-, hfil, hcomp⟩ := GlobalTheory.T.breuilKisin_integrality_computation O K l e a ι η H D hηH hl
  intro w hw
  obtain ⟨⟨y, hyM, rfl⟩, hinv⟩ := (D.desc.mem_Z).1 hw
  obtain ⟨p, hp, f, hf, hEq⟩ := hcomp y hyM
  have hfM := hfil f hf
  have h1 : E K l e ^ (2 * H) * Ezpow K l e (-(2 * H : ℤ)) = 1 := by
    simpa using E_pow_mul_Ezpow_neg (K := K) l e (2 * H)
  have hsplit : D.EN y = Ezpow K l e (-(2 * H : ℤ)) • p + Ezpow K l e (-(2 * H : ℤ)) • f := by
    rw [← smul_add, ← hEq, smul_smul, mul_comm, h1, one_smul]
  have hENy : D.EN y ∈ divE l e η D.Man := D.EN_mem_divE (D.M_le_Man hyM)
  have hy' : Ezpow K l e (-(2 * H : ℤ)) • p ∈ D.EM η := by
    have hA : E K l e ^ η • Ezpow K l e (-(2 * H : ℤ)) • p ∈ D.EM (2 * H) := by
      show E K l e ^ (2 * H) • E K l e ^ η • Ezpow K l e (-(2 * H : ℤ)) • p ∈ D.M
      rw [smul_comm (E K l e ^ (2 * H)) (E K l e ^ η), smul_smul (E K l e ^ (2 * H)), h1, one_smul]
      exact D.upper p hp
    have hB : E K l e ^ η • Ezpow K l e (-(2 * H : ℤ)) • p ∈ D.Man := by
      have : Ezpow K l e (-(2 * H : ℤ)) • p = D.EN y - Ezpow K l e (-(2 * H : ℤ)) • f := by
        rw [hsplit, add_sub_cancel_right]
      rw [this, smul_sub]
      exact sub_mem hENy (D.smul_mem_Man (pow_mem (E_mem l e _) η) hfM)
    exact D.mem_M_of_mem_Man hA hB
  refine (D.desc.mem_Z).2 ⟨⟨_, hy', ?_⟩, fun g => ?_⟩
  · rw [BKDat.Lc_cls, hsplit, map_add (f := _), add_eq_left.2 ((D.cls_eq_zero_iff).2 hfM)]
  · rw [D.actPol_Lc, hinv g]

end GlobalTheory.Proof.breuilKisin_descent_operator_preserves_lattice
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinDescentOperatorPreservesLatticeStatement
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_descent_operator_preserves_lattice : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), η < H → 10 * H + 2 ≤ l → GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction.Integral D := by
  first | exact @GlobalTheory.Proof.breuilKisin_descent_operator_preserves_lattice.integral | exact GlobalTheory.Proof.breuilKisin_descent_operator_preserves_lattice.integral | (intros; apply GlobalTheory.Proof.breuilKisin_descent_operator_preserves_lattice.integral <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfContinuousTrace
open Formalism.MainNotions.N GlobalTheory.PsChar

namespace GlobalTheory.SSCont

variable {Γ k : Type} [Group Γ] [Field k] {n : ℕ}

theorem mem_imAlg_iff (r : Γ →* GL (Fin n) k) (x : Matrix (Fin n) (Fin n) k) :
    x ∈ PI.SSAscent.UnitaryGroupMassFormula.imAlg r ↔
      x ∈ Submodule.span k (Set.range fun g => (r g : Matrix (Fin n) (Fin n) k)) := by
  have h : (Submonoid.closure (Set.range fun g => (r g : Matrix (Fin n) (Fin n) k)) :
      Set (Matrix (Fin n) (Fin n) k)) = Set.range fun g => (r g : Matrix (Fin n) (Fin n) k) := by
    have e : (Set.range fun g => (r g : Matrix (Fin n) (Fin n) k)) =
        (MonoidHom.mrange ((Units.coeHom _).comp r) : Set (Matrix (Fin n) (Fin n) k)) := by
      ext y
      simp
    rw [e, Submonoid.closure_eq]
  rw [PI.SSAscent.UnitaryGroupMassFormula.imAlg, ← Subalgebra.mem_toSubmodule, Algebra.adjoin_eq_span, h]

theorem exists_linear_of_trace [CharZero k] (r : Γ →* GL (Fin n) k) (hr : IsSSRep r) :
    ∃ (m : ℕ) (c : Fin m → Γ) (ψ : (Fin m → k) →ₗ[k] Matrix (Fin n) (Fin n) k),
      ∀ g, (r g : Matrix (Fin n) (Fin n) k) =
        ψ fun i => ((r (g * c i) : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace := by
  have hnd : PI.SSAscent.UnitaryGroupMassFormula.TrNondeg (PI.SSAscent.UnitaryGroupMassFormula.imAlg r) :=
    PI.SSAscent.UnitaryGroupMassFormula.downStep_of PI.SSAscent.UnitaryGroupMassFormula.trace_nilpotent_ascent k Γ n r hr
  set S : Set (Matrix (Fin n) (Fin n) k) := Set.range fun g => (r g : Matrix (Fin n) (Fin n) k) with hS
  obtain ⟨f, hf, hspan, -⟩ := Submodule.exists_fun_fin_finrank_span_eq k S
  choose c hc using hf
  let φ : Submodule.span k S →ₗ[k] (Fin (Module.finrank k (Submodule.span k S)) → k) :=
    LinearMap.pi fun i => (Matrix.traceLinearMap (Fin n) k k) ∘ₗ (LinearMap.mulRight k (f i)) ∘ₗ
      (Submodule.span k S).subtype
  have hφ : LinearMap.ker φ = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    apply Subtype.ext
    refine hnd x.1 ((mem_imAlg_iff r _).2 x.2) fun y hy => ?_
    have hy' := (mem_imAlg_iff r _).1 hy
    rw [← hS, ← hspan] at hy'
    clear hy
    induction hy' using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      simpa [φ] using congrFun hx i
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add, Matrix.trace_add, hy, hz, add_zero]
    | smul a y _ hy => rw [Matrix.mul_smul, Matrix.trace_smul, hy, smul_zero]
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_leftInverse_of_injective φ hφ
  refine ⟨_, c, (Submodule.span k S).subtype ∘ₗ ψ, fun g => ?_⟩
  let x : Submodule.span k S := ⟨r g, Submodule.subset_span ⟨g, rfl⟩⟩
  have h1 : (fun i => ((r (g * c i) : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace) = φ x := by
    funext i
    simp [φ, x, ← hc i]
  have h2 : ψ (φ x) = x := LinearMap.congr_fun hψ x
  rw [h1, LinearMap.comp_apply, h2]
  rfl

theorem continuous_of_continuous_trace : ∀ (Γ k : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Field k] [CharZero k] [TopologicalSpace k] [IsTopologicalRing k] (n : ℕ) (r : Γ →* GL (Fin n) k), IsSSRep r → Continuous (fun g => ((r g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace) → Continuous r := by
  intro Γ k _ _ _ _ _ _ _ n r hr ht
  obtain ⟨m, c, ψ, h⟩ := exists_linear_of_trace r hr
  have hc : Continuous fun g => ((r g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
    rw [funext h]
    exact ψ.continuous_on_pi.comp (continuous_pi fun i => ht.comp (continuous_mul_const (c i)))
  rw [Units.continuous_iff]
  refine ⟨hc, ?_⟩
  simp only [← map_inv]
  exact hc.comp continuous_inv

end GlobalTheory.SSCont
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTiltIntegersCpEquivCompatibleUntilt
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTiltIntegersCpEquivCompatibleUntilt
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer

open GroundTheory.PAdicHodge

variable (l : ℕ) [Fact l.Prime]

theorem oc_eq_normInteger : (𝓞_ℂ_[l]).toSubring = normInteger ℂ_[l] := by
  ext x
  rw [mem_normInteger, ← GlobalTheory.RingBasics.mem_OC]
  rfl

noncomputable def ocEquiv : OC l ≃+* normInteger ℂ_[l] := RingEquiv.subringCongr (oc_eq_normInteger l)

theorem coe_ocEquiv (x : OC l) : ((ocEquiv l x : normInteger ℂ_[l]) : ℂ_[l]) = (x : ℂ_[l]) := rfl

theorem span_map_ocEquiv :
    Ideal.span {(l : normInteger ℂ_[l])} = (Ideal.span {(l : OC l)}).map ((ocEquiv l : OC l →+* normInteger ℂ_[l])) := by
  rw [Ideal.map_span, Set.image_singleton]; simp

noncomputable def modEquiv : ModP (OC l) l ≃+* ModP (normInteger ℂ_[l]) l :=
  Ideal.quotientEquiv _ _ (ocEquiv l) (span_map_ocEquiv l)

noncomputable def flTo : Fl l →+* PreTilt (normInteger ℂ_[l]) l :=
  Perfection.map l (modEquiv l : ModP (OC l) l →+* ModP (normInteger ℂ_[l]) l)

noncomputable def flFrom : PreTilt (normInteger ℂ_[l]) l →+* Fl l :=
  Perfection.map l ((modEquiv l).symm : ModP (normInteger ℂ_[l]) l →+* ModP (OC l) l)

theorem coeff_flTo (x : Fl l) (n : ℕ) :
    Perfection.coeff _ l n (flTo l x) = modEquiv l (Perfection.coeff _ l n x) := rfl

theorem coeff_flFrom (x : PreTilt (normInteger ℂ_[l]) l) (n : ℕ) :
    Perfection.coeff _ l n (flFrom l x) = (modEquiv l).symm (Perfection.coeff _ l n x) := rfl

noncomputable def flEquiv : Fl l ≃+* PreTilt (normInteger ℂ_[l]) l :=
  RingEquiv.ofRingHom (flTo l) (flFrom l)
    (RingHom.ext fun x => Perfection.ext fun n => by
      change Perfection.coeff _ l n (flTo l (flFrom l x)) = Perfection.coeff _ l n x
      rw [coeff_flTo, coeff_flFrom, RingEquiv.apply_symm_apply])
    (RingHom.ext fun x => Perfection.ext fun n => by
      change Perfection.coeff _ l n (flFrom l (flTo l x)) = Perfection.coeff _ l n x
      rw [coeff_flFrom, coeff_flTo, RingEquiv.symm_apply_apply])

theorem flEquiv_apply (x : Fl l) : flEquiv l x = flTo l x := rfl

theorem untilt_flTo (x : Fl l) : (flTo l x).untilt = ocEquiv l x.untilt := by
  refine Perfection.teichmuller_spec (I := Ideal.span {(l : normInteger ℂ_[l])}) fun n => ?_
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (Perfection.coeff _ l n x)
  refine ⟨ocEquiv l y, ?_, ?_⟩
  · rw [coeff_flTo, ← hy]
    rfl
  · have := (Perfection.teichmuller_sModEq hy).symm
    rw [SModEq.sub_mem, GlobalTheory.RingBasics.mem_span_pow_OC] at this
    have hl : ((l : normInteger ℂ_[l]) : ℂ_[l]) = (l : ℂ_[l]) := by simp
    rw [SModEq.sub_mem, mem_span_singleton_pow_iff, ← map_pow, ← map_sub, coe_ocEquiv, hl]
    exact this

theorem exists_flEquiv_untilt : ∀ (l : ℕ) [Fact l.Prime], ∃ e : Fl l ≃+* PreTilt (GroundTheory.PAdicHodge.normInteger ℂ_[l]) l,
    ∀ x : Fl l, ((PreTilt.untilt (e x) : GroundTheory.PAdicHodge.normInteger ℂ_[l]) : ℂ_[l]) = sh x := by
  intro l _
  refine ⟨flEquiv l, fun x => ?_⟩
  rw [flEquiv_apply, untilt_flTo, coe_ocEquiv]
  rfl

end GlobalTheory.PSer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTiltIntegersCpEquivCompatibleUntiltStatement
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tiltIntegersCpEquiv_compatible_untilt : ∀ (l : ℕ) [Fact l.Prime], ∃ e : Fl l ≃+* PreTilt (GroundTheory.PAdicHodge.normInteger ℂ_[l]) l, ∀ x : Fl l, ((PreTilt.untilt (e x) : GroundTheory.PAdicHodge.normInteger ℂ_[l]) : ℂ_[l]) = sh x := by
  first | exact @GlobalTheory.PSer.exists_flEquiv_untilt | exact GlobalTheory.PSer.exists_flEquiv_untilt | (intros; apply GlobalTheory.PSer.exists_flEquiv_untilt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteCocyclesQuotientPowSmulModule
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteCocyclesQuotientPowSmulModule
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)

noncomputable section

namespace GlobalTheory.LocDualInt

theorem finite_of_finite_quotient_submodule {R N : Type*} [Ring R] [AddCommGroup N] [Module R N]
    (S : Submodule R N) [Finite (N ⧸ S)] [Finite S] : Finite N := by
  classical
  let s := Function.surjInv (Submodule.Quotient.mk_surjective S)
  have hs : ∀ x : N, x - s (Submodule.Quotient.mk x) ∈ S := fun x =>
    (Submodule.Quotient.eq S).1 (Function.surjInv_eq (Submodule.Quotient.mk_surjective S) _).symm
  refine Finite.of_injective (fun x : N => ((Submodule.Quotient.mk x : N ⧸ S), (⟨_, hs x⟩ : S))) ?_
  intro x y h
  simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  rw [h1] at h2
  simpa using h2

theorem finite_cocycles_of_finite_h1 {R : Type*} [CommRing R] {H : Type*} [Group H] [TopologicalSpace H]
    {Q : Type*} [AddCommGroup Q] [Module R Q] [TopologicalSpace Q] [IsTopologicalAddGroup Q]
    [ContinuousConstSMul R Q] [Finite Q] (σ : Representation R H Q) [Finite (H1 σ)] :
    Finite (Z1 σ) := by
  haveI : Finite ((B1 σ).comap (Z1 σ).subtype) := by
    haveI : Finite (B1 σ) := by
      haveI : Finite (Set.range (d0 σ)) := Set.finite_range _
      exact Finite.of_injective (fun x : B1 σ => (⟨x.1, x.2⟩ : Set.range (d0 σ)))
        (fun x y h => Subtype.ext (congrArg Subtype.val h))
    exact Finite.of_injective (fun x : (B1 σ).comap (Z1 σ).subtype => (⟨x.1.1, x.2⟩ : B1 σ))
      (fun x y h => by
        apply Subtype.ext; apply Subtype.ext
        have := congrArg Subtype.val h
        simpa using this)
  exact finite_of_finite_quotient_submodule ((B1 σ).comap (Z1 σ).subtype)

end GlobalTheory.LocDualInt

noncomputable section

namespace GlobalTheory.LocDualInt

def toZModRep {R H Q : Type*} [CommRing R] [Group H] [AddCommGroup Q] [Module R Q] (m : ℕ)
    [Module (ZMod m) Q] (τ : Representation R H Q) : Representation (ZMod m) H Q where
  toFun h := (τ h).toAddMonoidHom.toZModLinearMap m
  map_one' := LinearMap.ext fun x => by simp
  map_mul' g h := LinearMap.ext fun x => by simp [Module.End.mul_apply]

section Transport

variable {R G H Q : Type*} [CommRing R] [Group G] [TopologicalSpace G] [Group H]
  [TopologicalSpace H] [AddCommGroup Q] [Module R Q] [TopologicalSpace Q]
  [IsTopologicalAddGroup Q] [ContinuousConstSMul R Q] (m : ℕ) [Module (ZMod m) Q]
  [ContinuousConstSMul (ZMod m) Q]

theorem contAction_toZModRep (τ : Representation R H Q) (hτ : ContAction τ) :
    ContAction (toZModRep m τ) := hτ

theorem cocycles_subset_image_toZModRestriction (i : G ≃ₜ* H) (τ : Representation R G Q) :
    (Z1 τ : Set (G → Q)) ⊆
      (fun f : H → Q => f ∘ i) '' (Z1 (toZModRep m (τ.comp i.symm.toMonoidHom)) : Set (H → Q)) := by
  intro f hf
  refine ⟨f ∘ i.symm, ⟨hf.1.comp i.symm.continuous, fun g h => ?_⟩, ?_⟩
  · show f (i.symm (g * h)) = f (i.symm g) + τ (i.symm g) (f (i.symm h))
    rw [map_mul, hf.2]
  · funext x
    simp

end Transport

end GlobalTheory.LocDualInt

noncomputable section

namespace GlobalTheory.LocDualInt

theorem finite_cocycles_quotient_pow_smul_module : Formalism.GaloisCohomology.LocalTateDualityK → ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {G : Type} [Group G] [TopologicalSpace G] {M : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul O M] [CompactSpace M], FiniteDimensional ℚ_[p] K → (p : O) ∈ IsLocalRing.maximalIdeal O → ∀ (i : G ≃ₜ* Formalism.GaloisCohomology.GK p K) (ρ : Representation O G M), ContAction ρ → ∀ ϖ : O, Irreducible ϖ → (∀ n : ℕ, IsOpen ((powSub (M := M) ϖ n : Submodule O M) : Set M)) → ∀ n : ℕ, (Z1 (quotRep ρ ϖ n) : Set (G → M ⧸ powSub (M := M) ϖ n)).Finite := by
  intro hT p _ K O _ _ _ G _ _ M _ _ _ _ _ _ hK hp i ρ hρ ϖ hϖ hopen n
  have hmk := Submodule.isOpenQuotientMap_mkQ (powSub (M := M) ϖ n)
  haveI hdisc : DiscreteTopology (M ⧸ powSub (M := M) ϖ n) := by
    rw [discreteTopology_iff_isOpen_singleton_zero, ← hmk.isQuotientMap.isOpen_preimage]
    convert hopen n using 1
    ext x
    simp [Submodule.Quotient.mk_eq_zero]
  haveI : CompactSpace (M ⧸ powSub (M := M) ϖ n) :=
    ⟨by simpa [hmk.surjective.range_eq] using isCompact_univ.image hmk.continuous⟩
  haveI : Finite (M ⧸ powSub (M := M) ϖ n) := finite_of_compact_of_discrete
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · haveI : Subsingleton (M ⧸ powSub (M := M) ϖ 0) := by
      refine ⟨fun a b => ?_⟩
      induction a using Submodule.Quotient.induction_on with | _ x => ?_
      induction b using Submodule.Quotient.induction_on with | _ y => ?_
      rw [Submodule.Quotient.eq]
      exact mem_powSub.2 ⟨x - y, by simp⟩
    exact Set.Subsingleton.finite fun f _ g _ => Subsingleton.elim f g
  obtain ⟨a, ha⟩ := (Ideal.mem_span_singleton'.1 (hϖ.maximalIdeal_eq ▸ hp))
  have kill : ∀ x : M ⧸ powSub (M := M) ϖ n, (p ^ n) • x = 0 := by
    intro x
    induction x using Submodule.Quotient.induction_on with | _ y => ?_
    rw [← Nat.cast_smul_eq_nsmul O, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    push_cast
    rw [← ha, mul_pow, mul_comm, mul_smul]
    exact smul_mem_powSub ϖ n _
  letI : Module (ZMod (p ^ n)) (M ⧸ powSub (M := M) ϖ n) := AddCommGroup.zmodModule kill
  haveI : ContinuousConstSMul (ZMod (p ^ n)) (M ⧸ powSub (M := M) ϖ n) :=
    ⟨fun _ => continuous_of_discreteTopology⟩
  have hcont : ContAction ((quotRep ρ ϖ n).comp i.symm.toMonoidHom) := by
    refine continuous_prod_of_discrete_right.2 fun q => ?_
    induction q using Submodule.Quotient.induction_on with | _ x => ?_
    show Continuous fun g => quotRep ρ ϖ n (i.symm g) (Submodule.Quotient.mk x)
    simp only [quotRep_mk]
    exact hmk.continuous.comp (hρ.comp (i.symm.continuous.prodMk continuous_const))
  haveI := (GlobalTheory.finite_H1_H2_of_localTateDuality hT p K hK n (M ⧸ powSub (M := M) ϖ n)
    (toZModRep (p ^ n) ((quotRep ρ ϖ n).comp i.symm.toMonoidHom)) hn
    (contAction_toZModRep _ _ hcont)).1
  haveI := finite_cocycles_of_finite_h1 (toZModRep (p ^ n) ((quotRep ρ ϖ n).comp i.symm.toMonoidHom))
  exact ((Set.toFinite _).image _).subset (cocycles_subset_image_toZModRestriction (p ^ n) i (quotRep ρ ϖ n))

end GlobalTheory.LocDualInt
end
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteCocyclesQuotientPowSmulModuleStatement
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_cocycles_quotient_pow_smul_of_isOpen : Formalism.GaloisCohomology.LocalTateDualityK → ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {G : Type} [Group G] [TopologicalSpace G] {M : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul O M] [CompactSpace M], FiniteDimensional ℚ_[p] K → (p : O) ∈ IsLocalRing.maximalIdeal O → ∀ (i : G ≃ₜ* Formalism.GaloisCohomology.GK p K) (ρ : Representation O G M), ContAction ρ → ∀ ϖ : O, Irreducible ϖ → (∀ n : ℕ, IsOpen ((powSub (M := M) ϖ n : Submodule O M) : Set M)) → ∀ n : ℕ, (Z1 (quotRep ρ ϖ n) : Set (G → M ⧸ powSub (M := M) ϖ n)).Finite := by
  first | exact @GlobalTheory.LocDualInt.finite_cocycles_quotient_pow_smul_module | exact GlobalTheory.LocDualInt.finite_cocycles_quotient_pow_smul_module | (intros; apply GlobalTheory.LocDualInt.finite_cocycles_quotient_pow_smul_module <;> assumption)
end
end
