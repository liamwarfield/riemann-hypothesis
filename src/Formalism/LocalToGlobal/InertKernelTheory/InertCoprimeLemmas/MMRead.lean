module

public import Formalism.LocalToGlobal.InertKernelTheory.DefsRepRec
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntBasis
public import Formalism.LocalToGlobal.InertKernelTheory.StatementAlgT
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated

@[expose] public section

section -- merged from Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.MMRead
noncomputable section

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Classical

namespace ParameterChangeLemmas

open IntegralOrthonormalChange

variable {p : ℕ} [Fact p.Prime]

theorem constantCoeff_inVar_eq_zero {σ : Type*} (i : σ) (f : PowerSeries ℂ_[p]) (hf : PowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ ℂ_[p]) f) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X i) f hf

theorem integral_subst_single_variable {σ : Type*} (i : σ) (f : PowerSeries ℂ_[p]) (hf : ∀ n, IsIntP (PowerSeries.coeff n f)) :
    IntegralMv (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ ℂ_[p]) f) := by
  intro n
  rw [PowerSeries.coeff_subst_single]
  split_ifs
  · exact hf _
  · show ‖(0 : ℂ_[p])‖ ≤ 1
    simp

theorem integral_prod {σ ι : Type*} (s : Finset ι) (f : ι → MvPowerSeries σ ℂ_[p])
    (hf : ∀ i ∈ s, IntegralMv (f i)) : IntegralMv (∏ i ∈ s, f i) := by
  refine Finset.prod_induction f IntegralMv (fun a b ha hb => IntegralOrthonormalChange.integral_mul ha hb) ?_ hf
  intro n
  show ‖MvPowerSeries.coeff n (1 : MvPowerSeries σ ℂ_[p])‖ ≤ 1
  rw [MvPowerSeries.coeff_one]
  split_ifs <;> simp

theorem subst_single_var {σ τ : Type*} (S : σ → MvPowerSeries τ ℂ_[p]) (hS : MvPowerSeries.HasSubst S)
    (f : PowerSeries ℂ_[p]) (i : σ) :
    MvPowerSeries.subst S (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ ℂ_[p]) f) =
      PowerSeries.subst (S i) f := by
  have hX : MvPowerSeries.HasSubst (fun _ : Unit => (MvPowerSeries.X i : MvPowerSeries σ ℂ_[p])) :=
    (PowerSeries.HasSubst.X i).const
  rw [PowerSeries.subst, MvPowerSeries.subst_comp_subst_apply hX hS, PowerSeries.subst]
  congr 1
  funext _
  exact MvPowerSeries.subst_X hS i

theorem subst_inv {σ : Type*} (a : MvPowerSeries σ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0)
    (f : PowerSeries ℂ_[p]) : PowerSeries.subst a f⁻¹ = (PowerSeries.subst a f)⁻¹ := by
  have hs : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero ha
  by_cases hf : PowerSeries.constantCoeff f = 0
  · have h1 : f⁻¹ = 0 := PowerSeries.inv_eq_zero.mpr hf
    have h2 : MvPowerSeries.constantCoeff (PowerSeries.subst a f) = 0 :=
      PowerSeries.constantCoeff_subst_eq_zero ha f hf
    rw [h1, MvPowerSeries.inv_eq_zero.mpr h2, ← PowerSeries.coe_substAlgHom hs, map_zero]
  · have hm : PowerSeries.subst a f * PowerSeries.subst a f⁻¹ = 1 := by
      rw [← PowerSeries.subst_mul hs, PowerSeries.mul_inv_cancel f hf, ← PowerSeries.coe_substAlgHom hs, map_one]
    have hc : MvPowerSeries.constantCoeff (PowerSeries.subst a f) ≠ 0 := by
      intro h0
      have := congrArg MvPowerSeries.constantCoeff hm
      rw [map_mul, h0, zero_mul, map_one] at this
      exact zero_ne_one this
    rw [MvPowerSeries.eq_inv_iff_mul_eq_one hc, mul_comm, hm]

private theorem exists_integral_subst_inverse_of_unit_linear (h : PowerSeries ℂ_[p]) (h0 : PowerSeries.constantCoeff h = 0)
    (hI : ∀ n, ‖PowerSeries.coeff n h‖ ≤ 1) (h1 : ‖PowerSeries.coeff 1 h‖ = 1) :
    ∃ g : PowerSeries ℂ_[p], PowerSeries.constantCoeff g = 0 ∧ (∀ n, ‖PowerSeries.coeff n g‖ ≤ 1) ∧
      ‖PowerSeries.coeff 1 g‖ = 1 ∧ PowerSeries.subst h g = PowerSeries.X := by
  set u := PowerSeries.coeff 1 h with hudef
  have hu0 : u ≠ 0 := by
    intro hu
    rw [hu, norm_zero] at h1
    exact zero_ne_one h1
  obtain ⟨h', hh'⟩ : PowerSeries.X ∣ h := PowerSeries.X_dvd_iff.mpr h0
  have hcc : PowerSeries.constantCoeff h' = u := by
    rw [hudef, hh', PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have hpow : ∀ m k, PowerSeries.coeff k (h ^ m) =
      if m ≤ k then PowerSeries.coeff (k - m) (h' ^ m) else 0 := by
    intro m k
    rw [hh', mul_pow, PowerSeries.coeff_X_pow_mul']
  have hlow : ∀ m k, k < m → PowerSeries.coeff k (h ^ m) = 0 := by
    intro m k hk
    rw [hpow, ite_eq_right (by omega)]
  have hdiag : ∀ m, PowerSeries.coeff m (h ^ m) = u ^ m := by
    intro m
    rw [hpow, ite_eq_left le_rfl, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, hcc]
  let b : ℕ → ℂ_[p] := Nat.strongRec fun n rec =>
    (u ^ n)⁻¹ * PowerSeries.coeff n
      (PowerSeries.X - ∑ m : Fin n, PowerSeries.C (rec m m.isLt) * h ^ (m : ℕ))
  have hb : ∀ n, b n = (u ^ n)⁻¹ * PowerSeries.coeff n
      (PowerSeries.X - ∑ m ∈ Finset.range n, PowerSeries.C (b m) * h ^ m) := by
    intro n
    rw [← Fin.sum_univ_eq_sum_range (fun m => PowerSeries.C (b m) * h ^ m) n]
    exact Nat.strongRec_eq _ n
  have hcoeffP : ∀ N k, PowerSeries.coeff k (∑ m ∈ Finset.range N, PowerSeries.C (b m) * h ^ m) =
      ∑ m ∈ Finset.range N, b m * PowerSeries.coeff k (h ^ m) := by
    intro N k
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, PowerSeries.coeff_C_mul]
  have hA : ∀ N, ∀ k < N, PowerSeries.coeff k
      (PowerSeries.X - ∑ m ∈ Finset.range N, PowerSeries.C (b m) * h ^ m) = 0 := by
    intro N
    induction N with
    | zero => intro k hk; omega
    | succ N ih =>
      intro k hk
      rw [Finset.sum_range_succ, ← sub_sub, map_sub]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hk
      · rw [ih k hk, PowerSeries.coeff_C_mul, hlow N k hk, mul_zero, sub_zero]
      · subst hk
        rw [PowerSeries.coeff_C_mul, hdiag, hb k, mul_comm ((u ^ k)⁻¹) _, mul_assoc,
          inv_mul_cancel₀ (pow_ne_zero k hu0), mul_one, sub_self]
  have hb0 : b 0 = 0 := by
    rw [hb 0]
    simp
  have hb1 : b 1 = u⁻¹ := by
    rw [hb 1]
    simp [hb0]
  have hH : PowerSeries.HasSubst h := PowerSeries.HasSubst.of_constantCoeff_zero' h0
  have hhI : Formalism.L2.Th1.C.IntPS (IntegralOrthonormalChange.intRing p) h := fun n => hI n
  have hpowI : ∀ m, Formalism.L2.Th1.C.IntPS (IntegralOrthonormalChange.intRing p) (h ^ m) := by
    intro m
    induction m with
    | zero => simpa using Formalism.L2.Th1.C.USideA.intPS_C (R := IntegralOrthonormalChange.intRing p) (one_mem _)
    | succ m ihm => rw [pow_succ]; exact Formalism.L2.Th1.C.USideA.intPS_mul ihm hhI
  have hint : ∀ n, b n ∈ IntegralOrthonormalChange.intRing p := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rw [hb n]
      refine Subring.mul_mem _ ?_ ?_
      · show ‖(u ^ n)⁻¹‖ ≤ 1
        rw [norm_inv, norm_pow, h1, one_pow, inv_one]
      · exact Formalism.L2.Th1.C.USideA.intPS_sub Formalism.L2.Th1.C.USideA.intPS_X
          (Formalism.L2.Th1.C.USideA.intPS_sum _ fun m hm =>
            Formalism.L2.Th1.C.USideA.intPS_mul
              (Formalism.L2.Th1.C.USideA.intPS_C (ih m (Finset.mem_range.mp hm))) (hpowI m)) n
  refine ⟨PowerSeries.mk b, ?_, ?_, ?_, ?_⟩
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk, hb0]
  · intro n
    rw [PowerSeries.coeff_mk]
    exact hint n
  · rw [PowerSeries.coeff_mk, hb1, norm_inv, h1, inv_one]
  · ext k
    rw [PowerSeries.coeff_subst' hH]
    simp only [PowerSeries.coeff_mk, smul_eq_mul]
    rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (k + 1)) ?_]
    · have := hA (k + 1) k (Nat.lt_succ_self k)
      rw [map_sub, hcoeffP, sub_eq_zero] at this
      exact this.symm
    · intro d hd
      simp only [Function.mem_support] at hd
      simp only [Finset.coe_range, Set.mem_Iio]
      by_contra hdk
      exact hd (by rw [hlow d k (by omega), mul_zero])

theorem exists_inv (h : PowerSeries ℂ_[p]) (h0 : PowerSeries.constantCoeff h = 0)
    (hI : ∀ n, IsIntP (PowerSeries.coeff n h)) (h1 : ‖PowerSeries.coeff 1 h‖ = 1) :
    ∃ g : PowerSeries ℂ_[p], PowerSeries.constantCoeff g = 0 ∧ (∀ n, IsIntP (PowerSeries.coeff n g)) ∧
      h.subst g = PowerSeries.X := by
  obtain ⟨g, g0, gI, g1, hg⟩ := exists_integral_subst_inverse_of_unit_linear h h0 hI h1
  obtain ⟨k, k0, -, -, hk⟩ := exists_integral_subst_inverse_of_unit_linear g g0 gI g1
  have hG : PowerSeries.HasSubst g := PowerSeries.HasSubst.of_constantCoeff_zero' g0
  have hH : PowerSeries.HasSubst h := PowerSeries.HasSubst.of_constantCoeff_zero' h0
  have hkh : k = h := by
    have e1 : PowerSeries.subst h (PowerSeries.subst g k) = h := by
      rw [hk, PowerSeries.subst_X hH]
    rw [PowerSeries.subst_comp_subst_apply hG hH, hg, PowerSeries.X_subst] at e1
    exact e1
  refine ⟨g, g0, gI, ?_⟩
  rw [← hkh]
  exact hk

end ParameterChangeLemmas

open ParameterChangeLemmas IntegralOrthonormalChange

end Formalism.L2.KerInert
end
end

section -- merged from Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SecondKernelNonzeroUnit
noncomputable section

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Finset

namespace Formalism.L2.KerInert.K2

variable {p : ℕ} [Fact p.Prime] {X : Sys p}

theorem p_ne_zero_Kf (Y : Pend X) : (p : X.G.Kf) ≠ 0 := by
  intro h
  have h1 : algebraMap (K0 p) Y.Kc (p : K0 p) = 0 := by
    rw [map_natCast, ← map_natCast (algebraMap X.G.Kf Y.Kc), h, map_zero]
  rw [map_eq_zero_iff _ (algebraMap (K0 p) Y.Kc).injective] at h1
  exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) h1

theorem eS_ne_zero (Y : Pend X) (j : ℕ) (La : X.Lt j) : Y.eS j La ≠ 0 := by
  unfold Pend.eS
  exact Finset.prod_ne_zero_iff.mpr fun v _ => zpow_ne_zero _ (p_ne_zero_Kf Y)

theorem eT_ne_zero (Y : Pend X) (j : ℕ) (La' : X.Lt (j + 1)) : Y.eT j La' ≠ 0 := by
  unfold Pend.eT
  exact Finset.prod_ne_zero_iff.mpr fun v _ => zpow_ne_zero _ (p_ne_zero_Kf Y)

theorem kernel_of_smul : KerOfSmul := by
  intro p _ X Y j La La' f h G
  have hne : Y.eS j La * (Y.eT j La')⁻¹ ≠ 0 :=
    mul_ne_zero (eS_ne_zero Y j La) (inv_ne_zero (eT_ne_zero Y j La'))
  unfold Pend.ker Pend.kerF
  rw [h, map_smul, smul_smul, mul_inv_cancel₀ hne, one_smul]

theorem ker_zero (Y : Pend X) (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) : Y.ker j La La' 0 = 0 := by
  simp only [Pend.ker, Pend.kerF, map_zero, LinearMap.zero_apply, smul_zero]

theorem ker_add (Y : Pend X) (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) (G1 G2 : (X.Pj j).Xsp) :
    Y.ker j La La' (G1 + G2) = Y.ker j La La' G1 + Y.ker j La La' G2 := by
  simp only [Pend.ker, Pend.kerF, map_add (f := _), LinearMap.add_apply, smul_add]

theorem ker_smul (Y : Pend X) (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) (a : X.G.Kf) (G : (X.Pj j).Xsp) :
    Y.ker j La La' (a • G) = a • Y.ker j La La' G := by
  simp only [Pend.ker, Pend.kerF, map_smul, LinearMap.smul_apply]
  rw [smul_smul, smul_smul, mul_comm]

theorem map_smul_Kf (Y : Pend X) {σ : Type} (a : X.G.Kf) (P : MvPolynomial σ X.G.Kf) :
    MvPolynomial.map (algebraMap X.G.Kf Y.Kc) (a • P) = a • MvPolynomial.map (algebraMap X.G.Kf Y.Kc) P := by
  rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul, algebraMap_smul]

theorem body_of_span (Y : Pend X) (j : ℕ) (cK : Y.Kc) (S : Set (X.Fm j))
    (hS : ∀ F ∈ S, ∀ (c' : X.Lv.comp (j + 1)) (L' : (X.Pj (j + 1)).Tup), (X.Pj (j + 1)).IsLatTup L' →
      MvPolynomial.map (algebraMap X.G.Kf Y.Kc) (X.Kz j F c' L') =
        ∑ La ∈ Y.Rep j, (((X.stab j La : Y.Kc))⁻¹ * cK) • Y.ker j La (c', L') (F La.1 La.2))
    (F : X.Fm j) (hF : F ∈ Submodule.span X.G.Kf S) :
    ∀ (c' : X.Lv.comp (j + 1)) (L' : (X.Pj (j + 1)).Tup), (X.Pj (j + 1)).IsLatTup L' →
      MvPolynomial.map (algebraMap X.G.Kf Y.Kc) (X.Kz j F c' L') =
        ∑ La ∈ Y.Rep j, (((X.stab j La : Y.Kc))⁻¹ * cK) • Y.ker j La (c', L') (F La.1 La.2) := by
  induction hF using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero =>
    intro c' L' _
    simp only [map_zero, Pi.zero_apply, ker_zero, smul_zero, Finset.sum_const_zero]
  | add x y _ _ hx hy =>
    intro c' L' hL
    simp only [map_add (f := _), Pi.add_apply, ker_add, smul_add, Finset.sum_add_distrib, hx c' L' hL, hy c' L' hL]
  | smul a x _ hx =>
    intro c' L' hL
    simp only [map_smul, Pi.smul_apply, ker_smul]
    rw [map_smul_Kf Y, hx c' L' hL, Finset.smul_sum]
    refine Finset.sum_congr rfl fun La _ => ?_
    rw [smul_comm]

section Rec

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Th1.H Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc0 : G.Consts} {Dx : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc0 Dx cX}

theorem sharpQ_qOf {t : KerEntTied ex} {Tw : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup} {i : ℕ}
    {x : ((Tw.fm u μ).lat i).V} (h : ∃ Q, SharpQ t Tw u μ i x Q) : SharpQ t Tw u μ i x (qOf t Tw u μ i x) := by
  unfold qOf
  rw [dite_eq_left h]
  exact Classical.choose_spec h

end Rec

end Formalism.L2.KerInert.K2
end
end
