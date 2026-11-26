module

public import Formalism.LocalToGlobal.GroupLattices.FockModels.OperatorsPreserveLattices
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.HurwitzSubstituteTwoSeries
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.LocalLevelIsKOneAtT
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.RestEntOf
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.PhNorm
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.ReBase
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.ExistsWittSeriesInverseFormalGroupIso

@[expose] public section

section -- merged from Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.AdmissibleThirdOfSecondEleventh
noncomputable section

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.FormalGroupSystem.Pf Formalism.L2.PairingIndexBounds.PowerSeriesNecessity Finset

attribute [local instance] Formalism.L2.G.Pend.wittFractionAlgebraCp

namespace Formalism.L2.KerInert.Ent

variable {p : ℕ} [Fact p.Prime]

theorem geZ_iff (x : ℂ_[p]) : GeZ x ↔ x ∈ Formalism.L2.G.Pend.OcC p := by
  constructor
  · intro h
    have := h 0 1 one_pos (by simp)
    simpa using this
  · intro hx a b _ hab
    have ha : 0 ≤ -a := by
      have : (a : ℝ) ≤ 0 := by simpa using hab
      have : a ≤ 0 := by exact_mod_cast this
      omega
    obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le ha
    rw [hk, zpow_natCast]
    exact Subring.mul_mem _ (Subring.pow_mem _ hx b) (Subring.pow_mem _ (natCast_mem _ p) k)

def GeP {τ : Type} (a : MvPolynomial τ ℂ_[p]) : Prop := ∀ n, AddMonoidAlgebra.coeff a n ∈ Formalism.L2.G.Pend.OcC p

theorem geP_one {τ : Type} : GeP (1 : MvPolynomial τ ℂ_[p]) := by
  classical
  intro n
  rw [MvPolynomial.coeff_one]
  split_ifs
  · exact Subring.one_mem _
  · exact Subring.zero_mem _

theorem geP_mul {τ : Type} {a b : MvPolynomial τ ℂ_[p]} (ha : GeP a) (hb : GeP b) : GeP (a * b) := by
  classical
  intro n
  rw [MvPolynomial.coeff_mul]
  exact Subring.sum_mem _ fun xy _ => Subring.mul_mem _ (ha _) (hb _)

theorem geP_prod {τ α : Type} (s : Finset α) (a : α → MvPolynomial τ ℂ_[p]) (h : ∀ i ∈ s, GeP (a i)) :
    GeP (∏ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (geP_one : GeP (1 : MvPolynomial τ ℂ_[p]))
  | insert x s hx ih =>
    rw [Finset.prod_insert hx]
    exact geP_mul (h x (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem geP_sum {τ α : Type} (s : Finset α) (a : α → MvPolynomial τ ℂ_[p]) (h : ∀ i ∈ s, GeP (a i)) :
    GeP (∑ i ∈ s, a i) := by
  intro n
  rw [MvPolynomial.coeff_sum]
  exact Subring.sum_mem _ fun i hi => h i hi n

theorem geP_smul {τ : Type} {a : MvPolynomial τ ℂ_[p]} {c : ℂ_[p]} (hc : c ∈ Formalism.L2.G.Pend.OcC p) (h : GeP a) :
    GeP (c • a) := by
  intro n
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  exact Subring.mul_mem _ hc (h n)

variable (X : Sys p) (be : MvPowerSeries (Fin 2) (K0 p))

def PhB (j : ℕ) (v : X.Pl) : MvPowerSeries (X.EA j ⊕ X.EA j) (K0 p) :=
  ∑ e : Eidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)),
    sub2 p be (MvPowerSeries.X (Sum.inl (⟨v, e⟩ : X.EA j))) (MvPowerSeries.X (Sum.inr (⟨v, e⟩ : X.EA j)))

def FC (j : ℕ) (v : X.Pl) : MvPowerSeries (X.EA j ⊕ X.EA j) ℂ_[p] :=
  MvPowerSeries.map (algebraMap (K0 p) ℂ_[p]) (expS p (-PhB X be j v))

theorem PhB_supp (j : ℕ) (v : X.Pl) : PhB X be j v ∈ Gen.SuppOn (en_pi X j) v := by
  unfold PhB
  refine Subring.sum_mem _ fun e _ => ?_
  unfold sub2
  refine Gen.subst_mem (π := fun _ : Fin 2 => v) MvPowerSeries.HasSubst.X_X (fun _ _ _ _ => rfl) fun s _ => ?_
  fin_cases s
  · exact Gen.X_mem rfl
  · exact Gen.X_mem rfl

theorem FC_supp (j : ℕ) (v : X.Pl) : FC X be j v ∈ Gen.SuppOn (en_pi X j) v :=
  Gen.map_mem _ (en_expS_supp _ v (Subring.neg_mem _ (PhB_supp X be j v)))

theorem PhB_const (hbe : BeProp p be) (j : ℕ) (v : X.Pl) : MvPowerSeries.constantCoeff (PhB X be j v) = 0 := by
  unfold PhB
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_eq_zero fun e _ => by rw [substitution_of_variables]; exact th_ren_const _ (th_be_const hbe)

def ploc (j : ℕ) (I : X.ColCh j) (i0 : X.Pl → ℕ) (v : X.Pl) :
    MvPolynomial (Zidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1))) (MvPolynomial (X.FrI j) ℂ_[p]) :=
  ∏ s : Fin (X.G.P.n' v), ∏ c ∈ range (X.nuv v (j + 1) s 1).toNat,
    (p : MvPolynomial (Zidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)))
      (MvPolynomial (X.FrI j) ℂ_[p])) ^ (X.colExp j I i0 v s c) *
    Matrix.det (Matrix.of fun (i i' : Fin (X.colHt v (j + 1) s c)) =>
      ∑ a : Fin (NN X.G.P.m X.t j),
        MvPolynomial.C (MvPolynomial.X (⟨v, (s, i.val, a)⟩ : X.FrI j)) *
          MvPolynomial.X ((s, a, I v s c i'.val) :
            Zidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1))))

theorem mapP_PIvS (j : ℕ) (I : X.ColCh j) (i0 : X.Pl → ℕ) (v : X.Pl) :
    en_mapP ℂ_[p] (X.ZA j) (X.FrI j) (PIvS X j I i0 v) =
      MvPolynomial.rename (Sigma.mk v) (ploc X j I i0 v) := by
  unfold PIvS ploc Sys.colFac
  simp only [map_prod, map_mul, map_pow, map_natCast]
  refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => ?_
  congr 1
  rw [RingHom.map_det, AlgHom.map_det]
  congr 1
  ext i i'
  set_option synthInstance.maxHeartbeats 100000 in
    simp [en_mapP, RingHom.mapMatrix_apply, AlgHom.mapMatrix_apply, Matrix.map_apply, map_sum]

theorem geP_applyD_prod_FC_mul (j : ℕ) (hLow : ∀ v, LowZC X be j v)
    (U1 : MvPowerSeries (X.EA j ⊕ X.EA j) ℂ_[p]) (hU1 : IntR (Formalism.L2.G.Pend.OcC p) (inParamK p ℂ_[p] U1))
    (I : X.ColCh j) :
    GeP (applyD (X.PI j I fun _ => 0) (X.ThZA ℂ_[p] j ((∏ v, FC X be j v) * U1))) := by
  classical
  have e1 : X.ThZA ℂ_[p] j ((∏ v, FC X be j v) * U1) = (∏ v, X.ThZA ℂ_[p] j (FC X be j v)) *
      MvPowerSeries.subst (fun i => X.ThZA ℂ_[p] j (en_Ec p ℂ_[p] i)) (inParamK p ℂ_[p] U1) := by
    rw [en_ThZA_mul, en_ThZA_prod]
    congr 1
    conv_lhs => rw [← en_Ec_inParamK p ℂ_[p] U1]
    unfold Sys.ThZA
    rw [MvPowerSeries.subst_comp_subst_apply (en_Ec_hs p ℂ_[p]) (en_coordZA_hs X ℂ_[p] j)]
  have ha : MvPowerSeries.HasSubst (fun i => X.ThZA ℂ_[p] j (en_Ec p ℂ_[p] i)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i =>
      MvPowerSeries.constantCoeff_subst_eq_zero (en_coordZA_hs X ℂ_[p] j) (en_coordZA_zero X ℂ_[p] j)
        (en_Ec_zero p ℂ_[p] i)
  rw [en_applyD_eq, e1]
  obtain ⟨B, hB⟩ := Gen.jp_subst_expand (en_mapP ℂ_[p] (X.ZA j) (X.FrI j) (X.PI j I fun _ => 0))
    (∏ v, X.ThZA ℂ_[p] j (FC X be j v)) (fun i => X.ThZA ℂ_[p] j (en_Ec p ℂ_[p] i)) ha (inParamK p ℂ_[p] U1)
  rw [hB]
  refine geP_sum _ _ fun β _ => geP_smul (hU1 β) ?_
  set Ub : X.Pl → MvPowerSeries (X.EA j ⊕ X.EA j) ℂ_[p] := fun v =>
    ∏ i ∈ β.support.filter (fun i => en_pi X j i = v), (en_Ec p ℂ_[p] i) ^ (β i) with hUb
  have e2 : (β.prod fun i e => X.ThZA ℂ_[p] j (en_Ec p ℂ_[p] i) ^ e) = ∏ v, X.ThZA ℂ_[p] j (Ub v) := by
    unfold Finsupp.prod
    rw [← Finset.prod_fiberwise β.support (en_pi X j)]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [hUb, en_ThZA_prod]
    exact Finset.prod_congr rfl fun i _ => (en_ThZA_pow X ℂ_[p] j _ _).symm
  have e3 : (∏ v, X.ThZA ℂ_[p] j (FC X be j v)) * ∏ v, X.ThZA ℂ_[p] j (Ub v) =
      ∏ v, X.ThZA ℂ_[p] j (FC X be j v * Ub v) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun v _ => (en_ThZA_mul X ℂ_[p] j _ _).symm
  have hG : ∀ v, X.ThZA ℂ_[p] j (FC X be j v * Ub v) ∈ Gen.SuppOn (Sigma.fst : X.ZA j → X.Pl) v := fun v =>
    en_ThZA_supp X ℂ_[p] j v (Subring.mul_mem _ (FC_supp X be j v) (Subring.prod_mem _ fun i hi =>
      Subring.pow_mem _ (by
        have := en_Ec_supp p ℂ_[p] (en_pi X j) i
        rw [(Finset.mem_filter.1 hi).2] at this
        exact this) _))
  have e4 : ∏ v, X.ThZA ℂ_[p] j (FC X be j v * Ub v) =
      ∏ v, Gen.atP v (Gen.resP v (X.ThZA ℂ_[p] j (FC X be j v * Ub v))) :=
    Finset.prod_congr rfl fun v _ => Gen.eq_atP v _ (hG v)
  have e5 : en_mapP ℂ_[p] (X.ZA j) (X.FrI j) (X.PI j I fun _ => 0) =
      ∏ v, MvPolynomial.rename (Sigma.mk v) (ploc X j I (fun _ => 0) v) := by
    rw [PI_eq_prod, map_prod]
    exact Finset.prod_congr rfl fun v _ => mapP_PIvS X j I _ v
  rw [e2, e3, e4, e5, Gen.jp_prod]
  refine geP_prod _ _ fun v _ => ?_
  have e6 : Gen.jp (ploc X j I (fun _ => 0) v) (Gen.resP v (X.ThZA ℂ_[p] j (FC X be j v * Ub v))) =
      applyD (X.PIv j I v) (X.ThZA ℂ_[p] j (FC X be j v * Ub v)) := by
    rw [← PIvS_zero X j I v, en_applyD_eq, mapP_PIvS]
    conv_rhs => rw [Gen.eq_atP v _ (hG v)]
    rw [Gen.jp_rename]
  rw [e6]
  have hint : IntR (Formalism.L2.G.Pend.OcC p) (inParamK p ℂ_[p] (Ub v)) := by
    rw [hUb, en_inParamK_prod]
    refine en_IntR_prod _ _ fun i _ => ?_
    rw [en_inParamK_pow, en_inParamK_Ec]
    exact en_IntR_pow (en_IntR_X i) _
  exact fun n => (geZ_iff _).1 (hLow v (Ub v) hint I n)

theorem first_kernel_product_factor (j : ℕ) {Th : MvPowerSeries (X.EA j ⊕ X.EA j) ℂ_[p]}
    (hK : ExtensionGeneratorCondition p ℂ_[p] (Formalism.L2.G.Pend.OcC p) be Th) :
    ∃ U1 : MvPowerSeries (X.EA j ⊕ X.EA j) ℂ_[p], IntR (Formalism.L2.G.Pend.OcC p) (inParamK p ℂ_[p] U1) ∧
      Th = (∏ v, FC X be j v) * U1 := by
  obtain ⟨Ph, U0, hTh, hU0, _, hbe, hPh⟩ := hK
  have hcz := charZero_K' p (K0 p)
  have hΨ : (∑ e : X.EA j, sub2 p be (MvPowerSeries.X (Sum.inl e)) (MvPowerSeries.X (Sum.inr e)) :
      MvPowerSeries (X.EA j ⊕ X.EA j) (K0 p)) = ∑ v, PhB X be j v := by
    unfold PhB
    exact Fintype.sum_sigma _
  rw [hΨ] at hPh
  obtain ⟨hc0, h, hh0, hE⟩ := hPh
  have hE0 : E0 p (inParam p (Ph - ∑ v, PhB X be j v)) := ⟨th_inParam_const p hc0, h, hh0, hE⟩
  obtain ⟨w, hw⟩ := exp_neg_integral p hE0
  refine ⟨MvPowerSeries.map (algebraMap (K0 p) ℂ_[p]) (expS p (-(Ph - ∑ v, PhB X be j v))) * U0, ?_, ?_⟩
  · rw [en_inParamK_mul]
    refine en_IntR_mul ?_ hU0
    have e1 : inParam p (expS p (-(Ph - ∑ v, PhB X be j v))) = expK (inParam p (-(Ph - ∑ v, PhB X be j v))) := by
      unfold inParam
      exact th_subst_expK _ (fun i => by
        have := th_lX_const p (K0 p) i
        rwa [Algebra.algebraMap_self, PowerSeries.map_id] at this) (by rw [map_neg, hc0, neg_zero])
    rw [th_inParamK_map p (K0 p) ℂ_[p], ← th_inParam_eq, e1, th_inParam_neg, hw]
    intro n
    rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_map]
    show ‖Formalism.L2.G.Pend.k0ToC p (algebraMap (WW p) (K0 p) _)‖ ≤ 1
    rw [Formalism.L2.G.Pend.witt_fraction_to_Cp_algebraMap]
    exact Formalism.L2.G.Pend.norm_wToC_le p _
  · have e2 : -Ph = ∑ v, (-PhB X be j v) + -(Ph - ∑ v, PhB X be j v) := by
      rw [Finset.sum_neg_distrib]; ring
    have e3 : expS p (-Ph) = (∏ v, expS p (-PhB X be j v)) * expS p (-(Ph - ∑ v, PhB X be j v)) := by
      have a1 : expK (∑ v, (-PhB X be j v) + -(Ph - ∑ v, PhB X be j v)) =
          expK (∑ v, (-PhB X be j v)) * expK (-(Ph - ∑ v, PhB X be j v)) :=
        expK_add (by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sum]
          exact Finset.sum_eq_zero fun v _ => by rw [map_neg, PhB_const X be hbe, neg_zero])
          (by rw [map_neg, hc0, neg_zero])
      have a2 : expK (∑ v, (-PhB X be j v)) = ∏ v, expK (-PhB X be j v) :=
        th_expK_sum _ _ fun v _ => by rw [map_neg, PhB_const X be hbe, neg_zero]
      rw [e2]
      exact a1.trans (by rw [a2]; rfl)
    rw [hTh, e3, map_mul, map_prod, mul_assoc]
    rfl

theorem ent_of_K1gen (j : ℕ) (hLow : ∀ v, LowZC X be j v) {Th : MvPowerSeries (X.EA j ⊕ X.EA j) ℂ_[p]}
    (hK : ExtensionGeneratorCondition p ℂ_[p] (Formalism.L2.G.Pend.OcC p) be Th) (I : X.ColCh j) (n : X.FrI j →₀ ℕ) :
    GeZ (AddMonoidAlgebra.coeff (applyD (X.PI j I fun _ => 0) (X.ThZA ℂ_[p] j Th)) n) := by
  obtain ⟨U1, hU1, rfl⟩ := first_kernel_product_factor X be j hK
  exact (geZ_iff _).2 (geP_applyD_prod_FC_mul X be j hLow U1 hU1 I n)

end Formalism.L2.KerInert.Ent

namespace Formalism.L2.KerInert

theorem admissible_third_of_low_kernel_law : Adm3OfK1LowerBound := by
  intro p _ X _ E hfin be T pos F hLow H j hj L0 hL0 La' hL' φ I n
  exact Ent.ent_of_K1gen X be j (hLow j hj) (H j hj L0 hL0 La' hL' φ) I n


open Formalism.L2.G.Pend in
theorem low_order_vanishing_of_admissible (D : Formalism.BasicNotions.D7) {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf]
    (E : CEmbC X.G) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (hst : FinStab X.Lv) {g : Formalism.MainNotions.GL3Theta.G1 p}
    (hLT : LTIso g) {T : Type} (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T)
    (F : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p]) :
    Formalism.MainNotions.FormalGroupSystem.adm11 D X (pendT X E hfin hst hLT pos F) → ∀ j < X.mm, ∀ v, LowZC X (beLT hLT) j v :=
  fun h j hj v => h v j hj


open Formalism.L2.G.Pend in
theorem admissible_third_of_second_eleventh (D : Formalism.BasicNotions.D7) {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf]
    (E : CEmbC X.G) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (hst : FinStab X.Lv) {g : Formalism.MainNotions.GL3Theta.G1 p}
    (hLT : LTIso g) {T : Type} (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T)
    (F : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p]) :
    Formalism.MainNotions.FormalGroupSystem.adm2b D X (pendT X E hfin hst hLT pos F) → Formalism.MainNotions.FormalGroupSystem.adm11 D X (pendT X E hfin hst hLT pos F) →
      Formalism.MainNotions.FormalGroupSystem.adm3 D X (pendT X E hfin hst hLT pos F) :=
  fun h2b h11 => (adm_three_iff_representative D X E hfin hst hLT pos F).2
    (admissible_third_of_low_kernel_law X E hfin _ pos F (low_order_vanishing_of_admissible D X E hfin hst hLT pos F h11)
      ((adm_two_pendant_iff_representative D X E hfin hst hLT pos F).1 h2b))

end Formalism.L2.KerInert
end
end

section -- merged from Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.BeProp
section -- merged from Formalism.SharpRestriction.AdmissibleParameterJoins.GandSv
section -- merged from Formalism.SharpRestriction.AdmissibleParameterJoins.GandSu
section -- merged from Formalism.SharpRestriction.AdmissibleParameterJoins.GandSt
noncomputable section

namespace Formalism.MainNotions.J

open MvPowerSeries Formalism.MainNotions.G Formalism.BasicNotions Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta NumberField

section W

variable {p : ℕ} [Fact p.Prime]

theorem mem_W_of_norm (i0 : K0 p →+* ℂ_[p]) (hW : ∀ x : WW p, ‖i0 (algebraMap (WW p) (K0 p) x)‖ ≤ 1) (x : K0 p)
    (hx : ‖i0 x‖ ≤ 1) : ∃ w : WW p, algebraMap (WW p) (K0 p) w = x := by
  first | exact UpperTheory.Reformulated.B.Qi32.mem_W_of_norm .. | (apply UpperTheory.Reformulated.B.Qi32.mem_W_of_norm <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qi32.mem_W_of_norm <;> assumption) | (apply @UpperTheory.Reformulated.B.Qi32.mem_W_of_norm <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qi32.mem_W_of_norm <;> assumption) | (apply @UpperTheory.Reformulated.B.Qi32.mem_W_of_norm <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qi32.mem_W_of_norm p ‹_› i0 hW x hx | exact @UpperTheory.Reformulated.B.Qi32.mem_W_of_norm p ‹_› i0 hW x | exact @UpperTheory.Reformulated.B.Qi32.mem_W_of_norm p ‹_› i0 hW | exact @UpperTheory.Reformulated.B.Qi32.mem_W_of_norm p ‹_› i0 | exact @UpperTheory.Reformulated.B.Qi32.mem_W_of_norm p ‹_› | exact @UpperTheory.Reformulated.B.Qi32.mem_W_of_norm p

theorem cc_Ex {ι K : Type} [Field K] [CharZero K] {f : MvPowerSeries ι K} (hf : constantCoeff f = 0) :
    constantCoeff (Ex f) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_Ex hf]
  simp

theorem cc_lgE (Kc : Type) [Field Kc] [Algebra (K0 p) Kc] (iC : Kc →+* ℂ_[p])
    (th : PowerSeries (WW p)) (th_zero : PowerSeries.constantCoeff th = 0) (lgE : PowerSeries ℂ_[p])
    (th_log : PowerSeries.subst
      (PowerSeries.map (iC.comp ((algebraMap (K0 p) Kc).comp (algebraMap (WW p) (K0 p)))) th)
      (PowerSeries.map (iC.comp (algebraMap (K0 p) Kc)) (logF p)) = lgE) : PowerSeries.constantCoeff lgE = 0 := by
  rw [← th_log]
  exact PowerSeries.constantCoeff_subst_eq_zero (cc_pmap _ th_zero) _ (cc_pmap _ (cc_logF p))

theorem simeq_of {ι : Type} (Kc : Type) [Field Kc] [Algebra (K0 p) Kc] (Oc : Subring Kc)
    (witt_mem_integers_Cp : ∀ x : WW p, algebraMap (K0 p) Kc (algebraMap (WW p) (K0 p) x) ∈ Oc)
    (iC : Kc →+* ℂ_[p]) (iC_int : ∀ x : Kc, x ∈ Oc ↔ ‖iC x‖ ≤ 1)
    (th : PowerSeries (WW p)) (th_zero : PowerSeries.constantCoeff th = 0) (th_unit : IsUnit (PowerSeries.coeff 1 th))
    (lgE : PowerSeries ℂ_[p])
    (th_log : PowerSeries.subst
      (PowerSeries.map (iC.comp ((algebraMap (K0 p) Kc).comp (algebraMap (WW p) (K0 p)))) th)
      (PowerSeries.map (iC.comp (algebraMap (K0 p) Kc)) (logF p)) = lgE)
    (f g : MvPowerSeries ι (K0 p)) (hfg : constantCoeff (f - g) = 0)
    (h : IntegralMv (expMv (subst (diagS lgE) (map (iC.comp (algebraMap (K0 p) Kc)) (f - g))))) :
    FormalGroupSystem.Simeq p f g := by
  have : CharZero Kc := charZero_of_injective_algebraMap (algebraMap (K0 p) Kc).injective
  have hl0 := cc_lgE Kc iC th th_zero lgE th_log
  refine ⟨hfg, ?_⟩
  obtain ⟨U, hU1, hU2⟩ := K1core Kc Oc witt_mem_integers_Cp iC iC_int th th_zero th_unit lgE th_log (f - g) hfg 1 (by
    have h1 : subst (diagS lgE) (1 : MvPowerSeries ι ℂ_[p]) = 1 := by
      rw [← coe_substAlgHom (hs_dg hl0), map_one]
    rw [map_one, h1, one_mul]
    exact h)
  have hU : U = map (algebraMap (K0 p) Kc) (Ex (f - g)) := by
    have h1 : map (algebraMap (K0 p) Kc) (Ex (f - g)) * (map (algebraMap (K0 p) Kc) (expS p (-(f - g))) * U) =
        map (algebraMap (K0 p) Kc) (Ex (f - g)) := by rw [← hU1, mul_one]
    rw [expS_eq_Ex p (by rw [map_neg, hfg, neg_zero]), ← mul_assoc, ← map_mul, mul_comm (Ex (f - g)), Ex_neg_mul hfg,
      map_one, one_mul] at h1
    exact h1
  have e0 : constantCoeff (inParam p (f - g)) = 0 :=
    constantCoeff_subst_eq_zero (hs_dg (cc_logF p)) (cc_dg (cc_logF p)) hfg
  have hP : inParamK p Kc U = map (algebraMap (K0 p) Kc) (expS p (inParam p (f - g))) := by
    rw [expS_eq_Ex p e0, hU]
    show subst (diagS (PowerSeries.map (algebraMap (K0 p) Kc) (logF p))) (map (algebraMap (K0 p) Kc) (Ex (f - g))) =
      map (algebraMap (K0 p) Kc) (Ex (subst (diagS (logF p)) (f - g)))
    rw [← subst_Ex (hs_dg (cc_logF p)) hfg, map_subst (hs_dg (cc_logF p))]
    congr 1
    funext i
    rw [map_dg]
  have hm : ∀ n, ∃ w : WW p, algebraMap (WW p) (K0 p) w = coeff n (expS p (inParam p (f - g))) := fun n =>
    mem_W_of_norm (iC.comp (algebraMap (K0 p) Kc)) (fun x => (iC_int _).mp (witt_mem_integers_Cp x)) _ (by
      have h3 := hU2 n
      rw [hP, coeff_map] at h3
      exact (iC_int _).mp h3)
  choose G hG using hm
  let Gs : MvPowerSeries ι (WW p) := G
  have hGs : map (algebraMap (WW p) (K0 p)) Gs = expS p (inParam p (f - g)) := by
    ext n
    rw [coeff_map]
    exact hG n
  refine ⟨Gs - 1, ?_, ?_⟩
  · have h4 : algebraMap (WW p) (K0 p) (constantCoeff Gs) = 1 := by
      rw [← constantCoeff_map, hGs, expS_eq_Ex p e0, cc_Ex e0]
    rw [map_sub, map_one, sub_eq_zero]
    exact IsFractionRing.injective (WW p) (K0 p) (by rw [h4, map_one])
  · rw [map_sub, map_one, add_sub_cancel, hGs]

end W

end Formalism.MainNotions.J
end
end

noncomputable section

namespace Formalism.MainNotions.J

open MvPowerSeries Formalism.MainNotions.G Formalism.BasicNotions Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta NumberField

section Be

variable {p : ℕ} [Fact p.Prime] (g : G1 p) {σ τ : Type}

theorem lg_pt (hex : PowerSeries.constantCoeff g.ex = 0) (hinv : PowerSeries.subst g.ex g.l = PowerSeries.X)
    {x : MvPowerSeries σ ℂ_[p]} (hx : constantCoeff x = 0) : g.lg (g.pt x) = x := by
  have hax : PowerSeries.HasSubst x := PowerSeries.HasSubst.of_constantCoeff_zero hx
  have hae : PowerSeries.HasSubst g.ex := PowerSeries.HasSubst.of_constantCoeff_zero' hex
  unfold G1.lg G1.pt
  rw [← PowerSeries.subst_comp_subst_apply hae hax, hinv, PowerSeries.subst_X hax]

variable (i0 : K0 p →+* ℂ_[p]) (be : MvPowerSeries (Fin 2) (K0 p)) (ep : ℂ_[p])

theorem be_at (hex : PowerSeries.constantCoeff g.ex = 0)
    (be_tie : subst ![C ep * g.lg (X (0 : Fin 2)), C ep * g.lg (X (1 : Fin 2))] (map i0 be) =
      g.be (X (0 : Fin 2)) (X (1 : Fin 2)))
    {a b : MvPowerSeries τ ℂ_[p]} (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) :
    subst ![C ep * g.lg a, C ep * g.lg b] (map i0 be) = g.be a b := by
  have hlg : ∀ {σ' : Type} {c : σ' → MvPowerSeries τ ℂ_[p]}, HasSubst c → ∀ i : σ',
      subst c (C ep * g.lg (X i)) = C ep * g.lg (c i) := by
    intro σ' c hc i
    have hXi : HasSubst (fun _ : Unit => (X i : MvPowerSeries σ' ℂ_[p])) := by
      have hz : ∀ _ : Unit, constantCoeff (X i : MvPowerSeries σ' ℂ_[p]) = 0 := fun _ => constantCoeff_X i
      first
        | exact hasSubst_of_constantCoeff_zero hz
        | exact HasSubst.of_constantCoeff_zero' hz
        | exact hasSubst_of_constantCoeff_nilpotent (fun j => by rw [hz j]; exact IsNilpotent.zero)
    rw [← smul_eq_C_mul, subst_smul hc, ← smul_eq_C_mul]
    congr 1
    unfold G1.lg PowerSeries.subst
    rw [subst_comp_subst_apply hXi hc]
    simp only [subst_X hc]
  have h0 : ∀ i : Fin 2, constantCoeff (![a, b] i) = 0 := by
    intro i; fin_cases i <;> simpa
  have hc : HasSubst ![a, b] := by
    first
      | exact hasSubst_of_constantCoeff_zero h0
      | exact HasSubst.of_constantCoeff_zero' h0
      | exact hasSubst_of_constantCoeff_nilpotent (fun i => by rw [h0 i]; exact IsNilpotent.zero)
  have hl0 : ∀ i : Fin 2, constantCoeff (g.lg (X i : MvPowerSeries (Fin 2) ℂ_[p])) = 0 := fun i =>
    PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_X i) _ (cc_l g)
  have h1 : ∀ i : Fin 2, constantCoeff
      (![C ep * g.lg (X (0 : Fin 2)), C ep * g.lg (X (1 : Fin 2))] i) = 0 := by
    intro i; fin_cases i <;> simp [hl0]
  have hd : HasSubst ![C ep * g.lg (X (0 : Fin 2)), C ep * g.lg (X (1 : Fin 2))] := by
    first
      | exact hasSubst_of_constantCoeff_zero h1
      | exact HasSubst.of_constantCoeff_zero' h1
      | exact hasSubst_of_constantCoeff_nilpotent (fun i => by rw [h1 i]; exact IsNilpotent.zero)
  have h := congrArg (subst ![a, b]) be_tie
  rw [be_subst g hex hc (constantCoeff_X _) (constantCoeff_X _), subst_X hc, subst_X hc,
    subst_comp_subst_apply hd hc] at h
  have hfun : (fun i => subst ![a, b]
      (![C ep * g.lg (X (0 : Fin 2)), C ep * g.lg (X (1 : Fin 2))] i)) = ![C ep * g.lg a, C ep * g.lg b] := by
    funext i
    fin_cases i
    · exact hlg hc 0
    · exact hlg hc 1
  rw [hfun] at h
  simpa using h

def LogOf (x : MvPowerSeries τ (K0 p)) (a : MvPowerSeries τ ℂ_[p]) : Prop :=
  constantCoeff x = 0 ∧ constantCoeff a = 0 ∧
    subst (diagS (PowerSeries.C ep * g.l)) (map i0 x) = C ep * g.lg a

theorem logOf_X (i : τ) : LogOf g i0 ep (X i) (X i) := by
  refine ⟨constantCoeff_X i, constantCoeff_X i, ?_⟩
  have hc : PowerSeries.constantCoeff (PowerSeries.C ep * g.l) = 0 := by
    rw [map_mul, cc_l, mul_zero]
  rw [map_X, subst_X (hs_dg hc), dg_Cmul]

theorem logOf_add (hex : PowerSeries.constantCoeff g.ex = 0)
    (hinv : PowerSeries.subst g.ex g.l = PowerSeries.X) {x y : MvPowerSeries τ (K0 p)} {a b : MvPowerSeries τ ℂ_[p]}
    (hx : LogOf g i0 ep x a) (hy : LogOf g i0 ep y b) : LogOf g i0 ep (x + y) (g.add a b) := by
  obtain ⟨hx0, ha0, hx1⟩ := hx
  obtain ⟨hy0, hb0, hy1⟩ := hy
  have hc : PowerSeries.constantCoeff (PowerSeries.C ep * g.l) = 0 := by
    rw [map_mul, cc_l, mul_zero]
  have hla : constantCoeff (g.lg a) = 0 := PowerSeries.constantCoeff_subst_eq_zero ha0 _ (cc_l g)
  have hlb : constantCoeff (g.lg b) = 0 := PowerSeries.constantCoeff_subst_eq_zero hb0 _ (cc_l g)
  have hs : constantCoeff (g.lg a + g.lg b) = 0 := by rw [map_add (f := _), hla, hlb, add_zero]
  refine ⟨by rw [map_add (f := _), hx0, hy0, add_zero], ?_, ?_⟩
  · exact PowerSeries.constantCoeff_subst_eq_zero hs _ hex
  · rw [map_add (f := _), subst_add (hs_dg hc), hx1, hy1, G1.add, lg_pt g hex hinv hs, mul_add]

theorem logOf_mul (hex : PowerSeries.constantCoeff g.ex = 0)
    (hinv : PowerSeries.subst g.ex g.l = PowerSeries.X) (c : K0 p) {x : MvPowerSeries τ (K0 p)}
    {a : MvPowerSeries τ ℂ_[p]} (hx : LogOf g i0 ep x a) : LogOf g i0 ep (C c * x) (g.mulBy (i0 c) a) := by
  obtain ⟨hx0, ha0, hx1⟩ := hx
  have hc : PowerSeries.constantCoeff (PowerSeries.C ep * g.l) = 0 := by
    rw [map_mul, cc_l, mul_zero]
  have hla : constantCoeff (g.lg a) = 0 := PowerSeries.constantCoeff_subst_eq_zero ha0 _ (cc_l g)
  have hs : constantCoeff (C (i0 c) * g.lg a) = 0 := by rw [map_mul, hla, mul_zero]
  refine ⟨by rw [map_mul, hx0, mul_zero], ?_, ?_⟩
  · exact PowerSeries.constantCoeff_subst_eq_zero hs _ hex
  · rw [map_mul, map_C, ← smul_eq_C_mul, subst_smul (hs_dg hc), hx1, G1.mulBy, lg_pt g hex hinv hs,
      smul_eq_C_mul]
    ring

theorem subtraction_formal_group_log (hex : PowerSeries.constantCoeff g.ex = 0)
    (be_tie : subst ![C ep * g.lg (X (0 : Fin 2)), C ep * g.lg (X (1 : Fin 2))] (map i0 be) =
      g.be (X (0 : Fin 2)) (X (1 : Fin 2)))
    {x y : MvPowerSeries τ (K0 p)} {a b : MvPowerSeries τ ℂ_[p]}
    (hx : LogOf g i0 ep x a) (hy : LogOf g i0 ep y b) :
    subst (diagS (PowerSeries.C ep * g.l)) (map i0 (sub2 p be x y)) = g.be a b := by
  obtain ⟨hx0, ha0, hx1⟩ := hx
  obtain ⟨hy0, hb0, hy1⟩ := hy
  have hc : PowerSeries.constantCoeff (PowerSeries.C ep * g.l) = 0 := by
    rw [map_mul, cc_l, mul_zero]
  have h0 : ∀ i : Fin 2, constantCoeff (![x, y] i) = 0 := by
    intro i; fin_cases i <;> simpa
  have hs : HasSubst ![x, y] := by
    first
      | exact hasSubst_of_constantCoeff_zero h0
      | exact HasSubst.of_constantCoeff_zero' h0
      | exact hasSubst_of_constantCoeff_nilpotent (fun i => by rw [h0 i]; exact IsNilpotent.zero)
  have h0' : ∀ i : Fin 2, constantCoeff (map i0 (![x, y] i)) = 0 := by
    intro i; rw [constantCoeff_map, h0 i, map_zero]
  have hs' : HasSubst (fun i : Fin 2 => map i0 (![x, y] i)) := by
    first
      | exact hasSubst_of_constantCoeff_zero h0'
      | exact HasSubst.of_constantCoeff_zero' h0'
      | exact hasSubst_of_constantCoeff_nilpotent (fun i => by rw [h0' i]; exact IsNilpotent.zero)
  unfold sub2
  rw [map_subst hs, subst_comp_subst_apply hs' (hs_dg hc)]
  have hfun : (fun i : Fin 2 => subst (diagS (PowerSeries.C ep * g.l)) (map i0 (![x, y] i))) =
      ![C ep * g.lg a, C ep * g.lg b] := by
    funext i
    fin_cases i
    · exact hx1
    · exact hy1
  rw [hfun]
  exact be_at g i0 be ep hex be_tie ha0 hb0

theorem constantCoeff_sub2_eq_zero (hbe : constantCoeff be = 0) {x y : MvPowerSeries τ (K0 p)} (hx : constantCoeff x = 0)
    (hy : constantCoeff y = 0) : constantCoeff (sub2 p be x y) = 0 := by
  have h0 : ∀ i : Fin 2, constantCoeff (![x, y] i) = 0 := by
    intro i; fin_cases i <;> simpa
  have hs : HasSubst ![x, y] := by
    first
      | exact hasSubst_of_constantCoeff_zero h0
      | exact HasSubst.of_constantCoeff_zero' h0
      | exact Formalism.G.LogP.hs2 hx hy
      | exact hasSubst_of_constantCoeff_nilpotent (fun i => by rw [h0 i]; exact IsNilpotent.zero)
  unfold sub2
  first
    | exact constantCoeff_subst_eq_zero hs h0 hbe
    | exact constantCoeff_subst_eq_zero h0 hbe
    | exact MvPowerSeries.constantCoeff_subst_eq_zero hs h0 hbe

end Be

end Formalism.MainNotions.J
end
end

noncomputable section

namespace Formalism.MainNotions.J

open MvPowerSeries Formalism.MainNotions.G Formalism.BasicNotions Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta NumberField

section Ab

variable {p : ℕ} [Fact p.Prime] (g : G1 p)

theorem cc_ph : PowerSeries.constantCoeff g.ph = 0 := by
  rw [Formalism.MainNotions.GL3Theta.G1.ph.eq_1, map_neg, neg_eq_zero]
  show Formalism.MainNotions.GL3Theta.logMv _ 0 = 0
  rw [Formalism.MainNotions.GL3Theta.logMv.eq_1]
  simp

theorem be_ab (i0 : K0 p →+* ℂ_[p]) (be : MvPowerSeries (Fin 2) (K0 p)) (ep : ℂ_[p]) (hep : ep ≠ 0)
    (hex : PowerSeries.constantCoeff g.ex = 0) (hinv : PowerSeries.subst g.ex g.l = PowerSeries.X)
    (be_tie : subst ![C ep * g.lg (X (0 : Fin 2)), C ep * g.lg (X (1 : Fin 2))] (map i0 be) =
      g.be (X (0 : Fin 2)) (X (1 : Fin 2)))
    (n : Fin 2 →₀ ℕ) (hn : coeff n be ≠ 0) : 1 ≤ n 0 ∧ 1 ≤ n 1 := by
  classical
  set c : ℂ_[p] := ep⁻¹ with hc
  set ψ : PowerSeries ℂ_[p] :=
    PowerSeries.subst (PowerSeries.subst (PowerSeries.C c * PowerSeries.X : PowerSeries ℂ_[p]) g.ex) g.ph with hψ
  have hcX : PowerSeries.constantCoeff (PowerSeries.C c * PowerSeries.X : PowerSeries ℂ_[p]) = 0 := by simp
  have hE : PowerSeries.constantCoeff (PowerSeries.subst (PowerSeries.C c * PowerSeries.X : PowerSeries ℂ_[p]) g.ex) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hcX _ hex
  have hψ0 : PowerSeries.coeff 0 ψ = 0 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact PowerSeries.constantCoeff_subst_eq_zero hE _ (cc_ph g)
  have key : ∀ z : MvPowerSeries (Fin 2) ℂ_[p], constantCoeff z = 0 →
      g.phAt (g.pt (C c * z)) = PowerSeries.subst z ψ := by
    intro z hz
    have hz' := PowerSeries.HasSubst.of_constantCoeff_zero hz
    rw [hψ, PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hE) hz',
      PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hcX) hz',
      PowerSeries.subst_mul hz', PowerSeries.subst_C, PowerSeries.subst_X hz']
    rfl
  have h0 : ∀ i : Fin 2, constantCoeff (C c * X i : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := by intro i; simp
  have hB : map i0 be = PowerSeries.subst (X 0 + X 1 : MvPowerSeries (Fin 2) ℂ_[p]) ψ -
      PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) ℂ_[p]) ψ -
      PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) ℂ_[p]) ψ := by
    have h := be_at g i0 be ep hex be_tie (cc_pt g hex (h0 0)) (cc_pt g hex (h0 1))
    rw [lg_pt g hex hinv (h0 0), lg_pt g hex hinv (h0 1)] at h
    have e : (![C ep * (C c * X 0), C ep * (C c * X 1)] : Fin 2 → MvPowerSeries (Fin 2) ℂ_[p]) = X := by
      funext s
      fin_cases s
      · show C ep * (C c * X 0) = X 0
        rw [← mul_assoc, ← map_mul, hc, mul_inv_cancel₀ hep, map_one, one_mul]
      · show C ep * (C c * X 1) = X 1
        rw [← mul_assoc, ← map_mul, hc, mul_inv_cancel₀ hep, map_one, one_mul]
    rw [e, subst_self] at h
    have h' : map i0 be = g.be (g.pt (C c * X 0)) (g.pt (C c * X 1)) := h
    rw [h']
    unfold G1.be G1.add
    rw [lg_pt g hex hinv (h0 0), lg_pt g hex hinv (h0 1), ← mul_add, key _ (by simp), key _ (by simp),
      key _ (by simp)]
  have hco : i0 (coeff n be) = ((n 0 + n 1).choose (n 0) : ℂ_[p]) * PowerSeries.coeff (n 0 + n 1) ψ -
      (if n = Finsupp.single 0 (n 0) then PowerSeries.coeff (n 0) ψ else 0) -
      (if n = Finsupp.single 1 (n 1) then PowerSeries.coeff (n 1) ψ else 0) := by
    rw [← coeff_map, hB, map_sub, map_sub, PowerSeries.coeff_subst_X_zero_add_X_one, PowerSeries.coeff_subst_single,
      PowerSeries.coeff_subst_single]
  by_contra hcon
  apply hn
  apply i0.injective
  rw [map_zero, hco]
  have hcase : n 0 = 0 ∨ n 1 = 0 := by
    by_contra h
    push Not at h
    exact hcon ⟨Nat.one_le_iff_ne_zero.2 h.1, Nat.one_le_iff_ne_zero.2 h.2⟩
  rcases hcase with h | h
  · have e1 : n = Finsupp.single 1 (n 1) := by
      ext i
      fin_cases i
      · simp [h]
      · simp
    rw [if_pos e1, h, zero_add, Nat.choose_zero_right, Nat.cast_one, one_mul]
    split_ifs with h2
    · have : n 1 = 0 := by rw [h2]; simp
      rw [this, hψ0]; ring
    · ring
  · have e1 : n = Finsupp.single 0 (n 0) := by
      ext i
      fin_cases i
      · simp
      · simp [h]
    rw [if_pos e1, h, add_zero, Nat.choose_self, Nat.cast_one, one_mul]
    split_ifs with h2
    · have : n 0 = 0 := by rw [h2]; simp
      rw [this, hψ0]; ring
    · ring

end Ab

variable {D : D7} {Gt : GatTies D} {Tw : TwForms D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
    [Fact (D.what₂.places.resChar w).Prime] {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
    {T : Formalism.MainNotions.TaylorLogMetric.Tor D} {e : Formalism.MainNotions.TaylorLogMetric.FamE D} {X : Sys (D.what₂.places.resChar w)} {Y : Pend X}

end Formalism.MainNotions.J
end
end

noncomputable section

namespace Formalism.L2.KerInert

open MvPowerSeries Formalism.MainNotions.GL3Theta Formalism.L2.G.Pend Formalism.MainNotions.J

section Witt

variable {p : ℕ} [hp : Fact p.Prime]

theorem sig_teich (y : kb p) :
    Formalism.MainNotions.FormalGroupSystem.sigW p (WittVector.teichmuller p y) = WittVector.teichmuller p (y ^ p) := by
  ext n
  show (WittVector.frobenius (WittVector.teichmuller p y)).coeff n = _
  rw [WittVector.coeff_frobenius_charP]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [WittVector.teichmuller_coeff_zero, WittVector.teichmuller_coeff_zero]
  · rw [WittVector.teichmuller_coeff_pos p y n hn, WittVector.teichmuller_coeff_pos p _ n hn,
      zero_pow hp.out.ne_zero]

def pairHom (p : ℕ) [Fact p.Prime] : WW p →+* ℂ_[p] × ℂ_[p] :=
  RingHom.prod (wToC p) ((wToC p).comp (Formalism.MainNotions.FormalGroupSystem.sigW p))

def gensP (p : ℕ) [Fact p.Prime] : Set (ℂ_[p] × ℂ_[p]) :=
  {x : ℂ_[p] × ℂ_[p] | ∃ ζ : ℂ_[p], ζ ^ (p ^ 2 - 1) = 1 ∧ x = (ζ, ζ ^ p)}

theorem teich_mem {y : kb p} (hy : y ^ (p ^ 2) = y) :
    pairHom p (WittVector.teichmuller p y) ∈ Subring.closure (gensP p) := by
  by_cases h0 : y = 0
  · rw [h0, WittVector.teichmuller_zero, map_zero]
    exact zero_mem _
  · apply Subring.subset_closure
    refine ⟨wToC p (WittVector.teichmuller p y), ?_, ?_⟩
    · have h1 : y ^ (p ^ 2 - 1) * y = 1 * y := by
        rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_pow _ _ hp.out.pos), hy, one_mul]
      have h2 : y ^ (p ^ 2 - 1) = 1 := mul_right_cancel₀ h0 h1
      rw [← map_pow, ← map_pow, h2, map_one, map_one]
    · show (wToC p (WittVector.teichmuller p y), wToC p (Formalism.MainNotions.FormalGroupSystem.sigW p (WittVector.teichmuller p y))) = _
      rw [sig_teich, map_pow, map_pow]

theorem coeff_fix {α : WW p} (hα : (Formalism.MainNotions.FormalGroupSystem.sigW p)^[2] α = α) (i : ℕ) :
    α.coeff i ^ (p ^ 2) = α.coeff i := by
  have h2 : Formalism.MainNotions.FormalGroupSystem.sigW p (Formalism.MainNotions.FormalGroupSystem.sigW p α) = α := hα
  have h3 := congrArg (fun x : WW p => x.coeff i) h2
  have e : ∀ x : WW p, (Formalism.MainNotions.FormalGroupSystem.sigW p x).coeff i = x.coeff i ^ p := fun x =>
    WittVector.coeff_frobenius_charP (p := p) x i
  rw [e, e, ← pow_mul, ← sq] at h3
  exact h3

theorem pair_mem_W2pair {α : WW p} (hα : (Formalism.MainNotions.FormalGroupSystem.sigW p)^[2] α = α) :
    (wToC p α, wToC p (Formalism.MainNotions.FormalGroupSystem.sigW p α)) ∈ W2pair p := by
  show pairHom p α ∈ closure (Subring.closure (gensP p) : Set (ℂ_[p] × ℂ_[p]))
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (r_lt_one p)
  obtain ⟨c, hc⟩ := WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff α n
  set S := ∑ i ∈ Finset.Iic n, WittVector.teichmuller p
    (((_root_.frobeniusEquiv (kb p) p).symm ^ i) (α.coeff i)) * (p : WW p) ^ i with hS
  refine ⟨pairHom p S, ?_, ?_⟩
  · set_option synthInstance.maxHeartbeats 100000 in
    rw [hS, map_sum]
    refine Subring.sum_mem _ fun i _ => ?_
    rw [map_mul, map_pow, map_natCast]
    refine Subring.mul_mem _ (teich_mem ?_) (Subring.pow_mem _ (natCast_mem _ p) i)
    rw [← map_pow, coeff_fix hα]
  · rw [dist_eq_norm, ← map_sub, hc, Prod.norm_def]
    have h1 : ‖wToC p ((p : WW p) ^ (n + 1) * c)‖ ≤ ((p : ℝ)⁻¹) ^ (n + 1) := norm_wToC_pow_mul p (n + 1) c
    have h2 : ‖wToC p (Formalism.MainNotions.FormalGroupSystem.sigW p ((p : WW p) ^ (n + 1) * c))‖ ≤ ((p : ℝ)⁻¹) ^ (n + 1) := by
      rw [map_mul, map_pow, map_natCast]
      exact norm_wToC_pow_mul p (n + 1) _
    have h3 : ((p : ℝ)⁻¹) ^ (n + 1) ≤ ((p : ℝ)⁻¹) ^ n :=
      pow_le_pow_of_le_one (r_nonneg p) (r_lt_one p).le (Nat.le_succ n)
    exact lt_of_le_of_lt (max_le (h1.trans h3) (h2.trans h3)) hn

theorem okp_of (D : Formalism.BasicNotions.D7) (lam : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ_[p]) (h2 : p ≠ 2) (hin : InertK D p) {α : WW p}
    (hα : (Formalism.MainNotions.FormalGroupSystem.sigW p)^[2] α = α) : (wToC p α, wToC p (Formalism.MainNotions.FormalGroupSystem.sigW p α)) ∈ OKp D lam := by
  rw [Formalism.MainNotions.Ext.okpInert_holds D p lam h2 hin]
  exact pair_mem_W2pair hα

end Witt

section Be

variable {p : ℕ} [hp : Fact p.Prime]

theorem integralMv_of_integralW {σ : Type*} {F : MvPowerSeries σ ℂ_[p]} (h : IntegralW F) : Formalism.MainNotions.TaylorLogMetric.IntegralMv F := by
  intro n
  obtain ⟨w, hw⟩ := (mem_Wp_iff p _).1 (h n)
  show ‖_‖ ≤ 1
  rw [← hw]
  exact norm_wToC_le p w

theorem be_props_at (D : Formalism.BasicNotions.D7) (g : G1 p) (hLT : LTIso g) (hOk : g.Ok) (h2 : p ≠ 2) (hin : InertK D p)
    (hM : ModelOverW g.lam g.abelian₂ g.C) (hB : BeWAt D g) :
    (∀ n : Fin 2 →₀ ℕ, coeff n (beLT hLT) ≠ 0 → 1 ≤ n 0 ∧ 1 ≤ n 1) ∧
    Formalism.MainNotions.FormalGroupSystem.Simeq p (Formalism.MainNotions.FormalGroupSystem.sub2 p (beLT hLT) (MvPowerSeries.X 0 + MvPowerSeries.X 1) (MvPowerSeries.X 2) -
              Formalism.MainNotions.FormalGroupSystem.sub2 p (beLT hLT) (MvPowerSeries.X 0) (MvPowerSeries.X 2) -
              Formalism.MainNotions.FormalGroupSystem.sub2 p (beLT hLT) (MvPowerSeries.X 1) (MvPowerSeries.X 2))
      (0 : MvPowerSeries (Fin 3) (K0 p)) ∧
    Formalism.MainNotions.FormalGroupSystem.Simeq p (Formalism.MainNotions.FormalGroupSystem.sub2 p (beLT hLT) (MvPowerSeries.X 0) (MvPowerSeries.X 1 + MvPowerSeries.X 2) -
              Formalism.MainNotions.FormalGroupSystem.sub2 p (beLT hLT) (MvPowerSeries.X 0) (MvPowerSeries.X 1) -
              Formalism.MainNotions.FormalGroupSystem.sub2 p (beLT hLT) (MvPowerSeries.X 0) (MvPowerSeries.X 2))
      (0 : MvPowerSeries (Fin 3) (K0 p)) ∧
    ∀ α : WW p, (Formalism.MainNotions.FormalGroupSystem.sigW p)^[2] α = α →
      Formalism.MainNotions.FormalGroupSystem.Simeq p
        (Formalism.MainNotions.FormalGroupSystem.sub2 p (beLT hLT) (C (algebraMap (WW p) (K0 p) α) * MvPowerSeries.X (0 : Fin 2)) (MvPowerSeries.X 1))
        (Formalism.MainNotions.FormalGroupSystem.sub2 p (beLT hLT) (MvPowerSeries.X 0)
          (C (algebraMap (WW p) (K0 p) (Formalism.MainNotions.FormalGroupSystem.sigW p α)) * MvPowerSeries.X 1)) := by
  have hex : PowerSeries.constantCoeff g.ex = 0 := hOk.2.2.1
  have hinv : PowerSeries.subst g.ex g.l = PowerSeries.X := hOk.2.2.2
  set ep : ℂ_[p] := wToC p (epOf hLT : WW p) with hep
  have hep0 : ep ≠ 0 := wToC_unit_ne _
  have hrat : BeRat g ep := by
    rw [hep, ← witt_fraction_to_Cp_algebraMap]
    exact beRat_of g hex hB.1 (exRat_of g hOk hM) _
  set i0 : K0 p →+* ℂ_[p] := (k0ToC p).comp (algebraMap (K0 p) (K0 p)) with hi0
  have hi0' : i0 = k0ToC p := by rw [hi0, Algebra.algebraMap_self, RingHom.comp_id]
  have hi0W : ∀ x : WW p, i0 (algebraMap (WW p) (K0 p) x) = wToC p x := by
    intro x
    rw [hi0', witt_fraction_to_Cp_algebraMap]
  have htie : subst ![C ep * g.lg (MvPowerSeries.X (0 : Fin 2)), C ep * g.lg (MvPowerSeries.X (1 : Fin 2))]
      (map i0 (beLT hLT)) = g.be (MvPowerSeries.X (0 : Fin 2)) (MvPowerSeries.X (1 : Fin 2)) := by
    rw [hi0']
    exact be_tie hOk hep0 hrat
  have hlog : PowerSeries.subst
      (PowerSeries.map ((k0ToC p).comp ((algebraMap (K0 p) (K0 p)).comp (algebraMap (WW p) (K0 p)))) (thOf hLT))
      (PowerSeries.map ((k0ToC p).comp (algebraMap (K0 p) (K0 p))) (Formalism.MainNotions.FormalGroupSystem.logF p)) = PowerSeries.C ep * g.l := by
    have e1 : (k0ToC p).comp ((algebraMap (K0 p) (K0 p)).comp (algebraMap (WW p) (K0 p))) = wToC p := by
      rw [Algebra.algebraMap_self, RingHom.id_comp]
      exact wToC_eq
    have e2 : (k0ToC p).comp (algebraMap (K0 p) (K0 p)) = k0ToC p := by
      rw [Algebra.algebraMap_self, RingHom.comp_id]
    rw [e1, e2]
    exact thOf_log hLT
  have hab := be_ab g i0 (beLT hLT) ep hep0 hex hinv htie
  have hbe : constantCoeff (beLT hLT) = 0 := by
    by_contra h0
    have := (hab 0 (by rwa [coeff_zero_eq_constantCoeff_apply])).1
    simp at this
  have hs3 := hs_dg (ι := Fin 3) (cc_Cl g ep)
  have hs2' := hs_dg (ι := Fin 2) (cc_Cl g ep)
  have lX3 := fun i : Fin 3 => logOf_X g i0 ep i
  have lX2 := fun i : Fin 2 => logOf_X g i0 ep i
  let Oc : Subring (K0 p) := (algebraMap (WW p) (K0 p)).range
  have witt_mem_integers_Cp : ∀ x : WW p, algebraMap (K0 p) (K0 p) (algebraMap (WW p) (K0 p) x) ∈ Oc := by
    intro x
    rw [Algebra.algebraMap_self, RingHom.id_apply]
    exact ⟨x, rfl⟩
  have iC_int : ∀ x : K0 p, x ∈ Oc ↔ ‖k0ToC p x‖ ≤ 1 := by
    intro x
    rw [norm_k0ToC_le_iff]
    rfl
  have sim := fun (ι : Type) => simeq_of (ι := ι) (K0 p) Oc witt_mem_integers_Cp (k0ToC p) iC_int (thOf hLT) (thOf_zero hLT)
    (thOf_unit hLT) _ hlog
  refine ⟨hab, ?_, ?_, ?_⟩
  · have l01 := logOf_add g i0 ep hex hinv (lX3 0) (lX3 1)
    refine sim (Fin 3) _ _ ?_ ?_
    · rw [sub_zero, map_sub, map_sub, constantCoeff_sub2_eq_zero (beLT hLT) hbe l01.1 (lX3 2).1, constantCoeff_sub2_eq_zero (beLT hLT) hbe (lX3 0).1 (lX3 2).1,
        constantCoeff_sub2_eq_zero (beLT hLT) hbe (lX3 1).1 (lX3 2).1]
      simp
    · rw [sub_zero, map_sub, map_sub, subst_sub hs3, subst_sub hs3, subtraction_formal_group_log g i0 (beLT hLT) _ hex htie l01 (lX3 2),
        subtraction_formal_group_log g i0 (beLT hLT) _ hex htie (lX3 0) (lX3 2), subtraction_formal_group_log g i0 (beLT hLT) _ hex htie (lX3 1) (lX3 2), sub_sub]
      exact integralMv_of_integralW hB.2.1.2
  · have l12 := logOf_add g i0 ep hex hinv (lX3 1) (lX3 2)
    refine sim (Fin 3) _ _ ?_ ?_
    · rw [sub_zero, map_sub, map_sub, constantCoeff_sub2_eq_zero (beLT hLT) hbe (lX3 0).1 l12.1, constantCoeff_sub2_eq_zero (beLT hLT) hbe (lX3 0).1 (lX3 1).1,
        constantCoeff_sub2_eq_zero (beLT hLT) hbe (lX3 0).1 (lX3 2).1]
      simp
    · rw [sub_zero, map_sub, map_sub, subst_sub hs3, subst_sub hs3, subtraction_formal_group_log g i0 (beLT hLT) _ hex htie (lX3 0) l12,
        subtraction_formal_group_log g i0 (beLT hLT) _ hex htie (lX3 0) (lX3 1), subtraction_formal_group_log g i0 (beLT hLT) _ hex htie (lX3 0) (lX3 2), sub_sub]
      exact integralMv_of_integralW hB.2.2.1.2
  · intro α hα
    have la := logOf_mul g i0 ep hex hinv (algebraMap (WW p) (K0 p) α) (lX2 0)
    have lb := logOf_mul g i0 ep hex hinv (algebraMap (WW p) (K0 p) (Formalism.MainNotions.FormalGroupSystem.sigW p α)) (lX2 1)
    refine sim (Fin 2) _ _ ?_ ?_
    · rw [map_sub, constantCoeff_sub2_eq_zero (beLT hLT) hbe la.1 (lX2 1).1, constantCoeff_sub2_eq_zero (beLT hLT) hbe (lX2 0).1 lb.1, sub_zero]
    · rw [map_sub, subst_sub hs2', subtraction_formal_group_log g i0 (beLT hLT) _ hex htie la (lX2 1),
        subtraction_formal_group_log g i0 (beLT hLT) _ hex htie (lX2 0) lb]
      have hok := okp_of D g.lam h2 hin hα
      rw [← hi0W, ← hi0W] at hok
      exact integralMv_of_integralW (hB.2.2.2 _ hok).2

theorem beProp_of_ok (D : Formalism.BasicNotions.D7) (g : G1 p) (hLT : LTIso g) (hOk : g.Ok) (h2 : p ≠ 2) (hin : InertK D p)
    (hM : ModelOverW g.lam g.abelian₂ g.C) (hB : BeWAt D g) : Formalism.MainNotions.FormalGroupSystem.BeProp p (beLT hLT) := by
  obtain ⟨h1, h2', h3, h4⟩ := be_props_at D g hLT hOk h2 hin hM hB
  refine ⟨h1, h2', h3, ?_⟩
  intro α hα
  exact h4 α hα

end Be

theorem beta_property_of_weight : BePropOfBeW := by
  intro D cc δ p _ g hLT hAt h5 hin hM hB
  exact beProp_of_ok D g hLT hAt.2.2.2.2 (by omega) hin hM hB

theorem admissible_second_at_place : Adm2cAt := by
  intro D cc δ p _ g hLT hAt h5 hin hM hB X Y hY
  show Formalism.MainNotions.FormalGroupSystem.BeProp p Y.be
  rw [hY]
  exact beta_property_of_weight D cc δ p g hLT hAt h5 hin hM hB

end Formalism.L2.KerInert
end
end

section -- merged from Formalism.LocalToGlobal.InertKernelTheory.FinalA
section -- merged from Formalism.LocalToGlobal.InertKernelTheory.AdmissibleAllLevels
namespace Formalism.L2.KerInert

def Adm8All : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (p : ℕ) [Fact p.Prime] (X : Formalism.MainNotions.FormalGroupSystem.Sys p), Formalism.MainNotions.FormalGroupSystem.adm8 D X

theorem admissible_all_levels : Adm8All := fun D _ _ X =>
  ⟨Formalism.MainNotions.G.LatticeSystems.exponent_condition_holds D X.G, (Formalism.L2.G.Model.operators_preserve_lattices D X.G).2⟩

end Formalism.L2.KerInert
end

namespace Formalism.L2.KerInert

open Formalism.MainNotions.GL3Theta Formalism.L2.G.Pend

def FactsA : Prop := Sigma.InvAlg ∧ Sigma.SecondEisensteinAlgebraic ∧ EndIntInert ∧ PhNormOKInert

theorem beWInert_ofA (h : FactsA) : BeWInert :=
  beWInert_of_sigma (Sigma.sigmaCurveInert_of h.1 h.2.1) h.2.2.1 h.2.2.2

theorem beProp_ofA (h : FactsA) (D : Formalism.BasicNotions.D7) (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (δ : ℂ) (p : ℕ)
    [Fact p.Prime] (g : G1 p) (hLT : LTIso g) (hAt : At D cc δ g) (h5 : 5 ≤ p) (hin : InertK D p)
    (hW : ModelOverW g.lam g.abelian₂ g.C) : Formalism.MainNotions.FormalGroupSystem.BeProp p (beLT hLT) :=
  beta_property_of_weight D cc δ p g hLT hAt h5 hin hW (beWInert_ofA h D p cc δ g hAt h5 hin hW)

theorem admissible_second_of_facts (h : FactsA) (D : Formalism.BasicNotions.D7) (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (δ : ℂ) (p : ℕ)
    [Fact p.Prime] (g : G1 p) (hLT : LTIso g) (hAt : At D cc δ g) (h5 : 5 ≤ p) (hin : InertK D p)
    (hW : ModelOverW g.lam g.abelian₂ g.C) (X : Formalism.MainNotions.FormalGroupSystem.Sys p) (Y : Formalism.MainNotions.FormalGroupSystem.Pend X) (hY : Y.be = beLT hLT) :
    Formalism.MainNotions.FormalGroupSystem.adm2c D X Y :=
  admissible_second_at_place D cc δ p g hLT hAt h5 hin hW (beWInert_ofA h D p cc δ g hAt h5 hin hW) X Y hY

theorem admissible_eleventh_of_facts (h : FactsA) (D : Formalism.BasicNotions.D7) (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (δ : ℂ) (p : ℕ)
    [Fact p.Prime] (g : G1 p) (hLT : LTIso g) (hAt : At D cc δ g) (h5 : 5 ≤ p) (hin : InertK D p)
    (hW : ModelOverW g.lam g.abelian₂ g.C) (X : Formalism.MainNotions.FormalGroupSystem.Sys p) (Y : Formalism.MainNotions.FormalGroupSystem.Pend X) (hY : Y.be = beLT hLT) :
    Formalism.MainNotions.FormalGroupSystem.adm11 D X Y :=
  Jet.adm11OfBeProp D p X Y (hY ▸ beProp_ofA h D cc δ p g hLT hAt h5 hin hW)

end Formalism.L2.KerInert
end

namespace Formalism.L2.KerInert

open Formalism.MainNotions.GL3Theta Formalism.L2.G.Pend

theorem inert_facts_first_hold : FactsA :=
  ⟨Sigma.invAlg', Sigma.secondEisensteinAlgebraic, endomorphisms_integral_inert, phi_norm_inert_prime⟩

theorem admissible_second_inert (D : Formalism.BasicNotions.D7) (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (δ : ℂ) (p : ℕ)
    [Fact p.Prime] (g : G1 p) (hLT : LTIso g) (hAt : At D cc δ g) (h5 : 5 ≤ p) (hin : InertK D p)
    (hW : ModelOverW g.lam g.abelian₂ g.C) (X : Formalism.MainNotions.FormalGroupSystem.Sys p) (Y : Formalism.MainNotions.FormalGroupSystem.Pend X) (hY : Y.be = beLT hLT) :
    Formalism.MainNotions.FormalGroupSystem.adm2c D X Y :=
  admissible_second_of_facts inert_facts_first_hold D cc δ p g hLT hAt h5 hin hW X Y hY

theorem admissible_eleventh_inert (D : Formalism.BasicNotions.D7) (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (δ : ℂ) (p : ℕ)
    [Fact p.Prime] (g : G1 p) (hLT : LTIso g) (hAt : At D cc δ g) (h5 : 5 ≤ p) (hin : InertK D p)
    (hW : ModelOverW g.lam g.abelian₂ g.C) (X : Formalism.MainNotions.FormalGroupSystem.Sys p) (Y : Formalism.MainNotions.FormalGroupSystem.Pend X) (hY : Y.be = beLT hLT) :
    Formalism.MainNotions.FormalGroupSystem.adm11 D X Y :=
  admissible_eleventh_of_facts inert_facts_first_hold D cc δ p g hLT hAt h5 hin hW X Y hY

end Formalism.L2.KerInert
