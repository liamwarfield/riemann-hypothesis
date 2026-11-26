module

public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.BridgeTwoMore
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalC
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.Wp3ApplyEqSqMulSubSqMul
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.RealAdelicInertTransportTypeFormsEqAlt

@[expose] public section

section -- merged from Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.FirstLevelOfThreeVarParallelogram
noncomputable section

namespace Formalism.L2.Th1.B.E3

open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 in3 swap2 DivAB equivalence_rules)

theorem parallelogram_three_sub_pairs {K : Type} [NormedField K] [CharZero K] (F : MvPowerSeries (Fin 2) K)
    (hF : MvPowerSeries.constantCoeff F = 0) (i f : PowerSeries K)
    (hi : PowerSeries.constantCoeff i = 0) :
    par3 F i f -
        MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 1]
          (par F i f) -
        MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2]
          (par F i f) -
        MvPowerSeries.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2]
          (par F i f) =
      d1 F (cob F f) := by
  have h0 : ∀ j : Fin 3, MvPowerSeries.constantCoeff (MvPowerSeries.X j : MvPowerSeries (Fin 3) K) = 0 :=
    fun j => MvPowerSeries.constantCoeff_X j
  rw [parallelogram_coboundary_three_vars F hF f, cube_par_subst F hF i f hi _ _ (h0 0) (h0 1),
    cube_par_subst F hF i f hi _ _ (h0 0) (h0 2), cube_par_subst F hF i f hi _ _ (h0 1) (h0 2)]
  unfold par3 F3 lawDifferenceThree in3 at1
  ring

theorem cube_relation_from_parallelograms : CubeFromPars := by
  intro K _ _ _ F l i f hF hi hp h3
  obtain ⟨_, hsymm, _, hadd, _⟩ := equivalence_rules K (Fin 3)
  have hsubS : ∀ a b : MvPowerSeries (Fin 3) K, Simeq a 0 → Simeq b 0 → Simeq (a - b) 0 := by
    intro a b ha hb
    have h := hadd a 0 0 b ha (hsymm _ _ hb)
    rw [add_zero, zero_add] at h
    unfold Simeq at h ⊢
    simpa using h
  have hpar : ∀ j k : Fin 3,
      Simeq (MvPowerSeries.subst ![(MvPowerSeries.X j : MvPowerSeries (Fin 3) K), MvPowerSeries.X k]
        (par F i f)) 0 := by
    intro j k
    have hc : ∀ m : Fin 2, MvPowerSeries.constantCoeff
        (![(MvPowerSeries.X j : MvPowerSeries (Fin 3) K), MvPowerSeries.X k] m) = 0 := by
      intro m; fin_cases m <;> simp
    have hI : ∀ m : Fin 2, Integral
        (![(MvPowerSeries.X j : MvPowerSeries (Fin 3) K), MvPowerSeries.X k] m) := by
      intro m; fin_cases m <;> simp [integral_mvPowerSeries_X]
    have h := (equivalence_rules K (Fin 2)).2.2.2.2 (Fin 3) (par F i f) 0 _ hc hI hp
    have hz : MvPowerSeries.subst ![(MvPowerSeries.X j : MvPowerSeries (Fin 3) K), MvPowerSeries.X k]
        (0 : MvPowerSeries (Fin 2) K) = 0 := by
      rw [← MvPowerSeries.coe_substAlgHom (MvPowerSeries.hasSubst_of_constantCoeff_zero hc), map_zero]
    rwa [hz] at h
  rw [← parallelogram_three_sub_pairs F hF.1 i f hi.1]
  exact hsubS _ _ (hsubS _ _ (hsubS _ _ h3 (hpar 0 1)) (hpar 0 2)) (hpar 1 2)

theorem log_sigma_pullback_cocycle_jets_of_parallelogram_and_cube (hP : ParThree) (hC : CubeFromPars) : LogSigmaPullbackCocycleJets := by
  intro K _ _ _ g2 g3 s2 c0 a1 a3 P l i ep F hW hF hi hc hc3
  have hpar := parO K g2 g3 s2 c0 P l i ep F hW hF hi hc
  have hp3 := hP K g2 g3 s2 c0 a1 a3 P l i ep F hW hF hi hc hc3
  have hd := hC K F l i (phO s2 P l) hF hi hpar hp3
  have hf0 := constantCoeff_eq_zero_of_parallelogram hF hi hpar
  obtain ⟨hdiv, hsw⟩ := cobRules K F l (phO s2 P l) hF hf0
  refine ⟨hdiv, hsw, hd, ?_, fun n hn => jetsThree K F l _ hF hd n hn⟩
  rw [hsw]
  exact hd

end Formalism.L2.Th1.B.E3
end
end

section -- merged from Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.ConstantCoeffLawWithInverseThree
noncomputable section

namespace Formalism.L2.Th1.B.E2

open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob in3)
open Formalism.G.LogP (hs2 hs3 subst2_subst psubst_subst subst_XX subst_zero')

section Div

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K]

theorem integral_add {ι : Type} {f g : MvPowerSeries ι K} (hf : Integral f) (hg : Integral g) :
    Integral (f + g) := by
  intro n
  rw [map_add (f := _)]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hf n) (hg n))

theorem integral_neg {ι : Type} {f : MvPowerSeries ι K} (hf : Integral f) : Integral (-f) := by
  intro n
  rw [map_neg, norm_neg]
  exact hf n

theorem integral_sub {ι : Type} {f g : MvPowerSeries ι K} (hf : Integral f) (hg : Integral g) :
    Integral (f - g) := by
  rw [sub_eq_add_neg]
  exact integral_add hf (integral_neg hg)

theorem div_diag {G : MvPowerSeries (Fin 2) K} (hG : Integral G)
    (hd : MvPowerSeries.subst
      ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K), MvPowerSeries.X 1] G = 0) :
    ∃ n : MvPowerSeries (Fin 2) K, Integral n ∧ G = (MvPowerSeries.X 0 - MvPowerSeries.X 1) * n := by
  have c0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have c1 : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have cz : MvPowerSeries.constantCoeff (0 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have cs : MvPowerSeries.constantCoeff
      (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have cd : MvPowerSeries.constantCoeff
      (MvPowerSeries.X 0 - MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have i0 := integral_mvPowerSeries_X (K := K) (0 : Fin 2)
  have i1 := integral_mvPowerSeries_X (K := K) (1 : Fin 2)
  obtain ⟨H, hH⟩ : ∃ H, H = MvPowerSeries.subst
      ![(MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K), MvPowerSeries.X 1] G :=
    ⟨_, rfl⟩
  have iH : Integral H := by
    rw [hH]
    exact integral_subst_two_variables hG _ _ cs c1 (integral_add i0 i1) i1
  have hH0 : MvPowerSeries.subst ![0, (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)] H = 0 := by
    have hb := hs2 cz c1
    rw [hH, subst2_subst G cs c1 hb, MvPowerSeries.subst_add hb, MvPowerSeries.subst_X hb,
      MvPowerSeries.subst_X hb]
    simpa using hd
  have hdvd : (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ∣ H := by
    rw [MvPowerSeries.X_dvd_iff]
    intro m hm
    rw [law_coeff_axis1 H m hm, hH0, map_zero]
  obtain ⟨H1, e1⟩ := hdvd
  have iH1 : Integral H1 := by
    intro n
    have := iH (Finsupp.single 0 1 + n)
    rwa [e1, MvPowerSeries.X_def, MvPowerSeries.coeff_add_monomial_mul, one_mul] at this
  have hb := hs2 cd c1
  refine ⟨MvPowerSeries.subst
    ![(MvPowerSeries.X 0 - MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K), MvPowerSeries.X 1] H1,
    integral_subst_two_variables iH1 _ _ cd c1 (integral_sub i0 i1) i1, ?_⟩
  have e2 : MvPowerSeries.subst
      ![(MvPowerSeries.X 0 - MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K), MvPowerSeries.X 1] H =
      G := by
    rw [hH, subst2_subst G cs c1 hb, MvPowerSeries.subst_add hb, MvPowerSeries.subst_X hb,
      MvPowerSeries.subst_X hb]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, sub_add_cancel]
    exact subst_XX G
  rw [← e2, e1, MvPowerSeries.subst_mul hb, MvPowerSeries.subst_X hb]
  rfl

end Div

theorem formal_inverse_unit_holds : FIUnit := by
  intro K _ _ _ F l i hF hi
  have c0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have c1 : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have cz : MvPowerSeries.constantCoeff (0 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have ci : MvPowerSeries.constantCoeff (at1 (1 : Fin 2) i) = 0 := constantCoeff_series_at_variable 1 i hi.1
  have hd : MvPowerSeries.subst
      ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K), MvPowerSeries.X 1] (FI F i) = 0 := by
    have hb := hs2 c1 c1
    unfold FI
    rw [subst2_subst F c0 ci hb, MvPowerSeries.subst_X hb, subst_at_variable_eq_subst i 1 hb]
    refine law_eq_of_log hF _ _ 0 c1 (constantCoeff_series_at_variable 1 i hi.1) cz ?_
    rw [law_subst_zero l hF.2.2.1]
    have := log_subst_formal_inverse hi (1 : Fin 2)
    change PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) l +
      PowerSeries.subst (at1 (1 : Fin 2) i) l = 0
    rw [this]
    exact add_neg_cancel _
  obtain ⟨n, hn, e⟩ := div_diag (law_integral_FI hF hi) hd
  refine ⟨n, hn, ?_, e⟩
  have h1 : MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1) (FI F i) = 1 := by
    have hb := hs2 c0 cz
    rw [law_coeff_axis0 _ _ (by simp)]
    unfold FI
    rw [subst2_subst F c0 ci hb, MvPowerSeries.subst_X hb, subst_at_variable_eq_subst i 1 hb]
    have e0 : PowerSeries.subst ((![MvPowerSeries.X 0, 0] : Fin 2 → MvPowerSeries (Fin 2) K) 1) i =
        0 := PowerSeries.subst_zero_of_constantCoeff_zero hi.1
    rw [e0]
    change MvPowerSeries.coeff _ (MvPowerSeries.subst ![MvPowerSeries.X 0, 0] F) = 1
    rw [law_right_zero hF _ c0]
    simp [MvPowerSeries.coeff_X]
  rw [e, sub_mul, map_sub] at h1
  have a0 : MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1) (MvPowerSeries.X 0 * n) =
      MvPowerSeries.constantCoeff n := by
    have := MvPowerSeries.coeff_add_monomial_mul (Finsupp.single (0 : Fin 2) 1) 0 n (1 : K)
    rwa [add_zero, one_mul] at this
  have a1 : MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1) (MvPowerSeries.X 1 * n) = 0 := by
    have hx : (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) ∣ MvPowerSeries.X 1 * n :=
      Dvd.intro _ rfl
    exact MvPowerSeries.X_dvd_iff.1 hx _ (by simp)
  rw [a0, a1, sub_zero] at h1
  exact h1

section Alg

variable {K : Type} [Field K] [CharZero K]

theorem fExp_three {ι : Type} {f : MvPowerSeries ι K} (hf : MvPowerSeries.constantCoeff f = 0) :
    fExp (3 * f) = fExp f ^ 3 := by
  have h2 : MvPowerSeries.constantCoeff (f + f) = 0 := by rw [map_add (f := _), hf, add_zero]
  have e : (3 : MvPowerSeries ι K) * f = f + f + f := by ring
  rw [e, fExp_add h2 hf, fExp_add hf hf]
  ring

private theorem at1_C_eq_C {ι : Type} (x : ι) (c : K) :
    at1 x (PowerSeries.C c) = (MvPowerSeries.C c : MvPowerSeries ι K) := by
  have hx : PowerSeries.HasSubst (MvPowerSeries.X x : MvPowerSeries ι K) := PowerSeries.HasSubst.X x
  have e := (PowerSeries.substAlgHom hx).commutes c
  rw [PowerSeries.coe_substAlgHom] at e
  exact e

theorem curve3_at {ι : Type} {l P ep : PowerSeries K} {a1 a3 : K}
    (hl : PowerSeries.constantCoeff l = 0)
    (h : PowerSeries.X ^ 3 * (-2 + l ^ 3 * PowerSeries.subst l (PowerSeries.derivative (R := K) P)) =
      l ^ 3 * (-2 * ep + PowerSeries.C a1 * PowerSeries.X * ep +
        PowerSeries.C a3 * PowerSeries.X ^ 3)) (x : ι) :
    MvPowerSeries.X x ^ 3 * (-2 + at1 x l ^ 3 * PowerSeries.subst (at1 x l) (dz P)) =
      at1 x l ^ 3 * (-2 * at1 x ep + MvPowerSeries.C a1 * MvPowerSeries.X x * at1 x ep +
        MvPowerSeries.C a3 * MvPowerSeries.X x ^ 3) := by
  have hx : PowerSeries.HasSubst (MvPowerSeries.X x : MvPowerSeries ι K) := PowerSeries.HasSubst.X x
  have e := congrArg (PowerSeries.substAlgHom hx) h
  simp only [map_mul, map_add (f := _), map_pow, map_neg, map_ofNat, PowerSeries.coe_substAlgHom,
    PowerSeries.subst_X hx] at e
  have e1 : ∀ f : PowerSeries K,
      PowerSeries.subst (MvPowerSeries.X x : MvPowerSeries ι K) f = at1 x f := fun f => rfl
  simp only [e1, at1_C_eq_C, ParE.subst_inVar x _ hl] at e
  exact e

theorem subst_det_three_points {ι : Type} (P : PowerSeries K) {b : Fin 3 → MvPowerSeries ι K}
    (hb : MvPowerSeries.HasSubst b) :
    MvPowerSeries.subst b (det3 P) = Matrix.det (Matrix.of fun j : Fin 3 =>
      ![b j ^ 3, b j * (1 + b j ^ 2 * PowerSeries.subst (b j) P),
        -2 + b j ^ 3 * PowerSeries.subst (b j) (dz P)]) := by
  unfold det3
  rw [← MvPowerSeries.coe_substAlgHom hb, AlgHom.map_det]
  congr 1
  refine Matrix.ext fun j c => ?_
  fin_cases c <;> simp [-MvPowerSeries.coe_substAlgHom]
  all_goals
    rw [← MvPowerSeries.coe_substAlgHom hb]
    simp only [map_mul, map_pow, map_add (f := _), map_neg, map_one, map_ofNat]
    simp only [MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_X hb, ParO.subst_inVar _ _ hb]

theorem subst_series_at_sum_three {ι : Type} (g : PowerSeries K) {b : Fin 3 → MvPowerSeries ι K}
    (hb : MvPowerSeries.HasSubst b) :
    MvPowerSeries.subst b (evalSumThree g) = PowerSeries.subst (b 0 + b 1 + b 2) g := by
  unfold evalSumThree
  rw [psubst_subst g (u := (MvPowerSeries.X 0 + MvPowerSeries.X 1 + MvPowerSeries.X 2 :
    MvPowerSeries (Fin 3) K)) (by simp) hb]
  congr 1
  rw [← MvPowerSeries.coe_substAlgHom hb, map_add (f := _), map_add (f := _), MvPowerSeries.coe_substAlgHom,
    MvPowerSeries.subst_X hb, MvPowerSeries.subst_X hb, MvPowerSeries.subst_X hb]

theorem subst_series_at_difference_three {ι : Type} (j k : Fin 3) (g : PowerSeries K) {b : Fin 3 → MvPowerSeries ι K}
    (hb : MvPowerSeries.HasSubst b) :
    MvPowerSeries.subst b (evalDiffThree j k g) = PowerSeries.subst (b j - b k) g := by
  unfold evalDiffThree
  rw [psubst_subst g (u := (MvPowerSeries.X j - MvPowerSeries.X k : MvPowerSeries (Fin 3) K))
    (by simp) hb]
  congr 1
  rw [← MvPowerSeries.coe_substAlgHom hb, map_sub, MvPowerSeries.coe_substAlgHom,
    MvPowerSeries.subst_X hb, MvPowerSeries.subst_X hb]

theorem det_rows {R : Type} [CommRing R] (x L A B e : Fin 3 → R) (c0 a1 a3 : R)
    (h2 : ∀ j, x j ^ 2 * A j = L j ^ 2 * (e j + c0 * x j ^ 2))
    (h3 : ∀ j, x j ^ 3 * B j = L j ^ 3 * (-2 * e j + a1 * x j * e j + a3 * x j ^ 3)) :
    (x 0 * x 1 * x 2) ^ 3 * Matrix.det (Matrix.of fun j => ![L j ^ 3, L j * A j, B j]) =
      2 * (L 0 * L 1 * L 2) ^ 3 *
        Matrix.det (Matrix.of fun j => ![x j ^ 3, x j * e j, -e j]) := by
  have hA : ∀ j, x j ^ 3 * (L j * A j) = L j ^ 3 * (x j * e j + c0 * x j ^ 3) := fun j => by
    linear_combination (x j * L j) * h2 j
  have d1 : Matrix.det (Matrix.of fun j => ![L j ^ 3, L j * A j, B j]) =
      L 0 ^ 3 * (L 1 * A 1) * B 2 - L 0 ^ 3 * B 1 * (L 2 * A 2) - L 0 * A 0 * L 1 ^ 3 * B 2 +
        L 0 * A 0 * B 1 * L 2 ^ 3 + B 0 * L 1 ^ 3 * (L 2 * A 2) - B 0 * (L 1 * A 1) * L 2 ^ 3 := by
    rw [Matrix.det_fin_three]; rfl
  have d2 : Matrix.det (Matrix.of fun j => ![x j ^ 3, x j * e j, -e j]) =
      x 0 ^ 3 * (x 1 * e 1) * -e 2 - x 0 ^ 3 * -e 1 * (x 2 * e 2) - x 0 * e 0 * x 1 ^ 3 * -e 2 +
        x 0 * e 0 * -e 1 * x 2 ^ 3 + -e 0 * x 1 ^ 3 * (x 2 * e 2) - -e 0 * (x 1 * e 1) * x 2 ^ 3 := by
    rw [Matrix.det_fin_three]; rfl
  rw [d1, d2]
  calc _ = (x 0 ^ 3 * L 0 ^ 3) * (x 1 ^ 3 * (L 1 * A 1)) * (x 2 ^ 3 * B 2) -
        (x 0 ^ 3 * L 0 ^ 3) * (x 1 ^ 3 * B 1) * (x 2 ^ 3 * (L 2 * A 2)) -
        (x 0 ^ 3 * (L 0 * A 0)) * (x 1 ^ 3 * L 1 ^ 3) * (x 2 ^ 3 * B 2) +
        (x 0 ^ 3 * (L 0 * A 0)) * (x 1 ^ 3 * B 1) * (x 2 ^ 3 * L 2 ^ 3) +
        (x 0 ^ 3 * B 0) * (x 1 ^ 3 * L 1 ^ 3) * (x 2 ^ 3 * (L 2 * A 2)) -
        (x 0 ^ 3 * B 0) * (x 1 ^ 3 * (L 1 * A 1)) * (x 2 ^ 3 * L 2 ^ 3) := by ring
    _ = _ := by rw [hA 0, hA 1, hA 2, h3 0, h3 1, h3 2]; ring

private theorem coeff_single_one_at1_eq_ite {ι : Type} [DecidableEq ι] (x y : ι) (l : PowerSeries K) :
    MvPowerSeries.coeff (Finsupp.single y 1) (at1 x l) =
      if x = y then PowerSeries.coeff 1 l else 0 := by
  unfold at1
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.X x), finsum_eq_single _ 1]
  · split_ifs with hxy
    · subst hxy
      simp [MvPowerSeries.coeff_X]
    · simp [MvPowerSeries.coeff_X, Finsupp.single_left_inj one_ne_zero, Ne.symm hxy]
  · intro d hd
    rw [MvPowerSeries.coeff_X_pow, if_neg, smul_zero]
    intro he
    rw [Finsupp.single_eq_single_iff] at he
    rcases he with ⟨-, h1⟩ | ⟨h1, -⟩
    · exact hd h1.symm
    · exact one_ne_zero h1

theorem inVar_ne_zero {ι : Type} {l : PowerSeries K} (hl1 : PowerSeries.coeff 1 l = 1) (x : ι) :
    at1 x l ≠ 0 := by
  classical
  intro h0
  have e := coeff_single_one_at1_eq_ite x x l
  rw [h0, map_zero, if_pos rfl, hl1] at e
  exact zero_ne_one e

theorem sum_log_three_variables_ne_zero {l : PowerSeries K} (hl1 : PowerSeries.coeff 1 l = 1) :
    at1 (0 : Fin 3) l + at1 1 l + at1 2 l ≠ 0 := by
  intro h0
  have e := congrArg (MvPowerSeries.coeff (Finsupp.single (0 : Fin 3) 1)) h0
  rw [map_add (f := _), map_add (f := _), map_zero, coeff_single_one_at1_eq_ite, coeff_single_one_at1_eq_ite, coeff_single_one_at1_eq_ite] at e
  simp [hl1] at e

end Alg

section Norm

variable {K : Type} [NormedField K] [CharZero K]

theorem cX (j : Fin 3) :
    MvPowerSeries.constantCoeff (MvPowerSeries.X j : MvPowerSeries (Fin 3) K) = 0 := by
  simp

theorem constantCoeff_law_first_two_of_three {F : MvPowerSeries (Fin 2) K} (hF : MvPowerSeries.constantCoeff F = 0) :
    MvPowerSeries.constantCoeff (in3 F) = 0 := by
  unfold in3
  exact law_constantCoeff_subst2 F hF _ _ (by simp) (by simp)

theorem constantCoeff_law_three_variables {F : MvPowerSeries (Fin 2) K} (hF : MvPowerSeries.constantCoeff F = 0) :
    MvPowerSeries.constantCoeff (F3 F) = 0 := by
  unfold F3
  exact law_constantCoeff_subst2 F hF _ _ (constantCoeff_law_first_two_of_three hF) (by simp)

private theorem lawLog_subst_formal_sum_eq_add {F : MvPowerSeries (Fin 2) K} {l : PowerSeries K} (h : LawLog F l)
    {u v : MvPowerSeries (Fin 3) K} (hu : MvPowerSeries.constantCoeff u = 0)
    (hv : MvPowerSeries.constantCoeff v = 0) :
    PowerSeries.subst (MvPowerSeries.subst ![u, v] F) l =
      PowerSeries.subst u l + PowerSeries.subst v l := by
  obtain ⟨hF0, -, -, -, hc⟩ := h
  have hF : PowerSeries.subst F l = at1 0 l + at1 1 l := by
    unfold cob at hc
    linear_combination hc
  rw [← psubst_subst l hF0 (hs2 hu hv), hF, MvPowerSeries.subst_add (hs2 hu hv),
    ParO.subst_inVar _ _ (hs2 hu hv), ParO.subst_inVar _ _ (hs2 hu hv)]
  rfl

theorem log_formal_law_three_variables {F : MvPowerSeries (Fin 2) K} {l : PowerSeries K} (h : LawLog F l) :
    PowerSeries.subst (F3 F) l = at1 0 l + at1 1 l + at1 2 l := by
  unfold F3
  rw [lawLog_subst_formal_sum_eq_add h (constantCoeff_law_first_two_of_three h.1) (cX 2)]
  unfold in3
  rw [lawLog_subst_formal_sum_eq_add h (cX 0) (cX 1)]
  rfl

private theorem constantCoeff_at1_fin_eq_zero {n : ℕ} (k : Fin n) {f : PowerSeries K} (hf : PowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (at1 k f : MvPowerSeries (Fin n) K) = 0 :=
  (Formalism.G.LogP.constantCoeff_subst_of_zero (σ := Unit) f
    (b := fun _ => (MvPowerSeries.X k : MvPowerSeries (Fin n) K)) (fun _ => by simp)).trans hf

theorem constantCoeff_law_with_inverse_three {F : MvPowerSeries (Fin 2) K} {l i : PowerSeries K} (h : LawLog F l)
    (hi : IsInv l i) (j k : Fin 3) : MvPowerSeries.constantCoeff (lawDifferenceThree F i j k) = 0 := by
  unfold lawDifferenceThree
  exact law_constantCoeff_subst2 F h.1 _ _ (cX j) (constantCoeff_at1_fin_eq_zero k hi.1)

theorem log_law_with_inverse_three {F : MvPowerSeries (Fin 2) K} {l i : PowerSeries K} (h : LawLog F l)
    (hi : IsInv l i) (j k : Fin 3) :
    PowerSeries.subst (lawDifferenceThree F i j k) l = at1 j l - at1 k l := by
  unfold lawDifferenceThree
  rw [lawLog_subst_formal_sum_eq_add h (cX j) (constantCoeff_at1_fin_eq_zero k hi.1), ← ParE.subst_inVar k l hi.1, hi.2.2,
    sub_eq_add_neg]
  congr 1
  unfold at1
  rw [← PowerSeries.coe_substAlgHom (PowerSeries.HasSubst.X k), map_neg]

theorem law_with_inverse_three_eq_subst {F : MvPowerSeries (Fin 2) K} {i : PowerSeries K}
    (hi : PowerSeries.constantCoeff i = 0) (j k : Fin 3) :
    lawDifferenceThree F i j k = MvPowerSeries.subst
      ![(MvPowerSeries.X j : MvPowerSeries (Fin 3) K), MvPowerSeries.X k] (FI F i) := by
  have hb := hs2 (cX (K := K) j) (cX (K := K) k)
  unfold lawDifferenceThree FI
  rw [subst2_subst F (u := (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K)) (v := at1 1 i)
    (by simp) (constantCoeff_at1_fin_eq_zero 1 hi) hb, MvPowerSeries.subst_X hb, ParO.subst_inVar _ _ hb]
  rfl

theorem law_with_inverse_factor_difference {F n : MvPowerSeries (Fin 2) K} {i : PowerSeries K}
    (hi : PowerSeries.constantCoeff i = 0)
    (hn : FI F i = (MvPowerSeries.X 0 - MvPowerSeries.X 1) * n) (j k : Fin 3) :
    lawDifferenceThree F i j k = (MvPowerSeries.X j - MvPowerSeries.X k) * MvPowerSeries.subst
      ![(MvPowerSeries.X j : MvPowerSeries (Fin 3) K), MvPowerSeries.X k] n := by
  have hb := hs2 (cX (K := K) j) (cX (K := K) k)
  rw [law_with_inverse_three_eq_subst hi j k, hn, ← MvPowerSeries.coe_substAlgHom hb, map_mul, map_sub,
    MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_X hb, MvPowerSeries.subst_X hb]
  rfl

theorem X_sub_ne_zero {j k : Fin 3} (h : j ≠ k) :
    (MvPowerSeries.X j - MvPowerSeries.X k : MvPowerSeries (Fin 3) K) ≠ 0 := by
  intro h0
  have h1 := congrArg (MvPowerSeries.coeff (Finsupp.single j 1)) h0
  rw [map_sub, map_zero, MvPowerSeries.coeff_X, MvPowerSeries.coeff_X, if_pos rfl,
    if_neg (fun hh => h (Finsupp.single_left_injective one_ne_zero hh))] at h1
  simp at h1

theorem parallelogram_three_weierstrass_key (hA : FrobStickStar) {g2 g3 s2 c0 a1 a3 : K} {P l i ep : PowerSeries K}
    {F n : MvPowerSeries (Fin 2) K} {e : MvPowerSeries (Fin 3) K} (hP : IsWp g2 g3 P)
    (hF : LawLog F l) (hi : IsInv l i)
    (h2 : PowerSeries.X ^ 2 * (1 + l ^ 2 * PowerSeries.subst l P) =
      l ^ 2 * (ep + PowerSeries.C c0 * PowerSeries.X ^ 2))
    (h3 : PowerSeries.X ^ 3 * (-2 + l ^ 3 * PowerSeries.subst l (PowerSeries.derivative (R := K) P)) =
      l ^ 3 * (-2 * ep + PowerSeries.C a1 * PowerSeries.X * ep +
        PowerSeries.C a3 * PowerSeries.X ^ 3))
    (he : Matrix.det (Matrix.of fun j : Fin 3 =>
        ![(MvPowerSeries.X j : MvPowerSeries (Fin 3) K) ^ 3, MvPowerSeries.X j * at1 j ep,
          -at1 j ep]) =
        e * F3 F * (MvPowerSeries.X 0 - MvPowerSeries.X 1) *
          (MvPowerSeries.X 0 - MvPowerSeries.X 2) * (MvPowerSeries.X 1 - MvPowerSeries.X 2))
    (hn : FI F i = (MvPowerSeries.X 0 - MvPowerSeries.X 1) * n) :
    MvPowerSeries.constantCoeff (par3 F i (phO s2 P l)) = 0 ∧
    MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 1] n *
      MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2] n *
      MvPowerSeries.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2] n *
      fExp (-par3 F i (phO s2 P l)) = -e := by
  have hl0 := hF.2.2.1
  have hl1 := hF.2.2.2.1
  obtain ⟨hph0, hphe⟩ := phODef K s2 P l hl0 hl1
  generalize phO s2 P l = ph at hph0 hphe ⊢
  have cL : ∀ j : Fin 3, MvPowerSeries.constantCoeff (at1 j l) = 0 :=
    fun j => constantCoeff_series_at_variable j l hl0
  have hφ : MvPowerSeries.HasSubst (fun j : Fin 3 => (at1 j l : MvPowerSeries (Fin 3) K)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero cL
  have key := congrArg (MvPowerSeries.subst (fun j : Fin 3 => (at1 j l : MvPowerSeries (Fin 3) K)))
    (hA K g2 g3 s2 P hP)
  rw [← MvPowerSeries.coe_substAlgHom hφ] at key
  simp only [map_mul, map_pow, map_neg, map_ofNat] at key
  simp only [MvPowerSeries.coe_substAlgHom hφ, MvPowerSeries.subst_X hφ, subst_series_at_sum_three _ hφ,
    subst_series_at_difference_three _ _ _ hφ, subst_det_three_points _ hφ, ParO.subst_inVar _ _ hφ] at key
  have cS := constantCoeff_law_three_variables hF.1
  have cD := constantCoeff_law_with_inverse_three hF hi
  have v : ∀ j : Fin 3, PowerSeries.subst (at1 j l) (sgStar s2 P) =
      MvPowerSeries.X j * fExp (-at1 j ph) := fun j => ParO.value_at hl0 hph0 hphe (cX j)
  rw [← log_formal_law_three_variables hF, ← log_law_with_inverse_three hF hi 0 1, ← log_law_with_inverse_three hF hi 0 2, ← log_law_with_inverse_three hF hi 1 2,
    ParO.value_at hl0 hph0 hphe cS, ParO.value_at hl0 hph0 hphe (cD 0 1),
    ParO.value_at hl0 hph0 hphe (cD 0 2), ParO.value_at hl0 hph0 hphe (cD 1 2), v 0, v 1, v 2]
    at key
  have dr := det_rows (fun j : Fin 3 => (MvPowerSeries.X j : MvPowerSeries (Fin 3) K))
    (fun j => at1 j l) (fun j => 1 + at1 j l ^ 2 * PowerSeries.subst (at1 j l) P)
    (fun j => -2 + at1 j l ^ 3 * PowerSeries.subst (at1 j l) (dz P)) (fun j => at1 j ep)
    (MvPowerSeries.C c0) (MvPowerSeries.C a1) (MvPowerSeries.C a3)
    (fun j => ParO.curve_at hl0 h2 j) (fun j => curve3_at hl0 h3 j)
  simp only [he] at dr
  have cA : MvPowerSeries.constantCoeff (PowerSeries.subst (F3 F) ph) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero cS ph hph0
  have cB : ∀ j k, MvPowerSeries.constantCoeff (PowerSeries.subst (lawDifferenceThree F i j k) ph) = 0 :=
    fun j k => PowerSeries.constantCoeff_subst_eq_zero (cD j k) ph hph0
  have ca : ∀ j : Fin 3, MvPowerSeries.constantCoeff (at1 j ph) = 0 :=
    fun j => constantCoeff_series_at_variable j ph hph0
  have hpar : -par3 F i ph = -PowerSeries.subst (F3 F) ph + -PowerSeries.subst (lawDifferenceThree F i 0 1) ph +
      -PowerSeries.subst (lawDifferenceThree F i 0 2) ph + -PowerSeries.subst (lawDifferenceThree F i 1 2) ph +
      3 * at1 0 ph + 3 * at1 1 ph + 3 * at1 2 ph := by
    unfold par3; ring
  have h0 : MvPowerSeries.constantCoeff (par3 F i ph) = 0 := by
    unfold par3; simp [cA, cB, ca]
  refine ⟨h0, ?_⟩
  rw [hpar, fExp_add (by simp [cA, cB, ca]) (by simp [ca]),
    fExp_add (by simp [cA, cB, ca]) (by simp [ca]), fExp_add (by simp [cA, cB]) (by simp [ca]),
    fExp_add (by simp [cA, cB]) (by simp [cB]), fExp_add (by simp [cA, cB]) (by simp [cB]),
    fExp_add (by simp [cA]) (by simp [cB]), fExp_three (ca 0), fExp_three (ca 1),
    fExp_three (ca 2)]
  have r0 := ParO.fExp_mul_neg (ca 0)
  have r1 := ParO.fExp_mul_neg (ca 1)
  have r2 := ParO.fExp_mul_neg (ca 2)
  have f01 := law_with_inverse_factor_difference hi.1 hn 0 1
  have f02 := law_with_inverse_factor_difference hi.1 hn 0 2
  have f12 := law_with_inverse_factor_difference hi.1 hn 1 2
  have hF3 : F3 F ≠ 0 := ParO.ne_zero_of_psubst hl0 (by rw [log_formal_law_three_variables hF]; exact sum_log_three_variables_ne_zero hl1)
  generalize fExp (-PowerSeries.subst (F3 F) ph) = ES at key ⊢
  generalize fExp (-PowerSeries.subst (lawDifferenceThree F i 0 1) ph) = bivariateExponentMonomial at key ⊢
  generalize fExp (-PowerSeries.subst (lawDifferenceThree F i 0 2) ph) = E02 at key ⊢
  generalize fExp (-PowerSeries.subst (lawDifferenceThree F i 1 2) ph) = E12 at key ⊢
  rw [f01, f02, f12] at key
  generalize MvPowerSeries.subst
    ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 1] n = n01 at key ⊢
  generalize MvPowerSeries.subst
    ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2] n = n02 at key ⊢
  generalize MvPowerSeries.subst
    ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2] n = n12 at key ⊢
  generalize fExp (-at1 (0 : Fin 3) ph) = E0 at key r0 ⊢
  generalize fExp (-at1 (1 : Fin 3) ph) = E1 at key r1 ⊢
  generalize fExp (-at1 (2 : Fin 3) ph) = E2 at key r2 ⊢
  generalize fExp (at1 (0 : Fin 3) ph) = G0 at r0 ⊢
  generalize fExp (at1 (1 : Fin 3) ph) = G1 at r1 ⊢
  generalize fExp (at1 (2 : Fin 3) ph) = G2 at r2 ⊢
  have h2ne : (2 : MvPowerSeries (Fin 3) K) ≠ 0 := by
    intro h
    have := congrArg MvPowerSeries.constantCoeff h
    rw [map_ofNat, map_zero] at this
    exact two_ne_zero this
  have hne : 2 * (at1 (0 : Fin 3) l * at1 1 l * at1 2 l) ^ 3 * F3 F *
      (MvPowerSeries.X 0 - MvPowerSeries.X 1) * (MvPowerSeries.X 0 - MvPowerSeries.X 2) *
      (MvPowerSeries.X 1 - MvPowerSeries.X 2) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h2ne
      (pow_ne_zero 3 (mul_ne_zero (mul_ne_zero (inVar_ne_zero hl1 0) (inVar_ne_zero hl1 1))
        (inVar_ne_zero hl1 2)))) hF3) (X_sub_ne_zero (by decide))) (X_sub_ne_zero (by decide)))
      (X_sub_ne_zero (by decide))
  have E : (E0 * E1 * E2) ^ 3 * e = -(n01 * n02 * n12 * (ES * bivariateExponentMonomial * E02 * E12)) := by
    refine mul_left_cancel₀ hne ?_
    linear_combination key - (E0 * E1 * E2) ^ 3 * dr
  have hp : (G0 * G1 * G2) ^ 3 * (E0 * E1 * E2) ^ 3 = 1 := by
    have : G0 * G1 * G2 * (E0 * E1 * E2) = 1 := by
      calc G0 * G1 * G2 * (E0 * E1 * E2) = (G0 * E0) * (G1 * E1) * (G2 * E2) := by ring
        _ = 1 := by rw [r0, r1, r2]; ring
    rw [← mul_pow, this, one_pow]
  linear_combination (G0 * G1 * G2) ^ 3 * E - e * hp

end Norm

theorem ParThree_of (hF : FrobStickStar) (hU : FIUnit) : ParThree := by
  intro K _ _ _ g2 g3 s2 c0 a1 a3 P l i ep F hP hL hi hC hC3
  obtain ⟨-, -, h2, -⟩ := hC
  obtain ⟨h3, e, heI, he0, he⟩ := hC3
  obtain ⟨n, hnI, hn0, hn⟩ := hU K F l i hL hi
  obtain ⟨h0, key⟩ := parallelogram_three_weierstrass_key (s2 := s2) hF hP hL hi h2 h3 he hn
  have iN : ∀ j k : Fin 3, Integral (MvPowerSeries.subst
      ![(MvPowerSeries.X j : MvPowerSeries (Fin 3) K), MvPowerSeries.X k] n) := fun j k =>
    integral_subst_two_variables hnI _ _ (cX j) (cX k) (integral_mvPowerSeries_X j) (integral_mvPowerSeries_X k)
  have cN : ∀ j k : Fin 3, MvPowerSeries.constantCoeff (MvPowerSeries.subst
      ![(MvPowerSeries.X j : MvPowerSeries (Fin 3) K), MvPowerSeries.X k] n) = 1 := fun j k => by
    rw [Formalism.G.LogP.constantCoeff_subst_of_zero n (fun s => by fin_cases s <;> simp), hn0]
  generalize par3 F i (phO s2 P l) = q at h0 key ⊢
  obtain ⟨N, hN⟩ : ∃ N, N = MvPowerSeries.subst
      ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 1] n *
      MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2] n *
      MvPowerSeries.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2] n :=
    ⟨_, rfl⟩
  have iNN : Integral N := by
    rw [hN]
    exact Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_mul' (Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_mul' (iN 0 1) (iN 0 2)) (iN 1 2)
  have cNN : MvPowerSeries.constantCoeff N = 1 := by
    rw [hN, map_mul, map_mul, cN, cN, cN]; ring
  rw [← hN] at key
  have hq0 : MvPowerSeries.constantCoeff (-q) = 0 := by rw [map_neg, h0, neg_zero]
  have hlog := ParO.fLog_mul cNN (constantCoeff_fExp hq0)
  rw [key, fLog_fExp hq0] at hlog
  have hq : q = fLog N + -fLog (-e) := by linear_combination hlog
  have s1 := (simeqLog K (Fin 3) N cNN iNN).1
  have s2' := (simeqLog K (Fin 3) (-e) (by rw [map_neg, he0, neg_neg]) (integral_neg heI)).2
  have s3 := (Formalism.InvariantFactorPaths.G7.equivalence_rules K (Fin 3)).2.2.2.1 _ _ _ _ s1 s2'
  rw [add_zero] at s3
  rw [hq]
  exact s3

end Formalism.L2.Th1.B.E2
end
end

section -- merged from Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.XTwoDvdOfRestrictThirdZero
noncomputable section

namespace Formalism.L2.Th1.B.Wr

open MvPowerSeries

variable {K : Type} [Field K] [CharZero K]

private theorem hasSubst_fin_three_of_constantCoeff_eq_zero {a : Fin 3 → MvPowerSeries (Fin 3) K}
    (ha : ∀ s, constantCoeff (a s) = 0) : HasSubst a := by
  exact hasSubst_of_constantCoeff_zero ha

theorem hasSubst_restrictThirdZero : HasSubst ![(X 0 : MvPowerSeries (Fin 3) K), X 1, 0] :=
  hasSubst_fin_three_of_constantCoeff_eq_zero (fun s => by fin_cases s <;> simp)

theorem restrictThirdZero_eq_rescale (h : MvPowerSeries (Fin 3) K) : ev3 h = rescale ![1, 1, 0] h := by
  rw [rescale_eq_subst]
  unfold Formalism.L2.Th1.B.ev3
  congr 1
  funext s
  fin_cases s <;> simp

theorem coeff_restrictThirdZero (h : MvPowerSeries (Fin 3) K) (n : Fin 3 →₀ ℕ) (hn : n 2 = 0) :
    coeff n (ev3 h) = coeff n h := by
  rw [restrictThirdZero_eq_rescale]
  rw [coeff_rescale, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_three]
  simp [hn]

theorem restrictThirdZero_mul (f g : MvPowerSeries (Fin 3) K) : ev3 (f * g) = ev3 f * ev3 g := by
  simp only [restrictThirdZero_eq_rescale, map_mul]

theorem restrictThirdZero_add (f g : MvPowerSeries (Fin 3) K) : ev3 (f + g) = ev3 f + ev3 g := by
  simp only [restrictThirdZero_eq_rescale, map_add (f := _)]

theorem restrictThirdZero_sub (f g : MvPowerSeries (Fin 3) K) : ev3 (f - g) = ev3 f - ev3 g := by
  simp only [restrictThirdZero_eq_rescale, map_sub]

theorem restrictThirdZero_natCast (k : ℕ) : ev3 (k : MvPowerSeries (Fin 3) K) = k := by
  simp only [restrictThirdZero_eq_rescale, map_natCast]

theorem restrictThirdZero_X_two : ev3 (X 2 : MvPowerSeries (Fin 3) K) = 0 := by
  unfold Formalism.L2.Th1.B.ev3
  rw [subst_X hasSubst_restrictThirdZero]
  simp

theorem X_two_dvd_of_restrictThirdZero {h : MvPowerSeries (Fin 3) K} (h0 : ev3 h = 0) : X 2 ∣ h := by
  rw [X_dvd_iff]
  intro m hm
  rw [← coeff_restrictThirdZero h m hm, h0]
  simp

private theorem X_two_fin_three_ne_zero : (X 2 : MvPowerSeries (Fin 3) K) ≠ 0 := by
  intro h
  have := congrArg (coeff (Finsupp.single (2 : Fin 3) 1)) h
  simp [coeff_X] at this

private theorem pderiv_X_fin_three_self (i : Fin 3) :
    MvPowerSeries.pderiv (R := K) i (X i : MvPowerSeries (Fin 3) K) = 1 := by
  simp

private theorem pderiv_two_X_two_pow_succ (m : ℕ) :
    MvPowerSeries.pderiv (R := K) 2 ((X 2 : MvPowerSeries (Fin 3) K) ^ (m + 1)) =
      ((m + 1 : ℕ) : MvPowerSeries (Fin 3) K) * X 2 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ (X 2 : MvPowerSeries (Fin 3) K) (m + 1), Derivation.leibniz, ih, pderiv_X_fin_three_self]
    simp only [smul_eq_mul]
    push_cast
    ring

private theorem pd_two_X_two_pow_succ_mul (m : ℕ) (R : MvPowerSeries (Fin 3) K) :
    Formalism.L2.Th1.B.pd 2 (X 2 ^ (m + 1) * R) =
      X 2 ^ (m + 1) * Formalism.L2.Th1.B.pd 2 R + R * (((m + 1 : ℕ) : MvPowerSeries (Fin 3) K) * X 2 ^ m) := by
  unfold Formalism.L2.Th1.B.pd
  rw [Derivation.leibniz, pderiv_two_X_two_pow_succ]
  simp only [smul_eq_mul]

theorem eq_zero_of_wronsk {Q B : MvPowerSeries (Fin 3) K} (hw : Q * pd 2 B = B * pd 2 Q)
    (hQ : ev3 Q = 0) (hB : ev3 B ≠ 0) : Q = 0 := by
  have key : ∀ m : ℕ, ∃ R : MvPowerSeries (Fin 3) K, Q = X 2 ^ (m + 1) * R := by
    intro m
    induction m with
    | zero =>
      obtain ⟨R, hR⟩ := X_two_dvd_of_restrictThirdZero hQ
      exact ⟨R, by rw [hR]; ring⟩
    | succ m ih =>
      obtain ⟨R, rfl⟩ := ih
      rw [pd_two_X_two_pow_succ_mul] at hw
      have h1 : X 2 ^ m * (X 2 * R * Formalism.L2.Th1.B.pd 2 B) =
          X 2 ^ m * (B * (((m + 1 : ℕ) : MvPowerSeries (Fin 3) K) * R + X 2 * Formalism.L2.Th1.B.pd 2 R)) := by
        linear_combination hw
      have h2 := mul_left_cancel₀ (pow_ne_zero m X_two_fin_three_ne_zero) h1
      have h3 := congrArg Formalism.L2.Th1.B.ev3 h2
      simp only [restrictThirdZero_mul, restrictThirdZero_add, restrictThirdZero_X_two,
        restrictThirdZero_natCast, zero_mul, add_zero] at h3
      have hc : ((m + 1 : ℕ) : MvPowerSeries (Fin 3) K) ≠ 0 := by
        intro hc
        have := congrArg (coeff (0 : Fin 3 →₀ ℕ)) hc
        simp at this
        exact Nat.cast_add_one_ne_zero m this
      have hR : Formalism.L2.Th1.B.ev3 R = 0 := by
        rcases mul_eq_zero.mp h3.symm with h | h
        · exact absurd h hB
        · rcases mul_eq_zero.mp h with h | h
          · exact absurd h hc
          · exact h
      obtain ⟨S, hS⟩ := X_two_dvd_of_restrictThirdZero hR
      exact ⟨S, by rw [hS]; ring⟩
  ext n
  obtain ⟨R, hR⟩ := key (n 2)
  suffices hz : coeff n ((X 2 : MvPowerSeries (Fin 3) K) ^ (n 2 + 1) * R) = 0 by
    rw [hR, hz]; simp
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨p, q⟩ hpq
  have hpq' : p + q = n := by simpa using hpq
  rw [coeff_X_pow]
  split_ifs with hp
  · exfalso
    subst hp
    have := DFunLike.congr_fun hpq' 2
    simp only [Finsupp.add_apply, Finsupp.single_eq_same] at this
    omega
  · simp

theorem wronskianUniqueness : WronskLemma := by
  intro L _ _ A Bs hw hr hB
  have hQ : Formalism.L2.Th1.B.ev3 (A - Bs) = 0 := by rw [restrictThirdZero_sub, hr, sub_self]
  have hd : Formalism.L2.Th1.B.pd 2 (A - Bs) = Formalism.L2.Th1.B.pd 2 A - Formalism.L2.Th1.B.pd 2 Bs := by
    simp only [Formalism.L2.Th1.B.pd, map_sub]
  have hw' : (A - Bs) * Formalism.L2.Th1.B.pd 2 Bs = Bs * Formalism.L2.Th1.B.pd 2 (A - Bs) := by
    rw [hd]
    linear_combination hw
  exact sub_eq_zero.mp (eq_zero_of_wronsk hw' hQ hB)

def sh (h : MvPowerSeries (Fin 3) K) : MvPowerSeries (Fin 3) K :=
  subst ![(X 0 : MvPowerSeries (Fin 3) K), X 1 - X 2, X 2] h

def shI (h : MvPowerSeries (Fin 3) K) : MvPowerSeries (Fin 3) K :=
  subst ![(X 0 : MvPowerSeries (Fin 3) K), X 1 + X 2, X 2] h

theorem cc_sh (s : Fin 3) :
    constantCoeff (![(X 0 : MvPowerSeries (Fin 3) K), X 1 - X 2, X 2] s) = 0 := by
  fin_cases s <;> simp

theorem cc_shI (s : Fin 3) :
    constantCoeff (![(X 0 : MvPowerSeries (Fin 3) K), X 1 + X 2, X 2] s) = 0 := by
  fin_cases s <;> simp

theorem hasSubst_sh : HasSubst ![(X 0 : MvPowerSeries (Fin 3) K), X 1 - X 2, X 2] :=
  hasSubst_fin_three_of_constantCoeff_eq_zero cc_sh

theorem hasSubst_shI : HasSubst ![(X 0 : MvPowerSeries (Fin 3) K), X 1 + X 2, X 2] :=
  hasSubst_fin_three_of_constantCoeff_eq_zero cc_shI

private theorem subst_fin_three_mul {a : Fin 3 → MvPowerSeries (Fin 3) K} (ha : HasSubst a)
    (f g : MvPowerSeries (Fin 3) K) : subst a (f * g) = subst a f * subst a g := by
  exact subst_mul ha f g

theorem sh_mul (f g : MvPowerSeries (Fin 3) K) : sh (f * g) = sh f * sh g := by
  unfold sh
  exact subst_fin_three_mul hasSubst_sh f g

private theorem subst_fin_three_sub {a : Fin 3 → MvPowerSeries (Fin 3) K} (ha : HasSubst a)
    (f g : MvPowerSeries (Fin 3) K) : subst a (f - g) = subst a f - subst a g := by
  exact subst_sub ha f g

theorem sh_sub (f g : MvPowerSeries (Fin 3) K) : sh (f - g) = sh f - sh g := by
  unfold sh
  exact subst_fin_three_sub hasSubst_sh f g

private theorem subst_X_fin_three_eq_self (h : MvPowerSeries (Fin 3) K) :
    subst (X : Fin 3 → MvPowerSeries (Fin 3) K) h = h := by
  rw [← map_algebraMap_eq_subst_X]
  simp

theorem shI_sh (h : MvPowerSeries (Fin 3) K) : shI (sh h) = h := by
  unfold shI sh
  rw [subst_comp_subst_apply hasSubst_sh hasSubst_shI]
  trans subst (X : Fin 3 → MvPowerSeries (Fin 3) K) h
  · congr 1
    funext s
    fin_cases s <;> simp [subst_X hasSubst_shI, subst_fin_three_sub hasSubst_shI]
  · exact subst_X_fin_three_eq_self h

theorem restrictThirdZero_shear (h : MvPowerSeries (Fin 3) K) : ev3 (sh h) = ev3 h := by
  unfold Formalism.L2.Th1.B.ev3 sh
  rw [subst_comp_subst_apply hasSubst_sh hasSubst_restrictThirdZero]
  congr 1
  funext s
  fin_cases s <;> simp [subst_X hasSubst_restrictThirdZero, subst_fin_three_sub hasSubst_restrictThirdZero]

private theorem pderiv_X_fin_three_of_ne {i j : Fin 3} (hij : j ≠ i) :
    MvPowerSeries.pderiv (R := K) i (X j : MvPowerSeries (Fin 3) K) = 0 := by
  simp [hij]

theorem partialDeriv_two_shear (h : MvPowerSeries (Fin 3) K) : pd 2 (sh h) = sh (pd 2 h) - sh (pd 1 h) := by
  unfold sh Formalism.L2.Th1.B.pd
  rw [Formalism.G.LogCR.pderiv_subst cc_sh, Fin.sum_univ_three]
  simp [pderiv_X_fin_three_self, pderiv_X_fin_three_of_ne]
  try ring

theorem shearedWronskianUniqueness : ShearLemma := by
  intro L _ _ A Bs hw hr hB
  have h1 : sh A * Formalism.L2.Th1.B.pd 2 (sh Bs) = sh Bs * Formalism.L2.Th1.B.pd 2 (sh A) := by
    rw [partialDeriv_two_shear, partialDeriv_two_shear]
    have e := congrArg sh hw
    rw [sh_mul, sh_mul, sh_sub, sh_sub] at e
    linear_combination -e
  have h2 : Formalism.L2.Th1.B.ev3 (sh A) = Formalism.L2.Th1.B.ev3 (sh Bs) := by
    rw [restrictThirdZero_shear, restrictThirdZero_shear, hr]
  have h3 : Formalism.L2.Th1.B.ev3 (sh Bs) ≠ 0 := by
    rwa [restrictThirdZero_shear]
  have h4 := wronskianUniqueness L (sh A) (sh Bs) h1 h2 h3
  calc A = shI (sh A) := (shI_sh A).symm
    _ = shI (sh Bs) := by rw [h4]
    _ = Bs := shI_sh Bs

end Formalism.L2.Th1.B.Wr
end
end

namespace Formalism.L2.Th1.B

open Formalism.L2.Th1.A (bridgeWp bridgeLaw bridgeCurve bridgeCurve3)

theorem shearLemma : ShearLemma := Wr.shearedWronskianUniqueness
theorem tauRule : TauRule := Det.tau_derivative_rule_holds
theorem detRule : DetRule := Det.determinant_derivative_rule_holds
theorem frobStickLog : FrobStickLog := Fs.FrobStickLog_of shearLemma tauRule detRule
theorem frobStick : FrobStick := Fs.FrobStick_of frobStickLog
theorem frobStickStar : FrobStickStar := Fs.FrobStickStar_of frobStick
theorem fIUnit : FIUnit := E2.formal_inverse_unit_holds
theorem parThree : ParThree := E2.ParThree_of frobStickStar fIUnit
theorem cubeFromPars : CubeFromPars := E3.cube_relation_from_parallelograms
theorem first_level_all_formal_groups : LogSigmaPullbackCocycleJets := E3.log_sigma_pullback_cocycle_jets_of_parallelogram_and_cube parThree cubeFromPars

end Formalism.L2.Th1.B
