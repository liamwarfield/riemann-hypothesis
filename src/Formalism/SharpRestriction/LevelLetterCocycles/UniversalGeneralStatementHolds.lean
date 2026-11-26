module

public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.LevBasicsD
public import Formalism.SharpRestriction.LevelLetterCocycles.SingleMemSpan
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsGammaPi0EqPi0Mul

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.KillWinLOf
noncomputable section

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup

theorem killWinL_of (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (hAdm : AdmUnivA D HW F Cm) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F)
    (hInv : AtCaseA fun l _ K LL hG => Formalism.MainNotions.UnusedSlot80.CutU.InvLevCore ((HW l).W K 1 LL hG)) :
    KillWinL D HW := by
  intro l _ K LL hG hCA h5
  obtain ⟨⟨hdom, -, -⟩, -⟩ := Formalism.MainNotions.N.T2.litGoodO l LL
  haveI := hdom
  have : FiniteDimensional ℚ_[l] ↥(K0 K) := ((D.loc l).PD K).finK₀
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  have hR : ToolsR.RingP ((HW l).W K 1 LL hG) := ring_condition_uniformizer_polynomial D HW F h9 l K LL hCA
  have hT : Formalism.MainNotions.WachCoordinates.ToolsAlg ((HW l).W K 1 LL hG) := tool_algebra_of_ring_condition D HW F h9 l K LL hCA h5
  have hV := Formalism.MainNotions.WachCoordinates.Br.valRing_rec (D.loc l) LL
  have hvp : (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1 (((((D.loc l).PD K).p : ℕ) : ↥(OL LL)))) = 1 := by
    rw [map_natCast, (D.loc l).PD_p K]; exact (D.loc l).v_l LL
  have hKL := hAdm.2.1 l K LL hG hCA h5
  exact Formalism.MainNotions.UnusedSlot80.KWP.killWinFromCut ((HW l).W K 1 LL hG) hV.1 hV.2.1 hvp hR hKL
    (Formalism.MainNotions.UnusedSlot80.KF.psStable_of _ hR) hR.1
    (Formalism.MainNotions.UnusedSlot80.RatW.ratCore_of _ hR hT hR.2.2.1 hR.1) (hInv l K LL hG hCA h5)

end Formalism.MainNotions.UnusedSlot80
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.UniversalGeneralOfLevelInverse
section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.UniversalGeneratorsOfUnits
section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.EvalZeroXEqUniformizer
noncomputable section

open Classical PowerSeries

namespace Formalism.MainNotions.UnusedSlot80.UGen

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

def WF {O : Type} [CommRing O] (p : O) (F : PowerSeries O) (N : ℕ) : Prop :=
  ∃ g h : PowerSeries O, IsUnit (constantCoeff g) ∧ F = g * X ^ N + C p * h

theorem WF.mul {O : Type} [CommRing O] {p : O} {F F' : PowerSeries O} {N N' : ℕ} (h1 : WF p F N)
    (h2 : WF p F' N') : WF p (F * F') (N + N') := by
  obtain ⟨g, h, hg, rfl⟩ := h1
  obtain ⟨g', h', hg', rfl⟩ := h2
  refine ⟨g * g', g * X ^ N * h' + h * (g' * X ^ N' + C p * h'), by rw [map_mul]; exact hg.mul hg', ?_⟩
  rw [pow_add]; ring

theorem WF.one {O : Type} [CommRing O] (p : O) : WF p 1 0 :=
  ⟨1, 0, by simp, by simp⟩

theorem WF.X {O : Type} [CommRing O] (p : O) : WF p X 1 :=
  ⟨1, 0, by simp, by simp⟩

theorem WF.pow {O : Type} [CommRing O] {p : O} {F : PowerSeries O} {N : ℕ} (h : WF p F N) (k : ℕ) :
    WF p (F ^ k) (N * k) := by
  induction k with
  | zero => simpa using WF.one p
  | succ k ih => rw [pow_succ, Nat.mul_succ]; exact ih.mul h

theorem WF.prod {O : Type} [CommRing O] {p : O} (F : ℕ → PowerSeries O) (N : ℕ → ℕ)
    (h : ∀ t, WF p (F t) (N t)) (e : ℕ) :
    WF p (∏ t ∈ Finset.range e, F t) (∑ t ∈ Finset.range e, N t) := by
  induction e with
  | zero => simpa using WF.one p
  | succ e ih => rw [Finset.prod_range_succ, Finset.sum_range_succ]; exact ih.mul (h e)

section Idem

variable {A : Type} [CommRing A] {E : A}

theorem idem_mul (_hE : E * E = E) {x y : A} (h : x * E = y * E) (z : A) : (z * x) * E = (z * y) * E := by
  rw [mul_assoc, h, ← mul_assoc]

theorem idem_pow (hE : E * E = E) {x y : A} (h : x * E = y * E) (k : ℕ) : x ^ k * E = y ^ k * E := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc x ^ (k + 1) * E = (x ^ k * E) * (x * E) := by rw [pow_succ]; linear_combination (-(x ^ k * x)) * hE
      _ = (y ^ k * E) * (y * E) := by rw [ih, h]
      _ = y ^ (k + 1) * E := by rw [pow_succ]; linear_combination (y ^ k * y) * hE

theorem idem_prod (hE : E * E = E) (x y : ℕ → A) (h : ∀ t, x t * E = y t * E) (e : ℕ) :
    (∏ t ∈ Finset.range e, x t) * E = (∏ t ∈ Finset.range e, y t) * E := by
  induction e with
  | zero => simp
  | succ e ih =>
    calc (∏ t ∈ Finset.range (e + 1), x t) * E = ((∏ t ∈ Finset.range e, x t) * E) * (x e * E) := by
          rw [Finset.prod_range_succ]; linear_combination (-((∏ t ∈ Finset.range e, x t) * x e)) * hE
      _ = ((∏ t ∈ Finset.range e, y t) * E) * (y e * E) := by rw [ih, h]
      _ = (∏ t ∈ Finset.range (e + 1), y t) * E := by
          rw [Finset.prod_range_succ]; linear_combination ((∏ t ∈ Finset.range e, y t) * y e) * hE

end Idem

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem evalZero_X_eq_uniformizer (W : LocWach PD LL O v n) (hR : Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.Ring9 W) :
    Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W X = W.π₀ := by
  funext j
  rw [Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evaluation_apply, subst_X (Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.hasSubst W hR)]
  rfl

theorem ps_letter [IsDomain O] (W : LocWach PD LL O v n) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W)
    (hp0 : ((PD.p : ℕ) : O) ≠ 0) (a : ZMod n) (t : ℕ) :
    ∃ F : PowerSeries O, WF ((PD.p : ℕ) : O) F (PD.p ^ t) ∧
      Formalism.MainNotions.ArcLiftingSetup.ps W t * letE a = Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W F * letE a := by
  obtain ⟨v, hvΔ, hvu, r, hr⟩ := Formalism.MainNotions.UnusedSlot80.ToolsR.modp hR hp0 t
  have hps : Formalism.MainNotions.ArcLiftingSetup.ps W t = v * W.π₀ ^ (PD.p ^ t) + ((PD.p : ℕ) : LetA O n) * (r + 1) := by
    have := Formalism.MainNotions.UnusedSlot80.ToolsR.pS_sub (W := W) t
    rw [hr] at this
    change Formalism.MainNotions.WachCoordinates.pS W t = _
    linear_combination this
  have hpsΔ : Formalism.MainNotions.ArcLiftingSetup.ps W t ∈ W.AΔ :=
    Formalism.MainNotions.UnusedSlot80.ToolsR.φpow_AΔ t (Formalism.MainNotions.UnusedSlot80.ToolsR.qP_AΔ hR)
  have hpΔ : ((PD.p : ℕ) : LetA O n) ∈ W.AΔ := Subalgebra.natCast_mem _ _
  have hr1 : r + 1 ∈ W.AΔ := by
    refine Formalism.MainNotions.UnusedSlot80.ToolsR.cancel_AΔ hpΔ (fun i => ?_) ?_
    · simp only [Pi.natCast_apply]
      exact_mod_cast (by
        intro h
        have := congrArg constantCoeff h
        simp only [map_natCast, map_zero] at this
        exact hp0 this : ((PD.p : ℕ) : PowerSeries O) ≠ 0)
    · have : ((PD.p : ℕ) : LetA O n) * (r + 1) = Formalism.MainNotions.ArcLiftingSetup.ps W t - v * W.π₀ ^ (PD.p ^ t) := by
        rw [hps]; ring
      rw [this]
      exact W.AΔ.sub_mem hpsΔ (W.AΔ.mul_mem hvΔ (W.AΔ.pow_mem hR.1 _))
  obtain ⟨gv, hgv⟩ := Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.invariant_letter_eq_evaluation W hR hvΔ a
  obtain ⟨gr, hgr⟩ := Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.invariant_letter_eq_evaluation W hR hr1 a
  have hE := Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.letE_mul_self' (O := O) a
  refine ⟨gv * X ^ (PD.p ^ t) + C ((PD.p : ℕ) : O) * gr, ⟨gv, gr, ?_, rfl⟩, ?_⟩
  · have h1 := congrFun hgv a
    simp only [Pi.mul_apply, letE, Pi.single_eq_same, mul_one, Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evaluation_apply] at h1
    have hva : IsUnit (v a) := hvu.map (Pi.evalRingHom (fun _ : ZMod n => PowerSeries O) a)
    rw [h1] at hva
    have := hva.map constantCoeff
    rwa [Formalism.MainNotions.UnusedSlot80.ToolsR.cc_subst (Formalism.MainNotions.UnusedSlot80.ToolsR.π₀₁_cc hR)] at this
  · have hC : Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (C ((PD.p : ℕ) : O)) = ((PD.p : ℕ) : LetA O n) := by
      rw [map_natCast, Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evaluation_eq_homomorphism W hR, map_natCast]
    have hX : Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (X ^ (PD.p ^ t)) = W.π₀ ^ (PD.p ^ t) := by
      rw [Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evaluation_eq_homomorphism W hR, map_pow, ← Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evaluation_eq_homomorphism W hR, evalZero_X_eq_uniformizer W hR]
    rw [Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evaluation_add W hR, Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evalZero_mul W hR, Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evalZero_mul W hR, hX, hC,
      hps]
    linear_combination (W.π₀ ^ (PD.p ^ t)) * hgv + ((PD.p : ℕ) : LetA O n) * hgr

theorem finLev_of [IsDomain O] (W : LocWach PD LL O v n) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W)
    (hp0 : ((PD.p : ℕ) : O) ≠ 0) [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O]
    (hpu : ¬ IsUnit ((PD.p : ℕ) : O)) : FinLev W := by
  intro a e H
  set pO : O := ((PD.p : ℕ) : O) with hpO
  set I : Ideal O := Ideal.span {pO} with hI
  have hE := Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.letE_mul_self' (O := O) a
  choose Fs hFs hFe using fun t => ps_letter W hR hp0 a t
  set Gall : PowerSeries O := X * (∏ t ∈ Finset.range e, Fs t ^ H t) ^ 2 with hGall
  have hWF : WF pO Gall (1 + (∑ t ∈ Finset.range e, PD.p ^ t * H t) * 2) :=
    (WF.X pO).mul ((WF.prod (fun t => Fs t ^ H t) (fun t => PD.p ^ t * H t)
      (fun t => (hFs t).pow (H t)) e).pow 2)
  set D := 1 + (∑ t ∈ Finset.range e, PD.p ^ t * H t) * 2 with hD
  have hlet : W.π₀ * (∏ t ∈ Finset.range e, Formalism.MainNotions.ArcLiftingSetup.ps W t ^ H t) ^ 2 * letE a =
      Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W Gall * letE a := by
    have h1 : (∏ t ∈ Finset.range e, Formalism.MainNotions.ArcLiftingSetup.ps W t ^ H t) * letE a =
        (∏ t ∈ Finset.range e, Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (Fs t) ^ H t) * letE a :=
      idem_prod hE _ _ (fun t => idem_pow hE (hFe t) (H t)) e
    have h2 := idem_mul hE (idem_pow hE h1 2) W.π₀
    rw [h2, hGall, Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evaluation_eq_homomorphism W hR, map_mul, map_pow, map_prod, ← Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evaluation_eq_homomorphism W hR,
      evalZero_X_eq_uniformizer W hR]
    simp only [Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evaluation_eq_homomorphism W hR, map_pow]
  obtain ⟨g, h, hgu, hGe⟩ := hWF
  obtain ⟨P, uu, huu, hPm, hPd, hPc, hGP⟩ := Formalism.MainNotions.UnusedSlot80.ToolsR.weierP pO hpu D g h hgu
  have hmapP : (P : PowerSeries O).map (Ideal.Quotient.mk I) = X ^ D := by
    ext k
    rw [coeff_map, Polynomial.coeff_coe, coeff_X_pow]
    split_ifs with hk
    · subst hk; rw [← hPd, hPm.coeff_natDegree, map_one]
    · rcases lt_or_gt_of_ne hk with hlt | hgt
      · exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton.2 (hPc k hlt))
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), map_zero]
  haveI : Nontrivial (O ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr (by
    rw [Ne, hI, Ideal.span_singleton_eq_top]; exact hpu)
  have hord : ((P : PowerSeries O).map (Ideal.Quotient.mk I)).order.toNat = D := by
    rw [hmapP, order_X_pow]; rfl
  have hdiv : (P : PowerSeries O).IsWeierstrassDivisorAt I := by
    unfold PowerSeries.IsWeierstrassDivisorAt
    rw [hord, Polynomial.coeff_coe, ← hPd, hPm.coeff_natDegree]
    exact isUnit_one
  refine ⟨D, fun u hu => ?_⟩
  obtain ⟨f, hf⟩ := Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.invariant_letter_eq_evaluation W hR hu a
  have HD := hdiv.isWeierstrassDivisionAt_div_mod f
  set q := hdiv.div f
  set r := hdiv.mod f
  have hdeg : r.degree < (D : WithBot ℕ) := by
    have := HD.degree_lt
    rw [hord] at this
    exact this
  have heq : f = (P : PowerSeries O) * q + (r : PowerSeries O) := HD.eq_mul_add
  have hfG : f = Gall * (↑huu.unit⁻¹ * q) + (r : PowerSeries O) := by
    rw [heq, hGe, hGP, mul_assoc, ← mul_assoc uu, IsUnit.mul_val_inv, one_mul]
  refine ⟨fun j => r.coeff j, Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (↑huu.unit⁻¹ * q),
    Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evaluation_mem_invariants W hR _, ?_⟩
  have hr : Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (r : PowerSeries O) =
      ∑ j : Fin D, algebraMap O (LetA O n) (r.coeff j) * W.π₀ ^ (j : ℕ) := by
    rw [Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evaluation_eq_homomorphism W hR, Formalism.MainNotions.RamifiedCoefficientChains.S9.Ring.algHom_coe, ← Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evaluation_eq_homomorphism W hR,
      evalZero_X_eq_uniformizer W hR]
    have hnd : r.natDegree < D := by
      by_cases hr0 : r = 0
      · rw [hr0, Polynomial.natDegree_zero]; omega
      · exact (Polynomial.natDegree_lt_iff_degree_lt hr0).2 hdeg
    rw [Polynomial.aeval_eq_sum_range' hnd, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def]
  have hu' : (letE a : LetA O n) * u = letE a * Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W f := by
    rw [mul_comm, hf, mul_comm]
  rw [hu', hfG, Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evaluation_add W hR, Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evalZero_mul W hR, hr]
  have h3 : (letE a : LetA O n) * Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W Gall =
      W.π₀ * (∏ t ∈ Finset.range e, Formalism.MainNotions.ArcLiftingSetup.ps W t ^ H t) ^ 2 * letE a := by
    rw [hlet, mul_comm]
  linear_combination (Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (↑huu.unit⁻¹ * q)) * h3

end Formalism.MainNotions.UnusedSlot80.UGen
end
end

noncomputable section

namespace Formalism.MainNotions.UnusedSlot80.UGen

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.KL

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem univGenCore_of_lev [IsDomain O] [IsPrincipalIdealRing O] [NeZero n]
    [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O] [Fintype (K →ₐ[Qp] LL)]
    (W : LocWach PD LL O v n) (hinj : Function.Injective (algebraMap O LL))
    (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x)
    (hpu : ¬ IsUnit ((PD.p : ℕ) : O))
    (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hKL : KillerLevCore W) (hS : PsStable W)
    (hRAT : CutU.RATCore W)
    (hInv : ∀ (A : ArcP n) (c : ZMod n), c ∈ A.cuts → ∀ s < A.len c, InvLevAt W s) :
    Formalism.MainNotions.UnusedSlot80.UnivC.UnivGenCore PD W :=
  univGenCore_of' W hinj hO2 hpu hR hKL hS hRAT hInv (finLev_of W hR (p_ne_zero_O' W) hpu)

theorem universal_generators_of_units [IsDomain O] [IsPrincipalIdealRing O] [NeZero n]
    [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O] [Fintype (K →ₐ[Qp] LL)]
    (W : LocWach PD LL O v n) (hinj : Function.Injective (algebraMap O LL))
    (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x)
    (hpu : ¬ IsUnit ((PD.p : ℕ) : O)) :
    Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W → KillerLevCore W → PsStable W → W.π₀ ∈ W.AΔ →
      CutU.RATCore W → CutU.InvLevCore W → Formalism.MainNotions.UnusedSlot80.UnivC.UnivGenCore PD W :=
  fun hR hKL hS _ hRAT hInv =>
    univGenCore_of_lev W hinj hO2 hpu hR hKL hS hRAT fun _ _ _ s _ => invLevAt_of W hInv s

end Formalism.MainNotions.UnusedSlot80.UGen
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.UniversalGeneralOfInverseLevels
noncomputable section

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup

theorem universal_general_of_inverse_levels (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (hAdm : AdmUnivA D HW F Cm) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F)
    (hH : Formalism.MainNotions.LiftingTheory.ConclusionH D HW F) (h15 : Formalism.MainNotions.TruncatedSeriesCountingBounds.adm15 D)
    (hInv : AtCaseA fun l _ K LL hG => Formalism.MainNotions.UnusedSlot80.CutU.InvLevCore ((HW l).W K 1 LL hG))
    (hUG : UnivGenL D HW) : UniversalComponentCaseA D HW F Cm :=
  universal_general_of_window D HW F Cm hAdm h9 hH h15 (killWinL_of D HW F Cm hAdm h9 hInv) hUG

end Formalism.MainNotions.UnusedSlot80
end
end

noncomputable section

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup

theorem univGenL_of (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (hAdm : AdmUnivA D HW F Cm) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F)
    (hInv : AtCaseA fun l _ K LL hG => Formalism.MainNotions.UnusedSlot80.CutU.InvLevCore ((HW l).W K 1 LL hG)) :
    UnivGenL D HW := by
  intro l _ K LL hG hCA h5 _
  obtain ⟨⟨hdom, -, -⟩, -⟩ := Formalism.MainNotions.N.T2.litGoodO l LL
  haveI := hdom
  haveI : IsDiscreteValuationRing ↥(OL LL) := Formalism.BasicNotions.Examples₂.LB.OL_dvr LL
  have : FiniteDimensional ℚ_[l] ↥(K0 K) := ((D.loc l).PD K).finK₀
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  haveI : IsAdicComplete (Ideal.span {((((D.loc l).PD K).p : ℕ) : ↥(OL LL))}) ↥(OL LL) := by
    rw [(D.loc l).PD_p]
    exact Formalism.MainNotions.WachCoordinates.Br.complete_OL LL
  have hR : ToolsR.RingP ((HW l).W K 1 LL hG) := ring_condition_uniformizer_polynomial D HW F h9 l K LL hCA
  have hT : Formalism.MainNotions.WachCoordinates.ToolsAlg ((HW l).W K 1 LL hG) := tool_algebra_of_ring_condition D HW F h9 l K LL hCA h5
  have hV := Formalism.MainNotions.WachCoordinates.Br.valRing_rec (D.loc l) LL
  have hpu := Formalism.MainNotions.WachCoordinates.Br.not_isUnit_p ((HW l).W K 1 LL hG) hV
  have hKL := hAdm.2.1 l K LL hG hCA h5
  exact Formalism.MainNotions.UnusedSlot80.UGen.universal_generators_of_units ((HW l).W K 1 LL hG) hV.1 hV.2.1 hpu hR hKL
    (Formalism.MainNotions.UnusedSlot80.KF.psStable_of _ hR) hR.1
    (Formalism.MainNotions.UnusedSlot80.RatW.ratCore_of _ hR hT hR.2.2.1 hR.1) (hInv l K LL hG hCA h5)

theorem universal_general_of_level_inverse (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (hAdm : AdmUnivA D HW F Cm) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F)
    (hH : Formalism.MainNotions.LiftingTheory.ConclusionH D HW F) (h15 : Formalism.MainNotions.TruncatedSeriesCountingBounds.adm15 D)
    (hInv : AtCaseA fun l _ K LL hG => Formalism.MainNotions.UnusedSlot80.CutU.InvLevCore ((HW l).W K 1 LL hG)) :
    UniversalComponentCaseA D HW F Cm :=
  universal_general_of_inverse_levels D HW F Cm hAdm h9 hH h15 hInv (univGenL_of D HW F Cm hAdm h9 hInv)

end Formalism.MainNotions.UnusedSlot80
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.ReductionZeroOfPrincipalUnit
namespace Formalism.MainNotions.UnusedSlot80.InvCutPfL

open Formalism.MainNotions.N.Ln03 Formalism.MainNotions.UnusedSlot80.InvCut

section Part1

variable (LL : Type) [Field LL] (l : ℕ) [Fact l.Prime] (s : ℕ)

theorem invCutPf_precomp_mul (a b : (ZMod (l ^ (s + 1)))ˣ) (f : Rs LL l s → LL) :
    precomp LL l s a (precomp LL l s b f) = precomp LL l s (a * b) f := by
  funext ζ
  simp only [precomp_apply, powR_powR]

theorem invCutPf_precomp_one (f : Rs LL l s → LL) : precomp LL l s 1 f = f := by
  funext ζ
  simp only [precomp_apply, powR_one]

def invCutPf_stab (f : Rs LL l s → LL) : Subgroup (ZMod (l ^ (s + 1)))ˣ where
  carrier := {a | precomp LL l s a f = f}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [← invCutPf_precomp_mul, hb, ha]
  one_mem' := invCutPf_precomp_one LL l s f
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at ha ⊢
    calc precomp LL l s a⁻¹ f = precomp LL l s a⁻¹ (precomp LL l s a f) := by rw [ha]
      _ = f := by rw [invCutPf_precomp_mul, inv_mul_cancel, invCutPf_precomp_one]

theorem invCutPf_mem_stab (f : Rs LL l s → LL) (a : (ZMod (l ^ (s + 1)))ˣ) :
    a ∈ invCutPf_stab LL l s f ↔ precomp LL l s a f = f := Iff.rfl

theorem invCutPf_exists_pow (ζ₀ ζ : Rs LL l s) : ∃ a, powR LL l s a ζ₀ = ζ := by
  have hN : 0 < l ^ (s + 1) := pos_pow l s
  haveI : NeZero (l ^ (s + 1)) := ⟨hN.ne'⟩
  have h0 : IsPrimitiveRoot (ζ₀ : LL) (l ^ (s + 1)) := (mem_primitiveRoots hN).1 ζ₀.2
  have h1 : IsPrimitiveRoot (ζ : LL) (l ^ (s + 1)) := (mem_primitiveRoots hN).1 ζ.2
  obtain ⟨i, hi, hζ⟩ := h0.eq_pow_of_pow_eq_one h1.pow_eq_one
  have hcop : i.Coprime (l ^ (s + 1)) := (h0.pow_iff_coprime hN i).1 (by rw [hζ]; exact h1)
  refine ⟨ZMod.unitOfCoprime i hcop, Subtype.ext ?_⟩
  show (ζ₀ : LL) ^ ((ZMod.unitOfCoprime i hcop : ZMod (l ^ (s + 1)))).val = ζ
  rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi, hζ]

end Part1

theorem precompConst : PrecompConst := by
  intro LL _ l _ s S hS f hf
  by_cases h : Nonempty (Rs LL l s)
  · obtain ⟨ζ₀⟩ := h
    refine ⟨f ζ₀, fun ζ => ?_⟩
    have hle : Subgroup.closure S ≤ invCutPf_stab LL l s f :=
      (Subgroup.closure_le _).2 fun a ha => (invCutPf_mem_stab LL l s f a).2 (hf a ha)
    obtain ⟨a, rfl⟩ := invCutPf_exists_pow LL l s ζ₀ ζ
    have ha : precomp LL l s a f = f :=
      (invCutPf_mem_stab LL l s f a).1 (hle (by rw [hS]; exact Subgroup.mem_top a))
    exact (precomp_apply LL l s a f ζ₀).symm.trans (congrFun ha ζ₀)
  · exact ⟨0, fun ζ => (h ⟨ζ⟩).elim⟩

section Part2

variable {l : ℕ} [Fact l.Prime]

theorem invCutPf_toZModPow_eq_zero {n : ℕ} {z : ℤ_[l]} :
    PadicInt.toZModPow n z = 0 ↔ z ∈ Ideal.span {(l : ℤ_[l]) ^ n} := by
  rw [← PadicInt.ker_toZModPow, RingHom.mem_ker]

theorem invCutPf_eq_one_iff {k : ℕ} {z : ℤ_[l]} :
    PadicInt.toZModPow k z = 1 ↔ z - 1 ∈ Ideal.span {(l : ℤ_[l]) ^ k} := by
  rw [← invCutPf_toZModPow_eq_zero, map_sub, map_one, sub_eq_zero]

theorem invCutPf_lt_one_iff {z : ℤ_[l]} : ‖z‖ < 1 ↔ PadicInt.toZModPow 1 z = 0 := by
  rw [PadicInt.norm_lt_one_iff_dvd, invCutPf_toZModPow_eq_zero, pow_one, Ideal.mem_span_singleton]

theorem invCutPf_norm_eq_one {z : ℤ_[l]} (h : PadicInt.toZModPow 1 z ≠ 0) : ‖z‖ = 1 := by
  rcases (PadicInt.norm_le_one z).lt_or_eq with h1 | h1
  · exact absurd (invCutPf_lt_one_iff.1 h1) h
  · exact h1

theorem invCutPf_congr {z w : ℤ_[l]} (h : ‖z - w‖ < 1) :
    PadicInt.toZModPow 1 z = PadicInt.toZModPow 1 w := by
  rw [← sub_eq_zero, ← map_sub]
  exact invCutPf_lt_one_iff.1 h

theorem invCutPf_lower {k n : ℕ} (h : k ≤ n) {z w : ℤ_[l]}
    (e : PadicInt.toZModPow n z = PadicInt.toZModPow n w) :
    PadicInt.toZModPow k z = PadicInt.toZModPow k w := by
  rw [← PadicInt.zmod_cast_comp_toZModPow k n h, RingHom.comp_apply, RingHom.comp_apply, e]

theorem invCutPf_le (s : ℕ) : 0 + 1 ≤ s + 1 := by omega

def invCutPf_rho (s : ℕ) : (ZMod (l ^ (s + 1)))ˣ →* (ZMod (l ^ (0 + 1)))ˣ :=
  ZMod.unitsMap (pow_dvd_pow l (invCutPf_le s))

theorem invCutPf_rho_red (s : ℕ) (x : ℤ_[l]ˣ) : invCutPf_rho s (redU l s x) = redU l 0 x :=
  Units.ext (RingHom.congr_fun (PadicInt.zmod_cast_comp_toZModPow (0 + 1) (s + 1) (invCutPf_le s))
    (x : ℤ_[l]))

theorem reduction_zero_of_principal_unit (u : ℤ_[l]ˣ) (h1 : (u : ℤ_[l]) - 1 ∈ Ideal.span {(l : ℤ_[l])}) :
    redU l 0 u = 1 := by
  apply Units.ext
  show PadicInt.toZModPow (0 + 1) (u : ℤ_[l]) = 1
  rw [invCutPf_eq_one_iff, zero_add, pow_one]
  exact h1

theorem invCutPf_teich (x : (ZMod (l ^ 1))ˣ) : ∃ d : DeltaT l, redU l 0 d.1 = x := by
  have hl := (Fact.out : l.Prime)
  haveI : NeZero (l ^ 1) := ⟨pow_ne_zero _ hl.ne_zero⟩
  haveI : Fact (1 < l ^ 1) := ⟨by rw [pow_one]; exact hl.one_lt⟩
  obtain ⟨a, ha⟩ : ∃ a : ℤ_[l], a = (((x : ZMod (l ^ 1)).val : ℕ) : ℤ_[l]) := ⟨_, rfl⟩
  have hxa : PadicInt.toZModPow 1 a = x := by
    rw [ha, map_natCast, ZMod.natCast_zmod_val]
  have hanorm : ‖a‖ = 1 := invCutPf_norm_eq_one (by rw [hxa]; exact x.ne_zero)
  have htot : Nat.totient (l ^ 1) = l - 1 := by rw [pow_one, Nat.totient_prime hl]
  have hferm : (x : ZMod (l ^ 1)) ^ (l - 1) = 1 := by
    have h := pow_card_eq_one (x := x)
    rw [ZMod.card_units_eq_totient, htot] at h
    rw [← Units.val_pow_eq_pow_val, h, Units.val_one]
  have hl1norm : ‖((l - 1 : ℕ) : ℤ_[l])‖ = 1 := by
    apply invCutPf_norm_eq_one
    rw [map_natCast, Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    have := Nat.le_of_dvd (by have := hl.two_le; omega) hd
    rw [pow_one] at this
    have := hl.two_le
    omega
  have hFa : ‖Polynomial.aeval a ((Polynomial.X ^ (l - 1) - 1 : Polynomial ℤ_[l]))‖ < 1 := by
    rw [invCutPf_lt_one_iff]
    simp only [map_sub, map_pow, Polynomial.aeval_X, map_one, hxa, hferm, sub_self]
  have hder : ‖Polynomial.aeval a
      (Polynomial.derivative (Polynomial.X ^ (l - 1) - 1 : Polynomial ℤ_[l]))‖ = 1 := by
    simp only [Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_one,
      sub_zero, map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X, Algebra.algebraMap_self,
      RingHom.id_apply, norm_mul, norm_pow, hanorm, one_pow, mul_one]
    exact hl1norm
  obtain ⟨z, hz, hza, -, -⟩ := hensels_lemma (F := (Polynomial.X ^ (l - 1) - 1 : Polynomial ℤ_[l]))
    (a := a) (by rw [hder, one_pow]; exact hFa)
  rw [hder] at hza
  have hz1 : z ^ (l - 1) = 1 := by
    simpa [sub_eq_zero] using hz
  have hl1 : l - 1 ≠ 0 := by have := hl.two_le; omega
  have hzu : IsUnit z := IsUnit.of_pow_eq_one hz1 hl1
  refine ⟨⟨hzu.unit, Units.ext (by simpa using hz1)⟩, Units.ext ?_⟩
  show PadicInt.toZModPow 1 z = (x : ZMod (l ^ 1))
  rw [invCutPf_congr hza, hxa]

theorem invCutPf_pow_eq_one_iff (n : ℕ) (u : ℤ_[l]ˣ) (m : ℕ)
    (hmu : ((m : ℕ) : ZMod (l ^ (n + 1))) = PadicInt.toZModPow (n + 1) (u : ℤ_[l])) (hm : 1 ≤ m)
    (e : ℕ) : redU l n u ^ e = 1 ↔ l ^ (n + 1) ∣ m ^ e - 1 := by
  rw [← Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hm), ← ZMod.natCast_eq_natCast_iff, Nat.cast_pow,
    Nat.cast_one, hmu, Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one]
  exact eq_comm

theorem invCutPf_orderOf (hl2 : l ≠ 2) (s : ℕ) (u : ℤ_[l]ˣ)
    (h1 : (u : ℤ_[l]) - 1 ∈ Ideal.span {(l : ℤ_[l])})
    (h2 : (u : ℤ_[l]) - 1 ∉ Ideal.span {(l : ℤ_[l]) ^ 2}) :
    orderOf (redU l s u) = l ^ s := by
  have hl := (Fact.out : l.Prime)
  cases s with
  | zero => rw [pow_zero, orderOf_eq_one_iff]; exact reduction_zero_of_principal_unit u h1
  | succ t =>
    haveI : NeZero (l ^ (t + 1 + 1)) := ⟨(pos_pow l (t + 1)).ne'⟩
    obtain ⟨m, hm_def⟩ : ∃ m : ℕ, m = (PadicInt.toZModPow (t + 1 + 1) (u : ℤ_[l])).val := ⟨_, rfl⟩
    have hmu : ((m : ℕ) : ZMod (l ^ (t + 1 + 1))) = PadicInt.toZModPow (t + 1 + 1) (u : ℤ_[l]) := by
      rw [hm_def, ZMod.natCast_zmod_val]
    have hmu' : PadicInt.toZModPow (t + 1 + 1) ((m : ℕ) : ℤ_[l]) =
        PadicInt.toZModPow (t + 1 + 1) (u : ℤ_[l]) := by
      rw [map_natCast, hmu]
    have hk : ∀ k ≤ t + 1 + 1,
        (((m : ℕ) : ZMod (l ^ k)) = 1 ↔ (u : ℤ_[l]) - 1 ∈ Ideal.span {(l : ℤ_[l]) ^ k}) := by
      intro k hk
      rw [← map_natCast (PadicInt.toZModPow (p := l) k) m, invCutPf_lower hk hmu', invCutPf_eq_one_iff]
    have hl2' : 1 < l ^ 2 := Nat.one_lt_pow two_ne_zero hl.one_lt
    have hA : m % l = 1 := by
      have := (hk 1 (by omega)).2 (by rw [pow_one]; exact h1)
      rw [← Nat.cast_one (R := ZMod (l ^ 1)), ZMod.natCast_eq_natCast_iff', pow_one,
        Nat.mod_eq_of_lt hl.one_lt] at this
      exact this
    have hB : m % l ^ 2 ≠ 1 := by
      intro hc
      apply h2
      apply (hk 2 (by omega)).1
      rw [← Nat.cast_one (R := ZMod (l ^ 2)), ZMod.natCast_eq_natCast_iff', hc, Nat.mod_eq_of_lt hl2']
    have hm1 : 1 < m := by
      rcases Nat.lt_or_ge 1 m with h | h
      · exact h
      · interval_cases m
        · simp at hA
        · exact absurd (Nat.mod_eq_of_lt hl2') hB
    have hdvd1 : l ∣ m - 1 := (Nat.modEq_iff_dvd' hm1.le).1 (by
      show 1 % l = m % l
      rw [hA, Nat.mod_eq_of_lt hl.one_lt])
    have hndvd2 : ¬ l ^ 2 ∣ m - 1 := fun hd => hB (by
      have : 1 % l ^ 2 = m % l ^ 2 := (Nat.modEq_iff_dvd' hm1.le).2 hd
      rw [← this, Nat.mod_eq_of_lt hl2'])
    have hndvd : ¬ l ∣ m := by
      rw [Nat.dvd_iff_mod_eq_zero, hA]; exact one_ne_zero
    have hm0 : m - 1 ≠ 0 := by omega
    have hv1 : padicValNat l (m - 1) = 1 := by
      have a1 : 1 ≤ padicValNat l (m - 1) := ((by simpa only [_root_.Nat.padicValNat_def] using @_root_.multiplicity_dvd_iff_le : ∀ {p : _root_.Nat} [hp : _root_.Fact (_root_.Nat.Prime p)] {a n : _root_.Nat} (ha : a ≠ 0), p ^ n ∣ a ↔ n ≤ _root_.padicValNat p a) hm0).1 (by rw [pow_one]; exact hdvd1)
      have a2 : ¬ 2 ≤ padicValNat l (m - 1) := fun h => hndvd2 (((by simpa only [_root_.Nat.padicValNat_def] using @_root_.multiplicity_dvd_iff_le : ∀ {p : _root_.Nat} [hp : _root_.Fact (_root_.Nat.Prime p)] {a n : _root_.Nat} (ha : a ≠ 0), p ^ n ∣ a ↔ n ≤ _root_.padicValNat p a) hm0).2 h)
      omega
    have hodd : Odd l := hl.odd_of_ne_two hl2
    have hv : ∀ j : ℕ, padicValNat l (m ^ (l ^ j) - 1) = 1 + j := by
      intro j
      have := padicValNat.pow_sub_pow hodd hm1 hdvd1 hndvd (pow_ne_zero j hl.ne_zero)
      rw [one_pow] at this
      rw [Nat.padicValNat_def] at hv1 ⊢
      rw [this, hv1, Nat.multiplicity_prime_pow]
    have hne : ∀ j : ℕ, m ^ (l ^ j) - 1 ≠ 0 := by
      intro j
      have := Nat.one_lt_pow (pow_ne_zero j hl.ne_zero) hm1
      omega
    apply orderOf_eq_prime_pow
    · rw [invCutPf_pow_eq_one_iff (t + 1) u m hmu hm1.le, (by simpa only [_root_.Nat.padicValNat_def] using @_root_.multiplicity_dvd_iff_le : ∀ {p : _root_.Nat} [hp : _root_.Fact (_root_.Nat.Prime p)] {a n : _root_.Nat} (ha : a ≠ 0), p ^ n ∣ a ↔ n ≤ _root_.padicValNat p a) (hne t), hv]
      omega
    · rw [invCutPf_pow_eq_one_iff (t + 1) u m hmu hm1.le, (by simpa only [_root_.Nat.padicValNat_def] using @_root_.multiplicity_dvd_iff_le : ∀ {p : _root_.Nat} [hp : _root_.Fact (_root_.Nat.Prime p)] {a n : _root_.Nat} (ha : a ≠ 0), p ^ n ∣ a ↔ n ≤ _root_.padicValNat p a) (hne (t + 1)), hv]
      omega

theorem invCutPf_card_ker (s : ℕ) : Nat.card (invCutPf_rho (l := l) s).ker = l ^ s := by
  have hl := (Fact.out : l.Prime)
  haveI : NeZero (l ^ (s + 1)) := ⟨(pos_pow l s).ne'⟩
  haveI : NeZero (l ^ (0 + 1)) := ⟨(pos_pow l 0).ne'⟩
  have hsurj : Function.Surjective (invCutPf_rho (l := l) s) :=
    ZMod.unitsMap_surjective (pow_dvd_pow l (invCutPf_le s))
  have e1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (invCutPf_rho (l := l) s).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hsurj).toEquiv,
    Nat.card_eq_fintype_card (α := (ZMod (l ^ (s + 1)))ˣ),
    Nat.card_eq_fintype_card (α := (ZMod (l ^ (0 + 1)))ˣ),
    ZMod.card_units_eq_totient, ZMod.card_units_eq_totient, Nat.totient_prime_pow_succ hl,
    Nat.totient_prime_pow_succ hl, pow_zero, one_mul] at e1
  have hpos : 0 < l - 1 := by have := hl.two_le; omega
  exact Nat.eq_of_mul_eq_mul_left hpos (e1.symm.trans (mul_comm _ _))

theorem invCutPf_ker_eq (hl2 : l ≠ 2) (s : ℕ) (u : ℤ_[l]ˣ)
    (h1 : (u : ℤ_[l]) - 1 ∈ Ideal.span {(l : ℤ_[l])})
    (h2 : (u : ℤ_[l]) - 1 ∉ Ideal.span {(l : ℤ_[l]) ^ 2}) :
    (invCutPf_rho (l := l) s).ker = Subgroup.zpowers (redU l s u) := by
  haveI : NeZero (l ^ (s + 1)) := ⟨(pos_pow l s).ne'⟩
  symm
  apply Subgroup.eq_of_le_of_card_ge
  · rw [Subgroup.zpowers_le, MonoidHom.mem_ker, invCutPf_rho_red, reduction_zero_of_principal_unit u h1]
  · rw [Nat.card_zpowers, invCutPf_orderOf hl2 s u h1 h2, invCutPf_card_ker]

end Part2

theorem genUnits : GenUnits := by
  intro l _ hl2 s u h1 h2
  rw [eq_top_iff]
  intro g _
  obtain ⟨d, hd⟩ := invCutPf_teich (l := l) (invCutPf_rho s g)
  have hk : g * (redU l s d.1)⁻¹ ∈ (invCutPf_rho (l := l) s).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, invCutPf_rho_red, hd, mul_inv_cancel]
  rw [invCutPf_ker_eq hl2 s u h1 h2] at hk
  have hu : redU l s u ∈ Subgroup.closure
      (insert (redU l s u) (Set.range fun d : DeltaT l => redU l s d.1)) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hdm : redU l s d.1 ∈ Subgroup.closure
      (insert (redU l s u) (Set.range fun d : DeltaT l => redU l s d.1)) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ ⟨d, rfl⟩)
  have hz := (Subgroup.zpowers_le.2 hu) hk
  simpa using Subgroup.mul_mem _ hz hdm

end Formalism.MainNotions.UnusedSlot80.InvCutPfL

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound.LB

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80 Formalism.MainNotions.N.Ln03

def levelBasicsOfRingCondition (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F)
    (hGen : GenUnitsC) (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (h : CaseA K LL)
    (a : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (s : ℕ) :
    LevBasics ((HW l).W K 1 LL h.2.2) a s := by
  have e : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  haveI hpF : Fact ((D.loc l).PD K).p.Prime := ⟨by rw [e]; exact Fact.out⟩
  haveI : IsLocalRing ↥(OL LL) := Formalism.MainNotions.LiftingTheory.lkd_local (D.loc l) LL
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal ↥(OL LL)) ↥(OL LL) := OLC.complete_max LL
  haveI : CharZero ↥(OL LL) := Formalism.MainNotions.UnusedSlot80.levg_charZero LL
  letI : Algebra ℤ_[((D.loc l).PD K).p] ↥(OL LL) :=
    ((algebraMap ℤ_[l] ↥(OL LL)).comp (castZp e)).toAlgebra
  have hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F := h9
  have hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP ((HW l).W K 1 LL h.2.2) :=
    Formalism.MainNotions.UnusedSlot80.ring_condition_uniformizer_polynomial D HW F hP9 l K LL h
  have hlm : ((((D.loc l).PD K).p : ℕ) : ↥(OL LL)) ∈ IsLocalRing.maximalIdeal ↥(OL LL) := by
    rw [e]; exact Formalism.MainNotions.N.Pv.LocalLengthBound.l_mem_maxOL (D.loc l) LL
  have hZinj : Function.Injective (algebraMap ℤ_[((D.loc l).PD K).p] ↥(OL LL)) :=
    (Formalism.MainNotions.LiftingTheory.zl_inj_O LL).comp (castZp_inj e)
  have hχ : ∀ g : ((HW l).W K 1 LL h.2.2).Gam, ∃ z : ℤ_[((D.loc l).PD K).p]ˣ,
      algebraMap ℤ_[((D.loc l).PD K).p] ↥(OL LL) (z : ℤ_[((D.loc l).PD K).p]) =
        (((HW l).W K 1 LL h.2.2).χΓ g : ↥(OL LL)) := by
    intro g
    obtain ⟨z, hz⟩ := Formalism.MainNotions.LiftingTheory.chi_zl (P := D.loc l) (H := HW l) h.2.2 g
    refine ⟨Units.map (castZp e.symm).toMonoidHom z, ?_⟩
    show algebraMap ℤ_[l] ↥(OL LL) (castZp e (castZp e.symm (z : ℤ_[l]))) = _
    rw [castZp_symm, hz]
  have hγz : ∃ z0 : ℤ_[((D.loc l).PD K).p]ˣ,
      algebraMap ℤ_[((D.loc l).PD K).p] ↥(OL LL) (z0 : ℤ_[((D.loc l).PD K).p]) =
        (((HW l).W K 1 LL h.2.2).χΓ ((HW l).W K 1 LL h.2.2).gam : ↥(OL LL)) ∧
      ((z0 : ℤ_[((D.loc l).PD K).p]) - 1).valuation = 1 := by
    obtain ⟨z, hz, hv⟩ := Formalism.MainNotions.LiftingTheory.gam_zl (P := D.loc l) (H := HW l) h.2.2
    refine ⟨Units.map (castZp e.symm).toMonoidHom z, ?_, ?_⟩
    · show algebraMap ℤ_[l] ↥(OL LL) (castZp e (castZp e.symm (z : ℤ_[l]))) = _
      rw [castZp_symm, hz]
    · have : ((Units.map (castZp e.symm).toMonoidHom z : ℤ_[((D.loc l).PD K).p]ˣ) :
          ℤ_[((D.loc l).PD K).p]) - 1 = castZp e.symm ((z : ℤ_[l]) - 1) := by
        rw [map_sub, map_one]; rfl
      rw [this, castZp_val, hv]
  have hcard := Formalism.MainNotions.UnusedSlot80.LevR.card_delF D HW F hP9 l K LL h
  have hp2 : ((D.loc l).PD K).p ≠ 2 := by rw [e]; exact h.2.1
  letI : Algebra ↥(OL LL) (AlgebraicClosure ↥LL.1) :=
    ((algebraMap ↥LL.1 (AlgebraicClosure ↥LL.1)).comp (algebraMap ↥(OL LL) ↥LL.1)).toAlgebra
  have hinjF : Function.Injective (algebraMap ↥(OL LL) (AlgebraicClosure ↥LL.1)) :=
    (algebraMap ↥LL.1 (AlgebraicClosure ↥LL.1)).injective.comp Subtype.val_injective
  haveI : CharZero (AlgebraicClosure ↥LL.1) :=
    charZero_of_injective_algebraMap (algebraMap ↥LL.1 (AlgebraicClosure ↥LL.1)).injective
  exact levBasics_of ((HW l).W K 1 LL h.2.2) hlm (AlgebraicClosure ↥LL.1) hR hinjF hZinj hχ hγz
    (by rw [hcard, e]) hp2 hGen a s

end Formalism.MainNotions.N.Pv.LocalLengthBound.LB

noncomputable section

namespace Formalism.MainNotions.UnusedSlot80.InvW

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80 Formalism.MainNotions.N.Ln03

def levBasics_conv {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} {PD : PeriodData G Qp K₀ K B BdR}
    {W : LocWach PD LL O v n} {a : ZMod n} {s : ℕ} (h : Formalism.MainNotions.N.Pv.LocalLengthBound.LB.LevBasics W a s) :
    LevBasics W a s :=
  ⟨h.F, h.fF, h.algOF, h.inj, h.hp, h.root, h.ev, h.ev_O, h.ev_letE, h.ev_π, h.ev_ps, h.ev_pt, h.σ,
    h.ev_γ, h.gen⟩

theorem invLevCore_L (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F)
    (hRat : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (h : CaseA K LL)
      (a : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (s : ℕ) (hB : LevBasics ((HW l).W K 1 LL h.2.2) a s),
      LevRat ((HW l).W K 1 LL h.2.2) a s hB.F hB.ev) :
    AtCaseA fun l _ K LL hG => Formalism.MainNotions.UnusedSlot80.CutU.InvLevCore ((HW l).W K 1 LL hG) := by
  intro l _ K LL hG hCA h5
  have : FiniteDimensional ℚ_[l] ↥(K0 K) := ((D.loc l).PD K).finK₀
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  obtain ⟨⟨hdom, -, -⟩, -⟩ := Formalism.MainNotions.N.T2.litGoodO l LL
  haveI := hdom
  haveI : IsAdicComplete (Ideal.span {((((D.loc l).PD K).p : ℕ) : ↥(OL LL))}) ↥(OL LL) := by
    rw [(D.loc l).PD_p]
    exact Formalism.MainNotions.WachCoordinates.Br.complete_OL LL
  have hR : ToolsR.RingP ((HW l).W K 1 LL hCA.2.2) := ring_condition_uniformizer_polynomial D HW F h9 l K LL hCA
  have hT : Formalism.MainNotions.WachCoordinates.ToolsAlg ((HW l).W K 1 LL hCA.2.2) := tool_algebra_of_ring_condition D HW F h9 l K LL hCA h5
  have hpu := Formalism.MainNotions.WachCoordinates.Br.not_isUnit_p ((HW l).W K 1 LL hCA.2.2) (Formalism.MainNotions.WachCoordinates.Br.valRing_rec (D.loc l) LL)
  have hB : ∀ (a : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (s : ℕ),
      LevBasics ((HW l).W K 1 LL hCA.2.2) a s := fun a s =>
    levBasics_conv (Formalism.MainNotions.N.Pv.LocalLengthBound.LB.levelBasicsOfRingCondition D HW F h9
      Formalism.MainNotions.UnusedSlot80.InvCutPfL.genUnits l K LL hCA a s)
  exact invLevCore_of_parts ((HW l).W K 1 LL hCA.2.2) hR.1 hB
    (fun a s => levDiv_of ((HW l).W K 1 LL hCA.2.2) hR hT hpu a s (hB a s))
    (fun a s => hRat l K LL hCA a s (hB a s)) Formalism.MainNotions.UnusedSlot80.InvCutPfL.precompConst

end Formalism.MainNotions.UnusedSlot80.InvW
end
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.ExistsDvdPowOfNotIsUnitDvr
noncomputable section

namespace Formalism.MainNotions.UnusedSlot80.InvW

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80 Formalism.MainNotions.N.Ln03

section LevRatPf

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

theorem exists_dvd_pow_of_not_isUnit_dvr [IsDomain O] [IsDiscreteValuationRing O] (p : O) (hp0 : p ≠ 0) (hpu : ¬ IsUnit p)
    {y : O} (hy : y ≠ 0) : ∃ (κ : ℕ) (z : O), p ^ κ = y * z := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨m, u, hyu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hϖ
  obtain ⟨e, u', hpe⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hp0 hϖ
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · exact absurd (by rw [hpe, h, pow_zero, mul_one]; exact u'.isUnit) hpu
    · exact h
  refine ⟨m, ((u⁻¹ : Oˣ) : O) * (u' : O) ^ m * ϖ ^ (e * m - m), ?_⟩
  have hm : m ≤ e * m := Nat.le_mul_of_pos_left m he
  rw [hpe, hyu, mul_pow, ← pow_mul]
  have e1 : ϖ ^ (e * m) = ϖ ^ m * ϖ ^ (e * m - m) := by rw [← pow_add, Nat.add_sub_cancel' hm]
  rw [e1]
  have e2 : ((u : O) * ((u⁻¹ : Oˣ) : O)) = 1 := Units.mul_inv u
  linear_combination (-((u' : O) ^ m * ϖ ^ m * ϖ ^ (e * m - m))) * e2

variable [IsDomain O] [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O]

theorem levRatPf_ev (W : LocWach PD LL O v n) (hR : ToolsR.RingP W) (hT : Formalism.MainNotions.WachCoordinates.ToolsAlg W)
    (hpu : ¬ IsUnit ((PD.p : ℕ) : O)) (a : ZMod n) (s : ℕ) (hB : LevBasics W a s) (g : LetA O n) :
    ∃ r : Polynomial O, r.degree < ((PD.p - 1) * PD.p ^ s : ℕ) ∧
      ∀ ζ : Rs hB.F PD.p s, hB.ev ζ g = Polynomial.aeval ((ζ : hB.F) - 1) r := by
  obtain ⟨H, r, hdeg, heq⟩ := wdiv_ps W hR hT hpu a s (g a)
  refine ⟨r, hdeg, fun ζ => ?_⟩
  set wH : LetA O n := Pi.single a H with hwH
  have hRr : (fun _ : ZMod n => (r : PowerSeries O)) = Polynomial.aeval (letπ : LetA O n) r := by
    funext i
    show (r : PowerSeries O) = Pi.evalAlgHom O (fun _ : ZMod n => PowerSeries O) i (Polynomial.aeval letπ r)
    rw [← Polynomial.aeval_algHom_apply]
    exact (aeval_X_coe r).symm
  have key : (letE a : LetA O n) * g = ps W s * wH + letE a * Polynomial.aeval (letπ : LetA O n) r := by
    rw [← hRr]
    funext i
    by_cases hi : i = a
    · subst hi
      simp only [Pi.mul_apply, Pi.add_apply, hwH, letE, Pi.single_eq_same, one_mul, heq]
    · simp [Pi.mul_apply, Pi.add_apply, hwH, letE, Pi.single_eq_of_ne hi]
  have h1 := congrArg (hB.ev ζ) key
  rw [map_mul, hB.ev_letE, one_mul, map_add (f := _), map_mul, hB.ev_ps, zero_mul, zero_add, map_mul,
    hB.ev_letE, one_mul, ev_aeval hB] at h1
  exact h1

theorem levRat_of [IsDiscreteValuationRing O] (W : LocWach PD LL O v n) (hR : ToolsR.RingP W)
    (hT : Formalism.MainNotions.WachCoordinates.ToolsAlg W) (hpu : ¬ IsUnit ((PD.p : ℕ) : O)) (a : ZMod n) (s : ℕ)
    (hB : LevBasics W a s) : LevRat W a s hB.F hB.ev := by
  intro g _ d _ hd c hc
  obtain ⟨rg, hgdeg, hg⟩ := levRatPf_ev W hR hT hpu a s hB g
  obtain ⟨rd, hddeg, hdv⟩ := levRatPf_ev W hR hT hpu a s hB d
  have hN : ∀ r : Polynomial O, r.degree < ((PD.p - 1) * PD.p ^ s : ℕ) →
      (r.map (algebraMap O hB.F)).natDegree < (PD.p - 1) * PD.p ^ s := by
    intro r hr
    have hNpos : 0 < (PD.p - 1) * PD.p ^ s :=
      Nat.mul_pos (by have := PD.hp.two_le; omega) (pow_pos PD.hp.pos _)
    refine lt_of_le_of_lt Polynomial.natDegree_map_le ?_
    by_cases h0 : r = 0
    · rw [h0, Polynomial.natDegree_zero]; exact hNpos
    · exact (Polynomial.natDegree_lt_iff_degree_lt h0).2 hr
  set R : Polynomial hB.F := rg.map (algebraMap O hB.F) - Polynomial.C c * rd.map (algebraMap O hB.F) with hRdef
  have hR0 : R = 0 := by
    refine poly_eq_zero hB R ?_ ?_
    · refine lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _) (max_lt (hN rg hgdeg) ?_)
      exact lt_of_le_of_lt (Polynomial.natDegree_C_mul_le _ _) (hN rd hddeg)
    · intro ζ
      rw [hRdef, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_map,
        Polynomial.eval_map, ← Polynomial.aeval_def, ← Polynomial.aeval_def, ← hg ζ, ← hdv ζ, hc ζ, sub_self]
  have hne : Nonempty (Rs hB.F PD.p s) := by
    rw [← Fintype.card_pos_iff, card_Rs hB]
    exact Nat.mul_pos (by have := PD.hp.two_le; omega) (pow_pos PD.hp.pos _)
  obtain ⟨ζ₀⟩ := hne
  have hrd : rd ≠ 0 := by
    intro h
    apply hd ζ₀
    rw [hdv ζ₀, h, map_zero]
  obtain ⟨k, hk⟩ : ∃ k, rd.coeff k ≠ 0 := by
    by_contra h
    push Not at h
    exact hrd (Polynomial.ext fun k => by simpa using h k)
  have hck : algebraMap O hB.F (rg.coeff k) = c * algebraMap O hB.F (rd.coeff k) := by
    have := congrArg (fun P : Polynomial hB.F => P.coeff k) hR0
    simp only [hRdef, Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_map,
      Polynomial.coeff_zero] at this
    exact sub_eq_zero.1 this
  have hp0 : ((PD.p : ℕ) : O) ≠ 0 := by
    intro h
    apply hB.hp
    rw [← map_natCast (algebraMap O hB.F), h, map_zero]
  obtain ⟨κ, z, hz⟩ := exists_dvd_pow_of_not_isUnit_dvr ((PD.p : ℕ) : O) hp0 hpu hk
  refine ⟨κ, z * rg.coeff k, ?_⟩
  rw [map_mul, hck, ← map_natCast (algebraMap O hB.F), ← map_pow, hz, map_mul]
  ring

end LevRatPf

end Formalism.MainNotions.UnusedSlot80.InvW
end
end

noncomputable section

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup

theorem toolsAlg_at (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F)
    (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (h : CaseA K LL) :
    Formalism.MainNotions.WachCoordinates.ToolsAlg ((HW l).W K 1 LL h.2.2) := by
  have hR : ToolsR.RingP ((HW l).W K 1 LL h.2.2) := ring_condition_uniformizer_polynomial D HW F h9 l K LL h
  have : FiniteDimensional ℚ_[l] ↥(K0 K) := ((D.loc l).PD K).finK₀
  have : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  have hp0 := Formalism.MainNotions.WachCoordinates.Br.p_ne_zero_O ((HW l).W K 1 LL h.2.2)
  have hpu := Formalism.MainNotions.WachCoordinates.Br.not_isUnit_p ((HW l).W K 1 LL h.2.2) (Formalism.MainNotions.WachCoordinates.Br.valRing_rec (D.loc l) LL)
  have : IsAdicComplete (Ideal.span {((((D.loc l).PD K).p : ℕ) : ↥(OL LL))}) ↥(OL LL) := by
    rw [(D.loc l).PD_p]
    exact Formalism.MainNotions.WachCoordinates.Br.complete_OL LL
  exact ⟨ToolsR.tools1 hR, ToolsR.tools2 hR hp0 hpu, ToolsR.tools3 hR, ToolsR.tools4 hR⟩

theorem invLevCore_fin (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F) :
    AtCaseA fun l _ K LL hG => Formalism.MainNotions.UnusedSlot80.CutU.InvLevCore ((HW l).W K 1 LL hG) := by
  refine InvW.invLevCore_L D HW F h9 fun l _ K LL h a s hB => ?_
  obtain ⟨⟨hdom, -, -⟩, -⟩ := Formalism.MainNotions.N.T2.litGoodO l LL
  haveI := hdom
  haveI : IsDiscreteValuationRing ↥(OL LL) := Formalism.BasicNotions.Examples₂.LB.OL_dvr LL
  haveI : IsAdicComplete (Ideal.span {((((D.loc l).PD K).p : ℕ) : ↥(OL LL))}) ↥(OL LL) := by
    rw [(D.loc l).PD_p]
    exact Formalism.MainNotions.WachCoordinates.Br.complete_OL LL
  haveI := Formalism.MainNotions.UnusedSlot80.neZero_finrank_max_unramified K
  exact InvW.levRat_of ((HW l).W K 1 LL h.2.2) (ring_condition_uniformizer_polynomial D HW F h9 l K LL h) (toolsAlg_at D HW F h9 l K LL h)
    (Formalism.MainNotions.WachCoordinates.Br.not_isUnit_p ((HW l).W K 1 LL h.2.2) (Formalism.MainNotions.WachCoordinates.Br.valRing_rec (D.loc l) LL)) a s hB

theorem universal_general_statement_holds (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (hAdm : AdmUnivA D HW F Cm) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F) (hH : Formalism.MainNotions.LiftingTheory.ConclusionH D HW F)
    (h15 : Formalism.MainNotions.TruncatedSeriesCountingBounds.adm15 D) : UniversalComponentCaseA D HW F Cm :=
  universal_general_of_level_inverse D HW F Cm hAdm h9 hH h15 (invLevCore_fin D HW F h9)

end Formalism.MainNotions.UnusedSlot80
