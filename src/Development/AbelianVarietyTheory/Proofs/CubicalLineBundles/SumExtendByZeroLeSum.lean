module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.CmFrameOfEq
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.ArcDatumIsArcPointBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FrMapComp
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmTensorSmoothOfRelativeDimension
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmCurveBaseChangeComp
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NonemptyPolAVGenericFibreWithLieBasis
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ModelChartLiftCoordsGeneratorIndep
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FinrankInt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SumExtendByZeroLeSum
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.MainNotions Formalism.BasicNotions
open GlobalTheory GlobalTheory.RunIn

noncomputable section

namespace GlobalTheory.WtSizes

theorem extendByZero_le_sum {p : ℕ} (f : Fin p → ℕ) (i : ℕ) : Formalism.L2.Pj.ext0 f i ≤ ∑ k, f k := by
  unfold Formalism.L2.Pj.ext0
  split_ifs with hi
  · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ (⟨i, hi⟩ : Fin p))
  · exact Nat.zero_le _

theorem sum_extendByZero_le_sum {p : ℕ} (f : Fin p → ℕ) (m : ℕ) : ∑ i : Fin m, Formalism.L2.Pj.ext0 f i ≤ ∑ k, f k := by
  have h1 : ∑ k, f k = ∑ i : Fin p, Formalism.L2.Pj.ext0 f i :=
    Finset.sum_congr rfl fun i _ => by simp [Formalism.L2.Pj.ext0, i.isLt]
  rw [h1, Fin.sum_univ_eq_sum_range (fun i => Formalism.L2.Pj.ext0 f i) m,
    Fin.sum_univ_eq_sum_range (fun i => Formalism.L2.Pj.ext0 f i) p]
  refine Finset.sum_le_sum_of_ne_zero fun i _ hi => ?_
  rw [Finset.mem_range]
  by_contra hp
  exact hi (by simp [Formalism.L2.Pj.ext0, hp])

variable {D : D7} {j : ℕ}


open Classical in
def tot (w : WeightFamilies.Wt D j) (b : D.host.E →+* ℂ) : ℕ :=
  ∑ t : D.what₂.Tau, ((if b = DV.tauEmb D t then ∑ i, w.aP t i else 0) +
    if b = conjEmb (DV.tauEmb D t) then ∑ i, w.aM t i else 0)

theorem wtA_le_tot (w : WeightFamilies.Wt D j) (b : D.host.E →+* ℂ) (i : ℕ) : wtA w (b, i) ≤ tot w b := by
  unfold wtA tot
  refine Finset.sum_le_sum fun t _ => add_le_add ?_ ?_
  · dsimp only
    split_ifs
    · exact extendByZero_le_sum _ _
    · exact le_rfl
  · dsimp only
    split_ifs
    · exact extendByZero_le_sum _ _
    · exact le_rfl

theorem sum_wtA_le_tot (w : WeightFamilies.Wt D j) (b : D.host.E →+* ℂ) (m : ℕ) :
    ∑ i : Fin m, wtA w (b, i) ≤ tot w b := by
  unfold wtA tot
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun t _ => ?_
  rw [Finset.sum_add_distrib]
  refine add_le_add ?_ ?_
  · dsimp only
    split_ifs
    · exact sum_extendByZero_le_sum _ _
    · simp
  · dsimp only
    split_ifs
    · exact sum_extendByZero_le_sum _ _
    · simp

theorem sum_tot (w : WeightFamilies.Wt D j) :
    ∑ b, tot w b = ∑ t, ((∑ i, w.aP t i) + ∑ i, w.aM t i) := by
  classical
  unfold tot
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp

theorem tot_le_size (w : WeightFamilies.Wt D j) :
    ((∑ b, tot w b : ℕ) : ℝ) + ((D.R.f * D.R.r : ℕ) : ℝ) * w.n ≤ w.size := by
  rw [sum_tot]
  unfold WeightFamilies.Wt.size
  push_cast
  have h1 : (1 : ℝ) ≤ max ((D.R.sigW j).2 : ℝ) 1 := le_max_right _ _
  have h2 : (0 : ℝ) ≤ (D.R.f : ℝ) * D.R.r * w.n := by positivity
  nlinarith [mul_le_mul_of_nonneg_right h1 h2]

theorem spread_le {r : ℕ} (hr : 0 < r) (x : Fin r → ℝ) (A B : ℝ) (h1 : ∀ i, x i ≤ A) (h2 : ∀ i, -B ≤ x i) :
    (⨆ i, x i) - ⨅ i, x i ≤ A + B := by
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  have := ciSup_le h1
  have := le_ciInf h2
  linarith

theorem invFun_relab (T : Core D) (τ : D.host.E →+* ℂ) : Function.invFun (relab T.Q.c T.σ₀) τ = τ := by
  have h : ∀ τ : D.host.E →+* ℂ, relab T.Q.c T.σ₀ τ = τ := fun τ => RingHom.ext fun _ => rfl
  have h2 : relab T.Q.c T.σ₀ (Function.invFun (relab T.Q.c T.σ₀) τ) = τ := Function.invFun_eq ⟨τ, h τ⟩
  rwa [h] at h2

theorem spread_laU_le (T : Core D) (hr : 0 < D.R.r) (w : WeightFamilies.Wt D j) (k : (T.U j T.σ₀).Comp)
    (τ : ((T.U j T.σ₀).X k).Ψ) :
    ((T.U j T.σ₀).X k).spread (laU (T.U j T.σ₀) (wtA w) w.n k) τ ≤
      (tot w τ.1 : ℝ) + tot w (conjEmb τ.1) + w.n := by
  have hn : ((w.n / 2 : ℕ) : ℝ) + ((w.n / 2 : ℕ) : ℝ) ≤ w.n := by
    have : w.n / 2 + w.n / 2 ≤ w.n := by omega
    exact_mod_cast this
  have key : ∀ i, -((tot w (conjEmb τ.1) : ℤ) + ((w.n / 2 : ℕ) : ℤ)) ≤ laU (T.U j T.σ₀) (wtA w) w.n k τ i ∧
      laU (T.U j T.σ₀) (wtA w) w.n k τ i ≤ (tot w τ.1 : ℤ) + ((w.n / 2 : ℕ) : ℤ) := by
    intro i
    unfold laU
    rw [invFun_relab, invFun_relab]
    have a1 := wtA_le_tot w τ.1 ((i : ℕ) - ((T.U j T.σ₀).X k).p0)
    have a2 := wtA_le_tot w (conjEmb τ.1) (((T.U j T.σ₀).X k).p0 - 1 - (i : ℕ))
    split_ifs <;> constructor <;> omega
  refine (spread_le hr _ ((tot w τ.1 : ℝ) + ((w.n / 2 : ℕ) : ℝ))
    ((tot w (conjEmb τ.1) : ℝ) + ((w.n / 2 : ℕ) : ℝ)) (fun i => ?_) (fun i => ?_)).trans (by linarith)
  · have h1 := (Int.cast_le (R := ℝ)).2 (key i).2
    rwa [Int.cast_add, Int.cast_natCast, Int.cast_natCast] at h1
  · exact_mod_cast (key i).1

theorem sum_cm_le {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (B : (E →+* ℂ) → ℕ) : ∑ τ : X.Ψ, (B τ.1 + B (conjEmb τ.1)) ≤ ∑ b, B b := by
  classical
  have hcc : ∀ τ : E →+* ℂ, conjEmb (conjEmb τ) = τ := fun τ => RingHom.ext fun x => by simp [conjEmb]
  have hinj : Function.Injective (conjEmb : (E →+* ℂ) → (E →+* ℂ)) := Function.LeftInverse.injective hcc
  rw [Finset.sum_add_distrib, Finset.sum_coe_sort X.Ψ B, Finset.sum_coe_sort X.Ψ (fun τ => B (conjEmb τ)),
    ← Finset.sum_image (f := B) (g := conjEmb) (s := X.Ψ) hinj.injOn, ← Finset.sum_add_sum_compl X.Ψ B]
  refine Nat.add_le_add_left (Finset.sum_le_sum_of_subset fun b hb => ?_) _
  obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.1 hb
  rw [Finset.mem_compl]
  exact (X.cmType τ).1 hτ

theorem fdeg_eq (D : D7) : fdeg D.host.E = D.R.f := by
  unfold fdeg
  rw [hostSize_finrank]
  omega

theorem one_le_dE (D : D7) : 1 ≤ dE D.host.E := by
  unfold dE
  have h : (1 : ℤ) ≤ |NumberField.discr D.host.E| := Int.one_le_abs (NumberField.discr_ne_zero _)
  exact_mod_cast h

theorem sqrt_le_dE (D : D7) : Real.sqrt D.host.d ≤ dE D.host.E := by
  have h1 : Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ D.host.rdE :=
    (UpperTheory.KR.log_qd_le_rd D.host.toHostAx D.host.flPS).2.2.1
  have hq : (1 : ℝ) ≤ D.host.q := by exact_mod_cast D.host.hyp.1.one_lt.le
  have h2 : Real.sqrt D.host.d ≤ Real.sqrt ((D.host.q : ℝ) * D.host.d) :=
    Real.sqrt_le_sqrt (le_mul_of_one_le_left (Nat.cast_nonneg _) hq)
  have h4 : D.host.rdE ≤ dE D.host.E := by
    have h5 : (1 : ℝ) ≤ (Module.finrank ℚ D.host.E : ℝ) := by
      have : 0 < Module.finrank ℚ D.host.E := Module.finrank_pos
      exact_mod_cast this
    exact Real.rpow_le_self_of_one_le (one_le_dE D) ((div_le_one (by linarith)).2 h5)
  linarith

theorem sizes : ∀ (D : D7) (T : Core D) (h : LawsCore T) (j : ℕ), InR D j → ∀ w : WeightFamilies.Wt D j, 0 < D.R.r ∧ (T.Q.Dw j).p + (T.Q.Dw j).q = D.R.r ∧ fdeg D.host.E = D.R.f ∧ Real.sqrt D.host.d ≤ dE D.host.E ∧ 1 ≤ dE D.host.E ∧ Real.log (dE D.host.E) = logdE D ∧ (∀ k, (∑ τ, ((T.U j T.σ₀).X k).spread (laU (T.U j T.σ₀) (wtA w) w.n k) τ) ≤ w.size) ∧ ((∑ b : D.host.E →+* ℂ, ∑ i : Fin ((T.Q.Dw j).mult b), wtA w (b, i) : ℕ) : ℝ) + ((D.R.f * D.R.r : ℕ) : ℝ) * w.n ≤ w.size := by
  intro D T h j hj w
  have hr : 0 < D.R.r := by
    have := D.R.m_add_three_le_k
    unfold Ranks.r
    omega
  have hts := tot_le_size w
  refine ⟨hr, (h.unf j hj T.σ₀ T.good_σ₀).1.symm, fdeg_eq D, sqrt_le_dE D, one_le_dE D, rfl, fun k => ?_, ?_⟩
  · refine (Finset.sum_le_sum fun τ _ => spread_laU_le T hr w k τ).trans (le_trans ?_ hts)
    rw [Finset.sum_add_distrib]
    refine add_le_add ?_ ?_
    · exact_mod_cast sum_cm_le ((T.U j T.σ₀).X k) (tot w)
    · rw [Finset.sum_const, Finset.card_univ, QuadraticCoefficientForms.card_Psi (X := (T.U j T.σ₀).X k), fdeg_eq, nsmul_eq_mul]
      refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
      exact_mod_cast Nat.le_mul_of_pos_right _ hr
  · refine le_trans (add_le_add ?_ le_rfl) hts
    exact_mod_cast Finset.sum_le_sum fun b _ => sum_wtA_le_tot w b _

end GlobalTheory.WtSizes
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCompleteDVRCompletionIntegralIff
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCompleteDVRCompletionIntegralIff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

private lemma mem_range_algebraMap_iff_valV_le_one (T : CDVR) (x : T.Fr) :
    x ∈ Set.range (algebraMap T.V T.Fr) ↔ valV T.V x ≤ 1 := by
  unfold valV
  constructor
  · rintro ⟨r, rfl⟩
    exact (IsDiscreteValuationRing.maximalIdeal T.V).valuation_le_one r
  · intro h
    obtain ⟨a, ha⟩ := IsDiscreteValuationRing.exists_lift_of_le_one h
    exact ⟨a, ha⟩

private lemma withZero_le_one_iff_log_nonpos {x : WithZero (Multiplicative ℤ)} (hx : x ≠ 0) : x ≤ 1 ↔ WithZero.log x ≤ 0 := by
  conv_lhs => rw [← WithZero.exp_log hx, ← WithZero.exp_zero]
  exact WithZero.exp_le_exp

theorem exists_cdvr_completion_integral_iff :
    ∀ (K : Type) [Field K] [NumberField K] (p : HeightOneSpectrum (𝓞 K)),
      ∃ (T : CDVR) (iK : K →+* T.Fr), T.FinRes ∧
        ∀ y : K, iK y ∈ Set.range (algebraMap T.V T.Fr) ↔ p.valuation K y ≤ 1 := by
  intro K _ _ p

  obtain ⟨T, k, e, hO, hfin⟩ := locFld K K (RingHom.id K) p
  unfold OverLa vV vLa at hO
  obtain ⟨he, hv⟩ := hO
  simp only [RingHom.comp_id] at hv
  refine ⟨T, k, hfin, fun y => ?_⟩
  by_cases hy : y = 0
  · subst hy
    rw [map_zero, map_zero]
    exact ⟨fun _ => zero_le, fun _ => ⟨0, map_zero _⟩⟩
  · have hky : k y ≠ 0 := (map_ne_zero k).2 hy
    have ha : valV T.V (k y) ≠ 0 := by
      unfold valV
      exact (Valuation.ne_zero_iff _).2 hky
    have hb : p.valuation K y ≠ 0 := (Valuation.ne_zero_iff _).2 hy

    rw [mem_range_algebraMap_iff_valV_le_one, withZero_le_one_iff_log_nonpos ha, withZero_le_one_iff_log_nonpos hb]
    have h := hv y
    have he' : (0 : ℤ) < e := by exact_mod_cast he
    constructor <;> intro h' <;> nlinarith

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCompleteDVRCompletionIntegralIffStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_completeDVR_completion_integral_iff : ∀ (K : Type) [Field K] [NumberField K] (p : HeightOneSpectrum (𝓞 K)), ∃ (T : CDVR) (iK : K →+* T.Fr), T.FinRes ∧ ∀ y : K, iK y ∈ Set.range (algebraMap T.V T.Fr) ↔ p.valuation K y ≤ 1 := by
  first | exact @GlobalTheory.exists_cdvr_completion_integral_iff | exact GlobalTheory.exists_cdvr_completion_integral_iff | (intros; apply GlobalTheory.exists_cdvr_completion_integral_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsProdPolAV
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsProdPolAV
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.PolProd

open GlobalTheory.CechPic GlobalTheory.TripleProd

variable {S : Scheme.{0}}

theorem locZero_add {Y B : Scheme.{0}} {π : Y ⟶ B} {c d : Pic Y} (H : LocZero π c) (H' : LocZero π d) :
    LocZero π (c + d) := by
  have h := H.sub ((locZero_base π 0).sub H')
  rwa [map_zero, zero_sub, sub_neg_eq_add] at h

theorem rigidified_iff (A : Over S) [GrpObj A] {L : LB A.left} (hL : L.IsLB) :
    Out.Rigidified A L ↔ pull (eSec A) (cls L hL) = 0 := by
  exact (cls_eq_zero_iff (pull_isLB hL _)).symm

theorem sym_iff (A : Over S) [GrpObj A] {L : LB A.left} (hL : L.IsLB) :
    Out.Sym A L ↔ LocZero A.hom (pull (GrpObj.inv : A ⟶ A).left (cls L hL) - cls L hL) := by
  refine forall_congr' fun _ => exists_congr fun U => and_congr_right fun _ => ?_
  refine (cls_eq_zero_iff (LB.isLB_linComb hL _ _)).symm.trans ?_
  have e : cls (LB.LinComb L (K := Fin 2)
        ![(A.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : A ⟶ A).left, (A.hom ⁻¹ᵁ U).ι] ![1, -1]) (LB.isLB_linComb hL _ _) =
      pull (A.hom ⁻¹ᵁ U).ι (pull (GrpObj.inv : A ⟶ A).left (cls L hL) - cls L hL) := by
    refine (cls_linComb hL _ _ _).trans ?_
    rw [Fin.sum_univ_two]
    show (1 : ℤ) • pull ((A.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : A ⟶ A).left) (cls L hL) +
      (-1 : ℤ) • pull (A.hom ⁻¹ᵁ U).ι (cls L hL) = _
    rw [one_zsmul, neg_one_zsmul, map_sub, sub_eq_add_neg, pull_comp]
  rw [e]

theorem eSec_comp {A G : Over S} [GrpObj A] [GrpObj G] (f : A ⟶ G) [IsMonHom f] :
    eSec A ≫ f.left = eSec G := by
  have h : η[A] ≫ f = η[G] := IsMonHom.one_hom f
  exact congrArg (fun z => z.left) h

theorem inv_comp_left {A G : Over S} [GrpObj A] [GrpObj G] (f : A ⟶ G) [IsMonHom f] :
    (GrpObj.inv : A ⟶ A).left ≫ f.left = f.left ≫ (GrpObj.inv : G ⟶ G).left := by
  have h : (GrpObj.inv : A ⟶ A) ≫ f = f ≫ GrpObj.inv := GrpObj.inv_hom f
  exact congrArg (fun z => z.left) h

theorem exists_prod_polAV : Out.Laws → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (P P' : Out.PolAV (Sp R)), ∃ (Q : Out.PolAV (Sp R)) (p : Q.A ⟶ P.A) (q : Q.A ⟶ P'.A), IsMonHom p ∧ IsMonHom q ∧ IsIso (lift p q) ∧ Q.g = P.g + P'.g := by
  intro _ R _ _ P P'
  have hB : IsAbelianScheme (P.A ⊗ P'.A) := AbelianSchemeGerms.isAbelianScheme_tensor _ _ P.isAb P'.isAb
  let p := fst P.A P'.A
  let q := snd P.A P'.A
  obtain ⟨M, hM, eM⟩ := cls_surj (pull p.left (cls P.L P.isLB) + pull q.left (cls P'.L P'.isLB))
  have hd := LB.isLB_div hM (pull_isLB P.isLB p.left)
  have last : LBIso (M.div (P.L.pull p.left)) (P'.L.pull q.left) := by
    refine (cls_eq_iff hd (pull_isLB P'.isLB _)).1 ?_
    rw [cls_div hM (pull_isLB P.isLB p.left), eM, cls_pull P.isLB, cls_pull P'.isLB, add_sub_cancel_left]
  haveI := P.isAb.proper
  haveI := P'.isAb.proper
  haveI := hB.proper
  have hdim : SmoothOfRelativeDimension (P.g + P'.g) (P.A ⊗ P'.A).hom := by
    haveI := P.smoothDim
    haveI : SmoothOfRelativeDimension P'.g (pullback.fst P.A.hom P'.A.hom) :=
      (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
        (IsPullback.of_hasPullback _ _).flip P'.smoothDim
    rw [add_comm]
    exact inferInstanceAs (SmoothOfRelativeDimension (P'.g + P.g) (pullback.fst P.A.hom P'.A.hom ≫ P.A.hom))
  have hrig : Out.Rigidified (P.A ⊗ P'.A) M := by
    rw [rigidified_iff _ hM, eM, map_add (f := _), ← pull_comp, ← pull_comp, eSec_comp p, eSec_comp q,
      (rigidified_iff _ P.isLB).1 P.rigid, (rigidified_iff _ P'.isLB).1 P'.rigid, add_zero]
  have hsym : Out.Sym (P.A ⊗ P'.A) M := by
    have h₁ := ((sym_iff _ P.isLB).1 P.sym).pull_over (π' := (P.A ⊗ P'.A).hom) p.left (Over.w p)
    have h₂ := ((sym_iff _ P'.isLB).1 P'.sym).pull_over (π' := (P.A ⊗ P'.A).hom) q.left (Over.w q)
    rw [sym_iff _ hM, eM]
    convert locZero_add h₁ h₂ using 1
    rw [map_add (f := _), map_sub, map_sub, ← pull_comp, ← pull_comp, ← pull_comp, ← pull_comp, inv_comp_left p,
      inv_comp_left q]
    abel
  have hamp : Out.RelAmple (P.A ⊗ P'.A) M :=
    (relAmple_iff_isAmpleLB_of_isAffine _ hM).2 (IsAmpleLB.box
      ((relAmple_iff_isAmpleLB_of_isAffine _ P.isLB).1 P.ample) ((relAmple_iff_isAmpleLB_of_isAffine _ P'.isLB).1 P'.ample)
      hM (p := p.left) (q := q.left) (f := P.A.hom) (g := P'.A.hom) (IsPullback.of_hasPullback _ _) last.symm)
  refine ⟨⟨P.A ⊗ P'.A, hB, P.g + P'.g, hdim, M, hM, hrig, hsym, hamp,
    kTriv_prod hM P.isLB P'.isLB eM P.ktriv P'.ktriv⟩, p, q, inferInstance, inferInstance, ?_, rfl⟩
  show IsIso (lift (fst P.A P'.A) (snd P.A P'.A))
  rw [lift_fst_snd]
  infer_instance

end GlobalTheory.PolProd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsProdPolAVStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_prod_polAV_add_g : Out.Laws → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (P P' : Out.PolAV (Sp R)), ∃ (Q : Out.PolAV (Sp R)) (p : Q.A ⟶ P.A) (q : Q.A ⟶ P'.A), IsMonHom p ∧ IsMonHom q ∧ IsIso (lift p q) ∧ Q.g = P.g + P'.g := by
  first | exact @GlobalTheory.PolProd.exists_prod_polAV | exact GlobalTheory.PolProd.exists_prod_polAV | (intros; apply GlobalTheory.PolProd.exists_prod_polAV <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EqZeroOfPow
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

noncomputable section

namespace GlobalTheory.LamF.Ind

open GlobalTheory.SqZero GlobalTheory.LieComb

section General

variable {R : Type} [CommRing R] {S : Scheme.{0}} (f : Sp R ⟶ S)

def scaleOver (c : R) : Over.mk ((epsR R).hom ≫ f) ⟶ Over.mk ((epsR R).hom ≫ f) :=
  (Over.map f).map (Chart.spMap (epsTo R (TrivSqZeroExt.inr c : DualNumber R)
    (TrivSqZeroExt.inr_mul_inr _ _ _)) : epsR R ⟶ epsR R)

variable {f} {G : Over S} {G' : Over (Sp R)} [GrpObj G] [GrpObj G'] [IsCommMonObj G]
  [IsCommMonObj G'] {φ : G'.left ⟶ G.left}

theorem push_tanExp (Φ : (epsR R ⟶ G') ≃* (Over.mk ((epsR R).hom ≫ f) ⟶ G))
    (hΦ : ∀ x, (Φ x).left = x.left ≫ φ) {n : ℕ} (v : Fin n → (epsR R ⟶ G')) (c : Fin n → R) :
    Φ (tanExp v c) = ∏ i, scaleOver f (c i) ≫ Φ (v i) := by
  refine (map_prod Φ _ _).trans (Finset.prod_congr rfl fun i _ => ?_)
  apply Over.OverMorphism.ext
  rw [hΦ, Over.comp_left, Over.comp_left, hΦ, Category.assoc]
  rfl

theorem prod_comp {T G₁ : Over S} [GrpObj G₁] [IsCommMonObj G₁] (F : G ⟶ G₁) [IsMonHom F]
    {J : Type} (s : Finset J) (x : J → (T ⟶ G)) : (∏ i ∈ s, x i) ≫ F = ∏ i ∈ s, x i ≫ F :=
  map_prod (MonoidHom.mk' (fun y : T ⟶ G => y ≫ F) fun a b => MonObj.mul_comp a b F) x s


omit [GrpObj G] [IsCommMonObj G] in
theorem eq_zero_of_pow {K : Type} [Field K] [CharZero K] {A : Over (Sp K)} [GrpObj A]
    [IsCommMonObj A] {n : ℕ} {v : Fin n → (epsR K ⟶ A)} (hv : IsLieBasis v) {c : Fin n → K}
    {N : ℕ} (hN : 0 < N) (h : tanExp v c ^ N = 1) : c = 0 := by
  have h₁ : tanExp v (N • c) = tanExp v 0 := by
    change (combHom hv.1 (N • c)).toMul = (combHom hv.1 0).toMul
    rw [map_nsmul, map_zero, toMul_nsmul]
    exact h
  have h₂ := (isLieBasisOver_self hv).1 _ _ h₁
  funext i
  have := congrFun h₂ i
  simpa [hN.ne'] using this

end General

theorem lamInd : LamIndSt := by
  intro E _ _ _ _ H l cf _ nΨ n' f o La hg L hL hdet
  obtain ⟨-, -, -, hB, hΨ, h', -, -, -, -, -, -, -, ⟨hmΨ, hm', N, ψΨ, ψ', hN, -, hsum⟩, -⟩ := hg
  obtain ⟨hsrc, -, hw, -⟩ := hL
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hdet
  choose w hw hwc using hw
  obtain ⟨ΦB, hΦB⟩ := exists_mulEquiv_points_of_isGrpPullback _ _ _ _ _ _ hB.1 (epsR o.K₁)
  obtain ⟨ΦΨ, hΦΨ⟩ := exists_mulEquiv_points_of_isGrpPullback _ _ _ _ _ _ hΨ.1 (epsR o.K₁)
  obtain ⟨Φ', hΦ'⟩ := exists_mulEquiv_points_of_isGrpPullback _ _ _ _ _ _ h'.1 (epsR o.K₁)
  let e := Equiv.ofBijective _ hsrc
  have he : ∀ q, L.src (e.symm q) = q := fun q => e.apply_symm_apply q
  have hwl : ∀ j i, ΦB (w (e.symm (.inl (j, i)))) = ΦΨ (o.xΨ.v i) ≫ o.φΨ j := fun j i => by
    have := hw (e.symm (.inl (j, i)))
    rw [LamLetters.IsLetter, he] at this
    apply Over.OverMorphism.ext
    rw [hΦB, Over.comp_left, hΦΨ, Category.assoc]
    exact this
  have hwr : ∀ j i, ΦB (w (e.symm (.inr (j, i)))) = Φ' (o.x'.v i) ≫ o.φ' j := fun j i => by
    have := hw (e.symm (.inr (j, i)))
    rw [LamLetters.IsLetter, he] at this
    apply Over.OverMorphism.ext
    rw [hΦB, Over.comp_left, hΦ', Category.assoc]
    exact this
  have hone : tanExp w c = 1 := by
    obtain rfl : w = fun k => tanExp o.xB.v (L.U k) :=
      funext fun k => (isLieComb_iff_tanExp _ _).1 (hwc k)
    refine (tanExp_tanExp o.xB.basis.1 (fun k => L.U k) c).trans ?_
    rw [← Matrix.vecMul_eq_sum, hc]
    exact lieExp_eq_one o.xB.basis.1 _ (fun _ => rfl) _
  have hpad : ∀ a b : Over.mk ((epsR o.K₁).hom ≫ gmap o.K₁) ⟶ o.B.A,
      padd _ a b = a * b := fun _ _ => rfl
  have hps : ∀ (n : ℕ) (f : Fin n → (Over.mk ((epsR o.K₁).hom ≫ gmap o.K₁) ⟶ o.B.A)),
      psumPt f = (List.ofFn f).prod := by
    intro n f
    rw [List.prod_eq_foldr]
    rfl
  have hpow : ∀ (G : Over (Sp (𝓞 o.K₁))) [GrpObj G] (n : ℕ)
      (a : Over.mk ((epsR o.K₁).hom ≫ gmap o.K₁) ⟶ G), pnsmulPt n a = a ^ n := by
    intro G _ n a
    induction n with
    | zero => rw [pow_zero]; rfl
    | succ n ih => rw [pow_succ, ← ih]; rfl
  let a := fun j => ΦΨ (tanExp o.xΨ.v fun i => c (e.symm (.inl (j, i))))
  let a' := fun j => Φ' (tanExp o.x'.v fun i => c (e.symm (.inr (j, i))))
  have hs : padd o.B.A (psumPt fun k => a k ≫ o.φΨ k) (psumPt fun k => a' k ≫ o.φ' k) = 1 := by
    rw [hpad, hps, hps, List.prod_ofFn, List.prod_ofFn, ← map_one ΦB, ← hone,
      push_tanExp ΦB hΦB, ← e.symm.prod_comp, Fintype.prod_sum_type, Fintype.prod_prod_type,
      Fintype.prod_prod_type]
    congr 1 <;> refine Finset.prod_congr rfl fun j _ => ?_
    · have := hmΨ j
      simp only [a, push_tanExp ΦΨ hΦΨ, prod_comp, hwl, Category.assoc]
    · have := hm' j
      simp only [a', push_tanExp Φ' hΦ', prod_comp, hwr, Category.assoc]
  have hs₀ : padd o.B.A
      (psumPt fun k => (1 : Over.mk ((epsR o.K₁).hom ≫ gmap o.K₁) ⟶ _) ≫ o.φΨ k)
      (psumPt fun k => (1 : Over.mk ((epsR o.K₁).hom ≫ gmap o.K₁) ⟶ _) ≫ o.φ' k) = 1 := by
    rw [hpad, hps, hps, List.prod_ofFn, List.prod_ofFn, Finset.prod_eq_one, Finset.prod_eq_one,
      _root_.mul_one]
    · intro j _
      have := hm' j
      exact MonObj.one_comp _
    · intro j _
      have := hmΨ j
      exact MonObj.one_comp _
  obtain ⟨p₁, p₂⟩ := hsum _ a a'
  obtain ⟨q₁, q₂⟩ := hsum _ (fun _ => 1) (fun _ => 1)
  rw [hs] at p₁ p₂
  rw [hs₀] at q₁ q₂
  apply hc0
  funext k
  obtain ⟨q, rfl⟩ := e.symm.surjective k
  rcases q with ⟨j, i⟩ | ⟨j, i⟩
  · have h := (p₁ j).symm.trans (q₁ j)
    rw [hpow _, hpow _, one_pow,
      ← map_pow, map_eq_one_iff _ ΦΨ.injective] at h
    exact congrFun (eq_zero_of_pow o.xΨ.basis hN h) i
  · have h := (p₂ j).symm.trans (q₂ j)
    rw [hpow _, hpow _, one_pow,
      ← map_pow, map_eq_one_iff _ Φ'.injective] at h
    exact congrFun (eq_zero_of_pow o.x'.basis hN h) i

end GlobalTheory.LamF.Ind
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SecTieBaseChange
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT.TieCalc

theorem isoMaps_iff {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F))
    (σ : LB.Sec L') (s : LB.Sec (L.pull F)) :
    IsoMaps w σ s ↔ ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (j : L.ι) (k : L'.ι), F (r z) ∈ L.U j → r z ∈ L'.U k →
      gs r z _ (s.f (fun _ => j)) = (gw w r z j k).val * gs r z _ (σ.f k) := by
  constructor
  · intro h Z r z j k hj hk
    have hz : r z ∈ (L.pull F).U (fun _ => j) ⊓ L'.U k := ⟨mem_pull.2 hj, hk⟩
    have a := congrArg (gs r z _) (h (fun _ => j) k)
    exact (gs_res _ z _ hz _).symm.trans (a.trans ((gs_mul _ z _ hz _ _).trans
        (congrArg₂ (· * ·) (gs_unit _ z _ hz _) (gs_res _ z _ hz _))))
  · intro h (i : PUnit → L.ι) k
    exact fn_ext fun p hp =>
      (gs_res _ p _ hp _).trans ((h _ (𝟙 _) p (i PUnit.unit) k (mem_pull.1 hp.1) hp.2).trans
        (Eq.symm ((gs_mul _ p _ hp _ _).trans (congrArg₂ (· * ·) (gs_unit (𝟙 _) p _ hp _) (gs_res _ p _ hp _)))))

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {t : SAB H (Sp S)} (m : SABMap t Xo.univ.t x)

theorem exists_canon : ∃ g : t.G.left ⟶ Gx x, g ≫ (snd (Over.mk x) Xo.univ.t.G).left = m.φ ∧
    g ≫ (fst (Over.mk x) Xo.univ.t.G).left = t.G.hom := by
  let a₀ : Over.mk (t.G.hom ≫ x) ⟶ Over.mk x := Over.homMk t.G.hom rfl
  let b₀ : Over.mk (t.G.hom ≫ x) ⟶ Xo.univ.t.G := Over.homMk m.φ m.cart.1.w
  exact ⟨(lift a₀ b₀).left, congrArg (fun q => q.left) (lift_snd a₀ b₀), congrArg (fun q => q.left) (lift_fst a₀ b₀)⟩

theorem canon_mem {g : t.G.left ⟶ Gx x} (hg : g ≫ (snd (Over.mk x) Xo.univ.t.G).left = m.φ)
    (j : Xo.univ.t.PP.L.ι) (y : t.G.left) (hy : m.φ y ∈ Xo.univ.t.PP.L.U j) : g y ∈ (PPx x).U (fun _ => j) :=
  Set.mem_iInter.2 fun _ => (congrArg (fun q => q y ∈ Xo.univ.t.PP.L.U j) hg).mpr hy

theorem rigIso_unique {w w' : LB.Iso t.PP.L (Xo.univ.t.PP.L.pull m.φ)} (h : RigIso m w) (h' : RigIso m w') :
    w = w' := by
  have hp : IsProper t.G.hom := MorphismProperty.of_isPullback (P := @IsProper) m.cart.1 Xo.univ.proper
  have hab : IsAbelianScheme t.G := ⟨t.semi.comm, t.semi.smooth, hp, t.semi.geomConnected⟩
  exact GlobalTheory.iso_eq_of_maps_along_section (S := Sp S) (exists_chart t.PP.isLB)
    (fun y => (exists_chart Xo.univ.t.PP.isLB (m.φ y)).elim fun j hj => ⟨fun _ => j, mem_pull.2 hj⟩)
    t.G.hom (eSec t.G) (Over.w η[t.G]) (GlobalTheory.globalFns_holds _ _ hab).2 h.1 h'.1 h.2 h'.2

theorem secTie_iff {w : LB.Iso t.PP.L (Xo.univ.t.PP.L.pull m.φ)} (hw : RigIso m w) {g : t.G.left ⟶ Gx x}
    (hs : g ≫ (snd (Over.mk x) Xo.univ.t.G).left = m.φ) (hf : g ≫ (fst (Over.mk x) Xo.univ.t.G).left = t.G.hom)
    (th : LB.Sec t.PP.L) (s : LB.Sec (PPx x)) :
    SecTie m th s ↔ ∀ (Z : Scheme.{0}) (r : Z ⟶ t.G.left) (z : Z) (j : Xo.univ.t.PP.L.ι) (k : t.PP.L.ι),
      m.φ (r z) ∈ Xo.univ.t.PP.L.U j → r z ∈ t.PP.L.U k →
      gs (r ≫ g) z ((PPx x).U (fun _ => j)) (s.f (fun _ => j)) = (gw w r z j k).val * gs r z _ (th.f k) := by
  constructor
  · rintro ⟨w', s1, r1, i1, c⟩ Z r z j k hj hk
    obtain rfl : w' = w := rigIso_unique m r1 hw
    have le : (Xo.univ.t.PP.L.pull m.φ).U (fun _ => j) ≤ g ⁻¹ᵁ (PPx x).U (fun _ => j) :=
      fun q hq => canon_mem m hs j q (mem_pull.1 hq)
    refine Eq.trans ?_ ((isoMaps_iff w' th s1).1 i1 Z r z j k hj hk)
    rw [c g hs hf (fun _ => j) le]
    exact (gs_appLE g _ _ le r z (mem_pull.2 hj) _).symm
  · intro a
    obtain ⟨s1, hs1⟩ := thf_secUp ((isGen_iff w).1 hw.1) Xo.univ.t.PP.isLB t.PP.isLB th
    refine ⟨w, s1, hw, (isoMaps_iff w th s1).2 fun Z r z j k hj hk => hs1 Z r z (fun _ => j) k (mem_pull.2 hj) hk, ?_⟩
    intro g' e₁ e₂ (J : PUnit → Xo.univ.t.PP.L.ι) hJ
    obtain rfl : g' = g := SecCalc.pm_ext _ _ (e₁.trans hs.symm) (e₂.trans hf.symm)
    refine fn_ext fun p hp => ?_
    obtain ⟨k, hk⟩ := exists_chart t.PP.isLB p
    rw [hs1 _ (𝟙 _) p J k hp hk, gs_appLE _ _ _ hJ (𝟙 _) p hp, a _ (𝟙 _) p _ k (mem_pull.1 hp) hk]

theorem secTie_scale {th th' : LB.Sec t.PP.L} {s s' : LB.Sec (PPx x)} (h : SecTie m th s) (a : S)
    (hs' : ∀ i, s'.f i = scal x a i * s.f i) :
    SecTie m th' s' ↔ ∀ i, th'.f i = constFn t.G.hom _ a * th.f i := by
  obtain ⟨g, hs, hf⟩ := exists_canon m
  obtain ⟨w, -, hw, -⟩ := id h
  rw [secTie_iff m hw hs hf] at h ⊢
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ t.G.left) (z : Z) (j : Xo.univ.t.PP.L.ι) (k : t.PP.L.ι),
      m.φ (r z) ∈ Xo.univ.t.PP.L.U j → r z ∈ t.PP.L.U k →
      gs (r ≫ g) z ((PPx x).U (fun _ => j)) (s'.f (fun _ => j)) =
        (gw w r z j k).val * gs r z _ (constFn t.G.hom _ a * th.f k) := by
    intro Z r z j k hj hk
    have a₁ : (r ≫ g) z ∈ (PPx x).U (fun _ => j) := canon_mem m hs j _ hj
    rw [gs_mul _ z _ hk, gs_constFn _ _ _ z hk, mul_left_comm]
    refine (congrArg (gs _ z _) (hs' _)).trans ((gs_mul _ z _ a₁ _ _).trans (congrArg₂ (· * ·) ?_ (h Z r z j k hj hk)))
    exact (gs_constFn (fst (Over.mk x) Xo.univ.t.G).left _ _ z a₁ a).trans (by rw [Category.assoc, hf])
  constructor
  · intro h' k
    refine fn_ext fun y hy => ?_
    obtain ⟨j, hj⟩ := exists_chart Xo.univ.t.PP.isLB (m.φ y)
    exact (Units.mul_right_inj _).1 ((h' _ (𝟙 _) y j k hj hy).symm.trans (key _ (𝟙 _) y j k hj hy))
  · intro h' Z r z j k hj hk
    rw [h' k]
    exact key Z r z j k hj hk

theorem secTie_baseChange {th : LB.Sec t.PP.L} {s : LB.Sec (PPx x)} (h : SecTie m th s) {S' : Type} [CommRing S']
    (φ : S →+* S') {x' : Sp S' ⟶ Xo.X} {t'' : SAB H (Sp S')} (m' : SABMap t'' Xo.univ.t x')
    (n : SABMap t'' t (spMap φ)) (s' : LB.Sec (PPx x')) (w : LB.Iso t''.PP.L (t.PP.L.pull n.φ))
    (θ : LB.Sec (t.PP.L.pull n.φ)) (th' : LB.Sec t''.PP.L) (hx : x' = spMap φ ≫ x) (hφ : m'.φ = n.φ ≫ m.φ)
    (hb : SecBC φ 1 x x' s s') (hw : RigIso n w) (hθ : PullSec n.φ th θ) :
    SecTie m' th' s' ↔ IsoMaps w th' θ := by
  obtain ⟨g, hs, hf⟩ := exists_canon m
  obtain ⟨g', hs', hf'⟩ := exists_canon m'
  obtain ⟨w₁, -, hw₁, -⟩ := id h
  obtain ⟨w₂, hw₂, T⟩ := GlobalTheory.LiftBaseChange.rigIso_comp m n m' hx hφ hw₁ hw
  obtain ⟨pm, ps, pf, hp⟩ := hb
  have eg : g' ≫ pm = n.φ ≫ g := by
    apply SecCalc.pm_ext
    · rw [Category.assoc, ps, hs', Category.assoc, hs, hφ]
    · rw [Category.assoc, pf, ← Category.assoc, hf', Category.assoc, hf]
      exact n.cart.1.w.symm
  have ept : ∀ y, m'.φ y = m.φ (n.φ y) := fun y => by rw [hφ]; rfl
  rw [secTie_iff m hw₁ hs hf] at h
  rw [secTie_iff m' hw₂ hs' hf', isoMaps_iff]
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ t''.G.left) (z : Z) (j : Xo.univ.t.PP.L.ι) (i : t.PP.L.ι),
      m.φ (n.φ (r z)) ∈ Xo.univ.t.PP.L.U j → n.φ (r z) ∈ t.PP.L.U i →
      gs (r ≫ g') z ((PPx x').U (fun _ => j)) (s'.f (fun _ => j)) =
        (gw w₁ (r ≫ n.φ) z j i).val * gs r z _ (θ.f (fun _ => i)) := by
    intro Z r z j i hj hi
    have a₁ : (r ≫ g') z ∈ (PPx x').U (fun _ => j) := canon_mem m' hs' j _ (by rw [ept]; exact hj)
    have le : (t.PP.L.pull n.φ).U (fun _ => i) ≤ n.φ ⁻¹ᵁ t.PP.L.U i := fun q hq => mem_pull.1 hq
    have e₁ := hp (fun _ => j) (SecCalc.ppx_le pm ps _)
    rw [SecCalc.scal_one' x (fun _ => j), _root_.one_mul] at e₁
    rw [hθ (fun _ => i) le, gs_appLE n.φ _ _ le r z (mem_pull.2 hi), ← h Z (r ≫ n.φ) z j i hj hi, ← e₁,
      gs_appLE pm _ _ _ (r ≫ g') z a₁, Category.assoc, Category.assoc, eg]
  constructor
  · intro h' Z r z i k hi hk
    obtain ⟨j, hj⟩ := exists_chart Xo.univ.t.PP.isLB (m.φ (n.φ (r z)))
    have e := (key Z r z j i hj hi).symm.trans (h' Z r z j k (by rw [ept]; exact hj) hk)
    rw [T Z r z j i k hj hi hk, Units.val_mul, _root_.mul_assoc] at e
    exact (Units.mul_right_inj _).1 e
  · intro h' Z r z j k hj hk
    obtain ⟨i, hi⟩ := exists_chart t.PP.isLB (n.φ (r z))
    rw [ept] at hj
    rw [key Z r z j i hj hi, h' Z r z i k hi hk, T Z r z j i k hj hi hk, Units.val_mul, _root_.mul_assoc]

theorem secTie_calc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (t' : SAB H (Sp S)) (m : SABMap t' Xo.univ.t x) (th : LB.Sec t'.PP.L) (s : LB.Sec (PPx x)), SecTie m th s → (∀ (a : S) (x' : Sp S ⟶ Xo.X) (s' : LB.Sec (PPx x')) (th' : LB.Sec t'.PP.L), x' = x → SecBC (RingHom.id S) a x x' s s' → (SecTie m th' s' ↔ ∀ i, th'.f i = constFn t'.G.hom _ a * th.f i)) ∧ ∀ (S' : Type) [CommRing S'] (φ : S →+* S') (x' : Sp S' ⟶ Xo.X) (t'' : SAB H (Sp S')) (m' : SABMap t'' Xo.univ.t x') (n : SABMap t'' t' (spMap φ)) (s' : LB.Sec (PPx x')) (w : LB.Iso t''.PP.L (t'.PP.L.pull n.φ)) (θ : LB.Sec (t'.PP.L.pull n.φ)) (th' : LB.Sec t''.PP.L), x' = spMap φ ≫ x → m'.φ = n.φ ≫ m.φ → SecBC φ 1 x x' s s' → RigIso n w → PullSec n.φ th θ → (SecTie m' th' s' ↔ IsoMaps w th' θ) := by
  intro E _ _ _ H Dw l Xo S _ x t' m th s h
  refine ⟨fun a x' s' th' hx hb => ?_, fun S' _ φ x' t'' m' n s' w θ th' hx hφ hb hw hθ =>
    secTie_baseChange m h φ m' n s' w θ th' hx hφ hb hw hθ⟩
  subst hx
  have e : x' = spMap (RingHom.id S) ≫ x' := by rw [SecCalc.spMap_id', Category.id_comp]
  exact secTie_scale m h a
    (((SecCalc.sec_calc E H Dw l Xo S S S (RingHom.id S) (RingHom.id S) x' x' x' e e).2.1 a s s').1 hb)

end GlobalTheory.LamT.TieCalc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.BarEqOfLamEqMultiplier
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem bar_eq_of_lamEq_multiplier : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K] [NumberField K] (P B : Out.PolAV (Sp (𝓞 K))) (act : OAct (𝓞 E) P.A) (f : P.A ⟶ B.A) (h : 𝓞 E), 1 ≤ P.g → (∀ a, LamEq P.L (act.act a) (𝟙 P.A) P.L (𝟙 P.A) (act.act (H.bar a))) → LamEq B.L f f P.L (act.act h) (𝟙 P.A) → H.bar h = h := by
  intro hL E _ _ _ H K _ _ P B act f h hg hadj hf
  have : IsLocallyNoetherian (Sp (𝓞 K)) := inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of (𝓞 K))))
  have : IsCommMonObj P.A := P.isAb.comm
  have : IsCommMonObj B.A := B.isAb.comm
  have c := GlobalTheory.LamCalc.lamEq_calculus (Sp (𝓞 K)) P.A P.A

  have h₁ : LamEq B.L f f P.L (𝟙 P.A) (act.act h) :=
    ((c B.A P.A P.A B.L P.L P.L B.isLB P.isLB P.isLB f f f f _ (𝟙 _) _ (𝟙 _) (𝟙 _) (𝟙 _)).2.1 hf).2.1
  have h₂ : LamEq P.L (𝟙 P.A) (act.act h) B.L f f :=
    ((c B.A P.A P.A B.L P.L P.L B.isLB P.isLB P.isLB f f f f _ (𝟙 _) _ (𝟙 _) (𝟙 _) (𝟙 _)).2.1 h₁).1
  have h₃ : LamEq B.L f f P.L (𝟙 P.A) (act.act (H.bar h)) :=
    ((c B.A P.A P.A B.L P.L P.L B.isLB P.isLB P.isLB f f f f _ (𝟙 _) _ (𝟙 _) _ _).2.1 hf).2.2.1 (hadj h)
  have h₄ : LamEq P.L (𝟙 P.A) (act.act h) P.L (𝟙 P.A) (act.act (H.bar h)) :=
    ((c P.A B.A P.A P.L B.L P.L P.isLB B.isLB P.isLB _ (𝟙 _) _ (𝟙 _) f f f f _ _).2.1 h₂).2.2.1 h₃
  have h₅ : LamEq P.L (act.act h) (𝟙 P.A) P.L (act.act (H.bar h)) (𝟙 P.A) :=
    ((c P.A P.A P.A P.L P.L P.L P.isLB P.isLB P.isLB _ (𝟙 _) _ (𝟙 _) _ (𝟙 _) _ (𝟙 _) (𝟙 _) (𝟙 _)).2.1 h₄).2.1
  exact (GlobalTheory.T.ringOfIntegersAction_injective_on_abelianScheme hL E K P act hg (GlobalTheory.T.eq_of_lamEq_polAV hL _ P _ _ _ h₅)).symm

end GlobalTheory.LamF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LineBundleIsoDescendsFieldToDedekindDomain
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LineBundleIsoDescendsFieldToDedekindDomain
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.IsoDescent

theorem exists_gen_pull_div_iff {X Y : Scheme.{0}} (f : Y ⟶ X) {N N' : LB X} (hN : N.IsLB) (hN' : N'.IsLB) :
    (∃ t : LB.Gen ((LB.div N N').pull f), t.IsGen) ↔ LBIso (N.pull f) (N'.pull f) := by
  obtain ⟨Pic, groups, cl, pl, iso_iff, gen_iff, -, -, linComb, div⟩ :=
    CechPicMul.exists_picardGroup
  let _ := groups
  have pull_class {L : LB X} (hL : L.IsLB) :
      (L.pull f).IsLB ∧ cl (L.pull f) = pl f (cl L) := by
    simpa only [Fintype.prod_unique, zpow_one] using
      linComb X Y L hL PUnit (fun _ => f) (fun _ => 1)
  obtain ⟨hD, eD⟩ := div X N' N hN' hN
  obtain ⟨hDf, eDf⟩ := pull_class hD
  obtain ⟨hNf, eNf⟩ := pull_class hN
  obtain ⟨hN'f, eN'f⟩ := pull_class hN'
  rw [← gen_iff Y _ hDf, eDf, eD, map_div, div_eq_one, ← eNf, ← eN'f,
    iso_iff Y _ _ hNf hN'f]

theorem lbIso_of_field : ∀ (R k : Type) [CommRing R] [IsDedekindDomain R] [Field k] (β : R →+* k), Function.Injective β → ∀ (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (X' : Scheme.{0}) (π : X' ⟶ A.left) (p : X' ⟶ Sp k), IsPullback π p A.hom (spMap β) → ∀ N N' : LB A.left, N.IsLB → N'.IsLB → LBIso (N.pull (eSec A)) (N'.pull (eSec A)) → LBIso (N.pull π) (N'.pull π) → LBIso N N' := by
  intro R k _ _ _ β hβ A _ hA X' π p H N N' hN hN' he hπ
  have := hA.proper
  have := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ A.hom hA.smooth hA.geomConnected
  let K := FractionRing R
  let δ : K →+* k := IsFractionRing.lift hβ
  have hδ : spMap δ ≫ spMap (algebraMap R K) = spMap β := by
    have e : δ.comp (algebraMap R K) = β := RingHom.ext fun x => IsFractionRing.lift_algebraMap hβ x
    rw [← e]
    exact (Spec.map_comp _ _).symm
  have H₀ := IsPullback.of_hasPullback A.hom (spMap (algebraMap R K))
  set π₀ := pullback.fst A.hom (spMap (algebraMap R K))
  set p₀ := pullback.snd A.hom (spMap (algebraMap R K))
  let q := H₀.lift π (p ≫ spMap δ) (by rw [Category.assoc, hδ, H.w])
  have hq : q ≫ π₀ = π := H₀.lift_fst _ _ _
  have H₁ : IsPullback q p p₀ (spMap δ) := by
    refine IsPullback.of_right ?_ (H₀.lift_snd _ _ _) H₀
    rw [hq, hδ]
    exact H
  obtain ⟨Pic, groups, cl, pl, iso_iff, gen_iff, -, comp, linComb, div⟩ :=
    CechPicMul.exists_picardGroup
  let _ := groups
  have pull_class {S T : Scheme.{0}} (f : T ⟶ S) {L : LB S} (hL : L.IsLB) :
      (L.pull f).IsLB ∧ cl (L.pull f) = pl f (cl L) := by
    simpa only [Fintype.prod_unique, zpow_one] using
      linComb S T L hL PUnit (fun _ => f) (fun _ => 1)
  obtain ⟨hD, eD⟩ := div A.left N' N hN' hN
  obtain ⟨hD₀, eD₀⟩ := pull_class π₀ hD
  have h₁ : ∃ t : LB.Gen (((LB.div N N').pull π₀).pull q), t.IsGen := by
    obtain ⟨hDq, eDq⟩ := pull_class q hD₀
    obtain ⟨hDπ, eDπ⟩ := pull_class π hD
    rw [← gen_iff X' _ hDq, eDq, eD₀, ← comp, hq, ← eDπ, gen_iff X' _ hDπ]
    exact (exists_gen_pull_div_iff π hN hN').2 hπ
  obtain ⟨t, ht⟩ := h₁
  have h₂ := FieldTriv.exists_gen_of_isPullback δ p₀ q p H₁ hD₀ t ht
  have h₃ := TrivDedekind.exists_gen_of_generic R K A hA _ π₀ p₀ H₀ _ hD
    ((exists_gen_pull_div_iff _ hN hN').2 he) h₂
  rwa [← gen_iff A.left _ hD, eD, div_eq_one, iso_iff A.left _ _ hN hN'] at h₃

end GlobalTheory.IsoDescent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LineBundleIsoDescendsFieldToDedekindDomainStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleIso_descends_field_to_dedekindDomain : ∀ (R k : Type) [CommRing R] [IsDedekindDomain R] [Field k] (β : R →+* k), Function.Injective β → ∀ (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (X' : Scheme.{0}) (π : X' ⟶ A.left) (p : X' ⟶ Sp k), IsPullback π p A.hom (spMap β) → ∀ N N' : LB A.left, N.IsLB → N'.IsLB → LBIso (N.pull (eSec A)) (N'.pull (eSec A)) → LBIso (N.pull π) (N'.pull π) → LBIso N N' := by
  first | exact @GlobalTheory.IsoDescent.lbIso_of_field | exact GlobalTheory.IsoDescent.lbIso_of_field | (intros; apply GlobalTheory.IsoDescent.lbIso_of_field <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLieBasisLocalModel
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLieBasisLocalModel
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT

theorem exists_restrict_ringHom {R K V F : Type} [CommRing R] [CommRing K] [CommRing V] [CommRing F]
    (a : R →+* K) (b : V →+* F) (hb : Function.Injective b) (i : K →+* F)
    (h : ∀ r : R, i (a r) ∈ Set.range b) : ∃ ψ : R →+* V, b.comp ψ = i.comp a := by
  choose ψ hψ using h
  refine ⟨⟨⟨⟨ψ, hb ?_⟩, fun x y => hb ?_⟩, hb ?_, fun x y => hb ?_⟩, RingHom.ext fun r => hψ r⟩ <;>
    simp [hψ]

theorem exists_isLieBasis_locMod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (p : HeightOneSpectrum (𝓞 z.K)) (T : CDVR) (iK : z.K →+* T.Fr) (M : LocMod z T iK), (∀ y : z.K, iK y ∈ Set.range (algebraMap T.V T.Fr) ↔ p.valuation z.K y ≤ 1) → ∀ A : Matrix (Fin z.Φ.T.g) (Fin z.Φ.T.g) z.K, LamF.IsModelAt z.B.pol z.Φ.key z.m'.φ p A → ∃ vV : Fin z.Φ.T.g → (epsR T.V ⟶ M.G.t.G), IsLieBasis vV ∧ ∀ k, ∃ wK : epsR z.K ⟶ z.Φ.T.t.G, IsLieComb (A k) z.Φ.v wK ∧ spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)) ≫ (vV k).left ≫ M.n.φ = spMap (Formalism.L2.Pj.dualMap iK) ≫ wK.left ≫ z.m'.φ := by
  intro E _ _ _ H Dw l Xo c _ z p T iK M hT A hA
  obtain ⟨R, _, _, _, _, _, ρ, xR, φR, hg, hρ, hR, ⟨hfib, -⟩, -, hv⟩ := hA
  have hinj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective _ _
  obtain ⟨ψ, hψ⟩ := exists_restrict_ringHom (algebraMap R z.K) (algebraMap T.V T.Fr) hinj iK
    (fun r => (hT _).2 ((hR _).1 ⟨r, rfl⟩))
  have hρψ : M.ρ = ψ.comp ρ := by
    refine RingHom.ext fun x => hinj ?_
    have h₁ := RingHom.congr_fun M.hρ x
    have h₂ := RingHom.congr_fun hψ (ρ x)
    have h₃ := RingHom.congr_fun hρ x
    simp only [RingHom.comp_apply] at h₁ h₂ h₃ ⊢
    rw [h₁, h₂, h₃]
  have hp : IsGrpPullback xR.P.A z.B.t.G (spMap ρ) φR := hfib
  have e : spMap M.ρ = spMap ψ ≫ spMap ρ := by rw [hρψ]; exact spMap_comp ρ ψ
  have hn : IsGrpPullback M.G.t.G z.B.t.G (spMap M.ρ) M.n.φ := M.n.cart
  have w : M.n.φ ≫ z.B.t.G.hom = (M.G.t.G.hom ≫ spMap ψ) ≫ spMap ρ := by rw [hn.1.w, e, Category.assoc]
  have hq : IsGrpPullback M.G.t.G xR.P.A (spMap ψ) (hp.1.lift _ _ w) :=
    IsGrpPullback.cancel hp (hn.congr e (hp.1.lift_fst _ _ w).symm) (hp.1.lift_snd _ _ w)
  have := xR.P.isAb.comm
  obtain ⟨v', hb, hv'⟩ := GlobalTheory.exists_isLieBasis_baseChange R T.V ψ _ _ _ hq xR.P.isAb.smooth _ xR.v xR.basis
  have hb' : ∀ (k : ℕ) (hk : xR.P.g = k), IsLieBasis fun i : Fin k => v' (i.cast hk.symm) := by
    rintro k rfl
    exact hb
  refine ⟨fun k => v' (k.cast hg.symm), hb' _ hg, fun k => ?_⟩
  obtain ⟨wK, hw, hw'⟩ := hv k
  refine ⟨wK, hw, ?_⟩
  have ed : (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)).comp (Chart.dualMapR ψ) =
      (Formalism.L2.Pj.dualMap iK).comp (Formalism.L2.Pj.dualMap (algebraMap R z.K)) := by
    refine RingHom.ext fun x => ?_
    have h₁ := RingHom.congr_fun hψ x.fst
    have h₂ := RingHom.congr_fun hψ x.snd
    simp only [RingHom.comp_apply] at h₁ h₂
    refine TrivSqZeroExt.ext ?_ ?_
    · simpa [Formalism.L2.Pj.dualMap, Chart.dualMapR] using h₁
    · simp only [Formalism.L2.Pj.dualMap, Chart.dualMapR, RingHom.comp_apply, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
        TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
      exact h₂
  have es : spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)) ≫ spMap (Chart.dualMapR ψ) =
      spMap (Formalism.L2.Pj.dualMap iK) ≫ spMap (Formalism.L2.Pj.dualMap (algebraMap R z.K)) := by
    rw [← spMap_comp, ← spMap_comp, ed]
  have e₁ : (v' (k.cast hg.symm)).left ≫ M.n.φ =
      spMap (Chart.dualMapR ψ) ≫ (xR.v (k.cast hg.symm)).left ≫ φR := by
    rw [← Category.assoc, ← hv', Category.assoc, hp.1.lift_fst]
  exact (congrArg (_ ≫ ·) e₁).trans <| (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) es).trans <|
    (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hw'.symm)

end GlobalTheory.LamT
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLieBasisLocalModelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lieBasis_local_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (p : HeightOneSpectrum (𝓞 z.K)) (T : CDVR) (iK : z.K →+* T.Fr) (M : LocMod z T iK), (∀ y : z.K, iK y ∈ Set.range (algebraMap T.V T.Fr) ↔ p.valuation z.K y ≤ 1) → ∀ A : Matrix (Fin z.Φ.T.g) (Fin z.Φ.T.g) z.K, LamF.IsModelAt z.B.pol z.Φ.key z.m'.φ p A → ∃ vV : Fin z.Φ.T.g → (epsR T.V ⟶ M.G.t.G), IsLieBasis vV ∧ ∀ k, ∃ wK : epsR z.K ⟶ z.Φ.T.t.G, IsLieComb (A k) z.Φ.v wK ∧ spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)) ≫ (vV k).left ≫ M.n.φ = spMap (Formalism.L2.Pj.dualMap iK) ≫ wK.left ≫ z.m'.φ := by
  first | exact @GlobalTheory.LamT.exists_isLieBasis_locMod | exact GlobalTheory.LamT.exists_isLieBasis_locMod | (intros; apply GlobalTheory.LamT.exists_isLieBasis_locMod <;> assumption)
end
end
