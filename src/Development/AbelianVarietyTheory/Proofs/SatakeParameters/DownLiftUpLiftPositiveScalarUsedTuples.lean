module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAnalyticLocalLatticeBasis
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurDir
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PointsEqualEigenMatch
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodPlaceHeckeEigenMatch
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardElementSplitPlaceLabel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RuleSectionNowhereVanishingReal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DownLiftUpLiftPositiveScalarUsedTuples
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DownLiftUpLiftPositiveScalarUsedTuples
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling

namespace GlobalTheory.NRows.LamUsedProof

theorem main : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → GlobalTheory.NRows.LamUsed D := by
  intro h1 h2 h3 h4 D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH hD μ hU0 i σ
  have hU : Used0 D μ := hU0
  obtain ⟨t, rfl⟩ : ∃ t, Y.tup t = μ := ⟨_, Y.tupTie μ hU⟩
  set θ := D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) with hθ
  by_cases hne : D.what₂.isot ((i : ℕ) + 1) σ = ⊥
  · refine ⟨fun f hf => ?_, fun h => absurd hne h⟩
    rw [hne, Submodule.mem_bot] at hf
    subst hf
    simp
  obtain ⟨p, hL⟩ := GlobalTheory.Mem.R3.LabProof.hasLab_exists h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hD σ
  set c : ℝ := R.lam3 i t p A3.A.v0 with hc

  have hpre : ∀ y ∈ D.what₂.isot ((i : ℕ) + 1) σ, ∃ x ∈ (LinearMap.ker θ)ᗮ, θ x = y ∧
      ∀ x', ⟪θ x, θ x'⟫_ℂ = (c : ℂ) * ⟪x, x'⟫_ℂ := by
    intro y hy
    obtain ⟨x, rfl⟩ := GlobalTheory.T.liftThetaMap_surjective_onto_cuspForms_usedTuple h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hD i t hU y
    set K := (LinearMap.ker θ)ᗮ
    have hx0 : x - K.starProjection x ∈ LinearMap.ker θ := by
      have := K.sub_starProjection_mem_orthogonal x
      rwa [Submodule.orthogonal_orthogonal] at this
    have he : θ (K.starProjection x) = θ x := by
      rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at hx0; exact hx0.symm
    have hW : Y.mj.eW i (θ (K.starProjection x)) ∈ R.Wp3 i p := by
      rw [he]; exact hL.1 i ⟨θ x, hy, rfl⟩
    exact ⟨K.starProjection x, K.starProjection_apply_mem x, he,
      GlobalTheory.T.liftThetaMap_inner_eq_lambda_labelPart_baseLevel h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hD i t p hU (K.starProjection x)
        (K.starProjection_apply_mem x) hW⟩

  have heig : ∀ y ∈ D.what₂.isot ((i : ℕ) + 1) σ,
      D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.thetaT (Y.tup t) ((i : ℕ) + 1) y) = ((c : ℝ) : ℂ) • y := by
    intro y hy
    obtain ⟨x, -, rfl, hx⟩ := hpre y hy
    have ha : LinearMap.adjoint θ (θ x) = (c : ℂ) • x := by
      refine ext_inner_right ℂ fun x' => ?_
      rw [LinearMap.adjoint_inner_left, hx, inner_smul_left, Complex.conj_ofReal]
    show θ (LinearMap.adjoint θ (θ x)) = (c : ℂ) • θ x
    rw [ha, map_smul]
  have hlam : D.what₂.lamP (Y.tup t) ((i : ℕ) + 1) σ = c := Y.tied.lift.lamP (Y.tup t) hU i σ c hne heig
  refine ⟨fun f hf => by rw [hlam]; exact heig f hf, fun _ => ?_⟩
  rw [hlam]
  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 hne
  obtain ⟨x, -, rfl, hx⟩ := hpre y hy
  have h := hx x
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have hyn : 0 < ‖θ x‖ := norm_pos_iff.2 hy0
  have h' : ‖θ x‖ ^ 2 = c * ‖x‖ ^ 2 := by
    have h2 : ((‖θ x‖ ^ 2 : ℝ) : ℂ) = ((c * ‖x‖ ^ 2 : ℝ) : ℂ) := by
      first | (push_cast; exact h) | (push_cast; simpa using h) | (simp only [RCLike.ofReal_pow, Complex.ofReal_pow, Complex.ofReal_mul] at h ⊢; exact h) | (rw [Complex.ofReal_pow, Complex.ofReal_mul, Complex.ofReal_pow]; exact h)
    exact Complex.ofReal_injective h2
  by_contra hcn
  push_neg at hcn
  nlinarith [sq_nonneg ‖x‖, sq_pos_of_pos hyn]

end GlobalTheory.NRows.LamUsedProof
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DownLiftUpLiftPositiveScalarUsedTuplesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.downLift_upLift_positiveScalar_usedTuples : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → GlobalTheory.NRows.LamUsed D := by
  first | exact @GlobalTheory.NRows.LamUsedProof.main | exact GlobalTheory.NRows.LamUsedProof.main | (intros; apply GlobalTheory.NRows.LamUsedProof.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotMono0LpCharLpSp
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
open scoped TensorProduct

namespace GlobalTheory.SegLen

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem tmul_ne_zero_of_ne {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] {x : X} {y : Y}
    (hx : x ≠ 0) (hy : y ≠ 0) : x ⊗ₜ[ℂ] y ≠ 0 := by
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ Y, φ y ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hy ((Module.forall_dual_apply_eq_zero_iff ℂ y).1 hc)
  intro h0
  have := congrArg ((TensorProduct.rid ℂ X).toLinearMap ∘ₗ LinearMap.lTensor X φ) h0
  simp only [LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearEquiv.coe_coe, TensorProduct.rid_tmul,
    map_zero] at this
  exact hx ((smul_eq_zero.1 this).resolve_left hφ)

theorem lpChar_lpSp_one' (x : WD h) : x.lpChar (WD.lpSp (h := h) 1) = x := by
  have h1 : WD.lpSp (h := h) 1 = WD.lpOfChar h (WeilDeligne.unrChar h (qPow w 0)) (isSmooth_unrChar h _) := by
    refine WD.sound ⟨.refl _ _, fun σ v => ?_, fun v => ?_⟩
    · funext i
      simp [WDRep.spEig]
    · funext i
      simp [shiftEnd_apply]
  rw [h1, lpChar_lpOfChar]
  exact WD.lpTw_zero x

theorem not_mono0_lpChar_lpSp {x : WD h} (hx : IsIrrWD x) {n : ℕ} (hn : 2 ≤ n) :
    ¬ (x.lpChar (WD.lpSp (h := h) n)).mono0 := by
  have h0 := TemperedRec.monodromy_zero_of_irreducible_weilDeligne E Ω A w h x hx
  obtain ⟨m, b, rfl, hirr⟩ := hx
  have : Nontrivial (Fin m → ℂ) := Model.nontrivial_of_isIrreducible hirr
  obtain ⟨v, hv⟩ := exists_ne (0 : Fin m → ℂ)
  rw [WD.monodromyZero_ofWeilDeligneRepClass_iff] at h0
  rw [WD.lpSp, WD.lpChar_mk, WD.monodromyZero_ofWeilDeligneRepClass_iff, WDRep.tensor_N, h0, WDRep.sp_N, LinearMap.rTensor_zero, zero_add]
  intro hN
  obtain ⟨u, hu⟩ : ∃ u, shiftEnd n u ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact shiftEnd_ne_zero hn (LinearMap.ext hc)
  have := LinearMap.congr_fun hN (v ⊗ₜ u)
  rw [LinearMap.lTensor_tmul, LinearMap.zero_apply] at this
  exact tmul_ne_zero_of_ne hv hu this

end GlobalTheory.SegLen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalComponentUnitarisableTwist
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitCentreDerivativeEqSumDiagonalMatrixUnits
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitCentreDerivativeEqSumDiagonalMatrixUnits
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

namespace GlobalTheory.CuspRep.ZcTrace

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

def conjPerm : Equiv.Perm (E →+* ℂ) where
  toFun := ComplexEmbedding.conjugate
  invFun := ComplexEmbedding.conjugate
  left_inv τ := by ext x; simp [ComplexEmbedding.conjugate_coe_eq]
  right_inv τ := by ext x; simp [ComplexEmbedding.conjugate_coe_eq]

theorem sum_atEmb_I : ∑ τ : E →+* ℂ, atEmb τ Complex.I = 0 := by
  have e : ∀ τ : E →+* ℂ, atEmb (conjPerm τ) Complex.I = -atEmb τ Complex.I := by
    intro τ
    change atEmb (ComplexEmbedding.conjugate τ) Complex.I = _
    rw [atEmb_conj, Complex.conj_I, atEmb_eq]; simp
  have h := Equiv.sum_comp (conjPerm (E := E)) (fun τ => atEmb τ Complex.I)
  simp only [e, Finset.sum_neg_distrib] at h
  have h2 : (2 : ℝ) • ∑ τ : E →+* ℂ, atEmb τ Complex.I = 0 := by
    rw [two_smul]; nth_rewrite 1 [← h]; simp
  exact (smul_eq_zero.1 h2).resolve_left two_ne_zero

theorem sum_atEmb_one : ∑ τ : E →+* ℂ, atEmb τ 1 = (2 : ℝ) • (1 : Cinf E) := by
  classical
  have e : ∀ τ : E →+* ℂ, atEmb τ 1 = Pi.single (InfinitePlace.mk τ) 1 := by
    intro τ; unfold atEmb; split_ifs <;> simp
  simp only [e]
  funext w
  rw [Finset.sum_apply]
  simp only [Pi.single_apply, Finset.sum_boole]
  have hc : (Finset.univ.filter fun τ : E →+* ℂ => w = InfinitePlace.mk τ).card = 2 := by
    have := InfinitePlace.card_filter_mk_eq w
    rw [InfinitePlace.mult_isComplex ⟨w, IsTotallyComplex.isComplex w⟩] at this
    rw [← this]; congr 1; ext τ; simp [eq_comm]
  rw [hc]
  simp

theorem sum_Eop (a : ℕ) (i : Fin a) : ∑ τ : E →+* ℂ, Eop τ i i = lieS E a i i 1 := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Eop, ← Finset.smul_sum, Finset.sum_sub_distrib, ← map_sum, sum_atEmb_I, sum_atEmb_one, map_zero,
    smul_zero, sub_zero, map_smul]
  rw [← Complex.coe_smul, smul_smul]
  norm_num

end GlobalTheory.CuspRep.ZcTrace

namespace GlobalTheory.ResW


open GlobalTheory.CuspRep.ZcTrace in
theorem zc_eq_sum_Eop : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), GlobalTheory.ResW.zc E a = ∑ τ : E →+* ℂ, ∑ i : Fin a, GlobalTheory.CuspRep.Eop τ i i := by
  intro E _ _ _ a
  rw [Finset.sum_comm]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [sum_Eop, lieS_apply, ← map_sum]
  unfold zc
  congr 1
  funext k l
  simp [toL, Finset.sum_apply, Matrix.single_apply, eq_comm]
  simp only [Finset.sum_apply, Pi.single_apply]
  by_cases h : k = l
  · subst h; simp [ite_apply, Pi.single_apply]
  · simp [ite_apply, Pi.single_apply, h, Ne.symm h]

end GlobalTheory.ResW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitCentreDerivativeEqSumDiagonalMatrixUnitsStatement
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitCentreDerivative_eq_sum_diagonalMatrixUnits : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), GlobalTheory.ResW.zc E a = ∑ τ : E →+* ℂ, ∑ i : Fin a, GlobalTheory.CuspRep.Eop τ i i := by
  first | exact @GlobalTheory.ResW.zc_eq_sum_Eop | exact GlobalTheory.ResW.zc_eq_sum_Eop | (intros; apply GlobalTheory.ResW.zc_eq_sum_Eop <;> assumption)
end
end

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

namespace GlobalTheory.UnitLocWeight

open GlobalTheory.ResW

section Trace

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem zc_eq_sum_Eop : zc E a = ∑ τ : E →+* ℂ, ∑ i : Fin a, Eop τ i i := GlobalTheory.T.splitCentreDerivative_eq_sum_diagonalMatrixUnits E a

theorem sum_Eop_apply {π : CuspSub E a} {τ : E →+* ℂ} {m : Multiset ℂ} (h : π.HasInfChar τ m) {φ : Sm E a}
    (hφ : φ ∈ π.V) : (∑ i : Fin a, Eop τ i i) φ = m.sum • φ := GlobalTheory.T.cuspidal_traceMatrixUnits_acts_by_sum_infinitesimalCharacter E a π τ m h φ hφ

theorem cex_eq (π : CuspSub E a) : cex (⟨a, π⟩ : Letter E) = ∑ τ : E →+* ℂ, ((CG.mk π).infChar τ).sum := by
  refine (letter_centralExponent E ⟨a, π⟩).2.2.2.2 _ ?_
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  refine ⟨φ, hφ, h0, ?_⟩
  change zc E a φ = _
  rw [zc_eq_sum_Eop, LinearMap.sum_apply, Finset.sum_smul]
  exact Finset.sum_congr rfl fun τ _ => sum_Eop_apply (ParLaws.hasInfChar_infChar (CG.mk π) τ) hφ

end Trace

end GlobalTheory.UnitLocWeight

namespace GlobalTheory.UnitLocWeight

open GlobalTheory.ResW

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

theorem sum_infChar_of_isWeight {π : CuspSub E a} {wt : ℤ} (h : IsWeight π wt) :
    ∑ τ : E →+* ℂ, ((CG.mk π).infChar τ).sum =
      (Module.finrank ℚ E : ℂ) * ((a : ℂ) * ((a : ℂ) - 1 - (wt : ℂ))) / 2 := by
  set c : E →+* E := (IsCMField.complexConj E).toRingEquiv.toRingHom
  have hc : Function.Bijective fun τ : E →+* ℂ => τ.comp c := by
    refine Finite.injective_iff_bijective.1 fun τ τ' e => RingHom.ext fun x => ?_
    obtain ⟨y, rfl⟩ := (IsCMField.complexConj E).surjective x
    exact RingHom.congr_fun e y
  have h1 : ∑ τ : E →+* ℂ, ((CG.mk π).infChar (τ.comp c)).sum = ∑ τ : E →+* ℂ, ((CG.mk π).infChar τ).sum :=
    Function.Bijective.sum_comp hc (fun τ => ((CG.mk π).infChar τ).sum)
  have h2 : ∀ τ : E →+* ℂ, ((CG.mk π).infChar (τ.comp c)).sum =
      (a : ℂ) * ((a : ℂ) - 1 - (wt : ℂ)) - ((CG.mk π).infChar τ).sum := fun τ => by
    rw [h τ, Multiset.sum_map_sub, Multiset.map_const', Multiset.sum_replicate, CG.card_infChar, Multiset.map_id',
      nsmul_eq_mul]
  have h3 := Embeddings.card E ℂ
  simp only [h2, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, h3, nsmul_eq_mul] at h1
  linear_combination -h1 / 2

end GlobalTheory.UnitLocWeight

namespace GlobalTheory.UnitLocWeight

open GlobalTheory.ResW

theorem rexp_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} (ha : 1 ≤ a) {π : CuspSub E a} {wt : ℤ}
    (h : IsWeight π wt) : rexp (⟨a, π⟩ : Letter E) = ((a : ℝ) - 1 - wt) / 2 := by
  have e := (cex_eq π).trans (sum_infChar_of_isWeight h)
  have hd : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have e2 : (cex (⟨a, π⟩ : Letter E)).re = (Module.finrank ℚ E : ℝ) * ((a : ℝ) * ((a : ℝ) - 1 - wt)) / 2 := by
    rw [e]
    have : (Module.finrank ℚ E : ℂ) * ((a : ℂ) * ((a : ℂ) - 1 - (wt : ℂ))) / 2 =
        (((Module.finrank ℚ E : ℝ) * ((a : ℝ) * ((a : ℝ) - 1 - wt)) / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.ofReal_re]
  unfold rexp
  change (cex (⟨a, π⟩ : Letter E)).re / ((a : ℝ) * Module.finrank ℚ E) = _
  rw [e2]
  field_simp

end GlobalTheory.UnitLocWeight
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaEigenCompatibilityFirst
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.EigSplit

open Formalism.IndefR.Links in
theorem cast_add {D : D7} {μ : D.what₂.Tup} {a b : ℕ} (h : a = b) (x y : D.what₂.Mt μ a) :
    (h ▸ (x + y) : D.what₂.Mt μ b) = (h ▸ x : D.what₂.Mt μ b) + (h ▸ y : D.what₂.Mt μ b) := by
  subst h; rfl

theorem cast_zero {D : D7} {μ : D.what₂.Tup} {a b : ℕ} (h : a = b) :
    (h ▸ (0 : D.what₂.Mt μ a) : D.what₂.Mt μ b) = 0 := by
  subst h; rfl

theorem cast_inj {D : D7} {μ : D.what₂.Tup} {a b : ℕ} (h : a = b) {x y : D.what₂.Mt μ a}
    (hxy : (h ▸ x : D.what₂.Mt μ b) = (h ▸ y : D.what₂.Mt μ b)) : x = y := by
  subst h; exact hxy

theorem cast_symm {D : D7} {μ : D.what₂.Tup} {a b : ℕ} (h : a = b) (m : D.what₂.Mt μ b) :
    (h ▸ (h.symm ▸ m : D.what₂.Mt μ a) : D.what₂.Mt μ b) = m := by
  subst h; rfl

theorem fn_zero {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch} (X : GlobalTheory.NJoin.RealAt D cf nch tp)
    {μ : D.what₂.Tup} (hμ : Formalism.IndefR.RecTie.Used0 D μ) (j : Fin D.R.m) : X.fn hμ j 0 = 0 := by
  unfold GlobalTheory.NJoin.RealAt.fn; simp; rfl

theorem fn_add {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch} (X : GlobalTheory.NJoin.RealAt D cf nch tp)
    {μ : D.what₂.Tup} (hμ : Formalism.IndefR.RecTie.Used0 D μ) (j : Fin D.R.m) (x y : D.what₂.Mt μ (j.1 + 1)) :
    X.fn hμ j (x + y) = X.fn hμ j x + X.fn hμ j y := by
  unfold GlobalTheory.NJoin.RealAt.fn; simp; rfl

theorem rep_mem {D : D7} (V : Formalism.BasicNotions.TH.HSp D) (Pp : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ)
    {γ : Formalism.L2.Theta.GA D V} (hγ : γ ∈ GlobalTheory.Hk3.rep V Pp d) : γ ∈ Formalism.L2.Theta.GfC V := by
  unfold GlobalTheory.Hk3.rep at hγ
  split_ifs at hγ with hl
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hR⟩ := hl.choose_spec
    exact (hR.1 γ hγ).1
  · simp at hγ

theorem twist_eq {G H W : Type*} [Group G] [Group H] [AddCommGroup W] [Module ℂ W] (ρ : G →* Module.End ℂ W)
    (rr : G →* H) (F : H → W) (g γ : G) (h1 : ρ γ⁻¹ = 1) :
    ρ (g * γ)⁻¹ (F (rr (g * γ))) = ρ g⁻¹ (F (rr g * rr γ)) := by
  rw [mul_inv_rev, map_mul, map_mul, h1, one_mul]

theorem sum_single_one {W : Type*} [AddCommGroup W] [Module ℂ W] (d : List ℤ) (S : List ℤ → W) :
    (Finsupp.single d (1 : ℂ)).sum (fun d z => z • S d) = S d := by
  rw [Finsupp.sum_single_index (h := fun d (z : ℂ) => z • S d) (zero_smul ℂ _), one_smul]

theorem transport {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch} (X : GlobalTheory.NJoin.RealAt D cf nch tp)
    (j : Fin D.R.m) (t : X.T) (h : DIV.Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (X.R.HV j t).H)
    (hh : GlobalTheory.Hk3.IsOpsV X.R j t h) (Pp : DIV.Pl D.host.E) (hG : GlobalTheory.Hk3.Good X.R t Pp) (d : List ℤ)
    (y : (X.R.HV j t).H) (c : ℂ)
    (hc : ∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.R.extV j t y (g * γ) = c • X.R.extV j t y g) :
    h Pp (Finsupp.single d 1) y = c • y := by
  have hcv := (X.given.core.models.cV j).1
  apply X.hinj j t
  funext g
  have e1 : X.R.extV j t (c • y) g = c • X.R.extV j t y g :=
    congrFun ((X.R.extV j t).map_smul c y) g
  have e3 : ∀ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.R.extV j t y (g * γ) =
      (X.R.cV j).ρ g⁻¹ ((X.R.HV j t).e y ((Formalism.L2.Theta.finHom (Formalism.IndefR.Links.Vc D j)).rangeRestrict g *
        (Formalism.L2.Theta.finHom (Formalism.IndefR.Links.Vc D j)).rangeRestrict γ)) := by
    intro γ hγ
    exact twist_eq (X.R.cV j).ρ (Formalism.L2.Theta.finHom (Formalism.IndefR.Links.Vc D j)).rangeRestrict ((X.R.HV j t).e y) g γ
      (hcv γ⁻¹ (inv_mem (rep_mem _ Pp d hγ)))
  have e2 : X.R.extV j t (h Pp (Finsupp.single d 1) y) g =
      ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.R.extV j t y (g * γ) := by
    refine Eq.trans ?_ (Finset.sum_congr rfl e3).symm
    show (X.R.cV j).ρ g⁻¹ ((X.R.HV j t).e (h Pp (Finsupp.single d 1) y)
      ((Formalism.L2.Theta.finHom (Formalism.IndefR.Links.Vc D j)).rangeRestrict g)) = _
    refine Eq.trans (congrArg ((X.R.cV j).ρ g⁻¹) (congrFun (hh Pp hG (Finsupp.single d 1) y)
      ((Formalism.L2.Theta.finHom (Formalism.IndefR.Links.Vc D j)).rangeRestrict g))) ?_
    unfold GlobalTheory.Hk3.hkF
    exact (congrArg ((X.R.cV j).ρ g⁻¹) (sum_single_one d _)).trans (map_sum ((X.R.cV j).ρ g⁻¹) _ _)
  exact e2.trans ((hc g).trans e1.symm)

theorem eig_zero {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch} (X : GlobalTheory.NJoin.RealAt D cf nch tp)
    {μ : D.what₂.Tup} (hμ : Formalism.IndefR.RecTie.Used0 D μ) (j : Fin D.R.m) (Pp : DIV.Pl D.host.E) (d : List ℤ) (c : ℂ) :
    ∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j 0 (g * γ) = c • X.fn hμ j 0 g := by
  intro g
  rw [fn_zero]
  simp

theorem eig_add {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch} (X : GlobalTheory.NJoin.RealAt D cf nch tp)
    {μ : D.what₂.Tup} (hμ : Formalism.IndefR.RecTie.Used0 D μ) (j : Fin D.R.m) (Pp : DIV.Pl D.host.E) (d : List ℤ) (c : ℂ)
    (f₁ f₂ : D.what₂.Mt μ (j.1 + 1)) (h₁ : ∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j f₁ (g * γ) = c • X.fn hμ j f₁ g) (h₂ : ∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j f₂ (g * γ) = c • X.fn hμ j f₂ g) :
    ∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j (f₁ + f₂) (g * γ) = c • X.fn hμ j (f₁ + f₂) g := by
  intro g
  rw [fn_add]
  simp only [Pi.add_apply, Finset.sum_add_distrib, smul_add, h₁ g, h₂ g]

theorem alongEig {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch} (X : GlobalTheory.NJoin.RealAt D cf nch tp)
    (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (x : D.nd.X i) (Pp : DIV.Pl D.host.E) (d : List ℤ) (c : ℂ)
    (hc : ∀ Q : D.naut.AV i, D.naut.ptV i Q = some x → ∀ f' : D.what₂.Mt (D.nd.mu i) (j.1 + 1),
      (hj ▸ f' : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ D.naut.typeV i Q → ∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j f' (g * γ) = c • X.fn hμ j f' g) :
    ∀ m ∈ eigC D.nd D.naut i x, ∀ f' : D.what₂.Mt (D.nd.mu i) (j.1 + 1),
      (hj ▸ f' : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) = m → ∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j f' (g * γ) = c • X.fn hμ j f' g := by
  intro m hm
  unfold eigC at hm
  refine Submodule.iSup_induction (fun Q => ⨆ (_ : Q ∈ {P | D.naut.ptV i P = some x}), D.naut.typeV i Q)
    (motive := fun m => ∀ f' : D.what₂.Mt (D.nd.mu i) (j.1 + 1),
      (hj ▸ f' : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) = m → ∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j f' (g * γ) = c • X.fn hμ j f' g) hm ?_ ?_ ?_
  · intro Q m' hm' f' hf'
    by_cases hQ : D.naut.ptV i Q = some x
    · rw [iSup_pos (show Q ∈ {P | D.naut.ptV i P = some x} from hQ)] at hm'
      exact hc Q hQ f' (hf' ▸ hm')
    · rw [iSup_neg (show Q ∉ {P | D.naut.ptV i P = some x} from hQ), Submodule.mem_bot] at hm'
      have : f' = 0 := cast_inj hj (hf'.trans (hm'.trans (cast_zero hj).symm))
      subst this
      exact eig_zero X hμ j Pp d c
  · intro f' hf'
    have : f' = 0 := cast_inj hj (hf'.trans (cast_zero hj).symm)
    subst this
    exact eig_zero X hμ j Pp d c
  · intro m1 m2 ih1 ih2 f' hf'
    have hsplit : f' = (hj.symm ▸ m1 : D.what₂.Mt (D.nd.mu i) (j.1 + 1)) + (hj.symm ▸ m2) := by
      apply cast_inj hj
      rw [hf', cast_add, cast_symm, cast_symm]
    subst hsplit
    exact eig_add X hμ j Pp d c _ _ (ih1 _ (cast_symm hj m1)) (ih2 _ (cast_symm hj m2))

end GlobalTheory.EigSplit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExtensionVectorThetaCompatible
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardFrameMemHyperspecialIffMaxCompactTrivOut
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardFrameMemHyperspecialIffMaxCompactTrivOut
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.FrameHyp.mem_hyp_iff : ∀ {D : D7} (hF : D.host.F = maximalRealSubfield D.host.E) {V : TH.HSp D} {n : ℕ}
    (Ps : Formalism.IndefR.principalLevelFrame.RowPsi V n), GlobalTheory.NJoin.StdFrame hF Ps → ∀ (sp : SplitPlace D.host.E)
    (κ : Formalism.AUTREP.GAf D.host.E n), Ps.ψ κ ∈ GlobalTheory.Hk3.hyp V sp.w ↔ κ ∈ Umax D.host.E n ∧ TrivOutside {sp.v} κ := by
  intro D hF V n Ps hstd sp κ
  constructor
  · rintro ⟨hK, e, f, hef, hs⟩
    exact ⟨(hstd.2 κ).2 hK,
      (GlobalTheory.LabelTransport.suppF_iff_trivOutside D sp hF V n Ps hstd e f hef κ).1 hs⟩
  · rintro ⟨hU, hT⟩
    obtain ⟨-, e, f, hef, -⟩ := GlobalTheory.DefLiftHecke.one_mem_hyp V sp.w
    exact ⟨(hstd.2 κ).1 hU, e, f, hef,
      (GlobalTheory.LabelTransport.suppF_iff_trivOutside D sp hF V n Ps hstd e f hef κ).2 hT⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardFrameMemHyperspecialIffMaxCompactTrivOutStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardFrame_mem_hyperspecial_iff_maxCompact_trivOutside : ∀ {D : D7} (hF : D.host.F = maximalRealSubfield D.host.E) {V : TH.HSp D} {n : ℕ} (Ps : Formalism.IndefR.principalLevelFrame.RowPsi V n), GlobalTheory.NJoin.StdFrame hF Ps → ∀ (sp : SplitPlace D.host.E) (κ : Formalism.AUTREP.GAf D.host.E n), Ps.ψ κ ∈ GlobalTheory.Hk3.hyp V sp.w ↔ κ ∈ Umax D.host.E n ∧ TrivOutside {sp.v} κ := by
  first | exact @GlobalTheory.FrameHyp.mem_hyp_iff | exact GlobalTheory.FrameHyp.mem_hyp_iff | (intros; apply GlobalTheory.FrameHyp.mem_hyp_iff <;> assumption)
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.EigTransport

theorem frame_hyp : ∀ {D : D7} (hF : D.host.F = maximalRealSubfield D.host.E) {V : TH.HSp D} {n : ℕ}
    (Ps : Formalism.IndefR.principalLevelFrame.RowPsi V n), GlobalTheory.NJoin.StdFrame hF Ps → ∀ (sp : SplitPlace D.host.E)
    (κ : Formalism.AUTREP.GAf D.host.E n), Ps.ψ κ ∈ GlobalTheory.Hk3.hyp V sp.w ↔ κ ∈ Umax D.host.E n ∧ TrivOutside {sp.v} κ := GlobalTheory.T.standardFrame_mem_hyperspecial_iff_maxCompact_trivOutside

theorem exists_std : ∀ {D : D7} (hF : D.host.F = maximalRealSubfield D.host.E) {V : TH.HSp D} {n : ℕ}
    (Ps : Formalism.IndefR.principalLevelFrame.RowPsi V n), GlobalTheory.NJoin.StdFrame hF Ps → V.rank = n → ∀ (sp : SplitPlace D.host.E)
    (ϖ : (sp.v).adicCompletion (maximalRealSubfield D.host.E)), Formalism.AUTREP.IsUnif D.host.E sp.v ϖ →
    ∀ k ≤ n, ∃ x₀ ∈ Formalism.AUTREP.tSet D.host.E n sp ϖ k, ∃ (e f : Formalism.L2.Theta.AE D) (ϖ' : 𝓞 D.host.E),
      Formalism.IndefR.Mult.IsPrimeIdem sp.w e f ∧ ϖ' ∈ sp.w.asIdeal ∧ ϖ' ∉ sp.w.asIdeal ^ 2 ∧
        Formalism.IndefR.Mult.SuppF V f (Ps.ψ x₀) ∧
        Formalism.IndefR.Mult.DivAt V e (ϖ' : D.host.E) (List.replicate k 1 ++ List.replicate (n - k) 0) (Ps.ψ x₀) := GlobalTheory.T.standardElement_splitPlace_label

theorem tSet_dc : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] (n : ℕ) (sp : SplitPlace L)
    (ϖ : (sp.v).adicCompletion (maximalRealSubfield L)) (k : ℕ), ∀ x₀ ∈ Formalism.AUTREP.tSet L n sp ϖ k,
    ∀ κ, κ ∈ Formalism.AUTREP.tSet L n sp ϖ k ↔ ∃ k₁, (k₁ ∈ Umax L n ∧ TrivOutside {sp.v} k₁) ∧
      ∃ k₂, (k₂ ∈ Umax L n ∧ TrivOutside {sp.v} k₂) ∧ κ = k₁ * x₀ * k₂ := GlobalTheory.T.mem_heckeSplitPlaceSet_iff_doubleCoset

theorem pairwise_lab (k m : ℕ) : List.Pairwise (fun a b : ℤ => b ≤ a) (List.replicate k 1 ++ List.replicate m 0) := by
  rw [List.pairwise_append]
  refine ⟨List.pairwise_replicate.2 (Or.inr le_rfl), List.pairwise_replicate.2 (Or.inr le_rfl), ?_⟩
  intro a ha b hb
  rw [List.eq_of_mem_replicate ha, List.eq_of_mem_replicate hb]
  norm_num

end GlobalTheory.EigTransport

namespace GlobalTheory.EigTransport

theorem isLab_std {D : D7} (hF : D.host.F = maximalRealSubfield D.host.E) {V : TH.HSp D} {n : ℕ}
    (Ps : Formalism.IndefR.principalLevelFrame.RowPsi V n) (hs : GlobalTheory.NJoin.StdFrame hF Ps) (hn : V.rank = n) (sp : SplitPlace D.host.E)
    (ϖ : (sp.v).adicCompletion (maximalRealSubfield D.host.E)) (hϖ : Formalism.AUTREP.IsUnif D.host.E sp.v ϖ)
    (k : ℕ) (hk : k ≤ n) :
    GlobalTheory.Hk3.IsLab V sp.w (List.replicate k 1 ++ List.replicate (n - k) 0) := by
  obtain ⟨x₀, -, e, f, ϖ', h1, h2, h3, h4, h5⟩ := exists_std hF Ps hs hn sp ϖ hϖ k hk
  exact GlobalTheory.SphLabelOps.isLab_of_divAt h1 h2 h3 (pairwise_lab _ _) h4 h5

theorem tSet_iff {D : D7} (hF : D.host.F = maximalRealSubfield D.host.E) {V : TH.HSp D} {n : ℕ}
    (Ps : Formalism.IndefR.principalLevelFrame.RowPsi V n) (hs : GlobalTheory.NJoin.StdFrame hF Ps) (hn : V.rank = n) (sp : SplitPlace D.host.E)
    (ϖ : (sp.v).adicCompletion (maximalRealSubfield D.host.E)) (hϖ : Formalism.AUTREP.IsUnif D.host.E sp.v ϖ)
    (k : ℕ) (hk : k ≤ n) (κ : Formalism.AUTREP.GAf D.host.E n) :
    κ ∈ Formalism.AUTREP.tSet D.host.E n sp ϖ k ↔
      ∃ γ ∈ GlobalTheory.Hk3.rep V sp.w (List.replicate k 1 ++ List.replicate (n - k) 0),
        γ⁻¹ * Ps.ψ κ ∈ GlobalTheory.Hk3.hyp V sp.w := by
  obtain ⟨x₀, hx₀, e, f, ϖ', h1, h2, h3, h4, h5⟩ := exists_std hF Ps hs hn sp ϖ hϖ k hk
  have hLab := GlobalTheory.SphLabelOps.isLab_of_divAt h1 h2 h3 (pairwise_lab _ _) h4 h5
  obtain ⟨K, hK⟩ := GlobalTheory.SphLabelOps.exists_hyp V sp.w
  have hR := GlobalTheory.SphLabelOps.reps_of_sphOp hK h1 h2 h3 h4 h5 (GlobalTheory.SphLabelOps.sphOp_rep hLab)
  have memK : ∀ l, l ∈ K ↔ l ∈ GlobalTheory.Hk3.hyp V sp.w := fun l => by rw [hK]; rfl
  have pre : ∀ l ∈ K, ∃ m, (m ∈ Umax D.host.E n ∧ TrivOutside {sp.v} m) ∧ Ps.ψ m = l := by
    intro l hl
    have hl' := (memK l).1 hl
    obtain ⟨m, rfl⟩ := Ps.onto l hl'.1.1
    exact ⟨m, (frame_hyp hF Ps hs sp m).1 hl', rfl⟩
  have img : ∀ m, (m ∈ Umax D.host.E n ∧ TrivOutside {sp.v} m) → Ps.ψ m ∈ K := fun m hm =>
    (memK _).2 ((frame_hyp hF Ps hs sp m).2 hm)
  constructor
  · intro hκ
    obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := (tSet_dc n sp ϖ k x₀ hx₀ κ).1 hκ
    obtain ⟨γ, ⟨hγ, hm⟩, -⟩ := hR.2 (Ps.ψ (k₁ * x₀ * k₂))
      ⟨Ps.ψ k₁, img _ hk₁, Ps.ψ k₂, img _ hk₂, by rw [map_mul, map_mul]⟩
    exact ⟨γ, hγ, (memK _).1 hm⟩
  · rintro ⟨γ, hγ, hm⟩
    obtain ⟨l₁, hl₁, l₂, hl₂, hγe⟩ := hR.1 γ hγ
    have hl : γ⁻¹ * Ps.ψ κ ∈ K := (memK _).2 hm
    obtain ⟨m₁, hm₁, e₁⟩ := pre l₁ hl₁
    obtain ⟨m₂, hm₂, e₂⟩ := pre (l₂ * (γ⁻¹ * Ps.ψ κ)) (mul_mem hl₂ hl)
    refine (tSet_dc n sp ϖ k x₀ hx₀ κ).2 ⟨m₁, hm₁, m₂, hm₂, Ps.inj ?_⟩
    rw [map_mul, map_mul, e₁, e₂, ← mul_assoc, ← mul_assoc, ← hγe, mul_inv_cancel, one_mul]

end GlobalTheory.EigTransport

namespace GlobalTheory.EigTransport


open Classical in
theorem finsum_cosets {G W ι : Type} [Group G] [AddCommGroup W] (J : Subgroup G) (T : Set G) (R : Finset ι)
    (x : ι → G) (F : G → W) (h1 : ∀ γ ∈ R, x γ ∈ T) (h2 : ∀ y ∈ T, ∃ γ ∈ R, (x γ)⁻¹ * y ∈ J)
    (h3 : ∀ γ ∈ R, ∀ γ' ∈ R, (x γ)⁻¹ * x γ' ∈ J → γ = γ')
    (hF : ∀ y ∈ T, ∀ y' ∈ T, y⁻¹ * y' ∈ J → ∀ g, F (g * y') = F (g * y)) (g : G) :
    (∑ᶠ c : G ⧸ J, if hc : ∃ y ∈ T, (y : G ⧸ J) = c then F (g * hc.choose) else 0) =
      ∑ γ ∈ R, F (g * x γ) := by
  classical
  have hsupp : (Function.support fun c : G ⧸ J =>
      if hc : ∃ y ∈ T, (y : G ⧸ J) = c then F (g * hc.choose) else 0) ⊆
      ↑(R.image fun γ => (x γ : G ⧸ J)) := by
    intro c hc
    by_cases h : ∃ y ∈ T, (y : G ⧸ J) = c
    · obtain ⟨y, hy, rfl⟩ := h
      obtain ⟨γ, hγ, hm⟩ := h2 y hy
      exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨γ, hγ, QuotientGroup.eq.2 hm⟩)
    · exact absurd (by simp [h]) hc
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_image]
  · refine Finset.sum_congr rfl fun γ hγ => ?_
    have hc : ∃ y ∈ T, (y : G ⧸ J) = (x γ : G ⧸ J) := ⟨x γ, h1 γ hγ, rfl⟩
    rw [dif_pos hc]
    obtain ⟨hy, he⟩ := hc.choose_spec
    exact (hF _ hy _ (h1 γ hγ) (QuotientGroup.eq.1 he) g).symm
  · intro γ hγ γ' hγ' e
    exact h3 γ hγ γ' hγ' (QuotientGroup.eq.1 e)

theorem triv_mul {D : D7} {n : ℕ} {T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))}
    {x y : Formalism.AUTREP.GAf D.host.E n} (hx : TrivOutside T x) (hy : TrivOutside T y) : TrivOutside T (x * y) :=
  fun v hv => by
    have e : (x * y).1.1 = x.1.1 * y.1.1 := rfl
    show (x * y).1.1.map (compAt D.host.E v) = 1
    rw [e, Matrix.map_mul]
    rw [show x.1.1.map (compAt D.host.E v) = 1 from hx v hv, show y.1.1.map (compAt D.host.E v) = 1 from hy v hv, mul_one]

theorem triv_inv {D : D7} {n : ℕ} {T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))}
    {x : Formalism.AUTREP.GAf D.host.E n} (hx : TrivOutside T x) : TrivOutside T x⁻¹ := fun v hv => by
  have e : (x⁻¹).1.1.map (compAt D.host.E v) * x.1.1.map (compAt D.host.E v) = 1 := by
    rw [← Matrix.map_mul]
    have : (x⁻¹).1.1 * x.1.1 = 1 := by
      show (x⁻¹ * x).1.1 = 1
      rw [inv_mul_cancel]
      rfl
    rw [this, Matrix.map_one _ (map_zero _) (map_one _)]
  show (x⁻¹).1.1.map (compAt D.host.E v) = 1
  rwa [show x.1.1.map (compAt D.host.E v) = 1 from hx v hv, mul_one] at e

theorem rep_inj {D : D7} (V : TH.HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ)
    (hd : GlobalTheory.Hk3.IsLab V P d) : ∀ γ ∈ GlobalTheory.Hk3.rep V P d, ∀ γ' ∈ GlobalTheory.Hk3.rep V P d,
      γ⁻¹ * γ' ∈ GlobalTheory.Hk3.hyp V P → γ = γ' := by
  obtain ⟨K, hK⟩ := GlobalTheory.SphLabelOps.exists_hyp V P
  obtain ⟨g₀, -, hR⟩ := GlobalTheory.SphLabelOps.exists_reps hK (GlobalTheory.SphLabelOps.sphOp_rep hd)
  intro γ hγ γ' hγ' hm
  rw [hK] at hm
  exact (hR.2 γ' (hR.1 γ' hγ')).unique ⟨hγ, hm⟩ ⟨hγ', by rw [inv_mul_cancel]; exact one_mem K⟩

end GlobalTheory.EigTransport

namespace GlobalTheory.EigTransport

theorem sum_single {M : Type} [AddCommGroup M] [Module ℂ M] (d : List ℤ) (G : List ℤ → M) :
    ∑ d' ∈ (Finsupp.single d (1 : ℂ)).support, (Finsupp.single d (1 : ℂ)) d' • G d' = G d := by
  rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton, Finsupp.single_eq_same, one_smul]
end GlobalTheory.EigTransport

namespace GlobalTheory.EigTransport

theorem eig_sum {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch}
    (X : GlobalTheory.NJoin.RealAt D cf nch tp) {μ : D.what₂.Tup} (hμ : Formalism.IndefR.RecTie.Used0 D μ) (j : Fin D.R.m)
    (f : D.what₂.Mt μ (j.1 + 1)) (y) (hy : X.R.extV j (X.tupT μ) y = X.fn hμ j f) (h)
    (hOps : GlobalTheory.Hk3.IsOpsV X.R j (X.tupT μ) h) (s : GlobalTheory.DownLift.Sys D)
    (hEig : GlobalTheory.DownLift.IsEigV X.R j (X.tupT μ) h s y) (P : HeightOneSpectrum (𝓞 D.host.E))
    (hG : GlobalTheory.Hk3.Good X.R (X.tupT μ) P) (d : List ℤ) (hd : GlobalTheory.Hk3.IsLab (Formalism.IndefR.Links.Vc D j) P d)
    (g : Formalism.L2.Theta.GA D (Formalism.IndefR.Links.Vc D j)) :
    ∑ a ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) P d, X.fn hμ j f (g * a) = s P d • X.fn hμ j f g := by
  have hc : (X.R.cV j).Is := X.given.core.models.cV j
  have e1 := hOps P hG (Finsupp.single d 1) y
  have e2 := hEig P d hG hd
  have e4 : GlobalTheory.Hk3.hkF (Formalism.IndefR.Links.Vc D j) P (Finsupp.single d 1) ((X.R.HV j (X.tupT μ)).e y) =
      s P d • (X.R.HV j (X.tupT μ)).e y :=
    e1.symm.trans ((congrArg (X.R.HV j (X.tupT μ)).e e2).trans (map_smul _ _ _))
  have e3 := ((congrArg (fun F => (X.R.cV j).ext F g) e4).symm.trans
    (GlobalTheory.DefLiftHecke.ext_hkF (X.R.cV j) hc P (Finsupp.single d 1) ((X.R.HV j (X.tupT μ)).e y) g)).trans
    (sum_single d _)
  have hy2 : ∀ x, (X.R.cV j).ext ((X.R.HV j (X.tupT μ)).e y) x = X.fn hμ j f x := fun x =>
    (show X.R.extV j (X.tupT μ) y x = (X.R.cV j).ext ((X.R.HV j (X.tupT μ)).e y) x from rfl).symm.trans (congrFun hy x)
  calc ∑ a ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) P d, X.fn hμ j f (g * a)
      = ∑ a ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) P d, (X.R.cV j).ext ((X.R.HV j (X.tupT μ)).e y) (g * a) :=
        Finset.sum_congr rfl fun a _ => (hy2 _).symm
    _ = (X.R.cV j).ext (s P d • (X.R.HV j (X.tupT μ)).e y) g := e3.symm
    _ = s P d • (X.R.cV j).ext ((X.R.HV j (X.tupT μ)).e y) g :=
        congrFun (map_smul (X.R.cV j).ext (s P d) ((X.R.HV j (X.tupT μ)).e y)) g
    _ = s P d • X.fn hμ j f g := by rw [hy2]

end GlobalTheory.EigTransport

namespace GlobalTheory.EigTransport

end GlobalTheory.EigTransport
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AutomorphicLevelAwayNonsplit
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSatUOfUnderEq
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL
namespace GlobalTheory.CongL.SatConj

theorem exists_satU_of_under_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (U : Submodule ℂ (UA E a → ℂ)), IsAutRepU U → ∀ w u : HeightOneSpectrum (𝓞 E), IsSplitAt w → u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) → (∃ B, SatU U w B) → ∃ B, SatU U u B := by
  intro E _ _ _ a U hU w u hw hu ⟨B, σ, ⟨hirr, f, hf0, hfm, hf⟩, hS⟩
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS.1
  have hf' : ∀ g x, f (σ.ρ g x) = RU E a (GlobalTheory.SplitPts.locPt hw g).1 (f x) := fun g x => by
    have := hf (GlobalTheory.SplitPts.locPt hw g) x
    simpa [GlobalTheory.SplitPts.cLoc_locPt hw g] using this
  have hinj : Function.Injective f := by
    have hk := ((GlobalTheory.CuspRep.isIrreducible_iff _).1 hirr).2 (LinearMap.ker f) (fun g x hx => by
      rw [LinearMap.mem_ker] at hx ⊢
      rw [hf', hx, map_zero])
    rcases hk with h | h
    · exact LinearMap.ker_eq_bot.1 h
    · exact absurd (LinearMap.ker_eq_top.1 h) hf0
  have hloc : locU a u = locU a w := by
    unfold locU
    rw [hu]
  have hsu : IsSplitAt u := by
    by_cases h : u = w
    · exact h ▸ hw
    · exact ⟨w, Ne.symm h, hu.symm⟩
  have hKw : ∀ x : UA E a, cLoc u x ∈ GlobalTheory.LFun.KGL u (n := a) → cLoc w x ∈ GlobalTheory.LFun.KGL w (n := a) := by
    intro x hx
    rcases GlobalTheory.BCT.GlobLev.eq_or_eq_conjSrc hu with rfl | rfl
    · exact hx
    · have := GlobalTheory.BCT.GlobLev.integral_conjSrc x _ hx
      rwa [GlobalTheory.SplitPts.conjSrc_conjSrc_cm] at this
  have hfix : ∀ x ∈ locU a u, cLoc u x ∈ GlobalTheory.LFun.KGL u (n := a) → RU E a x (f v) = f v := by
    intro x hx hk
    have hx' : x ∈ locU a w := hloc ▸ hx
    have h1 : σ.ρ (cLoc w x) v = v := by simpa using hv ⟨_, hKw x hk⟩
    have h2 := hf ⟨x, hx'⟩ v
    rw [← h2]
    exact congrArg f h1
  obtain ⟨σ', S, hloc', hS', -⟩ := GlobalTheory.FrameAut.exists_locComp_hasSatGL_heckeVec E a U hU u hsu (f v) (hfm v)
    (fun h => hv0 (hinj (h.trans (map_zero f).symm))) hfix
  exact ⟨S, σ', hloc', hS'⟩

end GlobalTheory.CongL.SatConj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrobOpsIdx
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL GlobalTheory.CongL

noncomputable section

namespace GlobalTheory.FrobOpsIdx
open Polynomial

theorem frobOpsIdx : SphOps → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (Kw : Levels E a) (W0 : Set (HeightOneSpectrum (𝓞 E))), (∀ w ∈ W0, IsSplitAt w ∧ ((l : ℕ) : 𝓞 E) ∉ w.asIdeal ∧ Kw w = GlobalTheory.LFun.KGL w (n := a)) → ∃ (J : Type) (T : LocOps l ι Kw J) (x fr : J → G E Ω) (n : J → ℕ), (∀ j, x j = (fr j)⁻¹ ^ n j) ∧ (∀ j, T.pl j ∈ W0 ∧ ∃ A : ValuationSubring Ω, IsPlaceOver A (T.pl j) ∧ IsFrob A (normV (T.pl j)) (fr j)) ∧ (∀ w ∈ W0, ∀ A : ValuationSubring Ω, IsPlaceOver A w → ∀ s : G E Ω, IsFrob A (normV w) s → ∃ j, T.pl j = w ∧ fr j = s ∧ n j = 1) ∧ (∀ j g, ∃ q : ℚ, T.f j g = q) ∧ (∀ (j : J) (σ : SmIrr (GL (Fin a) ((T.pl j).adicCompletion E))), GlobalTheory.PRep.fixed σ.ρ (Kw (T.pl j)) ≠ ⊥ → ∀ B, GlobalTheory.LFun.HasSatGL (T.pl j) σ.ρ B → ∀ ρ : G E Ω →* GL (Fin a) (Qbar l), ((ρ (fr j)⁻¹ : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom = ((UpperTheory.V.Af.algSat a (normV (T.pl j)) B).map fun b => Polynomial.X - Polynomial.C b).prod → ι.symm (T.z j σ) = trc ρ (x j)) ∧ ∀ w ∈ W0, ∀ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), GlobalTheory.PRep.fixed σ.ρ (Kw w) ≠ ⊥ → ∀ B, GlobalTheory.LFun.HasSatGL w σ.ρ B → ∀ r : G E Ω →* GL (Fin a) (Qbar l), (∀ j (h : T.pl j = w), trc r (x j) = ι.symm (T.z j (h ▸ σ))) → ∀ A : ValuationSubring Ω, IsPlaceOver A w → ∀ s : G E Ω, IsFrob A (normV w) s → ((r s⁻¹ : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom = ((UpperTheory.V.Af.algSat a (normV w) B).map fun b => Polynomial.X - Polynomial.C b).prod := by
  intro hS E Ω _ _ _ _ _ _ l _ ι a Kw W0 hW
  classical
  have hl : l.Prime := Fact.out
  let J : Type := {p : HeightOneSpectrum (𝓞 E) × ValuationSubring Ω × G E Ω × ℕ //
    p.1 ∈ W0 ∧ IsPlaceOver p.2.1 p.1 ∧ IsFrob p.2.1 (normV p.1) p.2.2.1 ∧ 1 ≤ p.2.2.2}
  have hf : ∀ j : J, ∃ f : GL (Fin a) (j.1.1.adicCompletion E) →₀ ℂ,
      (∀ g, ∃ (m : ℤ) (e : ℕ), f g = (m : ℂ) / ((normV j.1.1 : ℕ) : ℂ) ^ e) ∧
      ∀ (σ : SmIrr (GL (Fin a) (j.1.1.adicCompletion E))) (B : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL j.1.1 σ.ρ B →
        ∀ v ∈ PRep.fixed σ.ρ (GlobalTheory.LFun.KGL j.1.1 (n := a)),
          opOf σ.ρ f v = ((UpperTheory.V.Af.algSat a (normV j.1.1) B).map (· ^ ((j.1.2.2.2 : ℕ) : ℤ))).sum • v :=
    fun j => (hS E j.1.1 a).2 (j.1.2.2.2 : ℤ)
  let zz : ∀ j : J, SmIrr (GL (Fin a) (j.1.1.adicCompletion E)) → ℂ := fun j σ =>
    if h : ∃ B, GlobalTheory.LFun.HasSatGL j.1.1 σ.ρ B then
      ((UpperTheory.V.Af.algSat a (normV j.1.1) h.choose).map (· ^ j.1.2.2.2)).sum else 0
  have hz : ∀ (j : J) (σ : SmIrr (GL (Fin a) (j.1.1.adicCompletion E))) (B : Multiset ℂˣ),
      GlobalTheory.LFun.HasSatGL j.1.1 σ.ρ B → zz j σ = ((UpperTheory.V.Af.algSat a (normV j.1.1) B).map (· ^ j.1.2.2.2)).sum := by
    intro j σ B hB
    have h : ∃ B, GlobalTheory.LFun.HasSatGL j.1.1 σ.ρ B := ⟨B, hB⟩
    simp only [zz, dif_pos h]
    rw [show h.choose = B from h.choose_spec.unique hB]
  let T : LocOps l ι Kw J :=
    { pl := fun j => j.1.1
      split := fun j => (hW _ j.2.1).1
      away := fun j => (hW _ j.2.1).2.1
      f := fun j => (hf j).choose
      int := fun j g => by
        obtain ⟨m, e, he⟩ := (hf j).choose_spec.1 g
        rw [he]
        exact GlobalTheory.FrobOps.norm_le_one ι m _ e (GlobalTheory.FrobOps.not_dvd_normV hl _ (hW _ j.2.1).2.1)
      z := zz
      act := fun j σ v hv => by
        rw [(hW _ j.2.1).2.2] at hv
        by_cases h : ∃ B, GlobalTheory.LFun.HasSatGL j.1.1 σ.ρ B
        · obtain ⟨B, hB⟩ := h
          rw [hz j σ B hB, (hf j).choose_spec.2 σ B hB v hv]
          simp only [zpow_natCast]
        · have h0 : PRep.fixed σ.ρ (GlobalTheory.LFun.KGL j.1.1 (n := a)) = ⊥ := by
            by_contra hne
            exact h ((hS E j.1.1 a).1 σ hne)
          rw [h0, Submodule.mem_bot] at hv
          subst hv
          simp [opOf] }
  let fr : J → G E Ω := fun j => j.1.2.2.1
  let nn : J → ℕ := fun j => j.1.2.2.2
  let x : J → G E Ω := fun j => (fr j)⁻¹ ^ nn j
  refine ⟨J, T, x, fr, nn, fun j => rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact ⟨j.2.1, j.1.2.1, j.2.2.1, j.2.2.2.1⟩
  · intro w hw A hA s hsF
    exact ⟨⟨(w, A, s, 1), hw, hA, hsF, le_rfl⟩, rfl, rfl, rfl⟩
  · intro j g
    obtain ⟨m, e, he⟩ := (hf j).choose_spec.1 g
    refine ⟨(m : ℚ) / ((normV j.1.1 : ℕ) : ℚ) ^ e, ?_⟩
    show (hf j).choose g = _
    rw [he]
    push_cast
    rfl
  · intro j σ _ B hB ρ hFE
    show ι.symm (zz j σ) = trc ρ (x j)
    rw [hz j σ B hB]
    apply ι.injective
    rw [RingEquiv.apply_symm_apply, GlobalTheory.FrobOps.iota_trc]
    exact (GlobalTheory.FrobOps.trace_pow_of_charpoly _ _ (by rw [Matrix.charpoly_map]; exact hFE) _).symm
  · intro w hw σ _ B hBσ r hr A hA s hsF
    rw [← Matrix.charpoly_map]
    refine GlobalTheory.CharpolyNewton.charpoly_eq_prod_of_trace_pow ℂ a _ _ ?_ ?_
    · simp [UpperTheory.V.Af.algSat, hBσ.card]
    · intro n hn
      let j : J := ⟨(w, A, s, n), hw, hA, hsF, hn⟩
      have h2 : trc r (x j) = ι.symm (zz j σ) := hr j rfl
      rw [hz j σ B hBσ] at h2
      rw [← GlobalTheory.FrobOps.iota_trc]
      change ι (trc r (x j)) = _
      rw [h2, RingEquiv.apply_symm_apply]

end GlobalTheory.FrobOpsIdx
end
end

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL GlobalTheory.CongL

namespace GlobalTheory.CongL.UnitLim

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem finite_not_sph (a : ℕ) (U : Submodule ℂ (UA E a → ℂ)) (hU : IsAutRepU U) :
    {w : HeightOneSpectrum (𝓞 E) | IsSplitAt w ∧ ¬ ∃ B, SatU U w B}.Finite := by
  obtain ⟨φ, hφ, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU.ne_bot
  let L : Subgroup (finU (E := E) (n := a)) :=
    { carrier := {k | RU E a k φ = φ}
      one_mem' := by simp
      mul_mem' := by
        intro x y hx hy
        simp only [Set.mem_setOf_eq] at *
        rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, hy, hx]
      inv_mem' := by
        intro x hx
        simp only [Set.mem_setOf_eq] at *
        conv_lhs => rw [← hx]
        rw [← Module.End.mul_apply, ← map_mul, Subgroup.coe_inv, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hLo : IsOpen (L : Set (finU (E := E) (n := a))) := (hU.aut φ hφ).level
  have hev : ∀ᶠ w in Filter.cofinite, IsSplitAt w → ∃ B, SatU U w B := by
    filter_upwards [GlobalTheory.BCT.GlobLev.eventually_locU_mem E a L hLo] with w hw hs
    obtain ⟨σ, B, hc, hB, -⟩ := GlobalTheory.FrameAut.exists_locComp_hasSatGL_heckeVec E a U hU w hs φ hφ hφ0
      fun x hx hxK => hw x hx hxK hx.1
    exact ⟨B, σ, hc, hB⟩
  exact (Filter.eventually_cofinite.1 hev).subset fun w hw h => hw.2 (h hw.1)

theorem dense_frob_usable_off (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (l : ℕ) (hl : l.Prime) (d : ℕ) (hd : ImQ E d) (X : Finset (HeightOneSpectrum (𝓞 E))) :
    Dense {g : G E Ω | ∃ w : HeightOneSpectrum (𝓞 E), w ∉ X ∧ UsPl d w ∧ ((l : ℕ) : 𝓞 E) ∉ w.asIdeal ∧ ApartAll X w ∧
      ∃ A : ValuationSubring Ω, IsPlaceOver A w ∧ IsFrob A (normV w) g} := by
  classical
  set M : ℕ := l * (2 * d) * ∏ u ∈ X, Ideal.absNorm u.asIdeal with hM
  have hM0 : M ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero hl.ne_zero (mul_ne_zero two_ne_zero hd.1.ne')) ?_
    rw [Finset.prod_ne_zero_iff]
    intro u _
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact u.ne_bot
  have hS1 : {w : HeightOneSpectrum (𝓞 E) | w.asIdeal ∣ Ideal.span {((M : ℕ) : 𝓞 E)}}.Finite := by
    refine Ideal.finite_factors ?_
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hM0
  have hS3 := (GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified E).2
  set S := {w : HeightOneSpectrum (𝓞 E) | w.asIdeal ∣ Ideal.span {((M : ℕ) : 𝓞 E)}} ∪
    {P : HeightOneSpectrum (𝓞 E) | P.asIdeal.ramificationIdx ℤ ≠ 1} with hSdef
  have hS : S.Finite := hS1.union hS3
  have hdense := GlobalTheory.Published.chebotarevDegreeOne'.dense (F := E) (Ω := Ω) hS
  refine hdense.mono ?_
  rintro g ⟨w, hwS, hdeg, A, hA, hg⟩
  simp only [hSdef, Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hwS
  obtain ⟨hM', hram⟩ := hwS
  have hMw : ((M : ℕ) : 𝓞 E) ∉ w.asIdeal := fun h => hM' (Ideal.dvd_span_singleton.2 h)
  have hp := ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified E).1 w).2 hdeg
  have hX : ∀ u ∈ X, ((Ideal.absNorm u.asIdeal : ℕ) : 𝓞 E) ∉ w.asIdeal := fun u hu h =>
    hMw (GlobalTheory.DenseUsable.natCast_mem_of_dvd w (Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ hu) _) h)
  refine ⟨w, fun hwX => hX w hwX (Ideal.absNorm_mem _), ?_, ?_, ?_, A, hA, hg⟩
  · refine GlobalTheory.DenseUsable.usPl_of_absNorm_prime hd w hp hram fun h => hMw ?_
    exact GlobalTheory.DenseUsable.natCast_mem_of_dvd w (Dvd.dvd.mul_right (dvd_mul_left _ _) _) h
  · exact fun h => hMw (GlobalTheory.DenseUsable.natCast_mem_of_dvd w (Dvd.dvd.mul_right (dvd_mul_right _ _) _) h)
  · intro u hu hwu
    exact hX u hu (GlobalTheory.DenseUsable.absNorm_mem_of_under_eq w u hwu)

end GlobalTheory.CongL.UnitLim
end
