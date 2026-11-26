module

public import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmVacuumEqSplitFacSmulSum
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsAlgebraicIndependentGenericPoint
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenMapTranspose
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricDenominatorOfZetaDenominators
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthonormalFrameReadingEqConjugateDatumTheta
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilActionTranslatesThetaByUnitScalar
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LatOEqHatA
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeisenbergOrientedFiniteFixesFockPolynomialVecto

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCartanInvOneSplitStab
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh

noncomputable section

theorem mt_mul_splitStab {D : D7} (V : HSp D) (g h : GA D V) : Formalism.L2.Theta.mt V (g * h) = Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V h := by
  unfold Formalism.L2.Theta.mt
  rw [map_mul, Units.val_mul]

theorem mt_one_splitStab {D : D7} (V : HSp D) : Formalism.L2.Theta.mt V 1 = 1 := by
  unfold Formalism.L2.Theta.mt
  rw [map_one, Units.val_one]

theorem idem_unit_splitStab {R : Type} [CommRing R] {e d d' : R} (he : e * e = e) (h : d' * d = 1) :
    (e * d + (1 - e)) * (e * d' + (1 - e)) = 1 := by
  linear_combination (e * e) * h + (2 - d - d') * he

theorem exists_isDetAt_splitStab {D : D7} {e : AE D} (he : e * e = e) (V : HSp D) (g : GA D V) : ∃ y, IsDetAt e V g y :=
  ⟨Units.mkOfMulEqOne _ _ (idem_unit_splitStab he (det_conj_mul V g)), Units.val_mkOfMulEqOne _⟩

open scoped ComplexOrder in
theorem isCartanInv_one_splitStab (k : ℕ) : IsCartanInv (1 : Matrix (Fin k) (Fin k) ℂ) 1 := by
  refine ⟨by simp, by simp, ?_⟩
  rw [Matrix.mul_one]
  exact Matrix.PosDef.one

theorem heisO_zero_splitStab {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (f : WO V W → ℂ) : heisO ψ V W 0 f = f := by
  funext w
  simp [heisO, symplOH, symplO, hO]

theorem om_vacuum_split_stab : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsPair ψ θ V W χV χW om → ∀ mu : GA D W → ℂ, Formalism.L2.Pj.MuVal W χV mu → ∀ (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)), IsSelfDualC V ΛV → IsSelfDualC W ΛW → ∀ (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ), (∀ τ, IsCartanInv (gramAt D W τ) (s τ)) → ∀ f, IsVacO ψ θ V W (fun _ => 1) s (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) f → ∀ (e : AE D) (k : GA D W), IsSplitIdem D e → SuppAt e W k → (∀ u, u ∈ (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True) ↔ actO V W 1 k u ∈ (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True)) → om (1, k) f = mu k • f := by
  intro D ψ θ V W χV χW om hP mu hmu ΛV ΛW hV hW s hs f hf e k he hk hst
  obtain ⟨y, hy⟩ := exists_isDetAt_splitStab he.1 W k
  have h1 : ∀ τ, IsCartanInv (gramAt D V τ) ((fun _ => 1 : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) τ) := by
    intro τ
    have : gramAt D V τ = 1 := by
      unfold gramAt
      rw [hP.std]
      simp
    rw [this]
    exact isCartanInv_one_splitStab _
  have hs1 : SuppAt e V 1 := by
    intro i j
    rw [mt_one_splitStab, sub_self, Matrix.zero_apply, mul_zero]
  have hx : IsDetAt e V 1 1 := by
    unfold IsDetAt
    rw [mt_one_splitStab, Matrix.det_one, Units.val_one]
    ring
  have hact : ∀ u, actO V W 1 k (actO V W 1 k⁻¹ u) = u := by
    intro u
    unfold actO
    rw [inv_one, mt_one_splitStab, Matrix.mul_one, Matrix.mul_one, ← Matrix.mul_assoc, ← mt_mul_splitStab,
      mul_inv_cancel, mt_one_splitStab, Matrix.one_mul]
  have key := GlobalTheory.SplitScalar.om_vacuum_eq_splitFac_smul_sum D ψ θ V W χV χW om hP.weil hP.inf hP.sigV hP.sigW
    (fun _ => 1) s h1 hs ΛV ΛV ΛW ΛW hV hV hW hW e he 1 k hs1 hk 1 y hx hy
    (fun u => ⟨fun hu => ⟨actO V W 1 k⁻¹ u, (hst _).2 (by rw [hact]; exact hu), (hact u).symm⟩,
      fun ⟨u₀, hu₀, h⟩ => h ▸ (hst u₀).1 hu₀⟩)
    {0} {0}
    (fun u hu => by
      rw [Finset.mem_singleton.1 hu]
      exact ⟨zero_mem _, fun i j => mul_zero _⟩)
    (fun u hu _ => ⟨0, ⟨Finset.mem_singleton_self _, by rwa [sub_zero]⟩, fun v hv => Finset.mem_singleton.1 hv.1⟩)
    (fun u hu => by
      rw [Finset.mem_singleton.1 hu]
      exact ⟨zero_mem _, fun i j => mul_zero _⟩)
    (fun u hu _ => ⟨0, ⟨Finset.mem_singleton_self _, by rwa [sub_zero]⟩, fun v hv => Finset.mem_singleton.1 hv.1⟩)
    f hf
  have hr : IsDetRoot W k y := isDetAt_root he W k hk y hy
  rw [key, hmu.2 k y hr]
  simp [heisO_zero_splitStab, splitFacO]

end

end GlobalTheory.AdTh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarRowsLevelCharacterEqLiftsLevelCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarRowsLevelCharacterEqLiftsLevelCharacter
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

noncomputable section

namespace GlobalTheory.ChiStarLev

variable {D : D7}

section Level

variable {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank}

theorem levChi_flag' (hs : L.s = 0) (hQ : L.Q = ∅) (κ : GA D V) : levChi V β (flagL L) κ = 1 := by
  have h2 : ext1 (flagL L).P.H (flagL L).P.chi (rTup β (flagL L) (finE V κ)) = 1 := subgroupCharExtension_one_apply _ _
  unfold levChi levFn
  rw [h2]
  simp [flagL, withP, hs, hQ]

theorem levChi_withP' (hs : L.s = 0) (hQ : L.Q = ∅) (P : LevelP L.Pg L.r ℂ) (κ : GA D V) :
    levChi V β (withP L P) κ = ((ext1 P.H P.chi (rTup β L (finE V κ)) : ℂˣ) : ℂ) := by
  have h := levChi_flag' (β := β) hs hQ κ
  unfold levChi at h ⊢
  rw [levFn_withP, Units.val_mul, h, mul_one]

end Level

theorem ext_by_one_apply_of_not_mem_subgroup {G N : Type} [Group G] [One N] [Mul N] {P : Subgroup G} (f : P → N) {x : G} (h : x ∉ P) :
    ext1 P f x = 1 := by
  unfold ext1; rw [dite_eq_right h]

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem star_levChi_levR (R : RealDat D A Ks) (F : Face D A) (b : Bool) (g : GA D (Yc D 0)) :
    star (levChi _ (R.βY 0) (R.dat0 (R.levR F b)) g) = levChi _ (R.βY 0) (R.dat0 (R.levL F b (sg0 D A))) g := by
  have hsg : sg0 D A = D.what₂.embLL := sgAt_mk _ R.hv0
  rw [hsg]
  have h1 := levChi_withP' (β := R.βY 0) (L := R.dat0 R.triv) rfl rfl (R.levL F b D.what₂.embLL) g
  have h2 := levChi_withP' (β := R.βY 0) (L := R.dat0 R.triv) rfl rfl (R.levR F b) g
  have hH : (R.levL F b D.what₂.embLL).H = (R.levR F b).H := rfl
  by_cases hm : rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) g) ∈ (R.levR F b).H
  · replace h2 := h2.trans (congrArg Units.val (extendOne_of_mem (P := (R.levR F b).H) (R.levR F b).chi hm))
    replace h1 := h1.trans (congrArg Units.val (extendOne_of_mem (P := (R.levL F b D.what₂.embLL).H) (R.levL F b D.what₂.embLL).chi hm))
    refine Eq.trans (congrArg star h2) (Eq.trans ?_ h1.symm)
    have h3 : (R.levL F b D.what₂.embLL).chi ⟨_, hm⟩ = ((R.levR F b).chi ⟨_, hm⟩)⁻¹ := by
      exact map_inv (Units.map D.what₂.embLL.toMonoidHom) _
    have h4 : IsOfFinOrder ((R.levR F b).chi ⟨_, hm⟩) := by
      have : Finite (G0 R.Pg D.R.r) := Finite.of_equiv _ R.eG.toEquiv
      exact MonoidHom.isOfFinOrder _ (isOfFinOrder_of_finite _)
    have h5 : ‖(((R.levR F b).chi ⟨_, hm⟩ : ℂˣ) : ℂ)‖ = 1 := ((Units.coeHom ℂ).isOfFinOrder h4).norm_eq_one
    rw [h3, Units.val_inv_eq_inv_val, Complex.inv_eq_conj h5]
    rfl
  · have hm' : rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) g) ∉ (R.levL F b D.what₂.embLL).H := hm
    replace h2 := h2.trans (congrArg Units.val (ext_by_one_apply_of_not_mem_subgroup (P := (R.levR F b).H) (R.levR F b).chi hm))
    replace h1 := h1.trans (congrArg Units.val (ext_by_one_apply_of_not_mem_subgroup (P := (R.levL F b D.what₂.embLL).H) (R.levL F b D.what₂.embLL).chi hm'))
    refine Eq.trans (congrArg star h2) (Eq.trans ?_ h1.symm)
    simp

end GlobalTheory.ChiStarLev
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarRowsLevelCharacterEqLiftsLevelCharacterStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.star_rows_level_character_eq_lifts_level_character : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (b : Bool) (g : GA D (Yc D 0)), star (levChi _ (R.βY 0) (R.dat0 (R.levR F b)) g) = levChi _ (R.βY 0) (R.dat0 (R.levL F b (sg0 D A))) g := by
  first | exact @GlobalTheory.ChiStarLev.star_levChi_levR | exact GlobalTheory.ChiStarLev.star_levChi_levR | (intros; apply GlobalTheory.ChiStarLev.star_levChi_levR <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealQuotientHilbertPolyConeIdealEqFieldDegree
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealQuotientHilbertPolyConeIdealEqFieldDegree
open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal

namespace GlobalTheory.CompHt

theorem finrank_quotPiece_coneIdeal_eq_finrank_map {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
    {N : ℕ} (y : Fin N → Ω) (n : ℕ) :
    Module.finrank K (quotPiece (coneIdeal K y) n) =
      Module.finrank K ((homogeneousSubmodule (Fin N) K n).map
        (aeval y : MvPolynomial (Fin N) K →ₐ[K] Ω).toLinearMap) := by
  have e1 := finrank_quotPiece_add (coneIdeal K y) n
  have e2 := GradedHilbert.finrank_map_add_finrank_inf_ker
    (aeval y : MvPolynomial (Fin N) K →ₐ[K] Ω).toLinearMap (homogeneousSubmodule (Fin N) K n)
  have e3 : ((coneIdeal K y).restrictScalars K ⊓ homogeneousSubmodule (Fin N) K n : Submodule K _)
      = homogeneousSubmodule (Fin N) K n ⊓
        LinearMap.ker (aeval y : MvPolynomial (Fin N) K →ₐ[K] Ω).toLinearMap := by
    ext g
    simp only [Submodule.mem_inf, Submodule.restrictScalars_mem, mem_homogeneousSubmodule,
      LinearMap.mem_ker, AlgHom.toLinearMap_apply]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h2, (mem_coneIdeal_of_isHomogeneous y h2).1 h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨(mem_coneIdeal_of_isHomogeneous y h1).2 h2, h1⟩
  rw [e3] at e1
  omega

theorem aeval_mem_map_homogeneousSubmodule {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
    {N : ℕ} (y : Fin N → Ω) {j : Fin N} (hj : y j = 1) (g : MvPolynomial (Fin N) K) {n : ℕ}
    (hn : g.totalDegree ≤ n) :
    aeval y g ∈ (homogeneousSubmodule (Fin N) K n).map
        (aeval y : MvPolynomial (Fin N) K →ₐ[K] Ω).toLinearMap := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← sum_homogeneousComponent g, map_sum]
  refine Submodule.sum_mem _ fun i hi => ?_
  have hi' : i ≤ n := by
    have := Finset.mem_range.1 hi
    omega
  refine ⟨homogeneousComponent i g * X j ^ (n - i), ?_, by simp [hj]⟩
  have := (homogeneousComponent_isHomogeneous i g).mul ((isHomogeneous_X K j).pow (n - i))
  rw [one_mul, Nat.add_sub_cancel' hi'] at this
  exact this

theorem idealHilbertPoly_coneIdeal_eq_C_finrank_adjoin (K : Type) [Field K] (N : ℕ)
    (y : Fin N → AlgebraicClosure K) (j : Fin N) (hj : y j = 1) :
    GlobalTheory.idealHilbertPoly (coneIdeal K y) =
      Polynomial.C (Module.finrank K (IntermediateField.adjoin K (Set.range y)) : ℚ) := by
  have halg : ∀ x ∈ Set.range y, IsAlgebraic K x := fun x _ => Algebra.IsAlgebraic.isAlgebraic x
  haveI : FiniteDimensional K (IntermediateField.adjoin K (Set.range y)) :=
    IntermediateField.finiteDimensional_adjoin fun x hx => (halg x hx).isIntegral
  set S : Submodule K (AlgebraicClosure K) :=
    Subalgebra.toSubmodule (IntermediateField.adjoin K (Set.range y)).toSubalgebra with hS
  have hmem : ∀ x, x ∈ S ↔ ∃ g : MvPolynomial (Fin N) K, aeval y g = x := by
    intro x
    rw [hS, IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halg, Subalgebra.mem_toSubmodule,
      Algebra.adjoin_range_eq_range_aeval]
    rfl
  have hfin : Module.Finite K S := ‹FiniteDimensional K (IntermediateField.adjoin K (Set.range y))›
  obtain ⟨s, hs⟩ := Module.Finite.iff_fg.1 hfin
  have hev : ∀ᶠ n : ℕ in atTop, ∀ x ∈ s, x ∈ (homogeneousSubmodule (Fin N) K n).map
      (aeval y : MvPolynomial (Fin N) K →ₐ[K] AlgebraicClosure K).toLinearMap := by
    rw [eventually_all_finset]
    intro x hx
    obtain ⟨g, rfl⟩ := (hmem x).1 (hs ▸ Submodule.subset_span hx)
    filter_upwards [eventually_ge_atTop g.totalDegree] with n hn
    exact aeval_mem_map_homogeneousSubmodule y hj g hn
  apply polynomial_eq_of_eventually_eval_nat
  filter_upwards [eventually_finrank_quotPiece (isHomogeneous_coneIdeal (K := K) y), hev]
    with n h1 h2
  have hW : (homogeneousSubmodule (Fin N) K n).map
      (aeval y : MvPolynomial (Fin N) K →ₐ[K] AlgebraicClosure K).toLinearMap = S := by
    apply le_antisymm
    · rintro _ ⟨g, -, rfl⟩
      exact (hmem _).2 ⟨g, rfl⟩
    · rw [← hs, Submodule.span_le]
      exact fun x hx => h2 x hx
  rw [← h1, finrank_quotPiece_coneIdeal_eq_finrank_map, hW, Polynomial.eval_C]
  rfl

end GlobalTheory.CompHt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealQuotientHilbertPolyConeIdealEqFieldDegreeStatement
open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idealQuotientHilbertPoly_coneIdeal_eq_field_degree : ∀ (K : Type) [Field K] (N : ℕ) (y : Fin N → AlgebraicClosure K) (j : Fin N), y j = 1 → GlobalTheory.idealHilbertPoly (coneIdeal K y) = Polynomial.C (Module.finrank K (IntermediateField.adjoin K (Set.range y)) : ℚ) := by
  first | exact @GlobalTheory.CompHt.idealHilbertPoly_coneIdeal_eq_C_finrank_adjoin | exact GlobalTheory.CompHt.idealHilbertPoly_coneIdeal_eq_C_finrank_adjoin | (intros; apply GlobalTheory.CompHt.idealHilbertPoly_coneIdeal_eq_C_finrank_adjoin <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVariableMultiplicationMemSpanHeisenbergOpera
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVariableMultiplicationMemSpanHeisenbergOpera
open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.MulVarSpan

variable {P Q R S : ℕ}

theorem heisOp_single (l : Ln P Q R S) (a : ℂ) :
    heisOp (Matrix.single l.1 l.2 a) = ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) •
      (a • raiB l - (lineSign (p := P) (q := Q) (r := R) (s := S) l.1 l.2 * star a) • lowB l) := by
  unfold heisOp
  congr 1
  rw [Finset.sum_eq_single l]
  · simp [Matrix.single_apply]
  · intro l' _ hne
    have h : ¬ (l.1 = l'.1 ∧ l.2 = l'.2) := by
      rintro ⟨h1, h2⟩; exact hne (Prod.ext h1.symm h2.symm)
    simp [Matrix.single_apply, h]
  · intro h; exact absurd (Finset.mem_univ l) h

theorem sq_ne (l : Ln P Q R S) : ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) ≠ 0 := by
  have : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  exact_mod_cast this.ne'

theorem lineSign_sq (a : Ix P Q) (b : Ix R S) : lineSign a b * lineSign a b = 1 := by
  cases a <;> cases b <;> simp [lineSign]

theorem raiB_mem (l : Ln P Q R S) :
    raiB l ∈ Submodule.span ℂ (Set.range (heisOp (P := P) (Q := Q) (R := R) (S := S))) := by
  set s : ℂ := ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ)
  have key : (2 * s) • raiB l = heisOp (Matrix.single l.1 l.2 1) - Complex.I • heisOp (Matrix.single l.1 l.2 Complex.I) := by
    rw [heisOp_single, heisOp_single]
    simp only [star_one, Complex.star_def, Complex.conj_I, one_smul, mul_one]
    generalize raiB l = A
    generalize lowB l = B
    generalize lineSign (p := P) (q := Q) (r := R) (s := S) l.1 l.2 = σ
    simp only [smul_sub, smul_smul]
    have hI : Complex.I * (s * Complex.I) = -s := by ring_nf; simp [Complex.I_sq]
    have hI2 : Complex.I * (s * (σ * -Complex.I)) = s * σ := by ring_nf; simp [Complex.I_sq]
    rw [hI, hI2]
    module
  have hs : (2 * s) ≠ 0 := mul_ne_zero two_ne_zero (sq_ne l)
  have : raiB l = (2 * s)⁻¹ • (heisOp (Matrix.single l.1 l.2 1) - Complex.I • heisOp (Matrix.single l.1 l.2 Complex.I)) := by
    rw [← key, inv_smul_smul₀ hs]
  rw [this]
  exact Submodule.smul_mem _ _ (sub_mem (Submodule.subset_span ⟨_, rfl⟩)
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)))

theorem lowB_mem (l : Ln P Q R S) :
    lowB l ∈ Submodule.span ℂ (Set.range (heisOp (P := P) (Q := Q) (R := R) (S := S))) := by
  set s : ℂ := ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ)
  set σ := lineSign (p := P) (q := Q) (r := R) (s := S) l.1 l.2 with hσ
  have hσσ : σ * σ = 1 := lineSign_sq l.1 l.2
  have key : (-2 * s * σ) • lowB l = heisOp (Matrix.single l.1 l.2 1) + Complex.I • heisOp (Matrix.single l.1 l.2 Complex.I) := by
    rw [heisOp_single, heisOp_single, ← hσ]
    simp only [star_one, Complex.star_def, Complex.conj_I, one_smul, mul_one]
    generalize raiB l = A
    generalize lowB l = B
    simp only [smul_sub, smul_smul]
    have hI : Complex.I * (s * Complex.I) = -s := by ring_nf; simp [Complex.I_sq]
    have hI2 : Complex.I * (s * (σ * -Complex.I)) = s * σ := by ring_nf; simp [Complex.I_sq]
    rw [hI, hI2]
    module
  have hs : (-2 * s * σ) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (by norm_num) (sq_ne l)) ?_
    intro h; rw [h, zero_mul] at hσσ; exact zero_ne_one hσσ
  have : lowB l = (-2 * s * σ)⁻¹ • (heisOp (Matrix.single l.1 l.2 1) + Complex.I • heisOp (Matrix.single l.1 l.2 Complex.I)) := by
    rw [← key, inv_smul_smul₀ hs]
  rw [this]
  exact Submodule.smul_mem _ _ (add_mem (Submodule.subset_span ⟨_, rfl⟩)
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)))

theorem mulX_mem_span : ∀ {P Q R S : ℕ} (l : Ln P Q R S), LinearMap.mulLeft ℂ (MvPolynomial.X l : Formalism.BasicNotions.TH.Pol P Q R S) ∈
    Submodule.span ℂ (Set.range (heisOp (P := P) (Q := Q) (R := R) (S := S))) := by
  intro P Q R S l
  cases h : linePos l
  · have e : LinearMap.mulLeft ℂ (MvPolynomial.X l : Formalism.BasicNotions.TH.Pol P Q R S) = lowB l := by simp [lowB, h]
    rw [e]; exact lowB_mem l
  · have e : LinearMap.mulLeft ℂ (MvPolynomial.X l : Formalism.BasicNotions.TH.Pol P Q R S) = raiB l := by simp [raiB, h]
    rw [e]; exact raiB_mem l

end GlobalTheory.MulVarSpan
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVariableMultiplicationMemSpanHeisenbergOperaStatement
open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockVariableMultiplication_mem_span_heisenbergOperators : ∀ {P Q R S : ℕ} (l : Ln P Q R S), LinearMap.mulLeft ℂ (MvPolynomial.X l : Formalism.BasicNotions.TH.Pol P Q R S) ∈ Submodule.span ℂ (Set.range (heisOp (P := P) (Q := Q) (R := R) (S := S))) := by
  first | exact @GlobalTheory.MulVarSpan.mulX_mem_span | exact GlobalTheory.MulVarSpan.mulX_mem_span | (intros; apply GlobalTheory.MulVarSpan.mulX_mem_span <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicVacuumReadsMultipleClassicalVacuum
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicVacuumReadsMultipleClassicalVacuum
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.VacLine

theorem hostHalfRoot_add_conj_eq_one {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) :
    (H.w0 : E) + cc (H.w0 : E) = 1 := by
  have := congrArg (algebraMap (𝓞 E) E) (PullbackSections.CVA.cmHostUnit_add_conj_eq_one H)
  rw [map_add (f := _), map_one] at this
  exact (congrArg _ (H.bar_eq _).symm).trans this

theorem isRelTraceOneIdempotentModTwo_hostElement {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) :
    GlobalTheory.Ker.IdemTwo (H.w0 : E) := by
  obtain ⟨k, hk⟩ : ∃ k, H.d = 16 * k + 7 := ⟨H.d / 16, by have := H.d_mod; omega⟩
  have h1 := hostHalfRoot_add_conj_eq_one H
  have h2 : 2 * (H.w0 : E) = 1 + (H.rt : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.two_weight_eq_one_add_root
    rwa [map_mul, map_add, map_one, map_ofNat] at this
  have h3 : (H.rt : E) ^ 2 = -(16 * k + 7) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    rw [map_pow, map_neg, map_natCast, hk] at this
    exact this.trans (by push_cast; rfl)
  refine ⟨((2 * k + 1 : ℕ) : E), isIntegral_natCast _, ?_⟩
  rw [eq_sub_of_add_eq' h1]
  push_cast
  linear_combination (-(1 / 4 : E)) * h3 - (1 / 4 : E) * (2 * (H.w0 : E) - 1 + (H.rt : E)) * h2

theorem isAA_aMul {D : D7} {n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) :
    GlobalTheory.Ker.IsAA (LatOf.aMul Λ) Λ := by
  intro v
  constructor
  · intro h
    exact LatOf.aMul_induction (p := fun v => v ∈ AddSubgroup.closure
      {u | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ t ∈ Λ, u = a • t})
      (fun a ha t ht => AddSubgroup.subset_closure ⟨a, ha, t, ht, rfl⟩) (zero_mem _) (fun _ _ => add_mem) h
  · intro h
    exact (AddSubgroup.closure_le (LatOf.aMul Λ).toAddSubgroup).2 Submodule.subset_span h

theorem vac_reads : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsStdChar D ψ (-1) → IsInfFam θ → V.gram = 1 → Even V.rank → IsMod W hr X → IsSympl X bas → ∀ (H : Geo.Tor.Host D.host.E), (H.rt : D.host.E) = D.host.sqrtMinusD → ∀ (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (Λ' : Lt D.host.E V.rank) (L : Lt D.host.E r), V.SigOK → W.SigOK → IsSelfDualC V ΛV → IsSelfDualC W ΛW → (∀ v : Fin V.rank → D.host.E, v ∈ Λ' ↔ (fun j => star (v j)) ∈ ΛV) → (∀ L₀ : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E), L₀ = Submodule.span (𝓞 D.host.E) {w | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ v ∈ ΛW, w = a • v} → L = latR hr L₀) → ∀ (x : Frame X.Ψ r) (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ), IsONFr X x → IsInvOf W hr X x s → ∀ f, IsVacO ψ θ V W (fun _ => 1) s (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) f → ∀ v : TF V.rank g, IsVac X bas (H.w0 : D.host.E) (tens Λ' L) v → ∃ κ : ℂ, κ ≠ 0 ∧ Reads θ V W hr X bas idx f (κ • v) x := by
  intro D ψ θ V W r g hr X bas idx hψ hθ hV he hX hs H _ ΛV ΛW Λ' L _ _ hΛV hΛW hΛ' hL x s hx hsx f hf v hv
  obtain ⟨-, hsd, hU, hfg⟩ := LatOf.isLatOf_tens D ψ θ V W r g hr X bas idx hψ hθ hV he hX hs ΛV ΛW Λ' L hΛV hΛW hΛ' hL
  subst hr
  have hL' : L = LatOf.aMul ΛW := by
    rw [hL (LatOf.aMul ΛW) rfl]
    exact Submodule.map_id _
  subst hL'
  obtain ⟨X', m, hq', hq, bas', idx', hs', -, -, hEF, hh, -, -, hfr⟩ :=
    GlobalTheory.T.orthonormal_frame_reading_eq_conjugate_datum_theta D ψ θ V W g X bas idx hψ hθ he hV hX hs
  obtain ⟨⟨B, hB⟩, hall⟩ := hfr x hx
  obtain ⟨hIB, -, hsB, -, -, -, -, -, hrd⟩ := hall B hB
  set C : GlobalTheory.Ker.Ctx V W := ⟨ψ, hψ, θ, hθ, X', m, g, X.p0, hq', bas', idx', hs', he⟩ with hC
  obtain rfl := hsB s hsx
  have hsd' : SelfD C.X (LatOf.aMul ΛW) := by
    refine ⟨hsd.1, fun u => (hsd.2 u).trans ?_⟩
    change _ ↔ ∀ y ∈ LatOf.aMul ΛW, ∃ k : ℤ, EF X' u y = k
    simp only [hEF]
  have hv' : IsVac C.X C.bas (H.w0 : D.host.E) (tens Λ' (LatOf.aMul ΛW)) v := by
    refine ⟨hv.1, hv.2.1, fun y hy => ?_⟩
    change epsW X' _ y • heisG X' bas' y v = v
    have e : epsW X' (H.w0 : D.host.E) y = epsW X (H.w0 : D.host.E) y := by simp only [epsW, hEF]
    rw [e, hh]
    exact hv.2.2 y hy
  have hlat := hf.2.lat
  rw [GlobalTheory.Ker.LatTens.latO_eq_hatA D V W C ΛV Λ' ΛW _ hΛ' (isAA_aMul ΛW)] at hlat
  obtain ⟨t, ht⟩ := (GlobalTheory.Ker.latVac_th_line D V W C _ H.w0.isIntegral_coe (hostHalfRoot_add_conj_eq_one H) (isRelTraceOneIdempotentModTwo_hostElement H) 1 Λ'
    (VacProj.mem_vset ⟨Λ'⟩ hU hfg) _ hsd').2 B hIB v hv' f hf.2.theta hf.2.fock hlat
  refine ⟨t, ?_, ((hrd f (t • v) (TensVac.sb_smul _ hv.1)).2 ?_).2⟩
  · rintro rfl
    rw [zero_smul] at ht
    subst ht
    obtain ⟨⟨p, hp⟩, hn⟩ := hf.2.norm
    have := hn p hp
    simp [nrm2] at this
  · rw [(GlobalTheory.T.thetaKernel_testFunction_map_linear_injective_equivariant D V W C _ ((GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear D V W C).2 B hIB).2.1 v hv.1).2.1]
    exact ht

end GlobalTheory.AdTh.VacLine
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicVacuumReadsMultipleClassicalVacuumStatement
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicVacuum_reads_multiple_classicalVacuum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsStdChar D ψ (-1) → IsInfFam θ → V.gram = 1 → Even V.rank → IsMod W hr X → IsSympl X bas → ∀ (H : Geo.Tor.Host D.host.E), (H.rt : D.host.E) = D.host.sqrtMinusD → ∀ (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (Λ' : Lt D.host.E V.rank) (L : Lt D.host.E r), V.SigOK → W.SigOK → IsSelfDualC V ΛV → IsSelfDualC W ΛW → (∀ v : Fin V.rank → D.host.E, v ∈ Λ' ↔ (fun j => star (v j)) ∈ ΛV) → (∀ L₀ : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E), L₀ = Submodule.span (𝓞 D.host.E) {w | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ v ∈ ΛW, w = a • v} → L = latR hr L₀) → ∀ (x : Frame X.Ψ r) (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ), IsONFr X x → IsInvOf W hr X x s → ∀ f, IsVacO ψ θ V W (fun _ => 1) s (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) f → ∀ v : TF V.rank g, IsVac X bas (H.w0 : D.host.E) (tens Λ' L) v → ∃ κ : ℂ, κ ≠ 0 ∧ Reads θ V W hr X bas idx f (κ • v) x := by
  first | exact @GlobalTheory.AdTh.VacLine.vac_reads | exact GlobalTheory.AdTh.VacLine.vac_reads | (intros; apply GlobalTheory.AdTh.VacLine.vac_reads <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelRowsEqTop
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelRowsEqTop
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

noncomputable section

namespace GlobalTheory.PrincipalRows

theorem theta_adjoint_mem {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)
    (cv : CrdV A) (hKR : X.KFormR) (hJR : X.JIsoR cv) (hRT : Formalism.IndefR.Rat.RowTest X) (t : Bs.Tup) (S : Submodule ℂ X.EE)
    (hZ : ∀ z ∈ X.Z t, X.Θ t (X.jR t z) ∈ S) (e : X.EE) : X.Θ t (LinearMap.adjoint (X.Θ t) e) ∈ S := by
  obtain ⟨N, ψ, hψ, hr⟩ := hRT
  have hspan : Submodule.span ℂ ((X.jR t) '' (X.Z t : Set (A.FR t))) = LinearMap.range (LinearMap.adjoint (X.Θ t)) :=
    Formalism.IndefR.Rat.range_adjoint_rat Bs.v0.embedding (X.jR t) (cv.hR t) (CxData.bR t) (hKR t).1 (hKR t).2 (hJR t) (X.Θ t) ψ hψ
      (fun i x => hr t i x)
  have hsub : LinearMap.range (LinearMap.adjoint (X.Θ t)) ≤ S.comap (X.Θ t) := by
    rw [← hspan, Submodule.span_le]
    rintro _ ⟨z, hz, rfl⟩
    exact hZ z hz
  exact hsub ⟨e, rfl⟩

end GlobalTheory.PrincipalRows

namespace GlobalTheory.PrincipalRows

theorem mem_range_toF_full {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
    (B : BlockDat K G Pl0) (Xc : Finset (G → K)) (Z : Submodule K B.S.Forms) (z : B.S.Forms) (hz : z ∈ Z)
    (hg : z ∈ B.goodF Xc) : z ∈ LinearMap.range (B.toF ⟨Xc, ⊥, 1⟩ Z) := by
  rw [GlobalTheory.OneForm.range_toF]
  refine ⟨hz, ?_⟩
  obtain ⟨w, hw⟩ := hg
  refine ⟨w, ?_⟩
  rw [← hw, Formalism.L2.DIV.CSD.gaOp, GlobalTheory.OneForm.asAlg_eq_sum, LinearMap.sum_apply]
  rfl

theorem theta_base_forms_mem_principal_good_part {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type}
    {m : ℕ} (A3 : FamIn3 K G Pl0 I0 Ty T m) (X : CxData A3.fam3.amb3) {P1 : Subgroup G} {ψ1 : P1 →* Kˣ}
    {Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)} {Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs)}
    {Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3} (hIB : X.zs.InBlock) :
    ∀ z ∈ X.Z A3.A.fam.μ0, X.Θ A3.A.fam.μ0 (X.jR A3.A.fam.μ0 z) ∈
      EEg3 A3 X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) := by
  intro z hz
  have h1 : z ∈ (A3.A.fam.R A3.A.fam.μ0).ZHg A3.A.fam.X := hIB.1 A3.A.fam.μ0 hz
  obtain ⟨x, hx⟩ := mem_range_toF_full (A3.A.fam.R A3.A.fam.μ0) A3.A.fam.X (X.zs.Z A3.A.fam.μ0) z hz h1.2
  refine ⟨cpt A3.A.v0.embedding x, ?_⟩
  have h3 := GlobalTheory.OneForm.iC_cpt X (crdOf3 A3 ⊥ 1 P1 ψ1 Dc Sp Zsc) false A3.A.fam.μ0 x
  refine h3.trans ?_
  exact congrArg (fun y => X.Θ A3.A.fam.μ0 (X.jR A3.A.fam.μ0 y)) hx

end GlobalTheory.PrincipalRows

namespace GlobalTheory.PrincipalRows


set_option maxHeartbeats 1000000 in
theorem principal_level_rows_eq_top : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → (⨆ p, R.EEp3 p) = ⊤ → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmB → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → (R.toCx3 F).zs.InBlock → EEg3 A3 (R.toCx3 F) (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc) = ⊤ := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s _hOk hC hTop hPos hB hRT hIB
  have hKR : (R.toCx3 F).KFormR := RealDat3.kFormR_of hC.base.models
  have hJR : (R.toCx3 F).JIsoR F.cv := RealDat3.jIsoR_of hC.base.models
  have hmem := theta_adjoint_mem (R.toCx3 F) F.cv hKR hJR hRT A3.A.fam.μ0
    (EEg3 A3 (R.toCx3 F) (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc))
    (theta_base_forms_mem_principal_good_part A3 (R.toCx3 F) hIB)

  have hpart : ∀ p, ∀ y ∈ R.EEp3 p, (Tw.mk (twAt D.what₂.embLL A3.A.v0) y : (R.toCx3 F).EE) ∈
      EEg3 A3 (R.toCx3 F) (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc) := by
    intro p y hy
    have hc : (0 : ℝ) < R.kap * ∏ j ∈ Finset.Icc 1 D.R.m, R.lamN A3.A.fam.μ0 j p := by
      refine mul_pos hPos.1 (Finset.prod_pos fun j _ => ?_)
      unfold RealDat3.lamN
      split_ifs
      · exact hPos.2 _ _ _
      · exact one_pos
    have hne : ((R.kap * ∏ j ∈ Finset.Icc 1 D.R.m, R.lamN A3.A.fam.μ0 j p : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    have hce : ((R.kap * ∏ j ∈ Finset.Icc 1 D.R.m, R.lamN A3.A.fam.μ0 j p : ℝ) : ℂ)⁻¹ • y ∈ R.EEp3 p :=
      (R.EEp3 p).smul_mem _ hy
    have key : R.Th A3.A.fam.μ0 (LinearMap.adjoint (R.Th A3.A.fam.μ0)
        (((R.kap * ∏ j ∈ Finset.Icc 1 D.R.m, R.lamN A3.A.fam.μ0 j p : ℝ) : ℂ)⁻¹ • y)) = y := by
      refine (hB A3.A.fam.μ0 p _ hce).trans ?_
      rw [smul_smul, mul_inv_cancel₀ hne, one_smul]
    have h3 := hmem (Tw.mk (twAt D.what₂.embLL A3.A.v0) (((R.kap * ∏ j ∈ Finset.Icc 1 D.R.m, R.lamN A3.A.fam.μ0 j p : ℝ) : ℂ)⁻¹ • y))
    have h4 : (R.toCx3 F).Θ A3.A.fam.μ0 (LinearMap.adjoint ((R.toCx3 F).Θ A3.A.fam.μ0)
        (Tw.mk (twAt D.what₂.embLL A3.A.v0) (((R.kap * ∏ j ∈ Finset.Icc 1 D.R.m, R.lamN A3.A.fam.μ0 j p : ℝ) : ℂ)⁻¹ • y))) = Tw.mk (twAt D.what₂.embLL A3.A.v0) y := by
      show Tw.map _ (R.Th A3.A.fam.μ0) (LinearMap.adjoint (Tw.map _ (R.Th A3.A.fam.μ0)) _) = _
      rw [Tw.adjoint_map]
      exact congrArg (Tw.mk (twAt D.what₂.embLL A3.A.v0)) key
    rw [h4] at h3
    exact h3
  rw [eq_top_iff]
  intro e0 _
  have hx : Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) e0 ∈ ⨆ p, R.EEp3 p := by rw [hTop]; exact Submodule.mem_top
  have hall : ∀ y ∈ ⨆ p, R.EEp3 p, (Tw.mk (twAt D.what₂.embLL A3.A.v0) y : (R.toCx3 F).EE) ∈
      EEg3 A3 (R.toCx3 F) (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc) := by
    intro y hy
    exact Submodule.iSup_induction R.EEp3 (motive := fun y => (Tw.mk (twAt D.what₂.embLL A3.A.v0) y : (R.toCx3 F).EE) ∈
      EEg3 A3 (R.toCx3 F) (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc)) hy hpart
      (Submodule.zero_mem _) (fun a b ha hb => Submodule.add_mem _ ha hb)
  exact hall _ hx

end GlobalTheory.PrincipalRows
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelRowsEqTopStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.EEg3_eq_univ_of_weakCharacterisation : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → (⨆ p, R.EEp3 p) = ⊤ → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmB → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → (R.toCx3 F).zs.InBlock → EEg3 A3 (R.toCx3 F) (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc) = ⊤ := by
  first | exact @GlobalTheory.PrincipalRows.principal_level_rows_eq_top | exact GlobalTheory.PrincipalRows.principal_level_rows_eq_top | (intros; apply GlobalTheory.PrincipalRows.principal_level_rows_eq_top <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankGrowthLimsupOfEventuallyPolynomial
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankGrowthLimsupOfEventuallyPolynomial
set_option autoImplicit false

namespace GlobalTheory.CompHt

open Filter Topology
open scoped ENNReal

set_option autoImplicit false in
open Filter Topology in
open scoped ENNReal in
private lemma factorial_mul_div_pow_ennreal_eq_ofReal (D k m : ℕ) (hk : 1 ≤ k) :
    (D.factorial : ℝ≥0∞) * ((m : ℕ∞) : ℝ≥0∞) / (k : ℝ≥0∞) ^ D =
      ENNReal.ofReal ((D.factorial : ℝ) * (m : ℝ) / (k : ℝ) ^ D) := by
  have hk' : (0 : ℝ) < (k : ℝ) ^ D := by
    have : (0 : ℝ) < k := by exact_mod_cast hk
    positivity
  rw [ENNReal.ofReal_div_of_pos hk', ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_pow (by positivity)]
  simp

set_option autoImplicit false in
open Filter Topology in
open scoped ENNReal in
private lemma tendsto_eval_div_pow_atTop_coeff_of_degree_le (Q : Polynomial ℝ) (D : ℕ) (hQ : Q.degree ≤ D) :
    Tendsto (fun y : ℝ => Q.eval y / y ^ D) atTop (𝓝 (Q.coeff D)) := by
  have hX : (Polynomial.X ^ D : Polynomial ℝ).degree = D := by simp
  rcases hQ.lt_or_eq with hlt | heq
  · have hc : Q.coeff D = 0 := Polynomial.coeff_eq_zero_of_degree_lt hlt
    rw [hc]
    simpa using Polynomial.div_tendsto_atTop_zero_of_degree_lt (P := Q) (Q := Polynomial.X ^ D) (by rw [hX]; exact hlt)
  · have hc : Q.leadingCoeff = Q.coeff D := by
      rw [Polynomial.leadingCoeff, Polynomial.natDegree_eq_of_degree_eq_some heq]
    have := Polynomial.div_tendsto_atTop_leadingCoeff_div_of_degree_eq (P := Q) (Q := Polynomial.X ^ D) (by rw [hX, heq])
    simpa [hc] using this


set_option autoImplicit false in
open Filter Topology in
open scoped ENNReal in
theorem _root_.GlobalTheory.CompHt.growth_of_eventually_eq_eval :
    ∀ (D a : ℕ) (h : ℕ → ℕ) (H : Polynomial ℚ), 1 ≤ a → (∀ᶠ n : ℕ in atTop, (h n : ℚ) = H.eval (n : ℚ)) →
      (H.degree ≤ D → ∀ δ : ℕ, (δ : ℚ) = (D.factorial : ℚ) * H.coeff D →
        _root_.GlobalTheory.CompHt.growth D (fun k => (h (a * k) : ℕ∞)) = (a : ℝ≥0∞) ^ D * δ) ∧
      ((D : WithBot ℕ) < H.degree → _root_.GlobalTheory.CompHt.growth D (fun k => (h (a * k) : ℕ∞)) = ⊤) := by
  intro D a h H ha hev
  set Q : Polynomial ℝ := H.map (algebraMap ℚ ℝ) with hQdef
  have hQdeg : Q.degree = H.degree := Polynomial.degree_map _ _

  have hak : Tendsto (fun k : ℕ => a * k) atTop atTop :=
    tendsto_atTop_mono (fun k => Nat.le_mul_of_pos_left k ha) tendsto_id
  have hakR : Tendsto (fun k : ℕ => ((a * k : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hak

  have hval : ∀ᶠ k : ℕ in atTop, (h (a * k) : ℝ) = Q.eval ((a * k : ℕ) : ℝ) := by
    filter_upwards [hak.eventually hev] with k hk
    have hcast : ((a * k : ℕ) : ℝ) = algebraMap ℚ ℝ ((a * k : ℕ) : ℚ) := by simp
    rw [hQdef, Polynomial.eval_map, hcast, Polynomial.eval₂_at_apply, ← hk]
    simp

  set g : ℕ → ℝ := fun k => (D.factorial : ℝ) * (h (a * k) : ℝ) / (k : ℝ) ^ D with hg
  have hg_eq : ∀ᶠ k : ℕ in atTop, g k = (D.factorial : ℝ) * (a : ℝ) ^ D *
      (Q.eval ((a * k : ℕ) : ℝ) / ((a * k : ℕ) : ℝ) ^ D) := by
    filter_upwards [hval, eventually_ge_atTop 1] with k hk hk1
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
    have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
    simp only [hg]
    rw [hk]
    push_cast
    field_simp
    ring
  have hlim : _root_.GlobalTheory.CompHt.growth D (fun k => (h (a * k) : ℕ∞)) = limsup (fun k => ENNReal.ofReal (g k)) atTop := by
    unfold _root_.GlobalTheory.CompHt.growth
    refine limsup_congr ?_
    filter_upwards [eventually_ge_atTop 1] with k hk
    exact factorial_mul_div_pow_ennreal_eq_ofReal D k (h (a * k)) hk
  refine ⟨fun hdeg δ hδ => ?_, fun hdeg => ?_⟩
  · have hT : Tendsto g atTop (𝓝 ((D.factorial : ℝ) * (a : ℝ) ^ D * Q.coeff D)) := by
      refine Tendsto.congr' (EventuallyEq.symm hg_eq) ?_
      exact ((tendsto_eval_div_pow_atTop_coeff_of_degree_le Q D (hQdeg ▸ hdeg)).comp hakR).const_mul _
    rw [hlim, (ENNReal.tendsto_ofReal hT).limsup_eq]
    have hc : (D.factorial : ℝ) * (a : ℝ) ^ D * Q.coeff D = ((a ^ D * δ : ℕ) : ℝ) := by
      rw [hQdef, Polynomial.coeff_map]
      have : ((δ : ℚ) : ℝ) = ((D.factorial : ℚ) * H.coeff D : ℚ) := by rw [hδ]
      push_cast at this ⊢
      rw [this]
      simp only [eq_ratCast]
      ring
    rw [hc, ENNReal.ofReal_natCast]
    push_cast
    rfl
  · have hQdeg' : (D : WithBot ℕ) < Q.degree := hQdeg ▸ hdeg
    have hX : (Polynomial.X ^ D : Polynomial ℝ).degree = D := by simp
    have hlc : 0 < Q.leadingCoeff := by
      by_contra hneg
      push_neg at hneg
      have hpos : 0 < Q.degree := lt_of_le_of_lt (by exact_mod_cast Nat.zero_le D) hQdeg'
      have hbot := (Polynomial.tendsto_atBot_of_leadingCoeff_nonpos hpos hneg).comp hakR
      have hneg' := hbot.eventually (eventually_lt_atBot (0 : ℝ))
      obtain ⟨k, hk1, hk2⟩ := (hneg'.and hval).exists
      simp only [Function.comp_apply] at hk1
      rw [← hk2] at hk1
      exact absurd hk1 (not_lt.2 (Nat.cast_nonneg _))
    have hT : Tendsto g atTop atTop := by
      refine Tendsto.congr' (EventuallyEq.symm hg_eq) ?_
      refine Tendsto.const_mul_atTop (by positivity) ?_
      refine (Polynomial.div_tendsto_atTop_of_degree_gt (P := Q) (Q := Polynomial.X ^ D) (by rw [hX]; exact hQdeg')
        (by simp) ?_).comp hakR |>.congr fun k => by simp
      simpa using hlc.le
    rw [hlim]
    exact (ENNReal.tendsto_ofReal_atTop.comp hT).limsup_eq

end GlobalTheory.CompHt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankGrowthLimsupOfEventuallyPolynomialStatement
open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankGrowthLimsup_of_eventually_polynomial : ∀ (D a : ℕ) (h : ℕ → ℕ) (H : Polynomial ℚ), 1 ≤ a → (∀ᶠ n : ℕ in atTop, (h n : ℚ) = H.eval (n : ℚ)) → (H.degree ≤ D → ∀ δ : ℕ, (δ : ℚ) = (D.factorial : ℚ) * H.coeff D → growth D (fun k => (h (a * k) : ℕ∞)) = (a : ℝ≥0∞) ^ D * δ) ∧ ((D : WithBot ℕ) < H.degree → growth D (fun k => (h (a * k) : ℕ∞)) = ⊤) := by
  first | exact @GlobalTheory.CompHt.growth_of_eventually_eq_eval | exact GlobalTheory.CompHt.growth_of_eventually_eq_eval | (intros; apply GlobalTheory.CompHt.growth_of_eventually_eq_eval <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLiftFormsEqGoodForms
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLiftFormsEqGoodForms
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.WgLift

open Formalism.IndefR.CxPass.LevelOperators


set_option maxHeartbeats 1000000 in
theorem principal_lift_forms_eq_good_forms : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → (∀ i, (⨆ p, R.Wp3 i p) = LinearMap.range (eH R.toRealDat i)) → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmA → Formalism.IndefR.Rat.LiftTest (R.toCx3 F) → (R.toCx3 F).zs.InBlock → ∀ i, principalFormsSubspace A3 (R.toCx3 F) (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc) i = Tw.sub (twAt D.what₂.embLL A3.A.v0) (LinearMap.range (eH R.toRealDat i)) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hok hch hex hW hpos hA hLT hB i
  have hc := Formalism.IndefR.Links.RealDat3.characterisation_of_weak hch hex
  have hM := hc.models
  have hCore : Core R.toRealDat F.lv2 := ⟨hc.lev, hc.grp, hc.fam, hc.models, hc.chain, hc.thP⟩
  have hL := GlobalTheory.Hk3.eH_laws R.toRealDat F.lv2 hCore hok.ok2.irr i
  have hK : (R.toCx3 F).KFormL := Formalism.IndefR.Links.RealDat3.kFormL_of (F := F) hM
  have hJ : (R.toCx3 F).JIsoL F.cv := Formalism.IndefR.Links.RealDat3.jIsoL_of (F := F) hM
  have hθ : ∀ t (u : (R.toCx3 F).FLC i t), Tw.out (s := (twAt D.what₂.embLL A3.A.v0)) (E := (R.HW i (sg0 D A3.A)).H) ((R.toCx3 F).θ' i t u) =
      cj (twAt D.what₂.embLL A3.A.v0) (R.phs i) • R.thG i t (Tw.out (s := (twAt D.what₂.embLL A3.A.v0)) (E := (R.HV i t).H) u) := by
    intro t u
    rfl

  have hsub : ∀ t, ∀ y ∈ LinearMap.range ((R.toCx3 F).θ' i t), y ∈ Tw.sub (twAt D.what₂.embLL A3.A.v0) (LinearMap.range (eH R.toRealDat i)) := by
    rintro t _ ⟨u, rfl⟩
    change Tw.out (s := (twAt D.what₂.embLL A3.A.v0)) (E := (R.HW i (sg0 D A3.A)).H) ((R.toCx3 F).θ' i t u) ∈ LinearMap.range (eH R.toRealDat i)
    rw [hθ]
    exact ⟨cj (twAt D.what₂.embLL A3.A.v0) (R.phs i) • R.thG i t (Tw.out (s := (twAt D.what₂.embLL A3.A.v0)) (E := (R.HV i t).H) u), by rw [map_smul, hL.2.2.2]⟩

  have hrng : ∀ t, LinearMap.range ((R.toCx3 F).θ' i t) ≤
      LinearMap.range ((R.toCx3 F).tC (crdOf3 A3 ⊥ 1 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false i t) := by
    intro t
    obtain ⟨N, ψ, hψ, hr⟩ := hLT i
    have hRZ := Formalism.IndefR.Rat.range_adjoint_rat A3.fam3.base3.v0.embedding ((R.toCx3 F).jL i t) (F.cv.hL i t)
      (Formalism.IndefR.Cx.CxData.bL (A := A3.fam3.amb3) i t)
      (hK i t).1 (hK i t).2 (hJ i t) ((R.toCx3 F).θ' i t) ψ hψ (fun k x => hr t k x)
    have hgood : (LinearMap.range (LinearMap.adjoint ((R.toCx3 F).θ' i t))).comap ((R.toCx3 F).jL i t) ≤
        LinearMap.range (opF (A3.A.fam.L i t).r (idemOf A3.A.X)) := by
      intro z hz
      have h1 : z ∈ (A3.A.fam.L i t).goodF A3.A.X := (hB.2 i t hz).2
      have h2 : (A3.A.fam.L i t).goodF A3.A.X = LinearMap.range (opF (A3.A.fam.L i t).r (idemOf A3.A.X)) := by
        unfold BlockDat.goodF
        rw [Formalism.IndefR.CxPass.LevelOperators.goodAt_bot]
        rfl
      rwa [h2] at h1
    rintro _ ⟨v, rfl⟩
    obtain ⟨u, hu, k, hk, hak⟩ := (LinearMap.range (LinearMap.adjoint ((R.toCx3 F).θ' i t))).exists_add_mem_mem_orthogonal v
    have hk0 : (R.toCx3 F).θ' i t k = 0 := by
      have h0 : ⟪LinearMap.adjoint ((R.toCx3 F).θ' i t) ((R.toCx3 F).θ' i t k), k⟫_ℂ = 0 := (Submodule.mem_orthogonal _ _).1 hk _ ⟨_, rfl⟩
      rw [LinearMap.adjoint_inner_left] at h0
      exact inner_self_eq_zero.1 h0
    rw [hak, map_add (f := _), hk0, add_zero]
    have hZeq : (((LinearMap.range (LinearMap.adjoint ((R.toCx3 F).θ' i t))).comap ((R.toCx3 F).jL i t)) ⊓
        LinearMap.range (opF (A3.A.fam.L i t).r (idemOf A3.A.X)) : Submodule _ _) =
        LinearMap.range ((A3.A.fam.L i t).toF (A3.A.fam.lvlA ⊥ 1) ((R.toCx3 F).Zl i t)) := by
      refine Eq.trans ?_ (Formalism.IndefR.CxPass.LevelOperators.range_toF (A3.A.fam.L i t) (A3.A.fam.lvlA ⊥ 1) _).symm
      rw [Formalism.IndefR.CxPass.LevelOperators.goodR_eq,
        show goodAt (A3.A.fam.lvlA ⊥ 1).X (A3.A.fam.lvlA ⊥ 1).P (A3.A.fam.lvlA ⊥ 1).ψ = idemOf A3.A.X from
          Formalism.IndefR.CxPass.LevelOperators.goodAt_bot _ _]
      rfl
    have hZ2 : (LinearMap.range (LinearMap.adjoint ((R.toCx3 F).θ' i t))).comap ((R.toCx3 F).jL i t) =
        LinearMap.range ((A3.A.fam.L i t).toF (A3.A.fam.lvlA ⊥ 1) ((R.toCx3 F).Zl i t)) := (inf_eq_left.2 hgood).symm.trans hZeq
    rw [← hRZ, hZ2] at hu
    obtain ⟨c, hc⟩ : u ∈ LinearMap.range (lin ((R.toCx3 F).uL (crdOf3 A3 ⊥ 1 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false i t)) := by
      refine (Submodule.span_le.2 ?_) hu
      rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨cpt A3.fam3.base3.v0.embedding x,
        ((R.toCx3 F).jL_toL (crdOf3 A3 ⊥ 1 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false i t x).symm⟩
    exact ⟨c, by rw [(R.toCx3 F).tC_eq, hc]⟩

  have hsup : Tw.sub (twAt D.what₂.embLL A3.A.v0) (LinearMap.range (eH R.toRealDat i)) ≤ LinearMap.range ((R.toCx3 F).θ' i A3.A.μ0) := by
    intro w hw
    have hw' : Tw.out (s := (twAt D.what₂.embLL A3.A.v0)) (E := (R.HW i (sg0 D A3.A)).H) w ∈ ⨆ p, R.Wp3 i p := by rw [hW i]; exact hw
    have hcc : starRingEnd ℂ (R.phs i) * R.phs i = 1 := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, (hch.phase i).1]; norm_num
    refine Submodule.iSup_induction (fun p => R.Wp3 i p) (motive := fun (x : (R.HW i (sg0 D A3.A)).H) => (Tw.mk (twAt D.what₂.embLL A3.A.v0) x : (R.toCx3 F).W i) ∈
      LinearMap.range ((R.toCx3 F).θ' i A3.A.μ0)) hw' ?_ ?_ ?_
    · intro p x hx
      have hlam := hpos.2 i A3.A.μ0 p
      have ha : LinearMap.adjoint (Tw.map (twAt D.what₂.embLL A3.A.v0) (R.thG i A3.A.μ0)) (Tw.mk (twAt D.what₂.embLL A3.A.v0) x) =
          Tw.map (twAt D.what₂.embLL A3.A.v0) (LinearMap.adjoint (R.thG i A3.A.μ0)) (Tw.mk (twAt D.what₂.embLL A3.A.v0) x) :=
        congrArg (fun f => f (Tw.mk (twAt D.what₂.embLL A3.A.v0) x)) (Formalism.IndefR.Links.Tw.adjoint_map (s := (twAt D.what₂.embLL A3.A.v0)) (R.thG i A3.A.μ0))
      have key : Tw.map (twAt D.what₂.embLL A3.A.v0) (R.thG i A3.A.μ0) (LinearMap.adjoint (Tw.map (twAt D.what₂.embLL A3.A.v0) (R.thG i A3.A.μ0)) (Tw.mk (twAt D.what₂.embLL A3.A.v0) x)) =
          ((R.lam3 i A3.A.μ0 p A3.A.v0 : ℝ) : ℂ) • Tw.mk (twAt D.what₂.embLL A3.A.v0) x := by
        refine (congrArg (Tw.map (twAt D.what₂.embLL A3.A.v0) (R.thG i A3.A.μ0)) ha).trans ?_
        show Tw.mk (twAt D.what₂.embLL A3.A.v0) (R.thG i A3.A.μ0 (LinearMap.adjoint (R.thG i A3.A.μ0) x)) = _
        rw [hA i A3.A.μ0 p _ hx, Tw.mk_smul, cj_ofReal]
      have h3 := (Formalism.IndefR.Links.RealDat3.phase_cancel hcc (Tw.map (twAt D.what₂.embLL A3.A.v0) (R.thG i A3.A.μ0)) (Tw.mk (twAt D.what₂.embLL A3.A.v0) x)).trans key
      refine ⟨((R.lam3 i A3.A.μ0 p A3.A.v0 : ℝ) : ℂ)⁻¹ •
        LinearMap.adjoint (R.phs i • Tw.map (twAt D.what₂.embLL A3.A.v0) (R.thG i A3.A.μ0)) (Tw.mk (twAt D.what₂.embLL A3.A.v0) x), ?_⟩
      change (R.phs i • Tw.map (twAt D.what₂.embLL A3.A.v0) (R.thG i A3.A.μ0)) (((R.lam3 i A3.A.μ0 p A3.A.v0 : ℝ) : ℂ)⁻¹ •
        LinearMap.adjoint (R.phs i • Tw.map (twAt D.what₂.embLL A3.A.v0) (R.thG i A3.A.μ0)) (Tw.mk (twAt D.what₂.embLL A3.A.v0) x)) = Tw.mk (twAt D.what₂.embLL A3.A.v0) x
      refine (map_smul _ _ _).trans ((congrArg (fun z => ((R.lam3 i A3.A.μ0 p A3.A.v0 : ℝ) : ℂ)⁻¹ • z) h3).trans ?_)
      rw [smul_smul, inv_mul_cancel₀ (by exact_mod_cast hlam.ne'), one_smul]
    · exact Submodule.zero_mem _
    · intro x y hx hy
      exact Submodule.add_mem _ hx hy
  unfold principalFormsSubspace
  apply le_antisymm
  · refine iSup_le fun t => ?_
    rintro _ ⟨c, rfl⟩
    rw [(R.toCx3 F).tC_eq]
    exact hsub t _ ⟨_, rfl⟩
  · exact (hsup.trans (hrng A3.A.μ0)).trans
      (le_iSup (fun t => LinearMap.range ((R.toCx3 F).tC (crdOf3 A3 ⊥ 1 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false i t)) A3.A.μ0)

end GlobalTheory.WgLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLiftFormsEqGoodFormsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalFormsSubspace_eq_good_forms : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → (∀ i, (⨆ p, R.Wp3 i p) = LinearMap.range (eH R.toRealDat i)) → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmA → Formalism.IndefR.Rat.LiftTest (R.toCx3 F) → (R.toCx3 F).zs.InBlock → ∀ i, principalFormsSubspace A3 (R.toCx3 F) (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc) i = Tw.sub (twAt D.what₂.embLL A3.A.v0) (LinearMap.range (eH R.toRealDat i)) := by
  first | exact @GlobalTheory.WgLift.principal_lift_forms_eq_good_forms | exact GlobalTheory.WgLift.principal_lift_forms_eq_good_forms | (intros; apply GlobalTheory.WgLift.principal_lift_forms_eq_good_forms <;> assumption)
end
end
