module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFockMapOfCanonicalCommutationRelations
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFockVacuumGaussianFrames
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ClassSumValuesUnitOfClassSumValues
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowGeneratorEqConstMulVacuumTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVacuumMultiplierConstantPerLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolSub0LeSpanRaw
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormAdelicThetaSumSchroedingerRationalPairInvari
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralAdelicThetaSumSqParsevalSecondVariable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceSzNonneg
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffThetaTransformAdelicSchwartzRealDirection

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGridCharactersArchExponentsGapGtRank
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGridCharactersArchExponentsGapGtRank
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.SquareExps

open GlobalTheory.Chain.StepVac

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem hasInfExp_one_of (τ : D.what₂.Tau) (h : ∃ θ, IsInfFam (D := D) θ) : HasInfExp D (1 : (AE D)ˣ →* Circle) τ 0 :=
  ⟨0, by simp, h, fun θ _ x _ _ => by simp⟩

theorem hasInfExp_pow {η : (AE D)ˣ →* Circle} {τ : D.what₂.Tau} {b : ℚ} (h : HasInfExp D η τ b) (n : ℕ) :
    HasInfExp D (η ^ n) τ (n * b) := by
  induction n with
  | zero =>
    obtain ⟨_, _, hθ, _⟩ := h
    simpa using hasInfExp_one_of τ hθ
  | succ n ih =>
    rw [pow_succ]
    have := hasInfExp_mul ih h
    convert this using 1
    push_cast; ring

theorem eta_exp {μ₀ : T} (hL : L.Is μ₀) (τ : D.what₂.Tau) : HasInfExp D L.eta τ (1 / 2) :=
  GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ hL.eta
    (hasInfQ_tau (a := fun _ => 1 / 2) ⟨_, fun _ => by norm_num, L.C.isEta.inf⟩) τ

theorem alpha_exp {μ₀ : T} (hL : L.Is μ₀) (t : T) (i j : ℕ) (hj : j < D.R.m) (τ : D.what₂.Tau) :
    HasInfExp D (alpha G t i j) τ (-(D.hc τ).e ⟨j, hj⟩ + (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps G i j : ℚ) * (1 / 2)) := by
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  have h0 := GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ (hL.mu0 ⟨j, hj⟩) (hasInfQ_tau (L.C.isMu0 ⟨j, hj⟩).inf) τ
  obtain ⟨θ, hθ⟩ : ∃ θ, IsInfFam (D := D) θ := by
    obtain ⟨_, _, hθ, _⟩ := h0
    exact hθ
  have h1 : HasInfExp D (L.mu t (j + 1)) τ (-(D.hc τ).e ⟨j, hj⟩) := by
    have := hasInfExp_mul h0 (hasInfExp_of_order hθ (hL.xi t) hn ho τ)
    rw [add_zero, Formalism.L2.Host.eExp, Equiv.symm_apply_apply] at this
    exact this
  exact hasInfExp_mul h1 (hasInfExp_pow (eta_exp hL τ) _)

theorem beta_exp {μ₀ : T} (hL : L.Is μ₀) (i j : ℕ) (hi : i < D.R.m) (τ : D.what₂.Tau) :
    HasInfExp D (beta G i j) τ ((cen D sc.cGap τ (D.R.m - i) : ℚ) + (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps G i j : ℚ) * (1 / 2)) := by
  have hm1 : 1 ≤ D.R.m - i := by omega
  have hm2 : D.R.m - i ≤ D.R.m := by omega
  have h0 : HasInfExp D (G.ch.chi (D.R.m - i)) τ (cen D sc.cGap τ (D.R.m - i) : ℚ) :=
    GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ (fun τ => (cen D sc.cGap τ (D.R.m - i) : ℚ)) (G.ch.chi_eq _ hm1 hm2)
      ⟨fun τ => 2 * cen D sc.cGap τ (D.R.m - i), fun τ => by push_cast; ring, G.ch.inf _ hm1 hm2⟩ τ
  exact hasInfExp_mul h0 (hasInfExp_pow (eta_exp hL τ) _)

theorem exps : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m), SquareStanding G t → ∀ (τf : InfinitePlace D.host.F → D.what₂.Tau)
    (hτf : ∀ w, ((starRingEnd ℂ).comp (tauE D (τf w))).comp (algebraMap D.host.F D.host.E) = w.embedding),
    ∃ mα mβ : InfinitePlace D.host.F → ℤ,
      HasExp (fun w => ⟨(starRingEnd ℂ).comp (tauE D (τf w)), hτf w⟩) (alpha G t i j) mα ∧
      HasExp (fun w => ⟨(starRingEnd ℂ).comp (tauE D (τf w)), hτf w⟩) (beta G i j) mβ ∧
      ∀ w, (((spW G i j).rank + (spW₁ G i j).rank : ℕ) : ℤ) < mα w - mβ w := by
  intro D T L sc G μ₀ hL t i j _ τf hτf
  obtain ⟨mα, hα, eα⟩ := GlobalTheory.T.hasArchimedeanCharExponents_conj_of_hasInfExp _ _ (fun τ => alpha_exp (G := G) hL t i j j.2 τ) τf hτf
  obtain ⟨mβ, hβ, eβ⟩ := GlobalTheory.T.hasArchimedeanCharExponents_conj_of_hasInfExp _ _ (fun τ => beta_exp (G := G) hL i j i.2 τ) τf hτf
  refine ⟨mα, mβ, hα, hβ, fun w => ?_⟩
  have hr : ∀ a b, a ≤ D.R.m → b ≤ D.R.m → (G.V (.grid a b)).rank = rankV D a b :=
    fun a b ha hb => (node_isV G hL (X := .grid a b) ⟨ha, hb⟩).rank
  have key := GlobalTheory.T.chiGridVertexRank_add_lt_two_exponent_add_centre sc.cGap (τf w) i j i.2 j.2
  have e1 : (spW G i j).rank = rankV D (i + 1) (j + 1) := hr _ _ (by omega) (by omega)
  have e2 : (spW₁ G i j).rank = rankV D i j := hr _ _ (by omega) (by omega)
  rw [e1, e2]
  have h1 := eα w
  have h2 := eβ w
  have : (((rankV D (i + 1) (j + 1) + rankV D i j : ℕ) : ℤ) : ℚ) < ((mα w - mβ w : ℤ) : ℚ) := by
    push_cast at h1 h2 key ⊢
    rw [h1, h2]
    linarith
  exact_mod_cast this

end GlobalTheory.SquareExps

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGridCharactersArchExponentsGapGtRankStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaGridCharacters_archExponents_gap_gt_rank : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m), SquareStanding G t → ∀ (τf : InfinitePlace D.host.F → D.what₂.Tau)
    (hτf : ∀ w, ((starRingEnd ℂ).comp (tauE D (τf w))).comp (algebraMap D.host.F D.host.E) = w.embedding),
    ∃ mα mβ : InfinitePlace D.host.F → ℤ,
      HasExp (fun w => ⟨(starRingEnd ℂ).comp (tauE D (τf w)), hτf w⟩) (alpha G t i j) mα ∧
      HasExp (fun w => ⟨(starRingEnd ℂ).comp (tauE D (τf w)), hτf w⟩) (beta G i j) mβ ∧
      ∀ w, (((spW G i j).rank + (spW₁ G i j).rank : ℕ) : ℤ) < mα w - mβ w := by
  first | exact @GlobalTheory.SquareExps.exps | exact GlobalTheory.SquareExps.exps | (intros; apply GlobalTheory.SquareExps.exps <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorSkewHermitianSplitSymplecticPair
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PiWIncM
open scoped TensorProduct
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.FourSumComposition

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem piW_cA (σ : E →ₐ[F] E) {v : Pl (F := F)} (τ : E →ₐ[F] Fv F v) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    piW τ (cA σ z) = piW (τ.comp σ) z := by

  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [piW, cA, GlobalTheory.AdelicU.compFin, GlobalTheory.AdelicU.splitProj_tmul]
  | add y z hy hz => rw [map_add (f := _), map_add (f := _), map_add (f := _), hy, hz]

theorem piW_incM {v : Pl (F := F)} (τ : E →ₐ[F] Fv F v) {m : ℕ} (J : Matrix (Fin m) (Fin m) E) (i j : Fin m) :
    piW τ (incM F J i j) = τ (J i j) := by
  simp [incM, inclR, piW, GlobalTheory.AdelicU.compFin, GlobalTheory.AdelicU.splitProj_tmul]

theorem comp_comp {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {v : Pl (F := F)} (τ : E →ₐ[F] Fv F v) : (τ.comp σ).comp σ = τ := by
  ext x
  simp [GlobalTheory.AdelicU.cm_conj_conj h x]

theorem sum_four {R : Type} [CommRing R] {m n : ℕ} (A : Matrix (Fin m) (Fin m) R) (B : Matrix (Fin n) (Fin n) R)
    (X U : Matrix (Fin m) (Fin n) R) :
    ∑ i, ∑ j, ∑ k, ∑ l, X i j * A k i * -B l j * U k l = ∑ k, ∑ l, (-(A * X * B.transpose)) k l * U k l := by

  have hR : ∀ k l, (-(A * X * B.transpose)) k l * U k l = ∑ j, ∑ i, X i j * A k i * -B l j * U k l := by
    intro k l
    simp only [Matrix.neg_apply, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, neg_mul,
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  simp only [hR]
  calc ∑ i, ∑ j, ∑ k, ∑ l, X i j * A k i * -B l j * U k l
      = ∑ i, ∑ k, ∑ j, ∑ l, X i j * A k i * -B l j * U k l :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ j, ∑ l, X i j * A k i * -B l j * U k l := Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ l, ∑ j, X i j * A k i * -B l j * U k l :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ k, ∑ l, ∑ i, ∑ j, X i j * A k i * -B l j * U k l :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ k, ∑ l, ∑ j, ∑ i, X i j * A k i * -B l j * U k l :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm

theorem main : ∀ {F E : Type} [inst : Field F] [inst_1 : NumberField F] [inst_2 : Field E] [inst_3 : NumberField E] [inst_4 : Algebra F E] {σ : E →ₐ[F] E}, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ → ∀ {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} (τ : E →ₐ[F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) {m n : ℕ} (JA : Matrix (Fin m) (Fin m) E) (JB : Matrix (Fin n) (Fin n) E), (∀ (i j : Fin m), (σ : E → E) (JA j i) = JA i j) → (∀ (i j : Fin n), (σ : E → E) (JB j i) = -JB i j) → ∀ (x u : Matrix (Fin m) (Fin n) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), Matrix.map x (⇑(GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) = (0 : Matrix (Fin m) (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) → Matrix.map u (⇑(GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (AlgHom.comp τ σ)) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) = (0 : Matrix (Fin m) (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) → (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (GlobalTheory.WeilM.hTens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JA) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JB) x u) + (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (AlgHom.comp τ σ) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (GlobalTheory.WeilM.hTens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JA) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JB) x u) = ∑ k : Fin m, ∑ l : Fin n, (-(Matrix.map JA (⇑τ : E → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) * Matrix.map x (⇑(GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (AlgHom.comp τ σ)) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) * Matrix.transpose (Matrix.map JB (⇑τ : E → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)))) k l * Matrix.map u (⇑(GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) k l := by
  intro F E _ _ _ _ _ σ hσ v τ m n JA JB hA hB x u hx hu
  have hx' : ∀ i j, piW τ (x i j) = 0 := fun i j => by simpa using congrFun (congrFun hx i) j
  have hu' : ∀ k l, piW (τ.comp σ) (u k l) = 0 := fun k l => by simpa using congrFun (congrFun hu k) l

  have h1 : piW τ (GlobalTheory.WeilM.hTens (cA σ) (incM F JA) (incM F JB) x u) = 0 := by
    simp [GlobalTheory.WeilM.hTens, piW_cA, hu']

  have h2 : piW (τ.comp σ) (GlobalTheory.WeilM.hTens (cA σ) (incM F JA) (incM F JB) x u) =
      ∑ i, ∑ j, ∑ k, ∑ l, (x.map (piW (τ.comp σ))) i j * (JA.map τ) k i * -(JB.map τ) l j *
        (u.map (piW τ)) k l := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [GlobalTheory.WeilM.hTens, map_sum, map_mul, piW_cA, comp_comp hσ, piW_incM, Matrix.map_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, hA k i, hB l j, map_neg]
  rw [h1, zero_add, h2]
  exact sum_four _ _ _ _

end GlobalTheory.FourSumComposition
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorSkewHermitianSplitSymplecticPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.HTensSplitPair

theorem hTens_split_pair : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ → ∀ {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} (τ : E →ₐ[F] Fv F v) {m n : ℕ} (JA : Matrix (Fin m) (Fin m) E) (JB : Matrix (Fin n) (Fin n) E), (∀ i j, σ (JA j i) = JA i j) → (∀ i j, σ (JB j i) = -JB i j) → ∀ (x u : Matrix (Fin m) (Fin n) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), x.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ) = 0 → u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (τ.comp σ)) = 0 → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ (GlobalTheory.WeilM.hTens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JA) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JB) x u) + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (τ.comp σ) (GlobalTheory.WeilM.hTens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JA) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JB) x u) = ∑ k, ∑ l, (-(JA.map τ * x.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (τ.comp σ)) * (JB.map τ)ᵀ)) k l * u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ) k l := by
  first
  | exact @_root_.GlobalTheory.FourSumComposition.main
  | exact _root_.GlobalTheory.FourSumComposition.main
  | (apply _root_.GlobalTheory.FourSumComposition.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.FourSumComposition.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FourSumComposition.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FourSumComposition.main ..)

end GlobalTheory.HTensSplitPair
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorSkewHermitianSplitSymplecticPairStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianTensor_skewHermitian_split_symplectic_pair : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ → ∀ {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} (τ : E →ₐ[F] Fv F v) {m n : ℕ} (JA : Matrix (Fin m) (Fin m) E) (JB : Matrix (Fin n) (Fin n) E), (∀ i j, σ (JA j i) = JA i j) → (∀ i j, σ (JB j i) = -JB i j) → ∀ (x u : Matrix (Fin m) (Fin n) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), x.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ) = 0 → u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (τ.comp σ)) = 0 → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ (GlobalTheory.WeilM.hTens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JA) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JB) x u) + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (τ.comp σ) (GlobalTheory.WeilM.hTens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JA) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JB) x u) = ∑ k, ∑ l, (-(JA.map τ * x.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (τ.comp σ)) * (JB.map τ)ᵀ)) k l * u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ) k l := by
  first | exact @GlobalTheory.HTensSplitPair.hTens_split_pair | exact GlobalTheory.HTensSplitPair.hTens_split_pair | (intros; apply GlobalTheory.HTensSplitPair.hTens_split_pair <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockToSchrodingerMapExistsOfArchHeisenbergDeriva
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockToSchrodingerMapExistsOfArchHeisenbergDeriva
noncomputable section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.FockMapEx

theorem fockEx_of_derEx : DerEx → FockEx := by
  intro hDer F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d a b A C hCM hψ hFr
  obtain ⟨D, hD⟩ := hDer F E σ α β κ ψ JA JB d hψ
  have hDf : ∀ u, At (evI F) u → ∀ (f : SInf F κ) x, D u f x =
      fderiv ℝ f x (fun i => evI F ((d.e u).1 i)) - 2 * Real.pi * Complex.I *
        (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * evI F ((d.e u).2 i)) : ℝ) * f x :=
    fun u hu f x => (hD u hu f).2 x
  obtain ⟨hadd, hsm, hcom⟩ := GlobalTheory.T.archHeisenbergDerivative_additive_commutator σ JA JB d D hDf
  have hex := fun c : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ => GlobalTheory.T.existsUnique_archimedeanMatrix_adeleExtension_of_components σ τ hCM (fun w => A w * c w * (C w)ᵀ)
  choose uOf huOf using fun c => (hex c).exists
  have huniq : ∀ c u, At (evI F) u → (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) → u = uOf c :=
    fun c u hu hw => (hex c).unique ⟨hu, hw⟩ (huOf c)
  have hAt_add : ∀ u u' : Matrix α β (AE F E), At (evI F) u → At (evI F) u' → At (evI F) (u + u') :=
    fun u u' hu hu' z hz => by rw [smul_add, hu z hz, hu' z hz, add_zero]
  have hAt_smul : ∀ (r : ℝ) (u : Matrix α β (AE F E)), At (evI F) u → At (evI F) (realAd F r • u) :=
    fun r u hu z hz => by rw [smul_comm, hu z hz, smul_zero]
  let H : (InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ) → Module.End ℂ (SInf F κ) :=
    fun c => (D (uOf c)).toLinearMap
  have hHadd : ∀ c c', H (c + c') = H c + H c' := by
    intro c c'
    have e : uOf (c + c') = uOf c + uOf c' := by
      symm
      refine huniq _ _ (hAt_add _ _ (huOf c).1 (huOf c').1) fun w => ?_
      rw [Matrix.map_add _ (map_add _), (huOf c).2 w, (huOf c').2 w]
      simp [Matrix.mul_add, Matrix.add_mul]
    ext1 f
    simp only [H, e, hadd _ _ (huOf c).1 (huOf c').1]
    rfl
  have hHsmul : ∀ (r : ℝ) c, H ((r : ℂ) • c) = (r : ℂ) • H c := by
    intro r c
    have e : uOf ((r : ℂ) • c) = realAd F r • uOf c := by
      symm
      refine huniq _ _ (hAt_smul r _ (huOf c).1) fun w => ?_
      rw [GlobalTheory.T.realScalarArchimedeanAdele_smul_matrix_realPlace σ τ hCM, (huOf c).2 w]
      simp [Matrix.mul_smul, Matrix.smul_mul]
    ext1 f
    simp only [H, e, hsm _ r (huOf c).1]
    rfl
  have hHcomm : ∀ c c', H c * H c' - H c' * H c =
      ((4 * Real.pi : ℂ) * Complex.I * ((∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im : ℂ)) • 1 := by
    intro c c'
    ext1 f
    have h1 := hcom _ _ (huOf c).1 (huOf c').1 f
    rw [GlobalTheory.T.archimedeanTrace_symplecticForm_orthonormalFrames σ τ JA JB a b A C hCM hFr _ _ c c' (huOf c).1 (huOf c').1 (huOf c).2 (huOf c').2] at h1
    simp only [H, LinearMap.sub_apply, Module.End.mul_apply, ContinuousLinearMap.coe_coe, LinearMap.smul_apply,
      Module.End.one_apply]
    rw [h1]
    congr 1
    push_cast
    ring
  obtain ⟨f₀, hf₀, hv⟩ := GlobalTheory.T.exists_fock_vacuum_gaussian_frames σ τ JA JB d a b A C D hCM hFr hDf
  have hHvac : ∀ w a b, H (Pi.single w (Matrix.single a b 1)) f₀ +
      (lineSign a b * Complex.I) • H (Pi.single w (Matrix.single a b Complex.I)) f₀ = 0 := fun w a b =>
    hv w a b _ _ (huOf _).1 (huOf _).1 (huOf _).2 (huOf _).2
  obtain ⟨Φ, hinj, hint⟩ := GlobalTheory.T.exists_fockMap_of_canonicalCommutationRelations H hHadd hHsmul hHcomm f₀ hf₀ hHvac
  refine ⟨Φ, hinj, fun u hu c hc T => ?_⟩
  rw [hint, huniq c u hu hc]
  exact (hD _ (huOf c).1 (Φ T)).1

end GlobalTheory.FockMapEx
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockToSchrodingerMapExistsOfArchHeisenbergDerivaStatement
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockToSchrodingerMapExists_of_archHeisenbergDerivatives : GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.FockEx := by
  first | exact @GlobalTheory.FockMapEx.fockEx_of_derEx | exact GlobalTheory.FockMapEx.fockEx_of_derEx | (intros; apply GlobalTheory.FockMapEx.fockEx_of_derEx <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroComplementaryAdelicSchwartzFunction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroComplementaryAdelicSchwartzFunction
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

open scoped Classical

namespace GlobalTheory.RestComplement

theorem exists_rest_ne_zero : ∀ {F : Type} [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {κ : Type} [Fintype κ]
    (f : (κ → Fv F v) → ℂ), f ∈ GlobalTheory.WeilM.SB (κ → Fv F v) →
    ∃ r : (κ → AF F) → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin F v) f r ∧ ∃ x₀, r x₀ ≠ 0 := by
  intro F _ _ v κ _ φ hφ
  obtain ⟨f, hf⟩ := GlobalTheory.TensUniq.exists_sInf_ne_zero F κ
  let φs : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F w) → ℂ :=
    fun w => Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1
  have hstd : ∀ᶠ w in Filter.cofinite, φs w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 :=
    Filter.Eventually.of_forall fun _ => rfl
  obtain ⟨r, hr, hrt⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φs hstd
  have hRest : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin F v) φ r := by
    refine ⟨hr, ?_⟩
    rw [hrt φ]
    refine GlobalTheory.TensUniq.pure_mem_schA f _ (fun w => ?_) (GlobalTheory.PureFactor.update_eventually φs v φ hstd)
    by_cases hw : w = v
    · subst hw; rw [Function.update_self]; exact hφ
    · rw [Function.update_of_ne hw]; exact GlobalTheory.StdVacuum.indicator_mem_SB w
  refine ⟨r, hRest, 0, ?_⟩
  have e := congrFun (hrt (fun _ => 1)) 0
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, one_mul] at e
  rw [e]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure
  have hI : (fun i : κ => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F ((0 : κ → AF F) i)) = 0 := by
    funext i
    show (InfiniteAdeleRing.ringEquiv_mixedSpace F) (0 : AF F).1 = 0
    exact map_zero _
  have hP : (∏ᶠ w, Function.update φs v (fun _ => 1) w fun i => evFin F w ((0 : κ → AF F) i)) = 1 := by
    refine finprod_eq_one_of_forall_eq_one fun w => ?_
    by_cases hw : w = v
    · subst hw; rw [Function.update_self]
    · rw [Function.update_of_ne hw]
      simp only [φs, Pi.zero_apply, map_zero]
      rw [Set.indicator_of_mem (by intro i; exact zero_mem _)]
      rfl
  rw [hI, hP, mul_one]
  exact hf

end GlobalTheory.RestComplement
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroComplementaryAdelicSchwartzFunctionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzero_complementary_adelicSchwartz_function : ∀ {F : Type} [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {κ : Type} [Fintype κ]
    (f : (κ → Fv F v) → ℂ), f ∈ GlobalTheory.WeilM.SB (κ → Fv F v) →
    ∃ r : (κ → AF F) → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin F v) f r ∧ ∃ x₀, r x₀ ≠ 0 := by
  first | exact @GlobalTheory.RestComplement.exists_rest_ne_zero | exact GlobalTheory.RestComplement.exists_rest_ne_zero | (intros; apply GlobalTheory.RestComplement.exists_rest_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerTransitive
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.EvNonzero

theorem pure_ne_zero {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f : SInf F κ) (hf : f ≠ 0)
    (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ) (h0 : ∀ v, φ v ≠ 0)
    (hstd : ∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ≠ 0 := by
  classical
  obtain ⟨yi, hyi⟩ : ∃ y, f y ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf (SchwartzMap.ext h)
  have hS : Set.Finite {v | ¬ (φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)} :=
    Filter.eventually_cofinite.mp hstd
  choose p hp using fun v => Function.ne_iff.mp (h0 v)
  set S := hS.toFinset with hSdef
  let yf : κ → FiniteAdeleRing (𝓞 F) F := fun i =>
    (⟨fun v => if v ∈ S then p v i else 0, by
      apply Filter.eventually_cofinite.mpr
      refine S.finite_toSet.subset ?_
      intro v hv
      by_contra hvS
      apply hv
      have hvS' : v ∉ S := fun h => hvS (Finset.mem_coe.mpr h)
      show (if v ∈ S then p v i else 0) ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))
      rw [if_neg hvS']
      exact zero_mem (v.adicCompletionIntegers F)⟩ :
      RestrictedProduct (fun v : Pl F => v.adicCompletion F) (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite)
  let x : κ → AdeleRing (𝓞 F) F := fun i =>
    (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (yi i), yf i) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
  intro hz
  have hx := congrFun hz x
  have h1 : (fun i => evI F (x i)) = yi := by
    funext i
    show InfiniteAdeleRing.ringEquiv_mixedSpace F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (yi i)) = yi i
    exact RingEquiv.apply_symm_apply _ _
  have h2 : ∀ v, (fun i => evFin F v (x i)) = fun i => if v ∈ S then p v i else 0 := fun v => rfl
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Pi.zero_apply, h1, h2] at hx
  have hg : ∀ v, v ∉ S → φ v (fun i => if v ∈ S then p v i else 0) = 1 := by
    intro v hv
    have hv' : φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
      by_contra h
      exact hv (hS.mem_toFinset.mpr h)
    rw [hv']
    have hzero : (fun i : κ => if v ∈ S then p v i else 0) = fun _ => 0 := funext fun i => if_neg hv
    rw [hzero, Set.indicator_of_mem (show (fun _ : κ => (0 : Fv F v)) ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from fun i => zero_mem _)]
    rfl
  have hsub : Function.mulSupport (fun v => φ v (fun i => if v ∈ S then p v i else 0)) ⊆ S := by
    intro v hv
    by_contra h
    exact hv (hg v h)
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub] at hx
  refine (mul_ne_zero hyi (Finset.prod_ne_zero_iff.mpr fun v hv => ?_)) hx
  have hpv : (fun i : κ => if v ∈ S then p v i else 0) = p v := funext fun i => if_pos hv
  rw [hpv]
  exact hp v

theorem exists_mem_schA_ev_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X₁ W₁) (ι : Matrix (Fin n) (Fin n₁) E) (ι' : Matrix (Fin d) (Fin d₁) E) (I : Set (Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁), M.IsGood B.ψ → M₁.IsGood B.ψ → IsEv B M M₁ ι ι' I e → ∃ Φ ∈ schA F (Fin n × Fin d), e Φ ≠ 0 := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ M M₁ ι ι' I e hM hM₁ hE
  obtain ⟨ei, ev, hei, hev, hpure⟩ := hE.loc
  obtain ⟨f, hf⟩ : ∃ f, ei f ≠ 0 := by
    by_contra h
    push_neg at h
    exact hei (ContinuousLinearMap.ext h)
  refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f M.vac, GlobalTheory.TensUniq.pure_mem_schA f M.vac (fun v => (hM.vac v).1) hM.std, ?_⟩
  rw [hpure f M.vac (fun v => (hM.vac v).1) (Filter.Eventually.of_forall fun _ => rfl)]
  have hv : (fun v => ev v (M.vac v)) = M₁.vac := funext fun v => (hev v).1
  rw [hv]
  exact pure_ne_zero (ei f) hf M₁.vac (fun v => (hM₁.vac v).2.1) hM₁.std

end GlobalTheory.EvNonzero

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesFirst
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.CcEx

noncomputable section

open GlobalTheory.ClsVal.Cmp

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ}

def anFibBas {H : Geo.Tor.Host E} {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} [Algebra c.F ℂ]
    {X : Data E r} {bas bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r} {e : Fin g ≃ Lt1 Dw}
    {x : Frame X.Ψ r} {L : Lt E r} {y : FrPt Xo c ℂ} (h : ∀ z w, hx X bas' idx x z w = hx X bas idx x z w)
    (A : AnFib X bas idx e x L y) : AnFib X bas' idx e x L y where
  ex := A.ex
  ex_add := A.ex_add
  ex_onto := A.ex_onto
  ex_ker := A.ex_ker
  ex_lin := A.ex_lin
  hol := A.hol
  der := A.der
  fr := A.fr
  fr_hol := A.fr_hol
  fr_ne := A.fr_ne
  fr_g := A.fr_g
  fr_0 := A.fr_0
  χ := A.χ
  χ_norm := A.χ_norm
  fr_per v hv j z hz := by rw [h, h]; exact A.fr_per v hv j z hz

theorem coord_eq {X : Data E r} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas)
    {x : Frame X.Ψ r} (hx' : x ∈ X.dom) {p q : X.Ψ × Fin r} (h : ∀ v, per X x v p = per X x v q) : p = q := by
  obtain ⟨i, rfl⟩ := idx.surjective p
  obtain ⟨j, rfl⟩ := idx.surjective q
  have hsp := ((hx_laws E r X g bas idx 0 hs Even.zero x hx').2.2.2.2.2.2.1 ⊤ (by simp)).1
  have key : ∀ z : Fin g → ℂ, z i = z j := by
    intro z
    have hz : z ∈ Submodule.span ℝ (pv X idx x '' ((⊤ : Lt E r) : Set (Fin r → E))) := hsp ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem z hz => obtain ⟨v, -, rfl⟩ := hz; exact h v
    | zero => rfl
    | add a b _ _ ha hb => simp only [Pi.add_apply, ha, hb]
    | smul a b _ hb => simp only [Pi.smul_apply, hb]
  by_contra hne
  have hij : j ≠ i := fun e => hne (by rw [e])
  have := key (Pi.single i 1)
  rw [Pi.single_eq_same, Pi.single_eq_of_ne hij] at this
  exact one_ne_zero this

variable {H : Geo.Tor.Host E} {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ}

theorem genReads_change (U : Unf Xo c σ r) (k : U.Comp) {g g' : ℕ}
    (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (U.X k).Λ) (idx : Fin g ≃ (U.X k).Ψ × Fin r) (e : Fin g ≃ Lt1 Dw)
    (bas' : (Fin g' ⊕ Fin g' → ℤ) ≃ₗ[ℤ] (U.X k).Λ) (idx' : Fin g' ≃ (U.X k).Ψ × Fin r) (e' : Fin g' ≃ Lt1 Dw)
    (hs : IsSympl (U.X k) bas) (hs' : IsSympl (U.X k) bas') (hi : IdxIs c σ (U.X k) idx e) (hi' : IdxIs c σ (U.X k) idx' e')
    (x : (U.X k).dom) (hon : IsONFr (U.X k) x.1) (ϑ' : (Fin g' → ℂ) → ℂ) (h : GenReads U k bas' idx' e' x ϑ') :
    ∃ ϑ, GenReads U k bas idx e x ϑ ∧ ∀ u : (U.X k).Ψ × Fin r → ℂ, ϑ' (u ∘ idx') = ϑ (u ∘ idx) ∧
      hx (U.X k) bas' idx' x.1 (u ∘ idx') (u ∘ idx') = hx (U.X k) bas idx x.1 (u ∘ idx) (u ∘ idx) := by
  have hg : g' = g := by simpa using Fintype.card_congr (idx'.trans idx.symm)
  subst hg
  obtain ⟨π, rfl⟩ : ∃ π : Equiv.Perm (Fin g'), e' = π.trans e := ⟨e'.trans e.symm, by ext1; simp⟩
  have hidx : idx' = π.trans idx := by
    ext1 j
    exact coord_eq idx hs x.2 fun v => (hi'.1 x.1 v j).trans (hi.1 x.1 v (π j)).symm
  subst hidx
  let _ : Algebra c.F ℂ := σ.toAlgebra
  obtain ⟨A, hA⟩ := h
  have hb : ∀ z w, hx (U.X k) bas idx x.1 z w = hx (U.X k) bas' idx x.1 z w := fun z w => by
    rw [(hx_of_isONFr E r g' 0 _ bas idx hs Even.zero _ hon).2.2, (hx_of_isONFr E r g' 0 _ bas' idx hs' Even.zero _ hon).2.2]
  refine ⟨ϑ' ∘ ren π, ⟨anFibBas hb (anFibRen π A), fun j z pt h1 h2 h3 => hA j (ren π z) pt h1 h2 h3⟩, fun u => ⟨rfl, ?_⟩⟩
  rw [hb]
  exact hx_ren _ bas' idx π x.1 (u ∘ idx) (u ∘ idx)

end Gen

theorem thA_smul' {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} (X : Data E r)
    (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (a : ℂ) (φ : TF n g) (x : Frame X.Ψ r)
    (z : Fin n → Fin g → ℂ) : thA X bas idx (a • φ) x z = a * thA X bas idx φ x z := by
  simp only [thA, SW.thS, show ∀ y, (a • φ) y = a * φ y from fun _ => rfl, _root_.mul_assoc, tsum_mul_left]
  ring

theorem exists_ccIs_of_pair (hci : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2) {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    {V W : HSp D} {χV χW : (AE D)ˣ →* Circle} {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)}
    (hP : IsPair ψ θ V W χV χW om) {mu : GA D W → ℂ} (hmu : MuVal W χV mu) (hmuQ : ∀ γ ∈ GQ W, ∀ h, mu (γ * h) = mu h)
    {r : ℕ} (hr : W.rank = r) {H : Geo.Tor.Host D.host.E} (hrt : (H.rt : D.host.E) = D.host.sqrtMinusD) {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (hσ : GoodEmb c σ)
    (hU : IsUnf U) (hr1 : 1 ≤ r) (hA : l.A = 1) {a : (D.host.E →+* ℂ) × ℕ → ℕ} (hdom : Dom a V.rank)
    {ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)}
    (hV0 : V.rank ≠ 0) (h1 : (ΛV : Set (Fin V.rank → D.host.E)) = L0c D V) (h2 : (ΛW : Set (Fin W.rank → D.host.E)) = L0c D W)
    (h3 : IsSelfDualC V ΛV) (h4 : IsSelfDualC W ΛW)
    (h5 : (ΛV : Set (Fin V.rank → D.host.E)) = (Formalism.L2.Pj.stdLat D.host.E V.rank : Set (Fin V.rank → D.host.E)))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ)
    (hmod : ∀ k, IsMod W hr (U.X k)) (hon : ∀ k, IsONFr (U.X k) (fun τ => x₀ τ.1))
    (hinv : ∀ k, IsInvOf W hr (U.X k) (fun τ => x₀ τ.1) s) {f : WO V W → ℂ}
    (hf : IsVacO ψ θ V W (fun _ => 1) s (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) f)
    (dict : GA D W → Σ k, Frame (U.X k).Ψ r) : ∃ cc, CcIs θ V W hr U dict mu x₀ om f cc := by
  have hU' : Formalism.L2.PjFree.IsUnf (Formalism.L2.PjFree.Unf.ofPj U) := hU
  obtain ⟨Wt⟩ := nonempty_uw hU'
  have hw : IsIntegral ℤ (H.w0 : D.host.E) := H.w0.isIntegral_coe
  have hw' : (H.w0 : D.host.E) + cc (H.w0 : D.host.E) = 1 := by
    rw [cc, ← H.bar_eq]
    exact_mod_cast congrArg (fun t : 𝓞 D.host.E => (t : D.host.E)) (PullbackSections.CVA.cmHostUnit_add_conj_eq_one H)
  have key : ∀ k : U.Comp, ∃ a : ℂ, ‖a‖ = 1 ∧ ∀ (h : GA D W) (x : (U.X k).dom), latR hr (latG W h) = (U.X k).Λ →
      x.1 = frMove θ W hr (U.X k) h (fun τ => x₀ τ.1) → ∀ (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (U.X k).Λ)
      (idx : Fin g ≃ (U.X k).Ψ × Fin r) (e : Fin g ≃ Lt1 Dw), IsSympl (U.X k) bas → IdxIs c σ (U.X k) idx e →
      ∀ ϑ : (Fin g → ℂ) → ℂ, GenReads U k bas idx e x ϑ → ∀ w : WO V W, w.map (finPart D) = 0 →
        om (1, h) f w = a * mu h *
          cexp (-(Real.pi / 2 : ℂ) * ∑ b, hx (U.X k) bas idx x.1
            (zOf θ V W hr (U.X k) idx x.1 w b) (zOf θ V W hr (U.X k) idx x.1 w b)) *
          ∏ b, ϑ (zOf θ V W hr (U.X k) idx x.1 w b) := by
    intro k
    have hsd : SelfD (U.X k) (U.X k).Λ := (uw_lattice _ H Dw l Xo c σ _ _ hσ hU' hr1 Wt k).2.1
    obtain ⟨Dc, -, -⟩ := exists_dic _ H Dw l c σ _ Wt.g V.rank (U.X k) a Wt.e hσ hU.1 (hU.2.1 k).1 (hU.2.1 k).2 hsd hdom
    have hi : IdxIs c σ (U.X k) Dc.idx Dc.e := ⟨Dc.per_eq, Dc.ty_eq⟩
    obtain ⟨v, hv⟩ := (TensVac.vacua _ _ _ _ Dc.bas Dc.idx V.rank Dc.sympl hP.even _ hw hw' _ hsd 1 _
      (Base.stdL_mem_Vset V.rank 1)).1
    obtain ⟨C, hC0, hC⟩ := GlobalTheory.T.pow_generator_eq_const_mul_vacuum_theta hci _ H Dw l Xo c σ r U hσ hU hr1 hA k V.rank _ Dc.bas Dc.idx Dc.e hP.even
      Dc.sympl hi v hv
    obtain ⟨κ, -, hκ, hrd⟩ := GlobalTheory.T.exists_vacuum_multiplier_constant_per_lattice D ψ θ V W χV χW om hP mu hmu r _ hr (U.X k) Dc.bas Dc.idx (hmod k) Dc.sympl H hrt
      ΛV ΛW hV0 h1 h2 h3 h4 h5 hsd _ s (hon k) (hinv k) f hf v hv
    refine ⟨κ / C, ?_, fun h x hL hxe g bas idx e hs hie ϑ' hϑ' w hw0 => ?_⟩
    · obtain ⟨hd, hu, -⟩ := hx_of_isONFr _ r _ 0 _ Dc.bas Dc.idx Dc.sympl Even.zero _ (hon k)
      obtain ⟨⟨ϑ, hϑ⟩, hall⟩ := hC ⟨_, hd⟩ hu
      obtain ⟨t1, t2, t3⟩ := hall ϑ hϑ
      rw [norm_div, ← hκ _ hd hu ϑ C t1 t2 t3, div_self (norm_ne_zero_iff.2 hC0)]
    · obtain ⟨hon', -, hread⟩ := hrd h hL
      rw [← hxe] at hon' hread
      obtain ⟨-, hu, -⟩ := hx_of_isONFr _ r _ 0 _ Dc.bas Dc.idx Dc.sympl Even.zero _ hon'
      obtain ⟨ϑ, hϑ, hch⟩ := genReads_change U k Dc.bas Dc.idx Dc.e bas idx e Dc.sympl hs hi hie x hon' ϑ' hϑ'
      have t3 := ((hC x hu).2 ϑ hϑ).2.2 (zOf θ V W hr (U.X k) Dc.idx x.1 w)
      have e1 : ∏ b, ϑ' (zOf θ V W hr (U.X k) idx x.1 w b) = ∏ b, ϑ (zOf θ V W hr (U.X k) Dc.idx x.1 w b) :=
        Finset.prod_congr rfl fun b _ => (hch _).1
      have e2 : ∑ b, hx (U.X k) bas idx x.1 (zOf θ V W hr (U.X k) idx x.1 w b) (zOf θ V W hr (U.X k) idx x.1 w b) =
          ∑ b, hx (U.X k) Dc.bas Dc.idx x.1 (zOf θ V W hr (U.X k) Dc.idx x.1 w b)
            (zOf θ V W hr (U.X k) Dc.idx x.1 w b) :=
        Finset.sum_congr rfl fun b _ => (hch _).2
      rw [hread w hw0, e1, e2, t3, thA_smul']
      field_simp
  choose cc hcc hkey using key
  refine ⟨cc, hcc, fun h γ hat hx' g bas idx e hs hi ϑ hϑ w hw0 => ?_⟩
  rw [← hmuQ γ hat.1 h]
  exact hkey _ (γ * h) ⟨_, hx'⟩ hat.2.1 hat.2.2 g bas idx e hs hi ϑ hϑ w hw0

end

end GlobalTheory.AdTh.CcEx
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLintegralSqEqMulSetLIntegralThetaTransform
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLintegralSqEqMulSetLIntegralThetaTransform
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaParseval

theorem exists_lintegral_sq_eq_mul_setLIntegral_theta : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
    ∀ (κ : Type) [Fintype κ] (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (ν : @Measure ((κ → AF F) × (κ → AF F)) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
    ∀ 𝓕 : Set ((κ → AF F) × (κ → AF F)),
      @IsAddFundamentalDomain (GlobalTheory.WeilUnitaryTransport.ratPair F κ) _ _ _ (borel _) 𝓕 ν →
      ∃ c : ENNReal, ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
        ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ w in 𝓕, ‖GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ w Φ)‖ₑ ^ 2 ∂ν := by
  intro F _ _ ψ hψ κ _ μ hμ ν hν 𝓕 h𝓕
  obtain ⟨𝓕₁, h𝓕₁, h0, htop⟩ := GlobalTheory.T.exists_fundDomain_rationalPointsAdeleTuple_finite_pos F κ μ hμ
  obtain ⟨c₁, hc0, hctop, hc⟩ := GlobalTheory.T.lintegral_rationalPair_fundDomain_eq_iterated F κ μ hμ ν hν 𝓕 h𝓕 𝓕₁ h𝓕₁
  refine ⟨(c₁ * μ 𝓕₁)⁻¹, fun Φ hΦ => ?_⟩
  have hm := GlobalTheory.T.measurable_theta_sum_of_schrodinger F ψ hψ κ Φ hΦ
  have hG : @Measurable _ _ (borel _) _ (fun w : (κ → AF F) × (κ → AF F) =>
      ‖GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ w Φ)‖ₑ ^ 2) := Measurable.pow_const (measurable_enorm.comp hm) 2
  rw [hc _ hG (fun γ hγ w => by rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, GlobalTheory.T.norm_adelicThetaSum_schroedinger_rationalPair_invariant F ψ hψ κ Φ γ hγ w])]
  simp_rw [GlobalTheory.T.lintegral_adelicThetaSum_sq_parseval_second_variable F ψ hψ κ μ hμ 𝓕₁ h𝓕₁ htop Φ hΦ]
  rw [lintegral_const_mul' _ _ htop, GlobalTheory.T.parseval_fundamental_domain_theta F κ μ hμ 𝓕₁ h𝓕₁ Φ hΦ, ← mul_assoc c₁, ← mul_assoc,
    ENNReal.inv_mul_cancel (mul_ne_zero hc0 h0) (ENNReal.mul_ne_top hctop htop), one_mul]

end GlobalTheory.ThetaParseval
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLintegralSqEqMulSetLIntegralThetaTransformStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lintegral_sq_eq_mul_setLIntegral_thetaTransform : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
    ∀ (κ : Type) [Fintype κ] (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (ν : @Measure ((κ → AF F) × (κ → AF F)) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
    ∀ 𝓕 : Set ((κ → AF F) × (κ → AF F)),
      @IsAddFundamentalDomain (GlobalTheory.WeilUnitaryTransport.ratPair F κ) _ _ _ (borel _) 𝓕 ν →
      ∃ c : ENNReal, ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
        ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ w in 𝓕, ‖GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ w Φ)‖ₑ ^ 2 ∂ν := by
  first | exact @GlobalTheory.ThetaParseval.exists_lintegral_sq_eq_mul_setLIntegral_theta | exact GlobalTheory.ThetaParseval.exists_lintegral_sq_eq_mul_setLIntegral_theta | (intros; apply GlobalTheory.ThetaParseval.exists_lintegral_sq_eq_mul_setLIntegral_theta <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiUnramifiedAwayDifferent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiUnramifiedAwayDifferent
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.StdCharUnrF

open GlobalTheory.Idele WithZero
open GlobalTheory.StdDual (codiff codiff_ne_zero)

theorem psiUnr_of_not_le : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal → PsiUnr ψ v := by
  classical
  intro F _ _ ψ hψ v hv x
  have hc := GlobalTheory.SplitUnram.count_codiff_eq_zero v (fun h => hv (Ideal.le_of_dvd h))
  set α : Af F := GlobalTheory.AdelicU.singleFin v x with hα
  have hαv : α v = x := GlobalTheory.AdelicU.evalV_singleFin_self v x
  have hαw : ∀ w, w ≠ v → α w = 0 := fun w hw => GlobalTheory.AdelicU.evalV_singleFin_ne hw x
  have h := GlobalTheory.SplitUnram.mem_adelicIdeal_codiff_iff hψ.1 (GlobalTheory.LatVacArith.psi_fin_rat hψ) α
  have key : (∀ y ∈ v.adicCompletionIntegers F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.psiLoc ψ v (x * y) = 1) ↔
      ∀ β : Af F, (∀ w, β w ∈ w.adicCompletionIntegers F) → ψ (pairA F 0 (β * α)) = 1 := by
    constructor
    · intro H β hβ
      have e : β * α = GlobalTheory.AdelicU.singleFin v (x * β v) := by
        apply GlobalTheory.AdelicU.af_ext
        intro u
        by_cases hu : u = v
        · subst hu
          rw [map_mul, hα, GlobalTheory.AdelicU.evalV_singleFin_self, GlobalTheory.AdelicU.evalV_singleFin_self]
          change β u * x = x * β u
          ring
        · rw [map_mul, hα, GlobalTheory.AdelicU.evalV_singleFin_ne hu, GlobalTheory.AdelicU.evalV_singleFin_ne hu, mul_zero]
      rw [e]
      exact H _ (hβ v)
    · intro H y hy
      have e : GlobalTheory.AdelicU.singleFin v y * α = GlobalTheory.AdelicU.singleFin v (x * y) := by
        rw [hα, ← GlobalTheory.AdelicU.singleFin_mul, mul_comm]
      have := H (GlobalTheory.AdelicU.singleFin v y) (fun w => by
        by_cases hw : w = v
        · subst hw
          change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV _ w (GlobalTheory.AdelicU.singleFin w y) ∈ _
          rw [GlobalTheory.AdelicU.evalV_singleFin_self]
          exact hy
        · change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV _ w (GlobalTheory.AdelicU.singleFin v y) ∈ _
          rw [GlobalTheory.AdelicU.evalV_singleFin_ne hw]
          exact zero_mem _)
      rw [e] at this
      exact this
  rw [key, ← h, mem_adelicIdeal_iff codiff_ne_zero, HeightOneSpectrum.mem_adicCompletionIntegers]
  constructor
  · intro H
    have := H v
    rwa [hc, neg_zero, exp_zero, hαv] at this
  · intro H w
    by_cases hw : w = v
    · subst hw
      rw [hc, neg_zero, exp_zero, hαv]
      exact H
    · rw [hαw w hw, map_zero]
      exact zero_le

end GlobalTheory.StdCharUnrF
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiUnramifiedAwayDifferentStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped GlobalTheory.VacAny

noncomputable section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psi_unramified_away_different : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal → PsiUnr ψ v := by
  first | exact @GlobalTheory.StdCharUnrF.psiUnr_of_not_le | exact GlobalTheory.StdCharUnrF.psiUnr_of_not_le | (intros; apply GlobalTheory.StdCharUnrF.psiUnr_of_not_le <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfFrameCols
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem eq_of_frame_cols : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ g g' : GAd σ J, (matHom _ σ J g).1 * adMat F C = (matHom _ σ J g').1 * adMat F C → (matHom _ σ J g).1 * adMat F Z = (matHom _ σ J g').1 * adMat F Z → (matHom _ σ J g).1 * adMat F D = (matHom _ σ J g').1 * adMat F D → g = g' := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF g g' hC hZ hD
  have key : ∀ h : GAd σ J, (matHom _ σ J h).1 =
      (matHom _ σ J h).1 * adMat F C * adMat F (cT (σ : E →+* E) D * J) +
      (matHom _ σ J h).1 * adMat F Z * adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) +
      (matHom _ σ J h).1 * adMat F D * adMat F (cT (σ : E →+* E) C * J) := by
    intro h
    have e : (matHom _ σ J h).1 = (matHom _ σ J h).1 * adMat F (C * (cT (σ : E →+* E) D * J) +
        Z * (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) + D * (cT (σ : E →+* E) C * J)) := by
      rw [hF.sum, adMat, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
    conv_lhs => rw [e]
    simp only [adMat, Matrix.map_add (inclR (F := F) (E := E) (AF F)) (map_add _), Matrix.map_mul, Matrix.mul_add, Matrix.mul_assoc]
  apply matHom_injective _ σ J
  apply Units.ext
  rw [key g, key g', hC, hZ, hD]

end GlobalTheory.SphEis
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffThetaTransformAdelicSchwartzRealDirectioStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiff_thetaTransform_adelicSchwartz_realDirections : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
      (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
      ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
      ∀ (κ : Type) [Fintype κ]
        (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
        (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
          co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
        ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ (k : ℕ) (L : (Fin k → ℝ) →+ Formalism.IndefR.Datum.WO S T), Continuous L →
          (∀ t, (L t).map (finPart D) = 0) → ∀ w, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ (w + L t) := by
  first | exact @GlobalTheory.ThetaSmooth.contDiff_thetaTr_real | exact GlobalTheory.ThetaSmooth.contDiff_thetaTr_real | (intros; apply GlobalTheory.ThetaSmooth.contDiff_thetaTr_real <;> assumption)
end
