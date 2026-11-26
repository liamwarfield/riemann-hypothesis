module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAllTiedNotStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepSplittingCharactersTameLevelResidue
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspAlongOfPairLifts
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTransformDarbouxModelLinearInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGridCharactersArchExponentsGapGtRank
public import Formalism.LocalToGlobal.Columns.DetChrChi
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowSizesNR
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspFormAvgTypeOtherPlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagPairingVectorsIntegralInFrame

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalGridNodeType
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.CuspValueType

section Model

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem dRep_conj (σ : Mx n → (H →L[ℂ] H)) {P : Mx n} (hP : IsUnit P) (X : Mx n) (w : H) :
    dRep (fun g => σ (P * g * P⁻¹)) X w = dRep σ (P * X * P⁻¹) w := by
  unfold dRep
  simp only [GlobalTheory.SmVecModel.exp_smul_conj hP]

theorem foldr_conj (σ : Mx n → (H →L[ℂ] H)) {P : Mx n} (hP : IsUnit P) (l : List (Mx n)) (w : H) :
    l.foldr (dRep fun g => σ (P * g * P⁻¹)) w = (l.map fun X => P * X * P⁻¹).foldr (dRep σ) w := by
  induction l with
  | nil => rfl
  | cons X l ih => rw [List.foldr_cons, List.map_cons, List.foldr_cons, ih, dRep_conj σ hP]

theorem sobNorm_conj (σ : Mx n → (H →L[ℂ] H)) {P : Mx n} (hP : IsUnit P) (S : List (List (Mx n))) (w : H) :
    sobNorm (fun g => σ (P * g * P⁻¹)) S w = sobNorm σ (S.map fun l => l.map fun X => P * X * P⁻¹) w := by
  unfold sobNorm
  rw [List.map_map]
  congr 1
  refine List.map_congr_left fun l _ => ?_
  simp only [Function.comp_apply, foldr_conj σ hP]

theorem sobNorm_conj_back (σ : Mx n → (H →L[ℂ] H)) {P : Mx n} (hP : IsUnit P) (S : List (List (Mx n))) (w : H) :
    sobNorm (fun g => σ (P * g * P⁻¹)) (S.map fun l => l.map fun X => P⁻¹ * X * P) w = sobNorm σ S w := by
  rw [sobNorm_conj σ hP, List.map_map]
  congr 1
  refine (List.map_congr_left fun l _ => ?_).trans (List.map_id S)
  show List.map (fun X => P * X * P⁻¹) (List.map (fun X => P⁻¹ * X * P) l) = l
  rw [List.map_map]
  refine (List.map_congr_left fun X _ => ?_).trans (List.map_id l)
  exact GlobalTheory.SmVecModel.conj_cancel hP X

theorem exists_ctrl_conj [CompleteSpace H] {ε : Fin n → Bool} {σ : Mx n → (H →L[ℂ] H)} (hσ : Std ε σ) {P G : Mx n}
    (hP : IsUnit P) (hG : Pᴴ * Jm ε * P = G) (S₀ : List (List (Mx n))) (hS₀ : Words (lieOf G) S₀) :
    ∃ S, Words (lieOf G) S ∧ Ctrl (lieOf G) (Formalism.QuantumDeterminants.UH G) (fun g => σ (P * g * P⁻¹)) S ∧
      ∃ A : ℝ, 0 ≤ A ∧ ∀ w, SmoothVec (lieOf G) (fun g => σ (P * g * P⁻¹)) w →
        sobNorm (fun g => σ (P * g * P⁻¹)) S₀ w ≤ A * sobNorm (fun g => σ (P * g * P⁻¹)) S w := by
  obtain ⟨S₁, hS₁, -, ⟨B, hB, hc⟩, A, hA, hd⟩ := GlobalTheory.TypeSumCtrl.exists_ctrl n ε H σ hσ
    (S₀.map fun l => l.map fun X => P * X * P⁻¹) (by
      intro l hl X hX
      obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
      obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
      exact GlobalTheory.SmVecModel.lie_conj hP hG (hS₀ l' hl' Y hY))
  refine ⟨S₁.map fun l => l.map fun X => P⁻¹ * X * P, ?_,
    ⟨fun g => B (P * g * P⁻¹), hB.comp (by fun_prop), fun g hg w hw => ?_⟩, A, hA, fun w hw => ?_⟩
  · intro l hl X hX
    obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
    obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
    exact GlobalTheory.SmVecModel.lie_conj_inv hP hG (hS₁ l' hl' Y hY)
  · rw [sobNorm_conj_back σ hP, sobNorm_conj_back σ hP]
    exact hc _ (GlobalTheory.TypeAtCompare.conj_mem hP hG hg) w (GlobalTheory.SmVecModel.smoothVec_of_conj hP hG hw)
  · rw [sobNorm_conj_back σ hP, sobNorm_conj σ hP]
    exact hd w (GlobalTheory.SmVecModel.smoothVec_of_conj hP hG hw)

theorem smoothVec_zero (Lie : Set (Mx n)) (σ : Mx n → (H →L[ℂ] H)) : SmoothVec Lie σ (0 : H) := by
  intro k Xs _
  simp only [map_zero]
  exact contDiff_const

theorem hasTypeAll_single [CompleteSpace H] {ε : Fin n → Bool} {σ : Mx n → (H →L[ℂ] H)} (hσ : Std ε σ) {P G : Mx n}
    (hP : IsUnit P) (hG : Pᴴ * Jm ε * P = G) {u : H} (hu : SmoothVec (lieOf G) (fun g => σ (P * g * P⁻¹)) u)
    {ℓ : H →ₗ[ℂ] ℂ} (hℓ : Sobolev₂ (lieOf G) (fun g => σ (P * g * P⁻¹)) ℓ) {f : Mx n → ℂ}
    (hf : ∀ g ∈ Formalism.QuantumDeterminants.UH G, ℓ (σ (P * g * P⁻¹) u) = f g) :
    HasTypeAll (lieOf G) (Formalism.QuantumDeterminants.UH G) (fun g => σ (P * g * P⁻¹)) f := by
  obtain ⟨S₀, C₀, hS₀, hb⟩ := hℓ
  obtain ⟨S, hS, hc, A, hA, hd⟩ := exists_ctrl_conj hσ hP hG S₀ hS₀
  have hv : ∀ i, SmoothVec (lieOf G) (fun g => σ (P * g * P⁻¹)) ((Pi.single 0 u : ℕ → H) i) := fun i => by
    by_cases hi : i = 0
    · subst hi; simpa using hu
    · rw [Pi.single_eq_of_ne hi]; exact smoothVec_zero _ _
  refine ⟨S, hS, hc, Pi.single 0 u, fun i => if i = 0 then ℓ else 0, Pi.single 0 (|C₀| * A),
    ⟨⟨hv, fun i => ?_, fun i w hw => ?_, ?_, fun g hg => ?_⟩, fun S' _ => ?_⟩⟩
  · by_cases hi : i = 0
    · subst hi; simp only [Pi.single_eq_same]; positivity
    · rw [Pi.single_eq_of_ne hi]
  · by_cases hi : i = 0
    · subst hi
      simp only [if_true, Pi.single_eq_same]
      have h1 := hb w hw
      have h2 := hd w hw
      have h3 : 0 ≤ sobNorm (fun g => σ (P * g * P⁻¹)) S₀ w := sobNorm_nonneg _ _ _
      have h4 : C₀ * sobNorm (fun g => σ (P * g * P⁻¹)) S₀ w ≤ |C₀| * sobNorm (fun g => σ (P * g * P⁻¹)) S₀ w :=
        mul_le_mul_of_nonneg_right (le_abs_self _) h3
      calc ‖ℓ w‖ ≤ C₀ * sobNorm (fun g => σ (P * g * P⁻¹)) S₀ w := h1
        _ ≤ |C₀| * sobNorm (fun g => σ (P * g * P⁻¹)) S₀ w := h4
        _ ≤ |C₀| * (A * sobNorm (fun g => σ (P * g * P⁻¹)) S w) := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
        _ = |C₀| * A * sobNorm (fun g => σ (P * g * P⁻¹)) S w := by ring
    · simp [hi, Pi.single_eq_of_ne hi]
  · refine (hasSum_single 0 fun i hi => ?_).summable
    simp [Pi.single_eq_of_ne hi]
  · rw [← hf g hg]
    have := hasSum_single (f := fun i : ℕ => (if i = 0 then ℓ else 0) (σ (P * g * P⁻¹) ((Pi.single 0 u : ℕ → H) i))) 0
      fun i hi => by simp [hi]
    simpa using this
  · refine (hasSum_single 0 fun i hi => ?_).summable
    simp [Pi.single_eq_of_ne hi]

end Model

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Matrix
open GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum

theorem isTypeAt_value {D : D7} (θ : InfFam D)
    (hHC : GlobalTheory.Published.HarishChandraModules) {V : HSp D} {Sp : D.what₂.Tau → SPar} (M : DSModel V Sp)
    {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M} (hT : IsMultMap θ M J χ T) (v : M.Vec) (τ : D.what₂.Tau) :
    IsTypeAt θ V τ (Sp τ) (T v) := by
  have hD := M.ds τ
  haveI : CompleteSpace (M.H τ) := hD.1
  have hσ : Std (M.ε τ) (M.σ τ) := std_of_isDS hHC hD
  refine ⟨M.H τ, _, _, M.σ τ, M.lam τ, M.ε τ, M.fr τ, M.enum τ, hD, M.fr_unit τ, M.fr_gram τ, fun x => ?_⟩
  obtain ⟨ℓ, hℓ, hℓv⟩ := hT.cont τ v x
  have hu : SmoothVec (lieAt V τ) (fun g => M.σ τ (M.fr τ * g * (M.fr τ)⁻¹)) (v τ : M.H τ) :=
    GlobalTheory.SmVecModel.smoothVec_to_conj (M.fr_unit τ) (M.fr_gram τ) ((GlobalTheory.SmVecModel.mem_sm_iff M τ _).1 (v τ).2)
  have hall : HasTypeAll (lieOf (gramAt D V τ)) (Formalism.QuantumDeterminants.UH (gramAt D V τ))
      (fun g => M.σ τ (M.fr τ * g * (M.fr τ)⁻¹)) (fun g => T v (x * atTau θ V τ g)) := by
    refine hasTypeAll_single hσ (M.fr_unit τ) (M.fr_gram τ) hu hℓ fun g hg => ?_
    have h1 := hT.equiv τ g hg v ⟨M.rep τ g (v τ), GlobalTheory.ConjMult.rep_mem_sm M τ hg (v τ).2⟩ rfl
    have h2 := hℓv ⟨M.rep τ g (v τ), GlobalTheory.ConjMult.rep_mem_sm M τ hg (v τ).2⟩
    show ℓ (M.rep τ g (v τ)) = _
    rw [h2, h1]
    rfl
  exact hasTypeAll_iff.1 hall

end GlobalTheory.CuspValueType

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagonalFixingDoublingMatrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.SplitDblGen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

abbrev dC (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) :
    Matrix (Fin d ⊕ Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) := diagCols (Fin d)

def half : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) := algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (⅟(2 : AF F))

def diagonalFixingDoublingMatrix (c : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (d : ℕ) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
  1 + (half * c) • (dC F E d * (GlobalTheory.InertDbl.antiCols d)ᵀ)

def splitDoublingNBlock {d : ℕ} (c : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (K K' : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
  ((half : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) * half * half) • ((1 - c) • (K - 1) - (1 + c) • (K' - 1))

def nMat {d : ℕ} (c : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (K K' : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
  let nBlock : Matrix (Fin d ⊕ Fin d) (Fin d) _ :=
    GlobalTheory.InertDbl.antiCols d * splitDoublingNBlock c K K'
  1 + nBlock * (dC F E d)ᵀ

def tMat {d : ℕ} (c : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (K : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
  1 + (half * (1 + c)) • (K - 1)

end GlobalTheory.SplitDblGen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowMapVUpdateZero
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.LastVertexInv

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FirstRowVertex

open GlobalTheory.LastVertexInv

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

def firstIx (D : D7) : Fin D.R.m := ⟨0, by have := D.R.two_le_m; omega⟩

def rowShift0 (S : GridChoice W U) (k : FinPt G (.grid 0 D.R.m)) :
    (WO (G.pS (.chi (firstIx D) D.R.m : Pair T)) (G.pT (.chi (firstIx D) D.R.m : Pair T)) → ℂ) →ₗ[ℂ]
      (WO (G.pS (.chi (firstIx D) D.R.m : Pair T)) (G.pT (.chi (firstIx D) D.R.m : Pair T)) → ℂ) :=
  W.om (.chi (firstIx D) D.R.m) (G.toPair (.chi (firstIx D) D.R.m)
    ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1)

theorem rowShift0_theta (S : GridChoice W U) (k : FinPt G (.grid 0 D.R.m))
    {f : WO (G.pS (.chi (firstIx D) D.R.m : Pair T)) (G.pT (.chi (firstIx D) D.R.m : Pair T)) → ℂ}
    (h : IsThetaFunO W.ψ _ _ f) : IsThetaFunO W.ψ _ _ (rowShift0 S k f) :=
  (W.om_is _ (inRange_chi (firstIx D))).om_pres _ _ h

def movedRow (S : GridChoice W U) (k : FinPt G (.grid 0 D.R.m))
    (gs : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ) :
    ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ :=
  Function.update gs (firstIx D) (rowShift0 S k (gs (firstIx D)))

theorem rowMapV_update_zero (S : GridChoice W U)
    (gs : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ)
    (y : ∀ i, FinPt G (.grid i D.R.m)) (k : FinPt G (.grid 0 D.R.m))
    (hg : IsThetaFunO W.ψ (G.pS (.chi (firstIx D) D.R.m : Pair T)) (G.pT (.chi (firstIx D) D.R.m : Pair T)) (gs (firstIx D))) :
    rowMapV S gs (Function.update y 0 (y 0 * k)) = rowMapV S (movedRow S k gs) y := by
  unfold rowMapV movedRow
  refine congrArg (fun F => LinearMap.comp (chainTo (V := fun i => VV ℂ (wt G (.grid i D.R.m))) F D.R.m) _) ?_
  funext i
  by_cases hi : i < D.R.m
  · simp only [dif_pos hi]
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0
      simp only [Function.update_self, Function.update_of_ne (show (0 + 1 : ℕ) ≠ 0 by omega)]
      have hu : Function.update gs (firstIx D) (rowShift0 S k (gs (firstIx D))) ⟨0, hi⟩ = rowShift0 S k (gs (firstIx D)) :=
        Function.update_self _ _ _
      have hm : y 0 * k * S.N.u (.grid 0 D.R.m) =
          (y 0 * S.N.u (.grid 0 D.R.m)) * ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)) := by group
      rw [hu, hm]
      exact congrArg _ (GlobalTheory.KerTrans.fockComp_mul_fin W S.N.frC (inRange_chi (firstIx D)) _ hg _ _ _)
    · have h2 : (⟨i, hi⟩ : Fin D.R.m) ≠ firstIx D := by
        intro h; have := congrArg Fin.val h; simp [firstIx] at this; omega
      have hu : Function.update gs (firstIx D) (rowShift0 S k (gs (firstIx D))) ⟨i, hi⟩ = gs ⟨i, hi⟩ :=
        Function.update_of_ne h2 _ _
      have hy1 : Function.update y 0 (y 0 * k) i = y i := Function.update_of_ne (by omega) _ _
      have hy2 : Function.update y 0 (y 0 * k) (i + 1) = y (i + 1) := Function.update_of_ne (by omega) _ _
      rw [hu, hy1, hy2]
  · simp only [dif_neg hi]

theorem prod_update_smul {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type} (F : ∀ i, X i → ℂ) (i₀ : ι) (h : X i₀ → ℂ)
    (c : ℂ) (ys : ∀ i, X i) :
    ∏ i, Function.update F i₀ (c • h) i (ys i) = c * ∏ i, Function.update F i₀ h i (ys i) := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i₀), ← Finset.mul_prod_erase _ _ (Finset.mem_univ i₀)]
  simp only [Function.update_self, Pi.smul_apply, smul_eq_mul, mul_assoc]
  congr 2
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hi), Function.update_of_ne (Finset.ne_of_mem_erase hi)]

end GlobalTheory.FirstRowVertex

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftsCuspidalOfFunctoriality
namespace GlobalTheory.PairLift

theorem liftsCuspidal_of_functoriality (hD : GlobalTheory.Published.DiscreteSeriesCover) (hH : GlobalTheory.Published.HarishChandraModules)
    (hC : GlobalTheory.Published.CuspRapidDecay) (hW : GlobalTheory.Published.CasselmanWallach) : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal := by
  obtain ⟨X, hX, -, -, h3, h4, h5⟩ := GlobalTheory.T.exists_real_discreteSeries_data_theta_properties hD hH
  have I := fun D => GlobalTheory.T.thetaPairAnalyticHypotheses_of_discreteSeries hD hH hC hW D X hX
  exact liftsCuspidal X hX h3 h4 h5 hH hC (fun D => (I D).bridge) (fun D => (I D).vacChar) (fun D => (I D).lie)
    (fun D => (I D).cpt) (fun D => (I D).dense) (fun D => (I D).laws) (fun D => (I D).const) (fun D => (I D).ext)

end GlobalTheory.PairLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetIdlVal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv GlobalTheory.SplitFlip
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section

namespace GlobalTheory.RowVacScalar

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

def idemAt (w : Pl D.host.E) : AE D := Classical.epsilon fun e : AE D => Formalism.L2.NTheta.IsIdemAt e w


open Classical in
def detIdl (e : AE D) (V : HSp D) (g : GA D V) : (AE D)ˣ :=
  if he : e * e = e then GlobalTheory.VecInv.detAt e he V g else 1


open Classical in
theorem detIdl_val {e : AE D} (he : e * e = e) (V : HSp D) (g : GA D V) :
    ((detIdl e V g : (AE D)ˣ) : AE D) = e * (Formalism.L2.Theta.mt V g).det + (1 - e) := by
  rw [detIdl, dite_eq_left he]; rfl

def splitScal (G : GridData L sc) (p : Pair T) (w : Pl D.host.E) (g : GA D (G.pS p)) (h : GA D (G.pT p)) : ℂ :=
  ((splitFacO (G.chrS p) (G.chrT p) (detIdl (idemAt w) (G.pS p) g) (detIdl (idemAt w) (G.pT p) h) : Circle) : ℂ)

end GlobalTheory.RowVacScalar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DifferentiableIntertwiningPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

namespace GlobalTheory.MovedDict.Entire

theorem differentiable_U' {D : D7} {T : Tor D} {N N' : ℕ} (x : VC D N N') {G : VC D N N' → ℂ}
    (hG : Differentiable ℂ G) : Differentiable ℂ (U D T x G) := by
  have h : Differentiable ℂ (fun z : VC D N N' => Hf D T z x) := by
    unfold Hf
    fun_prop
  unfold U
  fun_prop

theorem differentiable_Iop' {D : D7} {T : Tor D} {N N' : ℕ} (A B : AddSubgroup (VC D N N'))
    {G : VC D N N' → ℂ} (hG : Differentiable ℂ G) : Differentiable ℂ (Iop D T A B G) := by
  unfold Iop
  by_cases h : (A.addSubgroupOf B).index = 0
  · simp [h]
  · haveI : Finite (B ⧸ A.addSubgroupOf B) := Nat.finite_of_card_ne_zero h
    haveI := Fintype.ofFinite (B ⧸ A.addSubgroupOf B)
    simp only [finsum_eq_sum_of_fintype]
    exact (Differentiable.fun_sum fun q _ => (differentiable_U' _ hG).const_mul _).const_mul _

end GlobalTheory.MovedDict.Entire
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RankPolynomialFockSchrodingerModelLeAleph0
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RankPolynomialFockSchrodingerModelLeAleph0
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM

noncomputable section

namespace GlobalTheory.FockCount

open NumberField

theorem incM_map_piInf' {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n m : Type}
    (J : Matrix n m E) {w : InfinitePlace F} (τ : GlobalTheory.AdelicU.EmbOver E w) :
    (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F J).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf τ) = J.map τ.1 := by
  ext i j
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf, GlobalTheory.AdelicU.compInf, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR,
    GlobalTheory.AdelicU.infEmb_tmul]

theorem rank_tens_le (F : Type) [Field F] [NumberField F] (P Q R S : ℕ) :
    Module.rank ℂ (GlobalTheory.RealLift.Tens F P Q R S) ≤ Cardinal.aleph0 := by
  classical
  let b := _root_.Basis.piTensorProduct (R := ℂ)
    (fun _ : InfinitePlace F => MvPolynomial.basisMonomials (Formalism.BasicNotions.TH.Ix P Q × Formalism.BasicNotions.TH.Ix R S) ℂ)
  rw [← b.mk_eq_rank'']
  exact Cardinal.mk_le_aleph0

theorem rank_pol_le_aleph0 : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) {n d r s r' s' : ℕ} {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d}
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W),
    B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ →
    Module.rank ℂ (M.Pol B.ψ B.emb) ≤ Cardinal.aleph0 := by
  intro F E _ _ _ _ _ σ B n d r s r' s' X W M hB hX hW _hM
  classical
  have hcm := hB.cm
  have hstd := hB.std
  have hFr : ∀ w, ∃ A : Matrix (Fin n) (Formalism.BasicNotions.TH.Ix r s) ℂ,
      GlobalTheory.RealLift.IsFrame ((1 : ℂ) • (incM F X.J).map (piInf (B.emb w))) A ∧ X.θ w * A = A * Formalism.BasicNotions.TH.Jm r s := by
    intro w
    rw [incM_map_piInf', one_smul]
    exact GlobalTheory.T.cartanEigen_orthonormalFrame_exists n r s _ _ (hX.sig w) (hX.cartan w)
  have hFrW : ∀ w, ∃ C : Matrix (Fin d) (Formalism.BasicNotions.TH.Ix r' s') ℂ,
      GlobalTheory.RealLift.IsFrame (Complex.I • (incM F W.J).map (piInf (B.emb w))) C ∧
        W.θ w * C = C * Formalism.BasicNotions.TH.Jm r' s' := by
    intro w
    rw [incM_map_piInf']
    exact GlobalTheory.T.cartanEigen_orthonormalFrame_exists d r' s' _ _ (hW.sig w) (hW.cartan w)
  choose A hA hAθ using hFr
  choose C hC hCθ using hFrW
  have hFramed : GlobalTheory.RealLift.Framed B.emb (incM F X.J) (incM F W.J) 1 Complex.I A C :=
    ⟨one_mul _, hA, hC⟩
  have hder := GlobalTheory.T.archHeisenbergDerivatives_exist
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.fockToSchrodingerMapExists_of_archHeisenbergDerivatives hder F E σ (Fin n) (Fin d) (Fin n × Fin d) r s r' s' B.ψ B.emb (incM F X.J)
    (incM F W.J) M.co 1 Complex.I A C hcm hstd hFramed
  have hrange := GlobalTheory.T.fockPolynomialSpace_eq_fockImage_of_arch_laws GlobalTheory.RealLift.actsLaws hder (GlobalTheory.T.schwartzFockVacuumLineUnique_of_heisenberg_derivatives hder) F E σ n d r s r' s' X W M B.ψ B.emb A C Φ
    hcm hstd hFramed hAθ hCθ hΦ
  rw [← hrange]
  exact (rank_range_le Φ).trans (rank_tens_le F r s r' s')

end GlobalTheory.FockCount
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RankPolynomialFockSchrodingerModelLeAleph0Statement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_polynomialFock_schrodingerModel_le_aleph0 : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) {n d r s r' s' : ℕ} {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d}
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W),
    B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ →
    Module.rank ℂ (M.Pol B.ψ B.emb) ≤ Cardinal.aleph0 := by
  first | exact @GlobalTheory.FockCount.rank_pol_le_aleph0 | exact GlobalTheory.FockCount.rank_pol_le_aleph0 | (intros; apply GlobalTheory.FockCount.rank_pol_le_aleph0 <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticesSelfDualMovedPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

set_option maxHeartbeats 800000

namespace GlobalTheory.MovedSD

open Matrix

open Formalism.UG in
theorem colLat_one_eq_stdLat (D : D7) (n : ℕ) :
    colLat (1 : GL (Fin n) D.host.E) = Formalism.L2.Col.stdLat D.host.E n := by
  ext x
  rw [GlobalTheory.TestLat.Inhabitant.mem_colLat_one]
  simp [Formalism.L2.Col.stdLat, Submodule.mem_pi, Submodule.mem_one]

theorem move_vec (D : D7) {n : ℕ} (fr : GL (Fin n) D.host.E) (a b : GL (Fin n) (Lev.EAf D)) (v : Fin n → D.host.E) :
    (fr⁻¹).val.map (eToEAf D) *ᵥ ((b⁻¹).val *ᵥ ((a⁻¹).val *ᵥ fun i => Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) ((fr.val *ᵥ v) i))) =
      (Formalism.UG.bc (eToEAf D) fr⁻¹ * b⁻¹ * a⁻¹ * Formalism.UG.bc (eToEAf D) fr).val *ᵥ fun i => Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) (v i) := by
  have hb : ∀ g : GL (Fin n) D.host.E, (Formalism.UG.bc (eToEAf D) g).val = g.val.map (eToEAf D) := fun _ => rfl
  have ev : (fun i => Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) ((fr.val *ᵥ v) i)) =
      fr.val.map (eToEAf D) *ᵥ fun i => Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) (v i) := by
    funext i
    exact RingHom.map_mulVec (eToEAf D) fr.val v i
  rw [ev]
  simp only [Units.val_mul, hb, Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem mem_globLat_move (D : D7) {n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (fr : GL (Fin n) D.host.E)
    (a b : GL (Fin n) (Lev.EAf D))
    (hu : ∀ w, w ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) ↔ b.val *ᵥ w ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ)
    (v : Fin n → D.host.E) :
    fr.val *ᵥ v ∈ Formalism.UG.CS.globLat a Λ ↔
      v ∈ Formalism.UG.CS.globLat (Formalism.UG.bc (eToEAf D) fr⁻¹ * (a * b) * Formalism.UG.bc (eToEAf D) fr) (Formalism.L2.Col.stdLat D.host.E n) := by
  change (_ ∈ Formalism.L2.Herm.hatL (F := D.host.F) _) ↔ (_ ∈ Formalism.L2.Herm.hatL (F := D.host.F) _)
  generalize hw : ((a⁻¹).val *ᵥ fun i => Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) ((fr.val *ᵥ v) i)) = w
  have h1 := hu ((b⁻¹).val *ᵥ w)
  have e1 : b.val *ᵥ ((b⁻¹).val *ᵥ w) = w := by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  rw [e1] at h1
  rw [← h1]
  have hm := GlobalTheory.LatMulAd.mem_hatL_colLat_mul D fr 1 ((b⁻¹).val *ᵥ w)
  rw [mul_one, colLat_one_eq_stdLat] at hm
  rw [hm, ← hw]
  have eg : ((Formalism.UG.bc (eToEAf D) fr⁻¹ * (a * b) * Formalism.UG.bc (eToEAf D) fr)⁻¹ : GL (Fin n) (Lev.EAf D)) =
      Formalism.UG.bc (eToEAf D) fr⁻¹ * b⁻¹ * a⁻¹ * Formalism.UG.bc (eToEAf D) fr := by
    simp only [_root_.mul_inv_rev, ← map_inv, inv_inv, mul_assoc]
  rw [eg]
  refine Iff.of_eq (congrArg (· ∈ Formalism.L2.Herm.hatL (F := D.host.F) (Formalism.L2.Col.stdLat D.host.E n)) ?_)
  exact move_vec D fr a b v

theorem cT_map_inclE (D : D7) {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E) :
    Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) (M.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F))) =
      (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) M).map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) := by
  ext i j
  simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply]
  rfl

theorem move_mem_UAd (D : D7) {n : ℕ} (J : Matrix (Fin n) (Fin n) D.host.E) (fr : GL (Fin n) D.host.E)
    (hfr : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.val * J * fr.val = 1) (a b : GL (Fin n) (Lev.EAf D))
    (ha : a ∈ Formalism.L2.DIV.UA D.sp.cm J) (hb : b ∈ Formalism.L2.DIV.UA D.sp.cm J) :
    Formalism.UG.bc (eToEAf D) fr⁻¹ * (a * b) * Formalism.UG.bc (eToEAf D) fr ∈ Formalism.L2.Col.UAd D.sp.cm n := by
  have hab : Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) (a * b).val *
      J.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) * (a * b).val =
      J.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) := mul_mem ha hb
  set A := (a * b).val
  set ι := Formalism.UG.inclE (F := D.host.F) (E := D.host.E) (Formalism.L2.Herm.Af D.host.F)
  set σR := Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)
  have hm : ∀ g : GL (Fin n) D.host.E, (Formalism.UG.bc (eToEAf D) g).val = g.val.map ι := fun _ => rfl
  have hF : Formalism.UG.cT σR (fr.val.map ι) * J.map ι * fr.val.map ι = 1 := by
    rw [cT_map_inclE, ← Matrix.map_mul, ← Matrix.map_mul, hfr, Matrix.map_one _ (map_zero _) (map_one _)]
  have h1 : fr.val.map ι * (fr⁻¹).val.map ι = 1 := by
    rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hJ : Formalism.UG.cT σR ((fr⁻¹).val.map ι) * (fr⁻¹).val.map ι = J.map ι := by
    calc Formalism.UG.cT σR ((fr⁻¹).val.map ι) * (fr⁻¹).val.map ι
        = Formalism.UG.cT σR ((fr⁻¹).val.map ι) * (Formalism.UG.cT σR (fr.val.map ι) * J.map ι * fr.val.map ι) * (fr⁻¹).val.map ι := by
          rw [hF, Matrix.mul_one]
      _ = Formalism.UG.cT σR (fr.val.map ι * (fr⁻¹).val.map ι) * J.map ι * (fr.val.map ι * (fr⁻¹).val.map ι) := by
          rw [Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
      _ = J.map ι := by
          rw [h1]; simp [Formalism.UG.cT]
  show Formalism.UG.cT σR (_ : GL (Fin n) (Lev.EAf D)).val * (1 : Matrix (Fin n) (Fin n) D.host.E).map ι * _ = _
  rw [Units.val_mul, Units.val_mul, hm, hm, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
  calc Formalism.UG.cT σR ((fr⁻¹).val.map ι * A * fr.val.map ι) * ((fr⁻¹).val.map ι * A * fr.val.map ι)
      = Formalism.UG.cT σR (fr.val.map ι) * (Formalism.UG.cT σR A * (Formalism.UG.cT σR ((fr⁻¹).val.map ι) * (fr⁻¹).val.map ι) * A) * fr.val.map ι := by
        rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hJ, hab, hF]

theorem sd_latAt {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {W : G.Weil}
    (S : GridChoice W Set.univ) (X : Node) (hX : DefNode D.R.m X) (x : FinPt G X) : SD D (GlobalTheory.SumSize.latAt S X x) := by
  have e : GlobalTheory.SumSize.latAt S X x = Formalism.UG.CS.globLat (Formalism.UG.bc (eToEAf D) (S.N.fr X)⁻¹ *
      (finG (G.V X) x * Lev.finE (G.V X) (S.N.u X : Formalism.L2.Theta.GA D (G.V X))) * Formalism.UG.bc (eToEAf D) (S.N.fr X))
      (Formalism.L2.Col.stdLat D.host.E _) := by
    ext v
    exact mem_globLat_move D (G.Λ X) (S.N.fr X) _ _ (S.N.u_lat X hX) v
  have ha : finG (G.V X) x ∈ Formalism.L2.DIV.UA D.sp.cm (G.V X).gram := GlobalTheory.LevSplit.finE_mem_UA (G.V X) x.1
  have hb := GlobalTheory.LevSplit.finE_mem_UA (G.V X) (S.N.u X : Formalism.L2.Theta.GA D (G.V X))
  show IsSDLat D.host.E _ _
  rw [e]
  exact Formalism.L2.Col.DetChrChi.isSDLat_globLat D.sp.cm (move_mem_UAd D _ _ (S.N.fr_on X hX) _ _ ha hb)

end GlobalTheory.MovedSD
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepresentationIntegralAction
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepresentationIntegralAction
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open GlobalTheory.ArchUniq MeasureTheory
open scoped SchwartzMap Classical

noncomputable section

namespace GlobalTheory.ArchIsom

variable {F : Type} [Field F] [NumberField F]

theorem continuous_toMixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  have : (InfiniteAdeleRing.ringEquiv_mixedSpace F : InfiniteAdeleRing F → mixedEmbedding.mixedSpace F) =
      fun x => ((fun v : {w : InfinitePlace F // InfinitePlace.IsReal w} =>
          InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
        (fun v : {w : InfinitePlace F // InfinitePlace.IsComplex w} =>
          InfinitePlace.Completion.extensionEmbedding v.1 (x v))) := by
    funext x; exact InfiniteAdeleRing.ringEquiv_mixedSpace_apply F x
  rw [this]
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp
      (continuous_apply _)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp
      (continuous_apply _)


variable (F) in
def splitEquiv (κ : Type) :
    ((κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F)) ≃+ (κ → AF F) where
  toFun p := fun i => (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 i), p.2 i) : AF F)
  invFun x := (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1, fun i => (x i).2)
  left_inv p :=
    Prod.ext (funext fun i => (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply (p.1 i)) rfl
  right_inv x := by
    funext i
    exact Prod.ext ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm_apply_apply _) rfl
  map_add' p q := by
    funext i
    exact Prod.ext (map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 i) (q.1 i)) rfl

theorem continuous_splitEquiv (κ : Type) : Continuous (splitEquiv F κ) := by
  refine continuous_pi fun i => ?_
  exact ((GlobalTheory.HeckeOne.continuous_ringEquiv_mixedSpace_symm F).comp
    ((continuous_apply i).comp continuous_fst)).prodMk ((continuous_apply i).comp continuous_snd)

theorem continuous_splitEquiv_symm (κ : Type) : Continuous (splitEquiv F κ).symm := by
  refine (continuous_pi fun i => ?_).prodMk (continuous_pi fun i => ?_)
  · exact continuous_toMixed.comp (continuous_fst.comp (continuous_apply i))
  · exact continuous_snd.comp (continuous_apply i)

theorem evI_splitEquiv (κ : Type) (p : (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F))
    (i : κ) : evI F (splitEquiv F κ p i) = p.1 i :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply _


variable (F) in
def intPts (κ : Type) : Set (κ → FiniteAdeleRing (𝓞 F) F) :=
  Set.univ.pi fun _ => {b | ∀ v : HeightOneSpectrum (𝓞 F), b.1 v ∈ v.adicCompletionIntegers F}

theorem isCompact_intPts (κ : Type) : IsCompact (intPts F κ) :=
  isCompact_univ_pi fun _ => GlobalTheory.LatHatClosed.isCompact_integralFinite F

theorem isOpen_intPts (κ : Type) [Finite κ] : IsOpen (intPts F κ) :=
  isOpen_set_pi Set.finite_univ fun _ _ =>
    RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring _)

theorem zero_mem_intPts (κ : Type) : (0 : κ → FiniteAdeleRing (𝓞 F) F) ∈ intPts F κ :=
  fun _ _ v => zero_mem (v.adicCompletionIntegers F)


variable (F) in
def g0 (κ : Type) : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ := (intPts F κ).indicator 1


variable (F) in
def r0 (κ : Type) : (κ → AF F) → ℂ := fun x => g0 F κ (fun i => (x i).2)

theorem standard_vector_mem_schwartz_bruhat (κ : Type) [Fintype κ] : g0 F κ ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) := by
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  have hc : IsCompact (intPts F κ) := isCompact_intPts κ
  have hW : IsClopen (intPts F κ) := ⟨hc.isClosed, isOpen_intPts κ⟩
  refine ⟨?_, HasCompactSupport.intro' hc hW.isClosed fun x hx => Set.indicator_of_notMem hx _⟩
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ intPts F κ
  · filter_upwards [hW.isOpen.mem_nhds hx] with y hy
    simp [g0, Set.indicator_of_mem hy, Set.indicator_of_mem hx]
  · filter_upwards [hW.isClosed.isOpen_compl.mem_nhds hx] with y hy
    simp [g0, Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

theorem tensor_at_standard_point (κ : Type) (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) :
    tens (evI F) f (r0 F κ) = pureA F f (g0 F κ) := rfl

theorem restriction_at_standard_point (κ : Type) [Fintype κ] (f : SInf F κ) : Rest (evI F) (⇑f) (r0 F κ) := by
  refine ⟨fun x z hz => ?_, ?_⟩
  · have hz2 : ∀ i, (z i).2 = 0 := by
      intro i
      let u : AF F := show AF F from (0, 1)
      have h0 : evI F u = 0 := map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
      have h := congrFun (hz u h0) i
      have h2 := congrArg Prod.snd h
      have h4 : ((u • z) i).2 = (1 : FiniteAdeleRing (𝓞 F) F) * (z i).2 := rfl
      rw [h4, one_mul] at h2
      exact h2
    show g0 F κ (fun i => (x i + z i).2) = g0 F κ (fun i => (x i).2)
    congr 1
    funext i
    show (x i).2 + (z i).2 = (x i).2
    rw [hz2 i, add_zero]
  · rw [tensor_at_standard_point]
    exact Submodule.subset_span ⟨f, g0 F κ, standard_vector_mem_schwartz_bruhat κ, rfl⟩

end GlobalTheory.ArchIsom

namespace GlobalTheory.ArchIsom

variable {F : Type} [Field F] [NumberField F]

theorem lintegral_tensor_at_standard_point (κ : Type) [Fintype κ] (μ : Measure (κ → mixedEmbedding.mixedSpace F))
    [mB : MeasurableSpace (κ → FiniteAdeleRing (𝓞 F) F)] [BorelSpace (κ → FiniteAdeleRing (𝓞 F) F)]
    (ν : Measure (κ → FiniteAdeleRing (𝓞 F) F)) [SFinite ν]
    [mA : MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)]
    (e : ((κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F)) ≃ᵐ (κ → AF F))
    (he : ∀ p, e p = splitEquiv F κ p) (g : SInf F κ) :
    ∫⁻ x, ‖tens (evI F) (⇑g) (r0 F κ) x‖ₑ ^ 2 ∂(Measure.map e (μ.prod ν)) =
      (∫⁻ y, ‖g y‖ₑ ^ 2 ∂μ) * ν (intPts F κ) := by
  rw [lintegral_map_equiv]
  haveI : BorelSpace (κ → mixedEmbedding.mixedSpace F) := inferInstance
  have hpt : ∀ p : (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F),
      ‖tens (evI F) (⇑g) (r0 F κ) (e p)‖ₑ ^ 2 = ‖g p.1‖ₑ ^ 2 * (intPts F κ).indicator 1 p.2 := by
    intro p
    have h1 : (fun i => evI F (e p i)) = p.1 := funext fun i => by rw [he]; exact evI_splitEquiv κ p i
    have h2 : (fun i => (e p i).2) = p.2 := funext fun i => by rw [he]; rfl
    simp only [tens, r0, h1, h2, g0, enorm_mul, mul_pow]
    congr 1
    by_cases hp : p.2 ∈ intPts F κ
    · simp [Set.indicator_of_mem hp]
    · simp [Set.indicator_of_notMem hp]
  simp_rw [hpt]
  have hm := lintegral_prod_mul (μ := μ) (ν := ν) (f := fun y => ‖g y‖ₑ ^ 2)
    (g := (intPts F κ).indicator 1) (g.continuous.measurable.enorm.pow_const 2).aemeasurable
    ((measurable_one.indicator (isOpen_intPts κ).measurableSet).aemeasurable)
  rw [lintegral_indicator_one (isOpen_intPts κ).measurableSet] at hm
  exact hm

end GlobalTheory.ArchIsom

namespace GlobalTheory.ArchIsom

theorem acts_norm_sq_eq : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    M.IsWeil ψ χX χW om → ∀ (μ : Measure (Fin n × Fin d → mixedEmbedding.mixedSpace F)), μ.IsAddHaarMeasure →
    ∀ (h : UA σ W.J) (f f₁ : SInf F (Fin n × Fin d)), Acts (evI F) (om (1, h)) ⇑f ⇑f₁ →
      ∫ x, ‖f₁ x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  intro F E _ _ _ _ _ σ n d X W M ψ χX χW om hW μ hμ h f f₁ hact
  have hU := (IsUWeilPair.isUSplitting hW).unit
  haveI := hμ
  have hΦ := hact (r0 F (Fin n × Fin d)) (restriction_at_standard_point _ f)
  letI mB : MeasurableSpace (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  letI mA : MeasurableSpace (Fin n × Fin d → AF F) := borel _
  haveI : BorelSpace (Fin n × Fin d → AF F) := ⟨rfl⟩
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  haveI : BorelSpace (Fin n × Fin d → mixedEmbedding.mixedSpace F) := inferInstance
  let ν : Measure (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) := Measure.addHaar
  let H : ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F)) ≃ₜ
      (Fin n × Fin d → AF F) :=
    { (splitEquiv F (Fin n × Fin d)).toEquiv with
      continuous_toFun := continuous_splitEquiv _
      continuous_invFun := continuous_splitEquiv_symm _ }
  let e := H.toMeasurableEquiv
  have he : ∀ p, e p = splitEquiv F (Fin n × Fin d) p := fun _ => rfl
  haveI : SigmaFinite ν := inferInstance
  haveI : SigmaFinite μ := inferInstance
  have hμ' : (Measure.map e (μ.prod ν)).IsAddHaarMeasure :=
    (splitEquiv F (Fin n × Fin d)).isAddHaarMeasure_map (μ.prod ν) (continuous_splitEquiv _)
      (continuous_splitEquiv_symm _)
  have hmem : tens (evI F) (⇑f) (r0 F (Fin n × Fin d)) ∈ schA F (Fin n × Fin d) := (restriction_at_standard_point _ f).2
  have hu := hU (Measure.map e (μ.prod ν)) hμ' (1, h) _ hmem
  rw [hΦ, lintegral_tensor_at_standard_point _ μ ν e he, lintegral_tensor_at_standard_point _ μ ν e he] at hu
  have hc0 : ν (intPts F (Fin n × Fin d)) ≠ 0 :=
    ((isOpen_intPts _).measure_pos ν ⟨0, zero_mem_intPts _⟩).ne'
  have hct : ν (intPts F (Fin n × Fin d)) ≠ ⊤ := (isCompact_intPts _).measure_lt_top.ne
  have hl := (ENNReal.mul_left_inj hc0 hct).mp hu
  rw [integral_eq_lintegral_of_nonneg_ae (f := fun x => ‖f₁ x‖ ^ 2) (Filter.Eventually.of_forall fun _ => by positivity)
      ((f₁.continuous.norm.pow 2 : Continuous fun x => ‖f₁ x‖ ^ 2).aestronglyMeasurable),
    integral_eq_lintegral_of_nonneg_ae (f := fun x => ‖f x‖ ^ 2) (Filter.Eventually.of_forall fun _ => by positivity)
      ((f.continuous.norm.pow 2 : Continuous fun x => ‖f x‖ ^ 2).aestronglyMeasurable)]
  congr 1
  simp_rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  exact hl

end GlobalTheory.ArchIsom
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepresentationIntegralActionStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open GlobalTheory.ArchUniq MeasureTheory
open scoped SchwartzMap Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_representation_integral_action : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    M.IsWeil ψ χX χW om → ∀ (μ : Measure (Fin n × Fin d → mixedEmbedding.mixedSpace F)), μ.IsAddHaarMeasure →
    ∀ (h : UA σ W.J) (f f₁ : SInf F (Fin n × Fin d)), Acts (evI F) (om (1, h)) ⇑f ⇑f₁ →
      ∫ x, ‖f₁ x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  first | exact @GlobalTheory.ArchIsom.acts_norm_sq_eq | exact GlobalTheory.ArchIsom.acts_norm_sq_eq | (intros; apply GlobalTheory.ArchIsom.acts_norm_sq_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ToPairMul
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries

namespace GlobalTheory.RowReal

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem toPair_mul (p : Pair T) (g k : GA D (G.V p.small)) (h k' : GA D (G.V p.big)) :
    G.toPair p (g * k) (h * k') = G.toPair p g h * G.toPair p k k' := by
  cases p <;> simp [GridData.toPair, map_mul]

theorem ker_mul (W : G.Weil) (p : Pair T) (f : WO (G.pS p) (G.pT p) → ℂ) (g k : GA D (G.V p.small))
    (h k' : GA D (G.V p.big)) : W.ker p f (g * k) (h * k') = W.ker p (W.om p (G.toPair p k k') f) g h := by
  simp only [GridData.Weil.ker, thetaKO, toPair_mul, Prod.fst_mul, Prod.snd_mul, ← Prod.mk_mul_mk, Prod.mk.eta, map_mul,
    Module.End.mul_apply]

end GlobalTheory.RowReal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelCmExtension
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Filter Topology
open GlobalTheory.AdelicU
open scoped Classical

namespace GlobalTheory.Twist.SmoothLine

theorem finprod_add_of_at {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ) (x z : κ → AF F) (hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evI F) z) :
    (∏ᶠ v, φ v fun i => evFin F v ((x + z) i)) = ∏ᶠ v, φ v fun i => evFin F v (x i) := by
  refine finprod_congr fun v => ?_
  have hv : (fun i => evFin F v ((x + z) i)) = fun i => evFin F v (x i) := by
    funext i
    rw [Pi.add_apply, map_add (f := _), GlobalTheory.ThK.EvUniqInf.evFin_eq_zero_of_at z hz v i, add_zero]
  rw [hv]

end GlobalTheory.Twist.SmoothLine
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinsetAdelicUnitaryPreservesLatticeAlmostAStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_adelicUnitary_preserves_lattice_almost_all : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n), X.L.IsFullLattice E → ∀ g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J,
    ∃ S₁ : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), ∀ w ∉ S₁, ∀ z ∈ GlobalTheory.InertSph.latAt X w,
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g *ᵥ z ∈ GlobalTheory.InertSph.latAt X w ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g⁻¹ *ᵥ z ∈ GlobalTheory.InertSph.latAt X w := by
  first
  | exact @GlobalTheory.LatAlmostAll.exists_finset_keeps
  | intro F E _ _ _ _ _ σ n X hL g
    exact GlobalTheory.LatAlmostAll.exists_finset_keeps σ X hL.toIsLattice g
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultilinearCuspFormFamily
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
noncomputable section

namespace GlobalTheory.GKGlobalise

theorem kFin_eq {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : Formalism.IndefR.Mult.DSModel V S) (τ : D.what₂.Tau) :
    GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ) = GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ := by
  apply le_antisymm
  · refine sSup_le fun W hW v hv => ?_
    exact ⟨W, hW.1, hv, hW.2⟩
  · rintro v ⟨A, hA, hv, hs⟩
    exact le_sSup (show A ∈ {W : Submodule ℂ (M.H τ) | FiniteDimensional ℂ W ∧
      Formalism.MainNotions.S.IsKStableOn (M.ε τ) (M.σ τ) W} from ⟨hA, hs⟩) hv

theorem kFin_le_sm (hHC : GlobalTheory.Published.HarishChandraModules) {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}
    (M : Formalism.IndefR.Mult.DSModel V S) (τ : D.what₂.Tau) : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ ≤ M.sm τ := fun v hv =>
  (GlobalTheory.T.mem_smoothVectors_discreteSeriesModel_iff M τ v).2 ((GlobalTheory.TypeSum.std_of_isDS hHC (M.ds τ)).2.2.1 v hv)

end GlobalTheory.GKGlobalise
end
end
