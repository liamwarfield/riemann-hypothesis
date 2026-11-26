module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurePreservingMulRight
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteLastStepRealIntertwiner
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaLiftMultiplicitySpacesOfPublishedStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMultiplicityLiftLastChainStep
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletedGridArrowLatticeIffIntegralFrameMatr
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeFormOfDoubling
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacRowScalar

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneParamSubgroupTransposeGramUnitaryDecomposes
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneParamSubgroupTransposeGramUnitaryDecomposes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.KapXLineDec

variable {D : D7}

theorem pre_mem (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = D.host.xi0 • reindex e e X.gramᵀ) (u : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J) :
    Units.map (Matrix.reindexAlgEquiv (AE D) (AE D) e.symm).toMonoidHom u.1 ∈
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (AF D.host.F) D.sp.cm.sig X.gram := by
  have h0 : (u.1.1)ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J * (u.1.1).map (cA D) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J := u.2
  show ((reindex e.symm e.symm u.1.1).map (cA D))ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gram * reindex e.symm e.symm u.1.1 =
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gram
  generalize u.1.1 = M at h0 ⊢
  clear u
  subst hJ
  rw [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul, Matrix.mul_smul, Matrix.smul_mul] at h0
  have h1 := congrArg (fun A => incA D D.host.xi0⁻¹ • A) h0
  simp only [smul_smul, ← map_mul, inv_mul_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), map_one, one_smul] at h1
  have h2 := congrArg (fun A => Aᵀ.submatrix e e) h1
  have e1 : (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (reindex e e X.gramᵀ))ᵀ = (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gram).submatrix e.symm e.symm := rfl
  simp only [transpose_mul, transpose_transpose, e1] at h2
  have e2 : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gram = ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gram).submatrix e.symm e.symm).submatrix e e := by simp
  have e3 : ((reindex e.symm e.symm M).map (cA D))ᵀ = ((M.map (cA D))ᵀ).submatrix e e := rfl
  rw [e2, e3, reindex_apply, Equiv.symm_symm, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.mul_assoc]
  exact h2

def pre (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = D.host.xi0 • reindex e e X.gramᵀ) (u : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J) : GA D X :=
  ⟨Units.map (Matrix.reindexAlgEquiv (AE D) (AE D) e.symm).toMonoidHom u.1, pre_mem X e hJ u⟩

theorem kapX_pre (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = D.host.xi0 • reindex e e X.gramᵀ) (u : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J) : kapX X e hJ (pre X e hJ u) = u := by
  apply Subtype.ext
  apply Units.ext
  show reindex e e (reindex e.symm e.symm u.1.1) = u.1.1
  simp

theorem pre_mul (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = D.host.xi0 • reindex e e X.gramᵀ) (u v : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J) :
    pre X e hJ (u * v) = pre X e hJ u * pre X e hJ v := by
  apply Subtype.ext
  show Units.map (Matrix.reindexAlgEquiv (AE D) (AE D) e.symm).toMonoidHom (u.1 * v.1) =
    Units.map (Matrix.reindexAlgEquiv (AE D) (AE D) e.symm).toMonoidHom u.1 *
      Units.map (Matrix.reindexAlgEquiv (AE D) (AE D) e.symm).toMonoidHom v.1
  exact map_mul _ _ _

theorem continuous_pre (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = D.host.xi0 • reindex e e X.gramᵀ) : Continuous (pre X e hJ) := by
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · exact (Units.continuous_val.comp continuous_subtype_val).matrix_reindex e.symm e.symm
  · exact (Units.continuous_coe_inv.comp continuous_subtype_val).matrix_reindex e.symm e.symm

theorem pre_mem_GinfC (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) (Wd : Spc D.host.F D.host.E d)
    (hJ : Wd.J = D.host.xi0 • reindex e e X.gramᵀ) {u : UA D.sp.cm.sig Wd.J}
    (hu : u ∈ UAt D.sp.cm.sig Wd (evI D.host.F)) : pre X e hJ u ∈ GinfC X := by
  refine MonoidHom.mem_ker.2 (Units.ext ?_)
  show (Formalism.L2.Theta.mt X (pre X e hJ u)).map (finPart D) = 1
  ext i j
  have h1 : At (evI D.host.F) (mat u (e i) (e j) - (1 : Matrix (Fin d) (Fin d) (AE D)) (e i) (e j)) :=
    fun w hw => congrFun (congrFun (hu w hw) (e i)) (e j)
  have h2 := GlobalTheory.ConjInfExp.finPart_eq_one (mat u (e i) (e j) - (1 : Matrix (Fin d) (Fin d) (AE D)) (e i) (e j) + 1)
    (by rwa [add_sub_cancel_right])
  rw [RingHom.map_add (f := _), RingHom.map_one, add_eq_right, RingHom.map_sub, sub_eq_zero] at h2
  show finPart D (mat u (e i) (e j)) = (1 : Matrix (Fin X.rank) (Fin X.rank) _) i j
  rw [h2]
  by_cases c : i = j
  · subst c; simp
  · have c' : e i ≠ e j := fun k => c (e.injective k)
    simp [Matrix.one_apply_ne c, Matrix.one_apply_ne c']

theorem lie_of {n : Type} [Fintype n] [DecidableEq n] (G Y : Matrix n n ℂ)
    (h : ∀ t : ℝ, (NormedSpace.exp (t • Y))ᴴ * G * NormedSpace.exp (t • Y) = G) : Yᴴ * G + G * Y = 0 := by
  letI : NormedRing (Matrix n n ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix n n ℂ) := Matrix.linftyOpNormedAlgebra
  have e1 : ∀ t : ℝ, (NormedSpace.exp (t • Y))ᴴ = NormedSpace.exp (t • Yᴴ) := fun t => by
    rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, star_trivial]
  have h1 := ((hasDerivAt_exp_smul_const (Yᴴ) (0:ℝ)).mul_const G).mul (hasDerivAt_exp_smul_const Y (0:ℝ))
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h1
  have hc : ((fun y : ℝ => NormedSpace.exp (y • Yᴴ) * G) * fun u : ℝ => NormedSpace.exp (u • Y)) = fun _ => G :=
    funext fun t => by
      show NormedSpace.exp (t • Yᴴ) * G * NormedSpace.exp (t • Y) = G
      rw [← e1]; exact h t
  have h2 : HasDerivAt (fun _ : ℝ => G) (Yᴴ * G * 1 + G * Y) 0 :=
    h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => (congrFun hc t).symm)
  have h3 := h2.unique (hasDerivAt_const (0:ℝ) G)
  simpa only [mul_one] using h3

end GlobalTheory.KapXLineDec


open GlobalTheory.KapXLineDec in
theorem GlobalTheory.KapXLineDec.line_dec : ∀ (D : D7) (θ : InfFam D) (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d)
    (Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (hJ : Wd.J = D.host.xi0 • reindex e e X.gramᵀ), IsInfFam θ →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Wd,
    ∃ l : List (D.what₂.Tau × Matrix (Fin X.rank) (Fin X.rank) ℂ), (∀ q ∈ l, q.2 ∈ lieAt X q.1) ∧
      ∀ t : ℝ, γ (Multiplicative.ofAdd t) = kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod) := by
  intro D θ X d e Wd hJ hθ γ hγ
  classical
  let h : ℝ → GA D X := fun t => pre X e hJ (γ (Multiplicative.ofAdd t))
  have hc : Continuous h := (continuous_pre X e hJ).comp (hγ.1.comp continuous_ofAdd)
  have hadd : ∀ s t, h (s + t) = h s * h t := fun s t => by
    show pre X e hJ (γ (Multiplicative.ofAdd (s + t))) = _
    rw [ofAdd_add, map_mul, pre_mul]
  have h0 : h 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have hfin : ∀ t, h t ∈ GinfC X := fun t => pre_mem_GinfC X e Wd hJ (hγ.2 _)
  let N : D.what₂.Tau → ℝ → Matrix (Fin X.rank) (Fin X.rank) ℂ := fun τ t => infMat D.sp.cm.sig X.gram (θ τ) (h t)
  have hNc : ∀ τ, Continuous (N τ) := fun τ => (GlobalTheory.Mem.VolExists.continuous_infMat X.gram (hθ τ)).comp hc
  have hN0 : ∀ τ, N τ 0 = 1 := fun τ => by
    show infMat D.sp.cm.sig X.gram (θ τ) (h 0) = 1
    rw [h0]; exact GlobalTheory.PointAtPlaceHom.infMat_one X _
  have hNm : ∀ τ s t, N τ (s + t) = N τ s * N τ t := fun τ s t => by
    show infMat D.sp.cm.sig X.gram (θ τ) (h (s + t)) = _
    rw [hadd]; exact GlobalTheory.PointAtPlaceHom.infMat_mul X _ _ _
  choose Y hY using fun τ => GlobalTheory.T.matrix_oneParameterGroup_eq_exp_of_continuous (N τ) (hNc τ) (hN0 τ) (hNm τ)
  have hYl : ∀ τ, Y τ ∈ lieAt X τ := fun τ =>
    lie_of _ _ fun t => (hY τ t) ▸ GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ X (h t) τ
  let L : List D.what₂.Tau := (Finset.univ : Finset D.what₂.Tau).toList
  refine ⟨L.map fun τ => (τ, Y τ), ?_, fun t => ?_⟩
  · intro q hq
    obtain ⟨τ, -, rfl⟩ := List.mem_map.1 hq
    exact hYl τ
  · have hP : ((L.map fun τ => (τ, Y τ)).map fun q => oneP θ X q.1 q.2 t).prod = h t := by
      refine GlobalTheory.RowReal.IsRealAll.unique hθ (M := fun τ => N τ t) ⟨?_, fun σ => ?_⟩ ⟨hfin t, fun σ => rfl⟩
      · refine Subgroup.list_prod_mem (GinfC X) fun x hx => ?_
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
        obtain ⟨τ, -, rfl⟩ := List.mem_map.1 hq
        exact (GlobalTheory.Mem.Lift.isAtTau_oneP hθ (hYl τ) t).1
      · have e1 : GlobalTheory.RowReal.infMatHom X (θ σ) ((L.map fun τ => (τ, Y τ)).map fun q => oneP θ X q.1 q.2 t).prod =
            (L.map fun ρ => if ρ = σ then N σ t else 1).prod := by
          rw [map_list_prod, List.map_map, List.map_map]
          congr 1
          refine List.map_congr_left fun ρ _ => ?_
          show infMat D.sp.cm.sig X.gram (θ σ) (oneP θ X ρ (Y ρ) t) = _
          have hs := GlobalTheory.Mem.Lift.isAtTau_oneP hθ (hYl ρ) t
          by_cases hρ : ρ = σ
          · subst hρ
            rw [if_pos rfl]
            exact hs.2.1.trans (hY ρ t).symm
          · rw [if_neg hρ]
            exact hs.2.2 σ (Ne.symm hρ)
        exact e1.trans (GlobalTheory.RowReal.list_prod_map_ite _ _ L (Finset.nodup_toList _)
          (Finset.mem_toList.2 (Finset.mem_univ _)))
    rw [hP]
    exact (kapX_pre X e hJ _).symm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneParamSubgroupTransposeGramUnitaryDecomposesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oneParamSubgroup_transposeGramUnitary_decomposes : ∀ (D : D7) (θ : InfFam D) (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d)
    (Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (hJ : Wd.J = D.host.xi0 • reindex e e X.gramᵀ), IsInfFam θ →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Wd,
    ∃ l : List (D.what₂.Tau × Matrix (Fin X.rank) (Fin X.rank) ℂ), (∀ q ∈ l, q.2 ∈ lieAt X q.1) ∧
      ∀ t : ℝ, γ (Multiplicative.ofAdd t) = kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod) := by
  first | exact @GlobalTheory.KapXLineDec.line_dec | exact GlobalTheory.KapXLineDec.line_dec | (intros; apply GlobalTheory.KapXLineDec.line_dec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntertwinersAndLiftsExistAtChoices
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLastStepIntertwinerChain
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLastStepIntertwinerChain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Twist.LastStepExists

theorem exists_lastStep_intertwiner : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.IsChainW → R.ex_ItX := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hLev hFam hMod hW
  obtain ⟨-, It, hIt⟩ := GlobalTheory.T.definite_lastStep_real_intertwiner D G Pl0 T A Ks R hLev hFam hMod hW.ωX hW.vX
  exact ⟨It, fun t => hIt t⟩

end GlobalTheory.Twist.LastStepExists
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLastStepIntertwinerChainStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lastStep_intertwiner_chain : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.IsChainW → R.ex_ItX := by
  first | exact @GlobalTheory.Twist.LastStepExists.exists_lastStep_intertwiner | exact GlobalTheory.Twist.LastStepExists.exists_lastStep_intertwiner | (intros; apply GlobalTheory.Twist.LastStepExists.exists_lastStep_intertwiner <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInnerStepIntertwinersThetaChain
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInnerStepIntertwinersThetaChain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.ExItY

theorem ex_ItY_holds : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (G : Type) [Group G]
    [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks]
    [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → HostHyp D → R.IsChainW →
    R.ex_ItY := by
  intro hDS hHC D G _ _ Pl0 T A Ks _ _ _ R hL _ hM hH hW
  have hθ : IsInfFam R.θ := hM.inf
  exact GlobalTheory.Chain.innerIntertwiners_of_pair D G Pl0 T A Ks R (GlobalTheory.T.exists_uniformRealThetaIntertwiner_chainStep hDS hHC D)
    (GlobalTheory.Chain.ParOfNodeGap.chainPar_of_nodeGap D hH.nodeGap) hθ
    (GlobalTheory.Chain.StepVac.stepsOK D G Pl0 T A Ks R hL hθ hW.ωY hW.ωX hW.vY hW.vX)

end GlobalTheory.Chain.ExItY
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInnerStepIntertwinersThetaChainStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_innerStepIntertwiners_thetaChain : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → HostHyp D → R.IsChainW → R.ex_ItY := by
  first | exact @GlobalTheory.Chain.ExItY.ex_ItY_holds | exact GlobalTheory.Chain.ExItY.ex_ItY_holds | (intros; apply GlobalTheory.Chain.ExItY.ex_ItY_holds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLastStepThetaLift
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLastStepThetaLift
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Twist.LastStepLift

theorem exists_lastStep_lift : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type)
    (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks]
    [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels →
    R.IsChainW → R.ex_ioX := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hlev hfam hmod hc
  have hIt : R.chain_ItX := hc.ItX.1 (GlobalTheory.T.exists_lastStep_intertwiner_chain D G Pl0 T A Ks R hlev hfam hmod hc)
  obtain ⟨io, hio⟩ := GlobalTheory.T.exists_multiplicityLift_lastChainStep D G Pl0 T A Ks R hlev hfam hmod hc.ωX hc.vX hc.ptX hIt
  exact fun t => ⟨io t, hio t⟩

end GlobalTheory.Twist.LastStepLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLastStepThetaLiftStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lastStep_thetaLift : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.IsChainW → R.ex_ioX := by
  first | exact @GlobalTheory.Twist.LastStepLift.exists_lastStep_lift | exact GlobalTheory.Twist.LastStepLift.exists_lastStep_lift | (intros; apply GlobalTheory.Twist.LastStepLift.exists_lastStep_lift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInnerStepThetaLifts
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInnerStepThetaLifts
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.ExIoY

theorem ex_ioY_holds : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay →
    GlobalTheory.Published.CasselmanWallach → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type)
    (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → HostHyp D → R.IsChainW → R.ex_ioY := by
  intro hDS hHC hCR hCW D G _ _ Pl0 T A Ks _ _ _ R hL hF hM hH hW
  have hθ : IsInfFam R.θ := hM.inf
  have hE : R.ex_ItY := GlobalTheory.T.exists_innerStepIntertwiners_thetaChain hDS hHC D G Pl0 T A Ks R hL hF hM hH hW
  have hI : R.chain_ItY := fun t k hk => (hW.ItY k hk).1 (hE k hk) t
  have hS : GlobalTheory.Chain.StepsOK R :=
    GlobalTheory.Chain.StepVac.stepsOK D G Pl0 T A Ks R hL hθ hW.ωY hW.ωX hW.vY hW.vX
  have hLw : GlobalTheory.Chain.LawsOK R := GlobalTheory.T.chainSteps_levelCharacter_conditions_hold D G Pl0 T A Ks R hL hθ hW.ωY hW.ωX hW.vY hW.vX
  have hY := GlobalTheory.Chain.ioYSt_of_ioPair D G Pl0 T A Ks R (GlobalTheory.T.exists_thetaLift_multiplicitySpaces_of_hypotheses hDS hHC hCR hCW D)
    (GlobalTheory.Chain.ParOfNodeGap.chainPar_of_nodeGap D hH.nodeGap) hθ hS hLw hM.νY hM.νY' hI
  exact fun t k hk => hY t k hk

end GlobalTheory.Chain.ExIoY
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInnerStepThetaLiftsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_innerStepThetaLifts : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → HostHyp D → R.IsChainW → R.ex_ioY := by
  first | exact @GlobalTheory.Chain.ExIoY.ex_ioY_holds | exact GlobalTheory.Chain.ExIoY.ex_ioY_holds | (intros; apply GlobalTheory.Chain.ExIoY.ex_ioY_holds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMultiplicitySpaceThetaMapOfRapidDecay
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMultiplicitySpaceThetaMapOfRapidDecay
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefLift.ThetaMap

theorem ex_thF_of_weak : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.IsThPW → R.ex_ioP → R.ex_thF := by
  intro hP D G _ _ Pl0 T A Ks _ _ _ R h0 hf hm h e i t
  obtain ⟨th, h1, h2⟩ := GlobalTheory.T.exists_thetaLift_linearMap_cuspFormMultiplicity hP D G Pl0 T A Ks R h0 hf hm h.ωP h.vP h.pt_theta
    (fun i t => (h.ioP i).1 (e i) t)
  exact ⟨th i t, h1 i t, h2 i t⟩

end GlobalTheory.DefLift.ThetaMap
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMultiplicitySpaceThetaMapOfRapidDecayStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_multiplicitySpaceThetaMap_of_rapidDecay : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.IsThPW → R.ex_ioP → R.ex_thF := by
  first | exact @GlobalTheory.DefLift.ThetaMap.ex_thF_of_weak | exact GlobalTheory.DefLift.ThetaMap.ex_thF_of_weak | (intros; apply GlobalTheory.DefLift.ThetaMap.ex_thF_of_weak <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLowestKTypeCoeffSpaceFockMap
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLowestKTypeCoeffSpaceFockMap
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IndefLinks

theorem exists_ioP_of_realDat : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.thP_ωP → R.thP_vP → R.ex_ioP := by
  intro D G _ _ Pl0 T A Ks _ _ _ R h0 hf hm hω hv i
  obtain ⟨-, io, hio⟩ := GlobalTheory.T.exists_lowestKType_fockMap_thetaVectors D G Pl0 T A Ks R h0 hf hm hω hv
  exact ⟨io i, fun t => hio i t⟩

end GlobalTheory.IndefLinks
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLowestKTypeCoeffSpaceFockMapStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lowestKType_coeffSpace_fockMap : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.thP_ωP → R.thP_vP → R.ex_ioP := by
  first | exact @GlobalTheory.IndefLinks.exists_ioP_of_realDat | exact GlobalTheory.IndefLinks.exists_ioP_of_realDat | (intros; apply GlobalTheory.IndefLinks.exists_ioP_of_realDat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExThOfChain
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ProjectedLift

theorem ex_Th_of_chain : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.grp_record → R.ex_Th := by
  intro D G _ _ Pl0 T A Ks _ _ _ R h0 hf hm hr t
  obtain ⟨Th, hTh⟩ := GlobalTheory.ProjectedLift.exists_chain_Th D G Pl0 T A Ks R h0 hf hm hr
  exact ⟨Th t, fun x => hTh t x⟩

end GlobalTheory.ProjectedLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaLiftGoodProjectorModels
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaLiftGoodProjectorModels
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Twist

theorem exists_thG_models : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.tw_thF → R.ex_thF → R.ex_thG := by
  intro D G _ _ Pl0 T A Ks _ _ _ R h0 hf hm h e i t
  obtain ⟨th, h1⟩ := GlobalTheory.GoodProjLift.exists_thG D G Pl0 T A Ks R h0 hf hm fun i t => ((h i t).1 (e i t)).1
  exact ⟨th i t, h1 i t⟩

end GlobalTheory.Twist
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaLiftGoodProjectorModelsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaLift_goodProjector_models : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.tw_thF → R.ex_thF → R.ex_thG := by
  first | exact @GlobalTheory.Twist.exists_thG_models | exact GlobalTheory.Twist.exists_thG_models | (intros; apply GlobalTheory.Twist.exists_thG_models <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntertwinersAndLiftsExistAtChoices
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ExAtAssembly

theorem exAt_holds : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.grp_record → HostHyp D → R.IsChainW → R.IsThPW → R.ExAt := by
  intro h1 h2 h3 h4 D G _ _ Pl0 T A Ks _ _ _ R h0 hf hm hr hH hc hp
  have eP : R.ex_ioP := GlobalTheory.T.exists_lowestKType_coeffSpace_fockMap D G Pl0 T A Ks R h0 hf hm hp.ωP hp.vP
  have eF : R.ex_thF := GlobalTheory.T.exists_multiplicitySpaceThetaMap_of_rapidDecay h3 D G Pl0 T A Ks R h0 hf hm hp eP
  exact ⟨GlobalTheory.T.exists_innerStepIntertwiners_thetaChain h1 h2 D G Pl0 T A Ks R h0 hf hm hH hc, GlobalTheory.T.exists_lastStep_intertwiner_chain D G Pl0 T A Ks R h0 hf hm hc,
    GlobalTheory.T.exists_innerStepThetaLifts h1 h2 h3 h4 D G Pl0 T A Ks R h0 hf hm hH hc, GlobalTheory.T.exists_lastStep_thetaLift D G Pl0 T A Ks R h0 hf hm hc,
    GlobalTheory.ProjectedLift.ex_Th_of_chain D G Pl0 T A Ks R h0 hf hm hr, eP, eF,
    GlobalTheory.T.exists_thetaLift_goodProjector_models D G Pl0 T A Ks R h0 hf hm hp.thF eF⟩

end GlobalTheory.ExAtAssembly
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntertwinersAndLiftsExistAtChoicesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intertwinersAndLifts_exist_at_choices : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.grp_record → HostHyp D → R.IsChainW → R.IsThPW → R.ExAt := by
  first | exact @GlobalTheory.ExAtAssembly.exAt_holds | exact GlobalTheory.ExAtAssembly.exAt_holds | (intros; apply GlobalTheory.ExAtAssembly.exAt_holds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsValuationOneElementAtGridPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff

namespace GlobalTheory.AAUnit

theorem natCast_notMem_of_coprime {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {n p : ℕ}
    (h : Nat.Coprime n p) (hp : ((p : ℕ) : 𝓞 K) ∈ w.asIdeal) : ((n : ℕ) : 𝓞 K) ∉ w.asIdeal := by
  intro hn
  obtain ⟨u, v, huv⟩ := (Nat.isCoprime_iff_coprime.mpr h).map (Int.castRingHom (𝓞 K))
  have h1 : (1 : 𝓞 K) ∈ w.asIdeal := by
    rw [← huv]
    simp only [eq_intCast, Int.cast_natCast]
    exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left u hn) (w.asIdeal.mul_mem_left v hp)
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)

theorem absNorm_cmIdeal_not_mem_gridPlaces {D : D7} {T : Type} {L : LevCh D T} (P : Places L) {v : HeightOneSpectrum (𝓞 D.host.F)}
    (hv : v ∈ P.S0) : ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal := by
  rcases P.mem_S0_of_sum_eq.mp hv with h | h
  ·
    subst h
    have hq := GlobalTheory.ChiGrid.leastSplitAuxiliaryPrimeThetaChain_spec (D := D)
    exact natCast_notMem_of_coprime P.v0 ((Nat.Prime.coprime_iff_not_dvd hq.1).mpr hq.2.2).symm P.basePlace_over_qZero
  ·
    have hcop : ∀ p ∈ D.host.levelPrimes, ((p : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal →
        ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal :=
      fun p hp hpv => natCast_notMem_of_coprime v (D.host.ccK_coprime p (by simp [hp])) hpv
    rcases (GlobalTheory.ChiGrid.S1_mem_OmF (D := D)).mp h with h' | h' | h' | h'
    · exact hcop _ (D.host.g_level 0) h'
    · exact hcop _ (D.host.g_level 1) h'
    · exact hcop _ D.host.pde_level.1 h'
    · exact hcop _ D.host.pde_level.2 h'

theorem exists_valuation_one_element_at_grid_places : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, GlobalTheory.SepRows.OffQ D → L.Is μ₀ → ∀ (G : GridData L sc), ∀ w ∈ G.pl.W0, ∃ a ∈ D.host.AA, Valued.v ((algebraMap D.host.E (Kw w)) a) = 1 := by
  intro D T L sc μ₀ _ _ G w hw
  classical
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw

  have hN : ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ (G.pl.w v).asIdeal := by
    intro hin
    apply absNorm_cmIdeal_not_mem_gridPlaces G.pl hv
    have hc : ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.F) ∈ ((G.pl.w v).under (𝓞 D.host.F)).asIdeal := by
      show ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.F) ∈
        Ideal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (G.pl.w v).asIdeal
      rw [Ideal.mem_comap, map_natCast]
      exact hin
    rw [G.pl.under_w hv] at hc
    exact hc
  refine ⟨_, GlobalTheory.HostClear.absNorm_mem_AA D, ?_⟩
  have key := (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := D.host.E) (v := G.pl.w v)).mpr hN
  rw [map_natCast] at key
  first
  | exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := G.pl.w v) _).trans key
  | (erw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']; exact key)

end GlobalTheory.AAUnit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqConjOfInFrame
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowReal

section Subst

variable {D : D7}

def fockSubAll {m n : ℕ} (pS pT : D.what₂.Tau → ℕ) (κS : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ)
    (κT : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) : MvPolynomial (FVar D m n) ℂ →ₐ[ℂ] MvPolynomial (FVar D m n) ℂ :=
  MvPolynomial.aeval fun y : FVar D m n =>
    ∑ i, ∑ j, MvPolynomial.C (if (y.2.1.val < pT y.1 ↔ y.2.2.val < pS y.1) then κT y.1 i y.2.1 * (κS y.1)⁻¹ y.2.2 j
      else (starRingEnd ℂ) (κT y.1 i y.2.1 * (κS y.1)⁻¹ y.2.2 j)) * MvPolynomial.X (y.1, i, j)

end Subst

section Points

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def ptTop (W : G.Weil) (g : Gc D.what₂.Tau (rowSizes D)) (n : ℕ) : GA D (G.V (.top n)) :=
  if h : n < D.R.m then (kappa W g).1 ⟨n, h⟩ else if h' : n = D.R.m then h' ▸ kappaTop W g else 1

def ptGrid (W : G.Weil) (g : Gc D.what₂.Tau (rowSizes D)) (i : ℕ) : GA D (G.V (.grid i D.R.m)) :=
  if h : i < D.R.m + 1 then (kappa W g).2 ⟨i, h⟩ else 1

theorem ptTop_lt (W : G.Weil) (g : Gc D.what₂.Tau (rowSizes D)) {n : ℕ} (h : n < D.R.m) :
    ptTop W g n = (kappa W g).1 ⟨n, h⟩ := by
  simp only [ptTop, dif_pos h]

theorem ptTop_m (W : G.Weil) (g : Gc D.what₂.Tau (rowSizes D)) : ptTop W g D.R.m = kappaTop W g := by
  simp only [ptTop, lt_irrefl, dif_neg (lt_irrefl _), not_false_eq_true]
  rfl

theorem ptGrid_le (W : G.Weil) (g : Gc D.what₂.Tau (rowSizes D)) {i : ℕ} (h : i < D.R.m + 1) :
    ptGrid W g i = (kappa W g).2 ⟨i, h⟩ := by
  simp only [ptGrid, dif_pos h]

end Points

section Scal

variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : Sizes} (P : ι → Entries S)

def rowScal (j : Fin S.m) (g : Gc ι S) : ℂ :=
  ((detChar (S.nR j.castSucc) (fun τ => (P τ).e j - (S.nR j.succ / 2 : ℕ)) ((rowComp S g) j.castSucc) *
    detChar (S.nR j.succ) (fun τ => -(P τ).e j + (S.nR j.castSucc / 2 : ℕ)) ((rowComp S g) j.succ) : ℂˣ) : ℂ)

def colScal (i : Fin S.m) (g : Gc ι S) : ℂ :=
  ((detChar (S.nC i.castSucc) (fun τ => (P τ).c i.rev - ((S.nC i.succ + 1) / 2 : ℕ)) (g.2 i.castSucc) *
    detChar (S.nC i.succ) (fun τ => -(P τ).c i.rev + ((S.nC i.castSucc + 1) / 2 : ℕ)) (g.2 i.succ) : ℂˣ) : ℂ)

end Scal

end GlobalTheory.RowReal

namespace GlobalTheory.RowReal

section Frame

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def topFrame (W : G.Weil) (τ : D.what₂.Tau) : Matrix (Fin (G.V (.top D.R.m)).rank) (Fin (G.V (.top D.R.m)).rank) ℂ :=
  Matrix.of fun a k =>
    Sum.elim (fun b : Fin ((rowSizes D).nC D.R.m) =>
        ((frameMat _ _ G.sp.topDec.ι).map (tauE D τ) * W.onb (.grid D.R.m D.R.m) τ) a (Fin.cast (rank_gridM G le_rfl).symm b))
      (fun _ : Fin 1 => (G.sp.topDec.a.map (tauE D τ)) a 0)
      ((finSumFinEquiv.trans (finCongr (rowSizes D).nC_succ)).symm (Fin.cast (rank_top G le_rfl) k))

end Frame

end GlobalTheory.RowReal

namespace GlobalTheory.RowReal

section More

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem ptTop_mem (W : G.Weil) (g : Gc D.what₂.Tau (rowSizes D)) (n : ℕ) : ptTop W g n ∈ GinfC (G.V (.top n)) := by
  unfold ptTop
  split_ifs with h h'
  · exact kappa_fst_mem W g _
  · subst h'; exact kappaTop_mem W g
  · exact one_mem _

theorem ptGrid_mem (W : G.Weil) (g : Gc D.what₂.Tau (rowSizes D)) (i : ℕ) : ptGrid W g i ∈ GinfC (G.V (.grid i D.R.m)) := by
  unfold ptGrid
  split_ifs with h
  · exact kappa_snd_mem W g _
  · exact one_mem _

theorem isKMat_cast {a b : ℕ} (h : a = b) (u : Matrix.unitaryGroup (Fin b) ℂ) {p : ℕ} (hp : p = a ∨ p = 0) :
    GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.IsKMat p ((u : Matrix (Fin b) (Fin b) ℂ).submatrix (Fin.cast h) (Fin.cast h)) := by
  subst h
  refine ⟨by simpa using u.2, fun i j hij => absurd ?_ hij⟩
  rcases hp with rfl | rfl
  · exact iff_of_true i.2 j.2
  · exact iff_of_false (Nat.not_lt_zero _) (Nat.not_lt_zero _)

theorem trCol_injective (G : GridData L sc) (j : Fin D.R.m) : Function.Injective (trCol G j) :=
  MvPolynomial.rename_injective _ fun x y h => by
    simp only [Prod.mk.injEq, Fin.cast_inj] at h
    exact Prod.ext h.1 (Prod.ext h.2.1 h.2.2)

theorem trRow_injective (G : GridData L sc) (i : Fin D.R.m) : Function.Injective (trRow G i) :=
  MvPolynomial.rename_injective _ fun x y h => by
    simp only [Prod.mk.injEq, Fin.cast_inj] at h
    exact Prod.ext h.1 (Prod.ext h.2.2 h.2.1)

theorem eq_conj_of_inFrame {n : ℕ} {B M K : Matrix (Fin n) (Fin n) ℂ} (hB : IsUnit B.det) (h : B⁻¹ * M * B = K) :
    M = B * K * B⁻¹ := by
  rw [← h]
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hB, Matrix.mul_one]
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hB, Matrix.one_mul]

end More

end GlobalTheory.RowReal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UpwardThetaLiftNeZeroOfLValueNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaChainStageCartanFrameConjValuesCuspForms
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaChainStageCartanFrameConjValuesCuspForms
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EvenOnto

theorem conj_stage_val_mem_A0_and_cartan_frame : ∀ D : D7, ForStage D fun c _ s => ∃ (cA : GlobalTheory.Mem.Th.CptF s.V) (a : GL (Fin s.V.rank) (AE D)), GlobalTheory.Cusp.IsCartanFrame s.V cA ∧ (∀ τ, IsCartanInv (gramAt D s.V τ) (cart s.M τ)) ∧ (∀ τ, cA τ * cart s.M τ = Formalism.UG.Jpq (s.V.sig (tauE D τ)).1 (s.V.sig (tauE D τ)).2 * cA τ) ∧ GlobalTheory.Doubling.IsMaj s.V a ∧ (∀ τ, (compAt c.θ τ a.1)ᴴ * (gramAt D s.V τ * cart s.M τ) * compAt c.θ τ a.1 = 1) ∧ ∀ (u : s.CC c), ∀ v ∈ s.KF, (fun g => conj (PiLocalization₂.val u v g)) ∈ GlobalTheory.Cusp.A0 c.θ s.V cA := by
  intro D c hc j _ s hs
  obtain ⟨a, ha, hmaj⟩ := GlobalTheory.ChainOnto.RealData.exists_maj_cart c.θ hc.inf s.M
  exact ⟨GlobalTheory.ChainOnto.RealData.sortedFrame s.M hs.sigOK, a, GlobalTheory.ChainOnto.RealData.isCartanFrame_sortedFrame _ _,
    fun τ => GlobalTheory.ChainOnto.RealData.isCartanInv_cart _ τ, fun τ => GlobalTheory.ChainOnto.RealData.sortedFrame_cart _ _ τ, ha, hmaj,
    fun u v hv => GlobalTheory.ChainOnto.RealData.conj_multiplicityValue_mem_cuspFormsArchimedeanKFinite c.θ hc.inf s.M hs.sigOK u.1 u.2 v hv⟩

end GlobalTheory.EvenOnto

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaChainStageCartanFrameConjValuesCuspFormsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaChainStage_cartanFrame_conj_values_cuspForms : ∀ D : D7, ForStage D fun c _ s => ∃ (cA : GlobalTheory.Mem.Th.CptF s.V) (a : GL (Fin s.V.rank) (AE D)), GlobalTheory.Cusp.IsCartanFrame s.V cA ∧ (∀ τ, IsCartanInv (gramAt D s.V τ) (cart s.M τ)) ∧ (∀ τ, cA τ * cart s.M τ = Formalism.UG.Jpq (s.V.sig (tauE D τ)).1 (s.V.sig (tauE D τ)).2 * cA τ) ∧ GlobalTheory.Doubling.IsMaj s.V a ∧ (∀ τ, (compAt c.θ τ a.1)ᴴ * (gramAt D s.V τ * cart s.M τ) * compAt c.θ τ a.1 = 1) ∧ ∀ (u : s.CC c), ∀ v ∈ s.KF, (fun g => conj (PiLocalization₂.val u v g)) ∈ GlobalTheory.Cusp.A0 c.θ s.V cA := by
  first | exact @GlobalTheory.EvenOnto.conj_stage_val_mem_A0_and_cartan_frame | exact GlobalTheory.EvenOnto.conj_stage_val_mem_A0_and_cartan_frame | (intros; apply GlobalTheory.EvenOnto.conj_stage_val_mem_A0_and_cartan_frame <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UpwardThetaLiftNeZeroOfLValueNeZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EvenOnto

theorem upNe_of_heckeForm : ∀ D : D7, GlobalTheory.Core.Rk.IP.HeckeForm D → MetEx D → ZetaNe D → UpNe D := by
  intro D hHF _ hZ c hc k hk s s' hs hs' p hp u B hB hL
  obtain ⟨m₁, X₁, hmX⟩ := GlobalTheory.Size.exists_isCovolOne s.V s'.V
  obtain ⟨φ, v, hvK, hZ'⟩ := hZ c hc k hk s s' hs hs' p hp m₁ X₁ hmX
  refine ⟨φ, v, hvK, ?_⟩
  obtain ⟨hu0, hpar⟩ := hB
  obtain ⟨hI, hInt⟩ := hZ' u hu0
  have hF : PiLocalization₂.val u v ≠ 0 := by
    intro h0
    apply hI
    have : ∀ g, p.zint m₁ X₁ φ (PiLocalization₂.val u v) g = 0 := by
      intro g; simp [Step.zint, h0, PiLocalization₂.pet, Lift.pet, rTr]
    simp [this]
  have hparF := hpar v hF
  obtain ⟨cA, a, hcA, hcart, hJ, hmaj, hmaj_eq, hA0⟩ := GlobalTheory.T.thetaChainStage_cartanFrame_conj_values_cuspForms D c hc k hk.le s hs
  obtain ⟨-, -, -, hcartB, -, -, -, -⟩ := GlobalTheory.T.thetaChainStage_cartanFrame_conj_values_cuspForms D c hc (k + 1) hk s' hs'
  have hu1 : (fun g => conj (PiLocalization₂.val u v g)) ∈ GlobalTheory.Cusp.A0 c.θ s.V cA := hA0 u v hvK
  have hwitt : GlobalTheory.Cusp.wittIndex s'.V < c.t := hs'.witt
  have hfock := GlobalTheory.T.evenThetaChainStep_fockVectors_spherical_latticeVacua D c hc k hk s s' hs hs' p hp
  have hunrT := (hc.unr k hk)
  obtain ⟨-, -, hoff⟩ := GlobalTheory.T.doubledLatticeHeightFun_properties D s.V s.Λ a hs.selfDual hmaj
  have hmeas : MeasurableSet (intOff c s) := (hoff c.S).1.measurableSet
  have hr1 : 1 ≤ s.V.rank := by
    rw [hs.rank]; have := hc.one_le; omega
  have ht1 : 1 ≤ c.t := by have := hc.step; omega
  have hrk : s'.V.rank = s.V.rank + c.t := by rw [hs'.rank, hs.rank]; ring
  have hPair : GlobalTheory.Core.Rk.IP.Pair c.ψ c.θ s.V s'.V (c.χ k) (c.χ k) (cart s.M) (cart s'.M) c.t cA a p.ω
      m₁ X₁ :=
    { setting := ⟨hr1, ht1, hrk, hc.inf, hs.sigOK, hcA, hcart, hcartB, hJ⟩
      maj := hmaj
      maj_eq := hmaj_eq
      weil := hp.pre.weil
      covol := hmX }
  have hUnr : GlobalTheory.Core.Rk.IP.Unram c.ψ s.V s'.V (c.χ k) s.Λ s'.Λ c.S (p.pt φ) (p.pt φ) :=
    ⟨hs.selfDual, hs'.selfDual, fun w _ h2 => GlobalTheory.Core.Rk.IP.Model.isSplit_two w h2, hunrT, (hfock φ).2.2.1,
      (hfock φ).2.2.1⟩
  have hsph := GlobalTheory.ChainOnto.sphFun_of_isParamFun D s.V s.Λ c.S _ B hparF
  set F := PiLocalization₂.val u v with hFdef
  have hAut : Formalism.L2.Theta.IsAutFunSm c.θ s.V (fun g => conj (F g)) := hu1.1.1
  have hFl : ∀ γ ∈ GQ s.V, ∀ g, F (γ * g) = F g := fun γ hγ g => by
    simpa using congrArg (starRingEnd ℂ) (hAut.left γ hγ g)
  have hFc : Continuous F := by
    have h := hAut.cont.star
    change Continuous (fun g => star (star (F g))) at h
    simpa only [star_star] using h
  have hΦ : IsThetaFunO c.ψ s.V s'.V (p.pt φ) := (hfock φ).1
  have hθl : ∀ h, ∀ γ ∈ GQ s.V, ∀ g, thetaKO p.ω (γ * g) h (p.pt φ) = thetaKO p.ω g h (p.pt φ) := by
    intro h γ hγ g
    have e : ((γ * g, h) : GA D s.V × GA D s'.V) = (γ, 1) * (g, h) := by simp
    simp only [thetaKO, e, map_mul, Module.End.mul_apply]
    exact hp.pre.weil.om_aut γ hγ 1 (one_mem _) _ (hp.pre.weil.om_pres _ _ hΦ)
  have hθc : ∀ h, Continuous fun g => thetaKO p.ω g h (p.pt φ) := fun h =>
    (hp.pre.weil.om_cont _ hΦ 0).comp (continuous_id.prodMk continuous_const)
  have hrc : ∀ g, GlobalTheory.Core.Rk.IP.rcoef s.ν (fun x => conj (F x)) (fun x => conj (F x)) g = conj (s.pet (rTr s.V g F) F) := by
    intro g
    have := GlobalTheory.T.integral_quotient_eq_setIntegral_fundamentalDomain D s.V s.ν s.fd hs.haar hs.fund (fun x => conj (F (x * g)) * conj (conj (F x)))
      (fun γ hγ x => by simp only [mul_assoc, hFl γ hγ]) (by fun_prop)
    simp only [GlobalTheory.Core.Rk.IP.rcoef, PiLocalization₂.pet, Lift.pet, rTr]
    rw [← integral_conj]
    simp only [map_mul]
    exact this
  have hup : ∀ h, GlobalTheory.Core.Rk.IP.up p.ω s.ν (p.pt φ) (fun x => conj (F x)) h = conj (p.up φ F h) := by
    intro h
    have := GlobalTheory.T.integral_quotient_eq_setIntegral_fundamentalDomain D s.V s.ν s.fd hs.haar hs.fund (fun g => thetaKO p.ω g h (p.pt φ) * conj (F g))
      (fun γ hγ x => by simp only [hθl h γ hγ, hFl γ hγ]) (by have := hθc h; fun_prop)
    simp only [GlobalTheory.Core.Rk.IP.up, Step.up]
    rw [← integral_conj]
    simp only [map_mul, Complex.conj_conj]
    exact this
  have hsZ : GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.sZero s.V s'.V = (c.t : ℂ) / 2 := by
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.sZero, hrk]; push_cast; ring
  have hwz : ∀ g, GlobalTheory.Core.Rk.IP.wcoef p.ω m₁ X₁ (p.pt φ) (p.pt φ) g *
      GlobalTheory.Core.Rk.IP.rcoef s.ν (fun x => conj (F x)) (fun x => conj (F x)) g = p.zint m₁ X₁ φ F g := by
    intro g; simp only [Step.zint, hrc]; rfl
  have hint : ∃ s₁ : ℝ, s₁ < (c.t : ℝ) / 2 ∧ IntegrableOn (GlobalTheory.Core.Rk.IP.integrand p.ω s.ν m₁ X₁ s.Λ a (p.pt φ)
      (p.pt φ) (fun x => conj (F x)) (fun x => conj (F x)) s₁) (GlobalTheory.Core.Rk.IP.openOff s.V s.Λ c.S) s.ν := by
    obtain ⟨s₁, hs₁, hi⟩ := hInt a hmaj hmaj_eq
    refine ⟨s₁, hs₁, hi.congr_fun (fun g hg => ?_) hmeas⟩
    simp only [GlobalTheory.Core.Rk.IP.integrand, GlobalTheory.Doubling.npow, (hoff c.S).2 g hg, hsZ, hrc]
    simp only [Step.zint, coefW, GlobalTheory.Core.Rk.IP.wcoef, GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.ip, hgtS]
    ring
  obtain ⟨-, -, -, hval⟩ := hHF c.ψ c.θ s.V s'.V (c.χ k) (c.χ k) (cart s.M) (cart s'.M) c.t cA a p.ω
    m₁ X₁ hPair (Or.inr hwitt) s.Λ s'.Λ c.S (p.pt φ) (p.pt φ) (hfock φ).2.1 (hfock φ).2.1 hUnr s.ν s'.ν hs.haar hs'.haar
    _ hu1 _ hu1 B hparF hsph hint
  obtain ⟨l, hl0, hlv⟩ := hL
  have key := hval l hlv
  intro hup0
  have hz : GlobalTheory.Core.Rk.IP.up p.ω s.ν (p.pt φ) (fun x => conj (F x)) = 0 := by
    funext h; rw [hup, hup0]; simp
  rw [hz] at key
  have hlhs : GlobalTheory.Cusp.petersson s'.V s'.ν (0 : GA D s'.V → ℂ) 0 = 0 := by
    simp [GlobalTheory.Cusp.petersson, GlobalTheory.AutomorphicL2Unitary.pet, GlobalTheory.AutomorphicL2Unitary.descend]
  rw [hlhs] at key
  have hvol : (0 : ℝ) < GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ s'.V s'.ν := by
    have := hs'.haar; exact GlobalTheory.RallisIP.Model.vol_pos s'.ν
  have hd : GlobalTheory.LFun.dSfun (F := D.host.F) D.host.E (c.S : Set (GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.FinPl D)) s.V.rank s'.V.rank
      ((c.t : ℂ) / 2) ≠ 0 := by
    refine ((GlobalTheory.T.partialNormalizingFactorProduct_analytic_ne_zero D _ _ _).2 _ ?_).1
    simp only [Complex.div_ofNat_re, Complex.natCast_re]; positivity
  have hI' : ∫ g in GlobalTheory.Core.Rk.IP.openOff s.V s.Λ c.S, GlobalTheory.Core.Rk.IP.wcoef p.ω m₁ X₁ (p.pt φ) (p.pt φ) g *
      GlobalTheory.Core.Rk.IP.rcoef s.ν (fun x => conj (F x)) (fun x => conj (F x)) g ∂s.ν ≠ 0 := by
    simp only [hwz]; exact hI
  have hvolC : ((GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ s'.V s'.ν : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hvol.ne'
  exact hI' (by
    have := key.symm
    rcases mul_eq_zero.1 this with h | h
    · rcases mul_eq_zero.1 h with h | h
      · exact absurd h hvolC
      · exact absurd h (div_ne_zero hl0 hd)
    · exact h)

end GlobalTheory.EvenOnto

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UpwardThetaLiftNeZeroOfLValueNeZeroStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.upwardThetaLift_ne_zero_of_lValue_ne_zero : ∀ D : D7, GlobalTheory.Core.Rk.IP.HeckeForm D → MetEx D → ZetaNe D → UpNe D := by
  first | exact @GlobalTheory.EvenOnto.upNe_of_heckeForm | exact GlobalTheory.EvenOnto.upNe_of_heckeForm | (intros; apply GlobalTheory.EvenOnto.upNe_of_heckeForm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ActEqTranslateLiftV
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RationalFormsAction

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem isTranslate_act_V (hr : R.grp_red_L) (hj : R.models_jV) (i : Fin D.R.m) (t : T0) (g : G)
    (x : (A.fam.L i t).S.Forms) :
    GlobalTheory.IndefiniteRowSideFullHecke.TranslateRepresentations.IsTranslate (Vc D i) (R.βV i) (R.datVt i t) (R.eG g) ((R.HV i t).e (R.jV i t x))
      ((R.HV i t).e (R.jV i t ((A.fam.L i t).r g x))) := by

  have hred := hr i t
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TranslateRepresentations.IsTranslate
  constructor
  ·
    obtain ⟨q, hq⟩ := (R.B.L i t).act_tie.red_surj g
    have hq' := hred q
    rw [hq] at hq'
    exact ⟨q, hq'.symm⟩
  · intro κ hκ h

    have hg : (R.B.L i t).act_tie.red κ = g := by
      apply R.eG.injective
      rw [hred κ]
      exact hκ

    have key := congrFun ((R.B.L i t).act_tie.act_eq g κ hg x) h
    have e1 := hj i t ((A.fam.L i t).r g x)
    have e2 := hj i t x

    refine (congrFun e1 h).trans (key.trans ?_)
    exact congrArg (fun w => ((((levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch κ)⁻¹ : ℂˣ) : ℂ) • w)
      (congrFun e2 (h * (κ : Bridge.Gf (Vc D i)))).symm

end GlobalTheory.RationalFormsAction

theorem GlobalTheory.RationalFormsAction.act_eq_translate_lift_V : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.grp_red_L → R.models_jV → ∀ i t (g : G) (x : (A.fam.L i t).S.Forms), ∃ κ, IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) (R.eG g) κ ∧ ∀ h, (R.HV i t).e (R.jV i t ((A.fam.L i t).r g x)) h = (levChi _ (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • (R.HV i t).e (R.jV i t x) (h * (finHom _).rangeRestrict κ) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hr hj i t g x

  have htr := GlobalTheory.RationalFormsAction.isTranslate_act_V R hr hj i t g x
  have hex := GlobalTheory.LiftEquivariance.exists_adelic_lift htr
  exact hex

end
end
