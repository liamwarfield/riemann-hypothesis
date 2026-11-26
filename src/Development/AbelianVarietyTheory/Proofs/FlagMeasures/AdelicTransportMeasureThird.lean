module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicTransportMeasureSecond
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameAdaptedIsometryOfFixingBothFrames
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAllTiedPerTied
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitriangularFramesGramEqCellPoint
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdCons
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.OmegaDensityUnique
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DensFrame

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicTransportMeasureThird
noncomputable section

open MeasureTheory Formalism.MainNotions.S Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.RowLev GlobalTheory.SmVec NumberField Matrix
open scoped InnerProductSpace TensorProduct Classical ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RepSmooth

variable {D : D7} {θ : D.what₂.Tau → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}
  {S : D.what₂.Tau → SPar} {M : DSModel V S} {Φ : MMap M}

def IsEquiv (θ : D.what₂.Tau → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (Φ : MMap M) : Prop :=
  ∀ τ, ∀ a ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ (u : M.Vec) (w : M.sm τ),
    (w : M.H τ) = M.rep τ a (u τ) → Φ (Function.update u τ w) = rTr V (atTau θ V τ a) (Φ u)

def IsSob (Φ : MMap M) : Prop :=
  ∀ τ (u : M.Vec) (x : GA D V), ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt V τ) (M.rep τ) ℓ ∧
    ∀ w : M.sm τ, ℓ w = Φ (Function.update u τ w) x

def der (u : M.Vec) (τ : D.what₂.Tau) {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) : M.sm τ :=
  ⟨dRep (trRep (M.σ τ) (M.fr τ)) X (u τ), (MultGelf.mem_sm M τ).2
    (dRep_mem (gram_unit (M.fr_unit τ) (M.fr_gram τ)) (MultGelf.isURep M τ) ((MultGelf.mem_sm M τ).1 (u τ).2) hX)⟩

theorem hasDerivAt_apply (he : IsEquiv θ Φ) (hs : IsSob Φ) (τ : D.what₂.Tau) (u : M.Vec)
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) (x : GA D V) :
    HasDerivAt (fun t : ℝ => Φ u (x * oneP θ V τ X t)) (Φ (Function.update u τ (der u τ hX)) x) 0 := by
  haveI : CompleteSpace (M.H τ) := (M.ds τ).1
  have hG := gram_unit (M.fr_unit τ) (M.fr_gram τ)
  obtain ⟨ℓ, hℓ, hℓT⟩ := hs τ u x
  obtain ⟨m, ls, a, hls, ha⟩ := GlobalTheory.T.sobolevContinuousForm_sum_lieWord_inner _ _ _ (M.σ τ) (M.fr τ) _ (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1 ℓ hℓ
  have hu := (MultGelf.mem_sm M τ).1 (u τ).2
  have hmem : ∀ t : ℝ, trRep (M.σ τ) (M.fr τ) (NormedSpace.exp (t • X)) (u τ) ∈
      smSub (gramAt D V τ) (trRep (M.σ τ) (M.fr τ)) := fun t =>
    rep_mem hG (MultGelf.isURep M τ) hu (exp_mem_UH hG hX t)
  have h1 : (fun t : ℝ => Φ u (x * oneP θ V τ X t)) = fun t : ℝ =>
      ∑ i, ⟪a i, word (trRep (M.σ τ) (M.fr τ)) (ls i)
        (trRep (M.σ τ) (M.fr τ) (NormedSpace.exp (t • X)) (u τ))⟫_ℂ := by
    funext t
    rw [← ha _ (hmem t)]
    have h2 := he τ _ (exp_mem_UH hG hX t) u ⟨_, (MultGelf.mem_sm M τ).2 (hmem t)⟩ rfl
    have h3 := hℓT ⟨_, (MultGelf.mem_sm M τ).2 (hmem t)⟩
    rw [h2] at h3
    exact h3.symm
  rw [h1, ← hℓT, show ((der u τ hX : M.sm τ) : M.H τ) = dRep (trRep (M.σ τ) (M.fr τ)) X (u τ) from rfl,
    ha _ (dRep_mem hG (MultGelf.isURep M τ) hu hX)]
  refine HasDerivAt.fun_sum fun i _ => ?_
  have h5 := (hasDerivAt_const (0 : ℝ) (a i)).inner ℂ
    (GlobalTheory.T.lieWord_commutes_oneParameter_derivative _ _ _ (M.σ τ) (M.fr τ) _ (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1 (ls i) (hls i) _ hu X hX)
  simpa using h5

theorem rder_apply (he : IsEquiv θ Φ) (hs : IsSob Φ) (τ : D.what₂.Tau) (u : M.Vec)
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) :
    Rder θ V τ X (Φ u) = Φ (Function.update u τ (der u τ hX)) :=
  funext fun x => (hasDerivAt_apply he hs τ u hX x).deriv

theorem rderC_apply (he : IsEquiv θ Φ) (hs : IsSob Φ) (τ : D.what₂.Tau) (v : M.Vec)
    (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) (u w : M.sm τ)
    (hw : (w : M.H τ) = dRepC (gramAt D V τ) (trRep (M.σ τ) (M.fr τ)) Z u) :
    RderC θ V τ Z (Φ (Function.update v τ u)) = Φ (Function.update v τ w) := by
  have hp := parts_mem (gram_unit (M.fr_unit τ) (M.fr_gram τ)) (gram_herm (M.fr_gram τ)) Z
  have h1 := rder_apply he hs τ (Function.update v τ u) hp.1
  have h2 := rder_apply he hs τ (Function.update v τ u) hp.2
  rw [Function.update_idem] at h1 h2
  have h3 : w = der (Function.update v τ u) τ hp.1 + Complex.I • der (Function.update v τ u) τ hp.2 :=
    Subtype.ext (by rw [hw]; simp only [der, Function.update_self]; rfl)
  rw [h3, Φ.map_update_add, Φ.map_update_smul, ← h1, ← h2]
  rfl

theorem foldr_apply (he : IsEquiv θ Φ) (hs : IsSob Φ) (τ : D.what₂.Tau) (v : M.Vec)
    (l : List (Matrix (Fin V.rank) (Fin V.rank) ℂ)) (u : M.sm τ) :
    ∃ w : M.sm τ, (w : M.H τ) =
        (l.map fun Z => dRepC (gramAt D V τ) (trRep (M.σ τ) (M.fr τ)) Z).foldr (fun f acc => f acc) (u : M.H τ) ∧
      (l.map fun Z => RderC θ V τ Z).foldr (fun f acc => f acc) (Φ (Function.update v τ u)) =
        Φ (Function.update v τ w) := by
  induction l with
  | nil => exact ⟨u, rfl, rfl⟩
  | cons Z l ih =>
    obtain ⟨w, h1, h2⟩ := ih
    refine ⟨⟨_, (MultGelf.mem_sm M τ).2 (dRepC_mem (gram_unit (M.fr_unit τ) (M.fr_gram τ)) (gram_herm (M.fr_gram τ))
      (MultGelf.isURep M τ) Z ((MultGelf.mem_sm M τ).1 w.2))⟩, ?_, ?_⟩
    · rw [List.map_cons, List.foldr_cons, ← h1]
    · rw [List.map_cons, List.foldr_cons, h2]
      exact rderC_apply he hs τ v Z w _ rfl

theorem gelf_scalar (he : IsEquiv θ Φ) (hs : IsSob Φ) (τ : D.what₂.Tau) (k : ℕ) :
    ∃ c : ℂ, ∀ v : M.Vec, gelf θ V τ k (Φ v) = c • Φ v := by
  haveI : CompleteSpace (M.H τ) := (M.ds τ).1
  obtain ⟨c, hc⟩ := GlobalTheory.SmVec.GelfScalar.gelfH_scalar _ _ _ _ _ _ (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1
    (M.ds τ).2.2.2.1 k
  refine ⟨c, fun v => ?_⟩
  choose f hf1 hf2 using fun idx : Fin (k + 1) → Fin V.rank =>
    foldr_apply he hs τ v (List.ofFn fun a : Fin (k + 1) => Matrix.single (idx a) (idx (a + 1)) (1 : ℂ)) (v τ)
  simp only [List.map_ofFn, Function.comp_def, Function.update_eq_self] at hf1 hf2
  have h1 : c • v τ = ∑ idx, f idx := by
    refine Subtype.ext ?_
    rw [Submodule.coe_smul, ← hc _ ((MultGelf.mem_sm M τ).1 (v τ).2), Submodule.coe_sum]
    exact Finset.sum_congr rfl fun idx _ => (hf1 idx).symm
  have h2 : c • Φ v = Φ (Function.update v τ (c • v τ)) := by
    rw [Φ.map_update_smul, RingHom.id_apply, Function.update_eq_self]
  rw [h2, h1]
  refine Eq.trans ?_ (map_sum (Φ.toLinearMap v τ) f Finset.univ).symm
  exact Finset.sum_congr rfl fun idx _ => hf2 idx

theorem zfin (he : IsEquiv θ Φ) (hs : IsSob Φ) (u : M.Vec) :
    ∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ Φ u ∈ W ∧ ∀ τ k, ∀ f ∈ W, gelf θ V τ k f ∈ W := by
  refine ⟨Submodule.span ℂ {Φ u}, inferInstance, Submodule.mem_span_singleton_self _, fun τ k f hf => ?_⟩
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hf
  obtain ⟨c, hc⟩ := gelf_scalar he hs τ k
  have h2 : a • Φ u = Φ (Function.update u τ (a • u τ)) := by
    rw [Φ.map_update_smul, RingHom.id_apply, Function.update_eq_self]
  rw [h2, hc, ← h2]
  exact Submodule.smul_mem _ _ hf

attribute [local instance 100] LieRing.ofAssociativeRing in
theorem smooth (hθ : IsInfFam θ) (he : IsEquiv θ Φ) (hs : IsSob Φ) (hc : ∀ u, Continuous (Φ u)) (u : M.Vec)
    (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (hX : ∀ i, Xs i ∈ lieAt V (τs i)) (g : GA D V) :
    ContDiff ℝ ∞ fun t : Fin k → ℝ => Φ u (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod) := by
  refine GlobalTheory.T.derivative_along_lie_algebra_preserves_smooth_space D θ V hθ (Set.range Φ) ?_ _ ⟨u, rfl⟩ k τs Xs hX g
  rintro _ ⟨v, rfl⟩
  refine ⟨hc v, fun τ => ⟨fun X => Rder θ V τ X (Φ v), fun X hX => ?_, fun a X hX Y hY => ?_⟩⟩
  · simp only [rder_apply he hs τ v hX]
    exact ⟨⟨_, rfl⟩, hasDerivAt_apply he hs τ v hX⟩
  · haveI : CompleteSpace (M.H τ) := (M.ds τ).1
    obtain ⟨h1, h2⟩ := GlobalTheory.SmVecLinear.dRep_linear _ _ _ _ _ _ (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1 _
      ((MultGelf.mem_sm M τ).1 (v τ).2)
    have haX : a • X ∈ lieAt V τ := (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU (gramAt D V τ)).smul_mem' a hX
    have hXY : a • X + Y ∈ lieAt V τ := (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU (gramAt D V τ)).add_mem' haX hY
    have h3 : der v τ hXY = (a : ℂ) • der v τ hX + der v τ hY :=
      Subtype.ext ((h1 _ haX _ hY).trans (by rw [h2 a X hX]; rfl))
    simp only [rder_apply he hs τ v hX, rder_apply he hs τ v hY, rder_apply he hs τ v hXY]
    rw [h3, Φ.map_update_add, Φ.map_update_smul, RingHom.id_apply]

theorem foldr_rder (he : IsEquiv θ Φ) (hs : IsSob Φ) (u : M.Vec)
    (l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)) (hl : ∀ p ∈ l, p.2 ∈ lieAt V p.1) :
    ∃ v, l.foldr (fun p f => Rder θ V p.1 p.2 f) (Φ u) = Φ v := by
  induction l with
  | nil => exact ⟨u, rfl⟩
  | cons p l ih =>
    obtain ⟨v, hv⟩ := ih fun q hq => hl q (List.mem_cons_of_mem _ hq)
    exact ⟨_, by rw [List.foldr_cons, hv, rder_apply he hs p.1 v (hl p List.mem_cons_self)]⟩

section Inst

@[reducible] def bundle (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf]
    (fund : Set I.GA) (R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund)) (H : InfinitePlace I.F → Type)
    [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)] (hC : ∀ v, CompleteSpace (H v))
    (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v)) (Hs : Type)
    [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] [CompleteSpace Hs] (σs : I.Ginf → (Hs →L[ℂ] Hs))
    (tens : (∀ v, H v) → Hs) (hF : I.IsFundDom (I.muA μf) fund) (hR : I.IsRightReg μf fund R)
    (hH : I.IsHilbTensor σ σs tens) (g : ℕ) : RowsAut where
  I := I
  μf := μf
  fund := fund
  fund_spec := hF
  lam := fun _ _ => 0
  H := H
  hC := hC
  σ := σ
  w := fun _ => 0
  Hs := Hs
  σs := σs
  tens := tens
  tens_spec := hH
  R := R
  R_spec := hR
  g := g
  g₀ := 0
  e := fun _ => 0
  e_adm := ⟨IsLocallyConstant.const _, by funext x; simp [AutInst.convF], fun _ => by simp,
    fun _ _ _ => by simp, fun _ h => absurd rfl h, fun _ _ _ _ _ => rfl, fun _ h => absurd rfl h⟩
  Re := 0
  Re_spec := ⟨integrable_zero _ _ _, fun _ _ => by simp⟩

theorem isContRep_of_ae (B : RowsAut) {y : B.I.L2 B.μf B.fund} {f : B.I.GA → ℂ} (hc : Continuous f)
    (hl : ∀ γ ∈ B.I.GFset, ∀ x, f (γ * x) = f x) (h : ∀ᵐ x ∂(B.I.muA B.μf), f x = B.I.ext y x) :
    GlobalTheory.Dec.IsContRep B y f := by
  refine ⟨hc, hl, ?_⟩
  have h1 := B.R_spec 1 y
  rw [(GlobalTheory.RightRegFund.rightReg_unitary_continuous B).1] at h1
  filter_upwards [h1, ae_restrict_of_ae (s := B.fund) h] with x a b
  rw [b]
  simpa using a

theorem eq_of_ae (B : RowsAut) {f f' : B.I.GA → ℂ} (hc : Continuous f) (hc' : Continuous f')
    (h : f =ᵐ[B.I.muA B.μf] f') : f = f' := by
  obtain ⟨-, -, -, -, hop⟩ := GlobalTheory.T.adelicUnitaryHaar_bi_invariant B.I B.μf
  have : (B.I.muA B.μf).IsOpenPosMeasure := ⟨fun U hU hne => (hop U hU hne).ne'⟩
  exact (Continuous.ae_eq_iff_eq (B.I.muA B.μf) hc hc').1 h

theorem eq_onePar (B : RowsAut) (w : InfinitePlace B.I.F) (E : GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie (B.I.ε w)) (t : ℝ) {h : B.I.GA}
    (h2 : h.2 = 1) (hw : uMat (h.1 w) = NormedSpace.exp (t • E.1)) (hv : ∀ v, v ≠ w → uMat (h.1 v) = 1) :
    h = GlobalTheory.SobolevBound.onePar B (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.atPlace B w E) t := by
  refine Prod.ext (funext fun v => Subtype.ext (Units.ext ?_)) h2
  change uMat (h.1 v) = NormedSpace.exp (t • (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.atPlace B w E v).1)
  by_cases c : v = w
  · subst c
    rw [hw, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.atPlace, Pi.single_eq_same]
  · rw [hv v c, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.atPlace, Pi.single_eq_of_ne c]
    simp

theorem hasDerivAt_switch (he : IsEquiv θ Φ) (hs : IsSob Φ) (τ : D.what₂.Tau) (u : M.Vec)
    {Y : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hY : Y ∈ lieAt V τ) {G : Type} [Group G] (T : GA D V ≃* G) (c : ℝ → G)
    (hc : ∀ t, T (oneP θ V τ Y t) = c t) (y : G) :
    HasDerivAt (fun t : ℝ => Φ u (T.symm (y * c t))) (Φ (Function.update u τ (der u τ hY)) (T.symm y)) 0 := by
  simp only [← hc, map_mul, T.symm_apply_apply]
  exact hasDerivAt_apply he hs τ u hY (T.symm y)

end Inst

end GlobalTheory.RepSmooth

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermAtBasePointOfFrames
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermAtBasePointOfFrames
noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

namespace GlobalTheory.Unfold.BasePt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem frame_castSucc {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (i : Fin D.R.rS) :
    frame F i.castSucc = F.fl.e i := by
  simp [frame, FlagG.fvec]

theorem tri_of_adapt {T : D.host.E} (g : GV D) (F G : LFlag (D.sp.Y 0) D.R.rS T) (hg : g ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (h : ∀ a : Fin (D.R.rS + 1), g (frame F a) - frame G a ∈ Xflag G a.val) :
    GlobalTheory.LocOver.Tri D.host.E (frame G) (frame (Formalism.L2.SG.Saturated.mapL g hg F)) := by
  have ex : ∀ b : Fin (D.R.rS + 1), ∃ l : Fin D.R.rS →₀ D.host.E,
      l ∈ Finsupp.supported D.host.E D.host.E {i : Fin D.R.rS | i.val < b.val} ∧
        Finsupp.linearCombination D.host.E G.fl.e l = g (frame F b) - frame G b := fun b =>
    (Finsupp.mem_span_image_iff_linearCombination D.host.E).1 (h b)
  choose l hl hx using ex
  have hz : ∀ b (i : Fin D.R.rS), ¬ i.val < b.val → l b i = 0 := fun b i hi =>
    (Finsupp.mem_supported' D.host.E (l b)).1 (hl b) i hi
  refine ⟨fun a b => (if a = b then 1 else 0) + (if h : a.val < D.R.rS then l b ⟨a.val, h⟩ else 0), ⟨?_, ?_⟩, ?_⟩
  · intro a b hba
    dsimp only
    rw [if_neg (ne_of_gt hba), zero_add]
    split_ifs with h'
    · exact hz b _ (by show ¬ a.val < b.val; have := Fin.lt_def.1 hba; omega)
    · rfl
  · intro a
    dsimp only
    rw [if_pos rfl]
    split_ifs with h'
    · rw [hz a _ (by simp), add_zero]
    · rw [add_zero]
  · intro b
    rw [Formalism.L2.SG.Saturated.frame_mapL]
    simp only [add_smul, Finset.sum_add_distrib, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.is_lt, dif_pos, Fin.val_last, lt_irrefl, dif_neg, not_false_eq_true,
      zero_smul, add_zero, frame_castSucc, Fin.eta]
    have e := hx b
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at e
    rw [e]
    abel

theorem term_at_base_point : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
      (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 →
      ∀ (t : TauC Y u u') (Λ : LV D), TG F F' t Λ → t.G ≠ 0 ∧ ptPN t = toPts w := by
  intro D X Y u u' F F' w hZ hG t Λ hTG
  obtain ⟨g, ⟨hg, h1⟩, ⟨-, h2⟩, -⟩ := hTG
  have hT : ((Tu D u : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero
  have hT' : ((Tu D u' : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (D.mem u').A.T_prime.ne_zero
  have hcell : IsInCell (ZhatOM (ZhatL F F')) w := by
    refine ⟨1, 1, fun i j => ⟨fun hij => Matrix.one_apply_ne (ne_of_lt hij), fun hij => by subst hij; exact Matrix.one_apply_eq i⟩,
      fun i j => ⟨fun hij => Matrix.one_apply_ne (ne_of_gt hij), fun hij => by subst hij; exact Matrix.one_apply_eq i⟩, ?_⟩
    rw [hZ, Matrix.one_mul, Matrix.mul_one]
  obtain ⟨-, hB⟩ := GlobalTheory.T.exists_unitriangular_frames_gram_eq_cell_point D F F' w hT hT' hcell
  obtain ⟨hcell2, hG2⟩ := hB _ _ (tri_of_adapt g (lf D (X.Fu u)) F hg h1) (tri_of_adapt g t.frame F' hg h2)
  replace hcell2 : IsInCell (ZhatOM (ZhatL (lf D (X.Fu u)) t.frame)) w :=
    (congrArg (fun Z => IsInCell (ZhatOM Z) w) (Formalism.L2.SG.Saturated.zhat_mapL g hg (lf D (X.Fu u)) t.frame)).mp hcell2
  replace hG2 : Gval (lf D (X.Fu u)) t.frame = Gval F F' :=
    (Formalism.L2.SG.Saturated.gval_mapL g hg (lf D (X.Fu u)) t.frame).symm.trans hG2
  have hGt : t.G ≠ 0 := by rw [Formalism.L2.SG.Pf.SatGram.gterm_G Y t, hG2]; exact hG
  have hat : t.toTerm.atPt w := ⟨t.frame, ⟨t.rep.2.2.2.2, rfl⟩, fun h0 => hG (hG2.symm.trans h0), hcell2⟩
  have hrel : t.toTerm.relevant := Formalism.L2.SG.Pf.FinXP.atPtRelevant_holds D u u' _ _ t.toTerm w hat
  have hsp := Formalism.L2.SG.PairVal.ptOf_spec t.toTerm ⟨w, hat, hrel⟩
  have heq := Formalism.L2.SG.Pf.cellPtUnique_of Formalism.L2.SG.Pf.cell_point_uniqueness
    (Formalism.L2.SG.Closed.TermFun_holds D u u') (Y.rowsOK u) t.toTerm _ _ hsp hat
  exact ⟨hGt, by show toPts (Formalism.L2.SG.PairVal.ptOf t.toTerm) = toPts w; rw [heq]⟩

end GlobalTheory.Unfold.BasePt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermAtBasePointOfFramesStatement
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.term_at_base_point_of_frames : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (t : TauC Y u u') (Λ : LV D), TG F F' t Λ → t.G ≠ 0 ∧ ptPN t = toPts w := by
  first | exact @GlobalTheory.Unfold.BasePt.term_at_base_point | exact GlobalTheory.Unfold.BasePt.term_at_base_point | (intros; apply GlobalTheory.Unfold.BasePt.term_at_base_point <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HarishChandraFormalDegreeCompactDualLargeGaps
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HarishChandraFormalDegreeCompactDualLargeGaps
noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S

namespace GlobalTheory.FdegGap

def plusFirst {N : ℕ} (ε : Fin N → Bool) :
    Fin (Fintype.card {a // ε a = true}) ⊕ Fin (Fintype.card {a // ¬ ε a = true}) ≃ Fin N :=
  (Equiv.sumCongr (Fintype.equivFin _).symm (Fintype.equivFin _).symm).trans
    (Equiv.sumCompl (fun a => ε a = true))

theorem plusFirst_inl {N : ℕ} (ε : Fin N → Bool) (i) : ε (plusFirst ε (Sum.inl i)) = true := by
  simp only [plusFirst, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumCompl_apply_inl]
  exact ((Fintype.equivFin {a // ε a = true}).symm i).2

theorem plusFirst_inr {N : ℕ} (ε : Fin N → Bool) (j) : ε (plusFirst ε (Sum.inr j)) = false := by
  simp only [plusFirst, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr, Equiv.sumCompl_apply_inr]
  simpa using ((Fintype.equivFin {a // ¬ ε a = true}).symm j).2

theorem muCD_eq_scaled (cd : CDHaar) (sc : ∀ n : ℕ, (Fin n → Bool) → NNReal)
    (hc : ∀ (n : ℕ) (ε : Fin n → Bool) (P Q : ℕ) (e : Fin P ⊕ Fin Q ≃ Fin n),
      (∀ i, ε (e (Sum.inl i)) = true) → (∀ j, ε (e (Sum.inr j)) = false) →
      ∀ A : Set (Formalism.REAL.UJ ε), MeasurableSet A →
        ((sc n ε : ENNReal) • Formalism.REAL.muG ε) A =
          cd.cd P Q {g | ∃ a ∈ A, umat a = Matrix.reindex e e (UpqT.mat g)})
    {N : ℕ} (ε : Fin N → Bool) :
    ReciprocityTheory.ChartRestriction.DS.muCD ε = (sc N ε : ENNReal) • Formalism.REAL.muG ε := by
  ext A hA
  rw [ReciprocityTheory.ChartRestriction.DS.muCD_eq_cd_vol cd (plusFirst ε) (plusFirst_inl ε) (plusFirst_inr ε) A hA]
  exact (hc N ε _ _ (plusFirst ε) (plusFirst_inl ε) (plusFirst_inr ε) A hA).symm

theorem one_le_p {N : ℕ} {ε : Fin N → Bool} (h : ∃ a, ε a = true) : 1 ≤ ReciprocityTheory.ChartRestriction.DS.pOf ε := by
  obtain ⟨a, ha⟩ := h
  exact Finset.card_pos.mpr ⟨a, by simp [ha]⟩

theorem one_le_q {N : ℕ} {ε : Fin N → Bool} (h : ∃ a, ε a = false) : 1 ≤ ReciprocityTheory.ChartRestriction.DS.qOf ε := by
  obtain ⟨a, ha⟩ := h
  exact Finset.card_pos.mpr ⟨a, by simp [ha]⟩

theorem thrStar_eq {N : ℕ} (ε : Fin N → Bool) : ReciprocityTheory.ChartRestriction.DS.thrStar ε = Formalism.MainNotions.GapDS.thrE ε := by
  unfold ReciprocityTheory.ChartRestriction.DS.thrStar Formalism.MainNotions.GapDS.thrE Formalism.MainNotions.GapDS.thrDS
  rfl

theorem fdeg_gap : ∀ (cd : CDHaar) (sc : ∀ n : ℕ, (Fin n → Bool) → NNReal),
    (∀ (n : ℕ) (ε : Fin n → Bool) (P Q : ℕ) (e : Fin P ⊕ Fin Q ≃ Fin n),
      (∀ i, ε (e (Sum.inl i)) = true) → (∀ j, ε (e (Sum.inr j)) = false) →
      ∀ A : Set (Formalism.REAL.UJ ε), MeasurableSet A →
        ((sc n ε : ENNReal) • Formalism.REAL.muG ε) A =
          cd.cd P Q {g | ∃ a ∈ A, umat a = Matrix.reindex e e (UpqT.mat g)}) →
    ∀ (N : ℕ) (ε : Fin N → Bool) (lam : Fin N → ℝ) (h : ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
      (∃ a, ε a = true) → (∃ a, ε a = false) → Formalism.QuantumDeterminants.GapAtLeast ε lam h → Formalism.MainNotions.GapDS.thrE ε + 1 < h →
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)), IsDS ε lam σ →
        IsFdeg ((sc N ε : ENNReal) • Formalism.REAL.muG ε) σ (Formalism.QuantumDeterminants.fdegHC lam) := by
  intro cd sc hc N ε lam h hlam hp hq hgap hh H _ _ σ hσ
  haveI : CompleteSpace H := hσ.1
  haveI : Nontrivial H := hσ.2.1
  have hCD := muCD_eq_scaled cd sc hc ε
  have hp1 := one_le_p hp
  have hq1 := one_le_q hq
  have hh' : ReciprocityTheory.ChartRestriction.DS.thrStar ε + 1 < h := by rw [thrStar_eq]; exact hh
  have hq0 : 1 ≤ ReciprocityTheory.ChartRestriction.DS.S7.q0 ε := le_min hp1 hq1
  have h8 : 8 * (N : ℝ) * ReciprocityTheory.ChartRestriction.DS.S7.q0 ε < h := by
    have hm : 16 * (N : ℝ) * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ) + 8 * Real.sqrt (2 * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ))
        ≤ ReciprocityTheory.ChartRestriction.DS.thrStar ε := le_max_right _ _
    have h0 : (0 : ℝ) ≤ (N : ℝ) * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ) := by positivity
    have hs : (0 : ℝ) ≤ Real.sqrt (2 * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ)) := Real.sqrt_nonneg _
    nlinarith
  have hΨ : ∀ μ : Fin N → ℝ, ReciprocityTheory.ChartRestriction.DS.S7.IsHCParam μ → ReciprocityTheory.ChartRestriction.DS.GapAtLeast ε μ h →
      ∃ (T : ReciprocityTheory.ChartRestriction.DS.S7.KType ε (ReciprocityTheory.ChartRestriction.DS.lowK ε μ))
        (Ψ : Matrix (Fin N) (Fin N) ℂ → (T.V →L[ℂ] T.V)), ReciprocityTheory.ChartRestriction.DS.IsPsiFor ε μ T Ψ := by
    intro μ hμ hμg
    obtain ⟨T⟩ := ReciprocityTheory.ChartRestriction.DS.HW.kType_exists ε μ hμ
    obtain ⟨m, hm⟩ := ReciprocityTheory.ChartRestriction.DS.Lap.LemK.exists_isMu hμ
    exact ⟨T, _, (ReciprocityTheory.ChartRestriction.DS.Lap.Base.psiFor N ε μ h T m hμ hm hμg hq0 h8).1⟩
  obtain ⟨w, hw⟩ := exists_ne (0 : H)
  have hdim : fdegOf (ReciprocityTheory.ChartRestriction.DS.muCD ε) σ w = ReciprocityTheory.ChartRestriction.DS.dimVlam lam :=
    ReciprocityTheory.ChartRestriction.DS.fdCons_cd hp1 hq1 hlam hgap hh' hΨ hσ hw
  obtain ⟨d, hd⟩ := Formalism.MainNotions.BridgeCSchur.fdeg_of_DS lam σ hσ
  have hpos : (0 : ℝ) < (sc N ε : ℝ) := by
    rcases (sc N ε).coe_nonneg.lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      haveI := ReciprocityTheory.ChartRestriction.DS.muCD_isHaar ε
      have hz : sc N ε = 0 := by exact_mod_cast heq.symm
      have hne := (isOpen_univ (X := Formalism.REAL.UJ ε)).measure_ne_zero (ReciprocityTheory.ChartRestriction.DS.muCD ε) Set.univ_nonempty
      rw [hCD, hz] at hne
      simp at hne
  have hsc : IsFdeg ((sc N ε : ENNReal) • Formalism.REAL.muG ε) σ (d / (sc N ε : ℝ)) := by
    have := ReciprocityTheory.ChartRestriction.DS.isFdeg_smul hpos hd
    rwa [ENNReal.ofReal_coe_nnreal] at this
  have hval : d / (sc N ε : ℝ) = Formalism.QuantumDeterminants.fdegHC lam := by
    have h1 := ReciprocityTheory.ChartRestriction.DS.fdegOf_of_isFdeg' (hCD ▸ hsc) hw
    rw [h1] at hdim
    rw [hdim, ReciprocityTheory.ChartRestriction.DS.dimVlam_eq_vand hlam.1, Formalism.MainNotions.BridgeLemma.szh_fdegHC lam hlam.1]
    rfl
  rwa [hval] at hsc

end GlobalTheory.FdegGap
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HarishChandraFormalDegreeCompactDualLargeGapsStatement
open Formalism.BasicNotions Formalism.MainNotions.S MeasureTheory

theorem _root_.GlobalTheory.T.harishChandra_formalDegree_compactDual_large_gaps : ∀ (cd : CDHaar) (sc : ∀ n : ℕ, (Fin n → Bool) → NNReal),
    (∀ (n : ℕ) (ε : Fin n → Bool) (P Q : ℕ) (e : Fin P ⊕ Fin Q ≃ Fin n),
      (∀ i, ε (e (Sum.inl i)) = true) → (∀ j, ε (e (Sum.inr j)) = false) →
      ∀ A : Set (Formalism.REAL.UJ ε), MeasurableSet A →
        ((sc n ε : ENNReal) • Formalism.REAL.muG ε) A =
          cd.cd P Q {g | ∃ a ∈ A, umat a = Matrix.reindex e e (UpqT.mat g)}) →
    ∀ (N : ℕ) (ε : Fin N → Bool) (lam : Fin N → ℝ) (h : ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
      (∃ a, ε a = true) → (∃ a, ε a = false) → Formalism.QuantumDeterminants.GapAtLeast ε lam h → Formalism.MainNotions.GapDS.thrE ε + 1 < h →
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)), IsDS ε lam σ →
        IsFdeg ((sc N ε : ENNReal) • Formalism.REAL.muG ε) σ (Formalism.QuantumDeterminants.fdegHC lam) :=
  GlobalTheory.FdegGap.fdeg_gap
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalFramePairsDifferIsometryUnitriangular
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalFramePairsDifferIsometryUnitriangular
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocOver.WittFrames

theorem zhatOM_injective {K : Type*} [CommRing K] {r : ℕ} {Z Z' : Matrix (Fin (r + 1)) (Fin (r + 1)) K}
    (h : ZhatOM Z = ZhatOM Z') : Z = Z' := by
  ext a b
  have h1 := congrFun (congrFun h a) b
  simp only [ZhatOM] at h1
  exact ((isUnit_one.neg).pow (r - b.val)).mul_left_cancel h1

theorem tri_symm {E W : Type} [Field E] [AddCommGroup W] [Module E W] {n : ℕ} {f g : Fin n → W}
    (h : Tri E f g) : Tri E g f := by
  obtain ⟨A, ⟨hA1, hA2⟩, hc⟩ := h
  have hbt : A.BlockTriangular id := fun i j hij => hA1 i j hij
  have hdet : A.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hbt]; simp [hA2]
  have hu : IsUnit A.det := by rw [hdet]; exact isUnit_one
  obtain ⟨hB1, hB2⟩ := inv_unitri A hA1 hA2
  have hc' : ∀ b, g b = ∑ a, A a b • f a := hc
  refine ⟨A⁻¹, ⟨hB1, hB2⟩, fun b => ?_⟩
  show f b = ∑ a, A⁻¹ a b • g a
  have hm := Matrix.mul_nonsing_inv A hu
  simp_rw [hc', Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  have : ∀ c, ∑ a, (A⁻¹ a b * A c a) • f c = (A * A⁻¹) c b • f c := by
    intro c
    rw [← Finset.sum_smul, Matrix.mul_apply]
    congr 1
    exact Finset.sum_congr rfl (fun a _ => mul_comm _ _)
  simp_rw [this, hm, Matrix.one_apply, ite_smul, one_smul, zero_smul]
  simp

theorem tri_map {E W : Type} [Field E] [AddCommGroup W] [Module E W] {n : ℕ} {f g : Fin n → W}
    (γ : W →ₗ[E] W) (h : Tri E f g) : Tri E (fun a => γ (f a)) (fun a => γ (g a)) := by
  obtain ⟨A, hA, hc⟩ := h
  have hc' : ∀ b, g b = ∑ a, A a b • f a := hc
  refine ⟨A, hA, fun b => ?_⟩
  show γ (g b) = ∑ a, A a b • γ (f a)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hc' b, map_sum]
  simp [map_smul]

theorem exists_isom_of_gram (hW : PI.WittExtension) {K V : Type} [Field K] [StarRing K] [CharZero K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (B : V →ₗ⋆[K] V →ₗ[K] K) (hs : ∀ x y, star (B x y) = B y x) (hn : ∀ x, (∀ y, B x y = 0) → x = 0)
    {ι : Type} (v v' : ι → V) (hv : LinearIndependent K v) (hv' : LinearIndependent K v')
    (hg : ∀ i j, B (v i) (v j) = B (v' i) (v' j)) :
    ∃ g : V ≃ₗ[K] V, (∀ x y, B (g x) (g y) = B x y) ∧ ∀ i, g (v i) = v' i := by
  let U := Submodule.span K (Set.range v)
  let bU : Module.Basis ι K U := Module.Basis.span hv
  have hbU : ∀ i, (bU i : V) = v i := fun i => congrArg Subtype.val (Module.Basis.span_apply hv i)
  let f : U →ₗ[K] V := bU.constr K v'
  have hf : ∀ i, f (bU i) = v' i := fun i => by simp [f, Module.Basis.constr_basis]
  have hfe : f = Finsupp.linearCombination K v' ∘ₗ bU.repr.toLinearMap := by
    refine bU.ext (fun i => ?_)
    rw [hf]; simp
  have hinj : Function.Injective f := by
    rw [hfe, LinearMap.coe_comp]
    exact Function.Injective.comp hv' bU.repr.injective
  have hiso : ∀ x y : U, B (f x) (f y) = B x y := by
    have : (B.comp f).compl₂ f = (B.comp U.subtype).compl₂ U.subtype := by
      refine LinearMap.ext_basis bU bU (fun i j => ?_)
      simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, Submodule.subtype_apply, hf, hbU]
      exact (hg i j).symm
    intro x y
    have := LinearMap.congr_fun₂ this x y
    simpa using this
  obtain ⟨g, hg1, hg2⟩ := hW K V B hs hn U f hinj hiso
  exact ⟨g, hg1, fun i => by rw [← hbU i, hg2, hf]⟩

end GlobalTheory.LocOver.WittFrames

namespace GlobalTheory.LocOver


open GlobalTheory.LocOver.WittFrames Formalism.L2.SG.GramJoint in
theorem witt_frames_at_point : ∀ (D : D7) {T T' : D.host.E} (F F00 : LFlag (D.sp.Y 0) D.R.rS T)
    (F' F'0 : LFlag (D.sp.Y 0) D.R.rS T') (w : Point D.host.E (D.R.rS + 1)), T ≠ 0 → T' ≠ 0 → Gval F F' ≠ 0 →
    IsInCell (ZhatOM (ZhatL F F')) w → ZhatOM (ZhatL F00 F'0) = ptMat w →
    Gval F00 F'0 = Gval F F' ∧ ∃ γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT,
      Tri D.host.E (frame F00) (fun a => γ (frame F a)) ∧ Tri D.host.E (frame F'0) (fun a => γ (frame F' a)) := by
  intro D T T' F F00 F' F'0 w hT hT' hG hcell hpt
  obtain ⟨⟨Fb, Fb', h1, h2, hb⟩, hall⟩ := GlobalTheory.T.exists_unitriangular_frames_gram_eq_cell_point D F F' w hT hT' hcell
  have hGb : Gval Fb Fb' = Gval F F' := (hall Fb Fb' h1 h2).2
  have hZ : ZhatL Fb Fb' = ZhatL F00 F'0 := zhatOM_injective (hb.trans hpt.symm)
  have hG0 : Gval F00 F'0 = Gval Fb Fb' := by
    show Gmat (Zhat F00.fl F'0.fl) T T' = Gmat (Zhat Fb.fl Fb'.fl) T T'
    exact congrArg (fun Z => Gmat Z T T') hZ.symm
  refine ⟨hG0.trans hGb, ?_⟩
  have hGb0 : Gflag Fb.fl Fb'.fl ≠ 0 := by rw [← hGb] at hG; exact hG
  have hG00 : Gflag F00.fl F'0.fl ≠ 0 := by
    have := hG0.trans hGb; rw [← this] at hG; exact hG
  have hli := (gramIndep D.host.E (VS D) D.R.rS T T' Fb.fl Fb'.fl hGb0).1
  have hli' := (gramIndep D.host.E (VS D) D.R.rS T T' F00.fl F'0.fl hG00).1
  have hgram : ∀ i j, (VS D).hT (pairVec Fb.fl Fb'.fl i) (pairVec Fb.fl Fb'.fl j) =
      (VS D).hT (pairVec F00.fl F'0.fl i) (pairVec F00.fl F'0.fl j) := by
    intro i j
    have e := congrFun (congrFun (gramBlocks D.host.E (VS D) D.R.rS T T' Fb.fl Fb'.fl) i) j
    have e' := congrFun (congrFun (gramBlocks D.host.E (VS D) D.R.rS T T' F00.fl F'0.fl) i) j
    have hZ' : Zhat Fb.fl Fb'.fl = Zhat F00.fl F'0.fl := hZ
    rw [hZ'] at e
    exact e.trans e'.symm
  have hs : ∀ x y, star ((VS D).hT x y) = (VS D).hT y x := fun x y => (VS D).herm.eq x y
  have hn : ∀ x, (∀ y, (VS D).hT x y = 0) → x = 0 := fun x hx => (VS D).nondeg.1 x hx
  obtain ⟨γ, hγ, hγv⟩ := exists_isom_of_gram witt_extension_theorem (VS D).hT hs hn _ _ hli hli' hgram
  refine ⟨γ, fun x y => hγ x y, ?_, ?_⟩
  · have := tri_map (γ : (VS D).V →ₗ[D.host.E] (VS D).V) h1
    have e : (fun a => (γ : (VS D).V →ₗ[D.host.E] (VS D).V) (frame Fb a)) = frame F00 :=
      funext fun a => hγv (Sum.inl a)
    rw [e] at this
    exact tri_symm this
  · have := tri_map (γ : (VS D).V →ₗ[D.host.E] (VS D).V) h2
    have e : (fun a => (γ : (VS D).V →ₗ[D.host.E] (VS D).V) (frame Fb' a)) = frame F'0 :=
      funext fun a => hγv (Sum.inr a)
    rw [e] at this
    exact tri_symm this

end GlobalTheory.LocOver
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalFramePairsDifferIsometryUnitriangularStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalFramePairs_differ_isometry_unitriangular : ∀ (D : D7) {T T' : D.host.E} (F F00 : LFlag (D.sp.Y 0) D.R.rS T) (F' F'0 : LFlag (D.sp.Y 0) D.R.rS T') (w : Point D.host.E (D.R.rS + 1)), T ≠ 0 → T' ≠ 0 → Gval F F' ≠ 0 → IsInCell (ZhatOM (ZhatL F F')) w → ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 = Gval F F' ∧ ∃ γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT, Tri D.host.E (frame F00) (fun a => γ (frame F a)) ∧ Tri D.host.E (frame F'0) (fun a => γ (frame F' a)) := by
  first | exact @GlobalTheory.LocOver.witt_frames_at_point | exact GlobalTheory.LocOver.witt_frames_at_point | (intros; apply GlobalTheory.LocOver.witt_frames_at_point <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GluedUnimodularLatticeIffLocalCompletions
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GluedUnimodularLatticeIffLocalCompletions
noncomputable section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GenMass.GlueLoc

open Formalism.L2.SG.Pf Formalism.L2.SG.Pf.Cnt

variable {D : D7} (Z : LocDat D)

def locSp : Formalism.L2.SG.CntLocal.LocSp D Z.M where
  V := Vp D
  H := locH Z
  rank := finrank_Vp
  bc := baseChange₂ D
  bc_smul := baseChange_smul₂
  bc_span := span_baseChange_eq_top
  bc_form p := baseChangeAt_form Z.M p (Z.hcj p)

theorem eq_of_latP {A B : LV D} (hA : A.FG) (hB : B.FG) (h : ∀ p, lattice₂ D Z.M p A = lattice₂ D Z.M p B) : A = B := by
  apply eq_of_locP
  intro P
  exact (locEqC_holds D Z (P.under (𝓞 D.host.F)) A B hA hB).1 (h _) P rfl

theorem mem_of_bcP {Λ : LV D} (hΛ : Λ.FG) {x : (VS D).V} (h : ∀ p, baseChange₂ D p x ∈ lattice₂ D Z.M p Λ) : x ∈ Λ := by
  have e : Λ ⊔ Submodule.span (𝓞 D.host.E) {x} = Λ := by
    refine eq_of_latP Z (hΛ.sup (Submodule.fg_span_singleton x)) hΛ fun p => ?_
    rw [BBTie.latP_sup, BBTie.latP_span, sup_eq_left, Submodule.span_le]
    rintro _ ⟨y, rfl, rfl⟩
    exact h p
  rw [← e]
  exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)

theorem mem_dual_iff (Λ : LV D) (x : (VS D).V) :
    x ∈ Formalism.HermitianLatticesTheory.dual (VS D).hT Λ ↔ ∀ y ∈ Λ, (VS D).hT y x ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
  simp [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf]

theorem unimod_of_loc {Λ : LV D} (hΛ : Λ.FG) (hloc : ∀ p, (locH Z p).IsSelfDual (lattice₂ D Z.M p Λ)) :
    Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ := by
  have hf : ∀ p x y, (locH Z p).h (baseChange₂ D p x) (baseChange₂ D p y) = (D.s.atP p).ιE ((VS D).hT y x) :=
    fun p x y => baseChangeAt_form Z.M p (Z.hcj p) x y
  ext x
  rw [mem_dual_iff]
  constructor
  · intro h
    refine mem_of_bcP Z hΛ fun p => ((hloc p).2.2 _).2 fun w hw => ?_
    change LocFacts₂ Z.M p (baseChange₂ D p x) w ∈ _
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨y, hy, rfl⟩ := hw
      change (locH Z p).h _ _ ∈ _
      rw [hf]
      obtain ⟨o, ho⟩ := Submodule.mem_one.1 (h y hy)
      rw [← ho]
      exact BBTie.bt_iota_int Z p o
    | zero => rw [LocFacts.localForm_zero_right]; exact zero_mem _
    | add a b _ _ ha hb => rw [LocFacts.localForm_add_right]; exact add_mem ha hb
    | smul o w _ hw =>
      change LocFacts₂ Z.M p (baseChange₂ D p x) ((o : (D.s.atP p).Ep) • w) ∈ _
      rw [LocFacts.localForm_smul_right]
      exact mul_mem (LocFacts.lf_cjM_mem Z p _ o.2) hw
  · intro hx y hy
    refine DualityBasisChange.locGlobIntE D _ fun p => ?_
    rw [← hf, ← (Z.agree p).2.2.2.1]
    exact ((hloc p).2.2 (baseChange₂ D p x)).1 (Submodule.subset_span ⟨x, hx, rfl⟩) (baseChange₂ D p y)
      (Submodule.subset_span ⟨y, hy, rfl⟩)

variable (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) {T T' : D.host.E}
  (G : LFlag (D.sp.Y 0) D.R.rS T) (G' : LFlag (D.sp.Y 0) D.R.rS T')

theorem mmfam_eq (p : PlF D) (Λ : Submodule (Z.M p).L.O (Vp D p)) :
    (locH Z p).MMfam (tm FP G G' p Λ) = DualityBasisChange.locFam (locSp Z) Z.δ p G.fl G' := by
  funext b
  unfold Loc.HermSp.MMfam
  cases hs : (Z.M p).split with
  | none =>
    rw [DualityBasisChange.locFam_none (locSp Z) p G.fl G' hs]
    rcases b with a | a <;> rfl
  | some g =>
    rcases b with a | a
    · rw [DualityBasisChange.locFam_some_inl (locSp Z) p G.fl G' hs]; rfl
    · rw [DualityBasisChange.locFam_some_inr (locSp Z) p G.fl G' hs]; rfl

theorem span_mmfam (p : PlF D) (Λ : Submodule (Z.M p).L.O (Vp D p)) :
    Submodule.span (Z.M p).L.O (Set.range ((locH Z p).MMfam (tm FP G G' p Λ))) =
      lattice₂ D Z.M p (MMof D G.fl G') := by
  rw [mmfam_eq]
  exact DualityBasisChange.span_locFam Z.agree (locSp Z) p G.fl G'

theorem mmof_latIn : IsLatIn (UPair D G.fl G') (MMof D G.fl G') := by
  rw [R3.MMof_eq]; exact R3.BB_latIn D G.fl G'

theorem spanE_mmfam (p : PlF D) (Λ : Submodule (Z.M p).L.O (Vp D p)) :
    Submodule.span (D.s.atP p).Ep (Set.range ((locH Z p).MMfam (tm FP G G' p Λ))) =
      Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (UPair D G.fl G' : Set (VS D).V)) := by
  rw [← BBTie.bt_spanEp_spanO Z p, span_mmfam, lattice₂, BBTie.bt_spanEp_spanO Z p, ← (mmof_latIn G G').2,
    BBTie.bt_spanEp_spanE]

theorem glue_iff_local : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (u u' : D.what₂.Word) (G : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (G' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)), LinearIndependent D.host.E (Sum.elim (frame G) (frame G')) → ∀ Λ : LV D, Λ ∈ Formalism.L2.SG.Pf.Cnt.GlueSet (VS D).hT (Formalism.L2.SG.Pf.Cnt.UPair D G.fl G') (Formalism.L2.SG.Pf.Cnt.MMof D G.fl G') ↔ Submodule.IsLattice D.host.E Λ ∧ ∀ p, (locH Z p).IsSelfDual (lattice₂ D Z.M p Λ) ∧ (∀ i, (locH Z p).MMfam (tm FP G G' p (lattice₂ D Z.M p Λ)) i ∈ lattice₂ D Z.M p Λ) ∧ ¬ LocNG.BBne (H := locH Z p) (tm FP G G' p (lattice₂ D Z.M p Λ)) := by
  intro D Z FP u u' G G' _ Λ
  constructor
  · rintro ⟨hL, hU, hM⟩
    refine ⟨hL, fun p => ?_⟩
    have hle : lattice₂ D Z.M p (MMof D G.fl G') ≤ lattice₂ D Z.M p Λ :=
      BBTie.latP_mono Z p (hM ▸ inf_le_left)
    refine ⟨BBTie.bt_selfDual Z (locUnimodC_holds D Z) p Λ hL hU, fun i => hle ?_, ?_⟩
    · rw [← span_mmfam Z FP G G' p (lattice₂ D Z.M p Λ)]
      exact Submodule.subset_span ⟨i, rfl⟩
    · rw [BBTie.bt_bbne_iff Z p (locSatC_holds D Z) (tm FP G G' p (lattice₂ D Z.M p Λ)) Λ
        (MMof D G.fl G') (UPair D G.fl G') hL.fg rfl
        (span_mmfam Z FP G G' p _) (spanE_mmfam Z FP G G' p _) hle, not_not]
      exact congrArg _ hM
  · rintro ⟨hL, h⟩
    refine ⟨hL, unimod_of_loc Z hL.fg fun p => (h p).1, ?_⟩
    refine eq_of_latP Z (Submodule.FG.of_le hL.fg inf_le_left) (mmof_latIn G G').1 fun p => ?_
    have hle : lattice₂ D Z.M p (MMof D G.fl G') ≤ lattice₂ D Z.M p Λ := by
      rw [← span_mmfam Z FP G G' p (lattice₂ D Z.M p Λ), Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact (h p).2.1 i
    have h3 := (h p).2.2
    rw [BBTie.bt_bbne_iff Z p (locSatC_holds D Z) (tm FP G G' p (lattice₂ D Z.M p Λ)) Λ
        (MMof D G.fl G') (UPair D G.fl G') hL.fg rfl
      (span_mmfam Z FP G G' p _) (spanE_mmfam Z FP G G' p _) hle, not_not] at h3
    exact h3

end GlobalTheory.GenMass.GlueLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GluedUnimodularLatticeIffLocalCompletionsStatement
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glued_unimodular_lattice_iff_local_completions : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (u u' : D.what₂.Word) (G : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (G' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)), LinearIndependent D.host.E (Sum.elim (frame G) (frame G')) → ∀ Λ : LV D, Λ ∈ Formalism.L2.SG.Pf.Cnt.GlueSet (VS D).hT (Formalism.L2.SG.Pf.Cnt.UPair D G.fl G') (Formalism.L2.SG.Pf.Cnt.MMof D G.fl G') ↔ Submodule.IsLattice D.host.E Λ ∧ ∀ p, (locH Z p).IsSelfDual (lattice₂ D Z.M p Λ) ∧ (∀ i, (locH Z p).MMfam (tm FP G G' p (lattice₂ D Z.M p Λ)) i ∈ lattice₂ D Z.M p Λ) ∧ ¬ LocNG.BBne (H := locH Z p) (tm FP G G' p (lattice₂ D Z.M p Λ)) := by
  first | exact @GlobalTheory.GenMass.GlueLoc.glue_iff_local | exact GlobalTheory.GenMass.GlueLoc.glue_iff_local | (intros; apply GlobalTheory.GenMass.GlueLoc.glue_iff_local <;> assumption)
end
end
