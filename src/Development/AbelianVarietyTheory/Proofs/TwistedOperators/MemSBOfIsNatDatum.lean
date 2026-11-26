module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaTripleOfSquareGridLatticeCompatible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPartialFourierColumnBlockSchwartzBruhat
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZetaIdentityPersistsRowColumnChanges
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMixedLagrangianChartIntegralRowChange
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedLagrangianOppositeLagrangianChart
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsScalarFiniteTensorEqDatumSmallModel

@[expose] public section

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL Formalism.DoubleCosetMeasures.instMeasMat GroundTheory.Automorphic.GJMatrix.measurableSpace_matrix

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGaussianVacuumProductUnitVacua
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGaussianVacuumProductUnitVacua
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

noncomputable section

namespace GlobalTheory.FlipVac

theorem exists_gauss_vac : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (M : Vol G) (hst : SquareStanding G t) (e : Num G i j) (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
    (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (h : IsTripleOf W M t i j e Bs Γ X), IsTriple Bs Γ X om om' → IsTied t i j e Bs Γ X →
    ∃ f₀, f₀ ≠ 0 ∧ Γ.M.IsGauss Bs.ψ Bs.emb f₀ ∧
      IsDatumA (t := t) W e Γ (Finsupp.single (((), ρ.vX i (j + 1)), ρ.vT (i + 1) j) 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ Γ.M.vac) := by
  intro D T L sc G μ₀ hL W ρ t i j M _ e Bs Γ X om om' h hT hti
  have h₁ := ρ.vX_is i (j + 1) i.2 j.2
  have h₂ := ρ.vT_is t (i + 1) j i.2 j.2
  have hG : Γ.M.IsGood W.ψ := h.ψ ▸ hT.geo.hM
  obtain ⟨f, hf⟩ := GlobalTheory.BigDat.exists_vac hL h hT hti h₁ h₂
  refine ⟨f, fun h0 => ?_, GlobalTheory.BigDat.isGauss (c := 1) h hT h₁ h₂ (by rw [hf, one_smul]),
    (isFinPart_vac hG ∅).fam.mem hG f, fun u => ?_⟩
  · obtain ⟨x, hx⟩ := Function.ne_iff.1 (GlobalTheory.BigDat.vac_ne_zero h₁)
    obtain ⟨y, hy⟩ := Function.ne_iff.1 (GlobalTheory.BigDat.vac_ne_zero h₂)
    have := congrFun hf (GlobalTheory.BigDat.ofMaps e (x, y))
    rw [h0, show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (0 : SInf D.host.F (GlobalTheory.BigDat.Ix G i j)) Γ.M.vac =
        (0 : ℂ) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure 0 Γ.M.vac from funext fun _ => (zero_mul _).trans (zero_mul _).symm,
      GlobalTheory.BigDat.thetaPt_smul, zero_mul, GlobalTheory.BigDat.box, GlobalTheory.BigDat.mapV_ofMaps, GlobalTheory.BigDat.mapW_ofMaps] at this
    exact mul_ne_zero hx hy this.symm
  · refine (congrFun hf u).trans ?_
    first
    | exact (one_mul _).symm.trans (Finsupp.sum_single_index (h := fun d (c : ℂ) => c * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.boxA e d u) (zero_mul _)).symm
    | (erw [Finsupp.sum_single_index (by exact zero_mul _), one_mul]; rfl)
    | (simp only [Finsupp.sum_single_index, zero_mul, one_mul]; rfl)

end GlobalTheory.FlipVac

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGaussianVacuumProductUnitVacuaStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_gaussianVacuum_product_unitVacua : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (M : Vol G) (hst : SquareStanding G t) (e : Num G i j) (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
    (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (h : IsTripleOf W M t i j e Bs Γ X), IsTriple Bs Γ X om om' → IsTied t i j e Bs Γ X →
    ∃ f₀, f₀ ≠ 0 ∧ Γ.M.IsGauss Bs.ψ Bs.emb f₀ ∧
      IsDatumA (t := t) W e Γ (Finsupp.single (((), ρ.vX i (j + 1)), ρ.vT (i + 1) j) 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ Γ.M.vac) := by
  first | exact @GlobalTheory.FlipVac.exists_gauss_vac | exact GlobalTheory.FlipVac.exists_gauss_vac | (intros; apply GlobalTheory.FlipVac.exists_gauss_vac <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitVacuaProductEqGaussianDatumSmallModel
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PureVacInj
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

noncomputable section

namespace GlobalTheory.SmallGauss

open GlobalTheory.SmallDat GlobalTheory.TripleCplxAt
open scoped ComplexConjugate

theorem pure_vac_inj {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {Y : Spc F E d} {M : Model σ X Y} {ψ : AddChar (AF F) ℂ} (hG : M.IsGood ψ)
    {f f' : SInf F (Fin n × Fin d)} (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f M.vac = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f' M.vac) : f = f' := by
  classical
  choose ξ hξ using fun v => Function.ne_iff.1 (hG.vac v).2.1
  have hS := Filter.eventually_cofinite.1 hG.std
  let y : Fin n × Fin d → Af F := fun k => ∑ v ∈ hS.toFinset, singleFin v (ξ v k)
  have hy : finPartFn M.vac y ≠ 0 := by
    refine finprod_induction (· ≠ (0 : ℂ)) one_ne_zero (fun _ _ => mul_ne_zero) fun v => ?_
    by_cases hv : v ∈ hS.toFinset
    · have : (fun k => evalV F v (y k)) = ξ v := funext fun k => by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, Finset.sum_eq_single_of_mem v hv fun v' _ h => evalV_singleFin_ne h.symm _, evalV_singleFin_self]
      rw [this]
      exact hξ v
    · have : (fun k => evalV F v (y k)) = 0 := funext fun k => by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        exact Finset.sum_eq_zero fun v' h => evalV_singleFin_ne (fun e : v = v' => hv (e ▸ h)) _
      rw [this, of_not_not (mt hS.mem_toFinset.2 hv), Set.indicator_of_mem (by exact fun _ => zero_mem _)]
      exact one_ne_zero
  ext z
  have := congrFun h fun k => pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace _).symm (z k)) (y k)
  simp only [pure_eq, pureA, pairA, RingEquiv.apply_symm_apply] at this
  exact mul_right_cancel₀ hy this

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {i j : ℕ}

theorem compAt_mapA (θ : InfFam D) (hθ : IsInfFam θ) (τ : D.what₂.Tau) (t : T) (e : Num G i j) (u : PtS G i j) :
    compAt θ τ (mapA t e u) = ((compAt θ τ u).submatrix id fun k => e (.inl k))ᵀ * gramAt D (spW₁ G i j) τ := by
  show compAt θ τ (HMul.hMul (colV e u)ᵀ ((spW₁ G i j).gram.map (incA D))) = _
  rw [compAt_mul', compAt_inc θ hθ]
  rfl

theorem compAt_mapB (θ : InfFam D) (hθ : IsInfFam θ) (τ : D.what₂.Tau) (e : Num G i j) (u : PtS G i j) :
    compAt θ τ (mapB e u) = -(((compAt θ τ u).submatrix id fun k => e (.inr k)).map conj * gramAt D (spV₁ G i j) τ) := by
  show compAt θ τ (-HMul.hMul ((u.submatrix id fun k => e (.inr k)).map (cA D)) ((spV₁ G i j).gram.map (incA D))) = _
  rw [compAt_neg', compAt_mul', compAt_inc θ hθ, compAt_conj θ hθ]
  rfl


open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (blk) in
theorem cplx_pairS {W : G.Weil} {M : Vol G} {t : T} {i j : Fin D.R.m} {e : Num G i j} {Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E}
    {Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j} {X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E} (h : IsTripleOf W M t i j e Bs Γ X) (u u' : PtS G i j)
    (hu : ∀ w, u'.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w)) =
      Complex.I • (Γ.V'.θ w * u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w)) * (Γ.W.θ w)ᵀ)) (τ : D.what₂.Tau) :
    compAt W.θ τ (mapA t e u') = cplxO (W.cart (.grid i j) τ) (W.cart (.grid i (j + 1)) τ) (compAt W.θ τ (mapA t e u)) ∧
    compAt W.θ τ (mapB e u') = cplxO (-W.cart (.grid (i + 1) j) τ) (W.cart (.grid i j) τ) (compAt W.θ τ (mapB e u)) := by
  obtain ⟨w, hpi, hV, hWW⟩ : ∃ w, (∀ y, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w) y = conj (W.θ τ (infPart D y))) ∧
      Γ.V'.θ w = -W.cart (.grid i j) τ ∧
      Γ.W.θ w = (blk e (W.cart (.grid i (j + 1)) τ) (W.cart (.grid (i + 1) j) τ)).map conj := by
    obtain ⟨w, hw⟩ : ∃ w : InfinitePlace D.host.F, w = InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E)) :=
      ⟨_, rfl⟩
    obtain ⟨τ', hemb, -, hV, hWW⟩ := h.cart w
    have h1 : (Bs.emb w).1.comp (algebraMap D.host.F D.host.E) = w.embedding := (Bs.emb w).2
    have h2 : (tauE D τ').comp (algebraMap D.host.F D.host.E) = NumberField.ComplexEmbedding.conjugate w.embedding := by
      ext x
      rw [NumberField.ComplexEmbedding.conjugate_coe_eq, ← h1]
      simp [hemb]
    have hh : ((starRingEnd ℂ).comp (tauE D τ')).comp (algebraMap D.host.F D.host.E) = w.embedding := by
      rw [← h1]; ext x; simp [hemb]
    have hb : Bs.emb w = ⟨_, hh⟩ := Subtype.ext (RingHom.ext hemb)
    have hτ : τ' = τ := (GlobalTheory.CMTypePlaces.places_bijective D).1 (by
      show InfinitePlace.mk ((tauE D τ').comp _) = InfinitePlace.mk ((tauE D τ).comp _)
      rw [h2, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding, hw])
    subst hτ
    exact ⟨w, fun y => by rw [hb]; exact GlobalTheory.ConjInfExp.piInf_eq W.θ W.θ_is _ w hh y, hV, hWW⟩
  have hmap : ∀ v : PtS G i j, v.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w)) = (compAt W.θ τ v).map conj :=
    fun v => Matrix.ext fun a b => hpi _
  have hX := hu w
  rw [hmap, hmap, hV, hWW] at hX
  have cW₁ := W.cart_is (.grid (i : ℕ) (j : ℕ)) ⟨by omega, by omega⟩ τ
  have cV₁ := W.cart_is (.grid ((i : ℕ) + 1) (j : ℕ)) ⟨by omega, by omega⟩ τ
  refine ⟨?_, ?_⟩
  · have hs : (-W.cart (.grid i j) τ)ᴴ * (-gramAt D (spW₁ G i j) τ) =
        (-gramAt D (spW₁ G i j) τ) * (-W.cart (.grid i j) τ) := by
      rw [Matrix.conjTranspose_neg, neg_mul_neg, neg_mul_neg]
      exact cartan_comm cW₁
    have := algV e _ _ _ _ _ _ hX hs
    simp only [neg_neg] at this
    rw [compAt_mapA W.θ W.θ_is, compAt_mapA W.θ W.θ_is]
    exact this
  · have := algW e _ _ _ _ _ _ hX (cartan_comm cV₁)
    rw [compAt_mapB W.θ W.θ_is, compAt_mapB W.θ W.θ_is, this]
    show _ = Complex.I • (_ * _ * _)
    simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg]

theorem isGauss : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G) (t : T) (i j : Fin D.R.m) (e : Num G i j) (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
    (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W), IsTripleOf W M t i j e Bs Γ X → IsTriple Bs Γ X om om' →
    ∀ (f₁ : GlobalTheory.SmallDat.HomA G t i j → ℂ) (f₂ : GlobalTheory.SmallDat.HomB G i j → ℂ), W.IsVac (.mu t i j) f₁ → W.IsVac (.chi i j) f₂ →
    ∀ (c : ℂ) (f₀ : SInf D.host.F (GlobalTheory.SmallDat.IxS G i j)),
      GlobalTheory.SmallDat.thetaS Γ W.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ Γ.M'.vac) = c • GlobalTheory.SmallDat.boxS t e f₁ f₂ → Γ.M'.IsGauss Bs.ψ Bs.emb f₀ := by
  intro D T L sc G W M t i j e Bs Γ X om om' h hT f₁ f₂ h₁ h₂ c f₀ hb
  obtain ⟨-, hinj, -⟩ := GlobalTheory.T.smallModel_thetaTransform_injective_products W M t i j e Bs Γ X om om' h hT
  have hG : Γ.M'.IsGood W.ψ := h.ψ ▸ hT.geo.hM'
  have hm := fun f => (isFinPart_vac hG ∅).fam.mem hG f
  rw [h.ψ]
  refine ⟨1, fun u u' _ _ hJ f f' hf hf' => pure_vac_inj hG (hinj _ (hm _) _ (hm _) (funext fun x => ?_))⟩
  have hc := cplx_pairS h u u' fun w => by simpa using hJ w
  obtain ⟨a, ha, ha'⟩ := GlobalTheory.T.fockVacuum_thetaFunction_derivative_complex_structure W.ψ W.θ _ _ _ _ f₁ W.ψ_std W.θ_is h₁.2.theta h₁.2.fock _ _ (fun τ => (hc τ).1)
    (mapA t e x)
  obtain ⟨b, hb₁, hb'⟩ := GlobalTheory.T.fockVacuum_thetaFunction_derivative_complex_structure W.ψ W.θ _ _ _ _ f₂ W.ψ_std W.θ_is h₂.2.theta h₂.2.fock _ _ (fun τ => (hc τ).2)
    (mapB e x)
  have hr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evI D.host.F) f₀ fun y : IxS G i j → AF D.host.F => finPartFn Γ.M'.vac fun k => (y k).2 := by
    refine ⟨fun y z hz => ?_, hm f₀⟩
    refine congrArg (finPartFn Γ.M'.vac) (funext fun k => ?_)
    have : (pairA D.host.F 0 1 * z k).2 = 0 :=
      congrArg (fun q => (q k).2) (hz (pairA D.host.F 0 1) (map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace _)))
    exact (add_eq_left (a := (y k).2)).2 ((one_mul (z k).2).symm.trans this)
  have key : ∀ u (g : SInf D.host.F (IxS G i j)), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (evI D.host.F) (Γ.M'.heisLine W.ψ u) f₀ g →
      HasDerivAt (fun s : ℝ => c * (heisO W.ψ _ _ (realAd D.host.F s • mapA t e u) f₁ (mapA t e x) *
        heisO W.ψ _ _ (realAd D.host.F s • mapB e u) f₂ (mapB e x))) (thetaS Γ W.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g Γ.M'.vac) x) 0 := by
    intro u g hg
    have := GlobalTheory.T.hasDerivAt_thetaTransform_heisenberg_real_line Γ.M'.co W.ψ inferInstance W.ψ_std.1 u _ (hm f₀) _ (hm g) (hg _ hr) x
    convert this using 2 with s
    refine Eq.trans ?_ (congrFun (thetaS_rho Γ W.ψ _ (realAd D.host.F s • u)) x).symm
    rw [hb, ← mapA_smul, ← mapB_smul]
    refine Eq.trans (congrArg (c * ·) (congrFun (heisS_box t e Γ h.JW₁ h.JWW W.ψ _ f₁ f₂) x).symm) ?_
    simp only [heisS, Pi.smul_apply, smul_eq_mul]
    ring
  have e1 := (key u f hf).unique ((ha.mul hb₁).const_mul c)
  have e2 := (key u' f' hf').unique ((ha'.mul hb').const_mul c)
  have e3 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Complex.I • f) Γ.M'.vac = Complex.I • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f Γ.M'.vac :=
    funext fun _ => mul_assoc _ _ _
  have e4 : realAd D.host.F 0 = 0 := by
    unfold realAd
    rw [map_zero (algebraMap ℝ _), map_zero (RingEquiv.symm _)]
    rfl
  have e5 : thetaS Γ W.ψ (Complex.I • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f Γ.M'.vac) x =
      Complex.I * thetaS Γ W.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f Γ.M'.vac) x := thetaS_smul _ _ _ _ _
  rw [e3, e5, e1, e2]
  simp only [e4, zero_smul]
  ring

end GlobalTheory.SmallGauss
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitVacuaProductEqGaussianDatumSmallModel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.SmallVac

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}

open GlobalTheory.SmallDat

theorem heisS_box_gen {t : T} {i j : ℕ} {e : Num G i j} {Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j}
    (hW₁ : Γ.V'.J = (-1 : D.host.E) • (spW₁ G i j).gram) (hWW : Γ.W.J = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram (spV G i j) (spV₁ G i j) e)
    {ψ : AddChar (AF D.host.F) ℂ} {f₁ : HomA G t i j → ℂ} {f₂ : HomB G i j → ℂ}
    (h₁ : IsLatVac (heisO ψ _ _) (latA G t i j) f₁) (h₂ : IsLatVac (heisO ψ _ _) (latB G i j) f₂) {v : Pl D.host.F}
    {γ : PtS G i j} (hγ : γ ∈ genPtS t e v) : heisS Γ ψ γ (boxS t e f₁ f₂) = boxS t e f₁ f₂ := by
  unfold IsLatVac at h₁ h₂
  rw [heisS_box t e Γ hW₁ hWW ψ γ f₁ f₂]
  rcases hγ with ⟨γ', hγ', rfl⟩ | ⟨hγl, ε, hε, hxA, hxB⟩
  · have hdA : mapA t e (2 • γ') = 2 • mapA t e γ' := by rw [two_nsmul, two_nsmul, mapA_add]
    have hdB : mapB e (2 • γ') = 2 • mapB e γ' := by rw [two_nsmul, two_nsmul, mapB_add]
    rw [hdA, hdB, h₁.1 _ hγ'.2.1, h₂.1 _ hγ'.2.2]
  · rw [h₁.2 ε hε _ hγl.2.1 hxA, h₂.2 ε hε _ hγl.2.2 hxB]

variable {W : G.Weil} {t : T} {i j : Fin D.R.m} {M : Vol G} {e : Num G i j} {Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E}
  {Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j} {X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E} {om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W} {om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W}

theorem exists_vacS (hL : L.Is μ₀) (h : IsTripleOf W M t i j e Bs Γ X) (hT : IsTriple Bs Γ X om om')
    (hti : GlobalTheory.FlipMatch.IsDoublyCompatible t i j e Bs Γ X) {f₁ : HomA G t i j → ℂ} {f₂ : HomB G i j → ℂ}
    (h₁ : W.IsVac (.mu t i j) f₁) (h₂ : W.IsVac (.chi i j) f₂) :
    ∃ f, thetaS Γ W.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f Γ.M'.vac) = boxS t e f₁ f₂ := by
  have hψ : Bs.ψ = W.ψ := h.ψ
  have hGood : Γ.M'.IsGood W.ψ := hψ ▸ hT.geo.hM'
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd W.ψ := hψ ▸ hT.base.std
  obtain ⟨-, hvac₁⟩ := h₁
  obtain ⟨-, hvac₂⟩ := h₂
  have hbox := GlobalTheory.SmallDat.ThBox.thetaS_box W M t i j e Bs Γ X om om' h hT
  obtain ⟨Φ, hΦ, hΦθ⟩ := hbox.2.2 f₁ f₂ hvac₁.theta hvac₂.theta
  have hfix : ∀ v, ∀ γ ∈ genPtS t e v, Γ.M'.co.rho W.ψ γ Φ = Φ := by
    intro v γ hγ
    refine hbox.2.1 _ (GlobalTheory.HeisSchA.rho_mem_schA Γ.M' W.ψ hstd γ Φ hΦ) _ hΦ ?_
    rw [thetaS_rho, hΦθ, heisS_box_gen h.JW₁ h.JWW hvac₁.lat hvac₂.lat hγ]
  have hsd := GlobalTheory.SmallDatLat.latPtS_le_closure_and_selfDual hL W t i j e Γ h.JW₁ h.JWW
  have hlat := GlobalTheory.SmallDat.latPtS_le_latAtV t i j e Bs Γ X hti
  obtain ⟨f, hf⟩ := GlobalTheory.PureGlue.eq_pure_of_slices Γ.M'.vac (fun v => (hGood.vac v).2.1) hGood.std Φ hΦ (by
    intro v y hy
    rcases isEmpty_or_nonempty (IxS G i j) with hκ | ⟨⟨k₀⟩⟩
    · refine ⟨(fun ξ : IxS G i j → _ => Φ (y + fun k => GlobalTheory.LatVac.liftV v (ξ k))) default / Γ.M'.vac v default, fun ξ => ?_⟩
      have hξ : ξ = default := Subsingleton.elim _ _
      subst hξ
      have hv0 : Γ.M'.vac v default ≠ 0 := by
        intro h0
        apply (hGood.vac v).2.1
        funext ξ'
        rw [Subsingleton.elim ξ' default]
        exact h0
      rw [div_mul_cancel₀ _ hv0]
    obtain ⟨c, hc0, hcb⟩ := GlobalTheory.LatBound.locCo_latAtV_bounded Γ.V' Γ.W v Γ.M'.co hT.geo.hV'.lat.toIsLattice hT.geo.hW.lat.toIsLattice
    have hsdl := GlobalTheory.LatVac.DualLoc.map_selfDual v Γ.M'.co W.ψ (latPtS t e v) (fun γ hγ => hγ.1) ((hsd v).2)
    have hcont : Continuous (GlobalTheory.LatVac.psiAt W.ψ v) := by
      show Continuous (fun x => W.ψ (GlobalTheory.LatVac.liftV v x))
      exact hstd.1.comp (continuous_const.prodMk (GlobalTheory.AdelicU.continuous_singleFin v))
    have hne1 : GlobalTheory.LatVac.psiAt W.ψ v ≠ 1 := by
      intro h1
      obtain ⟨π, hπ⟩ := IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer (K := D.host.F) v
      have hx : ((π⁻¹ : D.host.F) : v.adicCompletion D.host.F) ∉ v.adicCompletionIntegers D.host.F := by
        rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
          IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_inv₀, hπ]
        first
        | decide
        | simp
        | (intro hle; have := (inv_le_one₀ (by simp)).1 hle; simp at this)
      have hall := (hsdl ((fun _ => c⁻¹ * ((π⁻¹ : D.host.F) : v.adicCompletion D.host.F)), 0)).2
        (fun l _ => by rw [h1, AddChar.one_apply])
      obtain ⟨γ, hγ, hγe⟩ := AddSubgroup.mem_map.1 hall
      have h2 := (hcb γ (hlat v γ hγ) k₀).1
      rw [hγe] at h2
      have h3 : c * (c⁻¹ * ((π⁻¹ : D.host.F) : v.adicCompletion D.host.F)) ∈ v.adicCompletionIntegers D.host.F := h2
      rw [mul_inv_cancel_left₀ hc0] at h3
      exact hx h3
    obtain ⟨a, ha⟩ := GlobalTheory.SchrFixUniq.proportional_of_fixed v (GlobalTheory.LatVac.psiAt W.ψ v) hcont hne1
      (GlobalTheory.LatVac.locCo Γ.M'.co v '' genPtS t e v) ((latPtS t e v).map (GlobalTheory.LatVac.locCo Γ.M'.co v)) c
      ((AddSubgroup.map_mono ((hsd v).1)).trans (AddMonoidHom.map_closure _ _).le) hc0 hsdl
      (by
        intro l hl k
        obtain ⟨γ, hγ, rfl⟩ := AddSubgroup.mem_map.1 hl
        exact hcb γ (hlat v γ hγ) k)
      (Γ.M'.vac v) (fun ξ => Φ (y + fun k => GlobalTheory.LatVac.liftV v (ξ k)))
      (by
        rintro _ ⟨γ, hγ, rfl⟩
        exact GlobalTheory.BigDat.schr_eq_of_acts Γ.M'.co W.ψ (genPtS_subset t e v hγ).1 (hGood.vac v).1
          (GlobalTheory.SmallDat.VacFix.vac_fixed W M t i j e Bs Γ X om om' h hT v (hlat v) γ hγ))
      (by
        rintro _ ⟨γ, hγ, rfl⟩
        exact GlobalTheory.BigDat.schr_slice Γ.M'.co W.ψ (genPtS_subset t e v hγ).1 (hfix v γ hγ) hy)
      (hGood.vac v).2.1
    exact ⟨a, fun ξ => by simpa using congrFun ha ξ⟩)
  exact ⟨f, by rw [← hf, hΦθ]⟩

end GlobalTheory.SmallVac

namespace GlobalTheory.SmallVac

open GlobalTheory.SmallDat GlobalTheory.FlipMatch

theorem vac_datumB : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (M : Vol G) (hst : SquareStanding G t) (e : Num G i j) (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
    (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (h : IsTripleOf W M t i j e Bs Γ X), IsTriple Bs Γ X om om' → IsDoublyCompatible t i j e Bs Γ X →
    ∃ f₀, f₀ ≠ 0 ∧ Γ.M'.IsGauss Bs.ψ Bs.emb f₀ ∧
      IsDatumB (t := t) W e Γ (Finsupp.single (((), ρ.vT i j), ρ.vX i j) 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ Γ.M'.vac) := by
  intro D T L sc G μ₀ hL W ρ t i j M hst e Bs Γ X om om' h hT hti
  have h₁ : W.IsVac (.mu t i j) (ρ.vT i j) := ρ.vT_is t i j i.2.le j.2
  have h₂ : W.IsVac (.chi i j) (ρ.vX i j) := ρ.vX_is i j i.2 j.2.le
  obtain ⟨f, hf⟩ := exists_vacS hL h hT hti h₁ h₂
  have hGood : Γ.M'.IsGood Bs.ψ := hT.geo.hM'
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · rintro rfl
    obtain ⟨x₁, hx₁⟩ : ∃ x : HomA G t i j, ρ.vT i j x ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact GlobalTheory.BigDat.vac_ne_zero h₁ (funext hc)
    obtain ⟨x₂, hx₂⟩ : ∃ x : HomB G i j, ρ.vX i j x ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact GlobalTheory.BigDat.vac_ne_zero h₂ (funext hc)
    have h0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf _ _) Γ.M'.vac =
        (0 : ℂ) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf _ _) Γ.M'.vac := by
      funext x
      simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
    have hu := congrFun hf (ofMaps t e (x₁, x₂))
    rw [h0, thetaS_smul, zero_mul] at hu
    unfold boxS at hu
    rw [mapA_ofMaps, mapB_ofMaps] at hu
    exact mul_ne_zero hx₁ hx₂ hu.symm
  · exact GlobalTheory.SmallGauss.isGauss W M t i j e Bs Γ X om om' h hT _ _ h₁ h₂ 1 f (by rw [one_smul]; exact hf)
  · exact GlobalTheory.TensUniq.pure_mem_schA f _ (fun v => (hGood.vac v).1) hGood.std
  · intro u
    erw [Finsupp.sum_single_index, one_mul]
    · exact congrFun hf u
    · exact zero_mul _

end GlobalTheory.SmallVac
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitVacuaProductEqGaussianDatumSmallModelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitVacua_product_eq_gaussianDatum_smallModel : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (M : Vol G) (hst : SquareStanding G t) (e : Num G i j) (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
    (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (h : IsTripleOf W M t i j e Bs Γ X), IsTriple Bs Γ X om om' → IsDoublyCompatible t i j e Bs Γ X →
    ∃ f₀, f₀ ≠ 0 ∧ Γ.M'.IsGauss Bs.ψ Bs.emb f₀ ∧
      IsDatumB (t := t) W e Γ (Finsupp.single (((), ρ.vT i j), ρ.vX i j) 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ Γ.M'.vac) := by
  first | exact @GlobalTheory.SmallVac.vac_datumB | exact GlobalTheory.SmallVac.vac_datumB | (intros; apply GlobalTheory.SmallVac.vac_datumB <;> assumption)
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.FlipMatch

section Pair

variable {k k' A C A' C' : Type} [Fintype A] [Fintype C]

theorem pairM_comm [CommRing k] (X Y : Matrix A C k) : pairM X Y = pairM Y X := by
  simp only [pairM, mul_comm]

theorem pairM_add_left [CommRing k] (X X' Y : Matrix A C k) : pairM (X + X') Y = pairM X Y + pairM X' Y := by
  simp only [pairM, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

theorem pairM_smul_right [CommRing k] (c : k) (X Y : Matrix A C k) : pairM X (c • Y) = c * pairM X Y := by
  simp only [pairM, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_left_comm]

theorem pairM_eq_zero [CommRing k] {P : Finset C} {X Y : Matrix A C k} (hX : ∀ r, ∀ s ∈ P, X r s = 0)
    (hY : ∀ r, ∀ s ∉ P, Y r s = 0) : pairM X Y = 0 :=
  Finset.sum_eq_zero fun r _ => Finset.sum_eq_zero fun s _ => by
    by_cases h : s ∈ P
    · rw [hX r s h, zero_mul]
    · rw [hY r s h, mul_zero]

theorem pairM_eq_trace [CommRing k] (X Y : Matrix A C k) : pairM X Y = (X * Yᵀ).trace := by
  simp [pairM, trace, Matrix.mul_apply]

variable [Field k] [Field k'] [DecidableEq A] [DecidableEq C] [Fintype A'] [Fintype C'] (j : k ≃+* k') (eA : A ≃ A') (eC : C ≃ C')
  (g : GL A k') (h : GL C k')

theorem pairM_chart (X Y : Matrix A C k) :
    pairM (chart j eA eC g h X) (chart j eA eC (invT g) (invT h) Y) = j (pairM X Y) := by
  have e1 : ∀ M N : Matrix A C k', pairM (reindex eA eC M) (reindex eA eC N) = pairM M N := fun M N => by
    unfold pairM
    rw [← eA.sum_comp]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← eC.sum_comp]
    simp
  have e2 : j (pairM X Y) = pairM (X.map j) (Y.map j) := by simp [pairM]
  rw [chart, chart, e1, e2, pairM_eq_trace, pairM_eq_trace, invT_val, invT_val, transpose_mul, transpose_mul,
    transpose_transpose, transpose_transpose, Matrix.mul_assoc (g.val * _), ← Matrix.mul_assoc h.val, Units.mul_inv,
    Matrix.one_mul, ← Matrix.mul_assoc, trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]

omit [Fintype A'] [Fintype C'] in
theorem chart_add (X Y : Matrix A C k) : chart j eA eC g h (X + Y) = chart j eA eC g h X + chart j eA eC g h Y := by
  rw [chart, chart, chart, Matrix.map_add _ (map_add j), Matrix.mul_add, Matrix.add_mul]
  rfl


omit [Fintype A'] [Fintype C'] in
theorem exists_homeo [TopologicalSpace k] [TopologicalSpace k'] [IsTopologicalRing k'] (h1 : Continuous j) (h2 : Continuous j.symm) :
    ∃ Θ : Matrix A C k ≃ₜ Matrix A' C' k', ∀ X, Θ X = chart j eA eC g h X :=
  ⟨{ toFun := chart j eA eC g h
     invFun := fun Z => ((g⁻¹).val * Z.submatrix eA eC * (h⁻¹).val).map j.symm
     left_inv := fun X => by
      simp only [chart, reindex_apply, submatrix_submatrix, Equiv.symm_comp_self, submatrix_id_id]
      rw [Matrix.mul_assoc g.val, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
      ext; simp
     right_inv := fun Z => by
      have : ∀ M : Matrix A C k', (M.map j.symm).map j = M := fun M => by ext; simp
      simp only [chart, this]
      rw [Matrix.mul_assoc (g⁻¹).val, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
      simp
     continuous_toFun := ((continuous_const.matrix_mul (continuous_id.matrix_map h1)).matrix_mul continuous_const).matrix_reindex _ _
     continuous_invFun := ((continuous_const.matrix_mul (continuous_id.matrix_submatrix _ _)).matrix_mul
        continuous_const).matrix_map h2 }, fun _ => rfl⟩

end Pair

theorem bijOn_funLeft {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (Θ : X ≃ₜ Y) :
    Set.BijOn (LinearMap.funLeft ℂ ℂ Θ.symm) (GlobalTheory.WeilM.SB X : Set _) (GlobalTheory.WeilM.SB Y : Set _) := by
  have key : ∀ {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (Θ : X ≃ₜ Y), ∀ f ∈ GlobalTheory.WeilM.SB Y, f ∘ Θ ∈ GlobalTheory.WeilM.SB X :=
    fun Θ f hf => ⟨hf.1.comp_continuous Θ.continuous, hf.2.comp_homeomorph Θ⟩
  refine ⟨fun f hf => key Θ.symm f hf, fun f _ f' _ e => funext fun x => ?_, fun f hf => ⟨f ∘ Θ, key Θ f hf, ?_⟩⟩
  · simpa [LinearMap.funLeft_apply] using congrFun e (Θ x)
  · funext y; simp [LinearMap.funLeft_apply]

section Mix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {Y : Spc F E d} {M : Model σ X Y} {ψ : AddChar (AF F) ℂ} {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)}

theorem isLagrModel_smul {A A' : Set (Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))} {Z : Type} [TopologicalSpace Z] [Add Z]
    {co : _ → Z} {ι} (h : IsLagrModel M ψ v A A' co ι) {c : ℂ} (hc : c ≠ 0) : IsLagrModel M ψ v A A' co (c • ι) := by
  refine ⟨⟨fun f hf => Submodule.smul_mem _ c (h.1.1 hf), fun f hf f' hf' e => h.1.2.1 hf hf' (smul_right_injective _ hc e),
    fun f hf => ?_⟩, fun u hu φ hφ φ₁ h₁ ha z => ?_, fun u hu φ hφ φ₁ h₁ ha x hx => ?_⟩
  · obtain ⟨φ, hφ, e⟩ := h.1.2.2 (Submodule.smul_mem _ c⁻¹ hf)
    exact ⟨φ, hφ, by rw [LinearMap.smul_apply, e, smul_smul, mul_inv_cancel₀ hc, one_smul]⟩
  · simp only [LinearMap.smul_apply, Pi.smul_apply, h.2.1 u hu φ hφ φ₁ h₁ ha z]
  · simp only [LinearMap.smul_apply, Pi.smul_apply, h.2.2 u hu φ hφ φ₁ h₁ ha x hx, smul_eq_mul]
    ring

theorem exists_mixed {k R C : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Fintype R] [DecidableEq R] [Fintype C] [DecidableEq C] {ψ₀ : AddChar k Circle} {ϖ : kˣ} (hϖ : IsUnif ϖ)
    (hψ : HasConductor ψ₀ 1) {j : Fv F v ≃+* k} (hj : IsLocIso j) {κ : k} (hκ : κ ≠ 0) {χ : Fv F v → ℂ}
    (hχ : ∀ x, χ x = ψ₀ (κ * j x)) {eA : Fin n ≃ R} {eC : Fin d ≃ C} {g h} {P : Finset C} {A A' co}
    {a b : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → Matrix (Fin n) (Fin d) (Fv F v)}
    (hc : IsMixChart v A A' co (fun u => chart j eA eC g h (a u)) (fun u => κ • chart j eA eC (invT g) (invT h) (b u)) P)
    {ι₀ : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F v) → ℂ)}
    (hb : Set.BijOn ι₀ (GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v) : Set _) (GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) (Fv F v)) : Set _))
    (ha : ∀ u, At (evFin F v) u → pairM (a u) (b u) = 0 → ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ₁ ∈ GlobalTheory.WeilM.SB _,
      Acts (evFin F v) (M.co.rho ψ u) φ φ₁ → ∀ Z, ι₀ φ₁ Z = χ (pairM Z (b u)) * ι₀ φ (Z + a u))
    (hs : ∀ x u, At (evFin F v) x → At (evFin F v) u →
      ψ (GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) x u) =
        χ (pairM (a x) (b u) - pairM (b x) (a u))) :
    ∃ ι, IsLagrModel M ψ v A A' co ι ∧ ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ m, IsNatDatum ϖ m (ι φ) →
      ι₀ φ = fun Z => fourierSum ψ₀⁻¹ ϖ m P (ι φ) (chart j eA eC g h Z) := by
  obtain ⟨𝓕, f1, f2, f3, f4⟩ := GlobalTheory.T.exists_partialFourier_columnBlock_schwartzBruhat k R C ψ₀ ϖ P hϖ hψ
  obtain ⟨Θ, hΘ⟩ := exists_homeo j eA eC g h hj.1 hj.2.1
  let ι₁ := LinearMap.funLeft ℂ ℂ Θ.symm ∘ₗ ι₀
  have b1 : Set.BijOn ι₁ (GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v) : Set _) (GlobalTheory.WeilM.SB (Matrix R C k) : Set _) := (bijOn_funLeft Θ).comp hb
  have e1 : ∀ φ Z, ι₁ φ (chart j eA eC g h Z) = ι₀ φ Z := fun φ Z => by
    rw [← hΘ]; exact congrArg (ι₀ φ) (Θ.symm_apply_apply Z)
  have pc : ∀ Z Z', pairM (chart j eA eC g h Z) (κ • chart j eA eC (invT g) (invT h) Z') = κ * j (pairM Z Z') := fun Z Z' => by
    rw [pairM_smul_right, pairM_chart]
  have act : ∀ u, At (evFin F v) u → pairM (chart j eA eC g h (a u)) (κ • chart j eA eC (invT g) (invT h) (b u)) = 0 →
      ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ₁ ∈ GlobalTheory.WeilM.SB _, Acts (evFin F v) (M.co.rho ψ u) φ φ₁ →
      ι₁ φ₁ = fun S => (ψ₀ (pairM S (κ • chart j eA eC (invT g) (invT h) (b u))) : ℂ) * ι₁ φ (S + chart j eA eC g h (a u)) := by
    intro u hu h0 φ hφ φ₁ h₁ hact
    funext S
    obtain ⟨Z, rfl⟩ := Θ.surjective S
    rw [pc, mul_eq_zero, map_eq_zero] at h0
    rw [hΘ, ← chart_add, e1, e1, pc, ← hχ]
    exact ha u hu (h0.resolve_left hκ) φ hφ φ₁ h₁ hact Z
  refine ⟨𝓕 ∘ₗ ι₁, ⟨f1.comp b1, fun u hu φ hφ φ₁ h₁ hact z => ?_, fun u hu φ hφ φ₁ h₁ hact x hx => ?_⟩, fun φ hφ m hm => ?_⟩
  · obtain ⟨c1, c2, c3, c4⟩ := hc.1 u hu
    rw [LinearMap.comp_apply, act u c1 (pairM_eq_zero c2 c3) φ hφ φ₁ h₁ hact, f2 _ (b1.1 hφ) _ _ c2 c3, c4]
    rfl
  · obtain ⟨c1, c2, c3⟩ := hc.2 u hu
    obtain ⟨d1, d2, d3, d4⟩ := hc.1 x hx
    rw [LinearMap.comp_apply, act u c1 ((pairM_comm _ _).trans (pairM_eq_zero c3 c2)) φ hφ φ₁ h₁ hact, f3 _ (b1.1 hφ) _ _ c2 c3,
      hs x u d1 c1, hχ, map_sub, mul_sub, ← pc, pairM_comm (b x), ← pc, d4]
    beta_reduce
    rw [pairM_add_left, pairM_add_left, pairM_eq_zero d2 c2, pairM_comm (κ • _) (κ • _), pairM_eq_zero c3 d3, add_zero, zero_add,
      pairM_comm _ (κ • chart j eA eC (invT g) (invT h) (b x))]
    rfl
  · funext Z
    rw [LinearMap.comp_apply, f4 _ (b1.1 hφ) m hm, e1]

theorem isGauss_smul {τ} {f₀ : SInf F (Fin n × Fin d)} (h : M.IsGauss ψ τ f₀) {s : ℂ} (hs : s ≠ 0) : M.IsGauss ψ τ (s • f₀) := by
  obtain ⟨ε, h⟩ := h
  have key : ∀ u (f : SInf F (Fin n × Fin d)), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (M.heisLine ψ u) (s • f₀ : SInf F _) f →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (M.heisLine ψ u) f₀ (s⁻¹ • f : SInf F _) := fun u f hf r hr x => by
    have e : ∀ (c : ℂ) (g : SInf F (Fin n × Fin d)), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (c • g : SInf F _) r =
        c • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) g r := fun c g => funext fun y => mul_assoc _ _ _
    have := (hf r ⟨hr.1, by rw [e]; exact Submodule.smul_mem _ _ hr.2⟩ x).const_mul s⁻¹
    have e' : ∀ y Φ, M.heisLine ψ u y (s • Φ) x = s * M.heisLine ψ u y Φ x := fun y Φ => mul_left_comm _ _ _
    simp only [e, e', inv_mul_cancel_left₀ hs] at this
    rw [e]
    exact this
  refine ⟨ε, fun u u' hu hu' e f f' hf hf' => ?_⟩
  have := h u u' hu hu' e _ _ (key u f hf) (key u' f' hf')
  rw [smul_comm] at this
  exact smul_right_injective _ (inv_ne_zero hs) this

end Mix

theorem mem_SB_of_isNatDatum {k A C : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Fintype A] [Fintype C] {ϖ : kˣ} {n : ℕ} {Φ : Matrix A C k → ℂ} (h : IsNatDatum ϖ n Φ) : Φ ∈ GlobalTheory.WeilM.SB (Matrix A C k) := by
  have h0 : 0 < ValuativeRel.valuation k ((ϖ ^ n : kˣ) : k) := zero_lt_iff.2 (by simp)
  refine ⟨(IsLocallyConstant.iff_exists_open Φ).2 fun x =>
      ⟨{x' | ∀ r s, (x' - x) r s / ((ϖ ^ n : kˣ) : k) ∈ (ValuativeRel.valuation k).integer}, ?_, fun r s => by simp,
      fun x' hx' => ?_⟩,
    HasCompactSupport.intro (GlobalTheory.SplitFlip.isCompact_intMatrix (k := k) (m := A) (n := C))
      fun x hx => h.1 x fun hm => hx (mem_matLat_stdLat.1 hm)⟩
  · simp only [Set.ofPred_forall]
    refine isOpen_iInter_of_finite fun r => isOpen_iInter_of_finite fun s => ?_
    exact IsOpen.preimage (f := fun x' : Matrix A C k => (x' - x) r s / ((ϖ ^ n : kˣ) : k)) (by fun_prop) Valuation.isOpen_integer
  · rw [← h.2 x (x' - x), add_sub_cancel]
    classical
    rw [GlobalTheory.SplitFlip.stdLat, smul_diagLat]
    simp only [Pi.one_apply, mul_one]
    change ∀ r s, ValuativeRel.valuation k ((x' - x) r s) ≤
      ValuativeRel.valuation k ((ϖ ^ n : kˣ) : k)
    intro r s
    have := hx' r s
    rwa [Valuation.mem_integer_iff, map_div₀, div_le_one₀ h0] at this

section Grid

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}

theorem det_skewGram_ne (A B : HSp D) {d : ℕ} (e : Fin A.rank ⊕ Fin B.rank ≃ Fin d) : (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram A B e).det ≠ 0 := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram, det_smul, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk, det_reindex_self, det_fromBlocks_zero₂₁, det_transpose, det_transpose]
  exact mul_ne_zero (pow_ne_zero _ GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero)
    (mul_ne_zero (GlobalTheory.RouteCoords.gram_det_ne A) (GlobalTheory.RouteCoords.gram_det_ne B))


set_option maxHeartbeats 1000000 in
theorem local_match (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) (t : T) (i j : Fin D.R.m) (M : Vol G) (hst : SquareStanding G t)
    {e : Num G i j} {Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E} {Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j} {X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E}
    {om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W} {om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W} (h : IsTripleOf W M t i j e Bs Γ X) {R Rf}
    (hm : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ X om om' R Rf) (hti : IsTied t i j e Bs Γ X) {w : Pl D.host.E} (hw : w ∈ locPl G t)
    {v : Pl D.host.F} (hv : w.under (𝓞 D.host.F) = v) :
    ∃ ι ι', IsLagrModel Γ.M W.ψ v (mixHalf e (atPl w 1)) (mixHalf e (cA D (atPl w 1))) (mixCo B t e w) ι ∧
      IsLagrModel Γ.M' W.ψ v (mixHalfS e (atPl w 1)) (mixHalfS e (cA D (atPl w 1))) (mixCoS B t e w) ι' ∧
      ∀ n Φ, depthAt G w ≤ n → IsNatDatum (unifAt w) n Φ → ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ' ∈ GlobalTheory.WeilM.SB _,
        ι φ = flipAt W t i j w n Φ → ι' φ' = Φ → Rf.p v φ = Rf.p' v φ' := by
  classical
  letI := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv v
  haveI := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv v
  have hT := hm.triple
  have hvT : v ∈ X.T := (hti.2.2.1 v).2 ⟨w, hw, hv⟩
  let v' : Bs.P := ⟨v, hT.chars.sub hvT⟩
  have hτ : splitPrime (Bs.τ v') = w := hti.2.2.2 v' w hw hv
  obtain ⟨ιA, ιB, hA, hB, -, -, hz⟩ := hm.fin.zeta v' hvT
  obtain ⟨jj, j1, j2, j3, j4⟩ := GlobalTheory.T.exists_placeIso_reading_components_characters hL W t i j X h.α h.β (Bs.τ v') w hτ
  let C0 : GL (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (Kw w) :=
    ⟨basCols B e w, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e (loc w (B.β i (j + 1)))⁻¹.val (-(loc w (B.β (i + 1) j))⁻¹.val),
      by rw [basCols, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk_mul, neg_mul_neg, Units.mul_inv, Units.mul_inv, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk_one],
      by rw [basCols, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk_mul, neg_mul_neg, Units.inv_mul, Units.inv_mul, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk_one]⟩
  let cj := GeneralLinearGroup.map (jj : Fv D.host.F v →+* Kw w) (Γ.W.bas v)
  have hcc : (Γ.W.bas v).val.map jj * (cj⁻¹ * C0).val = basCols B e w := congrArg Units.val (mul_inv_cancel_left cj C0)
  generalize cj⁻¹ * C0 = cc at hcc
  obtain ⟨g, hg, cA⟩ := GlobalTheory.T.exists_mixedLagrangian_chart_integral_rowChange hL W B t i j M e Bs Γ X om om' h hT hti v' w hτ jj j1 j2 cc hcc
  obtain ⟨g', cB⟩ := GlobalTheory.T.mixedLagrangian_oppositeLagrangian_chart hL W B t i j M e Bs Γ X h v' w hτ jj j1 cc hcc
  have hb : ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := fun hmem => hst.2 w hw (by
    have e : ((D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) =
        (D.host.d : 𝓞 D.host.E) * ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) := by push_cast; ring
    rw [e]; exact Ideal.mul_mem_left _ _ hmem)
  have hS := (Good.isGood_of_notMem hL W hw hb).square i i.2 j j.2
  have hξ : (xiAt w)⁻¹ ≠ 0 := inv_ne_zero ((_root_.map_ne_zero _).2 GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero)
  have dW : Γ.W.J.det ≠ 0 := h.JWW ▸ det_skewGram_ne _ _ e
  have dV : Γ.V.J.det ≠ 0 := by rw [h.JW, one_smul]; exact GlobalTheory.RouteCoords.gram_det_ne _
  have dV' : Γ.V'.J.det ≠ 0 := by
    rw [h.JW₁, det_smul]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) (GlobalTheory.RouteCoords.gram_det_ne _)
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd W.ψ := h.ψ ▸ hT.base.std
  rw [h.ψ] at hA hB
  obtain ⟨ι, i1, i2⟩ := exists_mixed (M := Γ.M) (ψ := W.ψ) hS.unif hS.cond j2 hξ j4 (h := invT cc) cA hA.bij
    (fun u hu h0 φ hφ φ₁ h₁ ha => (GlobalTheory.T.heisenbergOperator_isotropic_translation_char_split hT.base.cm Γ.V Γ.W hT.geo.hV.herm hT.geo.hW.skew dV dW Γ.M W.ψ hstd _ _ _ u hu h0
      φ hφ φ₁ h₁ ha).1 ιA hA)
    fun x u hx hu => GlobalTheory.T.tensorSymplecticForm_at_split_finite_place hT.base.cm Γ.V Γ.W hT.geo.hV.herm hT.geo.hW.skew W.ψ _ _ _ x u hx hu
  obtain ⟨ι', k1, k2⟩ := exists_mixed (M := Γ.M') (ψ := W.ψ) hS.unif hS.inv.cond j2 hξ (χ := fun x => psiLoc W.ψ v (-x))
    (fun x => by rw [j4, AddChar.inv_apply, map_neg, mul_neg]) cB hB.bij
    (fun u hu h0 φ hφ φ₁ h₁ ha => (GlobalTheory.T.heisenbergOperator_isotropic_translation_char_split hT.base.cm Γ.V' Γ.W hT.geo.hV'.herm hT.geo.hW.skew dV' dW Γ.M' W.ψ hstd _ _ _ u hu
      ((pairM_comm _ _).trans h0) φ hφ φ₁ h₁ ha).2 ιB hB)
    fun x u hx hu => by
      rw [GlobalTheory.T.tensorSymplecticForm_at_split_finite_place hT.base.cm Γ.V' Γ.W hT.geo.hV'.herm hT.geo.hW.skew W.ψ (Bs.τ v') (Γ.V'.bas v) (Γ.W.bas v) x u hx hu, neg_sub]
  have h1 := GivenAdm.givenLevel_open hL hw ((i : ℕ), (j : ℕ))
  have h2 := isOpen_map_invT h1.1 h1.2
  haveI hμ := isHaarMeasure_haarVol h2.1 h2.2
  haveI := isHaarMeasure_haarVol (k := Kw w) (n := Fin (spW₁ G i j).rank) isOpen_KO le_rfl
  haveI := isHaarMeasure_haarVol (k := Fv D.host.F v) (n := Fin (spW₁ G i j).rank) isOpen_KO le_rfl
  haveI : @MeasureTheory.Measure.IsHaarMeasure (GL (Fin (spW₁ G i j).rank) (Kw w)) _ _
      (@Units.instMeasurableSpace (Matrix (Fin (spW₁ G i j).rank) (Fin (spW₁ G i j).rank) (Kw w)) _
        GroundTheory.Automorphic.GJMatrix.measurableSpace_matrix)
      (haarVol (KO (Kw w) (Fin (spW₁ G i j).rank))) :=
    isHaarMeasure_haarVol (k := Kw w) (n := Fin (spW₁ G i j).rank) isOpen_KO le_rfl
  haveI : @MeasureTheory.Measure.IsHaarMeasure (GL (Fin ((locGrid G t w).rank ((i : ℕ), (j : ℕ)))) (Kw w)) _ _
      (@Units.instMeasurableSpace (Matrix (Fin ((locGrid G t w).rank ((i : ℕ), (j : ℕ)))) (Fin ((locGrid G t w).rank ((i : ℕ), (j : ℕ)))) (Kw w)) _
        GroundTheory.Automorphic.GJMatrix.measurableSpace_matrix)
      (haarVol ((givenLevel G t w ((i : ℕ), (j : ℕ))).map invT)) :=
    hμ
  obtain ⟨l₂, hl₂, z₂⟩ := GlobalTheory.T.zetaIdentity_persists_row_column_changes (Kw w) _ _ (rankW G t i j w) _ _ _ _ (finCongr (rankW₁ G t i j w)) (colsEq t e w) finSumFinEquiv
    (stdSplit ((locGrid G t w).rank_square i j)) (haarVol (KO (Kw w) _)) (haarVol ((givenLevel G t w (i, j)).map invT))
    (unifAt w) ((locGrid G t w).nu i j) 1 g g' cc hg
  obtain ⟨l₁, hl₁, z₁⟩ := GlobalTheory.T.zetaIdentity_transport_localFieldIso (Fv D.host.F v) (Kw w) jj j2 (spW G i j).rank (Fin (spW₁ G i j).rank) _ finSumFinEquiv
    (haarVol (KO _ _)) (haarVol (KO _ _)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) (unifAt w) (exists_isUnif (k := Fv D.host.F v)).choose_spec
    hS.unif (chrW X.ν (Bs.τ v')) (chrW X.β (Bs.τ v')) _ 1 j3
  refine ⟨ι, (l₁ * l₂)⁻¹ • ι', i1, isLagrModel_smul k1 (inv_ne_zero (mul_ne_zero hl₁ hl₂)), fun n Φ hn hΦ φ hφ φ' hφ' e1 e2 => ?_⟩
  have e3 : ι' ((l₁ * l₂)⁻¹ • φ') = Φ := by rw [map_smul]; exact e2
  have e4 := k2 _ (Submodule.smul_mem _ _ hφ') n (e3 ▸ hΦ)
  rw [e3, map_smul, inv_inv] at e4
  have e5 := i2 φ hφ n (e1 ▸ LocTensor.isNatDatum_flipAt hL W i j hw hb hn hΦ)
  rw [e1, flipAt, squareFlip, GlobalTheory.T.partialFourierSum_inverse_of_latticeDepth _ _ _ _ _ _ _ hS.unif hS.inv.cond _ (by
    rw [← latA_blockLat, ← Grid.alpha_div_beta]
    exact GlobalTheory.FrameDepth.hasDepth_phiA _ _ _ _ _ (hμ := hμ) _ _ _ _ _ _ hS.unif (hS.one_le.trans hn) (LocTensor.condLE_mono hS.unif hn hS.condν)
      (GlobalTheory.SplitFlip.FourierDepth.hasDepth_fourierSum hS.unif hS.cond n _ hΦ))] at e5
  have e6 : chrW X.α (Bs.τ v') = chrW X.ν (Bs.τ v') * chrW X.β (Bs.τ v') := by
    ext x
    simp [chrW, GlobalTheory.LFun.locChar, Chars.ν]
  refine (hz φ hφ φ' hφ').2 ?_
  rw [e5, e6]
  refine (z₁ _ _ (z₂ _ _ (GlobalTheory.T.primitiveFrameDatum_zetaIntegral_eq_smaller (Kw w) _ _ _ _ _ _ 1 _ n _ _ hS.unif))).trans ?_
  congr 1
  funext Y
  have := congrFun e4 Y
  rw [Pi.smul_apply, smul_eq_mul, inv_mul_eq_iff_eq_mul₀ (mul_ne_zero hl₁ hl₂)] at this
  rw [this, mul_assoc]
  rfl

end Grid

section Global

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}

theorem exists_tiedBoth (hL : L.Is μ₀) (W : G.Weil) (t : T) (i j : Fin D.R.m) (hst : SquareStanding G t) (M : Vol G) (hM : M.Is t) :
    ∃ (e : Num G i j) (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
      (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W),
      IsTripleOf W M t i j e Bs Γ X ∧ IsTriple Bs Γ X om om' ∧ IsDoublyCompatible t i j e Bs Γ X := by
  classical
  obtain ⟨e, Bs, Γ, X, om, om', h, hT, hti⟩ := GlobalTheory.T.exists_thetaTripleOfSquareGrid_latticeCompatible hL W t i j hst M hM
  have hsd := (node_isV G hL (X := .grid i j) ⟨i.2.le, j.2.le⟩).sd
  haveI hlat := GlobalTheory.TripleSpaceW.conjSub_isFullLattice
    (GlobalTheory.FunObj.selfDual_isFullLattice _ _ hsd)
  let bas := fun v : Bs.P => Classical.choose
    (exists_isSplitBasis (Bs.τ v) (GlobalTheory.TripleSpaceW.conjSub (G.Λ (.grid i j))) (isCMExt_host D))
  have hbas := fun v : Bs.P => Classical.choose_spec
    (exists_isSplitBasis (Bs.τ v) (GlobalTheory.TripleSpaceW.conjSub (G.Λ (.grid i j))) (isCMExt_host D))
  let V' : Spc D.host.F D.host.E (spW₁ G i j).rank :=
    ⟨Γ.V'.J, GlobalTheory.TripleSpaceW.conjSub (G.Λ (.grid i j)), Γ.V'.θ, fun v => if h : v ∈ Bs.P then bas ⟨v, h⟩ else 1⟩
  have hV' : V'.IsHerm D.sp.cm.sig Bs Γ.q ((spW₁ G i j).rank - Γ.q) :=
    ⟨hT.geo.hV'.herm, hT.geo.hV'.sig, hlat, fun y => by
      have := GlobalTheory.TripleSpace.mem_starLat_iff_form (spW₁ G i j) hsd y
      rw [← h.JW₁] at this
      simp only [Formalism.L2.Col.mem_starLat] at this
      exact this,
    hT.geo.hV'.cartan, fun v => by
      show IsSplitBasis _ _ (if h : v.1 ∈ Bs.P then bas ⟨v.1, h⟩ else 1)
      rw [dite_eq_left v.2]
      exact hbas v⟩
  obtain ⟨co, vac, dom, hMo⟩ := GlobalTheory.T.squareModel_negSpace_goodSchroedinger hL t i j M hM Bs hT.base V' Γ.W h.JW₁ _ _ _ _ hV' hT.geo.hW
  obtain ⟨om₁, hom⟩ := GlobalTheory.T.exists_weilRep_squarePair_characters_alpha_quotient hL t i j hst Bs hT.base V' Γ.W _ _ _ _ hV' hT.geo.hW _ hMo
  refine ⟨e, Bs, ⟨Γ.p, Γ.q, Γ.V, V', Γ.W, Γ.M, _⟩, X, om, om₁,
    ⟨h.ψ, h.JW, h.JW₁, h.JWW, h.cart, h.α, h.β, h.μW, rfl⟩,
    ⟨hT.base, ⟨hT.geo.lt, hT.geo.even, hT.geo.kappa, hT.geo.eBig, hT.geo.aBig, hT.geo.hV, hV', hT.geo.hW, hT.geo.hM, hMo⟩,
      hT.chars, hT.weil, ?_⟩, hti, rfl⟩
  rw [h.α, h.β]
  exact hom

theorem exists_finPart {n d : ℕ} {X : Spc D.host.F D.host.E n} {Y : Spc D.host.F D.host.E d} {M : Model D.sp.cm.sig X Y} {ψ}
    (hM : M.IsGood ψ) {S : Finset (Pl D.host.E)} {S' : Finset (Pl D.host.F)}
    (h1 : ∀ v, v ∈ S' ↔ ∃ w ∈ S, w.under (𝓞 D.host.F) = v)
    (h2 : ∀ w ∈ S, ∀ w' ∈ S, w.under (𝓞 D.host.F) = w'.under (𝓞 D.host.F) → w = w')
    (P : ∀ w : Pl D.host.E, ((Fin n × Fin d → Fv D.host.F (w.under (𝓞 D.host.F))) → ℂ) → Prop)
    (hP : ∀ w ∈ S, ∃ φ ∈ GlobalTheory.WeilM.SB _, P w φ) : ∃ φ, IsFinPart M S' φ ∧ ∀ w ∈ S, P w (φ (w.under (𝓞 D.host.F))) := by
  have H : ∀ v, ∃ φ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv D.host.F v), (v ∉ S' → φ = M.vac v) ∧
      ∀ w ∈ S, ∀ e : w.under (𝓞 D.host.F) = v, P w (e ▸ φ) := fun v => by
    by_cases hv : v ∈ S'
    · obtain ⟨w, hw, rfl⟩ := (h1 v).1 hv
      obtain ⟨φ, a, b⟩ := hP w hw
      refine ⟨φ, a, fun h => absurd hv h, fun w' hw' e => ?_⟩
      obtain rfl := h2 w' hw' w hw e
      exact b
    · exact ⟨M.vac v, (hM.vac v).1, fun _ => rfl, fun w hw e => absurd ((h1 v).2 ⟨w, hw, e⟩) hv⟩
  choose φ a b c using H
  exact ⟨φ, ⟨a, b⟩, fun w hw => c _ w hw rfl⟩

theorem finite_match (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (M : Vol G)
    (hst : SquareStanding G t) {e : Num G i j} {Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E} {Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j}
    {X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E} {om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W} {om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W}
    (h : IsTripleOf W M t i j e Bs Γ X) {R Rf} (hm : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ X om om' R Rf)
    (hti : IsDoublyCompatible t i j e Bs Γ X) :
    ∃ f₀ f₀', (f₀ ≠ 0 ∧ Γ.M.IsGauss Bs.ψ Bs.emb f₀) ∧ (f₀' ≠ 0 ∧ Γ.M'.IsGauss Bs.ψ Bs.emb f₀') ∧
      ∀ n Φ τ τ', (∀ w ∈ locPl G t, depthAt G w ≤ n w ∧ IsNatDatum (unifAt w) (n w) (Φ w)) → HasFlip B t ρ i j n Φ τ τ' →
        ∃ φ φ', IsFinPart Γ.M X.T φ ∧ IsFinPart Γ.M' X.T φ' ∧ IsDatumA W e Γ τ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ φ) ∧
          IsDatumB W e Γ τ' (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀' φ') ∧ ∀ v, Rf.p v (φ v) = Rf.p' v (φ' v) := by
  have hT := hm.triple
  have H := fun (w : Pl D.host.E) (hw : w ∈ locPl G t) => local_match hL W B t i j M hst h hm hti.1 hw rfl
  choose! ι ι' h1 h2 h3 using H
  obtain ⟨f, f1, f2, f3⟩ := GlobalTheory.T.exists_gaussianVacuum_product_unitVacua hL W ρ t i j M hst e Bs Γ X om om' h hT hti.1
  obtain ⟨f', g1, g2, g3⟩ := GlobalTheory.T.unitVacua_product_eq_gaussianDatum_smallModel hL W ρ t i j M hst e Bs Γ X om om' h hT hti
  obtain ⟨s, hs, a⟩ := GlobalTheory.T.finiteDatum_localFunctions_eq_pureTensor_scalar hL W B ρ t i j M hst e Bs Γ X om om' h hT hti.1 f f3 ι h1
  obtain ⟨s', hs', b⟩ := GlobalTheory.T.exists_scalar_finiteTensor_eq_datum_smallModel hL W B ρ t i j M hst e Bs Γ X om om' h hT hti f' g3 ι' h2
  refine ⟨s • f, s' • f', ⟨smul_ne_zero hs f1, isGauss_smul f2 hs⟩, ⟨smul_ne_zero hs' g1, isGauss_smul g2 hs'⟩, ?_⟩
  rintro n Φ τ τ' hn ⟨ε, hε, c, d⟩
  have hf : ∀ w ∈ locPl G t, IsNatDatum (unifAt w) (n w) (flipAt W t i j w (n w) (Φ w)) := fun w hw =>
    LocTensor.isNatDatum_flipAt hL W i j hw (fun hmem => hst.2 w hw (by
      have e : ((D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) =
          (D.host.d : 𝓞 D.host.E) * ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) := by push_cast; ring
      rw [e]; exact Ideal.mul_mem_left _ _ hmem)) (hn w hw).1 (hn w hw).2
  have hinj : ∀ w ∈ locPl G t, ∀ w' ∈ locPl G t, w.under (𝓞 D.host.F) = w'.under (𝓞 D.host.F) → w = w' :=
    fun w hw w' hw' e => Good.under_injOn hL G t hw hw' e
  obtain ⟨φ, p1, p2⟩ := exists_finPart hT.geo.hM hti.1.2.2.1 hinj (fun w φ => ι w φ = flipAt W t i j w (n w) (Φ w))
    fun w hw => (h1 w hw).1.2.2 (mem_SB_of_isNatDatum (hf w hw))
  obtain ⟨φ', q1, q2⟩ := exists_finPart hT.geo.hM' hti.1.2.2.1 hinj (fun w φ => ι' w φ = Φ w)
    fun w hw => (h2 w hw).1.2.2 (mem_SB_of_isNatDatum (hn w hw).2)
  refine ⟨φ, φ', p1, q1, a ε hε n _ τ hf d φ p1 p2, b ε hε n _ τ' (fun w hw => (hn w hw).2) c φ' q1 q2, fun v => ?_⟩
  by_cases hv : v ∈ X.T
  · obtain ⟨w, hw, rfl⟩ := (hti.1.2.2.1 v).1 hv
    exact h3 w hw _ _ (hn w hw).1 (hn w hw).2 _ (p1.1 _) _ (q1.1 _) (p2 w hw) (q2 w hw)
  · rw [p1.2 v hv, q1.2 v hv, (hm.fin.sph v hv).1]

theorem polMatch_pure {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    {Bs : Base F E} {Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a'} {X : Chars F E} {R Rf} {f f' φ φ'} (hf : f ∈ Γ.M.Pol Bs.ψ Bs.emb)
    (hf' : f' ∈ Γ.M'.Pol Bs.ψ Bs.emb) (h : IsFinPart Γ.M X.T φ) (h' : IsFinPart Γ.M' X.T φ') (e : R.p f = R.p' f')
    (e' : ∀ v, Rf.p v (φ v) = Rf.p' v (φ' v)) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs Γ X R Rf (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f' φ') :=
  ⟨X.T, subset_rfl, 1, 1, fun _ => f, fun _ => φ, fun _ => f', fun _ => φ', fun _ => ⟨hf, h⟩, fun _ => ⟨hf', h'⟩,
    by rw [Fin.sum_univ_one], by rw [Fin.sum_univ_one], by simp only [Fin.sum_univ_one, e, e']⟩

end Global

theorem flip_match {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil)
    (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (hst : SquareStanding G t) (M : Vol G) :
    (M.Is t → ∃ (e : Num G i j) (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
      (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W),
      IsTripleOf W M t i j e Bs Γ X ∧ IsTriple Bs Γ X om om' ∧ IsDoublyCompatible t i j e Bs Γ X) ∧
    ∀ (e : Num G i j) (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
      (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W), IsTripleOf W M t i j e Bs Γ X → IsDoublyCompatible t i j e Bs Γ X →
      ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ X om om' R Rf →
      ∃ f₀ f₀', (f₀ ≠ 0 ∧ Γ.M.IsGauss Bs.ψ Bs.emb f₀) ∧ (f₀' ≠ 0 ∧ Γ.M'.IsGauss Bs.ψ Bs.emb f₀') ∧
        ∀ n Φ τ τ', (∀ w ∈ locPl G t, depthAt G w ≤ n w ∧ IsNatDatum (unifAt w) (n w) (Φ w)) → HasFlip B t ρ i j n Φ τ τ' →
          ∃ φ φ', IsFinPart Γ.M X.T φ ∧ IsFinPart Γ.M' X.T φ' ∧ IsDatumA W e Γ τ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ φ) ∧
            IsDatumB W e Γ τ' (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀' φ') ∧ (∀ v, Rf.p v (φ v) = Rf.p' v (φ' v)) ∧
            ∀ f ∈ Γ.M.Pol Bs.ψ Bs.emb, ∀ f' ∈ Γ.M'.Pol Bs.ψ Bs.emb, R.p f = R.p' f' →
              GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs Γ X R Rf (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f' φ') := by
  refine ⟨exists_tiedBoth hL W t i j hst M, fun e Bs Γ X om om' h hti R Rf hm => ?_⟩
  obtain ⟨f₀, f₀', a, b, c⟩ := finite_match hL W B ρ t i j M hst h hm hti
  refine ⟨f₀, f₀', a, b, fun n Φ τ τ' hn hF => ?_⟩
  obtain ⟨φ, φ', d1, d2, d3, d4, d5⟩ := c n Φ τ τ' hn hF
  exact ⟨φ, φ', d1, d2, d3, d4, d5, fun f hf f' hf' e => polMatch_pure hf hf' d1 d2 e d5⟩

end GlobalTheory.FlipMatch

end
