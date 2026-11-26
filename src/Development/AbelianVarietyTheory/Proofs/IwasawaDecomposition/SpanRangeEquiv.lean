module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SwapCastEqSwapAE
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeOperatorKeepsRationalIntegralLevelForms
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernTopPartHodgeMetricUniformisationImage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelUnipotentGenericCharTypePlace
public import Formalism.LocalToGlobal.Columns.MtAdWtIrr
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HwFixEx
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteGroupGoodSetLevelsCharacters
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLiftFormsAdelicDecoratedLattices

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevOfAll
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MtIn.LevAll

theorem exists_levOf_all : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px), I.Ok → SelHalf I → ∀ (U₀ : Set I.ι) (L₀ : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U₀)), LevOf X I U₀ L₀ → ∀ U : Set I.ι, ∃ L, LevOf X I U L := by
  intro X px I hI hsel U₀ L₀ hL₀ U
  classical
  have htw : ∀ a, Chr.IsTwist X.B.host I.S (I.xi a) := fun a =>
    (GlobalTheory.Mem.ReadTwist.isTwist_of_reads _ X.B.host _ _ _ (I.tup a) (I.xi a) (hI.xi_reads a)).1
  have hram := GlobalTheory.Mem.Col2.RamQ.ram_iff X px I hI
  have hQr : ∀ a, ∀ PP ∈ I.Q a, ¬ (I.xi a).UnrAt PP := fun a PP h => (hram a PP).2 (Or.inl h)
  have hpl := fun a => GlobalTheory.Mem.TwistPlaces.twistPlaces X px I hI a (hQr a)
  obtain ⟨L0, h1, h2, h3, -, h4⟩ := GlobalTheory.LevelChoices.exists_levCh X.toD7 (Top.Fr.at X I.C) (TupU I U)
    (mu0F (X := X.B.fields) (tuOf I U)) (fun t => I.xi (ixOf I U t)) (fun t => I.Q (ixOf I U t))
    (hI.xi_inj.comp (ixOf_injective I U)) (by simp only [ixOf_mu0F]; exact hI.trueColumnChoices_heckeChar_reference_eq_one)
    (fun t => (htw _).1) (fun t => (htw _).2.1) (fun t => (htw _).2.2.1)
    (fun t => (hpl _).1) (fun t => (hpl _).2)
    (fun p hp => by
      have hpp : p.Prime := by
        rcases hp with rfl | rfl
        exacts [X.B.host.pde_prime, X.B.host.pde'_prime]
      obtain ⟨𝔭, h𝔭⟩ := GlobalTheory.Mem.R3.Model.exists_under_of_selHalf I hsel p hpp
      exact ⟨𝔭, fun t PP hPP hp' => h𝔭 _ PP hPP hp'⟩)
    (fun t PP => hram _ PP)
  have hPg : L0.Pg = (X.B.primes px).vGs := by
    refine Finset.ext fun P => (h4.Pg P).trans ?_
    rw [h1]
    exact (GlobalTheory.Mem.R3.Model.mem_vGs_iff I hI P).symm
  let L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U) :=
    { L0 with
      ΛY := L₀.ΛY
      ΛW := L₀.ΛW
      ΛX := L₀.ΛX
      ΛV := L₀.ΛV
      βY := L₀.βY
      βW := L₀.βW
      βX := L₀.βX
      βV := L₀.βV }
  exact ⟨L, ⟨⟨h4.mu0, h4.eta, h4.xi, h4.xi_inj, h4.xi_base, h4.xi_fin, h4.xi_triv, h4.xi_tame, h4.Pg, h4.Q_pl,
      h4.Q_off, h4.Q_de, h4.Q_ram, h4.chi, h4.xiR, hL₀.is.βY, hL₀.is.βX, hL₀.is.βV, hL₀.is.βW⟩, h1, fun t => congrFun h2 t, hPg,
      fun t => congrFun h3 t, hL₀.beta⟩⟩

end GlobalTheory.MtIn.LevAll

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefficientSpaceDefiniteFormIrreducibleAlgebraic
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefficientSpaceDefiniteFormIrreducibleAlgebraic
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MtIn

open _root_.Formalism.L2.Col

theorem map_inv_mat {E K : Type} [Field E] [Field K] (f : E →+* K) {n : ℕ} (γE : GL (Fin n) E) :
    ((γE : Matrix (Fin n) (Fin n) E).map f)⁻¹ = ((γE : Matrix (Fin n) (Fin n) E)⁻¹).map f := by
  have h := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) (map_inv (Matrix.GeneralLinearGroup.map f) γE)
  have h1 : ((Matrix.GeneralLinearGroup.map f γE : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (γE : Matrix (Fin n) (Fin n) E).map f := rfl
  have h2 : ((Matrix.GeneralLinearGroup.map f γE⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = ((γE⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map f := rfl
  simp only [Matrix.coe_units_inv] at h h2
  rw [h1] at h
  rw [h2] at h
  exact h.symm

theorem isAlgWeight_of_equiv {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W W' : Type}
    [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (ρ : Representation ℂ (ReciprocityTheory.Aut.GQ L n) W) (ρ' : Representation ℂ (ReciprocityTheory.Aut.GQ L n) W')
    (T : W ≃ₗ[ℂ] W') (hT : ∀ γ x, T (ρ γ x) = ρ' γ (T x)) (h : Formalism.AUTREP.IsAlgWeight L n ρ) :
    Formalism.AUTREP.IsAlgWeight L n ρ' := by
  obtain ⟨hf, κ, hfi, hd, bs, P, hP⟩ := h
  refine ⟨LinearEquiv.finiteDimensional T, κ, hfi, hd, bs.map T, P, fun γ γ₀ hm => ?_⟩
  rw [← hP γ γ₀ hm]
  ext i j
  rw [LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, Module.Basis.map_apply, ← hT, Module.Basis.map_repr,
    LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]

theorem exists_weight_of_coefMap {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {ι : Type} [Fintype ι]
    {K : Type} [Field K] (φ : K →+* ℂ) (lab : ι → L →+* K) (emb : ι → L →+* ℂ) (hlab : ∀ τ x, φ (lab τ x) = emb τ x)
    (hinj : Function.Injective emb) (hcm : ∀ τ τ', emb τ ≠ ComplexEmbedding.conjugate (emb τ'))
    (lam : ι → DomWeight n) {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (ReciprocityTheory.Aut.GQ L n) W)
    (c0 : VV K lam →ₛₗ[φ] W)
    (h0 : ∀ γ v, c0 (rhoVr lab lam (mtwRat (L := L) (n := n) γ) v) = ρ γ (c0 v))
    (h1 : LinearIndependent ℂ fun i => c0 (bVV K lam i))
    (h2 : Submodule.span ℂ (Set.range fun i => c0 (bVV K lam i)) = ⊤) :
    ∃ (alg : Formalism.AUTREP.IsAlgWeight L n ρ) (irr : ρ.IsIrreducible), ∀ (a : NG.AlgWt L n) (τ : ι) (lam0 : Fin n → ℤ),
      NG.AlgWt.IsDual { W := W, ρ := ρ, alg := alg, irr := irr } a → a.HWAt (emb τ) lam0 → lam0 = (lam τ).w := by
  obtain ⟨T, hT⟩ := GlobalTheory.CoefReal.exists_scalarExt φ lam c0 h1 h2
  have hint : ∀ (γ : ReciprocityTheory.Aut.GQ L n) (x : VV ℂ lam), T (mtRep emb lam γ x) = ρ γ (T x) := by
    intro γ x
    have hfam : (fun τ => Formalism.UG.bc φ (invTrK (embGL lab (mtwRat (L := L) (n := n) γ)) τ)) =
        mtwInvTr (mtwEmb emb (mtwRat (L := L) (n := n) γ)) := by
      funext τ
      apply Units.ext
      ext a b
      simp [mtwInvTr, mtwEmb, inside₂, invTrK_coe, bc_coe, embGL_coe, hlab, map_inv_mat]
    have hL : T.toLinearMap ∘ₗ mtRep emb lam γ = ρ γ ∘ₗ T.toLinearMap := by
      refine LinearMap.ext_on_range (GlobalTheory.CoefModel.span_mapVV φ lam) fun i => ?_
      show T (rhoK lam (mtwInvTr (mtwEmb emb (mtwRat (L := L) (n := n) γ)))
        (GlobalTheory.CoefModel.mapVV φ lam _)) = ρ γ (T _)
      rw [← hfam, ← GlobalTheory.CoefModel.mapVV_rhoK, hT, hT]
      exact h0 γ _
    exact LinearMap.congr_fun hL x
  have hi : TenIrr emb lam := tenIrr_of' highest_weight_fixed_exists highest_weight_fixed_line emb hinj hcm lam
  have alg : Formalism.AUTREP.IsAlgWeight L n ρ := isAlgWeight_of_equiv (mtRep emb lam) ρ T hint (mtRep_alg emb lam)
  have irr : ρ.IsIrreducible :=
    GlobalTheory.PiIsotypic.isIrreducible_of_linearEquiv (mtRep emb lam) ρ T (fun g v => (hint g v).symm) hi
  refine ⟨alg, irr, fun a τ lam0 hd hw => ?_⟩
  obtain ⟨B, hB0, hB⟩ : ∃ B : W →ₗ[ℂ] a.W →ₗ[ℂ] ℂ, B ≠ 0 ∧ ∀ γ x y, B (ρ γ x) (a.ρ γ y) = B x y := hd
  have hd' : ∃ B : VV ℂ lam →ₗ[ℂ] a.W →ₗ[ℂ] ℂ, B ≠ 0 ∧ ∀ γ x y, B (mtRep emb lam γ x) (a.ρ γ y) = B x y := by
    refine ⟨B ∘ₗ T.toLinearMap, fun h => hB0 (LinearMap.ext fun w => ?_), fun γ x y => ?_⟩
    · obtain ⟨x, rfl⟩ := T.surjective w
      exact LinearMap.congr_fun h x
    · show B (T (mtRep emb lam γ x)) (a.ρ γ y) = B (T x) y
      rw [hint]
      exact hB γ (T x) y
  exact mtWtOf_hw_dual highest_weight_fixed_exists highest_weight_fixed_line emb hinj hcm lam τ a lam0 hd' hw

theorem wt_main : ∀ (D : D7) (V : HSp D) (P : principalLevelFrame.RowPsi V V.rank) (e : ReciprocityTheory.Aut.GQ D.host.E V.rank ≃* Formalism.L2.Theta.GQ V), RatIso P e → ∀ (c : CoefA V) (lam : D.what₂.Tau → DomWeight V.rank) (c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] c.W), Bridge.CoefMapTie V c.coef c0 (rhoVr (labLL D) lam) → ∃ (alg : Formalism.AUTREP.IsAlgWeight D.host.E V.rank (wtRep c e)) (irr : (wtRep c e).IsIrreducible), ∀ (a : NG.AlgWt D.host.E V.rank) (τ : D.what₂.Tau) (lam0 : Fin V.rank → ℤ), NG.AlgWt.IsDual { W := c.W, ρ := wtRep c e, alg := alg, irr := irr } a → a.HWAt (Formalism.L2.embT D τ) lam0 → lam0 = (lam τ).w := by
  intro D V P e hR c lam c0 ht
  exact exists_weight_of_coefMap D.what₂.embLL (labLL D) (tauE D) GlobalTheory.CoefSpace.embLL_labLL (GlobalTheory.StdRat.tauE_injective D)
    (fun τ τ' h => (GlobalTheory.StdRat.tauE_cm D (tauE D τ')).1 ⟨τ', rfl⟩ ⟨τ, h⟩) lam (wtRep c e) c0
    (fun γ v => ht.1 (e γ) (mtwRat (L := D.host.E) (n := V.rank) γ)
      ((hR γ).2 _ (congrArg Units.val (mtwInc_mtwRatFun γ)).symm) v) ht.2.1 ht.2.2

end GlobalTheory.MtIn

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefficientSpaceDefiniteFormIrreducibleAlgebraicStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefficientSpace_definiteForm_irreducibleAlgebraicWeight : ∀ (D : D7) (V : HSp D) (P : principalLevelFrame.RowPsi V V.rank) (e : ReciprocityTheory.Aut.GQ D.host.E V.rank ≃* Formalism.L2.Theta.GQ V), RatIso P e → ∀ (c : CoefA V) (lam : D.what₂.Tau → DomWeight V.rank) (c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] c.W), Bridge.CoefMapTie V c.coef c0 (rhoVr (labLL D) lam) → ∃ (alg : Formalism.AUTREP.IsAlgWeight D.host.E V.rank (wtRep c e)) (irr : (wtRep c e).IsIrreducible), ∀ (a : NG.AlgWt D.host.E V.rank) (τ : D.what₂.Tau) (lam0 : Fin V.rank → ℤ), NG.AlgWt.IsDual { W := c.W, ρ := wtRep c e, alg := alg, irr := irr } a → a.HWAt (Formalism.L2.embT D τ) lam0 → lam0 = (lam τ).w := by
  first | exact @GlobalTheory.MtIn.wt_main | exact GlobalTheory.MtIn.wt_main | (intros; apply GlobalTheory.MtIn.wt_main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitFrame
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MtIn

theorem isOrthF_one {D : D7} (V : HSp D) (h : V.gram = 1) : GlobalTheory.StdFrameExist.IsOrthF V 1 := by
  unfold GlobalTheory.StdFrameExist.IsOrthF GlobalTheory.StdFrameExist.gA
  rw [h, Matrix.map_one _ (map_zero _) (map_one _), Units.val_one, Formalism.UG.cT_one, Matrix.mul_one, Matrix.mul_one]

theorem intM_one {D : D7} (n : ℕ) : GlobalTheory.StdFrameExist.IntM (GlobalTheory.StdFrameExist.SI D) (1 : GL (Fin n) (Lev.EAf D)).1 := by
  intro i j
  rw [Units.val_one, Matrix.one_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem exists_unit_frame : ∀ (D : D7) (V : HSp D) (hF : D.host.F = maximalRealSubfield D.host.E), V.gram = 1 → Seed.FrmC.StdLat V → ∃ P : principalLevelFrame.RowPsi V V.rank, StdFrame hF P ∧ UnitFr P := by
  intro D V hF hg hV
  have h := isOrthF_one V hg
  refine ⟨GlobalTheory.StdFrameExist.rowPsi V 1 h, GlobalTheory.StdFrameExist.stdFrame_rowPsi hF hV h (intM_one _) ?_, fun κ => ?_⟩
  · rw [inv_one]; exact intM_one _
  · show finE V (GlobalTheory.StdFrameExist.psiF V 1 h κ) = _
    rw [GlobalTheory.StdFrameExist.finE_psiF, one_mul, inv_one, mul_one]
    rfl

end GlobalTheory.MtIn
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqPlMapOfConj
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MtIn.GenOff

theorem mem_iff_of_conj (D : D7) (s : ReciprocityTheory.Aut.SplitPlace D.host.E) {v : PlE D.host}
    (hc : Formalism.BasicNotions.IsConjPl D.host v s.w) (a : 𝓞 (maximalRealSubfield D.host.E)) :
    algebraMap _ (𝓞 D.host.E) a ∈ v.asIdeal ↔ a ∈ s.v.asIdeal := by
  rw [hc (algebraMap _ (𝓞 D.host.E) a) (algebraMap _ (𝓞 D.host.E) a) ?_, ← Ideal.mem_comap, s.w_under]
  rw [GlobalTheory.SplitPlaceOver.host_conj_eq']
  exact (IsCMField.complexConj_apply_eq_self D.host.E (a : maximalRealSubfield D.host.E)).symm

theorem eq_of_conj (D : D7) {w v u : PlE D.host} (hw : Formalism.BasicNotions.IsConjPl D.host w u) (hv : Formalism.BasicNotions.IsConjPl D.host v u) :
    w = v := by
  refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
  have hy : ((IsCMField.ringOfIntegersComplexConj D.host.E x : 𝓞 D.host.E) : D.host.E) = D.host.conj (x : D.host.E) := by
    rw [IsCMField.coe_ringOfIntegersComplexConj, GlobalTheory.SplitPlaceOver.host_conj_eq']
  exact (hw x _ hy).trans (hv x _ hy).symm

theorem eq_plMap_of_conj (D : D7) {v u : PlE D.host} (hc : Formalism.BasicNotions.IsConjPl D.host v u) :
    u = Formalism.L2.Host.CT.plMap GlobalTheory.CMVal.InvConj.conjE v := by
  refine HeightOneSpectrum.ext (Ideal.ext fun z => ?_)
  set x := IsCMField.ringOfIntegersComplexConj D.host.E z
  have hz : z = RingOfIntegers.mapRingEquiv GlobalTheory.CMVal.InvConj.conjE x := by
    apply RingOfIntegers.ext
    show (z : D.host.E) = IsCMField.complexConj D.host.E (x : D.host.E)
    rw [IsCMField.coe_ringOfIntegersComplexConj, IsCMField.complexConj_apply_apply]
  have hy : (z : D.host.E) = D.host.conj (x : D.host.E) := by
    rw [GlobalTheory.SplitPlaceOver.host_conj_eq', IsCMField.coe_ringOfIntegersComplexConj, IsCMField.complexConj_apply_apply]
  rw [← (hc x z hy), hz, Formalism.L2.Host.CT.mem_plMap]

theorem gen_off_level : ∀ (D : D7) (cf : CharFrame D) (l : ℕ) (Q : Finset (PlE D.host)) (ψ : HChar D.host.E), (∀ v, v ∉ Q → ψ.UnrAt v) → ψ.TrivOn D.host.F → ∀ (j : Fin D.R.m) (v : PlE D.host) (k : ℕ) (s : ReciprocityTheory.Aut.SplitPlace D.host.E), GenAt D l Q v k → Formalism.BasicNotions.IsConjPl D.host v s.w → s.v ∉ gPl D ∪ qPl D (cf.mu0 j * ((if l = D.host.pde then cf.del' else cf.del) * ψ)) ∧ ¬ s.Above l := by
  intro D cf l Q ψ hψ hT j v k s hg hc
  obtain ⟨-, hvl, hvS, hvQ, -, -⟩ := hg
  have hvn : ∀ n : ℕ, ((n : ℕ) : 𝓞 (maximalRealSubfield D.host.E)) ∈ s.v.asIdeal → ((n : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal :=
    fun n h => by
      have := (mem_iff_of_conj D s hc (n : 𝓞 (maximalRealSubfield D.host.E))).2 h
      rwa [map_natCast] at this
  have hoff : ∀ w : PlE D.host, NG.OverPl w s.v → ∀ n : ℕ, ((n : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal →
      ((n : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal := fun w hw n h =>
    hvn n (by rw [← hw, Ideal.mem_comap, map_natCast]; exact h)
  have hg' : ∀ w : PlE D.host, NG.OverPl w s.v → ∀ k : Fin 2, w ∉ placesOver D.host.E (D.host.g k) := by
    intro w hw k hk
    have h := hoff w hw _ hk
    apply hvS
    refine ⟨?_, hvl⟩
    fin_cases k
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have hgPl : s.v ∉ gPl D := by
    rintro ⟨w, hw, k, hk⟩
    exact hg' w hw k hk
  refine ⟨?_, fun hl => hvl (hvn l hl)⟩
  rintro (h | ⟨-, w, hw, hu⟩)
  · exact hgPl h
  apply hu
  refine HChar.UnrAt.mul ((cf.isMu0 j).unr w fun k hk => hg' w hw k hk) (HChar.UnrAt.mul ?_ ?_)
  · split_ifs with hlp
    · exact cf.isDel'.unr w fun hp => hvS ⟨Or.inr (Or.inr (by rw [if_pos hlp]; exact hoff w hw _ hp)), hvl⟩
    · exact cf.isDel.unr w fun hp => hvS ⟨Or.inr (Or.inr (by rw [if_neg hlp]; exact hoff w hw _ hp)), hvl⟩
  · rcases GlobalTheory.SplitPlaceOver.eq_or_isConjPl D s w hw with e | e
    · rw [← e, eq_plMap_of_conj D hc]
      exact (GlobalTheory.CMVal.InvConj.unrAt_inv_iff ψ hT v).1 (HChar.UnrAt.inv (hψ v hvQ))
    · rw [eq_of_conj D e hc]
      exact hψ v hvQ

end GlobalTheory.MtIn.GenOff
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntOfFinite
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MtIn

theorem exists_int_of_finite {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) {G : Type} [Group G] [Finite G]
    (f : G →* ℂˣ) (g : G) (h : ∃ y : K, σ y = ((f g : ℂˣ) : ℂ)) : ∃ z : 𝓞 K, σ (z : K) = ((f g : ℂˣ) : ℂ) := by
  obtain ⟨y, hy⟩ := h
  have hn : 0 < Nat.card G := Nat.card_pos
  have hfg : (f g) ^ Nat.card G = 1 := by rw [← map_pow, pow_card_eq_one', map_one]
  have hy1 : y ^ Nat.card G = 1 := by
    apply σ.injective
    rw [map_pow, hy, map_one, ← Units.val_pow_eq_pow_val, hfg, Units.val_one]
  have hint : IsIntegral ℤ y := IsIntegral.of_pow hn (by rw [hy1]; exact isIntegral_one)
  exact ⟨⟨y, hint⟩, hy⟩

end GlobalTheory.MtIn

theorem GlobalTheory.MtIn.levChi_integral : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)), I.Ok → LevOf X I U L → ∀ (i : Fin X.toD7.R.m) (t : TupU I U) (k : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).J), ∃ z : 𝓞 X.toD7.what₂.LL, X.toD7.what₂.embLL (z : X.toD7.what₂.LL) = ((levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).χ k : ℂ) := by
  intro X px I U L hI hL i t k
  have hfin : ∀ PP : Pl X.toD7.host.E, Finite (kP PP)ˣ := fun PP =>
    haveI : Finite (kP PP) := Ideal.finiteQuotientOfFreeOfNeBot PP.asIdeal PP.ne_bot
    Finite.of_injective _ Units.val_injective
  have lift : ∀ (PP : Pl X.toD7.host.E) (d : (kP PP)ˣ), ∃ (a : 𝓞 X.toD7.host.E) (kE : X.toD7.host.Eˣ),
      (kE : X.toD7.host.E) = a ∧ (d : kP PP) = Ideal.Quotient.mk _ a := by
    intro PP d
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (d : kP PP)
    have ha0 : (a : X.toD7.host.E) ≠ 0 := by
      intro h0
      have : a = 0 := by exact_mod_cast h0
      apply d.ne_zero
      rw [← ha, this, map_zero]
    exact ⟨a, Units.mk0 _ ha0, rfl, ha.symm⟩
  have hchi : ∀ PP ∈ L.Pg, ∀ d : (kP PP)ˣ, ∃ y, X.toD7.what₂.embLL y = (((L.chi ((i : ℕ) + 1) PP)⁻¹ d : ℂˣ) : ℂ) := by
    intro PP hPP d
    obtain ⟨a, kE, h1, h2⟩ := lift PP d
    have hres := hL.is.chi i PP hPP a kE d h1 h2
    rw [hres, hL.C]
    have hw : PP ∈ (X.B.primes px).vGs := hL.Pg ▸ hPP
    exact ⟨_, ((hI.ch_tied.mu0 i).atg ⟨PP, hw⟩ kE a d h1 h2).symm⟩
  have hxi : ∀ PP ∈ L.Q t, ∀ d : (kP PP)ˣ, ∃ y, X.toD7.what₂.embLL y = ((L.xiR t PP d : ℂˣ) : ℂ) := by
    intro PP hPP d
    obtain ⟨a, kE, h1, h2⟩ := lift PP d
    have hres := hL.is.xiR t PP hPP a kE d h1 h2
    rw [hres, hL.xiH t]
    exact ⟨_, (hI.xi_reads (ixOf I U t) _).symm⟩
  let Pr : ℂˣ → Prop := fun u => ∃ z : 𝓞 X.toD7.what₂.LL, X.toD7.what₂.embLL (z : X.toD7.what₂.LL) = (u : ℂ)
  have hmul : ∀ a b : ℂˣ, Pr a → Pr b → Pr (a * b) := by
    rintro a b ⟨za, ha⟩ ⟨zb, hb⟩
    exact ⟨za * zb, by rw [Units.val_mul, ← ha, ← hb, ← map_mul]; rfl⟩
  have hone : Pr 1 := ⟨1, by rw [Units.val_one, ← map_one X.toD7.what₂.embLL]; rfl⟩
  have gchi : ∀ PP ∈ L.Pg, ∀ (c : ℕ) (d : (kP PP)ˣ), Pr ((if Frm.A = Frm.B then (fun _ : ℕ => L.chi ((i : ℕ) + 1)) else
      fun (_ : ℕ) (PP : Pl X.toD7.host.E) => (L.chi ((i : ℕ) + 1) PP)⁻¹) c PP d) := by
    intro PP hPP c d
    haveI := hfin PP
    have e : (if Frm.A = Frm.B then (fun _ : ℕ => L.chi ((i : ℕ) + 1)) else fun (_ : ℕ) (PP : Pl X.toD7.host.E) => (L.chi ((i : ℕ) + 1) PP)⁻¹) =
        fun (_ : ℕ) (PP : Pl X.toD7.host.E) => (L.chi ((i : ℕ) + 1) PP)⁻¹ := if_neg (by decide)
    rw [e]
    exact exists_int_of_finite X.toD7.what₂.embLL (L.chi ((i : ℕ) + 1) PP)⁻¹ d (hchi PP hPP d)
  have gxi : ∀ PP ∈ L.Q t, ∀ d : (kP PP)ˣ, Pr ((if Frm.A = Frm.B then (fun PP => (L.xiR t PP)⁻¹) else L.xiR t) PP d) := by
    intro PP hPP d
    haveI := hfin PP
    have e : (if Frm.A = Frm.B then (fun PP => (L.xiR t PP)⁻¹) else L.xiR t) = L.xiR t := if_neg (by decide)
    rw [e]
    exact exists_int_of_finite X.toD7.what₂.embLL (L.xiR t PP) d (hxi PP hPP d)
  show Pr (Formalism.L2.DIV.levFn (L.βV i) (flag1L (L.datVt i t)) _)
  unfold Formalism.L2.DIV.levFn
  refine hmul _ _ (hmul _ _ ?_ (Finset.prod_induction _ Pr hmul hone fun PP hPP =>
    Finset.prod_induction _ Pr hmul hone fun c _ => ?_)) (Finset.prod_induction _ Pr hmul hone fun PP hPP => ?_)
  · unfold Formalism.L2.DIV.ext1
    split_ifs
    · exact hone
    · exact hone
  · exact gchi PP hPP (c + 1) _
  · exact gxi PP hPP _
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideIn
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MtIn

variable {D : D7}

set_option genInjectivity false in
set_option genSizeOfSpec false in
structure SideIn (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (c : CoefA V) (j : ℕ) (hr : D.R.r ≤ V.rank)
    (Pg Q : Finset (Pl D.host.E)) (chi xi : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) : Type 1 where
  G₀ : Type
  [grp : Group G₀]
  [fin : Fintype G₀]
  S : CSD D.what₂.LL
  act : Representation D.what₂.LL G₀ S.Forms
  pres : Bridge.ClassPres (Bridge.ratF V) S D.what₂.embLL c.coef.ρ (levEnv V β (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).J
    (levEnv V β (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).χ
  tie : Bridge.ActTie (Bridge.ratF V) pres (levEnv V β (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).Q
    (levEnv V β (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).ch act
  eG : G₀ ≃* G0 Pg D.R.r
  P₀ : Subgroup G₀
  ψ₀ : P₀ →* D.what₂.LLˣ
  red : ∀ q : (levEnv V β (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).Q, eG (tie.red q) =
    rTup β (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi) (Formalism.UG.bc (swapAE D) ((q : Bridge.Gf V) : GL _ _))
  lev : levPOf eG D.what₂.embLL P₀ ψ₀ = P0 Pg D.R.r ψ
  c0 : VV D.what₂.LL (fun τ => Bridge.lamLdef (D := D) V.rank j τ) →ₛₗ[D.what₂.embLL] c.W
  pair : VV D.what₂.LL (fun τ => Bridge.lamLdef (D := D) V.rank j τ) →ₗ⋆[D.what₂.LL]
    VV D.what₂.LL (fun τ => Bridge.lamLdef (D := D) V.rank j τ) →ₗ[D.what₂.LL] D.what₂.LL
  del : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) →
    Submodule (𝓞 D.what₂.LL) (VV D.what₂.LL (fun τ => Bridge.lamLdef (D := D) V.rank j τ))
  map : Bridge.CoefMapTie V c.coef c0 (rhoVr (labLL D) _)
  coef : Bridge.CoefTie V c.coef pres _ c0 pair (nabAtr (labLL D) _) del
  vals : ∀ k : (levEnv V β (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).J, ∃ z : 𝓞 D.what₂.LL,
    D.what₂.embLL (z : D.what₂.LL) = ((levEnv V β (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).χ k : ℂ)

attribute [instance] SideIn.grp SideIn.fin

namespace SideIn

variable {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {c : CoefA V} {j : ℕ} {hr : D.R.r ≤ V.rank}
  {Pg Q : Finset (Pl D.host.E)} {chi xi : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ} {ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ}
  (u : SideIn V β c j hr Pg Q chi xi ψ)

abbrev dim : ℕ := u.S.lvlDim u.act u.P₀ u.ψ₀⁻¹

abbrev nab : Submodule (𝓞 D.what₂.LL) (Fin u.dim → D.what₂.LL) := u.S.lvlNab u.act u.P₀ u.ψ₀⁻¹

def fn (x : Fin u.dim → D.what₂.LL) : Bridge.Gf V → c.W := u.pres.ext (lvlForm u.S u.act u.P₀ u.ψ₀⁻¹ x).1

end SideIn

set_option genInjectivity false in
set_option genSizeOfSpec false in
structure TupIn (μ : D.what₂.Tup) (i : Fin D.R.m) (c : CoefA (Vc D i)) {T : Type} (L : LevCh D T) (t : T)
    (ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) : Type 1 where
  u : SideIn (Vc D i) (L.βV i) c ((i : ℕ) + 1) (r_le_V i) L.Pg (L.Q t) (L.chi ((i : ℕ) + 1)) (L.xiR t) ψ
  e : (Fin u.dim → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL μ ((i : ℕ) + 1)
  li : LinearIndependent ℂ fun a => D.what₂.jMt μ ((i : ℕ) + 1) (e (Pi.single a 1))
  span : Submodule.span ℂ (Set.range fun a => D.what₂.jMt μ ((i : ℕ) + 1) (e (Pi.single a 1))) = ⊤
  lat : OLatTie D.what₂.embLL (D.what₂.MtLat μ ((i : ℕ) + 1)) ((D.what₂.jMt μ ((i : ℕ) + 1)).comp e.toLinearMap) u.nab

structure Good {μ : D.what₂.Tup} (i : Fin D.R.m) (m : MtReal D μ ((i : ℕ) + 1)) (χ : HChar D.host.E) : Prop where
  prod : NG.IsProdLevel m.J
  para : ∀ v ∈ qPl D χ, ∃ (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ),
    s.v = v ∧ NG.IsCompAt χ s ξ ∧ NG.LevelPara m.J m.χ s D.R.r ξ
  uni : ∀ (k : Fin 2) (v : D.nd.PlG k) (s : ReciprocityTheory.Aut.SplitPlace D.host.E), s.w = D.naut.plGw k v →
    ∃ (ψ₀ : AddChar (s.v.adicCompletion (maximalRealSubfield D.host.E)) ℂ)
      (ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ), NG.IsPsi0 s ψ₀ ∧ NG.IsCompAt χ s ξ ∧
      NG.LevelUni m.J m.χ s D.R.r ψ₀ ξ
  hyp : NG.HypOutside m.J m.χ (gPl D ∪ qPl D χ)
  wt : ∀ (t : D.what₂.Tau) (a : NG.AlgWt D.host.E D.R.nV) (lam : Fin D.R.nV → ℤ),
    m.wt.IsDual a → a.HWAt (embT D t) lam → NG.infOf lam = NG.paramV D.R (D.hc t) i (1 / 2)
  rat : ∀ (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)) (k : ℕ),
    s.v ∉ gPl D ∪ qPl D χ → Formalism.AUTREP.IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∀ x, ∃ x',
      m.real (D.what₂.jMt μ ((i : ℕ) + 1) x') = NG.tN m.J s ϖ k (m.real (D.what₂.jMt μ ((i : ℕ) + 1) x))
  int : ∀ (w : D.what₂.places.Pl) (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)) (k : ℕ),
    s.v ∉ gPl D ∪ qPl D χ → ¬ s.Above (D.what₂.places.resChar w) → Formalism.AUTREP.IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV →
    ∀ y ∈ (D.what₂.MtLat μ ((i : ℕ) + 1)).gen, ∃ c : D.what₂.Mt μ ((i : ℕ) + 1) → D.what₂.LL, (∀ g, 0 ≤ D.what₂.places.val w (c g)) ∧
      NG.tN m.J s ϖ k (m.real y) = m.real (∑ g ∈ (D.what₂.MtLat μ ((i : ℕ) + 1)).gen, D.what₂.embLL (c g) • g)
  full : (∀ y ∈ (D.what₂.MtLat μ ((i : ℕ) + 1)).gen, y ∈ Set.range (D.what₂.jMt μ ((i : ℕ) + 1))) ∧
    Submodule.span ℂ ((D.what₂.MtLat μ ((i : ℕ) + 1)).gen : Set (D.what₂.Mt μ ((i : ℕ) + 1))) = ⊤

end GlobalTheory.MtIn

end
end

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000

namespace GlobalTheory.MtId

variable {D : D7}

theorem span_range_equiv {M N ι : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] (T : M ≃ₗ[ℂ] N) {f : ι → M}
    {S : Submodule ℂ M} {S' : Submodule ℂ N} (h : Submodule.span ℂ (Set.range f) = S) (h' : ∀ F, F ∈ S ↔ T F ∈ S') :
    Submodule.span ℂ (Set.range fun k => T (f k)) = S' := by
  have h1 : (Set.range fun k => T (f k)) = T.toLinearMap '' Set.range f := by
    rw [← Set.range_comp]; rfl
  rw [h1, ← Submodule.map_span, h]
  ext F
  obtain ⟨F, rfl⟩ := T.surjective F
  rw [Submodule.mem_map_equiv, T.symm_apply_apply]
  exact h' F

theorem constr_semi {K M N : Type} [Field K] [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] {σ : K →+* ℂ} {d : ℕ}
    (j : (Fin d → K) →ₛₗ[σ] M) (Φ : (Fin d → K) →ₛₗ[σ] N) (li : LinearIndependent ℂ fun a => j (Pi.single a 1))
    (sp : Submodule.span ℂ (Set.range fun a => j (Pi.single a 1)) = ⊤) (li' : LinearIndependent ℂ fun a => Φ (Pi.single a 1)) :
    ∃ r : M →ₗ[ℂ] N, Function.Injective r ∧ LinearMap.range r = Submodule.span ℂ (Set.range fun a => Φ (Pi.single a 1)) ∧
      ∀ x, r (j x) = Φ x := by
  let b : Module.Basis (Fin d) ℂ M := Module.Basis.mk li sp.ge
  have hb : ∀ a, b.constr ℂ (fun a => Φ (Pi.single a 1)) (j (Pi.single a 1)) = Φ (Pi.single a 1) := fun a => by
    have : j (Pi.single a 1) = b a := (Module.Basis.mk_apply li sp.ge a).symm
    rw [this, Module.Basis.constr_basis]
  refine ⟨b.constr ℂ fun a => Φ (Pi.single a 1), b.injective_constr_of_linearIndependent li', b.constr_range ℂ, fun x => ?_⟩
  have hx : x = ∑ a, x a • (Pi.single a 1 : Fin d → K) := by
    funext i; simp [Finset.sum_apply, Pi.single_apply]
  rw [hx]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smulₛₗ, hb, RingHom.id_apply]

theorem side_read {V : HSp D} {n : ℕ} (hn : V.rank = n) {β : GL (Fin V.rank) (EAf D)} (hβ : β = 1) {c : CoefA V} {j : ℕ}
    {hr : D.R.r ≤ V.rank} (hr' : D.R.r ≤ n) {Pg Q : Finset (Pl D.host.E)} {chi xi : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ}
    {ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ} (u : SideIn V β c j hr Pg Q chi xi ψ) (hg : V.gram = 1)
    (hs : Seed.FrmC.StdLat V) {P : principalLevelFrame.RowPsi V V.rank} (hP : UnitFr P)
    (Lv : LevelP Pg D.R.r ℂ) (hLv : levPOf u.eG D.what₂.embLL u.P₀ u.ψ₀ = Lv) :
    ∃ (a : NG.AlgWt D.host.E n) (eW : a.W ≃ₗ[ℂ] c.W)
      (Φ : (Fin u.dim → D.what₂.LL) →ₛₗ[D.what₂.embLL] (Formalism.AUTREP.GAf D.host.E n → a.W)),
      (∀ (a' : NG.AlgWt D.host.E n) (τ : D.what₂.Tau) (lam0 : Fin n → ℤ), a.IsDual a' → a'.HWAt (Formalism.L2.embT D τ) lam0 →
        lam0 = (Bridge.lamLdef (D := D) n j τ).w) ∧
      (∀ (g : ReciprocityTheory.Aut.GQ D.host.E n), ∀ γ ∈ Formalism.L2.Theta.GQ V, finHom V γ = finHom V ((castFr hn P).ψ g) →
        ∀ v, eW (a.ρ g v) = c.ρ γ (eW v)) ∧
      (∀ x g, eW (Φ x g) = u.fn x (toGf (castFr hn P) g)) ∧
      (LinearIndependent ℂ fun k => Φ (Pi.single k 1)) ∧
      Submodule.span ℂ (Set.range fun k => Φ (Pi.single k 1)) =
        NG.TypeSp a.ρ (stdJ (datV D n hr' Pg Q Lv chi xi)) (stdX (datV D n hr' Pg Q Lv chi xi)) ∧
      ∀ B, NG.HypOutside (stdJ (datV D n hr' Pg Q Lv chi xi)) (stdX (datV D n hr' Pg Q Lv chi xi)) B →
        ∀ (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)) (k : ℕ), s.v ∉ B →
          Formalism.AUTREP.IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ n → ∀ x, ∃ x',
            Φ x' = NG.tN (stdJ (datV D n hr' Pg Q Lv chi xi)) s ϖ k (Φ x) ∧
            ∀ 𝔴 : HeightOneSpectrum (𝓞 D.what₂.LL), (∀ p : ℕ, p.Prime → s.Above p → (p : 𝓞 D.what₂.LL) ∉ 𝔴.asIdeal) →
              x ∈ u.nab → ∃ d : 𝓞 D.what₂.LL, d ∉ 𝔴.asIdeal ∧ d • x' ∈ u.nab := by
  subst hn
  subst hβ
  subst hLv
  obtain ⟨hbij, e, he⟩ := GlobalTheory.MtInRat.toGf_bij_ratIso D V P hg hP
  obtain ⟨alg, irr, hw⟩ := GlobalTheory.T.coefficientSpace_definiteForm_irreducibleAlgebraicWeight D V P e he c _ u.c0 u.map
  have hcut := @GlobalTheory.MtIn.lvlForm_adelic_basis (Bridge.Gf V) (Formalism.L2.Theta.GQ V) c.coef.W D.what₂.LL _ _ _ _ _ _ _ (Bridge.ratF V) u.S D.what₂.embLL
    c.coef.ρ _ _ u.pres _ _ u.G₀ _ _ u.act u.tie u.P₀ u.ψ₀⁻¹
  have hli := hcut.1
  have hsp := hcut.2.1
  clear hcut
  have hty := GlobalTheory.T.definiteLevelForms_iff_stdGroupTypeSpace D V hr Pg Q chi xi c P e hg hP he u.G₀ u.tie.red u.eG u.P₀ u.ψ₀ u.red
  have hk := GlobalTheory.T.heckeOperator_keeps_rational_integral_levelForms D V hr Pg Q chi xi c P e hg hs hP he alg irr u.G₀ u.S u.act u.pres u.tie u.eG u.P₀ u.ψ₀ u.red _ u.c0
    u.pair u.del u.map u.coef u.vals
  let T : (Bridge.Gf V → c.W) ≃ₗ[ℂ] (Formalism.AUTREP.GAf D.host.E V.rank → c.W) :=
    LinearEquiv.funCongrLeft ℂ c.W (Equiv.ofBijective _ hbij)
  refine ⟨{ W := c.W, ρ := wtRep c e, alg := alg, irr := irr }, LinearEquiv.refl _ _,
    T.toLinearMap.comp (u.pres.extL.comp (lvlFormL u.S u.act u.P₀ u.ψ₀⁻¹)), hw, ?_, fun _ _ => rfl, ?_, ?_, hk⟩
  · intro g γ hγ h v
    have h1 : Bridge.ratF V (e g) = Bridge.ratF V ⟨γ, hγ⟩ := (he g).1.trans (Subtype.ext h.symm)
    have h2 : e g = ⟨γ, hγ⟩ := GlobalTheory.FormInner.ratF_injective V h1
    change c.ρ (e g) v = c.ρ γ v
    rw [h2]
  · exact hli.map' T.toLinearMap T.ker
  · have h1 := @span_range_equiv (Bridge.Gf V → c.W) (Formalism.AUTREP.GAf D.host.E V.rank → c.W) (Fin u.dim) _ _ _ _ T
      (fun k => u.pres.ext (lvlForm u.S u.act u.P₀ u.ψ₀⁻¹ (Pi.single k 1)).1) _
      (NG.TypeSp (wtRep c e) (stdJ (datV D V.rank hr Pg Q (levPOf u.eG D.what₂.embLL u.P₀ u.ψ₀) chi xi))
        (stdX (datV D V.rank hr Pg Q (levPOf u.eG D.what₂.embLL u.P₀ u.ψ₀) chi xi))) hsp (fun F => hty F)
    exact h1

theorem rank_V (i : Fin D.R.m) : (Vc D i).rank = D.R.nV := D.sp.V_rank _ (Nat.le_add_left _ _) i.2

theorem eq_resChar (w : D.what₂.places.Pl) {p : ℕ} (hp : p.Prime) (h : (p : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal) :
    p = D.what₂.places.resChar w := by
  by_contra hne
  have hc := (Nat.coprime_primes hp (D.what₂.places.resChar_prime w)).2 hne
  obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.2 hc).map (Int.castRingHom (𝓞 D.what₂.LL))
  refine (D.plEq w).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
  rw [← hab]
  exact add_mem (Ideal.mul_mem_left _ _ (by simpa using h)) (Ideal.mul_mem_left _ _ (by simpa using Formalism.BasicNotions.resChar_mem D w))

theorem tup_read {μ : D.what₂.Tup} {i : Fin D.R.m} {c : CoefA (Vc D i)} {T : Type} {L : LevCh D T} {μ0 : T} (hL : L.Is μ0)
    (hPg : ∀ PP, PP ∈ L.Pg ↔ ∃ k v, PP = D.naut.plGw k v) (hβ : L.βV i = 1) {t : T}
    {ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ} (hψ : IsGenericPsi L.Pg ψ) (τ : TupIn μ i c L t ψ) (hg : (Vc D i).gram = 1)
    (hs : Seed.FrmC.StdLat (Vc D i)) {P : principalLevelFrame.RowPsi (Vc D i) (Vc D i).rank} (hP : UnitFr P) :
    ∃ (m : MtReal D μ ((i : ℕ) + 1)) (eW : m.wt.W ≃ₗ[ℂ] c.W), Good i m (L.C.mu0 i * L.xiH t) ∧
      (∀ (g : ReciprocityTheory.Aut.GQ D.host.E D.R.nV), ∀ γ ∈ Formalism.L2.Theta.GQ (Vc D i),
        finHom (Vc D i) γ = finHom (Vc D i) ((castFr (rank_V i) P).ψ g) → ∀ v, eW (m.wt.ρ g v) = c.ρ γ (eW v)) ∧
      ∀ x g, eW (m.real (D.what₂.jMt μ ((i : ℕ) + 1) (τ.e x)) g) = τ.u.fn x (toGf (castFr (rank_V i) P) g) := by
  have hr : D.R.r ≤ D.R.nV := (r_le_V i).trans (rank_V i).le
  obtain ⟨a, eW, Φ, hw, heq, hΦ, hli, hsp, hk⟩ := side_read (rank_V i) hβ hr τ.u hg hs hP _ τ.u.lev
  obtain ⟨r, rinj, rrange, hr'⟩ := constr_semi ((D.what₂.jMt μ ((i : ℕ) + 1)).comp τ.e.toLinearMap) Φ τ.li τ.span hli
  have hrj : ∀ x, r (D.what₂.jMt μ ((i : ℕ) + 1) (τ.e x)) = Φ x := hr'
  obtain ⟨-, hop, hhyp⟩ := GlobalTheory.T.stdFrameLevelSubgroup_bounded_open_hyperspecial D D.R.nV
    (datV D D.R.nV hr L.Pg (L.Q t) (P0 L.Pg D.R.r ψ) (L.chi ((i : ℕ) + 1)) (L.xiR t))
  have hB := hhyp (gPl D ∪ qPl D (L.C.mu0 i * L.xiH t)) (GlobalTheory.MtIn.Under.places_under D T L μ0 hL hPg i t)
  have hk' := hk _ hB
  let m : MtReal D μ ((i : ℕ) + 1) :=
    { wt := a
      J := stdJ (datV D D.R.nV hr L.Pg (L.Q t) (P0 L.Pg D.R.r ψ) (L.chi ((i : ℕ) + 1)) (L.xiR t))
      χ := stdX (datV D D.R.nV hr L.Pg (L.Q t) (P0 L.Pg D.R.r ψ) (L.chi ((i : ℕ) + 1)) (L.xiR t))
      J_open := hop
      real := r
      real_inj := rinj
      real_range := rrange.trans hsp }
  refine ⟨m, eW, ?_, heq, fun x g => ?_⟩
  · refine ⟨GlobalTheory.T.isProdLevel_stdFrame_twoBlockUnipotentLevel D _ hr _ _ ψ _ _, GlobalTheory.T.ramifiedLevel_eq_parahoric_with_tupleCharacter D T L μ0 hL hPg i t hr ψ, fun k v s hs' => ?_, hB, fun t' a' lam h1 h2 => ?_,
      fun s ϖ k h1 h2 h3 h4 x => ?_, fun w s ϖ k h1 h0 h2 h3 h4 y hy => ?_, fun y hy => ?_, (D.what₂.MtLat μ ((i : ℕ) + 1)).span_top⟩
    · exact GlobalTheory.T.levelUnipotent_genericChar_typePlace D T L μ0 hL hPg i t hr ψ hψ s ((hPg _).2 ⟨k, v, hs'⟩)
    · rw [hw a' t' lam h1 h2]
      exact GlobalTheory.Mem.WtPar.infOf_lamLdef_eq_paramV D i t'
    · obtain ⟨x, rfl⟩ := τ.e.surjective x
      obtain ⟨x', hx', -⟩ := hk' s ϖ k h1 h2 h3 h4 x
      refine ⟨τ.e x', ?_⟩
      change r _ = NG.tN _ s ϖ k (r _)
      rw [hrj, hrj]
      exact hx'
    · obtain ⟨x, rfl⟩ := τ.lat.1 y hy
      have hx : x ∈ τ.u.nab := by
        classical
        refine (τ.lat.2 x).2 ⟨fun v => if v = (D.what₂.jMt μ ((i : ℕ) + 1)).comp τ.e.toLinearMap x then 1 else 0, ?_⟩
        rw [Finset.sum_eq_single_of_mem _ hy]
        · simp
        · intro v _ hv
          simp only [if_neg hv]
          simp
      obtain ⟨x', hx', hd⟩ := hk' s ϖ k h1 h2 h3 h4 x
      obtain ⟨d, hd, hdx⟩ := hd (D.plEq w) (fun p hp ha hm => h0 (eq_resChar w hp hm ▸ ha)) hx
      obtain ⟨cc, hcc⟩ := (τ.lat.2 _).1 hdx
      have hd0 : (d : D.what₂.LL) ≠ 0 := fun h => hd (by
        have : d = 0 := Subtype.ext h
        rw [this]; exact zero_mem _)
      have hv : (D.plEq w).valuation D.what₂.LL (d : D.what₂.LL) = 1 :=
        (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := D.what₂.LL) (D.plEq w)).2 hd
      refine ⟨fun g => (d : D.what₂.LL)⁻¹ * (cc g : D.what₂.LL), fun g => ?_, ?_⟩
      · rw [D.val_nonneg_iff, map_mul, map_inv₀, hv, inv_one, one_mul]
        exact (D.plEq w).valuation_le_one (K := D.what₂.LL) (cc g)
      · have e1 : ∑ g ∈ (D.what₂.MtLat μ ((i : ℕ) + 1)).gen, D.what₂.embLL ((d : D.what₂.LL)⁻¹ * (cc g : D.what₂.LL)) • g =
            D.what₂.jMt μ ((i : ℕ) + 1) (τ.e x') := by
          simp only [map_mul, mul_smul]
          rw [← Finset.smul_sum, ← hcc, ← map_smulₛₗ]
          have : (d : D.what₂.LL)⁻¹ • (d • x') = x' := by
            change (d : D.what₂.LL)⁻¹ • ((d : D.what₂.LL) • x') = x'
            rw [inv_smul_smul₀ hd0]
          rw [this]
          rfl
        rw [e1]
        change NG.tN _ s ϖ k (r (D.what₂.jMt μ ((i : ℕ) + 1) (τ.e x))) = r _
        rw [hrj, hrj]
        exact hx'.symm
    · obtain ⟨x, rfl⟩ := τ.lat.1 y hy
      exact ⟨τ.e x, rfl⟩
  · change eW (r _ g) = _
    rw [hrj, hΦ]

section Fam

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type}

theorem fam_read (A : FamIn D.what₂.LL G Pl0 T D.R.m) {μ : D.what₂.Tup} {i : Fin D.R.m} {c : CoefA (Vc D i)} {L : LevCh D T} {μ0 : T}
    (hL : L.Is μ0) (hPg : ∀ PP, PP ∈ L.Pg ↔ ∃ k v, PP = D.naut.plGw k v) (hβ : L.βV i = 1) (t : T)
    {ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ} (hψ : IsGenericPsi L.Pg ψ) (hg : (Vc D i).gram = 1)
    (hs : Seed.FrmC.StdLat (Vc D i)) {P : principalLevelFrame.RowPsi (Vc D i) (Vc D i).rank} (hP : UnitFr P)
    (eG : G ≃* G0 L.Pg D.R.r) (P₀ : Subgroup G) (ψ₀ : P₀ →* D.what₂.LLˣ)
    (hlev : levPOf eG D.what₂.embLL P₀ ψ₀ = P0 L.Pg D.R.r ψ)
    (pres : Bridge.ClassPres (Bridge.ratF (Vc D i)) (A.MtCSD i t) D.what₂.embLL c.coef.ρ (levEnv (Vc D i) (L.βV i) (L.datVt i t)).J
      (levEnv (Vc D i) (L.βV i) (L.datVt i t)).χ)
    (tie : Bridge.ActTie (Bridge.ratF (Vc D i)) pres (levEnv (Vc D i) (L.βV i) (L.datVt i t)).Q
      (levEnv (Vc D i) (L.βV i) (L.datVt i t)).ch (A.leftGroupActionLift i t))
    (red : ∀ q : (levEnv (Vc D i) (L.βV i) (L.datVt i t)).Q, eG (tie.red q) =
      rTup (L.βV i) (L.datVt i t) (Formalism.UG.bc (swapAE D) ((q : Bridge.Gf (Vc D i)) : GL _ _)))
    (c0 : VV D.what₂.LL (fun τ => Bridge.lamLdef (D := D) (Vc D i).rank ((i : ℕ) + 1) τ) →ₛₗ[D.what₂.embLL] c.W) (pair del)
    (hmap : Bridge.CoefMapTie (Vc D i) c.coef c0 (rhoVr (labLL D) _))
    (hcoef : Bridge.CoefTie (Vc D i) c.coef pres _ c0 pair (nabAtr (labLL D) _) del)
    (vals : ∀ k : (levEnv (Vc D i) (L.βV i) (L.datVt i t)).J, ∃ z : 𝓞 D.what₂.LL,
      D.what₂.embLL (z : D.what₂.LL) = ((levEnv (Vc D i) (L.βV i) (L.datVt i t)).χ k : ℂ))
    (e : (Fin (lDim D A P₀ ψ₀ i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL μ ((i : ℕ) + 1))
    (li : LinearIndependent ℂ fun a => D.what₂.jMt μ ((i : ℕ) + 1) (e (Pi.single a 1)))
    (span : Submodule.span ℂ (Set.range fun a => D.what₂.jMt μ ((i : ℕ) + 1) (e (Pi.single a 1))) = ⊤)
    (lat : OLatTie D.what₂.embLL (D.what₂.MtLat μ ((i : ℕ) + 1)) ((D.what₂.jMt μ ((i : ℕ) + 1)).comp e.toLinearMap)
      (lNab D A P₀ ψ₀ i t)) :
    ∃ (m : MtReal D μ ((i : ℕ) + 1)) (eW : m.wt.W ≃ₗ[ℂ] c.W), Good i m (L.C.mu0 i * L.xiH t) ∧
      (∀ (g : ReciprocityTheory.Aut.GQ D.host.E D.R.nV), ∀ γ ∈ Formalism.L2.Theta.GQ (Vc D i),
        finHom (Vc D i) γ = finHom (Vc D i) ((castFr (rank_V i) P).ψ g) → ∀ v, eW (m.wt.ρ g v) = c.ρ γ (eW v)) ∧
      ∀ x g, eW (m.real (D.what₂.jMt μ ((i : ℕ) + 1) (e x)) g) =
        pres.ext (liftForm A P₀ ψ₀ i t x).1 (toGf (castFr (rank_V i) P) g) :=
  tup_read hL hPg hβ hψ
    { u :=
        { G₀ := G
          S := A.MtCSD i t
          act := A.leftGroupActionLift i t
          pres := pres
          tie := tie
          eG := eG
          P₀ := P₀
          ψ₀ := ψ₀
          red := red
          lev := hlev
          c0 := c0
          pair := pair
          del := del
          map := hmap
          coef := hcoef
          vals := vals }
      e := e
      li := li
      span := span
      lat := lat } hg hs hP

variable {I0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def Reads {R : RealDat D A3.A Ks} {F : Face D A3.A} {X0 : BaseLevelRowSide D} (Y : R3.Read (A3 := A3) R F X0)
    (PV : ∀ i : Fin D.R.m, principalLevelFrame.RowPsi (Vc D i) D.R.nV) {μ : D.what₂.Tup} (h : RecTie.Used0 D μ) (i : Fin D.R.m)
    (m : MtReal D μ ((i : ℕ) + 1)) (eW : m.wt.W ≃ₗ[ℂ] (R.cV i).W) : Prop :=
  (∀ (g : ReciprocityTheory.Aut.GQ D.host.E D.R.nV), ∀ γ ∈ Formalism.L2.Theta.GQ (Vc D i),
      finHom (Vc D i) γ = finHom (Vc D i) ((PV i).ψ g) → ∀ v, eW (m.wt.ρ g v) = (R.cV i).ρ γ (eW v)) ∧
    ∀ (x : D.what₂.Mt μ ((i : ℕ) + 1)) g, eW (m.real x g) = (Y.IL.jMt μ h i x).1 ((PV i).ψ g)

theorem used_read {R : RealDat D A3.A Ks} {F : Face D A3.A} {X0 : BaseLevelRowSide D} (Y : R3.Read (A3 := A3) R F X0) (hb : R.BaseW F)
    (hPg : ∀ PP, PP ∈ R.Pg ↔ ∃ k v, PP = D.naut.plGw k v) (hβ : ∀ i, R.βV i = 1) (hg : ∀ i, (Vc D i).gram = 1)
    (hs : ∀ i, Seed.FrmC.StdLat (Vc D i)) {P : ∀ i, principalLevelFrame.RowPsi (Vc D i) (Vc D i).rank} (hP : ∀ i, UnitFr (P i))
    (vals : ∀ i t (k : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).J), ∃ z : 𝓞 D.what₂.LL,
      D.what₂.embLL (z : D.what₂.LL) = ((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ k : ℂ))
    (t : T) (h : RecTie.Used0 D (Y.tup t)) (i : Fin D.R.m) :
    ∃ (m : MtReal D (Y.tup t) ((i : ℕ) + 1)) (eW : m.wt.W ≃ₗ[ℂ] (R.cV i).W), Good i m (R.C.mu0 i * R.xiH t) ∧
      Reads Y (fun i => castFr (rank_V i) (P i)) h i m eW := by
  obtain ⟨ψ, hψ, hlev, -⟩ := hb.grp.levels
  obtain ⟨gramR, c0R, c0L, htie⟩ := hb.fam.tie
  obtain ⟨m, eW, h1, h2, h3⟩ := fam_read A3.A hb.lev hPg (hβ i) t hψ (hg i) (hs i) (hP i) R.eG F.P0 F.ψ0 hlev (R.B.L i t).pres
    (R.B.L i t).act_tie (hb.grp.red_L i t) (c0L i) _ _ (htie.mapL i) (htie.coefL i t) (vals i t) (Y.eMt i t) (Y.formsL i t).li
    (Y.formsL i t).span (Y.latL i t)
  refine ⟨m, eW, h1, h2, fun x g => ?_⟩
  have key : ∀ y, eW (m.real (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t y)) g) =
      (Y.IL.jMt (Y.tup t) h i (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t y))).1 ((castFr (rank_V i) (P i)).ψ g) := fun y => by
    refine (h3 y g).trans (Eq.symm ((congrFun (Y.mtRead i t h y) _).trans ?_))
    have e1 := hb.models.jV i t (liftForm A3.A F.P0 F.ψ0 i t y)
    have e2 := (hb.models.cV i).1 _ (inv_mem ((castFr (rank_V i) (P i)).into g))
    change (R.cV i).ρ ((castFr (rank_V i) (P i)).ψ g)⁻¹ ((R.HV i t).e (R.jV i t (liftForm A3.A F.P0 F.ψ0 i t y)) _) = _
    rw [e1, e2]
    rfl
  let l1 : D.what₂.Mt (Y.tup t) ((i : ℕ) + 1) →ₗ[ℂ] (R.cV i).W := eW.toLinearMap ∘ₗ LinearMap.proj g ∘ₗ m.real
  let l2 : D.what₂.Mt (Y.tup t) ((i : ℕ) + 1) →ₗ[ℂ] (R.cV i).W :=
    LinearMap.proj ((castFr (rank_V i) (P i)).ψ g) ∘ₗ Submodule.subtype _ ∘ₗ (Y.IL.jMt (Y.tup t) h i).toLinearMap
  have e : l1 = l2 := LinearMap.ext_on_range (Y.formsL i t).span fun a => key _
  exact LinearMap.congr_fun e x

end Fam

theorem rat_castFr {V : HSp D} {n : ℕ} (hn : V.rank = n) (hg : V.gram = 1) {P : principalLevelFrame.RowPsi V V.rank} (hP : UnitFr P)
    (g : Formalism.AUTREP.GAf D.host.E n) : g ∈ ReciprocityTheory.Aut.GQ D.host.E n ↔
      ∃ γ ∈ Formalism.L2.Theta.GQ V, finHom V γ = finHom V ((castFr hn P).ψ g) := by
  subst hn
  obtain ⟨hbij, e, he⟩ := GlobalTheory.MtInRat.toGf_bij_ratIso D V P hg hP
  constructor
  · intro h
    exact ⟨(e ⟨g, h⟩).1, (e ⟨g, h⟩).2, congrArg Subtype.val (he ⟨g, h⟩).1⟩
  · rintro ⟨γ, hγ, h⟩
    obtain ⟨g', hg'⟩ := e.surjective ⟨γ, hγ⟩
    have h1 : toGf P g'.1 = toGf P g := (he g').1.symm.trans (by rw [hg']; exact Subtype.ext h)
    exact hbij.1 h1 ▸ g'.2

theorem std_castFr {V : HSp D} {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (hn : V.rank = n)
    {P : principalLevelFrame.RowPsi V V.rank} (h : StdFrame hF P) : StdFrame hF (castFr hn P) := by
  subst hn
  exact h

theorem tie_cast {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] {O : Type} [CommRing O] {φ : O →+* ℂ}
    {σ : K →+* ℂ} {m m' : Rw.Mat1 K G} {s : Rw.Sp1 O φ G} (h : m = m') (t : Rw.Tie1 σ m s) :
    ∃ e : (Fin m'.n → K) ≃ₗ[K] (Fin m.n → K), (LinearIndependent ℂ fun a => t.j (e (Pi.single a 1))) ∧
      Submodule.span ℂ (Set.range fun a => t.j (e (Pi.single a 1))) = ⊤ ∧ OLatTie σ s.lat (t.j.comp e.toLinearMap) m'.N := by
  subst h
  exact ⟨LinearEquiv.refl _ _, t.forms.li, t.forms.span, t.latT⟩

section Asm

variable {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {C : Formalism.L2.Pj.CoreJ D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat3 D A3 C.Q.c.F} {F : Face3 D A3} {X0 : BaseLevelRowSide D}

theorem inMt_of (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (cf : CharFrame D) (xi : D.what₂.Tup → HChar D.host.E)
    (Q : D.what₂.places.Pl → Finset (PlE D.host)) (PV : ∀ i : Fin D.R.m, principalLevelFrame.RowPsi (Vc D i) D.R.nV)
    (std : ∀ i, StdFrame Y.hF (PV i)) (hid : ∀ i, GlobalTheory.MtRead.IdFrame Y.hF (PV i))
    (rat : ∀ (i : Fin D.R.m) (g : Formalism.AUTREP.GAf D.host.E D.R.nV), g ∈ ReciprocityTheory.Aut.GQ D.host.E D.R.nV ↔
      ∃ γ ∈ Formalism.L2.Theta.GQ (Vc D i), finHom (Vc D i) γ = finHom (Vc D i) ((PV i).ψ g))
    (H : ∀ (μ : D.what₂.Tup) (i : Fin D.R.m), ∃ m : MtReal D μ ((i : ℕ) + 1), Good i m (cf.mu0 i * xi μ) ∧
      ∀ h : RecTie.Used0 D μ, ∃ eW, Reads Y PV h i m eW)
    (gen : ∀ w (j : Fin D.R.m) (v : PlE D.host) (k : ℕ) (s : ReciprocityTheory.Aut.SplitPlace D.host.E),
      GenAt D (D.what₂.places.resChar w) (Q w) v k → Formalism.BasicNotions.IsConjPl D.host v s.w →
      s.v ∉ gPl D ∪ qPl D (cf.mu0 j * xi (D.what₂.muTw w)) ∧ ¬ s.Above (D.what₂.places.resChar w)) :
    ∃ m : GlobalTheory.HeightCounting.InMt Y cf xi Q, m.ad.PV = PV := by
  choose mm hgood hread using H
  choose eW hW using hread
  let M : MtFam D := fun μ j h1 h2 => match j, h1, h2 with
    | k + 1, _, h2 => mm μ ⟨k, h2⟩
  refine ⟨⟨M, ⟨PV, std, fun μ h i => eW μ i h, fun μ h i => (hW μ i h).2, rat, fun μ h i => (hW μ i h).1, hid⟩,
    ⟨fun w j => (hgood _ j).prod, fun w j => (hgood _ j).para, fun w j => (hgood _ j).uni, fun w j => (hgood _ j).hyp,
      fun μ j => (hgood μ j).wt, fun w j v k s ϖ h1 h2 h3 => ?_, fun w j v k s ϖ _ h1 h2 h3 => ?_,
      fun w j _ => (hgood _ j).full⟩⟩, rfl⟩
  · exact (hgood _ j).rat s ϖ k (gen w j v k s h1 h2).1 h3 h1.2.2.2.2.1 h1.2.2.2.2.2
  · exact (hgood _ j).int w s ϖ k (gen w j v k s h1 h2).1 (gen w j v k s h1 h2).2 h3 h1.2.2.2.2.1 h1.2.2.2.2.2

end Asm

section Cols

open GlobalTheory.Mem.Col2

variable (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px)

theorem pg_iff {U : Set I.ι} {L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)} (hL : LevOf X I U L) (hg : GrpAt X I)
    (PP : Pl X.toD7.host.E) : PP ∈ L.Pg ↔ ∃ k v, PP = X.toD7.naut.plGw k v := by
  obtain ⟨plg, h⟩ := hg.pl
  rw [hL.Pg]
  constructor
  · intro hP
    obtain ⟨kv, e⟩ := plg.surjective ⟨PP, hP⟩
    exact ⟨kv.1, kv.2, (congrArg Subtype.val e).symm.trans (h kv).1⟩
  · rintro ⟨k, v, rfl⟩
    rw [← (h ⟨k, v⟩).1]
    exact (plg ⟨k, v⟩).2

theorem all_read (hX : X.B.fields.Ok) (hI : I.Ok) (hV : ValsIn I) (hg : GrpAt X I)
    {L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I Set.univ)} (hL : LevOf X I Set.univ L) (Xg : Finset (Gc X.B px → X.B.LL))
    (tr : TrI X.B px) (a : I.ι) (μ : X.toD7.what₂.Tup) (i : Fin X.toD7.R.m)
    {P : principalLevelFrame.RowPsi (Vc X.toD7 i) (Vc X.toD7 i).rank} (hP : UnitFr P)
    (e : (Fin (lDim X.toD7 (famR X I hX Set.univ Xg tr).A (lev0 I) (chr0 I) i (Top.Bl.tAll I a)) → X.toD7.what₂.LL) ≃ₗ[X.toD7.what₂.LL]
      X.toD7.what₂.MtL μ ((i : ℕ) + 1))
    (li : LinearIndependent ℂ fun a => X.toD7.what₂.jMt μ ((i : ℕ) + 1) (e (Pi.single a 1)))
    (span : Submodule.span ℂ (Set.range fun a => X.toD7.what₂.jMt μ ((i : ℕ) + 1) (e (Pi.single a 1))) = ⊤)
    (lat : OLatTie X.toD7.what₂.embLL (X.toD7.what₂.MtLat μ ((i : ℕ) + 1)) ((X.toD7.what₂.jMt μ ((i : ℕ) + 1)).comp e.toLinearMap)
      (lNab X.toD7 (famR X I hX Set.univ Xg tr).A (lev0 I) (chr0 I) i (Top.Bl.tAll I a))) :
    ∃ m : MtReal X.toD7 μ ((i : ℕ) + 1), Good i m ((Top.Fr.at X I.C).mu0 i * (show HChar X.toD7.host.E from I.xi a)) := by
  obtain ⟨eG, cG, Xg', hid, -, -, -, -, hrest⟩ := GlobalTheory.T.exists_finite_group_goodSet_levels_characters X px I hX Set.univ L hI hg hL
  obtain ⟨ψ, hψ, hlev, -⟩ := (hrest tr).2.1
  have hVP : ∀ i, (Vc X.toD7 i).IsPosDef := fun i => X.B.V_posDef _ (by omega) i.2
  choose cV c0 hcV hmap hin using fun i => GlobalTheory.CoefModel.exists_coef_lift X.toD7 i (hVP i)
  have hgr := GlobalTheory.Mem.R3.StdModel.gram_V X I hI i
  have hst : Seed.FrmC.StdLat (Vc X.toD7 i) := ((GlobalTheory.Mem.HostFrames.stdLat_diag (D := X.toD7) hI.spaces).1 _).2.1
  obtain ⟨s, hs, -⟩ := GlobalTheory.T.exists_liftForms_adelic_decoratedLattices X px I hX Set.univ Xg tr L eG hI hV hL hid cV i (c0 i) (hcV i) (hmap i) (hin i) (hL.beta.1 i)
    hgr hst
  obtain ⟨m, -, h1, -⟩ := fam_read (famR X I hX Set.univ Xg tr).A hL.is (pg_iff X I hL hg) (hL.beta.1 i) (Top.Bl.tAll I a) hψ hgr hst hP
    eG (lev0 I) (chr0 I) hlev (s _).pres (s _).act_tie (hs _).1 (c0 i) _ _ (hmap i) (hs _).2.1
    (GlobalTheory.MtIn.levChi_integral X px I _ L hI hL i _) e li span lat
  refine ⟨m, ?_⟩
  rw [hL.C, hL.xiH, ixOf_eq I (t := Top.Bl.tAll I a) rfl] at h1
  exact h1

end Cols

section State

open GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}

theorem selHalf_of (p : ColPin w) : SelHalf w.I := by
  intro a b P hP P' hP' hq
  obtain ⟨q, hq, hqP, hqP'⟩ := hq
  obtain ⟨v, -, rfl⟩ := (Formalism.L2.Col.mem_QE _ _ _).1 hP
  obtain ⟨v', -, rfl⟩ := (Formalism.L2.Col.mem_QE _ _ _).1 hP'
  have hab : ∀ v, (w.I.sel v).under (𝓞 B.host.F) = v := fun v => by
    have h := p.above v
    unfold Formalism.L2.Host.aboveF at h
    rw [Set.Finite.mem_toFinset] at h
    exact h
  have hmem : ∀ v, ((q : 𝓞 B.host.E) ∈ (w.I.sel v).asIdeal) → (q : 𝓞 B.host.F) ∈ v.asIdeal := fun v h => by
    rw [← hab v]
    show (q : 𝓞 B.host.F) ∈ (w.I.sel v).asIdeal.comap (algebraMap _ _)
    rw [Ideal.mem_comap, map_natCast]
    exact h
  have := p.half v v' q hq (hmem v hqP) (hmem v' hqP')
  exact congrArg HeightOneSpectrum.asIdeal this

variable {P : Pre2 K w} (x : St P)

theorem gen_state (v₀ : (Dof x).what₂.places.Pl) (j : Fin (Dof x).R.m) (v : PlE (Dof x).host) (k : ℕ)
    (s : ReciprocityTheory.Aut.SplitPlace (Dof x).host.E) (h1 : GenAt (Dof x) ((Dof x).what₂.places.resChar v₀) (QOf P v₀) v k)
    (h2 : Formalism.BasicNotions.IsConjPl (Dof x).host v s.w) :
    s.v ∉ gPl (Dof x) ∪ qPl (Dof x) ((cfOf x).mu0 j * (show HChar (Dof x).host.E from w.I.xi ((Dof x).what₂.muTw v₀))) ∧
      ¬ s.Above ((Dof x).what₂.places.resChar v₀) := by
  have e : w.I.xi ((Dof x).what₂.muTw v₀) = T.xiTw w.I.C v₀ :=
    (P.q.mu.tw v₀).trans (congrArg (fun g => T.xiTw g v₀) w.C_eq.symm)
  have hu : ∀ u, u ∉ QOf P v₀ → (T.psi v₀).UnrAt u := fun u hu => by
    unfold Up.QOf at hu
    split_ifs at hu with h
    · exact ((T.psi_is v₀).ram u).2 hu
    · rw [P.supp v₀ h]
      exact fun _ _ => rfl
  rw [e]
  exact GlobalTheory.MtIn.GenOff.gen_off_level (Dof x) (cfOf x) _ (QOf P v₀) (T.psi v₀) hu (T.psi_is v₀).triv j v k s h1 h2

theorem real_state (pin : ColPin w) {Fm : ∀ i, principalLevelFrame.RowPsi (Vc (Dof x) i) (Vc (Dof x) i).rank} (hF : ∀ i, UnitFr (Fm i))
    (μ : (Dof x).what₂.Tup) (i : Fin (Dof x).R.m) :
    ∃ m : MtReal (Dof x) μ ((i : ℕ) + 1), Good i m ((cfOf x).mu0 i * (show HChar (Dof x).host.E from w.I.xi μ)) ∧
      ∀ h : RecTie.Used0 (Dof x) μ, ∃ eW, Reads x.r.Y (fun i => castFr (rank_V i) (Fm i)) h i m eW := by
  by_cases h : RecTie.Used0 (Dof x) μ
  · obtain ⟨t, rfl⟩ : ∃ t, x.r.Y.tup t = μ := ⟨_, x.r.Y.tupTie μ h⟩
    obtain ⟨m, eW, h1, h2⟩ := used_read x.r.Y x.m.z.pins.char.base (pg_iff (w.st x.o.Z) w.I x.m.z.lev x.fits.grpAt) x.m.z.lev.beta.1
      (GlobalTheory.Mem.R3.StdModel.gram_V (w.st x.o.Z) w.I w.ok)
      (fun i => ((GlobalTheory.Mem.HostFrames.stdLat_diag (D := Dof x) w.ok.spaces).1 _).2.1) hF
      (GlobalTheory.MtIn.levChi_integral (w.st x.o.Z) w.px w.I _ _ w.ok x.m.z.lev) t h i
    refine ⟨m, ?_, fun _ => ⟨eW, h2⟩⟩
    have e1 : x.m.z.R.C = cfOf x := x.m.z.lev.C
    have e2 : x.m.z.R.xiH t = w.I.xi (x.r.Y.tup t) :=
      (x.m.z.lev.xiH t).trans (congrArg w.I.xi ((congrFun x.r.tup t).trans (x.m.tup t)).symm)
    rw [e1, e2] at h1
    exact h1
  · obtain ⟨L, hL⟩ := GlobalTheory.MtIn.LevAll.exists_levOf_all (w.st x.o.Z) w.px w.I w.ok (selHalf_of pin) _ _ x.m.z.lev Set.univ
    have hm : P.q.p.mL μ ((i : ℕ) + 1) = lMat (D := Dof x) (famR (w.st x.o.Z) w.I P.hX Set.univ P.z.Xg P.z.tr).A (lev0 w.I) (chr0 w.I) i
        (tAll w.I μ) := by
      refine (P.q.mL μ _).trans ?_
      unfold mLU
      rw [dite_eq_left ⟨by omega, i.2⟩]
      rfl
    obtain ⟨e, li, span, lat⟩ := tie_cast hm (P.q.p.tL μ ((i : ℕ) + 1))
    obtain ⟨m, h1⟩ := all_read (w.st x.o.Z) w.I P.hX w.ok ⟨pin.vals, pin.roots⟩ x.fits.grpAt hL P.z.Xg P.z.tr μ μ i (hF i) e li span lat
    exact ⟨m, h1, fun h' => absurd h' h⟩

theorem inMt_state (pin : ColPin w) :
    ∃ m : InMt x.r.Y (cfOf x) w.I.xi (QOf P), ∀ i, GlobalTheory.MtRead.IdFrame x.r.Y.hF (m.ad.PV i) := by
  have hg := GlobalTheory.Mem.R3.StdModel.gram_V (w.st x.o.Z) w.I w.ok
  choose Fm hstd hF using fun i => GlobalTheory.MtIn.exists_unit_frame (Dof x) (Vc (Dof x) i) x.r.Y.hF (hg i)
    ((GlobalTheory.Mem.HostFrames.stdLat_diag (D := Dof x) w.ok.spaces).1 _).2.1
  obtain ⟨m, hm⟩ := inMt_of x.r.Y (cfOf x) w.I.xi (QOf P) (fun i => castFr (rank_V i) (Fm i))
    (fun i => std_castFr _ _ (hstd i)) (fun i => idFrame_castFr _ _ (hF i)) (fun i => rat_castFr _ (hg i) (hF i))
    (real_state x pin hF) (gen_state x)
  refine ⟨m, fun i => ?_⟩
  rw [hm]
  exact idFrame_castFr _ _ (hF i)

theorem sMt : SMt := by
  unfold SMt
  apply StepW.of_all
  intro K B f T w hK hF hs P x
  exact hs.1.elim fun pin => (inMt_state x pin).elim fun m _ => ⟨m⟩

end State

end GlobalTheory.MtId

end
