module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UntiltIterateSymmEpsilon
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SchwartzBruhatMajorants.ExistsSchwartzBruhatPiMajorant
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneAddInvPowMulRpowLe
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.UnitTestFunctions.TestFun
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.MirGen
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SiegelOneDescent.SgOneOfParts
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinScalingLaw
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JCh
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GoodFunctionLineDerivative
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapScalarVal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TriangularLowerRightDiag
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsParComap
public import GroundTheory.IdeleRoots.TorusPowers.HeckeIdem
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TubeChainHolds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaDecompositionStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrossingOfWallsAndHeights
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GalleryOfTubesAndCrossing
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviQuotientOfBlockDet
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConvergenceGroupOfBlockDet
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SphericalTestFunctionExists
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSymmUnitaryChart
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelEisensteinMultiplicativity

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TransferOfSectionAndWallLaws
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TransferOfSectionAndWallLaws
noncomputable section

open Filter Topology PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.RgTransfer

theorem transfer : SecLaw → WallLaw → Transfer := by
  intro hSec hWall G _ _ _ _ _ W _ _ _ K ρ hK hρ G' _ _ _ _ _ Γ Q S P₁ P₂ Γ' K' S' P₁' P₂' π ι c₀ c c'
    η₁ η₂ β ξ η₁' η₂' β' ξ' N hK' hL hS hP₁ hP₂ hS' hR₁ hR₂ hη₁ hη₂ hβ hp₁ hp₂ hpβ hpξ
  have hcont := resRep_cont hL hρ
  have c1 : c' 1 = 1 := isCh_one hR₁.ch
  have corr : ∀ {P : Subgroup G} {P' : Subgroup G'}, IsPull Q P P' π c₀ c c' →
      Corr ρ (secSp K P c ρ) (secSp K' P' c' (resRep hL ρ)) :=
    fun h w => mem_secSp_iff hL h c1 ρ w
  have lawG : ∀ {P : Subgroup G} {P' : Subgroup G'}, IsPull Q P P' π c₀ c c' →
      IsPar Γ' K' P' c' → Law K P c ρ :=
    fun h hp => (hSec G W K ρ hK hρ (Γ ⊓ Q) _ c (isPar_pull hL h hp)).1
  have lawG' : ∀ {P' : Subgroup G'}, IsPar Γ' K' P' c' → Law K' P' c' (resRep hL ρ) :=
    fun hp => (hSec G' _ K' (resRep hL ρ) hK' hcont Γ' _ c' hp).1
  obtain ⟨M₁, bd₁⟩ := (hSec G' _ K' (resRep hL ρ) hK' hcont Γ' _ c' hR₁).2.2
  obtain ⟨M₂, bd₂⟩ := (hSec G' _ K' (resRep hL ρ) hK' hcont Γ' _ c' hR₂).2.2
  have equi : ∀ {L' : Submodule ℂ (fixSp K Q π c₀ ρ)} {R : ℝ} {D : ℂ → ℂ}
      {Op' : ℂ → (L' →L[ℂ] secSp K' P₂' c' (resRep hL ρ))}
      {H' : ℂ → G' → (L' →L[ℂ] fixSp K Q π c₀ ρ)},
      Wall Γ' K' P₁' P₂' c' η₁' η₂' β' (resRep hL ρ) L' R D Op' H' →
      ∀ z (g : G') (k : K') (w : L'), H' z (g * k) w = resRep hL ρ k⁻¹ (H' z g w) :=
    fun hw => (hWall G' _ K' (resRep hL ρ) hK' hcont Γ' P₁' P₂' c' η₁' η₂' β' _ _ _ _ _ hR₁ hR₂
      hη₁ hη₂ hβ hw).2.1
  have key : ∀ {L : Submodule ℂ W} {L' : Submodule ℂ (fixSp K Q π c₀ ρ)} (hLL : Corr ρ L L')
      {R : ℝ} {D : ℂ → ℂ} {Op' : ℂ → (L' →L[ℂ] secSp K' P₂' c' (resRep hL ρ))}
      {H' : ℂ → G' → (L' →L[ℂ] fixSp K Q π c₀ ρ)},
      Wall Γ' K' P₁' P₂' c' η₁' η₂' β' (resRep hL ρ) L' R D Op' H' →
      Wall (Γ ⊓ Q) K P₁ P₂ c η₁ η₂ β ρ L R D (fun z => cj (corrE hLL) (corrE (corr hP₂)) (Op' z))
        (hOf hL ρ (corrE hLL) H') :=
    fun hLL _ _ _ _ hw => wall_pull hK hL hρ hP₁ hP₂ hR₁ hR₂ hη₁ hη₂ hβ hp₁ hp₂ hpβ (lawG hP₁ hR₁)
      (lawG hP₂ hR₂) (lawG' hR₁) (lawG' hR₂) bd₁ bd₂ hLL (corr hP₁) (corr hP₂) hw (equi hw)
  have hCS := corr hS
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · obtain ⟨R, D, Op', H', hw⟩ := h _ (resRep hL ρ) hcont
    exact ⟨R, D, _, _, key (corr hP₁) hw⟩
  · obtain ⟨R, D, Op', H', hw, ⟨a, ha, hH0⟩, O', hO, hOp⟩ := h _ (resRep hL ρ) hcont
    refine ⟨R, D, _, _, key hCS hw, ⟨a, ha, fun g w => ?_⟩,
      fun z => cj (corrE hCS) (corrE (corr hP₂)) (O' z),
      leftGood_comp (cj (corrE hCS) (corrE (corr hP₂))) hO, fun z hz => ?_⟩
    · obtain ⟨q, k, rfl⟩ := exists_qk hL g
      rw [hOf_eq hL ρ _ (equi hw), hH0, map_smul]
      have := sec_pull hL hS hS'.iwa (lawG hS hS') (lawG' hS') (corrE hCS w).2 w.2 q k
      exact congrArg (fun u => a • u) this.symm
    · show cj (corrE hCS) (corrE (corr hP₂)) (Op' z) = z • cj (corrE hCS) (corrE (corr hP₂)) (O' z)
      rw [hOp z hz, map_smul]
  · obtain ⟨R, D, Op', H', hw, hd, T', hT⟩ := h _ (resRep hL ρ) hcont
    refine ⟨R, D, _, _, key (corr hP₁) hw, hd, cj (corrE (corr hP₁)) (corrE hCS) T', fun g w => ?_⟩
    obtain ⟨q, k, rfl⟩ := exists_qk hL g
    rw [hOf_eq hL ρ _ (equi hw), hT, map_smul, hpξ q k k.2]
    have := sec_pull hL hS hS'.iwa (lawG hS hS') (lawG' hS') (T' (corrE (corr hP₁) w)).2
      (cj (corrE (corr hP₁)) (corrE hCS) T' w).2 q k
    exact congrArg (fun u => Complex.exp (ξ' (π q)) • u) this.symm

end GlobalTheory.CompanionTheory.RgTransfer
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TransferOfSectionAndWallLawsStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transfer_of_section_and_wall_laws : PositivityTheory.RgEis.SecLaw → PositivityTheory.RgEis.WallLaw → PositivityTheory.RgEis.Transfer := by
  first | exact @GlobalTheory.CompanionTheory.RgTransfer.transfer | exact GlobalTheory.CompanionTheory.RgTransfer.transfer | (intros; apply GlobalTheory.CompanionTheory.RgTransfer.transfer <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdentityTubeHolds
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdentityTubeHolds
open Filter Topology PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.Eis

theorem tube_isOpen {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) : IsOpen (tube Ω) := by
  have hc : Continuous fun l : ℂ × ℂ => (l.1.re, l.2.re) :=
    (Complex.continuous_re.comp continuous_fst).prodMk (Complex.continuous_re.comp continuous_snd)
  exact hc.isOpen_preimage Ω hΩ

theorem line_tube_convex {Ω : Set (ℝ × ℝ)} (hc : Convex ℝ Ω) (p v : ℂ × ℂ) :
    Convex ℝ {τ : ℂ | p + τ • v ∈ tube Ω} := by
  intro x hx y hy a b ha hb hab
  have key := hc hx hy ha hb hab
  simp only [tube, Set.mem_ofPred_eq] at hx hy key ⊢
  convert key using 1
  ext
  · simp only [Prod.fst_add, Prod.smul_fst, Complex.add_re, smul_eq_mul, Complex.real_smul,
      Complex.mul_re, Complex.mul_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Prod.fst_add, Prod.smul_mk, Prod.mk_add_mk]
    linear_combination (-p.1.re) * hab
  · simp only [Prod.snd_add, Prod.smul_snd, Complex.add_re, smul_eq_mul, Complex.real_smul,
      Complex.mul_re, Complex.mul_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Prod.smul_mk, Prod.mk_add_mk]
    linear_combination (-p.2.re) * hab

theorem idTube : IdTube := by
  intro X _ _ _ Ω Ω' F F' hΩ hc hΩ' hne hsub hF hF' heq z hz
  obtain ⟨ω, hω⟩ := hne
  set z0 : ℂ × ℂ := ((ω.1 : ℂ), (ω.2 : ℂ)) with hz0
  have hz0' : z0 ∈ tube Ω' := by simpa [tube, hz0] using hω
  have hline : Continuous fun τ : ℂ => z0 + τ • (z - z0) := by fun_prop
  have hDo : IsOpen {τ : ℂ | z0 + τ • (z - z0) ∈ tube Ω} := (tube_isOpen hΩ).preimage hline
  have hDc : Convex ℝ {τ : ℂ | z0 + τ • (z - z0) ∈ tube Ω} := line_tube_convex hc z0 (z - z0)
  have h0 : (0 : ℂ) ∈ {τ : ℂ | z0 + τ • (z - z0) ∈ tube Ω} := by
    show z0 + (0 : ℂ) • (z - z0) ∈ tube Ω
    rw [zero_smul, add_zero]
    exact hsub hz0'
  have h1 : (1 : ℂ) ∈ {τ : ℂ | z0 + τ • (z - z0) ∈ tube Ω} := by simpa using hz
  have hA := (hF z0 (z - z0)).analyticOnNhd hDo
  have hA' := (hF' z0 (z - z0)).analyticOnNhd hDo
  have hev : (fun τ : ℂ => F (z0 + τ • (z - z0))) =ᶠ[𝓝 0] (fun τ : ℂ => F' (z0 + τ • (z - z0))) := by
    have hO' : IsOpen {τ : ℂ | z0 + τ • (z - z0) ∈ tube Ω'} := (tube_isOpen hΩ').preimage hline
    filter_upwards [hO'.mem_nhds (by simpa using hz0')] with τ hτ
    exact heq hτ
  have := hA.eqOn_of_preconnected_of_eventuallyEq hA' hDc.isPreconnected h0 hev h1
  simpa using this

end GlobalTheory.CompanionTheory.Eis
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdentityTubeHoldsStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.identity_tube_holds : PositivityTheory.RgEis.IdTube := by
  first | exact @GlobalTheory.CompanionTheory.Eis.idTube | exact GlobalTheory.CompanionTheory.Eis.idTube | (intros; apply GlobalTheory.CompanionTheory.Eis.idTube <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightLipschitzHolds
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightLipschitzHolds
namespace GlobalTheory.CompanionTheory.RgEis

open PositivityTheory.RgEis

theorem htLip : PositivityTheory.RgEis.HtLip := by
  intro G _ _ _ Γ K P η hK hI hη C hC
  obtain ⟨M, hM⟩ := (hK.mul hC).exists_bound_of_continuousOn hη.cont.continuousOn
  refine ⟨M, fun g u hu => ?_⟩
  obtain ⟨p, hp, k, hk, rfl⟩ := hI g
  have h1 : η (p * k * u) = η p + η (k * u) := by
    rw [mul_assoc]; exact hη.left p hp _
  have h2 : η (p * k) = η p + η k := hη.left p hp k
  have h3 : η (1 : G) = 0 := by
    have := hη.left 1 P.one_mem 1
    simp only [mul_one] at this
    linarith
  have h4 : η k = 0 := by
    have := hη.right 1 k hk
    rw [one_mul] at this
    rw [this, h3]
  have h5 := hM (k * u) (Set.mul_mem_mul hk hu)
  rw [Real.norm_eq_abs] at h5
  rw [h1, h2, h4]
  simpa using h5

end GlobalTheory.CompanionTheory.RgEis
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightLipschitzHoldsStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_lipschitz_holds : PositivityTheory.RgEis.HtLip := by
  first | exact @GlobalTheory.CompanionTheory.RgEis.htLip | exact GlobalTheory.CompanionTheory.RgEis.htLip | (intros; apply GlobalTheory.CompanionTheory.RgEis.htLip <;> assumption)
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SchwartzBruhatMajorants.SgOneHd
section -- merged from Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SchwartzBruhatMajorants.BlgOfDict
open PositivityTheory.RgEis PositivityTheory.RgEis.So
open NumberField
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.RgEisSo.Hd

theorem blg_of_dict : Dict → BLg := by
  intro hD F E _ _ _ _ _ σ χ c hσ _ _ _
  obtain ⟨-, -, -, -, h5⟩ := hD F E
  have key : ∀ x : (IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))ˣ, (adCM σ χ).lg x =
      Real.log (GlobalTheory.Doubling.absE F E x : ℝ) := fun x => by
    show Real.log (GroundTheory.Global.IdeleGroup.ideleModule E (Units.map (eqv F E).toRingHom.toMonoidHom x) : ℝ) = _
    rw [h5]
  refine ⟨fun x => ?_, fun x => ?_⟩
  · have e : Units.map (eqv F E).toRingHom.toMonoidHom (Units.map (nuCM F E).toMonoidHom x) =
        GroundTheory.Global.ideleEmbedding F E x := by
      apply Units.ext
      exact GroundTheory.BlockD.ThmBHecke.adeleEquiv_algebraMap (x : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)
    show Real.log (GroundTheory.Global.IdeleGroup.ideleModule E (Units.map (eqv F E).toRingHom.toMonoidHom (Units.map (nuCM F E).toMonoidHom x)) : ℝ) =
      2 * Real.log (GroundTheory.Global.IdeleGroup.ideleModule F x : ℝ)
    rw [e, ← GroundTheory.Automorphic.EllipticTorus.ideleModule_ideleNorm (K := F),
      GroundTheory.Global.ideleNorm_ideleEmbedding, hσ.2.2.1, map_pow]
    have : (((GroundTheory.Global.IdeleGroup.ideleModule F x) ^ 2 : {r : ℝ // 0 < r}) : ℝ) =
      (GroundTheory.Global.IdeleGroup.ideleModule F x : ℝ) ^ 2 := rfl
    rw [this, Real.log_pow]
    norm_num
  · rw [key, key]
    have e : Units.map (adCM σ χ).σ.toMonoidHom x = GlobalTheory.Doubling.conjUnit σ x := by
      apply Units.ext
      rfl
    rw [e, GlobalTheory.Doubling.absE_conjUnit]
end GlobalTheory.CompanionTheory.RgEisSo.Hd
end

namespace PositivityTheory.RgEis.So

theorem sgOne_hd : SecLaw → WallLaw → Scale → StdGood → Dict → DictInf → CMGood → GrpTop → BdetLaw → ExtLaw → ParLaw →
    MirGen → SgOne := fun sl _ sc sg dict _ cg gt bl el pl mg =>
  have jt := GlobalTheory.CompanionTheory.EisSo.jtop
  have jc := GlobalTheory.CompanionTheory.RgEisSo.jcpt sg gt jt
  have ji := GlobalTheory.CompanionTheory.RgEisSo.JIwaAd.jiwa sg
  have jch := GlobalTheory.CompanionTheory.EisSo.jCh sg bl jt
  sgOne_of_parts
    (GlobalTheory.CompanionTheory.SgOneBase.baseCM cg GlobalTheory.CompanionTheory.RgEisFix.bFix GlobalTheory.CompanionTheory.EisBrat.brat GlobalTheory.CompanionTheory.RgEisBInt.bInt GlobalTheory.CompanionTheory.RgEisSo.bInf (GlobalTheory.CompanionTheory.RgEisSo.Hd.blg_of_dict dict) GlobalTheory.CompanionTheory.CMDelta.bDel)
    GlobalTheory.CompanionTheory.RgEis.Cover.jEx jt jc GlobalTheory.CompanionTheory.EisJ.jPar ji GlobalTheory.CompanionTheory.RgEisJRat.jRat (GlobalTheory.CompanionTheory.EisSec.jSec_of_top jt) jch
    (GlobalTheory.CompanionTheory.EisJMir.jmir sg gt bl el pl jt jc GlobalTheory.CompanionTheory.EisJ.jPar ji GlobalTheory.CompanionTheory.RgEisJRat.jRat jch) (GlobalTheory.CompanionTheory.RgDescendWall.descend2 sl) (GlobalTheory.CompanionTheory.RgEisTwist.twist sl) sc cg gt pl mg

end PositivityTheory.RgEis.So
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SchwartzBruhatMajorants.ContinuousOnThetaCFunLtr
section -- merged from Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SchwartzBruhatMajorants.ThetaCIntegrandMulDiagonalToNormOne
open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open PositivityTheory.He2M1 GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix IdeleGroup PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.AdelicThetaSeries.Hd

variable {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem thetaC_scalC_diagonal_mul (F : (ι → 𝔸[k]) → ℂ) (δ : kˣ) (a : IdeleGroup k) :
    thetaC F (scalC (diagonal k δ * a)) = thetaC F (scalC a) := by
  unfold thetaC
  have hv : ∀ ξ : ι → k, ((scalC (IdeleGroup.diagonal k δ * a) : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ ratV ξ
      = ((scalC a : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ ratV (δ • ξ) := by
    intro ξ
    funext i
    simp [scalC, ratV, Matrix.mulVec, dotProduct, Matrix.diagonal_apply, IdeleGroup.diagonal,
      Units.smul_def, mul_comm, mul_left_comm]
  simp_rw [hv]
  exact (MulAction.toPerm δ).tsum_eq (fun ξ => F (((scalC a : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ ratV ξ))

noncomputable def thetaCIntegrand (w : InfinitePlace k) (F : (ι → 𝔸[k]) → ℂ)
    (ω : HeckeCharacter k) (t : {r : ℝ // 0 < r}) (u : normOneSubgroup k) : ℂ :=
  thetaC F (scalC (moduleSection w t * (u : IdeleGroup k))) * (ω.toIdele (u : IdeleGroup k) : ℂ)

theorem thetaCIntegrand_mul_diagonalToNormOne (w : InfinitePlace k) (F : (ι → 𝔸[k]) → ℂ)
    (ω : HeckeCharacter k) (t : {r : ℝ // 0 < r}) (ξ : kˣ) (u : normOneSubgroup k) :
    thetaCIntegrand w F ω t (u * diagonalToNormOne k ξ) = thetaCIntegrand w F ω t u := by
  unfold thetaCIntegrand
  have hc : ((u * diagonalToNormOne k ξ : normOneSubgroup k) : IdeleGroup k) =
      IdeleGroup.diagonal k ξ * (u : IdeleGroup k) := by
    rw [Subgroup.coe_mul, mul_comm]
    rfl
  rw [hc, ← mul_assoc, mul_comm (moduleSection w t), mul_assoc, thetaC_scalC_diagonal_mul, map_mul,
    HeckeCharacter.toIdele_diagonal, one_mul]

theorem thetaCIntegrand_inv (w : InfinitePlace k) {F : (ι → 𝔸[k]) → ℂ}
    (hF : F ∈ schwartzBruhatPi (K := k) (ι := ι)) (ω : HeckeCharacter k) (t : {r : ℝ // 0 < r})
    (u : normOneSubgroup k) :
    thetaCIntegrand w F ω t⁻¹ u =
      ((t : ℝ) : ℂ) ^ Fintype.card ι * thetaCIntegrand w (adelicFourierPi k F) ω⁻¹ t u⁻¹ := by
  unfold thetaCIntegrand
  rw [EpsteinRankN.Hd.thetaC_scalC_eq hF]
  have e1 : (moduleSection w t⁻¹ * (u : IdeleGroup k))⁻¹ =
      moduleSection w t * ((u⁻¹ : normOneSubgroup k) : IdeleGroup k) := by
    rw [map_inv, mul_inv, inv_inv, Subgroup.coe_inv, mul_comm]
  have e2 : ideleModule k (moduleSection w t⁻¹ * (u : IdeleGroup k)) = t⁻¹ := by
    rw [map_mul, ideleModule_moduleSection, MonoidHom.mem_ker.mp u.2, mul_one]
  have e3 : (((ω⁻¹).toIdele ((u⁻¹ : normOneSubgroup k) : IdeleGroup k) : ℂ)) =
      ((ω.toIdele (u : IdeleGroup k) : ℂ)) := by
    have h : ∀ x, (ω⁻¹) x = (ω x)⁻¹ := fun x => rfl
    simp [HeckeCharacter.toIdele, h]
  rw [e1, e2, e3]
  have e4 : ((t⁻¹ : {r : ℝ // 0 < r}) : ℝ) = (t : ℝ)⁻¹ := by simp
  rw [e4]
  push_cast
  rw [inv_pow, inv_inv]
  ring

theorem theta_integral_functional_equation (w : InfinitePlace k) {F : (ι → 𝔸[k]) → ℂ}
    (hF : F ∈ schwartzBruhatPi (K := k) (ι := ι)) (ω : HeckeCharacter k) (t : {r : ℝ // 0 < r}) :
    thetaCInt w F ω t⁻¹ =
      ((t : ℝ) : ℂ) ^ Fintype.card ι * thetaCInt w (adelicFourierPi k F) ω⁻¹ t := by
  have hD := isFundamentalDomain_normOneFundamentalDomain k (normOneMeasure k)
  have hDinv : IsFundamentalDomain (↥(diagonalNormOne k).op)
      ((fun x => x⁻¹) ⁻¹' normOneFundamentalDomain k) (normOneMeasure k) := by
    refine hD.preimage_of_equiv
      (Measure.measurePreserving_inv (normOneMeasure k)).quasiMeasurePreserving
      inv_involutive.bijective (fun g x => ?_)
    show (g⁻¹ • x)⁻¹ = g • x⁻¹
    rw [Subgroup.smul_def, Subgroup.smul_def, MulOpposite.smul_eq_mul_unop,
      MulOpposite.smul_eq_mul_unop, Subgroup.coe_inv, MulOpposite.unop_inv, _root_.mul_inv_rev,
      inv_inv]
    exact mul_comm _ _
  have hinvar : ∀ (g : ↥(diagonalNormOne k).op) (x : normOneSubgroup k),
      thetaCIntegrand w (adelicFourierPi k F) ω⁻¹ t (g • x) =
        thetaCIntegrand w (adelicFourierPi k F) ω⁻¹ t x := by
    intro g x
    have hm : MulOpposite.unop (g : (normOneSubgroup k)ᵐᵒᵖ) ∈ diagonalNormOne k := g.2
    obtain ⟨ξ, hξ⟩ := MonoidHom.mem_range.mp (Subgroup.mem_subgroupOf.mp hm)
    have hg : MulOpposite.unop (g : (normOneSubgroup k)ᵐᵒᵖ) = diagonalToNormOne k ξ :=
      Subtype.ext hξ.symm
    rw [Subgroup.smul_def, MulOpposite.smul_eq_mul_unop, hg, thetaCIntegrand_mul_diagonalToNormOne]
  have hms := measurableSet_normOneFundamentalDomain (K := k)
  have step1 : thetaCInt w F ω t⁻¹ = ((t : ℝ) : ℂ) ^ Fintype.card ι *
      ∫ u in normOneFundamentalDomain k,
        thetaCIntegrand w (adelicFourierPi k F) ω⁻¹ t u⁻¹ ∂normOneMeasure k := by
    show ∫ u in normOneFundamentalDomain k, thetaCIntegrand w F ω t⁻¹ u ∂normOneMeasure k = _
    rw [← integral_const_mul]
    refine setIntegral_congr_fun hms (fun u _ => ?_)
    exact thetaCIntegrand_inv w hF ω t u
  have step2 : ∫ u in normOneFundamentalDomain k,
        thetaCIntegrand w (adelicFourierPi k F) ω⁻¹ t u⁻¹ ∂normOneMeasure k =
      ∫ u in (fun x => x⁻¹) ⁻¹' normOneFundamentalDomain k,
        thetaCIntegrand w (adelicFourierPi k F) ω⁻¹ t u ∂normOneMeasure k := by
    rw [← integral_indicator hms, ← integral_indicator (hms.preimage measurable_inv),
      ← integral_inv_eq_self (fun u => ((fun x => x⁻¹) ⁻¹' normOneFundamentalDomain k).indicator
        (thetaCIntegrand w (adelicFourierPi k F) ω⁻¹ t) u) (normOneMeasure k)]
    congr 1
  rw [step1, step2, hDinv.setIntegral_eq hD hinvar]
  rfl

theorem thetaCInt_inv : ∀ {k : Type} [Field k] [NumberField k], ∀ {ι : Type} [Fintype ι]
    [DecidableEq ι], ∀ (w : InfinitePlace k) {F : (ι → 𝔸[k]) → ℂ} (hF : F ∈ schwartzBruhatPi (K := k) (ι := ι))
    (ω : HeckeCharacter k) (t : {r : ℝ // 0 < r}), thetaCInt w F ω t⁻¹ =
      ((t : ℝ) : ℂ) ^ Fintype.card ι * thetaCInt w (adelicFourierPi k F) ω⁻¹ t :=
  fun w _ hF ω t ↦ theta_integral_functional_equation w hF ω t

end GlobalTheory.CompanionTheory.AdelicThetaSeries.Hd
end

open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.EpsteinMain.Hd

open PositivityTheory.He2M1 GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
  GroundTheory.Automorphic.GodementSection IdeleGroup PositivityTheory.RgEis Set Asymptotics

variable {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def detMod (A : GL ι 𝔸[k]) : ℝ :=
  (ideleModule k (Matrix.GeneralLinearGroup.det A) : ℝ)

theorem detMod_pos (A : GL ι 𝔸[k]) : 0 < detMod A := (ideleModule k _).2

theorem detMod_inv (A : GL ι 𝔸[k]) : detMod A⁻¹ = (detMod A)⁻¹ := by
  simp [detMod, map_inv]

theorem det_tInv (A : GL ι 𝔸[k]) :
    Matrix.GeneralLinearGroup.det (tInv A) = (Matrix.GeneralLinearGroup.det A)⁻¹ := by
  rw [← map_inv]
  ext1
  simp [tInv, Matrix.GeneralLinearGroup.det, Matrix.det_transpose]

theorem detMod_tInv (A : GL ι 𝔸[k]) : detMod (tInv A) = (detMod A)⁻¹ := by
  simp [detMod, det_tInv, map_inv]

theorem tInv_tInv (A : GL ι 𝔸[k]) : tInv (tInv A) = A := by
  ext1
  have h : (((tInv A)⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) = (A : Matrix ι ι 𝔸[k])ᵀ := rfl
  show (((tInv A)⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k])ᵀ = A
  rw [h, Matrix.transpose_transpose]

theorem continuous_det : Continuous (Matrix.GeneralLinearGroup.det : GL ι 𝔸[k] → IdeleGroup k) :=
  Continuous.units_map (Matrix.detMonoidHom : Matrix ι ι 𝔸[k] →* 𝔸[k])
    (show Continuous fun A : Matrix ι ι 𝔸[k] ↦ A.det from continuous_id.matrix_det)

theorem continuous_detMod : Continuous (detMod : GL ι 𝔸[k] → ℝ) :=
  continuous_subtype_val.comp (continuous_ideleModule.comp continuous_det)

theorem continuous_tInv : Continuous (tInv : GL ι 𝔸[k] → GL ι 𝔸[k]) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (Units.continuous_val.comp continuous_inv).matrix_transpose
  · have h : Continuous fun A : GL ι 𝔸[k] ↦ (A : Matrix ι ι 𝔸[k])ᵀ :=
      Units.continuous_val.matrix_transpose
    exact h

theorem thetaCFun_of_pos (w : InfinitePlace k) (F : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k)
    {x : ℝ} (hx : 0 < x) : thetaCFun w F ω x = thetaCInt w F ω ⟨x, hx⟩ := dif_pos hx

theorem thetaCFun_smul (w : InfinitePlace k) (c : ℂ) (F : (ι → 𝔸[k]) → ℂ)
    (ω : HeckeCharacter k) : thetaCFun w (c • F) ω = c • thetaCFun w F ω := by
  funext x
  by_cases hx : 0 < x
  · simp only [Pi.smul_apply, smul_eq_mul, thetaCFun_of_pos w _ ω hx]
    exact GlobalTheory.CompanionTheory.He2M1.thetaCInt_smul w c F ω _
  · simp [thetaCFun, hx]

theorem thetaCFun_neg (w : InfinitePlace k) (F : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k) :
    thetaCFun w (fun x ↦ F (-x)) ω = thetaCFun w F ω := by
  funext x
  unfold thetaCFun
  rw [GlobalTheory.CompanionTheory.AdelicThetaSeries.thetaCInt_neg w F ω]

theorem thetaCConst_smul (c : ℂ) (F : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k) :
    thetaCConst (c • F) ω = c * thetaCConst F ω := by
  simp [thetaCConst, mul_assoc]

theorem thetaCConst_ltr (A : GL ι 𝔸[k]) (F : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k) :
    thetaCConst (ltr A F) ω = thetaCConst F ω := by
  simp [thetaCConst, ltr]

theorem thetaCConst_neg (F : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k) :
    thetaCConst (fun x ↦ F (-x)) ω = thetaCConst F ω := by
  simp [thetaCConst]

theorem ltr_one (F : (ι → 𝔸[k]) → ℂ) : ltr (1 : GL ι 𝔸[k]) F = F := by
  funext x
  simp [ltr]

theorem ltr_neg (A : GL ι 𝔸[k]) (F : (ι → 𝔸[k]) → ℂ) :
    ltr A (fun x ↦ F (-x)) = fun x ↦ ltr A F (-x) := by
  funext x
  simp [ltr, Matrix.mulVec_neg]

theorem fourier_ltr (A : GL ι 𝔸[k]) (F : (ι → 𝔸[k]) → ℂ) :
    adelicFourierPi k (ltr A F) =
      (((detMod A : ℝ) : ℂ)⁻¹) • ltr (tInv A) (adelicFourierPi k F) :=
  GlobalTheory.CompanionTheory.LtrFourier.Hd.adelicFourierPi_ltr A F

theorem thetaCFun_decay (w : InfinitePlace k) {Ψ : (ι → 𝔸[k]) → ℂ}
    (hΨ : Ψ ∈ schwartzBruhatPi (K := k) (ι := ι)) (ω : HeckeCharacter k) {C : Set (GL ι 𝔸[k])}
    (hC : IsCompact C) (r : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ A ∈ C, ∀ x : ℝ, 1 ≤ x →
      ‖thetaCFun w (ltr A Ψ) ω x - thetaCConst (ltr A Ψ) ω‖ ≤ M * x ^ (-r) := by
  obtain ⟨N, hN⟩ := exists_nat_ge r
  obtain ⟨M, hM⟩ := GlobalTheory.CompanionTheory.AdelicThetaSeries.exists_norm_thetaCInt_sub_le w hΨ ω hC N
  refine ⟨max M 0, le_max_right _ _, fun A hA x hx ↦ ?_⟩
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have h := hM A hA ⟨x, hx0⟩ hx
  rw [← thetaCFun_of_pos w _ ω hx0] at h
  have hpow : (x ^ N)⁻¹ ≤ x ^ (-r) := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg hx0.le]
    exact Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have hp0 : 0 ≤ (x ^ N)⁻¹ := by positivity
  calc _ ≤ (x ^ N)⁻¹ * M := h
    _ ≤ (x ^ N)⁻¹ * max M 0 := mul_le_mul_of_nonneg_left (le_max_left _ _) hp0
    _ ≤ x ^ (-r) * max M 0 := mul_le_mul_of_nonneg_right hpow (le_max_right _ _)
    _ = _ := mul_comm _ _

theorem isBigO_thetaCFun_sub (w : InfinitePlace k) {F : (ι → 𝔸[k]) → ℂ}
    (hF : F ∈ schwartzBruhatPi (K := k) (ι := ι)) (ω : HeckeCharacter k) (r : ℝ) :
    (fun x ↦ thetaCFun w F ω x - thetaCConst F ω) =O[atTop] (· ^ r) := by
  obtain ⟨M, -, hM⟩ := thetaCFun_decay w hF ω (isCompact_singleton (x := (1 : GL ι 𝔸[k]))) (-r)
  refine IsBigO.of_bound M ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have h := hM 1 rfl x hx
  rw [ltr_one, neg_neg] at h
  rwa [Real.norm_of_nonneg (Real.rpow_nonneg (zero_le_one.trans hx) r)]

theorem continuousOn_thetaCFun_ltr (w : InfinitePlace k) {Ψ : (ι → 𝔸[k]) → ℂ}
    (hΨ : Ψ ∈ schwartzBruhatPi (K := k) (ι := ι)) (ω : HeckeCharacter k) :
    ContinuousOn (fun q : GL ι 𝔸[k] × ℝ ↦ thetaCFun w (ltr q.1 Ψ) ω q.2) (univ ×ˢ Ioi 0) := by
  have h := GlobalTheory.CompanionTheory.EpsteinThetaC.continuous_thetaCInt_ltr w hΨ ω
  rw [continuousOn_iff_continuous_restrict]
  have hc : Continuous fun q : ↥(univ ×ˢ Ioi (0 : ℝ) : Set (GL ι 𝔸[k] × ℝ)) ↦
      ((⟨q.1.2, q.2.2⟩ : {r : ℝ // 0 < r}), q.1.1) :=
    (Continuous.subtype_mk (continuous_snd.comp continuous_subtype_val) _).prodMk
      (continuous_fst.comp continuous_subtype_val)
  refine (h.comp hc).congr fun q ↦ ?_
  simp only [restrict, Function.comp]
  exact (thetaCFun_of_pos w _ ω q.2.2).symm

theorem continuousOn_thetaCFun (w : InfinitePlace k) {F : (ι → 𝔸[k]) → ℂ}
    (hF : F ∈ schwartzBruhatPi (K := k) (ι := ι)) (ω : HeckeCharacter k) :
    ContinuousOn (thetaCFun w F ω) (Ioi 0) := by
  have h := continuousOn_thetaCFun_ltr w hF ω
  have h2 := h.comp (f := fun x : ℝ ↦ ((1 : GL ι 𝔸[k]), x)) (s := Ioi 0) (by fun_prop)
    (fun x hx ↦ ⟨mem_univ _, hx⟩)
  simpa [Function.comp_def, ltr_one] using h2

theorem thetaCFun_one_div (w : InfinitePlace k) {F : (ι → 𝔸[k]) → ℂ}
    (hF : F ∈ schwartzBruhatPi (K := k) (ι := ι)) {ω : HeckeCharacter k} (hω : ω * ω = 1) (x : ℝ)
    (hx : x ∈ Ioi (0 : ℝ)) :
    thetaCFun w F ω (1 / x) =
      ((1 : ℂ) * ((x ^ (Fintype.card ι : ℝ) : ℝ) : ℂ)) • thetaCFun w (adelicFourierPi k F) ω x := by
  have hx0 : (0 : ℝ) < x := hx
  have h := GlobalTheory.CompanionTheory.AdelicThetaSeries.Hd.thetaCInt_inv w hF ω ⟨x, hx0⟩
  rw [← eq_inv_of_mul_eq_one_left hω] at h
  rw [thetaCFun_of_pos w _ ω (one_div_pos.2 hx0), thetaCFun_of_pos w _ ω hx0, Real.rpow_natCast]
  have e : (⟨1 / x, one_div_pos.2 hx0⟩ : {r : ℝ // 0 < r}) = (⟨x, hx0⟩ : {r : ℝ // 0 < r})⁻¹ := by
    ext
    simp
  rw [e, h]
  simp

noncomputable def pair [Nonempty ι] (w : InfinitePlace k) {F : (ι → 𝔸[k]) → ℂ}
    (hF : F ∈ schwartzBruhatPi (K := k) (ι := ι)) {ω : HeckeCharacter k} (hω : ω * ω = 1) : WeakFEPair ℂ where
  f := thetaCFun w F ω
  g := thetaCFun w (adelicFourierPi k F) ω
  k := Fintype.card ι
  ε := 1
  f₀ := thetaCConst F ω
  g₀ := thetaCConst (adelicFourierPi k F) ω
  hf_int := (continuousOn_thetaCFun w hF ω).locallyIntegrableOn measurableSet_Ioi
  hg_int := (continuousOn_thetaCFun w (adelicFourierPi_mem_schwartzBruhatPi hF) ω).locallyIntegrableOn
    measurableSet_Ioi
  hk := by exact_mod_cast Fintype.card_pos
  hε := one_ne_zero
  h_feq := thetaCFun_one_div w hF hω
  hf_top := isBigO_thetaCFun_sub w hF ω
  hg_top := isBigO_thetaCFun_sub w (adelicFourierPi_mem_schwartzBruhatPi hF) ω

noncomputable def entireForm (P : WeakFEPair ℂ) (z : ℂ) : ℂ :=
  z * (z - P.k) * P.Λ₀ z - (z - P.k) * P.f₀ + z * P.ε * P.g₀

theorem entireForm_eq (P : WeakFEPair ℂ) {z : ℂ} (h0 : z ≠ 0) (hk : z ≠ P.k) :
    entireForm P z = z * (z - P.k) * P.Λ z := by
  have h1 : z - P.k ≠ 0 := sub_ne_zero.2 hk
  have h2 : (P.k : ℂ) - z ≠ 0 := sub_ne_zero.2 hk.symm
  simp only [entireForm, WeakFEPair.Λ, smul_eq_mul]
  field_simp
  ring

theorem differentiable_entireForm (P : WeakFEPair ℂ) : Differentiable ℂ (entireForm P) := by
  unfold entireForm
  have := P.differentiable_Λ₀
  fun_prop

theorem thetaCFun_fourier_ltr (w : InfinitePlace k) (A : GL ι 𝔸[k]) (F : (ι → 𝔸[k]) → ℂ)
    (ω : HeckeCharacter k) :
    thetaCFun w (adelicFourierPi k (ltr A F)) ω =
      (((detMod A : ℝ) : ℂ)⁻¹) • thetaCFun w (ltr (tInv A) (adelicFourierPi k F)) ω := by
  rw [fourier_ltr, thetaCFun_smul]

theorem thetaCConst_fourier_ltr (A : GL ι 𝔸[k]) (F : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k) :
    thetaCConst (adelicFourierPi k (ltr A F)) ω =
      ((detMod A : ℝ) : ℂ)⁻¹ * thetaCConst (adelicFourierPi k F) ω := by
  rw [fourier_ltr, thetaCConst_smul, thetaCConst_ltr]

noncomputable def pairAt [Nonempty ι] (w : InfinitePlace k) {Ψ : (ι → 𝔸[k]) → ℂ}
    (hΨ : Ψ ∈ schwartzBruhatPi (K := k) (ι := ι)) {ω : HeckeCharacter k} (hω : ω * ω = 1) (A : GL ι 𝔸[k]) :
    WeakFEPair ℂ :=
  pair w (GlobalTheory.CompanionTheory.LinearChangeSchwartzBruhat.ltr_mem hΨ A) hω

section pairAt

variable [Nonempty ι] (w : InfinitePlace k) {Ψ : (ι → 𝔸[k]) → ℂ}
  (hΨ : Ψ ∈ schwartzBruhatPi (K := k) (ι := ι)) {ω : HeckeCharacter k} (hω : ω * ω = 1)

theorem pairAt_bound {C : Set (GL ι 𝔸[k])} (hC : IsCompact C) (r : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ A ∈ C, ∀ x : ℝ, 1 ≤ x →
      ‖(pairAt w hΨ hω A).f x - (pairAt w hΨ hω A).f₀‖ ≤ M * x ^ (-r) ∧
      ‖(pairAt w hΨ hω A).g x - (pairAt w hΨ hω A).g₀‖ ≤ M * x ^ (-r) := by
  obtain ⟨M₁, hM₁, h₁⟩ := thetaCFun_decay w hΨ ω hC r
  obtain ⟨M₂, hM₂, h₂⟩ := thetaCFun_decay w (adelicFourierPi_mem_schwartzBruhatPi hΨ) ω
    (hC.image continuous_tInv) r
  have hcont : ContinuousOn (fun A : GL ι 𝔸[k] ↦ (detMod A)⁻¹) C :=
    (continuous_detMod.inv₀ fun A ↦ (detMod_pos A).ne').continuousOn
  obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hcont
  refine ⟨max M₁ (max B 0 * M₂), le_max_of_le_left hM₁, fun A hA x hx ↦ ⟨?_, ?_⟩⟩
  · have hp : 0 ≤ x ^ (-r) := Real.rpow_nonneg (zero_le_one.trans hx) _
    exact (h₁ A hA x hx).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hp)
  · have hp : 0 ≤ x ^ (-r) := Real.rpow_nonneg (zero_le_one.trans hx) _
    have e : (pairAt w hΨ hω A).g x - (pairAt w hΨ hω A).g₀ =
        ((detMod A : ℝ) : ℂ)⁻¹ * (thetaCFun w (ltr (tInv A) (adelicFourierPi k Ψ)) ω x -
          thetaCConst (ltr (tInv A) (adelicFourierPi k Ψ)) ω) := by
      show thetaCFun w (adelicFourierPi k (ltr A Ψ)) ω x -
        thetaCConst (adelicFourierPi k (ltr A Ψ)) ω = _
      rw [thetaCFun_fourier_ltr, thetaCConst_fourier_ltr, thetaCConst_ltr, Pi.smul_apply,
        smul_eq_mul, mul_sub]
    have hn : ‖((detMod A : ℝ) : ℂ)⁻¹‖ ≤ max B 0 := by
      have := hB A hA
      simp only [Real.norm_eq_abs, abs_inv] at this
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs]
      exact this.trans (le_max_left _ _)
    rw [e, norm_mul]
    calc _ ≤ max B 0 * (M₂ * x ^ (-r)) :=
          mul_le_mul hn (h₂ _ ⟨A, hA, rfl⟩ x hx) (norm_nonneg _) (le_max_right _ _)
      _ = (max B 0 * M₂) * x ^ (-r) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hp

theorem continuous_pairAt_f₀ : Continuous fun A : GL ι 𝔸[k] ↦ (pairAt w hΨ hω A).f₀ := by
  have h : (fun A : GL ι 𝔸[k] ↦ (pairAt w hΨ hω A).f₀) = fun _ ↦ thetaCConst Ψ ω := by
    funext A
    exact thetaCConst_ltr A Ψ ω
  rw [h]
  exact continuous_const

theorem continuous_inv_detMod : Continuous fun A : GL ι 𝔸[k] ↦ ((detMod A : ℝ) : ℂ)⁻¹ :=
  (Complex.continuous_ofReal.comp continuous_detMod).inv₀ fun A ↦
    Complex.ofReal_ne_zero.2 (detMod_pos A).ne'

theorem continuous_pairAt_g₀ : Continuous fun A : GL ι 𝔸[k] ↦ (pairAt w hΨ hω A).g₀ := by
  have h : (fun A : GL ι 𝔸[k] ↦ (pairAt w hΨ hω A).g₀) = fun A ↦
      ((detMod A : ℝ) : ℂ)⁻¹ * thetaCConst (adelicFourierPi k Ψ) ω := by
    funext A
    exact thetaCConst_fourier_ltr A Ψ ω
  rw [h]
  exact continuous_inv_detMod.mul continuous_const

theorem continuous_pairAt_Λ₀ : Continuous fun q : ℂ × GL ι 𝔸[k] ↦ (pairAt w hΨ hω q.2).Λ₀ q.1 := by
  refine GlobalTheory.CompanionTheory.EisRk1Cont.weakFEPair_continuous_Λ₀ (pairAt w hΨ hω) (Fintype.card ι)
    (fun _ ↦ rfl) 1 (fun _ ↦ rfl) ?_ ?_ (continuous_pairAt_f₀ w hΨ hω)
    (continuous_pairAt_g₀ w hΨ hω) ?_
  · exact continuousOn_thetaCFun_ltr w hΨ ω
  · have h1 := continuousOn_thetaCFun_ltr w (adelicFourierPi_mem_schwartzBruhatPi hΨ) ω
    have h2 := h1.comp (f := fun q : GL ι 𝔸[k] × ℝ ↦ (tInv q.1, q.2)) (s := univ ×ˢ Ioi 0)
      ((continuous_tInv.comp continuous_fst).prodMk continuous_snd).continuousOn
      (fun q hq ↦ ⟨mem_univ _, hq.2⟩)
    have h3 : Continuous fun q : GL ι 𝔸[k] × ℝ ↦ ((detMod q.1 : ℝ) : ℂ)⁻¹ :=
      continuous_inv_detMod.comp continuous_fst
    refine (h3.continuousOn.mul h2).congr fun q _ ↦ ?_
    show thetaCFun w (adelicFourierPi k (ltr q.1 Ψ)) ω q.2 = _
    rw [thetaCFun_fourier_ltr]
    rfl
  · intro p₀ r
    obtain ⟨C, hC, hp⟩ := exists_compact_mem_nhds p₀
    obtain ⟨M, -, hM⟩ := pairAt_bound w hΨ hω hC r
    exact ⟨C, hp, M, hM⟩

theorem pairAt_k (A : GL ι 𝔸[k]) : (pairAt w hΨ hω A).k = (Fintype.card ι : ℝ) := rfl

theorem pairAt_ε (A : GL ι 𝔸[k]) : (pairAt w hΨ hω A).ε = 1 := rfl

theorem continuous_entireForm_inv :
    Continuous fun y : ℂ × GL ι 𝔸[k] ↦ entireForm (pairAt w hΨ hω y.2⁻¹) y.1 := by
  have hinv : Continuous fun y : ℂ × GL ι 𝔸[k] ↦ y.2⁻¹ := continuous_inv.comp continuous_snd
  have hc : Continuous fun y : ℂ × GL ι 𝔸[k] ↦ ((y.1, y.2⁻¹) : ℂ × GL ι 𝔸[k]) :=
    continuous_fst.prodMk hinv
  have hΛ : Continuous fun y : ℂ × GL ι 𝔸[k] ↦ (pairAt w hΨ hω y.2⁻¹).Λ₀ y.1 := by
    have h := (continuous_pairAt_Λ₀ w hΨ hω).comp hc
    simpa only [Function.comp_def] using h
  have hf : Continuous fun y : ℂ × GL ι 𝔸[k] ↦ (pairAt w hΨ hω y.2⁻¹).f₀ := by
    have h := (continuous_pairAt_f₀ w hΨ hω).comp hinv
    simpa only [Function.comp_def] using h
  have hg : Continuous fun y : ℂ × GL ι 𝔸[k] ↦ (pairAt w hΨ hω y.2⁻¹).g₀ := by
    have h := (continuous_pairAt_g₀ w hΨ hω).comp hinv
    simpa only [Function.comp_def] using h
  have hz : Continuous fun y : ℂ × GL ι 𝔸[k] ↦ y.1 - (((Fintype.card ι : ℝ)) : ℂ) :=
    continuous_fst.sub continuous_const
  simp only [entireForm, pairAt_k, pairAt_ε]
  exact (((continuous_fst.mul hz).mul hΛ).sub (hz.mul hf)).add
    ((continuous_fst.mul continuous_const).mul hg)

theorem isEpCont : IsEpCont Ψ ω fun z m ↦ entireForm (pairAt w hΨ hω m⁻¹) z := by
  refine { entire := fun _ ↦ differentiable_entireForm _
           cont := continuous_entireForm_inv w hΨ hω
           eq := ?_
           strip := ?_ }
  · intro z hz m
    have hN : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
    have hz0 : z ≠ 0 := by
      rintro rfl
      simp only [Complex.zero_re] at hz
      linarith
    have hzk : z ≠ (((pairAt w hΨ hω m⁻¹).k : ℝ) : ℂ) := by
      intro h
      have h2 : z.re = (Fintype.card ι : ℝ) := by
        rw [h]
        exact Complex.ofReal_re _
      linarith
    have hm := ((pairAt w hΨ hω m⁻¹).hasMellin (s := z) hz).2
    have he := (GlobalTheory.CompanionTheory.EpsteinUnfold.Hd.epstein_eq_mellin w ω hΨ hz m).2
    have hArch : archExponent w ω = 0 := by
      have h : archExponent w ω = -archExponent w ω := by
        rw [← archExponent_inv, ← eq_inv_of_mul_eq_one_left hω]
      linarith
    rw [hArch] at he
    simp only [Complex.ofReal_zero, zero_mul, add_zero] at he
    show entireForm (pairAt w hΨ hω m⁻¹) z = _
    rw [entireForm_eq _ hz0 hzk, he]
    have hk : (((pairAt w hΨ hω m⁻¹).k : ℝ) : ℂ) = (Fintype.card ι : ℂ) := by
      show (((Fintype.card ι : ℝ)) : ℂ) = _
      simp
    rw [hk, ← hm]
    rfl
  · intro a b C hC
    have hC' : IsCompact ((fun m : GL ι 𝔸[k] ↦ m⁻¹) '' C) := hC.image continuous_inv
    set N : ℝ := (Fintype.card ι : ℝ) with hNdef
    have hN : 0 ≤ N := Nat.cast_nonneg _
    obtain ⟨M, hM0, hM⟩ := pairAt_bound w hΨ hω hC' (|a| + |b| + N + 1)
    obtain ⟨B₁, hB₁⟩ := hC'.exists_bound_of_continuousOn
      (continuous_pairAt_f₀ w hΨ hω).continuousOn
    obtain ⟨B₂, hB₂⟩ := hC'.exists_bound_of_continuousOn
      (continuous_pairAt_g₀ w hΨ hω).continuousOn
    set B : ℝ := max 0 (max B₁ B₂) with hBdef
    have hB0 : 0 ≤ B := le_max_left _ _
    refine ⟨(N + 1) * (2 * M) + (N + 2) * B, fun z hza hzb m hm ↦ ?_⟩
    have hA : m⁻¹ ∈ (fun m : GL ι 𝔸[k] ↦ m⁻¹) '' C := ⟨m, hm, rfl⟩
    set P := pairAt w hΨ hω m⁻¹ with hP
    have hPk : P.k = N := rfl
    have hPε : P.ε = 1 := rfl
    have ha := neg_abs_le a
    have hb := le_abs_self b
    have habs := abs_nonneg a
    have habs' := abs_nonneg b
    have h1 : 1 ≤ (|a| + |b| + N + 1) - z.re := by linarith
    have h2 : 1 ≤ (|a| + |b| + N + 1) - (P.k - z.re) := by rw [hPk]; linarith
    have hΛ := GlobalTheory.CompanionTheory.EisRk1.weakFEPair_norm_Λ₀_le P (r := |a| + |b| + N + 1) (M := M)
      (fun x hx ↦ (hM _ hA x hx).1) (fun x hx ↦ (hM _ hA x hx).2) z (by linarith) (by linarith)
    have hΛ' : ‖P.Λ₀ z‖ ≤ 2 * M := by
      rw [hPε, norm_one, one_mul] at hΛ
      have e1 := div_le_self hM0 h1
      have e2 := div_le_self hM0 h2
      linarith
    have hf₀ : ‖P.f₀‖ ≤ B := (hB₁ _ hA).trans ((le_max_left _ _).trans (le_max_right _ _))
    have hg₀ : ‖P.g₀‖ ≤ B := (hB₂ _ hA).trans ((le_max_right _ _).trans (le_max_right _ _))
    have hzn : ‖z - ((N : ℝ) : ℂ)‖ ≤ ‖z‖ + N := by
      refine (norm_sub_le _ _).trans ?_
      rw [Complex.norm_real, Real.norm_of_nonneg hN]
    show ‖entireForm P z‖ ≤ _
    have hnorm : ‖entireForm P z‖ ≤ ‖z‖ * (‖z‖ + N) * (2 * M) + (‖z‖ + N) * B + ‖z‖ * B := by
      have e : entireForm P z = z * (z - ((N : ℝ) : ℂ)) * P.Λ₀ z - (z - ((N : ℝ) : ℂ)) * P.f₀ +
          z * P.g₀ := by
        simp only [entireForm, hPk, hPε, mul_one]
      rw [e]
      refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add ?_ ?_)) ?_)
      · rw [norm_mul, norm_mul]
        exact mul_le_mul (mul_le_mul_of_nonneg_left hzn (norm_nonneg _)) hΛ' (norm_nonneg _)
          (by positivity)
      · rw [norm_mul]
        exact mul_le_mul hzn hf₀ (norm_nonneg _) (by positivity)
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_left hg₀ (norm_nonneg _)
    refine hnorm.trans ?_
    set s : ℝ := ‖z‖ with hs
    have hs0 : 0 ≤ s := norm_nonneg _
    have hL : 0 ≤ 2 * M := by positivity
    have t1 : s * (s + N) * (2 * M) ≤ (N + 1) * (2 * M) * (1 + s) ^ 2 := by
      have : s * (s + N) ≤ (N + 1) * (1 + s) ^ 2 := by nlinarith [mul_nonneg hN hs0, mul_nonneg hs0 hs0, mul_nonneg hN (mul_nonneg hs0 hs0)]
      nlinarith
    have t2 : (s + N) * B + s * B ≤ (N + 2) * B * (1 + s) ^ 2 := by
      have : (s + N) + s ≤ (N + 2) * (1 + s) ^ 2 := by nlinarith [mul_nonneg hN hs0, mul_nonneg hs0 hs0, mul_nonneg hN (mul_nonneg hs0 hs0)]
      nlinarith
    nlinarith

theorem entireForm_fe (A : GL ι 𝔸[k]) (z : ℂ) :
    entireForm (pairAt w hΨ hω A) z = ((detMod A : ℝ) : ℂ)⁻¹ *
      entireForm (pairAt w (adelicFourierPi_mem_schwartzBruhatPi hΨ) hω (tInv A))
        ((Fintype.card ι : ℂ) - z) := by
  have hΨ' := adelicFourierPi_mem_schwartzBruhatPi hΨ
  set P := pairAt w hΨ hω A with hP
  set Q := pairAt w hΨ' hω (tInv A) with hQ
  set d : ℂ := ((detMod A : ℝ) : ℂ) with hd
  have hd0 : d ≠ 0 := Complex.ofReal_ne_zero.2 (detMod_pos A).ne'
  have hdinv : (((detMod (tInv A) : ℝ) : ℂ)⁻¹) = d := by
    rw [detMod_tInv, Complex.ofReal_inv, inv_inv]
  have hneg : ltr A (adelicFourierPi k (adelicFourierPi k Ψ)) = fun x ↦ ltr A Ψ (-x) := by
    rw [adelicFourierPi_adelicFourierPi hΨ, ltr_neg]
  have hQg : Q.g = d • P.f := by
    show thetaCFun w (adelicFourierPi k (ltr (tInv A) (adelicFourierPi k Ψ))) ω =
      d • thetaCFun w (ltr A Ψ) ω
    rw [thetaCFun_fourier_ltr, hdinv, tInv_tInv, hneg, thetaCFun_neg]
  have hQg₀ : Q.g₀ = d * P.f₀ := by
    show thetaCConst (adelicFourierPi k (ltr (tInv A) (adelicFourierPi k Ψ))) ω =
      d * thetaCConst (ltr A Ψ) ω
    rw [fourier_ltr, hdinv, tInv_tInv, hneg, thetaCConst_smul, thetaCConst_neg]
  have hPg : P.g = d⁻¹ • Q.f := by
    show thetaCFun w (adelicFourierPi k (ltr A Ψ)) ω =
      d⁻¹ • thetaCFun w (ltr (tInv A) (adelicFourierPi k Ψ)) ω
    rw [thetaCFun_fourier_ltr]
  have hPg₀ : P.g₀ = d⁻¹ * Q.f₀ := by
    show thetaCConst (adelicFourierPi k (ltr A Ψ)) ω =
      d⁻¹ * thetaCConst (ltr (tInv A) (adelicFourierPi k Ψ)) ω
    rw [fourier_ltr, thetaCConst_smul]
  have hPf : P.f = d⁻¹ • Q.g := by
    rw [hQg, smul_smul, inv_mul_cancel₀ hd0, one_smul]
  have hPf₀ : P.f₀ = d⁻¹ * Q.g₀ := by
    rw [hQg₀, ← mul_assoc, inv_mul_cancel₀ hd0, one_mul]
  have key : P.Λ₀ = d⁻¹ • Q.symm.Λ₀ :=
    GlobalTheory.CompanionTheory.EisRankOne.weakFEPair_Λ₀_of_smul Q.symm P d⁻¹ hPf hPg rfl
      (show (1 : ℂ) = (1 : ℂ)⁻¹ by simp) hPf₀ hPg₀
  have hfe := Q.functional_equation₀ z
  have hQk : ((Q.k : ℝ) : ℂ) = (Fintype.card ι : ℂ) := by
    show (((Fintype.card ι : ℝ)) : ℂ) = _
    simp
  have hPk : ((P.k : ℝ) : ℂ) = (Fintype.card ι : ℂ) := hQk
  have hQε : Q.ε = 1 := rfl
  have hPε : P.ε = 1 := rfl
  rw [hQk, hQε, one_smul] at hfe
  simp only [entireForm, hQk, hPk, hQε, hPε, hfe, key, Pi.smul_apply, smul_eq_mul, hPf₀, hPg₀]
  ring

end pairAt

theorem epMain_of_epConv : EpConv → EpMain := by
  intro _ k _ _
  obtain ⟨V, hV, hvol⟩ :=
    (GlobalTheory.CompanionTheory.EpsteinVol.volChar_one_eq : ∃ V : ℝ, 0 < V ∧ volChar (1 : HeckeCharacter k) = (V : ℂ))
  obtain ⟨w⟩ : Nonempty (InfinitePlace k) := inferInstance
  refine ⟨V, hV, fun ι _ _ _ Ψ ω hΨ hω ↦ ?_⟩
  have hΨ' := adelicFourierPi_mem_schwartzBruhatPi hΨ
  refine ⟨fun z m ↦ entireForm (pairAt w hΨ hω m⁻¹) z,
    fun z m ↦ entireForm (pairAt w hΨ' hω m⁻¹) z, isEpCont w hΨ hω, isEpCont w hΨ' hω, ?_, ?_⟩
  · intro z m
    have h := entireForm_fe w hΨ hω m⁻¹ z
    have e : modPow (Matrix.GeneralLinearGroup.det m) 1 = ((detMod m : ℝ) : ℂ) := by
      simp [modPow, detMod]
    rw [map_inv, detMod_inv, Complex.ofReal_inv, inv_inv] at h
    rw [e]
    exact h
  · rintro rfl m
    have hk : ∀ A : GL ι 𝔸[k], (((pairAt w hΨ hω A).k : ℝ) : ℂ) = (Fintype.card ι : ℂ) := by
      intro A
      show (((Fintype.card ι : ℝ)) : ℂ) = _
      simp
    have hε : ∀ A : GL ι 𝔸[k], (pairAt w hΨ hω A).ε = 1 := fun _ ↦ rfl
    have hf₀ : (pairAt w hΨ hω m⁻¹).f₀ = Ψ 0 * V := by
      show thetaCConst (ltr m⁻¹ Ψ) 1 = _
      rw [thetaCConst_ltr, thetaCConst, hvol]
    have hg₀ : (pairAt w hΨ hω m⁻¹).g₀ = ((detMod m : ℝ) : ℂ) * (adelicFourierPi k Ψ 0 * V) := by
      show thetaCConst (adelicFourierPi k (ltr m⁻¹ Ψ)) 1 = _
      rw [thetaCConst_fourier_ltr, detMod_inv, Complex.ofReal_inv, inv_inv, thetaCConst, hvol]
    have e : modPow (Matrix.GeneralLinearGroup.det m) 1 = ((detMod m : ℝ) : ℂ) := by
      simp [modPow, detMod]
    refine ⟨?_, ?_⟩
    · simp only [entireForm, hk, hε, hf₀, hg₀]
      ring
    · simp only [entireForm, hk, hε, hf₀, hg₀, e]
      ring

end GlobalTheory.CompanionTheory.EpsteinMain.Hd
end

noncomputable section

namespace PositivityTheory.RgEis.Hd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem idTube : IdTube := GlobalTheory.T.identity_tube_holds
theorem tubeChain : TubeChain := GlobalTheory.T.tube_chain_holds
theorem secLaw : SecLaw := GlobalTheory.T.section_law_holds
theorem htLip : HtLip := GlobalTheory.T.height_lipschitz_holds
theorem stage : PiLocalization₂ := GlobalTheory.T.staged_estimate_holds
theorem wallLaw_of : SecLaw → WallLaw := GlobalTheory.T.wall_law_of_section_law
theorem cross_of : SecLaw → HtLip → PiLocalization₂ → WallLaw → Cross := GlobalTheory.T.crossing_of_walls_and_heights
theorem gallery_of : SecLaw → IdTube → TubeChain → Cross → Gallery := GlobalTheory.T.gallery_of_tubes_and_crossing
theorem transfer_of : SecLaw → WallLaw → Transfer := GlobalTheory.T.transfer_of_section_and_wall_laws
theorem twist_of : SecLaw → Twist := GlobalTheory.T.twist_of_section_law
theorem scale : Scale := GlobalTheory.T.eisenstein_scaling_law
theorem grpTop : GrpTop := GlobalTheory.T.general_linear_topological_group
theorem bdetLaw : BdetLaw := GlobalTheory.T.block_determinant_law
theorem extLaw : ExtLaw := GlobalTheory.T.extension_law
theorem parLaw_of : BdetLaw → ExtLaw → GrpTop → ParLaw := GlobalTheory.T.parabolic_law_of_block_det
theorem leviS_of : BdetLaw → ExtLaw → GrpTop → LeviS := GlobalTheory.T.levi_decomp_of_block_det
theorem leviQ_of : BdetLaw → ExtLaw → GrpTop → LeviQ := GlobalTheory.T.levi_quotient_of_block_det
theorem convGrOf_of : BdetLaw → ExtLaw → ConvGrOf := GlobalTheory.T.convergence_group_of_block_det
theorem convU_of : ParLaw → ConvU := GlobalTheory.T.unipotent_convergence_of_parabolic
theorem sgStep_of : Gallery → Transfer → Twist → GrpTop → ParLaw → LeviS → LeviQ → ConvGrOf → ConvU → SgStep := GlobalTheory.T.siegel_induction_from_gallery
theorem epConv : EpConv := GlobalTheory.CompanionTheory.EpConvB.epConv
theorem epMain_of : EpConv → EpMain := GlobalTheory.CompanionTheory.EpsteinMain.Hd.epMain_of_epConv
theorem testFun : TestFun := PositivityTheory.RgEis.TF.testFun
theorem testSph : TestSph := GlobalTheory.T.spherical_test_function_exists
theorem stdGood : StdGood := GlobalTheory.T.standard_section_good
theorem mirGen_of : SecLaw → StdGood → BdetLaw → EpConv → EpMain → TestFun → TestSph → MirGen := PositivityTheory.RgEis.MG.mirGen
theorem dict : Dict := GlobalTheory.T.local_global_dictionary
theorem dictInf : DictInf := GlobalTheory.T.archimedean_local_global_dictionary
theorem cmGood_of : StdGood → Dict → DictInf → CMGood := GlobalTheory.T.constant_multiplier_good
theorem cmMir_of : Dict → CMGood → GrpTop → BdetLaw → ExtLaw → ParLaw → MirGen → CMMir := GlobalTheory.T.constant_multiplier_mirabolic
theorem sgOne_of : SecLaw → WallLaw → Scale → StdGood → Dict → DictInf → CMGood → GrpTop → BdetLaw → ExtLaw → ParLaw →
    MirGen → SgOne := PositivityTheory.RgEis.So.sgOne_hd
theorem siegelMult_of : SecLaw → WallLaw → Dict → DictInf → CMGood → GrpTop → BdetLaw → ExtLaw → ParLaw → SgAll →
    SiegelEisensteinSeries.BRoad.SiegelMult := GlobalTheory.T.siegel_eisenstein_multiplicativity

theorem sgAll_of (hG : CMGood) (hM : CMMir) (h1 : SgOne) (hS : SgStep) : SgAll := by
  intro F E _ _ _ _ _ σ χ c h h' hχ hc ε
  suffices H : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι = n → 1 ≤ n → (adCM σ χ).Sg ε ι from
    fun ι _ _ hι => H _ ι rfl hι
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro ι _ _ hι hn
    rcases Nat.eq_or_lt_of_le hn with e | e
    · exact h1 F E σ χ c h h' hχ hc ε ι (hι.trans e.symm)
    · exact hS E _ (adCM σ χ) (hG F E σ χ c h h' hχ hc) (hM F E σ χ c h h' hχ hc) ε ι (by omega)
        fun κ _ _ h1 h2 => ih _ (hι ▸ h2) κ rfl h1

theorem sgAll : SgAll :=
  have hW := wallLaw_of secLaw
  have hP := parLaw_of bdetLaw extLaw grpTop
  have hG := cmGood_of stdGood dict dictInf
  have hM := mirGen_of secLaw stdGood bdetLaw epConv (epMain_of epConv) testFun testSph
  sgAll_of hG (cmMir_of dict hG grpTop bdetLaw extLaw hP hM)
    (sgOne_of secLaw hW scale stdGood dict dictInf hG grpTop bdetLaw extLaw hP hM)
    (sgStep_of (gallery_of secLaw idTube tubeChain (cross_of secLaw htLip stage hW)) (transfer_of secLaw hW)
      (twist_of secLaw) grpTop hP (leviS_of bdetLaw extLaw grpTop) (leviQ_of bdetLaw extLaw grpTop)
      (convGrOf_of bdetLaw extLaw) (convU_of hP))

theorem eisBL : GlobalTheory.ThK.Dbl.EisBL :=
  have hW := wallLaw_of secLaw
  have hP := parLaw_of bdetLaw extLaw grpTop
  have hG := cmGood_of stdGood dict dictInf
  have hM := mirGen_of secLaw stdGood bdetLaw epConv (epMain_of epConv) testFun testSph
  SiegelEisensteinSeries.BRoad.eisBL_of GlobalTheory.T.eisenstein_half_holds
    (siegelMult_of secLaw hW dict dictInf hG grpTop bdetLaw extLaw hP
      (sgAll_of hG (cmMir_of dict hG grpTop bdetLaw extLaw hP hM)
        (sgOne_of secLaw hW scale stdGood dict dictInf hG grpTop bdetLaw extLaw hP hM)
        (sgStep_of (gallery_of secLaw idTube tubeChain (cross_of secLaw htLip stage hW)) (transfer_of secLaw hW)
          (twist_of secLaw) grpTop hP (leviS_of bdetLaw extLaw grpTop) (leviQ_of bdetLaw extLaw grpTop)
          (convGrOf_of bdetLaw extLaw) (convU_of hP))))
    GlobalTheory.CompanionTheory.Entire.local_factorisation

end PositivityTheory.RgEis.Hd
