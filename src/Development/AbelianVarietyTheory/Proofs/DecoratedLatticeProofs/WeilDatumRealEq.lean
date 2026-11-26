module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MeanPair
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinSimplePoleOfDoublingMethod
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.Garding
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GaussianIsSchwartzFunction
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingMapThetaIdentityAnyWeilData
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatAdelicMatrixOfMemAdelicSchwartz
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchrodingerFunctionLinearThetaFunctions

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumRealEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealEqWeil

theorem weilDatum_realEq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT χS' χT' : (AE D)ˣ →* Circle) (om om' : Om S T), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S T χS' χT' om' → (∀ τ, ∃ e : ℚ, HasInfExp D χS τ e ∧ HasInfExp D χS' τ e) → (∀ τ, ∃ e : ℚ, HasInfExp D χT τ e ∧ HasInfExp D χT' τ e) → ∀ a ∈ GinfC S, ∀ b ∈ GinfC T, ∀ f, IsThetaFunO ψ S T f → om (a, b) f = om' (a, b) f := by
  intro D ψ S T χS χT χS' χT' om om' hW hW' hS hT a ha b hb f hf
  obtain ⟨θ, hθ⟩ := GlobalTheory.DualPairCompare.exists_infFam D

  have eS : ∀ τ, HasInfExp D (χS' * χS⁻¹) τ ((0 : ℤ) : ℚ) := fun τ => by
    obtain ⟨e, h1, h2⟩ := hS τ
    simpa using GlobalTheory.Chain.hasInfExp_div h2 h1
  have eT : ∀ τ, HasInfExp D (χT' * χT⁻¹) τ ((0 : ℤ) : ℚ) := fun τ => by
    obtain ⟨e, h1, h2⟩ := hT τ
    simpa using GlobalTheory.Chain.hasInfExp_div h2 h1
  obtain ⟨om'', hW'', hmv⟩ := GlobalTheory.WeilChange.exists_weilDatum_twist D ψ hW.std S T χS χT (χS' * χS⁻¹) (χT' * χT⁻¹) om hW
    (GlobalTheory.WeilVacChar.hecke_mul_inv hW'.hecS hW.hecS) (GlobalTheory.WeilVacChar.hecke_mul_inv hW'.hecT hW.hecT)
    (GlobalTheory.WeilVacChar.resEta_mul_inv hW'.resS hW.resS) (GlobalTheory.WeilVacChar.resEta_mul_inv hW'.resT hW.resT)
  rw [GlobalTheory.WeilVacChar.mul_mul_inv_cancel, GlobalTheory.WeilVacChar.mul_mul_inv_cancel] at hW''
  obtain ⟨x, hx, hxv⟩ := GlobalTheory.OneMapRef.RealMove.exists_root hθ S (GlobalTheory.RealPairBound.gramAt_det_ne D S) a ha
  obtain ⟨y, hy, hyv⟩ := GlobalTheory.OneMapRef.RealMove.exists_root hθ T (GlobalTheory.RealPairBound.gramAt_det_ne D T) b hb
  have x1 : (χT' * χT⁻¹) x = 1 := by
    apply Circle.coe_injective
    rw [hxv _ (fun _ => 0) eT]
    simp
  have y1 : (χS' * χS⁻¹) y = 1 := by
    apply Circle.coe_injective
    rw [hyv _ (fun _ => 0) eS]
    simp
  have h1 := hmv a b x y hx hy
  rw [x1, y1, inv_one, one_mul, Circle.coe_one, one_smul] at h1
  rw [← h1]
  exact GlobalTheory.WeilUniq.weilDatum_unique D ψ hW.std S T χS' χT' om'' om' hW'' hW' (a, b) f hf

end GlobalTheory.RealEqWeil
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MeanPairingLieDerivativeAntisymm
open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RegSch.Ibp

variable {D : D7} {V : HSp D}

theorem isFiniteMeasure_autMeasure (m : Measure (GA D V)) [hm : m.IsHaarMeasure] :
    IsFiniteMeasure (autMeasure V m) := by
  have : BorelSpace (GA D V) := ⟨rfl⟩
  have hfd : IsFundamentalDomain (GQ V) (stdDom (GQ V)) m := isFundamentalDomain_stdDom _ m
  exact ⟨by
    rw [autMeasure, quotMeasure_univ hfd]
    exact GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol V m _ hm hfd⟩

theorem isMulRightInvariant (m : Measure (GA D V)) [hm : m.IsHaarMeasure] : m.IsMulRightInvariant := by
  have : BorelSpace (GA D V) := ⟨rfl⟩
  have hfd : IsFundamentalDomain (GQ V) (stdDom (GQ V)) m := isFundamentalDomain_stdDom _ m
  exact ⟨GlobalTheory.AutQuotCheck.rightInvariant_of_covolume (GQ V) m hfd (hfd.measure_ne_zero (NeZero.ne m))
    (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol V m _ hm hfd).ne⟩

variable {θ : InfFam D} {τ : D.what₂.Tau}

end GlobalTheory.RegSch.Ibp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GodementSectionSmoothBounded
open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SphSmooth

open GlobalTheory.SiegelSet (IsRealLine lineDer)

variable {D : D7} {θ : InfFam D} {V : HSp D}

theorem isRealLine_oneP (hθ : IsInfFam θ) (V : HSp D) {τ : D.what₂.Tau}
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) :
    IsRealLine D.sp.cm.sig V.gram (oneP θ V τ X) := by
  refine ⟨placeOf D τ, embOverOf D τ, X, hX, fun t => ?_⟩
  obtain ⟨x, hx⟩ := exists_archEquiv_eq V (embOverOf D τ) rfl
    (GlobalTheory.SmoothAutCheck.exp_mem_UH (GlobalTheory.SmoothAutCheck.gramAt_unit V τ) hX t)
  refine ⟨x, ?_, ?_⟩
  · rw [oneP, ← hx, atTau_archEquiv hθ V _ rfl x]
  · rw [GlobalTheory.Orb.archMat_eq_archEquiv _ (isCMExt_host D), hx]

theorem mem_smFun_of_isSm (hθ : IsInfFam θ) {f : GA D V → ℂ} (h : GlobalTheory.UAut.IsSm D.sp.cm.sig V.gram f) :
    f ∈ SmFun θ V :=
  fun k τs Xs hX g => h k (fun i => oneP θ V (τs i) (Xs i)) (fun i => isRealLine_oneP hθ V (hX i)) g

def derSpan (V : HSp D) (f : GA D V → ℂ) : Submodule ℂ (GA D V → ℂ) :=
  Submodule.span ℂ {g | ∃ l : List (ℝ → GA D V), (∀ γ ∈ l, IsRealLine D.sp.cm.sig V.gram γ) ∧ g = l.foldr lineDer f}

theorem derSpan_le (hθ : IsInfFam θ) {f : GA D V → ℂ} (hf : f ∈ SmFun θ V) : derSpan V f ≤ SmFun θ V := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨l, hl, rfl⟩
  induction l with
  | nil => exact hf
  | cons γ l ih =>
    obtain ⟨p, hp, rfl⟩ := (hl γ List.mem_cons_self).eq_oneP hθ
    exact GlobalTheory.Mem.AutSpace.Rder_mem (ih fun δ hδ => hl δ (List.mem_cons_of_mem _ hδ)) hp

end GlobalTheory.SphSmooth

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsCartanInvStandardInvolutionDoubledGram
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsCartanInvStandardInvolutionDoubledGram
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped ComplexOrder

namespace GlobalTheory.CartStd

variable {D : D7}

theorem tauE_star_eq (τ : D.what₂.Tau) (x : D.host.E) : tauE D τ (star x) = star (tauE D τ x) := by
  have := D.host.isCMField_hostE
  exact NumberField.IsCMField.complexEmbedding_complexConj D.host.E _ x

theorem submatrix_fromBlocks_mul {n : ℕ} (a b c d a' b' c' d' : Matrix (Fin n) (Fin n) ℂ) :
    blk4 a b c d * blk4 a' b' c' d' =
      blk4 (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  rw [blk4, blk4, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  rfl

theorem stdJ_mul_self (n : ℕ) : (blk4 0 1 (-1) 0 : Matrix (Fin (n + n)) (Fin (n + n)) ℂ) * blk4 0 1 (-1) 0 = -1 := by
  rw [submatrix_fromBlocks_mul]
  simp only [Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, Matrix.mul_one, zero_add, add_zero, Matrix.mul_neg,
    Matrix.neg_mul, neg_zero]
  rw [blk4, show Matrix.fromBlocks (-1 : Matrix (Fin n) (Fin n) ℂ) 0 0 (-1) = -1 by
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg, neg_zero]]
  rw [show ((-1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm =
      -((1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ).submatrix finSumFinEquiv.symm finSumFinEquiv.symm) from rfl,
    Matrix.submatrix_one_equiv]

theorem stdJ_conjTranspose (n : ℕ) :
    (blk4 0 1 (-1) 0 : Matrix (Fin (n + n)) (Fin (n + n)) ℂ)ᴴ = -blk4 0 1 (-1) 0 := by
  unfold blk4
  rw [Matrix.conjTranspose_submatrix, Matrix.fromBlocks_conjTranspose,
    show -((Matrix.fromBlocks (0 : Matrix (Fin n) (Fin n) ℂ) 1 (-1) 0).submatrix finSumFinEquiv.symm
      finSumFinEquiv.symm) = (-(Matrix.fromBlocks (0 : Matrix (Fin n) (Fin n) ℂ) 1 (-1) 0)).submatrix
      finSumFinEquiv.symm finSumFinEquiv.symm from rfl, Matrix.fromBlocks_neg]
  simp

theorem map_Jst (τ : D.what₂.Tau) (n : ℕ) : (Jst D n).map (tauE D τ) = blk4 0 1 (-1) 0 := by
  unfold Jst blk4
  rw [← Matrix.submatrix_map, Matrix.fromBlocks_map]
  have h1 : (-1 : Matrix (Fin n) (Fin n) D.host.E).map (tauE D τ) = -1 := by
    rw [← RingHom.mapMatrix_apply, map_neg, map_one]
  simp [h1]

end GlobalTheory.CartStd

namespace GlobalTheory.CartStd

theorem isCartanInv_stdInv : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ s : RealMat (dblSp A),
    IsStdInv A μ s → ∀ τ, IsCartanInv (gramAt D (dblSp A) τ) (s τ) := by
  intro D A μ hμ s hs τ
  obtain ⟨hgram, hdet, -⟩ := GlobalTheory.StdUnn.Tm_gram_inv D A μ hμ
  set f := tauE D τ with hf
  set T := (Tm A μ).map f with hT
  set J : Matrix (Fin (A.rank + A.rank)) (Fin (A.rank + A.rank)) ℂ := blk4 0 1 (-1) 0 with hJ
  set z := f μ with hz
  have hstar : Function.Semiconj f star star := fun x => tauE_star_eq τ x
  have hTG : Tᴴ * gramAt D (dblSp A) τ * T = z • J := by
    have h := congrArg (fun M => M.map f) hgram
    simp only [Matrix.map_mul] at h
    rw [Matrix.conjTranspose_map f hstar] at h
    rw [show gramAt D (dblSp A) τ = (dblSp A).gram.map f from rfl, h, hJ, ← map_Jst τ A.rank]
    ext i j
    simp [Matrix.smul_apply, hz, hf]
  have hTdet : IsUnit T.det := by
    rw [hT, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hdet.map f
  set U := T⁻¹ with hU
  have hTU : T * U = 1 := Matrix.mul_nonsing_inv T hTdet
  have hUT : U * T = 1 := Matrix.nonsing_inv_mul T hTdet
  have hUhTh : Uᴴ * Tᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hTU, Matrix.conjTranspose_one]

  have hz0 : z ≠ 0 := (map_ne_zero f).2 hμ.1
  have hzc : star z = -z := by rw [hz, ← tauE_star_eq, hμ.2, map_neg]
  have hn : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hz0
  have hzz : z * z = -(((‖z‖ : ℝ) : ℂ) ^ 2) := by
    have h1 := Complex.mul_conj z
    rw [Complex.normSq_eq_norm_sq, ← Complex.star_def, hzc] at h1
    push_cast at h1
    linear_combination -h1
  set c := z / ((‖z‖ : ℝ) : ℂ) with hc
  have hcc : c * c = -1 := by
    rw [hc]; field_simp; linear_combination hzz
  have hcstar : star c = -c := by
    rw [hc, star_div₀, hzc, Complex.star_def, Complex.conj_ofReal, neg_div]
  have hzc' : z * c = -((‖z‖ : ℝ) : ℂ) := by
    rw [hc]; field_simp; linear_combination hzz

  set S := c • J with hS
  have hJJ : J * J = -1 := stdJ_mul_self _
  have hSS : S * S = 1 := by
    rw [hS, smul_mul_smul_comm, hcc, hJJ, neg_one_smul, neg_neg]
  have hSh : Sᴴ = S := by
    rw [hS, Matrix.conjTranspose_smul, hJ, stdJ_conjTranspose, hcstar, smul_neg, neg_smul, neg_neg]
  have hsS : s τ = T * S * U := by
    have h := hs τ
    rw [show stdInv A.rank μ τ = S from rfl] at h
    calc s τ = s τ * T * U := by rw [Matrix.mul_assoc, hTU, Matrix.mul_one]
      _ = T * S * U := by rw [h]
  have hG : gramAt D (dblSp A) τ = Uᴴ * (z • J) * U := by
    rw [← hTG]
    calc gramAt D (dblSp A) τ = (Uᴴ * Tᴴ) * gramAt D (dblSp A) τ * (T * U) := by
          rw [hUhTh, hTU, Matrix.one_mul, Matrix.mul_one]
      _ = Uᴴ * (Tᴴ * gramAt D (dblSp A) τ * T) * U := by simp only [Matrix.mul_assoc]
  refine ⟨?_, ?_, ?_⟩
  · rw [hsS]
    calc T * S * U * (T * S * U) = T * S * (U * T) * S * U := by simp only [Matrix.mul_assoc]
      _ = T * U := by rw [hUT, Matrix.mul_one, Matrix.mul_assoc T S S, hSS, Matrix.mul_one]
      _ = 1 := hTU
  · rw [hsS, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hSh]
    have hSJS : S * (z • J) * S = z • J := by
      rw [hS, smul_mul_smul_comm, hJJ, smul_mul_smul_comm, Matrix.neg_mul, Matrix.one_mul,
        show c * z * c = -z by linear_combination z * hcc, neg_smul, smul_neg, neg_neg]
    calc Uᴴ * (S * Tᴴ) * gramAt D (dblSp A) τ * (T * S * U)
        = Uᴴ * (S * (Tᴴ * gramAt D (dblSp A) τ * T) * S) * U := by simp only [Matrix.mul_assoc]
      _ = gramAt D (dblSp A) τ := by rw [hTG, hSJS, hG]
  · have hGs : gramAt D (dblSp A) τ * s τ = Uᴴ * (((‖z‖ : ℝ) : ℂ) • (1 : Matrix _ _ ℂ)) * U := by
      rw [hsS]
      calc gramAt D (dblSp A) τ * (T * S * U) = (Uᴴ * Tᴴ) * gramAt D (dblSp A) τ * (T * S * U) := by
            rw [hUhTh, Matrix.one_mul]
        _ = Uᴴ * ((Tᴴ * gramAt D (dblSp A) τ * T) * S) * U := by simp only [Matrix.mul_assoc]
        _ = _ := by
          rw [hTG, hS, smul_mul_smul_comm, hJJ, hzc', neg_smul, smul_neg, neg_neg]
    rw [hGs]
    have hpos : (0 : ℂ) < ((‖z‖ : ℝ) : ℂ) := Complex.zero_lt_real.2 (norm_pos_iff.2 hz0)
    refine (Matrix.PosDef.one.smul hpos).conjTranspose_mul_mul_same ?_
    intro x y hxy
    have h := congrArg T.mulVec hxy
    simpa [Matrix.mulVec_mulVec, hTU] using h

end GlobalTheory.CartStd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsCartanInvStandardInvolutionDoubledGramStatement
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCartanInv_standardInvolution_doubledGram : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ s : RealMat (dblSp A), IsStdInv A μ s → ∀ τ, IsCartanInv (gramAt D (dblSp A) τ) (s τ) := by
  first | exact @GlobalTheory.CartStd.isCartanInv_stdInv | exact GlobalTheory.CartStd.isCartanInv_stdInv | (intros; apply GlobalTheory.CartStd.isCartanInv_stdInv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaIntegralTranslateSmul
open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ThetaInv

def rmulEquiv {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [DiscreteTopology Γ] (g : G) :
    GlobalTheory.AutomorphicL2Unitary.Quot Γ ≃ᵐ GlobalTheory.AutomorphicL2Unitary.Quot Γ where
  toFun := rmul Γ g
  invFun := rmul Γ g⁻¹
  left_inv q := by rw [← rmul_mul, mul_inv_cancel, rmul_one]
  right_inv q := by rw [← rmul_mul, inv_mul_cancel, rmul_one]
  measurable_toFun := measurable_rmul g
  measurable_invFun := measurable_rmul g⁻¹

end GlobalTheory.ThetaInv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GelfandTransposeEqOfInvariantWords
noncomputable section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RegSch.GelfCyc

open GlobalTheory.SmoothForms (gelfA gelfA_eq_sum_pow)

section Alg

variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ}

theorem gelfA_conj (G : Fin n → Fin n → A) (P Q : Matrix (Fin n) (Fin n) ℂ) (hQP : Q * P = 1) (k : ℕ) :
    gelfA (fun a b => ∑ c, ∑ d, (P a c * Q d b) • G c d) k = gelfA G k := by
  have hPQ : P * Q = 1 := mul_eq_one_comm.1 hQP
  let φ : Matrix (Fin n) (Fin n) ℂ →+* Matrix (Fin n) (Fin n) A := (algebraMap ℂ A).mapMatrix
  have hc : ∀ (M : Matrix (Fin n) (Fin n) A) a b, (φ P * M * φ Q) a b = ∑ c, ∑ d, (P a c * Q d b) • M c d := by
    intro M a b
    simp only [Matrix.mul_apply, φ, RingHom.mapMatrix_apply, Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    rw [← Algebra.smul_def, ← Algebra.commutes, ← Algebra.smul_def, smul_smul, mul_comm]
  have h1 : (Matrix.of fun a b => ∑ c, ∑ d, (P a c * Q d b) • G c d) = φ P * Matrix.of G * φ Q := by
    ext a b
    rw [hc]
    rfl
  have h2 : ∀ m : ℕ, (φ P * Matrix.of G * φ Q) ^ m = φ P * Matrix.of G ^ m * φ Q := by
    intro m
    induction m with
    | zero => rw [pow_zero, pow_zero, mul_one, ← map_mul, hPQ, map_one]
    | succ m ih =>
      have : φ Q * φ P = 1 := by rw [← map_mul, hQP, map_one]
      rw [pow_succ, pow_succ, ih]
      simp only [mul_assoc]
      rw [← mul_assoc (φ Q), this, one_mul]
  rw [gelfA_eq_sum_pow, gelfA_eq_sum_pow, h1, h2]
  simp only [hc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
  have : ∀ d, ∑ a, (P a c * Q d a) • (Matrix.of G ^ (k + 1)) c d = (Q * P) d c • (Matrix.of G ^ (k + 1)) c d := by
    intro d
    rw [← Finset.sum_smul, Matrix.mul_apply]
    simp only [mul_comm]
  simp [this, hQP, Matrix.one_apply]

theorem gelfA_swap (E : Fin n → Fin n → A) (k : ℕ) :
    gelfA (fun a b => E b a) k = ∑ idx : Fin (k + 1) → Fin n,
      (List.ofFn fun a : Fin (k + 1) => E (idx a) (idx (a + 1))).reverse.prod := by
  rw [gelfA]
  refine (Fintype.sum_equiv ((Equiv.neg (Fin (k + 1))).arrowCongr (Equiv.refl _)) _ _ fun idx => ?_).symm
  congr 1
  have h : ∀ a : Fin (k + 1), a.rev + 1 = -a := fun a => by
    have : a.rev + a = Fin.last k := Fin.ext (by
      have := a.2
      rw [Fin.val_add, Fin.val_rev, Fin.val_last, Nat.mod_eq_of_lt] <;> omega)
    rw [eq_neg_iff_add_eq_zero, add_right_comm, this, Fin.last_add_one]
  have h' : ∀ a : Fin (k + 1), a.rev = -(a + 1) := fun a => by
    rw [neg_add, ← h, add_neg_cancel_right]
  have e : ∀ g : Fin (k + 1) → A, (List.ofFn g).reverse = List.ofFn fun a => g a.rev := fun g => by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp only [List.getElem_reverse, List.getElem_ofFn, List.length_ofFn]
      congr 1
      ext
      simp
  rw [e]
  congr 1
  funext a
  rw [h, h']
  rfl

theorem prod_ofFn_neg : ∀ (m : ℕ) (g : Fin m → A),
    (List.ofFn fun a => -g a).prod = (-1 : ℂ) ^ m • (List.ofFn g).prod
  | 0, _ => by simp
  | m + 1, g => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, prod_ofFn_neg m fun a => g a.succ, pow_succ]
    simp

theorem sum_words (φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] A) (M : Matrix (Fin n) (Fin n) ℂ) (hM : IsUnit M.det) (k : ℕ) :
    ∑ idx : Fin (k + 1) → Fin n,
      (List.ofFn fun a : Fin (k + 1) => φ (-(M * (Matrix.single (idx a) (idx (a + 1)) 1)ᵀ * M⁻¹))).prod =
    (-1 : ℂ) ^ (k + 1) • ∑ idx : Fin (k + 1) → Fin n,
      (List.ofFn fun a : Fin (k + 1) => φ (Matrix.single (idx a) (idx (a + 1)) 1)).reverse.prod := by
  have e : ∀ a b, φ (M * (Matrix.single a b 1)ᵀ * M⁻¹) = ∑ c, ∑ d, (M⁻¹ a c * M d b) • φ (Matrix.single d c 1) := by
    intro a b
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [← map_smul, ← map_sum]
    congr 1
    rw [Matrix.matrix_eq_sum_single (M * _ * _), Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
    congr 1
    simp [Matrix.mul_apply, Matrix.single, ite_and, mul_comm]
  rw [← gelfA_swap (fun a b => φ (Matrix.single a b 1)),
    ← gelfA_conj _ M⁻¹ M (Matrix.mul_nonsing_inv M hM), gelfA, Finset.smul_sum]
  refine Finset.sum_congr rfl fun idx _ => ?_
  simp only [map_neg, e]
  exact prod_ofFn_neg _ _

end Alg

open GlobalTheory.Mem.RealTranslate (derEnd)

theorem wordDer_eq {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} (τ : D.what₂.Tau)
    (w : List (Matrix (Fin V.rank) (Fin V.rank) ℂ)) (f : SmFun θ V) :
    wordDer θ V τ w f.1 = ((w.map (derEnd hθ τ)).prod f).1 := by
  induction w with
  | nil => rfl
  | cons Z w ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply]
    show RderC θ V τ Z (wordDer θ V τ w f.1) = _
    rw [ih]
    rfl

end GlobalTheory.RegSch.GelfCyc

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUniqueAdelicMatrixRealComponentsFinitePart
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUniqueAdelicMatrixRealComponentsFinitePart
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.StdUnn

theorem exists_unique_of_comp_finPart : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n : ℕ) (z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) (x₀ : Mx D m n), ∃! x : Mx D m n, (∀ τ, compAt θ τ x = z τ) ∧ x.map (finPart D) = x₀.map (finPart D) := by
  intro D θ hθ m n z x₀
  have hL : ∀ τ (w : Matrix (Fin m) (Fin n) ℂ), IsLineAt θ τ w (lineAt θ τ w) := fun τ w =>
    Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hθ m n τ w)
  let C : D.what₂.Tau → Mx D m n →+ Matrix (Fin m) (Fin n) ℂ := fun τ =>
    (((θ τ).comp (infPart D)).toAddMonoidHom).mapMatrix
  have hC : ∀ τ w, compAt θ τ w = C τ w := fun τ w => rfl
  let P : Mx D m n →+ Matrix (Fin m) (Fin n) _ := ((finPart D).toAddMonoidHom).mapMatrix
  have hP : ∀ w : Mx D m n, w.map (finPart D) = P w := fun w => rfl
  have key : ∀ x y : Mx D m n, (∀ τ, compAt θ τ x = compAt θ τ y) → x.map (finPart D) = y.map (finPart D) → x = y := by
    intro x y h1 h2
    refine Matrix.ext fun i j => ?_
    rw [← sub_eq_zero]
    refine (GlobalTheory.T.extensionAdele_realComponents_cmType D θ hθ).2.2.2 (x i j - y i j) (fun τ => ?_) ?_
    · have := congrFun (congrFun (h1 τ) i) j
      simp only [compAt, Matrix.map_apply] at this
      rw [(infPart D).map_sub, (θ τ).map_sub, this, sub_self]
    · have := congrFun (congrFun h2 i) j
      simp only [Matrix.map_apply] at this
      rw [(finPart D).map_sub, this, sub_self]
  refine ⟨x₀ + ∑ σ, lineAt θ σ (z σ - compAt θ σ x₀) 1, ⟨fun τ => ?_, ?_⟩, ?_⟩
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [hC, map_add (f := _), map_sum, ← hC]
    simp_rw [← hC, (hL _ _).2.2 1 τ]
    rw [Finset.sum_eq_single τ (fun b _ hb => if_neg (Ne.symm hb)) (by simp), if_pos rfl, Complex.ofReal_one, one_smul]
    abel
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [hP, hP, map_add (f := _), map_sum]
    simp_rw [← hP, (hL _ _).2.1 1]
    simp
  · rintro y ⟨hy1, hy2⟩
    apply key
    · intro τ
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hy1, hC, map_add (f := _), map_sum, ← hC]
      simp_rw [← hC, (hL _ _).2.2 1 τ]
      rw [Finset.sum_eq_single τ (fun b _ hb => if_neg (Ne.symm hb)) (by simp), if_pos rfl, Complex.ofReal_one, one_smul]
      abel
    · set_option synthInstance.maxHeartbeats 100000 in
        rw [hy2, hP, hP, map_add (f := _), map_sum]
      simp_rw [← hP, (hL _ _).2.1 1]
      simp

end GlobalTheory.StdUnn
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUniqueAdelicMatrixRealComponentsFinitePartStatement
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_adelicMatrix_realComponents_finitePart : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n : ℕ) (z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) (x₀ : Mx D m n), ∃! x : Mx D m n, (∀ τ, compAt θ τ x = z τ) ∧ x.map (finPart D) = x₀.map (finPart D) := by
  first | exact @GlobalTheory.StdUnn.exists_unique_of_comp_finPart | exact GlobalTheory.StdUnn.exists_unique_of_comp_finPart | (intros; apply GlobalTheory.StdUnn.exists_unique_of_comp_finPart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawThetaIdentity
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepSourceLineEqOppositeTargetLine
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepSourceLineEqOppositeTargetLine
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.ConjLine

theorem weil_source_line_opposite : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (L L' S : HSp D) (τ : Matrix (Fin L.rank) (Fin L'.rank) D.host.E), L.rank = L'.rank → τᴴ ⬝ (L.gram ⬝ τ) = (((-1 : ℤ) : D.host.E) * (D.host.xi0 * star D.host.xi0)) • L'.gram → ∀ (χz χ χ' : ((AE D)ˣ →* Circle)) (om : Om L S) (om' : Om S L'), IsWeilDatumO ψ L S χz χ om → IsWeilDatumO ψ S L' χ' χz⁻¹ om' → ∀ f, IsThetaFunO ψ L S f → IsThetaFunO ψ S L' (fun w => f (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ w))) ∧ ∀ h, om' (h, 1) (fun w => f (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ w))) = fun w => om (1, h) f (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ w)) := by
  intro D ψ L L' S τ hrk hg χz χ χ' om om' hom hom' f hf
  have hstd : IsStdChar D ψ (-1) := hom.std
  have CA := GlobalTheory.T.weilConjugationAdjointRule_standard_char D ψ hstd S L'
  have h1 := (CA.conj_target χ' χz⁻¹ om' hom').1
  rw [inv_inv] at h1
  have hg' : τᴴ ⬝ (L.gram ⬝ τ) = (((1 : ℤ) : D.host.E) * (D.host.xi0 * star D.host.xi0)) • (GlobalTheory.ChiGrid.negSp L').gram := by
    rw [hg, GlobalTheory.ChiGrid.negSp_gram]; simp
  have H := GlobalTheory.T.weilRep_conj_sourceLine_eq_targetLine D ψ L (GlobalTheory.ChiGrid.negSp L') S τ hrk hg' χz χ χ'⁻¹ om (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjTarget om') hom h1 f hf
  refine ⟨?_, ?_⟩
  · have := H.1
    exact (CA.theta_neg _).1.mp this
  · intro h
    have key : ∀ F : WO S L' → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjTarget om' (h, 1) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id F) = GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (om' (h, 1) F) := by
      intro F
      have e := GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cjEnd_cj (Equiv.refl (WO S L')) (om' (h, (GlobalTheory.ChiGrid.negGA L').symm 1)) F
      simpa [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjTarget] using e
    have H2 := H.2 h
    have K : GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjTarget om' (h, 1) (fun w => star (f (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ w)))) = GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (om' (h, 1) (fun w => f (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ w)))) := key (fun w => f (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ w)))
    rw [K] at H2
    funext w
    have := congrArg star (congrFun H2 w)
    simpa [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj] using this

end GlobalTheory.ConjLine
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepSourceLineEqOppositeTargetLineStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRep_sourceLine_eq_opposite_targetLine : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (L L' S : HSp D) (τ : Matrix (Fin L.rank) (Fin L'.rank) D.host.E), L.rank = L'.rank → τᴴ ⬝ (L.gram ⬝ τ) = (((-1 : ℤ) : D.host.E) * (D.host.xi0 * star D.host.xi0)) • L'.gram → ∀ (χz χ χ' : ((AE D)ˣ →* Circle)) (om : Om L S) (om' : Om S L'), IsWeilDatumO ψ L S χz χ om → IsWeilDatumO ψ S L' χ' χz⁻¹ om' → ∀ f, IsThetaFunO ψ L S f → IsThetaFunO ψ S L' (fun w => f (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ w))) ∧ ∀ h, om' (h, 1) (fun w => f (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ w))) = fun w => om (1, h) f (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ w)) := by
  first | exact @GlobalTheory.ConjLine.weil_source_line_opposite | exact GlobalTheory.ConjLine.weil_source_line_opposite | (intros; apply GlobalTheory.ConjLine.weil_source_line_opposite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawThetaIdentity
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.SeeLastPf

theorem ofAdj_zero (D : D7) (L S : HSp D) : GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S 0 = 0 := by
  simp [GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj]

theorem seeLast : ∀ D : D7, SeeLast D := by
  intro D ψ V₀ A L S X T L'' o o'' τ hL hL'' hτ χA χz χS χS' χT om₁ oma omz omX omT omz'' h₁ ha hz hX hT hz'' Ξ Φ₂ hΞ hΦ₂
  have hψ : IsStdChar D ψ (-1) := h₁.std
  have hsrc := GlobalTheory.T.thetaTensorRule_orthogonalSum_source D ψ hψ V₀ A L o S
  have htgt := GlobalTheory.T.thetaTensorRule_targetOrthogonalSum D ψ hψ X T L'' o'' S
  have hτ' : τᴴ ⬝ (L.gram ⬝ τ) = (((-1 : ℤ) : D.host.E) * (D.host.xi0 * star D.host.xi0)) • L''.gram := by
    rw [hτ]; simp
  have hrk : L.rank = L''.rank := hL.trans hL''.symm
  have hline := fun u => GlobalTheory.T.weilRep_sourceLine_eq_opposite_targetLine D ψ L L'' S τ hrk hτ' χz χS χS' omz omz'' hz hz''
    (fun v => Ξ ((o.resS S).symm (u, v))) ((hsrc.slice_theta Ξ hΞ).2 u)
  refine ⟨fun u => (hline u).1, ?_⟩
  intro h₀ h h'
  have e1 : ∀ u, omX (h, o''.emb (h', 1)) (o''.boxT S Φ₂ fun w => Ξ ((o.resS S).symm
      (u, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L''.rank) ⬝ w)))) 0 =
      omT (h, h') Φ₂ 0 * omz (1, h) (fun v => Ξ ((o.resS S).symm (u, v))) 0 := by
    intro u
    rw [htgt.om_box χS' χT χz⁻¹ omX omT omz'' hX hT hz'' h h' 1 Φ₂ _ hΦ₂ (hline u).1, htgt.box_zero,
      (hline u).2 h]
    beta_reduce
    congr 1
    exact congrArg (omz (1, h) (fun v => Ξ ((o.resS S).symm (u, v))))
      ((congrArg (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S) (Matrix.mul_zero _)).trans (ofAdj_zero D L S))
  have e2 := (hsrc.om_slice χA χz χS om₁ oma omz h₁ ha hz h₀ 1 h Ξ hΞ 0).2 0
  have e0 : (o.resS S).symm (0, 0) = 0 := by
    rw [← Prod.zero_eq_mk, map_zero]
  rw [e0] at e2
  simp only [e1]
  rw [e2]
  have : (fun u => omT (h, h') Φ₂ 0 * omz (1, h) (fun v => Ξ ((o.resS S).symm (u, v))) 0) =
      omT (h, h') Φ₂ 0 • (fun u' => omz (1, h) (fun v' => Ξ ((o.resS S).symm (u', v'))) 0) := by
    funext u; simp
  rw [this, map_smul]
  simp

end GlobalTheory.SeeLastPf

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawThetaIdentityStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastSeeSaw_thetaIdentity : ∀ D : D7, SeeLast D := by
  first | exact @GlobalTheory.SeeLastPf.seeLast | exact GlobalTheory.SeeLastPf.seeLast | (intros; apply GlobalTheory.SeeLastPf.seeLast <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InertPlaceLocalTraceCharacterConductorIntegers
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InertPlaceLocalTraceCharacterConductorIntegers
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.InertFrameLoc

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.InertFrameLoc

section Rigid

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

theorem ringHom_eq_id_of_int (f : w.adicCompletion E →+* w.adicCompletion E)
    (h1 : ∀ x : E, f (algebraMap E _ x) = algebraMap E _ x)
    (h2 : ∀ z, Valued.v z ≤ 1 → Valued.v (f z) ≤ 1) : f = RingHom.id _ := by
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
  set t : w.adicCompletion E := algebraMap E _ (a : E) with ht
  have hft : f t = t := h1 _
  have ht1 : Valued.v t < 1 := by
    rw [ht, GlobalTheory.Idele.valued_algebraMap]
    exact (HeightOneSpectrum.valuation_lt_one_iff_mem w a).2 ha
  have htz : t ≠ 0 := by
    rw [ht, map_ne_zero, Ne, RingOfIntegers.coe_eq_zero_iff]
    exact ha0
  have key : ∀ (n : ℕ) z, Valued.v z ≤ Valued.v t ^ n → Valued.v (f z) ≤ Valued.v t ^ n := by
    intro n z hz
    have htn : t ^ n ≠ 0 := pow_ne_zero _ htz
    have hz' : z = t ^ n * (z / t ^ n) := by field_simp
    rw [hz', map_mul, map_pow, hft, Valuation.map_mul, Valuation.map_pow]
    refine mul_le_of_le_one_right' (h2 _ ?_)
    rw [map_div₀, map_pow]
    exact div_le_one_of_le₀ hz zero_le'
  have hcont : Continuous f := by
    refine continuous_of_continuousAt_zero f (Metric.tendsto_nhds.2 fun ε hε => ?_)
    have h1' : ‖t‖ < 1 := Valued.toNormedField.norm_lt_one_iff.2 ht1
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hε h1'
    have hne : Valued.v t ^ m ≠ 0 := pow_ne_zero _ ((map_ne_zero _).2 htz)
    filter_upwards [(GlobalTheory.Idele.isOpen_valued_le (K := E) w (WithZero.log (Valued.v t ^ m))).mem_nhds
      (x := 0) (by simp)] with z hz
    rw [map_zero, dist_zero_right]
    refine (Valued.toNormedField.norm_le_iff.2 ?_).trans_lt ((norm_pow t m).trans_lt hm)
    rw [map_pow]
    refine key m z ?_
    have hz' : Valued.v z ≤ WithZero.exp (WithZero.log (Valued.v t ^ m)) := hz
    rwa [WithZero.exp_log hne] at hz'
  exact RingHom.coe_inj ((HeightOneSpectrum.denseRange_algebraMap E w).equalizer hcont continuous_id
    (funext fun x => h1 x))

end Rigid

end GlobalTheory.InertFrameLoc

namespace GlobalTheory.InertFrameLoc

section Cond

open GlobalTheory.EmbChart

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}

theorem tensAt_mul_tensAt (y y' : Fv D.host.F v ⊗[D.host.F] D.host.E) :
    tensAt D.host.E v y * tensAt D.host.E v y' = tensAt D.host.E v (y * y') := by
  rw [tensAt_mul_right, compFin_tensAt]

theorem compFin_incA (x : D.host.E) :
    compFin D.host.F D.host.E v (incA D x) = (1 : Fv D.host.F v) ⊗ₜ[D.host.F] x := by
  show evFin D.host.F v 1 ⊗ₜ x = _
  rw [map_one]

theorem tensAt_one_mul_incA (x : D.host.E) :
    tensAt D.host.E v 1 * incA D x = tensAt D.host.E v ((1 : Fv D.host.F v) ⊗ₜ[D.host.F] x) := by
  rw [tensAt_mul_right, one_mul, compFin_incA]

theorem secW_mul (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v)
    (z z' : w.adicCompletion D.host.E) : secW hw h (z * z') = secW hw h z * secW hw h z' := by
  show tensAt D.host.E v ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm (z * z')) =
    tensAt D.host.E v ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm z) *
      tensAt D.host.E v ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm z')
  rw [map_mul, tensAt_mul_tensAt]

theorem complEquiv_symm_algebraMap (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v)
    (x : D.host.E) : (GlobalTheory.LFun.InertChart.complEquiv hw h).symm (algebraMap D.host.E _ x) =
      (1 : Fv D.host.F v) ⊗ₜ[D.host.F] x := by
  rw [RingEquiv.symm_apply_eq]
  show _ = GlobalTheory.LFun.toCompl h ((1 : Fv D.host.F v) ⊗ₜ[D.host.F] x)
  rw [GlobalTheory.LFun.toCompl_tmul, map_one, one_mul]

theorem isPrimeIdem_tensAt (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) :
    IsPrimeIdem w (tensAt D.host.E v 1) (tensAt D.host.E v 1) := by
  refine Or.inr ⟨rfl, ⟨v, atPlace v 1, ⟨GlobalTheory.AdelicU.singleFin v 1, rfl, GlobalTheory.AdelicU.evalV_singleFin_self v 1,
    fun u hu => GlobalTheory.AdelicU.evalV_singleFin_ne hu 1⟩, rfl⟩, fun x hx => ?_⟩
  rw [tensAt_one_mul_incA, finPart_tensAt_mem_iff, GlobalTheory.LFun.InertChart.mem_intLoc_iff hw h, GlobalTheory.LFun.toCompl_tmul,
    map_one, one_mul]
  show _ ↔ ¬ (Valued.v (algebraMap D.host.E (w.adicCompletion D.host.E) (x : D.host.E)⁻¹) ≤ 1)
  have h0 : w.valuation D.host.E (x : D.host.E) ≠ 0 := (map_ne_zero _).2 (RingOfIntegers.coe_ne_zero_iff.2 hx)
  rw [GlobalTheory.Idele.valued_algebraMap, map_inv₀, not_le, one_lt_inv₀ (zero_lt_iff.2 h0),
    HeightOneSpectrum.valuation_lt_one_iff_mem]

end Cond

theorem thW_cond : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) (c : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E) (ϖ : w.adicCompletion D.host.E) (k : w.adicCompletion D.host.E), IsStdChar D ψ (-1) → IsConjAt D.sp.cm.sig h c → IsUnramInv ϖ c (qV D.host.F v) → GlobalTheory.InertLoc.IsGen D w k → ∀ z, (∀ u ∈ Formalism.UG.intL (w.adicCompletion D.host.E), thW ψ hw h (k * c k) (z * u) = 1) ↔ z ∈ Formalism.UG.intL (w.adicCompletion D.host.E) := by
  intro D ψ v w hw h c ϖ k hψ hconj hU hk z
  have he := isPrimeIdem_tensAt (D := D) hw h
  obtain ⟨ϖ0, σ0, q0, π0, hU0, -, hch, hV⟩ := GlobalTheory.InertLoc.exists_chart (GlobalTheory.WeilAtPlace.conjPl_eq_of_inert hw h) he
  have hsec_e : ∀ y, GlobalTheory.EmbChart.tensAt D.host.E v 1 * secW hw h y = secW hw h y := fun y => by
    show GlobalTheory.EmbChart.tensAt D.host.E v 1 * GlobalTheory.EmbChart.tensAt D.host.E v _ = GlobalTheory.EmbChart.tensAt D.host.E v _
    rw [tensAt_mul_tensAt, one_mul]
  let f0 : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E :=
    { toFun := fun z => π0 (secW hw h z)
      map_one' := by
        show π0 (GlobalTheory.EmbChart.tensAt D.host.E v ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm 1)) = 1
        rw [map_one]
        exact hch.pi_idem
      map_mul' := fun z z' => by
        show π0 (secW hw h (z * z')) = π0 (secW hw h z) * π0 (secW hw h z')
        rw [secW_mul, map_mul]
      map_zero' := by
        show π0 (secW hw h 0) = 0
        rw [map_zero, map_zero]
      map_add' := fun z z' => by
        show π0 (secW hw h (z + z')) = π0 (secW hw h z) + π0 (secW hw h z')
        rw [map_add (f := _), map_add (f := _)] }
  have hf0 : f0 = RingHom.id _ := ringHom_eq_id_of_int w f0 (fun x => by
      show π0 (GlobalTheory.EmbChart.tensAt D.host.E v ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm (algebraMap D.host.E _ x))) = _
      rw [complEquiv_symm_algebraMap, ← tensAt_one_mul_incA, map_mul, hch.pi_idem, one_mul, hch.2.2.2.1])
    (fun z hz => by
      refine (hch.2.2.2.2.2 (secW hw h z)).1 ?_
      rw [hsec_e]
      show finPart D (GlobalTheory.EmbChart.tensAt D.host.E v ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm z)) ∈ intAE D
      rw [GlobalTheory.EmbChart.finPart_tensAt_mem_iff, GlobalTheory.LFun.InertChart.mem_intLoc_iff hw h]
      show (GlobalTheory.LFun.InertChart.complEquiv hw h) ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm z) ∈ Ov D.host.E w
      rw [RingEquiv.apply_symm_apply]
      exact hz)
  have hpi : ∀ z, π0 (secW hw h z) = z := fun z => RingHom.congr_fun hf0 z
  have hsec : ∀ z, hch.sec z = secW hw h z := fun z =>
    hch.ext (hch.mul_sec z) (hsec_e z) (by rw [hch.pi_sec, hpi])
  have hσc : ∀ x : D.host.E, σ0 (algebraMap D.host.E _ x) = c (algebraMap D.host.E _ x) := fun x => by
    calc σ0 (algebraMap D.host.E _ x) = σ0 (π0 (incA D x)) := by rw [hch.2.2.2.1]
      _ = π0 (cA D (incA D x)) := (hch.2.2.2.2.1 _).symm
      _ = algebraMap D.host.E _ (D.sp.cm.sig x) := hch.2.2.2.1 (D.sp.cm.sig x)
      _ = c (algebraMap D.host.E _ x) := (GlobalTheory.LFun.InertChart.conj_algebraMap hconj x).symm
  have hg := ringHom_eq_id_of_int w (c.comp σ0) (fun x => by
      rw [RingHom.comp_apply, hσc, hU.1])
    (fun z hz => by
      rw [RingHom.comp_apply, hU.2.1, hU0.2.1]
      exact hz)
  have hσ : ∀ z, σ0 z = c z := fun z => by
    have h1 : c (σ0 z) = z := RingHom.congr_fun hg z
    calc σ0 z = c (c (σ0 z)) := (hU.1 _).symm
      _ = c z := by rw [h1]
  have hth : ∀ z, GlobalTheory.InertLoc.th ψ hch k z = thW ψ hw h (k * c k) z := fun z => by
    rw [GlobalTheory.InertLoc.th_apply, thW_apply, hσ, hsec]
  obtain ⟨β, -, hβ, -⟩ := hV D.sp.X'
  have hi : 0 < D.sp.X'.rank := by
    have h1 := D.R.m_add_three_le_k
    rw [D.sp.X'_rank, Formalism.BasicNotions.Ranks.rankX', Formalism.BasicNotions.Ranks.r]
    omega
  have := GlobalTheory.InertLoc.th_cond hψ hch hU0.2.1 hβ ⟨0, hi⟩ hk z
  simpa only [hth] using this

end GlobalTheory.InertFrameLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InertPlaceLocalTraceCharacterConductorIntegersStatement
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.InertFrameLoc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPlace_localTraceCharacter_conductor_integers : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) (c : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E) (ϖ : w.adicCompletion D.host.E) (k : w.adicCompletion D.host.E), IsStdChar D ψ (-1) → IsConjAt D.sp.cm.sig h c → IsUnramInv ϖ c (qV D.host.F v) → GlobalTheory.InertLoc.IsGen D w k → ∀ z, (∀ u ∈ Formalism.UG.intL (w.adicCompletion D.host.E), thW ψ hw h (k * c k) (z * u) = 1) ↔ z ∈ Formalism.UG.intL (w.adicCompletion D.host.E) := by
  first | exact @GlobalTheory.InertFrameLoc.thW_cond | exact GlobalTheory.InertFrameLoc.thW_cond | (intros; apply GlobalTheory.InertFrameLoc.thW_cond <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchrodingerFunctionLinearThetaFunctionsStatement
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schrodingerFunction_linear_thetaFunctions : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A B : HSp D) (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ f f', IsThetaFunO ψ (dblSp A) B f → IsThetaFunO ψ (dblSp A) B f' → ∀ c : ℂ, IsThetaFunO ψ (dblSp A) B (f + f') ∧ IsThetaFunO ψ (dblSp A) B (c • f) ∧ sch ψ A B ν 𝓨 (f + f') = sch ψ A B ν 𝓨 f + sch ψ A B ν 𝓨 f' ∧ sch ψ A B ν 𝓨 (c • f) = c • sch ψ A B ν 𝓨 f := by
  first | exact @GlobalTheory.StdUnn.sch_linear | exact GlobalTheory.StdUnn.sch_linear | (intros; apply GlobalTheory.StdUnn.sch_linear <;> assumption)
end
