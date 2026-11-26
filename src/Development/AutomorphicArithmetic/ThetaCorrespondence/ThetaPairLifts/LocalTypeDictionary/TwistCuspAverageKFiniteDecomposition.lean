module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspFormKFiniteApprox
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedThetaLiftOfCuspFormIsSmoothAutomorphic

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.AveragingPreservesCuspType
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.AverageIsTypeAtOtherPlaceTwist
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
noncomputable section
namespace GlobalTheory.AvgTypeOther
section SeriesClosure
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S _root_.Formalism.L2.Theta Formalism.REAL MeasureTheory Matrix
open GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.PointAtPlaceHom GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes
open GlobalTheory.SeriesToClosure
open scoped TensorProduct InnerProductSpace
end SeriesClosure
section ClosureSeries
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S _root_.Formalism.L2.Theta Matrix
open scoped TensorProduct
open GlobalTheory.ClosureSeries
end ClosureSeries
open Formalism.MainNotions.S Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum in
theorem isTypeAt_average_other_place : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (τ τ' : D.what₂.Tau), τ' ≠ τ → ∀ (ψ : GA D N.V → ℂ), IsAutFunSm θ N.V ψ → IsTypeAt θ N.V τ' (N.S τ') ψ → ∀ (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), GlobalTheory.TypeSum.KFinFun (N.M.ε τ) e → IsTypeAt θ N.V τ' (N.S τ') (GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) e ψ) := by
  intro D θ hθ hPr N τ τ' hne ψ hψ hty e he
  have hec : Continuous e := by
    obtain ⟨F, -, h1, h2, -⟩ := he
    exact h2 _ h1
  have hHC := hPr.harishChandraModules
  have hCW := hPr.casselmanWallach
  have hUn := GlobalTheory.Published.discreteSeriesHermitianUnique_iff.1 hPr.discreteSeriesHermitianUnique
  have hT := hasTypeAt_of_isTypeAt θ N.V τ' (N.S τ') ψ hHC hθ hψ hty
  have hP := N.M.fr_unit τ
  have hJ := N.M.fr_gram τ
  have hU : ∀ k, (N.M.fr τ)⁻¹ * Formalism.REAL.toMK k * N.M.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ) :=
    fun k => GlobalTheory.LowTypeDetermined.conj_inv_mem hP hJ (K_le_UJ (toMK_mem_K k))
  have hκ := GlobalTheory.SeriesToClosure.continuous_conjK (ε := N.M.ε τ) (P := N.M.fr τ)
  have hA := GlobalTheory.AvgOtherPlace.hasTypeAt_avgF (Formalism.REAL.muK (N.M.ε τ)) hθ hne hκ hU hec hψ.cont hT
  have hAs := GlobalTheory.RealAverage.isAutFunSm_average D θ hθ N.V τ (Formalism.REAL.KG (N.M.ε τ)) (Formalism.REAL.muK (N.M.ε τ)) _
    hκ hU e hec ψ hψ
  obtain ⟨H, i1, i2, σ, lam, ε, P, hE, hD, hP', hJ', -⟩ := hty
  exact isTypeAt_of_hasTypeAt_model θ N.V τ' (N.S τ') _ hUn hHC hCW hθ H σ lam ε P hE
    (GlobalTheory.Published.HermitianUnique.isHCParam_of_isDS hE.1 hD) hD hP' hJ' hAs hA
end GlobalTheory.AvgTypeOther
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.average_isTypeAt_other_place_twist : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (τ τ' : D.what₂.Tau), τ' ≠ τ → ∀ (ψ : GA D N.V → ℂ), IsAutFunSm θ N.V ψ → IsTypeAt θ N.V τ' (N.S τ') ψ → ∀ (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), GlobalTheory.TypeSum.KFinFun (N.M.ε τ) e → IsTypeAt θ N.V τ' (N.S τ') (GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) e ψ) := by
  first | exact @_root_.GlobalTheory.AvgTypeOther.isTypeAt_average_other_place | exact _root_.GlobalTheory.AvgTypeOther.isTypeAt_average_other_place | (intros; apply _root_.GlobalTheory.AvgTypeOther.isTypeAt_average_other_place <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.AverageIsTypeAtSamePlaceTwist
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.PointAtPlaceHom GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes
namespace GlobalTheory.AvgSamePlace
theorem isTypeAt_average_same_place : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (τ : D.what₂.Tau) (ψ : GA D N.V → ℂ), IsAutFunSm θ N.V ψ → IsTypeAt θ N.V τ (N.S τ) ψ → ∀ (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), GlobalTheory.TypeSum.KFinFun (N.M.ε τ) e → IsTypeAt θ N.V τ (N.S τ) (GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) e ψ) := by
  intro D θ hθ hPr N τ ψ _ hT e he
  obtain ⟨H, i1, i2, σ, lam, ε, P, hE, hD, hP, hJ, hx⟩ := hT
  obtain ⟨rfl, rfl⟩ := GlobalTheory.SignedParTest.isEnum_unique hE (N.M.enum τ)
  haveI : CompleteSpace H := hD.1
  have hfr : IsUnit (N.M.fr τ) := N.M.fr_unit τ
  have hfrJ := N.M.fr_gram τ
  have dfr := (isUnit_iff_isUnit_det _).1 hfr
  have dP := (isUnit_iff_isUnit_det _).1 hP
  have fr1 : (N.M.fr τ)⁻¹ * N.M.fr τ = 1 := Matrix.nonsing_inv_mul _ dfr
  have fr2 : N.M.fr τ * (N.M.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ dfr
  have P1 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ dP
  have P2 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ dP
  set fr := N.M.fr τ with hfrdef
  set h := P * fr⁻¹ with hh
  set hi := fr * P⁻¹ with hhi
  have hih : hi * h = 1 := by
    calc hi * h = fr * (P⁻¹ * P) * fr⁻¹ := by simp only [hh, hhi, Matrix.mul_assoc]
      _ = 1 := by rw [P1, Matrix.mul_one, fr2]
  have hU : h ∈ UJset (N.M.ε τ) := by
    show hᴴ * Jm (N.M.ε τ) * h = Jm (N.M.ε τ)
    calc hᴴ * Jm (N.M.ε τ) * h = (fr⁻¹)ᴴ * (Pᴴ * Jm (N.M.ε τ) * P) * fr⁻¹ := by
          simp only [hh, conjTranspose_mul, Matrix.mul_assoc]
      _ = (fr * fr⁻¹)ᴴ * Jm (N.M.ε τ) * (fr * fr⁻¹) := by
          rw [hJ, ← hfrJ]; simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [fr2]; simp
  have hiU : hi ∈ UJset (N.M.ε τ) := by
    show hiᴴ * Jm (N.M.ε τ) * hi = Jm (N.M.ε τ)
    calc hiᴴ * Jm (N.M.ε τ) * hi = (P⁻¹)ᴴ * (frᴴ * Jm (N.M.ε τ) * fr) * P⁻¹ := by
          simp only [hhi, conjTranspose_mul, Matrix.mul_assoc]
      _ = (P * P⁻¹)ᴴ * Jm (N.M.ε τ) * (P * P⁻¹) := by
          rw [hfrJ, ← hJ]; simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [P2]; simp
  set σ₂ : Mx N.V.rank → (H →L[ℂ] H) := fun y => σ (h * y * hi) with hσ₂def
  have hD₂ : IsDS (N.M.ε τ) (N.M.lam τ) σ₂ := GlobalTheory.CayleyChoice.isDS_conj hD hiU hU hih
  have hσ₂ : Std (N.M.ε τ) σ₂ := std_of_isDS hPr.harishChandraModules hD₂
  have e1 : ∀ g, σ (P * g * P⁻¹) = σ₂ (fr * g * fr⁻¹) := by
    intro g
    show σ (P * g * P⁻¹) = σ (h * (fr * g * fr⁻¹) * hi)
    congr 1
    calc P * g * P⁻¹ = P * (fr⁻¹ * fr) * g * (fr⁻¹ * fr) * P⁻¹ := by rw [fr1]; simp
      _ = _ := by simp only [hh, hhi, Matrix.mul_assoc]
  simp only [e1] at hx
  refine ⟨H, i1, i2, σ₂, N.M.lam τ, N.M.ε τ, fr, N.M.enum τ, hD₂, hfr, hfrJ, fun x => ?_⟩
  have hx' : HasTypeAll (lieSet (N.M.ε τ)) (UJset (N.M.ε τ)) σ₂ (GlobalTheory.SeriesToClosure.res θ N.V τ fr ψ x) :=
    hasTypeAll_transport _ H H _ σ₂ (gramAt D N.V τ) (Jm (N.M.ε τ)) fr (GlobalTheory.LowTypeDetermined.isUnit_gram hfr hfrJ)
      hfr hfrJ (LinearIsometryEquiv.refl ℂ H) (fun _ _ _ => rfl) (fun g => ψ (x * atTau θ N.V τ g))
      (hasTypeAll_iff.2 (hx x))
  obtain ⟨S, hW, hc, v, ℓ, C, hex⟩ := hx'
  have hmv := GlobalTheory.SeriesToClosure.moves_avg hθ hfr hfrJ hσ₂ he ψ x S v ℓ C hW hc hex
  have hy : HasTypeAll (lieSet (N.M.ε τ)) (UJset (N.M.ε τ)) σ₂
      (GlobalTheory.SeriesToClosure.res θ N.V τ fr (GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) fr e ψ) x) :=
    ⟨S, hW, hc, _, ℓ, C, hmv⟩
  have hJ' : (fr⁻¹)ᴴ * gramAt D N.V τ * fr⁻¹ = Jm (N.M.ε τ) := by
    rw [← hfrJ]
    calc (fr⁻¹)ᴴ * (frᴴ * Jm (N.M.ε τ) * fr) * fr⁻¹ = (fr * fr⁻¹)ᴴ * Jm (N.M.ε τ) * (fr * fr⁻¹) := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [fr2]; simp
  have hfri : IsUnit fr⁻¹ := (Matrix.isUnit_nonsing_inv_iff).2 hfr
  have hii : fr⁻¹⁻¹ = fr := Matrix.nonsing_inv_nonsing_inv _ dfr
  have hb := hasTypeAll_transport _ H H σ₂ (fun g => σ₂ (fr * g * fr⁻¹)) (Jm (N.M.ε τ)) (gramAt D N.V τ) fr⁻¹
    (isUnit_Jm _) hfri hJ' (LinearIsometryEquiv.refl ℂ H) (fun g _ w => by
      show σ₂ g w = σ₂ (fr * (fr⁻¹ * g * fr⁻¹⁻¹) * fr⁻¹) w
      rw [hii]
      congr 2
      calc g = (fr * fr⁻¹) * g * (fr * fr⁻¹) := by rw [fr2]; simp
        _ = _ := by simp only [Matrix.mul_assoc]) _ hy
  have ef : (fun y => GlobalTheory.SeriesToClosure.res θ N.V τ fr (GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) fr e ψ) x
      (fr⁻¹⁻¹ * y * fr⁻¹)) = fun g => GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) fr e ψ (x * atTau θ N.V τ g) := by
    funext y
    simp only [GlobalTheory.SeriesToClosure.res]
    congr 3
    rw [hii]
    calc fr⁻¹ * (fr * y * fr⁻¹) * fr = (fr⁻¹ * fr) * y * (fr⁻¹ * fr) := by simp only [Matrix.mul_assoc]
      _ = y := by rw [fr1]; simp
  rw [ef] at hb
  exact hasTypeAll_iff.1 hb
end GlobalTheory.AvgSamePlace
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.average_isTypeAt_same_place_twist : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (τ : D.what₂.Tau) (ψ : GA D N.V → ℂ), IsAutFunSm θ N.V ψ → IsTypeAt θ N.V τ (N.S τ) ψ → ∀ (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), GlobalTheory.TypeSum.KFinFun (N.M.ε τ) e → IsTypeAt θ N.V τ (N.S τ) (GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) e ψ) := by
  first | exact @_root_.GlobalTheory.AvgSamePlace.isTypeAt_average_same_place | exact _root_.GlobalTheory.AvgSamePlace.isTypeAt_average_same_place | (intros; apply _root_.GlobalTheory.AvgSamePlace.isTypeAt_average_same_place <;> assumption)
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
namespace GlobalTheory.AvgCuspType
theorem cusp_average_isCuspOfType : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (ψ : GA D N.V → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N ψ → ∀ (τ : D.what₂.Tau) (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), GlobalTheory.TypeSum.KFinFun (N.M.ε τ) e → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N (GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) e ψ) := by
  intro D θ hθ hp N ψ hψ τ e he
  have hc : Continuous e := by obtain ⟨F, -, h1, h2, -⟩ := he; exact h2 _ h1
  refine ⟨?_, _root_.GlobalTheory.KFinCuspApprox.isCuspForm_kFinite_average θ hθ hp N τ e hc ψ hψ.1 hψ.2.1, fun τ' => ?_⟩
  · exact GlobalTheory.RealAverage.isAutFunSm_average D θ hθ N.V τ (Formalism.REAL.KG (N.M.ε τ)) (Formalism.REAL.muK (N.M.ε τ)) _
      GlobalTheory.SeriesToClosure.continuous_conjK
      (fun k => GlobalTheory.Published.AutFin.conj_mem_UH (N.M.fr_unit τ) (N.M.fr_gram τ) k) e hc ψ hψ.1
  · by_cases h : τ' = τ
    · subst h
      exact _root_.GlobalTheory.T.average_isTypeAt_same_place_twist D θ hθ hp N τ' ψ hψ.1 (hψ.2.2 τ') e he
    · exact _root_.GlobalTheory.T.average_isTypeAt_other_place_twist D θ hθ hp N τ τ' h ψ hψ.1 (hψ.2.2 τ') e he
end GlobalTheory.AvgCuspType
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.averaging_preserves_cusp_type : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (ψ : GA D N.V → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N ψ → ∀ (τ : D.what₂.Tau) (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), GlobalTheory.TypeSum.KFinFun (N.M.ε τ) e → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N (GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) e ψ) := by
  first | exact @_root_.GlobalTheory.AvgCuspType.cusp_average_isCuspOfType | exact _root_.GlobalTheory.AvgCuspType.cusp_average_isCuspOfType | (intros; apply _root_.GlobalTheory.AvgCuspType.cusp_average_isCuspOfType <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.CuspFormDecomposesIntoKFiniteComponents
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.WeilRepresentationPlaceDecomposition
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.PlacewiseDecompositionOfKAverage
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.SeriesToClosure GlobalTheory.PlaceDecomp GlobalTheory.KFinDecomp Matrix
open scoped InnerProductSpace
noncomputable section
namespace GlobalTheory.PlaceDecomp
theorem placeDecomposition_kAverage : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (U : Subgroup (GA D N.V)) (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] [∀ τ, FiniteDimensional ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (N.M.ε τ)) (W τ)) (τ : D.what₂.Tau) (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), KFinFun (N.M.ε τ) e → HasCtp θ N U (TyOf θ N ρ) τ (kAvg (N.M.ε τ) (N.M.σ τ) e) := by
  intro D θ hθ hp N U W _ _ _ ρ τ e he
  haveI : CompleteSpace (N.M.H τ) := (N.M.ds τ).1
  haveI : IsTopologicalGroup (GA D N.V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have hP := N.M.fr_unit τ
  have hJ := N.M.fr_gram τ
  have hσ : Std (N.M.ε τ) (N.M.σ τ) := std_of_isDS hp.harishChandraModules (N.M.ds τ)
  have hec : Continuous e := by obtain ⟨F, -, h1, h2, -⟩ := he; exact h2 _ h1
  have hU : ∀ k, (N.M.fr τ)⁻¹ * toMK k * N.M.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ) :=
    fun k => GlobalTheory.Published.AutFin.conj_mem_UH hP hJ k
  have hκ := GlobalTheory.SeriesToClosure.continuous_conjK (ε := N.M.ε τ) (P := N.M.fr τ)
  have hA : ∀ f, GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) e f =
      GlobalTheory.AvgOtherPlace.avgF θ N.V (muK (N.M.ε τ)) τ (fun k => (N.M.fr τ)⁻¹ * toMK k * N.M.fr τ) e f := fun f => rfl
  refine ⟨GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) e, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    fun φ _ => GlobalTheory.SeriesToClosure.moves_avg hθ hP hJ hσ he φ⟩
  · intro f hf
    exact GlobalTheory.KFinAvgSpan.continuous_avg hθ hP hJ hec hf
  · intro f f' hf hf'
    rw [hA, hA, hA]
    exact GlobalTheory.AvgOtherPlace.avgF_add _ hθ hκ hU hec hf hf'
  · intro c f _
    rw [hA, hA]
    exact GlobalTheory.AvgOtherPlace.avgF_smul _ c f
  · intro f hf
    refine ⟨_root_.GlobalTheory.AvgCuspType.cusp_average_isCuspOfType D θ hθ hp N f hf.1 τ e he, fun k hk hkf g => ?_⟩
    simp only [GlobalTheory.SeriesToClosure.avg]
    congr 1
    funext k'
    rw [mul_assoc, ← GlobalTheory.PointAtPlaceHom.comm_of_mem N.V (GlobalTheory.PointAtPlaceHom.atTau_mem N.V τ _) hkf, ← mul_assoc,
      hf.2 k hk hkf]
  · intro τ' hne f hf hT x
    haveI := GlobalTheory.AvgCoeff.coeffSpan_finiteDimensional (ρ τ')
    have hAc : Continuous fun k' : KG (N.M.ε τ) => atTau θ N.V τ ((N.M.fr τ)⁻¹ * toMK k' * N.M.fr τ) :=
      GlobalTheory.RealAverage.continuous_atTau hθ hκ hU
    have hc : ∀ k k', GlobalTheory.Published.AutFin.kAt θ N.V τ' (N.M.ε τ') (N.M.fr τ') k *
        atTau θ N.V τ ((N.M.fr τ)⁻¹ * toMK k' * N.M.fr τ) =
        atTau θ N.V τ ((N.M.fr τ)⁻¹ * toMK k' * N.M.fr τ) * GlobalTheory.Published.AutFin.kAt θ N.V τ' (N.M.ε τ') (N.M.fr τ') k :=
      fun k k' => GlobalTheory.PointAtPlaceComm.atTau_comm D θ hθ N.V τ' τ hne _
        (GlobalTheory.Published.AutFin.conj_mem_UH (N.M.fr_unit τ') (N.M.fr_gram τ') k) _ (hU k')
    have hcont : ∀ k, Continuous fun k' : KG (N.M.ε τ) => e k' *
        f (x * atTau θ N.V τ ((N.M.fr τ)⁻¹ * toMK k' * N.M.fr τ) * GlobalTheory.Published.AutFin.kAt θ N.V τ' (N.M.ε τ') (N.M.fr τ') k) :=
      fun k => hec.mul (hf.1.1.cont.comp ((continuous_const.mul hAc).mul continuous_const))
    have key := GlobalTheory.AvgCoeff.integral_mem (muK (N.M.ε τ)) (GlobalTheory.Published.AutFin.coeffSpan (ρ τ'))
      (fun k' k => e k' * f (x * atTau θ N.V τ ((N.M.fr τ)⁻¹ * toMK k' * N.M.fr τ) *
        GlobalTheory.Published.AutFin.kAt θ N.V τ' (N.M.ε τ') (N.M.fr τ') k))
      (fun k' => Submodule.smul_mem _ (e k') (hT _)) (fun k => GlobalTheory.ExpansionAverage.integrable_K (hcont k))
    have heq : (fun k => GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) e f
        (x * GlobalTheory.Published.AutFin.kAt θ N.V τ' (N.M.ε τ') (N.M.fr τ') k)) =
        fun k => ∫ k', e k' * f (x * atTau θ N.V τ ((N.M.fr τ)⁻¹ * toMK k' * N.M.fr τ) *
          GlobalTheory.Published.AutFin.kAt θ N.V τ' (N.M.ε τ') (N.M.fr τ') k) ∂(muK (N.M.ε τ)) := by
      funext k
      simp only [GlobalTheory.SeriesToClosure.avg]
      congr 1
      funext k'
      rw [mul_assoc, hc, ← mul_assoc]
    show (fun k => GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) e f
        (x * GlobalTheory.Published.AutFin.kAt θ N.V τ' (N.M.ε τ') (N.M.fr τ') k)) ∈ _
    rw [heq]
    exact key
  · intro τ' hne g hg f _
    funext x
    simp only [GlobalTheory.SeriesToClosure.avg, rTr]
    congr 1
    funext k
    rw [mul_assoc x, mul_assoc x, GlobalTheory.AvgOtherPlace.atTau_comm hθ hne (hU k) hg]
  · intro τ' hne X hX f hf
    rw [hA, hA]
    exact (GlobalTheory.AvgOtherPlace.avgF_Rder _ hθ hne hκ hU hec hf.1.1 hX).symm
end GlobalTheory.PlaceDecomp
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.SeriesToClosure GlobalTheory.PlaceDecomp GlobalTheory.KFinDecomp Matrix
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.placewise_decomposition_of_K_average : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (U : Subgroup (GA D N.V)) (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] [∀ τ, FiniteDimensional ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (N.M.ε τ)) (W τ)) (τ : D.what₂.Tau) (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), KFinFun (N.M.ε τ) e → HasCtp θ N U (TyOf θ N ρ) τ (kAvg (N.M.ε τ) (N.M.σ τ) e) := by
  exact @_root_.GlobalTheory.PlaceDecomp.placeDecomposition_kAverage
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.KFiniteIsotypicDecompositionAdditive
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.SeriesToClosure GlobalTheory.PlaceDecomp GlobalTheory.KFinDecomp Matrix
open scoped InnerProductSpace
noncomputable section
namespace GlobalTheory.KFinDecomp
theorem kFiniteDecomp_class_add : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (U : Subgroup (GA D N.V)) (f f' : GA D N.V → ℂ), f ∈ Cls θ N U → f' ∈ Cls θ N U → f + f' ∈ Cls θ N U := by
  intro D θ hθ hPr N U f f' hf hf'
  obtain ⟨⟨a1, a2, a3⟩, a4⟩ := hf
  obtain ⟨⟨b1, b2, b3⟩, b4⟩ := hf'
  refine ⟨⟨GlobalTheory.Mem.AutSpace.isAutFunSm_add a1 b1, GlobalTheory.MultMem.isCuspFun_add a1.toIsAutFun b1.toIsAutFun a2 b2,
    fun τ => _root_.GlobalTheory.CuspGKForms.isTypeAt_add_cuspForm hPr hθ a1 b1 (a3 τ) (b3 τ)⟩, fun k hk hkf g => ?_⟩
  simp only [Pi.add_apply, a4 k hk hkf g, b4 k hk hkf g]
end GlobalTheory.KFinDecomp
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.SeriesToClosure GlobalTheory.PlaceDecomp GlobalTheory.KFinDecomp Matrix
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kFinite_isotypic_decomposition_additive : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (U : Subgroup (GA D N.V)) (f f' : GA D N.V → ℂ), f ∈ Cls θ N U → f' ∈ Cls θ N U → f + f' ∈ Cls θ N U := by
  first | exact @_root_.GlobalTheory.KFinDecomp.kFiniteDecomp_class_add | exact _root_.GlobalTheory.KFinDecomp.kFiniteDecomp_class_add | (intros; apply _root_.GlobalTheory.KFinDecomp.kFiniteDecomp_class_add <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.PlaceDecompositionExistsExponentialModel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.SeriesToClosure GlobalTheory.PlaceDecomp GlobalTheory.KFinDecomp Matrix
open scoped InnerProductSpace
noncomputable section
namespace GlobalTheory.PlaceDecomp
theorem placeDecomposition_exists_exponential_model : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (τ : D.what₂.Tau) (f : GA D N.V → ℂ), IsAutFunSm θ N.V f → IsTypeAt θ N.V τ (N.S τ) f → ∀ x : GA D N.V, ∃ (S : List (List (Mx N.V.rank))) (v : ℕ → N.M.H τ) (ℓ : ℕ → (N.M.H τ →ₗ[ℂ] ℂ)) (C : ℕ → ℝ), Words (lieSet (N.M.ε τ)) S ∧ Ctrl (lieSet (N.M.ε τ)) (UJset (N.M.ε τ)) (N.M.σ τ) S ∧ Expn (N.M.ε τ) (N.M.σ τ) S v ℓ C (res θ N.V τ (N.M.fr τ) f x) := by
  intro D θ hθ hPr N τ f hf hty x
  obtain ⟨H', i1, i2, σ', lam', ε', P', hE', hD', hP', hJ', hx⟩ := hty
  obtain ⟨hl, he⟩ := GlobalTheory.SignedParTest.isEnum_unique (N.M.enum τ) hE'
  subst hl he
  obtain ⟨U, hU⟩ := hPr.discreteSeriesHermitianUnique _ (N.M.ε τ) (N.M.lam τ)
    (GlobalTheory.Published.HermitianUnique.isHCParam_of_isDS (N.M.enum τ).1 (N.M.ds τ)) _ (N.M.fr τ) P'
    (N.M.fr_unit τ) hP' (N.M.fr_gram τ) hJ' _ _ (N.M.σ τ) σ' (N.M.ds τ) hD'
  have t := GlobalTheory.TypeSum.hasTypeAll_transport _ H' (N.M.H τ) (fun g => σ' (P' * g * P'⁻¹)) (N.M.σ τ)
    (gramAt D N.V τ) (Formalism.REAL.Jm (N.M.ε τ)) (N.M.fr τ) (isUnit_gram (N.M.fr_unit τ) (N.M.fr_gram τ))
    (N.M.fr_unit τ) (N.M.fr_gram τ) U hU (fun g => f (x * atTau θ N.V τ g))
    (GlobalTheory.TypeSum.hasTypeAll_iff.2 (hx x))
  obtain ⟨S, hS, hc, v, ℓ, C, h⟩ := t
  exact ⟨S, v, ℓ, C, hS, hc, h⟩
end GlobalTheory.PlaceDecomp
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.SeriesToClosure GlobalTheory.PlaceDecomp GlobalTheory.KFinDecomp Matrix
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_exists_exponential_model : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (τ : D.what₂.Tau) (f : GA D N.V → ℂ), IsAutFunSm θ N.V f → IsTypeAt θ N.V τ (N.S τ) f → ∀ x : GA D N.V, ∃ (S : List (List (Mx N.V.rank))) (v : ℕ → N.M.H τ) (ℓ : ℕ → (N.M.H τ →ₗ[ℂ] ℂ)) (C : ℕ → ℝ), Words (lieSet (N.M.ε τ)) S ∧ Ctrl (lieSet (N.M.ε τ)) (UJset (N.M.ε τ)) (N.M.σ τ) S ∧ Expn (N.M.ε τ) (N.M.σ τ) S v ℓ C (res θ N.V τ (N.M.fr τ) f x) := by
  first | exact @_root_.GlobalTheory.PlaceDecomp.placeDecomposition_exists_exponential_model | exact _root_.GlobalTheory.PlaceDecomp.placeDecomposition_exists_exponential_model | (intros; apply _root_.GlobalTheory.PlaceDecomp.placeDecomposition_exists_exponential_model <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.PlaceDecompositionGkMapRankOneValues
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.SeriesToClosure GlobalTheory.PlaceDecomp GlobalTheory.KFinDecomp Matrix
open scoped InnerProductSpace
namespace GlobalTheory.PlaceDecomp
theorem placeDecomposition_gkMap_rankOne_values : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (τ : D.what₂.Tau) (φ : GA D N.V → ℂ) (S : GA D N.V → List (List (Mx N.V.rank))) (v : GA D N.V → ℕ → N.M.H τ) (ℓ : GA D N.V → ℕ → (N.M.H τ →ₗ[ℂ] ℂ)) (C : GA D N.V → ℕ → ℝ), (∀ x, Words (lieSet (N.M.ε τ)) (S x)) → (∀ x, Ctrl (lieSet (N.M.ε τ)) (UJset (N.M.ε τ)) (N.M.σ τ) (S x)) → (∀ x, Expn (N.M.ε τ) (N.M.σ τ) (S x) (v x) (ℓ x) (C x) (res θ N.V τ (N.M.fr τ) φ x)) → ∀ (c : N.M.H τ) (ψ : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ → GA D N.V → ℂ), (∀ u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ, Moves θ N.V τ (N.M.ε τ) (N.M.σ τ) (N.M.fr τ) (fun w => ⟪c, w⟫_ℂ • (u : N.M.H τ)) φ (ψ u)) → (∀ u x, ψ u x = ∑' i, ⟪c, v x i⟫_ℂ * ℓ x i u) ∧ (∀ u u', ψ (u + u') = ψ u + ψ u') ∧ (∀ (z : ℂ) u, ψ (z • u) = z • ψ u) ∧ (∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt N.M τ, ∀ u w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ, (w : N.M.H τ) = N.M.rep τ k u → ψ w = rTr N.V (atTau θ N.V τ k) (ψ u)) ∧ (∀ X ∈ lieAt N.V τ, ∀ u w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ, (w : N.M.H τ) = dRep (N.M.rep τ) X u → ψ w = Rder θ N.V τ X (ψ u)) := by
  intro D θ hθ hp N τ φ S v ℓ C hS hc h c ψ hψ
  have hσ : Std (N.M.ε τ) (N.M.σ τ) := std_of_isDS hp.harishChandraModules (N.M.ds τ)
  have hP := N.M.fr_unit τ
  haveI : CompleteSpace (N.M.H τ) := (N.M.ds τ).1
  have hJ := N.M.fr_gram τ
  have hb := fun x => (h x).sobFun (hS x) c
  have hsm : ∀ u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ, Sm (N.M.ε τ) (N.M.σ τ) u := fun u => hσ.2.2.1 _ u.2
  have key : ∀ u x, ∀ y ∈ UJset (N.M.ε τ),
      res θ N.V τ (N.M.fr τ) (ψ u) x y = ∑' i, ⟪c, v x i⟫_ℂ * ℓ x i (N.M.σ τ y u) := by
    intro u x y hy
    have := (hψ u x _ _ _ _ (hS x) (hc x) (h x)).1.2.2.2.2 y hy
    simp only [map_smul, smul_eq_mul] at this
    exact this.tsum_eq.symm
  have hval : ∀ u x, ψ u x = ∑' i, ⟪c, v x i⟫_ℂ * ℓ x i u := by
    intro u x
    have := key u x 1 (one_mem_UJ _)
    rwa [res_one hθ hP, sigma_one hσ.1] at this
  refine ⟨hval, fun u u' => funext fun x => ?_, fun z u => funext fun x => ?_, ?_, ?_⟩
  · rw [Pi.add_apply, hval, hval, hval, Submodule.coe_add]
    exact (hb x).1 _ _ (hsm u) (hsm u')
  · rw [Pi.smul_apply, hval, hval, Submodule.coe_smul, smul_eq_mul]
    exact (hb x).2.1 z _ (hsm u)
  · intro k hk u w hw
    funext x
    rw [rTr, ← res_conj hP (ψ u) x k, key u x _ (K_le_UJ hk), hval, hw]
    rfl
  · intro X hX u w hw
    funext x
    have hd := (isUnit_iff_isUnit_det _).1 hP
    have hY : N.M.fr τ * X * (N.M.fr τ)⁻¹ ∈ lieSet (N.M.ε τ) := by
      refine Transport.conj_lie (G := gramAt D N.V τ) (Matrix.nonsing_inv_mul _ hd) ?_ hX
      rw [← hJ]
      calc _ = (N.M.fr τ * (N.M.fr τ)⁻¹)ᴴ * Jm (N.M.ε τ) * (N.M.fr τ * (N.M.fr τ)⁻¹) := by
            simp only [conjTranspose_mul, Matrix.mul_assoc]
        _ = _ := by rw [Matrix.mul_nonsing_inv _ hd]; simp
    have e : (w : N.M.H τ) = dRep (N.M.σ τ) (N.M.fr τ * X * (N.M.fr τ)⁻¹) u := by
      rw [hw]
      unfold dRep
      congr 1
      funext t
      rw [Transport.exp_smul_conj hP]
      rfl
    have h1 := (hσ.hasDerivAt_sobFun (hb x) (hsm u) hY).deriv
    rw [← e] at h1
    rw [hval]
    refine h1.symm.trans ?_
    unfold Rder oneP
    congr 1
    funext t
    rw [← res_conj hP (ψ u) x, ← Transport.exp_smul_conj hP, key u x _ (exp_mem_UJ hY t)]
end GlobalTheory.PlaceDecomp
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.SeriesToClosure GlobalTheory.PlaceDecomp GlobalTheory.KFinDecomp Matrix
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_gkMap_rankOne_values : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (τ : D.what₂.Tau) (φ : GA D N.V → ℂ) (S : GA D N.V → List (List (Mx N.V.rank))) (v : GA D N.V → ℕ → N.M.H τ) (ℓ : GA D N.V → ℕ → (N.M.H τ →ₗ[ℂ] ℂ)) (C : GA D N.V → ℕ → ℝ), (∀ x, Words (lieSet (N.M.ε τ)) (S x)) → (∀ x, Ctrl (lieSet (N.M.ε τ)) (UJset (N.M.ε τ)) (N.M.σ τ) (S x)) → (∀ x, Expn (N.M.ε τ) (N.M.σ τ) (S x) (v x) (ℓ x) (C x) (res θ N.V τ (N.M.fr τ) φ x)) → ∀ (c : N.M.H τ) (ψ : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ → GA D N.V → ℂ), (∀ u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ, Moves θ N.V τ (N.M.ε τ) (N.M.σ τ) (N.M.fr τ) (fun w => ⟪c, w⟫_ℂ • (u : N.M.H τ)) φ (ψ u)) → (∀ u x, ψ u x = ∑' i, ⟪c, v x i⟫_ℂ * ℓ x i u) ∧ (∀ u u', ψ (u + u') = ψ u + ψ u') ∧ (∀ (z : ℂ) u, ψ (z • u) = z • ψ u) ∧ (∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt N.M τ, ∀ u w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ, (w : N.M.H τ) = N.M.rep τ k u → ψ w = rTr N.V (atTau θ N.V τ k) (ψ u)) ∧ (∀ X ∈ lieAt N.V τ, ∀ u w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ, (w : N.M.H τ) = dRep (N.M.rep τ) X u → ψ w = Rder θ N.V τ X (ψ u)) := by
  first | exact @_root_.GlobalTheory.PlaceDecomp.placeDecomposition_gkMap_rankOne_values | exact _root_.GlobalTheory.PlaceDecomp.placeDecomposition_gkMap_rankOne_values | (intros; apply _root_.GlobalTheory.PlaceDecomp.placeDecomposition_gkMap_rankOne_values <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.PlaceDecompositionHasCtpOfIsClosed
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.SeriesToClosure GlobalTheory.PlaceDecomp GlobalTheory.KFinDecomp Matrix
open scoped InnerProductSpace
noncomputable section
namespace GlobalTheory.PlaceDecomp
theorem placeDecomposition_hasCtp_of_isClosed : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (U : Subgroup (GA D N.V)) (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (N.M.ε τ)) (W τ)) (τ : D.what₂.Tau), (∀ f f' : GA D N.V → ℂ, f ∈ Cls θ N U → f' ∈ Cls θ N U → f + f' ∈ Cls θ N U) → (0 : GA D N.V → ℂ) ∈ Cls θ N U → (∀ (c : ℂ) (f : GA D N.V → ℂ), f ∈ Cls θ N U → c • f ∈ Cls θ N U) → (∀ T T' : N.M.H τ → N.M.H τ, HasCtp θ N U (TyOf θ N ρ) τ T → HasCtp θ N U (TyOf θ N ρ) τ T' → HasCtp θ N U (TyOf θ N ρ) τ (fun w => T w + T' w) ∧ HasCtp θ N U (TyOf θ N ρ) τ (fun w => T (T' w))) ∧ (∀ (c : ℂ) (T : N.M.H τ → N.M.H τ), HasCtp θ N U (TyOf θ N ρ) τ T → HasCtp θ N U (TyOf θ N ρ) τ (fun w => c • T w)) ∧ HasCtp θ N U (TyOf θ N ρ) τ (fun _ => 0) := by
  intro D θ _ hp N U W _ _ ρ τ hadd _ hsmul
  haveI : CompleteSpace (N.M.H τ) := (N.M.ds τ).1
  have hσ := (std_of_isDS hp.harishChandraModules (N.M.ds τ)).1
  have hs : ∀ (c : ℂ) (T : N.M.H τ → N.M.H τ), HasCtp θ N U (TyOf θ N ρ) τ T →
      HasCtp θ N U (TyOf θ N ρ) τ (fun w => c • T w) := by
    rintro c T ⟨A, hA, hm⟩
    refine ⟨fun φ => c • A φ, ⟨fun f hf => (hA.cont f hf).const_smul c, fun f f' hf hf' => ?_, fun a f hf => ?_,
      fun f hf => hsmul c _ (hA.maps f hf), fun τ' h f hf ht x => ?_, fun τ' h g hg f hf => ?_,
      fun τ' h X hX f hf => ?_⟩, fun φ hφ x S v ℓ C hS hc h => (hm φ hφ x S v ℓ C hS hc h).smul hσ hS c⟩
    · simp only [hA.add f f' hf hf', smul_add]
    · simp only [hA.smul a f hf, smul_comm c a]
    · exact Submodule.smul_mem _ c (hA.keep τ' h f hf ht x)
    · simp only [hA.tr τ' h g hg f hf]
      rfl
    · simp only [hA.lie τ' h X hX f hf, GlobalTheory.Mem.AutSpace.Rder_smul]
  refine ⟨?_, hs, ?_⟩
  · rintro T T' ⟨A, hA, hm⟩ ⟨A', hA', hm'⟩
    refine ⟨⟨fun φ => A φ + A' φ, ⟨fun f hf => (hA.cont f hf).add (hA'.cont f hf), fun f f' hf hf' => ?_,
      fun a f hf => ?_, fun f hf => hadd _ _ (hA.maps f hf) (hA'.maps f hf), fun τ' h f hf ht x => ?_,
      fun τ' h g hg f hf => ?_, fun τ' h X hX f hf => ?_⟩,
      fun φ hφ x S v ℓ C hS hc h => (hm φ hφ x S v ℓ C hS hc h).add hσ (hm' φ hφ x S v ℓ C hS hc h) hS⟩,
      ⟨fun φ => A (A' φ), ⟨fun f hf => hA.cont _ (hA'.cont f hf), fun f f' hf hf' => ?_, fun a f hf => ?_,
      fun f hf => hA.maps _ (hA'.maps f hf), fun τ' h f hf ht => hA.keep τ' h _ (hA'.maps f hf) (hA'.keep τ' h f hf ht),
      fun τ' h g hg f hf => ?_, fun τ' h X hX f hf => ?_⟩,
      fun φ hφ x S v ℓ C hS hc h => hm _ (hA'.maps φ hφ) x S _ ℓ C hS hc (hm' φ hφ x S v ℓ C hS hc h)⟩⟩
    · simp only [hA.add f f' hf hf', hA'.add f f' hf hf']
      abel
    · simp only [hA.smul a f hf, hA'.smul a f hf, smul_add]
    · exact Submodule.add_mem _ (hA.keep τ' h f hf ht x) (hA'.keep τ' h f hf ht x)
    · simp only [hA.tr τ' h g hg f hf, hA'.tr τ' h g hg f hf]
      rfl
    · simp only [hA.lie τ' h X hX f hf, hA'.lie τ' h X hX f hf]
      exact (GlobalTheory.Mem.AutSpace.Rder_add (hA.maps f hf).1.1.smooth (hA'.maps f hf).1.1.smooth hX).symm
    · simp only [hA'.add f f' hf hf', hA.add _ _ (hA'.cont f hf) (hA'.cont f' hf')]
    · simp only [hA'.smul a f hf, hA.smul a _ (hA'.cont f hf)]
    · simp only [hA'.tr τ' h g hg f hf, hA.tr τ' h g hg _ (hA'.maps f hf)]
    · simp only [hA'.lie τ' h X hX f hf, hA.lie τ' h X hX _ (hA'.maps f hf)]
  · simpa using hs 0 _ (hasCtp_id θ N U _ τ)
end GlobalTheory.PlaceDecomp
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.SeriesToClosure GlobalTheory.PlaceDecomp GlobalTheory.KFinDecomp Matrix
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_placeDecomposition_hasCtp : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (U : Subgroup (GA D N.V)) (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (N.M.ε τ)) (W τ)) (τ : D.what₂.Tau), (∀ f f' : GA D N.V → ℂ, f ∈ Cls θ N U → f' ∈ Cls θ N U → f + f' ∈ Cls θ N U) → (0 : GA D N.V → ℂ) ∈ Cls θ N U → (∀ (c : ℂ) (f : GA D N.V → ℂ), f ∈ Cls θ N U → c • f ∈ Cls θ N U) → (∀ T T' : N.M.H τ → N.M.H τ, HasCtp θ N U (TyOf θ N ρ) τ T → HasCtp θ N U (TyOf θ N ρ) τ T' → HasCtp θ N U (TyOf θ N ρ) τ (fun w => T w + T' w) ∧ HasCtp θ N U (TyOf θ N ρ) τ (fun w => T (T' w))) ∧ (∀ (c : ℂ) (T : N.M.H τ → N.M.H τ), HasCtp θ N U (TyOf θ N ρ) τ T → HasCtp θ N U (TyOf θ N ρ) τ (fun w => c • T w)) ∧ HasCtp θ N U (TyOf θ N ρ) τ (fun _ => 0) := by
  first | exact @_root_.GlobalTheory.PlaceDecomp.placeDecomposition_hasCtp_of_isClosed | exact _root_.GlobalTheory.PlaceDecomp.placeDecomposition_hasCtp_of_isClosed | (intros; apply _root_.GlobalTheory.PlaceDecomp.placeDecomposition_hasCtp_of_isClosed <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.PlacewiseDecompositionTranslationInvariant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.SeriesToClosure GlobalTheory.PlaceDecomp GlobalTheory.KFinDecomp Matrix
open scoped InnerProductSpace
noncomputable section
namespace GlobalTheory.PlaceDecomp
theorem placeDecomposition_translate : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (U : Subgroup (GA D N.V)) (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (N.M.ε τ)) (W τ)) (τ : D.what₂.Tau), ∀ g ∈ UJset (N.M.ε τ), HasCtp θ N U (TyOf θ N ρ) τ (N.M.σ τ g) := by
  intro D θ hθ hp N U W _ _ ρ τ g hg
  haveI : IsTopologicalGroup (GA D N.V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have hP := N.M.fr_unit τ
  have hJ := N.M.fr_gram τ
  haveI : CompleteSpace (N.M.H τ) := (N.M.ds τ).1
  have hσ : Std (N.M.ε τ) (N.M.σ τ) := std_of_isDS hp.harishChandraModules (N.M.ds τ)
  have hk : (N.M.fr τ)⁻¹ * g * N.M.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ) := conj_inv_mem hP hJ hg
  have comm : ∀ τ', τ' ≠ τ → ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ'),
      atTau θ N.V τ ((N.M.fr τ)⁻¹ * g * N.M.fr τ) * atTau θ N.V τ' h =
        atTau θ N.V τ' h * atTau θ N.V τ ((N.M.fr τ)⁻¹ * g * N.M.fr τ) :=
    fun τ' hne h hh => GlobalTheory.PointAtPlaceComm.atTau_comm D θ hθ N.V τ τ' (Ne.symm hne) _ hk h hh
  refine ⟨rTr N.V (atTau θ N.V τ ((N.M.fr τ)⁻¹ * g * N.M.fr τ)), ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro f hf
    exact hf.comp (continuous_mul_const _)
  · intro f f' _ _
    rfl
  · intro c f _
    rfl
  · rintro f ⟨⟨a1, a2, a3⟩, a4⟩
    refine ⟨⟨GlobalTheory.Mem.RealTranslate.isAutFunSm_rTr_atTau D θ hθ N.V f a1 τ _ hk, GlobalTheory.Cusp.isCuspFun_rTr a2 _,
      fun τ' => GlobalTheory.CuspGKForms.isTypeAt_rTr hθ (a3 τ') hk⟩, fun k hkU hkf x => ?_⟩
    simp only [rTr]
    rw [mul_assoc x, ← GlobalTheory.PointAtPlaceHom.comm_of_mem N.V (GlobalTheory.PointAtPlaceHom.atTau_mem N.V τ _) hkf, ← mul_assoc x]
    exact a4 k hkU hkf _
  · intro τ' hne f _ hf x
    have e : (fun k => rTr N.V (atTau θ N.V τ ((N.M.fr τ)⁻¹ * g * N.M.fr τ)) f
        (x * GlobalTheory.Published.AutFin.kAt θ N.V τ' (N.M.ε τ') (N.M.fr τ') k)) =
        fun k => f (x * atTau θ N.V τ ((N.M.fr τ)⁻¹ * g * N.M.fr τ) *
          GlobalTheory.Published.AutFin.kAt θ N.V τ' (N.M.ε τ') (N.M.fr τ') k) := funext fun k => by
      simp only [rTr, GlobalTheory.Published.AutFin.kAt]
      rw [mul_assoc x, mul_assoc x, comm τ' hne _
        (GlobalTheory.Published.AutFin.conj_mem_UH (N.M.fr_unit τ') (N.M.fr_gram τ') k)]
    show (fun k => _) ∈ _
    rw [e]
    exact hf _
  · intro τ' hne h hh f _
    funext x
    simp only [rTr]
    rw [mul_assoc x, mul_assoc x, comm τ' hne h hh]
  · intro τ' hne X hX f _
    funext x
    simp only [Rder, rTr, oneP]
    congr 1
    funext t
    rw [mul_assoc x, mul_assoc x, comm τ' hne _
      (GlobalTheory.SmoothAutCheck.exp_mem_UH (GlobalTheory.SmoothAutCheck.gramAt_unit N.V τ') hX t)]
  · intro φ _ x S v ℓ C hS _ h
    exact h.translate hσ.1 hS hg fun y hy => by
      simp only [res, rTr, at_mul hθ hP hJ hy hg, mul_assoc x]
end GlobalTheory.PlaceDecomp
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.SeriesToClosure GlobalTheory.PlaceDecomp GlobalTheory.KFinDecomp Matrix
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.placewise_decomposition_translation_invariant : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (U : Subgroup (GA D N.V)) (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (N.M.ε τ)) (W τ)) (τ : D.what₂.Tau), ∀ g ∈ UJset (N.M.ε τ), HasCtp θ N U (TyOf θ N ρ) τ (N.M.σ τ g) := by
  first | exact @_root_.GlobalTheory.PlaceDecomp.placeDecomposition_translate | exact _root_.GlobalTheory.PlaceDecomp.placeDecomposition_translate | (intros; apply _root_.GlobalTheory.PlaceDecomp.placeDecomposition_translate <;> assumption)
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.SeriesToClosure GlobalTheory.PlaceDecomp GlobalTheory.KFinDecomp Matrix
open scoped InnerProductSpace
theorem GlobalTheory.PlaceDecomp.weil_decomposition_at_place : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (U : Subgroup (GA D N.V)) (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] [∀ τ, FiniteDimensional ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (N.M.ε τ)) (W τ)), (∀ τ, GlobalTheory.Published.AutFin.IsContRep (ρ τ)) → ∀ τ, GlobalTheory.KFinDecomp.DecompAt θ N (GlobalTheory.KFinDecomp.Cls θ N U) (fun τ f => GlobalTheory.Published.AutFin.HasTypeAt θ N.V τ (N.M.ε τ) (N.M.fr τ) (ρ τ) f) τ := by
  intro D θ hθ hp N U W _ _ _ ρ hρ τ
  haveI : CompleteSpace (N.M.H τ) := (N.M.ds τ).1
  have hσ : Std (N.M.ε τ) (N.M.σ τ) := std_of_isDS hp.harishChandraModules (N.M.ds τ)
  obtain ⟨e, he, he1⟩ := GlobalTheory.T.exists_K_finite_reproducing_function _ (N.M.ε τ) (W τ) (ρ τ) (hρ τ)
  have hcl := _root_.GlobalTheory.T.twist_placeDecomposition_hasCtp D θ hθ hp N U W ρ τ (fun f f' hf hf' => _root_.GlobalTheory.T.kFinite_isotypic_decomposition_additive D θ hθ hp N U f f' hf hf')
    (GlobalTheory.T.cuspFormsOfVertexType_zero_mem_and_smul_mem D θ hθ N U).1 (GlobalTheory.T.cuspFormsOfVertexType_zero_mem_and_smul_mem D θ hθ N U).2
  obtain ⟨m, a, c, haK, hQ, hA⟩ := GlobalTheory.T.rankOneOperator_mem_of_translation_average_closed _ (N.M.ε τ) (N.M.H τ) (N.M.σ τ) hσ (HasCtp θ N U (TyOf θ N ρ) τ)
    (_root_.GlobalTheory.T.placewise_decomposition_translation_invariant D θ hθ hp N U W ρ τ) hcl.1 hcl.2.1 (_root_.GlobalTheory.T.placewise_decomposition_of_K_average D θ hθ hp N U W ρ τ) hcl.2.2 e he
  choose A hAop hAmv using fun j (u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ) => hA j u u.2
  have hexp := fun (f : GA D N.V → ℂ) (hf : f ∈ Cls θ N U) => _root_.GlobalTheory.T.twist_exists_exponential_model D θ hθ hp N τ f hf.1.1 (hf.1.2.2 τ)
  refine ⟨m, fun j => ⟨a j, haK j⟩, A, hAop, fun j f hf => ?_, fun f hf hTy => ?_⟩
  · choose S v ℓ C hW hc h using hexp f hf
    exact (_root_.GlobalTheory.T.twist_gkMap_rankOne_values D θ hθ hp N τ f S v ℓ C hW hc h (c j) (fun u => A j u f) fun u => hAmv j u f hf).2
  · choose S v ℓ C hW hc h using hexp f hf
    have hform := fun j => (_root_.GlobalTheory.T.twist_gkMap_rankOne_values D θ hθ hp N τ f S v ℓ C hW hc h (c j) (fun u => A j u f)
      fun u => hAmv j u f hf).1
    funext x
    have h1 := (moves_avg hθ (N.M.fr_unit τ) (N.M.fr_gram τ) hσ he f x _ _ _ _ (hW x) (hc x) (h x)).1.2.2.2.2 1
      (one_mem_UJ _)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [res_one hθ (N.M.fr_unit τ), sigma_one hσ.1, hQ, map_sum, map_smul, smul_eq_mul] at h1
    have h2 := h1.unique (hasSum_sum fun j _ => (Expn.summable_term (h x) (c j) (hσ.2.2.1 _ (haK j))).hasSum)
    have h3 : avg θ N.V τ (N.M.ε τ) (N.M.fr τ) e f x = f x := by
      have := he1 _ (hTy x)
      have h4 : f (x * atTau θ N.V τ ((N.M.fr τ)⁻¹ * toMK (1 : KG (N.M.ε τ)) * N.M.fr τ)) = f x :=
        res_one hθ (N.M.fr_unit τ) f x
      exact this.trans h4
    rw [Finset.sum_apply]
    simp only [hform]
    rw [← h2, h3]
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_representation_place_decomposition : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (U : Subgroup (GA D N.V)) (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] [∀ τ, FiniteDimensional ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (N.M.ε τ)) (W τ)), (∀ τ, GlobalTheory.Published.AutFin.IsContRep (ρ τ)) → ∀ τ, GlobalTheory.KFinDecomp.DecompAt θ N (GlobalTheory.KFinDecomp.Cls θ N U) (fun τ f => GlobalTheory.Published.AutFin.HasTypeAt θ N.V τ (N.M.ε τ) (N.M.fr τ) (ρ τ) f) τ := by
  first | exact @_root_.GlobalTheory.PlaceDecomp.weil_decomposition_at_place | exact _root_.GlobalTheory.PlaceDecomp.weil_decomposition_at_place | (intros; apply _root_.GlobalTheory.PlaceDecomp.weil_decomposition_at_place <;> assumption)
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
noncomputable section
open Classical in
theorem GlobalTheory.KFinDecomp.cuspForm_kFinite_decomposition : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (ψ : GA D N.V → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N ψ → ∀ (U : Subgroup (GA D N.V)), IsOpen (U : Set (GA D N.V)) → (∀ k ∈ U, k ∈ GfC N.V → ∀ g, ψ (g * k) = ψ g) → (∀ τ, GlobalTheory.CuspKFin.KFinAt θ N τ ψ) → ∀ (μ : Measure (GA D N.V)) (𝓕 : Set (GA D N.V)), μ.IsHaarMeasure → IsFundamentalDomain (GQ N.V) 𝓕 μ → ∃ (n : ℕ) (T₀ : Fin n → GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KMap N.M) (u : Fin n → GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec N.M), (∀ j, GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.IsGKMap θ N.M {k | k ∈ U ∧ k ∈ GfC N.V} 1 μ 𝓕 (T₀ j)) ∧ ψ = ∑ j, T₀ j (u j) := by
  intro D θ hθ hP N ψ hψ U hU hlev hK μ 𝓕 hμ h𝓕
  choose W i1 i2 i3 ρ hρc hρ using hK
  letI := i1; letI := i2; letI := i3
  obtain ⟨n, T₀, u, hv, hk, hl, he⟩ := GlobalTheory.T.kFiniteDecomposition_assemble_realPlaces D θ N (GlobalTheory.KFinDecomp.Cls θ N U)
    (fun τ f => GlobalTheory.Published.AutFin.HasTypeAt θ N.V τ (N.M.ε τ) (N.M.fr τ) (ρ τ) f)
    (fun f hf => hf.1.1.cont) (_root_.GlobalTheory.T.weil_representation_place_decomposition D θ hθ hP N U W ρ hρc) ψ ⟨hψ, hlev⟩ hρ
  refine ⟨n, T₀, u, fun j => ?_, he⟩
  have hc := fun v => (hv j v).1
  refine ⟨fun v => (hc v).1.toIsAutFun, fun v => (hc v).1.smooth, fun v => (hc v).2.1,
    fun v => GlobalTheory.CuspDecay.memLp_two_of_cuspBounded hP.cuspBounded hθ (hc v).1.toIsAutFun (hc v).1.smooth
      (hc v).1.growth (hc v).2.1 μ 𝓕 hμ h𝓕,
    fun v => unifModGrowth_of_isAutFunSm hθ (hc v).1, fun v k hk g => ?_, hk j, hl j⟩
  rw [Pi.one_apply, one_mul]
  exact (hv j v).2 k hk.1 hk.2 g
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_decomposes_into_kFinite_components : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (ψ : GA D N.V → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N ψ → ∀ (U : Subgroup (GA D N.V)), IsOpen (U : Set (GA D N.V)) → (∀ k ∈ U, k ∈ GfC N.V → ∀ g, ψ (g * k) = ψ g) → (∀ τ, GlobalTheory.CuspKFin.KFinAt θ N τ ψ) → ∀ (μ : Measure (GA D N.V)) (𝓕 : Set (GA D N.V)), μ.IsHaarMeasure → IsFundamentalDomain (GQ N.V) 𝓕 μ → ∃ (n : ℕ) (T₀ : Fin n → GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KMap N.M) (u : Fin n → GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec N.M), (∀ j, GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.IsGKMap θ N.M {k | k ∈ U ∧ k ∈ GfC N.V} 1 μ 𝓕 (T₀ j)) ∧ ψ = ∑ j, T₀ j (u j) := by
  first | exact @_root_.GlobalTheory.KFinDecomp.cuspForm_kFinite_decomposition | exact _root_.GlobalTheory.KFinDecomp.cuspForm_kFinite_decomposition | (intros; apply _root_.GlobalTheory.KFinDecomp.cuspForm_kFinite_decomposition <;> assumption)
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
noncomputable section
namespace GlobalTheory.CuspKFinDecomp
theorem cusp_average_k_finite_decomposition : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (φ : GA D N.V → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N φ → ∀ (U : Subgroup (GA D N.V)), IsOpen (U : Set (GA D N.V)) → (∀ k ∈ U, k ∈ GfC N.V → ∀ g, φ (g * k) = φ g) → ∀ (e : ∀ τ, Formalism.REAL.KG (N.M.ε τ) → ℂ), (∀ τ, GlobalTheory.TypeSum.KFinFun (N.M.ε τ) (e τ)) → ∀ (l : List D.what₂.Tau), (∀ τ, τ ∈ l) → ∃ (n : ℕ) (F : Fin n → N.Maps) (v : Fin n → SmT N.M), (∀ j, F j ∈ N.Cusp θ) ∧ (∀ j, ∀ k ∈ U, k ∈ GfC N.V → ∀ g, F j (v j) (g * k) = F j (v j) g) ∧ GlobalTheory.CuspApproxAll.avgList θ N e l φ = ∑ j, F j (v j) := by
  intro D θ hθ hP N φ hφ U hU hlev e he l hl
  have key : ∀ l' : List D.what₂.Tau, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N (GlobalTheory.CuspApproxAll.avgList θ N e l' φ) ∧
      (∀ k ∈ U, k ∈ GfC N.V → ∀ g, GlobalTheory.CuspApproxAll.avgList θ N e l' φ (g * k) = GlobalTheory.CuspApproxAll.avgList θ N e l' φ g) ∧
      ∀ τ ∈ l', GlobalTheory.CuspKFin.KFinAt θ N τ (GlobalTheory.CuspApproxAll.avgList θ N e l' φ) := by
    intro l'
    induction l' with
    | nil => exact ⟨hφ, hlev, fun τ h => absurd h List.not_mem_nil⟩
    | cons τ l' ih =>
      rw [GlobalTheory.CuspApproxAll.avgList_cons]
      refine ⟨_root_.GlobalTheory.T.averaging_preserves_cusp_type D θ hθ hP N _ ih.1 τ (e τ) (he τ), avg_lev D θ hθ N _ U ih.2.1 τ (e τ), fun τ' hτ' => ?_⟩
      rcases List.mem_cons.1 hτ' with rfl | h
      · exact GlobalTheory.T.averaged_automorphic_function_K_finite D θ hθ N _ ih.1.1 τ' (e τ') (he τ')
      · exact GlobalTheory.T.average_preserves_K_finiteness D θ hθ N _ ih.1.1 τ' τ (e τ) (he τ) (ih.2.2 τ' h)
  obtain ⟨hc, hlv, hk⟩ := key l
  obtain ⟨-, 𝓕, h𝓕⟩ := GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D N.V
    (Measure.haar : Measure (GA D N.V)) inferInstance
  obtain ⟨n, T₀, u, hT₀, hsum⟩ := _root_.GlobalTheory.T.cuspForm_decomposes_into_kFinite_components D θ hθ hP N _ hc U hU hlv (fun τ => hk τ (hl τ))
    (Measure.haar : Measure (GA D N.V)) 𝓕 inferInstance h𝓕
  have hext := fun j => (GlobalTheory.GKExt.extExists hP.harishChandraModules hP.casselmanWallach D θ hθ N.V N.S N.M
    {k | k ∈ U ∧ k ∈ GfC N.V} 1 (Measure.haar : Measure (GA D N.V)) 𝓕 inferInstance h𝓕 (T₀ j) (hT₀ j)).exists
  choose T hT using hext
  have hsm : ∀ τ (w : N.M.H τ), w ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ → w ∈ N.M.sm τ := fun τ w hw =>
    (GlobalTheory.T.mem_smoothVectors_discreteSeriesModel_iff N.M τ w).2 ((GlobalTheory.TypeSum.std_of_isDS hP.harishChandraModules (N.M.ds τ)).2.2.1 w hw)
  refine ⟨n, fun j => PiTensorProduct.lift (T j),
    fun j => PiTensorProduct.tprod ℂ (fun τ => (⟨(u j τ : N.M.H τ), hsm τ _ (u j τ).2⟩ : N.M.sm τ)),
    fun j => ?_, fun j k hk hkf g => ?_, ?_⟩
  · exact N.multT_le_cusp θ {k | k ∈ U ∧ k ∈ GfC N.V} 1
      (Submodule.mem_map_of_mem (Submodule.subset_span (hT j).1))
  · rw [PiTensorProduct.lift.tprod]
    have := (hT j).1.lev (fun τ => (⟨(u j τ : N.M.H τ), hsm τ _ (u j τ).2⟩ : N.M.sm τ)) k ⟨hk, hkf⟩ g
    simpa using this
  · rw [hsum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [PiTensorProduct.lift.tprod]
    exact ((hT j).2 _ (u j) fun τ => rfl).symm
end GlobalTheory.CuspKFinDecomp
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_cusp_average_k_finite_decomposition : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (φ : GA D N.V → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N φ → ∀ (U : Subgroup (GA D N.V)), IsOpen (U : Set (GA D N.V)) → (∀ k ∈ U, k ∈ GfC N.V → ∀ g, φ (g * k) = φ g) → ∀ (e : ∀ τ, Formalism.REAL.KG (N.M.ε τ) → ℂ), (∀ τ, GlobalTheory.TypeSum.KFinFun (N.M.ε τ) (e τ)) → ∀ (l : List D.what₂.Tau), (∀ τ, τ ∈ l) → ∃ (n : ℕ) (F : Fin n → N.Maps) (v : Fin n → SmT N.M), (∀ j, F j ∈ N.Cusp θ) ∧ (∀ j, ∀ k ∈ U, k ∈ GfC N.V → ∀ g, F j (v j) (g * k) = F j (v j) g) ∧ GlobalTheory.CuspApproxAll.avgList θ N e l φ = ∑ j, F j (v j) := by
  first | exact @_root_.GlobalTheory.CuspKFinDecomp.cusp_average_k_finite_decomposition | exact _root_.GlobalTheory.CuspKFinDecomp.cusp_average_k_finite_decomposition | (intros; apply _root_.GlobalTheory.CuspKFinDecomp.cusp_average_k_finite_decomposition <;> assumption)
end
