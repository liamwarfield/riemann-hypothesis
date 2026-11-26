module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerAdditivity
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.MatrixInfinitySpan.RealMatch
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.FockLatticeHeights.HWFinal
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.FiniteMatchingK2.FinitePlacesMatch
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaCoefficientOfConvergence
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypeFromConjugateComplement

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.SchrodingerMatching.HaarFam
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory

namespace PositivityTheory.PfSWUS.SwMatch

def HaarFam : Prop :=
  ∀ (D : D7) (n : ℕ), ∃ lam : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F),
      Measure (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E),
    ∀ v, (lam v).IsAddHaarMeasure

end PositivityTheory.PfSWUS.SwMatch

end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.IwasawaReduction.ModOfCg
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsAUNeZero
open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ResAniso.ResProp
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect

theorem absAU_ne_zero {D : D7} (u : (AE D)ˣ) : absA D u ≠ 0 := by
  intro h0
  have := congrArg (absA D) (mul_inv_cancel u)
  rw [map_mul, h0, zero_mul, map_one] at this
  exact zero_ne_one this

end GlobalTheory.ResAniso.ResProp
end

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.IwaRedHand

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

theorem mod_of_cg : ∀ (D : D7) (n : ℕ) (lam : Measure (PositivityTheory.GramSchwartzFunctions.BC.hermA D n)), lam.IsAddHaarMeasure → ∀ (a : GL (Fin n) (AE D)) (f : Mx D n n → ℂ), ∫ b, f b.1 ∂lam = ((GlobalTheory.Doubling.absA D (Matrix.GeneralLinearGroup.det a) : ℝ) : ℂ) ^ n * ∫ c, f (a.1 * c.1 * GlobalTheory.MixModel.adj a.1) ∂lam := by
  intro D n lam hlam a f
  have h := GlobalTheory.T.hermitian_measure_conjugation D n lam hlam a (fun c => f c.1)
  have hr0 : 0 < absA D (Matrix.GeneralLinearGroup.det a) :=
    pos_iff_ne_zero.2 (GlobalTheory.ResAniso.ResProp.absAU_ne_zero _)
  have e : ∫ c, f (a.1 * c.1 * adj a.1) ∂lam =
      npow (absA D (Matrix.GeneralLinearGroup.det a)) (-(n : ℂ)) * ∫ b, f b.1 ∂lam := h
  have key : ((absA D (Matrix.GeneralLinearGroup.det a) : ℝ) : ℂ) ^ n *
      npow (absA D (Matrix.GeneralLinearGroup.det a)) (-(n : ℂ)) = 1 := by
    have hne : ((absA D (Matrix.GeneralLinearGroup.det a) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast hr0.ne'
    unfold npow
    rw [← Complex.cpow_natCast, ← Complex.cpow_add _ _ hne]
    simp
  rw [e, ← mul_assoc, key, one_mul]

end GlobalTheory.CompanionTheory.IwaRedHand
end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.HaarFamilies.HaarFam
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory

namespace PositivityTheory.PfSWUS.SwMatch

theorem haarFam : HaarFam := by
  intro D n
  have key : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F),
      ∃ m : Measure (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E), m.IsAddHaarMeasure := by
    intro v
    have := (GlobalTheory.LocalDensityCompare.lcs (E := D.host.E) v).1
    have := (GlobalTheory.LocalDensityCompare.lcs (E := D.host.E) v).2.1
    have := GlobalTheory.LocalDensityCompare.topRing (E := D.host.E) v
    have : BorelSpace (HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E) := ⟨rfl⟩
    have : BorelSpace (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E) := Pi.borelSpace
    exact ⟨Measure.addHaar, inferInstance⟩
  choose lam hlam using key
  exact ⟨lam, hlam⟩

end PositivityTheory.PfSWUS.SwMatch

end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.MatrixInfinitySpan.RealConj
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.PfSWUS.SwSpan

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS.SwMatch

theorem matInf_map {D : D7} (θ : InfFam D) (τ : D.what₂.Tau) {n : ℕ} (X : Mx D n n) :
    (PositivityTheory.SiegelWeilFormula.Gen.matInf X).map (θ τ) = compAt θ τ X := by
  ext i j
  rfl

theorem aTau_val {D : D7} (θ : InfFam D) {n : ℕ} (a : GL (Fin n) (AE D)) (τ : D.what₂.Tau) :
    (aTau θ a τ).1 = compAt θ τ a.1 := rfl

theorem realConj : RealConj := by
  intro D θ hθ n a b
  unfold PositivityTheory.SiegelWeilFormula.Gen.nuInf
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hA : ((aTau θ a τ)⁻¹).1 * compAt θ τ a.1 = 1 := by
    rw [← aTau_val, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one]
  have hc : compAt θ τ (conjH a b).1 = compAt θ τ a.1 * compAt θ τ b.1 * (compAt θ τ a.1)ᴴ := by
    rw [← GlobalTheory.VacKInf.LeviFix.compAt_adj' hθ τ a.1]
    show (a.1 * b.1 * adj a.1).map ((θ τ).comp (infPart D)) = _
    rw [Matrix.map_mul, Matrix.map_mul]
    rfl
  have hB : ((aTau θ a τ)⁻¹).1 * (compAt θ τ a.1 * compAt θ τ b.1 * (compAt θ τ a.1)ᴴ) *
      (((aTau θ a τ)⁻¹).1)ᴴ = compAt θ τ b.1 := by
    calc _ = (((aTau θ a τ)⁻¹).1 * compAt θ τ a.1) * compAt θ τ b.1 *
          (((aTau θ a τ)⁻¹).1 * compAt θ τ a.1)ᴴ := by
            rw [Matrix.conjTranspose_mul]
            simp only [Matrix.mul_assoc]
      _ = compAt θ τ b.1 := by rw [hA]; simp
  rw [matInf_map, matInf_map, hc, hB]
  simp

end PositivityTheory.PfSWUS.SwSpan
end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.SchrodingerMatching.Assembly
section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.SchrodingerMatching.WhitSide
section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.SchrodingerMatching.MonoSch
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.PfSWUS.SwMatch

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd GlobalTheory.CompanionTheory.SiegelND

theorem monoFock (D : D7) (n : ℕ) (V : HSp D) (θ : InfFam D) (l : D.what₂.Tau → ℝ)
    (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (φ : Mx D V.rank n → ℂ) (h : IsMonoFock θ V l s φ) :
    φ ∈ fockA θ V n l s := by
  obtain ⟨e, c, g, d, bs, gv, hp, rfl⟩ := h
  exact Submodule.subset_span ⟨_, g, GlobalTheory.CompanionTheory.WhitAdd.sb_of_pure hp, rfl⟩

def MonoSchPos : Prop :=
  ∀ (D : D7) (n : ℕ) (V : HSp D) (θ : InfFam D) (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ),
    (∀ τ, l τ ≠ 0) → (∀ τ, IsCartanInv (gramAt D V τ) (s τ)) →
    ∀ φ : Mx D V.rank n → ℂ, IsMonoFock θ V l s φ → φ ∈ schwartzA θ V.rank n ∧ φ ∈ fockA θ V n l s

theorem monoSchPos : MonoSchPos := by
  intro D n V θ l s hl hs φ h
  refine ⟨?_, monoFock D n V θ l s φ h⟩
  obtain ⟨e, c, g, d, bs, gv, hp, rfl⟩ := h
  obtain ⟨f, hf⟩ := GlobalTheory.CompanionTheory.WhitAdd.exists_schwartz_polyGauss V l hl s hs (MvPolynomial.monomial e c)
  refine Submodule.subset_span ⟨f, g, GlobalTheory.CompanionTheory.WhitAdd.sb_of_pure hp, ?_⟩
  funext x
  rw [hf]
  rfl

def MonoSchStd : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν Φ, Std D n V ψ χ θ μ ω H l s ν Φ →
    ∀ φ : Mx D V.rank n → ℂ, IsMonoFock θ V l s φ → φ ∈ schwartzA θ V.rank n ∧ φ ∈ fockA θ V n l s

theorem monoSchStd : MonoSchStd := fun D n V _ _ θ _ _ _ l s _ _ hS φ h =>
  monoSchPos D n V θ l s (GlobalTheory.CompanionTheory.WhitAdd.par_ne_zero hS) hS.hs φ h

end PositivityTheory.PfSWUS.SwMatch

end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.SchrodingerMatching.TrPairEqHalfTr
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.PfSWUS.SwMatch

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd GlobalTheory.CompanionTheory.SiegelND

variable {D : D7} {n : ℕ}

theorem trPair_eq_halfTr (S T : Mx D n n) :
    PositivityTheory.PfSWUS.Loc.trPair (AF D.host.F) S T = halfTr (Matrix.trace (HMul.hMul S T : Mx D n n)) := rfl

theorem gramR_tupInv (V : HSp D) (y : Mx D V.rank n) :
    HeckeCharacterZeroLocus.SiegelWeilU.gramR (AF D.host.F) D.sp.cm.sig (HSpace.gram V) (tupInv y) = GlobalTheory.StdUnn.inner V y y := by
  ext a c
  exact hR_tup V y y a c

theorem inner_mul_right (V : HSp D) (y : Mx D V.rank n) (a : Mx D n n) :
    GlobalTheory.StdUnn.inner V (HMul.hMul y a : Mx D V.rank n) (HMul.hMul y a : Mx D V.rank n) =
      adj a * GlobalTheory.StdUnn.inner V y y * a := by
  unfold GlobalTheory.StdUnn.inner
  rw [adj_mul]
  simp only [Matrix.mul_assoc]


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem jt_conj (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n))
    (hμ : IsCovolOne (ratMx D V.rank n) μ 𝓕) (a : GL (Fin n) (AE D)) (φ : Mx D V.rank n → ℂ) (c : hermA D n) :
    PositivityTheory.PfSWUS.Loc.jtR (AF D.host.F) D.sp.cm.sig (HSpace.gram V) ψ (μ.map tupInv)
        (fun X => φ (HMul.hMul (tupOf X) a.1)) (hermTo (conjH a c)) =
      npow (absA D (Matrix.GeneralLinearGroup.det a)) (-(V.rank : ℂ)) * Jt ψ V μ φ c := by
  obtain ⟨k1, -, -, -, -, -⟩ := lattice_Mx D V.rank n
  have : IsTopologicalAddGroup (Mx D V.rank n) := k1
  have : BorelSpace (Mx D V.rank n) := ⟨rfl⟩
  have : BorelSpace (Fin n → Fin V.rank → AE D) := borel_tup
  unfold Jt
  rw [← GlobalTheory.RightMulJac.integral_mul_right D V.rank n μ 𝓕 hμ a]
  refine (integral_map_of tupInv tupOf tupOf_tupInv tupInv_tupOf tupInv_add continuous_tupInv continuous_tupOf μ
    (fun Y => φ (HMul.hMul (tupOf Y) a.1) * ψ (PositivityTheory.PfSWUS.Loc.trPair (AF D.host.F) (conjH a c).1
      (HeckeCharacterZeroLocus.SiegelWeilU.gramR (AF D.host.F) D.sp.cm.sig (HSpace.gram V) Y)))).trans ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  change φ (HMul.hMul y a.1) * ψ (PositivityTheory.PfSWUS.Loc.trPair (AF D.host.F) (conjH a c).1
      (HeckeCharacterZeroLocus.SiegelWeilU.gramR (AF D.host.F) D.sp.cm.sig (HSpace.gram V) (tupInv y))) =
    φ (HMul.hMul y a.1) * ψ (halfTr (Matrix.trace (HMul.hMul c.1
      (GlobalTheory.StdUnn.inner V (HMul.hMul y a.1 : Mx D V.rank n) (HMul.hMul y a.1 : Mx D V.rank n)) : Mx D n n)))
  rw [gramR_tupInv, trPair_eq_halfTr, inner_mul_right]
  have e : Matrix.trace (a.1 * c.1 * adj a.1 * GlobalTheory.StdUnn.inner V y y) =
      Matrix.trace (c.1 * (adj a.1 * GlobalTheory.StdUnn.inner V y y * a.1)) := by
    rw [← Matrix.mul_assoc c.1, Matrix.trace_mul_comm _ a.1]
    simp only [Matrix.mul_assoc]
  exact congrArg (fun z => φ (HMul.hMul y a.1) * ψ (halfTr z)) e

theorem char_conj (ψ : AddChar (AF D.host.F) ℂ) (β : HermE D n) (a : GL (Fin n) (AE D)) (c : hermA D n) :
    ψ (-PositivityTheory.PfSWUS.Loc.trPair (AF D.host.F) (β.1.map (HeckeCharacterZeroLocus.SiegelWeilU.inclR (AF D.host.F))) (hermTo (conjH a c)).1) =
      ψ (-halfTr (Matrix.trace (HMul.hMul (adj a.1 * β.1.map (incA D) * a.1) c.1 : Mx D n n))) := by
  have e : Matrix.trace (β.1.map (incA D) * (a.1 * c.1 * adj a.1)) =
      Matrix.trace (adj a.1 * β.1.map (incA D) * a.1 * c.1) := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm _ (adj a.1)]
    simp only [Matrix.mul_assoc]
  exact congrArg (fun z => ψ (-z))
    ((trPair_eq_halfTr (D := D) (β.1.map (incA D)) (a.1 * c.1 * adj a.1)).trans (congrArg halfTr e))

end PositivityTheory.PfSWUS.SwMatch

end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.SchrodingerMatching.IntegrableWhitOfUnfold
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.PfSWUS.SwMatch

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd GlobalTheory.CompanionTheory.SiegelND

variable {D : D7} {n : ℕ}

private theorem conjH_cancel (a a' : GL (Fin n) (AE D)) (h : a * a' = 1) (b : hermA D n) :
    conjH a (conjH a' b) = b := by
  have h1 : a.1 * a'.1 = 1 := by rw [← Units.val_mul, h, Units.val_one]
  have h2 : adj a'.1 * adj a.1 = 1 := by rw [← adj_mul, h1, adj_one]
  refine Subtype.ext ?_
  change a.1 * (a'.1 * b.1 * adj a'.1) * adj a.1 = b.1
  calc a.1 * (a'.1 * b.1 * adj a'.1) * adj a.1 = (a.1 * a'.1) * b.1 * (adj a'.1 * adj a.1) := by
        simp only [mul_assoc]
    _ = b.1 := by rw [h1, h2, one_mul, mul_one]

private theorem conjH_add' (a : GL (Fin n) (AE D)) (b c : hermA D n) :
    conjH a (b + c) = conjH a b + conjH a c := by
  refine Subtype.ext ?_
  change a.1 * (b.1 + c.1) * adj a.1 = a.1 * b.1 * adj a.1 + a.1 * c.1 * adj a.1
  rw [mul_add, add_mul]

private theorem continuous_conjH' (a : GL (Fin n) (AE D)) : Continuous (conjH (D := D) a) := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  exact ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const).subtype_mk _


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem integrable_comp_conjH (lam : Measure (hermA D n)) (hlam : lam.IsAddHaarMeasure) (a : GL (Fin n) (AE D))
    {f : hermA D n → ℂ} (hf : Integrable f lam) : Integrable (fun b => f (conjH a b)) lam := by
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D n n
  have : IsTopologicalAddGroup (Mx D n n) := i1
  have : LocallyCompactSpace (Mx D n n) := i2
  have : SecondCountableTopology (Mx D n n) := i3
  have : T2Space (Mx D n n) := i4
  have : BorelSpace (Mx D n n) := ⟨rfl⟩
  have : SecondCountableTopology (hermA D n) := Topology.IsInducing.subtypeVal.secondCountableTopology
  have : T2Space (hermA D n) := Topology.IsEmbedding.subtypeVal.t2Space
  have : LocallyCompactSpace (hermA D n) := (GlobalTheory.CompanionTheory.HermVol.isClosed_hermA (D := D) (r := n)).locallyCompactSpace
  have : BorelSpace (hermA D n) := Subtype.borelSpace _
  let e : hermA D n ≃+ hermA D n :=
    { toFun := conjH a, invFun := conjH a⁻¹
      left_inv := conjH_cancel a⁻¹ a (inv_mul_cancel a)
      right_inv := conjH_cancel a a⁻¹ (mul_inv_cancel a)
      map_add' := conjH_add' a }
  have hc : Continuous e := continuous_conjH' a
  have hc' : Continuous e.symm := continuous_conjH' a⁻¹
  have : (lam.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map lam hc hc'
  have h1 := Measure.isAddLeftInvariant_eq_smul (lam.map e) lam
  have h2 : Integrable f (lam.map e) := by
    rw [h1]
    exact hf.smul_measure_nnreal
  exact h2.comp_aemeasurable hc.measurable.aemeasurable

private theorem sect_wn {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D}
    {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)}
    (hω : IsWeilSch ψ χ θ V μ ω) (H : G D n → ℝ≥0) {nb : hermA D n → G D n} (hnb : IsNMap nb)
    {w : G D n} (hw : mat w = blk4 0 1 (-1) 0) (Φ : schwartzA θ V.rank n) (z : ℂ) (b : hermA D n) :
    sect ω H Φ z (w * nb b) = npow (H (w * nb b)) (z - s0 V n) * Jt ψ V μ Φ.1 b := by
  unfold sect
  congr 1
  rw [map_mul, mul_apply_eq_comp, hω.weyl w hw]
  unfold Jt
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  have h0 : GlobalTheory.StdUnn.inner V (0 : Mx D V.rank n) y = 0 := by
    ext i j
    simp [GlobalTheory.StdUnn.inner, adj, Matrix.mul_apply]
  beta_reduce
  rw [hω.unip (nb b) b.1 (hnb b), h0, Matrix.trace_zero, trA, map_zero, AddChar.map_zero_eq_one, mul_one, mul_comm]


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem integrable_whit_of_unfold (hU : Unfold) :
    ∀ D n V ψ χ θ μ ω H l s ν Φ, Std D n V ψ χ θ μ ω H l s ν Φ → InRange V n →
    ∀ (lam : Measure (hermA D n)) (𝓖 : Set (hermA D n)) (nb : hermA D n → G D n), CoefData nb lam 𝓖 →
    ∀ w : G D n, mat w = blk4 0 1 (-1) 0 → ∀ (β : HermE D n), β.1.det ≠ 0 →
    ∀ φ : Mx D V.rank n → ℂ, φ ∈ schwartzA θ V.rank n → φ ∈ fockA θ V n l s →
    ∀ (T : Mx D n n) (z : ℂ), (n : ℝ) / 2 < z.re →
      Integrable (fun b : hermA D n => npow (H (w * nb b)) (z - s0 V n) * Jt ψ V μ φ b *
        ψ (-halfTr (Matrix.trace (HMul.hMul T b.1 : Mx D n n)))) lam := by
  intro D n V ψ χ θ μ ω H l s ν Φ hS hR lam 𝓖 nb hC w hw β hβ φ hsch hfock T z hz
  have hS' : Std D n V ψ χ θ μ ω H l s ν ⟨φ, hsch⟩ :=
    ⟨hS.hψ, hS.hχ, hS.hη, hS.hθ, hS.hμ, hS.hω, hS.hH, hS.hl, hS.hs, hS.hν, hfock⟩
  have h1 := (hU D n V ψ χ θ μ ω H l s ν ⟨φ, hsch⟩ hS' hR nb lam 𝓖 hC w hw β hβ z hz 1).1
  have h2 : Integrable (fun b : hermA D n => npow (H (w * nb b)) (z - s0 V n) * Jt ψ V μ φ b) lam := by
    refine h1.congr (Filter.Eventually.of_forall fun b => ?_)
    beta_reduce
    rw [mul_one]
    exact sect_wn hS.hω H hC.1 hw ⟨φ, hsch⟩ z b
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D n n
  have : IsTopologicalAddGroup (Mx D n n) := i1
  have : SecondCountableTopology (Mx D n n) := i3
  have : BorelSpace (Mx D n n) := ⟨rfl⟩
  have : SecondCountableTopology (hermA D n) := Topology.IsInducing.subtypeVal.secondCountableTopology
  have : BorelSpace (hermA D n) := Subtype.borelSpace _
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have ht : Continuous (Algebra.trace (AF D.host.F) (AE D)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF D.host.F) (AE D))
  have hc : Continuous fun b : hermA D n => ψ (-halfTr (Matrix.trace (HMul.hMul T b.1 : Mx D n n))) := by
    unfold halfTr
    exact hS.hψ.1.comp (continuous_const.mul (ht.comp
      ((continuous_const.matrix_mul continuous_subtype_val).matrix_trace))).neg
  exact h2.mul_bdd (c := 1) hc.aestronglyMeasurable (Filter.Eventually.of_forall fun b => (hS.hψ.2.1 _).le)

end PositivityTheory.PfSWUS.SwMatch

end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.SchrodingerMatching.Transport
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.PfSWUS.SwMatch

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd GlobalTheory.CompanionTheory.SiegelND

section Transport

variable {D : D7} {n : ℕ}

def hermToME : hermA D n ≃ᵐ HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF D.host.F) D.sp.cm.sig n where
  toFun := hermTo
  invFun := hermFrom
  left_inv := hermFrom_hermTo
  right_inv := hermTo_hermFrom
  measurable_toFun := by
    haveI : BorelSpace (Mx D n n) := ⟨rfl⟩
    haveI : BorelSpace (hermA D n) := Subtype.borelSpace _
    haveI : BorelSpace (HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF D.host.F) D.sp.cm.sig n) := ⟨rfl⟩
    exact continuous_hermTo.measurable
  measurable_invFun := by
    haveI : BorelSpace (Mx D n n) := ⟨rfl⟩
    haveI : BorelSpace (hermA D n) := Subtype.borelSpace _
    haveI : BorelSpace (HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF D.host.F) D.sp.cm.sig n) := ⟨rfl⟩
    exact continuous_hermFrom.measurable

theorem integral_map_hermTo (lam : Measure (hermA D n))
    (W : HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF D.host.F) D.sp.cm.sig n → ℂ) :
    ∫ b, W b ∂(lam.map hermTo) = ∫ b, W (hermTo b) ∂lam :=
  (hermToME (D := D) (n := n)).measurableEmbedding.integral_map W

theorem integrable_map_hermTo (lam : Measure (hermA D n))
    (W : HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF D.host.F) D.sp.cm.sig n → ℂ) (h : Integrable (fun b => W (hermTo b)) lam) :
    Integrable W (lam.map hermTo) :=
  ((hermToME (D := D) (n := n)).measurableEmbedding.integrable_map_iff).2 h

end Transport

end PositivityTheory.PfSWUS.SwMatch

end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.SchrodingerMatching.ConjHConjHInv
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.PfSWUS.SwMatch

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd GlobalTheory.CompanionTheory.SiegelND

variable {D : D7} {n : ℕ}

theorem conjH_conjH_inv' (a : GL (Fin n) (AE D)) (b : hermA D n) : conjH a (conjH a⁻¹ b) = b := by
  apply Subtype.ext
  change a.1 * ((a⁻¹).1 * b.1 * adj (a⁻¹).1) * adj a.1 = b.1
  have h1 : a.1 * (a⁻¹).1 = 1 := Units.mul_inv a
  have h2 : adj (a⁻¹).1 * adj a.1 = 1 := by
    rw [← adj_mul, h1]
    unfold adj
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
  calc a.1 * ((a⁻¹).1 * b.1 * adj (a⁻¹).1) * adj a.1
      = (a.1 * (a⁻¹).1) * b.1 * (adj (a⁻¹).1 * adj a.1) := by simp only [mul_assoc]
    _ = b.1 := by rw [h1, h2, one_mul, mul_one]

theorem inv_cpow_neg' (x : ℝ≥0) {w : ℂ} (hw : w ≠ 0) : (((x : ℝ)⁻¹ : ℝ) : ℂ) ^ (-w) = npow x w := by
  unfold npow
  rcases eq_or_ne x 0 with rfl | hx
  · simp [Complex.zero_cpow hw, Complex.zero_cpow (neg_ne_zero.2 hw)]
  · have hpos : (0 : ℝ) ≤ (x : ℝ) := x.2
    have harg : ((x : ℝ) : ℂ).arg ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg hpos]
      exact Real.pi_ne_zero.symm
    rw [Complex.ofReal_inv, Complex.inv_cpow _ _ harg, Complex.cpow_neg, inv_inv]

set_option maxHeartbeats 1000000 in
theorem nu_conj {θ : InfFam D} (hRc : RealConj) (hθ : IsInfFam θ) (a : GL (Fin n) (AE D))
    (lam : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F),
      Measure (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E))
    (L L₁ L₂ : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F),
      AddSubgroup (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E))
    (hnu2 : ∀ v (b : hermA D n),
      PositivityTheory.SiegelWeilFormula.Gen.nu2 (lam v) (L₁ v) (L₂ v) (PositivityTheory.SiegelWeilFormula.Gen.matV v (conjH a b).1) =
        PositivityTheory.SiegelWeilFormula.Gen.nu2 (lam v) (L v) (L v) (PositivityTheory.SiegelWeilFormula.Gen.matV v b.1)) (c : hermA D n) :
    PositivityTheory.SiegelWeilFormula.Gen.nuA θ (aTau θ a) lam L₁ L₂ (conjH a c).1 = PositivityTheory.SiegelWeilFormula.Gen.nuA θ (fun _ => 1) lam L L c.1 := by
  exact congrArg₂ (· * ·) (hRc D θ hθ n a c) (finprod_congr fun v => hnu2 v c)

end PositivityTheory.PfSWUS.SwMatch

end
end

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.PfSWUS.SwMatch

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd GlobalTheory.CompanionTheory.SiegelND


set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem whit_side (hRc : RealConj) (hM : ConjMod) (hU : Unfold) (hK : HeightKInv)
    {D : D7} {n : ℕ} {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D}
    {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} {H : G D n → ℝ≥0}
    {l : D.what₂.Tau → ℝ} {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ν : Measure (GA D V)}
    {Φ : schwartzA θ V.rank n} (hstd : Std D n V ψ χ θ μ ω H l s ν Φ) (hrange : InRange V n)
    {lam : Measure (hermA D n)} {𝓖 : Set (hermA D n)} {nb : hermA D n → G D n} (hcd : CoefData nb lam 𝓖)
    {w : G D n} (hw : mat w = blk4 0 1 (-1) 0) {β : HermE D n} (hβ : β.1.det ≠ 0) (a : GL (Fin n) (AE D))
    {k : G D n} (hk : k ∈ K D n) {φ : Mx D V.rank n → ℂ} (hsch : φ ∈ schwartzA θ V.rank n) (hfock : φ ∈ fockA θ V n l s)
    (lamS : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F),
      Measure (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E))
    (hlamS : ∀ v, (lamS v).IsAddHaarMeasure)
    (L L₁ L₂ : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F),
      AddSubgroup (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E))
    (hLnu : ∀ lam : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F),
        Measure (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E),
      (∀ v, (lam v).IsAddHaarMeasure) →
      ∀ b : hermA D n, ((H (w * nb b) : ℝ))⁻¹ = PositivityTheory.SiegelWeilFormula.Gen.nuA θ (fun _ => 1) lam L L b.1)
    (hnu2 : ∀ v (b : hermA D n),
      PositivityTheory.SiegelWeilFormula.Gen.nu2 (lamS v) (L₁ v) (L₂ v) (PositivityTheory.SiegelWeilFormula.Gen.matV v (conjH a b).1) =
        PositivityTheory.SiegelWeilFormula.Gen.nu2 (lamS v) (L v) (L v) (PositivityTheory.SiegelWeilFormula.Gen.matV v b.1))
    (𝓕μ : Set (Mx D V.rank n)) (hμ : IsCovolOne (ratMx D V.rank n) μ 𝓕μ) :
    ∃ t : ℝ, ∀ z : ℂ, t < z.re →
      Integrable (PositivityTheory.SiegelWeilFormula.Gen.whI (HeckeCharacterZeroLocus.SiegelWeilU.AF D.host.F) D.sp.cm.sig (HSpace.gram V) ψ (μ.map tupInv)
        (fun X => φ (HMul.hMul (tupOf X) a.1))
        (PositivityTheory.SiegelWeilFormula.Gen.nuA θ (aTau θ a) lamS L₁ L₂) (β.1.map (HeckeCharacterZeroLocus.SiegelWeilU.inclR (HeckeCharacterZeroLocus.SiegelWeilU.AF D.host.F))) z)
        (lam.map hermTo) ∧
      whitT ψ V μ lam nb w H φ (adj a.1 * β.1.map (incA D) * a.1) k z =
        npow (absA D (Matrix.GeneralLinearGroup.det a)) ((V.rank : ℂ) - n) *
          ∫ b, PositivityTheory.SiegelWeilFormula.Gen.whI (HeckeCharacterZeroLocus.SiegelWeilU.AF D.host.F) D.sp.cm.sig (HSpace.gram V) ψ (μ.map tupInv)
            (fun X => φ (HMul.hMul (tupOf X) a.1))
            (PositivityTheory.SiegelWeilFormula.Gen.nuA θ (aTau θ a) lamS L₁ L₂)
            (β.1.map (HeckeCharacterZeroLocus.SiegelWeilU.inclR (HeckeCharacterZeroLocus.SiegelWeilU.AF D.host.F))) z b ∂(lam.map hermTo) := by
  classical
  refine ⟨(n : ℝ) / 2, fun z hz => ?_⟩
  set r : ℝ≥0 := absA D (Matrix.GeneralLinearGroup.det a) with hr
  have hr0 : r ≠ 0 := ((Group.isUnit (Matrix.GeneralLinearGroup.det a)).map (absA D)).ne_zero
  set T : Mx D n n := adj a.1 * β.1.map (incA D) * a.1 with hT

  set I : hermA D n → ℂ := fun c => npow (H (w * nb c * k)) (z - s0 V n) * Jt ψ V μ φ c *
    ψ (-halfTr (Matrix.trace (HMul.hMul T c.1 : Mx D n n))) with hI
  set W := PositivityTheory.SiegelWeilFormula.Gen.whI (HeckeCharacterZeroLocus.SiegelWeilU.AF D.host.F) D.sp.cm.sig (HSpace.gram V) ψ (μ.map tupInv)
        (fun X => φ (HMul.hMul (tupOf X) a.1))
        (PositivityTheory.SiegelWeilFormula.Gen.nuA θ (aTau θ a) lamS L₁ L₂) (β.1.map (HeckeCharacterZeroLocus.SiegelWeilU.inclR (HeckeCharacterZeroLocus.SiegelWeilU.AF D.host.F))) z
    with hW
  have hzs : z - s0 V n ≠ 0 := by
    intro h0
    have hre := congrArg Complex.re h0
    simp only [s0, Complex.sub_re, Complex.div_re, Complex.natCast_re, Complex.natCast_im, Complex.zero_re] at hre
    have h2 : (V.rank : ℝ) ≤ 2 * n := by exact_mod_cast hrange.2.1
    norm_num at hre
    linarith
  have hpt : ∀ c : hermA D n, W (hermTo (conjH a c)) = npow r (-(V.rank : ℂ)) * I c := by
    intro c
    have h1 := nu_conj hRc hstd.hθ a lamS L L₁ L₂ hnu2 c
    rw [← hLnu lamS hlamS c] at h1
    have h2 := jt_conj V ψ μ 𝓕μ hμ a φ c
    have h3 := char_conj ψ β a c
    have h4 : H (w * nb c * k) = H (w * nb c) := hK D n H hstd.hH (w * nb c) k hk
    have h5 : ((V.rank : ℂ) - n) / 2 = s0 V n := by unfold s0; ring
    simp only [hW, hI, PositivityTheory.SiegelWeilFormula.Gen.whI]
    change (((PositivityTheory.SiegelWeilFormula.Gen.nuA θ (aTau θ a) lamS L₁ L₂ (conjH a c).1 : ℝ)) : ℂ) ^ (-(z - ((V.rank : ℂ) - n) / 2)) *
        PositivityTheory.PfSWUS.Loc.jtR (AF D.host.F) D.sp.cm.sig (HSpace.gram V) ψ (μ.map tupInv)
          (fun X => φ (HMul.hMul (tupOf X) a.1)) (hermTo (conjH a c)) *
        ψ (-PositivityTheory.PfSWUS.Loc.trPair (AF D.host.F) (β.1.map (HeckeCharacterZeroLocus.SiegelWeilU.inclR (AF D.host.F))) (hermTo (conjH a c)).1) = _
    rw [h1, h2, h3, h4, h5, inv_cpow_neg' _ hzs]
    ring
  have hHaar : lam.IsAddHaarMeasure := hcd.2.1
  have hIint : Integrable I lam := by
    have h := integrable_whit_of_unfold hU D n V ψ χ θ μ ω H l s ν Φ hstd hrange lam 𝓖 nb hcd w hw β hβ φ hsch hfock
      T z hz
    refine h.congr (Filter.Eventually.of_forall fun c => ?_)
    simp only [hI, hK D n H hstd.hH (w * nb c) k hk]
  have hWcomp : (fun b => W (hermTo b)) = fun b => npow r (-(V.rank : ℂ)) * I (conjH a⁻¹ b) := by
    funext b
    conv_lhs => rw [← conjH_conjH_inv' a b]
    exact hpt _
  have hrC : ((r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr0
  have key : npow r ((V.rank : ℂ) - n) * (((r : ℝ) : ℂ) ^ n * npow r (-(V.rank : ℂ))) = 1 := by
    unfold npow
    rw [← Complex.cpow_natCast, ← Complex.cpow_add _ _ hrC, ← Complex.cpow_add _ _ hrC]
    have : ((V.rank : ℂ) - n) + ((n : ℂ) + -(V.rank : ℂ)) = 0 := by ring
    rw [this, Complex.cpow_zero]
  have hwI : whitT ψ V μ lam nb w H φ T k z = ∫ c, I c ∂lam := rfl
  refine ⟨?_, ?_⟩
  · refine integrable_map_hermTo lam W ?_
    rw [hWcomp]
    exact (integrable_comp_conjH lam hHaar a⁻¹ hIint).const_mul _
  · rw [integral_map_hermTo lam W]
    have hc := hM D n lam hHaar a (fun B => if h : B ∈ hermA D n then W (hermTo ⟨B, h⟩) else 0)
    have e1 : ∫ b, (fun B => if h : B ∈ hermA D n then W (hermTo ⟨B, h⟩) else 0) b.1 ∂lam = ∫ b, W (hermTo b) ∂lam :=
      integral_congr_ae (Filter.Eventually.of_forall fun b => by
        show (if h : b.1 ∈ hermA D n then W (hermTo ⟨b.1, h⟩) else 0) = W (hermTo b)
        rw [dite_eq_left b.2])
    have e2 : ∫ c, (fun B => if h : B ∈ hermA D n then W (hermTo ⟨B, h⟩) else 0) (a.1 * c.1 * adj a.1) ∂lam =
        ∫ c, W (hermTo (conjH a c)) ∂lam :=
      integral_congr_ae (Filter.Eventually.of_forall fun c => by
        show (if h : a.1 * c.1 * adj a.1 ∈ hermA D n then W (hermTo ⟨_, h⟩) else 0) = W (hermTo (conjH a c))
        rw [dite_eq_left (show a.1 * c.1 * adj a.1 ∈ hermA D n from (conjH a c).2)]
        rfl)
    rw [← e1, hc, e2]
    simp only [hpt]
    rw [integral_const_mul, hwI]
    calc ∫ c, I c ∂lam = (npow r ((V.rank : ℂ) - n) * (((r : ℝ) : ℂ) ^ n * npow r (-(V.rank : ℂ)))) * ∫ c, I c ∂lam := by
          rw [key, one_mul]
      _ = _ := by ring

end PositivityTheory.PfSWUS.SwMatch

end
end

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.PfSWUS.SwMatch

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd GlobalTheory.CompanionTheory.SiegelND

set_option maxHeartbeats 1000000 in
theorem matchMono_of' (hψ : PsiPlaces) (hR : RealMatch) (hRc : RealConj) (hH : HeightWN) (hF : FinMatch)
    (hM : ConjMod) (hT : ValueSide) (hU : Unfold) (hK : HeightKInv) (hA : HaarFam) : MatchMono := by
  intro D n V ψ χ θ μ ω H l s ν Φ hstd hrange lam 𝓖 nb hcd w hw β hβ a k hk φ hφ
  obtain ⟨hchar, hpl⟩ := hψ D n V ψ χ θ μ ω H l s ν Φ hstd
  obtain ⟨hsch, hfock⟩ := monoSchStd D n V ψ χ θ μ ω H l s ν Φ hstd φ hφ
  obtain ⟨e, c, g, d, bs, gv, hpure, hφeq⟩ := hφ
  obtain ⟨εG, frG, PG, hfr, hreal⟩ := hR D n V ψ θ l s hstd.hθ hstd.hl hstd.hs e c a
  obtain ⟨L, hLco, hLstd, hLnu⟩ := hH D n H hstd.hH θ hstd.hθ nb hcd.1 w hw
  obtain ⟨lamS, hlamS⟩ := hA D n
  obtain ⟨L₁, L₂, Φf, Φv, hco, hstd', hpure', hΦf, hnu2⟩ :=
    hF D n V.rank a d bs g gv hpure lamS L hlamS hLco (hLstd d bs)
  obtain ⟨𝓕μ, hμ⟩ := hstd.hμ
  refine ⟨d, bs, θ, l, εG, frG, aTau θ a, PG, lamS, L₁, L₂, fun X => φ (HMul.hMul (tupOf X) a.1), Φf, Φv,
    μ.map tupInv, lam.map hermTo, ψ, ?_, npow (absA D (Matrix.GeneralLinearGroup.det a)) ((V.rank : ℂ) - n), ?_, ?_⟩
  · constructor
    · exact GlobalTheory.DefiniteQuotient.cmExt D
    · exact GlobalTheory.DefiniteQuotient.gram_hermND V
    · exact hrange.1
    · intro i j
      exact congrFun (congrFun β.2 i) j
    · exact hβ
    · exact hchar
    · exact hpl
    · exact hfr
    · exact hlamS
    · exact hco
    · exact hstd'
    · exact hpure'
    · intro X
      have h1 := hreal (tupOf X)
      have h2 := hΦf (tupOf X)
      rw [tupInv_tupOf] at h1 h2
      change φ (HMul.hMul (tupOf X) a.1) = _
      rw [hφeq]
      simp only
      rw [h1, h2]
    · exact sdW_map V hchar hμ
    · exact sdHerm_map hchar hcd.2
  · exact whit_side hRc hM hU hK hstd hrange hcd hw hβ a hk hsch hfock lamS hlamS L L₁ L₂ hLnu hnu2 𝓕μ hμ
  · intro μH 𝓕 hHaar hFD
    exact congrArg _ (hT D n V ν hstd.hν (fun x => φ (HMul.hMul x a.1)) β hβ μH 𝓕 hHaar hFD)

end PositivityTheory.PfSWUS.SwMatch

end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.SchrodingerMatching.PsiVal
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.PfSWUS.SwMatch

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd GlobalTheory.CompanionTheory.SiegelND

theorem exists_ext_infFam (D : D7) (θ : InfFam D) (hθ : IsInfFam θ) :
    ∃ θ' : (D.host.E →+* ℂ) → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ),
      (∀ φ, Formalism.MainNotions.StandardLattice.IsInfEmb φ (θ' φ)) ∧ ∀ τ, θ' (tauE D τ) = θ τ := by
  classical
  obtain ⟨θ₀, h₀⟩ := (GlobalTheory.Member.infiniteAdele_bijective D).1
  refine ⟨Function.extend (tauE D) θ θ₀, fun φ => ?_, fun τ => (GlobalTheory.MassLink.tauE_injective' D).extend_apply θ θ₀ τ⟩
  by_cases h : ∃ τ, tauE D τ = φ
  · obtain ⟨τ, rfl⟩ := h
    rw [(GlobalTheory.MassLink.tauE_injective' D).extend_apply θ θ₀ τ]
    exact hθ τ
  · rw [Function.extend_apply' θ θ₀ φ h]
    exact h₀ φ

theorem infFam_spec (D : D7) (θ : InfFam D) (hθ : IsInfFam θ) :
    (∀ τ, Continuous (θ τ)) ∧
      (∀ τ z, θ τ (sigR (Ainf D.host.F) D.sp.cm.sig z) = starRingEnd ℂ (θ τ z)) ∧
      Function.Bijective fun (z : Ainf D.host.F ⊗[D.host.F] D.host.E) τ => θ τ z := by
  obtain ⟨θ', h', e⟩ := exists_ext_infFam D θ hθ
  obtain ⟨h1, h2, h3⟩ := (GlobalTheory.Member.infiniteAdele_bijective D).2 θ' h'
  refine ⟨fun τ => e τ ▸ h1 _, fun τ z => e τ ▸ h2 _ z, ?_⟩
  have h0 : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  let ι : D.what₂.Tau → {φ : D.host.E →+* ℂ // φ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD} :=
    fun τ => ⟨tauE D τ, (Formalism.L2.Theta.tauE_sqrtMinusD D τ).trans h0.symm⟩
  have hι : Function.Bijective ι :=
    ⟨fun a b h => GlobalTheory.MassLink.tauE_injective' D (congrArg Subtype.val h), fun φ => by
      obtain ⟨τ, hτ⟩ := GlobalTheory.MassLink.tauE_surj' D φ.1 (φ.2.trans h0)
      exact ⟨τ, Subtype.ext hτ⟩⟩
  have h4 := (hι.comp_right (γ := ℂ)).comp h3
  convert h4 using 2 with z
  funext τ
  exact (congrArg (fun t => t z) (e τ)).symm

theorem psiPlaces : PsiPlaces := by
  intro D n V ψ χ θ μ ω H l s ν Φ h
  obtain ⟨h1, h2, h3⟩ := infFam_spec D θ h.hθ
  exact ⟨h.hψ, h1, h3, h2, GlobalTheory.ResAniso.VacSchwartz.realPar_ne_zero D θ h.hθ ψ h.hψ l h.hl, h.hl⟩


open GlobalTheory.CompanionTheory.SiegelND.ThetaGlue in
theorem valueSide : ValueSide := by
  intro D r V ν hν φ β hβ μH 𝓕 hμ h𝓕
  have hrank : ∀ (δ : GL (Fin V.rank) D.host.E) (ξ : Matrix (Fin V.rank) (Fin r) D.host.E),
      (δ.1 * ξ).rank = ξ.rank := fun δ ξ =>
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).1 δ.isUnit)
  have hL := GlobalTheory.CompanionTheory.SplitGram.leftInv_subtypeSum V φ
    (fun x : Matrix (Fin V.rank) (Fin r) D.host.E => x.rank = r ∧ gramQ V x = β.1)
    (fun δ hδ ξ h => ⟨(hrank δ ξ).trans h.1, (GlobalTheory.CompanionTheory.SplitGram.gramQ_mul V hδ ξ).trans h.2⟩)
  have hI := average_eq_meanC V ν μH hν hμ 𝓕 h𝓕 _ hL
  have hS : HeckeCharacterZeroLocus.SiegelWeilU.thetaS D.host.F D.host.E D.sp.cm.sig V.rank V.gram (fun X => φ (tupOf X))
      {X | HeckeCharacterZeroLocus.SiegelWeilU.gramE D.sp.cm.sig V.gram X = β.1} =
      fun h => ∑' x : {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r ∧ gramQ V x = β.1},
        φ (GlobalTheory.SiegelFormula.invPt V h x.1) := by
    funext h
    refine (tsum_congr fun X => ?_).trans ((fibEquiv V β hβ).tsum_eq
      fun x => φ (GlobalTheory.SiegelFormula.invPt V h x.1))
    exact congrArg φ (tupOf_actW V h X.1)
  exact hI.trans (congrArg (HeckeCharacterZeroLocus.SiegelWeilU.meanC μH 𝓕) hS.symm)

end PositivityTheory.PfSWUS.SwMatch

end
end

namespace PositivityTheory.PfSWUS.SwMatch

theorem matchMono : PositivityTheory.PfSWUS.MatchMono :=
  matchMono_of' psiPlaces PositivityTheory.PfSWUS.SwSpanR.realMatch PositivityTheory.PfSWUS.SwSpan.realConj PositivityTheory.PfSWUS.SwFockk.heightWN
    PositivityTheory.PfSWUS.KFinMatch.finite_places_match GlobalTheory.CompanionTheory.IwaRedHand.mod_of_cg valueSide GlobalTheory.T.unfolding_holds GlobalTheory.T.height_K_invariance haarFam

end PositivityTheory.PfSWUS.SwMatch
