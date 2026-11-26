module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumMeas
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantTermBound
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormThetaMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRatRepr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareBottomHalfRankDiffLeHalfRank

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OfE
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global
open scoped TensorProduct ENNReal NNReal Matrix Classical

namespace GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def Psi (φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ)
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E))
    (Y : Fin 1 → Fin 1 → AF F ⊗[F] E) : ℝ≥0∞ :=
  {Y : Fin 1 → Fin 1 → AF F ⊗[F] E | ∀ v, projV v (projFin Y) ∈ A v}.indicator
    (fun Y => ENNReal.ofReal (φ (projInf Y))) Y

def Th (φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ)
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E))
    (y : (AF F ⊗[F] E)ˣ) : ℝ≥0∞ :=
  ∑' X : ({X : Fin 1 → Fin 1 → E | X ≠ 0} : Set _),
    Psi φ A (fun a i => (y : AF F ⊗[F] E) * inclR (AF F) (X.1 a i))

def ofF : (AF F)ˣ →* (AF F ⊗[F] E)ˣ :=
  Units.map (Algebra.TensorProduct.includeLeft : AF F →ₐ[F] AF F ⊗[F] E).toMonoidHom

def ofE : Eˣ →* (AF F ⊗[F] E)ˣ := Units.map (inclR (AF F)).toMonoidHom

end

def cV {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) :
    AF F ⊗[F] E →ₐ[F] Fv F v ⊗[F] E :=
  (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E)).comp
    (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E))

def cI {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] :
    AF F ⊗[F] E →ₐ[F] Ainf F ⊗[F] E :=
  Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)

def ue {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) (J : Matrix (Fin 1) (Fin 1) E) (h : HA R σ J) : (R ⊗[F] E)ˣ :=
  Matrix.GeneralLinearGroup.det (HA.mat R σ J h)

end GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShAdd
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE

theorem sh_add : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (y y' : Mx D ρ p),
    M.sh y * M.sh y' = M.sh (y + y') :=
  fun M y y' => GlobalTheory.CompanionTheory.PcB.sh_mul M y y'

end GlobalTheory.CompanionTheory.FJE
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThPr
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open GroundTheory.Global PositivityTheory.Rg.Base1
open scoped ENNReal NNReal Classical

namespace GlobalTheory.CompanionTheory.BasePsi

variable {F : Type} [Field F] [NumberField F]

def phiA (G : Ainf F → ℝ) (a : (AF F)ˣ) : (Unit → Ainf F) → ℝ := fun y => G ((a : AF F).1 * y ())

def psiA (S : Finset (HeightOneSpectrum (𝓞 F))) (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ) (a : (AF F)ˣ)
    (v : HeightOneSpectrum (𝓞 F)) : (Unit → Fv F v) → ℝ := fun y =>
  if v ∈ S then g v ((a : AF F).2 v * y ())
  else if (a : AF F).2 v * y () ∈ v.adicCompletionIntegers F then 1 else 0

theorem md_mul (a b : (AF F)ˣ) : md (a * b) = md a * md b := by
  simp [md, map_mul]

theorem md_pos (a : (AF F)ˣ) : 0 < md a := (IdeleGroup.ideleModule F a).2

theorem md_pr (t : Fˣ) : md (pr t) = 1 := by
  have h := IdeleGroup.ideleModule_diagonal (K := F) t
  have h2 : pr t = IdeleGroup.diagonal F t := rfl
  rw [md, h2, h]
  rfl

theorem th_pr (f : (AF F)ˣ → ℝ≥0∞) (k : Fˣ) (a : (AF F)ˣ) : th f (pr k * a) = th f a := by
  unfold th
  rw [← (Equiv.mulRight k).tsum_eq (fun t : Fˣ => f (pr t * a))]
  refine tsum_congr fun t => ?_
  have : pr (t * k) = pr t * pr k := by simp [pr, map_mul]
  simp only [Equiv.coe_mulRight, this, mul_assoc]

end GlobalTheory.CompanionTheory.BasePsi

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentreCharacterProperties
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentreCharacterProperties
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE.CentralChar

theorem chz_facts : ∀ {D : D7} {ρ : ℕ} (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ b₀ : HermE D ρ,
    (∀ z z' : hermA D ρ, chz ψ b₀ (z + z') = chz ψ b₀ z * chz ψ b₀ z') ∧ (∀ z, ‖chz ψ b₀ z‖ = 1) ∧
      (∀ z ∈ ratHerm D ρ, chz ψ b₀ z = 1) ∧ Continuous (chz ψ b₀) := by
  intro D ρ ψ hψ b₀
  refine ⟨fun z z' => ?_, GlobalTheory.CompanionTheory.PcB.chz_norm hψ b₀, fun z hz => ?_, GlobalTheory.CompanionTheory.PcB.continuous_chz hψ b₀⟩
  · have e : (HMul.hMul (b₀.1.map (incA D)) (z + z').1 : Mx D ρ ρ) =
        (HMul.hMul (b₀.1.map (incA D)) z.1 : Mx D ρ ρ) + (HMul.hMul (b₀.1.map (incA D)) z'.1 : Mx D ρ ρ) :=
      Matrix.mul_add _ _ _
    have hadd : ∀ a c : AE D, halfTr (a + c) = halfTr a + halfTr c := fun a c => by
      simp only [halfTr, trA, map_add (f := _), mul_add]
    unfold chz
    rw [e, Matrix.trace_add, hadd, AddChar.map_add_eq_mul]
  · obtain ⟨Z, hZ⟩ := hz
    have hZ' : Z.map (incA D) = z.1 := hZ
    have e : Matrix.trace (HMul.hMul (b₀.1.map (incA D)) z.1 : Mx D ρ ρ) = incA D (Matrix.trace (b₀.1 * Z)) := by
      rw [← hZ', ← Matrix.map_mul]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]
    unfold chz
    rw [e, GlobalTheory.CompanionTheory.ThetaInv.halfTr_incA]
    exact hψ.2.2.1 _

end GlobalTheory.CompanionTheory.FJE.CentralChar
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentreCharacterPropertiesStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centre_character_properties : ∀ {D : D7} {ρ : ℕ} (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ b₀ : HermE D ρ, (∀ z z' : hermA D ρ, chz ψ b₀ (z + z') = chz ψ b₀ z * chz ψ b₀ z') ∧ (∀ z, ‖chz ψ b₀ z‖ = 1) ∧ (∀ z ∈ ratHerm D ρ, chz ψ b₀ z = 1) ∧ Continuous (chz ψ b₀) := by
  first | exact @GlobalTheory.CompanionTheory.FJE.CentralChar.chz_facts | exact GlobalTheory.CompanionTheory.FJE.CentralChar.chz_facts | (intros; apply GlobalTheory.CompanionTheory.FJE.CentralChar.chz_facts <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionLeftInvariantRationalParabolic
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionLeftInvariantRationalParabolic
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE

theorem leftInv_of_isLaw : ∀ {D : D7} {n : ℕ} (χ : (AE D)ˣ →* Circle) (s : ℂ) (f : G D n → ℂ), IsHeckeChar D χ → IsLaw χ s f → LeftInv (P D n ⊓ GF D n) f := by
  intro D n χ s f hχ hf γ hγ g
  obtain ⟨a, ha⟩ := GlobalTheory.StdUnn.LeftInvSect.exists_blkA hγ.1
  obtain ⟨u, hu⟩ := GlobalTheory.StdUnn.LeftInvSect.det_rat hγ.2 a ha
  have h1 : absA D (Units.map (incA D).toMonoidHom u) = 1 := absE_inclR u
  rw [hf γ hγ.1 a ha g, hu, hχ.2 u, h1]
  simp

end GlobalTheory.CompanionTheory.FJE
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionLeftInvariantRationalParabolicStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_left_invariant_rational_parabolic : ∀ {D : D7} {n : ℕ} (χ : (AE D)ˣ →* Circle) (s : ℂ) (f : G D n → ℂ), IsHeckeChar D χ → IsLaw χ s f → LeftInv (P D n ⊓ GF D n) f := by
  first | exact @GlobalTheory.CompanionTheory.FJE.leftInv_of_isLaw | exact GlobalTheory.CompanionTheory.FJE.leftInv_of_isLaw | (intros; apply GlobalTheory.CompanionTheory.FJE.leftInv_of_isLaw <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeisenbergCharacterBilinearLaws
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeisenbergCharacterBilinearLaws
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE

variable {D : D7} {ρ p : ℕ}

theorem trA_add (a b : AE D) : trA (a + b) = trA a + trA b := map_add (Algebra.trace (AF D.host.F) (AE D)) a b

theorem pr_add_left (b₀ : HermE D ρ) (x x' y : Mx D ρ p) : pr b₀ (x + x') y = pr b₀ x y + pr b₀ x' y := by
  have h : adj (x + x') = adj x + adj x' := by
    ext i j
    simp only [adj, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, map_add (f := _)]
  simp only [pr, h]
  exact Matrix.add_mul _ _ _

theorem pr_add_right (b₀ : HermE D ρ) (x y y' : Mx D ρ p) : pr b₀ x (y + y') = pr b₀ x y + pr b₀ x y' := by
  simp only [pr]
  rw [show (HMul.hMul (b₀.1.map (incA D)) (y + y') : Mx D ρ p) = _ from Matrix.mul_add _ _ _]
  exact Matrix.mul_add _ _ _

theorem chv_add_left (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (x x' y : Mx D ρ p) :
    chv ψ b₀ (x + x') y = chv ψ b₀ x y * chv ψ b₀ x' y := by
  simp only [chv, pr_add_left, Matrix.trace_add, trA_add, AddChar.map_add_eq_mul]

theorem chv_add_right (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (x y y' : Mx D ρ p) :
    chv ψ b₀ x (y + y') = chv ψ b₀ x y * chv ψ b₀ x y' := by
  simp only [chv, pr_add_right, Matrix.trace_add, trA_add, AddChar.map_add_eq_mul]

theorem chv_norm (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ) (x y : Mx D ρ p) :
    ‖chv ψ b₀ x y‖ = 1 := hψ.2.1 _

theorem chv_zero_right (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (x : Mx D ρ p) : chv ψ b₀ x 0 = 1 := by
  have h : pr b₀ x 0 = 0 := by
    have := pr_add_right b₀ x 0 0
    simpa using this
  simp only [chv, h, Matrix.trace_zero]
  have h0 : trA (0 : AE D) = 0 := map_zero (Algebra.trace (AF D.host.F) (AE D))
  rw [h0, AddChar.map_zero_eq_one]

theorem chv_neg_right (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ) (x y : Mx D ρ p) :
    chv ψ b₀ x (-y) = conj (chv ψ b₀ x y) := by
  have h1 : chv ψ b₀ x y * chv ψ b₀ x (-y) = 1 := by
    rw [← chv_add_right, add_neg_cancel, chv_zero_right]
  have h2 : chv ψ b₀ x y * conj (chv ψ b₀ x y) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, chv_norm ψ hψ]
    simp
  exact mul_left_cancel₀ (left_ne_zero_of_mul_eq_one h1) (h1.trans h2.symm)

theorem trA_incA (t : D.host.E) :
    trA (incA D t) = algebraMap D.host.F (AF D.host.F) (Algebra.trace D.host.F D.host.E t) := by
  have h2 : Algebra.lmul (AF D.host.F) (AE D) (incA D t) =
      (Algebra.lmul D.host.F D.host.E t).baseChange (AF D.host.F) := by
    ext x
    simp [incA, inclR]
  show Algebra.trace (AF D.host.F) (AE D) (incA D t) = _
  rw [Algebra.trace_apply, h2, LinearMap.trace_baseChange, ← Algebra.trace_apply]

theorem pr_rt (b₀ : HermE D ρ) (ξ ξ' : Matrix (Fin ρ) (Fin p) D.host.E) :
    pr b₀ (rt ξ) (rt ξ') = ((ξ.map D.sp.cm.sig)ᵀ * (b₀.1 * ξ')).map (incA D) := by
  have h : adj (rt ξ) = ((ξ.map D.sp.cm.sig)ᵀ).map (incA D) := by
    ext i j
    simp only [adj, rt, Matrix.transpose_apply, Matrix.map_apply]
    rfl
  simp only [pr, h, Matrix.map_mul]

theorem chv_rt (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ)
    (ξ ξ' : Matrix (Fin ρ) (Fin p) D.host.E) : chv ψ b₀ (rt ξ) (rt ξ') = 1 := by
  have h : Matrix.trace (pr b₀ (rt ξ) (rt ξ')) = incA D (Matrix.trace ((ξ.map D.sp.cm.sig)ᵀ * (b₀.1 * ξ'))) := by
    rw [pr_rt]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.map_apply, map_sum]
  rw [chv, h, trA_incA]
  exact hψ.2.2.1 _

theorem chv_continuous (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ) :
    Continuous (fun v : Mx D ρ p × Mx D ρ p => chv ψ b₀ v.1 v.2) := by
  haveI : IsTopologicalRing (AE D) := (Formalism.IndefR.Eqv.ae_facts D).1
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have ht : Continuous (trA (D := D)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF D.host.F) (AE D))
  have hc : Continuous (cA D) := GlobalTheory.FockCompare.ThetaCont.continuous_conj
  have ha : Continuous fun v : Mx D ρ p × Mx D ρ p => adj v.1 := by
    unfold adj
    exact ((continuous_fst.matrix_map hc)).matrix_transpose
  refine hψ.1.comp (ht.comp ?_)
  exact (ha.matrix_mul (continuous_const.matrix_mul continuous_snd)).matrix_trace

theorem chv_facts : ∀ {D : D7} {ρ p : ℕ} (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ b₀ : HermE D ρ, (∀ x x' y : Mx D ρ p, GlobalTheory.CompanionTheory.FJE.chv ψ b₀ (x + x') y = GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x y * GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x' y) ∧ (∀ x y y' : Mx D ρ p, GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x (y + y') = GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x y * GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x y') ∧ (∀ x y : Mx D ρ p, ‖GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x y‖ = 1) ∧ (∀ x y : Mx D ρ p, GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x (-y) = conj (GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x y)) ∧ (∀ ξ ξ' : Matrix (Fin ρ) (Fin p) D.host.E, GlobalTheory.CompanionTheory.FJE.chv ψ b₀ (GlobalTheory.CompanionTheory.FJE.rt ξ) (GlobalTheory.CompanionTheory.FJE.rt ξ') = 1) ∧ Continuous (fun v : Mx D ρ p × Mx D ρ p => GlobalTheory.CompanionTheory.FJE.chv ψ b₀ v.1 v.2) := by
  intro D ρ p ψ hψ b₀
  exact ⟨chv_add_left ψ b₀, chv_add_right ψ b₀, chv_norm ψ hψ b₀, chv_neg_right ψ hψ b₀, chv_rt ψ hψ b₀,
    chv_continuous ψ hψ b₀⟩

end GlobalTheory.CompanionTheory.FJE
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeisenbergCharacterBilinearLawsStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenberg_character_bilinear_laws : ∀ {D : D7} {ρ p : ℕ} (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ b₀ : HermE D ρ, (∀ x x' y : Mx D ρ p, GlobalTheory.CompanionTheory.FJE.chv ψ b₀ (x + x') y = GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x y * GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x' y) ∧ (∀ x y y' : Mx D ρ p, GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x (y + y') = GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x y * GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x y') ∧ (∀ x y : Mx D ρ p, ‖GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x y‖ = 1) ∧ (∀ x y : Mx D ρ p, GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x (-y) = conj (GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x y)) ∧ (∀ ξ ξ' : Matrix (Fin ρ) (Fin p) D.host.E, GlobalTheory.CompanionTheory.FJE.chv ψ b₀ (GlobalTheory.CompanionTheory.FJE.rt ξ) (GlobalTheory.CompanionTheory.FJE.rt ξ') = 1) ∧ Continuous (fun v : Mx D ρ p × Mx D ρ p => GlobalTheory.CompanionTheory.FJE.chv ψ b₀ v.1 v.2) := by
  first | exact @GlobalTheory.CompanionTheory.FJE.chv_facts | exact GlobalTheory.CompanionTheory.FJE.chv_facts | (intros; apply GlobalTheory.CompanionTheory.FJE.chv_facts <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentAdditiveLaw
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentAdditiveLaw
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.NzxAdd

theorem nzx_add : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (z z' : hermA D ρ) (x x' : Mx D ρ p), M.nzx z x * M.nzx z' x' = M.nzx (z + z') (x + x') := by
  intro D n ρ p hn M z z' x x'
  exact GlobalTheory.CompanionTheory.PcB.nzx_mul M z z' x x'

end GlobalTheory.CompanionTheory.NzxAdd
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentAdditiveLawStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_heisenberg_mul : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (z z' : hermA D ρ) (x x' : Mx D ρ p), M.nzx z x * M.nzx z' x' = M.nzx (z + z') (x + x') := by
  first | exact @GlobalTheory.CompanionTheory.NzxAdd.nzx_add | exact GlobalTheory.CompanionTheory.NzxAdd.nzx_add | (intros; apply GlobalTheory.CompanionTheory.NzxAdd.nzx_add <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CountableMatricesAndCosets
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CountableMatricesAndCosets
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE

theorem countable_mat_cosets : ∀ (D : D7) (a b : ℕ), Countable (Matrix (Fin a) (Fin b) D.host.E) ∧ Countable (GlobalTheory.Eis.Cosets (P D b) (GF D b)) := by
  intro D a b
  have hE : Countable D.host.E := (Module.finBasis ℚ D.host.E).equivFun.injective.countable
  refine ⟨inferInstanceAs (Countable (Fin a → Fin b → D.host.E)), ?_⟩
  have hM : Countable (Matrix (Fin (b + b)) (Fin (b + b)) D.host.E) :=
    inferInstanceAs (Countable (Fin (b + b) → Fin (b + b) → D.host.E))
  have hGL : Countable (GL (Fin (b + b)) D.host.E) :=
    (Units.val_injective (α := Matrix (Fin (b + b)) (Fin (b + b)) D.host.E)).countable
  have hG : Countable (GF D b) := by
    have hR : Countable (GRat D.sp.cm.sig (Jst D b)) := by
      unfold GRat
      exact Subtype.val_injective.countable
    show Countable (ratPts D.sp.cm.sig (Jst D b))
    rw [← range_ratEmb]
    exact (Set.countable_range (ratEmb D.sp.cm.sig (Jst D b))).to_subtype
  exact Quotient.countable

end GlobalTheory.CompanionTheory.FJE
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CountableMatricesAndCosetsStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.countable_matrices_and_cosets : ∀ (D : D7) (a b : ℕ), Countable (Matrix (Fin a) (Fin b) D.host.E) ∧ Countable (GlobalTheory.Eis.Cosets (P D b) (GF D b)) := by
  first | exact @GlobalTheory.CompanionTheory.FJE.countable_mat_cosets | exact GlobalTheory.CompanionTheory.FJE.countable_mat_cosets | (intros; apply GlobalTheory.CompanionTheory.FJE.countable_mat_cosets <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShiftConjHeisenberg
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShiftConjHeisenberg
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE

theorem sh_mul_nzx {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (y : Mx D ρ p)
    (z : hermA D ρ) (x : Mx D ρ p) :
    M.sh y * M.nzx z x = M.nzx (z + GlobalTheory.CompanionTheory.FJE.jc y x) x * M.sh y := by
  apply GlobalTheory.CompanionTheory.FourierN.mat_injective
  rw [GlobalTheory.CompanionTheory.PcB.mat_mul', GlobalTheory.CompanionTheory.PcB.mat_mul',
    M.nzx_mat, M.nzx_mat, M.sh_mat]
  simp only [blk4, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, add_zero, zero_add]
  simp only [bl, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, add_zero, zero_add]
  congr 2
  simp only [jc]
  congr 2
  rw [Matrix.mul_neg]
  change z.1 + y * adj x = (z.1 + (y * adj x + x * adj y)) + -(x * adj y)
  abel

end GlobalTheory.CompanionTheory.FJE
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShiftConjHeisenbergStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shift_conj_heisenberg : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (y : Mx D ρ p) (z : hermA D ρ) (x : Mx D ρ p), M.sh y * M.nzx z x = M.nzx (z + GlobalTheory.CompanionTheory.FJE.jc y x) x * M.sh y := by
  first | exact @GlobalTheory.CompanionTheory.FJE.sh_mul_nzx | exact GlobalTheory.CompanionTheory.FJE.sh_mul_nzx | (intros; apply GlobalTheory.CompanionTheory.FJE.sh_mul_nzx <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralEqFundamentalDomainLatticeSum
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralEqFundamentalDomainLatticeSum
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE

theorem integral_fold {D : D7} {ρ p : ℕ} (m : Meas D ρ p) (P : Mx D ρ p → ℂ) (hP : Integrable P m.μ) :
    ∫ y, P y ∂m.μ = ∫ y in m.𝓕, ∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E, P (GlobalTheory.CompanionTheory.FJE.rt ξ + y) ∂m.μ := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := lattice_Mx D ρ p
  have : BorelSpace (Mx D ρ p) := ⟨rfl⟩
  have : Countable (ratMx D ρ p) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hμ := m.hμ
  have := hμ.1
  let e : Matrix (Fin ρ) (Fin p) D.host.E ≃ ratMx D ρ p :=
    Equiv.ofBijective (fun ξ => ⟨rat ξ, rat_mem ξ⟩)
      ⟨fun a b h => rat_injective (congrArg Subtype.val h), fun g => by
        obtain ⟨ξ, hξ⟩ := mem_ratMx.1 g.2
        exact ⟨ξ, Subtype.ext hξ⟩⟩
  have h1 : ∀ y, ∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E, P (GlobalTheory.CompanionTheory.FJE.rt ξ + y) =
      ∑' g : ratMx D ρ p, P (g +ᵥ y) := fun y => e.tsum_eq fun g => P (g +ᵥ y)
  simp only [h1]
  rw [hμ.2.1.integral_eq_tsum'' P hP]
  refine (integral_tsum (ι := ratMx D ρ p) (f := fun g y => P (g +ᵥ y)) (fun g => ?_) ?_).symm
  · exact ((hP.comp_add_left (g : Mx D ρ p)).aestronglyMeasurable).restrict
  · rw [← hμ.2.1.lintegral_eq_tsum'' fun x => ‖P x‖ₑ]
    exact hP.2.ne

end GlobalTheory.CompanionTheory.FJE
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralEqFundamentalDomainLatticeSumStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_eq_fundamental_domain_lattice_sum : ∀ {D : D7} {ρ p : ℕ} (m : Meas D ρ p) (P : Mx D ρ p → ℂ), Integrable P m.μ → ∫ y, P y ∂m.μ = ∫ y in m.𝓕, ∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E, P (GlobalTheory.CompanionTheory.FJE.rt ξ + y) ∂m.μ := by
  first | exact @GlobalTheory.CompanionTheory.FJE.integral_fold | exact GlobalTheory.CompanionTheory.FJE.integral_fold | (intros; apply GlobalTheory.CompanionTheory.FJE.integral_fold <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentreCharacterCommutator
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentreCharacterCommutator
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE

theorem adj_herm {D : D7} {ρ : ℕ} (b₀ : HermE D ρ) :
    adj (b₀.1.map (incA D) : Mx D ρ ρ) = b₀.1.map (incA D) := by
  have h := rat_conjTranspose b₀.1
  have e : b₀.1ᴴ = b₀.1 := b₀.2
  rw [e] at h
  exact h.symm

theorem chz_jc {D : D7} {ρ p : ℕ} (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (y x : Mx D ρ p) :
    chz ψ b₀ (GlobalTheory.CompanionTheory.FJE.jc y x) = GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x y := by
  set B : Mx D ρ ρ := b₀.1.map (incA D) with hB
  have hadj : adj B = B := adj_herm b₀
  have e1 : Matrix.trace (B * (y * adj x)) = Matrix.trace (pr b₀ x y) := by
    show _ = Matrix.trace (adj x * (B * y))
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
  have e2 : Matrix.trace (B * (x * adj y)) = cA D (Matrix.trace (pr b₀ x y)) := by
    rw [← GlobalTheory.CompanionTheory.FourierN.trace_adj]
    have h : adj (pr b₀ x y) = HMul.hMul (HMul.hMul (adj y) B : Mx D p ρ) x := by
      show adj (HMul.hMul (adj x) (HMul.hMul B y : Mx D ρ p) : Mx D p p) = _
      rw [adj_mul, adj_mul, adj_adj, hadj]
    rw [h, Matrix.trace_mul_comm, Matrix.mul_assoc x, Matrix.trace_mul_comm]
  have e3 : Matrix.trace (HMul.hMul B (GlobalTheory.CompanionTheory.FJE.jc y x).1 : Mx D ρ ρ) =
      Matrix.trace (pr b₀ x y) + cA D (Matrix.trace (pr b₀ x y)) := by
    show Matrix.trace (B * (y * adj x + x * adj y)) = _
    rw [Matrix.mul_add, Matrix.trace_add, e1, e2]
  rw [chz, show HMul.hMul (b₀.1.map (incA D)) (GlobalTheory.CompanionTheory.FJE.jc y x).1 = HMul.hMul B (GlobalTheory.CompanionTheory.FJE.jc y x).1 from rfl, e3,
    GlobalTheory.CompanionTheory.FourierN.halfTr_add_cA]
  rfl

end GlobalTheory.CompanionTheory.FJE
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentreCharacterCommutatorStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centre_character_commutator : ∀ {D : D7} {ρ p : ℕ} (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (y x : Mx D ρ p), chz ψ b₀ (GlobalTheory.CompanionTheory.FJE.jc y x) = GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x y := by
  first | exact @GlobalTheory.CompanionTheory.FJE.chz_jc | exact GlobalTheory.CompanionTheory.FJE.chz_jc | (intros; apply GlobalTheory.CompanionTheory.FJE.chz_jc <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzLatticeSumBoundedAltBis
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PeriodisationBound
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE

variable {D : D7} {ρ p : ℕ}

theorem maj_add_le (θ : InfFam D) (K K₀ : Set (Mx D ρ p)) (N : ℕ) (R : ℝ) (hR0 : 0 ≤ R)
    (hR : ∀ w ∈ K₀, GlobalTheory.Unf.realSize θ (-w) ≤ R) (g w : Mx D ρ p) (hw : w ∈ K₀) :
    GlobalTheory.Unf.maj θ K N (g + w) ≤ (1 + R) ^ N * GlobalTheory.Unf.maj θ (K + (-K₀)) N g := by
  by_cases hb : GlobalTheory.Unf.InBox K (g + w)
  · have hb' : GlobalTheory.Unf.InBox (K + (-K₀)) g := by
      obtain ⟨k, hk, h0⟩ := hb
      refine ⟨k + -w, Set.add_mem_add hk (Set.neg_mem_neg.2 hw), ?_⟩
      have e : g - (k + -w) = g + w - k := by abel
      rw [e]; exact h0
    unfold GlobalTheory.Unf.maj
    rw [if_pos hb, if_pos hb']
    have h0 := GlobalTheory.Unf.realSize_nonneg θ g
    have h1 := GlobalTheory.Unf.realSize_nonneg θ (g + w)
    have h2 : 1 + GlobalTheory.Unf.realSize θ g ≤ (1 + R) * (1 + GlobalTheory.Unf.realSize θ (g + w)) := by
      have h3 := GlobalTheory.MajSum.realSize_add_le θ (g + w) (-w)
      rw [add_neg_cancel_right] at h3
      have h4 := hR w hw
      nlinarith
    have hp : (0:ℝ) < (1 + GlobalTheory.Unf.realSize θ (g + w)) ^ N := by positivity
    have hq : (0:ℝ) < (1 + GlobalTheory.Unf.realSize θ g) ^ N := by positivity
    have h5 : (1 + GlobalTheory.Unf.realSize θ g) ^ N ≤ (1 + R) ^ N * (1 + GlobalTheory.Unf.realSize θ (g + w)) ^ N := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by linarith) h2 N
    rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ hp hq, one_mul]
    exact h5
  · have h0 : GlobalTheory.Unf.maj θ K N (g + w) = 0 := by unfold GlobalTheory.Unf.maj; rw [if_neg hb]
    rw [h0]
    exact mul_nonneg (by positivity) (GlobalTheory.Unf.maj_nonneg θ _ N g)

theorem continuous_realSize {θ : InfFam D} (hθ : IsInfFam θ) :
    Continuous (GlobalTheory.Unf.realSize θ : Mx D ρ p → ℝ) := by
  unfold GlobalTheory.Unf.realSize
  refine continuous_finsetSum _ fun τ _ => continuous_finsetSum _ fun i _ =>
    continuous_finsetSum _ fun j _ => ?_
  exact ((GlobalTheory.RealWeil.continuous_compAt hθ τ ρ p).matrix_elem i j).norm

theorem periodisation_bound : ∀ {D : D7} {ρ p : ℕ} (θ : InfFam D), IsInfFam θ → ∀ φ ∈ schwartzA θ ρ p,
    ∃ B : ℝ, ∀ y : Mx D ρ p,
      Summable (fun ξ : Matrix (Fin ρ) (Fin p) D.host.E => ‖φ (GlobalTheory.CompanionTheory.FJE.rt ξ + y)‖) ∧
      ∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E, ‖φ (GlobalTheory.CompanionTheory.FJE.rt ξ + y)‖ ≤ B := by
  intro D ρ p θ hθ φ hφ
  obtain ⟨-, K, hK, hbd⟩ := GlobalTheory.SchwartzMaj.hasMaj_of_mem hθ hφ
  obtain ⟨N, hN⟩ := GlobalTheory.MajSum.tsum_maj_ne_top D θ hθ ρ p
  obtain ⟨i1, -, -, -, -, K₀, hK₀, hcov⟩ := lattice_Mx D ρ p
  obtain ⟨C, hC⟩ := hbd N
  have hK' : IsCompact (K + (-K₀)) := hK.add hK₀.neg
  obtain ⟨R₀, hR₀⟩ := hK₀.exists_bound_of_continuousOn (f := fun w => GlobalTheory.Unf.realSize θ (-w))
    ((continuous_realSize hθ).comp continuous_neg).continuousOn
  have hR : ∀ w ∈ K₀, GlobalTheory.Unf.realSize θ (-w) ≤ |R₀| := fun w hw =>
    (le_abs_self _).trans ((hR₀ w hw).trans (le_abs_self _))
  have hg : Summable fun γ : ratMx D ρ p => GlobalTheory.Unf.maj θ (K + (-K₀)) N (γ : Mx D ρ p) := by
    have h := ENNReal.summable_toReal (hN _ hK')
    refine h.congr fun γ => ?_
    exact ENNReal.toReal_ofReal (GlobalTheory.Unf.maj_nonneg θ _ N _)
  set c : ℝ := |C| * (1 + |R₀|) ^ N with hc
  have hc0 : 0 ≤ c := by positivity
  refine ⟨c * ∑' γ : ratMx D ρ p, GlobalTheory.Unf.maj θ (K + (-K₀)) N (γ : Mx D ρ p), fun y => ?_⟩
  obtain ⟨γ, hγ, hy⟩ := hcov y
  obtain ⟨ξ₀, rfl⟩ := mem_ratMx.1 hγ
  let e : Matrix (Fin ρ) (Fin p) D.host.E → ratMx D ρ p := fun ξ => ⟨rat (ξ - ξ₀), rat_mem _⟩
  have he : Function.Injective e := fun a b h => by
    have := rat_injective (congrArg Subtype.val h)
    exact sub_left_injective this
  have key : ∀ ξ, ‖φ (rt ξ + y)‖ ≤ c * GlobalTheory.Unf.maj θ (K + (-K₀)) N (e ξ : Mx D ρ p) := by
    intro ξ
    have e1 : rt ξ + y = rat (ξ - ξ₀) + (rat ξ₀ + y) := by
      have : rat (ξ - ξ₀) = rt ξ - rat ξ₀ := by
        ext i j
        simp [rat, rt]
      rw [this]; abel
    rw [e1]
    refine (hC _).trans ?_
    have h1 := maj_add_le θ K K₀ N |R₀| (abs_nonneg _) hR (rat (ξ - ξ₀)) (rat ξ₀ + y) hy
    calc C * GlobalTheory.Unf.maj θ K N (rat (ξ - ξ₀) + (rat ξ₀ + y))
        ≤ |C| * GlobalTheory.Unf.maj θ K N (rat (ξ - ξ₀) + (rat ξ₀ + y)) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (GlobalTheory.Unf.maj_nonneg θ _ N _)
      _ ≤ |C| * ((1 + |R₀|) ^ N * GlobalTheory.Unf.maj θ (K + (-K₀)) N (rat (ξ - ξ₀))) :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg C)
      _ = c * GlobalTheory.Unf.maj θ (K + (-K₀)) N (e ξ : Mx D ρ p) := by rw [hc, mul_assoc]
  have hs' : Summable fun ξ => c * GlobalTheory.Unf.maj θ (K + (-K₀)) N (e ξ : Mx D ρ p) :=
    (hg.comp_injective he).mul_left c
  have hs : Summable fun ξ => ‖φ (rt ξ + y)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) key hs'
  refine ⟨hs, (hs.tsum_le_tsum key hs').trans ?_⟩
  rw [tsum_mul_left]
  refine mul_le_mul_of_nonneg_left ?_ hc0
  exact tsum_comp_le_tsum_of_inj hg (fun _ => GlobalTheory.Unf.maj_nonneg θ _ N _) he

end GlobalTheory.CompanionTheory.FJE
end
end

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bound_lattice_sum_norm_schwartzA : ∀ {D : D7} {ρ p : ℕ} (θ : InfFam D), IsInfFam θ → ∀ φ ∈ schwartzA θ ρ p, ∃ B : ℝ, ∀ y : Mx D ρ p, Summable (fun ξ : Matrix (Fin ρ) (Fin p) D.host.E => ‖φ (GlobalTheory.CompanionTheory.FJE.rt ξ + y)‖) ∧ ∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E, ‖φ (GlobalTheory.CompanionTheory.FJE.rt ξ + y)‖ ≤ B := by
  first | exact @GlobalTheory.CompanionTheory.FJE.periodisation_bound | exact GlobalTheory.CompanionTheory.FJE.periodisation_bound | (intros; apply GlobalTheory.CompanionTheory.FJE.periodisation_bound <;> assumption)
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitMeasureIntegralPointsNonzero
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitMeasureIntegralPointsNonzero
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ColumnSplitting

theorem eventually_cv_mem_intLoc {D : D7} (a : AE D) :
    ∀ᶠ v : Pl D in cofinite, cv D v a ∈ intLoc D.host.F D.host.E v :=
  GlobalTheory.ThK.ConeEuler.eventually_compFin_mem_intLoc_adele a

theorem isOpen_intAll (D : D7) : IsOpen {z : AE D | ∀ v : Pl D, cv D v z ∈ intLoc D.host.F D.host.E v} :=
  GlobalTheory.ThK.ConeEuler.UnitsOpen.isOpen_integral_everywhere

theorem exists_intOff {D : D7} {a b : ℕ} (x : Mx D a b) :
    ∀ᶠ v : Pl D in cofinite, ∀ i j, cv D v (x i j) ∈ intLoc D.host.F D.host.E v :=
  eventually_all.2 fun i => eventually_all.2 fun j => eventually_cv_mem_intLoc (x i j)

theorem isOpen_nearInt {D : D7} {a b : ℕ} (x : Mx D a b) :
    IsOpen {y : Mx D a b | ∀ i j, ∀ v : Pl D, cv D v (y i j - x i j) ∈ intLoc D.host.F D.host.E v} := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have h : {y : Mx D a b | ∀ i j, ∀ v : Pl D, cv D v (y i j - x i j) ∈ intLoc D.host.F D.host.E v} =
      ⋂ i, ⋂ j, (fun y : Mx D a b => y i j - x i j) ⁻¹' {z : AE D | ∀ v : Pl D, cv D v z ∈ intLoc D.host.F D.host.E v} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
  rw [h]
  have hT := (top_mx (D := D) a b).1
  haveI hS : ContinuousSub (Mx D a b) := @IsTopologicalAddGroup.to_continuousSub _ _ _ hT
  have hc : Continuous fun y : Mx D a b => y - x := continuous_id.sub continuous_const
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    (isOpen_intAll D).preimage (hc.matrix_elem i j)

theorem nuT_intOff_ne_zero : ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) (I : IkD d n)
    (μ : Measure (Mx D W.rank t)), μ.IsAddHaarMeasure → ∀ x₀, ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S →
      nuT hn I μ x₀ {z | IntOff S z.1 ∧ IntOff S z.2} ≠ 0 := by
  intro D n t B W d hn I μ hμ x₀
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  let π : I.l.K × Par D n t W → Mx D B.rank W.rank × Mx D B.rank t :=
    fun p => ac B ((p.1 : GA D B)⁻¹) (zp d hn x₀ p.2)
  let p₀ : I.l.K × Par D n t W := (1, (1, (0, 0)))
  have hbad : {v : Pl D | ¬ ((∀ i j, cv D v ((π p₀).1 i j) ∈ intLoc D.host.F D.host.E v) ∧
      ∀ i j, cv D v ((π p₀).2 i j) ∈ intLoc D.host.F D.host.E v)}.Finite :=
    ((exists_intOff (π p₀).1).and (exists_intOff (π p₀).2))
  refine ⟨hbad.toFinset, fun S hS => ?_⟩
  have hπ : Continuous π := by
    obtain ⟨-, k2, -, -, k5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
    exact (continuous_ac B).comp (((continuous_subtype_val.comp continuous_fst).inv).prodMk
      ((continuous_zp d hn x₀).comp continuous_snd))
  let N : Set (Mx D B.rank W.rank × Mx D B.rank t) :=
    {z | (∀ i j, ∀ v : Pl D, cv D v (z.1 i j - (π p₀).1 i j) ∈ intLoc D.host.F D.host.E v) ∧
      ∀ i j, ∀ v : Pl D, cv D v (z.2 i j - (π p₀).2 i j) ∈ intLoc D.host.F D.host.E v}
  have hNo : IsOpen N := ((isOpen_nearInt (π p₀).1).preimage continuous_fst).inter
    ((isOpen_nearInt (π p₀).2).preimage continuous_snd)
  have hN0 : π p₀ ∈ N := by
    constructor <;> intro i j v <;> simp only [sub_self, map_zero, zero_mem]
  have hNO : N ⊆ {z | IntOff S z.1 ∧ IntOff S z.2} := by
    intro z hz
    have key : ∀ v, v ∉ S → (∀ i j, cv D v ((π p₀).1 i j) ∈ intLoc D.host.F D.host.E v) ∧
        ∀ i j, cv D v ((π p₀).2 i j) ∈ intLoc D.host.F D.host.E v := fun v hv => by
      by_contra hc
      exact hv (hS (hbad.mem_toFinset.2 hc))
    refine ⟨fun v hv i j => ?_, fun v hv i j => ?_⟩
    · have := add_mem (hz.1 i j v) ((key v hv).1 i j)
      rwa [← RingHom.map_add, sub_add_cancel] at this
    · have := add_mem (hz.2 i j v) ((key v hv).2 i j)
      rwa [← RingHom.map_add, sub_add_cancel] at this
  obtain ⟨-, i2, i3, i4, i5⟩ := top_mx (D := D) t n
  obtain ⟨-, j2, j3, j4, j5⟩ := top_mx (D := D) W.rank t
  obtain ⟨-, g2, g3, -, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  have hGB : BorelSpace (GA D W) := ⟨rfl⟩
  obtain ⟨hc, 𝓕, hf⟩ := I.cov₁
  have := hf.1
  have := I.haar
  have := I.haarK
  have hs1 : SigmaFinite (I.μ₁.prod μ) := inferInstance
  have hs2 : SigmaFinite (Q0 I μ) := sigmaFinite_parameter_product_measure I μ hμ
  have p1 : (I.μ₁.prod μ).IsOpenPosMeasure := Measure.prod.instIsOpenPosMeasure
  have p2 : (Q0 I μ).IsOpenPosMeasure := Measure.prod.instIsOpenPosMeasure
  have hpos : (I.νK.prod (Q0 I μ)).IsOpenPosMeasure := Measure.prod.instIsOpenPosMeasure
  have hopen : IsOpen (π ⁻¹' N) := hNo.preimage hπ
  have hne : (I.νK.prod (Q0 I μ)) (π ⁻¹' N) ≠ 0 := hopen.measure_ne_zero _ ⟨p₀, hN0⟩
  intro h0
  apply hne
  have hle : (I.νK.prod (Q0 I μ)) (π ⁻¹' {z | IntOff S z.1 ∧ IntOff S z.2}) ≤ nuT hn I μ x₀ {z | IntOff S z.1 ∧ IntOff S z.2} :=
    Measure.le_map_apply (measurable_pi hn I x₀).aemeasurable _
  exact le_antisymm (((measure_mono (Set.preimage_mono hNO)).trans hle).trans h0.le) bot_le

end GlobalTheory.CompanionTheory.ColumnSplitting

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitMeasureIntegralPointsNonzeroStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbit_measure_integral_points_nonzero : ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) (I : IkD d n) (μ : Measure (Mx D W.rank t)), μ.IsAddHaarMeasure → ∀ x₀, ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S → nuT hn I μ x₀ {z | IntOff S z.1 ∧ IntOff S z.2} ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.ColumnSplitting.nuT_intOff_ne_zero | exact GlobalTheory.CompanionTheory.ColumnSplitting.nuT_intOff_ne_zero | (intros; apply GlobalTheory.CompanionTheory.ColumnSplitting.nuT_intOff_ne_zero <;> assumption)
end
end
