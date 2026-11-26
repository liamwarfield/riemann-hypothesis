module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatFiniteAdelesMemSpanRestrictedProdu
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonsplitCentraliserNormElement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoBarZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalDarbouxOrientedPairTransport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddCharHalfTraceTensorLatticeHeisenbergCocycle
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddCharHalfTraceTensorLatticeHeisenbergCocycle
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.VacCocycle

section General

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A)
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

set_option autoImplicit false in
open IsDedekindDomain NumberField MeasureTheory Matrix in
open Classical in
open scoped TensorProduct ComplexConjugate in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar _root_.GlobalTheory.LocalData.complRel
  _root_.GlobalTheory.LocalData.isLocalField _root_.GlobalTheory.FunObj.borelKw
  _root_.GlobalTheory.FunObj.borelSpaceKw in
variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A)
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
theorem _root_.GlobalTheory.VacCocycle.conj_hTens (hc : ∀ z, c (c z) = z) {JA : Matrix α α A}
    {JB : Matrix β β A} (hA : ∀ i j, c (JA j i) = JA i j) (hB : ∀ i j, c (JB j i) = -JB i j)
    (x y : Matrix α β A) :
    c (_root_.GlobalTheory.WeilM.hTens c JA JB y x) = -_root_.GlobalTheory.WeilM.hTens c JA JB x y := by
  unfold _root_.GlobalTheory.WeilM.hTens
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, hc, hA, hB]
  simp only [← Finset.sum_neg_distrib]
  conv_lhs => enter [2, i]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, k, 2, i]; rw [Finset.sum_comm]
  conv_lhs => enter [2, k]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ =>
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

set_option autoImplicit false in
open IsDedekindDomain NumberField MeasureTheory Matrix in
open Classical in
open scoped TensorProduct ComplexConjugate in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar _root_.GlobalTheory.LocalData.complRel
  _root_.GlobalTheory.LocalData.isLocalField _root_.GlobalTheory.FunObj.borelKw
  _root_.GlobalTheory.FunObj.borelSpaceKw in
variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A)
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
theorem _root_.GlobalTheory.VacCocycle.trace_conj (hc : ∀ z, c (c z) = z) (z : A) :
    Algebra.trace R A (c z) = Algebra.trace R A z :=
  Algebra.trace_eq_of_algEquiv (AlgEquiv.ofAlgHom c c (AlgHom.ext hc) (AlgHom.ext hc)) z

end General

set_option autoImplicit false in
open IsDedekindDomain NumberField MeasureTheory Matrix in
open Classical in
open scoped TensorProduct ComplexConjugate in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar _root_.GlobalTheory.LocalData.complRel
  _root_.GlobalTheory.LocalData.isLocalField _root_.GlobalTheory.FunObj.borelKw
  _root_.GlobalTheory.FunObj.borelSpaceKw in
variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A)
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
omit [DecidableEq α] [DecidableEq β] in
private lemma hTens_add_add (JA : Matrix α α A) (JB : Matrix β β A)
    (x y : Matrix α β A) :
    _root_.GlobalTheory.WeilM.hTens c JA JB (x + y) (x + y) =
      _root_.GlobalTheory.WeilM.hTens c JA JB x x + _root_.GlobalTheory.WeilM.hTens c JA JB x y +
        _root_.GlobalTheory.WeilM.hTens c JA JB y x + _root_.GlobalTheory.WeilM.hTens c JA JB y y := by
  unfold _root_.GlobalTheory.WeilM.hTens
  simp only [Matrix.add_apply, map_add (f := _), add_mul, mul_add, Finset.sum_add_distrib]
  ring

set_option autoImplicit false in
open IsDedekindDomain NumberField MeasureTheory Matrix in
open Classical in
open scoped TensorProduct ComplexConjugate in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar _root_.GlobalTheory.LocalData.complRel
  _root_.GlobalTheory.LocalData.isLocalField _root_.GlobalTheory.FunObj.borelKw
  _root_.GlobalTheory.FunObj.borelSpaceKw in
variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A)
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
private lemma addChar_symp_add_add (hc : ∀ z, c (c z) = z) {JA : Matrix α α A}
    {JB : Matrix β β A} (hA : ∀ i j, c (JA j i) = JA i j) (hB : ∀ i j, c (JB j i) = -JB i j)
    (ψ : AddChar R ℂ) {h : R} (hh : h * 2 = 1) {ξ : A} (hξ : c ξ = 1 - ξ) (x y : Matrix α β A)
    (h1 : ψ (_root_.GlobalTheory.WeilM.symp c ξ JA JB x y) = 1)
    (h2 : ψ (_root_.GlobalTheory.WeilM.symp c (-1) JA JB x y) = 1) :
    ψ (h * _root_.GlobalTheory.WeilM.symp c ξ JA JB (x + y) (x + y)) =
      ψ (h * _root_.GlobalTheory.WeilM.symp c ξ JA JB x x) *
        ψ (h * _root_.GlobalTheory.WeilM.symp c ξ JA JB y y) *
        ψ (-(h * _root_.GlobalTheory.WeilM.symp c (-1) JA JB x y)) := by
  unfold _root_.GlobalTheory.WeilM.symp at *
  have hswap : _root_.GlobalTheory.WeilM.hTens c JA JB y x =
      -c (_root_.GlobalTheory.WeilM.hTens c JA JB x y) := by
    rw [_root_.GlobalTheory.VacCocycle.conj_hTens c hc hA hB y x, neg_neg]
  have hconj : Algebra.trace R A (ξ * c (_root_.GlobalTheory.WeilM.hTens c JA JB x y)) =
      Algebra.trace R A (_root_.GlobalTheory.WeilM.hTens c JA JB x y) -
        Algebra.trace R A (ξ * _root_.GlobalTheory.WeilM.hTens c JA JB x y) := by
    rw [← _root_.GlobalTheory.VacCocycle.trace_conj c hc, map_mul, hc, hξ, sub_mul, one_mul, map_sub]
  have hm1 : Algebra.trace R A (-1 * _root_.GlobalTheory.WeilM.hTens c JA JB x y) =
      -Algebra.trace R A (_root_.GlobalTheory.WeilM.hTens c JA JB x y) := by
    rw [neg_one_mul, map_neg]
  have key : h * Algebra.trace R A (ξ * _root_.GlobalTheory.WeilM.hTens c JA JB (x + y) (x + y)) =
      h * Algebra.trace R A (ξ * _root_.GlobalTheory.WeilM.hTens c JA JB x x) +
        h * Algebra.trace R A (ξ * _root_.GlobalTheory.WeilM.hTens c JA JB y y) +
        -(h * Algebra.trace R A (-1 * _root_.GlobalTheory.WeilM.hTens c JA JB x y)) +
        (Algebra.trace R A (ξ * _root_.GlobalTheory.WeilM.hTens c JA JB x y) +
          Algebra.trace R A (-1 * _root_.GlobalTheory.WeilM.hTens c JA JB x y)) := by
    rw [hTens_add_add, hswap]
    simp only [mul_add, map_add (f := _), mul_neg, map_neg]
    rw [hconj]
    linear_combination (Algebra.trace R A (ξ * _root_.GlobalTheory.WeilM.hTens c JA JB x y) -
      Algebra.trace R A (_root_.GlobalTheory.WeilM.hTens c JA JB x y)) * hh + (h - 1) * hm1
  rw [key]
  simp only [AddChar.map_add_eq_mul]
  rw [h1, h2, mul_one, mul_one]


set_option autoImplicit false in
open IsDedekindDomain NumberField MeasureTheory Matrix in
open Classical in
open scoped TensorProduct ComplexConjugate in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar _root_.GlobalTheory.LocalData.complRel
  _root_.GlobalTheory.LocalData.isLocalField _root_.GlobalTheory.FunObj.borelKw
  _root_.GlobalTheory.FunObj.borelSpaceKw in
theorem _root_.GlobalTheory.VacCocycle.psi_half_symp_add : ∀ {F E : Type} [Field F]
    [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E), B.IsGood σ →
    ∀ {n d : ℕ} (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (Y : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d)
    (r s r' s' : ℕ),
    X.IsHerm σ B r s → Y.IsSkew σ B r' s' →
    ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 → ∀ v : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F),
    ∀ γ ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v, ∀ γ' ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v,
      B.ψ (⅟(2 : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) * _root_.GlobalTheory.WeilM.symp
          (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) (θ : E))
          (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J)
          (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) (γ + γ') (γ + γ')) =
        B.ψ (⅟(2 : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) * _root_.GlobalTheory.WeilM.symp
            (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) (θ : E))
            (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J)
            (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ γ) *
          B.ψ (⅟(2 : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) * _root_.GlobalTheory.WeilM.symp
            (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) (θ : E))
            (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J)
            (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ' γ') *
          B.ψ (-(⅟(2 : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) * _root_.GlobalTheory.WeilM.symp
            (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1)
            (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J)
            (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ γ')) := by
  intro F E _ _ _ _ _ σ B hB n d X Y r s r' s' hX hY θ hθ v γ hγ γ' hγ'
  have hσ : ∀ z, σ (σ z) = z := by
    have hcm := hB.cm
    unfold _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt at hcm
    obtain ⟨-, -, -, hτ⟩ := hcm
    intro z
    let τ : E →+* ℂ := (IsAlgClosed.lift (R := ℚ) (S := E) (M := ℂ)).toRingHom
    apply τ.injective
    rw [hτ, hτ, star_star]
  have hcc : ∀ z, _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ z) = z := by
    have hcomp : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ).comp (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) = AlgHom.id _ _ := by
      unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA
      rw [← Algebra.TensorProduct.map_comp]
      have hσσ : σ.comp σ = AlgHom.id F E := AlgHom.ext hσ
      rw [hσσ, AlgHom.comp_id]
      exact Algebra.TensorProduct.map_id
    intro z
    exact DFunLike.congr_fun hcomp z
  have hinc : ∀ x : E, _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) x) =
      _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) (σ x) := by
    intro x
    unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR
    simp
  have hA : ∀ i j, _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J j i) =
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J i j := by
    intro i j
    unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM
    rw [Matrix.map_apply, Matrix.map_apply, hinc, hX.herm]
  have hB' : ∀ i j, _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J j i) =
      -_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J i j := by
    intro i j
    unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM
    rw [Matrix.map_apply, Matrix.map_apply, hinc, hY.skew, map_neg]
  have hξ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) (θ : E)) =
      1 - _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) (θ : E) := by
    rw [hinc, eq_sub_of_add_eq' hθ, map_sub, map_one]
  have hone : (_root_.GlobalTheory.AdelicU.evFin F v) 1 ∈
      HeightOneSpectrum.adicCompletionIntegers F v := by
    rw [map_one]
    exact one_mem _
  have h1 := _root_.GlobalTheory.LatVacArith.psi_symp_latAtV σ B X Y r s r' s' hB hX hY v θ 1
    hone γ hγ γ' hγ'
  have h2 := _root_.GlobalTheory.LatVacArith.psi_symp_latAtV σ B X Y r s r' s' hB hX hY v (-1) 1
    hone γ hγ γ' hγ'
  rw [one_mul] at h1 h2
  have hm : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) (((-1 : 𝓞 E) : E)) = -1 := by
    simp
  rw [hm] at h2
  exact addChar_symp_add_add (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) hcc hA hB' B.ψ
    (invOf_mul_self (2 : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)) hξ γ γ' h1 h2

end GlobalTheory.VacCocycle

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddCharHalfTraceTensorLatticeHeisenbergCocycleStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped GlobalTheory.VacAny

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.addChar_halfTrace_tensorLattice_heisenbergCocycle : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E), B.IsGood σ → ∀ {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (r s r' s' : ℕ),
    X.IsHerm σ B r s → Y.IsSkew σ B r' s' → ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F),
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v, ∀ γ' ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v,
      B.ψ (⅟(2 : AF F) * GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) (θ : E))
          (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) (γ + γ') (γ + γ')) =
        B.ψ (⅟(2 : AF F) * GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) (θ : E))
            (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ γ) *
          B.ψ (⅟(2 : AF F) * GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) (θ : E))
            (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ' γ') *
          B.ψ (-(⅟(2 : AF F) * GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1)
            (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ γ')) := by
  first | exact @GlobalTheory.VacCocycle.psi_half_symp_add | exact GlobalTheory.VacCocycle.psi_half_symp_add | (intros; apply GlobalTheory.VacCocycle.psi_half_symp_add <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExpansionIff
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest

namespace GlobalTheory.DepthUnf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

def flatProd (S : GridChoice W U) (t : T) (Φ : G.Datum) (β : CosFam G t)
    (x : ∀ j : Fin D.R.m, WO (G.V (.top j)) (G.V (.top (j + 1))))
    (y : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))) : ℂ :=
  ∏ w, (S.term t Φ β w).datum (S.colAt t w x) (S.rowAt t w y)

def DepthOK (S : GridChoice W U) (t : T) (Φ : G.Datum) (β : CosFam G t) (e : AE D) (K : ℕ) : Prop :=
  (∀ (x : ∀ j : Fin D.R.m, WO (G.V (.top j)) (G.V (.top (j + 1))))
      (y : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))),
      (∀ j, IsHalf e (x j)) → (∀ i, IsHalf e (y i)) → flatProd S t Φ β x y ≠ 0 →
        (∀ j : Fin D.R.m, K • x j ∈ pairLat G (.top t j)) ∧ ∀ i : Fin D.R.m, K • y i ∈ pairLat G (.chi i D.R.m)) ∧
  ∀ (x u : ∀ j : Fin D.R.m, WO (G.V (.top j)) (G.V (.top (j + 1))))
    (y v : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))),
    (∀ j, IsHalf e (x j)) → (∀ i, IsHalf e (y i)) → (∀ j : Fin D.R.m, IsHalf e (u j) ∧ u j ∈ pairLat G (.top t j)) →
      (∀ i : Fin D.R.m, IsHalf e (v i) ∧ v i ∈ pairLat G (.chi i D.R.m)) → flatProd S t Φ β (x + K • u) (y + K • v) = flatProd S t Φ β x y

def ExpWith (S : GridChoice W U) (t : T) (Φ : G.Datum) (β : CosFam G t) (e : AE D) (τ : PureDat G t →₀ ℂ) : Prop :=
  (∀ d ∈ τ.support, (∀ j, (d.1 j).P = locPl G t ∧ (d.1 j).e = e ∧ (d.1 j).z = 1) ∧
      ∀ i, (d.2 i).P = locPl G t ∧ (d.2 i).e = e ∧ (d.2 i).z = 1) ∧
    ∀ (x : ∀ j : Fin D.R.m, WO (G.V (.top j)) (G.V (.top (j + 1))))
      (y : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))),
      (∀ j, IsHalf e (x j)) → (∀ i, IsHalf e (y i)) →
        (τ.sum fun d c => c * (∏ j, (d.1 j).fn (x j)) * ∏ i, (d.2 i).fn (y i)) = flatProd S t Φ β x y

end GlobalTheory.DepthUnf

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvaluationGoodModelsIntertwine
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvaluationGoodModelsIntertwine
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DoublingEv

noncomputable section

namespace GlobalTheory.EvTame

open scoped Classical

variable {F : Type} [Field F] [NumberField F]

def HasTameExp {κ κ' : Type} [Fintype κ] [Fintype κ'] (T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ))
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι)
    (P : ι → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] SchwartzMap (κ' → mixedEmbedding.mixedSpace F) ℂ)
    (g' : ι → (κ' → FiniteAdeleRing (𝓞 F) F) → ℂ), (∀ j, g' j ∈ SB (κ' → FiniteAdeleRing (𝓞 F) F)) ∧
      ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, T (pureA F f g) = ∑ j, pureA F (P j f) (g' j)

theorem pureA_zero {κ : Type} (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) :
    pureA F f (0 : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) = 0 := by
  funext x; simp [pureA]

theorem pureA_add {κ : Type} (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g₁ g₂ : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    pureA F f (g₁ + g₂) = pureA F f g₁ + pureA F f g₂ := by
  funext x; simp [pureA, mul_add]

theorem pureA_smul {κ : Type} (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (c : ℂ)
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) : pureA F f (c • g) = c • pureA F f g := by
  funext x; simp only [pureA, Pi.smul_apply, smul_eq_mul]; ring

theorem hasTameExp_zero {κ κ' : Type} [Fintype κ] [Fintype κ'] (T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)) :
    HasTameExp T 0 :=
  ⟨Empty, inferInstance, fun j => j.elim, fun j => j.elim, fun j => j.elim, fun f => by
    letI : IsEmpty Empty := Empty.instIsEmpty
    rw [pureA_zero, map_zero]; simp⟩

theorem HasTameExp.add {κ κ' : Type} [Fintype κ] [Fintype κ'] {T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)}
    {g₁ g₂ : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (h₁ : HasTameExp T g₁) (h₂ : HasTameExp T g₂) :
    HasTameExp T (g₁ + g₂) := by
  obtain ⟨ι₁, _, P₁, k₁, hk₁, e₁⟩ := h₁
  obtain ⟨ι₂, _, P₂, k₂, hk₂, e₂⟩ := h₂
  refine ⟨ι₁ ⊕ ι₂, inferInstance, Sum.elim P₁ P₂, Sum.elim k₁ k₂, ?_, fun f => ?_⟩
  · rintro (j | j)
    · exact hk₁ j
    · exact hk₂ j
  · rw [pureA_add, map_add (f := _), e₁, e₂, Fintype.sum_sum_type]
    rfl

theorem HasTameExp.smul {κ κ' : Type} [Fintype κ] [Fintype κ'] {T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)}
    {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (c : ℂ) (h : HasTameExp T g) : HasTameExp T (c • g) := by
  obtain ⟨ι, _, P, k, hk, e⟩ := h
  refine ⟨ι, inferInstance, P, fun j => c • k j, fun j => Submodule.smul_mem _ c (hk j), fun f => ?_⟩
  rw [pureA_smul, map_smul, e, Finset.smul_sum]
  exact Finset.sum_congr rfl fun j _ => (pureA_smul _ c _).symm

theorem pure_eq_pureA {κ : Type} [Fintype κ] (f : SInf F κ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ) :
    pure f φ = pureA F f (fun y : κ → FiniteAdeleRing (𝓞 F) F => ∏ᶠ v, φ v fun i => evalV F v (y i)) := rfl

end GlobalTheory.EvTame

namespace GlobalTheory.EvTame

open scoped Classical

theorem isTame_of_isEv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁)
    (M : Model σ X W) (M₁ : Model σ X₁ W₁) (ι : Matrix (Fin n) (Fin n₁) E) (ι' : Matrix (Fin d) (Fin d₁) E)
    (I : Set (Matrix (Fin n) (Fin d) (AE F E))) (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁),
    M.IsGood B.ψ → M₁.IsGood B.ψ → IsEv B M M₁ ι ι' I e → IsTame F e := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ M M₁ ι ι' I e hM hM₁ hE g hg
  obtain ⟨ei, ev, -, hev, hloc⟩ := hE.loc
  have hs := GlobalTheory.SBSpan.mem_span_restrictedProd F (Fin n × Fin d) g hg
  clear hg
  change HasTameExp e g
  induction hs using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨φ, hφ, hcof, rfl⟩ := hx
    have hvac : ∀ᶠ v in cofinite, φ v = M.vac v := by
      filter_upwards [hcof, hM.std] with v h1 h2
      rw [h1, h2]
    have hSB : ∀ v, ev v (φ v) ∈ SB (Fin n₁ × Fin d₁ → Fv F v) := fun v =>
      (hev v).2 ▸ Submodule.mem_map_of_mem (hφ v)
    have hcof' : ∀ᶠ v in cofinite,
        ev v (φ v) = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
      filter_upwards [hvac, hM₁.std] with v h1 h2
      rw [h1, (hev v).1, h2]
    refine ⟨Unit, inferInstance, fun _ => ei,
      fun _ y => ∏ᶠ v, ev v (φ v) fun i => evalV F v (y i),
      fun _ => GlobalTheory.AdelicCoordSB.finprod_mem_SB F _ (fun v => ev v (φ v)) hSB hcof', fun f => ?_⟩
    rw [← pure_eq_pureA, hloc f φ hφ hvac, pure_eq_pureA, Fintype.sum_unique]
  | zero => exact hasTameExp_zero e
  | add x y _ _ hx hy => exact hx.add hy
  | smul c x _ hx => exact hx.smul c

end GlobalTheory.EvTame
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvaluationGoodModelsIntertwineStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DoublingEv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evaluation_good_models_intertwine : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁)
    (M : Model σ X W) (M₁ : Model σ X₁ W₁) (ι : Matrix (Fin n) (Fin n₁) E) (ι' : Matrix (Fin d) (Fin d₁) E)
    (I : Set (Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁),
    M.IsGood B.ψ → M₁.IsGood B.ψ → IsEv B M M₁ ι ι' I e → IsTame F e := by
  first | exact @GlobalTheory.EvTame.isTame_of_isEv | exact GlobalTheory.EvTame.isTame_of_isEv | (intros; apply GlobalTheory.EvTame.isTame_of_isEv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.Gl2LocalToAdelicEmbedding
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.StdPar
open Formalism.UG (cT)
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.GLTwoHecke

section Matrices

variable {R : Type} [CommRing R]


end Matrices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ}

def singleNU (w : HeightOneSpectrum (𝓞 E)) : w.adicCompletion E →ₙ+* FiniteAdeleRing (𝓞 E) E where
  toFun := singleFin w
  map_mul' := singleFin_mul w
  map_zero' := map_zero _
  map_add' := map_add _



end GlobalTheory.GLTwoHecke

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardParabolicUnipotentMono
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardParabolicUnipotentMono
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
open Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.StdPar

section DimensionMonotonicity
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X : Matrix (Fin n) (Fin r) E}

theorem unip_maps_colSpan {T : Finset (Fin r)} {g : GAd σ J} (hg : g ∈ unip σ J X T) {I : Set (Fin r)}
    (hI : ∀ i ∈ I, ∀ l, l < i → l ∈ I) {y : Fin n → AF F ⊗[F] E} (hy : y ∈ colSpan F X I) :
    (matHom _ σ J g).1 *ᵥ y ∈ colSpan F X I := by
  have key : colSpan F X I ≤ (colSpan F X I).comap (matHom _ σ J g).1.mulVecLin := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, hi, rfl⟩
    have h1 := (Subgroup.mem_iInf.1 hg.1 i).2 _ (Submodule.subset_span ⟨i, rfl, rfl⟩)
    have h2 : colSpan F X {l | ∃ k ∈ T, l ≤ k ∧ k < i} ≤ colSpan F X I := by
      refine Submodule.span_mono (Set.image_mono ?_)
      rintro l ⟨k, -, hlk, hki⟩
      exact hI i hi l (lt_of_le_of_lt hlk hki)
    have h3 : (fun i => (adMat F X)ᵀ i) i ∈ colSpan F X I := Submodule.subset_span ⟨i, hi, rfl⟩
    show (matHom _ σ J g).1 *ᵥ _ ∈ colSpan F X I
    have := add_mem (h2 h1) h3
    rwa [sub_add_cancel] at this
  exact key hy

theorem unip_iff_colSpan {T : Finset (Fin r)} {g : GAd σ J} (hg : g ∈ unip σ J X T) {I : Set (Fin r)}
    (hI : ∀ i ∈ I, ∀ l, l < i → l ∈ I) (y : Fin n → AF F ⊗[F] E) :
    y ∈ colSpan F X I ↔ (matHom _ σ J g).1 *ᵥ y ∈ colSpan F X I := by
  refine ⟨unip_maps_colSpan hg hI, fun h => ?_⟩
  have := unip_maps_colSpan (inv_mem hg) hI h
  rwa [mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, one_mulVec] at this

end DimensionMonotonicity

theorem unip_mono_of_subset : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
      ∀ (S T : Finset (Fin r)), T ⊆ S → GlobalTheory.StdPar.unip σ J X T ≤ GlobalTheory.StdPar.unip σ J X S := by
  intro F E _ _ _ _ _ σ _ n J _ r X Y _ S T hTS g hg
  refine ⟨Subgroup.mem_iInf.2 fun j => ⟨unip_iff_colSpan hg ?_, fun y hy => ?_⟩,
    ⟨unip_iff_colSpan hg ?_, fun y hy => ?_⟩⟩
  · rintro i ⟨k, hk, hik, hkj⟩ l hl
    exact ⟨k, hk, (le_of_lt (lt_of_lt_of_le hl hik)), hkj⟩
  · refine Submodule.span_mono (Set.image_mono ?_) ((Subgroup.mem_iInf.1 hg.1 j).2 y hy)
    rintro l ⟨k, hk, h1, h2⟩
    exact ⟨k, hTS hk, h1, h2⟩
  · rintro i ⟨k, hk, hik⟩ l hl
    exact ⟨k, hk, le_of_lt (lt_of_lt_of_le hl hik)⟩
  · have hy' : y ∈ colPerp σ J X {i | ∃ k ∈ T, i ≤ k} := by
      simp only [colPerp, Submodule.mem_iInf] at hy ⊢
      rintro i ⟨k, hk, hik⟩
      exact hy i ⟨k, hTS hk, hik⟩
    refine Submodule.span_mono (Set.image_mono ?_) (hg.2.2 y hy')
    rintro l ⟨k, hk, h1⟩
    exact ⟨k, hTS hk, h1⟩

end GlobalTheory.StdPar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardParabolicUnipotentMonoStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardParabolicUnipotent_mono : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
      ∀ (S T : Finset (Fin r)), T ⊆ S → GlobalTheory.StdPar.unip σ J X T ≤ GlobalTheory.StdPar.unip σ J X S := by
  first | exact @GlobalTheory.StdPar.unip_mono_of_subset | exact GlobalTheory.StdPar.unip_mono_of_subset | (intros; apply GlobalTheory.StdPar.unip_mono_of_subset <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanTraceSymplecticFormOrthonormalFrames
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanTraceSymplecticFormOrthonormalFrames
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

noncomputable section

namespace GlobalTheory.SympFrames

def sgn {p q : ℕ} : Ix p q → ℂ := Sum.elim (fun _ => 1) (fun _ => -1)

theorem jm_eq_diagonal (p q : ℕ) : Jm p q = Matrix.diagonal (sgn (p := p) (q := q)) := by
  ext x y
  rcases x with x | x <;> rcases y with y | y <;>
    simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks, Matrix.diagonal, Matrix.one_apply, sgn] <;> split_ifs <;> simp

theorem lineSign_eq {p q r s : ℕ} (x : Ix p q) (y : Ix r s) : lineSign x y = sgn x * sgn y := by
  rcases x with x | x <;> rcases y with y | y <;> simp [lineSign, sgn]

theorem trace_jm {p q r s : ℕ} (c c' : Matrix (Ix p q) (Ix r s) ℂ) :
    (cᵀ * Jm p q * c'.map star * (Jm r s)ᵀ).trace = ∑ x, ∑ y, lineSign x y * c x y * star (c' x y) := by
  rw [jm_eq_diagonal, jm_eq_diagonal, Matrix.diagonal_transpose, Matrix.trace]
  simp only [Matrix.diag, Matrix.mul_diagonal, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul, lineSign_eq, Matrix.diagonal_apply, mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

theorem quad_eq_trace {α β : Type} [Fintype α] [Fintype β]
    (U U' : Matrix α β ℂ) (X : Matrix α α ℂ) (Y : Matrix β β ℂ) :
    ∑ i, ∑ j, ∑ k, ∑ l, U i j * X i k * Y j l * star (U' k l) = (Uᵀ * X * U'.map star * Yᵀ).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, k]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem frame_trace {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {P Q R S : ℕ}
    (X : Matrix α α ℂ) (Y : Matrix β β ℂ) (a b : ℂ) (A : Matrix α (Ix P Q) ℂ) (C : Matrix β (Ix R S) ℂ)
    (hA : Aᵀ * (a • X) * A.map star = Jm P Q) (hC : Cᵀ * (b • Y) * C.map star = Jm R S)
    (c c' : Matrix (Ix P Q) (Ix R S) ℂ) :
    a * b * ((A * c * Cᵀ)ᵀ * X * (A * c' * Cᵀ).map star * Yᵀ).trace =
      ∑ x, ∑ y, lineSign x y * c x y * star (c' x y) := by
  rw [← trace_jm, ← hA, ← hC]
  have hm : (A * c' * Cᵀ).map star = A.map star * c'.map star * (C.map star)ᵀ := by
    rw [show (star : ℂ → ℂ) = starRingEnd ℂ from rfl, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  rw [hm, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.transpose_smul, Matrix.trace_smul, smul_eq_mul, Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm C]
  simp only [Matrix.mul_assoc]
  ring

theorem symp_frames : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {α β : Type}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {P Q R S : ℕ} (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ), IsCMExt F E σ → Framed τ JA JB a b A C →
    ∀ (u u' : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (c c' : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ), At (evI F) u → At (evI F) u' →
    (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) → (∀ w, u'.map (piInf (τ w)) = A w * c' w * (C w)ᵀ) →
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (symp (R := AF F) (cA σ) (-1) JA JB u u')) =
      -2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im := by
  intro F E _ _ _ _ _ σ α β _ _ _ _ P Q R S τ JA JB a b A C hCM hF u u' c c' _ _ hu hu'
  have key : ∀ w, a * b * piInf (τ w) (hTens (cA σ) JA JB u u') =
      ∑ x, ∑ y, lineSign x y * c w x y * star (c' w x y) := by
    intro w
    have e : piInf (τ w) (hTens (cA σ) JA JB u u') = ∑ i, ∑ j, ∑ k, ∑ l, u.map (piInf (τ w)) i j *
        JA.map (piInf (τ w)) i k * JB.map (piInf (τ w)) j l * star (u'.map (piInf (τ w)) k l) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hTens, map_sum, map_mul, GlobalTheory.WrongSignPair.piInf_cA hCM, Matrix.map_apply]
    rw [e, hu w, hu' w, quad_eq_trace]
    exact frame_trace _ _ a b (A w) (C w) (hF.2.1 w).1 (hF.2.2 w).1 (c w) (c' w)
  rw [symp, GlobalTheory.WrongSignPair.trace_evI_trace hCM τ, Complex.im_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have h2 := key w
  rw [hF.1] at h2
  rw [← h2, map_mul, map_neg, map_one]
  simp only [Complex.neg_re, Complex.mul_im, Complex.I_re, Complex.I_im, neg_one_mul, zero_mul, one_mul, zero_add]
  ring

end GlobalTheory.SympFrames
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanTraceSymplecticFormOrthonormalFramesStatement
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanTrace_symplecticForm_orthonormalFrames : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {α β : Type}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {P Q R S : ℕ} (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ), IsCMExt F E σ → Framed τ JA JB a b A C →
    ∀ (u u' : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (c c' : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ), At (evI F) u → At (evI F) u' →
    (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) → (∀ w, u'.map (piInf (τ w)) = A w * c' w * (C w)ᵀ) →
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (symp (R := AF F) (cA σ) (-1) JA JB u u')) =
      -2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im := by
  first | exact @GlobalTheory.SympFrames.symp_frames | exact GlobalTheory.SympFrames.symp_frames | (intros; apply GlobalTheory.SympFrames.symp_frames <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartFrSgnFalseRigFr
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.StageDict

open GlobalTheory.ChainFr Matrix

variable {D : D7}

theorem jm_eq_diag {k p : ℕ} {ε : Fin k → ℝ} (h : ∀ a : Fin k, (ε a = 1 ∧ a.val < p) ∨ (ε a = -1 ∧ p ≤ a.val)) :
    Formalism.REAL.Jm (fun a : Fin k => decide (a.val < p)) = Matrix.diagonal (fun a => (ε a : ℂ)) := by
  unfold Formalism.REAL.Jm
  congr 1
  funext a
  rcases h a with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp [h1, h2]
  · have : ¬ a.val < p := by omega
    simp [h1, this]

theorem isUnit_of_isONBasis {k p : ℕ} {G s B : Matrix (Fin k) (Fin k) ℂ} (h : IsONBasis G s B p) : IsUnit B := by
  obtain ⟨ε, hε, h1, -⟩ := h
  have hd : IsUnit (Matrix.diagonal fun a => (ε a : ℂ)).det := by
    rw [Matrix.det_diagonal]
    refine IsUnit.mk0 _ (Finset.prod_ne_zero_iff.2 fun a _ => ?_)
    rcases hε a with ⟨e, -⟩ | ⟨e, -⟩ <;> simp [e]
  rw [← h1, Matrix.det_mul, Matrix.det_mul] at hd
  rw [Matrix.isUnit_iff_isUnit_det]
  exact isUnit_of_mul_isUnit_right hd

def sigIdx {V : HSp D} (r : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V) (h : r.Is) (τ : D.what₂.Tau) : ℕ := Classical.choose (h.2.2 τ).2

theorem sigIdx_spec {V : HSp D} (r : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V) (h : r.Is) (τ : D.what₂.Tau) :
    IsONBasis (gramAt D V τ) (r.s τ) (r.B τ) (sigIdx r h τ) := Classical.choose_spec (h.2.2 τ).2

def rigFr {V : HSp D} (r : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V) (h : r.Is) : Fr V where
  ε τ a := decide (a.val < sigIdx r h τ)
  fr τ := (r.B τ)⁻¹
  fr_unit τ := by
    have hu := isUnit_of_isONBasis (sigIdx_spec r h τ)
    exact (Matrix.isUnit_nonsing_inv_iff).2 hu
  fr_gram τ := by
    have hu := isUnit_of_isONBasis (sigIdx_spec r h τ)
    obtain ⟨ε, hε, h1, -⟩ := sigIdx_spec r h τ
    rw [jm_eq_diag hε, ← h1, Matrix.conjTranspose_nonsing_inv]
    have hu' : IsUnit (r.B τ)ᴴ.det := by
      rw [Matrix.det_conjTranspose]; exact ((Matrix.isUnit_iff_isUnit_det _).1 hu).star
    have hu0 : IsUnit (r.B τ).det := (Matrix.isUnit_iff_isUnit_det _).1 hu
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu0, Matrix.mul_one, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hu', Matrix.one_mul]

theorem onb_rigFr {V : HSp D} (r : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V) (h : r.Is) (τ : D.what₂.Tau) : (rigFr r h).onb τ = r.B τ := by
  have hu0 : IsUnit (r.B τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (isUnit_of_isONBasis (sigIdx_spec r h τ))
  simp only [Fr.onb, rigFr]
  exact Matrix.nonsing_inv_nonsing_inv _ hu0

theorem cart_rigFr {V : HSp D} (r : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V) (h : r.Is) (τ : D.what₂.Tau) : (rigFr r h).cart τ = r.s τ := by
  have hu0 : IsUnit (r.B τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (isUnit_of_isONBasis (sigIdx_spec r h τ))
  obtain ⟨ε, hε, -, h2⟩ := sigIdx_spec r h τ
  simp only [Fr.cart, rigFr]
  rw [Matrix.nonsing_inv_nonsing_inv _ hu0, jm_eq_diag hε, ← h2, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu0, Matrix.mul_one]

theorem cart_frSgn_true_rigFr {V : HSp D} (r : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V) (h : r.Is) (τ : D.what₂.Tau) :
    (GlobalTheory.SquareComm.frSgn true (rigFr r h)).cart τ = -r.s τ := by
  rw [← cart_rigFr r h τ]
  simp only [Fr.cart, GlobalTheory.SquareComm.frSgn]
  have e' : Formalism.REAL.Jm (fun a => xor true ((rigFr r h).ε τ a)) = -Formalism.REAL.Jm ((rigFr r h).ε τ) := by
    ext a b
    by_cases hab : a = b
    · subst hab; cases h' : (rigFr r h).ε τ a <;> simp [Formalism.REAL.Jm, h']
    · simp [Formalism.REAL.Jm, hab]
  rw [e', Matrix.mul_neg, Matrix.neg_mul]

theorem cart_frSgn_false_rigFr {V : HSp D} (r : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V) (h : r.Is) (τ : D.what₂.Tau) :
    (GlobalTheory.SquareComm.frSgn false (rigFr r h)).cart τ = r.s τ := by
  rw [← cart_rigFr r h τ]
  simp [Fr.cart, GlobalTheory.SquareComm.frSgn]

theorem stage_sizes (i j : Fin D.R.m) {p q a a' : ℕ} (hp : p ≤ pp D j) (hq : q ≤ qq D j)
    (ha : a + 2 * pp D j = rankV D (i + 1) (j + 1) + 2 * p) (ha' : a' + 2 * qq D j = rankV D i j + 2 * q) :
    Even (a + a') ∧ a' + 2 * (2 * (p + q) + 1) < a ∧ 2 * (p + q) + 1 < a' ∧
      a + a' ≤ rankV D (i + 1) (j + 1) + rankV D i j := by
  obtain ⟨u, hu⟩ := D.R.t_odd
  obtain ⟨v, hv⟩ := D.R.m_even
  obtain ⟨w, hw⟩ := D.R.k_even
  have e : rankV D (i + 1) (j + 1) = rankV D i j + D.R.t + sLen D := by simp only [rankV]; ring
  have r1 : rankV D i j = D.R.r + j.1 * D.R.t + i.1 * sLen D := rfl
  have r3 : D.R.r = D.R.k + D.R.m - 1 := rfl
  have r4 : sLen D = D.R.r + 6 := rfl
  have h1 := D.R.m_add_three_le_k
  have h2 := D.R.three_m_lt_t
  have h3 := D.R.two_le_m
  have hj := j.2
  simp only [pp, qq] at hp hq ha ha'
  refine ⟨Nat.even_iff.2 (by omega), by omega, by omega, by omega⟩

end GlobalTheory.StageDict

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryPairPartnerInverseTranspose
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryPairPartnerInverseTranspose
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilPairPartner

theorem map_mul_map_inv {R S : Type} [Field R] [CommRing S] (f : R →+* S) {n : Type} [Fintype n] [DecidableEq n]
    (M : Matrix n n R) (h : M.det ≠ 0) : M.map f * (M⁻¹).map f = 1 := by
  rw [← Matrix.map_mul, M.mul_nonsing_inv (isUnit_iff_ne_zero.mpr h), Matrix.map_one _ f.map_zero f.map_one]

theorem map_inv_mul_map {R S : Type} [Field R] [CommRing S] (f : R →+* S) {n : Type} [Fintype n] [DecidableEq n]
    (M : Matrix n n R) (h : M.det ≠ 0) : (M⁻¹).map f * M.map f = 1 := by
  rw [← Matrix.map_mul, M.nonsing_inv_mul (isUnit_iff_ne_zero.mpr h), Matrix.map_one _ f.map_zero f.map_one]

theorem map_smul_eq {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {m n : Type} (r : R) (M : Matrix m n R) :
    (r • M).map f = f r • M.map f := by
  ext i j
  simp

theorem conj_inv_transpose {S : Type} [CommRing S] (c : S →+* S) {n : Type} [Fintype n] [DecidableEq n] (ξ u : S)
    (hu : IsUnit u) (B Bi K G N : Matrix n n S) (hb : Bᵀ * K * B.map c = K) (hBB : B * Bi = 1) (hBB' : Bi * B = 1)
    (hK : ξ • K = u • N) (hGN : G * N = 1) (hNG : N * G = 1) : Bi.map c * G * Biᵀ = G := by
  have hbN : Bᵀ * N * B.map c = N := by
    have h1 : Bᵀ * (ξ • K) * B.map c = ξ • K := by rw [Matrix.mul_smul, Matrix.smul_mul, hb]
    rw [hK, Matrix.mul_smul, Matrix.smul_mul] at h1
    exact hu.smul_left_cancel.mp h1
  have hcc : Bi.map c * B.map c = 1 := by
    rw [← Matrix.map_mul, hBB', Matrix.map_one _ c.map_zero c.map_one]
  have hTT : Biᵀ * Bᵀ = 1 := by rw [← Matrix.transpose_mul, hBB, Matrix.transpose_one]
  calc Bi.map c * G * Biᵀ = Bi.map c * G * Biᵀ * (N * G) := by rw [hNG, Matrix.mul_one]
    _ = Bi.map c * G * Biᵀ * ((Bᵀ * N * B.map c) * G) := by rw [hbN]
    _ = Bi.map c * G * (Biᵀ * Bᵀ) * N * B.map c * G := by simp only [Matrix.mul_assoc]
    _ = Bi.map c * (G * N) * B.map c * G := by rw [hTT, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = G := by rw [hGN, Matrix.mul_one, hcc, Matrix.one_mul]

theorem pair_partner : ∀ (D : D7) (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E)
    (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
    ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
    ∀ (a : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA))
      (b : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB)),
      ∃ (g : GA D S) (h : GA D T), mt T h = a.1.1 ∧ mt S g = (b⁻¹).1.1ᵀ := by
  intro D S T JA JB ξ hA hB a b
  have hmap : ∀ {m n : Type} (X : Matrix m n (AE D)),
      X.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) = X.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) :=
    fun X => Matrix.ext fun i j => rfl

  have ha : (a.1.val)ᵀ * incM D.host.F JA * (a.1.val).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) = incM D.host.F JA := a.2
  set A : Matrix (Fin T.rank) (Fin T.rank) (AE D) := a.1.val with hAdef
  have hJA : incM D.host.F JA = (incM D.host.F T.gram)ᵀ := by
    rw [hA]; rfl
  rw [hJA] at ha
  have ha' := congrArg Matrix.transpose ha
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc] at ha'
  have hmemA : a.1 ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (AF D.host.F) D.sp.cm.sig T.gram := by
    show Formalism.UG.cT _ a.1.val * _ * a.1.val = _
    simp only [Formalism.UG.cT, hmap]
    rw [Matrix.mul_assoc]
    exact ha'

  obtain ⟨cR, hcR⟩ : ∃ f, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig = f := ⟨_, rfl⟩
  have hb : (b.1.val)ᵀ * incM D.host.F JB * (b.1.val).map cR = incM D.host.F JB := by
    rw [← hcR, hmap]; exact b.2
  have hBB : b.1.val * (b⁻¹).1.val = 1 := by
    rw [Subgroup.coe_inv]; exact (b.1).mul_inv
  have hBB' : (b⁻¹).1.val * b.1.val = 1 := by
    rw [Subgroup.coe_inv]; exact (b.1).inv_mul
  obtain ⟨B, hBdef⟩ : ∃ B : Matrix (Fin S.rank) (Fin S.rank) (AE D), b.1.val = B := ⟨_, rfl⟩
  obtain ⟨Bi, hBidef⟩ : ∃ B : Matrix (Fin S.rank) (Fin S.rank) (AE D), (b⁻¹).1.val = B := ⟨_, rfl⟩
  rw [hBdef] at hb hBB hBB'
  rw [hBidef] at hBB hBB'
  have hGN := GlobalTheory.WeilPairPartner.map_mul_map_inv (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F)) S.gram
    (GlobalTheory.VolHeckeCompare.gram_det_ne_zero S)
  have hNG := GlobalTheory.WeilPairPartner.map_inv_mul_map (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F)) S.gram
    (GlobalTheory.VolHeckeCompare.gram_det_ne_zero S)
  have hsm : incM D.host.F (D.host.xi0 • S.gram⁻¹) = inclR (F := D.host.F) (AF D.host.F) D.host.xi0 •
      incM D.host.F S.gram⁻¹ :=
    GlobalTheory.WeilPairPartner.map_smul_eq _ _ _
  have hu : IsUnit (inclR (F := D.host.F) (AF D.host.F) D.host.xi0) :=
    (isUnit_iff_ne_zero.mpr (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)).map _
  have hcore := GlobalTheory.WeilPairPartner.conj_inv_transpose cR ξ _ hu B Bi (incM D.host.F JB) (incM D.host.F S.gram)
    (incM D.host.F S.gram⁻¹) hb hBB hBB' (hB.trans hsm) hGN hNG
  have hTT : Biᵀ * Bᵀ = 1 := by
    rw [← Matrix.transpose_mul, hBB, Matrix.transpose_one]
  let gU : GL (Fin S.rank) (AE D) :=
    ⟨Biᵀ, Bᵀ, hTT, by rw [← Matrix.transpose_mul, hBB', Matrix.transpose_one]⟩
  have hmemB : gU ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (AF D.host.F) D.sp.cm.sig S.gram := by
    show Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) Biᵀ * incM D.host.F S.gram * Biᵀ =
      incM D.host.F S.gram
    rw [hcR]
    simp only [Formalism.UG.cT, Matrix.transpose_map, Matrix.transpose_transpose]
    exact hcore
  refine ⟨⟨gU, hmemB⟩, ⟨a.1, hmemA⟩, rfl, ?_⟩
  show Biᵀ = ((b⁻¹).1.val)ᵀ
  rw [hBidef]

end GlobalTheory.WeilPairPartner
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryPairPartnerInverseTransposeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryPair_partner_inverse_transpose : ∀ (D : D7) (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E)
    (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
    ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
    ∀ (a : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA))
      (b : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB)),
      ∃ (g : GA D S) (h : GA D T), mt T h = a.1.1 ∧ mt S g = (b⁻¹).1.1ᵀ := by
  first | exact @GlobalTheory.WeilPairPartner.pair_partner | exact GlobalTheory.WeilPairPartner.pair_partner | (intros; apply GlobalTheory.WeilPairPartner.pair_partner <;> assumption)
end
end
