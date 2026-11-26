module

public import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointMajorantFramesGiveMajorants
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointLatticeIntersectionSelfDualProperties
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StepLevelTLat
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NumericalFamilyShapeGaps
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CasimirScalarOfCapelliDeterminantEigenvalue
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ZhatSectionExists

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RootMeasureTransportDoubleCoset
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RootMeasureTransportDoubleCoset
noncomputable section

open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S
open scoped ENNReal

namespace GlobalTheory.Amp.RootMove

variable {k r : ℕ}

theorem _root_.GlobalTheory.Amp.RootMove.det_Hpk : IsUnit (_root_.Formalism.QuantumDeterminants.Hpk k r).det := by
  refine isUnit_iff_exists_inv.2 ⟨(_root_.Formalism.QuantumDeterminants.Hpk k r).det, ?_⟩
  rw [← Matrix.det_mul, _root_.Formalism.QuantumDeterminants.GBasic.Hpk_sq, Matrix.det_one]

theorem _root_.GlobalTheory.Amp.RootMove.unit_det {g : _root_.Formalism.MainNotions.S.MatKR k r} (hg : g ∈ _root_.Formalism.QuantumDeterminants.UH (_root_.Formalism.QuantumDeterminants.Hpk k r)) :
    IsUnit g.det := _root_.Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hg

def lr (a b : MatKR k r) : Mt k r → Mt k r := fun x => fun i j => (a * Matrix.of x * b) i j

theorem _root_.GlobalTheory.Amp.RootMove.continuous_lr (a b : _root_.Formalism.MainNotions.S.MatKR k r) :
    Continuous (_root_.GlobalTheory.Amp.RootMove.lr a b) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [_root_.GlobalTheory.Amp.RootMove.lr, Matrix.mul_apply, Matrix.of_apply]
  fun_prop

private theorem isClosed_Nset' : IsClosed (_root_.Formalism.QuantumDeterminants.Nset k r) := by
  have hent : ∀ i j, Continuous fun g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ => g i j :=
    fun i j => (continuous_apply j).comp (continuous_apply i)
  have e : _root_.Formalism.QuantumDeterminants.Nset k r = {g | gᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * g = _root_.Formalism.QuantumDeterminants.Hpk k r} ∩
      ((⋂ (a : Fin r) (i : Fin (2 * r + k + 1)) (_ : (a : ℕ) ≤ i),
        {g | g i (_root_.Formalism.QuantumDeterminants.eI k r a) = if i = _root_.Formalism.QuantumDeterminants.eI k r a then 1 else 0}) ∩
      ⋂ (i : Fin (2 * r + k + 1)) (j : Fin (2 * r + k + 1)) (_ : r ≤ (j : ℕ)) (_ : (j : ℕ) ≤ r + k)
        (_ : r ≤ (i : ℕ)), {g | g i j = if i = j then 1 else 0}) := by
    ext g
    simp only [_root_.Formalism.QuantumDeterminants.Nset, _root_.Formalism.QuantumDeterminants.UH, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [e]
  refine IsClosed.inter (isClosed_eq ?_ continuous_const) (IsClosed.inter ?_ ?_)
  · exact (continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id
  · exact isClosed_iInter fun a => isClosed_iInter fun i => isClosed_iInter fun _ =>
      isClosed_eq (hent _ _) continuous_const
  · exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_eq (hent _ _) continuous_const

theorem _root_.GlobalTheory.Amp.RootMove.measurableSet_notR (g : _root_.Formalism.MainNotions.S.MatKR k r) :
    MeasurableSet {x : _root_.Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∉ _root_.Formalism.MainNotions.S.Rset k r g} := by
  have h1 : Continuous fun x : _root_.Formalism.QuantumDeterminants.Mt k r =>
      (Matrix.of x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) := continuous_id
  have h2 : Continuous fun x : _root_.Formalism.QuantumDeterminants.Mt k r =>
      (g * Matrix.of x * g⁻¹ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :=
    (continuous_const.matrix_mul h1).matrix_mul continuous_const
  have hc : IsClosed {x : _root_.Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ _root_.Formalism.MainNotions.S.Rset k r g} :=
    (isClosed_Nset'.preimage h1).inter (isClosed_Nset'.preimage h2)
  exact hc.measurableSet.compl

theorem _root_.GlobalTheory.Amp.RootMove.measurable_rootCoords (z : Fin (2 * r + k + 1) → ℂ) (p : _root_.Formalism.MainNotions.S.Point ℂ (r + 1)) :
    Measurable (_root_.Formalism.MainNotions.S.rootCoords k r z p) := by
  refine Measurable.of_eval fun q => Continuous.measurable ?_
  by_cases hi : ((q : Fin (r + 1) × Fin (r + 1)).1 : ℕ) < r
  · simp only [_root_.Formalism.MainNotions.S.rootCoords, _root_.Formalism.MainNotions.S.flagMat, hi, dite_true, Matrix.mulVec, dotProduct, Matrix.of_apply]
    fun_prop
  · simp only [_root_.Formalism.MainNotions.S.rootCoords, _root_.Formalism.MainNotions.S.flagMat, hi, dite_false]
    exact continuous_const

private theorem flagMat_conj_eq_of_mem_UWset {z : Fin (2 * r + k + 1) → ℂ}
    {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : h ∈ _root_.Formalism.QuantumDeterminants.UWset k r z)
    (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    _root_.Formalism.MainNotions.S.flagMat k r z (h * X * h⁻¹) = _root_.Formalism.MainNotions.S.flagMat k r z X := by
  have hfix : ∀ {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}, g ∈ _root_.Formalism.QuantumDeterminants.UWset k r z →
      ∀ c, g *ᵥ _root_.Formalism.QuantumDeterminants.fvec k r z c = _root_.Formalism.QuantumDeterminants.fvec k r z c := by
    intro g hg c
    obtain ⟨-, hb, hz⟩ := hg
    unfold _root_.Formalism.QuantumDeterminants.fvec
    split_ifs with hc
    · exact (hb _).1
    · exact hz
  obtain ⟨hU, hb, -⟩ := id hh
  have hrow : ∀ (a : Fin r) (j : Fin (2 * r + k + 1)),
      h (_root_.Formalism.QuantumDeterminants.eI k r a) j = if _root_.Formalism.QuantumDeterminants.eI k r a = j then 1 else 0 := by
    intro a j
    have hτ : _root_.Formalism.QuantumDeterminants.WeylGroupFacts.tau k r (_root_.Formalism.QuantumDeterminants.esI k r a) = _root_.Formalism.QuantumDeterminants.eI k r a := by
      have := a.isLt
      ext
      simp only [_root_.Formalism.QuantumDeterminants.WeylGroupFacts.tau, _root_.Formalism.QuantumDeterminants.esI, _root_.Formalism.QuantumDeterminants.eI]
      by_cases hc : 2 * r + k - (a : ℕ) < r ∨ r + k < 2 * r + k - (a : ℕ)
      · simp only [hc, ↓reduceIte]; omega
      · omega
    rw [← hτ]
    exact _root_.Formalism.QuantumDeterminants.WeylGroupFacts.row_of_fixed_col hU _ (_root_.Formalism.QuantumDeterminants.WeylGroupFacts.col_of_fix (hb a).2) j
  ext i j
  simp only [_root_.Formalism.MainNotions.S.flagMat, Matrix.of_apply]
  split_ifs with hi
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hfix (_root_.Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hh), _root_.Formalism.QuantumDeterminants.WeylGroupFacts.mulVec_apply_of_row _ _ (hrow _)]
  all_goals rfl

theorem _root_.GlobalTheory.Amp.RootMove.rootMeas_move : ∀ (D : _root_.Formalism.BasicNotions.D7) (z z' : Fin (2 * D.R.rS + D.R.k + 1) → ℂ) (p : _root_.Formalism.MainNotions.S.Point ℂ (D.R.rS + 1)) (g a a' : _root_.Formalism.MainNotions.S.MatKR D.R.k D.R.rS) (μ : Measure (_root_.Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)), _root_.Formalism.QuantumDeterminants.inWb D.R.k D.R.rS z → _root_.Formalism.QuantumDeterminants.inWb D.R.k D.R.rS z' → 0 < _root_.Formalism.QuantumDeterminants.Tz D.R.k D.R.rS z → 0 < _root_.Formalism.QuantumDeterminants.Tz D.R.k D.R.rS z' → g ∈ _root_.Formalism.QuantumDeterminants.UH (_root_.Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) → a ∈ _root_.Formalism.QuantumDeterminants.Sset D.R.k D.R.rS z → a' ∈ _root_.Formalism.QuantumDeterminants.Sset D.R.k D.R.rS z' → _root_.Formalism.MainNotions.S.IsRootMeasR D z z' p g μ → _root_.Formalism.MainNotions.S.IsRootMeasR D z z' p (a * g * a'⁻¹) (μ.map fun x => fun i j => (a' * Matrix.of x * a'⁻¹) i j) := by
  intro D z z' p g a a' μ hz hz' _ _ _ ha ha' hμ
  obtain ⟨h, hh, m, hm, rfl⟩ := ha
  obtain ⟨h', hh', m', hm', rfl⟩ := ha'
  obtain ⟨n, hn, n', hn', g₀, rfl, hZ, μ₀, hnull, hmap, rfl⟩ := hμ
  have hd : IsUnit h.det := _root_.Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hh.1
  have hd' : IsUnit h'.det := _root_.Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hh'.1
  have hdm' : IsUnit m'.det := _root_.Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh ((_root_.Formalism.QuantumDeterminants.WeylGroupFacts.nset_iff m').1 hm').1
  have hc' : Continuous (_root_.GlobalTheory.Amp.RootMove.lr h' h'⁻¹) :=
    _root_.GlobalTheory.Amp.RootMove.continuous_lr h' h'⁻¹
  refine ⟨h * (m * n) * h⁻¹, (_root_.Formalism.QuantumDeterminants.uWNormal _ _ z hz h hh _ (_root_.Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_mul hm hn)).1,
    h' * (n' * m'⁻¹) * h'⁻¹, (_root_.Formalism.QuantumDeterminants.uWNormal _ _ z' hz' h' hh' _ (_root_.Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_mul hn' (_root_.Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_inv hm'))).1,
    h * g₀ * h'⁻¹, ?_, ?_, μ₀.map (_root_.GlobalTheory.Amp.RootMove.lr h' h'⁻¹), ?_, ?_, ?_⟩
  · rw [Matrix.mul_inv_rev]
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hd,
      Matrix.nonsing_inv_mul_cancel_left _ _ hd']
  · have hF : h⁻¹ * _root_.Formalism.QuantumDeterminants.Fm _ _ z = _root_.Formalism.QuantumDeterminants.Fm _ _ z := _root_.Formalism.QuantumDeterminants.UW_F (_root_.Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hh)
    have hF' : h'⁻¹ * _root_.Formalism.QuantumDeterminants.Fm _ _ z' = _root_.Formalism.QuantumDeterminants.Fm _ _ z' := _root_.Formalism.QuantumDeterminants.UW_F (_root_.Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hh')
    have hU : (h⁻¹)ᴴ * _root_.Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * h⁻¹ = _root_.Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := _root_.Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hh.1
    have hU2 : (h⁻¹)ᴴ * _root_.Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS = _root_.Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * h := by
      conv_rhs => rw [← hU]
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.mul_one]
    have key : (_root_.Formalism.QuantumDeterminants.Fm _ _ z)ᴴ * _root_.Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * h = (_root_.Formalism.QuantumDeterminants.Fm _ _ z)ᴴ * _root_.Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := by
      rw [Matrix.mul_assoc, ← hU2, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, hF]
    have E : (_root_.Formalism.QuantumDeterminants.Fm _ _ z)ᴴ * _root_.Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (h * g₀ * h'⁻¹) * _root_.Formalism.QuantumDeterminants.Fm _ _ z' =
        (_root_.Formalism.QuantumDeterminants.Fm _ _ z)ᴴ * _root_.Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * g₀ * _root_.Formalism.QuantumDeterminants.Fm _ _ z' := by
      calc _ = ((_root_.Formalism.QuantumDeterminants.Fm _ _ z)ᴴ * _root_.Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * h) * g₀ * (h'⁻¹ * _root_.Formalism.QuantumDeterminants.Fm _ _ z') := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [key, hF']
    rw [← hZ]
    unfold _root_.Formalism.MainNotions.S.ZhatO
    rw [_root_.Formalism.QuantumDeterminants.Zhat_eq, _root_.Formalism.QuantumDeterminants.Zhat_eq, E]
  · rw [Measure.map_apply hc'.measurable (_root_.GlobalTheory.Amp.RootMove.measurableSet_notR _)]
    refine measure_mono_null ?_ hnull
    intro x hx
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hx ⊢
    intro hR
    apply hx
    obtain ⟨hR1, hR2⟩ := hR
    have e : (h * g₀ * h'⁻¹) * (h' * Matrix.of x * h'⁻¹) * (h * g₀ * h'⁻¹)⁻¹ =
        h * (g₀ * Matrix.of x * g₀⁻¹) * h⁻¹ := by
      simp only [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hd', Matrix.mul_assoc,
        Matrix.nonsing_inv_mul_cancel_left _ _ hd']
    refine ⟨(_root_.Formalism.QuantumDeterminants.uWNormal _ _ z' hz' h' hh' _ hR1).1, ?_⟩
    change (h * g₀ * h'⁻¹) * (h' * Matrix.of x * h'⁻¹) * (h * g₀ * h'⁻¹)⁻¹ ∈ _
    rw [e]
    exact (_root_.Formalism.QuantumDeterminants.uWNormal _ _ z hz h hh _ hR2).1
  · rw [Measure.map_map (_root_.GlobalTheory.Amp.RootMove.measurable_rootCoords z' p) hc'.measurable]
    convert hmap using 2
    funext x
    have hx := flagMat_conj_eq_of_mem_UWset hh' (Matrix.of x)
    simp only [Function.comp_apply]
    unfold _root_.Formalism.MainNotions.S.rootCoords
    exact congrArg (fun M => fun q : ↥(_root_.Formalism.MainNotions.S.rootPat p) => M q.1.1 q.1.2) hx
  · have E : ∀ X : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ,
        (h' * m') * (n'⁻¹ * X * n') * (h' * m')⁻¹ =
          (h' * (n' * m'⁻¹) * h'⁻¹)⁻¹ * (h' * X * h'⁻¹) * (h' * (n' * m'⁻¹) * h'⁻¹) := by
      intro X
      simp only [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hd',
        Matrix.nonsing_inv_nonsing_inv _ hdm', Matrix.mul_assoc,
        Matrix.nonsing_inv_mul_cancel_left _ _ hd']
    rw [Measure.map_map, Measure.map_map]
    · congr 1
      funext x i j
      exact congrArg (fun M : Matrix _ _ ℂ => M i j) (E (Matrix.of x))
    all_goals exact (_root_.GlobalTheory.Amp.RootMove.continuous_lr _ _).measurable

end GlobalTheory.Amp.RootMove
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RootMeasureTransportDoubleCosetStatement
open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rootMeasure_transport_doubleCoset : ∀ (D : D7) (z z' : Fin (2 * D.R.rS + D.R.k + 1) → ℂ) (p : Point ℂ (D.R.rS + 1)) (g a a' : MatKR D.R.k D.R.rS) (μ : Measure (Mt D.R.k D.R.rS)), inWb D.R.k D.R.rS z → inWb D.R.k D.R.rS z' → 0 < Tz D.R.k D.R.rS z → 0 < Tz D.R.k D.R.rS z' → g ∈ UH (Hpk D.R.k D.R.rS) → a ∈ Sset D.R.k D.R.rS z → a' ∈ Sset D.R.k D.R.rS z' → IsRootMeasR D z z' p g μ → IsRootMeasR D z z' p (a * g * a'⁻¹) (μ.map fun x => fun i j => (a' * Matrix.of x * a'⁻¹) i j) := by
  first | exact @GlobalTheory.Amp.RootMove.rootMeas_move | exact GlobalTheory.Amp.RootMove.rootMeas_move | (intros; apply GlobalTheory.Amp.RootMove.rootMeas_move <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ComplexSpanAtRealPlaceAutPointLatticeProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImportsMore
namespace GlobalTheory.IntegralBoundFlagMeasures

open NumberField

theorem main {E : Type} [Field E] [NumberField E] {n : ℕ}
    (Λ : Submodule (NumberField.RingOfIntegers E) (Fin n → E)) :
    ∀ y ∈ Submodule.span E (↑Λ : Set (Fin n → E)),
      ∃ (c : NumberField.RingOfIntegers E), c ≠ (0 : NumberField.RingOfIntegers E) ∧ c • y ∈ Λ := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x z _ _ hx hz =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have h1 : (a * b) • x = b • (a • x) := by rw [mul_comm, mul_smul]
    have h2 : (a * b) • z = a • (b • z) := by rw [mul_smul]
    rw [smul_add, h1, h2]
    exact Λ.add_mem (Λ.smul_mem _ hax) (Λ.smul_mem _ hbz)
  | smul e x _ hx =>
    obtain ⟨c, hc, hcx⟩ := hx
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 E)) e
    simp only at hab
    have hb : (b : 𝓞 E) ≠ 0 := nonZeroDivisors.ne_zero b.2
    refine ⟨(b : 𝓞 E) * c, mul_ne_zero hb hc, ?_⟩
    have key : (b : 𝓞 E) • (e • x) = a • x := by
      rw [← algebraMap_smul E (b : 𝓞 E) (e • x), smul_smul, mul_comm, hab, algebraMap_smul]
    have : ((b : 𝓞 E) * c) • (e • x) = a • (c • x) := by
      rw [mul_comm, mul_smul, key, smul_comm]
    rw [this]
    exact Λ.smul_mem _ hcx

end GlobalTheory.IntegralBoundFlagMeasures
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ComplexSpanAtRealPlaceAutPointLatticeProperties
open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset

noncomputable section

namespace GlobalTheory.RealSpan

section General

variable {E A : Type} [Field E] [CommRing A] {n : ℕ}

theorem span_image_span (ι : E →+* A) (S : Set (Fin n → E)) :
    Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' S) =
      Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) ''
        (Submodule.span E S : Set (Fin n → E))) := by
  refine le_antisymm (Submodule.span_mono (Set.image_mono Submodule.subset_span)) ?_
  rw [Submodule.span_le]
  rintro _ ⟨w, hw, rfl⟩
  induction hw using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
  | zero =>
    have : (fun i => ι ((0 : Fin n → E) i)) = 0 := by funext i; simp
    simp only [this]
    exact zero_mem _
  | add y z _ _ hy hz =>
    have : (fun i => ι ((y + z) i)) = (fun i => ι (y i)) + fun i => ι (z i) := by funext i; simp
    simp only [this]
    exact add_mem hy hz
  | smul c y _ hy =>
    have : (fun i => ι ((c • y) i)) = ι c • fun i => ι (y i) := by funext i; simp
    simp only [this]
    exact Submodule.smul_mem _ _ hy

theorem span_image_univ (ι : E →+* A) :
    Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' Set.univ) = ⊤ := by
  rw [eq_top_iff, ← (Pi.basisFun A (Fin n)).span_eq, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  refine Submodule.subset_span ⟨Pi.single j 1, trivial, ?_⟩
  funext i
  by_cases h : i = j
  · subst h; simp
  · simp [h]

theorem map_mulVec_image (ι : E →+* A) (Y : Matrix (Fin n) (Fin n) E) (w : Fin n → E) :
    Y.map ι *ᵥ (fun i => ι (w i)) = fun i => ι ((Y *ᵥ w) i) := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.mulVec, dotProduct, map_sum]

theorem map_mulVec_mem (ι : E →+* A) (Y : Matrix (Fin n) (Fin n) E) (S T : Set (Fin n → E))
    (h : ∀ u ∈ S, Y *ᵥ u ∈ T) (u : Fin n → A)
    (hu : u ∈ Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' S)) :
    Y.map ι *ᵥ u ∈ Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' T) := by
  induction hu using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, hw, rfl⟩ := hy
    exact Submodule.subset_span ⟨Y *ᵥ w, h w hw, (map_mulVec_image ι Y w).symm⟩
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [Matrix.mulVec_add]; exact add_mem hy hz
  | smul c y _ hy => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ _ hy

theorem map_mulVec_eq_zero (ι : E →+* A) (Y : Matrix (Fin n) (Fin n) E) (S : Set (Fin n → E))
    (h : ∀ u ∈ S, Y *ᵥ u = 0) (u : Fin n → A)
    (hu : u ∈ Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' S)) :
    Y.map ι *ᵥ u = 0 := by
  induction hu using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, hw, rfl⟩ := hy
    rw [map_mulVec_image, h w hw]
    funext i; simp
  | zero => rw [Matrix.mulVec_zero]
  | add y z _ _ hy hz => rw [Matrix.mulVec_add, hy, hz, add_zero]
  | smul c y _ hy => rw [Matrix.mulVec_smul, hy, smul_zero]

variable (σ : E →+* E) (s : A →+* A) (ι : E →+* A) (hc : ∀ e, s (ι e) = ι (σ e))
  (J : Matrix (Fin n) (Fin n) E)

include hc

theorem isSkew_map (Y : Matrix (Fin n) (Fin n) E) (h : IsSkew σ J Y) :
    IsSkew s (J.map ι) (Y.map ι) := by
  rw [← GlobalTheory.CoverRadiiEq.skew_iff] at h ⊢
  have h1 : Formalism.UG.cT s (Y.map ι) = (Formalism.UG.cT σ Y).map ι := by
    ext i j; simp [Formalism.UG.cT, hc]
  rw [h1, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add ι), h]
  simp

theorem inNil_map (W : Submodule E (Fin n → E)) (Y : Matrix (Fin n) (Fin n) E) (h : InNil σ J W Y) :
    InNil s (J.map ι) (Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' (W : Set (Fin n → E))))
      (Y.map ι) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨isSkew_map σ s ι hc J Y h1, fun u => ?_, fun u hu => ?_, map_mulVec_eq_zero ι Y _ h4⟩
  · rw [GlobalTheory.PerpBaseChange.perpSet_baseChange E A σ s ι n J W hc]
    exact map_mulVec_mem ι Y Set.univ _ (fun u _ => h2 u) u (by rw [span_image_univ]; trivial)
  · rw [GlobalTheory.PerpBaseChange.perpSet_baseChange E A σ s ι n J W hc] at hu
    exact map_mulVec_mem ι Y _ _ h3 u hu

theorem inCen_map (W : Submodule E (Fin n → E)) (Y : Matrix (Fin n) (Fin n) E) (h : InCen σ J W Y) :
    InCen s (J.map ι) (Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' (W : Set (Fin n → E))))
      (Y.map ι) := by
  refine ⟨inNil_map σ s ι hc J W Y h.1, fun u hu => ?_⟩
  rw [GlobalTheory.PerpBaseChange.perpSet_baseChange E A σ s ι n J W hc] at hu
  exact map_mulVec_eq_zero ι Y _ h.2 u hu

end General

section Lattice

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem exists_smul_mem (Λ : Submodule (𝓞 E) (Fin n → E)) (y : Fin n → E)
    (hy : y ∈ Submodule.span E (Λ : Set (Fin n → E))) :
    ∃ c : 𝓞 E, c ≠ 0 ∧ c • y ∈ Λ := by
  first
  | exact @_root_.GlobalTheory.IntegralBoundFlagMeasures.main
  | exact _root_.GlobalTheory.IntegralBoundFlagMeasures.main
  | (apply _root_.GlobalTheory.IntegralBoundFlagMeasures.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralBoundFlagMeasures.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralBoundFlagMeasures.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralBoundFlagMeasures.main ..)

omit [NumberField E] in
theorem mem_perpSet_span (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (S : Set (Fin n → E))
    (y : Fin n → E) :
    y ∈ perpSet σ J (Submodule.span E S) ↔ ∀ w ∈ S, Formalism.UG.hform σ J w y = 0 := by
  refine ⟨fun h w hw => h w (Submodule.subset_span hw), fun h w hw => ?_⟩
  induction hw using Submodule.span_induction with
  | mem w hw => exact h w hw
  | zero => simp [Formalism.UG.hform]
  | add u v _ _ hu hv => rw [Formalism.UG.P.csScale_hform_add_left, hu, hv, add_zero]
  | smul c u _ hu => rw [Formalism.UG.P.csScale_hform_smul_left, hu, mul_zero]

theorem span_perp (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (Λ R : Submodule (𝓞 E) (Fin n → E))
    (hΛ : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) :
    (Submodule.span E (Submodule.span (𝓞 E) {y | y ∈ Λ ∧ ∀ s ∈ R, Formalism.UG.hform σ J s y = 0} :
      Set (Fin n → E)) : Set (Fin n → E)) = perpSet σ J (Submodule.span E (R : Set (Fin n → E))) := by
  rw [Submodule.span_span_of_tower]
  ext y
  rw [mem_perpSet_span]
  constructor
  · intro hy w hw
    induction hy using Submodule.span_induction with
    | mem u hu => exact hu.2 w hw
    | zero => simp [Formalism.UG.hform]
    | add u v _ _ hu hv => rw [Formalism.UG.P.csScale_hform_add_right, hu, hv, add_zero]
    | smul c u _ hu => rw [Formalism.UG.P.csScale_hform_smul_right, hu, mul_zero]
  · intro hy
    obtain ⟨c, hc, hcy⟩ := exists_smul_mem Λ y (by rw [hΛ]; trivial)
    have hc1 : algebraMap (𝓞 E) E c ≠ 0 := by simpa using hc
    rw [← algebraMap_smul E c] at hcy
    have : y = (algebraMap (𝓞 E) E c)⁻¹ • algebraMap (𝓞 E) E c • y := by
      rw [smul_smul, inv_mul_cancel₀ hc1, one_smul]
    rw [this]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨hcy, fun w hw => ?_⟩)
    rw [Formalism.UG.P.csScale_hform_smul_right, hy w hw, mul_zero]

end Lattice

theorem conj_emb (I : AutInst) (v : InfinitePlace I.F) (e : I.E) :
    starRingEnd ℂ (I.φ v e) = I.φ v (starRingEnd I.E e) :=
  (I.cm.cmUnram.2.1 (I.φ v) e).symm

theorem spanAt_properties : ∀ (I : AutInst) (x : I.GA) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)), (∀ v, spanAt I R v = Submodule.span ℂ ((fun w : Fin I.n → I.E => fun i => I.φ v (w i)) '' (Submodule.span I.E (R : Set (Fin I.n → I.E)) : Set (Fin I.n → I.E)))) ∧ (∀ v, spanAt I (lamX I x) v = ⊤) ∧ (∀ v, (spanAt I (perpIn I x R) v : Set (Fin I.n → ℂ)) = perpSet (starRingEnd ℂ) (I.J.map (I.φ v)) (spanAt I R v)) ∧ (∀ Y : Matrix (Fin I.n) (Fin I.n) I.E, InNil (starRingEnd I.E) I.J (Submodule.span I.E (R : Set (Fin I.n → I.E))) Y → diagEmb I Y ∈ nilReal I R) ∧ ∀ Y : Matrix (Fin I.n) (Fin I.n) I.E, InCen (starRingEnd I.E) I.J (Submodule.span I.E (R : Set (Fin I.n → I.E))) Y → diagEmb I Y ∈ cenReal I R := by
  intro I x R
  have h1 : ∀ (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) v, spanAt I R v = Submodule.span ℂ
      ((fun w : Fin I.n → I.E => fun i => I.φ v (w i)) ''
        (Submodule.span I.E (R : Set (Fin I.n → I.E)) : Set (Fin I.n → I.E))) :=
    fun R v => span_image_span (I.φ v) _
  have hΛ := (GlobalTheory.PointLattice.lamX_selfDual I x).2.2.1
  refine ⟨h1 R, fun v => ?_, fun v => ?_, fun Y hY v => ?_, fun Y hY v => ?_⟩
  · rw [h1, hΛ]
    exact span_image_univ _
  · rw [h1, h1, GlobalTheory.PerpBaseChange.perpSet_baseChange _ _ (starRingEnd I.E) _ _ _ _ _ (conj_emb I v), perpIn,
      span_perp _ _ _ _ hΛ]
  · rw [h1]
    exact inNil_map _ _ _ (conj_emb I v) _ _ Y hY
  · rw [h1]
    exact inCen_map _ _ _ (conj_emb I v) _ _ Y hY

end GlobalTheory.RealSpan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ComplexSpanAtRealPlaceAutPointLatticePropertiesStatement
open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexSpanAtRealPlace_autPointLattice_properties : ∀ (I : AutInst) (x : I.GA) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)), (∀ v, spanAt I R v = Submodule.span ℂ ((fun w : Fin I.n → I.E => fun i => I.φ v (w i)) '' (Submodule.span I.E (R : Set (Fin I.n → I.E)) : Set (Fin I.n → I.E)))) ∧ (∀ v, spanAt I (lamX I x) v = ⊤) ∧ (∀ v, (spanAt I (perpIn I x R) v : Set (Fin I.n → ℂ)) = perpSet (starRingEnd ℂ) (I.J.map (I.φ v)) (spanAt I R v)) ∧ (∀ Y : Matrix (Fin I.n) (Fin I.n) I.E, InNil (starRingEnd I.E) I.J (Submodule.span I.E (R : Set (Fin I.n → I.E))) Y → diagEmb I Y ∈ nilReal I R) ∧ ∀ Y : Matrix (Fin I.n) (Fin I.n) I.E, InCen (starRingEnd I.E) I.J (Submodule.span I.E (R : Set (Fin I.n → I.E))) Y → diagEmb I Y ∈ cenReal I R := by
  first | exact @GlobalTheory.RealSpan.spanAt_properties | exact GlobalTheory.RealSpan.spanAt_properties | (intros; apply GlobalTheory.RealSpan.spanAt_properties <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ClosedSubgroupBesselUnitaryHaarUnique
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ClosedSubgroupBesselUnitaryHaarUnique
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

theorem hpk_ne_zero (k r : ℕ) : Hpk k r ≠ 0 := by
  intro h
  have := congrFun (congrFun h ⟨r, by omega⟩) ⟨r, by omega⟩
  simp only [Hpk, Matrix.zero_apply] at this
  split_ifs at this <;> first | omega | norm_num at this | skip
  all_goals simp_all

theorem isMatGroup_of_isClosedSub {k r : ℕ} {S : Set (Mat k r)} (hS : IsClosedSub k r S) :
    PI.IsMatGroup S := by
  obtain ⟨hU, hc, h1, hm, hi⟩ := hS
  refine ⟨hc, h1, hm, fun a ha => ⟨hi a ha, ?_⟩⟩
  by_cases hd : IsUnit a.det
  · exact Matrix.mul_nonsing_inv a hd
  · exfalso
    have h0 : a⁻¹ = 0 := Matrix.nonsing_inv_apply_not_isUnit a hd
    have hmem := hU (hi a ha)
    rw [h0] at hmem
    have : (0 : Mat k r)ᴴ * Hpk k r * 0 = Hpk k r := hmem
    simp at this
    exact hpk_ne_zero k r this.symm

theorem haarOn_unique : ∀ (k r : ℕ) (S : Set (Mat k r)) (μ μ' : Measure (Mt k r)), IsClosedSub k r S →
    IsHaarOn S μ → IsHaarOn S μ' → ∃ c : ENNReal, 0 < c ∧ c < ⊤ ∧ μ' = c • μ := by
  intro k r S μ μ' hS hμ hμ'
  exact (GlobalTheory.MatHaar.haar_unique_locFinite_openPos (2 * r + k + 1) S μ (isMatGroup_of_isClosedSub hS) hμ).1 μ' hμ'

end GlobalTheory.SgInf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ClosedSubgroupBesselUnitaryHaarUniqueStatement
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closedSubgroupBesselUnitary_haar_unique : ∀ (k r : ℕ) (S : Set (Mat k r)) (μ μ' : Measure (Mt k r)), IsClosedSub k r S → IsHaarOn S μ → IsHaarOn S μ' → ∃ c : ENNReal, 0 < c ∧ c < ⊤ ∧ μ' = c • μ := by
  first | exact @GlobalTheory.SgInf.haarOn_unique | exact GlobalTheory.SgInf.haarOn_unique | (intros; apply GlobalTheory.SgInf.haarOn_unique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsTraceOne
open NumberField

namespace GlobalTheory.TraceOnto

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem exists_star (x : 𝓞 E) : ∃ t : 𝓞 E, (t : E) = star (x : E) :=
  ⟨RingOfIntegers.mapRingHom (starRingEnd E) x, rfl⟩

def normTraceIdeal (E : Type) [Field E] [NumberField E] [StarRing E] : Ideal (𝓞 E) where
  carrier := {x | ∃ w : 𝓞 E, (w : E) + star (w : E) = (x : E) * star (x : E)}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro a b ⟨u, hu⟩ ⟨v, hv⟩
    obtain ⟨t, ht⟩ := exists_star b
    refine ⟨u + v + a * t, ?_⟩
    push_cast
    simp only [ht, star_add, star_mul', star_star]
    linear_combination hu + hv
  smul_mem' := by
    rintro c a ⟨u, hu⟩
    obtain ⟨t, ht⟩ := exists_star c
    refine ⟨c * t * u, ?_⟩
    simp only [smul_eq_mul]
    push_cast
    simp only [ht, star_mul', star_star]
    linear_combination ((c : E) * star (c : E)) * hu

theorem exists_trace_one : ∀ (E : Type) [Field E] [NumberField E] [StarRing E],
    Formalism.HermitianLatticesTheory.IsCMUnram E → ∃ w : 𝓞 E, (w : E) + star (w : E) = 1 := by
  intro E _ _ _ h
  have htop : normTraceIdeal E = ⊤ := by
    by_contra hne
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨θ, t, ht, hn⟩ := h.2.2 P hP
    apply hn
    apply hle
    have ht' : (t : E) = star (θ : E) := ht
    refine ⟨θ * t - θ * θ, ?_⟩
    push_cast
    simp only [ht', star_sub, star_mul', star_star]
    ring
  have h1 : (1 : 𝓞 E) ∈ normTraceIdeal E := htop ▸ Submodule.mem_top
  obtain ⟨w, hw⟩ := h1
  exact ⟨w, by simpa using hw⟩

end GlobalTheory.TraceOnto
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsIrrAndDenseOfIsFdegG
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.Dec

theorem IsFdegG.dense_span_orbit {G : Type} [MeasurableSpace G] {μ : Measure G} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {σ : G → (H →L[ℂ] H)} {d : ℝ} (h : IsFdegG μ σ d)
    (w : H) (hw : w ≠ 0) : Dense (Submodule.span ℂ (Set.range fun g => σ g w) : Set H) := by
  obtain ⟨hd, hint⟩ := h
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro u hu
  rw [Submodule.mem_orthogonal] at hu

  have hzero : ∀ g, ⟪u, σ g w⟫_ℂ = 0 := fun g =>
    inner_eq_zero_symm.mp (hu (σ g w) (Submodule.subset_span ⟨g, rfl⟩))

  have key := (hint w u w u).2
  have hfun : (fun g => ⟪u, σ g w⟫_ℂ * star ⟪u, σ g w⟫_ℂ) = fun _ => (0 : ℂ) := by
    funext g
    simp [hzero g]
  rw [hfun, integral_zero] at key
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hw' : ⟪w, w⟫_ℂ ≠ 0 := inner_self_ne_zero.mpr hw
  have huu : ⟪u, u⟫_ℂ = 0 := by
    rcases div_eq_zero_iff.mp key.symm with h1 | h1
    · exact (mul_eq_zero.mp h1).resolve_left hw'
    · exact absurd h1 hd'
  exact inner_self_eq_zero.mp huu

theorem isIrr_and_dense_of_isFdegG : ∀ (G : Type) [MeasurableSpace G] (μ : Measure G) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : G → (H →L[ℂ] H)) (d : ℝ), IsFdegG μ σ d → IsIrr σ ∧ ∀ w : H, w ≠ 0 → Dense (Submodule.span ℂ (Set.range fun g => σ g w) : Set H) := by
  intro G _ μ H _ _ _ σ d h
  refine ⟨?_, fun w hw => IsFdegG.dense_span_orbit h w hw⟩
  intro S hS hinv
  by_cases hbot : S = ⊥
  · exact Or.inl hbot
  · right
    obtain ⟨w, hwS, hw⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot

    have hsub : Submodule.span ℂ (Set.range fun g => σ g w) ≤ S := by
      rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      exact hinv g w hwS
    have hcl : closure ((Submodule.span ℂ (Set.range fun g => σ g w) : Submodule ℂ H) : Set H) ⊆ (S : Set H) :=
      closure_minimal (fun y hy => hsub hy) hS
    rw [Submodule.eq_top_iff']
    intro x
    exact hcl (by rw [(IsFdegG.dense_span_orbit h w hw).closure_eq]; exact Set.mem_univ x)

end GlobalTheory.Dec
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InitialLengthsProductMomentLe
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InitialLengthsProductMomentLe
open MeasureTheory Finset
open scoped ENNReal

namespace GlobalTheory.MomentHolder

theorem initial_product_moment_le :
    ∀ (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω) (r l : ℕ) (hl : l ≤ r + 1)
      (len : Fin (r + 1) → Ω → ℝ) (Ph : Ω → ℝ) (A Rr : ℝ), (∀ a, AEMeasurable (len a) ν) →
      (∀ a, ∀ᵐ x ∂ν, 0 < len a x) → AEMeasurable Ph ν → (∀ x, 0 ≤ Ph x) →
      ∫⁻ x, ENNReal.ofReal (Ph x) ∂ν = 1 → 0 ≤ A → 1 ≤ Rr →
      (∀ q ≤ (r + 1) ^ 2, ∫⁻ x, ENNReal.ofReal (len 0 x ^ (2 * q) * Ph x) ∂ν
        ≤ ENNReal.ofReal (A ^ q)) →
      (∀ a : Fin r, ∀ q ≤ (r + 1) ^ 2,
        ∫⁻ x, ENNReal.ofReal ((len a.succ x / len a.castSucc x) ^ (2 * q) * Ph x) ∂ν
          ≤ ENNReal.ofReal (Rr ^ (2 * q))) →
      ∫⁻ x, ENNReal.ofReal ((∏ a : Fin l, len (Fin.castLE hl a) x ^ 2) * Ph x) ∂ν
        ≤ ENNReal.ofReal ((A * Rr ^ (2 * r)) ^ l) := by
  intro Ω _ ν r l hl len Ph A Rr hlen hpos hPh h0 hmass hA hR hm0 hrat
  rcases Nat.eq_zero_or_pos l with rfl | hl0
  · simp [hmass]
  obtain ⟨s, rfl⟩ : ∃ s, l = s + 1 := ⟨l - 1, by omega⟩
  have hs : s ≤ r := by omega
  have hq' : ∀ q, q ≤ (s + 1) ^ 2 → q ≤ (r + 1) ^ 2 :=
    fun q hq => hq.trans (Nat.pow_le_pow_left (by omega) 2)
  have h1 : ∀ q ≤ (s + 1) ^ 2,
      ∫⁻ x, ENNReal.ofReal ((fun a : Fin (s + 1) => len (Fin.castLE hl a)) 0 x ^ (2 * q) * Ph x) ∂ν
        ≤ ENNReal.ofReal (A ^ q) := by
    intro q hq
    have e : Fin.castLE hl (0 : Fin (s + 1)) = 0 := Fin.ext (by simp)
    simp only [e]
    exact hm0 q (hq' q hq)
  have h2 : ∀ a : Fin s, ∀ q ≤ (s + 1) ^ 2,
      ∫⁻ x, ENNReal.ofReal (((fun a : Fin (s + 1) => len (Fin.castLE hl a)) a.succ x /
        (fun a : Fin (s + 1) => len (Fin.castLE hl a)) a.castSucc x) ^ (2 * q) * Ph x) ∂ν
        ≤ ENNReal.ofReal (Rr ^ (2 * q)) := by
    intro a q hq
    have e1 : Fin.castLE hl a.succ = (⟨a, by omega⟩ : Fin r).succ := Fin.ext (by simp)
    have e2 : Fin.castLE hl a.castSucc = (⟨a, by omega⟩ : Fin r).castSucc := Fin.ext (by simp)
    simp only [e1, e2]
    exact hrat _ q (hq' q hq)
  have key := product_moment_le Ω ν s (fun a => len (Fin.castLE hl a)) Ph A Rr
    (fun _ => hlen _) (fun _ => hpos _) hPh h0 hmass hA hR h1 h2
  refine key.trans (ENNReal.ofReal_le_ofReal ?_)
  exact pow_le_pow_left₀ (mul_nonneg hA (pow_nonneg (zero_le_one.trans hR) _))
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hR (by omega)) hA) _

end GlobalTheory.MomentHolder
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InitialLengthsProductMomentLeStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.initial_lengths_product_moment_le : ∀ (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω) (r l : ℕ) (hl : l ≤ r + 1) (len : Fin (r + 1) → Ω → ℝ) (Ph : Ω → ℝ) (A Rr : ℝ), (∀ a, AEMeasurable (len a) ν) → (∀ a, ∀ᵐ x ∂ν, 0 < len a x) → AEMeasurable Ph ν → (∀ x, 0 ≤ Ph x) → ∫⁻ x, ENNReal.ofReal (Ph x) ∂ν = 1 → 0 ≤ A → 1 ≤ Rr → (∀ q ≤ (r + 1) ^ 2, ∫⁻ x, ENNReal.ofReal (len 0 x ^ (2 * q) * Ph x) ∂ν ≤ ENNReal.ofReal (A ^ q)) → (∀ a : Fin r, ∀ q ≤ (r + 1) ^ 2, ∫⁻ x, ENNReal.ofReal ((len a.succ x / len a.castSucc x) ^ (2 * q) * Ph x) ∂ν ≤ ENNReal.ofReal (Rr ^ (2 * q))) → ∫⁻ x, ENNReal.ofReal ((∏ a : Fin l, len (Fin.castLE hl a) x ^ 2) * Ph x) ∂ν ≤ ENNReal.ofReal ((A * Rr ^ (2 * r)) ^ l) := by
  first | exact @GlobalTheory.MomentHolder.initial_product_moment_le | exact GlobalTheory.MomentHolder.initial_product_moment_le | (intros; apply GlobalTheory.MomentHolder.initial_product_moment_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassRatioRankFactor
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassRatioRankFactor
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas

theorem volU_succ_eq_mul (m : ℕ) :
    volU (m + 1) = volU m * (2 * Real.pi ^ (m + 1) / (m.factorial : ℝ) * 2 ^ m) := by
  have h : (m + 1) * (m + 1 - 1) / 2 = m * (m - 1) / 2 + m := by
    have := Nat.triangle_succ m
    simpa using this
  unfold volU sphV
  rw [Finset.prod_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le m)), h, pow_add]
  simp only [Nat.add_sub_cancel]
  ring

theorem vInv_pos_of_numberField (E : Type) [Field E] [NumberField E] : 0 < Formalism.HermitianLatticesTheory.vInv E := by
  unfold Formalism.HermitianLatticesTheory.vInv
  have : (0 : ℝ) < |(discr E : ℝ)| := abs_pos.mpr (by exact_mod_cast discr_ne_zero E)
  positivity

theorem mass_ratio_mul_unitary_volume :
    ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (M : ℕ), 1 ≤ M →
      Formalism.HermitianLatticesTheory.massRatioRightSide E M * volU M ^ Formalism.HermitianLatticesTheory.fDeg E =
        rankFac E M * volU (M - 1) ^ Formalism.HermitianLatticesTheory.fDeg E := by
  intro E _ _ _ M hM
  obtain ⟨m, rfl⟩ : ∃ m, M = m + 1 := ⟨M - 1, by omega⟩
  have hv := vInv_pos_of_numberField E
  unfold Formalism.HermitianLatticesTheory.massRatioRightSide rankFac
  simp only [Nat.add_sub_cancel]
  rw [volU_succ_eq_mul]
  set v := Formalism.HermitianLatticesTheory.vInv E
  set f := Formalism.HermitianLatticesTheory.fDeg E
  have h2 : 0 < 2 * v := by positivity
  have hfac : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  have hpi := Real.pi_pos.ne'
  have key : ((m.factorial : ℝ) * (v / Real.pi) ^ (m + 1)) *
      (2 * Real.pi ^ (m + 1) / (m.factorial : ℝ) * 2 ^ m) = (2 * v) ^ (m + 1) := by
    rw [div_pow, mul_pow]
    field_simp
    ring
  have hr : (2 * v) ^ ((f : ℝ) * (((m + 1 : ℕ) : ℝ) - 1 / 2)) =
      ((2 * v) ^ (m + 1)) ^ f / Real.sqrt ((2 * v) ^ f) := by
    rw [Real.sqrt_eq_rpow, ← pow_mul, ← Real.rpow_natCast, ← Real.rpow_natCast,
      ← Real.rpow_mul h2.le, ← Real.rpow_sub h2]
    congr 1
    push_cast
    ring
  rw [hr, ← key, mul_pow (volU m), mul_pow ((m.factorial : ℝ) * (v / Real.pi) ^ (m + 1))]
  ring

end GlobalTheory.FlagMeas
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassRatioRankFactorStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mass_ratio_rank_factor : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (M : ℕ), 1 ≤ M → Formalism.HermitianLatticesTheory.massRatioRightSide E M * volU M ^ Formalism.HermitianLatticesTheory.fDeg E = rankFac E M * volU (M - 1) ^ Formalism.HermitianLatticesTheory.fDeg E := by
  first | exact @GlobalTheory.FlagMeas.mass_ratio_mul_unitary_volume | exact GlobalTheory.FlagMeas.mass_ratio_mul_unitary_volume | (intros; apply GlobalTheory.FlagMeas.mass_ratio_mul_unitary_volume <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CellRep
open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S
open scoped ENNReal

namespace GlobalTheory.CellRep

lemma det_upUni {m : ℕ} {u : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ Formalism.FourierDecayAlt.C2.UTset m) : u.det = 1 := by
  have hb : u.BlockTriangular id := fun i j h => hu.1 i j h
  rw [Matrix.det_of_upperTriangular hb]
  simp [hu.2]

theorem cell_rep : ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : MatKR k r) (p : Point ℂ (r + 1)), inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → γ ∈ UH (Hpk k r) → IsInCell (ZhatO k r z z' γ) p → ∃ n ∈ Nset k r, ∃ n' ∈ Nset k r, ∃ g₀ ∈ UH (Hpk k r), γ = n * g₀ * n' ∧ ZhatO k r z z' g₀ = ptMat p := by
  intro k r z z' γ p hz hz' hT hT' hγ ⟨L, U, hL, hU, hZ⟩
  set d : Fin (r + 1) → ℂ := fun b => (-1 : ℂ) ^ (r - b.val) with hd
  have hdd : ∀ b, d b * d b = 1 := fun b => by
    simp only [hd]; rw [← mul_pow]; simp
  set D : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ := Matrix.diagonal d with hD
  have hDD : D * D = 1 := by
    rw [hD, Matrix.diagonal_mul_diagonal]; simp [hdd]
  have hO : ∀ g, ZhatO k r z z' g = Zhat k r z z' g * D := fun g => by
    ext a b
    rw [hD, Matrix.mul_diagonal, mul_comm]; rfl
  have hLU : Lᴴ ∈ Formalism.FourierDecayAlt.C2.UTset (r + 1) :=
    ⟨fun i j h => by simp [Matrix.conjTranspose_apply, (hL j i).1 h],
     fun i => by simp [Matrix.conjTranspose_apply, (hL i i).2 rfl]⟩
  have hUU : U ∈ Formalism.FourierDecayAlt.C2.UTset (r + 1) := ⟨fun i j h => (hU i j).1 h, fun i => (hU i i).2 rfl⟩
  have hU' : D * U * D ∈ Formalism.FourierDecayAlt.C2.UTset (r + 1) :=
    ⟨fun i j h => by simp [hD, Matrix.mul_diagonal, Matrix.diagonal_mul, (hU i j).1 h],
     fun i => by simp [hD, Matrix.mul_diagonal, Matrix.diagonal_mul, (hU i i).2 rfl, hdd]⟩
  obtain ⟨ha, -, hau⟩ := Formalism.FourierDecayAlt.P.c2_tau_mem k r z ⟨hz, hT⟩ _ hLU
  obtain ⟨hb, -, hbu⟩ := Formalism.FourierDecayAlt.P.c2_tau_mem k r z' ⟨hz', hT'⟩ _ hU'
  set a := Formalism.FourierDecayAlt.C2.tauM k r z Lᴴ
  set b := Formalism.FourierDecayAlt.C2.tauM k r z' (D * U * D)
  have hS : ∀ (w : Fin (2 * r + k + 1) → ℂ) (n : MatKR k r), n ∈ Nset k r → n ∈ Sset k r w :=
    fun w n hn => ⟨1, ⟨WeylGroupFacts.uh_one, fun _ => ⟨Matrix.one_mulVec _, Matrix.one_mulVec _⟩,
      Matrix.one_mulVec _⟩, n, hn, (Matrix.one_mul n).symm⟩
  have hai := WeylGroupFacts.mem_n_inv ha
  have hbi := WeylGroupFacts.mem_n_inv hb
  have hau' : IsUnit a.det := WeylGroupFacts.isUnit_of_uh ha.1
  have hbu' : IsUnit b.det := WeylGroupFacts.isUnit_of_uh hb.1
  have hg : a * γ * b⁻¹ ∈ UH (Hpk k r) := WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul ha.1 hγ) hbi.1
  have he : γ = a⁻¹ * (a * γ * b⁻¹) * b := by
    rw [Matrix.mul_assoc a, Matrix.nonsing_inv_mul_cancel_left _ _ hau',
      Matrix.nonsing_inv_mul_cancel_right _ _ hbu']
  refine ⟨a⁻¹, hai, b, hb, a * γ * b⁻¹, hg, he, ?_⟩
  have hE := Formalism.FourierDecayAlt.P.zhat_equivalence k r z z' ⟨hz, hT⟩ ⟨hz', hT'⟩ a (hS z a ha) b (hS z' b hb)
    (a * γ * b⁻¹)
  rw [← he, hau, hbu, Matrix.conjTranspose_conjTranspose] at hE
  have h1 : L * ZhatO k r z z' (a * γ * b⁻¹) * U = L * ptMat p * U := by
    rw [← hZ, hO, hO γ, hE]
    simp only [Matrix.mul_assoc, hDD, Matrix.mul_one]
  have hLu : IsUnit L.det := by
    have := det_upUni hLU
    rw [Matrix.det_conjTranspose] at this
    have h2 : L.det = 1 := by simpa using congrArg star this
    rw [h2]; exact isUnit_one
  have hUu : IsUnit U.det := by rw [det_upUni hUU]; exact isUnit_one
  have h2 := congrArg (fun X => L⁻¹ * (X * U⁻¹)) h1
  simpa only [Matrix.mul_nonsing_inv_cancel_right _ _ hUu, Matrix.nonsing_inv_mul_cancel_left _ _ hLu] using h2

end GlobalTheory.CellRep
end
