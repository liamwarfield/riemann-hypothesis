module

public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure
public import CompanionTheory.AutomorphicTheory.UnitriangularMeasure.AdeleCoordinateMeasure.GJGlobalModulus
public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.FiniteInfinitePlaceProduct

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.CubicPeriodConstant
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace cubicPeriodConstant

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem blkU_low {j : ℕ} (x : UnipotentBlockColumnIndex k j j → Ad E) (i c : Fin k) (h : c ≤ i) :
    (blkU x : GA E k).val i c = (1 : Matrix (Fin k) (Fin k) (Ad E)) i c := by
  have h' : (c : ℕ) ≤ i := h
  change (1 + posM Subtype.val x : Matrix (Fin k) (Fin k) (Ad E)) i c = _
  rw [Matrix.add_apply, posM, Matrix.sum_apply, Finset.sum_eq_zero, add_zero]
  intro t _
  have h1 := t.2
  rw [Matrix.single_apply_of_ne]
  rintro ⟨e1, e2⟩
  rw [← e1, ← e2] at h'
  omega

theorem blkU_unipotent_zero {j : ℕ} (x : UnipotentBlockColumnIndex k j j → Ad E) : UU 0 (blkU x : GA E k) := by
  refine ⟨fun i c h => ?_, fun i => ?_, fun i c h => absurd h (Nat.not_lt_zero _)⟩
  · rw [blkU_low x i c h.le, Matrix.one_apply_ne (ne_of_gt h)]
  · rw [blkU_low x i i le_rfl, Matrix.one_apply_eq]

theorem unipotent_zero_one : UU 0 (1 : GA E k) := by
  refine ⟨fun i c h => ?_, fun i => ?_, fun i c h => absurd h (Nat.not_lt_zero _)⟩
  · rw [Units.val_one, Matrix.one_apply_ne (ne_of_gt h)]
  · rw [Units.val_one, Matrix.one_apply_eq]

theorem unipotent_zero_mul {u v : GA E k} (hu : UU 0 u) (hv : UU 0 v) : UU 0 (u * v) := by
  refine ⟨fun i c h => ?_, fun i => ?_, fun i c h => absurd h (Nat.not_lt_zero _)⟩
  · rw [Units.val_mul, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rcases lt_or_ge l i with hl | hl
    · rw [hu.1 i l hl, zero_mul]
    · rw [hv.1 l c (lt_of_lt_of_le h hl), mul_zero]
  · rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hu.2.1, hv.2.1, one_mul]
    · intro l _ hl
      rcases lt_or_gt_of_ne hl with hl | hl
      · rw [hu.1 i l hl, zero_mul]
      · rw [hv.1 l i hl, mul_zero]
    · intro hi; exact absurd (Finset.mem_univ i) hi

theorem step (ψ : AddChar (Ad E) ℂ) (j : ℕ) (f f' : GA E k → ℂ) (g g' : GA E k) (c : ℂ)
    (h : ∀ u, UU 0 u → f (u * g) = c * f' (u * g')) :
    ∀ u, UU 0 u → colT ψ j f (u * g) = c * colT ψ j f' (u * g') := by
  intro u hu
  simp only [colT, coefF]
  rw [← avg_const_mul]
  congr 1
  funext x
  rw [← mul_assoc (blkU x) u g, ← mul_assoc (blkU x) u g', h _ (unipotent_zero_mul (blkU_unipotent_zero x) hu)]
  ring

theorem whit_gen (ψ : AddChar (Ad E) ℂ) (g g' : GA E k) : ∀ (m : ℕ) (f f' : GA E k → ℂ) (c : ℂ),
    (∀ u, UU 0 u → f (u * g) = c * f' (u * g')) →
      ∀ u, UU 0 u → whit ψ m f (u * g) = c * whit ψ m f' (u * g')
  | 0, _, _, _, h => h
  | m + 1, f, f', c, h => whit_gen ψ g g' m _ _ c (step ψ (m + 1) f f' g g' c h)

end cubicPeriodConstant

theorem crystalline_clause_of_admitted : P3 := by
  intro E _ _ _ k ψ m f f' g g' c h
  simpa only [one_mul] using cubicPeriodConstant.whit_gen ψ g g' m f f' c h 1 cubicPeriodConstant.unipotent_zero_one

end PositivityTheory.AdelicQuotientData

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.KuOf
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

theorem ku_of : jumpWindows.G5 → D0 → KU := by
  intro hG hD E _ _ _ k ψ hψ φ u hφ h1
  obtain ⟨-, -, -, hW⟩ := hG E k ψ hψ
  have hWc : Continuous (Wh ψ φ) := (hW φ hφ).1
  obtain ⟨hpos, hmul, hcont, -⟩ := hD E k
  have hD1 : Dt (1 : GA E k) = 1 := by
    have h := hmul 1 1
    rw [show (1 : GA E k) * 1 = 1 from mul_one 1] at h
    exact mul_left_cancel₀ (hpos 1).ne' (h.symm.trans (mul_one _).symm)
  set F : GA E k → ℂ := fun c => conj (Wh ψ φ c) * (Dt c : ℂ) ^ ((u : ℂ) * Complex.I) with hF
  have hDc : Continuous fun c : GA E k => (Dt c : ℂ) := Complex.continuous_ofReal.comp hcont
  have hFc : Continuous F := (Complex.continuous_conj.comp hWc).mul
    (hDc.cpow continuous_const fun c => Complex.ofReal_mem_slitPlane.2 (hpos c))
  have hF1 : F 1 = 1 := by simp [F, h1, hD1]
  refine ⟨{c | Dt c ∈ Set.Ioo (1 / 2 : ℝ) 2} ∩ {c | 0 < (F c).re}, ?_, ?_⟩
  · apply IsOpen.mem_nhds
    · exact (isOpen_Ioo.preimage hcont).inter (isOpen_lt continuous_const (Complex.continuous_re.comp hFc))
    · simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Ioo, hD1, hF1]
      norm_num
  · rintro c ⟨⟨ha, hb⟩, hc⟩
    exact ⟨ha.le, hb.le, hc⟩

end PositivityTheory.AdelicQuotientData

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.KsecOf
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

theorem ksec_of : jumpWindows.G2c → jumpWindows.G5 → CuspDecayShortRowColumn → K9 → KSec := by
  intro hG2c hG5 hG1d hK9 E _ _ _ k hk ψ hψ hcof π hπ
  obtain ⟨S₀, hS₀⟩ := hK9 E k hk ψ hψ hcof π hπ
  refine ⟨S₀, fun S hS => ⟨(hS₀ S hS).1, fun α hα => ?_⟩⟩
  obtain ⟨φ, hφ, h, x, hh, hx, hsat, -, hone⟩ := (hS₀ S hS).2 α hα
  have hval : ∀ g, Rt E k h x g = φ.1 (g * h) := fun g => by rw [Rt_apply, hx]
  have hgood : Good ψ (k - 1) (x : GA E k → ℂ) := by
    rw [hx]; exact good_of_isCuspForm E k ψ φ (π.cusp φ hφ)
  refine ⟨φ, hφ, h, Rt E k h x, hval, ?_⟩
  refine ⟨(hG5 E k ψ hψ).2.2.1 x h hgood, ?_, ?_, ?_, ?_, ?_, hone⟩
  · intro γ g
    rw [hval, hval, mul_assoc]
    exact (π.cusp φ hφ).1.left γ (g * h)
  · intro t g
    rw [hval, hval, mul_assoc]
    exact hπ φ hφ t (g * h)
  · intro w
    obtain ⟨Y, -, hYst, hYmem⟩ := hG2c E k w.1 (Finset.univ.val.map (α w)) (by simp)
    exact (hYmem _).1 (hYst h (hh w.1 w.2) x ((hYmem x).2 (hsat w)))
  · have e : (⇑(Rt E k h x) : GA E k → ℂ) = fun g => φ.1 (g * h) := funext hval
    rw [e]
    exact (hG1d E k hk π hπ φ hφ h).1
  · have := (hG1d E k hk π hπ φ hφ h).2
    simpa only [hval] using this

end PositivityTheory.AdelicQuotientData

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.VectorMeasureTranspose
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace VectorMeasureTranspose

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

def trM (g : GA E k) : GA E k :=
  ⟨(g.val)ᵀ, (g⁻¹.val)ᵀ, by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]⟩

theorem det_trM (g : GA E k) : GeneralLinearGroup.det (trM g) = GeneralLinearGroup.det g := by
  exact Units.ext (Matrix.det_transpose g.val)

theorem Dt_trM (g : GA E k) : Dt (trM g) = Dt g := by
  unfold Dt
  rw [det_trM]

theorem vecMeasure_eq : vecMeasure E (Fin k) = GroundTheory.Automorphic.GJMatrix.adeleMeasurePi E := rfl

theorem vecMul_eq (g : GA E k) (F : (Fin k → Ad E) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, F (x ᵥ* g.val) ∂vecMeasure E (Fin k) = ENNReal.ofReal (Dt g)⁻¹ * ∫⁻ x, F x ∂vecMeasure E (Fin k) := by
  have hm : Measurable fun x : Fin k → Ad E => x ᵥ* g.val := GroundTheory.Automorphic.GJGlobal.Modulus.measurable_vecMul' g
  have e1 : ∫⁻ x, F x ∂((GroundTheory.Automorphic.GJMatrix.adeleMeasurePi E).map fun x : Fin k → Ad E => x ᵥ* g.val) =
      ∫⁻ x, F (x ᵥ* g.val) ∂GroundTheory.Automorphic.GJMatrix.adeleMeasurePi E := lintegral_map hF hm
  have h := GroundTheory.Automorphic.GJGlobal.Modulus.map_vecMul_adeleMeasurePi g
  unfold Dt
  rw [vecMeasure_eq, ← e1, h, lintegral_smul_measure]
  try rw [smul_eq_mul]

theorem mulVec_eq (g : GA E k) (F : (Fin k → Ad E) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, F (g.val *ᵥ x) ∂vecMeasure E (Fin k) = ENNReal.ofReal (Dt g)⁻¹ * ∫⁻ x, F x ∂vecMeasure E (Fin k) := by
  have e : ∀ x : Fin k → Ad E, F (g.val *ᵥ x) = F (x ᵥ* (trM g).val) := fun x => by
    show F (g.val *ᵥ x) = F (x ᵥ* (g.val)ᵀ)
    rw [Matrix.vecMul_transpose]
  refine (lintegral_congr e).trans ?_
  rw [vecMul_eq (trM g) F hF, Dt_trM]

end VectorMeasureTranspose

theorem linear_change_variables_of : D0 → AdelicLinearChange := by
  intro _ E _ _ _ k g F hF
  exact ⟨VectorMeasureTranspose.mulVec_eq g F hF, VectorMeasureTranspose.vecMul_eq g F hF⟩

end PositivityTheory.AdelicQuotientData

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.TableDegreeOneUnipotent
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace tableDegreeOneUnipotent

theorem mul_le_sq_add (a b : ℝ≥0∞) : a * b ≤ a ^ 2 + b ^ 2 := by
  rcases le_total a b with h | h
  · calc a * b ≤ b * b := by gcongr
      _ = b ^ 2 := (sq b).symm
      _ ≤ _ := le_add_self
  · calc a * b ≤ a * a := by gcongr
      _ = a ^ 2 := (sq a).symm
      _ ≤ _ := le_self_add

theorem integ {X : Type} [MeasurableSpace X] {ν : Measure X} {f φ : X → ℂ}
    (hf : AEStronglyMeasurable f ν) (hφ : AEStronglyMeasurable φ ν)
    (h1 : ∫⁻ g, ‖f g‖ₑ ^ 2 ∂ν < ∞) (h2 : ∫⁻ g, ‖φ g‖ₑ ^ 2 ∂ν < ∞) :
    Integrable (fun g => f g * conj (φ g)) ν := by
  refine ⟨hf.mul (Complex.continuous_conj.comp_aestronglyMeasurable hφ), ?_⟩
  show ∫⁻ g, ‖f g * conj (φ g)‖ₑ ∂ν < ∞
  calc ∫⁻ g, ‖f g * conj (φ g)‖ₑ ∂ν ≤ ∫⁻ g, (‖f g‖ₑ ^ 2 + ‖φ g‖ₑ ^ 2) ∂ν := by
        refine lintegral_mono fun g => ?_
        have hc : ‖conj (φ g)‖ₑ = ‖φ g‖ₑ := by simp [enorm_eq_nnnorm]
        rw [enorm_mul, hc]
        exact mul_le_sq_add _ _
    _ = ∫⁻ g, ‖f g‖ₑ ^ 2 ∂ν + ∫⁻ g, ‖φ g‖ₑ ^ 2 ∂ν := lintegral_add_left' (hf.enorm.pow_const 2) _
    _ < ∞ := ENNReal.add_lt_top.2 ⟨h1, h2⟩

theorem pre_of_good {E : Type} [Field E] [NumberField E] {k : ℕ} {ψ : AddChar (Ad E) ℂ} {m : ℕ}
    {f : GA E k → ℂ} (h : Good ψ m f) : Pre ψ m f :=
  ⟨h.cont, h.left, h.law⟩

theorem main (hU1 : U1) (hP1 : P1) (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (k : ℕ)
    (μ : Measure (GA E k)) [μ.IsHaarMeasure] (ψ : AddChar (Ad E) ℂ) (hψ : StdPsi ψ) :
    ∀ m, m < k → ∀ β, IsWt (nuP E k m) β → ∃ β', IsWt (nuP E k 0) β' ∧
      ∀ f φ, Pre ψ m f → Good ψ m φ → ∫⁻ g, ‖f g‖ₑ ^ 2 ∂μ.withDensity β < ∞ →
        ∫⁻ g, ‖φ g‖ₑ ^ 2 ∂μ.withDensity β < ∞ →
        Integrable (fun g => whit ψ m f g * conj (whit ψ m φ g)) (μ.withDensity β') ∧
        ∫ g, f g * conj (φ g) ∂μ.withDensity β = ∫ g, whit ψ m f g * conj (whit ψ m φ g) ∂μ.withDensity β' := by
  intro m
  induction m with
  | zero =>
    intro _ β hβ
    refine ⟨β, hβ, fun f φ hf hφ h1 h2 => ⟨?_, rfl⟩⟩
    exact integ hf.cont.aestronglyMeasurable (pre_of_good hφ).cont.aestronglyMeasurable h1 h2
  | succ m ih =>
    intro hm β hβ
    obtain ⟨β1, hβ1, hL2, hip⟩ := hU1 E k μ ψ hψ (m + 1) (by omega) hm β hβ
    obtain ⟨β', hβ', h⟩ := ih (by omega) β1 hβ1
    refine ⟨β', hβ', fun f φ hf hφ h1 h2 => ?_⟩
    have hf' : Pre ψ m (colT ψ (m + 1) f) := (hP1 E k ψ hψ (m + 1) (by omega) hm f hf).1
    have hφ' : Good ψ m (colT ψ (m + 1) φ) := by
      refine { cont := ?_, left := ?_, law := ?_, van := ?_ }
      · exact _root_.GlobalTheory.T.continuous_unipotentColumnWhittakerTransform E k ψ hψ m φ hφ
      · exact _root_.GlobalTheory.T.unipotentColumnWhittakerTransform_mirabolic_invariant E k ψ hψ m φ hm hφ
      · intro j hj y g
        rcases Nat.lt_or_ge (m + 1) j with h | h
        · exact _root_.GlobalTheory.T.columnWhittakerTransform_keeps_later_law E k ψ m φ hφ j h y g
        · obtain rfl : j = m + 1 := by omega
          exact _root_.GlobalTheory.T.unipotentColumnWhittakerTransform_column_law E k ψ hψ m φ hφ y g
      · exact _root_.GlobalTheory.T.quotientAverage_unipotentBlock_columnTransform_eq_zero E k ψ hψ m φ hm hφ
    obtain ⟨hi, he⟩ := h _ _ hf' hφ' ((hL2 f hf).trans_lt h1) ((hL2 φ (pre_of_good hφ)).trans_lt h2)
    exact ⟨hi, (hip f φ hf hφ h1 h2).trans he⟩

end tableDegreeOneUnipotent

theorem unitaryGroupGeometricSide_of_quotient_identities : U1 → P1 → U2 := by
  intro hU1 hP1 E _ _ _ k μ _ ψ hψ
  exact tableDegreeOneUnipotent.main hU1 hP1 E k μ ψ hψ

end PositivityTheory.AdelicQuotientData

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.CosetIntegralMeasure
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace CosetIntegralMeasure

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem meas_mul (g : GA E k) : Measurable (fun h : GA E k => g * h) := by
  exact measurable_const_mul g

theorem lint_nuG (Γ : Set (GL (Fin k) E)) (d : ℕ) (F : GA E k → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ h, F h ∂nuG Γ d = ∑' γ : Γ, ∫⁻ h, F (ratGL E k γ * h) ∂nuD E k d := by
  rw [nuG, lintegral_sum_measure]
  refine tsum_congr fun γ => ?_
  exact lintegral_map hF (meas_mul _)

end CosetIntegralMeasure

open CosetIntegralMeasure in
theorem coset_integration_of : N0 → N1 → N3 → CosetIntegralParabolic := by
  intro h0 _ _ E _ _ _ k j hj1 hjk F hF
  obtain ⟨hgam, huniq, hmul, hinv, -, hmir, -⟩ := h0 E k j hj1 hjk
  have hd : k - (j - 1 + 1) = k - j := by omega
  let f : RowT E k j × ({γ : GL (Fin k) E | IsMir (j - 1) γ} : Set (GL (Fin k) E)) →
      ({γ : GL (Fin k) E | GlobalTheory j γ} : Set (GL (Fin k) E)) := fun x =>
    ⟨(gam x.1)⁻¹ * (x.2 : GL (Fin k) E), hmul (gam x.1)⁻¹ (x.2 : GL (Fin k) E) (hinv (gam x.1) (hgam x.1).1)
      (hmir (x.2 : GL (Fin k) E) x.2.2).2⟩
  have hinj : Function.Injective f := by
    rintro ⟨ξ, p⟩ ⟨ξ', p'⟩ h
    have hv : (gam ξ)⁻¹ * (p : GL (Fin k) E) = (gam ξ')⁻¹ * (p' : GL (Fin k) E) := congrArg Subtype.val h
    have hB : GlobalTheory j ((gam ξ)⁻¹ * (p : GL (Fin k) E))⁻¹ := hinv ((gam ξ)⁻¹ * (p : GL (Fin k) E)) (f (ξ, p)).2
    obtain ⟨q, -, huq⟩ := huniq _ hB
    have e1 : (ξ, (p : GL (Fin k) E)⁻¹) = q :=
      huq (ξ, (p : GL (Fin k) E)⁻¹) ⟨(hmir (p : GL (Fin k) E) p.2).1, by simp only [_root_.mul_inv_rev, inv_inv]⟩
    have e2 : (ξ', (p' : GL (Fin k) E)⁻¹) = q :=
      huq (ξ', (p' : GL (Fin k) E)⁻¹) ⟨(hmir (p' : GL (Fin k) E) p'.2).1, by simp only [hv, _root_.mul_inv_rev, inv_inv]⟩
    have h3 := Prod.mk.inj (e1.trans e2.symm)
    exact Prod.ext h3.1 (Subtype.ext (inv_injective h3.2))
  have hsurj : Function.Surjective f := by
    rintro ⟨γ, hγ⟩
    obtain ⟨⟨ξ, q⟩, ⟨hq, heq⟩, -⟩ := huniq γ⁻¹ (hinv γ hγ)
    have hq' : IsMir (j - 1) q := hq
    have heq' : γ⁻¹ = q * gam ξ := heq
    refine ⟨(ξ, ⟨q⁻¹, (hmir q hq').1⟩), Subtype.ext ?_⟩
    show (gam ξ)⁻¹ * q⁻¹ = γ
    rw [← _root_.mul_inv_rev, ← heq', inv_inv]
  let e := Equiv.ofBijective f ⟨hinj, hsurj⟩
  have hR : ∀ ξ : RowT E k j, ∫⁻ h, F ((ratGL E k (gam ξ))⁻¹ * h) ∂nuP E k (j - 1) =
      ∑' p : ({γ : GL (Fin k) E | IsMir (j - 1) γ} : Set (GL (Fin k) E)),
        ∫⁻ h, F (ratGL E k ((gam ξ)⁻¹ * (p : GL (Fin k) E)) * h) ∂nuD E k (k - j) := by
    intro ξ
    have e0 := lint_nuG {γ : GL (Fin k) E | IsMir (j - 1) γ} (k - (j - 1 + 1))
      (fun h => F ((ratGL E k (gam ξ))⁻¹ * h)) (hF.comp (meas_mul _))
    refine e0.trans ?_
    rw [hd]
    refine tsum_congr fun p => ?_
    simp only [map_mul, map_inv, mul_assoc]
  calc ∫⁻ h, F h ∂nuB E k j
      = ∑' γ : ({γ : GL (Fin k) E | GlobalTheory j γ} : Set (GL (Fin k) E)),
          ∫⁻ h, F (ratGL E k γ * h) ∂nuD E k (k - j) := lint_nuG {γ : GL (Fin k) E | GlobalTheory j γ} (k - j) F hF
    _ = ∑' x : RowT E k j × ({γ : GL (Fin k) E | IsMir (j - 1) γ} : Set (GL (Fin k) E)),
          ∫⁻ h, F (ratGL E k ((gam x.1)⁻¹ * (x.2 : GL (Fin k) E)) * h) ∂nuD E k (k - j) :=
        (e.tsum_eq (fun γ : ({γ : GL (Fin k) E | GlobalTheory j γ} : Set (GL (Fin k) E)) =>
          ∫⁻ h, F (ratGL E k γ * h) ∂nuD E k (k - j))).symm
    _ = ∑' ξ : RowT E k j, ∑' p : ({γ : GL (Fin k) E | IsMir (j - 1) γ} : Set (GL (Fin k) E)),
          ∫⁻ h, F (ratGL E k ((gam ξ)⁻¹ * (p : GL (Fin k) E)) * h) ∂nuD E k (k - j) := by
        exact ENNReal.tsum_prod (f := fun (ξ : RowT E k j) (p : ({γ : GL (Fin k) E | IsMir (j - 1) γ} : Set (GL (Fin k) E))) =>
            ∫⁻ h, F (ratGL E k ((gam ξ)⁻¹ * (p : GL (Fin k) E)) * h) ∂nuD E k (k - j))
    _ = ∑' ξ : RowT E k j, ∫⁻ h, F ((ratGL E k (gam ξ))⁻¹ * h) ∂nuP E k (j - 1) :=
        tsum_congr fun ξ => (hR ξ).symm

end PositivityTheory.AdelicQuotientData

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.LocalUnramifiedOf
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

section PK7

open GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.LFun Formalism.UG Formalism.L2.Host

theorem local_unramified_of : JacquetShalikaLocal.L7 → JacquetShalikaLocal.lift_levelP_alt₂ → jumpWindows.G0 → jumpWindows.G5 → K7 := by
  intro hL7 hL12 hG0 hG5 E _ _ _ a ψ hψ w hc
  refine ⟨WeilJacquetShalikaLaw.psiW ψ w, WeilJacquetShalikaLaw.psiOK hψ hc, fun y => rfl, ?_⟩
  intro z φ hφ hsat h hh u
  have hcomm := (hG0 E a).2.2.2.2.2.2.2.1 w h hh
  obtain ⟨hΛ, hrt, hgood, hreg⟩ := hG5 E a ψ hψ
  rcases hsat with rfl | hsat
  · have h0 : ∀ g, Wh ψ (0 : XB E a) g = 0 := fun g => by
      obtain ⟨Λ, hΛ'⟩ := hΛ g
      rw [← hΛ' 0 hφ, map_zero]
    rw [h0, h0, zero_mul]
  let v : GL (Fin a) (w.adicCompletion E) → ℂ := fun x => Wh ψ φ (h * fl a w x)
  have hfix : ∀ k ∈ KGL w (n := a), Rt E a (fl a w k) φ = φ := fun k hk => GlobalTheory.LGrp.mem_fixed.1 hsat.2.1 k hk
  have hv : v ∈ WeilJacquetShalikaLaw.WS (WeilJacquetShalikaLaw.psiW ψ w) a := by
    intro n hn x
    change Wh ψ φ (h * fl a w (n * x)) = _ * Wh ψ φ (h * fl a w x)
    rw [map_mul, ← mul_assoc, hcomm n, mul_assoc]
    exact WeilJacquetShalikaLaw.law (hreg φ hφ).2.2 w n hn _
  let vs : WeilJacquetShalikaLaw.WS (WeilJacquetShalikaLaw.psiW ψ w) a := ⟨v, hv⟩
  have hv1 : (vs : GL (Fin a) (w.adicCompletion E) → ℂ) 1 = Wh ψ φ h := by
    change Wh ψ φ (h * fl a w 1) = _
    rw [map_one, mul_one]
  by_cases h0 : vs = 0
  · have e : ∀ x, (vs : GL (Fin a) (w.adicCompletion E) → ℂ) x = 0 := fun x =>
      congrFun (congrArg Subtype.val h0) x
    have e1 : Wh ψ φ (h * fl a w u) = 0 := e u
    rw [e1, ← hv1, e 1, zero_mul]
  have hK := Final.GLintComm E w a
  have hsv : IsSatVecGL w (WeilJacquetShalikaLaw.rhoW (WeilJacquetShalikaLaw.psiW ψ w) a) vs (Finset.univ.val.map z) := by
    refine ⟨h0, GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_, by simp, fun ϖ hϖ j hj => ?_⟩
    · apply Subtype.ext
      funext x
      change Wh ψ φ (h * fl a w (x * k)) = Wh ψ φ (h * fl a w x)
      rw [map_mul, ← mul_assoc, ← hrt, hfix k hk]
    · apply Subtype.ext
      have e := map_heckeVec (ρ := WeilJacquetShalikaLaw.rhoW (WeilJacquetShalikaLaw.psiW ψ w) a)
        (ρ' := GlobalTheory.PRep.rightReg ℂ (GL (Fin a) (w.adicCompletion E)) ℂ) hK (Tj_mem_hecke hϖ j) (WeilJacquetShalikaLaw.WS (WeilJacquetShalikaLaw.psiW ψ w) a).subtype (fun _ _ => rfl) vs
      rw [Submodule.subtype_apply, Submodule.subtype_apply] at e
      rw [e, Submodule.coe_smul]
      funext x
      obtain ⟨Λ, hΛ'⟩ := hΛ (h * fl a w x)
      have hfin := finite_heckeVec hK (Tj_mem_hecke hϖ j) (GlobalTheory.PRep.rightReg ℂ (GL (Fin a) (w.adicCompletion E)) ℂ) v
      have hfin2 := finite_heckeVec hK (Tj_mem_hecke hϖ j) (repW a w) φ
      have e1 := (LinearMap.proj (R := ℂ) (φ := fun _ : GL (Fin a) (w.adicCompletion E) => ℂ) x).toAddMonoidHom.map_finsum hfin
      have e2 := (Λ : XB E a →L[ℂ] ℂ).toLinearMap.toAddMonoidHom.map_finsum hfin2
      have e3 := hsat.2.2.2 ϖ hϖ j hj
      have key : ∀ c : GL (Fin a) (w.adicCompletion E) ⧸ KGL w (n := a),
          (Tj ℂ a (Ov E w) ϖ j c.out • GlobalTheory.PRep.rightReg ℂ (GL (Fin a) (w.adicCompletion E)) ℂ c.out v) x =
            Λ (Tj ℂ a (Ov E w) ϖ j c.out • repW a w c.out φ) := by
        intro c
        rw [map_smul, hΛ' (repW a w c.out φ) (hgood φ (fl a w c.out) hφ)]
        change _ * v (x * c.out) = _ • Wh ψ (Rt E a (fl a w c.out) φ) (h * fl a w x)
        rw [hrt, smul_eq_mul]
        change _ * Wh ψ φ (h * fl a w (x * c.out)) = _
        rw [map_mul, mul_assoc]
      have LHS : heckeVec (GlobalTheory.PRep.rightReg ℂ (GL (Fin a) (w.adicCompletion E)) ℂ) (KGL w (n := a))
          (Tj ℂ a (Ov E w) ϖ j) v x = Λ (heckeVec (repW a w) (KGL w (n := a)) (Tj ℂ a (Ov E w) ϖ j) φ) := by
        rw [heckeVec, heckeVec]
        exact e1.trans ((finsum_congr key).trans e2.symm)
      refine LHS.trans ?_
      rw [e3, map_smul, hΛ' φ hφ]
      rfl
  have heig := (hL12 E w).2 a _ (WeilJacquetShalikaLaw.rhoW (WeilJacquetShalikaLaw.psiW ψ w) a) vs z hsv
  have := hL7 (w.adicCompletion E) (WeilJacquetShalikaLaw.psiW ψ w) (WeilJacquetShalikaLaw.psiOK hψ hc) a _ (WeilJacquetShalikaLaw.rhoW (WeilJacquetShalikaLaw.psiW ψ w) a) vs z heig
    (WeilJacquetShalikaLaw.ev _ a) (WeilJacquetShalikaLaw.whitW w _) u
  rw [WeilJacquetShalikaLaw.ev_apply, WeilJacquetShalikaLaw.ev_apply, WeilJacquetShalikaLaw.rhoW_apply, one_mul, hv1] at this
  exact this

end PK7

end PositivityTheory.AdelicQuotientData

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.RhoSigmaFinite
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace RhoSigmaFinite

set_option synthInstance.maxHeartbeats 400000

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {k : ℕ}

omit [_root_.NumberField.IsTotallyComplex E] in
theorem uu_eq_one {u : GA E k} {j : ℕ} (hj : k ≤ j) (hu : UU j u) : u = 1 :=
  Units.ext <| Matrix.ext fun i c => by rw [hu.2.2 i c (by omega), Units.val_one]


variable (E k) in
def rho : Measure (GA E k) := Measure.sum fun ξ : RowT E k k => Measure.dirac (ratGL E k (gam ξ))

omit [_root_.NumberField.IsTotallyComplex E] in
theorem rho_sFinite [Countable (RowT E k k)] : SFinite (rho E k) := by
  rw [rho]; infer_instance

omit [_root_.NumberField.IsTotallyComplex E] in
theorem lint_rho (F : GA E k → ℝ≥0∞) : ∫⁻ r, F r ∂rho E k = ∑' ξ : RowT E k k, F (ratGL E k (gam ξ)) := by
  rw [rho, lintegral_sum_measure]
  simp only [lintegral_dirac]

omit [_root_.NumberField.IsTotallyComplex E] in
theorem int_rho (Φ : GA E k → ℂ) (hΦ : Measurable Φ) (g : GA E k) :
    ∫ r, Φ (r * g) ∂rho E k = sumF Φ g := by
  by_cases hi : Integrable (fun r => Φ (r * g)) (rho E k)
  · rw [rho, integral_sum_measure hi, sumF]
    simp only [integral_dirac]
  · rw [integral_undef hi, sumF, tsum_eq_zero_of_not_summable]
    intro hs
    apply hi
    refine ⟨(hΦ.comp (measurable_mul_const g)).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral, lint_rho]
    have h1 : Summable fun ξ : RowT E k k => ‖Φ (ratGL E k (gam ξ) * g)‖₊ :=
      NNReal.summable_coe.mp (by simpa using hs.norm)
    have h2 := ENNReal.tsum_coe_ne_top_iff_summable.mpr h1
    simpa [enorm_eq_nnnorm] using h2.lt_top

end RhoSigmaFinite

open RhoSigmaFinite in
set_option synthInstance.maxHeartbeats 400000 in
theorem unipotent_integral_of : Q1 → Q2 → N0 → N3 → CosetIntegralParabolic → U0 := by
  intro hQ1 hQ2 hN0 hN3 hN4a E _ _ _ k μ _ hk β hβ
  have : Countable (RowT E k k) := (hN0 E k k hk le_rfl).2.2.2.2.2.2.1
  have : SFinite (rho E k) := rho_sFinite
  obtain ⟨hsf, hinv, hae⟩ := (hN3 E k).1 (k - 1) (by omega)
  have key : ∀ g, ∑' ξ : RowT E k k, ∫⁻ h, β ((ratGL E k (gam ξ))⁻¹ * h * g) ∂nuP E k (k - 1) = 1 := by
    intro g
    rw [← hN4a E k k hk le_rfl (fun h => β (h * g)) (hβ.1.comp (measurable_mul_const g))]
    exact hβ.2 g
  set β' : GA E k → ℝ≥0∞ := fun g => ∑' ξ : RowT E k k, β ((ratGL E k (gam ξ))⁻¹ * g) with hβ'
  have hwt : IsWt (nuP E k (k - 1)) β' := by
    refine ⟨Measurable.tsum fun ξ => hβ.1.comp (measurable_const_mul _), fun g => ?_⟩
    simp only [hβ']
    rw [lintegral_tsum (f := fun ξ h => β ((ratGL E k (gam ξ))⁻¹ * (h * g)))
      fun ξ => (hβ.1.comp ((measurable_const_mul _).comp (measurable_mul_const g))).aemeasurable]
    simpa only [mul_assoc] using key g
  have hH : ∀ᵐ h ∂nuP E k (k - 1), h ∈ {x : GA E k | ∃ γ, IsMir (k - 1) γ ∧ ratGL E k γ = x} := by
    filter_upwards [hae] with h ⟨γ, u, hγ, hu, hh⟩
    rw [hh, uu_eq_one (by omega) hu, mul_one]
    exact ⟨γ, hγ, rfl⟩
  have hone : ∀ g, ∫⁻ r, ∫⁻ h, β (r⁻¹ * h * g) ∂nuP E k (k - 1) ∂rho E k = 1 := fun g => by
    rw [lint_rho]; exact key g
  refine ⟨β', hwt, fun Φ hΦ hΦi => ?_, fun Φ hΦ hΦi hint => ?_⟩
  · have := hQ1 (GA E k) μ (nuP E k (k - 1)) (rho E k) _ β' β hinv hH hwt hβ.1 hone Φ hΦ
      (by rintro _ ⟨γ, hγ, rfl⟩ g; exact hΦi γ hγ g)
    rw [this]
    simp only [lint_rho]
  · have := (hQ2 (GA E k) μ (nuP E k (k - 1)) (rho E k) _ β' β hinv hH hwt hβ.1 hone Φ hΦ
      (by rintro _ ⟨γ, hγ, rfl⟩ g; exact hΦi γ hγ g) hint).2
    rw [this]
    simp only [int_rho Φ hΦ]

end PositivityTheory.AdelicQuotientData

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.DminNonneg
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace PKIR

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem dt_pos (g : GA E k) : 0 < Dt g := (GroundTheory.Global.IdeleGroup.ideleModule E (GeneralLinearGroup.det g)).2

theorem ht_nonneg (g : GA E k) (ξ : Fin k → E) : 0 ≤ ht g ξ :=
  div_nonneg (height_nonneg _ _) (Real.rpow_nonneg (dt_pos g).le _)

theorem dmin_nonneg (g : GA E k) : 0 ≤ dmin g := by
  unfold dmin
  exact Real.iInf_nonneg fun ξ => ht_nonneg g ξ.1

theorem wt_nonneg (M : ℕ) (g : GA E k) : 0 ≤ wt M g := by
  unfold wt
  exact pow_nonneg (le_min zero_le_one (dmin_nonneg g)) M

end PKIR

theorem kir_of : jumpWindows.S2 → jumpWindows.G0 → jumpWindows.G2a → jumpWindows.G2c → jumpWindows.G5 → jumpWindows.G5b → K2 → K3 → K4 → K9 → KIR := by
  intro hS2 hG0 hG2a hG2c _hG5 hG5b hK2 hK3 hK4 hK9 E _ _ _ k hk ψ hψ hcof π hπ
  obtain ⟨S₀, hS₀⟩ := hK9 E k hk ψ hψ hcof π hπ
  refine ⟨S₀, fun S hS α hα M j hj U hU Y hYc hYi hYπ => ?_⟩
  obtain ⟨_hcond, h9⟩ := hS₀ S hS
  obtain ⟨φ, hφ, h, x, hhS, hx, hsat, hlev, hwh⟩ := h9 α hα
  obtain ⟨ρ, J, hW, hsm⟩ := hK2 E k hk M
  obtain ⟨x₀, hx₀, hsm₀⟩ := hK3 E k hk M ρ J hW π hπ φ hφ
  have hJx₀ : J x₀ = x := DFunLike.coe_injective (hx₀.trans hx.symm)

  obtain ⟨_, _, _, hSg, hST, _⟩ := hS2 _ k (XB E k) (ρ.comp (infGL E k)) hW.poly
  obtain ⟨g1, g2, _, _, _, _, g7, _⟩ := hG0 E k
  have hsm1 : SmV (ρ.comp (infGL E k)) (ρ h x₀) := by
    set y := cInf h
    set hf := (infGL E k y)⁻¹ * h
    have hcf : cInf hf = 1 := by simp only [hf, map_mul, map_inv, g1, y, inv_mul_cancel]
    have hc : ∀ (g : GL (Fin k) (Cinf E)) z, ρ hf ((ρ.comp (infGL E k)) g z) = (ρ.comp (infGL E k)) g (ρ hf z) := by
      intro g z
      simp only [MonoidHom.comp_apply]
      rw [← ContinuousLinearMap.mul_apply, ← map_mul, g7 hf hcf g, map_mul, ContinuousLinearMap.mul_apply]
    have := hSg y _ (hST (ρ hf) hc x₀ hsm₀)
    simpa only [MonoidHom.comp_apply, ← ContinuousLinearMap.mul_apply, ← map_mul, hf, mul_inv_cancel_left] using this

  obtain ⟨Yg, hYgc, hYgi, hYgm⟩ := hG2a E k ψ hψ
  have hw := fun w : Off E S => hG2c E k w.1 (Finset.univ.val.map (α w)) (by simp)
  choose Yw hYwc hYwi hYwm using hw
  set Y' : Submodule ℂ (XB E k) := Y ⊓ Yg ⊓ ⨅ w, Yw w with hY'
  have hmem : ∀ z, z ∈ Y' ↔ (z ∈ Y ∧ z ∈ Yg) ∧ ∀ w, z ∈ Yw w := fun z => by
    simp only [Y', Submodule.mem_inf, Submodule.mem_iInf]
  have hYOK : YOK ψ S Y' := by
    refine ⟨?_, ?_, ?_⟩
    · rw [Submodule.coe_inf, Submodule.coe_inf, Submodule.coe_iInf]
      exact (hYc.inter hYgc).inter (isClosed_iInter hYwc)
    · intro g hg z hz
      rw [hmem] at hz ⊢
      exact ⟨⟨hYi g z hz.1.1, hYgi g z hz.1.2⟩, fun w => hYwi w g (hg w.1 w.2) z (hz.2 w)⟩
    · intro z hz
      exact ((hYgm z).1 ((hmem z).1 hz).1.2).1
  have hcusp := π.cusp φ hφ
  have hxY' : Rt E k h x ∈ Y' := by
    have hxg : x ∈ Yg := by
      refine (hYgm x).2 ⟨?_, fun γ g => ?_⟩
      · rw [hx]; exact GlobalTheory.T.isMirabolicWhittakerStage_of_isCuspForm E k ψ φ hcusp
      · rw [congrFun hx, congrFun hx]; exact hcusp.1.left γ g
    rw [hmem]
    exact ⟨⟨hYi h x (hYπ x ⟨φ, hφ, hx⟩), hYgi h x hxg⟩,
      fun w => hYwi w h (hhS w.1 w.2) x ((hYwm w x).2 (hsat w))⟩
  have hJ1 : J (ρ h x₀) = Rt E k h x := by rw [hW.inter, hJx₀]
  obtain ⟨x', C, hCU, hx'Y, hsm', hlev', hBlk, hBump⟩ := hK4 E k (wt M) ρ J hW ψ hψ S Y' hYOK j hj U hU (ρ h x₀)
    (hJ1 ▸ hxY') hsm1 (hJ1 ▸ (hG5b E k S).2.1 h x hlev) (hJ1 ▸ hwh)
  obtain ⟨⟨hx'1, hx'2⟩, hx'3⟩ := (hmem _).1 hx'Y
  obtain ⟨hgood, hinv⟩ := (hYgm _).1 hx'2
  refine ⟨J x', hx'1, ⟨hgood, hinv, fun w => (hYwm w _).1 (hx'3 w), hsm x' hsm', hlev', ?_, ⟨C, hCU, hBlk, hBump⟩⟩⟩
  refine ⟨‖x'‖, fun g => ?_⟩
  have hw0 := PKIR.wt_nonneg M g
  rw [hW.mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hw0, mul_comm ‖x'‖]
  exact mul_le_mul_of_nonneg_left (x'.norm_coe_le_norm g) hw0

end PositivityTheory.AdelicQuotientData

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.QuadraticTransferFirst
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace QuadraticTransferFirst

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [BorelSpace G] in
theorem swap3 {μ ν ρ : Measure G} [SFinite μ] [SFinite ν] [SFinite ρ] (K : G → G → G → ℝ≥0∞)
    (hK : Measurable fun p : G × G × G => K p.1 p.2.1 p.2.2) :
    ∫⁻ g, ∫⁻ r, ∫⁻ h, K r h g ∂ν ∂ρ ∂μ = ∫⁻ r, ∫⁻ h, ∫⁻ g, K r h g ∂μ ∂ν ∂ρ := by
  have hF : Measurable (Function.uncurry fun g r => ∫⁻ h, K r h g ∂ν) := by
    have : Measurable fun q : (G × G) × G => K q.1.2 q.2 q.1.1 :=
      hK.comp ((measurable_snd.comp measurable_fst).prodMk
        (measurable_snd.prodMk (measurable_fst.comp measurable_fst)))
    exact this.lintegral_prod_right'
  rw [lintegral_lintegral_swap hF.aemeasurable]
  refine lintegral_congr fun r => ?_
  have hK' : Measurable (Function.uncurry fun g h => K r h g) :=
    hK.comp (measurable_const.prodMk (measurable_snd.prodMk measurable_fst))
  exact lintegral_lintegral_swap hK'.aemeasurable

theorem main (μ : Measure G) [μ.IsHaarMeasure] (ν ρ : Measure G) [SFinite ν] [SFinite ρ] (H : Set G)
    (β β₁ : G → ℝ≥0∞) (hinv : Measure.map (fun h => h⁻¹) ν = ν) (hH : ∀ᵐ h ∂ν, h ∈ H) (hβ : IsWt ν β)
    (hβ₁ : Measurable β₁) (h1 : ∀ g, ∫⁻ r, ∫⁻ h, β₁ (r⁻¹ * h * g) ∂ν ∂ρ = 1) (Φ : G → ℝ≥0∞)
    (hΦ : Measurable Φ) (hΦH : ∀ h ∈ H, ∀ g, Φ (h * g) = Φ g) :
    ∫⁻ g, Φ g ∂μ.withDensity β = ∫⁻ g, ∫⁻ r, Φ (r * g) ∂ρ ∂μ.withDensity β₁ := by
  have hβm : Measurable β := hβ.1
  have hH' : ∀ᵐ h ∂ν, h⁻¹ ∈ H := by
    have hH2 := hH
    rw [← hinv] at hH2
    exact ae_of_ae_map measurable_inv.aemeasurable hH2
  have hinvβ : ∀ g, ∫⁻ h, β (h⁻¹ * g) ∂ν = 1 := by
    intro g
    have hm : Measurable fun h : G => β (h * g) := by fun_prop
    rw [show (∫⁻ h, β (h⁻¹ * g) ∂ν) = ∫⁻ h, β (h * g) ∂(Measure.map (fun h => h⁻¹) ν) from
      (lintegral_map hm measurable_inv).symm, hinv]
    exact hβ.2 g
  calc ∫⁻ g, Φ g ∂μ.withDensity β
      = ∫⁻ g, β g * Φ g ∂μ := lintegral_withDensity_eq_lintegral_mul _ hβm hΦ
    _ = ∫⁻ g, ∫⁻ r, ∫⁻ h, β g * Φ g * β₁ (r⁻¹ * h * g) ∂ν ∂ρ ∂μ := by
        refine lintegral_congr fun g => ?_
        have hm1 : ∀ r, Measurable fun h => β₁ (r⁻¹ * h * g) := fun r => by fun_prop
        have hm2 : Measurable fun r => ∫⁻ h, β₁ (r⁻¹ * h * g) ∂ν := by
          have : Measurable fun p : G × G => β₁ (p.1⁻¹ * p.2 * g) := by fun_prop
          exact this.lintegral_prod_right'
        calc β g * Φ g = β g * Φ g * ∫⁻ r, ∫⁻ h, β₁ (r⁻¹ * h * g) ∂ν ∂ρ := by rw [h1 g, mul_one]
          _ = _ := by
            rw [← lintegral_const_mul _ hm2]
            refine lintegral_congr fun r => ?_
            rw [lintegral_const_mul _ (hm1 r)]
    _ = ∫⁻ r, ∫⁻ h, ∫⁻ g, β g * Φ g * β₁ (r⁻¹ * h * g) ∂μ ∂ν ∂ρ :=
        swap3 (fun r h g => β g * Φ g * β₁ (r⁻¹ * h * g))
          (show Measurable fun p : G × G × G => β p.2.2 * Φ p.2.2 * β₁ (p.1⁻¹ * p.2.1 * p.2.2) by fun_prop)
    _ = ∫⁻ r, ∫⁻ h, ∫⁻ g, β (h⁻¹ * g) * Φ g * β₁ (r⁻¹ * g) ∂μ ∂ν ∂ρ := by
        refine lintegral_congr fun r => lintegral_congr_ae (hH'.mono fun h hh => ?_)
        refine (lintegral_mul_left_eq_self (μ := μ) (fun x => β x * Φ x * β₁ (r⁻¹ * h * x)) h⁻¹).symm.trans
          (lintegral_congr fun g => ?_)
        show β (h⁻¹ * g) * Φ (h⁻¹ * g) * β₁ (r⁻¹ * h * (h⁻¹ * g)) = _
        rw [hΦH _ hh, mul_assoc r⁻¹ h, mul_inv_cancel_left]
    _ = ∫⁻ r, ∫⁻ g, ∫⁻ h, β (h⁻¹ * g) * Φ g * β₁ (r⁻¹ * g) ∂ν ∂μ ∂ρ := by
        refine lintegral_congr fun r => ?_
        exact lintegral_lintegral_swap
          (show Measurable fun p : G × G => β (p.1⁻¹ * p.2) * Φ p.2 * β₁ (r⁻¹ * p.2) by fun_prop).aemeasurable
    _ = ∫⁻ r, ∫⁻ g, Φ g * β₁ (r⁻¹ * g) ∂μ ∂ρ := by
        refine lintegral_congr fun r => lintegral_congr fun g => ?_
        simp_rw [mul_assoc]
        rw [lintegral_mul_const _ (show Measurable fun h : G => β (h⁻¹ * g) by fun_prop), hinvβ g, one_mul]
    _ = ∫⁻ r, ∫⁻ g, Φ (r * g) * β₁ g ∂μ ∂ρ := by
        refine lintegral_congr fun r => ?_
        refine (lintegral_mul_left_eq_self (μ := μ) (fun x => Φ x * β₁ (r⁻¹ * x)) r).symm.trans
          (lintegral_congr fun g => ?_)
        show Φ (r * g) * β₁ (r⁻¹ * (r * g)) = _
        rw [inv_mul_cancel_left]
    _ = ∫⁻ g, ∫⁻ r, Φ (r * g) * β₁ g ∂ρ ∂μ :=
        lintegral_lintegral_swap
          (show Measurable fun p : G × G => Φ (p.1 * p.2) * β₁ p.2 by fun_prop).aemeasurable
    _ = ∫⁻ g, ∫⁻ r, Φ (r * g) ∂ρ ∂μ.withDensity β₁ := by
        have hm : Measurable fun g => ∫⁻ r, Φ (r * g) ∂ρ := by
          have : Measurable fun p : G × G => Φ (p.2 * p.1) := by fun_prop
          exact this.lintegral_prod_right'
        rw [lintegral_withDensity_eq_lintegral_mul _ hβ₁ hm]
        refine lintegral_congr fun g => ?_
        rw [lintegral_mul_const _ (show Measurable fun r : G => Φ (r * g) by fun_prop)]
        exact mul_comm _ _

end QuadraticTransferFirst

theorem isUnit_last_join : Q1 := by
  intro G _ _ _ _ _ _ _ μ _ ν ρ _ _ H β β₁ hinv hH hβ hβ₁ h1 Φ hΦ hΦH
  exact QuadraticTransferFirst.main μ ν ρ H β β₁ hinv hH hβ hβ₁ h1 Φ hΦ hΦH

end PositivityTheory.AdelicQuotientData

end
end
