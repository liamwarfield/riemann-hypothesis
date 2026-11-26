module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.LocOpMMLaw
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopLocForm

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopMChar
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopChiWPf
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace KC
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
def sec_k : (InfinitePlace F → ℂ) → AE F E := (Place.exists_sec d.cm d.B.emb).choose
theorem sec_spec_k : Continuous (_root_.PositivityTheory.SiegelWeilFormula.KC.sec_k d) ∧ (∀ x w, piInf (d.B.emb w) (_root_.PositivityTheory.SiegelWeilFormula.KC.sec_k d x) = x w) ∧ (∀ x, finOne F • _root_.PositivityTheory.SiegelWeilFormula.KC.sec_k d x = 0) ∧
    (∀ x y, _root_.PositivityTheory.SiegelWeilFormula.KC.sec_k d (x + y) = _root_.PositivityTheory.SiegelWeilFormula.KC.sec_k d x + _root_.PositivityTheory.SiegelWeilFormula.KC.sec_k d y) ∧ (∀ x y, _root_.PositivityTheory.SiegelWeilFormula.KC.sec_k d (x * y) = _root_.PositivityTheory.SiegelWeilFormula.KC.sec_k d x * _root_.PositivityTheory.SiegelWeilFormula.KC.sec_k d y) :=
  (Place.exists_sec d.cm d.B.emb).choose_spec
theorem uW_eq_k (w : InfinitePlace F) (z : ℂ) :
    d.uW w z = _root_.PositivityTheory.SiegelWeilFormula.KC.sec_k d (Function.update (fun _ => 1) w z) + finOne F • (1 : AE F E) := rfl
theorem sec_mul_e_k (x : InfinitePlace F → ℂ) : _root_.PositivityTheory.SiegelWeilFormula.KC.sec_k d x * (finOne F • (1 : AE F E)) = 0 := by
  rw [mul_smul_comm, mul_one, (_root_.PositivityTheory.SiegelWeilFormula.KC.sec_spec_k d).2.2.1]
theorem e_mul_sec_k (x : InfinitePlace F → ℂ) : (finOne F • (1 : AE F E)) * _root_.PositivityTheory.SiegelWeilFormula.KC.sec_k d x = 0 := by
  rw [smul_mul_assoc, one_mul, (_root_.PositivityTheory.SiegelWeilFormula.KC.sec_spec_k d).2.2.1]
theorem uW_mul_k (w : InfinitePlace F) (z z' : ℂ) : d.uW w (z * z') = d.uW w z * d.uW w z' := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.KC.uW_eq_k, _root_.PositivityTheory.SiegelWeilFormula.KC.uW_eq_k, _root_.PositivityTheory.SiegelWeilFormula.KC.uW_eq_k, update_mul, (_root_.PositivityTheory.SiegelWeilFormula.KC.sec_spec_k d).2.2.2.2, add_mul, mul_add, mul_add, _root_.PositivityTheory.SiegelWeilFormula.KC.sec_mul_e_k, _root_.PositivityTheory.SiegelWeilFormula.KC.e_mul_sec_k, e_mul_e]
  abel
theorem uW_one_k (w : InfinitePlace F) : d.uW w 1 = 1 := by
  apply d.ae_ext
  · intro w'
    rw [_root_.PositivityTheory.SiegelWeilFormula.KC.uW_eq_k, map_add (f := _), (_root_.PositivityTheory.SiegelWeilFormula.KC.sec_spec_k d).2.1, Place.piInf_finOne, map_one]
    simp [Function.update_apply]
  · rw [_root_.PositivityTheory.SiegelWeilFormula.KC.uW_eq_k, smul_add, (_root_.PositivityTheory.SiegelWeilFormula.KC.sec_spec_k d).2.2.1, smul_smul, finOne_mul_self, zero_add]
theorem uW_isUnit_k (w : InfinitePlace F) {z : ℂ} (hz : z ≠ 0) : IsUnit (d.uW w z) := by
  have h : d.uW w z * d.uW w z⁻¹ = 1 := by rw [← _root_.PositivityTheory.SiegelWeilFormula.KC.uW_mul_k, mul_inv_cancel₀ hz, _root_.PositivityTheory.SiegelWeilFormula.KC.uW_one_k]
  exact ⟨⟨d.uW w z, d.uW w z⁻¹, h, by rw [mul_comm]; exact h⟩, rfl⟩
theorem uW_cont_k (w : InfinitePlace F) : Continuous (d.uW w) := by
  have h : Continuous fun z : ℂ => Function.update (fun _ : InfinitePlace F => (1 : ℂ)) w z :=
    continuous_const.update w continuous_id
  exact ((_root_.PositivityTheory.SiegelWeilFormula.KC.sec_spec_k d).1.comp h).add continuous_const
end KC
namespace SD
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
theorem _root_.PositivityTheory.SiegelWeilFormula.SD_k.chiW_mul_pf (w : InfinitePlace F) : ∀ z z' : ℂ, z ≠ 0 → z' ≠ 0 →
    d.chiW w (z * z') = d.chiW w z * d.chiW w z' := by
  intro z z' hz hz'
  have h1 := _root_.PositivityTheory.SiegelWeilFormula.KC.uW_isUnit_k d w hz
  have h2 := _root_.PositivityTheory.SiegelWeilFormula.KC.uW_isUnit_k d w hz'
  have h3 := _root_.PositivityTheory.SiegelWeilFormula.KC.uW_isUnit_k d w (mul_ne_zero hz hz')
  unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.chiW
  rw [dite_eq_left h3, dite_eq_left h1, dite_eq_left h2]
  have : h3.unit = h1.unit * h2.unit := Units.ext (by simp [_root_.PositivityTheory.SiegelWeilFormula.KC.uW_mul_k])
  rw [this, map_mul, Circle.coe_mul]
theorem _root_.PositivityTheory.SiegelWeilFormula.SD_k.chiW_cont_pf (w : InfinitePlace F) : ContinuousOn (d.chiW w) {z : ℂ | z ≠ 0} := by
  rw [continuousOn_iff_continuous_domRestrict]
  let U : {z : ℂ // z ≠ 0} → (AE F E)ˣ := fun z => (_root_.PositivityTheory.SiegelWeilFormula.KC.uW_isUnit_k d w z.2).unit
  have hU : Continuous U := by
    rw [Units.continuous_iff]
    constructor
    · exact (_root_.PositivityTheory.SiegelWeilFormula.KC.uW_cont_k d w).comp continuous_subtype_val
    · have e : ∀ z : {z : ℂ // z ≠ 0}, ((U z)⁻¹ : (AE F E)ˣ).1 = d.uW w (z.1)⁻¹ := fun z =>
        Units.inv_eq_of_mul_eq_one_right (by
          show d.uW w z.1 * d.uW w (z.1)⁻¹ = 1
          rw [← _root_.PositivityTheory.SiegelWeilFormula.KC.uW_mul_k, mul_inv_cancel₀ z.2, _root_.PositivityTheory.SiegelWeilFormula.KC.uW_one_k])
      simp only [e]
      exact (_root_.PositivityTheory.SiegelWeilFormula.KC.uW_cont_k d w).comp (continuous_subtype_val.inv₀ fun z => z.2)
  have e : Set.domRestrict {z : ℂ | z ≠ 0} (d.chiW w) = fun z => ((d.χ (U z) : Circle) : ℂ) := by
    funext z
    rw [Set.domRestrict_apply]
    unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.chiW
    rw [dite_eq_left (_root_.PositivityTheory.SiegelWeilFormula.KC.uW_isUnit_k d w z.2)]
  rw [e]
  exact continuous_subtype_val.comp (d.ok.hecke.1.comp hU)
theorem _root_.PositivityTheory.SiegelWeilFormula.SD_k.chiW_pos_pf (w : InfinitePlace F) : ∀ r : ℝ, 0 < r → d.chiW w (r : ℂ) = 1 := by
  intro r hr
  set t := Real.sqrt r with ht
  have ht0 : (t : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    exact (Real.sqrt_pos.mpr hr).ne'
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hc : cA σ (d.uW w t) = d.uW w t := by
    apply d.ae_ext
    · intro w'
      rw [Place.piInf_cA d.cm, _root_.PositivityTheory.SiegelWeilFormula.KC.uW_eq_k, map_add (f := _), (_root_.PositivityTheory.SiegelWeilFormula.KC.sec_spec_k d).2.1, Place.piInf_finOne, add_zero]
      by_cases h : w' = w
      · subst h; simp
      · simp [Function.update_apply, h]
    · rw [← map_smul, _root_.PositivityTheory.SiegelWeilFormula.KC.uW_eq_k, smul_add, (_root_.PositivityTheory.SiegelWeilFormula.KC.sec_spec_k d).2.2.1, zero_add, smul_smul, KC.finOne_mul_self, map_smul,
        map_one]
  have huw : d.uW w (r : ℂ) = d.uW w t * cA σ (d.uW w t) := by
    rw [hc, ← _root_.PositivityTheory.SiegelWeilFormula.KC.uW_mul_k, ← Complex.ofReal_mul, ht, Real.mul_self_sqrt hr.le]
  obtain ⟨ξ, hξ⟩ := GlobalTheory.SplitIdele.exists_isQuad d.cm
  have hn := hξ.algebraMap_norm (d.uW w t)
  let u := (_root_.PositivityTheory.SiegelWeilFormula.KC.uW_isUnit_k d w ht0).unit
  let a : (AF F)ˣ := Units.map (Algebra.norm (AF F) : AE F E →* AF F) u
  have ha : Units.map (algebraMap (AF F) (AE F E) : AF F →* AE F E) a = (_root_.PositivityTheory.SiegelWeilFormula.KC.uW_isUnit_k d w hr0).unit :=
    Units.ext (by
      show algebraMap (AF F) (AE F E) (Algebra.norm (AF F) (d.uW w t)) = d.uW w (r : ℂ)
      rw [hn, huw])
  have hres := d.ok.res a
  rw [if_pos (Subgroup.mem_sup_right (MonoidHom.mem_range.mpr ⟨u, rfl⟩))] at hres
  unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.chiW
  rw [dite_eq_left (_root_.PositivityTheory.SiegelWeilFormula.KC.uW_isUnit_k d w hr0), ← ha]
  exact hres
end SD
end PositivityTheory.SiegelWeilFormula
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace SD
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
theorem _root_.PositivityTheory.SiegelWeilFormula.SD_k.chiW_mul (w : InfinitePlace F) : ∀ z z' : ℂ, z ≠ 0 → z' ≠ 0 → d.chiW w (z * z') = d.chiW w z * d.chiW w z' :=
  d.chiW_mul_pf w
theorem _root_.PositivityTheory.SiegelWeilFormula.SD_k.chiW_cont (w : InfinitePlace F) : ContinuousOn (d.chiW w) {z : ℂ | z ≠ 0} :=
  d.chiW_cont_pf w
theorem _root_.PositivityTheory.SiegelWeilFormula.SD_k.chiW_norm (w : InfinitePlace F) : ∀ z : ℂ, z ≠ 0 → ‖d.chiW w z‖ = 1 := by
  intro z _
  by_cases h : IsUnit (d.uW w z)
  · rw [_root_.PositivityTheory.SiegelWeilFormula.SD_k.chiW, dite_eq_left h]
    exact Circle.norm_coe _
  · rw [_root_.PositivityTheory.SiegelWeilFormula.SD_k.chiW, dite_eq_right h, norm_one]
theorem _root_.PositivityTheory.SiegelWeilFormula.SD_k.chiW_pos (w : InfinitePlace F) : ∀ r : ℝ, 0 < r → d.chiW w (r : ℂ) = 1 :=
  d.chiW_pos_pf w
theorem _root_.PositivityTheory.SiegelWeilFormula.SD_k.chiW_form (w : InfinitePlace F) : ∃ k : ℤ, ∀ z : ℂ, z ≠ 0 → d.chiW w z = (z / (‖z‖ : ℂ)) ^ k :=
  GlobalTheory.T.continuous_unitary_multiplicative_eq_arg_pow (d.chiW w) (d.chiW_mul w) (d.chiW_cont w) (d.chiW_norm w) (d.chiW_pos w)
end SD
namespace RD
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F)
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.stepM_val (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) : ∀ (y : GR d.n) (a : Matrix (Fin d.n) (Fin d.n) ℂ), IsUnit a.det → mR y = mLoc a →
    R.StepOK w (R.ι w y) (fun f u => (d.chiW w a.det * (‖a.det‖ : ℂ) ^ d.m) * f (Matrix.of u * a)) id :=
  R.stepM_val_pf w hT
variable {L : GR d.n → ((Fin d.m → Fin d.n → ℂ) → ℂ) → (Fin d.m → Fin d.n → ℂ) → ℂ}
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.locOp_mM_law (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hG : _root_.PositivityTheory.SiegelWeilFormula.GoodAwayEx_k) (hL : R.IsLocOp w L) :
    ∃ k : ℤ, ∀ (y : GR d.n) (a : Matrix (Fin d.n) (Fin d.n) ℂ), IsUnit a.det → mR y = mLoc a → ∀ f, IsSw f →
      L y f = fun u => (a.det / (‖a.det‖ : ℂ)) ^ k * (‖a.det‖ : ℂ) ^ d.m * f (Matrix.of u * a) := by
  obtain ⟨k, hk⟩ := d.chiW_form w
  refine ⟨k, fun y a ha hy f hf => ?_⟩
  obtain ⟨Ψ, hΨ⟩ := hG F E σ d R w
  obtain ⟨Φ, hΦ, hT'⟩ := R.exists_adm hT hΨ hf
  have e1 := (hL y f hf).2 Ψ hΨ.1 Φ hΦ hT'
  have e2 := ((R.stepM_val w hT y a ha hy).2 Ψ hΨ.1).2 f hf Φ hΦ hT'
  rw [R.tens_cancel hΨ.1 hΨ.2.1 (e1.symm.trans e2), hk _ ha.ne_zero]
  rfl
end RD
end PositivityTheory.SiegelWeilFormula
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopLocNbar
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace RD
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {w : InfinitePlace F}
  {L : GR d.n → ((Fin d.m → Fin d.n → ℂ) → ℂ) → (Fin d.m → Fin d.n → ℂ) → ℂ}
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.locOp_zero (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hG : _root_.PositivityTheory.SiegelWeilFormula.GoodAwayEx_k) (hL : R.IsLocOp w L) (y : GR d.n) : L y 0 = 0 := by
  obtain ⟨Ψ, hΨ⟩ := hG F E σ d R w
  have h0 : IsSw (0 : d.LF) := ⟨0, by ext; simp⟩
  obtain ⟨Φ, hΦ, hT'⟩ := R.exists_adm hT hΨ h0
  have hΦ0 : Φ = 0 := d.T_inj hT Φ hΦ (by rw [hT']; funext X; simp [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens])
  have e := (hL y 0 h0).2 Ψ hΨ.1 Φ hΦ hT'
  rw [hΦ0, map_zero, d.T_zero] at e
  apply R.tens_cancel hΨ.1 hΨ.2.1
  rw [← e]
  funext X
  simp [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens]
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.locOp_nbar (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (hG : _root_.PositivityTheory.SiegelWeilFormula.GoodAwayEx_k) (hL : R.IsLocOp w L) :
    ∃ (C s κ : ℂ) (ε : ℤˣ), s ≠ 0 ∧ κ ≠ 0 ∧
      (∀ f : d.LF, IsSw f → locFT C s (locFT C s (locFT C s (locFT C s f))) = κ • f) ∧
      (∀ (y : GR d.n) (c : Matrix (Fin d.n) (Fin d.n) ℂ), cᴴ = c → mR y = nbLoc c → ∀ f, IsSw f →
        L y f = κ⁻¹ • locFT C s (locFT C s (locFT C s
          (chirp ((R.sg w : ℤ) : ℂ) ((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c) (locFT C s f))))) ∧
      (∀ (y : GR d.n) (c : Matrix (Fin d.n) (Fin d.n) ℂ), cᴴ = c → mR y = nbLoc c → ∀ f, IsSw f →
        locFT C s (L y f) = chirp ((R.sg w : ℤ) : ℂ) ((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c) (locFT C s f)) ∧
      ‖s‖ = 2 ∧ ((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹ = -1 := by
  obtain ⟨-, ⟨ε, w₀, hw₀, -⟩, -⟩ := hA F E σ d
  obtain ⟨C, B, -, hW⟩ := R.stepW_exp w hT hA ε w₀ hw₀
  set s : ℂ := -2 * ((ε : ℤ) : ℂ) * ((R.sg w : ℤ) : ℂ) / R.ζ with hs_def
  have hW' : R.StepOK w w₀ (locFT C s) B := hW
  have hζn : ‖R.ζ‖ = 1 := by
    rcases R.hζ with ⟨-, hz⟩ | ⟨-, hz⟩ <;> rw [hz] <;> simp
  have hunit : ∀ u : ℤˣ, ‖((u : ℤ) : ℂ)‖ = 1 := fun u => by
    rcases Int.units_eq_one_or u with h | h <;> rw [h] <;> simp
  have hsn : ‖s‖ = 2 := by
    rw [hs_def, norm_div, norm_mul, norm_mul, hunit, hunit, hζn]
    norm_num
  have hs : s ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hsn
    norm_num at hsn
  have hη : ((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹ = -1 := by
    rw [R.isW_eps w hw₀]
    rcases R.hζ with ⟨he, hz⟩ | ⟨he, hz⟩
    · rw [he, hz]; simp
    · rw [he, hz]; simp [Complex.inv_I]
  have hsch := d.om_sch
  have h4 := R.step_comp w hsch (R.step_comp w hsch (R.step_comp w hsch hW' hW') hW') hW'
  rw [_root_.PositivityTheory.SiegelWeilFormula.RD_k.w_four hw₀] at h4
  obtain ⟨Ψ, hΨ⟩ := hG F E σ d R w
  obtain ⟨X₀, hX₀⟩ : ∃ X₀, Ψ X₀ ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hΨ.2.1 (funext hc)
  have hB4 : d.IsAwayW w (B (B (B (B Ψ)))) := (h4.2 Ψ hΨ.1).1
  have key : ∀ f : d.LF, IsSw f → ∀ X, f (R.loc w X) * Ψ X =
      locFT C s (locFT C s (locFT C s (locFT C s f))) (R.loc w X) * B (B (B (B Ψ))) X := by
    intro f hf X
    obtain ⟨Φ, hΦ, hT'⟩ := R.exists_adm hT hΨ hf
    have e := (h4.2 Ψ hΨ.1).2 f hf Φ hΦ hT'
    rw [map_one, Module.End.one_apply, hT'] at e
    exact congrFun e X
  have key0 : ∀ f : d.LF, IsSw f → ∀ u, f u * Ψ X₀ =
      locFT C s (locFT C s (locFT C s (locFT C s f))) u * B (B (B (B Ψ))) X₀ := by
    intro f hf u
    obtain ⟨Z, hZ1, hZ2, hZ3⟩ := R.loc_surj w X₀ u
    have := key f hf (X₀ + Z)
    rwa [hZ3, hΨ.1 X₀ Z hZ1 hZ2, hB4 X₀ Z hZ1 hZ2] at this
  by_cases hb : B (B (B (B Ψ))) X₀ = 0
  · have hz : ∀ f : d.LF, IsSw f → f = 0 := by
      intro f hf
      funext u
      have := key0 f hf u
      rw [hb, mul_zero] at this
      exact (mul_eq_zero.mp this).resolve_right hX₀
    refine ⟨C, s, 1, ε, hs, one_ne_zero, fun f hf => ?_, fun y c hc hy f hf => ?_, fun y c hc hy f hf => ?_, hsn, hη⟩
    · rw [hz f hf]
      simp [locFT_zero]
    · rw [hz f hf, R.locOp_zero hT hG hL y]
      simp [locFT_zero, chirp_zero]
    · rw [hz f hf, R.locOp_zero hT hG hL y]
      simp [locFT_zero, chirp_zero]
  · set κ := Ψ X₀ / B (B (B (B Ψ))) X₀ with hκ
    have hκ0 : κ ≠ 0 := div_ne_zero hX₀ hb
    have h4f : ∀ f : d.LF, IsSw f → locFT C s (locFT C s (locFT C s (locFT C s f))) = κ • f := by
      intro f hf
      funext u
      have := key0 f hf u
      simp only [Pi.smul_apply, smul_eq_mul, hκ]
      field_simp
      linear_combination -this
    have hmain : ∀ (y : GR d.n) (c : Matrix (Fin d.n) (Fin d.n) ℂ), cᴴ = c → mR y = nbLoc c → ∀ f, IsSw f →
        IsSw (chirp ((R.sg w : ℤ) : ℂ) ((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c) (locFT C s f)) ∧
        L y f = κ⁻¹ • locFT C s (locFT C s (locFT C s
          (chirp ((R.sg w : ℤ) : ℂ) ((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c) (locFT C s f)))) := by
      intro y c hc hy f hf
      obtain ⟨y', hy', hrel⟩ := R.oppositeUnipotent_weylConj w hw₀ y c hc hy
      have hx : ((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c)ᴴ = (((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c := by
        have hs : star (((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) = ((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹ := by
          rcases R.hζ with ⟨-, hz⟩ | ⟨-, hz⟩
          · rw [hz]; simp
          · rw [hz]; simp [Complex.inv_I]
        rw [Matrix.conjTranspose_smul, hc, hs]
      have hN : R.StepOK w (R.ι w y') (chirp ((R.sg w : ℤ) : ℂ) ((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c)) id :=
        R.stepN w hT y' _ hx hy'
      refine ⟨hN.1 _ (hW'.1 f hf), ?_⟩
      by_cases hf0 : ∀ u, f u = 0
      · have : f = 0 := funext hf0
        rw [this, R.locOp_zero hT hG hL y]
        simp [locFT_zero, chirp_zero]
      push Not at hf0
      obtain ⟨u₀, hu₀⟩ := hf0
      have hBΨ : ∀ X, B (B (B (B Ψ))) X = κ⁻¹ * Ψ X := by
        intro X
        obtain ⟨Z, hZ1, hZ2, hZ3⟩ := R.loc_surj w X u₀
        have := key f hf (X + Z)
        rw [hZ3, hΨ.1 X Z hZ1 hZ2, hB4 X Z hZ1 hZ2, h4f f hf] at this
        simp only [Pi.smul_apply, smul_eq_mul] at this
        rw [eq_inv_mul_iff_mul_eq₀ hκ0]
        apply mul_left_cancel₀ hu₀
        linear_combination -this
      have hc3 := R.step_comp w hsch (R.step_comp w hsch (R.step_comp w hsch (R.step_comp w hsch hW' hW') hW') hN) hW'
      obtain ⟨Φ, hΦ, hT'⟩ := R.exists_adm hT hΨ hf
      have e := (hc3.2 Ψ hΨ.1).2 f hf Φ hΦ hT'
      have e1 := (hL y f hf).2 Ψ hΨ.1 Φ hΦ hT'
      rw [hrel] at e1
      apply R.tens_cancel hΨ.1 hΨ.2.1
      rw [← e1, e]
      funext X
      simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, Function.comp_apply, id, Pi.smul_apply, smul_eq_mul, hBΨ]
      ring
    refine ⟨C, s, κ, ε, hs, hκ0, h4f, fun y c hc hy f hf => (hmain y c hc hy f hf).2,
      fun y c hc hy f hf => ?_, hsn, hη⟩
    obtain ⟨hsw, heq⟩ := hmain y c hc hy f hf
    rw [heq, locFT_smul, h4f _ hsw, smul_smul, inv_mul_cancel₀ hκ0, one_smul]
end RD
end PositivityTheory.SiegelWeilFormula
end
end
end
