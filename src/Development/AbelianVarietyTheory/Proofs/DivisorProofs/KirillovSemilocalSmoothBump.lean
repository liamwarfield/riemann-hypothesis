module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormModerateGrowthCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KirillovSemiLocalMirabolicAbstract

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicGLComplementarySupportsCommute
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicGLComplementarySupportsCommute
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

namespace GlobalTheory.JSW.MirSemi

theorem supS_mul_comm : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (h t : GA E a), h ∈ GlobalTheory.JSW.supS (E := E) (a := a) S →
    GeneralLinearGroup.map (pInf E) t = 1 →
    (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) t = 1) → h * t = t * h := by
  intro E _ _ _ a S h t hh ht htS
  refine ga_ext ?_ ?_
  · rw [map_mul, map_mul, ht, mul_one, one_mul]
  · ext i j w
    have key : GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) (h * t) =
        GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) (t * h) := by
      rw [map_mul, map_mul]
      by_cases hw : w ∈ S
      · rw [htS w hw, mul_one, one_mul]
      · rw [hh w hw, mul_one, one_mul]
    have e : ((GeneralLinearGroup.map (pFin E) (h * t)).val i j) w =
        ((GeneralLinearGroup.map (pFin E) (t * h)).val i j) w :=
      congrArg (fun g : GL (Fin a) (w.adicCompletion E) => g.val i j) key
    rw [e]

end GlobalTheory.JSW.MirSemi
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicGLComplementarySupportsCommuteStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicGL_complementary_supports_commute : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (h t : GA E a), h ∈ GlobalTheory.JSW.supS (E := E) (a := a) S → GeneralLinearGroup.map (pInf E) t = 1 → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) t = 1) → h * t = t * h := by
  first | exact @GlobalTheory.JSW.MirSemi.supS_mul_comm | exact GlobalTheory.JSW.MirSemi.supS_mul_comm | (intros; apply GlobalTheory.JSW.MirSemi.supS_mul_comm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanKernelSpanCuspFormRightInvariantOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanKernelSpanCuspFormRightInvariantOpen
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

namespace GlobalTheory.JSW.MirSemi.OpenInv

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def invSub (F : GA E a → ℂ) : Subgroup (GL (Fin a) (Af E)) where
  carrier := {k | ∀ g, F (g * finGL E a k) = F g}
  one_mem' g := by simp
  mul_mem' {k l} hk hl g := by rw [map_mul, ← mul_assoc, hl, hk]
  inv_mem' {k} hk g := by
    have := hk (g * finGL E a k⁻¹)
    rw [mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one] at this
    exact this.symm


variable (E a) in
def openInv : Submodule ℂ (GA E a → ℂ) where
  carrier := {F | IsOpen (invSub F : Set (GL (Fin a) (Af E)))}
  zero_mem' := by
    have : invSub (0 : GA E a → ℂ) = ⊤ := by
      ext k; simp [invSub]
    show IsOpen ((invSub (0 : GA E a → ℂ) : Subgroup (GL (Fin a) (Af E))) : Set (GL (Fin a) (Af E)))
    rw [this]; exact isOpen_univ
  add_mem' {F G} hF hG := by
    have hF' : IsOpen (invSub F : Set (GL (Fin a) (Af E))) := hF
    have hG' : IsOpen (invSub G : Set (GL (Fin a) (Af E))) := hG
    refine Subgroup.isOpen_mono (H₁ := invSub F ⊓ invSub G) ?_ (hF'.inter hG')
    intro k hk g
    simp only [Pi.add_apply]
    rw [hk.1 g, hk.2 g]
  smul_mem' c F hF := by
    refine Subgroup.isOpen_mono (H₁ := invSub F) ?_ hF
    intro k hk g
    simp only [Pi.smul_apply]
    rw [hk g]

theorem rt_mem_openInv {F : GA E a → ℂ} (hF : F ∈ openInv E a) (h : GA E a) :
    (fun g => F (g * h)) ∈ openInv E a := by
  set y := GeneralLinearGroup.map (pInf E) h
  set k := GeneralLinearGroup.map (pFin E) h
  have hh : infGL E a y * finGL E a k = h := infGL_mul_finGL h
  have hc : Continuous fun u : GL (Fin a) (Af E) => k⁻¹ * u * k :=
    (continuous_const.mul continuous_id).mul continuous_const
  let U : Subgroup (GL (Fin a) (Af E)) := (invSub F).comap (MulAut.conj k⁻¹).toMonoidHom
  have hU : (U : Set _) = (fun u : GL (Fin a) (Af E) => k⁻¹ * u * k) ⁻¹' (invSub F : Set _) := by
    ext u; simp [U, MulAut.conj_apply]
  have hF' : IsOpen (invSub F : Set (GL (Fin a) (Af E))) := hF
  refine Subgroup.isOpen_mono (H₁ := U) ?_ (by rw [hU]; exact hF'.preimage hc)
  intro u hu g
  have hu' : ∀ g, F (g * finGL E a (k⁻¹ * u * k)) = F g := by
    have hm : k⁻¹ * u * k ∈ invSub F := by
      have := Subgroup.mem_comap.1 hu; simpa [MulAut.conj_apply] using this
    exact hm
  change F (g * finGL E a u * h) = F (g * h)
  rw [← hu' (g * h), ← hh]
  congr 1
  simp only [map_mul, map_inv, mul_assoc]
  rw [← mul_assoc (finGL E a u) (infGL E a y), ← infGL_comm, mul_assoc, mul_inv_cancel_left]

theorem kerInf_mem_openInv {F : GA E a → ℂ} (hF : F ∈ openInv E a) {X : Type} [MeasurableSpace X]
    (ν : Measure X) (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)) : kerInf ν k γ F ∈ openInv E a := by
  refine Subgroup.isOpen_mono (H₁ := invSub F) ?_ (show IsOpen (invSub F : Set (GL (Fin a) (Af E))) from hF)
  intro u hu g
  change ∫ x, k x * F (g * finGL E a u * infGL E a (γ x)) ∂ν = ∫ x, k x * F (g * infGL E a (γ x)) ∂ν
  congr 1; funext x
  rw [mul_assoc, ← infGL_comm, ← mul_assoc, hu]

theorem mem_openInv_of_mem {π : CuspSub E a} {φ : Sm E a} (hφ : φ ∈ π.V) : φ.1 ∈ openInv E a := by
  have h := π.isSmooth_finPart ⟨φ, hφ⟩
  show IsOpen (invSub φ.1 : Set (GL (Fin a) (Af E)))
  have e : (invSub φ.1 : Set (GL (Fin a) (Af E))) = {k | π.finPart k ⟨φ, hφ⟩ = ⟨φ, hφ⟩} := by
    ext k
    simp only [SetLike.mem_coe, Set.mem_setOf_eq]
    exact ⟨fun hk => Subtype.ext (Subtype.ext (funext hk)), fun hk g => congrArg (fun ψ : π.V => ψ.1.1 g) hk⟩
  rw [e]; exact h

end GlobalTheory.JSW.MirSemi.OpenInv


open GlobalTheory.JSW.MirSemi.OpenInv in
theorem GlobalTheory.JSW.MirSemi.locSpan_openInv : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (π : CuspSub E a) (φ : Sm E a), φ ∈ π.V →
    ∀ F ∈ GlobalTheory.JSW.MirSemi.locSpan S φ.1, ∃ U : Subgroup (GL (Fin a) (Af E)),
      IsOpen (U : Set (GL (Fin a) (Af E))) ∧ ∀ u ∈ U, ∀ g, F (g * finGL E a u) = F g := by
  intro E _ _ _ a S π φ hφ F hF
  have h := GlobalTheory.JSW.MirSemi.locSpan_le (V := openInv E a) (S := S) (mem_openInv_of_mem hφ)
    (fun F hF h _ => rt_mem_openInv hF h) (fun F hF X _ ν _ k γ _ => kerInf_mem_openInv hF ν k γ) hF
  exact ⟨invSub F, h, fun u hu g => hu g⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanKernelSpanCuspFormRightInvariantOpenStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanKernelSpan_cuspForm_right_invariant_open : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (π : CuspSub E a) (φ : Sm E a), φ ∈ π.V → ∀ F ∈ GlobalTheory.JSW.MirSemi.locSpan S φ.1, ∃ U : Subgroup (GL (Fin a) (Af E)), IsOpen (U : Set (GL (Fin a) (Af E))) ∧ ∀ u ∈ U, ∀ g, F (g * finGL E a u) = F g := by
  first | exact @GlobalTheory.JSW.MirSemi.locSpan_openInv | exact GlobalTheory.JSW.MirSemi.locSpan_openInv | (intros; apply GlobalTheory.JSW.MirSemi.locSpan_openInv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KirillovSemilocalMirabolicWhittaker
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhittakerRelationPassesToSemiLocalSpan
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhittakerRelationPassesToSemiLocalSpan
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

namespace GlobalTheory.JSW.MirSemi

open GlobalTheory.JSW

theorem whit_rt_apply {E : Type} [Field E] [NumberField E] {a : ℕ} (F : GA E a → ℂ) (h g : GA E a) :
    whit (fun x => F (x * h)) g = whit F (g * h) := by
  simp only [whit, GroundTheory.Automorphic.FourierWhittaker.whittaker, mul_assoc]

theorem whit_zero_apply {E : Type} [Field E] [NumberField E] {a : ℕ} (g : GA E a) :
    whit (0 : GA E a → ℂ) g = 0 := by
  simp [whit, GroundTheory.Automorphic.FourierWhittaker.whittaker]

theorem mul_mem_supS' {E : Type} [Field E] [NumberField E] {a : ℕ} {S : Finset (HeightOneSpectrum (𝓞 E))}
    {x h : GA E a} (hx : x ∈ supS (E := E) (a := a) S) (hh : h ∈ supS (E := E) (a := a) S) : x * h ∈ supS (E := E) (a := a) S := by
  intro w hw
  rw [map_mul, hx w hw, hh w hw, one_mul]

theorem infGL_mem_supS' {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (S : Finset (HeightOneSpectrum (𝓞 E)))
    (y : GL (Fin a) (Cinf E)) : infGL E a y ∈ supS (E := E) (a := a) S := by
  intro w _
  have h1 : GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) (infGL E a y) =
      GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) (infGL E a y)) := by
    ext i j; rfl
  rw [h1, pFin_infGL, map_one]

theorem whit_rel_locSpan : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (π : CuspSub E a) (φ : Sm E a), φ ∈ π.V → ∀ (t : GA E a) (c : ℂ), GeneralLinearGroup.map (pInf E) t = 1 → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) t = 1) → (∀ x ∈ GlobalTheory.JSW.supS (E := E) (a := a) S, GlobalTheory.JSW.whit φ.1 (x * t) = c * GlobalTheory.JSW.whit φ.1 x) → ∀ F ∈ GlobalTheory.JSW.MirSemi.locSpan S φ.1, ∀ x ∈ GlobalTheory.JSW.supS (E := E) (a := a) S, GlobalTheory.JSW.whit F (x * t) = c * GlobalTheory.JSW.whit F x := by
  intro E _ _ _ a S π φ hφ t c htInf htS hrel
  have hreg := GlobalTheory.T.cusp_form_moderate_growth_compact E a S π φ hφ
  have hlin : ∀ F ∈ locSpan S φ.1, ∀ G ∈ locSpan S φ.1, ∀ (c' : ℂ) (g : GA E a),
      whit (fun x => F x + c' * G x) g = whit F g + c' * whit G g := fun F hF G hG =>
    (GlobalTheory.T.globalWhittakerCoefficient_linear_archimedeanKernel E a F G (hreg F hF).1 (hreg G hG).1 (hreg F hF).2 (hreg G hG).2).1
  let V : Submodule ℂ (GA E a → ℂ) :=
    { carrier := {F | F ∈ locSpan S φ.1 ∧ ∀ x ∈ supS (E := E) (a := a) S, whit F (x * t) = c * whit F x}
      add_mem' := by
        rintro F G ⟨hF, hF'⟩ ⟨hG, hG'⟩
        refine ⟨add_mem hF hG, fun x hx => ?_⟩
        have e : (F + G) = fun y => F y + 1 * G y := by funext y; simp
        rw [e, hlin F hF G hG, hlin F hF G hG, hF' x hx, hG' x hx]; ring
      zero_mem' := ⟨zero_mem _, fun x _ => by rw [whit_zero_apply, whit_zero_apply, mul_zero]⟩
      smul_mem' := by
        rintro c' F ⟨hF, hF'⟩
        refine ⟨Submodule.smul_mem _ c' hF, fun x hx => ?_⟩
        have e : (c' • F) = fun y => (0 : GA E a → ℂ) y + c' * F y := by funext y; simp
        rw [e, hlin 0 (zero_mem _) F hF, hlin 0 (zero_mem _) F hF, whit_zero_apply, whit_zero_apply, hF' x hx]
        ring }
  have hV : locSpan S φ.1 ≤ V := by
    refine locSpan_le ⟨self_mem_locSpan, hrel⟩ ?_ ?_
    · rintro F ⟨hF, hF'⟩ h hh
      refine ⟨rt_mem_locSpan hF hh, fun x hx => ?_⟩
      rw [whit_rt_apply, whit_rt_apply, mul_assoc, ← GlobalTheory.T.adelicGL_complementary_supports_commute E a S h t hh htInf htS, ← mul_assoc]
      exact hF' (x * h) (mul_mem_supS' hx hh)
    · rintro F ⟨hF, hF'⟩ X _ ν _ k γ hk
      refine ⟨kerInf_mem_locSpan hF ν hk, fun x hx => ?_⟩
      have hker := (GlobalTheory.T.globalWhittakerCoefficient_linear_archimedeanKernel E a F F (hreg F hF).1 (hreg F hF).1 (hreg F hF).2 (hreg F hF).2).2 X ν k γ hk
      rw [hker, hker, ← integral_const_mul]
      congr 1
      funext y
      have hc := GlobalTheory.T.adelicGL_complementary_supports_commute E a S (infGL E a (γ y)) t (infGL_mem_supS' S (γ y)) htInf htS
      rw [mul_assoc x t, ← hc, ← mul_assoc, hF' _ (mul_mem_supS' hx (infGL_mem_supS' S (γ y)))]
      ring
  intro F hF x hx
  exact (hV hF).2 x hx

end GlobalTheory.JSW.MirSemi
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhittakerRelationPassesToSemiLocalSpanStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_relation_passes_to_semi_local_span : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (π : CuspSub E a) (φ : Sm E a), φ ∈ π.V → ∀ (t : GA E a) (c : ℂ), GeneralLinearGroup.map (pInf E) t = 1 → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) t = 1) → (∀ x ∈ GlobalTheory.JSW.supS (E := E) (a := a) S, GlobalTheory.JSW.whit φ.1 (x * t) = c * GlobalTheory.JSW.whit φ.1 x) → ∀ F ∈ GlobalTheory.JSW.MirSemi.locSpan S φ.1, ∀ x ∈ GlobalTheory.JSW.supS (E := E) (a := a) S, GlobalTheory.JSW.whit F (x * t) = c * GlobalTheory.JSW.whit F x := by
  first | exact @GlobalTheory.JSW.MirSemi.whit_rel_locSpan | exact GlobalTheory.JSW.MirSemi.whit_rel_locSpan | (intros; apply GlobalTheory.JSW.MirSemi.whit_rel_locSpan <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspFormSemiLocalWhittakerSpace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspFormSemiLocalWhittakerSpace
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory Topology

namespace GlobalTheory.JSW.MirSemi

open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GlobalTheory.JSW

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem whit_smul_fun (c : ℂ) (F : GA E a → ℂ) (g : GA E a) : whit (c • F) g = c * whit F g := by
  unfold whit whittaker
  rw [← integral_const_mul]
  congr 1
  funext X
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem whit_mul_right_fun (F : GA E a → ℂ) (g h : GA E a) : whit F (g * h) = whit (fun z => F (z * h)) g := by
  simp only [whit, whittaker, mul_assoc]

theorem continuous_heightInf : Continuous (fun y : GL (Fin a) (Cinf E) => height y) := by
  unfold height
  have h1 : Continuous fun y : GL (Fin a) (Cinf E) => toL y.val :=
    continuous_pi fun i => continuous_pi fun j => Units.continuous_val.matrix_elem i j
  have h2 : Continuous fun y : GL (Fin a) (Cinf E) => toL (y⁻¹).val :=
    continuous_pi fun i => continuous_pi fun j => Units.continuous_coe_inv.matrix_elem i j
  exact (continuous_const.add h1.norm).add h2.norm

theorem height_pos_inf (y : GL (Fin a) (Cinf E)) : 0 < height y := by
  unfold height; positivity

theorem whit_infGL_growth {F : GA E a → ℂ} (hc : Continuous F)
    (hg : ∀ K : Set (GA E a), IsCompact K → ∃ (C : ℝ) (N : ℕ), ∀ g ∈ K, ∀ y : GL (Fin a) (Cinf E),
      ‖F (g * infGL E a y)‖ ≤ C * height y ^ N) (g : GA E a) :
    Continuous (fun y : GL (Fin a) (Cinf E) => whit F (g * infGL E a y)) ∧
      ∃ (C : ℝ) (N : ℕ), ∀ y, ‖whit F (g * infGL E a y)‖ ≤ C * height y ^ N := by
  set K : Set (GA E a) := (fun X => uGL X * g) '' closure (vecDomain E (Pos a)) with hKdef
  have hK : IsCompact K := isCompact_closure_vecDomain.image (continuous_uGL.mul continuous_const)
  obtain ⟨C, N, hC⟩ := hg K hK
  set f : GL (Fin a) (Cinf E) → (Pos a → Ad E) → ℂ := fun y X =>
    F (uGL X * (g * infGL E a y)) * (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ) with hfdef
  have hwf : ∀ y, whit F (g * infGL E a y) = ∫ X in vecDomain E (Pos a), f y X ∂vecMeasure E (Pos a) :=
    fun y => rfl
  have hb : ∀ y, ∀ X ∈ vecDomain E (Pos a), ‖f y X‖ ≤ C * height y ^ N := by
    intro y X hX
    simp only [hfdef]
    rw [norm_mul, Circle.norm_coe, mul_one, ← mul_assoc]
    exact hC _ ⟨X, subset_closure hX, rfl⟩ y
  have hbound : ∀ y, ‖whit F (g * infGL E a y)‖ ≤ C * height y ^ N := by
    intro y
    have h := norm_setIntegral_le_of_norm_le_const (μ := vecMeasure E (Pos a)) (s := vecDomain E (Pos a))
      (C := C * height y ^ N) (f := f y) (by rw [vecMeasure_vecDomain]; exact ENNReal.one_lt_top) (hb y)
    rwa [measureReal_def, vecMeasure_vecDomain, ENNReal.toReal_one, mul_one, ← hwf] at h
  refine ⟨?_, C, N, hbound⟩
  haveI : IsFiniteMeasure ((vecMeasure E (Pos a)).restrict (vecDomain E (Pos a))) :=
    ⟨by rw [Measure.restrict_apply_univ, vecMeasure_vecDomain]; exact ENNReal.one_lt_top⟩
  have hchar : Continuous fun X : Pos a → Ad E => (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ) :=
    continuous_subtype_val.comp (GroundTheory.Global.continuous_adelicChar.comp (continuous_supSum 0).neg)
  have hfc : ∀ y, Continuous (f y) := fun y =>
    (hc.comp (continuous_uGL.mul continuous_const)).mul hchar
  haveI : FirstCountableTopology (MulOpposite (Matrix (Fin a) (Fin a) (Cinf E))) :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin a) (Fin a) (Cinf E))).symm.isInducing.firstCountableTopology
  haveI : FirstCountableTopology (GL (Fin a) (Cinf E)) :=
    Units.isEmbedding_embedProduct.isInducing.firstCountableTopology
  rw [continuous_iff_continuousAt]
  intro y₀
  have hev : ∀ᶠ y in 𝓝 y₀, height y < height y₀ + 1 :=
    continuous_heightInf.continuousAt.eventually (gt_mem_nhds (lt_add_one _))
  simp only [hwf]
  refine continuousAt_of_dominated (bound := fun _ => max C 0 * (height y₀ + 1) ^ N) ?_ ?_ (integrable_const _) ?_
  · exact Filter.Eventually.of_forall fun y => (hfc y).aestronglyMeasurable
  · filter_upwards [hev] with y hy
    refine ae_restrict_of_forall_mem measurableSet_vecDomain fun X hX => ?_
    calc ‖f y X‖ ≤ C * height y ^ N := hb y X hX
      _ ≤ max C 0 * height y ^ N :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (height_pos_inf y).le _)
      _ ≤ max C 0 * (height y₀ + 1) ^ N :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (height_pos_inf y).le hy.le _) (le_max_right _ _)
  · refine Filter.Eventually.of_forall fun X => ?_
    have : Continuous fun y : GL (Fin a) (Cinf E) => f y X :=
      (hc.comp (continuous_const.mul (continuous_const.mul GlobalTheory.ConstTermSmooth.continuous_infGL))).mul
        continuous_const
    exact this.continuousAt

end GlobalTheory.JSW.MirSemi


open GlobalTheory.JSW.MirSemi in
theorem GlobalTheory.JSW.MirSemi.whitSpace_exists : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (π : CuspSub E (m + 1)) (φ : Sm E (m + 1)), φ ∈ π.V → ∃ 𝒲 : Submodule ℂ (GA E (m + 1) → ℂ), GlobalTheory.JSW.whit φ.1 ∈ 𝒲 ∧ (∀ W ∈ 𝒲, ∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) ∧ (∀ W ∈ 𝒲, ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, (fun g => W (g * h)) ∈ 𝒲) ∧ (∀ W ∈ 𝒲, ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ) (γ : X → GL (Fin (m + 1)) (Cinf E)), GlobalTheory.JSW.IsRapidInf ν k γ → GlobalTheory.JSW.kerInf ν k γ W ∈ 𝒲) ∧ (∀ W ∈ 𝒲, ∀ g, Continuous (fun y : GL (Fin (m + 1)) (Cinf E) => W (g * infGL E (m + 1) y)) ∧ ∃ (C : ℝ) (N : ℕ), ∀ y, ‖W (g * infGL E (m + 1) y)‖ ≤ C * height y ^ N) ∧ (∀ W ∈ 𝒲, ∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, W (g * finGL E (m + 1) u) = W g) ∧ ∀ W ∈ 𝒲, ∃ F ∈ GlobalTheory.JSW.MirSemi.locSpan S φ.1, ∀ g, GlobalTheory.JSW.whit F g = W g := by
  intro E _ _ _ m S π φ hφ
  have hreg := GlobalTheory.T.cusp_form_moderate_growth_compact E (m + 1) S π φ hφ
  let 𝒲 : Submodule ℂ (GA E (m + 1) → ℂ) :=
    { carrier := {W | ∃ F ∈ locSpan S φ.1, GlobalTheory.JSW.whit F = W}
      add_mem' := by
        rintro _ _ ⟨F, hF, rfl⟩ ⟨G, hG, rfl⟩
        refine ⟨F + G, add_mem hF hG, funext fun g => ?_⟩
        have h := ((GlobalTheory.T.globalWhittakerCoefficient_linear_archimedeanKernel E (m + 1) F G (hreg F hF).1 (hreg G hG).1 (hreg F hF).2 (hreg G hG).2).1 1 g)
        simp only [one_mul] at h
        exact h
      zero_mem' := ⟨0, zero_mem _, funext fun g => by
        simpa using whit_smul_fun (0 : ℂ) (0 : GA E (m + 1) → ℂ) g⟩
      smul_mem' := by
        rintro c _ ⟨F, hF, rfl⟩
        exact ⟨c • F, Submodule.smul_mem _ c hF, funext fun g => whit_smul_fun c F g⟩ }
  refine ⟨𝒲, ⟨φ.1, self_mem_locSpan, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨F, hF, rfl⟩ u hu g
    exact GlobalTheory.JSW.WhitModel.whit_mul (hreg F hF).1
      (fun γ g => GlobalTheory.JSW.rspan_left π (locSpan_le_rspan hφ hF) γ g) hu g
  · rintro _ ⟨F, hF, rfl⟩ h hh
    exact ⟨_, rt_mem_locSpan hF hh, funext fun g => (whit_mul_right_fun F g h).symm⟩
  · rintro _ ⟨F, hF, rfl⟩ X _ ν _ k γ hk
    refine ⟨GlobalTheory.JSW.kerInf ν k γ F, kerInf_mem_locSpan hF ν hk, funext fun g => ?_⟩
    rw [(GlobalTheory.T.globalWhittakerCoefficient_linear_archimedeanKernel E (m + 1) F F (hreg F hF).1 (hreg F hF).1 (hreg F hF).2 (hreg F hF).2).2 X ν k γ hk g]
    rfl
  · rintro _ ⟨F, hF, rfl⟩ g
    exact whit_infGL_growth (hreg F hF).1 (hreg F hF).2 g
  · rintro _ ⟨F, hF, rfl⟩
    obtain ⟨U, hU, hinv⟩ := GlobalTheory.T.archimedeanKernelSpan_cuspForm_right_invariant_open E (m + 1) S π φ hφ F hF
    refine ⟨U, hU, fun u hu g => ?_⟩
    rw [whit_mul_right_fun]
    congr 1
    funext z
    exact hinv u hu z
  · rintro _ ⟨F, hF, rfl⟩
    exact ⟨F, hF, fun g => rfl⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspFormSemiLocalWhittakerSpaceStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cusp_form_semi_local_whittaker_space : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (π : CuspSub E (m + 1)) (φ : Sm E (m + 1)), φ ∈ π.V → ∃ 𝒲 : Submodule ℂ (GA E (m + 1) → ℂ), GlobalTheory.JSW.whit φ.1 ∈ 𝒲 ∧ (∀ W ∈ 𝒲, ∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) ∧ (∀ W ∈ 𝒲, ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, (fun g => W (g * h)) ∈ 𝒲) ∧ (∀ W ∈ 𝒲, ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ) (γ : X → GL (Fin (m + 1)) (Cinf E)), GlobalTheory.JSW.IsRapidInf ν k γ → GlobalTheory.JSW.kerInf ν k γ W ∈ 𝒲) ∧ (∀ W ∈ 𝒲, ∀ g, Continuous (fun y : GL (Fin (m + 1)) (Cinf E) => W (g * infGL E (m + 1) y)) ∧ ∃ (C : ℝ) (N : ℕ), ∀ y, ‖W (g * infGL E (m + 1) y)‖ ≤ C * height y ^ N) ∧ (∀ W ∈ 𝒲, ∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, W (g * finGL E (m + 1) u) = W g) ∧ ∀ W ∈ 𝒲, ∃ F ∈ GlobalTheory.JSW.MirSemi.locSpan S φ.1, ∀ g, GlobalTheory.JSW.whit F g = W g := by
  first | exact @GlobalTheory.JSW.MirSemi.whitSpace_exists | exact GlobalTheory.JSW.MirSemi.whitSpace_exists | (intros; apply GlobalTheory.JSW.MirSemi.whitSpace_exists <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiLocalSpanRightInvariantOfTrivialInfinityFins
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiLocalSpanRightInvariantOfTrivialInfinityFins
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

namespace GlobalTheory.JSW.MirSemi

theorem infGL_mem_supS {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    (S : Finset (HeightOneSpectrum (𝓞 E))) (y : GL (Fin a) (Cinf E)) : infGL E a y ∈ GlobalTheory.JSW.supS (E := E) (a := a) S := by
  intro w _
  have h := pFin_infGL (E := E) (a := a) y
  ext i j
  have := congrArg (fun z : GL (Fin a) (Af E) => (pLoc E w) ((z : Matrix (Fin a) (Fin a) (Af E)) i j)) h
  simpa [Matrix.one_apply, apply_ite] using this

theorem locSpan_rightInv : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (F₀ : GA E a → ℂ) (k : GA E a),
    GeneralLinearGroup.map (pInf E) k = 1 → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) k = 1) →
    (∀ g, F₀ (g * k) = F₀ g) → ∀ F ∈ GlobalTheory.JSW.MirSemi.locSpan S F₀, ∀ g, F (g * k) = F g := by
  intro E _ _ _ a S F₀ k hInf hS hF₀
  let V : Submodule ℂ (GA E a → ℂ) :=
    { carrier := {F | ∀ g, F (g * k) = F g}
      add_mem' := fun {F G} hF hG g => by simp only [Pi.add_apply, hF g, hG g]
      zero_mem' := fun _ => rfl
      smul_mem' := fun c F hF g => by simp only [Pi.smul_apply, hF g] }
  have hc : ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := a) S, h * k = k * h := fun h hh => GlobalTheory.T.adelicGL_complementary_supports_commute E a S h k hh hInf hS
  refine fun F hF => (locSpan_le (V := V) hF₀ ?_ ?_) hF
  · intro F hF h hh g
    show F (g * k * h) = F (g * h)
    rw [mul_assoc, ← hc h hh, ← mul_assoc, hF]
  · intro F hF X _ ν _ k' γ _ g
    show GlobalTheory.JSW.kerInf ν k' γ F (g * k) = GlobalTheory.JSW.kerInf ν k' γ F g
    unfold GlobalTheory.JSW.kerInf
    congr 1
    funext x
    rw [mul_assoc, ← hc _ (infGL_mem_supS S (γ x)), ← mul_assoc, hF]

end GlobalTheory.JSW.MirSemi
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiLocalSpanRightInvariantOfTrivialInfinityFinsStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiLocalSpan_rightInvariant_of_trivial_infinity_finset : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (F₀ : GA E a → ℂ) (k : GA E a), GeneralLinearGroup.map (pInf E) k = 1 → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) k = 1) → (∀ g, F₀ (g * k) = F₀ g) → ∀ F ∈ GlobalTheory.JSW.MirSemi.locSpan S F₀, ∀ g, F (g * k) = F g := by
  first | exact @GlobalTheory.JSW.MirSemi.locSpan_rightInv | exact GlobalTheory.JSW.MirSemi.locSpan_rightInv | (intros; apply GlobalTheory.JSW.MirSemi.locSpan_rightInv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KirillovSemilocalMirabolicWhittaker
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix

namespace GlobalTheory.JSW.MirSemi

theorem kirillov_semilocal : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (b : GA E (m + 1) → ℂ), (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) → (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), b p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * p ∈ C) → (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, b (g * finGL E (m + 1) u) = b g) → (∀ g, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (chart b g) (invSet E (m + 1))) → ∀ (π : CuspSub E (m + 1)) (φ : Sm E (m + 1)), φ ∈ π.V → (∃ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), GlobalTheory.JSW.whit φ.1 p ≠ 0) → ∃ F ∈ GlobalTheory.JSW.mspanR π, (∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), GlobalTheory.JSW.whit F p = b p) ∧ (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, F (g * finGL E (m + 1) u) = F g) ∧ (∀ k : GA E (m + 1), GeneralLinearGroup.map (pInf E) k = 1 → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) k = 1) → (∀ g, φ.1 (g * k) = φ.1 g) → ∀ g, F (g * k) = F g) ∧ ∀ (t : GA E (m + 1)) (c : ℂ), GeneralLinearGroup.map (pInf E) t = 1 → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) t = 1) → (∀ x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, GlobalTheory.JSW.whit φ.1 (x * t) = c * GlobalTheory.JSW.whit φ.1 x) → ∀ x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, GlobalTheory.JSW.whit F (x * t) = c * GlobalTheory.JSW.whit F x := by
  intro E _ _ _ m S b hbe hbC hbU hbs π φ hφ hnz
  obtain ⟨𝒲, hw0, h1, h2, h3, h4, h5, hback⟩ := GlobalTheory.T.exists_cusp_form_semi_local_whittaker_space E m S π φ hφ
  obtain ⟨W, hW, hWb⟩ := GlobalTheory.T.kirillov_semiLocal_mirabolic_abstract E m S b hbe hbC hbU hbs 𝒲 h1 h2 h3 h4 h5 ⟨_, hw0, hnz⟩
  obtain ⟨F, hF, hFW⟩ := hback W hW
  exact ⟨F, locSpan_le_mspanR hφ hF, fun p hp => by rw [hFW, hWb p hp],
    GlobalTheory.T.archimedeanKernelSpan_cuspForm_right_invariant_open E (m + 1) S π φ hφ F hF, fun k hk1 hk2 hk3 => GlobalTheory.T.semiLocalSpan_rightInvariant_of_trivial_infinity_finset E (m + 1) S φ.1 k hk1 hk2 hk3 F hF,
    fun t c ht1 ht2 ht3 => GlobalTheory.T.whittaker_relation_passes_to_semi_local_span E (m + 1) S π φ hφ t c ht1 ht2 ht3 F hF⟩

end GlobalTheory.JSW.MirSemi
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KirillovSemilocalMirabolicWhittakerStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kirillov_semilocal_mirabolic_whittaker : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (b : GA E (m + 1) → ℂ), (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) → (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), b p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * p ∈ C) → (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, b (g * finGL E (m + 1) u) = b g) → (∀ g, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (chart b g) (invSet E (m + 1))) → ∀ (π : CuspSub E (m + 1)) (φ : Sm E (m + 1)), φ ∈ π.V → (∃ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), GlobalTheory.JSW.whit φ.1 p ≠ 0) → ∃ F ∈ GlobalTheory.JSW.mspanR π, (∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), GlobalTheory.JSW.whit F p = b p) ∧ (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, F (g * finGL E (m + 1) u) = F g) ∧ (∀ k : GA E (m + 1), GeneralLinearGroup.map (pInf E) k = 1 → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) k = 1) → (∀ g, φ.1 (g * k) = φ.1 g) → ∀ g, F (g * k) = F g) ∧ ∀ (t : GA E (m + 1)) (c : ℂ), GeneralLinearGroup.map (pInf E) t = 1 → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) t = 1) → (∀ x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, GlobalTheory.JSW.whit φ.1 (x * t) = c * GlobalTheory.JSW.whit φ.1 x) → ∀ x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, GlobalTheory.JSW.whit F (x * t) = c * GlobalTheory.JSW.whit F x := by
  first | (exact @GlobalTheory.JSW.MirSemi.kirillov_semilocal) | (exact GlobalTheory.JSW.MirSemi.kirillov_semilocal) | (intros; apply GlobalTheory.JSW.MirSemi.kirillov_semilocal  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousGlobalWhittakerCoefficientArchimedean
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousGlobalWhittakerCoefficientArchimedean
open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix

namespace GlobalTheory.JSW

theorem continuous_whit_infGL : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a),
    IsAutForm φ → ∀ g h : GA E a,
      Continuous (fun y : GL (Fin a) (Cinf E) => GlobalTheory.JSW.whit φ.1 (g * infGL E a y * h)) := by
  intro E _ _ _ a φ hφ g h
  have hc : Continuous φ.1 := hφ.continuous
  have hW : Continuous (GlobalTheory.JSW.whit φ.1) := by
    have : GlobalTheory.JSW.whit φ.1 = GroundTheory.Automorphic.FourierWhittaker.partialCoeff φ.1 0 := by
      funext x
      exact GroundTheory.Automorphic.FourierWhittaker.whittaker_eq_partialCoeff_zero hc x
    rw [this]
    exact GroundTheory.Automorphic.FourierWhittaker.continuous_partialCoeff hc 0
  exact hW.comp ((continuous_const.mul GlobalTheory.ConstTermSmooth.continuous_infGL).mul continuous_const)

end GlobalTheory.JSW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousGlobalWhittakerCoefficientArchimedeanStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_globalWhittakerCoefficient_archimedean : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a), IsAutForm φ → ∀ g h : GA E a, Continuous (fun y : GL (Fin a) (Cinf E) => GlobalTheory.JSW.whit φ.1 (g * infGL E a y * h)) := by
  first | exact @GlobalTheory.JSW.continuous_whit_infGL | exact GlobalTheory.JSW.continuous_whit_infGL | (intros; apply GlobalTheory.JSW.continuous_whit_infGL <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMirabolicScalarUnitaryDecompositionArchime
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMirabolicScalarUnitaryDecompositionArchime
open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix

namespace GlobalTheory.IwasawaLast

theorem exists_unitary_lastRow {n : ℕ} (ℓ : Fin (n + 1) → ℂ) (hℓ : ℓ ≠ 0) :
    ∃ r : ℂ, r ≠ 0 ∧ ∃ k ∈ unitaryGroup (Fin (n + 1)) ℂ, ∀ l, ℓ l = r * k (Fin.last n) l := by
  set x : EuclideanSpace ℂ (Fin (n + 1)) := WithLp.toLp 2 (star ℓ) with hx
  have hx0 : x ≠ 0 := by
    intro h
    apply hℓ
    have : star ℓ = 0 := by
      have := congrArg WithLp.ofLp h
      simpa [hx] using this
    simpa using congrArg star this
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx0
  set w : EuclideanSpace ℂ (Fin (n + 1)) := ((‖x‖ : ℂ)⁻¹) • x with hw
  have hw1 : ‖w‖ = 1 := by
    rw [hw, norm_smul]
    simp [hn]
  have hon : Orthonormal ℂ (({Fin.last n} : Set (Fin (n + 1))).domRestrict (fun _ => w)) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    simp only [Set.mem_singleton_iff] at hi hj
    subst hi; subst hj
    simp [Set.domRestrict, inner_self_eq_norm_sq_to_K, hw1]
  obtain ⟨b, hb⟩ := hon.exists_orthonormalBasis_extension_of_card_eq (by simp)
  have hbl : b (Fin.last n) = w := hb _ (Set.mem_singleton _)
  set M := (EuclideanSpace.basisFun (Fin (n + 1)) ℂ).toBasis.toMatrix b with hM
  have hMu : M ∈ unitaryGroup (Fin (n + 1)) ℂ :=
    OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary _ _
  refine ⟨(‖x‖ : ℂ), by exact_mod_cast hn, star M, ?_, ?_⟩
  · exact Unitary.star_mem hMu
  · intro l
    simp [hM, Matrix.star_apply, Module.Basis.toMatrix_apply, hbl, hw, hx]
    have hn' : ((‖WithLp.toLp 2 (star ℓ)‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn
    rw [← mul_assoc, mul_inv_cancel₀ hn', one_mul]

end GlobalTheory.IwasawaLast

namespace GlobalTheory.IwasawaLast

theorem iwasawa_lastRow : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (y : GL (Fin (m + 1)) (Cinf E)), ∃ (p : GL (Fin (m + 1)) (Cinf E)) (ρ : (Cinf E)ˣ) (k : Kinf E (m + 1)), (∀ j, (p : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) (Fin.last m) j = if j = Fin.last m then 1 else 0) ∧ y = p * Units.map (Matrix.scalar (Fin (m + 1)) : Cinf E →+* Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)).toMonoidHom ρ * Unitary.toUnits k := by
  intro E _ _ _ m y
  set Y : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E) := (y : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) with hY
  set ℓ : InfinitePlace E → Fin (m + 1) → ℂ := fun v j => Y (Fin.last m) j v with hℓdef
  have hne : ∀ v, ℓ v ≠ 0 := by
    intro v h
    have hdet : IsUnit Y.det := (Matrix.isUnit_iff_isUnit_det Y).mp (Units.isUnit y)
    have hv : IsUnit (Y.det v) := (Pi.isUnit_iff.mp hdet) v
    have hmap : Y.det v = ((Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) v).mapMatrix Y).det :=
      RingHom.map_det (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) v) Y
    have h0 : ((Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) v).mapMatrix Y).det = 0 :=
      Matrix.det_eq_zero_of_row_eq_zero (Fin.last m) (fun j => by
        simpa [hℓdef] using congrFun h j)
    rw [hmap, h0] at hv
    exact not_isUnit_zero hv
  choose r hr kv hkv hℓ using fun v => exists_unitary_lastRow (ℓ v) (hne v)
  set K : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E) := Matrix.of fun i j v => kv v i j with hKdef
  have hK : K ∈ unitaryGroup (Fin (m + 1)) (Cinf E) := by
    rw [mem_unitaryGroup_iff]
    ext i j v
    have := congrFun (congrFun (mem_unitaryGroup_iff.mp (hkv v)) i) j
    by_cases hij : i = j <;> simp [hKdef, Matrix.mul_apply, Finset.sum_apply, Matrix.star_apply, Matrix.one_apply, hij] at this ⊢ <;> exact this
  have hρ : IsUnit (fun v => r v : Cinf E) := Pi.isUnit_iff.mpr fun v => (hr v).isUnit
  refine ⟨y * (Unitary.toUnits (⟨K, hK⟩ : Kinf E (m + 1)))⁻¹ *
      (Units.map (Matrix.scalar (Fin (m + 1)) : Cinf E →+* Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)).toMonoidHom hρ.unit)⁻¹,
    hρ.unit, ⟨K, hK⟩, ?_, by group⟩
  intro j
  ext v
  have hinv : (((Unitary.toUnits (⟨K, hK⟩ : Kinf E (m + 1)))⁻¹ : GL (Fin (m + 1)) (Cinf E)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) = star K := rfl
  have hρv : ((hρ.unit⁻¹ : (Cinf E)ˣ) : Cinf E) v = (r v)⁻¹ := by
    have h1 := congrFun hρ.unit.inv_mul v
    simp only [Units.val_mul, Pi.mul_apply, IsUnit.unit_spec, Units.val_one, Pi.one_apply] at h1
    exact eq_inv_of_mul_eq_one_left h1
  have hrow : ∀ l, Y (Fin.last m) l v = r v * kv v (Fin.last m) l := fun l => hℓ v l
  have hu := congrFun (congrFun (mem_unitaryGroup_iff.mp (hkv v)) (Fin.last m)) j
  simp only [Units.val_mul, Units.coe_map_inv, MonoidHom.coe_coe, hinv]
  rw [← hY]
  show (Y * star K * Matrix.scalar (Fin (m + 1)) ((hρ.unit⁻¹ : (Cinf E)ˣ) : Cinf E)) (Fin.last m) j v = _
  rw [Matrix.scalar_apply, Matrix.mul_diagonal]
  simp only [Matrix.scalar_apply, Matrix.mul_diagonal, Pi.mul_apply, hρv, Matrix.mul_apply, Finset.sum_apply, hrow, Matrix.star_apply, Pi.star_apply, hKdef, Matrix.of_apply] at hu ⊢
  have hs : ∑ x, r v * kv v (Fin.last m) x * star (kv v j x) = r v * ∑ x, kv v (Fin.last m) x * star (kv v j x) := by
    rw [Finset.mul_sum]; simp [mul_assoc]
  rw [hs, hu, Matrix.one_apply]
  by_cases hj : j = Fin.last m
  · subst hj; simp [hr v]
  · simp [hj, Ne.symm hj]

end GlobalTheory.IwasawaLast
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMirabolicScalarUnitaryDecompositionArchimeStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mirabolic_scalar_unitary_decomposition_archimedean : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (y : GL (Fin (m + 1)) (Cinf E)), ∃ (p : GL (Fin (m + 1)) (Cinf E)) (ρ : (Cinf E)ˣ) (k : Kinf E (m + 1)), (∀ j, (p : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) (Fin.last m) j = if j = Fin.last m then 1 else 0) ∧ y = p * Units.map (Matrix.scalar (Fin (m + 1)) : Cinf E →+* Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)).toMonoidHom ρ * Unitary.toUnits k := by
  first | exact @GlobalTheory.IwasawaLast.iwasawa_lastRow | exact GlobalTheory.IwasawaLast.iwasawa_lastRow | (intros; apply GlobalTheory.IwasawaLast.iwasawa_lastRow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFieldUnitMemOpenArchimedeanUnits
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFieldUnitMemOpenArchimedeanUnits
open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix

namespace GlobalTheory.UnitsDense

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem denseRange_embeddings' : DenseRange fun (x : E) (w : InfinitePlace E) => w.embedding x := by
  have h1 := NumberField.InfiniteAdeleRing.denseRange_algebraMap E
  have hs : Function.Surjective
      (Pi.map fun w : InfinitePlace E => InfinitePlace.Completion.extensionEmbedding w) := by
    intro y
    choose x hx using fun w : InfinitePlace E =>
      InfinitePlace.Completion.surjective_extensionEmbedding_of_isComplex (IsTotallyComplex.isComplex w) (y w)
    exact ⟨x, funext hx⟩
  have hc : Continuous (Pi.map fun w : InfinitePlace E => InfinitePlace.Completion.extensionEmbedding w) :=
    continuous_pi fun w => (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp (continuous_apply w)
  have := hs.denseRange.comp h1 hc
  convert this using 1
  funext x w
  change w.embedding x = InfinitePlace.Completion.extensionEmbedding w (algebraMap E (InfiniteAdeleRing E) x w)
  rw [InfiniteAdeleRing.algebraMap_apply]
  have := InfinitePlace.Completion.extensionEmbedding_coe (v := w) ((WithAbs.equiv w.1).symm x)
  simp only [RingEquiv.apply_symm_apply] at this
  rw [← this]
  rfl

theorem exists_unit_mem_open :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (V : Set (Cinf E)ˣ), IsOpen V → V.Nonempty →
      ∃ α : Eˣ, Units.map ((pInf E).comp (algebraMap E (Ad E))).toMonoidHom α ∈ V := by
  intro E _ _ _ V hV ⟨v, hv⟩
  have hU : IsOpen (Units.val '' V) := Units.isOpenEmbedding_val.isOpenMap V hV
  have hd : DenseRange fun x : E => pInf E (algebraMap E (Ad E) x) := by
    have : (fun x : E => pInf E (algebraMap E (Ad E) x)) = fun (x : E) (w : InfinitePlace E) => w.embedding x := by
      funext x w; exact pInf_algebraMap x w
    rw [this]; exact denseRange_embeddings'
  obtain ⟨x, u, hu, hxu⟩ := hd.exists_mem_open hU ⟨v.1, v, hv, rfl⟩
  have hx : x ≠ 0 := by
    rintro rfl
    simp only [map_zero] at hxu
    haveI : Nonempty (InfinitePlace E) := inferInstance
    exact u.ne_zero hxu
  refine ⟨Units.mk0 x hx, ?_⟩
  convert hu using 1
  ext
  simp [hxu]

end GlobalTheory.UnitsDense
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFieldUnitMemOpenArchimedeanUnitsStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_field_unit_mem_open_archimedean_units : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (V : Set (Cinf E)ˣ), IsOpen V → V.Nonempty → ∃ α : Eˣ, Units.map ((pInf E).comp (algebraMap E (Ad E))).toMonoidHom α ∈ V := by
  first | exact @GlobalTheory.UnitsDense.exists_unit_mem_open | exact GlobalTheory.UnitsDense.exists_unit_mem_open | (intros; apply GlobalTheory.UnitsDense.exists_unit_mem_open <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KirillovSemilocalSmoothBump
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix
open scoped ContDiff

namespace GlobalTheory.JSW.KirSemi

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem gl_af_ext {g h : GL (Fin a) (Af E)}
    (H : ∀ w, GeneralLinearGroup.map (pLoc E w) g = GeneralLinearGroup.map (pLoc E w) h) : g = h := by
  refine Units.ext (Matrix.ext fun i j => Subtype.ext (funext fun w => ?_))
  exact congrArg (fun x : GL (Fin a) (w.adicCompletion E) => x.1 i j) (H w)

theorem map_loc_fin (w : HeightOneSpectrum (𝓞 E)) (g : GA E a) :
    GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) g) =
      GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) g := by
  ext; rfl

theorem comm_of_supp (S : Finset (HeightOneSpectrum (𝓞 E))) {s t : GA E a} (hs : s ∈ supS (E := E) (a := a) S)
    (h1 : GeneralLinearGroup.map (pInf E) t = 1)
    (h2 : ∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) t = 1) : s * t = t * s := by
  apply ga_ext
  · simp [map_mul, h1]
  · apply gl_af_ext
    intro w
    simp only [map_mul, map_loc_fin]
    by_cases hw : w ∈ S
    · rw [h2 w hw]; simp
    · rw [hs w hw]; simp

theorem supS_mul (S : Finset (HeightOneSpectrum (𝓞 E))) {x y : GA E a} (hx : x ∈ supS (E := E) (a := a) S)
    (hy : y ∈ supS (E := E) (a := a) S) : x * y ∈ supS (E := E) (a := a) S := by
  intro w hw
  rw [map_mul, hx w hw, hy w hw, one_mul]

theorem whit_rt (F : GA E a → ℂ) (h g : GA E a) : whit (fun y => F (y * h)) g = whit F (g * h) := by
  simp only [whit, GroundTheory.Automorphic.FourierWhittaker.whittaker, mul_assoc]

theorem ratGL_scalar_val (α : Eˣ) :
    ((ratGL E a (Units.map (Matrix.scalar (Fin a) : E →+* Matrix (Fin a) (Fin a) E).toMonoidHom α) : GA E a) :
      Matrix (Fin a) (Fin a) (Ad E)) = Matrix.scalar (Fin a) (algebraMap E (Ad E) (α : E)) := by
  ext i j
  by_cases h : i = j <;> simp [ratGL, Matrix.scalar_apply, Matrix.diagonal_apply, h]

theorem aut_central {φ : Sm E a} (hφ : IsAutForm φ) (α : Eˣ) (g : GA E a) :
    φ.1 (g * ratGL E a (Units.map (Matrix.scalar (Fin a) : E →+* Matrix (Fin a) (Fin a) E).toMonoidHom α)) = φ.1 g := by
  have hc : g * ratGL E a (Units.map (Matrix.scalar (Fin a) : E →+* Matrix (Fin a) (Fin a) E).toMonoidHom α) =
      ratGL E a (Units.map (Matrix.scalar (Fin a) : E →+* Matrix (Fin a) (Fin a) E).toMonoidHom α) * g := by
    apply Units.ext
    simp only [Units.val_mul, ratGL_scalar_val]
    exact ((Matrix.scalar_commute _ (fun r => Commute.all _ r) _)).symm
  rw [hc, hφ.left]

theorem exists_mirabolic_nonzero : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (π : CuspSub E (m + 1)) (φ : Sm E (m + 1)), φ ∈ π.V → (∃ x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, GlobalTheory.JSW.whit φ.1 x ≠ 0) → ∃ ψ ∈ π.V, (∃ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), GlobalTheory.JSW.whit ψ.1 p ≠ 0) ∧ (∀ k : GA E (m + 1), GeneralLinearGroup.map (pInf E) k = 1 → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) k = 1) → (∀ g, φ.1 (g * k) = φ.1 g) → ∀ g, ψ.1 (g * k) = ψ.1 g) ∧ ∀ (t : GA E (m + 1)) (c : ℂ), GeneralLinearGroup.map (pInf E) t = 1 → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) t = 1) → (∀ x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, GlobalTheory.JSW.whit φ.1 (x * t) = c * GlobalTheory.JSW.whit φ.1 x) → ∀ x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, GlobalTheory.JSW.whit ψ.1 (x * t) = c * GlobalTheory.JSW.whit ψ.1 x := by
  intro E _ _ _ m S π φ hφ ⟨x, hxS, hx⟩
  have haut : IsAutForm φ := (π.cusp φ hφ).1
  set xf := GeneralLinearGroup.map (pFin E) x with hxf
  obtain ⟨p0, ρ, k, hp0, hy⟩ := GlobalTheory.T.exists_mirabolic_scalar_unitary_decomposition_archimedean E m (GeneralLinearGroup.map (pInf E) x)
  let sc : (Cinf E)ˣ →* GL (Fin (m + 1)) (Cinf E) :=
    Units.map (Matrix.scalar (Fin (m + 1)) : Cinf E →+* Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)).toMonoidHom
  have hsc : Continuous sc := by
    apply Continuous.units_map
    show Continuous (fun c : Cinf E => Matrix.scalar (Fin (m + 1)) c)
    simp only [Matrix.scalar_apply]
    exact Continuous.matrix_diagonal (continuous_pi fun _ => continuous_id)
  let ζ : (Cinf E)ˣ → ℂ := fun c =>
    whit φ.1 (infGL E (m + 1) p0 * infGL E (m + 1) (sc c * Unitary.toUnits k) * finGL E (m + 1) xf)
  have hζc : Continuous ζ :=
    (GlobalTheory.T.continuous_globalWhittakerCoefficient_archimedean E (m + 1) φ haut _ _).comp (hsc.mul continuous_const)
  have hζρ : ζ ρ ≠ 0 := by
    have hx' : infGL E (m + 1) p0 * infGL E (m + 1) (sc ρ * Unitary.toUnits k) * finGL E (m + 1) xf = x := by
      rw [← map_mul, ← mul_assoc]
      rw [show p0 * sc ρ * Unitary.toUnits k = GeneralLinearGroup.map (pInf E) x from hy.symm]
      exact infGL_mul_finGL x
    show whit φ.1 _ ≠ 0
    rw [hx']
    exact hx
  obtain ⟨β, hβ⟩ := GlobalTheory.T.exists_field_unit_mem_open_archimedean_units E {c | ζ c ≠ 0} (isOpen_ne_fun hζc continuous_const) ⟨ρ, hζρ⟩
  set c := Units.map ((pInf E).comp (algebraMap E (Ad E))).toMonoidHom β with hc
  let zE : GL (Fin (m + 1)) E := Units.map (Matrix.scalar (Fin (m + 1)) : E →+* Matrix (Fin (m + 1)) (Fin (m + 1)) E).toMonoidHom β⁻¹
  set s := infGL E (m + 1) (sc c * Unitary.toUnits k) * finGL E (m + 1) xf with hs
  have hcen : ∀ g : GL (Fin (m + 1)) (Cinf E), sc c * g = g * sc c := by
    intro g
    apply Units.ext
    exact Matrix.scalar_commute _ (fun r => Commute.all _ r) _
  have hzinf : GeneralLinearGroup.map (pInf E) (ratGL E (m + 1) zE) = (sc c)⁻¹ := by
    have hci : (sc c)⁻¹ = sc (Units.map ((pInf E).comp (algebraMap E (Ad E))).toMonoidHom β⁻¹) := by
      simp only [hc, map_inv]
    rw [hci]
    apply Units.ext
    show ((ratGL E (m + 1) zE : GA E (m + 1)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)).map (pInf E) =
      Matrix.scalar (Fin (m + 1)) (((Units.map ((pInf E).comp (algebraMap E (Ad E))).toMonoidHom β⁻¹ : (Cinf E)ˣ)) : Cinf E)
    rw [ratGL_scalar_val]
    simp [Matrix.scalar_apply, Matrix.diagonal_map]
    funext v
    simp [pInf_algebraMap, map_inv₀]
  set z := GeneralLinearGroup.map (pFin E) (ratGL E (m + 1) zE) with hz
  have hsz : s * ratGL E (m + 1) zE = infGL E (m + 1) (Unitary.toUnits k) * finGL E (m + 1) (xf * z) := by
    apply ga_ext
    · simp only [hs, map_mul, pInf_infGL, hzinf]
      simp
      rw [hcen]; group
    · simp [hs, hz, mul_assoc]
  let ψ : Sm E (m + 1) := act (Op.cpt k) (act (Op.fin (xf * z)) φ)
  have hψV : ψ ∈ π.V := π.stable _ _ (π.stable _ _ hφ)
  have hψ : ∀ g, ψ.1 g = φ.1 (g * s) := by
    intro g
    have h0 : ψ.1 g = φ.1 (g * infGL E (m + 1) (Unitary.toUnits k) * finGL E (m + 1) (xf * z)) := rfl
    rw [h0, mul_assoc, ← hsz, ← mul_assoc, aut_central haut β⁻¹]
  have hψf : ψ.1 = fun g => φ.1 (g * s) := funext hψ
  have hsS : s ∈ supS (E := E) (a := (m + 1)) S := by
    intro w hw
    rw [← map_loc_fin, hs, map_mul, pFin_infGL, pFin_finGL, one_mul, hxf, map_loc_fin]
    exact hxS w hw
  refine ⟨ψ, hψV, ⟨infGL E (m + 1) p0, ⟨?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · intro w hw
    rw [← map_loc_fin]
    simp
  · intro j
    have h1 : pInf E (((infGL E (m + 1) p0 : GA E (m + 1)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j) =
        (p0 : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) (Fin.last m) j :=
      congrArg (fun y : GL (Fin (m + 1)) (Cinf E) => (y : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) (Fin.last m) j)
        (pInf_infGL (E := E) p0)
    have h2 : pFin E (((infGL E (m + 1) p0 : GA E (m + 1)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j) =
        ((1 : GL (Fin (m + 1)) (Af E)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Af E)) (Fin.last m) j :=
      congrArg (fun y : GL (Fin (m + 1)) (Af E) => (y : Matrix (Fin (m + 1)) (Fin (m + 1)) (Af E)) (Fin.last m) j)
        (pFin_infGL (E := E) p0)
    rw [hp0 j] at h1
    apply ad_ext
    · rw [h1]; split_ifs <;> simp
    · rw [h2]; split_ifs with h <;> simp [Matrix.one_apply, h, eq_comm]
  · rw [hψf, whit_rt]
    have : infGL E (m + 1) p0 * s = infGL E (m + 1) p0 * infGL E (m + 1) (sc c * Unitary.toUnits k) * finGL E (m + 1) xf := by
      rw [hs, mul_assoc]
    rw [this]
    exact hβ
  · intro k' h1 h2 hk g
    rw [hψ, hψ, mul_assoc, ← comm_of_supp S hsS h1 h2, ← mul_assoc, hk]
  · intro t c' h1 h2 hrel y hy
    rw [hψf, whit_rt, whit_rt, mul_assoc, ← comm_of_supp S hsS h1 h2, ← mul_assoc]
    exact hrel (y * s) (supS_mul S hy hsS)

theorem kirillov_semilocal_bump : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (b : GA E (m + 1) → ℂ), (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) → (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), b p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * p ∈ C) → (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, b (g * finGL E (m + 1) u) = b g) → (∀ g, ContDiffOn ℝ ∞ (chart b g) (invSet E (m + 1))) → ∀ (π : CuspSub E (m + 1)) (φ : Sm E (m + 1)), φ ∈ π.V → (∃ x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, GlobalTheory.JSW.whit φ.1 x ≠ 0) → ∃ F ∈ GlobalTheory.JSW.mspanR π, (∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), GlobalTheory.JSW.whit F p = b p) ∧ (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, F (g * finGL E (m + 1) u) = F g) ∧ (∀ t : GA E (m + 1), GeneralLinearGroup.map (pInf E) t = 1 → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) t = 1) → (∀ g, φ.1 (g * t) = φ.1 g) → ∀ g, F (g * t) = F g) ∧ ∀ (t : GA E (m + 1)) (c : ℂ), GeneralLinearGroup.map (pInf E) t = 1 → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) t = 1) → (∀ x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, GlobalTheory.JSW.whit φ.1 (x * t) = c * GlobalTheory.JSW.whit φ.1 x) → ∀ x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, GlobalTheory.JSW.whit F (x * t) = c * GlobalTheory.JSW.whit F x := by
  intro E _ _ _ m S b hb hC hU hsm π φ hφ hx
  obtain ⟨ψ, hψ, hp, hk, hrel⟩ := exists_mirabolic_nonzero E m S π φ hφ hx
  obtain ⟨F, hF, hFb, hFU, hFk, hFrel⟩ := GlobalTheory.T.kirillov_semilocal_mirabolic_whittaker E m S b hb hC hU hsm π ψ hψ hp
  exact ⟨F, hF, hFb, hFU, fun k h1 h2 h3 => hFk k h1 h2 (hk k h1 h2 h3),
    fun t c h1 h2 h3 => hFrel t c h1 h2 (hrel t c h1 h2 h3)⟩

end GlobalTheory.JSW.KirSemi
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KirillovSemilocalSmoothBumpStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kirillov_semilocal_smooth_bump : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (b : GA E (m + 1) → ℂ), (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) → (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), b p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * p ∈ C) → (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, b (g * finGL E (m + 1) u) = b g) → (∀ g, ContDiffOn ℝ ∞ (chart b g) (invSet E (m + 1))) → ∀ (π : CuspSub E (m + 1)) (φ : Sm E (m + 1)), φ ∈ π.V → (∃ x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, GlobalTheory.JSW.whit φ.1 x ≠ 0) → ∃ F ∈ GlobalTheory.JSW.mspanR π, (∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), GlobalTheory.JSW.whit F p = b p) ∧ (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, F (g * finGL E (m + 1) u) = F g) ∧ (∀ t : GA E (m + 1), GeneralLinearGroup.map (pInf E) t = 1 → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) t = 1) → (∀ g, φ.1 (g * t) = φ.1 g) → ∀ g, F (g * t) = F g) ∧ ∀ (t : GA E (m + 1)) (c : ℂ), GeneralLinearGroup.map (pInf E) t = 1 → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) t = 1) → (∀ x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, GlobalTheory.JSW.whit φ.1 (x * t) = c * GlobalTheory.JSW.whit φ.1 x) → ∀ x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, GlobalTheory.JSW.whit F (x * t) = c * GlobalTheory.JSW.whit F x := by
  first | (exact @GlobalTheory.JSW.KirSemi.kirillov_semilocal_bump) | (exact GlobalTheory.JSW.KirSemi.kirillov_semilocal_bump) | (intros; apply GlobalTheory.JSW.KirSemi.kirillov_semilocal_bump  <;> assumption)
end
