module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArchimedeanModerateGrowthMatrixSmoothingIntegr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArchimedeanRapidKernelOperatorFinsetSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRapidSuperpositionCharactersStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SandCLMInfApply
noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW
open scoped FourierTransform

namespace GlobalTheory.JSW.MirCinf

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

def IsRapidFamInf {X Z : Type} [MeasurableSpace X] [NormedAddCommGroup Z] [NormedSpace ℝ Z] (ν : Measure X)
    (k : GL (Fin n) (Cinf E) → X → ℂ) (γ : X → GL (Fin n) (Cinf E)) (η : GL (Fin n) (Cinf E) → X → Z →L[ℝ] ℝ) :
    Prop :=
  (∀ i j, Measurable fun x =>(γ x : Matrix (Fin n) (Fin n) (Cinf E)) i j) ∧
  (∀ (X₀ : Type) [MeasurableSpace X₀] (γ₀ : X₀ → GL (Fin n) (Cinf E)),
    (∀ i j, Measurable fun x =>(γ₀ x : Matrix (Fin n) (Fin n) (Cinf E)) i j) →
      Measurable (fun p : X₀ × X =>k (γ₀ p.1) p.2) ∧ ∀ z, Measurable fun p : X₀ × X =>η (γ₀ p.1) p.2 z) ∧
  ∀ N : ℕ, ∃ (C : ℝ) (M : ℕ), ∀ q, Integrable (fun x =>‖k q x‖ * (htInf (γ x) * (1 + ‖η q x‖)) ^ N) ν ∧
    ∫ x, ‖k q x‖ * (htInf (γ x) * (1 + ‖η q x‖)) ^ N ∂ν ≤ C * htInf q ^ M

def sandCLMInf (A B : Matrix (Fin n) (Fin n) (Cinf E)) :
    (Fin n → Fin n → Cinf E) →L[ℝ] (Fin n → Fin n → Cinf E) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x i j =>(A * Matrix.of x * B) i j
      map_add' := fun x y =>by
        funext i j
        change (A * (Matrix.of x + Matrix.of y) * B) i j = (A * Matrix.of x * B) i j + (A * Matrix.of y * B) i j
        rw [mul_add, add_mul, Matrix.add_apply]
      map_smul' := fun c x =>by
        funext i j
        change (A * (c • Matrix.of x) * B) i j = c • (A * Matrix.of x * B) i j
        rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply] }

theorem sandCLMInf_apply (A B : Matrix (Fin n) (Fin n) (Cinf E)) (x : Fin n → Fin n → Cinf E) (i j : Fin n) :
    sandCLMInf A B x i j = (A * Matrix.of x * B) i j := rfl

def jacInf (x : Matrix (Fin n) (Fin n) (Cinf E)) : ℝ := ∏ w : InfinitePlace E, Complex.normSq (x.det w) ^ n


open Classical in
def secKInf {X Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] (R : ℝ) (σ₀ : Fin n → Fin n → Cinf E)
    (κ : X → ℂ) (τ : X → (Z × (Fin n → Fin n → Cinf E)) →L[ℝ] ℝ) (q : GL (Fin n) (Cinf E))
    (p : (Fin n → Fin n → Cinf E) × X) : ℂ :=
  if IsUnit (Matrix.of p.1) ∧ htInf (toGLInf (Matrix.of p.1)) ≤ R * htInf q then
    ((jacInf ((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) : ℝ) : ℂ) * κ p.2 *
      (𝐞 (τ p.2 (0, sandCLMInf ((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) (Matrix.of p.1) σ₀)) : ℂ)
  else 0

def secEtaInf {X Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] (L : Z →L[ℝ] (Fin n → Fin n → Cinf E))
    (τ : X → (Z × (Fin n → Fin n → Cinf E)) →L[ℝ] ℝ) (q : GL (Fin n) (Cinf E))
    (p : (Fin n → Fin n → Cinf E) × X) : Z →L[ℝ] ℝ :=
  (τ p.2).comp ((ContinuousLinearMap.id ℝ Z).prod
    ((sandCLMInf ((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) (Matrix.of p.1)).comp L))

theorem jacInf_mul (x y : Matrix (Fin n) (Fin n) (Cinf E)) : jacInf (x * y) = jacInf x * jacInf y := by
  simp only [jacInf, Matrix.det_mul, Pi.mul_apply, map_mul, mul_pow, Finset.prod_mul_distrib]

end GlobalTheory.JSW.MirCinf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzIntegralBoundSmooth
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumNormEntriesMulLe
namespace GlobalTheory.EntryNormProductBound

theorem sum_norm_entries_mul_le {n : ℕ} {α : Type} [NormedRing α]
    (a b : Matrix (Fin n) (Fin n) α) :
    ∑ i : Fin n, ∑ j : Fin n, ‖(a * b) i j‖ ≤
      (∑ i : Fin n, ∑ j : Fin n, ‖a i j‖) * ∑ i : Fin n, ∑ j : Fin n, ‖b i j‖ := by
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  calc ∑ j : Fin n, ‖(a * b) i j‖
      ≤ ∑ j : Fin n, ∑ k : Fin n, ‖a i k‖ * ‖b k j‖ := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [Matrix.mul_apply]
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => norm_mul_le _ _)
    _ = ∑ k : Fin n, ‖a i k‖ * ∑ j : Fin n, ‖b k j‖ := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm
    _ ≤ ∑ k : Fin n, ‖a i k‖ * ∑ l : Fin n, ∑ j : Fin n, ‖b l j‖ := by
        refine Finset.sum_le_sum fun k _ => ?_
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        exact Finset.single_le_sum (f := fun l => ∑ j : Fin n, ‖b l j‖)
          (fun l _ => Finset.sum_nonneg fun j _ => norm_nonneg _) (Finset.mem_univ k)
    _ = (∑ k : Fin n, ‖a i k‖) * ∑ l : Fin n, ∑ j : Fin n, ‖b l j‖ :=
        (Finset.sum_mul _ _ _).symm

end GlobalTheory.EntryNormProductBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzIntegralBoundSmooth
open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

noncomputable section

namespace GlobalTheory.JSW.MirCinf.SecFamInf

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem sum_norm_mul_le' {α : Type} [NormedRing α] (a b : Matrix (Fin n) (Fin n) α) :
    ∑ i, ∑ j, ‖(a * b) i j‖ ≤ (∑ i, ∑ j, ‖a i j‖) * ∑ i, ∑ j, ‖b i j‖ := by
  first
  | exact @_root_.GlobalTheory.EntryNormProductBound.sum_norm_entries_mul_le
  | exact _root_.GlobalTheory.EntryNormProductBound.sum_norm_entries_mul_le
  | (apply _root_.GlobalTheory.EntryNormProductBound.sum_norm_entries_mul_le <;> assumption)
  | (intros; apply _root_.GlobalTheory.EntryNormProductBound.sum_norm_entries_mul_le <;> assumption)
  | (intros; apply @_root_.GlobalTheory.EntryNormProductBound.sum_norm_entries_mul_le <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.EntryNormProductBound.sum_norm_entries_mul_le ..)

theorem norm_sandCLMInf_le (A B : Matrix (Fin n) (Fin n) (Cinf E)) :
    ‖sandCLMInf A B‖ ≤ (n : ℝ) ^ 2 * (∑ i, ∑ j, ‖A i j‖) * (∑ i, ∑ j, ‖B i j‖) := by
  have hA : 0 ≤ ∑ i, ∑ j, ‖A i j‖ := by positivity
  have hB : 0 ≤ ∑ i, ∑ j, ‖B i j‖ := by positivity
  have h0 : 0 ≤ (n : ℝ) ^ 2 * (∑ i, ∑ j, ‖A i j‖) * (∑ i, ∑ j, ‖B i j‖) := by positivity
  refine ContinuousLinearMap.opNorm_le_bound _ h0 fun x => ?_
  have h1 : 0 ≤ (n : ℝ) ^ 2 * (∑ i, ∑ j, ‖A i j‖) * (∑ i, ∑ j, ‖B i j‖) * ‖x‖ := mul_nonneg h0 (norm_nonneg _)
  have key : ∀ i j, ‖sandCLMInf A B x i j‖ ≤ (n : ℝ) ^ 2 * (∑ i, ∑ j, ‖A i j‖) * (∑ i, ∑ j, ‖B i j‖) * ‖x‖ := by
    intro i j
    rw [sandCLMInf_apply]
    have e1 : ‖(A * Matrix.of x * B) i j‖ ≤ ∑ i, ∑ j, ‖(A * Matrix.of x * B) i j‖ :=
      (Finset.single_le_sum (f := fun j => ‖(A * Matrix.of x * B) i j‖) (fun _ _ => norm_nonneg _)
        (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, ‖(A * Matrix.of x * B) i j‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i))
    have e2 := sum_norm_mul_le' (A * Matrix.of x) B
    have e3 := sum_norm_mul_le' A (Matrix.of x)
    have e4 : ∑ i, ∑ j, ‖(Matrix.of x) i j‖ ≤ (n : ℝ) ^ 2 * ‖x‖ := by
      calc ∑ i, ∑ j, ‖(Matrix.of x) i j‖ ≤ ∑ _i : Fin n, ∑ _j : Fin n, ‖x‖ :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
              (norm_le_pi_norm (x i) j).trans (norm_le_pi_norm x i)
        _ = _ := by simp; ring
    calc ‖(A * Matrix.of x * B) i j‖ ≤ (∑ i, ∑ j, ‖(A * Matrix.of x) i j‖) * ∑ i, ∑ j, ‖B i j‖ := e1.trans e2
      _ ≤ ((∑ i, ∑ j, ‖A i j‖) * ((n : ℝ) ^ 2 * ‖x‖)) * ∑ i, ∑ j, ‖B i j‖ :=
          mul_le_mul_of_nonneg_right (e3.trans (mul_le_mul_of_nonneg_left e4 hA)) hB
      _ = _ := by ring
  exact (pi_norm_le_iff_of_nonneg h1).2 fun i => (pi_norm_le_iff_of_nonneg h1).2 fun j => key i j

theorem sum_norm_le_of_le (A : Matrix (Fin n) (Fin n) (Cinf E)) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i j w, ‖A i j w‖ ≤ c) : ∑ i, ∑ j, ‖A i j‖ ≤ (n : ℝ) ^ 2 * c := by
  calc ∑ i, ∑ j, ‖A i j‖ ≤ ∑ _i : Fin n, ∑ _j : Fin n, c :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          (pi_norm_le_iff_of_nonneg hc).2 fun w => h i j w
    _ = _ := by simp; ring

theorem measurable_sandCLMInf_apply {Y : Type} [MeasurableSpace Y] {A B : Y → Matrix (Fin n) (Fin n) (Cinf E)}
    (hA : ∀ i j, Measurable fun y => A y i j) (hB : ∀ i j, Measurable fun y => B y i j) (c : Fin n → Fin n → Cinf E) :
    Measurable fun y => sandCLMInf (A y) (B y) c := by
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  simp only [sandCLMInf_apply, Matrix.mul_apply, Matrix.of_apply]
  refine Finset.measurable_sum _ fun l _ => ?_
  refine Measurable.mul ?_ (hB l j)
  exact Finset.measurable_sum _ fun k _ => (hA i k).mul measurable_const

theorem measurable_clm_evalInf {Y V : Type} [MeasurableSpace Y] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] {f : Y → V →L[ℝ] ℝ} {w : Y → V}
    (hf : ∀ e, Measurable fun y => f y e) (hw : Measurable w) : Measurable fun y => f y (w y) := by
  have h1 : Measurable f := measurable_dual hf
  have hc : Continuous fun p : (V →L[ℝ] ℝ) × V => p.1 p.2 := isBoundedBilinearMap_apply.continuous
  exact hc.measurable.comp (h1.prodMk hw)

theorem measurable_htInf_comp {Y : Type} [MeasurableSpace Y] {γ : Y → GL (Fin n) (Cinf E)}
    (hγ : ∀ i j, Measurable fun y => (γ y : Matrix (Fin n) (Fin n) (Cinf E)) i j) :
    Measurable fun y => htInf (γ y) := by
  unfold htInf
  refine Finset.measurable_prod _ fun w _ => ?_
  exact measurable_comp_GL (F := htGL) continuous_htGL fun i j => (measurable_pi_apply w).comp (hγ i j)

theorem isOpen_isUnit_ofInf : IsOpen {x : Fin n → Fin n → Cinf E | IsUnit (Matrix.of x)} := by
  have := (isOpenEmbedding_entriesGLInf (E := E) (n := n)).isOpen_range
  convert this using 1
  ext x
  exact ⟨fun ⟨u, hu⟩ => ⟨u, hu⟩, fun ⟨u, hu⟩ => ⟨u, hu⟩⟩

theorem measurable_toGLInf_entry (i j : Fin n) :
    Measurable fun x : Fin n → Fin n → Cinf E => (toGLInf (Matrix.of x) : Matrix (Fin n) (Fin n) (Cinf E)) i j := by
  classical
  have : (fun x : Fin n → Fin n → Cinf E => (toGLInf (Matrix.of x) : Matrix (Fin n) (Fin n) (Cinf E)) i j) =
      fun x => if x ∈ {x : Fin n → Fin n → Cinf E | IsUnit (Matrix.of x)} then x i j
        else (1 : Matrix (Fin n) (Fin n) (Cinf E)) i j := by
    funext x
    by_cases h : IsUnit (Matrix.of x) <;> simp [toGLInf, h]
  rw [this]
  exact Measurable.ite isOpen_isUnit_ofInf.measurableSet (by fun_prop) measurable_const

theorem continuous_jacInf : Continuous (jacInf : Matrix (Fin n) (Fin n) (Cinf E) → ℝ) := by
  unfold jacInf
  refine continuous_finsetProd _ fun w _ => ?_
  exact (Complex.continuous_normSq.comp ((continuous_apply w).comp (continuous_id.matrix_det))).pow n

theorem one_le_htInf' (y : GL (Fin n) (Cinf E)) : 1 ≤ htInf y := by
  unfold htInf
  calc (1 : ℝ) = ∏ _w : InfinitePlace E, (1 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) fun w _ => one_le_htGL _

theorem htGL_le_htInf' (y : GL (Fin n) (Cinf E)) (w : InfinitePlace E) :
    htGL (Matrix.GeneralLinearGroup.map (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w) y) ≤ htInf y := by
  classical
  unfold htInf
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ w)]
  refine le_mul_of_one_le_right (htGL_pos _).le ?_
  calc (1 : ℝ) = ∏ _w ∈ Finset.univ.erase w, (1 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) fun w _ => one_le_htGL _

theorem norm_entry_le_htInf' (y : GL (Fin n) (Cinf E)) (i j : Fin n) (w : InfinitePlace E) :
    ‖(y : Matrix (Fin n) (Fin n) (Cinf E)) i j w‖ ≤ htInf y ∧
      ‖((y⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) i j w‖ ≤ htInf y := by
  set p : GL (Fin n) (Cinf E) →* GL (Fin n) ℂ :=
    Matrix.GeneralLinearGroup.map (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w)
  refine ⟨(norm_entry_le_htGL (p y) i j).trans (htGL_le_htInf' y w), ?_⟩
  have e : ((y⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) i j w =
      (((p y)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j := by
    rw [← map_inv]; rfl
  rw [e]
  exact (norm_entry_le_htGL _ i j).trans ((htGL_inv (p y)).le.trans (htGL_le_htInf' y w))

theorem measurable_secKInf_secEtaInf {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    {X : Type} [MeasurableSpace X] (κ : X → ℂ) (τ : X → (Z × (Fin n → Fin n → Cinf E)) →L[ℝ] ℝ)
    (hκ : Measurable κ) (hτ : ∀ z, Measurable fun x => τ x z) (R : ℝ) (σ₀ : Fin n → Fin n → Cinf E)
    (L : Z →L[ℝ] (Fin n → Fin n → Cinf E)) (X₀ : Type) [MeasurableSpace X₀] (γ₀ : X₀ → GL (Fin n) (Cinf E))
    (hγ₀ : ∀ i j, Measurable fun x => (γ₀ x : Matrix (Fin n) (Fin n) (Cinf E)) i j) :
    Measurable (fun p : X₀ × ((Fin n → Fin n → Cinf E) × X) => secKInf R σ₀ κ τ (γ₀ p.1) p.2) ∧
      ∀ z, Measurable fun p : X₀ × ((Fin n → Fin n → Cinf E) × X) => secEtaInf L τ (γ₀ p.1) p.2 z := by
  letI : MeasurableSpace Z := borel Z
  haveI : BorelSpace Z := ⟨rfl⟩
  have hq : ∀ i j, Measurable fun p : X₀ × ((Fin n → Fin n → Cinf E) × X) =>
      (γ₀ p.1 : Matrix (Fin n) (Fin n) (Cinf E)) i j :=
    fun i j => (hγ₀ i j).comp measurable_fst
  have hinv : ∀ i j, Measurable fun p : X₀ × ((Fin n → Fin n → Cinf E) × X) =>
      (((γ₀ p.1)⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) i j := fun i j =>
    measurable_comp_GLInf
      (F := fun g : GL (Fin n) (Cinf E) => ((g⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) i j)
      (Units.continuous_coe_inv.matrix_elem i j) hq
  have hx1 : Measurable fun p : X₀ × ((Fin n → Fin n → Cinf E) × X) => p.2.1 := measurable_fst.comp measurable_snd
  have hx : ∀ i j, Measurable fun p : X₀ × ((Fin n → Fin n → Cinf E) × X) => Matrix.of p.2.1 i j :=
    fun i j => (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hx1)
  have hy : Measurable fun p : X₀ × ((Fin n → Fin n → Cinf E) × X) => p.2.2 := measurable_snd.comp measurable_snd
  have hτy : ∀ e, Measurable fun p : X₀ × ((Fin n → Fin n → Cinf E) × X) => τ p.2.2 e := fun e => (hτ e).comp hy
  refine ⟨?_, fun z => ?_⟩
  · unfold secKInf
    refine Measurable.ite ?_ ?_ measurable_const
    · have e : {p : X₀ × ((Fin n → Fin n → Cinf E) × X) | IsUnit (Matrix.of p.2.1) ∧
          htInf (toGLInf (Matrix.of p.2.1)) ≤ R * htInf (γ₀ p.1)} =
          (fun p : X₀ × ((Fin n → Fin n → Cinf E) × X) => p.2.1) ⁻¹' {x | IsUnit (Matrix.of x)} ∩
          {p | htInf (toGLInf (Matrix.of p.2.1)) ≤ R * htInf (γ₀ p.1)} := by
        ext p; simp
      rw [e]
      refine (isOpen_isUnit_ofInf.measurableSet.preimage hx1).inter (measurableSet_le ?_ ?_)
      · exact measurable_htInf_comp (γ := fun p : X₀ × ((Fin n → Fin n → Cinf E) × X) => toGLInf (Matrix.of p.2.1))
          (fun i j => (measurable_toGLInf_entry i j).comp hx1)
      · exact (measurable_htInf_comp hq).const_mul R
    · refine Measurable.mul (Measurable.mul ?_ (hκ.comp hy)) ?_
      · exact measurable_comp_GLInf
          (F := fun g : GL (Fin n) (Cinf E) =>
            ((jacInf ((g⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) : ℝ) : ℂ))
          (Complex.continuous_ofReal.comp (continuous_jacInf.comp Units.continuous_coe_inv)) hq
      · exact (continuous_subtype_val.comp Real.continuous_fourierChar).measurable.comp
          (measurable_clm_evalInf hτy (measurable_const.prodMk (measurable_sandCLMInf_apply hinv hx σ₀)))
  · have e : (fun p : X₀ × ((Fin n → Fin n → Cinf E) × X) => secEtaInf L τ (γ₀ p.1) p.2 z) = fun p =>
        τ p.2.2 (z, sandCLMInf (((γ₀ p.1)⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E))
          (Matrix.of p.2.1) (L z)) := by
      funext p; rfl
    rw [e]
    exact measurable_clm_evalInf hτy (measurable_const.prodMk (measurable_sandCLMInf_apply hinv hx (L z)))

theorem jacInf_inv_le (q : GL (Fin n) (Cinf E)) :
    jacInf ((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) ≤
      ((((n.factorial : ℝ) * htInf q ^ n) ^ 2) ^ n) ^ Fintype.card (InfinitePlace E) := by
  unfold jacInf
  rw [← Finset.card_univ, ← Finset.prod_const]
  refine Finset.prod_le_prod₀ (fun w _ => pow_nonneg (Complex.normSq_nonneg _) _) fun w _ => ?_
  set M := ((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) with hM
  have hdw : M.det w = ((Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w).mapMatrix M).det :=
    RingHom.map_det (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w) M
  have hdet : ‖M.det w‖ ≤ n.factorial * htInf q ^ n := by
    rw [hdw]
    have := Matrix.det_le (abv := NormedField.toAbsoluteValue ℂ)
      (A := (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w).mapMatrix M) (x := htInf q)
      (fun i j => (norm_entry_le_htInf' q i j w).2)
    rw [Fintype.card_fin, nsmul_eq_mul] at this
    exact this
  refine pow_le_pow_left₀ (Complex.normSq_nonneg _) ?_ n
  rw [Complex.normSq_eq_norm_sq]
  exact pow_le_pow_left₀ (norm_nonneg _) hdet 2

theorem secKInf_moment_le {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] {X : Type} (κ : X → ℂ)
    (τ : X → (Z × (Fin n → Fin n → Cinf E)) →L[ℝ] ℝ) (R : ℝ) (σ₀ : Fin n → Fin n → Cinf E)
    (L : Z →L[ℝ] (Fin n → Fin n → Cinf E)) (N : ℕ) (q : GL (Fin n) (Cinf E)) (p : (Fin n → Fin n → Cinf E) × X) :
    ‖secKInf R σ₀ κ τ q p‖ * (htInf (toGLInf (Matrix.of p.1)) * (1 + ‖secEtaInf L τ q p‖)) ^ N ≤
      (Metric.closedBall (0 : Fin n → Fin n → Cinf E) (|R| * htInf q)).indicator
        (fun _ => ((((n.factorial : ℝ) * htInf q ^ n) ^ 2) ^ n) ^ Fintype.card (InfinitePlace E) *
          ((|R| * (1 + (n : ℝ) ^ 6 * |R| * ‖L‖)) * htInf q ^ 3) ^ N) p.1 *
        (‖κ p.2‖ * (1 + ‖τ p.2‖) ^ N) := by
  have hh1 := one_le_htInf' q
  have hh0 : 0 ≤ htInf q := by linarith
  have hK0 : 0 ≤ ((((n.factorial : ℝ) * htInf q ^ n) ^ 2) ^ n) ^ Fintype.card (InfinitePlace E) *
      ((|R| * (1 + (n : ℝ) ^ 6 * |R| * ‖L‖)) * htInf q ^ 3) ^ N := by
    have : 0 ≤ |R| * (1 + (n : ℝ) ^ 6 * |R| * ‖L‖) := by positivity
    exact mul_nonneg (pow_nonneg (pow_nonneg (sq_nonneg _) _) _)
      (pow_nonneg (mul_nonneg this (pow_nonneg hh0 _)) _)
  by_cases hc : IsUnit (Matrix.of p.1) ∧ htInf (toGLInf (Matrix.of p.1)) ≤ R * htInf q
  · obtain ⟨hu, hle⟩ := hc
    have hg1 := one_le_htInf' (toGLInf (Matrix.of p.1))
    have hR : 0 ≤ R := by
      by_contra hR
      push_neg at hR
      nlinarith
    have habs : |R| = R := abs_of_nonneg hR
    have hval : (toGLInf (Matrix.of p.1) : Matrix (Fin n) (Fin n) (Cinf E)) = Matrix.of p.1 := val_toGLInf hu
    have hent : ∀ i j w, ‖p.1 i j w‖ ≤ R * htInf q := by
      intro i j w
      have := (norm_entry_le_htInf' (toGLInf (Matrix.of p.1)) i j w).1
      rw [hval] at this
      exact this.trans hle
    have hRh : 0 ≤ R * htInf q := mul_nonneg hR hh0
    have hball : p.1 ∈ Metric.closedBall (0 : Fin n → Fin n → Cinf E) (|R| * htInf q) := by
      rw [mem_closedBall_zero_iff, habs]
      exact (pi_norm_le_iff_of_nonneg hRh).2 fun i => (pi_norm_le_iff_of_nonneg hRh).2 fun j =>
        (pi_norm_le_iff_of_nonneg hRh).2 fun w => hent i j w
    rw [Set.indicator_of_mem hball]
    set D := jacInf ((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) with hDdef
    have hD0 : 0 ≤ D := Finset.prod_nonneg fun w _ => pow_nonneg (Complex.normSq_nonneg _) _
    have hK : ‖secKInf R σ₀ κ τ q p‖ = D * ‖κ p.2‖ := by
      simp only [secKInf, if_pos (And.intro hu hle), norm_mul, Circle.norm_coe, mul_one, Complex.norm_real,
        Real.norm_eq_abs]
      rw [abs_of_nonneg hD0]
    have hD : D ≤ ((((n.factorial : ℝ) * htInf q ^ n) ^ 2) ^ n) ^ Fintype.card (InfinitePlace E) :=
      jacInf_inv_le q
    set s := sandCLMInf ((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) (Matrix.of p.1)
    have hs : ‖s‖ ≤ (n : ℝ) ^ 6 * R * htInf q ^ 2 := by
      refine (norm_sandCLMInf_le _ _).trans ?_
      have e1 := sum_norm_le_of_le ((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) hh0
        (fun i j w => (norm_entry_le_htInf' q i j w).2)
      have e2 := sum_norm_le_of_le (Matrix.of p.1) hRh hent
      have e0 : 0 ≤ ∑ i, ∑ j, ‖((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) i j‖ :=
        Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
      have e3 : 0 ≤ ∑ i, ∑ j, ‖(Matrix.of p.1) i j‖ :=
        Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
      have hn : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
      calc (n : ℝ) ^ 2 * (∑ i, ∑ j, ‖((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) i j‖) *
            (∑ i, ∑ j, ‖(Matrix.of p.1) i j‖)
          ≤ (n : ℝ) ^ 2 * ((n : ℝ) ^ 2 * htInf q) * ((n : ℝ) ^ 2 * (R * htInf q)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left e1 hn) e2 e3 (mul_nonneg hn (mul_nonneg hn hh0))
        _ = _ := by ring
    have hη : ‖secEtaInf L τ q p‖ ≤ ‖τ p.2‖ * (1 + ‖s‖ * ‖L‖) := by
      unfold secEtaInf
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
      rw [ContinuousLinearMap.opNorm_prod, Prod.norm_def]
      refine max_le ?_ ?_
      · have := ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := Z)
        have : 0 ≤ ‖s‖ * ‖L‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
        linarith
      · have := ContinuousLinearMap.opNorm_comp_le s L
        linarith
    set t := ‖τ p.2‖
    set ℓ := ‖L‖
    set h := htInf q
    have ht0 : 0 ≤ t := norm_nonneg _
    have hl0 : 0 ≤ ℓ := norm_nonneg _
    have hc0 : 0 ≤ (n : ℝ) ^ 6 * R * ℓ := by positivity
    have hsl : ‖s‖ * ℓ ≤ (n : ℝ) ^ 6 * R * ℓ * h ^ 2 := by
      calc ‖s‖ * ℓ ≤ ((n : ℝ) ^ 6 * R * h ^ 2) * ℓ := mul_le_mul_of_nonneg_right hs hl0
        _ = _ := by ring
    have hbase : htInf (toGLInf (Matrix.of p.1)) * (1 + ‖secEtaInf L τ q p‖) ≤
        (|R| * (1 + (n : ℝ) ^ 6 * |R| * ℓ)) * h ^ 3 * (1 + t) := by
      rw [habs]
      have h2 : 1 ≤ h ^ 2 := one_le_pow₀ hh1
      have a1 : 1 + ‖secEtaInf L τ q p‖ ≤ (1 + t) * ((1 + (n : ℝ) ^ 6 * R * ℓ) * h ^ 2) := by
        have b1 : 1 + ‖secEtaInf L τ q p‖ ≤ 1 + t * (1 + (n : ℝ) ^ 6 * R * ℓ * h ^ 2) := by
          have := mul_le_mul_of_nonneg_left (add_le_add_left hsl 1) ht0
          linarith
        have b2 : 1 + (n : ℝ) ^ 6 * R * ℓ * h ^ 2 ≤ (1 + (n : ℝ) ^ 6 * R * ℓ) * h ^ 2 := by nlinarith
        have b3 : 1 ≤ (1 + (n : ℝ) ^ 6 * R * ℓ) * h ^ 2 := by nlinarith
        nlinarith
      have a0 : 0 ≤ 1 + ‖secEtaInf L τ q p‖ := by positivity
      calc htInf (toGLInf (Matrix.of p.1)) * (1 + ‖secEtaInf L τ q p‖)
          ≤ (R * h) * ((1 + t) * ((1 + (n : ℝ) ^ 6 * R * ℓ) * h ^ 2)) :=
            mul_le_mul hle a1 a0 (by nlinarith)
        _ = _ := by ring
    have hpow := pow_le_pow_left₀ (mul_nonneg (htInf_pos' _).le (by positivity)) hbase N
    rw [mul_pow _ (1 + t)] at hpow
    rw [hK]
    have k0 : 0 ≤ ‖κ p.2‖ := norm_nonneg _
    calc D * ‖κ p.2‖ * (htInf (toGLInf (Matrix.of p.1)) * (1 + ‖secEtaInf L τ q p‖)) ^ N
        ≤ ((((n.factorial : ℝ) * h ^ n) ^ 2) ^ n) ^ Fintype.card (InfinitePlace E) * ‖κ p.2‖ *
            (((|R| * (1 + (n : ℝ) ^ 6 * |R| * ℓ)) * h ^ 3) ^ N * (1 + t) ^ N) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hD k0) hpow
            (pow_nonneg (mul_nonneg (htInf_pos' _).le (by positivity)) _) (mul_nonneg (hD0.trans hD) k0)
      _ = _ := by ring
  · have : secKInf R σ₀ κ τ q p = 0 := by simp only [secKInf, if_neg hc]
    rw [this, norm_zero, zero_mul]
    exact mul_nonneg (Set.indicator_nonneg (fun _ _ => hK0) _) (by positivity)

theorem isRapidFamInf_secKInf : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (Z : Type) [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (κ : X → ℂ)
    (τ : X → (Z × (Fin n → Fin n → Cinf E)) →L[ℝ] ℝ), Measurable κ → (∀ z, Measurable fun x => τ x z) →
    (∀ N : ℕ, Integrable (fun x => ‖κ x‖ * (1 + ‖τ x‖) ^ N) ν) → ∀ (R : ℝ) (σ₀ : Fin n → Fin n → Cinf E)
    (L : Z →L[ℝ] (Fin n → Fin n → Cinf E)), IsRapidFamInf ((volume : Measure (Fin n → Fin n → Cinf E)).prod ν)
      (secKInf R σ₀ κ τ) (fun p => toGLInf (Matrix.of p.1)) (secEtaInf L τ) := by
  intro E _ _ n Z _ _ _ X _ ν _ κ τ hκ hτ hint R σ₀ L
  have hγ : ∀ i j, Measurable fun p : (Fin n → Fin n → Cinf E) × X =>
      (toGLInf (Matrix.of p.1) : Matrix (Fin n) (Fin n) (Cinf E)) i j :=
    fun i j => (measurable_toGLInf_entry i j).comp measurable_fst
  refine ⟨hγ, fun X₀ _ γ₀ hγ₀ => measurable_secKInf_secEtaInf κ τ hκ hτ R σ₀ L X₀ γ₀ hγ₀, fun N => ?_⟩
  refine ⟨(n.factorial : ℝ) ^ (2 * n * Fintype.card (InfinitePlace E)) *
      (|R| * (1 + (n : ℝ) ^ 6 * |R| * ‖L‖)) ^ N *
      |R| ^ Module.finrank ℝ (Fin n → Fin n → Cinf E) *
      (volume : Measure (Fin n → Fin n → Cinf E)).real (Metric.ball 0 1) * ∫ y, ‖κ y‖ * (1 + ‖τ y‖) ^ N ∂ν,
    n * 2 * n * Fintype.card (InfinitePlace E) + 3 * N + Module.finrank ℝ (Fin n → Fin n → Cinf E), fun q => ?_⟩
  have hm := measurable_secKInf_secEtaInf κ τ hκ hτ R σ₀ L Unit (fun _ => q) (fun _ _ => measurable_const)
  have hu : Measurable fun p : (Fin n → Fin n → Cinf E) × X => (((), p) : Unit × ((Fin n → Fin n → Cinf E) × X)) :=
    measurable_const.prodMk measurable_id
  have hk : Measurable (secKInf R σ₀ κ τ q) := hm.1.comp hu
  have hη : Measurable (secEtaInf L τ q) := measurable_dual fun z => (hm.2 z).comp hu
  have hg : Measurable fun p : (Fin n → Fin n → Cinf E) × X => htInf (toGLInf (Matrix.of p.1)) :=
    measurable_htInf_comp hγ
  have hF : Measurable fun p : (Fin n → Fin n → Cinf E) × X =>
      ‖secKInf R σ₀ κ τ q p‖ * (htInf (toGLInf (Matrix.of p.1)) * (1 + ‖secEtaInf L τ q p‖)) ^ N :=
    hk.norm.mul ((hg.mul (measurable_const.add hη.norm)).pow_const N)
  have h0 : ∀ p : (Fin n → Fin n → Cinf E) × X,
      0 ≤ ‖secKInf R σ₀ κ τ q p‖ * (htInf (toGLInf (Matrix.of p.1)) * (1 + ‖secEtaInf L τ q p‖)) ^ N := fun p =>
    mul_nonneg (norm_nonneg _) (pow_nonneg (mul_nonneg (htInf_pos' _).le (by positivity)) _)
  have hbd := secKInf_moment_le κ τ R σ₀ L N q
  have hr : 0 ≤ |R| * htInf q := mul_nonneg (abs_nonneg _) (htInf_pos' _).le
  set K := ((((n.factorial : ℝ) * htInf q ^ n) ^ 2) ^ n) ^ Fintype.card (InfinitePlace E) *
    ((|R| * (1 + (n : ℝ) ^ 6 * |R| * ‖L‖)) * htInf q ^ 3) ^ N with hK
  have hB : Integrable (fun p : (Fin n → Fin n → Cinf E) × X =>
      (Metric.closedBall (0 : Fin n → Fin n → Cinf E) (|R| * htInf q)).indicator (fun _ => K) p.1 *
        (‖κ p.2‖ * (1 + ‖τ p.2‖) ^ N)) ((volume : Measure (Fin n → Fin n → Cinf E)).prod ν) :=
    Integrable.mul_prod ((integrable_indicator_iff measurableSet_closedBall).2
      (integrableOn_const measure_closedBall_lt_top.ne)) (hint N)
  refine ⟨hB.mono' hF.aestronglyMeasurable (ae_of_all _ fun p => ?_), ?_⟩
  · rw [Real.norm_eq_abs, abs_of_nonneg (h0 p)]
    exact hbd p
  · refine (integral_mono_of_nonneg (ae_of_all _ h0) hB (ae_of_all _ hbd)).trans (le_of_eq ?_)
    rw [integral_prod_mul ((Metric.closedBall (0 : Fin n → Fin n → Cinf E) (|R| * htInf q)).indicator fun _ => K)
      (fun y => ‖κ y‖ * (1 + ‖τ y‖) ^ N), integral_indicator_const _ measurableSet_closedBall, smul_eq_mul]
    simp only [Measure.real, Measure.addHaar_closedBall _ _ hr, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ (|R| * htInf q) ^ Module.finrank ℝ (Fin n → Fin n → Cinf E)), hK]
    simp only [mul_pow, ← pow_mul, pow_add]
    ring

end GlobalTheory.JSW.MirCinf.SecFamInf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzIntegralBoundSmoothStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_integral_bound_smooth : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (κ : X → ℂ) (τ : X → (Z × (Fin n → Fin n → Cinf E)) →L[ℝ] ℝ), Measurable κ → (∀ z, Measurable fun x => τ x z) → (∀ N : ℕ, Integrable (fun x => ‖κ x‖ * (1 + ‖τ x‖) ^ N) ν) → ∀ (R : ℝ) (σ₀ : Fin n → Fin n → Cinf E) (L : Z →L[ℝ] (Fin n → Fin n → Cinf E)), IsRapidFamInf ((volume : Measure (Fin n → Fin n → Cinf E)).prod ν) (secKInf R σ₀ κ τ) (fun p => toGLInf (Matrix.of p.1)) (secEtaInf L τ) := by
  first | (exact @GlobalTheory.JSW.MirCinf.SecFamInf.isRapidFamInf_secKInf) | (exact GlobalTheory.JSW.MirCinf.SecFamInf.isRapidFamInf_secKInf) | (intros; apply GlobalTheory.JSW.MirCinf.SecFamInf.isRapidFamInf_secKInf  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothingAffineFamilyEqIntegralKernel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralArchimedeanMatricesLeftMulJacobian
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralArchimedeanMatricesLeftMulJacobian
open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW.MirCinf

theorem integral_eq_integral_mulLeft_matrixInf (E : Type) [Field E] [NumberField E] (n : ℕ)
    (A : GL (Fin n) (Cinf E)) (F : (Fin n → Fin n → Cinf E) → ℂ) :
    ∫ a, F a = ∫ h : (Fin n → Fin n → Cinf E), ((jacInf (A : Matrix (Fin n) (Fin n) (Cinf E)) : ℝ) : ℂ) *
      F (fun i j => ((A : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of h) i j) := by
  set W := InfinitePlace E
  set M : Matrix (Fin n) (Fin n) (Cinf E) := (A : Matrix (Fin n) (Fin n) (Cinf E)) with hM
  set L : (Fin n → Fin n → Cinf E) →ₗ[ℝ] (Fin n → Fin n → Cinf E) :=
    { toFun := fun x i j => (M * Matrix.of x) i j
      map_add' := fun x y => by
        funext i j
        change (M * (Matrix.of x + Matrix.of y)) i j = (M * Matrix.of x) i j + (M * Matrix.of y) i j
        rw [mul_add, Matrix.add_apply]
      map_smul' := fun c x => by
        funext i j
        change (M * (c • Matrix.of x)) i j = c • (M * Matrix.of x) i j
        rw [Matrix.mul_smul, Matrix.smul_apply] } with hLdef
  have hL : ∀ h, L h = fun i j => (M * Matrix.of h) i j := fun h => rfl

  let e : (Fin n → Fin n → Cinf E) ≃ₗ[ℝ] (W → Fin n → Fin n → ℂ) :=
    { toFun := fun h w i j => h i j w
      invFun := fun g i j w => g w i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let Lw : W → (Fin n → Fin n → ℂ) →ₗ[ℝ] (Fin n → Fin n → ℂ) := fun w =>
    (LinearMap.mulLeft ℂ (M.map (fun z => z w))).restrictScalars ℝ
  have hconj : (e : _ →ₗ[ℝ] _) ∘ₗ L ∘ₗ (e.symm : _ →ₗ[ℝ] _) =
      LinearMap.pi (fun w => Lw w ∘ₗ LinearMap.proj w) := by
    apply LinearMap.ext; intro g; funext w i j
    change (M * Matrix.of (fun i j w => g w i j)) i j w = (M.map (fun z => z w) * Matrix.of (g w)) i j
    simp [Matrix.mul_apply, Finset.sum_apply, Matrix.map_apply]
  have hdetw : ∀ w, LinearMap.det (Lw w) = Complex.normSq (M.det w) ^ n := by
    intro w
    have := GroundTheory.Automorphic.det_restrictScalars_mulLeft (M.map (fun z => z w))
    rw [Fintype.card_fin, ← Complex.normSq_eq_norm_sq] at this
    show LinearMap.det ((LinearMap.mulLeft ℂ (M.map fun z => z w)).restrictScalars ℝ) = _
    rw [this]
    congr 2
    exact (RingHom.map_det (Pi.evalRingHom (fun _ : W => ℂ) w) M).symm
  have hdet : LinearMap.det L = jacInf M := by
    rw [← LinearMap.det_conj L e, hconj, LinearMap.det_pi]
    simp only [hdetw]
    rfl
  have hpos : 0 < jacInf M := by
    have hdA : M.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 A.isUnit).ne_zero
    refine Finset.prod_pos fun w _ => pow_pos (Complex.normSq_pos.2 ?_) n
    intro h0
    have hu : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det _).1 A.isUnit
    have : IsUnit (M.det w) := hu.map (Pi.evalRingHom (fun _ : W => ℂ) w)
    exact this.ne_zero h0
  have hd0 : LinearMap.det L ≠ 0 := by rw [hdet]; exact hpos.ne'
  have hmap : Measure.map L (volume : Measure (Fin n → Fin n → Cinf E)) =
      ENNReal.ofReal |(LinearMap.det L)⁻¹| • volume :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume hd0
  set Le : (Fin n → Fin n → Cinf E) ≃L[ℝ] (Fin n → Fin n → Cinf E) :=
    (LinearMap.equivOfDetNeZero L hd0).toContinuousLinearEquiv
  have hLe : (Le : (Fin n → Fin n → Cinf E) → (Fin n → Fin n → Cinf E)) = L := rfl
  have hemb : MeasurableEmbedding (L : (Fin n → Fin n → Cinf E) → (Fin n → Fin n → Cinf E)) := by
    rw [← hLe]; exact Le.toHomeomorph.measurableEmbedding
  simp_rw [← hL]
  rw [integral_const_mul, ← hemb.integral_map, hmap, integral_smul_measure, hdet,
    abs_of_pos (inv_pos.2 hpos), ENNReal.toReal_ofReal (inv_pos.2 hpos).le, Complex.real_smul, ← mul_assoc]
  push_cast
  rw [mul_inv_cancel₀ (by exact_mod_cast hpos.ne'), one_mul]

end GlobalTheory.JSW.MirCinf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralArchimedeanMatricesLeftMulJacobianStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_archimedeanMatrices_leftMul_jacobian : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (A : GL (Fin n) (Cinf E)) (F : (Fin n → Fin n → Cinf E) → ℂ), ∫ a, F a = ∫ h : (Fin n → Fin n → Cinf E), ((jacInf (A : Matrix (Fin n) (Fin n) (Cinf E)) : ℝ) : ℂ) * F (fun i j => ((A : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of h) i j) := by
  first | (exact @GlobalTheory.JSW.MirCinf.integral_eq_integral_mulLeft_matrixInf) | (exact GlobalTheory.JSW.MirCinf.integral_eq_integral_mulLeft_matrixInf) | (intros; apply GlobalTheory.JSW.MirCinf.integral_eq_integral_mulLeft_matrixInf  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothingAffineFamilyEqIntegralKernel
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW.MirCinf.SecAffine

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem htInf_inv_eq (g : GL (Fin n) (Cinf E)) : htInf g⁻¹ = htInf g := by
  unfold htInf
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [map_inv, htGL_inv]

end GlobalTheory.JSW.MirCinf.SecAffine

namespace GlobalTheory.JSW.MirCinf

theorem smoothMatInf_affine_eq_integral_secKInf : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] (σ₀ : Fin n → Fin n → Cinf E) (L : Z →L[ℝ] (Fin n → Fin n → Cinf E)) (χ : Z → ℂ) (α : (Fin n → Fin n → Cinf E) → ℂ), HasCompactSupport χ → (∀ z ∈ tsupport χ, IsUnit (Matrix.of (σ₀ + L z))) → HasCompactSupport α → tsupport α ⊆ {x | IsUnit (Matrix.of x)} → ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (κ : X → ℂ) (τ : X → (Z × (Fin n → Fin n → Cinf E)) →L[ℝ] ℝ), Measurable κ → (∀ z, Measurable fun x => τ x z) → (∀ N : ℕ, Integrable (fun x => ‖κ x‖ * (1 + ‖τ x‖) ^ N) ν) → (∀ z a, χ z * ((jacInf (Matrix.of (σ₀ + L z)) : ℝ) : ℂ) * α a = ∫ x, κ x * (𝐞 (τ x (z, a)) : ℂ) ∂ν) → ∃ R : ℝ, ∀ W : GL (Fin n) (Cinf E) → ℂ, IsModGrowthInf W → ∀ q z g, χ z * smoothMatInf α W (g * (toGLInf (Matrix.of (σ₀ + L z)))⁻¹ * q) = ∫ p, secKInf R σ₀ κ τ q p * (𝐞 (secEtaInf L τ q p z) : ℂ) * W (g * toGLInf (Matrix.of p.1)) ∂((volume : Measure (Fin n → Fin n → Cinf E)).prod ν) := by
  classical
  intro E _ _ n Z _ _ _ σ₀ L χ α hχ hσ hα hαu X _ ν _ κ τ hκ hτ hmom hk
  obtain ⟨R1, hR1⟩ : ∃ R1 : ℝ, ∀ z ∈ tsupport χ, htInf (toGLInf (Matrix.of (σ₀ + L z))) ≤ R1 := by
    have hc : ContinuousOn (fun z => htInf (toGLInf (Matrix.of (σ₀ + L z)))) (tsupport χ) :=
      SmoothGrowth.continuous_htInf.comp_continuousOn (SmoothGrowth.continuousOn_toGLInf.comp
        (by fun_prop : Continuous fun z => σ₀ + L z).continuousOn fun z hz => hσ z hz)
    obtain ⟨C, hC⟩ := hχ.isCompact.exists_bound_of_continuousOn hc
    exact ⟨C, fun z hz => (Real.le_norm_self _).trans (hC z hz)⟩
  obtain ⟨R2, hR2⟩ : ∃ R2 : ℝ, ∀ a ∈ tsupport α, htInf (toGLInf (Matrix.of a)) ≤ R2 := by
    have hc : ContinuousOn (fun a : Fin n → Fin n → Cinf E => htInf (toGLInf (Matrix.of a))) (tsupport α) :=
      SmoothGrowth.continuous_htInf.comp_continuousOn (SmoothGrowth.continuousOn_toGLInf.mono hαu)
    obtain ⟨C, hC⟩ := hα.isCompact.exists_bound_of_continuousOn hc
    exact ⟨C, fun a ha => (Real.le_norm_self _).trans (hC a ha)⟩
  refine ⟨R1 * R2, ?_⟩
  intro W hW q z g
  have hfam := GlobalTheory.T.schwartz_integral_bound_smooth E n Z X ν κ τ hκ hτ hmom (R1 * R2) σ₀ L
  have hrap : IsRapidFInf ((volume : Measure (Fin n → Fin n → Cinf E)).prod ν) (secKInf (R1 * R2) σ₀ κ τ q)
      (fun p => toGLInf (Matrix.of p.1)) (secEtaInf L τ q) := by
    obtain ⟨h1, h2, h3⟩ := hfam
    obtain ⟨m1, m2⟩ := h2 Unit (fun _ => q) (fun _ _ => measurable_const)
    refine ⟨m1.comp ((measurable_const (a := ()) : Measurable fun _ : (Fin n → Fin n → Cinf E) × X => ()).prodMk measurable_id), h1,
      fun z => (m2 z).comp ((measurable_const (a := ()) : Measurable fun _ : (Fin n → Fin n → Cinf E) × X => ()).prodMk measurable_id), fun N => ?_⟩
    obtain ⟨C, M, hC⟩ := h3 N
    exact (hC q).1
  have hint : Integrable (fun p : (Fin n → Fin n → Cinf E) × X => secKInf (R1 * R2) σ₀ κ τ q p *
      (𝐞 (secEtaInf L τ q p z) : ℂ) * W (g * toGLInf (Matrix.of p.1))) ((volume : Measure (Fin n → Fin n → Cinf E)).prod ν) :=
    hrap.integrable hW z g
  have hinner : ∀ h : Fin n → Fin n → Cinf E, ∫ x, secKInf (R1 * R2) σ₀ κ τ q (h, x) * (𝐞 (secEtaInf L τ q (h, x) z) : ℂ) *
      W (g * toGLInf (Matrix.of (h, x).1)) ∂ν =
      (if IsUnit (Matrix.of h) ∧ htInf (toGLInf (Matrix.of h)) ≤ R1 * R2 * htInf q then
        ((jacInf ((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) : ℝ) : ℂ) else 0) *
      (χ z * ((jacInf (Matrix.of (σ₀ + L z)) : ℝ) : ℂ) *
        α (fun i j => (((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of (σ₀ + L z) * Matrix.of h) i j)) *
      W (g * toGLInf (Matrix.of h)) := by
    intro h
    rw [hk z]
    by_cases hc : IsUnit (Matrix.of h) ∧ htInf (toGLInf (Matrix.of h)) ≤ R1 * R2 * htInf q
    · have hsum : ((0 : Z), sandCLMInf ((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) (Matrix.of h) σ₀) +
          (z, sandCLMInf ((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) (Matrix.of h) (L z)) =
          (z, fun i j => (((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of (σ₀ + L z) * Matrix.of h) i j) := by
        rw [Prod.mk_add_mk, zero_add]
        congr 1
        funext i j
        simp only [Pi.add_apply, sandCLMInf_apply]
        rw [← Matrix.add_apply, ← Matrix.add_mul, ← Matrix.mul_add]
        rfl
      have e : ∀ x, secKInf (R1 * R2) σ₀ κ τ q (h, x) * (𝐞 (secEtaInf L τ q (h, x) z) : ℂ) *
          W (g * toGLInf (Matrix.of (h, x).1)) =
          (((jacInf ((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) : ℝ) : ℂ) *
            W (g * toGLInf (Matrix.of h))) *
          (κ x * (𝐞 (τ x (z, fun i j => (((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) *
            Matrix.of (σ₀ + L z) * Matrix.of h) i j)) : ℂ)) := by
        intro x
        simp only [secKInf, secEtaInf, if_pos hc]
        rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
          ContinuousLinearMap.comp_apply, ← hsum, map_add, AddChar.map_add_eq_mul, Circle.coe_mul]
        ring
      rw [integral_congr_ae (Filter.Eventually.of_forall e), integral_const_mul, if_pos hc]
      ring
    · simp [secKInf, if_neg hc]
  have hR : ∫ p, secKInf (R1 * R2) σ₀ κ τ q p * (𝐞 (secEtaInf L τ q p z) : ℂ) * W (g * toGLInf (Matrix.of p.1))
      ∂((volume : Measure (Fin n → Fin n → Cinf E)).prod ν) = ∫ h : Fin n → Fin n → Cinf E,
      (if IsUnit (Matrix.of h) ∧ htInf (toGLInf (Matrix.of h)) ≤ R1 * R2 * htInf q then
        ((jacInf ((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) : ℝ) : ℂ) else 0) *
      (χ z * ((jacInf (Matrix.of (σ₀ + L z)) : ℝ) : ℂ) *
        α (fun i j => (((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of (σ₀ + L z) * Matrix.of h) i j)) *
      W (g * toGLInf (Matrix.of h)) := by
    rw [integral_prod _ hint]
    exact integral_congr_ae (Filter.Eventually.of_forall hinner)
  rw [hR]
  by_cases hz : χ z = 0
  · simp [hz]
  have hzK : z ∈ tsupport χ := subset_tsupport _ hz
  have hu := hσ z hzK
  set σ' := toGLInf (Matrix.of (σ₀ + L z)) with hσ'
  have hσv : (σ' : Matrix (Fin n) (Fin n) (Cinf E)) = Matrix.of (σ₀ + L z) := val_toGLInf hu
  rw [smoothMatInf, GlobalTheory.T.integral_archimedeanMatrices_leftMul_jacobian E n (q⁻¹ * σ'), ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  simp only
  have hAh : Matrix.of (fun i j => (((q⁻¹ * σ' : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of h) i j) =
      ((q⁻¹ * σ' : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of h := rfl
  have ha : (fun i j => (((q⁻¹ * σ' : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of h) i j) =
      (fun i j => (((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of (σ₀ + L z) * Matrix.of h) i j) := by
    rw [Units.val_mul, hσv]
  rw [hAh, ha]
  by_cases hαz : α (fun i j => (((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of (σ₀ + L z) * Matrix.of h) i j) = 0
  · rw [hαz]; ring
  have hmem := subset_tsupport _ hαz
  have hAu : IsUnit (Matrix.of (fun i j => (((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of (σ₀ + L z) * Matrix.of h) i j)) := hαu hmem
  rw [← ha] at hAu hmem
  rw [hAh] at hAu
  have hh : IsUnit (Matrix.of h) := (Units.isUnit_units_mul _ _).1 hAu
  have ht : toGLInf (((q⁻¹ * σ' : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of h) = (q⁻¹ * σ') * toGLInf (Matrix.of h) :=
    Units.ext (by rw [val_toGLInf hAu, Units.val_mul (q⁻¹ * σ'), val_toGLInf hh])
  have hb1 := hR1 z hzK
  have hb2 : htInf (toGLInf (((q⁻¹ * σ' : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of h)) ≤ R2 := hR2 _ hmem
  rw [ht] at hb2
  have hb1' : htInf σ' ≤ R1 := hb1
  have hbound : htInf (toGLInf (Matrix.of h)) ≤ R1 * R2 * htInf q := by
    have e1 : toGLInf (Matrix.of h) = (q⁻¹ * σ')⁻¹ * (q⁻¹ * σ' * toGLInf (Matrix.of h)) := by group
    have p1 := htInf_pos' σ'
    have p2 := htInf_pos' (q⁻¹ * σ' * toGLInf (Matrix.of h))
    have p3 := htInf_pos' q
    calc htInf (toGLInf (Matrix.of h)) = htInf ((q⁻¹ * σ')⁻¹ * (q⁻¹ * σ' * toGLInf (Matrix.of h))) := by rw [← e1]
      _ ≤ htInf ((q⁻¹ * σ')⁻¹) * htInf (q⁻¹ * σ' * toGLInf (Matrix.of h)) := htInf_mul_le _ _
      _ = htInf (q⁻¹ * σ') * htInf (q⁻¹ * σ' * toGLInf (Matrix.of h)) := by rw [SecAffine.htInf_inv_eq]
      _ ≤ (htInf q⁻¹ * htInf σ') * htInf (q⁻¹ * σ' * toGLInf (Matrix.of h)) :=
          mul_le_mul_of_nonneg_right (htInf_mul_le _ _) p2.le
      _ = htInf q * (htInf σ' * htInf (q⁻¹ * σ' * toGLInf (Matrix.of h))) := by rw [SecAffine.htInf_inv_eq]; ring
      _ ≤ htInf q * (R1 * R2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hb1' hb2 p2.le (p1.le.trans hb1')) p3.le
      _ = R1 * R2 * htInf q := by ring
  rw [if_pos ⟨hh, hbound⟩]
  have hG : ((g * σ'⁻¹ * q : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) *
      (((q⁻¹ * σ' : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of h) = (g : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of h := by
    rw [← Matrix.mul_assoc, ← Units.val_mul]
    congr 2
    group
  have hgt : toGLInf ((g : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of h) = g * toGLInf (Matrix.of h) :=
    Units.ext (by rw [val_toGLInf (g.isUnit.mul hh), Units.val_mul, val_toGLInf hh])
  rw [hG, onMatInf_of_isUnit W (g.isUnit.mul hh), hgt, Units.val_mul, jacInf_mul, hσv]
  push_cast
  ring

end GlobalTheory.JSW.MirCinf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothingAffineFamilyEqIntegralKernelStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothing_affine_family_eq_integral_kernel : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] (σ₀ : Fin n → Fin n → Cinf E) (L : Z →L[ℝ] (Fin n → Fin n → Cinf E)) (χ : Z → ℂ) (α : (Fin n → Fin n → Cinf E) → ℂ), HasCompactSupport χ → (∀ z ∈ tsupport χ, IsUnit (Matrix.of (σ₀ + L z))) → HasCompactSupport α → tsupport α ⊆ {x | IsUnit (Matrix.of x)} → ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (κ : X → ℂ) (τ : X → (Z × (Fin n → Fin n → Cinf E)) →L[ℝ] ℝ), Measurable κ → (∀ z, Measurable fun x => τ x z) → (∀ N : ℕ, Integrable (fun x => ‖κ x‖ * (1 + ‖τ x‖) ^ N) ν) → (∀ z a, χ z * ((jacInf (Matrix.of (σ₀ + L z)) : ℝ) : ℂ) * α a = ∫ x, κ x * (𝐞 (τ x (z, a)) : ℂ) ∂ν) → ∃ R : ℝ, ∀ W : GL (Fin n) (Cinf E) → ℂ, IsModGrowthInf W → ∀ q z g, χ z * smoothMatInf α W (g * (toGLInf (Matrix.of (σ₀ + L z)))⁻¹ * q) = ∫ p, secKInf R σ₀ κ τ q p * (𝐞 (secEtaInf L τ q p z) : ℂ) * W (g * toGLInf (Matrix.of p.1)) ∂((volume : Measure (Fin n → Fin n → Cinf E)).prod ν) := by
  first | exact @GlobalTheory.JSW.MirCinf.smoothMatInf_affine_eq_integral_secKInf | exact GlobalTheory.JSW.MirCinf.smoothMatInf_affine_eq_integral_secKInf | (intros; apply GlobalTheory.JSW.MirCinf.smoothMatInf_affine_eq_integral_secKInf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanRapidKernelOperatorCompRapidFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanRapidKernelOperatorCompRapidFamily
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW.MirCinf

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem measurable_htInf_comp {X : Type} [MeasurableSpace X] {γ : X → GL (Fin n) (Cinf E)}
    (hγ : ∀ i j, Measurable fun x => (γ x : Matrix (Fin n) (Fin n) (Cinf E)) i j) :
    Measurable fun x => htInf (γ x) := by
  unfold htInf
  refine Finset.measurable_prod _ fun w _ => ?_
  exact measurable_comp_GL (F := htGL) continuous_htGL fun i j => (measurable_pi_apply w).comp (hγ i j)

theorem isKerOpInf_comp_rapidFamInf : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (Z : Type) [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] (T : (GL (Fin n) (Cinf E) → ℂ) → Z → GL (Fin n) (Cinf E) → ℂ),
    IsKerOpInf T → ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : GL (Fin n) (Cinf E) → X → ℂ)
    (γ : X → GL (Fin n) (Cinf E)) (η : GL (Fin n) (Cinf E) → X → Z →L[ℝ] ℝ), IsRapidFamInf ν k γ η →
    ∀ (S : (GL (Fin n) (Cinf E) → ℂ) → GL (Fin n) (Cinf E) → ℂ) (t : Z → GL (Fin n) (Cinf E)) (χ : Z → ℂ),
    (∀ W, IsModGrowthInf W → IsModGrowthInf (S W)) →
    (∀ W, IsModGrowthInf W → ∀ q z g, χ z * S W (g * t z * q) = ∫ x, k q x * (𝐞 (η q x z) : ℂ) * W (g * γ x) ∂ν) →
    IsKerOpInf (fun W z g => χ z * T (S W) z (g * t z)) := by
  intro E _ _ n Z _ _ _ T hT X _ ν _ k γ η hfam S t χ hS hSk
  obtain ⟨X₀, m₀, ν₀, hν₀, k₀, γ₀, η₀, ⟨hk₀, hγ₀, hη₀, hint₀⟩, hT⟩ := hT
  obtain ⟨hγ, hjoint, hmom⟩ := hfam
  obtain ⟨hkj, hηj⟩ := hjoint X₀ γ₀ hγ₀
  have mη₀ : Measurable η₀ := measurable_dual hη₀
  have mηj : Measurable fun p : X₀ × X => η (γ₀ p.1) p.2 := measurable_dual hηj
  have mht : Measurable fun x => htInf (γ x) := measurable_htInf_comp hγ
  have hrap : IsRapidFInf (ν₀.prod ν) (fun p : X₀ × X => k₀ p.1 * k (γ₀ p.1) p.2) (fun p => γ p.2)
      (fun p => η₀ p.1 + η (γ₀ p.1) p.2) := by
    refine ⟨(hk₀.comp measurable_fst).mul hkj, fun i j => (hγ i j).comp measurable_snd,
      fun z => ((hη₀ z).comp measurable_fst).add (hηj z), fun N => ?_⟩
    obtain ⟨C, M, hCM⟩ := hmom N
    let F : X₀ × X → ℝ := fun p => (‖k₀ p.1‖ * (1 + ‖η₀ p.1‖) ^ N) *
      (‖k (γ₀ p.1) p.2‖ * (htInf (γ p.2) * (1 + ‖η (γ₀ p.1) p.2‖)) ^ N)
    have mF : Measurable F := by
      have a1 : Measurable fun p : X₀ × X => k₀ p.1 := hk₀.comp measurable_fst
      have a2 : Measurable fun p : X₀ × X => η₀ p.1 := mη₀.comp measurable_fst
      have a3 : Measurable fun p : X₀ × X => htInf (γ p.2) := mht.comp measurable_snd
      exact (a1.norm.mul ((measurable_const.add a2.norm).pow_const N)).mul
        (hkj.norm.mul ((a3.mul (measurable_const.add mηj.norm)).pow_const N))
    have F0 : ∀ p, 0 ≤ F p := fun p => by
      have := htInf_pos' (γ p.2)
      positivity
    have hF : Integrable F (ν₀.prod ν) := by
      rw [integrable_prod_iff mF.aestronglyMeasurable]
      refine ⟨Filter.Eventually.of_forall fun x₀ => ((hCM (γ₀ x₀)).1.const_mul (‖k₀ x₀‖ * (1 + ‖η₀ x₀‖) ^ N)), ?_⟩
      refine ((hint₀ (max N M)).const_mul (max C 0)).mono'
        (mF.norm.stronglyMeasurable.integral_prod_right').aestronglyMeasurable
        (Filter.Eventually.of_forall fun x₀ => ?_)
      have e1 : ∫ y, ‖F (x₀, y)‖ ∂ν = (‖k₀ x₀‖ * (1 + ‖η₀ x₀‖) ^ N) *
          ∫ y, ‖k (γ₀ x₀) y‖ * (htInf (γ y) * (1 + ‖η (γ₀ x₀) y‖)) ^ N ∂ν := by
        rw [← integral_const_mul]
        exact integral_congr_ae (Filter.Eventually.of_forall fun y => Real.norm_of_nonneg (F0 _))
      have I0 : 0 ≤ ∫ y, ‖F (x₀, y)‖ ∂ν := integral_nonneg fun _ => norm_nonneg _
      rw [Real.norm_of_nonneg I0, e1]
      have hq := (hCM (γ₀ x₀)).2
      have A0 : 0 ≤ ‖k₀ x₀‖ * (1 + ‖η₀ x₀‖) ^ N := by positivity
      have h1 : 1 ≤ htInf (γ₀ x₀) := le_of_eq_of_le rfl (by
        unfold htInf
        calc (1 : ℝ) = ∏ _w : InfinitePlace E, (1 : ℝ) := by simp
          _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) fun w _ => one_le_htGL _)
      have h2 : (1 : ℝ) ≤ 1 + ‖η₀ x₀‖ := by linarith [norm_nonneg (η₀ x₀)]
      have p1 : (1 + ‖η₀ x₀‖) ^ N ≤ (1 + ‖η₀ x₀‖) ^ max N M := pow_le_pow_right₀ h2 (le_max_left _ _)
      have p2 : htInf (γ₀ x₀) ^ M ≤ htInf (γ₀ x₀) ^ max N M := pow_le_pow_right₀ h1 (le_max_right _ _)
      have hm : C * htInf (γ₀ x₀) ^ M ≤ max C 0 * htInf (γ₀ x₀) ^ max N M :=
        mul_le_mul (le_max_left _ _) p2 (by positivity) (le_max_right _ _)
      calc ‖k₀ x₀‖ * (1 + ‖η₀ x₀‖) ^ N * ∫ y, ‖k (γ₀ x₀) y‖ * (htInf (γ y) * (1 + ‖η (γ₀ x₀) y‖)) ^ N ∂ν
          ≤ ‖k₀ x₀‖ * (1 + ‖η₀ x₀‖) ^ N * (max C 0 * htInf (γ₀ x₀) ^ max N M) :=
            mul_le_mul_of_nonneg_left (hq.trans hm) A0
        _ ≤ ‖k₀ x₀‖ * (1 + ‖η₀ x₀‖) ^ max N M * (max C 0 * htInf (γ₀ x₀) ^ max N M) := by
            gcongr
        _ = max C 0 * (‖k₀ x₀‖ * (htInf (γ₀ x₀) * (1 + ‖η₀ x₀‖)) ^ max N M) := by rw [mul_pow]; ring
    refine hF.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
    · exact (((hk₀.comp measurable_fst).mul hkj).norm.mul (((mht.comp measurable_snd).mul
        (measurable_const.add ((mη₀.comp measurable_fst).add mηj).norm)).pow_const N)).aestronglyMeasurable
    · have hh := htInf_pos' (γ p.2)
      have hb : htInf (γ p.2) * (1 + ‖η₀ p.1 + η (γ₀ p.1) p.2‖) ≤
          (1 + ‖η₀ p.1‖) * (htInf (γ p.2) * (1 + ‖η (γ₀ p.1) p.2‖)) := by
        have := mul_le_mul_of_nonneg_left (show 1 + ‖η₀ p.1 + η (γ₀ p.1) p.2‖ ≤ (1 + ‖η₀ p.1‖) * (1 + ‖η (γ₀ p.1) p.2‖) by
          nlinarith [norm_add_le (η₀ p.1) (η (γ₀ p.1) p.2), norm_nonneg (η₀ p.1), norm_nonneg (η (γ₀ p.1) p.2),
            mul_nonneg (norm_nonneg (η₀ p.1)) (norm_nonneg (η (γ₀ p.1) p.2))]) hh.le
        linarith
      have hp : (htInf (γ p.2) * (1 + ‖η₀ p.1 + η (γ₀ p.1) p.2‖)) ^ N ≤
          (1 + ‖η₀ p.1‖) ^ N * (htInf (γ p.2) * (1 + ‖η (γ₀ p.1) p.2‖)) ^ N :=
        (pow_le_pow_left₀ (by positivity) hb N).trans_eq (mul_pow _ _ _)
      rw [Real.norm_of_nonneg (by positivity), norm_mul]
      calc ‖k₀ p.1‖ * ‖k (γ₀ p.1) p.2‖ * (htInf (γ p.2) * (1 + ‖η₀ p.1 + η (γ₀ p.1) p.2‖)) ^ N
          ≤ ‖k₀ p.1‖ * ‖k (γ₀ p.1) p.2‖ *
              ((1 + ‖η₀ p.1‖) ^ N * (htInf (γ p.2) * (1 + ‖η (γ₀ p.1) p.2‖)) ^ N) :=
            mul_le_mul_of_nonneg_left hp (by positivity)
        _ = F p := by simp only [F]; ring
  refine ⟨X₀ × X, inferInstance, ν₀.prod ν, inferInstance, _, _, _, hrap, ?_⟩
  intro W hW z g
  have hint := hrap.integrable hW z g
  show χ z * T (S W) z (g * t z) = _
  rw [integral_prod _ hint, hT (S W) (hS W hW) z (g * t z), ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x₀ => ?_)
  simp only
  rw [show χ z * (k₀ x₀ * (𝐞 (η₀ x₀ z) : ℂ) * S W (g * t z * γ₀ x₀)) =
      k₀ x₀ * (𝐞 (η₀ x₀ z) : ℂ) * (χ z * S W (g * t z * γ₀ x₀)) by ring, hSk W hW (γ₀ x₀) z g,
    ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [ContinuousLinearMap.add_apply, AddChar.map_add_eq_mul, Circle.coe_mul]
  ring

end GlobalTheory.JSW.MirCinf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanRapidKernelOperatorCompRapidFamilyStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanRapidKernelOperator_comp_rapidFamily : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] (T : (GL (Fin n) (Cinf E) → ℂ) → Z → GL (Fin n) (Cinf E) → ℂ), IsKerOpInf T → ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : GL (Fin n) (Cinf E) → X → ℂ) (γ : X → GL (Fin n) (Cinf E)) (η : GL (Fin n) (Cinf E) → X → Z →L[ℝ] ℝ), IsRapidFamInf ν k γ η → ∀ (S : (GL (Fin n) (Cinf E) → ℂ) → GL (Fin n) (Cinf E) → ℂ) (t : Z → GL (Fin n) (Cinf E)) (χ : Z → ℂ), (∀ W, IsModGrowthInf W → IsModGrowthInf (S W)) → (∀ W, IsModGrowthInf W → ∀ q z g, χ z * S W (g * t z * q) = ∫ x, k q x * (𝐞 (η q x z) : ℂ) * W (g * γ x) ∂ν) → IsKerOpInf (fun W z g => χ z * T (S W) z (g * t z)) := by
  first | (exact @GlobalTheory.JSW.MirCinf.isKerOpInf_comp_rapidFamInf) | (exact GlobalTheory.JSW.MirCinf.isKerOpInf_comp_rapidFamInf) | (intros; apply GlobalTheory.JSW.MirCinf.isKerOpInf_comp_rapidFamInf  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanMatrixSmoothingModerateGrowth
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanMatrixSmoothingModerateGrowth
open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW.MirCinf

theorem smoothMatInf_keeps_modGrowth : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ)
    (α : (Fin n → Fin n → Cinf E) → ℂ), Continuous α → HasCompactSupport α →
    tsupport α ⊆ {x | IsUnit (Matrix.of x)} → ∀ W : GL (Fin n) (Cinf E) → ℂ, IsModGrowthInf W →
    IsModGrowthInf (smoothMatInf α W) :=
  isModGrowthInf_smoothMatInf

end GlobalTheory.JSW.MirCinf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanMatrixSmoothingModerateGrowthStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanMatrixSmoothing_moderateGrowth : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (α : (Fin n → Fin n → Cinf E) → ℂ), Continuous α → HasCompactSupport α → tsupport α ⊆ {x | IsUnit (Matrix.of x)} → ∀ W : GL (Fin n) (Cinf E) → ℂ, IsModGrowthInf W → IsModGrowthInf (smoothMatInf α W) := by
  first | (exact @GlobalTheory.JSW.MirCinf.smoothMatInf_keeps_modGrowth) | (exact GlobalTheory.JSW.MirCinf.smoothMatInf_keeps_modGrowth) | (intros; apply GlobalTheory.JSW.MirCinf.smoothMatInf_keeps_modGrowth  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelOperatorGLnSmoothAffineTranslationSection
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW.MirCinf

theorem kerOpInf_section : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] (σ₀ : Fin n → Fin n → Cinf E) (L : Z →L[ℝ] (Fin n → Fin n → Cinf E)) (χ : Z → ℂ) (α : (Fin n → Fin n → Cinf E) → ℂ), ContDiff ℝ ∞ χ → HasCompactSupport χ → (∀ z ∈ tsupport χ, IsUnit (Matrix.of (σ₀ + L z))) → ContDiff ℝ ∞ α → HasCompactSupport α → tsupport α ⊆ {x | IsUnit (Matrix.of x)} → ∀ T : (GL (Fin n) (Cinf E) → ℂ) → Z → GL (Fin n) (Cinf E) → ℂ, IsKerOpInf T → IsKerOpInf (fun W z g => χ z * T (smoothMatInf α W) z (g * (toGLInf (Matrix.of (σ₀ + L z)))⁻¹)) := by
  intro E _ _ n Z _ _ _ σ₀ L χ α hχ hχc hσ hα hαc hαs T hT
  have hdet : ∀ w : InfinitePlace E, ContDiff ℝ ∞ fun p : Z × (Fin n → Fin n → Cinf E) =>
      (Matrix.of (σ₀ + L p.1)).det w := by
    intro w
    simp only [Matrix.det_apply', Matrix.of_apply, Finset.sum_apply, Pi.mul_apply, Finset.prod_apply]
    refine ContDiff.sum fun s _ => ?_
    refine ContDiff.mul ?_ (contDiff_prod fun i _ => ?_)
    · exact contDiff_const
    have : ContDiff ℝ ∞ fun p : Z × (Fin n → Fin n → Cinf E) => σ₀ + L p.1 :=
      contDiff_const.add (L.contDiff.comp contDiff_fst)
    exact contDiff_pi.1 (contDiff_pi.1 (contDiff_pi.1 this (s i)) i) w
  have hJ : ContDiff ℝ ∞ fun p : Z × (Fin n → Fin n → Cinf E) =>
      ((jacInf (Matrix.of (σ₀ + L p.1)) : ℝ) : ℂ) := by
    simp only [jacInf, Complex.ofReal_prod, Complex.ofReal_pow, Complex.normSq_eq_conj_mul_self]
    exact contDiff_prod fun w _ => ((Complex.conjCLE.contDiff.comp (hdet w)).mul (hdet w)).pow n
  have hΦ : ContDiff ℝ ∞ fun p : Z × (Fin n → Fin n → Cinf E) =>
      χ p.1 * ((jacInf (Matrix.of (σ₀ + L p.1)) : ℝ) : ℂ) * α p.2 :=
    ((hχ.comp contDiff_fst).mul hJ).mul (hα.comp contDiff_snd)
  have hΦc : HasCompactSupport fun p : Z × (Fin n → Fin n → Cinf E) =>
      χ p.1 * ((jacInf (Matrix.of (σ₀ + L p.1)) : ℝ) : ℂ) * α p.2 := by
    refine HasCompactSupport.intro (hχc.isCompact.prod hαc.isCompact) fun p hp => ?_
    rcases not_and_or.1 hp with h | h
    · simp [image_eq_zero_of_notMem_tsupport h]
    · simp [image_eq_zero_of_notMem_tsupport h]
  obtain ⟨X, _, ν, _, κ, τ, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_rapid_superposition_characters' _ _ hΦ hΦc
  obtain ⟨R, hR⟩ := GlobalTheory.T.smoothing_affine_family_eq_integral_kernel E n Z σ₀ L χ α hχc hσ hαc hαs X ν κ τ h1 h2 h3 (fun z a => h4 (z, a))
  exact GlobalTheory.T.archimedeanRapidKernelOperator_comp_rapidFamily E n Z T hT _ _ _ _ _ (GlobalTheory.T.schwartz_integral_bound_smooth E n Z X ν κ τ h1 h2 h3 R σ₀ L) (smoothMatInf α) _ χ
    (GlobalTheory.T.archimedeanMatrixSmoothing_moderateGrowth E n α hα.continuous hαc hαs) hR

end GlobalTheory.JSW.MirCinf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelOperatorGLnSmoothAffineTranslationSectionStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelOperator_GLn_smoothAffineTranslation_section : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] (σ₀ : Fin n → Fin n → Cinf E) (L : Z →L[ℝ] (Fin n → Fin n → Cinf E)) (χ : Z → ℂ) (α : (Fin n → Fin n → Cinf E) → ℂ), ContDiff ℝ ∞ χ → HasCompactSupport χ → (∀ z ∈ tsupport χ, IsUnit (Matrix.of (σ₀ + L z))) → ContDiff ℝ ∞ α → HasCompactSupport α → tsupport α ⊆ {x | IsUnit (Matrix.of x)} → ∀ T : (GL (Fin n) (Cinf E) → ℂ) → Z → GL (Fin n) (Cinf E) → ℂ, IsKerOpInf T → IsKerOpInf (fun W z g => χ z * T (smoothMatInf α W) z (g * (toGLInf (Matrix.of (σ₀ + L z)))⁻¹)) := by
  first | exact @GlobalTheory.JSW.MirCinf.kerOpInf_section | exact GlobalTheory.JSW.MirCinf.kerOpInf_section | (intros; apply GlobalTheory.JSW.MirCinf.kerOpInf_section <;> assumption)
end
