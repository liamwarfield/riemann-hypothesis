module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.MapMulInvEqOne

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.QuaternaryFourierEqAdelic
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.D.FourierTransformSplitting

variable {F : Type} [Field F] [NumberField F]

private theorem psi_add (a b : A F) : ψ (a + b) = ψ a * ψ b := by
  simp [ψ, AddChar.map_add_eq_mul]

private theorem cons_eq {n : ℕ} :
    (fun p : A F × (Fin n → A F) => (Fin.cons p.1 p.2 : Fin (n + 1) → A F)) =
      ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => A F) 0).symm := by
  funext p
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [MeasurableEquiv.piFinSuccAbove, Fin.consEquiv]

private theorem fub_mp {n : ℕ} : MeasurePreserving
    (fun p : A F × (Fin n → A F) => (Fin.cons p.1 p.2 : Fin (n + 1) → A F))
    ((adeleMeasure F).prod (adeleMeasurePi F)) (adeleMeasurePi F) := by
  rw [cons_eq]
  exact (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => adeleMeasure F) 0).symm

private theorem fub_emb {n : ℕ} : MeasurableEmbedding
    (fun p : A F × (Fin n → A F) => (Fin.cons p.1 p.2 : Fin (n + 1) → A F)) := by
  rw [cons_eq]
  exact (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => A F) 0).symm.measurableEmbedding

private theorem fub {n : ℕ} {f : (Fin (n + 1) → A F) → ℂ} (hf : Integrable f (adeleMeasurePi F)) :
    Integrable (fun p : A F × (Fin n → A F) => f (Fin.cons p.1 p.2))
        ((adeleMeasure F).prod (adeleMeasurePi F)) ∧
      ∫ x, f x ∂(adeleMeasurePi F) = ∫ p : A F × (Fin n → A F), f (Fin.cons p.1 p.2)
        ∂((adeleMeasure F).prod (adeleMeasurePi F)) :=
  ⟨(fub_mp.integrable_comp_emb fub_emb).2 hf, (fub_mp.integral_comp fub_emb f).symm⟩

private theorem one_int (h : (Fin 1 → A F) → ℂ) :
    ∫ a, h a ∂(adeleMeasurePi F) = ∫ s : A F, h (fun _ => s) ∂(adeleMeasure F) :=
  ((measurePreserving_funUnique (adeleMeasure F) (Fin 1)).symm.integral_comp' h).symm

private theorem reindex_mem {ι κ : Type} [Fintype ι] [Fintype κ] (e : κ ≃ ι)
    {f : (κ → A F) → ℂ} (hf : f ∈ schwartzBruhatPi (K := F) (ι := κ)) :
    (fun x : ι → A F => f (x ∘ e)) ∈ schwartzBruhatPi (K := F) (ι := ι) := by
  have h := GroundTheory.Heights₂.Theta.comp_mulVec_mem_schwartzBruhatPi
    ((1 : Matrix ι ι F).submatrix e id) ((1 : Matrix ι ι F).submatrix id e)
    (by rw [Matrix.submatrix_mul_equiv]; simp) (by
      ext i j
      simp [Matrix.mul_apply, Matrix.one_apply]) hf
  convert h using 2
  rename_i x
  congr 1
  ext k
  simp [Matrix.mulVec, dotProduct, Matrix.one_apply]

private theorem elim_cons (a : Fin 1 → A F) (y : Fin 3 → A F) :
    (Sum.elim a y) ∘ (finSumFinEquiv (m := 1) (n := 3)).symm = (Fin.cons (a 0) y : Fin 4 → A F) := by
  ext i
  fin_cases i <;> rfl

private theorem g_mem {φ : (Fin 4 → A F) → ℂ} (hφ : φ ∈ schwartzBruhatPi (K := F) (ι := Fin 4))
    (η : Fin 3 → A F) :
    (fun a : Fin 1 → A F => adelicFourierPi F (fun y : Fin 3 → A F => φ (Fin.cons (a 0) y)) η)
      ∈ schwartzBruhatPi (K := F) (ι := Fin 1) := by
  have h1 : (fun x : (Fin 1 ⊕ Fin 3) → A F => φ (x ∘ (finSumFinEquiv (m := 1) (n := 3)).symm))
      ∈ schwartzBruhatPi (K := F) (ι := Fin 1 ⊕ Fin 3) :=
    reindex_mem (finSumFinEquiv (m := 1) (n := 3)).symm hφ
  have h2 := GroundTheory.Heights₂.Theta.partialFourierPi_mem h1
  have h3 := reindex_mem (Equiv.sumComm (Fin 1) (Fin 3)) h2
  have h4 := GroundTheory.Heights₂.Theta.schwartzBruhatPi_sumElim_mem h3 η
  convert h4 using 2
  rename_i a
  have e : (Sum.elim η a : (Fin 3 ⊕ Fin 1) → A F) ∘ (Equiv.sumComm (Fin 1) (Fin 3)) = Sum.elim a η := by
    ext s
    cases s <;> rfl
  rw [e, GroundTheory.Heights₂.Theta.partialFourierPi_sumElim]
  simp only [elim_cons]

private theorem slice_mem {φ : (Fin 4 → A F) → ℂ} (hφ : φ ∈ schwartzBruhatPi (K := F) (ι := Fin 4))
    (b : A F) :
    (fun y : Fin 3 → A F => φ (Fin.cons b y)) ∈ schwartzBruhatPi (K := F) (ι := Fin 3) := by
  have h1 : (fun x : (Fin 1 ⊕ Fin 3) → A F => φ (x ∘ (finSumFinEquiv (m := 1) (n := 3)).symm))
      ∈ schwartzBruhatPi (K := F) (ι := Fin 1 ⊕ Fin 3) :=
    reindex_mem (finSumFinEquiv (m := 1) (n := 3)).symm hφ
  have h4 := GroundTheory.Heights₂.Theta.schwartzBruhatPi_sumElim_mem h1 (fun _ => b)
  convert h4 using 2
  rename_i y
  rw [elim_cons]

private theorem ft_split {φ : (Fin 4 → A F) → ℂ} (hφ : φ ∈ schwartzBruhatPi (K := F) (ι := Fin 4))
    (ξ : Fin 4 → A F) :
    adelicFourierPi F φ ξ = ∫ a : A F,
      adelicFourierPi F (fun y : Fin 3 → A F => φ (Fin.cons a y)) (Fin.tail ξ) * ψ (a * ξ 0)
        ∂(adeleMeasure F) := by
  have hint := integrable_mul_adelicChar_pi (integrable_of_mem_schwartzBruhatPi hφ) ξ
  obtain ⟨h1, h2⟩ := fub hint
  rw [adelicFourierPi, h2, integral_prod _ h1]
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  simp only [adelicFourierPi]
  rw [← integral_mul_const]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [Fin.sum_univ_succ (n := 3), Fin.cons_zero, Fin.cons_succ, Fin.tail]
  have := psi_add (a * ξ 0) (∑ i : Fin 3, y i * ξ i.succ)
  simp only [ψ] at this ⊢
  rw [this, mul_assoc]
  exact congrArg _ (mul_comm _ _)

private theorem quaternaryFourier_eq_adelic (δ : F) (f : V4 F → ℂ) (v : V4 F) (s : A F) :
    ft4 δ f (Function.update v 1 s) =
      adelicFourierPi F f ![-s, -v 0, 2 * v 2, -(2 * (rt δ * v 3))] := by
  rw [ft4, adelicFourierPi]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have e : B4 δ x (Function.update v 1 s) =
      ∑ i, x i * (![-s, -v 0, 2 * v 2, -(2 * (rt δ * v 3))] : Fin 4 → A F) i := by
    simp [B4, Fin.sum_univ_four]
    ring
  simp only [ψ, e]

private theorem g_hat (δ : F) (φ : S4 F) (v : V4 F) (η : Fin 3 → A F)
    (hη : η = ![-v 0, 2 * v 2, -(2 * (rt δ * v 3))]) (s : A F) :
    ft4 δ φ.1 (Function.update v 1 s) = adelicFourierPi F
      (fun a : Fin 1 → A F => adelicFourierPi F (fun y : Fin 3 → A F => φ.1 (Fin.cons (a 0) y)) η)
      (fun _ => -s) := by
  have ht : Fin.tail (![-s, -v 0, 2 * v 2, -(2 * (rt δ * v 3))] : Fin 4 → A F) = η := by
    rw [hη]
    ext i
    fin_cases i <;> rfl
  rw [quaternaryFourier_eq_adelic, ft_split φ.2, adelicFourierPi, one_int, ht]
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  simp [ψ]

end UpperTheory.ConvolutionTheory.R2.D.FourierTransformSplitting

open UpperTheory.ConvolutionTheory.R2.D.FourierTransformSplitting in
theorem UpperTheory.ConvolutionTheory.R2.D.hatW :
    ∀ (F : Type) [Field F] [NumberField F] (δ : F) (φ : S4 F) (v : V4 F), δ ≠ 0 → hat (ft4 δ φ.1) v =
      ∫ z : Fin 2 → A F, hat φ.1 ![-v 1, v 0, z 0, z 1] * ψ (2 * (z 0 * v 2 - rt δ * (z 1 * v 3))) ∂(adeleMeasurePi F) := by
  intro F _ _ δ φ v _
  obtain ⟨η, hη⟩ : ∃ η : Fin 3 → A F, η = ![-v 0, 2 * v 2, -(2 * (rt δ * v 3))] := ⟨_, rfl⟩
  have hg := g_mem φ.2 η
  have inv := congrFun (adelicFourierPi_adelicFourierPi hg) (fun _ => v 1)
  rw [adelicFourierPi, one_int] at inv
  have hB : hat (ft4 δ φ.1) v =
      adelicFourierPi F (fun y : Fin 3 → A F => φ.1 (Fin.cons (-v 1) y)) η := by
    refine Eq.trans ?_ inv
    rw [hat, ← integral_neg_eq_self]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    simp only [g_hat δ φ v η hη]
    simp [ψ]
  rw [hB, adelicFourierPi]
  have hint := integrable_mul_adelicChar_pi
    (integrable_of_mem_schwartzBruhatPi (slice_mem φ.2 (-v 1))) η
  obtain ⟨h1, h2⟩ := fub hint
  rw [h2, integral_prod_symm _ h1]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only []
  rw [hat, ← integral_mul_const]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  have e1 : (Fin.cons (-v 1) (Fin.cons s z : Fin 3 → A F) : Fin 4 → A F) =
      Function.update ![-v 1, v 0, z 0, z 1] 1 s := by
    ext i
    fin_cases i <;> simp [Function.update] <;> rfl
  have e2 : ∑ i, (Fin.cons s z : Fin 3 → A F) i * η i =
      -(s * v 0) + 2 * (z 0 * v 2 - rt δ * (z 1 * v 3)) := by
    have hc : (Fin.cons s z : Fin 3 → A F) 2 = z 1 := rfl
    simp [hη, Fin.sum_univ_three, hc]
    ring
  have := psi_add (-(s * v 0)) (2 * (z 0 * v 2 - rt δ * (z 1 * v 3)))
  simp only [ψ] at this ⊢
  simp only [e1, e2, this]
  simp [mul_assoc]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.HatN
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.D.hatN :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D), ∀ b φ v, hat (W.Om (nU b) φ).1 v = ψ (b * (v 2 ^ 2 - rt D.δ * v 3 ^ 2)) * hat φ.1 (Function.update v 1 (v 1 + b * v 0)) := by
  intro F E _ _ _ _ _ _ _ D W b φ v
  have hψ : ∀ x y : A F, ψ (x + y) = ψ x * ψ y := by
    intro x y
    simp only [ψ, AddChar.map_add_eq_mul, Circle.coe_mul]
  have hq : ∀ s : A F, q4 D.δ (Function.update v 1 s) = v 2 ^ 2 - rt D.δ * v 3 ^ 2 - s * v 0 := by
    intro s
    simp [q4]
  unfold hat
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  have h : ψ (b * q4 D.δ (Function.update v 1 s)) * ψ (-(s * v 1)) =
      ψ (b * (v 2 ^ 2 - rt D.δ * v 3 ^ 2)) * ψ (-(s * (v 1 + b * v 0))) := by
    rw [← hψ, ← hψ, hq]
    congr 1
    ring
  simp only [W.Om_n, Function.update_idem, Function.update_self]
  linear_combination (φ.1 (Function.update v 1 s)) * h
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.Sl2InductionUnipotentWeyl
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.FinSumFinEquiv
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.D.SliceScalingEquiv

private theorem slice_mem {F : Type} [Field F] [NumberField F] {f : V4 F → ℂ}
    (hf : f ∈ schwartzBruhatPi (K := F) (ι := Fin 4)) (a b : A F) :
    (fun z : Fin 2 → A F => f ![a, b, z 0, z 1]) ∈ schwartzBruhatPi (K := F) (ι := Fin 2) := by
  let e : Fin 2 ⊕ Fin 2 ≃ Fin 4 := finSumFinEquiv
  let M : Matrix (Fin 4) (Fin 2 ⊕ Fin 2) F := (1 : Matrix (Fin 4) (Fin 4) F).submatrix id e
  let N : Matrix (Fin 2 ⊕ Fin 2) (Fin 4) F := (1 : Matrix (Fin 4) (Fin 4) F).submatrix e id
  have hNM : N * M = 1 := by
    ext i j
    simp [M, N, Matrix.mul_apply, Matrix.one_apply]
  have hMN : M * N = 1 := by
    ext i j
    have h := Equiv.sum_comp e
      (fun k => (1 : Matrix (Fin 4) (Fin 4) F) i k * (1 : Matrix (Fin 4) (Fin 4) F) k j)
    rw [Matrix.mul_apply]
    refine h.trans ?_
    simp [Matrix.one_apply]
  have hv : ∀ x : Fin 2 ⊕ Fin 2 → A F, M.map (algebraMap F (A F)) *ᵥ x = fun i => x (e.symm i) := by
    intro x
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, M, Matrix.submatrix_apply, id]
    rw [← Equiv.sum_comp e.symm]
    simp [Matrix.one_apply, apply_ite]
  have h1 := GroundTheory.Heights₂.Theta.comp_mulVec_mem_schwartzBruhatPi M N hNM hMN hf
  have h2 := GroundTheory.Heights₂.Theta.schwartzBruhatPi_sumElim_mem h1 ![a, b]
  have h3 : (fun z : Fin 2 → A F => f ![a, b, z 0, z 1]) =
      fun x : Fin 2 → A F => f (M.map (algebraMap F (A F)) *ᵥ Sum.elim ![a, b] x) := by
    funext z
    rw [hv]
    congr 1
    funext i
    fin_cases i <;> simp [e, finSumFinEquiv] <;> rfl
  rw [h3]
  exact h2

private def scaleEquiv {F : Type} [Field F] [NumberField F] (δ : F) (hδ : δ ≠ 0) :
    (Fin 2 → F) ≃ (Fin 2 → F) where
  toFun ξ := ![2 * ξ 0, -2 * δ * ξ 1]
  invFun ξ := ![ξ 0 / 2, -(ξ 1) / (2 * δ)]
  left_inv ξ := by
    have h2 : (2 : F) ≠ 0 := two_ne_zero
    funext i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      field_simp
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      field_simp
  right_inv ξ := by
    have h2 : (2 : F) ≠ 0 := two_ne_zero
    funext i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      field_simp
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      field_simp

end UpperTheory.ConvolutionTheory.R2.D.SliceScalingEquiv

open UpperTheory.ConvolutionTheory.R2.D.SliceScalingEquiv in
theorem UpperTheory.ConvolutionTheory.R2.D.rowW :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D), ∀ (r₀ r₁ : F) φ, ThRow (rt r₀) (rt r₁) (W.Om (wW F) φ).1 = ThRow (rt (-r₁)) (rt r₀) φ.1 := by
  intro F E _ _ _ _ _ _ _ D W r₀ r₁ φ
  have hδ : D.δ ≠ 0 := by
    intro h0
    have hθ : D.θ = 0 := by
      have h := D.sq
      rw [h0, map_zero] at h
      exact pow_eq_zero_iff (two_ne_zero) |>.1 h
    have hb : D.b 1 = 0 := by rw [D.b1, hθ]
    exact D.b.ne_zero 1 hb
  have hS : (W.Om (wW F) φ).1 = ft4 D.δ φ.1 := funext (W.Om_w φ)
  set G : (Fin 2 → A F) → ℂ := fun z => hat φ.1 ![-rt r₁, rt r₀, z 0, z 1] with hGdef
  have hG : G ∈ schwartzBruhatPi (K := F) (ι := Fin 2) :=
    slice_mem (UpperTheory.ConvolutionTheory.R2.D.hatMem F φ).1 (-rt r₁) (rt r₀)
  have hR : ThRow (rt (-r₁)) (rt r₀) φ.1 = ∑' ξ : Fin 2 → F, G fun i => algebraMap F (A F) (ξ i) := by
    simp only [ThRow, hGdef, map_neg]
  rw [hR, tsum_algebraMap_eq_tsum_adelicFourierPi hG,
    ← (scaleEquiv D.δ hδ).tsum_eq (fun ξ : Fin 2 → F => adelicFourierPi F G fun i => algebraMap F (A F) (ξ i))]
  unfold ThRow
  refine tsum_congr fun ξ => ?_
  rw [hS, UpperTheory.ConvolutionTheory.R2.D.hatW F D.δ φ _ hδ]
  simp only [adelicFourierPi, Fin.sum_univ_two]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [hGdef, ψ, scaleEquiv, Equiv.coe_fn_mk]
  have key : 2 * (z 0 * rt (ξ 0) - rt D.δ * (z 1 * rt (ξ 1))) =
      z 0 * algebraMap F (A F) (2 * ξ 0) + z 1 * algebraMap F (A F) (-2 * D.δ * ξ 1) := by
    simp only [rt, map_mul, map_neg, map_ofNat]
    ring
  show hat φ.1 ![-rt r₁, rt r₀, z 0, z 1] *
      ((adelicChar F (2 * (z 0 * rt (ξ 0) - rt D.δ * (z 1 * rt (ξ 1)))) : Circle) : ℂ) =
    hat φ.1 ![-rt r₁, rt r₀, z 0, z 1] *
      ((adelicChar F (z 0 * algebraMap F (A F) (2 * ξ 0) +
        z 1 * algebraMap F (A F) (-2 * D.δ * ξ 1)) : Circle) : ℂ)
  rw [key]
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.D.SL2BruhatGenerators

section Gen

variable {F : Type} [Field F]

private def nF (b : F) : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, b; 0, 1], by simp [Matrix.det_fin_two]⟩


variable (F) in
private def wF : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩

private theorem coe_nF (b : F) : (nF b).1 = !![1, b; 0, 1] := rfl

private theorem coe_wF : (wF F).1 = !![0, 1; -1, 0] := rfl

private theorem decomp (γ : Matrix.SpecialLinearGroup (Fin 2) F) (hc : γ.1 1 0 ≠ 0) :
    γ = nF ((γ.1 0 0 - 1) / γ.1 1 0) * (wF F * nF (-(γ.1 1 0)) * (wF F * wF F * wF F)) *
      nF ((γ.1 1 1 - 1) / γ.1 1 0) := by
  have hdet := γ.det_coe
  rw [Matrix.det_fin_two] at hdet
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_nF, coe_wF]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;>
    first | ring1 | linear_combination hdet | linear_combination -hdet

private theorem decomp0 (γ : Matrix.SpecialLinearGroup (Fin 2) F) :
    γ = (γ * wF F) * (wF F * wF F * wF F) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_wF]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem specialLinearGroup_two_induction_on_unipotent_weyl (P : Matrix.SpecialLinearGroup (Fin 2) F → Prop)
    (hmul : ∀ a b, P a → P b → P (a * b)) (hn : ∀ b, P (nF b)) (hw : P (wF F))
    (γ : Matrix.SpecialLinearGroup (Fin 2) F) : P γ := by
  have hw3 : P (wF F * wF F * wF F) := hmul _ _ (hmul _ _ hw hw) hw
  have key : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) F, γ.1 1 0 ≠ 0 → P γ := by
    intro γ hc
    rw [decomp γ hc]
    exact hmul _ _ (hmul _ _ (hn _) (hmul _ _ (hmul _ _ hw (hn _)) hw3)) (hn _)
  by_cases hc : γ.1 1 0 = 0
  · have hdet := γ.det_coe
    rw [Matrix.det_fin_two, hc] at hdet
    have hd : γ.1 1 1 ≠ 0 := by
      intro h
      rw [h] at hdet
      simp at hdet
    rw [decomp0 γ]
    refine hmul _ _ (key _ ?_) hw3
    have h10 : (γ * wF F).1 1 0 = -γ.1 1 1 := by
      rw [Matrix.SpecialLinearGroup.coe_mul, coe_wF, Matrix.mul_apply, Fin.sum_univ_two]
      simp
    rw [h10]
    exact neg_ne_zero.mpr hd
  · exact key γ hc

end Gen

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] {D : Dat F E} (W : Weil D)

private theorem ratS_coe (g : Matrix.SpecialLinearGroup (Fin 2) F) (i j : Fin 2) :
    (ratS F g).1 i j = rt (g.1 i j) := rfl

private theorem ratS_nF (b : F) : ratS F (nF b) = nU (rt b) := by
  apply Subtype.ext
  ext i j
  rw [ratS_coe, coe_nF]
  fin_cases i <;> fin_cases j <;> simp [nU]

private theorem ratS_wF : ratS F (wF F) = wW F := by
  apply Subtype.ext
  ext i j
  rw [ratS_coe, coe_wF]
  fin_cases i <;> fin_cases j <;> simp [wW]

private theorem psi_rt (x : F) : ψ (rt x) = 1 := by
  simp [ψ, adelicChar_algebraMap]

private def Good (γ : Matrix.SpecialLinearGroup (Fin 2) F) : Prop :=
  ∀ (r : Fin 2 → F) (φ : S4 F), ThRow (rt (r 0)) (rt (r 1)) (W.Om (ratS F γ) φ).1 =
    ThRow (rt ((r ᵥ* γ.1) 0)) (rt ((r ᵥ* γ.1) 1)) φ.1

private theorem good_mul (a b : Matrix.SpecialLinearGroup (Fin 2) F)
    (ha : Good W a) (hb : Good W b) : Good W (a * b) := by
  intro r φ
  rw [map_mul, map_mul, Module.End.mul_apply, ha r, hb (r ᵥ* a.1) φ,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.vecMul_vecMul]

private theorem good_n (b : F) : Good W (nF b) := by
  intro r φ
  rw [ratS_nF]
  have h0 : (r ᵥ* (nF b).1) 0 = r 0 := by
    rw [coe_nF]
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  have h1 : (r ᵥ* (nF b).1) 1 = r 1 + b * r 0 := by
    rw [coe_nF]
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    ring
  rw [h0, h1]
  unfold ThRow
  refine tsum_congr fun ξ => ?_
  rw [UpperTheory.ConvolutionTheory.R2.D.hatN F E D W (rt b) φ]
  have hψ : ψ (rt b * ((![rt (r 0), rt (r 1), rt (ξ 0), rt (ξ 1)] : V4 F) 2 ^ 2 -
      rt D.δ * (![rt (r 0), rt (r 1), rt (ξ 0), rt (ξ 1)] : V4 F) 3 ^ 2)) = 1 := by
    have : rt b * ((![rt (r 0), rt (r 1), rt (ξ 0), rt (ξ 1)] : V4 F) 2 ^ 2 -
        rt D.δ * (![rt (r 0), rt (r 1), rt (ξ 0), rt (ξ 1)] : V4 F) 3 ^ 2) =
        rt (b * (ξ 0 ^ 2 - D.δ * ξ 1 ^ 2)) := by
      simp [map_mul, map_sub, map_pow]
    rw [this, psi_rt]
  rw [hψ, one_mul]
  congr 1
  funext i
  fin_cases i <;> simp [Function.update, map_add (f := _), map_mul]

private theorem good_w : Good W (wF F) := by
  intro r φ
  rw [ratS_wF]
  have h0 : (r ᵥ* (wF F).1) 0 = -r 1 := by
    rw [coe_wF]
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  have h1 : (r ᵥ* (wF F).1) 1 = r 0 := by
    rw [coe_wF]
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  rw [h0, h1]
  exact UpperTheory.ConvolutionTheory.R2.D.rowW F E D W (r 0) (r 1) φ

private theorem good_all (γ : Matrix.SpecialLinearGroup (Fin 2) F) : Good W γ :=
  specialLinearGroup_two_induction_on_unipotent_weyl (Good W) (good_mul W) (good_n W) (good_w W) γ

end Main

end UpperTheory.ConvolutionTheory.R2.D.SL2BruhatGenerators

theorem UpperTheory.ConvolutionTheory.R2.D.row :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D), ∀ γ (r : Fin 2 → F) φ, ThRow (rt (r 0)) (rt (r 1)) (W.Om (ratS F γ) φ).1 =
      ThRow (rt ((r ᵥ* γ.1) 0)) (rt ((r ᵥ* γ.1) 1)) φ.1 := by
  intro F E _ _ _ _ _ _ _ D W γ r φ
  exact UpperTheory.ConvolutionTheory.R2.D.SL2BruhatGenerators.good_all W γ r φ
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.IntegralMulLeftAdele
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical

private theorem integral_mul_left_adele {F : Type} [Field F] [NumberField F] (a : (A F)ˣ) (g : A F → ℂ) :
    ∫ s, g ((a : A F) * s) ∂(adeleMeasure F) = (((ab a)⁻¹ : ℝ) : ℂ) * ∫ s, g s ∂(adeleMeasure F) := by
  have hpos : 0 ≤ ((IdeleGroup.ideleModule F a : ℝ))⁻¹ := inv_nonneg.mpr (IdeleGroup.ideleModule F a).2.le
  have hmap := map_smul_adeleMeasure (K := F) a
  have he : MeasurableEmbedding (fun x : A F => a • x) :=
    (Homeomorph.smul a).measurableEmbedding
  have h1 : ∫ s, g ((a : A F) * s) ∂(adeleMeasure F) =
      ∫ s, g s ∂((adeleMeasure F).map (fun x : A F => a • x)) :=
    (he.integral_map g).symm
  rw [h1, hmap, integral_smul_measure, ENNReal.toReal_ofReal hpos]
  rw [Complex.real_smul]
  rfl

theorem UpperTheory.ConvolutionTheory.R2.D.hatM :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D), ∀ (a : (A F)ˣ) φ v, hat (W.Om (mD a) φ).1 v = ((W.η.1 a : ℂˣ) : ℂ) * ((ab a : ℝ) : ℂ) *
      hat φ.1 ![a * v 0, ((a⁻¹ : (A F)ˣ) : A F) * v 1, a * v 2, a * v 3] := by
  intro F E _ _ _ _ _ _ _ D W a φ v
  have hab : ((ab a : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (IdeleGroup.ideleModule F a).2
  set w : V4 F := ![a * v 0, ((a⁻¹ : (A F)ˣ) : A F) * v 1, a * v 2, a * v 3] with hw
  have hpt : ∀ s : A F, (fun i => (a : A F) * Function.update v 1 s i) =
      Function.update w 1 ((a : A F) * s) := by
    intro s
    funext i
    fin_cases i <;> simp [hw, Function.update]
  have hch : ∀ s : A F, (a : A F) * s * w 1 = s * v 1 := by
    intro s
    have : w 1 = ((a⁻¹ : (A F)ˣ) : A F) * v 1 := by simp [hw]
    rw [this, mul_mul_mul_comm, Units.mul_inv, one_mul]
  obtain ⟨G, hG⟩ : ∃ G : A F → ℂ, G = fun r => φ.1 (Function.update w 1 r) * ψ (-(r * w 1)) := ⟨_, rfl⟩
  have hL : hat (W.Om (mD a) φ).1 v =
      ∫ s, ((W.η.1 a : ℂˣ) : ℂ) * ((ab a ^ 2 : ℝ) : ℂ) * G ((a : A F) * s) ∂(adeleMeasure F) := by
    unfold hat
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp only [W.Om_m, hpt s, hG, hch s]
    ring
  have hR : hat φ.1 w = ∫ s, G s ∂(adeleMeasure F) := by
    rw [hG]
    rfl
  rw [hL, integral_const_mul, integral_mul_left_adele, hR]
  push_cast
  field_simp
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.ThetaSq
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem psi_add (a b : A F) : ψ (a + b) = ψ a * ψ b := by
  simp [ψ, AddChar.map_add_eq_mul]

private theorem co_mkE (D : Dat F E) (u t : A F) : D.co (D.mkE u t) = ![u, t] := by
  letI : Algebra (A F) (A E) := AdeleBaseChange.algebraAdeleRing
  have h : D.mkE u t = ∑ i, (![u, t] : Fin 2 → A F) i • AdeleBaseChange.adeleBasis D.b i := by
    rw [Fin.sum_univ_two]
    simp only [AdeleBaseChange.adeleBasis_apply, D.b0, D.b1, Algebra.smul_def, map_one, Dat.mkE,
      AdeleBaseChange.algebraMap_adeleRing]
    simp
  unfold Dat.co
  rw [h, Module.Basis.repr_sum_self]

private theorem bar_mkE (D : Dat F E) (u t : A F) : D.bar (D.mkE u t) = D.mkE u (-t) := by
  have h1 : ∀ a : A F, D.bar (AdeleBaseChange.adeleMap F E a) = AdeleBaseChange.adeleMap F E a :=
    fun a => AdeleBaseChange.smul_adeleMap D.σ a
  have h2 : D.bar (rt D.θ) = - rt D.θ := by
    have : D.bar (rt D.θ) = rt (D.σ D.θ) := AdeleBaseChange.smul_algebraMap D.σ D.θ
    rw [this, D.conj]; simp [UpperTheory.ConvolutionTheory.R2.rt]
  simp only [Dat.mkE, map_add (f := _), map_mul, h1, h2, map_neg]
  ring

private theorem theta_sq (D : Dat F E) :
    rt D.θ * rt D.θ = AdeleBaseChange.adeleMap F E (rt D.δ) := by
  rw [UpperTheory.ConvolutionTheory.R2.rt, UpperTheory.ConvolutionTheory.R2.rt, AdeleBaseChange.adeleMap_algebraMap, ← D.sq, ← map_mul, pow_two]

private theorem nu_gl (b : A E) : nu F (gl (nU b)) = 1 := by
  have h : Matrix.GeneralLinearGroup.det (gl (nU b)) = 1 := by
    ext
    simp [Matrix.GeneralLinearGroup.det]
  simp [nu, h]

private theorem ab_one : ab (1 : (A F)ˣ) = 1 := by simp [ab]

private theorem gl_val (b : A E) : (gl (nU b)).val = !![1, b; 0, 1] := rfl

private theorem gl_inv (b : A E) : (gl (nU b))⁻¹ = gl (nU (-b)) := by
  apply inv_eq_of_mul_eq_one_right
  apply Units.ext
  rw [Units.val_mul, gl_val, gl_val, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem act_nU (D : Dat F E) (u t s z₀ z₁ : A F) :
    D.act (gl (nU (D.mkE u t)))⁻¹ ![0, s, z₀, z₁] =
      ![0, s - 2 * (u * z₀ - UpperTheory.ConvolutionTheory.R2.rt D.δ * (t * z₁)), z₀, z₁] := by
  rw [gl_inv]
  have hb : D.bar (-D.mkE u t) = - D.mkE u (-t) := by rw [map_neg, bar_mkE]
  have h0 : D.mkE 0 0 = 0 := by simp [Dat.mkE]
  have hθ := theta_sq D
  have e11 : ((gl (nU (-D.mkE u t))).val * D.herm ![0, s, z₀, z₁] *
      ((gl (nU (-D.mkE u t))).val.map D.bar)ᵀ) 1 1 = 0 := by
    rw [gl_val]
    simp [Dat.herm, Matrix.mul_apply, Fin.sum_univ_two, h0]
  have e01 : ((gl (nU (-D.mkE u t))).val * D.herm ![0, s, z₀, z₁] *
      ((gl (nU (-D.mkE u t))).val.map D.bar)ᵀ) 0 1 = D.mkE z₀ z₁ := by
    rw [gl_val]
    simp [Dat.herm, Matrix.mul_apply, Fin.sum_univ_two, h0]
  have e00 : ((gl (nU (-D.mkE u t))).val * D.herm ![0, s, z₀, z₁] *
      ((gl (nU (-D.mkE u t))).val.map D.bar)ᵀ) 0 0 =
      D.mkE (s - 2 * (u * z₀ - UpperTheory.ConvolutionTheory.R2.rt D.δ * (t * z₁))) 0 := by
    rw [gl_val]
    simp [Dat.herm, Matrix.mul_apply, Fin.sum_univ_two, h0, hb]
    simp only [Dat.mkE, map_sub, map_mul, map_add (f := _), map_neg, map_zero, map_ofNat]
    linear_combination (2 * AdeleBaseChange.adeleMap F E t * AdeleBaseChange.adeleMap F E z₁) * hθ
  have z0 : D.co 0 = ![0, 0] := by rw [← h0, co_mkE]
  rw [Dat.act, Dat.unherm, e11, e01, e00, co_mkE, co_mkE, z0]
  ext i
  fin_cases i <;> simp

end SlopeTestRemainingChoices

theorem UpperTheory.ConvolutionTheory.R2.D.hatNE :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D), ∀ u t φ x z₀ z₁, hat (W.L (gl (nU (D.mkE u t))) φ).1 ![0, x, z₀, z₁] =
      ψ (-(x * (2 * (u * z₀ - rt D.δ * (t * z₁))))) * hat φ.1 ![0, x, z₀, z₁] := by
  intro F E _ _ _ _ _ _ _ D W u t φ x z₀ z₁
  set T : A F := 2 * (u * z₀ - rt D.δ * (t * z₁)) with hT
  have hup : ∀ s : A F, Function.update (![0, x, z₀, z₁] : V4 F) 1 s = ![0, s, z₀, z₁] := by
    intro s
    ext i
    fin_cases i <;> simp
  set g : A F → ℂ := fun s => φ.1 ![0, s, z₀, z₁] * ψ (-(s * x)) with hg
  have hR : hat φ.1 ![0, x, z₀, z₁] = ∫ s, g s ∂(adeleMeasure F) := by
    simp only [hat, hup, hg]
    rfl
  have hL : hat (W.L (gl (nU (D.mkE u t))) φ).1 ![0, x, z₀, z₁] =
      ∫ s, ψ (-(x * T)) * g (s - T) ∂(adeleMeasure F) := by
    simp only [hat, hup]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    have e : ψ (-(s * x)) = ψ (-(x * T)) * ψ (-((s - T) * x)) := by
      rw [← psi_add]; congr 1; ring
    simp only [W.L_apply, nu_gl, act_nU, hg, ← hT]
    simp [e, ab_one]
    ring
  rw [hL, hR, integral_const_mul, integral_sub_right_eq_self g T]
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.hatSt :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D), St.Hat W := by
  intro F E _ _ _ _ _ _ _ D W
  have hδ : D.δ ≠ 0 := by
    intro h0
    have hθ : D.θ = 0 := by
      have h := D.sq
      rw [h0, map_zero] at h
      exact pow_eq_zero_iff (two_ne_zero) |>.mp h
    exact D.b.ne_zero 1 (by rw [D.b1, hθ])
  refine
    { n := _root_.UpperTheory.ConvolutionTheory.R2.D.hatN F E D W
      m := _root_.UpperTheory.ConvolutionTheory.R2.D.hatM F E D W
      w := ?_
      nE := _root_.UpperTheory.ConvolutionTheory.R2.D.hatNE F E D W
      aE := _root_.UpperTheory.ConvolutionTheory.R2.D.hatAE F E D W
      mem := fun φ => (_root_.UpperTheory.ConvolutionTheory.R2.D.hatMem F φ).1
      th := fun φ => (_root_.UpperTheory.ConvolutionTheory.R2.D.hatMem F φ).2
      row := _root_.UpperTheory.ConvolutionTheory.R2.D.row F E D W }
  intro φ v
  have h : (W.Om (wW F) φ).1 = ft4 D.δ φ.1 := funext (W.Om_w φ)
  rw [h]
  exact _root_.UpperTheory.ConvolutionTheory.R2.D.hatW F D.δ φ v hδ
