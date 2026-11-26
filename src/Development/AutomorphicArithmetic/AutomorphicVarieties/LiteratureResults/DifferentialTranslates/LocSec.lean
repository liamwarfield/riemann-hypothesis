module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.SecondFromFirstStatement
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.IntegralityGoodReduction

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.LocSec
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af Filter Topology
open scoped ContDiff

namespace UpperTheory.V.Lit.Dr

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private def jor (X Y : HV E a) : HV E a :=
  ⟨toL (Matrix.of X.1 * Matrix.of Y.1 + Matrix.of Y.1 * Matrix.of X.1), by
    have hX : star (Matrix.of X.1) = Matrix.of X.1 := X.2
    have hY : star (Matrix.of Y.1) = Matrix.of Y.1 := Y.2
    change star (Matrix.of X.1 * Matrix.of Y.1 + Matrix.of Y.1 * Matrix.of X.1) =
      Matrix.of X.1 * Matrix.of Y.1 + Matrix.of Y.1 * Matrix.of X.1
    rw [star_add, star_mul, star_mul, hX, hY, add_comm]⟩

private def jorL : HV E a →ₗ[ℝ] HV E a →ₗ[ℝ] HV E a :=
  LinearMap.mk₂ ℝ jor
    (fun X X' Y => Subtype.ext (by
      change (Matrix.of X.1 + Matrix.of X'.1) * Matrix.of Y.1 + Matrix.of Y.1 * (Matrix.of X.1 + Matrix.of X'.1) =
        (Matrix.of X.1 * Matrix.of Y.1 + Matrix.of Y.1 * Matrix.of X.1) +
          (Matrix.of X'.1 * Matrix.of Y.1 + Matrix.of Y.1 * Matrix.of X'.1)
      rw [add_mul, mul_add]; abel))
    (fun c X Y => Subtype.ext (by
      change (c • Matrix.of X.1) * Matrix.of Y.1 + Matrix.of Y.1 * (c • Matrix.of X.1) =
        c • (Matrix.of X.1 * Matrix.of Y.1 + Matrix.of Y.1 * Matrix.of X.1)
      rw [smul_mul_assoc, mul_smul_comm, smul_add]))
    (fun X Y Y' => Subtype.ext (by
      change Matrix.of X.1 * (Matrix.of Y.1 + Matrix.of Y'.1) + (Matrix.of Y.1 + Matrix.of Y'.1) * Matrix.of X.1 =
        (Matrix.of X.1 * Matrix.of Y.1 + Matrix.of Y.1 * Matrix.of X.1) +
          (Matrix.of X.1 * Matrix.of Y'.1 + Matrix.of Y'.1 * Matrix.of X.1)
      rw [add_mul, mul_add]; abel))
    (fun c X Y => Subtype.ext (by
      change Matrix.of X.1 * (c • Matrix.of Y.1) + (c • Matrix.of Y.1) * Matrix.of X.1 =
        c • (Matrix.of X.1 * Matrix.of Y.1 + Matrix.of Y.1 * Matrix.of X.1)
      rw [smul_mul_assoc, mul_smul_comm, smul_add]))

private def jorC : HV E a →L[ℝ] HV E a →L[ℝ] HV E a :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := HV E a) (F' := HV E a)).toLinearMap ∘ₗ jorL)

private theorem jorC_val (X Y : HV E a) :
    Matrix.of (jorC X Y).1 = Matrix.of X.1 * Matrix.of Y.1 + Matrix.of Y.1 * Matrix.of X.1 := rfl

private def sq2 (X : HV E a) : HV E a := (1 / 2 : ℝ) • jorC X X

private theorem square_map_val (X : HV E a) : Matrix.of (sq2 X).1 = Matrix.of X.1 * Matrix.of X.1 := by
  change (1 / 2 : ℝ) • Matrix.of (jorC X X).1 = _
  rw [jorC_val, ← two_smul ℝ, smul_smul]; norm_num

private theorem square_map_one : sq2 (hOne E a) = hOne E a := by
  apply Subtype.ext
  change Matrix.of (sq2 (hOne E a)).1 = Matrix.of (hOne E a).1
  rw [square_map_val, hOne_val, mul_one]

private theorem square_map_contDiff : ContDiff ℝ ∞ (sq2 (E := E) (a := a)) :=
  ((jorC (E := E) (a := a)).contDiff.clm_apply contDiff_id).const_smul _

private def dbl : HV E a ≃L[ℝ] HV E a :=
  ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := HV E a) (Units.mk0 (2 : ℝ) two_ne_zero)

private theorem square_map_hasFDerivAt : HasFDerivAt (sq2 (E := E) (a := a)) (dbl (E := E) (a := a) : HV E a →L[ℝ] HV E a) (hOne E a) := by
  have h := (((jorC (E := E) (a := a)).hasFDerivAt (x := hOne E a)).clm_apply (hasFDerivAt_id (hOne E a))).const_smul (1 / 2 : ℝ)
  refine HasFDerivAt.congr_fderiv h ?_
  refine ContinuousLinearMap.ext fun H => Subtype.ext ?_
  change (1 / 2 : ℝ) • (Matrix.of (jorC (hOne E a) H).1 + Matrix.of (jorC H (hOne E a)).1) = (2 : ℝ) • Matrix.of H.1
  rw [jorC_val, jorC_val, hOne_val, mul_one, one_mul]
  module

private theorem exists_sqrt : ∃ σ : HV E a → HV E a, ContDiffAt ℝ ∞ σ (hOne E a) ∧ σ (hOne E a) = hOne E a ∧
    ∀ᶠ p in 𝓝 (hOne E a), sq2 (σ p) = p := by
  have hc : ContDiffAt ℝ ∞ (sq2 (E := E) (a := a)) (hOne E a) := square_map_contDiff.contDiffAt
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  refine ⟨hc.localInverse square_map_hasFDerivAt hn, ?_, ?_, ?_⟩
  · have := hc.to_localInverse square_map_hasFDerivAt hn
    rwa [square_map_one] at this
  · have := hc.localInverse_apply_image square_map_hasFDerivAt hn
    rwa [square_map_one] at this
  · have := (hc.hasStrictFDerivAt' square_map_hasFDerivAt hn).eventually_right_inverse
    rwa [square_map_one] at this

private theorem ev_unit : ∀ᶠ X in 𝓝 (hOne E a), IsUnit (Matrix.of X.1) := by
  have hc : Continuous fun X : HV E a => (Matrix.of X.1).det :=
    Continuous.matrix_det (A := fun X : HV E a => Matrix.of X.1) continuous_subtype_val
  have h1 : (Matrix.of (hOne E a).1).det ∈ {x : Cinf E | IsUnit x} := by
    rw [hOne_val, det_one]; exact isUnit_one
  filter_upwards [hc.continuousAt.preimage_mem_nhds (Units.isOpen.mem_nhds h1)] with X hX
  exact (Matrix.isUnit_iff_isUnit_det _).2 hX

private def lmul (g : Matrix (Fin a) (Fin a) (Cinf E)) : HV E a →L[ℝ] Lie E a :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => toL (g * Matrix.of X.1)
      map_add' := fun X Y => by
        change g * (Matrix.of X.1 + Matrix.of Y.1) = g * Matrix.of X.1 + g * Matrix.of Y.1
        rw [mul_add]
      map_smul' := fun c X => by
        change g * (c • Matrix.of X.1) = c • (g * Matrix.of X.1)
        rw [mul_smul_comm] }

open Classical in
theorem locSec : LocSec := by
  rintro E _ _ a p₀ ⟨g, rfl⟩
  obtain ⟨σ, hσ, hσ1, hσ2⟩ := exists_sqrt (E := E) (a := a)
  have h0 : sand g⁻¹ (sand g (hOne E a)) = hOne E a := by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
  have hq : Tendsto (sand g⁻¹) (𝓝 (sand g (hOne E a))) (𝓝 (hOne E a)) := by
    have := (sand g⁻¹).continuous.tendsto (sand g (hOne E a))
    rwa [h0] at this
  have hs : Tendsto σ (𝓝 (hOne E a)) (𝓝 (hOne E a)) := by
    have := hσ.continuousAt.tendsto
    rwa [hσ1] at this
  have hu := (hs.comp hq).eventually ev_unit
  let u : HV E a → GL (Fin a) (Cinf E) := fun X => if h : IsUnit (Matrix.of X.1) then h.unit else 1
  have hval : ∀ X : HV E a, IsUnit (Matrix.of X.1) → (u X).val = Matrix.of X.1 := fun X h => by
    simp only [u, dif_pos h, IsUnit.unit_spec]
  refine ⟨fun p => g * u (σ (sand g⁻¹ p)), ?_, ?_⟩
  · have h1 : ContDiffAt ℝ ∞ (fun p => σ (sand g⁻¹ p)) (sand g (hOne E a)) :=
      ContDiffAt.comp (g := σ) _ (h0.symm ▸ hσ) (sand g⁻¹).contDiff.contDiffAt
    refine ((lmul g.val).contDiff.contDiffAt.comp _ h1).congr_of_eventuallyEq ?_
    filter_upwards [hu] with p hp
    rw [Units.val_mul, hval (σ (sand g⁻¹ p)) hp]; rfl
  · filter_upwards [hu, hq.eventually hσ2] with p hp hp2
    have h2 : sand (u (σ (sand g⁻¹ p))) (hOne E a) = sand g⁻¹ p := by
      rw [← hp2]
      apply Subtype.ext
      change Matrix.of (sand _ _).1 = Matrix.of (sq2 _).1
      have hX : star (Matrix.of (σ (sand g⁻¹ p)).1) = Matrix.of (σ (sand g⁻¹ p)).1 := (σ (sand g⁻¹ p)).2
      rw [sand_val, square_map_val, hOne_val, mul_one, hp2, hval (σ (sand g⁻¹ p)) hp, hX]
    rw [map_mul, ContinuousLinearMap.mul_apply, h2, ← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl

end UpperTheory.V.Lit.Dr
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.EvFacts
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af
open scoped TensorProduct

namespace UpperTheory.V.Lit.Dr

private theorem ev_comp {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a d : ℕ}
    (m : Sm E a ⊗[ℂ] (Fin d → ℂ)) (j : Fin d) :
    (fun g => ev m g j) = (TensorProduct.piScalarRight ℂ ℂ (Sm E a) (Fin d) m j).1 := by
  induction m using TensorProduct.induction_on with
  | zero =>
    rw [(ev (E := E) (a := a) (d := d)).map_zero,
      (TensorProduct.piScalarRight ℂ ℂ (Sm E a) (Fin d)).map_zero]
    rfl
  | tmul φ v =>
    funext g
    simp [mul_comm]
  | add x y hx hy =>
    rw [map_add (f := _), map_add (f := _), Pi.add_apply, Submodule.coe_add, ← hx, ← hy]
    rfl

theorem evFacts : EvFacts := by
  intro E _ _ _ a d
  refine ⟨fun m m' h => ?_, fun m j => ?_, fun f hf => ?_⟩
  · apply (TensorProduct.piScalarRight ℂ ℂ (Sm E a) (Fin d)).injective
    funext j
    apply Subtype.ext
    rw [← ev_comp, ← ev_comp, h]
  · rw [ev_comp]
    exact Subtype.property _
  · refine ⟨(TensorProduct.piScalarRight ℂ ℂ (Sm E a) (Fin d)).symm fun j => ⟨_, hf j⟩, ?_⟩
    funext g j
    have := congrFun (ev_comp ((TensorProduct.piScalarRight ℂ ℂ (Sm E a) (Fin d)).symm fun j => ⟨_, hf j⟩) j) g
    rw [LinearEquiv.apply_symm_apply] at this
    exact this

end UpperTheory.V.Lit.Dr
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.MatSmooth
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh
open scoped ContDiff

namespace UpperTheory.V.Lit.Dr

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private theorem smooth_of_formula {f : GL (Fin a) (Cinf E) → ℂ} {F : Lie E a → ℂ} (h : ∀ y, f y = F (toL y.val))
    (hF : ContDiffOn ℝ ∞ F (invSet E a)) : ContDiffOn ℝ ∞ (extGL f) (invSet E a) :=
  hF.congr fun _ hx => (extGL_eventuallyEq h hx).self_of_nhds

private theorem smooth_reg (σ : GL (Fin a) (Cinf E) → GL (Fin a) (Cinf E))
    (h1 : ∀ τ i j, ContDiffOn ℝ ∞ (extGL fun y => coord τ ((σ y).val i j)) (invSet E a))
    (h2 : ∀ τ, ContDiffOn ℝ ∞ (extGL fun y => (coord τ (σ y).val.det)⁻¹) (invSet E a))
    {f : GL (Fin a) (Cinf E) → ℂ} (hf : f ∈ regFun E a) :
    ContDiffOn ℝ ∞ (extGL fun y => f (σ y)) (invSet E a) := by
  induction hf using Algebra.adjoin_induction with
  | mem f hf =>
    obtain ⟨τ, i, j, rfl⟩ | ⟨τ, rfl⟩ := hf
    exacts [h1 τ i j, h2 τ]
  | algebraMap c => exact smooth_of_formula (F := fun _ => c) (fun _ => rfl) contDiffOn_const
  | add f g _ _ hf hg => exact smooth_of_formula (fun y => by simp [extGL_val]) (hf.add hg)
  | mul f g _ _ hf hg => exact smooth_of_formula (fun y => by simp [extGL_val]) (hf.mul hg)

private theorem smooth_det (τ : E →+* ℂ) : ContDiff ℝ ∞ fun x : Lie E a => coord τ (Matrix.of x).det :=
  (coordL τ).contDiff.comp contDiff_det

private theorem smooth_det_inv (τ : E →+* ℂ) :
    ContDiffOn ℝ ∞ (fun x : Lie E a => (coord τ (Matrix.of x).det)⁻¹) (invSet E a) :=
  (smooth_det τ).contDiffOn.inv fun _ hx => (((Matrix.isUnit_iff_isUnit_det _).1 hx).map (coord τ)).ne_zero

private theorem smooth_adj (τ : E →+* ℂ) (i j : Fin a) :
    ContDiff ℝ ∞ fun x : Lie E a => coord τ ((Matrix.of x).adjugate i j) := by
  have h : ContDiff ℝ ∞ fun x : Lie E a => (Function.update x j (Pi.single i 1) : Lie E a) := by
    refine contDiff_pi.2 fun k => ?_
    by_cases hk : k = j
    · subst hk
      simpa using contDiff_const
    · simpa [Function.update_of_ne hk] using contDiff_apply ℝ _ k
  simp only [Matrix.adjugate_apply]
  exact (smooth_det τ).comp h

omit [NumberField E] in
private theorem coord_inv_entry (τ : E →+* ℂ) (y : GL (Fin a) (Cinf E)) (i j : Fin a) :
    coord τ ((y⁻¹).val i j) = (coord τ y.val.det)⁻¹ * coord τ (y.val.adjugate i j) := by
  have hu : IsUnit y.val.det := (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit
  have e : y.val.adjugate = y.val.det • (y⁻¹).val := by
    calc y.val.adjugate = (y.val.adjugate * y.val) * (y⁻¹).val := by
          rw [mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [Matrix.adjugate_mul, smul_mul_assoc, one_mul]
  rw [e, Matrix.smul_apply, smul_eq_mul, map_mul, inv_mul_cancel_left₀ (hu.map (coord τ)).ne_zero]

omit [NumberField E] in
private theorem coord_inv_det (τ : E →+* ℂ) (y : GL (Fin a) (Cinf E)) :
    (coord τ (y⁻¹).val.det)⁻¹ = coord τ y.val.det := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← map_mul, ← Matrix.det_mul, Units.inv_mul, Matrix.det_one, map_one]

theorem matSmooth : MatSmooth := by
  intro E _ _ a Ξ i j
  refine ⟨smooth_reg id (fun τ k l => ?_) (fun τ => ?_) (Ξ.reg i j),
    smooth_reg (fun y => y⁻¹) (fun τ k l => ?_) (fun τ => ?_) (Ξ.reg i j)⟩
  · exact smooth_of_formula (F := fun x => coordL τ (x k l)) (fun _ => rfl) (by fun_prop)
  · exact smooth_of_formula (fun _ => rfl) (smooth_det_inv τ)
  · exact smooth_of_formula (fun y => coord_inv_entry τ y k l) ((smooth_det_inv τ).mul (smooth_adj τ k l).contDiffOn)
  · exact smooth_of_formula (fun y => coord_inv_det τ y) (smooth_det τ).contDiffOn

end UpperTheory.V.Lit.Dr
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.LevelVal
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af
open scoped TensorProduct

namespace UpperTheory.V.Lit.Dr

section Components

variable {S : Type} [AddCommGroup S] [Module ℂ S] {d : ℕ}

private def cmp (j : Fin d) : S ⊗[ℂ] (Fin d → ℂ) →ₗ[ℂ] S :=
  (TensorProduct.rid ℂ S).toLinearMap ∘ₗ (LinearMap.proj j : (Fin d → ℂ) →ₗ[ℂ] ℂ).lTensor S

private theorem cmp_tmul (j : Fin d) (φ : S) (v : Fin d → ℂ) : cmp j (φ ⊗ₜ[ℂ] v) = v j • φ := by
  simp [cmp]

private theorem sum_cmp (m : S ⊗[ℂ] (Fin d → ℂ)) :
    ∑ j, cmp j m ⊗ₜ[ℂ] (Pi.single j 1 : Fin d → ℂ) = m := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul φ v =>
    simp only [cmp_tmul, TensorProduct.smul_tmul]
    rw [← TensorProduct.tmul_sum]
    congr 1
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  | add x y hx hy => simp only [map_add (f := _), TensorProduct.add_tmul, Finset.sum_add_distrib, hx, hy]

private theorem cmp_sum (L : Module.End ℂ S) (c : ℂ) (j : Fin d) (m : S ⊗[ℂ] (Fin d → ℂ)) :
    cmp j ((L.rTensor (Fin d → ℂ) + (Matrix.toLin' (c • (1 : Matrix (Fin d) (Fin d) ℂ))).lTensor S) m) =
      L (cmp j m) + c • cmp j m := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul φ v => simp [cmp_tmul, smul_smul]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), map_add (f := _), smul_add]; abel

end Components

private theorem cmp_apply {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a d : ℕ}
    (m : Sm E a ⊗[ℂ] (Fin d → ℂ)) (j : Fin d) (g : GA E a) : (cmp j m).1 g = ev m g j := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul φ v => simp [cmp_tmul, mul_comm]
  | add x y hx hy => simp [hx, hy]

theorem levelVal : LevelVal := by
  intro E _ _ _ a U Ξ m
  refine ⟨fun hm => ?_, fun hl hr h0 => ?_⟩
  · induction hm using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨φ, v, hφ, rfl⟩ := hx
      refine ⟨fun γ g => ?_, fun u hu g => ?_⟩
      · rw [ev_tmul, ev_tmul, hφ.1]
      · have h : φ.1 (g * finGL E a u) = φ.1 g := congrFun (congrArg Subtype.val (hφ.2.1 u hu)) g
        rw [ev_tmul, ev_tmul, h]
    | zero => exact ⟨fun γ g => by simp, fun u _ g => by simp⟩
    | add x y _ _ hx hy =>
      exact ⟨fun γ g => by simp only [map_add (f := _), Pi.add_apply, hx.1 γ g, hy.1 γ g],
        fun u hu g => by simp only [map_add (f := _), Pi.add_apply, hx.2 u hu g, hy.2 u hu g]⟩
    | smul c x _ hx =>
      exact ⟨fun γ g => by simp only [map_smul, Pi.smul_apply, hx.1 γ g],
        fun u hu g => by simp only [map_smul, Pi.smul_apply, hx.2 u hu g]⟩
  · rw [← sum_cmp m]
    refine Submodule.sum_mem _ fun j _ => Submodule.subset_span ⟨cmp j m, _, ⟨fun γ g => ?_, fun u hu => ?_, fun c hc => ?_⟩, rfl⟩
    · rw [cmp_apply, cmp_apply, hl]
    · refine Subtype.ext (funext fun g => ?_)
      change (cmp j m).1 (g * finGL E a u) = (cmp j m).1 g
      rw [cmp_apply, cmp_apply, hr u hu]
    · have h := cmp_sum (lie E a (oneL E a)) c j m
      rw [← hc] at h
      have h1 : cmp j (smLie Ξ (oneL E a) m) = 0 := by rw [h0, map_zero]
      rw [neg_smul]
      exact eq_neg_of_add_eq_zero_left (h.symm.trans h1)

end UpperTheory.V.Lit.Dr
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.EvK
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af
open scoped TensorProduct

namespace UpperTheory.V.Lit.Dr

theorem evK : EvK := by
  intro E _ _ _ a Ξ k m g
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul φ v =>
    have h : ev (smK Ξ k (φ ⊗ₜ[ℂ] v)) g =
        φ.1 (g * infGL E a (Unitary.toUnits k)) • (Ξ.mat (Unitary.toUnits k) *ᵥ v) := rfl
    rw [h, ev_tmul, Matrix.mulVec_smul]
  | add x y hx hy => simp only [map_add (f := _), Pi.add_apply, hx, hy, Matrix.mulVec_add]

end UpperTheory.V.Lit.Dr
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.CorrInv
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af
open scoped TensorProduct ContDiff ComplexOrder

namespace UpperTheory.V.Lit.Dr

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem rat_mul_split (γ : GL (Fin a) E) (g : GL (Fin a) (Cinf E)) (x : GL (Fin a) (Af E)) :
    infGL E a (GeneralLinearGroup.map (pInf E) (ratGL E a γ) * g) *
        finGL E a (GeneralLinearGroup.map (algebraMap E (Af E)) γ * x) =
      ratGL E a γ * (infGL E a g * finGL E a x) := by
  refine ga_ext ?_ ?_
  · simp only [map_mul, pInf_infGL, pInf_finGL, mul_one]
  · simp only [map_mul, pFin_infGL, pFin_finGL, one_mul]
    rfl

private theorem split_ga (g : GA E a) :
    infGL E a (GeneralLinearGroup.map (pInf E) g) * finGL E a (GeneralLinearGroup.map (pFin E) g) = g := by
  refine ga_ext ?_ ?_
  · simp only [map_mul, pInf_infGL, pInf_finGL, mul_one]
  · simp only [map_mul, pFin_infGL, pFin_finGL, one_mul]

private theorem act_corr (ho : IsOpen (cone E a)) (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a) (q : ℕ)
    (α : Herm E a [⋀^Fin q]→ₗ[ℝ] (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ))) (w : (geo ho U Ξ).Om q) (h : Corr U Ξ α w.1)
    (γ : (⊤ : Subgroup (GL (Fin a) E))) (g : GL (Fin a) (Cinf E)) (x : GL (Fin a) (Af E)) (X : Fin q → Herm E a) :
    ((geo ho U Ξ).act q γ w).1 (x : GL (Fin a) (Af E) ⧸ U) (sand g (hOne E a))
        (fun i => (2 : ℝ) • sand g (hv (X i))) =
      Ξ.mat g *ᵥ ev (α X) (ratGL E a (γ⁻¹).1 * (infGL E a g * finGL E a x)) := by
  have hs : ∀ p : HV E a, (geo ho U Ξ).ρ γ⁻¹ (sand g p) =
      sand (GeneralLinearGroup.map (pInf E) (ratGL E a (γ⁻¹).1) * g) p := fun p => by
    rw [geo_ρ, map_mul]; rfl
  have hσ : (geo ho U Ξ).σ γ⁻¹ (x : GL (Fin a) (Af E) ⧸ U) =
      ((GeneralLinearGroup.map (algebraMap E (Af E)) (γ⁻¹).1 * x : GL (Fin a) (Af E)) : GL (Fin a) (Af E) ⧸ U) := rfl
  rw [Geo.act_apply, hσ]
  simp only [map_smul, hs]
  rw [h, rat_mul_split, geo_ξ, Matrix.mulVec_mulVec, ← map_mul, ← mul_assoc, ← map_mul, ← map_mul]
  simp only [Subgroup.coe_inv, mul_inv_cancel, map_one, one_mul]

theorem corrInv : CorrInv := by
  intro E _ _ _ a ho U Ξ q α w h
  constructor
  · intro hL γ
    refine Subtype.ext (funext fun s => funext fun p => ?_)
    by_cases hp : p ∈ cone E a
    · obtain ⟨g, rfl⟩ := hp
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
      ext1 v
      have hv' : v = fun i => (2 : ℝ) • sand g (hv (hv.symm ((2 : ℝ)⁻¹ • sand g⁻¹ (v i)))) := by
        funext i
        rw [LinearEquiv.apply_symm_apply, map_smul, smul_smul, ← ContinuousLinearMap.mul_apply, ← map_mul,
          mul_inv_cancel, map_one]
        simp
      rw [hv', act_corr ho U Ξ q α w h, h, hL]
    · rw [(((geo ho U Ξ).act q γ w).2 s).2 p hp, (w.2 s).2 p hp]
  · intro hw X γ g
    have h1 := act_corr ho U Ξ q α w h (⟨γ, Subgroup.mem_top γ⟩ : (⊤ : Subgroup (GL (Fin a) E)))⁻¹
      (GeneralLinearGroup.map (pInf E) g) (GeneralLinearGroup.map (pFin E) g) X
    rw [hw, h, split_ga, inv_inv] at h1
    have h2 := congrArg (fun y => Ξ.mat (GeneralLinearGroup.map (pInf E) g)⁻¹ *ᵥ y) h1
    simp only [Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec] at h2
    exact h2.symm

end UpperTheory.V.Lit.Dr
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.ConeConvex
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.ConePos
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af
open scoped ComplexOrder MatrixOrder

namespace UpperTheory.V.Lit.Dr

private theorem posDef_iff_mul_star {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) :
    M.PosDef ↔ ∃ B : Matrix n n ℂ, IsUnit B ∧ M = B * star B := by
  open scoped Matrix.Norms.L2Operator in
  rw [← Matrix.isStrictlyPositive_iff_posDef, CStarAlgebra.isStrictlyPositive_iff_eq_mul_star_self]

private theorem pi_iff {n ι : Type} [Fintype n] [DecidableEq n] (M : Matrix n n (ι → ℂ)) :
    (∃ g : GL n (ι → ℂ), g.val * 1 * star g.val = M) ↔ ∀ w, (Matrix.of fun i j => M i j w).PosDef := by
  simp only [posDef_iff_mul_star, mul_one]
  constructor
  · rintro ⟨g, rfl⟩ w
    refine ⟨g.val.map (Pi.evalRingHom (fun _ => ℂ) w), ?_, ?_⟩
    · exact g.isUnit.map (Pi.evalRingHom (fun _ : ι => ℂ) w).mapMatrix
    · ext i j
      simp [Matrix.mul_apply, Finset.sum_apply]
  · intro h
    choose B hB hM using h
    have hu : IsUnit (Matrix.of fun i j w => B w i j : Matrix n n (ι → ℂ)) := by
      rw [Matrix.isUnit_iff_isUnit_det, Pi.isUnit_iff]
      intro w
      have := RingHom.map_det (Pi.evalRingHom (fun _ : ι => ℂ) w) (Matrix.of fun i j w => B w i j : Matrix n n (ι → ℂ))
      rw [Pi.evalRingHom_apply] at this
      rw [this, ← Matrix.isUnit_iff_isUnit_det]
      exact hB w
    refine ⟨hu.unit, ?_⟩
    ext i j w
    have := congrFun (congrFun (hM w) i) j
    simp only [Matrix.of_apply] at this
    rw [this]
    simp [Matrix.mul_apply, Finset.sum_apply]

theorem conePos : ConePos := by
  intro E _ _ a p
  refine Iff.trans ?_ (pi_iff (Matrix.of p.1))
  exact exists_congr fun g => Subtype.ext_iff

end UpperTheory.V.Lit.Dr
end
end

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af
open scoped TensorProduct ContDiff ComplexOrder

namespace UpperTheory.V.Lit.Dr

theorem coneConvex : ConeConvex := by
  intro E _ _ a
  have hs : IsCone (cone E a) := by
    intro t ht p hp
    rw [conePos] at hp ⊢
    intro w
    have h := (hp w).smul ht
    convert h using 1
    ext i j
    rfl
  have hadd : ∀ p ∈ cone E a, ∀ q ∈ cone E a, p + q ∈ cone E a := by
    intro p hp q hq
    rw [conePos] at hp hq ⊢
    intro w
    have h := (hp w).add (hq w)
    convert h using 1
    ext i j
    rfl
  refine ⟨?_, hs⟩
  rw [convex_iff_forall_pos]
  intro x hx y hy s t hs' ht _
  exact hadd _ (hs s hs' x hx) _ (hs t ht y hy)

end UpperTheory.V.Lit.Dr
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.BoundInf
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af

namespace UpperTheory.V.Lit.Dr

private theorem entry_sq_le {ι : Type} [Fintype ι] {a : ℕ} (A : Matrix (Fin a) (Fin a) (ι → ℂ)) (i j : Fin a) :
    ‖A i j‖ ≤ Real.sqrt ‖(A * star A) i i‖ := by
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun w => Real.le_sqrt_of_sq_le ?_
  refine le_trans ?_ (norm_le_pi_norm ((A * star A) i i) w)
  have h : (A * star A) i i w = ((∑ k, ‖A i k w‖ ^ 2 : ℝ) : ℂ) := by
    simp [Matrix.mul_apply, Finset.sum_apply, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [h, Complex.norm_real, Real.norm_eq_abs]
  exact le_trans (Finset.single_le_sum (f := fun k => ‖A i k w‖ ^ 2) (fun _ _ => sq_nonneg _)
    (Finset.mem_univ j)) (le_abs_self _)

theorem boundInf : BoundInf := by
  intro E _ _ a K hK hc
  obtain ⟨C₁, hC₁⟩ := hc.isBounded.exists_norm_le
  have hcont : ContinuousOn (fun p : HV E a => toL (Matrix.of p.1)⁻¹) K := by
    intro p hp
    obtain ⟨h, rfl⟩ := hK hp
    have hu : IsUnit (Matrix.of (sand h (hOne E a)).1).det := by
      rw [sand_val, hOne_val, mul_one, ← Matrix.isUnit_iff_isUnit_det]
      exact h.isUnit.mul h.isUnit.star
    have h1 : ContinuousAt (Inv.inv : Matrix (Fin a) (Fin a) (Cinf E) → _) (Matrix.of (sand h (hOne E a)).1) :=
      continuousAt_matrix_inv _ (by
        obtain ⟨u, hu⟩ := hu
        rw [← hu]
        exact NormedRing.inverse_continuousAt u)
    have h2 : Continuous (fun p : HV E a => (Matrix.of p.1 : Matrix (Fin a) (Fin a) (Cinf E))) :=
      continuous_subtype_val
    exact (ContinuousAt.comp (f := fun p : HV E a => (Matrix.of p.1 : Matrix (Fin a) (Fin a) (Cinf E))) h1
      h2.continuousAt).continuousWithinAt
  obtain ⟨C₂, hC₂⟩ := hc.exists_bound_of_continuousOn hcont
  refine ⟨a * (Real.sqrt C₁ * Real.sqrt C₂), fun g p hp hgp => ?_⟩
  obtain ⟨h, rfl⟩ := hK hp
  have hA : ∀ i j, ‖(g * h).val i j‖ ≤ Real.sqrt C₁ := fun i j => by
    refine (entry_sq_le _ i j).trans (Real.sqrt_le_sqrt (le_trans ?_ (hC₁ _ hgp)))
    have e : (g * h).val * star (g * h).val = Matrix.of (sand g (sand h (hOne E a))).1 := by
      rw [sand_val, sand_val, hOne_val]; simp only [Units.val_mul, star_mul, mul_assoc, one_mul]
    rw [e]
    exact (norm_le_pi_norm _ i).trans (norm_le_pi_norm (sand g (sand h (hOne E a))).1 i)
  have hB : ∀ i j, ‖(h⁻¹).val i j‖ ≤ Real.sqrt C₂ := fun i j => by
    have e0 : ‖(h⁻¹).val i j‖ = ‖(star (h⁻¹).val) j i‖ := by rw [Matrix.star_apply, norm_star]
    rw [e0]
    refine (entry_sq_le _ j i).trans (Real.sqrt_le_sqrt (le_trans ?_ (hC₂ _ hp)))
    have e : star (h⁻¹).val * star (star (h⁻¹).val) = (Matrix.of (sand h (hOne E a)).1)⁻¹ := by
      rw [sand_val, hOne_val, mul_one, star_star]
      refine (Matrix.inv_eq_left_inv ?_).symm
      rw [mul_assoc, ← mul_assoc (h⁻¹).val, Units.inv_mul, one_mul, ← star_mul, Units.mul_inv, star_one]
    rw [e]
    exact (norm_le_pi_norm _ j).trans (norm_le_pi_norm (toL (Matrix.of (sand h (hOne E a)).1)⁻¹) j)
  have h0 : (0 : ℝ) ≤ a * (Real.sqrt C₁ * Real.sqrt C₂) := by positivity
  refine (pi_norm_le_iff_of_nonneg h0).2 fun i => (pi_norm_le_iff_of_nonneg h0).2 fun j => ?_
  have e : g.val = (g * h).val * (h⁻¹).val := by rw [← Units.val_mul, mul_inv_cancel_right]
  change ‖g.val i j‖ ≤ _
  rw [e, Matrix.mul_apply]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun k _ => (norm_mul_le _ _).trans
    (mul_le_mul (hA i k) (hB k j) (norm_nonneg _) (Real.sqrt_nonneg _))).trans ?_
  simp

end UpperTheory.V.Lit.Dr
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.DeRhamInjOf
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af
open scoped TensorProduct

namespace UpperTheory.V.Lit.Dr

theorem geo_main (h1 : AbsMain) (h2 : DEquiv) (h3 : InclFacts) (h4 : DExact) (h5 : Average) (h6 : Window) (h7 : Cutoff)
    {Γ V S : Type} [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {d : ℕ} (G : Geo Γ V S d)
    (hc : Convex ℝ G.Y) (hn : G.Y.Nonempty) (hp : G.Proper) (q n : ℕ) (w : Fin n → G.Om q)
    (hi : ∀ i γ, G.act q γ (w i) = w i) (hd : ∀ i, G.dOm q (w i) = 0)
    (hx : ∀ c : Fin n → ℂ, InvExact (Ω := fun q => G.Om q) G.act G.dOm (∑ i, c i • w i) → c = 0) :
    (n : Cardinal) ≤ Module.rank ℂ (groupCohomology (Rep.of G.lev) q) := by
  obtain ⟨W, hW⟩ := h6 Γ V S d G hp
  obtain ⟨u, hu⟩ := h7 Γ V S d G W hW
  obtain ⟨a1, a2, a3⟩ := h3 Γ V S d G hc hn
  exact h1 q Γ _ (fun q => G.Om q) G.lev G.act G.incl G.dOm a1 (h2 Γ V S d G) a2 a3 (h4 Γ V S d G hc) (h5 Γ V S d G u hu)
    n w hi hd hx

section

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
  (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a) {q : ℕ}

private theorem alt_sum {V M : Type} [AddCommGroup V] [Module ℝ V] [AddCommGroup M] [Module ℝ M] {n : ℕ}
    (f : Fin n → V [⋀^Fin q]→ₗ[ℝ] M) (X : Fin q → V) : (∑ i, f i) X = ∑ i, f i X :=
  map_sum (AddMonoidHom.mk' (fun g : V [⋀^Fin q]→ₗ[ℝ] M => g X) fun _ _ => rfl) f _

theorem corr_zero : Corr (q := q) U Ξ 0 0 := fun g x X => by simp

theorem corr_sum {n : ℕ} (c : Fin n → ℂ) {α : Fin n → Herm E a [⋀^Fin q]→ₗ[ℝ] (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ))}
    {w : Fin n → (GL (Fin a) (Af E) ⧸ U) → HV E a → HV E a [⋀^Fin q]→L[ℝ] (Fin Ξ.d → ℂ)} (h : ∀ i, Corr U Ξ (α i) (w i)) :
    Corr U Ξ (∑ i, c i • α i) (∑ i, c i • w i) := fun g x X => by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [alt_sum, map_sum, Finset.sum_apply, Finset.sum_apply, Finset.sum_apply, ContinuousAlternatingMap.sum_apply,
    Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [AlternatingMap.smul_apply, map_smul, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, Matrix.mulVec_smul, ← h i g x X]
  rfl

end

theorem deRhamInj_of (h1 : AbsMain) (h2 : DEquiv) (h3 : InclFacts) (h4 : DExact) (h5 : Average) (h6 : Window) (h7 : Cutoff)
    (h8 : Retract) (k1 : LocSec) (k2 : ConeConvex) (k3 : GeoProper) (k4 : Gauge) (k5 : LevelVal) (k6 : CentralOf)
    (k7 : CorrFwd) (k8 : CorrSmooth) (k9 : CorrBwd) (k10 : CorrCochain) (k11 : CorrUniq) (k12 : CorrInv) (k13 : CorrBasic)
    (k14 : CorrD) : DeRhamInj := by
  intro E _ _ _ a ha U _ hU Ξ q n α hα hind
  have ho : IsOpen (cone E a) := isOpen_iff_mem_nhds.2 fun p hp => by
    obtain ⟨τ, -, hτ⟩ := k1 E a p hp
    exact hτ.mono fun x hx => ⟨τ x, hx⟩
  have hv : ∀ i X, LeftInv (α i X) ∧ RightInv U (α i X) := fun i X => (k5 E a U Ξ _).1 ((hα i).1.val X)
  have hw : ∀ i, ∃ w : (geo ho U Ξ).Om q, Corr U Ξ (α i) w.1 := fun i => by
    obtain ⟨w, hw, h0⟩ := k7 E a U Ξ q (α i) (hα i).1.equiv fun X => (hv i X).2
    exact ⟨⟨w, fun s => ⟨k8 E a U Ξ q _ w hw s, h0 s⟩⟩, hw⟩
  choose w hw using hw
  rw [← geo_lev ho U Ξ]
  refine geo_main h1 h2 h3 h4 h5 h6 h7 (geo ho U Ξ) (k2 E a).1 ⟨_, hOne_mem_cone⟩ (k3 E a ho U Ξ hU) q n w
    (fun i => (k12 E a ho U Ξ q _ _ (hw i)).1 fun X => (hv i X).1) (fun i => ?_) fun c hc => hind c ?_
  · have h := k14 E a ho U Ξ q _ _ (hw i)
    rw [(hα i).2] at h
    exact (k11 E a ho U Ξ (q + 1)).2 0 _ 0 h (corr_zero U Ξ)
  · have hs : Corr U Ξ (∑ i, c i • α i) (∑ i, c i • w i).1 := by
      rw [Submodule.coe_sum]
      exact corr_sum U Ξ c hw
    have hb : ∀ (X : Fin q → Herm E a) (i : Fin q), (X i).1 = 1 → (∑ i, c i • α i) X = 0 := fun X i hX => by
      rw [alt_sum]
      exact Finset.sum_eq_zero fun j _ => by rw [AlternatingMap.smul_apply, (hα j).1.basic X i hX, smul_zero]
    generalize ∑ i, c i • α i = β at hs hb
    generalize ∑ i, c i • w i = z at hs hc
    cases q with
    | zero =>
      obtain rfl : z = 0 := hc
      exact (k11 E a ho U Ξ 0).1 _ 0 _ hs (corr_zero U Ξ)
    | succ q =>
      obtain ⟨y, hy, rfl⟩ := hc
      obtain ⟨l, hl⟩ := k4 E a ha ho U Ξ hU
      obtain ⟨y', i1, i2, i3⟩ := h8 _ _ _ _ (geo ho U Ξ) (k2 E a).2 l hl q y hy ((k13 E a U Ξ _ _ _ hs).1 hb)
      obtain ⟨η, hη⟩ := k9 E a ho U Ξ q y'
      have e : dCo (smLie Ξ) η = β := (k11 E a ho U Ξ (q + 1)).1 _ _ _ (i3 ▸ k14 E a ho U Ξ q _ _ hη) hs
      have b := (k13 E a U Ξ _ _ _ hη).2 i2
      obtain ⟨c1, c2⟩ := k10 E a U Ξ q _ _ hη
      exact ⟨η, ⟨c1, b, fun X => (k5 E a U Ξ _).2 ((k12 E a ho U Ξ q _ _ hη).2 i1 X) (c2 X)
        (k6 E a _ (smLie Ξ) q η b (e ▸ hb) X)⟩, e⟩

end UpperTheory.V.Lit.Dr
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.CentralOf
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af

namespace UpperTheory.V.Lit.Dr

theorem centralOf : CentralOf := by
  intro E _ _ a M _ _ _ _ L q η h1 h2 X
  let o : Herm E a := ⟨1, IsSelfAdjoint.one _⟩
  have h := h2 (Fin.cons o X) 0 rfl
  rw [dCo_apply, Fin.sum_univ_succ, Finset.sum_eq_zero, add_zero] at h
  · have e : Fin.removeNth (α := fun _ => Herm E a) 0 (Fin.cons o X) = X := by
      funext j; simp [Fin.removeNth]
    rw [e, Fin.val_zero, pow_zero, one_smul] at h
    exact h
  · intro i _
    have hz : η (Fin.removeNth (α := fun _ => Herm E a) i.succ (Fin.cons o X)) = 0 := by
      cases q with
      | zero => exact i.elim0
      | succ q =>
        refine h1 _ 0 ?_
        simp only [Fin.removeNth, Fin.succ_succAbove_zero, Fin.cons_zero]
        rfl
    rw [hz, map_zero, smul_zero]

end UpperTheory.V.Lit.Dr
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.FinField
open NumberField IsDedekindDomain

theorem UpperTheory.V.Lit.Dr.finField : UpperTheory.V.Lit.Dr.FinField := by
  intro E _ _ C T hT
  obtain ⟨d, hd0, hd⟩ := GroundTheory.Global.exists_mul_mem_integralFiniteAdeles_of_isCompact (K := E) hT
  have hdE : algebraMap (𝓞 E) E d ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr hd0
  have hfin := NumberField.Embeddings.finite_of_norm_le E ℂ
    ((∑ w : InfinitePlace E, w (algebraMap (𝓞 E) E d)) * C)
  refine Set.Finite.of_finite_image (f := fun x => algebraMap (𝓞 E) E d * x) (hfin.subset ?_)
    (mul_right_injective₀ hdE).injOn
  rintro _ ⟨x, ⟨hx, hxT⟩, rfl⟩
  refine ⟨?_, fun φ => ?_⟩
  · have h := hd _ hxT
    rw [← map_mul] at h
    obtain ⟨z, hz⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) E
      (algebraMap (𝓞 E) E d * x) fun v => by
        rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v]
        exact GroundTheory.Global.mem_integralFiniteAdeles.1 h v
    beta_reduce
    rw [← hz]
    exact RingOfIntegers.isIntegral_coe _
  · beta_reduce
    rw [← InfinitePlace.apply, map_mul]
    exact mul_le_mul
      (Finset.single_le_sum (f := fun w : InfinitePlace E => w (algebraMap (𝓞 E) E d))
        (fun w _ => apply_nonneg w _) (Finset.mem_univ _))
      (hx _) (apply_nonneg _ _) (Finset.sum_nonneg fun w _ => apply_nonneg w _)
end
