module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.EqAmOfBarEq

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousQuaternaryQuadraticForm
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2

section Base
variable {F : Type} [Field F] [NumberField F]

theorem continuous_quaternaryQuadraticForm (δ : F) : Continuous (q4 δ) := by unfold q4; fun_prop

end Base

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E)

theorem nu_mul (h h' : GL (Fin 2) (A E)) : nu F (h * h') = nu F h * nu F h' := by simp [nu]
@[simp] theorem nu_gl (g : G1 E) : nu F (gl g) = 1 := by rw [nu, det_gl, map_one]
@[simp] theorem nu_aE (a : (A E)ˣ) : nu F (aE a) = ideleNorm F E a := by rw [nu, det_aE]
@[simp] theorem nu_dM (a : (A E)ˣ) : nu F (dM a) = ideleNorm F E a := by rw [nu, det_dM]
theorem nu_scalar (z : (A E)ˣ) : nu F (Matrix.GeneralLinearGroup.scalar (Fin 2) z) = ideleNorm F E z ^ 2 := by
  rw [nu, det_scalar, map_pow]
theorem continuous_nu : Continuous (nu F : GL (Fin 2) (A E) → (A F)ˣ) := continuous_ideleNorm.comp continuous_adelicGL2_det

namespace Dat

def star2 (X : Matrix (Fin 2) (Fin 2) (A E)) : Matrix (Fin 2) (Fin 2) (A E) := (X.map D.bar)ᵀ
theorem conjTransposeGal_apply (X : Matrix (Fin 2) (Fin 2) (A E)) (i j : Fin 2) : D.star2 X i j = D.bar (X j i) := rfl
theorem conjTransposeGal_mul (X Y : Matrix (Fin 2) (Fin 2) (A E)) : D.star2 (X * Y) = D.star2 Y * D.star2 X := by
  rw [star2, Matrix.map_mul, Matrix.transpose_mul]; rfl
@[simp] theorem conjTransposeGal_involutive (X : Matrix (Fin 2) (Fin 2) (A E)) : D.star2 (D.star2 X) = X := by ext i j; simp [conjTransposeGal_apply]
@[simp] theorem conjTransposeGal_one : D.star2 1 = 1 := by rw [star2, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
theorem det_star2 (X : Matrix (Fin 2) (Fin 2) (A E)) : (D.star2 X).det = D.bar X.det := by
  rw [star2, Matrix.det_transpose, RingHom.map_det]; rfl
theorem herm_eq (v : V4 F) : D.herm v = !![am E (v 1), D.mkE (v 2) (v 3); D.bar (D.mkE (v 2) (v 3)), am E (v 0)] := by
  simp [herm, bar_mkE]
@[simp] theorem conjTranspose_herm (v : V4 F) : D.star2 (D.herm v) = D.herm v := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [conjTransposeGal_apply, herm_eq]
@[simp] theorem unherm_herm (v : V4 F) : D.unherm (D.herm v) = v := by
  have hc (u : A F) : D.co (am E u) = ![u, 0] := by rw [← D.mkE_base, D.co_mkE]
  ext i; fin_cases i <;> simp [unherm, herm_eq, hc]
theorem herm_unherm {X : Matrix (Fin 2) (Fin 2) (A E)} (hX : D.star2 X = X) : D.herm (D.unherm X) = X := by
  have h : ∀ i j, D.bar (X j i) = X i j := fun i j => congrFun (congrFun hX i) j
  ext i j; fin_cases i <;> fin_cases j <;> simp [unherm, herm_eq]
  exacts [(D.eq_am_of_bar_eq (h 0 0)).symm, h 1 0, (D.eq_am_of_bar_eq (h 1 1)).symm]
theorem herm_injective : Function.Injective D.herm := Function.LeftInverse.injective D.unherm_herm
theorem herm_add (v v' : V4 F) : D.herm (v + v') = D.herm v + D.herm v' := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [herm_eq, mkE_add]
theorem herm_smul (a : A F) (v : V4 F) : D.herm (a • v) = am E a • D.herm v := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [herm_eq, ← am_mul_mkE]
theorem det_herm (v : V4 F) : (D.herm v).det = -am E (q4 D.δ v) := by
  rw [herm_eq, Matrix.det_fin_two_of, mkE_mul_bar, q4]; simp only [map_sub, map_mul]; ring
theorem act_def (h : GL (Fin 2) (A E)) (v : V4 F) : D.act h v = D.unherm (h.val * D.herm v * D.star2 h.val) := rfl
theorem herm_act (h : GL (Fin 2) (A E)) (v : V4 F) : D.herm (D.act h v) = h.val * D.herm v * D.star2 h.val :=
  (congrArg D.herm (D.act_def h v)).trans <| D.herm_unherm (by rw [conjTransposeGal_mul, conjTransposeGal_mul, conjTransposeGal_involutive, conjTranspose_herm, Matrix.mul_assoc])
@[simp] theorem act_one (v : V4 F) : D.act 1 v = v := D.herm_injective (by rw [herm_act]; simp)
theorem act_mul (h h' : GL (Fin 2) (A E)) (v : V4 F) : D.act (h * h') v = D.act h (D.act h' v) :=
  D.herm_injective (by simp only [herm_act, Units.val_mul, conjTransposeGal_mul, Matrix.mul_assoc])
@[simp] theorem act_inv_act (h : GL (Fin 2) (A E)) (v : V4 F) : D.act h⁻¹ (D.act h v) = v := by rw [← act_mul]; simp
@[simp] theorem act_act_inv (h : GL (Fin 2) (A E)) (v : V4 F) : D.act h (D.act h⁻¹ v) = v := by rw [← act_mul]; simp
theorem act_add (h : GL (Fin 2) (A E)) (v v' : V4 F) : D.act h (v + v') = D.act h v + D.act h v' :=
  D.herm_injective (by simp only [herm_act, herm_add, Matrix.mul_add, Matrix.add_mul])
theorem act_smul (h : GL (Fin 2) (A E)) (a : A F) (v : V4 F) : D.act h (a • v) = a • D.act h v :=
  D.herm_injective (by simp only [herm_act, herm_smul, Matrix.mul_smul, Matrix.smul_mul])
theorem continuous_herm : Continuous D.herm := continuous_matrix fun i j => by
  have e : ∀ k l, Continuous fun v : V4 F => D.mkE (v k) (v l) := fun k l =>
    D.continuous_mkE' (continuous_apply k) (continuous_apply l)
  simp only [herm_eq]
  fin_cases i <;> fin_cases j
  exacts [continuous_am.comp (continuous_apply 1), e 2 3, D.continuous_bar.comp (e 2 3), continuous_am.comp (continuous_apply 0)]
theorem continuous_unherm : Continuous D.unherm := continuous_pi fun i => by
  have e : ∀ k l m, Continuous fun X : Matrix (Fin 2) (Fin 2) (A E) => D.co (X k l) m := fun k l m =>
    (continuous_apply m).comp (D.continuous_co.comp ((continuous_apply l).comp (continuous_apply k)))
  fin_cases i
  exacts [e 1 1 0, e 0 0 0, e 0 1 0, e 0 1 1]
theorem continuous_act : Continuous fun p : GL (Fin 2) (A E) × V4 F => D.act p.1 p.2 := by
  have h : Continuous fun p : GL (Fin 2) (A E) × V4 F => p.1.val := Units.continuous_val.comp continuous_fst
  exact D.continuous_unherm.comp ((h.matrix_mul (D.continuous_herm.comp continuous_snd)).matrix_mul
    (h.matrix_map D.continuous_bar).matrix_transpose)
theorem continuous_act' {X : Type*} [TopologicalSpace X] {h : X → GL (Fin 2) (A E)} {v : X → V4 F} (hh : Continuous h)
    (hv : Continuous v) : Continuous fun x => D.act (h x) (v x) := by
  have e : (fun x => D.act (h x) (v x)) = (fun p : GL (Fin 2) (A E) × V4 F => D.act p.1 p.2) ∘ fun x => (h x, v x) := rfl
  rw [e]; exact D.continuous_act.comp (hh.prodMk hv)

def actL : GL (Fin 2) (A E) →* (V4 F ≃ₗ[A F] V4 F) where
  toFun h :=
    { toFun := D.act h, invFun := D.act h⁻¹, left_inv := D.act_inv_act h, right_inv := D.act_act_inv h
      map_add' := D.act_add h, map_smul' := D.act_smul h }
  map_one' := LinearEquiv.ext D.act_one
  map_mul' h h' := LinearEquiv.ext (D.act_mul h h')

def actM (h : GL (Fin 2) (A E)) : Matrix (Fin 4) (Fin 4) (A F) := Matrix.of fun i j => D.act h (Pi.single j 1) i
theorem actM_eq (h : GL (Fin 2) (A E)) : D.actM h = LinearMap.toMatrix' (D.actL h).toLinearMap := by
  ext i j; rw [LinearMap.toMatrix'_apply]; rfl
theorem actM_mulVec (h : GL (Fin 2) (A E)) (v : V4 F) : D.actM h *ᵥ v = D.act h v := by
  rw [actM_eq, LinearMap.toMatrix'_mulVec]; rfl
theorem actM_one : D.actM 1 = 1 := by ext i j; simp [actM, Matrix.one_apply, Pi.single_apply]
theorem actM_mul (h h' : GL (Fin 2) (A E)) : D.actM (h * h') = D.actM h * D.actM h' := by
  rw [actM_eq, actM_eq, actM_eq, ← LinearMap.toMatrix'_mul, map_mul]; rfl

theorem quadForm_act (h : GL (Fin 2) (A E)) (v : V4 F) : q4 D.δ (D.act h v) = (nu F h : (A F)ˣ) * q4 D.δ v := by
  have e := congrArg Matrix.det (D.herm_act h v)
  rw [Matrix.det_mul, Matrix.det_mul, det_herm, det_herm, det_star2] at e
  apply am_injective (E := E)
  rw [map_mul, nu, D.am_ideleNorm, Matrix.GeneralLinearGroup.val_det_apply]
  linear_combination -e

theorem act_nU (u t : A F) (v : V4 F) : D.act (gl (nU (D.mkE u t))) v =
    ![v 0, v 1 + 2 * (u * v 2 - rt D.δ * (t * v 3)) + (u ^ 2 - rt D.δ * t ^ 2) * v 0, v 2 + u * v 0, v 3 + t * v 0] := by
  apply D.herm_injective
  rw [herm_act]
  have hθ := D.rt_θ_sq
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [herm, conjTransposeGal_apply, Matrix.mul_apply, Fin.sum_univ_two, gl, Matrix.SpecialLinearGroup.toGL, nU, bar_mkE, mkE_def, bar_rt, D.conj, ← hθ, map_ofNat] <;> ring
theorem act_scalar (z : (A E)ˣ) (v : V4 F) :
    D.act (Matrix.GeneralLinearGroup.scalar (Fin 2) z) v = ((ideleNorm F E z : (A F)ˣ) : A F) • v := by
  apply D.herm_injective
  rw [herm_act, herm_smul, D.am_ideleNorm]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [conjTransposeGal_apply, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

end Dat

end UpperTheory.ConvolutionTheory.R2

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.HomCommTrivial
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.CellGeneric
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.CellLocal
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open scoped Classical
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.cellLocal :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (ι : Type) (s : Finset ι) (c d : ι → R),
      (∀ j : ℕ, 0 < j → j ≤ s.card → IsUnit (j : R)) → (∀ i ∈ s, IsUnit (c i) ∨ IsUnit (d i)) →
        ∃ x : ℕ, ∀ i ∈ s, IsUnit (c i + d i * x) := by
  intro R _ _ ι s c d hj hcd
  by_contra hcon
  have hbad : ∀ x : ℕ, ∃ i, i ∈ s ∧ ¬ IsUnit (c i + d i * x) := by
    intro x
    by_contra h
    exact hcon ⟨x, fun i hi => by
      by_contra h'
      exact h ⟨i, hi, h'⟩⟩
  choose f hfs hf using hbad
  have key : ∀ x y : ℕ, x < y → y ≤ s.card → f x = f y → False := by
    intro x y hxy hy he
    have h1 : c (f x) + d (f x) * x ∈ IsLocalRing.maximalIdeal R := hf x
    have h2 : c (f x) + d (f x) * y ∈ IsLocalRing.maximalIdeal R := by
      rw [he]; exact hf y
    have hu : IsUnit ((y - x : ℕ) : R) := hj _ (by omega) (by omega)
    have h3 : d (f x) * ((y - x : ℕ) : R) ∈ IsLocalRing.maximalIdeal R := by
      have := Ideal.sub_mem _ h2 h1
      rw [Nat.cast_sub hxy.le]
      convert this using 1
      ring
    have h4 : d (f x) ∈ IsLocalRing.maximalIdeal R := by
      intro hd
      exact h3 (hd.mul hu)
    have h5 : c (f x) ∈ IsLocalRing.maximalIdeal R := by
      have := Ideal.sub_mem _ h1 (Ideal.mul_mem_right (x : R) _ h4)
      simpa using this
    rcases hcd _ (hfs x) with h | h
    · exact h5 h
    · exact h4 h
  obtain ⟨x, hx, y, hy, hne, he⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to (s := Finset.range (s.card + 1)) (t := s)
      (by simp) (f := f) (fun x _ => hfs x)
  rw [Finset.mem_range] at hx hy
  rcases lt_or_gt_of_ne hne with h | h
  · exact key x y h (by omega) he
  · exact key y x h (by omega) he.symm
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open scoped Classical
open UpperTheory.ConvolutionTheory.R2

private theorem unit_or_unit {R : Type} [CommRing R] [IsLocalRing R] {a b c d : R}
    (h : a * d - b * c = 1) : IsUnit c ∨ IsUnit d := by
  have hu : IsUnit (a * d + (-(b * c))) := by
    rw [← sub_eq_add_neg, h]; exact isUnit_one
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hu with h1 | h1
  · exact Or.inr (isUnit_of_mul_isUnit_right h1)
  · rw [IsUnit.neg_iff] at h1
    exact Or.inl (isUnit_of_mul_isUnit_right h1)

private theorem nat_isUnit {F : Type} [Field F] [NumberField F] (j : ℕ) (hj : 0 < j) :
    IsUnit ((j : ℕ) : A F) := by
  have h : ((j : ℕ) : A F) = algebraMap F (A F) (j : F) := (map_natCast _ j).symm
  rw [h]
  exact (IsUnit.mk0 (j : F) (Nat.cast_ne_zero.2 hj.ne')).map _

private theorem map_unit_or_unit {F : Type} [Field F] [NumberField F] {R : Type} [CommRing R]
    [IsLocalRing R] (f : A F →+* R) (g : G1 F) : IsUnit (f (g 1 0)) ∨ IsUnit (f (g 1 1)) := by
  refine unit_or_unit (a := f (g 0 0)) (b := f (g 0 1)) ?_
  rw [← map_mul, ← map_mul, ← map_sub, specialLinear_det_entries, map_one]

private theorem inf_step {F : Type} [Field F] [NumberField F] (s : Finset (G1 F)) (w : InfinitePlace F) :
    ∃ n : ℕ, ∀ g ∈ s, (g 1 0).1 w + (g 1 1).1 w * (n : w.Completion) ≠ 0 := by
  let f : A F →+* w.Completion :=
    (Pi.evalRingHom (fun w : InfinitePlace F => w.Completion) w).comp (p1 F)
  obtain ⟨n, hn⟩ := cellLocal w.Completion (G1 F) s (fun g => f (g 1 0)) (fun g => f (g 1 1))
    (fun j h0 _ => by simpa using (nat_isUnit (F := F) j h0).map f)
    (fun g _ => map_unit_or_unit f g)
  exact ⟨n, fun g hg => (hn g hg).ne_zero⟩

private theorem isUnit_int_iff {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (x : v.adicCompletionIntegers F) : IsUnit x ↔ Valued.v (x : v.adicCompletion F) = 1 := by
  exact Valuation.Integers.isUnit_iff_valuation_eq_one (Valuation.integer.integers _)

private theorem fin_step {F : Type} [Field F] [NumberField F] (s : Finset (G1 F))
    (v : HeightOneSpectrum (𝓞 F)) :
    ∃ n : ℕ, (∀ g ∈ s, pv v (g 1 0) + pv v (g 1 1) * (n : v.adicCompletion F) ≠ 0) ∧
      ((∀ g ∈ s, IntAt v g) → (∀ j : ℕ, 0 < j → j ≤ s.card → Valued.v (j : v.adicCompletion F) = 1) →
        ∀ g ∈ s, Valued.v (pv v (g 1 0) + pv v (g 1 1) * (n : v.adicCompletion F)) = 1) := by
  by_cases hgood : (∀ g ∈ s, IntAt v g) ∧
      ∀ j : ℕ, 0 < j → j ≤ s.card → Valued.v (j : v.adicCompletion F) = 1
  · obtain ⟨hint, hval⟩ := hgood
    let c : {g // g ∈ s} → v.adicCompletionIntegers F := fun g => ⟨pv v (g.1 1 0), hint g.1 g.2 1 0⟩
    let d : {g // g ∈ s} → v.adicCompletionIntegers F := fun g => ⟨pv v (g.1 1 1), hint g.1 g.2 1 1⟩
    let a : {g // g ∈ s} → v.adicCompletionIntegers F := fun g => ⟨pv v (g.1 0 0), hint g.1 g.2 0 0⟩
    let b : {g // g ∈ s} → v.adicCompletionIntegers F := fun g => ⟨pv v (g.1 0 1), hint g.1 g.2 0 1⟩
    obtain ⟨n, hn⟩ := cellLocal (v.adicCompletionIntegers F) {g // g ∈ s} s.attach c d
      (fun j h0 hj => by
        rw [isUnit_int_iff]
        simpa using hval j h0 (by simpa using hj))
      (fun g _ => by
        refine unit_or_unit (a := a g) (b := b g) (Subtype.ext ?_)
        have h := congrArg (pv v) (specialLinear_det_entries g.1)
        rw [map_sub, map_mul, map_mul, map_one] at h
        simpa [a, b, c, d] using h)
    have key : ∀ g ∈ s, Valued.v (pv v (g 1 0) + pv v (g 1 1) * (n : v.adicCompletion F)) = 1 := by
      intro g hg
      have h := (isUnit_int_iff v _).1 (hn ⟨g, hg⟩ (Finset.mem_attach _ _))
      simpa [c, d] using h
    refine ⟨n, fun g hg h0 => ?_, fun _ _ => key⟩
    have h := key g hg
    rw [h0, map_zero] at h
    exact zero_ne_one h
  · obtain ⟨n, hn⟩ := cellLocal (v.adicCompletion F) (G1 F) s (fun g => pv v (g 1 0)) (fun g => pv v (g 1 1))
      (fun j h0 _ => by simpa using (nat_isUnit (F := F) j h0).map (pv v))
      (fun g _ => map_unit_or_unit (pv v) g)
    exact ⟨n, fun g hg => (hn g hg).ne_zero, fun h1 h2 => absurd ⟨h1, h2⟩ hgood⟩

private theorem eventually_good {F : Type} [Field F] [NumberField F] (s : Finset (G1 F)) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, (∀ g ∈ s, IntAt v g) ∧
      ∀ j : ℕ, 0 < j → j ≤ s.card → Valued.v (j : v.adicCompletion F) = 1 := by
  refine Filter.Eventually.and ((Filter.eventually_all_finset s).2 fun g _ => eventually_intAt g) ?_
  have h : ∀ j ∈ Finset.Icc 1 s.card, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
      Valued.v (j : v.adicCompletion F) = 1 := by
    intro j hj
    have hu := ((isUnit_adele_iff _).1 (nat_isUnit (F := F) j (Finset.mem_Icc.1 hj).1)).2.2
    filter_upwards [hu] with v hv
    have e : (((j : ℕ) : A F)).2 v = (j : v.adicCompletion F) := map_natCast (pv v) j
    rwa [e] at hv
  filter_upwards [(Filter.eventually_all_finset _).2 h] with v hv j h0 hj
  exact hv j (Finset.mem_Icc.2 ⟨h0, hj⟩)

theorem UpperTheory.ConvolutionTheory.R2.cellGeneric :
    ∀ (F : Type) [Field F] [NumberField F] (s : Finset (G1 F)), ∃ x : A F, ∀ g ∈ s, g * nL x ∈ Cell F := by
  intro F _ _ s
  choose ni hi using inf_step s
  choose nf hf hf' using fin_step s
  let x : A F := (fun w => (ni w : w.Completion),
    ⟨fun v => (nf v : v.adicCompletion F), Filter.Eventually.of_forall fun v => natCast_mem _ _⟩)
  refine ⟨x, fun g hg => ?_⟩
  change IsUnit ((g * nL x) 1 0)
  have h00 : (nL x) 0 0 = 1 := rfl
  have h10 : (nL x) 1 0 = x := rfl
  rw [specialLinear_mul_entry, h00, h10, mul_one, isUnit_adele_iff]
  refine ⟨fun w => hi w g hg, fun v => hf v g hg, ?_⟩
  filter_upwards [eventually_good s] with v hv
  exact hf' v hv.1 hv.2 g hg
end

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2

variable {F : Type} [Field F] [NumberField F]

theorem eq_top_of_nU_nL (H : Subgroup (G1 F)) (hn : ∀ b, nU b ∈ H) (hl : ∀ c, nL c ∈ H) : H = ⊤ := by
  refine eq_top_iff.2 fun g _ => ?_
  obtain ⟨x, hx⟩ := cellGeneric F {g}
  obtain ⟨b₁, a, b₂, h⟩ := (mem_cell_iff _).1 (hx g (Finset.mem_singleton_self g))
  rw [← H.mul_mem_cancel_right (hl x), h, mul_assoc (nU b₁), mD_mul_wW]
  exact mul_mem (mul_mem (hn _) (mul_mem (mul_mem (hn _) (hl _)) (hn _))) (hn _)
theorem eq_top_of_nU_wW (H : Subgroup (G1 F)) (hn : ∀ b, nU b ∈ H) (hw : wW F ∈ H) : H = ⊤ :=
  eq_top_of_nU_nL H hn fun c => by rw [nL_eq]; exact mul_mem (mul_mem hw (hn _)) (inv_mem hw)

theorem Gam_le (H : Subgroup (G1 F)) (hn : ∀ b : F, nU (rt b) ∈ H) (hw : wW F ∈ H) : Gam F ≤ H := by
  have hl : ∀ c : F, nL (rt c) ∈ H := fun c => by
    rw [nL_eq, rt, ← map_neg]; exact mul_mem (mul_mem hw (hn _)) (inv_mem hw)
  have key : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) F, γ 1 0 ≠ 0 → ratS F γ ∈ H := fun γ hc => by
    have e : ((IdeleGroup.diagonal F (Units.mk0 _ hc))⁻¹ : (A F)ˣ).val = rt (γ 1 0)⁻¹ := rfl
    have e' : (IdeleGroup.diagonal F (Units.mk0 _ hc) : (A F)ˣ).val = rt (γ 1 0) := rfl
    rw [cell_normal (ratS F γ) (IdeleGroup.diagonal F (Units.mk0 _ hc)) rfl, mul_assoc (nU _), mD_mul_wW, inv_neg, inv_inv,
      Units.val_neg, Units.val_neg, neg_neg, e, e', ratS_apply, ratS_apply]
    simp only [rt, ← map_mul, ← map_neg]
    exact mul_mem (mul_mem (hn _) (mul_mem (mul_mem (hn _) (hl _)) (hn _))) (hn _)
  rintro _ ⟨γ, rfl⟩
  by_cases hc : γ 1 0 = 0
  · obtain ⟨w, hw'⟩ := wW_mem (F := F)
    have h10 : w 1 0 = -1 := by
      haveI := AdeleBaseChange.nontrivial_adeleRing F
      apply (algebraMap F (A F)).injective
      simpa using (ratS_apply w 1 0).symm.trans (congrArg (fun g : G1 F => g 1 0) hw')
    rw [← H.mul_mem_cancel_right hw, ← hw', ← map_mul]
    refine key _ ?_
    have hd := γ.det_coe
    rw [Matrix.det_fin_two, hc] at hd
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hc, h10]
    intro h
    have : γ.1 1 1 = 0 := by simpa using h
    simp [this] at hd
  · exact key γ hc

end UpperTheory.ConvolutionTheory.R2

end
end
