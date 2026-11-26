module

public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.IsHolVOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.PCuspFin
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatLoc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IntegralityOfNormCoefficients

@[expose] public section

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.HyperbolicKernelAlgebraProof
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.HyperbolicKernelAlgebraLemmas

variable {F : Type} [Field F] [NumberField F]

def rotA (θ : TR.Rinf F) : GL (Fin 2) (TR.Rinf F) where
  val := !![fun v => Real.cos (θ v), fun v => Real.sin (θ v); fun v => -Real.sin (θ v), fun v => Real.cos (θ v)]
  inv := !![fun v => Real.cos (θ v), fun v => -Real.sin (θ v); fun v => Real.sin (θ v), fun v => Real.cos (θ v)]
  val_inv := by
    ext i j v
    have := Real.sin_sq_add_cos_sq (θ v)
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ] <;> nlinarith
  inv_val := by
    ext i j v
    have := Real.sin_sq_add_cos_sq (θ v)
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ] <;> nlinarith

omit [NumberField F] in
theorem rotA_add (θ η : TR.Rinf F) : rotA (θ + η) = rotA θ * rotA η := by
  ext i j v
  fin_cases i <;> fin_cases j <;> simp [rotA, Matrix.mul_apply, Fin.sum_univ_succ, Real.cos_add, Real.sin_add] <;> ring

omit [NumberField F] in
theorem rotA_zero : rotA (0 : TR.Rinf F) = 1 := by
  ext i j v
  fin_cases i <;> fin_cases j <;> simp [rotA]

theorem rotA_deriv (θ : TR.Rinf F) :
    HasDerivAt (fun t : ℝ => TR.toL (rotA (t • θ)).val) (TR.toL !![0, θ; -θ, 0]) 0 := by
  refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun v => ?_
  have h : HasDerivAt (fun t : ℝ => t * θ v) (θ v) 0 := by simpa using (hasDerivAt_id (0 : ℝ)).mul_const (θ v)
  fin_cases i <;> fin_cases j
  · simpa [rotA] using h.cos
  · simpa [rotA] using h.sin
  · simpa [rotA] using h.sin.fun_neg
  · simpa [rotA] using h.cos

variable [IsTotallyReal F]

theorem lie_rotV {k : InfinitePlace F → ℕ} {φ : TR.Sm F 2}
    (hw : ∀ v, TR.Eop v 0 1 φ - TR.Eop v 1 0 φ = (Complex.I * k v) • φ) (θ : TR.Rinf F) :
    TR.lie F 2 (TR.toL !![0, θ; -θ, 0]) φ = (∑ v, Complex.I * k v * ((θ v : ℝ) : ℂ)) • φ := by
  classical
  have e : (TR.toL !![0, θ; -θ, 0] : TR.Lie F 2) = ∑ v, θ v • ((TR.toL (Matrix.single 0 1 (Pi.single v 1)) : TR.Lie F 2) -
      TR.toL (Matrix.single 1 0 (Pi.single v 1))) := by
    ext i j w
    fin_cases i <;> fin_cases j <;> simp [Finset.sum_apply, Matrix.single, Pi.single_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, map_sum, LinearMap.sum_apply, Finset.sum_smul]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [map_smul, map_sub, LinearMap.smul_apply, LinearMap.sub_apply, mul_comm, mul_smul, ← hw v]
  simp only [TR.Eop]
  congr!

theorem rot_eq {k : InfinitePlace F → ℕ} {φ : TR.Sm F 2}
    (hw : ∀ v, TR.Eop v 0 1 φ - TR.Eop v 1 0 φ = (Complex.I * k v) • φ) (θ : TR.Rinf F) (g : GA F 2) :
    φ.1 (g * TR.infGL F 2 (rotA θ)) * Complex.exp (-∑ v, Complex.I * k v * ((θ v : ℝ) : ℂ)) = φ.1 g := by
  set s : ℂ := ∑ v, Complex.I * k v * ((θ v : ℝ) : ℂ) with hs
  set f : ℝ → ℂ := fun t => φ.1 (g * TR.infGL F 2 (rotA (t • θ))) with hf
  have hd : ∀ t, HasDerivAt f (s * f t) t := fun t => by
    have h1 := TR.hasDerivAt_curve φ (g * TR.infGL F 2 (rotA (t • θ))) (fun u : ℝ => rotA (u • θ)) _
      (by simp [rotA_zero]) (rotA_deriv θ)
    rw [← TR.lie_apply, lie_rotV hw] at h1
    have h2 : HasDerivAt (fun u : ℝ => f (t + u)) (s * f t) 0 := by
      convert h1 using 2
      · simp only [hf, add_smul, rotA_add, map_mul, mul_assoc]
    have h3 := HasDerivAt.comp_add_const t (-t) (f := fun u : ℝ => f (t + u)) (by simpa using h2)
    simpa using h3
  have he : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (-s * t)) (Complex.exp (-s * t) * -s) t := fun t => by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (-s)).cexp
  have hz : ∀ t, HasDerivAt (fun t : ℝ => f t * Complex.exp (-s * t)) 0 t := fun t => by
    have := (hd t).fun_mul (he t)
    rwa [show s * f t * Complex.exp (-s * t) + f t * (Complex.exp (-s * t) * -s) = 0 by ring] at this
  have hc := is_const_of_deriv_eq_zero (fun t => (hz t).differentiableAt) (fun t => (hz t).deriv) 1 0
  simpa [hf, rotA_zero] using hc

theorem infGL_scalar (ρ : (TR.Rinf F)ˣ) :
    TR.infGL F 2 (Matrix.GeneralLinearGroup.scalar (Fin 2) ρ) = Matrix.GeneralLinearGroup.scalar (Fin 2) (TR.infId F ρ) := by
  have h1 : TR.pInf F (TR.infId F ρ).val = ρ.val := by
    change TR.pInf F (1 - TR.sInf F 1 + TR.sInf F _) = _
    have h : ∀ x, TR.pInf F (TR.sInf F x) = x := fun x => (TR.infEq F).symm_apply_apply x
    simp [h]
  have h2 : pFin F (TR.infId F ρ).val = 1 := by
    change (1 : Af F) - 0 + 0 = 1
    simp
  refine TR.ga_ext ?_ ?_
  · rw [TR.pInf_infGL]
    refine Units.ext (Matrix.ext fun i j => ?_)
    fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.scalar, Matrix.GeneralLinearGroup.map, h1]
  · rw [TR.pFin_infGL]
    refine Units.ext (Matrix.ext fun i j => ?_)
    fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.scalar, Matrix.GeneralLinearGroup.map, h2]

theorem fin_expU {ω : HChar F} (h : IsOfFinOrder ω) (z : TR.Rinf F) : ω.1 (TR.infId F (TR.expU z)) = 1 := by
  obtain ⟨n, hn, e⟩ := isOfFinOrder_iff_pow_eq_one.1 h
  have e1 : TR.expU z = TR.expU ((n : ℝ)⁻¹ • z) ^ n := by
    refine Units.ext (funext fun i => ?_)
    have : (n : ℝ) ≠ 0 := by positivity
    simp only [Units.val_pow_eq_pow_val, Pi.pow_apply, TR.expU_val, ← Real.exp_nat_mul, Pi.smul_apply, smul_eq_mul]
    congr 1
    field_simp
  rw [e1, map_pow, map_pow]
  have e2 : ω.1 ^ n = 1 := congrArg Subtype.val e
  exact DFunLike.congr_fun e2 _

theorem scal {k : InfinitePlace F → ℕ} {c : Pl F → ℕ} {ω : HChar F} (hω : IsOfFinOrder ω) {φ : TR.Sm F 2}
    (hφ : IsHolV k c ω φ) (z : TR.Rinf F) (h : GA F 2) :
    φ.1 (h * TR.infGL F 2 (Matrix.GeneralLinearGroup.scalar (Fin 2) (TR.expU z))) = φ.1 h := by
  rw [infGL_scalar, ← GlobalTheory.CuspRep.scalar_comm, hφ.cent, fin_expU hω]
  simp

theorem inf_fin_comm (y : GL (Fin 2) (TR.Rinf F)) (x : GF F) :
    TR.infGL F 2 y * finGL F 2 x = finGL F 2 x * TR.infGL F 2 y :=
  TR.ga_ext (by simp only [map_mul, TR.pInf_infGL, TR.pInf_finGL, mul_one, one_mul])
    (by simp only [map_mul, TR.pFin_infGL, pFin_finGL, mul_one, one_mul])

theorem stab {k : InfinitePlace F → ℕ} {c : Pl F → ℕ} {ω : HChar F} (hω : IsOfFinOrder ω) {φ : TR.Sm F 2}
    (hφ : IsHolV k c ω φ) (r : GL (Fin 2) (TR.Rinf F)) (hr : ∀ v, gv v r • iP = iP) (h : GA F 2) :
    φ.1 (h * TR.infGL F 2 r) * ∏ v, j1 (k v) (gv v r) iP = φ.1 h := by
  have hgv : ∀ v i j, (gv v r) i j = r i j v := fun v i j => rfl
  have hE : ∀ v, r 1 1 v = r 0 0 v ∧ r 1 0 v = -r 0 1 v := fun v => by
    have h1 := congrArg Subtype.val (hr v)
    rw [coe_smul, div_eq_iff (den_ne _ iP.2)] at h1
    have hre := congrArg Complex.re h1
    have him := congrArg Complex.im h1
    simp [num, den, iP, hgv] at hre him
    constructor <;> linarith
  set w : InfinitePlace F → ℂ := fun v => ⟨r 0 0 v, r 0 1 v⟩ with hw
  have hw0 : ∀ v, w v ≠ 0 := fun v h0 => by
    have ha : r 0 0 v = 0 := congrArg Complex.re h0
    have hb : r 0 1 v = 0 := congrArg Complex.im h0
    apply (gv v r).det_ne_zero
    rw [det_eq]
    simp only [hgv, (hE v).1, (hE v).2, ha, hb]
    ring
  have hρ : ∀ v, 0 < ‖w v‖ := fun v => norm_pos_iff.2 (hw0 v)
  set θ : TR.Rinf F := fun v => Complex.arg (w v) with hθ
  set u := TR.expU (fun v => Real.log ‖w v‖) with hu0
  have hu : ∀ v, (u : TR.Rinf F) v = ‖w v‖ := fun v => by
    rw [hu0, TR.expU_val, Real.exp_log (hρ v)]
  have hc : ∀ v, Real.cos (θ v) = r 0 0 v / ‖w v‖ := fun v => Complex.cos_arg (hw0 v)
  have hs : ∀ v, Real.sin (θ v) = r 0 1 v / ‖w v‖ := fun v => Complex.sin_arg _
  have hdec : r = Matrix.GeneralLinearGroup.scalar (Fin 2) u * rotA θ := by
    ext i j v
    have h0 := (hρ v).ne'
    fin_cases i <;> fin_cases j <;>
      simp [rotA, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.GeneralLinearGroup.scalar, hu, hc, hs, (hE v).1, (hE v).2] <;>
      field_simp
  have hj : ∀ v, j1 (k v) (gv v r) iP = Complex.exp (-(Complex.I * k v * ((θ v : ℝ) : ℂ))) := fun v => by
    unfold j1
    have hden : den (gv v r) iP.1 = (‖w v‖ : ℂ) * Complex.exp (-((θ v : ℝ) : ℂ) * Complex.I) := by
      rw [Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos, ← Complex.ofReal_sin, hc, hs]
      have h0 := (hρ v).ne'
      apply Complex.ext <;> simp [den, hgv, (hE v).1, (hE v).2, iP] <;> field_simp
    have hdet : |(gv v r).val.det| = ‖w v‖ ^ 2 := by
      rw [det_eq, Complex.sq_norm, Complex.normSq_apply]
      simp only [hgv, (hE v).1, (hE v).2, hw]
      rw [abs_of_nonneg (by nlinarith [mul_self_nonneg (r 0 0 v), mul_self_nonneg (r 0 1 v)])]
      ring
    have hp : (‖w v‖ ^ 2) ^ (-(k v : ℝ) / 2) = (‖w v‖ ^ (k v))⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), ← Real.rpow_natCast, ← Real.rpow_neg (norm_nonneg _)]
      congr 1
      push_cast
      ring
    rw [hden, hdet, hp, mul_pow, ← Complex.exp_nat_mul, Complex.ofReal_inv, Complex.ofReal_pow, mul_right_comm,
      mul_inv_cancel₀ (pow_ne_zero _ (by exact_mod_cast (hρ v).ne')), one_mul]
    congr 1
    ring
  have hinf : h * TR.infGL F 2 r =
      (h * TR.infGL F 2 (Matrix.GeneralLinearGroup.scalar (Fin 2) u)) * TR.infGL F 2 (rotA θ) := by
    rw [mul_assoc, ← map_mul, ← hdec]
  rw [Finset.prod_congr rfl fun v _ => hj v, ← Complex.exp_sum, Finset.sum_neg_distrib, hinf, rot_eq hφ.wt θ,
    hu0, scal hω hφ]

theorem key (hB : B1b) {k : InfinitePlace F → ℕ} {c : Pl F → ℕ} {ω : HChar F} (hω : IsOfFinOrder ω) {φ : TR.Sm F 2}
    (hφ : IsHolV k c ω φ) (g g' : GL (Fin 2) (TR.Rinf F)) (x : GF F) (h : ∀ v, gv v g • iP = gv v g' • iP) :
    φ.1 (TR.infGL F 2 g' * finGL F 2 x) * ∏ v, j1 (k v) (gv v g') iP =
      φ.1 (TR.infGL F 2 g * finGL F 2 x) * ∏ v, j1 (k v) (gv v g) iP := by
  obtain ⟨r, rfl⟩ : ∃ r, g' = g * r := ⟨g⁻¹ * g', by group⟩
  have hs : ∀ v, gv v r • iP = iP := fun v => by
    have := h v
    rw [map_mul, mul_smul] at this
    exact ((smul_left_cancel_iff _).1 this).symm
  have hj : ∀ v, j1 (k v) (gv v (g * r)) iP = j1 (k v) (gv v g) iP * j1 (k v) (gv v r) iP := fun v => by
    rw [map_mul, hB.1, hs v]
  have hc : TR.infGL F 2 (g * r) * finGL F 2 x = (TR.infGL F 2 g * finGL F 2 x) * TR.infGL F 2 r := by
    rw [map_mul, mul_assoc, mul_assoc, inf_fin_comm]
  rw [Finset.prod_congr rfl fun v _ => hj v, Finset.prod_mul_distrib, hc,
    ← stab hω hφ r hs (TR.infGL F 2 g * finGL F 2 x)]
  ring

end UpperTheory.Esk.HyperbolicKernelAlgebraLemmas

theorem UpperTheory.Esk.hyperbolic_kernel_algebra_proof : UpperTheory.Esk.B1b → UpperTheory.Esk.B1c → UpperTheory.Esk.H1a := by
  intro hB _ F _ _ _ k c ω φ hω hφ
  classical
  refine ⟨fun p => if h : ∃ g : GL (Fin 2) (TR.Rinf F), (fun v => UpperTheory.Esk.gv v g • UpperTheory.Esk.iP) = p.1 then
      φ.1 (TR.infGL F 2 h.choose * finGL F 2 p.2) * ∏ v, UpperTheory.Esk.j1 (k v) (UpperTheory.Esk.gv v h.choose) UpperTheory.Esk.iP else 0,
    fun g x => ?_⟩
  have h : ∃ g' : GL (Fin 2) (TR.Rinf F), (fun v => UpperTheory.Esk.gv v g' • UpperTheory.Esk.iP) = fun v => UpperTheory.Esk.gv v g • UpperTheory.Esk.iP :=
    ⟨g, rfl⟩
  dsimp only
  rw [dite_eq_left h]
  exact UpperTheory.Esk.HyperbolicKernelAlgebraLemmas.key hB hω hφ h.choose g x fun v => congrFun h.choose_spec v
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.PfHFinC
open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.GlobalFixedVectors UpperTheory.V.Sd
open Neutral.B1 Formalism.L2.Host UpperTheory.V.Base

namespace UpperTheory.Esk.HFinCAux

theorem exists_rep {K ι A : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [Finite ι] (e : ι → K) (r : A → K)
    (χ : A → ℂ) (h : ∀ x, ∃ i a, x = e i * r a) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (_ : FiniteDimensional ℂ W) (ρ : Representation ℂ K W),
      GlobalTheory.Published.AutFin.IsContRep ρ ∧
        ∀ f : K → ℂ, Continuous f → (∀ x a, f (x * r a) = χ a * f x) → f ∈ GlobalTheory.Published.AutFin.coeffSpan ρ := by
  let V : Submodule ℂ (K → ℂ) :=
    { carrier := {f | Continuous f ∧ ∀ x a, f (x * r a) = χ a * f x}
      add_mem' := fun hf hg => ⟨hf.1.add hg.1, fun x a => by simp [hf.2, hg.2, mul_add]⟩
      zero_mem' := ⟨continuous_const, fun x a => by simp⟩
      smul_mem' := fun c f hf => ⟨hf.1.const_smul c, fun x a => by simp [hf.2, mul_left_comm]⟩ }
  haveI : FiniteDimensional ℂ V := by
    refine Module.Finite.of_injective ((LinearMap.funLeft ℂ ℂ e).comp V.subtype) ?_
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro f hf
    ext x
    obtain ⟨i, a, rfl⟩ := h x
    have : f.1 (e i) = 0 := congrFun hf i
    rw [f.2.2, this]; simp
  let L : Representation ℂ K V :=
    { toFun := fun k =>
        { toFun := fun f => ⟨fun x => f.1 (k⁻¹ * x), f.2.1.comp (continuous_const.mul continuous_id), fun x a => by
            simp only [← mul_assoc, f.2.2]⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      map_one' := by ext f x; simp
      map_mul' := fun k k' => by ext f x; simp [mul_assoc] }
  refine ⟨Module.Dual ℂ V, inferInstance, inferInstance, inferInstance, L.dual, fun l w => ?_, fun f hf hf' => ?_⟩
  · obtain ⟨f, rfl⟩ := (Module.evalEquiv ℂ V).surjective l
    change Continuous fun k => w (L k⁻¹ f)
    refine w.continuous_of_finiteDimensional.comp (Continuous.subtype_mk (continuous_pi fun x => ?_) _)
    exact f.2.1.comp (continuous_inv.inv.mul continuous_const)
  · refine Submodule.subset_span ⟨Module.Dual.eval ℂ V ⟨f, hf, hf'⟩, (LinearMap.proj 1).comp V.subtype, funext fun k => ?_⟩
    change f k = f (k⁻¹⁻¹ * 1)
    simp

variable {F : Type} [Field F] [NumberField F]

theorem local_mem_principal_congruence {M : ℕ} (w : HeightOneSpectrum (𝓞 F)) (c : ℕ)
    (hM : (M : w.adicCompletionIntegers F) ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c)
    {k : GL (Fin 2) (Af F)} (hk : k ∈ KLev F 2 M) : GeneralLinearGroup.map (pLoc F w) k ∈ K1 w c := by
  obtain ⟨g, hg, rfl⟩ := hk
  let p : Ohat F →+* w.adicCompletionIntegers F :=
    ((pLoc F w).comp (Ohat F).subtype).codRestrict (w.adicCompletionIntegers F) fun x => GlobalFixedVectors.mem_Ohat.1 x.2 w
  refine ⟨GeneralLinearGroup.map p g, ?_, Units.ext rfl⟩
  have key : GeneralLinearGroup.map (n := Fin 2)
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c)) (GeneralLinearGroup.map p g) = 1 := by
    let q := Ideal.quotientMap (I := Ideal.span {(M : ↥(Ohat F))}) (IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c) p
      ((Ideal.span_singleton_le_iff_mem _).2 (by simpa using hM))
    have := congrArg (GeneralLinearGroup.map q) (MonoidHom.mem_ker.1 hg)
    rw [map_one] at this
    rw [← this]
    rfl
  exact Subgroup.mem_comap.2 (key ▸ one_mem _)

theorem exists_level (c : HeightOneSpectrum (𝓞 F) → ℕ) (hc : {w | c w ≠ 0}.Finite) :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ w : HeightOneSpectrum (𝓞 F),
      (M : w.adicCompletionIntegers F) ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c w := by
  refine ⟨∏ w ∈ hc.toFinset, Ideal.absNorm w.asIdeal ^ c w, ?_, fun w => ?_⟩
  · refine Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ ?_)
    exact fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  · by_cases h : c w = 0
    · simp [h]
    obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem (fun w : HeightOneSpectrum (𝓞 F) => Ideal.absNorm w.asIdeal ^ c w)
      (hc.mem_toFinset.2 h)
    rw [hm, Nat.cast_mul, Nat.cast_pow]
    refine Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow ?_ _)
    have h1 := Ideal.absNorm_mem w.asIdeal
    rw [← map_natCast (algebraMap (𝓞 F) (w.adicCompletionIntegers F))]
    generalize (Ideal.absNorm w.asIdeal : 𝓞 F) = x at h1
    refine (Valuation.mem_maximalIdeal_iff _ (Valued.v : Valuation (w.adicCompletion F) _)).2 ?_
    have h2 : Valued.v (algebraMap (𝓞 F) (w.adicCompletion F) x) < 1 := by
      rw [IsScalarTower.algebraMap_apply (𝓞 F) F (w.adicCompletion F)]
      exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _).trans_lt ((w.valuation_lt_one_iff_mem x).2 h1)
    exact h2

theorem fixed_KLev {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin 2) (Af F)) V) {M : ℕ} (v : V)
    (ho : IsOpen {k | ρ k v = v}) (h : ∀ w, ∀ k ∈ KLev F 2 M, ρ (locGL F 2 w (GeneralLinearGroup.map (pLoc F w) k)) v = v) :
    ∀ k ∈ KLev F 2 M, ρ k v = v := by
  classical
  have key : ∀ S : Finset (HeightOneSpectrum (𝓞 F)), (∀ k ∈ KAway 2 M S, ρ k v = v) → ∀ k ∈ KAway 2 M ∅, ρ k v = v := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact id
    | insert w S hw ih =>
      refine fun hv => ih fun k hk => ?_
      have h1 := loc_mem w (mem_KAway.1 hk).1
      have h2 : k * (locGL F 2 w (GeneralLinearGroup.map (pLoc F w) k))⁻¹ ∈ KAway 2 M (insert w S) := by
        refine mem_KAway.2 ⟨mul_mem (mem_KAway.1 hk).1 (inv_mem h1), fun u hu => ?_⟩
        by_cases huw : u = w
        · subst huw; simp [pLoc_locGL]
        · simp [pLoc_locGL_of_ne huw, (mem_KAway.1 hk).2 u ((Finset.mem_insert.1 hu).resolve_left huw)]
      have h3 := h w k (mem_KAway.1 hk).1
      have h4 := hv _ h2
      rwa [← h3, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, h3] at h4
  obtain ⟨S, hS⟩ := exists_KAway_subset (M := M) (ho.mem_nhds (by simp))
  exact fun k hk => key S (fun k hk => hS hk) k (mem_KAway.2 ⟨hk, by simp⟩)

noncomputable def rot (θ : TR.Rinf F) : TR.Kinf F 2 :=
  ⟨!![fun v => Real.cos (θ v), fun v => Real.sin (θ v); fun v => -Real.sin (θ v), fun v => Real.cos (θ v)], by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j v
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply] <;>
      nlinarith [Real.sin_sq_add_cos_sq (θ v)]⟩

noncomputable def eps (s : InfinitePlace F → ℤˣ) : TR.Kinf F 2 :=
  ⟨!![1, 0; 0, fun v => ((s v : ℤ) : ℝ)], by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j v
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply]
    rcases Int.units_eq_one_or (s v) with h | h <;> simp [h]⟩

omit [NumberField F] in
theorem rot_add (θ η : TR.Rinf F) : rot (θ + η) = rot θ * rot η := by
  ext i j v
  fin_cases i <;> fin_cases j <;> simp [rot, Matrix.mul_apply, Fin.sum_univ_succ, Real.cos_add, Real.sin_add] <;> ring

omit [NumberField F] in
theorem rot_zero : rot (0 : TR.Rinf F) = 1 := by
  ext i j v
  fin_cases i <;> fin_cases j <;> simp [rot]

theorem real_dec {a b c d : ℝ} (h1 : a * a + b * b = 1) (h2 : a * c + b * d = 0) (h3 : c * c + d * d = 1) :
    ∃ (s : ℤˣ) (t : ℝ), a = Real.cos t ∧ b = Real.sin t ∧ c = -((s : ℤ) * Real.sin t) ∧ d = (s : ℤ) * Real.cos t := by
  have hn : ‖(⟨a, b⟩ : ℂ)‖ = 1 := by
    rw [Complex.norm_def, Complex.normSq_mk, h1, Real.sqrt_one]
  have h0 : (⟨a, b⟩ : ℂ) ≠ 0 := fun h => by simp [h] at hn
  have ha : a = Real.cos (Complex.arg ⟨a, b⟩) := by rw [Complex.cos_arg h0, hn, div_one]
  have hb : b = Real.sin (Complex.arg ⟨a, b⟩) := by rw [Complex.sin_arg, hn, div_one]
  have hc : c = -((a * d - b * c) * b) := by linear_combination (-c) * h1 + a * h2
  have hd : d = (a * d - b * c) * a := by linear_combination (-d) * h1 + b * h2
  have hs : (a * d - b * c) * (a * d - b * c) = 1 := by
    linear_combination (c * c + d * d) * h1 + h3 - (a * c + b * d) * h2
  rcases mul_self_eq_one_iff.1 hs with h | h
  · exact ⟨1, _, ha, hb, by rw [← hb]; simpa [h] using hc, by rw [← ha]; simpa [h] using hd⟩
  · exact ⟨-1, _, ha, hb, by rw [← hb]; simpa [h] using hc, by rw [← ha]; simpa [h] using hd⟩

omit [NumberField F] in
theorem dec (x : TR.Kinf F 2) : ∃ s θ, x = eps s * rot θ := by
  have h := Matrix.mem_unitaryGroup_iff.1 x.2
  have e : ∀ i j v, x.1 i 0 v * x.1 j 0 v + x.1 i 1 v * x.1 j 1 v = (1 : Matrix (Fin 2) (Fin 2) (TR.Rinf F)) i j v := fun i j v => by
    rw [← h]; simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply]
  choose s θ h1 h2 h3 h4 using fun v => real_dec (a := x.1 0 0 v) (b := x.1 0 1 v) (c := x.1 1 0 v) (d := x.1 1 1 v)
    (by simpa using e 0 0 v) (by simpa using e 0 1 v) (by simpa using e 1 1 v)
  refine ⟨s, θ, ?_⟩
  ext i j v
  fin_cases i <;> fin_cases j <;> simp [rot, eps, Matrix.mul_apply, Fin.sum_univ_succ, h1, h2, h3, h4]

variable [IsTotallyReal F]

theorem cont (φ : TR.Sm F 2) (g : GA F 2) : Continuous fun k : TR.Kinf F 2 => (TR.cptRep F 2 k φ).1 g := by
  have e : (fun k : TR.Kinf F 2 => (TR.cptRep F 2 k φ).1 g) = fun k : TR.Kinf F 2 => TR.chart φ.1 g (TR.toL k.1) :=
    funext fun k => (TR.chart_val φ.1 g (Unitary.toUnits k)).symm
  rw [e]
  exact (φ.2 g).continuousOn.comp_continuous continuous_subtype_val fun k => TR.val_mem_invSet (Unitary.toUnits k)

theorem rot_eig (φ : TR.Sm F 2) (z : InfinitePlace F → ℂ) (h : ∀ v, TR.Eop v 0 1 φ - TR.Eop v 1 0 φ = z v • φ) (g : GA F 2) (θ : TR.Rinf F) :
    φ.1 (g * TR.infGL F 2 (Unitary.toUnits (rot θ))) = Complex.exp (∑ v, z v * (θ v : ℂ)) * φ.1 g := by
  classical
  set μ : ℂ := ∑ v, z v * (θ v : ℂ) with hμ
  let X : TR.Lie F 2 := TR.toL !![0, θ; -θ, 0]
  have hX : X = ∑ v, θ v • (TR.toL (Matrix.single 0 1 (Pi.single v 1)) - TR.toL (Matrix.single 1 0 (Pi.single v 1))) := by
    ext i j u
    fin_cases i <;> fin_cases j <;> simp [X, Finset.sum_apply, Pi.single_apply]
  have hL : TR.lie F 2 X φ = μ • φ := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hX, map_sum, LinearMap.sum_apply, hμ, Finset.sum_smul]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [map_smul, map_sub, LinearMap.smul_apply, LinearMap.sub_apply, mul_comm, mul_smul, Complex.coe_smul, ← h v]
    simp only [TR.Eop]
  have hc : HasDerivAt (fun t : ℝ => TR.toL (Unitary.toUnits (rot (t • θ))).val) X 0 := by
    refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun v => ?_
    have h1 : HasDerivAt (fun t : ℝ => t * θ v) (θ v) 0 := by simpa using (hasDerivAt_id (0 : ℝ)).mul_const (θ v)
    fin_cases i <;> fin_cases j
    · simpa [X, rot] using h1.cos
    · simpa [X, rot] using h1.sin
    · simpa [X, rot] using h1.sin.fun_neg
    · simpa [X, rot] using h1.cos
  let f : ℝ → ℂ := fun t => φ.1 (g * TR.infGL F 2 (Unitary.toUnits (rot (t • θ))))
  have hf : ∀ t, HasDerivAt f (μ * f t) t := fun t => by
    have h1 := TR.hasDerivAt_curve φ (g * TR.infGL F 2 (Unitary.toUnits (rot (t • θ)))) (fun s => Unitary.toUnits (rot (s • θ))) X
      (by rw [zero_smul, rot_zero, map_one]) hc
    rw [← TR.lie_apply, hL] at h1
    have h2 : HasDerivAt (fun s => f (t + s)) (μ * f t) 0 := by
      simpa only [f, add_smul, rot_add, map_mul, mul_assoc] using! h1
    have h3 := HasDerivAt.comp_sub_const t t (f := fun s => f (t + s)) (by rw [sub_self]; exact h2)
    simpa using h3
  have hg : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Complex.exp (-μ * s) * f s) 0 t := fun t => by
    have h1 : HasDerivAt (fun s : ℝ => -μ * (s : ℂ)) (-μ) t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (-μ)
    exact (h1.cexp.fun_mul (hf t)).congr_deriv (by ring)
  have h4 := is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt) (fun t => (hg t).deriv) 1 0
  simp only [f, one_smul, zero_smul, rot_zero, map_one, mul_one, Complex.ofReal_one, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero, one_mul] at h4
  rw [← h4, ← mul_assoc, ← Complex.exp_add]
  simp

end UpperTheory.Esk.HFinCAux

open UpperTheory.Esk.HFinCAux in
theorem UpperTheory.Esk.pf_HFinC : UpperTheory.Esk.HCap → UpperTheory.Esk.HFinC := by
  intro hcap F _ _ _ k c hc ω hω
  obtain ⟨M, hM1, hM⟩ := exists_level c hc
  have hfix : ∀ φ : TR.Sm F 2, UpperTheory.Esk.IsHolV k c ω φ → ∀ u ∈ KLev F 2 M, TR.finRep F 2 u φ = φ := fun φ hφ =>
    fixed_KLev _ φ hφ.aut.level fun w u hu => hφ.level w _ (local_mem_principal_congruence w _ (hM w) hu)
  obtain ⟨W, _, _, _, ρ, hρ, hf⟩ := exists_rep (eps (F := F)) (rot (F := F))
    (fun θ => Complex.exp (∑ v, Complex.I * (k v : ℂ) * (θ v : ℂ))) dec
  have := UpperTheory.V.Af.cuspFormsFiniteReal F 2 (KLev F 2 M) (isOpen_KLev hM1) W ρ hρ
    fun v u => (u + ((k v : ℂ) - 1) / 2) * (u - ((k v : ℂ) - 1) / 2)
  refine Submodule.finiteDimensional_of_le (S₂ := _) (Submodule.span_mono (fun φ hφ => ?_) : _ ≤ Submodule.span ℂ
    {φ : TR.Sm F 2 | TR.IsCuspForm φ ∧ (∀ u ∈ KLev F 2 M, TR.finRep F 2 u φ = φ) ∧
      (∀ g : GA F 2, (fun u : TR.Kinf F 2 => (TR.cptRep F 2 u φ).1 g) ∈ GlobalTheory.Published.AutFin.coeffSpan ρ) ∧
      ∀ v u, TR.cap v u φ = ((u + ((k v : ℂ) - 1) / 2) * (u - ((k v : ℂ) - 1) / 2)) • φ})
  obtain ⟨hφ', hcusp⟩ := hφ
  refine ⟨hcusp, hfix φ hφ', fun g => hf _ (cont φ g) fun x θ => ?_, (hcap F k c ω hω φ hφ').2⟩
  have := rot_eig φ (fun v => Complex.I * (k v : ℂ)) hφ'.wt (g * TR.infGL F 2 (Unitary.toUnits x)) θ
  rw [mul_assoc, ← map_mul, ← map_mul] at this
  exact this
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.AffOneZero
noncomputable section

open NumberField MeasureTheory Topology Matrix Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Sd UpperTheory.V.Sd.Eis

namespace UpperTheory.Esk.ArchimedeanConjugationLemmas

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem map_aff1 {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (x : R) :
    GeneralLinearGroup.map f (aff 1 x) = aff 1 (f x) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [aff]

theorem aff_one_zero {R : Type} [CommRing R] : aff (1 : Rˣ) (0 : R) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [aff]

theorem aff_mul {R : Type} [CommRing R] (y y' : Rˣ) (x x' : R) : aff y x * aff y' x' = aff (y * y') (y * x' + x) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [aff, Matrix.mul_apply, Fin.sum_univ_succ]

theorem infGL_aff (x : TR.Rinf F) : TR.infGL F 2 (aff 1 x) = aff 1 (TR.sInf F x) := by
  refine TR.ga_ext ?_ ?_
  · rw [TR.pInf_infGL, map_aff1]
    exact congrArg _ ((TR.infEq F).symm_apply_apply x).symm
  · rw [TR.pFin_infGL, map_aff1]
    exact aff_one_zero.symm

theorem infGL_left (a : GL (Fin 2) (TR.Rinf F)) (g : GA F 2) :
    TR.infGL F 2 a * g = g * TR.infGL F 2 ((GeneralLinearGroup.map (TR.pInf F) g)⁻¹ * a * GeneralLinearGroup.map (TR.pInf F) g) :=
  TR.ga_ext (by simp only [map_mul, map_inv, TR.pInf_infGL]; group) (by simp only [map_mul, map_inv, TR.pFin_infGL]; group)

omit [IsTotallyReal F] in
theorem conj_deriv (h : GL (Fin 2) (TR.Rinf F)) (a : ℝ → GL (Fin 2) (TR.Rinf F)) (X : Matrix (Fin 2) (Fin 2) (TR.Rinf F))
    (ha : HasDerivAt (fun t => TR.toL (a t).val) (TR.toL X) 0) :
    HasDerivAt (fun t => TR.toL (h⁻¹ * a t * h).val) (TR.toL ((h⁻¹).val * X * h.val)) 0 :=
  ((TR.rmul (TR.toL h.val)).comp (TR.lmul (TR.toL (h⁻¹).val))).hasFDerivAt.comp_hasDerivAt (0 : ℝ) ha

open Classical in
omit [IsTotallyReal F] in
theorem conj_dec (h : GL (Fin 2) (TR.Rinf F)) (i j : Fin 2) (u : TR.Rinf F) :
    TR.toL ((h⁻¹).val * Matrix.single i j u * h.val) = ∑ v, u v • ∑ a, ∑ b,
      ((((GeneralLinearGroup.map (Pi.evalRingHom (fun _ => ℝ) v) h)⁻¹).val * Matrix.single i j (1 : ℝ) *
        (GeneralLinearGroup.map (Pi.evalRingHom (fun _ => ℝ) v) h).val) a b : ℝ) •
          TR.toL (Matrix.single a b (Pi.single v 1 : TR.Rinf F)) := by
  funext a b w
  simp only [← map_inv]
  generalize h⁻¹ = h'
  fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.single_apply, Fin.sum_univ_two, Pi.single_apply, Finset.sum_apply] <;> ring

omit [IsTotallyReal F] in
theorem nil_curve (u : TR.Rinf F) :
    Continuous (fun t : ℝ => aff (1 : (TR.Rinf F)ˣ) (t • u)) ∧
    (∀ s t : ℝ, aff (1 : (TR.Rinf F)ˣ) ((s + t) • u) = aff 1 (s • u) * aff 1 (t • u)) ∧
    HasDerivAt (fun t : ℝ => TR.toL (aff (1 : (TR.Rinf F)ˣ) (t • u)).val) (TR.toL (Matrix.single 0 1 u)) 0 := by
  refine ⟨Units.continuous_iff.2 ⟨?_, ?_⟩, fun s t => ?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [aff] <;> fun_prop
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [aff, -Matrix.coe_units_inv] <;> fun_prop
  · ext i j : 2
    fin_cases i <;> fin_cases j <;> simp [aff, add_smul, add_comm]
  · refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
    fin_cases i <;> fin_cases j <;> simp [aff, hasDerivAt_const]
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const u

omit [IsTotallyReal F] in
theorem tor_curve (u : TR.Rinf F) (y : ℝ → (TR.Rinf F)ˣ) (hy : ∀ t v, (y t).val v = Real.exp (t * u v)) :
    Continuous (fun t : ℝ => aff (y t) 0) ∧
    (∀ s t : ℝ, aff (y (s + t)) 0 = aff (y s) 0 * aff (y t) 0) ∧
    HasDerivAt (fun t : ℝ => TR.toL (aff (y t) 0).val) (TR.toL (Matrix.single 0 0 u)) 0 := by
  have e : ∀ t, (y t).val = fun v => Real.exp (t * u v) := fun t => funext (hy t)
  have e' : ∀ t, ((y t)⁻¹).val = fun v => Real.exp (-(t * u v)) := fun t =>
    Units.inv_eq_of_mul_eq_one_right (by funext v; simp [hy, ← Real.exp_add])
  refine ⟨Units.continuous_iff.2 ⟨?_, ?_⟩, fun s t => ?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [aff, e] <;> fun_prop
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [aff, -Matrix.coe_units_inv, e'] <;> fun_prop
  · ext i j v
    fin_cases i <;> fin_cases j <;> simp [aff, hy, add_mul, Real.exp_add]
  · refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
    fin_cases i <;> fin_cases j <;> simp [aff, hasDerivAt_const]
    refine hasDerivAt_pi.2 fun v => ?_
    simpa [hy] using ((hasDerivAt_id (0 : ℝ)).mul_const (u v)).exp

theorem ctLeftV [MeasurableSpace (NA F)] [BorelSpace (NA F)] (μ : Measure (NA F)) [μ.IsAddHaarMeasure] (D : Set (NA F))
    (hD : IsAddFundamentalDomain (ratN F 2 1) D μ) (k : InfinitePlace F → ℕ) (c : Pl F → ℕ) (ω : HChar F)
    (hω : IsOfFinOrder ω) (φ : TR.Sm F 2) (hφ : UpperTheory.Esk.IsHolV k c ω φ) (u : TR.Rinf F) (y : ℝ → (TR.Rinf F)ˣ)
    (hy : ∀ t v, (y t).val v = Real.exp (t * u v)) (g : GA F 2) :
    HasDerivAt (fun t => cterm μ D φ.1 (TR.infGL F 2 (aff (y t) 0) * g))
      ((∑ v, (k v : ℂ) / 2 * ((u v : ℝ) : ℂ)) * cterm μ D φ.1 g) 0 := by
  classical
  have hS := UpperTheory.eisenstein_smooth_continuous
  have hB := UpperTheory.eisenstein_constantTerm_of_periodMean_of_upperBlock UpperTheory.periodic_integral_fundamentalDomain_invariant UpperTheory.eisenstein_constantTerm_upperBlock
  have hL := UpperTheory.constant_term_automorphy UpperTheory.eisenstein_smooth_continuous UpperTheory.periodic_integral_fundamentalDomain_invariant UpperTheory.eisenstein_period_derivative UpperTheory.eisenstein_constantTerm_upperBlock
  have hA := UpperTheory.eisenstein_lie_algebra_action
  have hl := hL F μ D hD φ hφ.aut.left hφ.aut.level
  have hb := hB F μ D hD φ.1 (hS F 2 φ hφ.aut.level) hφ.aut.left
  have hi : ∀ X, IntegrableOn (fun x : NA F => (TR.lie F 2 X φ).1 (unip x * g)) D μ := fun X =>
    (hB F μ D hD _ (hl X).1.2 (hl X).1.1).1 g
  let L : TR.Lie F 2 →ₗ[ℝ] ℂ :=
    { toFun := fun X => cterm μ D (TR.lie F 2 X φ).1 g
      map_add' := fun X Y => by
        rw [map_add (f := _)]
        exact integral_add (hi X) (hi Y)
      map_smul' := fun r X => by
        rw [map_smul]
        exact integral_smul r (fun x : NA F => (TR.lie F 2 X φ).1 (unip x * g)) }
  have hsm : ∀ (X) (z : ℂ) (ψ : TR.Sm F 2), TR.lie F 2 X φ = z • ψ → L X = z * cterm μ D ψ.1 g := fun X z ψ e => by
    change cterm μ D (TR.lie F 2 X φ).1 g = _
    rw [e]
    exact integral_const_mul z (fun x : NA F => ψ.1 (unip x * g))
  set h := GeneralLinearGroup.map (TR.pInf F) g with hh
  have key : ∀ (a : ℝ → GL (Fin 2) (TR.Rinf F)) (X : Matrix (Fin 2) (Fin 2) (TR.Rinf F)), Continuous a →
      (∀ s t, a (s + t) = a s * a t) → HasDerivAt (fun t => TR.toL (a t).val) (TR.toL X) 0 →
      HasDerivAt (fun t => cterm μ D φ.1 (TR.infGL F 2 (a t) * g)) (L (TR.toL ((h⁻¹).val * X * h.val))) 0 := by
    intro a X h1 h2 h3
    simp only [infGL_left _ g]
    exact (hl _).2 (fun t => h⁻¹ * a t * h) (by fun_prop) (fun s t => by rw [h2]; group) (conj_deriv h a X h3) g
  have hnil : ∀ x : TR.Rinf F, L (TR.toL ((h⁻¹).val * Matrix.single 0 1 x * h.val)) = 0 := fun x => by
    obtain ⟨h1, h2, h3⟩ := nil_curve x
    have := key _ _ h1 h2 h3
    simp only [infGL_aff, hb.2.1] at this
    exact this.unique (hasDerivAt_const _ _)
  let E : InfinitePlace F → Fin 2 → Fin 2 → TR.Lie F 2 := fun v a b => TR.toL (Matrix.single a b (Pi.single v 1 : TR.Rinf F))
  have hE : ∀ v a b, TR.lie F 2 (E v a b) = TR.Eop v a b := fun _ _ _ => by
    simp only [E, TR.Eop]
  have hdec : ∀ (i j : Fin 2) (x : TR.Rinf F), L (TR.toL ((h⁻¹).val * Matrix.single i j x * h.val)) =
      ∑ v, (x v : ℂ) * ∑ a, ∑ b,
      ((((GeneralLinearGroup.map (Pi.evalRingHom (fun _ => ℝ) v) h)⁻¹).val * Matrix.single i j (1 : ℝ) *
        (GeneralLinearGroup.map (Pi.evalRingHom (fun _ => ℝ) v) h).val) a b : ℝ) * L (E v a b) := fun i j x => by
    rw [conj_dec]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Complex.real_smul, E]
  have hv := fun v : InfinitePlace F => hA (GeneralLinearGroup.map (Pi.evalRingHom (fun _ => ℝ) v) h) (fun a b => L (E v a b))
    ((k v : ℂ) * cterm μ D φ.1 g)
    (by
      rw [← map_add (f := _), hsm _ 0 φ, zero_mul]
      rw [map_add (f := _), hE, hE, zero_smul]
      exact UpperTheory.V.Sd.Hm.trzero F ω hω φ hφ.cent v)
    (by
      rw [← map_sub, hsm _ (Complex.I * (k v : ℂ)) φ, mul_assoc]
      rw [map_sub, hE, hE]
      exact hφ.wt v)
    (by
      rw [← map_sub, ← map_add (f := _), hsm _ Complex.I (TR.lie F 2 (E v 0 1 + E v 1 0) φ)]
      · rfl
      rw [map_sub, map_add (f := _), hE, hE, hE, hE]
      exact hφ.low v)
    (by
      have := hnil (Pi.single v 1)
      rw [hdec, Finset.sum_eq_single v (fun w _ hw => by simp [Pi.single_eq_of_ne hw]) (by simp)] at this
      simpa only [Pi.single_eq_same, Complex.ofReal_one, one_mul] using this)
  obtain ⟨h1, h2, h3⟩ := tor_curve u y hy
  have := key _ _ h1 h2 h3
  rw [hdec] at this
  simp only [hv] at this
  convert this using 1
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun v _ => ?_
  ring

theorem ode {f : ℝ → ℂ} {κ : ℂ} (h : ∀ t, HasDerivAt f (κ * f t) t) : f 1 = Complex.exp κ * f 0 := by
  have h1 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (-κ * t) * f t) 0 t := fun t => by
    have := (((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (-κ)).cexp).mul (h t)
    refine this.congr_deriv ?_
    simp only [Complex.ofRealCLM_apply, Complex.ofReal_one]; ring
  have h2 := is_const_of_deriv_eq_zero (fun t => (h1 t).differentiableAt) (fun t => (h1 t).deriv) 1 0
  simp only [Complex.ofReal_one, mul_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul] at h2
  rw [← h2, ← mul_assoc, ← Complex.exp_add]; simp

theorem ct_grow [MeasurableSpace (NA F)] [BorelSpace (NA F)] (μ : Measure (NA F)) [μ.IsAddHaarMeasure] (D : Set (NA F))
    (hD : IsAddFundamentalDomain (ratN F 2 1) D μ) (k : InfinitePlace F → ℕ) (c : Pl F → ℕ) (ω : HChar F)
    (hω : IsOfFinOrder ω) (φ : TR.Sm F 2) (hφ : UpperTheory.Esk.IsHolV k c ω φ) (T : ℝ) (g : GA F 2) :
    ∃ g' : GA F 2, cterm μ D φ.1 g' = Complex.exp (∑ v, (k v : ℂ) / 2 * ((T : ℝ) : ℂ)) * cterm μ D φ.1 g := by
  let z : ℝ → (TR.Rinf F)ˣ := fun t => ⟨fun _ => Real.exp (t * T), fun _ => Real.exp (-(t * T)),
    by funext v; simp [← Real.exp_add], by funext v; simp [← Real.exp_add]⟩
  have hz : ∀ s t, z (s + t) = z s * z t := fun s t => Units.ext (funext fun v => by simp [z, add_mul, Real.exp_add])
  have h0 : z 0 = 1 := Units.ext (funext fun v => by simp [z])
  have := ode (f := fun t => cterm μ D φ.1 (TR.infGL F 2 (aff (z t) 0) * g))
    (κ := ∑ v, (k v : ℂ) / 2 * ((T : ℝ) : ℂ)) fun t => by
    have h2 := ctLeftV μ D hD k c ω hω φ hφ (fun _ => T) z (fun _ _ => rfl) (TR.infGL F 2 (aff (z t) 0) * g)
    have h3 := HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact h2)
    refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    beta_reduce
    rw [← mul_assoc, ← map_mul, aff_mul, ← hz]; simp
  refine ⟨_, this.trans ?_⟩
  rw [h0, aff_one_zero, map_one, one_mul]

theorem ct_zero [MeasurableSpace (NA F)] [BorelSpace (NA F)] (μ : Measure (NA F)) [μ.IsAddHaarMeasure] (D : Set (NA F))
    (hD : IsAddFundamentalDomain (ratN F 2 1) D μ) (k : InfinitePlace F → ℕ) (c : Pl F → ℕ) (ω : HChar F)
    (hω : IsOfFinOrder ω) (φ : TR.Sm F 2) (hφ : UpperTheory.Esk.IsHolV k c ω φ) (hk : ∀ v, 1 ≤ k v) (C : ℝ)
    (hC : ∀ g, ‖φ.1 g‖ ≤ C) (g : GA F 2) : cterm μ D φ.1 g = 0 := by
  obtain ⟨i1, i2, i3, i4, hco, -, -⟩ := UpperTheory.eisenstein_constantTerm_upperBlock F
  have hfin : μ D ≠ ⊤ := (UpperTheory.periodic_integral_fundamentalDomain_invariant (NA F) (ratN F 2 1) hco μ D hD).1
  set M := C * μ.real D
  have hb : ∀ h, ‖cterm μ D φ.1 h‖ ≤ M := fun h =>
    norm_setIntegral_le_of_norm_le_const (lt_top_iff_ne_top.2 hfin) (fun x _ => hC _)
  set s : ℝ := ∑ v, (k v : ℝ) / 2
  obtain ⟨v₀⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hs : 0 < s := by
    have : (k v₀ : ℝ) / 2 ≤ s := Finset.single_le_sum (f := fun v => (k v : ℝ) / 2) (fun v _ => by positivity) (Finset.mem_univ v₀)
    have h1 : (1 : ℝ) ≤ k v₀ := by exact_mod_cast hk v₀
    linarith
  by_contra hne
  have ha : 0 < ‖cterm μ D φ.1 g‖ := norm_pos_iff.2 hne
  set a := ‖cterm μ D φ.1 g‖
  set T : ℝ := (|M| + 1) / (a * s)
  obtain ⟨g', hg'⟩ := ct_grow μ D hD k c ω hω φ hφ T g
  have e : (∑ v, (k v : ℂ) / 2 * ((T : ℝ) : ℂ)) = ((s * T : ℝ) : ℂ) := by
    simp only [s, Finset.sum_mul]; push_cast; rfl
  have h1 := hb g'
  rw [hg', e, norm_mul, Complex.norm_exp_ofReal] at h1
  have h2 : s * T + 1 ≤ Real.exp (s * T) := Real.add_one_le_exp _
  have h3 : s * T * a = |M| + 1 := by
    simp only [T]; field_simp
  have h4 : M ≤ |M| := le_abs_self M
  nlinarith

end UpperTheory.Esk.ArchimedeanConjugationLemmas

theorem UpperTheory.Esk.pf_H2e : UpperTheory.Esk.H2e := by
  intro F _ _ _ k c ω φ hω hk hφ hC
  obtain ⟨C, hC⟩ := hC
  refine ⟨hφ.aut, ?_⟩
  intro r h0 h1 _ _ μ D hμ hD g
  obtain rfl : r = 1 := by omega
  exact UpperTheory.Esk.ArchimedeanConjugationLemmas.ct_zero μ D hD k c ω hω φ hφ hk C hC g
end
end
