module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.MsetSep

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.EllFacts
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem ell_toL {E : Type} [Field E] [NumberField E] {a : ℕ} (X : Matrix (Fin a) (Fin a) (Cinf E)) :
    ell E a (toL X) = (∑ w : InfinitePlace E, (X.trace w).re) / ((a : ℝ) * Fintype.card (InfinitePlace E)) := by
  simp [ell, Matrix.trace, Finset.sum_apply]

private theorem ell_br {E : Type} [Field E] [NumberField E] {a : ℕ} (X Y : Matrix (Fin a) (Fin a) (Cinf E)) :
    ell E a (toL (X * Y - Y * X)) = 0 := by
  rw [ell_toL, Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]
  simp

theorem UpperTheory.V.Lit.Bor.ellFacts :
    UpperTheory.V.Lit.Bor.EllFacts := by
  intro E _ _ _ a
  refine ⟨fun ha => ?_, ell_br, fun k X => ?_, fun A _ _ _ _ L r hL X Y => ?_⟩
  · have h1 : (a : ℝ) ≠ 0 := by exact_mod_cast (by omega : a ≠ 0)
    have h2 : (Fintype.card (InfinitePlace E) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    change ell E a (toL 1) = 1
    rw [ell_toL, div_eq_one_iff_eq (mul_ne_zero h1 h2)]
    simp [mul_comm]
  · rw [ell_toL, ell_toL, Matrix.trace_mul_cycle, k.2.1, one_mul]
  · have h := hL X Y
    simp only [shift_apply, ell_br, mul_zero, zero_smul, add_zero, ← h, mul_add, add_mul, smul_mul_assoc, mul_smul_comm,
      one_mul, mul_one, smul_add, smul_smul]
    rw [mul_comm (r * ell E a (toL Y))]
    abel
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.OneParam
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem op_cont_inf (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) :
    Continuous (infGL E a) := by
  have hs : Continuous (sInf E : Cinf E → Ad E) := (GlobalTheory.CuspRep.continuous_infEq E).prodMk continuous_const
  exact Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map hs))

open scoped Matrix.Norms.Operator in
private theorem exists_one_parameter_exp {E : Type} [Field E] [NumberField E] {a : ℕ} (Y : Matrix (Fin a) (Fin a) (Cinf E)) :
    ∃ c : ℝ → GL (Fin a) (Cinf E), c 0 = 1 ∧ (∀ s t, c (s + t) = c s * c t) ∧ Continuous c ∧
      HasDerivAt (fun t => toL (c t).val) (toL Y) 0 ∧ ∀ t : ℝ, (c t).val = NormedSpace.exp (t • Y) := by
  let c : ℝ → GL (Fin a) (Cinf E) := fun t => (Matrix.isUnit_exp (t • Y)).unit
  have hc : ∀ t, (c t).val = NormedSpace.exp (t • Y) := fun t => rfl
  have h0 : c 0 = 1 := Units.ext (by simp [c])
  have hadd : ∀ s t, c (s + t) = c s * c t := fun s t => Units.ext (by
    rw [Units.val_mul, hc, hc, hc, add_smul,
      Matrix.exp_add_of_commute _ _ (((Commute.refl Y).smul_left s).smul_right t)])
  have hv : Continuous fun t : ℝ => NormedSpace.exp (t • Y) :=
    continuous_iff_continuousAt.2 fun t => (hasDerivAt_exp_smul_const (𝕂 := ℝ) Y t).continuousAt
  have hinv : ∀ t, (c t)⁻¹ = c (-t) := fun t =>
    inv_eq_of_mul_eq_one_right (by rw [← hadd, add_neg_cancel, h0])
  refine ⟨c, h0, hadd, Units.continuous_iff.2 ⟨hv, ?_⟩, ?_, hc⟩
  · simp only [hinv, hc]
    exact hv.comp continuous_neg
  · have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) Y 0
    rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
    exact h

theorem UpperTheory.V.Lit.Bor.oneParam :
    UpperTheory.V.Lit.Bor.OneParam := by
  intro E _ _ _ a X
  obtain ⟨c, h0, hadd, hc, hd, he⟩ := exists_one_parameter_exp (E := E) (Matrix.of X)
  exact ⟨c, h0, hadd, (op_cont_inf E a).comp hc, hd, he⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.ExpOfDeriv
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem exp_of_deriv (f : ℝ → ℂ) (c : ℂ) (hf : ∀ u, HasDerivAt f (c * f u) u) (t : ℝ) :
    f t = Complex.exp (c * t) * f 0 := by
  have h1 : ∀ u : ℝ, HasDerivAt (fun v : ℝ => Complex.exp (-c * v) * f v) 0 u := fun u => by
    have h2 : HasDerivAt (fun v : ℝ => -c * (v : ℂ)) (-c) u := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := u)).const_mul (-c)
    exact (h2.cexp.fun_mul (hf u)).congr_deriv (by ring)
  have h3 := is_const_of_deriv_eq_zero (fun u => (h1 u).differentiableAt) (fun u => (h1 u).deriv) t 0
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul] at h3
  rw [← h3, ← mul_assoc, ← Complex.exp_add]
  simp

section
variable (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)

private noncomputable def sc (t : ℝ) : GL (Fin a) (Cinf E) :=
  Units.map (Matrix.scalar (Fin a)).toMonoidHom (expU fun _ : InfinitePlace E => (t : ℂ))

private theorem sc_zero : sc E a 0 = 1 := by
  have h : (expU fun _ : InfinitePlace E => ((0 : ℝ) : ℂ)) = 1 := Units.ext (funext fun _ => by simp [expU])
  rw [sc, h, map_one]

private theorem sc_deriv : HasDerivAt (fun t => toL (sc E a t).val) (oneL E a) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => Complex.exp (t : ℂ)) 1 0 := by
    simpa using (Complex.hasDerivAt_exp ((0 : ℝ) : ℂ)).comp_ofReal
  refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun w => ?_
  have e : (fun t : ℝ => toL (sc E a t).val i j w) = fun t : ℝ => Complex.exp (t : ℂ) * oneL E a i j w := by
    funext t
    by_cases h : i = j
    · subst h
      simp [sc, toL, oneL, expU, Matrix.scalar_apply]
    · simp [sc, toL, oneL, Matrix.scalar_apply, h]
  rw [e]
  exact (h1.mul_const _).congr_deriv (one_mul _)

end

theorem UpperTheory.V.Lit.Bor.aInv :
    UpperTheory.V.Lit.Bor.AInv := by
  intro E _ _ _ a φ c hφ t g
  have h := exp_of_deriv (fun u => φ.1 (g * GlobalTheory.UnitaryBC.splitCentre E a u)) c (fun u => by
    have h1 := hasDerivAt_curve φ (g * GlobalTheory.UnitaryBC.splitCentre E a u) (sc E a) (oneL E a) (sc_zero E a) (sc_deriv E a)
    have h2 : lieD (oneL E a) φ.1 (g * GlobalTheory.UnitaryBC.splitCentre E a u) = c * φ.1 (g * GlobalTheory.UnitaryBC.splitCentre E a u) :=
      congrArg (fun ψ : Sm E a => ψ.1 (g * GlobalTheory.UnitaryBC.splitCentre E a u)) hφ
    rw [h2] at h1
    have h3 := HasDerivAt.comp_sub_const u u (by rw [sub_self]; exact h1)
    refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
    have e := CuspidalL2GL.splitCentre_add (E := E) (a := a) u (x - u)
    rw [add_sub_cancel] at e
    simp only [e, mul_assoc]
    rfl) t
  rw [CuspidalL2GL.splitCentre_comm]
  simpa only [CuspidalL2GL.splitCentre_zero, mul_one] using h
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.FrameEx
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem frame_abs {V : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (B : LinearMap.BilinForm ℝ V) (hs : LinearMap.IsSymm B) (hp : ∀ x, x ≠ 0 → 0 < B x x) :
    ∃ (n : ℕ) (e : Fin n → V), ∀ x, x = ∑ j, B (e j) x • e j := by
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis hs
  refine ⟨_, fun j => (Real.sqrt (B (v j) (v j)))⁻¹ • v j, fun x => ?_⟩
  conv_lhs => rw [← v.sum_repr x]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h0 : 0 < B (v j) (v j) := hp _ (v.ne_zero j)
  have h1 : B (v j) x = v.repr x j * B (v j) (v j) := by
    conv_lhs => rw [← v.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_eq_single j]
    · simp
    · intro k _ hk
      have : B (v j) (v k) = 0 := hv (Ne.symm hk)
      simp [this]
    · simp
  have h2 : Real.sqrt (B (v j) (v j)) * Real.sqrt (B (v j) (v j)) = B (v j) (v j) := Real.mul_self_sqrt h0.le
  have h3 : Real.sqrt (B (v j) (v j)) ≠ 0 := (Real.sqrt_pos.2 h0).ne'
  rw [smul_smul, map_smul, LinearMap.smul_apply, h1, smul_eq_mul]
  congr 1
  generalize Real.sqrt (B (v j) (v j)) = s at h2 h3
  rw [← h2]
  field_simp

private noncomputable def trB (E : Type) [Field E] [NumberField E] (a : ℕ) : LinearMap.BilinForm ℝ (Herm E a) :=
  LinearMap.mk₂ ℝ (fun X Y => trF X.1 Y.1)
    (fun X Y Z => by simp [trF, add_mul, Finset.sum_add_distrib])
    (fun c X Y => by simp [trF, Finset.mul_sum])
    (fun X Y Z => by simp [trF, mul_add, Finset.sum_add_distrib])
    (fun c X Y => by simp [trF, Finset.mul_sum])

private theorem trF_self {E : Type} [Field E] [NumberField E] {a : ℕ} (X : Herm E a) :
    trF X.1 X.1 = ∑ w : InfinitePlace E, ∑ i, ∑ j, Complex.normSq (X.1 i j w) := by
  have h : star X.1 = X.1 := X.2
  have h' : ∀ i j w, X.1 j i w = starRingEnd ℂ (X.1 i j w) := fun i j w => by
    conv_lhs => rw [← h]
    rfl
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_apply, Pi.mul_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [h' i j w, Complex.mul_conj, Complex.ofReal_re]

theorem UpperTheory.V.Lit.Bor.frameEx :
    UpperTheory.V.Lit.Bor.FrameEx := by
  intro E _ _ _ a
  refine frame_abs (trB E a) ⟨fun X Y => ?_⟩ fun X hX => ?_
  · change trF X.1 Y.1 = trF Y.1 X.1
    simp only [trF, Matrix.trace_mul_comm X.1 Y.1]
  · change 0 < trF X.1 X.1
    rw [trF_self]
    have hn : ∀ w i j, 0 ≤ Complex.normSq (X.1 i j w) := fun _ _ _ => Complex.normSq_nonneg _
    refine lt_of_le_of_ne (Finset.sum_nonneg fun w _ => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hn w i j)
      fun h => hX ?_
    refine Subtype.ext (Matrix.ext fun i j => funext fun w => ?_)
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun w _ =>
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hn w i j).1 h.symm w (Finset.mem_univ _)
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => Finset.sum_nonneg fun j _ => hn w i j).1 h1 i (Finset.mem_univ _)
    have h3 := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hn w i j).1 h2 j (Finset.mem_univ _)
    exact Complex.normSq_eq_zero.1 h3
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.IpDef
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

theorem UpperTheory.V.Lit.Bor.ipDef :
    UpperTheory.V.Lit.Bor.IpDef := by
  intro E _ _ _ a n e he M _ _ _ _ H N hH q
  refine ⟨fun ω η => ?_, fun ω hω => ⟨?_, fun h0 => ?_⟩⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [ip, map_sum]
      exact Finset.sum_congr rfl fun I _ => hH.herm _ _
  · simp only [ip, Complex.re_sum]
    exact Finset.sum_nonneg fun I _ => hH.nonneg _ (hω _)
  · have hre : ∑ I : Fin q → Fin n, (H (ω fun i => e (I i)) (ω fun i => e (I i))).re = 0 := by
      rw [← Complex.re_sum]
      exact congrArg Complex.re h0
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun I _ => hH.nonneg _ (hω _))).1 hre
    have h2 : ∀ I : Fin q → Fin n, (ω fun i => e (I i)) = 0 := fun I => by
      refine hH.definite _ (hω _) (Complex.ext (h1 I (Finset.mem_univ _)) ?_)
      exact Complex.conj_eq_iff_im.1 (hH.herm _ _).symm
    refine AlternatingMap.ext fun X => ?_
    have hX : X = fun i => ∑ j, trF (e j).1 (X i).1 • e j := funext fun i => he (X i)
    have h3 : ω X = ∑ I : Fin q → Fin n, ω fun i => trF (e (I i)).1 (X i).1 • e (I i) := by
      conv_lhs => rw [hX]
      exact ω.toMultilinearMap.map_sum (fun i j => trF (e j).1 (X i).1 • e j)
    rw [h3, AlternatingMap.zero_apply]
    refine Finset.sum_eq_zero fun I _ => ?_
    rw [ω.map_smul_univ (fun i => trF (e (I i)).1 (X i).1) (fun i => e (I i)), h2, smul_zero]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.LieOneComm
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

section
variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem lie_left (X : Lie E a) (φ : Sm E a) (h g : GA E a) (hφ : ∀ g, φ.1 (h * g) = φ.1 g) :
    (lie E a X φ).1 (h * g) = (lie E a X φ).1 g := by
  have e : chart φ.1 (h * g) =ᶠ[nhds (oneL E a)] chart φ.1 g := by
    filter_upwards [isOpen_invSet.mem_nhds (val_mem_invSet (1 : GL (Fin a) (Cinf E)))] with x hx
    obtain ⟨u, hu⟩ := hx
    obtain rfl : x = toL u.val := hu.symm
    rw [chart_val, chart_val, mul_assoc, hφ]
  change fderiv ℝ (chart φ.1 (h * g)) (oneL E a) X = fderiv ℝ (chart φ.1 g) (oneL E a) X
  rw [e.fderiv_eq]

private theorem lie_fin (X : Lie E a) (k : GL (Fin a) (Af E)) (φ : Sm E a) :
    act (.fin k) (lie E a X φ) = lie E a X (act (.fin k) φ) :=
  (LinearMap.congr_fun (lie_rt_fin X k) φ).symm

private theorem lie_one_comm (X : Lie E a) (φ : Sm E a) :
    lie E a (oneL E a) (lie E a X φ) = lie E a X (lie E a (oneL E a) φ) := by
  have h := lie_comm (oneL E a) X
  have e : Matrix.of (oneL E a) * Matrix.of X = Matrix.of X * Matrix.of (oneL E a) :=
    (one_mul (Matrix.of X)).trans (mul_one (Matrix.of X)).symm
  rw [e, sub_self, sub_eq_zero] at h
  exact LinearMap.congr_fun h φ

private theorem level_lie (X : Lie E a) (φ : Sm E a) (h : IsOpen {k | act (.fin k) φ = φ}) :
    IsOpen {k | act (.fin k) (lie E a X φ) = lie E a X φ} := by
  let ρ : GL (Fin a) (Af E) →* Module.End ℂ (Sm E a) := (rt E a).comp (finGL E a)
  let S : Sm E a → Subgroup (GL (Fin a) (Af E)) := fun ψ =>
    { carrier := {k | ρ k ψ = ψ}
      one_mem' := by simp
      mul_mem' := fun {x y} hx hy => by
        change ρ (x * y) ψ = ψ
        rw [map_mul, mul_apply_eq_comp, hy, hx]
      inv_mem' := fun {x} hx => by
        change ρ x⁻¹ ψ = ψ
        have hx' : ρ x ψ = ψ := hx
        conv_lhs => rw [← hx', ← mul_apply_eq_comp, ← map_mul, inv_mul_cancel, map_one, one_apply_eq_self] }
  have hle : S φ ≤ S (lie E a X φ) := fun k hk => (lie_fin X k φ).trans (congrArg (lie E a X) hk)
  exact Subgroup.isOpen_mono hle h

private theorem isSq_lie (r : ℝ) (X : Lie E a) (φ : Sm E a) (h : IsSq r φ) : IsSq r (lie E a X φ) := by
  refine ⟨fun γ g => lie_left X φ _ g (h.left γ), level_lie X φ h.level, ?_, ?_⟩
  · rw [lie_one_comm, h.one, map_smul]
  · intro l
    have := h.sq (l ++ [X])
    rwa [List.map_append, List.prod_append, List.map_singleton, List.prod_singleton, mul_apply_eq_comp] at this

end

theorem UpperTheory.V.Lit.Bor.sqLie :
    UpperTheory.V.Lit.Bor.SqLie := by
  intro E _ _ _ a r
  refine ⟨isSq_lie r, fun X φ hφ => ?_⟩
  have h : sqSub E a r ≤ (sqSub E a r).comap (lie E a X) :=
    Submodule.span_le.2 fun ψ hψ => Submodule.subset_span (isSq_lie r X ψ hψ)
  exact h hφ
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.HarmLin
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} {Ξ : AlgRep E a}

private theorem rel_mono {P Q : Sm E a → Prop} (h : ∀ φ, P φ → Q φ) {q : ℕ}
    {ω : GlobalTheory.GKCoh.Herm E a [⋀^Fin q]→ₗ[ℝ] (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ))} (hω : IsRelCochain Ξ P ω) :
    IsRelCochain Ξ Q ω :=
  ⟨hω.equiv, hω.basic, fun X => Submodule.span_mono (by
    rintro _ ⟨φ, v, hφ, rfl⟩
    exact ⟨φ, v, h φ hφ, rfl⟩) (hω.val X)⟩

private theorem level_mono {U U' : Subgroup (GL (Fin a) (Af E))} (h : U' ≤ U) (φ : Sm E a) (hφ : IsLevelFn U Ξ φ) :
    IsLevelFn U' Ξ φ := ⟨hφ.1, fun u hu => hφ.2.1 u (h hu), hφ.2.2⟩

variable {U : Subgroup (GL (Fin a) (Af E))} {r : ℝ} {n : ℕ} {e : Fin n → GlobalTheory.GKCoh.Herm E a}

private theorem harm_zero {q : ℕ} :
    IsHarm U Ξ r e (0 : GlobalTheory.GKCoh.Herm E a [⋀^Fin q]→ₗ[ℝ] (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ))) := by
  refine ⟨⟨fun k X => by simp, fun X i _ => rfl, fun X => Submodule.zero_mem _⟩, ?_, ?_⟩
  · exact AlternatingMap.ext fun X => by simp [dCo_apply]
  · cases q with
    | zero => trivial
    | succ q => exact AlternatingMap.ext fun X => by simp [del_apply]

private theorem harm_comb {q : ℕ} (c : ℂ)
    {ω η : GlobalTheory.GKCoh.Herm E a [⋀^Fin q]→ₗ[ℝ] (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ))} (hω : IsHarm U Ξ r e ω)
    (hη : IsHarm U Ξ r e η) : IsHarm U Ξ r e (c • ω + η) := by
  have ap : ∀ X, (c • ω + η) X = c • ω X + η X := fun X => rfl
  refine ⟨⟨fun k X => ?_, fun X i hi => ?_, fun X => ?_⟩, ?_, ?_⟩
  · rw [ap, ap, hω.rel.equiv k X, hη.rel.equiv k X, map_add (f := _), map_smul]
  · rw [ap, hω.rel.basic X i hi, hη.rel.basic X i hi, smul_zero, add_zero]
  · rw [ap]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (hω.rel.val X)) (hη.rel.val X)
  · refine AlternatingMap.ext fun X => ?_
    have h1 := DFunLike.congr_fun hω.closed X
    have h2 := DFunLike.congr_fun hη.closed X
    rw [dCo_apply, AlternatingMap.zero_apply] at h1 h2 ⊢
    simp only [ap, map_add (f := _), map_smul, smul_add, Finset.sum_add_distrib, h2, add_zero]
    rw [← smul_zero c, ← h1, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
  · cases q with
    | zero => trivial
    | succ q =>
      refine AlternatingMap.ext fun X => ?_
      have h1 := DFunLike.congr_fun (show del _ e ω = 0 from hω.coclosed) X
      have h2 := DFunLike.congr_fun (show del _ e η = 0 from hη.coclosed) X
      rw [del_apply, AlternatingMap.zero_apply] at h1 h2 ⊢
      simp only [ap, map_add (f := _), map_smul, Finset.sum_add_distrib, h2, add_zero, ← Finset.smul_sum, h1, smul_zero]

end SlopeTestRemainingChoices

theorem UpperTheory.V.Lit.Bor.harmLin :
    UpperTheory.V.Lit.Bor.HarmLin := by
  intro E _ _ _ a n e U Ξ r q
  refine ⟨fun s ω c h => ?_, fun ω => ⟨fun h => rel_mono (fun _ hφ => hφ.1) h.rel, fun U' hU =>
    ⟨fun h => ⟨rel_mono (fun φ hφ => ⟨level_mono hU φ hφ.1, hφ.2⟩) h.rel, h.closed, h.coclosed⟩,
      rel_mono (level_mono hU)⟩⟩⟩
  induction (Finset.univ : Finset (Fin s)) using Finset.cons_induction with
  | empty => exact harm_zero
  | cons j t hj ih =>
    rw [Finset.sum_cons]
    exact harm_comb _ (h j) ih
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.TformPos
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem tform_star_mul_self_eq_sum_cmp {W : Type} [AddCommGroup W] [Module ℂ W] {d : ℕ}
    (H : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) (B : Matrix (Fin d) (Fin d) ℂ) (x : W ⊗[ℂ] (Fin d → ℂ)) :
    tform H (star B * B) x x = ∑ k, H (∑ i, B k i • Bor.cmp i x) (∑ j, B k j • Bor.cmp j x) := by
  rw [tform_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, map_smul, smul_eq_mul,
    Matrix.mul_apply, Matrix.star_apply, starRingEnd_apply, Finset.sum_mul, Finset.mul_sum,
    RingHom.id_apply]
  conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => ?_
  ring

open scoped ComplexOrder MatrixOrder in
theorem UpperTheory.V.Lit.Bor.tformPos :
    UpperTheory.V.Lit.Bor.TformPos := by
  intro W _ _ d H N G hH hG
  classical
  have h0 : 0 ≤ G := Matrix.nonneg_iff_posSemidef.mpr hG.posSemidef
  obtain ⟨B, hBs, -, hBB⟩ := sub_zero G ▸
    CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts h0.isSelfAdjoint
      (QuasispectrumRestricts.nnreal_of_nonneg h0)
  have hB : G = star B * B := by rw [hBs.star_eq, hBB, sub_zero]
  have hself : ∀ y : W, H y y = ((H y y).re : ℂ) := by
    intro y
    have hc := hH.herm y y
    apply Complex.ext
    · simp
    · have := congrArg Complex.im hc
      simp at this
      simp
      linarith
  have hz : ∀ x ∈ tens d N, ∀ k : Fin d, (∑ i, B k i • Bor.cmp i x) ∈ N := by
    intro x hx k
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (mem_tens.mp hx i)
  refine ⟨?_, ?_, ?_⟩
  · intro x y
    set_option synthInstance.maxHeartbeats 100000 in
      rw [tform_apply, tform_apply, map_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hH.herm, ← hG.isHermitian.apply j i]
    simp [mul_comm]
  · intro x hx
    rw [hB, tform_star_mul_self_eq_sum_cmp, Complex.re_sum]
    exact Finset.sum_nonneg fun k _ => hH.nonneg _ (hz x hx k)
  · intro x hx h
    rw [hB, tform_star_mul_self_eq_sum_cmp] at h
    have hre : ∑ k, (H (∑ i, B k i • Bor.cmp i x) (∑ j, B k j • Bor.cmp j x)).re = 0 := by
      rw [← Complex.re_sum, h, Complex.zero_re]
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hH.nonneg _ (hz x hx k))] at hre
    have hzero : ∀ k, (∑ i, B k i • Bor.cmp i x) = 0 := by
      intro k
      apply hH.definite _ (hz x hx k)
      rw [hself, hre k (Finset.mem_univ _), Complex.ofReal_zero]
    have hdet : IsUnit B.det := by
      have := (Matrix.isUnit_iff_isUnit_det G).mp hG.isUnit
      rw [hB, Matrix.det_mul] at this
      exact isUnit_of_mul_isUnit_right this
    have hinv : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hdet
    have hcomp : ∀ l, Bor.cmp l x = 0 := by
      intro l
      have e : Bor.cmp l x = ∑ k, B⁻¹ l k • ∑ i, B k i • Bor.cmp i x := by
        simp only [Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        simp only [← Finset.sum_smul]
        have : ∀ i, ∑ k, B⁻¹ l k * B k i = (1 : Matrix (Fin d) (Fin d) ℂ) l i := by
          intro i
          rw [← hinv, Matrix.mul_apply]
        simp only [this, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
          Finset.mem_univ, if_true]
      rw [e]
      simp [hzero]
    rw [← sum_cmp x]
    simp [hcomp]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.KugaZero
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

theorem UpperTheory.V.Lit.Bor.kugaZero :
    UpperTheory.V.Lit.Bor.KugaZero := by
  intro E _ _ _ a n e M _ _ _ _ A B hc ω hω X
  rw [del_apply]
  simp only [cas, LinearMap.sub_apply, LinearMap.sum_apply, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hs : star (Complex.I • (e j).1) = -(Complex.I • (e j).1) := by
    have h : star (e j).1 = (e j).1 := (e j).2
    rw [star_smul, h, Complex.star_def, Complex.conj_I, neg_smul]
  have h0 := hω _ hs X
  rw [Fin.sum_univ_zero, LinearMap.add_apply, LinearMap.add_apply] at h0
  have h1 : ∀ (Y Z) (m : M), A Y (B Z m) = B Z (A Y m) := fun Y Z m => LinearMap.congr_fun (hc Y Z).eq m
  have h2 := congrArg (B (toL (Complex.I • (e j).1))) h0
  have h3 := congrArg (A (toL (Complex.I • (e j).1))) h0
  rw [map_add (f := _), map_zero] at h2 h3
  rw [h1] at h3
  have h4 : B (toL (Complex.I • (e j).1)) (B (toL (Complex.I • (e j).1)) (ω X)) =
      A (toL (Complex.I • (e j).1)) (A (toL (Complex.I • (e j).1)) (ω X)) := by
    rw [← sub_eq_zero, ← sub_self (0 : M)]
    nth_rewrite 1 [← h2]
    rw [← h3]
    abel
  rw [dCo_apply, Fin.sum_univ_one, Subsingleton.elim (Fin.removeNth _ _) X]
  simp only [Fin.val_zero, pow_zero, one_smul, Matrix.cons_val_zero, LinearMap.add_apply, map_add (f := _), Module.End.mul_apply, h1, h4]
  abel
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.IpAdj
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

theorem UpperTheory.V.Lit.Bor.ipAdj :
    UpperTheory.V.Lit.Bor.IpAdj := by
  intro E _ _ _ a n e M _ _ _ _ L L' H N hadj q ω η hω hη
  have key : ∀ i : Fin (q + 1), ∑ I : Fin (q + 1) → Fin n,
      H (ω fun k => e (I k)) ((-1 : ℤ) ^ (i : ℕ) • L (toL (e (I i)).1) (η (i.removeNth fun k => e (I k)))) =
      ip e H (del L' e ω) η := fun i => by
    rw [← (Fin.insertNthEquiv (fun _ => Fin n) i).sum_comp, Fintype.sum_prod_type, Finset.sum_comm, ip]
    refine Finset.sum_congr rfl fun J _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [del_apply, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h1 : (fun k => e ((Fin.insertNthEquiv (fun _ => Fin n) i (j, J)) k)) =
        i.insertNth (α := fun _ => Herm E a) (e j) (fun k => e (J k)) := by
      funext k
      refine Fin.succAboveCases i ?_ (fun k => ?_) k <;> simp [Fin.insertNthEquiv]
    have h2 : (Fin.insertNthEquiv (fun _ => Fin n) i (j, J)) i = j := by simp [Fin.insertNthEquiv]
    rw [h1, h2, Fin.removeNth_insertNth, AlternatingMap.map_insertNth, ← hadj _ _ (hω _) _ (hη _),
      map_zsmul, map_zsmul, LinearMap.smul_apply, smul_smul, ← mul_pow]
    simp
  have h0 : ip e H ω (dCo L η) = ∑ i : Fin (q + 1), ∑ I : Fin (q + 1) → Fin n,
      H (ω fun k => e (I k)) ((-1 : ℤ) ^ (i : ℕ) • L (toL (e (I i)).1) (η (i.removeNth fun k => e (I k)))) := by
    rw [Finset.sum_comm, ip]
    refine Finset.sum_congr rfl fun I _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [dCo_apply, map_sum]
  rw [h0, Finset.sum_congr rfl fun i _ => key i]
  simp
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.FrameAd
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

theorem UpperTheory.V.Lit.Bor.frameAd :
    UpperTheory.V.Lit.Bor.FrameAd := by
  intro E _ _ _ a n e he N _ _ β k
  have hk1 : k.1 * star k.1 = 1 := k.2.2
  have hc : ∀ i j, trF (e i).1 (adHerm k (e j)).1 = trF (e j).1 (star k.1 * (e i).1 * k.1) := fun i j => by
    have h : ((e i).1 * (k.1 * (e j).1 * star k.1)).trace = ((e j).1 * (star k.1 * (e i).1 * k.1)).trace := by
      rw [show (e i).1 * (k.1 * (e j).1 * star k.1) = ((e i).1 * k.1) * ((e j).1 * star k.1) by simp only [mul_assoc],
        Matrix.trace_mul_comm]
      simp only [mul_assoc]
    simp only [trF, adHerm, h]
  have hs : ∀ i, ∑ j, trF (e i).1 (adHerm k (e j)).1 • adHerm k (e j) = e i := fun i => by
    have h := congrArg Subtype.val (he ⟨star k.1 * (e i).1 * k.1, IsSelfAdjoint.conjugate' (e i).2 k.1⟩)
    simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at h
    refine Subtype.ext ?_
    simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul, hc]
    calc ∑ j, trF (e j).1 (star k.1 * (e i).1 * k.1) • (adHerm k (e j)).1
        = k.1 * (∑ j, trF (e j).1 (star k.1 * (e i).1 * k.1) • (e j).1) * star k.1 := by
          simp only [adHerm, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]
      _ = k.1 * (star k.1 * (e i).1 * k.1) * star k.1 := by rw [← h]
      _ = (k.1 * star k.1) * (e i).1 * (k.1 * star k.1) := by simp only [mul_assoc]
      _ = (e i).1 := by rw [hk1, one_mul, mul_one]
  calc ∑ j, β (adHerm k (e j)) (adHerm k (e j))
      = ∑ j, β (∑ i, trF (e i).1 (adHerm k (e j)).1 • e i) (adHerm k (e j)) :=
        Finset.sum_congr rfl fun j _ => by rw [← he (adHerm k (e j))]
    _ = ∑ j, ∑ i, trF (e i).1 (adHerm k (e j)).1 • β (e i) (adHerm k (e j)) := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
    _ = ∑ i, β (e i) (∑ j, trF (e i).1 (adHerm k (e j)).1 • adHerm k (e j)) := by
        rw [Finset.sum_comm]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, map_smul]
    _ = ∑ j, β (e j) (e j) := by simp only [hs]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.TformAdj
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem cmp_lTensor_toLin {W : Type} [AddCommGroup W] [Module ℂ W] {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℂ)
    (y : W ⊗[ℂ] (Fin d → ℂ)) (j : Fin d) :
    cmp j ((Matrix.toLin' Q).lTensor W y) = ∑ k, Q j k • cmp k y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul φ v =>
    simp only [LinearMap.lTensor_tmul, cmp_tmul, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
      Finset.sum_smul, smul_smul]
  | add a b ha hb =>
    simp only [map_add (f := _), ha, hb, smul_add, Finset.sum_add_distrib]

private theorem cmp_rTensor_end {W : Type} [AddCommGroup W] [Module ℂ W] {d : ℕ} (S : Module.End ℂ W)
    (y : W ⊗[ℂ] (Fin d → ℂ)) (j : Fin d) :
    cmp j (S.rTensor (Fin d → ℂ) y) = S (cmp j y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul φ v => simp only [LinearMap.rTensor_tmul, cmp_tmul, map_smul]

theorem UpperTheory.V.Lit.Bor.tformAdj :
    UpperTheory.V.Lit.Bor.TformAdj := by
  intro W _ _ d H N G P Q S T
  refine ⟨fun hPQ x y => ?_, fun hST x hx y hy => ?_⟩
  · have key : ∀ a b, (G * Q) a b = (Pᴴ * G) a b := fun a b => by rw [hPQ]
    have hL : tform H G x ((Matrix.toLin' Q).lTensor W y)
        = ∑ a, ∑ b, (G * Q) a b * H (cmp a x) (cmp b y) := by
      rw [tform_apply]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [cmp_lTensor_toLin, map_sum, map_smul, smul_eq_mul, Matrix.mul_apply,
        Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
    have hR : tform H G ((Matrix.toLin' P).lTensor W x) y
        = ∑ a, ∑ b, (Pᴴ * G) a b * H (cmp a x) (cmp b y) := by
      rw [tform_apply]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [cmp_lTensor_toLin, map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply,
        LinearMap.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.conjTranspose_apply,
        starRingEnd_apply, Finset.mul_sum, Finset.sum_mul]
      conv_lhs => rw [Finset.sum_comm]
      conv_lhs => enter [2, j]; rw [Finset.sum_comm]
      conv_lhs => rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr rfl fun i _ => by ring
    rw [hL, hR]
    simp only [key]
  · rw [mem_tens] at hx hy
    rw [tform_apply, tform_apply]
    simp only [cmp_rTensor_end, hST _ (hx _) _ (hy _)]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.FrameBr
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem tr_one {R : Type} [CommRing R] {a : ℕ} (A B Z : Matrix (Fin a) (Fin a) R) :
    (A * (Z * B - B * Z)).trace = -(B * (Z * A - A * Z)).trace := by
  have h1 : (A * (Z * B)).trace = (B * (A * Z)).trace := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
  have h2 : (B * (Z * A)).trace = (A * (B * Z)).trace := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_sub, Matrix.trace_sub, h1, h2]
  ring

private theorem trF_one {E : Type} [Field E] [NumberField E] {a : ℕ} (A B Z : Matrix (Fin a) (Fin a) (Cinf E)) :
    trF A (Z * B - B * Z) = -trF B (Z * A - A * Z) := by
  unfold trF
  rw [tr_one, ← Finset.sum_neg_distrib]
  rfl

private theorem trF_neg {E : Type} [Field E] [NumberField E] {a : ℕ} (A B : Matrix (Fin a) (Fin a) (Cinf E)) :
    trF A (-B) = -trF A B := by
  unfold trF
  rw [Matrix.mul_neg, Matrix.trace_neg, ← Finset.sum_neg_distrib]
  rfl

theorem UpperTheory.V.Lit.Bor.frameBr :
    UpperTheory.V.Lit.Bor.FrameBr := by
  intro E _ _ _ a n e he N _ _
  refine ⟨fun β Z hZ => ?_, fun β X h => ?_⟩
  · have h1 : ∀ j, β (brH Z hZ (e j)) (e j) = ∑ k, trF (e k).1 (Z * (e j).1 - (e j).1 * Z) • β (e k) (e j) := by
      intro j
      conv_lhs => rw [he (brH Z hZ (e j))]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
      rfl
    have h2 : ∀ j, β (e j) (brH Z hZ (e j)) = ∑ k, trF (e k).1 (Z * (e j).1 - (e j).1 * Z) • β (e j) (e k) := by
      intro j
      conv_lhs => rw [he (brH Z hZ (e j))]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul]
      rfl
    simp only [h1, h2]
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [trF_one, neg_smul, neg_add_cancel]
  · have hb : ∀ j, (brH _ (h j) X).1 = -((Complex.I • X.1) * (e j).1 - (e j).1 * (Complex.I • X.1)) := by
      intro j
      change (Complex.I • (e j).1) * X.1 - X.1 * (Complex.I • (e j).1) = _
      simp only [Matrix.smul_mul, Matrix.mul_smul, neg_sub]
    have h1 : ∀ j, X.1 * (e j).1 - (e j).1 * X.1 =
        ∑ k, trF (e k).1 (brH _ (h j) X).1 • (Complex.I • (e k).1) := by
      intro j
      have h0 : (brH _ (h j) X).1 = ∑ k, trF (e k).1 (brH _ (h j) X).1 • (e k).1 := by
        conv_lhs => rw [he (brH _ (h j) X)]
        simp only [Submodule.coe_sum, Submodule.coe_smul]
      have h3 : X.1 * (e j).1 - (e j).1 * X.1 = Complex.I • (brH _ (h j) X).1 := by
        rw [hb]
        simp only [Matrix.smul_mul, Matrix.mul_smul, ← smul_sub, smul_neg, smul_smul, Complex.I_mul_I, neg_smul,
          one_smul, neg_neg]
      rw [h3]
      conv_lhs => rw [h0]
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun k _ => smul_comm _ _ _
    have h2 : ∀ j, β (Complex.I • (e j).1) (brH _ (h j) X) =
        ∑ k, trF (e k).1 (brH _ (h j) X).1 • β (Complex.I • (e j).1) (e k) := by
      intro j
      conv_lhs => rw [he (brH _ (h j) X)]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul]
    simp only [h1, h2]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.map_smul β, LinearMap.sum_apply, LinearMap.smul_apply]
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hb, hb, trF_neg, trF_neg, trF_one, neg_smul]
end
