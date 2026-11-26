module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.CentEq
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private def sc {R : Type} [CommRing R] (n : ℕ) : GL (Fin 1) R →* GL (Fin n) R :=
  (GeneralLinearGroup.scalar (Fin n)).comp GeneralLinearGroup.det

private theorem sc_val {R : Type} [CommRing R] (n : ℕ) (x : GL (Fin 1) R) (i j : Fin n) :
    (sc n x).val i j = if i = j then x.val 0 0 else 0 := by
  change Matrix.scalar (Fin n) (Matrix.det x.val) i j = _
  rw [Matrix.det_fin_one]
  by_cases e : i = j <;> simp [e]

private theorem sc_scalar {R : Type} [CommRing R] (n : ℕ) (z : Rˣ) :
    sc n (GeneralLinearGroup.scalar (Fin 1) z) = GeneralLinearGroup.scalar (Fin n) z := by
  ext i j
  rw [sc_val]
  change (if i = j then Matrix.scalar (Fin 1) z.val 0 0 else 0) = Matrix.scalar (Fin n) z.val i j
  by_cases e : i = j <;> simp [e]

private theorem sc_comm {R : Type} [CommRing R] (n : ℕ) (x : GL (Fin 1) R) (g : GL (Fin n) R) :
    sc n x * g = g * sc n x :=
  Units.ext (Matrix.scalar_commute (Matrix.det x.val) (fun _ => Commute.all _ _) g.val).eq

private theorem map_sc {R S : Type} [CommRing R] [CommRing S] (n : ℕ) (p : R →+* S) (x : GL (Fin 1) R) :
    GeneralLinearGroup.map p (sc n x) = sc n (GeneralLinearGroup.map p x) := by
  ext i j
  change p ((sc n x).val i j) = _
  rw [sc_val, sc_val]
  split_ifs
  · rfl
  · exact map_zero p

private theorem corner_sc {R S : Type} [CommRing R] [CommRing S] (n : ℕ) (s : R →ₙ+* S) (x : GL (Fin 1) R) :
    GlobalTheory.CuspRep.cornerGL n s (sc n x) = sc n (GlobalTheory.CuspRep.cornerGL 1 s x) := by
  ext i j
  rw [sc_val]
  change (1 : Matrix (Fin n) (Fin n) S) i j - s ((1 : Matrix (Fin n) (Fin n) R) i j) + s ((sc n x).val i j) =
    if i = j then (1 : Matrix (Fin 1) (Fin 1) S) 0 0 - s ((1 : Matrix (Fin 1) (Fin 1) R) 0 0) + s (x.val 0 0) else 0
  rw [sc_val]
  by_cases e : i = j <;> simp [Matrix.one_apply, e]

private theorem continuous_sc {R : Type} [CommRing R] [TopologicalSpace R] (n : ℕ) :
    Continuous (sc n : GL (Fin 1) R → GL (Fin n) R) := by
  have h : Continuous fun x : GL (Fin 1) R => (sc n x).val := by
    refine continuous_matrix fun i j => ?_
    simp only [sc_val]
    split_ifs
    · exact Units.continuous_val.matrix_elem 0 0
    · exact continuous_const
  refine Units.continuous_iff.2 ⟨h, ?_⟩
  simp only [← map_inv]
  refine continuous_matrix fun i j => ?_
  simp only [sc_val]
  split_ifs
  · exact Units.continuous_coe_inv.matrix_elem 0 0
  · exact continuous_const

private theorem sc_mem {K : Type} [Field K] (n : ℕ) (O : Subring K) (x : GL (Fin 1) K)
    (h : x ∈ Formalism.UG.GLint (Fin 1) O) : sc n x ∈ Formalism.UG.GLint (Fin n) O := by
  rw [GlobalTheory.AdelicU.mem_GLint_iff] at h ⊢
  rw [← map_inv]
  constructor <;> intro i j <;> rw [sc_val] <;> split_ifs
  · exact h.1 0 0
  · exact zero_mem _
  · exact h.2 0 0
  · exact zero_mem _

theorem UpperTheory.V.Af.Smo.centEq :
    UpperTheory.V.Af.Smo.CentLoc → UpperTheory.V.Af.Smo.AwayInd → UpperTheory.V.Af.Smo.DenseAway → UpperTheory.V.Af.Smo.CentEq := by
  intro hL hA hD E _ _ n S B f f' hc hc' hl hl' hE hK hK' z g g'
  have h1 : ∀ k : GL (Fin 1) (Af E), Away S k → ∀ g g' : GA E n,
      f (g * finGL E n (sc n k)) * f' g' = f g * f' (g' * finGL E n (sc n k)) := by
    refine hA E 1 S _ (fun k hk g g' => ?_) (fun w hw k _ _ hP y g g' => ?_)
    · have hk' : InKS S (sc n k) := by
        refine ⟨fun w hw => ?_, fun w => ?_⟩
        · rw [map_sc, hk.1 w hw, map_one]
        · rw [map_sc]; exact sc_mem n _ _ (hk.2 w)
      rw [hK g _ hk', hK' g' _ hk']
    · obtain ⟨c, hcc⟩ := hL E n w (B w) (GeneralLinearGroup.det y)
      have e : sc n (locGL E 1 w y) = locGL E n w (1 * GeneralLinearGroup.scalar (Fin n) (GeneralLinearGroup.det y)) := by
        rw [one_mul]; exact (corner_sc n (sLoc E w) y).symm
      have a := hcc _ ((hE w hw).1 (g * finGL E n (sc n k))) 1
      have b := hcc _ ((hE w hw).2 (g' * finGL E n (sc n k))) 1
      simp only [map_one, mul_one] at a b
      rw [map_mul, map_mul, ← mul_assoc, ← mul_assoc, e, a, b, mul_assoc, hP]
      ring
  have h2 : ∀ x : GA E 1, f (g * sc n x) * f' g' = f g * f' (g' * sc n x) := by
    refine isClosed_property (hD E 1 S).denseRange_val (isClosed_eq ?_ ?_) ?_
    · exact (hc.comp (continuous_const.mul (continuous_sc n))).mul continuous_const
    · exact continuous_const.mul (hc'.comp (continuous_const.mul (continuous_sc n)))
    · rintro ⟨_, γ, k, hk, rfl⟩
      have e : ∀ u : GA E n, u * sc n (ratGL E 1 γ * finGL E 1 k) = ratGL E n (sc n γ) * (u * finGL E n (sc n k)) := by
        intro u
        rw [map_mul, ← mul_assoc, ← sc_comm n (ratGL E 1 γ) u, mul_assoc]
        congr 1
        · exact (map_sc n _ γ).symm
        · exact congrArg _ (corner_sc n (sFin E) k).symm
      change f (g * sc n (ratGL E 1 γ * finGL E 1 k)) * _ = _ * f' (g' * sc n (ratGL E 1 γ * finGL E 1 k))
      rw [e, e]
      have a : ∀ u, f (ratGL E n (sc n γ) * u) = f u := hl _
      have b : ∀ u, f' (ratGL E n (sc n γ) * u) = f' u := hl' _
      rw [a, b]
      exact h1 k hk g g'
  rw [← sc_scalar]
  exact h2 _
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.WlNiceZero
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

private theorem wl_nice_zero : Nice (0 : GA E n → ℂ) := by
  exact ⟨continuous_zero, ⟨0, fun _ => by simp⟩, fun _ _ => rfl,
    fun _ _ _ g => constantTerm_zero g, ⟨⊤, fun _ _ _ => rfl⟩⟩

private theorem wl_nice_add {f f' : GA E n → ℂ} (h : Nice f) (h' : Nice f') : Nice (f + f') := by
  refine ⟨h.cont.add h'.cont, ?_, IsLeftInvariant.add h.left h'.left, ?_, ?_⟩
  · obtain ⟨C, hC⟩ := h.bdd
    obtain ⟨C', hC'⟩ := h'.bdd
    exact ⟨C + C', fun g => (norm_add_le _ _).trans (add_le_add (hC g) (hC' g))⟩
  · intro r a b g
    have e := constantTerm_add (r := r) h.cont h'.cont g
    rw [h.cusp r a b g, h'.cusp r a b g, add_zero] at e
    exact e
  · obtain ⟨V, hV⟩ := h.level
    obtain ⟨V', hV'⟩ := h'.level
    refine ⟨V ⊓ V', fun g v hv => ?_⟩
    rw [OpenSubgroup.mem_inf] at hv
    rw [Pi.add_apply, Pi.add_apply, hV g v hv.1, hV' g v hv.2]

private theorem wl_nice_smul {f : GA E n → ℂ} (h : Nice f) (z : ℂ) : Nice (z • f) := by
  refine ⟨h.cont.const_smul z, ?_, IsLeftInvariant.smul z h.left, ?_, ?_⟩
  · obtain ⟨C, hC⟩ := h.bdd
    refine ⟨‖z‖ * C, fun g => ?_⟩
    rw [Pi.smul_apply, norm_smul]
    exact mul_le_mul_of_nonneg_left (hC g) (norm_nonneg _)
  · intro r a b g
    have e := constantTerm_smul (r := r) z f g
    rw [h.cusp r a b g, smul_zero] at e
    exact e
  · obtain ⟨V, hV⟩ := h.level
    exact ⟨V, fun g v hv => by rw [Pi.smul_apply, Pi.smul_apply, hV g v hv]⟩

private theorem wl_nice_tr {f : GA E n → ℂ} (h : Nice f) (x : GL (Fin n) (Af E)) :
    Nice (fun g => f (g * finGL E n x)) := by
  refine ⟨h.cont.comp (continuous_id.mul continuous_const),
    h.bdd.imp (fun _ hC _ => hC _), ?_, ?_, ?_⟩
  · intro γ g
    have e := h.left γ (g * finGL E n x)
    rw [← mul_assoc] at e
    exact e
  · intro r a b g
    exact (constantTerm_rightTranslate (r := r) f (finGL E n x) g).trans (h.cusp r a b _)
  · obtain ⟨V, hV⟩ := h.level
    refine ⟨V.comap (MulAut.conj x⁻¹).toMonoidHom ?_, fun g v hv => ?_⟩
    · show Continuous fun v => x⁻¹ * v * x⁻¹⁻¹
      exact (continuous_const.mul continuous_id).mul continuous_const
    · have hv' : x⁻¹ * v * x⁻¹⁻¹ ∈ V := hv
      have e := hV (g * finGL E n x) _ hv'
      rw [inv_inv, mul_assoc g, ← map_mul, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul, map_mul,
        ← mul_assoc] at e
      exact e

private theorem wl_add {f f' : GA E n → ℂ} (h : Continuous f) (h' : Continuous f') :
    whittaker (f + f') = whittaker f + whittaker f' := by
  funext g
  obtain ⟨C, hC, hD⟩ := FourierWhittaker.exists_isCompact_superset_vecDomain (K := E)
    (ι := FourierWhittaker.Pos n)
  have i : ∀ {φ : GA E n → ℂ}, Continuous φ → IntegrableOn (FourierWhittaker.wInt 0 φ g)
      (FourierWhittaker.vecDomain E (FourierWhittaker.Pos n))
      (FourierWhittaker.vecMeasure E (FourierWhittaker.Pos n)) := fun hφ =>
    ((FourierWhittaker.continuous_wInt 0 hφ g).continuousOn.integrableOn_compact hC).mono_set hD
  have e := integral_add (i h) (i h')
  simp only [FourierWhittaker.wInt] at e
  simp only [whittaker, Pi.add_apply, add_mul]
  exact e

private theorem wl_smul (f : GA E n → ℂ) (z : ℂ) : whittaker (z • f) = z • whittaker f := by
  funext g
  simp only [whittaker, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul _ _

private theorem wl_tr (f : GA E n → ℂ) (y : GA E n) :
    whittaker (fun g => f (g * y)) = fun g => whittaker f (g * y) := by
  funext g
  simp only [whittaker, mul_assoc]

private theorem wl_sum {f : GA E n → ℂ} (h : Nice f) (c : GL (Fin n) (Af E) → ℂ) (s : Finset (GL (Fin n) (Af E))) :
    Nice (∑ x ∈ s, c x • fun g => f (g * finGL E n x)) ∧
      whittaker (∑ x ∈ s, c x • fun g => f (g * finGL E n x)) =
        ∑ x ∈ s, c x • fun g => whittaker f (g * finGL E n x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    refine ⟨wl_nice_zero, ?_⟩
    funext g
    simp [whittaker]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have k := wl_nice_smul (wl_nice_tr h a) (c a)
    exact ⟨wl_nice_add k ih.1, by rw [wl_add k.cont ih.1.cont, ih.2, wl_smul, wl_tr]⟩

private theorem wl_fop (c : GL (Fin n) (Af E) →₀ ℂ) (f : GA E n → ℂ) :
    fop c f = ∑ x ∈ c.support, c x • fun g => f (g * finGL E n x) := by
  funext g
  simp [fop, Finsupp.sum, Finset.sum_apply]

end SlopeTestRemainingChoices

theorem UpperTheory.V.Af.Smo.whLin :
    UpperTheory.V.Af.Smo.WhLin := by
  intro E _ _ n f hf
  refine ⟨fun c => ?_, fun f' hf' => ?_⟩
  · rw [wl_fop, wl_fop]
    exact wl_sum hf c c.support
  · have e : f - f' = f + (-1 : ℂ) • f' := by rw [neg_one_smul, sub_eq_add_neg]
    have k := wl_nice_smul hf' (-1)
    rw [e]
    exact ⟨wl_nice_add hf k, by rw [wl_add hf.cont k.cont, wl_smul, neg_one_smul, sub_eq_add_neg]⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.SchTensor
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

theorem UpperTheory.V.Af.Smo.schTensor :
    UpperTheory.V.Af.Smo.SchOfClosed → UpperTheory.V.Af.Smo.SchTensor := by
  intro hS V M _ _ _ _ _ _ h hh hhc α
  classical
  let S : Set (V × M → ℂ) := {F | ∃ (f : V → ℂ) (β : 𝓢(M, ℂ)), ContDiff ℝ ∞ f ∧
    HasCompactSupport f ∧ F = fun p => f p.1 * β p.2}
  let A : Set (V × M → ℂ) := (Submodule.span ℂ S : Set (V × M → ℂ))
  have hgen : ∀ F ∈ S, (∃ C, ∀ x, ‖F x‖ ≤ C) ∧ Differentiable ℝ F ∧
      (∀ v : V × M, (fun x => fderiv ℝ F x v) ∈ A) ∧
      ∀ l : V × M →L[ℝ] ℝ, (fun x => (l x : ℂ) * F x) ∈ A := by
    rintro F ⟨f, β, hf, hfc, rfl⟩
    have hfd : Differentiable ℝ f := hf.differentiable (by simp)
    refine ⟨?_, ?_, ?_, ?_⟩
    · obtain ⟨Cf, hCf⟩ := hfc.exists_bound_of_continuous hf.continuous
      obtain ⟨Cb, hCb⟩ : ∃ C, ∀ y, ‖β y‖ ≤ C :=
        ⟨‖β.toBoundedContinuousFunction‖, fun y => by
          simpa using β.toBoundedContinuousFunction.norm_coe_le_norm y⟩
      refine ⟨Cf * Cb, fun p => ?_⟩
      rw [norm_mul]
      exact mul_le_mul (hCf _) (hCb _) (norm_nonneg _) (le_trans (norm_nonneg _) (hCf p.1))
    · exact (hfd.comp differentiable_fst).mul (β.differentiable.comp differentiable_snd)
    · intro v
      have hder : ∀ p : V × M, fderiv ℝ (fun p : V × M => f p.1 * β p.2) p v =
          fderiv ℝ f p.1 v.1 * β p.2 + f p.1 * (LineDeriv.lineDerivOp v.2 β : 𝓢(M, ℂ)) p.2 := by
        intro p
        have h1 : HasFDerivAt (fun p : V × M => f p.1)
            ((fderiv ℝ f p.1).comp (ContinuousLinearMap.fst ℝ V M)) p :=
          (hfd p.1).hasFDerivAt.comp p hasFDerivAt_fst
        have h2 : HasFDerivAt (fun p : V × M => β p.2)
            ((fderiv ℝ β p.2).comp (ContinuousLinearMap.snd ℝ V M)) p :=
          (β.differentiableAt).hasFDerivAt.comp p hasFDerivAt_snd
        rw [show (fun p : V × M => f p.1 * β p.2) = (fun p => f p.1) * (fun p => β p.2) from rfl,
          (h1.mul h2).fderiv, SchwartzMap.lineDerivOp_apply_eq_fderiv]
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
          smul_eq_mul]
        ring
      have hfe : (fun x => fderiv ℝ (fun p : V × M => f p.1 * β p.2) x v) =
          (fun p : V × M => (fun ξ => fderiv ℝ f ξ v.1) p.1 * β p.2) +
          (fun p : V × M => f p.1 * (LineDeriv.lineDerivOp v.2 β : 𝓢(M, ℂ)) p.2) := by
        ext p
        rw [hder]
        rfl
      rw [hfe]
      refine (Submodule.span ℂ S).add_mem
        (Submodule.subset_span ⟨fun ξ => fderiv ℝ f ξ v.1, β, ?_, ?_, rfl⟩)
        (Submodule.subset_span ⟨f, LineDeriv.lineDerivOp v.2 β, hf, hfc, rfl⟩)
      · exact ((contDiff_infty_iff_fderiv.mp hf).2).clm_apply contDiff_const
      · exact (hfc.fderiv ℝ).comp_left (g := fun L : V →L[ℝ] ℂ => L v.1) (by simp)
    · intro l
      let l1 : V →L[ℝ] ℝ := l.comp (ContinuousLinearMap.inl ℝ V M)
      let l2 : M →L[ℝ] ℝ := l.comp (ContinuousLinearMap.inr ℝ V M)
      have hl : ∀ p : V × M, l p = l1 p.1 + l2 p.2 := by
        intro p
        simp only [l1, l2, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
          ContinuousLinearMap.inr_apply]
        rw [← map_add (f := _)]
        congr 1
        ext <;> simp
      have htg : Function.HasTemperateGrowth (fun y : M => ((l2 y : ℝ) : ℂ)) := by
        fun_prop
      have hfe : (fun x : V × M => (l x : ℂ) * (f x.1 * β x.2)) =
          (fun p : V × M => (fun ξ => ((l1 ξ : ℝ) : ℂ) * f ξ) p.1 * β p.2) +
          (fun p : V × M => f p.1 *
            (SchwartzMap.smulLeftCLM ℂ (fun y : M => ((l2 y : ℝ) : ℂ)) β) p.2) := by
        ext p
        simp only [Pi.add_apply, SchwartzMap.smulLeftCLM_apply_apply htg, smul_eq_mul, hl p]
        push_cast
        ring
      rw [hfe]
      refine (Submodule.span ℂ S).add_mem
        (Submodule.subset_span ⟨fun ξ => ((l1 ξ : ℝ) : ℂ) * f ξ, β, ?_, ?_, rfl⟩)
        (Submodule.subset_span ⟨f, SchwartzMap.smulLeftCLM ℂ (fun y : M => ((l2 y : ℝ) : ℂ)) β,
          hf, hfc, rfl⟩)
      · exact (Complex.ofRealCLM.contDiff.comp l1.contDiff).mul hf
      · exact hfc.mul_left
  have hclosed : ∀ F ∈ A, (∃ C, ∀ x, ‖F x‖ ≤ C) ∧ Differentiable ℝ F ∧
      (∀ v : V × M, (fun x => fderiv ℝ F x v) ∈ A) ∧
      ∀ l : V × M →L[ℝ] ℝ, (fun x => (l x : ℂ) * F x) ∈ A := by
    intro F hF
    induction hF using Submodule.span_induction with
    | mem F hF => exact hgen F hF
    | zero =>
      refine ⟨⟨0, fun x => by simp⟩, differentiable_const 0, fun v => ?_, fun l => ?_⟩
      · have h0 : (fun x => fderiv ℝ (0 : V × M → ℂ) x v) = 0 := by
          ext x
          simp
        rw [h0]
        exact (Submodule.span ℂ S).zero_mem
      · have h0 : (fun x => (l x : ℂ) * (0 : V × M → ℂ) x) = 0 := by
          ext x
          simp
        rw [h0]
        exact (Submodule.span ℂ S).zero_mem
    | add F G _ _ hF hG =>
      obtain ⟨⟨C1, hC1⟩, hd1, hv1, hl1⟩ := hF
      obtain ⟨⟨C2, hC2⟩, hd2, hv2, hl2⟩ := hG
      refine ⟨⟨C1 + C2, fun x => (norm_add_le _ _).trans (add_le_add (hC1 x) (hC2 x))⟩,
        hd1.add hd2, fun v => ?_, fun l => ?_⟩
      · have he : (fun x => fderiv ℝ (F + G) x v) =
            (fun x => fderiv ℝ F x v) + (fun x => fderiv ℝ G x v) := by
          ext x
          rw [fderiv_add (hd1 x) (hd2 x)]
          rfl
        rw [he]
        exact (Submodule.span ℂ S).add_mem (hv1 v) (hv2 v)
      · have he : (fun x => (l x : ℂ) * (F + G) x) =
            (fun x => (l x : ℂ) * F x) + (fun x => (l x : ℂ) * G x) := by
          ext x
          simp [mul_add]
        rw [he]
        exact (Submodule.span ℂ S).add_mem (hl1 l) (hl2 l)
    | smul c F _ hF =>
      obtain ⟨⟨C1, hC1⟩, hd1, hv1, hl1⟩ := hF
      refine ⟨⟨‖c‖ * C1, fun x => ?_⟩, hd1.const_smul c, fun v => ?_, fun l => ?_⟩
      · rw [Pi.smul_apply, norm_smul]
        exact mul_le_mul_of_nonneg_left (hC1 x) (norm_nonneg _)
      · have he : (fun x => fderiv ℝ (c • F) x v) = c • (fun x => fderiv ℝ F x v) := by
          ext x
          rw [fderiv_const_smul (hd1 x) c]
          rfl
        rw [he]
        exact (Submodule.span ℂ S).smul_mem c (hv1 v)
      · have he : (fun x => (l x : ℂ) * (c • F) x) = c • (fun x => (l x : ℂ) * F x) := by
          ext x
          simp only [Pi.smul_apply, smul_eq_mul]
          ring
        rw [he]
        exact (Submodule.span ℂ S).smul_mem c (hl1 l)
  obtain ⟨G, hG⟩ := hS (V × M) A hclosed _ (Submodule.subset_span ⟨h, α, hh, hhc, rfl⟩)
  exact ⟨G, fun ξ y => by rw [hG]⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.DenseAway
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

noncomputable section

namespace UpperTheory.V.Af.Smo.DenseAwayFromPlace

open GlobalTheory.CuspRep (cornerGL matN map_cornerGL_of_hom map_cornerGL_of_zero pFin_finGL)

private theorem dense_gl {K R : Type} [Field K] [NormedCommRing R] [CompleteSpace R] [Nontrivial R] (n : ℕ)
    (q : K →+* R) (hq : DenseRange q) : DenseRange (GeneralLinearGroup.map (n := Fin n) q) := by
  have ho : Topology.IsOpenEmbedding (Units.val : GL (Fin n) R → Matrix (Fin n) (Fin n) R) := by
    have h : ∀ (M : Type) [NormedRing M], CompleteSpace M → Topology.IsOpenEmbedding (Units.val : Mˣ → M) :=
      fun _ _ _ => Units.isOpenEmbedding_val
    exact @h _ Matrix.linftyOpNormedRing (inferInstanceAs (CompleteSpace (Fin n → Fin n → R)))
  have hd : DenseRange fun x : Matrix (Fin n) (Fin n) K => x.map q :=
    DenseRange.piMap fun _ : Fin n => DenseRange.piMap fun _ : Fin n => hq
  refine dense_iff_inter_open.2 fun U hU hne => ?_
  obtain ⟨x, u, hu, e⟩ := hd.exists_mem_open (ho.isOpenMap U hU) (hne.image _)
  have h1 : IsUnit (q x.det) := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, ← e]
    exact (Matrix.isUnit_iff_isUnit_det _).1 u.isUnit
  have h2 : x.det ≠ 0 := fun h => by
    rw [h, map_zero] at h1
    exact not_isUnit_zero h1
  exact ⟨u, hu, GeneralLinearGroup.mkOfDetNeZero x h2, Units.ext e.symm⟩

private theorem dense_abs {K R A : Type} [Field K] [NormedCommRing R] [CompleteSpace R] [Nontrivial R] [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] (n : ℕ) (a : K →+* A) (p : A →+* R) (s : R →ₙ+* A) (hs : Continuous s)
    (hp : ∀ x, p (s x) = x) (hq : DenseRange (p.comp a)) :
    Dense {x : GL (Fin n) A | ∃ γ k, GeneralLinearGroup.map p k = 1 ∧ x = GeneralLinearGroup.map a γ * k} := by
  have hc : Continuous (cornerGL n s) := by
    refine Continuous.units_map _ ?_
    change Continuous fun x : Matrix (Fin n) (Fin n) R => 1 - matN n s 1 + matN n s x
    exact continuous_const.add (continuous_id.matrix_map hs)
  have hps : ∀ y, GeneralLinearGroup.map p (cornerGL n s y) = y := fun y => by
    rw [map_cornerGL_of_hom s p (RingHom.id _) hp]
    rfl
  refine dense_iff_inter_open.2 fun U hU ⟨g, hg⟩ => ?_
  let Φ : GL (Fin n) R → GL (Fin n) A := fun y => cornerGL n s y * ((cornerGL n s (GeneralLinearGroup.map p g))⁻¹ * g)
  have hΦ : Continuous Φ := hc.mul continuous_const
  obtain ⟨γ, hγ⟩ := (dense_gl n _ hq).exists_mem_open (hU.preimage hΦ)
    ⟨GeneralLinearGroup.map p g, by simpa [Φ] using hg⟩
  refine ⟨_, hγ, γ, (GeneralLinearGroup.map a γ)⁻¹ * Φ (GeneralLinearGroup.map (p.comp a) γ), ?_, by simp⟩
  have e : GeneralLinearGroup.map p (GeneralLinearGroup.map a γ) = GeneralLinearGroup.map (p.comp a) γ := rfl
  simp only [Φ, map_mul, map_inv, hps, e, inv_mul_cancel, mul_one]

variable {E : Type} [Field E] [NumberField E]

private theorem cont_sLoc (w : HeightOneSpectrum (𝓞 E)) : Continuous (sLoc E w) := by
  classical
  have hle : (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 E))) ≤ Filter.principal {w}ᶜ :=
    Filter.le_principal_iff.2 (Set.finite_singleton w).compl_mem_cofinite
  let f : w.adicCompletion E → RestrictedProduct (fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
      (fun v => (v.adicCompletionIntegers E : Set (v.adicCompletion E))) (Filter.principal {w}ᶜ) :=
    fun x => ⟨Pi.single w x, Filter.eventually_principal.2 fun v hv => by
      rw [Pi.single_eq_of_ne hv]
      exact zero_mem _⟩
  have hf : Continuous f := RestrictedProduct.continuous_rng_of_principal.2
    (continuous_single (A := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E) w)
  exact (RestrictedProduct.continuous_inclusion hle).comp hf

variable (S : Finset (HeightOneSpectrum (𝓞 E)))

private theorem sum_mem (x : ∀ v : S, v.1.adicCompletion E) (w : S) : pLoc E w.1 (∑ v : S, sLoc E v.1 (x v)) = x w := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_eq_single w]
  · exact Pi.single_eq_same (M := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E) w.1 _
  · exact fun v _ h => Pi.single_eq_of_ne (M := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
      (fun e => h (Subtype.ext e.symm)) _
  · simp

private theorem sum_notMem (x : ∀ v : S, v.1.adicCompletion E) {w : HeightOneSpectrum (𝓞 E)} (hw : w ∉ S) :
    pLoc E w (∑ v : S, sLoc E v.1 (x v)) = 0 := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_eq_zero fun v _ => Pi.single_eq_of_ne (M := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
    (fun e : w = v.1 => hw (e ▸ v.2)) _

private abbrev RS : Type :=
  (∀ v : S, v.1.adicCompletion E) × (∀ w : (Finset.univ : Finset (InfinitePlace E)), w.1.Completion)

private def pS : Ad E →+* RS S :=
  (RingHom.pi fun v : S => (pLoc E v.1).comp (pFin E)).prod
    (RingHom.pi fun w => (Pi.evalRingHom (fun w : InfinitePlace E => w.Completion) w.1).comp
      (RingHom.fst (InfiniteAdeleRing E) (Af E)))

private def sS : RS S →ₙ+* Ad E where
  toFun x := ((fun w => x.2 ⟨w, Finset.mem_univ w⟩, ∑ v : S, sLoc E v.1 (x.1 v)) : InfiniteAdeleRing E × Af E)
  map_mul' x y := Prod.ext rfl (FiniteAdeleRing.ext _ fun w => by
    change pLoc E w (∑ v : S, sLoc E v.1 ((x.1 * y.1) v)) =
      pLoc E w ((∑ v : S, sLoc E v.1 (x.1 v)) * ∑ v : S, sLoc E v.1 (y.1 v))
    rw [map_mul]
    by_cases hw : w ∈ S
    · rw [sum_mem S _ ⟨w, hw⟩, sum_mem S _ ⟨w, hw⟩, sum_mem S _ ⟨w, hw⟩]
      rfl
    · rw [sum_notMem S _ hw, sum_notMem S _ hw, zero_mul])
  map_zero' := Prod.ext rfl (Finset.sum_eq_zero fun v _ => map_zero _)
  map_add' x y := Prod.ext rfl ((Finset.sum_congr rfl fun v _ => map_add _ _ _).trans Finset.sum_add_distrib)

private theorem cont_sS : Continuous (sS S) :=
  Continuous.prodMk (continuous_pi fun w => (continuous_apply _).comp continuous_snd)
    (continuous_finsetSum _ fun v _ => (cont_sLoc v.1).comp ((continuous_apply v).comp continuous_fst))

private theorem pS_sS (x : RS S) : pS S (sS S x) = x :=
  Prod.ext (funext fun v => sum_mem S x.1 v) rfl

end UpperTheory.V.Af.Smo.DenseAwayFromPlace

end

open UpperTheory.V.Af.Smo.DenseAwayFromPlace in
theorem UpperTheory.V.Af.Smo.denseAway :
    UpperTheory.V.Af.Smo.DenseAway := by
  intro E _ _ n S
  haveI : Inhabited (Finset.univ : Finset (InfinitePlace E)) := ⟨⟨Classical.arbitrary _, Finset.mem_univ _⟩⟩
  haveI : Nontrivial (∀ w : (Finset.univ : Finset (InfinitePlace E)), w.1.Completion) := Pi.nontrivial
  haveI : Nontrivial (RS S) := nontrivial_prod_right
  refine (dense_abs n (algebraMap E (Ad E)) (pS S) (sS S) (cont_sS S) (pS_sS S)
    (GroundTheory.Global.denseRange_algebraMap_prod_pi S Finset.univ)).mono ?_
  rintro _ ⟨γ, k, hk, rfl⟩
  have h : ∀ i j, pS S (k i j) = (1 : Matrix (Fin n) (Fin n) (RS S)) i j := fun i j =>
    congrArg (fun x : GL (Fin n) (RS S) => x i j) hk
  refine ⟨γ, GeneralLinearGroup.map (pFin E) k, fun w hw => ?_, congrArg _ ?_⟩
  · refine Units.ext (Matrix.ext fun i j => ?_)
    refine (congrFun (congrArg Prod.fst (h i j)) ⟨w, hw⟩).trans ?_
    by_cases e : i = j <;> simp [Matrix.one_apply, e]
  · refine Units.ext (Matrix.ext fun i j => Prod.ext (funext fun w => ?_) ?_)
    · refine (congrFun (congrArg Prod.snd (h i j)) ⟨w, Finset.mem_univ w⟩).trans ?_
      change _ = (((1 : Matrix (Fin n) (Fin n) (Ad E)) i j).1 - 0 + 0) w
      rw [add_zero, sub_zero]
      by_cases e : i = j <;> simp only [Matrix.one_apply, e, if_true, if_false] <;> rfl
    · exact (congrArg (fun x : GL (Fin n) (Af E) => x i j)
        (GlobalTheory.CuspRep.pFin_finGL (GeneralLinearGroup.map (pFin E) k))).symm
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.PftDeriv
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem exists_one_add_norm_pow_mul_norm_schwartz_le {V M E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup M] [NormedSpace ℝ M] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : 𝓢(V × M, E)) (k : ℕ) :
    ∃ C, ∀ ξ m, (1 + ‖ξ‖) ^ k * ‖H (ξ, m)‖ ≤ C := by
  refine ⟨2 ^ k * ((Finset.Iic (k, 0)).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2) H, fun ξ m => ?_⟩
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0)) le_rfl le_rfl H (ξ, m)
  rw [norm_iteratedFDeriv_zero] at h
  refine le_trans ?_ h
  gcongr
  exact norm_fst_le (ξ, m)

theorem UpperTheory.V.Af.Smo.pftDeriv :
    UpperTheory.V.Af.Smo.PftDeriv := by
  intro V M _ _ _ _ _ _ _ _ G
  obtain ⟨C0, hC0⟩ := exists_one_add_norm_pow_mul_norm_schwartz_le G (Module.finrank ℝ V + 2)
  obtain ⟨C1, hC1⟩ := exists_one_add_norm_pow_mul_norm_schwartz_le (SchwartzMap.fderivCLM ℝ (V × M) ℂ G) (Module.finrank ℝ V + 1)
  simp only [SchwartzMap.fderivCLM_apply] at hC1
  have hC0n : 0 ≤ C0 := le_trans (by positivity) (hC0 0 0)
  have hC1n : 0 ≤ C1 := le_trans (by positivity) (hC1 0 0)
  have hG0 : Continuous (⇑G) := G.continuous
  have hG1 : Continuous (fun p => fderiv ℝ (⇑G) p) :=
    (SchwartzMap.fderivCLM ℝ (V × M) ℂ G).continuous
  obtain ⟨B, hB⟩ : ∃ B : V → ℝ, ∀ ξ,
      B ξ = (C1 + 2 * Real.pi * C0) / (1 + ‖ξ‖) ^ (Module.finrank ℝ V + 1) := ⟨_, fun _ => rfl⟩
  have hBint : Integrable B := by
    have h := (integrable_one_add_norm (E := V) (μ := volume)
      (r := ((Module.finrank ℝ V + 1 : ℕ) : ℝ)) (by push_cast; linarith)).const_mul (C1 + 2 * Real.pi * C0)
    refine h.congr (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [hB]
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast, div_eq_mul_inv]
  have hGB : ∀ ξ m, ‖G (ξ, m)‖ ≤ B ξ := by
    intro ξ m
    rw [hB, le_div_iff₀ (by positivity)]
    calc ‖G (ξ, m)‖ * (1 + ‖ξ‖) ^ (Module.finrank ℝ V + 1)
        ≤ (1 + ‖ξ‖) ^ (Module.finrank ℝ V + 2) * ‖G (ξ, m)‖ := by
          have : (1 + ‖ξ‖) ^ (Module.finrank ℝ V + 1) ≤ (1 + ‖ξ‖) ^ (Module.finrank ℝ V + 2) :=
            pow_le_pow_right₀ (by linarith [norm_nonneg ξ]) (by omega)
          nlinarith [norm_nonneg (G (ξ, m))]
      _ ≤ C0 := hC0 ξ m
      _ ≤ C1 + 2 * Real.pi * C0 := by nlinarith [Real.pi_gt_three]
  obtain ⟨F', hF'⟩ : ∃ F' : V × M → V → (V × M →L[ℝ] ℂ), ∀ z ξ, F' z ξ =
      ((𝐞 (-⟪ξ, z.1⟫) : Circle) : ℂ) • ((fderiv ℝ G (ξ, z.2)).comp
        ((0 : V × M →L[ℝ] V).prod (ContinuousLinearMap.snd ℝ V M))) +
      G (ξ, z.2) • ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
        (2 * (Real.pi : ℂ) * Complex.I * 𝐞 (-⟪ξ, z.1⟫))).comp
        (-((innerSL ℝ ξ).comp (ContinuousLinearMap.fst ℝ V M)))) := ⟨_, fun _ _ => rfl⟩
  have hF'v : ∀ z ξ v, F' z ξ v = (𝐞 (-⟪ξ, z.1⟫) : ℂ) * fderiv ℝ G (ξ, z.2) (0, v.2) +
      G (ξ, z.2) * (-((⟪ξ, v.1⟫ : ℝ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * 𝐞 (-⟪ξ, z.1⟫))) := by
    intro z ξ v
    rw [hF']
    simp [Complex.real_smul]
  have hcont : ∀ z, Continuous (F' z) := by
    intro z
    have he : Continuous (fun ξ : V => ((𝐞 (-⟪ξ, z.1⟫) : Circle) : ℂ)) := by fun_prop
    have : F' z = fun ξ => _ := funext (hF' z)
    rw [this]
    fun_prop
  have hbound : ∀ z ξ, ‖F' z ξ‖ ≤ B ξ := by
    intro z ξ
    have ht : 0 < 1 + ‖ξ‖ := by positivity
    have ha : ‖fderiv ℝ G (ξ, z.2)‖ ≤ C1 / (1 + ‖ξ‖) ^ (Module.finrank ℝ V + 1) := by
      rw [le_div_iff₀ (by positivity), mul_comm]
      exact hC1 ξ z.2
    have hb : ‖G (ξ, z.2)‖ * ‖ξ‖ ≤ C0 / (1 + ‖ξ‖) ^ (Module.finrank ℝ V + 1) := by
      rw [le_div_iff₀ (by positivity)]
      calc ‖G (ξ, z.2)‖ * ‖ξ‖ * (1 + ‖ξ‖) ^ (Module.finrank ℝ V + 1)
          ≤ ‖G (ξ, z.2)‖ * (1 + ‖ξ‖) * (1 + ‖ξ‖) ^ (Module.finrank ℝ V + 1) := by
            gcongr
            linarith
        _ = (1 + ‖ξ‖) ^ (Module.finrank ℝ V + 2) * ‖G (ξ, z.2)‖ := by ring
        _ ≤ C0 := hC0 ξ z.2
    rw [hB]
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    rw [hF'v]
    have h0v : ‖((0 : V), v.2)‖ ≤ ‖v‖ := by
      rw [Prod.norm_def, Prod.norm_def]
      simp
    have h1 : ‖fderiv ℝ G (ξ, z.2) (0, v.2)‖ ≤ ‖fderiv ℝ G (ξ, z.2)‖ * ‖v‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr)
    have h2 : |⟪ξ, v.1⟫| ≤ ‖ξ‖ * ‖v‖ :=
      (abs_real_inner_le_norm _ _).trans (by gcongr; exact norm_fst_le v)
    have e1 : ‖(𝐞 (-⟪ξ, z.1⟫) : ℂ) * fderiv ℝ G (ξ, z.2) (0, v.2)‖
        = ‖fderiv ℝ G (ξ, z.2) (0, v.2)‖ := by
      rw [norm_mul, Circle.norm_coe, one_mul]
    have e2 : ‖G (ξ, z.2) * (-((⟪ξ, v.1⟫ : ℝ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * 𝐞 (-⟪ξ, z.1⟫)))‖
        = ‖G (ξ, z.2)‖ * (|⟪ξ, v.1⟫| * (2 * Real.pi)) := by
      simp [abs_of_pos Real.pi_pos, Circle.norm_coe]
    have h3 := mul_le_mul_of_nonneg_right hb (by positivity : 0 ≤ ‖v‖ * (2 * Real.pi))
    have h4 := mul_le_mul_of_nonneg_right ha (norm_nonneg v)
    calc _ ≤ ‖fderiv ℝ G (ξ, z.2)‖ * ‖v‖ + ‖G (ξ, z.2)‖ * (‖ξ‖ * ‖v‖ * (2 * Real.pi)) := by
          refine (norm_add_le _ _).trans ?_
          rw [e1, e2]
          exact add_le_add h1 (by gcongr)
      _ ≤ (C1 + 2 * Real.pi * C0) / (1 + ‖ξ‖) ^ (Module.finrank ℝ V + 1) * ‖v‖ := by
          have e3 : (C1 + 2 * Real.pi * C0) / (1 + ‖ξ‖) ^ (Module.finrank ℝ V + 1) * ‖v‖
              = C1 / (1 + ‖ξ‖) ^ (Module.finrank ℝ V + 1) * ‖v‖
                + C0 / (1 + ‖ξ‖) ^ (Module.finrank ℝ V + 1) * (‖v‖ * (2 * Real.pi)) := by ring
          rw [e3]
          nlinarith [h3, h4]
  have hFint : ∀ z, Integrable (F' z) :=
    fun z => hBint.mono' (hcont z).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => hbound z ξ)
  have hder1 : ∀ ξ z, HasFDerivAt (fun z : V × M => (𝐞 (-⟪ξ, z.1⟫) : ℂ) * G (ξ, z.2)) (F' z ξ) z := by
    intro ξ z
    have h1 := (Real.hasDerivAt_fourierChar _).hasFDerivAt.comp z
      (((innerSL ℝ ξ).comp (ContinuousLinearMap.fst ℝ V M)).hasFDerivAt.neg)
    have h2 : HasFDerivAt (fun z : V × M => G (ξ, z.2))
        ((fderiv ℝ G (ξ, z.2)).comp ((0 : V × M →L[ℝ] V).prod (ContinuousLinearMap.snd ℝ V M))) z :=
      (G.hasFDerivAt (ξ, z.2)).comp z ((hasFDerivAt_const ξ z).prodMk hasFDerivAt_snd)
    rw [hF']
    refine ((h1.mul h2).congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => ?_)).congr_fderiv ?_
    · simp
    · refine ContinuousLinearMap.ext fun v => ?_
      simp
  have hpft : ∀ (H : V × M → ℂ) z, pft H z = ∫ ξ, (𝐞 (-⟪ξ, z.1⟫) : ℂ) * H (ξ, z.2) := by
    intro H z
    simp only [UpperTheory.V.Af.Smo.pft, Real.fourier_eq, Circle.smul_def, smul_eq_mul]
  have hder : ∀ z, HasFDerivAt (pft ⇑G) (∫ ξ, F' z ξ) z := by
    intro z
    have hfun : pft ⇑G = fun z => ∫ ξ, (𝐞 (-⟪ξ, z.1⟫) : ℂ) * G (ξ, z.2) := funext (hpft G)
    rw [hfun]
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (s := Set.univ) (bound := B)
      Filter.univ_mem ?_ ?_ ((hcont z).aestronglyMeasurable) ?_ hBint ?_
    · refine Filter.Eventually.of_forall fun z' => ?_
      have : Continuous fun ξ : V => (𝐞 (-⟪ξ, z'.1⟫) : ℂ) * G (ξ, z'.2) := by fun_prop
      exact this.aestronglyMeasurable
    · have : Continuous fun ξ : V => (𝐞 (-⟪ξ, z.1⟫) : ℂ) * G (ξ, z.2) := by fun_prop
      refine hBint.mono' this.aestronglyMeasurable (Filter.Eventually.of_forall fun ξ => ?_)
      rw [norm_mul, Circle.norm_coe, one_mul]
      exact hGB ξ z.2
    · exact Filter.Eventually.of_forall fun ξ z' _ => hbound z' ξ
    · exact Filter.Eventually.of_forall fun ξ z' _ => hder1 ξ z'
  refine ⟨fun z => (hder z).differentiableAt, fun v => ?_⟩
  have hl := (Complex.ofRealCLM.comp ((innerSL ℝ v.1).comp
    (ContinuousLinearMap.fst ℝ V M))).hasTemperateGrowth
  obtain ⟨G', hG'⟩ : ∃ G' : 𝓢(V × M, ℂ), ∀ p : V × M,
      G' p = -(2 * (Real.pi : ℂ) * Complex.I) * ((⟪v.1, p.1⟫ : ℝ) : ℂ) * G p + fderiv ℝ G p (0, v.2) := by
    refine ⟨(-(2 * (Real.pi : ℂ) * Complex.I)) • SchwartzMap.smulLeftCLM ℂ (⇑(Complex.ofRealCLM.comp ((innerSL ℝ v.1).comp (ContinuousLinearMap.fst ℝ V M)))) G
      + LineDeriv.lineDerivOp ((0 : V), v.2) G, fun p => ?_⟩
    simp [SchwartzMap.smulLeftCLM_apply_apply hl, SchwartzMap.lineDerivOp_apply_eq_fderiv]
    ring
  refine ⟨G', ?_⟩
  funext z
  show fderiv ℝ (pft ⇑G) z v = pft (⇑G') z
  rw [(hder z).fderiv, ContinuousLinearMap.integral_apply (hFint z) v, hpft]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  dsimp only
  rw [hF'v, hG', real_inner_comm v.1 ξ]
  ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.SeedConv
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem exists_schwartz_integral_eq_one {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [μ.IsAddHaarMeasure] (F : X → ℂ) (U : Set X) (x₀ : X)
    (hU : U ∈ 𝓝 x₀) (hF : ContinuousOn F U) (h0 : F x₀ ≠ 0) : ∃ α : 𝓢(X, ℂ), ∫ x, F x * α x ∂μ = 1 := by
  have hc : ContinuousAt (fun x => (F x / F x₀).re) x₀ :=
    Complex.continuous_re.continuousAt.comp ((hF.continuousAt hU).div_const _)
  have hp : ∀ᶠ x in 𝓝 x₀, 0 < (F x / F x₀).re :=
    hc.eventually (lt_mem_nhds (by simp [div_self h0]))
  obtain ⟨r, hr, hb⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (Filter.inter_mem (interior_mem_nhds.2 hU) hp)
  let b : ContDiffBump x₀ := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  have hs : tsupport b = Metric.closedBall x₀ r := b.tsupport_eq
  have hs' : Function.support b = Metric.ball x₀ r := b.support_eq
  have hG : Continuous fun x => b x • (F x / F x₀) := by
    refine continuous_of_tsupport fun x hx => ?_
    have hx' : x ∈ Metric.closedBall x₀ r := hs ▸ tsupport_smul_subset_left _ _ hx
    exact b.continuous.continuousAt.smul ((hF.continuousAt (mem_interior_iff_mem_nhds.1 (hb hx').1)).div_const _)
  have hK : HasCompactSupport fun x => b x • (F x / F x₀) := b.hasCompactSupport.smul_right
  have hI : Integrable (fun x => b x • (F x / F x₀)) μ := hG.integrable_of_hasCompactSupport hK
  have hpos : 0 < ∫ x, (b x • (F x / F x₀)).re ∂μ := by
    refine (Complex.continuous_re.comp hG).integral_pos_of_hasCompactSupport_nonneg_nonzero (x := x₀)
      (hK.comp_left (g := Complex.re) rfl) (fun x => ?_) ?_
    · by_cases hx : b x = 0
      · simp [hx]
      · have hx' : x ∈ Metric.closedBall x₀ r := Metric.ball_subset_closedBall (hs' ▸ hx)
        have h1 : 0 < (F x / F x₀).re := (hb hx').2
        simpa using mul_nonneg b.nonneg h1.le
    · have h1 : b x₀ = 1 := b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)
      simp [h1, div_self h0]
  have hne : ∫ x, b x • (F x / F x₀) ∂μ ≠ 0 := by
    intro h
    have h2 := integral_re hI
    rw [h] at h2
    simp only [RCLike.re_to_complex, Complex.zero_re] at h2
    exact hpos.ne' h2
  set c := ∫ x, b x • (F x / F x₀) ∂μ with hc'
  have hd : ContDiff ℝ ∞ fun x => b x • ((F x₀)⁻¹ * c⁻¹) := b.contDiff.smul contDiff_const
  have hk : HasCompactSupport fun x => b x • ((F x₀)⁻¹ * c⁻¹) := b.hasCompactSupport.smul_right
  refine ⟨hk.toSchwartzMap hd, ?_⟩
  have e : ∀ x, F x * (hk.toSchwartzMap hd) x = (b x • (F x / F x₀)) * c⁻¹ := fun x => by
    change F x * (b x • ((F x₀)⁻¹ * c⁻¹)) = _
    simp only [Complex.real_smul, div_eq_mul_inv]
    ring
  simp only [e]
  rw [integral_mul_const, ← hc', mul_inv_cancel₀ hne]

theorem UpperTheory.V.Af.Smo.seedConv :
    UpperTheory.V.Af.Smo.ChartCont → UpperTheory.V.Af.Smo.SeedConv := by
  intro h E _ _ _ n W hW y hy
  haveI i1 : (volume : Measure (Rinf E)).IsAddHaarMeasure := inferInstance
  haveI i2 : (volume : Measure (Fin n → Rinf E)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI i3 : (volume : Measure (Lie E n)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  refine exists_schwartz_integral_eq_one volume (chart W 1) (invSet E n) (toL y.val) ?_ ?_ ?_
  · exact TR.isOpen_invSet.mem_nhds (TR.val_mem_invSet y)
  · exact (h E n W hW).1.comp (f := fun x => ((1 : GA E n), x)) (by fun_prop) fun x hx => ⟨trivial, hx⟩
  · rw [TR.chart_val, one_mul]
    exact hy
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ChartSmul
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem isY_map {R R' : Type} [CommRing R] [CommRing R'] {n m : ℕ} (f : R →+* R') (p : GL (Fin n) R)
    (hp : IsY m p.val) : IsY m (GeneralLinearGroup.map f p).val := by
  intro i hi
  obtain ⟨h1, h2⟩ := hp i hi
  refine ⟨?_, fun j hj => ?_⟩
  · change f (p.val i i) = 1
    rw [h1, map_one]
  · change f (p.val i j) = 0
    rw [h2 j hj, map_zero]

private theorem chart_smul {E : Type} [Field E] [NumberField E] [IsTotallyReal E] {n : ℕ} (f f' : GA E n → ℂ)
    (g g' : GA E n) (a : ℂ) (h : ∀ y, f (g * infGL E n y) = a * f' (g' * infGL E n y)) (x : Lie E n) :
    chart f g x = a * chart f' g' x := by
  unfold chart
  split_ifs with hx
  · exact h _
  · simp

theorem UpperTheory.V.Af.Smo.killP :
    UpperTheory.V.Af.Smo.ArchKir → UpperTheory.V.Af.Smo.FinKir → UpperTheory.V.Af.Smo.EmbY → UpperTheory.V.Af.Smo.PsiInf → UpperTheory.V.Af.Smo.ChartCont → UpperTheory.V.Af.Smo.KillP := by
  intro hA hF hE hP hC E _ _ _ n hn S U
  obtain ⟨c, Hf, hf1, hc, hf⟩ := hF E n hn S U
  obtain ⟨Hi, hi1, hi⟩ := hA E n (n - 1) (by omega)
  refine ⟨c, fun p => Hi (GeneralLinearGroup.map (pInf E) p) * Hf (GeneralLinearGroup.map (pFin E) p),
    by simp [hi1, hf1], hc, fun α => ?_⟩
  obtain ⟨β, hβ⟩ := hi α
  refine ⟨β, fun W hW hb hWh hU p hp => ?_⟩
  obtain ⟨C, hb⟩ := hb
  have hpi := isY_map (pInf E) p hp.1
  have hpf := isY_map (pFin E) p hp.1
  have hS := hp.2
  beta_reduce
  have e : p = finGL E n (GeneralLinearGroup.map (pFin E) p) * infGL E n (GeneralLinearGroup.map (pInf E) p) := by
    rw [← TR.infGL_comm, TR.infGL_mul_finGL]
  generalize GeneralLinearGroup.map (pInf E) p = a at *
  generalize GeneralLinearGroup.map (pFin E) p = b at *
  have h1 : ∀ x, chart (fop c W) (finGL E n b) x = Hf b * chart W 1 x := by
    refine chart_smul _ _ _ _ _ fun y => ?_
    have := hf (fun k => W (finGL E n k * infGL E n y)) (fun ν _ hν g _ => ?_) (fun g _ u hu _ => ?_) b hS hpf
    · simp only [map_one] at this
      rw [← this]
      unfold fop comb
      refine Finsupp.sum_congr fun x _ => ?_
      beta_reduce
      rw [map_mul, mul_assoc, mul_assoc, TR.infGL_comm]
    · obtain ⟨k1, k2⟩ := (hE E n 0).2.1 ν hν
      rw [map_mul, mul_assoc, hWh _ k1, k2]
      rfl
    · rw [map_mul, mul_assoc, ← TR.infGL_comm, ← mul_assoc, hU _ u hu]
  have h2 := hβ (chart W 1) ((hC E n W hW).2 1) ⟨max C 0, fun x => ?_⟩ (fun ν hν x => ?_) a hpi
  · unfold conv
    rw [e, TR.chart_mul]
    simp only [Function.comp_apply, h1, mul_assoc]
    rw [integral_const_mul, h2]
    ring
  · unfold chart
    split_ifs
    · exact (hb _).trans (le_max_left _ _)
    · simp
  · obtain ⟨k1, k2⟩ := (hE E n 0).2.2.1 ν hν
    have := congrFun (TR.chart_mul W 1 ν) x
    rw [Function.comp_apply] at this
    rw [← this]
    refine chart_smul _ _ _ _ _ (fun y => ?_) x
    rw [one_mul, one_mul, hWh _ k1, k2, hP]
end
