module

public import Development.AutomorphicArithmetic.WhittakerHecke.WhittakerFunctionContinuousBoundedEquivariant
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.NzCont
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.OpsEx

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.ConjLieElementEmbedRotationEqTrigMatrix
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

private theorem kInf_val {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (D : Dat ℚ E) (t : ℝ)
    (i j : Fin 2) (w : InfinitePlace E) :
    (kInf (em E (rot t))).val i j w = (((Nz.X t).val i j (Fo.pl ℚ w.embedding) : ℝ) : ℂ) := by
  have h1 := (UpperTheory.ConvolutionTheory.R2.Fo.coordMk ℚ E D).1 w.embedding ((rot t).val i j) 0
  rw [FieldIso.coord_embedding] at h1
  have h2 : D.mkE ((rot t).val i j) 0 = AdeleBaseChange.adeleMap ℚ E ((rot t).val i j) := by
    simp [Dat.mkE]
  have h3 : TR.pInf ℚ ((rot t).val i j) = (Nz.X t).val i j := by
    have h := congrArg (fun g : GL (Fin 2) (TR.Rinf ℚ) => g.val i j) (TR.pInf_infGL (Nz.X t))
    rw [← Nz.rot_eq] at h
    exact h
  change pInf E (AdeleBaseChange.adeleMap ℚ E ((rot t).val i j)) w = _
  rw [← h2, h1]
  simp [Fo.cw, h3]

private theorem kInf_rot {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (D : Dat ℚ E) (t : ℝ) :
    (kInf (em E (rot t))).val =
      !![fun _ => (Real.cos t : ℂ), fun _ => -(Real.sin t : ℂ); fun _ => (Real.sin t : ℂ), fun _ => (Real.cos t : ℂ)] := by
  ext i j w
  rw [kInf_val D]
  fin_cases i <;> fin_cases j <;> simp [Nz.X]

theorem UpperTheory.conj_lie_element_embed_rotation_eq_trig_matrix :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (D : Dat ℚ E) (t : ℝ), XB D (em E (rot t)) = !![(Real.cos t * Real.sin t) • thInf D, (Real.cos t ^ 2) • thInf D; -((Real.sin t ^ 2) • thInf D), -((Real.cos t * Real.sin t) • thInf D)] := by
  intro E _ _ _ D t
  have hinv : (kInf (em E (rot t)))⁻¹ = kInf (em E (rot (-t))) := by
    rw [Nz.rot_neg, map_inv]
    simp [kInf, map_inv]
  rw [XB, hinv, kInf_rot D, kInf_rot D]
  ext i j w
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Real.cos_neg, Real.sin_neg] <;> ring
end

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.LieActionPreservesRightInvarianceFiniteAdelic
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

theorem UpperTheory.lie_action_preserves_right_invariance_finite_adelic :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (k : GL (Fin 2) (A ℚ)), (∀ i j, (k.val i j).1 = ((1 : Matrix (Fin 2) (Fin 2) (A ℚ)) i j).1) → ∀ (f : Sm E 2) (X : Lie E 2), (∀ g, f.1 (g * em E k) = f.1 g) → ∀ g, (lie E 2 X f).1 (g * em E k) = (lie E 2 X f).1 g := by
  intro E _ _ _ k hk f X hf g
  have hfst : ∀ i j, ((em E k).val i j).1 = ((1 : Matrix (Fin 2) (Fin 2) (A E)) i j).1 := by
    intro i j
    have e : (em E k).val i j = AdeleBaseChange.adeleMap ℚ E (k.val i j) := rfl
    have e1 : (1 : Matrix (Fin 2) (Fin 2) (A E)) i j =
        AdeleBaseChange.adeleMap ℚ E ((1 : Matrix (Fin 2) (Fin 2) (A ℚ)) i j) := by
      by_cases h : i = j
      · subst h; simp
      · simp [Matrix.one_apply_ne h]
    rw [e, e1, AdeleBaseChange.adeleMap_apply, AdeleBaseChange.adeleMap_apply, hk i j]
  have h1 : Matrix.GeneralLinearGroup.map (pInf E) (em E k) = 1 := by
    have h2 : Matrix.GeneralLinearGroup.map (pInf E) (em E k) =
        Matrix.GeneralLinearGroup.map (pInf E) (1 : GL (Fin 2) (A E)) := by
      refine Units.ext (Matrix.ext fun i j => ?_)
      exact congrArg (fun x => (infEq E).symm x) (hfst i j)
    rw [h2, map_one]
  have hm : finGL E 2 (Matrix.GeneralLinearGroup.map (pFin E) (em E k)) = em E k := by
    have h3 := infGL_mul_finGL (em E k)
    rwa [h1, map_one, one_mul] at h3
  have hr : GlobalTheory.CuspRep.rt E 2 (em E k) f = f := Subtype.ext (funext hf)
  have h4 := LinearMap.congr_fun (lie_rt_fin X (Matrix.GeneralLinearGroup.map (pFin E) (em E k))) f
  rw [hm, Module.End.mul_apply, Module.End.mul_apply, hr] at h4
  exact (congrArg (fun φ : Sm E 2 => φ.1 g) h4).symm
end

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.LieActionPreservesSatakeEigenAtPlace
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

theorem UpperTheory.lie_action_preserves_satake_eigen_at_place :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (w : H.P E) (B : Multiset ℂˣ) (f : Sm E 2) (X : Lie E 2), UpperTheory.V.Af.Smo.EigAt w B f.1 → UpperTheory.V.Af.Smo.EigAt w B (lie E 2 X f).1 := by
  intro E _ _ _ w B f X hf g
  have hc : ∀ (k : GL (Fin 2) (Af E)) (φ : Sm E 2) (x : GA E 2),
      (lie E 2 X φ).1 (x * finGL E 2 k) = (lie E 2 X (GlobalTheory.CuspRep.rt E 2 (finGL E 2 k) φ)).1 x := by
    intro k φ x
    have h := LinearMap.congr_fun (lie_rt_fin X k) φ
    exact (congrArg (fun ψ : Sm E 2 => ψ.1 x) h).symm
  have hev : ∀ (k : GA E 2) (φ : Sm E 2) (x : GA E 2), (GlobalTheory.CuspRep.rt E 2 k φ).1 x = φ.1 (x * k) :=
    fun _ _ _ => rfl
  refine ⟨(hf 1).card, ?_, ?_⟩
  · intro y k hk
    have hfix : GlobalTheory.CuspRep.rt E 2 (finGL E 2 (locGL E 2 w k)) f = f := by
      refine Subtype.ext (funext fun x => ?_)
      have h := (hf x).inv 1 k hk
      simp only [one_mul, map_one, mul_one] at h
      rw [hev]
      exact h
    have e1 : g * finGL E 2 (locGL E 2 w (y * k)) =
        g * finGL E 2 (locGL E 2 w y) * finGL E 2 (locGL E 2 w k) := by
      simp only [map_mul, mul_assoc]
    show (lie E 2 X f).1 (g * finGL E 2 (locGL E 2 w (y * k))) = (lie E 2 X f).1 (g * finGL E 2 (locGL E 2 w y))
    rw [e1, hc, hfix]
  · intro ϖ hϖ j hj x
    have hfin := (GlobalTheory.TjCount.tj_cosets_finite_card_le E w 2 ϖ hϖ j hj).1
    have hsum : ∀ W : GL (Fin 2) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w (n := 2) → ℂ,
        ∑ᶠ c, Formalism.UG.Tj ℂ 2 (Formalism.UG.Ov E w) ϖ j c.out * W c =
          ∑ c ∈ hfin.toFinset, Formalism.UG.Tj ℂ 2 (Formalism.UG.Ov E w) ϖ j c.out * W c := by
      intro W
      refine finsum_eq_sum_of_support_subset _ fun c hc' => ?_
      rw [Set.Finite.coe_toFinset]
      exact fun h0 => hc' (by simp [h0])
    have key : ∑ c ∈ hfin.toFinset, Formalism.UG.Tj ℂ 2 (Formalism.UG.Ov E w) ϖ j c.out •
          GlobalTheory.CuspRep.rt E 2 (finGL E 2 (locGL E 2 w c.out)) f =
        GlobalTheory.LFun.satEig (Formalism.UG.qV E w) 2 B j • f := by
      refine Subtype.ext (funext fun z => ?_)
      have h := (hf z).eig ϖ hϖ j hj 1
      simp only [one_mul, map_one, mul_one] at h
      rw [hsum fun c => f.1 (z * finGL E 2 (locGL E 2 w c.out))] at h
      simpa [Submodule.coe_sum, Finset.sum_apply, hev] using h
    have h2 := congrArg (fun ψ : Sm E 2 => (lie E 2 X ψ).1 (g * finGL E 2 (locGL E 2 w x))) key
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply,
      smul_eq_mul] at h2
    rw [hsum fun c => (lie E 2 X f).1 (g * finGL E 2 (locGL E 2 w (x * c.out)))]
    rw [← h2]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_mul, map_mul, ← mul_assoc, hc]
end

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.LieActionPreservesFixedAtPlace
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

theorem UpperTheory.lie_action_preserves_fixed_at_place :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (w : H.P E) (f : Sm E 2) (X : Lie E 2), H.Fix w f.1 → H.Fix w (lie E 2 X f).1 := by
  intro E _ _ _ w f X hf g k hk
  have h1 : rt E 2 (finGL E 2 (locGL E 2 w k)) f = f :=
    Subtype.ext (funext fun x => hf x k hk)
  have h2 : lie E 2 X (rt E 2 (finGL E 2 (locGL E 2 w k)) f) =
      rt E 2 (finGL E 2 (locGL E 2 w k)) (lie E 2 X f) :=
    LinearMap.congr_fun (lie_rt_fin X (locGL E 2 w k)) f
  rw [h1] at h2
  exact (congrArg (fun u : Sm E 2 => u.1 g) h2).symm
end

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.ExistsSmoothLieActionMemCuspidalTranslates
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

private theorem rt_infGL_lie {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    (y : GL (Fin a) (Cinf E)) (X : Matrix (Fin a) (Fin a) (Cinf E)) :
    rt E a (infGL E a y) * lie E a (toL X) =
      lie E a (toL (y.val * X * (y⁻¹).val)) * rt E a (infGL E a y) := by
  refine LinearMap.ext fun φ => Subtype.ext <| funext fun g => ?_
  change fderiv ℝ (chart φ.1 (g * infGL E a y)) (oneL E a) (toL X) =
    fderiv ℝ (chart (fun x => φ.1 (x * infGL E a y)) g) (oneL E a) (toL (y.val * X * (y⁻¹).val))
  have hd : DifferentiableAt ℝ (chart φ.1 g) (toL y.val) :=
    (contDiffAt_chart φ.2 g (val_mem_invSet y)).differentiableAt (by simp)
  have e1 : lmul (toL y.val) (oneL E a) = toL y.val := mul_one y.val
  have e2 : rmul (toL y.val) (oneL E a) = toL y.val := one_mul y.val
  rw [chart_mul, chart_rt_inf, fderiv_comp _ (by rw [e1]; exact hd) (lmul (toL y.val)).differentiableAt,
    fderiv_comp _ (by rw [e2]; exact hd) (rmul (toL y.val)).differentiableAt, e1, e2,
    ContinuousLinearMap.fderiv, ContinuousLinearMap.fderiv]
  exact congrArg (fun Z => fderiv ℝ (chart φ.1 g) (toL y.val) (toL Z))
    (Units.inv_mul_cancel_right (y.val * X) y).symm

private theorem lie_rt_eq {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    (X : Matrix (Fin a) (Fin a) (Cinf E)) (h : GL (Fin a) (A E)) :
    ∃ Y : Lie E a, lie E a (toL X) * rt E a h = rt E a h * lie E a Y := by
  set y := Matrix.GeneralLinearGroup.map (pInf E) h with hy
  set κ := Matrix.GeneralLinearGroup.map (pFin E) h with hκ
  have hh : h = infGL E a y * finGL E a κ := (infGL_mul_finGL h).symm
  refine ⟨toL ((y⁻¹).val * X * y.val), ?_⟩
  have e : y.val * ((y⁻¹).val * X * y.val) * (y⁻¹).val = X := by
    simp [Matrix.mul_assoc]
  have key := rt_infGL_lie y ((y⁻¹).val * X * y.val)
  rw [e] at key
  conv_lhs => rw [hh, map_mul, ← mul_assoc, ← key, mul_assoc, lie_rt_fin, ← mul_assoc]
  rw [← map_mul, ← hh]

theorem UpperTheory.exists_smooth_lie_action_mem_cuspidal_translates :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (P : CuspSub E 2) (X : Lie E 2) (φ : GL (Fin 2) (A E) → ℂ), φ ∈ Tr P → ∃ f : Sm E 2, f.1 = φ ∧ (lie E 2 X f).1 ∈ Tr P := by
  intro E _ _ _ P X φ hφ
  induction hφ using Submodule.span_induction with
  | mem φ hφ =>
    obtain ⟨f, hf, h, rfl⟩ := hφ
    obtain ⟨Y, hY⟩ := lie_rt_eq (a := 2) (E := E) X h
    refine ⟨rt E 2 h ⟨f.1, f.2⟩, rfl, ?_⟩
    have e : lie E 2 X (rt E 2 h f) = rt E 2 h (lie E 2 Y f) := LinearMap.congr_fun hY f
    have hm : lie E 2 Y f ∈ P.V := P.stable (.lie Y) f hf
    refine Submodule.subset_span ⟨_, hm, h, ?_⟩
    rw [show (⟨f.1, f.2⟩ : Sm E 2) = f from rfl, e]
    rfl
  | zero => exact ⟨0, rfl, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨fa, rfl, ha⟩ := ha
    obtain ⟨fb, rfl, hb⟩ := hb
    refine ⟨fa + fb, rfl, ?_⟩
    rw [map_add (f := _)]
    exact (Tr P).add_mem ha hb
  | smul c a _ ha =>
    obtain ⟨fa, rfl, ha⟩ := ha
    refine ⟨c • fa, rfl, ?_⟩
    rw [map_smul]
    exact (Tr P).smul_mem c ha
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

noncomputable section

namespace UpperTheory.ConvolutionTheory.RankTwoDescent.SH

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

private theorem re_iy (y : ℝ) (hy : y ≠ 0) : re ((iy y : (A ℚ)ˣ) : A ℚ) = y := by
  have h : iy y = TR.infId ℚ ⟨fun _ => y, fun _ => y⁻¹, funext fun _ => mul_inv_cancel₀ hy, funext fun _ => inv_mul_cancel₀ hy⟩ := dif_neg hy
  have h2 : ∀ x, TR.pInf ℚ (TR.sInf ℚ x) = x := fun x => (TR.infEq ℚ).symm_apply_apply x
  rw [h, re]
  change TR.pInf ℚ (1 - TR.sInf ℚ 1 + TR.sInf ℚ (fun _ => y)) _ = y
  simp [h2]

private def Q (D : Dat ℚ E) (L N : ℕ) (f : Sm E 2) (X : Lie E 2) : Prop :=
  (∀ (y : (A ℚ)ˣ) x, Wo D (lie E 2 X f).1 (em E (aE y) * infGL E 2 x) ≠ 0 → ∀ v, Bad N v → Dv L v ((y : A ℚ) - 1)) ∧
  ∀ t ∈ UU, (∀ v, Dv L v ((t : A ℚ) - 1)) → ∀ (y : (A ℚ)ˣ) x,
    Wo D (lie E 2 X f).1 (em E (aE (y * t)) * infGL E 2 x) = Wo D (lie E 2 X f).1 (em E (aE y) * infGL E 2 x)

private theorem eig_smul {w : H.P E} {B : Multiset ℂˣ} {f : GL (Fin 2) (A E) → ℂ} (c : ℂ)
    (h : UpperTheory.V.Af.Smo.EigAt w B f) : UpperTheory.V.Af.Smo.EigAt w B (c • f) := fun g => by
  have h0 := h g
  refine ⟨h0.card, fun g' k hk => ?_, fun ϖ hϖ j hj g' => ?_⟩
  · simpa using congrArg (c * ·) (h0.inv g' k hk)
  · have h1 := h0.eig ϖ hϖ j hj g'
    simp only [Pi.smul_apply, smul_eq_mul] at h1 ⊢
    rw [mul_left_comm, ← h1, ← smul_eq_mul, smul_finsum]
    exact finsum_congr fun x => by rw [smul_eq_mul, mul_left_comm]

private theorem gd_smul {D : Dat ℚ E} {P : CuspSub E 2} {L N : ℕ} {f : Sm E 2} {X : Lie E 2} {c : ℂ}
    (hG : Gd D P L N f.1) (hm : (lie E 2 X f).1 ∈ Tr P) (hQ : Q D L N f X) :
    Gd D P L N (c • (lie E 2 X f).1) := by
  have hs : ∀ h, Wo D (c • (lie E 2 X f).1) h = c * Wo D (lie E 2 X f).1 h := fun h => (UpperTheory.whittakerPeriod_add_smul_and_norm_le E D).2.1 c _ h
  refine ⟨hG.pos, hG.dvd, hG.same, (Tr P).smul_mem c hm, hG.pl, fun w hw => ?_, fun k hk g => ?_, fun y x hne => ?_, fun t ht hL y x => ?_⟩
  · obtain ⟨h1, B, h2, h3⟩ := hG.fix w hw
    refine ⟨fun g k hk => ?_, B, h2, eig_smul c (UpperTheory.lie_action_preserves_satake_eigen_at_place E w B f X h3)⟩
    simpa using congrArg (c * ·) (UpperTheory.lie_action_preserves_fixed_at_place E w f X h1 g k hk)
  · have := UpperTheory.lie_action_preserves_right_invariance_finite_adelic E k hk.1 f X (hG.lev k hk) g
    simpa using congrArg (c * ·) this
  · rw [hs] at hne
    exact hQ.1 y x (right_ne_zero_of_mul hne)
  · rw [hs, hs, hQ.2 t ht hL y x]

private theorem q_cv {D : Dat ℚ E} {P : CuspSub E 2} {L N : ℕ} {f : Sm E 2} (k : GL (Fin 2) (A E))
    (hG : Gd D P L N f.1) (hc : Continuous f.1) (hX : Continuous (lie E 2 (toL (XB D k)) f).1)
    (hB : ∃ B : ℝ, ∀ g, ‖(lie E 2 (toL (XB D k)) f).1 g‖ ≤ B) : Q D L N f (toL (XB D k)) := by
  obtain ⟨h0, hadd, hd, -⟩ := UpperTheory.archimedeanConjugateCurve_oneParameterSubgroup E D k
  have key : ∀ g, HasDerivAt (fun t : ℝ => Wo D f.1 (g * infGL E 2 (cv D k t)))
      (Wo D (lie E 2 (toL (XB D k)) f).1 g) 0 := fun g =>
    UpperTheory.hasDerivAt_whittakerPeriod_oneParameter E D f (cv D k) _ g h0 hadd hd hc hX hB
  refine ⟨fun y x hne v hv => ?_, fun t ht hL y x => ?_⟩
  · by_contra hcon
    have hz : (fun s : ℝ => Wo D f.1 (em E (aE y) * infGL E 2 x * infGL E 2 (cv D k s))) = fun _ => 0 := funext fun s => by
      by_contra h1
      rw [mul_assoc, ← map_mul] at h1
      exact hcon (hG.supp y _ h1 v hv)
    have h2 := key (em E (aE y) * infGL E 2 x)
    rw [hz] at h2
    exact hne (h2.unique (hasDerivAt_const _ _))
  · have h1 := key (em E (aE (y * t)) * infGL E 2 x)
    have h2 := key (em E (aE y) * infGL E 2 x)
    have e : (fun s : ℝ => Wo D f.1 (em E (aE (y * t)) * infGL E 2 x * infGL E 2 (cv D k s))) =
        fun s : ℝ => Wo D f.1 (em E (aE y) * infGL E 2 x * infGL E 2 (cv D k s)) := funext fun s => by
      rw [mul_assoc, mul_assoc, ← map_mul, hG.tor t ht hL y]
    rw [e] at h1
    exact h1.unique h2

private theorem lieDerivative_linear (f : Sm E 2) (a b c : ℝ) (X Y Z : Lie E 2) :
    (lie E 2 (a • X + b • Y + c • Z) f).1 = (a : ℂ) • (lie E 2 X f).1 + (b : ℂ) • (lie E 2 Y f).1 + (c : ℂ) • (lie E 2 Z f).1 := by
  rw [map_add (f := _), map_add (f := _), map_smul, map_smul, map_smul]
  funext g
  simp

private theorem whittaker_lieDerivative_linear {D : Dat ℚ E} {f : Sm E 2} (hc : ∀ X, Continuous (lie E 2 X f).1) (a b c : ℝ) (X Y Z : Lie E 2)
    (h : GL (Fin 2) (A E)) :
    Wo D (lie E 2 (a • X + b • Y + c • Z) f).1 h = a * Wo D (lie E 2 X f).1 h + b * Wo D (lie E 2 Y f).1 h + c * Wo D (lie E 2 Z f).1 h := by
  obtain ⟨h1, h2, -⟩ := UpperTheory.whittakerPeriod_add_smul_and_norm_le E D
  rw [lieDerivative_linear, h1 _ _ (((hc X).const_smul _).add ((hc Y).const_smul _)) ((hc Z).const_smul _),
    h1 _ _ ((hc X).const_smul _) ((hc Y).const_smul _), h2, h2, h2]

private theorem quadraticCondition_linear {D : Dat ℚ E} {L N : ℕ} {f : Sm E 2} (hc : ∀ X, Continuous (lie E 2 X f).1) (a b c : ℝ) {X Y Z : Lie E 2}
    (hX : Q D L N f X) (hY : Q D L N f Y) (hZ : Q D L N f Z) : Q D L N f (a • X + b • Y + c • Z) := by
  refine ⟨fun y x hne v hv => ?_, fun t ht hL y x => ?_⟩
  · rw [whittaker_lieDerivative_linear hc] at hne
    by_contra hcon
    have h1 : Wo D (lie E 2 X f).1 (em E (aE y) * infGL E 2 x) = 0 := by
      by_contra h; exact hcon (hX.1 y x h v hv)
    have h2 : Wo D (lie E 2 Y f).1 (em E (aE y) * infGL E 2 x) = 0 := by
      by_contra h; exact hcon (hY.1 y x h v hv)
    have h3 : Wo D (lie E 2 Z f).1 (em E (aE y) * infGL E 2 x) = 0 := by
      by_contra h; exact hcon (hZ.1 y x h v hv)
    exact hne (by rw [h1, h2, h3]; ring)
  · rw [whittaker_lieDerivative_linear hc, whittaker_lieDerivative_linear hc, hX.2 t ht hL y x, hY.2 t ht hL y x, hZ.2 t ht hL y x]

private theorem xb_dec (D : Dat ℚ E) (t : ℝ) :
    toL (XB D (em E (rot t))) = (Real.cos t ^ 2) • toL (XB D (em E (rot 0))) + (Real.sin t ^ 2) • toL (XB D (em E (rot (Real.pi / 2)))) +
      (Real.cos t * Real.sin t) • ((2 : ℝ) • toL (XB D (em E (rot (Real.pi / 4)))) + (-1 : ℝ) • toL (XB D (em E (rot 0))) +
        (-1 : ℝ) • toL (XB D (em E (rot (Real.pi / 2))))) := by
  have c4 : Real.cos (Real.pi / 4) ^ 2 = 1 / 2 := by
    rw [Real.cos_pi_div_four, div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have s4 : Real.sin (Real.pi / 4) ^ 2 = 1 / 2 := by
    rw [Real.sin_pi_div_four, div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have m4 : Real.cos (Real.pi / 4) * Real.sin (Real.pi / 4) = 1 / 2 := by
    rw [Real.sin_pi_div_four, Real.cos_pi_div_four, ← pow_two, div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  rw [UpperTheory.conj_lie_element_embed_rotation_eq_trig_matrix E D t, UpperTheory.conj_lie_element_embed_rotation_eq_trig_matrix E D 0, UpperTheory.conj_lie_element_embed_rotation_eq_trig_matrix E D (Real.pi / 2), UpperTheory.conj_lie_element_embed_rotation_eq_trig_matrix E D (Real.pi / 4), c4, s4, m4]
  simp only [Real.cos_zero, Real.sin_zero, Real.cos_pi_div_two, Real.sin_pi_div_two]
  funext i j w
  fin_cases i <;> fin_cases j <;> simp <;> ring

end UpperTheory.ConvolutionTheory.RankTwoDescent.SH

open UpperTheory.ConvolutionTheory.RankTwoDescent.SH in
theorem UpperTheory.ConvolutionTheory.RankTwoDescent.shift_of :
    TrAdm → Shift := by
  intro hT E _ _ _ D P ω χ hC hU hχ L N φ hG
  have adm := hT E D P ω χ hC hU hχ
  obtain ⟨f, rfl, -⟩ := UpperTheory.exists_smooth_lie_action_mem_cuspidal_translates E P 0 φ hG.mem
  have hmem : ∀ X, (lie E 2 X f).1 ∈ Tr P := fun X => by
    obtain ⟨f', hf', hm⟩ := UpperTheory.exists_smooth_lie_action_mem_cuspidal_translates E P X f.1 hG.mem
    rwa [show f' = f from Subtype.ext hf'] at hm
  have hc : ∀ X, Continuous (lie E 2 X f).1 := fun X => (adm _ (hmem X)).cont
  have hb : ∀ X, ∃ B : ℝ, ∀ g, ‖(lie E 2 X f).1 g‖ ≤ B := fun X => (adm _ (hmem X)).bdd
  have hf0 := adm _ hG.mem
  have hq : ∀ k, Q D L N f (toL (XB D k)) := fun k => q_cv k hG hf0.cont (hc _) (hb _)
  set b0 : Lie E 2 := toL (XB D (em E (rot 0))) with hb0
  set b1 : Lie E 2 := toL (XB D (em E (rot (Real.pi / 2)))) with hb1
  set b2 : Lie E 2 := toL (XB D (em E (rot (Real.pi / 4)))) with hb2
  set b3 : Lie E 2 := (2 : ℝ) • b2 + (-1 : ℝ) • b0 + (-1 : ℝ) • b1 with hb3
  have hq3 : Q D L N f b3 := quadraticCondition_linear hc _ _ _ (hq _) (hq _) (hq _)
  set κ : ℂ := (2 * Real.pi * Complex.I)⁻¹ with hκ
  have hκ0 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  refine ⟨κ • (lie E 2 b1 f).1, κ • (lie E 2 b3 f).1, κ • (lie E 2 b0 f).1, gd_smul hG (hmem _) (hq _), gd_smul hG (hmem _) hq3,
    gd_smul hG (hmem _) (hq _), fun y t hy => ?_⟩
  obtain ⟨-, h2, -⟩ := UpperTheory.whittakerPeriod_add_smul_and_norm_le E D
  have e := UpperTheory.whittakerCoeff_lieDeriv_unipotent_eq_mul E D f ⟨hf0.cont, hf0.left⟩ (fun X => ⟨hc X, hb X⟩) (iy y) (em E (rot t))
  rw [xb_dec D t, whittaker_lieDerivative_linear hc, re_iy y hy, ← map_mul] at e
  rw [h2, h2, h2]
  have e' : (y : ℂ) * Wo D f.1 (em E (aE (iy y) * rot t)) = κ * ((2 * Real.pi * Complex.I * (y : ℂ)) * Wo D f.1 (em E (aE (iy y) * rot t))) := by
    rw [hκ]; field_simp
  rw [e', ← e, hκ]
  push_cast
  ring

end
