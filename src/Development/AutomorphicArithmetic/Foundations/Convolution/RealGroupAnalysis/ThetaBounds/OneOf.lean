module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.EqAmOfBarEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertSlashUnnormalizedConstMul

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.NormInf
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjOfSqNeg
theorem UpperTheory.Reformulated.B.Qh17.conj_of_sq_neg :
    ∀ {t : ℂ} {r : ℝ},
    r < (0 : ℝ) → t ^ (2 : ℕ) = (↑r : ℂ) → (starRingEnd ℂ : ℂ → ℂ) t = -t := by
  intro t r hr h
  have h1 : t.re * t.re - t.im * t.im = r := by
    have := congrArg Complex.re h
    simpa [pow_two] using this
  have h2 : t.re * t.im + t.im * t.re = 0 := by
    have := congrArg Complex.im h
    simpa [pow_two] using this
  have h3 : t.re = 0 := by
    have hm : t.re * t.im = 0 := by linarith [mul_comm t.im t.re]
    rcases mul_eq_zero.mp hm with h0 | h0
    · exact h0
    · exfalso
      rw [h0] at h1
      nlinarith [mul_self_nonneg t.re]
  apply Complex.ext
  · simp [h3]
  · simp
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical NumberField.LiesOver

namespace UpperTheory.ConvolutionTheory.R2.Ff.NI

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]

private theorem pInf_apply (x : A E) (w : InfinitePlace E) : GlobalTheory.CuspRep.pInf E x w =
    (InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)) (x.1 w) := rfl

private theorem pInf_infId (s : (Cinf E)ˣ) : GlobalTheory.CuspRep.pInf E (infId E s).val = s.val := by
  change (infEq E).symm (1 - infEq E 1 + infEq E s.val) = _
  simp

variable (F) in
private theorem real_comp (w : InfinitePlace E) (s : ℝ) :
    (InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w))
      (algebraMap (w.comap (algebraMap F E)).Completion w.Completion
        ((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal (w.comap (algebraMap F E)))).symm s)) = s := by
  let ψ : ℝ →+* ℂ := ((InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).toRingHom.comp
    (algebraMap (w.comap (algebraMap F E)).Completion w.Completion)).comp
    (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal (w.comap (algebraMap F E)))).symm.toRingHom
  have hψ : Continuous ψ :=
    ((InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_algebraMap _ _)).comp
      (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal (w.comap (algebraMap F E)))).symm.continuous
  have := map_real_smul ψ hψ s 1
  simpa [ψ] using this

private theorem pInf_am (a : A F) (w : InfinitePlace E) :
    GlobalTheory.CuspRep.pInf E (am E a) w = ((TR.pInf F a (w.comap (algebraMap F E)) : ℝ) : ℂ) := by
  have e : a.1 (w.comap (algebraMap F E)) =
      (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal (w.comap (algebraMap F E)))).symm
        (TR.pInf F a (w.comap (algebraMap F E))) :=
    ((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal (w.comap (algebraMap F E)))).symm_apply_apply _).symm
  rw [pInf_apply]
  change (InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w))
    (algebraMap (w.comap (algebraMap F E)).Completion w.Completion (a.1 (w.comap (algebraMap F E)))) = _
  rw [e]
  exact real_comp F w _

private theorem rt_δ_neg (D : Dat F E) (v : InfinitePlace F) : TR.pInf F (rt D.δ) v < 0 := by
  have h := congrFun (GlobalTheory.HilbertThetaSeries.RatPts.pInf_algebraMap F D.δ) v
  change TR.pInf F (rt D.δ) v = _ at h
  rw [h]
  exact D.neg (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v))

private theorem conj_of_sq_neg {t : ℂ} {r : ℝ} (hr : r < 0) (h : t ^ 2 = (r : ℂ)) : (starRingEnd ℂ) t = -t :=
  _root_.UpperTheory.Reformulated.B.Qh17.conj_of_sq_neg hr h

private theorem pInf_rt_conj (D : Dat F E) (w : InfinitePlace E) :
    (starRingEnd ℂ) (GlobalTheory.CuspRep.pInf E (rt D.θ) w) = -GlobalTheory.CuspRep.pInf E (rt D.θ) w := by
  refine conj_of_sq_neg (rt_δ_neg D (w.comap (algebraMap F E))) ?_
  rw [← pInf_am, ← D.rt_θ_sq, map_pow]
  rfl

private theorem pInf_bar (D : Dat F E) (x : A E) (w : InfinitePlace E) :
    GlobalTheory.CuspRep.pInf E (D.bar x) w = (starRingEnd ℂ) (GlobalTheory.CuspRep.pInf E x w) := by
  obtain ⟨u, t, rfl⟩ := D.exists_mkE x
  rw [Dat.bar_mkE, Dat.mkE_def, Dat.mkE_def]
  simp only [map_add (f := _), map_mul, map_neg, Pi.add_apply, Pi.mul_apply, Pi.neg_apply, pInf_rt_conj, pInf_am,
    TR.pInf, Complex.conj_ofReal]
  simp

private theorem pInf_norm (D : Dat F E) (z : (A E)ˣ) (w : InfinitePlace E) :
    ((TR.pInf F (ideleNorm F E z : (A F)ˣ) (w.comap (algebraMap F E)) : ℝ) : ℂ) =
      GlobalTheory.CuspRep.pInf E z w * (starRingEnd ℂ) (GlobalTheory.CuspRep.pInf E z w) := by
  rw [← pInf_am, D.am_ideleNorm, map_mul, Pi.mul_apply, pInf_bar]

private theorem fin_norm (D : Dat F E) (s : (Cinf E)ˣ) : ((ideleNorm F E (infId E s) : (A F)ˣ) : A F).2 = 1 := by
  set z : A E := (infId E s).val with hz
  have hz2 : z.2 = 1 := by
    change (1 : Af E) - 0 + 0 = 1
    simp
  have hf : am E (1 - eInf F) = ((0, 1) : A E) := by
    rw [map_sub, map_one]
    have h1 : (am E (eInf F)).1 = 1 := by
      rw [AdeleBaseChange.adeleMap_apply, show (eInf F).1 = 1 from rfl, map_one]
    have h2 : (am E (eInf F)).2 = 0 := by
      rw [AdeleBaseChange.adeleMap_apply, show (eInf F).2 = 0 from rfl, map_zero]
    exact Prod.ext (by change (1 : InfiniteAdeleRing E) - (am E (eInf F)).1 = 0; rw [h1]; simp)
      (by change (1 : FiniteAdeleRing (𝓞 E) E) - (am E (eInf F)).2 = 1; rw [h2]; simp)
  have hfz : am E (1 - eInf F) * z = am E (1 - eInf F) := by
    rw [hf]
    exact Prod.ext (zero_mul _) (by change (1 : FiniteAdeleRing (𝓞 E) E) * z.2 = 1; rw [hz2, one_mul])
  have hfb : am E (1 - eInf F) * D.bar z = am E (1 - eInf F) := by
    have := congrArg D.bar hfz
    rwa [map_mul, D.bar_am] at this
  have key : (1 - eInf F) * ((ideleNorm F E (infId E s) : (A F)ˣ) : A F) = (1 - eInf F) * 1 := by
    apply am_injective (E := E)
    rw [map_mul, map_mul, D.am_ideleNorm, map_one, mul_one, ← hz, ← mul_assoc, hfz, hfb]
  have k1 := one_sub_eInf_mul (F := F) ((ideleNorm F E (infId E s) : (A F)ˣ) : A F)
  have k2 := one_sub_eInf_mul (F := F) 1
  exact congrArg Prod.snd (k1.symm.trans (key.trans k2))

private theorem exists_repr (D : Dat F E) (x : E) :
    ∃ a b : F, x = algebraMap F E a + algebraMap F E b * D.θ := by
  refine ⟨D.b.repr x 0, D.b.repr x 1, ?_⟩
  have h := D.b.sum_repr x
  rw [Fin.sum_univ_two, D.b0, D.b1, Algebra.smul_def, Algebra.smul_def, mul_one] at h
  exact h.symm

private theorem place_unique (D : Dat F E) {w w' : InfinitePlace E}
    (h : w.comap (algebraMap F E) = w'.comap (algebraMap F E)) : w = w' := by
  set φ : F →+* ℂ := w.embedding.comp (algebraMap F E) with hφ
  set φ' : F →+* ℂ := w'.embedding.comp (algebraMap F E) with hφ'
  have hm : InfinitePlace.mk φ = InfinitePlace.mk φ' := by
    rw [hφ, hφ', ← InfinitePlace.comap_mk, ← InfinitePlace.comap_mk, InfinitePlace.mk_embedding, InfinitePlace.mk_embedding, h]
  have hreal : ComplexEmbedding.IsReal φ := InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal _)
  have hc : ComplexEmbedding.conjugate φ = φ := ComplexEmbedding.isReal_iff.1 hreal
  have he : φ = φ' := by
    rcases InfinitePlace.mk_eq_iff.1 hm with h1 | h1
    · exact h1
    · exact hc.symm.trans h1
  have hsq : ∀ τ : E →+* ℂ, τ D.θ ^ 2 = τ (algebraMap F E D.δ) := fun τ => by rw [← map_pow, D.sq]
  have hθ : w'.embedding D.θ ^ 2 = w.embedding D.θ ^ 2 := by
    rw [hsq, hsq]
    exact (congrArg (fun f : F →+* ℂ => f D.δ) he).symm
  have hneg : (starRingEnd ℂ) (w.embedding D.θ) = -w.embedding D.θ := by
    refine conj_of_sq_neg (D.neg hreal.embedding) ?_
    rw [hsq, ComplexEmbedding.IsReal.coe_embedding_apply]
    rfl
  have hreal_val : ∀ a : F, (starRingEnd ℂ) (w.embedding (algebraMap F E a)) = w.embedding (algebraMap F E a) := fun a =>
    congrArg (fun f : F →+* ℂ => f a) hc
  rw [← InfinitePlace.mk_embedding w, ← InfinitePlace.mk_embedding w']
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hθ with h1 | h1
  · congr 1
    ext x
    obtain ⟨a, b, rfl⟩ := exists_repr D x
    have ha : ∀ c : F, w'.embedding (algebraMap F E c) = w.embedding (algebraMap F E c) := fun c =>
      (congrArg (fun f : F →+* ℂ => f c) he).symm
    simp only [map_add (f := _), map_mul, ha, h1]
  · have : ComplexEmbedding.conjugate w.embedding = w'.embedding := by
      ext x
      obtain ⟨a, b, rfl⟩ := exists_repr D x
      have ha : ∀ c : F, w'.embedding (algebraMap F E c) = w.embedding (algebraMap F E c) := fun c =>
        (congrArg (fun f : F →+* ℂ => f c) he).symm
      rw [ComplexEmbedding.conjugate_coe_eq]
      simp only [map_add (f := _), map_mul, ha, h1, hneg, hreal_val]
    rw [← this, InfinitePlace.mk_conjugate_eq]

end UpperTheory.ConvolutionTheory.R2.Ff.NI

theorem UpperTheory.ConvolutionTheory.R2.Ff.normInf :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (_D : Dat F E), NormInf F E := by
  intro F E _ _ _ _ _ _ _ D s
  haveI : Module.Finite F E := Module.Finite.of_basis D.b
  have hsurj : Function.Surjective fun w : InfinitePlace E => w.comap (algebraMap F E) :=
    InfinitePlace.comap_surjective
  let val : TR.Rinf F := fun v => ∏ w : InfinitePlace E, if w.comap (algebraMap F E) = v then ‖s.val w‖ ^ 2 else 1
  have hval : ∀ w : InfinitePlace E, val (w.comap (algebraMap F E)) = ‖s.val w‖ ^ 2 := fun w => by
    refine (Finset.prod_eq_single w (fun w' _ hw => if_neg fun e => hw (NI.place_unique D e)) (fun h => absurd (Finset.mem_univ w) h)).trans (if_pos rfl)
  have hs : ∀ w, s.val w ≠ 0 := fun w h => by
    have := congrFun s.mul_inv w
    rw [Pi.mul_apply, h, zero_mul] at this
    exact zero_ne_one this
  have hne : ∀ v, val v ≠ 0 := fun v => by
    obtain ⟨w, rfl⟩ := hsurj v
    rw [hval]
    exact pow_ne_zero 2 (norm_ne_zero_iff.2 (hs w))
  let u : (TR.Rinf F)ˣ := ⟨val, fun v => (val v)⁻¹, funext fun v => mul_inv_cancel₀ (hne v), funext fun v => inv_mul_cancel₀ (hne v)⟩
  refine ⟨u, fun v => rfl, Units.ext (TR.ad_ext ?_ ?_)⟩
  · have h1 : TR.pInf F (TR.infId F u).val = u.val := by
      change (TR.infEq F).symm (1 - TR.infEq F 1 + TR.infEq F u.val) = _
      simp
    rw [h1]
    funext v
    obtain ⟨w, rfl⟩ := hsurj v
    change _ = val _
    rw [hval]
    have h := NI.pInf_norm D (infId E s) w
    rw [NI.pInf_infId, Complex.mul_conj, Complex.normSq_eq_norm_sq] at h
    exact_mod_cast h
  · have h2 : pFin F (TR.infId F u).val = 1 := by
      change (1 : Af F) - 0 + 0 = 1
      simp
    rw [h2]
    exact NI.fin_norm D s
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.OneOf
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.oneOf :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (_D : Dat F E), OneOf F E := by
  intro F E _ _ _ _ _ _ _ D y hy
  obtain ⟨u, hu, hn⟩ := normInf F E D (Matrix.GeneralLinearGroup.det y)
  have hu1 : u = 1 := by
    refine Units.ext (funext fun v => ?_)
    rw [hu v]
    have h1 : ∀ w : InfinitePlace E, ‖(Matrix.GeneralLinearGroup.det y).val w‖ = 1 := hy
    change _ = (1 : ℝ)
    refine Finset.prod_eq_one fun w _ => ?_
    split_ifs
    · rw [h1 w, one_pow]
    · rfl
  change ideleNorm F E (Matrix.GeneralLinearGroup.det (infGL E 2 y)) = 1
  rw [det_infGL, hn, hu1, map_one]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.CenExp
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

private noncomputable def euF {F : Type} [Field F] (z : TR.Rinf F) (t : ℝ) : (TR.Rinf F)ˣ :=
  ⟨fun w => Real.exp (t * z w), fun w => Real.exp (-(t * z w)),
    funext fun w => by simp [← Real.exp_add], funext fun w => by simp [← Real.exp_add]⟩

private noncomputable def euE {E : Type} [Field E] (s : Cinf E) (t : ℝ) : (Cinf E)ˣ :=
  ⟨fun w => Complex.exp (t * s w), fun w => Complex.exp (-(t * s w)),
    funext fun w => by simp [← Complex.exp_add], funext fun w => by simp [← Complex.exp_add]⟩

private theorem inf_scalarF {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (u : (TR.Rinf F)ˣ) :
    TR.infGL F 2 (Matrix.GeneralLinearGroup.scalar (Fin 2) u) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (TR.infId F u) := by
  have h1 : TR.pInf F (TR.infId F u).val = u.val := by
    change TR.pInf F (1 - TR.sInf F 1 + TR.sInf F _) = _
    have h : ∀ x, TR.pInf F (TR.sInf F x) = x := fun x => (TR.infEq F).symm_apply_apply x
    simp [h]
  have h2 : pFin F (TR.infId F u).val = 1 := by
    change (1 : Af F) - 0 + 0 = 1
    simp
  refine TR.ga_ext ?_ ?_
  · rw [TR.pInf_infGL]
    ext i j
    by_cases e : i = j <;> simp [Matrix.diagonal_apply, e, h1]
  · rw [TR.pFin_infGL]
    ext i j
    by_cases e : i = j <;> simp [Matrix.diagonal_apply, e, h2]

private theorem inf_scalarE {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (u : (Cinf E)ˣ) :
    infGL E 2 (Matrix.GeneralLinearGroup.scalar (Fin 2) u) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (infId E u) := by
  have hd : infId E u =
      Matrix.GeneralLinearGroup.det (infGL E 1 (Matrix.GeneralLinearGroup.scalar (Fin 1) u)) := by
    rw [det_infGL]
    congr 1
    exact Units.ext (by simp)
  have h1 : pInf E (infId E u : Ideles E) = u := by
    rw [hd, ← GlobalTheory.CuspRep.det_map, pInf_infGL]
    simp
  have h2 : pFin E (infId E u : Ideles E) = 1 := by
    rw [hd, ← GlobalTheory.CuspRep.det_map, pFin_infGL]
    simp
  refine ga_ext ?_ ?_
  · rw [pInf_infGL]
    ext i j
    by_cases e : i = j <;> simp [Matrix.diagonal_apply, e, h1]
  · rw [pFin_infGL]
    ext i j
    by_cases e : i = j <;> simp [Matrix.diagonal_apply, e, h2]

private theorem ex_zE {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (s : Cinf E) (t : ℝ) :
    ex (zE s) t = Matrix.GeneralLinearGroup.scalar (Fin 2) (euE s t) := by
  apply Units.ext
  have e : t • Matrix.of (zE s) = Matrix.diagonal (fun _ : Fin 2 => t • s) := by
    ext i j w
    by_cases h : i = j <;> simp [zE, Matrix.diagonal_apply, h]
  change NormedSpace.exp (t • Matrix.of (zE s)) = _
  rw [e, Matrix.exp_diagonal]
  ext i j w
  by_cases h : i = j
  · subst h
    simp [euE, Pi.exp_def, Complex.exp_eq_exp_ℂ]
  · simp [Matrix.diagonal_apply, h]

private theorem norm_euE {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (s : Cinf E) (t : ℝ) (v : InfinitePlace F) :
    (∏ w : InfinitePlace E, if w.comap (algebraMap F E) = v then ‖(euE s t).val w‖ ^ 2 else 1) =
      (euF (trI F s) t).val v := by
  have h : ∀ w : InfinitePlace E, (if w.comap (algebraMap F E) = v then ‖(euE s t).val w‖ ^ 2 else 1) =
      Real.exp (t * if w.comap (algebraMap F E) = v then 2 * (s w).re else 0) := by
    intro w
    split_ifs
    · change ‖Complex.exp (t * s w)‖ ^ 2 = _
      rw [Complex.norm_exp, ← Real.exp_nat_mul]
      simp
      ring_nf
    · simp
  simp only [h]
  rw [← Real.exp_sum, ← Finset.mul_sum]
  rfl

theorem UpperTheory.ConvolutionTheory.R2.Ff.cenExp :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (_D : Dat F E), CenExp F E := by
  intro F E _ _ _ _ _ _ _ D s
  refine ⟨fun t => infId E (euE s t), fun t => Matrix.GeneralLinearGroup.scalar (Fin 2) (euF (trI F s) t),
    ⟨fun a b => ?_, ?_⟩, fun t => ⟨?_, ?_⟩⟩
  · have h : euF (trI F s) (a + b) = euF (trI F s) a * euF (trI F s) b := by
      refine Units.ext (funext fun w => ?_)
      change Real.exp ((a + b) * _) = Real.exp (a * _) * Real.exp (b * _)
      rw [add_mul, Real.exp_add]
    change Matrix.GeneralLinearGroup.scalar (Fin 2) (euF (trI F s) (a + b)) = _
    rw [h, map_mul]
  · refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun v => ?_
    by_cases e : i = j
    · subst e
      have h : HasDerivAt (fun t : ℝ => Real.exp (t * trI F s v)) (trI F s v) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (trI F s v)).exp
      simpa [zF, euF, Matrix.diagonal_apply] using h
    · simpa [zF, Matrix.diagonal_apply, e] using hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · rw [ex_zE, inf_scalarE]
  · obtain ⟨u, hu, hn⟩ := normInf F E D (euE s t)
    have e : u = euF (trI F s) t := Units.ext (funext fun v => by rw [hu, norm_euE])
    rw [hn, e, inf_scalarF]
end
