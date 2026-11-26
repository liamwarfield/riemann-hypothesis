module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XApply
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.InfinitesimalCharacterPullback.HasInfCharPullSub
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ArchimedeanCompact.InfEmbGrpEq
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.EqAmOfBarEq

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.OpsEx
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XEx
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.Fo

open NumberField.mixedEmbedding

private noncomputable def lin {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
    (w : InfinitePlace F) (i : Fin 4) : (Fin 4 → mixedSpace F) →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : {w : InfinitePlace F // w.IsReal} => ℝ)
      ⟨w, IsTotallyReal.isReal w⟩).comp
      ((ContinuousLinearMap.fst ℝ ({w : InfinitePlace F // w.IsReal} → ℝ)
        ({w : InfinitePlace F // w.IsComplex} → ℂ)).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => mixedSpace F) i)))

end UpperTheory.ConvolutionTheory.R2.Fo

theorem UpperTheory.ConvolutionTheory.R2.Fo.xEx :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (w : InfinitePlace F) (i : Fin 4) (φ : V4 F → ℂ), φ ∈ schwartzBruhatPi (K := F) (ι := Fin 4) → (fun v => cw w (v i) * φ v) ∈ schwartzBruhatPi (K := F) (ι := Fin 4) := by
  intro F _ _ _ w i φ hφ
  induction hφ using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨f, g, hg, rfl⟩ := hG
    have e : (fun v => cw w (v i) * schwartzBruhatTensorPi f g v) =
        schwartzBruhatTensorPi (SchwartzMap.smulLeftCLM ℂ (lin w i) f) g := by
      funext v
      simp only [schwartzBruhatTensorPi]
      rw [SchwartzMap.smulLeftCLM_apply_apply (lin w i).hasTemperateGrowth, smul_eq_mul, mul_assoc]
      congr 1
    rw [e]
    exact schwartzBruhatTensorPi_mem _ hg
  | zero =>
    have e : (fun v => cw w (v i) * (0 : V4 F → ℂ) v) = 0 := by
      funext v
      simp
    rw [e]
    exact zero_mem _
  | add G H _ _ hG hH =>
    have e : (fun v => cw w (v i) * (G + H) v) = (fun v => cw w (v i) * G v) + fun v => cw w (v i) * H v := by
      funext v
      simp [mul_add]
    rw [e]
    exact add_mem hG hH
  | smul c G _ hG =>
    have e : (fun v => cw w (v i) * (c • G) v) = c • fun v => cw w (v i) * G v := by
      funext v
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [e]
    exact Submodule.smul_mem _ c hG
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.ContinuousPlaceEmbedReal
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

private theorem infPartPi_add' {F : Type} [Field F] [NumberField F] (x y : V4 F) :
    infPartPi (x + y) = infPartPi x + infPartPi y := by
  funext j
  simp only [infPartPi, Pi.add_apply, homeomorphMixedSpace_apply]
  exact map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) (x j).1 (y j).1

private theorem placeEmbedReal_add {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (w : InfinitePlace F) (s t : ℝ) :
    at1 w (s + t) = at1 w s + at1 w t := by
  simp only [at1, Pi.single_add, map_add (f := _)]

private theorem continuous_placeEmbedReal {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (w : InfinitePlace F) :
    Continuous (at1 w : ℝ → A F) := by
  have h : Continuous fun t : ℝ => (Pi.single w t : TR.Rinf F) := by
    refine continuous_pi fun u => ?_
    by_cases hu : u = w
    · subst hu; simp only [Pi.single_eq_same]; exact continuous_id
    · simpa [Pi.single_eq_of_ne hu] using continuous_const
  exact ((TR.continuous_infEq F).comp h).prodMk continuous_const

private theorem inf_line {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (w : InfinitePlace F) (i : Fin 4)
    (v : V4 F) (t : ℝ) :
    infPartPi (v + Pi.single i (at1 w t)) = infPartPi v + t • infPartPi (Pi.single i (at1 w 1) : V4 F) := by
  let L : ℝ →+ (Fin 4 → mixedEmbedding.mixedSpace F) :=
    { toFun := fun t => infPartPi (Pi.single i (at1 w t) : V4 F)
      map_zero' := by
        have h0 : at1 w (0 : ℝ) = (0 : A F) := by simp [at1]
        rw [h0, Pi.single_zero]
        funext j
        simp only [infPartPi, Pi.zero_apply, homeomorphMixedSpace_apply]
        exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
      map_add' := fun s t => by
        rw [placeEmbedReal_add, Pi.single_add, infPartPi_add'] }
  have hL : Continuous L := by
    refine continuous_infPartPi.comp (continuous_pi fun j => ?_)
    by_cases hj : j = i
    · subst hj; simpa using continuous_placeEmbedReal w
    · simpa [Pi.single_eq_of_ne hj] using continuous_const
  have h := map_real_smul L hL t (1 : ℝ)
  rw [infPartPi_add']
  have e : t • (1 : ℝ) = t := by simp
  rw [e] at h
  exact congrArg (infPartPi v + ·) h

private theorem fin_line {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (w : InfinitePlace F) (i : Fin 4)
    (v : V4 F) (t : ℝ) : finPartPi (v + Pi.single i (at1 w t)) = finPartPi v := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp only [finPartPi, Pi.add_apply, Pi.single_eq_same]
    change (v j).2 + 0 = (v j).2
    exact add_zero _
  · simp [finPartPi, Pi.single_eq_of_ne hj]

theorem UpperTheory.ConvolutionTheory.R2.Fo.dEx :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (w : InfinitePlace F) (i : Fin 4) (φ : V4 F → ℂ), φ ∈ schwartzBruhatPi (K := F) (ι := Fin 4) →
    ∃ φ' ∈ schwartzBruhatPi (K := F) (ι := Fin 4), ∀ v, HasDerivAt (fun t : ℝ => φ (v + Pi.single i (at1 w t))) (φ' v) 0 := by
  intro F _ _ _ w i φ hφ
  induction hφ using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨f, g, hg, rfl⟩ := hG
    set e := infPartPi (Pi.single i (at1 w 1) : V4 F) with he
    refine ⟨schwartzBruhatTensorPi (LineDeriv.lineDerivOpCLM ℂ (SchwartzMap (Fin 4 → mixedEmbedding.mixedSpace F) ℂ) e f) g,
      schwartzBruhatTensorPi_mem _ hg, fun v => ?_⟩
    have hfun : (fun t : ℝ => schwartzBruhatTensorPi f g (v + Pi.single i (at1 w t))) =
        fun t : ℝ => f (infPartPi v + t • e) * g (finPartPi v) := by
      funext t
      simp only [schwartzBruhatTensorPi, inf_line, fin_line, he]
    rw [hfun]
    have hline : HasDerivAt (fun t : ℝ => infPartPi v + t • e) e 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add (infPartPi v)
    have hf : HasFDerivAt (f : (Fin 4 → mixedEmbedding.mixedSpace F) → ℂ) (fderiv ℝ f (infPartPi v))
        (infPartPi v + (0 : ℝ) • e) :=
      by
        rw [zero_smul, add_zero]
        exact (f.differentiableAt).hasFDerivAt
    have hc := (hf.comp_hasDerivAt (0 : ℝ) hline).mul_const (g (finPartPi v))
    simpa [schwartzBruhatTensorPi, LineDeriv.lineDerivOpCLM_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv] using hc
  | zero =>
    exact ⟨0, Submodule.zero_mem _, fun v => by simpa using hasDerivAt_const (0 : ℝ) (0 : ℂ)⟩
  | add G H _ _ hG hH =>
    obtain ⟨a, ha, ha'⟩ := hG
    obtain ⟨b, hb, hb'⟩ := hH
    exact ⟨a + b, Submodule.add_mem _ ha hb, fun v => (ha' v).add (hb' v)⟩
  | smul c G _ hG =>
    obtain ⟨a, ha, ha'⟩ := hG
    exact ⟨c • a, Submodule.smul_mem _ c ha, fun v => (ha' v).const_mul c⟩
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Fo.opsEx :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], Nonempty (Ops F) := by
  intro F _ _ _
  have hd : ∀ (w : InfinitePlace F) (i : Fin 4) (φ : S4 F), ∃ φ' : S4 F, ∀ v,
      HasDerivAt (fun t : ℝ => φ.1 (v + Pi.single i (at1 w t))) (φ'.1 v) 0 := by
    intro w i φ
    obtain ⟨φ', h, hs⟩ := dEx F w i φ.1 φ.2
    exact ⟨⟨φ', h⟩, hs⟩
  choose dd hdd using hd
  refine ⟨{
    x := fun w i =>
      { toFun := fun φ => ⟨fun v => cw w (v i) * φ.1 v, xEx F w i φ.1 φ.2⟩
        map_add' := fun φ ψ => by
          apply Subtype.ext
          funext v
          change cw w (v i) * (φ.1 v + ψ.1 v) = cw w (v i) * φ.1 v + cw w (v i) * ψ.1 v
          rw [mul_add]
        map_smul' := fun c φ => by
          apply Subtype.ext
          funext v
          change cw w (v i) * (c * φ.1 v) = c * (cw w (v i) * φ.1 v)
          rw [mul_left_comm] }
    d := fun w i =>
      { toFun := dd w i
        map_add' := fun φ ψ => by
          apply Subtype.ext
          funext v
          have h1 := (hdd w i φ v).add (hdd w i ψ v)
          exact (hdd w i (φ + ψ) v).unique h1
        map_smul' := fun c φ => by
          apply Subtype.ext
          funext v
          have h1 := (hdd w i φ v).const_mul c
          exact (hdd w i (c • φ) v).unique h1 }
    x_apply := fun w i φ v => rfl
    d_spec := fun w i φ v => hdd w i φ v }⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.FkBasic
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Fo.fkBasic :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (O : Ops F), (∀ N N' : Submodule ℂ (S4 F), N ≤ N' → ∀ m m', m ≤ m' → O.Fk N m ≤ O.Fk N' m') ∧
    (∀ N m w i, ∀ φ ∈ O.Fk N m, O.x w i φ ∈ O.Fk N (m + 1)) ∧
    ∀ N : Submodule ℂ (S4 F), FiniteDimensional ℂ N → ∀ m, FiniteDimensional ℂ (O.Fk N m) := by
  intro F _ _ _ O
  have hs : ∀ (N : Submodule ℂ (S4 F)) (m : ℕ),
      O.Fk N (m + 1) = O.Fk N m ⊔ ⨆ w, ⨆ i, (O.Fk N m).map (O.x w i) := fun _ _ => rfl
  refine ⟨?_, ?_, ?_⟩
  · intro N N' h m m' hm
    have h1 : ∀ k, O.Fk N k ≤ O.Fk N' k := by
      intro k
      induction k with
      | zero => exact h
      | succ k ih =>
        rw [hs, hs]
        exact sup_le_sup ih (iSup_mono fun w => iSup_mono fun i => Submodule.map_mono ih)
    have h2 : Monotone (O.Fk N') := monotone_nat_of_le_succ fun k => by
      rw [hs]; exact le_sup_left
    exact (h1 m).trans (h2 hm)
  · intro N m w i φ hφ
    rw [hs]
    refine Submodule.mem_sup_right ?_
    refine Submodule.mem_iSup_of_mem w ?_
    refine Submodule.mem_iSup_of_mem i ?_
    exact Submodule.mem_map_of_mem hφ
  · intro N hN m
    induction m with
    | zero => exact hN
    | succ k ih =>
      rw [hs]
      haveI := ih
      haveI : ∀ w : InfinitePlace F, FiniteDimensional ℂ
          (⨆ i, (O.Fk N k).map (O.x w i) : Submodule ℂ (S4 F)) := fun w =>
        Submodule.finiteDimensional_iSup _
      haveI : FiniteDimensional ℂ
          (⨆ w, ⨆ i, (O.Fk N k).map (O.x w i) : Submodule ℂ (S4 F)) :=
        Submodule.finiteDimensional_iSup _
      exact Submodule.finiteDimensional_sup _ _
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.CoordMk
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

noncomputable section

namespace UpperTheory.ConvolutionTheory.R2.Fo

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E]

private theorem continuous_coordE (τ : E →+* ℂ) : Continuous (coord τ) :=
  AddMonoidHomClass.continuous_of_bound (coord τ) 1 fun x => by
    simpa using FieldIso.norm_coord_le τ x

private theorem continuous_infEqE_symm : Continuous (GlobalTheory.CuspRep.infEq E).symm :=
  continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)

private theorem continuous_infEqF_symm : Continuous (TR.infEq F).symm :=
  continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp
      (continuous_apply w)

private theorem cw_rt (w : InfinitePlace F) (k : F) :
    cw w (rt k) = w.embedding k := by
  have h : TR.pInf F (rt k) w = InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w) k := by
    change InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)
      ((algebraMap F (A F) k).1 w) = _
    rw [AdeleRing.algebraMap_fst_apply, InfinitePlace.Completion.ringEquivRealOfIsReal_apply]
    exact InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe (IsTotallyReal.isReal w) (WithAbs.toAbs _ k)
  rw [cw, h, InfinitePlace.embedding_of_isReal_apply]

private theorem embedding_pl (τ : E →+* ℂ) (k : F) :
    (pl F τ).embedding k = τ (algebraMap F E k) := by
  have h : (pl F τ).IsReal := IsTotallyReal.isReal _
  have h' := InfinitePlace.embedding_mk_eq_of_isReal (InfinitePlace.isReal_mk_iff.1 h)
  exact RingHom.congr_fun h' k

private theorem cw_rt_pl (τ : E →+* ℂ) (k : F) : cw (pl F τ) (rt k) = τ (algebraMap F E k) := by
  rw [cw_rt, embedding_pl]

private theorem coord_adeleMap (τ : E →+* ℂ) (a : A F) :
    coord τ (pInf E (AdeleBaseChange.adeleMap F E a)) = cw (pl F τ) a := by
  have key : (fun b : InfiniteAdeleRing F =>
        coord τ ((GlobalTheory.CuspRep.infEq E).symm (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := E) b))) =
      fun b => (((TR.infEq F).symm b (pl F τ) : ℝ) : ℂ) := by
    refine (InfiniteAdeleRing.denseRange_algebraMap F).equalizer
      ((continuous_coordE τ).comp (continuous_infEqE_symm.comp
        GroundTheory.Global.InfinitePlace.continuous_infiniteAdeleRingMap))
      (Complex.continuous_ofReal.comp ((continuous_apply _).comp continuous_infEqF_symm)) (funext fun k => ?_)
    have h1 := cw_rt_pl (E := E) τ k
    have h2 := coord_algebraMap τ (algebraMap F E k)
    simp only [Function.comp_apply]
    rw [GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap_algebraMap]
    exact h2.trans h1.symm
  exact congrFun key a.1

end UpperTheory.ConvolutionTheory.R2.Fo

theorem UpperTheory.ConvolutionTheory.R2.Fo.coordMk :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E), (∀ (τ : E →+* ℂ) u t, coord τ (pInf E (D.mkE u t)) = cw (pl F τ) u + τ D.θ * cw (pl F τ) t) ∧
    (∀ τ : E →+* ℂ, τ D.θ ^ 2 = cw (pl F τ) (rt D.δ) ∧ starRingEnd ℂ (τ D.θ) = -τ D.θ ∧ τ D.θ ≠ 0) ∧
    (∀ w, cw w (rt D.δ) ≠ 0) ∧ ∀ w, ∃ τ : E →+* ℂ, pl F τ = w := by
  intro F E _ _ _ _ _ _ _ D
  have hneg : ∀ w : InfinitePlace F, ∃ r : ℝ, r < 0 ∧ cw w (rt D.δ) = r := fun w =>
    ⟨InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w) D.δ, D.neg _, by
      rw [cw_rt, InfinitePlace.embedding_of_isReal_apply]⟩
  have hsq : ∀ τ : E →+* ℂ, τ D.θ ^ 2 = cw (pl F τ) (rt D.δ) := fun τ => by
    rw [cw_rt_pl, ← map_pow, D.sq]
  refine ⟨fun τ u t => ?_, fun τ => ⟨hsq τ, ?_, ?_⟩, fun w => ?_, fun w => ?_⟩
  · rw [Dat.mkE, map_add (f := _), map_add (f := _), map_mul, map_mul, coord_adeleMap, coord_adeleMap, coord_algebraMap, mul_comm (cw _ t)]
  · obtain ⟨r, hr, e⟩ := hneg (pl F τ)
    have h := (hsq τ).trans e
    have hre := congrArg Complex.re h
    have him := congrArg Complex.im h
    simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] at hre him
    have h0 : (τ D.θ).re = 0 := by
      by_contra hc
      have : (τ D.θ).im = 0 := by
        have : (τ D.θ).re * (τ D.θ).im = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left hc
      rw [this] at hre
      nlinarith [mul_self_nonneg (τ D.θ).re]
    apply Complex.ext <;> simp [h0]
  · intro h0
    obtain ⟨r, hr, e⟩ := hneg (pl F τ)
    have h := (hsq τ).trans e
    rw [h0] at h
    have : (r : ℂ) = 0 := by simpa using h.symm
    exact hr.ne (by exact_mod_cast this)
  · obtain ⟨r, hr, e⟩ := hneg w
    rw [e]
    exact_mod_cast hr.ne
  · obtain ⟨W, hW⟩ := InfinitePlace.comap_surjective (k := F) (K := E) w
    refine ⟨W.embedding, ?_⟩
    rw [← hW]
    change InfinitePlace.mk (W.embedding.comp (algebraMap F E)) = W.comap (algebraMap F E)
    rw [← InfinitePlace.comap_mk, InfinitePlace.mk_embedding]

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.FkLe
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.VacForm
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

private theorem slice_mem {F : Type} [Field F] [NumberField F] {f : V4 F → ℂ}
    (hf : f ∈ schwartzBruhatPi (K := F) (ι := Fin 4)) :
    (fun y : Fin 4 → FiniteAdeleRing (𝓞 F) F => f fun i => ((0, y i) : A F)) ∈
      finiteSchwartzBruhatPi F (ι := Fin 4) := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, g, hg, rfl⟩ := hx
    have e : (fun y : Fin 4 → FiniteAdeleRing (𝓞 F) F =>
        schwartzBruhatTensorPi p g fun i => ((0, y i) : A F)) =
        p (infPartPi fun _ : Fin 4 => (0 : A F)) • g := by
      funext y
      rfl
    rw [e]
    exact Submodule.smul_mem _ _ hg
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul c x _ hx => exact Submodule.smul_mem _ c hx

private theorem gauss_fin {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (δ : F)
    (y : Fin 4 → FiniteAdeleRing (𝓞 F) F) : gauss δ (fun i => ((0, y i) : A F)) = 1 := by
  have key : ∀ a : V4 F, (∀ i, TR.pInf F (a i) = 0) → gauss δ a = 1 := fun a h => by
    simp only [gauss, map_add (f := _), map_sub, map_mul, map_pow, h]
    simp
  exact key _ fun i => map_zero (TR.infEq F).symm

theorem UpperTheory.ConvolutionTheory.R2.Fo.vacForm :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (δ : F), ∀ φ ∈ Vac δ, ∃ g ∈ finiteSchwartzBruhatPi F (ι := Fin 4), φ.1 = fun v => gauss δ v * g (finPartPi v) := by
  intro F _ _ _ δ φ hφ
  refine ⟨_, slice_mem φ.2, funext fun v => ?_⟩
  have h := hφ v (fun i => ((0, (v i).2) : A F)) rfl
  rw [gauss_fin, mul_one] at h
  rw [h, mul_comm]
  rfl
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Fo.fkLe :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (δ : F) (O : Ops F), (∀ w i, ∀ φ ∈ Fock δ, O.x w i φ ∈ Fock δ) ∧ ∀ N ≤ Vac δ, ∀ m, O.Fk N m ≤ Fock δ := by
  intro F _ _ _ δ O
  have hF : ∀ φ : S4 F, (φ : V4 F → ℂ) ∈ Submodule.span ℂ {φ : V4 F → ℂ | ∃ p ∈ polyFn (F := F),
        ∃ g ∈ finiteSchwartzBruhatPi F (ι := Fin 4), φ = fun v => p v * gauss δ v * g (finPartPi v)} → φ ∈ Fock δ := fun _ h => h
  have hx : ∀ w i, ∀ φ ∈ Fock δ, O.x w i φ ∈ Fock δ := by
    intro w i φ hφ
    have hc : (fun v : V4 F => cw w (v i)) ∈ polyFn (F := F) :=
      Algebra.subset_adjoin ⟨i, w, rfl⟩
    have key : ∀ f : V4 F → ℂ, f ∈ Submodule.span ℂ {φ : V4 F → ℂ | ∃ p ∈ polyFn (F := F),
        ∃ g ∈ finiteSchwartzBruhatPi F (ι := Fin 4), φ = fun v => p v * gauss δ v * g (finPartPi v)} →
        (fun v => cw w (v i) * f v) ∈ Submodule.span ℂ {φ : V4 F → ℂ | ∃ p ∈ polyFn (F := F),
        ∃ g ∈ finiteSchwartzBruhatPi F (ι := Fin 4), φ = fun v => p v * gauss δ v * g (finPartPi v)} := by
      intro f hf
      induction hf using Submodule.span_induction with
      | mem f hf =>
        obtain ⟨p, hp, g, hg, rfl⟩ := hf
        refine Submodule.subset_span ⟨(fun v : V4 F => cw w (v i)) * p, mul_mem hc hp, g, hg, ?_⟩
        funext v
        simp only [Pi.mul_apply]
        ring
      | zero =>
        have : (fun v : V4 F => cw w (v i) * (0 : V4 F → ℂ) v) = 0 := by
          funext v
          simp
        rw [this]
        exact Submodule.zero_mem _
      | add a b _ _ ha hb =>
        have : (fun v : V4 F => cw w (v i) * (a + b) v) =
            (fun v => cw w (v i) * a v) + fun v => cw w (v i) * b v := by
          funext v
          simp only [Pi.add_apply]
          ring
        rw [this]
        exact Submodule.add_mem _ ha hb
      | smul c a _ ha =>
        have : (fun v : V4 F => cw w (v i) * (c • a) v) = c • fun v => cw w (v i) * a v := by
          funext v
          simp only [Pi.smul_apply, smul_eq_mul]
          ring
        rw [this]
        exact Submodule.smul_mem _ c ha
    have hφ' := key φ.1 hφ
    have e : ((O.x w i φ : S4 F) : V4 F → ℂ) = fun v => cw w (v i) * φ.1 v := by
      funext v
      exact O.x_apply w i φ v
    apply hF
    rw [e]
    exact hφ'
  refine ⟨hx, fun N hN m => ?_⟩
  have hvac : Vac δ ≤ Fock δ := by
    intro φ hφ
    obtain ⟨g, hg, e⟩ := vacForm F δ φ hφ
    apply hF
    refine Submodule.subset_span ⟨1, one_mem _, g, hg, ?_⟩
    rw [e]
    funext v
    simp
  induction m with
  | zero => exact hN.trans hvac
  | succ m ih =>
    refine sup_le ih (iSup_le fun w => iSup_le fun i => ?_)
    rintro _ ⟨φ, hφ, rfl⟩
    exact hx w i φ (ih hφ)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.HermAct
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.Fo.HermitianActionFixed

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E)

private noncomputable def st (X : Matrix (Fin 2) (Fin 2) (A E)) : Matrix (Fin 2) (Fin 2) (A E) := (X.map D.bar)ᵀ

private theorem st_mul (X Y : Matrix (Fin 2) (Fin 2) (A E)) : st D (X * Y) = st D Y * st D X := by
  simp only [st, Matrix.map_mul, Matrix.transpose_mul]

private theorem st_st (X : Matrix (Fin 2) (Fin 2) (A E)) : st D (st D X) = X := by
  ext i j
  simp [st]

private theorem st_herm (v : V4 F) : st D (D.herm v) = D.herm v := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [st, Dat.herm, Dat.bar_mkE]

private theorem mkE_of_fixed {z : A E} (h : D.bar z = z) : D.mkE (D.co z 0) 0 = z := by
  rw [D.mkE_base]
  exact (D.eq_am_of_bar_eq h).symm

private theorem herm_unherm {X : Matrix (Fin 2) (Fin 2) (A E)} (h : st D X = X) :
    D.herm (D.unherm X) = X := by
  have e : ∀ i j, D.bar (X j i) = X i j := fun i j => congrFun (congrFun h i) j
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [Dat.herm, Dat.unherm] using mkE_of_fixed D (e 0 0)
  · simpa [Dat.herm, Dat.unherm] using D.mkE_co (X 0 1)
  · have := D.bar_mkE (D.co (X 0 1) 0) (D.co (X 0 1) 1)
    rw [D.mkE_co, e] at this
    simpa [Dat.herm, Dat.unherm] using this.symm
  · simpa [Dat.herm, Dat.unherm] using mkE_of_fixed D (e 1 1)

private noncomputable def eps (K : Type) [Field K] [NumberField K] : A K := (0, 1)

private theorem eps_mul_snd (a : A F) : (eps F * a).2 = a.2 := one_mul _

private theorem am_eps : am E (eps F) = eps E := by
  refine Prod.ext ?_ ?_
  · exact map_zero (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := E))
  · exact map_one (AdeleBaseChange.finiteAdeleMap F E)

end UpperTheory.ConvolutionTheory.R2.Fo.HermitianActionFixed

open UpperTheory.ConvolutionTheory.R2.Fo.HermitianActionFixed in
theorem UpperTheory.ConvolutionTheory.R2.Fo.hermAct :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E), (∀ h v, D.herm (D.act h v) = h.val * D.herm v * (h.val.map D.bar)ᵀ) ∧ (∀ u t, D.bar (D.mkE u t) = D.mkE u (-t)) ∧
    (∀ z, D.mkE (D.co z 0) (D.co z 1) = z) ∧ ∀ u t : A F, (D.mkE u t).2 = 0 → u.2 = 0 ∧ t.2 = 0 := by
  intro F E _ _ _ _ _ _ _ D
  refine ⟨fun h v => ?_, D.bar_mkE, D.mkE_co, fun u t h0 => ?_⟩
  · change D.herm (D.unherm (h.val * D.herm v * st D h.val)) = h.val * D.herm v * st D h.val
    apply herm_unherm
    rw [st_mul, st_mul, st_st, st_herm, mul_assoc]
  · have h1 : D.mkE (eps F * u) (eps F * t) = D.mkE 0 0 := by
      rw [← D.am_mul_mkE, am_eps, D.mkE_zero]
      refine Prod.ext (zero_mul _) ?_
      rw [eps_mul_snd, h0]
      rfl
    obtain ⟨hu, ht⟩ := D.mkE_inj h1
    exact ⟨(eps_mul_snd u).symm.trans (congrArg Prod.snd hu), (eps_mul_snd t).symm.trans (congrArg Prod.snd ht)⟩
end
