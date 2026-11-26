module

public import Development.AutomorphicArithmetic.WhittakerHecke.WhittakerUnipotentTranslateOfInfiniteComponentZe
public import GroundTheory.AutomorphicForms.GL2.GJGlobalLattice

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.WhittakerFunctionContinuousBoundedEquivariant
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private theorem compact_cover_fundamental_domain : ∃ C : Set (Fin 2 → A ℚ), IsCompact C ∧ FS2 ℚ ⊆ C := by
  obtain ⟨C, hC, hs⟩ := UpperTheory.ConvolutionTheory.R2.Pp.exists_cpt (F := ℚ)
  exact ⟨Set.univ.pi fun _ : Fin 2 => C, isCompact_univ_pi fun _ => hC, Set.pi_mono fun _ _ => hs⟩

private theorem cont_nE {E : Type} [Field E] [NumberField E] (D : Dat ℚ E) :
    Continuous (nE D : (Fin 2 → A ℚ) → GL (Fin 2) (A E)) :=
  UpperTheory.ConvolutionTheory.R2.Pp.cont_n.comp (D.continuous_mkE' (continuous_apply 0) (continuous_apply 1))

theorem UpperTheory.whittakerFunction_continuous_bounded_equivariant :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (ω : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ), admitted D ω φ →
        Continuous (Wo D φ) ∧ (∃ B : ℝ, ∀ h, ‖Wo D φ h‖ ≤ B) ∧
        (∀ (u : Fin 2 → A ℚ) h, Wo D φ (nE D u * h) = ψ (-(u 1)) * Wo D φ h) ∧
        (∀ z h, Wo D φ (Matrix.GeneralLinearGroup.scalar (Fin 2) z * h) = ((ω.1 (ideleNorm ℚ E z) : ℂˣ) : ℂ) * Wo D φ h) := by
  intro E _ _ D ω φ hφ
  obtain ⟨B, hB⟩ := hφ.bdd
  refine ⟨?_, ⟨B, fun h => (UpperTheory.whittakerPeriod_add_smul_and_norm_le E D).2.2 φ B h hB⟩,
    fun u h => UpperTheory.whittaker_unipotent_mul_eq_additiveChar_mul E D φ ⟨hφ.cont, hφ.left⟩ u h, fun z h => ?_⟩
  · obtain ⟨C, hC, hs⟩ := compact_cover_fundamental_domain
    have e : Wo D φ = fun h => ∫ u in C, φ (nE D u * h) * ψ (u 1) ∂((adeleMeasurePi ℚ).restrict (FS2 ℚ)) := by
      funext h
      rw [Measure.restrict_restrict hC.measurableSet, Set.inter_eq_right.2 hs]
      rfl
    rw [e]
    haveI : IsFiniteMeasure ((adeleMeasurePi (ι := Fin 2) ℚ).restrict (FS2 ℚ)) :=
      ⟨by simpa using (measure_mono hs).trans_lt hC.measure_lt_top⟩
    set_option synthInstance.maxHeartbeats 200000 in
    exact continuous_parametric_integral_of_continuous
      ((hφ.cont.comp (((cont_nE D).comp continuous_snd).mul continuous_fst)).mul
        (UpperTheory.ConvolutionTheory.R2.Pp.cont_ψ.comp ((continuous_apply 1).comp continuous_snd))) hC
  · unfold Wo
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only []
    rw [← mul_assoc, ← UpperTheory.ConvolutionTheory.R2.scalar_comm, mul_assoc, hφ.cen, mul_assoc]
end

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.SchwartzBruhatRowLintegralAbsPowBounded
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal NNReal
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

private theorem abs_re (x : A ℚ) : |re x| = ‖x.1 Rat.infinitePlace‖ :=
  (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
    (IsTotallyReal.isReal Rat.infinitePlace)).norm_map_of_map_zero (map_zero _) (x.1 Rat.infinitePlace)

private theorem re_mul (x y : A ℚ) : re (x * y) = re x * re y := by
  simp [re]

private theorem re_add (x y : A ℚ) : re (x + y) = re x + re y := by
  simp [re]

private theorem re_congr {x y : A ℚ} (h : x.1 = y.1) : re x = re y := by
  unfold re
  have : TR.pInf ℚ x = TR.pInf ℚ y := by
    change (TR.infEq ℚ).symm x.1 = (TR.infEq ℚ).symm y.1
    rw [h]
  rw [this]

private theorem re_one : re (1 : A ℚ) = 1 := by
  simp [re]

private theorem row_sq {k : G1 ℚ} (hk : InfOrth k) :
    re (k 1 0) ^ 2 + re (k 1 1) ^ 2 = 1 := by
  have h := re_congr (hk 1 1)
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.one_apply_eq] at h
  rw [re_add, re_mul, re_mul, re_one] at h
  nlinarith [h]

private theorem abs_re_le_infPart (x : Fin 2 → A ℚ) (j : Fin 2) : |re (x j)| ≤ ‖infPartPi x‖ := by
  rw [abs_re]
  exact (GroundTheory.Automorphic.GJGlobal.norm_apply_le_norm_homeomorphMixedSpace _ _).trans
    (norm_le_pi_norm (infPartPi x) j)

private theorem abs_re_le {k : G1 ℚ} (hk : InfOrth k) (z : A ℚ) :
    |re z| ≤ 2 * ‖infPartPi fun j => z * row k j‖ := by
  set N := ‖infPartPi fun j => z * row k j‖ with hN
  have h0 : |re z| * |re (k 1 0)| ≤ N := by
    have h : |re (z * k 1 0)| ≤ N := abs_re_le_infPart (fun j => z * row k j) 0
    rwa [re_mul, abs_mul] at h
  have h1 : |re z| * |re (k 1 1)| ≤ N := by
    have h : |re (z * k 1 1)| ≤ N := abs_re_le_infPart (fun j => z * row k j) 1
    rwa [re_mul, abs_mul] at h
  have hs := row_sq hk
  have hz := abs_nonneg (re z)
  have ha := abs_nonneg (re (k 1 0))
  have hb := abs_nonneg (re (k 1 1))
  have hs' : |re (k 1 0)| ^ 2 + |re (k 1 1)| ^ 2 = 1 := by simpa [sq_abs] using hs
  by_contra hc
  push_neg at hc
  have hlt : |re (k 1 0)| + |re (k 1 1)| ≥ 1 := by nlinarith
  nlinarith

private theorem fin_eq {k : G1 ℚ} (z : A ℚ) :
    z.2 = (z * row k 0).2 * (-(k 0 1).2) + (z * row k 1).2 * (k 0 0).2 := by
  have hd := congrArg Prod.snd k.det_coe
  rw [Matrix.det_fin_two] at hd
  have hd' : (k 0 0).2 * (k 1 1).2 - (k 0 1).2 * (k 1 0).2 = 1 := hd
  change z.2 = (z.2 * (k 1 0).2) * (-(k 0 1).2) + (z.2 * (k 1 1).2) * (k 0 0).2
  linear_combination (-z.2) * hd'

theorem UpperTheory.schwartzBruhat_row_lintegral_abs_pow_bounded :
    ∀ Φ ∈ schwartzBruhatPi (K := ℚ) (ι := Fin 2), ∀ e : ℝ, 1 < e → ∃ C : ℝ≥0, ∀ k ∈ KK ℚ,
        ∫⁻ z : IdeleGroup ℚ, ‖Φ fun j => ((z : (A ℚ)ˣ) : A ℚ) * row k j‖ₑ * ENNReal.ofReal (ab z ^ e) ∂(ideleMeasure ℚ) ≤ C := by
  intro Φ hΦ e he
  obtain ⟨M, hM⟩ := exists_nat_gt e
  obtain ⟨C₀, hC₀, L, hL, hmaj⟩ := GroundTheory.Automorphic.GJGlobal.exists_majorant_pi hΦ M
  set O : Set (FiniteAdeleRing (𝓞 ℚ) ℚ) := ↑(integralFiniteAdeles (𝓞 ℚ) ℚ) with hO
  have hOc : IsCompact O := isCompact_integralFiniteAdeles ℚ
  set K' : Set (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
    (fun p : (Fin 2 → FiniteAdeleRing (𝓞 ℚ) ℚ) × FiniteAdeleRing (𝓞 ℚ) ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ =>
      p.1 0 * p.2.1 + p.1 1 * p.2.2) '' (L ×ˢ (O ×ˢ O)) with hK'
  have hK'c : IsCompact K' := (hL.prod (hOc.prod hOc)).image (by fun_prop)
  have hI := UpperTheory.lintegral_idele_rat_polyDecay_mul_norm_rpow_lt_top K' hK'c e he M hM
  set I : ℝ≥0∞ := ∫⁻ y : IdeleGroup ℚ, (if (y : A ℚ).2 ∈ K' then
    ENNReal.ofReal (((1 + |re (y : A ℚ)|) ^ M)⁻¹ * ab y ^ e) else 0) ∂(ideleMeasure ℚ) with hIdef
  refine ⟨(ENNReal.ofReal (C₀ * 2 ^ M) * I).toNNReal, fun k hk => ?_⟩
  rw [ENNReal.coe_toNNReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hI.ne), hIdef,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun z => ?_
  have hab : 0 ≤ ab z ^ e := by
    have : 0 < ab z := (IdeleGroup.ideleModule ℚ z).2
    positivity
  set x : Fin 2 → A ℚ := fun j => ((z : (A ℚ)ˣ) : A ℚ) * row k j with hx
  have hm := hmaj x
  by_cases hxL : finPartPi x ∈ L
  · rw [Set.indicator_of_mem hxL, mul_one] at hm
    have hmem : ((z : (A ℚ)ˣ) : A ℚ).2 ∈ K' := by
      refine ⟨(finPartPi x, -(k 0 1).2, (k 0 0).2), ⟨hxL, ?_, ?_⟩, (fin_eq _).symm⟩
      · exact Subring.neg_mem _ (mem_integralFiniteAdeles.2 fun v => hk.2 v 0 1)
      · exact mem_integralFiniteAdeles.2 fun v => hk.2 v 0 0
    rw [if_pos hmem, ← ENNReal.ofReal_mul (by positivity)]
    rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul (norm_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hle := abs_re_le hk.1 ((z : (A ℚ)ˣ) : A ℚ)
    set N := ‖infPartPi x‖ with hN
    have hN0 : 0 ≤ N := norm_nonneg _
    have hpow : (1 + |re ((z : (A ℚ)ˣ) : A ℚ)|) ^ M ≤ 2 ^ M * (1 + N) ^ M := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith) M
    have hinv : ((1 + N) ^ M)⁻¹ ≤ 2 ^ M * ((1 + |re ((z : (A ℚ)ˣ) : A ℚ)|) ^ M)⁻¹ := by
      rw [inv_le_comm₀ (by positivity) (by positivity), mul_inv, inv_inv, inv_mul_le_iff₀ (by positivity)]
      exact hpow
    calc ‖Φ x‖ * ab z ^ e ≤ (C₀ * ((1 + N) ^ M)⁻¹) * ab z ^ e :=
          mul_le_mul_of_nonneg_right hm hab
      _ ≤ (C₀ * (2 ^ M * ((1 + |re ((z : (A ℚ)ˣ) : A ℚ)|) ^ M)⁻¹)) * ab z ^ e :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hinv hC₀) hab
      _ = C₀ * 2 ^ M * (((1 + |re ((z : (A ℚ)ˣ) : A ℚ)|) ^ M)⁻¹ * ab z ^ e) := by ring
  · rw [Set.indicator_of_notMem hxL, mul_zero] at hm
    have h0 : Φ x = 0 := norm_le_zero_iff.1 hm
    simp [h0]
end

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.WhittakerCoeffLieDerivUnipotentEqMul
section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.StandardAddCharNegArchimedeanRat
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

theorem UpperTheory.standardAddChar_neg_archimedean_rat :
    ∀ x : ℝ, ψ (-(TR.sInf ℚ fun _ => x)) = Complex.exp (2 * Real.pi * Complex.I * x) := by
  intro x
  have hu : Nonempty (InfinitePlace ℚ) := inferInstance
  obtain ⟨w⟩ := hu
  have huniq : ∀ v : InfinitePlace ℚ, v = w := fun v => Subsingleton.elim v w
  have hreal : InfinitePlace.IsReal w := IsTotallyReal.isReal w
  have h : adelicChar ℚ (TR.sInf ℚ fun _ => x) = Real.fourierChar (-x) := by
    have e : TR.sInf ℚ (fun _ => x) = infiniteAdeleInl (TR.infEq ℚ fun _ => x) := rfl
    rw [e, adelicChar_infiniteAdeleInl, Fintype.prod_eq_single w (fun v hv => absurd (huniq v) hv)]
    rw [infiniteAdelicChar_apply_of_isReal hreal]
    have e2 : InfinitePlace.Completion.extensionEmbeddingOfIsReal hreal (TR.infEq ℚ (fun _ => x) w) = x :=
      (InfinitePlace.Completion.ringEquivRealOfIsReal hreal).apply_symm_apply x
    rw [e2]
  have h2 : adelicChar ℚ (-(TR.sInf ℚ fun _ => x)) = Real.fourierChar x := by
    rw [AddChar.map_neg_eq_inv, h, AddChar.map_neg_eq_inv, inv_inv]
  have h3 : ψ (-(TR.sInf ℚ fun _ => x)) = ((adelicChar ℚ (-(TR.sInf ℚ fun _ => x)) : Circle) : ℂ) := rfl
  rw [h3, h2, Real.fourierChar_apply]
  congr 1
  push_cast
  ring
end

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.DiagonalMulArchimedeanCurveEqUnipotentMul
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

private theorem inf_const (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (c : ℝ) :
    GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := ℚ) (L := E) (TR.infEq ℚ fun _ => c) =
      infEq E fun _ => (c : ℂ) := by
  funext w
  let f : ℝ →+* w.Completion := (Pi.evalRingHom (fun w : InfinitePlace E => w.Completion) w).comp
    ((GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := ℚ) (L := E)).comp
      ((TR.infEq ℚ).toRingHom.comp (Pi.constRingHom (InfinitePlace ℚ) ℝ)))
  let g : ℝ →+* w.Completion := (Pi.evalRingHom (fun w : InfinitePlace E => w.Completion) w).comp
    ((infEq E).toRingHom.comp ((Pi.constRingHom (InfinitePlace E) ℂ).comp Complex.ofRealHom))
  have hf : Continuous f := (continuous_apply w).comp
    (GroundTheory.Global.InfinitePlace.continuous_infiniteAdeleRingMap.comp
      ((TR.continuous_infEq ℚ).comp (continuous_pi fun _ => continuous_id)))
  have hg : Continuous g := (continuous_apply w).comp
    ((continuous_infEq E).comp (continuous_pi fun _ => Complex.continuous_ofReal))
  have h := Rat.denseRange_cast (𝕜 := ℝ) |>.equalizer hf hg (funext fun q => by simp)
  exact congrFun h c

private theorem re_const (x : A ℚ) : TR.pInf ℚ x = fun _ => re x := by
  funext v
  rw [Subsingleton.elim v Rat.infinitePlace]
  rfl

private theorem pInf_adeleMap (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (x : A ℚ) :
    pInf E (AdeleBaseChange.adeleMap ℚ E x) = fun _ => (re x : ℂ) := by
  have h : x.1 = TR.infEq ℚ fun _ => re x := by
    rw [← re_const]
    exact ((TR.infEq ℚ).apply_symm_apply x.1).symm
  change (infEq E).symm (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap x.1) = _
  rw [h, inf_const, RingEquiv.symm_apply_apply]

private theorem pInf_s {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (x : Cinf E) :
    pInf E (GlobalTheory.CuspRep.sInf E x) = x := (infEq E).symm_apply_apply x

private theorem pFin_s {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (x : Cinf E) :
    pFin E (GlobalTheory.CuspRep.sInf E x) = 0 := rfl

private theorem re_s (c : ℝ) : re (TR.sInf ℚ fun _ => c) = c :=
  congrFun ((TR.infEq ℚ).symm_apply_apply fun _ => c) Rat.infinitePlace

private theorem map_n {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (g : Matrix.GeneralLinearGroup (Fin 2) R) (z : R)
    (hg : g.val = !![1, z; 0, 1]) (h : Matrix.GeneralLinearGroup (Fin 2) S) (hh : h.val = !![1, f z; 0, 1]) :
    Matrix.GeneralLinearGroup.map f g = h := by
  refine Units.ext ?_
  rw [hh]
  ext i j
  change f (g.val i j) = _
  rw [hg]
  fin_cases i <;> fin_cases j <;> simp

private theorem step1 {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (D : Dat ℚ E) (k : GL (Fin 2) (A E)) (t : ℝ) :
    k * infGL E 2 (cv D k t) = gl (nU (GlobalTheory.CuspRep.sInf E (t • thInf D))) * k := by
  refine ga_ext ?_ ?_
  · rw [map_mul, map_mul, pInf_infGL]
    have h : Matrix.GeneralLinearGroup.map (pInf E) (gl (nU (GlobalTheory.CuspRep.sInf E (t • thInf D)))) = nC (t • thInf D) :=
      map_n _ _ _ rfl _ (by rw [pInf_s]; rfl)
    rw [h]
    change kInf k * cv D k t = nC (t • thInf D) * kInf k
    simp only [cv, mul_assoc, mul_inv_cancel_left]
  · rw [map_mul, map_mul, pFin_infGL, mul_one]
    have h : Matrix.GeneralLinearGroup.map (pFin E) (gl (nU (GlobalTheory.CuspRep.sInf E (t • thInf D)))) = 1 := by
      refine map_n _ _ _ rfl _ ?_
      rw [pFin_s]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    rw [h, one_mul]

private theorem em_aE {E : Type} [Field E] [NumberField E] (y : (A ℚ)ˣ) :
    em E (aE y) = aE (Units.map (AdeleBaseChange.adeleMap ℚ E : A ℚ →* A E) y) := by
  refine Units.ext ?_
  ext i j
  change AdeleBaseChange.adeleMap ℚ E ((aE y).val i j) = _
  fin_cases i <;> fin_cases j <;> simp [aE]

private theorem step3 {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (D : Dat ℚ E) (y : (A ℚ)ˣ) (t : ℝ) :
    AdeleBaseChange.adeleMap ℚ E (y : A ℚ) * GlobalTheory.CuspRep.sInf E (t • thInf D) =
      D.mkE 0 (TR.sInf ℚ fun _ => t * re (y : A ℚ)) := by
  refine ad_ext ?_ ?_
  · rw [Dat.mkE, map_zero, zero_add, map_mul, map_mul, pInf_s, pInf_adeleMap, pInf_adeleMap, re_s]
    change _ = _ * thInf D
    funext w
    simp [Pi.mul_apply, Pi.smul_apply]
    ring
  · rw [Dat.mkE, map_zero, zero_add, map_mul, map_mul, pFin_s, mul_zero]
    have : pFin E (AdeleBaseChange.adeleMap ℚ E (TR.sInf ℚ fun _ => t * re (y : A ℚ))) = 0 :=
      map_zero (AdeleBaseChange.finiteAdeleMap ℚ E)
    rw [this, zero_mul]

theorem UpperTheory.diagonal_mul_archimedeanCurve_eq_unipotent_mul :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (D : Dat ℚ E) (y : (A ℚ)ˣ) (k : GL (Fin 2) (A E)) (t : ℝ),
        em E (aE y) * k * infGL E 2 (cv D k t) = nE D ![0, TR.sInf ℚ fun _ => t * re (y : A ℚ)] * (em E (aE y) * k) := by
  intro E _ _ _ D y k t
  have h3 := step3 D y t
  have hn : nE D ![0, TR.sInf ℚ fun _ => t * re (y : A ℚ)] =
      gl (nU (AdeleBaseChange.adeleMap ℚ E (y : A ℚ) * GlobalTheory.CuspRep.sInf E (t • thInf D))) := by
    rw [h3]
    rfl
  rw [mul_assoc, step1, hn, ← mul_assoc, ← mul_assoc, em_aE, Pp.a_n]
  rfl
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

theorem UpperTheory.whittakerCoeff_lieDeriv_unipotent_eq_mul :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (D : Dat ℚ E) (f : Sm E 2), Pp.Lf f.1 →
        (∀ X, Continuous (lie E 2 X f).1 ∧ ∃ B : ℝ, ∀ g, ‖(lie E 2 X f).1 g‖ ≤ B) → ∀ (y : (A ℚ)ˣ) (k : GL (Fin 2) (A E)),
        Wo D (lie E 2 (toL (XB D k)) f).1 (em E (aE y) * k) = (2 * Real.pi * Complex.I * (re (y : A ℚ) : ℂ)) * Wo D f.1 (em E (aE y) * k) := by
  intro E _ _ _ D f hf hl y k
  obtain ⟨c0, cadd, cd, -⟩ := UpperTheory.archimedeanConjugateCurve_oneParameterSubgroup E D k
  have h1 := UpperTheory.hasDerivAt_whittakerPeriod_oneParameter E D f (cv D k) (toL (XB D k)) (em E (aE y) * k) c0 cadd cd hf.1 (hl _).1 (hl _).2
  have e : (fun t : ℝ => Wo D f.1 (em E (aE y) * k * infGL E 2 (cv D k t))) =
      fun t : ℝ => Complex.exp (2 * Real.pi * Complex.I * ((t : ℂ) * (re (y : A ℚ) : ℂ))) * Wo D f.1 (em E (aE y) * k) := by
    funext t
    rw [UpperTheory.diagonal_mul_archimedeanCurve_eq_unipotent_mul, UpperTheory.whittaker_unipotent_mul_eq_additiveChar_mul E D f.1 hf]
    have e1 : (![0, TR.sInf ℚ fun _ => t * re (y : A ℚ)] : Fin 2 → A ℚ) 1 = TR.sInf ℚ fun _ => t * re (y : A ℚ) := rfl
    rw [e1, UpperTheory.standardAddChar_neg_archimedean_rat]
    push_cast
    rfl
  rw [e] at h1
  have a : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := (hasDerivAt_id (0 : ℝ)).ofReal_comp
  have h2 := (((a.mul_const (re (y : A ℚ) : ℂ)).const_mul (2 * Real.pi * Complex.I)).cexp).mul_const
    (Wo D f.1 (em E (aE y) * k))
  have h3 := h1.unique h2
  rw [h3]
  simp
end

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.IntegralTsumIdeleCoveringEqConstMul
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal NNReal
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

private theorem gen {T U P Y Q : Type*} [MeasurableSpace T] [MeasurableSpace U] [MeasurableSpace P] [MeasurableSpace Y]
    [MeasurableSpace Q] [Countable Q] [MeasurableSingletonClass Q]
    (τ : Measure T) (υ : Measure U) (ν : Measure P) (μ : Measure Y) [SFinite τ] [SFinite υ] [SFinite ν] [SFinite μ]
    (f : T → U → P → Q → Y) (hf : Measurable fun x : T × U × P × Q => f x.1 x.2.1 x.2.2.1 x.2.2.2) (c : ℝ≥0)
    (hc : ∀ p, ∀ h : Y → ℝ≥0∞, Measurable h → ∫⁻ t, ∫⁻ u, ∑' α, h (f t u p α) ∂υ ∂τ = c * ∫⁻ y, h y ∂μ)
    (H : Y × P → ℂ) (hH : Measurable H) (hI : Integrable H (μ.prod ν)) :
    (∀ᵐ t ∂τ, ∀ᵐ u ∂υ, ∀ᵐ p ∂ν, Summable fun α => H (f t u p α, p)) ∧
      ∫ t, ∫ u, ∫ p, ∑' α, H (f t u p α, p) ∂ν ∂υ ∂τ = (c : ℂ) * ∫ q, H q ∂(μ.prod ν) := by
  let Ψ : T × U × P × Q → Y × P := fun x => (f x.1 x.2.1 x.2.2.1 x.2.2.2, x.2.2.1)
  have hΨ : Measurable Ψ := hf.prodMk (measurable_fst.comp (measurable_snd.comp measurable_snd))
  let m : Measure (T × U × P × Q) := τ.prod (υ.prod (ν.prod Measure.count))
  have hmap : m.map Ψ = c • μ.prod ν := by
    refine Measure.ext_of_lintegral _ fun h hh => ?_
    have hΨh : Measurable fun x => h (Ψ x) := hh.comp hΨ
    have hG : Measurable fun x : T × U × P => ∑' α, h (f x.1 x.2.1 x.2.2 α, x.2.2) :=
      Measurable.tsum fun α => hΨh.comp (f := fun x : T × U × P => (x.1, x.2.1, x.2.2, α)) (by fun_prop)
    rw [lintegral_map hh hΨ, lintegral_smul_measure, lintegral_prod _ hΨh.aemeasurable, lintegral_prod_symm _ hh.aemeasurable]
    have e1 : ∀ t, ∫⁻ y, h (Ψ (t, y)) ∂(υ.prod (ν.prod Measure.count)) =
        ∫⁻ p, ∫⁻ u, ∑' α, h (f t u p α, p) ∂υ ∂ν := by
      intro t
      have a1 : Measurable fun y : U × P × Q => h (Ψ (t, y)) := hΨh.comp measurable_prodMk_left
      have a2 : Measurable (Function.uncurry fun (u : U) (p : P) => ∑' α, h (f t u p α, p)) :=
        hG.comp (measurable_prodMk_left (x := t))
      rw [lintegral_prod _ a1.aemeasurable, ← lintegral_lintegral_swap a2.aemeasurable]
      refine lintegral_congr fun u => ?_
      have a3 : Measurable fun y : P × Q => h (Ψ (t, u, y)) := a1.comp measurable_prodMk_left
      rw [lintegral_prod _ a3.aemeasurable]
      refine lintegral_congr fun p => ?_
      rw [lintegral_count]
    simp only [e1]
    have hG2 : Measurable fun x : T × P => ∫⁻ u, ∑' α, h (f x.1 u x.2 α, x.2) ∂υ :=
      Measurable.lintegral_prod_right' (f := fun x : (T × P) × U => ∑' α, h (f x.1.1 x.2 x.1.2 α, x.1.2))
        (hG.comp (f := fun x : (T × P) × U => (x.1.1, x.2, x.1.2)) (by fun_prop))
    rw [lintegral_lintegral_swap hG2.aemeasurable]
    have e2 : ∀ p, ∫⁻ t, ∫⁻ u, ∑' α, h (f t u p α, p) ∂υ ∂τ = c * ∫⁻ y, h (y, p) ∂μ :=
      fun p => hc p (fun y => h (y, p)) (hh.comp measurable_prodMk_right)
    simp only [e2]
    rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top]
    rfl
  have hI1 : Integrable H (m.map Ψ) := by
    rw [hmap]
    exact hI.smul_measure ENNReal.coe_ne_top
  have hI2 : Integrable (fun x => H (Ψ x)) m := (integrable_map_measure hH.aestronglyMeasurable hΨ.aemeasurable).1 hI1
  have hval : ∫ x, H (Ψ x) ∂m = (c : ℂ) * ∫ q, H q ∂(μ.prod ν) := by
    rw [← integral_map hΨ.aemeasurable hH.aestronglyMeasurable, hmap, integral_smul_nnreal_measure, NNReal.smul_def,
      Complex.real_smul]
  constructor
  · filter_upwards [hI2.prod_right_ae] with t ht
    filter_upwards [ht.prod_right_ae] with u hu
    filter_upwards [hu.prod_right_ae] with p hp
    exact (integrable_count_iff.1 hp).of_norm
  · rw [← hval, integral_prod _ hI2]
    refine integral_congr_ae ?_
    filter_upwards [hI2.prod_right_ae] with t ht
    rw [integral_prod _ ht]
    refine integral_congr_ae ?_
    filter_upwards [ht.prod_right_ae] with u hu
    rw [integral_prod _ hu]
    refine integral_congr_ae ?_
    filter_upwards [hu.prod_right_ae] with p hp
    rw [integral_countable hp]
    simp [Ψ]

theorem UpperTheory.integral_tsum_ideleCovering_eq_const_mul :
    ∀ (U : UMeas) (c : ℝ≥0), (∀ h : IdeleGroup ℚ → ℝ≥0∞, Measurable h →
          ∫⁻ t : ℝ, ∫⁻ u, ∑' α : ℚˣ, h (Un.cov t u α) ∂U.υ = c * ∫⁻ y, h y ∂(ideleMeasure ℚ)) →
        ∀ (κ : Measure (G1 ℚ)) [IsProbabilityMeasure κ] (H : IdeleGroup ℚ × IdeleGroup ℚ × G1 ℚ → ℂ), Measurable H →
        Integrable H ((ideleMeasure ℚ).prod ((ideleMeasure ℚ).prod κ)) →
        (∀ᵐ t : ℝ, ∀ᵐ u ∂U.υ, ∀ᵐ p ∂((ideleMeasure ℚ).prod κ), Summable fun α : ℚˣ => H (Un.cov t u α * (p.1 * p.1)⁻¹, p)) ∧
        ∫ t : ℝ, ∫ u, ∫ p, ∑' α : ℚˣ, H (Un.cov t u α * (p.1 * p.1)⁻¹, p) ∂((ideleMeasure ℚ).prod κ) ∂U.υ =
          (c : ℂ) * ∫ q, H q ∂((ideleMeasure ℚ).prod ((ideleMeasure ℚ).prod κ)) := by
  intro U c hc κ _ H hH hI
  haveI := U.prob
  letI : MeasurableSpace ℚˣ := ⊤
  haveI : MeasurableSingletonClass ℚˣ := ⟨fun _ => trivial⟩
  haveI : Countable ℚˣ := Units.val_injective.countable
  have hiy : Measurable (fun t : ℝ => (iy (Real.exp t) : IdeleGroup ℚ)) := by
    have h : Continuous (fun t : ℝ => (iy (Real.exp t) : IdeleGroup ℚ)) := UpperTheory.realIdele_mul_abs_continuous_and_unit_abs_eq_one.2.2.1
    exact h.measurable
  have hd : Measurable (fun α : ℚˣ => (IdeleGroup.diagonal ℚ α : IdeleGroup ℚ)) := measurable_from_top
  refine gen volume U.υ ((ideleMeasure ℚ).prod κ) (ideleMeasure ℚ)
    (fun t u p α => Un.cov t u α * (p.1 * p.1)⁻¹) ?_ c ?_ H hH hI
  · have h1 : Measurable fun x : ℝ × IdeleGroup ℚ × (IdeleGroup ℚ × G1 ℚ) × ℚˣ => x.2.2.1.1 := by fun_prop
    exact (((hd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))).mul
      ((hiy.comp measurable_fst).mul (hiy.comp measurable_fst))).mul (measurable_fst.comp measurable_snd)).mul (h1.mul h1).inv
  · intro p h hh
    rw [hc (fun y => h (y * (p.1 * p.1)⁻¹)) (hh.comp (measurable_mul_const _)), lintegral_mul_right_eq_self]
end
