module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.IsClosedEmbeddingSlVal
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.ThetaIntegralExistsBilinear
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.FixTr

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.NonzeroPlacesInvariant
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

private theorem diagonal_mul_gl_conj {F : Type} [Field F] [NumberField F] (t : (A F)ˣ) (g : G1 F) :
    dM t * gl g = gl (cD t g) * dM t := by
  apply Units.ext
  ext i j
  have h1 : (t : A F) * ((t⁻¹ : (A F)ˣ) : A F) = 1 := Units.mul_inv t
  fin_cases i <;> fin_cases j <;>
    simp [dM, cD, gl, Matrix.mul_apply, Fin.sum_univ_two, Matrix.SpecialLinearGroup.toGL, mul_assoc, h1, mul_comm]

private theorem Wf_tr {F : Type} [Field F] [NumberField F] (f : GL (Fin 2) (A F) → ℂ) (x g₀ : G1 F) (t : (A F)ˣ) :
    Wf (fun g => f (g * gl g₀)) (gl x * dM t) = Wf f (gl (x * cD t g₀) * dM t) := by
  have e : ∀ b, gl (nU b) * (gl x * dM t) * gl g₀ = gl (nU b) * (gl (x * cD t g₀) * dM t) := by
    intro b
    have hg : gl (x * cD t g₀) = gl x * gl (cD t g₀) := map_mul Matrix.SpecialLinearGroup.toGL _ _
    rw [mul_assoc, mul_assoc, diagonal_mul_gl_conj, hg, mul_assoc]
  simp only [Wf, e]

private theorem Om_tr {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] {D : Dat F E} (W : Weil D) (φ : S4 F) (h : GL (Fin 2) (A E)) (x g₀ : G1 F) :
    W.Om x (W.L h (W.Om g₀ φ)) = W.Om (x * cD (nu F h) g₀) (W.L h φ) := by
  have hL := LinearMap.congr_fun (W.comm h g₀) φ
  simp only [Module.End.mul_apply] at hL
  rw [hL, map_mul, Module.End.mul_apply]

private theorem weilLift_translate {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] {D : Dat F E} (W : Weil D) (f : GL (Fin 2) (A F) → ℂ) (φ : S4 F) (h : GL (Fin 2) (A E)) (g₀ x : G1 F) :
    w1 W (fun g => f (g * gl g₀)) (W.Om g₀ φ) h x = w1 W f φ h (x * cD (nu F h) g₀) := by
  simp only [w1]
  rw [Wf_tr, Om_tr]

theorem UpperTheory.ConvolutionTheory.R2.I.weilLift_invariance :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), ∀ f ∈ π.V, ∀ φ ∈ Fock D.δ, ∀ h (g₀ : G1 F),
      W1 W M (fun g => f.1 (g * gl g₀)) (W.Om g₀ φ) h = W1 W M f.1 φ h := by
  intro F E _ _ _ _ _ _ _ D W M π f hf φ hφ h g₀
  obtain ⟨-, -, hm, hN, hi⟩ := conv F E D W M π f hf φ hφ h
  have key : w1 W (fun g => f.1 (g * gl g₀)) (W.Om g₀ φ) h =
      fun x => w1 W f.1 φ h (x * cD (nu F h) g₀) := funext (weilLift_translate W f.1 φ h g₀)
  unfold W1
  rw [key]
  exact ((inv F M (w1 W f.1 φ h) hm hN hi).1 (cD (nu F h) g₀)).2
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.PtL
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.I.ptL :
    ∀ (F : Type) [Field F] [NumberField F] (v : P F) (a : M2 v → ℂ) (x : GLv v) (X : M2 v),
      Pt a ((x⁻¹).val * X) = ((ab (idl v (Matrix.GeneralLinearGroup.det x)) : ℝ) : ℂ) * Pt (fun m => a ((x⁻¹).val * m * (dd x).val)) X := by
  intro F _ _ v a x X
  set t : (Kv v)ˣ := Matrix.GeneralLinearGroup.det x with ht
  have htv : (t : Kv v) = (x.val).det := by
    rw [ht, Matrix.GeneralLinearGroup.val_det_apply]
  have hxx : x.val * (x⁻¹).val = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hxx' : (x⁻¹).val * x.val = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hdet : (t : Kv v) * ((x⁻¹).val).det = 1 := by
    rw [htv, ← Matrix.det_mul, hxx, Matrix.det_one]
  have htt : ((t⁻¹ : (Kv v)ˣ) : Kv v) * (t : Kv v) = 1 := Units.inv_mul t
  have htt' : (t : Kv v) * ((t⁻¹ : (Kv v)ˣ) : Kv v) = 1 := Units.mul_inv t
  let A : M2 v := (t : Kv v) • (x⁻¹).val
  let B : M2 v := ((t⁻¹ : (Kv v)ˣ) : Kv v) • x.val
  have hAB : A * B = 1 := by
    simp only [A, B, Matrix.smul_mul, Matrix.mul_smul, hxx', smul_smul, htt, one_smul]
  have hBA : B * A = 1 := by
    simp only [A, B, Matrix.smul_mul, Matrix.mul_smul, hxx, smul_smul, htt', one_smul]
  let L : (Fin 2 → Kv v) ≃ₗ[Kv v] (Fin 2 → Kv v) := Matrix.toLin'OfInv hBA hAB
  have hL : ∀ y, L y = A *ᵥ y := fun y => rfl
  have hLdet : ((LinearEquiv.det L : (Kv v)ˣ) : Kv v) = t := by
    have h1 : ((LinearEquiv.det L : (Kv v)ˣ) : Kv v) = A.det := by
      rw [LinearEquiv.coe_det]
      exact LinearMap.det_toLin' A
    rw [h1, Matrix.det_smul, Fintype.card_fin, pow_two, mul_assoc, hdet, mul_one]
  have hLu : LinearEquiv.det L = t := Units.ext hLdet
  have hmod : (((distribHaarChar (Kv v) t : NNReal) : ℝ) : ℂ) = ((ab (idl v t) : ℝ) : ℂ) := by
    rw [(UpperTheory.ConvolutionTheory.R2.I.psiLaws F v).2.2.2.2.2 t, GroundTheory.LocalField.distribHaarChar_eq_modulus]
  have hne : ((ab (idl v t) : ℝ) : ℂ) ≠ 0 := by
    rw [← hmod]
    exact_mod_cast (distribHaarChar_pos (A := Kv v) (g := t)).ne'
  haveI : (μ2 v).IsAddHaarMeasure := by
    unfold μ2
    infer_instance
  have key := GlobalTheory.DetScale.integral_comp_linearEquiv (k := Kv v) (μ2 v) L
    (fun c' => a (cols (fun i => ((x⁻¹).val * X) i 1) c') *
      ψl v (((x⁻¹).val * X) 0 0 * c' 1 - ((x⁻¹).val * X) 1 0 * c' 0))
  rw [hLu, hmod] at key
  have hpt : ∀ y : Fin 2 → Kv v,
      a ((x⁻¹).val * cols (fun i => X i 1) y * (dd x).val) * ψl v (X 0 0 * y 1 - X 1 0 * y 0) =
      a (cols (fun i => ((x⁻¹).val * X) i 1) (L y)) *
        ψl v (((x⁻¹).val * X) 0 0 * (L y) 1 - ((x⁻¹).val * X) 1 0 * (L y) 0) := by
    intro y
    have hd2 := hdet
    rw [Matrix.det_fin_two] at hd2
    have e1 : (x⁻¹).val * cols (fun i => X i 1) y * (dd x).val =
        cols (fun i => ((x⁻¹).val * X) i 1) (L y) := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [hL, A, cols, dd, dL, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mulVec, dotProduct, ← ht] <;> ring
    have e2 : X 0 0 * y 1 - X 1 0 * y 0 =
        ((x⁻¹).val * X) 0 0 * (L y) 1 - ((x⁻¹).val * X) 1 0 * (L y) 0 := by
      simp only [hL, A, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul]
      linear_combination (-(X 0 0 * y 1 - X 1 0 * y 0)) * hd2
    rw [e1, e2]
  unfold Pt
  rw [integral_congr_ae (Eventually.of_forall hpt)]
  rw [show (fun a_1 => a (cols (fun i => ((x⁻¹).val * X) i 1) (L a_1)) * ψl v (((x⁻¹).val * X) 0 0 * (L a_1) 1 - ((x⁻¹).val * X) 1 0 * (L a_1) 0)) = _ from rfl]
  rw [key, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.SgZero
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.I

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (D : Dat F E) (v : P F) (θ : Kv v)

private theorem two_ne : (2 : Kv v) ≠ 0 := by
  rw [← map_ofNat (algebraMap F (Kv v)) 2]
  exact (map_ne_zero _).2 two_ne_zero

private theorem sg_add' (x y : Kv v) : sg v (x + y) = sg v x + sg v y := (sgLaws F v).1 x y
private theorem sg_mul' (a : A F) (x : Kv v) : a * sg v x = sg v (cp v a * x) := (sgLaws F v).2.1 a x
private theorem cp_sg' (x : Kv v) : cp v (sg v x) = x := (sgLaws F v).2.2.1 x
private theorem sg_zero' : sg v (0 : Kv v) = 0 := by
  have h := sg_add' v (0 : Kv v) 0
  simpa using h
private theorem sg_neg' (x : Kv v) : sg v (-x) = -sg v x := by
  have h := sg_add' v (-x) x
  rw [neg_add_cancel, sg_zero'] at h
  exact eq_neg_of_add_eq_zero_left h.symm
private theorem sg_mm (x y : Kv v) : sg v x * sg v y = sg v (x * y) := by rw [sg_mul', cp_sg']
private theorem cp_rt' (c : F) : cp v (rt c) = algebraMap F (Kv v) c := rfl

private theorem mk_add (u t u' t' : A F) : D.mkE u t + D.mkE u' t' = D.mkE (u + u') (t + t') :=
  (mkLaws F E D).2.1 u t u' t'
private theorem mk_mul (u t u' t' : A F) :
    D.mkE u t * D.mkE u' t' = D.mkE (u * u' + rt D.δ * (t * t')) (u * t' + t * u') :=
  (mkLaws F E D).1 u t u' t'
private theorem mk_zero : D.mkE (0 : A F) 0 = 0 := by
  have h := mk_add D (0 : A F) 0 0 0
  simpa using h
private theorem mk_co (u t : A F) : D.co (D.mkE u t) = ![u, t] := (mkLaws F E D).2.2.2.1 u t

private noncomputable def sB (k : Kv v) : A E := D.mkE (sg v (k / 2)) (sg v (-(k / (2 * θ))))

variable {θ}

private theorem mk_sE (hq : θ ^ 2 = algebraMap F (Kv v) D.δ) (h0 : θ ≠ 0) (u t : A F) (k : Kv v) :
    D.mkE u t * sE D v θ k = sE D v θ ((cp v u + cp v t * θ) * k) := by
  have h2 := two_ne (F := F) v
  unfold sE
  rw [mk_mul]
  simp only [sg_mul', ← sg_add', map_mul, cp_sg', cp_rt']
  rw [← hq]
  congr 2
  · congr 1; field_simp
  · congr 1; field_simp

private theorem mk_sB (hq : θ ^ 2 = algebraMap F (Kv v) D.δ) (h0 : θ ≠ 0) (u t : A F) (k : Kv v) :
    D.mkE u t * sB D v θ k = sB D v θ ((cp v u - cp v t * θ) * k) := by
  have h2 := two_ne (F := F) v
  unfold sB
  rw [mk_mul]
  simp only [sg_mul', ← sg_add', map_mul, cp_sg', cp_rt']
  rw [← hq]
  congr 2
  · congr 1; field_simp; ring
  · congr 1; field_simp; ring

private theorem sE_mul (hq : θ ^ 2 = algebraMap F (Kv v) D.δ) (h0 : θ ≠ 0) (k k' : Kv v) :
    sE D v θ k * sE D v θ k' = sE D v θ (k * k') := by
  have h2 := two_ne (F := F) v
  have h := mk_sE D v hq h0 (sg v (k / 2)) (sg v (k / (2 * θ))) k'
  rw [cp_sg', cp_sg'] at h
  have e : (k / 2 + k / (2 * θ) * θ) * k' = k * k' := by field_simp; ring
  rw [e] at h
  exact h

private theorem sE_sB (hq : θ ^ 2 = algebraMap F (Kv v) D.δ) (h0 : θ ≠ 0) (k k' : Kv v) :
    sE D v θ k * sB D v θ k' = 0 := by
  have h2 := two_ne (F := F) v
  have h := mk_sE D v hq h0 (sg v (k' / 2)) (sg v (-(k' / (2 * θ)))) k
  rw [cp_sg', cp_sg'] at h
  have e : (k' / 2 + -(k' / (2 * θ)) * θ) * k = 0 := by field_simp; ring
  rw [e] at h
  rw [mul_comm]
  refine h.trans ?_
  unfold sE
  simp [sg_zero', mk_zero]

private theorem bar_sE (k : Kv v) : D.bar (sE D v θ k) = sB D v θ k := by
  unfold sE sB
  rw [sg_neg']
  exact (mkLaws F E D).2.2.2.2.2.1 _ _

private theorem add_pair (h0 : θ ≠ 0) (u t : A F) (k k' : Kv v) :
    D.mkE u t + sE D v θ k + sB D v θ k' =
      D.mkE (u + sg v ((k + k') / 2)) (t + sg v ((k - k') / (2 * θ))) := by
  have h2 := two_ne (F := F) v
  unfold sE sB
  rw [mk_add, mk_add, add_assoc, add_assoc, ← sg_add', ← sg_add']
  congr 3
  · ring
  · ring

private theorem herm_sE (hq : θ ^ 2 = algebraMap F (Kv v) D.δ) (h0 : θ ≠ 0) (X : V4 F) (i j : Fin 2) (k : Kv v) :
    D.herm X i j * sE D v θ k = sE D v θ (mat v θ X i j * k) := by
  fin_cases i <;> fin_cases j
  · simpa [Dat.herm, mat, sub_eq_add_neg] using mk_sE D v hq h0 (X 1) 0 k
  · simpa [Dat.herm, mat, sub_eq_add_neg] using mk_sE D v hq h0 (X 2) (X 3) k
  · simpa [Dat.herm, mat, sub_eq_add_neg] using mk_sE D v hq h0 (X 2) (-X 3) k
  · simpa [Dat.herm, mat, sub_eq_add_neg] using mk_sE D v hq h0 (X 0) 0 k

private theorem herm_sB (hq : θ ^ 2 = algebraMap F (Kv v) D.δ) (h0 : θ ≠ 0) (X : V4 F) (i j : Fin 2) (k : Kv v) :
    D.herm X i j * sB D v θ k = sB D v θ (mat v θ X j i * k) := by
  fin_cases i <;> fin_cases j
  · simpa [Dat.herm, mat, sub_eq_add_neg] using mk_sB D v hq h0 (X 1) 0 k
  · simpa [Dat.herm, mat, sub_eq_add_neg] using mk_sB D v hq h0 (X 2) (X 3) k
  · simpa [Dat.herm, mat, sub_eq_add_neg] using mk_sB D v hq h0 (X 2) (-X 3) k
  · simpa [Dat.herm, mat, sub_eq_add_neg] using mk_sB D v hq h0 (X 0) 0 k

private theorem sE_add (k l : Kv v) : sE D v θ (k + l) = sE D v θ k + sE D v θ l := by
  unfold sE
  rw [mk_add, ← sg_add', ← sg_add']
  congr 2 <;> ring

private theorem sE_sub (k l : Kv v) : sE D v θ (k - l) = sE D v θ k - sE D v θ l := by
  have h := sE_add (θ := θ) D v (k - l) l
  rw [sub_add_cancel] at h
  rw [h]
  ring

private theorem sB_add (k l : Kv v) : sB D v θ (k + l) = sB D v θ k + sB D v θ l := by
  unfold sB
  rw [mk_add, ← sg_add', ← sg_add']
  congr 2 <;> ring

private theorem act_eq {J : GLv v →* GL (Fin 2) (A E)} (hs : Splt D v θ J) (y : GLv v) (X : V4 F) (Pm : M2 v)
    (hP : Pm = (y.val - 1) * mat v θ X) :
    D.act (J y) X = ![X 0 + sg v (Pm 1 1), X 1 + sg v (Pm 0 0), X 2 + sg v ((Pm 0 1 + Pm 1 0) / 2),
      X 3 + sg v ((Pm 0 1 - Pm 1 0) / (2 * θ))] := by
  have hq := hs.sq
  have h0 := hs.ne
  have h2 := two_ne (F := F) v
  obtain ⟨N, hN⟩ : ∃ N : M2 v, N = y.val - 1 := ⟨_, rfl⟩
  rw [← hN] at hP
  have hNe : ∀ i j, y.val i j - (1 : M2 v) i j = N i j := by
    intro i j
    rw [hN]
    rfl
  obtain ⟨H, hH⟩ : ∃ H, H = D.herm X := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : Matrix (Fin 2) (Fin 2) (A E), ∀ i j, T i j = sE D v θ (N i j) :=
    ⟨fun i j => sE D v θ (N i j), fun _ _ => rfl⟩
  obtain ⟨T', hT'⟩ : ∃ T : Matrix (Fin 2) (Fin 2) (A E), ∀ i j, T i j = sB D v θ (N i j) :=
    ⟨fun i j => sB D v θ (N i j), fun _ _ => rfl⟩
  have hv : (J y).val = 1 + T := by
    ext i j
    rw [hs.val, Matrix.add_apply, hNe, hT]
  have hb : (J y).val.map D.bar = 1 + T' := by
    ext i j
    rw [Matrix.map_apply, hs.val, map_add (f := _), bar_sE, Matrix.add_apply]
    have e : D.bar ((1 : Matrix (Fin 2) (Fin 2) (A E)) i j) = (1 : Matrix (Fin 2) (Fin 2) (A E)) i j := by
      rw [Matrix.one_apply]
      split_ifs <;> simp
    rw [e, hNe, hT']
  have hz : T * H * T'ᵀ = 0 := by
    ext i j
    have z := sE_sB D v hq h0
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.zero_apply, hT, hT']
    linear_combination H 0 0 * z (N i 0) (N j 0) + H 1 0 * z (N i 1) (N j 0) +
      H 0 1 * z (N i 0) (N j 1) + H 1 1 * z (N i 1) (N j 1)
  have hTH : ∀ i j, (T * H) i j = sE D v θ (Pm i j) := by
    intro i j
    have e := fun a b k => herm_sE D v hq h0 X a b k
    rw [← hH] at e
    simp only [Matrix.mul_apply, Fin.sum_univ_two, hT]
    rw [hP, Matrix.mul_apply, Fin.sum_univ_two, sE_add, mul_comm (sE D v θ _) (H 0 j),
      mul_comm (sE D v θ _) (H 1 j), e, e, mul_comm (mat v θ X 0 j), mul_comm (mat v θ X 1 j)]
  have hHT : ∀ i j, (H * T'ᵀ) i j = sB D v θ (Pm j i) := by
    intro i j
    have e := fun a b k => herm_sB D v hq h0 X a b k
    rw [← hH] at e
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, hT']
    rw [hP, Matrix.mul_apply, Fin.sum_univ_two, sB_add, e, e, mul_comm (mat v θ X 0 i),
      mul_comm (mat v θ X 1 i)]
  have hR : (J y).val * H * ((J y).val.map D.bar)ᵀ = H + T * H + H * T'ᵀ := by
    rw [hb, hv, Matrix.transpose_add, Matrix.transpose_one]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hz, add_zero]
  have hent : ∀ i j, ((J y).val * H * ((J y).val.map D.bar)ᵀ) i j =
      H i j + sE D v θ (Pm i j) + sB D v θ (Pm j i) := by
    intro i j
    rw [hR, Matrix.add_apply, Matrix.add_apply, hTH, hHT]
  have e00 : H 0 0 = D.mkE (X 1) 0 := by rw [hH]; rfl
  have e01 : H 0 1 = D.mkE (X 2) (X 3) := by rw [hH]; rfl
  have e11 : H 1 1 = D.mkE (X 0) 0 := by rw [hH]; rfl
  have hd : ∀ a : Kv v, (a + a) / 2 = a := fun a => by
    rw [← two_mul, mul_div_cancel_left₀ _ h2]
  unfold Dat.act Dat.unherm
  rw [← hH]
  simp only [hent, e00, e01, e11, add_pair D v h0, mk_co, hd, sub_self, zero_div, sg_zero', add_zero]
  funext i
  fin_cases i <;> simp

private theorem nu_J {J : GLv v →* GL (Fin 2) (A E)} (hs : Splt D v θ J) (x : GLv v) :
    nu F (J x) = idl v (Matrix.GeneralLinearGroup.det x) := by
  have hq := hs.sq
  have h0 := hs.ne
  have h2 := two_ne (F := F) v
  obtain ⟨d, hd⟩ : ∃ d : Kv v, d = x.val.det - 1 := ⟨_, rfl⟩
  have hz : ((Matrix.GeneralLinearGroup.det (J x) : (A E)ˣ) : A E) =
      D.mkE (1 + sg v (d / 2)) (sg v (d / (2 * θ))) := by
    have h1 : D.mkE (1 + sg v (d / 2)) (sg v (d / (2 * θ))) = 1 + sE D v θ d := by
      unfold sE
      rw [← (mkLaws F E D).2.2.1, mk_add, zero_add]
    have h3 : d = (x.val 0 0 - 1) + (x.val 1 1 - 1) + (x.val 0 0 - 1) * (x.val 1 1 - 1) -
        x.val 0 1 * x.val 1 0 := by
      rw [hd, Matrix.det_fin_two]
      ring
    rw [h1, h3, sE_sub, sE_add, sE_add, ← sE_mul D v hq h0, ← sE_mul D v hq h0,
      Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
    simp only [hs.val, Matrix.one_apply_eq, ne_eq, zero_ne_one, one_ne_zero, not_false_eq_true,
      Matrix.one_apply_ne, sub_zero, zero_add]
    ring
  refine Units.ext ?_
  unfold nu
  rw [(mkLaws F E D).2.2.2.2.2.2 _ _ _ hz, (sgLaws F v).2.2.2.1,
    Matrix.GeneralLinearGroup.val_det_apply, ← hd]
  have s : sg v d = sg v (d / 2) + sg v (d / 2) := by
    rw [← sg_add', add_halves]
  have t : rt D.δ * sg v (d / (2 * θ)) ^ 2 = sg v (d / 2) ^ 2 := by
    rw [sq, sq, sg_mm, sg_mm, sg_mul', cp_rt', ← hq]
    congr 1
    field_simp
  rw [t, s]
  ring

end SlopeTestRemainingChoices

end UpperTheory.ConvolutionTheory.R2.I

theorem UpperTheory.ConvolutionTheory.R2.I.actJ :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E) (v : P F) (θ : Kv v) (J : GLv v →* GL (Fin 2) (A E)), Splt D v θ J → ∀ x,
      nu F (J x) = idl v (Matrix.GeneralLinearGroup.det x) ∧
      ∀ X, away v (D.act (J x)⁻¹ X) = away v X ∧ mat v θ (D.act (J x)⁻¹ X) = (x⁻¹).val * mat v θ X := by
  intro F E _ _ _ _ _ D v θ J hs x
  refine ⟨nu_J D v hs x, fun X => ?_⟩
  have h0 := hs.ne
  have h2 := two_ne (F := F) v
  rw [← map_inv]
  obtain ⟨Pm, hP⟩ : ∃ Pm : M2 v, Pm = ((x⁻¹).val - 1) * mat v θ X := ⟨_, rfl⟩
  rw [act_eq D v hs x⁻¹ X Pm hP]
  have aw : ∀ (a : A F) (c : Kv v), (a + sg v c) - sg v (cp v (a + sg v c)) = a - sg v (cp v a) := by
    intro a c
    rw [map_add (f := _), cp_sg', sg_add']
    ring
  refine ⟨funext fun i => ?_, ?_⟩
  · fin_cases i
    · exact aw (X 0) _
    · exact aw (X 1) _
    · exact aw (X 2) _
    · exact aw (X 3) _
  · have e : (x⁻¹).val * mat v θ X = mat v θ X + Pm := by
      rw [hP, Matrix.sub_mul, Matrix.one_mul]
      abel
    rw [e]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j
    · change cp v (X 1 + sg v (Pm 0 0)) = cp v (X 1) + Pm 0 0
      rw [map_add (f := _), cp_sg']
    · change cp v (X 2 + sg v ((Pm 0 1 + Pm 1 0) / 2)) + cp v (X 3 + sg v ((Pm 0 1 - Pm 1 0) / (2 * θ))) * θ =
        cp v (X 2) + cp v (X 3) * θ + Pm 0 1
      rw [map_add (f := _), map_add (f := _), cp_sg', cp_sg']
      field_simp
      ring
    · change cp v (X 2 + sg v ((Pm 0 1 + Pm 1 0) / 2)) - cp v (X 3 + sg v ((Pm 0 1 - Pm 1 0) / (2 * θ))) * θ =
        cp v (X 2) - cp v (X 3) * θ + Pm 1 0
      rw [map_add (f := _), map_add (f := _), cp_sg', cp_sg']
      field_simp
      ring
    · change cp v (X 0 + sg v (Pm 1 1)) = cp v (X 0) + Pm 1 1
      rw [map_add (f := _), cp_sg']
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.WeilActionUnipotentNull
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.I

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem matrix_two_by_two_congr {R : Type} {a b c d a' b' c' d' : R} (h1 : a = a') (h2 : b = b') (h3 : c = c')
    (h4 : d = d') : !![a, b; c, d] = !![a', b'; c', d'] := by
  rw [h1, h2, h3, h4]

private theorem gl_val (z : A E) : (gl (nU z)).val = !![1, z; 0, 1] := rfl

private theorem inv_nU (z : A E) : (gl (nU z))⁻¹ = gl (nU (-z)) := by
  refine inv_eq_of_mul_eq_one_right ?_
  apply Units.ext
  rw [Units.val_mul, gl_val, gl_val, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem act_entry (D : Dat F E) (z : A E) (X : V4 F) :
    (gl (nU (-z))).val * D.herm X * ((gl (nU (-z))).val.map D.bar)ᵀ =
      !![D.mkE (X 1) 0 - z * D.mkE (X 2) (-X 3) - (D.mkE (X 2) (X 3) - z * D.mkE (X 0) 0) * D.bar z,
         D.mkE (X 2) (X 3) - z * D.mkE (X 0) 0;
         D.mkE (X 2) (-X 3) - D.mkE (X 0) 0 * D.bar z, D.mkE (X 0) 0] := by
  rw [gl_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Dat.herm, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private theorem weilAction_unipotent_null (D : Dat F E) (a b : A F) (hN : a ^ 2 - rt D.δ * b ^ 2 = 0) (X : V4 F) :
    D.act (gl (nU (-D.mkE a b))) X =
      ![X 0, X 1 - 2 * (a * X 2) + 2 * (rt D.δ * (b * X 3)), X 2 - a * X 0, X 3 - b * X 0] := by
  obtain ⟨hmul, hadd, -, hco, -, hbar, -⟩ := mkLaws F E D
  have hsub : ∀ u t u' t', D.mkE u t - D.mkE u' t' = D.mkE (u - u') (t - t') := by
    intro u t u' t'
    rw [sub_eq_iff_eq_add, hadd, sub_add_cancel, sub_add_cancel]
  have e00 : D.mkE (X 1) 0 - D.mkE a b * D.mkE (X 2) (-X 3) -
      (D.mkE (X 2) (X 3) - D.mkE a b * D.mkE (X 0) 0) * D.bar (D.mkE a b) =
      D.mkE (X 1 - 2 * (a * X 2) + 2 * (rt D.δ * (b * X 3))) 0 := by
    simp only [hbar, hmul, hsub]
    congr 1
    · linear_combination (X 0) * hN
    · ring
  have e01 : D.mkE (X 2) (X 3) - D.mkE a b * D.mkE (X 0) 0 = D.mkE (X 2 - a * X 0) (X 3 - b * X 0) := by
    simp only [hmul, hsub]
    congr 1 <;> ring
  rw [Dat.act, act_entry, e00, e01]
  ext1 i
  fin_cases i
  · change D.co (D.mkE (X 0) 0) 0 = X 0
    rw [hco]; rfl
  · change D.co (D.mkE (X 1 - 2 * (a * X 2) + 2 * (rt D.δ * (b * X 3))) 0) 0 = _
    rw [hco]; rfl
  · change D.co (D.mkE (X 2 - a * X 0) (X 3 - b * X 0)) 0 = _
    rw [hco]; rfl
  · change D.co (D.mkE (X 2 - a * X 0) (X 3 - b * X 0)) 1 = _
    rw [hco]; rfl

end UpperTheory.ConvolutionTheory.R2.I

theorem UpperTheory.ConvolutionTheory.R2.I.actN :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E) (v : P F) (θ : Kv v), θ ^ 2 = algebraMap F (Kv v) D.δ → θ ≠ 0 → ∀ s,
      nu F (nbar D v θ s) = 1 ∧
      ∀ X, away v (D.act (nbar D v θ s)⁻¹ X) = away v X ∧ mat v θ (D.act (nbar D v θ s)⁻¹ X) = mat v θ X * !![1, 0; -s, 1] := by
  intro F E _ _ _ _ _ D v θ hθ hθ0 s
  obtain ⟨sadd, smul, scp, -, -, -, -, -, -, -⟩ := sgLaws F v
  have h2 : (2 : Kv v) ≠ 0 := by norm_num
  have hδ : cp v (rt D.δ) = θ ^ 2 := hθ.symm ▸ rfl
  have s0 : sg v 0 = 0 := by
    have := sadd 0 0
    rw [add_zero] at this
    exact left_eq_add.mp this
  have sneg : ∀ x, sg v (-x) = -sg v x := by
    intro x
    have := sadd x (-x)
    rw [add_neg_cancel, s0] at this
    exact eq_neg_of_add_eq_zero_right this.symm
  refine ⟨?_, fun X => ?_⟩
  · have : Matrix.GeneralLinearGroup.det (nbar D v θ s) = 1 := by
      apply Units.ext
      simp [nbar, Matrix.det_fin_two]
    rw [nu, this, map_one]
  set a := sg v (s / 2) with ha
  set b := sg v (-(s / (2 * θ))) with hb
  have hN : a ^ 2 - rt D.δ * b ^ 2 = 0 := by
    rw [pow_two, pow_two, ← mul_assoc]
    rw [ha, hb, smul, smul, smul, scp, scp, hδ, sub_eq_zero]
    congr 1
    field_simp
  let d : Fin 4 → Kv v := ![0, -(s * cp v (X 2)) - s * θ * cp v (X 3), -(s / 2 * cp v (X 0)), s / (2 * θ) * cp v (X 0)]
  have hX : D.act (nbar D v θ s)⁻¹ X = fun i => X i + sg v (d i) := by
    rw [nbar, inv_nU, weilAction_unipotent_null D a b hN X]
    ext1 i
    fin_cases i
    · simp [d, s0]
    · have e0 : d 1 = -(cp v (2 * X 2) * (s / 2)) + cp v (2 * (rt D.δ * X 3)) * (-(s / (2 * θ))) := by
        change -(s * cp v (X 2)) - s * θ * cp v (X 3) = _
        rw [map_mul, map_mul, map_mul, hδ, map_ofNat]
        field_simp
        ring
      have e1 : sg v (d 1) = -(2 * (a * X 2)) + 2 * (rt D.δ * (b * X 3)) := by
        rw [e0, sadd, sneg, ← smul, ← smul]
        ring
      change X 1 - 2 * (a * X 2) + 2 * (rt D.δ * (b * X 3)) = X 1 + sg v (d 1)
      rw [e1]
      ring
    · have e0 : d 2 = -(cp v (X 0) * (s / 2)) := by
        change -(s / 2 * cp v (X 0)) = _
        ring
      have e1 : sg v (d 2) = -(a * X 0) := by
        rw [e0, sneg, ← smul]
        ring
      change X 2 - a * X 0 = X 2 + sg v (d 2)
      rw [e1]
      ring
    · have e0 : d 3 = -(cp v (X 0) * (-(s / (2 * θ)))) := by
        change s / (2 * θ) * cp v (X 0) = _
        ring
      have e1 : sg v (d 3) = -(b * X 0) := by
        rw [e0, sneg, ← smul]
        ring
      change X 3 - b * X 0 = X 3 + sg v (d 3)
      rw [e1]
      ring
  have hcp : ∀ i, cp v (D.act (nbar D v θ s)⁻¹ X i) = cp v (X i) + d i := by
    intro i
    rw [hX]
    change cp v (X i + sg v (d i)) = _
    rw [map_add (f := _), scp]
  constructor
  · funext i
    change D.act (nbar D v θ s)⁻¹ X i - sg v (cp v (D.act (nbar D v θ s)⁻¹ X i)) = X i - sg v (cp v (X i))
    rw [hcp, sadd, hX]
    change X i + sg v (d i) - _ = _
    ring
  · simp only [mat, hcp]
    rw [Matrix.mul_fin_two]
    refine matrix_two_by_two_congr ?_ ?_ ?_ ?_
    · change cp v (X 1) + (-(s * cp v (X 2)) - s * θ * cp v (X 3)) = _
      ring
    · change cp v (X 2) + -(s / 2 * cp v (X 0)) + (cp v (X 3) + s / (2 * θ) * cp v (X 0)) * θ = _
      field_simp
      ring
    · change cp v (X 2) + -(s / 2 * cp v (X 0)) - (cp v (X 3) + s / (2 * θ) * cp v (X 0)) * θ = _
      field_simp
      ring
    · change cp v (X 0) + 0 = _
      ring
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

private noncomputable def trB {F : Type} [Field F] [NumberField F] {v : P F} (x : GLv v)
    (a : SB (M2 v)) : SB (M2 v) :=
  let e : M2 v ≃ₜ M2 v :=
    { toFun := fun m => (x⁻¹).val * m * (dd x).val
      invFun := fun m => x.val * m * ((dd x)⁻¹).val
      left_inv := fun m => by
        show x.val * ((x⁻¹).val * m * (dd x).val) * ((dd x)⁻¹).val = m
        have h1 : x.val * (x⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
        have h2 : (dd x).val * ((dd x)⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
        rw [Matrix.mul_assoc, Matrix.mul_assoc, h2, Matrix.mul_one, ← Matrix.mul_assoc, h1, Matrix.one_mul]
      right_inv := fun m => by
        show (x⁻¹).val * (x.val * m * ((dd x)⁻¹).val) * (dd x).val = m
        have h1 : (x⁻¹).val * x.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
        have h2 : ((dd x)⁻¹).val * (dd x).val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
        rw [Matrix.mul_assoc, Matrix.mul_assoc, h2, Matrix.mul_one, ← Matrix.mul_assoc, h1, Matrix.one_mul]
      continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
      continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const }
  ⟨fun m => a.1 (e m), a.2.1.comp_continuous e.continuous, a.2.2.comp_homeomorph e⟩

private theorem exT {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsTotallyReal F] (D : Dat F E) (v : P F) (θ : Kv v) (u : V4 F → ℂ) (hu : GoodU v D.δ θ u) :
    ∃ T : SB (M2 v) →ₗ[ℂ] Fock (F := F) D.δ, ∀ a, (T a).1.1 = ten v θ u (Pt a.1) := by
  obtain ⟨P, hP⟩ := UpperTheory.ConvolutionTheory.R2.I.ptMem F v
  have h : ∀ a : SB (M2 v), ∃ φ : Fock (F := F) D.δ, φ.1.1 = ten v θ u (Pt a.1) := by
    intro a
    obtain ⟨φ, hφ, e⟩ := hu (P a) (P a).2
    exact ⟨⟨φ, hφ⟩, by rw [e, hP]⟩
  choose t ht using h
  refine ⟨{ toFun := t, map_add' := ?_, map_smul' := ?_ }, ht⟩
  · intro a b
    apply Subtype.ext
    apply Subtype.ext
    show (t (a + b)).1.1 = (t a).1.1 + (t b).1.1
    rw [ht, ht, ht, ← hP, ← hP, ← hP, map_add (f := _)]
    funext X
    simp [ten, mul_add]
  · intro c a
    apply Subtype.ext
    apply Subtype.ext
    show (t (c • a)).1.1 = c • (t a).1.1
    rw [ht, ht, ← hP, ← hP, map_smul]
    funext X
    simp [ten, mul_left_comm]

private theorem L_nbar {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] {D : Dat F E} (W : Weil D) (v : P F) (θ : Kv v)
    (hθ : θ ^ 2 = algebraMap F (Kv v) D.δ) (hθ0 : θ ≠ 0) (u : V4 F → ℂ) (a a' : M2 v → ℂ) (s : Kv v)
    (ha' : ∀ m, a' m = ψl v (-(s * m.det)) * a m) (φ φ' : S4 F)
    (hφ : φ.1 = ten v θ u (Pt a)) (hφ' : φ'.1 = ten v θ u (Pt a')) :
    W.L (nbar D v θ s) φ = φ' := by
  obtain ⟨hnu, hact⟩ := UpperTheory.ConvolutionTheory.R2.I.actN F E D v θ hθ hθ0 s
  apply Subtype.ext
  funext X
  obtain ⟨e1, e2⟩ := hact X
  have hab : ab (1 : (A F)ˣ) = 1 := by simp [ab]
  have ha2 : a' = fun m => ψl v (-(s * m.det)) * a m := funext ha'
  rw [W.L_apply, hφ, hφ', hnu, hab]
  simp only [ten]
  rw [e1, e2, (UpperTheory.ConvolutionTheory.R2.I.ptN F v a (mat v θ X)).2 s, ha2]
  simp

private theorem L_J {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] {D : Dat F E} (W : Weil D) (v : P F) (θ : Kv v)
    (J : GLv v →* GL (Fin 2) (A E)) (hJ : Splt D v θ J) (u : V4 F → ℂ) (a : M2 v → ℂ) (x : GLv v)
    (φ φ' : S4 F) (hφ : φ.1 = ten v θ u (Pt a))
    (hφ' : φ'.1 = ten v θ u (Pt fun m => a ((x⁻¹).val * m * (dd x).val))) :
    W.L (J x) φ = φ' := by
  obtain ⟨hnu, hact⟩ := UpperTheory.ConvolutionTheory.R2.I.actJ F E D v θ J hJ x
  apply Subtype.ext
  funext X
  obtain ⟨e1, e2⟩ := hact X
  have hab : ((ab (idl v (Matrix.GeneralLinearGroup.det x)) : ℝ) : ℂ) ≠ 0 := by
    have : 0 < ab (idl v (Matrix.GeneralLinearGroup.det x)) := (IdeleGroup.ideleModule F _).2
    exact_mod_cast this.ne'
  rw [W.L_apply, hφ, hφ', hnu]
  simp only [ten]
  rw [e1, e2, UpperTheory.ConvolutionTheory.R2.I.ptL F v a x (mat v θ X)]
  push_cast
  field_simp

private theorem psi_nbar {F : Type} [Field F] [NumberField F] (v : P F) (s : Kv v) :
    ψ (-(2 * sg v (s / 2))) = ψl v (-s) := by
  have hadd := (sgLaws F v).1
  have h0 : sg v 0 = 0 := by
    have := hadd 0 0
    simpa using this
  have e : -(2 * sg v (s / 2)) = sg v (-s) := by
    have h1 := hadd (s / 2) (s / 2)
    have h2 := hadd s (-s)
    rw [add_neg_cancel, h0] at h2
    rw [add_halves] at h1
    rw [two_mul, ← h1]
    exact neg_eq_of_add_eq_zero_right h2.symm
  rw [e]
  exact (UpperTheory.ConvolutionTheory.R2.I.psiLaws F v).2.1 _

theorem UpperTheory.ConvolutionTheory.R2.I.keyPure :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2) (v : P F) (θ : Kv v) (J : GLv v →* GL (Fin 2) (A E)), Splt D v θ J →
      ∀ h', (∀ s, Commute h' (nbar D v θ s)) → ∀ u, Mod v θ W u → ∀ a ∈ SB (M2 v), ∀ φ : S4 F, φ.1 = ten v θ u (Pt a) →
      ∀ f ∈ π.V, (fun x => W1 W M f.1 φ (h' * J x)) ∈ MC (π.locRep v) := by
  intro F E _ _ _ _ _ _ _ D W M π v θ J hJ h' hcomm u hu a ha φ hφ f hf
  obtain ⟨hsm, hloc, -⟩ := UpperTheory.ConvolutionTheory.R2.I.locSm F π v
  obtain ⟨T, hT⟩ := exT D v θ u hu.1
  obtain ⟨B, hB⟩ := UpperTheory.ConvolutionTheory.R2.I.thetaIntegral_exists_bilinear F E D W M π h'
  have hfun : ∀ (x : GLv v) (f : π.V), (fun g => f.1.1 (g * lc v x)) = (π.locRep v x f).1.1 :=
    fun x f => funext fun g => (hloc x f g).symm
  have hyp1 : ∀ (g : SL v) f (a a' : SB (M2 v)), (∀ m, a'.1 m = a.1 (m * g.1)) →
      (B.compl₂ T) (π.locRep v (Matrix.SpecialLinearGroup.toGL g) f) a' = (B.compl₂ T) f a := by
    intro g f a a' ha'
    obtain ⟨j, hj⟩ := (jEx F v).1
    have h1 : W.Om (j g) (T a).1 = (T a').1 := by
      apply Subtype.ext
      rw [hu.2 j hj g a.1 a.2 (T a).1 (hT a), hT a']
      congr 2
      exact (funext ha').symm
    have h2 := UpperTheory.ConvolutionTheory.R2.I.weilLift_invariance F E D W M π f.1 f.2 (T a).1 (T a).2 h' (j g)
    rw [hj g, hfun, h1] at h2
    rw [LinearMap.compl₂_apply, LinearMap.compl₂_apply, hB, hB]
    exact h2
  have hyp2 : ∀ f (s : Kv v) (a a' : SB (M2 v)), (∀ m, a'.1 m = ψl v (-(s * m.det)) * a.1 m) →
      (B.compl₂ T) f a' = ψl v (-s) * (B.compl₂ T) f a := by
    intro f s a a' ha'
    have h1 := L_nbar W v θ hJ.sq hJ.ne u a.1 a'.1 s ha' (T a).1 (T a').1 (hT a) (hT a')
    have h2 := ((UpperTheory.ConvolutionTheory.R2.I.weilLift_equivariance F E D W M f.1.1 (T a).1 h').1 (nbar D v θ s))
    have h3 := ((UpperTheory.ConvolutionTheory.R2.I.weilLift_equivariance F E D W M f.1.1 (T a).1 h').2 (sg v (s / 2)) (sg v (-(s / (2 * θ)))))
    have hnu := (UpperTheory.ConvolutionTheory.R2.I.actN F E D v θ hJ.sq hJ.ne s).1
    have hd1 : dM (1 : (A F)ˣ) = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [dM]
    rw [hnu, hd1, h1] at h2
    simp only [mul_one] at h2
    rw [LinearMap.compl₂_apply, LinearMap.compl₂_apply, hB, hB, ← h2, (hcomm s).eq]
    rw [← psi_nbar]
    exact h3
  have key := UpperTheory.ConvolutionTheory.R2.I.absM F v π.V (π.locRep v) hsm (B.compl₂ T) hyp1 hyp2 ⟨f, hf⟩ ⟨a, ha⟩
    (fun x => trB x ⟨a, ha⟩) (fun x m => rfl)
  have hfin : (fun x => W1 W M f.1 φ (h' * J x)) =
      fun x => (B.compl₂ T) (π.locRep v (dd x) ⟨f, hf⟩) (trB x ⟨a, ha⟩) := by
    funext x
    have h1 := L_J W v θ J hJ u a x φ (T (trB x ⟨a, ha⟩)).1 hφ (hT _)
    have h2 := ((UpperTheory.ConvolutionTheory.R2.I.weilLift_equivariance F E D W M f.1 φ h').1 (J x))
    have h3 : dM (nu F (J x)) = lc v (dd x) := by
      rw [(UpperTheory.ConvolutionTheory.R2.I.actJ F E D v θ J hJ x).1]
      exact ((lcLaws F v).2.2.1 _).symm
    rw [h3, h1] at h2
    rw [h2, LinearMap.compl₂_apply, hB, ← hfun]
  rw [hfin]
  exact key
