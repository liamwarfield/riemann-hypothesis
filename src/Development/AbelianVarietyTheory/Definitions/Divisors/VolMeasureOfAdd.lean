module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CabsDiagEqOne
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.VolMeasureOfAdd
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField MeasureTheory Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CxPts GlobalTheory.TopForm GlobalTheory.ChartGlue
open scoped ENNReal

namespace GlobalTheory

section General

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {B L : LB Y} {O : Y.Opens}

theorem CompHS.cval_mem_fibSec (f : H0 p B O) : cval σ f ∈ fibSec p σ B := by
  refine ⟨fun i j y hi hj => ?_, fun i y h => ev_of_notMem (fun e => h (mem_ptsIn_inf.1 e).2) _⟩
  by_cases hO : y ∈ ptsIn p σ O
  · rw [cval_eq_val σ f i y hO hi, cval_eq_val σ f j y hO hj, H0.val_change y.1 i j hO hi hj]
    exact congrArg (· * _) (ev_eq (mem_ptsIn_inf.2 ⟨hi, hj⟩) _).symm
  · exact (ev_of_notMem (fun e => hO (mem_ptsIn_inf.1 e).1) _).trans
      ((mul_zero _).symm.trans (congrArg _ (ev_of_notMem (fun e => hO (mem_ptsIn_inf.1 e).1) _).symm))

namespace CompHS

def divVal (σ : k →+* ℂ) (ω : H0 p (LB.div B L) O) : (tens B (dual L)).ι → CxPts p σ → ℂ := cval σ ω

theorem divVal_mem (ω : H0 p (LB.div B L) O) : divVal σ ω ∈ fibSec p σ (tens B (dual L)) := by
  have h := cval_mem_fibSec (σ := σ) ω
  refine ⟨fun i j y hi hj => (h.1 i j y hi hj).trans (congrArg (· * _) ?_), h.2⟩
  have hy := mem_ptsIn_inf.2 ⟨hi, hj⟩
  exact (ev_mul _ _ y).trans (Eq.trans (congrArg (_ * ·) ((ev_inv hy _).trans (Eq.symm ((ev_res _ hy _).trans
    ((ev_inv (mem_ptsIn_inf.2 ⟨(mem_ptsIn_inf.1 hi).2, (mem_ptsIn_inf.1 hj).2⟩) _).trans
      (congrArg (·⁻¹) (ev_res _ hy _).symm)))))) (ev_mul _ _ y).symm)

variable {D : ℕ} [SmoothOfRelativeDimension D p] (K : CanonLB p D) (φ φ' : Weight p σ L)
  (ω : H0 p (LB.div K.bundle L) O)

def volDens (a : AlgChart p σ D) (y : CxPts p σ) : ℝ := a.topDens K φ.dual (divVal σ ω) y

def volMeasure : Measure (CxPts p σ) :=
  ((AnRead.all p σ D).topMeasure K φ.dual (divVal σ ω)).restrict (ptsIn p σ O)

variable {φ φ'}

theorem volDens_eq (a : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ a.e.source) {i : K.bundle.ι} {j : L.ι}
    (hi : y ∈ ptsIn p σ (K.bundle.U i)) (hj : y ∈ ptsIn p σ (L.U j)) : volDens K φ ω a y =
      2 ^ D * (‖rv σ a.isFrame (K.isFrame i) y * cval σ ω (i, j) y‖ ^ 2 / Real.exp (-φ.φ j y)) := by
  rw [volDens, a.topDens_eq K φ.dual (divVal_mem ω) hy hi (b := j) hj, div_eq_mul_inv, ← Real.exp_neg]
  rfl

theorem volDens_pos (hω : NowhereZero ω) (a : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ a.e.source)
    (hO : y ∈ ptsIn p σ O) : 0 < volDens K φ ω a y := by
  have hi := mem_pick K.isLB y
  have hj := mem_pick φ.isLB y
  have hm : y ∈ ptsIn p σ (O ⊓ (LB.div K.bundle L).U (_, _)) := mem_ptsIn_inf.2 ⟨hO, mem_ptsIn_inf.2 ⟨hi, hj⟩⟩
  have h₁ : cval σ ω (_, _) y ≠ 0 := (mem_ptsIn_basicOpen hm _).1 (mem_ptsIn.2
    ((Y.mem_basicOpen _ _ (mem_ptsIn.1 hm)).2 (hω _ (mem_ptsIn.1 hm).1 _ (mem_ptsIn.1 hm).2)))
  have h₂ := mul_ne_zero (rv_ne_zero a.isFrame (K.isFrame _) (a.source_subset hy) hi) h₁
  rw [volDens_eq K ω a hy hi hj]
  exact mul_pos (by positivity) (div_pos (pow_pos (norm_pos_iff.2 h₂) _) (Real.exp_pos _))

variable [SecondCountableTopology (CxPts p σ)]

theorem volMeasure_apply (a : AlgChart p σ D) {A : Set (CxPts p σ)} (hA : MeasurableSet A) (h : A ⊆ a.e.source) :
    volMeasure K φ ω A = ∫⁻ v in a.e '' (A ∩ ptsIn p σ O), ENNReal.ofReal (volDens K φ ω a (a.e.symm v)) := by
  rw [volMeasure, Measure.restrict_apply hA]
  exact (AnRead.all p σ D).topMeasure_apply K _ _ a (hA.inter (isOpen_ptsIn O).measurableSet) (inter_subset_left.trans h)

theorem volMeasure_of_add {s : ℝ} (h : ∀ j, ∀ y ∈ ptsIn p σ O, y ∈ ptsIn p σ (L.U j) → φ'.φ j y = φ.φ j y + s) :
    volMeasure K φ' ω = ENNReal.ofReal (Real.exp s) • volMeasure K φ ω := by
  refine ext_of_cover _ (fun a : AlgChart p σ D => a.e.open_source) AlgChart.exists_mem_source fun a A hA hs => ?_
  have hA' := hA.inter (isOpen_ptsIn (p := p) (σ := σ) O).measurableSet
  rw [smul_apply, volMeasure_apply K ω a hA hs, volMeasure_apply K ω a hA hs, smul_eq_mul,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun (measurableSet_image a.e hA' (inter_subset_left.trans hs)) ?_
  rintro _ ⟨y, hy, rfl⟩
  have hi := mem_pick K.isLB y
  have hj := mem_pick φ.isLB y
  simp only [a.e.left_inv (hs hy.1)]
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, volDens_eq K ω a (hs hy.1) hi hj, volDens_eq K ω a (hs hy.1) hi hj,
    h _ y hy.2 hj, neg_add, Real.exp_add, Real.exp_neg s]
  congr 1
  field_simp

theorem volMeasure_pos (hω : NowhereZero ω) (hφ : ∀ j, ContinuousOn (φ.φ j) (ptsIn p σ O ∩ ptsIn p σ (L.U j)))
    {y : CxPts p σ} (hy : y ∈ ptsIn p σ O) : 0 < volMeasure K φ ω univ := by
  obtain ⟨a, ha⟩ := AlgChart.exists_mem_source (D := D) y
  have hi := mem_pick K.isLB y
  have hj := mem_pick φ.isLB y
  set i := pick K.isLB y
  set j := pick φ.isLB y
  let S := a.e.source ∩ (ptsIn p σ (a.U ⊓ K.bundle.U i) ∩ ptsIn p σ (O ⊓ (LB.div K.bundle L).U (i, j)))
  have hS : IsOpen S := a.e.open_source.inter ((isOpen_ptsIn _).inter (isOpen_ptsIn _))
  have hO : S ⊆ ptsIn p σ O := fun z hz => (mem_ptsIn_inf.1 hz.2.2).1
  have hL : S ⊆ ptsIn p σ (L.U j) := fun z hz => (mem_ptsIn_inf.1 (mem_ptsIn_inf.1 hz.2.2).2).2
  have hc : ContinuousOn (volDens K φ ω a) S := (continuousOn_const.mul
    (((((continuousOn_ev _).mono (t := S) fun _ hz => hz.2.1).mul
      ((continuousOn_ev _).mono (t := S) fun _ hz => hz.2.2)).norm.pow 2).div
      ((hφ j).mono (subset_inter hO hL)).neg.rexp fun _ _ => (Real.exp_pos _).ne')).congr
    fun z hz => volDens_eq K ω a hz.1 (mem_ptsIn_inf.1 hz.2.1).2 (hL hz)
  have ho := a.e.isOpen_image_of_subset_source hS inter_subset_left
  have hm : MapsTo a.e.symm (a.e '' S) S := by
    rintro _ ⟨z, hz, rfl⟩
    rwa [a.e.left_inv hz.1]
  have hc' := ENNReal.continuous_ofReal.comp_continuousOn (hc.comp (a.e.continuousOn_symm.mono (t := a.e '' S)
    (image_subset_iff.2 fun _ hz => a.e.map_source hz.1)) hm)
  refine lt_of_lt_of_le ?_ (measure_mono (subset_univ S))
  rw [volMeasure_apply K ω a hS.measurableSet inter_subset_left, inter_eq_left.2 hO, pos_iff_ne_zero]
  intro h
  have h₁ := (ae_restrict_iff' ho.measurableSet).1 ((lintegral_eq_zero_iff' (hc'.aemeasurable ho.measurableSet)).1 h)
  refine (ho.measure_pos volume ⟨_, y, ⟨ha, mem_ptsIn_inf.2 ⟨a.source_subset ha, hi⟩,
    mem_ptsIn_inf.2 ⟨hy, mem_ptsIn_inf.2 ⟨hi, hj⟩⟩⟩, rfl⟩).ne' (measure_mono_null ?_ (ae_iff.1 h₁))
  exact fun v hv hh => (ENNReal.ofReal_pos.2 (volDens_pos K ω hω a (hm hv).1 (hO (hm hv)))).ne' (hh hv)

end CompHS

end General

namespace CompHS

open ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.AllWt (exOf wtOf lieFacZ modelWt homN)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

section Good

variable {Y T : Scheme.{0}} {p : Y ⟶ Sp c.F} {σ σ' : c.F →+* ℂ} {B : LB Y}


end Good

section Fac

variable {r : ℕ} {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (x : ℝ)


open Classical in
def diagChar (e : Ix Dw → ℤ) (t : Ix Dw → (CAt σ)ˣ) : ℂ := toC (∏ ix, t ix ^ e ix).val

def homFac (la : AllWt.Weight Dw) (k : U.Comp) (w : (U.X k).dom) : ℝ :=
  lieFacZ Dw x (wtOf Dw la 0) * (U.X k).nfac (modelWt U (wtOf Dw la 0) k) w.1

theorem homN_eq_homFac (la : AllWt.Weight Dw) (f : Rul Xo c) (k : U.Comp) (w : (U.X k).dom) :
    homN U x (wtOf Dw la 0) f ⟨k, w.1⟩ = homFac U x la k w * ‖toC (evR Xo c f (U.un k w))‖ := by
  have e : rdU U f k w.1 = toC (evR Xo c f (U.un k w)) := dite_eq_left w.2
  change _ * (‖rdU U f k w.1‖ * (U.X k).nfac _ _) = _
  rw [e, homFac]
  ring

variable {U}

end Fac

end CompHS

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice

namespace GlobalTheory.HSShort

def ht {F : Type} [Field F] [NumberField F] {B N n : ℕ} (w : Matrix (Fin N) (Fin n) F)
    (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) (G : MvPolynomial (Fin B × Fin N) F) : ℝ := formHeight 0 w A G

def cst (n Λ : ℝ) : ℝ := Real.log (n * Λ) + (Real.log n + 1) / 2

structure Lat {F : Type} [Field F] [NumberField F] {N n : ℕ} (w : Matrix (Fin N) (Fin n) F)
    (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) (Λ : ℝ) : Prop where
  pos : 0 < N
  spans : Submodule.span F (Set.range w.col) = ⊤
  det : ∀ σ, (A σ).det ≠ 0
  le : ∀ k σ, frameNorm (A σ) (fun j => σ (w j k)) ≤ Λ
  one_le : 1 ≤ Λ

def HtMul : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (B N n : ℕ) (w : Matrix (Fin N) (Fin n) F) (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ)
    (Λ : ℝ), Lat w A Λ → (∀ (a a' : Fin B → ℕ) (G G' : MvPolynomial (Fin B × Fin N) F), G ≠ 0 → G' ≠ 0 →
      IsMultiHomogeneous a G → IsMultiHomogeneous a' G' → ht w A (G * G') = ht w A G + ht w A G') ∧
    ∀ c : F, c ≠ 0 → ht w A (C c : MvPolynomial (Fin B × Fin N) F) = 0

def HtLow : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (B N n : ℕ) (w : Matrix (Fin N) (Fin n) F) (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ)
    (Λ : ℝ), Lat w A Λ → ∀ (a : Fin B → ℕ) (G : MvPolynomial (Fin B × Fin N) F), G ≠ 0 → IsMultiHomogeneous a G →
      -(cst n Λ * ∑ b, (a b : ℝ)) ≤ ht w A G

def HeightTie : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (T : HermSys F) (Λ : ℝ), Lat T.w T.A Λ → ∀ h, T.IsHeight h →
    ∀ (d e : ℕ) (f : MvPolynomial (Fin (T.D + 1) × Fin T.N) F) (c : F), IsChowForm T.imageIdeal T.D d f → 1 ≤ e → c ≠ 0 →
      ht T.w T.A (C c * f ^ e) / (((T.D : ℝ) + 1) * (e * d : ℕ)) = h - (harmonic (T.N - 1) : ℝ) / 2 ∧
      h - (Real.log T.n + 1) / 2 ≤ ht T.w T.A (C c * f ^ e) / (((T.D : ℝ) + 1) * (e * d : ℕ))

structure SimpleAt {F : Type} [Field F] [NumberField F] (T : Tuple F) (δ : ℕ) (f : MvPolynomial (Fin (T.D + 1) × Fin T.N) F)
    (E : Type) [Field E] [Algebra F E] (s : Fin T.D → Fin T.N → E) : Prop where
  good : T.IsGoodSection E s
  card : (T.geomPts E (T.linSection E s)).ncard = δ
  inj : (T.toLinSys.baseChange E).InjOnPts (T.geomPts E (T.linSection E s))
  fac : ∃ c : AlgebraicClosure E, c ≠ 0 ∧ spec (fun i j => algebraMap E (AlgebraicClosure E) (s i j)) f =
    C c * ∏ᶠ x ∈ T.geomPts E (T.linSection E s), lin (T.coords (LinSys.toBase x : T.Pt (AlgebraicClosure E)).1)

def Bertini : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (T : Tuple F), T.IsGeometric → T.Birational →
    ∀ (δ : ℕ) (f : MvPolynomial (Fin (T.D + 1) × Fin T.N) F), IsChowForm T.imageIdeal T.D δ f →
      (δ : ℤ) = T.del ∧ ∃ Q : MvPolynomial (Fin T.D × Fin T.N) F, Q ≠ 0 ∧
        ∀ (E : Type) [Field E] [Algebra F E] (s : Fin T.D → Fin T.N → E),
          aeval (fun p : Fin T.D × Fin T.N => s p.1 p.2) Q ≠ 0 → SimpleAt T δ f E s

def BertiniNF : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (T : Tuple F), T.IsGeometric → T.Birational →
    ∀ (δ : ℕ) (f : MvPolynomial (Fin (T.D + 1) × Fin T.N) F), IsChowForm T.imageIdeal T.D δ f →
      (δ : ℤ) = T.del ∧ ∃ Q : MvPolynomial (Fin T.D × Fin T.N) F, Q ≠ 0 ∧
        ∀ (E : Type) [Field E] [NumberField E] [Algebra F E] (s : Fin T.D → Fin T.N → E),
          aeval (fun p : Fin T.D × Fin T.N => s p.1 p.2) Q ≠ 0 → SimpleAt T δ f E s

section Words

variable {K A : Type} [Field K] [AddCommGroup A] [Module K A] {N : ℕ} (mul : (Fin N → K) →ₗ[K] Module.End K A)

def word {t : ℕ} (u : Fin t → Fin N → K) : Module.End K A := (List.ofFn fun i => mul (u i)).prod

def pw {D : ℕ} (s : Fin D → Fin N → K) (α : Fin D →₀ ℕ) : Module.End K A := (List.ofFn fun i => mul (s i) ^ α i).prod

def coordP {B t : ℕ} (c : A →ₗ[K] K) (β : Fin t → Fin B) (m : A) : MvPolynomial (Fin B × Fin N) K :=
  ∑ e : Fin t → Fin N, C (c (word mul (fun i => Pi.single (e i) 1) m)) * ∏ i, X (β i, e i)

end Words

structure Sys (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A] where

  N : ℕ

  n : ℕ

  D : ℕ

  T : ℕ

  w : Matrix (Fin N) (Fin n) F

  fr : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ

  mul : (Fin N → F) →ₗ[F] Module.End F A

  V : ℕ → Submodule F A

  M : ∀ j, Submodule (𝓞 F) (V j)

  nm : ∀ j, HermFam F (V j)

  beta : ℝ

  abelian₂ : ℝ

  Lam0 : ℝ

  LamD : ℝ

  LamT : ℝ

def ClaimS (T D : ℕ) (n Λ β Λ₀ ΛD ΛT δ h d deg : ℝ) : Prop :=
  0 ≤ 1 - ((T - 1).choose D : ℝ) * δ / d ∧ 1 - ((T - 1).choose D : ℝ) * δ / d ≤ 1 ∧
    (1 - (1 - ((T - 1).choose D : ℝ) * δ / d)) * (T * h - D * (D + 1) * cst n Λ - Real.log Λ₀ - T / 2 * Real.log β) -
      (1 - ((T - 1).choose D : ℝ) * δ / d) * (T * cst n Λ + T / 2 * Real.log β + Real.log ΛD + Real.log ΛT) ≤ deg / d

namespace Sys

variable {F A : Type} [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A]
  (S : Sys F A)

def Short (j : ℕ) (Λ : ℝ) : Prop :=
  ∃ (r : ℕ) (b : Module.Basis (Fin r) F (S.V j)), ∀ i, b i ∈ S.M j ∧ ∀ σ, (S.nm j).nrm σ (b i) ≤ Λ

structure Hyp : Prop where
  one_le : 1 ≤ S.D
  le_T : S.D + 1 ≤ S.T
  lat : Lat S.w S.fr S.abelian₂
  comm : ∀ u v, S.mul u * S.mul v = S.mul v * S.mul u
  full : ∀ j ≤ S.T, IsFull (S.M j)
  stable : ∀ j < S.T, ∀ k, ∀ f ∈ S.M j, ∃ g ∈ S.M (j + 1), (g : A) = S.mul (S.w.col k) f
  bound : ∀ σ, ∀ j < S.T, ∀ (u : Fin S.N → ℂ) (m : ℕ) (c : Fin m → ℂ) (f : Fin m → S.V j) (g : Fin S.N × Fin m → S.V (j + 1)),
    (∀ k i, (g (k, i) : A) = S.mul (Pi.single k 1) (f i)) →
      cnrm (S.nm (j + 1)) σ (fun t => u t.1 * c t.2) g ≤ Real.sqrt S.beta * frameNorm (S.fr σ) u * cnrm (S.nm j) σ c f
  one_le_beta : 1 ≤ S.beta
  hermSysHyp_one_le_lambdaZero : 1 ≤ S.Lam0
  one_le_LamD : 1 ≤ S.LamD
  one_le_LamT : 1 ≤ S.LamT
  short0 : S.Short 0 S.Lam0
  shortD : S.Short S.D S.LamD
  shortT : S.Short S.T S.LamT

structure Col where

  j : ℕ

  t : ℕ
  add : j + t = S.T

  β : Fin t → Fin (S.D + 1)

  x : S.V j

def IsCo {d : ℕ} (b : Module.Basis (Fin d) F (S.V S.T)) (c : Fin d → A →ₗ[F] F) : Prop := ∀ i (x : S.V S.T), c i x = b.repr x i

def det {d : ℕ} (c : Fin d → A →ₗ[F] F) (col : Fin d → S.Col) : MvPolynomial (Fin (S.D + 1) × Fin S.N) F :=
  (Matrix.of fun i k => coordP S.mul (c i) (col k).β ((col k).x : A)).det

def Col.HasType {S : Sys F A} (κ : S.Col) (α : Fin S.D →₀ ℕ) : Prop :=
  ∀ i : Fin S.D, (Finset.univ.filter fun q => κ.β q = i.castSucc).card = α i

structure Flat (E A' : Type) [Field E] [Algebra F E] [AddCommGroup A'] [Module E A'] (s : Fin S.D → Fin S.N → E) (δ : ℕ) where

  ι : A →ₛₗ[algebraMap F E] A'
  indep : ∀ (m : ℕ) (v : Fin m → S.V S.T), LinearIndependent F v → LinearIndependent E fun i => ι (v i)

  mul : (Fin S.N → E) →ₗ[E] Module.End E A'
  comm : ∀ u v, mul u * mul v = mul v * mul u
  mul_ι : ∀ u x, mul (fun k => algebraMap F E (u k)) (ι x) = ι (S.mul u x)

  y : Fin δ → Fin S.N → E
  y_ne : ∀ p, y p ≠ 0

  res : A' →ₗ[E] (Fin δ → E)
  onto : (Submodule.span E (ι '' S.V 0)).map res = ⊤

  U : ℕ → Submodule E A'

  sym : ∀ a, U a →ₗ[E] (MonoDeg (Fin S.D) a × Fin δ → E)
  le : ∀ a < S.T - S.D, U (a + 1) ≤ U a
  ker : ∀ a < S.T - S.D, ∀ x : U a, sym a x = 0 ↔ x.1 ∈ U (a + 1)
  mono : ∀ a < S.T - S.D, ∀ (α : MonoDeg (Fin S.D) a) (l : Fin (S.T - a) → Fin S.N → E), ∀ m ∈ Submodule.span E (ι '' S.V 0),
    ∃ h : pw mul s α.1 (word mul l m) ∈ U a, ∀ α' p,
      sym a ⟨_, h⟩ (α', p) = if α'.1 = α.1 then (∏ q, ∑ k, l q k * y p k) * res m p else 0
  div : U (S.T - S.D) = ⨆ α : MonoDeg (Fin S.D) (S.T - S.D), (Submodule.span E (ι '' S.V S.D)).map (pw mul s α.1)

def FlatAt (δ : ℕ) (f : MvPolynomial (Fin (S.D + 1) × Fin S.N) F) (s : Fin S.D → Fin S.N → F) : Prop :=
  ∃ (E A' : Type) (_ : Field E) (_ : Algebra F E) (_ : AddCommGroup A') (_ : Module E A')
    (Φ : S.Flat E A' (fun i k => algebraMap F E (s i k)) δ) (c : E), c ≠ 0 ∧
      spec (fun i k => algebraMap F E (s i k)) f = C c * ∏ p, lin (Φ.y p)

structure Shape {d : ℕ} (δ : ℕ) (col : Fin d → S.Col) (m : Fin δ → S.V 0)
    (ix : (Σ a : Fin (S.T - S.D), MonoDeg (Fin S.D) a) × Fin δ ↪ Fin d) : Prop where
  x_j : ∀ q, (col (ix q)).j = 0
  x_vec : ∀ q, ((col (ix q)).x : A) = m q.2
  x_type : ∀ q, (col (ix q)).HasType q.1.2.1
  rest : ∀ k, k ∉ Set.range ix → ((col k).j = S.D ∧ ∀ q, (col k).β q ≠ Fin.last S.D) ∨ (col k).j = S.T

def ShortCols {d : ℕ} (col : Fin d → S.Col) : Prop :=
  ∀ k, (col k).x ∈ S.M (col k).j ∧ ∀ σ, (S.nm (col k).j).nrm σ (col k).x ≤
    if (col k).j = 0 then S.Lam0 else if (col k).j = S.D then S.LamD else S.LamT

def deepRank (s : Fin S.D → Fin S.N → F) : ℕ :=
  Module.finrank F (⨆ α : MonoDeg (Fin S.D) (S.T - S.D), (S.V S.D).map (pw S.mul s α.1) : Submodule F A)

def expo : ℕ := ∑ a ∈ Finset.range (S.T - S.D), (a + S.D - 1).choose (S.D - 1) * (S.T - a)

end Sys

def SlopeBound : Prop :=
  ∀ (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A]
    (S : Sys F A), S.Hyp → ∀ (δ : ℕ) (f : MvPolynomial (Fin (S.D + 1) × Fin S.N) F) (Q : MvPolynomial (Fin S.D × Fin S.N) F),
      1 ≤ δ → IsMultiHomogeneous (fun _ => δ) f → Irreducible f → Q ≠ 0 →
      (∀ s : Fin S.D → Fin S.N → F, eval (fun p => s p.1 p.2) Q ≠ 0 → S.FlatAt δ f s) →
      0 < Module.finrank F (S.V S.T) ∧
        ClaimS S.T S.D S.n S.abelian₂ S.beta S.Lam0 S.LamD S.LamT δ (ht S.w S.fr f / (((S.D : ℝ) + 1) * δ))
          (Module.finrank F (S.V S.T)) (deg (S.nm S.T) (S.M S.T))

structure GeoHyp {F : Type} [Field F] [NumberField F] (X : Data F) (Λ₀ : ℝ) : Prop where
  totallyComplex : IsTotallyComplex F
  bir : X.Birational
  nef : IsNef F X.LA
  big : IsBig F X.LA
  nef₂ : IsNef F X.L₂
  big₂ : IsBig F X.L₂
  mulStable : Data.MulStable X
  mulBound : Data.MulBound X fun _ => X.beta
  normsLe : X.NormsLe
  one_le_Lam : 1 ≤ X.abelian₂
  hermSysHyp_one_le_lambdaZero : 1 ≤ Λ₀
  short0 : X.ShortFamily 0 Λ₀
  shortD : X.ShortFamily X.D X.LamD
  shortT : X.ShortFamily X.T X.LamT

def GeoBound : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (X : Data F) (Λ₀ : ℝ), GeoHyp X Λ₀ → ∀ h, X.IsHeight h →
    Formalism.NormVectorIdentities.Items.HSClaimS 26 X.T X.D X.n 1 X.abelian₂ X.beta X.LamD X.LamT (Real.log Λ₀) X.del h X.d (X.degM X.T)

end GlobalTheory.HSShort
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.OverPair
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong Formalism.UG

namespace GlobalTheory.CongW

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {l : ℕ} [Fact l.Prime]

def OverPair (ι : Qbar l ≃+* ℂ) (w₀ : HeightOneSpectrum (𝓞 E)) (τ : E →+* ℂ) : Prop :=
  (∀ x : 𝓞 E, x ∈ w₀.asIdeal → ‖ι.symm (τ (x : E))‖ < 1) ∨
    (∀ x : 𝓞 E, x ∈ w₀.asIdeal → ‖ι.symm (τ (IsCMField.complexConj E (x : E)))‖ < 1)

end GlobalTheory.CongW
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.FrameSignSimple
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct nonZeroDivisors

namespace GlobalTheory.FunObj.SumModel

open GlobalTheory.ChiGrid Formalism.L2.Host Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem readOK {ι : Type} [Fintype ι] {n : ℕ} (σ : ι → DomWeight n) : ReadOK σ := by
  obtain ⟨Φ, h, -⟩ := funForm (K := ℂ) σ
  exact readOK_of_equiv σ Φ fun F => (h F _).2 rfl

theorem finEmb_eq {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) (y : GfC A) (x : GfC B)
    (h : EmbRel B A d.ι x.1 y.1) : finEmb d y = x :=
  Subtype.ext ((GlobalTheory.AutFunCounterexample.embRel_existsUnique B A d.ι d.isom y.1).unique (finEmb_rel d y) h)

theorem finEmb_mul {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) (y y' : GfC A) :
    finEmb d (y * y') = finEmb d y * finEmb d y' := by
  refine finEmb_eq d _ _ ⟨?_, fun v hv => ?_⟩
  · have h1 := (finEmb_rel d y).1
    have h2 := (finEmb_rel d y').1
    simp only [Subgroup.coe_mul, map_mul, Units.val_mul] at *
    rw [Matrix.mul_assoc, h2, ← Matrix.mul_assoc, h1, Matrix.mul_assoc]
  · have h1 := (finEmb_rel d y).2 v hv
    have h2 := (finEmb_rel d y').2 v hv
    simp only [Subgroup.coe_mul, map_mul, Units.val_mul] at *
    rw [← Matrix.mulVec_mulVec, h2, h1]

end GlobalTheory.FunObj.SumModel

end
end
