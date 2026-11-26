module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BXiAsm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HasFDerivAtFsvOther

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrablePairOfSquareIntegrable
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate InnerProductSpace ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerB

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section L2

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem norm_hs_le (A C : Wq →L[ℂ] Wp) : ‖B.hsInner A C‖ ≤ ‖B.hsInner A A‖ + ‖B.hsInner C C‖ := by
  unfold B.hsInner
  have h1 := norm_inner_le_norm (𝕜 := ℂ) (B.hsVec C) (B.hsVec A)
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
  simp only [norm_pow, RCLike.norm_ofReal, Complex.norm_real, abs_norm, norm_norm]
  nlinarith [norm_nonneg (B.hsVec A), norm_nonneg (B.hsVec C), sq_nonneg (‖B.hsVec A‖ - ‖B.hsVec C‖)]

end L2

section Cls

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

end Cls

section Top

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

end Top

end Formalism.FourierDecayAlt.P5.HerB
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.SfiniteOfIsHaarOn
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.HerClassesOfParts
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.TopIdentFromParts
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd

theorem ofWordRR : OfWordRR := by
  intro A S _ _ _ _ _ r L st w
  induction w with
  | nil =>
    exact ⟨by simp [Fr.ofWord, RRw, Fr.Start.frame], fun Y => by simp [Fr.ofWord, TTw, Fr.Start.frame]⟩
  | cons l w ih =>
    obtain ⟨ih1, ih2⟩ := ih
    cases hl : l.plus
    · exact ⟨by simp [Fr.ofWord, RRw, hl, Fr.FrameData.minus, ih1, ih2],
        fun Y => by simp [Fr.ofWord, TTw, hl, Fr.FrameData.minus, ih2]⟩
    · exact ⟨by simp [Fr.ofWord, RRw, hl, Fr.FrameData.plus, ih1, ih2],
        fun Y => by simp [Fr.ofWord, TTw, hl, Fr.FrameData.plus, ih2]⟩

section

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem tprod_ge (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (Y : ℂ) (i : ℕ) (h : r ≤ i) :
    tprod L Y i = 1 := by
  rw [tprod, dite_eq_right (by omega)]

theorem QQi_last (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (st : Fr.Start (Pr (RadSp k r z z' π π')))
    (Y : ℂ) : QQi L st (Fin.last r) Y = st.QQ Y := by
  rw [QQi, Fin.val_last, tprod_ge L (star Y) r le_rfl, tprod_ge L Y r le_rfl, Matrix.conjTranspose_one,
    one_mul, mul_one]

end

theorem topIdentFromParts {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π')))
    (K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')) (l0 : ℕ) :
    TopIdentFromParts (S := S) P z z' π π' X μ L st K l0 := by
  intro hD hFA hOW hAdj w hw x y hx hy c hc
  obtain ⟨hint, heq⟩ := hAdj w hw x y hx hy c hc
  refine ⟨hint, ?_⟩
  have hQ : QQi L st (Fin.last P.r) = st.QQ := funext fun Y => QQi_last L st Y
  have hfr := hFA (Pr (RadSp P.k P.r z z' π π')) S P.r L st w hD.2.2.2.2.2.2.1 hD.2.2.2.2.2.2.2 hw.1
  have hRR : RRi L st (Fin.last P.r) w =
      star (Fr.ofWord L st w).F * (Fr.ofWord L st w).d L * (Fr.ofWord L st w).F := by
    rw [RRi, hQ, ← (hOW _ S P.r L st w).1, hfr.form]
  rw [RRform, hRR, heq]

end Formalism.FourierDecayAlt.P5
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.EqOfContinuousOffZero
open MeasureTheory Filter Topology
open scoped ComplexConjugate ComplexOrder

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T

theorem isClosed_nonneg_complex : IsClosed {z : ℂ | 0 ≤ z} := by
  have h : {z : ℂ | 0 ≤ z} = {z : ℂ | 0 ≤ z.re} ∩ {z : ℂ | z.im = 0} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Complex.le_def, Complex.zero_re, Complex.zero_im]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2.symm⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2.symm⟩
  rw [h]
  exact (isClosed_le continuous_const Complex.continuous_re).inter
    (isClosed_eq Complex.continuous_im continuous_const)

theorem integral_nonneg_complex {α : Type*} [MeasurableSpace α] (ν : Measure α) (f : α → ℂ)
    (h : ∀ a, 0 ≤ f a) : 0 ≤ ∫ a, f a ∂ν := by
  have hre : ∀ a, f a = ((f a).re : ℂ) := fun a => by
    apply Complex.ext
    · simp
    · simp only [Complex.ofReal_im]
      exact ((Complex.le_def.mp (h a)).2).symm
  have hf : (fun a => f a) = fun a => ((f a).re : ℂ) := funext hre
  rw [hf]
  first
  | rw [integral_complex_ofReal]
  | rw [integral_ofReal]
  | rw [← RCLike.ofReal_eq_complex_ofReal, integral_ofReal]
  exact Complex.zero_le_real.mpr (integral_nonneg fun a => (Complex.le_def.mp (h a)).1)

theorem continuous_fsv (s : ℂ) : Continuous (fsv s) := by
  unfold fsv
  exact ((continuous_const.mul continuous_id).sub
    (continuous_const.mul Complex.continuous_conj)).cexp

theorem nonneg_of_continuous {φ : ℂ → ℂ} (hc : Continuous φ) (h : ∀ t, t ≠ 0 → 0 ≤ φ t) :
    ∀ t, 0 ≤ φ t := by
  have hcl : IsClosed {t | 0 ≤ φ t} := isClosed_nonneg_complex.preimage hc
  have hsub : ({(0 : ℂ)}ᶜ : Set ℂ) ⊆ {t | 0 ≤ φ t} := fun t ht => h t ht
  have hcl2 := hcl.closure_subset_iff.mpr hsub
  rw [(dense_compl_singleton (0 : ℂ)).closure_eq] at hcl2
  intro t
  exact hcl2 (Set.mem_univ t)

theorem eq_of_continuous_off_zero {f g : ℂ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ t, t ≠ 0 → f t = g t) : f = g := hf.ext_on (dense_compl_singleton (0 : ℂ)) hg (fun t ht => h t ht)

theorem update_mem_OmX {m : ℕ} {c : Fin m → ℂ} (hc : c ∈ OmX m) (l : Fin m) {t : ℂ} (ht : t ≠ 0) :
    Function.update c l t ∈ OmX m := by
  intro j
  rcases eq_or_ne j l with rfl | hj
  · simpa using ht
  · rw [Function.update_of_ne hj]
    exact hc j

theorem nonneg_all_levels {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S]
    [DecidableEq S] (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π')))
    (K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')) (l0 : ℕ)
    (hTI : TopIdent (S := S) P z z' π π' μ L st K l0) (hTN : TopDensNonneg (S := S) P z z' π π' L st K l0)
    (hSI : SliceIn (S := S) P z z' π π' L st K l0) (hSD : StepDens (S := S) P z z' π π' μ L st K l0)
    (w : List (Letter ℂ S)) (hw : WordOK P z z' π π' st l0 w) :
    ∀ (n : ℕ) (i : Fin (P.r + 1)), i.val + n = P.r → ∀ c ∈ OmX P.r,
      ∀ x : Ix S → RadSp P.k P.r z z' π π', InK (K i) x → 0 ≤ RRform L st μ i w x x c := by
  intro n
  induction n with
  | zero =>
    intro i hi c hc x hx
    have hi' : i = Fin.last P.r := Fin.ext (by simpa using hi)
    subst hi'
    rw [(hTI w hw x x hx hx c hc).2]
    exact integral_nonneg_complex μ _ (fun g => hTN w hw x hx c hc (Matrix.of g))
  | succ n ih =>
    intro i hi c hc x hx
    have hlt : i.val < P.r := by omega
    obtain ⟨l, rfl⟩ : ∃ l : Fin P.r, l.castSucc = i := ⟨⟨i.val, hlt⟩, Fin.ext rfl⟩
    obtain ⟨φ, hφc, hφ, -, hint⟩ := hSD w hw l x x hx hx c hc
    rw [← hint]
    apply integral_nonneg_complex
    apply nonneg_of_continuous hφc
    intro t ht
    rw [hφ t ht]
    unfold ph
    apply mul_nonneg
    · exact Complex.zero_le_real.mpr (by positivity)
    · have hn : (l.succ).val + n = P.r := by
        simp only [Fin.coe_castSucc] at hi
        simp only [Fin.val_succ]
        omega
      exact ih l.succ hn _ (update_mem_OmX hc l ht) _ (hSI w hw l x hx)

theorem thmPFromStepsAll : ThmPFromStepsAll := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' μ L st K l0
  intro hTI hTN hTT hSI hSD hST hFS w hw
  refine ⟨?_, ?_, ?_⟩
  · intro x y hx hy c hc
    refine ⟨(hTI w hw x y hx hy c hc).1, ?_, ?_⟩
    · intro s Wv Wv' h1 h2
      obtain ⟨hK, hD⟩ := hTT w hw s Wv Wv' h1 h2 x y hx hy c hc
      rw [(hTI w hw _ y hK hy c hc).2]
      congr 1
      funext g
      rw [hD]
    · exact nonneg_all_levels (S := S) P z z' π π' μ L st K l0 hTI hTN hSI hSD w hw 0
        (Fin.last P.r) (by simp) c hc x hx
  · intro l x y hx hy c hc
    obtain ⟨φ, hφc, hφ, hC, -⟩ := hSD w hw l x y hx hy c hc
    refine ⟨φ, hφc, hφ, hC, ?_⟩
    intro s Wv Wv' h1 h2
    obtain ⟨hK, hT⟩ := hST w hw l s Wv Wv' h1 h2 x y hx hy c hc
    obtain ⟨ψ, hψc, hψ, -, hψint⟩ := hSD w hw l _ y hK hy c hc
    rw [← hψint]
    congr 1
    apply eq_of_continuous_off_zero ((continuous_fsv s).mul hφc) hψc
    intro t ht
    show fsv s t * φ t = ψ t
    rw [hψ t ht, hT t ht, hφ t ht]
  · intro i c hc
    refine ⟨hFS w hw i c hc, ?_⟩
    intro x hx
    have hxK : InK (K i) x := fun a => (Submodule.mem_pi.mp hx) a (Set.mem_univ a)
    exact nonneg_all_levels (S := S) P z z' π π' μ L st K l0 hTI hTN hSI hSD w hw (P.r - i.val) i
      (by omega) c hc x hxK

end Formalism.FourierDecayAlt.P5
end
end

open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd

section Struct

variable {V : Type} [AddCommGroup V] [Module ℂ V] {S : Type} [Fintype S] [DecidableEq S]

theorem inK_act_span {G G' : Set V} (M : SlopeTestRemainingChoices S (Pr V)) (hM : ∀ a b, ∀ Φ ∈ G, (M a b).1 Φ ∈ Submodule.span ℂ G')
    (x : Ix S → V) (hx : ∀ a, x a ∈ Submodule.span ℂ G) : ∀ a, ∑ b, (M a b).1 (x b) ∈ Submodule.span ℂ G' := by
  intro a
  refine Submodule.sum_mem _ (fun b _ => ?_)
  have hle : Submodule.span ℂ G ≤ (Submodule.span ℂ G').comap (M a b).1 :=
    Submodule.span_le.mpr (fun Φ hΦ => hM a b Φ hΦ)
  exact hle (hx b)

end Struct

section Classes

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
variable {S : Type} [Fintype S] [DecidableEq S]
variable {P : M.Par} {z z' : Fin (2 * P.r + P.k + 1) → ℂ} {π : Mx P.k P.r → (Wp →L[ℂ] Wp)}
  {π' : Mx P.k P.r → (Wq →L[ℂ] Wq)} {L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r}
  {st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))} {l0 : ℕ} {D : B.RealPlaceData P.k P.r Wp Wq}

end Classes

end Formalism.FourierDecayAlt.P5
end
end

open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd

theorem sfinite_of_isHaarOn {k r : ℕ} (U : Set (B.Mat k r)) (μ : Measure (Mt k r)) (h : B.IsHaarOn U μ) :
    SFinite μ := by
  haveI : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => h.finite_compact K hK⟩
  infer_instance

end Formalism.FourierDecayAlt.P5
end
end

open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerC

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB

section Classes

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
variable {S : Type} [Fintype S] [DecidableEq S]
variable {P : M.Par} {z z' : Fin (2 * P.r + P.k + 1) → ℂ} {π : Mx P.k P.r → (Wp →L[ℂ] Wp)}
  {π' : Mx P.k P.r → (Wq →L[ℂ] Wq)} {L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r}
  {st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))} {l0 : ℕ} {D : B.RealPlaceData P.k P.r Wp Wq}

theorem herKc_sliceIn : SliceIn (S := S) P z z' π π' L st (herKc S P z z' π π' L st l0 D) l0 := by
  intro w hw l x hx
  exact inK_act_span (bTl L l w) (fun a b Φ hΦ => Submodule.subset_span (HerGenC.slice l w a b Φ hw hΦ)) x hx

theorem herKc_waveK : WaveK (S := S) P z z' π π' st (herKc S P z z' π π' L st l0 D) l0 := by
  intro w hw l s Wv Wv' hW hW' x hx
  exact inK_act_span (Vw (mkP Wv Wv') s w)
    (fun a b Φ hΦ => Submodule.subset_span (HerGenC.waveC l w s Wv Wv' a b Φ hw hW hW' hΦ)) x hx

theorem herKc_waveZ (w : List (Letter ℂ S)) (hw : WordOK P z z' π π' st l0 w) (s : ℂ)
    (Wv Wv' : Module.End ℂ (RadSp P.k P.r z z' π π')) (hW : multiplicationOperator Wv (fun _ g => fsv s (zeta P.k P.r z z' g)))
    (hW' : multiplicationOperator Wv' (fun _ g => fsv (-s) (zeta P.k P.r z z' g))) (x : Ix S → RadSp P.k P.r z z' π π')
    (hx : InK (herKc S P z z' π π' L st l0 D (Fin.last P.r)) x) :
    InK (herKc S P z z' π π' L st l0 D (Fin.last P.r)) (act (Vw (mkP Wv Wv') s w) x) :=
  inK_act_span (Vw (mkP Wv Wv') s w)
    (fun a b Φ hΦ => Submodule.subset_span (HerGenC.waveZ w s Wv Wv' a b Φ hw hW hW' hΦ)) x hx

theorem herKc_jf (F : Mx P.k P.r → (Wq →L[ℂ] Wp)) (hF : JFOKCpt P z z' F) (Φ : RadSp P.k P.r z z' π π')
    (hΦ : IsRadJF P z z' π π' D F Φ) : Φ ∈ herKc S P z z' π π' L st l0 D 0 :=
  Submodule.subset_span (HerGenC.jf F Φ hF hΦ)

end Classes

def HerCptTopAll : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    herKc S P z z' π π' L st l0 D (Fin.last P.r) ≤ cptSub P.k P.r z z' π π'

def StepFormCptAll : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    StepDens (S := S) P z z' π π' μ L st (herKc S P z z' π π' L st l0 D) l0 ∧
      FormInt S P z z' π π' μ L st l0 (herKc S P z z' π π' L st l0 D)

theorem thmPActualCpt_of_herClassesCpt (hHer : HerClassesCpt) (hWC : WaveCommQQAll) : ThmPActualCpt := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D A mm hD hl1 hl2 hz hz' hπ hπ' hA hmm
  obtain ⟨K, hAdj, hTD, hTT, hSl, hSD, hWK, hFS, hCor, hJ⟩ :=
    hHer Wp Wq S P z z' π π' X μ L st l0 D A mm hD hl1 hl2 hz hz' hπ hπ' hA hmm
  refine ⟨K, ?_, hSl, hCor, hJ⟩
  have hTI := topIdentFromParts (S := S) P z z' π π' X μ L st K l0 hD Formalism.FourierDecayAlt.P.frame_of_admissible_word ofWordRR hAdj
  have hST := stepTwistFromParts (S := S) P z z' π π' X μ L st K l0 hD Formalism.FourierDecayAlt.P.plane_wave_vector_identity
    (waveSiteAll Wp Wq P z z' π π' X L) (hWC Wp Wq P z z' π π' X μ L st l0 hD) hWK
  exact thmPFromStepsAll Wp Wq S P z z' π π' μ L st K l0 hTI hTD hTT hSl hSD hST hFS

theorem herClassesCpt_of_parts (hT : HerCptTopAll) (hSF : StepFormCptAll) : HerClassesCpt := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D A mm hD hl1 hl2 hz hz' hπ hπ' _ _
  obtain ⟨hSD, hFI⟩ := hSF Wp Wq S P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ'
  set K := herKc S P z z' π π' L st l0 D with hKdef
  haveI : SFinite μ := sfinite_of_isHaarOn _ μ hD.2.1
  have hAdj : AdjTop (S := S) P z z' π π' μ L st K l0 :=
    adjTop_cpt P z z' π π' X μ L st K l0 hD (hT Wp Wq S P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ')
  have hTI := topIdentFromParts (S := S) P z z' π π' X μ L st K l0 hD
    Formalism.FourierDecayAlt.P.frame_of_admissible_word ofWordRR hAdj
  have hXK := xKappaOfNF Formalism.FourierDecayAlt.P.normal_form_actual kappaFibrePos Wp Wq P z z' π π' X μ L st l0 hD
  have hTD := topDensNonnegOfKappa Wp Wq S P z z' π π' X μ L st l0 K hD hl1 hl2 hXK
  have hCor := integral_formula_of_steps Wp Wq S P z z' π π' μ L st l0 K hTI hTD herKc_sliceIn hSD
    (topDensMeasAll Wp Wq S P z z' π π' μ L st K)
  have hTT := topTwistDensOfZeta Formalism.FourierDecayAlt.P.actual_zeta_smooth_alt Wp Wq S P z z' π π' X μ L st l0 K hD
  have hFS := formSesqOfInt Wp Wq S P z z' π π' μ L st l0 _ hFI
  refine ⟨K, hAdj, hTD, ?_, herKc_sliceIn, hSD, herKc_waveK, hFS, hCor, ?_⟩
  · intro w hw s Wv Wv' hW hW' x y hx hy c hc
    exact ⟨herKc_waveZ w hw s Wv Wv' hW hW' x hx, hTT w hw s Wv Wv' hW hW' x y hx hy c hc⟩
  · intro F ε hε hF hC hG
    obtain ⟨Φ, hΦ⟩ := radJFExists Wp Wq P z z' π π' D F hD.1 hz hz' hπ hπ' ⟨hF, ε, hε, hG⟩
    exact ⟨Φ, herKc_jf F ⟨⟨hF, ε, hε, hG⟩, hC⟩ Φ hΦ, hΦ⟩

theorem thmPActualCpt_of_parts (hT : HerCptTopAll) (hSF : StepFormCptAll) : ThmPActualCpt :=
  thmPActualCpt_of_herClassesCpt (herClassesCpt_of_parts hT hSF) waveCommQQAll

end Formalism.FourierDecayAlt.P5.HerC
