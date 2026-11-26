module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsOpenDomP

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEJSliceCut
open MeasureTheory Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC
  Formalism.FourierDecayAlt.P5.HerD

section WaveJc

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
variable (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
  (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (D : B.RealPlaceData P.k P.r Wp Wq) (l : Fin P.r)

def IsWaveJc (Ψ : RadSp P.k P.r z z' π π') : Prop :=
  Ψ ∈ lcSub P.k P.r z z' π π' ∧ ∃ (s : ℂ) (ε : ℝ) (G : Mx P.k P.r → (Wq →L[ℂ] Wp)), 0 < ε ∧ JC.NiceCoef D ε G ∧
    HasCompactSupport G ∧ ∀ y ∈ DomR P.k P.r z z', (Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) y.1 y.2 =
      fsv s (y.1 l) • resG P.k P.r (Fin.last P.r) (B.JF D G) y.1 y.2

def waveJc : Submodule ℂ (RadSp P.k P.r z z' π π') :=
  Submodule.span ℂ {Ψ | IsWaveJc P z z' π π' D l Ψ}

end WaveJc

def JSliceGenC : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    ∀ (l : Fin P.r), l.val = 0 →
    ∀ c ∈ OmX P.r, ∀ Ψ : RadSp P.k P.r z z' π π', IsWaveJc P z z' π π' D l Ψ → SliceGood X μ l c Ψ

def JSSob2 : Prop :=
  ∀ (t0 : ℂ) (δ : ℝ), 0 < δ → ∃ K : ℝ, ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f fx fy fxy : ℂ → E),
    (∀ t ∈ Metric.closedBall t0 (2 * δ),
      HasFDerivAt f (Complex.reCLM.smulRight (fx t) + Complex.imCLM.smulRight (fy t)) t) →
    (∀ t ∈ Metric.closedBall t0 (2 * δ), ∃ fyy : E,
      HasFDerivAt fy (Complex.reCLM.smulRight (fxy t) + Complex.imCLM.smulRight fyy) t) →
    ContinuousOn fx (Metric.closedBall t0 (2 * δ)) → ContinuousOn fxy (Metric.closedBall t0 (2 * δ)) →
    ∀ t ∈ Metric.ball t0 δ, ‖f t‖ ^ 2 ≤
      K * ∫ s in Metric.closedBall t0 (2 * δ), (‖f s‖ ^ 2 + ‖fx s‖ ^ 2 + ‖fy s‖ ^ 2 + ‖fxy s‖ ^ 2)

def JSMeas : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (π : Mx k r → (Wp →L[ℂ] Wp)) (π' : Mx k r → (Wq →L[ℂ] Wq)) (l : Fin r) (c : Fin r → ℂ)
    (Φ Ψ : RadSp k r z z' π π'),
    Measurable (fun q : (ℂ × Cf r l.succ) × Mt k r =>
      B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) (glue l.succ (Function.update c l q.1.1) q.1.2) (Matrix.of q.2))
        ((Ψ : Fn k r (Wq →L[ℂ] Wp)) (glue l.succ (Function.update c l q.1.1) q.1.2) (Matrix.of q.2)))

def SpectralL2Locality : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    ∀ (l : Fin P.r), l.val = 0 →
    ∀ c ∈ OmX P.r, ∀ Ψ : RadSp P.k P.r z z' π π', IsWaveJc P z z' π π' D l Ψ → ∀ (js : List (Fin 6)) (t0 : ℂ),
      t0 ≠ 0 → ∃ ε : ℝ, 0 < ε ∧ ∃ M : ℝ, ∀ t ∈ Metric.ball t0 ε,
        LevelSquareIntegrable μ l.succ (wOp X l js Ψ) (Function.update c l t) ∧
          ‖fs μ l (wOp X l js Ψ) (wOp X l js Ψ) c t‖ ≤ M

def JSWordNF : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (π : Mx k r → (Wp →L[ℂ] Wp)) (π' : Mx k r → (Wq →L[ℂ] Wq)) (X : ActualOps k r z z' π π') (l : Fin r)
    (s : ℂ) (Wv : Module.End ℂ (RadSp k r z z' π π')), multiplicationOperator Wv (fun c _ => fsv s (c l)) →
    ∀ js : List (Fin 6), ∃ (K : ℕ) (m : Fin K → ℂ → ℂ) (ab : Fin K → List (Fin 6)),
      (∀ i, ContinuousOn (m i) {0}ᶜ) ∧ (∀ i, ∀ j ∈ ab i, j = 0 ∨ j = 3) ∧
      ∀ (Φ : RadSp k r z z' π π') (p : Fin r → ℂ), p ∈ OmX r → ∀ g : Mx k r,
        (wOp X l js (Wv Φ) : Fn k r (Wq →L[ℂ] Wp)) p g =
          ∑ i, (m i (p l) * fsv s (p l)) • (wOp X l (ab i) Φ : Fn k r (Wq →L[ℂ] Wp)) p g

def JSRadLoc : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    ∀ (l : Fin P.r), l.val = 0 → ∀ (ε : ℝ), 0 < ε → ∀ G : Mx P.k P.r → (Wq →L[ℂ] Wp), JC.NiceCoef D ε G →
    HasCompactSupport G → ∀ Φ : RadSp P.k P.r z z' π π', Φ ∈ lcSub P.k P.r z z' π π' →
    (∀ y ∈ DomR P.k P.r z z', (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) y.1 y.2 =
      resG P.k P.r (Fin.last P.r) (B.JF D G) y.1 y.2) →
    ∀ c ∈ OmX P.r, ∀ js : List (Fin 6), (∀ j ∈ js, j = 0 ∨ j = 3) → ∀ t0 : ℂ, t0 ≠ 0 →
      ∃ ε' : ℝ, 0 < ε' ∧ ∃ M : ℝ, ∀ t ∈ Metric.ball t0 ε',
        LevelSquareIntegrable μ l.succ (wOp X l js Φ) (Function.update c l t) ∧
          ‖fs μ l (wOp X l js Φ) (wOp X l js Φ) c t‖ ≤ M

end Formalism.FourierDecayAlt.P.CutSE
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.LocOfSmoothOnH
open Matrix
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.SingleEntryHermitianProducts

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.PBG

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem glev0 {g : Mat k r} (hg : g ∈ GV k r) : g ∈ Q.Glev k r 0 :=
  ⟨hg, fun a ha => by simp at ha⟩

theorem fold_congrV (V : Set (Mat k r)) :
    ∀ (L : List ((Mat k r → E) → (Mat k r → E))),
    (∀ T ∈ L, ∀ h₁ h₂ : Mat k r → E, (∀ x ∈ V, x ∈ GV k r → h₁ x = h₂ x) →
      ∀ x ∈ V, x ∈ GV k r → T h₁ x = T h₂ x) →
    ∀ h₁ h₂ : Mat k r → E, (∀ x ∈ V, x ∈ GV k r → h₁ x = h₂ x) →
      ∀ x ∈ V, x ∈ GV k r → L.foldr (fun T h => T h) h₁ x = L.foldr (fun T h => T h) h₂ x
  | [], _, _, _, he => by simpa using he
  | T :: L, hT, h₁, h₂, he => by
    intro x hx hxG
    simp only [List.foldr_cons]
    exact hT T (by simp) _ _ (fold_congrV V L (fun T' hT' => hT T' (by simp [hT'])) h₁ h₂ he) x hx hxG

theorem qminorOp_congr {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ) {V : Set (Mat k r)} (hV : IsOpen V)
    {f₁ f₂ : Mat k r → E} (he : ∀ x ∈ V, x ∈ GV k r → f₁ x = f₂ x) (x : Mat k r) (hx : x ∈ V)
    (hxG : x ∈ GV k r) : qminorOp (EabH (Hpk k r)) a b u f₁ x = qminorOp (EabH (Hpk k r)) a b u f₂ x := by
  unfold qminorOp
  rw [Finset.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Pi.smul_apply]
  congr 1
  refine fold_congrV V _ ?_ f₁ f₂ he x hx hxG
  intro T hT h₁ h₂ he' y hy hyG
  obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hT
  exact top_congr' V hV _ _ _ he' y hy hyG

theorem vLet_congr (z z' : Fin (2 * r + k + 1) → ℂ) (i : ℕ) (hi : i ≤ r) (l : C.Letter) (e : Fin 2)
    {V : Set (Mat k r)} (hV : IsOpen V) {f₁ f₂ : Mat k r → E} (he : ∀ x ∈ V, x ∈ GV k r → f₁ x = f₂ x)
    (x : Mat k r) (hx : x ∈ V) (hxG : x ∈ GV k r) :
    D.vLet k r z z' i hi l e f₁ x = D.vLet k r z z' i hi l e f₂ x := by
  unfold D.vLet C3.AAop C3.AAvop
  split_ifs
  · rfl
  · congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs
    · rw [qminorOp_congr _ _ _ hV he x hx hxG]
    · rfl
  · congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs
    · rw [qminorOp_congr _ _ _ hV he x hx hxG]
    · rfl

theorem loc_of_smoothOnH {f : Mat k r → E} (hf : SmoothOnH (Hpk k r) f) (g : Mat k r) (hg : g ∈ GV k r) :
    Loc (⊤ : ℕ∞) f g := by
  obtain ⟨U, F, a, b, c, d⟩ := hf g hg
  exact ⟨U, F, a, b, c, d⟩

theorem bump_ext {Φ : Mat k r → E} {Dm : Set (Mat k r)} (hDm : IsOpen Dm) (hΦ : Q.SmoothLev k r 0 Dm Φ)
    {p : Mat k r} (hp : p ∈ Dm) (hpG : p ∈ GV k r) :
    ∃ V : Set (Mat k r), IsOpen V ∧ p ∈ V ∧ V ⊆ Dm ∧
      ∃ f : Mat k r → E, SmoothOnH (Hpk k r) f ∧ ∀ x ∈ V, x ∈ GV k r → f x = Φ x := by
  obtain ⟨U, F, hU, hpU, hF, hΦF⟩ := hΦ p ⟨glev0 hpG, hp⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (hU.inter hDm) p ⟨hpU, hp⟩
  let χ : ContDiffBump p := ⟨ε / 3, ε / 2, by positivity, by linarith⟩
  refine ⟨Metric.ball p (ε / 3), Metric.isOpen_ball, Metric.mem_ball_self (by positivity),
    fun x hx => (hball (Metric.ball_subset_ball (by linarith) hx)).2,
    fun x => ((χ x : ℝ) : ℂ) • F x, ?_, ?_⟩
  · intro g₀ hg₀
    by_cases hg : g₀ ∈ U
    · exact ⟨U, fun x => ((χ x : ℝ) : ℂ) • F x, hU, hg,
        ((Complex.ofRealCLM.contDiff.comp χ.contDiff).contDiffOn).smul hF, fun _ _ _ => rfl⟩
    · refine ⟨(tsupport χ)ᶜ, fun _ => 0, (isClosed_tsupport _).isOpen_compl, ?_, contDiffOn_const,
        fun x hx _ => ?_⟩
      · intro hs
        apply hg
        have h2 : g₀ ∈ Metric.closedBall p (ε / 2) := χ.tsupport_eq.subset hs
        exact (hball (Metric.closedBall_subset_ball (by linarith) h2)).1
      · have h0 : χ x = 0 := by
          by_contra h
          exact hx (subset_tsupport χ (Function.mem_support.2 h))
        simp [h0]
  · intro x hx hxG
    have h1 : χ x = 1 := χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hx)
    show ((χ x : ℝ) : ℂ) • F x = Φ x
    rw [h1, Complex.ofReal_one, one_smul]
    exact (hΦF x (hball (Metric.ball_subset_ball (by linarith) hx)).1 (glev0 hxG)).symm

theorem vLet_smul (z z' : Fin (2 * r + k + 1) → ℂ) (i : ℕ) (hi : i ≤ r) (l : C.Letter) (e : Fin 2)
    {f : Mat k r → E} (hf : SmoothOnH (Hpk k r) f) {x : Mat k r} (hx : x ∈ GV k r) (c : ℂ) :
    D.vLet k r z z' i hi l e (fun y => c • f y) x = c • D.vLet k r z z' i hi l e f x := by
  let fW : Wsm (E := E) (Set.univ : Set (Mat k r)) := ⟨f, fun g _ hgG => loc_of_smoothOnH hf g hgG⟩
  have ec : ((c • fW : Wsm (E := E) (Set.univ : Set (Mat k r))) : Mat k r → E) = fun y => c • f y := rfl
  have hA : ∀ m (hm : m ≤ r) u, C3.AAop k r m hm u (fun y => c • f y) x = c • C3.AAop k r m hm u f x := by
    intro m hm u
    have e1 := AAop_eq Set.univ isOpen_univ m hm u (c • fW) x trivial hx
    have e2 := AAop_eq Set.univ isOpen_univ m hm u fW x trivial hx
    rw [ec] at e1
    rw [e1, e2, map_smul]
    rfl
  have hAv : ∀ m (hm : m ≤ r) u, C3.AAvop k r m hm u (fun y => c • f y) x = c • C3.AAvop k r m hm u f x := by
    intro m hm u
    have e1 := AAvop_eq Set.univ isOpen_univ m hm u (c • fW) x trivial hx
    have e2 := AAvop_eq Set.univ isOpen_univ m hm u fW x trivial hx
    rw [ec] at e1
    rw [e1, e2, map_smul]
    rfl
  unfold D.vLet
  split_ifs
  · simp
  · rw [hA, smul_comm]
  · rw [hAv, smul_comm]

theorem vLet_transl (z z' : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hz' : inWb k r z') (i : ℕ) (hi : i ≤ r)
    (l : C.Letter) (e : Fin 2) {f : Mat k r → E} (hf : SmoothOnH (Hpk k r) f) {s s' : Mat k r}
    (hs : s ∈ Sset k r z) (hs' : s' ∈ Sset k r z') {g : Mat k r} (hg : g ∈ GV k r) :
    D.vLet k r z z' i hi l e f (s * g * s') = D.vLet k r z z' i hi l e (fun x => f (s * x * s')) g := by
  have hD : ∀ l', Dmin k r z z' (s * g * s') l' = Dmin k r z z' g l' :=
    fun l' => dInv k r z z' hz hz' s hs s' hs' g l'
  have hX := fun m (hm : m ≤ r) u ell => operators_commute_translations E k r z z' m hm u ell f hz hz' hf s hs s' hs' g hg
  unfold D.vLet
  split_ifs
  · rfl
  · rw [hD, (hX _ _ _ 0).1]
  · rw [hD, (hX _ _ 0 _).2]

theorem smooth_vLet (z z' : Fin (2 * r + k + 1) → ℂ) (i : ℕ) (hi : i ≤ r) (l : C.Letter) (e : Fin 2)
    {Dm : Set (Mat k r)} (hDm : IsOpen Dm) {Φ : Mat k r → E} (hΦ : Q.SmoothLev k r 0 Dm Φ)
    (hne : ∀ g ∈ Dm, Dmin k r z z' g ⟨i, by omega⟩ ≠ 0) :
    Q.SmoothLev k r 0 Dm (D.vLet k r z z' i hi l e Φ) := by
  rintro g₀ ⟨hg₀G', hg₀D⟩
  have hg₀G : g₀ ∈ GV k r := hg₀G'.1
  obtain ⟨V, hV, hpV, hVD, f, hf, hfe⟩ := bump_ext hDm hΦ hg₀D hg₀G
  let fW : Wsm (E := E) (Sd z z' i hi) := ⟨f, fun g _ hgG => loc_of_smoothOnH hf g hgG⟩
  have hL : Loc (⊤ : ℕ∞) (D.vLet k r z z' i hi l e f) g₀ :=
    vLet_mem z z' i hi l e fW g₀ (hne g₀ hg₀D) hg₀G
  have hL2 : Loc (⊤ : ℕ∞) (D.vLet k r z z' i hi l e Φ) g₀ :=
    loc_of_eq hL hV hpV (fun x hx hxG =>
      vLet_congr z z' i hi l e hV (fun y hy hyG => (hfe y hy hyG).symm) x hx hxG)
  obtain ⟨U, F, hU, hgU, hF, hFe⟩ := hL2
  exact ⟨U, F, hU, hgU, hF, fun g hg hgl => hFe g hg hgl.1⟩

theorem one_mem_S (z : Fin (2 * r + k + 1) → ℂ) {n : Mat k r} (hn : n ∈ Nset k r) : n ∈ Sset k r z :=
  ⟨1, BigCellZetaMinors.one_uw z, n, hn, (Matrix.one_mul n).symm⟩

theorem rulesOn_vLet (k r j : ℕ) (hj : j + 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (E : Type)
    [NormedAddCommGroup E] [NormedSpace ℂ E] (Dm : Set (Q.Mx k r)) (Φ : Q.Mx k r → E) (hz : inWb k r z)
    (hz' : inWb k r z') (hDm : IsOpen Dm) (hDJ : Dm ⊆ LevelPointCoordinates.domJ k r j hj z z')
    (hR : LevelPointCoordinates.RulesOn k r j hj z z' Dm Φ) (i : ℕ) (hi : i ≤ j + 1) (hij : i = j ∨ i = j + 1)
    (l : C.Letter) (e : Fin 2) :
    LevelPointCoordinates.RulesOn k r j hj z z' Dm (D.vLet k r z z' i (by omega) l e Φ) := by
  obtain ⟨hS, hRt, hLt⟩ := hR
  have hne : ∀ g ∈ Dm, Dmin k r z z' g ⟨i, by omega⟩ ≠ 0 := by
    intro g hg
    obtain ⟨h1, h2, _⟩ := hDJ hg
    rcases hij with rfl | rfl
    · exact h1
    · exact h2
  refine ⟨smooth_vLet z z' i (by omega) l e hDm hS hne, ?_, ?_⟩
  · rintro g ⟨hgG', hgD⟩ n hn
    have hgnD := (hRt g ⟨hgG', hgD⟩ n hn).1
    refine ⟨hgnD, ?_⟩
    have hgG : g ∈ GV k r := hgG'.1
    have hgnG : g * n ∈ GV k r := AAInvW.inUH_mul hgG hn.1
    obtain ⟨Va, hVa, hpa, _, fa, hfa, hfae⟩ := bump_ext hDm hS hgnD hgnG
    obtain ⟨Vb, hVb, hpb, hVbD, fb, hfb, hfbe⟩ := bump_ext hDm hS hgD hgG
    have hW : IsOpen (Vb ∩ (fun x : Mat k r => x * n) ⁻¹' Va) :=
      hVb.inter (hVa.preimage (continuous_id.matrix_mul continuous_const))
    calc D.vLet k r z z' i _ l e Φ (g * n) = D.vLet k r z z' i _ l e fa (1 * g * n) := by
          rw [Matrix.one_mul]
          exact vLet_congr z z' i _ l e hVa (fun y hy hyG => (hfae y hy hyG).symm) _ hpa hgnG
      _ = D.vLet k r z z' i _ l e (fun x => fa (1 * x * n)) g :=
          vLet_transl z z' hz hz' i _ l e hfa (one_mem_S z WeylGroupFacts.mem_n_one) (one_mem_S z' hn) hgG
      _ = D.vLet k r z z' i _ l e (fun x => psi k r z' cStd n • fb x) g := by
          refine vLet_congr z z' i _ l e hW (fun y hy hyG => ?_) g ⟨hpb, hpa⟩ hgG
          rw [Matrix.one_mul, hfae (y * n) hy.2 (AAInvW.inUH_mul hyG hn.1),
            (hRt y ⟨glev0 hyG, hVbD hy.1⟩ n hn).2, hfbe y hy.1 hyG]
      _ = psi k r z' cStd n • D.vLet k r z z' i _ l e fb g := vLet_smul z z' i _ l e hfb hgG _
      _ = psi k r z' cStd n • D.vLet k r z z' i _ l e Φ g := by
          rw [vLet_congr z z' i _ l e hVb (fun y hy hyG => hfbe y hy hyG) g hpb hgG]
  · rintro g ⟨hgG', hgD⟩ a
    have hgnD := (hLt g ⟨hgG', hgD⟩ a).1
    refine ⟨hgnD, ?_⟩
    set s := LevelPointCoordinates.nL k r j hj a with hs_def
    have hsN : s ∈ Nset k r := nL_mem j hj a
    have hgG : g ∈ GV k r := hgG'.1
    have hsgG : s * g ∈ GV k r := AAInvW.inUH_mul hsN.1 hgG
    obtain ⟨Va, hVa, hpa, _, fa, hfa, hfae⟩ := bump_ext hDm hS hgnD hsgG
    obtain ⟨Vb, hVb, hpb, hVbD, fb, hfb, hfbe⟩ := bump_ext hDm hS hgD hgG
    have hW : IsOpen (Vb ∩ (fun x : Mat k r => s * x) ⁻¹' Va) :=
      hVb.inter (hVa.preimage (continuous_const.matrix_mul continuous_id))
    calc D.vLet k r z z' i _ l e Φ (s * g) = D.vLet k r z z' i _ l e fa (s * g * 1) := by
          rw [Matrix.mul_one]
          exact vLet_congr z z' i _ l e hVa (fun y hy hyG => (hfae y hy hyG).symm) _ hpa hsgG
      _ = D.vLet k r z z' i _ l e (fun x => fa (s * x * 1)) g :=
          vLet_transl z z' hz hz' i _ l e hfa (one_mem_S z hsN) (one_mem_S z' WeylGroupFacts.mem_n_one) hgG
      _ = D.vLet k r z z' i _ l e (fun x => psi k r z cStd s • fb x) g := by
          refine vLet_congr z z' i _ l e hW (fun y hy hyG => ?_) g ⟨hpb, hpa⟩ hgG
          rw [Matrix.mul_one, hfae (s * y) hy.2 (AAInvW.inUH_mul hsN.1 hyG),
            (hLt y ⟨glev0 hyG, hVbD hy.1⟩ a).2, hfbe y hy.1 hyG]
      _ = psi k r z cStd s • D.vLet k r z z' i _ l e fb g := vLet_smul z z' i _ l e hfb hgG _
      _ = psi k r z cStd s • D.vLet k r z z' i _ l e Φ g := by
          rw [vLet_congr z z' i _ l e hVb (fun y hy hyG => hfbe y hy hyG) g hpb hgG]

end Formalism.FourierDecayAlt.P.SingleEntryHermitianProducts

namespace Formalism.FourierDecayAlt.P

theorem rules_closed : Formalism.FourierDecayAlt.P.LevelPointCoordinates.RulesClosed :=
  fun k r j hj z z' E _ _ Dm Φ hz hz' hDm hDJ hR i hi hij l e =>
    SingleEntryHermitianProducts.rulesOn_vLet k r j hj z z' E Dm Φ hz hz' hDm hDJ hR i hi hij l e

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.RdVOfEq
open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.HeadLetterLemmas

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.PBG

variable {k r : ℕ}


open Formalism.FourierDecayAlt.Q.QRR in
theorem rdV_of_eq {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (z' : Fin (2 * r + k + 1) → ℂ)
    (hz : inWb k r z') (Φ : Q.Mx k r → E) (g : Q.Mx k r)
    (hΦ : ∀ n ∈ QuantumDeterminants.Nset k r, Φ (g * n) = psi k r z' cStd n • Φ g)
    (l : Fin r) (X : Q.Mx k r) (hX : Pat k r l X) (hS : dag k r X = -X) :
    RdV X Φ g = (ell k r z' X - star (ell k r z' X)) • Φ g := by
  unfold RdV
  have hfun : (fun t : ℝ => Φ (g * NormedSpace.exp ((t : ℂ) • X))) =
      fun t : ℝ => psi k r z' cStd (NormedSpace.exp ((t : ℂ) • X)) • Φ g := by
    funext t
    apply hΦ
    apply (exp_mem_nlev (pat_smul _ hX) _).1
    rw [dag_smul, hS, Complex.star_def, Complex.conj_ofReal, smul_neg]
  rw [hfun]
  exact ((hasDerivAt_psi z' hz X).smul_const (Φ g)).deriv

theorem _root_.Formalism.FourierDecayAlt.P.rule_of_eq : LevelPointCoordinates.RuleOfEq := by
  intro E _ _ k r z' Φ g hz hΦ p q hpq
  obtain ⟨l, hl⟩ := exists_pat p q hpq
  have hr : 1 ≤ r := by have := l.isLt; omega
  set Z : B.Mat k r := Matrix.single p q (1 : ℂ) with hZ
  have h1 := rdV_of_eq z' hz Φ g hΦ l _ (Formalism.FourierDecayAlt.Q.QRR.pat_hpart1 hl) (Formalism.FourierDecayAlt.Q.QRR.skew_hpart1 Z)
  have h2 := rdV_of_eq z' hz Φ g hΦ l _ (Formalism.FourierDecayAlt.Q.QRR.pat_hpart2 hl) (Formalism.FourierDecayAlt.Q.QRR.skew_hpart2 Z)
  set Λ : B.Mat k r → ℂ := fun X => ∑ a, ∑ b, X a b * C3.dpsiP k r z' a b with hΛ
  have hΛ1 : ell k r z' (hpart1 (Hpk k r) Z) - star (ell k r z' (hpart1 (Hpk k r) Z)) = Λ (hpart1 (Hpk k r) Z) := by
    rw [← dEll_eq_ell _ _ hr]
    exact (Formalism.FourierDecayAlt.P.dpsi_is_derivation k r z' _ hr hz (Formalism.FourierDecayAlt.P.PBG.hermitian_part_one_mem_lie Z)
      (pat_inNp (Formalism.FourierDecayAlt.Q.QRR.pat_hpart1 hl))).symm
  have hΛ2 : ell k r z' (hpart2 (Hpk k r) Z) - star (ell k r z' (hpart2 (Hpk k r) Z)) = Λ (hpart2 (Hpk k r) Z) := by
    rw [← dEll_eq_ell _ _ hr]
    exact (Formalism.FourierDecayAlt.P.dpsi_is_derivation k r z' _ hr hz (Formalism.FourierDecayAlt.P.PBG.hermitian_part_two_mem_lie Z)
      (pat_inNp (Formalism.FourierDecayAlt.Q.QRR.pat_hpart2 hl))).symm
  have hsum : hpart1 (Hpk k r) Z + Complex.I • hpart2 (Hpk k r) Z = Z := by
    unfold hpart1 hpart2
    rw [smul_smul]
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    have : Complex.I * (1 / (2 * Complex.I)) = 1 / 2 := by field_simp
    rw [this, ← smul_add]
    rw [show Z - (Hpk k r)⁻¹ * Zᴴ * Hpk k r + (Z + (Hpk k r)⁻¹ * Zᴴ * Hpk k r) = (2 : ℂ) • Z by
      rw [two_smul]; abel]
    rw [smul_smul]; norm_num
  have hΛZ : Λ (hpart1 (Hpk k r) Z) + Complex.I * Λ (hpart2 (Hpk k r) Z) = C3.dpsiP k r z' p q := by
    have hlin : Λ (hpart1 (Hpk k r) Z) + Complex.I * Λ (hpart2 (Hpk k r) Z) =
        Λ (hpart1 (Hpk k r) Z + Complex.I • hpart2 (Hpk k r) Z) := by
      simp only [hΛ, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
        Finset.mul_sum, mul_assoc]
    rw [hlin, hsum]
    simp only [hΛ, hZ, Matrix.single_apply]
    rw [Finset.sum_eq_single p, Finset.sum_eq_single q]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
    · intro a _ ha; apply Finset.sum_eq_zero; intro b _; simp [Ne.symm ha]
    · simp
  show EabH (Hpk k r) p q Φ g = _
  unfold EabH
  rw [h1, h2, hΛ1, hΛ2, smul_smul, ← add_smul, hΛZ]

end Formalism.FourierDecayAlt.P.HeadLetterLemmas
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHL2
open Matrix
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutHL

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates

section defs

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def Hyp (k r j : ℕ) (hj : j + 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (Dm : Set (Q.Mx k r)) (Φ : Q.Mx k r → E)
    (Z : Matrix (Fin j) (Fin j) ℂ) (γ : B.Mat k (r - (j + 1))) (τ : ℂ) : Prop :=
  inWb k r z ∧ inWb k r z' ∧ IsOpen Dm ∧ Dm ⊆ domJ k r j hj z z' ∧ RulesOn k r j hj z z' Dm Φ ∧
    Z.det ≠ 0 ∧ τ ≠ 0 ∧ γ ∈ B.GV k (r - (j + 1)) ∧ x0 k r j hj Z τ γ ∈ Dm

def Eq1 (k r j : ℕ) (hj : j + 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (Φ : Q.Mx k r → E)
    (Z : Matrix (Fin j) (Fin j) ℂ) (γ : B.Mat k (r - (j + 1))) (τ : ℂ) (Y : ℝ) : Prop :=
  D.vLet k r z z' (j + 1) hj (true, Y) 0 Φ (x0 k r j hj Z τ γ) =
    ((Y : ℂ) + levelZeroKernel k r j) • D.vLet k r z z' j (by omega) (true, Y) 0 Φ (x0 k r j hj Z τ γ) +
      τ • PBP.dz (fun τ' => D.vLet k r z z' j (by omega) (true, Y) 0 Φ (x0 k r j hj Z τ' γ)) τ -
      τ • D.vLet k r z z' j (by omega) (true, Y) 1 Φ (x0 k r j hj Z τ γ)

def Eq2 (k r j : ℕ) (hj : j + 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (Φ : Q.Mx k r → E)
    (Z : Matrix (Fin j) (Fin j) ℂ) (γ : B.Mat k (r - (j + 1))) (τ : ℂ) (Y : ℝ) : Prop :=
  D.vLet k r z z' (j + 1) hj (true, Y) 1 Φ (x0 k r j hj Z τ γ) =
    τ⁻¹ • D.vLet k r z z' j (by omega) (true, Y) 0 Φ (x0 k r j hj Z τ γ)

def Eq3 (k r j : ℕ) (hj : j + 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (Φ : Q.Mx k r → E)
    (Z : Matrix (Fin j) (Fin j) ℂ) (γ : B.Mat k (r - (j + 1))) (τ : ℂ) (Y : ℝ) : Prop :=
  D.vLet k r z z' (j + 1) hj (false, Y) 0 Φ (x0 k r j hj Z τ γ) =
    ((Y : ℂ) - levelZeroKernel k r j) • D.vLet k r z z' j (by omega) (false, Y) 0 Φ (x0 k r j hj Z τ γ) -
      conj τ • PBP.dzb (fun τ' => D.vLet k r z z' j (by omega) (false, Y) 0 Φ (x0 k r j hj Z τ' γ)) τ -
      conj τ • D.vLet k r z z' j (by omega) (false, Y) 1 Φ (x0 k r j hj Z τ γ)

def Eq4 (k r j : ℕ) (hj : j + 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (Φ : Q.Mx k r → E)
    (Z : Matrix (Fin j) (Fin j) ℂ) (γ : B.Mat k (r - (j + 1))) (τ : ℂ) (Y : ℝ) : Prop :=
  D.vLet k r z z' (j + 1) hj (false, Y) 1 Φ (x0 k r j hj Z τ γ) =
    (conj τ)⁻¹ • D.vLet k r z z' j (by omega) (false, Y) 0 Φ (x0 k r j hj Z τ γ)

end defs

def Comp1 : Prop :=
  ∀ (k r j : ℕ) (hj : j + 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (E : Type) [NormedAddCommGroup E]
    [NormedSpace ℂ E] (Dm : Set (Q.Mx k r)) (Φ : Q.Mx k r → E) (Z : Matrix (Fin j) (Fin j) ℂ)
    (γ : B.Mat k (r - (j + 1))) (τ : ℂ), Hyp k r j hj z z' Dm Φ Z γ τ →
    ∀ Y : ℝ, Eq2 k r j hj z z' Φ Z γ τ Y ∧ Eq4 k r j hj z z' Φ Z γ τ Y

def PlusPos : Prop :=
  ∀ (k r j : ℕ) (hj : j + 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (E : Type) [NormedAddCommGroup E]
    [NormedSpace ℂ E] (Dm : Set (Q.Mx k r)) (Φ : Q.Mx k r → E) (Z : Matrix (Fin j) (Fin j) ℂ)
    (γ : B.Mat k (r - (j + 1))) (τ : ℂ), 1 ≤ j → Hyp k r j hj z z' Dm Φ Z γ τ →
    ∀ Y : ℝ, Eq1 k r j hj z z' Φ Z γ τ Y

def PlusZero : Prop :=
  ∀ (k r j : ℕ) (hj : j + 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (E : Type) [NormedAddCommGroup E]
    [NormedSpace ℂ E] (Dm : Set (Q.Mx k r)) (Φ : Q.Mx k r → E) (Z : Matrix (Fin j) (Fin j) ℂ)
    (γ : B.Mat k (r - (j + 1))) (τ : ℂ), j = 0 → Hyp k r j hj z z' Dm Φ Z γ τ →
    ∀ Y : ℝ, Eq1 k r j hj z z' Φ Z γ τ Y

def MinusPos : Prop :=
  ∀ (k r j : ℕ) (hj : j + 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (E : Type) [NormedAddCommGroup E]
    [NormedSpace ℂ E] (Dm : Set (Q.Mx k r)) (Φ : Q.Mx k r → E) (Z : Matrix (Fin j) (Fin j) ℂ)
    (γ : B.Mat k (r - (j + 1))) (τ : ℂ), 1 ≤ j → Hyp k r j hj z z' Dm Φ Z γ τ →
    ∀ Y : ℝ, Eq3 k r j hj z z' Φ Z γ τ Y

def MinusZero : Prop :=
  ∀ (k r j : ℕ) (hj : j + 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (E : Type) [NormedAddCommGroup E]
    [NormedSpace ℂ E] (Dm : Set (Q.Mx k r)) (Φ : Q.Mx k r → E) (Z : Matrix (Fin j) (Fin j) ℂ)
    (γ : B.Mat k (r - (j + 1))) (τ : ℂ), j = 0 → Hyp k r j hj z z' Dm Φ Z γ τ →
    ∀ Y : ℝ, Eq3 k r j hj z z' Φ Z γ τ Y

theorem headLetter_of (h1 : Comp1) (hPP : PlusPos) (hPZ : PlusZero) (hMP : MinusPos) (hMZ : MinusZero) :
    LevelPointCoordinates.HeadLetter := by
  intro k r j hj z z' E _ _ Dm Φ hz hz' hD hDs hR Z γ τ hZ hτ hγ hx Y
  have hH : Hyp k r j hj z z' Dm Φ Z γ τ := ⟨hz, hz', hD, hDs, hR, hZ, hτ, hγ, hx⟩
  obtain ⟨c2, c4⟩ := h1 k r j hj z z' E Dm Φ Z γ τ hH Y
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · exact ⟨hPZ k r j hj z z' E Dm Φ Z γ τ h0 hH Y, c2, hMZ k r j hj z z' E Dm Φ Z γ τ h0 hH Y, c4⟩
  · exact ⟨hPP k r j hj z z' E Dm Φ Z γ τ hpos hH Y, c2, hMP k r j hj z z' E Dm Φ Z γ τ hpos hH Y, c4⟩

def NormalFormsAtBasePoint : Prop :=
  ∀ (k r j : ℕ) (hj : j + 1 ≤ r) (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ) (γ : B.Mat k (r - (j + 1))),
    Z.det ≠ 0 → τ ≠ 0 → γ ∈ B.GV k (r - (j + 1)) →
    (∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val < j + 1 →
      PBG.xi0 (x0 k r j hj Z τ γ) a p = if p.val < j + 1 then C3.Zb j 1 Z τ a.val p.val else 0) ∧
    (∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val < j + 1 →
      PBG.y0 (x0 k r j hj Z τ γ) a p =
        if r + k < p.val ∧ 2 * r + k - p.val < j + 1 then star (C3.Zb j 1 Z τ a.val (2 * r + k - p.val)) else 0)

def LeadingMinorsAtBasePoint : Prop :=
  ∀ (k r j : ℕ) (hj : j + 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ)
    (γ : B.Mat k (r - (j + 1))), Z.det ≠ 0 → τ ≠ 0 → γ ∈ B.GV k (r - (j + 1)) →
    Dmin k r z z' (x0 k r j hj Z τ γ) ⟨j, by omega⟩ = Z.det ∧
      Dmin k r z z' (x0 k r j hj Z τ γ) ⟨j + 1, by omega⟩ = Z.det * τ

def LeftActionRuleAtBasePoint : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r j : ℕ) (hj : j + 1 ≤ r)
    (z : Fin (2 * r + k + 1) → ℂ) (Dm : Set (Q.Mx k r)) (Ψ : Q.Mx k r → E) (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ)
    (γ : B.Mat k (r - (j + 1))), 1 ≤ j → inWb k r z → IsOpen Dm → Q.SmoothLev k r 0 Dm Ψ → Z.det ≠ 0 → τ ≠ 0 →
    γ ∈ B.GV k (r - (j + 1)) → x0 k r j hj Z τ γ ∈ Dm →
    (∀ a : Fin j → ℂ, Ψ (nL k r j hj a * x0 k r j hj Z τ γ) = psi k r z cStd (nL k r j hj a) • Ψ (x0 k r j hj Z τ γ)) →
    ∀ b : Fin j, Q.EH k r (eI k r ⟨j, by omega⟩) (eI k r ⟨b, by omega⟩) Ψ (x0 k r j hj Z τ γ) =
      (τ * Z⁻¹ b ⟨j - 1, by have := b.isLt; omega⟩) • Ψ (x0 k r j hj Z τ γ)

def TorusDirectionAtBasePoint : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r j : ℕ) (hj : j + 1 ≤ r)
    (Dm : Set (Q.Mx k r)) (Ψ : Q.Mx k r → E) (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ)
    (γ : B.Mat k (r - (j + 1))), IsOpen Dm → Q.SmoothLev k r 0 Dm Ψ → Z.det ≠ 0 → τ ≠ 0 →
    γ ∈ B.GV k (r - (j + 1)) → x0 k r j hj Z τ γ ∈ Dm →
    Q.EH k r (eI k r ⟨j, by omega⟩) (eI k r ⟨j, by omega⟩) Ψ (x0 k r j hj Z τ γ) =
      τ • PBP.dz (fun τ' => Ψ (x0 k r j hj Z τ' γ)) τ

def ConjugateActionRuleAtBasePoint : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r j : ℕ) (hj : j + 1 ≤ r)
    (z : Fin (2 * r + k + 1) → ℂ) (Dm : Set (Q.Mx k r)) (Ψ : Q.Mx k r → E) (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ)
    (γ : B.Mat k (r - (j + 1))), 1 ≤ j → inWb k r z → IsOpen Dm → Q.SmoothLev k r 0 Dm Ψ → Z.det ≠ 0 → τ ≠ 0 →
    γ ∈ B.GV k (r - (j + 1)) → x0 k r j hj Z τ γ ∈ Dm →
    (∀ a : Fin j → ℂ, Ψ (nL k r j hj a * x0 k r j hj Z τ γ) = psi k r z cStd (nL k r j hj a) • Ψ (x0 k r j hj Z τ γ)) →
    ∀ b : Fin j, Q.EH k r (esI k r ⟨b, by omega⟩) (esI k r ⟨j, by omega⟩) Ψ (x0 k r j hj Z τ γ) =
      (conj τ * conj (Z⁻¹ b ⟨j - 1, by have := b.isLt; omega⟩)) • Ψ (x0 k r j hj Z τ γ)

def ConjugateTorusDirectionAtBasePoint : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r j : ℕ) (hj : j + 1 ≤ r)
    (Dm : Set (Q.Mx k r)) (Ψ : Q.Mx k r → E) (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ)
    (γ : B.Mat k (r - (j + 1))), IsOpen Dm → Q.SmoothLev k r 0 Dm Ψ → Z.det ≠ 0 → τ ≠ 0 →
    γ ∈ B.GV k (r - (j + 1)) → x0 k r j hj Z τ γ ∈ Dm →
    Q.EH k r (esI k r ⟨j, by omega⟩) (esI k r ⟨j, by omega⟩) Ψ (x0 k r j hj Z τ γ) =
      -(conj τ • PBP.dzb (fun τ' => Ψ (x0 k r j hj Z τ' γ)) τ)

def FrozenX : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (k r j : ℕ) (hj : j + 1 ≤ r)
    (Eu : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (Z : Matrix (Fin j) (Fin j) ℂ) (τ τ' u : ℂ)
    (γ : B.Mat k (r - (j + 1))), GlRel Eu → Z.det ≠ 0 → τ ≠ 0 → τ' ≠ 0 → γ ∈ B.GV k (r - (j + 1)) →
    C3.AAx k r Eu (PBG.xi0 (x0 k r j hj Z τ' γ)) j (by omega) u =
        C3.AAx k r Eu (PBG.xi0 (x0 k r j hj Z τ γ)) j (by omega) u ∧
      Eu (eI k r ⟨j, by omega⟩) (eI k r ⟨j, by omega⟩) * C3.AAx k r Eu (PBG.xi0 (x0 k r j hj Z τ γ)) j (by omega) u =
        C3.AAx k r Eu (PBG.xi0 (x0 k r j hj Z τ γ)) j (by omega) u * Eu (eI k r ⟨j, by omega⟩) (eI k r ⟨j, by omega⟩)

def FrozenV : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (k r j : ℕ) (hj : j + 1 ≤ r)
    (Eu : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (Z : Matrix (Fin j) (Fin j) ℂ) (τ τ' ℓ : ℂ)
    (γ : B.Mat k (r - (j + 1))), GlRel Eu → Z.det ≠ 0 → τ ≠ 0 → τ' ≠ 0 → γ ∈ B.GV k (r - (j + 1)) →
    C3.AAv k r Eu (PBG.y0 (x0 k r j hj Z τ' γ)) j (by omega) ℓ =
        C3.AAv k r Eu (PBG.y0 (x0 k r j hj Z τ γ)) j (by omega) ℓ ∧
      Eu (esI k r ⟨j, by omega⟩) (esI k r ⟨j, by omega⟩) * C3.AAv k r Eu (PBG.y0 (x0 k r j hj Z τ γ)) j (by omega) ℓ =
        C3.AAv k r Eu (PBG.y0 (x0 k r j hj Z τ γ)) j (by omega) ℓ * Eu (esI k r ⟨j, by omega⟩) (esI k r ⟨j, by omega⟩)

def Comp1OfParts : Prop := NormalFormsAtBasePoint → Comp1

def PlusPosOfParts : Prop := NormalFormsAtBasePoint → LeadingMinorsAtBasePoint → LeftActionRuleAtBasePoint → TorusDirectionAtBasePoint → FrozenX → PlusPos

def PlusZeroOfParts : Prop := NormalFormsAtBasePoint → LeadingMinorsAtBasePoint → TorusDirectionAtBasePoint → PlusZero

def MinusPosOfParts : Prop := NormalFormsAtBasePoint → LeadingMinorsAtBasePoint → ConjugateActionRuleAtBasePoint → ConjugateTorusDirectionAtBasePoint → FrozenV → MinusPos

def MinusZeroOfParts : Prop := NormalFormsAtBasePoint → LeadingMinorsAtBasePoint → ConjugateTorusDirectionAtBasePoint → MinusZero

theorem headLetter_of_leaves (hNf : NormalFormsAtBasePoint) (hDm : LeadingMinorsAtBasePoint) (hL : LeftActionRuleAtBasePoint) (hT : TorusDirectionAtBasePoint) (hSL : ConjugateActionRuleAtBasePoint)
    (hST : ConjugateTorusDirectionAtBasePoint) (hFX : FrozenX) (hFV : FrozenV) (h1 : Comp1OfParts) (hPP : PlusPosOfParts)
    (hPZ : PlusZeroOfParts) (hMP : MinusPosOfParts) (hMZ : MinusZeroOfParts) : LevelPointCoordinates.HeadLetter :=
  headLetter_of (h1 hNf) (hPP hNf hDm hL hT hFX) (hPZ hNf hDm hT) (hMP hNf hDm hSL hST hFV) (hMZ hNf hDm hST)

end Formalism.FourierDecayAlt.P.CutHL
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.ExpFromBlocks
open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.WirtingerOperators.LeviExponential

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

def fbHom (m n : Type*) [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] :
    Matrix m m ℂ × Matrix n n ℂ →+* Matrix (m ⊕ n) (m ⊕ n) ℂ where
  toFun p := Matrix.fromBlocks p.1 0 0 p.2
  map_one' := Matrix.fromBlocks_one
  map_mul' p q := by simp [Matrix.fromBlocks_multiply]
  map_zero' := by simp
  map_add' p q := by simp [Matrix.fromBlocks_add]

set_option backward.isDefEq.respectTransparency false in
theorem exp_reindex (e : m ≃ n) (M : Matrix m m ℂ) :
    NormedSpace.exp (Matrix.reindex e e M) = Matrix.reindex e e (NormedSpace.exp M) := by
  have hc : Continuous fun M : Matrix m m ℂ => Matrix.reindexAlgEquiv ℂ ℂ e M := by
    simp only [Matrix.coe_reindexAlgEquiv]; exact continuous_id.matrix_reindex e e
  open scoped Matrix.Norms.Operator in
  have h := NormedSpace.map_exp (Matrix.reindexAlgEquiv ℂ ℂ e) hc M
  simp only [Matrix.coe_reindexAlgEquiv] at h
  exact h.symm

set_option backward.isDefEq.respectTransparency false in
theorem exp_fromBlocks (A : Matrix m m ℂ) (D : Matrix n n ℂ) :
    NormedSpace.exp (Matrix.fromBlocks A 0 0 D) = Matrix.fromBlocks (NormedSpace.exp A) 0 0 (NormedSpace.exp D) := by
  have hc : Continuous fun p : Matrix m m ℂ × Matrix n n ℂ => fbHom m n p := by
    show Continuous fun p : Matrix m m ℂ × Matrix n n ℂ => Matrix.fromBlocks p.1 0 0 p.2
    exact Continuous.matrix_fromBlocks continuous_fst continuous_const continuous_const continuous_snd
  open scoped Matrix.Norms.Operator in
  have h := NormedSpace.map_exp (fbHom m n) hc (A, D)
  open scoped Matrix.Norms.Operator in
  have h1 := Prod.fst_exp (A, D)
  open scoped Matrix.Norms.Operator in
  have h2 := Prod.snd_exp (A, D)
  change Matrix.fromBlocks _ 0 0 _ = NormedSpace.exp (Matrix.fromBlocks _ 0 0 _) at h
  rw [h1, h2] at h
  exact h.symm

end Formalism.FourierDecayAlt.P.WirtingerOperators.LeviExponential
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDBeta
open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

theorem radial_beta_identity : RDBeta := by
  intro k r Wp Wq _ _ _ _ _ _ D μ hμ
  obtain ⟨C1, hC1, hpair⟩ := Formalism.FourierDecayAlt.P.JCx2.rb_pairAt D μ hμ
  refine ⟨(C1 : ℂ), by exact_mod_cast hC1.ne', fun F H Φ Ψ hF hH hΦ hΨ c => ?_⟩
  have h := Formalism.FourierDecayAlt.P.JCx2.rb_main D μ C1 hpair (n := 0) (fun _ => F) (fun _ => H) (fun _ => Φ) (fun _ => Ψ)
    (fun _ => hF) (fun _ => hH) (fun _ => hΦ) (fun _ => hΨ)
  have hsum : ∑ _a : Wd.Ix (Fin 0), B.beta D F H = B.beta D F H := by simp
  rw [hsum] at h
  rw [← h]
  unfold LocFacts₂ P5.form
  refine integral_congr_ae (Filter.Eventually.of_forall fun c' => ?_)
  have hg : glue (0 : Fin (r + 1)) c c' = glue 0 0 c' := by
    funext l
    simp only [glue]
    have h0 : ((0 : Fin (r + 1)) : ℕ) ≤ (l : ℕ) := Nat.zero_le _
    rw [dite_eq_left h0, dite_eq_left h0]
  simp only [hg, Finset.univ_unique, Finset.sum_singleton]

end Formalism.FourierDecayAlt.P.CutSE
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.DerivativeKeepsCharacter
open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.HeadLetterLemmas

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.Qx5

theorem nL_glev0 {k r j : ℕ} (hj : j + 1 ≤ r) (a : Fin j → ℂ) : LevelPointCoordinates.nL k r j hj a ∈ Q.Glev k r 0 :=
  ⟨SingleEntryHermitianProducts.nL_uh j hj a, fun b hb => absurd hb (by simp)⟩

theorem derivative_keeps_character {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {k r j : ℕ} (hj : j + 1 ≤ r)
    (z : Fin (2 * r + k + 1) → ℂ) {Dm : Set (Q.Mx k r)} (hD : IsOpen Dm)
    (hDm : ∀ g ∈ Q.Glev k r 0 ∩ Dm, ∀ a : Fin j → ℂ, LevelPointCoordinates.nL k r j hj a * g ∈ Dm)
    (p q : Fin (2 * r + k + 1)) (w : VS k r 0 Dm E)
    (hw : ∀ g ∈ Q.Glev k r 0 ∩ Dm, ∀ a : Fin j → ℂ,
      (w : Q.Mx k r → E) (LevelPointCoordinates.nL k r j hj a * g) = psi k r z cStd (LevelPointCoordinates.nL k r j hj a) • (w : Q.Mx k r → E) g)
    (g : Q.Mx k r) (hg : g ∈ Q.Glev k r 0 ∩ Dm) (a : Fin j → ℂ) :
    ((PBG.E0 hD p q w : VS k r 0 Dm E) : Q.Mx k r → E) (LevelPointCoordinates.nL k r j hj a * g) =
      psi k r z cStd (LevelPointCoordinates.nL k r j hj a) • ((PBG.E0 hD p q w : VS k r 0 Dm E) : Q.Mx k r → E) g := by
  have hng : LevelPointCoordinates.nL k r j hj a * g ∈ Q.Glev k r 0 ∩ Dm :=
    ⟨Qx3.glev_mul (nL_glev0 hj a) hg.1, hDm g hg a⟩
  set c := psi k r z cStd (LevelPointCoordinates.nL k r j hj a) with hc
  have hG := Qx2.good_eh (E := E) (k := k) (r := r) (i := 0) hD (PBG.c0 p) (PBG.c0 q)
  simp only [PBG.position_level_zero_coord] at hG
  unfold PBG.E0
  rw [ev_E hD _ _ w hng, ev_E hD _ _ w hg, PBG.position_level_zero_coord, PBG.position_level_zero_coord]
  rw [← WeylCellAction.eH_left (LevelPointCoordinates.nL k r j hj a) p q (w : Q.Mx k r → E) g]
  rw [hG.loc (fun x => (w : Q.Mx k r → E) (LevelPointCoordinates.nL k r j hj a * x)) (fun x => (fun _ => (0 : E)) x + c • (w : Q.Mx k r → E) x)
    (fun x hx => by simp only [zero_add]; exact hw x hx a) g hg]
  rw [hG.lin (fun _ => (0 : E)) (w : Q.Mx k r → E) c Qx2.smooth_zero w.2.1 g hg]
  have h0 : Q.EH k r p q (fun _ : Q.Mx k r => (0 : E)) g = 0 := by
    simp [Q.EH, EabH, RdV]
  rw [h0, zero_add]

theorem _root_.Formalism.FourierDecayAlt.P.adjoin_lower_unipotent : LevelPointCoordinates.AdjoinNL := by
  intro E _ _ k r j hj z Dm hD hDm x hx
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨⟨p, q⟩, rfl⟩ := hy
    intro v hv g hg a
    exact derivative_keeps_character hj z hD hDm p q v hv g hg a
  | algebraMap c =>
    intro v hv g hg a
    simp only [Module.algebraMap_end_apply, Submodule.coe_smul, Pi.smul_apply]
    rw [hv g hg a, smul_comm]
  | add y1 y2 _ _ h1 h2 =>
    intro v hv g hg a
    simp only [LinearMap.add_apply, Submodule.coe_add, Pi.add_apply]
    rw [h1 v hv g hg a, h2 v hv g hg a, smul_add]
  | mul y1 y2 _ _ h1 h2 =>
    intro v hv
    exact h1 _ (h2 v hv)

end Formalism.FourierDecayAlt.P.HeadLetterLemmas
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.VecVNonloc
namespace Formalism.FourierDecayAlt.P.GermRateSplit

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate InnerProductSpace

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

def hsLE {Wp' Wq' : Type} [NormedAddCommGroup Wp'] [InnerProductSpace ℂ Wp'] [NormedAddCommGroup Wq']
    [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wp'] [FiniteDimensional ℂ Wq'] (Eρ : Wp' →L[ℂ] Wp') :
    (Wq' →L[ℂ] Wp') →L[ℂ] PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq') => Wp') :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => B.hsVec (Eρ.comp X)
      map_add' := fun X Y => by rw [ContinuousLinearMap.comp_add]; unfold B.hsVec; rfl
      map_smul' := fun c X => by rw [ContinuousLinearMap.comp_smul]; exact PBL.hsVec_smul c _ }

theorem hsLE_apply {Wp' Wq' : Type} [NormedAddCommGroup Wp'] [InnerProductSpace ℂ Wp'] [NormedAddCommGroup Wq']
    [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wp'] [FiniteDimensional ℂ Wq'] (Eρ : Wp' →L[ℂ] Wp')
    (X : Wq' →L[ℂ] Wp') : hsLE Eρ X = B.hsVec (Eρ.comp X) := rfl

theorem vecV_nonloc {P : M.Par} {Wp' Wq' : Type} [NormedAddCommGroup Wp'] [InnerProductSpace ℂ Wp']
    [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] (Bs : B.RealPlaceData P.k P.r Wp' Wq')
    (ν' : Fin (2 * P.r + P.k + 1) → ℂ) (m₀ : B.Mat P.k P.r) (F : B.Mat P.k P.r → (Wq' →L[ℂ] Wp')) (Q : C.LPt)
    (hQ : ¬ D.IsLocPt Q (P.r + 1)) : D.vecV Bs ν' m₀ F Q = 0 := by
  unfold D.vecV
  rw [dite_eq_right (fun h => hQ h.1)]

theorem gN_top_gram {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
    {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}
    (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (hF : ∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (a : List C.Letter)
    (ha : D.AdmAt S v a) :
    ∃ (I : Type) (_ : Fintype I) (c : I → ℝ) (Fi : I → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
      (L : I → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)) →L[ℂ] PBL.HV S v),
      (∀ i, 0 ≤ c i) ∧ (∀ i, KB.CptCoef (p v).T.base (Fi i)) ∧
      ∀ P Q : C.LPt, KB.gN (PBL.setC S p F) v ε (S.G.r + 1) a P Q =
        ∑ i, (c i : ℂ) * ⟪(omN S a.length Q : ℂ) • L i ((p v).V (Fi i) (PBL.stdS S Q)),
          (omN S a.length P : ℂ) • L i ((p v).V (Fi i) (PBL.stdS S P))⟫_ℂ := by
  classical
  have hgpos := PBL.g_pos_of_built hB
  have hTT := (PBL.pdG_of_built hB v).2
  have hB' := hB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hGr, -, -, -, -, hv⟩ := hB'
  obtain ⟨hl0, hInD, -, -, -⟩ := hv v
  have hcutw : KB.CutWord (D.parOf S v) (p v).l0 a := by
    obtain ⟨w, hw⟩ := ha
    rw [hl0, ← hw]
    exact PBD.cutWord_of_adm S hGr (PBCut.cutInside_of_built hB) w v
  have hInD' : KB.InDDplus2 (D.parOf S v) (p v).l0 (p v).T.base Cb (p v).Θ := by rw [hl0]; exact hInD
  have hTh : ∀ e : Wd.Ix (Fin a.length), ∃ F' : B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)),
      KB.CptCoef (p v).T.base F' ∧ ∀ Q, (p v).V ((p v).Θ.Θ a e (F v ε)) Q = (p v).V F' Q := by
    intro e
    obtain ⟨F', hF', -, hV⟩ := Formalism.FourierDecayAlt.P.theta_compact_support _ _ (D.parOf S v) (p v) (F v ε) a e Cb hInD'
      (hF v ε hε) hcutw
    exact ⟨F', hF', hV⟩
  choose Fe hFe hVe using hTh
  have hΓ : PBL.ΓS S (S.G.r + 1) = 1 := by simp [PBL.ΓS, D.GamLev]
  refine ⟨Wd.Ix (Fin a.length) × M.Ty (D.parOf S v), inferInstance,
    fun i => PBL.del2 S p v a i.1 i.2 / (PBL.ΓS S (S.G.r + 1) * S.sizeAt v a), fun i => Fe i.1,
    fun i => hsLE ((p v).TP.E i.2), fun i => ?_, fun i => hFe i.1, fun P Q => ?_⟩
  · rw [hΓ, one_mul]
    exact div_nonneg (PBL.second_defect_nonneg S p v a i.1 i.2) (PBL.sizeAt_nonneg S v a)
  by_cases hloc : D.IsLocPt P (S.G.r + 1) ∧ D.IsLocPt Q (S.G.r + 1)
  · obtain ⟨hPl, hQl⟩ := hloc
    have hPs : D.IsLocPt (PBL.stdS S P) (S.G.r + 1) := (PBD.isLocPt_toStd_iff _ _ hgpos _ 1 _).2 hPl
    have hQs : D.IsLocPt (PBL.stdS S Q) (S.G.r + 1) := (PBD.isLocPt_toStd_iff _ _ hgpos _ 1 _).2 hQl
    rw [PBL.gN_setC hB, PBL.rr_top_eq Formalism.FourierDecayAlt.P.vector_valued_types (p v) (F v ε) a _ _ hPs hQs]
    unfold Top.topOf
    rw [Finset.mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    dsimp only
    have e1 := hVe e (PBL.stdS S P)
    have e2 := hVe e (PBL.stdS S Q)
    unfold KB.Pl.V at e1 e2
    rw [e1, e2, inner_smul_left, inner_smul_right, hsLE_apply, hsLE_apply]
    have hin : ⟪B.hsVec (((p v).TP.E ρ).comp ((p v).V (Fe e) (PBL.stdS S Q))),
        B.hsVec (((p v).TP.E ρ).comp ((p v).V (Fe e) (PBL.stdS S P)))⟫_ℂ =
        B.hsInner (((p v).TP.E ρ).comp (D.vecV (p v).T.base (p v).ν' (p v).m₀ (Fe e) (PBL.stdS S P)))
          (((p v).TP.E ρ).comp (D.vecV (p v).T.base (p v).ν' (p v).m₀ (Fe e) (PBL.stdS S Q))) := rfl
    rw [hin]
    set TT := Formalism.QuantumDeterminants.Tz S.G.k S.G.r (p v).T.base.z * Formalism.QuantumDeterminants.Tz S.G.k S.G.r (p v).T.base.z' with hTTdef
    by_cases h1 : 0 < D.ptG TT S.G.r (PBL.stdS S P)
    · by_cases h2 : 0 < D.ptG TT S.G.r (PBL.stdS S Q)
      · have hw1 : 0 ≤ Top.wPt TT S.G.r (PBL.stdS S P) ^ a.length :=
          pow_nonneg (div_nonneg (Complex.normSq_nonneg _) h1.le) _
        have hw2 : 0 ≤ Top.wPt TT S.G.r (PBL.stdS S Q) ^ a.length :=
          pow_nonneg (div_nonneg (Complex.normSq_nonneg _) h2.le) _
        have hd1 : Top.dH (D.parOf S v) (p v).l0 TT a (PBL.stdS S P) e ρ =
            √(Top.wPt TT S.G.r (PBL.stdS S P) ^ a.length) * √((Top.cW (D.parOf S v) (p v).l0 a e ρ).re) := by
          unfold Top.dH; exact Real.sqrt_mul hw1 _
        have hd2 : Top.dH (D.parOf S v) (p v).l0 TT a (PBL.stdS S Q) e ρ =
            √(Top.wPt TT S.G.r (PBL.stdS S Q) ^ a.length) * √((Top.cW (D.parOf S v) (p v).l0 a e ρ).re) := by
          unfold Top.dH; exact Real.sqrt_mul hw2 _
        rw [hd1, hd2]
        unfold omN PBL.del2
        rw [← hTT]
        simp only [Complex.conj_ofReal]
        push_cast
        ring
      · rw [PBL.vecV_of_G _ _ _ _ _ h2, ContinuousLinearMap.comp_zero, PBL.hsInner_zero_right']
        simp
    · rw [PBL.vecV_of_G _ _ _ _ _ h1, ContinuousLinearMap.comp_zero, PBD.hsInner_zero_left]
      simp
  · rw [PBL.gN_setC_zero hB F v ε (S.G.r + 1) a P Q hloc]
    symm
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hPl : D.IsLocPt P (S.G.r + 1)
    · have hQl : ¬ D.IsLocPt Q (S.G.r + 1) := fun h => hloc ⟨hPl, h⟩
      have hQs : ¬ D.IsLocPt (PBL.stdS S Q) (S.G.r + 1) := fun h =>
        hQl ((PBD.isLocPt_toStd_iff _ _ hgpos _ 1 _).1 h)
      unfold KB.Pl.V
      dsimp only
      rw [vecV_nonloc (p v).T.base (p v).ν' (p v).m₀ (Fe i.1) (PBL.stdS S Q) hQs, map_zero, smul_zero,
        inner_zero_left, mul_zero]
    · have hPs : ¬ D.IsLocPt (PBL.stdS S P) (S.G.r + 1) := fun h =>
        hPl ((PBD.isLocPt_toStd_iff _ _ hgpos _ 1 _).1 h)
      unfold KB.Pl.V
      dsimp only
      rw [vecV_nonloc (p v).T.base (p v).ν' (p v).m₀ (Fe i.1) (PBL.stdS S P) hPs, map_zero, smul_zero,
        inner_zero_right, mul_zero]

end

end Formalism.FourierDecayAlt.P.GermRateSplit
end
