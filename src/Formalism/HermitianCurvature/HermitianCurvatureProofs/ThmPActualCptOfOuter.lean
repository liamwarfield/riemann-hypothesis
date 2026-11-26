module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.StepFormCptAllOfStepFormAll

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.ThmPActualCptOfStepForm
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.OpLEqZeroOfEventually
open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerC

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Loc

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

def VanOut (Φ : RadSp k r z z' π π') (c : Fin r → ℂ) (K : Set (Mx k r)) : Prop :=
  ∀ g ∈ Glev k r (Fin.last r), g ∉ K → (Φ : Fn k r (Wq →L[ℂ] Wp)) c g = 0

def LCptAt (Φ : RadSp k r z z' π π') (c : Fin r → ℂ) : Prop :=
  ∃ U : Set (Fin r → ℂ), IsOpen U ∧ c ∈ U ∧ ∃ K : Set (Mx k r), IsCompact K ∧ K ⊆ {g | 0 < GGl k r z z' g} ∧
    ∀ c' ∈ U, VanOut Φ c' K


variable (k r z z' π π') in
def lcSub : Submodule ℂ (RadSp k r z z' π π') where
  carrier := {Φ | ∀ c ∈ OmX r, LCptAt Φ c}
  zero_mem' := fun c _ => ⟨Set.univ, isOpen_univ, trivial, ∅, isCompact_empty, Set.empty_subset _,
    fun _ _ _ _ _ => rfl⟩
  add_mem' := by
    intro Φ Ψ hΦ hΨ c hc
    obtain ⟨U1, hU1, hc1, K1, h1c, h1G, h10⟩ := hΦ c hc
    obtain ⟨U2, hU2, hc2, K2, h2c, h2G, h20⟩ := hΨ c hc
    refine ⟨U1 ∩ U2, hU1.inter hU2, ⟨hc1, hc2⟩, K1 ∪ K2, h1c.union h2c, Set.union_subset h1G h2G,
      fun c' hc' g hg hgK => ?_⟩
    show (Φ : Fn k r (Wq →L[ℂ] Wp)) c' g + (Ψ : Fn k r (Wq →L[ℂ] Wp)) c' g = 0
    rw [h10 c' hc'.1 g hg (fun h => hgK (Or.inl h)), h20 c' hc'.2 g hg (fun h => hgK (Or.inr h)), add_zero]
  smul_mem' := by
    intro a Φ hΦ c hc
    obtain ⟨U, hU, hcU, K, hKc, hKG, hK0⟩ := hΦ c hc
    refine ⟨U, hU, hcU, K, hKc, hKG, fun c' hc' g hg hgK => ?_⟩
    show a • (Φ : Fn k r (Wq →L[ℂ] Wp)) c' g = 0
    rw [hK0 c' hc' g hg hgK, smul_zero]

theorem lcSub_le_cptSub : lcSub k r z z' π π' ≤ cptSub k r z z' π π' := by
  intro Φ hΦ c hc
  obtain ⟨U, hU, hcU, K, hKc, hKG, hK0⟩ := hΦ c hc
  exact ⟨K, hKc, hKG, hK0 c hcU⟩

theorem mul_van {W : Module.End ℂ (RadSp k r z z' π π')} {m : (Fin r → ℂ) → Mx k r → ℂ} (hW : multiplicationOperator W m)
    (Φ : RadSp k r z z' π π') (c : Fin r → ℂ) (K : Set (Mx k r)) (h : VanOut Φ c K) : VanOut (W Φ) c K := by
  intro g hg hgK
  rw [hW Φ c g, h g hg hgK, smul_zero]

theorem t_van (X : ActualOps k r z z' π π') (Y : ℂ) (a b : Fin 2) (Φ : RadSp k r z z' π π') (c : Fin r → ℂ)
    (K : Set (Mx k r)) (hKc : IsCompact K) (h : VanOut Φ c K) : VanOut (X.t Y a b Φ) c K := by
  intro g hg hgK
  by_cases hd : (c, g) ∈ DomR k r z z'
  · have e := X.t_apply Y a b Φ (c, g) hd
    simp only at e
    rw [e]
    set D : Set (Mx k r) := {g | 0 < GGl k r z z' g} \ K with hDdef
    have hDo : IsOpen D := (isOpen_lt continuous_const (P.Qx5.GGl_continuous k r z z')).sdiff hKc.isClosed
    have hDG : D ⊆ {g | 0 < GGl k r z z' g} := Set.sdiff_subset
    have hgD : g ∈ Glev k r (Fin.last r) ∩ D := ⟨hg, hd.2.2, hgK⟩
    have hS1 := smoothLev_slice Φ c hd.1 D hDG
    have hS0 : SmoothLev k r (Fin.last r) D (fun _ : Mx k r => (0 : Wq →L[ℂ] Wp)) := by
      intro g₀ _
      exact ⟨Set.univ, fun _ => 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩
    have hL := Formalism.FourierDecayAlt.P.transfer_linear_local (Wq →L[ℂ] Wp) k r z z' (Fin.last r) D Y a b
      (fun g => (Φ : Fn k r (Wq →L[ℂ] Wp)) c g) (fun _ => 0) 1 hDo hS1 hS0 g hgD
    have hL0 := Formalism.FourierDecayAlt.P.transfer_linear_local (Wq →L[ℂ] Wp) k r z z' (Fin.last r) D Y a b
      (fun _ => (0 : Wq →L[ℂ] Wp)) (fun _ => 0) 1 hDo hS0 hS0 g hgD
    have h0 : tL k r z z' (Fin.last r) Y a b (fun _ : Mx k r => (0 : Wq →L[ℂ] Wp)) g = 0 := by
      have h := hL0.1
      simp only [smul_zero, add_zero, one_smul] at h
      have h2 : tL k r z z' (Fin.last r) Y a b (fun _ : Mx k r => (0 : Wq →L[ℂ] Wp)) g +
          tL k r z z' (Fin.last r) Y a b (fun _ : Mx k r => (0 : Wq →L[ℂ] Wp)) g =
          tL k r z z' (Fin.last r) Y a b (fun _ : Mx k r => (0 : Wq →L[ℂ] Wp)) g + 0 := by
        rw [add_zero]; exact h.symm
      exact add_left_cancel h2
    have hloc := hL.2 (fun x hx => h x hx.1 hx.2.2)
    rw [show (Φ : Fn k r (Wq →L[ℂ] Wp)) c = fun g => (Φ : Fn k r (Wq →L[ℂ] Wp)) c g from rfl, hloc, h0]
  · exact radSp_zero_off (X.t Y a b Φ) (x := (c, g)) hd

theorem opL_eq_zero_of_eventually {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (l : Fin r) (i : Fin 6)
    (f : (Fin r → ℂ) → E) (c : Fin r → ℂ) (hf : f =ᶠ[𝓝 c] fun _ => 0) : opL l i f c = 0 := by
  have h0 : f c = 0 := hf.self_of_nhds
  have hd : fderiv ℝ f c = 0 := by
    rw [hf.fderiv_eq]
    exact fderiv_const_apply 0
  fin_cases i <;> simp [opL, pOp, cOp, ciOp, pbOp, cbOp, cbiOp, wirt, wirtBar, h0, hd]

theorem op_van (X : ActualOps k r z z' π π') (l : Fin r) (i : Fin 6) (Φ : RadSp k r z z' π π')
    (U : Set (Fin r → ℂ)) (hU : IsOpen U) (K : Set (Mx k r)) (h : ∀ c' ∈ U, VanOut Φ c' K) :
    ∀ c ∈ U, VanOut (X.op l i Φ) c K := by
  intro c hc g hg hgK
  rw [X.op_apply l i Φ]
  show opL l i (fun c' => (Φ : Fn k r (Wq →L[ℂ] Wp)) c' g) c = 0
  apply opL_eq_zero_of_eventually
  filter_upwards [hU.mem_nhds hc] with c' hc'
  exact h c' hc' g hg hgK

theorem t_lc (X : ActualOps k r z z' π π') (Y : ℂ) (a b : Fin 2) :
    ∀ Φ ∈ lcSub k r z z' π π', X.t Y a b Φ ∈ lcSub k r z z' π π' := by
  intro Φ hΦ c hc
  obtain ⟨U, hU, hcU, K, hKc, hKG, hK0⟩ := hΦ c hc
  exact ⟨U, hU, hcU, K, hKc, hKG, fun c' hc' => t_van X Y a b Φ c' K hKc (hK0 c' hc')⟩

theorem mul_lc {W : Module.End ℂ (RadSp k r z z' π π')} {m : (Fin r → ℂ) → Mx k r → ℂ} (hW : multiplicationOperator W m) :
    ∀ Φ ∈ lcSub k r z z' π π', W Φ ∈ lcSub k r z z' π π' := by
  intro Φ hΦ c hc
  obtain ⟨U, hU, hcU, K, hKc, hKG, hK0⟩ := hΦ c hc
  exact ⟨U, hU, hcU, K, hKc, hKG, fun c' hc' => mul_van hW Φ c' K (hK0 c' hc')⟩

theorem op_lc (X : ActualOps k r z z' π π') (l : Fin r) (i : Fin 6) :
    ∀ Φ ∈ lcSub k r z z' π π', X.op l i Φ ∈ lcSub k r z z' π π' := by
  intro Φ hΦ c hc
  obtain ⟨U, hU, hcU, K, hKc, hKG, hK0⟩ := hΦ c hc
  exact ⟨U, hU, hcU, K, hKc, hKG, op_van X l i Φ U hU K hK0⟩

end Loc

section Alg

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem neg_lc {T : Module.End ℂ (RadSp k r z z' π π')} (hT : ∀ Φ ∈ lcSub k r z z' π π', T Φ ∈ lcSub k r z z' π π') :
    ∀ Φ ∈ lcSub k r z z' π π', (-T) Φ ∈ lcSub k r z z' π π' := fun Φ hΦ => by
  rw [LinearMap.neg_apply]
  exact (lcSub k r z z' π π').neg_mem (hT Φ hΦ)

theorem mkPair_mem_preservingAlgebra {T T' : Module.End ℂ (RadSp k r z z' π π')}
    (hT : ∀ Φ ∈ lcSub k r z z' π π', T Φ ∈ lcSub k r z z' π π')
    (hT' : ∀ Φ ∈ lcSub k r z z' π π', T' Φ ∈ lcSub k r z z' π π') :
    mkP T T' ∈ presAlg (lcSub k r z z' π π') := ⟨fun Φ hΦ => hT Φ hΦ, fun Φ hΦ => hT' Φ hΦ⟩

theorem UUiw_mem {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {𝒜 : StarSubalgebra ℂ A} (s : ℂ) :
    ∀ w : List (Letter ℂ S), (UUiw s w : SlopeTestRemainingChoices S A) ∈ entSub 𝒜 := by
  intro w
  induction w with
  | nil => exact (entSub 𝒜).one_mem
  | cons l w ih =>
    rw [UUiw]
    refine (entSub 𝒜).mul_mem (Formalism.FourierDecayAlt.P5.HerA.ins_mem _ fun i j => ?_) ih
    show io ((Formalism.YangianSpanCharacter.T.Uinv (if l.plus then s else star s) : M2 A) i j) ∈ entSub 𝒜
    apply Formalism.FourierDecayAlt.P5.HerA.io_mem
    fin_cases i <;> fin_cases j <;> simp [Formalism.YangianSpanCharacter.T.Uinv, 𝒜.one_mem, 𝒜.zero_mem, 𝒜.algebraMap_mem]

end Alg

section Classes

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]
variable {P : M.Par} {z z' : Fin (2 * P.r + P.k + 1) → ℂ} {π : Mx P.k P.r → (Wp →L[ℂ] Wp)}
  {π' : Mx P.k P.r → (Wq →L[ℂ] Wq)} {L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r}
  {st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))} {l0 : ℕ} {D : B.RealPlaceData P.k P.r Wp Wq}

theorem herGenC_lc (X : ActualOps P.k P.r z z' π π') (hAL : IsActualLevel X L)
    (hJ : ∀ (F : Mx P.k P.r → (Wq →L[ℂ] Wp)) (Φ : RadSp P.k P.r z z' π π'), JFOKCpt P z z' F →
      IsRadJF P z z' π π' D F Φ → Φ ∈ lcSub P.k P.r z z' π π')
    {i : Fin (P.r + 1)} {Φ : RadSp P.k P.r z z' π π'} (h : HerGenC S P z z' π π' L st l0 D i Φ) :
    Φ ∈ lcSub P.k P.r z z' π π' := by
  have hsite : ∀ l : Fin P.r, (site L l).p ∈ presAlg (lcSub P.k P.r z z' π π') ∧
      (site L l).c ∈ presAlg (lcSub P.k P.r z z' π π') ∧ (site L l).ci ∈ presAlg (lcSub P.k P.r z z' π π') := by
    intro l
    refine ⟨?_, ?_, ?_⟩
    · show L.p l ∈ _
      rw [hAL.1 l]; exact mkPair_mem_preservingAlgebra (op_lc X l 0) (neg_lc (op_lc X l 3))
    · show L.c l ∈ _
      rw [hAL.2.2.1 l]; exact mkPair_mem_preservingAlgebra (op_lc X l 1) (op_lc X l 4)
    · show L.ci l ∈ _
      rw [hAL.2.2.2.1 l]; exact mkPair_mem_preservingAlgebra (op_lc X l 2) (op_lc X l 5)
  induction h with
  | jf F Φ hF hΦ => exact hJ F Φ hF hΦ
  | slice l w a b Φ _ _ ih =>
    obtain ⟨hp, hc, hci⟩ := hsite l
    exact (Formalism.FourierDecayAlt.P5.HerA.bT_mem (site L l) hp hc hci w a b).1 Φ ih
  | waveC l w s Wv Wv' a b Φ _ h1 h2 _ ih =>
    have hm : (Vw (mkP Wv Wv') s w : SlopeTestRemainingChoices S (Pr (RadSp P.k P.r z z' π π'))) ∈
        entSub (presAlg (lcSub P.k P.r z z' π π')) :=
      (entSub _).mul_mem (Formalism.FourierDecayAlt.P5.HerA.io_mem (mkPair_mem_preservingAlgebra (mul_lc h1) (mul_lc h2))) (UUiw_mem s w)
    exact (hm a b).1 Φ ih
  | waveZ w s Wv Wv' a b Φ _ h1 h2 _ ih =>
    have hm : (Vw (mkP Wv Wv') s w : SlopeTestRemainingChoices S (Pr (RadSp P.k P.r z z' π π'))) ∈
        entSub (presAlg (lcSub P.k P.r z z' π π')) :=
      (entSub _).mul_mem (Formalism.FourierDecayAlt.P5.HerA.io_mem (mkPair_mem_preservingAlgebra (mul_lc h1) (mul_lc h2))) (UUiw_mem s w)
    exact (hm a b).1 Φ ih

theorem herKc_le_lc (X : ActualOps P.k P.r z z' π π') (hAL : IsActualLevel X L)
    (hJ : ∀ (F : Mx P.k P.r → (Wq →L[ℂ] Wp)) (Φ : RadSp P.k P.r z z' π π'), JFOKCpt P z z' F →
      IsRadJF P z z' π π' D F Φ → Φ ∈ lcSub P.k P.r z z' π π') (i : Fin (P.r + 1)) :
    herKc S P z z' π π' L st l0 D i ≤ lcSub P.k P.r z z' π π' := Submodule.span_le.2 fun Φ h => herGenC_lc X hAL hJ h

end Classes

def JFCptLocAll : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (D : B.RealPlaceData P.k P.r Wp Wq) (F : Mx P.k P.r → (Wq →L[ℂ] Wp))
    (Φ : RadSp P.k P.r z z' π π'),
    IsPlace P z z' π π' → D.z = z → D.z' = z' → D.π = π → D.π' = π' → JFOKCpt P z z' F →
    IsRadJF P z z' π π' D F Φ → Φ ∈ lcSub P.k P.r z z' π π'

theorem herCptTopAll_of_jf (hJ : JFCptLocAll) : HerCptTopAll := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ'
  refine (herKc_le_lc X hD.2.2.1
    (fun F Φ hF hR => hJ Wp Wq P z z' π π' D F Φ hD.1 hz hz' hπ hπ' hF hR) (Fin.last P.r)).trans ?_
  exact lcSub_le_cptSub

theorem thmPActualCpt_of_jf (hJ : JFCptLocAll) (hSF : StepFormCptAll) : ThmPActualCpt := thmPActualCpt_of_parts (herCptTopAll_of_jf hJ) hSF

end Formalism.FourierDecayAlt.P5.HerC
end
end

open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerC

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Minors

variable {k r : ℕ}

def pc (c : Fin r → ℂ) : ℂ := ∏ a : Fin r with a.val < (Fin.last r).val, c a

theorem pc_continuous : Continuous (pc (r := r)) := by
  unfold pc
  exact continuous_finsetProd _ fun a _ => continuous_apply a

theorem pc_ne_zero {c : Fin r → ℂ} (hc : c ∈ OmX r) : pc c ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => hc a

theorem dmin_wCell {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') {c : Fin r → ℂ}
    (hc : c ∈ OmX r) {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r)) :
    Dmin k r z z' (wCell k r (Fin.last r) c * g) ⟨r, by omega⟩ = pc c ∧
      Dmin k r z z' (wCell k r (Fin.last r) c * g) (Fin.last (r + 1)) = zetaL k r z z' (Fin.last r) g * pc c := by
  obtain ⟨μ, _, rfl⟩ := (Formalism.FourierDecayAlt.P.TwoByOneBlock.UWb_iff g).1 (Formalism.FourierDecayAlt.P5.Rad.glev_last_uwb hg)
  have e : wCell k r (Fin.last r) c * Formalism.FourierDecayAlt.B2.embWb k r μ = bigCell k r c μ := by
    rw [Formalism.FourierDecayAlt.P5.Rad.wCell_last_eq, ← (Formalism.FourierDecayAlt.P.bruhat_big_cell_factorization k r c μ).1]
  rw [e]
  have hmin := big_cell_minors_holds k r z z' c μ hz hz'
  have hζ : herm (Hpk k r) (bigCell k r c μ *ᵥ z') z = zetaL k r z z' (Fin.last r) (Formalism.FourierDecayAlt.B2.embWb k r μ) := by
    rw [Formalism.FourierDecayAlt.P5.Rad.zetaL_last, ← Formalism.FourierDecayAlt.P.TwoByOneBlock.jV_wbPart hz', Formalism.FourierDecayAlt.P.BigCellHermitian.bigCell_mulVec_jV,
      Formalism.FourierDecayAlt.P.TwoByOneBlock.emb_mulVec_jV]
  have hr : Dmin k r z z' (bigCell k r c μ) ⟨r, by omega⟩ = pc c := hmin.1 (Fin.last r)
  refine ⟨hr, ?_⟩
  have hzeta := hmin.2.2 hc
  rw [hζ] at hzeta
  unfold Formalism.QuantumDeterminants.zeta at hzeta
  rw [hr] at hzeta
  have h2 := div_mul_cancel₀ (Dmin k r z z' (bigCell k r c μ) (Fin.last (r + 1))) (pc_ne_zero hc)
  rw [hzeta] at h2
  exact h2.symm

end Minors

theorem jfCptLocAll : JFCptLocAll := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' D F Φ _hP hz hz' hπ hπ' hF hΦ
  subst hz hz' hπ hπ'
  obtain ⟨⟨_, ε, hε, hG⟩, hC⟩ := hF
  have hW := Formalism.FourierDecayAlt.P.weyl_subgroup_closed P.k P.r
  have hN := Formalism.FourierDecayAlt.P.unipotent_radical_closed P.k P.r
  have hGV := Formalism.FourierDecayAlt.P.unitary_group_closed P.k P.r
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarN
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW'

  have hcont : Continuous (fun h : Mx P.k P.r => Dmin P.k P.r D.z D.z' h (Fin.last (P.r + 1))) :=
    (Formalism.FourierDecayAlt.P.JCx1.contDiff_Dmin D.z D.z' (Fin.last (P.r + 1))).continuous
  obtain ⟨R0, hR0⟩ := hC.isCompact.exists_bound_of_continuousOn hcont.continuousOn

  have hae : ∀ᵐ (p : (Mt P.k P.r × Mt P.k P.r) × (Mt P.k P.r × Mt P.k P.r)) ∂((D.μW.prod D.μN).prod (D.μW'.prod D.μN)),
      (Matrix.of p.1.1 ∈ UWset P.k P.r D.z ∧ Matrix.of p.1.2 ∈ Formalism.QuantumDeterminants.Nset P.k P.r) ∧
        (Matrix.of p.2.1 ∈ UWset P.k P.r D.z' ∧ Matrix.of p.2.2 ∈ Formalism.QuantumDeterminants.Nset P.k P.r) := by
    have hw : ∀ᵐ (a : Mt P.k P.r) ∂D.μW, Matrix.of a ∈ UWset P.k P.r D.z :=
      (measure_eq_zero_iff_ae_notMem.1 D.haarW.conc).mono fun a ha => not_not.1 ha
    have hn : ∀ᵐ (a : Mt P.k P.r) ∂D.μN, Matrix.of a ∈ Formalism.QuantumDeterminants.Nset P.k P.r :=
      (measure_eq_zero_iff_ae_notMem.1 D.haarN.conc).mono fun a ha => not_not.1 ha
    have hw' : ∀ᵐ (a : Mt P.k P.r) ∂D.μW', Matrix.of a ∈ UWset P.k P.r D.z' :=
      (measure_eq_zero_iff_ae_notMem.1 D.haarW'.conc).mono fun a ha => not_not.1 ha
    have h1 : ∀ᵐ (q : Mt P.k P.r × Mt P.k P.r) ∂(D.μW.prod D.μN), Matrix.of q.1 ∈ UWset P.k P.r D.z ∧ Matrix.of q.2 ∈ Formalism.QuantumDeterminants.Nset P.k P.r :=
      (Measure.quasiMeasurePreserving_fst.ae hw).and (Measure.quasiMeasurePreserving_snd.ae hn)
    have h2 : ∀ᵐ (q : Mt P.k P.r × Mt P.k P.r) ∂(D.μW'.prod D.μN), Matrix.of q.1 ∈ UWset P.k P.r D.z' ∧ Matrix.of q.2 ∈ Formalism.QuantumDeterminants.Nset P.k P.r :=
      (Measure.quasiMeasurePreserving_fst.ae hw').and (Measure.quasiMeasurePreserving_snd.ae hn)
    exact (Measure.quasiMeasurePreserving_fst.ae h1).and (Measure.quasiMeasurePreserving_snd.ae h2)
  intro c hc
  set p0 : ℝ := ‖pc c‖ with hp0
  have hp0pos : 0 < p0 := norm_pos_iff.2 (pc_ne_zero hc)
  set U : Set (Fin P.r → ℂ) := {c' | p0 / 2 < ‖pc c'‖ ∧ ‖pc c'‖ < 2 * p0} with hU
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const (continuous_norm.comp pc_continuous)).inter
      (isOpen_lt (continuous_norm.comp pc_continuous) continuous_const)
  have hcU : c ∈ U := ⟨by linarith, by linarith⟩
  set e' : ℝ := ε / (2 * p0) ^ 2 with he'
  set R' : ℝ := R0 / (p0 / 2) with hR'
  have he'pos : 0 < e' := div_pos hε (by positivity)
  refine ⟨U, hUo, hcU, {g | g ∈ Glev P.k P.r (Fin.last P.r) ∧ e' ≤ GGl P.k P.r D.z D.z' g ∧
      ‖zetaL P.k P.r D.z D.z' (Fin.last P.r) g‖ ≤ R'},
    isCompact_zeta_le D.z D.z' D.z_mem D.z'_mem D.T_pos D.T'_pos e' R', fun g hg => lt_of_lt_of_le he'pos hg.2.1, ?_⟩
  intro c' hc' g hg hgK
  by_cases hd : (c', g) ∈ DomR P.k P.r D.z D.z'
  swap
  · exact radSp_zero_off Φ (x := (c', g)) hd
  rw [hΦ (c', g) hd]
  unfold resG
  have hc'O : c' ∈ OmX P.r := hd.1
  set x : Mx P.k P.r := wCell P.k P.r (Fin.last P.r) c' * g with hx
  obtain ⟨hDr, hDl⟩ := dmin_wCell D.z_mem D.z'_mem hc'O hg
  rw [← hx] at hDr hDl
  have hxG : x ∈ B.GV P.k P.r := hGV.mul_mem _ (Formalism.FourierDecayAlt.P.Qx3.wlist_glev hc'O _).1 _ hg.1

  have hF0 : ∀ y ∈ B.GV P.k P.r, Dmin P.k P.r D.z D.z' y ⟨P.r, by omega⟩ = pc c' →
      Dmin P.k P.r D.z D.z' y (Fin.last (P.r + 1)) = zetaL P.k P.r D.z D.z' (Fin.last P.r) g * pc c' → F y = 0 := by
    intro y hy hyr hyl
    by_contra hFy
    apply hgK
    have hsupp : y ∈ tsupport F := subset_tsupport F hFy
    have hb := hR0 y hsupp
    have hGy := hG y hy hFy
    rw [hyl] at hb
    have hGy' : Gf P.k P.r D.z D.z' y = Complex.normSq (pc c') * GGl P.k P.r D.z D.z' g := by
      unfold Formalism.QuantumDeterminants.Gf GGl
      rw [hyr, hyl, Complex.normSq_mul]
      ring
    have hpc1 : p0 / 2 < ‖pc c'‖ := hc'.1
    have hpc2 : ‖pc c'‖ < 2 * p0 := hc'.2
    have hpcpos : 0 < ‖pc c'‖ := by linarith
    have hns : Complex.normSq (pc c') = ‖pc c'‖ ^ 2 := by rw [Complex.sq_norm]
    refine ⟨hg, ?_, ?_⟩
    ·
      have hGG : ε ≤ ‖pc c'‖ ^ 2 * GGl P.k P.r D.z D.z' g := by rw [← hns, ← hGy']; exact hGy
      have hGGpos : 0 < GGl P.k P.r D.z D.z' g := hd.2.2
      have hsq : ‖pc c'‖ ^ 2 ≤ (2 * p0) ^ 2 := by nlinarith
      rw [he', div_le_iff₀ (by positivity)]
      nlinarith
    ·
      rw [norm_mul] at hb
      have hz0 : 0 ≤ ‖zetaL P.k P.r D.z D.z' (Fin.last P.r) g‖ := norm_nonneg _
      have hR0nn : 0 ≤ R0 := le_trans (by positivity) hb
      rw [hR', le_div_iff₀ (by positivity)]
      nlinarith
  have hJ0 : B.JF D F x = 0 := by
    unfold B.JF besselJ
    refine integral_eq_zero_of_ae (hae.mono fun p hp => ?_)
    obtain ⟨⟨ha, hn⟩, ⟨ha', hn'⟩⟩ := hp
    set a := Matrix.of p.1.1
    set n := Matrix.of p.1.2
    set a' := Matrix.of p.2.1
    set n' := Matrix.of p.2.2
    have hainv : a⁻¹ ∈ UWset P.k P.r D.z := (hW D.z).inv_mem _ ha
    have hninv : n⁻¹ ∈ Formalism.QuantumDeterminants.Nset P.k P.r := hN.inv_mem _ hn
    have hs1 : a⁻¹ * n⁻¹ ∈ Formalism.QuantumDeterminants.Sset P.k P.r D.z := ⟨a⁻¹, hainv, n⁻¹, hninv, rfl⟩
    have hs2 : n' ∈ Formalism.QuantumDeterminants.Sset P.k P.r D.z' := ⟨1, (hW D.z').one_mem, n', hn', (one_mul _).symm⟩
    have hs3 : (1 : Mx P.k P.r) ∈ Formalism.QuantumDeterminants.Sset P.k P.r D.z := ⟨1, (hW D.z).one_mem, 1, hN.one_mem, (mul_one _).symm⟩
    have hs4 : a' ∈ Formalism.QuantumDeterminants.Sset P.k P.r D.z' := ⟨a', ha', 1, hN.one_mem, (mul_one _).symm⟩
    have hinvD : ∀ l, Dmin P.k P.r D.z D.z' (a⁻¹ * n⁻¹ * x * n' * a') l = Dmin P.k P.r D.z D.z' x l := by
      intro l
      have e1 := diagonal_inverse_holds P.k P.r D.z D.z' D.z_mem D.z'_mem 1 hs3 a' hs4 (a⁻¹ * n⁻¹ * x * n') l
      rw [one_mul] at e1
      rw [e1]
      exact diagonal_inverse_holds P.k P.r D.z D.z' D.z_mem D.z'_mem _ hs1 n' hs2 x l
    have hyG : a⁻¹ * n⁻¹ * x * n' * a' ∈ B.GV P.k P.r :=
      hGV.mul_mem _ (hGV.mul_mem _ (hGV.mul_mem _ (hGV.mul_mem _ hainv.1 _ hninv.1) _ hxG) _ hn'.1) _ ha'.1
    have hFy : F (a⁻¹ * n⁻¹ * x * n' * a') = 0 :=
      hF0 _ hyG (by rw [hinvD]; exact hDr) (by rw [hinvD]; exact hDl)
    have hxy : (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * x * Matrix.of p.2.2 * Matrix.of p.2.1 =
        a⁻¹ * n⁻¹ * x * n' * a' := rfl
    simp only [hxy, hFy, ContinuousLinearMap.comp_zero, ContinuousLinearMap.zero_comp, smul_zero, Pi.zero_apply]
  rw [hJ0, smul_zero]

theorem thmPActualCpt_of_stepForm (hSF : StepFormCptAll) : ThmPActualCpt := thmPActualCpt_of_jf jfCptLocAll hSF

end Formalism.FourierDecayAlt.P5.HerC
end
end

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerC

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB

section Ent

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]
variable {P : M.Par} {z z' : Fin (2 * P.r + P.k + 1) → ℂ} {π : Mx P.k P.r → (Wp →L[ℂ] Wp)}
  {π' : Mx P.k P.r → (Wq →L[ℂ] Wq)}

theorem site_lc (X : ActualOps P.k P.r z z' π π') {L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r}
    (hAL : IsActualLevel X L) (l : Fin P.r) :
    L.p l ∈ presAlg (lcSub P.k P.r z z' π π') ∧ L.c l ∈ presAlg (lcSub P.k P.r z z' π π') ∧
      L.ci l ∈ presAlg (lcSub P.k P.r z z' π π') := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hAL.1 l]; exact mkPair_mem_preservingAlgebra (op_lc X l 0) (neg_lc (op_lc X l 3))
  · rw [hAL.2.2.1 l]; exact mkPair_mem_preservingAlgebra (op_lc X l 1) (op_lc X l 4)
  · rw [hAL.2.2.2.1 l]; exact mkPair_mem_preservingAlgebra (op_lc X l 2) (op_lc X l 5)

theorem QQ_lc (X : ActualOps P.k P.r z z' π π') (Y : ℂ) (a b : Fin 2) :
    X.QQ Y a b ∈ presAlg (lcSub P.k P.r z z' π π') :=
  mkPair_mem_preservingAlgebra (t_lc X Y a b) (t_lc X (star Y) b a)

theorem RRi_lc (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (hD : IsData P z z' π π' X μ L st l0) (i : Fin (P.r + 1)) (w : List (Letter ℂ S))
    (hw : ∀ l ∈ w, star l.pt = l.pt) : RRi L st i w ∈ entSub (presAlg (lcSub P.k P.r z z' π π')) := by
  obtain ⟨-, -, hAL, hQQ, -⟩ := hD
  refine rrw_mem (QQi L st i) (QQi_mem L st _ i (fun Y _ a b => ?_) (fun l _ => site_lc X hAL l)) w hw
  rw [hQQ Y, Matrix.smul_apply]
  exact (presAlg (lcSub P.k P.r z z' π π')).smul_mem (QQ_lc X Y a b) _

end Ent

section G

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem int_lc (μ : Measure (Mt k r)) (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) {Φ Ψ : RadSp k r z z' π π'}
    (hΦ : Φ ∈ lcSub k r z z' π π') (hΨ : Ψ ∈ lcSub k r z z' π π') (c : Fin r → ℂ) :
    Integrable (fun g : Mt k r => B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))
      ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))) μ := by
  by_cases hc : c ∈ OmX r
  · exact intOn_cpt μ hμ c hc Φ (lcSub_le_cptSub hΦ) Ψ (lcSub_le_cptSub hΨ)
  · have e : (fun g : Mt k r => B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))
        ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))) = fun _ => 0 := by
      funext g
      rw [radSp_zero_off Φ (x := (c, Matrix.of g)) (fun h => hc h.1)]
      exact hsInner_zero_left _
    rw [e]; exact integrable_zero _ _ _

end G

section Form

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

theorem formIntG_herKc (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq) (hD : IsData P z z' π π' X μ L st l0) (hz : D.z = z) (hz' : D.z' = z')
    (hπ : D.π = π) (hπ' : D.π' = π') (w : List (Letter ℂ S)) (hw : WordOK P z z' π π' st l0 w)
    (i : Fin (P.r + 1)) (c : Fin P.r → ℂ) (x y : Ix S → RadSp P.k P.r z z' π π')
    (hx : InK (herKc S P z z' π π' L st l0 D i) x) (hy : InK (herKc S P z z' π π' L st l0 D i) y)
    (c' : Cf P.r i) (a : Ix S) :
    Integrable (fun g : Mt P.k P.r =>
      B.hsInner ((act (RRi L st i w) x a : Fn P.k P.r (Wq →L[ℂ] Wp)) (glue i c c') (Matrix.of g))
        ((y a : Fn P.k P.r (Wq →L[ℂ] Wp)) (glue i c c') (Matrix.of g))) μ := by
  have hle := herKc_le_lc (S := S) (st := st) (l0 := l0) X hD.2.2.1
    (fun F Φ hF hΦ => jfCptLocAll Wp Wq P z z' π π' D F Φ hD.1 hz hz' hπ hπ' hF hΦ) i
  have hRR := RRi_lc X μ L st l0 hD i w hw.1.2.1
  have hu : act (RRi L st i w) x a ∈ lcSub P.k P.r z z' π π' :=
    (lcSub P.k P.r z z' π π').sum_mem fun b _ => (hRR a b).1 _ (hle (hx b))
  exact int_lc μ hD.2.1 hu (hle (hy a)) _

def FormIntOuterCpt : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    ∀ w : List (Letter ℂ S), WordOK P z z' π π' st l0 w → ∀ (i : Fin (P.r + 1)) (c : Fin P.r → ℂ), c ∈ OmX P.r →
    ∀ x y : Ix S → RadSp P.k P.r z z' π π', InK (herKc S P z z' π π' L st l0 D i) x →
      InK (herKc S P z z' π π' L st l0 D i) y →
      Integrable (fun c' : Cf P.r i => ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
        ∑ a, pairAt μ (act (RRi L st i w) x a) (y a) (glue i c c'))

def StepDensCptAll : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    StepDens (S := S) P z z' π π' μ L st (herKc S P z z' π π' L st l0 D) l0

theorem stepFormCptAll_of (hSD : StepDensCptAll) (hFO : FormIntOuterCpt) : StepFormCptAll := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ'
  refine ⟨hSD Wp Wq S P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ', fun w hw i c hc x y hx hy => ⟨?_, ?_⟩⟩
  · exact fun c' a => formIntG_herKc P z z' π π' X μ L st l0 D hD hz hz' hπ hπ' w hw i c x y hx hy c' a
  · exact hFO Wp Wq S P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' w hw i c hc x y hx hy

theorem thmPActualCpt_of_outer (hSD : StepDensCptAll) (hFO : FormIntOuterCpt) : ThmPActualCpt :=
  thmPActualCpt_of_stepForm (stepFormCptAll_of hSD hFO)

end Form

end Formalism.FourierDecayAlt.P5.HerC
