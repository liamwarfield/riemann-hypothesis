module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.InsertUnitMatrixZeroApply
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PictureMemLevelZeroClass
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PositiveDensityModerateGrowth
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStableLoc
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAlgebraFacts

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyZeroNear
open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBE

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section gen

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem ckOn_top_of_nat {f : B.Mat k r → E} (hf : ∀ m : ℕ, B.CkOn (m : ℕ∞) (B.GV k r) f) :
    B.CkOn ⊤ (B.GV k r) f := by
  intro g₀ hG
  refine ⟨P5.Rad.retDom g₀, fun Y => f (P5.Rad.ret g₀ Y), P5.Rad.isOpen_retDom g₀, P5.Rad.self_mem_retDom hG,
    ?_, ?_⟩
  · intro Y hY
    apply ContDiffAt.contDiffWithinAt
    rw [show (((⊤ : ℕ∞) : WithTop ℕ∞)) = ∞ from rfl, contDiffAt_infty]
    intro n
    obtain ⟨U, F, hU, hYU, hF, hfF⟩ := hf n (P5.Rad.ret g₀ Y) (P5.Rad.ret_mem hG hY)
    have hr : ContDiffAt ℝ ∞ (P5.Rad.ret g₀) Y :=
      (P5.Rad.cd_ret g₀).contDiffAt ((P5.Rad.isOpen_retDom g₀).mem_nhds hY)
    have hFa : ContDiffAt ℝ n F (P5.Rad.ret g₀ Y) := by
      have := hF.contDiffAt (hU.mem_nhds hYU)
      exact_mod_cast this
    have hcomp : ContDiffAt ℝ n (fun Y' => F (P5.Rad.ret g₀ Y')) Y := hFa.comp Y (hr.of_le (mod_cast le_top))
    refine hcomp.congr_of_eventuallyEq ?_
    filter_upwards [(P5.Rad.isOpen_retDom g₀).mem_nhds hY, hr.continuousAt.preimage_mem_nhds (hU.mem_nhds hYU)]
      with Y' h1 h2
    exact hfF _ h2 (P5.Rad.ret_mem hG h1)
  · intro Y hY hYG
    show f Y = f (P5.Rad.ret g₀ Y)
    rw [P5.Rad.ret_self hG hYG hY.1]

theorem rdV_congrGV {X : B.Mat k r} (hX : B.inLie k r X) {h₁ h₂ : B.Mat k r → E}
    (hh : ∀ g ∈ B.GV k r, h₁ g = h₂ g) : ∀ g ∈ B.GV k r, RdV X h₁ g = RdV X h₂ g := by
  intro g hg
  unfold RdV
  congr 1
  funext t
  exact hh _ (B5.curve_mem hg hX t)

theorem rw_congrGV : ∀ (v : List (B.Mat k r)), (∀ X ∈ v, B.inLie k r X) → ∀ {h₁ h₂ : B.Mat k r → E},
    (∀ g ∈ B.GV k r, h₁ g = h₂ g) → ∀ g ∈ B.GV k r, B.Rw v h₁ g = B.Rw v h₂ g
  | [], _, _, _, hh => hh
  | X :: v, hv, _, _, hh => by
    show ∀ g ∈ B.GV k r, RdV X (B.Rw v _) g = RdV X (B.Rw v _) g
    exact rdV_congrGV (hv X (by simp)) (rw_congrGV v (fun Y hY => hv Y (by simp [hY])) hh)

theorem rdV_zero_near {X : B.Mat k r} (hX : B.inLie k r X) {h : B.Mat k r → E} {U : Set (B.Mat k r)}
    (hU : IsOpen U) (hh : ∀ g ∈ B.GV k r, g ∈ U → h g = 0) : ∀ g ∈ B.GV k r, g ∈ U → RdV X h g = 0 := by
  intro g hg hgU
  unfold RdV
  have hc : Continuous (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) := (B5.curve_contDiff g X).continuous
  have hU0 : U ∈ 𝓝 (g * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) := by
    rw [B5.curve_zero]; exact hU.mem_nhds hgU
  have hev : (fun t : ℝ => h (g * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[𝓝 0] fun _ => 0 := by
    filter_upwards [hc.continuousAt.preimage_mem_nhds hU0] with t ht
    exact hh _ (B5.curve_mem hg hX t) ht
  rw [hev.deriv_eq]
  simp

theorem rw_zero_near : ∀ (v : List (B.Mat k r)), (∀ X ∈ v, B.inLie k r X) → ∀ {h : B.Mat k r → E}
    {U : Set (B.Mat k r)}, IsOpen U → (∀ g ∈ B.GV k r, g ∈ U → h g = 0) →
    ∀ g ∈ B.GV k r, g ∈ U → B.Rw v h g = 0
  | [], _, _, _, _, hh => hh
  | X :: v, hv, _, _, hU, hh => by
    show ∀ g ∈ B.GV k r, g ∈ _ → RdV X (B.Rw v _) g = 0
    exact rdV_zero_near (hv X (by simp)) hU (rw_zero_near v (fun Y hY => hv Y (by simp [hY])) hU hh)

end gen

section ops

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem opApply_congrGV (Θ : B.DiffOp k r Wp Wq) {F₁ F₂ : B.Mat k r → (Wq →L[ℂ] Wp)}
    (hh : ∀ g ∈ B.GV k r, F₁ g = F₂ g) : ∀ g ∈ B.GV k r, B.opApply Θ F₁ g = B.opApply Θ F₂ g := by
  intro g hg
  unfold B.opApply
  congr 1
  apply List.map_congr_left
  intro T _
  rw [rw_congrGV T.word T.word_lie hh g hg]

theorem opApply_zero_near (Θ : B.DiffOp k r Wp Wq) {F : B.Mat k r → (Wq →L[ℂ] Wp)} {U : Set (B.Mat k r)}
    (hU : IsOpen U) (hh : ∀ g ∈ B.GV k r, g ∈ U → F g = 0) : ∀ g ∈ B.GV k r, g ∈ U → B.opApply Θ F g = 0 := by
  intro g hg hgU
  unfold B.opApply
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨T, _, rfl⟩ := List.mem_map.1 hx
  rw [rw_zero_near T.word T.word_lie hU hh g hg hgU, map_zero]

end ops

section casts

variable {k : ℕ}

theorem castM_GV {a b : ℕ} (e : a = b) {x : B.Mat k a} (hx : x ∈ B.GV k a) : D.castM e x ∈ B.GV k b := by
  subst e; rwa [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]

theorem gN_castM {a b : ℕ} (e : a = b) (x : B.Mat k a) : B.gN (D.castM e x) = B.gN x := by
  subst e; rw [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]

theorem Gf_castM {a b : ℕ} (e : a = b) (z z' : Fin (2 * b + k + 1) → ℂ) (x : B.Mat k a) :
    Gf k a (D.castV e.symm z) (D.castV e.symm z') x = Gf k b z z' (D.castM e x) := by
  subst e; rw [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl, Formalism.FourierDecayAlt.P.JCTx6.Link2.castV_self,
    Formalism.FourierDecayAlt.P.JCTx6.Link2.castV_self]

end casts

theorem isCompact_gN_le (k r : ℕ) (R : ℝ) : IsCompact {g : B.Mat k r | B.gN g ≤ R} := by
  have hcl : IsClosed {g : B.Mat k r | B.gN g ≤ R} := isClosed_le Formalism.FourierDecayAlt.P.B6.gN_continuous continuous_const
  refine (isCompact_closedBall (0 : B.Mat k r) R).of_isClosed_subset hcl ?_
  intro g hg
  rw [Metric.mem_closedBall, dist_zero_right]
  refine (Matrix.norm_le_iff ((norm_nonneg _).trans ((Formalism.FourierDecayAlt.P.Dx3.entry_le_gN g 0 0).trans hg))).2 ?_
  intro i j
  exact (Formalism.FourierDecayAlt.P.Dx3.entry_le_gN g i j).trans hg

end Formalism.FourierDecayAlt.P.PBE
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.FormZeroEqSlotPairingOfLe
namespace Formalism.FourierDecayAlt.P.PBF

open Finset Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.Q Formalism.QuantumDeterminants
open scoped ComplexConjugate ComplexOrder

noncomputable section

theorem pairJ_rel {X Y : Type} {w : List C.Letter} (R : X → Y → Prop) (c : ℂ)
    (Ξ1 : (Ix (Fin w.length) → X) → (Ix (Fin w.length) → X) → ℂ)
    (Ξ2 : (Ix (Fin w.length) → Y) → (Ix (Fin w.length) → Y) → ℂ)
    (h : ∀ x x' y y', (∀ e, R (x e) (y e)) → (∀ e, R (x' e) (y' e)) → Ξ1 x x' = c * Ξ2 y y') :
    ∀ (ys : List ℝ) (x : Ix (Fin (KB.plusW ys w).length) → X) (x' : Ix (Fin (KB.minusW ys w).length) → X)
      (y : Ix (Fin (KB.plusW ys w).length) → Y) (y' : Ix (Fin (KB.minusW ys w).length) → Y),
      (∀ e, R (x e) (y e)) → (∀ e, R (x' e) (y' e)) → KB.pairJ Ξ1 ys x x' = c * KB.pairJ Ξ2 ys y y'
  | [], x, x', y, y', hx, hx' => h x x' y y' hx hx'
  | _ :: ys, x, x', y, y', hx, hx' => by
    show KB.pairJ Ξ1 ys _ _ - KB.pairJ Ξ1 ys _ _ = c * (KB.pairJ Ξ2 ys _ _ - KB.pairJ Ξ2 ys _ _)
    have a1 := pairJ_rel R c Ξ1 Ξ2 h ys (fun e => x (Fin.cons 1 e)) (fun e => x' (Fin.cons 0 e))
      (fun e => y (Fin.cons 1 e)) (fun e => y' (Fin.cons 0 e)) (fun e => hx _) (fun e => hx' _)
    have a2 := pairJ_rel R c Ξ1 Ξ2 h ys (fun e => x (Fin.cons 0 e)) (fun e => x' (Fin.cons 1 e))
      (fun e => y (Fin.cons 0 e)) (fun e => y' (Fin.cons 1 e)) (fun e => hx _) (fun e => hx' _)
    exact (congrArg₂ (· - ·) a1 a2).trans (mul_sub _ _ _).symm

theorem prod_real (zs : List ℂ) (h : ∀ z ∈ zs, z.im = 0) : zs.prod.im = 0 ∧ zs.prod.re = (zs.map Complex.re).prod := by
  induction zs with
  | nil => simp
  | cons z zs ih =>
    have hz := h z (by simp)
    obtain ⟨h1, h2⟩ := ih fun z' hz' => h z' (by simp [hz'])
    simp only [List.prod_cons, List.map_cons, Complex.mul_im, Complex.mul_re, hz, h1, mul_zero, zero_mul,
      add_zero, sub_zero, h2]
    exact ⟨trivial, trivial⟩

theorem form_castIx {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} (μ : MeasureTheory.Measure (Mt k r))
    {n m : ℕ} (h : n = m) (U V : Ix (Fin n) → RadSp k r z z' π π') (c : Fin r → ℂ) :
    form μ 0 (fun z => U (z ∘ Fin.cast h)) (fun z => V (z ∘ Fin.cast h)) c = form μ 0 U V c := by
  subst h
  rfl

theorem form_embed {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} (μ : MeasureTheory.Measure (Mt k r))
    {S S' : Type} [Fintype S] [DecidableEq S] [Fintype S'] [DecidableEq S'] (ι : Ix S' → Ix S)
    (hι : Function.Injective ι) (x y : Ix S' → RadSp k r z z' π π') (c : Fin r → ℂ) :
    form μ 0 (Function.extend ι x 0) (Function.extend ι y 0) c = form μ 0 x y c := by
  unfold form
  congr 1
  funext c'
  congr 1
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image ι)), Finset.sum_image (fun a _ b _ h => hι h)]
  · simp only [hι.extend_apply]
  · intro z _ hz
    have : ¬ ∃ a, ι a = z := fun ⟨a, ha⟩ => hz (Finset.mem_image.2 ⟨a, Finset.mem_univ a, ha⟩)
    rw [Function.extend_apply' _ _ _ this, Pi.zero_apply, pairAt_zero_left]

theorem pairS_embed {V : Type} [AddCommGroup V] [Module ℂ V] {S S' : Type} [Fintype S] [DecidableEq S] [Fintype S']
    [DecidableEq S'] (β : V → V → ℂ) (hβ : ∀ v, β 0 v = 0) (ι : Ix S' → Ix S) (hι : Function.Injective ι)
    (x y : Ix S' → V) : pairS β (Function.extend ι x 0) (Function.extend ι y 0) = pairS β x y := by
  unfold pairS
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image ι)), Finset.sum_image (fun a _ b _ h => hι h)]
  · simp only [hι.extend_apply]
  · intro z _ hz
    have : ¬ ∃ a, ι a = z := fun ⟨a, ha⟩ => hz (Finset.mem_image.2 ⟨a, Finset.mem_univ a, ha⟩)
    rw [Function.extend_apply' _ _ _ this, Pi.zero_apply, hβ]

def ixEmb {m n : ℕ} (h : m ≤ n) (e : Ix (Fin m)) : Ix (Fin n) := fun t => if ht : t.val < m then e ⟨t, ht⟩ else 0

theorem ixEmb_inj {m n : ℕ} (h : m ≤ n) : Function.Injective (ixEmb h) := by
  intro e e' he
  funext t
  have := congrFun he ⟨t.val, by omega⟩
  simpa [ixEmb, t.isLt] using this

theorem bet_neg {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} (μ : MeasureTheory.Measure (Mt k r))
    (v v' : RadSp k r z z' π π') : bet μ (-v) v' = -bet μ v v' := by
  unfold bet
  have := pairLev_smul_left (μ := μ) (i := 0) v v' (fun _ => 1) (-1)
  have e : ((-1 : ℂ) • v) = -v := neg_one_smul ℂ v
  rw [e, neg_one_mul] at this
  exact this

theorem bet_zero {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} (μ : MeasureTheory.Measure (Mt k r))
    (v : RadSp k r z z' π π') : bet μ 0 v = 0 := by
  unfold bet; exact pairLev_zero_left v _

section EmbData

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {n : ℕ}
  {P : M.Par} {z z' : Fin (2 * P.r + P.k + 1) → ℂ} {π : Mx P.k P.r → (Wp →L[ℂ] Wp)}
  {π' : Mx P.k P.r → (Wq →L[ℂ] Wq)} {μ : MeasureTheory.Measure (Mt P.k P.r)}
  {L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r} {st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))} {l0 : ℕ}
  {K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')}

theorem form_zero_eq_position_pairing_of_le (hThm : ThmPOn (S := Fin n) P z z' π π' μ L st K l0) {m : ℕ} (hmn : m ≤ n)
    (Y₁ Y₂ : Ix (Fin m) → RadSp P.k P.r z z' π π') (h₁ : ∀ a, Y₁ a ∈ K 0) (h₂ : ∀ a, Y₂ a ∈ K 0) :
    form μ 0 Y₁ Y₂ 0 = pairS (bet μ) Y₁ Y₂ := by
  have extK : ∀ v : Ix (Fin m) → RadSp P.k P.r z z' π π', (∀ a, v a ∈ K 0) →
      ∀ z, Function.extend (ixEmb hmn) v 0 z ∈ K 0 := by
    intro v hv z
    by_cases hz : ∃ a, ixEmb hmn a = z
    · obtain ⟨a, rfl⟩ := hz
      rw [(ixEmb_inj hmn).extend_apply]; exact hv a
    · rw [Function.extend_apply' _ _ _ hz]; exact (K 0).zero_mem
  have e1 := form_embed μ (ixEmb hmn) (ixEmb_inj hmn) Y₁ Y₂ 0
  have e2 := form_zero_eq_position_pairing hThm (Function.extend (ixEmb hmn) Y₁ 0) (Function.extend (ixEmb hmn) Y₂ 0)
    (extK _ h₁) (extK _ h₂)
  have e3 := pairS_embed (V := RadSp P.k P.r z z' π π') (bet μ) (fun v => bet_zero μ v) (ixEmb hmn) (ixEmb_inj hmn) Y₁ Y₂
  exact e1.symm.trans (e2.trans e3)

end EmbData

theorem final_ineq (Cst : ℝ) (A B P0 Q : ℂ) (qs : List ℂ) (hQ : Q = qs.prod)
    (hqs : ∀ z ∈ qs, 0 < z.re ∧ z.im = 0) (hAi : A.im = 0) (hBi : B.im = 0) (hdk : ‖P0‖ ^ 2 ≤ (A * B / Q).re) :
    ‖(Cst : ℂ) * P0‖ ^ 2 * (qs.map Complex.re).prod ≤ ((Cst : ℂ) * A).re * ((Cst : ℂ) * B).re := by
  obtain ⟨hQi, hQr⟩ := prod_real qs fun z hz => (hqs z hz).2
  have hpos : 0 < (qs.map Complex.re).prod := List.prod_pos fun x hx => by
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hx
    exact (hqs z hz).1
  have eA : A = (A.re : ℂ) := Complex.ext (by simp) (by simp [hAi])
  have eB : B = (B.re : ℂ) := Complex.ext (by simp) (by simp [hBi])
  have eQ : Q = ((qs.map Complex.re).prod : ℂ) := by
    rw [hQ]; exact Complex.ext (by simp [hQr]) (by simp [hQi])
  have h1 : (A * B / Q).re = A.re * B.re / (qs.map Complex.re).prod := by
    rw [eA, eB, eQ, ← Complex.ofReal_mul, ← Complex.ofReal_div, Complex.ofReal_re]
    simp
  rw [h1, le_div_iff₀ hpos] at hdk
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.re_ofReal_mul, Complex.re_ofReal_mul, mul_pow, sq_abs]
  nlinarith [sq_nonneg Cst]

theorem cast_map_pred {n m : ℕ} (h : n = m) (Q : ∀ k, List (Letter ℂ (Fin k)) → Prop) (u : List (Letter ℂ (Fin n)))
    (hu : Q n u) : Q m (u.map (castL h)) := by
  subst h; rwa [castL_rfl]

theorem Lw_qw (q : ℂ → ℂ) (ys : List ℝ) (w : List C.Letter) :
    ((Lw ys w).map fun l => qw q (Ww ys w) l.pt) = ys.map fun y : ℝ => qw q (D.positionted w) (y : ℂ) := by
  apply List.ext_getElem
  · simp [Lw_length]
  · intro i h1 h2
    rw [List.getElem_map, List.getElem_map, Lw_getElem, qw_Ww]

end

end Formalism.FourierDecayAlt.P.PBF

namespace Formalism.FourierDecayAlt.P

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.PBFVnice
noncomputable section

open Complex

namespace Formalism.FourierDecayAlt.P.PBFV

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem norm_iter_cexp (i : ℕ) (z : ℂ) : ‖iteratedFDeriv ℝ i Complex.exp z‖ = Real.exp z.re := by
  have hc : ContDiffAt ℂ (i : ℕ) Complex.exp z := Complex.contDiff_exp.contDiffAt
  rw [← hc.restrictScalars_iteratedFDeriv (𝕜 := ℝ)]
  simp only [Function.comp]
  rw [ContinuousMultilinearMap.norm_restrictScalars, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have h := congrFun (iteratedDeriv_cexp_const_mul i 1) z
  simp only [one_mul, one_pow] at h
  rw [h, Complex.norm_exp]

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def phaseL (s : ℂ) (D : Mat k r →L[ℝ] ℂ) : Mat k r →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun g => s * D g - starRingEnd ℂ (s * D g)
      map_add' := by intro g g'; simp only [map_add (f := _), mul_add]; ring
      map_smul' := by
        intro c g
        simp only [map_smul, Complex.real_smul, map_mul, Complex.conj_ofReal, RingHom.id_apply]
        ring }

theorem phaseL_apply (s : ℂ) (D : Mat k r →L[ℝ] ℂ) (g : Mat k r) :
    phaseL s D g = s * D g - starRingEnd ℂ (s * D g) := rfl

theorem phaseL_re (s : ℂ) (D : Mat k r →L[ℝ] ℂ) (g : Mat k r) : (phaseL s D g).re = 0 := by
  rw [phaseL_apply, Complex.sub_re, Complex.conj_re, sub_self]

theorem good_cexp (Bs : RealPlaceData k r Wp Wq) (ε : ℝ) (θ : Mat k r →L[ℝ] ℂ) (hθ : ∀ g, (θ g).re = 0) :
    JCx2.mnGood Bs ε (fun g => Complex.exp (θ g)) := by
  intro F hF
  obtain ⟨hF1, hF2, hF3⟩ := hF
  have hexp : ContDiff ℝ ⊤ Complex.exp := Complex.contDiff_exp
  have hc : ContDiff ℝ ⊤ (fun g : Mat k r => Complex.exp (θ g)) := hexp.comp θ.contDiff
  refine ⟨?_, fun A m => ?_, fun g hg h => hF3 g hg (fun h0 => h (by simp [h0]))⟩
  · intro g₀ hg₀
    obtain ⟨U, f, hU, hgU, hf, hff⟩ := hF1 g₀ hg₀
    have hc' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun g : Mat k r => Complex.exp (θ g)) U :=
      (hc.of_le le_top).contDiffOn
    exact ⟨U, fun g => Complex.exp (θ g) • f g, hU, hgU, hc'.smul hf,
      fun g hg hG => by simp only [hff g hg hG]⟩
  · obtain ⟨b, hb⟩ := hF2 (A + m) m
    set Lid : ℂ →L[ℝ] ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) :=
      ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℂ) (ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp))
      with hLid
    set Λ : Mat k r → ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) := fun g => Lid (Complex.exp (θ g)) with hΛdef
    have hΛ : ∀ g, Λ g = Complex.exp (θ g) • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp) := fun g => by
      simp [Λ, Lid]
    have hΛc : ContDiff ℝ ⊤ Λ := Lid.contDiff.comp hc
    obtain ⟨C1, hC1, hdlr⟩ := JCx4.dlr_bound (k := k) (r := r)
      (E := (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) m
    obtain ⟨K0, hK0⟩ : ∃ K : ℝ, ∀ M : Mat k r, ‖θ M‖ ≤ K * ‖M‖ := ⟨_, θ.le_opNorm⟩
    set K : ℝ := max K0 0 with hKdef
    have hK : ∀ M : Mat k r, ‖θ M‖ ≤ K * ‖M‖ := fun M =>
      (hK0 M).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    have hKnn : 0 ≤ K := le_max_right _ _
    have hθK := θ.opNorm_le_bound hKnn hK
    have hit : ∀ i g, ‖iteratedFDeriv ℝ i Λ g‖ ≤ ‖Lid‖ * K ^ i := by
      intro i g
      have h1 := Lid.norm_iteratedFDeriv_comp_left (f := fun g => Complex.exp (θ g)) (x := g) (N := ⊤) (n := i)
        hc.contDiffAt (by exact_mod_cast le_top)
      have h2 : iteratedFDeriv ℝ i (fun g => Complex.exp (θ g)) g =
          (iteratedFDeriv ℝ i Complex.exp (θ g)).compContinuousLinearMap (fun _ => θ) :=
        θ.iteratedFDeriv_comp_right (f := Complex.exp) hexp g (by exact_mod_cast le_top)
      have h3 := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
        (iteratedFDeriv ℝ i Complex.exp (θ g)) (fun _ : Fin i => θ)
      have h5 := h3.trans (mul_le_mul (le_of_eq (by rw [norm_iter_cexp, hθ, Real.exp_zero]))
        (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun _ _ => hθK))
        (Finset.prod_nonneg fun _ _ => norm_nonneg _) zero_le_one)
      rw [one_mul, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h5
      calc ‖iteratedFDeriv ℝ i Λ g‖ ≤ ‖Lid‖ * ‖iteratedFDeriv ℝ i (fun g => Complex.exp (θ g)) g‖ := h1
        _ ≤ ‖Lid‖ * K ^ i := by rw [h2]; exact mul_le_mul_of_nonneg_left h5 (norm_nonneg _)
    set C : ℝ := C1 * 2 ^ m * ((m + 1 : ℕ) * (‖Lid‖ * (1 + K) ^ m)) with hC
    have hab : ∀ u v : List (Mat k r), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ v, unitLie k r X) →
        u.length + v.length ≤ m → ∀ g ∈ GV k r, g ∉ (∅ : Set (Mat k r)) →
          ‖dLR u v Λ g‖ ≤ C * gN g ^ (m : ℝ) := by
      intro u v hu hv hl g hg _
      rw [Real.rpow_natCast]
      have h1 := hdlr Λ (hΛc.of_le (by exact_mod_cast le_top)) u v hu hv hl g
      have hg1 : 1 ≤ gN g := Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hg
      have hng : ‖g‖ ≤ gN g := JCx2.mn_norm_le_gN g
      have hsum : ∑ i ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ i Λ g‖ ≤
          (m + 1 : ℕ) * (‖Lid‖ * (1 + K) ^ m) := by
        calc ∑ i ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ i Λ g‖
            ≤ ∑ _i ∈ Finset.range (m + 1), ‖Lid‖ * (1 + K) ^ m := by
              refine Finset.sum_le_sum fun i hi => (hit i g).trans ?_
              refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
              have hi' : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
              calc K ^ i ≤ (1 + K) ^ i := pow_le_pow_left₀ hKnn (by linarith) i
                _ ≤ (1 + K) ^ m := pow_le_pow_right₀ (by linarith) hi'
          _ = (m + 1 : ℕ) * (‖Lid‖ * (1 + K) ^ m) := by simp
      have hpow : (1 + ‖g‖) ^ m ≤ 2 ^ m * gN g ^ m := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (by positivity) (by linarith) m
      have hS0 : 0 ≤ ∑ i ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ i Λ g‖ :=
        Finset.sum_nonneg fun _ _ => norm_nonneg _
      calc ‖dLR u v Λ g‖ ≤ C1 * (1 + ‖g‖) ^ m * ∑ i ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ i Λ g‖ := h1
        _ ≤ C1 * (2 ^ m * gN g ^ m) * ((m + 1 : ℕ) * (‖Lid‖ * (1 + K) ^ m)) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hpow hC1) hsum hS0
          exact mul_nonneg hC1 (by positivity)
        _ = C * gN g ^ m := by rw [hC]; ring
    have ha : CkOn (m : ℕ∞) Set.univ Λ := fun g₀ _ =>
      ⟨Set.univ, Λ, isOpen_univ, trivial, (hΛc.of_le (by exact_mod_cast le_top)).contDiffOn, fun _ _ _ => rfl⟩
    have hb' := Formalism.FourierDecayAlt.P.BetaSesquilinearity.prodBound (O := ∅) (UU := Set.univ) isOpen_empty (fun g _ => Or.inr trivial)
      (A := A) (d := (m : ℝ)) ha hab hb (fun g _ h => h.elim)
    have e : (fun g => Complex.exp (θ g) • F g) = Formalism.FourierDecayAlt.P.BetaSesquilinearity.ap Λ F := by
      funext g
      simp [Formalism.FourierDecayAlt.P.BetaSesquilinearity.ap, hΛ]
    rw [e]
    exact ⟨_, hb'⟩

theorem dmin_one (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mat k r) (h : 1 < r + 2) :
    Dmin k r z z' g ⟨1, h⟩ = herm (Hpk k r) (g *ᵥ fvec k r z' 0) (fvec k r z 0) := by
  unfold Dmin
  rw [Matrix.det_fin_one]
  rfl

theorem fsv_dmin_one (s : ℂ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mat k r) (h : 1 < r + 2) :
    P5.fsv s (Dmin k r z z' g ⟨1, h⟩) =
      Complex.exp (phaseL s (JCx2.mnLinHerm (fvec k r z' 0) (fvec k r z 0)) g) := by
  rw [dmin_one, phaseL_apply, P5.fsv, map_mul]
  rfl

theorem good_fsv_dmin (Bs : RealPlaceData k r Wp Wq) (ε : ℝ) (s : ℂ) (h : 1 < r + 2) :
    JCx2.mnGood Bs ε (fun g => P5.fsv s (Dmin k r Bs.z Bs.z' g ⟨1, h⟩)) := by
  intro F hF
  have := good_cexp Bs ε (phaseL s (JCx2.mnLinHerm (fvec k r Bs.z' 0) (fvec k r Bs.z 0))) (phaseL_re _ _) F hF
  simpa only [fsv_dmin_one] using this

theorem uInv_nice (Bs : RealPlaceData k r Wp Wq) (ε : ℝ) (s : ℂ) :
    ∀ (w : List C.Letter) (x : Wd.Ix (Fin w.length) → Mat k r → (Wq →L[ℂ] Wp)),
      (∀ e, JC.NiceCoef Bs ε (x e)) → ∀ e, JC.NiceCoef Bs ε (KB.uInv s w x e)
  | [], x, hx, e => hx e
  | l :: w, x, hx, e => by
    unfold KB.uInv
    split_ifs
    · exact uInv_nice Bs ε s w _ (fun e' => hx _) _
    · exact JCx2.mn_nice_add (uInv_nice Bs ε s w _ (fun e' => hx _) _)
        (JCx2.mn_nice_smul _ (uInv_nice Bs ε s w _ (fun e' => hx _) _))
    · exact JCx2.mn_nice_add (uInv_nice Bs ε s w _ (fun e' => hx _) _)
        (JCx2.mn_nice_smul _ (uInv_nice Bs ε s w _ (fun e' => hx _) _))

theorem waveG_nice (Bs : RealPlaceData k r Wp Wq) (ε : ℝ) (s : ℂ) (w : List C.Letter)
    (x : Wd.Ix (Fin w.length) → Mat k r → (Wq →L[ℂ] Wp)) (hx : ∀ e, JC.NiceCoef Bs ε (x e)) :
    ∀ e, JC.NiceCoef Bs ε (KB.waveG Bs s w x e) := fun e =>
  good_fsv_dmin Bs ε s (by omega) _ (uInv_nice Bs ε s w x hx e)

end Formalism.FourierDecayAlt.P.PBFV
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftCapelliOperators
namespace Formalism.FourierDecayAlt.P.TLB

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
open scoped ComplexConjugate

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section terms

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]


open Classical in
def cTerm (c : ℂ) (w : List (B.Mat k r)) : B.DTerm k r Wp Wq where
  coef := fun _ => c • ContinuousLinearMap.id ℂ _
  coefAdj := fun _ => conj c • ContinuousLinearMap.id ℂ _
  word := if ∀ X ∈ w, B.inLie k r X then w else []
  word_lie := by
    split_ifs with h
    · exact h
    · simp
  adj_id := by
    intro x A B'
    simp only [_root_.smul_apply, ContinuousLinearMap.id_apply]
    rw [Formalism.FourierDecayAlt.P5.HerB.hs_smul_left, Formalism.FourierDecayAlt.P5.HerB.hs_smul_right, Complex.conj_conj]

theorem cTerm_word {c : ℂ} {w : List (B.Mat k r)} (hw : ∀ X ∈ w, B.inLie k r X) :
    (cTerm (Wp := Wp) (Wq := Wq) c w).word = w := by
  unfold cTerm
  dsimp only
  rw [if_pos hw]

theorem cTerm_word_le (c : ℂ) (w : List (B.Mat k r)) :
    (cTerm (Wp := Wp) (Wq := Wq) c w).word.length ≤ w.length := by
  unfold cTerm
  dsimp only
  split_ifs <;> simp

theorem cTerm_apply (c : ℂ) (w : List (B.Mat k r)) (hw : ∀ X ∈ w, B.inLie k r X)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r) :
    (cTerm (Wp := Wp) (Wq := Wq) c w).coef g (B.Rw (cTerm (Wp := Wp) (Wq := Wq) c w).word F g) = c • B.Rw w F g := by
  rw [cTerm_word hw]
  simp [cTerm]

theorem opOrder_le_of (Θ : B.DiffOp k r Wp Wq) (n : ℕ) (h : ∀ T ∈ Θ, T.word.length ≤ n) : B.opOrder Θ ≤ n := by
  induction Θ with
  | nil => simp [B.opOrder]
  | cons T Θ ih =>
    simp only [B.opOrder, List.map_cons, List.foldr_cons] at ih ⊢
    exact max_le (h T List.mem_cons_self) (ih fun T' hT' => h T' (List.mem_cons_of_mem _ hT'))

theorem opOrder_cons_eq (T : B.DTerm k r Wp Wq) (Θ : B.DiffOp k r Wp Wq)
    (h : ∀ T' ∈ Θ, T'.word.length ≤ T.word.length) : B.opOrder (T :: Θ) = T.word.length := by
  have h2 := opOrder_le_of Θ _ h
  simp only [B.opOrder, List.map_cons, List.foldr_cons] at h2 ⊢
  exact max_eq_left h2

def capOp (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (s : ℂ)
    (Lw : List (ℂ × List (B.Mat k r))) : B.DiffOp k r Wp Wq :=
  cTerm 0 (List.replicate (2 * r + k + 1) 0) :: Lw.map fun cw => cTerm (s * cw.1) cw.2

theorem zero_lie : B.inLie k r (0 : B.Mat k r) := by
  simp [B.inLie]

theorem opApply_capOp_tail (s : ℂ) (Lw : List (ℂ × List (B.Mat k r)))
    (hL : ∀ cw ∈ Lw, ∀ X ∈ cw.2, B.inLie k r X) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r) :
    B.opApply (Lw.map fun cw => (cTerm (Wp := Wp) (Wq := Wq) (s * cw.1) cw.2)) F g =
      s • (Lw.map fun cw => cw.1 • B.Rw cw.2 F g).sum := by
  induction Lw with
  | nil => simp [B.opApply]
  | cons cw Lw ih =>
    have ih' := ih fun cw' h => hL cw' (List.mem_cons_of_mem _ h)
    simp only [B.opApply, List.map_cons, List.sum_cons, List.map_map] at ih' ⊢
    rw [smul_add, ← ih']
    congr 1
    rw [cTerm_apply _ _ (hL cw List.mem_cons_self), mul_smul]

theorem opApply_capOp (s : ℂ) (Lw : List (ℂ × List (B.Mat k r)))
    (hL : ∀ cw ∈ Lw, ∀ X ∈ cw.2, B.inLie k r X) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r) :
    B.opApply (capOp k r Wp Wq s Lw) F g = s • (Lw.map fun cw => cw.1 • B.Rw cw.2 F g).sum := by
  have e : B.opApply (capOp k r Wp Wq s Lw) F g =
      (cTerm (Wp := Wp) (Wq := Wq) 0 (List.replicate (2 * r + k + 1) 0)).coef g
        (B.Rw (cTerm (Wp := Wp) (Wq := Wq) 0 (List.replicate (2 * r + k + 1) 0)).word F g) +
      B.opApply (Lw.map fun cw => (cTerm (Wp := Wp) (Wq := Wq) (s * cw.1) cw.2)) F g := by
    simp [B.opApply, capOp]
  rw [e, opApply_capOp_tail s Lw hL F g]
  simp [cTerm]

theorem opOrder_capOp (s : ℂ) (Lw : List (ℂ × List (B.Mat k r)))
    (hL : ∀ cw ∈ Lw, cw.2.length ≤ 2 * r + k + 1) :
    B.opOrder (capOp k r Wp Wq s Lw) = 2 * r + k + 1 := by
  have hw : (cTerm (Wp := Wp) (Wq := Wq) 0 (List.replicate (2 * r + k + 1) (0 : B.Mat k r))).word =
      List.replicate (2 * r + k + 1) 0 :=
    cTerm_word fun X hX => by rw [List.eq_of_mem_replicate hX]; exact zero_lie
  unfold capOp
  rw [opOrder_cons_eq, hw, List.length_replicate]
  intro T hT
  rw [hw, List.length_replicate]
  obtain ⟨cw, hcw, rfl⟩ := List.mem_map.1 hT
  exact (cTerm_word_le _ _).trans (hL cw hcw)

theorem cTerm_inDDPlus (D : B.RealPlaceData k r Wp Wq) (c : ℂ) (w : List (B.Mat k r)) (o : ℕ) (hw : w.length ≤ o)
    (T : B.DTerm k r Wp Wq) (hT : T = cTerm c w) :
    (B.CkOn ⊤ (C6.domL D ∅) T.coef ∧ B.CkOn ⊤ (C6.domL D ∅) T.coefAdj) ∧
    ∃ (P : B.Mat k r → ℂ) (a b : Fin (r + 2) → ℕ) (cc : ℕ) (es : List (Fin 0 × List (B.Mat k r))),
      U.IsPolyDeg 0 P ∧ (∀ l, l ∉ (∅ : Finset (Fin (r + 2))) → l ≠ Fin.last (r + 1) → a l = 0 ∧ b l = 0) ∧
      T.word.length + (es.map fun e => e.2.length).sum ≤ o ∧ (∀ e ∈ es, ∀ X ∈ e.2, B.inLie k r X) ∧
      ∀ g ∈ C6.domL D ∅, T.coef g = (P g * C6.monoM D a b cc g) • C6.Epart (fun j : Fin 0 => j.elim0) es g := by
  subst hT
  refine ⟨⟨fun g₀ _ => ⟨Set.univ, fun _ => c • ContinuousLinearMap.id ℂ _, isOpen_univ, trivial, contDiffOn_const,
      fun _ _ _ => rfl⟩, fun g₀ _ => ⟨Set.univ, fun _ => conj c • ContinuousLinearMap.id ℂ _, isOpen_univ, trivial,
      contDiffOn_const, fun _ _ _ => rfl⟩⟩, fun _ => c, fun _ => 0, fun _ => 0, 0, [], ?_, ?_, ?_, by simp, ?_⟩
  · exact ⟨MvPolynomial.C c, by simp, fun g => by simp⟩
  · intro l _ _; exact ⟨rfl, rfl⟩
  · simpa using (cTerm_word_le (Wp := Wp) (Wq := Wq) c w).trans hw
  · intro g _
    simp [C6.monoM, C6.Epart, cTerm]
    rfl

end terms

end

end Formalism.FourierDecayAlt.P.TLB

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

noncomputable section

theorem lift_capelli_operators : TL.LiftCap := by
  intro Wp Wq _ _ _ _ _ _ P Bs X μ L st l0 hD Y
  obtain ⟨Lw, hLw, hCV⟩ := Formalism.FourierDecayAlt.P.capelli_word_sum P.k P.r Y
  set s : ℂ := M.sgn P l0 with hs
  have hLie : ∀ cw ∈ Lw, ∀ X ∈ cw.2, B.inLie P.k P.r X := fun cw h X hX => ((hLw cw h).1 X hX).1
  have hlen : ∀ cw ∈ Lw, cw.2.length ≤ 2 * P.r + P.k + 1 := fun cw h => (hLw cw h).2
  set Dop := TLB.capOp P.k P.r Wp Wq s Lw with hDop
  have hApp : ∀ f : B.Mat P.k P.r → (Wq →L[ℂ] Wp), B.CkOn ((2 * P.r + P.k + 1 : ℕ) : ℕ∞) (B.GV P.k P.r) f →
      ∀ g ∈ B.GV P.k P.r, B.opApply Dop f g = s • Q.CV P.k P.r Y f g := by
    intro f hf g hg
    rw [hDop, TLB.opApply_capOp s Lw hLie, hCV _ _ f hf g hg hg]
  refine ⟨0, fun j => j.elim0, Dop, fun j => j.elim0, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro T hT
    rcases List.mem_cons.1 hT with rfl | hT
    · exact (TLB.cTerm_inDDPlus Bs 0 _ _ (le_of_eq (List.length_replicate ..)) _ rfl).1
    · obtain ⟨cw, hcw, rfl⟩ := List.mem_map.1 hT
      exact (TLB.cTerm_inDDPlus Bs _ _ _ (hlen cw hcw) _ rfl).1
  · intro p hp f hf g hg
    rw [hDop, TLB.opOrder_capOp s Lw hlen] at hf
    have hgG : g ∈ B.GV P.k P.r := hg.1
    have hs' := Formalism.FourierDecayAlt.P.B7.sgs_mem Bs hp hgG
    rw [hApp _ (Formalism.FourierDecayAlt.P.B5.ckOn_rho Bs hp hf) g hgG,
      Formalism.FourierDecayAlt.P.capelli_rho_commute P.k P.r Wp Wq Bs Y f p hp hf g hgG]
    simp only [B.rho]
    rw [hApp f hf _ hs', ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  · intro T hT
    rcases List.mem_cons.1 hT with rfl | hT
    · exact (TLB.cTerm_inDDPlus Bs 0 _ _ (le_of_eq (List.length_replicate ..)) _ rfl).2
    · obtain ⟨cw, hcw, rfl⟩ := List.mem_map.1 hT
      exact (TLB.cTerm_inDDPlus Bs _ _ _ (hlen cw hcw) _ rfl).2
  · intro F hF Φ hΦ y hy
    obtain ⟨ε, hε, hN⟩ := (compact_support_facts P.k P.r Wp Wq Bs F hF).1
    have hz := Bs.z_mem
    have hz' := Bs.z'_mem
    have hL := hD.2.2.1
    have hst := hD.2.2.2.1
    have hJ := Formalism.FourierDecayAlt.P.bessel_function_finite_class P.k P.r Wp Wq Bs F ε hε hN
    have hGV : wCell P.k P.r (Fin.last P.r) y.1 * y.2 ∈ B.GV P.k P.r := by
      rw [P5.Rad.wCell_last_eq]
      exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (big_cell_mem_holds _ _ _ 1 hy.1 (by simp)) hy.2.1.1
    have hh : wCell P.k P.r (Fin.last P.r) y.1 * y.2 ∈ JF.Om P.k P.r Bs.z Bs.z' :=
      ⟨hGV, P5.Rad.wCell_mem_omPlus hz hz' hy.1 hy.2.1 hy.2.2⟩
    have h1 := JCx2.rma_QQi X L hL st s hst Y 0 0 Φ hy
    have h2 := (JCx2.rma_sandw X L hL Y P.r le_rfl _ _ (JCx2.rma_base X Y) (JCx2.rma_QL_loc Y)).2 0 0
      (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) (resG P.k P.r (Fin.last P.r) (B.JF Bs F)) (fun y' hy' => hΦ y' hy') y hy
    have h3 := Formalism.FourierDecayAlt.P.chain_recursion_all_levels Wp Wq P.k P.r Bs.z Bs.z' Bs.π Bs.π' (Fin.last P.r) _ Y 0 0 hz hz'
      (JCx2.rma_isDom_omPlus hz hz') _ hJ y.1 hy.1 y.2 hy.2.1 hh.2
    rw [Fin.val_last] at h3
    have h4 := (JCx2.bcGood_tL (Bs := Bs) (ε := ε) s Y 0 0).2.1 F hN _ hh
    have h5 := Formalism.FourierDecayAlt.P.Qx8.JF_congr Bs (F := fun g => s • Q.tL P.k P.r Bs.z Bs.z' 0 Y 0 0 F g)
      (F' := B.opApply Dop F) (a := 1) (fun g hg => by
        rw [one_smul, hApp F (Formalism.FourierDecayAlt.P.B5.ckOn_mono le_top hF.1) g hg]; rfl) hGV
    refine Eq.trans h1 ?_
    rw [h2, ← h3]
    simp only [Q.resG]
    have h4' : B.JF Bs (fun g => s • Q.tL P.k P.r Bs.z Bs.z' 0 Y 0 0 F g) (wCell P.k P.r (Fin.last P.r) y.1 * y.2) =
        s • Q.tL P.k P.r Bs.z Bs.z' 0 Y 0 0 (B.JF Bs F) (wCell P.k P.r (Fin.last P.r) y.1 * y.2) := h4
    rw [h5, one_smul, h4', smul_comm]

end

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnFoldRev
open Formalism.FourierDecayAlt
open Formalism.REAL Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P.CutMP.En

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem cV_smul {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (Y α : ℂ) (f : B.Mat k r → E) :
    Q.CV k r Y (α • f) = α • Q.CV k r Y f :=
  Formalism.FourierDecayAlt.P5.qminorOp_smulC (Formalism.FourierDecayAlt.P5.eH_smulC (k := k) (r := r)) _ _ _ α f

section fold

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] {z z' : Fin (2 * r + k + 1) → ℂ} {π : Q.Mx k r → (Wp →L[ℂ] Wp)}
  {π' : Q.Mx k r → (Wq →L[ℂ] Wq)} {Dm : Set (Q.Mx k r)}

theorem ckOn_of_ffl {J : Q.Mx k r → (Wq →L[ℂ] Wp)} (hJ : J ∈ Q.FFl k r z z' π π' 0 Dm) :
    B.CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (Dm ∩ B.GV k r) J := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hc, he⟩ := hJ.1 g₀ ⟨Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hg₀.2, hg₀.1⟩
  exact ⟨U, F, hU, hgU, hc.of_le (by exact_mod_cast le_top), fun g hg hgG => he g hg (Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hgG)⟩

theorem letter_congr (hCL : CVLocal) (hDm : IsOpen Dm) {J₁ J₂ : Q.Mx k r → (Wq →L[ℂ] Wp)}
    (h₁ : J₁ ∈ Q.FFl k r z z' π π' 0 Dm) (h₂ : J₂ ∈ Q.FFl k r z z' π π' 0 Dm)
    (he : ∀ g ∈ Q.Glev k r 0 ∩ Dm, J₁ g = J₂ g) (Y : ℝ) (s : ℂ) :
    ∀ g ∈ Q.Glev k r 0 ∩ Dm, (s • Q.CV k r (Y : ℂ) J₁) g = (s • Q.CV k r (Y : ℂ) J₂) g := by
  intro g hg
  have := hCL k r _ Dm J₁ J₂ (Y : ℂ) hDm (ckOn_of_ffl h₁) (ckOn_of_ffl h₂)
    (fun x hx => he x ⟨Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hx.2, hx.1⟩) g ⟨hg.2, hg.1.1⟩
  simp only [Pi.smul_apply, this]

theorem letter_swap (hDm : IsOpen Dm) {J : Q.Mx k r → (Wq →L[ℂ] Wp)} (hJ : J ∈ Q.FFl k r z z' π π' 0 Dm)
    (x y : ℝ) (s : ℂ) : ∀ g ∈ Q.Glev k r 0 ∩ Dm,
      (s • Q.CV k r (x : ℂ) (s • Q.CV k r (y : ℂ) J)) g = (s • Q.CV k r (y : ℂ) (s • Q.CV k r (x : ℂ) J)) g := by
  intro g hg
  simp only [cV_smul, Pi.smul_apply]
  unfold Q.CV
  rw [Formalism.FourierDecayAlt.P.capelli_commutation _ k r 0 Dm J hDm hJ.1 g hg]

theorem foldCV_append (s : ℂ) (l₁ l₂ : List C.Letter) (J : Q.Mx k r → (Wq →L[ℂ] Wp)) :
    foldCV k r s (l₁ ++ l₂) J = foldCV k r s l₁ (foldCV k r s l₂ J) := by
  unfold foldCV; rw [List.foldr_append]

end fold

theorem foldRev_of (hCL : CVLocal) : FoldRev := by
  intro k r Wp Wq _ _ _ _ z z' π π' Dm hDm hcl J hJ s a
  have hcomm : ∀ (b : List C.Letter) (J : Q.Mx k r → (Wq →L[ℂ] Wp)), J ∈ Q.FFl k r z z' π π' 0 Dm →
      ∀ x : C.Letter, ∀ g ∈ Q.Glev k r 0 ∩ Dm,
        foldCV k r s b (s • Q.CV k r (x.2 : ℂ) J) g = (s • Q.CV k r (x.2 : ℂ) (foldCV k r s b J)) g := by
    intro b
    induction b with
    | nil => intro J _ x g _; rfl
    | cons y b ih =>
      intro J hJ x g hg
      have h1 := letter_congr hCL hDm (foldCV_mem hcl (hcl J hJ x.2 s) s b)
        (hcl _ (foldCV_mem hcl hJ s b) x.2 s) (ih J hJ x) y.2 s g hg
      have h2 := letter_swap hDm (foldCV_mem hcl hJ s b) y.2 x.2 s g hg
      rw [foldCV_cons, h1, h2]
      rfl
  induction a generalizing J with
  | nil => intro g _; rfl
  | cons x a ih =>
    intro g hg
    rw [List.reverse_cons, foldCV_append]
    rw [ih (foldCV k r s [x] J) (hcl J hJ x.2 s) g hg]
    exact hcomm a J hJ x g hg

theorem folding_reversal_holds : FoldRev := foldRev_of coefficient_vector_locality

end Formalism.FourierDecayAlt.P.CutMP.En
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDRInvDefs
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open Matrix

noncomputable section

def alP (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (i : Fin (k + 1)) : ℂ :=
  ((-1 : ℂ) ^ (i : ℕ)) * herm (Hpk k r) (bvec (wI k r i)) z'

def beM (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (t : Fin (k + 1)) : ℂ :=
  ((-1 : ℂ) ^ (t : ℕ)) * z' (wI k r t)

def RInvAlphaP : Prop :=
  ∀ (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (w m : B.Mat k r), inWb k r z' → w ∈ UWset k r z' → m ∈ Nset k r →
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (X : (Fin (r + k) → Fin (2 * r + k + 1)) → M),
      ∑ c ∈ jSetR k r, (∑ i : Fin (k + 1), alP k r z' i * ((m * w)⁻¹.submatrix c (rowsR k r i)).det) • X c =
        ((m * w)⁻¹).det • ∑ i : Fin (k + 1), alP k r z' i • X (rowsR k r i)

def RInvBetaP : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (g S : B.Mat k r), g ∈ B.GV k r → S ∈ B.GV k r →
    ∀ d : Fin (r + k) → Fin (2 * r + k + 1),
      ∑ J ∈ jSetR k r, beJ k r z g J * (S.submatrix J d).det = S.det * beJ k r z (g * S) d

def RInvBetaLeftP : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (h m g : B.Mat k r), inWb k r z → h ∈ UWset k r z → m ∈ Nset k r →
    g ∈ B.GV k r → ∀ J : Fin (r + k) → Fin (2 * r + k + 1), beJ k r z (h⁻¹ * m⁻¹ * g) J = beJ k r z g J

def RInvAlphaM : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (g S : B.Mat k r), g ∈ B.GV k r → S ∈ B.GV k r →
    ∀ c : Fin (r + k) → Fin (2 * r + k + 1),
      ∑ J ∈ jSetR k r, alJ k r z g J * ((S⁻¹).submatrix c J).det = (S⁻¹).det * alJ k r z (g * S) c

def RInvAlphaLeftM : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (h m g : B.Mat k r), inWb k r z → h ∈ UWset k r z → m ∈ Nset k r →
    g ∈ B.GV k r → ∀ J : Fin (r + k) → Fin (2 * r + k + 1), alJ k r z (h⁻¹ * m⁻¹ * g) J = alJ k r z g J

def RInvBetaM : Prop :=
  ∀ (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (w m : B.Mat k r), inWb k r z' → w ∈ UWset k r z' → m ∈ Nset k r →
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (X : (Fin (r + k) → Fin (2 * r + k + 1)) → M),
      ∑ d ∈ jSetR k r, (∑ t : Fin (k + 1), beM k r z' t * ((m * w).submatrix (colsV k r t) d).det) • X d =
        (m * w).det • ∑ t : Fin (k + 1), beM k r z' t • X (colsV k r t)

end

end Formalism.FourierDecayAlt.P.CutMP
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutRegFFName
namespace Formalism.FourierDecayAlt.P.CutMP

abbrev JfSmoothBuilt : Prop := JfSmoothDS

end Formalism.FourierDecayAlt.P.CutMP
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpPCont
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

noncomputable section

section tdU

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

def tdU (r : ℕ) (Y : ℂ) : ℕ → Fin 2 → (((Fin r → ℂ) → X) → (Fin r → ℂ) → X)
  | 0, b => if b = 0 then id else fun _ => 0
  | 1, b => if h : 1 ≤ r then (if b = 0 then fun f => Y • f + pOp ⟨r - 1, by omega⟩ f else ciOp ⟨r - 1, by omega⟩)
      else fun _ => 0
  | m + 2, b => if h : m + 2 ≤ r then
        fun f => Y • tdU r Y (m + 1) b f + pOp ⟨r - (m + 2), by omega⟩ (tdU r Y (m + 1) b f) -
          cOp ⟨r - (m + 1), by omega⟩ (ciOp ⟨r - (m + 2), by omega⟩ (tdU r Y m b f))
      else fun _ => 0

end tdU

def JDRCont : Prop :=
  ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (r : ℕ) (Y : ℂ) (O : Set (Fin r → ℂ)), IsOpen O → O ⊆ OmX r →
    ∀ f : (Fin r → ℂ) → X, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f O → ∀ c ∈ O, ∀ b : Fin 2,
      tdU r Y r b f c = Q.cmp (Q.vAB r Y r) b f c

end

end Formalism.FourierDecayAlt.P.CutMP
end
