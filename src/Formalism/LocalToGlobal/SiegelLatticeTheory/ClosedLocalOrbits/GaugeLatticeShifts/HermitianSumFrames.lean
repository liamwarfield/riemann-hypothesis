module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RowsAbsX
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHDef
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PtCellUniq
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TermDefPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHGlue

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HermitianSumFrames
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ComplexConjugate
open Matrix

namespace Formalism.L2.SG.RealObj.HermitianSumRootCoordinateFrames

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj.HermitianBlockSpans Formalism.L2.SG.RealObj.RootCoordinateFrames

theorem nxt_eq {n r : ℕ} (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (a : Fin r) : nxt e z a = fam e z a.succ := by
  unfold nxt fam
  split_ifs with h
  · have hs : a.succ = Fin.castSucc ⟨a.1 + 1, h⟩ := Fin.ext (by simp)
    rw [hs, Fin.snoc_castSucc]
  · have hs : a.succ = Fin.last r := Fin.ext (by simp; omega)
    rw [hs, Fin.snoc_last]

theorem hJ_sum_left {n m : ℕ} (ε : Fin n → Bool) (c : Fin m → ℂ) (v : Fin m → Fin n → ℂ) (w : Fin n → ℂ) :
    hJ ε (∑ i, c i • v i) w = ∑ i, star (c i) * hJ ε (v i) w := by
  unfold hJ
  rw [star_sum, sum_dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [star_smul, smul_dotProduct, smul_eq_mul]

private theorem hJ_fintype_sum_smul_right {n : ℕ} {ι : Type} [Fintype ι] (ε : Fin n → Bool) (x : Fin n → ℂ)
    (Q : ι → ℂ) (y : ι → Fin n → ℂ) :
    hJ ε x (∑ c, Q c • y c) = ∑ c, Q c * hJ ε x (y c) := by
  unfold hJ
  rw [Matrix.mulVec_sum, dotProduct_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem RootCoordFrame_holds : RootCoordFrame := by
  intro n r ε e f z hfe hfz g P hP a
  unfold rootCoord
  rw [nxt_eq, hP, hJ_fintype_sum_smul_right]
  rw [Finset.sum_eq_single a.castSucc]
  · rw [show fam e z a.castSucc = e a from by unfold fam; exact Fin.snoc_castSucc _ _ _, hfe, if_pos rfl, mul_one]
  · intro c _ hc
    refine Fin.lastCases ?_ (fun b hb => ?_) c hc
    · intro _
      rw [show fam e z (Fin.last r) = z from by unfold fam; exact Fin.snoc_last _ _, hfz, mul_zero]
    · rw [show fam e z b.castSucc = e b from by unfold fam; exact Fin.snoc_castSucc _ _ _, hfe]
      have hab : a ≠ b := fun h => hb (by rw [h])
      rw [if_neg hab, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem ZhatNAct_holds : ZhatNAct := by
  intro n r ε f f' s si s' g P P' hsi hinv hP hP'
  have hs : s * si = 1 := mul_eq_one_comm.mp hsi
  ext a b
  have h1 : (si * g * s') *ᵥ f' b = si *ᵥ (g *ᵥ (s' *ᵥ f' b)) := by
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have h2 : hJ ε (f a) (si *ᵥ (g *ᵥ (s' *ᵥ f' b))) = hJ ε (s *ᵥ f a) (g *ᵥ (s' *ᵥ f' b)) := by
    rw [← hinv (f a) (si *ᵥ _), Matrix.mulVec_mulVec, hs, Matrix.one_mulVec]
  show hJ ε (f a) ((si * g * s') *ᵥ f' b) = _
  rw [h1, h2, hP a, hP' b, hJ_sum_left, Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul, hJ_fintype_sum_smul_right, Matrix.mul_apply, Matrix.map_apply,
    Matrix.transpose_apply, Zhat, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => ?_
  ring

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem FrameAtV_holds : FrameAtV := by
  intro D X u v
  have hc : ∀ p q : (VS D).V, hJ (X.B.I.ε v) (rv X.B.I v (X.crd p)) (rv X.B.I v (X.crd q)) =
      embS D (X.pl v) ((VS D).hT p q) := fun p q => Formalism.L2.SG.PoincareInHH.Cut.hJ_crd (X := X) v p q
  have hs : ∀ p q : (VS D).V, (VS D).hT q p = starRingEnd D.host.E ((VS D).hT p q) := by
    intro p q
    first
    | exact ((VS D).herm.eq p q).symm
    | exact ((VS D).herm p q).symm
  simp only [HidaSetting.eR, HidaSetting.fR, HidaSetting.zR, hc]
  refine ⟨fun a b => by rw [X.ee a b, map_zero], fun a b => by rw [X.ff a b, map_zero],
    fun a b => ?_, fun a b => ?_,
    fun a => ⟨by rw [(X.zu_orth u a).1, map_zero], by rw [(X.zu_orth u a).2, map_zero]⟩, ?_, ?_⟩
  · rw [X.ef a b]
    split_ifs <;> simp
  · rw [hs, X.ef b a]
    by_cases h : a = b
    · subst h
      simp
    · rw [if_neg (Ne.symm h), if_neg h, map_zero, map_zero]
  · rw [X.zu_norm u, map_neg, map_natCast]
    simp [Tw]
  · unfold Tw
    exact_mod_cast (D.mem u).A.T_prime.ne_zero

end Formalism.L2.SG.RealObj.HermitianSumRootCoordinateFrames
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RowsAbsPt
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermDef

namespace Formalism.L2.SG.RowsAbsX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem atPt_uniq {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}
    (Λ : Submodule (𝓞 E) S.V) {T T' : E} (F : LFlag S r T) (P : LFlag S r T' → Prop) (t : TermQ Λ F P)
    (w w' : Point E (r + 1)) (h : AtPt Λ F P t w) (h' : AtPt Λ F P t w') : w = w' := by
  obtain ⟨F₁, ⟨h₁, e₁⟩, -, c₁⟩ := h
  obtain ⟨F₂, ⟨h₂, e₂⟩, -, c₂⟩ := h'
  have hq : Quot.mk (Rel Λ F P) ⟨F₁, h₁⟩ = Quot.mk (Rel Λ F P) ⟨F₂, h₂⟩ := e₁.trans e₂.symm
  have hg := Quot.eqvGen_exact hq
  have inv : ∀ x y : Carrier P, Relation.EqvGen (Rel Λ F P) x y → ∀ v : Point E (r + 1),
      (IsInCell (ZhatOM (ZhatL F x.1)) v ↔ IsInCell (ZhatOM (ZhatL F y.1)) v) := by
    intro x y hxy
    induction hxy with
    | rel x y hr => exact Formalism.L2.SG.Pf.cell_function_holds Λ F P x y hr
    | refl x => exact fun v => Iff.rfl
    | symm x y _ ih => exact fun v => (ih v).symm
    | trans x y z _ _ ih₁ ih₂ => exact fun v => (ih₁ v).trans (ih₂ v)
  exact Formalism.L2.SG.PtCell.isInCell_uniq ((inv _ _ hg w).1 c₁) c₂

variable {D : D7} (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word)

theorem ptUniq_holds : PtUniq X Y u u' := fun t w w' h h' => atPt_uniq _ _ _ t.cls w w' h h'

end Formalism.L2.SG.RowsAbsX
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHVolP
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Formalism.L2.SG.Pf.BH

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf

theorem ballDim : BallDim := by
  intro E _ _ _ _ _ s
  let f := (stdOrthonormalBasis ℝ E).repr
  have hf : MeasurePreserving f := f.measurePreserving
  have e : f ⁻¹' Metric.ball 0 s = Metric.ball 0 s := by
    ext x
    simp only [Set.mem_preimage, Metric.mem_ball, dist_zero_right, LinearIsometryEquiv.norm_map]
  rw [← e, hf.measure_preimage measurableSet_ball.nullMeasurableSet]

variable {k r : ℕ}

theorem measurableSet_expImage_univ (S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) :
    MeasurableSet ((fun x : Formalism.MainNotions.S.lieE S =>
      fun i j => NormedSpace.exp (Formalism.MainNotions.S.unrealify (x : EuclideanSpace ℝ _)) i j : Formalism.MainNotions.S.lieE S → Mt k r) '' Set.univ) := by
  have hE := Formalism.MainNotions.BridgeCSB.continuous_expLie (k := k) (r := r) S
  have hU : (Set.univ : Set (Formalism.MainNotions.S.lieE S)) = ⋃ n : ℕ, Metric.closedBall 0 (n : ℝ) := by
    ext x
    simp only [Set.mem_univ, Set.mem_iUnion, Metric.mem_closedBall, dist_zero_right, true_iff]
    obtain ⟨n, hn⟩ := exists_nat_ge ‖x‖
    exact ⟨n, hn⟩
  rw [hU, Set.image_iUnion]
  exact MeasurableSet.iUnion fun n => ((isCompact_closedBall _ _).image hE).isClosed.measurableSet

theorem rhoMeas : RhoMeas := by
  intro k r S
  refine measurable_of_Iio fun t => ?_
  have e : rhoS k r S ⁻¹' Set.Iio t = (fun x : Formalism.MainNotions.S.lieE S =>
      fun i j => NormedSpace.exp (Formalism.MainNotions.S.unrealify (x : EuclideanSpace ℝ _)) i j : Formalism.MainNotions.S.lieE S → Mt k r) ''
        {Y | (‖(Y : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))‖₊ : ℝ≥0∞) < t} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Iio, rhoS, iInf_lt_iff, Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨Y, hY, hlt⟩; exact ⟨Y, hlt, hY⟩
    · rintro ⟨Y, hlt, hY⟩; exact ⟨Y, hY, hlt⟩
  rw [e]
  rcases eq_or_ne t ⊤ with rfl | ht
  · have : {Y : Formalism.MainNotions.S.lieE S | (‖(Y : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))‖₊ : ℝ≥0∞)
        < ⊤} = Set.univ := by
      ext Y; simp
    rw [this]
    exact measurableSet_expImage_univ S
  · rcases eq_or_ne t 0 with rfl | ht0
    · have : {Y : Formalism.MainNotions.S.lieE S | (‖(Y : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))‖₊ : ℝ≥0∞)
          < 0} = ∅ := by ext Y; simp
      rw [this, Set.image_empty]; exact MeasurableSet.empty
    · have hb : {Y : Formalism.MainNotions.S.lieE S | (‖(Y : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))‖₊ : ℝ≥0∞)
          < t} = Metric.ball 0 t.toReal := by
        ext Y
        simp only [Set.mem_setOf_eq, Metric.mem_ball, dist_zero_right]
        rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm, ENNReal.ofReal_lt_iff_lt_toReal (norm_nonneg _) ht]
        rfl
      have hpos : 0 < t.toReal := ENNReal.toReal_pos ht0 ht
      rw [hb]
      exact measurableSet_expBall (k := k) (r := r) S t.toReal hpos

theorem rhoN : RhoN := by
  intro k r Y
  have hinj : ∀ Y' : Formalism.MainNotions.S.lieE (Nset k r), expL k r (Nset k r) Y' = expL k r (Nset k r) Y → Y' = Y := by
    intro Y' h
    have hY : (Y : EuclideanSpace ℝ _) ∈ (Formalism.MainNotions.BridgeCSB.lieNS k r).map Formalism.MainNotions.BridgeCSB.RL := by
      rw [← Formalism.MainNotions.BridgeCSB.lieE_N]; exact Y.2
    have hY' : (Y' : EuclideanSpace ℝ _) ∈ (Formalism.MainNotions.BridgeCSB.lieNS k r).map Formalism.MainNotions.BridgeCSB.RL := by
      rw [← Formalism.MainNotions.BridgeCSB.lieE_N]; exact Y'.2
    obtain ⟨X, hX, hXY⟩ := hY
    obtain ⟨X', hX', hXY'⟩ := hY'
    have e1 : Formalism.MainNotions.S.unrealify (Y : EuclideanSpace ℝ _) = X := by
      rw [← hXY]; exact Formalism.MainNotions.BridgeCSB.unrealify_RL X
    have e2 : Formalism.MainNotions.S.unrealify (Y' : EuclideanSpace ℝ _) = X' := by
      rw [← hXY']; exact Formalism.MainNotions.BridgeCSB.unrealify_RL X'
    have hexp : NormedSpace.exp X' = NormedSpace.exp X := by
      have h2 : (fun i j => NormedSpace.exp (Formalism.MainNotions.S.unrealify (Y' : EuclideanSpace ℝ _)) i j : Mt k r) =
          fun i j => NormedSpace.exp (Formalism.MainNotions.S.unrealify (Y : EuclideanSpace ℝ _)) i j := h
      rw [e1, e2] at h2
      ext i j
      exact congrFun (congrFun h2 i) j
    have hXX : X' = X := Formalism.MainNotions.BridgeCSB.exp_injOn hX'.1 hX.1 hexp
    apply Subtype.ext
    rw [← hXY, ← hXY', hXX]
  unfold rhoS
  refine le_antisymm (iInf_le_of_le Y (iInf_le_of_le rfl le_rfl)) (le_iInf₂ fun Y' hY' => ?_)
  rw [hinj Y' hY']
  exact le_of_eq rfl

end Formalism.L2.SG.Pf.BH
end
end
