module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePf

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RowsAbsX
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.FourierDecayAlt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
open Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups

namespace Formalism.L2.SG.RowsAbsX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

theorem summable_of_fibre_bound {P T : Type*} (A : P → T → Prop)
    (hA : ∀ p p' t, A p t → A p' t → p = p') (g : T → ℝ) (hg0 : ∀ t, 0 ≤ g t) (hg : Summable g)
    (F : P → ℝ) (hF0 : ∀ p, 0 ≤ F p) (hF : ∀ p, F p ≤ ∑' t : {t // A p t}, g t) : Summable F := by
  refine summable_of_sum_le hF0 (c := ∑' t, g t) (fun S => ?_)
  have hind : ∀ p, ∑' t : {t // A p t}, g t = ∑' t, Set.indicator {t | A p t} g t :=
    fun p => tsum_subtype {t | A p t} g
  calc ∑ p ∈ S, F p ≤ ∑ p ∈ S, ∑' t, Set.indicator {t | A p t} g t :=
        Finset.sum_le_sum fun p _ => (hF p).trans (hind p).le
    _ = ∑' t, ∑ p ∈ S, Set.indicator {t | A p t} g t :=
        (Summable.tsum_finsetSum fun p _ => hg.indicator _).symm
    _ ≤ ∑' t, g t := by
        refine Summable.tsum_le_tsum (fun t => ?_) (summable_sum fun p _ => hg.indicator _) hg
        by_cases h : ∃ p ∈ S, A p t
        · obtain ⟨p, hp, hpt⟩ := h
          rw [Finset.sum_eq_single p]
          · exact (Set.indicator_of_mem (show t ∈ {t | A p t} from hpt) g).le
          · intro q _ hq
            exact Set.indicator_of_notMem (fun hqt => hq (hA q p t hqt hpt)) g
          · intro h
            exact absurd hp h
        · simp only [not_exists, not_and] at h
          exact (Finset.sum_eq_zero fun p hp =>
            Set.indicator_of_notMem (show t ∉ {t | A p t} from h p hp) g).le.trans (hg0 t)

theorem sign_list_injective {K : Type} [Ring K] (r : ℕ) :
    ∀ (b : ℕ) (x y : TB.Pt K), DataInst.signAux r b x = DataInst.signAux r b y → x = y
  | _, [], [], _ => rfl
  | _, [], _ :: _, h => by simp [DataInst.signAux] at h
  | _, _ :: _, [], h => by simp [DataInst.signAux] at h
  | b, (s, t) :: xs, (s', t') :: ys, h => by
    change (s, (-1 : K) ^ (r + 1 - (b + s - 1)) * t) :: DataInst.signAux r (b + s) xs =
      (s', (-1 : K) ^ (r + 1 - (b + s' - 1)) * t') :: DataInst.signAux r (b + s') ys at h
    injection h with hst hr
    injection hst with hs ht
    subst s'
    have hu : IsUnit ((-1 : K) ^ (r + 1 - (b + s - 1))) := isUnit_one.neg.pow _
    rw [hu.mul_left_cancel ht, sign_list_injective r (b + s) xs ys hr]

theorem ptOfList_inj {D : Formalism.BasicNotions.D7} {i : ℕ} {x y : TB.Pt D.host.E} {w : Point D.host.E i}
    (hx : DataInst.ptOfList (D := D) i x = some w) (hy : DataInst.ptOfList (D := D) i y = some w) : x = y := by
  unfold DataInst.ptOfList at hx hy
  by_cases h1 : Formalism.L2.S.IsPtL (DataInst.signPt D.R.rS x) i
  · by_cases h2 : Formalism.L2.S.IsPtL (DataInst.signPt D.R.rS y) i
    · rw [dite_eq_left h1] at hx
      rw [dite_eq_left h2] at hy
      have he := (Option.some.inj hx).trans (Option.some.inj hy).symm
      have hv := congrArg Subtype.val ((Formalism.L2.S.ptEquiv D.host.E i).symm.injective he)
      exact sign_list_injective D.R.rS 1 x y hv
    · rw [dite_eq_right h2] at hy
      exact absurd hy (by simp)
  · rw [dite_eq_right h1] at hx
    exact absurd hx (by simp)

end Gen

section Inputs

variable {D : D7} (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word)

def PtUniq : Prop :=
  ∀ (t : TermDef.Term D u u' (X.Fu u) (Y.what₂ u)) (w w' : Point D.host.E (D.R.rS + 1)), t.atPt w → t.atPt w' → w = w'

def WeightBound (nc : ℝ) : Prop :=
  ∃ C : ℝ, ∀ (p : TB.Pt D.host.E) (w : Point D.host.E (D.R.rS + 1)), DataInst.ptOfList (D.R.rS + 1) p = some w →
    (∃ γ, RealObj.IsPtRep X u u' w γ) → (∃ t : TermDef.Term D u u' (X.Fu u) (Y.what₂ u), t.G ≠ 0 ∧ t.atPt w) →
      Real.sqrt (RealObj.nW X u u' w) ≤
        C * |Real.sqrt (n0 nc (D.mem u).A.T (D.mem u').A.T w) * DataInst.phi (D.R.rS + 1) p|

end Inputs

section Main

variable {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word}

theorem massTerm_le (t : TermDef.Term D u u' (X.Fu u) (Y.what₂ u)) :
    PairVal.massTerm t ≤ ∑ Λ ∈ Y.what₂ u, |PairVal.massRow D (X.Fu u) (Y.what₂ u) Λ| := by
  exact (le_abs_self _).trans
    (Finset.single_le_sum (f := fun Λ => |PairVal.massRow D (X.Fu u) (Y.what₂ u) Λ|)
      (fun _ _ => abs_nonneg _) t.mem)

end Main

end Formalism.L2.SG.RowsAbsX
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RootCoordinateFrames
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped InnerProductSpace ComplexConjugate ENNReal
open Matrix

namespace Formalism.L2.SG.RealObj.RootCoordinateFrames

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def NRealize : Prop :=
  ∀ (n r : ℕ) (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ),
    (∀ a b, hJ ε (e a) (e b) = 0) → (∀ a b, hJ ε (f a) (f b) = 0) →
    (∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0) →
    (∀ a, hJ ε (e a) z = 0 ∧ hJ ε (f a) z = 0) → hJ ε z z ≠ 0 →
    ∀ P : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ, IsLoUni P →
      ∃ s : Formalism.REAL.UJ ε, InN ε e z (uMat s) ∧ ∀ a, uMat s *ᵥ fam e z a = ∑ c, P a c • fam e z c

def RootCoordFrame : Prop :=
  ∀ (n r : ℕ) (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ),
    (∀ a b, hJ ε (f a) (e b) = if a = b then 1 else 0) → (∀ a, hJ ε (f a) z = 0) →
    ∀ (g : Matrix (Fin n) (Fin n) ℂ) (P : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ),
      (∀ a, g *ᵥ fam e z a = ∑ c, P a c • fam e z c) →
      ∀ a : Fin r, rootCoord ε e f z g a = P a.succ a.castSucc

def TraceSum : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (g : ℕ) (x : X.B.I.E),
    ∏ v, Complex.exp (2 * Real.pi * Complex.I * ((X.B.I.φ v x + star (X.B.I.φ v x)) / (g : ℂ))) =
      Formalism.L2.SG.PairVal.psiInf g (X.ιE x)

def ZhatNAct : Prop :=
  ∀ (n r : ℕ) (ε : Fin n → Bool) (f f' : Fin (r + 1) → Fin n → ℂ) (s si s' g : Matrix (Fin n) (Fin n) ℂ)
    (P P' : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ),
    si * s = 1 → (∀ x y, hJ ε (s *ᵥ x) (s *ᵥ y) = hJ ε x y) →
    (∀ a, s *ᵥ f a = ∑ c, P a c • f c) → (∀ b, s' *ᵥ f' b = ∑ c, P' b c • f' c) →
    Zhat ε f f' (si * g * s') = P.map star * Zhat ε f f' g * P'.transpose

def FrameAtV : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (v : InfinitePlace X.B.I.F),
    (∀ a b, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.eR b)) = 0) ∧
    (∀ a b, hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) (rv X.B.I v (X.fR b)) = 0) ∧
    (∀ a b, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.fR b)) = if a = b then 1 else 0) ∧
    (∀ a b, hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) (rv X.B.I v (X.eR b)) = if a = b then 1 else 0) ∧
    (∀ a, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) = 0 ∧
      hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR u)) = 0) ∧
    hJ (X.B.I.ε v) (rv X.B.I v (X.zR u)) (rv X.B.I v (X.zR u)) = -(Tw u : ℂ) ∧ Tw u ≠ 0

end Formalism.L2.SG.RealObj.RootCoordinateFrames
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HermitianBlockSpans
noncomputable section

open scoped ComplexConjugate
open Matrix

namespace Formalism.L2.SG.RealObj.HermitianBlockSpans

open Formalism.L2.SG.HidaSetting

variable {n : ℕ} (ε : Fin n → Bool)

theorem hJ_sub_left (x y w : Fin n → ℂ) : hJ ε (x - y) w = hJ ε x w - hJ ε y w := by
  unfold hJ; rw [star_sub, sub_dotProduct]

theorem hJ_sub_right (x y w : Fin n → ℂ) : hJ ε w (x - y) = hJ ε w x - hJ ε w y := by
  unfold hJ; rw [Matrix.mulVec_sub, dotProduct_sub]

theorem hJ_sum_right {m : ℕ} (c : Fin m → ℂ) (v : Fin m → Fin n → ℂ) (w : Fin n → ℂ) :
    hJ ε w (∑ i, c i • v i) = ∑ i, c i * hJ ε w (v i) := by
  unfold hJ
  rw [Matrix.mulVec_sum, dotProduct_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem hJ_conj (x y : Fin n → ℂ) : hJ ε y x = star (hJ ε x y) := by
  unfold hJ Formalism.REAL.Jm
  simp only [Matrix.mulVec_diagonal, dotProduct, star_sum, star_mul']
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp <;> ring

theorem hJ_map {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) (x y : Fin n → ℂ) :
    hJ ε (g *ᵥ x) (g *ᵥ y) = hJ ε x y := by
  unfold hJ
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  unfold Formalism.REAL.inUJ at hg
  rw [hg]

variable {r : ℕ}

theorem spanLt_eq (e : Fin r → Fin n → ℂ) {a : ℕ} (ha : a ≤ r) :
    spanLt e a = Submodule.span ℂ (Set.range fun c : Fin a => e (Fin.castLE ha c)) := by
  unfold spanLt
  congr 1
  ext v
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨⟨b.1, hb⟩, rfl⟩
  · rintro ⟨c, rfl⟩
    exact ⟨Fin.castLE ha c, c.2, rfl⟩

def blk (e e' : Fin r → Fin n → ℂ) {a : ℕ} (ha : a ≤ r) : Matrix (Fin a) (Fin a) ℂ :=
  Matrix.of fun b c => hJ ε (e (Fin.castLE ha b)) (e' (Fin.castLE ha c))

theorem zero_of_perp_right (e e' : Fin r → Fin n → ℂ) {a : ℕ} (ha : a ≤ r)
    (hD : a = 0 ∨ (blk ε e e' ha).det ≠ 0)
    {x : Fin n → ℂ} (hx : x ∈ spanLt e' a) (hp : ∀ b : Fin a, hJ ε (e (Fin.castLE ha b)) x = 0) : x = 0 := by
  rw [spanLt_eq e' ha, Submodule.mem_span_range_iff_exists_fun] at hx
  obtain ⟨c, rfl⟩ := hx
  rcases hD with h0 | hdet
  · subst h0
    simp
  · have hM : blk ε e e' ha *ᵥ c
        = 0 := by
      funext b
      have := hp b
      rw [hJ_sum_right] at this
      simpa [blk, Matrix.mulVec, dotProduct, mul_comm] using this
    have := Matrix.eq_zero_of_mulVec_eq_zero hdet hM
    simp [this]

theorem zero_of_perp_left (e e' : Fin r → Fin n → ℂ) {a : ℕ} (ha : a ≤ r)
    (hD : a = 0 ∨ (blk ε e e' ha).det ≠ 0)
    {x : Fin n → ℂ} (hx : x ∈ spanLt e a) (hp : ∀ b : Fin a, hJ ε x (e' (Fin.castLE ha b)) = 0) : x = 0 := by
  refine zero_of_perp_right ε e' e ha ?_ hx fun b => by rw [hJ_conj, hp b, star_zero]
  rcases hD with h0 | hdet
  · exact Or.inl h0
  · right
    have e1 : blk ε e' e ha = (blk ε e e' ha)ᴴ := by
      ext b c
      simp only [blk, Matrix.conjTranspose_apply, Matrix.of_apply]
      rw [← hJ_conj]
    rw [e1, Matrix.det_conjTranspose]
    exact fun h => hdet (star_eq_zero.1 h)

theorem st_triv (e e' : Fin r → Fin n → ℂ) (s : Matrix (Fin n) (Fin n) ℂ)
    (hU : ∀ x y, hJ ε (s *ᵥ x) (s *ᵥ y) = hJ ε x y)
    (h1 : ∀ a : Fin r, (s - 1) *ᵥ e a ∈ spanLt e a.1) (h1' : ∀ a : Fin r, (s - 1) *ᵥ e' a ∈ spanLt e' a.1)
    (h2 : ∀ y, (∀ a, hJ ε (e a) y = 0) → (s - 1) *ᵥ y ∈ spanLt e r)
    (hD : ∀ l (hl : l ≤ r), 1 ≤ l →
      (blk ε e e' hl).det ≠ 0) :
    s = 1 := by
  have hD' : ∀ l (hl : l ≤ r),
      l = 0 ∨ (blk ε e e' hl).det ≠ 0 :=
    fun l hl => by
      rcases Nat.eq_zero_or_pos l with h | h
      · exact Or.inl h
      · exact Or.inr (hD l hl h)
  have hsub : ∀ v : Fin n → ℂ, (s - 1) *ᵥ v = s *ᵥ v - v := fun v => by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]

  have step : ∀ a : ℕ, a ≤ r → ∀ c : Fin r, c.1 < a → s *ᵥ e c = e c ∧ s *ᵥ e' c = e' c := by
    intro a
    induction a with
    | zero => intro _ c hc; exact absurd hc (Nat.not_lt_zero _)
    | succ a ih =>
      intro ha c hc
      have ha' : a ≤ r := Nat.le_of_succ_le ha
      have IH := ih ha'
      rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hlt | heq
      · exact IH c hlt
      · have hca : c.1 = a := heq
        constructor
        · have hx := h1 c
          rw [hca] at hx
          have := zero_of_perp_left ε e e' ha' (hD' a ha') hx fun b => by
            have hb := (IH (Fin.castLE ha' b) b.2).2
            rw [hsub, hJ_sub_left, ← hb, hU, hb, sub_self]
          rw [hsub, sub_eq_zero] at this
          exact this
        · have hx := h1' c
          rw [hca] at hx
          have := zero_of_perp_right ε e e' ha' (hD' a ha') hx fun b => by
            have hb := (IH (Fin.castLE ha' b) b.2).1
            rw [hsub, hJ_sub_right, ← hb, hU, hb, sub_self]
          rw [hsub, sub_eq_zero] at this
          exact this
  have hfix : ∀ c : Fin r, s *ᵥ e c = e c ∧ s *ᵥ e' c = e' c := fun c => step r le_rfl c c.2

  ext i j
  suffices hall : ∀ y : Fin n → ℂ, s *ᵥ y = y by
    have := congrFun (hall (Pi.single j 1)) i
    simpa [Matrix.mulVec_single, Matrix.one_apply, Pi.single_apply] using this
  intro y
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    have hy := h2 y (fun a => a.elim0)
    have h0 : spanLt e 0 = ⊥ := by
      unfold spanLt
      simp
    rw [h0, Submodule.mem_bot, hsub, sub_eq_zero] at hy
    exact hy
  · let M : Matrix (Fin r) (Fin r) ℂ := fun b c => hJ ε (e b) (e' c)
    have hMdet : M.det ≠ 0 := hD r le_rfl hr
    let lam : Fin r → ℂ := M⁻¹ *ᵥ fun b => hJ ε (e b) y
    let x' : Fin n → ℂ := ∑ c, lam c • e' c
    have hMl : M *ᵥ lam = fun b => hJ ε (e b) y := by
      simp only [lam, Matrix.mulVec_mulVec]
      rw [Matrix.mul_nonsing_inv _ (Ne.isUnit hMdet), Matrix.one_mulVec]
    have hperp : ∀ b, hJ ε (e b) (y - x') = 0 := by
      intro b
      rw [hJ_sub_right, hJ_sum_right]
      have := congrFun hMl b
      simp only [Matrix.mulVec, dotProduct, M] at this
      rw [← this]
      simp only [mul_comm, sub_self]
    have hx'fix : s *ᵥ x' = x' := by
      simp only [x', Matrix.mulVec_sum, Matrix.mulVec_smul, (hfix _).2]
    have hw : (s - 1) *ᵥ y ∈ spanLt e r := by
      have := h2 (y - x') hperp
      rwa [Matrix.mulVec_sub, hsub x', hx'fix, sub_self, sub_zero] at this
    have hw0 := zero_of_perp_left ε e e' le_rfl (hD' r le_rfl) hw fun b => by
      have hb := (hfix (Fin.castLE le_rfl b)).2
      rw [hsub, hJ_sub_left, ← hb, hU, hb, sub_self]
    rw [hsub, sub_eq_zero] at hw0
    exact hw0

end Formalism.L2.SG.RealObj.HermitianBlockSpans
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfM
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ScalarFramePf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section GenericX

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V)

theorem identResp_generic {r : ℕ} (abelian₂ : Submodule M.L.O V) (f₀ f₁ f₂ : Fin (r + 1) → V) (T T' : F)
    (e : V ≃ₗ[E] V) (hiso : ∀ v w, H.h (e v) (e w) = H.h v w)
    (h12 : ∀ x ∈ H.X f₁, e x ∈ H.X f₂) (h21 : ∀ y ∈ H.X f₂, e.symm y ∈ H.X f₁)
    (hX0 : ∀ a ∈ H.X f₀, ∀ b ∈ H.X f₀, H.h a b = 0) (hX2 : ∀ a ∈ H.X f₂, ∀ b ∈ H.X f₂, H.h a b = 0)
    (hL : ∀ x ∈ abelian₂, e x ∈ abelian₂) (hL' : ∀ x ∈ abelian₂, e.symm x ∈ abelian₂)
    (hW0 : ∀ w ∈ H.W0 f₀ f₁, ∃ w₂ ∈ H.W0 f₀ f₂, w - w₂ ∈ H.X f₀ ∧ e w - w₂ ∈ H.X f₂)
    (homp : H.Dl f₀ f₂ (r + 1) • H.om' f₀ f₁ - H.Dl f₀ f₁ (r + 1) • H.om' f₀ f₂ ∈ H.X f₀)
    (hom : M.L.cj (H.Dl f₀ f₂ (r + 1)) • e (H.om f₀ f₁) - M.L.cj (H.Dl f₀ f₁ (r + 1)) • H.om f₀ f₂ ∈ H.X f₂)
    (hrat : H.Dl f₀ f₁ r * H.Dl f₀ f₂ (r + 1) = H.Dl f₀ f₂ r * H.Dl f₀ f₁ (r + 1))
    (hz : e (f₁ (Fin.last r)) - f₂ (Fin.last r) ∈ H.X f₂)
    (hI : ∀ g, M.split = some g → IotaG H (algebraMap F E (g.q : F)) abelian₂ f₀ f₁ f₂ e) :
    H.Ident (⟨abelian₂, f₀, f₁, T, T'⟩ : Loc.Term V M r) ⟨abelian₂, f₀, f₂, T, T'⟩ (LinearEquiv.refl _ _)
        (qEquiv H e hiso (H.X f₁) (H.X f₂) h12 h21) ∧
      H.Respects (⟨abelian₂, f₀, f₁, T, T'⟩ : Loc.Term V M r) ⟨abelian₂, f₀, f₂, T, T'⟩ (LinearEquiv.refl _ _)
        (qEquiv H e hiso (H.X f₁) (H.X f₂) h12 h21) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, hrat⟩, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro x y x₂ y₂ hx hy
    exact h_eq_of_sub_mem H _ hX0 x.2 y.2 ((mk_eq_iff H _ x x₂).1 hx) ((mk_eq_iff H _ y y₂).1 hy)
  · intro x y x₂ y₂ hx hy
    have hx' : e x - x₂ ∈ H.X f₂ := (mk_eq_iff H _ _ x₂).1 hx
    have hy' : e y - y₂ ∈ H.X f₂ := (mk_eq_iff H _ _ y₂).1 hy
    rw [h_eq_of_sub_mem H _ hX2 (perp_map H e hiso _ _ h21 x.2) (perp_map H e hiso _ _ h21 y.2) hx' hy',
      hiso]
  · intro w hw
    obtain ⟨w₂, hw₂, h1, h2⟩ := hW0 w hw
    refine ⟨w₂, hw₂, ?_, ?_⟩
    · intro x x₂ hx hx₂
      apply smul_mk_eq H
      rw [one_smul, one_smul, hx, hx₂]
      exact h1
    · intro x x₂ hx hx₂
      apply smul_mk_eq H
      show (1 : E) • e x - (1 : E) • (x₂ : V) ∈ H.X f₂
      rw [one_smul, one_smul, hx, hx₂]
      exact h2
  · intro x x₂ hx hx₂
    apply smul_mk_eq H
    rw [hx, hx₂]
    exact homp
  · intro x x₂ hx hx₂
    apply smul_mk_eq H
    show M.L.cj (H.Dl f₀ f₂ (r + 1)) • e x - M.L.cj (H.Dl f₀ f₁ (r + 1)) • (x₂ : V) ∈ H.X f₂
    rw [hx, hx₂]
    exact hom
  · ext w
    simp
  · intro x x₂ hx hx₂
    have : x = x₂ := Subtype.ext (hx.trans hx₂.symm)
    rw [this]
    rfl
  · ext w
    constructor
    · rintro ⟨_, ⟨x, hxΛ, rfl⟩, rfl⟩
      exact ⟨perpEquiv H e hiso _ _ h12 h21 x, hL _ hxΛ, rfl⟩
    · rintro ⟨x₂, hx₂Λ, rfl⟩
      refine ⟨H.mkW _ ⟨e.symm x₂, perp_map_symm H e hiso _ _ h12 x₂.2⟩,
        ⟨⟨e.symm x₂, perp_map_symm H e hiso _ _ h12 x₂.2⟩, hL' _ hx₂Λ, rfl⟩, ?_⟩
      show qEquiv H e hiso (H.X f₁) (H.X f₂) h12 h21 (Submodule.Quotient.mk _) = Submodule.Quotient.mk x₂
      rw [qEquiv_mk]
      congr 1
      exact Subtype.ext (e.apply_symm_apply x₂)
  · intro x x₂ hx hx₂
    apply smul_mk_eq H
    show (1 : E) • e x - (1 : E) • (x₂ : V) ∈ H.X f₂
    rw [one_smul, one_smul, hx, hx₂]
    exact hz
  · intro g hg
    obtain ⟨hA, hB⟩ := hI g hg
    ext ⟨a, b⟩
    constructor
    · rintro ⟨⟨a0, b0⟩, ⟨x', x, hx'Λ, hxΛ, hq, heq⟩, hmap⟩
      obtain ⟨y, y'', hyΛ, hy''Λ, hyp, hy''p, hxy, hxy'', hyq⟩ := hA x x' hxΛ hx'Λ x.2 x'.2 hq
      refine ⟨⟨y'', hy''p⟩, ⟨y, hyp⟩, hy''Λ, hyΛ, hyq, ?_⟩
      simp only [Prod.map, Prod.mk.injEq] at hmap heq
      obtain ⟨rfl, rfl⟩ := heq
      obtain ⟨rfl, rfl⟩ := hmap
      refine Prod.ext ?_ ?_
      · show qEquiv H e hiso (H.X f₁) (H.X f₂) h12 h21 (Submodule.Quotient.mk x') = Submodule.Quotient.mk _
        rw [qEquiv_mk, mk_eq_iff]
        exact hxy''
      · show Submodule.Quotient.mk x = Submodule.Quotient.mk _
        rw [mk_eq_iff]
        exact hxy
    · rintro ⟨x'', x, hx''Λ, hxΛ, hq, heq⟩
      obtain ⟨y, y', hyΛ, hy'Λ, hyp, hy'p, hxy, hxy', hyq⟩ := hB x x'' hxΛ hx''Λ x.2 x''.2 hq
      refine ⟨(H.mkW _ ⟨y', hy'p⟩, H.mkW _ ⟨y, hyp⟩), ⟨⟨y', hy'p⟩, ⟨y, hyp⟩, hy'Λ, hyΛ, hyq, rfl⟩, ?_⟩
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      refine Prod.ext ?_ ?_
      · show qEquiv H e hiso (H.X f₁) (H.X f₂) h12 h21 (Submodule.Quotient.mk _) = Submodule.Quotient.mk x''
        rw [qEquiv_mk, mk_eq_iff]
        have h := h12 _ hxy'
        rw [map_sub, LinearEquiv.apply_symm_apply] at h
        have h' := Submodule.neg_mem _ h
        rwa [neg_sub] at h'
      · show Submodule.Quotient.mk _ = Submodule.Quotient.mk x
        rw [mk_eq_iff]
        have h' := Submodule.neg_mem _ hxy
        rwa [neg_sub] at h'

end GenericX

section ConcreteX

variable {D : D7} (Z : LocDat D) (p : PlF D)

def phiP (Λ : Submodule (𝓞 D.host.E) (VS D).V) (f g1 g2 : Fin (D.R.rS + 1) → (VS D).V)
    (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hG : GFacts Λ f g1 g2 β) :
    (locH Z p).Wb (fun b => sF' Z p b • baseChange₂ D p (g1 b)) ≃ₗ[(D.s.atP p).Ep]
      (locH Z p).Wb (fun b => sF' Z p b • baseChange₂ D p (g2 b)) :=
  qEquiv (locH Z p) (betaP p β) (betaP_iso Z p β hG.iso) _ _
    (fun x hx => betaP_mem_X Z p β g1 g2 (sF' Z p) (isUnit_sF' Z p) hG.xmap hx)
    (fun y hy => betaP_symm_mem_X Z p β g1 g2 (sF' Z p) (isUnit_sF' Z p) hG.xmap' hy)

theorem identResp_lt (Λ : Submodule (𝓞 D.host.E) (VS D).V) (f g1 g2 : Fin (D.R.rS + 1) → (VS D).V)
    (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (Tn T'n : ℕ) (hG : GFacts Λ f g1 g2 β)
    (hI : IotaEl Z p Λ f g1 g2 β) :
    (locH Z p).Ident (lt Z p Λ f g1 Tn T'n) (lt Z p Λ f g2 Tn T'n) (LinearEquiv.refl _ _) (phiP Z p Λ f g1 g2 β hG) ∧
      (locH Z p).Respects (lt Z p Λ f g1 Tn T'n) (lt Z p Λ f g2 Tn T'n) (LinearEquiv.refl _ _)
        (phiP Z p Λ f g1 g2 β hG) := by
  have hiso : ∀ v w, (locH Z p).h (betaP p β v) (betaP p β w) = (locH Z p).h v w := betaP_iso Z p β hG.iso
  refine identResp_generic (locH Z p) (lattice₂ D Z.M p Λ) (fun a => sF Z p a • baseChange₂ D p (f a))
    (fun b => sF' Z p b • baseChange₂ D p (g1 b)) (fun b => sF' Z p b • baseChange₂ D p (g2 b)) _ _ (betaP p β) hiso
    (fun x hx => betaP_mem_X Z p β g1 g2 (sF' Z p) (isUnit_sF' Z p) hG.xmap hx)
    (fun y hy => betaP_symm_mem_X Z p β g1 g2 (sF' Z p) (isUnit_sF' Z p) hG.xmap' hy) ?_ ?_
    (fun x hx => betaP_lat Z p β Λ hG.lam hx) (fun x hx => betaP_symm_lat Z p β Λ hG.lam' hx)
    (fun w hw => scalar_frame_w_zero_exists Z p Λ f g1 g2 β hG hw) ?_ ?_ ?_ ?_ hI
  · apply iso_span
    intro i j
    rw [h_bcP, brS, hG.fiso j i, map_zero, mul_zero]
  · apply iso_span
    intro i j
    rw [h_bcP, brS, hG.g2iso j i, map_zero, mul_zero]
  ·
    rw [om'_loc, om'_loc, dl_loc Z p f g2 (sF Z p) (sF' Z p) _ le_rfl,
      dl_loc Z p f g1 (sF Z p) (sF' Z p) _ le_rfl]
    rw [omp_combine]
    exact Submodule.smul_mem _ _ (bcP_mem_X Z p f (sF Z p) (isUnit_sF Z p) hG.omp)
  ·
    rw [om_loc, om_loc, dl_loc Z p f g2 (sF Z p) (sF' Z p) _ le_rfl,
      dl_loc Z p f g1 (sF Z p) (sF' Z p) _ le_rfl, map_smul, betaP_bc]
    rw [om_combine]
    exact Submodule.smul_mem _ _ (bcP_mem_X Z p g2 (sF' Z p) (isUnit_sF' Z p) hG.om)
  ·
    rw [dl_loc Z p f g1 (sF Z p) (sF' Z p) _ (Nat.le_succ _), dl_loc Z p f g2 (sF Z p) (sF' Z p) _ le_rfl,
      dl_loc Z p f g2 (sF Z p) (sF' Z p) _ (Nat.le_succ _), dl_loc Z p f g1 (sF Z p) (sF' Z p) _ le_rfl]
    have h := congrArg (D.s.atP p).ιE hG.ratio
    rw [map_mul, map_mul] at h
    linear_combination ((∏ i : Fin D.R.rS, (Z.M p).L.cj (sF Z p (Fin.castLE (Nat.le_succ _) i))) *
      (∏ i : Fin D.R.rS, sF' Z p (Fin.castLE (Nat.le_succ _) i)) *
      ((∏ i : Fin (D.R.rS + 1), (Z.M p).L.cj (sF Z p (Fin.castLE le_rfl i))) *
      (∏ i : Fin (D.R.rS + 1), sF' Z p (Fin.castLE le_rfl i)))) * h
  ·
    show betaP p β (sF' Z p (Fin.last _) • baseChange₂ D p (g1 (Fin.last _))) -
      sF' Z p (Fin.last _) • baseChange₂ D p (g2 (Fin.last _)) ∈ _
    rw [map_smul, betaP_bc, ← smul_sub, ← map_sub]
    exact Submodule.smul_mem _ _ (bcP_mem_X Z p g2 (sF' Z p) (isUnit_sF' Z p) hG.zmap)

end ConcreteX

end Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc
  Formalism.L2.SG.Pf.ScalarFramePf

end Formalism.L2.SG.Pf
end
end
