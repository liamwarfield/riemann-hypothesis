module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatTensorPureTensorEqProdLocalFactors
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameLatticePointsEqIntegralMatricesLargeDepth
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatDictionaryScalarLargeDepth
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArrowLocalModelMovedFrames
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeVacuumCombinationLocalModel
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatDictionaryLastTwoStepsAtPlace

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiFrameOfGridLatticeLargeDepth
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiFrameOfGridLatticeLargeDepth
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

namespace GlobalTheory.FlatPlace

namespace NormalJac

theorem jacobiDualColumn_scalar_identity {K : Type} [Field K] (X : K) (hX : X ≠ 0) (i k : ℕ) :
    (X ^ (i + 1 + k))⁻¹ * (-((-X) ^ (i + 1 + k) * X ^ (i + 1 + k)) / X) * (-1 / X) ^ k = (-X) ^ i := by
  have h1 : ((-1 : K) ^ k) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  rw [neg_pow X, neg_pow X, div_pow]
  field_simp
  linear_combination (X * X ^ i * X ^ k * (-1) ^ i) * h1

theorem mul_col_eq {ι' ι κ μ K : Type} [Fintype ι] [Field K] (P : Matrix ι' ι K) (Y : Matrix ι κ K) (Z : Matrix ι μ K)
    (c : κ) (c' : μ) (h : ∀ l, Y l c = Z l c') (r : ι') : (P * Y) r c = (P * Z) r c' := by
  simp only [Matrix.mul_apply, h]

theorem hz_besAt {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {t : T} {M : Vol G} (hM : M.Is t)
    (j σ : ℕ) (hj : j + 2 * σ + 2 = D.R.m) (vN : GlobalTheory.Unf.VolN (besDecAt G j σ hj)) {k : Type} [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) :
    p.hz (besAt G hM j σ hj vN) = -((-p.xi) ^ σ * p.xi ^ σ) := by
  simp only [Place.hz, besAt, dotProduct, mulVec]
  show p.pr (∑ i : Fin 1, star (fun _ : Fin 1 => D.host.xi0 ^ σ) i * ∑ i_1 : Fin 1, (GlobalTheory.SeeSaw.Model.nLine D).gram i i_1 * D.host.xi0 ^ σ) = _
  simp only [Fin.sum_univ_one, nLine_gram, Pi.star_apply, star_pow, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, Place.xi, Place.pr, map_mul, map_neg, map_pow, map_one]
  ring

theorem pr_mul' {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)
    (x y : D.host.E) : p.pr (x * y) = p.pr x * p.pr y := map_mul (p.π.comp (incA D)) x y

theorem place_proj_neg_xi_pow {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) (n : ℕ) : p.pr ((-D.host.xi0) ^ n) = (-p.xi) ^ n :=
  (map_pow (p.π.comp (incA D)) _ n).trans (congrArg (· ^ n) (map_neg (p.π.comp (incA D)) _))

theorem neg_mul_neg_one_eq_of_eq {K : Type} [Field K] (y a S : K) (h : S = a) : -(y * a) * -1 = S * y := by rw [h]; ring

end NormalJac


open NormalJac in
set_option maxHeartbeats 1600000 in
theorem big_jacP : Big fun ch => JacP ch := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ hε hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch hsc => ?_⟩⟩
  clear hε hx hsc hch s
  intro t w hw p hp M hM j σ hj vN a ha c hc
  have h1 := ch.S.row t trivial w hw (j + 1) (by omega)
  have hm : (locGrid ch.G t w).m = D.R.m := rfl
  obtain rfl : c = 2 * σ := by
    have h2 := topRank_add (G := locGrid ch.G t w) one_le_sLen (j + 1)
    rw [hm] at h2; omega
  have hpr : ∀ x, p.pr x = algebraMap D.host.E (Kw w) x := fun x =>
    (hp.2.1 _).trans (Comparison₂.cpt_tmul w x)
  have hxi : p.xi ≠ 0 := by
    rw [Place.xi, hpr]; exact (map_ne_zero _).2 (GlobalTheory.Unf.Inhab.cmHost_imaginaryGenerator_ne_zero D)
  have hE : (epsV ch.G t w (D.R.m, j + 1)).val =
      diagonal fun q => if topRank (locGrid ch.G t w) (j + 1) + σ ≤ q.val then -1 else 1 := by
    by_cases hσ : σ = 0
    · subst hσ
      rw [epsV_eq_one _ _ (by omega), Units.val_one]
      ext q q'
      rw [Matrix.one_apply, diagonal_apply, if_neg (show ¬ (topRank (locGrid ch.G t w) (j + 1) + 0 ≤ q.val) by have := q.2; omega)]
    · have hodd : Odd (j + 1) := by
        obtain ⟨b, hb⟩ := D.R.m_even
        exact ⟨j / 2, by omega⟩
      rw [epsV_apply, if_pos (mem_idx.2 ⟨by omega, by omega⟩), sgnAt, GlobalTheory.SplitFlip.diagGL_val]
      congr 1
      funext q
      have e : (D.R.m - 1 - (j + 1)) / 2 = σ := by omega
      simp only [e, hodd, true_and]
      split_ifs <;> simp
  have h₁ : j + 1 < D.R.m := by omega
  have h₂ : D.R.m - 1 - (j + 1) = 2 * σ := by omega
  obtain ⟨T0, T1, T2⟩ : (mt _ a).map p.π * (rowJac ch.G (j + 1) h₁ σ h₂).i₀.map p.pr = (rowJac ch.G (j + 1) h₁ σ h₂).i₀.map p.pr ∧
      (mt _ a).map p.π * (rowJac ch.G (j + 1) h₁ σ h₂).e.map p.pr =
        ((rowJac ch.G (j + 1) h₁ σ h₂).e * diagonal fun a : Fin σ => (D.host.xi0 ^ a.1)⁻¹).map p.pr ∧
      (mt _ a).map p.π * (rowJac ch.G (j + 1) h₁ σ h₂).e'.map p.pr =
        ((rowJac ch.G (j + 1) h₁ σ h₂).e' * diagonal fun a : Fin σ => star (D.host.xi0 ^ a.1)).map p.pr := by
    rcases ha with ⟨rfl, rfl⟩ | ⟨δ, hδ, hδa⟩
    · refine ⟨?_, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
      rw [show mt (ch.G.V (Node.grid D.R.m (j + 1))) 1 = 1 by simp [Formalism.L2.Theta.mt], Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
    · obtain ⟨e0, e1, e2⟩ := hδ.2.2 σ h₁ h₂
      have key : ∀ {n : ℕ} (X Y : Matrix (Fin (ch.G.V (Node.grid D.R.m (j + 1))).rank) (Fin n) D.host.E),
          HMul.hMul (mt _ δ) (X.map (incA D)) = Y.map (incA D) → (mt _ a).map p.π * X.map p.pr = Y.map p.pr := by
        intro n X Y h
        have := congrArg (fun Z => Z.map p.π) h
        simp only [Matrix.map_mul, Matrix.map_map] at this
        rw [hδa]
        exact this
      exact ⟨key _ _ e0, key _ _ e1, key _ _ e2⟩
  have hfl : ∀ {a c b : ℕ} (h : a + c = b) (x : Fin a), ((frame h (Sum.inl x)) : ℕ) = x := by intros; simp [frame]
  have hfr : ∀ {a c b : ℕ} (h : a + c = b) (q : Fin c), ((frame h (Sum.inr q)) : ℕ) = a + q := by intros; simp [frame]
  clear ha
  have T0' : ∀ {n : Type} [Fintype n] (Z : Matrix (Fin (ch.G.V (Node.top (j + 1))).rank) n (Kw w)), (mt _ a).map p.π * ((rowJac ch.G (j + 1) h₁ σ h₂).i₀.map p.pr * Z) =
      (rowJac ch.G (j + 1) h₁ σ h₂).i₀.map p.pr * Z := by
    intro n _ Z; rw [← Matrix.mul_assoc, T0]
  dsimp only [Place.IsJacFrame, jacAt]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro r x
    simp only [mvFr, frRow, frOf, frTop, submatrix_apply, id, hE, mul_diagonal]
    rw [if_neg (by rw [hfl]; omega), mul_one]
    refine (mul_col_eq _ _ ((rowJac ch.G (j + 1) h₁ σ h₂).i₀.map p.pr *
      (loc w (ch.S.βp (j + 1))).val.submatrix id (Fin.cast (topRank_eq ch.G t w h₁.le))) _ x (fun l => ?_) r).trans
      (congrFun (congrFun (T0' _) r) x)
    have e1 := congrFun (congrFun h1 l) (Sum.inl (Fin.cast (topRank_eq ch.G t w h₁.le) x))
    simp only [submatrix_apply, id, fromCols_apply_inl, Matrix.mul_apply, Matrix.map_apply] at e1
    simp only [submatrix_apply, id, Matrix.mul_apply, Matrix.map_apply, hpr]
    refine (congrArg _ (Fin.ext ?_)).trans e1
    simp [frame]
  · intro i jj hij r
    simp only [mvFr, frRow, frOf, submatrix_apply, id, hE, mul_diagonal]
    rw [if_neg (by rw [hfr]; omega), mul_one]
    refine (mul_col_eq _ _ ((rowJac ch.G (j + 1) h₁ σ h₂).e.map p.pr) _ i (fun l => ?_) r).trans ?_
    rotate_left
    · rw [T1]
      have hinv : ∀ x : D.host.E, p.π (incA D x⁻¹) = (p.π (incA D x))⁻¹ := fun x => map_inv₀ (p.π.comp (incA D)) x
      simp only [Matrix.map_apply, mul_diagonal, Place.pr, Place.xi, map_mul, hinv, map_pow]
      have hx : p.π (incA D D.host.xi0) ≠ 0 := hxi
      have e : p.π (incA D D.host.xi0) ^ σ = p.π (incA D D.host.xi0) ^ (σ - i.val) * p.π (incA D D.host.xi0) ^ i.val := by
        rw [← pow_add]; congr 1; omega
      rw [e]
      field_simp
    · have e1 := congrFun (congrFun h1 l) (Sum.inr (Fin.cast h₂.symm jj))
      simp only [submatrix_apply, id, fromCols_apply_inr, mul_diagonal, Matrix.map_apply] at e1
      rw [if_neg (Nat.succ_ne_zero j), pow_zero, mul_one, frameSign, if_neg (by simp only [Fin.val_cast]; omega), mul_one] at e1
      simp only [submatrix_apply, id, Matrix.map_apply, hpr]
      refine (congrArg _ (Fin.ext ?_)).trans (e1.trans ?_)
      · simp [frame, topRank_eq ch.G t w h₁.le]
      · have he : (rowJac ch.G (j + 1) h₁ σ h₂).e l i = (ch.G.rowDec (j + 1) h₁).a l (Fin.castLE (by omega) i) := rfl
        rw [he]
        exact congrArg _ (congrArg _ (Fin.ext (by simp; omega)))
  · intro i jj hij r
    simp only [mvFr, frRow, frOf, submatrix_apply, id, hE, mul_diagonal]
    rw [if_pos (by rw [hfr]; omega)]
    refine (congrArg (· * (-1)) (mul_col_eq _ _ (-((rowJac ch.G (j + 1) h₁ σ h₂).e'.map p.pr)) _ i (fun l => ?_) r)).trans ?_
    rotate_left
    · rw [Matrix.mul_neg, Matrix.neg_apply, T2, hz_besAt]
      simp only [Matrix.neg_apply, Matrix.map_apply, mul_diagonal, pr_mul', star_pow, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, place_proj_neg_xi_pow]
      have key := jacobiDualColumn_scalar_identity p.xi hxi i (σ - 1 - i)
      rw [show (i : ℕ) + 1 + (σ - 1 - i) = σ by omega] at key
      exact neg_mul_neg_one_eq_of_eq _ _ _ key
    · have e1 := congrFun (congrFun h1 l) (Sum.inr (Fin.cast h₂.symm jj))
      simp only [submatrix_apply, id, fromCols_apply_inr, mul_diagonal, Matrix.map_apply] at e1
      rw [if_neg (Nat.succ_ne_zero j), pow_zero, mul_one, frameSign, if_pos (by simp only [Fin.val_cast]; omega), mul_neg_one] at e1
      simp only [submatrix_apply, id, Matrix.neg_apply, Matrix.map_apply, hpr]
      refine (congrArg _ (Fin.ext ?_)).trans (e1.trans ?_)
      · simp [frame, topRank_eq ch.G t w h₁.le]
      · simp only [rowJac, jacDec, submatrix_apply, id]
        exact congrArg _ (congrArg _ (congrArg _ (Fin.ext (by simp; omega))))

end GlobalTheory.FlatPlace
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiFrameOfGridLatticeLargeDepthStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacobiFrameOfGridLattice_largeDepth : Big fun ch => JacP ch := by
  first | exact @GlobalTheory.FlatPlace.big_jacP | exact GlobalTheory.FlatPlace.big_jacP | (intros; apply GlobalTheory.FlatPlace.big_jacP <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselFrameOfGridLatticeLargeDepth
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselFrameOfGridLatticeLargeDepth
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

noncomputable section

namespace GlobalTheory.FlatPlace

open GlobalTheory.LocMod (Place Frame)

section Entries

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem epsV_even (t : T) (w : Pl D.host.E) {j : ℕ} (hj : Even j) : epsV G t w (D.R.m, j) = 1 := by
  rw [epsV_apply]
  split_ifs
  · refine Units.ext ?_
    rw [sgnAt, GlobalTheory.SplitFlip.diagGL_val, Units.val_one, ← diagonal_one]
    congr 1
    funext x
    rw [if_neg (fun h => (Nat.not_odd_iff_even.2 hj) h.1)]
    rfl
  · rfl

theorem baseM_val (t : T) (w : Pl D.host.E) (j : ℕ) : (baseM G t w j).val = diagonal fun x =>
    if j = 0 then (((unifAt w : Kw w)) ^ (cosExp G w * (x.val + 1 - topRank (locGrid G t w) j)))⁻¹ else 1 := by
  unfold baseM
  split_ifs with h
  · subst h
    have e : (stair (locGrid G t w) (unifAt w) (cosExp G w) 0)⁻¹ =
        GlobalTheory.SplitFlip.diagGL fun x : Fin ((locGrid G t w).rank ((locGrid G t w).m, 0)) =>
          (unifAt w ^ (cosExp G w * (x.val + 1 - topRank (locGrid G t w) 0)))⁻¹ := by
      refine inv_eq_of_mul_eq_one_right (Units.ext ?_)
      rw [Units.val_mul, stair, GlobalTheory.SplitFlip.diagGL_val, GlobalTheory.SplitFlip.diagGL_val, diagonal_mul_diagonal, Units.val_one,
        ← diagonal_one]
      ext i
      simp
    have e2 := congrArg Units.val e
    rw [GlobalTheory.SplitFlip.diagGL_val] at e2
    refine e2.trans ?_
    congr 1
    ext i
    simp
  · rw [Units.val_one, ← diagonal_one]

theorem mvFr_entries (S : GridChoice W U) {t : T} (ht : t ∈ U) {w : Pl D.host.E} (hw : w ∈ locPl G t) (p : Place D (Kw w))
    {j : ℕ} (hj : j < D.R.m) (hje : Even j) (a : GA D (G.V (.grid D.R.m j)))
    (ha : (mt _ a).map p.π * (frRow S.B t w j hj.le).β = (frRow S.B t w j hj.le).β * (baseM G t w j).val) {c : ℕ}
    (hc : topRank (locGrid G t w) j + c = (locGrid G t w).rank (D.R.m, j)) (r : Fin (G.V (.grid D.R.m j)).rank) :
    (∀ q, (mvFr p a (frRow S.B t w j hj.le) (epsV G t w (D.R.m, j)) (frame hc)).β r (Sum.inl q) =
      ((frameMat _ _ (G.rowDec j hj).ι).map (algebraMap D.host.E (Kw w)) * (loc w (S.βp j)).val) r
        (Fin.cast (topRank_eq G t w hj.le) q)) ∧
    ∀ (q : Fin c) (q' : Fin (D.R.m - 1 - j)), q'.val = q.val →
      (mvFr p a (frRow S.B t w j hj.le) (epsV G t w (D.R.m, j)) (frame hc)).β r (Sum.inr q) =
        algebraMap D.host.E (Kw w) ((G.rowDec j hj).a r q') * frameSign (Kw w) (D.R.m - 1 - j) q' := by
  have hrow := S.row t ht w hw j hj
  unfold IsSumFrame at hrow
  have hT := topRank_eq G t w hj.le
  have key : ∀ z, (mvFr p a (frRow S.B t w j hj.le) (epsV G t w (D.R.m, j)) (frame hc)).β r z =
      (loc w (S.B.β D.R.m j)).val r (Fin.cast (rank_vertex G t w (X := (D.R.m, j)) ⟨le_rfl, hj.le⟩) (frame hc z)) *
        (if j = 0 then (((unifAt w : Kw w)) ^ (cosExp G w * ((frame hc z).val + 1 - topRank (locGrid G t w) j)))⁻¹ else 1) := by
    intro z
    show ((mt _ a).map p.π * (frRow S.B t w j hj.le).β * (epsV G t w (D.R.m, j)).val) r (frame hc z) = _
    rw [epsV_even t w hje, Units.val_one, Matrix.mul_one, ha, baseM_val, mul_diagonal]
    rfl
  refine ⟨fun q => ?_, fun q q' hq => ?_⟩
  · rw [key]
    have e1 : Fin.cast (rank_vertex G t w (X := (D.R.m, j)) ⟨le_rfl, hj.le⟩) (frame hc (Sum.inl q)) =
        frame (G.rowDec j hj).rank (Sum.inl (Fin.cast hT q)) := by
      ext; simp [frame]
    have e2 := congrFun (congrFun hrow r) (Sum.inl (Fin.cast hT q))
    rw [submatrix_apply, id, fromCols_apply_inl] at e2
    rw [e1, e2]
    have e3 : (frame hc (Sum.inl q)).val + 1 - topRank (locGrid G t w) j = 0 := by
      have := q.2; simp [frame]
    rw [e3]
    simp
  · rw [key]
    have e1 : Fin.cast (rank_vertex G t w (X := (D.R.m, j)) ⟨le_rfl, hj.le⟩) (frame hc (Sum.inr q)) =
        frame (G.rowDec j hj).rank (Sum.inr q') := by
      ext; simp [frame, hq, hT]
    have e2 := congrFun (congrFun hrow r) (Sum.inr q')
    rw [submatrix_apply, id, fromCols_apply_inr, mul_diagonal, Matrix.map_apply] at e2
    rw [e1, e2]
    have e3 : (frame hc (Sum.inr q)).val + 1 - topRank (locGrid G t w) j = q'.val + 1 := by
      simp [frame, hq]; omega
    rw [e3]
    have hu : ((unifAt w : Kw w)) ≠ 0 := Units.ne_zero _
    split_ifs
    · field_simp
    · simp

end Entries

section Main

section Alg

variable {k : Type} [Field k]

theorem alg_e (x y : k) (hx : x ≠ 0) (σ i : ℕ) (h : i ≤ σ) : y * 1 = (x ^ σ)⁻¹ * x ^ (σ - i) * (y * x ^ i) := by
  obtain ⟨e, rfl⟩ : ∃ e, σ = i + e := ⟨σ - i, by omega⟩
  rw [Nat.add_sub_cancel_left, pow_add]
  field_simp

theorem scalar_inv_pow_mul_cancel (x y : k) (hx : x ≠ 0) (σ : ℕ) : y * 1 = (x ^ σ)⁻¹ * (x ^ σ * y) := by
  field_simp

theorem alg_e' (x y : k) (hx : x ≠ 0) (σ i : ℕ) (h : i < σ) :
    y * -1 = (x ^ σ)⁻¹ * (-(-((-x) ^ σ * x ^ σ)) / x) * (-1 / x) ^ (σ - 1 - i) * (y * ((-x) ^ i)⁻¹) := by
  obtain ⟨e, rfl⟩ : ∃ e, σ = i + 1 + e := ⟨σ - 1 - i, by omega⟩
  have hx' : -x ≠ 0 := neg_ne_zero.2 hx
  rw [show i + 1 + e - 1 - i = e by omega, show (-1 / x) = (-x)⁻¹ by rw [neg_div, one_div, neg_inv], inv_pow, pow_add (-x),
    pow_succ (-x)]
  have ha : (-x) ^ i ≠ 0 := pow_ne_zero _ hx'
  have hb : (-x) ^ e ≠ 0 := pow_ne_zero _ hx'
  generalize (-x) ^ i = a at ha ⊢
  generalize (-x) ^ e = b at hb ⊢
  field_simp

end Alg

section Core

variable {D : D7} {A B : HSp D} {c : ℕ}

theorem coreMat_iA_bes {σ : ℕ} (d : HermitianOrthogonalExtensionData A B c (-1)) (h : c = 2 * σ + 1) :
    GlobalTheory.RowUnf.coreMat d h * (GlobalTheory.OrthSumExists.orthDecHsum D A (GlobalTheory.SeeSaw.Model.nLine D)).iA = frameMat B A d.ι := by
  refine (Matrix.submatrix_mul_equiv _ _ _ _ _).trans ?_
  show Matrix.fromCols (frameMat B A d.ι) (GlobalTheory.RowUnf.midCol d h) *
      Matrix.fromRows (1 : Matrix (Fin A.rank) (Fin A.rank) D.host.E) (0 : Matrix (Fin 1) (Fin A.rank) D.host.E) = _
  rw [Matrix.fromCols_mul_fromRows, Matrix.mul_one, Matrix.mul_zero, add_zero]

theorem coreMat_vecB_bes {σ : ℕ} (d : HermitianOrthogonalExtensionData A B c (-1)) (h : c = 2 * σ + 1) (x : D.host.E) :
    GlobalTheory.RowUnf.coreMat d h *ᵥ vecB (GlobalTheory.OrthSumExists.orthDecHsum D A (GlobalTheory.SeeSaw.Model.nLine D)) (fun _ => x) =
      fun k => x * d.a k ⟨σ, by omega⟩ := by
  have e : GlobalTheory.RowUnf.coreMat d h * (GlobalTheory.OrthSumExists.orthDecHsum D A (GlobalTheory.SeeSaw.Model.nLine D)).iB =
      GlobalTheory.RowUnf.midCol d h := by
    refine (Matrix.submatrix_mul_equiv _ _ _ _ _).trans ?_
    show Matrix.fromCols (frameMat B A d.ι) (GlobalTheory.RowUnf.midCol d h) *
        Matrix.fromRows (0 : Matrix (Fin A.rank) (Fin 1) D.host.E) (1 : Matrix (Fin 1) (Fin 1) D.host.E) = _
    rw [Matrix.fromCols_mul_fromRows, Matrix.mul_one, Matrix.mul_zero, zero_add]
  show GlobalTheory.RowUnf.coreMat d h *ᵥ (_ *ᵥ _) = _
  rw [Matrix.mulVec_mulVec, e]
  funext k
  show ∑ j : Fin 1, GlobalTheory.RowUnf.midCol d h k j * x = _
  simp [GlobalTheory.RowUnf.midCol, mul_comm]

theorem nLine_norm (x : D.host.E) :
    star (fun _ : Fin (GlobalTheory.SeeSaw.Model.nLine D).rank => x) ⬝ᵥ (GlobalTheory.SeeSaw.Model.nLine D).gram *ᵥ (fun _ => x) = -(star x * x) := by
  show ∑ i : Fin 1, star x * ∑ j : Fin 1, (GlobalTheory.SeeSaw.Model.nLine D).gram i j * x = _
  simp [GlobalTheory.RowUnf.nLine_gram]

end Core

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem BesP₂ (ch : Choice R) : BesP ch := by
  intro t w hw p hp M hM j σ hj vN a ha c hc
  have hjm : j < D.R.m := by omega
  have hje : Even j := by
    obtain ⟨k, hk⟩ := D.R.m_even
    exact ⟨k - σ - 1, by omega⟩
  have E := mvFr_entries ch.S.toGridChoice (Set.mem_univ t) hw p hjm hje a ha hc
  have hpr : ∀ x, p.pr x = algebraMap D.host.E (Kw w) x := fun x => by
    rw [Place.pr, hp.2.1]
    exact GlobalTheory.FunObj.Good.cpt_incA w x
  have hxi : p.xi = algebraMap D.host.E (Kw w) D.host.xi0 := hpr _
  have hx0 : algebraMap D.host.E (Kw w) D.host.xi0 ≠ 0 := hxi ▸ GlobalTheory.LocMod.Witness.xi_ne p
  have hTA : (locGrid ch.G t w).rank (D.R.m, j) + j + 1 = topRank (locGrid ch.G t w) j + D.R.m :=
    (topRank_add (G := locGrid ch.G t w) one_le_sLen j).symm
  have hc' : c = 2 * σ + 1 := by omega
  have hc2 : D.R.m - 1 - j = 2 * σ + 1 := by omega
  refine ⟨hc', fun r q => ?_, fun i q hiq r => ?_, fun q hq r => ?_, fun i q hiq r => ?_⟩
  · refine ((E r).1 q).trans ?_
    have e1 : ((besAt ch.G hM j σ hj vN).d.i₀ * (besAt ch.G hM j σ hj vN).o.iA) =
        frameMat (ch.G.V (Node.grid D.R.m j)) (ch.G.V (Node.top j)) (ch.G.rowDec j hjm).ι :=
      coreMat_iA_bes (ch.G.rowDec j hjm) hc2
    rw [e1]
    erw [Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun y _ => ?_
    exact congrArg₂ (· * ·) (hpr _).symm rfl
  · refine ((E r).2 q ⟨q.val, by omega⟩ rfl).trans ?_
    have hd : (besAt ch.G hM j σ hj vN).d.e r i = (ch.G.rowDec j hjm).a r ⟨q.val, by omega⟩ * D.host.xi0 ^ i.val := by
      show (((ch.G.rowDec j hjm).iso σ (by omega) * diagonal (GlobalTheory.RowChain.lam σ) :
        Matrix (Fin (ch.G.V (Node.grid D.R.m j)).rank) (Fin σ) D.host.E)) r i = _
      erw [mul_diagonal]
      simp only [HermitianOrthogonalExtensionData.iso, submatrix_apply, id, GlobalTheory.RowChain.lam]
      congr 2
      show (ch.G.rowDec j hjm).a r (Fin.castLE (by omega) i) = _
      exact congrArg _ (Fin.ext (by simp [hiq]))
    rw [hd, hpr, hxi, map_mul, map_pow, frameSign, if_neg (by first | omega | (simp only [Fin.val_mk]; omega) | (simp; omega))]
    exact alg_e _ _ hx0 σ i.val (by omega)
  · refine ((E r).2 q ⟨σ, by omega⟩ hq.symm).trans ?_
    have hv : (besAt ch.G hM j σ hj vN).d.i₀ *ᵥ vecB (besAt ch.G hM j σ hj vN).o (besAt ch.G hM j σ hj vN).ζ =
        fun k => D.host.xi0 ^ σ * (ch.G.rowDec j hjm).a k ⟨σ, by omega⟩ :=
      coreMat_vecB_bes (ch.G.rowDec j hjm) hc2 (D.host.xi0 ^ σ)
    rw [hv, hpr, hxi, map_mul, map_pow, frameSign, if_neg (by first | omega | (simp only [Fin.val_mk]; omega) | (simp; omega))]
    exact scalar_inv_pow_mul_cancel _ _ hx0 σ
  · refine ((E r).2 q ⟨q.val, by omega⟩ rfl).trans ?_
    have hd : (besAt ch.G hM j σ hj vN).d.e' r i =
        (ch.G.rowDec j hjm).a r ⟨q.val, by omega⟩ * (star (D.host.xi0 ^ i.val))⁻¹ := by
      show (((ch.G.rowDec j hjm).a.submatrix id (fun i : Fin σ => (Fin.castLE (by omega : σ ≤ D.R.m - 1 - j) i).rev) *
        diagonal (fun a => (star (GlobalTheory.RowChain.lam (D := D) σ a))⁻¹) :
        Matrix (Fin (ch.G.V (Node.grid D.R.m j)).rank) (Fin σ) D.host.E)) r i = _
      erw [mul_diagonal]
      simp only [submatrix_apply, id, GlobalTheory.RowChain.lam]
      congr 2
      show (ch.G.rowDec j hjm).a r (Fin.castLE (by omega) i).rev = _
      exact congrArg _ (Fin.ext (by simp only [Fin.val_rev, Fin.val_castLE]; omega))
    have hz : p.hz (besAt ch.G hM j σ hj vN) = algebraMap D.host.E (Kw w) (-(star (D.host.xi0 ^ σ) * D.host.xi0 ^ σ)) := by
      rw [Place.hz, hpr]
      exact congrArg _ (nLine_norm _)
    have hs : ∀ n : ℕ, star (D.host.xi0 ^ n) = (-D.host.xi0) ^ n := fun n => by
      rw [star_pow, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg]
    rw [hd, hz, hpr, hxi, hs, hs, frameSign, if_pos (by first | omega | (simp only [Fin.val_mk]; omega) | (simp; omega))]
    simp only [map_mul, map_neg, map_pow, map_inv₀]
    exact alg_e' _ _ hx0 σ i.val i.2

end Main

theorem Big₂ : Big fun ch => BesP ch :=
  ⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ R _ _ ch _ _ => BesP₂ (R := R) ch⟩⟩

end GlobalTheory.FlatPlace
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselFrameOfGridLatticeLargeDepthStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselFrameOfGridLattice_largeDepth : Big fun ch => BesP ch := by
  first | exact @GlobalTheory.FlatPlace.Big₂ | exact GlobalTheory.FlatPlace.Big₂ | (intros; apply GlobalTheory.FlatPlace.Big₂ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DictionaryPointsLocalMatricesLargeDepth
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DictionaryPointsLocalMatricesLargeDepth
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

noncomputable section

namespace GlobalTheory.FlatPlaceLoc

open GlobalTheory.FlatPlace GlobalTheory.LocMod

variable {D : D7}

theorem mt_mul' (V : HSp D) (a b : GA D V) : Formalism.L2.Theta.mt V (a * b) = Formalism.L2.Theta.mt V a * Formalism.L2.Theta.mt V b := by
  simp [Formalism.L2.Theta.mt]

theorem mt_inv_mul' (V : HSp D) (a : GA D V) : Formalism.L2.Theta.mt V a⁻¹ * Formalism.L2.Theta.mt V a = 1 := by
  simp [Formalism.L2.Theta.mt]

theorem map_eq_one_of_off {w : Pl D.host.E} {p : Place D (Kw w)} (hp : IsPlc w p) {V : HSp D} {g : GA D V}
    (hg : g ∈ GlobalTheory.FinPl.grpOff V (· = w.under (𝓞 D.host.F))) : (Formalism.L2.Theta.mt V g).map p.π = 1 := by
  ext i k
  have h0 := (GlobalTheory.FinPl.SetCut.mem_grpOff_iff_parts V _ g).1 hg i k _ rfl
  have h1 : p.π ((Formalism.L2.Theta.mt V g - 1) i k) = 0 := by
    rw [hp.2.1]
    exact (GlobalTheory.LocHat.prV_eq_zero_iff_cpt _ _).1 (GlobalTheory.StabOff.prV_toEAf_eq_zero _ _ h0) w rfl
  rw [Matrix.sub_apply, map_sub, sub_eq_zero] at h1
  rw [Matrix.map_apply, h1, ← Matrix.map_apply (f := p.π), Matrix.map_one _ (map_zero _) (map_one _)]

theorem suppAt_iff' (e : AE D) (V : HSp D) (g : GA D V) :
    SuppAt e V g ↔ (e + cA D e) • (Formalism.L2.Theta.mt V g - 1) = Formalism.L2.Theta.mt V g - 1 := by
  constructor
  · intro h
    ext i j
    exact h i j
  · intro h i j
    exact congrFun (congrFun h i) j

theorem suppAt_mul' {e : AE D} {V : HSp D} {a b : GA D V} (ha : SuppAt e V a) (hb : SuppAt e V b) : SuppAt e V (a * b) := by
  rw [suppAt_iff'] at ha hb ⊢
  have : Formalism.L2.Theta.mt V (a * b) - 1 = (Formalism.L2.Theta.mt V a - 1) * Formalism.L2.Theta.mt V b + (Formalism.L2.Theta.mt V b - 1) := by
    rw [mt_mul', Matrix.sub_mul, Matrix.one_mul]; abel
  rw [this, smul_add, ← smul_mul_assoc, ha, hb]

theorem suppAt_inv' {e : AE D} {V : HSp D} {a : GA D V} (ha : SuppAt e V a) : SuppAt e V a⁻¹ := by
  rw [suppAt_iff'] at ha ⊢
  have : Formalism.L2.Theta.mt V a⁻¹ - 1 = -(Formalism.L2.Theta.mt V a⁻¹ * (Formalism.L2.Theta.mt V a - 1)) := by
    rw [Matrix.mul_sub, mt_inv_mul', Matrix.mul_one]; abel
  rw [this, smul_neg, ← mul_smul_comm, ha]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)
  {Y : Type} [Fintype Y] [DecidableEq Y]

theorem isLoc_mul' {S : HSp D} {F : Frame k S.rank Y} {a b : GA D S} {x y : GL Y k} (ha : p.IsLoc F a x)
    (hb : p.IsLoc F b y) : p.IsLoc F (a * b) (x * y) := by
  refine ⟨suppAt_mul' ha.1 hb.1, ?_⟩
  rw [mt_mul', Matrix.map_mul, ha.2, hb.2, Units.val_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc F.γ, F.γβ, Matrix.one_mul]

theorem isLoc_inv' {S : HSp D} {F : Frame k S.rank Y} {a : GA D S} {x : GL Y k} (ha : p.IsLoc F a x) :
    p.IsLoc F a⁻¹ x⁻¹ := by
  refine ⟨suppAt_inv' ha.1, ?_⟩
  have h1 : (Formalism.L2.Theta.mt S a⁻¹).map p.π * (F.β * x.val * F.γ) = 1 := by
    rw [← ha.2, ← Matrix.map_mul, mt_inv_mul', Matrix.map_one _ (map_zero _) (map_one _)]
  have h2 : (F.β * x.val * F.γ) * (F.β * (x⁻¹).val * F.γ) = 1 := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc F.γ, F.γβ, Matrix.one_mul, ← Matrix.mul_assoc x.val, Units.mul_inv, Matrix.one_mul, F.βγ]
  calc (Formalism.L2.Theta.mt S a⁻¹).map p.π = (Formalism.L2.Theta.mt S a⁻¹).map p.π * ((F.β * x.val * F.γ) * (F.β * (x⁻¹).val * F.γ)) := by
        rw [h2, Matrix.mul_one]
    _ = F.β * (x⁻¹).val * F.γ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]

omit p in
theorem frOf_conj {n N : ℕ} (h : N = n) (β : GL (Fin n) (Lev.EAf D)) (w : Pl D.host.E) (x : GL (Fin n) (Lev.EAf D)) :
    (frOf h β w).β * (GlobalTheory.FunObj.inBasis h β w x).val * (frOf h β w).γ = (loc w x).val := by
  subst h
  have e1 : (frOf rfl β w).β = (loc w β).val := by ext i j; rfl
  have e2 : (frOf rfl β w).γ = ((loc w β)⁻¹).val := by ext i j; rfl
  have e3 : GlobalTheory.FunObj.inBasis rfl β w x = (loc w β)⁻¹ * loc w x * loc w β := by
    have e4 : GlobalTheory.FunObj.inBasis rfl β w x = GlobalTheory.StepData.reGL (finCongr rfl) (loc w (β⁻¹ * x * β)) := by
      simp only [GlobalTheory.FunObj.inBasis, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have e5 : ∀ g : GL (Fin N) (Kw w), GlobalTheory.StepData.reGL (finCongr rfl) g = g := fun g => Units.ext (by ext i j; rfl)
    rw [e4, e5, map_mul, map_mul, map_inv]
  rw [e1, e2, e3, ← Units.val_mul, ← Units.val_mul]
  congr 1
  group

end GlobalTheory.FlatPlaceLoc

namespace GlobalTheory.FlatPlaceLoc

open GlobalTheory.FlatPlace GlobalTheory.LocMod

variable {D : D7}

theorem loc_finE {w : Pl D.host.E} {p : Place D (Kw w)} (hp : IsPlc w p) {V : HSp D} (g : GA D V) :
    (loc w (Lev.finE V g)).val = (Formalism.L2.Theta.mt V g).map p.π := by
  ext i j
  rw [Matrix.map_apply, hp.2.1]
  rfl

theorem isLoc_of_inBasis {w : Pl D.host.E} {p : Place D (Kw w)} (hp : IsPlc w p) {V : HSp D} {N : ℕ} (h : N = V.rank)
    (β : GL (Fin V.rank) (Lev.EAf D)) (g : GA D V) (gk : GL (Fin N) (Kw w)) (hs : SuppAt p.e V g)
    (hb : GlobalTheory.FunObj.inBasis h β w (Lev.finE V g) = gk) : p.IsLoc (frOf h β w) g gk :=
  ⟨hs, by rw [← hb, frOf_conj, loc_finE hp]⟩

theorem elt_zero {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (w : Pl D.host.E)
    (β : Cosets (G := locGrid G t w) one_le_sLen (givenLevel G t w)) :
    (repsAt G t w).elt β (D.R.m, 0) = stair (locGrid G t w) (unifAt w) (cosExp G w) 0 :=
  (onColumn_apply (G := locGrid G t w) _ 0).trans rfl


open Classical in
theorem localization₂ : Big fun ch => LocP ch := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  intro t w hw p hp β r r₀ h hpts j hj
  obtain ⟨hr, hr₀, hh⟩ := hpts
  have L1 : p.IsLoc (frRow ch.S.B t w j hj) (r j) _ := isLoc_of_inBasis hp _ _ _ _ (hr j hj).1 (hr j hj).2
  have L0 : p.IsLoc (frRow ch.S.B t w j hj) (r₀ j) _ := isLoc_of_inBasis hp _ _ _ _ (hr₀ j hj).1 (hr₀ j hj).2
  refine ⟨?_, fun he => ?_, fun ho => ?_⟩
  · convert isLoc_mul' p (isLoc_inv' p L0) L1 using 1
    beta_reduce
    rw [Pi.mul_apply]
    by_cases h0 : j = 0
    · subst h0
      have hn : (0 : ℕ) ∉ idx D := by rw [mem_idx]; omega
      rw [if_pos rfl, if_neg hn, epsV_apply, if_neg hn, one_mul, elt_zero]
      exact (inv_inv _).symm.trans (mul_one _).symm
    · by_cases hi : j ∈ idx D
      · rw [if_neg h0, if_pos hi, inv_one, one_mul, epsV_apply, if_pos hi]
      · have hm : D.R.m ≤ j + 1 := by rw [mem_idx] at hi; omega
        rw [if_neg h0, if_neg hi, inv_one, mul_one, epsV_eq_one t w hm, elt_eq_one t w β hm, mul_one]
  · obtain ⟨δ, hδ, hoff⟩ := hh j hj
    rw [hδ.2.1 he, inv_one, one_mul] at hoff
    rw [mt_mul', Matrix.map_mul, map_eq_one_of_off hp hoff, Matrix.one_mul, L0.2, Matrix.mul_assoc,
      (frRow ch.S.B t w j hj).γβ, Matrix.mul_one]
    rfl
  · obtain ⟨δ, hδ, hoff⟩ := hh j hj
    refine ⟨δ, hδ, ?_⟩
    have h0 : j ≠ 0 := by rintro rfl; simp at ho
    have hr0 : (Formalism.L2.Theta.mt _ (r₀ j)).map p.π = 1 := by
      rw [L0.2]
      simp only [if_neg h0, Units.val_one, Matrix.mul_one, (frRow ch.S.B t w j hj).βγ]
    rw [mt_mul', Matrix.map_mul, hr0, Matrix.mul_one, ← mul_inv_cancel_left δ (h j), mt_mul', Matrix.map_mul,
      map_eq_one_of_off hp hoff, Matrix.mul_one]

end GlobalTheory.FlatPlaceLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DictionaryPointsLocalMatricesLargeDepthStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dictionaryPoints_localMatrices_largeDepth : Big fun ch => LocP ch := by
  first | exact @GlobalTheory.FlatPlaceLoc.localization₂ | exact GlobalTheory.FlatPlaceLoc.localization₂ | (intros; apply GlobalTheory.FlatPlaceLoc.localization₂ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProdEqSumOfFactorwiseLinearExpansion
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProdEqSumOfFactorwiseLinearExpansion
namespace GlobalTheory


open Finset in
theorem prod_eq_sum_of_factorwise_expansion : ∀ (K : Type) [Fintype K] (X : K → Type) (I : Type) (S : Finset I) (x : I → ℂ) (a : ∀ n, I → X n → ℂ) (b : K → I → ℂ) (A : ∀ n, X n → ℂ) (B : K → ℂ), (∀ n (y : I → ℂ), (∀ q, ∑ i ∈ S, y i * a n i q = 0) → ∑ i ∈ S, y i * b n i = 0) → (∀ n (y : I → ℂ), (∀ q, A n q = ∑ i ∈ S, y i * a n i q) → B n = ∑ i ∈ S, y i * b n i) → (∀ q : ∀ n, X n, ∏ n, A n (q n) = ∑ i ∈ S, x i * ∏ n, a n i (q n)) → (∀ n, Nonempty (X n)) → ∏ n, B n = ∑ i ∈ S, x i * ∏ n, b n i := by
  intro K _ X I S x a b A B h1 h2 h3 hne
  classical
  have key : ∀ T : Finset K, ∀ q : ∀ n, X n,
      ∑ i ∈ S, x i * ∏ n, (if n ∈ T then b n i else a n i (q n)) =
        ∏ n, (if n ∈ T then B n else A n (q n)) := by
    intro T
    induction T using Finset.induction_on with
    | empty => intro q; simpa using (h3 q).symm
    | insert m T hm ih =>
      intro q
      obtain ⟨c, hc⟩ : ∃ c, c = ∏ n ∈ univ.erase m, (if n ∈ T then B n else A n (q n)) := ⟨_, rfl⟩
      obtain ⟨y, hy⟩ : ∃ y : I → ℂ, y = fun i => x i * ∏ n ∈ univ.erase m,
          (if n ∈ T then b n i else a n i (q n)) := ⟨_, rfl⟩
      have hL : ∀ t, ∑ i ∈ S, y i * a m i t = A m t * c := by
        intro t
        have h := ih (Function.update q m t)
        have e1 : ∀ i, ∏ n, (if n ∈ T then b n i else a n i (Function.update q m t n)) =
            a m i t * ∏ n ∈ univ.erase m, (if n ∈ T then b n i else a n i (q n)) := by
          intro i
          rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ m)]
          congr 1
          · simp [hm]
          · apply Finset.prod_congr rfl
            intro n hn
            have hnm : n ≠ m := Finset.ne_of_mem_erase hn
            rw [Function.update_of_ne hnm]
        have e2 : ∏ n, (if n ∈ T then B n else A n (Function.update q m t n)) = A m t * c := by
          rw [hc, ← Finset.mul_prod_erase _ _ (Finset.mem_univ m)]
          congr 1
          · simp [hm]
          · apply Finset.prod_congr rfl
            intro n hn
            have hnm : n ≠ m := Finset.ne_of_mem_erase hn
            rw [Function.update_of_ne hnm]
        rw [e2] at h
        simp only [e1] at h
        rw [← h, hy]
        apply Finset.sum_congr rfl
        intro i _
        ring
      have e3 : ∀ i, ∏ n, (if n ∈ insert m T then b n i else a n i (q n)) =
          b m i * ∏ n ∈ univ.erase m, (if n ∈ T then b n i else a n i (q n)) := by
        intro i
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ m)]
        congr 1
        · simp
        · apply Finset.prod_congr rfl
          intro n hn
          have hnm : n ≠ m := Finset.ne_of_mem_erase hn
          simp [Finset.mem_insert, hnm]
      have e4 : ∏ n, (if n ∈ insert m T then B n else A n (q n)) = B m * c := by
        rw [hc, ← Finset.mul_prod_erase _ _ (Finset.mem_univ m)]
        congr 1
        · simp
        · apply Finset.prod_congr rfl
          intro n hn
          have hnm : n ≠ m := Finset.ne_of_mem_erase hn
          simp [Finset.mem_insert, hnm]
      rw [e4]
      simp only [e3]
      have hs : ∑ i ∈ S, x i * (b m i * ∏ n ∈ univ.erase m, (if n ∈ T then b n i else a n i (q n))) =
          ∑ i ∈ S, y i * b m i := by
        rw [hy]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hs]
      by_cases hc0 : c = 0
      · rw [hc0, mul_zero]
        apply h1 m y
        intro t
        rw [hL t, hc0, mul_zero]
      · have hB := h2 m (fun i => y i / c) (by
          intro t
          have : ∑ i ∈ S, y i / c * a m i t = (∑ i ∈ S, y i * a m i t) / c := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro i _
            ring
          rw [this, hL t, mul_div_cancel_right₀ _ hc0])
        rw [hB, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        field_simp
  obtain ⟨q⟩ : Nonempty (∀ n, X n) := ⟨fun n => Classical.choice (hne n)⟩
  simpa using (key Finset.univ q).symm

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProdEqSumOfFactorwiseLinearExpansionStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_eq_sum_of_factorwise_linear_expansion : ∀ (K : Type) [Fintype K] (X : K → Type) (I : Type) (S : Finset I) (x : I → ℂ) (a : ∀ n, I → X n → ℂ) (b : K → I → ℂ) (A : ∀ n, X n → ℂ) (B : K → ℂ), (∀ n (y : I → ℂ), (∀ q, ∑ i ∈ S, y i * a n i q = 0) → ∑ i ∈ S, y i * b n i = 0) → (∀ n (y : I → ℂ), (∀ q, A n q = ∑ i ∈ S, y i * a n i q) → B n = ∑ i ∈ S, y i * b n i) → (∀ q : ∀ n, X n, ∏ n, A n (q n) = ∑ i ∈ S, x i * ∏ n, a n i (q n)) → (∀ n, Nonempty (X n)) → ∏ n, B n = ∑ i ∈ S, x i * ∏ n, b n i := by
  first | exact @GlobalTheory.prod_eq_sum_of_factorwise_expansion | exact GlobalTheory.prod_eq_sum_of_factorwise_expansion | (intros; apply GlobalTheory.prod_eq_sum_of_factorwise_expansion <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSignFlatDictionaryAtOnePlaceLargeDepth
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil
open GlobalTheory.SplitFlip (Grid Edge oppositePath)

namespace GlobalTheory.FlatPlace

theorem prod_range_pairs (g : ℕ → ℂ) (n : ℕ) : ∏ j ∈ Finset.range (2 * n), g j = ∏ l ∈ Finset.range n, g (2 * l) * g (2 * l + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.mul_succ, Finset.prod_range_succ, Finset.prod_range_succ, ih, Finset.prod_range_succ, mul_assoc]

theorem prod_fin_pairs {m : ℕ} (hm : Even m) (g : Fin m → ℂ) :
    ∏ j, g j = ∏ l : Fin (m / 2), g ⟨2 * l, by have := l.2; omega⟩ * g ⟨2 * l + 1, by have := l.2; omega⟩ := by
  have h2 : m = 2 * (m / 2) := by obtain ⟨a, ha⟩ := hm; omega
  let g' : ℕ → ℂ := fun j => if h : j < m then g ⟨j, h⟩ else 1
  have e1 : ∏ j, g j = ∏ j ∈ Finset.range m, g' j := by
    rw [Finset.prod_range]
    exact Finset.prod_congr rfl fun j _ => by simp only [g', dif_pos j.2]
  rw [e1, congrArg Finset.range h2, prod_range_pairs, Finset.prod_range]
  refine Finset.prod_congr rfl fun l _ => ?_
  have := l.2
  simp only [g']
  rw [dif_pos (by omega), dif_pos (by omega)]

theorem exists_unpair {Y : ℕ → Type} [∀ j, Nonempty (Y j)] {n : ℕ} (q : ∀ l : Fin n, Y (2 * l) × Y (2 * l + 1)) :
    ∃ x : ∀ j, Y j, ∀ l : Fin n, (x (2 * l), x (2 * l + 1)) = q l := by
  have h : ∀ j, ∃ y : Y j, ∀ l : Fin n, (j = 2 * l → HEq y (q l).1) ∧ (j = 2 * l + 1 → HEq y (q l).2) := fun j => by
    by_cases h1 : ∃ l : Fin n, j = 2 * l
    · obtain ⟨l, rfl⟩ := h1
      refine ⟨(q l).1, fun l' => ⟨fun e => ?_, fun e => by omega⟩⟩
      obtain rfl : l = l' := Fin.ext (by omega)
      rfl
    · by_cases h2 : ∃ l : Fin n, j = 2 * l + 1
      · obtain ⟨l, rfl⟩ := h2
        refine ⟨(q l).2, fun l' => ⟨fun e => by omega, fun e => ?_⟩⟩
        obtain rfl : l = l' := Fin.ext (by omega)
        rfl
      · exact ⟨Classical.arbitrary _, fun l => ⟨fun e => absurd ⟨l, e⟩ h1, fun e => absurd ⟨l, e⟩ h2⟩⟩
  choose x hx using h
  exact ⟨x, fun l => Prod.ext (eq_of_heq ((hx _ l).1 rfl)) (eq_of_heq ((hx _ l).2 rfl))⟩

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Γ : Grid k)

theorem pureTensor_phiM (keep : Bool) (ε g : Γ.VertexGroup)
    (φ : ∀ b : Edge, Matrix (Fin (Γ.rank b.tgt)) (Fin (Γ.rank b.src)) k → ℂ) (z : Γ.Args) :
    Γ.lines₂ (oppositePath Γ.m) (phiM Γ (ε * g) g φ) z =
      zetaLoc Γ keep ε g * moved Γ keep g (Γ.lines₂ (oppositePath Γ.m) φ) z := by
  have h1 : Γ.edgeFactor .one (ε * g) = fun e => Γ.edgeFactor .one ε e * Γ.edgeFactor .one g e := by
    funext e
    simp only [Grid.edgeFactor, Pi.mul_apply, map_mul, GlobalTheory.SplitFlip.apow_mul, _root_.mul_inv_rev, Units.val_mul]
    ring
  have h2 : Γ.lines₂ (oppositePath Γ.m) (phiM Γ (ε * g) g φ) z = ((oppositePath Γ.m).map (Γ.edgeFactor .one ε)).prod *
      Γ.pathAct .one (oppositePath Γ.m) g (Γ.lines₂ (oppositePath Γ.m) φ) z := by
    simp only [Grid.lines₂, Grid.pathAct, phiM, h1, List.prod_map_mul, mul_assoc]
    rfl
  rw [h2, zetaLoc, moved]
  cases keep
  · simp only [Bool.false_eq_true, if_false, mul_assoc, Units.mul_inv_cancel_left]
  · simp only [if_true, mul_one, one_mul]

theorem flatTensor_phiM [MeasurableSpace k] [BorelSpace k] (hs : 1 ≤ Γ.s) (ψ : AddChar k Circle) (ν : Measure k) (keep : Bool)
    (ε g : Γ.VertexGroup) (φ : ∀ b : Edge, Matrix (Fin (Γ.rank b.tgt)) (Fin (Γ.rank b.src)) k → ℂ) (x : ColArgs Γ) (y : RowArgs Γ) :
    flatTensor hs ψ ν (Γ.lines₂ (oppositePath Γ.m) (phiM Γ (ε * g) g φ)) x y =
      zetaLoc Γ keep ε g * flatTensor hs ψ ν (moved Γ keep g (Γ.lines₂ (oppositePath Γ.m) φ)) x y := by
  simp only [flatTensor, flatIntegrand, pureTensor_phiM Γ keep, mul_assoc, integral_const_mul]

end Local

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)

theorem gv_row (t : T) (w : Pl D.host.E) (β : Cosets (G := locGrid ch.G t w) one_le_sLen (givenLevel ch.G t w)) (i : ℕ) :
    (epsV ch.G t w * (repsAt ch.G t w).elt β) (i, D.R.m) = 1 := by
  rw [Pi.mul_apply]
  by_cases hi : i = D.R.m
  · subst hi
    rw [epsV_eq_one t w (by omega), elt_eq_one t w β (by omega), mul_one]
  · have e1 : epsV ch.G t w (i, D.R.m) = 1 := dif_neg hi
    have e2 : (repsAt ch.G t w).elt β (i, D.R.m) = 1 := dif_neg hi
    rw [e1, e2, mul_one]

theorem colAt_up {t : T} {w : Pl D.host.E} {p : Place D (Kw w)} (hp : IsPlc w p) (x : ColArgs (locGrid ch.G t w)) (j : ℕ)
    (hj : j < D.R.m) : ch.S.toGridChoice.colAt t w (fun j => p.up (frTop ch.S.toGridChoice t w j j.2.le)
      (frTop ch.S.toGridChoice t w (j + 1) j.2) (x j)) j = x j := by
  rw [GridChoice.colAt, dif_pos hj]
  refine Eq.trans ?_ (Witness.down_up p (frTop ch.S.toGridChoice t w j hj.le) (frTop ch.S.toGridChoice t w (j + 1) hj) (x j))
  have e : p.π = (cpt w).comp (toEAf D) := RingHom.ext hp.2.1
  rw [Place.down, e]
  rfl

theorem placeAt_of (hc : ChrP ch) (ha : ArrP ch) (hl : LocP ch) (hd : DblP ch) (hz : LastP ch) (hb : CombP ch) (hs : ScalP ch) :
    PlaceAt ch (-1) := by
  obtain ⟨κ, z, h1, h2, h3⟩ := hs
  refine ⟨κ, z, h1, h2, fun t w hw β => ⟨_, h3 t w hw β, ?_⟩⟩
  intro e he M hM r r₀ h hr hr₀ hh φ hφ v f hv hf I S x d c hdc hx u
  obtain ⟨p, hp, rfl⟩ := GlobalTheory.T.exists_completionPlaceData D w e he
  have hm := D.R.two_le_m
  have hev : Even D.R.m := D.R.m_even
  have hP : IsPts ch t w β p.e r r₀ h := ⟨hr, hr₀, hh⟩
  have hV : ∀ j : Fin D.R.m, IsArrVec ch t w p.e φ j j.2 (v j) (f j) := fun j => ⟨hv j, hf j⟩
  have hcond := (hc t w hw p hp).2.1
  have hE : ∀ j (hj : j + 1 < D.R.m), Even j →
      Expands p j hj (facAt ch t w β φ j) (conAt ch.W hM f (h * r) j) (conAt ch.W hM v (h * r₀) j) := fun j hj hj' => by
    by_cases h2 : j + 2 = D.R.m
    · exact hz t w hw p hp β r r₀ h hP M hM φ v f hV j h2
    · exact hd t w hw p hp β r r₀ h hP M hM φ v f hV j hj' (by omega)
  have hΞ : ∀ (i : I) (j : Fin D.R.m), ∃ Ξ : SB (Matrix _ _ (Kw w)), i ∈ S →
      (∀ y, Ξ.1 y = (d i j).fn (p.up (frTop ch.S.toGridChoice t w j j.2.le) (frTop ch.S.toGridChoice t w (j + 1) j.2) y)) ∧
      p.IsCombAt ch.W.ψ (frTop ch.S.toGridChoice t w j j.2.le) (frTop ch.S.toGridChoice t w (j + 1) j.2) ((c i).1 j) Ξ.1 :=
    fun i j => by
      by_cases hi : i ∈ S
      · obtain ⟨Ξ, hΞ⟩ := hb t w hw p hp j j.2 (d i j) ((c i).1 j) (hdc i hi j).1 (hdc i hi j).2
        exact ⟨Ξ, fun _ => hΞ⟩
      · exact ⟨0, fun h => absurd h hi⟩
  choose Ξ hΞ using hΞ
  have hlt : ∀ l : Fin (D.R.m / 2), 2 * l.1 + 1 < D.R.m := fun l => by have := l.2; omega
  have hSB : ∀ j < D.R.m - 1, phiM (locGrid ch.G t w) (epsV ch.G t w * (repsAt ch.G t w).elt β) ((repsAt ch.G t w).elt β) φ
      (.theta D.R.m j) ∈ SB _ := fun j hj => by
    obtain ⟨-, -, -, Φ, hΦ, -⟩ := ha t w hw p hp φ j (by omega) _ _ (hV ⟨j, by omega⟩) _ _ (epsV_mem t w) 1 _ 1 _
      (hl t w hw p hp β r r₀ h hP j (by omega)).1 (hl t w hw p hp β r r₀ h hP (j + 1) (by omega)).1 _ _ (Equiv.refl _) (Equiv.refl _)
    obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := Kw w)
    have key : ∀ {A B : Type}, Topology.IsClosedEmbedding fun z : Matrix A B (Kw w) => zᵀ :=
      Function.LeftInverse.isClosedEmbedding (f := fun z => zᵀ) (fun z => rfl) continuous_id.matrix_transpose
        continuous_id.matrix_transpose
    have e : phiM (locGrid ch.G t w) (epsV ch.G t w * (repsAt ch.G t w).elt β) ((repsAt ch.G t w).elt β) φ (.theta D.R.m j) =
        Φ.1 ∘ fun z => zᵀ := funext fun z => (hΦ zᵀ).symm
    rw [e]
    exact ⟨Φ.2.1.comp_continuous key.continuous, Φ.2.2.comp_isClosedEmbedding key⟩
  have key := GlobalTheory.T.prod_eq_sum_of_factorwise_linear_expansion (Fin (D.R.m / 2)) _ I S
    (fun i => zetaLoc (locGrid ch.G t w) (keepAt ch.G w) (epsV ch.G t w) ((repsAt ch.G t w).elt β) * x i)
    (fun l i q => (Ξ i ⟨2 * l, by have := hlt l; omega⟩).1 q.1 * (Ξ i ⟨2 * l + 1, hlt l⟩).1 q.2)
    (fun l i => combC ch.W (c i) (conAt ch.W hM v (h * r₀)) (2 * l) (u (2 * l)) (u (2 * l + 1)))
    (fun l => facAt ch t w β φ (2 * l)) (fun l => conAt ch.W hM f (h * r) (2 * l) (u (2 * l)) (u (2 * l + 1)))
    (fun l y hy => by
      have := congrFun (congrFun ((hE (2 * l) (hlt l) (even_two_mul _) I S y _ _ (fun i => (c i).1 (2 * l))
        (fun i => (c i).1 (2 * l + 1)) fun i hi => ⟨(hΞ i ⟨2 * l, by have := hlt l; omega⟩ hi).2, (hΞ i ⟨2 * l + 1, hlt l⟩ hi).2⟩).1
        fun q₁ q₂ => hy (q₁, q₂)) (u (2 * l))) (u (2 * l + 1))
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, combC] using this)
    (fun l y hy => by
      have := congrFun (congrFun ((hE (2 * l) (hlt l) (even_two_mul _) I S y _ _ (fun i => (c i).1 (2 * l))
        (fun i => (c i).1 (2 * l + 1)) fun i hi => ⟨(hΞ i ⟨2 * l, by have := hlt l; omega⟩ hi).2, (hΞ i ⟨2 * l + 1, hlt l⟩ hi).2⟩).2
        hy) (u (2 * l))) (u (2 * l + 1))
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, combC] using this)
    (fun q => by
      obtain ⟨y, hy⟩ := exists_unpair (Y := fun j => Matrix (Fin (topRank (locGrid ch.G t w) (j + 1)))
        (Fin (topRank (locGrid ch.G t w) j)) (Kw w)) q
      have e1 := hx (fun j => p.up (frTop ch.S.toGridChoice t w j j.2.le) (frTop ch.S.toGridChoice t w (j + 1) j.2) (y j))
        fun j => Witness.up_half p _ _ _
      have e2 := GlobalTheory.T.flatTensor_pureTensor_eq_prod_localFactors (Kw w) (locGrid ch.G t w) one_le_sLen hm hev (psiAt ch.W w) (unitVol w) hcond.continuous hcond.ne_one
        (isUnitVol_unitVol w).1 _ hSB (ch.S.toGridChoice.colAt t w fun j => p.up (frTop ch.S.toGridChoice t w j j.2.le)
          (frTop ch.S.toGridChoice t w (j + 1) j.2) (y j)) 0
      replace e2 := ((flatTensor_phiM (locGrid ch.G t w) one_le_sLen (psiAt ch.W w) (unitVol w) (keepAt ch.G w) (epsV ch.G t w)
        ((repsAt ch.G t w).elt β) φ _ 0).trans (congrArg _ e1.symm)).symm.trans e2
      rw [Finset.prod_eq_one (s := Finset.range (locGrid ch.G t w).m) (fun i _ => by
        simp only [phiM, hφ, Grid.edgeFactor, mul_one]
        change ((_ : ℂˣ) : ℂ) * _ * _ * _ = 1
        rw [show (epsV ch.G t w * (repsAt ch.G t w).elt β) (Edge.ex i (locGrid ch.G t w).m).src = 1 from gv_row ch t w β i,
          show (epsV ch.G t w * (repsAt ch.G t w).elt β) (Edge.ex i (locGrid ch.G t w).m).tgt = 1 from gv_row ch t w β (i + 1)]
        simp), one_mul, Finset.prod_range] at e2
      refine Eq.trans (Finset.prod_congr rfl fun l _ => ?_) (e2.symm.trans ?_)
      · rw [colAt_up ch hp y _ (by have := hlt l; omega), colAt_up ch hp y _ (hlt l), hy l]
      · rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [← mul_assoc, prod_fin_pairs hev]
        congr 1
        refine Finset.prod_congr rfl fun l _ => ?_
        rw [(hΞ i _ hi).1, (hΞ i _ hi).1, ← hy l])
    fun l => ⟨0⟩
  simp only [evT, Pi.one_apply, Finset.prod_const_one, mul_one, Finset.prod_range]
  rw [key, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => mul_assoc _ _ _

theorem big_placeAt : Big fun ch => ∃ s, PlaceAt ch s :=
  big_mono (fun ch ⟨⟨⟨⟨⟨⟨⟨⟨⟨lat, chr⟩, loc⟩, bes⟩, jac⟩, scal⟩, arr⟩, comb⟩, dbl⟩, last⟩ =>
    ⟨-1, placeAt_of ch chr (arr lat chr) loc (dbl chr (arr lat chr) loc bes jac) (last chr (arr lat chr) loc bes jac) (comb lat) scal⟩)
  (((((((((GlobalTheory.T.frameLattice_points_eq_integralMatrices_largeDepth.and GlobalTheory.T.localCharacterComponents_largeDepth).and GlobalTheory.T.dictionaryPoints_localMatrices_largeDepth).and GlobalTheory.T.besselFrameOfGridLattice_largeDepth).and GlobalTheory.T.jacobiFrameOfGridLattice_largeDepth).and GlobalTheory.T.flatDictionaryScalar_largeDepth).and
    GlobalTheory.T.arrowLocalModel_movedFrames).and GlobalTheory.T.latticeVacuumCombination_localModel).and GlobalTheory.T.flatDictionary_doubleStep_at_place).and GlobalTheory.T.flatDictionary_lastTwoSteps_at_place)

end GlobalTheory.FlatPlace

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSignFlatDictionaryAtOnePlaceLargeDepthStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sign_flatDictionaryAtOnePlace_largeDepth : Big fun ch => ∃ s, PlaceAt ch s := by
  first | exact @GlobalTheory.FlatPlace.big_placeAt | exact GlobalTheory.FlatPlace.big_placeAt | (intros; apply GlobalTheory.FlatPlace.big_placeAt <;> assumption)
end
