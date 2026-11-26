module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCosetOfIsTensor
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletedGridArrowLatticeIffIntegralFrameMatr

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.LocalEmbeddings.StairDepth
noncomputable section

open IsDedekindDomain NumberField Matrix MeasureTheory ValuativeRel
open GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx

namespace GlobalTheory.StairDepth

variable {k : Type} [Field k] {G : Grid k}


variable (G) in
def wt (ϖ : kˣ) (e : ℕ) (X : ℕ × ℕ) (a : ℕ) : kˣ :=
  if X.1 = G.m ∧ X.2 + 2 ≤ G.m then ϖ ^ (e * (a + 1 - topRank G X.2)) else 1


variable (G) in
def dg (ϖ : kˣ) (e : ℕ) : G.VertexGroup := fun X => diagGL fun a : Fin (G.rank X) => wt G ϖ e X a

theorem wt_core (ϖ : kˣ) (e : ℕ) (X : ℕ × ℕ) {a : ℕ} (ha : a < topRank G X.2) : wt G ϖ e X a = 1 := by
  unfold wt
  split_ifs
  · rw [show a + 1 - topRank G X.2 = 0 by omega]
    simp
  · rfl

theorem wt_end (ϖ : kˣ) (e : ℕ) {i j : ℕ} (h : G.m < j + 2) (a : ℕ) : wt G ϖ e (i, j) a = 1 := by
  unfold wt
  rw [if_neg]
  rintro ⟨-, h2⟩
  dsimp only at h2
  omega

theorem moveArgs_apply (ϖ : kˣ) (e : ℕ) (z : G.Args) (b : Edge) (r : Fin (G.rank b.tgt)) (s : Fin (G.rank b.src)) :
    G.moveArgs .one (dg G ϖ e) z b r s = (wt G ϖ e b.tgt r : k) * z b r s * ((wt G ϖ e b.src s)⁻¹ : kˣ) := by
  simp only [Grid.moveArgs, Assignment.read, dg]
  change ((diagonal fun a : Fin (G.rank b.tgt) => (wt G ϖ e b.tgt a : k))ᵀ * z b *
    (diagonal fun a : Fin (G.rank b.src) => (((wt G ϖ e b.src a)⁻¹ : kˣ) : k))ᵀ) r s = _
  rw [diagonal_transpose, diagonal_transpose, mul_diagonal, diagonal_mul]

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem elt_eq [MeasurableSpace k] [BorelSpace k] (hs : 1 ≤ G.s) (J : G.Level) (ϖ : kˣ) (e : ℕ) (hm : 2 ≤ G.m) :
    (Reps.through hs J (stair G ϖ e)).elt (fun i => DoubleCoset.mk _ _ (stair G ϖ e (i + 1))) = dg G ϖ e := by
  have hd1 : ∀ X : ℕ × ℕ, ¬ (X.1 = G.m ∧ X.2 + 2 ≤ G.m) → dg G ϖ e X = 1 := by
    intro X hX
    apply Units.ext
    ext a b
    simp [dg, diagGL, wt, hX, Matrix.one_apply, Matrix.diagonal_apply]
  funext X
  obtain ⟨i, j⟩ := X
  by_cases hc : i = G.m ∧ j + 2 ≤ G.m
  · obtain ⟨rfl, hj⟩ := hc
    rw [through_elt _ hj]
    apply Units.ext
    ext a b
    simp [stair, dg, diagGL, wt, hj]
  · rw [hd1 _ hc]
    by_cases hi : i = G.m
    · subst hi
      have hj : G.m < j + 2 := by
        simp only [true_and] at hc
        omega
      obtain _ | j := j
      · omega
      · simp only [Reps.elt, onColumn_apply]
        rw [dif_neg (by omega)]
    · simp only [Reps.elt, onColumn]
      rw [dif_neg hi]

theorem val_wt_le {ϖ : kˣ} (hϖ : IsUnif ϖ) (e : ℕ) (X : ℕ × ℕ) (a : ℕ) : valuation k (wt G ϖ e X a : k) ≤ 1 := by
  unfold wt
  split_ifs
  · simpa using val_pow_anti hϖ (Nat.zero_le (e * (a + 1 - topRank G X.2)))
  · simp

theorem moved_supp {ϖ : kˣ} {e : ℕ}
    {T : G.Args → ℂ} (hT : G.IsTensor ϖ e (oppositePath G.m) T) (keep : Bool) {z : G.Args}
    (hz : moved G keep (dg G ϖ e) T z ≠ 0) {b : Edge} (hb : b ∈ oppositePath G.m) (r : Fin (G.rank b.tgt))
    (s : Fin (G.rank b.src)) :
    valuation k ((wt G ϖ e b.tgt r : k) * z b r s * ((wt G ϖ e b.src s)⁻¹ : kˣ)) ≤ 1 := by
  have hT0 : T (G.moveArgs .one (dg G ϖ e) z) ≠ 0 := by
    intro h0; apply hz; simp [moved, Grid.pathAct, h0]
  have hint : G.moveArgs .one (dg G ϖ e) z b ∈ matLat _ (SplitFlip.stdLat k _) := by
    by_contra hc; exact hT0 (hT.2.1 _ b hb hc)
  rw [← moveArgs_apply]
  exact mem_matLat_stdLat.1 hint r s

theorem moved_per {ϖ : kˣ} {e : ℕ}
    {T : G.Args → ℂ} (hT : G.IsTensor ϖ e (oppositePath G.m) T) (keep : Bool) (z z' : G.Args)
    (hδ : ∀ b ∈ oppositePath G.m, ∀ (r : Fin (G.rank b.tgt)) (s : Fin (G.rank b.src)),
      valuation k ((wt G ϖ e b.tgt r : k) * (z' - z) b r s * ((wt G ϖ e b.src s)⁻¹ : kˣ)) ≤
        valuation k ((ϖ ^ e : kˣ) : k)) :
    moved G keep (dg G ϖ e) T z' = moved G keep (dg G ϖ e) T z := by
  have key : T (G.moveArgs .one (dg G ϖ e) z') = T (G.moveArgs .one (dg G ϖ e) z) := by
    let d : G.Args := fun b => if b ∈ oppositePath G.m then
      G.moveArgs .one (dg G ϖ e) z' b - G.moveArgs .one (dg G ϖ e) z b else 0
    have h1 : T (G.moveArgs .one (dg G ϖ e) z + d) = T (G.moveArgs .one (dg G ϖ e) z) := by
      apply hT.2.2
      intro b
      rw [FourierDepth.mem_matLat_smul_stdLat]
      intro r s
      by_cases hb : b ∈ oppositePath G.m
      · simp only [d, if_pos hb, Matrix.sub_apply, moveArgs_apply]
        convert hδ b hb r s using 2
        simp only [Pi.sub_apply, Matrix.sub_apply]
        ring
      · simp [d, hb]
    rw [← h1]
    apply hT.1
    intro b hb
    have hb' : b ∈ oppositePath G.m := hb
    simp [d, hb']
  simp only [moved, Grid.pathAct, key]

variable (hs : 1 ≤ G.s)

private theorem lt_of_frame_symm_eq_inl {p c m : ℕ} (h : p + c = m) (i : Fin m) (q : Fin p)
    (hq : (frame h).symm i = Sum.inl q) : (i : ℕ) < p := by
  have hi : i = frame h (Sum.inl q) := by
    rw [← hq]
    simp
  rw [hi]
  simp [frame]

private theorem lt_and_lt_of_fromBlocks_frame_ne_zero {p q c d m n : ℕ} (A : Matrix (Fin p) (Fin q) k) (h1 : p + c = m) (h2 : q + d = n)
    (s : Fin m) (r : Fin n)
    (hne : fromBlocks A 0 0 (0 : Matrix (Fin c) (Fin d) k) ((frame h1).symm s) ((frame h2).symm r) ≠ 0) :
    (s : ℕ) < p ∧ (r : ℕ) < q := by
  rcases hs' : (frame h1).symm s with s' | s' <;> rcases hr' : (frame h2).symm r with r' | r' <;>
    rw [hs', hr'] at hne <;>
    simp only [fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.zero_apply,
      ne_eq, not_true_eq_false] at hne
  exact ⟨lt_of_frame_symm_eq_inl h1 s s' hs', lt_of_frame_symm_eq_inl h2 r r' hr'⟩

theorem fill_sub_wt_le (ϖ : kˣ) (e : ℕ) {x a : ColArgs G} {y b : RowArgs G} {t : ValueGroupWithZero k}
    (ha : ∀ j, j < G.m → ∀ r s, valuation k (a j r s) ≤ t) (hb : ∀ i, i < G.m → ∀ r s, valuation k (b i r s) ≤ t)
    (u : Vars G) {c : Edge} (hc : c ∈ oppositePath G.m) (r : Fin (G.rank c.tgt)) (s : Fin (G.rank c.src)) :
    valuation k ((wt G ϖ e c.tgt r : k) * (fill hs (x + a) (y + b) u - fill hs x y u) c r s *
      ((wt G ϖ e c.src s)⁻¹ : kˣ)) ≤ t := by
  have key : ∀ (r : Fin (G.rank c.tgt)) (s : Fin (G.rank c.src)),
      (fill hs (x + a) (y + b) u - fill hs x y u) c r s ≠ 0 →
        wt G ϖ e c.tgt r = 1 ∧ wt G ϖ e c.src s = 1 := by
    rcases FlatDep.mem_opp hc with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
    · intro r s _
      exact ⟨wt_end (G := G) ϖ e (i := i + 1) (j := G.m) (by omega) _,
        wt_end (G := G) ϖ e (i := i) (j := G.m) (by omega) _⟩
    · by_cases hjm : j < G.m - 1
      · show ∀ (r : Fin (G.rank (G.m, j))) (s : Fin (G.rank (G.m, j + 1))),
          (fill hs (x + a) (y + b) u - fill hs x y u) (Edge.theta G.m j) r s ≠ 0 →
            wt G ϖ e (G.m, j) r = 1 ∧ wt G ϖ e (G.m, j + 1) s = 1
        intro r s hne
        rw [Pi.sub_apply, fill_theta, fill_theta, Matrix.sub_apply, Matrix.transpose_apply,
          Matrix.transpose_apply] at hne
        simp only [downMap, dif_pos hjm, Pi.add_apply, FlatDep.stepPt_add, Matrix.reindex_apply,
          Matrix.submatrix_apply] at hne
        rw [Matrix.add_apply, add_sub_cancel_left] at hne
        obtain ⟨hs1, hr1⟩ := lt_and_lt_of_fromBlocks_frame_ne_zero _ _ _ s r hne
        exact ⟨wt_core ϖ e (G.m, j) hr1, wt_core ϖ e (G.m, j + 1) hs1⟩
      · intro r s _
        exact ⟨wt_end (G := G) ϖ e (i := G.m) (j := j) (by omega) _,
          wt_end (G := G) ϖ e (i := G.m) (j := j + 1) (by omega) _⟩
  by_cases hD : (fill hs (x + a) (y + b) u - fill hs x y u) c r s = 0
  · rw [hD, mul_zero, zero_mul, map_zero]
    exact zero_le'
  · obtain ⟨h1, h2⟩ := key r s hD
    rw [h1, h2]
    simp only [Units.val_one, inv_one, one_mul, mul_one]
    exact FlatDep.fill_sub_le hs ha hb u hc r s

theorem colVar_le {ϖ : kˣ} {e : ℕ} {T : G.Args → ℂ} (hT : G.IsTensor ϖ e (oppositePath G.m) T) (keep : Bool)
    {x : ColArgs G} {y : RowArgs G} {u : Vars G} (hz : moved G keep (dg G ϖ e) T (fill hs x y u) ≠ 0)
    (j : Fin (G.m - 1)) (hj : (j : ℕ) + 2 = G.m) (r : Fin (topRank G (j + 1))) :
    valuation k (((ϖ ^ e : kˣ) : k) * colVar x u j r) ≤ 1 := by
  have hjm : (j : ℕ) < G.m - 1 := by omega
  have hb : Edge.theta G.m j ∈ oppositePath G.m := FlatDep.mem_opp_theta (by omega)
  have e1 := topRank_add hs (j : ℕ)
  have e2 := topRank_add hs ((j : ℕ) + 1)
  have h2 : topRank G j + (G.m - 2 - j + 1) = G.rank (G.m, j) := by omega
  have h1 : topRank G (j + 1) + (G.m - 2 - j) = G.rank (G.m, j + 1) := by omega
  have hm := moved_supp hT keep hz hb (frame h2 (Sum.inr ⟨0, by omega⟩)) (frame h1 (Sum.inl r))
  rw [fill_theta, Matrix.transpose_apply] at hm
  simp only [downMap, dif_pos hjm, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply] at hm
  have hw1 : wt G ϖ e (G.m, (j : ℕ)) (topRank G j) = ϖ ^ e := by
    unfold wt
    rw [if_pos ⟨rfl, by omega⟩]
    simp
  have hw2 : wt G ϖ e (G.m, (j : ℕ) + 1) r = 1 := wt_core ϖ e _ r.isLt
  simp only [frame, Equiv.trans_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, finCongr_apply,
    Fin.coe_cast, Fin.coe_castAdd, Fin.coe_natAdd, add_zero] at hm
  rw [hw1, hw2] at hm
  simp only [Units.val_one, inv_one, mul_one] at hm
  simp only [colVar]
  convert hm using 4
  congr 1
  apply Fin.ext
  show (G.m - 2 - (j : ℕ)) / 2 = 0
  omega

private theorem lt_of_frame_entry_ne_zero_of_inr_zero {p c m : ℕ} {n' : Type} (h : p + c = m) (s : Fin m) (col : n')
    (M : Matrix (Fin p ⊕ Fin c) n' k) (hM : ∀ l col, M (Sum.inr l) col = 0)
    (hne : M ((frame h).symm s) col ≠ 0) : (s : ℕ) < p := by
  rcases hq : (frame h).symm s with q | q
  · exact lt_of_frame_symm_eq_inl h s q hq
  · rw [hq, hM] at hne
    exact absurd rfl hne

theorem shift_wt_le {ϖ : kˣ} (hϖ : IsUnif ϖ) (e : ℕ) (x : ColArgs G) (y : RowArgs G) (u : Vars G) (j₀ : Fin (G.m - 1))
    (hj₀ : (j₀ : ℕ) + 2 = G.m) (q : ℕ) {t s₀ : k} (ht : valuation k t ≤ valuation k s₀)
    {c : Edge} (hc : c ∈ oppositePath G.m) (r : Fin (G.rank c.tgt)) (s : Fin (G.rank c.src)) :
    valuation k ((wt G ϖ e c.tgt r : k) * (fill hs x y (u + FlatLast.shiftVar j₀ q t) - fill hs x y u) c r s *
      ((wt G ϖ e c.src s)⁻¹ : kˣ)) ≤ valuation k s₀ := by
  have key : ∀ (r : Fin (G.rank c.tgt)) (s : Fin (G.rank c.src)),
      (fill hs x y (u + FlatLast.shiftVar j₀ q t) - fill hs x y u) c r s ≠ 0 → wt G ϖ e c.src s = 1 := by
    rcases FlatDep.mem_opp hc with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
    · intro r s _
      exact wt_end (G := G) ϖ e (i := i) (j := G.m) (by omega) _
    · by_cases hjm : j < G.m - 1
      · show ∀ (r : Fin (G.rank (G.m, j))) (s : Fin (G.rank (G.m, j + 1))),
          (fill hs x y (u + FlatLast.shiftVar j₀ q t) - fill hs x y u) (Edge.theta G.m j) r s ≠ 0 →
            wt G ϖ e (G.m, j + 1) s = 1
        intro r s hne
        rw [Pi.sub_apply, fill_theta, fill_theta, Matrix.sub_apply, Matrix.transpose_apply,
          Matrix.transpose_apply] at hne
        simp only [downMap, dif_pos hjm, Matrix.reindex_apply, Matrix.submatrix_apply] at hne
        rw [← Matrix.sub_apply] at hne
        have hlt := lt_of_frame_entry_ne_zero_of_inr_zero _ s _ _ (by
          intro l col
          simp [stepPt, basePt, FlatLast.shiftVar]) hne
        exact wt_core ϖ e (G.m, j + 1) hlt
      · intro r s _
        exact wt_end (G := G) ϖ e (i := G.m) (j := j + 1) (by omega) _
  by_cases hD : (fill hs x y (u + FlatLast.shiftVar j₀ q t) - fill hs x y u) c r s = 0
  · rw [hD, mul_zero, zero_mul, map_zero]
    exact zero_le'
  · rw [key r s hD]
    simp only [inv_one, Units.val_one, mul_one]
    rw [map_mul]
    calc valuation k (wt G ϖ e c.tgt r : k) *
          valuation k ((fill hs x y (u + FlatLast.shiftVar j₀ q t) - fill hs x y u) c r s)
        ≤ 1 * valuation k s₀ :=
          mul_le_mul' (val_wt_le hϖ e _ _)
            (FlatLast.valuation_fill_sub_le hs x y u _ (FlatLast.valuation_shiftVar_le j₀ q ht) c r s)
      _ = valuation k s₀ := one_mul _

variable [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k)

private theorem valuation_sum_colVar_even_le_one {ϖ : kˣ} {e : ℕ} (x a : ColArgs G) (u : Vars G)
    (ha : ∀ j, j < G.m → ∀ r s, valuation k (a j r s) ≤ valuation k ((ϖ ^ e : kˣ) : k))
    (hc : ∀ (j : Fin (G.m - 1)), (j : ℕ) + 2 = G.m → ∀ r,
      valuation k (((ϖ ^ e : kˣ) : k) * colVar x u j r) ≤ 1) :
    valuation k (∑ j : Fin (G.m - 1), if Even (G.m - 2 - ↑j) then
      ∑ r, (if ↑j + 1 < G.m - 1 then 0 else a (↑j + 1) (topLast G (↑j + 1 + 1)) r) * colVar x u j r
      else 0) ≤ 1 := by
  apply Valuation.map_sum_le
  intro j _
  have hjlt := j.isLt
  by_cases hev : Even (G.m - 2 - ↑j)
  · rw [if_pos hev]
    apply Valuation.map_sum_le
    intro r _
    by_cases hj : (j : ℕ) + 1 < G.m - 1
    · rw [if_pos hj, zero_mul, map_zero]
      exact zero_le'
    · have hj2 : (j : ℕ) + 2 = G.m := by omega
      rw [if_neg hj, map_mul]
      have h1 := ha (j + 1) (by omega) (topLast G (↑j + 1 + 1)) r
      have h2 := hc j hj2 r
      rw [map_mul] at h2
      exact le_trans (mul_le_mul' h1 le_rfl) h2
  · rw [if_neg hev, map_zero]
    exact zero_le'

private theorem addChar_neg_add_eq_of_conductor_one (hψ : HasConductor ψ 1) (p E : k) (hE : valuation k E ≤ 1) :
    ψ (-(p + E)) = ψ (-p) := by
  rw [neg_add, AddChar.map_add_eq_mul,
    (hψ 1).mpr (by simp) (-E) (by rw [Valuation.map_neg]; simpa using hE), mul_one]

theorem flat_per {ϖ : kˣ} {e : ℕ} {T : G.Args → ℂ} (hψ : HasConductor ψ 1) (hT : G.IsTensor ϖ e (oppositePath G.m) T)
    (keep : Bool) (x a : ColArgs G) (y b : RowArgs G)
    (ha : ∀ j, j < G.m → ∀ r s, valuation k (a j r s) ≤ valuation k ((ϖ ^ e : kˣ) : k))
    (hb : ∀ i, i < G.m → ∀ r s, valuation k (b i r s) ≤ valuation k ((ϖ ^ e : kˣ) : k)) :
    flatTensor hs ψ ν (moved G keep (dg G ϖ e) T) (x + a) (y + b) = flatTensor hs ψ ν (moved G keep (dg G ϖ e) T) x y := by
  unfold flatTensor
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [flatIntegrand]
  have hper : moved G keep (dg G ϖ e) T (fill hs (x + a) (y + b) u) =
      moved G keep (dg G ϖ e) T (fill hs x y u) :=
    moved_per hT keep _ _ (fun c hc r s => fill_sub_wt_le hs ϖ e ha hb u hc r s)
  rw [hper]
  by_cases hz : moved G keep (dg G ϖ e) T (fill hs x y u) = 0
  · rw [hz, zero_mul, zero_mul]
  · have hE := valuation_sum_colVar_even_le_one x a u ha (fun j hj r => colVar_le hs hT keep hz j hj r)
    rw [FlatDep.phase_add, addChar_neg_add_eq_of_conductor_one ψ hψ _ _ hE]

theorem flat_supp {ϖ : kˣ} {e : ℕ} {T : G.Args → ℂ} (hT : G.IsTensor ϖ e (oppositePath G.m) T) (keep : Bool)
    (x : ColArgs G) (y : RowArgs G) (hne : flatTensor hs ψ ν (moved G keep (dg G ϖ e) T) x y ≠ 0) :
    (∀ j, j < G.m → ∀ r s, (j + 1 = G.m → r ≠ topLast G (j + 1)) → valuation k (x j r s) ≤ 1) ∧
      ∀ i, i < G.m → ∀ r s, valuation k (y i r s) ≤ 1 := by
  have hex : ∃ u, moved G keep (dg G ϖ e) T (fill hs x y u) ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply hne
    unfold flatTensor
    simp [flatIntegrand, hall]
  obtain ⟨u, hu⟩ := hex
  constructor
  · intro j hj r s hr
    have hb := FlatDep.mem_opp_theta (G := G) hj
    have e1 := topRank_add hs j
    have e2 := topRank_add hs (j + 1)
    by_cases hjm : j < G.m - 1
    · have h2 : topRank G j + (G.m - 2 - j + 1) = G.rank (G.m, j) := by omega
      have h1 : topRank G (j + 1) + (G.m - 2 - j) = G.rank (G.m, j + 1) := by omega
      have hm := moved_supp hT keep hu hb (frame h2 (Sum.inl s)) (frame h1 (Sum.inl r))
      rw [fill_theta, Matrix.transpose_apply] at hm
      simp only [downMap, dif_pos hjm, Matrix.reindex_apply, Matrix.submatrix_apply,
        Equiv.symm_apply_apply] at hm
      simp only [frame, Equiv.trans_apply, finSumFinEquiv_apply_left, finCongr_apply,
        Fin.coe_cast, Fin.coe_castAdd] at hm
      rw [wt_core ϖ e (G.m, j) s.isLt, wt_core ϖ e (G.m, j + 1) r.isLt] at hm
      simpa [stepPt, basePt, Free, Kept] using hm
    · have hj1 : j + 1 = G.m := by omega
      have hrne : (r : ℕ) ≠ topRank G (j + 1) - 1 := fun h => hr hj1 (Fin.ext h)
      have hrl : (r : ℕ) < G.rank (G.m, j + 1) := by
        have := r.isLt
        omega
      have hsl : (s : ℕ) < G.rank (G.m, j) := by
        have := s.isLt
        omega
      have hm := moved_supp hT keep hu hb ⟨s, hsl⟩ ⟨r, hrl⟩
      rw [fill_theta, Matrix.transpose_apply] at hm
      simp only [downMap, dif_neg hjm, dif_pos hj1, Matrix.submatrix_apply] at hm
      rw [wt_end (G := G) ϖ e (i := G.m) (j := j) (by omega),
        wt_end (G := G) ϖ e (i := G.m) (j := j + 1) (by omega)] at hm
      simpa using hm
  · intro i hi r s
    have hb : Edge.ex i G.m ∈ oppositePath G.m := by
      simp [oppositePath, hi]
    have hm := moved_supp hT keep hu hb s r
    rw [fill_ex, Matrix.transpose_apply, wt_end (G := G) ϖ e (i := i + 1) (j := G.m) (by omega),
      wt_end (G := G) ϖ e (i := i) (j := G.m) (by omega)] at hm
    simpa using hm

theorem flat_last [ν.IsAddHaarMeasure] {ϖ : kˣ} {e : ℕ} {T : G.Args → ℂ} (hϖ : IsUnif ϖ) (hψ : HasConductor ψ 1)
    (hT : G.IsTensor ϖ e (oppositePath G.m) T) (keep : Bool) (x : ColArgs G) (y : RowArgs G)
    (hF : flatTensor hs ψ ν (moved G keep (dg G ϖ e) T) x y ≠ 0) (j₀ : Fin (G.m - 1)) (hj₀ : (j₀ : ℕ) + 2 = G.m)
    (r : Fin (topRank G ((j₀ : ℕ) + 1))) :
    valuation k (x ((j₀ : ℕ) + 1) (topLast G ((j₀ : ℕ) + 1 + 1)) r) ≤ valuation k (((ϖ ^ e)⁻¹ : kˣ) : k) := by
  obtain ⟨hsc, ht2⟩ := Model.secondCountable_and_t2_local_field (k := k)
  haveI := hsc
  haveI := ht2
  haveI : SigmaFinite ν := inferInstance
  haveI hinv : (varsVol G ν).IsAddRightInvariant := by
    unfold varsVol
    infer_instance
  by_contra hlt
  push_neg at hlt
  set X := x ((j₀ : ℕ) + 1) (topLast G ((j₀ : ℕ) + 1 + 1)) r with hX
  have hnot : X ∉ cball ((1 : kˣ) * (ϖ ^ e)⁻¹) := by
    simp only [cball, Set.mem_setOf_eq, one_mul, not_le]
    exact hlt
  obtain ⟨t, ht, hψt⟩ := hψ.exists_ne_one (ϖ ^ e) hnot
  have hneg : valuation k (-t) ≤ valuation k ((ϖ ^ e : kˣ) : k) := by
    rw [Valuation.map_neg]
    exact ht
  have hshift : flatTensor hs ψ ν (moved G keep (dg G ϖ e) T) x y =
      ((ψ (-(X * -t)) : Circle) : ℂ) * flatTensor hs ψ ν (moved G keep (dg G ϖ e) T) x y := by
    unfold flatTensor
    calc ∫ u, flatIntegrand hs ψ (moved G keep (dg G ϖ e) T) x y u ∂varsVol G ν
        = ∫ u, flatIntegrand hs ψ (moved G keep (dg G ϖ e) T) x y (u + FlatLast.shiftVar j₀ r (-t))
            ∂varsVol G ν := (integral_add_right_eq_self _ _).symm
      _ = ∫ u, ((ψ (-(X * -t)) : Circle) : ℂ) * flatIntegrand hs ψ (moved G keep (dg G ϖ e) T) x y u
            ∂varsVol G ν := by
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
          simp only [flatIntegrand]
          rw [moved_per hT keep (fill hs x y u) (fill hs x y (u + FlatLast.shiftVar j₀ r (-t)))
            (fun c hc r' s' => shift_wt_le hs hϖ e x y u j₀ hj₀ r hneg hc r' s')]
          rw [FlatLast.phase_shift x u j₀ hj₀ r (-t)]
          have hrow : rowVar x u ((j₀ : ℕ) + 1) r = X := by
            unfold rowVar
            rw [dif_neg (by omega)]
          rw [hrow, neg_add, AddChar.map_add_eq_mul, Circle.coe_mul]
          ring
      _ = _ := MeasureTheory.integral_const_mul _ _
  have h1 : ((ψ (-(X * -t)) : Circle) : ℂ) = 1 := (mul_eq_right₀ hF).mp hshift.symm
  apply hψt
  have h3 : -(X * -t) = t * X := by ring
  rw [← h3]
  exact Circle.ext h1

theorem isSBArgs_stair [ν.IsAddHaarMeasure] {ϖ : kˣ} {e : ℕ} {T : G.Args → ℂ} (hm : 2 ≤ G.m) (hϖ : IsUnif ϖ)
    (hψ : HasConductor ψ 1) (hT : G.IsTensor ϖ e (oppositePath G.m) T) (keep : Bool) :
    IsSBArgs G ϖ e (flatTensor hs ψ ν (moved G keep (dg G ϖ e) T)) := by
  have h1 : (1 : ValueGroupWithZero k) ≤ valuation k (((ϖ ^ e)⁻¹ : kˣ) : k) := by
    simpa using val_inv_pow_mono hϖ (Nat.zero_le e)
  refine ⟨(GlobalTheory.T.flatTensor_depends_below_and_small_translation_invariant G hs ψ ν ϖ e T keep _ hϖ hψ hT).1, fun x y a b ha hb => flat_per hs ψ ν hψ hT keep x a y b ha hb,
    fun x y hxy => ⟨fun j hj r s => ?_, fun i hi r s => ((flat_supp hs ψ ν hT keep x y hxy).2 i hi r s).trans h1⟩⟩
  by_cases hr : j + 1 = G.m ∧ r = topLast G (j + 1)
  · obtain ⟨h2, rfl⟩ := hr
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    exact flat_last hs ψ ν hϖ hψ hT keep x y hxy ⟨j, by omega⟩ (by simp only; omega) s
  · exact ((flat_supp hs ψ ν hT keep x y hxy).1 j hj r s fun h h' => hr ⟨h, h'⟩).trans h1

end GlobalTheory.StairDepth

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.DepthUnf GlobalTheory.SumSize GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section SlopeTestRemainingChoices

open ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7}

private theorem val_nat_le_unif (w : Pl D.host.E) {p : ℕ} (hp : (p : 𝓞 D.host.E) ∈ w.asIdeal) :
    valuation (Kw w) (p : Kw w) ≤ valuation (Kw w) (unifAt w : Kw w) := by
  rw [isUnif_unifAt w]
  refine le_uniformizer_iff.2 ((Comparison₂.vEq w).lt_one_iff_lt_one.2 ?_)
  rw [← map_natCast (algebraMap D.host.E (Kw w)), Good.valued_alg, ← map_natCast (algebraMap (𝓞 D.host.E) D.host.E)]
  exact (HeightOneSpectrum.valuation_lt_one_iff_mem w _).2 hp

private theorem exists_depth (P : Finset (Pl D.host.E)) (n : Pl D.host.E → ℕ) : ∃ K : ℕ, 0 < K ∧
    (∀ l B : ℕ, l.Prime → (∀ w ∈ P, (l : 𝓞 D.host.E) ∈ w.asIdeal → n w ≤ B) → padicValNat l K ≤ B) ∧
    ∀ w ∈ P, valuation (Kw w) (K : Kw w) ≤ valuation (Kw w) ((unifAt w ^ n w : (Kw w)ˣ) : Kw w) := by
  classical
  let N : ℕ → ℕ := fun p => (P.filter fun w => Formalism.EigenvalueLevelCeiling.plc w = p).sup n
  have hpr : ∀ p ∈ P.image Formalism.EigenvalueLevelCeiling.plc, p.Prime := fun p hp => by
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 hp
    exact Formalism.EigenvalueLevelCeiling.plc_prime w
  refine ⟨∏ p ∈ P.image Formalism.EigenvalueLevelCeiling.plc, p ^ N p, Finset.prod_pos fun p hp => pow_pos (hpr p hp).pos _, fun l B hl hB => ?_,
    fun w hw => ?_⟩
  · have hN : N l ≤ B := Finset.sup_le fun w hw => by
      obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hw
      exact hB w h1 (h2 ▸ Formalism.EigenvalueLevelCeiling.plc_mem w)
    rw [Nat.padicValNat_def, ← Nat.factorization_def _ hl, Nat.factorization_prod fun p hp => pow_ne_zero _ (hpr p hp).ne_zero,
      Finset.sum_congr rfl fun p hp => (hpr p hp).factorization_pow, Finset.sum_apply']
    simp only [Finsupp.single_apply, Finset.sum_ite_eq']
    split_ifs
    · exact hN
    · exact Nat.zero_le _
  · obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun p => p ^ N p) (Finset.mem_image_of_mem Formalism.EigenvalueLevelCeiling.plc hw)
    have hn : n w ≤ N (Formalism.EigenvalueLevelCeiling.plc w) := Finset.le_sup (f := n) (Finset.mem_filter.2 ⟨hw, rfl⟩)
    have hc1 : valuation (Kw w) (c : Kw w) ≤ 1 := (Valuation.mem_integer_iff _ _).1 (natCast_mem _ c)
    rw [hc, Nat.cast_mul, map_mul]
    refine (mul_le_mul' ?_ hc1).trans ((mul_one _).le.trans (val_pow_anti (isUnif_unifAt w) hn))
    rw [Nat.cast_pow, Units.val_pow_eq_pow_val, map_pow, map_pow]
    exact pow_le_pow_left' (val_nat_le_unif w (Formalism.EigenvalueLevelCeiling.plc_mem w)) _

private theorem frAt_nsmul (w : Pl D.host.E) {a b : ℕ} (β' : GL (Fin b) (Lev.EAf D)) (β : GL (Fin a) (Lev.EAf D)) (K : ℕ)
    (x : Mx D b a) (r : Fin b) (s : Fin a) : frAt w β' β (K • x) r s = (K : Kw w) * frAt w β' β x r s := by
  induction K with
  | zero => simp [frAt, Comparison₂.fr]
  | succ K ih => rw [succ_nsmul, frAt_add, Matrix.add_apply, ih, Nat.cast_succ, add_mul, one_mul]

section Lat

variable {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
  {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {βS : GL (Fin S.rank) (Lev.EAf D)} {βT : GL (Fin T.rank) (Lev.EAf D)}
  {P : Finset (Pl D.host.E)} {n : Pl D.host.E → ℕ} {K : ℕ}

private theorem nsmul_mem_lat (hS : IsSelfDualC S ΛS) (hβS : IsFrame βS ΛS) (hβT : IsFrame βT ΛT) {e : AE D} (he : IsIdemSum e P)
    (hAA : ∀ w ∈ P, ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1)
    (hK : ∀ w ∈ P, valuation (Kw w) (K : Kw w) ≤ valuation (Kw w) ((unifAt w ^ n w : (Kw w)ˣ) : Kw w)) {x : WO S T}
    (hx : IsHalf e x)
    (h : ∀ w ∈ P, ∀ r s, valuation (Kw w) (frAt w βT βS x r s) ≤ valuation (Kw w) (((unifAt w ^ n w)⁻¹ : (Kw w)ˣ) : Kw w)) :
    K • x ∈ latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True := by
  have hx' : IsHalf e (K • x) := fun i j => by
    rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, hx i j]
  refine GlobalTheory.RowLatChi.mem_latO_of_mem_hatMx hS he hAA hx' (GlobalTheory.RowLatChi.mem_hatMx_of_int hβS hβT he hx' fun w hw r s => ?_)
  refine (Comparison₂.vEq w).le_one_iff_le_one.1 ?_
  change valuation (Kw w) (frAt w βT βS (K • x) r s) ≤ 1
  rw [frAt_nsmul, map_mul]
  refine (mul_le_mul' (hK w hw) (h w hw r s)).trans_eq ?_
  rw [← map_mul, Units.mul_inv, map_one]

private theorem nsmul_small (hS : IsSelfDualC S ΛS) (hβS : IsFrame βS ΛS) (hβT : IsFrame βT ΛT) {w : Pl D.host.E}
    (hAA : ∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) {c : ValueGroupWithZero (Kw w)}
    (hK : valuation (Kw w) (K : Kw w) ≤ c) {u : WO S T}
    (hu : u ∈ latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) (r : Fin T.rank) (s : Fin S.rank) :
    valuation (Kw w) (frAt w βT βS (K • u) r s) ≤ c := by
  have h1 : valuation (Kw w) (frAt w βT βS u r s) ≤ 1 :=
    (Comparison₂.vEq w).le_one_iff_le_one.2 (GlobalTheory.RowLatChi.int_of_mem_latO hS hβS hβT w hAA hu r s)
  rw [frAt_nsmul, map_mul]
  exact (mul_le_mul' hK h1).trans_eq (mul_one _)

end Lat

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

private theorem isSBArgs_of_mem_good_places {μ₀ : T} (hL : L.Is μ₀) (S : GridChoice W U) (t : T) (Φ : G.Datum)
    (hde : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q))
    (hc : ∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) {P : Pl D.host.E} (hP : P ∈ G.pl.W0)
    (hl : P ∈ locPl G t) {β : CosFam G t} (hβ : β ∈ S.supp t Φ) :
    IsSBArgs (locGrid G t P) (unifAt P) (depthAt G P) (S.term t Φ β ⟨P, hl⟩).datum := by
  classical
  have hs : 1 ≤ (locGrid G t P).s := one_le_sLen
  have hkeep : keepAt G P = false := by simp [keepAt, hP]
  have hdep : depthAt G P = cosExp G P := by
    obtain ⟨v, hv, rfl⟩ : ∃ v ∈ G.pl.S0, G.pl.w v = P := by simpa [Places.W0] using hP
    obtain ⟨h1, h2⟩ := depthAt_w G hv
    rw [h1, h2]
  have hm2 : 2 ≤ D.R.m := D.R.two_le_m
  have hm : 0 < D.R.m := by omega
  have h00 := ((Good.locGrid_isGood hL G W t hde hc).1 P hl).square 0 hm 0 hm
  haveI := (isUnitVol_unitVol P).1
  have hT := isTensor_Tflip hL W S.B t Φ hde hc hl
  rw [hdep] at hT ⊢
  have hKO : ∀ j, 0 < j → j < (locGrid G t P).m → givenLevel G t P ((locGrid G t P).m, j) = KO (Kw P) _ := by
    intro j hj _
    have key : ∀ i, 0 < i → givenLevel G t P (i, j) = KO _ _ := by
      rintro (_ | i) hi
      · omega
      · obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        rfl
    exact key _ hm
  have hO := oneCoset hs (psiAt W P) (unitVol P) (givenLevel G t P) (Tflip W S.B t Φ P) (unifAt P) (cosExp G P) D.R.m_even
    (isUnif_unifAt P) h00.cond hT hKO
  have hb := hβ ⟨P, hl⟩
  have hb' : β ⟨P, hl⟩ ∈ unfSupport (psiAt W P) (unitVol P) false
      (Reps.through hs (givenLevel G t P) (stair (locGrid G t P) (unifAt P) (cosExp G P))) (Tflip W S.B t Φ P) := by
    have : keepAt G (⟨P, hl⟩ : locPl G t).1 = false := hkeep
    rw [this] at hb
    exact hb
  have hβ' := funext (hO _ hb')
  have h := GlobalTheory.StairDepth.isSBArgs_stair hs (psiAt W P) (unitVol P) hm2 (isUnif_unifAt P) h00.cond hT (keepAt G P)
  rw [← GlobalTheory.StairDepth.elt_eq hs (givenLevel G t P) _ _ hm2, ← hβ'] at h
  exact h

private theorem depthOK_of {μ₀ : T} (hL : L.Is μ₀) (S : GridChoice W U) (t : T) (Φ : G.Datum)
    (hde : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q))
    (hc : ∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) (β : CosFam G t)
    {n : Pl D.host.E → ℕ} (hF : ∀ w : locPl G t, IsSBArgs (locGrid G t w.1) (unifAt w.1) (n w.1) (S.term t Φ β w).datum)
    {K : ℕ} (hK : ∀ w ∈ locPl G t, valuation (Kw w) (K : Kw w) ≤ valuation (Kw w) ((unifAt w ^ n w : (Kw w)ˣ) : Kw w))
    {e : AE D} (he : IsIdemSum e (locPl G t)) : DepthOK S t Φ β e K := by
  have hAA : ∀ w ∈ locPl G t, (∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧
      ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1 := by
    intro w hw
    have hb := Good.badInt_notMem hL hde hc hw
    have h2q := fun h => hb (GlobalTheory.HalfCompare.mem_of_dvd h (Dvd.intro _ rfl))
    have hN := fun h => hb (GlobalTheory.HalfCompare.mem_of_dvd h (Dvd.intro_left _ rfl))
    refine ⟨fun a ha => ?_, ⟨_, GlobalTheory.HostClear.absNorm_mem_AA D, ?_⟩⟩
    · rw [Good.valued_alg]
      exact Good.valuation_le_one_of_mem h2q (Or.inl ha)
    · rw [Good.valued_alg]
      exact Good.valuation_nat hN
  have sT : ∀ j : Fin D.R.m, IsSelfDualC (G.pS (.top t j)) (G.latS (.top t j)) := fun j =>
    (G.isV (X := .top j) j.2.le fun _ e => by cases e).sd
  have sC : ∀ i : Fin D.R.m, IsSelfDualC (G.pS (.chi i D.R.m : Pair T)) (G.latS (.chi i D.R.m : Pair T)) := fun i =>
    isSelfDualC_neg (G.isV (X := .grid (i + 1) D.R.m) ⟨i.2, le_rfl⟩ fun j e => by injection e with h1; omega).sd
  refine ⟨fun x y hx hy hne => ?_, fun x u y v _ _ hu hv => ?_⟩
  · have hw : ∀ w : locPl G t, (S.term t Φ β w).datum (S.colAt t w x) (S.rowAt t w y) ≠ 0 := fun w h0 =>
      hne (Finset.prod_eq_zero (Finset.mem_univ w) h0)
    refine ⟨fun j => nsmul_mem_lat (sT j) (S.βp_is j j.2.le) (S.βp_is (j + 1) j.2) he (fun w hw => (hAA w hw).2) hK (hx j)
        fun w hwP r s => ?_,
      fun i => nsmul_mem_lat (sC i) (S.B.isFrame_β hL i.2 le_rfl) (S.B.isFrame_β hL i.2.le le_rfl) he
        (fun w hw => (hAA w hw).2) hK (hy i) fun w hwP r s => ?_⟩
    · have := ((hF ⟨w, hwP⟩).supp _ _ (hw ⟨w, hwP⟩)).1 j j.2 (Fin.cast (topRank_eq G t w j.2).symm r)
        (Fin.cast (topRank_eq G t w j.2.le).symm s)
      rw [colAt_eq S t w x j.2] at this
      exact this
    · have := ((hF ⟨w, hwP⟩).supp _ _ (hw ⟨w, hwP⟩)).2 i i.2
        (Fin.cast (rank_vertex G t w (X := (i, D.R.m)) ⟨i.2.le, le_rfl⟩).symm r)
        (Fin.cast (rank_vertex G t w (X := (i + 1, D.R.m)) ⟨i.2, le_rfl⟩).symm s)
      rw [rowAt_eq S t w y i.2] at this
      exact this
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [colAt_add, rowAt_add]
    refine (hF w).per _ _ _ _ (fun j hj r s => ?_) (fun i hi r s => ?_)
    · rw [colAt_eq S t w _ hj]
      exact nsmul_small (sT ⟨j, hj⟩) (S.βp_is j hj.le) (S.βp_is (j + 1) hj) (hAA w.1 w.2).1 (hK w.1 w.2) (hu ⟨j, hj⟩).2 _ _
    · rw [rowAt_eq S t w _ hi]
      exact nsmul_small (sC ⟨i, hi⟩) (S.B.isFrame_β hL hi le_rfl) (S.B.isFrame_β hL hi.le le_rfl) (hAA w.1 w.2).1
        (hK w.1 w.2) (hv ⟨i, hi⟩).2 _ _

private theorem depth_main {μ₀ : T} (hL : L.Is μ₀) (S : GridChoice W U) (t : T) (Φ : G.Datum)
    (hde : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q))
    (hc : ∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) {β : CosFam G t} (hβ : β ∈ S.supp t Φ) :
    ∃ K : ℕ, 0 < K ∧ (∀ (w : PlL D) (l : ℕ), l.Prime → (l : 𝓞 D.what₂.LL) ∈ w.asIdeal → Away G t w →
      padicValNat l K ≤ depL G l) ∧ ∀ e, IsIdemSum e (locPl G t) → DepthOK S t Φ β e K := by
  classical
  have hm : 2 ≤ D.R.m := D.R.two_le_m
  have hSB : ∀ w : Pl D.host.E, ∃ n, (w ∈ G.pl.W0 → n = depthAt G w) ∧ ∀ hw : w ∈ locPl G t,
      IsSBArgs (locGrid G t w) (unifAt w) n (S.term t Φ β ⟨w, hw⟩).datum := fun w => by
    by_cases h0 : w ∈ G.pl.W0
    · exact ⟨_, fun _ => rfl, fun hw => isSBArgs_of_mem_good_places hL S t Φ hde hc h0 hw hβ⟩
    by_cases hw : w ∈ locPl G t
    · have hg := (Good.locGrid_isGood hL G W t hde hc).1 w hw
      have h00 := hg.square 0 (by change 0 < D.R.m; omega) 0 (by change 0 < D.R.m; omega)
      haveI := (isUnitVol_unitVol w).1
      obtain ⟨n, hn⟩ := exists_isSBArgs_flat (locGrid G t w) one_le_sLen (psiAt W w) (unitVol w) (unifAt w) (depthAt G w)
        (Tflip W S.B t Φ w) (keepAt G w) ((repsAt G t w).elt (β ⟨w, hw⟩)) hm h00.unif h00.cond
        (isTensor_Tflip hL W S.B t Φ hde hc hw)
      exact ⟨n, fun h => absurd h h0, fun _ => hn⟩
    · exact ⟨0, fun h => absurd h h0, fun h => absurd h hw⟩
  choose n hn0 hn using hSB
  obtain ⟨K, hK0, hKl, hK⟩ := exists_depth (locPl G t) n
  refine ⟨K, hK0, fun w l hl hlw hA => hKl l _ hl fun P hP hlP => ?_,
    fun e he => depthOK_of hL S t Φ hde hc β (fun w => hn w.1 w.2) hK he⟩
  have hW : P ∈ G.pl.W0 := by
    rcases Good.locPl_cases hP with ⟨a, b⟩ | ⟨a, -, b⟩
    · rw [b]
      unfold Places.W0
      convert Finset.mem_image_of_mem _ a
    · exact absurd hlw ((hA P b).resolve_left a l hl hlP)
  rw [hn0 P hW]
  exact Finset.le_sup (f := depthAt G) (Finset.mem_filter.2 ⟨hW, hlP⟩)

end SlopeTestRemainingChoices

theorem _root_.GlobalTheory.T.flatTensor_depth_conditions_away_from_twist : BigC fun {D} _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ => ∀ (t : _) (Φ : ch.G.Datum), ∀ β ∈ ch.S.supp t Φ, ∃ K : ℕ, 0 < K ∧ (∀ (w : PlL D) (l : ℕ), l.Prime → (l : 𝓞 D.what₂.LL) ∈ w.asIdeal → Away ch.G t w → padicValNat l K ≤ depL ch.G l) ∧ ∀ e, IsIdemSum e (locPl ch.G t) → DepthOK ch.S.toGridChoice t Φ β e K := by
  refine ⟨0, fun CF _ => ⟨0, fun ε C _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch _ _ _ t Φ β hβ => ?_⟩⟩⟩
  exact depth_main hS.core.lev ch.S.toGridChoice t Φ (GlobalTheory.RowClaim.Test.pde_ne_q hS) (GlobalTheory.RowClaim.Test.guard hS t) hβ
