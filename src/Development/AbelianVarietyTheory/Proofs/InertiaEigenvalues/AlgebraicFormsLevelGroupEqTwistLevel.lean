module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VacuumTranslatesConjHalfSqNormEqCard
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitSupportedClassScalarMemValuationRing

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraicFormsLevelGroupEqTwistLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraicFormsLevelGroupEqTwistLevel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MtRead
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.MtLev

theorem blockSizes_sub_eq_twoBlock {n : ℕ} (r : ℕ) : (Formalism.L2.DIV.blkOf (n := n) r (n - r)) = Formalism.L2.DIV.blk2 r := by
  funext a
  unfold Formalism.L2.DIV.blkOf Formalism.L2.DIV.blk2
  split_ifs with h
  · rfl
  · have : (a.val - r) / (n - r) = 0 := Nat.div_eq_of_lt (by omega)
    rw [this]

theorem mem_levJ_iff {D : D7} {S T : HSp D} {n : ℕ} (B : Base S T) (t : Twist D Circle) (P : principalLevelFrame.RowPsi S n) (g : GAf D.host.E n) :
    frameEquiv P g ∈ B.levJ t ↔ Lev.finE S (P.ψ g) ∈ Formalism.L2.DIV.lev D.sp.cm S.gram B.F.βS (B.levS t) := Iff.rfl

end GlobalTheory.MtLev

namespace GlobalTheory.MtLev

variable {D : D7} {V : HSp D} {n : ℕ} {hF : D.host.F = maximalRealSubfield D.host.E} {P : principalLevelFrame.RowPsi V n}

theorem loc_zero (hP : IdFrame hF P) (hn : V.rank = n) {κ : GAf D.host.E n} (hκ : κ ∈ ReciprocityTheory.Aut.Umax D.host.E n)
    (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (a c : Fin V.rank) :
    Valued.v (NX.locM s κ (Fin.cast hn a) (Fin.cast hn c)) < 1 ↔
      (Formalism.L2.DIV.redFn 1 s.w (Lev.finE V (P.ψ κ)) : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.DIV.kP s.w)) a c = 0 := by
  have h := ((GlobalTheory.T.frameKeepsMatrices_splitPlace_reduction_local D V n hF P hP hn κ).2 s hκ a c).2 0
  simp only [map_zero, zero_sub, Valuation.map_neg] at h
  exact h

theorem loc_one (hP : IdFrame hF P) (hn : V.rank = n) {κ : GAf D.host.E n} (hκ : κ ∈ ReciprocityTheory.Aut.Umax D.host.E n)
    (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (a : Fin V.rank) :
    Valued.v (NX.locM s κ (Fin.cast hn a) (Fin.cast hn a) - 1) < 1 ↔
      (Formalism.L2.DIV.redFn 1 s.w (Lev.finE V (P.ψ κ)) : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.DIV.kP s.w)) a a = 1 := by
  have h := ((GlobalTheory.T.frameKeepsMatrices_splitPlace_reduction_local D V n hF P hP hn κ).2 s hκ a a).2 1
  simp only [map_one] at h
  rw [Valuation.map_sub_swap] at h
  exact h

theorem cast_surj (hn : V.rank = n) (a : Fin n) : ∃ a' : Fin V.rank, Fin.cast hn a' = a :=
  ⟨Fin.cast hn.symm a, by simp⟩

theorem inParah_iff (hP : IdFrame hF P) (hn : V.rank = n) {κ : GAf D.host.E n} (hκ : κ ∈ ReciprocityTheory.Aut.Umax D.host.E n)
    (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (r : ℕ) :
    NX.InParah s.v r (NX.locM s κ) ↔ Formalism.L2.DIV.redFn 1 s.w (Lev.finE V (P.ψ κ)) ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r) := by
  constructor
  · rintro ⟨-, h⟩ i j hij
    unfold Formalism.L2.DIV.blk2 at hij
    split_ifs at hij with h1 h2 <;> try omega
    exact (loc_zero hP hn hκ s i j).1 (h _ _ (by simpa using h2) (by simpa using h1))
  · intro h
    refine ⟨fun a b => ?_, fun a b ha hb => ?_⟩
    · obtain ⟨a', rfl⟩ := cast_surj hn a
      obtain ⟨b', rfl⟩ := cast_surj hn b
      exact ((GlobalTheory.T.frameKeepsMatrices_splitPlace_reduction_local D V n hF P hP hn κ).2 s hκ a' b').1
    · obtain ⟨a', rfl⟩ := cast_surj hn a
      obtain ⟨b', rfl⟩ := cast_surj hn b
      refine (loc_zero hP hn hκ s a' b').2 (Formalism.L2.DIV.mem_blockTri.1 h a' b' ?_)
      simp only [Fin.coe_cast] at ha hb
      unfold Formalism.L2.DIV.blk2
      rw [if_pos hb, if_neg (by omega)]
      exact Nat.zero_lt_one

end GlobalTheory.MtLev

namespace GlobalTheory.MtLev

variable {D : D7} {V : HSp D} {n : ℕ} {hF : D.host.F = maximalRealSubfield D.host.E} {P : principalLevelFrame.RowPsi V n}

def UT {m : ℕ} {k : Type} [CommRing k] (r : ℕ) (M : Matrix (Fin m) (Fin m) k) : Prop :=
  ∀ a c : Fin m, (a : ℕ) < r → (c : ℕ) < r → (c < a → M a c = 0) ∧ (a = c → M a c = 1)

theorem inLevG_iff (hP : IdFrame hF P) (hn : V.rank = n) {κ : GAf D.host.E n} (hκ : κ ∈ ReciprocityTheory.Aut.Umax D.host.E n)
    (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (r : ℕ) :
    NX.InLevG s.v r (NX.locM s κ) ↔ Formalism.L2.DIV.redFn 1 s.w (Lev.finE V (P.ψ κ)) ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r) ∧
      UT r (Formalism.L2.DIV.redFn 1 s.w (Lev.finE V (P.ψ κ)) : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.DIV.kP s.w)) := by
  unfold NX.InLevG
  refine and_congr (inParah_iff hP hn hκ s r) ⟨fun h a c ha hc => ?_, fun h a b ha hb => ?_⟩
  · have h' := h (Fin.cast hn a) (Fin.cast hn c) (by simpa using ha) (by simpa using hc)
    refine ⟨fun hca => (loc_zero hP hn hκ s a c).1 (h'.1 hca), fun hac => ?_⟩
    subst hac
    exact (loc_one hP hn hκ s a).1 (h'.2 rfl)
  · obtain ⟨a', rfl⟩ := cast_surj hn a
    obtain ⟨b', rfl⟩ := cast_surj hn b
    have h' := h a' b' (by simpa using ha) (by simpa using hb)
    refine ⟨fun hba => (loc_zero hP hn hκ s a' b').2 (h'.1 hba), fun hab => ?_⟩
    have e : a' = b' := by simpa using hab
    subst e
    exact (loc_one hP hn hκ s a').2 (h'.2 rfl)

theorem UT_iff {m r : ℕ} {k : Type} [CommRing k] (hr : r ≤ m) (M : Matrix (Fin m) (Fin m) k) :
    UT r M ↔ ∀ a c : Fin r, (c < a → M (Fin.castLE hr a) (Fin.castLE hr c) = 0) ∧
      (a = c → M (Fin.castLE hr a) (Fin.castLE hr c) = 1) := by
  constructor
  · intro h a c
    have h' := h (Fin.castLE hr a) (Fin.castLE hr c) a.2 c.2
    exact ⟨fun hca => h'.1 hca, fun hac => h'.2 (by rw [hac])⟩
  · intro h a c ha hc
    have h' := h ⟨a, ha⟩ ⟨c, hc⟩
    have ea : Fin.castLE hr ⟨a, ha⟩ = a := Fin.ext rfl
    have ec : Fin.castLE hr ⟨c, hc⟩ = c := Fin.ext rfl
    rw [ea, ec] at h'
    refine ⟨fun hca => h'.1 hca, fun hac => h'.2 (by subst hac; rfl)⟩

end GlobalTheory.MtLev

namespace GlobalTheory.MtLev

theorem rTup_mem_iff (D : D7) (j : Fin D.R.m) (B : Base (Vc D j) (Wc D j)) (t : Twist D Circle)
    (x : GL (Fin (Vc D j).rank) (Lev.EAf D)) (hPg : ∀ PP, PP ∈ B.G.Pg ↔ ∃ kv, PP = NX.pG D kv)
    (iso : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), ZMod (D.host.g kv.1) ≃+* kP (NX.pG D kv))
    (eG : G0g D.nd ≃* G0 B.G.Pg (Wc D j).rank)
    (hiso : ∀ (g : G0g D.nd) kv (h : NX.pG D kv ∈ B.G.Pg) (a c : Fin (Wc D j).rank), (eG g ⟨NX.pG D kv, h⟩).val a c =
      iso kv ((g kv).val (Fin.cast (FWT.rank_Wc j) a) (Fin.cast (FWT.rank_Wc j) c)))
    (hH : ∀ g, eG g ∈ B.G.P.H ↔ g ∈ D.nexp.U)
    (hU : D.nexp.U = NX.Uup (fun kv : (Σ kk : Fin 2, D.nd.PlG kk) => D.host.g kv.1) D.R.r)
    (hblk : ∀ kv, Formalism.L2.DIV.redFn 1 (NX.pG D kv) x ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 (Wc D j).rank)) :
    Formalism.L2.DIV.rTup 1 (B.levS t) x ∈ B.G.P.H ↔ ∀ kv, ∀ a c : Fin (Wc D j).rank,
      (c < a → (Formalism.L2.DIV.redFn 1 (NX.pG D kv) x : Matrix (Fin (Vc D j).rank) (Fin (Vc D j).rank) (kP (NX.pG D kv))) (Fin.castLE B.hr a) (Fin.castLE B.hr c) = 0) ∧
      (a = c → (Formalism.L2.DIV.redFn 1 (NX.pG D kv) x : Matrix (Fin (Vc D j).rank) (Fin (Vc D j).rank) (kP (NX.pG D kv))) (Fin.castLE B.hr a) (Fin.castLE B.hr c) = 1) := by
  set y : G0 B.G.Pg (Wc D j).rank := Formalism.L2.DIV.rTup 1 (B.levS t) x with hy
  have key : ∀ kv (h : NX.pG D kv ∈ B.G.Pg) (a c : Fin (Wc D j).rank),
      ((eG.symm y) kv).val (Fin.cast (FWT.rank_Wc j) a) (Fin.cast (FWT.rank_Wc j) c) =
        (iso kv).symm ((Formalism.L2.DIV.redFn 1 (NX.pG D kv) x : Matrix (Fin (Vc D j).rank) (Fin (Vc D j).rank) (kP (NX.pG D kv))) (Fin.castLE B.hr a) (Fin.castLE B.hr c)) := by
    intro kv h a c
    have e := hiso (eG.symm y) kv h a c
    rw [MulEquiv.apply_symm_apply] at e
    rw [RingEquiv.eq_symm_apply, ← e]
    have e2 : (y ⟨NX.pG D kv, h⟩ : Matrix (Fin (Wc D j).rank) (Fin (Wc D j).rank) (kP (NX.pG D kv))) =
        (Formalism.L2.DIV.upperLeftBlock B.hr (Formalism.L2.DIV.redFn 1 (NX.pG D kv) x) : Matrix (Fin (Wc D j).rank) (Fin (Wc D j).rank) (kP (NX.pG D kv))) := rfl
    rw [e2, Formalism.L2.DIV.upper_block_val_submatrix B.hr (hblk kv)]
    rfl
  have hmem := hH (eG.symm y)
  rw [MulEquiv.apply_symm_apply] at hmem
  refine hmem.trans ?_
  rw [hU, NX.mem_Uup]
  refine forall_congr' fun kv => ?_
  have h : NX.pG D kv ∈ B.G.Pg := (hPg _).2 ⟨kv, rfl⟩
  have hc : ∀ a' : Fin D.R.r, ∃ a : Fin (Wc D j).rank, Fin.cast (FWT.rank_Wc j) a = a' :=
    fun a' => ⟨Fin.cast (FWT.rank_Wc j).symm a', by simp⟩
  constructor
  · rintro ⟨h1, h2⟩ a c
    refine ⟨fun hca => ?_, fun hac => ?_⟩
    · have e : ((eG.symm y) kv).val (Fin.cast (FWT.rank_Wc j) a) (Fin.cast (FWT.rank_Wc j) c) = 0 := h1 hca
      rw [key kv h] at e
      exact (map_eq_zero_iff _ (iso kv).symm.injective).1 e
    · subst hac
      have e := h2 (Fin.cast (FWT.rank_Wc j) a)
      rw [key kv h] at e
      exact (iso kv).symm.injective (by rw [e, map_one])
  · intro H
    refine ⟨fun a' c' hca => ?_, fun a' => ?_⟩
    · obtain ⟨a, rfl⟩ := hc a'
      obtain ⟨c, rfl⟩ := hc c'
      rw [key kv h, (H a c).1 hca, map_zero]
    · obtain ⟨a, rfl⟩ := hc a'
      rw [key kv h, (H a a).2 rfl, map_one]

end GlobalTheory.MtLev

namespace GlobalTheory.MtLev

theorem levMem : ∀ (D : D7) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host)) (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (e : ℤ) (W₀ : Type) [AddCommGroup W₀] [Module (FractionRing (D.ntw.O i)) W₀] (ρ₀ : Representation (FractionRing (D.ntw.O i)) (ReciprocityTheory.Aut.GQ D.host.E D.R.nV) W₀) (τ : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ) (M : NX.MtVReal D i (j.1 + 1) b k Q ψ e W₀ ρ₀ τ) (B : GlobalTheory.ExportSeries.Base (Vc D j) (Wc D j)) (t : Twist D Circle) (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi (Vc D j) D.R.nV), IdFrame hF P → B.F.βS = 1 → (∀ PP, PP ∈ B.G.Pg ↔ ∃ kv, PP = NX.pG D kv) → Function.Injective (NX.pG D) → t.Q = M.QP → B.de.Q = M.DP → ∀ (iso : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), ZMod (D.host.g kv.1) ≃+* kP (NX.pG D kv)) (eG : G0g D.nd ≃* G0 B.G.Pg (Wc D j).rank), (∀ (g : G0g D.nd) kv (h : NX.pG D kv ∈ B.G.Pg) (a c : Fin (Wc D j).rank), (eG g ⟨NX.pG D kv, h⟩).val a c = iso kv ((g kv).val (Fin.cast (FWT.rank_Wc j) a) (Fin.cast (FWT.rank_Wc j) c))) → (∀ g, eG g ∈ B.G.P.H ↔ g ∈ D.nexp.U) → D.nexp.U = NX.Uup (fun kv : (Σ kk : Fin 2, D.nd.PlG kk) => D.host.g kv.1) D.R.r → ∀ g, g ∈ M.J ↔ frameEquiv P g ∈ B.levJ t := by
  intro D i j b k Q ψ e W₀ _ _ ρ₀ τ M B t hF P hP hβ hPg hinj htQ hdQ iso eG hiso hH hU g
  classical
  obtain ⟨hn, -⟩ := id hP
  have hrW : (Wc D j).rank = D.R.r := FWT.rank_Wc j
  have hSt := (GlobalTheory.T.frameKeepsMatrices_splitPlace_reduction_local D (Vc D j) D.R.nV hF P hP hn g).1
  have hUA := GlobalTheory.LevSplit.finE_mem_UA (Vc D j) (P.ψ g)
  have levG_iff : ∀ (hU' : g ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV) kv,
      NX.InLevG (M.sp (NX.pG D kv)).v D.R.r (NX.locM (M.sp (NX.pG D kv)) g) ↔
        Formalism.L2.DIV.redFn 1 (NX.pG D kv) (Lev.finE (Vc D j) (P.ψ g)) ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 (Wc D j).rank) ∧
        UT (Wc D j).rank (Formalism.L2.DIV.redFn 1 (NX.pG D kv) (Lev.finE (Vc D j) (P.ψ g)) :
          Matrix (Fin (Vc D j).rank) (Fin (Vc D j).rank) (kP (NX.pG D kv))) := by
    intro hU' kv
    have h := inLevG_iff hP hn hU' (M.sp (NX.pG D kv)) D.R.r
    rw [M.sp_w _ (Or.inr (Or.inr ⟨kv, rfl⟩))] at h
    rw [h, hrW]
  have par_iff : ∀ (hU' : g ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV) PP, (PP ∈ M.QP ∨ PP ∈ M.DP) →
      (NX.InParah (M.sp PP).v D.R.r (NX.locM (M.sp PP) g) ↔
        Formalism.L2.DIV.redFn 1 PP (Lev.finE (Vc D j) (P.ψ g)) ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 (Wc D j).rank)) := by
    intro hU' PP hPP
    have h := inParah_iff hP hn hU' (M.sp PP) D.R.r
    rw [M.sp_w _ (hPP.elim Or.inl (fun h => Or.inr (Or.inl h)))] at h
    rw [h, hrW]
  have hblkOf : Formalism.L2.DIV.blkOf (n := (Vc D j).rank) (Wc D j).rank ((Vc D j).rank - (Wc D j).rank) =
      Formalism.L2.DIV.blk2 (Wc D j).rank := blockSizes_sub_eq_twoBlock _
  rw [M.J_mem, mem_levJ_iff, hβ, Formalism.L2.DIV.mem_lev, Formalism.L2.DIV.mem_parLev]
  constructor
  · rintro ⟨hU', hG, hQ, hD⟩
    have hGk := fun kv => (levG_iff hU' kv).1 (hG kv)
    have hblk : ∀ kv, Formalism.L2.DIV.redFn 1 (NX.pG D kv) (Lev.finE (Vc D j) (P.ψ g)) ∈
        Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 (Wc D j).rank) := fun kv => (hGk kv).1
    refine ⟨⟨hUA, hSt.1 hU', fun PP hPP => ?_, fun PP hPP => ?_⟩, ?_⟩
    · obtain ⟨kv, rfl⟩ := (hPg PP).1 hPP
      change _ ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf (Wc D j).rank ((Vc D j).rank - (Wc D j).rank))
      rw [hblkOf]
      exact hblk kv
    · change PP ∈ B.de.Q ∪ t.Q at hPP
      rw [hdQ, htQ] at hPP
      rcases Finset.mem_union.1 hPP with h | h
      · exact (par_iff hU' PP (Or.inr h)).1 (hD PP h)
      · exact (par_iff hU' PP (Or.inl h)).1 (hQ PP h)
    · exact (rTup_mem_iff D j B t _ hPg iso eG hiso hH hU hblk).2 fun kv => (UT_iff B.hr _).1 (hGk kv).2
  · rintro ⟨⟨-, hSt', hPg', hQ'⟩, hR⟩
    have hU' := hSt.2 hSt'
    have hblk : ∀ kv, Formalism.L2.DIV.redFn 1 (NX.pG D kv) (Lev.finE (Vc D j) (P.ψ g)) ∈
        Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 (Wc D j).rank) := fun kv => by
      have h := hPg' (NX.pG D kv) ((hPg _).2 ⟨kv, rfl⟩)
      change _ ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf (Wc D j).rank ((Vc D j).rank - (Wc D j).rank)) at h
      rwa [hblkOf] at h
    have hR' := (rTup_mem_iff D j B t _ hPg iso eG hiso hH hU hblk).1 hR
    have hQm : ∀ PP, PP ∈ M.QP ∨ PP ∈ M.DP → PP ∈ (B.levS t).Q := fun PP h => by
      change PP ∈ B.de.Q ∪ t.Q
      rw [hdQ, htQ]
      exact h.elim (Finset.mem_union_right _) (Finset.mem_union_left _)
    refine ⟨hU', fun kv => (levG_iff hU' kv).2 ⟨hblk kv, (UT_iff B.hr _).2 (hR' kv)⟩,
      fun PP hPP => (par_iff hU' PP (Or.inl hPP)).2 (hQ' PP (hQm PP (Or.inl hPP))),
      fun PP hPP => (par_iff hU' PP (Or.inr hPP)).2 (hQ' PP (hQm PP (Or.inr hPP)))⟩

end GlobalTheory.MtLev
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraicFormsLevelGroupEqTwistLevelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MtRead
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicForms_levelGroup_eq_twistLevel : ∀ (D : D7) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host)) (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (e : ℤ) (W₀ : Type) [AddCommGroup W₀] [Module (FractionRing (D.ntw.O i)) W₀] (ρ₀ : Representation (FractionRing (D.ntw.O i)) (ReciprocityTheory.Aut.GQ D.host.E D.R.nV) W₀) (τ : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ) (M : NX.MtVReal D i (j.1 + 1) b k Q ψ e W₀ ρ₀ τ) (B : GlobalTheory.ExportSeries.Base (Vc D j) (Wc D j)) (t : Twist D Circle) (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi (Vc D j) D.R.nV), IdFrame hF P → B.F.βS = 1 → (∀ PP, PP ∈ B.G.Pg ↔ ∃ kv, PP = NX.pG D kv) → Function.Injective (NX.pG D) → t.Q = M.QP → B.de.Q = M.DP → ∀ (iso : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), ZMod (D.host.g kv.1) ≃+* kP (NX.pG D kv)) (eG : G0g D.nd ≃* G0 B.G.Pg (Wc D j).rank), (∀ (g : G0g D.nd) kv (h : NX.pG D kv ∈ B.G.Pg) (a c : Fin (Wc D j).rank), (eG g ⟨NX.pG D kv, h⟩).val a c = iso kv ((g kv).val (Fin.cast (FWT.rank_Wc j) a) (Fin.cast (FWT.rank_Wc j) c))) → (∀ g, eG g ∈ B.G.P.H ↔ g ∈ D.nexp.U) → D.nexp.U = NX.Uup (fun kv : (Σ kk : Fin 2, D.nd.PlG kk) => D.host.g kv.1) D.R.r → ∀ g, g ∈ M.J ↔ frameEquiv P g ∈ B.levJ t := by
  first | exact @GlobalTheory.MtLev.levMem | exact GlobalTheory.MtLev.levMem | (intros; apply GlobalTheory.MtLev.levMem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlipScalarMemCoefficientRingAuxiliaryLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlipScalarMemCoefficientRingAuxiliaryLevel
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.FlipScalUnit

open Formalism.L2.Host

theorem locK_eq_val_zpow {L : Type} [Field L] [NumberField L] (χ : HChar L) (R : HeightOneSpectrum (𝓞 L))
    (hR : χ.UnrAt R) (m : Lˣ) : χ.locK R m = χ.val R ^ ordF R m := by
  set N := ordF R m with hN
  set u : Lˣ := m * (unif R ^ N)⁻¹ with hu
  have hmu : m = u * unif R ^ N := by rw [hu, inv_mul_cancel_right]
  have hPv : R.valuation L (m : L) = WithZero.exp (-N) := by
    have h0 : R.valuation L (m : L) ≠ 0 := by simp
    rw [hN, ordF, neg_neg]
    exact (WithZero.exp_log h0).symm
  have hatFin : ∀ (x : Lˣ), Valued.v ((atFin R x : (R.adicCompletion L)ˣ) : R.adicCompletion L) = R.valuation L (x : L) :=
    fun x => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' R (x : L)
  have hunit : IsUnitAt R (atFin R u) := by
    have h1 := unif_spec R
    unfold IsUnifAt at h1
    unfold IsUnitAt
    rw [hu, map_mul, map_inv, map_zpow, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, map_mul,
      map_inv₀, map_zpow₀, h1, hatFin, hPv, ← WithZero.exp_zsmul, ← WithZero.exp_neg, ← WithZero.exp_add]
    simp
  have h1 : χ.locK R u = 1 := hR _ hunit
  calc χ.locK R m = χ.locK R (u * unif R ^ N) := by rw [← hmu]
    _ = χ.val R ^ N := by rw [map_mul, map_zpow, h1, one_mul]; rfl


open Formalism.L2.JoinChr in
set_option maxHeartbeats 800000 in
theorem char_flipDet {D : D7} (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E) (hc : ChrEq c χ)
    (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D) (he : IsIdemSum e T) (m : D.host.Eˣ) (x : (AE D)ˣ)
    (hx : (x : AE D) * (e * incA D (m : D.host.E) + (1 - e)) = 1) :
    ((c x : Circle) : ℂ) = ∏ R ∈ T, ((χ.locK R m⁻¹ : ℂˣ) : ℂ) := by
  classical
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D ι h1 h2
    (GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3) c χ hc
  have hinf : infPart D (x : AE D) = 1 := by
    have h0 := congrArg (infPart D) hx
    simp only [map_mul, map_add (f := _), map_sub, map_one, GlobalTheory.PlaceVec.idemSum_infPart he, zero_mul, zero_add, sub_zero,
      mul_one] at h0
    exact h0
  obtain ⟨⟨es, hes, hsum⟩, -⟩ := he
  obtain ⟨ev, hev⟩ : ∃ ev : ∀ R : HeightOneSpectrum (𝓞 D.host.E), AE D →+* R.adicCompletion D.host.E,
      ∀ R z, ev R z = GlobalTheory.CharLocProd.evalAt R (ι (finPart D z)) :=
    ⟨fun R => (GlobalTheory.CharLocProd.evalAt R).comp ((ι : _ →+* _).comp (finPart D)), fun _ _ => rfl⟩
  have hidem : ∀ Q ∈ T, ev Q (es Q) = 1 ∧ ∀ R, R ≠ Q → ev R (es Q) = 0 := by
    intro Q hQ
    simp only [hev]
    refine GlobalTheory.TameSplitChar.idem_apply _ (by rw [← RingEquiv.map_mul, ← RingHom.map_mul, (hes Q hQ).1.1]) Q fun y hy => ?_
    refine ((hes Q hQ).2 y hy).trans (not_congr ((h2 _).trans ?_))
    rw [RingHom.map_mul, RingEquiv.map_mul, show finPart D (incA D ((y : D.host.E)⁻¹)) =
      (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] ((y : D.host.E)⁻¹) from rfl, h1]
    rfl
  have heT : ∀ R ∈ T, ev R e = 1 := by
    intro R hR
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsum, map_sum, Finset.sum_eq_single R, (hidem R hR).1]
    · intro Q hQ hne; exact (hidem Q hQ).2 R hne.symm
    · intro h; exact absurd hR h
  have heT' : ∀ R, R ∉ T → ev R e = 0 := by
    intro R hR
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsum, map_sum]
    exact Finset.sum_eq_zero fun Q hQ => (hidem Q hQ).2 R fun h => hR (h ▸ hQ)
  have hinc : ∀ R (k : D.host.E), ev R (incA D k) = algebraMap D.host.E (R.adicCompletion D.host.E) k := by
    intro R k
    rw [hev, show finPart D (incA D k) = (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] k from rfl, h1,
      GlobalTheory.CharLocProd.evalAt_algebraMap]
  have hxT : ∀ R ∈ T, ev R x = algebraMap D.host.E (R.adicCompletion D.host.E) ((m⁻¹ : D.host.Eˣ) : D.host.E) := by
    intro R hR
    have h0 := congrArg (ev R) hx
    simp only [map_mul, map_add (f := _), map_sub, map_one, heT R hR, one_mul, sub_self, add_zero, hinc] at h0
    rw [eq_inv_of_mul_eq_one_left h0, Units.val_inv_eq_inv_val, map_inv₀]
  have hxT' : ∀ R, R ∉ T → ev R x = 1 := by
    intro R hR
    have h0 := congrArg (ev R) hx
    simp only [map_mul, map_add (f := _), map_sub, map_one, heT' R hR, zero_mul, zero_add, sub_zero, mul_one] at h0
    exact h0
  have hfin : {R : HeightOneSpectrum (𝓞 D.host.E) | R.asIdeal ∣ Ideal.span {(N : 𝓞 D.host.E)}}.Finite :=
    Ideal.finite_factors (by simpa [Ideal.span_singleton_eq_bot] using hN.ne')
  have key := hprod x hinf (T ∪ hfin.toFinset) (fun R => if R ∈ T then m⁻¹ else 1) ?_ ?_
  rotate_left
  · intro R _
    change Valued.v (GlobalTheory.CharLocProd.evalAt R (ι (finPart D x))) = _ ∧
      Valued.v (GlobalTheory.CharLocProd.evalAt R (ι (finPart D x)) - _) ≤ _
    rw [← hev]
    by_cases hR : R ∈ T
    · simp only [if_pos hR]
      rw [hxT R hR, sub_self, map_zero, GlobalTheory.CharLocProd.val_algebraMap]
      exact ⟨rfl, zero_le'⟩
    · simp only [if_neg hR]
      rw [hxT' R hR, Units.val_one, map_one, map_one, map_one, sub_self, map_zero]
      exact ⟨rfl, zero_le'⟩
  · intro R hR
    rw [Finset.mem_union, not_or] at hR
    change Valued.v (GlobalTheory.CharLocProd.evalAt R (ι (finPart D x))) = _ ∧ _
    rw [← hev, hxT' R hR.1, map_one]
    exact ⟨rfl, fun h => hR.2 (hfin.mem_toFinset.2 (Ideal.dvd_span_singleton.2 h))⟩
  rw [key, ← Finset.prod_subset Finset.subset_union_left
    (fun R _ hR => by rw [if_neg hR, map_one, Units.val_one])]
  exact Finset.prod_congr rfl fun R hR => by rw [if_pos hR]

end GlobalTheory.FlipScalUnit


open GlobalTheory.FlipScalUnit in
set_option maxHeartbeats 1600000 in
theorem GlobalTheory.LevelSeries.flipScal_mem_valRing_of_unit : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → Odd W.rank → ∀ (χ : Formalism.L2.Host.HChar D.host.E) (M₀ l pd : ℕ), ChiData χW χ M₀ → l.Prime → Nat.Coprime pd M₀ → Nat.Coprime pd l → Nat.Coprime pd (GlobalTheory.Tow.badN D) → ∀ (k : Type) [Field k] [NumberField k] (σ : k →+* ℂ) (la : HeightOneSpectrum (𝓞 k)) (O : Subring ℂ), ((l : ℕ) : 𝓞 k) ∈ la.asIdeal → ValRing σ la O → ConjIn D σ → χ.ValuesIn (-1 / 2) σ → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (eT : AE D) (x : (AE D)ˣ), IsIdemSum eT T → (∀ PP ∈ T, ((pd : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → IsFlipDet V eT pd x → flipScal χW V W T pd x ∈ O := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hv hodd χ M₀ l pd hχ hl hpM hpl hpbad k _ _ σ la O hla hVR hConj hVI T eT x hT
    hpT hx
  classical
  have hpair := hv.1
  have hpd0 : pd ≠ 0 := by
    rintro rfl
    exact hl.one_lt.ne' ((Nat.coprime_zero_left l).1 hpl)
  have hnot : ∀ (a b : ℕ), Nat.Coprime a b → ∀ R : HeightOneSpectrum (𝓞 D.host.E),
      ((a : ℕ) : 𝓞 D.host.E) ∈ R.asIdeal → ((b : ℕ) : 𝓞 D.host.E) ∉ R.asIdeal := by
    intro a b hab R ha hb
    obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hab
    have h1 : (((u * a + v * b : ℤ)) : 𝓞 D.host.E) = 1 := by rw [huv]; simp
    apply R.isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← h1]
    push_cast
    exact add_mem (Ideal.mul_mem_left _ _ ha) (Ideal.mul_mem_left _ _ hb)
  have hu : ∀ R ∈ T, χ.UnrAt R := fun R hR => hχ.2.1 R (hnot pd M₀ hpM R (hpT R hR))
  have hlR : ∀ R ∈ T, ((l : ℕ) : 𝓞 D.host.E) ∉ R.asIdeal := fun R hR => hnot pd l hpl R (hpT R hR)
  have hO : ∀ m : ℕ, Nat.Coprime m l → ((m : ℂ))⁻¹ ∈ O := fun m hm => by
    have h1 := hVR ((m : k)⁻¹) (by rw [map_inv₀, GlobalTheory.ScalarUnit.val_natCast la hla hm, inv_one])
    simpa using h1
  letI : Algebra k ℂ := σ.toAlgebra
  obtain ⟨A, hA⟩ := ReciprocityTheory.Gal.exists_valuationSubring_over (Ω := ℂ) la
  have hA' : ∀ x : 𝓞 k, A.valuation (σ (x : k)) < 1 ↔ x ∈ la.asIdeal := hA
  have hpA : (l : ℂ) ∈ A.nonunits := by
    rw [ValuationSubring.mem_nonunits_iff]
    have h1 := (hA' (l : 𝓞 k)).2 hla
    simpa using h1
  choose bW hbW using hpair.expW
  have hval : ∀ R ∈ T, ((χ.val R : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm R.asIdeal) : ℝ) : ℂ) ∈ O := by
    intro R hR
    obtain ⟨y, hy⟩ := hVI R (hu R hR)
    have hy' : σ y = ((χ.val R : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm R.asIdeal) : ℝ) : ℂ) := by
      rw [hy, Formalism.L2.Host.HChar.valTw, GlobalTheory.LevelSeriesScal.natCast_cpow_half]
    obtain ⟨h1, -⟩ := GlobalTheory.LevelSeriesScal.val_mul_sqrt_unit D χW χ hχ.1 _ hbW l A hl hpA R (hlR R hR)
    rw [← hy'] at h1
    have hy0 : la.valuation k y ≤ 1 :=
      GlobalTheory.LevelSeriesScal.val_le_one_of_mem σ la A hA' y ((A.valuation_le_one_iff _).2 h1)
    exact hy' ▸ hVR y hy0
  have hNl : ∀ R ∈ T, Nat.Coprime (Ideal.absNorm R.asIdeal) l := by
    intro R hR
    have hle : Ideal.span {((pd : ℕ) : 𝓞 D.host.E)} ≤ R.asIdeal := (Ideal.span_singleton_le_iff_mem _).2 (hpT R hR)
    have hd := Ideal.absNorm_dvd_absNorm_of_le hle
    rw [Ideal.absNorm_span_singleton, ← map_natCast (algebraMap ℤ (𝓞 D.host.E)) pd, Algebra.norm_algebraMap,
      Int.natAbs_pow, Int.natAbs_natCast] at hd
    exact Nat.Coprime.coprime_dvd_left hd (Nat.Coprime.pow_left _ hpl)
  have hN0 : ∀ R : HeightOneSpectrum (𝓞 D.host.E), Ideal.absNorm R.asIdeal ≠ 0 := fun R h =>
    R.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  set mU : D.host.Eˣ := Units.mk0 ((pd : ℕ) : D.host.E) (by exact_mod_cast hpd0) with hmU
  set nR : HeightOneSpectrum (𝓞 D.host.E) → ℕ := fun R =>
    (Associates.mk R.asIdeal).count (Associates.mk (Ideal.span {((pd : ℕ) : 𝓞 D.host.E)})).factors with hnR
  have hord : ∀ R : HeightOneSpectrum (𝓞 D.host.E), Formalism.L2.Host.ordF R mU = (nR R : ℤ) := by
    intro R
    have h0 : ((pd : ℕ) : 𝓞 D.host.E) ≠ 0 := by exact_mod_cast hpd0
    have e1 : ((mU : D.host.Eˣ) : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E ((pd : ℕ) : 𝓞 D.host.E) := by
      rw [hmU, Units.val_mk0, map_natCast]
    unfold Formalism.L2.Host.ordF
    rw [e1, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_def, if_neg h0, WithZero.log_exp,
      neg_neg]
  have hx' : (x : AE D) * (eT * incA D ((mU ^ V.rank : D.host.Eˣ) : D.host.E) + (1 - eT)) = 1 := by
    have h := hx
    unfold IsFlipDet at h
    rwa [Units.val_pow_eq_pow_val, map_pow, hmU, Units.val_mk0, map_natCast]
  have hcx := char_flipDet χW χ hχ.1 T eT hT (mU ^ V.rank) x hx'
  have hcx' : ((χW x : Circle) : ℂ) = ∏ R ∈ T, (((χ.val R : ℂˣ) : ℂ) ^ (nR R * V.rank))⁻¹ := by
    rw [hcx]
    refine Finset.prod_congr rfl fun R hR => ?_
    rw [map_inv, map_pow, locK_eq_val_zpow χ R (hu R hR), hord R, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
      zpow_natCast, Units.val_pow_eq_pow_val, ← pow_mul]
  have hsq : Real.sqrt ((flipIdx V W T pd : ℕ) : ℝ) =
      ∏ R ∈ T, Real.sqrt (Ideal.absNorm R.asIdeal) ^ (nR R * V.rank * W.rank) := by
    have hnn : 0 ≤ ∏ R ∈ T, Real.sqrt (Ideal.absNorm R.asIdeal) ^ (nR R * V.rank * W.rank) :=
      Finset.prod_nonneg fun _ _ => pow_nonneg (Real.sqrt_nonneg _) _
    rw [← Real.sqrt_sq hnn]
    congr 1
    unfold flipIdx
    rw [← Finset.prod_pow]
    push_cast
    refine Finset.prod_congr rfl fun R _ => ?_
    unfold HeightOneSpectrum.maxPowDividing
    have hsN : Real.sqrt (Ideal.absNorm R.asIdeal : ℝ) ^ 2 = (Ideal.absNorm R.asIdeal : ℝ) :=
      Real.sq_sqrt (Nat.cast_nonneg _)
    rw [map_pow, Nat.cast_pow]
    conv_lhs => rw [← hsN]
    simp only [hnR, ← pow_mul]
    ring_nf
  obtain ⟨s, hs⟩ := hodd
  have hfac : flipScal χW V W T pd x = ∏ R ∈ T, ((((χ.val R : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm R.asIdeal) : ℝ) : ℂ)) ^
      (nR R * V.rank) * (((Ideal.absNorm R.asIdeal ^ (nR R * V.rank * (s + 1)) : ℕ) : ℂ))⁻¹) := by
    unfold flipScal
    rw [hcx', hsq, ← Finset.prod_inv_distrib, Complex.ofReal_prod, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun R _ => ?_
    have hs0 : ((Real.sqrt (Ideal.absNorm R.asIdeal) : ℝ) : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero, Real.sqrt_ne_zero']
      exact_mod_cast Nat.pos_of_ne_zero (hN0 R)
    have h2 : ((Real.sqrt (Ideal.absNorm R.asIdeal) : ℝ) : ℂ) ^ 2 = ((Ideal.absNorm R.asIdeal : ℕ) : ℂ) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      push_cast
      rfl
    rw [inv_inv, Complex.ofReal_pow, Nat.cast_pow, ← h2, hs, mul_pow, ← pow_mul]
    field_simp
    ring
  rw [hfac]
  exact prod_mem fun R hR => O.mul_mem (O.pow_mem (hval R hR) _) (hO _ (Nat.Coprime.pow_left _ (hNl R hR)))
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlipScalarMemCoefficientRingAuxiliaryLevelStatement
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flipScalar_mem_coefficientRing_auxiliaryLevel : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → Odd W.rank → ∀ (χ : Formalism.L2.Host.HChar D.host.E) (M₀ l pd : ℕ), ChiData χW χ M₀ → l.Prime → Nat.Coprime pd M₀ → Nat.Coprime pd l → Nat.Coprime pd (GlobalTheory.Tow.badN D) → ∀ (k : Type) [Field k] [NumberField k] (σ : k →+* ℂ) (la : HeightOneSpectrum (𝓞 k)) (O : Subring ℂ), ((l : ℕ) : 𝓞 k) ∈ la.asIdeal → ValRing σ la O → ConjIn D σ → χ.ValuesIn (-1 / 2) σ → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (eT : AE D) (x : (AE D)ˣ), IsIdemSum eT T → (∀ PP ∈ T, ((pd : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → IsFlipDet V eT pd x → flipScal χW V W T pd x ∈ O := by
  first | exact @GlobalTheory.LevelSeries.flipScal_mem_valRing_of_unit | exact GlobalTheory.LevelSeries.flipScal_mem_valRing_of_unit | (intros; apply GlobalTheory.LevelSeries.flipScal_mem_valRing_of_unit <;> assumption)
end
end
