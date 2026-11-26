module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPeriodGroupPointLiftingRowGroupLocalElemen

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TiltedPointsCoveredByRepresentativeCells
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLocalLatticeMatricesInv
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLocalLatticeMatricesInv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.RowVal

theorem hasLoc_inv : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (t : T) (B : Frames G) {j : ℕ}
    (hj : j ≤ D.R.m) (x : GA D (G.V (.grid D.R.m j)))
    (g : ∀ w : locPl G t, GL (Fin ((locGrid G t w.1).rank (D.R.m, j))) (Kw w.1)), HasLoc t B hj x g → HasLoc t B hj x⁻¹ (fun w => (g w)⁻¹) := by
  intro D T L sc G t B j hj x g ⟨e, he, hs, hg⟩
  refine ⟨e, he, ?_, fun w => by rw [map_inv, map_inv, hg w]⟩
  intro i k
  set c := e + Formalism.L2.Theta.cA D e
  have hinv : Formalism.L2.Theta.mt _ x⁻¹ * Formalism.L2.Theta.mt _ x = 1 := by
    simp [Formalism.L2.Theta.mt, map_inv]
  have key : Formalism.L2.Theta.mt _ x⁻¹ - 1 = -(Formalism.L2.Theta.mt _ x⁻¹ * (Formalism.L2.Theta.mt _ x - 1)) := by
    rw [Matrix.mul_sub, hinv, Matrix.mul_one]; abel
  rw [key, Matrix.neg_apply, Matrix.mul_apply, mul_neg, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_left_comm, hs l k]

end GlobalTheory.RowVal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLocalLatticeMatricesInvStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasLocalLatticeMatrices_inv : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (t : T) (B : Frames G) {j : ℕ}
    (hj : j ≤ D.R.m) (x : GA D (G.V (.grid D.R.m j)))
    (g : ∀ w : locPl G t, GL (Fin ((locGrid G t w.1).rank (D.R.m, j))) (Kw w.1)), HasLoc t B hj x g → HasLoc t B hj x⁻¹ (fun w => (g w)⁻¹) := by
  first | exact @GlobalTheory.RowVal.hasLoc_inv | exact GlobalTheory.RowVal.hasLoc_inv | (intros; apply GlobalTheory.RowVal.hasLoc_inv <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLocalLatticeMatricesMul
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLocalLatticeMatricesMul
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.RowVal

theorem isIdemSum_unique {D : D7} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} {e e' : AE D}
    (he : Formalism.IndefR.Datum.IsIdemSum e P) (he' : Formalism.IndefR.Datum.IsIdemSum e' P) : e = e' := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  obtain ⟨⟨es', hes', rfl⟩, -⟩ := he'
  exact Finset.sum_congr rfl fun PP hPP =>
    Formalism.IndefR.Fin.idemAt_eq_split (Formalism.IndefR.Fin.idemAt_split (hes PP hPP)) (hes PP hPP) (hes' PP hPP)

theorem suppAt_mul_of {D : D7} {V : HSp D} {e : AE D} {a b : GA D V} (ha : SuppAt e V a) (hb : SuppAt e V b) :
    SuppAt e V (a * b) := by
  intro i j
  have hab : mt V (a * b) = mt V a * mt V b := rfl
  have hm : mt V (a * b) - 1 = (mt V a - 1) * mt V b + (mt V b - 1) := by
    rw [hab]; noncomm_ring
  rw [hm, Matrix.add_apply, Matrix.mul_apply, mul_add, Finset.mul_sum, hb i j]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← mul_assoc, ha i k]

theorem hasLoc_mul : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (t : T) (B : Frames G) {j : ℕ}
    (hj : j ≤ D.R.m) (x y : GA D (G.V (.grid D.R.m j)))
    (g g' : ∀ w : locPl G t, GL (Fin ((locGrid G t w.1).rank (D.R.m, j))) (Kw w.1)), HasLoc t B hj x g → HasLoc t B hj y g' → HasLoc t B hj (x * y) (fun w => g w * g' w) := by
  intro D T L sc G t B j hj x y g g' ⟨e, he, hs, hg⟩ ⟨e', he', hs', hg'⟩
  rw [isIdemSum_unique he' he] at hs'
  refine ⟨e, he, suppAt_mul_of hs hs', fun w => ?_⟩
  rw [map_mul, map_mul, hg w, hg' w]

end GlobalTheory.RowVal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLocalLatticeMatricesMulStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasLocalLatticeMatrices_mul : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (t : T) (B : Frames G) {j : ℕ}
    (hj : j ≤ D.R.m) (x y : GA D (G.V (.grid D.R.m j)))
    (g g' : ∀ w : locPl G t, GL (Fin ((locGrid G t w.1).rank (D.R.m, j))) (Kw w.1)), HasLoc t B hj x g → HasLoc t B hj y g' → HasLoc t B hj (x * y) (fun w => g w * g' w) := by
  first | exact @GlobalTheory.RowVal.hasLoc_mul | exact GlobalTheory.RowVal.hasLoc_mul | (intros; apply GlobalTheory.RowVal.hasLoc_mul <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TiltedPointsCoveredByRepresentativeCells
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.RowVal

theorem eltAt {k : Type} [Field k] {Gr : GlobalTheory.SplitFlip.Grid k} {hs : 1 ≤ Gr.s} {J : Gr.Level} (ρ : Reps hs J)
    (β : Cosets hs J) (i : ℕ) (hi : i < Gr.m - 2) : ρ.elt β (Gr.m, i + 1) = ρ.rep ⟨i, hi⟩ (β ⟨i, hi⟩) := by
  rw [Reps.elt, onColumn_apply]
  simp only [dif_pos hi]


set_option maxHeartbeats 1600000 in
theorem cover_at : Big fun ch => ∀ s, CoverAt ch s := by
  refine big_mono (fun {D} _ _ _ _ _ _ _ _ _ _ _ ch h => ?_) (Big.and GlobalTheory.T.rowTest_mem_latticeStabilizer_of_localMatrices GlobalTheory.T.exists_periodGroup_point_lifting_rowGroup_localElements)
  obtain ⟨h5, h7⟩ := h
  classical
  intro s t b hb p hp
  have hidx : ∀ i : ℕ, i < D.R.m - 2 → i + 1 ∈ idx D := fun i hi => by
    simp only [idx, List.mem_range'_1]; omega
  choose r hr a ha δ x g hδ hx k hk hpe using hp
  let β : CosFam ch.G t := fun w i => DoubleCoset.mk _ _
    ((sgnAt ch.G t s w.1 (i + 1))⁻¹ * g (i + 1) (hidx i i.2) (by have h : (i : ℕ) < D.R.m - 2 := i.2; omega) w)
  refine ⟨β, fun j hj => ?_⟩
  have hj1 : 1 ≤ j ∧ j < 1 + (D.R.m - 2) := by simpa [idx, List.mem_range'_1] using hj
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hi : i < D.R.m - 2 := by omega
  have hjm : i + 1 ≤ D.R.m := by omega
  have hj' : i + 1 < D.R.m := by omega
  obtain ⟨-, hb2⟩ := hb β
  obtain ⟨δ', r', hδ', hr', hfin, a₀, ha₀, hab⟩ := hb2 (i + 1) hj hjm
  have key : ∀ w : locPl ch.G t, ∃ l : GL (Fin ((locGrid ch.G t w.1).rank (D.R.m, i + 1))) (Kw w.1), l ∈ rowR (G := locGrid ch.G t w.1) one_le_sLen (j := i + 1) hj' ∧
      ∃ κ ∈ givenLevel ch.G t w.1 (D.R.m, i + 1),
        (repsAt ch.G t w.1).elt (β w) (D.R.m, i + 1) =
          l * ((sgnAt ch.G t s w.1 (i + 1))⁻¹ * g (i + 1) hj hjm w) * κ := by
    intro w
    have e1 : (repsAt ch.G t w.1).elt (β w) (D.R.m, i + 1) = (repsAt ch.G t w.1).rep ⟨i, hi⟩ (β w ⟨i, hi⟩) :=
      eltAt (repsAt ch.G t w.1) (β w) i hi
    have e2 := (repsAt ch.G t w.1).mk_rep ⟨i, hi⟩ (β w ⟨i, hi⟩)
    rw [e1]
    obtain ⟨l, hl, κ, hκ, e⟩ := (@DoubleCoset.eq _ _ _ _ _ _).1 e2.symm
    exact ⟨l, hl, κ, hκ, e⟩
  choose l hl κ hκ hrep using key
  obtain ⟨y, hy, hyR⟩ := h7 s t (i + 1) hj hjm hj' (δ (i + 1) hj hjm) (hδ _ _ _) (fun w => (l w)⁻¹)
    fun w => inv_mem (hl w)
  have h1 := GlobalTheory.T.hasLocalLatticeMatrices_mul t ch.S.B hjm y r' _ _ hy hr'
  have h2 := GlobalTheory.T.hasLocalLatticeMatrices_inv t ch.S.B hjm (y * r') _ h1
  have hz := GlobalTheory.T.hasLocalLatticeMatrices_mul t ch.S.B hjm ((y * r')⁻¹) (x (i + 1) hj hjm) _ _ h2 (hx (i + 1) hj hjm)
  have hfun : (fun w => ((sgnAt ch.G t s w.1 (i + 1) * (l w)⁻¹ * (sgnAt ch.G t s w.1 (i + 1))⁻¹) *
      (sgnAt ch.G t s w.1 (i + 1) * (repsAt ch.G t w.1).elt (β w) (D.R.m, i + 1)))⁻¹ * g (i + 1) hj hjm w) =
      fun w => (κ w)⁻¹ := by
    funext w
    rw [hrep w]
    group
  rw [hfun] at hz
  set z := (y * r')⁻¹ * x (i + 1) hj hjm with hzdef
  have hzl : z ∈ latGrp ch.G (i + 1) := h5 t (i + 1) (by omega) hjm _ _ hz fun w => inv_mem (hκ w)
  have htilt : δ (i + 1) hj hjm = δ' := GlobalTheory.T.isRowFlagTilt_unique ch.G hj' _ _ (hδ _ _ _) hδ'
  have hyf : y ∈ GfC _ := GlobalTheory.T.mem_finitePoints_of_hasLocalLatticeMatrices t ch.S.B hjm _ _ hy
  set Y := δ (i + 1) hj hjm * y * (δ (i + 1) hj hjm)⁻¹ with hY
  have hYf : Y ∈ GfC _ := by
    rw [GfC, MonoidHom.mem_ker] at hyf ⊢
    rw [hY, map_mul, map_mul, hyf, mul_one, map_inv, mul_inv_cancel]
  have hcomm : a (i + 1) hj hjm * Y = Y * a (i + 1) hj hjm :=
    (GlobalTheory.AdelicSplit.adelic_split D _).2.2.1 _ (ha _ _ _) _ hYf
  refine ⟨r (i + 1) hj hjm * Y, mul_mem (hr _ _ _) hyR, a (i + 1) hj hjm * a₀, mul_mem (ha _ _ _) ha₀,
    z * k (i + 1) hj hjm, mul_mem hzl (hk _ _ _), ?_⟩
  have hxz : x (i + 1) hj hjm = y * r' * z := by rw [hzdef, mul_inv_cancel_left]
  rw [hpe (i + 1) hj hjm, hxz, show r (i + 1) hj hjm * Y * (a (i + 1) hj hjm * a₀) * b β (i + 1) * (z * k (i + 1) hj hjm) =
    r (i + 1) hj hjm * (a (i + 1) hj hjm * Y) * (a₀ * b β (i + 1)) * z * k (i + 1) hj hjm by
      rw [hcomm]; simp only [mul_assoc], hab, ← htilt, hY]
  simp only [mul_assoc, inv_mul_cancel_left]

end GlobalTheory.RowVal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TiltedPointsCoveredByRepresentativeCellsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tiltedPoints_covered_by_representativeCells : Big fun ch => ∀ s, CoverAt ch s := by
  first | exact @GlobalTheory.RowVal.cover_at | exact GlobalTheory.RowVal.cover_at | (intros; apply GlobalTheory.RowVal.cover_at <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrandSupportedOnCellsLargeDepth
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowVal

theorem biInv_eq_of_cells {ι : Type} [DecidableEq ι] {H : ι → Type} [∀ i, Group (H i)]
    {R K : ∀ i, Subgroup (H i)} {q : (∀ i, H i) → ℂ} :
    ∀ (l : List ι), BiInv R K l q → ∀ h h' : (∀ i, H i), (∀ i, i ∉ l → h i = h' i) →
      (∀ i ∈ l, ∃ r ∈ R i, ∃ k ∈ K i, h i = r * h' i * k) → q h = q h'
  | [], _, h, h', h1, _ => by
      have : h = h' := funext fun i => h1 i List.not_mem_nil
      rw [this]
  | i :: l, hq, h, h', h1, h2 => by
      have hi : i ∈ i :: l := List.mem_cons_self
      rcases h2 i hi with ⟨r, hr, k, hk, e⟩
      have hq' : BiInv R K l q := fun j hj => hq j (List.mem_cons_of_mem _ hj)
      set h₁ := Function.update h i (h' i) with hh₁
      have hi₁ : h₁ i = h' i := by simp [hh₁]
      have step1 : q h = q h₁ := by
        have a1 := (hq i List.mem_cons_self (Function.update h₁ i (h' i * k))).1 r hr
        have a2 := (hq i List.mem_cons_self h₁).2 k hk
        simp only [Function.update_self, Function.update_idem] at a1
        rw [hi₁] at a2
        have hh : h = Function.update h₁ i (r * (h' i * k)) := by
          funext j
          by_cases hj : j = i
          · subst hj; simp [e, mul_assoc]
          · simp [hh₁, Function.update_of_ne hj]
        rw [hh, a1, a2]
      rw [step1]
      refine biInv_eq_of_cells l hq' h₁ h' (fun j hj => ?_) (fun j hj => ?_)
      · by_cases hji : j = i
        · subst hji; exact hi₁
        · rw [hh₁, Function.update_of_ne hji]
          exact h1 j (by simp [hji, hj])
      · by_cases hji : j = i
        · subst hji; exact ⟨1, one_mem _, 1, one_mem _, by simp [hi₁]⟩
        · rw [hh₁, Function.update_of_ne hji]
          exact h2 j (List.mem_cons_of_mem _ hj)

theorem zero_not_mem_idx (D : D7) : 0 ∉ idx D := by simp [idx, List.mem_range']; intro x _; omega

section
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : GlobalTheory.RowTest.Choice R)

theorem evT_eq_zero_of (C : BiFam ch.G) (j : ℕ) (hj : Even j) (hjm : j < D.R.m) (hC : C j = 0) (f : SchRow ch.G)
    (u : ColPt ch.G) (y : RowPt ch.G) : evT C f u y = 0 := by
  obtain ⟨k, rfl⟩ := hj
  obtain ⟨c, hc⟩ := D.R.m_even
  unfold evT
  rw [Finset.prod_eq_zero (i := k) (by simp [Finset.mem_range]; omega) (by rw [two_mul, hC]; rfl), zero_mul]

end
end GlobalTheory.RowVal

namespace GlobalTheory.RowVal
section
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : GlobalTheory.RowTest.Choice R)

theorem suppOn_of_cover (s : ℤˣ) (hC : CoverAt ch s) (hF : FlatAt ch s) (hO : OffAt ch) (hI : InvAt ch) (hT : TensAt ch)
    (hB : BasicAt ch) : SuppOn ch s := by
  intro t a τ hτ M hM P y b hb h h1 hne
  obtain ⟨hφ, hFt, hHaar, -, hGood, -, -⟩ := hB
  have hsum : ∀ h' : Pts ch.G, tot ch.W hM P τ (colFn ch a) (formTop ch t y) h' = ∑ d ∈ τ.support,
      τ d * per ch.W M t (conAt ch.W hM (fockD ch.W t d.2 P.2) h') d.1 P.1 (colFn ch a) (formTop ch t y) := fun _ => rfl
  have hne' := hne
  rw [hsum] at hne'
  obtain ⟨d, hd, hdne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne'
  have hper := right_ne_zero_of_mul hdne
  have hnz : ∀ j, Even j → j < D.R.m → conAt ch.W hM (fockD ch.W t d.2 P.2) h j ≠ 0 := by
    intro j hj hjm h0
    apply hper
    have := hT t M (hHaar t M hM) _ _ (hφ a) (hFt t y) Unit {()} (fun _ => 1)
      (fun _ => conAt ch.W hM (fockD ch.W t d.2 P.2) h) (fun _ => d.1)
      (fun _ _ => hGood t _ τ hτ M hM d hd P.2 h)
      (fun u y' => by simp [evT_eq_zero_of ch _ j hj hjm h0]) P.1
    simpa using this
  have h0 : h 0 = 1 := h1 0 (zero_not_mem_idx D)
  obtain ⟨β, hβ⟩ := hC t b hb h (hO t _ τ hτ M hM d hd P.2 h h0 hnz)
  refine ⟨β, ?_, hβ⟩
  by_contra hns
  apply hne
  classical

  choose! r hr a' ha' k hk e using hβ
  let p : Pts ch.G := fun j => if j ∈ idx D then a' j else 1
  have hp : IsRealPt p := by
    refine ⟨fun j => ?_, fun j hj => by simp [p, hj]⟩
    by_cases hj : j ∈ idx D
    · simp only [p, if_pos hj]; exact ha' j hj
    · simp only [p, if_neg hj]; exact one_mem _
  have hmove : tot ch.W hM P τ (colFn ch a) (formTop ch t y) h = tot ch.W hM P τ (colFn ch a) (formTop ch t y) (p * b β) := by
    refine biInv_eq_of_cells (idx D) (hI t a τ hτ M hM P y) h (p * b β) (fun j hj => ?_) (fun j hj => ?_)
    · simp [p, hj, h1 j hj, (hb β).1 j hj]
    · refine ⟨r j, hr j hj, k j, hk j hj, ?_⟩
      simp only [Pi.mul_apply, p, if_pos hj, e j hj, mul_assoc]
  rw [hmove]

  have hexp : ch.S.IsExpansion t (ch.Phi a) β 0 := by
    obtain ⟨e₀, he₀, -⟩ := hτ
    refine ⟨e₀, he₀, by simp, fun x y' _ _ => ?_⟩
    rw [Finsupp.sum_zero_index]
    simp only [GridChoice.supp, Set.mem_setOf_eq, not_forall] at hns
    obtain ⟨w, hw⟩ := hns
    have hz : (ch.S.term t (ch.Phi a) β w).datum = 0 := by
      simpa [unfSupport, GridChoice.term] using hw
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ w) (by rw [hz]; rfl)
  obtain ⟨z, -, hFl⟩ := hF
  obtain ⟨Cr, -, hCr⟩ := hFl P.2 p hp
  obtain ⟨ζ, -, hz⟩ := hCr t (ch.Phi a) τ hτ M hM β (b β) (hb β) 0 (fun _ => 0) hexp (by intro d hd; simp at hd)
  rw [hsum]
  exact hT t M (hHaar t M hM) _ _ (hφ a) (hFt t y) _ τ.support (fun d => τ d)
    (fun d => conAt ch.W hM (fockD ch.W t d.2 P.2) (p * b β)) (fun d => d.1)
    (fun d hd => hGood t _ τ hτ M hM d hd P.2 _)
    (fun u y' => by simpa [Finsupp.sum] using hz u y') P.1

end

theorem big_suppOn_of_flat :
    GlobalTheory.RowClaim.Big fun ch => ∀ s, FlatAt ch s → OffAt ch → InvAt ch → TensAt ch → BasicAt ch → SuppOn ch s :=
  big_mono (fun ch hC s hF hO hI hT hB => suppOn_of_cover ch s (hC s) hF hO hI hT hB) GlobalTheory.T.tiltedPoints_covered_by_representativeCells

end GlobalTheory.RowVal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrandSupportedOnCellsLargeDepthStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrand_supported_on_cells_largeDepth : Big fun ch => ∀ s, FlatAt ch s → OffAt ch → InvAt ch → TensAt ch → BasicAt ch → SuppOn ch s := by
  first | exact @GlobalTheory.RowVal.big_suppOn_of_flat | exact GlobalTheory.RowVal.big_suppOn_of_flat | (intros; apply GlobalTheory.RowVal.big_suppOn_of_flat <;> assumption)
end
