module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestColumnInductionLocalToGlobalExpansion

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowDataLocalPureTensorsLargeDepth
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowDataLocalPureTensorsLargeDepth
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.RowSingle

theorem locPl_under {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData L sc) (t : T) :
    ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ∈ G.pl.S0 ∨ ∃ w' ∈ L.Q t, w.under (𝓞 D.host.F) = w'.under (𝓞 D.host.F) := by
  intro w hw
  unfold locPl at hw
  rcases Finset.mem_union.1 hw with h | h
  · left
    unfold Places.W0 at h
    obtain ⟨v, hv, rfl⟩ := by simpa only [Finset.mem_image] using h
    rw [G.pl.under_w hv]
    exact hv
  · exact Or.inr ⟨w, h, rfl⟩

theorem exists_rowData {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} (W : G.Weil)
    {μ₀ : T} (hL : L.Is μ₀) (ρ : RealMatch W) (t : T) (e : AE D) (he : IsIdemSum e (locPl G t))
    (F : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ) (fr : SchRow G)
    (hfr : ∀ i : Fin D.R.m, IsLocVec W (.chi i D.R.m) e (ρ.vX i D.R.m) (F i) (fr i)) :
    ∃ (dr : ∀ i : Fin D.R.m, FinDatum G t (.chi i D.R.m))
      (cr : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) →₀ ℂ),
      (∀ i, (dr i).e = e ∧ IsCombOf W (dr i) (cr i)) ∧ (∀ i, comb W.ψ _ _ (cr i) (ρ.vX i D.R.m) = fr i) ∧
        ∀ i, (dr i).fn = F i := by
  let dr : ∀ i : Fin D.R.m, FinDatum G t (.chi i D.R.m) := fun i =>
    { FinDatum.ind G t (.chi i D.R.m) (locPl G t) (locPl_under G t) e he with fn := F i, sb := (hfr i).1 }
  let d : PureDat G t := (fun j => FinDatum.vacuum G t (.top t j), dr)
  obtain ⟨c, hc⟩ := GlobalTheory.CombsExist.exists_isCombs W hL (Finsupp.single d 1)
  have hc' := (hc d (by simp)).2
  refine ⟨dr, fun i => (c d).2 i, fun i => ⟨rfl, hc' i⟩, fun i => ?_, fun i => rfl⟩
  have hv := ρ.vX_is i D.R.m i.2 le_rfl
  obtain ⟨⟨Tm, hTm⟩, h1⟩ := (hc' i).2.2 (ρ.vX i D.R.m) hv.2.theta hv.2.lat
  exact (h1 Tm hTm).trans ((hfr i).2.2 Tm hTm).symm

theorem rowData : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (e : AE D), IsIdemSum e (locPl ch.G t) → ∀ (φ : (∀ w : locPl ch.G t, ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w.1).rank b.tgt)) (Fin ((locGrid ch.G t w.1).rank b.src)) (Kw w.1) → ℂ)) (fr : SchRow ch.G), (∀ i : Fin D.R.m, IsLocVec ch.W (.chi i D.R.m) e (ch.rm.vX i D.R.m) (fun y => if IsHalf e y then ∏ w : locPl ch.G t, φ w (.ex i D.R.m) (ch.S.B.coord t w.1 (X := (i, D.R.m)) (Y := (i + 1, D.R.m)) ⟨i.2.le, le_rfl⟩ ⟨i.2, le_rfl⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (fr i)) → ∃ (dr : ∀ i : Fin D.R.m, FinDatum ch.G t (.chi i D.R.m)) (cr : ∀ i : Fin D.R.m, WO (ch.G.pS (.chi i D.R.m : Pair T)) (ch.G.pT (.chi i D.R.m : Pair T)) →₀ ℂ), (∀ i, (dr i).e = e ∧ IsCombOf ch.W (dr i) (cr i)) ∧ (∀ i, comb ch.W.ψ _ _ (cr i) (ch.rm.vX i D.R.m) = fr i) ∧ ∀ i y, IsHalf e y → (dr i).fn y = ∏ w : locPl ch.G t, φ w (.ex i D.R.m) (ch.S.B.coord t w.1 (X := (i, D.R.m)) (Y := (i + 1, D.R.m)) ⟨i.2.le, le_rfl⟩ ⟨i.2, le_rfl⟩ (y.map fun a => cpt w.1 (toEAf D a))) := by
  refine ⟨0, fun _ _ _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch _ _ => ?_⟩⟩
  intro t e he φ fr hfr
  obtain ⟨dr, cr, h1, h2, h3⟩ := exists_rowData ch.W s.core.lev ch.rm t e he _ fr hfr
  exact ⟨dr, cr, h1, h2, fun i y hy => by simp only [h3 i, hy, ↓reduceIte]⟩

end GlobalTheory.RowSingle
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowDataLocalPureTensorsLargeDepthStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowData_localPureTensors_largeDepth : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (e : AE D), IsIdemSum e (locPl ch.G t) → ∀ (φ : (∀ w : locPl ch.G t, ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w.1).rank b.tgt)) (Fin ((locGrid ch.G t w.1).rank b.src)) (Kw w.1) → ℂ)) (fr : SchRow ch.G), (∀ i : Fin D.R.m, IsLocVec ch.W (.chi i D.R.m) e (ch.rm.vX i D.R.m) (fun y => if IsHalf e y then ∏ w : locPl ch.G t, φ w (.ex i D.R.m) (ch.S.B.coord t w.1 (X := (i, D.R.m)) (Y := (i + 1, D.R.m)) ⟨i.2.le, le_rfl⟩ ⟨i.2, le_rfl⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (fr i)) → ∃ (dr : ∀ i : Fin D.R.m, FinDatum ch.G t (.chi i D.R.m)) (cr : ∀ i : Fin D.R.m, WO (ch.G.pS (.chi i D.R.m : Pair T)) (ch.G.pT (.chi i D.R.m : Pair T)) →₀ ℂ), (∀ i, (dr i).e = e ∧ IsCombOf ch.W (dr i) (cr i)) ∧ (∀ i, comb ch.W.ψ _ _ (cr i) (ch.rm.vX i D.R.m) = fr i) ∧ ∀ i y, IsHalf e y → (dr i).fn y = ∏ w : locPl ch.G t, φ w (.ex i D.R.m) (ch.S.B.coord t w.1 (X := (i, D.R.m)) (Y := (i + 1, D.R.m)) ⟨i.2.le, le_rfl⟩ ⟨i.2, le_rfl⟩ (y.map fun a => cpt w.1 (toEAf D a))) := by
  first | exact @GlobalTheory.RowSingle.rowData | exact GlobalTheory.RowSingle.rowData | (intros; apply GlobalTheory.RowSingle.rowData <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColumnFlatTensorExpansionLargeDepth
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColumnFlatTensorExpansionLargeDepth
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.LocAsm

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def exInd {G : GlobalTheory.SplitFlip.Grid k} (φ : ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ) :
    ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ := fun b =>
  match b with
  | .ex i j => (SetLike.coe (GlobalTheory.SplitFlip.matLat (Fin (G.rank (GlobalTheory.SplitFlip.Edge.ex i j).tgt))
      (GlobalTheory.SplitFlip.stdLat k (Fin (G.rank (GlobalTheory.SplitFlip.Edge.ex i j).src))))).indicator 1
  | .theta i j => φ (.theta i j)

theorem isNatDatum_exInd {G : GlobalTheory.SplitFlip.Grid k} {ϖ : kˣ} (hϖ : GlobalTheory.SplitFlip.IsUnif ϖ) {e : ℕ} {γ : List GlobalTheory.SplitFlip.Edge}
    (φ : ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ)
    (hφ : ∀ b ∈ γ, GlobalTheory.SplitFlip.IsNatDatum ϖ e (φ b)) : ∀ b ∈ γ, GlobalTheory.SplitFlip.IsNatDatum ϖ e (exInd φ b) := by
  intro b hb
  cases b with
  | ex i j => exact GlobalTheory.SplitFlip.hasDepth_indicator hϖ e _
  | theta i j => exact hφ _ hb

variable [MeasurableSpace k] [BorelSpace k]

theorem flatTensor_exOne_eq_exInd {G : GlobalTheory.SplitFlip.Grid k} (hs : 1 ≤ G.s) (ψ : AddChar k Circle) (ν : Measure k)
    (keep : Bool) (g : G.VertexGroup) (γ : List GlobalTheory.SplitFlip.Edge)
    (φ : ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ) (x : ColArgs G) :
    flatTensor hs ψ ν (moved G keep g (G.lines₂ γ (exOne φ))) x 0 =
      flatTensor hs ψ ν (moved G keep g (G.lines₂ γ (exInd φ))) x 0 := by
  unfold flatTensor
  congr 1
  funext v
  unfold flatIntegrand moved GlobalTheory.SplitFlip.Grid.pathAct GlobalTheory.SplitFlip.Grid.lines₂
  have key : (γ.map fun b => exOne φ b (G.moveArgs .one g (fill hs x 0 v) b)).prod =
      (γ.map fun b => exInd φ b (G.moveArgs .one g (fill hs x 0 v) b)).prod := by
    refine congrArg List.prod (List.map_congr_left fun b _ => ?_)
    cases b with
    | theta i j => rfl
    | ex i j =>
      have h0 : G.moveArgs .one g (fill hs x 0 v) (.ex i j) = 0 := by
        have : fill hs x 0 v (.ex i j) = 0 := by
          unfold fill
          dsimp only
          split_ifs <;> ext <;> simp
        simp [GlobalTheory.SplitFlip.Grid.moveArgs, this]
      rw [h0]
      simp [exOne, exInd, Set.indicator_of_mem (Submodule.zero_mem _)]
  rw [key]

end Local

section Abstract

variable {ι : Type} [Fintype ι] [DecidableEq ι] {A : ι → Type} [∀ j, AddCommGroup (A j)]

theorem sum_reps_mul_indicator_eq_self (SA BA : ∀ j, A j → Prop) (hSA : ∀ j a b, SA j a → SA j b → SA j (a - b)) (R : ∀ j, Finset (A j))
    (hR2 : ∀ j x, BA j x → ∃ r ∈ R j, SA j (x - r)) (hR3 : ∀ j, ∀ r ∈ R j, ∀ r' ∈ R j, SA j (r - r') → r = r')
    (F : (∀ j, A j) → ℂ) (hper : ∀ x a, (∀ j, SA j (a j)) → F (x + a) = F x) (x : ∀ j, A j)
    (hsupp : F x ≠ 0 → ∀ j, BA j (x j)) :
    ∑ q : (∀ j, R j), F (fun j => (q j).1) * ∏ j, (if SA j (x j - (q j).1) then (1 : ℂ) else 0) = F x := by
  by_cases hex : ∃ q : (∀ j, R j), ∀ j, SA j (x j - (q j).1)
  · obtain ⟨q₀, hx⟩ := hex
    rw [Finset.sum_eq_single q₀]
    · rw [Finset.prod_eq_one fun j _ => if_pos (hx j), mul_one]
      have h := hper (fun j => (q₀ j).1) (x - fun j => (q₀ j).1) hx
      rw [add_sub_cancel] at h
      exact h.symm
    · intro q _ hne
      by_contra hz
      apply hne
      have h1 : ∀ j, SA j (x j - (q j).1) := fun j => by
        by_contra h0
        apply hz
        rw [Finset.prod_eq_zero (Finset.mem_univ j) (if_neg h0)]; ring
      refine funext fun j => Subtype.ext ?_
      have := hSA j _ _ (hx j) (h1 j)
      rw [sub_sub_sub_cancel_left] at this
      exact hR3 j _ (q j).2 _ (q₀ j).2 this
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [Finset.sum_eq_zero]
    · symm
      by_contra hne
      apply hex
      have sx := hsupp hne
      choose r hr hrs using fun j => hR2 j (x j) (sx j)
      exact ⟨fun j => ⟨r j, hr j⟩, hrs⟩
    · intro q _
      by_contra hz
      apply hex
      refine ⟨q, fun j => ?_⟩
      by_contra h0
      apply hz
      rw [Finset.prod_eq_zero (Finset.mem_univ j) (if_neg h0)]; ring

end Abstract

set_option maxHeartbeats 1000000 in
theorem colFlat_expansion : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (β : CosFam ch.G t) (w : locPl ch.G t) (eL : AE D), IsIdemSum eL {w.1} → ∀ (φ : ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w.1).rank b.tgt)) (Fin ((locGrid ch.G t w.1).rank b.src)) (Kw w.1) → ℂ), (∀ b ∈ GlobalTheory.SplitFlip.oppositePath D.R.m, GlobalTheory.SplitFlip.IsNatDatum (unifAt w.1) (depthAt ch.G w.1) (φ b)) → ∃ (I : Type) (S : Finset I) (x : I → ℂ) (d : I → ∀ j : Fin D.R.m, FinDatum ch.G t (.top t j)) (c : I → Combs ch.G), (∀ i ∈ S, ∀ j : Fin D.R.m, (d i j).e = eL ∧ IsCombOf ch.W (d i j) ((c i).1 j)) ∧ ∀ y : ∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))), (∀ j, IsHalf eL (y j)) → ∑ i ∈ S, x i * ∏ j, (d i j).fn (y j) = flatTensor one_le_sLen (psiAt ch.W w.1) (unitVol w.1) (moved (locGrid ch.G t w.1) (keepAt ch.G w.1) ((repsAt ch.G t w.1).elt (β w)) ((locGrid ch.G t w.1).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) (GlobalTheory.LocAsm.exOne φ))) (ch.S.colAt t w.1 y) 0 := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  intro t β w eL heL φ hφ
  have hL := s.core.lev
  have hde : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q) := by
    obtain ⟨⟨P, -, -⟩, -⟩ := s.size
    have key : ∀ p ∈ D.host.levelPrimes, p.Prime → Nat.Coprime p (D.host.QS * D.host.q) := fun p hp hpp =>
      UpperTheory.Ram.Fun.coprime_QSq_of_splitK D.host hpp (P.level_split p hp)
    exact ⟨key _ D.host.pde_level.1 D.host.pde_prime, key _ D.host.pde_level.2 D.host.pde'_prime⟩
  have hm : 2 ≤ D.R.m := D.R.two_le_m
  have hg := (Good.locGrid_isGood hL ch.G ch.W t hde (hch.guard t)).1 w.1 w.2
  have h00 := hg.square 0 (by change 0 < D.R.m; omega) 0 (by change 0 < D.R.m; omega)
  haveI := (isUnitVol_unitVol w.1).1
  have hT := (locGrid ch.G t w.1).isTensor_pureTensor (unifAt w.1) (depthAt ch.G w.1)
    (GlobalTheory.SplitFlip.oppositePath D.R.m) (exInd φ) (isNatDatum_exInd (isUnif_unifAt w.1) φ hφ)
  obtain ⟨N, hF⟩ := exists_isSBArgs_flat (locGrid ch.G t w.1) one_le_sLen (psiAt ch.W w.1) (unitVol w.1) (unifAt w.1)
    (depthAt ch.G w.1) _ (keepAt ch.G w.1) ((repsAt ch.G t w.1).elt (β w)) hm h00.unif h00.cond hT
  set Fl := flatTensor one_le_sLen (psiAt ch.W w.1) (unitVol w.1) (moved (locGrid ch.G t w.1) (keepAt ch.G w.1)
    ((repsAt ch.G t w.1).elt (β w)) ((locGrid ch.G t w.1).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) (exInd φ))) with hFl
  choose Rp hR1 hR2 hR3 using fun j : Fin D.R.m => GlobalTheory.T.exists_finset_cosetReps_bounded_half_points (ch.S.βp (j + 1)) (ch.S.βp j) {w.1} eL N heL
  have sdT : ∀ j, j ≤ D.R.m → IsSelfDualC (ch.G.V (.top j)) (ch.G.Λ (.top j)) := fun j hj =>
    (ch.G.isV (X := .top j) hj fun _ h => by cases h).sd
  let d : (∀ j : Fin D.R.m, Rp j) → ∀ j : Fin D.R.m, FinDatum ch.G t (.top t j) := fun κ j =>
    { FinDatum.ind ch.G t (.top t j) {w.1} (fun w' hw' => by
        rw [Finset.mem_singleton] at hw'
        subst hw'
        exact (Good.locPl_cases w.2).elim (fun h => .inl h.1) fun h => .inr ⟨_, h.2.2, rfl⟩) eL heL with
      fn := cosLoc {w.1} eL (ch.S.βp (j + 1)) (ch.S.βp j) (N : ℤ) (κ j).1
      sb := GlobalTheory.T.indicator_smallCoset_half_isSchwartzBruhat (ch.G.V (.top j)) (ch.G.V (.top (j + 1))) (ch.G.Λ (.top j)) (ch.G.Λ (.top (j + 1))) (ch.S.βp j)
        (ch.S.βp (j + 1)) {w.1} eL N (κ j).1 (by first | exact GlobalTheory.ProjXCols.selfDual_isFullLattice _ _ (sdT j j.2.le) | exact (sdT j j.2.le).1)
        (by first | exact GlobalTheory.ProjXCols.selfDual_isFullLattice _ _ (sdT (j + 1) j.2) | exact (sdT (j + 1) j.2).1) (ch.S.βp_is j j.2.le)
        (ch.S.βp_is (j + 1) j.2) heL (hR1 j _ (κ j).2).1 }
  choose c₁ hc₁ using fun (κ : ∀ j : Fin D.R.m, Rp j) (j : Fin D.R.m) =>
    GlobalTheory.CombsExist.exists_isCombOf ch.W (p := .top t j) (sdT j j.2.le) (sdT (j + 1) j.2) (d κ j)
  refine ⟨∀ j : Fin D.R.m, Rp j, Finset.univ, fun κ => Fl (ch.S.colAt t w.1 fun j => (κ j).1) 0, d,
    fun κ => (fun j => if h : j < D.R.m then c₁ κ ⟨j, h⟩ else 0, fun _ => 0), ?_, ?_⟩
  · intro κ _ j
    refine ⟨rfl, ?_⟩
    dsimp only
    rw [dite_eq_left j.2]
    exact hc₁ κ j
  · intro y hy
    refine Eq.trans ?_ (flatTensor_exOne_eq_exInd (G := locGrid ch.G t w.1) one_le_sLen _ _ _ _ _ φ _).symm
    have hper : ∀ (x a : ∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1)))),
        (∀ j : Fin D.R.m, IsSmall {w.1} (ch.S.βp ((j : ℕ) + 1)) (ch.S.βp j) (N : ℤ) (a j)) →
        Fl (ch.S.colAt t w.1 (x + a)) 0 = Fl (ch.S.colAt t w.1 x) 0 := fun x a ha => by
      rw [colAt_add]
      have := hF.per (ch.S.colAt t w.1 x) 0 (ch.S.colAt t w.1 a) 0 (fun j hj r s => ?_) (fun i _ r s => by simp)
      · rwa [add_zero] at this
      · rw [colAt_eq _ t w.1 _ hj]
        have := ha ⟨j, hj⟩ w.1 (Finset.mem_singleton_self _) (Fin.cast (topRank_eq ch.G t w.1 hj) r)
          (Fin.cast (topRank_eq ch.G t w.1 hj.le) s)
        rw [zpow_natCast] at this
        exact this
    have hsupp : Fl (ch.S.colAt t w.1 y) 0 ≠ 0 → ∀ j : Fin D.R.m,
        IsHalf eL (y j) ∧ IsSmall {w.1} (ch.S.βp ((j : ℕ) + 1)) (ch.S.βp j) (-(N : ℤ)) (y j) := by
      intro hne j
      refine ⟨hy j, fun w' hw' r s => ?_⟩
      rw [Finset.mem_singleton] at hw'
      subst hw'
      have := (hF.supp _ _ hne).1 j j.2 (Fin.cast (topRank_eq ch.G t w.1 j.2).symm r)
        (Fin.cast (topRank_eq ch.G t w.1 j.2.le).symm s)
      rw [colAt_eq _ t w.1 y j.2] at this
      rw [_root_.zpow_neg, zpow_natCast]
      exact this
    have key := sum_reps_mul_indicator_eq_self (ι := Fin D.R.m) (A := fun j : Fin D.R.m => WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))))
      (fun j a => IsSmall {w.1} (ch.S.βp ((j : ℕ) + 1)) (ch.S.βp j) (N : ℤ) a)
      (fun j a => IsHalf eL a ∧ IsSmall {w.1} (ch.S.βp ((j : ℕ) + 1)) (ch.S.βp j) (-(N : ℤ)) a)
      (fun _ _ _ h h' => h.sub h') Rp (fun j x h => hR2 j x h.1 h.2) hR3 (fun x => Fl (ch.S.colAt t w.1 x) 0)
      hper y hsupp
    refine (Finset.sum_congr rfl fun κ _ => ?_).trans key
    exact congrArg₂ (· * ·) rfl (Finset.prod_congr rfl fun j _ => cosLoc_eq_ite (hy j))

end GlobalTheory.LocAsm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColumnFlatTensorExpansionLargeDepthStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnFlatTensor_expansion_largeDepth : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (β : CosFam ch.G t) (w : locPl ch.G t) (eL : AE D), IsIdemSum eL {w.1} → ∀ (φ : ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w.1).rank b.tgt)) (Fin ((locGrid ch.G t w.1).rank b.src)) (Kw w.1) → ℂ), (∀ b ∈ GlobalTheory.SplitFlip.oppositePath D.R.m, GlobalTheory.SplitFlip.IsNatDatum (unifAt w.1) (depthAt ch.G w.1) (φ b)) → ∃ (I : Type) (S : Finset I) (x : I → ℂ) (d : I → ∀ j : Fin D.R.m, FinDatum ch.G t (.top t j)) (c : I → Combs ch.G), (∀ i ∈ S, ∀ j : Fin D.R.m, (d i j).e = eL ∧ IsCombOf ch.W (d i j) ((c i).1 j)) ∧ ∀ y : ∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))), (∀ j, IsHalf eL (y j)) → ∑ i ∈ S, x i * ∏ j, (d i j).fn (y j) = flatTensor one_le_sLen (psiAt ch.W w.1) (unitVol w.1) (moved (locGrid ch.G t w.1) (keepAt ch.G w.1) ((repsAt ch.G t w.1).elt (β w)) ((locGrid ch.G t w.1).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) (GlobalTheory.LocAsm.exOne φ))) (ch.S.colAt t w.1 y) 0 := by
  first | exact @GlobalTheory.LocAsm.colFlat_expansion | exact GlobalTheory.LocAsm.colFlat_expansion | (intros; apply GlobalTheory.LocAsm.colFlat_expansion <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatTensorRowFactorLargeDepth
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatTensorRowFactorLargeDepth
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LocAsm
open GlobalTheory.SplitFlip

section General
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem moved_pureTensor_eq_mul (G : Grid k) (keep : Bool) (g : G.VertexGroup)
    (hg : ∀ i < G.m, g (i, G.m) = 1 ∧ g (i + 1, G.m) = 1)
    (φ : ∀ b : Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ) (z : G.Args) :
    moved G keep g (G.lines₂ (oppositePath G.m) φ) z =
      moved G keep g (G.lines₂ (oppositePath G.m) (exOne φ)) z *
        ∏ i ∈ Finset.range G.m, φ (.ex i G.m) (z (.ex i G.m)) := by
  have h1 : ((List.range G.m).map fun i => φ (.ex i G.m) (G.moveArgs .one g z (.ex i G.m))) =
      (List.range G.m).map fun i => φ (.ex i G.m) (z (.ex i G.m)) := by
    refine List.map_congr_left fun i hi => ?_
    obtain ⟨ha, hb⟩ := hg i (List.mem_range.1 hi)
    simp only [Grid.moveArgs, Edge.src, Edge.tgt, ha, hb, map_one, inv_one, Units.val_one, Matrix.one_mul,
      Matrix.mul_one]
  have h2 : ((List.range G.m).map fun i => exOne φ (.ex i G.m) (G.moveArgs .one g z (.ex i G.m))).prod = 1 := by
    simp [exOne]
  simp only [moved, Grid.pathAct, Grid.lines₂, oppositePath, List.map_append, List.prod_append, List.map_map,
    Function.comp_def]
  rw [h1, h2]
  show _ = _ * ((List.range G.m).map fun i => φ (.ex i G.m) (z (.ex i G.m))).prod
  simp only [exOne_theta, List.map_reverse]
  ring

theorem moved_exOne_fill (G : Grid k) (hs : 1 ≤ G.s) (keep : Bool) (g : G.VertexGroup) (γ : List Edge)
    (φ : ∀ b : Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ) (x : ColArgs G) (y y' : RowArgs G)
    (e : Vars G) :
    moved G keep g (G.lines₂ γ (exOne φ)) (fill hs x y e) =
      moved G keep g (G.lines₂ γ (exOne φ)) (fill hs x y' e) := by
  simp only [moved, Grid.pathAct, Grid.lines₂]
  congr 3
  refine List.map_congr_left fun b _ => ?_
  cases b <;> rfl

variable [MeasurableSpace k] [BorelSpace k]

theorem flatTensor_moved_pureTensor (G : Grid k) (hs : 1 ≤ G.s) (ψ : AddChar k Circle) (ν : Measure k) (keep : Bool)
    (g : G.VertexGroup) (hg : ∀ i < G.m, g (i, G.m) = 1 ∧ g (i + 1, G.m) = 1)
    (φ : ∀ b : Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ) (x : ColArgs G) (y : RowArgs G) :
    flatTensor hs ψ ν (moved G keep g (G.lines₂ (oppositePath G.m) φ)) x y =
      flatTensor hs ψ ν (moved G keep g (G.lines₂ (oppositePath G.m) (exOne φ))) x 0 *
        ∏ i ∈ Finset.range G.m, φ (.ex i G.m) (y i)ᵀ := by
  unfold flatTensor flatIntegrand
  rw [← integral_mul_const]
  congr 1
  funext e
  rw [moved_pureTensor_eq_mul G keep g hg φ, moved_exOne_fill G hs keep g _ φ x y 0 e]
  simp only [fill_ex]
  ring

end General

theorem Reps.elt_row {k : Type} [Field k] {G : Grid k} {hs : 1 ≤ G.s} {J : G.Level} (ρ : Reps hs J)
    (β : Cosets hs J) : ∀ i < G.m, ρ.elt β (i, G.m) = 1 ∧ ρ.elt β (i + 1, G.m) = 1 := by
  intro i hi
  refine ⟨dif_neg (by simp only; omega), ?_⟩
  by_cases h : i + 1 = G.m
  · have key : ∀ j (hj : j = i + 1), ρ.elt β (G.m, j) = 1 := by
      intro j hj
      subst hj
      rw [Reps.elt, onColumn_apply]
      exact dif_neg (by omega)
    rw [h]
    exact key G.m h.symm
  · exact dif_neg (by simp only; omega)

theorem flatTensor_rowFactor : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (β : CosFam ch.G t) (w : locPl ch.G t) (φ : ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w.1).rank b.tgt)) (Fin ((locGrid ch.G t w.1).rank b.src)) (Kw w.1) → ℂ), (∀ b ∈ GlobalTheory.SplitFlip.oppositePath D.R.m, GlobalTheory.SplitFlip.IsNatDatum (unifAt w.1) (depthAt ch.G w.1) (φ b)) → ∀ (u : ∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1)))) (y : ∀ i : Fin D.R.m, WO (ch.G.pS (.chi i D.R.m : Pair T)) (ch.G.pT (.chi i D.R.m : Pair T))), flatTensor one_le_sLen (psiAt ch.W w.1) (unitVol w.1) (moved (locGrid ch.G t w.1) (keepAt ch.G w.1) ((repsAt ch.G t w.1).elt (β w)) ((locGrid ch.G t w.1).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) φ)) (ch.S.colAt t w.1 u) (ch.S.rowAt t w.1 y) = flatTensor one_le_sLen (psiAt ch.W w.1) (unitVol w.1) (moved (locGrid ch.G t w.1) (keepAt ch.G w.1) ((repsAt ch.G t w.1).elt (β w)) ((locGrid ch.G t w.1).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) (GlobalTheory.LocAsm.exOne φ))) (ch.S.colAt t w.1 u) 0 * ∏ i : Fin D.R.m, φ (.ex i D.R.m) (ch.S.B.coord t w.1 (X := (i, D.R.m)) (Y := (i + 1, D.R.m)) ⟨i.2.le, le_rfl⟩ ⟨i.2, le_rfl⟩ ((y i).map fun a => cpt w.1 (toEAf D a))) := by
  refine ⟨0, fun _ _ _ => ⟨0, ?_⟩⟩
  intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F _ ch _ _ t β w φ _ u y
  refine (flatTensor_moved_pureTensor (locGrid ch.G t w.1) one_le_sLen _ _ _ _ (Reps.elt_row _ _) φ _ _).trans ?_
  congr 1
  rw [Finset.prod_range]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [GridChoice.rowAt]
  rw [dite_eq_left (show (i : ℕ) < D.R.m from i.2)]
  rfl

end GlobalTheory.LocAsm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatTensorRowFactorLargeDepthStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatTensor_rowFactor_largeDepth : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (β : CosFam ch.G t) (w : locPl ch.G t) (φ : ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w.1).rank b.tgt)) (Fin ((locGrid ch.G t w.1).rank b.src)) (Kw w.1) → ℂ), (∀ b ∈ GlobalTheory.SplitFlip.oppositePath D.R.m, GlobalTheory.SplitFlip.IsNatDatum (unifAt w.1) (depthAt ch.G w.1) (φ b)) → ∀ (u : ∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1)))) (y : ∀ i : Fin D.R.m, WO (ch.G.pS (.chi i D.R.m : Pair T)) (ch.G.pT (.chi i D.R.m : Pair T))), flatTensor one_le_sLen (psiAt ch.W w.1) (unitVol w.1) (moved (locGrid ch.G t w.1) (keepAt ch.G w.1) ((repsAt ch.G t w.1).elt (β w)) ((locGrid ch.G t w.1).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) φ)) (ch.S.colAt t w.1 u) (ch.S.rowAt t w.1 y) = flatTensor one_le_sLen (psiAt ch.W w.1) (unitVol w.1) (moved (locGrid ch.G t w.1) (keepAt ch.G w.1) ((repsAt ch.G t w.1).elt (β w)) ((locGrid ch.G t w.1).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) (GlobalTheory.LocAsm.exOne φ))) (ch.S.colAt t w.1 u) 0 * ∏ i : Fin D.R.m, φ (.ex i D.R.m) (ch.S.B.coord t w.1 (X := (i, D.R.m)) (Y := (i + 1, D.R.m)) ⟨i.2.le, le_rfl⟩ ⟨i.2, le_rfl⟩ ((y i).map fun a => cpt w.1 (toEAf D a))) := by
  first | exact @GlobalTheory.LocAsm.flatTensor_rowFactor | exact GlobalTheory.LocAsm.flatTensor_rowFactor | (intros; apply GlobalTheory.LocAsm.flatTensor_rowFactor <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalPureTensorProductExpansionAllPlaces
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LocAsm

theorem exists_idemSum_singleton : ∀ {D : D7} (e : AE D) (P : Finset (Pl D.host.E)), IsIdemSum e P → ∀ w ∈ P, ∃ e' : AE D, IsIdemSum e' {w} := fun e P he w hw =>
  (GlobalTheory.IdemFlip.idemSum_sub_and_flip _ e P {w} he (Finset.singleton_subset_iff.2 hw)).1

theorem oneProduct : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (s : ℤˣ) (t : T) (β : CosFam ch.G t) (ζ : locPl ch.G t → ℂ), (∀ w : locPl ch.G t, GlobalTheory.LocAsm.PlaceCl ch s t w (β w) (ζ w)) → ∀ (M : Vol ch.G) (hM : M.Is t) (b b₀ : Pts ch.G), IsRep t ch.S.B s β b → IsBase t ch.S.B b₀ → ∀ e : AE D, IsIdemSum e (locPl ch.G t) → ∀ (φ : (∀ w : locPl ch.G t, ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w.1).rank b.tgt)) (Fin ((locGrid ch.G t w.1).rank b.src)) (Kw w.1) → ℂ)), (∀ w : locPl ch.G t, ∀ b ∈ GlobalTheory.SplitFlip.oppositePath D.R.m, GlobalTheory.SplitFlip.IsNatDatum (unifAt w.1) (depthAt ch.G w.1) (φ w b)) → ∀ (fd : SchDown ch.G t) (fr : SchRow ch.G), (∀ j : Fin D.R.m, IsLocVec ch.W (.mu t D.R.m j) e (ch.rm.vT D.R.m j) (fun y => if IsHalf e y then ∏ w : locPl ch.G t, φ w (.theta D.R.m j) (ch.S.B.coord t w.1 (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (fd j)) → (∀ i : Fin D.R.m, IsLocVec ch.W (.chi i D.R.m) e (ch.rm.vX i D.R.m) (fun y => if IsHalf e y then ∏ w : locPl ch.G t, φ w (.ex i D.R.m) (ch.S.B.coord t w.1 (X := (i, D.R.m)) (Y := (i + 1, D.R.m)) ⟨i.2.le, le_rfl⟩ ⟨i.2, le_rfl⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (fr i)) → ∃ σ : (PureDat ch.G t × Combs ch.G) →₀ ℂ, (∀ k ∈ σ.support, (∀ j : Fin D.R.m, (k.1.1 j).e = e ∧ IsCombOf ch.W (k.1.1 j) (k.2.1 j)) ∧ ∀ n, (k.1.2 n).e = e ∧ IsCombOf ch.W (k.1.2 n) (k.2.2 n)) ∧ (∀ (u : ∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1)))) (y : ∀ i : Fin D.R.m, WO (ch.G.pS (.chi i D.R.m : Pair T)) (ch.G.pT (.chi i D.R.m : Pair T))), (∀ j, IsHalf e (u j)) → (∀ i, IsHalf e (y i)) → (σ.sum fun k x => x * ((∏ j, (k.1.1 j).fn (u j)) * ∏ n, (k.1.2 n).fn (y n))) = ∏ w : locPl ch.G t, flatTensor one_le_sLen (psiAt ch.W w.1) (unitVol w.1) (moved (locGrid ch.G t w.1) (keepAt ch.G w.1) ((repsAt ch.G t w.1).elt (β w)) ((locGrid ch.G t w.1).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) (φ w))) (ch.S.colAt t w.1 u) (ch.S.rowAt t w.1 y)) ∧ ∀ (P : PolDown ch.G) (p : Pts ch.G), IsRealPt p → ∀ (u : ColPt ch.G) (y : RowPt ch.G), evT (conAt ch.W hM (fockD ch.W t fd P) (p * b)) fr u y = (∏ w, ζ w) * σ.sum fun k x => x * evT (combC ch.W k.2 (conAt ch.W hM (fockD ch.W t (fun j => ch.rm.vT D.R.m j) P) (p * b₀))) (combR ch.rm k.2) u y := by
  refine big_mono (fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch h => ?_) ((GlobalTheory.T.rowData_localPureTensors_largeDepth.and GlobalTheory.T.flatTensor_rowFactor_largeDepth).and (GlobalTheory.T.columnFlatTensor_expansion_largeDepth.and GlobalTheory.T.rowTest_columnInduction_localToGlobalExpansion))
  obtain ⟨⟨hR, hF⟩, hL, hC⟩ := h
  intro s t β ζ hζ M hM b b₀ hb hb₀ e he φ hφ fd fr hfd hfr
  obtain ⟨dr, cr, hdr, hcr, hdrfn⟩ := hR t e he φ fr hfr
  have heL : ∀ w : locPl ch.G t, ∃ eL, IsIdemSum eL {w.1} := fun w => exists_idemSum_singleton e _ he w.1 w.2
  choose eL heL using heL
  have hloc := fun w : locPl ch.G t => hL t β w (eL w) (heL w) (φ w) (hφ w)
  choose I S x d c hdc hexp using hloc
  obtain ⟨J, SJ, xJ, dJ, cJ, hJ, hJexp, hJev⟩ :=
    hC s t β ζ hζ M hM b b₀ hb hb₀ e he φ hφ fd hfd eL heL I S x d c hdc hexp
  let key : J → PureDat ch.G t × Combs ch.G := fun a => ((dJ a, dr), (cJ a, cr))
  have hsum : ∀ F : PureDat ch.G t × Combs ch.G → ℂ,
      ((∑ a ∈ SJ, Finsupp.single (key a) (xJ a)).sum fun k x => x * F k) = ∑ a ∈ SJ, xJ a * F (key a) := by
    intro F
    rw [← Finsupp.sum_finsetSum_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
    exact Finset.sum_congr rfl fun a _ => Finsupp.sum_single_index (zero_mul _)
  refine ⟨∑ a ∈ SJ, Finsupp.single (key a) (xJ a), ?_, ?_, ?_⟩
  · intro k hk
    obtain ⟨a, ha, hk'⟩ := Finset.mem_biUnion.1 (Finsupp.support_finsetSum hk)
    rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hk')]
    exact ⟨fun j => hJ a ha j, fun n => hdr n⟩
  · intro u y hu hy
    rw [hsum]
    have hrow : ∏ n, (dr n).fn (y n) = ∏ n : Fin D.R.m, ∏ w : locPl ch.G t, φ w (.ex n D.R.m)
        (ch.S.B.coord t w.1 (X := (n, D.R.m)) (Y := (n + 1, D.R.m)) ⟨n.2.le, le_rfl⟩ ⟨n.2, le_rfl⟩
          ((y n).map fun a => cpt w.1 (toEAf D a))) :=
      Finset.prod_congr rfl fun n _ => hdrfn n (y n) (hy n)
    calc (∑ a ∈ SJ, xJ a * ((∏ j, ((key a).1.1 j).fn (u j)) * ∏ n, ((key a).1.2 n).fn (y n)))
        = (∑ a ∈ SJ, xJ a * ∏ j, (dJ a j).fn (u j)) * ∏ n, (dr n).fn (y n) := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun a _ => by simp only [key]; ring
      _ = _ := by
          rw [hJexp u hu, hrow, Finset.prod_comm, ← Finset.prod_mul_distrib]
          exact Finset.prod_congr rfl fun w _ => (hF t β w (φ w) (hφ w) u y).symm
  · intro P p hp u y
    rw [hsum]
    have hev : ∀ (C : BiFam ch.G) (f : SchRow ch.G), evT C f u y = evT C 1 u 0 * ∏ i, f i (y i) := by
      intro C f
      simp only [evT, Pi.one_apply, Finset.prod_const_one, mul_one]
    have hcomb : ∀ a (C₀ : BiFam ch.G), evT (combC ch.W (key a).2 C₀) (combR ch.rm (key a).2) u y =
        evT (combC ch.W (cJ a, 0) C₀) 1 u 0 * ∏ i, fr i (y i) := by
      intro a C₀
      rw [hev]
      congr 1
      exact Finset.prod_congr rfl fun i _ => by simp only [key, combR, hcr i]
    rw [hev, hJev P p hp u, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => by rw [hcomb a]; ring

end GlobalTheory.LocAsm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalPureTensorProductExpansionAllPlacesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localPureTensor_product_expansion_all_places : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (s : ℤˣ) (t : T) (β : CosFam ch.G t) (ζ : locPl ch.G t → ℂ), (∀ w : locPl ch.G t, GlobalTheory.LocAsm.PlaceCl ch s t w (β w) (ζ w)) → ∀ (M : Vol ch.G) (hM : M.Is t) (b b₀ : Pts ch.G), IsRep t ch.S.B s β b → IsBase t ch.S.B b₀ → ∀ e : AE D, IsIdemSum e (locPl ch.G t) → ∀ (φ : (∀ w : locPl ch.G t, ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w.1).rank b.tgt)) (Fin ((locGrid ch.G t w.1).rank b.src)) (Kw w.1) → ℂ)), (∀ w : locPl ch.G t, ∀ b ∈ GlobalTheory.SplitFlip.oppositePath D.R.m, GlobalTheory.SplitFlip.IsNatDatum (unifAt w.1) (depthAt ch.G w.1) (φ w b)) → ∀ (fd : SchDown ch.G t) (fr : SchRow ch.G), (∀ j : Fin D.R.m, IsLocVec ch.W (.mu t D.R.m j) e (ch.rm.vT D.R.m j) (fun y => if IsHalf e y then ∏ w : locPl ch.G t, φ w (.theta D.R.m j) (ch.S.B.coord t w.1 (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (fd j)) → (∀ i : Fin D.R.m, IsLocVec ch.W (.chi i D.R.m) e (ch.rm.vX i D.R.m) (fun y => if IsHalf e y then ∏ w : locPl ch.G t, φ w (.ex i D.R.m) (ch.S.B.coord t w.1 (X := (i, D.R.m)) (Y := (i + 1, D.R.m)) ⟨i.2.le, le_rfl⟩ ⟨i.2, le_rfl⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (fr i)) → ∃ σ : (PureDat ch.G t × Combs ch.G) →₀ ℂ, (∀ k ∈ σ.support, (∀ j : Fin D.R.m, (k.1.1 j).e = e ∧ IsCombOf ch.W (k.1.1 j) (k.2.1 j)) ∧ ∀ n, (k.1.2 n).e = e ∧ IsCombOf ch.W (k.1.2 n) (k.2.2 n)) ∧ (∀ (u : ∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1)))) (y : ∀ i : Fin D.R.m, WO (ch.G.pS (.chi i D.R.m : Pair T)) (ch.G.pT (.chi i D.R.m : Pair T))), (∀ j, IsHalf e (u j)) → (∀ i, IsHalf e (y i)) → (σ.sum fun k x => x * ((∏ j, (k.1.1 j).fn (u j)) * ∏ n, (k.1.2 n).fn (y n))) = ∏ w : locPl ch.G t, flatTensor one_le_sLen (psiAt ch.W w.1) (unitVol w.1) (moved (locGrid ch.G t w.1) (keepAt ch.G w.1) ((repsAt ch.G t w.1).elt (β w)) ((locGrid ch.G t w.1).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) (φ w))) (ch.S.colAt t w.1 u) (ch.S.rowAt t w.1 y)) ∧ ∀ (P : PolDown ch.G) (p : Pts ch.G), IsRealPt p → ∀ (u : ColPt ch.G) (y : RowPt ch.G), evT (conAt ch.W hM (fockD ch.W t fd P) (p * b)) fr u y = (∏ w, ζ w) * σ.sum fun k x => x * evT (combC ch.W k.2 (conAt ch.W hM (fockD ch.W t (fun j => ch.rm.vT D.R.m j) P) (p * b₀))) (combR ch.rm k.2) u y := by
  first | exact @GlobalTheory.LocAsm.oneProduct | exact GlobalTheory.LocAsm.oneProduct | (intros; apply GlobalTheory.LocAsm.oneProduct <;> assumption)
end
