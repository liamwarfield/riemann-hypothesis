module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyFlatFinrank
public import Lean
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DifferentiableThetaLocalSum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenRankSelfDualUnitary
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacRowScalar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletedGridArrowLatticeIffIntegralFrameMatr
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurePreservingMulRight

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CarryWeilUnitaryPair
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

namespace GlobalTheory.RowEx.CarryWeil

open GlobalTheory.ChiGrid GlobalTheory.FunObj
open scoped ComplexOrder

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem gram_posDef_def (G : GridData L sc) {Y : Node} (hY : DefNode D.R.m Y) (τ : D.what₂.Tau) :
    (gramAt D (G.V Y) τ).PosDef := by
  rcases Y with ⟨_ | i, j⟩ | i | j
  · obtain ⟨-, rfl⟩ := hY
    have e : G.V (.grid 0 D.R.m) = D.sp.X' := congrArg LSp.sp (colY_m L)
    rw [e]
    exact GlobalTheory.Hk3.StepX.gram_posDef_X τ
  · obtain ⟨hi, rfl⟩ := hY
    have hV := G.isV (X := .grid (i + 1) D.R.m) ⟨hi, le_rfl⟩ (fun j h => by cases h)
    have := hV.sigOK (tauE D τ)
    rw [hV.sig] at this
    simp only [Node.neg, Nat.sub_self, Nat.zero_div] at this
    exact GlobalTheory.DefiniteQuotient.posDef_of_signature this
  · exact hY.elim
  · have hV := G.isV (X := .top j) hY (fun j h => by cases h)
    have := hV.sigOK (tauE D τ)
    rw [hV.sig] at this
    simp only [Node.neg] at this
    exact GlobalTheory.DefiniteQuotient.posDef_of_signature this

theorem cart_def (G : GridData L sc) (W : G.Weil) {Y : Node} (hY : DefNode D.R.m Y) : W.cart Y = fun _ => 1 := by
  funext τ
  have hr : Y.InRange D.R.m := by
    rcases Y with ⟨i, j⟩ | i | j <;> simp only [DefNode, Node.InRange] at hY ⊢ <;> omega
  have hpos := gram_posDef_def G hY τ
  exact GlobalTheory.StdUnn.isCartanInv_eq_of_commute _ _ _ _ (W.cart_is Y hr τ) ⟨Matrix.mul_one 1, by simp, by simpa using hpos⟩
    (by simp)

theorem heq_one {V V' : HSp D} (h : V' = V) :
    HEq (fun _ : D.what₂.Tau => (1 : Matrix (Fin V'.rank) (Fin V'.rank) ℂ))
      (fun _ : D.what₂.Tau => (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ)) := by
  subst h; rfl

theorem attChr_congr {C : Type} [CommGroup C] {a a' b b' : C} {n n' : ℕ} (h1 : a = a') (h2 : b = b') (h3 : n = n') :
    Formalism.IndefR.Lift.attChr a b n = Formalism.IndefR.Lift.attChr a' b' n' := by
  subst h1 h2 h3; rfl

section Transport

open GlobalTheory.Mem

theorem exists_om_tr {X X' : Stages} (h : X'.B.toPre = X.B.toPre) {ψ : AddChar (AF X.toD7.host.F) ℂ} {S T : HSp X.toD7}
    {χS χT : (AE X.toD7)ˣ →* Circle} {ω : GA X.toD7 S × GA X.toD7 T →* Module.End ℂ (WO S T → ℂ)}
    {ψ' : AddChar (AF X'.toD7.host.F) ℂ} {S' T' : HSp X'.toD7} {χS' χT' : (AE X'.toD7)ˣ →* Circle}
    (hψ : HEq ψ' ψ) (hS : HEq S' S) (hT : HEq T' T) (h1 : HEq χS' χS) (h2 : HEq χT' χT)
    (hw : IsWeilDatumO ψ S T χS χT ω) :
    ∃ ω' : GA X'.toD7 S' × GA X'.toD7 T' →* Module.End ℂ (WO S' T' → ℂ), IsWeilDatumO ψ' S' T' χS' χT' ω' ∧ HEq ω' ω := by
  obtain ⟨B, C, Wr, V, Sg, N, Gj⟩ := X
  obtain ⟨B', C', Wr', V', Sg', N', Gj'⟩ := X'
  cases B; cases B'
  dsimp only at h
  subst h
  obtain rfl := eq_of_heq hψ
  obtain rfl := eq_of_heq hS
  obtain rfl := eq_of_heq hT
  obtain rfl := eq_of_heq h1
  obtain rfl := eq_of_heq h2
  refine ⟨ω, ?_, HEq.rfl⟩
  exact
    { std := (by with_unfolding_all exact (hw.std :))
      hecS := (by with_unfolding_all exact (hw.hecS :))
      hecT := (by with_unfolding_all exact (hw.hecT :))
      resS := (by with_unfolding_all exact (hw.resS :))
      resT := (by with_unfolding_all exact (hw.resT :))
      om_pres := fun p f hf =>
        have r := hw.om_pres p f ⟨(by with_unfolding_all exact (hf.quasi :)), (by with_unfolding_all exact (hf.level :)), (by with_unfolding_all exact (hf.cont :)), (by with_unfolding_all exact (hf.smooth :))⟩
        ⟨(by with_unfolding_all exact (r.quasi :)), (by with_unfolding_all exact (r.level :)), (by with_unfolding_all exact (r.cont :)), (by with_unfolding_all exact (r.smooth :))⟩
      om_heis := fun g h w₀ f hf => hw.om_heis g h w₀ f ⟨(by with_unfolding_all exact (hf.quasi :)), (by with_unfolding_all exact (hf.level :)), (by with_unfolding_all exact (hf.cont :)), (by with_unfolding_all exact (hf.smooth :))⟩
      om_aut := fun γ hγ γ' hγ' f hf => hw.om_aut γ hγ γ' hγ' f ⟨(by with_unfolding_all exact (hf.quasi :)), (by with_unfolding_all exact (hf.level :)), (by with_unfolding_all exact (hf.cont :)), (by with_unfolding_all exact (hf.smooth :))⟩
      om_cont := fun f hf => hw.om_cont f ⟨(by with_unfolding_all exact (hf.quasi :)), (by with_unfolding_all exact (hf.level :)), (by with_unfolding_all exact (hf.cont :)), (by with_unfolding_all exact (hf.smooth :))⟩
      om_unit := fun μ 𝓕 hμ h𝓕 p f hf => hw.om_unit μ 𝓕 hμ h𝓕 p f ⟨(by with_unfolding_all exact (hf.quasi :)), (by with_unfolding_all exact (hf.level :)), (by with_unfolding_all exact (hf.cont :)), (by with_unfolding_all exact (hf.smooth :))⟩
      om_split := fun e he g h hg hh x y hx hy => by
        obtain ⟨r, hr, hℓ⟩ := hw.om_split e he g h hg hh x y hx hy
        exact ⟨r, hr, fun ℓ hℓ' f hf => hℓ ℓ (fun u hu f' hf' => hℓ' u hu f' ⟨(by with_unfolding_all exact (hf'.quasi :)), (by with_unfolding_all exact (hf'.level :)), (by with_unfolding_all exact (hf'.cont :)), (by with_unfolding_all exact (hf'.smooth :))⟩) f ⟨(by with_unfolding_all exact (hf.quasi :)), (by with_unfolding_all exact (hf.level :)), (by with_unfolding_all exact (hf.cont :)), (by with_unfolding_all exact (hf.smooth :))⟩⟩ }

end Transport

end GlobalTheory.RowEx.CarryWeil


open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowEx.CarryWeil in
theorem GlobalTheory.RowEx.carryW_of_weil : GlobalTheory.Published.WeilRepresentationUnitaryPair → CarryW := by
  intro hW X X' T T' L Γ _ _ Pl0 A Ks _ _ _ R μ₀ ι hL hch hmod sc G G' hG W
  obtain ⟨W1, hW1⟩ := GlobalTheory.ChiGrid.WeilOver.exists_weil_over_of_clauses hW R hL.is' hch hmod sc G'
  have hm : X'.toD7.R.m = X.toD7.R.m := by
    have hpre := hL.pre
    obtain ⟨B, C, Wr, V, S, N, Gj⟩ := X
    obtain ⟨B', C', Wr', V', S', N', Gj'⟩ := X'
    cases B; cases B'
    dsimp only at hpre
    subst hpre
    rfl
  have F1 : HEq W1.ψ W.ψ := by
    have hpre := hL.pre
    obtain ⟨B, C, Wr, V, S, N, Gj⟩ := X
    obtain ⟨B', C', Wr', V', S', N', Gj'⟩ := X'
    cases B; cases B'
    dsimp only at hpre
    subst hpre
    exact heq_of_eq ((GlobalTheory.StdAdelicChar.existsUnique_isStdChar _ (-1) (Or.inr rfl)).unique W1.ψ_std ((by with_unfolding_all exact (W.ψ_std :))))
  have F2 : HEq W1.θ W.θ := by
    have hpre := hL.pre
    obtain ⟨B, C, Wr, V, S, N, Gj⟩ := X
    obtain ⟨B', C', Wr', V', S', N', Gj'⟩ := X'
    cases B; cases B'
    dsimp only at hpre
    subst hpre
    exact heq_of_eq ((GlobalTheory.SmoothForms.RealPts.realPoints _).1 _ _ W1.θ_is ((by with_unfolding_all exact (W.θ_is :))))
  have F3 : ∀ Y, DefNode X'.toD7.R.m Y → HEq (W1.cart Y) (W.cart Y) := by
    intro Y hY
    rw [cart_def G' W1 hY, cart_def G W (hm ▸ hY)]
    have hV : HEq (G'.V Y) (G.V Y) := by
      rcases Y with ⟨_ | i, j⟩ | i | j
      · obtain ⟨-, rfl⟩ := hY
        have hpre := hL.pre
        obtain ⟨B, C, Wr, V, S, N, Gj⟩ := X
        obtain ⟨B', C', Wr', V', S', N', Gj'⟩ := X'
        cases B; cases B'
        dsimp only at hpre
        subst hpre
        exact heq_of_eq ((congrArg LSp.sp (colY_m _)).trans (congrArg LSp.sp (colY_m L)).symm)
      · exact (hG.grid i j).1
      · exact hY.elim
      · exact (hG.top j).1
    have hpre := hL.pre
    obtain ⟨B, C, Wr, V, S, N, Gj⟩ := X
    obtain ⟨B', C', Wr', V', S', N', Gj'⟩ := X'
    cases B; cases B'
    dsimp only at hpre
    subst hpre
    exact heq_one (eq_of_heq hV)
  have F4 : ∀ p, DefPair X'.toD7.R.m p → ∃ ω, IsWeilDatumO W1.ψ (G'.pS p) (G'.pT p) (G'.chrS p) (G'.chrT p) ω ∧
      HEq ω (W.om (mapPair ι p)) := by
    intro p hp
    have hr : (mapPair ι p).InRange X.toD7.R.m := by
      rw [← hm]
      rcases p with ⟨i, j⟩ | ⟨t, i, j⟩ | i | ⟨t, j⟩ <;>
        simp only [DefPair, mapPair, Pair.InRange, Pair.big, Node.InRange] at hp ⊢ <;> omega
    have key : HEq (G'.pS p) (G.pS (mapPair ι p)) ∧ HEq (G'.pT p) (G.pT (mapPair ι p)) ∧
        HEq (G'.chrS p) (G.chrS (mapPair ι p)) ∧ HEq (G'.chrT p) (G.chrT (mapPair ι p)) := by
      have eta := hL.is.eta
      have eta' := hL.is'.eta
      have mu0 := hL.is.mu0
      have mu0' := hL.is'.mu0
      have xi := hL.is.xi
      have xi' := hL.is'.xi
      have hxi := hL.xi
      obtain ⟨f, f', hff, hC, hC'⟩ := hL.C
      have hpre := hL.pre
      obtain ⟨B, C, Wr, V, S, N, Gj⟩ := X
      obtain ⟨B', C', Wr', V', S', N', Gj'⟩ := X'
      cases B; cases B'
      dsimp only at hpre
      subst hpre
      obtain rfl := eq_of_heq hff
      rw [hC] at eta mu0
      rw [hC'] at eta' mu0'
      have eEta : R.toLevCh.eta = L.eta := (GlobalTheory.ChrEqUnique.chrEq_unique _).2.1 _ _ _ eta' ((by with_unfolding_all exact (eta :)))
      rcases p with ⟨i, j⟩ | ⟨t, i, j⟩ | i | ⟨t, j⟩
      · obtain ⟨hi, hj⟩ := hp
        have hS1 : G'.V (.grid (i + 1) j) = G.V (.grid (i + 1) j) := eq_of_heq (hG.grid i j).1
        have hT1 : G'.V (.grid i j) = G.V (.grid i j) := by
          cases i with
          | zero =>
            subst hj
            exact (congrArg LSp.sp (colY_m _)).trans (congrArg LSp.sp (colY_m L)).symm
          | succ k => exact eq_of_heq (hG.grid k j).1
        have ech := eq_of_heq hG.chi
        exact ⟨heq_of_eq (congrArg negSp hS1), heq_of_eq hT1,
          heq_of_eq (attChr_congr (congrFun ech _) eEta (congrArg (fun V : HSp _ => (negSp V).rank) hS1)),
          heq_of_eq (attChr_congr (congrFun ech _) eEta (congrArg (fun V : HSp _ => V.rank) hT1))⟩
      · exact hp.elim
      · exact hp.elim
      · have hj := Nat.lt_of_succ_le hp
        have emu : R.toLevCh.mu0 (j + 1) = L.mu0 (j + 1) :=
          (GlobalTheory.ChrEqUnique.chrEq_unique _).2.1 _ _ _ (mu0' ⟨j, hj⟩) ((by with_unfolding_all exact ((mu0 ⟨j, hj⟩) :)))
        have exi : R.toLevCh.xi t = L.xi (ι t) := by
          have h1 := xi (ι t)
          have h2 := xi' t
          rw [eq_of_heq (hxi t)] at h2
          exact (GlobalTheory.ChrEqUnique.chrEq_unique _).2.1 _ _ _ h2 ((by with_unfolding_all exact (h1 :)))
        have hS1 : G'.V (.top j) = G.V (.top j) := eq_of_heq (hG.top j).1
        have hT1 : G'.V (.top (j + 1)) = G.V (.top (j + 1)) := eq_of_heq (hG.top (j + 1)).1
        have emu' : R.toLevCh.mu t (j + 1) = L.mu (ι t) (j + 1) := congrArg₂ (· * ·) emu exi
        exact ⟨heq_of_eq hS1, heq_of_eq hT1,
          heq_of_eq (attChr_congr emu' eEta (congrArg (fun V : HSp _ => V.rank) hS1)),
          heq_of_eq (attChr_congr emu' eEta (congrArg (fun V : HSp _ => V.rank) hT1))⟩
    exact exists_om_tr hL.pre F1 key.1 key.2.1 key.2.2.1 key.2.2.2 (W.om_is (mapPair ι p) hr)
  have key : ∀ p : Pair T', ∃ ω, (p.InRange X'.toD7.R.m →
      IsWeilDatumO W1.ψ (G'.pS p) (G'.pT p) (G'.chrS p) (G'.chrT p) ω) ∧
      (DefPair X'.toD7.R.m p → HEq ω (W.om (mapPair ι p))) ∧ (¬ DefPair X'.toD7.R.m p → ω = W1.om p) := by
    intro p
    by_cases hp : DefPair X'.toD7.R.m p
    · obtain ⟨ω, h1, h2⟩ := F4 p hp
      exact ⟨ω, fun _ => h1, fun _ => h2, fun h => absurd hp h⟩
    · exact ⟨W1.om p, W1.om_is p, fun h => absurd h hp, fun _ => rfl⟩
  choose om hom hdef hnd using key
  refine ⟨{ W1 with om := om, om_is := hom }, ?_, F1, F2, F3, hdef⟩
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hW1
  refine ⟨a1, a2, a3, a4, a5, a6, fun t k hk => ?_, fun t k hk => ?_⟩
  · show HEq (om (.mu t 0 k)) _
    rw [hnd (.mu t 0 k) (fun h => h)]
    exact a7 t k hk
  · show HEq (om (.mu t 0 k)) _
    rw [hnd (.mu t 0 k) (fun h => h)]
    exact a8 t k hk

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetScalarRationalTranslate
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

noncomputable section

namespace GlobalTheory.RatMoveJets

theorem unitAt_mul {q : ℕ} [Fact q.Prime] {a b : ℂ} (ha : Mod1All a) (hb : Mod1All b) (hua : GlobalTheory.MovedKappaEx.UnitAt q a)
    (hub : GlobalTheory.MovedKappaEx.UnitAt q b) : GlobalTheory.MovedKappaEx.UnitAt q (a * b) := by
  obtain ⟨ha', -⟩ := ha
  obtain ⟨hb', -⟩ := hb
  intro lam
  have hab : a * b ∈ Qbar := mul_mem ha' hb'
  have e : lamC lam (a * b) = lamC lam a * lamC lam b := by
    unfold lamC
    rw [dite_eq_left hab, dite_eq_left ha', dite_eq_left hb', ← map_mul]
    rfl
  rw [e, norm_mul, hua lam, hub lam, one_mul]

end GlobalTheory.RatMoveJets
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChiArrowPairMovesStandardVacuumByScalar
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChiArrowPairMovesStandardVacuumByScalar
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.RowChiVac

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem vac_chi_scalar : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {i : ℕ}, i + 1 ≤ D.R.m → ∀ (x : FinPt G (.grid i D.R.m)) (y : FinPt G (.grid (i + 1) D.R.m)), (∀ u, u ∈ latO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) (S.N.latS (.chi i D.R.m) : Set _) (S.N.latT (.chi i D.R.m) : Set _) (fun _ => True) ↔ actO _ _ (G.toPair (.chi i D.R.m) x y).1 (G.toPair (.chi i D.R.m) x y).2 u ∈ latO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) (S.N.latS (.chi i D.R.m) : Set _) (S.N.latT (.chi i D.R.m) : Set _) (fun _ => True)) → ∃ c : ℂ, W.om (.chi i D.R.m) (G.toPair (.chi i D.R.m) x y) (S.Z.vac (.chi i D.R.m)) = c • S.Z.vac (.chi i D.R.m) := by
  intro D T L sc G W U S i hi x y hlat
  have hp : DefPair D.R.m (Pair.chi i D.R.m : Pair T) := ⟨hi, rfl⟩
  have hom := W.om_is (.chi i D.R.m) (by simp only [Pair.InRange, Pair.big, Node.InRange]; omega)
  have m1 : (G.toPair (.chi i D.R.m) x y).1 ∈ GfC _ := GlobalTheory.LastRowVac.negGA_mem _ y.2
  have m2 : (G.toPair (.chi i D.R.m) x y).2 ∈ GfC _ := x.2
  have hΛ : ∀ u, u ∈ latO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) (S.N.latS (.chi i D.R.m) : Set _)
        (S.N.latT (.chi i D.R.m) : Set _) (fun _ => True) ↔
      ∃ u₀ ∈ latO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) (S.N.latS (.chi i D.R.m) : Set _)
        (S.N.latT (.chi i D.R.m) : Set _) (fun _ => True),
        u = actO _ _ (G.toPair (.chi i D.R.m) x y).1 (G.toPair (.chi i D.R.m) x y).2 u₀ := by
    intro u
    have e := GlobalTheory.WeilVacMove.actO_inv_actO (G.toPair (.chi i D.R.m) x y).1⁻¹ (G.toPair (.chi i D.R.m) x y).2⁻¹ u
    rw [inv_inv, inv_inv] at e
    constructor
    · intro hu
      refine ⟨actO _ _ (G.toPair (.chi i D.R.m) x y).1⁻¹ (G.toPair (.chi i D.R.m) x y).2⁻¹ u, (hlat _).2 ?_, e.symm⟩
      rw [e]
      exact hu
    · rintro ⟨u₀, hu₀, rfl⟩
      exact (hlat u₀).1 hu₀
  have hv' := GlobalTheory.WeilVacMove.isVacO_om D W.ψ W.θ _ _ _ _ (W.om _) hom W.θ_is _ _ _ _ _ _ _ _
    (G.toPair (.chi i D.R.m) x y).1 (G.toPair (.chi i D.R.m) x y).2
    (fun τ => by rw [GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC W.θ _ m1, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC W.θ _ m2, Matrix.mul_one, Matrix.one_mul])
    hΛ _ (S.Z.vac_is _ hp)
  obtain ⟨c, -, hc⟩ := GlobalTheory.LastRowVac.eq_smul_vac S hp _ hv'
  exact ⟨c, hc⟩

end GlobalTheory.RowChiVac

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChiArrowPairMovesStandardVacuumByScalarStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chiArrowPair_moves_standardVacuum_by_scalar : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {i : ℕ}, i + 1 ≤ D.R.m → ∀ (x : FinPt G (.grid i D.R.m)) (y : FinPt G (.grid (i + 1) D.R.m)), (∀ u, u ∈ latO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) (S.N.latS (.chi i D.R.m) : Set _) (S.N.latT (.chi i D.R.m) : Set _) (fun _ => True) ↔ actO _ _ (G.toPair (.chi i D.R.m) x y).1 (G.toPair (.chi i D.R.m) x y).2 u ∈ latO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) (S.N.latS (.chi i D.R.m) : Set _) (S.N.latT (.chi i D.R.m) : Set _) (fun _ => True)) → ∃ c : ℂ, W.om (.chi i D.R.m) (G.toPair (.chi i D.R.m) x y) (S.Z.vac (.chi i D.R.m)) = c • S.Z.vac (.chi i D.R.m) := by
  first | exact @GlobalTheory.RowChiVac.vac_chi_scalar | exact GlobalTheory.RowChiVac.vac_chi_scalar | (intros; apply GlobalTheory.RowChiVac.vac_chi_scalar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GivenStageFunctionRowArrowEqHalfExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GivenStageFunctionRowArrowEqHalfExtension
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.CosetRow


open Classical in
theorem givenFn_right_eq_extFn {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}
    (hL : L.Is μ₀) (B : Frames G) (t : T) (Φ : G.Datum) {e e₀ : AE D} (he : IsIdemSum e (locPl G t))
    (he₀ : IsIdemSum e₀ G.pl.W0)
    (hAA : ∀ w ∈ L.Q t, w ∉ G.pl.W0 → ((∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧
      ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1)) (i : Fin D.R.m) :
    GlobalTheory.FlipStart.givenFn B t Φ e (.right i 0) = GlobalTheory.CosetRow.extFn e₀ (e - e₀)
      (latO (G.pS (.chi (i : ℕ) 0)) (G.pT (.chi (i : ℕ) 0)) (G.latS (.chi (i : ℕ) 0) : Set _)
        (G.latT (.chi (i : ℕ) 0) : Set _) fun _ => True) (cosInd e₀ (Φ i)) := by
  have hsub : G.pl.W0 ⊆ locPl G t := Finset.subset_union_left
  obtain ⟨he₁, h01⟩ := GlobalTheory.T.isIdemSum_sub_of_subset_and_orthogonal he he₀ hsub
  have hee : e₀ + (e - e₀) = e := add_sub_cancel e₀ e
  have h0 := GlobalTheory.PlaceDatum.idemSum_mul_self he₀
  have h1 := GlobalTheory.PlaceDatum.idemSum_mul_self he₁
  obtain ⟨-, c0, -⟩ := GlobalTheory.FunObj.Comparison₂.cpt_idemSum he₀
  obtain ⟨-, c1, -⟩ := GlobalTheory.FunObj.Comparison₂.cpt_idemSum he₁
  have hAA' : ∀ w ∈ locPl G t \ G.pl.W0, ((∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧
      ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1) := fun w hw => by
    rw [Finset.mem_sdiff] at hw
    exact hAA w ((Finset.mem_union.1 hw.1).resolve_left hw.2) hw.2

  have hmap : ∀ (a : AE D) (w : Pl D.host.E), cpt (D := D) w (toEAf D a) = 1 →
      ∀ x : WO (G.pS (.chi (i : ℕ) 0)) (G.pT (.chi (i : ℕ) 0)),
      (a • x).map (cpt (D := D) w ∘ toEAf D) = x.map (cpt (D := D) w ∘ toEAf D) := fun a w ha x => by
    ext p q
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Function.comp_apply, RingHom.map_mul, ha, one_mul]
  funext x
  unfold GlobalTheory.FlipStart.givenFn GlobalTheory.CosetRow.extFn
  rw [hee]
  by_cases hx : IsHalf e x
  swap
  · rw [if_neg hx, if_neg hx]
  rw [if_pos hx, if_pos hx]

  have hfac : ∀ w, givenDatum t w B Φ (edgeOf (.right i 0)) (locArg B t w (.right i 0) x) =
      if B.coord t w (X := ((i : ℕ), 0)) (Y := ((i : ℕ) + 1, 0)) ⟨i.2.le, Nat.zero_le _⟩ ⟨i.2, Nat.zero_le _⟩
        (x.map (cpt (D := D) w ∘ toEAf D)) ∈ cosetSet t w B i.2 (Φ i) then 1 else 0 := fun w => by
    have hh : (i : ℕ) < D.R.m ∧ 0 ≤ D.R.m := ⟨i.2, Nat.zero_le _⟩
    have hla : locArg B t w (.right i 0) x = B.coord t w (X := ((i : ℕ), 0)) (Y := ((i : ℕ) + 1, 0))
        ⟨i.2.le, Nat.zero_le _⟩ ⟨i.2, Nat.zero_le _⟩ (x.map (cpt (D := D) w ∘ toEAf D)) := by
      exact dif_pos hh
    rw [hla]
    simp only [edgeOf, givenDatum, dif_pos i.2, Set.indicator_apply, Pi.one_apply, Fin.eta]
  rw [Finset.prod_congr rfl fun w _ => hfac w, ← Finset.prod_sdiff hsub, Finset.prod_boole, Finset.prod_boole]
  have hx0 : IsHalf e₀ (e₀ • x) := fun p q => by
    simp only [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, h0]
  have hx1 : IsHalf (e - e₀) ((e - e₀) • x) := fun p q => by
    simp only [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, h1]
  have k0 : cosInd e₀ (Φ i) (e₀ • x) = if ∀ w ∈ G.pl.W0, B.coord t w (X := ((i : ℕ), 0)) (Y := ((i : ℕ) + 1, 0))
      ⟨i.2.le, Nat.zero_le _⟩ ⟨i.2, Nat.zero_le _⟩ (x.map (cpt (D := D) w ∘ toEAf D)) ∈ cosetSet t w B i.2 (Φ i)
      then 1 else 0 := by
    unfold cosInd
    rw [Set.indicator_apply, Pi.one_apply]
    refine if_congr ?_ rfl rfl
    rw [GlobalTheory.FunObj.Comparison₂.mem_cosSet_iff_cosetSet B t hL he₀ i.2 (Φ i) hx0]
    exact forall₂_congr fun w hw => by rw [hmap e₀ w (c0 w hw)]
  have k1 : halfInd (e - e₀) (latO (G.pS (.chi (i : ℕ) 0)) (G.pT (.chi (i : ℕ) 0)) (G.latS (.chi (i : ℕ) 0) : Set _)
        (G.latT (.chi (i : ℕ) 0) : Set _) fun _ => True) ((e - e₀) • x) = if ∀ w ∈ locPl G t \ G.pl.W0,
      B.coord t w (X := ((i : ℕ), 0)) (Y := ((i : ℕ) + 1, 0))
      ⟨i.2.le, Nat.zero_le _⟩ ⟨i.2, Nat.zero_le _⟩ (x.map (cpt (D := D) w ∘ toEAf D)) ∈ cosetSet t w B i.2 (Φ i)
      then 1 else 0 := by
    unfold halfInd
    refine if_congr ?_ rfl rfl
    rw [and_iff_left hx1, GlobalTheory.T.mem_completedGridArrowLattice_iff_integral_frameMatrix hL B t he₁ hAA' i _ hx1]
    refine forall₂_congr fun w hw => ?_
    rw [hmap _ w (c1 w hw), GlobalTheory.FunObj.Comparison₂.cosetSet_of_notMem B t w hL (Finset.mem_sdiff.1 hw).2 i.2 (Φ i)]
    rfl
  rw [k0, k1, mul_comm]

end GlobalTheory.CosetRow
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GivenStageFunctionRowArrowEqHalfExtensionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.givenStageFunction_rowArrow_eq_halfExtension : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (B : Frames G) (t : T) (Φ : G.Datum) {e e₀ : AE D}, IsIdemSum e (locPl G t) → IsIdemSum e₀ G.pl.W0 → (∀ w ∈ L.Q t, w ∉ G.pl.W0 → ((∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧ ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1)) → ∀ (i : Fin D.R.m), GlobalTheory.FlipStart.givenFn B t Φ e (.right i 0) = GlobalTheory.CosetRow.extFn e₀ (e - e₀) (latO (G.pS (.chi (i : ℕ) 0)) (G.pT (.chi (i : ℕ) 0)) (G.latS (.chi (i : ℕ) 0) : Set _) (G.latT (.chi (i : ℕ) 0) : Set _) fun _ => True) (cosInd e₀ (Φ i)) := by
  first | exact @GlobalTheory.CosetRow.givenFn_right_eq_extFn | exact GlobalTheory.CosetRow.givenFn_right_eq_extFn | (intros; apply GlobalTheory.CosetRow.givenFn_right_eq_extFn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaAtHalfExtensionLatticeIndicatorFn
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaAtHalfExtensionLatticeIndicatorFn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section
namespace GlobalTheory.CosetRow

section ThetaExt
variable {D : D7} {m n : ℕ}

theorem isHalf_add_right_iff {e : AE D} {t x : Mx D m n} (hx : IsHalf e x) :
    IsHalf e (t + x) ↔ IsHalf e t := by
  constructor
  · intro h i j
    have h1 := h i j
    have h2 := hx i j
    simp only [Matrix.add_apply, mul_add] at h1
    linear_combination h1 - h2
  · intro h i j
    have h1 := h i j
    have h2 := hx i j
    simp only [Matrix.add_apply, mul_add]
    linear_combination h1 + h2

theorem smul_of_isHalf {e : AE D} {x : Mx D m n} (hx : IsHalf e x) : e • x = x := by
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact hx i j

theorem smul_eq_zero_of_isHalf {e e' : AE D} (h : e' * e = 0) {x : Mx D m n} (hx : IsHalf e x) : e' • x = 0 := by
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
  rw [← hx i j, ← mul_assoc, h, zero_mul]

theorem isHalf_smul_idem {e : AE D} (he : e * e = e) (t : Mx D m n) : IsHalf e (e • t) := by
  intro i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [← mul_assoc, he]

def extLin (e₀ e₁ : AE D) (Λ : AddSubgroup (Mx D m n)) : (Mx D m n → ℂ) →ₗ[ℂ] (Mx D m n → ℂ) where
  toFun := extFn e₀ e₁ Λ
  map_add' Φ Ψ := by
    funext t
    simp only [extFn, Pi.add_apply]
    split_ifs <;> ring
  map_smul' c Φ := by
    funext t
    simp only [extFn, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

theorem extFn_shift {e₀ e₁ : AE D} (h10 : e₁ * e₀ = 0) (Λ : AddSubgroup (Mx D m n)) (Φ : Mx D m n → ℂ)
    {x : Mx D m n} (hx : IsHalf e₀ x) :
    extFn e₀ e₁ Λ (fun t => Φ (t + x)) = fun t => extFn e₀ e₁ Λ Φ (t + x) := by
  funext t
  have hx' : IsHalf (e₀ + e₁) x := by
    rw [add_comm]; exact GlobalTheory.VecProd.half_add_of_right h10 hx
  simp only [extFn]
  rw [isHalf_add_right_iff hx', smul_add, smul_add, smul_of_isHalf hx, smul_eq_zero_of_isHalf h10 hx, add_zero]

theorem extFn_modul {e₀ e₁ : AE D} (Λ : AddSubgroup (Mx D m n)) (Φ : Mx D m n → ℂ) (g : Mx D m n → ℂ)
    (hg : ∀ t, IsHalf (e₀ + e₁) t → g t = g (e₀ • t)) :
    extFn e₀ e₁ Λ (fun t => g t * Φ t) = fun t => g t * extFn e₀ e₁ Λ Φ t := by
  funext t
  simp only [extFn]
  split_ifs with h
  · rw [hg t h]; ring
  · ring

theorem extFn_halfInd {e₀ e₁ : AE D} (h00 : e₀ * e₀ = e₀) (h11 : e₁ * e₁ = e₁) {Λ : AddSubgroup (Mx D m n)}
    (hΛ0 : ∀ u ∈ Λ, e₀ • u ∈ Λ) (hΛ1 : ∀ u ∈ Λ, e₁ • u ∈ Λ) :
    extFn e₀ e₁ Λ (halfInd e₀ Λ) = halfInd (e₀ + e₁) Λ := by
  funext t
  simp only [extFn, halfInd]
  by_cases ht : IsHalf (e₀ + e₁) t
  · have hdec : t = e₀ • t + e₁ • t := by
      rw [← add_smul, smul_of_isHalf ht]
    have hiff : (e₀ • t ∈ Λ ∧ e₁ • t ∈ Λ) ↔ t ∈ Λ := by
      constructor
      · rintro ⟨h0, h1⟩; rw [hdec]; exact Λ.add_mem h0 h1
      · intro h; exact ⟨hΛ0 t h, hΛ1 t h⟩
    have a0 := isHalf_smul_idem h00 t
    have a1 := isHalf_smul_idem h11 t
    rw [if_pos ht]
    by_cases h0 : e₀ • t ∈ Λ <;> by_cases h1 : e₁ • t ∈ Λ
    · rw [if_pos ⟨h0, a0⟩, if_pos ⟨h1, a1⟩, if_pos ⟨hiff.1 ⟨h0, h1⟩, ht⟩, one_mul]
    · rw [if_pos ⟨h0, a0⟩, if_neg (fun h => h1 h.1), if_neg (fun h => h1 (hiff.2 h.1).2), mul_zero]
    · rw [if_neg (fun h => h0 h.1), if_pos ⟨h1, a1⟩, if_neg (fun h => h0 (hiff.2 h.1).1), zero_mul]
    · rw [if_neg (fun h => h0 h.1), if_neg (fun h => h1 h.1), if_neg (fun h => h0 (hiff.2 h.1).1), zero_mul]
  · simp only [if_neg ht]
    rw [if_neg (fun h => ht h.2)]

theorem isThetaAt_extFn : ∀ {D : D7} {m n : ℕ} {ψ : AddChar (AF D.host.F) ℂ} {B : Mx D m n → Mx D m n → AF D.host.F} {hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ)} {Λ : AddSubgroup (Mx D m n)} {e₀ e₁ : AE D} {f₀ Φ f : Mx D m n → ℂ}, e₀ * e₀ = e₀ → e₁ * e₁ = e₁ → e₀ * e₁ = 0 → (∀ u ∈ Λ, e₀ • u ∈ Λ) → (∀ u ∈ Λ, e₁ • u ∈ Λ) → (∀ t y, IsHalf (e₀ + e₁) t → IsHalf (cA D e₀) y → B t y = B (e₀ • t) y) → (∃ T, IsPlaceModel ψ B hs (e₀ + e₁) Λ 1 f₀ T) → IsThetaAt ψ B hs e₀ Λ 1 f₀ Φ f → IsThetaAt ψ B hs (e₀ + e₁) Λ 1 f₀ (GlobalTheory.CosetRow.extFn e₀ e₁ Λ Φ) f := by
  intro D m n ψ B hs Λ e₀ e₁ f₀ Φ f h00 h11 h01 hΛ0 hΛ1 hB hex h
  have h10 : e₁ * e₀ = 0 := by rw [mul_comm]; exact h01
  have hsb : ∀ Ψ, IsSBHalf e₀ Λ Ψ → IsSBHalf (e₀ + e₁) Λ (extFn e₀ e₁ Λ Ψ) := fun Ψ hΨ =>
    GlobalTheory.T.isSBHalf_halfExtensionLatticeIndicatorFn h00 h11 h01 hΛ0 hΛ1 hΨ
  refine ⟨hex, fun T hT => ?_⟩
  have hT₀ : IsPlaceModel ψ B hs e₀ Λ 1 f₀ (T ∘ₗ extLin e₀ e₁ Λ) := by
    refine ⟨fun Ψ hΨ x hx => ?_, fun Ψ hΨ y hy => ?_, ?_⟩
    · have hx' : IsHalf (e₀ + e₁) x := by
        rw [add_comm]; exact GlobalTheory.VecProd.half_add_of_right h10 hx
      simp only [LinearMap.comp_apply]
      change T (extFn e₀ e₁ Λ (fun t => Ψ (t + x))) = hs x (T (extFn e₀ e₁ Λ Ψ))
      rw [extFn_shift h10 Λ Ψ hx]
      exact hT.trans _ (hsb Ψ hΨ) x hx'
    · have hy' : IsHalf (cA D (e₀ + e₁)) y := by
        rw [add_comm]; exact GlobalTheory.VecProd.half_conj_add_of_right h10 hy
      simp only [LinearMap.comp_apply]
      change T (extFn e₀ e₁ Λ (fun t => ψ (B t y) * Ψ t)) = hs y (T (extFn e₀ e₁ Λ Ψ))
      rw [extFn_modul Λ Ψ (fun t => ψ (B t y)) (fun t ht => by simp only [hB t y ht hy])]
      exact hT.modul _ (hsb Ψ hΨ) y hy'
    · simp only [LinearMap.comp_apply, one_smul]
      change T (extFn e₀ e₁ Λ (halfInd e₀ Λ)) = f₀
      rw [extFn_halfInd h00 h11 hΛ0 hΛ1]
      simpa using hT.vac
  exact h.2 _ hT₀

end ThetaExt

end GlobalTheory.CosetRow

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaAtHalfExtensionLatticeIndicatorFnStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isThetaAt_halfExtensionLatticeIndicatorFn : ∀ {D : D7} {m n : ℕ} {ψ : AddChar (AF D.host.F) ℂ} {B : Mx D m n → Mx D m n → AF D.host.F} {hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ)} {Λ : AddSubgroup (Mx D m n)} {e₀ e₁ : AE D} {f₀ Φ f : Mx D m n → ℂ}, e₀ * e₀ = e₀ → e₁ * e₁ = e₁ → e₀ * e₁ = 0 → (∀ u ∈ Λ, e₀ • u ∈ Λ) → (∀ u ∈ Λ, e₁ • u ∈ Λ) → (∀ t y, IsHalf (e₀ + e₁) t → IsHalf (cA D e₀) y → B t y = B (e₀ • t) y) → (∃ T, IsPlaceModel ψ B hs (e₀ + e₁) Λ 1 f₀ T) → IsThetaAt ψ B hs e₀ Λ 1 f₀ Φ f → IsThetaAt ψ B hs (e₀ + e₁) Λ 1 f₀ (GlobalTheory.CosetRow.extFn e₀ e₁ Λ Φ) f := by
  first | exact @GlobalTheory.CosetRow.isThetaAt_extFn | exact GlobalTheory.CosetRow.isThetaAt_extFn | (intros; apply GlobalTheory.CosetRow.isThetaAt_extFn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemOffP
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FibreAtTau

variable {D : D7} (θ : InfFam D) (V : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) (τ : D.what₂.Tau)

def atP : Subgroup (NI V C) :=
  (GinfC V ⊓ ⨅ (τ' : D.what₂.Tau) (_ : τ' ≠ τ), (GlobalTheory.RowReal.infMatHom V (θ τ')).ker).subgroupOf (NI V C)

def offP : Subgroup (NI V C) := ((GlobalTheory.RowReal.infMatHom V (θ τ)).ker).subgroupOf (NI V C)

variable {θ V C τ}

theorem mem_atP {p : NI V C} :
    p ∈ atP θ V C τ ↔ (p : GA D V) ∈ GinfC V ∧ ∀ τ', τ' ≠ τ → cmp θ τ' (p : GA D V) = 1 := by
  simp only [atP, Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_iInf, MonoidHom.mem_ker]
  rfl

theorem mem_offP {q : NI V C} : q ∈ offP θ V C τ ↔ cmp θ τ (q : GA D V) = 1 := by
  simp only [offP, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
  rfl

end GlobalTheory.FibreAtTau
end
end
