module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinrankInvFunBranch
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CastRealAll
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GenPerMove
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharFiniteIdelesIsAlgebraicOfResEta

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestRealPlacesDefinitePeriodsOnOneLine
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestDefinitePeriodsInvariantFunctional
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InvContCast
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.RowReal
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GenConvProof

variable {D : D7}

theorem invCont_cast {Λ : Submodule (𝓞 D.host.E) (Fin D.sp.X'.rank → D.host.E)} (X : LSp D) (h : X = ⟨D.sp.X', Λ⟩)
    (φ : GA D D.sp.X' → ℂ) (hc : Continuous φ) (hl : ∀ γ ∈ GQ D.sp.X', ∀ g, φ (γ * g) = φ g) :
    Continuous (fun g => φ (cast (congrArg (fun X : LSp D => GA D X.sp) h) g)) ∧
      ∀ γ ∈ GQ X.sp, ∀ g, φ (cast (congrArg (fun X : LSp D => GA D X.sp) h) (γ * g)) =
        φ (cast (congrArg (fun X : LSp D => GA D X.sp) h) g) := by
  subst h
  exact ⟨hc, hl⟩

theorem genPer_conv : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ t a, ch.S.SumOK t (ch.Phi a) →
    ∀ β ∈ ch.S.supp t (ch.Phi a), ∀ M : Vol ch.G, IsTermVol t ch.S.toGridChoice (ch.Phi a) β M →
      ∀ τ, ch.S.IsExpansion t (ch.Phi a) β τ → ∀ d ∈ τ.support, ∀ y Q ξ η, GenConv ch t a M d y Q ξ η := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch _ _ => ?_⟩⟩
  intro t a hOK β hβ M hM τ hτ d hd y Q ξ η
  have hL := s.core.lev
  have hm := s.core.models
  have hcol : GlobalTheory.DefConv.IsInvCont (.top 0) (pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a)) :=
    ⟨GlobalTheory.RowBplus.pairVec_cont ch.G ch.W.θ ch.W.θ_is ξ (col_mem ch a),
      fun γ hγ g => GlobalTheory.RowBplus.pairVec_left ch.G ch.W.θ ξ (col_mem ch a) hγ g⟩
  have hx := (hm.HX t).2.1.le (LinearMap.mem_range_self (R.HX t).e y)
  have hform : GlobalTheory.DefConv.IsInvCont (.grid 0 D.R.m) (formGen ch t y η) := by
    have k := invCont_cast (columnBlock R.toLevCh D.R.m) (colY_m R.toLevCh) (fun g => η (R.cX.ext ((R.HX t).e y) g))
      ((LinearMap.continuous_of_finiteDimensional η).comp
        (GlobalTheory.ThetaIntegrand.ext_continuous R.cX hm.cX R.βX (R.datXt t) hx))
      (fun γ hγ g => by simp only [GlobalTheory.ThetaIntegrand.ext_invariant R.cX hx γ hγ g])
    exact ⟨k.1, k.2⟩
  have hv := hOK.vec β τ hτ d hd
  have hcG : Path.Fam.All (fun a f => GlobalTheory.DefConv.Good ch.W M a f)
      (colFam t D.R.m fun j => ch.W.fock (.top t j) (movedVec t ch.S.toGridChoice (d.1 j)) (Q.1 j)) :=
    GlobalTheory.DefConv.all_colFam t _ _ fun j => GlobalTheory.DefConv.good_col ch.W M j.2 _
      (GlobalTheory.DefConv.theta_fock ch.W ch.S.toGridChoice (p := .top t j) (by show (j : ℕ) + 1 ≤ D.R.m; omega)
        (by show (j : ℕ) + 1 ≤ D.R.m; omega) (d.1 j) (hv.1 j) (Q.1 j))
      (GlobalTheory.DefConv.posDef_of_node ch.G hL (X := .top j) (show (j : ℕ) ≤ D.R.m by omega) rfl) (hM.1 j j.2)
  have hrG : Path.Fam.All (fun a f => GlobalTheory.DefConv.Good ch.W M a f)
      (rowFam D.R.m D.R.m fun i => ch.W.fock (.chi i D.R.m) (movedVec t ch.S.toGridChoice (d.2 i)) (Q.2 i)) :=
    GlobalTheory.DefConv.all_rowFam D.R.m _ _ fun i => GlobalTheory.DefConv.good_row ch.W M i.2 _
      (GlobalTheory.DefConv.theta_fock ch.W ch.S.toGridChoice (p := .chi i D.R.m)
        (show (i : ℕ) + 1 ≤ D.R.m ∧ D.R.m = D.R.m from ⟨by omega, rfl⟩)
        (show (i : ℕ) + 1 ≤ D.R.m ∧ D.R.m ≤ D.R.m from ⟨by omega, le_rfl⟩) (d.2 i) (hv.2 i) (Q.2 i))
      (GlobalTheory.DefConv.posDef_of_node ch.G hL (X := .grid i D.R.m) ⟨by omega, le_rfl⟩ (by simp [Node.neg]))
      (hM.2 i (by omega))
  obtain ⟨hc1, hc2⟩ := GlobalTheory.DefConv.path ch.W M hcol _ _ hcG
  obtain ⟨hr1, hr2⟩ := GlobalTheory.DefConv.path ch.W M hform _ _ hrG
  refine ⟨hc1, hr1, ?_⟩
  obtain ⟨hac, hamul, haQ⟩ := GlobalTheory.T.unitaryEmbedding_continuous_mul_rational ch.G.sp.topDec
  have hpos := GlobalTheory.DefConv.posDef_of_node ch.G hL (X := .grid D.R.m D.R.m) ⟨le_rfl, le_rfl⟩ (by simp [Node.neg])
  obtain ⟨Cc, hCc, hcov⟩ := GlobalTheory.definite_unitary_cocompact _ hpos
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (ch.G.V (.grid D.R.m D.R.m))
  obtain ⟨hH, hfd⟩ := (hM.2 D.R.m le_rfl).haar_fund
  refine GlobalTheory.CocompactIntegrable.integrableOn_of_cocompact _ _ _ Cc hfd hCc hcov _
    ((hc2.1.comp hac).mul hr2.1) fun γ hγ g => ?_
  simp only [hamul, hc2.2 _ (haQ γ hγ), hr2.2 γ hγ]

end GlobalTheory.GenConvProof

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeftCast
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.RowReal
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.RowReal

theorem left_cast {D : D7} {Λ : Submodule (𝓞 D.host.E) (Fin D.sp.X'.rank → D.host.E)} (X : LSp D) (h : X = ⟨D.sp.X', Λ⟩)
    (φ : GA D D.sp.X' → ℂ) (hφ : ∀ γ ∈ GQ D.sp.X', ∀ g, φ (γ * g) = φ g) :
    ∀ γ ∈ GQ X.sp, ∀ g, φ (cast (congrArg (fun X : LSp D => GA D X.sp) h) (γ * g)) =
      φ (cast (congrArg (fun X : LSp D => GA D X.sp) h) g) := by
  subst h
  exact hφ

theorem gen_left : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch =>
    (∀ a ξ, ∀ γ ∈ GQ (ch.G.V (.top 0)), ∀ g,
      pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a) (γ * g) =
        pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a) g) ∧
    ∀ t y η, ∀ γ ∈ GQ (ch.G.V (.grid 0 D.R.m)), ∀ g, formGen ch t y η (γ * g) = formGen ch t y η g := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch _ => ?_⟩⟩
  refine ⟨fun a ξ γ hγ g => GlobalTheory.RowBplus.pairVec_left ch.G ch.W.θ ξ (col_mem ch a) hγ g, fun t y η => ?_⟩
  have hm := hS.core.models
  exact left_cast (columnBlock R.toLevCh D.R.m) (colY_m R.toLevCh) (fun g => η (R.cX.ext ((R.HX t).e y) g))
    (fun γ hγ g => congrArg η
      (GlobalTheory.ThetaProjEquiv.ext_left R.cX ((R.HX t).e y) _ _ ((hm.HX t).2.1.le ⟨y, rfl⟩) γ hγ g))

end GlobalTheory.RowReal

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GenPerMultilinear
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.RowReal
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowReal

section Lin

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G)

theorem kerA_col_add (t : T) (j : ℕ) (f f' : Sch G (.col t j)) :
    ∀ g h, W.kerA (.col t j) (f + f') g h = W.kerA (.col t j) f g h + W.kerA (.col t j) f' g h := by
  intro g h
  simp only [GridData.Weil.kerA, GridData.Weil.ker, thetaKO, map_add (f := _), Pi.add_apply]

theorem kerA_col_smul (t : T) (j : ℕ) (c : ℂ) (f : Sch G (.col t j)) :
    ∀ g h, W.kerA (.col t j) (c • f) g h = c * W.kerA (.col t j) f g h := by
  intro g h
  simp only [GridData.Weil.kerA, GridData.Weil.ker, thetaKO, map_smul, Pi.smul_apply, smul_eq_mul]

theorem kerA_right_add (i j : ℕ) (f f' : Sch G (.right i j)) :
    ∀ g h, W.kerA (.right i j) (f + f') g h = W.kerA (.right i j) f g h + W.kerA (.right i j) f' g h := by
  intro g h
  simp only [GridData.Weil.kerA, GridData.Weil.ker, thetaKO, map_add (f := _), Pi.add_apply]

theorem kerA_right_smul (i j : ℕ) (c : ℂ) (f : Sch G (.right i j)) :
    ∀ g h, W.kerA (.right i j) (c • f) g h = c * W.kerA (.right i j) f g h := by
  intro g h
  simp only [GridData.Weil.kerA, GridData.Weil.ker, thetaKO, map_smul, Pi.smul_apply, smul_eq_mul]

end Lin

end GlobalTheory.RowReal

namespace GlobalTheory.RowReal

section Lin2

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G)

theorem liftA_datum_add {a : Arrow T} {f f' f'' : Sch G a} {F : Fn G a.src}
    (hk : ∀ g h, W.kerA a f'' g h = W.kerA a f g h + W.kerA a f' g h)
    (h1 : LiftConv W M a f F) (h2 : LiftConv W M a f' F) :
    liftA W M a f'' F = liftA W M a f F + liftA W M a f' F := by
  funext x
  simp only [liftA_apply, Pi.add_apply, hk, add_mul]
  exact integral_add (h1 x) (h2 x)

theorem liftA_datum_smul {a : Arrow T} {f f'' : Sch G a} {F : Fn G a.src} (c : ℂ)
    (hk : ∀ g h, W.kerA a f'' g h = c * W.kerA a f g h) :
    liftA W M a f'' F = c • liftA W M a f F := by
  funext x
  simp only [liftA_apply, Pi.smul_apply, smul_eq_mul, hk, mul_assoc, integral_const_mul]

theorem pathLift_column_add (t : T) : ∀ (n : ℕ) (f f' f'' : ∀ j : Fin n, Sch G (.col t j)) (j0 : Fin n),
    (∀ j, j ≠ j0 → f j = f'' j ∧ f' j = f'' j) → f'' j0 = f j0 + f' j0 → ∀ F : Fn G (.top 0),
    PathConv W M (colPath t n) (colFam t n f) F → PathConv W M (colPath t n) (colFam t n f') F →
    liftP W M (colPath t n) (colFam t n f'') F =
      liftP W M (colPath t n) (colFam t n f) F + liftP W M (colPath t n) (colFam t n f') F
  | 0, _, _, _, j0, _, _, _, _, _ => j0.elim0
  | n + 1, f, f', f'', j0, hne, h0, F, h1, h2 => by
    have h1a : PathConv W M (colPath t n) (colFam t n fun j => f j.castSucc) F := h1.1
    have h2a : PathConv W M (colPath t n) (colFam t n fun j => f' j.castSucc) F := h2.1
    have h1b : LiftConv W M (.col t n) (f (Fin.last n)) (liftP W M (colPath t n) (colFam t n fun j => f j.castSucc) F) := h1.2
    have h2b : LiftConv W M (.col t n) (f' (Fin.last n)) (liftP W M (colPath t n) (colFam t n fun j => f' j.castSucc) F) := h2.2
    change liftA W M (.col t n) (f'' (Fin.last n)) (liftP W M (colPath t n) (colFam t n fun j => f'' j.castSucc) F) =
      liftA W M (.col t n) (f (Fin.last n)) (liftP W M (colPath t n) (colFam t n fun j => f j.castSucc) F) +
      liftA W M (.col t n) (f' (Fin.last n)) (liftP W M (colPath t n) (colFam t n fun j => f' j.castSucc) F)
    by_cases hj : j0 = Fin.last n
    · subst hj
      have e1 : (fun j : Fin n => f j.castSucc) = fun j : Fin n => f'' j.castSucc :=
        funext fun j => (hne _ (Fin.castSucc_lt_last j).ne).1
      have e2 : (fun j : Fin n => f' j.castSucc) = fun j : Fin n => f'' j.castSucc :=
        funext fun j => (hne _ (Fin.castSucc_lt_last j).ne).2
      rw [e1] at h1b ⊢
      rw [e2] at h2b ⊢
      exact liftA_datum_add W M (fun g h => by rw [h0]; exact kerA_col_add W t n _ _ g h) h1b h2b
    · rcases Fin.eq_castSucc_of_ne_last hj with ⟨j1, rfl⟩
      have el : f (Fin.last n) = f'' (Fin.last n) := (hne _ (Ne.symm hj)).1
      have el' : f' (Fin.last n) = f'' (Fin.last n) := (hne _ (Ne.symm hj)).2
      have ih := pathLift_column_add t n (fun j => f j.castSucc) (fun j => f' j.castSucc) (fun j => f'' j.castSucc) j1
        (fun j hj' => hne _ (fun e => hj' (Fin.castSucc_injective _ e))) h0 F h1a h2a
      rw [el] at h1b ⊢
      rw [el'] at h2b ⊢
      rw [ih]
      exact liftA_add W M h1b h2b

theorem pathLift_column_smul (t : T) (c : ℂ) : ∀ (n : ℕ) (f f'' : ∀ j : Fin n, Sch G (.col t j)) (j0 : Fin n),
    (∀ j, j ≠ j0 → f j = f'' j) → f'' j0 = c • f j0 → ∀ F : Fn G (.top 0),
    liftP W M (colPath t n) (colFam t n f'') F = c • liftP W M (colPath t n) (colFam t n f) F
  | 0, _, _, j0, _, _, _ => j0.elim0
  | n + 1, f, f'', j0, hne, h0, F => by
    change liftA W M (.col t n) (f'' (Fin.last n)) (liftP W M (colPath t n) (colFam t n fun j => f'' j.castSucc) F) =
      c • liftA W M (.col t n) (f (Fin.last n)) (liftP W M (colPath t n) (colFam t n fun j => f j.castSucc) F)
    by_cases hj : j0 = Fin.last n
    · subst hj
      have e1 : (fun j : Fin n => f j.castSucc) = fun j : Fin n => f'' j.castSucc :=
        funext fun j => hne _ (Fin.castSucc_lt_last j).ne
      rw [e1]
      exact liftA_datum_smul W M c (fun g h => by rw [h0]; exact kerA_col_smul W t n c _ g h)
    · rcases Fin.eq_castSucc_of_ne_last hj with ⟨j1, rfl⟩
      have el : f (Fin.last n) = f'' (Fin.last n) := hne _ (Ne.symm hj)
      have ih := pathLift_column_smul t c n (fun j => f j.castSucc) (fun j => f'' j.castSucc) j1
        (fun j hj' => hne _ (fun e => hj' (Fin.castSucc_injective _ e))) h0 F
      rw [el, ih]
      exact liftA_smul W M _ _ c _

theorem pathLift_row_add (k : ℕ) : ∀ (n : ℕ) (f f' f'' : ∀ i : Fin n, Sch G (.right i k)) (j0 : Fin n),
    (∀ j, j ≠ j0 → f j = f'' j ∧ f' j = f'' j) → f'' j0 = f j0 + f' j0 → ∀ F : Fn G (.grid 0 k),
    PathConv W M (rowPath T k n) (rowFam k n f) F → PathConv W M (rowPath T k n) (rowFam k n f') F →
    liftP W M (rowPath T k n) (rowFam k n f'') F =
      liftP W M (rowPath T k n) (rowFam k n f) F + liftP W M (rowPath T k n) (rowFam k n f') F
  | 0, _, _, _, j0, _, _, _, _, _ => j0.elim0
  | n + 1, f, f', f'', j0, hne, h0, F, h1, h2 => by
    have h1a : PathConv W M (rowPath T k n) (rowFam k n fun j => f j.castSucc) F := h1.1
    have h2a : PathConv W M (rowPath T k n) (rowFam k n fun j => f' j.castSucc) F := h2.1
    have h1b : LiftConv W M (.right n k) (f (Fin.last n)) (liftP W M (rowPath T k n) (rowFam k n fun j => f j.castSucc) F) := h1.2
    have h2b : LiftConv W M (.right n k) (f' (Fin.last n)) (liftP W M (rowPath T k n) (rowFam k n fun j => f' j.castSucc) F) := h2.2
    change liftA W M (.right n k) (f'' (Fin.last n)) (liftP W M (rowPath T k n) (rowFam k n fun j => f'' j.castSucc) F) =
      liftA W M (.right n k) (f (Fin.last n)) (liftP W M (rowPath T k n) (rowFam k n fun j => f j.castSucc) F) +
      liftA W M (.right n k) (f' (Fin.last n)) (liftP W M (rowPath T k n) (rowFam k n fun j => f' j.castSucc) F)
    by_cases hj : j0 = Fin.last n
    · subst hj
      have e1 : (fun j : Fin n => f j.castSucc) = fun j : Fin n => f'' j.castSucc :=
        funext fun j => (hne _ (Fin.castSucc_lt_last j).ne).1
      have e2 : (fun j : Fin n => f' j.castSucc) = fun j : Fin n => f'' j.castSucc :=
        funext fun j => (hne _ (Fin.castSucc_lt_last j).ne).2
      rw [e1] at h1b ⊢
      rw [e2] at h2b ⊢
      exact liftA_datum_add W M (fun g h => by rw [h0]; exact kerA_right_add W n k _ _ g h) h1b h2b
    · rcases Fin.eq_castSucc_of_ne_last hj with ⟨j1, rfl⟩
      have el : f (Fin.last n) = f'' (Fin.last n) := (hne _ (Ne.symm hj)).1
      have el' : f' (Fin.last n) = f'' (Fin.last n) := (hne _ (Ne.symm hj)).2
      have ih := pathLift_row_add k n (fun j => f j.castSucc) (fun j => f' j.castSucc) (fun j => f'' j.castSucc) j1
        (fun j hj' => hne _ (fun e => hj' (Fin.castSucc_injective _ e))) h0 F h1a h2a
      rw [el] at h1b ⊢
      rw [el'] at h2b ⊢
      rw [ih]
      exact liftA_add W M h1b h2b

theorem pathLift_row_smul (k : ℕ) (c : ℂ) : ∀ (n : ℕ) (f f'' : ∀ i : Fin n, Sch G (.right i k)) (j0 : Fin n),
    (∀ j, j ≠ j0 → f j = f'' j) → f'' j0 = c • f j0 → ∀ F : Fn G (.grid 0 k),
    liftP W M (rowPath T k n) (rowFam k n f'') F = c • liftP W M (rowPath T k n) (rowFam k n f) F
  | 0, _, _, j0, _, _, _ => j0.elim0
  | n + 1, f, f'', j0, hne, h0, F => by
    change liftA W M (.right n k) (f'' (Fin.last n)) (liftP W M (rowPath T k n) (rowFam k n fun j => f'' j.castSucc) F) =
      c • liftA W M (.right n k) (f (Fin.last n)) (liftP W M (rowPath T k n) (rowFam k n fun j => f j.castSucc) F)
    by_cases hj : j0 = Fin.last n
    · subst hj
      have e1 : (fun j : Fin n => f j.castSucc) = fun j : Fin n => f'' j.castSucc :=
        funext fun j => hne _ (Fin.castSucc_lt_last j).ne
      rw [e1]
      exact liftA_datum_smul W M c (fun g h => by rw [h0]; exact kerA_right_smul W n k c _ g h)
    · rcases Fin.eq_castSucc_of_ne_last hj with ⟨j1, rfl⟩
      have el : f (Fin.last n) = f'' (Fin.last n) := hne _ (Ne.symm hj)
      have ih := pathLift_row_smul k c n (fun j => f j.castSucc) (fun j => f'' j.castSucc) j1
        (fun j hj' => hne _ (fun e => hj' (Fin.castSucc_injective _ e))) h0 F
      rw [el, ih]
      exact liftA_smul W M _ _ c _

end Lin2

end GlobalTheory.RowReal

namespace GlobalTheory.RowReal

section Outer

variable {X : Type} [MeasurableSpace X] {μ : Measure X} {s : Set X}

end Outer

section Multi

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)
  (t : T) (a : Fin ch.n) (M : Vol ch.G) (d : PureDat ch.G t) (y : (R.HX t).H)

def colLift (Q1 : PolCol ch.G) (ξ : Module.Dual ℂ (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ).W) : Fn ch.G (.top D.R.m) :=
  liftP ch.W M (colPath t D.R.m)
    (colFam t D.R.m fun j => ch.W.fock (.top t j) (movedVec t ch.S.toGridChoice (d.1 j)) (Q1 j))
    (pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a))

def rowLift (Q2 : PolRow ch.G) (η : Module.Dual ℂ R.cX.W) : Fn ch.G (.grid D.R.m D.R.m) :=
  liftP ch.W M (rowPath T D.R.m D.R.m)
    (rowFam D.R.m D.R.m fun i => ch.W.fock (.chi i D.R.m) (movedVec t ch.S.toGridChoice (d.2 i)) (Q2 i))
    (formGen ch t y η)

theorem genPer_eq (Q : PolCol ch.G × PolRow ch.G) ξ η :
    genPer ch t a M d y Q ξ η = ∫ h in M.fd (.grid D.R.m D.R.m),
      colLift ch t a M d Q.1 ξ (stabilizerEmbedding ch.G.sp.topDec h) * rowLift ch t M d y Q.2 η h ∂M.ν (.grid D.R.m D.R.m) := rfl

theorem genConv_int {Q : PolCol ch.G × PolRow ch.G} {ξ η} (h : GenConv ch t a M d y Q ξ η) :
    IntegrableOn (fun h => colLift ch t a M d Q.1 ξ (stabilizerEmbedding ch.G.sp.topDec h) * rowLift ch t M d y Q.2 η h)
      (M.fd (.grid D.R.m D.R.m)) (M.ν (.grid D.R.m D.R.m)) := h.2.2

theorem colLift_add [DecidableEq (Fin D.R.m)] (Q1 : PolCol ch.G) (i : Fin D.R.m)
    (x x' : PolF D (ch.G.V (.top ((i : ℕ) + 1))).rank (ch.G.V (.top i)).rank) ξ
    (h1 : PathConv ch.W M (colPath t D.R.m)
      (colFam t D.R.m fun j => ch.W.fock (.top t j) (movedVec t ch.S.toGridChoice (d.1 j)) (Function.update Q1 i x j))
      (pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a)))
    (h2 : PathConv ch.W M (colPath t D.R.m)
      (colFam t D.R.m fun j => ch.W.fock (.top t j) (movedVec t ch.S.toGridChoice (d.1 j)) (Function.update Q1 i x' j))
      (pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a))) :
    colLift ch t a M d (Function.update Q1 i (x + x')) ξ =
      colLift ch t a M d (Function.update Q1 i x) ξ + colLift ch t a M d (Function.update Q1 i x') ξ :=
  pathLift_column_add ch.W M t D.R.m
    (fun j => ch.W.fock (.top t j) (movedVec t ch.S.toGridChoice (d.1 j)) (Function.update Q1 i x j))
    (fun j => ch.W.fock (.top t j) (movedVec t ch.S.toGridChoice (d.1 j)) (Function.update Q1 i x' j))
    (fun j => ch.W.fock (.top t j) (movedVec t ch.S.toGridChoice (d.1 j)) (Function.update Q1 i (x + x') j)) i
    (fun j hj => by simp only [Function.update_of_ne hj, and_self])
    (by simp only [Function.update_self, map_add (f := _)]) _ h1 h2

theorem colLift_smul [DecidableEq (Fin D.R.m)] (Q1 : PolCol ch.G) (i : Fin D.R.m) (c : ℂ)
    (x : PolF D (ch.G.V (.top ((i : ℕ) + 1))).rank (ch.G.V (.top i)).rank) ξ :
    colLift ch t a M d (Function.update Q1 i (c • x)) ξ = c • colLift ch t a M d (Function.update Q1 i x) ξ :=
  pathLift_column_smul ch.W M t c D.R.m
    (fun j => ch.W.fock (.top t j) (movedVec t ch.S.toGridChoice (d.1 j)) (Function.update Q1 i x j))
    (fun j => ch.W.fock (.top t j) (movedVec t ch.S.toGridChoice (d.1 j)) (Function.update Q1 i (c • x) j)) i
    (fun j hj => by simp only [Function.update_of_ne hj])
    (by simp only [Function.update_self, map_smul]) _

theorem rowLift_add [DecidableEq (Fin D.R.m)] (Q2 : PolRow ch.G) (i : Fin D.R.m)
    (x x' : PolF D (ch.G.V (.grid i D.R.m)).rank (ch.G.V (.grid ((i : ℕ) + 1) D.R.m)).rank) η
    (h1 : PathConv ch.W M (rowPath T D.R.m D.R.m)
      (rowFam D.R.m D.R.m fun j => ch.W.fock (.chi j D.R.m) (movedVec t ch.S.toGridChoice (d.2 j)) (Function.update Q2 i x j))
      (formGen ch t y η))
    (h2 : PathConv ch.W M (rowPath T D.R.m D.R.m)
      (rowFam D.R.m D.R.m fun j => ch.W.fock (.chi j D.R.m) (movedVec t ch.S.toGridChoice (d.2 j)) (Function.update Q2 i x' j))
      (formGen ch t y η)) :
    rowLift ch t M d y (Function.update Q2 i (x + x')) η =
      rowLift ch t M d y (Function.update Q2 i x) η + rowLift ch t M d y (Function.update Q2 i x') η :=
  pathLift_row_add ch.W M D.R.m D.R.m
    (fun j => ch.W.fock (.chi j D.R.m) (movedVec t ch.S.toGridChoice (d.2 j)) (Function.update Q2 i x j))
    (fun j => ch.W.fock (.chi j D.R.m) (movedVec t ch.S.toGridChoice (d.2 j)) (Function.update Q2 i x' j))
    (fun j => ch.W.fock (.chi j D.R.m) (movedVec t ch.S.toGridChoice (d.2 j)) (Function.update Q2 i (x + x') j)) i
    (fun j hj => by simp only [Function.update_of_ne hj, and_self])
    (by simp only [Function.update_self, map_add (f := _)]) _ h1 h2

theorem rowLift_smul [DecidableEq (Fin D.R.m)] (Q2 : PolRow ch.G) (i : Fin D.R.m) (c : ℂ)
    (x : PolF D (ch.G.V (.grid i D.R.m)).rank (ch.G.V (.grid ((i : ℕ) + 1) D.R.m)).rank) η :
    rowLift ch t M d y (Function.update Q2 i (c • x)) η = c • rowLift ch t M d y (Function.update Q2 i x) η :=
  pathLift_row_smul ch.W M D.R.m c D.R.m
    (fun j => ch.W.fock (.chi j D.R.m) (movedVec t ch.S.toGridChoice (d.2 j)) (Function.update Q2 i x j))
    (fun j => ch.W.fock (.chi j D.R.m) (movedVec t ch.S.toGridChoice (d.2 j)) (Function.update Q2 i (c • x) j)) i
    (fun j hj => by simp only [Function.update_of_ne hj])
    (by simp only [Function.update_self, map_smul]) _

theorem colLift_xi_add (Q1 : PolCol ch.G) ξ ξ'
    (h1 : PathConv ch.W M (colPath t D.R.m)
      (colFam t D.R.m fun j => ch.W.fock (.top t j) (movedVec t ch.S.toGridChoice (d.1 j)) (Q1 j))
      (pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a)))
    (h2 : PathConv ch.W M (colPath t D.R.m)
      (colFam t D.R.m fun j => ch.W.fock (.top t j) (movedVec t ch.S.toGridChoice (d.1 j)) (Q1 j))
      (pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ' (ch.col a))) :
    colLift ch t a M d Q1 (ξ + ξ') = colLift ch t a M d Q1 ξ + colLift ch t a M d Q1 ξ' := by
  have hp : pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) (ξ + ξ') (ch.col a) =
      pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a) + pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ' (ch.col a) := by
    funext h
    simp only [pairVec_apply, LinearMap.add_apply, Pi.add_apply]
  unfold colLift
  rw [hp]
  exact pathLift_add ch.W M _ _ h1 h2

theorem colLift_xi_smul (Q1 : PolCol ch.G) (c : ℂ) ξ :
    colLift ch t a M d Q1 (c • ξ) = c • colLift ch t a M d Q1 ξ := by
  have hp : pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) (c • ξ) (ch.col a) =
      c • pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a) := by
    funext h
    simp only [pairVec_apply, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
  unfold colLift
  rw [hp]
  exact pathLift_smul ch.W M _ _ _ _

theorem formGen_add (η η' : Module.Dual ℂ R.cX.W) : formGen ch t y (η + η') = formGen ch t y η + formGen ch t y η' := by
  funext g
  simp only [formGen, LinearMap.add_apply, Pi.add_apply]

theorem formGen_smul (c : ℂ) (η : Module.Dual ℂ R.cX.W) : formGen ch t y (c • η) = c • formGen ch t y η := by
  funext g
  simp only [formGen, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]

theorem rowLift_eta_add (Q2 : PolRow ch.G) η η'
    (h1 : PathConv ch.W M (rowPath T D.R.m D.R.m)
      (rowFam D.R.m D.R.m fun i => ch.W.fock (.chi i D.R.m) (movedVec t ch.S.toGridChoice (d.2 i)) (Q2 i)) (formGen ch t y η))
    (h2 : PathConv ch.W M (rowPath T D.R.m D.R.m)
      (rowFam D.R.m D.R.m fun i => ch.W.fock (.chi i D.R.m) (movedVec t ch.S.toGridChoice (d.2 i)) (Q2 i)) (formGen ch t y η')) :
    rowLift ch t M d y Q2 (η + η') = rowLift ch t M d y Q2 η + rowLift ch t M d y Q2 η' := by
  unfold rowLift
  rw [formGen_add]
  exact pathLift_add ch.W M _ _ h1 h2

theorem rowLift_eta_smul (Q2 : PolRow ch.G) (c : ℂ) η :
    rowLift ch t M d y Q2 (c • η) = c • rowLift ch t M d y Q2 η := by
  unfold rowLift
  rw [formGen_smul]
  exact pathLift_smul ch.W M _ _ _ _

end Multi

end GlobalTheory.RowReal

namespace GlobalTheory.RowReal

section Multi2

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)
  (t : T) (a : Fin ch.n) (M : Vol ch.G) (d : PureDat ch.G t) (y : (R.HX t).H)

theorem genPer_col_add [DecidableEq (Fin D.R.m)] (hc : ∀ Q ξ η, GenConv ch t a M d y Q ξ η) (Q1 : PolCol ch.G)
    (Q2 : PolRow ch.G) (i : Fin D.R.m) (x x' : PolF D (ch.G.V (.top ((i : ℕ) + 1))).rank (ch.G.V (.top i)).rank) ξ η :
    genPer ch t a M d y (Function.update Q1 i (x + x'), Q2) ξ η =
      genPer ch t a M d y (Function.update Q1 i x, Q2) ξ η + genPer ch t a M d y (Function.update Q1 i x', Q2) ξ η := by
  have i1 := genConv_int ch t a M d y (hc (Function.update Q1 i x, Q2) ξ η)
  have i2 := genConv_int ch t a M d y (hc (Function.update Q1 i x', Q2) ξ η)
  have e := colLift_add ch t a M d Q1 i x x' ξ (hc (Function.update Q1 i x, Q2) ξ η).1
    (hc (Function.update Q1 i x', Q2) ξ η).1
  dsimp only at i1 i2
  rw [genPer_eq, genPer_eq, genPer_eq]
  dsimp only
  rw [e]
  simp only [Pi.add_apply, add_mul]
  exact integral_add i1 i2

theorem genPer_col_smul [DecidableEq (Fin D.R.m)] (Q1 : PolCol ch.G) (Q2 : PolRow ch.G) (i : Fin D.R.m) (c : ℂ)
    (x : PolF D (ch.G.V (.top ((i : ℕ) + 1))).rank (ch.G.V (.top i)).rank) ξ η :
    genPer ch t a M d y (Function.update Q1 i (c • x), Q2) ξ η = c * genPer ch t a M d y (Function.update Q1 i x, Q2) ξ η := by
  rw [genPer_eq, genPer_eq]
  dsimp only
  rw [colLift_smul]
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]

theorem genPer_row_add [DecidableEq (Fin D.R.m)] (hc : ∀ Q ξ η, GenConv ch t a M d y Q ξ η) (Q1 : PolCol ch.G)
    (Q2 : PolRow ch.G) (i : Fin D.R.m)
    (x x' : PolF D (ch.G.V (.grid i D.R.m)).rank (ch.G.V (.grid ((i : ℕ) + 1) D.R.m)).rank) ξ η :
    genPer ch t a M d y (Q1, Function.update Q2 i (x + x')) ξ η =
      genPer ch t a M d y (Q1, Function.update Q2 i x) ξ η + genPer ch t a M d y (Q1, Function.update Q2 i x') ξ η := by
  have i1 := genConv_int ch t a M d y (hc (Q1, Function.update Q2 i x) ξ η)
  have i2 := genConv_int ch t a M d y (hc (Q1, Function.update Q2 i x') ξ η)
  have e := rowLift_add ch t M d y Q2 i x x' η (hc (Q1, Function.update Q2 i x) ξ η).2.1
    (hc (Q1, Function.update Q2 i x') ξ η).2.1
  dsimp only at i1 i2
  rw [genPer_eq, genPer_eq, genPer_eq]
  dsimp only
  rw [e]
  simp only [Pi.add_apply, mul_add]
  exact integral_add i1 i2

theorem genPer_row_smul [DecidableEq (Fin D.R.m)] (Q1 : PolCol ch.G) (Q2 : PolRow ch.G) (i : Fin D.R.m) (c : ℂ)
    (x : PolF D (ch.G.V (.grid i D.R.m)).rank (ch.G.V (.grid ((i : ℕ) + 1) D.R.m)).rank) ξ η :
    genPer ch t a M d y (Q1, Function.update Q2 i (c • x)) ξ η = c * genPer ch t a M d y (Q1, Function.update Q2 i x) ξ η := by
  rw [genPer_eq, genPer_eq]
  dsimp only
  rw [rowLift_smul]
  simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm _ c, integral_const_mul]

theorem genPer_xi_add (hc : ∀ Q ξ η, GenConv ch t a M d y Q ξ η) (Q : PolCol ch.G × PolRow ch.G) ξ ξ' η :
    genPer ch t a M d y Q (ξ + ξ') η = genPer ch t a M d y Q ξ η + genPer ch t a M d y Q ξ' η := by
  have i1 := genConv_int ch t a M d y (hc Q ξ η)
  have i2 := genConv_int ch t a M d y (hc Q ξ' η)
  rw [genPer_eq, genPer_eq, genPer_eq, colLift_xi_add ch t a M d Q.1 ξ ξ' (hc Q ξ η).1 (hc Q ξ' η).1]
  simp only [Pi.add_apply, add_mul]
  exact integral_add i1 i2

theorem genPer_xi_smul (Q : PolCol ch.G × PolRow ch.G) (c : ℂ) ξ η :
    genPer ch t a M d y Q (c • ξ) η = c * genPer ch t a M d y Q ξ η := by
  rw [genPer_eq, genPer_eq, colLift_xi_smul]
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]

theorem genPer_eta_add (hc : ∀ Q ξ η, GenConv ch t a M d y Q ξ η) (Q : PolCol ch.G × PolRow ch.G) ξ η η' :
    genPer ch t a M d y Q ξ (η + η') = genPer ch t a M d y Q ξ η + genPer ch t a M d y Q ξ η' := by
  have i1 := genConv_int ch t a M d y (hc Q ξ η)
  have i2 := genConv_int ch t a M d y (hc Q ξ η')
  rw [genPer_eq, genPer_eq, genPer_eq, rowLift_eta_add ch t M d y Q.2 η η' (hc Q ξ η).2.1 (hc Q ξ η').2.1]
  simp only [Pi.add_apply, mul_add]
  exact integral_add i1 i2

theorem genPer_eta_smul (Q : PolCol ch.G × PolRow ch.G) (c : ℂ) ξ η :
    genPer ch t a M d y Q ξ (c • η) = c * genPer ch t a M d y Q ξ η := by
  rw [genPer_eq, genPer_eq, rowLift_eta_smul]
  simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm _ c, integral_const_mul]

theorem genPer_multilinear (hc : ∀ Q ξ η, GenConv ch t a M d y Q ξ η) :
    ∃ Φ : MultilinearMap (RingHom.id ℂ) (fun j : Fin D.R.m => PolF D (ch.G.V (.top ((j : ℕ) + 1))).rank (ch.G.V (.top j)).rank)
      (MultilinearMap (RingHom.id ℂ) (fun i : Fin D.R.m => PolF D (ch.G.V (.grid i D.R.m)).rank (ch.G.V (.grid ((i : ℕ) + 1) D.R.m)).rank)
        (Module.Dual ℂ (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ).W →ₗ[ℂ] Module.Dual ℂ R.cX.W →ₗ[ℂ] ℂ)),
      ∀ Q ξ η, Φ Q.1 Q.2 ξ η = genPer ch t a M d y Q ξ η := by
  refine ⟨
    { toFun := fun Q1 =>
        { toFun := fun Q2 => LinearMap.mk₂ ℂ (fun ξ η => genPer ch t a M d y (Q1, Q2) ξ η)
            (fun ξ ξ' η => genPer_xi_add ch t a M d y hc _ ξ ξ' η)
            (fun c ξ η => genPer_xi_smul ch t a M d y _ c ξ η)
            (fun ξ η η' => genPer_eta_add ch t a M d y hc _ ξ η η')
            (fun c ξ η => genPer_eta_smul ch t a M d y _ c ξ η)
          map_update_add' := fun Q2 i x x' => LinearMap.ext fun ξ => LinearMap.ext fun η =>
            genPer_row_add ch t a M d y hc Q1 Q2 i x x' ξ η
          map_update_smul' := fun Q2 i c x => LinearMap.ext fun ξ => LinearMap.ext fun η =>
            genPer_row_smul ch t a M d y Q1 Q2 i c x ξ η }
      map_update_add' := fun Q1 i x x' => MultilinearMap.ext fun Q2 => LinearMap.ext fun ξ => LinearMap.ext fun η =>
        genPer_col_add ch t a M d y hc Q1 Q2 i x x' ξ η
      map_update_smul' := fun Q1 i c x => MultilinearMap.ext fun Q2 => LinearMap.ext fun ξ => LinearMap.ext fun η =>
        genPer_col_smul ch t a M d y Q1 Q2 i c x ξ η }, fun Q ξ η => rfl⟩

end Multi2

end GlobalTheory.RowReal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmLiftOfMultilinearTprod
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.RowReal

variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : Sizes} (P : ι → Entries S)

def omLiftOfMultilinear
    (Φ : MultilinearMap (RingHom.id ℂ) (fun j : Fin S.m => Pol ι (S.nR j.castSucc) (S.nR j.succ))
      (MultilinearMap (RingHom.id ℂ) (fun i : Fin S.m => Pol ι (S.nC i.castSucc) (S.nC i.succ))
        (weylSub (S.nR (0 : Fin (S.m + 1))) (psiWt P) →ₗ[ℂ]
          Module.Dual ℂ (weylSub (S.nC (0 : Fin (S.m + 1))) (baseWt P)) →ₗ[ℂ] ℂ))) : OM P →ₗ[ℂ] ℂ :=
  TensorProduct.lift
    ((TensorProduct.uncurry (RingHom.id ℂ) _ _ ℂ).comp
      (((LinearMap.llcomp ℂ _ _ _ (TensorProduct.uncurry (RingHom.id ℂ) _ _ ℂ)).comp
        PiTensorProduct.lift.toLinearMap).comp (PiTensorProduct.lift Φ)))

theorem omLiftOfMultilinear_tprod
    (Φ : MultilinearMap (RingHom.id ℂ) (fun j : Fin S.m => Pol ι (S.nR j.castSucc) (S.nR j.succ))
      (MultilinearMap (RingHom.id ℂ) (fun i : Fin S.m => Pol ι (S.nC i.castSucc) (S.nC i.succ))
        (weylSub (S.nR (0 : Fin (S.m + 1))) (psiWt P) →ₗ[ℂ]
          Module.Dual ℂ (weylSub (S.nC (0 : Fin (S.m + 1))) (baseWt P)) →ₗ[ℂ] ℂ))) (x y v φ) :
    omLiftOfMultilinear P Φ (PiTensorProduct.tprod ℂ x ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ y ⊗ₜ[ℂ] (v ⊗ₜ[ℂ] φ))) =
      Φ x y v φ := by
  simp only [omLiftOfMultilinear, TensorProduct.lift.tmul, LinearMap.comp_apply, TensorProduct.uncurry_apply,
    LinearMap.llcomp_apply, LinearEquiv.coe_coe, PiTensorProduct.lift.tprod]

theorem invFun_of_multilinear : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {S : Sizes} (P : ι → Entries S)
    (Φ : MultilinearMap (RingHom.id ℂ) (fun j : Fin S.m => Pol ι (S.nR j.castSucc) (S.nR j.succ))
      (MultilinearMap (RingHom.id ℂ) (fun i : Fin S.m => Pol ι (S.nC i.castSucc) (S.nC i.succ))
        (weylSub (S.nR (0 : Fin (S.m + 1))) (psiWt P) →ₗ[ℂ]
          Module.Dual ℂ (weylSub (S.nC (0 : Fin (S.m + 1))) (baseWt P)) →ₗ[ℂ] ℂ)))
    (hΦ : ∀ g x y v φ, Φ (fun j => rowFock P j g (x j)) (fun i => colFock P i g (y i)) (psiRep P g v)
      ((baseRep P).dual g φ) = Φ x y v φ), ∃ l ∈ invFun (omRep P), ∀ x y v φ,
      l (PiTensorProduct.tprod ℂ x ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ y ⊗ₜ[ℂ] (v ⊗ₜ[ℂ] φ))) = Φ x y v φ := by
  intro ι _ _ S P Φ hΦ
  refine ⟨omLiftOfMultilinear P Φ, ?_, omLiftOfMultilinear_tprod P Φ⟩
  intro g z
  have key : (omLiftOfMultilinear P Φ).comp (omRep P g) = omLiftOfMultilinear P Φ := by
    ext x y v φ
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, TensorProduct.AlgebraTensorModule.curry_apply,
      TensorProduct.curry_apply, LinearMap.restrictScalars_apply]
    rw [omRep, Representation.tprod_apply, TensorProduct.map_tmul, Representation.tprod_apply,
      TensorProduct.map_tmul, Representation.tprod_apply, TensorProduct.map_tmul]
    simp only [piTprod, MonoidHom.comp_apply, PiTensorProduct.mapMonoidHom_apply, PiTensorProduct.map_tprod,
      Pi.monoidHom_apply, omLiftOfMultilinear_tprod]
    exact hΦ g x y v φ
  exact LinearMap.congr_fun key z

end GlobalTheory.RowReal

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestDefinitePeriodsInvariantFunctional
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowReal

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

def pullBil {V₁ V₂ W₁ W₂ : Type} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂] [AddCommGroup W₁]
    [Module ℂ W₁] [AddCommGroup W₂] [Module ℂ W₂] (a : V₁ →ₗ[ℂ] W₁) (b : V₂ →ₗ[ℂ] W₂) :
    (W₁ →ₗ[ℂ] W₂ →ₗ[ℂ] ℂ) →ₗ[ℂ] (V₁ →ₗ[ℂ] V₂ →ₗ[ℂ] ℂ) where
  toFun f := f.compl₁₂ a b
  map_add' f f' := by ext; simp
  map_smul' c f := by ext; simp

theorem invLine_of_iso [DecidableEq D.what₂.Tau] (ch : Choice R) {μ0 : T} (hL : R.toLevCh.Is μ0)
    (hlf : (∀ a ξ, ∀ γ ∈ GQ (ch.G.V (.top 0)), ∀ g,
      pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a) (γ * g) =
        pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a) g) ∧
      ∀ t y η, ∀ γ ∈ GQ (ch.G.V (.grid 0 D.R.m)), ∀ g, formGen ch t y η (γ * g) = formGen ch t y η g)
    (hc : ∀ t a, ch.S.SumOK t (ch.Phi a) → ∀ β ∈ ch.S.supp t (ch.Phi a), ∀ M : Vol ch.G,
      IsTermVol t ch.S.toGridChoice (ch.Phi a) β M → ∀ τ, ch.S.IsExpansion t (ch.Phi a) β τ → ∀ d ∈ τ.support,
        ∀ y Q ξ η, GenConv ch t a M d y Q ξ η)
    (Aψ : weylSub ((rowSizes D).nR (0 : Fin ((rowSizes D).m + 1))) (psiWt (rowEntries D ch.sc.cGap)) ≃ₗ[ℂ]
      Module.Dual ℂ (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ).W)
    (hA : ∀ g F, Aψ (psiRep (rowEntries D ch.sc.cGap) g F) =
      Aψ F ∘ₗ (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ).ρ ((kappa ch.W g).1 ⟨0, (rowSizes D).m_pos⟩)⁻¹)
    (Bf : Module.Dual ℂ (weylSub ((rowSizes D).nC (0 : Fin ((rowSizes D).m + 1))) (baseWt (rowEntries D ch.sc.cGap))) ≃ₗ[ℂ]
      Module.Dual ℂ R.cX.W)
    (hB : ∀ g φ, Bf ((baseRep (rowEntries D ch.sc.cGap)).dual g φ) =
      Bf φ ∘ₗ R.cX.ρ (cast (congrArg (fun X : LSp D => GA D X.sp) (colY_m R.toLevCh)) ((kappa ch.W g).2 0))⁻¹) :
    InvLine ch := by
  classical
  obtain ⟨tc, tr, htr⟩ := GlobalTheory.RowReal.exists_fock_transport hL ch.W
  refine ⟨D.what₂.Tau, inferInstance, inferInstance, rowSizes D, rowEntries D ch.sc.cGap,
    fun τ => rowEntries_good D _ τ, fun Q => PiTensorProduct.tprod ℂ (fun j => tc j (Q.1 j)) ⊗ₜ[ℂ]
      (PiTensorProduct.tprod ℂ (fun i => tr i (Q.2 i)) ⊗ₜ[ℂ] (Aψ.symm ch.ξ ⊗ₜ[ℂ] Bf.symm (R.prX.flip ch.cv.v))), ?_⟩
  intro t a hS β hβ M hM τ hτ d hd y
  obtain ⟨Φ0, hΦ0⟩ := GlobalTheory.RowReal.genPer_multilinear ch t a M d y (hc t a hS β hβ M hM τ hτ d hd y)
  let Irow := (LinearMap.compMultilinearMapₗ ℂ (pullBil Aψ.toLinearMap Bf.toLinearMap)) ∘ₗ
    (MultilinearMap.compLinearMapₗ (σ₂₃ := RingHom.id ℂ) (σ₁₃ := RingHom.id ℂ) (fun i : Fin D.R.m => (tr i).symm.toLinearMap))
  let Φ := (Irow.compMultilinearMap Φ0).compLinearMap (fun j : Fin D.R.m => (tc j).symm.toLinearMap)
  have hΦ : ∀ x₁ y₁ v₁ φ₁, Φ x₁ y₁ v₁ φ₁ =
      genPer ch t a M d y (fun j => (tc j).symm (x₁ j), fun i => (tr i).symm (y₁ i)) (Aψ v₁) (Bf φ₁) :=
    fun x₁ y₁ v₁ φ₁ => hΦ0 (fun j => (tc j).symm (x₁ j), fun i => (tr i).symm (y₁ i)) (Aψ v₁) (Bf φ₁)
  have hv := hS.vec β τ hτ d hd
  have hinv : ∀ g x₁ y₁ v₁ φ₁, Φ (fun j => rowFock (rowEntries D ch.sc.cGap) j g (x₁ j))
      (fun i => colFock (rowEntries D ch.sc.cGap) i g (y₁ i)) (psiRep (rowEntries D ch.sc.cGap) g v₁)
      ((baseRep (rowEntries D ch.sc.cGap)).dual g φ₁) = Φ x₁ y₁ v₁ φ₁ := by
    intro g x₁ y₁ v₁ φ₁
    rw [hΦ, hΦ, hA, hB]
    obtain ⟨h1, h2⟩ := htr ch.S.toGridChoice g t
    have e1 : ptTop ch.W g 0 = (kappa ch.W g).1 ⟨0, (rowSizes D).m_pos⟩ := ptTop_lt ch.W g _
    have e2 : ptGrid ch.W g 0 = (kappa ch.W g).2 0 := ptGrid_le ch.W g (Nat.succ_pos _)
    have key := GlobalTheory.RowReal.genPer_move ch hL t a M d y (fun j => ⟨_, hM.1 j j.2⟩) (fun i => ⟨_, hM.2 i (Nat.le_of_lt_succ i.2)⟩)
      hv.1 hv.2 (hlf.1 a) (hlf.2 t y) g (fun j => (tc j).symm (x₁ j), fun i => (tr i).symm (y₁ i))
      (fun j => (tc j).symm (rowFock (rowEntries D ch.sc.cGap) j g (x₁ j)),
        fun i => (tr i).symm (colFock (rowEntries D ch.sc.cGap) i g (y₁ i)))
      (fun j => by simpa using h1 j (d.1 j) (hv.1 j) ((tc j).symm (x₁ j)))
      (fun i => by simpa using h2 i (d.2 i) (hv.2 i) ((tr i).symm (y₁ i))) (Aψ v₁) (Bf φ₁)
    rw [e1, e2] at key
    exact key
  obtain ⟨l, hl, hle⟩ := GlobalTheory.RowReal.invFun_of_multilinear (rowEntries D ch.sc.cGap) Φ hinv
  refine ⟨l, hl, fun Q => ?_⟩
  rw [hle]
  refine Eq.trans ?_ (hΦ _ _ _ _).symm
  simp only [LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]
  rfl

theorem invLine_big : Big fun ch => InvLine ch := by
  obtain ⟨C1, h1⟩ := GlobalTheory.RowReal.gen_left
  obtain ⟨C2, h2⟩ := GlobalTheory.GenConvProof.genPer_conv
  refine ⟨max C1 C2, fun ε CF hCF => ?_⟩
  obtain ⟨x1, h1'⟩ := h1 ε CF (le_of_max_le_left hCF)
  obtain ⟨x2, h2'⟩ := h2 ε CF (le_of_max_le_right hCF)
  refine ⟨max x1 x2, fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch hsc => ?_⟩
  classical
  have hlf := h1' D large₂ he (le_of_max_le_left hx) Γ Pl0 T A Ks R F hS ch hch hsc
  have hc := h2' D large₂ he (le_of_max_le_right hx) Γ Pl0 T A Ks R F hS ch hch hsc
  have hL := hS.core.lev
  obtain ⟨Aψ, hA⟩ := GlobalTheory.CoefPsi.coefPsi ch.W (posOnb_of_defNode ch.W A.μ0 hL (X := .top 0) (Nat.zero_le _))
  obtain ⟨Bf, hB⟩ := GlobalTheory.CoefBase.coefBase ch hS.core.models.inf hS.core.models.cX hS.core.models.prX hch.weil
    (posOnb_of_defNode ch.W A.μ0 hL (X := .grid 0 D.R.m) ⟨Nat.zero_le _, rfl⟩)
  exact invLine_of_iso ch hL hlf hc Aψ hA Bf hB

end GlobalTheory.RowReal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestDefinitePeriodsInvariantFunctionalStatement
open GlobalTheory.RowClaim GlobalTheory.RowReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowTest_definitePeriods_invariant_functional : Big fun ch => InvLine ch := by
  first | exact @GlobalTheory.RowReal.invLine_big | exact GlobalTheory.RowReal.invLine_big | (intros; apply GlobalTheory.RowReal.invLine_big <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestRealPlacesDefinitePeriodsOnOneLine
open GlobalTheory.RowClaim GlobalTheory.RowReal

theorem GlobalTheory.RowReal.periodsOnLine_big : Big fun ch => PeriodsOnLine ch :=
  big_mono (fun ch h => periodsOnLine_of_invLine GlobalTheory.OneFunctional.oneLine ch h) GlobalTheory.T.rowTest_definitePeriods_invariant_functional
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestRealPlacesDefinitePeriodsOnOneLineStatement
open GlobalTheory.RowClaim GlobalTheory.RowReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowTest_realPlaces_definitePeriods_onOneLine : Big fun ch => PeriodsOnLine ch := by
  first | exact @GlobalTheory.RowReal.periodsOnLine_big | exact GlobalTheory.RowReal.periodsOnLine_big | (intros; apply GlobalTheory.RowReal.periodsOnLine_big <;> assumption)
end
end

namespace GlobalTheory.RowReal

open GlobalTheory.RowClaim

theorem realLine : Big fun ch => RealLine ch :=
  big_mono (fun ch h => realLine_of_periodsOnLine ch h) GlobalTheory.T.rowTest_realPlaces_definitePeriods_onOneLine

end GlobalTheory.RowReal
