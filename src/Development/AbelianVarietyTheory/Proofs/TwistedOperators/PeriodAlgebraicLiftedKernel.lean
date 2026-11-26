module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodAlgebraicIdealExpansion
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RepresentationAtEveryPlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OffPlacesPartMovedLevelKeepsStandardHomLattice
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowGrpEq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalVectorDownEdgeInterior
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPointActsOnVacuumByAlgebraicScalar

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodAlgebraicLiftedKernel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

namespace GlobalTheory.BotDictAlg

theorem applyAt0_isAlgebraic {D : D7} {N N' : ℕ} {P : MvPolynomial (GL3Theta.Idx D N N') ℂ} {G : TaylorLogMetric.VC D N N' → ℂ}
    (hP : ∀ α, IsAlgebraic ℚ (P.coeff α)) (hG : TaylorLogMetric.CoefIn D G TaylorLogMetric.Qbar) : IsAlgebraic ℚ (GL3Theta.applyAt0 D P G) := by
  rw [← mem_algebraicClosure_iff]
  unfold GL3Theta.applyAt0
  refine sum_mem fun α _ => mul_mem (mul_mem ((mem_algebraicClosure_iff).2 (hP α)) ?_) (hG α)
  exact prod_mem fun _ _ => natCast_mem _ _

theorem even_bot {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW} (hX : IsBottomTri W i j X) : Even (A'.rank * WW.rank) := by
  refine Even.mul_left ?_ _
  have h1 := hX.rank
  have h2 := hX.rank'
  have h3 := hX.is.rank
  have h4 := SqNum.ranks_exact D i j
  rw [← h3, h1, h2]
  refine ⟨SqNum.halfRank D i j - (D.R.m - (j.1 + 1)) / 2 - (D.R.m - j.1) / 2, ?_⟩
  omega

end GlobalTheory.BotDictAlg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestMemLatticeStabilizerOfLocalMatrices
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestMemLatticeStabilizerOfLocalMatrices
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.LatOfHasLoc

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


set_option maxHeartbeats 800000 in
theorem mem_latGrp_of_hasLoc : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ t, ∀ j, 1 ≤ j → ∀ (hj : j ≤ D.R.m)
    (x : GA D (ch.G.V (.grid D.R.m j)))
    (g : ∀ w : locPl ch.G t, GL (Fin ((locGrid ch.G t w.1).rank (D.R.m, j))) (Kw w.1)),
    HasLoc t ch.S.B hj x g → (∀ w, g w ∈ givenLevel ch.G t w.1 (D.R.m, j)) → x ∈ latGrp ch.G j := by
  refine ⟨0, fun _ _ _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch _ _ => ?_⟩⟩
  intro t j h1 hj x g hx hg
  obtain ⟨e, he, hsupp, hloc⟩ := hx
  have hm : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
  have e0 : infPart D e = 0 := (GlobalTheory.FunObj.Comparison₂.cpt_idemSum he).1
  have e0' : infPart D (cA D e) = 0 := GlobalTheory.PlaceDatum.infPart_cA e0
  refine ⟨GlobalTheory.LevelCut.mem_GfC_of _ x fun i k => ?_, ?_⟩
  · rw [← hsupp i k, map_mul, map_add (f := _), e0, e0', add_zero, zero_mul]
  · have hl : ∀ (w : Pl D.host.E) (X : ℕ × ℕ), 1 ≤ X.1 → 1 ≤ X.2 →
        givenLevel ch.G t w X = GlobalTheory.SplitWeil.KO (Kw w) _ := by
      rintro w ⟨_ | a, _ | b⟩ h h'
      · omega
      · simp at h
      · simp at h'
      · rfl
    have hβ : IsFrame (ch.S.B.β D.R.m j) (ch.G.Λ (.grid D.R.m j)) := ch.S.B.isFrame_β hS.core.lev le_rfl hj
    have hsd : IsSelfDualC _ (ch.G.Λ (.grid D.R.m j)) :=
      (ch.G.isV (X := .grid D.R.m j) ⟨le_rfl, hj⟩ fun k h => by
        have := (Node.grid.inj h).1; omega).sd
    set c : Lev.EAf D := toEAf D (e + cA D e) with hc
    have hX : (Lev.finE (ch.G.V (.grid D.R.m j)) x).val =
        c • (Lev.finE (ch.G.V (.grid D.R.m j)) x).val + (1 - c) • (1 : Matrix _ _ (Lev.EAf D)) := by
      have hM : (Lev.finE (ch.G.V (.grid D.R.m j)) x).val = (mt _ x).map (toEAf D) := rfl
      rw [hM]
      ext i k
      have h0 := congrArg (toEAf D) (hsupp i k)
      rw [map_mul, Matrix.sub_apply, map_sub] at h0
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.map_apply]
      by_cases hik : i = k
      · subst hik
        simp only [Matrix.one_apply_eq, map_one] at h0 ⊢
        rw [← hc] at h0
        linear_combination -h0
      · simp only [Matrix.one_apply_ne hik, map_zero, sub_zero, mul_zero, add_zero] at h0 ⊢
        exact h0.symm
    have key := GlobalTheory.FunObj.LevRowSucc.prodLev_inf_UA (V := ch.G.V (.grid D.R.m j)) (Λ := ch.G.Λ (.grid D.R.m j))
      (β := ch.S.B.β D.R.m j) hβ hsd (locPl ch.G t) (n' := fun w => (locGrid ch.G t w.1).rank (D.R.m, j))
      (fun w => rank_vertex ch.G t w.1 (X := (D.R.m, j)) ⟨le_rfl, hj⟩) (fun w => GlobalTheory.SplitWeil.KO (Kw w.1) _) fun _ => rfl
    have hmax : Lev.finE (ch.G.V (.grid D.R.m j)) x ∈ ch.G.levMax (.grid D.R.m j) := by
      rw [GridData.levMax, ← key]
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨Subgroup.mem_iInf.2 fun w => ?_,
        Subgroup.mem_iInf.2 fun w' => Subgroup.mem_iInf.2 fun hw' => ?_⟩, GlobalTheory.LevSplit.finE_mem_UA _ x⟩
      · rw [Subgroup.mem_comap, hloc w]
        have := hg w
        rw [hl w.1 (D.R.m, j) hm h1] at this
        exact this
      · rw [Subgroup.mem_comap, (GlobalTheory.OffPartLattice.inBasis_mix (ch.S.B.β D.R.m j) _ _ c hX w').1
          (GlobalTheory.OffPartLattice.cpt_pair_zero (ch.G.V (.grid D.R.m j)) he w' hw')]
        exact one_mem _
    exact hmax

end GlobalTheory.LatOfHasLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestMemLatticeStabilizerOfLocalMatricesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowTest_mem_latticeStabilizer_of_localMatrices : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ t, ∀ j, 1 ≤ j → ∀ (hj : j ≤ D.R.m) (x : GA D (ch.G.V (.grid D.R.m j)))
    (g : ∀ w : locPl ch.G t, GL (Fin ((locGrid ch.G t w.1).rank (D.R.m, j))) (Kw w.1)),
    HasLoc t ch.S.B hj x g → (∀ w, g w ∈ givenLevel ch.G t w.1 (D.R.m, j)) → x ∈ latGrp ch.G j := by
  first | exact @GlobalTheory.LatOfHasLoc.mem_latGrp_of_hasLoc | exact GlobalTheory.LatOfHasLoc.mem_latGrp_of_hasLoc | (intros; apply GlobalTheory.LatOfHasLoc.mem_latGrp_of_hasLoc <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GivenPathRepresentationFinite
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FlipStart

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem restrictPol_comp (P : PolE G) {X Y : Node} (p : Path T X Y) : ∀ {Z : Node} (q : Path T Y Z),
    restrictPol P (p.comp q) = Path.Fam.append (restrictPol P p) (restrictPol P q)
  | _, .nil => rfl
  | _, .snoc a q => by
    show (restrictPol P (p.comp q), polOf P a) = (Path.Fam.append (restrictPol P p) (restrictPol P q), polOf P a)
    rw [restrictPol_comp P p q]

theorem zip_append {S S' S'' : Arrow T → Type} (φ : ∀ a, S a → S' a → S'' a) {X Y : Node} {p : Path T X Y} (d : p.Fam S)
    (d' : p.Fam S') : ∀ {Z : Node} (q : Path T Y Z) (e : q.Fam S) (e' : q.Fam S'),
    Path.Fam.zip φ (d.append e) (d'.append e') = (Path.Fam.zip φ d d').append (Path.Fam.zip φ e e')
  | _, .nil, _, _ => rfl
  | _, .snoc a q, e, e' => by
    show (Path.Fam.zip φ (d.append e.1) (d'.append e'.1), φ a e.2 e'.2) =
      ((Path.Fam.zip φ d d').append (Path.Fam.zip φ e.1 e'.1), φ a e.2 e'.2)
    rw [zip_append φ d d' q e.1 e'.1]

theorem zip_rowFam {S S' S'' : Arrow T → Type} (φ : ∀ a, S a → S' a → S'' a) (j : ℕ) : ∀ n (f : ∀ i : Fin n, S (.right i j))
    (g : ∀ i : Fin n, S' (.right i j)), Path.Fam.zip φ (rowFam j n f) (rowFam j n g) = rowFam j n fun i => φ _ (f i) (g i)
  | 0, _, _ => rfl
  | n + 1, f, g => by
    show (Path.Fam.zip φ (rowFam j n fun i => f i.castSucc) (rowFam j n fun i => g i.castSucc), φ _ (f (Fin.last n)) (g (Fin.last n))) =
      (rowFam j n fun i => φ _ (f i.castSucc) (g i.castSucc), φ _ (f (Fin.last n)) (g (Fin.last n)))
    rw [zip_rowFam φ j n]

theorem zip_downFam {S S' S'' : Arrow T → Type} (φ : ∀ a, S a → S' a → S'' a) (t : T) (i : ℕ) : ∀ n (f : ∀ j : Fin n, S (.down t i j))
    (g : ∀ j : Fin n, S' (.down t i j)), Path.Fam.zip φ (downFam t i n f) (downFam t i n g) = downFam t i n fun j => φ _ (f j) (g j)
  | 0, _, _ => rfl
  | n + 1, f, g => by
    show Path.Fam.zip φ (Path.Fam.append (p := Path.one (.down t i n)) ((), f (Fin.last n)) (downFam t i n fun j => f j.castSucc))
        (Path.Fam.append (p := Path.one (.down t i n)) ((), g (Fin.last n)) (downFam t i n fun j => g j.castSucc)) =
      Path.Fam.append (p := Path.one (.down t i n)) ((), φ _ (f (Fin.last n)) (g (Fin.last n)))
        (downFam t i n fun j => φ _ (f j.castSucc) (g j.castSucc))
    refine (zip_append φ (p := Path.one (.down t i n)) (((), f (Fin.last n)) : (Path.one (.down t i n)).Fam S)
      (((), g (Fin.last n)) : (Path.one (.down t i n)).Fam S') (downPath t i n) (downFam t i n fun j => f j.castSucc)
      (downFam t i n fun j => g j.castSucc)).trans ?_
    rw [zip_downFam φ t i n]
    rfl

theorem restrictPol_rowPath (P : PolE G) (j : ℕ) : ∀ n, restrictPol P (rowPath T j n) = rowFam j n fun i => polOf P (.right i j)
  | 0 => rfl
  | n + 1 => by
    show (restrictPol P (rowPath T j n), polOf P (.right n j)) = (rowFam j n fun i => polOf P (.right (i.castSucc : Fin (n + 1)) j), _)
    rw [restrictPol_rowPath P j n]
    rfl

theorem restrictPol_downPath (P : PolE G) (t : T) (i : ℕ) : ∀ n,
    restrictPol P (downPath t i n) = downFam t i n fun j => polOf P (.down t i j)
  | 0 => rfl
  | n + 1 => by
    show restrictPol P ((Path.one (.down t i n)).comp (downPath t i n)) = _
    rw [restrictPol_comp, restrictPol_downPath P t i n]
    rfl

theorem tensE_single (W : G.Weil) {X Y : Node} (p : Path T X Y) (P : PolE G) (d : PureT G p) (c : ℂ) :
    tensE W p (Finsupp.single P 1) (Finsupp.single d c) =
      Finsupp.single (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d (restrictPol P p)) c := by
  unfold tensE tensT
  rw [Finsupp.mapDomain_single, Finsupp.sum_single_index, Finsupp.sum_single_index, one_mul]
  · simp
  · simp

theorem zip_given (W : G.Weil) (t : T) (ρ : G.RealVec) (q : ∀ j : ℕ, PolF D (G.V (.grid 0 (j + 1))).rank (G.V (.grid 0 j)).rank)
    (f : ∀ j : Fin D.R.m, Sch G (.down t 0 j)) (Φ : G.Datum) :
    Path.Fam.zip (fun a (g : Sch G a) Q => W.fock a.pair g Q) (givenFin W t f Φ) (restrictPol (gPol ρ q) (givenPath t D.R.m)) =
      Path.Fam.append (colPure W t f fun j => q j) (rowDatum W ρ Φ) := by
  unfold givenFin givenPath
  rw [restrictPol_comp, zip_append, restrictPol_downPath, restrictPol_rowPath, zip_downFam, zip_rowFam]
  congr 1
  unfold rowDatum
  congr 1
  funext i
  show W.fock (.chi i 0) (W.cosVec i (Φ i)) (if h : (i : ℕ) < D.R.m then ρ ⟨i, h⟩ else 0) = W.datum ρ Φ i
  rw [dite_eq_left i.2]
  rfl

end GlobalTheory.FlipStart


end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstRowVertexWeilValue
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstRowArgumentConjugateMoveLeftMulInvComponent
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstRowArgumentConjugateMoveLeftMulInvComponent
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.FirstRowCoord

open GlobalTheory.RowMoveAt

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem actO_chi_small (i : ℕ) (M : GA D (G.V (.grid i D.R.m)))
    (x : WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))) :
    actO _ _ (G.toPair (.chi i D.R.m) M 1).1⁻¹ (G.toPair (.chi i D.R.m) M 1).2⁻¹ x =
      mt (G.V (.grid i D.R.m)) M⁻¹ * (x : Matrix _ _ (AE D)) := by
  simp only [actO, GridData.toPair, inv_inv, map_one, inv_one]
  rw [show mt (G.pS (.chi i D.R.m : Pair T)) 1 = 1 from rfl, Matrix.mul_one]

theorem rowAt_first_move : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T},
    t ∈ U → ∀ w ∈ locPl G t, ∀ (k : FinPt G (.grid 0 D.R.m))
      (ys : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))),
      S.rowAt t w (Function.update ys (GlobalTheory.FirstRowVertex.firstIx D) (actO (G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T))
        (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).1⁻¹
        (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).2⁻¹ (ys (GlobalTheory.FirstRowVertex.firstIx D)))) =
      Function.update (S.rowAt t w ys) 0 (((GlobalTheory.FirstRowTermLaw.kapAt S t w k)⁻¹ : GL (Fin ((locGrid G t w).rank (0, (locGrid G t w).m))) (Kw w)).val * S.rowAt t w ys 0) := by
  intro D T L sc G W U S t ht w hw k ys
  have hX : DefNode D.R.m (.grid 0 D.R.m) := ⟨Nat.zero_le _, rfl⟩
  obtain ⟨P, e, he, hsupp, hoff⟩ := S.N.u_supp _ hX
  have hn := notOff S ht hw
  have hu := map_mt_eq_one hn he hoff hsupp
  have hu' := map_mt_eq_one hn he hoff (GlobalTheory.StdHalfLat.suppAt_inv' hsupp)
  have hM' : (mt _ ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1⁻¹).map ((cpt w).comp (toEAf D)) =
      (loc w (finG (G.V (.grid 0 D.R.m)) k⁻¹)).val := by
    rw [show mt _ ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1⁻¹ =
        mt _ (S.N.u (.grid 0 D.R.m)).1⁻¹ * mt _ k.1⁻¹ * mt _ (S.N.u (.grid 0 D.R.m)).1 from by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv, mul_assoc]; rfl,
      Matrix.map_mul, Matrix.map_mul, hu, hu', Matrix.one_mul, Matrix.mul_one]
    rfl
  have h0 : 0 < D.R.m := (GlobalTheory.FirstRowVertex.firstIx D).2
  funext i
  by_cases h1 : i = 0
  · subst h1
    rw [Function.update_self]
    simp only [GridChoice.rowAt, dif_pos h0, Frames.coord]
    erw [Function.update_self, actO_chi_small 0, Matrix.map_mul, hM']
    erw [Matrix.transpose_transpose, Matrix.transpose_transpose]
    rw [GlobalTheory.FirstRowTermLaw.kapAt]
    erw [← map_inv (inBasis _ (S.B.β 0 D.R.m) w)]
    rw [map_inv (finG (G.V (Node.grid 0 D.R.m))) k]
    erw [inBasis_val, mul_sub_cast]
    rfl
  · rw [Function.update_of_ne h1]
    simp only [GridChoice.rowAt]
    by_cases hi : i < D.R.m
    · rw [dif_pos hi, dif_pos hi, Function.update_of_ne (fun h => h1 (congrArg Fin.val h))]
    · rw [dite_eq_right hi, dite_eq_right hi]

end GlobalTheory.FirstRowCoord
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstRowArgumentConjugateMoveLeftMulInvComponentStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.firstRowArgument_conjugateMove_left_mul_inv_component : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T},
    t ∈ U → ∀ w ∈ locPl G t, ∀ (k : FinPt G (.grid 0 D.R.m))
      (ys : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))),
      S.rowAt t w (Function.update ys (GlobalTheory.FirstRowVertex.firstIx D) (actO (G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T))
        (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).1⁻¹
        (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).2⁻¹ (ys (GlobalTheory.FirstRowVertex.firstIx D)))) =
      Function.update (S.rowAt t w ys) 0 (((GlobalTheory.FirstRowTermLaw.kapAt S t w k)⁻¹ : GL (Fin ((locGrid G t w).rank (0, (locGrid G t w).m))) (Kw w)).val * S.rowAt t w ys 0) := by
  first | exact @GlobalTheory.FirstRowCoord.rowAt_first_move | exact GlobalTheory.FirstRowCoord.rowAt_first_move | (intros; apply GlobalTheory.FirstRowCoord.rowAt_first_move <;> assumption)
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.FirstRowTermLaw

theorem law_gen {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {t : T} (ht : t ∈ U) {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ}
    (hτ : S.IsExpansion t Φ β τ) (k : FinPt G (.grid 0 D.R.m)) (lam : locPl G t → ℂ)
    (hlam : ∀ w : locPl G t, (locGrid G t w).pathAct .one (GlobalTheory.SplitFlip.oppositePath D.R.m)
      (Pi.mulSingle (0, D.R.m) (kapAt S t w k)) (Tflip W S.B t Φ w) = lam w • Tflip W S.B t Φ w)
    (s : ℂ) (hs : s * ∏ w, lam w = ∏ w : locPl G t, (locGrid G t w).edgeFactor .one (Pi.mulSingle (0, D.R.m) (kapAt S t w k)) (.ex 0 D.R.m))
    (xs : ∀ j : Fin D.R.m, WO (G.pS (.top t j)) (G.pT (.top t j)))
    (ys : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))) :
    s * (τ.sum fun d a' => a' * (∏ j, (d.1 j).fn (xs j)) * ∏ i, (d.2 i).fn (Function.update ys (GlobalTheory.FirstRowVertex.firstIx D) ((actO (G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).1⁻¹ (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).2⁻¹) (ys (GlobalTheory.FirstRowVertex.firstIx D))) i)) =
      τ.sum fun d a' => a' * (∏ j, (d.1 j).fn (xs j)) * ∏ i, (d.2 i).fn (ys i) := by
  obtain ⟨e, he, hsupp, hexp⟩ := hτ
  have hm : D.R.m ≠ 0 := by have := D.R.two_le_m; omega
  by_cases hh : (∀ j, IsHalf e (xs j)) ∧ ∀ i, IsHalf e (ys i)
  · have hh' : ∀ i, IsHalf e (Function.update ys (GlobalTheory.FirstRowVertex.firstIx D) ((actO (G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).1⁻¹ (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).2⁻¹) (ys (GlobalTheory.FirstRowVertex.firstIx D))) i) := by
      intro i
      by_cases h : i = (GlobalTheory.FirstRowVertex.firstIx D)
      · subst h; rw [Function.update_self]; exact (GlobalTheory.SchrMove.isHalf_actO_iff _ _ _).2 (hh.2 _)
      · rw [Function.update_of_ne h]; exact hh.2 i
    rw [hexp xs _ hh.1 hh', hexp xs ys hh.1 hh.2]
    have hloc : ∀ w : locPl G t, (locGrid G t w).edgeFactor .one (Pi.mulSingle (0, D.R.m) (kapAt S t w k)) (.ex 0 D.R.m) *
        (S.term t Φ β w).datum (S.colAt t w xs) (S.rowAt t w (Function.update ys (GlobalTheory.FirstRowVertex.firstIx D) ((actO (G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).1⁻¹ (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).2⁻¹) (ys (GlobalTheory.FirstRowVertex.firstIx D))))) =
        lam w * (S.term t Φ β w).datum (S.colAt t w xs) (S.rowAt t w ys) := by
      intro w
      rw [GlobalTheory.T.firstRowArgument_conjugateMove_left_mul_inv_component S ht w w.2 k ys]
      exact GlobalTheory.FirstRowTermLaw.datum_law (Γ := locGrid G t w) one_le_sLen hm _ _ _ _ _ _ _ _ (hlam w) _ _
    have hprod := Finset.prod_congr rfl fun w (_ : w ∈ Finset.univ) => hloc w
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib] at hprod
    exact key_cancel _ _ _ _ _ (Finset.prod_ne_zero_iff.2 fun w _ => edgeFactor_ne_zero _ _ _) hs hprod
  · have hz : ∀ d ∈ τ.support, (∏ j, (d.1 j).fn (xs j)) * ∏ i, (d.2 i).fn (ys i) = 0 ∧
        (∏ j, (d.1 j).fn (xs j)) * ∏ i, (d.2 i).fn (Function.update ys (GlobalTheory.FirstRowVertex.firstIx D) ((actO (G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).1⁻¹ (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).2⁻¹) (ys (GlobalTheory.FirstRowVertex.firstIx D))) i) = 0 := by
      intro d hd
      have hX : ∀ j, (d.1 j).fn (xs j) ≠ 0 → IsHalf e (xs j) := fun j h => ((hsupp d hd).1 j).2.1 ▸ (d.1 j).sb.1 _ h
      have hY : ∀ i y, (d.2 i).fn y ≠ 0 → IsHalf e y := fun i y h => ((hsupp d hd).2 i).2.1 ▸ (d.2 i).sb.1 _ h
      by_cases hx : ∀ j, IsHalf e (xs j)
      · obtain ⟨i, hi⟩ : ∃ i, ¬ IsHalf e (ys i) := by
          by_contra hc; push_neg at hc; exact hh ⟨hx, hc⟩
        have h1 : (d.2 i).fn (ys i) = 0 := by by_contra h; exact hi (hY i _ h)
        have h2 : (d.2 i).fn (Function.update ys (GlobalTheory.FirstRowVertex.firstIx D) ((actO (G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).1⁻¹ (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).2⁻¹) (ys (GlobalTheory.FirstRowVertex.firstIx D))) i) = 0 := by
          by_contra h
          have h' := hY i _ h
          by_cases hi0 : i = (GlobalTheory.FirstRowVertex.firstIx D)
          · subst hi0; rw [Function.update_self] at h'; exact hi ((GlobalTheory.SchrMove.isHalf_actO_iff _ _ _).1 h')
          · rw [Function.update_of_ne hi0] at h'; exact hi h'
        exact ⟨by rw [show (∏ i, (d.2 i).fn (ys i)) = 0 from Finset.prod_eq_zero (Finset.mem_univ i) h1, mul_zero],
          by rw [show (∏ i, (d.2 i).fn (Function.update ys (GlobalTheory.FirstRowVertex.firstIx D) ((actO (G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).1⁻¹ (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).2⁻¹) (ys (GlobalTheory.FirstRowVertex.firstIx D))) i)) = 0 from
            Finset.prod_eq_zero (Finset.mem_univ i) h2, mul_zero]⟩
      · push_neg at hx
        obtain ⟨j, hj⟩ := hx
        have h1 : (d.1 j).fn (xs j) = 0 := by by_contra h; exact hj (hX j h)
        rw [show (∏ j, (d.1 j).fn (xs j)) = 0 from Finset.prod_eq_zero (Finset.mem_univ j) h1]
        simp only [zero_mul, and_self]
    simp only [Finsupp.sum]
    rw [Finset.sum_eq_zero fun d hd => by rw [mul_assoc, (hz d hd).2, mul_zero],
      Finset.sum_eq_zero fun d hd => by rw [mul_assoc, (hz d hd).1, mul_zero], mul_zero]

end GlobalTheory.FirstRowTermLaw

namespace GlobalTheory.FirstRowTermLaw


end GlobalTheory.FirstRowTermLaw

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumBasePointUniqueAllTuples
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumBasePointUniqueAllTuples
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowBaseUniq
open GlobalTheory.RootEx GlobalTheory.RowRep
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem smul_eq_of_adj {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] {c : R} {A A' X X' G H : Matrix n n R}
    (h : A * (G * X) = G) (h' : A' * (G * X') = G) (hH : G * H = 1) (e : c • A = c • A') : c • X = c • X' := by
  have h1 : A * G * (X * H) = 1 := by rw [← Matrix.mul_assoc, Matrix.mul_assoc A, h, hH]
  have h2 : X * H * (A * G) = 1 := mul_eq_one_comm.1 h1
  have h3 : A * G * (c • X) = A * G * (c • X') := by
    rw [Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_assoc, Matrix.mul_assoc, h, ← Matrix.smul_mul, e, Matrix.smul_mul, h']
  have h4 := congrArg (X * H * ·) h3
  simp only [← Matrix.mul_assoc (X * H) (A * G), h2, Matrix.one_mul] at h4
  exact h4

theorem eq_of_halves {R : Type} [CommRing R] {n : Type} [DecidableEq n] {a b : R} {X X' : Matrix n n R}
    (h : ∀ i j, (a + b) * (X - 1) i j = (X - 1) i j) (h' : ∀ i j, (a + b) * (X' - 1) i j = (X' - 1) i j)
    (ha : a • X = a • X') (hb : b • X = b • X') : X = X' := by
  ext i j
  have k1 : a * X i j = a * X' i j := congrFun (congrFun ha i) j
  have k2 : b * X i j = b * X' i j := congrFun (congrFun hb i) j
  have k3 := h i j
  have k4 := h' i j
  simp only [Matrix.sub_apply] at k3 k4
  linear_combination k1 + k2 - k3 + k4

theorem supp_shrink {R : Type} [CommRing R] {n : Type} [DecidableEq n] {a b a' b' : R} {X : Matrix n n R}
    (h : ∀ i j, (a + b) * (X - 1) i j = (X - 1) i j) (ha : (a - a') • X = (a - a') • (1 : Matrix n n R))
    (hb : (b - b') • X = (b - b') • (1 : Matrix n n R)) (i j : n) : (a' + b') * (X - 1) i j = (X - 1) i j := by
  have k1 : (a - a') * X i j = (a - a') * (1 : Matrix n n R) i j := congrFun (congrFun ha i) j
  have k2 : (b - b') * X i j = (b - b') * (1 : Matrix n n R) i j := congrFun (congrFun hb i) j
  have k3 := h i j
  simp only [Matrix.sub_apply] at k3 ⊢
  linear_combination k3 - k1 - k2

variable {D : D7}

theorem smul_conj {V : HSp D} {e : AE D} {g g' : GA D V} (h : e • mt V g = e • mt V g') :
    cA D e • mt V g = cA D e • mt V g' :=
  smul_eq_of_adj (mt_unitary V g) (mt_unitary V g') (gA_mul_giA V)
    ((adj_smul e _).symm.trans ((congrArg adj h).trans (adj_smul e _)))

theorem smul_eq_of_loc {V : HSp D} {e : AE D} (h0 : infPart D e = 0) {g g' : GA D V}
    (h : ∀ w : Pl D.host.E, piAt w e = 0 ∨ GlobalTheory.StdFrames.loc w (Lev.finE V g) = GlobalTheory.StdFrames.loc w (Lev.finE V g')) :
    e • mt V g = e • mt V g' := by
  refine mx_ext ?_ fun w => ?_
  · rw [map_smul_mx, map_smul_mx, h0, zero_smul, zero_smul]
  · rw [map_smul_mx, map_smul_mx]
    rcases h w with h | h
    · rw [h, zero_smul, zero_smul]
    · exact congrArg (piAt w e • ·) (congrArg Units.val h)

theorem loc_eq_of_inBasis {n n' : ℕ} (h : n' = n) (β : GL (Fin n) (Lev.EAf D)) (w : Pl D.host.E) {x y : GL (Fin n) (Lev.EAf D)}
    (e : inBasis h β w x = inBasis h β w y) : GlobalTheory.StdFrames.loc w x = GlobalTheory.StdFrames.loc w y := by
  have e1 : GlobalTheory.StdFrames.loc w (β⁻¹ * x * β⁻¹⁻¹) = GlobalTheory.StdFrames.loc w (β⁻¹ * y * β⁻¹⁻¹) :=
    (GlobalTheory.StepData.reGL _).injective e
  rw [map_mul, map_mul, map_mul, map_mul] at e1
  exact mul_left_cancel (mul_right_cancel e1)

theorem isFinOf_unique {V : HSp D} {g b b' : GA D V} (h : IsFinOf g b) (h' : IsFinOf g b') : b = b' := by
  obtain ⟨hb, a, ha, e⟩ := h
  obtain ⟨hb', a', ha', e'⟩ := h'
  have i : infHom V b = infHom V b' := (MonoidHom.mem_ker.1 hb).trans (MonoidHom.mem_ker.1 hb').symm
  have f : finHom V b = finHom V b' := by
    have := congrArg (finHom V) (e.trans e'.symm)
    rwa [map_mul, map_mul, MonoidHom.mem_ker.1 ha, MonoidHom.mem_ker.1 ha', one_mul, one_mul] at this
  have f' : Lev.finE V b = Lev.finE V b' := congrArg (Formalism.UG.bc (Lev.swapAE D)) f
  refine Subtype.ext (Units.ext (mx_ext (congrArg Units.val i) fun w => ?_))
  exact congrArg (fun z => (GlobalTheory.StdFrames.loc w z).val) f'

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem exists_indicator (P : Finset (Pl D.host.E)) :
    ∃ e : AE D, infPart D e = 0 ∧ (∀ w ∈ P, piAt w e = 1) ∧ ∀ w ∉ P, piAt w e = 0 := by
  obtain ⟨X, a, b, c⟩ := exists_lift (n := 1) P fun _ => 1
  exact ⟨X 0 0, congrFun (congrFun a 0) 0, fun w hw => (congrFun (congrFun (b ⟨w, hw⟩) 0) 0).trans (one_apply_eq _),
    fun w hw => congrFun (congrFun (c w hw) 0) 0⟩

theorem stair_off (t : T) {w : Pl D.host.E} (hw : w ∉ G.pl.W0) (j : ℕ) :
    stair (locGrid G t w) (unifAt w) (cosExp G w) j = 1 := by
  rw [(depthAt_of_notMem G hw).1, stair]
  simp only [zero_mul, pow_zero]
  exact Units.ext diagonal_one

theorem supp_base (B : Frames G) {t : T} {r : GA D (G.V (.grid D.R.m 0))}
    (h : HasLoc t B (Nat.zero_le _) r fun w => (stair (locGrid G t w.1) (unifAt w.1) (cosExp G w.1) 0)⁻¹) {e₀ : AE D}
    (h0 : infPart D e₀ = 0) (h1 : ∀ w ∈ G.pl.W0, piAt w e₀ = 1) (h2 : ∀ w ∉ G.pl.W0, piAt w e₀ = 0) : SuppAt e₀ _ r := by
  classical
  obtain ⟨e, he, hs, hl⟩ := h
  obtain ⟨e0, e1, e2⟩ := GlobalTheory.FunObj.Comparison₂.cpt_idemSum he
  replace e1 : ∀ w ∈ locPl G t, piAt w e = 1 := e1
  replace e2 : ∀ w ∉ locPl G t, piAt w e = 0 := e2
  have hsub : ∀ w ∈ G.pl.W0, w ∈ locPl G t := fun w hw => by
    unfold locPl; convert Finset.mem_union_left _ hw
  have k : (e - e₀) • mt _ r = (e - e₀) • mt _ (1 : GA D (G.V (.grid D.R.m 0))) := by
    refine smul_eq_of_loc (by rw [RingHom.map_sub, e0, h0, sub_self]) fun w => ?_
    by_cases hw : w ∈ G.pl.W0
    · exact .inl (by rw [RingHom.map_sub, e1 w (hsub w hw), h1 w hw, sub_self])
    · by_cases hp : w ∈ locPl G t
      · refine .inr (loc_eq_of_inBasis _ (B.β D.R.m 0) w ((hl ⟨w, hp⟩).trans ?_))
        rw [map_one, map_one]
        exact inv_eq_one.2 (stair_off t hw 0)
      · exact .inl (by rw [RingHom.map_sub, e2 w hp, h2 w hw, sub_self])
  have k' := smul_conj k
  rw [RingHom.map_sub] at k'
  rw [GlobalTheory.MixModel.mt_one] at k k'
  exact supp_shrink hs k k'

theorem base_zero (B : Frames G) {t t' : T} {r r' : GA D (G.V (.grid D.R.m 0))}
    (h : HasLoc t B (Nat.zero_le _) r fun w => (stair (locGrid G t w.1) (unifAt w.1) (cosExp G w.1) 0)⁻¹)
    (h' : HasLoc t' B (Nat.zero_le _) r' fun w => (stair (locGrid G t' w.1) (unifAt w.1) (cosExp G w.1) 0)⁻¹) : r = r' := by
  classical
  obtain ⟨e₀, h0, h1, h2⟩ := exists_indicator (D := D) G.pl.W0
  have s := supp_base B h h0 h1 h2
  have s' := supp_base B h' h0 h1 h2
  obtain ⟨-, -, -, hl⟩ := h
  obtain ⟨-, -, -, hl'⟩ := h'
  have hsub : ∀ t, ∀ w ∈ G.pl.W0, w ∈ locPl G t := fun t w hw => by
    unfold locPl; convert Finset.mem_union_left _ hw
  have k : e₀ • mt _ r = e₀ • mt _ r' := by
    refine smul_eq_of_loc h0 fun w => ?_
    by_cases hw : w ∈ G.pl.W0
    · exact .inr (loc_eq_of_inBasis _ (B.β D.R.m 0) w ((hl ⟨w, hsub t w hw⟩).trans (hl' ⟨w, hsub t' w hw⟩).symm))
    · exact .inl (h2 w hw)
  exact Subtype.ext (Units.ext (eq_of_halves s s' k (smul_conj k)))

theorem isBase_eq (B : Frames G) {t t' : T} {b b' : Pts G} (h : IsBase t B b) (h' : IsBase t' B b') : b = b' := by
  funext j
  by_cases h0 : j = 0
  · subst h0
    exact base_zero B h.1 h'.1
  · by_cases hj : j ∈ GlobalTheory.RowVal.idx D
    · obtain ⟨δ, hδ, hb⟩ := h.2.1 j hj
      obtain ⟨δ', hδ', hb'⟩ := h'.2.1 j hj
      obtain rfl := isTilt_unique (by have := idx_le hj; omega) hδ hδ'
      exact isFinOf_unique hb hb'
    · rw [h.2.2 j h0 hj, h'.2.2 j h0 hj]

theorem isBase_unique : Big fun ch => ∀ t t' b b', IsBase t ch.S.B b → IsBase t' ch.S.B b' → b = b' :=
  ⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ _ _ _ _ h h' => isBase_eq ch.S.B h h'⟩⟩

end GlobalTheory.RowBaseUniq

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumBasePointUniqueAllTuplesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuumBasePoint_unique_all_tuples : Big fun ch => ∀ t t' b b', IsBase t ch.S.B b → IsBase t' ch.S.B b' → b = b' := by
  first | exact @GlobalTheory.RowBaseUniq.isBase_unique | exact GlobalTheory.RowBaseUniq.isBase_unique | (intros; apply GlobalTheory.RowBaseUniq.isBase_unique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftTOppTens
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DownEqLiftP
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR Formalism.IndefR.Links Formalism.L2.DIV GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowChain

theorem bplus_eq_per {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (Wl : G.Weil) (t : T)
    (M : GlobalTheory.FunObj.Vol G) (hM : M.Is t) (φ : Fn G (.top 0)) (F : Fn G (.grid D.R.m 0)) :
    Bplus Wl M φ F = (topLev G hM).per Wl.ψ φ F :=
  GlobalTheory.T.besselPeriodCorankOneLess_eq_topBesselLevel_period G Wl t M hM φ F

end GlobalTheory.RowChain

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BplusEqCoef
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowVal

theorem bplus_eq_coef {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G)
    (φ : Fn G (.top 0)) (F : Fn G (.grid D.R.m 0)) :
    Bplus W M φ F = ∫ h in M.fd (.top 0), φ h *
      GlobalTheory.Mem.TrueRecord.coef W.ψ G.besTop M.νN M.fdN F (embTop G h) ∂M.ν (.top 0) := by
  simp only [Bplus, besInt, GlobalTheory.Mem.TrueRecord.coef, ← integral_const_mul, mul_assoc]

theorem nu_top_eq {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {M M' : Vol G}
    (hM : M.IsRow) (hM' : M'.IsRow) : M.ν (.top 0) = M'.ν (.top 0) := by
  obtain ⟨i1, i2, i3, i4, i5, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V (.top 0))
  have h1 := hM.top
  have h2 := hM'.top
  unfold Vol.IsAt at h1 h2
  have hz : Node.neg D.R.m (Node.top 0) = 0 := rfl
  rw [if_pos hz] at h1 h2
  haveI := h1.1.1
  haveI := h2.1.1
  have e := Measure.isMulLeftInvariant_eq_smul (M.ν (.top 0)) (M'.ν (.top 0))
  have a1 := GlobalTheory.Mass.Levels.measure_comap_finE h1.1
  have a2 := GlobalTheory.Mass.Levels.measure_comap_finE h2.1
  have hc : Measure.haarScalarFactor (M.ν (.top 0)) (M'.ν (.top 0)) = 1 := by
    rw [e, Measure.smul_apply, a2] at a1
    simpa using a1
  rw [e, hc, one_smul]

theorem bplus_indep : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (W : G.Weil) (M M' : Vol G),
    M.IsRow → M'.IsRow → ∀ φ F, GlobalTheory.Unf.IsContAut _ φ → GlobalTheory.Unf.IsContAut _ F → Bplus W M φ F = Bplus W M' φ F := by
  intro D T L sc G W M M' hM hM' φ F hφ hF
  have hψ := W.ψ_std
  have hι := (G.rowDec 0 (by have := D.R.two_le_m; omega)).isom
  have hF' : ∀ γ ∈ GQ (G.V (.grid D.R.m 0)), ∀ g, F (γ * g) = F g := hF.1
  have hN := hM.unip
  have hN' := hM'.unip
  rw [bplus_eq_coef, bplus_eq_coef]
  have ec : ∀ g, GlobalTheory.Mem.TrueRecord.coef W.ψ G.besTop M.νN M.fdN F g =
      GlobalTheory.Mem.TrueRecord.coef W.ψ G.besTop M'.νN M'.fdN F g := fun g =>
    GlobalTheory.Mem.TrueRecord.coef_eq hψ hι G.besTop hN.1 hN.2.1 hN.2.2 hN'.1 hN'.2.1 hN'.2.2 hF' g
  simp only [ec]
  obtain ⟨i1, i2, i3, i4, i5, -, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V (.top 0))
  have hf1 := (hM.top.haar_fund).2
  have hf2 := hM'.top.haar_fund
  rw [nu_top_eq hM hM'] at hf1 ⊢
  haveI := hf2.1
  set d := G.rowDec 0 (by have := D.R.two_le_m; omega)
  have e0 : ∀ h, embTop G h = stabilizerEmbedding d h := fun h => rfl
  have e1 : stabilizerEmbedding d 1 = 1 := by
    have := GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_mul d 1 1
    rw [one_mul] at this
    exact left_eq_mul.mp this
  refine hf1.setIntegral_eq hf2.2 fun γ h => ?_
  have hγ : (γ : GA D (G.V (.top 0))) ∈ GQ (G.V (.top 0)) := γ.2
  have hinv : stabilizerEmbedding d (γ : GA D (G.V (.top 0)))⁻¹ = (stabilizerEmbedding d γ)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_mul, inv_mul_cancel, e1]
  have r1 : EmbRel _ _ d.ι (stabilizerEmbedding d γ) γ := (embRel_iff d _ _).2 rfl
  have r2 : EmbRel _ _ d.ι (stabilizerEmbedding d γ)⁻¹ (γ : GA D (G.V (.top 0)))⁻¹ := hinv ▸ (embRel_iff d _ _).2 rfl
  change φ ((γ : GA D (G.V (.top 0))) * h) *
      GlobalTheory.Mem.TrueRecord.coef W.ψ G.besTop M'.νN M'.fdN F (embTop G ((γ : GA D (G.V (.top 0))) * h)) = _
  rw [hφ.1 _ hγ, e0, e0, GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_mul,
    GlobalTheory.Mem.TrueRecord.coef_left hψ hι G.besTop hN'.1 hN'.2.1 hN'.2.2 hF' (GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_rational d _ hγ) r1 r2]

end GlobalTheory.RowVal
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowVal

section Lin

variable {T : Type} {D : D7} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {M : Vol G}
  {ρ : RealMatch W} {t : T}

theorem rowFam_cusp (hS : GlobalTheory.FlipRun.CuspStep W M ρ t) {e : AE D} (he : IsIdemSum e (locPl G t))
    {F : Fn G (.grid 0 D.R.m)} (hF : GlobalTheory.FlipRun.IsCuspListed W.θ (.grid 0 D.R.m) F) :
    ∀ n, n ≤ D.R.m → ∀ (f : ∀ i : Fin n, Sch G (.right i D.R.m)),
      (∀ i : Fin n, ∃ φ g Q, IsLocVec W (.chi i D.R.m) e (ρ.vX i D.R.m) φ g ∧ f i = W.fock (.chi i D.R.m) g Q) →
      GlobalTheory.FlipRun.IsCuspListed W.θ (.grid n D.R.m) (liftP W M (rowPath T D.R.m n) (rowFam D.R.m n f) F) := by
  intro n
  induction n with
  | zero =>
    intro _ _ _
    exact hF
  | succ n ih =>
    intro hn f hf
    obtain ⟨φ, g, Q, hl, e1⟩ := hf (Fin.last n)
    have hprev := ih (by omega) (fun i => f i.castSucc) (fun i => hf i.castSucc)
    have h1 := (hS (.right n D.R.m) (Or.inl ⟨n, D.R.m, by omega, le_rfl, rfl⟩) e he φ g hl Q _ hprev).2
    show GlobalTheory.FlipRun.IsCuspListed W.θ (.grid (n + 1) D.R.m)
      (liftA W M (.right n D.R.m) (f (Fin.last n)) (liftP W M (rowPath T D.R.m n) (rowFam D.R.m n fun i => f i.castSucc) F))
    rw [e1]
    exact h1

theorem downFam_cusp (hS : GlobalTheory.FlipRun.CuspStep W M ρ t) {e : AE D} (he : IsIdemSum e (locPl G t)) :
    ∀ n, n ≤ D.R.m → ∀ (f : ∀ j : Fin n, Sch G (.down t D.R.m j)),
      (∀ j : Fin n, ∃ φ g Q, IsLocVec W (.mu t D.R.m j) e (ρ.vT D.R.m j) φ g ∧ f j = W.fock (.mu t D.R.m j) g Q) →
      ∀ F : Fn G (.grid D.R.m n), GlobalTheory.FlipRun.IsCuspListed W.θ (.grid D.R.m n) F →
      GlobalTheory.FlipRun.IsCuspListed W.θ (.grid D.R.m 0) (liftP W M (downPath t D.R.m n) (downFam t D.R.m n f) F) := by
  intro n
  induction n with
  | zero =>
    intro _ _ _ _ hF
    exact hF
  | succ n ih =>
    intro hn f hf F hF
    obtain ⟨φ, g, Q, hl, e1⟩ := hf (Fin.last n)
    have h1 := (hS (.down t D.R.m n) (Or.inr ⟨D.R.m, n, le_rfl, by omega, rfl⟩) e he φ g hl Q F hF).2
    have h1' : GlobalTheory.FlipRun.IsCuspListed W.θ (.grid D.R.m n) (liftA W M (.down t D.R.m n) (f (Fin.last n)) F) := by
      rw [e1]; exact h1
    have key : liftP W M (downPath t D.R.m (n + 1)) (downFam t D.R.m (n + 1) f) F =
        liftP W M (downPath t D.R.m n) (downFam t D.R.m n fun j => f j.castSucc)
          (liftA W M (.down t D.R.m n) (f (Fin.last n)) F) :=
      pathLift_comp W M (Path.one (.down t D.R.m n)) ((), f (Fin.last n)) F (downPath t D.R.m n)
        (downFam t D.R.m n fun j => f j.castSucc)
    rw [key]
    exact ih (by omega) (fun j => f j.castSucc) (fun j => hf j.castSucc) _ h1'

theorem opp_contAut (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam W.θ) (hS : GlobalTheory.FlipRun.CuspStep W M ρ t) {e : AE D}
    (he : IsIdemSum e (locPl G t)) {F : Fn G (.grid 0 D.R.m)} (hF : GlobalTheory.FlipRun.IsCuspListed W.θ (.grid 0 D.R.m) F)
    (P : PolRow G × PolDown G) (d φ : SchRow G × SchDown G t)
    (hd : (∀ i : Fin D.R.m, IsLocVec W (.chi i D.R.m) e (ρ.vX i D.R.m) (φ.1 i) (d.1 i)) ∧
      ∀ j : Fin D.R.m, IsLocVec W (.mu t D.R.m j) e (ρ.vT D.R.m j) (φ.2 j) (d.2 j)) :
    GlobalTheory.Unf.IsContAut (G.V (.grid D.R.m 0)) (liftP W M (oppPath t D.R.m) (oppPure W t P d) F) := by
  have hr := rowFam_cusp (M := M) hS he hF D.R.m le_rfl _ fun i => ⟨φ.1 i, d.1 i, P.1 i, hd.1 i, rfl⟩
  have hdn := downFam_cusp hS he D.R.m le_rfl _ (fun j => ⟨φ.2 j, d.2 j, P.2 j, hd.2 j, rfl⟩) _ hr
  have key : liftP W M (oppPath t D.R.m) (oppPure W t P d) F =
      liftP W M (downPath t D.R.m D.R.m) (downFam t D.R.m D.R.m fun j => W.fock (.mu t D.R.m j) (d.2 j) (P.2 j))
        (liftP W M (rowPath T D.R.m D.R.m) (rowFam D.R.m D.R.m fun i => W.fock (.chi i D.R.m) (d.1 i) (P.1 i)) F) :=
    pathLift_comp W M _ _ F _ _
  rw [key]
  have hrd := rapidDec_of_cuspForm hP hθ hdn.1 hdn.2.1
  exact ⟨hrd.1, hrd.2.1⟩

theorem bplus_fsum {M₀ : Vol G} (h₀ : M₀.IsRow) (hM : M.Is t) {φ : Fn G (.top 0)} (hφ : GlobalTheory.Unf.IsContAut _ φ) {I : Type}
    (s : Finset I) (a : I → ℂ) (f : I → Fn G (.grid D.R.m 0)) (hf : ∀ i ∈ s, GlobalTheory.Unf.IsContAut _ (f i)) :
    Bplus W M₀ φ (∑ i ∈ s, a i • f i) = ∑ i ∈ s, a i * Bplus W M₀ φ (f i) := by
  suffices hs : Bplus W M φ (∑ i ∈ s, a i • f i) = ∑ i ∈ s, a i * Bplus W M φ (f i) by
    rw [bplus_indep G W M₀ M h₀ hM.isRow φ _ hφ (GlobalTheory.SeeSaw.TrcProof.contAut_sum s a f hf), hs]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [bplus_indep G W M₀ M h₀ hM.isRow φ _ hφ (hf i hi)]
  have hconv (F : Fn G (.grid D.R.m 0)) (hF : GlobalTheory.Unf.IsContAut _ F) : BplusConv W M φ F := by
    let d := G.rowDec 0 (by have := D.R.two_le_m; omega)
    have hV := G.isV (X := .top 0) (Nat.zero_le _) (fun j e => by cases e)
    have hA : IsAniso (G.V (.top 0)) := GlobalTheory.Per.isAniso_of_posDef hV.sigOK fun τ => by
      rw [hV.sig τ, hV.rank]
      simp [Node.neg]
    obtain ⟨emb, hc, hrel, hrat⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D _ _ _ d.isom
    have hemb : embTop G = emb := funext fun h => (hrel h _).1 ((embRel_iff d h _).2 rfl)
    have hQ : GlobalTheory.Per.Inhab.IsRatInv d.ι G.besTop.e
        (fun h n => φ h * F (n * embTop G h) * star (besChar W.ψ G.besTop n)) := by
      refine ⟨fun δ γ h n hn => (GlobalTheory.BesselChar.besChar_conj W.ψ G.besTop δ γ h n hn).1, ?_, ?_⟩
      · intro g n hn γ hγ hq
        rw [GlobalTheory.BesselChar.besChar_mul W.ψ G.besTop γ n hγ hn,
          GlobalTheory.BesselChar.besChar_rat W.ψ W.ψ_std.1 G.besTop γ hγ hq, one_mul,
          mul_assoc γ, hF.1 γ hq]
      · intro g n hn γ hγ δ hδ
        have e : (δ * n * δ⁻¹) * embTop G (γ * g) = emb γ * (n * embTop G g) := by
          rw [hemb, (hrel _ _).1 hδ]
          simp only [map_mul, mul_assoc, inv_mul_cancel_left]
        rw [(GlobalTheory.BesselChar.besChar_conj W.ψ G.besTop δ γ hδ n hn).2, e,
          hF.1 _ (hrat γ hγ), hφ.1 γ hγ]
    obtain ⟨hμ, hfd⟩ := hM.isRow.top.haar_fund
    obtain ⟨-, -, -, -, _, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V (.grid D.R.m 0))
    have hemb_cont : Continuous (embTop G) := hemb.symm ▸ hc
    exact GlobalTheory.RowBplus.integrable_of_haar hQ G.besTop.e_iso d.isom hA
      (((hφ.2.comp continuous_fst).mul
        (hF.2.comp ((continuous_subtype_val.comp continuous_snd).mul (hemb_cont.comp continuous_fst)))).mul
        ((GlobalTheory.BesselChar.besChar_continuous W.ψ W.ψ_std.1 G.besTop).comp continuous_snd).star)
      hμ hfd hM.isRow.unip
  have hterms := fun i (hi : i ∈ s) => hconv (f i) (hf i hi)
  have hsum (h : GA D (G.V (.top 0))) (n : NFlag (G.V (.grid D.R.m 0)) G.besTop.e) :
      besInt W φ (∑ i ∈ s, a i • f i) h n = ∑ i ∈ s, a i * besInt W φ (f i) h n := by
    simp only [besInt, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [Bplus]
  simp_rw [hsum]
  have hinner (h : GA D (G.V (.top 0))) :
      (∫ n in M.fdN, ∑ i ∈ s, a i * besInt W φ (f i) h n ∂M.νN) =
        ∑ i ∈ s, a i * ∫ n in M.fdN, besInt W φ (f i) h n ∂M.νN := by
    rw [integral_finsetSum s fun i hi => ((hterms i hi).1 h).const_mul (a i)]
    exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
  simp_rw [hinner]
  rw [integral_finsetSum s fun i hi => (hterms i hi).2.const_mul (a i)]
  exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _

theorem liftT_oppTens (τi : PolRow G × PolDown G →₀ ℂ) (τ : SchRow G × SchDown G t →₀ ℂ) (F : Fn G (.grid 0 D.R.m)) :
    liftT W M (oppPath t D.R.m) (oppTens W t τi τ) F =
      ∑ P ∈ τi.support, τi P • ∑ d ∈ τ.support, τ d • liftP W M (oppPath t D.R.m) (oppPure W t P d) F := by
  have e : liftT W M (oppPath t D.R.m) (oppTens W t τi τ) F =
      AddMonoidHom.mk' (fun x => liftT W M (oppPath t D.R.m) x F) (fun x y => liftT_add W M _ x y F) (oppTens W t τi τ) := rfl
  rw [e]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [oppTens, Finsupp.sum, map_sum, AddMonoidHom.mk'_apply, liftT_single, Finset.smul_sum, smul_smul]

end Lin

end GlobalTheory.RowVal
end
end
