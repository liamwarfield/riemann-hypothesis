module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleLevelFixesVector
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarizationSectionBasisPullbackAffine
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RouteDatumMemAlgebraicVectorsGridFrames
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVectorBlockLevelUnimodularEigen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateModulusStandardThetaPresentation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsParallelWeightInvertibleSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateTopBoundOfInputs

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleThetaEval
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.BotBigLevel

open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter GlobalTheory.RowVacScalar _root_.Formalism.L2.DIV GlobalTheory.BotFinLevel
open Formalism.IndefR.Fin.LevelGroupLemmas.Lat (frG intM)

variable {D : D7}

theorem topL_mul_sq {κ : Type} [CommRing κ] {a b : ℕ} (y : Matrix (Fin b) (Fin a) κ) (γ : Matrix (Fin a) (Fin a) κ) :
    topL a (y * γ) = topL a y * γ := by
  ext i j
  by_cases hi : i.val < b
  · simp [topL, Matrix.mul_apply, hi]
  · simp [topL, Matrix.mul_apply, hi]

theorem unitChar_congr (ν : (Formalism.L2.Theta.AE D)ˣ →* Circle) (e : Formalism.L2.Theta.AE D) {k : ℕ}
    {M N : Matrix (Fin k) (Fin k) (Lev.EAf D)} (h : M.det = N.det) : unitChar ν e M = unitChar ν e N := by
  have h1 : IsUnitDet e M = IsUnitDet e N := by
    funext x
    unfold IsUnitDet
    rw [h]
  unfold unitChar
  rw [h1]

theorem inId_mul_right {I : Ideal (𝓞 D.host.E)} {k d : ℕ} {K : Matrix (Fin k) (Fin k) (Lev.EAf D)} (hK : IsIntM K)
    {Y : Matrix (Fin d) (Fin k) (Lev.EAf D)} {i : Fin d} (h : ∀ j, InId I (Y i j)) (j : Fin k) :
    InId I ((HMul.hMul Y K) i j) := by
  have := inId_mul (K := K.transpose) (Y := Y.transpose) (j := i) (fun a b => hK b a) h j
  rwa [← Matrix.transpose_mul] at this

theorem detIdl_inv {e : Formalism.L2.Theta.AE D} (hee : e * e = e) (S : HSp D) (g : Formalism.L2.Theta.GA D S) :
    detIdl e S g⁻¹ = (detIdl e S g)⁻¹ := by
  refine (inv_eq_of_mul_eq_one_right (Units.ext ?_)).symm
  have h1 : (Formalism.L2.Theta.mt S g).det * (Formalism.L2.Theta.mt S g⁻¹).det = 1 := by
    rw [← Matrix.det_mul, Formalism.IndefR.Fin.LevelGroupLemmas.Lat.mt_mul_inv, Matrix.det_one]
  rw [Units.val_mul, detIdl_val hee, detIdl_val hee, Units.val_one]
  linear_combination e * h1 + ((Formalism.L2.Theta.mt S g).det * (Formalism.L2.Theta.mt S g⁻¹).det - (Formalism.L2.Theta.mt S g).det -
    (Formalism.L2.Theta.mt S g⁻¹).det + 1) * hee

theorem stdFst_actO (ν : (Formalism.L2.Theta.AE D)ˣ →* Circle) {e : Formalism.L2.Theta.AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P)
    (I : Ideal (𝓞 D.host.E)) (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D))
    {g : Formalism.L2.Theta.GA D S} (hg : Lev.finE S g ∈ St βS) (y : WO S T) :
    stdFst ν e I S T βS βT (actO S T g 1 y) = ((ν (detIdl e S g) : Circle) : ℂ) * stdFst ν e I S T βS βT y := by
  have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hg' : Lev.finE S g⁻¹ ∈ St βS := by rw [map_inv]; exact inv_mem hg
  have hK : (frG S βS g).1 * (frG S βS g⁻¹).1 = 1 := by
    rw [Formalism.IndefR.Fin.LevelGroupLemmas.Lat.frG_inv, Units.mul_inv]
  have hK' : (frG S βS g⁻¹).1 * (frG S βS g).1 = 1 := by
    rw [Formalism.IndefR.Fin.LevelGroupLemmas.Lat.frG_inv, Units.inv_mul]
  have h1 : frG T βT 1 = 1 := by
    unfold frG
    rw [map_one, mul_one, inv_mul_cancel]
  have hact : frMapO S T βS βT (actO S T g 1 y) = HMul.hMul (frMapO S T βS βT y) (frG S βS g⁻¹).1 := by
    rw [Formalism.IndefR.Fin.LevelGroupLemmas.Lat.frMapO_actO, h1, Units.val_one, Matrix.one_mul, Formalism.IndefR.Fin.LevelGroupLemmas.Lat.frG_inv]
  have hback : frMapO S T βS βT y =
      HMul.hMul (HMul.hMul (frMapO S T βS βT y) (frG S βS g⁻¹).1) (frG S βS g).1 := by
    rw [Matrix.mul_assoc, hK', Matrix.mul_one]
  unfold stdFst
  rw [hact]
  by_cases hc : IsHalf e y ∧ IsIntM (frMapO S T βS βT y) ∧ ∀ i j, S.rank ≤ i.1 → InId I (frMapO S T βS βT y i j)
  · rw [if_pos hc, if_pos ⟨(GlobalTheory.SchrMove.isHalf_actO_iff g 1 y).2 hc.1,
      Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isIntM_mul hc.2.1 (isIntM_frG hg'),
      fun i j hi => inId_mul_right (isIntM_frG hg') (fun l => hc.2.2 i l hi) j⟩, topL_mul_sq,
      unitChar_congr ν e (Matrix.det_mul_comm _ _),
      unitChar_mul ν hee hK (isUnitDet_frG he hg') (isUnitDet_frG he hg), detIdl_inv hee, map_inv, inv_inv]
  · rw [if_neg hc, if_neg, mul_zero]
    rintro ⟨h1, h2, h3⟩
    refine hc ⟨(GlobalTheory.SchrMove.isHalf_actO_iff g 1 y).1 h1, ?_, fun i j hi => ?_⟩
    · rw [hback]; exact Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isIntM_mul h2 (isIntM_frG hg)
    · rw [hback]; exact inId_mul_right (isIntM_frG hg) (fun l => h3 i l hi) j

theorem fix_fst_of_unram {T : Type} {A A' WW : HSp D} {X : Tri T A A' WW} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    {α β : T → ((Formalism.L2.Theta.AE D)ˣ →* Circle)} {νH : T → Formalism.L2.Host.HChar D.host.E} {S : T → Finset (Pl D.host.E)}
    (hX : X.Is ψ θ α β νH S) (s : T)
    (hu : ∀ v : HeightOneSpectrum (𝓞 D.host.F), (∀ w ∈ S s, w.under (𝓞 D.host.F) ≠ v) →
      CharUnramAt D (α s) v ∧ CharUnramAt D (β s) v)
    {k : Formalism.L2.Theta.GA D A} (hk1 : k ∈ GfC A) (hk2 : Lev.finE A k ∈ St X.rA.β) : X.ω s (k, 1) (X.f s) = X.f s := by
  have hW : IsWeilDatumO ψ (GlobalTheory.Grid.neg A) WW (β s) (β s / α s) ((X.ω s).toSgn true) := hX.weil s
  have hA : IsSelfDualC (GlobalTheory.Grid.neg A) X.rA.Λ := GlobalTheory.RowTest.isSelfDualC_neg' hX.rigA.1
  set k' : Formalism.L2.Theta.GA D (GlobalTheory.Grid.neg A) := (GlobalTheory.Grid.ofSgn true A).symm k with hk'
  have hk1' : k' ∈ GfC (GlobalTheory.Grid.neg A) := hk1
  have hk2' : Lev.finE (GlobalTheory.Grid.neg A) k' ∈ St X.rA.β := hk2
  have he := hX.idem s
  have hee : X.e s * X.e s = X.e s := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hP : ∀ w ∈ S s, Formalism.L2.NTheta.IsIdemAt (idemAt w) w := fun w hw => by
    obtain ⟨⟨es, hes, -⟩, -⟩ := he
    exact Classical.epsilon_spec (p := fun e : Formalism.L2.Theta.AE D => Formalism.L2.NTheta.IsIdemAt e w) ⟨es w, hes w hw⟩
  have h1 : Lev.finE WW 1 ∈ St X.rW.β := by rw [map_one]; exact one_mem _
  have hv := GlobalTheory.LatStabScalar.om_eq_prod_splitFac hW hA hX.rigW.1 (S s) hP (GlobalTheory.LevelPlaces.under_injOn he)
    (fun v hv => ⟨(hu v hv).2, by
      rw [div_eq_mul_inv]
      exact GlobalTheory.SeeSaw.WeilLines.charUnram_mul (hu v hv).2 (GlobalTheory.SeeSaw.WeilLines.charUnram_inv (hu v hv).1)⟩)
    k' hk1' 1 (one_mem _) (keeps_latHat (S := GlobalTheory.Grid.neg A) hX.rigA.2.1 hk2') (keeps_latHat hX.rigW.2.1 h1) X.vac
    hX.isVac.2.theta hX.isVac.2.lat
  have hc : (∏ w ∈ S s, ((splitFacO (β s) (β s / α s) (detIdl (idemAt w) (GlobalTheory.Grid.neg A) k')
      (detIdl (idemAt w) WW 1) : Circle) : ℂ)) = (((α s / β s) (detIdl (X.e s) (GlobalTheory.Grid.neg A) k') : Circle) : ℂ) := by
    rw [← prod_detIdl he hP, map_prod]
    rw [show ∀ f : Pl D.host.E → Circle, ((∏ w ∈ S s, f w : Circle) : ℂ) = ∏ w ∈ S s, (f w : ℂ) from
      fun f => map_prod Circle.coeHom f (S s)]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [splitFacO, detIdl_one, map_one, mul_one, MonoidHom.div_apply, MonoidHom.div_apply, inv_div]
  rw [hc] at hv
  have key := GlobalTheory.SchrMove.smul_om_eq D ψ (GlobalTheory.Grid.neg A) WW X.rA.Λ X.rW.Λ _ _ _ hW hA hX.rigW.1 (X.e s)
    hee (GlobalTheory.PlaceDatum.infPart_idemSum he) k' 1
    (GlobalTheory.StabLatInv.mem_latO_iff_actO_mem D (GlobalTheory.Grid.neg A) WW _ _ _ _ hA hX.rigW.1 hX.rigA.2.1 hX.rigW.2.1 k' 1 hk2' h1)
    X.vac _ (X.f s) _ _ hX.isVac.2.theta (hX.fst s) (Circle.coe_ne_zero _) hv
    (stdFst_actO (α s / β s) he (X.ideal S s) (GlobalTheory.Grid.neg A) WW X.rA.β X.rW.β hk2')
  exact smul_right_injective _ (Circle.coe_ne_zero _) key

theorem mem_St_of_isFinPt {A : HSp D} {r : Rig A} (hr : r.Is) (hs : r.IsStd) {n : ℕ} {x : Formalism.MainNotions.StandardLatticesGL3.GA D n}
    {k : Formalism.L2.Theta.GA D A} (hx : x ∈ GlobalTheory.NormSum.intG D n) (hk : GlobalTheory.BotFormula.IsFinPt A k x) : Lev.finE A k ∈ St r.β := by
  obtain rfl : A.rank = n := hk.2.choose
  have hΛ : r.Λ = Formalism.L2.Col.stdLat D.host.E A.rank := by
    ext y
    rw [hs.2.1 y]
    exact ⟨fun h i _ => Submodule.mem_one.2 (h i), fun h i => Submodule.mem_one.1 (h i trivial)⟩
  have hβ : Formalism.L2.DIV.IsFrame r.β (Formalism.L2.Col.stdLat D.host.E A.rank) := hΛ ▸ hr.2.1
  refine (GlobalTheory.BotClassDict.mem_level_iff A hs.1 hβ k).2 ?_
  rw [GlobalTheory.BotClassDict.finStd_of_isFinPt A hs.1 hk]
  exact hx

theorem ker_mul_of_fix {T : Type} {A A' WW : HSp D} {X : Tri T A A' WW} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    {α β : T → ((Formalism.L2.Theta.AE D)ˣ →* Circle)} {νH : T → Formalism.L2.Host.HChar D.host.E} {S : T → Finset (Pl D.host.E)}
    (hX : X.Is ψ θ α β νH S) (t : T) {k : Formalism.L2.Theta.GA D A} (hk : k ∈ GfC A) (hf : X.ω t (k, 1) (X.f t) = X.f t)
    (P : PolF D WW.rank A.rank) (g : Formalism.L2.Theta.GA D WW) (y : Formalism.L2.Theta.GA D A) :
    X.ker ψ θ t P g (y * k) = X.ker ψ θ t P g y := by
  set pt : (WO (GlobalTheory.Grid.neg A) WW → ℂ) → (WO (GlobalTheory.Grid.neg A) WW → ℂ) := fun f =>
    pureTensorO ψ θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B f P with hpt
  have e1 : ∀ f, ((X.ω t).toSgn true) ((GlobalTheory.Grid.ofSgn true A).symm k, 1) f = X.ω t (k, 1) f := fun f => rfl
  have move : X.ω t (k, 1) (pt (X.f t)) = pt (X.ω t (k, 1) (X.f t)) := by
    rw [← e1, ← e1]
    exact GlobalTheory.OrientedHeis.om_fin_pureTensorO _ _ _ _ _ _ (hX.weil t) θ hX.isVac.2.inf ((GlobalTheory.Grid.ofSgn true A).symm k) hk 1
      (one_mem _) (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P (GlobalTheory.ConstRatio.theta_f hX t).1
  have e2 : ∀ z, X.ker ψ θ t P g z = X.ω t (z, g) (pt (X.f t)) 0 := fun z => rfl
  have e3 : ((y * k, g) : Formalism.L2.Theta.GA D A × Formalism.L2.Theta.GA D WW) = (y, g) * (k, 1) := by
    rw [Prod.mk_mul_mk, mul_one]
  rw [e2, e2, e3, map_mul, Module.End.mul_apply, move, hf]

end GlobalTheory.BotBigLevel

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilTopGridStageExists
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PureTensorOPerm
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel IsLocalRing
open GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.StepData (XIx Ix latOf box LatFrame)
open GlobalTheory.LocMod (GAt PinGBy ofSplit MovedTo)
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (CharUnramAt)
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastPair lastKer)
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedLocalFrameSequences (IsFockOver StepsAll vec atW IsMoved InAt InvOnUnits IsBesFrame IsJacFrame FrameMapsPrefix jacLat ptBF ptFB)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FockOrder

variable {D : D7}

theorem exists_sortPerm {n : ℕ} (ε : Fin n → Bool) :
    ∃ π : Equiv.Perm (Fin n), ∀ a, ε (π a) = decide (a.val < (Finset.univ.filter fun a => ε a = true).card) := by
  classical
  set p := (Finset.univ.filter fun a => ε a = true).card with hp
  set q := (Finset.univ.filter fun a => ¬ ε a = true).card with hq
  have hpq : p + q = n := by
    rw [hp, hq, Finset.card_filter_add_card_filter_not]; simp
  have e1 : {a // ε a = true} ≃ Fin p := Fintype.equivFinOfCardEq (by rw [Fintype.card_subtype])
  have e2 : {a // ¬ ε a = true} ≃ Fin q := Fintype.equivFinOfCardEq (by rw [Fintype.card_subtype])
  refine ⟨(finCongr hpq.symm).trans (finSumFinEquiv.symm.trans ((Equiv.sumCongr e1.symm e2.symm).trans
    (Equiv.sumCompl _))), fun a => ?_⟩
  by_cases ha : a.val < p
  · have h : finCongr hpq.symm a = Fin.castAdd q ⟨a.val, ha⟩ := Fin.ext rfl
    simp only [Equiv.trans_apply, h, finSumFinEquiv_symm_apply_castAdd, Equiv.sumCongr_apply, Sum.map_inl,
      Equiv.sumCompl_apply_inl]
    rw [(e1.symm _).2]; simp [ha]
  · have h : finCongr hpq.symm a = Fin.natAdd p ⟨a.val - p, by omega⟩ := Fin.ext (by simp; omega)
    simp only [Equiv.trans_apply, h, finSumFinEquiv_symm_apply_natAdd, Equiv.sumCongr_apply, Sum.map_inr,
      Equiv.sumCompl_apply_inr]
    have h2 := (e2.symm ⟨a.val - p, by omega⟩).2
    simp only [Bool.not_eq_true] at h2
    rw [h2]; simp [ha]

variable {V : HSp D} {S : D.what₂.Tau → SPar}

section Main

variable {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {V W : HSp D} {S S' : D.what₂.Tau → SPar}

end Main

end GlobalTheory.FockOrder

end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.ConstRatio (Factor NegIdx)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.SqTower.TopGridExists


open Matrix in
theorem exists_isONBasis {k : ℕ} {G s B : Matrix (Fin k) (Fin k) ℂ} {ε : Fin k → Bool}
    (hG : Bᴴ * G * B = Formalism.REAL.Jm ε) (hs : s * B = B * Formalism.REAL.Jm ε) :
    ∃ (B' : Matrix (Fin k) (Fin k) ℂ) (p : ℕ), IsONBasis G s B' p := by
  obtain ⟨π, hπ⟩ := GlobalTheory.FockOrder.exists_sortPerm ε
  generalize (Finset.univ.filter fun a => ε a = true).card = p at hπ
  have hJ : (Matrix.diagonal fun a => (((if ε a then 1 else -1 : ℝ)) : ℂ)) = Formalism.REAL.Jm ε := by
    unfold Formalism.REAL.Jm
    congr 1
    funext a
    cases ε a <;> simp
  refine ⟨B.submatrix id π, p, fun a => if a.val < p then 1 else -1, fun a => ?_, ?_, ?_⟩
  · by_cases ha : a.val < p
    · left; simp [ha]
    · right; simp [ha, not_lt.1 ha]
  · have e : (B.submatrix id π)ᴴ * G * B.submatrix id π = (Bᴴ * G * B).submatrix π π := by
      ext a b; simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [e, hG, ← hJ, Matrix.submatrix_diagonal_equiv]
    congr 1; funext a; simp [hπ a]
  · have e : s * B.submatrix id π = (s * B).submatrix id π := by
      ext a b; simp [Matrix.mul_apply]
    rw [e, hs, ← Matrix.submatrix_mul_equiv (e₂ := π), ← hJ, Matrix.submatrix_diagonal_equiv]
    congr 2; funext a; simp [hπ a]


open Matrix GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle in
theorem exists_rig_of_frame {D : D7} {V : HSp D} (A : Fr V) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hΛ : IsSelfDualC V Λ) : ∃ r : Rig V, r.Λ = Λ ∧ r.s = A.cart ∧ r.Is := by
  haveI : Submodule.IsLattice D.host.E Λ := hΛ.1
  have hfull : Submodule.IsFullLattice D.host.E Λ := by
    refine ⟨?_⟩
    obtain ⟨s, hs⟩ := hΛ.1.fg
    apply eq_top_iff.mpr
    intro y _
    let f : (Fin V.rank → D.host.E) → D.host.E := fun x =>
      ∑ i, ∑ j, star (x i) * V.gram i j * y j
    obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 D.host.E)) s f
    have ha0 : (algebraMap (𝓞 D.host.E) D.host.E a) ≠ 0 := by
      exact (FaithfulSMul.algebraMap_injective _ _).ne (mem_nonZeroDivisors_iff_ne_zero.mp a.2)
    let P : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := {
      carrier := {x | ∃ b : 𝓞 D.host.E, (b : D.host.E) = (algebraMap (𝓞 D.host.E) D.host.E a) * f x}
      zero_mem' := by refine ⟨0, ?_⟩; simp [f]
      add_mem' := by
        rintro x z ⟨b, hb⟩ ⟨c, hc⟩
        refine ⟨b + c, ?_⟩
        change (b : D.host.E) + c = _
        rw [hb, hc]
        simp [f, map_add, add_mul, Finset.sum_add_distrib, mul_add]
      smul_mem' := by
        rintro c x ⟨b, hb⟩
        refine ⟨RingOfIntegers.mapRingHom (starRingEnd D.host.E) c * b, ?_⟩
        simp only [map_mul, hb, f, Pi.smul_apply, Algebra.smul_def, map_mul, RingOfIntegers.mapRingHom_apply, star_mul]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        change star (c : D.host.E) * _ = _
        ring }
    have hsP : (s : Set (Fin V.rank → D.host.E)) ⊆ P := by
      intro x hx
      obtain ⟨b, hb⟩ := ha x hx
      exact ⟨b, by simpa [Algebra.smul_def] using hb⟩
    have hy : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Λ := by
      apply (hΛ.2 _).2
      intro x hx
      have hxP : x ∈ P := (hs ▸ Submodule.span_le.mpr hsP) hx
      obtain ⟨b, hb⟩ := hxP
      refine ⟨b, ?_⟩
      rw [hb]
      dsimp only [f, Pi.smul_apply]
      simp only [smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hy' : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) :=
      Submodule.subset_span hy
    have := (Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E))).smul_mem
      (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ hy' 
    change (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ •
      ((algebraMap (𝓞 D.host.E) D.host.E a) • y) ∈ _ at this
    rw [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ ha0, one_smul] at this
    exact this
  obtain ⟨β, hβ⟩ := GlobalTheory.latticeFrame.exists_frame D.host.F D.host.E V.rank Λ hfull
  have hτ : ∀ τ : D.what₂.Tau, ∃ (B : Matrix (Fin V.rank) (Fin V.rank) ℂ) (p : ℕ),
      IsONBasis (gramAt D V τ) (A.cart τ) B p := fun τ => by
    have hu := (Matrix.isUnit_iff_isUnit_det _).1 (A.fr_unit τ)
    have h1 := Matrix.mul_nonsing_inv _ hu
    refine exists_isONBasis (B := (A.fr τ)⁻¹) (ε := A.ε τ) ?_ ?_
    · rw [← A.fr_gram τ]
      simp only [Matrix.mul_assoc, h1, Matrix.mul_one]
      rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one, Matrix.one_mul]
    · simp only [Fr.cart, Matrix.mul_assoc, h1, Matrix.mul_one]
  choose B hB using hτ
  exact ⟨⟨Λ, β, A.cart, B⟩, rfl, rfl, hΛ, hβ, fun τ => ⟨GlobalTheory.CompactFockAction.cart_isCartanInv A τ, hB τ⟩⟩


end GlobalTheory.SqTower.TopGridExists

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBottomPairSmallMemberTwistedTuple
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModTMulConjLe
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)
open GlobalTheory.SqTop (twPl Qn modT)

noncomputable section
namespace GlobalTheory.BotPairSmallTw

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem modT_ne_bot (G : GridData L sc) (t : T) : modT G t ≠ ⊥ := by
  unfold modT
  exact mul_ne_zero (condE_ne_bot G.pl) (Finset.prod_ne_zero_iff.2 fun w _ => w.ne_bot)

theorem absNorm_modT (G : GridData L sc) (t : T) : Ideal.absNorm (modT G t) = levQ G.pl * Qn G t := by
  rw [modT, map_mul, map_prod, GlobalTheory.ModulusNorm.absNorm_condE, Qn]

theorem hatId_mono {I J : Ideal (𝓞 D.host.E)} (h : I ≤ J) : hatId D I ≤ hatId D J :=
  AddSubgroup.closure_mono fun _ ⟨b, hb, s, hs, e⟩ => ⟨b, h hb, s, hs, e⟩

theorem modT_mul_conj_le (G : GridData L sc) (t : T) :
    modT G t * D.host.conj • modT G t ≤ condE G.pl * D.host.conj • condE G.pl := by
  have h : modT G t ≤ condE G.pl := by
    show condE G.pl * _ ≤ _
    exact Ideal.mul_le_inf.trans inf_le_left
  exact Ideal.mul_mono h (Ideal.map_mono h)

end GlobalTheory.BotPairSmallTw

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBottomPairSmallMemberTwistedTuple
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)
open GlobalTheory.SqTop (twPl Qn modT)

noncomputable section
namespace GlobalTheory.BotPairSmallTw

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem nuH_inv_eq_one {μ₀ : T} (hL : L.Is μ₀) (G : GridData L sc) (t : T) (i j : Fin D.R.m) (u : (AE D)ˣ)
    (hu : IntU D u) (h : (u : AE D) - 1 ∈ hatId D (modT G t * D.host.conj • modT G t)) :
    (nuH G t i j)⁻¹.1 (finIdl D u) = 1 := by
  have e : nuH G t i j = nuH G μ₀ i j * L.xiH t := by
    simp only [nuH, hL.xi_base, mul_one, div_eq_mul_inv]; exact mul_right_comm _ _ _
  have h0 := GlobalTheory.BotPairSmall.CondNu.nuH_inv_eq_one_of_cong hL G i j u hu (hatId_mono (modT_mul_conj_le G t) h)
  have h1 := GlobalTheory.BotPairSmall.CondXi.xiH_eq_one_of_cong hL G t u hu h
  rw [e, mul_inv]
  change ((nuH G μ₀ i j)⁻¹.1 * (L.xiH t)⁻¹.1) (finIdl D u) = 1
  rw [MonoidHom.mul_apply, h0, one_mul]
  change ((L.xiH t).1 (finIdl D u))⁻¹ = 1
  rw [h1, inv_one]

theorem conj_isCoprime_halfDifferent {I : Ideal (𝓞 D.host.E)}
    (h : IsCoprime I (Ideal.span {((D.host.QS * D.host.q : ℕ) : 𝓞 D.host.E)})) : IsCoprime (D.host.conj • I) D.host.𝔟 := by
  rw [Ideal.isCoprime_iff_sup_eq] at h ⊢
  by_contra hne
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  have hb : D.host.𝔟 ≤ M := le_sup_right.trans hle
  have h0 : M ≠ ⊥ := fun e => ReciprocityTheory.ChartRestriction.G.PullbackSections.MLI.bb_ne_bot D (eq_bot_iff.2 (e ▸ hb))
  let P : HeightOneSpectrum (𝓞 D.host.E) := ⟨M, hM.isPrime, h0⟩
  have h2 : ((D.host.QS * D.host.q : ℕ) : 𝓞 D.host.E) ∈ M := GlobalTheory.HalfCompare.two_q_mem (P := P) (Ideal.dvd_iff_le.2 hb)
  obtain ⟨a, ha, b, hb', e⟩ := Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 h)
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hb'
  have e1 := congrArg (MulSemiringAction.toRingHom _ (𝓞 D.host.E) D.host.conj) e
  rw [map_add (f := _), map_mul, map_natCast, map_one] at e1
  refine hM.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
  rw [← e1]
  exact M.add_mem (hle (Ideal.mem_sup_left (Ideal.smul_mem_pointwise_smul D.host.conj _ _ ha))) (M.mul_mem_left _ h2)

theorem modT_isCoprime_two_q {μ₀ : T} (hL : L.Is μ₀) (hpq : Nat.Coprime D.host.pde (D.host.QS * D.host.q)) (hpq' : Nat.Coprime D.host.pde' (D.host.QS * D.host.q))
    (G : GridData L sc) (t : T) : IsCoprime (modT G t) (Ideal.span {((D.host.QS * D.host.q : ℕ) : 𝓞 D.host.E)}) := by
  classical
  unfold modT
  refine IsCoprime.mul_left ?_ (IsCoprime.prod_left fun w hw => ?_)
  · obtain ⟨N, hN, hm⟩ := GlobalTheory.FunObj.StdDatum.HalfDiff.exists_nat_mem_condE G.pl ⟨hpq, hpq'⟩
    obtain ⟨x, y, e⟩ : IsCoprime ((N : ℕ) : 𝓞 D.host.E) ((D.host.QS * D.host.q : ℕ) : 𝓞 D.host.E) := Nat.Coprime.cast hN
    rw [Ideal.isCoprime_iff_sup_eq, Ideal.eq_top_iff_one, ← e]
    exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mul_mem_left _ _ hm))
      (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))
  · simp only [twPl, GlobalTheory.FunObj.locPl, Finset.mem_filter, Finset.mem_union] at hw
    have hP : w ∈ L.Q t := hw.1.resolve_left hw.2
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra hne
    have heq := w.isMaximal.eq_of_le hne le_sup_left
    have h2q : ((D.host.QS * D.host.q : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal :=
      heq.symm.le (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    refine (hL.Q_off t w hP).1 ?_
    rw [show D.host.QS * D.host.q * D.host.d * D.sp.T = (D.host.QS * D.host.q) * (D.host.d * D.sp.T) by ring, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ h2q

theorem conj_modT_isCoprime_halfDifferent {μ₀ : T} (hL : L.Is μ₀) (hpq : Nat.Coprime D.host.pde (D.host.QS * D.host.q)) (hpq' : Nat.Coprime D.host.pde' (D.host.QS * D.host.q))
    (G : GridData L sc) (t : T) : IsCoprime (D.host.conj • modT G t) D.host.𝔟 :=
  conj_isCoprime_halfDifferent (modT_isCoprime_two_q hL hpq hpq' G t)

theorem smallPair_exists_tw : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, GlobalTheory.NormSum.Inp D → L.Is μ₀ → Nat.Coprime D.host.pde (D.host.QS * D.host.q) → Nat.Coprime D.host.pde' (D.host.QS * D.host.q) → ∀ (G : GridData L sc) (t : T) {δ t0 : ℂ}, Crv D ⊤ δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0 → ∀ (i j : Fin D.R.m) (χα : HeckeU D (botSmall D i j)), (∀ x, χα.f x = (alphaH L t i j).1 (finIdl D x)) → ∀ (χν : HeckeU D (botBig D i j + botSmall D i j)), (∀ x, χν.f x = (nuH G t i j)⁻¹.1 (finIdl D x)) → (∀ τ, ((botBig D i j + botSmall D i j : ℕ) : ℤ) ≤ χν.n τ) → ∃ P' : GlobalTheory.NormSum.Pair D ⊤ δ t0 (levQ G.pl * Qn G t), P'.a = botSmall D i j ∧ P'.d = botBig D i j + botSmall D i j ∧ HasChars P' (alphaH L t i j) (nuH G t i j)⁻¹ ∧ IsStdDatum P' (D.host.conj • modT G t) (botBig D i j) ∧ IsBlockLevel P' (modT G t) (botBig D i j) := by
  intro D T L sc μ₀ _ hL hpq hpq' G t δ t0 hc ht i j χα hα χν hν hn
  obtain ⟨h1, h2, h3⟩ := ranks_exact D i j
  have hd : Even (botBig D i j + botSmall D i j) :=
    ⟨halfRank D i j - (D.R.m - (j + 1)) / 2 - (D.R.m - j) / 2, by omega⟩
  obtain ⟨e0, hv, h0⟩ := GlobalTheory.Vacuum.exists_vacuum D ⊤ δ hc t0 ht (botSmall D i j) (botBig D i j + botSmall D i j)
    (hd.mul_left _)
  obtain ⟨W, hW1, hW2, hW3, hW4⟩ := GlobalTheory.FinWeil.exists_weil_of_vacuum D ⊤ δ hc _ _ e0 hv.1 h0 χα χν
  have hm := modT_ne_bot G t
  have hcop := GlobalTheory.SqTop.modT_sup_conj hL G t
  have hcond : ∀ u : (AE D)ˣ, IntU D u → (u : AE D) - 1 ∈ hatId D (modT G t * D.host.conj • modT G t) →
      W.chV'.f u = 1 := by
    intro u hu h
    rw [hW2, hν, nuH_inv_eq_one hL G t i j u hu h]
  obtain ⟨R, hR1, hR2⟩ := GlobalTheory.CongReps.exists_reps D (botSmall D i j) _ (GlobalTheory.BotPairSmall.conj_smul_ne_bot D hm)
  have hTT := GlobalTheory.BotPairSmall.cvec_conj_mem_TT D δ t0 hc ht _ _ hd e0 hv W hW3 hW4 _ hm hcop hcond (botBig D i j) rfl
  have hK := GlobalTheory.T.weilAction_cosetVector_fixed_principalCongruence D δ t0 hc ht _ _ hd e0 hv W hW3 hW4 _ hm hcop hcond (botBig D i j) rfl
  have hS := GlobalTheory.StdSumFix.stdSum_fix_eig D δ _ _ e0 W _ _ hTT hK R hR1 hR2
  have hN := absNorm_modT G t
  have hidx := GlobalTheory.BotPairSmall.blockJ_relIndex D (modT G t) hm (botBig D i j) (botBig D i j + botSmall D i j)
  have hQ : 1 ≤ levQ G.pl * Qn G t := by
    rw [← hN]; exact Nat.one_le_iff_ne_zero.2 (Ideal.absNorm_eq_zero_iff.not.2 hm)
  have heig : ∀ h ∈ GlobalTheory.BotPairSmall.blockJ D (modT G t) (botBig D i j) (botBig D i j + botSmall D i j), ∃ c : ℂ, ‖c‖ = 1 ∧
      W.Om 1 h (∑ r ∈ R, W.Om r 1 (GlobalTheory.BotPairSmall.cvec D δ (D.host.conj • modT G t) (botBig D i j) (botSmall D i j)
        (botBig D i j + botSmall D i j) e0)) = c • ∑ r ∈ R, W.Om r 1 (GlobalTheory.BotPairSmall.cvec D δ (D.host.conj • modT G t)
          (botBig D i j) (botSmall D i j) (botBig D i j + botSmall D i j) e0) := by
    intro h hh
    obtain ⟨k, hk, c, hc1, e⟩ := GlobalTheory.T.cosetVector_blockLevel_unimodular_eigen D δ t0 hc ht _ _ hd e0 hv W hW3 hW4 _ hm hcop hcond (botBig D i j) rfl h hh
    exact ⟨c, hc1, hS.2 h k c hk e⟩
  refine ⟨{
      crv := hc, pt0 := ht, a := botSmall D i j, d := botBig D i j + botSmall D i j, a_le := Nat.le_add_left _ _,
      d_even := hd, e0 := e0, vac := hv, W := W,
      n := fun τ => ((χν.n τ - ((botBig D i j + botSmall D i j : ℕ) : ℤ)) / 2).toNat, wt := ?_,
      F := ∑ r ∈ R, W.Om r 1 (GlobalTheory.BotPairSmall.cvec D δ (D.host.conj • modT G t) (botBig D i j) (botSmall D i j)
      (botBig D i j + botSmall D i j) e0),
      pres := GlobalTheory.T.conjugateModulus_standardTheta_presentation D δ t0 hc ht _ _ hd e0 hv W hW3 hW4 _ hm hcop (conj_modT_isCoprime_halfDifferent hL hpq hpq' G t) hcond (botBig D i j) rfl _ hN R hR1 hR2,
      fix := hS.1,
      J := GlobalTheory.BotPairSmall.blockJ D (modT G t) (botBig D i j) (botBig D i j + botSmall D i j),
      J_le := GlobalTheory.BotPairSmall.blockJ_le _ _ _ _,
      idx_ne := hidx.1,
      idx_le := hidx.2.trans (by rw [hN]; exact Nat.pow_le_pow_right hQ (by omega)),
      eig := heig }, rfl, rfl, ⟨fun x => ?_, fun x => ?_⟩, ⟨R, hR1, hR2, rfl⟩,
    fun h => GlobalTheory.BotPairSmall.blockJ_mem_iff_blockSet _ _ _ _ h⟩
  · intro τ
    show 2 * (((χν.n τ - ((botBig D i j + botSmall D i j : ℕ) : ℤ)) / 2).toNat : ℤ) = W.ep' * W.chV'.n τ - _
    rw [hW4, hW2]
    obtain ⟨r, hr⟩ := χν.par τ
    have := hn τ
    omega
  · show W.chV.f x ^ W.ep = _
    rw [hW3, zpow_one, hW1, hα]
  · show W.chV'.f x ^ W.ep' = _
    rw [hW4, zpow_one, hW2, hν]

end GlobalTheory.BotPairSmallTw

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBottomPairSmallMemberTwistedTupleStatement
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)
open GlobalTheory.SqTop (twPl Qn modT)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bottomPair_smallMember_twisted_tuple : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, GlobalTheory.NormSum.Inp D → L.Is μ₀ → Nat.Coprime D.host.pde (D.host.QS * D.host.q) → Nat.Coprime D.host.pde' (D.host.QS * D.host.q) → ∀ (G : GridData L sc) (t : T) {δ t0 : ℂ}, Crv D ⊤ δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0 → ∀ (i j : Fin D.R.m) (χα : HeckeU D (botSmall D i j)), (∀ x, χα.f x = (alphaH L t i j).1 (finIdl D x)) → ∀ (χν : HeckeU D (botBig D i j + botSmall D i j)), (∀ x, χν.f x = (nuH G t i j)⁻¹.1 (finIdl D x)) → (∀ τ, ((botBig D i j + botSmall D i j : ℕ) : ℤ) ≤ χν.n τ) → ∃ P' : GlobalTheory.NormSum.Pair D ⊤ δ t0 (levQ G.pl * Qn G t), P'.a = botSmall D i j ∧ P'.d = botBig D i j + botSmall D i j ∧ HasChars P' (alphaH L t i j) (nuH G t i j)⁻¹ ∧ IsStdDatum P' (D.host.conj • modT G t) (botBig D i j) ∧ IsBlockLevel P' (modT G t) (botBig D i j) := by
  first | exact @GlobalTheory.BotPairSmallTw.smallPair_exists_tw | exact GlobalTheory.BotPairSmallTw.smallPair_exists_tw | (intros; apply GlobalTheory.BotPairSmallTw.smallPair_exists_tw <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenousPDivGroupFinrankOmegaDual
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenousPDivGroupFinrankOmegaDual
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Dieu.IsogDim

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p]

def frobImage {N : Type} [AddCommGroup N] [Module (WittVector p k) N]
    (F : N →ₛₗ[(WittVector.frobenius : WittVector p k →+* WittVector p k)] N)
    (X : Submodule (WittVector p k) N) : Submodule (WittVector p k) N where
  carrier := {m | ∃ n ∈ X, F n = m}
  add_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, X.add_mem ha hb, map_add F a b⟩
  zero_mem' := ⟨0, X.zero_mem, map_zero F⟩
  smul_mem' := by
    rintro c _ ⟨a, ha, rfl⟩
    obtain ⟨d, rfl⟩ := (WittVector.frobeniusEquiv p k).surjective c
    refine ⟨d • a, X.smul_mem d ha, ?_⟩
    rw [map_smulₛₗ, WittVector.frobeniusEquiv_apply]

theorem mem_frobImage {N : Type} [AddCommGroup N] [Module (WittVector p k) N]
    (F : N →ₛₗ[(WittVector.frobenius : WittVector p k →+* WittVector p k)] N)
    (X : Submodule (WittVector p k) N) (m : N) : m ∈ frobImage F X ↔ ∃ n ∈ X, F n = m := Iff.rfl

theorem length_frobImage {N : Type} [AddCommGroup N] [Module (WittVector p k) N]
    (F : N →ₛₗ[(WittVector.frobenius : WittVector p k →+* WittVector p k)] N) (hF : Function.Injective F)
    (X : Submodule (WittVector p k) N) :
    Module.length (WittVector p k)
        (frobImage F ⊤ ⧸ Submodule.comap (frobImage F ⊤).subtype (frobImage F X)) =
      Module.length (WittVector p k) (N ⧸ X) := by
  haveI : RingHomSurjective (WittVector.frobenius : WittVector p k →+* WittVector p k) :=
    ⟨fun c => by
      obtain ⟨d, rfl⟩ := (WittVector.frobeniusEquiv p k).surjective c
      exact ⟨d, by rw [WittVector.frobeniusEquiv_apply]⟩⟩
  let f : N →ₛₗ[(WittVector.frobenius : WittVector p k →+* WittVector p k)] frobImage F ⊤ :=
    LinearMap.codRestrict (frobImage F ⊤) F (fun c => ⟨c, Submodule.mem_top, rfl⟩)
  have hf : Function.Bijective f := by
    refine ⟨fun a b h => hF (congrArg Subtype.val h), ?_⟩
    rintro ⟨m, n, -, rfl⟩
    exact ⟨n, rfl⟩
  have hX : Submodule.orderIsoMapComapOfBijective f hf X =
      Submodule.comap (frobImage F ⊤).subtype (frobImage F X) := by
    ext ⟨m, hm⟩
    change (⟨m, hm⟩ : frobImage F ⊤) ∈ Submodule.map f X ↔ _
    rw [Submodule.mem_map, Submodule.mem_comap]
    constructor
    · rintro ⟨n, hn, h⟩
      exact ⟨n, hn, congrArg Subtype.val h⟩
    · rintro ⟨n, hn, h⟩
      exact ⟨n, hn, Subtype.ext h⟩
  rw [Module.length_quotient, Module.length_quotient, ← hX, Order.coheight_orderIso]

theorem finite_of_frob_surj {N U : Type} [AddCommGroup N] [Module (WittVector p k) N]
    [Module.Finite (WittVector p k) N] [AddCommGroup U] [Module k U] (θ : N →+ U)
    (hθ : Function.Surjective θ)
    (hs : ∀ (a : WittVector p k) n, θ (WittVector.frobenius a • n) = WittVector.constantCoeff a • θ n) :
    Module.Finite k U := by
  classical
  obtain ⟨s, hs'⟩ := (Module.Finite.fg_top : (⊤ : Submodule (WittVector p k) N).FG)
  refine ⟨⟨s.image θ, ?_⟩⟩
  rw [Finset.coe_image, eq_top_iff]
  rintro u -
  obtain ⟨n, rfl⟩ := hθ u
  have hn : n ∈ Submodule.span (WittVector p k) (s : Set N) := hs' ▸ Submodule.mem_top
  induction hn using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    obtain ⟨b, rfl⟩ := (WittVector.frobeniusEquiv p k).surjective a
    rw [WittVector.frobeniusEquiv_apply, hs]
    exact Submodule.smul_mem _ _ hx

end GlobalTheory.Dieu.IsogDim

namespace GlobalTheory.Dieu.IsogDim

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p]

theorem isog_core (T : GlobalTheory.Dieu.Theory p) {G H : PDivGroup p k} (q : G ⟶ H)
    (hq : IsIsog q) :
    Function.Injective (T.map q) ∧
    Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) ≠ ⊤ ∧
    Module.finrank k G.omega = Module.finrank k H.omega := by
  obtain ⟨n, q', h1, h2⟩ := hq
  have huv : ∀ m : T.M G, T.map q (T.map q' m) = p ^ n • m := by
    intro m
    rw [← LinearMap.comp_apply, ← T.base.map_comp' trivial trivial trivial q q', h1,
      T.base.map_pow_smul trivial trivial, T.base.map_id' trivial, LinearMap.id_apply]
  have hvu : ∀ m : T.M H, T.map q' (T.map q m) = p ^ n • m := by
    intro m
    rw [← LinearMap.comp_apply, ← T.base.map_comp' trivial trivial trivial q' q, h2,
      T.base.map_pow_smul trivial trivial, T.base.map_id' trivial, LinearMap.id_apply]
  have hinj : Function.Injective (T.map q) := by
    intro a b hab
    have h := congrArg (T.map q') hab
    rw [hvu a, hvu b] at h
    have h0 : p ^ n • (a - b) = 0 := by rw [smul_sub, h, sub_self]
    exact sub_eq_zero.1 (T.base.eq_zero_of_pow_smul (G := H) trivial n _ h0)
  have LA := (GlobalTheory.T.witt_module_length_composition p k (T.M G) (T.M H) (T.M G)).1 (T.map q) (T.map q') hinj
  have LB := (GlobalTheory.T.witt_module_length_composition p k (T.M G) (T.M G) (T.M G)).2.1 (T.base.free G trivial)
    (T.base.finite G trivial) n (T.map q ∘ₗ T.map q') (fun a => huv a)
  rw [LB] at LA
  have hfin : Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) ≠ ⊤ := by
    intro h
    rw [h, top_add] at LA
    exact ENat.natCast_ne_top _ LA
  refine ⟨hinj, hfin, ?_⟩
  obtain ⟨θ, hθ⟩ := GlobalTheory.T.exists_theta_dieudonne_mod_frobenius_differentials p T k
  have dimω : ∀ K : PDivGroup p k,
      Module.length (WittVector p k) (T.M K ⧸ frobImage (T.F K) ⊤) = Module.finrank k K.omega := by
    intro K
    obtain ⟨-, hs, hk, hl, -⟩ := hθ K
    haveI : Module.Finite (WittVector p k) (T.M K) := T.base.finite K trivial
    haveI := finite_of_frob_surj (θ K) hs hl
    refine (GlobalTheory.T.length_ge_finrank_of_semilinear_surjective p k (T.M K) K.omega (WittVector.frobeniusEquiv p k) (θ K) hs ?_
      (frobImage (T.F K) ⊤)).2 ?_
    · intro a m
      rw [WittVector.frobeniusEquiv_apply]
      exact hl a m
    · intro m
      rw [hk, mem_frobImage]
      constructor
      · rintro ⟨c, -, h⟩
        exact ⟨c, h.symm⟩
      · rintro ⟨c, h⟩
        exact ⟨c, Submodule.mem_top, h.symm⟩
  have hF : ∀ y : T.M H, T.map q (T.F H y) = T.F G (T.map q y) :=
    T.base.map_F trivial trivial q
  set X := LinearMap.range (T.map q) with hXdef
  set L3 := frobImage (T.F G) X with hL3
  set FG := frobImage (T.F G) ⊤ with hFG
  set FH := frobImage (T.F H) ⊤ with hFH
  have hle : L3 ≤ FG := by
    rintro m ⟨c, -, rfl⟩
    exact ⟨c, Submodule.mem_top, rfl⟩
  have hr1 : LinearMap.range (FG.subtype ∘ₗ (Submodule.comap FG.subtype L3).subtype) = L3 := by
    rw [LinearMap.range_comp, Submodule.range_subtype, Submodule.map_comap_subtype, inf_eq_right.2 hle]
  have hr2 : LinearMap.range (T.map q ∘ₗ FH.subtype) = L3 := by
    ext m
    rw [LinearMap.mem_range, hL3, mem_frobImage]
    constructor
    · rintro ⟨⟨x, y, -, rfl⟩, rfl⟩
      exact ⟨T.map q y, LinearMap.mem_range.2 ⟨y, rfl⟩, (hF y).symm⟩
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨y, rfl⟩ := LinearMap.mem_range.1 hz
      exact ⟨⟨T.F H y, y, Submodule.mem_top, rfl⟩, hF y⟩
  have eA := (GlobalTheory.T.witt_module_length_composition p k (T.M G) FG (Submodule.comap FG.subtype L3)).1
    FG.subtype (Submodule.comap FG.subtype L3).subtype (Submodule.injective_subtype _)
  rw [hr1, Submodule.range_subtype, Submodule.range_subtype] at eA
  have eB := (GlobalTheory.T.witt_module_length_composition p k (T.M G) (T.M H) FH).1 (T.map q) FH.subtype hinj
  rw [hr2, Submodule.range_subtype] at eB
  have hC : Module.length (WittVector p k) (FG ⧸ Submodule.comap FG.subtype L3) =
      Module.length (WittVector p k) (T.M G ⧸ X) :=
    length_frobImage (T.F G) (GlobalTheory.T.dieudonneTheory_V_eq_verschiebung_injective p T k G).1 X
  rw [hC, hFG, dimω G] at eA
  rw [hFH, dimω H] at eB
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.1 hfin
  rw [← hd] at eA eB
  have h' : ((Module.finrank k G.omega + d : ℕ) : ℕ∞) = ((d + Module.finrank k H.omega : ℕ) : ℕ∞) := by
    push_cast
    exact eA.symm.trans eB
  have h'' := Nat.cast_injective h'
  omega

end GlobalTheory.Dieu.IsogDim

namespace GlobalTheory.Dieu

theorem isog_finrank_omega : ∀ (p : ℕ) [Fact p.Prime] (T : GlobalTheory.Dieu.Theory p)
    (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G H : PDivGroup p k) (q : G ⟶ H),
    IsIsog q → Function.Injective (T.map q) ∧
      Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) ≠ ⊤ ∧
      Module.finrank k G.omega = Module.finrank k H.omega ∧
      Module.finrank k G.dual.omega = Module.finrank k H.dual.omega := by
  intro p _ T k _ _ _ G H q hq
  obtain ⟨h1, h2, h3⟩ := IsogDim.isog_core T q hq
  obtain ⟨-, hd, -⟩ := GlobalTheory.T.pDivGroupIsogeny_height_eq_dual_sameDegree p k G H q hq
  exact ⟨h1, h2, h3, (IsogDim.isog_core T (dualHom G H q) hd).2.2.symm⟩

end GlobalTheory.Dieu
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenousPDivGroupFinrankOmegaDualStatement
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

theorem _root_.GlobalTheory.T.isogenous_pDivGroup_finrank_omega_dual :
    ∀ (p : ℕ) [Fact p.Prime] (T : GlobalTheory.Dieu.Theory p)
      (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G H : PDivGroup p k) (q : G ⟶ H),
      IsIsog q → Function.Injective (T.map q) ∧
        Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) ≠ ⊤ ∧
        Module.finrank k G.omega = Module.finrank k H.omega ∧
        Module.finrank k G.dual.omega = Module.finrank k H.dual.omega :=
  @GlobalTheory.Dieu.isog_finrank_omega
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedExtensionPresentationOfSeriesPairs
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedExtensionPresentationOfSeriesPairs
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem GlobalTheory.Katz.isRigOf_rigMk : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k) (c : Chart G d), ∀ (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (ρ : MvPowerSeries (Fin d ⊕ Fin d) k × (Fin d → k) →ₗ[k] ((G.cocycles × G.omega) ⧸ _root_.LinearMap.range (G.cob.prod (_root_.LinearMap.codRestrict G.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G.A i))).domRestrict G.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n))))))), c.IsLawOf μ → (∀ s w (z : G.cocycles) (u : G.omega), (∀ n, z.1 n = c.ev₂ n s) → (∀ n, u.1 n = ∑ i, w i • dUnit (R := k) (c.x n i)) → ρ (s, w) = G.rigMk (z, u)) → IsRigOf μ ρ := by
  intro p k _ d G c μ ρ hμ hρ
  have hcoc := GlobalTheory.T.isSymmetricFormalGroupCocycle_iff_mem_cocycles p k d G c μ hμ
  have hdu := GlobalTheory.T.counit_cotangentClass_powerSeriesEvalAtNilpotent k d
  have hlaw := ((GlobalTheory.T.connectedPDivGroup_formalLaw_coordinates p k d G c).2 μ hμ).2
  have hom := GlobalTheory.T.invariantDifferentials_connectedPDivGroup_coordinates p k d G c
  have hone := GlobalTheory.T.functions_eq_series_in_chart p k d G c
  have hpres := (GlobalTheory.T.chart_square_coordinates_present_levels p k d G c).2
  constructor
  · intro v
    obtain ⟨⟨z, u⟩, rfl⟩ := Submodule.mkQ_surjective _ v
    obtain ⟨s, hs, -⟩ := hpres z.1 (fun n => (z.2 n).2)
    obtain ⟨w, hw, -⟩ := hom.2 u
    have hz : (fun n => c.ev₂ n s) = z.1 := funext hs
    refine ⟨s, w, (hcoc s).2 (hz ▸ z.2), ?_⟩
    exact hρ s w z u (fun n => (hs n).symm) hw
  · intro s w hs
    let z : G.cocycles := ⟨fun n => c.ev₂ n s, (hcoc s).1 hs⟩
    let u : G.omega := ⟨fun n => ∑ i, w i • dUnit (R := k) (c.x n i), hom.1 w⟩
    rw [hρ s w z u (fun _ => rfl) (fun _ => rfl)]
    change Submodule.Quotient.mk _ = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
    constructor
    · rintro ⟨B, hB⟩
      rw [LinearMap.prod_apply, Prod.mk.injEq] at hB
      obtain ⟨b, hb, -⟩ := hone.2.2 B.1 B.2
      refine ⟨b, ?_, ?_⟩
      · have hz2 : ∀ n, pullbackTwo (G.res n) (c.ev₂ (n + 1) s) = c.ev₂ n s := fun n => hone.2.1 n s
        obtain ⟨t, -, ht⟩ := hpres (fun n => c.ev₂ n s) hz2
        have h1 := ht s (fun _ => rfl)
        have h2 := ht (cob1 μ b) (fun n => by
          rw [(hlaw n b).2, hb n]
          exact (congrArg (fun y : G.cocycles => y.1 n) hB.1))
        exact h1.trans h2.symm
      · obtain ⟨w', -, hw'⟩ := hom.2 u
        have e1 := hw' w (fun _ => rfl)
        have e2 := hw' (lin b) (fun n => by
          rw [← (hdu (G.A n) (c.x n) (c.nil n) (c.aug n) b).2]
          change _ = dUnit (R := k) (c.ev n b)
          rw [hb n]
          exact (congrArg (fun y : G.omega => y.1 n) hB.2).symm)
        exact e1.trans e2.symm
    · rintro ⟨b, rfl, rfl⟩
      refine ⟨⟨fun n => c.ev n b, fun n => hone.1 n b⟩, ?_⟩
      rw [LinearMap.prod_apply, Prod.mk.injEq]
      constructor
      · apply Subtype.ext; funext n
        exact ((hlaw n b).2).symm
      · apply Subtype.ext; funext n
        exact (hdu (G.A n) (c.x n) (c.nil n) (c.aug n) b).2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedExtensionPresentationOfSeriesPairsStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rigidifiedExtension_presentation_of_series_pairs : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k) (c : Chart G d), ∀ (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (ρ : MvPowerSeries (Fin d ⊕ Fin d) k × (Fin d → k) →ₗ[k] ((G.cocycles × G.omega) ⧸ _root_.LinearMap.range (G.cob.prod (_root_.LinearMap.codRestrict G.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G.A i))).domRestrict G.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n))))))), c.IsLawOf μ → (∀ s w (z : G.cocycles) (u : G.omega), (∀ n, z.1 n = c.ev₂ n s) → (∀ n, u.1 n = ∑ i, w i • dUnit (R := k) (c.x n i)) → ρ (s, w) = G.rigMk (z, u)) → IsRigOf μ ρ := by
  first | exact @GlobalTheory.Katz.isRigOf_rigMk | exact GlobalTheory.Katz.isRigOf_rigMk | (intros; apply GlobalTheory.Katz.isRigOf_rigMk <;> assumption)
end
end
