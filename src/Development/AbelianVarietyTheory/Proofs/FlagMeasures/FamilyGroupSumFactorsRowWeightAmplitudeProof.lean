module

public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.FamilyGroupSumFactorsWeightAmplitude
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalAmplitudeEqLocalAmplitudes
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowDoubleCosetSumNormSqBound
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalisedBaseFramesRelevantPair
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RatCoordCont

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermMovesToBaseFramesUpToUnitriangular
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermMovesToBaseFramesUpToUnitriangular
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL.MoveTerm

theorem term_moves_to_base : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ t₀ : TauC Y u u', t₀.toTerm.atPt w → ∃ (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' := by
  intro D X Y u u' _hS w F00 F'0 FP hZ _hG _hB t₀ ht
  obtain ⟨F', ⟨hP, hmk⟩, hGv, hCell⟩ := ht
  have hrow : IsRowLat D (X.Fu u) t₀.lam := (Y.rowsOK u).1 _ t₀.mem
  obtain ⟨hGF, hCF, -⟩ := Formalism.L2.SG.Closed.TermFun_holds D u u' (X.Fu u) t₀.lam hrow
  have hrel := (Formalism.L2.SG.Closed.TermEqIff_holds D u u' (X.Fu u) t₀.lam hrow _ _).1 hmk
  have hGt : Gval (lf D (X.Fu u)) t₀.frame ≠ 0 := by
    intro h
    apply hGv
    rw [hGF _ _ hrel]
    exact h
  have hCt := (hCF _ _ hrel w).1 hCell
  have hTu : ∀ v : D.what₂.Word, ((Tu D v : ℕ) : D.host.E) ≠ 0 := fun v =>
    Nat.cast_ne_zero.mpr (Formalism.L2.SG.GramJoint.Tu_pos D v).ne'
  obtain ⟨-, γ, hγ, ⟨A, hA, hAc⟩, ⟨A', hA', hAc'⟩⟩ :=
    GlobalTheory.T.rationalFramePairs_differ_isometry_unitriangular D (lf D (X.Fu u)) F00 t₀.frame F'0 w (hTu u) (hTu u') hGt hCt hZ
  refine ⟨γ, A, A', hγ, ?_, ?_, fun b => hAc b, fun b => hAc' b⟩
  · exact fun i j => ⟨fun h => hA.1 i j h, fun h => h ▸ hA.2 i⟩
  · exact fun i j => ⟨fun h => hA'.1 i j h, fun h => h ▸ hA'.2 i⟩

end GlobalTheory.HL.MoveTerm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermMovesToBaseFramesUpToUnitriangularStatement
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.term_moves_to_baseFrames_up_to_unitriangular : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ t₀ : TauC Y u u', t₀.toTerm.atPt w → ∃ (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' := by
  first | exact @GlobalTheory.HL.MoveTerm.term_moves_to_base | exact GlobalTheory.HL.MoveTerm.term_moves_to_base | (intros; apply GlobalTheory.HL.MoveTerm.term_moves_to_base <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGlobalCoordinatesRationalFlagPair
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGlobalCoordinatesRationalFlagPair
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HL.GCoordEx

open ValuativeRel

section Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]

theorem h_smul_right (H : Formalism.MainNotions.S.Loc.HermSp M V) (c : E) (x y : V) :
    H.h x (c • y) = M.L.cj c * H.h x y := by
  rw [H.h_herm (c • y) x, H.h_smul_left, map_mul, ← H.h_herm]

theorem loc_ex (hM : M.OK) (H : Formalism.MainNotions.S.Loc.HermSp M V) (r k : ℕ) (P : Formalism.MainNotions.S.LocNG.FPair H r)
    (hP : P.RelG (Formalism.MainNotions.S.LocNG.theta M)) (b : Module.Basis (Fin (k + 2 * r + 1)) E V) (es es' : Fin r → V)
    (hd : ∀ a j, H.h (P.A.f a) (es j) = if a = j.castSucc then 1 else 0)
    (hd' : ∀ a j, H.h (P.B.f a) (es' j) = if a = j.castSucc then 1 else 0)
    (hi : ∀ i j, H.h (es i) (es j) = 0) (hi' : ∀ i j, H.h (es' i) (es' j) = 0) :
    ∃ S : Frames M.L r k, S.Hm = Matrix.of (fun i j => H.h (b i) (b j)) ∧
      S.es = (fun j => b.equivFun (es j)) ∧ S.es' = (fun j => b.equivFun (es' j)) ∧
      S.gg = M.split.isSome ∧ ∃ c : WCoord P S, c.e = b.equivFun := by
  obtain ⟨-, -, hG, -, -, ⟨w, hw⟩, hTo, hT, hTo', hT', hgg⟩ := hP
  have := hM.loc
  have := CoordExist.nontriv M.L
  obtain ⟨ϖ, hϖ, hϖg⟩ : ∃ ϖ : 𝒪[F], Irreducible ϖ ∧ ∀ g, M.split = some g → ϖ = g.q := by
    rcases h : M.split with _ | g
    · obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
      exact ⟨ϖ, hϖ, fun g hg => by cases hg⟩
    · exact ⟨g.q, g.q_irr, fun g' hg => by cases hg; rfl⟩
  refine ⟨
    { ϖ := ϖ
      ϖ_irr := hϖ
      Hm := Matrix.of fun i j => H.h (b i) (b j)
      herm := CoordExist.hermND H b
      T := Units.mk0 _ hT
      T' := Units.mk0 _ hT'
      f := fun a => b.equivFun (P.A.f a)
      f' := fun a => b.equivFun (P.B.f a)
      es := fun a => b.equivFun (es a)
      es' := fun a => b.equivFun (es' a)
      gram := fun a c => by rw [CoordExist.hf_basis]; exact CoordExist.gram_eq _ _ _
      gram' := fun a c => by rw [CoordExist.hf_basis]; exact CoordExist.gram_eq _ _ _
      dual := fun a c => by rw [CoordExist.hf_basis]; exact hd _ _
      dual' := fun a c => by rw [CoordExist.hf_basis]; exact hd' _ _
      iso := fun a c => by rw [CoordExist.hf_basis]; exact hi _ _
      iso' := fun a c => by rw [CoordExist.hf_basis]; exact hi' _ _
      w := w
      relevant := fun a c => ?_
      G_ne := ?_
      gg := M.split.isSome
      gg_ok := fun h => ?_ }, rfl, rfl, rfl, rfl,
    { e := b.equivFun
      h_eq := fun x y => CoordExist.hf_basis H b x y
      f_eq := fun _ => rfl
      f'_eq := fun _ => rfl
      T_eq := rfl
      T'_eq := rfl
      gg_none := fun h => by simp only [h, Option.isSome_none]
      gg_some := fun g h => ⟨by simp only [h, Option.isSome_some], hϖg g h⟩ }, rfl⟩
  · rw [CoordExist.hf_basis, ← hw, mul_right_comm, ← mul_pow]
    simp [Formalism.MainNotions.S.Loc.HermSp.Zhat]
  · simp only [CoordExist.hf_basis]
    have h1 : H.Dl P.A.f P.B.f (r + 1) =
        lead (Matrix.of fun a c => H.h (P.B.f c) (P.A.f a)) (Fin.last (r + 1)) := by
      unfold Formalism.MainNotions.S.Loc.HermSp.Dl; rw [dite_eq_left le_rfl]; rfl
    have h2 : H.Dl P.A.f P.B.f r =
        lead (Matrix.of fun a c => H.h (P.B.f c) (P.A.f a)) (Fin.last r).castSucc := by
      unfold Formalism.MainNotions.S.Loc.HermSp.Dl; rw [dite_eq_left (Nat.le_succ r)]; rfl
    rw [← h1, ← h2]
    exact hG
  · obtain ⟨g, hg⟩ := Option.isSome_iff_exists.1 h
    obtain ⟨⟨u, v, hu, hv⟩, -⟩ := hgg g hg
    exact ⟨CoordExist.not_field M.L g, CoordExist.unit_of hTo u hu, CoordExist.unit_of hTo' v hv⟩

end Loc

section Glob

variable {D : D7}

theorem nV_eq (D : D7) : nV D = D.R.k + 2 * D.R.rS + 1 := by
  have h1 : nV D = D.R.r := by
    show (D.sp.Y 0).rank = _
    rw [D.sp.Y_rank 0 (Nat.zero_le _)]
    simp [Ranks.rankY]
  have hm2 := D.R.two_le_m
  obtain ⟨j, hj⟩ := D.R.m_even
  have hrS : 2 * D.R.rS + 1 = D.R.m - 1 := by
    unfold Formalism.BasicNotions.Ranks.rS
    rw [hj]
    omega
  rw [h1]
  unfold Formalism.BasicNotions.Ranks.r
  omega

def sg (D : D7) : Fin (D.R.k + 2 * D.R.rS + 1) ≃ Fin (nV D) := finCongr (nV_eq D).symm

def eG (D : D7) : (VS D).V ≃ₗ[D.host.E] (Fin (D.R.k + 2 * D.R.rS + 1) → D.host.E) :=
  (VS D).frame.equivFun.trans (LinearEquiv.funCongrLeft D.host.E D.host.E (sg D))

def eL (D : D7) (p : PlF D) : Vp D p ≃ₗ[(D.s.atP p).Ep] (Fin (D.R.k + 2 * D.R.rS + 1) → (D.s.atP p).Ep) :=
  LinearEquiv.funCongrLeft _ _ (sg D)

def HmG (D : D7) : Matrix (Fin (D.R.k + 2 * D.R.rS + 1)) (Fin (D.R.k + 2 * D.R.rS + 1)) D.host.E :=
  Matrix.of fun i j => gramV D (sg D i) (sg D j)

theorem eL_bcP (Z : LocDat D) (p : PlF D) (x : (VS D).V) : eL D p (baseChange₂ D p x) = (placesOf Z).bc p (eG D x) := by
  funext i; rfl

theorem sum_sg {R : Type} [AddCommMonoid R] (g : Fin (nV D) → Fin (nV D) → R) :
    ∑ i, ∑ j, g (sg D i) (sg D j) = ∑ i, ∑ j, g i j := by
  calc ∑ i, ∑ j, g (sg D i) (sg D j) = ∑ i, ∑ j, g (sg D i) j :=
        Finset.sum_congr rfl fun i _ => Equiv.sum_comp (sg D) (g (sg D i))
    _ = ∑ i, ∑ j, g i j := Equiv.sum_comp (sg D) (fun i => ∑ j, g i j)

theorem h_eqG (x y : (VS D).V) :
    ∑ i, ∑ j, eG D x i * HmG D i j * star (eG D y j) = brS (VS D) x y := by
  have key : (VS D).hT y x = ∑ j, ∑ i, star ((VS D).frame.repr y j) *
      ((VS D).frame.repr x i * (VS D).hT ((VS D).frame j) ((VS D).frame i)) := by
    conv_lhs => rw [← (VS D).frame.sum_repr y, ← (VS D).frame.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smulₛₗ, smul_eq_mul, starRingEnd_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      RingHom.id_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  have e1 : ∑ i, ∑ j, eG D x i * HmG D i j * star (eG D y j) = ∑ i, ∑ j,
      (fun a b => (VS D).frame.repr x a * gramV D a b * star ((VS D).frame.repr y b)) (sg D i) (sg D j) := rfl
  rw [e1, sum_sg (D := D) (fun a b => (VS D).frame.repr x a * gramV D a b * star ((VS D).frame.repr y b)), brS, key, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  simp only [gramV, brS]
  ring

theorem split_isSome (Z : LocDat D) (p : PlF D) : (Z.M p).split.isSome = (D.s.atP p).split.isSome := by
  obtain ⟨-, -, -, -, -, h⟩ := Z.agree p
  revert h
  cases (Z.M p).split <;> cases (D.s.atP p).split <;> simp

end Glob

section Glob2

variable {D : D7}

def bL (D : D7) (p : PlF D) : Module.Basis (Fin (D.R.k + 2 * D.R.rS + 1)) (D.s.atP p).Ep (Vp D p) :=
  Module.Basis.ofEquivFun (eL D p)

theorem bL_apply (p : PlF D) (i : Fin (D.R.k + 2 * D.R.rS + 1)) : bL D p i = Pi.single (sg D i) 1 := by
  funext j
  simp only [bL, Module.Basis.coe_ofEquivFun, eL, LinearEquiv.funCongrLeft_symm]
  simp only [LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]
  by_cases h : j = sg D i
  · subst h; simp
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne]
    intro h'; apply h; rw [← h']; simp

theorem gram_bL (Z : LocDat D) (p : PlF D) :
    Matrix.of (fun i j => (locH Z p).h (bL D p i) (bL D p j)) = (HmG D).map (D.s.atP p).ιE := by
  ext i j
  simp only [Matrix.of_apply, bL_apply, Matrix.map_apply, HmG]
  show LocFacts₂ Z.M p _ _ = _
  rw [localForm_single]
  simp [Matrix.vecMul, dotProduct, Pi.single_apply]

theorem loc_pair (Z : LocDat D) (p : PlF D) (s t : (D.s.atP p).Ep) (x y : (VS D).V) :
    (locH Z p).h (s • baseChange₂ D p x) (t • baseChange₂ D p y) = s * ((Z.M p).L.cj t * (D.s.atP p).ιE (brS (VS D) x y)) := by
  rw [(locH Z p).h_smul_left, h_smul_right]
  congr 2
  exact baseChangeAt_form Z.M p (Z.hcj p) x y

end Glob2

section Glob3

variable {D : D7}

def cval (Z : LocDat D) (p : PlF D) : (D.s.atP p).Fp := Z.δ p * (D.s.atP p).ιF ((uP p : ℚ) : D.host.F)

theorem unitAt_ne (p : PlF D) : uP p ≠ 0 := by
  have h0 := D.host.g_prime 0
  have h1 := D.host.g_prime 1
  unfold uP gpart
  refine div_ne_zero ?_ ?_
  · split_ifs
    · exact_mod_cast h0.ne_zero
    · exact_mod_cast h1.ne_zero
    · exact one_ne_zero
  · unfold Formalism.MainNotions.S.Lat.gS
    exact_mod_cast (Nat.mul_ne_zero h0.ne_zero h1.ne_zero)

theorem cval_ne (Z : LocDat D) (p : PlF D) : cval Z p ≠ 0 := by
  obtain ⟨-, hδ, -⟩ := Z.agree p
  refine mul_ne_zero hδ ?_
  rw [map_ne_zero]
  exact_mod_cast unitAt_ne p

theorem cval_E (Z : LocDat D) (p : PlF D) :
    algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p) * (D.s.atP p).ιE ((uP p : ℚ) : D.host.E) =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cval Z p) := by
  rw [cval, map_mul, ← (D.s.atP p).compat, map_ratCast (algebraMap D.host.F D.host.E)]

theorem cval_unitE (Z : LocDat D) (p : PlF D) : IsUnit (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cval Z p)) :=
  (isUnit_iff_ne_zero.2 (cval_ne Z p)).map _

theorem frFac_eq (Z : LocDat D) (p : PlF D) (a : Fin (D.R.rS + 1)) :
    frFac Z.δ p a = Ring.inverse (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cval Z p ^ (D.R.rS - (a : ℕ)))) := by
  rw [frFac, cval_E, map_pow]

theorem frFac_mul (Z : LocDat D) (p : PlF D) (a : Fin (D.R.rS + 1)) :
    algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cval Z p ^ (D.R.rS - (a : ℕ))) * frFac Z.δ p a = 1 := by
  rw [frFac_eq, map_pow]
  exact Ring.mul_inverse_cancel _ ((cval_unitE Z p).pow _)

theorem loc_dual (Z : LocDat D) (p : PlF D) {N : ℕ} (F0 : FlagG (VS D) D.R.rS (N : D.host.E))
    (y : Fin D.R.rS → (VS D).V) (hy : Formalism.L2.SG.Pf.Cnt.R1.Dual F0.e y F0.z N) (a : Fin (D.R.rS + 1))
    (j : Fin D.R.rS) :
    (locH Z p).h (scaled Z p F0.fvec a)
      (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cval Z p ^ (D.R.rS - (j : ℕ))) • baseChange₂ D p (y j)) =
      if a = j.castSucc then 1 else 0 := by
  show (locH Z p).h (frFac Z.δ p a • baseChange₂ D p (F0.fvec a)) _ = _
  rw [loc_pair, AlgEquiv.commutes]
  induction a using Fin.lastCases with
  | last =>
    have h0 : brS (VS D) (F0.fvec (Fin.last _)) (y j) = 0 := by
      simp only [FlagG.fvec, Fin.snoc_last, brS]; exact hy.yz j
    rw [h0, map_zero, mul_zero, mul_zero, if_neg (Fin.castSucc_lt_last j).ne']
  | cast i =>
    have h0 : brS (VS D) (F0.fvec i.castSucc) (y j) = if i = j then 1 else 0 := by
      simp only [FlagG.fvec, Fin.snoc_castSucc, brS]; exact hy.ye j i
    rw [h0]
    simp only [Fin.castSucc_inj]
    split_ifs with hij
    · subst hij
      rw [map_one, mul_one, mul_comm]
      have := frFac_mul Z p i.castSucc
      rwa [Fin.coe_castSucc] at this
    · rw [map_zero, mul_zero, mul_zero]

theorem loc_iso (Z : LocDat D) (p : PlF D) (s t : (D.s.atP p).Ep) {N : ℕ} (F0 : FlagG (VS D) D.R.rS (N : D.host.E))
    (y : Fin D.R.rS → (VS D).V) (hy : Formalism.L2.SG.Pf.Cnt.R1.Dual F0.e y F0.z N) (i j : Fin D.R.rS) :
    (locH Z p).h (s • baseChange₂ D p (y i)) (t • baseChange₂ D p (y j)) = 0 := by
  rw [loc_pair]
  simp only [brS, hy.yy, map_zero, mul_zero]

end Glob3

section Fin

variable {D : D7}

theorem unit_of_mem {K : Type} [Field K] [ValuativeRel K] {c : K} (hc : c ≠ 0) (h1 : c ∈ 𝒪[K])
    (h2 : c⁻¹ ∈ 𝒪[K]) : ∃ u : (𝒪[K])ˣ, ((u : 𝒪[K]) : K) = c :=
  ⟨⟨⟨c, h1⟩, ⟨c⁻¹, h2⟩, Subtype.ext (mul_inv_cancel₀ hc), Subtype.ext (inv_mul_cancel₀ hc)⟩, rfl⟩

theorem resChar_mem (p : PlF D) : ((Formalism.MainNotions.S.Loc.resChar p : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact ringChar.Nat.cast_ringChar

theorem iF_unit (p : PlF D) (x : 𝓞 D.host.F) (hx : x ∉ p.asIdeal) :
    ((D.s.atP p).ιF (x : D.host.F))⁻¹ ∈ 𝒪[(D.s.atP p).Fp] ∧ (D.s.atP p).ιF (x : D.host.F) ≠ 0 := by
  have hv : p.valuation D.host.F (x : D.host.F) = 1 := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff]
    exact hx
  have h1 : (D.s.atP p).ιF 1 ≤ᵥ (D.s.atP p).ιF (x : D.host.F) := by
    rw [(D.s.atP p).val, hv, map_one]
  rw [map_one, Valuation.Compatible.vle_iff_le (v := valuation (D.s.atP p).Fp), map_one] at h1
  have hx0 : (D.s.atP p).ιF (x : D.host.F) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at h1
    exact absurd h1 (not_le.2 zero_lt_one)
  refine ⟨?_, hx0⟩
  rw [Valuation.mem_integer_iff, map_inv₀]
  exact inv_le_one_of_one_le₀ h1

theorem gg_ne_zero (D : D7) : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ≠ 0 := by
  exact_mod_cast Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero

theorem not_mem_of (p : PlF D) (hn : ¬ ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal) (i : Fin 2) :
    Formalism.MainNotions.S.Loc.resChar p ≠ D.host.g i := by
  intro h
  apply hn
  have hc := resChar_mem p
  rw [h] at hc
  rw [Nat.cast_mul]
  fin_cases i
  · exact Ideal.mul_mem_right _ _ hc
  · exact Ideal.mul_mem_left _ _ hc

theorem split_fin (D : D7) : {p : PlF D | (D.s.atP p).split.isSome = true}.Finite := by
  refine (Ideal.finite_factors (I := Ideal.span {((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F)}) ?_).subset ?_
  · rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact gg_ne_zero D
  intro p hp
  simp only [Set.mem_setOf_eq] at hp ⊢
  rw [Ideal.dvd_span_singleton]
  by_contra hn
  rw [D.s_split] at hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with h | h
  · exact not_mem_of p hn 0 h
  · exact not_mem_of p hn 1 h

theorem isUnit_unitAt (D : D7) :
    {p : PlF D | ¬ ∃ u : (𝒪[(D.s.atP p).Fp])ˣ,
      ((u : 𝒪[(D.s.atP p).Fp]) : (D.s.atP p).Fp) = (D.s.atP p).ιF ((uP p : ℚ) : D.host.F)}.Finite := by
  refine (Ideal.finite_factors (I := Ideal.span {((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F)}) ?_).subset ?_
  · rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact gg_ne_zero D
  intro p hp
  simp only [Set.mem_setOf_eq] at hp ⊢
  rw [Ideal.dvd_span_singleton]
  by_contra hn
  apply hp
  have hu : uP p = ((D.host.g 0 * D.host.g 1 : ℕ) : ℚ)⁻¹ := by
    unfold uP gpart
    rw [if_neg (not_mem_of p hn 0), if_neg (not_mem_of p hn 1)]
    unfold Formalism.MainNotions.S.Lat.gS
    push_cast
    ring
  obtain ⟨hinv, hx0⟩ := iF_unit p _ hn
  have e : (D.s.atP p).ιF ((uP p : ℚ) : D.host.F) =
      ((D.s.atP p).ιF (((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) : D.host.F))⁻¹ := by
    rw [hu, ← map_inv₀]
    congr 1
    push_cast
    rfl
  rw [e]
  refine unit_of_mem (inv_ne_zero hx0) hinv ?_
  rw [inv_inv]
  exact GlobalTheory.LocDiffGen.iF_int p _

theorem memF_of (p : PlF D) (c : (D.s.atP p).Fp) (h : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c ∈ (D.s.atP p).O) :
    c ∈ 𝒪[(D.s.atP p).Fp] := by
  rw [(D.s.atP p).O_def] at h
  have hi : IsIntegral 𝒪[(D.s.atP p).Fp] c :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom 𝒪[(D.s.atP p).Fp] (D.s.atP p).Fp (D.s.atP p).Ep)
      (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep).injective).1 h
  exact PI.UnitaryGroupMassFormula.CntFormula.DeltaC.mem_of_isIntegral_fp (D.s.atP p) hi

theorem delta_unit (D : D7) (Z : LocDat D) :
    {p : PlF D | ¬ ∃ u : (𝒪[(D.s.atP p).Fp])ˣ, ((u : 𝒪[(D.s.atP p).Fp]) : (D.s.atP p).Fp) = Z.δ p}.Finite := by
  refine (Ideal.finite_factors (I := differentIdeal ℤ (𝓞 D.host.F)) ?_).subset ?_
  · exact differentIdeal_ne_bot
  intro p hp
  simp only [Set.mem_setOf_eq] at hp ⊢
  rw [Ideal.dvd_iff_le]
  intro x hx
  by_contra hxp
  apply hp
  obtain ⟨-, hδ, -, hO, -, -⟩ := Z.agree p
  have hspan := GlobalTheory.LocDiffGen.span_different_eq D Z p
  have himg : ∀ y : 𝓞 D.host.F, (D.s.atP p).ιE (algebraMap D.host.F D.host.E (y : D.host.F)) =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (y : D.host.F)) := fun y => (D.s.atP p).compat _
  have hin : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p) ∈ (D.s.atP p).O := by
    have hm : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p) ∈ Submodule.span (Z.M p).L.O
        ((fun x : 𝓞 D.host.F => (D.s.atP p).ιE (algebraMap D.host.F D.host.E x)) ''
          (differentIdeal ℤ (𝓞 D.host.F) : Set (𝓞 D.host.F))) := by
      rw [hspan]; exact Submodule.mem_span_singleton_self _
    have key : ∀ v ∈ Submodule.span (Z.M p).L.O
        ((fun x : 𝓞 D.host.F => (D.s.atP p).ιE (algebraMap D.host.F D.host.E x)) ''
          (differentIdeal ℤ (𝓞 D.host.F) : Set (𝓞 D.host.F))), v ∈ (Z.M p).L.O := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨y, -, rfl⟩ := hz
        show (D.s.atP p).ιE (algebraMap D.host.F D.host.E (y : D.host.F)) ∈ (Z.M p).L.O
        rw [himg, hO]
        exact PI.CntNotIntW.algMap_mem_O D p _ (GlobalTheory.LocDiffGen.iF_int p y)
      | zero => exact zero_mem _
      | add a b _ _ ha hb => exact add_mem ha hb
      | smul c a _ ha => exact (Z.M p).L.O.mul_mem c.2 ha
    rw [← hO]
    exact key _ hm
  have hx2 : (D.s.atP p).ιE (algebraMap D.host.F D.host.E (x : D.host.F)) ∈
      (Z.M p).L.O ∙ algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p) := by
    rw [← hspan]
    exact Submodule.subset_span ⟨x, hx, rfl⟩
  obtain ⟨o, ho⟩ := Submodule.mem_span_singleton.1 hx2
  obtain ⟨hinvx, hx0⟩ := iF_unit p x hxp
  rw [himg] at ho
  have hinv : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p)⁻¹ ∈ (D.s.atP p).O := by
    have e : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p)⁻¹ =
        (o : (D.s.atP p).Ep) * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (x : D.host.F))⁻¹ := by
      have ho' : (o : (D.s.atP p).Ep) * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p) =
          algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (x : D.host.F)) := ho
      have h3 : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p)⁻¹ =
          algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (x : D.host.F)) *
            algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (((D.s.atP p).ιF (x : D.host.F))⁻¹ * (Z.δ p)⁻¹) := by
        rw [← map_mul]; congr 1; field_simp
      rw [h3, ← ho', map_mul]
      have h4 : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p) * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p)⁻¹ = 1 := by
        rw [← map_mul, mul_inv_cancel₀ hδ, map_one]
      calc (o : (D.s.atP p).Ep) * algebraMap _ _ (Z.δ p) *
            (algebraMap _ _ ((D.s.atP p).ιF (x : D.host.F))⁻¹ * algebraMap _ _ (Z.δ p)⁻¹)
          = (o : (D.s.atP p).Ep) * algebraMap _ _ ((D.s.atP p).ιF (x : D.host.F))⁻¹ *
            (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p) * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p)⁻¹) := by ring
        _ = _ := by rw [h4, mul_one]
    rw [e, ← hO]
    refine (Z.M p).L.O.mul_mem o.2 ?_
    rw [hO]
    exact PI.CntNotIntW.algMap_mem_O D p _ hinvx
  exact unit_of_mem hδ (memF_of p _ hin) (memF_of p _ hinv)

end Fin

section Main

variable {D : D7}

theorem cval_unit_fin (Z : LocDat D) :
    {p : PlF D | ¬ ∃ u : (𝒪[(D.s.atP p).Fp])ˣ, ((u : 𝒪[(D.s.atP p).Fp]) : (D.s.atP p).Fp) = cval Z p}.Finite := by
  refine ((delta_unit D Z).union (isUnit_unitAt D)).subset ?_
  intro p hp
  simp only [Set.mem_setOf_eq, Set.mem_union] at hp ⊢
  by_contra h
  push_neg at h
  obtain ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ := h
  refine hp ⟨u * v, ?_⟩
  rw [cval, ← hu, ← hv, Units.val_mul, MulMemClass.coe_mul]

theorem exists_gen (D : D7) (Z : LocDat D) (N N' : ℕ) (hN : 0 < N) (hN' : 0 < N')
    (F00 : LFlag (D.sp.Y 0) D.R.rS (N : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (N' : D.host.E))
    (FP : ∀ p : PlF D, Formalism.MainNotions.S.LocNG.FPair (locH Z p) D.R.rS)
    (hFP : ∀ p, AtBase Z p F00 F'0 N N' (FP p) ∧ (FP p).RelG (Formalism.MainNotions.S.LocNG.theta (Z.M p))) :
    ∃ G : GFrames (placesOf Z) D.R.rS D.R.k, Nonempty (GCoord Z F00 F'0 FP G) := by
  obtain ⟨y, hy⟩ := Formalism.L2.SG.Pf.Cnt.R1.dual_of_flag D hN F00.fl
  obtain ⟨y', hy'⟩ := Formalism.L2.SG.Pf.Cnt.R1.dual_of_flag D hN' F'0.fl
  have hloc : ∀ p, ∃ S : Frames (Z.M p).L D.R.rS D.R.k,
      S.Hm = Matrix.of (fun i j => (locH Z p).h (bL D p i) (bL D p j)) ∧
      S.es = (fun j : Fin D.R.rS => (bL D p).equivFun
        (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cval Z p ^ (D.R.rS - (j : ℕ))) • baseChange₂ D p (y j))) ∧
      S.es' = (fun j : Fin D.R.rS => (bL D p).equivFun
        (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cval Z p ^ (D.R.rS - (j : ℕ))) • baseChange₂ D p (y' j))) ∧
      S.gg = (Z.M p).split.isSome ∧ ∃ c : WCoord (FP p) S, c.e = (bL D p).equivFun := by
    intro p
    obtain ⟨⟨hA, hB, -, -⟩, hR⟩ := hFP p
    refine loc_ex (Z.agree p).1 (locH Z p) D.R.rS D.R.k (FP p) hR (bL D p) _ _ ?_ ?_ ?_ ?_
    · intro a j; rw [hA]; exact loc_dual Z p F00.fl y hy a j
    · intro a j; rw [hB]; exact loc_dual Z p F'0.fl y' hy' a j
    · intro i j; exact loc_iso Z p _ _ F00.fl y hy i j
    · intro i j; exact loc_iso Z p _ _ F'0.fl y' hy' i j
  choose S hS using hloc
  choose W hW using fun p => (hS p).2.2.2.2
  have heq : ∀ p, (bL D p).equivFun = eL D p := fun p => Module.Basis.equivFun_ofEquivFun _
  refine ⟨
    { Hm := HmG D
      f := fun a => eG D (frame F00 a)
      f' := fun a => eG D (frame F'0 a)
      es := fun a => eG D (y a)
      es' := fun a => eG D (y' a)
      c := fun p => Units.mk0 (cval Z p) (cval_ne Z p)
      S := S
      Hm_eq := fun p => by rw [(hS p).1, gram_bL]; rfl
      f_eq := ?_
      f'_eq := ?_
      es_eq := ?_
      es'_eq := ?_
      c_unit := ?_
      gg_fin := ?_ }, ⟨
    { e := eG D
      h_eq := h_eqG
      f_eq := fun a => rfl
      f'_eq := fun a => rfl
      c := W
      compat := ?_
      c_eq := ?_ }⟩⟩
  · intro p a
    obtain ⟨⟨hA, -, -, -⟩, -⟩ := hFP p
    rw [(W p).f_eq, hW p, hA, heq, ← eL_bcP Z]
    show algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cval Z p ^ (D.R.rS - (a : ℕ))) •
      eL D p (frFac Z.δ p a • baseChange₂ D p (frame F00 a)) = eL D p (baseChange₂ D p (frame F00 a))
    rw [LinearEquiv.map_smul, smul_smul, frFac_mul, one_smul]
  · intro p a
    obtain ⟨⟨-, hB, -, -⟩, -⟩ := hFP p
    rw [(W p).f'_eq, hW p, hB, heq, ← eL_bcP Z]
    show algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cval Z p ^ (D.R.rS - (a : ℕ))) •
      eL D p (frFac Z.δ p a • baseChange₂ D p (frame F'0 a)) = eL D p (baseChange₂ D p (frame F'0 a))
    rw [LinearEquiv.map_smul, smul_smul, frFac_mul, one_smul]
  · intro p a
    rw [(hS p).2.1]
    show (bL D p).equivFun _ = _
    rw [heq, LinearEquiv.map_smul, eL_bcP Z]
    rfl
  · intro p a
    rw [(hS p).2.2.1]
    show (bL D p).equivFun _ = _
    rw [heq, LinearEquiv.map_smul, eL_bcP Z]
    rfl
  · exact cval_unit_fin Z
  · refine (split_fin D).subset ?_
    intro p hp
    simp only [Set.mem_setOf_eq] at hp ⊢
    rw [← split_isSome Z p, ← (hS p).2.2.2.1]
    exact hp
  · intro p x
    have h1 := congrArg (fun e : Vp D p ≃ₗ[(D.s.atP p).Ep] (Fin (D.R.k + 2 * D.R.rS + 1) → (D.s.atP p).Ep) =>
      e (baseChange₂ D p x)) ((hW p).trans (heq p))
    exact h1.trans (eL_bcP Z p x)
  · intro p
    show algebraMap _ _ (cval Z p) = _
    rw [cval_E]

theorem exists_global_coords : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∃ G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k, Nonempty (GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G) := by
  intro D X Y u u' hst w F00 F'0 FP _ _ hFP
  have hN : 0 < Tu D u := by have := hst.2.2.2.1; omega
  have hN' : 0 < Tu D u' := by have := hst.2.2.2.2.1; omega
  exact exists_gen D _ _ _ hN hN' F00 F'0 FP hFP

end Main

end GlobalTheory.HL.GCoordEx
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGlobalCoordinatesRationalFlagPairStatement
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_global_coordinates_rational_flagPair : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∃ G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k, Nonempty (GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G) := by
  first | exact @GlobalTheory.HL.GCoordEx.exists_global_coords | exact GlobalTheory.HL.GCoordEx.exists_global_coords | (intros; apply GlobalTheory.HL.GCoordEx.exists_global_coords <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamilyGroupSumFactorsRowWeightAmplitudeProof
noncomputable section

open scoped Classical Pointwise
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic
  Formalism.L2.SG.FamDefs Formalism.MainNotions.S.LocNG GlobalTheory.HL GlobalTheory.LocOver GlobalTheory.SnFam

namespace GlobalTheory.FamilyNormRational

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem toPts_inj' {K : Type} [Zero K] {i : ℕ} (p q : Point K (i + 1)) (h : toPts p = toPts q) : p = q := by
  have hb : p.1.map Prod.snd = q.1.map Prod.snd := congrArg (fun x => x.1.blocks) h
  have hl : p.1.length = q.1.length := by simpa using congrArg List.length hb
  have hv : ∀ k (hk : k < p.1.length) (hk' : k < q.1.length), (p.1[k]).1 = (q.1[k]).1 := by
    intro k hk hk'
    have key := congrArg (fun x : (Σ c : Composition (i + 1), (Fin c.length → K)) =>
      if hk : k < x.1.length then x.2 ⟨k, hk⟩ else 0) h
    have e1 : k < (toPts p).1.length := by simpa [toPts, Composition.length] using hk
    have e2 : k < (toPts q).1.length := by simpa [toPts, Composition.length] using hk'
    simp only [dif_pos e1, dif_pos e2] at key
    simpa [toPts] using key
  apply Subtype.ext
  apply List.ext_getElem hl
  intro k hk hk'
  have hs := congrArg (fun l => l[k]?) hb
  simp only [List.getElem?_map, List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hk', Option.map_some,
    Option.some.injEq] at hs
  exact Prod.ext (hv k hk hk') hs

theorem one_mem_nRat {D : D7} {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) : (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) ∈ NRat F :=
  ⟨one_mem _, fun j x _ => by simp, fun x _ => by simp⟩

theorem squaredGroupSum_classDoubleCoset_eq_rowWeight : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k →
    ConcTie X Y → ∀ ν, Formalism.L2.SG.RealObj.NuQPin X u u' ν → ∀ s : X.B.I.Ginf → NNReal, (∀ γ, 0 < s γ) →
    (∀ w : Point D.host.E (D.R.rS + 1), (∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w g) →
      (s (Formalism.L2.SG.RealObj.gamW X u u' w) : ℝ) = (((X.B.g : ℝ) ^ (D.R.f * Fintype.card (Formalism.L2.SG.RealObj.FreeE w)))⁻¹)) →
    ∀ (K : Type) (S : Prop → Prop) (TS : Set (TauC Y u u')) (cls : TauC Y u u' → K), FamQ Y u u' S TS cls →
    ∀ γ : PN.Pts D.host.E D.R.rS, HasPt Y u u' TS γ →
    ∀ Fm : LocFam (zOf Y) K (NuC D), FamTie TS cls (nmlOf Y u u') γ Fm →
    ∀ (c : K) (n : NuC D), a2F Y u u' TS cls (sc s ν) c γ n = a2W Fm.toL (ampQ S Fm.toL) c n := by
  intro D X Y u u' hSt hk hCT ν hνP s hs0 hsw K S TS cls hFQ γ hγ Fm hFT c n
  obtain ⟨w, F00, F'0, F'1, hw, -, -, -, hZ, hbase, hOm, hgood, -, -, -, -, hdat, -, -⟩ := hFT
  have hdc := hdat c n
  have hL : Fm.toL.dat c n = Fm.dat c n := rfl
  show ‖grpF Y u u' TS cls c γ n‖ ^ 2 / J2of Y u u' (sc s ν) γ = a2W Fm.toL (ampQ S Fm.toL) c n
  unfold a2W
  rw [hL]
  rcases hd : Fm.dat c n with _ | d
  · rw [hd] at hdc
    have h0 : grpF Y u u' TS cls c γ n = 0 := by
      unfold grpF
      have h0 : ∀ t, (TS ∩ {t | cls t = c ∧ ptPN t = γ ∧ nmlOf Y u u' t = n}).indicator (Y.tO u u').vec t = 0 := by
        intro t; apply Set.indicator_of_notMem; rintro ⟨h1, h2, h3, h4⟩; exact hdc ⟨t, h1, h2, h3, h4⟩
      simp [h0]
    simp [h0]
  · rw [hd] at hdc
    obtain ⟨⟨t0, ht0, hc0, hp0, hn0⟩, hall⟩ := hdc
    obtain ⟨hOv, hrw⟩ := hall t0 ht0 hc0 hp0 hn0
    obtain ⟨hTS, hCR, hRow⟩ := hFQ
    obtain ⟨t1, ht1, hv1, hp1⟩ := hγ
    have hGTS : ∀ t ∈ TS, t.G ≠ 0 := by
      intro t ht h0
      rw [hTS] at ht
      apply ht.1
      show Formalism.L2.SG.TermOp.Gt t = 0
      unfold Formalism.L2.SG.TermOp.Gt
      rw [if_pos h0]
    have hG1 := hGTS t1 ht1
    have hG0 := hGTS t0 ht0
    have hrel1 : t1.relevant := (GlobalTheory.T.nonGeneric_family_classes_determine_rows D X Y u u' hCT).2.2 t1 hv1
    obtain ⟨w1, hw1, hat1, -⟩ := GlobalTheory.T.terms_at_point_of_relevant_term_relevant_finite D X Y u u' t1 hG1 hrel1
    have hw1w : w1 = w := toPts_inj' _ _ (hw1.trans (hp1.trans hw.symm))
    subst hw1w
    have hatOf : ∀ t : TauC Y u u', ptPN t = γ → t.relevant ∧ t.toTerm.atPt w1 ∧ Formalism.L2.SG.PairVal.ptOf t.toTerm = w1 := by
      intro t ht
      obtain ⟨hr, hg, hcell⟩ := hat1 t (ht.trans hp1.symm)
      refine ⟨hr, ⟨(Quot.out t.toTerm.cls).1, ⟨(Quot.out t.toTerm.cls).2, Quot.out_eq _⟩, hg, hcell⟩, ?_⟩
      exact toPts_inj' _ _ (ht.trans hw.symm)
    obtain ⟨hrel0, hat0, hpt0⟩ := hatOf t0 hp0
    obtain ⟨-, hat1', hpt1⟩ := hatOf t1 hp1
    have hAtB : ∀ p, AtBase (zOf Y) p F00 F'0 (Tu D u) (Tu D u') (Fm.FP p) := fun p =>
      ⟨(hbase p).1, (hbase p).2.1, (hbase p).2.2.1, (hbase p).2.2.2⟩
    have hGv : Gval F00 F'0 ≠ 0 := by
      obtain ⟨-, hg0, hcell0⟩ := hat1 t0 (hp0.trans hp1.symm)
      have hcell00 : IsInCell (ZhatOM (ZhatL F00 F'0)) w1 :=
        ⟨1, 1, fun i j => ⟨fun h => Matrix.one_apply_ne (ne_of_lt h), fun h => h ▸ Matrix.one_apply_eq i⟩,
          fun i j => ⟨fun h => Matrix.one_apply_ne (ne_of_gt h), fun h => h ▸ Matrix.one_apply_eq i⟩,
          by rw [hZ, Matrix.one_mul, Matrix.mul_one]⟩
      have e1 := Formalism.L2.SG.WConst.gPoint_eq_gval F00 F'0 w1 hcell00
      have e2 := Formalism.L2.SG.WConst.gPoint_eq_gval (T := Tu D u) (T' := Tu D u') (lf D (X.Fu u)) (Quot.out t0.toTerm.cls).1
        w1 hcell0
      change Gpt (D.mem u).A.T (D.mem u').A.T w1 = _ at e2
      rw [← e1, e2]
      exact hg0
    have hBase : ∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (Fm.FP p) ∧
        (Fm.FP p).RelG (LocNG.theta (Y.M p)) := fun p =>
      ⟨hAtB p, (GlobalTheory.T.localisedBaseFrames_relevantPair D (zOf Y) u u' w1 F00 F'0 hZ hGv p).2 _ (hAtB p)⟩
    obtain ⟨G, ⟨cc⟩⟩ := GlobalTheory.T.exists_global_coordinates_rational_flagPair D X Y u u' hSt w1 F00 F'0 Fm.FP hZ hGv hBase
    obtain ⟨ρ, U, U', hmv⟩ := GlobalTheory.T.term_moves_to_baseFrames_up_to_unitriangular D X Y u u' hSt w1 F00 F'0 Fm.FP hZ hGv hBase t0 hat0
    have hcore := GlobalTheory.T.row_doubleCoset_sum_norm_sq_bound D X Y u u' hSt hk w1 F00 F'0 Fm.FP hZ hGv hBase G cc ν hνP t0 ρ U U' hmv hrel0 hpt0 S
    have hamp := GlobalTheory.T.globalAmplitude_eq_localAmplitudes D X Y u u' hSt hk w1 F00 F'0 Fm.FP hZ hGv hBase G cc t0 ρ U U' hmv Fm.R Fm.P Fm.Om
      (fun p => (d p).1) hgood hOm (fun p => hOv p.1 p.2) S
    have hset : (TS ∩ {t | cls t = c ∧ ptPN t = γ ∧ nmlOf Y u u' t = n}) =
        {t : TauC Y u u' | (Y.tO u u').rowOf t = (Y.tO u u').rowOf t0 ∧ nmlOf Y u u' t = nmlOf Y u u' t0 ∧
          S (¬ t.generic)} := by
      ext t
      constructor
      · rintro ⟨htS, hct, -, hnt⟩
        refine ⟨hRow t htS t0 ht0 (hct.trans hc0.symm), hnt.trans hn0.symm, ?_⟩
        have h2 := htS
        rw [hTS] at h2
        exact h2.2
      · rintro ⟨hr, hnm, hS⟩
        obtain ⟨nn, mm, hnn, hmm, hlin⟩ := (GlobalTheory.T.doubleCoset_eq_iff_isometry_unipotent_translate D X Y u u' hSt t0 t).1 hnm
        obtain ⟨-, hGeq, hpteq, -, -⟩ := GlobalTheory.T.flagTerm_invariants_const_on_rationalDoubleCoset D X Y u u' hSt t0 t nn mm hrel0 hG0 ⟨hnn, hmm, hlin⟩
        have htS : t ∈ TS := by
          rw [hTS]
          refine ⟨?_, hS⟩
          show Formalism.L2.SG.TermOp.Gt t ≠ 0
          unfold Formalism.L2.SG.TermOp.Gt
          rw [if_neg (hGeq ▸ hG0)]
          exact one_ne_zero
        refine ⟨htS, ((hCR t htS t0 ht0 hnm).2 hr).trans hc0, ?_, hnm.trans hn0⟩
        show toPts (Formalism.L2.SG.PairVal.ptOf t.toTerm) = γ
        rw [hpteq]
        exact hp0
    have hrep : ∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w1 g :=
      (GlobalTheory.T.orbital_integrals_terms_one_doubleCoset D X Y u u' hSt ν hνP t0 hrel0 hG0 w1 hpt0.symm).1
    have hJ : J2of Y u u' (sc s ν) γ = (s (Formalism.L2.SG.RealObj.gamW X u u' w1) : ℝ) ^ 2 *
        ‖Formalism.L2.SG.PackageTie.hsEmb (Jw Y u u' ν w1)‖ ^ 2 := by
      unfold J2of
      have hex : ∃ w' : Point D.host.E (D.R.rS + 1), toPts w' = γ ∧ ∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w' g :=
        ⟨w1, hw, hrep⟩
      rw [dif_pos hex]
      have hcw : hex.choose = w1 := toPts_inj' _ _ (hex.choose_spec.1.trans hw.symm)
      rw [hcw, Jw_sc, map_smul, norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have hJne : ‖Formalism.L2.SG.PackageTie.hsEmb (Jw Y u u' ν w1)‖ ≠ 0 := by
      intro h0
      obtain ⟨ρ1, U1, U1', hmv1⟩ := GlobalTheory.T.term_moves_to_baseFrames_up_to_unitriangular D X Y u u' hSt w1 F00 F'0 Fm.FP hZ hGv hBase t1 hat1'
      obtain ⟨T, hT, hamp1⟩ := GlobalTheory.T.rowTerm_amplitude_eq_mass_mul_phase D X Y u u' hSt hk w1 F00 F'0 Fm.FP hZ hGv hBase G cc ν hνP t1 ρ1 U1 U1'
        hmv1 hrel1 hpt1
      have he := hamp1 t1 1 1 rfl ⟨one_mem_nRat _, one_mem_nRat _, by simp⟩
      have hT0 : Formalism.L2.SG.PackageTie.hsEmb T = 0 := norm_eq_zero.1 (hT.trans h0)
      apply hv1
      show Formalism.L2.SG.TermOp.vec (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') t1 = 0
      unfold Formalism.L2.SG.TermOp.vec
      rw [he, map_smul, hT0, smul_zero, smul_zero]
      ext q
      simp
    have hgi := hsw w1 hrep
    have hspos : (0 : ℝ) < s (Formalism.L2.SG.RealObj.gamW X u u' w1) := by exact_mod_cast hs0 _
    have hampeq : ‖G.amp (G.datOf (cc.lat ρ t0.lam)) (fun Γ => S (¬ G.Gen (G.datOf (cc.lat ρ t0.lam)) Γ))‖ =
        ‖ampQ S Fm.toL d‖ := by
      rw [hamp]; unfold ampQ
      congr 1
      refine Finset.sum_congr rfl (fun A _ => Finset.prod_congr rfl (fun p _ => ?_))
      split_ifs <;> first | rfl | (exfalso; tauto)
    have hgrp : grpF Y u u' TS cls c γ n = ∑' t : TauC Y u u', {t : TauC Y u u' | (Y.tO u u').rowOf t =
        (Y.tO u u').rowOf t0 ∧ nmlOf Y u u' t = nmlOf Y u u' t0 ∧ S (¬ t.generic)}.indicator (Y.tO u u').vec t := by
      unfold grpF; rw [hset]
    rw [hgrp, hcore, hJ, hampeq]
    show _ = Fm.rw c * ‖ampQ S Fm.toL d‖ ^ 2
    rw [hrw, ← hgi]
    have hJp : 0 < ‖Formalism.L2.SG.PackageTie.hsEmb (Jw Y u u' ν w1)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hJne)
    field_simp

theorem familyGroupSumFactorsRowWeightAmplitude : GlobalTheory.SnFam.FamilyGroupSumFactorsWeightAmplitude := by
  intro Cg cb Cw cT CT C0
  refine ⟨0, le_rfl, 0, 0, fun C' Cl _ _ D large₂ X Y u u' hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hBk ν hν => ?_⟩
  have hk := four_rank_add_seven_le_k hc
  obtain ⟨-, hSt, hCT⟩ := hc
  obtain ⟨s, hs1, hs0, hsle, hsw⟩ := GlobalTheory.T.exists_scale_normalised_localReading D X u u'
  refine ⟨s, hs1, hs0, fun γ => ?_, fun K S TS cls hFQ γ hγ Fm hFT c n =>
    squaredGroupSum_classDoubleCoset_eq_rowWeight D X Y u u' hSt hk hCT ν hν.2 s hs0 hsw K S TS cls hFQ γ hγ Fm hFT c n⟩
  have h1 : (s γ : ℝ) ≤ 1 := by exact_mod_cast hsle γ
  have h0 : (0 : ℝ) ≤ s γ := (s γ).2
  simp only [zero_mul, Real.rpow_zero]
  nlinarith

end GlobalTheory.FamilyNormRational
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamilyGroupSumFactorsRowWeightAmplitudeProofStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.familyGroupSumFactorsRowWeightAmplitude_proof : GlobalTheory.SnFam.FamilyGroupSumFactorsWeightAmplitude := by
  first | exact @GlobalTheory.FamilyNormRational.familyGroupSumFactorsRowWeightAmplitude | exact GlobalTheory.FamilyNormRational.familyGroupSumFactorsRowWeightAmplitude | (intros; apply GlobalTheory.FamilyNormRational.familyGroupSumFactorsRowWeightAmplitude <;> assumption)
end
