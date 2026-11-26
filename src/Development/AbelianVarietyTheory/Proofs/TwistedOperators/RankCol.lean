module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridRowLevelZeroInfUnitaryEqDatumLevel
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatIntegrandFlippedTensorLocallyConstantCompact
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeilDatumAnisotropicKernelPair
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GivenLevelInner

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RankCol
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FlipTop

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem rank_col (G : GridData L sc) {j : ℕ} (hj : j ≤ D.R.m) : (G.V (.grid 0 j)).rank = D.R.r + j * D.R.t := by
  change (columnBlock L j).sp.rank = _
  rcases hj.eq_or_lt with rfl | hk
  · rw [colY_m]; exact D.sp.X'_rank
  · rw [colY_lt L hk]; exact Comparison₂.rank_Yc hk.le


open Classical in
def topPl (L : LevCh D T) (t : T) : Finset (Pl D.host.E) := L.Pg ∪ L.Q t


open Classical in
def topFn {G : GridData L sc} (B : Frames G) (t : T) (e : AE D) (j : ℕ) (ha : (G.V (.grid 0 j)).rank = D.R.r + j * D.R.t)
    (hb : (G.V (.grid 0 (j + 1))).rank = D.R.r + (j + 1) * D.R.t)
    (x : Mx D (G.V (.grid 0 (j + 1))).rank (G.V (.grid 0 j)).rank) : ℂ :=
  if IsHalf e x ∧ IsIntM (Comparison₂.fr (B.β 0 (j + 1)) (B.β 0 j) (x.map (toEAf D))) then
    ∏ w ∈ topPl L t, stepFn L t w j
      (((Comparison₂.fr (B.β 0 (j + 1)) (B.β 0 j) (x.map (toEAf D))).map (cpt (D := D) w)).submatrix (Comparison₂.ixOf G t w hb)
        (Comparison₂.ixOf G t w ha))
  else 0

end GlobalTheory.FlipTop

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAlgebraicStdCharHalfSymplecticRealPartZeroStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAlgebraicStdCharHalfSymplecticRealPartZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PsiFinAlgebraic

theorem exists_pow_psi_fin_eq_one {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ)
    (y : Af F) : ∃ M : ℕ, 0 < M ∧ ψ (pairA F 0 y) ^ M = 1 := by
  obtain ⟨N, hN, h⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F {c | ψ (pairA F 0 c) = 1}
    (GlobalTheory.FinTranslate.eventually_fin_eq_one hψ)
  obtain ⟨m, hm, hy⟩ := GlobalTheory.UnRep.SmallMat.exists_nsmul_integral y
  refine ⟨N * m, Nat.mul_pos hN (Nat.pos_of_ne_zero hm), ?_⟩
  have h1 : ψ (pairA F 0 (N • m • y)) = 1 := h _ hy
  have e : pairA F 0 (N • m • y) = (N * m) • pairA F 0 y :=
    Prod.ext (smul_zero (N * m)).symm (mul_smul N m y).symm
  rwa [e, AddChar.map_nsmul_eq_pow] at h1

theorem isAlgebraic_psi_fin {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ)
    (y : Af F) : IsAlgebraic ℚ (ψ (pairA F 0 y)) := by
  obtain ⟨M, hM, h⟩ := exists_pow_psi_fin_eq_one hψ y
  refine IsAlgebraic.of_pow hM ?_
  rw [h]
  exact isAlgebraic_one

theorem isAlgebraic_psi_symplOH : ∀ {D : D7} {ψ : AddChar (AF D.host.F) ℂ}, IsStdChar D ψ (-1) → ∀ (S T : HSp D) (u v : WO S T),
    u.map (infPart D) = 0 → v.map (infPart D) = 0 → IsAlgebraic ℚ (ψ (symplOH S T u v)) := by
  intro D ψ hψ S T u v hu _
  have e : pairA D.host.F 0 (sndA D.host.F (symplOH S T u v)) = symplOH S T u v :=
    Prod.ext (GlobalTheory.WeilVacMove.fst_symplOH S T u v (Or.inl hu)).symm rfl
  rw [← e]
  exact isAlgebraic_psi_fin hψ.1 _

end GlobalTheory.PsiFinAlgebraic
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAlgebraic_stdChar_halfSymplectic_realPart_zero : ∀ {D : D7} {ψ : AddChar (AF D.host.F) ℂ}, IsStdChar D ψ (-1) → ∀ (S T : HSp D) (u v : WO S T),
    u.map (infPart D) = 0 → v.map (infPart D) = 0 → IsAlgebraic ℚ (ψ (symplOH S T u v)) := by
  first | exact @GlobalTheory.PsiFinAlgebraic.isAlgebraic_psi_symplOH | exact GlobalTheory.PsiFinAlgebraic.isAlgebraic_psi_symplOH | (intros; apply GlobalTheory.PsiFinAlgebraic.isAlgebraic_psi_symplOH <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TopOrthEmb
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR Formalism.IndefR.Links GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.ChiGrid GlobalTheory.Unf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowChain

open GlobalTheory.FunObj GlobalTheory.RowUnf

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (Wl : G.Weil) (t : T) {M : Vol G}

abbrev pLine (D : D7) : HSp D := Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral 1

theorem pLine_gram : (pLine D).gram = antiDiagonalSignGramMatrix 1 (1 : D.host.E) := by
  refine Matrix.ext fun i j => ?_
  have e : ∀ a b : Fin 1, (Examples₂.stdSpace (E := D.host.E) Examples₂.star_isIntegral 1 (fun _ => false) 1 0).gram a b = 1 :=
    fun a b => by rw [Examples₂.stdSpace_gram_apply, Subsingleton.elim a b]; simp [Examples₂.sgn]
  exact (e i j).trans (by simp [antiDiagonalSignGramMatrix]; exact ⟨Fin.val_eq_zero i, Fin.val_eq_zero j⟩)

def topOrth : OrthDec (G.V (.top D.R.m)) (G.V (.grid D.R.m D.R.m)) (pLine D) where
  iA := frameMat _ _ G.sp.topDec.ι
  iB := G.sp.topDec.a
  isoA := frameMat_isom G.sp.topDec
  isoB := G.sp.topDec.gram.trans pLine_gram.symm
  orth := perp_sub' G.sp.topDec id
  rank_add := G.sp.topDec.rank

def topOrthAt {n : ℕ} (h : D.R.m = n) : OrthDec (G.V (.top n)) (G.V (.grid D.R.m D.R.m)) (pLine D) :=
  Eq.rec (motive := fun k _ => OrthDec (G.V (.top k)) (G.V (.grid D.R.m D.R.m)) (pLine D)) (topOrth G) h

def topEmb {n : ℕ} (h : D.R.m = n) : GA D (G.V (.grid D.R.m D.R.m)) → GA D (G.V (.top n)) :=
  Eq.rec (motive := fun k _ => GA D (G.V (.grid D.R.m D.R.m)) → GA D (G.V (.top k))) (stabilizerEmbedding G.sp.topDec) h

def lastTau : Matrix (Fin (GlobalTheory.SeeSaw.Model.nLine D).rank) (Fin (pLine D).rank) D.host.E := Matrix.of fun _ _ => -D.host.xi0

variable {G t}

def lastDat (hM : M.Is t) (j : ℕ) (hj : j + 2 * 0 + 2 = D.R.m) (vN : VolN (besDecAt G j 0 hj)) (g : GA D (G.V (.grid D.R.m j)))
    (Φ₁ : WO (G.V (.grid D.R.m j)) (G.V (.grid D.R.m (j + 1))) → ℂ)
    (Φ₂ : WO (G.V (.grid D.R.m (j + 1))) (G.V (.grid D.R.m D.R.m)) → ℂ) :
    WO (G.V (.top j)) (G.V (.top (j + 1))) → WO (G.V (.top (j + 1))) (G.V (.top (j + 1 + 1))) → ℂ :=
  GlobalTheory.FinPl.lastBi (besAt G hM j 0 hj vN).o (topOrthAt G (show D.R.m = j + 1 + 1 by omega)) lastTau
    (flatBF (lastAt G Wl t hM j hj vN).s ((lastAt G Wl t hM j hj vN).s.om (g, 1) Φ₁))
    (fun w => Φ₂ ((rowJac G (j + 1) (by omega) 0 (by omega)).ext0 _ w))

end GlobalTheory.RowChain

namespace GlobalTheory.RowChain

open GlobalTheory.FunObj GlobalTheory.RowUnf

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (Wl : G.Weil) (t : T) {M : Vol G}

theorem topOrth_emb (h : GA D (G.V (.grid D.R.m D.R.m))) : (topOrth G).emb (h, 1) = stabilizerEmbedding G.sp.topDec h :=
  (embRel_iff G.sp.topDec h _).1 ((topOrth G).embRel_left G.sp.topDec.ι rfl h)

variable {G t}

noncomputable def colPer (hM : M.Is t) : (σ j : ℕ) → (hj : j + 2 * σ + 2 = D.R.m) → (vN : VolN (besDecAt G j σ hj)) →
    (chainFrom G Wl t hM σ j hj vN).Data → Fn G (.grid D.R.m D.R.m) → (GA D (G.V (.top j)) → ℂ) →
    GA D (G.V (.grid D.R.m j)) → (chainFrom G Wl t hM σ j hj vN).Var → ℂ
  | 0, j, hj, vN, Φ, F, φ, g, _ =>
    ∫ h' in M.fd (.grid D.R.m D.R.m), F h' * GlobalTheory.SeeSaw.biLift (Wl.om (.top t j)) (Wl.om (.top t (j + 1)))
      (volAt hM (.top j) (by show j ≤ D.R.m; omega)) (volAt hM (.top (j + 1)) (by show j + 1 ≤ D.R.m; omega)) φ
      (lastDat Wl hM j hj vN g Φ.1 Φ.2) (topEmb G (show D.R.m = j + 1 + 1 by omega) h') ∂M.ν (.grid D.R.m D.R.m)
  | σ + 1, j, hj, vN, Φ, F, φ, g, h =>
    colPer hM σ (j + 1 + 1) (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some Φ.2.2 F
      (GlobalTheory.SeeSaw.biLift (Wl.om (.top t j)) (Wl.om (.top t (j + 1)))
        (volAt hM (.top j) (by show j ≤ D.R.m; omega)) (volAt hM (.top (j + 1)) (by show j + 1 ≤ D.R.m; omega)) φ
        (contr (linkAt hM j σ hj vN (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some) (G.V (.top (j + 1)))
          ((GlobalTheory.Unf.Inhab.nonempty_volM D _ _).some)
          (flatBF (B := besAt G hM j (σ + 1) hj vN) (J := jacAt G hM (j + 1) (σ + 1) (by omega)) (stepAt G Wl t hM j (by omega) (besDecAt G j (σ + 1) hj) (rowJac G (j + 1) (by omega) (σ + 1) (by omega)))
            ((stepAt G Wl t hM j (by omega) (besDecAt G j (σ + 1) hj) (rowJac G (j + 1) (by omega) (σ + 1) (by omega))).om
              (g, h.1) Φ.1))
          (flatFB (J := jacAt G hM (j + 1) (σ + 1) (by omega))
            (B := besAt G hM (j + 1 + 1) σ (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some) (stepAt G Wl t hM (j + 1) (by omega) (rowJac G (j + 1) (by omega) (σ + 1) (by omega))
              (besDecAt G (j + 1 + 1) σ (by omega)))
            ((stepAt G Wl t hM (j + 1) (by omega) (rowJac G (j + 1) (by omega) (σ + 1) (by omega))
              (besDecAt G (j + 1 + 1) σ (by omega))).om (h.1, h.2.1) Φ.2.1))))
      h.2.1 h.2.2

end GlobalTheory.RowChain
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetUnitaryConjAtPlaceEqDetLatticeBasisComponent
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetUnitaryConjAtPlaceEqDetLatticeBasisComponent
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

noncomputable section

namespace GlobalTheory.TopLevelInv

theorem det_val_conj_inv {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] (b Y : GL n R) :
    (b⁻¹ * Y * b⁻¹⁻¹).val.det = Y.val.det := by
  rw [Units.val_mul, Units.val_mul, det_mul, det_mul, mul_right_comm, ← det_mul, inv_inv, Units.inv_mul, det_one, one_mul]

theorem det_val_reGL {k : Type} [Field k] {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (e : a ≃ b)
    (g : GL a k) : (GlobalTheory.StepData.reGL e g).val.det = g.val.det :=
  det_reindex_self e g.val

theorem val_loc {D : D7} (w : Pl D.host.E) {n : ℕ} (g : GL (Fin n) (Lev.EAf D)) :
    (GlobalTheory.StdFrames.loc w g).val = g.val.map (GlobalTheory.StdFrames.cpt w) := rfl

theorem val_finG {D : D7} (V : HSp D) (k : GfC V) :
    (finG V k).val = (Formalism.L2.Theta.mt V (k : GA D V)).map (toEAf D) := rfl

theorem det_mt_conj {D : D7} (V : HSp D) (k u : GfC V) :
    (Formalism.L2.Theta.mt V ((u⁻¹ * k * u : GfC V) : GA D V)).det = (Formalism.L2.Theta.mt V (k : GA D V)).det := by
  have h1 : Formalism.L2.Theta.mt V ((u⁻¹ * k * u : GfC V) : GA D V)
      = (matHom V (u : GA D V))⁻¹.val * Formalism.L2.Theta.mt V (k : GA D V) * (matHom V (u : GA D V)).val := by
    simp [Formalism.L2.Theta.mt, map_mul, map_inv]
  rw [h1, det_mul, det_mul, mul_right_comm, ← det_mul, Units.inv_mul, det_one, one_mul]

theorem det_mt_conj_eq_gdet_kapAt : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) (t : T) (j : ℕ) (hj : j + 1 < D.R.m) (k u : FinPt G (.top (j + 1))) (w : Pl D.host.E), ((Formalism.L2.Theta.mt (G.V (.top (j + 1))) ((u⁻¹ * k * u : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))).map fun z => GlobalTheory.StdFrames.cpt w (toEAf D z)).det = ((gdet (kapAt S t j hj k w) : (Kw w)ˣ) : Kw w) := by
  intro D T L sc G W U S t j hj k u w
  have hfun : (fun z => GlobalTheory.StdFrames.cpt w (toEAf D z)) = ⇑((GlobalTheory.StdFrames.cpt w).comp (toEAf D)) := rfl
  rw [hfun, ← RingHom.mapMatrix_apply, ← RingHom.map_det, det_mt_conj, RingHom.comp_apply]
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  rw [kapAt, GlobalTheory.FunObj.inBasis, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply, det_val_reGL, val_loc, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
    det_val_conj_inv, val_finG, ← RingHom.mapMatrix_apply, ← RingHom.map_det]

end GlobalTheory.TopLevelInv

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetUnitaryConjAtPlaceEqDetLatticeBasisComponentStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_unitaryConj_atPlace_eq_det_latticeBasisComponent : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) (t : T) (j : ℕ) (hj : j + 1 < D.R.m) (k u : FinPt G (.top (j + 1))) (w : Pl D.host.E), ((Formalism.L2.Theta.mt (G.V (.top (j + 1))) ((u⁻¹ * k * u : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))).map fun z => GlobalTheory.StdFrames.cpt w (toEAf D z)).det = ((gdet (kapAt S t j hj k w) : (Kw w)ˣ) : Kw w) := by
  first | exact @GlobalTheory.TopLevelInv.det_mt_conj_eq_gdet_kapAt | exact GlobalTheory.TopLevelInv.det_mt_conj_eq_gdet_kapAt | (intros; apply GlobalTheory.TopLevelInv.det_mt_conj_eq_gdet_kapAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodAlgebraicFixedDegree
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section

namespace GlobalTheory.BotTransJet

open GlobalTheory.Grid (neg)

theorem conj_isAlgebraic {z : ℂ} (h : IsAlgebraic ℚ z) : IsAlgebraic ℚ (starRingEnd ℂ z) := by
  obtain ⟨p, hp, hz⟩ := h
  refine ⟨p, hp, ?_⟩
  have := Polynomial.aeval_algHom_apply ((starRingEnd ℂ).toRatAlgHom) z p
  rw [hz, map_zero] at this
  simpa using this

theorem applyAt0_isAlgebraic {D : D7} {N N' : ℕ} {P : MvPolynomial (GL3Theta.Idx D N N') ℂ} {G : TaylorLogMetric.VC D N N' → ℂ}
    (hP : ∀ α, IsAlgebraic ℚ (P.coeff α)) (hG : TaylorLogMetric.CoefIn D G TaylorLogMetric.Qbar) : IsAlgebraic ℚ (GL3Theta.applyAt0 D P G) := by
  rw [← mem_algebraicClosure_iff]
  unfold GL3Theta.applyAt0
  refine sum_mem fun α _ => mul_mem (mul_mem ((mem_algebraicClosure_iff).2 (hP α)) ?_) (hG α)
  exact prod_mem fun _ _ => natCast_mem _ _

theorem jet_negSp_heis {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (f : WO S T → ℂ) (u : WO S T) (k : FVar D T.rank S.rank →₀ ℕ) :
    pureTensorO ψ θ (negSp S) T (fun τ => -sS τ) sT BS BT (heisO ψ (negSp S) T u f) (MvPolynomial.monomial k 1) 0 =
      starRingEnd ℂ (pureTensorO ψ θ S T sS sT BS BT (heisO ψ S T u (fun w => starRingEnd ℂ (f w)))
        (MvPolynomial.monomial k 1) 0) := by
  rw [GlobalTheory.FockConj.pureTensorO_negSp_monomial ψ θ S T sS sT BS BT _ hψ hθ k 0]
  have h := ((GlobalTheory.CjNeg.theta_heis_neg D ψ hψ S T).2 u (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f)).2
  have hcc : GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f) = f := by
    funext x
    simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]
  rw [hcc] at h
  have key : (fun w => starRingEnd ℂ (heisO ψ (negSp S) T u f w)) = heisO ψ S T u (fun w => starRingEnd ℂ (f w)) := by
    have hcj : GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f = fun w => starRingEnd ℂ (f w) := rfl
    rw [h, ← hcj]
    funext w
    simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]
  rw [key]

theorem std_eq_colLat_one {D : D7} {n : ℕ} (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (hL : ∀ y, y ∈ L ↔ ∀ i, ∃ b : 𝓞 D.host.E, (b : D.host.E) = y i) :
    (L : Set (Fin n → D.host.E)) = (colLat (1 : GL (Fin n) D.host.E) : Set _) := by
  ext y
  simp only [SetLike.mem_coe, hL, lc_mem_colLat_one, Submodule.mem_one]

theorem even_bot {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW} (hX : IsBottomTri W i j X) : Even (A.rank * WW.rank) := by
  refine Even.mul_left ?_ _
  have h1 := hX.rank
  have h2 := hX.rank'
  have h3 := hX.is.rank
  have h4 := SqNum.ranks_exact D i j
  rw [← h3, h1, h2]
  refine ⟨SqNum.halfRank D i j - (D.R.m - (j.1 + 1)) / 2 - (D.R.m - j.1) / 2, ?_⟩
  omega

end GlobalTheory.BotTransJet

namespace GlobalTheory.BotTransJet

open GlobalTheory.Grid (neg)

end GlobalTheory.BotTransJet
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemFrameLatticeIffIntegralCoords
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section
namespace GlobalTheory.SplitVacAlg

variable {D : D7}

def frameLat (V : HSp D) : Submodule (𝓞 D.host.E) V.V := Submodule.span (𝓞 D.host.E) (Set.range V.frame)

theorem frameLat_isLattice (V : HSp D) : Submodule.IsFullLattice D.host.E (frameLat V) := by
  refine Submodule.IsFullLattice.mk
    (toIsLattice := Submodule.IsLattice.of_fg D.host.E (Submodule.fg_span (Set.finite_range _))) ?_
  rw [frameLat, Submodule.span_span_of_tower]
  exact V.frame.span_eq

theorem frameLat_unimod (V : HSp D) (hV : V.gram = 1) : Formalism.HermitianLatticesTheory.IsUnimodular V.hT (frameLat V) := by
  have key := (Formalism.E.hermDual (𝓞 D.host.E) D.host.E V.V (Fin V.rank) V.hT V.frame
    (IsFractionRing.injective (𝓞 D.host.E) D.host.E)
    (fun s => ⟨⟨star (s : D.host.E), s.2.map (starRingEnd D.host.E).toIntAlgHom⟩, rfl⟩)).2
    (1 : Matrix (Fin V.rank) (Fin V.rank) (𝓞 D.host.E)) (fun i j => by
      have := congrFun (congrFun hV i) j
      simp only [HSpace.gram] at this
      rw [this]
      by_cases h : i = j
      · subst h; simp
      · simp [h]) (by simp)
  exact key.2.2 (by simp)

def stdLatSp (V : HSp D) (hV : V.gram = 1) : HSp D :=
  { V with L0 := frameLat V, standardTuple_isLattice := (frameLat_isLattice V).toIsLattice, baseLattice_isUnimodular := frameLat_unimod V hV }

theorem mem_frameLattice_iff_integral_coords (V : HSp D) (hV : V.gram = 1) (y : Fin V.rank → D.host.E) :
    y ∈ L0c D (stdLatSp V hV) ↔ ∀ i, ∃ b : 𝓞 D.host.E, (b : D.host.E) = y i := by
  change ∑ i, y i • V.frame i ∈ Submodule.span (𝓞 D.host.E) (Set.range V.frame) ↔ _
  rw [V.frame.mem_span_iff_repr_mem (𝓞 D.host.E), Module.Basis.repr_sum_self]
  rfl

end GlobalTheory.SplitVacAlg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ActOOneResGCompl
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open Formalism.IndefR.Fin.LevelGroupLemmas (resG detAt resG_compl suppAt_resG isDetAt_detAt resG_one resG_mul actO_actO isHalf_actO)

noncomputable section

namespace GlobalTheory.TopLevelInv

abbrev conjPt {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) (j : ℕ) (k : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))) :=
  (((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem detAt_resG_eq {D : D7} {V : HSp D} {e : AE D} {ε : AF D.host.F} (he2 : e * e = e) (hc : e * cA D e = 0)
    (hε : IsIdempotentElem ε) (halg : algebraMap (AF D.host.F) (AE D) ε = e + cA D e) (g : GA D V) :
    detAt e V (resG V ε g) = detAt e V g := by
  apply Units.ext
  rw [Formalism.IndefR.Fin.LevelGroupLemmas.detAt_val he2, Formalism.IndefR.Fin.LevelGroupLemmas.detAt_val he2, Formalism.IndefR.Fin.LevelGroupLemmas.mt_resG V hε, halg]
  congr 1
  set I : Ideal (AE D) := Ideal.span {1 - e}
  have h1 : Ideal.Quotient.mk I e = 1 := by
    rw [← (Ideal.Quotient.mk I).map_one, Ideal.Quotient.eq]
    have : e - 1 = (-1) * (1 - e) := by ring
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  have h2 : Ideal.Quotient.mk I (cA D e) = 0 := by
    calc Ideal.Quotient.mk I (cA D e) = Ideal.Quotient.mk I (cA D e) * Ideal.Quotient.mk I e := by rw [h1, mul_one]
      _ = Ideal.Quotient.mk I (cA D e * e) := (map_mul _ _ _).symm
      _ = 0 := by rw [mul_comm, hc, map_zero]
  have key : (Formalism.IndefR.Fin.LevelGroupLemmas.resM (e + cA D e) (mt V g)).map (Ideal.Quotient.mk I) =
      (mt V g).map (Ideal.Quotient.mk I) := by
    ext i j
    simp only [Matrix.map_apply, Formalism.IndefR.Fin.LevelGroupLemmas.resM, Matrix.add_apply, Matrix.smul_apply,
      Matrix.sub_apply, smul_eq_mul, RingHom.map_add, RingHom.map_mul, RingHom.map_sub, h1, h2]
    ring
  have hd : Ideal.Quotient.mk I (Formalism.IndefR.Fin.LevelGroupLemmas.resM (e + cA D e) (mt V g)).det = Ideal.Quotient.mk I (mt V g).det := by
    rw [RingHom.map_det, RingHom.map_det]
    exact congrArg Matrix.det key
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton'] at hd
  obtain ⟨r, hr⟩ := hd
  linear_combination (-e) * hr + (-r) * he2

theorem detAt_one' {D : D7} {e : AE D} (he2 : e * e = e) (V : HSp D) : detAt e V 1 = 1 := by
  apply Units.ext
  rw [Formalism.IndefR.Fin.LevelGroupLemmas.detAt_val he2, Formalism.IndefR.Fin.LevelGroupLemmas.mt_one', Matrix.det_one, Units.val_one]
  ring

theorem resG_inv_eq {D : D7} {V : HSp D} {ε : AF D.host.F} (hε : IsIdempotentElem ε) (g : GA D V) :
    (resG V ε g)⁻¹ = resG V ε g⁻¹ := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← resG_mul V hε, mul_inv_cancel, resG_one V hε]

theorem actO_one_resG_compl {D : D7} {S T : HSp D} {e : AE D} (he2 : e * e = e) (hc : e * cA D e = 0) {ε : AF D.host.F}
    (hε : IsIdempotentElem ε) (halg : algebraMap (AF D.host.F) (AE D) ε = e + cA D e) (h : GA D T) (x : WO S T)
    (hx : IsHalf e x) : actO S T 1 (resG T (1 - ε) h) x = x := by
  have hann : ∀ i j, algebraMap (AF D.host.F) (AE D) (1 - ε) * x i j = 0 := by
    intro i j
    rw [map_sub, map_one, halg, ← hx i j]
    linear_combination (-(x i j)) * he2 + (-(x i j)) * hc
  rw [Formalism.IndefR.Fin.LevelGroupLemmas.actO_eq, inv_one, Formalism.IndefR.Fin.LevelGroupLemmas.mt_one', Matrix.mul_one,
    Formalism.IndefR.Fin.LevelGroupLemmas.mt_resG T hε.one_sub]
  unfold Formalism.IndefR.Fin.LevelGroupLemmas.resM
  rw [Matrix.add_mul, Matrix.one_mul, add_eq_left]
  ext i j
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [mul_assoc, mul_left_comm, hann l j, mul_zero]

theorem isSBHalf_halfInd {D : D7} {m n : ℕ} (e : AE D) (Λ : AddSubgroup (Mx D m n)) : IsSBHalf e Λ (halfInd e Λ) := by
  refine ⟨fun x hx => ?_, 1, one_pos, fun u hu hu' x => ?_, fun x hx => ?_⟩
  · by_contra h; exact hx (if_neg fun h' => h h'.2)
  · rw [one_smul]
    have h1 : IsHalf e (x + u) ↔ IsHalf e x := forall₂_congr fun i j => by
      rw [Matrix.add_apply, mul_add, hu' i j, add_left_inj]
    exact halfInd_congr (and_congr (AddSubgroup.add_mem_cancel_right _ hu) h1)
  · rw [one_smul]; by_contra h; exact hx (if_neg fun h' => h h'.1)

end GlobalTheory.TopLevelInv

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFourierIndexRationalPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.MovedJetNZ

open GlobalTheory.Grid (neg ofSgn)

theorem std_eq_colLat_one' {D : D7} {n : ℕ} (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (hL : ∀ y, y ∈ L ↔ ∀ i, ∃ b : 𝓞 D.host.E, (b : D.host.E) = y i) :
    (L : Set (Fin n → D.host.E)) = (colLat (1 : GL (Fin n) D.host.E) : Set _) := by
  ext y
  simp only [SetLike.mem_coe, hL, lc_mem_colLat_one, Submodule.mem_one]

theorem even_bot' {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW} (hX : IsBottomTri W i j X) : Even (A.rank * WW.rank) := by
  refine Even.mul_left ?_ _
  have h1 := hX.rank
  have h2 := hX.rank'
  have h3 := hX.is.rank
  have h4 := SqNum.ranks_exact D i j
  rw [← h3, h1, h2]
  refine ⟨SqNum.halfRank D i j - (D.R.m - (j.1 + 1)) / 2 - (D.R.m - j.1) / 2, ?_⟩
  omega

theorem vac_jet_ne_zero {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW} (hI : ∀ D, GlobalTheory.NormSum.Inp D) (hX : IsBottomTri W i j X) :
    ∃ k : FVar D WW.rank A.rank →₀ ℕ, pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B X.vac
      (MvPolynomial.monomial k 1) 0 ≠ 0 := by
  classical
  have hIs := hX.is
  have hψ : IsStdChar D W.ψ (-1) := hIs.isVac.1
  have hθ : IsInfFam W.θ := hIs.isVac.2.inf
  set f : WO A WW → ℂ := fun w => starRingEnd ℂ (X.vac w) with hfdef
  have hf0 : IsVacO W.ψ W.θ A WW X.rA.s X.rW.s X.rA.Λ X.rW.Λ f :=
    GlobalTheory.VacConj.isVacO_conj_negSp W.ψ W.θ A WW X.rA.s X.rW.s _ _ X.vac hIs.isVac
  have hf : IsVacO W.ψ W.θ A WW X.rA.s X.rW.s (colLat (1 : GL (Fin A.rank) D.host.E) : Set _)
      (colLat (1 : GL (Fin WW.rank) D.host.E) : Set _) f := by
    rw [← std_eq_colLat_one' X.rA.Λ hX.std.2.1, ← std_eq_colLat_one' X.rW.Λ hX.stdW.2.1]
    exact hf0
  have hS : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (1 : GL (Fin A.rank) D.host.E).1 * A.gram *
      (1 : GL (Fin A.rank) D.host.E).1 = 1 := by
    rw [hX.std.1]
    simp [Formalism.UG.cT]
  have hW : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (1 : GL (Fin WW.rank) D.host.E).1 * WW.gram *
      (1 : GL (Fin WW.rank) D.host.E).1 = 1 := by
    rw [hX.stdW.1]
    simp [Formalism.UG.cT]
  have hcA : ∀ τ, IsCartanInv (gramAt D A τ) (X.rA.s τ) := fun τ => (hIs.rigA.2.2 τ).1
  have hcW : ∀ τ, IsCartanInv (gramAt D WW τ) (X.rW.s τ) := fun τ => (hIs.rigW.2.2 τ).1
  have hBA : (fun τ => (1 : GL (Fin A.rank) D.host.E).1.map (tauE D τ)) = X.rA.B := by
    funext τ
    rw [(hX.std.2.2 τ).2]
    simp
  have hBW : (fun τ => (1 : GL (Fin WW.rank) D.host.E).1.map (tauE D τ)) = X.rW.B := by
    funext τ
    rw [(hX.stdW.2.2 τ).2]
    simp
  obtain ⟨δ, hC, hδ⟩ := GlobalTheory.FunObj.exists_delta D
  obtain ⟨t0, ht0⟩ := ((hI D).t0Ex D.host.ccK δ hC).1
  obtain ⟨e0, he0, he0ne⟩ := GlobalTheory.Vacuum.exists_vacuum D D.host.ccK δ hC t0 ht0 A.rank WW.rank (even_bot' hX)
  obtain ⟨c, hc⟩ := GlobalTheory.FockPos.fock_jets_eq_unit_mul_period_jets W.ψ W.θ A WW X.rA.s X.rW.s 1 1 hS hW hcA hcW δ t0 hC hδ
    ht0 e0 he0 f hf
  obtain ⟨α, hα⟩ := GlobalTheory.NatFamily.exists_taylor_ne D he0.1.1 he0ne
  refine ⟨α, ?_⟩
  change pureTensorO W.ψ W.θ (negSp A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B X.vac (MvPolynomial.monomial α 1) 0 ≠ 0
  rw [GlobalTheory.FockConj.pureTensorO_negSp_monomial W.ψ W.θ A WW X.rA.s X.rW.s X.rA.B X.rW.B X.vac hψ hθ α 0, map_ne_zero,
    ← hBA, ← hBW, hc α, GlobalTheory.FockPos.applyAt0_monomial']
  have hprod : (α.prod fun v n => GlobalTheory.FunObj.period δ v.1 ^ n) ≠ 0 :=
    Finsupp.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ (GlobalTheory.FunObj.period_ne_zero hδ v.1)
  have hfac : (α.prod fun _ n => (n.factorial : ℂ)) ≠ 0 :=
    Finsupp.prod_ne_zero_iff.2 fun _ _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  exact mul_ne_zero c.ne_zero (mul_ne_zero hprod (mul_ne_zero hfac hα))

end GlobalTheory.MovedJetNZ

end

namespace GlobalTheory.MovedJetNZ

open GlobalTheory.Grid (neg ofSgn)

end GlobalTheory.MovedJetNZ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenSubgroupFixesVacuumDefiniteBottom
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenSubgroupFixesVacuumDefiniteBottom
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

open scoped Topology

noncomputable section

namespace GlobalTheory.VacFixSource

theorem om_pow_eq_fst {D : D7} {S V : HSp D} (om : GA D S × GA D V →* Module.End ℂ (WO S V → ℂ)) (k : GA D S)
    (f : WO S V → ℂ) (c : ℂ) (hc : om (k, 1) f = c • f) : ∀ m : ℕ, om (k ^ m, 1) f = c ^ m • f := by
  intro m
  induction m with
  | zero => rw [pow_zero, pow_zero, Prod.mk_one_one, map_one, Module.End.one_apply, one_smul]
  | succ m ih =>
    have e : ((k ^ (m + 1), (1 : GA D V)) : GA D S × GA D V) = (k ^ m, 1) * (k, 1) := by
      rw [pow_succ, Prod.mk_mul_mk, mul_one]
    rw [e, map_mul, Module.End.mul_apply, hc, map_smul, ih, smul_smul, pow_succ, mul_comm]


set_option maxHeartbeats 1000000 in
theorem exists_open_fix_vac_source : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, IsBottomTri W i j X → ∀ t : T,
    ∃ U : Subgroup (GA D A'), IsOpen (U : Set (GA D A')) ∧ ∀ κ ∈ U, κ ∈ GfC A' → X.ω' t (κ, 1) X.vac' = X.vac' := by
  intro D T L sc G W i j A A' WW X hX t
  have hW : IsWeilDatumO W.ψ A' WW _ _ (X.ω' t) := hX.is.weil' t
  have hvac : IsVacO W.ψ W.θ A' WW X.rA'.s X.rW.s X.rA'.Λ X.rW.Λ X.vac' := hX.is.isVac'
  have hθ : IsInfFam W.θ := hvac.2.inf
  have hsdS : IsSelfDualC A' X.rA'.Λ := hX.is.rigA'.1
  have hsdT : IsSelfDualC WW X.rW.Λ := hX.is.rigW.1
  have hcS : ∀ τ, IsCartanInv (gramAt D A' τ) (X.rA'.s τ) := fun τ => (hX.is.rigA'.2.2 τ).1
  have hcT : ∀ τ, IsCartanInv (gramAt D WW τ) (X.rW.s τ) := fun τ => (hX.is.rigW.2.2 τ).1
  have hev := (GlobalTheory.LatNhds.eventually_actO D A' WW X.rA'.Λ X.rW.Λ hsdS hsdT
    (GlobalTheory.LatFinGen.latO_finitely_generated D A' WW X.rA'.Λ X.rW.Λ hsdS hsdT)).1
  have hpair : Filter.Tendsto (fun x : GA D A' => ((x, (1 : GA D WW)) : GA D A' × GA D WW)) (𝓝 1) (𝓝 1) := by
    have := ((continuous_id.prodMk continuous_const :
      Continuous fun x : GA D A' => ((x, (1 : GA D WW)) : GA D A' × GA D WW))).tendsto 1
    exact this
  have hev' := hpair.eventually hev
  obtain ⟨n₁, hn₁⟩ : ∃ n : ℕ, ∀ x ∈ GfC A', GlobalTheory.Member.FinCong A' n.factorial x →
      ∀ u ∈ (latO A' WW (X.rA'.Λ : Set (Fin A'.rank → D.host.E)) (X.rW.Λ : Set (Fin WW.rank → D.host.E)) fun _ => True),
        actO A' WW x 1 u ∈
          (latO A' WW (X.rA'.Λ : Set (Fin A'.rank → D.host.E)) (X.rW.Λ : Set (Fin WW.rank → D.host.E)) fun _ => True) := by
    by_contra hne
    push_neg at hne
    choose k hk hkc u hu hu' using hne
    have ht := GlobalTheory.SplitCharTrivial.tendsto_one_of_finCong hk hkc
    obtain ⟨n, hn⟩ := (ht.eventually hev').exists
    exact hu' n (hn _ (hu n))
  have hscal : ∀ k ∈ GfC A', GlobalTheory.Member.FinCong A' n₁.factorial k →
      ∃ c : ℂ, ‖c‖ = 1 ∧ X.ω' t (k, 1) X.vac' = c • X.vac' := by
    intro k hk hc
    have hΛ : ∀ u : WO A' WW, u ∈ (latO A' WW (X.rA'.Λ : Set (Fin A'.rank → D.host.E))
        (X.rW.Λ : Set (Fin WW.rank → D.host.E)) fun _ => True) ↔ ∃ u₀ ∈ (latO A' WW
        (X.rA'.Λ : Set (Fin A'.rank → D.host.E)) (X.rW.Λ : Set (Fin WW.rank → D.host.E)) fun _ => True),
        u = actO A' WW k 1 u₀ := by
      intro u
      constructor
      · intro hu
        refine ⟨actO A' WW k⁻¹ 1 u, hn₁ k⁻¹ (inv_mem hk) (GlobalTheory.Member.PrincLevel.finCong_inv hc) u hu, ?_⟩
        have := GlobalTheory.WeilVacMove.actO_inv_actO k⁻¹ (1 : GA D WW) u
        rw [inv_inv, inv_one] at this
        exact this.symm
      · rintro ⟨u₀, hu₀, rfl⟩
        exact hn₁ k hk hc u₀ hu₀
    have hvac' := GlobalTheory.WeilVacMove.isVacO_om D W.ψ W.θ A' WW _ _ (X.ω' t) hW hθ
      X.rA'.s X.rA'.s X.rW.s X.rW.s _ _ _ _ k 1
      (fun τ => by rw [GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC W.θ A' hk τ, Matrix.one_mul, Matrix.mul_one])
      (fun τ => GlobalTheory.SmoothVac.comm_compAt_one WW W.θ τ (X.rW.s τ)) hΛ X.vac' hvac
    exact GlobalTheory.VacUnique.vacUniqueO D W.ψ W.θ hvac.1 hθ (Formalism.L2.Fam.ThC.fixSig A') (Formalism.L2.Fam.ThC.fixSig WW)
      X.rA'.s X.rW.s (Formalism.L2.Fam.ThC.fixSig_ok _) (Formalism.L2.Fam.ThC.fixSig_ok _) hcS hcT X.rA'.Λ X.rW.Λ
      hsdS hsdT X.vac' _ (GlobalTheory.VacFixTarget.isVacO_fixSig hvac) (GlobalTheory.VacFixTarget.isVacO_fixSig hvac')
  obtain ⟨w₀, hw₀⟩ := GlobalTheory.SmoothVac.exists_ne_zero_of_isVacO hvac
  have hcont : Continuous fun k : GA D A' => X.ω' t (k, 1) X.vac' w₀ :=
    (hW.om_cont _ hvac.2.theta w₀).comp (continuous_id.prodMk continuous_const)
  have key : ∃ n : ℕ, ∀ k ∈ GfC A', GlobalTheory.Member.FinCong A' (n₁.factorial * n.factorial) k →
      X.ω' t (k, 1) X.vac' = X.vac' := by
    by_contra hne
    push_neg at hne
    choose k hk hkc hkne using hne
    have hpow : ∀ n, ∃ m : ℕ, ∃ c : ℂ, X.ω' t (k n ^ m, 1) X.vac' = c • X.vac' ∧ ¬ ‖c - 1‖ ≤ 1 / 2 := by
      intro n
      obtain ⟨c, -, hc⟩ := hscal (k n) (hk n) (GlobalTheory.SmoothVac.finCong_of_mul_left (hkc n))
      have hc1 : c ≠ 1 := by
        rintro rfl
        exact hkne n (by rw [hc, one_smul])
      by_contra h
      push_neg at h
      exact hc1 (GlobalTheory.Doubling.eq_one_of_forall_norm_pow_sub_one_le (A := ℂ) fun m =>
        h m (c ^ m) (om_pow_eq_fst _ (k n) _ c hc m))
    choose m c hmc hc using hpow
    have hmem : ∀ n, k n ^ m n ∈ GlobalTheory.Member.PrincLevel.levelGroup A' (n₁.factorial * n.factorial) :=
      fun n => pow_mem (show k n ∈ GlobalTheory.Member.PrincLevel.levelGroup A' (n₁.factorial * n.factorial) from ⟨hk n, hkc n⟩) _
    have ht := GlobalTheory.SplitCharTrivial.tendsto_one_of_finCong (k := fun n => k n ^ m n) (fun n => (hmem n).1)
      (fun n => GlobalTheory.SmoothVac.finCong_of_mul_right (hmem n).2)
    have h2 := (hcont.tendsto 1).comp ht
    have e1 : X.ω' t ((1 : GA D A'), (1 : GA D WW)) X.vac' w₀ = X.vac' w₀ := by
      show X.ω' t 1 X.vac' w₀ = _
      rw [map_one]
      rfl
    rw [Function.comp_def, e1] at h2
    have hpos : 0 < ‖X.vac' w₀‖ / 2 := half_pos (norm_pos_iff.2 hw₀)
    obtain ⟨n, hn⟩ := (h2.eventually (Metric.ball_mem_nhds _ hpos)).exists
    rw [hmc n, Pi.smul_apply, smul_eq_mul, dist_eq_norm, ← sub_one_mul, norm_mul] at hn
    have := hc n
    push_neg at this
    nlinarith [norm_nonneg (X.vac' w₀)]
  obtain ⟨n, hn⟩ := key
  exact ⟨GlobalTheory.VacFixTarget.congGroup A' (n₁.factorial * n.factorial),
    GlobalTheory.VacFixTarget.isOpen_congGroup A' (Nat.mul_pos n₁.factorial_pos n.factorial_pos), fun κ hU hκ => hn κ hκ hU⟩

end GlobalTheory.VacFixSource
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenSubgroupFixesVacuumDefiniteBottomStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_subgroup_fixes_vacuum_definiteBottom : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m}
    {A A' WW : HSp D} {X : Tri T A A' WW}, IsBottomTri W i j X → ∀ t : T,
    ∃ U : Subgroup (GA D A'), IsOpen (U : Set (GA D A')) ∧ ∀ κ ∈ U, κ ∈ GfC A' → X.ω' t (κ, 1) X.vac' = X.vac' := by
  first | exact @GlobalTheory.VacFixSource.exists_open_fix_vac_source | exact GlobalTheory.VacFixSource.exists_open_fix_vac_source | (intros; apply GlobalTheory.VacFixSource.exists_open_fix_vac_source <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierIndexRationalPairValue
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section

namespace GlobalTheory.MovedJet

open GlobalTheory.Grid (neg sgn ofSgn)
open MvPolynomial

theorem substF_one {ι : Type} {N n : ℕ} (P : MvPolynomial (ι × Fin N × Fin n) ℂ) :
    GlobalTheory.CompactHowe.substF (fun _ : ι => (1 : Matrix (Fin N) (Fin N) ℂ)) (fun _ : ι => (1 : Matrix (Fin n) (Fin n) ℂ)) P = P := by
  have key : GlobalTheory.CompactHowe.substF (fun _ : ι => (1 : Matrix (Fin N) (Fin N) ℂ)) (fun _ : ι => (1 : Matrix (Fin n) (Fin n) ℂ)) =
      AlgHom.id ℂ (MvPolynomial (ι × Fin N × Fin n) ℂ) := by
    refine algHom_ext fun p => ?_
    rw [GlobalTheory.CompactHowe.substF_X]
    obtain ⟨τ, a, b⟩ := p
    rw [Finset.sum_eq_single a (fun x _ hx => Finset.sum_eq_zero fun y _ => by simp [Matrix.one_apply, hx]) (by simp),
      Finset.sum_eq_single b (fun y _ hy => by simp [Matrix.one_apply, hy]) (by simp)]
    simp
  exact congrArg (fun f => f P) key

theorem mul_conjT_of_unitary {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : Matrix.conjTranspose M * M = 1) :
    M * Matrix.conjTranspose M = 1 := Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _) |>.1 h

theorem map_conj_mul_conjT {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : M * Matrix.conjTranspose M = 1) :
    M.map (starRingEnd ℂ) * Matrix.conjTranspose (M.map (starRingEnd ℂ)) = 1 := by
  have e := congrArg (fun N : Matrix (Fin n) (Fin n) ℂ => N.map (starRingEnd ℂ)) h
  simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at e
  convert e using 2
  ext a b
  simp [Matrix.conjTranspose_apply]

end GlobalTheory.MovedJet

namespace GlobalTheory.MovedJet

open GlobalTheory.Grid (neg sgn ofSgn)
open MvPolynomial

theorem conj_invT_of_unitary' {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : Matrix.conjTranspose M * M = 1) :
    ((M⁻¹).transpose).map (starRingEnd ℂ) = M := by
  rw [Matrix.inv_eq_left_inv h]
  ext a b
  simp only [Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply, RCLike.star_def, Complex.conj_conj]

theorem conjT_mul_compAt {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} (hV : V.gram = 1) (g : GA D V)
    (τ : D.what₂.Tau) :
    Matrix.conjTranspose (compAt θ τ (Formalism.L2.Theta.mt V g)) * compAt θ τ (Formalism.L2.Theta.mt V g) = 1 := by
  have h1 := GlobalTheory.StdUnn.CartanMove.compAt_isom hθ V g τ
  have hg : gramAt D V τ = 1 := by
    unfold gramAt
    rw [hV]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  rw [hg, Matrix.mul_one] at h1
  exact h1

theorem om_pureTensorO_vac {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW} (hX : IsBottomTri W i j X) (t : T) (g : GA D A)
    (h : GA D WW) (P : MvPolynomial (FVar D WW.rank A.rank) ℂ) :
    IsThetaFunO W.ψ (neg A) WW (pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B X.vac P) ∧
    (X.ω t).toSgn true ((ofSgn true A).symm g, h)
        (pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B X.vac P) =
      pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B
        ((X.ω t).toSgn true ((ofSgn true A).symm g, h) X.vac)
        (GlobalTheory.CompactHowe.substF (fun τ => (compAt W.θ τ (Formalism.L2.Theta.mt WW h)).map (starRingEnd ℂ))
          (fun τ => compAt W.θ τ (Formalism.L2.Theta.mt A g)) P) := by
  have hI := hX.is
  have hθ : IsInfFam W.θ := hI.isVac.2.inf
  have hψ : IsStdChar D W.ψ (-1) := hI.isVac.1
  have hom := hI.weil t
  have hsA : ∀ τ, X.rA.s τ = 1 := fun τ => (hX.std.2.2 τ).1
  have hsW : ∀ τ, X.rW.s τ = 1 := fun τ => (hX.stdW.2.2 τ).1
  have hBA : ∀ τ, X.rA.B τ = 1 := fun τ => (hX.std.2.2 τ).2
  have hBW : ∀ τ, X.rW.B τ = 1 := fun τ => (hX.stdW.2.2 τ).2
  have hf : IsThetaFunO W.ψ (neg A) WW X.vac := hI.isVac.2.theta
  have hmt : Formalism.L2.Theta.mt (neg A) ((ofSgn true A).symm g) = Formalism.L2.Theta.mt A g := by
    rw [← GlobalTheory.Grid.mt_ofSgn, MulEquiv.apply_symm_apply]
  set u : D.what₂.Tau → Matrix (Fin A.rank) (Fin A.rank) ℂ := fun τ => compAt W.θ τ (Formalism.L2.Theta.mt A g) with hu
  set v : D.what₂.Tau → Matrix (Fin WW.rank) (Fin WW.rank) ℂ := fun τ => compAt W.θ τ (Formalism.L2.Theta.mt WW h) with hv
  have hop := GlobalTheory.OrientedHeis.om_pureTensorO D W.ψ W.θ (neg A) WW _ _ ((X.ω t).toSgn true) hom hθ
    (fun τ => -X.rA.s τ) (fun τ => -X.rA.s τ) X.rA.B (fun τ => X.rA.B τ * u τ) X.rW.s X.rW.s X.rW.B
    (fun τ => X.rW.B τ * v τ) ((ofSgn true A).symm g) h
    (fun τ => by rw [hmt, hsA, Matrix.neg_mul, Matrix.mul_neg, Matrix.one_mul, Matrix.mul_one])
    (fun τ => by rw [hsW, Matrix.one_mul, Matrix.mul_one])
    (fun τ => by rw [hmt, hBA, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [hBW, Matrix.mul_one, Matrix.one_mul]) X.vac hf P
  refine ⟨hop.1, ?_⟩
  rw [hop.2]
  have hf' : IsThetaFunO W.ψ (neg A) WW ((X.ω t).toSgn true ((ofSgn true A).symm g, h) X.vac) :=
    hom.om_pres _ _ hf
  have e1 : (fun τ => -X.rA.s τ) = fun _ => (-1 : Matrix (Fin A.rank) (Fin A.rank) ℂ) := funext fun τ => by rw [hsA]
  have e2 : X.rW.s = fun _ => (1 : Matrix (Fin WW.rank) (Fin WW.rank) ℂ) := funext hsW
  have key := GlobalTheory.FockNegSubst.pureTensorO_negSp_subst D W.ψ W.θ A WW hψ hθ X.rA.B u X.rW.B v _ hf' P
  have hunit : ∀ τ, (((u τ)⁻¹).transpose).map (starRingEnd ℂ) = u τ := fun τ =>
    conj_invT_of_unitary' (conjT_mul_compAt hθ hX.std.1 g τ)
  rw [funext hunit] at key
  rw [e1, e2]
  exact key

end GlobalTheory.MovedJet

namespace GlobalTheory.MovedJet

open GlobalTheory.Grid (neg sgn ofSgn)
open MvPolynomial

theorem isAlgebraic_compAt_of_mem_GQ {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {γ : GA D V}
    (hγ : γ ∈ GQ V) (τ : D.what₂.Tau) (a b : Fin V.rank) :
    IsAlgebraic ℚ (compAt θ τ (Formalism.L2.Theta.mt V γ) a b) := by
  obtain ⟨γ₀, h0⟩ := GlobalTheory.Member.exists_isRat_of_mem_GQ V hγ
  have key : compAt θ τ (Formalism.L2.Theta.mt V γ) a b = tauE D τ (γ₀.1 a b) := by
    unfold compAt Formalism.L2.Theta.mt
    rw [h0]
    exact (hθ τ).1 _
  rw [key]
  have h0 : IsAlgebraic ℚ (γ₀.1 a b) := Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (γ₀.1 a b)
  first
    | exact h0.algHom (tauE D τ).toRatAlgHom
    | exact IsAlgebraic.map (tauE D τ).toRatAlgHom h0
    | exact (isAlgebraic_algHom_iff (tauE D τ).toRatAlgHom (tauE D τ).injective).2 h0

theorem isAlgebraic_conj {z : ℂ} (h : IsAlgebraic ℚ z) : IsAlgebraic ℚ (starRingEnd ℂ z) := by
  first
    | exact h.algHom (starRingEnd ℂ).toRatAlgHom
    | exact IsAlgebraic.map (starRingEnd ℂ).toRatAlgHom h
    | exact (isAlgebraic_algHom_iff (starRingEnd ℂ).toRatAlgHom (starRingEnd ℂ).injective).2 h

end GlobalTheory.MovedJet

end
end
