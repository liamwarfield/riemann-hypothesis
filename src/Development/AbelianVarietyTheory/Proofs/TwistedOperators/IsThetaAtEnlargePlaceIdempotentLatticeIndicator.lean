module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RankCol
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittCoreInclusionMemCompletedHomLattice
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumValueAlgebraicCongruence
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeThetaLevelFourth
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DependenceFixed

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaAtEnlargePlaceIdempotentLatticeIndicator
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaAtEnlargePlaceIdempotentLatticeIndicator
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ThetaEnlarge

theorem isThetaAt_enlarge : ∀ {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)},
    IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ {f₀ : WO S T → ℂ}, IsVacO ψ θ S T sS sT (ΛS : Set _) (ΛT : Set _) f₀ →
    ∀ {e e' : AE D} {P P' : Finset (Pl D.host.E)}, IsIdemSum e P → IsIdemSum e' P' → P' ⊆ P →
    ∀ {Φ g : WO S T → ℂ}, IsSBHalf e' (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) Φ →
    IsThetaAt ψ (symplO S T) (heisO ψ S T) e' (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) 1 f₀ Φ g →
    IsSBHalf e (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True)
        (GlobalTheory.HalfProd.prodHalf e' (e - e') (halfInd (e - e') (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True)) Φ) ∧
      IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) 1 f₀
        (GlobalTheory.HalfProd.prodHalf e' (e - e') (halfInd (e - e') (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True)) Φ) g := by
  intro D S T ψ θ sS sT ΛS ΛT hS hT f₀ hvac e e' P P' he he' hsub Φ g hΦ hg
  obtain ⟨b, rfl, hb, hab⟩ := GlobalTheory.RowLocVec.exists_compl_idem hsub he he'
  have ha := GlobalTheory.PlaceDatum.idemSum_mul_self he'
  rw [add_sub_cancel_left]
  exact GlobalTheory.RowLocVec.isThetaAt_extend hvac.1 hS hT he ha hb hab hvac.2.lat hΦ hg

end GlobalTheory.ThetaEnlarge

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaAtEnlargePlaceIdempotentLatticeIndicatorStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isThetaAt_enlarge_placeIdempotent_latticeIndicator : ∀ {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)},
    IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ {f₀ : WO S T → ℂ}, IsVacO ψ θ S T sS sT (ΛS : Set _) (ΛT : Set _) f₀ →
    ∀ {e e' : AE D} {P P' : Finset (Pl D.host.E)}, IsIdemSum e P → IsIdemSum e' P' → P' ⊆ P →
    ∀ {Φ g : WO S T → ℂ}, IsSBHalf e' (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) Φ →
    IsThetaAt ψ (symplO S T) (heisO ψ S T) e' (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) 1 f₀ Φ g →
    IsSBHalf e (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True)
        (GlobalTheory.HalfProd.prodHalf e' (e - e') (halfInd (e - e') (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True)) Φ) ∧
      IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) 1 f₀
        (GlobalTheory.HalfProd.prodHalf e' (e - e') (halfInd (e - e') (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True)) Φ) g := by
  first | exact @GlobalTheory.ThetaEnlarge.isThetaAt_enlarge | exact GlobalTheory.ThetaEnlarge.isThetaAt_enlarge | (intros; apply GlobalTheory.ThetaEnlarge.isThetaAt_enlarge <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFiniteAdelicMatrixLatticeDepthLatticeOfPair
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFiniteAdelicMatrixLatticeDepthLatticeOfPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.DepLat

variable {D : D7}

theorem finLat_of_nsmul {m n : ℕ} {Λ A : AddSubgroup (Mx D m n)} (h : FinLat Λ) (hle : A ≤ Λ)
    {K : ℕ} (hK : 0 < K) (hA : ∀ u ∈ Λ, K • u ∈ A) : FinLat A := by
  obtain ⟨U, h1, h2, h3⟩ := h.opn
  have inv : (K : AE D) * incA D (K : D.host.E)⁻¹ = 1 := by
    rw [← map_natCast (incA D), ← map_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hK.ne'), map_one]
  have hc : Continuous fun a : Mx D m n => incA D (K : D.host.E)⁻¹ • a := continuous_id.const_smul (incA D (K : D.host.E)⁻¹)
  refine GlobalTheory.AscFinWit.finLat_of (fun a ha => h.fin a (hle ha))
    ⟨_, h1.preimage hc, by rwa [Set.mem_preimage, smul_zero], fun a ha hb => ?_⟩ h.cpt fun a ha => hle ha
  have := hA _ (h3 _ ha fun i j => Ideal.mul_mem_left _ _ (hb i j))
  rwa [← Nat.cast_smul_eq_nsmul (AE D), smul_smul, inv, one_smul] at this

theorem finLat_depLat : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (p : Pair T), IsSelfDualC (G.pS p) (G.latS p) → IsSelfDualC (G.pT p) (G.latT p) → FinLat (depLat G p) := by
  intro D T L sc G p hS hT
  obtain ⟨K, hK, h⟩ := GlobalTheory.GridWeil.exists_nsmul_latO (T := G.pT p) (ΛT := G.latT p) hS (G.pl.modul_ne_bot sc)
  refine finLat_of_nsmul (GlobalTheory.AscFinWit.finLat_latO (GlobalTheory.ProjXCols.selfDual_isFullLattice _ _ hS) (GlobalTheory.ProjXCols.selfDual_isFullLattice _ _ hT)) (fun u hu => hu.1) hK
    fun u hu => ⟨nsmul_mem hu K, fun e he => ?_⟩
  rw [smul_comm]
  exact h _ (GlobalTheory.LatticeStable.smul_mem_latO D _ _ _ _ _ e
    (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, GlobalTheory.PlaceVec.idemSum_mul_self he])) _ hu)

end GlobalTheory.AscFin.DepLat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFiniteAdelicMatrixLatticeDepthLatticeOfPairStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFiniteAdelicMatrixLattice_depthLatticeOfPair : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (p : Pair T), IsSelfDualC (G.pS p) (G.latS p) → IsSelfDualC (G.pT p) (G.latT p) → FinLat (depLat G p) := by
  first | exact @GlobalTheory.AscFin.DepLat.finLat_depLat | exact GlobalTheory.AscFin.DepLat.finLat_depLat | (intros; apply GlobalTheory.AscFin.DepLat.finLat_depLat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitModulusScalarLocal
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

namespace GlobalTheory.MovedKappaEx

theorem selfDualLattice_intertwiner_baseVector_ne_zero {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} (hC : Crv D cc δ)
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) {N N' : ℕ} {e0 : VC D N N' → ℂ} (he : oddE0 D cc δ t0 N N' e0)
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (hL : SD D L) (hL' : SD D L') :
    Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D cc δ) L L') e0 ≠ 0 := by
  have s0 := GlobalTheory.MovedVacuum.sd_stdL D N
  have s0' := GlobalTheory.MovedVacuum.sd_stdL D N'
  have k0 : KLat D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') := Or.inr ⟨_, _, s0, s0', rfl⟩
  have k1 : KLat D (tor0 D cc δ) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D cc δ) L L') := Or.inr ⟨_, _, hL, hL', rfl⟩
  have huni := GlobalTheory.theta_translation_intertwiner_unitary D cc δ hC N N' _ _ k0 k1
  intro h
  exact GlobalTheory.TrueTheta.ne_zero_of_like hC ht s0 s0' he.2.2.2.1
    (by rw [← (huni e0 he.1).2.2.2, h, GlobalTheory.VacuumScalar.Iop_zero])

theorem applyAt0_monomial' (D : D7) {N N' : ℕ} (α : Mono D N N') (G : VC D N N' → ℂ) :
    Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial α 1) G
      = (α.prod fun _ n => (n.factorial : ℂ)) * Formalism.MainNotions.TaylorLogMetric.taylor D G α := by
  classical
  unfold Formalism.MainNotions.GL3Theta.applyAt0
  rw [MvPolynomial.support_monomial, if_neg one_ne_zero, Finset.sum_singleton, MvPolynomial.coeff_monomial,
    if_pos rfl, one_mul]

theorem unitAt_mul {q : ℕ} [Fact q.Prime] {a b : ℂ} (ha : Mod1All a) (hb : Mod1All b) (hua : UnitAt q a)
    (hub : UnitAt q b) : UnitAt q (a * b) := by
  obtain ⟨ha', -⟩ := ha
  obtain ⟨hb', -⟩ := hb
  intro lam
  have hab : a * b ∈ Qbar := mul_mem ha' hb'
  have e : lamC lam (a * b) = lamC lam a * lamC lam b := by
    unfold lamC
    rw [dite_eq_left hab, dite_eq_left ha', dite_eq_left hb', ← map_mul]
    rfl
  rw [e, norm_mul, hua lam, hub lam, one_mul]

end GlobalTheory.MovedKappaEx

namespace GlobalTheory.MovedKappaEx

end GlobalTheory.MovedKappaEx
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetIdeleConjugatedTopPointEqProdLocal
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetIdeleConjugatedTopPointEqProdLocal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open Formalism.IndefR.Fin.LevelGroupLemmas (resG detAt)

namespace GlobalTheory.TopLevelInv

theorem det_kapAt_val {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) (t : T) (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))) (w : Pl D.host.E) :
    ((gdet (kapAt S t j hj k w) : (Kw w)ˣ) : Kw w) =
      GlobalTheory.StdFrames.cpt w (toEAf D (mt (G.V (.top (j + 1))) (k : GA D (G.V (.top (j + 1))))).det) := by
  unfold kapAt GlobalTheory.FunObj.inBasis
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, GlobalTheory.SplitFlip.gdet, GlobalTheory.StepData.det_reGL]
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  obtain ⟨X, hX⟩ : ∃ X, X = (MulAut.conj (S.βp (j + 1))⁻¹) ((finG (G.V (.top (j + 1)))) k) := ⟨_, rfl⟩
  rw [← hX]
  refine ((RingHom.map_det (StdFrames.cpt w) X.val).symm : _).trans (congrArg _ ?_)
  rw [hX, MulAut.conj_apply, Units.val_mul, Units.val_mul, det_mul, det_mul, inv_inv, mul_right_comm, ← det_mul,
    ← Units.val_mul, inv_mul_cancel, Units.val_one, det_one, one_mul]
  show ((Lev.finE (G.V (.top (j + 1))) (k : GA D (G.V (.top (j + 1))))).val).det = _
  rw [GlobalTheory.VecInv.finE_val, RingHom.map_det]
  rfl


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem detAt_conjPt_eq_prod {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {U : Set T} (S : GridChoice W U) {t : T} (_ht : t ∈ U) (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1)))
    (e : AE D) (hI : IsIdemSum e (locPl G t)) :
    detAt e (G.V (.top (j + 1))) (conjPt S j k) =
      ∏ w : locPl G t, GlobalTheory.LFun.locIdele D.host.F w.1 (gdet (kapAt S t j hj k w)) := by
  classical
  have he2 : e * e = e := (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum hI).idem
  have hinf := GlobalTheory.PlaceDatum.infPart_idemSum hI
  have hcomp : ∀ Q, GlobalTheory.StdFrames.cpt (D := D) Q (toEAf D e) = if Q ∈ locPl G t then 1 else 0 := by
    intro Q
    obtain ⟨⟨es, hes, hsum⟩, -⟩ := hI
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsum, map_sum (toEAf D), map_sum (GlobalTheory.StdFrames.cpt (D := D) Q)]
    split_ifs with hQ
    · rw [Finset.sum_eq_single Q (fun P hP hPQ => (GlobalTheory.StdFrames.cpt_of_isIdemAt (hes P hP)).2 Q (Ne.symm hPQ))
        (fun h => absurd hQ h)]
      exact (GlobalTheory.StdFrames.cpt_of_isIdemAt (hes Q hQ)).1
    · exact Finset.sum_eq_zero fun P hP => (GlobalTheory.StdFrames.cpt_of_isIdemAt (hes P hP)).2 Q (fun h => hQ (h ▸ hP))
  have hloc : ∀ (w Q : Pl D.host.E) (y : (Kw w)ˣ),
      GlobalTheory.StdFrames.cpt (D := D) Q (toEAf D (GlobalTheory.LFun.locIdele D.host.F w y : AE D)) =
        (Neutral.B1.finiteSingle D.host.E w (y : Kw w)) Q := by
    intro w Q y
    rw [GlobalTheory.DepthFix.cpt_eq_finAd]
    exact congrArg (fun z : FiniteAdeleRing (𝓞 D.host.E) D.host.E => z Q) (GlobalTheory.LFun.finTens_locIdele (F := D.host.F) w y)
  have hdet : (mt (G.V (.top (j + 1))) (conjPt S j k)).det = (mt (G.V (.top (j + 1))) (k : GA D _)).det := by
    unfold Formalism.L2.Theta.mt
    rw [← Matrix.GeneralLinearGroup.val_det_apply, ← Matrix.GeneralLinearGroup.val_det_apply]
    congr 1
    simp only [conjPt, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
    rw [mul_right_comm, inv_mul_cancel, one_mul]
  apply Units.ext
  rw [Formalism.IndefR.Fin.LevelGroupLemmas.detAt_val he2, Units.coe_prod, hdet]
  apply GlobalTheory.FunObj.ae_ext
  · rw [RingHom.map_add (f := _), RingHom.map_mul, RingHom.map_sub, RingHom.map_one, hinf, zero_mul, zero_add, sub_zero, map_prod]
    exact (Finset.prod_eq_one fun w _ => GlobalTheory.LFun.infTens_locIdele (F := D.host.F) w.1 _).symm
  · intro Q
    simp only [RingHom.map_add (f := _), RingHom.map_mul, RingHom.map_sub, RingHom.map_one, map_prod, hcomp, hloc]
    by_cases hQ : Q ∈ locPl G t
    · rw [if_pos hQ, one_mul, sub_self, add_zero, Finset.prod_eq_single ⟨Q, hQ⟩]
      · rw [GlobalTheory.LFun.finSingle_self, det_kapAt_val]
      · intro b _ hb
        exact GlobalTheory.LFun.finSingle_ne (fun h => hb (Subtype.ext h.symm)) _
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [if_neg hQ, zero_mul, zero_add, sub_zero]
      exact (Finset.prod_eq_one fun w _ => GlobalTheory.LFun.finSingle_ne (fun h => hQ (by rw [h]; exact w.2)) _).symm

end GlobalTheory.TopLevelInv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetIdeleConjugatedTopPointEqProdLocalStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open Formalism.IndefR.Fin.LevelGroupLemmas (resG detAt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.detIdele_conjugatedTopPoint_eq_prod_local : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {t : T}, t ∈ U → ∀ (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))) (e : AE D),
    IsIdemSum e (locPl G t) →
    detAt e (G.V (.top (j + 1))) (conjPt S j k) =
      ∏ w : locPl G t, GlobalTheory.LFun.locIdele D.host.F w.1 (gdet (kapAt S t j hj k w)) := by
  first | exact @GlobalTheory.TopLevelInv.detAt_conjPt_eq_prod | exact GlobalTheory.TopLevelInv.detAt_conjPt_eq_prod | (intros; apply GlobalTheory.TopLevelInv.detAt_conjPt_eq_prod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowChainLastStepVectorEqThetaOfDatum
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowChainLastStepVectorEqThetaOfDatum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.FlipTopChain


open Classical in
theorem transport {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (k : ℕ)
    (P : Finset (Pl D.host.E)) (ψ : AddChar (AF D.host.F) ℂ) (e : AE D)
    {S S' : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛS' : Submodule (𝓞 D.host.E) (Fin S'.rank → D.host.E)}
    {X Y : LSp D} (hX : X = ⟨S, ΛS⟩) (hY : Y = ⟨S', ΛS'⟩)
    {βS : GL (Fin X.sp.rank) (EAf D)} {βT : GL (Fin Y.sp.rank) (EAf D)} {βS₀ : GL (Fin S.rank) (EAf D)}
    {βT₀ : GL (Fin S'.rank) (EAf D)} (h1 : HEq βS βS₀) (h2 : HEq βT βT₀)
    {f₀ g : WO X.sp Y.sp → ℂ} {f₀' g' : WO S S' → ℂ} (h3 : HEq f₀ f₀') (h4 : HEq g g')
    (ha : X.sp.rank = D.R.r + k * D.R.t) (hb : Y.sp.rank = D.R.r + (k + 1) * D.R.t)
    (ha' : S.rank = D.R.r + k * D.R.t) (hb' : S'.rank = D.R.r + (k + 1) * D.R.t)
    (Ω : Matrix (Fin S'.rank) (Fin S.rank) (EAf D) → ℂ)
    (hN : ∀ N, IsIntM N → Ω N = ∏ w ∈ P, stepFn L t w k
      ((N.map (cpt (D := D) w)).submatrix (Comparison₂.ixOf G t w hb') (Comparison₂.ixOf G t w ha')))
    (hθ : IsThetaAt ψ (symplO S S') (heisO ψ S S') e (latO S S' (ΛS : Set _) (ΛS' : Set _) fun _ => True) 1 f₀'
      (fun x => if IsHalf e x ∧ IsIntM (frMapO S S' βS₀ βT₀ x) then Ω (frMapO S S' βS₀ βT₀ x) else 0) g') :
    IsThetaAt ψ (symplO X.sp Y.sp) (heisO ψ X.sp Y.sp) e (latO X.sp Y.sp (X.lat : Set _) (Y.lat : Set _) fun _ => True) 1 f₀
      (fun x => if IsHalf e x ∧ IsIntM (Comparison₂.fr βT βS (x.map (toEAf D))) then
        ∏ w ∈ P, stepFn L t w k (((Comparison₂.fr βT βS (x.map (toEAf D))).map (cpt (D := D) w)).submatrix
          (Comparison₂.ixOf G t w hb) (Comparison₂.ixOf G t w ha)) else 0) g := by
  subst hX hY
  obtain rfl := eq_of_heq h1
  obtain rfl := eq_of_heq h2
  obtain rfl := eq_of_heq h3
  obtain rfl := eq_of_heq h4
  convert hθ using 2
  rename_i x
  by_cases h : IsHalf e x ∧ IsIntM (Comparison₂.fr βT βS (x.map (toEAf D)))
  · have h' : IsHalf e x ∧ IsIntM (frMapO S S' βS βT x) := h
    rw [if_pos h, if_pos h']
    exact (hN _ h.2).symm
  · have h' : ¬ (IsHalf e x ∧ IsIntM (frMapO S S' βS βT x)) := h
    rw [if_neg h, if_neg h']

end GlobalTheory.FlipTopChain

namespace GlobalTheory.FlipTopChain

theorem colY_eq_m {D : D7} {T : Type} (L : LevCh D T) : ∀ n, n = D.R.m → columnBlock L n = ⟨D.sp.X', L.ΛX⟩ := by
  rintro _ rfl; exact colY_m L

theorem colFrame_eq_m {D : D7} {T : Type} (L : LevCh D T) : ∀ n, n = D.R.m → HEq (colFrame L n) L.βX := by
  rintro _ rfl; exact colFrame_m L


set_option maxHeartbeats 1600000 in
theorem last_step_theta : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} {large₂ : SizeData₂ D},
    HidaSetting large₂ R F → ∀ ch : Choice R, ch.Is → ∀ (t : T) (j : Fin D.R.m) (g : Sch ch.G (.down t 0 j)) (hj : (j : ℕ) + 1 = D.R.m),
    HEq g (R.vX t) → ∃ e' : AE D, IsIdemSum e' (GlobalTheory.FlipTop.topPl R.toLevCh t) ∧
      IsThetaAt ch.W.ψ (symplO _ _) (heisO ch.W.ψ _ _) e' (latO (ch.G.pS (.mu t 0 j)) (ch.G.pT (.mu t 0 j)) (ch.G.latS (.mu t 0 j) : Set _) (ch.G.latT (.mu t 0 j) : Set _) fun _ => True) 1 (ch.rm.vT 0 j)
        (GlobalTheory.FlipTop.topFn ch.S.B t e' j (GlobalTheory.FlipTop.rank_col ch.G (by omega)) (GlobalTheory.FlipTop.rank_col ch.G (by omega))) g := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R F large₂ hS ch hch t j g hj hg
  obtain ⟨k, hk⟩ := j
  simp only at hj
  obtain rfl : k = D.R.m - 1 := by omega
  obtain ⟨-, e', he', hθ⟩ := hS.core.chain.vX t
  refine ⟨e', he', ?_⟩
  have hm : D.R.m - 1 < D.R.m := hk
  have hb' : D.sp.X'.rank = D.R.r + (D.R.m - 1 + 1) * D.R.t := by
    rw [hj]; exact D.sp.X'_rank
  have hN := (Comparison₂.local_factors ch.S.B t hS.core.lev).2.2 (D.R.m - 1) hm _ hb'
  have hchi : R.toLevCh.chi (D.R.m - 1 + 1) = R.toLevCh.chi D.R.m := by rw [hj]
  rw [hchi] at hN
  unfold GlobalTheory.FlipTop.topFn
  exact transport ch.G t (D.R.m - 1) _ ch.W.ψ e' (X := ch.G.node (.grid 0 (D.R.m - 1)))
    (Y := ch.G.node (.grid 0 (D.R.m - 1 + 1))) (colY_lt R.toLevCh hm) (colY_eq_m R.toLevCh _ hj)
    (colFrame_lt R.toLevCh hm) (colFrame_eq_m R.toLevCh _ hj) (hch.vac.2 _ hj) hg _ _ (Comparison₂.rank_Yc hm.le) hb' _ hN
    (hch.weil.ψ ▸ hθ)

end GlobalTheory.FlipTopChain

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowChainLastStepVectorEqThetaOfDatumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowChain_last_step_vector_eq_theta_of_datum : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} {large₂ : SizeData₂ D},
    HidaSetting large₂ R F → ∀ ch : Choice R, ch.Is → ∀ (t : T) (j : Fin D.R.m) (g : Sch ch.G (.down t 0 j)) (hj : (j : ℕ) + 1 = D.R.m),
    HEq g (R.vX t) → ∃ e' : AE D, IsIdemSum e' (GlobalTheory.FlipTop.topPl R.toLevCh t) ∧
      IsThetaAt ch.W.ψ (symplO _ _) (heisO ch.W.ψ _ _) e' (latO (ch.G.pS (.mu t 0 j)) (ch.G.pT (.mu t 0 j)) (ch.G.latS (.mu t 0 j) : Set _) (ch.G.latT (.mu t 0 j) : Set _) fun _ => True) 1 (ch.rm.vT 0 j)
        (GlobalTheory.FlipTop.topFn ch.S.B t e' j (GlobalTheory.FlipTop.rank_col ch.G (by omega)) (GlobalTheory.FlipTop.rank_col ch.G (by omega))) g := by
  first | exact @GlobalTheory.FlipTopChain.last_step_theta | exact GlobalTheory.FlipTopChain.last_step_theta | (intros; apply GlobalTheory.FlipTopChain.last_step_theta <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGridLastRowColumnCharactersDiffer
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGridLastRowColumnCharactersDiffer
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR Formalism.IndefR.Links GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.ChiGrid GlobalTheory.Unf GlobalTheory.FunObj GlobalTheory.RowUnf GlobalTheory.RowChain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowChars

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem rank_top (G : GridData L sc) {j : ℕ} (hj : j ≤ D.R.m) : (G.V (.top j)).rank = rankX D j :=
  (G.isV (X := .top j) hj (fun _ h => by cases h)).rank

theorem rank_grid (G : GridData L sc) {j : ℕ} (hj : j ≤ D.R.m) :
    (G.V (.grid D.R.m j)).rank = rankV D D.R.m j :=
  (G.isV (X := .grid D.R.m j) ⟨le_rfl, hj⟩ (fun _ h => by
    have := D.R.two_le_m; have := (Node.grid.inj h).1; omega)).rank

theorem rankX_mod (j : ℕ) : rankX D j % 2 = rankX D 0 % 2 := by
  obtain ⟨c, hc⟩ := D.R.t_odd
  have : rankX D j = rankX D 0 + 2 * (j * (c + 1)) := by
    simp only [rankX, hc]; ring
  omega

theorem rankV_row (j : ℕ) : rankV D D.R.m j + 1 + j = rankX D j + D.R.m := by
  have h : sLen D - 1 = D.R.r + 5 := by simp only [sLen]; omega
  simp only [rankV, rankX, rankP, nRk]
  rw [h]
  simp only [sLen]
  ring

theorem rankV_succ (j : ℕ) : rankV D D.R.m (j + 1) = rankV D D.R.m j + D.R.t := by
  simp only [rankV]; ring

noncomputable def chiZ (L : LevCh D T) : (AE D)ˣ →* Circle := if Odd (rankX D 0) then L.eta else L.eta⁻¹

theorem chr_top (G : GridData L sc) (t : T) {j : ℕ} (hj : j < D.R.m) :
    G.chrS (.top t j) = Formalism.IndefR.Lift.attChr (L.mu t (j + 1)) L.eta (rankX D j) ∧
    G.chrT (.top t j) = Formalism.IndefR.Lift.attChr (L.mu t (j + 1)) L.eta (rankX D (j + 1)) := by
  refine ⟨?_, ?_⟩
  · show Formalism.IndefR.Lift.attChr _ _ (G.V (.top j)).rank = _
    rw [rank_top G hj.le]; rfl
  · show Formalism.IndefR.Lift.attChr _ _ (G.V (.top (j + 1))).rank = _
    rw [rank_top G hj]; rfl

theorem chr_mu (G : GridData L sc) (t : T) {j : ℕ} (hj : j < D.R.m) :
    G.chrS (.mu t D.R.m j) = Formalism.IndefR.Lift.attChr (L.mu t (j + 1)) L.eta (rankV D D.R.m j) ∧
    G.chrT (.mu t D.R.m j) = Formalism.IndefR.Lift.attChr (L.mu t (j + 1)) L.eta (rankV D D.R.m (j + 1)) := by
  refine ⟨?_, ?_⟩
  · show Formalism.IndefR.Lift.attChr _ _ (G.V (.grid D.R.m j)).rank = _
    rw [rank_grid G hj.le]; rfl
  · show Formalism.IndefR.Lift.attChr _ _ (G.V (.grid D.R.m (j + 1))).rank = _
    rw [rank_grid G hj]; rfl

theorem chiZ_eq (G : GridData L sc) (t : T) :
    chiZ L = (G.chrS (.top t 0))⁻¹ * G.chrS (.mu t D.R.m 0) := by
  have hm := D.R.two_le_m
  obtain ⟨a, ha⟩ := D.R.m_even
  rw [(chr_top G t (by omega)).1, (chr_mu G t (by omega)).1]
  have h1 := rankV_row (D := D) 0
  simp only [chiZ, Formalism.IndefR.Lift.attChr, Nat.odd_iff]
  split_ifs <;> first | (exfalso; omega) | group

theorem rowChars {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (Wl : G.Weil) (t : T) :
    ∃ χz : (AE D)ˣ →* Circle, IsHeckeChar D χz ∧ ResEta D χz 1 ∧
      (∀ j, j < D.R.m → G.chrS (.top t j) = G.chrT (.top t j)) ∧
      (∀ j, j < D.R.m → (D.R.m - 1 - j) % 2 = 0 →
        G.chrS (.mu t D.R.m j) = G.chrS (.top t j) ∧ G.chrT (.mu t D.R.m j) = G.chrT (.top t j) * χz) ∧
      (∀ j, j < D.R.m → (D.R.m - 1 - j) % 2 = 1 →
        G.chrS (.mu t D.R.m j) = G.chrS (.top t j) * χz ∧ G.chrT (.mu t D.R.m j) = G.chrT (.top t j)) := by
  have hm := D.R.two_le_m
  obtain ⟨a, ha⟩ := D.R.m_even
  obtain ⟨c, hc⟩ := D.R.t_odd
  have HA := Wl.om_is (.top t 0) (show 0 + 1 ≤ D.R.m by omega)
  have HB := Wl.om_is (.mu t D.R.m 0) (show D.R.m ≤ D.R.m ∧ 0 + 1 ≤ D.R.m by omega)
  refine ⟨chiZ L, ?_, ?_, ?_, ?_, ?_⟩
  · rw [chiZ_eq G t]
    refine ⟨?_, fun x => ?_⟩
    · exact (HA.hecS.1.inv).mul HB.hecS.1
    · rw [MonoidHom.mul_apply, MonoidHom.inv_apply, HA.hecS.2 x, HB.hecS.2 x, inv_one, one_mul]
  · rw [chiZ_eq G t]
    have rA : (G.pS (.top t 0)).rank = rankX D 0 := rank_top G (by omega)
    have rB : (G.pS (.mu t D.R.m 0)).rank = rankV D D.R.m 0 := rank_grid G (by omega)
    have eA := HA.resS
    have eB := HB.resS
    rw [rA] at eA
    rw [rB] at eB
    refine ⟨eA.1, fun η hη x => ?_⟩
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, eA.2 η hη x, eB.2 η hη x]
    have hx : η x * η x = 1 := GlobalTheory.VolHeckeCompare.IsEta_mul_self hη x
    have hn : rankV D D.R.m 0 = rankX D 0 + 2 * (a - 1) + 1 := by
      have := rankV_row (D := D) 0
      omega
    rw [hn, pow_add, pow_add, pow_mul, pow_two, hx, one_pow, mul_one, inv_mul_cancel_left]
  · intro j hj
    rw [(chr_top G t hj).1, (chr_top G t hj).2]
    have h1 := rankX_mod (D := D) j
    have h2 := rankX_mod (D := D) (j + 1)
    simp only [Formalism.IndefR.Lift.attChr, Nat.odd_iff]
    rw [h1, h2]
  · intro j hj hp
    rw [(chr_top G t hj).1, (chr_top G t hj).2, (chr_mu G t hj).1, (chr_mu G t hj).2]
    have h1 := rankX_mod (D := D) j
    have h2 := rankX_mod (D := D) (j + 1)
    have h3 := rankV_row (D := D) j
    have h4 := rankV_succ (D := D) j
    simp only [chiZ, Formalism.IndefR.Lift.attChr, Nat.odd_iff]
    refine ⟨?_, ?_⟩ <;> split_ifs <;> first | rfl | (exfalso; omega) | group
  · intro j hj hp
    rw [(chr_top G t hj).1, (chr_top G t hj).2, (chr_mu G t hj).1, (chr_mu G t hj).2]
    have h1 := rankX_mod (D := D) j
    have h2 := rankX_mod (D := D) (j + 1)
    have h3 := rankV_row (D := D) j
    have h4 := rankV_succ (D := D) j
    simp only [chiZ, Formalism.IndefR.Lift.attChr, Nat.odd_iff]
    refine ⟨?_, ?_⟩ <;> split_ifs <;> first | rfl | (exfalso; omega) | group

end GlobalTheory.RowChars
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGridLastRowColumnCharactersDifferStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR Formalism.IndefR.Links GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.ChiGrid GlobalTheory.Unf GlobalTheory.FunObj GlobalTheory.RowUnf GlobalTheory.RowChain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaGrid_lastRow_column_characters_differ : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (Wl : G.Weil) (t : T),
    ∃ χz : (AE D)ˣ →* Circle, IsHeckeChar D χz ∧ ResEta D χz 1 ∧
      (∀ j, j < D.R.m → G.chrS (.top t j) = G.chrT (.top t j)) ∧
      (∀ j, j < D.R.m → (D.R.m - 1 - j) % 2 = 0 →
        G.chrS (.mu t D.R.m j) = G.chrS (.top t j) ∧ G.chrT (.mu t D.R.m j) = G.chrT (.top t j) * χz) ∧
      (∀ j, j < D.R.m → (D.R.m - 1 - j) % 2 = 1 →
        G.chrS (.mu t D.R.m j) = G.chrS (.top t j) * χz ∧ G.chrT (.mu t D.R.m j) = G.chrT (.top t j)) := by
  first | exact @GlobalTheory.RowChars.rowChars | exact GlobalTheory.RowChars.rowChars | (intros; apply GlobalTheory.RowChars.rowChars <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitCharacterValueAlgebraic
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInterOfSubfield
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host

namespace GlobalTheory.HeckeLocVals

def embField (E : Type) [Field E] [NumberField E] : IntermediateField ℚ ℂ :=
  ⨆ ψ : E →+* ℂ, ψ.toRatAlgHom.fieldRange

variable {E : Type} [Field E] [NumberField E]

instance embField_fd : FiniteDimensional ℚ (embField E) := by
  haveI : ∀ ψ : E →+* ℂ, FiniteDimensional ℚ ψ.toRatAlgHom.fieldRange := fun ψ =>
    ψ.toRatAlgHom.equivFieldRange.toLinearEquiv.finiteDimensional
  exact IntermediateField.finiteDimensional_iSup_of_finite

theorem emb_mem (ψ : E →+* ℂ) (k : E) : ψ k ∈ embField E :=
  le_iSup (fun ψ : E →+* ℂ => ψ.toRatAlgHom.fieldRange) ψ ⟨k, rfl⟩

theorem inf_mem_of_even {I : Type} [Fintype I] {φ : I → E →+* ℂ} {c : I → ℤ} {χ : HChar E}
    (h : χ.HasInf φ (fun i => 2 * c i)) (k : Eˣ) : ((χ.inf k : ℂˣ) : ℂ) ∈ embField E := by
  rw [h k]
  refine prod_mem fun i _ => ?_
  have h0 : φ i (k : E) ≠ 0 := by simp
  rw [zpow_mul, show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, GlobalTheory.HalfIntChars.unit_sq _ h0]
  exact zpow_mem (div_mem (emb_mem _ _) (emb_mem ((starRingEnd ℂ).comp (φ i)) (k : E))) _

theorem exists_inter_of_subfield (C : Subfield ℂ) [FiniteDimensional ℚ C] :
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ (C : Set ℂ) ⊆ M := by
  let M : IntermediateField ℚ ℂ := C.toIntermediateField fun x => by simpa using SubfieldClass.ratCast_mem C x
  let e : C ≃ₗ[ℚ] M :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun q x => Subtype.ext (by simp [Rat.smul_def])
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact ⟨M, e.finiteDimensional, fun _ h => h⟩

end GlobalTheory.HeckeLocVals

namespace GlobalTheory.HeckeLocVals

variable {E : Type} [Field E] [NumberField E]

theorem zpow_fsum {G : Type} [CommGroup G] (a : G) {ι : Type} (s : Finset ι) (f : ι → ℤ) :
    a ^ (∑ i ∈ s, f i) = ∏ i ∈ s, a ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, zpow_add, ih]

theorem algType_of_even {I : Type} [Fintype I] {φ : I → E →+* ℂ} {c : I → ℤ} {χ : HChar E}
    (h : χ.HasInf φ (fun i => 2 * c i)) : ∃ m : (E →+* ℂ) → ℤ, ∀ k : Eˣ,
      ((χ.inf k : ℂˣ) : ℂ) * ∏ ψ : E →+* ℂ, ((‖ψ (k : E)‖ : ℝ) : ℂ) ^ (((0 : ℝ)) : ℂ) = ∏ ψ : E →+* ℂ, ψ (k : E) ^ m ψ := by
  classical
  refine ⟨fun ψ => ∑ i, ((if φ i = ψ then c i else 0) - (if (starRingEnd ℂ).comp (φ i) = ψ then c i else 0)), fun k => ?_⟩
  simp only [Complex.ofReal_zero, Complex.cpow_zero, Finset.prod_const_one, mul_one]
  rw [h k]
  let u : (E →+* ℂ) → ℂˣ := fun ψ => Units.mk0 (ψ (k : E)) (by simp)
  have hu : ∀ ψ (n : ℤ), ψ (k : E) ^ n = ((u ψ ^ n : ℂˣ) : ℂ) := fun ψ n => by
    rw [Units.val_zpow_eq_zpow_val]; rfl
  have hL : ∀ i, (φ i (k : E) / ((‖φ i (k : E)‖ : ℝ) : ℂ)) ^ (2 * c i) =
      ((u (φ i) ^ c i * (u ((starRingEnd ℂ).comp (φ i)) ^ c i)⁻¹ : ℂˣ) : ℂ) := fun i => by
    rw [zpow_mul, show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, GlobalTheory.HalfIntChars.unit_sq _ (by simp), div_zpow]
    rw [Units.val_mul, Units.val_inv_eq_inv_val, ← hu, ← hu, div_eq_mul_inv]
    rfl
  simp_rw [hL, hu]
  rw [← Units.coe_prod, ← Units.coe_prod]
  congr 1
  symm
  rw [Finset.prod_congr rfl fun ψ _ => (zpow_fsum (u ψ) Finset.univ _).trans (Finset.prod_congr rfl fun i _ => zpow_sub (u ψ) _ _),
    Finset.prod_comm]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  have e1 : ∏ ψ : E →+* ℂ, u ψ ^ (if φ i = ψ then c i else 0) = u (φ i) ^ c i := by
    rw [Finset.prod_eq_single (φ i) (fun ψ _ hψ => by rw [if_neg (Ne.symm hψ), zpow_zero]) (by simp)]
    simp
  have e2 : ∏ ψ : E →+* ℂ, u ψ ^ (if (starRingEnd ℂ).comp (φ i) = ψ then c i else 0) =
      u ((starRingEnd ℂ).comp (φ i)) ^ c i := by
    rw [Finset.prod_eq_single ((starRingEnd ℂ).comp (φ i)) (fun ψ _ hψ => by rw [if_neg (Ne.symm hψ), zpow_zero]) (by simp)]
    simp
  rw [e1, e2]

theorem locVals_of_even {I : Type} [Fintype I] {φ : I → E →+* ℂ} {c : I → ℤ} {χ : HChar E}
    (h : χ.HasInf φ (fun i => 2 * c i)) :
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ ∀ v x, ((χ.loc v x : ℂˣ) : ℂ) ∈ M := by
  obtain ⟨m, hm⟩ := algType_of_even h
  obtain ⟨C, hC, hv⟩ := CharEx.algValsFin E χ 0 m hm
  obtain ⟨C', hC', hCC⟩ := exists_inter_of_subfield C
  refine ⟨C' ⊔ embField E, inferInstance, fun v x => ?_⟩
  have hle : GlobalTheory.Mem.Fld.valueField χ 0 ≤ C' ⊔ embField E := by
    rw [GlobalTheory.Mem.Fld.valueField_le_iff]
    intro w hw
    obtain ⟨y, hy⟩ := hv w hw
    exact ⟨⟨y, le_sup_left (a := C') (hCC y.2)⟩, hy⟩
  exact GlobalTheory.HeckeValField.mem_unitsIn.1
    (GlobalTheory.HeckeValField.loc_mem χ hle (fun k => le_sup_right (a := C') (inf_mem_of_even h k)) v x)

end GlobalTheory.HeckeLocVals
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.SplitCharAlg

open _root_.Formalism.L2.Host
open scoped TensorProduct

theorem isAlgebraic_loc {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] {φ : I → E →+* ℂ} {n : I → ℤ}
    {χ : HChar E} (h : χ.HasInf φ n) (v : HeightOneSpectrum (𝓞 E)) (x : (v.adicCompletion E)ˣ) :
    IsAlgebraic ℚ ((χ.loc v x : ℂˣ) : ℂ) := by
  have h2 : (χ ^ 2).HasInf φ (fun i => 2 * n i) := by
    intro k
    have e1 : (((χ ^ 2).inf k : ℂˣ) : ℂ) = ((χ.inf k : ℂˣ) : ℂ) ^ 2 := rfl
    rw [e1, h k, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun i _ => ?_
    show _ = _ ^ (2 * n i)
    rw [mul_comm, zpow_mul]
    norm_cast
  obtain ⟨M, hM, hv⟩ := GlobalTheory.HeckeLocVals.locVals_of_even h2
  have hx := hv v x
  have e2 : (((χ ^ 2).loc v x : ℂˣ) : ℂ) = ((χ.loc v x : ℂˣ) : ℂ) ^ 2 := rfl
  rw [e2] at hx
  have hint : IsIntegral ℚ (((⟨_, hx⟩ : M) : ℂ)) := (IsIntegral.of_finite ℚ (⟨_, hx⟩ : M)).map M.val
  exact IsAlgebraic.of_pow two_pos hint.isAlgebraic


open GlobalTheory.AdelicU GlobalTheory.AdelicU.Supp GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels in
theorem exists_locIdele {D : D7} {e : AE D} (he : IsSplitIdem D e) (x : (AE D)ˣ) (hx : (x : AE D) = e * x + (1 - e)) :
    ∃ (w : HeightOneSpectrum (𝓞 D.host.E)) (y : (w.adicCompletion D.host.E)ˣ), x = GlobalTheory.LFun.locIdele D.host.F w y := by
  obtain ⟨v, τ, rfl⟩ := isSplitIdem_iff_exists.1 he
  have hA : At (evFin D.host.F v) (splitIdemAd (isCMExt_host D) τ) := by
    intro u hu
    rw [Algebra.smul_def, mul_comm]
    change singleTens D.host.E v _ * _ = 0
    rw [singleTens_mul]
    have : compFin D.host.F D.host.E v (algebraMap (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) u) = 0 := by
      change (evFin D.host.F v u) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
      rw [hu, TensorProduct.zero_tmul]
    rw [this, mul_zero, map_zero]
  have h1 : (x : AE D) - 1 = splitIdemAd (isCMExt_host D) τ * ((x : AE D) - 1) := by
    rw [mul_sub, mul_one]
    nth_rewrite 1 [hx]
    ring
  refine ⟨_, _, GlobalTheory.ChrLocal.eq_locIdele_splitPrime (isCMExt_host D) τ x ?_ ?_⟩
  · intro u hu
    rw [h1, ← smul_mul_assoc, hA u hu, zero_mul]
  · obtain ⟨-, e0⟩ := GlobalTheory.LatSplit.piW_splitIdemAd (isCMExt_host D) τ
    rw [hx, map_add (f := _), map_mul, map_sub, map_one, e0]
    ring

end GlobalTheory.SplitCharAlg

namespace GlobalTheory.SplitCharAlg

end GlobalTheory.SplitCharAlg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CorePairIntegralPointPairsTriviallyHalf
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CorePairIntegralPointPairsTriviallyHalf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CoreOnto.IntDatum

theorem selfDual_core {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (i : ℕ) (hi : i < D.R.m) :
    IsSelfDualC (G.pS (.core i)) (G.latS (.core i)) ∧ IsSelfDualC (G.pT (.core i)) (G.latT (.core i)) := by
  have hV : ∀ k, k ≤ D.R.m → IsSelfDualC (G.V (.core k)) (G.Λ (.core k)) := fun k hk =>
    (G.isV (X := .core k) hk (fun j h => Node.noConfusion h)).sd
  exact ⟨isSelfDualC_neg (hV (i + 1) hi), hV i hi.le⟩

theorem finPart_mul_inv_mem {D : D7} {e : AE D} {S : Finset (Pl D.host.E)} (he : IsIdemSum e S) (s : 𝓞 D.host.E)
    (hs : ∀ P ∈ S, s ∉ P.asIdeal) (hs0 : s ≠ 0) : finPart D (e * incA D ((s : D.host.E))⁻¹) ∈ intAE D := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.sum_mul, map_sum]
  refine sum_mem fun PP hPP => ?_
  by_contra h
  exact hs PP hPP (((hes PP hPP).2 s hs0).2 h)

end GlobalTheory.CoreOnto.IntDatum

open GlobalTheory.CoreOnto.IntDatum in
theorem GlobalTheory.CoreOnto.IntDatum.psi_int : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ e : AE D, IsIdemSum e G.pl.W0 → ∀ x₀ ∈ homLat (G.Λ (.core (i + 1))) (G.Λ (.core i)), ∀ a ∈ latO (G.pS (.core i)) (G.pT (.core i)) (G.latS (.core i) : Set _) (G.latT (.core i) : Set _) (fun _ => True), IsHalf (cA D e) a → W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (e • x₀.map (incA D)) a) = 1 := by
  intro D hQ T L μ₀ hL sc G W M hM i hi e he x₀ hx₀ a ha _
  classical
  obtain ⟨hS, hT⟩ := selfDual_core G i hi
  set N : ℕ := Ideal.absNorm D.host.ccK with hNdef
  have hN : ∀ P ∈ G.pl.W0, ((N : 𝓞 D.host.E)) ∉ P.asIdeal := by
    intro P hP h
    obtain ⟨v, hv, rfl⟩ : ∃ v ∈ G.pl.S0, G.pl.w v = P := by
      unfold Places.W0 at hP
      simpa using hP
    refine GlobalTheory.AAUnit.absNorm_cmIdeal_not_mem_gridPlaces G.pl hv ?_
    rw [← G.pl.under_w hv]
    change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ (G.pl.w v).asIdeal
    rwa [map_natCast]
  have hNn : N ≠ 0 := by
    rw [hNdef]
    exact fun h => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hs0 : (N : 𝓞 D.host.E) ≠ 0 := by exact_mod_cast hNn
  have hN0 : ((N : 𝓞 D.host.E) : D.host.E) ≠ 0 := by exact_mod_cast hNn
  have hα : ((N : 𝓞 D.host.E) : D.host.E) ∈ D.host.AA := by
    have := GlobalTheory.HostClear.absNorm_mem_AA D
    push_cast
    exact this
  have h1 := GlobalTheory.AscFinWit.rat_mem_latO (P := fun _ => True) hS hT x₀ (fun y hy => hx₀ y hy) hα
  have h2 := finPart_mul_inv_mem he (N : 𝓞 D.host.E) hN hs0
  have h3 := GlobalTheory.LatticeStable.smul_mem_latO D _ _ _ _ _ _ h2 _ h1
  refine GlobalTheory.AscFinWit.psi_eq_one (P := fun _ => True) W.ψ_std hS hT ?_ ha
  convert h3 using 1
  have hu : incA D ((N : 𝓞 D.host.E) : D.host.E)⁻¹ * incA D ((N : 𝓞 D.host.E) : D.host.E) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hN0, map_one]
  ext j k
  simp only [Matrix.smul_apply, smul_eq_mul, GlobalTheory.MixModel.rat, Matrix.map_apply, map_mul]
  linear_combination (GlobalTheory.FinPlLoc.idem D fun _ => True) * e * incA D (x₀ j k) * hu.symm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CorePairIntegralPointPairsTriviallyHalfStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.corePair_integralPoint_pairs_trivially_half : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ e : AE D, IsIdemSum e G.pl.W0 → ∀ x₀ ∈ homLat (G.Λ (.core (i + 1))) (G.Λ (.core i)), ∀ a ∈ latO (G.pS (.core i)) (G.pT (.core i)) (G.latS (.core i) : Set _) (G.latT (.core i) : Set _) (fun _ => True), IsHalf (cA D e) a → W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (e • x₀.map (incA D)) a) = 1 := by
  first | exact @GlobalTheory.CoreOnto.IntDatum.psi_int | exact GlobalTheory.CoreOnto.IntDatum.psi_int | (intros; apply GlobalTheory.CoreOnto.IntDatum.psi_int <;> assumption)
end
end
