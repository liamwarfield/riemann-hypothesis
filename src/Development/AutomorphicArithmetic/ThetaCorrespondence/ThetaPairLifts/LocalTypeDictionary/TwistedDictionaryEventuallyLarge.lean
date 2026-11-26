module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DictionarySizeBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TranslatedJetsDictionary
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.CuspidalLiftSmoothAtOfCuspidalLift

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedDictionaryEventuallyLarge
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
namespace GlobalTheory.DictFree
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
end GlobalTheory.DictFree
namespace GlobalTheory.DictFree
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 MvPolynomial
end GlobalTheory.DictFree
namespace GlobalTheory.DictFree
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 MvPolynomial
theorem twisted_dictionary_eventually_large : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → Big fun ch => GlobalTheory.SumSize.DictAt ch := by
  intro hP hI
  obtain ⟨CF0, hCF⟩ := _root_.GlobalTheory.T.translated_jets_dictionary hP hI
  refine ⟨CF0, fun ε CF hCF0 => ?_⟩
  obtain ⟨x₀, hx⟩ := hCF ε CF hCF0
  refine ⟨x₀, ?_⟩
  intro D large₂ hε hx₀ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hIs hAt
  have H2 := hx D large₂ hε hx₀ Γ Pl0 T A Ks R F hS ch hIs hAt
  intro t p hp k d hk hcos hz hP' x y
  obtain ⟨Ls, Lt, κ, hLs, hLt, hκ, hdiff, hq, htr⟩ := H2 p hp x y
  obtain ⟨n, c, w, hwL, hwf, hcI, hcN, hvec⟩ := GlobalTheory.T.cosetDatumVector_finite_heisenbergCombination ch.S.toGridChoice t p hp k d hk hcos hz hP'
  choose ζ s hζ hs hjet using fun i => htr k hk (w i) (hwL i)
  refine ⟨Ls, Lt, κ, n, fun i => oppQ p (c i) * ζ i, s, hLs, hLt, hκ, hs, fun i => ?_, fun ρ => ?_, hq, fun mon => ?_⟩
  · obtain ⟨m, hm, hζm⟩ := hζ i
    have hζi : IsIntegral ℤ (ζ i) := ⟨Polynomial.X ^ m - 1, Polynomial.monic_X_pow_sub_C 1 hm.ne', by simp [hζm]⟩
    have e : (k : Qbar) ^ (D.R.f * (ch.G.pS p).rank * (ch.G.pT p).rank) * (oppQ p (c i) * ζ i) =
        oppQ p ((k : Qbar) ^ (D.R.f * (ch.G.pS p).rank * (ch.G.pT p).rank) * c i) * ζ i := by
      rw [map_mul, map_pow, map_natCast]; ring
    rw [e]
    exact ((hcI i).map (oppQ p).toIntAlgHom).mul hζi
  · have h1 : ∀ i, ‖ρ (ζ i)‖ = 1 := fun i => by
      obtain ⟨m, hm, hζm⟩ := hζ i
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 (by rw [← norm_pow, ← map_pow, hζm, map_one, norm_one])
    calc ∑ i, ‖ρ (oppQ p (c i) * ζ i)‖ = ∑ i, ‖(ρ.comp (oppQ p)) (c i)‖ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_mul, norm_mul, h1, mul_one]; rfl
      _ ≤ 1 := hcN _
  · have hvac : IsThetaFunO ch.W.ψ _ _ (ch.S.Z.vac p) := (ch.S.Z.vac_is p hp).2.theta
    show jetTab ch.W ch.S.N.frC p (ch.S.Z.vec d) _ _ mon = _
    rw [hvec, jetTab_comb ch.W ch.S.N.frC p hvac _ w hwf]
    simp only [hjet]
    set Gt := Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _)
      (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) Ls Lt) (ch.S.Z.e0 p) with hGt
    set M := MvPolynomial.monomial (mon.mapDomain (fvar ch.G p)) (1 : ℂ)
    set Per := (mon.mapDomain (fvar ch.G p)).prod fun v e => period ch.S.Z.δ v.1 ^ e
    have hGi : ∀ i, Differentiable ℂ (fun z => κ * ((ζ i : ℂ) * Formalism.MainNotions.TaylorLogMetric.U D (tor0 D D.host.ccK ch.S.Z.δ) (s i) Gt z)) :=
      fun i => ((differentiable_U _ (s i) hdiff).const_mul _).const_mul _
    have hfun : (fun z => κ * ∑ i, ((oppQ p (c i) * ζ i : Qbar) : ℂ) * Formalism.MainNotions.TaylorLogMetric.U D (tor0 D D.host.ccK ch.S.Z.δ) (s i) Gt z) =
        ∑ i ∈ Finset.univ, ((oppQ p (c i) : Qbar) : ℂ) • fun z => κ * ((ζ i : ℂ) * Formalism.MainNotions.TaylorLogMetric.U D (tor0 D D.host.ccK ch.S.Z.δ) (s i) Gt z) := by
      funext z
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      push_cast; ring
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hfun, GlobalTheory.NormSum.RepInv.applyAt0_sum _ _ _ hGi, Finset.mul_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [oppQ_coe]
    simp only [map_mul, opp_opp]
    ring
end GlobalTheory.DictFree
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_dictionary_correspondence : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → Big fun ch => GlobalTheory.SumSize.DictAt ch := by
  first | exact @_root_.GlobalTheory.DictFree.twisted_dictionary_eventually_large | exact _root_.GlobalTheory.DictFree.twisted_dictionary_eventually_large | (intros; apply _root_.GlobalTheory.DictFree.twisted_dictionary_eventually_large <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.CuspStepOfLargeFlipRun
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FlipRunDescendingCuspTransition
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.FlipRun
theorem cuspStep_down_of_large_flipRun : (∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidalSmoothAt D) → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch =>
  ∀ (t : T) (M : Vol ch.G), M.Is t → ∀ a : Arrow T, IsGridArrow D.R.m t a → (∃ i j, a = Arrow.down t i j) →
    ∀ e, IsIdemSum e (locPl ch.G t) → ∀ φ f, IsLocVec ch.W a.pair e (vacOf ch.rm a) φ f →
    ∀ (Q : PolF D (ch.G.pT a.pair).rank (ch.G.pS a.pair).rank) (F : Fn ch.G a.src), IsCuspListed ch.W.θ a.src F →
      LiftConv ch.W M a (ch.W.fock a.pair f Q) F ∧ IsCuspListed ch.W.θ a.tgt (liftA ch.W M a (ch.W.fock a.pair f Q) F) := by
  intro hS hP
  refine ⟨0, fun ε CF _ => ⟨0, ?_⟩⟩
  intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hset ch hch hsc t M hMt a ha hdown e he φ f hf Q Fn hFn
  obtain ⟨i, j, rfl⟩ := hdown
  have hgap : ch.sc.cGap = 1 := by rw [hsc]
  obtain ⟨hi, hj⟩ : i ≤ D.R.m ∧ j < D.R.m := by
    rcases ha with ⟨_, _, _, _, h⟩ | ⟨i', j', h1, h2, h⟩
    · cases h
    · cases h; exact ⟨h1, h2⟩
  obtain ⟨G, hG, hMa⟩ := GlobalTheory.GridJoin.exists_gridPre hP.discreteSeriesUpqExists hP.discreteSeriesCover
    hP.harishChandraModules hset.host hset.size hset.core hgap ch.W hch.weil
  have hRB : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R :=
    ⟨hset.core.lev, hset.core.models.inf, hset.core.models.νY, hset.core.models.νY', hset.core.models.νX⟩
  have hCS := hS D (GlobalTheory.RowSizes.sizes_of_sizeRows large₂ hset.size) Γ Pl0 T A Ks R G hRB hG
  have eA := ga_eq_of_match hMa hi (Nat.succ_le_of_lt hj)
  have eB := ga_eq_of_match hMa hi hj.le
  have hΨ := GlobalTheory.T.isThetaFunction_fock_vector_downward_arrow ch.rm t i j hi hj he hf Q
  obtain ⟨Φ, hΦ, hK⟩ := GlobalTheory.T.thetaKernel_downward_testGrid_eq_sender_grid ch.W hch.weil G hG hMa t i j hi hj eA eB _ hΨ
  have hF' := (GlobalTheory.T.isCuspTyped_testGrid_iff_sender_grid_conj hset hgap ch.W hch.weil G hG hMa i (j + 1) hi (Nat.succ_le_of_lt hj) eA Fn).1 hFn
  obtain ⟨hint, hcusp⟩ := hCS.th t i j hi hj Φ hΦ _ hF'
  have hθ : ch.W.θ = R.θ := hch.weil.θ
  have hinv : ∀ h, ∀ γ ∈ GQ (ch.G.V (.grid i (j + 1))), ∀ g,
      (fun g => ch.W.kerA (.down t i j) (ch.W.fock (.mu t i j) f Q) g h * Fn g) (γ * g) =
      (fun g => ch.W.kerA (.down t i j) (ch.W.fock (.mu t i j) f Q) g h * Fn g) g := fun h γ hγ g => by
    simp only [GlobalTheory.T.thetaKernel_downward_arrow_left_invariant ch.W t i j hi hj _ hΨ h γ hγ g, hFn.1.toIsAutFun.left γ hγ g]
  have key := fun h => GlobalTheory.T.testGrid_measure_domain_downward_eq_sender hset hgap ch.W hch.weil G hG hMa M t hMt i j hi hj eA
    (fun g => ch.W.kerA (.down t i j) (ch.W.fock (.mu t i j) f Q) g h * Fn g) (hinv h)
  have hcb : ∀ h : GA D (ch.G.V (.grid i j)), cast eB (cast eB.symm h) = h := fun h => cast_cast _ _ h
  refine ⟨fun h => ?_, ?_⟩
  · rw [← hcb h]
    refine (key _).1.1 ?_
    simpa only [hK] using hint (cast eB.symm h)
  · refine (GlobalTheory.T.isCuspTyped_testGrid_iff_sender_grid_conj hset hgap ch.W hch.weil G hG hMa i j hi hj.le eB _).2 ?_
    convert hcusp using 2 with h
    rw [liftA_apply, ← (key _).2]
    simp only [hK]
end GlobalTheory.FlipRun
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flipRun_descending_cusp_transition : (∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidalSmoothAt D) → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch =>
  ∀ (t : T) (M : Vol ch.G), M.Is t → ∀ a : Arrow T, IsGridArrow D.R.m t a → (∃ i j, a = Arrow.down t i j) →
    ∀ e, IsIdemSum e (locPl ch.G t) → ∀ φ f, IsLocVec ch.W a.pair e (vacOf ch.rm a) φ f →
    ∀ (Q : PolF D (ch.G.pT a.pair).rank (ch.G.pS a.pair).rank) (F : Fn ch.G a.src), IsCuspListed ch.W.θ a.src F →
      LiftConv ch.W M a (ch.W.fock a.pair f Q) F ∧ IsCuspListed ch.W.θ a.tgt (liftA ch.W M a (ch.W.fock a.pair f Q) F) := by
  first | exact @_root_.GlobalTheory.FlipRun.cuspStep_down_of_large_flipRun | exact _root_.GlobalTheory.FlipRun.cuspStep_down_of_large_flipRun | (intros; apply _root_.GlobalTheory.FlipRun.cuspStep_down_of_large_flipRun <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.CuspTransitionRightward
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.RightArrowCusp
theorem cuspStep_rightward : (∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidalSmoothAt D) → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch =>
  ∀ (t : T) (M : Vol ch.G), M.Is t → ∀ a : Arrow T, IsGridArrow D.R.m t a → (∃ i j, a = Arrow.right i j) →
    ∀ e, IsIdemSum e (locPl ch.G t) → ∀ φ f, IsLocVec ch.W a.pair e (vacOf ch.rm a) φ f →
    ∀ (Q : PolF D (ch.G.pT a.pair).rank (ch.G.pS a.pair).rank) (F : Fn ch.G a.src), IsCuspListed ch.W.θ a.src F →
      LiftConv ch.W M a (ch.W.fock a.pair f Q) F ∧ IsCuspListed ch.W.θ a.tgt (liftA ch.W M a (ch.W.fock a.pair f Q) F) := by
  intro hLS hP
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hSet ch hch hsc => ?_⟩⟩
  intro t M hM a ha hr e he φ f hf Q F' hF
  obtain ⟨i, j, rfl⟩ := hr
  obtain ⟨i', j', hi, hj, h'⟩ | ⟨_, _, _, _, _, h'⟩ := ha
  · cases h'
    have hcg : ch.sc.cGap = 1 := by rw [hsc]
    obtain ⟨G, hG, hMa⟩ := GlobalTheory.GridJoin.exists_gridPre hP.discreteSeriesUpqExists hP.discreteSeriesCover
      hP.harishChandraModules hSet.host hSet.size hSet.core hcg ch.W hch.weil
    have hRB : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R :=
      ⟨hSet.core.lev, hSet.core.models.inf, hSet.core.models.νY, hSet.core.models.νY', hSet.core.models.νX⟩
    have hSm := (hLS D (GlobalTheory.RowSizes.sizes_of_sizeRows large₂ hSet.size) Γ Pl0 T A Ks R G hRB hG).X t i j hi hj
    have hgm := meas_haar_fund hSet.core G hG t i j hi.le hj
    exact lift_right_of_smooth hcg ch.W hch.weil ch.rm hch.vac M t hM i j hi hj (G.V i j) (G.V (i + 1) j)
      (hMa.1.vert i j hi.le hj).sp (hMa.1.vert (i + 1) j hi hj).sp (vert_par hSet.core G hG i j hi.le hj)
      (vert_par hSet.core G hG (i + 1) j hi hj) (G.meas t i j) hgm.1 hgm.2 (G.X i j).ω (hMa.2.omX i j hi hj) hSm
      e he φ f hf Q F' hF
end GlobalTheory.RightArrowCusp
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_transition_rightward : (∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidalSmoothAt D) → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch =>
  ∀ (t : T) (M : Vol ch.G), M.Is t → ∀ a : Arrow T, IsGridArrow D.R.m t a → (∃ i j, a = Arrow.right i j) →
    ∀ e, IsIdemSum e (locPl ch.G t) → ∀ φ f, IsLocVec ch.W a.pair e (vacOf ch.rm a) φ f →
    ∀ (Q : PolF D (ch.G.pT a.pair).rank (ch.G.pS a.pair).rank) (F : Fn ch.G a.src), IsCuspListed ch.W.θ a.src F →
      LiftConv ch.W M a (ch.W.fock a.pair f Q) F ∧ IsCuspListed ch.W.θ a.tgt (liftA ch.W M a (ch.W.fock a.pair f Q) F) := by
  first | exact @_root_.GlobalTheory.RightArrowCusp.cuspStep_rightward | exact _root_.GlobalTheory.RightArrowCusp.cuspStep_rightward | (intros; apply _root_.GlobalTheory.RightArrowCusp.cuspStep_rightward <;> assumption)
end
end

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.FlipRun
theorem cuspStep_of_large_flipRun : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.RowClaim.Big fun {_} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (M : Vol ch.G), M.Is t → GlobalTheory.FlipRun.CuspStep ch.W M ch.rm t := by
  intro hLC hP
  have hS := _root_.GlobalTheory.T.cuspidal_lift_smooth_at_cusps hLC hP
  have hRight : (∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidalSmoothAt D) → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch =>
    ∀ (t : T) (M : Vol ch.G), M.Is t → ∀ a : Arrow T, IsGridArrow D.R.m t a → (∃ i j, a = Arrow.right i j) →
      ∀ e, IsIdemSum e (locPl ch.G t) → ∀ φ f, IsLocVec ch.W a.pair e (vacOf ch.rm a) φ f →
      ∀ (Q : PolF D (ch.G.pT a.pair).rank (ch.G.pS a.pair).rank) (F : Fn ch.G a.src), IsCuspListed ch.W.θ a.src F →
        LiftConv ch.W M a (ch.W.fock a.pair f Q) F ∧ IsCuspListed ch.W.θ a.tgt (liftA ch.W M a (ch.W.fock a.pair f Q) F) := by
    exact @_root_.GlobalTheory.RightArrowCusp.cuspStep_rightward
  have hDown : (∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidalSmoothAt D) → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch =>
    ∀ (t : T) (M : Vol ch.G), M.Is t → ∀ a : Arrow T, IsGridArrow D.R.m t a → (∃ i j, a = Arrow.down t i j) →
      ∀ e, IsIdemSum e (locPl ch.G t) → ∀ φ f, IsLocVec ch.W a.pair e (vacOf ch.rm a) φ f →
      ∀ (Q : PolF D (ch.G.pT a.pair).rank (ch.G.pS a.pair).rank) (F : Fn ch.G a.src), IsCuspListed ch.W.θ a.src F →
        LiftConv ch.W M a (ch.W.fock a.pair f Q) F ∧ IsCuspListed ch.W.θ a.tgt (liftA ch.W M a (ch.W.fock a.pair f Q) F) := by
    exact @_root_.GlobalTheory.FlipRun.cuspStep_down_of_large_flipRun
  refine (GlobalTheory.RowClaim.Big.and (hRight hS hP) (hDown hS hP)).imp fun CF0 h ε CF hC => ?_
  obtain ⟨x₀, h⟩ := h ε CF hC
  refine ⟨x₀, fun D large₂ e hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch hsc t M hM a ha e' he φ f hf Q F' hF => ?_⟩
  have H := h D large₂ e hx Γ Pl0 T A Ks R F s ch hch hsc
  rcases ha with ⟨i, j, hi, hj, rfl⟩ | ⟨i, j, hi, hj, rfl⟩
  · exact H.1 t M hM _ (Or.inl ⟨i, j, hi, hj, rfl⟩) ⟨i, j, rfl⟩ e' he φ f hf Q F' hF
  · exact H.2 t M hM _ (Or.inr ⟨i, j, hi, hj, rfl⟩) ⟨i, j, rfl⟩ e' he φ f hf Q F' hF
end GlobalTheory.FlipRun
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flipRun_cusp_transition : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.RowClaim.Big fun {_} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (M : Vol ch.G), M.Is t → GlobalTheory.FlipRun.CuspStep ch.W M ch.rm t := by
  first | exact @_root_.GlobalTheory.FlipRun.cuspStep_of_large_flipRun | exact _root_.GlobalTheory.FlipRun.cuspStep_of_large_flipRun | (intros; apply _root_.GlobalTheory.FlipRun.cuspStep_of_large_flipRun <;> assumption)
end
end
