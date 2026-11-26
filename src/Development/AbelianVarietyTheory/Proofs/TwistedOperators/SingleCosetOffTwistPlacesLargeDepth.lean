module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepIntegrandBesselPeriodInvariantProof
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastRowLatticesGoodPositionLargeDepth
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldedVacuaDifferByTwistValuesLargeDepth

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InBigFb
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.Unf.FB GlobalTheory.FinPl GlobalTheory.FinPl.HandInvPf
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowOneCos

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}


set_option maxHeartbeats 1000000 in
theorem flatBF_source {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} (s : StepBF ψ B J) {Ψ : WO B.V J.W → ℂ}
    (hΨ : IsThetaFunO ψ B.V J.W Ψ) {n : GA D B.V} (hn : n ∈ flagN B.d) :
    ∃ c : ℂ, c ≠ 0 ∧ flatBF s (s.om (n, 1) Ψ) = c • flatBF s Ψ := by
  have hψ := s.weil.std
  obtain ⟨u, hu, b, c, rfl⟩ := GlobalTheory.MixPer.Decomp.flag_decomp B.d hn
  obtain ⟨om', hom'⟩ := (GlobalTheory.Desc.weil_data_descend D ψ B.V J.W s.χV s.χW s.om s.weil).1 B.V₀ ρ B.d
  have FS := fun f hf => GlobalTheory.T.mixedModelFormulasWittSource_proof D ψ B.V B.V₀ J.W ρ B.d s.χV s.χW s.om om' s.weil hom' s.vS.μ s.vS.𝓕 s.vS.covol f hf
  have MV := fun x => (GlobalTheory.T.mixedCoordinates_of_thetaFunction_are_thetaFunctions D ψ hψ).1 B.V B.V₀ J.W ρ B.d s.vS.μ s.vS.𝓕 s.vS.covol Ψ hΨ x
  have hdet : Matrix.GeneralLinearGroup.det u = 1 := by
    have bt : Matrix.BlockTriangular u.1 id := fun a b h => (hu a b).1 h
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_of_isUpperTriangular bt, Units.val_one]
    exact Finset.prod_eq_one fun i _ => (hu i i).2
  have hmod : GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod J.W.rank u = 1 := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod, hdet, map_one, NNReal.coe_one, Real.one_rpow]
  have h1 := s.weil.om_pres (B.d.nC c, 1) Ψ hΨ
  have h2 := s.weil.om_pres (B.d.nB b, 1) _ h1
  have e : s.om (B.d.levi u * (B.d.nB b * B.d.nC c), 1) Ψ =
      s.om (B.d.levi u, 1) (s.om (B.d.nB b, 1) (s.om (B.d.nC c, 1) Ψ)) := by
    rw [← om_mul, ← om_mul, mul_assoc, mul_one, mul_one]
  let u' : UX D ρ := ⟨u, hu⟩
  have hq : ∀ X : Mx D ρ ρ, B.d.qS J.W c (xZero J.d ⬝ X) = 0 := fun X => by
    have h0 : adj J.d.jX ⬝ (gA J.W ⬝ (J.d.jX ⬝ X)) = 0 := by
      rw [← Matrix.mul_assoc, ← J.d.pY_eq, ← Matrix.mul_assoc, J.d.pY_jX, Matrix.zero_mul]
    rw [HypDec.qS, HypDec.symplOH_extX_extY, pairS, xZero, adj_mul, adj_mul, Matrix.mul_assoc, Matrix.mul_assoc, h0,
      Matrix.mul_zero, Matrix.mul_zero, trace_zero, map_zero]
  set y := yZero B.V₀ ρ (vecB B.o B.ζ) with hy
  set k : ℂ := ψ (Algebra.trace (AF D.host.F) (AE D) (ell D ρ ⬝ᵥ b *ᵥ ratV (vecB B.o B.ζ))) with hk
  have key : ∀ v : UX D ρ,
      evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (B.d.levi u * (B.d.nB b * B.d.nC c), 1) Ψ) (xZero J.d ⬝ v.1.1) y =
        k • evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xZero J.d ⬝ (v * u').1.1) y := by
    intro v
    have ex : xZero J.d ⬝ v.1.1 ⬝ u.1 = xZero J.d ⬝ (v * u').1.1 := by
      rw [Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc]
    have t1 := (FS _ h2).levi u (xZero J.d ⬝ v.1.1)
    rw [hdet, hmod, map_one, inv_one, Circle.coe_one, Complex.ofReal_one, mul_one, one_smul, ex] at t1
    have t2 := (FS _ h1).unip b (xZero J.d ⬝ (v * u').1.1)
    rw [Matrix.mul_assoc (xZero J.d)] at t2
    have t3 : B.d.mixS J.W ψ s.vS.μ s.vS.𝓕 (s.om (B.d.nC c, 1) Ψ) (xZero J.d ⬝ (v * u').1.1) =
        ψ (B.d.qS J.W c (xZero J.d ⬝ (v * u').1.1)) • B.d.mixS J.W ψ s.vS.μ s.vS.𝓕 Ψ (xZero J.d ⬝ (v * u').1.1) :=
      (FS _ hΨ).centre c _
    rw [hq, AddChar.map_zero_eq_one, one_smul] at t3
    rw [e]
    change (_root_.I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.target J.d) B.V₀ ψ s.vT.μ s.vT.𝓕
      (B.d.mixS J.W ψ s.vS.μ s.vS.𝓕 _ _) y =
      k • (_root_.I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.target J.d) B.V₀ ψ s.vT.μ s.vT.𝓕
        (B.d.mixS J.W ψ s.vS.μ s.vS.𝓕 Ψ _) y
    change B.d.mixS J.W ψ s.vS.μ s.vS.𝓕 _ _ = B.d.mixS J.W ψ s.vS.μ s.vS.𝓕 _ _ at t1
    change B.d.mixS J.W ψ s.vS.μ s.vS.𝓕 _ _ = heisO ψ B.V₀ J.W _ (B.d.mixS J.W ψ s.vS.μ s.vS.𝓕 _ _) at t2
    rw [t1, t2, t3]
    have t4 := (GlobalTheory.T.heisenbergThetaMixedModelTarget_of_mixedModel D ψ hψ B.V₀ J.W J.W₀ ρ J.d s.vT.μ s.vT.𝓕 s.vT.covol _ (MV (xZero J.d ⬝ (v * u').1.1))).1
      ((v * u').1.1 ⬝ b) y
    have t5 : symplO B.V₀ J.W (J.d.incAdj B.V₀ y) (J.d.incX B.V₀ ((v * u').1.1 ⬝ b)) =
        Algebra.trace (AF D.host.F) (AE D) (ell D ρ ⬝ᵥ b *ᵥ ratV (vecB B.o B.ζ)) := by
      refine (symplO_yZero J.d _ _).trans ?_
      rw [← Matrix.mulVec_mulVec, dotProduct_mulVec, ell_vecMul (v * u').2]
    rw [t5] at t4
    exact t4
  have : BorelSpace (UX D ρ) := ⟨rfl⟩
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.UnitU.topology D ρ
  have := (GlobalTheory.UnitU.isUnitU_exists_unique_rightInvariant D ρ).2.2 _ s.vU.unit
  have hmul : ∀ v : UX D ρ, psiUni ψ (v * u').1 = psiUni ψ v.1 * psiUni ψ u := fun v => by
    rw [← ThLaws.psiFlag_levi ψ J.d, ← ThLaws.psiFlag_levi ψ J.d, ← ThLaws.psiFlag_levi ψ J.d, Subgroup.coe_mul, map_mul,
      psiFlag_mul J.d ψ (J.d.levi_mem_NFlag v.2) (J.d.levi_mem_NFlag hu)]
  have hu1 : psiUni ψ u * star (psiUni ψ u) = 1 := mul_star_psi hψ _
  refine ⟨psiUni ψ u * k, mul_ne_zero (left_ne_zero_of_mul_eq_one hu1) (GlobalTheory.FlatRInv.addChar_ne_zero ψ _), ?_⟩
  funext w
  simp only [Pi.smul_apply, smul_eq_mul]
  change ∫ v, star (psiUni ψ v.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕
      (s.om (B.d.levi u * (B.d.nB b * B.d.nC c), 1) Ψ) (xZero J.d ⬝ v.1.1) y w ∂s.vU.ν = _ *
    ∫ v, star (psiUni ψ v.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xZero J.d ⬝ v.1.1) y w ∂s.vU.ν
  conv_rhs => rw [← integral_mul_right_eq_self _ u', ← integral_const_mul]
  congr 1
  funext v
  rw [key, hmul, star_mul']
  simp only [Pi.smul_apply, smul_eq_mul]
  generalize evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xZero J.d ⬝ (v * u').1.1) y w = z
  linear_combination (-(star (psiUni ψ v.1) * k * z)) * hu1

theorem flatBF_src_ne {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} (s : StepBF ψ B J) {Ψ : WO B.V J.W → ℂ}
    (hΨ : IsThetaFunO ψ B.V J.W Ψ) {r : GA D B.V} (hr : r ∈ besGrp B.d B.o) (h : flatBF s (s.om (r, 1) Ψ) ≠ 0) :
    flatBF s Ψ ≠ 0 := by
  intro h0
  apply h
  obtain ⟨n, hn, a, rfl⟩ := (GlobalTheory.CharLaws.mem_besGrp B.d B.o r).1 hr
  obtain ⟨om', hom'⟩ := (GlobalTheory.Desc.weil_data_descend D ψ B.V J.W s.χV s.χW s.om s.weil).1 B.V₀ ρ B.d
  have e := GlobalTheory.T.besselToJacobiFlatSchwartz_equivariant D ψ ρ B J s om' hom' Ψ hΨ a 1 (one_mem _) 1
  rw [map_one, mul_one, h0, (GlobalTheory.FlatRInv.opA_eq_zero_iff ψ J.d B.o B.ζ s.om₀ 1 1 0).2 rfl, map_zero, smul_zero] at e
  obtain ⟨c, -, hc⟩ := flatBF_source s (s.weil.om_pres (embA B.d B.o a, 1) Ψ hΨ) hn
  rw [← om_mul, one_mul, e, smul_zero] at hc
  exact hc

theorem flatFB_src_ne {σ : ℕ} {J : JacLev D (σ + 1)} {B : BesLev D σ} (s : StepFB ψ J B) {Ψ : WO J.W B.V → ℂ}
    (hΨ : IsThetaFunO ψ J.W B.V Ψ) {r : GA D J.W} (hr : r ∈ jacGrp J.d) (h : flatFB s (s.om (r, 1) Ψ) ≠ 0) :
    flatFB s Ψ ≠ 0 := by
  intro h0
  apply h
  obtain ⟨n, hn, a, rfl⟩ := (GlobalTheory.MixPer.Decomp.mem_jacGrp_iff J.d).1 hr
  have e := GlobalTheory.T.jacobiToBesselFlat_intertwines_weilAction D (GlobalTheory.Desc.weil_data_descend D) ψ σ J B s Ψ hΨ a 1
  rw [map_one, h0, map_zero] at e
  have hc := flatFB_source s (s.weil.om_pres (J.d.emb0 a, 1) Ψ hΨ) hn
  rw [← om_mul, one_mul, e, (GlobalTheory.FlatRInv.heisO_eq_zero_iff ψ _ _ _ 0).2 rfl, smul_zero] at hc
  exact hc

theorem inBig_bf {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} (s : StepBF ψ B J) {LV : Lat B.V} {LV₀ : Lat B.V₀} {LW : Lat J.W}
    {LW₀ : Lat J.W₀} {P : Pl D → Prop} (good : ∀ v, P v → GoodBF ψ B J LV LV₀ LW LW₀ v) (unr : ∀ v, P v → UnrAt s v)
    (sd : IsSelfDualC J.W LW) {Φ : WO B.V J.W → ℂ} (hΦ : Vac ψ B.V J.W LV LW P Φ) {g : GA D B.V} {h : GA D J.W}
    (hg : InBig B.V (besGrp B.d B.o) LV P g) (hne : flatBF s (s.om (g, h) Φ) ≠ 0) : InBig J.W (jacGrp J.d) LW P h := by
  obtain ⟨r, hr, -, g', hg', κ, hκ, rfl⟩ := hg
  obtain ⟨h1, h2⟩ := GlobalTheory.T.besselToJacobiFirstStepFlatMapSupport_all D ψ ρ B J s LV LV₀ LW LW₀ P good unr sd Φ hΦ
  refine (h2 g' hg').1 h (flatBF_src_ne s (s.weil.om_pres _ _ hΦ.1) hr ?_)
  have e : s.om (r * g' * κ, h) Φ = s.om (r, 1) (s.om (g', h) (s.om (κ, 1) Φ)) := by
    rw [← om_mul, ← om_mul, one_mul, mul_one]
  rwa [e, h1 κ 1 hκ ⟨one_mem _, fun y _ => by rw [mt_one, Matrix.one_mulVec]⟩] at hne

theorem inBig_fb {σ : ℕ} {J : JacLev D (σ + 1)} {B : BesLev D σ} (s : StepFB ψ J B) {LV : Lat J.W} {LV₀ : Lat J.W₀} {LW : Lat B.V}
    {LW₀ : Lat B.V₀} {P : Pl D → Prop} (ad : ∀ v, P v → AdaptFB ψ J B LV LV₀ LW LW₀ v) (unr : ∀ v, P v → UnrAt s v)
    (spl : ∀ v, P v → SplitCore B LW₀ v) (sdV : IsSelfDualC J.W LV) (sd : IsSelfDualC B.V LW) {Φ : WO J.W B.V → ℂ}
    (hΦ : Vac ψ J.W B.V LV LW P Φ) {g : GA D J.W} {h : GA D B.V}
    (hg : InBig J.W (jacGrp J.d) LV P g) (hne : flatFB s (s.om (g, h) Φ) ≠ 0) : InBig B.V (besGrp B.d B.o) LW P h := by
  obtain ⟨r, hr, -, g', hg', κ, hκ, rfl⟩ := hg
  have tameP : ∀ v, P v → Tame D v := fun v hv => (ad v hv).tame
  have h1 := GlobalTheory.T.selfDualLatticeStabilizers_fix_weilVacuum_on_placeSet D ψ J.W B.V s.χV s.χW s.om s.weil LV LW sdV sd P
    (fun v hv => ⟨tameP v hv, (unr v hv).1, (unr v hv).2⟩) Φ hΦ κ 1 hκ ⟨one_mem _, fun y _ => by rw [mt_one, Matrix.one_mulVec]⟩
  have e : s.om (r * g' * κ, h) Φ = s.om (r, 1) (s.om (g', h) (s.om (κ, 1) Φ)) := by
    rw [← om_mul, ← om_mul, one_mul, mul_one]
  rw [e, h1] at hne
  replace hne := flatFB_src_ne s (s.weil.om_pres _ _ hΦ.1) hr hne
  refine GlobalTheory.T.placewise_to_adelicDecomposition_forall D B.V LW P sd (besGrp B.d B.o) h fun v hv => ?_
  obtain ⟨x, hx, h', hh', rfl⟩ := GlobalTheory.T.unitaryAdelic_eq_componentAtPlace_mul_offPlace D B.V h v
  refine ⟨x, hx, h', hh', rfl, ?_⟩
  have hΦv : Vac ψ J.W B.V LV LW (· = v) Φ :=
    ((GlobalTheory.T.latticeVacuum_iff_placewise D ψ J.W B.V s.χV s.χW s.om s.weil LV LW sdV sd P tameP Φ).1.mp hΦ).2 v hv
  have hf : Vac ψ J.W B.V LV LW (· = v) (s.om (g', h') Φ) :=
    (GlobalTheory.T.latticeVacuum_iff_placewise D ψ J.W B.V s.χV s.χW s.om s.weil LV LW sdV sd (· = v)
      (fun w hw => hw ▸ tameP v hv) Φ).2.1 hΦv g' (GlobalTheory.T.unitaryAdelicTrivialAtPlacesSubgroup_antitone D J.W P (· = v) (fun w hw => hw ▸ hv) hg') h' hh'
  have hom : s.om (g', x * h') Φ = s.om (1, x) (s.om (g', h') Φ) := by rw [← om_mul, one_mul]
  rw [hom] at hne
  obtain ⟨n, hnF, hnv, γ, hγ, k, hk, hdec, hγp⟩ :=
    (GlobalTheory.T.jacobiToBesselFlatMapSupport_proof D ψ σ J B s LV LV₀ LW LW₀ v (ad v hv) (unr v hv) (flatFB s)
      ((GlobalTheory.FlatLawsDuality.flatLaws_all D ψ (· = v)).2 σ J B s) ((GlobalTheory.T.flatMaps_heisenbergTranslation_law D ψ (· = v)).2 σ J B s) _ hf).2 x hx hne
  obtain ⟨a₀, ha₀, κ₀, hκ₀, rfl⟩ := GlobalTheory.T.unitNormVectors_one_orbit_selfDualLattice_split D σ B LW₀ v (tameP v hv) (ad v hv).sdW₀ (spl v hv) γ hγ hγp
  obtain ⟨r', hr', hrv, κ', hκ', heq⟩ := GlobalTheory.T.besselUnfolding_orbit_mem_parabolic_mul_stabiliser D σ B LW LW₀ v (ad v hv).monoW n hnF hnv a₀ ha₀ κ₀ hκ₀ k hk
  exact ⟨r', hr', hrv, κ', hκ', hdec.trans heq⟩

end GlobalTheory.RowOneCos

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SingleCosetOffTwistPlacesLargeDepth
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowOneCos

open GlobalTheory.FinPl (Lat idAt idOff grpAt grpOff latV InK Moves Vac InBig Tame UnrAt SplitCore)
open GlobalTheory.Core.Mi.FrameMove (mulVec_mem_ideal hat_iff_of_moves)

section Lattices

theorem cell_eq {H : Type} [Group H] {h b r g κ x y : H} (h1 : h * b⁻¹ = r * g * κ) (h2 : b⁻¹ * g * b = x * y)
    (h3 : y * (b * x) = b * x * y) : h = r * y * (b * x) * (b⁻¹ * κ * b) := by
  have e2 : g = b * (x * y) * b⁻¹ := by rw [← h2]; group
  rw [mul_assoc r y, h3, mul_inv_eq_iff_eq_mul.1 h1, e2]
  group

variable {D : D7}

theorem latV_iff_of_le (S : HSp D) (L : Lat S) {P Q : GlobalTheory.FinPl.Pl D → Prop} (h : ∀ v, Q v → P v) {y : Fin S.rank → AE D}
    (hy : ∀ i, y i ∈ idAt D Q) : y ∈ latV S L P ↔ y ∈ latV S L Q :=
  ⟨fun h' => GlobalTheory.HatLatV.mem_latV_of_hatL D S L Q y hy (GlobalTheory.LatVHat.latV_mem_hatL D S L P y h'),
    fun h' => GlobalTheory.HatLatV.mem_latV_of_hatL D S L P y (fun i => GlobalTheory.FinPl.KSplit.idAt_mono h (hy i))
      (GlobalTheory.LatVHat.latV_mem_hatL D S L Q y h')⟩

theorem moves_of_le {S : HSp D} {g : GA D S} {L M : Lat S} {P Q : GlobalTheory.FinPl.Pl D → Prop} (h : ∀ v, Q v → P v)
    (hm : Moves S g L M P) : Moves S g L M Q := fun y hy => by
  rw [← latV_iff_of_le S L h hy, ← latV_iff_of_le S M h (mulVec_mem_ideal _ hy)]
  exact hm y fun i => GlobalTheory.FinPl.KSplit.idAt_mono h (hy i)

theorem moves_all_of_inK {S : HSp D} {L : Lat S} (hL : IsSelfDualC S L) {P : GlobalTheory.FinPl.Pl D → Prop} {κ : GA D S}
    (hκ : InK S L P κ) : Moves S κ L L fun _ => True := by
  refine (GlobalTheory.FinPl.movesLocal D S L hL κ).2 fun v => ?_
  by_cases hv : P v
  · exact moves_of_le (fun w hw => hw ▸ hv) hκ.2
  · exact GlobalTheory.fixes_latV_of_mem_grpOff D S L _ κ
      (GlobalTheory.FinPl.SetCut.grpAt_le_grpOff S P (· = v) (fun p hp hpv => hv (hpv ▸ hp)) hκ.1)

variable {e : AE D} {Z : Finset (Pl D.host.E)} {P : GlobalTheory.FinPl.Pl D → Prop}

theorem grpOff_of_suppAt (he : IsIdemSum e Z) (hP : ∀ v, P v ↔ ∀ w ∈ Z, w.under (𝓞 D.host.F) ≠ v) {V : HSp D} {g : GA D V}
    (hg : SuppAt e V g) : g ∈ grpOff V P := by
  have h1 := GlobalTheory.StepComb.idemSum_mem_idAt he
  obtain ⟨ε, -, hc, -, hAt, -⟩ := (GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D fun p => ∃ PP ∈ Z, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)).1
  have h2 : cA D e ∈ idAt D fun p => ∃ PP ∈ Z, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) := by
    rw [hAt, ← hc, ← map_mul, (hAt e).1 h1]
  refine (GlobalTheory.FinPl.SetCut.mem_grpOff_iff_parts V P g).2 fun i j w hw => ?_
  rw [← hg i j, map_mul, ((GlobalTheory.FinPl.mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere D _ _).1 (add_mem h1 h2)).2 w, zero_mul]
  rintro ⟨PP, hPP, rfl⟩
  exact (hP _).1 hw PP hPP rfl

theorem suppAt_of_grpAt (he : IsIdemSum e Z) (hP : ∀ v, P v ↔ ∀ w ∈ Z, w.under (𝓞 D.host.F) ≠ v) {V : HSp D} {g : GA D V}
    (hg : g ∈ grpAt V fun v => ¬ P v) : SuppAt e V g := by
  intro i j
  obtain ⟨ε, -, -, -, hAt, hOff⟩ := (GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D fun v => ¬ P v).1
  have hy : (mt V g - 1) i j ∈ idAt D fun v => ¬ P v :=
    (GlobalTheory.FinPl.mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere D _ _).2 ((GlobalTheory.FinPl.SetCut.mem_grpAt_iff_parts V _ g).1 hg i j)
  generalize (mt V g - 1) i j = y at hy
  have h1 : (1 - (e + cA D e)) * y ∈ idAt D fun v => ¬ P v := Ideal.mul_mem_left _ _ hy
  have h2 : (1 - (e + cA D e)) * y ∈ idOff D fun v => ¬ P v := by
    refine Ideal.mul_mem_right _ _ ((GlobalTheory.FinPl.SetCut.mem_idOff_iff _ _).2 fun w hw => ?_)
    rw [hP] at hw
    push_neg at hw
    obtain ⟨PP, hPP, rfl⟩ := hw
    rw [RingHom.map_sub, RingHom.map_one, ← GlobalTheory.FinPl.LatMem.compFin_eq_compAt, GlobalTheory.CompFinIdemSum.compFin_add_cA_eq_one Z e he PP hPP, sub_self]
  have h3 := ((hAt _).1 h1).symm.trans ((hOff _).1 h2)
  linear_combination -h3

theorem cell_of_inBig (he : IsIdemSum e Z) (hP : ∀ v, P v ↔ ∀ w ∈ Z, w.under (𝓞 D.host.F) ≠ v) {V : HSp D} {Λ N : Lat V}
    (hN : IsSelfDualC V N) {R : Subgroup (GA D V)} {b h : GA D V} (hb : b ∈ GfC V) (hm : Moves V b Λ N fun _ => True)
    (hh : InBig V R N P (h * b⁻¹)) :
    ∃ r ∈ R, ∃ a ∈ GinfC V, ∃ x, SuppAt e V x ∧ ∃ k ∈ GfC V,
      (∀ z, z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ ↔ (Lev.finE V k).val *ᵥ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) ∧ h = r * a * (b * x) * k := by
  obtain ⟨r, hr, -, g, hg, κ, hκ, eq⟩ := hh
  have hg' : b⁻¹ * g * b ∈ grpOff V P := by
    have := (MonoidHom.normal_ker _).conj_mem g hg b⁻¹
    rwa [inv_inv] at this
  obtain ⟨x, hx, y, hy, exy⟩ := ((GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D fun v => ¬ P v).2 V).1 (b⁻¹ * g * b)
  have hy' : y ∈ grpOff V P := by
    have e1 : y = x⁻¹ * (b⁻¹ * g * b) := by rw [exy, inv_mul_cancel_left]
    rw [e1]
    exact mul_mem (inv_mem (GlobalTheory.FinPl.SetCut.grpAt_le_grpOff V _ P (fun _ hp => hp) hx)) hg'
  have hyi : y ∈ GinfC V := by
    refine GlobalTheory.FinPl.OffInh.mem_GinfC_of_all (P := fun _ => True) (fun _ => trivial)
      ((GlobalTheory.FinPl.SetCut.mem_grpOff_iff_parts V _ y).2 fun i j w _ => ?_)
    by_cases hw : P w
    · exact (GlobalTheory.FinPl.SetCut.mem_grpOff_iff_parts V _ y).1 hy' i j w hw
    · exact (GlobalTheory.FinPl.SetCut.mem_grpOff_iff_parts V _ y).1 hy i j w hw
  have hbx : b * x ∈ GfC V := mul_mem hb (GlobalTheory.FinPl.SetCut.grpAt_le_GfC V _ hx)
  refine ⟨r, hr, y, hyi, x, suppAt_of_grpAt he hP hx, b⁻¹ * κ * b,
    mul_mem (mul_mem (inv_mem hb) (GlobalTheory.FinPl.SetCut.grpAt_le_GfC V _ hκ.1)) hb, fun z => ?_, ?_⟩
  · have e1 : (Lev.finE V b).val *ᵥ ((Lev.finE V (b⁻¹ * κ * b)).val *ᵥ z) = (Lev.finE V κ).val *ᵥ ((Lev.finE V b).val *ᵥ z) := by
      have e0 : Lev.finE V b * Lev.finE V (b⁻¹ * κ * b) = Lev.finE V κ * Lev.finE V b := by
        rw [← MonoidHom.map_mul, ← MonoidHom.map_mul, ← mul_assoc, mul_inv_cancel_left]
      generalize Lev.finE V (b⁻¹ * κ * b) = c at e0
      generalize Lev.finE V b = b₁ at e0
      generalize Lev.finE V κ = κ₁ at e0
      exact (Matrix.mulVec_mulVec z b₁.val c.val).trans ((congrArg (fun u : GL _ _ => u.val *ᵥ z) e0).trans
        (Matrix.mulVec_mulVec z κ₁.val b₁.val).symm)
    refine (hat_iff_of_moves V b Λ N hm z).trans ((hat_iff_of_moves V κ N N (moves_all_of_inK hN hκ) _).trans ?_)
    exact (Iff.of_eq (congrArg (fun u => u ∈ Formalism.L2.Herm.hatL (F := D.host.F) N) e1.symm)).trans
      (hat_iff_of_moves V b Λ N hm _).symm
  · have hc : y * (b * x) = b * x * y := GlobalTheory.PointAtPlaceHom.comm_of_mem V hyi hbx
    exact cell_eq eq exy hc

end Lattices

section Row

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc)

theorem rowGrp_bes (j σ : ℕ) (hj : j + 2 * σ + 2 = D.R.m) :
    rowGrp G j = besGrp (besDecAt G j σ hj) (GlobalTheory.OrthSumExists.orthDecHsum D _ _) := by
  obtain rfl : σ = (D.R.m - 2 - j) / 2 := by omega
  exact (dif_neg (by omega)).trans (dif_pos hj)

theorem rowGrp_jac (j σ : ℕ) (hj : j + 2 * σ + 1 = D.R.m) :
    rowGrp G j = jacGrp (rowJac G j (by omega) σ (by omega)) := by
  obtain rfl : σ = (D.R.m - 1 - j) / 2 := by omega
  exact dif_pos hj

theorem contr_ne_zero {ρ σ : ℕ} {B : GlobalTheory.Unf.BesLev D ρ} {B' : GlobalTheory.Unf.BesLev D σ} {l : GlobalTheory.Unf.Link B B'.L B'.ζ} {S : HSp D}
    {vL : GlobalTheory.Unf.VolM D B'.L.rank S.rank} {Ξ₁ : WO B.V₀ S → ℂ} {Ξ₂ : WO S B'.V₀ → ℂ}
    (h : GlobalTheory.Unf.contr l S vL Ξ₁ Ξ₂ ≠ 0) : Ξ₁ ≠ 0 ∧ Ξ₂ ≠ 0 := by
  constructor
  all_goals
    rintro rfl
    apply h
    funext u v
    simp [GlobalTheory.Unf.contr]

theorem sd_row (j : ℕ) (hj : j ≤ D.R.m) : IsSelfDualC (G.V (.grid D.R.m j)) (G.Λ (.grid D.R.m j)) :=
  (G.isV (X := .grid D.R.m j) ⟨le_rfl, hj⟩ fun k hk => by
    have := D.R.two_le_m
    simp only [Node.grid.injEq] at hk
    omega).sd

theorem sd_top (j : ℕ) (hj : j ≤ D.R.m) : IsSelfDualC (G.V (.top j)) (G.Λ (.top j)) :=
  (G.isV (X := .top j) hj fun _ hk => by cases hk).sd


variable {G} in
theorem vac_moved (W : G.Weil) (ρ : RealMatch W) (t : T) (j : ℕ) (hj : j < D.R.m) {e : AE D} (he : IsIdemSum e (locPl G t))
    (Sf : Finset (GlobalTheory.FinPl.Pl D)) (hS : ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ∈ Sf) (tame : ∀ v, Tame D v)
    {φ f : WO (G.V (.grid D.R.m j)) (G.V (.grid D.R.m (j + 1))) → ℂ}
    (hf : IsLocVec W (.mu t D.R.m j) e (ρ.vT D.R.m j) φ f) (Q) {N : Lat (G.V (.grid D.R.m j))}
    {N' : Lat (G.V (.grid D.R.m (j + 1)))} (hN : IsSelfDualC _ N) (hN' : IsSelfDualC _ N') {b b'}
    (hb : Moves _ b (G.Λ (.grid D.R.m j)) N fun _ => True) (hb' : Moves _ b' (G.Λ (.grid D.R.m (j + 1))) N' fun _ => True) :
    Vac W.ψ _ _ N N' (· ∉ Sf) (W.om (.mu t D.R.m j) (b, b') (W.fock (.mu t D.R.m j) f Q)) := by
  have hth := fun Q => GlobalTheory.DownFock.isThetaFunO_fock_down ρ t D.R.m j le_rfl hj he hf Q
  have h0 : Vac W.ψ _ _ (G.Λ (.grid D.R.m j)) (G.Λ (.grid D.R.m (j + 1))) (· ∉ Sf) (W.fock (.mu t D.R.m j) f Q) :=
    ⟨hth Q, GlobalTheory.FockSph.isLatVac_pureTensorO_off W.θ_is _ _ (ρ.vT_is t D.R.m j le_rfl hj) he hf.2 Sf hS hth Q⟩
  exact (GlobalTheory.T.latticeVacuum_iff_placewise D W.ψ _ _ _ _ _ (W.om_is (.mu t D.R.m j) ⟨le_rfl, hj⟩) _ _ (sd_row G j hj.le) (sd_row G (j + 1) hj)
    (· ∉ Sf) (fun v _ => tame v) _).2.2 h0 b b' N N' hN hN' (moves_of_le (fun _ _ => trivial) hb)
    (moves_of_le (fun _ _ => trivial) hb')

end Row

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)


set_option maxHeartbeats 1000000 in
theorem offAt_of_shape (hS : ShapeAt ch) (hB : ∀ t, ∃ b, IsBase t ch.S.B b) : OffAt ch := by
  classical
  intro t Φ τ hτ M hM d hd P h h0 hne
  obtain ⟨N, N₀, LL, LZ, hmv, -, -, hsh⟩ := hS
  obtain ⟨b, hb⟩ := hB t
  replace hmv := hmv t b hb
  replace hsh := hsh t M hM
  obtain ⟨e, he, φ, hφ, -⟩ := hτ
  obtain ⟨Sf, hSf⟩ : ∃ Sf : Finset (GlobalTheory.FinPl.Pl D), ∀ v, v ∉ Sf ↔ ∀ w ∈ locPl ch.G t, w.under (𝓞 D.host.F) ≠ v :=
    ⟨(locPl ch.G t).image fun w => w.under (𝓞 D.host.F), fun v => by simp⟩
  have hSf' : ∀ w ∈ locPl ch.G t, w.under (𝓞 D.host.F) ∈ Sf := fun w hw => by
    by_contra hn
    exact (hSf _).1 hn w hw rfl
  obtain ⟨v₀⟩ : Nonempty (GlobalTheory.FinPl.Pl D) := by
    obtain ⟨I, hI⟩ := Ideal.exists_maximal (𝓞 D.host.F)
    exact ⟨⟨I, hI.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hI (RingOfIntegers.not_isField _)⟩⟩
  have tame : ∀ v, Tame D v := fun v => (hsh 0 _ top_idx (GlobalTheory.Unf.Inhab.nonempty_volN _).some v).2.2.1.tame
  obtain ⟨m', hm'⟩ := D.R.m_even
  have sdN : ∀ j, j < D.R.m → IsSelfDualC _ (N j) := by
    intro j hj
    rcases Nat.even_or_odd' j with ⟨k, hk | hk⟩
    · exact (hsh j (m' - k - 1) (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some v₀).2.2.1.sdV
    · subst hk
      exact (hsh (2 * k) (m' - k - 1) (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some v₀).2.2.1.sdW
  have vac : ∀ j (hj : j + 1 < D.R.m), Vac ch.W.ψ _ _ (N j) (N (j + 1)) (· ∉ Sf)
      (ch.W.om (.mu t D.R.m j) (b j, b (j + 1)) (fockD ch.W t d.2 P ⟨j, by omega⟩)) := fun j hj =>
    vac_moved ch.W ch.rm t j (by omega) he Sf hSf' tame ((hφ d hd).2 ⟨j, by omega⟩) _ (sdN j (by omega)) (sdN (j + 1) hj)
      (hmv j (by omega)) (hmv (j + 1) hj.le)
  have move : ∀ j f, ch.W.om (.mu t D.R.m j) (h j, h (j + 1)) f =
      ch.W.om (.mu t D.R.m j) (h j * (b j)⁻¹, h (j + 1) * (b (j + 1))⁻¹) (ch.W.om (.mu t D.R.m j) (b j, b (j + 1)) f) := fun j f => by
    rw [← GlobalTheory.FinPl.HandInvPf.om_mul, inv_mul_cancel_right, inv_mul_cancel_right]
  obtain ⟨Inv, hInv⟩ : ∃ Inv : ℕ → Prop, ∀ j, Inv j ↔ InBig _ (rowGrp ch.G j) (N j) (· ∉ Sf) (h j * (b j)⁻¹) :=
    ⟨_, fun _ => Iff.rfl⟩
  have step : ∀ j, Even j → j + 4 ≤ D.R.m → Inv j → Inv (j + 1) ∧ Inv (j + 1 + 1) := by
    intro j hje hj hI
    have hj' : j + 2 * ((D.R.m - 4 - j) / 2 + 1) + 2 = D.R.m := by
      obtain ⟨k, hk⟩ := hje
      omega
    have hc := hne j hje (by omega)
    have hj0 : ¬ j + 2 * 0 + 2 = D.R.m := by omega
    rw [show conAt ch.W hM (fockD ch.W t d.2 P) h j = _ from (dif_neg hj0).trans (dif_pos hj')] at hc
    obtain ⟨c1, c2⟩ := contr_ne_zero hc
    rw [move] at c1 c2
    rw [hInv, rowGrp_bes ch.G j _ hj'] at hI
    have s1 := hsh j _ hj' (GlobalTheory.Unf.Inhab.nonempty_volN _).some
    have s2 := hsh (j + 1 + 1) ((D.R.m - 4 - j) / 2) (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some
    have I1 := inBig_bf (B := besAt ch.G hM j _ hj' (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
      (J := jacAt ch.G hM (j + 1) ((D.R.m - 4 - j) / 2 + 1) (by omega))
      (stepAt ch.G ch.W t hM j (by omega) _ _) (fun v _ => (s1 v).2.2.1) (fun v hv => (s1 v).2.2.2.2.2 ((hSf v).1 hv) j (by omega))
      (sdN (j + 1) (by omega)) (vac j (by omega)) hI c1
    have I2 := inBig_fb (J := jacAt ch.G hM (j + 1) ((D.R.m - 4 - j) / 2 + 1) (by omega))
      (B := besAt ch.G hM (j + 1 + 1) ((D.R.m - 4 - j) / 2) (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
      (stepAt ch.G ch.W t hM (j + 1) (by omega) _ _) (fun v _ => (s2 v).2.2.2.1 (j + 1) rfl (by omega))
      (fun v hv => (s1 v).2.2.2.2.2 ((hSf v).1 hv) (j + 1) (by omega))
      (fun v _ => ⟨_, _, sd_top ch.G (j + 1 + 1) (by omega), (s2 v).1, (s2 v).2.1⟩)
      (sdN (j + 1) (by omega)) (sdN (j + 1 + 1) (by omega)) (vac (j + 1) (by omega)) I1 c2
    rw [hInv, hInv, rowGrp_jac ch.G (j + 1) ((D.R.m - 4 - j) / 2 + 1) (by omega),
      rowGrp_bes ch.G (j + 1 + 1) ((D.R.m - 4 - j) / 2) (by omega)]
    exact ⟨I1, I2⟩
  have ev : ∀ k, 2 * k + 2 ≤ D.R.m → Inv (2 * k) := by
    intro k
    induction k with
    | zero =>
      intro _
      show Inv 0
      obtain ⟨e', he', hs, -⟩ := hb.1
      rw [hInv, h0]
      exact ⟨1, one_mem _, one_mem _, (b 0)⁻¹, inv_mem (grpOff_of_suppAt he' hSf hs), 1,
        ⟨one_mem _, fun y _ => by rw [mt_one, Matrix.one_mulVec]⟩, by rw [mul_one]⟩
    | succ k ih =>
      intro hk
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring]
      exact (step _ (even_two_mul k) (by omega) (ih (by omega))).2
  intro j hj hjm
  have hj' := List.mem_range'_1.1 hj
  have hI : Inv j := by
    rcases Nat.even_or_odd' j with ⟨k, hk | hk⟩
    · rw [hk]
      exact ev k (by omega)
    · rw [hk]
      exact (step _ (even_two_mul k) (by omega) (ev k (by omega))).1
  obtain ⟨δ, hδ, hbf, a', ha', ea⟩ := hb.2.1 j hj
  obtain ⟨r, hr, a, ha, x, hx, k, hk, hkl, eq⟩ := cell_of_inBig he hSf (sdN j (by omega)) hbf (hmv j hjm) ((hInv j).1 hI)
  refine ⟨r, hr, a * a'⁻¹, mul_mem ha (inv_mem ha'), δ, x, _, hδ, ⟨e, he, hx, fun _ => rfl⟩, k, ⟨hk, ?_⟩, ?_⟩
  · show Lev.finE (ch.G.V (.grid D.R.m j)) k ∈ ch.G.levMax (.grid D.R.m j)
    rw [GridData.levMax, congLev_top]
    exact ⟨GlobalTheory.LevSplit.finE_mem_UA _ k, hkl⟩
  · rw [eq, ← ea]
    group

theorem offAt_big : Big fun ch => OffAt ch := by
  obtain ⟨CF0, H⟩ := GlobalTheory.T.lastRowLatticesGoodPosition_large_depth.and GlobalTheory.T.unfoldedVacua_differ_by_twist_values_largeDepth
  refine ⟨CF0, fun ε CF hC => ?_⟩
  obtain ⟨x, H⟩ := H ε CF hC
  refine ⟨x, fun D large₂ e hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch i j => ?_⟩
  have H' := H D large₂ e hx Γ Pl0 T A Ks R F s ch i j
  exact offAt_of_shape ch H'.1 H'.2.1

end GlobalTheory.RowOneCos

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SingleCosetOffTwistPlacesLargeDepthStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.singleCosetOffTwistPlaces_largeDepth : Big fun ch => OffAt ch := by
  first | exact @GlobalTheory.RowOneCos.offAt_big | exact GlobalTheory.RowOneCos.offAt_big | (intros; apply GlobalTheory.RowOneCos.offAt_big <;> assumption)
end
