module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefMapNormEquivariantBasisOfPre
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MovedFiniteDatumFourierExpansionChainless
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PureTensorOSmul

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCcIsEquivAtSerOfTie
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCuspIsThClsDOfPre
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.AdTh.CcEx
noncomputable section
open GlobalTheory.ClsVal.Cmp
section Gen
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ}
variable {H : Geo.Tor.Host E} {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ}
end Gen

theorem exists_ccIs_ofPre : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.RealGeo.PreChar R → TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ∃ cc, CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.U ((i : ℕ) + 1) O.s0) O.dict O.mu (T.x₀ ((i : ℕ) + 1) O.s0) (R.ωP i A.μ0) (R.vacP i) cc := by
  intro hci D G _ _ Pl0 T0 A T _ R κ v₀ hC hT i Tp tup O hO
  have hs0 : O.s0 = T.toCore.σ₀ := sOv_eq _ _ _
  have hσ : GoodEmb T.Q.c O.s0 := rfl
  obtain ⟨hP, hV0, h1, h2, h3, h4, h5⟩ := GlobalTheory.AdTh.RecPair.isPair_record_ofPre D G Pl0 T0 A _ R hC i A.μ0 hO.lift.std
  have hM := GlobalTheory.AdTh.models_at_record_ofPre D G Pl0 T0 A T R κ v₀ hC hT i O.s0 hs0
  have hχ : (Lift.chrTh (R.toLevCh.mu A.μ0) R.eta ((i : ℕ) + 1)).1 = T.chiW ((i : ℕ) + 1) O.s0 := by
    rw [hs0, chiTie_of_chiR T R hT.alg hT.laws.pins.2.2.1 hT.chiR i]
    ext1 x
    change R.mu0 _ x * R.xi A.μ0 x = _
    rw [TwistFactorCompare.eq_one_of_chrEq_one (χ := R.xi A.μ0) (hC.lev.xi_base ▸ hC.lev.xi A.μ0) x, mul_one]
  have hcast : ∀ (W : HSp D) (hV : T.V ((i : ℕ) + 1) O.s0 = W),
      MuVal W (T.chiW ((i : ℕ) + 1) O.s0) (castDict hV (T.mu ((i : ℕ) + 1) O.s0)) ∧ ∀ γ ∈ GQ W, ∀ h,
        castDict hV (T.mu ((i : ℕ) + 1) O.s0) (γ * h) = castDict hV (T.mu ((i : ℕ) + 1) O.s0) h := by
    intro W hV
    subst hV
    have hu := hT.laws.muUnit _ (inR i) _ hσ
    exact ⟨hT.laws.muVal _ (inR i) _ hσ, fun γ hγ h => (hu.1 γ h).trans (by rw [hu.2.2.1 γ hγ, one_mul]; rfl)⟩
  obtain ⟨hmu, hmuQ⟩ := hcast _ O.hV
  obtain ⟨-, -, -, -, -, -, hr1, hrt, -, -, hdom, -⟩ := hM (O.dict 1).1
  exact exists_ccIs_of_pair hci hP (hχ ▸ hmu) hmuQ (rank_Wc i) hrt _ hσ (hT.laws.unf _ (inR i) _ hσ) hr1
    hT.laws.pins.2.1.2 hdom hV0 h1 h2 h3 h4 h5 _ _ (fun k => (hM k).1) (fun k => (hM k).2.1) (fun k => (hM k).2.2.1)
    (hC.thP.vP i A.μ0).1 _

end
end GlobalTheory.AdTh.CcEx
end

section
noncomputable section
namespace GlobalTheory.FrameConstMove
section Geo
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open _root_.Formalism.L2.Pj GlobalTheory.Dict GlobalTheory.Dict.Lift
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {r g : ℕ} {X : Data E r} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ}
  {idx : Fin g ≃ X.Ψ × Fin r} {e : Fin g ≃ Lt1 Dw} {x : Frame X.Ψ r} {L : Lt E r}
end Geo
section Classical
open NumberField Matrix Complex ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.LevelCusp
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open _root_.Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} {X X' : Data E r}
end Classical
section Adelic
open NumberField Matrix Complex ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.LevelCusp GlobalTheory.DictMove
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice _root_.Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.FWT _root_.Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7}
end Adelic
end GlobalTheory.FrameConstMove
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.FrameConstMove
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem om_lift_vac_ofPre (hR : GlobalTheory.RealGeo.PreChar R) (i : Fin D.R.m) (hV : VStd D i) (H : Geo.Tor.Host D.host.E)
    {mu : GA D (Wc D i) → ℂ} (hmu : MuVal (Wc D i) (R.mu0 ((i : ℕ) + 1)) mu) {g : G} {k : GA D (Wc D i)}
    (hk : Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k) :
    R.ωP i A.μ0 (1, k) (R.vacP i) = mu k • R.vacP i := by
  obtain ⟨hP, hV0, -, -, sV, sW, -⟩ := GlobalTheory.AdTh.RecPair.isPair_record_ofPre D G Pl0 T0 A Ks R hR i A.μ0 hV
  have hχ : (Lift.chrTh (R.toLevCh.mu A.μ0) R.eta ((i : ℕ) + 1)).1 = R.mu0 ((i : ℕ) + 1) := MonoidHom.ext fun x => by
    show R.mu0 ((i : ℕ) + 1) x * R.xi A.μ0 x = _
    rw [GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one (χ := R.xi A.μ0) (hR.lev.xi_base ▸ hR.lev.xi A.μ0) x, mul_one]
  have hl : Formalism.L2.Pj.latHat (Wc D i) = GlobalTheory.AdLat.hat D.host.F (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) := by
    rw [GlobalTheory.PrincInLevel.eq_latC (hR.lev.βW i)]
    exact (GlobalTheory.Member.latHat_eq_hat_and_gram D _).1
  have mv : ∀ {g k}, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g k → ∀ u, u ∈ _ → actO (Vc D i) (Wc D i) 1 k u ∈ _ :=
    fun hk => GlobalTheory.MovedLat.actO_mem (Vc D i) (Wc D i) 1 _ (R.ΛV i) (R.ΛV i) (R.ΛW i) (R.ΛW i)
      (fun z hz => by rw [map_one, Units.val_one, Matrix.one_mulVec]; exact hz)
      (fun z hz => by rw [← hl] at hz ⊢; exact GlobalTheory.DictMove.mulVec_mem_latHat (hR.lev.βW i) hk hz)
  refine GlobalTheory.T.weilRep_lattice_stabilizer_vacuum_eq_det_char_smul D _ _ _ _ _ _ _ hP mu (hχ ▸ hmu) H _ _ hV0 sV sW _
    (GlobalTheory.FrameEquiv.isCartanInv_cart_model (R.MW i (sg0 D A))) _ (hR.thP.vP i A.μ0).1 k hk.1 fun u => ⟨mv hk u, fun hu => ?_⟩
  have h := mv (GlobalTheory.ProjComm.isLift_inv hk) _ hu
  rw [actO_one_left, actO_one_left, ← Matrix.mul_assoc] at h
  unfold Formalism.L2.Theta.mt at h
  rwa [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mul] at h


set_option maxHeartbeats 1000000 in
theorem equivAt_of_ccIs_ofPre : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.RealGeo.PreChar R → TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ∀ cc, CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.U ((i : ℕ) + 1) O.s0) O.dict O.mu (T.x₀ ((i : ℕ) + 1) O.s0) (R.ωP i A.μ0) (R.vacP i) cc → ∀ u : ℂ, O.EquivAt (κ i) (u • cc) := by
  intro _ D G _ _ Pl0 T0 A T _ R κ v₀ hR ht i Tp tup O hO cc hcc u g k hk f hf
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have h := ht.laws
  have hact := hO.act.1
  refine ⟨GlobalTheory.GeoLevel.actLev_mem_cuspA h.toLawsM hj hact (κ i) g hf, fun p => ?_⟩
  have hσ : GoodEmb T.Q.c O.s0 := T.good_σ₀
  obtain ⟨_, _, -, hd⟩ := h.dictU _ hj _ hσ
  obtain ⟨hr, g₀, e, F₀, ik, φ, th, -, -, hth, hL⟩ := h.adPin _ hj _ hσ
  obtain ⟨-, hA, -, -, -, -, hnum⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q h.pins
  have hU := h.unf _ hj _ hσ
  have hpq := hU.1 ▸ (show 1 ≤ D.R.r from (hnum _ hj).2.1)
  have hmod := GlobalTheory.AdTh.models_at_record_ofPre D G Pl0 T0 A T R κ v₀ hR ht i O.s0 rfl
  have hn : (κ i).n = (Vc D i).rank := (hmod (O.dict p).1).2.2.2.2.2.2.2.2.2.2.2.1
  have hmu : MuVal (Wc D i) (R.mu0 ((i : ℕ) + 1)) O.mu := by
    rw [← chiTie_of_chiR T R ht.alg h.pins.2.2.1 ht.chiR i]
    exact muVal_cast O.hV (h.muVal _ hj _ hσ)
  have hmul : ∀ a b, O.mu (a * b) = O.mu a * O.mu b := GlobalTheory.GeoLevel.castDict_mu_mul (h.muUnit _ hj _ hσ).1 O.hV
  have hag := GlobalTheory.LiftAgrees.levAgrees_of_isLift R i hR.lev _ (iotaW T i) (Mfr T.Q.l) O.lev
    (GlobalTheory.LevelAction.latEmb_iotaW T h i) (h.pins.2.1.1 ▸ hO.lift.lev) g k hk
  have hs : f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (wtA (κ i)) (Vc D i).rank := hn ▸ ((mem_cusp _ _ _ _ _ _).1 hf).1
  have key := value_move O.hV hr (rank_Wc i) (T.iota _) hσ hU hpq hA (fun c => (hmod c).1) hL hth hd.2.2.2.1
    (h.muUnit _ hj _ hσ).2.2.2 (GlobalTheory.AdTh.RecPair.isPair_record_ofPre D G Pl0 T0 A _ R hR i A.μ0 hO.lift.std).1
    (hR.thP.vP i A.μ0).1.2.theta hmul (fun a => norm_ne_zero_iff.1 ((hmu.norm a).trans_ne one_ne_zero)) hcc
    (s := O.lev g) (s' := LinearMap.id) (κ := k)
    ⟨hk.1, GlobalTheory.DictMove.latGHat_eq (hR.lev.βW i) hk, fun a ha => by
      obtain ⟨w, hw, ew⟩ := hag a ha
      refine ⟨-w, neg_mem hw, ?_⟩
      rw [h.pins.2.1.1]
      exact eq_add_nsmul_neg ew⟩
    (om_lift_vac_ofPre hR i hO.lift.std T.Q.H hmu hk) (f' := actLev T.Q.c O.lev2 g f) hs (fun y => by
      obtain ⟨ρ, ν, -, hν, hm⟩ := mvPt_spec hact.total g y
      exact ⟨ρ, ν, _, hν, hm, evalAt_actL hact (h.evalWD _ hj) frMap_trans_id g hs.1 y⟩) p
  have h1 := chi_mul_mu hR.lev i hmu hk
  change u * cc (O.dict p).1 * O.mu p * rdU (T.U ((i : ℕ) + 1) O.s0) (actLev T.Q.c O.lev2 g f) (O.dict p).1 (O.dict p).2 =
    _ * (u * cc (O.dict (p * k)).1 * O.mu (p * k) * rdU (T.U ((i : ℕ) + 1) O.s0) f (O.dict (p * k)).1 (O.dict (p * k)).2)
  rw [hmul]
  linear_combination u * O.mu p * key - u * O.mu p * cc (O.dict (p * k)).1 *
    rdU (T.U ((i : ℕ) + 1) O.s0) f (O.dict (p * k)).1 (O.dict (p * k)).2 * h1

end GlobalTheory.FrameConstMove
end
end

section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.Datum
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.ClassSumRule
open GlobalTheory.LevelActionPinned GlobalTheory.GeoLevel GlobalTheory.DatumInverseCharacter
variable {D : D7}
section Pairing
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
end Pairing
variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H}
variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m} {t : T0}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
end GlobalTheory.ClassSumRule
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate

set_option maxHeartbeats 1600000 in
theorem GlobalTheory.ClassSumRule.exists_cusp_isThClsD_ofPre : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.RealGeo.PreChar R → TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ∀ (t : Tp) (x : O.Cl' t → VsV D i O.c'.F), ∃ f ∈ cusp (T.Q.Xo ((i : ℕ) + 1)) O.c' (unfBC O.hle (T.U ((i : ℕ) + 1))) (wtA (κ i)) (Vc D i).rank, IsThClsD (T.Q.Xo ((i : ℕ) + 1)) O.c' (O.dδ t) (O.w t) (O.La t) (O.Nc t) (O.gam t) (O.vol t) (O.ep t) O.io x f := by
  intro hci D G _ _ Pl0 T0 A T _ R κ v₀ hR hT i Tp tup O hO t x
  have hj := inR i
  have hσ : GoodEmb T.Q.c O.s0 := rfl
  obtain ⟨-, -, -, -, hr, -, hr1, -, -, -, hDom, -, hLast⟩ := GlobalTheory.AdTh.models_at_record_ofPre D G Pl0 T0 A T R κ v₀ hR hT i _ rfl
    (T.dict ((i : ℕ) + 1) T.toCore.σ₀ 1).1
  obtain ⟨hι, hx₀⟩ := GlobalTheory.TupleCover.iotaOK_and_frame T hT.laws _ hj _ hσ (Wc D i) O.hV (rank_Wc i)
  obtain ⟨c0, ⟨m, hm, hc0⟩, hv⟩ := hO.cxi
  obtain ⟨hxi, n, hn, hxn⟩ := GlobalTheory.ClassSumRule.xi_laws hR.lev (hO.tuple t).xi
  obtain ⟨hd, hA, -⟩ := hO.cov t
  have hpq := hr ▸ hr1
  have hN : 0 < m * n := Nat.mul_pos hm hn
  have hcN : c0 ^ (m * n) = 1 := by rw [pow_mul, hc0, one_pow]
  have hxN : ∀ h : GA D (Wc D i), O.xi t (Matrix.GeneralLinearGroup.det (finHom (Wc D i) h)) ^ (m * n) = 1 := fun h => by
    rw [mul_comm, pow_mul, hxn, one_pow]
  obtain ⟨_, _, _, hfam⟩ := hR.fam.tie
  obtain ⟨ψ, hψ, hw⟩ := GlobalTheory.ClassSumRule.exists_char hR.lev (O.dδ t) hd hι (hr.symm.trans (rank_Wc i).symm) hpq
    (hO.tuple t).half (fun P hP z => by
      obtain ⟨a, ha⟩ := GlobalTheory.RationalValues.xiR_mem R hR.lev hR.fam.pl_onto hR.fam.muVal hfam.ok i (tup t) P hP z
      rw [← ha, ← hO.lift.field]
      exact (O.jL a).2) (hO.tuple t).xi (hO.tuple t).phi
  obtain ⟨f, hf, hcls, -⟩ := GlobalTheory.ClsVal.exists_cusp_isThClsD_unique hci _ _ _ _ _ O.c' _ (O.dδ t) _
    (unfBC O.hle (T.U ((i : ℕ) + 1))) hr1
    (fun σ hσ => GlobalTheory.OneMapAll.isUnf_unfExt O.hle σ (fun _ => rfl) (hT.laws.unf _ hj (σ.comp (incF T.Q.c O.c' O.hle)) hσ))
    hT.laws.pins.2.1.2 (fun _ => hO.cov t)
    (GlobalTheory.OneMapTuples.unitC_of_cXiAt D _ _ _ _ _ _ _ _ (O.dδ t) (rank_Wc i) _ hι hpq _ hx₀ hd hA _ _ hN hxN _ _ c0 hcN (hv t))
    ψ (GlobalTheory.ClassSumRule.psiTie_of_values _ (O.dδ t) (rank_Wc i) _ hι hpq _ hx₀ hd hA _ _ hN hxN hxi _ _ c0 hcN (hv t) ψ hψ)
    _ (O.w t) (O.La t) (O.Nc t) (O.gam t) (O.bad t) (O.vol t) (O.ep t) _ O.io (wtA (κ i)) hDom hLast
    (fun k => hw _ (hO.w t k)) (hO.reps t).1 (by
      obtain ⟨-, _, h⟩ := hO.io
      exact h.2.2.1.le) x
  exact ⟨f, hf, hcls⟩

end
end
end

section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.AdTh

set_option maxHeartbeats 1000000 in
theorem oneMapRow_of_serOf_ofPre : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.RealGeo.PreChar R → TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ∀ cc, SerOf O (κ i) (v₀ i (sg0 D A)) cc 1 → (∀ (t : Tp) (x : O.Cl' t → VsV D i O.c'.F), ∃ f ∈ cusp (T.Q.Xo ((i : ℕ) + 1)) O.c' (unfBC O.hle (T.U ((i : ℕ) + 1))) (wtA (κ i)) (Vc D i).rank, IsThClsD (T.Q.Xo ((i : ℕ) + 1)) O.c' (O.dδ t) (O.w t) (O.La t) (O.Nc t) (O.gam t) (O.vol t) (O.ep t) O.io x f) → OneMapRow (T.Q.Xo ((i : ℕ) + 1)) O.c' (Wc D i) (unfBC O.hle (T.U ((i : ℕ) + 1)) (inC O.c')) O.dict O.mu (xiR D) (wtA (κ i)) (actLev O.c' O.lev2) O.dδ O.Cl' O.w O.La O.Nc O.gam O.vol O.ep O.io O.thAd O.Plc D.what₂.embLL.toRatAlgHom.fieldRange (cusp (T.Q.Xo ((i : ℕ) + 1)) O.c' (unfBC O.hle (T.U ((i : ℕ) + 1))) (wtA (κ i)) (Vc D i).rank) cc 1 := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ _ _ i Tp tup O hP cc hS hE
  refine ⟨hS.1, hS.2.1, 1, Subgroup.one_mem _, fun t => ⟨1, one_mem _, ⟨1, Nat.one_pos, one_pow _⟩, fun x hx => ⟨hE t x, ?_⟩⟩⟩
  intro f hf hT q
  obtain ⟨h, J', hR, -, hA, hPl⟩ := (hP.tuple t).reps
  obtain ⟨x₀, hx₀⟩ := (hPl x).1 hx
  have hL := hP.act.2
  have h1 : actLev (Xo := T.Q.Xo ((i : ℕ) + 1)) O.c' O.lev2 1 f = f :=
    actL_one _ _ _ hL.total hL.func hL.one hf.1
  have h2 := hS.2.2 t h J' hR _ x hx₀ f hf hT q.out
  rw [h1, hA _ x hx₀, one_mul (cc _)]
  refine h2.trans ?_
  rw [mul_assoc (cc _ * _)]
  rfl

end GlobalTheory.AdTh
end

section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.PtId.OneScalar
section Hw
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m}
end Hw

theorem exists_scalar_ofPre : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.RealGeo.PreChar R → TieIn T R κ v₀ → IoExt R → ∀ (i : Fin D.R.m) (c0L : VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).W), ∃ ka : ℂ, ‖ka‖ = 1 ∧ ∀ (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → CoefficientBaseChange R i O.jL (inC O.c') c0L O.c0' → GlobalTheory.PtId.IoAt O (v₀ i (sg0 D A)) ka := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hC hT hI i c0L
  by_cases hex : ∃ (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup),
      O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) ∧ CoefficientBaseChange R i O.jL (inC O.c') c0L O.c0'
  swap
  · exact ⟨1, norm_one, fun Tp tup O h1 h2 => absurd ⟨Tp, tup, O, h1, h2⟩ hex⟩
  obtain ⟨Tp₀, tup₀, O₀, hP₀, hB₀⟩ := hex
  obtain ⟨ka₀, hn₀, hk₀⟩ := GlobalTheory.AdTh.PhaseMap.io_eq_phase_smul_ofPre D G Pl0 T0 A T R κ v₀ hC hT hI i Tp₀ tup₀ O₀ hP₀
  refine ⟨ka₀, hn₀, fun Tp tup O hP hB => ?_⟩
  obtain ⟨ka, -, hk⟩ := GlobalTheory.AdTh.PhaseMap.io_eq_phase_smul_ofPre D G Pl0 T0 A T R κ v₀ hC hT hI i Tp tup O hP
  intro lt hlt u hu
  suffices h : ka = ka₀ by
    subst h
    exact hk lt hlt u hu
  have e1 := hk lt hlt u hu A.μ0 O.hw
  have e2 := hk₀ lt hlt u hu A.μ0 O₀.hw
  obtain ⟨hw1, cga, -, hinj, -, -, -, -, hio, -⟩ := hP.io
  obtain ⟨hw2, cga', -, -, -, -, -, -, hio₀, -⟩ := hP₀.io
  have hne : O.io O.hw ≠ 0 := by
    intro h0
    have h1 : O.hw = 0 := hinj (h0.trans (map_zero _).symm)
    have h2 := (GlobalTheory.AdTh.coefMap_norm_equivariant_basis_ofPre D G Pl0 T0 A T R κ v₀ hC hT i Tp tup O hP).1
    rw [h1, map_zero, norm_zero] at h2
    exact zero_ne_one h2
  rw [coefficientMap_extremalTensor_baseChange O hw1 hB] at e1
  rw [coefficientMap_extremalTensor_baseChange O₀ hw2 hB₀, hio₀, map_pG_eq O₀.c' O.c' (inC O₀.c') (inC O.c'), ← hio, e1] at e2
  have hV := hP.lift.std
  obtain ⟨f1, f2, f3, f4, f5⟩ := GlobalTheory.AdTh.VecFock.vec_fock_ofPre D G Pl0 T0 A T.Q.c.F R hC i A.μ0 hV
  have hON : ∀ τ, IsONBasis (gramAt D (Vc D i) τ) 1 1 (Vc D i).rank := fun τ => by
    refine ⟨fun _ => 1, fun a => Or.inl ⟨rfl, a.2⟩, ?_, ?_⟩
    · simp [gramAt, hV.1]
    · simp
  have hinjP := GlobalTheory.FockVecInj.pureTensorO_injective D R.ψ R.θ (Vc D i) (Wc D i) (hC.thP.ωP i A.μ0).std hC.models.inf
    (fun _ => 1) (fun _ => 1) (cart (R.MW i (sg0 D A))) (onb (R.MW i (sg0 D A))) (fun _ => (Vc D i).rank) _ f4 f3 hON f5
    (D.sp.V_sig _) (D.sp.W_sig _) (R.vP i A.μ0) f1 f2 (GlobalTheory.AdTh.VecNe.thetaVector_ne_zero_of_preChar D G Pl0 T0 A T.Q.c.F R hC i hV)
  have hlti : Function.Injective lt := lt_injective (fun ρ => hT.laws.pins.1.2.2.2 ρ) lt hlt
  refine smul_left_injective ℂ (fun h0 => hne ?_) e2
  have h1 := hinjP (h0.trans (map_zero _).symm)
  have h2 := MvPolynomial.rename_injective lt hlti (h1.trans (map_zero _).symm)
  exact MvPolynomial.map_injective _ (inC O.c').injective (h2.trans (map_zero _).symm)

end GlobalTheory.PtId.OneScalar
end

section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.PtId

open GlobalTheory.AdTh.CoverVal in
theorem covAt_of_xiConst_ofPre : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.RealGeo.PreChar R → TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ∀ c0 : ℂ, GlobalTheory.OneMapTuples.XiConst O (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) c0 → GlobalTheory.PtId.CovAt O c0 := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hR hT i Tp tup O hO c0 hc
    t X g bas idx e k xk mk hX hp hs hi hL hxk hmk hk y₂ A₂ hA₂
  obtain ⟨hU, hW, g', e', F', ik, φ, th, hth, hD, hval⟩ := hc t
  obtain ⟨hlev, hA, -⟩ := hO.cov t
  obtain ⟨hX₀, hon₀, -, hp₀, -, -, h1, -, hΨ₀, -⟩ := GlobalTheory.AdTh.models_at_record_ofPre D G Pl0 T0 A T R κ v₀ hR hT i O.s0
    (sOv_eq _ _ _) (T.dict _ O.s0 1).1
  have hσ : GoodEmb (O.dδ t).c₂ ((inC O.c').comp ((O.dδ t).eF.symm : (O.dδ t).c₂.F →+* O.c'.F)) := rfl
  have hmod : ∀ j, IsMod (Wc D i) (rank_Wc i) ((O.U₂ t).X j) := fun j =>
    isMod_of _ _ _ (hW j) fun ρ => ((hU.2.1 j).2 _).2 ((hΨ₀ _).1 ((hX₀.psi _).2 ⟨ρ, rfl⟩))
  have hor : ∀ j, IsOrthogonalFrame ((O.U₂ t).X j) (T.x₀ ((i : ℕ) + 1) O.s0) := fun j τ hτ => by
    have hsp := sameSp_of (hmod j) hX₀ ((hU.2.1 j).1.trans hp₀.symm)
    rw [hsp.gm, hsp.p0]
    exact hon₀ ⟨τ, hsp.psi ▸ hτ⟩
  obtain ⟨Wt⟩ := nonempty_uw ((Formalism.L2.PjFree.isUnf_ofPj _).2 hU)
  obtain ⟨hon, γ, ⟨hγ, hl, hf⟩, hma, -⟩ := GlobalTheory.AdTh.dict_atComp_markAd D _ _ _ _ _ _ _ (O.U₂ t) hσ hU h1 hA R.θ (Wc D i)
    (rank_Wc i) (O.dict₂ t) (iotaW T i) g' e' F' ik φ th _ hR.models.inf hmod hor hth hD Wt k
  obtain ⟨hd, hpt⟩ := point_eq (Formalism.L2.PjFree.Unf.ofPj (O.U₂ t)) hσ hU h1 hA hR.models.inf (Wc D i) (rank_Wc i) (iotaW T i)
    _ Wt (O.dict₂ t k).1 (O.dict₂ t k).2 γ k hγ (hmod _) hl hf hon hma X g bas idx e mk hX hp hs hi hL hmk hk y₂ A₂ hA₂
  obtain ⟨γ', hγ', h2, h3, -⟩ := hD.2 k
  obtain ⟨-, -, hrat, hmul⟩ := GlobalTheory.Member.isDetRoot_laws D (Wc D i)
  obtain ⟨a, ha⟩ := hrat γ' hγ'
  have hv := hval k γ' ⟨hγ', h2, h3⟩
  rw [(hO.tuple t).xi _ _ (hmul _ _ _ _ ha hxk), map_mul, (hR.lev.xi (tup t)).1.2 a, _root_.one_mul] at hv
  exact (evR_eq_of_point _ hlev.2.2.2.2.2.2.2.1 _ y₂ hpt).trans ((dif_pos hd).symm.trans hv)

end GlobalTheory.PtId
end

section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.PtId
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
  {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}

set_option maxHeartbeats 2000000 in
theorem ad_value_ofPre (hC : GlobalTheory.RealGeo.PreChar R) (hT : TieIn T R κ v₀) (O : OMDat T.toCore R i Tp tup)
    (hP : O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0)) {ka : ℂ} (hka : IoAt O (v₀ i (sg0 D A)) ka)
    {δ : ℤˣ} (hδ : ClsAt R i (iotaW T i) δ) (t : Tp) (h : O.Cl' t → GA D (Vc D i)) (J' : Subgroup (Bridge.Gf (Vc D i)))
    (hR : RepsR R i (tup t) h (O.bad t) J' (O.Lh t) (O.gam t) (O.vol t)) (y : (R.HV i (tup t)).H)
    (xs : O.Cl' t → VsV D i O.c'.F) (hpl : Place R i (tup t) h O.c0' y xs) (g' γ : GA D (Wc D i)) (hγ : γ ∈ GQ (Wc D i))
    (X : Data D.host.E D.R.r) (g : ℕ)
    (Dc : Dic (T.Q.Dw ((i : ℕ) + 1)) O.c' (inC O.c') X g (T.Q.Dw ((i : ℕ) + 1)).p (Vc D i).rank (wtA (κ i)))
    (hX : IsMod (Wc D i) (rank_Wc i) X) (hp : X.p0 = (T.Q.Dw ((i : ℕ) + 1)).q)
    (hrt : (T.Q.H.rt : D.host.E) = D.host.sqrtMinusD) (x₀ : Frame X.Ψ D.R.r) (hon : IsONFr X x₀)
    (hinv : IsInvOf (Wc D i) (rank_Wc i) X x₀ (cart (R.MW i (sg0 D A))))
    (hbas : IsBasOf (Wc D i) (rank_Wc i) X Dc.hr x₀ (onb (R.MW i (sg0 D A))))
    (hΛ : latR (rank_Wc i) (latG (Wc D i) (γ * g')) = X.Λ)
    (mk₂ : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E))
    (ha₂ : MarkAd (O.dδ t).l₂ (Wc D i) (rank_Wc i) (iotaW T i) (γ * g') mk₂) (v : TF (Vc D i).rank g) (a : ℂ)
    (hv : IsVac X Dc.bas (T.Q.H.w0 : D.host.E) (tens (stdL D.host.E (Vc D i).rank) X.Λ) v)
    (hrd : Reads R.θ (Vc D i) (Wc D i) (rank_Wc i) X Dc.bas Dc.idx (R.ωP i (tup t) (1, γ * g') (R.vacP i)) (a • v)
      (frMove R.θ (Wc D i) (rank_Wc i) X (γ * g') x₀))
    (Y : O.Cl' t → (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (O.dδ t).l₂) → Matrix (Fin (Vc D i).rank) (Fin D.R.r) D.host.E)
    (hY : ∀ j, IsRoots (O.dδ t).l₂ X.Λ mk₂ (O.Nc t j) (Y j)) :
    R.thF i (tup t) y (v₀ i (sg0 D A)) g' = cmpConst D ka δ (degW (T.Q.Dw ((i : ℕ) + 1)) (wtA (κ i))) * a *
      clsSum (inC O.c') X Dc.hr Dc.bas Dc.idx Dc.eL (O.w t) (O.La t) (O.Nc t) (O.gam t) (O.vol t) (O.ep t)
        (fun j => O.io (xs j)) X.Λ v Y (frMove R.θ (Wc D i) (rank_Wc i) X (γ * g') x₀) := by
  let u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ := fun ρ => ⟨v₀ i (sg0 D A) ρ, (hP.lift.v0.1 ρ).2.1⟩
  have hun := GlobalTheory.LiftUnfold.thF_eq_classSum_ofPre D G Pl0 T0 A _ R hC i (tup t) _ (inC O.c') O.c0' _ h _ J' _ _ _ hP.lift.std hR y xs hpl u g'
  refine hun.trans ?_
  rw [clsSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  obtain ⟨vr, hvr⟩ := exists_isVarOf (Vc D i) (Wc D i) (rank_Wc i) X hX _ Dc.hr
  have hlt := letters_eq_fockVars_ofPre D G Pl0 T0 A T R κ v₀ hC hT i Tp tup O hP X g Dc vr hX hp hvr
  have hω := hC.thP.ωP i (tup t)
  have hmove : ∀ f, IsThetaFunO R.ψ (Vc D i) (Wc D i) f →
      thetaKO (R.ωP i (tup t)) (h j) g' f = thetaKO (R.ωP i (tup t)) (h j) (γ * g') f := fun f hf => by
    have e1 : ((h j, γ * g') : GA D (Vc D i) × GA D (Wc D i)) = (1, γ) * (h j, g') := by simp
    rw [thetaKO, thetaKO, e1, map_mul]
    exact (hω.om_aut 1 (one_mem _) γ hγ _ (hω.om_pres _ f hf)).symm
  rw [hmove _ (hC.thP.pt_theta i (tup t) _), hka (fun ℓ => vr (Dc.eL ℓ)) hlt u (fun _ => rfl) (tup t) (xs j)]
  obtain ⟨⟨hfin, e, Ps, he, hPs, hsupp⟩, hLh, -⟩ := hR.2.2.2.2.2.2 j
  obtain ⟨yd, hyd⟩ := exists_isDetAt he (Vc D i) (h j)
  obtain ⟨hlev, -, -⟩ := hP.cov t
  obtain ⟨-, cga, hio⟩ := hP.io
  have hH := mem_HHa_of_span _ _ _ _ _ _ (hio.2.2.1 ▸ LinearMap.mem_range_self O.io (xs j))
  have hhom : (MvPolynomial.rename Dc.eL (MvPolynomial.map (inC O.c') (O.io (xs j)))).IsHomogeneous
      (degW (T.Q.Dw ((i : ℕ) + 1)) (wtA (κ i))) :=
    ((isHomogeneous_of_rowDeg _ _ _ _ hH.2.2).map _).rename_isHomogeneous
  have hhalf : ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q (tup t) → (O.dδ t).l₂.Mb ≤ PP.asIdeal ∧
      ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := fun PP hPP => by
    obtain ⟨k1, k2, k3⟩ := (hP.tuple t).half
    refine ⟨?_, k3 PP hPP⟩
    rw [hlev.2.2.2.1]
    rcases hPP with hPP | hPP
    · exact Ideal.mul_le_left.trans (k1.le.trans (Ideal.prod_le_inf.trans (Finset.inf_le hPP)))
    · exact Ideal.mul_le_right.trans (k2 PP hPP)
  have hla : ∀ w, w ∈ (O.La t j).La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) (h j)) := fun w => by
    rw [← hLh]
    exact (hP.reps t).2 j w
  have hcl := hδ (tup t) (O.dδ t).l₂ (fun x => inC O.c' (O.φ t x)) (hP.tuple t).phi hhalf hrt g _ X Dc.hr Dc.bas Dc.idx x₀ vr hX
    Dc.sympl hon hinv hbas hvr (O.bad t) (O.Nc t j) (h j) (γ * g') (O.La t j) mk₂ e Ps yd hR.2.1 he hPs hfin hsupp hyd hla
    ((hP.reps t).1 j).2.2.1 ((hP.reps t).1 j).2.2.2.1 ha₂ (Y j) (hΛ ▸ hY j) v a (hΛ ▸ hv) hrd _ _ hhom
  have hep := GlobalTheory.ClassScalarValue.class_scalar_value_ofPre D G Pl0 T0 A T R κ v₀ hC hT i Tp tup O hP t j (h j) e Ps yd he hPs hsupp hyd hLh hR.2.1
  have hw : hatC (O.dδ t).l₂ (fun x => inC O.c' (O.φ t x)) = fun q => inC O.c' (O.w t j q) := funext fun q =>
    (PairModel.hatC_phiHat (O.dδ t).c₂ (fun x => (O.dδ t).eF (O.φ t x)) q).symm.trans
      (congrArg (inC (O.dδ t).c₂) (hP.w t j q).symm)
  rw [← hep, hw, hΛ, MvPolynomial.rename_rename] at hcl
  have hsm : ∀ f, thetaKO (R.ωP i (tup t)) (h j) (γ * g') (ka • f) = ka * thetaKO (R.ωP i (tup t)) (h j) (γ * g') f :=
    fun f => by rw [thetaKO, thetaKO, map_smul]; rfl
  rw [hsm]
  refine (congrArg (fun z => inC O.c' (O.vol t * ((O.gam t j : O.c'.F))⁻¹) * (ka * z)) hcl).trans ?_
  simp only [cmpConst, map_mul, map_inv₀, map_natCast]
  ring


set_option maxHeartbeats 2000000 in
theorem exact_identity_ofPre (hC : GlobalTheory.RealGeo.PreChar R) (hT : TieIn T R κ v₀) (O : OMDat T.toCore R i Tp tup)
    (hP : O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0)) {ka : ℂ} (hka : IoAt O (v₀ i (sg0 D A)) ka)
    {δ : ℤˣ} (hδ : ClsAt R i (iotaW T i) δ) {c0 : ℂ} (hc : CovAt O c0) {cst : (T.U ((i : ℕ) + 1) O.s0).Comp → ℂ}
    (hcc : CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.U ((i : ℕ) + 1) O.s0) O.dict O.mu (T.x₀ ((i : ℕ) + 1) O.s0)
      (R.ωP i A.μ0) (R.vacP i) cst)
    (t : Tp) (h : O.Cl' t → GA D (Vc D i)) (J' : Subgroup (Bridge.Gf (Vc D i)))
    (hR : RepsR R i (tup t) h (O.bad t) J' (O.Lh t) (O.gam t) (O.vol t)) (y : (R.HV i (tup t)).H)
    (xs : O.Cl' t → VsV D i O.c'.F) (hpl : Place R i (tup t) h O.c0' y xs) (f : Rul (T.Q.Xo ((i : ℕ) + 1)) O.c')
    (hf : GlobalTheory.OneMapTuples.IsCls O t xs f) (g' : GA D (Wc D i)) :
    c0 * R.thF i (tup t) y (v₀ i (sg0 D A)) g' = cmpConst D ka δ (degW (T.Q.Dw ((i : ℕ) + 1)) (wtA (κ i))) *
      cst (O.dict g').1 * (O.mu g' * rdU (unfO O) f (O.dict g').1 (O.dict g').2) := by
  have hs : O.s0 = T.toCore.σ₀ := sOv_eq _ _ _
  have hσ : GoodEmb T.Q.c O.s0 := hs ▸ T.toCore.good_σ₀
  have hmod := models_at_record_ofPre D G Pl0 T0 A T R κ v₀ hC hT i O.s0 hs
  obtain ⟨hemb, -, hroot, hmk⟩ := dict_cast T hT.laws _ (inR i) O.s0 hσ (Wc D i) O.hV (rank_Wc i)
  obtain ⟨hX, hon, hinv, hp, hrk, hpq, h1, hrt, -, hbas, hD, -⟩ := hmod (O.dict g').1
  have hU : IsUnf (unfO O) := GlobalTheory.OneMapAll.isUnf_unfExt O.hle (inC O.c') (fun _ => rfl) (hT.laws.unf _ (inR i) O.s0 hσ)
  obtain ⟨hx, g, Dc, γ, mk, v, ϑ, κ', B, hat, hsd, hm, hBm, hma, hϑ, hv, hκ, hrd⟩ :=
    exists_point (unfO O) hσ hU h1 hT.laws.pins.2.1.2 R.θ (Vc D i) (Wc D i) (rank_Wc i) O.dict (iotaW T i)
      (T.x₀ ((i : ℕ) + 1) O.s0)
      (fun Wt k => hmk R.θ hC.models.inf (fun k => (hmod k).1) h1 ⟨Wt.g, Wt.e, Wt.F, Wt.ik, Wt.φ, Wt.isom, Wt.pt⟩ k)
      (wtA (κ i)) hD O.mu (R.ωP i A.μ0) (R.vacP i) cst (CcIs.unfBC _ _ _ _ O.hle _ (inC O.c') _ _ _ _ _ _ hcc) g'
  obtain ⟨hγ, hΛ, hfr⟩ := hat
  obtain ⟨xk, hxk⟩ := hroot (γ * g')
  have hlev := (hP.cov t).1
  obtain ⟨mk₂, hm₂, ha₂, hov⟩ := GlobalTheory.AdMark.exists_marking D _ _ T.Q.l (O.dδ t).l₂ (Wc D i) _ (rank_Wc i) (iotaW T i) hemb
    (hlev.2.1 ▸ dvd_mul_right _ _) (hlev.2.2.2.1 ▸ Ideal.mul_le_left) (γ * g')
  rw [hΛ] at hm₂ hov
  have hM : 0 < (O.dδ t).l₂.M := lt_of_lt_of_le (by norm_num) (O.dδ t).l₂.three_le
  choose Y hY using fun j : O.Cl' t => (DualMark.dual_marking _ _ _ (O.dδ t).l₂ _ _ _ mk₂ _ hsd hm₂
    (Complex.isPrimitiveRoot_exp _ hM.ne')).2.2.2.2 (Vc D i).rank (O.Nc t j) ((hP.reps t).1 j).2.2.2.1.1.pos
  have hgeo := geo_value hT O hP hc t _ g Dc (γ * g') xk hxk hX hp hpq hrk hD.2 hΛ hsd _ hx hfr mk mk₂ hm hm₂ ha₂
    (hov mk hm.mem hma) v ϑ κ' hv hκ Y hY xs f hf _ B hBm hϑ
  have htw := GlobalTheory.AdTh.weil_twist_base_ofPre D G Pl0 T0 A _ R hC i (tup t) (γ * g') xk hxk (R.vacP i) (hC.thP.vP i (tup t)).1.2.theta
  have hrd' : Reads R.θ (Vc D i) (Wc D i) (rank_Wc i) ((unfO O).X (O.dict g').1) Dc.bas Dc.idx
      (R.ωP i (tup t) (1, γ * g') (R.vacP i)) ((((R.xi (tup t) xk : Circle) : ℂ) * (cst (O.dict g').1 * O.mu g' * κ')) • v)
      (O.dict g').2 := by
    obtain ⟨s1, s2⟩ := ((thA_heis_entire_linear_injective _ _ g _ _ Dc.bas Dc.idx Dc.sympl hD.2 _ hx _ hrd.1).2.2 v hv.1).1
      ((R.xi (tup t) xk : Circle) : ℂ) 0
    rw [zero_smul, add_zero, smul_smul] at s1 s2
    rw [zero_smul, add_zero] at s2
    refine ⟨s1, fun w hw => ?_⟩
    rw [htw, s2, Pi.smul_apply, Pi.smul_apply, hrd.2 w hw, smul_eq_mul, smul_eq_mul]
    ring
  have had := ad_value_ofPre hC hT O hP hka hδ t h J' hR y xs hpl g' γ hγ _ g Dc hX hp hrt _ hon hinv (hbas _) hΛ mk₂ ha₂ v _ hv
    (hfr ▸ hrd') Y hY
  have hrdU : rdU (unfO O) f (O.dict g').1 (O.dict g').2 = _ := (dif_pos hx).trans hgeo
  have e1 := congrArg (clsSum (inC O.c') ((unfO O).X (O.dict g').1) Dc.hr Dc.bas Dc.idx Dc.eL (O.w t) (O.La t) (O.Nc t) (O.gam t)
    (O.vol t) (O.ep t) (fun j => O.io (xs j)) ((unfO O).X (O.dict g').1).Λ v Y) hfr
  rw [had.trans (congrArg (fun z => _ * z) e1.symm), hrdU]
  ring

end GlobalTheory.PtId
end
end
end

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RealGeo.PhaseOne

open GlobalTheory.PhaseRationalDegenerate GlobalTheory.AdTh GlobalTheory.PtId GlobalTheory.OneMapTuples

theorem lieFac_eq_pow {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H) {x : ℝ}
    (hx : 0 < x) (a : (E →+* ℂ) × ℕ → ℕ) : lieFac Dw x a = (Real.sqrt (2 * Real.pi * x))⁻¹ ^ GlobalTheory.PtId.degW Dw a := by
  have h : 0 < 2 * Real.pi * x := by positivity
  have e : (Real.sqrt (2 * Real.pi * x))⁻¹ = Real.exp (-(1 / 2) * Real.log (2 * Real.pi * x)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos h, ← Real.exp_neg]
    congr 1
    ring
  rw [e, ← Real.exp_nat_mul, lieFac, GlobalTheory.PtId.degW]
  congr 1
  push_cast
  ring

theorem shape {c s l k m r : ℂ} (hc : c ≠ 0) : s * l * k * (m * r) = c * (c⁻¹ * s * k * l * m * r) := by
  field_simp

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Rat

variable {C : Formalism.L2.Pj.Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}
  (O : OMDat C R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : (R.MW i (sg0 D A)).Vec)
  (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ)

end Rat

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
  {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}

theorem wt_n (hT : TieIn T R κ v₀) (i : Fin D.R.m) : (κ i).n = (Vc D i).rank :=
  (hT.kap i (D.eTau.symm 1)).2.2.trans (D.sp.V_rank _ (Nat.le_add_left _ _) i.2).symm

theorem fieldRange_le (O : OMDat T.toCore R i Tp tup)
    (hP : O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0)) :
    D.what₂.embLL.toRatAlgHom.fieldRange ≤ O.c'.F := by
  rintro _ ⟨a, rfl⟩
  have h : ((O.jL a : O.c'.F) : ℂ) = D.what₂.embLL a := RingHom.congr_fun hP.lift.field a
  show D.what₂.embLL a ∈ O.c'.F
  exact h ▸ (O.jL a).2


set_option maxHeartbeats 1000000 in
theorem tieC_of_serOf (hR : PreChar R) (hT : TieIn T R κ v₀) (O : OMDat T.toCore R i Tp tup)
    (hP : O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0)) {cc : (T.U ((i : ℕ) + 1) O.s0).Comp → ℂ}
    (hs : SerOf O (κ i) (v₀ i (sg0 D A)) cc 1) :
    OneMapTieC O.hle D.what₂.embLL.toRatAlgHom.fieldRange (T.U ((i : ℕ) + 1)) (inC O.c') (Wc D i) O.dict O.mu (xiR D) (wtA (κ i))
      (actLev T.Q.c O.lev2) (actLev O.c' O.lev2) O.dδ O.Cl' O.w O.La O.Nc O.gam O.vol O.ep O.io O.thAd O.Plc cc 1 :=
  ⟨fieldRange_le O hP, (GlobalTheory.FieldBC.secBC_and_cuspBC _ _ _ _ _ _ _ O.hle).2 _ _,
    (GlobalTheory.FieldBC.actLev_and_actBC _ _ _ _ _ _ _ O.hle _ _ hP.act.1).2,
    oneMapRow_of_serOf_ofPre D G Pl0 T0 A T R κ v₀ hR hT i Tp tup O hP cc hs
      (GlobalTheory.ClassSumRule.exists_cusp_isThClsD_ofPre GlobalTheory.ChartFree.chartIndep D G Pl0 T0 A T R κ v₀ hR hT i Tp tup O hP)⟩

end GlobalTheory.RealGeo.PhaseOne

namespace GlobalTheory.RealGeo

open GlobalTheory.AdTh GlobalTheory.PtId GlobalTheory.OneMapTuples PhaseOne


set_option maxHeartbeats 2000000 in
theorem exists_scalar_serOf {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
    {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec} (hC : PreChar R) (hT : TieIn T R κ v₀) (hio : IoExt R)
    (i : Fin D.R.m) (c0L : VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).W) :
    ∃ s : ℂ, ‖s‖ = 1 ∧ ∀ (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup),
      O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → CoefficientBaseChange R i O.jL (inC O.c') c0L O.c0' →
      ∀ c0 : ℂ, ‖c0‖ = 1 → XiConst O (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) c0 →
      ∀ cc, CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.U ((i : ℕ) + 1) O.s0) O.dict O.mu (T.x₀ ((i : ℕ) + 1) O.s0)
        (R.ωP i A.μ0) (R.vacP i) cc → SerOf O (κ i) (v₀ i (sg0 D A)) ((c0⁻¹ * s) • cc) 1 := by
  by_cases hex : ∃ (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup),
    O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0)
  swap
  · exact ⟨1, norm_one, fun Tp tup O hP => absurd ⟨Tp, tup, O, hP⟩ hex⟩
  obtain ⟨Tp₀, tup₀, O₀, hP₀⟩ := hex
  obtain ⟨ka, hka1, hka⟩ := OneScalar.exists_scalar_ofPre D G Pl0 T0 A T R κ v₀ hC hT hio i c0L
  have hs₀ : O₀.s0 = T.toCore.σ₀ := sOv_eq _ _ _
  obtain ⟨hemb, hiso, -⟩ := dict_cast T hT.laws _ (inR i) O₀.s0 (hs₀ ▸ T.toCore.good_σ₀) (Wc D i) O₀.hV (rank_Wc i)
  obtain ⟨δ, hδ⟩ := ShortSeries.thetaKO_eq_short_series_ofPre D G Pl0 T0 A _ R hC i hP₀.lift.std _ _ (iotaW T i) hemb hiso
  obtain ⟨s, hs⟩ : ∃ s : ℂ, s = ka * (((δ : ℤ) : ℂ) ^ GlobalTheory.PtId.degW (T.Q.Dw ((i : ℕ) + 1)) (wtA (κ i)) *
    (-1) ^ GlobalTheory.PtId.degW (T.Q.Dw ((i : ℕ) + 1)) (wtA (κ i))) := ⟨_, rfl⟩
  have hs1 : ‖s‖ = 1 := by
    rcases Int.units_eq_one_or δ with h | h <;> simp [hs, h, hka1]
  have hx : 0 < xiR D := norm_pos_iff.2 ((_root_.map_ne_zero _).2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D))
  have hcm : cmpConst D ka δ (GlobalTheory.PtId.degW (T.Q.Dw ((i : ℕ) + 1)) (wtA (κ i))) =
      s * (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) := by
    rw [lieFac_eq_pow _ hx, hs, cmpConst]
    simp only [Complex.ofReal_pow, Complex.ofReal_inv]
    ring
  refine ⟨s, hs1, fun Tp tup O hP hbc c0 h0 hxi cc hcc => ?_⟩
  have hne : c0 ≠ 0 := norm_ne_zero_iff.1 (h0 ▸ one_ne_zero)
  refine ⟨fun k => ?_, norm_one, fun t h J' hR y x hx f _ hf g => ?_⟩
  · show ‖c0⁻¹ * s * cc k‖ = 1
    rw [norm_mul, norm_mul, norm_inv, h0, hs1, hcc.1 k]
    norm_num
  · have h2 := exact_identity_ofPre hC hT O hP (hka Tp tup O hP hbc) hδ
      (covAt_of_xiConst_ofPre D G Pl0 T0 A T R κ v₀ hC hT i Tp tup O hP c0 hxi) hcc t h J' hR y x hx f hf g
    rw [hcm] at h2
    refine mul_left_cancel₀ hne ((congrArg _ (one_mul _)).trans (h2.trans ?_))
    exact shape hne


set_option maxHeartbeats 1000000 in
theorem exists_serOf_of_ccIs : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), PreChar R → TieIn T R κ v₀ → IoExt R → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ∀ cc, CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.U ((i : ℕ) + 1) O.s0) O.dict O.mu (T.x₀ ((i : ℕ) + 1) O.s0) (R.ωP i A.μ0) (R.vacP i) cc → ∃ u : ℂ, ‖u‖ = 1 ∧ SerOf O (κ i) (v₀ i (sg0 D A)) (u • cc) 1 := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hC hT hio i Tp tup O hP cc hcc
  obtain ⟨_, _, c0L, -, hbc⟩ := hP.lift.c0
  obtain ⟨c0, ⟨m, hm, hr⟩, hxi⟩ := hP.cxi
  have h0 : ‖c0‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hr hm.ne'
  obtain ⟨s, hs1, hs⟩ := exists_scalar_serOf hC hT hio i (c0L i)
  refine ⟨c0⁻¹ * s, ?_, hs Tp tup O hP hbc c0 h0 hxi cc hcc⟩
  rw [norm_mul, norm_inv, h0, hs1]
  norm_num


set_option maxHeartbeats 1000000 in
theorem exists_ccIs_equivAt_serOf_tie : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), PreChar R → TieIn T R κ v₀ → IoExt R → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ∃ cc, CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.U ((i : ℕ) + 1) O.s0) O.dict O.mu (T.x₀ ((i : ℕ) + 1) O.s0) (R.ωP i A.μ0) (R.vacP i) cc ∧ ∃ u : ℂ, ‖u‖ = 1 ∧ O.EquivAt (κ i) (u • cc) ∧ SerOf O (κ i) (v₀ i (sg0 D A)) (u • cc) 1 ∧ OneMapTieC O.hle D.what₂.embLL.toRatAlgHom.fieldRange (T.U ((i : ℕ) + 1)) (inC O.c') (Wc D i) O.dict O.mu (xiR D) (wtA (κ i)) (actLev T.Q.c O.lev2) (actLev O.c' O.lev2) O.dδ O.Cl' O.w O.La O.Nc O.gam O.vol O.ep O.io O.thAd O.Plc (u • cc) 1 := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hC hT hio i Tp tup O hP
  obtain ⟨cc, hcc⟩ := CcEx.exists_ccIs_ofPre GlobalTheory.ChartFree.chartIndep D G Pl0 T0 A T R κ v₀ hC hT i Tp tup O hP
  obtain ⟨u, hu, hS⟩ := exists_serOf_of_ccIs D G Pl0 T0 A T R κ v₀ hC hT hio i Tp tup O hP cc hcc
  exact ⟨cc, hcc, u, hu,
    GlobalTheory.FrameConstMove.equivAt_of_ccIs_ofPre GlobalTheory.ChartFree.chartIndep D G Pl0 T0 A T R κ v₀ hC hT i Tp tup O hP cc hcc u, hS,
    tieC_of_serOf hC hT O hP hS⟩

end GlobalTheory.RealGeo
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TieInOfFwTie
noncomputable section

open NumberField

namespace GlobalTheory.OneMapRefObj

open Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.IndefR.Links _root_.Formalism.L2.Pj _root_.Formalism.L2.DIV Formalism.BasicNotions

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem tieIn_of_fwTie {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, Formalism.MainNotions.WeightFamilies.Wt D ((i : ℕ) + 1)}
    {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec} (t : FWTie T R κ v₀) : TieIn T R κ v₀ :=
  ⟨t.laws, t.alg_eq, t.kap, t.hv₀, t.chiR, t.x0⟩

end GlobalTheory.OneMapRefObj
end
end

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Mult
open GlobalTheory.RealGeo GlobalTheory.OneMapAll GlobalTheory.AdTh

namespace GlobalTheory.Mem.R3.Rw.GeoTies

theorem eq_of_span {H ι X : Type} [AddCommGroup H] [Module ℂ H] {M : ι → Type} [∀ t, AddCommGroup (M t)] [∀ t, Module ℂ (M t)]
    (θ : H →ₗ[ℂ] ((∀ t, M t) →ₘₗ[ℂ] (X → ℂ))) (v : ∀ t, M t) (a b : X) (c : ℂ) {S : Set H} (hS : Submodule.span ℂ S = ⊤)
    (h : ∀ y ∈ S, θ y v a = c * θ y v b) (y : H) : θ y v a = c * θ y v b := by
  have hy : y ∈ Submodule.span ℂ S := hS ▸ Submodule.mem_top
  induction hy using Submodule.span_induction with
  | mem y hy => exact h y hy
  | zero => simp
  | add y y' _ _ h h' =>
    simp only [map_add (f := _), add_apply, Pi.add_apply]
    linear_combination h + h'
  | smul a y _ h =>
    simp only [map_smul, smul_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination a * h

theorem span_image {H H' : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup H'] [Module ℂ H'] (e : H ≃ₗ[ℂ] H') {S : Set H}
    (hS : Submodule.span ℂ S = ⊤) : Submodule.span ℂ (e '' S) = ⊤ := by
  have := congrArg (Submodule.map (e : H →ₗ[ℂ] H')) hS
  rwa [Submodule.map_span, Submodule.map_top, LinearEquiv.range] at this

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section One

variable {C : Formalism.L2.Pj.Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}

def adOver (O : OMDat C R i Tp tup) (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ) (f : Rul (C.Q.Xo ((i : ℕ) + 1)) O.c')
    (g : GA D (Wc D i)) : ℂ :=
  cc (O.dict g).1 * (O.mu g * rdU (unfBC O.hle (C.U ((i : ℕ) + 1)) (inC O.c')) f (O.dict g).1 (O.dict g).2)

theorem adOver_of_isBC (O : OMDat C R i Tp tup) (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ) {m : ℕ}
    {f : Rul (C.Q.Xo ((i : ℕ) + 1)) O.c'} {as : Fin m → O.c'.F} {fs : Fin m → Rul (C.Q.Xo ((i : ℕ) + 1)) C.Q.c}
    (h : IsBC O.hle f as fs) (g : GA D (Wc D i)) : adOver O cc f g = ∑ k, (as k : ℂ) * O.phi cc (fs k) g := by
  have h2 := GlobalTheory.PhaseRational.rdU_of_isBC O.hle (C.U ((i : ℕ) + 1)) (inC O.c') h (O.dict g).1 (O.dict g).2
  refine (congrArg (fun w => cc (O.dict g).1 * (O.mu g * w)) h2).trans ?_
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  show cc _ * (O.mu _ * ((as k : ℂ) * _)) = (as k : ℂ) * (cc _ * O.mu _ * _)
  ring

theorem adOver_act (O : OMDat C R i Tp tup) {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} (hn : κ.n = (Vc D i).rank)
    (hact : ActLev (Xo := C.Q.Xo ((i : ℕ) + 1)) C.Q.c O.lev2) {cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ} (hE : O.EquivAt κ cc)
    {z : G} {k : GA D (Wc D i)} (hk : Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG z) k)
    {f : Rul (C.Q.Xo ((i : ℕ) + 1)) O.c'} (hf : f ∈ cuspOver O κ) (g : GA D (Wc D i)) :
    adOver O cc (actLev O.c' O.lev2 z f) g =
      (∏ PP : R.Pg, ((R.chi ((i : ℕ) + 1) PP.1 (Matrix.GeneralLinearGroup.det (R.eG z PP)) : ℂˣ) : ℂ)) * adOver O cc f (g * k) := by
  obtain ⟨m, as, fs, hfs, hBC⟩ := (GlobalTheory.FieldBC.secBC_and_cuspBC _ _ _ _ _ _ _ O.hle).2 _ (C.U ((i : ℕ) + 1)) _ _ f hf
  have h1 := (GlobalTheory.FieldBC.actLev_and_actBC _ _ _ _ _ _ _ O.hle _ _ hact).2 _ _ z m as fs f ((mem_cusp _ _ _ _ _ _).1 hf).1
    (fun l => ((mem_cusp _ _ _ _ _ _).1 (hfs l)).1) hBC
  rw [adOver_of_isBC O cc h1, adOver_of_isBC O cc hBC, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [(hE z k hk (fs l) (by rw [hn]; exact hfs l)).2 g]
  ring

end One

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
  {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec} {i : Fin D.R.m}

def LiftIsSum (O : OMDat T.toCore R i Unit (fun _ => A.μ0)) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : (R.MW i (sg0 D A)).Vec)
    (cc : (T.U ((i : ℕ) + 1) O.s0).Comp → ℂ) (z : G) (ζ : ℂ) (y : (R.HV i A.μ0).H) : Prop :=
  ∃ h J x f, RepsR R i A.μ0 h (O.bad ()) J (O.Lh ()) (O.gam ()) (O.vol ()) ∧ Place R i A.μ0 h O.c0' y x ∧
    f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) O.c' (wtA κ) (Vc D i).rank ∧ IsSum O () x f ∧
    ∀ q : AutQ (Wc D i), R.thF i A.μ0 y v₀ q.out =
      ζ * (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * adOver O cc (actLev O.c' O.lev2 z f) q.out


set_option maxHeartbeats 2000000 in
theorem oneMapOf_of_span (hR : PreChar R) (hchi : R.grp_chiW) (hT : Formalism.IndefR.FWT.TieIn T R κ v₀)
    (O : OMDat T.toCore R i Unit (fun _ => A.μ0))
    (hF : O.c'.F = D.what₂.embLL.toRatAlgHom.fieldRange)
    (hP : O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0)) {cE : (T.U ((i : ℕ) + 1) O.s0).Comp → ℂ}
    (hU : ∀ k, ‖cE k‖ = 1) (hE : O.EquivAt (κ i) cE) {z : G} (hz : z ∈ Subgroup.center G) {ζ : ℂ}
    (hζL : ζ ∈ D.what₂.embLL.toRatAlgHom.fieldRange) (hζ : ∃ m : ℕ, 0 < m ∧ ζ ^ m = 1)
    (hS : Submodule.span ℂ {y | LiftIsSum O (κ i) (v₀ i (sg0 D A)) cE z ζ y} = ⊤) :
    O.OneMapOf (κ i) (v₀ i (sg0 D A)) cE 1 := by
  have hio : IoExt R := GlobalTheory.IoExtremal.ioExt D G Pl0 T0 A T.Q.c.F R hR.lev hR.fam hR.models hR.thP
  have hn : (κ i).n = (Vc D i).rank :=
    (hT.kap i (D.eTau.symm 1)).2.2.trans (D.sp.V_rank _ (Nat.le_add_left _ _) i.2).symm
  obtain ⟨cc₀, -, u, -, -, hser, -⟩ := exists_ccIs_equivAt_serOf_tie D G Pl0 T0 A T R κ v₀ hR hT hio i _ _ O hP
  generalize u • cc₀ = cc at hser
  have hex := GlobalTheory.ClassSumRule.exists_cusp_isThClsD_ofPre GlobalTheory.ChartFree.chartIndep D G Pl0 T0 A T R κ v₀ hR hT i _ _ O hP ()
  obtain ⟨k, hk, -⟩ := hP.lift.lev z
  obtain ⟨s, hs⟩ : ∃ s : ℂ, s = (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℝ) := ⟨_, rfl⟩
  obtain ⟨χ, hχ⟩ : ∃ χ : ℂ, χ = ∏ PP : R.Pg, ((R.chi ((i : ℕ) + 1) PP.1 (Matrix.GeneralLinearGroup.det (R.eG z PP)) : ℂˣ) : ℂ) :=
    ⟨_, rfl⟩
  have hcc : ∀ c, cc c ≠ 0 := fun c => norm_ne_zero_iff.1 ((hser.1 c).trans_ne one_ne_zero)
  have key : ∀ h J x f y, RepsR R i A.μ0 h (O.bad ()) J (O.Lh ()) (O.gam ()) (O.vol ()) → Place R i A.μ0 h O.c0' y x →
      f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) O.c' (wtA (κ i)) (Vc D i).rank → IsSum O () x f → ∀ g,
      ζ * s * adOver O cE (actLev O.c' O.lev2 z f) g = ζ * χ * (cE (O.dict (g * k)).1 / cc (O.dict (g * k)).1) *
        R.thF i A.μ0 y (v₀ i (sg0 D A)) (g * k) := by
    intro h J x f y hr hy hf hx g
    obtain ⟨f₁, hf₁, hx₁⟩ := hex x
    have e : f = f₁ := isSum_unique hP () hf ((mem_cusp _ _ _ _ _ _).1 hf₁).1 hx hx₁
    have h1 := adOver_act O hn hP.act.1 hE hk (e ▸ hf₁ : f ∈ cuspOver O (κ i)) g
    have h2 := (one_mul _).symm.trans (hser.2.2 () h J hr y x hy f hf hx (g * k))
    rw [h1, h2, ← hχ, ← hs, adOver]
    have := hcc (O.dict (g * k)).1
    field_simp
  have all : ∀ y (q : AutQ (Wc D i)), R.thF i A.μ0 y (v₀ i (sg0 D A)) q.out =
      ζ * χ * (cE (O.dict (q.out * k)).1 / cc (O.dict (q.out * k)).1) * R.thF i A.μ0 y (v₀ i (sg0 D A)) (q.out * k) := by
    intro y q
    refine eq_of_span (R.thF i A.μ0) _ _ _ _ hS (fun y hy => ?_) y
    obtain ⟨h, J, x, f, h1, h2, h3, h4, h5⟩ := hy
    rw [h5 q, ← hs]
    exact key h J x f y h1 h2 h3 h4 _
  have hid : GlobalTheory.PhaseRational.IdentityAt O (κ i) cE 1 := by
    obtain ⟨h, J, hr, -, hA, hPl⟩ := (hP.tuple ()).reps
    refine ⟨hU, norm_one, z, hz, fun t => ⟨ζ, hζL, hζ, fun x hx => ⟨hex x, fun f hf hc q => ?_⟩⟩⟩
    obtain ⟨x₀, hx₀⟩ := (hPl x).1 hx
    have h1 := (all _ q).trans (key h J x f _ hr hx₀ hf hc q.out).symm
    rw [one_mul, hA _ x hx₀]
    refine h1.trans ?_
    rw [hs, mul_right_comm ζ (cE _), mul_assoc (ζ * _) (cE _)]
    rfl
  exact ⟨hE, ⟨hF.ge, (GlobalTheory.FieldBC.secBC_and_cuspBC _ _ _ _ _ _ _ O.hle).2 _ _,
    (GlobalTheory.FieldBC.actLev_and_actBC _ _ _ _ _ _ _ O.hle _ _ hP.act.1).2, hid⟩,
    GlobalTheory.PhaseRational.phRat_of_identity O (κ i) _ cE 1 () rfl hF hP hT.laws.toLawsM (hT.kap i (D.eTau.symm 1)).2.2 hchi
      hR.thP.thF_mem hR.thP.thG hE hid⟩


set_option maxHeartbeats 2000000 in
theorem lift_of_oneMapOf (O : OMDat T.toCore R i Unit (fun _ => A.μ0)) {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : (R.MW i (sg0 D A)).Vec}
    {ι x₀} (hP : O.Pins κ v₀ ι x₀) {cE : (T.U ((i : ℕ) + 1) O.s0).Comp → ℂ} (h : O.OneMapOf κ v₀ cE 1) :
    ∃ z ∈ Subgroup.center G, ∃ ζ ∈ D.what₂.embLL.toRatAlgHom.fieldRange, (∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) ∧
      ∃ h J, RepsR R i A.μ0 h (O.bad ()) J (O.Lh ()) (O.gam ()) (O.vol ()) ∧ ∀ y₀ : A.fam.amb.FL i A.μ0, ∃ x f,
        Place R i A.μ0 h O.c0' (jVx R i A.μ0 y₀) x ∧ f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) O.c' (wtA κ) (Vc D i).rank ∧ IsSum O () x f ∧
        ∀ q : AutQ (Wc D i), R.thF i A.μ0 (jVx R i A.μ0 y₀) v₀ q.out =
          ζ * (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * adOver O cE (actLev O.c' O.lev2 z f) q.out := by
  obtain ⟨-, ⟨-, -, -, -, -, z, hz, h1⟩, -⟩ := h
  obtain ⟨ζ, hζL, hζ, h1⟩ := h1 ()
  obtain ⟨h, J, hr, hPx, hA, hPl⟩ := (hP.tuple ()).reps
  refine ⟨z, hz, ζ, hζL, hζ, h, J, hr, fun y₀ => ?_⟩
  obtain ⟨x, hx⟩ := hPx y₀
  obtain ⟨⟨f, hf, hc⟩, h2⟩ := h1 x ((hPl x).2 ⟨y₀, hx⟩)
  have hf' := ((mem_cusp _ _ _ _ _ _).1 hf).1
  refine ⟨x, f, hx, hf', hc, fun q => ?_⟩
  have h3 := h2 f hf' hc q
  rw [one_mul, hA _ x hx, mul_right_comm ζ (cE _), mul_assoc (ζ * _) (cE _)] at h3
  exact h3

theorem exists_equiv_lift {V : HSp D} {S S' : D.what₂.Tau → SPar} {M : DSModel V S} {M' : DSModel V S'} (hM : ModelSame M M')
    {Γ W W' : Type} {nW : NormedAddCommGroup W} {nW' : NormedAddCommGroup W'} {iW : InnerProductSpace ℂ W}
    {iW' : InnerProductSpace ℂ W'} (h1 : HEq W' W) (h2 : HEq nW' nW) (h3 : HEq iW' iW) {H : HMod (Γ → W)} {H' : HMod (Γ → W')}
    (hH : HEq H' H) {θ : H.H →ₗ[ℂ] MMap M} {θ' : H'.H →ₗ[ℂ] MMap M'} (hθ : HEq θ' θ) {v : M.Vec} {v' : M'.Vec} (hv : HEq v' v) :
    ∃ e : H.H ≃ₗ[ℂ] H'.H, ∀ y, HEq (e y) y ∧ θ' (e y) v' = θ y v := by
  cases h1; cases h2; cases h3; cases hH
  cases M; cases M'
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hM
  dsimp only at a1 a2 a3 a4 a5 a6 a7
  cases a1; cases a2; cases a3; cases a4; cases a5; cases a6; cases a7
  have e1 : θ' = θ := eq_of_heq hθ
  have e2 : v' = v := eq_of_heq hv
  exact ⟨LinearEquiv.refl _ _, fun y => ⟨HEq.rfl, by rw [e1, e2]; rfl⟩⟩

theorem adOver_rulBC {C : Formalism.L2.Pj.Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m} {Tp : Type}
    {tup : Tp → T0} (O : OMDat C R i Tp tup) (hact : ActLev (Xo := C.Q.Xo ((i : ℕ) + 1)) C.Q.c O.lev2)
    (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff C.Q.l) (hle : O.c'.F ≤ c.F) (h₃ : C.Q.c.F ≤ c.F) {lev} (hlev : lev = O.lev)
    (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ) (z : G) {a : (D.host.E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    {f : Rul (C.Q.Xo ((i : ℕ) + 1)) O.c'} (hf : f ∈ sec _ O.c' a n) (g : GA D (Wc D i)) :
    cc (O.dict g).1 * (O.mu g * rdU (unfBC h₃ (C.U ((i : ℕ) + 1)) (inC c))
      (actLev c (fun g => (lev g, LinearMap.id)) z (GlobalTheory.FieldBC.rulBC hle f)) (O.dict g).1 (O.dict g).2) =
      adOver O cc (actLev O.c' O.lev2 z f) g := by
  subst hlev
  obtain ⟨m, as, fs, hfs, h⟩ := (GlobalTheory.FieldBC.secBC_and_cuspBC _ _ _ _ _ _ _ O.hle).1 a n f hf
  have h1 := (GlobalTheory.FieldBC.actLev_and_actBC _ _ _ _ _ _ _ O.hle _ _ hact).2 a n z m as fs f hf hfs h
  have h2 := (GlobalTheory.FieldBC.actLev_and_actBC _ _ _ _ _ _ _ h₃ _ _ hact).2 a n z m _ fs _ (GlobalTheory.FieldBCModel.rulBC_mem_sec hle hf) hfs
    (isBC_rulBC_trans O.hle hle h₃ hf h)
  have e1 := GlobalTheory.PhaseRational.rdU_of_isBC O.hle (C.U ((i : ℕ) + 1)) (inC O.c') h1 (O.dict g).1 (O.dict g).2
  have e2 := GlobalTheory.PhaseRational.rdU_of_isBC h₃ (C.U ((i : ℕ) + 1)) (inC c) h2 (O.dict g).1 (O.dict g).2
  exact congrArg (fun w => cc (O.dict g).1 * (O.mu g * w)) (e2.trans e1.symm)

end GlobalTheory.Mem.R3.Rw.GeoTies

end
