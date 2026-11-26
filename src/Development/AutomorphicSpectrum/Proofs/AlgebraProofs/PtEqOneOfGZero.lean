module

public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.VVAlgebraMapNonnegDvr
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsIntegralEndOfActionLinearPart
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PeriodDatumSignCharactersMemEvalImage
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsPolAVFiniteTypeSubring
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsLiftPrincipallyPolarisedAbelianSquareZero
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsCharacterPairSer
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PadicUnitQuotientPrincipalBasis
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsTangentChartMatrixOfBasis
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsPeriodTowerDatumOfAbelianSchemeSymmetricBu
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.SmoothOfRelativeDimensionOfGrpPullbackLocalRing
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsTorusExtensionPointsPullbackFieldPoint
public import Development.WeilBound.CoreStatements.HodgeTatePoints.IsLocalHomOfFinite
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.RosatiAdjOfPoints

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.TorsrepEx
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.GR

noncomputable section

namespace PositivityTheory.HtPt.Rg

theorem torsrep_ex : ∀ (R : Type) [CommRing R] [IsLocalRing R] (p : ℕ), 1 ≤ p → ∀ (A : Over (Spec (CommRingCat.of R))) [GrpObj A] (L : LB A.left), IsAbelianScheme A → L.IsLB → Out.RelAmple A L → Nonempty (TorsRep A p) := by
  intro R _ _ p hp A _ L hA hL ha
  have := hA.comm
  obtain ⟨hf, hfl, -⟩ := (GlobalTheory.ChF.exists_gen_theta_tensor_and_finite_flat_surjective_pow R A L
    (L.pull (fst A A).left) hA hL ha (LB.isLB_pull hL _)).2 p hp
  obtain ⟨B, cr, al, al', tw, hfree, hfin, y, hy, hu⟩ :=
    GlobalTheory.finRep_kernel_mul_finite_free A (LAlg.mk R : LAlg R) p hf hfl hA.smooth
  have e : al = al' := by
    refine Algebra.algebra_ext _ _ fun r => ?_
    have := @IsScalarTower.algebraMap_apply R R B _ _ _ _ al al' tw r
    exact this.symm
  subst e
  refine ⟨{ A := B, cr := cr, alg := al, free := hfree, fin := hfin, y := y, y_p := hy, univ := ?_ }⟩
  intro S _ _ z hz
  exact hu S z hz

end PositivityTheory.HtPt.Rg
end
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.RiOact
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.GR

namespace PositivityTheory.HtPt.Ri

theorem oact_int : ∀ (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] (P : Out.PolAV (Geo.Tor.Sp O)), Nonempty (P.OAct ℤ) := by
  intro O _ _ _ P
  obtain ⟨R, P₀, φ, hft, -, h₁, h₂⟩ := GlobalTheory.KeyTf.exists_polAV_finiteType_subring O P
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  obtain ⟨o, -⟩ := GlobalTheory.exists_oAct_int GlobalTheory.allSixLaws.1.cube _ P₀
  obtain ⟨o', -⟩ := Geo.Tor.polOActPull _ _ _ P₀ P φ h₁ h₂.symm ℤ o
  exact ⟨o'⟩

end PositivityTheory.HtPt.Ri
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalGroupChartFamily
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualTowerHodgeTateDatum
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualTowerHodgeTateDatum
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.GR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.dual_tower_hodge_tate_datum : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) {R₀ : Type} [CommRing R₀] (g : ℕ) (B : BX R₀) (Tw : ATowerL R₀ p) (Dt : DualTower Tw) [Algebra (Tw.O : Type) C], v.Integers (Tw.O : Type) → v (p : C) < 1 → ∀ [Algebra ℤ_[p] (Tw.O : Type)] (Oe : Type) [CommRing Oe] [Algebra ℤ_[p] Oe] (σ : Oe ≃ₐ[ℤ_[p]] Oe) (cp : (Tw.O : Type)) (D : Dat p g B Tw Dt Oe σ cp) (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] (e : ∀ R : LAlg R₀, B.G R → (sp (R₀ := R₀) (R : Type) ⟶ G)), (∀ R, Function.Bijective (e R)) → (∀ R x y, e R (x + y) = e R x * e R y) → (∀ {R S : LAlg R₀} (f : LHom R S) (x : B.G R), e S (B.map f x) = spMap f.1 ≫ e R x) → ∀ (G' : Over (Spec (CommRingCat.of (Tw.O : Type)))) [GrpObj G'] [IsCommMonObj G'] (ψ : G'.left ⟶ G.left), Geo.Tor.IsGrpPullback G' G (Spec.map (CommRingCat.ofHom (algebraMap R₀ (Tw.O : Type)))) ψ → ∃ pt : Nb p g → (sp (R₀ := (Tw.O : Type)) (Tw.O : Type) ⟶ G'), (∀ t, (pt t).left ≫ ψ = (e Tw.O (ptOf B D.L.τ t)).left) ∧ IsTorsPts G' p pt ∧ ∀ T : TorsRep G' p, D.evImg C = torsFun C T pt := by
  first | exact @PositivityTheory.HtPt.Rf.htd_tie | exact PositivityTheory.HtPt.Rf.htd_tie
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualTowerHodgeTateDatumStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.GR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_tower_hodge_tate_datum : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) {R₀ : Type} [CommRing R₀] (g : ℕ) (B : BX R₀) (Tw : ATowerL R₀ p) (Dt : DualTower Tw) [Algebra (Tw.O : Type) C], v.Integers (Tw.O : Type) → v (p : C) < 1 → ∀ [Algebra ℤ_[p] (Tw.O : Type)] (Oe : Type) [CommRing Oe] [Algebra ℤ_[p] Oe] (σ : Oe ≃ₐ[ℤ_[p]] Oe) (cp : (Tw.O : Type)) (D : Dat p g B Tw Dt Oe σ cp) (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] (e : ∀ R : LAlg R₀, B.G R → (sp (R₀ := R₀) (R : Type) ⟶ G)), (∀ R, Function.Bijective (e R)) → (∀ R x y, e R (x + y) = e R x * e R y) → (∀ {R S : LAlg R₀} (f : LHom R S) (x : B.G R), e S (B.map f x) = spMap f.1 ≫ e R x) → ∀ (G' : Over (Spec (CommRingCat.of (Tw.O : Type)))) [GrpObj G'] [IsCommMonObj G'] (ψ : G'.left ⟶ G.left), Geo.Tor.IsGrpPullback G' G (Spec.map (CommRingCat.ofHom (algebraMap R₀ (Tw.O : Type)))) ψ → ∃ pt : Nb p g → (sp (R₀ := (Tw.O : Type)) (Tw.O : Type) ⟶ G'), (∀ t, (pt t).left ≫ ψ = (e Tw.O (ptOf B D.L.τ t)).left) ∧ IsTorsPts G' p pt ∧ ∀ T : TorsRep G' p, D.evImg C = torsFun C T pt := by
  first | exact @GlobalTheory.CompanionTheory.Relay.dual_tower_hodge_tate_datum | exact GlobalTheory.CompanionTheory.Relay.dual_tower_hodge_tate_datum | (intros; apply GlobalTheory.CompanionTheory.Relay.dual_tower_hodge_tate_datum <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalGroupChartFamily
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.GR

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.Ar.GR

private theorem thetaBar_surj (p : ℕ) [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
    {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (hv : v.Integers O) (ε : PreTilt O p)
    (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p) :
    Function.Surjective (Ainf.thetaBar p O hv ε hε) := by
  intro b
  obtain ⟨a, rfl⟩ := Ainf.theta_surj p O hv b
  exact ⟨Ideal.Quotient.mk _ a, rfl⟩

private theorem thetaBar_mul (p : ℕ) [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
    {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (hv : v.Integers O) (ε : PreTilt O p)
    (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p)
    (x y : Ainf.R0 p O ε) (hx : x ∈ RingHom.ker (Ainf.thetaBar p O hv ε hε))
    (hy : y ∈ RingHom.ker (Ainf.thetaBar p O hv ε hε)) : x * y = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  have ha : a ∈ RingHom.ker (WittVector.fontaineTheta O p) := hx
  have hb : b ∈ RingHom.ker (WittVector.fontaineTheta O p) := hy
  rw [Ainf.ker_theta p O hv ε hε, Ideal.mem_span_singleton'] at ha hb
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨b', rfl⟩ := hb
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton'.2 ⟨a' * b', by ring⟩

private theorem ptOf_act {R₀ : Type} [CommRing R₀] (p : ℕ) [Fact p.Prime] (g : ℕ) (B : BX R₀) (O : LAlg R₀)
    (τ : Ix g → ℕ → B.G O) (h0 : ∀ i, p • τ i 0 = 0) (f : B.G O →+ B.G O)
    (M : Matrix (Ix g) (Ix g) ℤ_[p])
    (hf : ∀ j, f (τ j 0) = ∑ k, (PadicInt.toZModPow (0 + 1) (M k j)).val • τ k 0) (t : TT p g) :
    f (ptOf B τ (red p g t)) = ptOf B τ (red p g (M *ᵥ t)) := by
  have hsum : ∀ (s : Finset (Ix g)) (c : Ix g → ZMod p) (x : B.G O), p • x = 0 →
      (∑ j ∈ s, c j).val • x = ∑ j ∈ s, (c j).val • x := by
    intro s c x hx
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert b s hb ih =>
      rw [Finset.sum_insert hb, Finset.sum_insert hb, GlobalTheory.TateMatrices.val_add_smul _ _ x hx, ih]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [ptOf, red, map_sum, map_nsmul, hf]
  have hred : ∀ k, PadicInt.toZMod ((M *ᵥ t) k) = ∑ j, PadicInt.toZMod (M k j) * PadicInt.toZMod (t j) := by
    intro k
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  simp only [hred]
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hsum _ _ _ (h0 k)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm, GlobalTheory.TateMatrices.val_mul_smul _ _ _ (h0 k), GlobalTheory.TateMatrices.toZMod_val_smul _ _ (h0 k)]

private theorem htd_of_dat {R₀ : Type} [CommRing R₀] (p : ℕ) [Fact p.Prime] (C : Type) [Field C]
    (v : Valuation C NNReal) (Tw : ATowerL R₀ p) [Algebra (Tw.O : Type) C] (hv : v.Integers (Tw.O : Type))
    (hp : ¬IsUnit (p : (Tw.O : Type))) (hc : IsAdicComplete (Ideal.span {(p : (Tw.O : Type))}) (Tw.O : Type))
    [Algebra ℤ_[p] (Tw.O : Type)] (g : ℕ) (OE : Type) [CommRing OE] [StarRing OE]
    (B : BX R₀) (F : FGLaw (Tw.O : Type) g)
    (Y : ∀ R : LAlg R₀, LHom Tw.O R → (Fin g → (R : Type)) → B.G R) (hY : BXChart B Tw.O F.F Y)
    (α : OE → Fin g → PS (Tw.O : Type) 1 g) (hα : ∀ a j, MvPowerSeries.constantCoeff (α a j) = 0)
    (A : OE → OEnd B Tw.O)
    (hA : ∀ b (R : LAlg R₀) (s : LHom Tw.O R) (a : Fin g → (R : Type)), (∀ i, IsNilpotent (a i)) →
      (A b).f s (Y R s a) = Y R s (fun j => nv s.1.toRingHom (α b j) ![a]))
    (Dt : DualTower Tw) (cp : (Tw.O : Type)) (D : Dat p g B Tw Dt (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp)
    (h₁ : D.H.P = 0) (h₂ : D.H.PL = 0)
    (h₃ : ∀ a {R S : LAlg R₀} (s : LHom Tw.O R) (π : LHom R S) (hπ : π.SqZero) (l : Fin g) (i : π.ker)
      (m : Fin g → π.ker), (∀ k, (m k : (R : Type)) = s.1 (D.H.ρL (1 ⊗ₜ[ℤ] a) k l) * i) →
      (A a).f s (B.tg π hπ (D.ch.gb l ⊗ₜ[R₀] i)) = B.tg π hπ (∑ k, D.ch.gb k ⊗ₜ[R₀] m k)) :
    ∃ (H : HodgeTateDatum p g v (Tw.O : Type) (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (S : Matrix (Fin g) (Fin g) (Tw.O : Type)),
      H.P = 0 ∧ H.PL = 0 ∧ IsUnit S ∧ (∀ a : OE, lin (α a) * S = S * H.ρL (1 ⊗ₜ[ℤ] a)) ∧
      (∀ i, ∃ u : PS (Tw.O : Type) 1 g, IsCh F.F u ∧ Sᵀ *ᵥ dl u = fun l => H.Ht l i) ∧
      H.AA.carrier = D.evImg C ∧ H.ρ = D.H.ρ := by
  obtain ⟨S, hS, hT⟩ := GlobalTheory.T.exists_tangentChartMatrix_of_basis R₀ B Tw.O g F Y hY D.ch.gb
  refine ⟨GlobalTheory.EvClose.htdOfDat D C v (Function.Injective.isDomain _ hv.hom_inj) hv.hom_inj, S, h₁, h₂, hS,
    fun a => ?_, fun i => ?_, rfl, rfl⟩
  · exact GlobalTheory.T.jacobian_mul_tangentChartMatrix_intertwines R₀ B Tw.O g F Y hY D.ch.gb S hT (A a) (α a) _ (hα a) (hA a) (h₃ a)
  · obtain ⟨u, hu, hP⟩ := GlobalTheory.T.exists_character_pairSer_alt R₀ B Tw.O g F Y hY p hp hc (D.L.τ i) (D.L.τ_tors i) (D.L.τ_compat i)
    refine ⟨u, hu, ?_⟩
    rw [GlobalTheory.T.linear_part_pairing_series_eq_height R₀ B p Tw Dt g Y D.ch.gb S hT (D.L.τ i) u hu.1 hP (D.L.ht i) (D.L.ht_spec i)]
    funext l
    exact (D.L.Ht_eq l i).symm

private theorem htd_of_tower (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (hv : v.Integers O) (ε : PreTilt O p)
    (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p)
    (Tw : ATowerL (Ainf.R0 p O ε) p) (hTw : Tw = Ainf.ainfTowerL p O hv ε hε)
    [Algebra (Tw.O : Type) C] (hv' : v.Integers (Tw.O : Type))
    [hp : Fact ¬IsUnit (p : (Tw.O : Type))]
    [hc : IsAdicComplete (Ideal.span {(p : (Tw.O : Type))}) (Tw.O : Type)]
    [Algebra ℤ_[p] (Tw.O : Type)] (hvp : v (p : C) < 1)
    (T : Type) [CommRing T] [IsNoetherianRing T] (P₀ : Out.PolAV (Geo.Tor.Sp T)) (io : T →+* (Tw.O : Type))
    (P : Out.PolAV (Geo.Tor.Sp (Tw.O : Type))) (φ : P.A.left ⟶ P₀.A.left)
    (h₁ : Geo.Tor.IsGrpPullback P.A P₀.A (Geo.Tor.spMap io) φ) (h₂ : Geo.Tor.LBIso P.L (P₀.L.pull φ))
    (h₃ : P.g = P₀.g) (h₄ : 1 ≤ P.g) (OE : Type) [CommRing OE] [StarRing OE] (o : P.OAct OE)
    (F : FGLaw (Tw.O : Type) P.g) (X : Fam P.A P.g) (hX : NilChart P.A F.F X)
    (α : OE → Fin P.g → PS (Tw.O : Type) 1 P.g) (hα : ∀ a, Reads X X (o.act a) (α a)) :
    ∃ (H : HodgeTateDatum p P.g v (Tw.O : Type) (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) Tw.c)
      (S : Matrix (Fin P.g) (Fin P.g) (Tw.O : Type))
      (pt : Nb p P.g → (sp (R₀ := (Tw.O : Type)) (Tw.O : Type) ⟶ P.A)),
      H.P = 0 ∧ H.PL = 0 ∧ IsUnit S ∧ (∀ a : OE, lin (α a) * S = S * H.ρL (1 ⊗ₜ[ℤ] a)) ∧
      (∀ i, ∃ u : PS (Tw.O : Type) 1 P.g, IsCh F.F u ∧ Sᵀ *ᵥ dl u = fun l => H.Ht l i) ∧
      IsTorsPts P.A p pt ∧ (∀ T : TorsRep P.A p, H.AA.carrier = torsFun C T pt) ∧
      ∀ (a : OE) (t : TT p P.g), pt (red p P.g (H.ρ (1 ⊗ₜ[ℤ] a) *ᵥ t)) = pt (red p P.g t) ≫ o.act a := by
  have hsurj : Function.Surjective (algebraMap (Ainf.R0 p O ε) (Tw.O : Type)) := by
    subst hTw; exact thetaBar_surj p O hv ε hε
  have hmul : ∀ x y : Ainf.R0 p O ε, x ∈ RingHom.ker (algebraMap (Ainf.R0 p O ε) (Tw.O : Type)) →
      y ∈ RingHom.ker (algebraMap (Ainf.R0 p O ε) (Tw.O : Type)) → x * y = 0 := by
    subst hTw; exact thetaBar_mul p O hv ε hε
  have hker : RingHom.ker (algebraMap (Ainf.R0 p O ε) (Tw.O : Type)) ^ 2 = ⊥ := by
    refine (pow_two _).trans (eq_bot_iff.2 ?_)
    exact Ideal.mul_le.2 fun x hx y hy => (Submodule.mem_bot _).2 (hmul x y hx hy)
  haveI : IsLocalRing (Ainf.R0 p O ε) := Ainf.local_of_surj_sq _ hsurj (fun k hk => hmul k k hk hk)
  obtain ⟨G, iG, cG, Q, ψ, ψ₂, hab, hQ, t₁, t₂, hsym, hamp, hnd, hpb, hsq, hΛ⟩ :=
    GlobalTheory.T.exists_lift_principally_polarised_abelian_square_zero p C v (Tw.O : Type) hv' T P₀ io P φ h₁ h₂ h₃ h₄ _ _ hsurj hker
  letI : Algebra (Ainf.R0 p O ε) C :=
    ((algebraMap (Tw.O : Type) C).comp (algebraMap (Ainf.R0 p O ε) (Tw.O : Type))).toAlgebra
  haveI : IsScalarTower (Ainf.R0 p O ε) (Tw.O : Type) C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hp0 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  have hsm := GlobalTheory.T.smoothOfRelativeDimension_of_grpPullback_localRing _ _ _ G P.A ψ P.g hab hpb P.smoothDim
  obtain ⟨hθ, hn⟩ := GlobalTheory.T.cube_trivial_and_finite_flat_surjective_mul_abelianScheme _ G _ Q hab (LB.isLB_pull hQ _) hamp hQ
  obtain ⟨hf₁, hf₂, hf₃⟩ := hn p hp0
  have hcard := GlobalTheory.T.card_torsion_of_polarisedAbelianScheme_lift _ _ C G P ψ hpb p (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  have hros := fun a : OE =>
    GlobalTheory.T.exists_generator_of_rosatiAdjoint_lambdaBundle _ P _ Q ψ₂ hQ hΛ _ _ (o.hom a) (o.hom (star a)) (o.rosati a)
  have key : ∃ (B : BX (Ainf.R0 p O ε)) (e : ∀ R : LAlg (Ainf.R0 p O ε), B.G R → (sp (R₀ := (Ainf.R0 p O ε)) (R : Type) ⟶ G)) (Ad : OE → OAdj B Tw.O), (∀ R, Function.Bijective (e R)) ∧ (∀ R x y, e R (x + y) = e R x * e R y) ∧ (∀ {R S : LAlg (Ainf.R0 p O ε)} (f : LHom R S) (x : B.G R), e S (B.map f x) = spMap f.1 ≫ e R x) ∧ (∀ a, (∀ {R : LAlg (Ainf.R0 p O ε)} (s : LHom Tw.O R) (x : B.G R) (x' : Over.mk (Spec.map (CommRingCat.ofHom s.1.toRingHom)) ⟶ P.A), x'.left ≫ ψ = (e R x).left → (x' ≫ o.act a).left ≫ ψ = (e R ((Ad a).a.f s x)).left)) ∧ ∃ (Dt : DualTower Tw) (D : Dat p P.g B Tw Dt (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) Tw.c), D.H.P = 0 ∧ D.H.PL = 0 ∧ (∀ a {R S : LAlg (Ainf.R0 p O ε)} (s : LHom Tw.O R) (π : LHom R S) (hπ : π.SqZero) (l : Fin P.g) (i : π.ker) (m : Fin P.g → π.ker), (∀ k, (m k : (R : Type)) = s.1 (D.H.ρL (1 ⊗ₜ[ℤ] a) k l) * i) → (Ad a).a.f s (B.tg π hπ (D.ch.gb l ⊗ₜ[(Ainf.R0 p O ε)] i)) = B.tg π hπ (∑ k, D.ch.gb k ⊗ₜ[(Ainf.R0 p O ε)] m k)) ∧ (∀ a j, (Ad a).a.f (LHom.id Tw.O) (D.L.τ j 0) = ∑ k, (PadicInt.toZModPow (0 + 1) (D.H.ρ (1 ⊗ₜ[ℤ] a) k j)).val • D.L.τ k 0) := by
    subst hTw
    obtain ⟨B, e, Ad, k₁, k₂, k₃, k₄, Dt, D, k₅, k₆, k₇, k₈⟩ :=
      GlobalTheory.T.exists_periodTowerDatum_of_abelianScheme_symmetricBundle p O hv ε hε P.g G Q hab hsm hQ hθ t₁ t₂ hsym hf₁ hf₂ hf₃ hv' (hnd _) hcard
        P.A ψ ψ₂ P.isAb hpb hsq OE (cjZ OE) o.toRingAct (fun a => star_star a) hros
    exact ⟨B, e, Ad, k₁, k₂, k₃, k₄, Dt, D, k₅, k₆, k₇, fun a j => k₈ a j 0⟩
  obtain ⟨B, e, Ad, k₁, k₂, k₃, k₄, Dt, D, k₅, k₆, k₇, k₈⟩ := key
  obtain ⟨Y, hY, hR⟩ := GlobalTheory.T.abelianFunctorNilChart_of_nilpotent_chart _ G B e k₁ k₂ k₃ Tw.O P.A ψ hpb P.g F.F X hX
  obtain ⟨H, S, e₁, e₂, e₃, e₄, e₅, e₆, e₇⟩ :=
    htd_of_dat p C v Tw hv' hp.out hc P.g OE B F Y hY α (fun a => (hα a).1) (fun a => (Ad a).a)
      (fun b => hR _ _ _ (hα b) (k₄ b)) Dt Tw.c D k₅ k₆ k₇
  obtain ⟨pt, hpt, hT, hE⟩ :=
    GlobalTheory.T.dual_tower_hodge_tate_datum p C v P.g B Tw Dt hv' hvp _ (sigE p OE) Tw.c D G e k₁ k₂ k₃ P.A ψ hpb
  refine ⟨H, S, pt, e₁, e₂, e₃, e₄, e₅, hT, fun T => e₆.trans (hE T), fun a t => ?_⟩
  have h0 : ∀ i, p • D.L.τ i 0 = 0 := fun i => by
    have h := D.L.τ_tors i 0
    rwa [zero_add, pow_one] at h
  have hAct := ptOf_act p P.g B Tw.O D.L.τ h0 ((Ad a).a.f (LHom.id Tw.O)) (D.H.ρ (1 ⊗ₜ[ℤ] a)) (k₈ a) t
  have hA := k₄ a (LHom.id Tw.O) (ptOf B D.L.τ (red p P.g t)) (pt (red p P.g t)) (hpt _)
  rw [hAct] at hA
  rw [e₇]
  apply Over.OverMorphism.ext
  apply hpb.1.hom_ext
  · rw [hpt]
    exact hA.symm
  · simp

theorem exists_htd_act : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (P : Out.PolAV (Geo.Tor.Sp O)), 1 ≤ P.g → ∀ (g : ℕ), P.g = g → ∀ (OE : Type) [CommRing OE] [StarRing OE] (o : P.OAct OE) (F : FGLaw O g) (X : Fam P.A g), NilChart P.A F.F X → ∀ α : OE → Fin g → PS O 1 g, (∀ a, Reads X X (o.act a) (α a)) → ∃ (cp : O) (_ : HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (H : HodgeTateDatum p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (S : Matrix (Fin g) (Fin g) O) (pt : Nb p g → (sp (R₀ := O) O ⟶ P.A)), H.P = 0 ∧ H.PL = 0 ∧ IsUnit S ∧ (∀ a : OE, lin (α a) * S = S * H.ρL (1 ⊗ₜ[ℤ] a)) ∧ (∀ i, ∃ u : PS O 1 g, IsCh F.F u ∧ Sᵀ *ᵥ dl u = fun l => H.Ht l i) ∧ IsTorsPts P.A p pt ∧ (∀ T : TorsRep P.A p, H.AA.carrier = torsFun C T pt) ∧ ∀ (a : OE) (t : TT p g), pt (red p g (H.ρ (1 ⊗ₜ[ℤ] a) *ᵥ t)) = pt (red p g t) ≫ o.act a := by
  intro p _ C _ _ _ v O _ iA hv iF iC iZ P h₄ g hg OE _ _ o F X hX α hα
  subst hg
  haveI : IsDomain O := Function.Injective.isDomain _ hv.hom_inj
  haveI : IsLocalRing O := Ainf.O_local O hv
  obtain ⟨R, P₀, φ, hft, hg₀, h₁, h₂⟩ := GlobalTheory.KeyTf.exists_polAV_finiteType_subring O P
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  have hvp : v (p : C) < 1 := by
    have h := lt_of_le_of_ne (hv.map_le_one (p : O)) fun h => iF.out (hv.isUnit_iff_valuation_eq_one.2 h)
    simpa using h
  obtain ⟨ε, hε⟩ := exists_eps (p := p) C v O hv
  exact ⟨_, GlobalTheory.T.hodgeTate_datum_hypotheses_period_tower p O hv ε hε OE,
    @htd_of_tower p _ C _ _ _ v O _ _ _ _ hv ε hε _ rfl iA hv iF
      iC iZ hvp R _ _ P₀ R.subtype P φ h₁ h₂ hg₀.symm h₄ OE _ _ o F X hX α hα⟩

end GlobalTheory.CompanionTheory.Ar.GR
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalGroupChartFamilyStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.GR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_group_chart_family : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (P : Out.PolAV (Geo.Tor.Sp O)), 1 ≤ P.g → ∀ (g : ℕ), P.g = g → ∀ (OE : Type) [CommRing OE] [StarRing OE] (o : P.OAct OE) (F : FGLaw O g) (X : Fam P.A g), NilChart P.A F.F X → ∀ α : OE → Fin g → PS O 1 g, (∀ a, Reads X X (o.act a) (α a)) → ∃ (cp : O) (_ : HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (H : HodgeTateDatum p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (S : Matrix (Fin g) (Fin g) O) (pt : Nb p g → (sp (R₀ := O) O ⟶ P.A)), H.P = 0 ∧ H.PL = 0 ∧ IsUnit S ∧ (∀ a : OE, lin (α a) * S = S * H.ρL (1 ⊗ₜ[ℤ] a)) ∧ (∀ i, ∃ u : PS O 1 g, IsCh F.F u ∧ Sᵀ *ᵥ dl u = fun l => H.Ht l i) ∧ IsTorsPts P.A p pt ∧ (∀ T : TorsRep P.A p, H.AA.carrier = torsFun C T pt) ∧ ∀ (a : OE) (t : TT p g), pt (red p g (H.ρ (1 ⊗ₜ[ℤ] a) *ᵥ t)) = pt (red p g t) ≫ o.act a := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.exists_htd_act | exact GlobalTheory.CompanionTheory.Ar.GR.exists_htd_act | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.exists_htd_act <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AbelianSchemeTorsionRepresentation
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AbelianSchemeTorsionRepresentation
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.GR

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem torsRep_nonempty_of_relAmple : ∀ (R : Type) [CommRing R] [IsLocalRing R] (p : ℕ), 1 ≤ p → ∀ (A : Over (Spec (CommRingCat.of R))) [GrpObj A] (L : LB A.left), IsAbelianScheme A → L.IsLB → Out.RelAmple A L → Nonempty (TorsRep A p) :=
  PositivityTheory.HtPt.Rg.torsrep_ex

end GlobalTheory.CompanionTheory.Ar.GR
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AbelianSchemeTorsionRepresentationStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.GR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_scheme_torsion_representation : ∀ (R : Type) [CommRing R] [IsLocalRing R] (p : ℕ), 1 ≤ p → ∀ (A : Over (Spec (CommRingCat.of R))) [GrpObj A] (L : LB A.left), IsAbelianScheme A → L.IsLB → Out.RelAmple A L → Nonempty (TorsRep A p) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.torsRep_nonempty_of_relAmple | exact GlobalTheory.CompanionTheory.Ar.GR.torsRep_nonempty_of_relAmple | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.torsRep_nonempty_of_relAmple <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PolarisedVarietyIntegerAction
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PolarisedVarietyIntegerAction
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.GR

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem polAV_oAct_int : ∀ (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] (P : Out.PolAV (Geo.Tor.Sp O)), Nonempty (P.OAct ℤ) :=
  @PositivityTheory.HtPt.Ri.oact_int

end GlobalTheory.CompanionTheory.Ar.GR
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PolarisedVarietyIntegerActionStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.GR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarised_variety_integer_action : ∀ (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] (P : Out.PolAV (Geo.Tor.Sp O)), Nonempty (P.OAct ℤ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.polAV_oAct_int | exact GlobalTheory.CompanionTheory.Ar.GR.polAV_oAct_int | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.polAV_oAct_int <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeTateDatumReduceScalars
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeTateDatumReduceScalars
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.GR

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem htd_restrict_coefficients : ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] (Oe : Type) [CommRing Oe] [Algebra ℤ_[p] Oe] (σ : Oe ≃ₐ[ℤ_[p]] Oe) (cp : R), HodgeTateSetting p v R Oe σ cp → ∀ H : HodgeTateDatum p g v R Oe σ cp, HodgeTateSetting p v R ℤ_[p] AlgEquiv.refl cp ∧ ∃ H' : HodgeTateDatum p g v R ℤ_[p] AlgEquiv.refl cp, H'.AA = H.AA ∧ H'.Ht = H.Ht ∧ H'.Bt = H.Bt ∧ H'.E = H.E := by
  intro p _ g C _ v R _ _ _ Oe _ _ σ cp hS H
  refine ⟨⟨hS.integers, hS.p_lt, hS.p_ne, hS.cp_val, fun _ => rfl⟩,
    { ρ := H.ρ.comp (Algebra.ofId _ _)
      ρL := H.ρL.comp (algebraMap _ _)
      P := H.P
      PL := H.PL
      E := H.E
      E_alternating := H.E_alternating
      isUnit_det_E := H.isUnit_det_E
      E_equivariant := fun a => ?_
      projectors := ⟨H.projectors.1, H.projectors.2.1, H.projectors.2.2.1, fun a => H.projectors.2.2.2.1 _, fun a => H.projectors.2.2.2.2 _⟩
      Ht := H.Ht
      Bt := H.Bt
      Ht_equivariant := ⟨fun a => ?_, H.Ht_equivariant.2⟩
      form_eq_alt := H.form_eq_alt
      AA := H.AA
      h3 := fun a => H.h3 _
      h4 := H.h4
      h5 := H.h5
      φ := H.φ
      cotangent_surjective := H.cotangent_surjective
      cotangent_ker_eq := H.cotangent_ker_eq
      cotangent_linear := fun a => H.cotangent_linear _ }, rfl, rfl, rfl, rfl⟩
  · have := H.E_equivariant (algebraMap ℤ_[p] Oe a)
    rw [σ.commutes] at this
    exact this
  · have := H.Ht_equivariant.1 (algebraMap ℤ_[p] Oe a)
    rw [σ.commutes] at this
    exact this

end GlobalTheory.CompanionTheory.Ar.GR
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeTateDatumReduceScalarsStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.GR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_datum_reduce_scalars : ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] (Oe : Type) [CommRing Oe] [Algebra ℤ_[p] Oe] (σ : Oe ≃ₐ[ℤ_[p]] Oe) (cp : R), HodgeTateSetting p v R Oe σ cp → ∀ H : HodgeTateDatum p g v R Oe σ cp, HodgeTateSetting p v R ℤ_[p] AlgEquiv.refl cp ∧ ∃ H' : HodgeTateDatum p g v R ℤ_[p] AlgEquiv.refl cp, H'.AA = H.AA ∧ H'.Ht = H.Ht ∧ H'.Bt = H.Bt ∧ H'.E = H.E := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.htd_restrict_coefficients | exact GlobalTheory.CompanionTheory.Ar.GR.htd_restrict_coefficients | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.htd_restrict_coefficients <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TrivialPolarizedAbelianPointEqOne
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TrivialPolarizedAbelianPointEqOne
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.DimZero

theorem isIso_hom_of_relDim_zero {S : Scheme.{0}} (A : Over S) [GrpObj A] (h : IsAbelianScheme A)
    (hd : SmoothOfRelativeDimension 0 A.hom) : IsIso A.hom := by
  haveI := h.proper
  haveI := h.geomConnected
  haveI : Etale A.hom := (Etale.iff_smoothOfRelativeDimension_zero _).2 hd
  let e : S ⟶ A.left := eSec A
  have he : e ≫ A.hom = 𝟙 S := Over.w η[A]
  haveI : IsClosedImmersion e := by
    haveI : IsClosedImmersion (e ≫ A.hom) := by rw [he]; infer_instance
    exact IsClosedImmersion.of_comp e A.hom
  haveI : MorphismProperty.HasOfPostcompProperty @IsOpenImmersion
      (MorphismProperty.diagonal @IsOpenImmersion) :=
    MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr le_rfl
  haveI : IsOpenImmersion e :=
    MorphismProperty.of_postcomp (W := @IsOpenImmersion)
      (W' := MorphismProperty.diagonal @IsOpenImmersion) e A.hom
      (inferInstanceAs (IsOpenImmersion (pullback.diagonal A.hom))) (by rw [he]; infer_instance)
  have hs : ∀ y : S, A.hom (e y) = y := fun y => by rw [← Scheme.Hom.comp_apply, he]; rfl
  haveI : IsIso e := by
    refine isIso_of_isOpenImmersion_of_opensRange_eq_top _ (top_unique fun a _ => ?_)
    have hc := (A.hom.isConnected_preimage_singleton (A.hom a)).isPreconnected
    have hcl : IsClopen (Set.range e) :=
      ⟨e.isClosedEmbedding.isClosed_range, e.isOpenEmbedding.isOpen_range⟩
    exact hc.subset_isClopen hcl ⟨e (A.hom a), hs _, _, rfl⟩ rfl
  haveI : IsIso (e ≫ A.hom) := by rw [he]; infer_instance
  exact IsIso.of_isIso_comp_left e _

theorem over_hom_eq_of_mono {S : Scheme.{0}} {T A : Over S} [Mono A.hom] (x y : T ⟶ A) : x = y := by
  ext1
  rw [← cancel_mono A.hom, Over.w x, Over.w y]

theorem eq_one_of_g_eq_zero (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (P : Out.PolAV (Spec (CommRingCat.of R))) (hg : P.g = 0) (z : sp (R₀ := R) R ⟶ P.A) :
    z = 1 := by
  have hd : SmoothOfRelativeDimension 0 P.A.hom := hg ▸ P.smoothDim
  haveI := isIso_hom_of_relDim_zero P.A P.isAb hd
  exact over_hom_eq_of_mono _ _

end GlobalTheory.CompanionTheory.Ar.DimZero
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TrivialPolarizedAbelianPointEqOneStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trivial_polarized_abelian_point_eq_one : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (P : Out.PolAV (Spec (CommRingCat.of R))), P.g = 0 → ∀ z : sp (R₀ := R) R ⟶ P.A, z = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.DimZero.eq_one_of_g_eq_zero | exact GlobalTheory.CompanionTheory.Ar.DimZero.eq_one_of_g_eq_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.DimZero.eq_one_of_g_eq_zero <;> assumption)
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.GR

namespace GlobalTheory.CompanionTheory.Ar.GR.Top

theorem pt_eq_one_of_g_zero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (P : Out.PolAV (Spec (CommRingCat.of R))), P.g = 0 → ∀ z : sp (R₀ := R) R ⟶ P.A, z = 1 :=
  GlobalTheory.T.trivial_polarized_abelian_point_eq_one

theorem exists_cp (p : ℕ) [hp : Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
    {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C] (hv : v.Integers R)
    (hpv : v (p : C) < 1) :
    ∃ cp : R, v (algebraMap R C cp) ^ (p - 1) = v (algebraMap R C (p : R)) := by
  have h1 : 0 < p - 1 := Nat.sub_pos_of_lt hp.out.one_lt
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (p : C) h1
  have hle : v c ≤ 1 := by
    by_contra h
    push_neg at h
    have : 1 < v c ^ (p - 1) := one_lt_pow₀ h h1.ne'
    rw [← map_pow, hc] at this
    exact absurd hpv (not_lt.2 this.le)
  obtain ⟨r, hr⟩ := hv.exists_of_le_one hle
  exact ⟨r, by rw [hr, ← v.map_pow, hc, map_natCast (algebraMap R C)]⟩

theorem hopf_carrier_g_zero {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {R : Type} [CommRing R]
    [Algebra R C] (AA : ReciprocityTheory.PGsh.L2.HopfOrder (C := C) R (Nb p 0)) :
    AA.carrier = ReciprocityTheory.PGsh.L2.intFun R (Nb p 0) := by
  let _ : Unique (Nb p 0) := Pi.uniqueOfIsEmpty _
  refine le_antisymm AA.le_int fun f hf => ?_
  obtain ⟨r, hr⟩ := hf default
  have : f = r • (1 : Nb p 0 → C) := by
    funext x
    rw [Subsingleton.elim x default, ← hr]
    simp [Algebra.smul_def]
  rw [this]
  exact AA.carrier.smul_mem r AA.one_mem

theorem torsFun_one_eq {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {R : Type} [CommRing R]
    [Algebra R C] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] (T : TorsRep G p) :
    torsFun C T (fun _ : Nb p 0 => (1 : sp (R₀ := R) R ⟶ G)) = ReciprocityTheory.PGsh.L2.intFun R (Nb p 0) := by
  let _ : Unique (Nb p 0) := Pi.uniqueOfIsEmpty _
  obtain ⟨φ₀, hφ₀, -⟩ := T.univ R (1 : sp (R₀ := R) R ⟶ G) (one_pow p)
  ext f
  constructor
  · rintro ⟨a, ha⟩ x
    exact ⟨φ₀ a, (ha x φ₀ hφ₀).symm⟩
  · intro hf
    obtain ⟨r, hr⟩ := hf default
    refine ⟨algebraMap R T.A r, fun x φ _ => ?_⟩
    rw [Subsingleton.elim x default, ← hr, AlgHom.commutes]
    rfl

theorem main : HodgeTateDatumStatement := by
  intro p _ C _ _ _ v R _ _ hv hp hcomp _ P
  haveI : IsLocalRing R := isLocal_of_integers hv
  haveI : IsDomain R := hv.hom_inj.isDomain (algebraMap R C)
  haveI : Fact ¬IsUnit (p : R) := ⟨fun hu => by
    have h1 := hv.one_of_isUnit hu
    rw [map_natCast] at h1
    rw [h1] at hp
    exact lt_irrefl _ hp⟩
  haveI : IsAdicComplete (Ideal.span {(p : R)}) R := hcomp
  haveI : IsCommMonObj P.A := P.isAb.comm
  have hT : Nonempty (TorsRep P.A p) :=
    GlobalTheory.T.abelian_scheme_torsion_representation R p (Fact.out : p.Prime).one_le P.A P.L P.isAb P.isLB P.ample
  refine ⟨hT, ?_⟩
  rcases Nat.eq_zero_or_pos P.g with hg | hg
  · obtain ⟨cp, hcp⟩ := exists_cp p hv hp
    have hpne : v (algebraMap R C (p : R)) ≠ 0 := by
      rw [map_natCast]
      exact fun h => Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero ((Valuation.zero_iff v).1 h)
    have hplt : v (algebraMap R C (p : R)) < 1 := by rwa [map_natCast]
    have hS : HodgeTateSetting p v R (ℤ_[p] ⊗[ℤ] ℤ) (sigE p ℤ) cp := by
      refine ⟨hv, hplt, hpne, hcp, ?_⟩
      intro a
      induction a using TensorProduct.induction_on with
      | zero => simp
      | tmul x y =>
        have h : ∀ (x : ℤ_[p]) (y : ℤ), sigE p ℤ (x ⊗ₜ[ℤ] y) = x ⊗ₜ[ℤ] star y := fun _ _ => rfl
        rw [h, h, star_star]
      | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
    obtain ⟨H⟩ := GlobalTheory.ChF.htd_dim_zero p C v R hv ℤ cp
    rw [← hg] at H
    obtain ⟨hS', H', -⟩ := GlobalTheory.T.hodge_tate_datum_reduce_scalars p P.g C v R (ℤ_[p] ⊗[ℤ] ℤ) (sigE p ℤ) cp hS H
    have h1 := pt_eq_one_of_g_zero R P hg
    revert H'
    rw [hg]
    intro H'
    refine ⟨cp, hS', H', fun _ => 1, ⟨?_, ?_, ?_⟩, fun T => ?_⟩
    · intro x y _
      let _ : Unique (Nb p 0) := Pi.uniqueOfIsEmpty _
      exact Subsingleton.elim x y
    · intro x y
      exact (_root_.mul_one _).symm
    · intro z
      exact ⟨fun _ => ⟨0, (h1 z).symm⟩, fun _ => by rw [h1 z]; exact one_pow p⟩
    · rw [hopf_carrier_g_zero, torsFun_one_eq]
  · obtain ⟨F, X, hX⟩ := GlobalTheory.ChF.exists_nilChart R P.A P.g P.smoothDim
    obtain ⟨o⟩ := GlobalTheory.T.polarised_variety_integer_action R P
    have hα : ∀ a : ℤ, ∃ φ, Reads X X (o.act a) φ := fun a =>
      GlobalTheory.ChF.exists_reads R P.A P.A _ _ F.F F.F X X hX hX (o.act a) (o.hom a)
    choose α hα using hα
    obtain ⟨cp, hS, H, S, pt, -, -, -, -, -, hpt, hAA, -⟩ :=
      GlobalTheory.T.formal_group_chart_family p C v R hv P hg P.g rfl ℤ o F X hX α hα
    obtain ⟨hS', H', hAA', -⟩ := GlobalTheory.T.hodge_tate_datum_reduce_scalars p P.g C v R (ℤ_[p] ⊗[ℤ] ℤ) (sigE p ℤ) cp hS H
    exact ⟨cp, hS', H', pt, hpt, fun T => by rw [hAA']; exact hAA T⟩

end GlobalTheory.CompanionTheory.Ar.GR.Top
