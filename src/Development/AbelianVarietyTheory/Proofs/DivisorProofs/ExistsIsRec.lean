module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TiedRecordExistsOfActionPin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitaryOnWeilDatumTransportAdelicSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerOperatorHeisenbergLawApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFunctionalArchimedeanFactor
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemRangeSrcForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsRec
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.FormTies GlobalTheory.BigOn GlobalTheory.RunDepth

namespace GlobalTheory.BigOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem eq_kaR {D : D7} {L : SizeData₂ D} {Pm : ParameterChoice' D L} (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (i : Fin D.R.m)
    (w : WeightFamilies.Wt D ((i : ℕ) + 1))
    (hP : ∀ τ (k : Fin (D.R.sigW ((i : ℕ) + 1)).1), w.aP τ k = aPl D i ((Wc D i).sig (tauE D τ)).1 τ k)
    (hM : ∀ τ (k : Fin (D.R.sigW ((i : ℕ) + 1)).2),
      w.aM τ k = aMi D i ((Wc D i).sig (tauE D τ)).1 ((Wc D i).sig (tauE D τ)).2 τ k)
    (hn : w.n = D.R.nV) : w = kaR Tp hK ((i : ℕ) + 1) := by
  have hi := i.2
  have hk := D.R.m_add_three_le_k
  have h1 := (inR_succ i).1
  have h2 := (inR_succ i).2
  have hs : ∀ τ, (Wc D i).sig (tauE D τ) = D.R.sigW ((i : ℕ) + 1) := fun τ => D.sp.W_sigval _ h1 h2 _
  have hp : (D.R.sigW ((i : ℕ) + 1)).1 = D.R.k + i := by
    simp only [Ranks.sigW]; omega
  have hq : i + 1 + (D.R.sigW ((i : ℕ) + 1)).2 = D.R.m := by
    simp only [Ranks.sigW]; omega
  have eP : w.aP = (kaR Tp hK ((i : ℕ) + 1)).aP := by
    funext τ a
    have h := (hK _ h1 h2 τ).1 a
    have h' := GlobalTheory.RecordWeightVec.aPl_eq_aPlusQ D i τ a (hp ▸ a.2)
    have e := kaWt_big D hK (even_nV Tp) _ h1 h2 τ a
    rw [← h, ← hp, ← e] at h'
    rw [hP τ a, hs τ]
    exact_mod_cast h'
  have eM : w.aM = (kaR Tp hK ((i : ℕ) + 1)).aM := by
    funext τ c
    have h := (hK _ h1 h2 τ).2 (Fin.rev c)
    have hc := c.2
    have h' := GlobalTheory.RecordWeightVec.aMi_eq_aMinusQ D i τ _ c (Fin.rev c) hq (by rw [Fin.val_rev]; omega)
    have e := kaWt_small D hK (even_nV Tp) _ h1 h2 τ c
    rw [← hp, ← neg_neg (DV.aMinusQ _ _ _ _), ← h, ← Int.cast_neg, ← e] at h'
    rw [hM τ c, hs τ]
    exact_mod_cast h'
  have en : w.n = (kaR Tp hK ((i : ℕ) + 1)).n := hn.trans (kaWt_n _ _ _ _).symm
  generalize kaR Tp hK ((i : ℕ) + 1) = u at eP eM en
  cases w; cases u
  simp only at eP eM en
  subst eP eM en
  rfl

theorem exists_isRec : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (J : CoreJ D) [Algebra J.Q.c.F D.what₂.LL] (R : RealDat D A J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie J R κ v₀) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (EX : ErrX D) (r : TwoRuns J G) (c : OnConst), J.Q.Canon → HalfEX J.toCore EX → RunsOk fw r → ∃ O : OnObj ((R.toCx F).data F.cr false) (Mir R) c, IsRec Tp hK EX F fw r O := by
  intro D G _ _ Pl0 T0 A J inst R F κ v₀ fw L Pm Tp hK EX r c _ hE ok
  obtain ⟨v₁, -⟩ := exists_place3 D.what₂.LL
  have hc : LawsCore J.toCore := (ok.laws v₁).p.toLawsCore
  have hinj : Function.Injective D.what₂.OtoLL := fun x y hxy => by
    obtain ⟨x, rfl⟩ := J.Q.eO.surjective x
    obtain ⟨y, rfl⟩ := J.Q.eO.surjective y
    rw [← fw.alg_eq, ← fw.alg_eq] at hxy
    exact congrArg _ (RingOfIntegers.ext ((algebraMap J.Q.c.F D.what₂.LL).injective hxy))
  have hκ : ∀ i : Fin D.R.m, κ i = kaR Tp hK ((i : ℕ) + 1) := fun i =>
    eq_kaR Tp hK i (κ i) (fun τ => (fw.kap i τ).1) (fun τ => (fw.kap i τ).2.1)
      (fw.kap i (plOf D (false, Classical.arbitrary _))).2.2
  choose ρ hρ using fun i : Fin D.R.m =>
    ActionPin.exists_rep (T := (r.used v₁).full) (inst := inst) (R := R) (ok.action v₁ i) (mirIncl R)
  obtain ⟨O, z, act, y, ht⟩ := exists_tiedObj (F := F) (fw := fw) (hc := hc) (run := r.used) (h := fun v => (ok.laws v).p)
    (hinj := hinj) (EX := EX) (p := ownAt D) (wL := fun _ i => lR Tp hK ((i : ℕ) + 1))
    (wF := fun _ i => fR Tp hK ((i : ℕ) + 1)) (nT := Tp.TO) (ℓ := r.lev) (ph := fun _ => 1) (c := c) (mirIncl R)
    (blankObj D _ (Mir R) c fun i => R.nW i) ok.action ρ (fun _ i => hρ i)
  letI st : StarRing (𝓞 D.host.E) := J.Q.H.starRing
  letI := hostAlg D
  letI : ∀ s : GlobalTheory.RealIndexBound.RunData J, Algebra s.full.J.Q.c.F D.what₂.LL := fun _ => inst
  have hφ : ∀ x : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.what₂.LL x =
      algebraMap J.Q.c.F D.what₂.LL ((iE D hinj (recB hc) x : 𝓞 J.Q.c.F) : J.Q.c.F) := fun x => by
    refine Eq.trans ?_ (fw.alg_eq _).symm
    refine (oEOsFun_spec D x).symm.trans (congrArg D.what₂.OtoLL ?_)
    exact (J.Q.eO.apply_symm_apply _).symm
  have hσ : ∀ v (i : Fin D.R.m), O.σ v i =
      sigAt (Dw := J.Q.Dw ((i : ℕ) + 1)) (H := J.Q.H) (LL := D.what₂.LL) (depOf J.toCore EX Tp hK) ((i : ℕ) + 1) := fun v i => by
    letI : Algebra (recB (ok.laws v).p.toLawsCore).KO D.what₂.LL := inst
    refine (ht v i).1.toFormTieK.σ_eq.trans ?_
    rw [hκ i]
    exact (GlobalTheory.ScalarOfRun.sigAt_eq_sigRec D L Pm Tp hK (r.used v).full.toTop (ok.laws v).p hinj EX _ (inR_succ i) hE
      D.what₂.LL (algebraMap J.Q.c.F D.what₂.LL) hφ).symm
  refine ⟨{ O with
    E := fun v (j : Fin D.R.m) =>
      EAt (Xo := J.Q.Xo ((j : ℕ) + 1)) (c := J.Q.c) (LL := D.what₂.LL) (depOf J.toCore EX Tp hK) v ((j : ℕ) + 1)
    nnK := fun j : Fin D.R.m => nnKAt (H := J.Q.H) (LL := D.what₂.LL) (depOf J.toCore EX Tp hK) ((j : ℕ) + 1)
    T := (Tp.TO : ℝ)
    g1 := D.host.g 0
    g2 := D.host.g 1
    q1 := D.host.q
    dd := D.host.d
    sm := D.host.small
    k := (D.R.k : ℝ)
    m := (D.R.m : ℝ)
    f := (D.R.f : ℝ)
    x := L.sc.x
    eps := L.sc.eps
    Sc := L.Sc
    eta := L.etaSz
    bp := L.sc.b'
    X2 := L.sc.X'' D.R.n
    vd := vd2 D
    wt := fun _ => 2 * (D.R.f : ℝ) * L.sc.b
    th := fun l => Formalism.UnitaryBoundIntegral.thl D.R.k l
    ad := fun _ => 0
    DF := ((Finset.univ.sup fun j : Fin D.R.m => WeightAlgebra.DF (lR Tp hK ((j : ℕ) + 1)) : ℕ) : ℝ)
    rr := (D.R.r : ℝ)
    Nc := L.Nc
    T2 := D.host.T2.card
    pde := D.host.pde }, ok, hκ, ⟨hc, hinj, z, act, y, fun v i => ⟨{ (ht v i).1 with }, (ht v i).2⟩⟩, ⟨st, ?_⟩,
    rfl, rfl, rfl, rfl, rfl⟩
  refine ⟨fun j => inR_succ j, fun _ => rfl, fun a => ?_, fun _ _ => rfl, hσ, fun _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun j => ?_⟩
  · show star (D.embE (a : D.host.E)) = D.embE ((J.toCore.Q.H.bar a : 𝓞 D.host.E) : D.host.E)
    rw [bar_core, barE_eq_conj, D.embE_conj]
  · exact Nat.cast_le.2 (Finset.le_sup (f := fun j : Fin D.R.m => WeightAlgebra.DF (lR Tp hK ((j : ℕ) + 1))) (Finset.mem_univ j))

end GlobalTheory.BigOn

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetsUnitVacuumEqUnitMulPeriodJets
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetsUnitVacuumEqUnitMulPeriodJets
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FockPos

theorem fock_jets_eq_unit_mul_period_jets : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1 → (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∀ (δ t0 : ℂ), Formalism.MainNotions.StandardLatticesGL3.Crv D D.host.ccK δ → δ ≠ 0 → Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (Formalism.MainNotions.TaylorLogMetric.lamOf D D.host.ccK δ) t0 → ∀ e0 : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ, Formalism.MainNotions.StandardLatticesGL3.oddE0 D D.host.ccK δ t0 _ _ e0 → ∀ f, IsVacO ψ θ S T sS sT (colLat frS : Set _) (colLat frT : Set _) f → ∃ c : ℂˣ, ∀ k : FVar D T.rank S.rank →₀ ℕ, pureTensorO ψ θ S T sS sT (fun τ => frS.1.map (tauE D τ)) (fun τ => frT.1.map (tauE D τ)) f (MvPolynomial.monomial k 1) 0 = c * ((k.prod fun v n => GlobalTheory.FunObj.period δ v.1 ^ n) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) e0) := by
  intro D ψ θ S T sS sT frS frT hS hT hcS hcT δ t0 hC hδ ht0 e0 he0 f hf
  obtain ⟨Θ, hΘ, hΘ0, hjet⟩ := GlobalTheory.T.fockJets_unitVacuum_eq_scaled_thetaJets ψ θ S T sS sT frS frT hS hT hcS hcT δ hC hδ f hf
  have hG := (GlobalTheory.InducedType.induced_type D).1
  have he0ne : e0 ≠ 0 := by
    intro h
    have hn := he0.2.2.1
    rw [h] at hn
    have h0 : Formalism.MainNotions.TaylorLogMetric.normSq D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (Formalism.MainNotions.StandardLatticesGL3.La0 D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) S.rank T.rank) 0 = 0 := by
      simp [Formalism.MainNotions.TaylorLogMetric.normSq]
    rw [h0] at hn
    exact pow_ne_zero _ (GlobalTheory.ConjJet.thetaZeroNormSq_ne_zero_cmLattice D hG D.host.ccK δ t0 hC ht0) hn.symm
  have hK : Formalism.MainNotions.StandardLatticesGL3.KLat D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (Formalism.MainNotions.TaylorLogMetric.La D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (Formalism.MainNotions.StandardLatticesGL3.stdL D S.rank) (Formalism.MainNotions.StandardLatticesGL3.stdL D T.rank)) :=
    Or.inr ⟨_, _, GlobalTheory.NormSum.VacInt.sd_std D S.rank, GlobalTheory.NormSum.VacInt.sd_std D T.rank, rfl⟩
  obtain ⟨c, hc⟩ := (GlobalTheory.ThetaLine.theta_line D hG D.host.ccK δ hC S.rank T.rank _ hK).1 Θ hΘ e0 he0.1 he0ne
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hΘ0 (by rw [hc, zero_smul])
  refine ⟨Units.mk0 c hc0, fun k => ?_⟩
  rw [hjet k, Units.val_mk0]
  rw [hc, (GlobalTheory.NormSum.applyAt0_minorPol_linear D S.rank T.rank (fun _ => 0) e0 he0.1.1).2.2.1 c]
  ring

end GlobalTheory.FockPos
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetsUnitVacuumEqUnitMulPeriodJetsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockJets_unitVacuum_eq_unit_mul_periodJets : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1 → (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∀ (δ t0 : ℂ), Formalism.MainNotions.StandardLatticesGL3.Crv D D.host.ccK δ → δ ≠ 0 → Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (Formalism.MainNotions.TaylorLogMetric.lamOf D D.host.ccK δ) t0 → ∀ e0 : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ, Formalism.MainNotions.StandardLatticesGL3.oddE0 D D.host.ccK δ t0 _ _ e0 → ∀ f, IsVacO ψ θ S T sS sT (colLat frS : Set _) (colLat frT : Set _) f → ∃ c : ℂˣ, ∀ k : FVar D T.rank S.rank →₀ ℕ, pureTensorO ψ θ S T sS sT (fun τ => frS.1.map (tauE D τ)) (fun τ => frT.1.map (tauE D τ)) f (MvPolynomial.monomial k 1) 0 = c * ((k.prod fun v n => GlobalTheory.FunObj.period δ v.1 ^ n) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) e0) := by
  first | exact @GlobalTheory.FockPos.fock_jets_eq_unit_mul_period_jets | exact GlobalTheory.FockPos.fock_jets_eq_unit_mul_period_jets | (intros; apply GlobalTheory.FockPos.fock_jets_eq_unit_mul_period_jets <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkMapInjective
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

namespace GlobalTheory.HSApp.ValCrit

open IsLocalRing

theorem exists_valuation (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R] :
    ∃ μ : Valuation R (WithZero (Multiplicative ℤ)),
      (∀ a, μ a ≤ 1) ∧ (∀ a ∈ maximalIdeal R, μ a < 1) ∧ ∀ a, μ a = 0 → a = 0 := by
  classical
  by_cases hf : IsField R
  · refine ⟨1, fun a => ?_, fun a ha => ?_, fun a ha => ?_⟩
    · by_cases h : a = 0
      · simp [h]
      · rw [Valuation.one_apply_of_ne_zero h]
    · have : a = 0 := by
        rw [isField_iff_maximalIdeal_eq.1 hf] at ha
        exact ha
      simp [this]
    · by_contra h
      rw [Valuation.one_apply_of_ne_zero h] at ha
      exact one_ne_zero ha
  · obtain ⟨V, hV, hd⟩ := exists_discreteValuationSubring_dominating R (FractionRing R) (FractionRing R) hf
    obtain ⟨h1, h2⟩ := (localSubring_range_le_valuationSubring_iff_isLocalHom _ _).1 hd
    let ρ : R →+* V := (algebraMap R (FractionRing R)).codRestrict V h1
    have hρ : Function.Injective ρ := fun a b hab =>
      IsFractionRing.injective R (FractionRing R) (congrArg Subtype.val hab)
    let v : IsDedekindDomain.HeightOneSpectrum V :=
      ⟨maximalIdeal V, inferInstance, IsDiscreteValuationRing.not_a_field V⟩
    refine ⟨v.intValuation.comap ρ, fun a => v.intValuation_le_one _, fun a ha => ?_, fun a ha => ?_⟩
    · refine (v.intValuation_lt_one_iff_mem _).2 ?_
      exact (mem_maximalIdeal _).2 fun hu => (mem_maximalIdeal _).1 ha (isUnit_of_map_unit ρ a hu)
    · by_contra h
      exact v.intValuation_ne_zero _ (fun e => h (hρ (e.trans (map_zero ρ).symm))) ha

variable {k : Type} [Field k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {U : Y.Opens} {D : ℕ}

theorem isIntegral_X [IsIntegral Y] (M : Modif p U D) [Nonempty M.X] : IsIntegral M.X := by
  haveI : Smooth M.str := SmoothOfRelativeDimension.smooth D M.str
  haveI : IsReduced M.X := isReduced_of_smooth M.str
  obtain ⟨x, hx⟩ := M.dense.nonempty
  haveI : Nonempty (M.σ ⁻¹ᵁ U) := ⟨⟨x, hx⟩⟩
  haveI : Nonempty U := ⟨⟨M.σ x, hx⟩⟩
  haveI := M.iso
  haveI : IsIntegral (M.σ ⁻¹ᵁ U : Scheme) := isIntegral_of_isOpenImmersion (M.σ ∣_ U)
  have h1 : IsIrreducible ((M.σ ⁻¹ᵁ U : M.X.Opens) : Set M.X) := by
    have := (IrreducibleSpace.isIrreducible_univ (M.σ ⁻¹ᵁ U : Scheme)).image (⇑(M.σ ⁻¹ᵁ U).ι)
      (M.σ ⁻¹ᵁ U).ι.continuous.continuousOn
    rwa [Set.image_univ, Scheme.Opens.range_ι] at this
  have h2 := h1.closure
  rw [M.dense.closure_eq] at h2
  haveI : IrreducibleSpace M.X := (irreducibleSpace_def _).2 h2
  exact isIntegral_of_irreducibleSpace_of_isReduced M.X

end GlobalTheory.HSApp.ValCrit

namespace GlobalTheory.HSApp

end GlobalTheory.HSApp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseTupleThetaKernelTameCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseTupleThetaKernelTameCharacter
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OnBaseKer


open Classical in
theorem kerDat_of_isBaseKernel : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → ∀ ω φ, IsBaseKernel R i v (ownAt D v) ω φ → ∃ χ ξR, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i v hv hmu ω φ hK
  obtain ⟨χ, ξR, hchr, hres, hweil, hvec⟩ := hK
  have hD := GlobalTheory.BigOn.isDelta_delAt_ownAt R.C v
  obtain ⟨ψ, Qw, hψ, hxi⟩ := hmu v hv
  have hL := hC.lev
  have hmem : ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (n : ℕ), ((n : 𝓞 D.host.E) ∈ P.asIdeal ↔ Formalism.EigenvalueLevelCeiling.plc P ∣ n) :=
    fun P n => by
      unfold Formalism.EigenvalueLevelCeiling.plc
      rw [← ringChar.spec, ← map_natCast (Ideal.Quotient.mk P.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
  have hstar : ∀ (n : ℕ) (c : 𝓞 D.host.E), (c : D.host.E) = star ((n : 𝓞 D.host.E) : D.host.E) → c = n := by
    intro n c h
    apply RingOfIntegers.coe_injective
    refine h.trans ?_
    simp
  refine ⟨χ, ξR, ⟨hchr, hD.fin, hD.triv, hD.tame, ?_, ?_, ?_, hres, hweil, hvec⟩⟩
  · intro PP hP
    have hP' := (Finset.mem_filter.1 hP).1
    exact ⟨(hL.Q_pl _ PP hP').1, fun PP' hP'' => (hL.Q_pl _ PP hP').2 PP' (Finset.mem_filter.1 hP'').1⟩
  · intro PP hP
    exact (hL.Q_off _ PP (Finset.mem_filter.1 hP).1).1
  · intro PP
    constructor
    · intro hnu
      have hover : ((ownAt D v : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
        by_contra h
        exact hnu (hD.unr PP h)
      have hram : ¬ (R.xiH (R.mu v)).UnrAt PP := by
        rw [hxi]
        intro hu
        obtain ⟨a, ha⟩ := hψ.ord
        have h15 : 15 ∣ Formalism.EigenvalueLevelCeiling.plc v ^ a := by
          refine (hD.ine PP hover _).1 fun x hx => ?_
          have h1 := hu x hx
          have loc_mul (a b : Formalism.L2.Host.HChar D.host.E) :
              (a * b).loc PP x = a.loc PP x * b.loc PP x := rfl
          rw [loc_mul] at h1
          have h2 : ψ.loc PP x ^ (Formalism.EigenvalueLevelCeiling.plc v ^ a) = 1 := by
            have h3 := congrArg (fun χ' : Formalism.L2.Host.HChar D.host.E => χ'.loc PP x) ha
            exact h3
          rw [eq_inv_of_mul_eq_one_left h1, inv_pow, h2, inv_one]
        have hl := Formalism.EigenvalueLevelCeiling.plc_prime v
        have h3 : 3 = Formalism.EigenvalueLevelCeiling.plc v := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hl).1
          (Nat.prime_three.dvd_of_dvd_pow (dvd_trans (by norm_num) h15))
        have h5 : 5 = Formalism.EigenvalueLevelCeiling.plc v := (Nat.prime_dvd_prime_iff_eq Nat.prime_five hl).1
          (Nat.prime_five.dvd_of_dvd_pow (dvd_trans (by norm_num) h15))
        omega
      rcases (hL.Q_ram _ PP).1 hram with h | ⟨PP', h, hc⟩
      · exact Or.inl (Finset.mem_filter.2 ⟨h, hover⟩)
      · refine Or.inr ⟨PP', Finset.mem_filter.2 ⟨h, ?_⟩, hc⟩
        obtain ⟨c', hc', he⟩ := hc _ ((hmem PP' _).2 dvd_rfl)
        rw [hstar _ _ he, hmem] at hc'
        have heq := (Nat.prime_dvd_prime_iff_eq (Formalism.EigenvalueLevelCeiling.plc_prime PP) (Formalism.EigenvalueLevelCeiling.plc_prime PP')).1 hc'
        rw [hmem] at hover ⊢
        exact heq ▸ hover
    · intro h hu
      have hover : ((ownAt D v : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
        rcases h with h | ⟨PP', h, hc⟩
        · exact (Finset.mem_filter.1 h).2
        · obtain ⟨c', hc', he⟩ := hc _ (Finset.mem_filter.1 h).2
          rwa [hstar _ _ he] at hc'
      have h1 := (hD.ine PP hover 1).1 fun x hx => by rw [pow_one]; exact hu x hx
      norm_num at h1

end GlobalTheory.OnBaseKer

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseTupleThetaKernelTameCharacterStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseTuple_thetaKernel_tameCharacter : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → ∀ ω φ, IsBaseKernel R i v (ownAt D v) ω φ → ∃ χ ξR, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ := by
  first | exact @GlobalTheory.OnBaseKer.kerDat_of_isBaseKernel | exact GlobalTheory.OnBaseKer.kerDat_of_isBaseKernel | (intros; apply GlobalTheory.OnBaseKer.kerDat_of_isBaseKernel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelesCompactOfLocalBounds
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.ConeEuler
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)

namespace GlobalTheory.IdeleCyl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem evInf_eInf (w : InfinitePlace F) : evInf F w (eInf F) = 1 := by
  show GlobalTheory.AutFunCompare.evW w ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ 1)) = 1
  rw [map_one, map_one, map_one]

theorem compInf_unitArch (w : InfinitePlace F) (l : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))ˣ) :
    compInf F E w (unitArch F E l : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) = compInf F E w l := by
  change compInf F E w (eInf F • (l : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) + (1 - eInf F) • 1) = _
  rw [map_add (f := _), compInf_smul, compInf_smul, evInf_eInf, map_sub, map_one, evInf_eInf, sub_self, zero_smul, one_smul,
    add_zero]

end GlobalTheory.IdeleCyl

namespace GlobalTheory.IdeleCyl

theorem isCompact_restrictedProduct_forall_mem {ι : Type} (R : ι → Type) [∀ i, TopologicalSpace (R i)]
    (A : ∀ i, Set (R i)) (C : ∀ i, Set (R i)) (hC : ∀ i, IsCompact (C i)) (hCA : ∀ᶠ i in Filter.cofinite, C i ⊆ A i) :
    IsCompact {x : RestrictedProduct R A Filter.cofinite | ∀ i, x i ∈ C i} := by
  let S : Set ι := {i | C i ⊆ A i}
  have hS : (Filter.cofinite : Filter ι) ≤ Filter.principal S := Filter.le_principal_iff.2 hCA
  have h1 : IsCompact (((↑) : RestrictedProduct R A (Filter.principal S) → ∀ i, R i) ⁻¹' Set.univ.pi C) := by
    refine RestrictedProduct.isEmbedding_coe_of_principal.isCompact_preimage_iff ?_ |>.mpr (isCompact_univ_pi hC)
    rintro f hf
    refine ⟨⟨f, Filter.eventually_principal.2 fun i hi => hi (hf i trivial)⟩, rfl⟩
  convert h1.image (RestrictedProduct.continuous_inclusion hS) using 1
  ext x
  constructor
  · intro hx
    exact ⟨⟨x, Filter.eventually_principal.2 fun i hi => hi (hx i)⟩, fun i _ => hx i, rfl⟩
  · rintro ⟨y, hy, rfl⟩ i
    exact hy i trivial

theorem repr_tmul_basis {n : ℕ} {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (b : Module.Basis (Fin n) F E) (a : R) (x : E) (j : Fin n) :
    (Algebra.TensorProduct.basis R b).repr (a ⊗ₜ[F] x) j = a * algebraMap F R (b.repr x j) := by
  simp [Algebra.TensorProduct.basis_repr_tmul, Algebra.smul_def, mul_comm]

theorem eventually_repr_mem_of_mem_intLoc (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [Module.Finite F E] (j : Fin (Module.finrank F E)) : ∀ᶠ v in Filter.cofinite, ∀ y ∈ intLoc F E v,
      (Algebra.TensorProduct.basis (Fv F v) (Module.finBasis F E)).repr y j ∈ (v.adicCompletionIntegers F : Set (Fv F v)) := by
  classical
  let b := Module.finBasis F E
  let β := RingOfIntegers.basis E
  have hfin : ∀ᶠ v in Filter.cofinite, ∀ k, algebraMap F (Fv F v) (b.repr (β k : E) j) ∈ (v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F :=
    Filter.eventually_all.2 fun k => (algebraMap F (FiniteAdeleRing (𝓞 F) F) (b.repr (β k : E) j)).2
  refine hfin.mono fun v hv y hy => ?_
  have hx : ∀ x : 𝓞 E, algebraMap F (Fv F v) (b.repr (x : E) j) ∈ v.adicCompletionIntegers F := by
    intro x
    have e : (x : E) = ∑ k, (β.repr x k : ℤ) • (β k : E) := by
      conv_lhs => rw [← β.sum_repr x]
      simp
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply, map_sum]
    refine Subring.sum_mem (v.adicCompletionIntegers F).toSubring fun k _ => ?_
    rw [map_zsmul, Finsupp.smul_apply, map_zsmul]
    exact Subring.zsmul_mem (v.adicCompletionIntegers F).toSubring (hv k) _
  refine intLoc_induction (p := fun y => (Algebra.TensorProduct.basis (Fv F v) b).repr y j ∈ (v.adicCompletionIntegers F : Set (Fv F v)))
    (fun a ha x => ?_) (by simp) (fun y z hy hz => ?_) (fun y hy => ?_) hy
  · rw [repr_tmul_basis]
    exact mul_mem ha (hx x)
  · rw [map_add (f := _), Finsupp.add_apply]; exact add_mem hy hz
  · rw [map_neg, Finsupp.neg_apply]; exact neg_mem hy

end GlobalTheory.IdeleCyl

namespace GlobalTheory.IdeleCyl

theorem repr_map_tens {n : ℕ} {F E R R' : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R] [CommRing R']
    [Algebra F R'] (b : Module.Basis (Fin n) F E) (φ : R →ₐ[F] R') (z : R ⊗[F] E) (j : Fin n) :
    (Algebra.TensorProduct.basis R' b).repr (Algebra.TensorProduct.map φ (AlgHom.id F E) z) j =
      φ ((Algebra.TensorProduct.basis R b).repr z j) := by
  induction z using TensorProduct.inductionOn with
  | tmul a x => simp [Algebra.TensorProduct.basis_repr_tmul]
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]

end GlobalTheory.IdeleCyl


open GlobalTheory.IdeleCyl in
theorem GlobalTheory.IdeleCyl.exists_isCompact_box : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (M : ∀ w : InfinitePlace F, Set (w.Completion ⊗[F] E)) (L : ∀ v : Pl (F := F), Set (Fv F v ⊗[F] E)),
    (∀ w, IsCompact (M w)) → (∀ v, IsCompact (L v)) → (∀ᶠ v in Filter.cofinite, L v ⊆ (intLoc F E v : Set (Fv F v ⊗[F] E))) →
    ∃ K : Set (AE F E), IsCompact K ∧ ∀ z : AE F E, (∀ w, compInf F E w z ∈ M w) → (∀ v, compFin F E v z ∈ L v) → z ∈ K := by
  intro F E _ _ _ _ _ M L hM hL hLc
  classical
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  let b := Module.finBasis F E
  let e := (Algebra.TensorProduct.basis (AF F) b).equivFun
  have he : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let Mc : Fin (Module.finrank F E) → ∀ w : InfinitePlace F, Set w.Completion := fun j w =>
    (fun y => (Algebra.TensorProduct.basis w.Completion b).repr y j) '' M w
  let Lc : Fin (Module.finrank F E) → ∀ v : Pl (F := F), Set (Fv F v) := fun j v =>
    (fun y => (Algebra.TensorProduct.basis (Fv F v) b).repr y j) '' L v
  have hMc : ∀ j w, IsCompact (Mc j w) := fun j w => by
    haveI : IsModuleTopology w.Completion (w.Completion ⊗[F] E) := ⟨rfl⟩
    exact (hM w).image (IsModuleTopology.continuous_of_linearMap ((Algebra.TensorProduct.basis w.Completion b).coord j))
  have hLc' : ∀ j v, IsCompact (Lc j v) := fun j v => by
    haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
    exact (hL v).image (IsModuleTopology.continuous_of_linearMap ((Algebra.TensorProduct.basis (Fv F v) b).coord j))
  let Q : Fin (Module.finrank F E) → Set (AF F) := fun j =>
    (Set.univ.pi (Mc j)) ×ˢ {y : FiniteAdeleRing (𝓞 F) F | ∀ v, y v ∈ Lc j v}
  have hQ : ∀ j, IsCompact (Q j) := fun j => by
    refine (isCompact_univ_pi (hMc j)).prod ?_
    have := isCompact_restrictedProduct_forall_mem (fun v : Pl F => v.adicCompletion F) (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
      (Lc j) (hLc' j) ((hLc.and (eventually_repr_mem_of_mem_intLoc F E j)).mono fun v ⟨h1, h2⟩ => by
        rintro _ ⟨y, hy, rfl⟩
        exact h2 y (h1 hy))
    exact this
  refine ⟨e.symm '' Set.univ.pi Q, (isCompact_univ_pi hQ).image he, fun z hz1 hz2 => ⟨e z, fun j _ => ⟨fun w _ => ?_, fun v => ?_⟩, e.symm_apply_apply z⟩⟩
  · refine ⟨compInf F E w z, hz1 w, ?_⟩
    exact repr_map_tens b (evInf F w) z j
  · refine ⟨compFin F E v z, hz2 v, ?_⟩
    exact repr_map_tens b (evFin F v) z j

namespace GlobalTheory.IdeleCyl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

end GlobalTheory.IdeleCyl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenSchwartzSurjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenSchwartzSurjective
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

noncomputable section
namespace GlobalTheory.ThetaChange

theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ M₁ : Model σ X W, M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, IsEv B M M₁ 1 1 ∅ e → Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) → ∃ c₀ : ℂ, c₀ ≠ 0 ∧ ∀ Φ ∈ schA F (Fin n × Fin d), thetaSum F (e Φ) = c₀ * thetaSum F Φ := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP M₁ hM₁ e hE hbij
  have hstd : IsStd B.ψ := hP.base.std
  have hrk : Module.finrank F E = 2 := hP.base.cm.2.2.1
  obtain ⟨Φr, hΦr⟩ := GlobalTheory.RatCoord.ratEquiv F E σ n d X W M B.ψ hP.good hrk
  obtain ⟨lθ, hlθ, hlθ'⟩ := GlobalTheory.ThetaAdmitted.exists_admitted_form_eq_adelicThetaDistribution_alt F (Fin n × Fin d)
  have hcomp := GlobalTheory.EvAdm.comp_mem_adm F E σ B n d n d X W X W M M₁ 1 1 ∅ e hP.good hM₁ hE lθ hlθ
  have hinc1 : ∀ k : ℕ, incM F (1 : Matrix (Fin k) (Fin k) E) = 1 := by
    intro k; unfold incM; exact Matrix.map_one _ (map_zero _) (map_one _)
  obtain ⟨c, hc⟩ := GlobalTheory.T.schwartz_functional_archimedean_factor F B.ψ hstd (Fin n × Fin d) (fun Φ => thetaSum F (e Φ))
    (fun Φ hΦ Ψ hΨ => by
      simp only [map_add (f := _)]
      exact GlobalTheory.WeilM.thetaSum_add F (hE.maps Φ hΦ) (hE.maps Ψ hΨ))
    (fun c Φ _ => by simp only [map_smul]; exact GlobalTheory.WeilM.thetaSum_smul F c (e Φ))
    (fun g hg => by
      obtain ⟨T, hT⟩ := hcomp g hg
      refine ⟨T, fun f => ?_⟩
      have hm : pureA F f g ∈ schA F (Fin n × Fin d) := Submodule.subset_span ⟨f, g, hg, rfl⟩
      rw [← hlθ' _ (hE.maps _ hm)]
      exact hT f)
    (fun a b Φ hΦ => by
      set x := Φr.symm (a, b) with hx
      have hxe : M.co.e (incM F x) = ((fun i => algebraMap F (AF F) (a i)), (fun i => algebraMap F (AF F) (b i))) := by
        rw [hΦr x, hx, LinearEquiv.apply_symm_apply]
      have h1 : schr B.ψ ((fun i => algebraMap F (AF F) (a i)), (fun i => algebraMap F (AF F) (b i))) Φ =
          M.co.rho B.ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * incM F x * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ) Φ := by
        rw [hinc1, hinc1, Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one]
        show _ = schr B.ψ (M.co.e (incM F x)) Φ
        rw [hxe]
      rw [h1, hE.Heisenberg₂ _ Φ hΦ]
      obtain ⟨y, z, hyz⟩ := hM₁.rat x
      show thetaSum F (schr B.ψ (M₁.co.e (incM F x)) (e Φ)) = _
      rw [hyz]
      exact GlobalTheory.ThetaQuasiRat.thetaSum_schr_rat F B.ψ (fun a => hstd.2.1 a) y z (e Φ))
  refine ⟨c, ?_, hc⟩
  rintro rfl
  obtain ⟨φ₀, hφ₀, hne⟩ := GlobalTheory.ThetaSumNe.exists_mem_schA_thetaSum_ne_zero F (Fin n × Fin d)
  obtain ⟨Φ, hΦ, rfl⟩ := hbij.surjOn hφ₀
  exact hne (by rw [hc Φ hΦ, zero_mul])

end GlobalTheory.ThetaChange
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenSchwartzSurjectiveStatement
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_eigen_schwartz_surjective : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ M₁ : Model σ X W, M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, IsEv B M M₁ 1 1 ∅ e → Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) → ∃ c₀ : ℂ, c₀ ≠ 0 ∧ ∀ Φ ∈ schA F (Fin n × Fin d), thetaSum F (e Φ) = c₀ * thetaSum F Φ := by
  first | exact @GlobalTheory.ThetaChange.main | exact GlobalTheory.ThetaChange.main | (intros; apply GlobalTheory.ThetaChange.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodLiftOntoOfBase
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.FormTies GlobalTheory.BigOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TraceIncl

namespace GlobalTheory.BaseTwistIncl

section Rank

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

theorem ws_le_base (hX : ∀ χ ∈ A.X, IsAbsIrrChar χ) (h5 : (R.toCx F).H5 F.cr false) (i : Fin D.R.m) (t : T0)
    (N : Submodule ℂ (R.HW i (sg0 D A)).H) (hN : ∀ x, R.thG i t (jVx R i t (OnTies.srcForm A i t F.P0 F.ψ0⁻¹ x)) ∈ N) :
    R.WS F false i (sg0 D A) ≤ N := by
  intro w h1
  obtain ⟨c, hc⟩ := exists_w0C_eq R F i h1
  have h0 : ∀ y, (R.toCx F).θ' i t ((R.toCx F).jL i t (F.cr.toL (R.toCx F).zs false i t y)) ∈
      Tw.sub (twAt D.what₂.embLL A.v0) N := by
    intro y
    obtain ⟨x, hx⟩ := exists_srcForm_eq F hX i t ((R.toCx F).zs.Zl i t) y
    have k5 : ∀ u u' : A.fam.amb.FL i t, u = u' → R.thG i t (jVx R i t u) ∈ N → R.thG i t (jVx R i t u') ∈ N :=
      fun u u' h hu => h ▸ hu
    have k4 := k5 _ _ hx (hN x)
    have k3 := out_lift_toL R F i t y
    exact (congrArg (fun u : (R.HW i (sg0 D A)).H => u ∈ N) k3).mpr k4
  have h2 := goodFormsCoordinateMap_mem_of_lifts_mem (R.toCx F) F.cr false h5 i t _ h0 c
  exact (congrArg (· ∈ N) hc).mp h2

theorem goodLiftOnto_of_base (hX : ∀ χ ∈ A.X, IsAbsIrrChar χ) (hW : R.models_HW) (hG : R.thP_thG) (hU : R.LUnif)
    (h5 : (R.toCx F).H5 F.cr false) (i : Fin D.R.m) (t : T0) (ph : ℂ) (hph : ph ≠ 0) :
    GoodLiftOnto R i t F.P0 F.ψ0⁻¹ ph := by
  intro θ hθ z hz
  refine mem_of_mem_span_image ((R.FW i).j (sg0 D A)) (hU i _).1 _ ?_
  have h1 : (R.FW i).j (sg0 D A) z ∈
      Submodule.span ℂ (Set.range fun x => R.thG i t (jVx R i t (OnTies.srcForm A i t F.P0 F.ψ0⁻¹ x))) := by
    refine ws_le_base R F hX h5 i t _ (fun x => Submodule.subset_span (Set.mem_range_self x)) ?_
    rw [GlobalTheory.LevelForms.ws_eq_span]
    exact Submodule.subset_span ⟨z, hz, rfl⟩
  refine Submodule.span_le.2 ?_ h1
  rintro _ ⟨x, rfl⟩
  refine (Submodule.smul_mem_iff _ hph).1 ?_
  exact Submodule.subset_span ⟨_, ⟨x, rfl⟩, j_eOp_of_adForm R hW hG hU i t ph _ _ (hθ x)⟩

end Rank

attribute [local instance] GlobalTheory.BigOn.runAlg'

theorem leafTW2_of_isRec : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (J : CoreJ D) [Algebra J.Q.c.F D.what₂.LL] (R : RealDat D A J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie J R κ v₀) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (EX : ErrX D) (r : TwoRuns J G) (c : OnConst) (O : OnObj ((R.toCx F).data F.cr false) (Mir R) c), IsRec Tp hK EX F fw r O → ∀ s : ℕ, A.fam.Ok s → R.Char F → R.LUnif → BaseLinks R F → TwistedRational R F (fun _ => 1) → LeafTW2 O := by
  intro D G _ _ Pl0 T0 A J inst R F κ v₀ fw L Pm Tp hK EX r c O hrec s hOk hC hU hB hrat
  obtain ⟨hc, hinj, z, act, y, ht⟩ := hrec.tied
  have hinc : F.P0 ≤ (mirIncl R).range := fun g hg => by
    obtain ⟨u, -, e⟩ := (mem_base_iff hC.grp.levels g).1 hg
    exact ⟨u, e⟩
  have main : ∀ v, (∀ j, ClassSumRational R j (R.mu v) F.P0 F.ψ0⁻¹ 1) →
      ∀ j, IsLatIn (O.Zg j) (O.X₃ v j) ∧ IsLatIn (O.Zg j) (O.Im v j) ∧
        Formalism.HermitianLatticesTheory.localization₂ v.asIdeal (O.X₃ v j) ≤ Formalism.HermitianLatticesTheory.localization₂ v.asIdeal (O.Im v j) := by
    intro v h3 j
    have := lattices_of_tie (T := (r.used v).full) (inst := inst) (R := R)
      (ht v j).1 (ht v j).2 hinc (chi_eq_one_of_mem_base R F hC.grp j)
      ⟨hC.lev, hC.grp.red_L, hC.fam.tie, hC.models, hC.thP, hU, ⟨_, (fw.hv₀ j _).1⟩, (hOk.lifts _ _).act,
        GlobalTheory.T.weilAction_liftPair_stepVector_invLevelChar R hC.lev hC.models.inf hC.thP.ωP hC.thP.vP j (R.mu v)⟩
      (hOk.lifts _ _).good hOk.irr (h3 j)
      (goodLiftOnto_of_base R F hOk.irr hC.models.HW hC.thP.thG hU hB.1 _ _ _ one_ne_zero)
    exact ⟨this.1, this.2.1, Formalism.L2.DIV.localization_mono _ this.2.2⟩
  intro w hw
  exact ⟨main w (hrat w hw), main _ (by rw [hC.tup.mu_conj w]; exact hrat w hw)⟩

end GlobalTheory.BaseTwistIncl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomRankSumLeTwoMulTotalRank
open Formalism.BasicNotions Formalism.MainNotions Formalism.IndefR Formalism.IndefR.Links IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.SqTop GlobalTheory.NormSum
open Formalism.L2.Host (HChar)

noncomputable section

namespace GlobalTheory.SqTop.BotSmallProof

theorem eq_of_dvd_absNorm {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) {ℓ p : ℕ}
    (hℓ : ℓ.Prime) (hp : p.Prime) (hv : ((ℓ : ℕ) : 𝓞 K) ∈ v.asIdeal) (h : p ∣ Ideal.absNorm v.asIdeal) : p = ℓ := by
  have hmax : (Ideal.span {((ℓ : ℕ) : ℤ)} : Ideal ℤ).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hℓ).irreducible
  haveI hl : v.asIdeal.LiesOver (Ideal.span {((ℓ : ℕ) : ℤ)}) := by
    refine ⟨hmax.eq_of_le ?_ ?_⟩
    · exact (v.isPrime.comap (algebraMap ℤ (𝓞 K))).ne_top
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      show algebraMap ℤ (𝓞 K) ((ℓ : ℕ) : ℤ) ∈ v.asIdeal
      rw [map_natCast]; exact hv
  rw [Ideal.absNorm_eq_pow_inertiaDeg' v.asIdeal hℓ] at h
  exact (Nat.prime_dvd_prime_iff_eq hp hℓ).1 (hp.dvd_of_dvd_pow h)

theorem splitIn_of_cls {D : D7} {p : ℕ} (h : D.host.cls p = .splitK) : SplitIn D p := by
  right
  unfold Formalism.BasicNotions.Host.cls primeClass at h
  split_ifs at h with h1 h2 h3 h4 <;> first | exact h4 | cases h

theorem goodLevel {D : D7} {T : Type} {L : LevCh D T} (P : Places L)
    (hsplit : ∀ p ∈ D.host.levelPrimes, D.host.cls p = .splitK) : GoodLevel D (levQ P) := by
  refine ⟨?_, fun p hp hdvd => ?_⟩
  · unfold levQ
    exact Finset.prod_pos fun v _ => pow_pos (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot)) _
  · unfold levQ at hdvd
    obtain ⟨v, hv, hd⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 hdvd
    have hd' := hp.dvd_of_dvd_pow hd
    rcases P.mem_S0_of_sum_eq.1 hv with rfl | h1
    · rw [eq_of_dvd_absNorm _ (leastSplitAuxiliaryPrimeThetaChain_spec D).1 hp P.basePlace_over_qZero hd']
      exact Or.inr (Formalism.L2.Host.split_prime_jacobi_neg_d D)
    · rcases (S1_mem_OmF D).1 h1 with h | h | h | h
      · rw [eq_of_dvd_absNorm _ (D.host.g_prime 0) hp h hd']
        exact splitIn_of_cls (hsplit _ (D.host.g_level 0))
      · rw [eq_of_dvd_absNorm _ (D.host.g_prime 1) hp h hd']
        exact splitIn_of_cls (hsplit _ (D.host.g_level 1))
      · rw [eq_of_dvd_absNorm _ D.host.pde_prime hp h hd']
        exact splitIn_of_cls (hsplit _ D.host.pde_level.1)
      · rw [eq_of_dvd_absNorm _ D.host.pde'_prime hp h hd']
        exact splitIn_of_cls (hsplit _ D.host.pde_level.2)

theorem twPl_base {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {μ₀ : T} (hL : L.Is μ₀) :
    twPl G μ₀ = ∅ := by
  have hQ : L.Q μ₀ = ∅ := by
    ext PP
    simp only [Finset.notMem_empty, iff_false]
    intro h
    refine ((hL.Q_ram μ₀ PP).2 (Or.inl h)) ?_
    rw [hL.xi_base]
    intro x _
    rfl
  ext w
  simp [twPl, locPl, hQ]

theorem nuH_inv_hasInf_all {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T} (hL : L.Is μ₀) (G : GridData L sc)
    (t : T) (i j : Fin D.R.m) : (nuH G t i j)⁻¹.HasInf (Formalism.L2.Host.embTau D)
      (fun τ => 2 * ((GlobalTheory.ChiGrid.num D sc.cGap τ).e (j + 1) + GlobalTheory.ChiGrid.cen D sc.cGap τ (D.R.m - i))) := by
  intro k
  have e : nuH G t i j = nuH G μ₀ i j * L.xiH t := by
    simp only [nuH, hL.xi_base, mul_one]; exact mul_div_right_comm _ _ _
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  rw [e, mul_inv, HChar.inf_mul, Units.val_mul, HChar.inf_inv (L.xiH t), Formalism.L2.Host.HChar.inf_eq_one_of_order hn ho k, inv_one,
    Units.val_one, mul_one]
  exact nuH_inv_hasInf hL G i j k

theorem rankV_lt {D : D7} {i j : ℕ} (hi : i ≤ D.R.m) (hj : j ≤ D.R.m) : rankV D i j + 1 ≤ bigN D := by
  have hm := D.R.two_le_m
  have e1 : j * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul_right _ hj
  have e2 : i * sLen D ≤ D.R.m * sLen D := Nat.mul_le_mul_right _ hi
  have e3 : D.R.m * (D.R.t + sLen D + 1) = D.R.m * D.R.t + D.R.m * sLen D + D.R.m := by ring
  simp only [rankV, bigN, Ranks.r]
  omega

theorem bottomRank_sum_le_two_mul_totalRank (D : D7) (i j : Fin D.R.m) : botBig D i j + botSmall D i j ≤ 2 * bigN D := by
  obtain ⟨h1, h2, -⟩ := ranks_exact D i j
  have a1 := rankV_lt (D := D) (i := i + 1) (j := j + 1) (by omega) (by omega)
  have a2 := rankV_lt (D := D) (i := i) (j := j) (by omega) (by omega)
  omega

theorem natAbs_le_maxWt (D : D7) (C : ℝ) (i j : Fin D.R.m) (τ : D.what₂.Tau) :
    max (wtA D C i j τ).natAbs (wtA' D C i j τ).natAbs ≤ maxWt D C := by
  unfold maxWt
  refine le_max_of_le_right ?_
  have := Finset.le_sup (f := fun x : Fin D.R.m × Fin D.R.m × D.what₂.Tau =>
      max (wtA D C x.1 x.2.1 x.2.2).natAbs (wtA' D C x.1 x.2.1 x.2.2).natAbs) (Finset.mem_univ (i, j, τ))
  exact this

theorem n_le_arith {n d ε c e A A' : ℤ} (hd : 0 ≤ d) (hε : ε = 1 ∨ ε = -1) (hc : c = e ∨ c = -e)
    (hw : 2 * n = ε * c - d) (hA : 2 * (A - A') = e - d) : n ≤ |A| + |A'| := by
  have l1 := le_abs_self A
  have l2 := neg_abs_le A
  have l3 := le_abs_self A'
  have l4 := neg_abs_le A'
  rcases hε with rfl | rfl <;> rcases hc with rfl | rfl <;> omega

theorem small_of {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T} (hL : L.Is μ₀) (G : GridData L sc)
    (t : T) (i j : Fin D.R.m) {δ t0 : ℂ} {Q : ℕ} (X : Pair D ⊤ δ t0 Q) (hd : X.d = botBig D i j + botSmall D i j)
    {χ : HChar D.host.E} (hc : HasChars X χ (nuH G t i j)⁻¹) : X.Small (bigN D) (maxWt D sc.cGap) := by
  refine ⟨hd ▸ bottomRank_sum_le_two_mul_totalRank D i j, fun τ => ?_⟩
  have habs := GlobalTheory.SplitWeight.abs_weight_eq_abs_infType X.W.chV' X.W.ep' _ _ X.W.ep_pm.2 hc.2
    (nuH_inv_hasInf_all hL G t i j) τ
  have hw : 2 * (X.n τ : ℤ) = X.W.ep' * X.W.chV'.n τ - ((botBig D i j + botSmall D i j : ℕ) : ℤ) := by
    rw [← hd]; exact X.wt τ
  have hn := n_le_arith (Nat.cast_nonneg _) X.W.ep_pm.2 (abs_eq_abs.1 habs) hw (two_mul_wtA_sub D sc.cGap i j τ)
  have hB := natAbs_le_maxWt D sc.cGap i j τ
  have hB1 := (le_max_left _ _).trans hB
  have hB2 := (le_max_right _ _).trans hB
  have c1 : ((wtA D sc.cGap i j τ).natAbs : ℤ) = |wtA D sc.cGap i j τ| := Int.natCast_natAbs _
  have c2 : ((wtA' D sc.cGap i j τ).natAbs : ℤ) = |wtA' D sc.cGap i j τ| := Int.natCast_natAbs _
  have hB1' : ((wtA D sc.cGap i j τ).natAbs : ℤ) ≤ maxWt D sc.cGap := by exact_mod_cast hB1
  have hB2' : ((wtA' D sc.cGap i j τ).natAbs : ℤ) ≤ maxWt D sc.cGap := by exact_mod_cast hB2
  have n_le : (X.n τ : ℤ) ≤ 2 * maxWt D sc.cGap := by linarith
  exact_mod_cast n_le

theorem botSmall_holds : BotSmall := by
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ hR T Lc μ₀ hL G => ⟨?_, ?_, ?_⟩⟩⟩
  · obtain ⟨⟨Pm, -, -⟩, -⟩ := hR.size
    exact goodLevel G.pl Pm.level_split
  · exact twPl_base G hL
  · intro δ t0 Q P P' t i j 𝔪 h
    exact ⟨small_of hL G t i j P h.rank.2.2.1 h.chars,
      small_of hL G t i j P' (h.rank.2.2.2.trans h.rank.2.2.1) h.chars'⟩

end GlobalTheory.SqTop.BotSmallProof
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareNuTwistedTupleRamifiedAtTwistPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareNuTwistedTupleRamifiedAtTwistPlace
open NumberField IsDedekindDomain
open Classical

namespace GlobalTheory.SqTop

open Formalism.BasicNotions Formalism.IndefR.Links Formalism.L2.Host GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum

theorem nuH_not_unrAt_twPl : ∀ {D : Formalism.BasicNotions.D7} {T : Type} {L : Formalism.IndefR.Links.LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GlobalTheory.ChiGrid.GridData L sc) {μ₀ : T}, L.Is μ₀ → ∀ (t : T) (i j : Fin D.R.m), ∀ P ∈ GlobalTheory.SqTop.twPl G t, ¬ (GlobalTheory.FunObj.SqNum.nuH G t i j).UnrAt P := by
  intro D T L sc G μ₀ hL t i j P hP
  classical
  have hP' : P ∈ L.Q t ∧ P ∉ G.pl.W0 := by
    simp only [twPl, GlobalTheory.FunObj.locPl, Finset.mem_filter, Finset.mem_union] at hP
    exact ⟨hP.1.resolve_left hP.2, hP.2⟩
  have hxi : ¬ (L.xiH t).UnrAt P := (hL.Q_ram t P).2 (Or.inl hP'.1)
  have hS1 : P.under (𝓞 D.host.F) ∉ S1 D := fun h => by
    have e := G.pl.w_Q t P hP'.1 h
    refine hP'.2 ?_
    rw [e]
    exact Finset.mem_image_of_mem _ (G.pl.mem_S0_of_sum_eq.2 (Or.inr h))
  have hS0 : P.under (𝓞 D.host.F) ∉ G.pl.S0 := fun h =>
    (G.pl.mem_S0_of_sum_eq.1 h).elim (G.pl.levelPlace_ne_basePlace t P hP'.1) hS1
  have a1 : 1 ≤ D.R.m - i := by have := i.2; omega
  have a2 : D.R.m - i ≤ D.R.m := by omega
  have hmu : (L.C.mu0 j).UnrAt P := (L.C.isMu0 j).unr P fun k hk => hS1 ((S1_mem_OmF D).2 ?_)
  · have hchi : (G.ch.chiH (D.R.m - i)).UnrAt P := G.ch.unr _ a1 a2 P hS0
    intro hnu
    apply hxi
    have e : L.xiH t = nuH G t i j * (L.C.mu0 j)⁻¹ * G.ch.chiH (D.R.m - i) := by
      rw [nuH]
      have key : ∀ {M : Type} [CommGroup M] (a x c : M), x = a * x / c * a⁻¹ * c := fun a x c => by
        rw [div_mul_eq_mul_div, div_mul_cancel, mul_comm a x, mul_inv_cancel_right]
      exact key _ _ _
    rw [e]
    exact (hnu.mul hmu.inv).mul hchi
  · have : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (P.under (𝓞 D.host.F)).asIdeal := by
      show algebraMap _ (𝓞 D.host.E) _ ∈ P.asIdeal
      rw [map_natCast]; exact hk
    fin_cases k
    · exact Or.inl this
    · exact Or.inr (Or.inl this)

end GlobalTheory.SqTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareNuTwistedTupleRamifiedAtTwistPlaceStatement
open NumberField IsDedekindDomain
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.square_nu_twisted_tuple_ramified_at_twist_place : ∀ {D : Formalism.BasicNotions.D7} {T : Type} {L : Formalism.IndefR.Links.LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GlobalTheory.ChiGrid.GridData L sc) {μ₀ : T}, L.Is μ₀ → ∀ (t : T) (i j : Fin D.R.m), ∀ P ∈ GlobalTheory.SqTop.twPl G t, ¬ (GlobalTheory.FunObj.SqNum.nuH G t i j).UnrAt P := by
  first | exact @GlobalTheory.SqTop.nuH_not_unrAt_twPl | exact GlobalTheory.SqTop.nuH_not_unrAt_twPl | (intros; apply GlobalTheory.SqTop.nuH_not_unrAt_twPl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEmbeddingSplitPrimeGridLocalTensorPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.AdelicU

namespace GlobalTheory.LocPlTau

theorem exists_splitPrime_locPl : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}
    (_hL : L.Is μ₀) (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)), (∃ w ∈ locPl G t, w.under (𝓞 D.host.F) = v) →
    ∃ τ : D.host.E →ₐ[D.host.F] Fv D.host.F v, ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) = v → splitPrime τ = w := by
  intro D T L sc G μ₀ hL t v ⟨w, hw, hv⟩
  subst hv
  obtain ⟨τ⟩ := GlobalTheory.LocPlSplit.locPl_split hL t w hw
  have hc := GlobalTheory.AdelicU.isCMExt_host D
  have hex : ∃ ρ : D.host.E →ₐ[D.host.F] Fv D.host.F (w.under (𝓞 D.host.F)), splitPrime ρ = w := by
    by_cases e : w = splitPrime τ
    · exact ⟨τ, e.symm⟩
    · exact (existsUnique_splitPrime_eq hc e rfl (splitPrime_under τ)).exists
  obtain ⟨ρ, hρ⟩ := hex
  exact ⟨ρ, fun w' hw' h => hρ.trans (GlobalTheory.FunObj.Good.under_injOn hL G t hw hw' h.symm)⟩

end GlobalTheory.LocPlTau
end
