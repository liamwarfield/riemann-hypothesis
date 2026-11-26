module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSpanAndGoodRange
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadNatZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormSmoothSpanNormLeShortRationalVector
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldMirabolic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCompletedLatticeConjugateHalfIffDual
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TsumRsPsiEqTsumNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleTrivialOfSamePolarization

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeOperatorPreservesSupLatticeRealSide
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeOperatorPreservesSupLatticeRealSide
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckeSupReal

open _root_.Formalism.L2.Pj Formalism.IndefR.FWT GlobalTheory.HeckeSup


set_option maxHeartbeats 1600000 in
theorem hkSupAt_realSide : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt → GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform → GlobalTheory.HeckeSupSt.HeckeReadTie → ∀ (D : D7) (X : RealSide D) j, GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.HkSupAt X.core X.R.toRealDat j := by
  intro hDec hI hT hRT D X i
  have hC := X.char
  have ht : TieIn X.core X.R.toRealDat X.geo.κ X.geo.v₀ :=
    ⟨X.geo.fw.laws, X.geo.fw.alg_eq, X.geo.fw.kap, X.geo.fw.hv₀, X.geo.fw.chiR, X.geo.fw.x0⟩
  have h5 : GlobalTheory.Core5 X.R.toRealDat X.F.lv2 := ⟨hC.lev, hC.grp, hC.fam, hC.models, hC.thP⟩
  have hio := GlobalTheory.IoExtremal.ioExt D _ _ _ _ _ X.R.toRealDat hC.lev hC.fam hC.models hC.thP
  have hr := GlobalTheory.OneMapTies.oneMapRow0_of_ties_ofFive GlobalTheory.ChartFree.chartIndep D _ _ _ _ X.core X.R.toRealDat X.F.lv2
    X.geo.κ X.geo.v₀ h5 ht hio X.geo.O i (X.geo.pins i)
  have hc := GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.constPinned_of X.core X.R.toRealDat X.geo.κ X.geo.v₀ X.geo.O i (X.geo.pins i) hr (X.geo.cTie i)
  have h0 := GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.readAt0_of X.core X.R.toRealDat X.geo.κ X.geo.v₀ X.inGeo.jEvExists X.geo.fw X.unif i hc
  have hsp := GlobalTheory.AdSpan.spanAt X.R.toRealDat hDec X.size hC.lev hC.fam hC.models hC.thP i X.A3.A.μ0
  refine hkSupAt_of_clauses hI hT GlobalTheory.HeckePointLaw.heckePointLaws (hC.lev.βW i) hC.fam.Sb hC.models.inf hC.models.HW
    hC.models.gW hC.models.HV hC.models.jV hC.thP.thF_mem X.geo.fw h0 hsp (fun O hO => ?_) fun c' hL hV => ?_
  · obtain ⟨cc, h1, u, h2, h3, h4, -⟩ := GlobalTheory.AdTh.ioExt_oneMap_ofFive.2.1 GlobalTheory.ChartFree.chartIndep D _ _ _ _ X.core
      X.R.toRealDat X.F.lv2 X.geo.κ X.geo.v₀ h5 ht hio i _ _ O hO
    exact ⟨cc, h1, u, h2, h3, h4⟩
  · exact @hRT D X.Γ _ _ X.Pl0 _ X.A3.A (withConst X.core c') X.alg X.R.toRealDat X.F.lv2 X.geo.κ X.geo.v₀ hC.lev hC.grp
      hC.fam hC.models hC.thP
      (@TieIn.mk D X.Γ _ _ X.Pl0 _ X.A3.A (withConst X.core c') X.alg X.R.toRealDat X.geo.κ X.geo.v₀ hL X.geo.fw.alg_eq
        X.geo.fw.kap X.geo.fw.hv₀ X.geo.fw.chiR X.geo.fw.x0) i _ rfl hV

end GlobalTheory.HeckeSupReal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeOperatorPreservesSupLatticeRealSideStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeOperator_preserves_supLattice_realSide : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt → GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform → GlobalTheory.HeckeSupSt.HeckeReadTie → ∀ (D : D7) (X : RealSide D) j, GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.HkSupAt X.core X.R.toRealDat j := by
  first | exact @GlobalTheory.HeckeSupReal.hkSupAt_realSide | exact GlobalTheory.HeckeSupReal.hkSupAt_realSide | (intros; apply GlobalTheory.HeckeSupReal.hkSupAt_realSide <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalPhaseThetaSeriesExpandsCuspFormsSmallFie
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalPhaseThetaSeriesExpandsCuspFormsSmallFie
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.ConjTwist
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.SeriesTie.RatExpand

variable {D : D7}

theorem castDict_sum_smul {V W : HSp D} (e : V = W) {m : ℕ} (a : Fin m → ℂ) (ψ : Fin m → GA D V → ℂ) (g : GA D W) :
    castDict e (∑ i, a i • ψ i) g = ∑ i, a i * castDict e (ψ i) g := by
  subst e
  simp [castDict, Finset.sum_apply]

theorem castDict_phiJ {T : CoreJ D} {j : ℕ} {W : HSp D} {σ : T.Q.c.F →+* ℂ} (hσ : σ = T.σ₀) (h1 : T.V j σ = W)
    (h2 : T.V j T.σ₀ = W) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) (g : GA D W) :
    (h1 ▸ T.phiJ j σ a f : GA D W → ℂ) g = castDict h2 (T.phiJ j T.σ₀ a f) g := by
  subst hσ
  subst h1
  rfl

theorem mem_ratVec {G : Type} [Group G] [Fintype G] {Pl0 T1 : Type} {A : FamIn D.what₂.LL G Pl0 T1 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (j : Fin D.R.m)
    (c0 : VsV D j D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV j).W) (v : VsV D j D.what₂.LL)
    (hv : ∀ m, ∃ q : ℚ, AddMonoidAlgebra.coeff (v : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank) m = (q : D.what₂.LL))
    (k : Subfield ℂ) : c0 v ∈ GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.ratVec R j c0 k := by
  refine Submodule.subset_span ⟨v, fun m => ?_, rfl⟩
  obtain ⟨q, hq⟩ := hv m
  rw [hq, map_ratCast]
  exact SubfieldClass.ratCast_mem k q

theorem expands_of_isRatPhase : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m), GlobalTheory.NT.RayField → ∀ (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T.Q.c.F) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (F : Face D A3.A) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (O : ∀ j, OMDat T.toCore Rl.toRealDat j Unit (fun _ => A3.A.μ0)), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → LawsJ T → GlobalTheory.Hk3.Core Rl.toRealDat F → Nonempty (FWTie T Rl.toRealDat κ v₀) → TieIn T Rl.toRealDat κ v₀ → IoExt Rl.toRealDat → QGuard Rl.toRealDat → IsGalois ℚ D.LL0 → Formalism.L2.Host.ValLL0 D Rl.C → RayIn D (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') (embLL0 D).fieldRange → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange) → ∀ (j : Fin D.R.m) (hV : T.V ((j : ℕ) + 1) T.σ₀ = Wc D j), OMPins T Rl.toRealDat κ v₀ O j → GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T Rl.toRealDat j T.σ₀ hV → ∀ gramR c0R c0L, Bridge.FamTie Rl.B Rl.pl (Rl.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) Rl.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ) (fun j τ => Bridge.lamLdef (Vc D j).rank ((j : ℕ) + 1) τ) gramR c0R c0L → CoefficientBaseChange Rl.toRealDat j (O j).jL (inC (O j).c') (c0L j) (O j).c0' → ∀ (u : ∀ ρ, lowT (Rl.MW j (sg0 D A3.A)) ρ), (∀ ρ, (u ρ : (Rl.MW j (sg0 D A3.A)).sm ρ) = v₀ j _ ρ) → ∀ (ph₀ : ℂ), GlobalTheory.SeriesTie.IsRatPhase T Rl.toRealDat j hV (κ j) u (c0L j) ph₀ → ∀ (c : VsV D j ℂ →ₗ[ℂ] (Rl.cV j).W), ExtC Rl.toRealDat j (inC (O j).c') (O j).c0' c → ∀ (v : VsV D j D.what₂.LL), (∀ m, ∃ q : ℚ, AddMonoidAlgebra.coeff (v : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank) m = (q : D.what₂.LL)) → ∀ (x : VsV D j ℂ), (x : Pol ℂ D.what₂.Tau (Vc D j).rank) = MvPolynomial.map D.what₂.embLL (v : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank) → ∀ h ∈ GfC (Vc D j), ∃ (n : ℕ) (e : Fin n → ℂ) (f : Fin n → T.toCore.cuspA ((j : ℕ) + 1) (wtA (κ j)) (κ j).n), Expands (O j) (κ j) (fun g => ph₀ * ser Rl.toRealDat j A3.A.μ0 (Rl.vP j A3.A.μ0) u h (c x) g) e f ∧ ∀ k, e k ∈ (embLL0 D).fieldRange := by
  intro D Γ _ _ Pl0 I0 T0 A3 hRF T _ Rl cG S YS F κ v₀ O hnV hT hcore hfw hti hio hQ hgal hval hray hroots j hV hpins hfp
    gramR c0R c0L hft hbc u hu ph₀ hph c hc v hv x hx h hh
  have hInR : Formalism.L2.Pj.InR D ((j : ℕ) + 1) := ⟨by omega, by have := j.2; omega⟩
  have hlast : (κ j).LastPos := fun τ i hi => by
    rw [(hti.kap j τ).1 i]
    exact GlobalTheory.LiftWeight.kapTop_lastPos D j τ i hi
  have hn : 8 * D.R.f * D.R.r + 4 ≤ (κ j).n := by
    rw [(hti.kap j (D.eTau.symm 1)).2.2]
    exact hnV

  obtain ⟨C, hpd, hfr, hgood⟩ := GlobalTheory.T.exists_goodCover_levelOne_over_smallField D Γ Pl0 I0 T0 A3 hRF T Rl cG S YS F κ v₀ O hT hcore hfw hti hio hQ hgal hval hray hroots j hV
    hpins hfp (κ j).n
  have hser := hph C hgood hfr.ge
  have hdat : GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.IsLevDatum Rl.toRealDat.ψ (Vc D j) (Wc D j) (Rl.toRealDat.ΛV j) (Rl.toRealDat.ΛW j)
      (T.Q.l.M * C.d.pd) C.σ₂.fieldRange (Rl.toRealDat.vacP j) (Rl.toRealDat.vP j A3.A.μ0) := by
    rw [hpd, mul_one, hfr]
    exact GlobalTheory.T.isLevelDatum_referenceTuple_smallField D Γ Pl0 I0 T0 A3 hRF T Rl cG S YS F κ v₀ O hT hcore hfw hti hio hQ hgal hval hray hroots j hV hpins hfp

  have hcx : c x = c0L j v := by
    obtain ⟨v', hv', he⟩ := hbc v
    refine (hc v' x ?_).trans he
    rw [hx, hv', MvPolynomial.map_map, hpins.2.lift.field]
  have hw : c x ∈ GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.ratVec Rl.toRealDat j (c0L j) C.σ₂.fieldRange := by
    rw [hcx]
    exact mem_ratVec Rl.toRealDat j (c0L j) v hv _
  obtain ⟨φ', hφ'm, hφ'e⟩ := (hser h hh _ hdat (c x) hw).1

  have hspan : Formalism.L2.Pj.holSub0 (T.U ((j : ℕ) + 1) T.σ₀).X (laU (T.U ((j : ℕ) + 1) T.σ₀) (wtA (κ j)) (κ j).n) ≤
      Submodule.span ℂ (rdU (T.U ((j : ℕ) + 1) T.σ₀) '' {f | f ∈ sec (T.Q.Xo ((j : ℕ) + 1)) T.Q.c (wtA (κ j)) (κ j).n ∧
        rdU (T.U ((j : ℕ) + 1) T.σ₀) f ∈ Formalism.L2.Pj.holSub0 (T.U ((j : ℕ) + 1) T.σ₀).X
          (laU (T.U ((j : ℕ) + 1) T.σ₀) (wtA (κ j)) (κ j).n)}) := by
    refine (GlobalTheory.OntoCore.holSub0_le_span_cuspA D T hT _ hInR (κ j) hlast hn T.σ₀ T.toCore.good_σ₀).trans
      (Submodule.span_mono (Set.image_mono fun f hf => ⟨Formalism.L2.Pj.cusp_le_sec _ _ _ _ _ hf, ?_, ?_⟩))
    · exact ((Formalism.L2.Pj.mem_cusp _ _ _ _ _ f).1 hf).2 T.σ₀ T.toCore.good_σ₀
    · exact Formalism.L2.Pj.rdU_mem_offZero _ _
  have hmu := GlobalTheory.T.dictionaryCharacter_right_invariant_coreLevel D Γ Pl0 I0 T0 A3 hRF T Rl cG S YS F κ v₀ O hT hcore hfw hti hio hQ hgal hval hray hroots j hV hpins hfp
  have hinv := GlobalTheory.T.liftDatum_thetaSeries_right_invariant_coreLevel D Γ Pl0 I0 T0 A3 hRF T Rl cG S YS F κ v₀ O hT hcore hfw hti hio hQ hgal hval hray hroots j hV hpins hfp
    u h hh (c x) ph₀ φ' hφ'e
  obtain ⟨m, xs, ψ, hψ, hφeq⟩ := GlobalTheory.T.holomorphic_sections_span_restriction D T hT _ hInR T.σ₀ T.toCore.good_σ₀ C hgood.1 (wtA (κ j)) (κ j).n
    (dom_wtA _) (hgood.2.1 _ (dom_wtA _)) hspan hmu φ' hφ'm hinv
  have hψ' : ∀ k, ∃ f, (f ∈ sec (T.Q.Xo ((j : ℕ) + 1)) T.Q.c (wtA (κ j)) (κ j).n ∧
      rdU (T.U ((j : ℕ) + 1) T.σ₀) f ∈ Formalism.L2.Pj.holSub0 (T.U ((j : ℕ) + 1) T.σ₀).X
        (laU (T.U ((j : ℕ) + 1) T.σ₀) (wtA (κ j)) (κ j).n)) ∧ T.phiJ ((j : ℕ) + 1) T.σ₀ (wtA (κ j)) f = ψ k := hψ
  choose fs hfs using hψ'
  let f' : Fin m → T.toCore.cuspA ((j : ℕ) + 1) (wtA (κ j)) (κ j).n := fun k =>
    ⟨fs k, GlobalTheory.T.mem_cuspForms_of_reading_bounded_cuspidal_holomorphic D T hT _ hInR (κ j) hlast hn (fs k) (hfs k).1.1 (hfs k).1.2⟩
  refine ⟨m, fun k => C.σ₂ (xs k), f', fun g => ?_, fun k => by rw [← hfr]; exact ⟨xs k, rfl⟩⟩
  show ph₀ * ser Rl.toRealDat j A3.A.μ0 (Rl.vP j A3.A.μ0) u h (c x) g = _
  rw [show ph₀ * ser Rl.toRealDat j A3.A.μ0 (Rl.vP j A3.A.μ0) u h (c x) g = castDict hV φ' g from
    (congrFun hφ'e g).symm, hφeq, castDict_sum_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  rw [← (hfs k).2]
  exact ((Formalism.IndefR.FWT.phi_cE T Rl.toRealDat O j (wtA (κ j)) (fs k) g).trans
    (castDict_phiJ (sOv_eq _ _ _) (O j).hV hV _ _ g)).symm

end GlobalTheory.SeriesTie.RatExpand
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalPhaseThetaSeriesExpandsCuspFormsSmallFieStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.ConjTwist
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalPhaseThetaSeries_expands_cuspForms_smallField : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m), GlobalTheory.NT.RayField → ∀ (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T.Q.c.F) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (F : Face D A3.A) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (O : ∀ j, OMDat T.toCore Rl.toRealDat j Unit (fun _ => A3.A.μ0)), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → LawsJ T → GlobalTheory.Hk3.Core Rl.toRealDat F → Nonempty (FWTie T Rl.toRealDat κ v₀) → TieIn T Rl.toRealDat κ v₀ → IoExt Rl.toRealDat → QGuard Rl.toRealDat → IsGalois ℚ D.LL0 → Formalism.L2.Host.ValLL0 D Rl.C → RayIn D (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') (embLL0 D).fieldRange → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange) → ∀ (j : Fin D.R.m) (hV : T.V ((j : ℕ) + 1) T.σ₀ = Wc D j), OMPins T Rl.toRealDat κ v₀ O j → GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T Rl.toRealDat j T.σ₀ hV → ∀ gramR c0R c0L, Bridge.FamTie Rl.B Rl.pl (Rl.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) Rl.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ) (fun j τ => Bridge.lamLdef (Vc D j).rank ((j : ℕ) + 1) τ) gramR c0R c0L → CoefficientBaseChange Rl.toRealDat j (O j).jL (inC (O j).c') (c0L j) (O j).c0' → ∀ (u : ∀ ρ, lowT (Rl.MW j (sg0 D A3.A)) ρ), (∀ ρ, (u ρ : (Rl.MW j (sg0 D A3.A)).sm ρ) = v₀ j _ ρ) → ∀ (ph₀ : ℂ), GlobalTheory.SeriesTie.IsRatPhase T Rl.toRealDat j hV (κ j) u (c0L j) ph₀ → ∀ (c : VsV D j ℂ →ₗ[ℂ] (Rl.cV j).W), ExtC Rl.toRealDat j (inC (O j).c') (O j).c0' c → ∀ (v : VsV D j D.what₂.LL), (∀ m, ∃ q : ℚ, AddMonoidAlgebra.coeff (v : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank) m = (q : D.what₂.LL)) → ∀ (x : VsV D j ℂ), (x : Pol ℂ D.what₂.Tau (Vc D j).rank) = MvPolynomial.map D.what₂.embLL (v : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank) → ∀ h ∈ GfC (Vc D j), ∃ (n : ℕ) (e : Fin n → ℂ) (f : Fin n → T.toCore.cuspA ((j : ℕ) + 1) (wtA (κ j)) (κ j).n), Expands (O j) (κ j) (fun g => ph₀ * ser Rl.toRealDat j A3.A.μ0 (Rl.vP j A3.A.μ0) u h (c x) g) e f ∧ ∀ k, e k ∈ (embLL0 D).fieldRange := by
  first | exact @GlobalTheory.SeriesTie.RatExpand.expands_of_isRatPhase | exact GlobalTheory.SeriesTie.RatExpand.expands_of_isRatPhase | (intros; apply GlobalTheory.SeriesTie.RatExpand.expands_of_isRatPhase <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaIntegralUpperMspan
noncomputable section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GlobalTheory.ThetaPoisson GlobalTheory.ShortVecDecay
open scoped ComplexConjugate nonZeroDivisors ENNReal
open GlobalTheory.RSTheta GroundTheory.Global.IdeleGroup

namespace GlobalTheory.RSThetaM

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def measSub (E : Type) [Field E] [NumberField E] (a : ℕ) : Submodule ℂ (GA E a → ℂ) where
  carrier := {F | Measurable F}
  add_mem' hF hG := Measurable.add hF hG
  zero_mem' := measurable_const
  smul_mem' c _ hF := Measurable.const_smul hF c

theorem measurable_gl_of_matrix {X : Type} [MeasurableSpace X] {γ : X → GL (Fin a) (Cinf E)}
    (h : Measurable fun x => (γ x : Matrix (Fin a) (Fin a) (Cinf E))) : Measurable γ := by
  have hu : Continuous fun q : invSet E a =>
      (IsUnit.unit (q.2 : IsUnit (Matrix.of q.1)) : GL (Fin a) (Cinf E)) := by
    refine Units.continuous_iff.2 ⟨continuous_subtype_val, ?_⟩
    have := GlobalTheory.ConstTermSmooth.contDiffOn_invM.continuousOn.comp_continuous
      (f := fun q : invSet E a => q.1) continuous_subtype_val fun q => q.2
    refine Continuous.congr this fun q => ?_
    simp only [Matrix.coe_units_inv]
    rfl
  have hm : Measurable fun x => (⟨toL (γ x).val, (γ x).isUnit⟩ : invSet E a) := h.subtype_mk
  convert hu.measurable.comp hm using 1
  funext x
  ext1
  rfl

theorem measurable_of_mem_mspanR (π : CuspSub E a) {F : GA E a → ℂ} (hF : F ∈ GlobalTheory.JSW.mspanR π) : Measurable F := by
  have hF' := hF
  unfold GlobalTheory.JSW.mspanR at hF'
  refine Submodule.mem_sInf.1 hF' (measSub E a) ⟨fun φ hφ => ?_, fun F hF h => ?_,
    fun F hF X _ ν _ k γ hk => ?_⟩
  · exact (continuous_of_mem_or (π := π) (Or.inl hφ)).measurable
  · exact (hF : Measurable F).comp (continuous_mul_const h).measurable
  · have hγ : Measurable fun p : GA E a × X => p.1 * infGL E a (γ p.2) :=
      measurable_fst.mul ((GlobalTheory.ConstTermSmooth.continuous_infGL.measurable.comp
        (measurable_gl_of_matrix hk.2.1)).comp measurable_snd)
    have h1 : StronglyMeasurable fun p : GA E a × X => k p.2 * F (p.1 * infGL E a (γ p.2)) :=
      ((hk.1.comp measurable_snd).mul ((hF : Measurable F).comp hγ)).stronglyMeasurable
    exact (h1.integral_prod_right' (ν := ν)).measurable

theorem measurable_rsInf {ℓ : Fin a} {φ φ' : GA E a → ℂ} {Φ : (Fin a → Cinf E) → ℂ} (h : Measurable φ)
    (h' : Measurable φ') (hΦ : Continuous Φ) (hs : tsupport Φ ⊆ rowSet E ℓ) :
    Measurable fun p : GA E a × (Fin a → Cinf E) => rsInf ℓ φ φ' Φ p.1 p.2 := by
  set s : Set (GA E a × (Fin a → Cinf E)) := Set.univ ×ˢ rowSet E ℓ with hsdef
  have hsm : MeasurableSet s := (isOpen_univ.prod (isOpen_rowSet ℓ)).measurableSet
  refine measurable_of_restrict_of_restrict_compl hsm ?_ ?_
  · have hc : Continuous fun p : s => p.1.1 * (infGL E a (rowGL ℓ p.1.2))⁻¹ := by
      have h2 : ContinuousOn (fun p : GA E a × (Fin a → Cinf E) => p.1 * (infGL E a (rowGL ℓ p.2))⁻¹) s :=
        continuous_fst.continuousOn.mul ((continuousOn_inv_rowGL ℓ).comp continuous_snd.continuousOn
          fun p hp => hp.2)
      exact h2.restrict
    have hm := hc.measurable
    exact ((h.comp hm).mul (Complex.continuous_conj.measurable.comp (h'.comp hm))).mul
      (hΦ.measurable.comp (measurable_snd.comp measurable_subtype_coe))
  · convert (measurable_const (a := (0 : ℂ)) : Measurable fun _ : (sᶜ : Set (GA E a × (Fin a → Cinf E))) => (0 : ℂ)) using 1
    funext p
    have hp : p.1.2 ∉ tsupport Φ := fun hp => p.2 ⟨trivial, hs hp⟩
    change rsInf ℓ φ φ' Φ p.1.1 p.1.2 = 0
    simp [rsInf, image_eq_zero_of_notMem_tsupport hp]

theorem measurable_rsPsi_vecMul {ℓ : Fin a} {φ φ' : GA E a → ℂ} {Φ : (Fin a → Cinf E) → ℂ} (h : Measurable φ)
    (h' : Measurable φ') (hΦ : Continuous Φ) (hs : tsupport Φ ⊆ rowSet E ℓ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ)
    (η : Fin a → Af E) (ξ : Fin a → E) :
    Measurable fun g : GA E a => rsPsi ℓ φ φ' Φ J η g ((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val) := by
  have hY : Continuous fun g : GA E a => (fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val :=
    continuous_const.matrix_vecMul Units.continuous_val
  have hI : Continuous fun g : GA E a => fun i => pInf E (((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val) i) :=
    continuous_pi fun i => GlobalTheory.ShortVecDecay.continuous_pInf.comp ((continuous_apply i).comp hY)
  have hF : Continuous fun g : GA E a => (fun i => pFin E (((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val) i)) - η :=
    (continuous_pi fun i => (continuous_snd : Continuous (pFin E)).comp ((continuous_apply i).comp hY)).sub
      continuous_const
  have h3 : Continuous ((latt a J).indicator (1 : (Fin a → Af E) → ℂ)) :=
    IsClopen.continuous_indicator ⟨isClosed_latt J, isOpen_latt J⟩ continuous_const
  exact ((measurable_rsInf h h' hΦ hs).comp (measurable_id.prodMk hI.measurable)).mul (h3.comp hF).measurable

theorem theta_integral_upper_mspan : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ℓ : Fin a)
    (π π' : CuspSub E a), π.IsUnitary → π'.IsUnitary → ∀ φ φ' : Sm E a,
    (φ ∈ π.V ∨ φ.1 ∈ GlobalTheory.JSW.mspanR π) → (φ' ∈ π'.V ∨ φ'.1 ∈ GlobalTheory.JSW.mspanR π') →
    ∀ Φ : (Fin a → Cinf E) → ℂ, Continuous Φ → HasCompactSupport Φ → tsupport Φ ⊆ rowSet E ℓ →
    ∀ (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 : Set (GA E a)),
    IsFundamentalDomain (ratGL E a).range 𝓕 μ →
    (∀ g : GA E a, Summable fun ξ : {ξ : Fin a → E // ξ ≠ 0} =>
      ‖rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)‖) ∧
    (∀ x : ℝ, IntegrableOn (fun g : GA E a =>
      (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)‖) *
        (ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x)
      (𝓕 ∩ {g | 1 ≤ (ideleModule E (GeneralLinearGroup.det g) : ℝ)}) μ) ∧
    (∀ s : ℂ, IntegrableOn (fun g : GA E a =>
      (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) *
        ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ s)
      (𝓕 ∩ {g | 1 ≤ (ideleModule E (GeneralLinearGroup.det g) : ℝ)}) μ) ∧
    (Differentiable ℂ fun s : ℂ => ∫ g in 𝓕 ∩ {g | 1 ≤ (ideleModule E (GeneralLinearGroup.det g) : ℝ)},
      (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) *
        ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ s ∂μ) ∧
    Continuous fun x : ℝ => ∫ g in 𝓕 ∩ {g | 1 ≤ (ideleModule E (GeneralLinearGroup.det g) : ℝ)},
      (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) *
        (((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x : ℝ) : ℂ) ∂μ := by
  intro E _ _ _ a ℓ π π' hπ hπ' φ φ' hφ hφ' Φ hΦ hc hs J η μ _ 𝓕 h𝓕
  have hdec : ∀ {ρ : CuspSub E a}, ρ.IsUnitary → ∀ {ψ : Sm E a}, (ψ ∈ ρ.V ∨ ψ.1 ∈ GlobalTheory.JSW.mspanR ρ) → Decays ψ.1 :=
    fun {ρ} hρ {ψ} hψ L hL C₀ hC₀ N => GlobalTheory.T.cuspFormSmoothSpan_norm_le_shortRationalVector E a ρ hρ ψ hψ [] L hL C₀ hC₀ N
  have hmeas : ∀ {ρ : CuspSub E a} {ψ : Sm E a}, (ψ ∈ ρ.V ∨ ψ.1 ∈ GlobalTheory.JSW.mspanR ρ) → Measurable ψ.1 :=
    fun {ρ} {ψ} hψ => hψ.elim (fun h => (continuous_of_mem_or (π := ρ) (Or.inl h)).measurable)
      (GlobalTheory.RSThetaM.measurable_of_mem_mspanR ρ)
  have hK := isSmallKernel_rsPsi (hdec hπ hφ) (hdec hπ' hφ') hΦ hc hs J η
  obtain ⟨C, hC⟩ := hK.tsum_le (N := 1) le_rfl
  obtain ⟨h1, h2, h3⟩ := hK.integrableOn μ h𝓕 fun ξ _ =>
    (GlobalTheory.RSThetaM.measurable_rsPsi_vecMul (hmeas hφ) (hmeas hφ') hΦ hs J η ξ).aestronglyMeasurable
  refine ⟨fun g => (hC g).1, h1, h2, h3, (h3.continuous.comp Complex.continuous_ofReal).congr fun x => ?_⟩
  refine integral_congr_ae (.of_forall fun g => ?_)
  exact congrArg _ (Complex.ofReal_cpow (ideleModule E _).2.le x).symm

end GlobalTheory.RSThetaM

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsMirabolicWhittakerStageTopOfVanishingBlockAver
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsMirabolicWhittakerStageTopOfVanishingBlockAver
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open GlobalTheory.MirTower GlobalTheory.CuspGeneric
open GroundTheory.Automorphic.FourierWhittaker (partialCoeff blockGL uGL)

noncomputable section

namespace GlobalTheory.CuspGeneric

theorem good_top : ∀ (E : Type) [Field E] [NumberField E] (m : ℕ) (ψ : AddChar (Ad E) ℂ) (f : GA E (m + 1) → ℂ),
    Continuous f → (∀ γ g, f (ratGL E (m + 1) γ * g) = f g) →
    (∀ r, 0 < r → r ≤ m → ∀ g, avg (ratV E (UnipotentBlockColumnIndex (m + 1) r m)) (fun x => f (blkU x * g)) = 0) → Good ψ m f := by
  intro E _ _ m ψ f hc hl hv
  refine ⟨hc, fun γ _ g => hl γ g, by
    intro k hk y g
    have he : IsEmpty (UnipotentBlockColumnIndex (m + 1) k k) := ⟨fun t => by have := t.1.2.isLt; have := t.2; omega⟩
    have hy : y = 0 := Subsingleton.elim _ _
    subst hy
    have hd : dot (eLast (m + 1) k) (0 : UnipotentBlockColumnIndex (m + 1) k k → Ad E) = 0 := by simp [dot]
    rw [hd, AddChar.map_zero_eq_one, one_mul]
    unfold blkU
    rw [posU_zero, one_mul], hv⟩

end GlobalTheory.CuspGeneric

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsMirabolicWhittakerStageTopOfVanishingBlockAverStatement
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open GlobalTheory.MirTower GlobalTheory.CuspGeneric
open GroundTheory.Automorphic.FourierWhittaker (partialCoeff blockGL uGL)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isMirabolicWhittakerStage_top_of_vanishing_blockAverages : ∀ (E : Type) [Field E] [NumberField E] (m : ℕ) (ψ : AddChar (Ad E) ℂ) (f : GA E (m + 1) → ℂ),
    Continuous f → (∀ γ g, f (ratGL E (m + 1) γ * g) = f g) →
    (∀ r, 0 < r → r ≤ m → ∀ g, avg (ratV E (UnipotentBlockColumnIndex (m + 1) r m)) (fun x => f (blkU x * g)) = 0) → Good ψ m f := by
  first | (exact @GlobalTheory.CuspGeneric.good_top) | (exact GlobalTheory.CuspGeneric.good_top) | (intros; apply GlobalTheory.CuspGeneric.good_top  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeTransformCuspFormsReadsCosetSum
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeTransformCuspFormsReadsCosetSum
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX Formalism.IndefR.FWT GlobalTheory.TwInputs NumberField IsDedekindDomain
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckeSupReal

open GlobalTheory.HeckeSup


set_option maxHeartbeats 1600000 in
theorem readsCusp_realSide : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.HeckeSupSt.HeckeReadTie → ∀ (D : D7) (X : GlobalTheory.TwInputs.RealSide D)
    (i : Fin D.R.m) (hV : X.core.V ((i : ℕ) + 1) (Formalism.IndefR.FWT.res X.core (sg0 D X.A3.A)) = Wc D i),
    GlobalTheory.HeckeSup.ReadsCusp X.core X.R.toRealDat X.geo.κ i (Formalism.IndefR.FWT.res X.core (sg0 D X.A3.A)) hV := by
  intro hDec hRT D X i hV
  have hC := X.char
  have ht : TieIn X.core X.R.toRealDat X.geo.κ X.geo.v₀ :=
    ⟨X.geo.fw.laws, X.geo.fw.alg_eq, X.geo.fw.kap, X.geo.fw.hv₀, X.geo.fw.chiR, X.geo.fw.x0⟩
  have h5 : GlobalTheory.Core5 X.R.toRealDat X.F.lv2 := ⟨hC.lev, hC.grp, hC.fam, hC.models, hC.thP⟩
  have hio := GlobalTheory.IoExtremal.ioExt D _ _ _ _ _ X.R.toRealDat hC.lev hC.fam hC.models hC.thP
  have hr := GlobalTheory.OneMapTies.oneMapRow0_of_ties_ofFive GlobalTheory.ChartFree.chartIndep D _ _ _ _ X.core X.R.toRealDat X.F.lv2
    X.geo.κ X.geo.v₀ h5 ht hio X.geo.O i (X.geo.pins i)
  have hc := GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.constPinned_of X.core X.R.toRealDat X.geo.κ X.geo.v₀ X.geo.O i (X.geo.pins i) hr (X.geo.cTie i)
  have h0 := GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.readAt0_of X.core X.R.toRealDat X.geo.κ X.geo.v₀ X.inGeo.jEvExists X.geo.fw X.unif i hc
  have hsp := GlobalTheory.AdSpan.spanAt X.R.toRealDat hDec X.size hC.lev hC.fam hC.models hC.thP i X.A3.A.μ0
  refine readsCusp_of_clauses (hC.lev.βW i) hC.fam.Sb hC.models.inf hC.models.HW hC.models.gW hC.models.HV hC.models.jV
    hC.thP.thF_mem X.geo.fw hV (h0.ex hV) h0.const hsp (fun O hO => ?_) fun c' hL hV' => ?_
  · obtain ⟨cc, h1, u, h2, h3, h4, -⟩ := GlobalTheory.AdTh.ioExt_oneMap_ofFive.2.1 GlobalTheory.ChartFree.chartIndep D _ _ _ _ X.core
      X.R.toRealDat X.F.lv2 X.geo.κ X.geo.v₀ h5 ht hio i _ _ O hO
    exact ⟨cc, h1, u, h2, h3, h4⟩
  · exact @hRT D X.Γ _ _ X.Pl0 _ X.A3.A (withConst X.core c') X.alg X.R.toRealDat X.F.lv2 X.geo.κ X.geo.v₀ hC.lev hC.grp
      hC.fam hC.models hC.thP
      (@TieIn.mk D X.Γ _ _ X.Pl0 _ X.A3.A (withConst X.core c') X.alg X.R.toRealDat X.geo.κ X.geo.v₀ hL X.geo.fw.alg_eq
        X.geo.fw.kap X.geo.fw.hv₀ X.geo.fw.chiR X.geo.fw.x0) i _ rfl hV'

end GlobalTheory.HeckeSupReal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeTransformCuspFormsReadsCosetSumStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX Formalism.IndefR.FWT GlobalTheory.TwInputs NumberField IsDedekindDomain
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeTransform_cuspForms_reads_cosetSum : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.HeckeSupSt.HeckeReadTie → ∀ (D : D7) (X : GlobalTheory.TwInputs.RealSide D) (i : Fin D.R.m) (hV : X.core.V ((i : ℕ) + 1) (Formalism.IndefR.FWT.res X.core (sg0 D X.A3.A)) = Wc D i), GlobalTheory.HeckeSup.ReadsCusp X.core X.R.toRealDat X.geo.κ i (Formalism.IndefR.FWT.res X.core (sg0 D X.A3.A)) hV := by
  first | exact @GlobalTheory.HeckeSupReal.readsCusp_realSide | exact GlobalTheory.HeckeSupReal.readsCusp_realSide | (intros; apply GlobalTheory.HeckeSupReal.readsCusp_realSide <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SuperDiagBlockGL
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
noncomputable section

namespace GlobalTheory.RSnmUnfProps

open GroundTheory.Automorphic.FourierWhittaker (blockGL blockMat blockMat_apply coe_blockGL)

theorem superDiag_blockGL {R : Type} [CommRing R] {j n : ℕ} (hj : j ≤ n) (g : GL (Fin j) R) :
    GlobalTheory.Whittaker.superDiag (blockGL hj g) = GlobalTheory.Whittaker.superDiag g := by
  unfold GlobalTheory.Whittaker.superDiag
  simp only [Finset.sum_filter]
  symm
  refine Fintype.sum_of_injective (Fin.castLE hj) (Fin.castLE_injective hj) _ _ ?_ ?_
  · intro i hi
    have hij : ¬ (i : ℕ) < j := fun h => hi ⟨⟨i, h⟩, rfl⟩
    refine Finset.sum_eq_zero fun b _ => ?_
    split_ifs with hb
    · rw [coe_blockGL, blockMat_apply, dite_eq_right hij, if_neg]
      intro h; rw [h] at hb; omega
    · rfl
  · intro i
    refine Fintype.sum_of_injective (Fin.castLE hj) (Fin.castLE_injective hj) _ _ ?_ ?_
    · intro b hb
      have hbj : ¬ (b : ℕ) < j := fun h => hb ⟨⟨b, h⟩, rfl⟩
      split_ifs
      · rw [coe_blockGL, blockMat_apply, dite_eq_left (by simp), dite_eq_right hbj]
      · rfl
    · intro b
      simp only [Fin.coe_castLE]
      split_ifs
      · rw [coe_blockGL, blockMat_apply, dite_eq_left (by simp), dite_eq_left (by simp)]
        rfl
      · rfl

variable {E : Type} [Field E] [NumberField E]

theorem psiN_blockGL {j n : ℕ} (hj : j ≤ n) (g : GA E j) :
    GlobalTheory.JSW.psiN (blockGL hj g : GA E n) = GlobalTheory.JSW.psiN g := by
  unfold GlobalTheory.JSW.psiN
  rw [superDiag_blockGL]

theorem norm_psiN {a : ℕ} (u : GA E a) : ‖GlobalTheory.JSW.psiN u‖ = 1 := by
  simp [GlobalTheory.JSW.psiN, Circle.norm_coe]

theorem blockGL_mem_NA {j n : ℕ} (hj : j ≤ n) {u : GA E j} (hu : u ∈ GlobalTheory.JSW.NA (E := E) (a := j)) :
    (blockGL hj u : GA E n) ∈ GlobalTheory.JSW.NA (E := E) (a := n) := by
  obtain ⟨h1, h2⟩ := hu
  refine ⟨fun i k hik => ?_, fun i => ?_⟩
  · rw [coe_blockGL, blockMat_apply]
    split_ifs with ha hb hc
    · exact h1 _ _ (by rw [Fin.lt_def] at hik ⊢; exact hik)
    · rfl
    · exact absurd hik (by rw [hc]; exact lt_irrefl _)
    · rfl
  · rw [coe_blockGL, blockMat_apply]
    split_ifs with ha hb
    · exact h2 _
    · rfl
    · exact absurd rfl hb

theorem detAbs_unip {a : ℕ} {u : GA E a} (hu : u ∈ GlobalTheory.CellDec.NA E a) : GlobalTheory.RSnm.detAbs u = 1 := by
  have hd : Matrix.GeneralLinearGroup.det u = 1 := Units.ext (GlobalTheory.RSLocalPart.det_eq_one hu)
  rw [GlobalTheory.RSnm.detAbs, hd, map_one]; rfl

end GlobalTheory.RSnmUnfProps


open GroundTheory.Automorphic.FourierWhittaker (blockGL) in
theorem GlobalTheory.RSnmUnfProps.uIntNM_props : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (φ : GA E (m + r + 1 + 1) → ℂ) (φ' : GA E (m + 1) → ℂ) (F : (Fin (m + 1) → Ad E) → ℂ),
    Continuous (GlobalTheory.JSW.whit φ) → Continuous (GlobalTheory.JSW.whit φ') →
    (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + r + 1 + 1)), ∀ g, GlobalTheory.JSW.whit φ (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ g) →
    (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, GlobalTheory.JSW.whit φ' (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ' g) →
    Continuous (GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F) →
    Continuous (fun g : GA E (m + 1) => GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) g)) ∧
    Continuous (fun g : GA E (m + 1) => GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow g)) ∧
    (∀ x : ℝ, Measurable (GlobalTheory.RSnmUnf.uIntNM (by omega : m + 1 ≤ m + r + 1 + 1) F φ φ' x)) ∧
    (∀ u ∈ GlobalTheory.CellDec.NA E (m + 1), ∀ g : GA E (m + 1),
      ‖GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) (u * g))‖ = ‖GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) g)‖ ∧
      ‖GlobalTheory.JSW.whit φ' (u * g)‖ = ‖GlobalTheory.JSW.whit φ' g‖ ∧
      GlobalTheory.ZEul.lastRow (u * g) = GlobalTheory.ZEul.lastRow g ∧ GlobalTheory.RSnm.detAbs (u * g) = GlobalTheory.RSnm.detAbs g ∧
      ∀ x : ℝ, GlobalTheory.RSnmUnf.uIntNM (by omega : m + 1 ≤ m + r + 1 + 1) F φ φ' x (u * g) = GlobalTheory.RSnmUnf.uIntNM (by omega : m + 1 ≤ m + r + 1 + 1) F φ φ' x g) ∧
    ∀ (x : ℝ) (g : GA E (m + 1)), ‖GlobalTheory.RSnmUnf.uIntNM (by omega : m + 1 ≤ m + r + 1 + 1) F φ φ' x g‖ ≤
      (‖GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) g)‖ ^ 2 * ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow g)‖ * GlobalTheory.RSnm.detAbs g ^ (x - ((r : ℝ) + 1)) +
        ‖GlobalTheory.JSW.whit φ' g‖ ^ 2 * ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow g)‖ * GlobalTheory.RSnm.detAbs g ^ x) / 2 := by
  intro E _ _ _ m r S φ φ' F hW hW' hl hl' hF
  have hmn : m + 1 ≤ m + r + 1 + 1 := by omega
  have cW : Continuous (fun g : GA E (m + 1) => GlobalTheory.JSW.whit φ (blockGL hmn g)) :=
    hW.comp (GlobalTheory.RSnm.continuous_blockGL hmn)
  have cF : Continuous (fun g : GA E (m + 1) => GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow g)) :=
    hF.comp GlobalTheory.ZUnfTheta.continuous_lastRow
  have cD : ∀ y : ℂ, Continuous (fun g : GA E (m + 1) => ((GlobalTheory.RSnm.detAbs g : ℝ) : ℂ) ^ y) := fun y =>
    (Complex.continuous_ofReal.comp GlobalTheory.RSnm.continuous_detAbs).cpow continuous_const
      fun h => Complex.ofReal_mem_slitPlane.2 (GlobalTheory.RSnm.detAbs_pos h)
  have hwu : ∀ u ∈ GlobalTheory.CellDec.NA E (m + 1), ∀ g : GA E (m + 1),
      GlobalTheory.JSW.whit φ (blockGL hmn (u * g)) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ (blockGL hmn g) := by
    intro u hu g
    have hu' : u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)) := (GlobalTheory.SmGL.mem_unipB (Ad E)).1 hu
    rw [map_mul, hl _ (GlobalTheory.RSnmUnfProps.blockGL_mem_NA hmn hu'), GlobalTheory.RSnmUnfProps.psiN_blockGL]
  refine ⟨cW, cF, fun x => ?_, fun u hu g => ?_, fun x g => ?_⟩
  · unfold GlobalTheory.RSnmUnf.uIntNM
    exact (((cW.mul (Complex.continuous_conj.comp hW')).mul cF).mul (cD _)).measurable
  · have hu' : u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)) := (GlobalTheory.SmGL.mem_unipB (Ad E)).1 hu
    have hlr := GlobalTheory.ZEulProps.lastRow_unip hu g
    have hd : GlobalTheory.RSnm.detAbs (u * g) = GlobalTheory.RSnm.detAbs g := by
      rw [GlobalTheory.RSnm.detAbs_mul, GlobalTheory.RSnmUnfProps.detAbs_unip hu, one_mul]
    refine ⟨?_, ?_, hlr, hd, fun x => ?_⟩
    · rw [hwu u hu g, norm_mul, GlobalTheory.RSnmUnfProps.norm_psiN, one_mul]
    · rw [hl' u hu' g, norm_mul, GlobalTheory.RSnmUnfProps.norm_psiN, one_mul]
    · unfold GlobalTheory.RSnmUnf.uIntNM
      rw [hwu u hu g, hl' u hu' g, hlr, hd, map_mul]
      have h1 := GlobalTheory.ZEulProps.psiN_mul_conj u
      linear_combination (GlobalTheory.JSW.whit φ (blockGL hmn g) * conj (GlobalTheory.JSW.whit φ' g) *
        GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow g) *
        ((GlobalTheory.RSnm.detAbs g : ℝ) : ℂ) ^ ((x : ℂ) - (((m + r + 1 + 1 : ℕ) : ℂ) - ((m + 1 : ℕ) : ℂ)) / 2)) * h1

  · have hdp := GlobalTheory.RSnm.detAbs_pos g
    have hre : ((x : ℂ) - (((m + r + 1 + 1 : ℕ) : ℂ) - ((m + 1 : ℕ) : ℂ)) / 2).re = (x - ((r : ℝ) + 1)) / 2 + x / 2 := by
      push_cast
      simp only [Complex.sub_re, Complex.div_re, Complex.add_re, Complex.ofReal_re, Complex.natCast_re,
        Complex.one_re, Complex.natCast_im, Complex.one_im, Complex.add_im, Complex.ofReal_im]
      norm_num
      ring
    unfold GlobalTheory.RSnmUnf.uIntNM
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_cpow_eq_rpow_re_of_pos hdp, hre,
      Real.rpow_add hdp]
    have hA : GlobalTheory.RSnm.detAbs g ^ (x - ((r : ℝ) + 1)) = (GlobalTheory.RSnm.detAbs g ^ ((x - ((r : ℝ) + 1)) / 2)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hdp.le]; norm_num
    have hB : GlobalTheory.RSnm.detAbs g ^ x = (GlobalTheory.RSnm.detAbs g ^ (x / 2)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hdp.le]; norm_num
    rw [hA, hB]
    set a := ‖GlobalTheory.JSW.whit φ (blockGL hmn g)‖
    set b := ‖GlobalTheory.JSW.whit φ' g‖
    set c := ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow g)‖
    set α := GlobalTheory.RSnm.detAbs g ^ ((x - ((r : ℝ) + 1)) / 2)
    set β := GlobalTheory.RSnm.detAbs g ^ (x / 2)
    have hc : 0 ≤ c := norm_nonneg _
    nlinarith [mul_nonneg hc (sq_nonneg (a * α - b * β))]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNormRsHatLeConst
noncomputable section

open NumberField Matrix MeasureTheory Filter GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.ThetaPoisson GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped ComplexConjugate nonZeroDivisors ContDiff
open GlobalTheory.RSTheta GlobalTheory.ShortVecDecay GlobalTheory.Petersson GlobalTheory.CuspQuot Topology GroundTheory.Automorphic.GJMatrix GlobalTheory.RSThetaLow

namespace GlobalTheory.RSThetaLowM

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem mspanR_invT (π : CuspSub E a) {F : GA E a → ℂ} (hF : F ∈ GlobalTheory.JSW.mspanR π) :
    (fun g => F (invT a (Ad E) g)) ∈ GlobalTheory.JSW.mspanR π.contra :=
  GlobalTheory.T.inverseTranspose_mem_cuspFormRapidKernelSpan_contragredient E a π F hF

def rsm (π : CuspSub E a) : Submodule ℂ (Sm E a) := (GlobalTheory.JSW.mspanR π).comap (Sm E a).subtype

theorem lie_mem_rsm {π : CuspSub E a} (hπ : π.IsUnitary) (X : Lie E a) {F : Sm E a} (hF : F ∈ rsm π) :
    lie E a X F ∈ rsm π := by
  obtain ⟨ψ, hψ, hw, -⟩ := GlobalTheory.T.cuspFormRapidKernelSmoothSpan_smooth_cuspidal_bounded E a GlobalTheory.CuspOrth.cuspFormsBounded π hπ F.1 hF
  obtain rfl : ψ = F := Subtype.ext hψ
  simpa [GlobalTheory.GLFin.word, rsm] using hw [X]

theorem bounded_of_mem_rsm {π : CuspSub E a} (hπ : π.IsUnitary) {F : Sm E a} (hF : F ∈ rsm π) :
    ∃ C : ℝ, ∀ g, ‖F.1 g‖ ≤ C :=
  (GlobalTheory.T.cuspFormRapidKernelSmoothSpan_smooth_cuspidal_bounded E a GlobalTheory.CuspOrth.cuspFormsBounded π hπ F.1 hF).choose_spec.2.2.2

theorem decays_invT_of_mem_rsm {π : CuspSub E a} (hπ : π.IsUnitary) {F : Sm E a} (hF : F ∈ rsm π) :
    Decays fun g => F.1 (invT a (Ad E) g) := by
  obtain ⟨ψ, hψ, -, -⟩ := GlobalTheory.T.cuspFormRapidKernelSmoothSpan_smooth_cuspidal_bounded E a GlobalTheory.CuspOrth.cuspFormsBounded π.contra hπ.contra _ (mspanR_invT π hF)
  intro L hL C₀ hC₀ N
  obtain ⟨C, h⟩ := GlobalTheory.T.cuspFormSmoothSpan_norm_le_shortRationalVector E a π.contra hπ.contra ψ (Or.inr (hψ ▸ mspanR_invT π hF)) [] L hL C₀ hC₀ N
  refine ⟨C, fun g c hc ξ hξ hm => ?_⟩
  have := h g c hc ξ hξ hm
  simpa [GlobalTheory.GLFin.word, hψ] using this

variable {ℓ : Fin a} {Φ : (Fin a → Cinf E) → ℂ} (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E)
variable {π π' : CuspSub E a} {φ φ' : Sm E a}

theorem exists_norm_rsHat_le_const (hπ : π.IsUnitary) (hπ' : π'.IsUnitary) (hφ : φ ∈ rsm π)
    (hφ' : φ' ∈ rsm π') (hΦ : IsTest (rowSet E ℓ) Φ) :
    ∃ C : ℝ, ∀ g y, ‖rsHat ℓ φ.1 φ'.1 Φ J η g y‖ ≤ C := by
  obtain ⟨C, h⟩ := exists_norm_rsHat_le J η (g := id) (w := fun _ => 1) (fun X _ => lie_mem_rsm hπ X)
    (fun X _ => lie_mem_rsm hπ' X)
    (fun F hF _ _ => (bounded_of_mem_rsm hπ hF).imp fun C h _ _ _ => (h _).trans_eq (mul_one _).symm)
    (fun F hF => bounded_of_mem_rsm hπ' hF) hφ hφ' hΦ 0
  exact ⟨C, fun g y => by simpa using h g y⟩

theorem exists_tsum_norm_rsHat_le (hπ : π.IsUnitary) (hπ' : π'.IsUnitary) (hφ : φ ∈ rsm π)
    (hφ' : φ' ∈ rsm π') (hΦ : IsTest (rowSet E ℓ) Φ) (K : ℕ) : ∃ C : ℝ, ∀ g ∈ lowSet E a,
      ∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖rsHat ℓ φ.1 φ'.1 Φ J η g
        ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* (g⁻¹).valᵀ)‖ ≤
        C * (ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ K := by
  set N := K + Module.finrank ℝ (Fin a → Cinf E) with hN
  have had : 1 ≤ a * Module.finrank ℚ E := Nat.mul_pos ℓ.pos Module.finrank_pos
  obtain ⟨M, C₁, h₁⟩ := GlobalTheory.T.summable_nonzeroRationalVector_le_shortestVector E a (traceDualIdeal E J) (a * Module.finrank ℚ E * N)
    ((Nat.le_add_left _ K).trans (Nat.le_mul_of_pos_left _ had))
  obtain ⟨C₂, h₂⟩ := exists_norm_rsHat_le J η
    (ι := {p : GA E a × (Fin a → E) // p.2 ≠ 0 ∧
      (fun i => pFin E (((fun j => algebraMap E (Ad E) (p.2 j)) ᵥ* p.1.val) i)) ∈ latt a (traceDualIdeal E J)})
    (g := fun p => invT a (Ad E) p.1.1)
    (w := fun p => (‖fun i => pInf E (((fun j => algebraMap E (Ad E) (p.1.2 j)) ᵥ* p.1.1.val) i)‖ ^
      (a * Module.finrank ℚ E) / (ideleModule E (GeneralLinearGroup.det p.1.1) : ℝ)) ^ N)
    (fun X _ => lie_mem_rsm hπ X) (fun X _ => lie_mem_rsm hπ' X)
    (fun F hF C₀ hC₀ => (decays_invT_of_mem_rsm hπ hF _ (isCompact_latt _) _ (hC₀.image continuous_invT) N).imp
      fun C h p c hc => by simpa only [map_mul, invT_invT] using h p.1.1 _ ⟨c, hc, rfl⟩ p.1.2 p.2.1 p.2.2)
    (fun F hF => bounded_of_mem_rsm hπ' hF) hφ hφ' hΦ M
  refine ⟨|C₁| * |C₂|, fun g hg => ?_⟩
  set δ : ℝ := (ideleModule E (GeneralLinearGroup.det g) : ℝ) with hδ
  have hδ0 : 0 < δ := (ideleModule E _).2
  have h := (h₁ (invT a (Ad E) g) (|C₂| * δ ^ N)
    (fun ξ => rsHat ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* (g⁻¹).valᵀ)) (by positivity)
    (fun ξ hξ => by
      rw [rsHat_eq J η φ φ' hΦ]
      exact mul_eq_zero_of_left (mul_eq_zero_of_right _ (Set.indicator_of_notMem hξ _)) _)
    (fun ξ ξ' h0 hξ' => by
      have h3 := h₂ ⟨(invT a (Ad E) g, ξ'), h0, hξ'⟩ ((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* (g⁻¹).valᵀ)
      simp only [invT_invT, absDet_invT, ← hδ, div_inv_eq_mul, mul_pow, ← pow_mul] at h3
      refine h3.trans ?_
      rw [mul_assoc |C₂|, mul_comm (δ ^ N)]
      exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))).2
  refine h.trans ?_
  rw [mul_assoc]
  refine mul_le_mul (le_abs_self _) (mul_le_mul_of_nonneg_left
    (pow_le_pow_of_le_one hδ0.le hg (Nat.le_add_right _ _)) (abs_nonneg _)) (by positivity) (abs_nonneg _)

variable {μ : Measure (GA E a)} [μ.IsHaarMeasure] {𝓕 : Set (GA E a)}

theorem integrableOn_partA (hπ : π.IsUnitary) (hπ' : π'.IsUnitary) (hφ : φ ∈ rsm π)
    (hφ' : φ' ∈ rsm π') (hc : Continuous φ.1) (hc' : Continuous φ'.1) (hΦ : IsTest (rowSet E ℓ) Φ)
    (h𝓕 : IsFundamentalDomain (ratGL E a).range 𝓕 μ)
    {s : ℂ} (hs : 1 < s.re) : IntegrableOn (fun g => rsHat ℓ φ.1 φ'.1 Φ J η g 0 *
      ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (s - 1)) (𝓕 ∩ lowSet E a) μ := by
  obtain ⟨C, hC⟩ := exists_norm_rsHat_le_const J η hπ hπ' hφ hφ' hΦ
  refine ((GlobalTheory.T.integrableOn_absDet_rpow_le_one_fundamentalDomain E a ℓ.pos μ 𝓕 h𝓕 (s.re - 1) (by linarith)).const_mul C).mono'
    ((stronglyMeasurable_rsHat J η hc hc' hΦ continuous_const).aestronglyMeasurable.mul
      ((Complex.measurable_ofReal.comp GlobalTheory.RSThetaLow.continuous_absDet.measurable).pow_const _).aestronglyMeasurable)
    (.of_forall fun g => ?_)
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (ideleModule E _).2, Complex.sub_re, Complex.one_re]
  exact mul_le_mul_of_nonneg_right (hC g 0) (Real.rpow_nonneg (ideleModule E _).2.le _)

theorem partB_entire (hπ : π.IsUnitary) (hπ' : π'.IsUnitary) (hφ : φ ∈ rsm π)
    (hφ' : φ' ∈ rsm π') (hc : Continuous φ.1) (hc' : Continuous φ'.1) (hΦ : IsTest (rowSet E ℓ) Φ)
    (h𝓕 : IsFundamentalDomain (ratGL E a).range 𝓕 μ) :
    (∀ x : ℝ, IntegrableOn (fun g => (∑' ξ : {ξ : Fin a → E // ξ ≠ 0},
      ‖rsHat ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* (g⁻¹).valᵀ)‖) *
        (ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x - 1)) (𝓕 ∩ lowSet E a) μ) ∧
    (∀ s : ℂ, IntegrableOn (fun g => (∑' ξ : {ξ : Fin a → E // ξ ≠ 0},
      rsHat ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* (g⁻¹).valᵀ)) *
        ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (s - 1)) (𝓕 ∩ lowSet E a) μ) ∧
    Differentiable ℂ (partB ℓ φ.1 φ'.1 Φ J η μ 𝓕) := by
  haveI : Countable E := Finsupp.Countable.of_moduleFinite (R := ℚ)
  have hm : ∀ ξ : {ξ : Fin a → E // ξ ≠ 0}, AEStronglyMeasurable (fun g : GA E a =>
      rsHat ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* (g⁻¹).valᵀ)) (μ.restrict (𝓕 ∩ lowSet E a)) :=
    fun ξ => (stronglyMeasurable_rsHat J η hc hc' hΦ
      (continuous_const.matrix_vecMul Units.continuous_coe_inv.matrix_transpose)).aestronglyMeasurable
  have hlow : ∀ᵐ g ∂μ.restrict (𝓕 ∩ lowSet E a), g ∈ lowSet E a :=
    ae_restrict_of_ae_restrict_of_subset Set.inter_subset_right
      (ae_restrict_mem (isClosed_le GlobalTheory.RSThetaLow.continuous_absDet continuous_const).measurableSet)
  have hδ := hlow.mono (q := fun g => 0 < (ideleModule E (GeneralLinearGroup.det g) : ℝ) ∧
    (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1) fun g hg => ⟨(ideleModule E _).2, hg⟩
  have hi := GlobalTheory.T.integrableOn_absDet_rpow_le_one_fundamentalDomain E a ℓ.pos μ 𝓕 h𝓕 1 one_pos
  simp only [Real.rpow_one] at hi
  have hb := exists_tsum_norm_rsHat_le J η hπ hπ' hφ hφ' hΦ
  have h1 := GlobalTheory.T.mellin_integral_rapidDecay_entire_of_le_one _ _ _ _ GlobalTheory.RSThetaLow.continuous_absDet.measurable hδ hi (AEStronglyMeasurable.tsum hm) fun K =>
    (hb K).imp fun C h => hlow.mono fun g hg =>
      (norm_tsum_le_tsum_norm (poisson_rsPsi J η φ φ' hΦ g).2.1).trans (h g hg)
  have h2 := GlobalTheory.T.mellin_integral_rapidDecay_entire_of_le_one _ _ _ _ GlobalTheory.RSThetaLow.continuous_absDet.measurable hδ hi
    (Complex.continuous_ofReal.comp_aestronglyMeasurable (AEStronglyMeasurable.tsum fun ξ => (hm ξ).norm)) fun K =>
    (hb K).imp fun C h => hlow.mono fun g hg => by
      rw [Complex.norm_real, Real.norm_of_nonneg (tsum_nonneg fun _ => norm_nonneg _)]
      exact h g hg
  refine ⟨fun x => ((h2.1 ((x - 1 : ℝ) : ℂ)).norm).congr (.of_forall fun g => ?_), fun s => h1.1 _,
    h1.2.comp (differentiable_id.sub_const 1)⟩
  simp only [norm_mul, Complex.norm_real, Complex.norm_cpow_eq_rpow_re_of_pos (ideleModule E _).2, Complex.ofReal_re]
  rw [Real.norm_of_nonneg (tsum_nonneg fun _ => norm_nonneg _)]

theorem integral_low_eq (hπ : π.IsUnitary) (hπ' : π'.IsUnitary) (hφ : φ ∈ rsm π)
    (hφ' : φ' ∈ rsm π') (hc : Continuous φ.1) (hc' : Continuous φ'.1) (hΦ : IsTest (rowSet E ℓ) Φ)
    (h𝓕 : IsFundamentalDomain (ratGL E a).range 𝓕 μ) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun g => (∑' ξ : Fin a → E, rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val)) *
      ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ s) (𝓕 ∩ lowSet E a) μ ∧
    ∫ g in 𝓕 ∩ lowSet E a, (∑' ξ : Fin a → E, rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val)) *
      ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ s ∂μ =
      partA ℓ φ.1 φ'.1 Φ J η μ 𝓕 s + partB ℓ φ.1 φ'.1 Φ J η μ 𝓕 s := by
  have hA := integrableOn_partA J η hπ hπ' hφ hφ' hc hc' hΦ h𝓕 hs
  have hB := (partB_entire J η hπ hπ' hφ hφ' hc hc' hΦ h𝓕).2.1 s
  have e : ∀ g : GA E a, (∑' ξ : Fin a → E, rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val)) *
      ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ s =
      rsHat ℓ φ.1 φ'.1 Φ J η g 0 * ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (s - 1) +
      (∑' ξ : {ξ : Fin a → E // ξ ≠ 0},
        rsHat ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* (g⁻¹).valᵀ)) *
        ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (s - 1) := fun g => by
    rw [(poisson_rsPsi J η φ φ' hΦ g).2.2, Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.2 (ideleModule E _).2.ne'),
      Complex.cpow_one]
    ring
  simp only [e]
  exact ⟨hA.add hB, integral_add hA hB⟩

end GlobalTheory.RSThetaLowM
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilRepCentralActsByDilationUnit
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilRepCentralActsByDilationUnit
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.TupDil

theorem card_mem {E : Type} [Field E] [NumberField E] (PP : HeightOneSpectrum (𝓞 E)) :
    ((Nat.card (𝓞 E ⧸ PP.asIdeal) : ℕ) : 𝓞 E) ∈ PP.asIdeal := by
  have := Ideal.absNorm_mem PP.asIdeal
  rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply] at this

theorem card_ne_zero {E : Type} [Field E] [NumberField E] (PP : HeightOneSpectrum (𝓞 E)) :
    Nat.card (𝓞 E ⧸ PP.asIdeal) ≠ 0 := by
  have := (Ideal.absNorm_eq_zero_iff (I := PP.asIdeal)).not.2 PP.ne_bot
  rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply] at this

theorem om_model_eq_unit_smul_dilate : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t : T0), VStd D i → ∀ (eg eQ : AE D) (fg : WO (Vc D i) (Wc D i) → ℂ), IsIdemSum eg R.Pg → IsIdemSum eQ (R.Q t) → IsThetaAt R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) (cA D eg) (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) 1 (R.vacP i) (fun x => if IsHalf (cA D eg) x ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then omegaK R.Pg (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) else 0) fg → ∀ ϖ : 𝓞 D.host.E, ϖ ≠ 0 → (∀ PP ∈ R.Q t, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) → ∀ z : GA D (Vc D i), mt (Vc D i) z = Matrix.diagonal (fun _ => eQ * incA D ((ϖ : D.host.E)⁻¹) + cA D eQ * cA D (incA D (ϖ : D.host.E)) + (1 - eQ - cA D eQ)) → ∃ κ : ℂ, UnitOff (GlobalTheory.TwistField.tupPrime R t) κ ∧ ∀ (Tm : (WO (Vc D i) (Wc D i) → ℂ) →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ)), IsPlaceModel R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) eQ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) 1 fg Tm → ∀ Ψ : WO (Vc D i) (Wc D i) → ℂ, IsSBHalf eQ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) Ψ → R.ωP i t (z, 1) (Tm Ψ) = κ • Tm (fun x => Ψ (x.map fun w => incA D ((ϖ : D.host.E)⁻¹) * w)) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC hQG i t hV eg eQ fg heg heQ hfg ϖ hϖ0 hϖ z hz
  refine GlobalTheory.T.central_uniformiser_acts_by_dilation_tame_kernel D G Pl0 T0 A Ks R F hC hQG i hV _ _ _ _ _ _ (GlobalTheory.OnCmp.kerDat_tuple hC.lev hC.thP t)
    ⟨t, subset_rfl⟩ _ ?_ ?_ eg eQ fg heg heQ hfg ϖ (by exact_mod_cast hϖ0) hϖ z hz
  · refine Finset.prod_ne_zero_iff.2 fun q hq => ?_
    obtain ⟨PP, -, rfl⟩ := Finset.mem_image.1 hq
    exact card_ne_zero PP
  · intro PP hPP
    obtain ⟨c, hc⟩ : Nat.card (kP PP) ∣ GlobalTheory.TwistField.tupPrime R t :=
      Finset.dvd_prod_of_mem (fun q : ℕ => q) (Finset.mem_image_of_mem (fun PP => Nat.card (kP PP)) hPP)
    rw [hc, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (card_mem PP)

end GlobalTheory.TupDil
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilRepCentralActsByDilationUnitStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRep_central_acts_by_dilation_unit : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t : T0), VStd D i → ∀ (eg eQ : AE D) (fg : WO (Vc D i) (Wc D i) → ℂ), IsIdemSum eg R.Pg → IsIdemSum eQ (R.Q t) → IsThetaAt R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) (cA D eg) (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) 1 (R.vacP i) (fun x => if IsHalf (cA D eg) x ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then omegaK R.Pg (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) else 0) fg → ∀ ϖ : 𝓞 D.host.E, ϖ ≠ 0 → (∀ PP ∈ R.Q t, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) → ∀ z : GA D (Vc D i), mt (Vc D i) z = Matrix.diagonal (fun _ => eQ * incA D ((ϖ : D.host.E)⁻¹) + cA D eQ * cA D (incA D (ϖ : D.host.E)) + (1 - eQ - cA D eQ)) → ∃ κ : ℂ, UnitOff (GlobalTheory.TwistField.tupPrime R t) κ ∧ ∀ (Tm : (WO (Vc D i) (Wc D i) → ℂ) →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ)), IsPlaceModel R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) eQ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) 1 fg Tm → ∀ Ψ : WO (Vc D i) (Wc D i) → ℂ, IsSBHalf eQ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) Ψ → R.ωP i t (z, 1) (Tm Ψ) = κ • Tm (fun x => Ψ (x.map fun w => incA D ((ϖ : D.host.E)⁻¹) * w)) := by
  first | exact @GlobalTheory.TupDil.om_model_eq_unit_smul_dilate | exact GlobalTheory.TupDil.om_model_eq_unit_smul_dilate | (intros; apply GlobalTheory.TupDil.om_model_eq_unit_smul_dilate <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetIntegralRsHatZero
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped nonZeroDivisors

open GlobalTheory.RSTheta GlobalTheory.ThetaPoisson GlobalTheory.RSThetaLow GroundTheory.Automorphic.GJMatrix GroundTheory.Global
open scoped ComplexConjugate

noncomputable section

namespace GlobalTheory.RSResidue

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem rsHat_zero {ℓ : Fin a} {Φ : (Fin a → Cinf E) → ℂ} (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E)
    (F F' : Sm E a) (hΦ : GlobalTheory.CuspQuot.IsTest (rowSet E ℓ) Φ) (g : GA E a) :
    adelicFourierPi E (rsPsi ℓ F.1 F'.1 Φ J η g) 0 =
      (∫ x, rsInf ℓ F.1 F'.1 Φ g x ∂infMeasure E a) * ((finiteMeasurePi E (latt a J)).toReal : ℂ) := by
  have h := rsHat_eq J η F F' hΦ g 0
  simp only [rsHat] at h
  rw [h]
  have h0 : (fun i => pFin E ((0 : Fin a → Ad E) i)) = 0 := funext fun _ => map_zero _
  have h1 : (fun i => pInf E ((0 : Fin a → Ad E) i)) = 0 := funext fun _ => map_zero _
  have h2 : (latt a (traceDualIdeal E J)).indicator (1 : (Fin a → Af E) → ℂ) 0 = 1 :=
    Set.indicator_of_mem (s := latt a (traceDualIdeal E J)) (show (0 : Fin a → Af E) ∈ latt a (traceDualIdeal E J) from
      fun i => (idealFiniteAdeles (traceDualIdeal E J)).zero_mem) _
  rw [h0, h1, h2]
  simp [infFourier]

theorem setIntegral_mul_right {μ : Measure (GA E a)} [μ.IsHaarMeasure] {𝓕 : Set (GA E a)}
    (h𝓕 : IsFundamentalDomain (latticeGL E a) 𝓕 μ) {f : GA E a → ℂ}
    (hf : ∀ γ ∈ latticeGL E a, ∀ g, f (γ * g) = f g) (h : GA E a) :
    ∫ g in 𝓕, f (g * h) ∂μ = ∫ g in 𝓕, f g ∂μ := by
  haveI := GlobalTheory.CovolGL.isMulRightInvariant E a μ
  have hmp : MeasurePreserving (fun g => g * h) μ μ := measurePreserving_mul_right μ h
  have e1 := hmp.setIntegral_preimage_emb (measurableEmbedding_mulRight h) f ((fun g => g * h⁻¹) ⁻¹' 𝓕)
  have e2 : (fun g => g * h) ⁻¹' ((fun g => g * h⁻¹) ⁻¹' 𝓕) = 𝓕 := by ext; simp
  rw [e2] at e1
  rw [e1]
  have h2 : IsFundamentalDomain (latticeGL E a) ((fun g => g * h⁻¹) ⁻¹' 𝓕) μ :=
    h𝓕.preimage_of_equiv (measurePreserving_mul_right μ h⁻¹).quasiMeasurePreserving (e := id)
      Function.bijective_id (fun γ x => by simp [Subgroup.smul_def, mul_assoc])
  haveI : DiscreteTopology (latticeGL E a) := GlobalTheory.CuspRep.CuspidalL2GL.discreteTopology_latticeGL
  haveI : SecondCountableTopology (GA E a) := GlobalTheory.CuspRep.CuspidalL2GL.secondCountableTopology_GA E a
  have hI : GlobalTheory.AutomorphicL2Unitary.LeftInv (latticeGL E a) f := hf
  have A := (GlobalTheory.AutomorphicL2Unitary.integral_quotMeasure h2 (GlobalTheory.AutomorphicL2Unitary.descend (latticeGL E a) f)).trans
    (integral_congr_ae (Eventually.of_forall hI.descend_mk))
  have B := (GlobalTheory.AutomorphicL2Unitary.integral_quotMeasure h𝓕 (GlobalTheory.AutomorphicL2Unitary.descend (latticeGL E a) f)).trans
    (integral_congr_ae (Eventually.of_forall hI.descend_mk))
  exact A.symm.trans B

end GlobalTheory.RSResidue
end
end
