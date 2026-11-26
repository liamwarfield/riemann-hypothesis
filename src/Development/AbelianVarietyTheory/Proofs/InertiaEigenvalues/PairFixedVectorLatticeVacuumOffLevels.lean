module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilMatrixCoefficientVacuaUnramifiedPlace
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormLinearRelationDefinedOverCoreField
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValRingLocRing
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HeckePin
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelStandardCharacter

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PairFixedVectorLatticeVacuumOffLevels
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PairFixedVectorLatticeVacuumOffLevels
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

theorem GlobalTheory.RawLift.vacFin_off : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ (i : Fin D.R.m) (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (f : AE D), IsFinIdem D v f → (∀ P, P ∈ R.Pg ∨ P ∈ R.Q t → ∀ e f', IsPrimeIdem P e f' → f' ≠ f) → GlobalTheory.FinZeta.VacFin R.ψ (Vc D i) (Wc D i) v (R.vP i t) := by
  classical
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL i t v f hf hoffP
  have hth : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) := by
    have := hL.thP.pt_theta i t 1
    unfold RealDat.ptP pureTensorO at this
    rwa [GlobalTheory.AdTh.VecFock.pureTensorL_one] at this
  refine ⟨hth, ?_⟩
  obtain ⟨hf₀, e, he, hthA⟩ := hL.thP.vP i t
  obtain ⟨ε, hε, rfl⟩ := hf
  have hoff : ∀ PP ∈ R.Pg ∪ R.Q t, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ v := by
    intro PP hPP h0
    obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
    obtain ⟨e', f', hp⟩ := GlobalTheory.IdemSupport.exists_isPrimeIdem hΦ PP
    obtain ⟨w, ε', hε', hf', hw⟩ := GlobalTheory.VacLat.place_of_primeIdem hp
    refine hoffP PP (Finset.mem_union.1 hPP) e' f' hp ?_
    rw [h0] at hw
    subst hw
    rw [hf', GlobalTheory.IdemSupport.placeIdem_unique hε' hε]
  have hV : (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E)) = (GlobalTheory.AdelicU.frameLat (Vc D i) : Set _) := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.StandardHermitianSpace.baseLat_eq hL.lev i, GlobalTheory.AdelicU.hermitianSpaceBaseLattice_eq_frameLattice]
  have hW : (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) = (GlobalTheory.AdelicU.frameLat (Wc D i) : Set _) := by
    rw [← GlobalTheory.AdelicU.hermitianSpaceBaseLattice_eq_frameLattice]
    obtain ⟨c, -, -, -, h1, h2⟩ := hL.lev.βW i
    ext x
    constructor
    · intro hx
      simpa using h2 x hx
    · intro hx
      simpa using h1 x hx
  have hlat := hf₀.2.lat
  have hle : latO (Vc D i) (Wc D i) (GlobalTheory.AdelicU.frameLat (Vc D i) : Set _) (GlobalTheory.AdelicU.frameLat (Wc D i) : Set _) (fun u => u = v) ≤
      latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True := by
    rw [hV, hW]
    exact GlobalTheory.PlaceTensor.latO_mono fun _ _ => trivial
  have hz : ∀ u ∈ latO (Vc D i) (Wc D i) (GlobalTheory.AdelicU.frameLat (Vc D i) : Set _) (GlobalTheory.AdelicU.frameLat (Wc D i) : Set _) (fun u => u = v),
      ∀ a b, cA D e * u a b = 0 ∧ cA D (cA D e) * u a b = 0 := fun u hu a b => by
    obtain ⟨h1, h2⟩ := GlobalTheory.FinZeta.VacOff.idemSum_mul_off he hoff hu a b
    rw [GlobalTheory.DualPairCheck.cA_cA]
    exact ⟨h2, h1⟩
  refine ⟨fun u hu => ?_, fun e' he' u hu hh => ?_⟩
  · exact GlobalTheory.Hk3.heisO_fix_thetaAt_off R.ψ _ _ _ _ _ _ _ _ hthA (2 • u)
      (hz _ (AddSubgroup.nsmul_mem _ hu 2)) (hlat.1 u (hle hu))
  · exact GlobalTheory.Hk3.heisO_fix_thetaAt_off R.ψ _ _ _ _ _ _ _ _ hthA u (hz u hu) (hlat.2 e' he' u (hle hu) hh)

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PairFixedVectorLatticeVacuumOffLevelsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairFixedVector_latticeVacuum_offLevels : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ (i : Fin D.R.m) (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (f : AE D), IsFinIdem D v f → (∀ P, P ∈ R.Pg ∨ P ∈ R.Q t → ∀ e f', IsPrimeIdem P e f' → f' ≠ f) → GlobalTheory.FinZeta.VacFin R.ψ (Vc D i) (Wc D i) v (R.vP i t) := by
  first | exact @GlobalTheory.RawLift.vacFin_off | exact GlobalTheory.RawLift.vacFin_off | (intros; apply GlobalTheory.RawLift.vacFin_off <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormReadingGaloisConjExpansion
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormReadingGaloisConjExpansion
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.ConjExpand

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}


set_option maxHeartbeats 1000000 in
theorem read_of_isBC (M : OMDat C R i Tp tup) (hact : ActLev (Xo := C.Q.Xo ((i : ℕ) + 1)) C.Q.c M.lev2)
    (cc : (C.U ((i : ℕ) + 1) M.s0).Comp → ℂ) (L : ℂ) (z : G) {a : (D.host.E →+* ℂ) × ℕ → ℕ} {n m : ℕ}
    {f : Rul (C.Q.Xo ((i : ℕ) + 1)) M.c'} (hf : f ∈ sec _ M.c' a n) {as : Fin m → M.c'.F}
    {fs : Fin m → Rul (C.Q.Xo ((i : ℕ) + 1)) C.Q.c} (hfs : ∀ k, fs k ∈ sec _ C.Q.c a n) (h : IsBC M.hle f as fs)
    (g : GA D (Wc D i)) :
    cc (M.dict g).1 * L * M.mu g * rdU (unfBC M.hle (C.U ((i : ℕ) + 1)) (inC M.c')) (actLev M.c' M.lev2 z f) (M.dict g).1 (M.dict g).2 =
      ∑ k, (as k : ℂ) * (L * M.phi cc (actLev C.Q.c M.lev2 z (fs k)) g) := by
  have h1 := (GlobalTheory.FieldBC.actLev_and_actBC _ _ _ _ _ _ _ M.hle _ _ hact).2 a n z m as fs f hf hfs h
  have h2 := congrFun (congrFun (rdU_unfBC M.hle (C.U ((i : ℕ) + 1)) (inC M.c') h1) (M.dict g).1) (M.dict g).2
  rw [Finset.sum_apply, Finset.sum_apply] at h2
  refine (congrArg (fun w => cc (M.dict g).1 * L * M.mu g * w) h2).trans ?_
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  show cc _ * L * M.mu _ * ((as k : ℂ) * _) = (as k : ℂ) * (L * (cc _ * M.mu _ * _))
  ring

end GlobalTheory.ConjExpand


set_option maxHeartbeats 4000000 in
theorem GlobalTheory.ConjExpand.conjFun_galRul : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (τ : ℂ ≃+* ℂ) (ta : M.c'.F ≃+* M.c'.F), (∀ a : M.c'.F, ((ta a : M.c'.F) : ℂ) = τ (a : ℂ)) → FixBase T R i τ → ∀ (hf : Fixes M.c' ta) (z : G), ∀ f ∈ cusp (T.Q.Xo ((i : ℕ) + 1)) M.c' (unfBC M.hle (T.U ((i : ℕ) + 1))) (wtA (κ i)) (Vc D i).rank, M.EquivAt (κ i) (T.cE ((i : ℕ) + 1) M.s0) → ConjFun M (κ i) τ 1 (fun g => T.cE ((i : ℕ) + 1) M.s0 (M.dict g).1 * (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) * M.mu g * rdU (unfBC M.hle (T.U ((i : ℕ) + 1)) (inC M.c')) (actLev M.c' M.lev2 z f) (M.dict g).1 (M.dict g).2) (fun g => T.cE ((i : ℕ) + 1) M.s0 (M.dict g).1 * (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) * M.mu g * rdU (unfBC M.hle (T.U ((i : ℕ) + 1)) (inC M.c')) (actLev M.c' M.lev2 z (galRul hf f)) (M.dict g).1 (M.dict g).2) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hC hT i Tp tup M hP τ ta hta hB hf z f hfc hE
  have hact := hP.act.1
  obtain ⟨ht⟩ := id hT
  have hn : (κ i).n = (Vc D i).rank :=
    (ht.kap i (D.eTau.symm 1)).2.2.trans (D.sp.V_rank _ (Nat.le_add_left _ _) i.2).symm
  obtain ⟨m, as, fs, hfs, hBC⟩ := (GlobalTheory.FieldBC.secBC_and_cuspBC _ _ _ _ _ _ _ M.hle).2 _ (T.U ((i : ℕ) + 1)) _ _ f hfc
  have hsec := ((mem_cusp _ _ _ _ _ _).1 hfc).1
  have hs : ∀ k, fs k ∈ sec _ T.Q.c (wtA (κ i)) (Vc D i).rank := fun k => ((mem_cusp _ _ _ _ _ _).1 (hfs k)).1
  have hgal := GlobalTheory.GalTw.galRul_sec_val_semilinear _ _ (T.Q.Dw ((i : ℕ) + 1)) _ (T.Q.Xo ((i : ℕ) + 1)) M.c' ta hf
  have hFix : ∀ x : T.Q.c.F, ta (incF T.Q.c M.c' M.hle x) = incF T.Q.c M.c' M.hle x := by
    intro x
    apply Subtype.ext
    rw [hta]
    exact hB.core x
  have hgsec := ((hgal.1 _ _ f hsec).1)
  have hgBC := hgal.2.2 T.Q.c M.hle hFix _ _ m as fs f hsec hBC
  have hkeep : ∀ k, actLev T.Q.c M.lev2 z (fs k) ∈ T.toCore.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n := by
    intro k
    obtain ⟨y, hy, -⟩ := hP.lift.lev z
    refine (hE z y hy (fs k) ?_).1
    rw [hn]
    exact hfs k
  obtain ⟨Fk, hFk⟩ : ∃ Fk : Fin m → T.toCore.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n,
      ∀ k, (Fk k : T.toCore.R ((i : ℕ) + 1)) = actLev T.Q.c M.lev2 z (fs k) := ⟨fun k => ⟨_, hkeep k⟩, fun _ => rfl⟩
  have e1 := fun g => GlobalTheory.ConjExpand.read_of_isBC M hact (T.cE ((i : ℕ) + 1) M.s0) (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) z hsec hs hBC g
  have e2 := fun g => GlobalTheory.ConjExpand.read_of_isBC M hact (T.cE ((i : ℕ) + 1) M.s0) (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) z hgsec hs hgBC g
  simp only [← hFk] at e1 e2
  refine ⟨⟨m, fun k => (as k : ℂ), Fk, fun g => e1 g⟩, ?_⟩
  intro n a h hex g
  have hz : Expands M (κ i) (fun _ => 0) (Fin.append a (fun k => -(as k : ℂ))) (Fin.append h Fk) := by
    intro g
    have h0 := (e1 g).symm.trans (hex g)
    show (0 : ℂ) = _
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, neg_mul, Finset.sum_neg_distrib]
    linear_combination h0
  have hz' : (0 : ℂ) = _ := GlobalTheory.T.cuspForm_linear_relation_defined_over_core_field D G Pl0 T0 A T R F κ v₀ hC hT i Tp tup M hP τ hB.core _ _ _ hz g
  rw [Fin.sum_univ_add] at hz'
  simp only [Fin.append_left, Fin.append_right, map_neg, neg_mul, Finset.sum_neg_distrib] at hz'
  refine (e2 g).trans ?_
  simp only [one_mul, hta]
  linear_combination hz'
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormReadingGaloisConjExpansionStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspFormReading_galoisConj_expansion : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (τ : ℂ ≃+* ℂ) (ta : M.c'.F ≃+* M.c'.F), (∀ a : M.c'.F, ((ta a : M.c'.F) : ℂ) = τ (a : ℂ)) → FixBase T R i τ → ∀ (hf : Fixes M.c' ta) (z : G), ∀ f ∈ cusp (T.Q.Xo ((i : ℕ) + 1)) M.c' (unfBC M.hle (T.U ((i : ℕ) + 1))) (wtA (κ i)) (Vc D i).rank, M.EquivAt (κ i) (T.cE ((i : ℕ) + 1) M.s0) → ConjFun M (κ i) τ 1 (fun g => T.cE ((i : ℕ) + 1) M.s0 (M.dict g).1 * (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) * M.mu g * rdU (unfBC M.hle (T.U ((i : ℕ) + 1)) (inC M.c')) (actLev M.c' M.lev2 z f) (M.dict g).1 (M.dict g).2) (fun g => T.cE ((i : ℕ) + 1) M.s0 (M.dict g).1 * (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) * M.mu g * rdU (unfBC M.hle (T.U ((i : ℕ) + 1)) (inC M.c')) (actLev M.c' M.lev2 z (galRul hf f)) (M.dict g).1 (M.dict g).2) := by
  first | exact @GlobalTheory.ConjExpand.conjFun_galRul | exact GlobalTheory.ConjExpand.conjFun_galRul | (intros; apply GlobalTheory.ConjExpand.conjFun_galRul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasDerivAtFockVectorTargetLieOneParam
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasDerivAtFockVectorTargetLieOneParam
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.ExportSeries GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes

namespace GlobalTheory.FockDerivP

def frONB {D : D7} {V : HSp D} (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (hB : ∀ τ, IsONBasis (gramAt D V τ) 1 (B τ) V.rank) : GlobalTheory.ChainFr.Fr V where
  ε _ _ := true
  fr τ := (B τ)⁻¹
  fr_unit τ := (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_nonsing_inv_det _
    ((Matrix.isUnit_iff_isUnit_det _).1 (GlobalTheory.ConjTwist.isUnit_of_isONBasis (hB τ))))
  fr_gram τ := by
    have hu : IsUnit (B τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (GlobalTheory.ConjTwist.isUnit_of_isONBasis (hB τ))
    obtain ⟨ε, hε, hG, -⟩ := hB τ
    have h1 : (fun a => (ε a : ℂ)) = fun _ => 1 := by
      funext a
      rcases hε a with h | h
      · rw [h.1]; simp
      · exact absurd h.2 (not_le.2 a.2)
    rw [h1, Matrix.diagonal_one] at hG
    have hJ : Formalism.REAL.Jm (fun _ : Fin V.rank => true) = 1 := by
      simp [Formalism.REAL.Jm]
    have h2 : ((B τ)⁻¹)ᴴ * (B τ)ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hu, Matrix.conjTranspose_one]
    calc ((B τ)⁻¹)ᴴ * Formalism.REAL.Jm (fun _ : Fin V.rank => true) * (B τ)⁻¹
        = ((B τ)⁻¹)ᴴ * ((B τ)ᴴ * gramAt D V τ * B τ) * (B τ)⁻¹ := by rw [hJ, hG]
      _ = (((B τ)⁻¹)ᴴ * (B τ)ᴴ) * gramAt D V τ * (B τ * (B τ)⁻¹) := by simp only [Matrix.mul_assoc]
      _ = gramAt D V τ := by rw [h2, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul, Matrix.mul_one]

theorem frONB_cart {D : D7} {V : HSp D} (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (hB : ∀ τ, IsONBasis (gramAt D V τ) 1 (B τ) V.rank) : (frONB B hB).cart = fun _ => 1 := by
  funext τ
  have hu : IsUnit (B τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (GlobalTheory.ConjTwist.isUnit_of_isONBasis (hB τ))
  have hJ : Formalism.REAL.Jm (fun _ : Fin V.rank => true) = 1 := by
    simp [Formalism.REAL.Jm]
  show ((B τ)⁻¹)⁻¹ * Formalism.REAL.Jm (fun _ : Fin V.rank => true) * (B τ)⁻¹ = 1
  rw [hJ, Matrix.mul_one, Matrix.nonsing_inv_nonsing_inv _ hu, Matrix.mul_nonsing_inv _ hu]

theorem frONB_onb {D : D7} {V : HSp D} (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (hB : ∀ τ, IsONBasis (gramAt D V τ) 1 (B τ) V.rank) : (frONB B hB).onb = B := by
  funext τ
  have hu : IsUnit (B τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (GlobalTheory.ConjTwist.isUnit_of_isONBasis (hB τ))
  show ((B τ)⁻¹)⁻¹ = B τ
  rw [Matrix.nonsing_inv_nonsing_inv _ hu]

theorem hasDerivAt_ptP : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (τ : D.what₂.Tau) (Y : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ), Y ∈ lieAt (Wc D i) τ → ∃ a : ℂ, ∀ (P : PolF D (Wc D i).rank (Vc D i).rank) (z : WO (Vc D i) (Wc D i)), HasDerivAt (fun s : ℝ => R.ωP i t (1, oneP R.θ (Wc D i) τ Y s) (R.ptP i t P) z) (R.ptP i t (fockT τ (fun _ : Fin (Vc D i).rank => true) (fun j : Fin (Wc D i).rank => decide ((j : ℕ) < pS D i τ)) ((R.MW i (sg0 D A)).fr τ * Y * ((R.MW i (sg0 D A)).fr τ)⁻¹) P + a • P) z) 0 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG _ i t τ Y hY
  have hC := hG.core
  have hB := hC.models.BV i
  set AV := frONB (R.BV i) hB with hAV
  set BW := GlobalTheory.ChainFr.Fr.ofModel (R.MW i (sg0 D A)) with hBW
  have hcA := frONB_cart (R.BV i) hB
  have hoA := frONB_onb (R.BV i) hB
  obtain ⟨hf, hv, -⟩ := GlobalTheory.CoefActIo.thetaVector_laws (i := i) hC t
  have hvac : GlobalTheory.ChainFr.IsVacF R.ψ R.θ AV BW (R.vP i t) := by
    refine ⟨hf, fun ρ => ?_⟩
    rw [hcA]
    exact hv ρ
  have hI := GlobalTheory.PairInfTypes.infTypesAt D T R.toLevCh A.μ0 hC.lev i t τ
  have hAll := GlobalTheory.LieScalar.lieFockAll D (Vc D i) (Wc D i) AV BW R.θ R.ψ _ _ (R.ωP i t) (R.vP i t) τ _ _
    hC.models.inf (hC.thP.ωP i t) hI.chiV hI.chiW hvac
  refine ⟨((-eS D i τ : ℚ) : ℂ) * Y.trace, fun P z => ?_⟩
  have hpt : GlobalTheory.ChainFr.ptF R.ψ R.θ AV BW (R.vP i t) = R.ptP i t := by
    unfold GlobalTheory.ChainFr.ptF RealDat.ptP
    rw [hcA, hoA]
    rfl
  have hε : BW.ε τ = fun j : Fin (Wc D i).rank => decide ((j : ℕ) < pS D i τ) := by
    funext j
    exact hC.models.order i τ j
  have h := hAll.2 Y hY P z
  rw [hpt, hε] at h
  exact h

end GlobalTheory.FockDerivP

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasDerivAtFockVectorTargetLieOneParamStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.ExportSeries GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDerivAt_fockVector_targetLieOneParam : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (τ : D.what₂.Tau) (Y : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ), Y ∈ lieAt (Wc D i) τ → ∃ a : ℂ, ∀ (P : PolF D (Wc D i).rank (Vc D i).rank) (z : WO (Vc D i) (Wc D i)), HasDerivAt (fun s : ℝ => R.ωP i t (1, oneP R.θ (Wc D i) τ Y s) (R.ptP i t P) z) (R.ptP i t (fockT τ (fun _ : Fin (Vc D i).rank => true) (fun j : Fin (Wc D i).rank => decide ((j : ℕ) < pS D i τ)) ((R.MW i (sg0 D A)).fr τ * Y * ((R.MW i (sg0 D A)).fr τ)⁻¹) P + a • P) z) 0 := by
  first | exact @GlobalTheory.FockDerivP.hasDerivAt_ptP | exact GlobalTheory.FockDerivP.hasDerivAt_ptP | (intros; apply GlobalTheory.FockDerivP.hasDerivAt_ptP <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComplexPrincipalLevelEqRealisationPrincipalLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComplexPrincipalLevelEqRealisationPrincipalLevel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.Lev Formalism.L2.DIV Formalism.IndefR.Mult
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SeriesTie.LevKProof

variable {D : D7}

theorem blkOf_zero_of_le {n r t : ℕ} (h : n ≤ r) : (blkOf r t : Fin n → ℕ) = fun _ => 0 := by
  funext a
  have := a.2
  simp only [blkOf]
  rw [if_pos (by omega)]

theorem secondBlockIndex_eq_zero_of_dim_le {n r : ℕ} (h : n ≤ r) : (blk2 r : Fin n → ℕ) = fun _ => 0 := by
  funext a
  have := a.2
  simp only [blk2]
  rw [if_pos (by omega)]

theorem mem_blockTriangular_singleBlock_of_le {n r : ℕ} {κ : Type} [CommRing κ] (h : n ≤ r) (g : GL (Fin n) κ) :
    g ∈ blockTri (blk2 r) := by
  intro i k hik
  rw [secondBlockIndex_eq_zero_of_dim_le h] at hik
  exact absurd hik (lt_irrefl _)

end GlobalTheory.SeriesTie.LevKProof

namespace GlobalTheory.SeriesTie


open LevKProof in
theorem levK_eq_levG_triv : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks) {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {ρ : Setup D.ntw}, RealPin Rl cG ρ → ∀ (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool), ρ.levK i j b = levG (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv) := by
  intro D Γ _ _ Pl0 I0 T A3 Ks _ _ _ Rl cG ρ hp i j b
  unfold Setup.levK levG
  rw [hp.frT]
  congr 1
  have hr : (Wc D j).rank ≤ D.R.r := (FWT.rank_Wc j).le
  have hpar : parLev D.sp.cm (Wc D j).gram (Rl.βW j) (flag1L (ρ.B i j b).G.levT) =
      parLev D.sp.cm (Wc D j).gram (Rl.βW j) (Rl.datWp j Rl.triv) := by
    unfold parLev
    have hP : (flag1L (ρ.B i j b).G.levT).Pg = (Rl.datWp j Rl.triv).Pg := hp.Pg i j b
    have hb : (blkOf (flag1L (ρ.B i j b).G.levT).r (flag1L (ρ.B i j b).G.levT).t : Fin (Wc D j).rank → ℕ) =
        blkOf (Rl.datWp j Rl.triv).r (Rl.datWp j Rl.triv).t :=
      (blkOf_zero_of_le le_rfl).trans (blkOf_zero_of_le hr).symm
    have hb2 : (blk2 (flag1L (ρ.B i j b).G.levT).r : Fin (Wc D j).rank → ℕ) = blk2 (Rl.datWp j Rl.triv).r :=
      (secondBlockIndex_eq_zero_of_dim_le le_rfl).trans (secondBlockIndex_eq_zero_of_dim_le hr).symm
    rw [hP, hb, hb2]
    rfl
  have h1 : (flag1L (ρ.B i j b).G.levT).P.H = ⊥ := rfl
  have h2 : (Rl.datWp j Rl.triv).P.H = ⊥ := rfl

  have key : ∀ (x : GL (Fin (Wc D j).rank) (Lev.EAf D)) (PP : Pl D.host.E) (e1 : PP ∈ (flag1L (ρ.B i j b).G.levT).Pg)
      (e2 : PP ∈ (Rl.datWp j Rl.triv).Pg) (a c : Fin (Wc D j).rank),
      (rTup (Rl.βW j) (flag1L (ρ.B i j b).G.levT) x ⟨PP, e1⟩).val a c =
        (rTup (Rl.βW j) (Rl.datWp j Rl.triv) x ⟨PP, e2⟩).val
          (Fin.cast (FWT.rank_Wc j) a) (Fin.cast (FWT.rank_Wc j) c) := by
    intro x PP e1 e2 a c
    unfold rTup
    erw [upper_block_val_submatrix _ (mem_blockTriangular_singleBlock_of_le hr _), upper_block_val_submatrix _ (mem_blockTriangular_singleBlock_of_le le_rfl _)]
    rfl
  have hiff : ∀ x : GL (Fin (Wc D j).rank) (Lev.EAf D),
      rTup (Rl.βW j) (flag1L (ρ.B i j b).G.levT) x = 1 ↔ rTup (Rl.βW j) (Rl.datWp j Rl.triv) x = 1 := by
    intro x
    constructor
    · intro h
      funext PP
      apply Units.ext
      ext a c
      have e1 : PP.1 ∈ (flag1L (ρ.B i j b).G.levT).Pg := by
        show PP.1 ∈ (ρ.B i j b).G.Pg
        rw [hp.Pg i j b]
        exact PP.2
      have hk := key x PP.1 e1 PP.2 (Fin.cast (FWT.rank_Wc j).symm a) (Fin.cast (FWT.rank_Wc j).symm c)
      rw [h] at hk
      refine hk.symm.trans ?_
      simp [Matrix.one_apply, Fin.ext_iff]
      erw [Matrix.one_apply]
      simp [Fin.ext_iff]
      rfl
    · intro h
      funext PP
      apply Units.ext
      ext a c
      have e2 : PP.1 ∈ (Rl.datWp j Rl.triv).Pg := by
        show PP.1 ∈ Rl.Pg
        rw [← hp.Pg i j b]
        exact PP.2
      have hk := key x PP.1 PP.2 e2 a c
      rw [h] at hk
      refine hk.trans ?_
      simp [Matrix.one_apply, Fin.ext_iff]
      rfl
  ext x
  change (x ∈ parLev _ _ _ _ ∧ rTup _ _ x ∈ _) ↔ (x ∈ parLev _ _ _ _ ∧ rTup _ _ x ∈ _)
  rw [hpar, h1, h2, Subgroup.mem_bot, Subgroup.mem_bot, hiff]

end GlobalTheory.SeriesTie
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComplexPrincipalLevelEqRealisationPrincipalLevelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.Lev Formalism.L2.DIV Formalism.IndefR.Mult
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complex_principal_level_eq_realisation_principal_level : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks) {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {ρ : Setup D.ntw}, RealPin Rl cG ρ → ∀ (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool), ρ.levK i j b = levG (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv) := by
  first | exact @GlobalTheory.SeriesTie.levK_eq_levG_triv | exact GlobalTheory.SeriesTie.levK_eq_levG_triv | (intros; apply GlobalTheory.SeriesTie.levK_eq_levG_triv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UniversalCharSpreadCommutesWithRestriction
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UniversalCharSpreadCommutesWithRestriction
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SpreadRestrict

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
  {Y : NExp D.R D.host D.what₂ D.LL0 N X}

theorem surj_conj {B : Type} [CommGroup B] (χ : G D.host.E N.Om →* B) (hA : AntiHom X.cc χ)
    {P P' : PlE D.host} (hPP : IsConjPl D.host P P')
    (hs : ∀ A : ValuationSubring N.Om, IsPlaceOver A P → ∀ b : B, ∃ σ ∈ Ine (F := D.host.E) A, χ σ = b)
    (A : ValuationSubring N.Om) (hA' : IsPlaceOver A P') (b : B) : ∃ σ ∈ Ine (F := D.host.E) A, χ σ = b := by
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  have hst : ∀ x : D.host.E, IsCMField.complexConj D.host.E x = D.host.conj x :=
    Formalism.BasicNotions.bridge_star_holds D.R D.host
  obtain ⟨⟨j, hj⟩, -⟩ := X.cc_cm
  have hκ : ∀ x, D.host.conj (D.host.conj x) = x := fun x => by
    rw [← hst, ← hst, IsCMField.complexConj_apply_apply]
  have hc : ∀ x, X.cc (algebraMap D.host.E N.Om x) =
      algebraMap D.host.E N.Om (D.host.conj x) := fun x => by
    apply j.injective
    rw [hj, ← hst]
    exact (IsCMField.complexEmbedding_complexConj D.host.E
      (j.comp (algebraMap D.host.E N.Om)) x).symm
  have hs' : ∀ x, X.cc.symm (algebraMap D.host.E N.Om x) =
      algebraMap D.host.E N.Om (D.host.conj x) := fun x => by
    rw [RingEquiv.symm_apply_eq, hc, hκ]
  have hinv : ∀ x, X.cc (X.cc x) = x := fun x => by
    apply j.injective
    rw [hj, hj]
    simp
  have hsymm : ∀ x, X.cc.symm x = X.cc x := fun x => by
    rw [RingEquiv.symm_apply_eq, hinv]
  have hP'P := GlobalTheory.GalChar.isConjPl_symm hPP
  have hpl : IsPlaceOver (A.comap X.cc.symm.toRingHom) P := fun y => by
    have hint : IsIntegral ℤ (D.host.conj (y : D.host.E)) := by
      rw [← hst]
      exact (RingOfIntegers.isIntegral_coe y).map
        ((IsCMField.complexConj D.host.E).toRingEquiv.toRingHom.toIntAlgHom)
    rw [GlobalTheory.AntiRam.valuation_comap_lt_one, hs', ← hP'P ⟨_, hint⟩ y (hκ _).symm]
    exact hA' ⟨_, hint⟩
  obtain ⟨σ, hσ, hσb⟩ := hs _ hpl b⁻¹
  obtain ⟨σ', h1, h2⟩ := GlobalTheory.AntiRam.exists_conj_mem_Ine X.cc (fun x => D.host.conj x) hc hκ _ σ hσ
  have eA : (A.comap X.cc.symm.toRingHom).comap X.cc.symm.toRingHom = A := by
    ext y
    show X.cc.symm (X.cc.symm y) ∈ A ↔ y ∈ A
    rw [hsymm, hsymm, hinv]
  refine ⟨σ', eA ▸ h2, ?_⟩
  rw [hA σ σ' h1, hσb, inv_inv]

theorem sign_eq_one (hY : GlobalTheory.UnivChar.IsUnivChar Y) {i : X.Tw} {S : Finset (Pl D.host.E)} {M : ℕ}
    {P v : Pl D.host.E} (hP : P ∈ S) (hv : v ∈ S) (hc : IsConjPl D.host P v) (hPa : P ∈ admissibleConjugatePairPlaces X i S M) :
    (((Y.delU_conj i S M P hP v hv hc).choose : ℤ) : ZMod (X.l i ^ M)) = 1 := by
  classical
  have hs := (Y.delU_conj i S M P hP v hv hc).choose_spec
  have hva : v ∈ admissibleConjugatePairPlaces X i S M := conj_mem_admissibleConjugatePairPlaces hPa hc
  obtain ⟨-, P', -, -, hadm⟩ := mem_admissibleConjugatePairPlaces_iff.1 hPa
  obtain ⟨-, χ, h1, h2, h3, h4, h5⟩ := hadm.2 P (by simp)
  have hDel : GlobalTheory.GalChar.IsDel D.host X.cc (X.l i) M (GlobalTheory.GalChar.pair D.host P) χ := by
    refine ⟨h1, h2, h3, fun w hw => h4 w (fun e => hw (Or.inl e)) (fun e => hw (Or.inr e)), fun w hw A hA b => ?_⟩
    have hsP : ∀ A : ValuationSubring N.Om, IsPlaceOver A P →
        ∀ b, ∃ σ ∈ Ine (F := D.host.E) A, χ σ = b := fun A hA b => by
      obtain ⟨σ, hσ⟩ := h5 A hA (Multiplicative.toAdd b)
      exact ⟨σ.1, σ.2, Multiplicative.toAdd.injective hσ⟩
    rcases hw with rfl | hw
    · exact hsP A hA b
    · exact surj_conj χ h2 hw hsP A hA b
  have hD := GlobalTheory.GalChar.isDel_delOf D.host X.cc (X.l i) ⟨χ, hDel⟩
  obtain ⟨A, hA⟩ := ReciprocityTheory.Gal.exists_isPlaceOver N.Om P
  obtain ⟨σ, -, hσ⟩ := hD.2.2.2.2 P (Or.inl rfl) A hA (Multiplicative.ofAdd 1)
  have e := hs σ
  rw [delU_on hY σ ⟨v, hv⟩ hva, delU_on hY σ ⟨P, hP⟩ hPa] at e
  simp only at e
  rw [GlobalTheory.GalChar.pair_eq hc, hσ, toAdd_ofAdd, mul_one] at e
  exact e.symm

theorem spread_conj (hY : GlobalTheory.UnivChar.IsUnivChar Y) {i : X.Tw} {M : ℕ} {ch : Set (Pl D.host.E)} (hch : IsChoice ch)
    {S : Finset (Pl D.host.E)} (hS : admissibleConjugatePairPlaces X i S M = S) (x : ↥(half ch (admissibleConjugatePairPlaces X i S M)) → ZMod (X.l i ^ M))
    {v P : Pl D.host.E} (hvS : v ∈ S) (hvc : v ∉ ch) (hvP : IsConjPl D.host v P)
    (hPh : P ∈ half ch (admissibleConjugatePairPlaces X i S M)) :
    spread Y i S M ch x ⟨v, hvS⟩ = x ⟨P, hPh⟩ := by
  have hva : v ∈ admissibleConjugatePairPlaces X i S M := by rw [hS]; exact hvS
  have hne : v ≠ P := ne_of_split (isSplit_of_mem_admissibleConjugatePairPlaces hva) hvP
  have hPv := GlobalTheory.GalChar.isConjPl_symm hvP
  have hPaa : P ∈ admissibleConjugatePairPlaces X i (admissibleConjugatePairPlaces X i S M) M := by
    simp only [hS]
    rw [← hS]
    exact (mem_half.1 hPh).1
  rw [spread_apply, Finset.sum_eq_single ⟨P, hPh⟩, weight, if_neg hne, dite_eq_left ⟨hva, hPv⟩, sign_eq_one hY _ _ hPv hPaa,
    one_mul]
  · intro P' _ h'
    rw [weight, if_neg fun e : v = P'.1 => hvc (e ▸ (mem_half.1 P'.2).2), dite_eq_right fun h => h' (Subtype.ext
      (GlobalTheory.GalChar.isConjPl_unique (GlobalTheory.GalChar.isConjPl_symm h.2) hvP)), zero_mul]
  · exact fun h => absurd (Finset.mem_univ _) h

theorem spread_restrict : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (Y : NExp D.R D.host D.what₂ D.LL0 N X), GlobalTheory.UnivChar.IsUnivChar Y → ∀ (i : X.Tw) (M : ℕ) (ch : Set (Pl D.host.E)), IsChoice ch → ∀ (Q Q' : Finset (Pl D.host.E)) (hQQ : Q' ⊆ Q), admissibleConjugatePairPlaces X i Q M = Q → admissibleConjugatePairPlaces X i Q' M = Q' → ∀ (hsub : ∀ w ∈ half ch (admissibleConjugatePairPlaces X i Q' M), w ∈ half ch (admissibleConjugatePairPlaces X i Q M)) (c : ↥(half ch (admissibleConjugatePairPlaces X i Q M)) → ZMod (X.l i ^ M)) (v : Pl D.host.E) (hv : v ∈ Q'), spread Y i Q M ch c ⟨v, hQQ hv⟩ = spread Y i Q' M ch (fun w => c ⟨w.1, hsub w.1 w.2⟩) ⟨v, hv⟩ := by
  intro D N X Y hY i M ch hch Q Q' hQQ hQ hQ' hsub c v hv
  by_cases hc : v ∈ ch
  · have h1 : v ∈ half ch (admissibleConjugatePairPlaces X i Q M) := mem_half.2 ⟨by rw [hQ]; exact hQQ hv, hc⟩
    have h2 : v ∈ half ch (admissibleConjugatePairPlaces X i Q' M) := mem_half.2 ⟨by rw [hQ']; exact hv, hc⟩
    rw [spread_of_mem Y i Q M hch c ⟨v, hQQ hv⟩ h1, spread_of_mem Y i Q' M hch _ ⟨v, hv⟩ h2]
  · have hva : v ∈ admissibleConjugatePairPlaces X i Q' M := by rw [hQ']; exact hv
    obtain ⟨-, P, -, hvP, -⟩ := mem_admissibleConjugatePairPlaces_iff.1 hva
    have hne : v ≠ P := ne_of_split (isSplit_of_mem_admissibleConjugatePairPlaces hva) hvP
    have hPc : P ∈ ch := by
      by_contra h
      exact hc ((hch.pair _ _ hvP hne).2 h)
    have hPa' : P ∈ admissibleConjugatePairPlaces X i Q' M := conj_mem_admissibleConjugatePairPlaces hva hvP
    have hPh' : P ∈ half ch (admissibleConjugatePairPlaces X i Q' M) := mem_half.2 ⟨hPa', hPc⟩
    rw [spread_conj hY hch hQ c (hQQ hv) hc hvP (hsub P hPh'), spread_conj hY hch hQ' _ hv hc hvP hPh']

end GlobalTheory.SpreadRestrict

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UniversalCharSpreadCommutesWithRestrictionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.universalChar_spread_commutes_with_restriction : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (Y : NExp D.R D.host D.what₂ D.LL0 N X), GlobalTheory.UnivChar.IsUnivChar Y → ∀ (i : X.Tw) (M : ℕ) (ch : Set (Pl D.host.E)), IsChoice ch → ∀ (Q Q' : Finset (Pl D.host.E)) (hQQ : Q' ⊆ Q), admissibleConjugatePairPlaces X i Q M = Q → admissibleConjugatePairPlaces X i Q' M = Q' → ∀ (hsub : ∀ w ∈ half ch (admissibleConjugatePairPlaces X i Q' M), w ∈ half ch (admissibleConjugatePairPlaces X i Q M)) (c : ↥(half ch (admissibleConjugatePairPlaces X i Q M)) → ZMod (X.l i ^ M)) (v : Pl D.host.E) (hv : v ∈ Q'), spread Y i Q M ch c ⟨v, hQQ hv⟩ = spread Y i Q' M ch (fun w => c ⟨w.1, hsub w.1 w.2⟩) ⟨v, hv⟩ := by
  first | exact @GlobalTheory.SpreadRestrict.spread_restrict | exact GlobalTheory.SpreadRestrict.spread_restrict | (intros; apply GlobalTheory.SpreadRestrict.spread_restrict <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisConjClassScalarsAndVolume
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisConjClassScalarsAndVolume
set_option autoImplicit false

namespace GlobalTheory.ConjScalar

section Ideals

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.HeckeIdealValue
open scoped nonZeroDivisors

variable {L : Type} [Field L] [NumberField L]

theorem conj_of_primes (χ χ' : HChar L) (τ : ℂ ≃+* ℂ) (b : 𝓞 L)
    (h : ∀ v : HeightOneSpectrum (𝓞 L), b ∉ v.asIdeal →
      τ (((χ.val v : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm v.asIdeal : ℝ) : ℝ) : ℂ)) =
        ((χ'.val v : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm v.asIdeal : ℝ) : ℝ) : ℂ))
    (cc : Ideal (𝓞 L)) (h0 : cc ≠ ⊥) (h1 : cc ⊔ Ideal.span {b} = ⊤) :
    τ (((χ.onId (cc : FractionalIdeal (𝓞 L)⁰ L) : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm cc : ℝ) : ℝ) : ℂ)) =
      ((χ'.onId (cc : FractionalIdeal (𝓞 L)⁰ L) : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm cc : ℝ) : ℝ) : ℂ) := by
  induction cc using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl h0
  | h₂ x hx =>
    obtain rfl : x = ⊤ := Ideal.isUnit_iff.1 hx
    simp [onId_one]
  | h₃ a p ha hp ih =>
    let v : HeightOneSpectrum (𝓞 L) := ⟨p, Ideal.isPrime_of_prime hp, hp.ne_zero⟩
    have hb : b ∉ v.asIdeal := fun hb => v.isPrime.ne_top
      (top_le_iff.1 (h1.ge.trans (sup_le Ideal.mul_le_left ((Ideal.span_singleton_le_iff_mem _).2 hb))))
    have ha1 : a ⊔ Ideal.span {b} = ⊤ := top_le_iff.1 (h1.ge.trans (sup_le_sup_right Ideal.mul_le_right _))
    have key : ∀ ψ : HChar L,
        ((ψ.onId ((p * a : Ideal (𝓞 L)) : FractionalIdeal (𝓞 L)⁰ L) : ℂˣ) : ℂ) *
          ((Real.sqrt (Ideal.absNorm (p * a) : ℝ) : ℝ) : ℂ) =
        (((ψ.val v : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm v.asIdeal : ℝ) : ℝ) : ℂ)) *
          (((ψ.onId (a : FractionalIdeal (𝓞 L)⁰ L) : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm a : ℝ) : ℝ) : ℂ)) := fun ψ => by
      rw [FractionalIdeal.coeIdeal_mul, onId_mul ψ (FractionalIdeal.coeIdeal_ne_zero.2 hp.ne_zero)
        (FractionalIdeal.coeIdeal_ne_zero.2 ha), map_mul, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _),
        show ψ.onId (p : FractionalIdeal (𝓞 L)⁰ L) = ψ.val v from onId_prime ψ v]
      push_cast
      ring
    rw [key, key, map_mul, h v hb, ih ha ha1]

end Ideals

section Lattice

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_numerator_coprime (H : Host E) {n bad : ℕ} (Λ : GenLat E n) (hU : Λ.Unimod) (hT : Λ.TrivAt bad) :
    ∃ cc : Ideal (𝓞 E), cc ≠ ⊥ ∧ cc ⊔ Ideal.span {(bad : 𝓞 E)} = ⊤ ∧ cc ⊔ cc.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ ∧
      Submodule.span (𝓞 E) (detSet Λ.La) * idlE (cc.map (H.bar : 𝓞 E →+* 𝓞 E)) = idlE cc := by
  obtain ⟨h0, cc, c1, c2, c3⟩ := GlobalTheory.ScalarUnit.exists_numerator H Λ hU
  have hN : Nat.Coprime (Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index bad := by
    refine Nat.coprime_of_dvd fun p hp h1 h2 => ?_
    obtain ⟨k, hk, hk'⟩ := hT
    exact (Nat.Prime.coprime_iff_not_dvd hp).1
      (GlobalTheory.ScalarUnit.index_coprime hp Λ ⟨k, hk.coprime_dvd_right h2, hk'⟩ h0).symm h1
  generalize (Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index = N at *
  refine ⟨cc, fun e => h0 ?_, ?_, c1, c2⟩
  · rw [e, Ideal.mem_bot] at c3
    exact_mod_cast c3
  · obtain ⟨u, v, e⟩ := (Nat.isCoprime_iff_coprime.2 hN).map (Int.castRingHom (𝓞 E))
    simp only [map_natCast] at e
    rw [Ideal.eq_top_iff_one, ← e]
    exact add_mem (Ideal.mem_sup_left (Ideal.mul_mem_left _ _ c3))
      (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))

theorem ep_conj {H : Host E} {Dw : Datum H} {l : Level H} (c : Coeff l) {n bad : ℕ} (ta : c.F ≃+* c.F)
    {B B' : Ideal (𝓞 E) → c.F} {epF epF' : Submodule (𝓞 E) (Fin n → E) → c.F}
    (he : EpIs (Dw := Dw) c bad B epF) (he' : EpIs (Dw := Dw) c bad B' epF')
    (hB : ∀ cc, cc ≠ ⊥ → cc ⊔ Ideal.span {(bad : 𝓞 E)} = ⊤ → ta (B cc) = B' cc)
    {L : Submodule (𝓞 E) (Fin n → E)} (g : GlobalTheory.ClassScalarCompare.Guard H bad L) : ta (epF L) = epF' L := by
  obtain ⟨cc, c0, c1, c2, c3⟩ := exists_numerator_coprime H ⟨L⟩ g.1 g.2.1
  obtain ⟨q, q0, q1, q2⟩ := he L cc g.1 g.2.1 g.2.2 c2 c3
  obtain ⟨q', q0', q1', q2'⟩ := he' L cc g.1 g.2.1 g.2.2 c2 c3
  have hN : (Ideal.absNorm cc : ℚ) ≠ 0 := by exact_mod_cast fun h => c0 (Ideal.absNorm_eq_zero_iff.1 h)
  have hq : q = q' := by
    have h1 := q1.trans q1'.symm
    rw [← q1] at hN
    exact (pow_left_inj₀ q0.le q0'.le two_ne_zero).1 (mul_right_cancel₀ (right_ne_zero_of_mul hN) h1)
  rw [q2, q2', map_mul, map_inv₀, hB cc c0 c1, map_ratCast, hq]

end Lattice

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical


set_option maxHeartbeats 1000000 in
theorem conj_vol_ep : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (τ : ℂ ≃+* ℂ) (ta : M.c'.F ≃+* M.c'.F), (∀ a : M.c'.F, ((ta a : M.c'.F) : ℂ) = τ (a : ℂ)) → FixBase T R i τ → ∀ (a b : Tp) (e : M.Cl' a ≃ M.Cl' b), SameCover M a b e → ConjTup R τ (tup a) (tup b) → ta (M.vol a) = M.vol b ∧ ∀ k, ta (M.ep a k) = M.ep b (e k) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hC _ i Tp tup M hO τ ta hta hF a b e hS hab
  obtain ⟨-, -, -, hbad, hvol, hk⟩ := hS
  refine ⟨?_, fun k => ?_⟩
  · obtain ⟨h, J', hR, -⟩ := (hO.tuple a).reps
    rw [hvol, hR.2.2.2.2.1, map_inv₀, map_natCast]
  · have hxi := (GlobalTheory.T.conjugate_tuples_conjugate_residue_levels D G Pl0 T0 A T R F κ v₀ hC τ (tup a) (tup b) hab).2.2.1
    obtain ⟨r1, r2, -, -, -, r6⟩ := (hO.reps a).1 k
    have hcj := (GlobalTheory.ClassScalarCompare.latPin_iff_conjLat _ _).1 (hO.reps a).2 k
    have g := GlobalTheory.ClassScalarCompare.guard_conjLat (H := T.Q.H) (L := (M.La a k).La) ⟨r1, r2, r6⟩
    rw [hcj, GlobalTheory.ClassScalarCompare.conjLat_conjLat] at g
    have heb := (hO.ep b).2
    have hBb := (hO.tuple b).B
    rw [hbad] at heb hBb
    rw [(hO.ep a).1 k, (hO.ep b).1 (e k), (hk k).1]
    refine ep_conj M.c' ta (hO.ep a).2 heb (fun cc c0 c1 => Subtype.ext ?_) g
    have h1 : ((M.B a cc : M.c'.F) : ℂ) = _ := (hO.tuple a).B cc c0 c1
    have h2 : ((M.B b cc : M.c'.F) : ℂ) = _ := hBb cc c0 c1
    rw [hta, h1, h2]
    refine conj_of_primes _ _ τ _ (fun P hP => ?_) cc c0 c1
    have hs := hF.split P fun hj => hP (by
      obtain ⟨u, hu⟩ := (hO.bad a).2.2.2.2
      rw [hu, Nat.cast_mul]
      exact Ideal.mul_mem_right _ _ hj)
    have key : ∀ t, (((R.C.mu0 i * R.xiH t * R.C.eta⁻¹).val P : ℂˣ) : ℂ) *
        ((Real.sqrt (Ideal.absNorm P.asIdeal : ℝ) : ℝ) : ℂ) = (((R.xiH t).val P : ℂˣ) : ℂ) *
        ((((R.C.mu0 i * R.C.eta⁻¹).val P : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm P.asIdeal : ℝ) : ℝ) : ℂ)) := fun t => by
      simp only [Formalism.L2.Host.HChar.val_mul, Units.val_mul]
      ring
    rw [key, key, map_mul, hs, hxi]

end GlobalTheory.ConjScalar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisConjClassScalarsAndVolumeStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisConj_classScalars_and_volume : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (τ : ℂ ≃+* ℂ) (ta : M.c'.F ≃+* M.c'.F), (∀ a : M.c'.F, ((ta a : M.c'.F) : ℂ) = τ (a : ℂ)) → FixBase T R i τ → ∀ (a b : Tp) (e : M.Cl' a ≃ M.Cl' b), SameCover M a b e → ConjTup R τ (tup a) (tup b) → ta (M.vol a) = M.vol b ∧ ∀ k, ta (M.ep a k) = M.ep b (e k) := by
  first | exact @GlobalTheory.ConjScalar.conj_vol_ep | exact GlobalTheory.ConjScalar.conj_vol_ep | (intros; apply GlobalTheory.ConjScalar.conj_vol_ep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DownwardLiftLevelActsByInverseCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DownwardLiftLevelActsByInverseCharacter
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite

noncomputable section

namespace GlobalTheory.DownLift.TypeLaw

variable {D : D7}

theorem setIntegral_mul_right_of_fd {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant] (𝓕 : Set G) (h𝓕 : IsFundamentalDomain Γ 𝓕 μ)
    (k : G) (hk : Measure.map (fun g => g * k) μ = μ) (f : G → ℂ) (hf : ∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) :
    ∫ g in 𝓕, f (g * k) ∂μ = ∫ g in 𝓕, f g ∂μ := by
  have hmp : MeasurePreserving (fun g : G => g * k) μ μ := ⟨measurable_mul_const k, hk⟩
  have hemb : MeasurableEmbedding (fun g : G => g * k) := measurableEmbedding_mulRight k
  have h2 : IsFundamentalDomain Γ ((fun g : G => g * k) ⁻¹' 𝓕) μ := by
    refine h𝓕.preimage_of_equiv hmp.quasiMeasurePreserving (e := id) Function.bijective_id ?_
    intro γ g
    simp only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc]
  have hinv : ∀ (γ : Γ) (g : G), (fun g : G => f (g * k)) (γ • g) = (fun g : G => f (g * k)) g := by
    intro γ g
    simp only [Subgroup.smul_def, smul_eq_mul, mul_assoc]
    exact hf γ γ.2 _
  rw [h𝓕.setIntegral_eq h2 hinv]
  exact hmp.setIntegral_preimage_emb hemb f 𝓕

theorem flagOneLevel_eq_self_of_trivial {n : ℕ} (L : LevDat D.host.E ℂ n) (hL : L.P = LevelP.triv L.Pg L.r ℂ) : flag1L L = L := by
  cases L
  simp only at hL
  subst hL
  rfl

theorem adForms_right {G Γ W : Type} [Group G] [Group Γ] (ι : Γ →* G) [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) (F : G → W)
    (hF : F ∈ Formalism.IndefR.Bridge.AdForms ι ρ J χ) (x : G) (k : J) : F (x * k) = (χ k : ℂ) • F x := by
  have h1 := hF 1 x k
  rw [map_one, one_mul, map_one, Module.End.one_apply] at h1
  exact h1

theorem adForm_type (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (c : CoefA V)
    (F : Formalism.IndefR.Bridge.Gf V → c.W)
    (hF : F ∈ Formalism.IndefR.Bridge.AdForms (Formalism.IndefR.Bridge.ratF V) c.coef.ρ (levEnv V β L).J (levEnv V β L).χ)
    (κ : GA D V) (hκ : κ ∈ levG V β (flag1L L)) (x : Formalism.IndefR.Bridge.Gf V) :
    F (x * (finHom V).rangeRestrict κ) = levChi V β (flag1L L) κ • F x := by
  have hmem : (finHom V).rangeRestrict κ ∈ (levEnv V β L).J := by
    show finE V κ ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (flag1L L)
    exact hκ.2
  have h1 := adForms_right (W := c.W) (Formalism.IndefR.Bridge.ratF V) c.coef.ρ (levEnv V β L).J (levEnv V β L).χ F hF x ⟨_, hmem⟩
  have hχ : (((levEnv V β L).χ ⟨_, hmem⟩ : ℂˣ) : ℂ) = levChi V β (flag1L L) κ := rfl
  rw [hχ] at h1
  exact h1

end GlobalTheory.DownLift.TypeLaw

namespace GlobalTheory.DownLift.TypeLaw

theorem datVt_P {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) :
    (R.datVt i t).P = LevelP.triv (R.datVt i t).Pg (R.datVt i t).r ℂ := by
  simp [LevCh.datVt, datY, LevelP.conj, LevelP.triv]
  rfl

end GlobalTheory.DownLift.TypeLaw

namespace GlobalTheory.DownLift.TypeLaw

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem extV_type (R : RealDat D A Ks) (hM : R.IsModels) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (κ : GA D (Vc D i))
    (hκ : κ ∈ levG (Vc D i) (R.βV i) (R.datVt i t)) (h : GA D (Vc D i)) :
    R.extV i t y (h * κ) = levChi (Vc D i) (R.βV i) (R.datVt i t) κ • R.extV i t y h := by
  have hL : flag1L (R.datVt i t) = R.datVt i t := flagOneLevel_eq_self_of_trivial _ (datVt_P R i t)
  have hκ1 : κ ∈ levG (Vc D i) (R.βV i) (flag1L (R.datVt i t)) := by rw [hL]; exact hκ
  have hc0 : levChi (Vc D i) (R.βV i) (R.datVt i t) κ ≠ 0 := levChi_ne_zero _ κ
  have hchi : levChi (Vc D i) (R.βV i) (flag1L (R.datVt i t)) κ = levChi (Vc D i) (R.βV i) (R.datVt i t) κ := by rw [hL]
  have hyA : (R.HV i t).e y ∈ Formalism.IndefR.Bridge.AdForms (Formalism.IndefR.Bridge.ratF (Vc D i)) (R.cV i).coef.ρ
      (levEnv (Vc D i) (R.βV i) (R.datVt i t)).J (levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ :=
    (hM.HV i t).2.1.le ⟨y, rfl⟩
  have hty : ∀ x, (R.HV i t).e y x = (levChi (Vc D i) (R.βV i) (R.datVt i t) κ)⁻¹ •
      (R.HV i t).e y (x * (finHom (Vc D i)).rangeRestrict κ) := by
    intro x
    have h1 := adForm_type (Vc D i) (R.βV i) (R.datVt i t) (R.cV i) ((R.HV i t).e y) hyA κ hκ1 x
    have h2 : (R.HV i t).e y (x * (finHom (Vc D i)).rangeRestrict κ) =
        levChi (Vc D i) (R.βV i) (R.datVt i t) κ • (R.HV i t).e y x :=
      h1.trans (congrArg (· • (R.HV i t).e y x) hchi)
    exact (inv_smul_smul₀ hc0 _).symm.trans (congrArg ((levChi (Vc D i) (R.βV i) (R.datVt i t) κ)⁻¹ • ·) h2.symm)
  have e1 := GlobalTheory.ThetaProjEquiv.ext_shift (R.cV i) (hM.cV i) κ hκ.1 _ hc0 ((R.HV i t).e y) ((R.HV i t).e y) hty h
  have hx : ∀ z, R.extV i t y z = (R.cV i).ext ((R.HV i t).e y) z := fun z => rfl
  have e2 : (R.cV i).ext (levChi (Vc D i) (R.βV i) (R.datVt i t) κ • (R.HV i t).e y) h =
      levChi (Vc D i) (R.βV i) (R.datVt i t) κ • (R.cV i).ext ((R.HV i t).e y) h := by
    exact congrFun (LinearMap.map_smul (R.cV i).ext _ ((R.HV i t).e y)) h
  exact (hx (h * κ)).trans (e1.symm.trans (e2.trans (congrArg (levChi (Vc D i) (R.βV i) (R.datVt i t) κ • ·) (hx h).symm)))

end GlobalTheory.DownLift.TypeLaw

namespace GlobalTheory.DownLift.TypeLaw

theorem alg_step {a b c d d' : ℂ} (hc : c ≠ 0) (hab : a = b) (hd : d' = c * d) : a * d = c⁻¹ * (b * d') := by
  rw [hab, hd, mul_left_comm b c d, inv_mul_cancel_left₀ hc]

theorem downInt_level : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (f : WO (Vc D i) (Wc D i) → ℂ), IsThetaFunO R.ψ (Vc D i) (Wc D i) f → ∀ κ ∈ levG (Vc D i) (R.βV i) (R.datVt i t), ∀ (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i)), downInt R i t y (R.ωP i t (κ, 1) f) l g = (levChi (Vc D i) (R.βV i) (R.datVt i t) κ)⁻¹ * downInt R i t y f l g := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG hP i t y f hf κ hκ l g
  have hM := hG.core.models
  have hc0 : levChi (Vc D i) (R.βV i) (R.datVt i t) κ ≠ 0 := levChi_ne_zero _ κ
  have hFn : ∀ h, l (R.extV i t y (h * κ)) = levChi (Vc D i) (R.βV i) (R.datVt i t) κ * l (R.extV i t y h) := by
    intro h
    exact (congrArg l (extV_type R hM i t y κ hκ h)).trans (l.map_smul _ _)

  have hth : ∀ h, thetaKO (R.ωP i t) h g (R.ωP i t (κ, 1) f) = thetaKO (R.ωP i t) (h * κ) g f := by
    intro h
    have hm : ((h, g) : GA D (Vc D i) × GA D (Wc D i)) * (κ, 1) = (h * κ, g) := by
      rw [Prod.mk_mul_mk, mul_one]
    show R.ωP i t (h, g) (R.ωP i t (κ, 1) f) 0 = R.ωP i t (h * κ, g) f 0
    rw [← hm, map_mul, Module.End.mul_apply]

  let Φ : GA D (Vc D i) → ℂ := fun h => thetaKO (R.ωP i t) h g f * l (R.extV i t y h)
  have hΦ : ∀ γ ∈ GQ (Vc D i), ∀ h, Φ (γ * h) = Φ h := by
    intro γ hγ h
    have ht : thetaKO (R.ωP i t) (γ * h) g f = thetaKO (R.ωP i t) h g f := by
      have hm : ((γ, 1) : GA D (Vc D i) × GA D (Wc D i)) * (h, g) = (γ * h, g) := by
        rw [Prod.mk_mul_mk, one_mul]
      show R.ωP i t (γ * h, g) f 0 = R.ωP i t (h, g) f 0
      rw [← hm, map_mul, Module.End.mul_apply]
      exact (hP i t).datum.om_aut γ hγ 1 (GQ (Wc D i)).one_mem _ ((hP i t).datum.om_pres _ _ hf)
    have hl : l (R.extV i t y (γ * h)) = l (R.extV i t y h) :=
      congrArg l (GlobalTheory.ThetaProjEquiv.extV_left R hM.HV i t y γ hγ h)
    exact congrArg₂ (· * ·) ht hl

  obtain ⟨i1, i2, i3, i4⟩ := GlobalTheory.TwistAdelicTop.locallyCompact_secondCountable_borel_countable (Vc D i)
  have : IsTopologicalGroup (GA D (Vc D i)) :=
    inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig (Vc D i).gram))
  have hH : (R.νV i t).IsHaarMeasure := (hM.νV i t).1.1
  have hmap := GlobalTheory.haar_map_mul_right_of_mem_compact_subgroup (R.νV i t) _
    (GlobalTheory.ParahoricCompact.isCompact_levG (Vc D i) (R.βV i) (R.datVt i t)) κ hκ
  have hint := setIntegral_mul_right_of_fd (GQ (Vc D i)) (R.νV i t) (R.fdV i t) (hM.νV i t).2 κ hmap Φ hΦ
  have hfun : (fun h => thetaKO (R.ωP i t) h g (R.ωP i t (κ, 1) f) * l (R.extV i t y h)) =
      fun h => (levChi (Vc D i) (R.βV i) (R.datVt i t) κ)⁻¹ * Φ (h * κ) := by
    funext h
    exact alg_step hc0 (hth h) (hFn h)
  exact (congrArg (fun φ : GA D (Vc D i) → ℂ => ∫ h in R.fdV i t, φ h ∂(R.νV i t)) hfun).trans
    ((integral_const_mul _ _).trans (congrArg ((levChi (Vc D i) (R.βV i) (R.datVt i t) κ)⁻¹ * ·) hint))

end GlobalTheory.DownLift.TypeLaw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DownwardLiftLevelActsByInverseCharacterStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.downwardLift_level_acts_by_inverse_character : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (f : WO (Vc D i) (Wc D i) → ℂ), IsThetaFunO R.ψ (Vc D i) (Wc D i) f → ∀ κ ∈ levG (Vc D i) (R.βV i) (R.datVt i t), ∀ (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i)), downInt R i t y (R.ωP i t (κ, 1) f) l g = (levChi (Vc D i) (R.βV i) (R.datVt i t) κ)⁻¹ * downInt R i t y f l g := by
  first | exact @GlobalTheory.DownLift.TypeLaw.downInt_level | exact GlobalTheory.DownLift.TypeLaw.downInt_level | (intros; apply GlobalTheory.DownLift.TypeLaw.downInt_level <;> assumption)
end
end
