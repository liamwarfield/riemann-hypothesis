module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalShareSumBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodSingle

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PageSt
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevelSqYBoundAtRec
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevelSqYBoundAtRec
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.BigOn
theorem levelSq_yBound_atRec_alt :
    _root_.GlobalTheory.BigOn.ForallRecordObjects fun Fm x _ i p _ O => LeafLevelSq O (Res (R2 p)) (Fm.D x i).R.f ∧ LeafYBound O := by
  refine ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ =>
    ⟨0, fun c _ _ => _root_.GlobalTheory.BigTop.EventuallyAtPoints.of_forall fun x hx i p _ _ r O hO => ?_⟩⟩⟩
  obtain ⟨st, td⟩ := hO.1.depth
  letI := hostAlg (Fm.D x i)
  have g1 : O.g1 = (Fm.D x i).host.g 0 := td.jets_eq_fact
  have g2 : O.g2 = (Fm.D x i).host.g 1 := td.g2_eq
  have f1 : O.f = ((Fm.D x i).R.f : ℝ) := td.f_eq
  have k1 : O.k = ((Fm.D x i).R.k : ℝ) := td.k_eq
  have hrec : (R2 p).grp_record := by
    obtain ⟨plg, iso, -, h2, h3, h4⟩ := p.grpRecPin
    exact ⟨p.R.eG.trans p.cG, plg, iso, h2, h3, h4⟩
  have yb : ∀ {large₂ : SizeData₂ (Fm.D x i)} {Pm : ParameterChoice' (Fm.D x i) large₂}, ParamsT (Fm.D x i) large₂ Pm →
      LeafYBound (onOf (R2 p) (F2 p) c (supArgs (R2 p))) := fun {_ Pm} _ =>
    leafYBound (F := F2 p) c (supArgs (R2 p)) Pm
  refine ⟨?_, ?_⟩
  · have := leafLevelSq (F := F2 p) c (supArgs (R2 p)) hrec
    unfold LeafLevelSq
    rw [g1, g2]
    exact this
  · have := yb (Fm.parT x hx i)
    unfold LeafYBound OnObj.y
    rw [g1, g2, f1, k1]
    exact this
end GlobalTheory.BigOn
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevelSqYBoundAtRecStatement
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leafLevelSq_and_leafYBound : _root_.GlobalTheory.BigOn.ForallRecordObjects fun Fm x _ i p _ O => LeafLevelSq O (Res (R2 p)) (Fm.D x i).R.f ∧ LeafYBound O := by
  first | exact @_root_.GlobalTheory.BigOn.levelSq_yBound_atRec_alt | exact _root_.GlobalTheory.BigOn.levelSq_yBound_atRec_alt | (intros; apply _root_.GlobalTheory.BigOn.levelSq_yBound_atRec_alt <;> assumption)
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn
namespace GlobalTheory.BigOn.PageNumbers
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {Pm : ParameterChoice' D L}
end GlobalTheory.BigOn.PageNumbers
namespace GlobalTheory.BigOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem pageSt_alt : _root_.GlobalTheory.BigOn.PageStatement := by
  refine (GlobalTheory.T.indexBoundParameterRequirements_eventually_family.and _root_.GlobalTheory.T.leafLevelSq_and_leafYBound).imp fun Fm CH _ H => ?_
  obtain ⟨⟨xs, hxs⟩, ⟨c1, hc1⟩⟩ := H
  refine ⟨max c1 1, fun c hc hB => ?_⟩
  obtain ⟨x2, hx2⟩ := hc1 c ((le_max_left _ _).trans hc) hB
  refine ⟨max (max xs x2) (3 * c.C), fun x hx hle i p hp hm r O hr => ?_⟩
  have hxs' : xs ≤ x := (le_max_left _ _).trans ((le_max_left _ _).trans hle)
  have hx2' : x2 ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans hle)
  have hxC : 3 * c.C ≤ x := (le_max_right _ _).trans hle
  have hR := hxs x hx hxs' i
  obtain ⟨hSq, hY⟩ := hx2 x hx hx2' i p hp hm r O hr
  have hE : ∀ C CH', ErrorConstantMatchesDefinition ((R2 p).num (F2 p) C CH') O C := fun C CH' => (GlobalTheory.BigOn.Check.twoRunDatum_boundUnit_at_indefinitePoint p (Fm.parT x hx i) r O hr C CH').1
  have hb : O.b = (Fm.L x i).sc.b := (GlobalTheory.BigOn.Check.twoRunDatum_boundUnit_at_indefinitePoint p (Fm.parT x hx i) r O hr 0 0).2
  obtain ⟨st, hd⟩ := hr.1.depth
  letI := st
  letI := hostAlg (Fm.D x i)
  have hd' : GlobalTheory.RunDepth.RunTie p.T.toCore (Fm.ex x hx i).errX (Fm.parT x hx i) (Fm.ex x hx i).kap_def ({ O with de2 := (Fm.L x i).de2 } : Obj p c)
      (fun j : Fin (Fm.D x i).R.m => (j : ℕ) + 1) := { hd with }
  have hN : GlobalTheory.IndexAssembly.NumTie (Fm.parT x hx i) (Fm.ex x hx i).kap_def ({ O with de2 := (Fm.L x i).de2 } : Obj p c) :=
    ⟨hr.1.rr_eq, hr.1.realisedChain_torus_eq, hr.1.Nc_eq,
      hr.1.DF_eq.trans (congrArg (fun n : ℕ => (n : ℝ)) (PageNumbers.sup_fin_eq_topDeg _ _)), rfl, hr.1.pde_eq⟩
  have hx3 : 3 * c.C ≤ (Fm.L x i).sc.x := by rw [Fm.L_x x i hx]; exact hxC
  have hC : Formalism.L2.Indef.Tree.OnPage.ConstC c := (le_max_right _ _).trans hc
  obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.IndexAssembly.numericLeaves hd' hN hR hC hB hx3
  refine ⟨h1, h2, h3, h4, hSq, hY, hb, ?_, hE⟩
  have hx0 : 0 < (Fm.L x i).sc.x := by linarith [(Fm.L x i).sc.one_lt_alt]
  have e1 := Real.rpow_pos_of_pos hx0 (Fm.L x i).sc.eps
  have e2 := Real.rpow_pos_of_pos hx0 (-(Fm.L x i).sc.eps)
  change 0 ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps * (((Fm.D x i).R.f : ℝ) * (Fm.D x i).R.m * (Fm.L x i).sc.b *
    (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps + (Fm.L x i).Nc)
  have hb0 : 0 < (Fm.L x i).sc.b := Real.exp_pos _
  unfold SizeData₂.Nc budgetNc rankBudget bSize
  positivity
end GlobalTheory.BigOn
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RefTheta
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FactorDepth GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop
namespace GlobalTheory.RefSum
section Free
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) {c : Coeff l} {p : ℕ} [Fact p.Prime]
end Free
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
end Point
def SumPtAlt : Prop := _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i PP C => (i : ℕ) + 1 < (Fm.D x ι).R.m → ∀ u1, Quo p i PP u1 → SumAt p i PP C u1
def ReferenceCore : Prop := _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i PP C => (i : ℕ) + 1 < (Fm.D x ι).R.m → ∀ u1, Quo p i PP u1 →
  RefAt p i (p.T.U ((i : ℕ) + 1)) (GOf p i u1) PP C
def ReferenceTheta : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y PP C => ∀ u1, Quo p i PP u1 → RefAt p i Y.U (GOf p i u1) PP C
def ReferenceWeight : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y PP C => ∀ u1, Quo p i PP u1 → RefAt p i Y.U (wtOf (dat p i) u1 0) PP C
end GlobalTheory.RefSum
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RanksAndFrameOfTiedClass
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExactRanksAlongTiedFamily
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions
namespace GlobalTheory
theorem exact_ranks_along_tied_family_alt : (∀ D : D7, RT.MassRatioUnderVolume D) → ∀ (eps : ℝ) (Fm : FamP eps), _root_.Formalism.L2.TwistSelectionFunctions Fm →
    ∀ C0 Cg cb Cu cT CT : ℝ, PX.RanksF Fm C0 Cg cb Cu cT CT := by
  intro hU eps Fm s C0 Cg cb Cu cT CT
  refine ⟨max s.1 (Fm.x1 + 1), fun x hx i hh => ?_⟩
  have hx1 : Fm.x1 < x := lt_of_lt_of_le (lt_add_one _) (le_trans (le_max_right _ _) hx)
  have R := s.2 x hx1 (le_trans (le_max_left _ _) hx) i
  have hr := R.T.theta.real
  have hm : ∀ u, StandardLattice.Mu0Tie (Fm.D x i) u := GlobalTheory.T.rankCondition_of_columns_equal_symmetricLevel _ R.T.cols
  have h4f : StandardLattice.Conclusion4f (Fm.D x i) (Fm.ex x hx1 i).lev :=
    StandardLattice.HarishChandraReduction.rankFormula_of_classNumber _ _ (ColClassNumber.classNumber_all _ _)
  obtain ⟨-, -, -, -, -, -, -, -, hT, -, h0, h1, -⟩ := hh.1
  have hS : ∀ j, StandardLattice.SplitsF (Fm.D x i) ((Fm.D x i).host.g j) :=
    Fin.forall_fin_two.2 ⟨RankSplit.splitsF_of_norm _ _ ((Fm.D x i).host.g_prime 0) h0,
      RankSplit.splitsF_of_norm _ _ ((Fm.D x i).host.g_prime 1) h1⟩
  exact exact_ranks_of_record (Fm.D x i) hS (RankVolume.definiteSpaceVolume_eq_mass_of_volumeComparison (fun D => hU D) _ hr)
    (StandardLattice.factDstar_fam Fm x hx1 i)
    (fun u => h4f (first_type_prime_large_of_record _) hS u
      (RankSplit.splitsF_of_norm _ _ ((Fm.D x i).mem u).A.T_prime (hT u).1) (hm u))
end GlobalTheory
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RanksAndFrameOfTiedClass
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions
namespace GlobalTheory
theorem ranks_and_frame_of_tied_class_alt : (∀ D : D7, RT.MassRatioUnderVolume D) → ∀ (𝒞 : FamClass), _root_.Formalism.L2.TwistSelection 𝒞 →
    (Closed 𝒞 fun Fm _ => PX.RanksF Fm 3 (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu) ∧
      Closed 𝒞 fun Fm _ => PX.TFrame Fm (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu 3 := by
  intro hU 𝒞 sel
  have hR : Closed 𝒞 fun Fm _ => PX.RanksF Fm 3 (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu :=
    Formalism.MainNotions.Pk.Closed.of_class fun Fm _ hc =>
      _root_.GlobalTheory.exact_ranks_along_tied_family_alt hU _ Fm (sel Fm hc) _ _ _ _ _ _
  exact ⟨hR, GlobalTheory.tFrame_of_ranksRow_three 𝒞 hR⟩
end GlobalTheory
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RanksAndFrameOfTiedClassStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ranksF_tFrame_closed_of_mass_ratio : (∀ D : D7, RT.MassRatioUnderVolume D) → ∀ (𝒞 : FamClass), _root_.Formalism.L2.TwistSelection 𝒞 → (Closed 𝒞 fun Fm _ => PX.RanksF Fm 3 (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu) ∧ Closed 𝒞 fun Fm _ => PX.TFrame Fm (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu 3 := by
  first | exact @_root_.GlobalTheory.ranks_and_frame_of_tied_class_alt | exact _root_.GlobalTheory.ranks_and_frame_of_tied_class_alt | (intros; apply _root_.GlobalTheory.ranks_and_frame_of_tied_class_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalShareCountLeExp
set_option synthInstance.maxHeartbeats 200000

section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.CovTop.LocShareNum
open Formalism.MainNotions.ArithmeticCylinders (admLq TieAdmG eUk eJk locShare goodAt VecAt IsLabel)
open _root_.Formalism.L2.GlobalTheoryTheory.ConcN (Wg SizesRec SizesAt weight_numbers_bound)
open _root_.Formalism.L2.GlobalTheoryTheory.ConcNWeight (RangeW host_facts sum_wtOf eUk_coeff_one_re_pos eJk_coeff_one_re_pos wtOf_eq_zero_of_not_label rangeW_of_sizes)
end GlobalTheory.CovTop.LocShareNum
namespace GlobalTheory.CovTop.LocShareNum
open Formalism.MainNotions.ArithmeticCylinders (admLq TieAdmG eUk eJk locShare goodAt VecAt IsLabel)
open _root_.Formalism.L2.GlobalTheoryTheory.ConcN (Wg SizesRec SizesAt weight_numbers_bound)
open _root_.Formalism.L2.GlobalTheoryTheory.ConcNWeight (RangeW rangeW_of_sizes)
theorem local_share_count_le_exp_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GreenCuspidal → _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι _ _ _ _ => ∃ ψ₀ : ∀ k : Fin 2, AddChar (ZMod ((Fm.D x ι).host.g k)) ℂ, (∀ k, ψ₀ k ≠ 1) ∧ ∀ S : ∀ k : Fin 2, Finset (Formalism.MainNotions.ArithmeticCylinders.Tup (Fm.D x ι) k), (∀ k, ∀ t ∈ S k, ¬ Formalism.MainNotions.ArithmeticCylinders.goodAt (Fm.D x ι) k t) → Formalism.MainNotions.ArithmeticCylinders.locShare (Fm.D x ι) (fun k _ => Formalism.MainNotions.ArithmeticCylinders.eUk (Fm.D x ι) k (ψ₀ k)) 0 (S 0) + Formalism.MainNotions.ArithmeticCylinders.locShare (Fm.D x ι) (fun k _ => Formalism.MainNotions.ArithmeticCylinders.eUk (Fm.D x ι) k (ψ₀ k)) 1 (S 1) ≤ Real.exp (-((Fm.L x ι).sc.x ^ ((Fm.L x ι).sc.ez / 7))) := by
  intro _hP hG
  refine ⟨1 / 52, by norm_num, fun eps he he1 => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ => ⟨0, le_rfl, ?_⟩⟩⟩
  have hez : 0 < Fm.ez := div_pos he (lt_of_lt_of_le one_pos Fm.toFamCore.one_le_J)
  have hez1 : Fm.ez ≤ 1 := le_trans (div_le_self he.le Fm.toFamCore.one_le_J) (by linarith)
  obtain ⟨a, ha⟩ := wg_sum_le Fm.ez hez hez1
  refine ⟨max (max a (Fm.x1 + 1)) (max 4 ((3 / 2 : ℝ) ^ (1 / Fm.ez))), fun x hx hle ι p hp _ => ?_⟩
  have hx4 : 4 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hle
  have hxa : a ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hle
  have hx1 : (3 / 2 : ℝ) ^ (1 / Fm.ez) ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hle
  have hxe : 3 / 2 ≤ x ^ Fm.ez := by
    have hpos : 0 ≤ (3 / 2 : ℝ) ^ (1 / Fm.ez) := by positivity
    calc (3 / 2 : ℝ) = ((3 / 2 : ℝ) ^ (1 / Fm.ez)) ^ Fm.ez := by
          rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hez.ne', Real.rpow_one]
      _ ≤ x ^ Fm.ez := Real.rpow_le_rpow hpos hx1 hez.le
  have hS := sizesRec_at_point Fm hx hx4 ι (le_refl (6 : ℝ))
  have hR := rangeW_of_sizes hS hxe
  have hL := GlobalTheory.GLq.lemmaL_series_weights_of_greenCuspidalParametrisation hG _ hp.2.2
  dsimp only
  rw [Fm.L_x x ι hx, Fm.toFamCore.L_ez x ι]
  have hψ := stdAddChar_ne_one (Fm.D x ι)
  refine ⟨fun k => @ZMod.stdAddChar _ ⟨((Fm.D x ι).host.g_prime k).ne_zero⟩, hψ, fun S hS' => ?_⟩
  have h0 := locShare_eUk_le_Wg hL (tieAdmG_rec _) hR _ hψ 0 (S 0) (hS' 0)
  have h1 := locShare_eUk_le_Wg hL (tieAdmG_rec _) hR _ hψ 1 (S 1) (hS' 1)
  have h2 := ha x hxa _ hS
  linarith
end GlobalTheory.CovTop.LocShareNum
end
end
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_share_number_bound_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GreenCuspidal → _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι _ _ _ _ => ∃ ψ₀ : ∀ k : Fin 2, AddChar (ZMod ((Fm.D x ι).host.g k)) ℂ, (∀ k, ψ₀ k ≠ 1) ∧ ∀ S : ∀ k : Fin 2, Finset (Formalism.MainNotions.ArithmeticCylinders.Tup (Fm.D x ι) k), (∀ k, ∀ t ∈ S k, ¬ Formalism.MainNotions.ArithmeticCylinders.goodAt (Fm.D x ι) k t) → Formalism.MainNotions.ArithmeticCylinders.locShare (Fm.D x ι) (fun k _ => Formalism.MainNotions.ArithmeticCylinders.eUk (Fm.D x ι) k (ψ₀ k)) 0 (S 0) + Formalism.MainNotions.ArithmeticCylinders.locShare (Fm.D x ι) (fun k _ => Formalism.MainNotions.ArithmeticCylinders.eUk (Fm.D x ι) k (ψ₀ k)) 1 (S 1) ≤ Real.exp (-((Fm.L x ι).sc.x ^ ((Fm.L x ι).sc.ez / 7))) := by
  first | exact @_root_.GlobalTheory.CovTop.LocShareNum.local_share_count_le_exp_alt | exact _root_.GlobalTheory.CovTop.LocShareNum.local_share_count_le_exp_alt | (intros; apply _root_.GlobalTheory.CovTop.LocShareNum.local_share_count_le_exp_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadsOfVal
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Col Formalism.IndefR Formalism.IndefR.Links NumberField IsDedekindDomain
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MiS GlobalTheory.Fam GlobalTheory.Core.Rk.Top
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.TopVal
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre}
variable {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)}
variable {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex)
def ValEqvAlt (c : Val B →ₛₗ[B.embLL] (_root_.GlobalTheory.Fam.pk_z W).cX.W) : Prop :=
  ∀ (γ : GQ (I.rec7 l Z).sp.X') γE (g : GL (Fin (B.R.N B.R.m - 1)) B.fields.E), Bridge.IsRatMat (I.rec7 l Z).sp.X' γ γE →
    GlobalTheory.Mem.R3.MatEq (A := B.fields.E) γE g → ∀ v, c (rhoV B.fields.emb B.wts.sgTrue g v) = (_root_.GlobalTheory.Fam.pk_z W).cX.ρ γ.1 (c v)
def packageAtPoint (t : W.P.T) (x : W.P.A3.A.fam.amb.FR t) (h : GA (I.rec7 l Z) (I.rec7 l Z).sp.X') : (_root_.GlobalTheory.Fam.pk_z W).cX.W :=
  ((_root_.GlobalTheory.Fam.pk_z W).HX t).e ((_root_.GlobalTheory.Fam.pk_z W).jX t x) ((finHom (I.rec7 l Z).sp.X').rangeRestrict h)
def PackageValuation (c : Val B →ₛₗ[B.embLL] (_root_.GlobalTheory.Fam.pk_z W).cX.W) : Prop :=
  ∀ (t : W.P.T) (φ : Frm I (W.P.I.tup t)) (x : W.P.A3.A.fam.amb.FR t), IsRes φ x →
    ∀ h y, HasMat h y → IsUni B y → _root_.GlobalTheory.TopVal.packageAtPoint W t x h = c (val φ (latOf I (W.P.I.tup t) y))
def ValuationCompatible (c : Val B →ₛₗ[B.embLL] (_root_.GlobalTheory.Fam.pk_z W).cX.W) (j : SmT (_root_.GlobalTheory.Fam.pk_z W).MX →ₗ[ℂ] (Formalism.L2.Forms.FrP (I.rec7 l Z) → ℂ)) : Prop :=
  ∀ w v, (_root_.GlobalTheory.Fam.pk_z W).prX (c w) v = pairVal B (j v) w
end GlobalTheory.TopVal
end
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Col Formalism.IndefR Formalism.IndefR.Links NumberField IsDedekindDomain
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MiS GlobalTheory.Fam GlobalTheory.Core.Rk.Top
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.TopVal
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X}
variable {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex)
set_option maxHeartbeats 1000000 in
theorem reads_of_pairVal (hC : I.StdC l Z W.R.T.cols) (hW : _root_.GlobalTheory.AdForm.TwStdAlt W) (u : B.Word)
    (j : SmT (_root_.GlobalTheory.Fam.pk_z W).MX →ₗ[ℂ] (Formalism.L2.Forms.FrP (I.rec7 l Z) → ℂ)) (a : (I.rec7 l Z).what₂.Tup) (φ : Frm I a)
    (G : (I.rec7 l Z).what₂.Amb a) (hG : RecVal u a φ G)
    (f : SmT (_root_.GlobalTheory.Fam.pk_z W).MX →ₗ[ℂ] (GA (I.rec7 l Z) (I.rec7 l Z).sp.X' → ℂ))
    (hf : ∀ h y (p : XPt (B.primes X) B.R I.sel (I.tup a)) v, HasMat h y → TC.PtOf y p →
      f v h = pairVal B (j v) (val φ (toRow I.sel (I.tup a) p))) :
    _root_.GlobalTheory.Fam.ReadsCoefficients W u j 1 a G f := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · subst h
    intro c v g hg
    have s := hC u
    rw [mul_one, hf g _ _ v hg (s.what₂.pt c)]
    have e := fun c' y => (s.eW ((W.R.T.cols.forms u).valP.eW.symm (Pi.single c (j v))) c' y y rfl).symm
    simp only [LinearEquiv.apply_symm_apply] at e
    refine (period_single l u I.mu0 φ _ (hG.1 rfl) c (j v) _ (funext fun y => (e c y).trans ?_)
      fun c' hc => funext fun y => (e c' y).trans ?_).symm
    · rw [Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne' (fun e => hc e.symm : ¬ c = c')]
      rfl
  · obtain ⟨l0, t, he, ht, -, -, s⟩ := hW
    have key : ∀ (Tw : TwForms (I.rec7 l Z)) (t' : Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes W.R.T.n.tp W.R.T.cols Tw), Tw = I.tw l l0 Z → HEq t' t →
        ReadsG (t'.pt.cls u a h) (t'.pt.val u a h).eW j 1 (((I.rec7 l Z).eMtTw u a).symm G) f := by
      rintro _ t' rfl rfl
      intro c v g hg
      rw [mul_one, hf g _ _ v hg ((s.what₂ u a h).pt c)]
      have e := fun c' y => (s.eW u a h ((t'.pt.val u a h).eW.symm (Pi.single c (j v))) c' y y rfl).symm
      simp only [LinearEquiv.apply_symm_apply] at e
      refine (period_single l u a φ _ hG.2 c (j v) _ (funext fun y => (e c y).trans ?_)
        fun c' hc => funext fun y => (e c' y).trans ?_).symm
      · rw [Pi.single_eq_same]
      · rw [Pi.single_eq_of_ne' (fun e => hc e.symm : ¬ c = c')]
        rfl
    exact key _ _ he ht
end GlobalTheory.TopVal
end
end
end
