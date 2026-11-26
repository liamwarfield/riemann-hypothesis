module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringTopologyRefinement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.TamagawaPeterssonLambdaSqNonneg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformisationComponentsCovolumeEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModModT
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringDomainLatticeRegularity
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.PlugPairs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneLeDimAtStatement

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ProportionalityPrincipleCompactification
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
namespace GlobalTheory.CompProport
theorem hirzebruch_proportionality_toroidal :
    _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → Proport Y.U ∧ ∀ Z, 0 < CompHt.vZero Y.U Z := by
  intro hP hS hT hL D T _ j hp _ hf _ Y e o hY
  have hr : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by omega
  obtain ⟨X, h1, h2, h3, h4⟩ := hT.exists_model_charts hS hr Y.d.Xo₂ Y.d.c₂
  obtain ⟨TF, hc⟩ := exists_torFlag_charts hr X h1 h2 h3 h4
  exact _root_.GlobalTheory.CompProport.proportionality_of_local_charts (_root_.GlobalTheory.T.covering_topology_refinement hP) hP.q7 hL hY hf TF hc
end GlobalTheory.CompProport
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.proportionality_principle_compactification : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → Proport Y.U ∧ ∀ Z, 0 < CompHt.vZero Y.U Z := by
  first | exact @_root_.GlobalTheory.CompProport.hirzebruch_proportionality_toroidal | exact _root_.GlobalTheory.CompProport.hirzebruch_proportionality_toroidal | (intros; apply _root_.GlobalTheory.CompProport.hirzebruch_proportionality_toroidal <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.IntegralCuspSlopePowerBound
section
section
noncomputable section
namespace UpperTheory.Lit.Tam
end UpperTheory.Lit.Tam
end
end
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal
namespace GlobalTheory.SupModel
open Classical
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
end GlobalTheory.SupModel
end
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal
noncomputable section
namespace GlobalTheory.LevGeo.RankBd
variable {D : D7} {r : ℕ} {Comp : Type} [Fintype Comp] {X : Comp → Data D.host.E r}
open scoped TensorProduct
open scoped TensorProduct
variable {D : D7} {r : ℕ} {Comp : Type} [Fintype Comp] {X : Comp → Data D.host.E r}
open Module
end GlobalTheory.LevGeo.RankBd
end
end
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal
namespace GlobalTheory.LamPet
open scoped ENNReal
end GlobalTheory.LamPet
end
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal
set_option synthInstance.maxHeartbeats 400000
namespace GlobalTheory.LamMuMax
end GlobalTheory.LamMuMax
end
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal
namespace GlobalTheory
end GlobalTheory
end
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal
namespace GlobalTheory
end GlobalTheory
end
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
namespace GlobalTheory.BergComp
open MeasureTheory
end GlobalTheory.BergComp
end
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
namespace GlobalTheory.ConstSzRows
end GlobalTheory.ConstSzRows
end
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
namespace GlobalTheory.BergRank
open ReciprocityTheory.ChartRestriction.G.FD
end GlobalTheory.BergRank
namespace GlobalTheory.BergRank
theorem _root_.UpperTheory.Lit.Tam.tamagawa_number_formula : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ Lb : ℝ, 1 ≤ Lb → Real.log Y.d.l₂.M ≤ 30 * Lb → fieldSz D.host.E ≤ 3 * Lb → Real.log (D.R.f * D.R.r) ≤ Lb → o ≤ 391 * (D.R.f * D.R.r * Lb) ^ 2 → ∀ la : AllWt.Weight (T.Q.Dw j), (∀ τ, Antitone (la τ)) → Real.log (∑ τ, ∑ k, |(la τ k : ℝ)|) ≤ 20 * Lb → ∀ Z, BergLe Z Y.U (fun _ => D.sp.W j) Y.dict la (Real.exp (C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 3)) ∧ SupBdWt Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z la (Real.exp (C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 3)) ∧ Real.log (Y.rkC la Z) ≤ C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 3 := by
  intro hP
  refine ⟨4000, by norm_num, ?_⟩
  intro D T hT j hp hq hE hj Y e o hY Lb hLb hM hsz hfr ho la hla hS Z
  have hL := (GlobalTheory.T.deepLevelCover_principalLevel_laws_galois D T j Y e o hT hj hY hY.unit hY.modelW).1
  set S : ℝ := ∑ τ, ∑ k, |(la τ k : ℝ)| with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  set n : ℝ := (Module.finrank ℚ D.host.E : ℝ) with hn
  have hn1 : 1 ≤ n := by
    have : 0 < Module.finrank ℚ D.host.E := Module.finrank_pos
    rw [hn]; exact_mod_cast this
  have hnlog : Real.log n ≤ 3 * Lb := (log_finrank_le_fieldSz _).trans hsz
  set w : ℝ := 2 * n * S + 1 with hw
  have hnS : 0 ≤ n * S := mul_nonneg (by linarith) hS0
  have hw1 : 1 ≤ w := by rw [hw]; nlinarith
  have hlogw : Real.log w ≤ 25 * Lb := by
    have hint : S = (((∑ τ, ∑ k, |la τ k|) : ℤ) : ℝ) := by rw [hSdef]; push_cast; rfl
    have hz : (0 : ℤ) ≤ ∑ τ, ∑ k, |la τ k| := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
    rcases hz.eq_or_lt with h0 | h1
    · have : S = 0 := by rw [hint, ← h0]; simp
      rw [hw, this]; simp; linarith
    · have hS1 : 1 ≤ S := by rw [hint]; exact_mod_cast h1
      have hwle : w ≤ 3 * (n * S) := by rw [hw]; nlinarith
      have hlS : Real.log S ≤ 20 * Lb := hS
      have e1 : Real.log w ≤ Real.log (3 * (n * S)) := Real.log_le_log (by linarith) hwle
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_mul (by positivity) (by positivity)] at e1
      have h3 : Real.log 3 < 2 := by
        have := Real.log_two_lt_d9; have h4 : Real.log 3 < Real.log 4 := Real.log_lt_log (by norm_num) (by norm_num)
        have : Real.log 4 = 2 * Real.log 2 := by rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
        linarith
      linarith
  obtain ⟨hβ1, hβ⟩ := UpperTheory.Lit.Tam.supConst2Bounds D Y.d.l₂.M Lb w (by have := Y.d.l₂.three_le; omega) hLb hM hsz hfr hw1 hlogw
  set β := MainStatements.Tam.Plug.supConst2 D.host.E D.R.r D.host.d Y.d.l₂.M w with hβdef
  have hβexp : β ≤ Real.exp (4000 * ((D.R.f : ℝ) * D.R.r * Lb) ^ 3) := by
    rw [← Real.exp_log (by linarith : 0 < β)]; exact Real.exp_le_exp.2 hβ
  have hsp : ∀ σ k, ∑ τ, ((Y.U σ).X k).spread (AllWt.modelWt (Y.U σ) (wtOf _ la 0) k) τ ≤ w := fun σ k =>
    (sum_spread_modelWt_le _ la k).trans (by rw [hw]; linarith)
  have hB : BergLe Z Y.U (fun _ => D.sp.W j) Y.dict la β := fun σ hσ y hy =>
    UpperTheory.Lit.Tam.tamagawaPeterssonLambdaSq_nonneg trivial D j _ _ _ _ _ Y.U Y.dict hL σ hσ (wtOf _ la 0) (AllWt.even_wtOf la 0) w (by linarith) (hsp σ) Z y hy
  have hBexp : BergLe Z Y.U (fun _ => D.sp.W j) Y.dict la (Real.exp (4000 * ((D.R.f : ℝ) * D.R.r * Lb) ^ 3)) :=
    fun σ hσ y hy => (hB σ hσ y hy).trans (ENNReal.ofReal_le_ofReal hβexp)
  refine ⟨hBexp, ?_, ?_⟩
  · refine SupBdWt.of_bergOn (Real.exp_pos _).le ?_ hBexp
    intro σ hσ g
    obtain ⟨th, hr, -, hd⟩ := hY.dictU σ hσ
    exact Formalism.L2.Pj.dict_dom_of hd g
  · have hrk := GlobalTheory.T.cuspFormRank_le_bergmanBound_goodCover D T.toCore j Y e o hY la Z β (by linarith) hB
    have hpos : 0 ≤ 4000 * ((D.R.f : ℝ) * D.R.r * Lb) ^ 3 := by positivity
    rcases (show (0 : ℝ) ≤ Y.rkC la Z by unfold Deep.rkC; positivity).eq_or_lt with h0 | h0
    · rw [← h0, Real.log_zero]; exact hpos
    · exact (Real.log_le_log h0 hrk).trans hβ
end GlobalTheory.BergRank
end
section
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
namespace GlobalTheory.CovTop.LamCore
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
end GlobalTheory.CovTop.LamCore
end
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CompactificationTopChernEqVolume
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
namespace GlobalTheory.CompEqVol
theorem equal_volume_of_compactification : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → EqVolume Y.U := by
  intro hP2 hS hKS hSA D T hT j hp hq hf hj Y e o hY
  have hr : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by omega
  obtain ⟨M, hs, hb, hk, hc⟩ := hKS.exists_model_charts hS hr Y.d.Xo₂ Y.d.c₂
  obtain ⟨TF, hTF⟩ := GlobalTheory.CompProport.exists_torFlag_charts hr M hs hb hk hc
  have hσ : GoodEmb Y.d.c₂ Y.d.c₂.F.val.toRingHom := rfl
  obtain ⟨-, q, -, hv⟩ := _root_.GlobalTheory.CompProport.invariant_volume_eq_covolume (_root_.GlobalTheory.T.covering_topology_refinement hP2) hP2.q7 hSA hY hf TF hTF hσ
  have hg0 : ∀ p : ℕ, p.Prime → T.Q.l.GoodAt p :=
    Formalism.L2.Pj.goodAt_of_two_primes hT.pins.2.1.1 (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne
  have hg : ∀ p : ℕ, p.Prime → Y.d.l₂.GoodAt p := GlobalTheory.LawsDeep.goodAt_of_mul _ _ _ hY.lev.1.2.1 hg0
  have hcov := GlobalTheory.T.complexUniformisation_components_covolume_eq _ _ _ _ _ _ _ _ (Formalism.L2.PjFree.Unf.ofPj (Y.U Y.d.c₂.F.val.toRingHom)) hσ
    ((Formalism.L2.PjFree.isUnf_ofPj _).2 (hY.unf _ hσ)) hg hp hq
  intro Z Z'
  obtain ⟨k, rfl⟩ := q.surjective Z
  obtain ⟨k', rfl⟩ := q.surjective Z'
  rw [hv, hv]
  exact congrArg (fun x => x * _ / _) (hcov k k')
end GlobalTheory.CompEqVol
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactification_top_chern_eq_volume : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → EqVolume Y.U := by
  first | exact @_root_.GlobalTheory.CompEqVol.equal_volume_of_compactification | exact _root_.GlobalTheory.CompEqVol.equal_volume_of_compactification | (intros; apply _root_.GlobalTheory.CompEqVol.equal_volume_of_compactification <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringShiftPreservesGoodAt
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.WeightLatticeSpannedByWeights
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
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace GlobalTheory.GenShift
open IsDedekindDomain ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw
section General
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}
  {Z : Comp Xo c}
end General
theorem span_weight_lattice_of_weights : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ (la : GlobalTheory.AllWt.Weight (T.Q.Dw j)), (∀ τ, Antitone (la τ)) → (∀ τ, 1 ≤ gap (la τ) ((T.Q.Dw j).p - 1)) → (∀ k : ℕ, Y.GoodAt (wtOf _ ((k + 1) • la) 0)) → ∀ m : ℕ, Submodule.span Y.d.c₂.F (GlobalTheory.AllWt.latW Y.U (wtOf _ la m) : Set (Y.V (wtOf _ la m))) = ⊤ := by
  intro _ D T hT j hp _ _ hj Y e o hG la _ _ hgood m
  have hg0 : ∀ p : ℕ, p.Prime → T.Q.l.GoodAt p :=
    Formalism.L2.Pj.goodAt_of_two_primes hT.pins.2.1.1 (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne
  have hg : ∀ p : ℕ, p.Prime → Y.d.l₂.GoodAt p := GlobalTheory.LawsDeep.goodAt_of_mul _ _ _ hG.lev.1.2.1 hg0
  have hs : ∀ Z : Comp Y.d.Xo₂ Y.d.c₂, Nonempty (TwSec Y.U (xiR D) Z (wtOf (T.Q.Dw j) 0 (m : ℤ))) := fun Z => by
    obtain ⟨s⟩ := GlobalTheory.KeyTwDeep.twSec_keyRoot _ _ _ _ _ _ _ _ _ hG.unf hG.xiAbs hG.geo (le_add_right hp) hg Z
    exact exists_twPow s m
  have h0 := (hgood 0).2.2
  rw [zero_add, one_smul] at h0
  have key := span_latW_add hG.unf (wtOf (T.Q.Dw j) la 0) (wtOf (T.Q.Dw j) 0 (m : ℤ)) (even_wtOf _ _) hs h0
  have hGG : wtOf (T.Q.Dw j) la 0 + wtOf (T.Q.Dw j) 0 (m : ℤ) = wtOf (T.Q.Dw j) la (m : ℤ) := by
    rw [← wtOf_add, add_zero, zero_add]
  rw [hGG] at key
  exact key
end GlobalTheory.GenShift
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
set_option synthInstance.maxHeartbeats 400000 in
theorem _root_.GlobalTheory.T.weight_lattice_spanned_by_weights : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ (la : GlobalTheory.AllWt.Weight (T.Q.Dw j)), (∀ τ, Antitone (la τ)) → (∀ τ, 1 ≤ gap (la τ) ((T.Q.Dw j).p - 1)) → (∀ k : ℕ, Y.GoodAt (wtOf _ ((k + 1) • la) 0)) → ∀ m : ℕ, Submodule.span Y.d.c₂.F (GlobalTheory.AllWt.latW Y.U (wtOf _ la m) : Set (Y.V (wtOf _ la m))) = ⊤ := by
  first | exact @_root_.GlobalTheory.GenShift.span_weight_lattice_of_weights | exact _root_.GlobalTheory.GenShift.span_weight_lattice_of_weights | (intros; apply _root_.GlobalTheory.GenShift.span_weight_lattice_of_weights <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ShiftedWeightLatticeFg
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
open GlobalTheory.LamT (CMPt)
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace GlobalTheory.CovTop.ShiftFG
set_option maxHeartbeats 1000000 in
theorem weight_lattice_pow_fg : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q →
    2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o →
    ∀ (la : GlobalTheory.AllWt.Weight (T.Q.Dw j)), (∀ τ, Antitone (la τ)) → (∀ τ, 1 ≤ gap (la τ) ((T.Q.Dw j).p - 1)) →
    (∀ k : ℕ, Y.GoodAt (wtOf _ ((k + 1) • la) 0)) → ∀ m : ℕ, (GlobalTheory.AllWt.latW Y.U (wtOf _ la m)).FG := by
  intro _ D T _ j hp hq _ _ Y e o hY la hA hb _ m
  letI := T.Q.H.starRing
  haveI := GlobalTheory.Deep.finiteDimensional_V_of_good D T.toCore j Y e o hY (wtOf _ la m)
  refine GlobalTheory.fg_of_integral_functionals Y.d.c₂.F (Y.V (wtOf _ la m)) _ fun x hx => ?_
  obtain ⟨z, La, y, hz, hyx, hne⟩ := exists_good_cmPt_frame_ne_zero Y hY (fun _ => rfl) _ x.1 x.2
    (fun h => hx (Subtype.ext h))
  obtain ⟨N, hN, hint⟩ := GlobalTheory.T.exists_frame_denominator_dominant_weight_power_cm _ _ _ _ _ _ z _ La hz y hyx hp hq la hA hb m
  refine ⟨z.K, inferInstance, inferInstance, inferInstance,
    { toFun := fun F => N * evR Y.d.Xo₂ Y.d.c₂ F.1 y
      map_add' := fun F G => ?_
      map_smul' := fun s F => ?_ }, mul_ne_zero hN hne, fun F hF => hint F.1 (GlobalTheory.AllWt.cuspW_le_secZ _ F.2) hF⟩
  · rw [← mul_add]
    exact congrArg _ (evalAt_add _ _ F.1 G.1 y)
  · have e1 : evR Y.d.Xo₂ Y.d.c₂ (s • F).1 y = algebraMap Y.d.c₂.F z.K s * evR Y.d.Xo₂ Y.d.c₂ F.1 y :=
      evalAt_smul _ _ s F.1 y
    rw [e1, RingHom.id_apply, Algebra.smul_def, mul_left_comm]
end GlobalTheory.CovTop.ShiftFG
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
theorem _root_.GlobalTheory.T.shifted_weight_lattice_fg : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ (la : GlobalTheory.AllWt.Weight (T.Q.Dw j)), (∀ τ, Antitone (la τ)) → (∀ τ, 1 ≤ gap (la τ) ((T.Q.Dw j).p - 1)) → (∀ k : ℕ, Y.GoodAt (wtOf _ ((k + 1) • la) 0)) → ∀ m : ℕ, (GlobalTheory.AllWt.latW Y.U (wtOf _ la m)).FG := by
  first | exact @_root_.GlobalTheory.CovTop.ShiftFG.weight_lattice_pow_fg | exact _root_.GlobalTheory.CovTop.ShiftFG.weight_lattice_pow_fg | (intros; apply _root_.GlobalTheory.CovTop.ShiftFG.weight_lattice_pow_fg <;> assumption)
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
noncomputable section
namespace GlobalTheory.CovTop.ShiftGood
variable {D : D7} {T : Core D} {j : ℕ}
end GlobalTheory.CovTop.ShiftGood
namespace GlobalTheory.CovTop.ShiftGood
open MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions.TH in
set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
private theorem exists_semilinear_L2_independent {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
    {c : Coeff l} {r : ℕ} {D : D7} (hS : Out.SecBaseChangeSt) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ : c.F →+* ℂ)
    (hσ : GoodEmb c σ) (hU : IsUnf (U σ)) (V : HSp D)
    (dict : Formalism.L2.Theta.GA D V → Σ k, Frame ((U σ).X k).Ψ r) (mu : Formalism.L2.Theta.GA D V → ℂ)
    (hmu1 : ∀ g, ‖mu g‖ = 1) (hm : Formalism.L2.Pj.AdelMeas U σ V dict mu) (hae : Formalism.L2.Pj.AeDom U σ V dict mu)
    (hd : ∀ g, (dict g).2 ∈ ((U σ).X (dict g).1).dom)
    (hunit : ∀ g τ i, ‖dmin ((U σ).X (dict g).1).Gm (dict g).2 τ i‖ = 1) (G : WTZ E) (x : ℝ) :
    ∃ Φ : GlobalTheory.AllWt.cuspW Xo c U G →+ Lp ℂ 2 (muQ1 V), (∀ (a : c.F) f, Φ (a • f) = σ a • Φ f) ∧
      (∀ f : GlobalTheory.AllWt.cuspW Xo c U G, GlobalTheory.AllWt.petAt (U σ) x V dict (muQ1 V) G (f : Rul Xo c) = ‖Φ f‖) ∧
      ∀ (n : ℕ) (e : Fin n → GlobalTheory.AllWt.cuspW Xo c U G), LinearIndependent c.F e →
        LinearIndependent ℂ (fun i => Φ (e i)) := by
  have hhol : ∀ f : GlobalTheory.AllWt.cuspW Xo c U G,
      rdU (U σ) (f : Rul Xo c) ∈ holSub (U σ).X (GlobalTheory.AllWt.modelWt (U σ) G) := fun f =>
    (GlobalTheory.AllWt.mem_cuspW.1 f.2).2 σ hσ
  have heq : ∀ P : holSub (U σ).X (GlobalTheory.AllWt.modelWt (U σ) G),
      eLpNorm (onQ V (adel V dict mu P)) 2 (muQ1 V) =
        GlobalTheory.AllWt.petE V dict (muQ1 V) (GlobalTheory.AllWt.modelWt (U σ) G) P := by
    intro P
    unfold GlobalTheory.AllWt.petE
    have hp : ∀ q : AutQ V, ‖mu q.out * (P : FDSec (U σ).X) (dict q.out).1 (dict q.out).2‖ =
        GlobalTheory.AllWt.ptN (GlobalTheory.AllWt.modelWt (U σ) G) P (dict q.out) := by
      intro q
      rw [norm_mul, hmu1, one_mul, GlobalTheory.AllWt.ptN,
        pnorm_eq_of_unit _ _ _ _ (hunit q.out)]
    have hf := aesm_of_holSub hm _ P.2
    have hg := hf.norm.congr (Filter.Eventually.of_forall hp)
    have hh := eLpNorm_congr_norm_ae (p := 2) hf hg (Filter.Eventually.of_forall fun q => by
      rw [Real.norm_of_nonneg (GlobalTheory.AllWt.ptN_nonneg _ _ _)]
      exact hp q)
    rw [eLpNorm_eq_eLpNorm' (by norm_num) (by simp) hg] at hh
    simpa using hh
  have hmem : ∀ P : holSub (U σ).X (GlobalTheory.AllWt.modelWt (U σ) G),
      MemLp (onQ V (adel V dict mu (P : FDSec (U σ).X))) 2 (muQ1 V) := fun P =>
    by
      change eLpNorm _ _ _ < ⊤
      rw [heq P]
      exact lt_top_iff_ne_top.2 (GlobalTheory.AllWt.petE_ne_top V dict (muQ1 V) prob_le_one hd P.2)
  let L : holSub (U σ).X (GlobalTheory.AllWt.modelWt (U σ) G) →ₗ[ℂ] Lp ℂ 2 (muQ1 V) :=
    { toFun := fun P => (hmem P).toLp _
      map_add' := fun P Q => by
        rw [← MemLp.toLp_add]
        exact MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq (by rw [Submodule.coe_add, map_add (f := _), map_add (f := _)]))
      map_smul' := fun a P => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        exact MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq (by rw [Submodule.coe_smul, map_smul, map_smul])) }
  have hL : ∀ P, L P = (hmem P).toLp _ := fun _ => rfl
  let R : GlobalTheory.AllWt.cuspW Xo c U G → holSub (U σ).X (GlobalTheory.AllWt.modelWt (U σ) G) := fun f => ⟨_, hhol f⟩
  have hRadd : ∀ f g, R (f + g) = R f + R g := fun f g => Subtype.ext (by
    show rdU (U σ) ((f + g : GlobalTheory.AllWt.cuspW Xo c U G) : Rul Xo c) = rdU (U σ) (f : Rul Xo c) + rdU (U σ) (g : Rul Xo c)
    rw [Submodule.coe_add, map_add (f := _)])
  have hRsm : ∀ (a : c.F) f, R (a • f) = σ a • R f := fun a f => Subtype.ext (by
    show rdU (U σ) ((a • f : GlobalTheory.AllWt.cuspW Xo c U G) : Rul Xo c) = σ a • rdU (U σ) (f : Rul Xo c)
    rw [Submodule.coe_smul, map_smulₛₗ])
  let cf : ℝ := GlobalTheory.AllWt.lieFacZ Dw x G
  have hcf : 0 < cf := GlobalTheory.AllWt.lieFacZ_pos x G
  refine ⟨AddMonoidHom.mk' (fun f => (cf : ℂ) • L (R f)) (fun f g => by rw [hRadd, map_add (f := _), smul_add]),
    fun a f => ?_, fun f => ?_, fun n e he => ?_⟩
  · show (cf : ℂ) • L (R (a • f)) = σ a • ((cf : ℂ) • L (R f))
    rw [hRsm, map_smul, smul_comm]
  · show _ = ‖(cf : ℂ) • L (R f)‖
    rw [norm_smul, hL, Lp.norm_toLp, heq, Complex.norm_real, Real.norm_of_nonneg hcf.le]
    rfl
  · have hb : LinearIndependent c.F (fun i => (e i : Rul Xo c)) :=
      he.map' (GlobalTheory.AllWt.cuspW Xo c U G).subtype (Submodule.ker_subtype _)
    have hc := GlobalTheory.reading_linearIndependent_secZ hS (U σ) hU _ n _
      (fun i => GlobalTheory.AllWt.cuspW_le_secZ G (e i).2) hb
    rw [Fintype.linearIndependent_iff] at hc ⊢
    intro w hw
    refine hc w ?_
    have h1 : (cf : ℂ) • L (∑ i, w i • R (e i)) = 0 := by
      have hw' : ∑ i, w i • ((cf : ℂ) • L (R (e i))) = 0 := hw
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.smul_sum, ← hw']
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [L.map_smul]
      exact smul_comm _ _ _
    have h2 : L (∑ i, w i • R (e i)) = 0 :=
      (smul_eq_zero.1 h1).resolve_left (Complex.ofReal_ne_zero.2 hcf.ne')
    have h3 : onQ V (adel V dict mu ((∑ i, w i • R (e i) : holSub (U σ).X (GlobalTheory.AllWt.modelWt (U σ) G)) :
        FDSec (U σ).X)) =ᵐ[muQ1 V] 0 := by
      refine (MemLp.coeFn_toLp (hmem _)).symm.trans ?_
      rw [← hL, h2]
      exact Lp.coeFn_zero _ _ _
    have h4 := hae _ _ (∑ i, w i • R (e i)).2 h3
    have h5 : ((∑ i, w i • R (e i) : holSub (U σ).X (GlobalTheory.AllWt.modelWt (U σ) G)) : FDSec (U σ).X) =
        ∑ i, w i • rdU (U σ) (e i : Rul Xo c) := by
      rw [Submodule.coe_sum]
      rfl
    rw [h5] at h4
    funext k z
    by_cases hz : z ∈ ((U σ).X k).dom
    · exact h4 k z hz
    · simp [Finset.sum_apply, rdU, hz]
set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
private theorem hasGram_nrm_of_good (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ) (hY : Y.Good e o)
    (G : WTZ D.host.E) : GlobalTheory.AllWt.HasGram (Y.nrm G) := by
  haveI := GlobalTheory.Deep.finiteDimensional_V_of_good D T j Y e o hY G
  refine GlobalTheory.HSApp.hasGram_of_inner Y.d.c₂.F (Y.V G) (Y.nrm G) fun v => ?_
  have hσ' : GoodEmb Y.d.c₂ (Formalism.L2.Pj.goodOf Y.d.c₂ v.embedding) := Formalism.L2.Pj.goodEmb_goodOf _ _
  have hd : ∀ g, (Y.dict (Formalism.L2.Pj.goodOf Y.d.c₂ v.embedding) g).2 ∈
      ((Y.U (Formalism.L2.Pj.goodOf Y.d.c₂ v.embedding)).X (Y.dict (Formalism.L2.Pj.goodOf Y.d.c₂ v.embedding) g).1).dom :=
    fun g => ((hY.dictU _ hσ').choose_spec.choose_spec.2).2.2.2.1 g
  have hex := exists_semilinear_L2_independent GlobalTheory.abelianSchemeLaws_all.1.secBaseChange Y.U _ hσ' (hY.unf _ hσ')
    (D.sp.W j) (Y.dict _) (fun _ => (1 : ℂ)) (fun _ => norm_one)
    (adelMeas_of_aut Y.d.Xo₂ Y.d.c₂ (U := Y.U) (σ := _) (GlobalTheory.PetDef.adelAut_good Y hY _ hσ'))
    (GlobalTheory.PetDef.aeDom_good Y hY _ hσ') hd (hY.unit _ hσ') G (xiR D)
  refine ⟨_, inferInstance, inferInstance, Classical.choose hex, ?_, fun x => (Classical.choose_spec hex).2.1 x,
    (Classical.choose_spec hex).2.2⟩
  by_cases h : GoodEmb Y.d.c₂ v.embedding
  · left
    intro a x
    refine ((Classical.choose_spec hex).1 a x).trans ?_
    exact congrArg (· • Classical.choose hex x) (congrArg (fun τ : Y.d.c₂.F →+* ℂ => τ a) (ite_eq_left h))
  · right
    intro a x
    refine ((Classical.choose_spec hex).1 a x).trans ?_
    exact congrArg (· • Classical.choose hex x) (congrArg (fun τ : Y.d.c₂.F →+* ℂ => τ a) (ite_eq_right h))
theorem covering_goodAt_shift : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (s : ℤ), Even n → (∀ τ, Antitone ((laOf (T.Q.Dw j) a n + s • hodgeWt (T.Q.Dw j)) τ)) → (∀ τ, 1 ≤ gap ((laOf (T.Q.Dw j) a n + s • hodgeWt (T.Q.Dw j)) τ) ((T.Q.Dw j).p - 1)) → Y.GoodAt (shiftG (T.Q.Dw j) a n s) := by
  intro hP D T hT j hp hq hf hj Y e o hY a n s hn hA hg
  obtain ⟨m, rfl⟩ := hn
  have hmul : ∀ k : ℕ, Y.GoodAt (wtOf _ ((k + 1) • (laOf (T.Q.Dw j) a (m + m) + s • hodgeWt (T.Q.Dw j))) 0) := by
    intro k
    refine (_root_.GlobalTheory.T.covering_domain_lattice_regularity hP D T hT j hp hq hf hj Y e o hY _ (fun τ => ?_) (fun τ => ?_)).1
    · intro x y hxy
      simp only [Pi.smul_apply]
      exact nsmul_le_nsmul_right (hA τ hxy) _
    · have := hg τ
      simp only [Pi.smul_apply]
      unfold gap at this ⊢
      split_ifs at this ⊢ with h1
      · simp only [Pi.smul_apply, smul_eq_mul, nsmul_eq_mul] at this ⊢
        have hk : (1 : ℤ) ≤ ((k + 1 : ℕ) : ℤ) := by exact_mod_cast Nat.succ_pos k
        rw [← mul_sub]
        exact this.trans (le_mul_of_one_le_left (by linarith) hk)
      · exact this
  refine goodAt_of_exZ hY ?_ ⟨hasGram_nrm_of_good D T.toCore j Y e o hY _,
    _root_.GlobalTheory.T.shifted_weight_lattice_fg hP D T hT j hp hq hf hj Y e o hY _ hA hg hmul m,
    _root_.GlobalTheory.T.weight_lattice_spanned_by_weights hP D T hT j hp hq hf hj Y e o hY _ hA hg hmul m⟩
  rw [← two_mul, GlobalTheory.CovTop.Model.exZ_shiftG]
  rfl
end GlobalTheory.CovTop.ShiftGood
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
theorem _root_.GlobalTheory.T.covering_shift_preserves_goodAt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (s : ℤ), Even n → (∀ τ, Antitone ((laOf (T.Q.Dw j) a n + s • hodgeWt (T.Q.Dw j)) τ)) → (∀ τ, 1 ≤ gap ((laOf (T.Q.Dw j) a n + s • hodgeWt (T.Q.Dw j)) τ) ((T.Q.Dw j).p - 1)) → Y.GoodAt (shiftG (T.Q.Dw j) a n s) := by
  first | exact @_root_.GlobalTheory.CovTop.ShiftGood.covering_goodAt_shift | exact _root_.GlobalTheory.CovTop.ShiftGood.covering_goodAt_shift | (intros; apply _root_.GlobalTheory.CovTop.ShiftGood.covering_goodAt_shift <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.NormalizedCovolumeEqOne
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.VolumeFundamentalDomainNeTopOfFiniteCovolume
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta
namespace GlobalTheory.CovTop.MeasFin
theorem volume_fundamentalDomain_ne_top_of_finite_covolume : ∀ (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (D : D7) (Tu : Type) (C : LevCh D Tu) (t0 : Tu) (hC : C.Is t0) (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ) (μ : MeasureTheory.Measure (GA D (Wc D i))) (𝓕 : Set (GA D (Wc D i))) (hF : IsMeasFD (Wc D i) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW C i P) μ 𝓕), μ 𝓕 ≠ ⊤ :=
  fun _ _ _ _ _ _ _ _ μ 𝓕 hF => measure_ne_top_of_isMeasFD _ _ μ 𝓕 hF
end GlobalTheory.CovTop.MeasFin
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_measure_lt_top_of_finite_covolume : ∀ (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (D : D7) (Tu : Type) (C : LevCh D Tu) (t0 : Tu) (hC : C.Is t0) (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ) (μ : MeasureTheory.Measure (GA D (Wc D i))) (𝓕 : Set (GA D (Wc D i))) (hF : IsMeasFD (Wc D i) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW C i P) μ 𝓕), μ 𝓕 ≠ ⊤ := by
  first | exact @_root_.GlobalTheory.CovTop.MeasFin.volume_fundamentalDomain_ne_top_of_finite_covolume | exact _root_.GlobalTheory.CovTop.MeasFin.volume_fundamentalDomain_ne_top_of_finite_covolume | (intros; apply _root_.GlobalTheory.CovTop.MeasFin.volume_fundamentalDomain_ne_top_of_finite_covolume <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.HaarMeasureFundamentalDomainNeZeroOfCocompact
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta
namespace GlobalTheory.CovTop
theorem haarMeasure_fundamentalDomain_ne_zero_of_cocompact : ∀ (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (D : D7) (Tu : Type) (C : LevCh D Tu) (t0 : Tu) (hC : C.Is t0) (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ) (μ : MeasureTheory.Measure (GA D (Wc D i))) (𝓕 : Set (GA D (Wc D i))) (hF : IsMeasFD (Wc D i) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW C i P) μ 𝓕), μ 𝓕 ≠ 0 := by
  intro _ D Tu C t0 _ i P μ 𝓕 hF h0
  haveI : IsTopologicalGroup (GA D (Wc D i)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : BorelSpace (GA D (Wc D i)) := ⟨rfl⟩
  haveI : Countable (GQ (Wc D i)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig (Wc D i).gram
  haveI : μ.IsHaarMeasure := hF.1.1
  have h1 : μ Set.univ = 0 := by
    rw [hF.2.measure_eq_tsum Set.univ]
    refine ENNReal.tsum_eq_zero.2 fun g => ?_
    rw [Set.smul_set_univ, Set.univ_inter, h0]
  exact (isOpen_univ.measure_pos μ Set.univ_nonempty).ne' h1
end GlobalTheory.CovTop
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fundamentalDomain_volume_ne_zero : ∀ (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (D : D7) (Tu : Type) (C : LevCh D Tu) (t0 : Tu) (hC : C.Is t0) (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ) (μ : MeasureTheory.Measure (GA D (Wc D i))) (𝓕 : Set (GA D (Wc D i))) (hF : IsMeasFD (Wc D i) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW C i P) μ 𝓕), μ 𝓕 ≠ 0 := by
  first | exact @_root_.GlobalTheory.CovTop.haarMeasure_fundamentalDomain_ne_zero_of_cocompact | exact _root_.GlobalTheory.CovTop.haarMeasure_fundamentalDomain_ne_zero_of_cocompact | (intros; apply _root_.GlobalTheory.CovTop.haarMeasure_fundamentalDomain_ne_zero_of_cocompact <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.LogMeasureRatioBounded
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta
namespace GlobalTheory.OneMeasureRatio
theorem log_covolume_ratio_le : ∀ (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (D : D7) (Tu : Type) (C : LevCh D Tu) (t0 : Tu) (hC : C.Is t0) (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ) (μ : MeasureTheory.Measure (GA D (Wc D i))) (𝓕 : Set (GA D (Wc D i))) (hF : IsMeasFD (Wc D i) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW C i P) μ 𝓕) (L : ℝ) (hL : GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.Sizes D L), Real.log (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.ratio D i μ 𝓕) ≤ 122 * (D.R.f * (D.R.r : ℝ) ^ 2 * L) := by
  intro hP D Tu C t0 hC i P μ 𝓕 hF L hL
  have h0 := _root_.GlobalTheory.T.fundamentalDomain_volume_ne_zero hP D Tu C t0 hC i P μ 𝓕 hF
  have ht := _root_.GlobalTheory.T.quotient_measure_lt_top_of_finite_covolume hP D Tu C t0 hC i P μ 𝓕 hF
  have hv := _root_.MainStatements.Tam.Plug.tamagawa_pairs_compatible hP D Tu C t0 hC i P μ 𝓕 hF L hL
  have hd : ∀ τ, Real.log (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ) ≤ 3 / 2 * (D.R.r : ℝ) ^ 2 * L :=
    GlobalTheory.T.log_lowestKTypeWeylDimension_le_of_sizeBounds D i L hL
  have hd1 : ∀ τ, 1 ≤ GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ := GlobalTheory.DimAtOne.one_le_dimAt D i
  have hvpos : 0 < (μ 𝓕).toReal := ENNReal.toReal_pos h0 ht
  have hdpos : ∀ τ, 0 < GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ := fun τ => zero_lt_one.trans_le (hd1 τ)
  unfold GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.ratio
  rw [Real.log_mul hvpos.ne' (Finset.prod_pos fun τ _ => hdpos τ).ne',
    Real.log_prod (fun τ _ => (hdpos τ).ne')]
  have hsum : ∑ τ, Real.log (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ) ≤ ∑ _τ : D.what₂.Tau, 3 / 2 * (D.R.r : ℝ) ^ 2 * L :=
    Finset.sum_le_sum fun τ _ => hd τ
  rw [Finset.sum_const, Finset.card_univ, D.what₂.card_Tau, nsmul_eq_mul] at hsum
  have hlog := log_r_add_three_le D L hL
  have hL0 : 0 ≤ L := le_trans (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) D.R.r; linarith)) hlog
  have hfr : 0 ≤ (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 := by positivity
  have h3 := mul_le_mul_of_nonneg_left hlog hfr
  have h4 : 0 ≤ (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * L := mul_nonneg hfr hL0
  nlinarith
end GlobalTheory.OneMeasureRatio
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_measure_ratio_bounded : ∀ (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (D : D7) (Tu : Type) (C : LevCh D Tu) (t0 : Tu) (hC : C.Is t0) (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ) (μ : MeasureTheory.Measure (GA D (Wc D i))) (𝓕 : Set (GA D (Wc D i))) (hF : IsMeasFD (Wc D i) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW C i P) μ 𝓕) (L : ℝ) (hL : GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.Sizes D L), Real.log (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.ratio D i μ 𝓕) ≤ 122 * (D.R.f * (D.R.r : ℝ) ^ 2 * L) := by
  first | exact @_root_.GlobalTheory.OneMeasureRatio.log_covolume_ratio_le | exact _root_.GlobalTheory.OneMeasureRatio.log_covolume_ratio_le | (intros; apply _root_.GlobalTheory.OneMeasureRatio.log_covolume_ratio_le <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CovolumeRatioEqIndex
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.ExactRatioProof
open scoped InnerProductSpace ComplexConjugate
theorem exact_covolume_ratio : ∀ (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (D : D7) (Tu : Type) (C : LevCh D Tu) (t0 : Tu) (hC : C.Is t0) (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ) (μ : MeasureTheory.Measure (GA D (Wc D i))) (𝓕 : Set (GA D (Wc D i))) (hF : IsMeasFD (Wc D i) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW C i P) μ 𝓕), GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.ExactRatio C i P μ 𝓕 := by
  intro hP D Tu C t0 hC i P μ 𝓕 hF T _ hT ha θ hθ σ M hV F hFm f hf hc
  have hμ : μ.IsHaarMeasure := hF.1.1
  have hS : ∃ c, IsMultIP M μ 𝓕 F F c :=
    GlobalTheory.MultFinite.schurMult GlobalTheory.T.cusp_forms_rapid_decay μ 𝓕 hθ hμ hF.2 F hFm F hFm
  refine ⟨hS, ?_⟩
  obtain ⟨v, hv1, hnorm⟩ : ∃ v : M.Vec, (∀ τ, ‖(v τ : M.H τ)‖ = 1) ∧
      ∀ g, ‖F v g‖ = ‖GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.adFun T i hV f g‖ := by
    rcases hc with ⟨-, v, hv, e⟩ | ⟨-, v, hv, e⟩
    · exact ⟨v, fun τ => (hv τ).1, fun g => by rw [e]⟩
    · exact ⟨v, hv, fun g => by rw [e, RCLike.norm_conj]⟩
  have hFM := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 hFm
  have haut := hFM.aut v
  have h1 := (ipM_spec M μ 𝓕 F F hS v v).2
  have hprod : ∏ τ, ⟪(v τ : M.H τ), (v τ : M.H τ)⟫_ℂ = 1 :=
    Finset.prod_eq_one fun τ _ => by rw [inner_self_eq_norm_sq_to_K, hv1 τ]; simp
  rw [hprod, mul_one] at h1
  have hs : GoodEmb T.Q.c (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.gd T σ) := goodEmb_goodOf _ _
  set c := lieFacZ (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW D i) with hcdef
  have hc0 : 0 < c := lieFacZ_pos _ _
  set ψ : AutQ (Wc D i) → ℂ := fun q => ((‖F v q.out‖ / c : ℝ) : ℂ) with hψdef
  have hK2 := K2 D T hT i _ hs hV f
  have hK3 := K3 D T hT i _ hs f hf
  have hψm : AEStronglyMeasurable ψ (muQ1 (Wc D i)) := by
    haveI : BorelSpace (GA D (Wc D i)) := ⟨rfl⟩
    have hm : Measurable fun q : AutQ (Wc D i) => F v q.out := by
      rw [measurable_from_quotient]
      have e : ((fun q : AutQ (Wc D i) => F v q.out) ∘ Quotient.mk'') = F v := funext fun g => by
        have h2 : g * (Quotient.mk (QuotientGroup.rightRel (GQ (Wc D i))) g).out⁻¹ ∈ GQ (Wc D i) :=
          QuotientGroup.rightRel_apply.1 (Quotient.mk_out g)
        have h3 := haut.left _ h2 (Quotient.mk (QuotientGroup.rightRel (GQ (Wc D i))) g).out
        rw [inv_mul_cancel_right] at h3
        exact h3.symm
      rw [e]
      exact haut.cont.measurable
    refine Measurable.aestronglyMeasurable ?_
    exact Complex.measurable_ofReal.comp ((hm.norm).div_const c)
  have hE : eLpNorm ψ 2 (muQ1 (Wc D i)) = petE (T.V ((i : ℕ) + 1) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.gd T σ))
      (T.dict ((i : ℕ) + 1) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.gd T σ)) (muQ1 (T.V ((i : ℕ) + 1) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.gd T σ)))
      (modelWt (T.U ((i : ℕ) + 1) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.gd T σ)) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW D i)) f := by
    have e1 : eLpNorm ψ 2 (muQ1 (Wc D i)) =
        eLpNorm (c⁻¹ • fun q : AutQ (Wc D i) => ‖GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.adFun T i hV f q.out‖) 2 (muQ1 (Wc D i)) := by
      have heq : ∀ q : AutQ (Wc D i), ‖ψ q‖ =
          (c⁻¹ • fun q : AutQ (Wc D i) => ‖GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.adFun T i hV f q.out‖) q := by
        intro q
        simp only [hψdef, Pi.smul_apply, smul_eq_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_norm,
          abs_of_pos hc0, hnorm]
        ring
      have hm : AEStronglyMeasurable (c⁻¹ • fun q : AutQ (Wc D i) => ‖GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.adFun T i hV f q.out‖) (muQ1 (Wc D i)) :=
        hψm.norm.congr (Filter.Eventually.of_forall heq)
      refine eLpNorm_congr_norm_ae hψm hm (Filter.Eventually.of_forall fun q => ?_)
      rw [← heq q, Real.norm_eq_abs, abs_norm]
    have hadm : AEStronglyMeasurable (fun q : AutQ (Wc D i) =>
        ‖GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.adFun T i hV f q.out‖)
        (muQ1 (Wc D i)) := by
      have heq : (fun q : AutQ (Wc D i) =>
          ‖GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.adFun T i hV f q.out‖) =
          c • (fun q => ‖ψ q‖) := by
        funext q
        simp only [hψdef, Pi.smul_apply, smul_eq_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_div, abs_norm, abs_of_pos hc0, hnorm]
        field_simp
      rw [heq]
      exact hψm.norm.const_smul c
    rw [e1, eLpNorm_const_smul]
    conv_lhs =>
      rw [eLpNorm_eq_eLpNorm' (by norm_num) (by simp) hadm]
    have ht : (2 : ENNReal).toReal = 2 := by norm_num
    rw [ht, hK2]
    rw [← mul_assoc, Real.enorm_eq_ofReal (inv_nonneg.2 hc0.le),
      ← ENNReal.ofReal_mul (inv_nonneg.2 hc0.le), inv_mul_cancel₀ hc0.ne', ENNReal.ofReal_one, one_mul]
  have hψ : MemLp ψ 2 (muQ1 (Wc D i)) := by rw [memLp_iff, hE]; exact lt_top_iff_ne_top.2 hK3
  have hI := GlobalTheory.ReadingNorm.integral_star_mul (Wc D i) (D.sp.W_sig _) hμ hF.2 (F v) haut.left ψ hψ c
    (fun q => by
      simp only [hψdef, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_norm, abs_of_pos hc0]
      field_simp)
  have hL : ‖hψ.toLp ψ‖ = (petE (T.V ((i : ℕ) + 1) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.gd T σ))
      (T.dict ((i : ℕ) + 1) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.gd T σ)) (muQ1 (T.V ((i : ℕ) + 1) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.gd T σ)))
      (modelWt (T.U ((i : ℕ) + 1) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.gd T σ)) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW D i)) f).toReal := by
    rw [Lp.norm_toLp, hE]
  rw [Formalism.IndefR.Links.ipAt, ← h1, hI, L1 D i σ, hL]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.ratio GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.probSq
  push_cast
  ring
end GlobalTheory.ExactRatioProof
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covolume_ratio_eq_index : ∀ (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (D : D7) (Tu : Type) (C : LevCh D Tu) (t0 : Tu) (hC : C.Is t0) (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ) (μ : MeasureTheory.Measure (GA D (Wc D i))) (𝓕 : Set (GA D (Wc D i))) (hF : IsMeasFD (Wc D i) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW C i P) μ 𝓕), GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.ExactRatio C i P μ 𝓕 := by
  first | exact @_root_.GlobalTheory.ExactRatioProof.exact_covolume_ratio | exact _root_.GlobalTheory.ExactRatioProof.exact_covolume_ratio | (intros; apply _root_.GlobalTheory.ExactRatioProof.exact_covolume_ratio <;> assumption)
end
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta
namespace GlobalTheory.OneMeasureAll
theorem covolume_measure_eq_one : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.OneMeasure D := by
  intro hP D Tu C t0 hC i P
  refine ⟨_root_.GlobalTheory.T.level_subgroup_index_bounded hP D Tu C t0 hC i P, fun τ => GlobalTheory.T.one_le_dimAt' D i τ, fun μ 𝓕 hF =>
    ⟨_root_.GlobalTheory.T.fundamentalDomain_volume_ne_zero hP D Tu C t0 hC i P μ 𝓕 hF, _root_.GlobalTheory.T.quotient_measure_lt_top_of_finite_covolume hP D Tu C t0 hC i P μ 𝓕 hF,
      _root_.GlobalTheory.T.covolume_ratio_eq_index hP D Tu C t0 hC i P μ 𝓕 hF, fun L hL =>
        ⟨fun τ => GlobalTheory.T.log_lowestKTypeWeylDimension_le_of_sizeBounds D i L hL τ, _root_.MainStatements.Tam.Plug.tamagawa_pairs_compatible hP D Tu C t0 hC i P μ 𝓕 hF L hL,
          _root_.GlobalTheory.T.log_measure_ratio_bounded hP D Tu C t0 hC i P μ 𝓕 hF L hL⟩⟩⟩
end GlobalTheory.OneMeasureAll
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalized_covolume_eq_one : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.OneMeasure D := by
  first | exact @_root_.GlobalTheory.OneMeasureAll.covolume_measure_eq_one | exact _root_.GlobalTheory.OneMeasureAll.covolume_measure_eq_one | (intros; apply _root_.GlobalTheory.OneMeasureAll.covolume_measure_eq_one <;> assumption)
end
end
