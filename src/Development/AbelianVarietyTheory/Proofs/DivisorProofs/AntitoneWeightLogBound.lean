module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalfAtSmallPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeFromGramAndBounds

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormRankLeBergmanBoundGoodCover
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormRankLeBergmanBoundGoodCover
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.RankBergman

open MeasureTheory ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.AllWt (ptN petE muOn muPart framesOn bergE bergOn modelWt mem_cuspW cuspW_le_secZ cuspOn_le classesOver
  isProbabilityMeasure_muPart muPart_univ_le petE_ne_top bergE_le_iff)
open scoped ENNReal


set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in
theorem rkC_le_of_bergLe : ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o →
    ∀ (la : AllWt.Weight (T.Q.Dw j)) (Z : Comp Y.d.Xo₂ Y.d.c₂) (β : ℝ), 0 ≤ β →
    BergLe Z Y.U (fun _ => D.sp.W j) Y.dict la β → (Y.rkC la Z : ℝ) ≤ β := by
  intro D T j Y e o hY la Z β hβ hB
  classical
  obtain ⟨G, hG⟩ : ∃ G : WTZ D.host.E, G = wtOf (T.Q.Dw j) la 0 := ⟨_, rfl⟩
  set σ : Y.d.c₂.F →+* ℂ := goodOf Y.d.c₂ Y.d.c₂.F.val.toRingHom with hσdef
  have hσ : GoodEmb Y.d.c₂ σ := goodEmb_goodOf _ _
  obtain ⟨th, hr, hth, hdU⟩ := hY.dictU σ hσ
  have hd : ∀ g, (Y.dict σ g).2 ∈ ((Y.U σ).X (Y.dict σ g).1).dom := hdU.2.2.2.1
  have hu := hY.unit σ hσ
  set Cw := cuspOn Y.U Z G with hCw
  set S : Submodule ℂ (FDSec (Y.U σ).X) := Submodule.span ℂ (rdU (Y.U σ) '' (Cw : Set (Rul Y.d.Xo₂ Y.d.c₂))) with hS
  set μ := muOn (Y.U σ) (D.sp.W j) (Y.dict σ) Z with hμdef
  set lw := modelWt (Y.U σ) G with hlw
  have hSsub : S ≤ holSub (Y.U σ).X lw :=
    Submodule.span_le.2 (by rintro _ ⟨f, hf, rfl⟩; exact (mem_cuspW.1 hf.1).2 σ hσ)
  have hoff : ∀ P ∈ S, ∀ z, z ∉ framesOn (Y.U σ) Z → P z.1 z.2 = 0 := fun P hP z hz =>
    eq_zero_of_mem_span_cuspOn hP hz
  have hμ1 : μ Set.univ ≤ 1 := muPart_univ_le _ _ _
  have hfin : ∀ P ∈ holSub (Y.U σ).X lw, petE (D.sp.W j) (Y.dict σ) μ lw P ≠ ⊤ := fun P hP =>
    petE_ne_top _ _ μ hμ1 hd hP

  have hpt : ∀ P ∈ S, ∀ z, ptN lw P z ^ 2 ≤ β * (petE (D.sp.W j) (Y.dict σ) μ lw P).toReal ^ 2 := by
    intro P hP z
    by_cases hz : z ∈ framesOn (Y.U σ) Z
    · have hzd := hz.1
      have hb := hB σ hσ ⟨z.1, z.2, hzd⟩ hz
      have hb' : bergE (D.sp.W j) (Y.dict σ) μ lw ⟨z.1, z.2, hzd⟩ ≤ ENNReal.ofReal β := by
        rw [hlw, hG]; exact hb
      have h := (bergE_le_iff (D.sp.W j) (Y.dict σ) μ hfin ⟨z.1, z.2, hzd⟩ ENNReal.ofReal_ne_top).1 hb' P (hSsub hP)
      have hf := hfin P (hSsub hP)
      have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top hf)) h
      rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal (GlobalTheory.AllWt.ptN_nonneg _ _ _), ENNReal.toReal_mul,
        ENNReal.toReal_ofReal hβ, ENNReal.toReal_pow] at h2
      exact h2
    · have h0 : ptN lw P z = 0 := by
        simp only [ptN, Data.pnorm, hoff P hP z hz, norm_zero, zero_mul]
      rw [h0]
      nlinarith [sq_nonneg (petE (D.sp.W j) (Y.dict σ) μ lw P).toReal]
  have hzero : ∀ P ∈ S, petE (D.sp.W j) (Y.dict σ) μ lw P = 0 → P = 0 := by
    intro P hP h0
    funext k x
    by_cases hz : (⟨k, x⟩ : Σ k, Frame ((Y.U σ).X k).Ψ D.R.r) ∈ framesOn (Y.U σ) Z
    · have h1 := hpt P hP ⟨k, x⟩
      rw [h0, ENNReal.toReal_zero] at h1
      have h2 : ptN lw P ⟨k, x⟩ = 0 := by nlinarith [GlobalTheory.AllWt.ptN_nonneg lw P ⟨k, x⟩]
      have h3 := GlobalTheory.LevGeo.RankBd.pnorm_fac_pos ((Y.U σ).X k) (lw k) hz.1
      have h4 : ‖P k x‖ * _ = 0 := h2
      rcases mul_eq_zero.1 h4 with h5 | h5
      · simpa using h5
      · exact absurd h5 h3.ne'
    · exact hoff P hP ⟨k, x⟩ hz
  have hptd : ∀ (P : FDSec (Y.U σ).X) g, ptN lw P (Y.dict σ g) = ‖P (Y.dict σ g).1 (Y.dict σ g).2‖ := fun P g =>
    pnorm_eq_of_unit _ _ _ _ (hu g)
  have hmeasQ : ∀ P ∈ S, AEStronglyMeasurable
      (fun q : AutQ (D.sp.W j) => ‖P (Y.dict σ q.out).1 (Y.dict σ q.out).2‖) (muQ1 (D.sp.W j)) := by
    intro P hP
    have h := aesm_of_holSub (adelMeas_of_aut Y.d.Xo₂ Y.d.c₂ (U := Y.U) (σ := σ) (GlobalTheory.PetDef.adelAut_good Y hY σ hσ))
      _ (hSsub hP)
    have e : (fun q : AutQ (D.sp.W j) => ‖P (Y.dict σ q.out).1 (Y.dict σ q.out).2‖) =
        fun q => ‖onQ (D.sp.W j) (adel (D.sp.W j) (Y.dict σ) (fun _ => (1 : ℂ)) P) q‖ := by
      funext q
      simp [onQ, adel]
    rw [e]
    exact h.norm
  have hmeas : ∀ P ∈ S, AEStronglyMeasurable
      (fun q : AutQ (D.sp.W j) => ‖P (Y.dict σ q.out).1 (Y.dict σ q.out).2‖) μ := by
    intro P hP
    rw [hμdef]
    unfold GlobalTheory.AllWt.muOn GlobalTheory.AllWt.muPart ProbabilityTheory.cond
    exact ((hmeasQ P hP).restrict).smul_measure _

  have hSfin : FiniteDimensional ℂ S ∧ (Module.finrank ℂ S : ℝ) ≤ β := by
    by_cases hA : muQ1 (D.sp.W j) (classesOver (D.sp.W j) (Y.dict σ) (framesOn (Y.U σ) Z)) = 0
    · have hμ0 : μ = 0 := ProbabilityTheory.cond_eq_zero_of_meas_eq_zero hA
      have hsub : Subsingleton S := ⟨fun a b => by
        have ha := hzero a a.2 (by rw [hμ0]; unfold GlobalTheory.AllWt.petE; exact eLpNorm'_measure_zero_of_pos (by norm_num))
        have hb := hzero b b.2 (by rw [hμ0]; unfold GlobalTheory.AllWt.petE; exact eLpNorm'_measure_zero_of_pos (by norm_num))
        exact Subtype.ext (ha.trans hb.symm)⟩
      refine ⟨inferInstance, ?_⟩
      rw [Module.finrank_zero_of_subsingleton]
      simpa using hβ
    · haveI : IsProbabilityMeasure μ := isProbabilityMeasure_muPart _ _ hA
      have hpet : ∀ P ∈ S, (petE (D.sp.W j) (Y.dict σ) μ lw P).toReal ^ 2 =
          ∫ q, ‖P (Y.dict σ q.out).1 (Y.dict σ q.out).2‖ ^ 2 ∂μ := by
        intro P hP
        obtain ⟨M, -, hM⟩ := exists_ptN_le (hSsub hP)
        have e : petE (D.sp.W j) (Y.dict σ) μ lw P =
            eLpNorm (fun q : AutQ (D.sp.W j) => ‖P (Y.dict σ q.out).1 (Y.dict σ q.out).2‖) 2 μ := by
          unfold GlobalTheory.AllWt.petE
          rw [eLpNorm_eq_eLpNorm' (by norm_num) (by simp) (hmeas P hP)]
          congr 1
          funext q
          exact hptd P _
        have h2 := GlobalTheory.LevGeo.RankBd.eLpNorm_sq_eq (μ := μ) (fun _ => norm_nonneg _) (hmeas P hP) (B := M)
          fun q => by rw [← hptd]; exact hM ⟨_, _, hd q.out⟩
        rw [← e] at h2
        rw [← ENNReal.toReal_pow, h2, ENNReal.toReal_ofReal (integral_nonneg fun _ => by positivity)]
      refine GlobalTheory.Bergman.finite_and_finrank_le_of_pointwise (μ := μ)
        (fun q (P : S) => ‖(P : FDSec (Y.U σ).X) (Y.dict σ q.out).1 (Y.dict σ q.out).2‖)
        (fun q => ⟨(LinearMap.proj (R := ℂ) (φ := fun _ : Frame ((Y.U σ).X (Y.dict σ q.out).1).Ψ D.R.r => ℂ)
          (Y.dict σ q.out).2 ∘ₗ LinearMap.proj (R := ℂ) (φ := fun k => Frame ((Y.U σ).X k).Ψ D.R.r → ℂ)
          (Y.dict σ q.out).1) ∘ₗ S.subtype, fun P => rfl⟩)
        (fun P => hmeas P P.2) ?_ hβ ?_
      · intro P hP0
        refine Subtype.ext (hzero P P.2 ?_)
        unfold GlobalTheory.AllWt.petE
        have e : (fun q : AutQ (D.sp.W j) => ptN lw (P : FDSec (Y.U σ).X) (Y.dict σ q.out)) = fun _ => 0 := by
          funext q
          rw [hptd]
          exact hP0 q
        rw [e]
        exact eLpNorm'_zero (by norm_num)
      · intro P q
        have h1 := hpt P P.2 (Y.dict σ q.out)
        rw [hptd, hpet P P.2] at h1
        exact h1

  obtain ⟨hSf, hSle⟩ := hSfin
  have hcard : ∀ s : Finset Cw, LinearIndependent Y.d.c₂.F (fun i : s => (i : Cw)) → s.card ≤ Module.finrank ℂ S := by
    intro s hs
    let eq : Fin s.card ≃ s := s.equivFin.symm
    let b : Fin s.card → Rul Y.d.Xo₂ Y.d.c₂ := fun i => ((eq i : Cw) : Rul Y.d.Xo₂ Y.d.c₂)
    have hb : LinearIndependent Y.d.c₂.F b := (hs.comp eq eq.injective).map' Cw.subtype (Submodule.ker_subtype _)
    have hrd := GlobalTheory.reading_linearIndependent_secZ GlobalTheory.abelianSchemeLaws_all.1.secBaseChange (Y.U σ) (hY.unf σ hσ)
      (exZ _ G) s.card b (fun i => cuspW_le_secZ G (cuspOn_le Y.U Z G (eq i : Cw).2)) hb
    let v : Fin s.card → S := fun i => ⟨rdU (Y.U σ) (b i), Submodule.subset_span ⟨b i, (eq i : Cw).2, rfl⟩⟩
    have hv : LinearIndependent ℂ v := LinearIndependent.of_comp S.subtype hrd
    simpa using hv.fintype_card_le_finrank
  haveI : Module.Free Y.d.c₂.F Cw := Module.Free.of_divisionRing Y.d.c₂.F Cw
  have hrank : Module.rank Y.d.c₂.F Cw ≤ ((Module.finrank ℂ S : ℕ) : Cardinal) := rank_le hcard
  haveI hCf : FiniteDimensional Y.d.c₂.F Cw :=
    Module.rank_lt_aleph0_iff.1 (lt_of_le_of_lt hrank Cardinal.natCast_lt_aleph0)
  have h2 : Module.finrank Y.d.c₂.F Cw ≤ Module.finrank ℂ S := Module.finrank_le_of_rank_le hrank
  have h3 : GlobalTheory.AllWt.rankOn Y.U Z G ≤ Module.finrank Y.d.c₂.F Cw := by
    unfold GlobalTheory.AllWt.rankOn Formalism.HN.rkK
    exact Submodule.finrank_le _
  show (GlobalTheory.AllWt.rankOn Y.U Z (wtOf (T.Q.Dw j) la 0) : ℝ) ≤ β
  rw [← hG]
  exact le_trans (Nat.cast_le.2 (h3.trans h2)) hSle

end GlobalTheory.RankBergman
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormRankLeBergmanBoundGoodCoverStatement
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
theorem _root_.GlobalTheory.T.cuspFormRank_le_bergmanBound_goodCover : ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ (la : AllWt.Weight (T.Q.Dw j)) (Z : Comp Y.d.Xo₂ Y.d.c₂) (β : ℝ), 0 ≤ β → BergLe Z Y.U (fun _ => D.sp.W j) Y.dict la β → (Y.rkC la Z : ℝ) ≤ β := by
  first | exact @GlobalTheory.RankBergman.rkC_le_of_bergLe | exact GlobalTheory.RankBergman.rkC_le_of_bergLe | (intros; apply GlobalTheory.RankBergman.rkC_le_of_bergLe <;> assumption)
end
end

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

theorem abs_wtOf_le {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} (la : AllWt.Weight Dw) (x : (E →+* ℂ) × ℕ) :
    |(((wtOf Dw la 0).1 x : ℤ) : ℝ)| ≤ ∑ τ, ∑ i, |(la τ i : ℝ)| := by
  have key : ∀ τ i, |(la τ i : ℝ)| ≤ ∑ τ, ∑ i, |(la τ i : ℝ)| := fun τ i =>
    (Finset.single_le_sum (f := fun i => |(la τ i : ℝ)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)).trans
      (Finset.single_le_sum (f := fun τ => ∑ i, |(la τ i : ℝ)|) (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
        (Finset.mem_univ τ))
  have h0 : (0 : ℝ) ≤ ∑ τ, ∑ i, |(la τ i : ℝ)| := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  unfold wtOf
  dsimp only
  split_ifs <;> push_cast <;> simp only [sub_zero, abs_neg, abs_zero] <;> first | exact h0 | exact key _ _

theorem abs_modelWt_le {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r)
    (la : AllWt.Weight Dw) (k : U.Comp) (τ : (U.X k).Ψ) (i : Fin r) :
    |((AllWt.modelWt U (wtOf Dw la 0) k τ i : ℤ) : ℝ)| ≤ ∑ τ, ∑ i, |(la τ i : ℝ)| := by
  unfold AllWt.modelWt
  have h2 : (wtOf Dw la 0).2 / 2 = 0 := by rw [AllWt.wtOf_snd]; simp
  split_ifs
  · rw [h2, add_zero]; exact abs_wtOf_le la _
  · rw [h2, sub_zero]; push_cast; rw [abs_neg]; exact abs_wtOf_le la _

theorem sum_spread_modelWt_le {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r)
    (la : AllWt.Weight Dw) (k : U.Comp) :
    ∑ τ, (U.X k).spread (AllWt.modelWt U (wtOf Dw la 0) k) τ ≤
      2 * (Module.finrank ℚ E : ℝ) * ∑ τ, ∑ i, |(la τ i : ℝ)| := by
  set S := ∑ τ, ∑ i, |(la τ i : ℝ)| with hS
  have h0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hsp : ∀ τ, (U.X k).spread (AllWt.modelWt U (wtOf Dw la 0) k) τ ≤ 2 * S := by
    intro τ
    unfold Data.spread
    rcases isEmpty_or_nonempty (Fin r) with hr | hr
    · simp; linarith
    · have hb := fun i => abs_le.1 (abs_modelWt_le U la k τ i)
      have h1 : (⨆ i, ((AllWt.modelWt U (wtOf Dw la 0) k τ i : ℤ) : ℝ)) ≤ S := ciSup_le fun i => (hb i).2
      have h2 : -S ≤ ⨅ i, ((AllWt.modelWt U (wtOf Dw la 0) k τ i : ℤ) : ℝ) := le_ciInf fun i => (hb i).1
      linarith
  have hcard : (Fintype.card (U.X k).Ψ : ℝ) ≤ Module.finrank ℚ E := by
    have e1 : Fintype.card (U.X k).Ψ = (U.X k).Ψ.card := Fintype.card_coe _
    have e2 : (U.X k).Ψ.card ≤ Fintype.card (E →+* ℂ) := Finset.card_le_univ _
    rw [NumberField.Embeddings.card] at e2
    exact_mod_cast e1 ▸ e2
  calc ∑ τ, (U.X k).spread (AllWt.modelWt U (wtOf Dw la 0) k) τ ≤ ∑ _τ : (U.X k).Ψ, 2 * S :=
        Finset.sum_le_sum fun τ _ => hsp τ
    _ = (Fintype.card (U.X k).Ψ : ℝ) * (2 * S) := by rw [Finset.sum_const, nsmul_eq_mul]; rfl
    _ ≤ (Module.finrank ℚ E : ℝ) * (2 * S) := mul_le_mul_of_nonneg_right hcard (by linarith)
    _ = _ := by ring

end GlobalTheory.BergRank

namespace GlobalTheory.BergRank

theorem berg_sup_rank : GlobalTheory.CovTop.Hypotheses2 → ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ Lb : ℝ, 1 ≤ Lb → Real.log Y.d.l₂.M ≤ 30 * Lb → fieldSz D.host.E ≤ 3 * Lb → Real.log (D.R.f * D.R.r) ≤ Lb → o ≤ 391 * (D.R.f * D.R.r * Lb) ^ 2 → ∀ la : AllWt.Weight (T.Q.Dw j), (∀ τ, Antitone (la τ)) → Real.log (∑ τ, ∑ k, |(la τ k : ℝ)|) ≤ 20 * Lb → ∀ Z, BergLe Z Y.U (fun _ => D.sp.W j) Y.dict la (Real.exp (C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 3)) ∧ SupBdWt Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z la (Real.exp (C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 3)) ∧ Real.log (Y.rkC la Z) ≤ C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 3 := by
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
  obtain ⟨hβ1, hβ⟩ := GlobalTheory.T.sup_constant_log_bound D Y.d.l₂.M Lb w (by have := Y.d.l₂.three_le; omega) hLb hM hsz hfr hw1 hlogw
  set β := GlobalTheory.LevGeo.supConst D.host.E D.R.r D.host.d Y.d.l₂.M w with hβdef
  have hβexp : β ≤ Real.exp (4000 * ((D.R.f : ℝ) * D.R.r * Lb) ^ 3) := by
    rw [← Real.exp_log (by linarith : 0 < β)]; exact Real.exp_le_exp.2 hβ
  have hsp : ∀ σ k, ∑ τ, ((Y.U σ).X k).spread (AllWt.modelWt (Y.U σ) (wtOf _ la 0) k) τ ≤ w := fun σ k =>
    (sum_spread_modelWt_le _ la k).trans (by rw [hw]; linarith)
  have hB : BergLe Z Y.U (fun _ => D.sp.W j) Y.dict la β := fun σ hσ y hy =>
    GlobalTheory.T.level_geometry_weight_bound hP.p6 D j _ _ _ _ _ Y.U Y.dict hL σ hσ (wtOf _ la 0) (AllWt.even_wtOf la 0) w (by linarith) (hsp σ) Z y hy
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
