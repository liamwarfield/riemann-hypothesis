module

public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.AdmissibleVectors
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.BlockMirrorMap
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.CornerEmbeddingGL
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.UnipotentMeasureProperties
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.UnipotentBlockMeasure
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralVecSmul
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.LocalAlgebraPowers
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.OneMoreColumnOf
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.PoissonCutoffAlgebra
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.KernelLessSecondOf
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.TableDegreeThreeBase
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.PrimePairSetSecond
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.WeightCoefficients
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.HeightParamNonneg
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.CuspDecayShortRow
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.SeparatedThetaSum
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.LogBallEstimates
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.HeightBoundSetup
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.WeightInverseContinuity
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.BlockInfGL
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.TransformEmbeddingBlocks
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.UnipotentZeroOfLevel
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.LastRowCutoffOf
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.KernelEqualityFirstOf
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.CuspOrthogonalityOf
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.PRSPole

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.KatoClassHeckeEulerFactorRelation
namespace PositivityTheory.AdelicQuotientData

theorem nm_agrees_with_twisted_norm_sigmaGL : D0 → jumpWindows.G0 → N2 := @GlobalTheory.CompanionTheory.UnipotentNormalizer.main

end PositivityTheory.AdelicQuotientData
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.LevelScalarAction
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace LevelScalarAction

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem lev_smul {S : Finset (Pl E)} {x : XB E k} (h : Lev S x) (c : ℂ) : Lev S (c • x) := by
  intro w hw
  filter_upwards [h w hw] with u hu
  have hu' : repW k w u x = x := hu
  change repW k w u (c • x) = c • x
  rw [map_smul, hu']

end LevelScalarAction

theorem global_level_of : jumpWindows.G0 → jumpWindows.G1 → jumpWindows.AlmostEverywhereSpherical → jumpWindows.G2c → jumpWindows.G5 → K8 → K9 := by
  intro hG0 hG1 hG1b hG2c hG5 hK8 E _ _ _ k _ ψ hψ hcond π hπ
  obtain ⟨φ₀, hφ₀, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot π.ne_bot
  obtain ⟨x₀, hx₀, -, hlev⟩ := hG1 E k π hπ φ₀ hφ₀
  have hev := hcond.and (hG1b E k π hπ φ₀ hφ₀ x₀ hx₀)
  have hfin := Filter.eventually_cofinite.1 hev
  refine ⟨hfin.toFinset, fun S hS => ?_⟩
  have hoff : ∀ w, w ∉ S → Cond ψ w ∧ ∀ B, (CG.mk π).HasSat w B → SatFn w B x₀ := by
    intro w hw
    by_contra hc
    exact hw (hS ((Set.Finite.mem_toFinset _).2 hc))
  refine ⟨fun w hw => (hoff w hw).1, fun α hα => ?_⟩
  have hgood : Good ψ (k - 1) (x₀ : GA E k → ℂ) := by
    rw [hx₀]; exact GlobalTheory.T.isMirabolicWhittakerStage_of_isCuspForm E k ψ φ₀ (π.cusp _ hφ₀)
  have hx0 : x₀ ≠ 0 := by
    intro h
    subst h
    exact hne (Subtype.ext (by rw [← hx₀]; rfl))
  obtain ⟨g, hg⟩ := ((hG5 E k ψ hψ).2.2.2 x₀ hgood).2.1 hx0
  have hsat : ∀ w : Off E S, SatFn w.1 (Finset.univ.val.map (α w)) x₀ := fun w => (hoff w.1 w.2).2 _ (hα w)
  obtain ⟨g₀, h1, h2, h3⟩ := (hG0 E k).2.2.2.2.2.2.2.2.2.2.1 S g
  have hne0 : Wh ψ x₀ g₀ ≠ 0 :=
    ((hK8 E k ψ hψ S (fun w hw => (hoff w hw).1) α x₀ hgood hsat).2.2 g hg).1 g₀ h1 h2 h3
  refine ⟨(Wh ψ x₀ g₀)⁻¹ • φ₀, π.V.smul_mem _ hφ₀, g₀, (Wh ψ x₀ g₀)⁻¹ • x₀, h3, ?_, ?_, LevelScalarAction.lev_smul (hlev S) _, ?_⟩
  · funext y
    change (Wh ψ x₀ g₀)⁻¹ * x₀ y = (Wh ψ x₀ g₀)⁻¹ * φ₀.1 y
    rw [hx₀]
  · intro w
    obtain ⟨Y, -, -, hY⟩ := hG2c E k w.1 (Finset.univ.val.map (α w)) (by simp)
    exact (hY _).1 (Y.smul_mem _ ((hY x₀).2 (hsat w)))
  · rw [(hG5 E k ψ hψ).2.1, one_mul]
    change whit ψ (k - 1) (fun y => (Wh ψ x₀ g₀)⁻¹ * x₀ y) g₀ = 1
    rw [GlobalTheory.CuspRep.Generic.whit_smul]
    exact inv_mul_cancel₀ hne0

end PositivityTheory.AdelicQuotientData

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.PrimePairSetFirst
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace primePairSetFirst

variable {E : Type} [Field E] [NumberField E] {k : ℕ} {ψ : AddChar (Ad E) ℂ}

theorem cont_colT (hψ : StdPsi ψ) (m : ℕ) (f : GA E k → ℂ) (hc : Continuous f)
    (hl : ∀ (c : UnipotentBlockColumnIndex k (m + 1) (m + 1) → E) g, f (ratGL E k (blkU c) * g) = f g) :
    Continuous (colT ψ (m + 1) f) := by
  have key := GlobalTheory.T.continuous_quotientAverage_periodic_family (UnipotentBlockColumnIndex k (m + 1) (m + 1) → Ad E) (ratV E (UnipotentBlockColumnIndex k (m + 1) (m + 1)))
    (isCoLat_ratV E _) (GA E k)
    (fun p => ψ (-dot (eLast k (m + 1)) p.2) * f (blkU p.2 * p.1)) ?_ ?_
  · exact key
  · exact (hψ.cont.comp ((continuous_dot _).neg.comp continuous_snd)).mul
      (hc.comp (((continuous_posU _).comp continuous_snd).mul continuous_fst))
  · intro g γ hγ y
    exact (per_coef hψ (eLast k (m + 1)) hc hl g).2 γ hγ y

theorem colT_blkU (hψ : StdPsi ψ) (m : ℕ) (f : GA E k → ℂ) (hc : Continuous f)
    (hl : ∀ (c : UnipotentBlockColumnIndex k (m + 1) (m + 1) → E) g, f (ratGL E k (blkU c) * g) = f g)
    (y : UnipotentBlockColumnIndex k (m + 1) (m + 1) → Ad E) (g : GA E k) :
    colT ψ (m + 1) f (blkU y * g) = ψ (dot (eLast k (m + 1)) y) * colT ψ (m + 1) f g := by
  have hper := per_coef (a := k) hψ (eLast k (m + 1)) hc hl g
  have hT := GlobalTheory.T.quotientAverage_translate_invariant (UnipotentBlockColumnIndex k (m + 1) (m + 1) → Ad E) (ratV E (UnipotentBlockColumnIndex k (m + 1) (m + 1)))
    (isCoLat_ratV E _) _ hper y
  have hpt : (fun x : UnipotentBlockColumnIndex k (m + 1) (m + 1) → Ad E =>
        ψ (-dot (eLast k (m + 1)) x) * f (blkU x * (blkU y * g))) =
      fun x => ψ (dot (eLast k (m + 1)) y) *
        (ψ (-dot (eLast k (m + 1)) (x + y)) * f (blkU (x + y) * g)) := by
    funext x
    have hd : dot (eLast k (m + 1)) (x + y) = dot (eLast k (m + 1)) x + dot (eLast k (m + 1)) y := by
      simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    have hu : (blkU (x + y) : GA E k) = blkU x * blkU y := posU_add _ x y
    have h1 : ψ (dot (eLast k (m + 1)) y) * ψ (-dot (eLast k (m + 1)) y) = 1 := by
      rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
    rw [hd, hu, neg_add, AddChar.map_add_eq_mul, mul_assoc (blkU x)]
    calc ψ (-dot (eLast k (m + 1)) x) * f (blkU x * (blkU y * g))
        = (ψ (dot (eLast k (m + 1)) y) * ψ (-dot (eLast k (m + 1)) y)) *
            (ψ (-dot (eLast k (m + 1)) x) * f (blkU x * (blkU y * g))) := by rw [h1, one_mul]
      _ = _ := by ring
  change avg _ (fun x => ψ (-dot (eLast k (m + 1)) x) * f (blkU x * (blkU y * g))) =
    _ * avg _ (fun x => ψ (-dot (eLast k (m + 1)) x) * f (blkU x * g))
  rw [hpt, avg_const_mul]
  exact congrArg _ hT

theorem colT_law (m : ℕ) (f : GA E k → ℂ) (j : ℕ) (hj : m + 1 < j)
    (hlaw : ∀ (y : UnipotentBlockColumnIndex k j j → Ad E) (g : GA E k), f (blkU y * g) = ψ (dot (eLast k j) y) * f g)
    (y : UnipotentBlockColumnIndex k j j → Ad E) (g : GA E k) :
    colT ψ (m + 1) f (blkU y * g) = ψ (dot (eLast k j) y) * colT ψ (m + 1) f g := by
  simp only [colT, coefF]
  rw [← avg_const_mul]
  congr 1
  funext x
  have e1 : f (blkU x * (blkU y * g)) = ψ (dot (eLast k j) y) * f (blkU x * g) := by
    rw [← mul_assoc, blkU_mul_blkU hj x y, mul_assoc, hlaw, dot_eLast_shift hj x y]
  rw [e1]
  ring

theorem colT_rat (hψ : StdPsi ψ) (m : ℕ) (hmk : m + 1 < k) (f : GA E k → ℂ) (hc : Continuous f)
    (hl : ∀ γ : GL (Fin k) E, IsMir (m + 1) γ → ∀ g, f (ratGL E k γ * g) = f g)
    (γ : GL (Fin k) E) (hγ : IsMir (m + 1) γ) (g : GA E k) :
    colT ψ (m + 1) f (ratGL E k γ * g) = coefF ψ (m + 1) (fun t => γ.val ⟨m, by omega⟩ t.1.1) f g := by
  unfold colT
  rw [GlobalTheory.T.whittakerCoefficient_rationalMirabolic_mul E k ψ hψ m f hc hl γ hγ (eLast k (m + 1)) g]
  congr 1
  funext t
  let s0 : UnipotentBlockColumnIndex k (m + 1) (m + 1) := ⟨(⟨m, by omega⟩, ⟨m + 1, hmk⟩), Nat.lt_succ_self m, le_refl _, le_refl _⟩
  rw [Finset.sum_eq_single s0]
  · have h1 : eLast (E := E) k (m + 1) s0 = 1 := by simp [eLast, s0]
    rw [h1, one_mul]
  · intro s _ hs
    have h0 : eLast (E := E) k (m + 1) s = 0 := by
      simp only [eLast]
      rw [if_neg]
      intro e
      apply hs
      have h2 := s.2.2
      apply Subtype.ext
      exact Prod.ext (Fin.ext (by simp [s0]; omega)) (Fin.ext (by simp [s0]; omega))
    rw [h0, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem blk_eta {m : ℕ} (hmk : m + 1 < k) (t : UnipotentBlockColumnIndex k (m + 1) (m + 1)) :
    (⟨(t.1.1, ⟨m + 1, hmk⟩), t.2.1, le_rfl, le_rfl⟩ : UnipotentBlockColumnIndex k (m + 1) (m + 1)) = t := by
  have h := t.2.2
  exact Subtype.ext (Prod.ext rfl (Fin.ext (by show m + 1 = (t.1.2 : ℕ); omega)))

def rowEquiv (m : ℕ) (hmk : m + 1 < k) : RowT E k (m + 1) ≃ {ξ : UnipotentBlockColumnIndex k (m + 1) (m + 1) → E // ξ ≠ 0} where
  toFun ξ := ⟨fun t => ξ.1 t.1.1, by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 ξ.2.1
    have him : (i : ℕ) < m + 1 := by
      by_contra h
      exact hi (ξ.2.2 i (by omega))
    intro h0
    exact hi (congrFun h0 ⟨(i, ⟨m + 1, hmk⟩), him, le_rfl, le_rfl⟩)⟩
  invFun η := ⟨fun i => if h : (i : ℕ) < m + 1 then η.1 ⟨(i, ⟨m + 1, hmk⟩), h, le_rfl, le_rfl⟩ else 0, by
    refine ⟨fun h0 => η.2 ?_, fun i hi => dif_neg (by omega)⟩
    funext t
    have h1 := congrFun h0 t.1.1
    simp only [Pi.zero_apply] at h1
    rw [dif_pos t.2.1, blk_eta hmk t] at h1
    exact h1⟩
  left_inv ξ := by
    apply Subtype.ext
    funext i
    by_cases h : (i : ℕ) < m + 1
    · exact dif_pos h
    · exact (dif_neg h).trans (ξ.2.2 i (by omega)).symm
  right_inv η := by
    apply Subtype.ext
    funext t
    show (if h : (t.1.1 : ℕ) < m + 1 then η.1 ⟨(t.1.1, ⟨m + 1, hmk⟩), h, le_rfl, le_rfl⟩ else 0) = η.1 t
    rw [dif_pos t.2.1, blk_eta hmk t]

end primePairSetFirst

theorem p1_holds : N0 → P0 → P1 := by
  intro hN _ E _ _ _ k ψ hψ m hm1 hmk f hf
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hl : ∀ (c : UnipotentBlockColumnIndex k (m + 1) (m + 1) → E) g, f (ratGL E k (blkU c) * g) = f g :=
    fun c g => hf.left _ (isMir_blkU c) g
  simp only [Nat.add_sub_cancel]
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ⟨primePairSetFirst.rowEquiv m hmk, fun ξ t => rfl⟩⟩
  · exact primePairSetFirst.cont_colT hψ m f hf.cont hl
  · intro γ hγ g
    have hγ1 : IsMir (m + 1) γ := fun i c h => hγ i c (by omega)
    rw [primePairSetFirst.colT_rat hψ m hmk f hf.cont hf.left γ hγ1 g]
    unfold colT
    congr 1
    funext t
    rw [hγ ⟨m, by omega⟩ t.1.1 (Or.inl le_rfl)]
    have ht := t.2.1
    simp only [eLast, Matrix.one_apply]
    by_cases h : (t.1.1 : ℕ) = m
    · rw [if_pos (Fin.ext h.symm), if_pos (by omega)]
    · rw [if_neg (fun e => h (congrArg Fin.val e).symm), if_neg (by omega)]
  · intro j hj y g
    rcases Nat.lt_or_ge (m + 1) j with h1 | h1
    · exact primePairSetFirst.colT_law m f j h1 (hf.law j h1) y g
    · obtain rfl : j = m + 1 := by omega
      exact primePairSetFirst.colT_blkU hψ m f hf.cont hl y g
  · intro ξ g
    obtain ⟨hB, hrow⟩ := (hN E k (m + 1) (by omega) (by omega)).1 ξ
    have hγ : IsMir (m + 1) (gam ξ) := fun i c h => hB i c (by omega)
    rw [primePairSetFirst.colT_rat hψ m hmk f hf.cont hf.left _ hγ g]
    congr 1
    funext t
    exact (hrow _ _ rfl).symm
  · intro χ hχ
    funext g
    simp only [colT, coefF]
    rw [← avg_const_mul]
    congr 1
    funext x
    rw [hχ]
    ring

end PositivityTheory.AdelicQuotientData

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.PsiDeterminantFlag
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace PsiDeterminantFlag

theorem exists_psiOK {E : Type} [Field E] [NumberField E] (w : Pl E) :
    ∃ χ : AddChar (w.adicCompletion E) ℂ, PositivityTheory.JacquetShalikaLocal.PsiOK χ := by
  obtain ⟨ψ₁, hψ₁⟩ := GlobalTheory.SplitWeil.exists_hasConductor_one (w.adicCompletion E)
  exact ⟨_, GlobalTheory.CompanionTheory.JSBound.psiOK_of_hasConductor hψ₁⟩

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {k : ℕ}

theorem dt_fl (hG0 : jumpWindows.G0) (hD0 : D0) (w : Pl E)
    (n : GL (Fin k) (w.adicCompletion E)) (hn : n ∈ Iwasawa.unipotent (w.adicCompletion E) k)
    (κ : GL (Fin k) (w.adicCompletion E)) (hκ : κ ∈ GLnLocal.integralGL (w.adicCompletion E) k)
    (l : Fin k → ℤ) :
    Dt (fl k w (n * Iwasawa.torusPow (w.adicCompletion E) k l * κ)) =
      (Ideal.absNorm w.asIdeal : ℝ) ^ (-∑ i, l i) := by
  obtain ⟨_, hmul, _, _, hUU, _, _, _, _, htor, hint⟩ := hD0 E k
  obtain ⟨_, _, hci, hcl, hcl', -⟩ := hG0 E k
  have h1 : Dt (fl k w n) = 1 := by
    obtain ⟨t1, t2, -⟩ := GlobalTheory.T.localUpperUnipotent_adelic_upperUnipotent E k w n (fun i j hij => hn.1 hij) hn.2
    exact hUU 0 _ ⟨t1, t2, fun i c hc => absurd hc (Nat.not_lt_zero _)⟩
  have h2 : Dt (fl k w κ) = 1 := by
    refine hint _ (hci w κ) fun v => ?_
    by_cases hv : v = w
    · subst hv; rw [hcl]; exact hκ
    · rw [hcl' w v κ hv]; exact one_mem _
  rw [map_mul, map_mul, hmul, hmul, h1, h2, htor, one_mul, mul_one]

end PsiDeterminantFlag

theorem mean_convergence_of : jumpWindows.G0 → D0 → P2 → C0 → C2 → D1 → M0 → LocalHeckeAlgebra → CAUCHY → M1 := by
  intro hG0 hD0 hP2 _ hC2 hD1 hM0 hK8a hC E _ _ _ k μ _ hk β hβ ψ hψ S m α α' u f φ hkm hα hα' hD
  have : BorelSpace (GA E k) := ⟨rfl⟩
  obtain ⟨hpos, hmul, hcont, -, hUU, -⟩ := hD0 E k
  obtain ⟨hlaw, hpsN, hUU01, hwhit, -, hgood, -⟩ := hP2 E k ψ hψ
  obtain ⟨β', σ₀', hβ', hM⟩ := hM0 E k μ hk β hβ ψ hψ S m α α' u f φ hD
  have hk1 : k - 1 < k := by omega
  have hWf : Pre ψ 0 (whit ψ (k - 1) f) := hwhit _ hk1 f hD.pre
  have hWφ : Pre ψ 0 (whit ψ (k - 1) φ) := hwhit _ hk1 φ (hgood _ φ hD.good)
  have hPc : Continuous (PW ψ f φ) := hWf.cont.mul (Complex.continuous_conj.comp hWφ.cont)
  have hPu : ∀ n, UU 0 n → ∀ g, PW ψ f φ (n * g) = PW ψ f φ g := by
    intro n hn g
    have h1 := hlaw 0 _ hWf n (hUU01 n hn) g
    have h2 := hlaw 0 _ hWφ n (hUU01 n hn) g
    simp only [PW, h1, h2, map_mul]
    have e : psN ψ n * conj (psN ψ n) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hpsN]; simp
    linear_combination (whit ψ (k - 1) f g * conj (whit ψ (k - 1) φ g)) * e
  have hDtu : ∀ n, UU 0 n → ∀ g, Dt (n * g) = Dt g := fun n hn g => by rw [hmul, hUU 0 n hn, one_mul]
  have hDtm : Measurable fun g : GA E k => (Dt g : ℂ) := Complex.measurable_ofReal.comp hcont.measurable
  have hΦm : ∀ z : ℂ, Measurable fun g => PW ψ f φ g * (Dt g : ℂ) ^ z := fun z =>
    hPc.measurable.mul (hDtm.pow_const z)
  have hΦu : ∀ z : ℂ, ∀ n, UU 0 n → ∀ g,
      PW ψ f φ (n * g) * (Dt (n * g) : ℂ) ^ z = PW ψ f φ g * (Dt g : ℂ) ^ z := by
    intro z n hn g; rw [hPu n hn, hDtu n hn]
  have hχ : ∀ w : Off E S, ∃ χ : AddChar (w.1.adicCompletion E) ℂ, PositivityTheory.JacquetShalikaLocal.PsiOK χ :=
    fun w => PsiDeterminantFlag.exists_psiOK w.1
  let a' : ℂ → Off E S → (Fin k → ℤ) → ℂ := fun z w l =>
    aLoc α α' w l * (((nq w : ℝ) ^ (-∑ i, l i) : ℝ) : ℂ) ^ z
  have ha0 : ∀ z w, a' z w 0 = 1 := by
    intro z w
    obtain ⟨χ, hχ'⟩ := hχ w
    simp [a', (hK8a E S m k α α' w χ hχ' hk hkm).1]
  have hlawz : ∀ z, LawOff S (fun g => PW ψ f φ g * (Dt g : ℂ) ^ z) (a' z) := by
    intro z w g hg n hn κ hκ l
    simp only [a']
    rw [hD.law w g hg n hn κ hκ l, hmul, PsiDeterminantFlag.dt_fl hG0 hD0 w.1 n hn κ hκ l, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (hpos g).le (by positivity)]
    simp only [nq]; ring
  have hI : ∀ s : ℂ, 2 < s.re → σ₀' < (s - ((m : ℂ) - k) / 2).re →
      ∫ g, PW ψ f φ g * (Dt g : ℂ) ^ (s - ((m : ℂ) - k) / 2) ∂μ.withDensity β' =
        (∫ g in G0 S, PW ψ f φ g * (Dt g : ℂ) ^ (s - ((m : ℂ) - k) / 2) ∂μ.withDensity β') * LS S α α' s := by
    intro s hs hs'
    have hsum := hC2 E k μ hk β' hβ' S _ (a' (s - ((m : ℂ) - k) / 2)) (hΦm _) (hΦu _) (hlawz _) (ha0 _)
      (hM _ hs').1
    obtain ⟨-, hL⟩ := hC E S m k α α' s hkm hα hα' hs
    have e : (fun l : Off E S →₀ (Fin k → ℤ) => ∏ w ∈ l.support, loc (nq w) (α w) (α' w) s (l w)) =
        fun l => ∏ w ∈ l.support, (nq w : ℂ) ^ rhoPair (l w) * a' (s - ((m : ℂ) - k) / 2) w (l w) := by
      funext l
      refine Finset.prod_congr rfl fun w _ => ?_
      obtain ⟨χ, hχ'⟩ := hχ w
      exact (((hK8a E S m k α α' w χ hχ' hk hkm).2 (l w)).1 s).symm
    rw [e] at hL
    have hL2 := hL.mul_right (∫ g in G0 S, PW ψ f φ g * (Dt g : ℂ) ^ (s - ((m : ℂ) - k) / 2) ∂μ.withDensity β')
    rw [mul_comm _ (LS S α α' s)]
    exact hsum.unique hL2
  obtain ⟨hdiff, hnz⟩ := hD1 E k μ hk β' hβ' S (PW ψ f φ) u ((σ₀' + 1 : ℝ) : ℂ) hPc hPu hD.one hD.pos
    (hM _ (by simp)).1
  refine ⟨fun s => ∫ g in G0 S, PW ψ f φ g * (Dt g : ℂ) ^ (s - ((m : ℂ) - k) / 2) ∂μ.withDensity β',
    max 2 (σ₀' + ((m : ℝ) - k) / 2), hdiff.comp (differentiable_id.sub_const _), ?_, ?_⟩
  · intro σ
    have e : ((σ : ℂ) + u * Complex.I) - ((m : ℂ) - k) / 2 =
        ((σ - ((m : ℝ) - k) / 2 : ℝ) : ℂ) + u * Complex.I := by push_cast; ring
    dsimp only
    rw [e]
    exact hnz _
  · intro s hs
    have hs2 : 2 < s.re := lt_of_le_of_lt (le_max_left _ _) hs
    have hre : (s - ((m : ℂ) - k) / 2).re = s.re - ((m : ℝ) - k) / 2 := by simp
    have hs' : σ₀' < (s - ((m : ℂ) - k) / 2).re := by
      rw [hre]; linarith [le_max_right 2 (σ₀' + ((m : ℝ) - k) / 2)]
    have e1 : ∀ g, sumF f g * conj (φ g) * (Dt g : ℂ) ^ (-(((m : ℂ) - k) / 2)) * (Dt g : ℂ) ^ s =
        sumF f g * conj (φ g) * (Dt g : ℂ) ^ (s - ((m : ℂ) - k) / 2) := by
      intro g
      rw [mul_assoc, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.2 (hpos g).ne'), neg_add_eq_sub]
    simp_rw [e1]
    rw [(hM _ hs').2, hI s hs2 hs']

end PositivityTheory.AdelicQuotientData

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.RowsCompactSum
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace RowsCompactSum

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {k : ℕ}

theorem contFin : Continuous (fun (y : Fin k → Ad E) (i : Fin k) => pFin E (y i)) :=
  continuous_pi fun i => (GlobalTheory.CuspRep.GASplit.continuous_pFin E).comp (continuous_apply i)

theorem contInf : Continuous (fun (y : Fin k → Ad E) (i : Fin k) => pInf E (y i)) :=
  continuous_pi fun i => (GlobalTheory.CuspRep.GASplit.continuous_pInf E).comp (continuous_apply i)

theorem one_le (C₀ : Set (Fin k → Ad E)) (hC₀ : IsCompact C₀) (M : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ y,
    C₀.indicator (fun _ => (1 : ℝ≥0∞)) y ≤ ENNReal.ofReal B * ENNReal.ofReal
      (((fun y (i : Fin k) => pFin E (y i)) '' C₀).indicator
        (fun _ => ((1 + ‖fun i => pInf E (y i)‖) ^ M)⁻¹) fun i => pFin E (y i)) := by
  obtain ⟨R, hR⟩ := hC₀.exists_bound_of_continuousOn (contInf (E := E) (k := k)).continuousOn
  refine ⟨(1 + max R 0) ^ M, by positivity, fun y => ?_⟩
  by_cases hy : y ∈ C₀
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (Set.mem_image_of_mem _ hy), ← ENNReal.ofReal_mul (by positivity)]
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    have h0 : 0 < (1 + ‖fun i => pInf E (y i)‖) ^ M := by positivity
    rw [← div_eq_mul_inv, le_div_iff₀ h0, one_mul]
    apply pow_le_pow_left₀ (by positivity)
    have := hR y hy
    linarith [le_max_left R 0]
  · rw [Set.indicator_of_notMem hy]
    exact bot_le

theorem sum_le (hN : N0) (hG3 : ThetaSeriesBound) (hk : 1 ≤ k) (C₀ : Set (Fin k → Ad E)) (hC₀ : IsCompact C₀) (a : ℕ) (ha : k ≤ a) :
    ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧ ∀ (g : GA E k) (r : ℝ), 0 < r → (∀ ξ, ξ ≠ 0 → r ≤ height g ξ) →
      ∑' ξ : RowT E k k, C₀.indicator (fun _ => (1 : ℝ≥0∞)) (lastRow (ratGL E k (gam ξ) * g)) ≤
        ENNReal.ofReal (B * (C * (r ^ a)⁻¹)) := by
  have hCf : IsCompact ((fun y (i : Fin k) => pFin E (y i)) '' C₀) := hC₀.image contFin
  obtain ⟨M, C, hMC⟩ := hG3 E k _ hCf a ha
  obtain ⟨B, hB, hB1⟩ := one_le C₀ hC₀ M
  have hlast := (hN E k k hk le_rfl).2.2.2.2.2.2.2.2.2
  refine ⟨B, max C 0, hB, le_max_right _ _, fun g r hr hrh => ?_⟩
  have hinj : Function.Injective (fun ξ : RowT E k k => (⟨ξ.1, ξ.2.1⟩ : {ξ : Fin k → E // ξ ≠ 0})) := by
    intro x y h
    simp only [Subtype.mk.injEq] at h
    exact Subtype.ext h
  let F : {ξ : Fin k → E // ξ ≠ 0} → ℝ≥0∞ := fun ξ => ENNReal.ofReal
    (((fun y (i : Fin k) => pFin E (y i)) '' C₀).indicator
      (fun _ => ((1 + ‖fun i => pInf E (((fun i => algebraMap E (Ad E) (ξ.1 i)) ᵥ* g.val) i)‖) ^ M)⁻¹)
      fun i => pFin E (((fun i => algebraMap E (Ad E) (ξ.1 i)) ᵥ* g.val) i))
  have hF : ∑' ξ, F ξ ≤ ENNReal.ofReal (C * (r ^ a)⁻¹) := hMC g r hr hrh
  have h1 : ∀ ξ : RowT E k k, C₀.indicator (fun _ => (1 : ℝ≥0∞)) (lastRow (ratGL E k (gam ξ) * g)) ≤
      ENNReal.ofReal B * F ⟨ξ.1, ξ.2.1⟩ := by
    intro ξ
    rw [hlast]
    exact hB1 _
  calc _ ≤ ∑' ξ : RowT E k k, ENNReal.ofReal B * F ⟨ξ.1, ξ.2.1⟩ := ENNReal.tsum_le_tsum h1
    _ ≤ ∑' ξ, ENNReal.ofReal B * F ξ := ENNReal.tsum_comp_le_tsum_of_injective hinj (fun ξ => ENNReal.ofReal B * F ξ)
    _ = ENNReal.ofReal B * ∑' ξ, F ξ := ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal B * ENNReal.ofReal (max C 0 * (r ^ a)⁻¹) := by
        gcongr
        refine hF.trans (ENNReal.ofReal_le_ofReal ?_)
        gcongr
        exact le_max_left _ _
    _ = ENNReal.ofReal (B * (max C 0 * (r ^ a)⁻¹)) := (ENNReal.ofReal_mul hB).symm

theorem r_le (hD : D0) (hK : K1) (hk : 1 ≤ k) (g : GA E k) :
    0 < dmin g * Dt g ^ ((k : ℝ)⁻¹) ∧ ∀ ξ, ξ ≠ 0 → dmin g * Dt g ^ ((k : ℝ)⁻¹) ≤ height g ξ := by
  have hDt := (hD E k).1 g
  have hK' := hK E k hk
  have hp : 0 < Dt g ^ ((k : ℝ)⁻¹) := Real.rpow_pos_of_pos hDt _
  refine ⟨mul_pos (hK'.2.1 g) hp, fun ξ hξ => ?_⟩
  have h1 := hK'.2.2.1 g ξ hξ
  have h2 : height g ξ = ht g ξ * Dt g ^ ((k : ℝ)⁻¹) := by
    unfold ht; field_simp
  rw [h2]
  exact mul_le_mul_of_nonneg_right h1 hp.le

end RowsCompactSum

theorem rows_compact_of_bound : D0 → N0 → H0 → ThetaSeriesBound → K1 → RowsInCompactSet := by
  intro hD hN _ hG3 hK E _ _ _ k hk C₀ hC₀
  refine ⟨fun g => ?_, fun a ha => ?_⟩
  · obtain ⟨B, C, hB, hC, h⟩ := RowsCompactSum.sum_le hN hG3 hk C₀ hC₀ k le_rfl
    obtain ⟨hr, hrh⟩ := RowsCompactSum.r_le hD hK hk g
    have hfin := h g _ hr hrh
    have hne : ∑' ξ : RowT E k k, C₀.indicator (fun _ => (1 : ℝ≥0∞)) (lastRow (ratGL E k (gam ξ) * g)) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hfin
    refine (ENNReal.finite_const_le_of_tsum_ne_top hne one_ne_zero).subset fun ξ hξ => ?_
    simp only [Set.mem_setOf_eq] at hξ ⊢
    rw [Set.indicator_of_mem hξ]
  · obtain ⟨B, C, hB, hC, h⟩ := RowsCompactSum.sum_le hN hG3 hk C₀ hC₀ a ha
    refine ⟨B * C, fun g => ?_⟩
    obtain ⟨hr, hrh⟩ := RowsCompactSum.r_le hD hK hk g
    have hDt := (hD E k).1 g
    have hd := (hK E k hk).2.1 g
    have hp : 0 < Dt g ^ ((k : ℝ)⁻¹) := Real.rpow_pos_of_pos hDt _
    have hw0 : 0 ≤ wt a g := by unfold wt; exact pow_nonneg (le_min zero_le_one hd.le) _
    have hw : wt a g ≤ dmin g ^ a := by unfold wt; exact pow_le_pow_left₀ (le_min zero_le_one hd.le) (min_le_right _ _) _
    calc (∑' ξ : RowT E k k, C₀.indicator (fun _ => (1 : ℝ≥0∞)) (lastRow (ratGL E k (gam ξ) * g))) *
          ENNReal.ofReal (wt a g)
        ≤ ENNReal.ofReal (B * (C * ((dmin g * Dt g ^ ((k : ℝ)⁻¹)) ^ a)⁻¹)) * ENNReal.ofReal (wt a g) := by
          gcongr; exact h g _ hr hrh
      _ = ENNReal.ofReal (B * (C * ((dmin g * Dt g ^ ((k : ℝ)⁻¹)) ^ a)⁻¹) * wt a g) :=
          (ENNReal.ofReal_mul (by positivity)).symm
      _ ≤ ENNReal.ofReal (B * C * Dt g ^ (-(a : ℝ) / k)) := by
          apply ENNReal.ofReal_le_ofReal
          have he : Dt g ^ (-(a : ℝ) / k) = ((Dt g ^ ((k : ℝ)⁻¹)) ^ a)⁻¹ := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hDt.le, ← Real.rpow_neg hDt.le]
            congr 1; ring
          rw [he, mul_pow, mul_inv]
          have hda : 0 < dmin g ^ a := pow_pos hd _
          have hpa : 0 < (Dt g ^ ((k : ℝ)⁻¹)) ^ a := pow_pos hp _
          calc B * (C * ((dmin g ^ a)⁻¹ * ((Dt g ^ ((k : ℝ)⁻¹)) ^ a)⁻¹)) * wt a g
              ≤ B * (C * ((dmin g ^ a)⁻¹ * ((Dt g ^ ((k : ℝ)⁻¹)) ^ a)⁻¹)) * dmin g ^ a := by
                gcongr
            _ = B * C * ((Dt g ^ ((k : ℝ)⁻¹)) ^ a)⁻¹ := by field_simp

end PositivityTheory.AdelicQuotientData

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.DeterminantHeight
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace DeterminantHeight

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem dt_eq (g : GA E k) :
    Dt g = (GroundTheory.Global.IdeleGroup.ideleModule E (AdelicGLn.det E k g) : ℝ) := rfl

theorem dt_maxCompact {κ : GA E k} (hκ : κ ∈ Reduction.maxCompact) : Dt κ = 1 := by
  rw [dt_eq]; exact mem_normOneGL.1 (maxCompact_le_normOneGL hκ)

theorem dt_diag (γ : GL (Fin k) E) : Dt (AdelicGLn.diagonal E k γ) = 1 := by
  rw [dt_eq]; exact mem_normOneGL.1 (rationalGL_le_normOneGL ⟨γ, rfl⟩)

theorem dt_mul (g h : GA E k) : Dt (g * h) = Dt g * Dt h := by
  rw [dt_eq, dt_eq, dt_eq, map_mul, map_mul, Positive.val_mul]

theorem adeleAbs_pos {b : GA E k} (hb : b ∈ adelicBorel) (i : Fin k) :
    0 < adeleAbs ((b : Matrix (Fin k) (Fin k) (Ad E)) i i) := by
  rw [← IsUnit.unit_spec (isUnit_apply_self_of_mem_adelicBorel hb i), adeleAbs_units]
  exact (GroundTheory.Global.IdeleGroup.ideleModule E _).2

theorem dt_borel {b : GA E k} (hb : b ∈ adelicBorel) :
    Dt b = ∏ i, adeleAbs ((b : Matrix (Fin k) (Fin k) (Ad E)) i i) := by
  have hu : ∀ i, IsUnit ((b : Matrix (Fin k) (Fin k) (Ad E)) i i) :=
    isUnit_apply_self_of_mem_adelicBorel hb
  have hdet : AdelicGLn.det E k b = ∏ i, (hu i).unit := by
    ext
    rw [AdelicGLn.coe_det, Matrix.det_of_isUpperTriangular hb, Units.coe_prod]
    simp
  rw [dt_eq, hdet, map_prod (GroundTheory.Global.IdeleGroup.ideleModule E), coe_finset_prod_pos]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← adeleAbs_units, IsUnit.unit_spec]

theorem height_last {b : GA E k} (hb : b ∈ adelicBorel) (L : Fin k) (hL : (L : ℕ) + 1 = k) :
    height b (Pi.single L 1) = adeleAbs ((b : Matrix (Fin k) (Fin k) (Ad E)) L L) := by
  have hu := isUnit_apply_self_of_mem_adelicBorel hb L
  have hrow : ratVec (Pi.single L (1 : E)) ᵥ* (b : Matrix (Fin k) (Fin k) (Ad E)) =
      Pi.single L ((b : Matrix (Fin k) (Fin k) (Ad E)) L L) := by
    have : ratVec (Pi.single L (1 : E)) = Pi.single L (1 : Ad E) := by
      ext l
      by_cases hl : l = L
      · subst hl; simp [ratVec]
      · simp [ratVec, Pi.single_eq_of_ne hl]
    rw [this, single_one_vecMul]
    ext l
    by_cases hl : l = L
    · subst hl; simp [Matrix.row]
    · have hlt : l < L := lt_of_le_of_ne (Fin.le_iff_val_le_val.2 (by omega)) hl
      simp [Matrix.row, Pi.single_eq_of_ne hl, hb hlt]
  rw [Reduction.height, hrow, ← IsUnit.unit_spec hu, adelicNorm_single_units, adeleAbs_units]

end DeterminantHeight

theorem minkowski_bound_of : D0 → MinkowskiBoundAlt := by
  intro _ E _ _ _ k hk
  obtain ⟨t₀, ht₀, hred⟩ := GroundTheory.Automorphic.Reduction.exists_reduced (K := E)
  set s : ℝ := min t₀ 1 with hs
  have hs0 : 0 < s := lt_min ht₀ one_pos
  have hs1 : s ≤ 1 := min_le_right _ _
  refine ⟨(s ^ k)⁻¹, fun g => ?_⟩
  obtain ⟨γ, b, hb, κ, hκ, heq, hr⟩ := hred k g
  set L : Fin k := ⟨k - 1, by omega⟩ with hLdef
  have hL : (L : ℕ) + 1 = k := by simp [L]; omega
  set a : Fin k → ℝ := fun i => adeleAbs ((b : Matrix (Fin k) (Fin k) (Ad E)) i i) with hadef
  have ha : ∀ i, 0 < a i := fun i => DeterminantHeight.adeleAbs_pos hb i
  refine ⟨Pi.single L 1 ᵥ* (γ : Matrix (Fin k) (Fin k) E), ?_, ?_⟩
  · intro h
    have h2 := congrArg (fun y => y ᵥ* ((γ⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fin k) E)) h
    simp only [vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, vecMul_one,
      zero_vecMul] at h2
    have := congrFun h2 L
    simp at this
  · have hH : Reduction.height g (Pi.single L 1 ᵥ* (γ : Matrix (Fin k) (Fin k) E)) = a L := by
      rw [← height_diagonal_mul, heq, height_mul_maxCompact _ hκ, DeterminantHeight.height_last hb L hL]
    have hD : Dt g = ∏ i, a i := by
      have h1 : Dt (AdelicGLn.diagonal E k γ * g) = Dt g := by
        rw [DeterminantHeight.dt_mul, DeterminantHeight.dt_diag, one_mul]
      rw [← h1, heq, DeterminantHeight.dt_mul, DeterminantHeight.dt_maxCompact hκ, mul_one, DeterminantHeight.dt_borel hb]
    have hchain : ∀ d : ℕ, ∀ i : Fin k, (i : ℕ) + d = k - 1 → s ^ d * a L ≤ a i := by
      intro d
      induction d with
      | zero =>
        intro i hi
        have : i = L := Fin.ext (by simp [L]; omega)
        subst this; simp
      | succ d ih =>
        intro i hi
        have hi' : (i : ℕ) + 1 < k := by omega
        have h1 := ih ⟨(i : ℕ) + 1, hi'⟩ (by simp; omega)
        have h2 := hr i ⟨(i : ℕ) + 1, hi'⟩ rfl
        calc s ^ (d + 1) * a L = s * (s ^ d * a L) := by ring
          _ ≤ s * a ⟨(i : ℕ) + 1, hi'⟩ := mul_le_mul_of_nonneg_left h1 hs0.le
          _ ≤ t₀ * a ⟨(i : ℕ) + 1, hi'⟩ := mul_le_mul_of_nonneg_right (min_le_left _ _) (ha _).le
          _ ≤ a i := h2
    have hlow : ∀ i, s ^ k * a L ≤ a i := fun i =>
      (mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hs0.le hs1 (by omega : k - 1 - (i : ℕ) ≤ k))
        (ha L).le).trans (hchain (k - 1 - (i : ℕ)) i (by omega))
    have hsa : 0 < s ^ k * a L := mul_pos (pow_pos hs0 k) (ha L)
    have hprod : (s ^ k * a L) ^ k ≤ Dt g := by
      rw [hD]
      calc (s ^ k * a L) ^ k = ∏ _i : Fin k, s ^ k * a L := by simp
        _ ≤ ∏ i, a i := Finset.prod_le_prod₀ (fun _ _ => hsa.le) (fun i _ => hlow i)
    have hDt : 0 < Dt g := by rw [hD]; exact Finset.prod_pos fun i _ => ha i
    have hDpos : 0 < Dt g ^ ((k : ℝ)⁻¹) := Real.rpow_pos_of_pos hDt _
    have hDk : (Dt g ^ ((k : ℝ)⁻¹)) ^ k = Dt g := Real.rpow_inv_natCast_pow hDt.le (by omega)
    have hle : s ^ k * a L ≤ Dt g ^ ((k : ℝ)⁻¹) :=
      (pow_le_pow_iff_left₀ hsa.le hDpos.le (by omega : k ≠ 0)).1 (hprod.trans hDk.ge)
    have hsk : 0 < s ^ k := pow_pos hs0 k
    rw [ht, hH, div_le_iff₀ hDpos, inv_mul_eq_div, le_div_iff₀ hsk]
    linarith

end PositivityTheory.AdelicQuotientData

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.NormAverageBound
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace NormAverageBound

theorem norm_avg_le {G : Type} [AddCommGroup G] [TopologicalSpace G] (Γ : AddSubgroup G) (Φ : G → ℂ) (C : ℝ)
    (hC : 0 ≤ C) (h : ∀ x, ‖Φ x‖ ≤ C) : ‖avg Γ Φ‖ ≤ C := by
  unfold GlobalTheory.CuspGeneric.avg
  split_ifs with hex
  · obtain ⟨-, -, h1⟩ := hex.choose_spec
    have hfin : hex.choose.1 hex.choose.2 < ⊤ := by rw [h1]; exact ENNReal.one_lt_top
    calc ‖∫ x in hex.choose.2, Φ x ∂hex.choose.1‖ ≤ C * hex.choose.1.real hex.choose.2 :=
          norm_setIntegral_le_of_norm_le_const hfin (fun x _ => h x)
      _ = C := by simp [Measure.real, h1]
  · simpa using hC

end NormAverageBound

open NormAverageBound in
theorem fourier_column_of : N0 → P0 → P1 → CornerEmbedding → FourierSeriesColumn := by
  intro hN0 hP0 hP1 hK5e E _ _ _ m k hk hkm ψ hψ ι hι F hF g
  obtain ⟨hFc, hFl, hFlaw, hFvan⟩ := hF
  have hPre : PositivityTheory.AdelicQuotientData.Pre ψ k F := ⟨hFc, hFl, hFlaw⟩
  obtain ⟨hcolPre, hcoef, -, -⟩ := hP1 E m ψ hψ k hk hkm F hPre
  obtain ⟨-, hcolL, -⟩ := hcolPre
  obtain ⟨hgamM, huniqM, -⟩ := hN0 E m k hk hkm.le
  obtain ⟨hgamK, -⟩ := hN0 E k k hk le_rfl
  obtain ⟨hex, hprops⟩ := hK5e E m k hkm.le
  obtain ⟨ιE, hιE⟩ := hex E
  obtain ⟨-, -, -, -, -, -, hrat, -⟩ := hprops ι hι
  have hlift : ∀ ρ : RowT E k k, ∃ ρ' : RowT E m k, ∀ i : Fin m,
      Subtype.val ρ' i = if h : (i : ℕ) < k then Subtype.val ρ ⟨i, h⟩ else 0 := by
    intro ρ
    refine ⟨Subtype.mk (fun i : Fin m => if h : (i : ℕ) < k then Subtype.val ρ ⟨i, h⟩ else 0) ⟨?_, ?_⟩,
      fun i => rfl⟩
    · obtain ⟨c, hc⟩ := Function.ne_iff.1 (Subtype.property ρ).1
      intro h0
      apply hc
      have h1 := congrFun h0 ⟨c, lt_trans c.isLt hkm⟩
      simpa [c.isLt] using h1
    · intro i hi
      simp [show ¬ (i : ℕ) < k by omega]
  choose lift hlift using hlift
  have hA : ∀ ρ : RowT E k k, coefF ψ k (fun t : UnipotentBlockColumnIndex m k k => Subtype.val (lift ρ) (Subtype.val t).1) F (ι g) =
      colT ψ k F (ι (ratGL E k (gam ρ) * g)) := by
    intro ρ
    rw [hcoef (lift ρ) (ι g), map_mul, hrat ιE hιE]
    have hBlk : PositivityTheory.jumpWindows.GlobalTheory k (ιE (gam ρ)) := by
      intro i c hic
      rw [hιE (gam ρ)]
      simp only [PositivityTheory.AdelicQuotientData.embM, Matrix.of_apply]
      rw [dite_eq_right (by omega)]
    obtain ⟨⟨ξ'', p⟩, ⟨hp, hγ⟩, -⟩ := huniqM _ hBlk
    have hξ : ξ'' = lift ρ := by
      apply Subtype.ext
      funext c
      have hrow := congrArg (fun γ : GL (Fin m) E => (γ : Matrix (Fin m) (Fin m) E) ⟨k - 1, by omega⟩ c) hγ
      simp only [hιE (gam ρ), Units.val_mul, Matrix.mul_apply] at hrow
      have hpr : ∀ l, (p : Matrix (Fin m) (Fin m) E) ⟨k - 1, by omega⟩ l =
          (1 : Matrix (Fin m) (Fin m) E) ⟨k - 1, by omega⟩ l := fun l => hp _ _ (Or.inl le_rfl)
      simp only [hpr, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
        if_true] at hrow
      rw [(hgamM ξ'').2 ⟨k - 1, by omega⟩ c (by show k - 1 + 1 = k; omega)] at hrow
      rw [← hrow, hlift ρ c]
      simp only [PositivityTheory.AdelicQuotientData.embM, Matrix.of_apply]
      by_cases hc : (c : ℕ) < k
      · rw [dite_eq_left ⟨by show k - 1 < k; omega, hc⟩, dite_eq_left hc]
        exact (hgamK ρ).2 _ _ (by show k - 1 + 1 = k; omega)
      · rw [dite_eq_right (fun h => hc h.2), dite_eq_right hc, Matrix.one_apply, if_neg]
        intro h
        apply hc
        rw [← h]
        show k - 1 < k
        omega
    rw [hγ, map_mul, mul_assoc, hcolL p hp, hξ]
  have hcoef0 : coefF ψ k (0 : UnipotentBlockColumnIndex m k k → E) F (ι g) = 0 := by
    have h0 := hFvan k (by omega) le_rfl (ι g)
    simpa [GlobalTheory.CuspGeneric.coefF, GlobalTheory.CuspGeneric.dot] using h0
  have hinj : Function.Injective
      (fun ρ : RowT E k k => fun t : UnipotentBlockColumnIndex m k k => Subtype.val (lift ρ) (Subtype.val t).1) := by
    intro ρ₁ ρ₂ h
    apply Subtype.ext
    funext j
    have h1 := congrFun h (Subtype.mk ((⟨j, lt_trans j.isLt hkm⟩ : Fin m), (⟨k, hkm⟩ : Fin m))
      ⟨j.isLt, le_rfl, le_rfl⟩ : UnipotentBlockColumnIndex m k k)
    beta_reduce at h1
    rw [hlift, hlift, dite_eq_left j.isLt, dite_eq_left j.isLt] at h1
    exact h1
  have hkey : ∀ t : UnipotentBlockColumnIndex m k k, t = (Subtype.mk ((⟨((Subtype.val t).1 : ℕ), ((Subtype.val t).1).isLt⟩ : Fin m),
      (⟨k, hkm⟩ : Fin m)) ⟨(Subtype.property t).1, le_rfl, le_rfl⟩ : UnipotentBlockColumnIndex m k k) := by
    intro t
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Fin.ext
      show ((Subtype.val t).2 : ℕ) = k
      have h2 := Subtype.property t
      omega
  have hsurj : ∀ c : UnipotentBlockColumnIndex m k k → E, c ≠ 0 → ∃ ρ : RowT E k k,
      (fun t : UnipotentBlockColumnIndex m k k => Subtype.val (lift ρ) (Subtype.val t).1) = c := by
    intro c hc
    obtain ⟨ρ, hρ⟩ : ∃ ρ : RowT E k k, ∀ j : Fin k, Subtype.val ρ j =
        c (Subtype.mk ((⟨j, lt_trans j.isLt hkm⟩ : Fin m), (⟨k, hkm⟩ : Fin m)) ⟨j.isLt, le_rfl, le_rfl⟩ :
          UnipotentBlockColumnIndex m k k) := by
      refine ⟨Subtype.mk (fun j : Fin k => c (Subtype.mk ((⟨j, lt_trans j.isLt hkm⟩ : Fin m),
        (⟨k, hkm⟩ : Fin m)) ⟨j.isLt, le_rfl, le_rfl⟩ : UnipotentBlockColumnIndex m k k))
        ⟨?_, fun i hi => absurd hi (not_le.2 i.isLt)⟩, fun j => rfl⟩
      intro h0
      apply hc
      funext t
      rw [hkey t]
      exact congrFun h0 ⟨((Subtype.val t).1 : ℕ), (Subtype.property t).1⟩
    refine ⟨ρ, ?_⟩
    funext t
    show Subtype.val (lift ρ) (Subtype.val t).1 = c t
    rw [hlift, dite_eq_left (Subtype.property t).1, hρ]
    exact congrArg c (hkey t).symm
  have hoff : ∀ c : UnipotentBlockColumnIndex m k k → E,
      c ∉ Set.range (fun ρ : RowT E k k => fun t : UnipotentBlockColumnIndex m k k => Subtype.val (lift ρ) (Subtype.val t).1) →
        coefF ψ k c F (ι g) = 0 := by
    intro c hc
    by_cases hc0 : c = 0
    · rw [hc0]; exact hcoef0
    · exact absurd (hsurj c hc0) (fun h => hc h)
  have hper : Per (ratV E (UnipotentBlockColumnIndex m k k)) (fun x => F (blkU x * ι g)) :=
    per_blk hFc (fun c h => hFl _ (isMir_blkU c) h) (ι g)
  obtain ⟨-, hP0b, hP0c⟩ := hP0 E ψ hψ (UnipotentBlockColumnIndex m k k)
  refine ⟨?_, ?_⟩
  · intro B hB
    have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
    have hpar : HasSum (fun c => coefF ψ k c F (ι g) * (starRingEnd ℂ) (coefF ψ k c F (ι g)))
        (avg (ratV E (UnipotentBlockColumnIndex m k k)) fun x => F (blkU x * ι g) * (starRingEnd ℂ) (F (blkU x * ι g))) :=
      hP0b _ _ hper hper
    have hS := (hinj.hasSum_iff (f := fun c => coefF ψ k c F (ι g) * (starRingEnd ℂ) (coefF ψ k c F (ι g)))
      (fun c hc => by simp only [hoff c hc, zero_mul])).2 hpar
    have hSle : ‖avg (ratV E (UnipotentBlockColumnIndex m k k)) fun x => F (blkU x * ι g) * (starRingEnd ℂ) (F (blkU x * ι g))‖ ≤ B ^ 2 :=
      norm_avg_le _ _ _ (sq_nonneg B) (fun x => by
        simpa [norm_mul, sq] using mul_le_mul (hB x) (hB x) (norm_nonneg _) hB0)
    have hre := ((Complex.hasSum_iff _ _).1 hS).1
    simp only [Function.comp_def, Complex.mul_conj, Complex.ofReal_re] at hre
    simp only [Complex.mul_conj] at hSle
    have hterm : ∀ ρ : RowT E k k, ‖colT ψ k F (ι (ratGL E k (gam ρ) * g))‖ₑ ^ 2 =
        ENNReal.ofReal (Complex.normSq (coefF ψ k (fun t : UnipotentBlockColumnIndex m k k => Subtype.val (lift ρ) (Subtype.val t).1) F (ι g))) := by
      intro ρ
      rw [hA ρ, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), Complex.normSq_eq_norm_sq]
    calc ∑' ρ : RowT E k k, ‖colT ψ k F (ι (ratGL E k (gam ρ) * g))‖ₑ ^ 2
        = ∑' ρ : RowT E k k, ENNReal.ofReal (Complex.normSq
            (coefF ψ k (fun t : UnipotentBlockColumnIndex m k k => Subtype.val (lift ρ) (Subtype.val t).1) F (ι g))) := tsum_congr hterm
      _ = ENNReal.ofReal (∑' ρ : RowT E k k, Complex.normSq
            (coefF ψ k (fun t : UnipotentBlockColumnIndex m k k => Subtype.val (lift ρ) (Subtype.val t).1) F (ι g))) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun _ => Complex.normSq_nonneg _) hre.summable).symm
      _ ≤ ENNReal.ofReal (B ^ 2) := by
          rw [hre.tsum_eq]
          exact ENNReal.ofReal_le_ofReal (le_trans (Complex.re_le_norm _) hSle)
  · intro hfin
    have hfin' : {c : UnipotentBlockColumnIndex m k k → E | coefF ψ k c F (ι g) ≠ 0}.Finite := by
      refine (hfin.image (fun ρ : RowT E k k => fun t : UnipotentBlockColumnIndex m k k => Subtype.val (lift ρ) (Subtype.val t).1)).subset ?_
      intro c hc
      have hc0 : c ≠ 0 := by
        rintro rfl
        exact hc hcoef0
      obtain ⟨ρ, rfl⟩ := hsurj c hc0
      refine ⟨ρ, ?_, rfl⟩
      show colT ψ k F (ι (ratGL E k (gam ρ) * g)) ≠ 0
      rw [← hA ρ]
      exact hc
    have hs : HasSum (fun c => coefF ψ k c F (ι g)) (F (blkU (0 : UnipotentBlockColumnIndex m k k → GlobalTheory.CuspRep.Ad E) * ι g)) :=
      hP0c _ hper hfin'
    have hb0 : blkU (0 : UnipotentBlockColumnIndex m k k → GlobalTheory.CuspRep.Ad E) = 1 := by
      unfold GlobalTheory.CuspGeneric.blkU
      exact GlobalTheory.CuspGeneric.posU_zero _
    rw [hb0, one_mul] at hs
    have hs2 := (hinj.hasSum_iff (f := fun c => coefF ψ k c F (ι g)) hoff).2 hs
    show ∑' ρ : RowT E k k, colT ψ k F (ι (ratGL E k (gam ρ) * g)) = F (ι g)
    rw [← hs2.tsum_eq]
    exact tsum_congr fun ρ => (hA ρ).symm

end PositivityTheory.AdelicQuotientData

end
end

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

theorem rsPole_of_inputs (eJS2G0 : jumpWindows.G0) (eCAUCHY : CAUCHY) (eJS2S1 : jumpWindows.S1) (eJS1L7 : JacquetShalikaLocal.L7) (eJS1L12 : JacquetShalikaLocal.lift_levelP_alt₂) (eJS2G5 : jumpWindows.G5) (eJS2S7 : jumpWindows.S7) (eJS2S10 : jumpWindows.MirabolicColumnBlock) (eJS2G5b : jumpWindows.G5b) (eJS2S2 : jumpWindows.S2) (eJS2S9 : jumpWindows.S9) (eJS2G1 : jumpWindows.G1) (eJS2G1b : jumpWindows.AlmostEverywhereSpherical) (eJS2G2c : jumpWindows.G2c) (eJS2G2a : jumpWindows.G2a) (eJS2G11 : jumpWindows.FourierUniquenessMirabolic) (eJS2S4 : jumpWindows.S4) (eJS2S8 : jumpWindows.S8) (eJS2G14 : jumpWindows.CuspidalIrreducibleSubrep) (eJS2SmoNorm : jumpWindows.SmoNorm) (eBlkJacquetShalikaBound : GlobalTheory.Published.JacquetShalikaBound) (eJS2G10 : jumpWindows.StandardCharacterExists) : RSPole :=
  have hQ1 : Q1 := isUnit_last_join
  have hQ2 : Q2 := closedSubgroup_cutoff_exists
  have hD0 : D0 := determinant_basic_of_G0 eJS2G0
  have hMOD0 : AdelicLinearChange := linear_change_variables_of hD0
  have hK5e : CornerEmbedding := corner_embedding_of eJS2G0
  have hMOD1 : ColumnConjugationMeasure := algebraic_modulus_one_of_finiteOrder_char hMOD0 hK5e
  have hN0 : N0 := mem_unipotent_fixer_of
  have hN1 : N1 := monic_polynomial_is_matrix_charpoly hD0 hMOD1
  have hN2 : N2 := nm_agrees_with_twisted_norm_sigmaGL hD0 eJS2G0
  have hN3 : N3 := galois_fixed_adelic_matrices_descend hD0 hN0 hN1
  have hN4a : CosetIntegralParabolic := coset_integration_of hN0 hN1 hN3
  have hN4b : OneMoreAdelicColumn := one_more_column_of hD0 hN0 hN1 hN3 hMOD1
  have hW0 : W0 := fundamental_domain_of hQ1 hD0 hN3
  have hV1 : V1 := volume_shell_of hQ1 hQ2 hD0 hN3 hW0
  have hP0 : P0 := poisson_base_holds
  have hP1 : P1 := p1_holds hN0 hP0
  have hP2 : P2 := p2_of hP1
  have hP3 : P3 := crystalline_clause_of_admitted
  have hU1 : U1 := twistedGeometricSide_unfolding hQ1 hQ2 hN0 hN3 hN4a hN4b hP0 hP1 hP2
  have hU2 : U2 := unitaryGroupGeometricSide_of_quotient_identities hU1 hP1
  have hU0 : U0 := unipotent_integral_of hQ1 hQ2 hN0 hN3 hN4a
  have hH0 : H0 := height_change_of_D0 hD0
  have hG1d : CuspDecayShortRowColumn := cusp_decay_short_row_of hD0 hH0
  have hG2m : MinkowskiBoundAlt := minkowski_bound_of hD0
  have hG3t : ThetaSeriesBound := theta_bound_holds
  have hG4t : ThetaDecaying := theta_decaying_of_bound hD0 hN0 hH0 hG3t
  have hK1 : K1 := firstCohomologyBound_of_boundaryBound hD0 hH0
  have hG5t : RowsInCompactSet := rows_compact_of_bound hD0 hN0 hH0 hG3t hK1
  have hC0 : C0 := open_decomposition_of_G0 eJS2G0
  have hC1 : C1 := sum_wt_mul_massS_le_inv_pow_mul_total_mass hQ1 hQ2 hN2 hN3
  have hC2 : C2 := torus_exponential_of_open eJS2G0 hC0 hC1
  have hD1 : D1 := log_norm_estimate_of_Q hQ1 hD0 hN3 hC0
  have hE1 : E1 := height_bound_of_weights hD0 hW0 hV1
  have hE2 : E2 := duality_diagonalClass_of_affineProperBaseChange hD0 hV1 hE1
  have hM0 : M0 := moderate_growth_of hD0 hN0 hP2 hU0 hU2 hV1 hG4t
  have hK8a : LocalHeckeAlgebra := localHeckeAlgebra_statement
  have hM1 : M1 := mean_convergence_of eJS2G0 hD0 hP2 hC0 hC2 hD1 hM0 hK8a eCAUCHY
  have hK2 : K2 := secondCohomologyBound_of_boundaryBound hH0 hK1
  have hK3 : K3 := koszulThree_of_det eJS2S1 hH0 hG1d hK1
  have hK7 : K7 := local_unramified_of eJS1L7 eJS1L12 eJS2G0 eJS2G5
  have hK8 : K8 := spherical_function_of eJS2G0 eJS2G5 hC0 hK7
  have hK4a : InfinitePlaceStep := infinite_place_step_of eJS2S7 eJS2S10 eJS2G0 eJS2G5 eJS2G5b hP2
  have hK4b : FinitePlaceStep := finite_place_of_jump_windows eJS2S2 eJS2S9 eJS2S10 eJS2G0 eJS2G5 eJS2G5b hP2
  have hK4 : K4 := kept_block_at_of_pair_level_chain_threshold eJS2S10 eJS2G0 hK4a hK4b
  have hK9 : K9 := global_level_of eJS2G0 eJS2G1 eJS2G1b eJS2G2c eJS2G5 hK8
  have hKIR : KIR := kir_of eJS2S2 eJS2G0 eJS2G2a eJS2G2c eJS2G5 eJS2G5b hK2 hK3 hK4 hK9
  have hKSec : KSec := ksec_of eJS2G2c eJS2G5 hG1d hK9
  have hK5a : TransformsEmbedding := transform_embedding_of eJS2G11 hP0 hP1 hP2 hK5e
  have hK5b : FourierSeriesColumn := fourier_column_of hN0 hP0 hP1 hK5e
  have hK5c : ShortRowsEmbedding := short_rows_embedding_of hD0 hG2m hK1 hK5e
  have hK6 : K6 := last_row_integral_of eJS2G0 hK5e hK8
  have hKU : KU := ku_of eJS2G5 hD0
  have hKLt1 : KLt1 := kernel_less_first_of eJS2G0 eJS2G5 hD0 hP2 hC0 hK1 hK5e hK5a hK5b hK5c hK6 hK7 hK8 hK8a hKU
  have hKLt2 : KLt2 := kernel_less_second_of hD0 hN0 hH0 hG5t hK1 hK5e hK5a hK5b hK5c hK6
  have hK11 : LastRowCutoff := last_row_cutoff_of eJS2S4 eJS2S8 eJS2G0
  have hK12 : PoissonCutoffFormula := poisson_cutoff_of hD0 hMOD0 hN0 hH0 hG3t hK1
  have hKEq1 : KEq1 := kernel_equality_first_of eJS2G0 eJS2G5 hD0 hN0 hP2 hP3 hC0 hG5t hK1 hK7 hK8 hK8a hKU
  have hKEq2 : KEq2 := kernel_equality_second_of hD0 hN0 hH0 hG4t hG5t hK12
  have hORT : ORT := cusp_orthogonality_of eJS2G14 eJS2SmoNorm hQ2 hD0 hN3 hW0
  have hKY : KY := ky_of hW0
  have hRSPole : RSPole := rspole_of eBlkJacquetShalikaBound eJS2G1 eJS2G10 hW0 hE2 hM1 hKIR hKSec hK5e hKLt1 hKLt2 hK11 hKEq1 hKEq2 hORT hKY
  hRSPole

end PositivityTheory.AdelicQuotientData

end
