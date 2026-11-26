module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameBoundSpaces.FrameBound
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.HyperbolicEntryBounds.AllLeavesMono
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.FullThetaHolds
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.QuadraticCharacterNorms.QuadCharNorm
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.QuadraticCharacterNorms.BadEx2Of
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.HyperbolicEntryBounds.ArchFinal
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.Count1
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.G2OfLocalOrbitCharacter
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalIntegralUnitIndicatorEventuallyOneClass
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterHolds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactSupportDcos
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelExistsBis

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitPlaceExists
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitPlaceExists
open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.Ex0 PositivityTheory.Rg.Bc.ArchbcB.B
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.SplitLevel

theorem exists_reps {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K K' : Subgroup G)
    (hc : IsCompact (K : Set G)) (ho : IsOpen (K' : Set G)) :
    ∃ X : Finset G, (∀ x ∈ X, x ∈ K) ∧ ∀ k ∈ K, ∃! x ∈ X, x⁻¹ * k ∈ K' := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hc
  have hop : IsOpen ((K'.subgroupOf K : Subgroup K) : Set K) := by
    rw [Subgroup.coe_subgroupOf]
    exact ho.preimage continuous_subtype_val
  haveI : Finite (K ⧸ K'.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ hop
  haveI := Fintype.ofFinite (K ⧸ K'.subgroupOf K)
  refine ⟨Finset.univ.image fun q : K ⧸ K'.subgroupOf K => ((q.out : K) : G), ?_, ?_⟩
  · intro x hx
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hx
    exact q.out.2
  · intro k hk
    let q₀ : K ⧸ K'.subgroupOf K := QuotientGroup.mk ⟨k, hk⟩
    refine ⟨((q₀.out : K) : G), ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩, ?_⟩
    · have h : (q₀.out)⁻¹ * ⟨k, hk⟩ ∈ K'.subgroupOf K := QuotientGroup.eq.1 (QuotientGroup.out_eq' q₀)
      exact Subgroup.mem_subgroupOf.1 h
    · rintro x ⟨hx, hxk⟩
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hx
      have h : q = q₀ := by
        rw [← QuotientGroup.out_eq' q]
        exact QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 hxk)
      rw [h]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem congSub_conj (w : Pl E) (n m : ℕ) : ∀ k ∈ GlobalTheory.LFun.KGL w (n := n), ∀ k' ∈ GlobalTheory.PrincCong.congSub w n m,
    k * k' * k⁻¹ ∈ GlobalTheory.PrincCong.congSub w n m := by
  rintro _ ⟨h, rfl⟩ _ ⟨h', hh', rfl⟩
  refine ⟨h * h' * h⁻¹, ?_, by simp⟩
  exact Subgroup.Normal.conj_mem h' hh' h

def lev (w : Pl E) (μ : (w.adicCompletion E)ˣ →* ℂˣ) (m b : ℕ) : Subgroup (GLw b w) :=
  GlobalTheory.PrincCong.congSub w b m ⊓ μ.ker.comap GeneralLinearGroup.det

theorem continuous_det (w : Pl E) (b : ℕ) :
    Continuous (GeneralLinearGroup.det : GLw b w → (w.adicCompletion E)ˣ) :=
  Units.continuous_iff.2 ⟨Continuous.matrix_det Units.continuous_val,
    Continuous.matrix_det (Units.continuous_val.comp continuous_inv)⟩

theorem isLevel_lev (w : Pl E) (hw : IsSplitAt w) (μ : (w.adicCompletion E)ˣ →* ℂˣ)
    (hμ : IsOpen (μ.ker : Set (w.adicCompletion E)ˣ)) (m b : ℕ) :
    GlobalTheory.BCT.IsLevel (thL b w) (GlobalTheory.LFun.KGL w (n := b)) (lev w μ m b) := by
  refine ⟨?_, fun g hg => ((GlobalTheory.PrincCong.mem_congSub_iff w b m g).1 hg.1).1, fun k hk => ?_⟩
  · exact (GlobalTheory.PrincCong.isOpen_congSub w b m).inter (hμ.preimage (continuous_det w b))
  · have ht : thL b w = MonoidHom.id _ := by unfold thL; rw [if_pos hw]
    rw [ht]
    exact hk

theorem blk_mem {a b n : ℕ} (h : a + b = n) (w : Pl E) (m : ℕ) (y : GLw a w × GLw b w)
    (h1 : y.1 ∈ GlobalTheory.PrincCong.congSub w a m) (h2 : y.2 ∈ GlobalTheory.PrincCong.congSub w b m) :
    blk h w y 0 ∈ GlobalTheory.PrincCong.congSub w n m := by
  rw [GlobalTheory.CompanionTheory.GL3BlockMatrixLocal.blk_zero_eq, GlobalTheory.PrincCong.mem_congSub_iff]
  obtain ⟨k1, e1⟩ := (GlobalTheory.PrincCong.mem_congSub_iff w a m _).1 h1
  obtain ⟨k2, e2⟩ := (GlobalTheory.PrincCong.mem_congSub_iff w b m _).1 h2
  have hI1 := GlobalTheory.AdelicU.mem_GLint_iff.1 k1
  have hI2 := GlobalTheory.AdelicU.mem_GLint_iff.1 k2
  refine ⟨GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩, fun i j => ?_⟩
  · rw [CtLevel.dgM_val]
    exact CtLevel.blockDiagonalMatrixOfAddEq_entries_mem_subring _ h _ _ hI1.1 hI2.1 i j
  · rw [← map_inv, CtLevel.dgM_val]
    exact CtLevel.blockDiagonalMatrixOfAddEq_entries_mem_subring _ h _ _ hI1.2 hI2.2 i j
  · obtain ⟨i', rfl⟩ := (CtLevel.blkEq h).surjective i
    obtain ⟨j', rfl⟩ := (CtLevel.blkEq h).surjective j
    have hone : ∀ p q, (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (CtLevel.blkEq h p) (CtLevel.blkEq h q) =
        (1 : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) (w.adicCompletion E)) p q := by
      intro p q
      simp [Matrix.one_apply, (CtLevel.blkEq h).injective.eq_iff]
    rw [hone]
    rcases i' with i' | i' <;> rcases j' with j' | j'
    · rw [(GlobalTheory.CompanionTheory.GL3BlockMatrixLocal.dgM_entries h w y).1]
      simpa [Matrix.one_apply] using e1 i' j'
    · rw [CtLevel.dgM_val, CtLevel.dgMat, reindex_apply, submatrix_apply, Equiv.symm_apply_apply,
        Equiv.symm_apply_apply]
      simp
    · rw [CtLevel.dgM_val, CtLevel.dgMat, reindex_apply, submatrix_apply, Equiv.symm_apply_apply,
        Equiv.symm_apply_apply]
      simp
    · rw [(GlobalTheory.CompanionTheory.GL3BlockMatrixLocal.dgM_entries h w y).2]
      simpa [Matrix.one_apply] using e2 i' j'

theorem splitEx : SplitEx := by
  intro E _ _ _ n w hw μ hμ m hm KB hKB
  have hKc := (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w n).2
  have ho := GlobalTheory.PrincCong.isOpen_congSub w n m
  have hle : GlobalTheory.PrincCong.congSub w n m ≤ GlobalTheory.LFun.KGL w (n := n) :=
    fun g hg => ((GlobalTheory.PrincCong.mem_congSub_iff w n m g).1 hg).1
  have hcl : IsClosed (GlobalTheory.PrincCong.congSub w n m : Set (GLw n w)) := Subgroup.isClosed_of_isOpen _ ho
  have hc : IsCompact (GlobalTheory.PrincCong.congSub w n m : Set (GLw n w)) := hKc.of_isClosed_subset hcl hle
  obtain ⟨X, hX, hXu⟩ := exists_reps (GlobalTheory.LFun.KGL w (n := n)) (GlobalTheory.PrincCong.congSub w n m) hKc ho
  refine ⟨GlobalTheory.PrincCong.congSub w n m, X, (GlobalTheory.PrincCong.congSub w n m : Set (GLw n w)).indicator 1,
    fun a => (lev w μ m a).prod (lev w μ m (n - a)), ?_, ho, hle, congSub_conj w n m, hX, hXu, ?_, ?_⟩
  · ext k
    rw [Subgroup.mem_subgroupOf, GlobalTheory.PrincCong.mem_congSub_iff, hKB k]
    exact Iff.rfl
  · refine ⟨ho, hc, ?_, fun k₁ hk₁ k₂ hk₂ g => ?_⟩
    · refine HasCompactSupport.of_support_subset_isCompact hc ?_
      intro g hg
      by_contra h
      exact hg (Set.indicator_of_notMem h _)
    · have hiff : k₁ * g * k₂ ∈ GlobalTheory.PrincCong.congSub w n m ↔ g ∈ GlobalTheory.PrincCong.congSub w n m := by
        rw [Subgroup.mul_mem_cancel_right _ hk₂, Subgroup.mul_mem_cancel_left _ hk₁]
      by_cases hg : g ∈ GlobalTheory.PrincCong.congSub w n m
      · rw [Set.indicator_of_mem (show _ ∈ (GlobalTheory.PrincCong.congSub w n m : Set (GLw n w)) from hiff.2 hg),
          Set.indicator_of_mem (show _ ∈ (GlobalTheory.PrincCong.congSub w n m : Set (GLw n w)) from hg)]
        rfl
      · rw [Set.indicator_of_notMem (show _ ∉ (GlobalTheory.PrincCong.congSub w n m : Set (GLw n w)) from fun h => hg (hiff.1 h)),
          Set.indicator_of_notMem (show _ ∉ (GlobalTheory.PrincCong.congSub w n m : Set (GLw n w)) from hg)]
  · intro a ha
    refine ⟨⟨_, _, rfl, isLevel_lev w hw μ hμ m a, isLevel_lev w hw μ hμ m (n - a)⟩, fun y hy => ⟨?_, ?_⟩⟩
    · exact blk_mem (Nat.add_sub_of_le ha) w m y hy.1.1 hy.2.1
    · have d1 : μ (GeneralLinearGroup.det y.1) = 1 := hy.1.2
      have d2 : μ (GeneralLinearGroup.det y.2) = 1 := hy.2.2
      rw [map_mul, map_pow, map_pow, d1, d2, one_pow, one_pow, one_mul]

end GlobalTheory.CompanionTheory.SplitLevel

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitPlaceExistsStatement
open NumberField GlobalTheory.BCT Formalism.L2.Host PositivityTheory.Rg.BcB.F.Ex0 PositivityTheory.Rg.Bc.ArchbcB.B
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_place_exists : SplitEx := by
  first | exact @GlobalTheory.CompanionTheory.SplitLevel.splitEx | exact GlobalTheory.CompanionTheory.SplitLevel.splitEx | (intros; apply GlobalTheory.CompanionTheory.SplitLevel.splitEx <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionExistsStatement
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionExistsAlt
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.Ex0 PositivityTheory.Rg.Bc.ArchbcB.B
open scoped Classical

namespace GlobalTheory.CompanionTheory.SecThrough

theorem secEx : SecEx := by
  intro E _ _ _ S₀ hS₀
  let f : Pl E → HeightOneSpectrum (𝓞 (maximalRealSubfield E)) := fun w => w.under (𝓞 (maximalRealSubfield E))
  have hex : ∀ y : Set.range f, ∃ u : Pl E, f u = y.1 ∧ ∀ w ∈ S₀, f w = y.1 → u = w := by
    rintro ⟨_, w₀, rfl⟩
    by_cases h : ∃ w ∈ S₀, f w = f w₀
    · obtain ⟨w, hw, hfw⟩ := h
      exact ⟨w, hfw, fun w' hw' _ => Finset.card_le_one.1 hS₀ w hw w' hw'⟩
    · exact ⟨w₀, rfl, fun w hw hfw => absurd ⟨w, hw, hfw⟩ h⟩
  let g : Set.range f → Pl E := fun y => (hex y).choose
  have hg : ∀ y, f (g y) = y.1 := fun y => (hex y).choose_spec.1
  have hg₀ : ∀ y, ∀ w ∈ S₀, f w = y.1 → g y = w := fun y => (hex y).choose_spec.2
  refine ⟨Set.range g, fun w => ⟨g ⟨f w, w, rfl⟩, ⟨⟨_, rfl⟩, hg _⟩, ?_⟩, ?_, ?_⟩
  · rintro _ ⟨⟨y, rfl⟩, hy⟩
    exact congrArg g (Subtype.ext ((hg y).symm.trans hy))
  · intro w hw
    exact ⟨⟨f w, w, rfl⟩, hg₀ _ w hw rfl⟩
  · intro w hw
    refine ⟨⟨f w, w, rfl⟩, ?_⟩
    by_contra hne
    exact hw ⟨_, hne, hg _⟩

end GlobalTheory.CompanionTheory.SecThrough

end
end

open NumberField GlobalTheory.BCT Formalism.L2.Host PositivityTheory.Rg.BcB.F.Ex0 PositivityTheory.Rg.Bc.ArchbcB.B
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sec_ex : SecEx := by
  first | exact @GlobalTheory.CompanionTheory.SecThrough.secEx | exact GlobalTheory.CompanionTheory.SecThrough.secEx | (intros; apply GlobalTheory.CompanionTheory.SecThrough.secEx <;> assumption)
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.CongruenceInertMatching
theorem PositivityTheory.HtPt.Bc.CongruenceInertMatching.matchCongInert : type_of% @GlobalTheory.CongMatch.match_principal_congruence_inert := @GlobalTheory.CongMatch.match_principal_congruence_inert
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.HyperbolicEntryBounds.ChainFinal
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitalSignAlmostEverywhere
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KapOrbUnitEqOne
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.UnitOrbCount

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem cp_conj {n : ℕ} {w : Pl E} (g γ : UL n w) :
    (g⁻¹ * γ * g).1.val.charpoly = γ.1.val.charpoly := by
  have h : ((g⁻¹ * γ * g : UL n w) : GLw n w) = (g : GLw n w)⁻¹ * (γ : GLw n w) * (g : GLw n w) := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  have h2 : (g⁻¹ * γ * g).1.val = ((g : GLw n w)⁻¹ : GLw n w).val * γ.1.val * (g : GLw n w).val := by
    rw [← Units.val_mul, ← Units.val_mul]
    exact congrArg Units.val h
  rw [h2, Matrix.coe_units_inv]
  exact Matrix.charpoly_units_conj' (g : GLw n w) γ.1.val

theorem mk_eq_iff {G : Type} [Group G] (x y : G) :
    (Quot.mk _ x : TwCl (MonoidHom.id G)) = Quot.mk _ y ↔ ∃ g : G, y = g⁻¹ * x * g := by
  constructor
  · intro h
    have h' := Quot.eqvGen_exact h
    clear h
    induction h' with
    | rel a b hab => obtain ⟨g, hg⟩ := hab; exact ⟨g, by simpa using hg⟩
    | refl a => exact ⟨1, by simp⟩
    | symm a b _ ih => obtain ⟨g, hg⟩ := ih; exact ⟨g⁻¹, by rw [hg]; group⟩
    | trans a b c _ _ ih1 ih2 =>
      obtain ⟨g, hg⟩ := ih1; obtain ⟨k, hk⟩ := ih2; exact ⟨g * k, by rw [hk, hg]; group⟩
  · rintro ⟨g, hg⟩
    exact Quot.sound ⟨g, by simpa using hg⟩

theorem exists_section : ∃ S : Set (Pl E), IsSection S := by
  refine ⟨{u | u = @Classical.epsilon _ ⟨u⟩ fun u' : Pl E => u'.under (𝓞 (maximalRealSubfield E)) =
      u.under (𝓞 (maximalRealSubfield E))}, fun w => ?_⟩
  haveI : Nonempty (Pl E) := ⟨w⟩
  have hspec := Classical.epsilon_spec (p := fun u' : Pl E => u'.under (𝓞 (maximalRealSubfield E)) =
      w.under (𝓞 (maximalRealSubfield E))) ⟨w, rfl⟩
  refine ⟨_, ⟨?_, hspec⟩, ?_⟩
  · show _ = _
    simp only [hspec]
  · rintro u ⟨hu, hu'⟩
    rw [Set.mem_setOf_eq] at hu
    rw [hu]
    simp only [hu']

theorem ell_mul {n : ℕ} (p₁ p₂ : E[X]) (h1 : p₁ ∈ Ell E p₁.natDegree) (h2 : p₂ ∈ Ell E p₂.natDegree)
    (hc : IsCoprime p₁ p₂) (hn : p₁.natDegree + p₂.natDegree = n) : p₁ * p₂ ∈ Ell E n := by
  obtain ⟨m1, -, s1, r1⟩ := h1
  obtain ⟨m2, -, s2, r2⟩ := h2
  refine ⟨m1.mul m2, by rw [m1.natDegree_mul m2, hn], s1.mul s2 hc, fun τ z hz => ?_⟩
  rw [Polynomial.map_mul, Polynomial.roots_mul] at hz
  · rcases Multiset.mem_add.1 hz with h | h
    · exact r1 τ z h
    · exact r2 τ z h
  · rw [← Polynomial.map_mul]
    exact ((m1.mul m2).map τ).ne_zero

end GlobalTheory.UnitOrbCount

namespace GlobalTheory.UnitOrbCount

end GlobalTheory.UnitOrbCount
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitalSignAlmostEverywhere
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.G2
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.KapOrbAE

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_integral_unitary (hE : Unr E) (n : ℕ) (P : E[X]) (hP : P ∈ Ell E n) :
    ∀ᶠ w : Pl E in cofinite, ¬ IsSplitAt w → ∃ γ : UL n w, γ ∈ KL n w ∧ γ.1.val.charpoly = atPl w P := by
  obtain ⟨M, G, hMP, hG, hGh, hMG⟩ := GlobalTheory.EllHermGlobal.exists_charpoly_herm E n P hP
  have h1 : ∀ᶠ w : Pl E in cofinite, ∀ i j,
      algebraMap E (w.adicCompletion E) (M i j) ∈ w.adicCompletionIntegers E :=
    eventually_all.2 fun i => eventually_all.2 fun j => GlobalTheory.ExInertUnit.eventually_mem_integers _
  have h2 : ∀ᶠ w : Pl E in cofinite, ∀ i j,
      algebraMap E (w.adicCompletion E) (G i j) ∈ w.adicCompletionIntegers E :=
    eventually_all.2 fun i => eventually_all.2 fun j => GlobalTheory.ExInertUnit.eventually_mem_integers _
  have h3 : ∀ᶠ w : Pl E in cofinite, ∀ i j,
      algebraMap E (w.adicCompletion E) (G⁻¹ i j) ∈ w.adicCompletionIntegers E :=
    eventually_all.2 fun i => eventually_all.2 fun j => GlobalTheory.ExInertUnit.eventually_mem_integers _
  filter_upwards [h1, h2, h3] with w hw1 hw2 hw3 hw
  obtain ⟨γ, hγ, hc⟩ := GlobalTheory.ExInertUnit.local_step hE w hw M G hG hGh hMG hw1 hw2 hw3
  exact ⟨γ, hγ, by rw [hc, hMP]⟩


open GlobalTheory.UnitOrbCount in
theorem kapOrb_unit_pos (hU : Unr E) (n : ℕ) (hn : 1 ≤ n) (p₁ p₂ : E[X]) (h1 : p₁ ∈ Ell E p₁.natDegree)
    (h2 : p₂ ∈ Ell E p₂.natDegree) (hc : IsCoprime p₁ p₂) (hd : p₁.natDegree + p₂.natDegree = n) :
    ∀ᶠ w : Pl E in cofinite, kapOrb n w (atPl w p₁) (atPl w p₂) ((KL n w : Set (UL n w)).indicator 1) = 1 := by
  have hP := ell_mul p₁ p₂ h1 h2 hc hd
  obtain ⟨S, hS⟩ := exists_section (E := E)
  filter_upwards [GlobalTheory.BCT.OrbUnit.orbUnit_ae E hU n hn S hS _ hP, GlobalTheory.T.eventually_exists_integral_charpoly_split_place E hU n hn _ hP,
    exists_integral_unitary hU n _ hP, GlobalTheory.T.eventually_unitary_conj_of_same_elliptic_charpoly_inert E hU n hn _ hP] with w hA hE1 hE2 hU2
  have hmap : atPl w (p₁ * p₂) = atPl w p₁ * atPl w p₂ := Polynomial.map_mul _
  rw [hmap] at hA hE1 hE2 hU2
  obtain ⟨γ₀, hγ₀K, hγ₀P⟩ : ∃ γ : UL n w, γ ∈ KL n w ∧ γ.1.val.charpoly = atPl w p₁ * atPl w p₂ := by
    by_cases hs : IsSplitAt w
    · exact hE1 hs
    · exact hE2 hs
  have huniq : ∀ γ γ' : UL n w, γ ∈ KL n w → γ' ∈ KL n w → γ.1.val.charpoly = atPl w p₁ * atPl w p₂ →
      γ'.1.val.charpoly = atPl w p₁ * atPl w p₂ → ∃ g : UL n w, γ' = g⁻¹ * γ * g := by
    intro γ γ' hk hk' hp hp'
    by_cases hs : IsSplitAt w
    · have := GlobalTheory.T.exists_conj_same_separable_charpoly_split_place E n _ hP w hs γ γ'
      rw [hmap] at this
      exact this hp hp'
    · exact hU2 hs γ γ' hk hk' hp hp'
  have key : ∀ γ : UL n w, γ.1.val.charpoly = atPl w p₁ * atPl w p₂ →
      ((∃ g : UL n w, g⁻¹ * γ * g ∈ KL n w) ↔ (Quot.mk _ γ : TwCl (MonoidHom.id (UL n w))) = Quot.mk _ γ₀) := by
    intro γ hp
    rw [mk_eq_iff]
    constructor
    · rintro ⟨g, hg⟩
      obtain ⟨k, hk⟩ := huniq _ γ₀ hg hγ₀K (by rw [cp_conj, hp]) hγ₀P
      exact ⟨g * k, by rw [hk]; group⟩
    · rintro ⟨g, hg⟩
      exact ⟨g, hg ▸ hγ₀K⟩
  unfold kapOrb clSum
  simp only [Set.mem_setOf_eq]
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : TwCl (MonoidHom.id (UL n w)), Quot.mk _ γ₀ = c₀ := ⟨_, rfl⟩
  rw [hc₀] at key
  rw [finsum_eq_single _ c₀]
  · have hc : (Quot.mk _ c₀.rep : TwCl (MonoidHom.id (UL n w))) = Quot.mk _ γ₀ := by
      rw [hc₀]; exact Quot.out_eq _
    obtain ⟨g, hg⟩ := (mk_eq_iff _ _).1 hc
    have hp : c₀.rep.1.val.charpoly = atPl w p₁ * atPl w p₂ := by
      rw [← hγ₀P, hg, cp_conj]
    have hex : ∃ g : UL n w, g⁻¹ * c₀.rep * g ∈ KL n w :=
      ⟨g, hg ▸ hγ₀K⟩
    obtain ⟨hT, -, hQ⟩ := hA _ hp
    rw [if_pos hp, hT, if_pos hex, hQ (atPl w p₁) (dvd_mul_right _ _) hex, mul_one]
  · intro c hne
    have hc : (Quot.mk _ c.rep : TwCl (MonoidHom.id (UL n w))) = c := Quot.out_eq c
    by_cases hp : c.rep.1.val.charpoly = atPl w p₁ * atPl w p₂
    · obtain ⟨hT, -, -⟩ := hA c.rep hp
      rw [if_pos hp, hT, if_neg, mul_zero]
      intro hex
      apply hne
      rw [← hc]
      exact (key _ hp).1 hex
    · rw [if_neg hp]

instance subsingleton_units_rank_zero (w : Pl E) : Subsingleton (UL 0 w) := by
  refine ⟨fun a b => Subtype.ext (Units.ext ?_)⟩
  exact Subsingleton.elim _ _

theorem kapSign_zero (w : Pl E) (Q : (w.adicCompletion E)[X]) (γ : GLw 0 w) : kapSign 0 w Q γ = 1 := by
  unfold kapSign
  split_ifs with hs
  · rfl
  · simp only
    have hsub : Subsingleton (LinearMap.ker (Matrix.toLin' (aeval γ.val Q))) := by
      refine ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
    haveI : IsEmpty (Fin (Module.finrank (w.adicCompletion E) (LinearMap.ker (Matrix.toLin' (aeval γ.val Q))))) := by
      rw [Module.finrank_zero_of_subsingleton]
      infer_instance
    rw [Matrix.det_isEmpty]
    simp [ordL]
    exact zpow_zero _

theorem kapOrb_unit_zero (w : Pl E) (Q₁ Q₂ : (w.adicCompletion E)[X]) (hQ : Q₁ * Q₂ = 1) :
    kapOrb 0 w Q₁ Q₂ ((KL 0 w : Set (UL 0 w)).indicator 1) = 1 := by
  haveI : Subsingleton (TwCl (MonoidHom.id (UL 0 w))) := by
    refine ⟨fun a b => ?_⟩
    induction a using Quot.ind with | _ x => ?_
    induction b using Quot.ind with | _ y => ?_
    rw [Subsingleton.elim x y]
  haveI : Unique (TwCl (MonoidHom.id (UL 0 w))) := ⟨⟨Quot.mk _ 1⟩, fun _ => Subsingleton.elim _ _⟩
  unfold kapOrb clSum
  rw [finsum_unique]
  set γ : UL 0 w := (default : TwCl (MonoidHom.id (UL 0 w))).rep
  have hcp : γ.1.val.charpoly = Q₁ * Q₂ := by
    rw [hQ]
    rw [Matrix.charpoly, Matrix.det_isEmpty]
  have hγ : γ ∈ KL 0 w := by
    rw [Subsingleton.elim γ 1]
    exact one_mem _
  have hT : twOrb (MonoidHom.id _) (KL 0 w) γ ((KL 0 w : Set (UL 0 w)).indicator 1) = 1 := by
    rw [GlobalTheory.BCT.OrbUnit.twOrb_unit (KL 0 w) γ, if_pos ⟨1, by simpa using hγ⟩]
    · intro g₁ g₂ _ _
      exact ⟨1, one_mem _, 1, one_mem _, Subsingleton.elim _ _⟩
    · intro g _ x _
      rw [Subsingleton.elim x 1]
      exact one_mem _
  have hcp' : γ ∈ {γ : UL 0 w | γ.1.val.charpoly = Q₁ * Q₂} := hcp
  rw [if_pos hcp', hT, mul_one]
  exact kapSign_zero w Q₁ γ.1

end GlobalTheory.CompanionTheory.KapOrbAE

theorem GlobalTheory.CompanionTheory.KapOrbAE.kapOrbAE : KapOrbAE := by
  intro E _ _ _ hU n K' f hf p₁ p₂ h1 h2 hc hd
  have hunit : ∀ᶠ w : Pl E in cofinite,
      kapOrb n w (atPl w p₁) (atPl w p₂) ((KL n w : Set (UL n w)).indicator 1) = 1 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have d1 : p₁.natDegree = 0 := by omega
      have d2 : p₂.natDegree = 0 := by omega
      have e1 : p₁ = 1 := h1.1.natDegree_eq_zero.1 d1
      have e2 : p₂ = 1 := h2.1.natDegree_eq_zero.1 d2
      refine Eventually.of_forall fun w => GlobalTheory.CompanionTheory.KapOrbAE.kapOrb_unit_zero w _ _ ?_
      simp [e1, e2]
    · exact GlobalTheory.CompanionTheory.KapOrbAE.kapOrb_unit_pos hU n hn p₁ p₂ h1 h2 hc hd
  have hall : ∀ᶠ w : Pl E in cofinite, kapOrb n w (atPl w p₁) (atPl w p₂) (f w) = 1 := by
    filter_upwards [hf.2, hunit] with w hw h
    rw [hw]
    exact h
  exact Filter.eventually_cofinite.1 hall
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitalSignAlmostEverywhereStatement
open NumberField IsDedekindDomain Polynomial GlobalTheory.BCT PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.G2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbital_sign_almost_everywhere : KapOrbAE := by
  first | exact @GlobalTheory.CompanionTheory.KapOrbAE.kapOrbAE | exact GlobalTheory.CompanionTheory.KapOrbAE.kapOrbAE | (intros; apply GlobalTheory.CompanionTheory.KapOrbAE.kapOrbAE <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterWeightMap
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterWeightMap
open NumberField IsDedekindDomain Polynomial GlobalTheory.BCT PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.G2

namespace GlobalTheory.CompanionTheory.CharInf

theorem chWMap : ChWMap := by
  intro E _ _ n lam P
  rfl

end GlobalTheory.CompanionTheory.CharInf
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterWeightMapStatement
open NumberField IsDedekindDomain Polynomial GlobalTheory.BCT PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.G2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_weight_map : ChWMap := by
  first | exact @GlobalTheory.CompanionTheory.CharInf.chWMap | exact GlobalTheory.CompanionTheory.CharInf.chWMap | (intros; apply GlobalTheory.CompanionTheory.CharInf.chWMap <;> assumption)
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.HyperbolicEntryBounds.ChainPlug
section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.HyperbolicEntryBounds.InfinitesimalWeightZero
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace PositivityTheory.Rg.BcB.F.F0

open PositivityTheory.Rg.BcB.F

attribute [local instance] borelG borelF borelA

theorem haarGA_ex (E : Type) [Field E] [NumberField E] (a : ℕ) : ∃ μ : Measure (GA E a), μ.IsHaarMeasure := by
  open scoped GlobalTheory.CuspRep.CuspidalL2GL in
  haveI : BorelSpace (GA E a) := ⟨rfl⟩
  exact ⟨Measure.haar, inferInstance⟩

theorem haarG_ex (a : ℕ) : ∃ ν : Measure (G a), ν.IsHaarMeasure := by
  haveI : BorelSpace (G a) := ⟨rfl⟩
  haveI : LocallyCompactSpace (Matrix (Fin a) (Fin a) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin a → Fin a → ℂ))
  haveI : LocallyCompactSpace (Matrix (Fin a) (Fin a) ℂ)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : LocallyCompactSpace (G a) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  exact ⟨Measure.haar, inferInstance⟩

def dw0 (N : ℕ) : DomWeight N := ⟨fun _ => 0, fun _ _ _ => le_rfl⟩

theorem infinitesimal_weight_zero (n : ℕ) : infOfWeight (dw0 (n - n)) = 0 := by
  haveI : IsEmpty (Fin (n - n)) := by rw [Nat.sub_self]; infer_instance
  simp [infOfWeight]

theorem chainEx_of (h2 : G8.GlobalComplexCoefficients) (h3 : G8.G3) (h4 : G8.G4) : ChainEx := by
  intro E _ _ _ hE n hn μ e hμ lam
  obtain ⟨ι, hι, a, l₁, l₂, sg, hsg, hgeo⟩ := h2 E hE n hn μ e hμ lam
  choose μG hG using haarGA_ex E
  choose νC hC using haarG_ex
  have c4 : ∀ a b : ℕ, ∃ c : ℂ, c ≠ 0 ∧ _ := fun a b =>
    @h4 E _ _ _ hE a b _ ⟨rfl⟩ _ ⟨rfl⟩ _ ⟨rfl⟩ _ ⟨rfl⟩ (μG a) (hG a) (μG b) (hG b) (νC a) (hC a) (νC b) (hC b)
  choose c hc0 hc using c4
  let K : ℕ := n * Fintype.card (InfinitePlace E)
  refine ⟨{
    ι := Option ι
    a := fun o => o.elim n a
    l₁ := fun o => match o with | none => lam | some i => l₁ i
    l₂ := fun o => match o with | none => fun _ => dw0 (n - n) | some i => l₂ i
    le := fun o => match o with | none => le_rfl | some i => (hsg i).2.1
    inf := fun o v => match o with
      | none => by simp [infinitesimal_weight_zero]
      | some i => (hsg i).2.2 v
    μG := μG
    hG := hG
    νC := νC
    hC := hC
    c := fun o => match o with | none => 0 | some i => sg i / (c (a i) (n - a i) * 2 ^ K)
    eq := ?_ }⟩
  intro S hS K' f hK' hf u₁ u₂ hu φ₁ φ₂ hφ hreg val ψ hlef z hz
  rw [Fintype.sum_option]
  simp only [zero_mul, zero_add]
  have hstep : ∀ i : ι, sg i / (c (a i) (n - a i) * 2 ^ K) *
      ellSum2 (μG (a i)) (μG (n - a i)) (adel S (u₁ (a i)) (u₂ (a i)) (ψ (some i)) (φ₁ (a i)) (φ₂ (a i))) =
      z * (sg i * geomSt2 S (l₁ i) (l₂ i) (seen (φ₁ (a i)) (φ₂ (a i)))) := by
    intro i
    have hai := (hsg i).2.1
    obtain ⟨t₁, t₂, t₃, -⟩ := hφ (a i) hai
    rw [hc (a i) (n - a i) S hS (u₁ (a i)) (u₂ (a i)) (hu (a i)).1 (hu (a i)).2 (l₁ i) (l₂ i) (val (some i))
      (ψ (some i)) (φ₁ (a i)) (φ₂ (a i)) (hlef (some i)) t₁ t₂, hz (some i),
      h3 E hE (a i) (n - a i) S hS (l₁ i) (l₂ i) _ t₃ (hreg (some i))]
    have hK : (a i + (n - a i)) * Fintype.card (InfinitePlace E) = K := by
      simp only [K, Nat.add_sub_of_le hai]
    rw [hK]
    have h2K : (2 : ℂ) ^ K ≠ 0 := pow_ne_zero _ two_ne_zero
    have hc' := hc0 (a i) (n - a i)
    field_simp
  calc z * geomU S lam f = ∑ i, z * (sg i * geomSt2 S (l₁ i) (l₂ i) (seen (φ₁ (a i)) (φ₂ (a i)))) := by
        rw [← Finset.mul_sum]
        exact congrArg (z * ·) (hgeo S hS K' f (fun a' => seen (φ₁ a') (φ₂ a')) hK' hf fun a' ha' =>
          ⟨(hφ a' ha').2.2.1, (hφ a' ha').2.2.2⟩)
    _ = _ := Finset.sum_congr rfl fun i _ => (hstep i).symm

end PositivityTheory.Rg.BcB.F.F0

end
end

namespace PositivityTheory.Rg.BcB.F.F0

theorem complex_coefficient_multiplicity_holds : PositivityTheory.Rg.BcB.G8.GlobalComplexCoefficients := GlobalTheory.T.globalComplexCoefficients_of_local_orbit_character GlobalTheory.T.elliptic_local_identity GlobalTheory.T.orbital_sign_almost_everywhere GlobalTheory.T.character_weight_map

theorem chain_existence_of_global_character (h4 : PositivityTheory.Rg.BcB.G8.G4) : PositivityTheory.Rg.BcB.F.ChainEx :=
  chainEx_of complex_coefficient_multiplicity_holds PositivityTheory.Rg.BcB.G3.g3 h4

end PositivityTheory.Rg.BcB.F.F0
end

namespace PositivityTheory.Rg.BcB.F.F0

theorem chainEx_holds : PositivityTheory.Rg.BcB.F.ChainEx := chain_existence_of_global_character PositivityTheory.Rg.BcB.G8.global_character_holds

end PositivityTheory.Rg.BcB.F.F0
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.HyperbolicEntryBounds.WExFinal
section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.MemLeafListOfAllLeaves
noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcN.F2

set_option synthInstance.maxHeartbeats 200000

namespace PositivityTheory.Rg.BcB.F.Tail

section Leaves

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem mem_leafList_of_allLeaves {P : ∀ M : ℕ, Submodule ℂ (Sm E M) → Prop} :
    ∀ {N : ℕ} (t : Tr E N), t.AllLeaves P → ∀ x ∈ t.leafList, P x.1 x.2
  | _, .leaf V z, h, x, hx => by
    simp only [Tr.leafList, List.mem_singleton] at hx
    subst hx
    exact h
  | _, .node t₁ t₂, h, x, hx => by
    simp only [Tr.leafList, List.mem_append] at hx
    rcases hx with hx | hx
    · exact mem_leafList_of_allLeaves t₁ h.1 x hx
    · exact mem_leafList_of_allLeaves t₂ h.2 x hx

theorem mem_parts_of_treeParts {N : ℕ} {t : Tr E N} {P : Pre E N} {Q : ∀ M : ℕ, Submodule ℂ (Sm E M) → Prop}
    (ht : TreeParts t P) (hl : t.AllLeaves Q) : ∀ x ∈ parts P, 0 < x.1 ∧ Q x.1 x.2 := by
  intro x hx
  have hx' : x ∈ t.leafList.filter fun y => 0 < y.1 := by
    rw [← ht]
    exact hx
  rw [List.mem_filter] at hx'
  exact ⟨by simpa using hx'.2, mem_leafList_of_allLeaves t hl x hx'.1⟩

end Leaves

section Twist

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def mulK (N : ℕ) (χ : HChar E) : (Kinf E N → ℂ) →ₗ[ℂ] (Kinf E N → ℂ) where
  toFun f k := (chiDet N χ (infGL E N (Unitary.toUnits k)) : ℂ) * f k
  map_add' f g := by
    funext k
    simp only [Pi.add_apply, mul_add]
  map_smul' c f := by
    funext k
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem hasKType_twist {N : ℕ} (χ : HChar E) {K' : Subgroup (GL (Fin N) (Af E))} {W' : Submodule ℂ (Kinf E N → ℂ)}
    {V : Submodule ℂ (Sm E N)} (h : HasType K' W' V) :
    HasKType (W'.map (mulK N χ)) (V.map (mulChi N χ).toLinearMap) := by
  obtain ⟨φ, hφV, hφ0, -, hT⟩ := h
  refine ⟨mulChi N χ φ, Submodule.mem_map_of_mem hφV, ?_, fun g => ?_⟩
  · exact (LinearEquiv.map_ne_zero_iff (mulChi N χ)).2 hφ0
  · have e : (fun k : Kinf E N => ((mulChi N χ φ : Sm E N) : GA E N → ℂ) (g * infGL E N (Unitary.toUnits k))) =
        (chiDet N χ g : ℂ) • mulK N χ (fun k : Kinf E N => (φ : GA E N → ℂ) (g * infGL E N (Unitary.toUnits k))) := by
      funext k
      simp only [mulChi_apply, map_mul, Units.val_mul, Pi.smul_apply, smul_eq_mul, mulK, LinearMap.coe_mk,
        AddHom.coe_mk]
      ring
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.mem_map_of_mem (hT g))

theorem HasKType.mono {N : ℕ} {W₁ W₂ : Submodule ℂ (Kinf E N → ℂ)} {V : Submodule ℂ (Sm E N)} (h : W₁ ≤ W₂)
    (hV : HasKType W₁ V) : HasKType W₂ V := by
  obtain ⟨φ, hφ, h0, hW⟩ := hV
  exact ⟨φ, hφ, h0, fun g => h (hW g)⟩

end Twist

theorem joinType : JoinType := by
  intro E _ _ _ n μ Ω hΩ
  have : ∀ M, Finite (Ω M) := fun M => (hΩ M).1.to_subtype
  let W : ∀ N : ℕ, Submodule ℂ (Kinf E N → ℂ) := fun N =>
    ⨆ p : Ω N × Fin (n + 1), (p.1 : Submodule ℂ (Kinf E N → ℂ)).map (mulK N (μ ^ (p.2 : ℕ)))
  have hle : ∀ (N k : ℕ) (W' : Submodule ℂ (Kinf E N → ℂ)), W' ∈ Ω N → k ≤ n → W'.map (mulK N (μ ^ k)) ≤ W N :=
    fun N k W' hW' hk => le_iSup (fun p : Ω N × Fin (n + 1) => (p.1 : Submodule ℂ (Kinf E N → ℂ)).map
      (mulK N (μ ^ (p.2 : ℕ)))) (⟨W', hW'⟩, ⟨k, Nat.lt_succ_of_le hk⟩)
  refine ⟨W, fun N => ?_, ?_⟩
  · have : ∀ p : Ω N × Fin (n + 1), FiniteDimensional ℂ
        ((p.1 : Submodule ℂ (Kinf E N → ℂ)).map (mulK N (μ ^ (p.2 : ℕ)))) := fun p => by
      have := (hΩ N).2 _ p.1.2
      infer_instance
    infer_instance
  intro a b hab s₁ s₂ Pa Pb D hc h₁ h₂ i
  have key : ∀ (k : ℕ), k ≤ n → ∀ x : Σ M : ℕ, Submodule ℂ (Sm E M),
      (0 < x.1 ∧ (x.1 = 0 ∨ ∃ K', ∃ W' ∈ Ω x.1, HasType K' W' x.2)) →
      HasKType (W (twPart (μ ^ k) x).1) (twPart (μ ^ k) x).2 := by
    rintro k hk ⟨M, V⟩ ⟨hM, h0 | ⟨K', W', hW', hT⟩⟩
    · exact absurd h0 (Nat.pos_iff_ne_zero.1 hM)
    · exact HasKType.mono (hle M k W' hW' hk) (hasKType_twist (μ ^ k) hT)
  have hmem : (⟨D.N i, D.V i⟩ : Σ M : ℕ, Submodule ℂ (Sm E M)) ∈ parts D :=
    List.mem_ofFn.2 ⟨i, rfl⟩
  have hj := hc.join
  unfold IsJoin at hj
  rw [hj, List.mem_append, List.mem_map, List.mem_map] at hmem
  rcases hmem with ⟨x, hx, e⟩ | ⟨x, hx, e⟩
  · have := key b (by omega) x (mem_parts_of_treeParts hc.t₁ h₁ x hx)
    rw [e] at this
    exact this
  · have := key a (by omega) x (mem_parts_of_treeParts hc.t₂ h₂ x hx)
    rw [e] at this
    exact this

end PositivityTheory.Rg.BcB.F.Tail

end
end

namespace PositivityTheory.Rg.BcB.F.F0

theorem wEx_holds : WEx := wEx_of PositivityTheory.Rg.BcB.F.Tail.joinType

end PositivityTheory.Rg.BcB.F.F0
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.SplitMuMatching
theorem PositivityTheory.HtPt.Bc.SplitMuMatching.matchCtMuSplit : type_of% @GlobalTheory.BCT.SplitCtMatch.match_ctMu_of_isSplitAt := @GlobalTheory.BCT.SplitCtMatch.match_ctMu_of_isSplitAt
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameEx0Of
section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalExistenceOfUnramified
noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.Bc.ArchbcB.B
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Ex0

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

structure Loc0 (π : Submodule ℂ (UA E n → ℂ)) (S : Finset (Pl E)) (μ : HChar E) (Sec : Set (Pl E)) (d₀ : LocData E n) : Prop where
  hSec : IsSection Sec
  inert : ∀ w, ¬ IsSplitAt w → w ∈ Sec
  ok₀ : d₀.Ok
  T₀ : d₀.T = ∅
  μloc : ∀ w, d₀.μ w = μ.loc w
  unif : ∀ w, IsUnifAt (d₀.ϖ w) ∧ IsUnifV E w (d₀.ϖ w : w.adicCompletion E)
  S₀ : ∀ w ∈ d₀.S₀, w ∈ Sec ∧ IsSplitAt w
  S_le : ∀ w ∈ S, IsSplitAt w → w ∈ d₀.S₀
  bad : ∀ w ∈ d₀.Bad, w ∈ Sec ∧ (¬ IsSplitAt w → ¬ IsUnramU π w)
  good : ∀ w ∈ Sec, w ∉ d₀.S₀ → w ∉ d₀.Bad → IsUnramU π w ∧ μ.UnrAt w
  levFam : IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) d₀.KU
  level : ∀ K' : ∀ w : Pl E, Subgroup (UL n w), (∀ w, K' w ≤ d₀.KU w) → HasLevel Sec π K'
  fix : ∀ a ≤ n, ∀ w ∈ d₀.Bad, Match n a (n - a) w (μ.loc w) (U.lone (d₀.KB w)) (d₀.fix a w)
  mok₀ : MLM.MOk d₀
  off : ∀ w, w ∉ d₀.Bad → d₀.KB w = KL n w ∧ ∀ a, d₀.fix a w = 0

theorem isLevel_KL (w : Pl E) {K : Subgroup (UL n w)} (h : GlobalTheory.BCT.IsLevel (MonoidHom.id _) (KL n w) K) :
    GlobalTheory.BCT.IsLevel (MonoidHom.id _) (KL n w) (KL n w) :=
  ⟨Subgroup.isOpen_mono h.2.1 h.1, le_rfl, fun _ hk => hk⟩

theorem local_existence_of_unramified (hSec : SecEx) (hU : UnifEx) (hLev : LevelEx) (hS : SplitEx) (hB : BadEx2) (hE : GlobalTheory.BCT.Unr E)
    (π : Submodule ℂ (UA E n → ℂ)) (hπ : IsAutRepU π) (hun : ∀ᶠ w : Pl E in cofinite, IsUnramU π w) (S : Finset (Pl E))
    (hS1 : S.card ≤ 1) (μ : HChar E) (hin : ∀ w : Pl E, ¬ IsSplitAt w → μ.UnrAt w) (hae : ∀ᶠ w : Pl E in cofinite, μ.UnrAt w)
    (hop : ∀ w : Pl E, IsOpen ((μ.loc w).ker : Set (w.adicCompletion E)ˣ)) : ∃ Sec d₀, Loc0 π S μ Sec d₀ := by
  set S₀ := S.filter IsSplitAt with hS₀
  obtain ⟨Sec, hsec, hS₀S, hinS⟩ := hSec E S₀ ((Finset.card_filter_le _ _).trans hS1)
  have hfin : {w : Pl E | ¬ (IsUnramU π w ∧ μ.UnrAt w)}.Finite := Filter.eventually_cofinite.1 (hun.and hae)
  set Bad := (hfin.toFinset.filter (· ∈ Sec)) \ S₀ with hBad
  have memBad : ∀ w, w ∈ Bad ↔ (¬ (IsUnramU π w ∧ μ.UnrAt w) ∧ w ∈ Sec) ∧ w ∉ S₀ := fun w => by
    simp only [hBad, Finset.mem_sdiff, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  obtain ⟨K₀, m, -, hm, hfam, hgood, hcong, hlev⟩ := hLev E n π hπ Sec hsec (S₀ ∪ Bad) 1
  choose ϖ hϖ using hU E hE
  have h1 : ∀ w : Pl E, ∃ (K' : Subgroup (GLw n w)) (X : Finset (GLw n w)) (e : GLw n w → ℂ)
      (L : ∀ a : ℕ, Subgroup (GLw a w × GLw (n - a) w)), w ∈ S₀ →
      K'.subgroupOf (UL n w) = K₀ w ∧ IsOpen (K' : Set (GLw n w)) ∧ K' ≤ KGL w (n := n) ∧
      (∀ k ∈ KGL w (n := n), ∀ k' ∈ K', k * k' * k⁻¹ ∈ K') ∧ (∀ x ∈ X, x ∈ KGL w (n := n)) ∧ (∀ k ∈ KGL w (n := n), ∃! x ∈ X, x⁻¹ * k ∈ K') ∧
      IsHk K' e ∧ ∀ a (ha : a ≤ n), IsPairLevel (L a) ∧ ∀ y ∈ L a, y ∈ leviOf (Nat.add_sub_of_le ha) w K' ∧
        μ.loc w (GeneralLinearGroup.det y.1 ^ (n - a) * GeneralLinearGroup.det y.2 ^ a) = 1 := fun w => by
    by_cases hw : w ∈ S₀
    · obtain ⟨K', X, e, L, h⟩ := hS E n w (Finset.mem_filter.1 hw).2 (μ.loc w) (hop w) m hm (K₀ w)
        (hcong w (Or.inr (Finset.mem_union_left _ hw)))
      exact ⟨K', X, e, L, fun _ => h⟩
    · exact ⟨⊥, ∅, 0, fun _ => ⊥, fun h => absurd h hw⟩
  choose K' X e LS hSp using h1
  let fx : ∀ (a : ℕ) (w : Pl E), LF a (n - a) w := fun a w => fixFn n a w (μ.loc w) m (K₀ w)
  have h2 : ∀ (a : ℕ) (w : Pl E), ∃ L : Subgroup (GLw a w × GLw (n - a) w), a ≤ n → w ∈ Bad →
      IsPairLevel L ∧ IsHecke L (fx a w) ∧ Match n a (n - a) w (μ.loc w) (U.lone (K₀ w)) (fx a w) := fun a w => by
    by_cases hw : a ≤ n ∧ w ∈ Bad
    · obtain ⟨L, h⟩ := hB E hE n a hw.1 w (μ.loc w) (hop w) m hm (K₀ w) (hcong w (Or.inr (Finset.mem_union_right _ hw.2)))
      exact ⟨L, fun _ _ => h⟩
    · exact ⟨⊥, fun h h' => absurd ⟨h, h'⟩ hw⟩
  choose LB hBd using h2
  let d : LocData E n := ⟨∅, S₀, Bad, fun w => μ.loc w, ϖ, 0, K', X, e, fun a w => if w ∈ S₀ then LS w a else LB a w,
    fun a w => if w ∈ Bad then fx a w else 0, fun _ => 1, fun w => if w ∈ Bad then K₀ w else KL n w⟩
  have dK : ∀ w ∈ Bad, d.KB w = K₀ w := fun w hw => if_pos hw
  have dF : ∀ a, ∀ w ∈ Bad, d.fix a w = fx a w := fun a w hw => if_pos hw
  have hKU : ∀ w, d.KU w = if w ∈ S₀ ∪ Bad then K₀ w else KL n w := fun w => by
    show (if w ∈ (∅ : Finset (Pl E)) then _ else if w ∈ S₀ then (K' w).subgroupOf (UL n w) else if w ∈ Bad then (if w ∈ Bad then K₀ w else KL n w) else KL n w) = _
    by_cases a1 : w ∈ S₀
    · simp [a1, (hSp w a1).1]
    · by_cases a2 : w ∈ Bad <;> simp [a1, a2]
  have hgd : ∀ w ∈ Sec, w ∉ S₀ → w ∉ Bad → IsUnramU π w ∧ μ.UnrAt w := fun w a1 a2 a3 => by
    by_contra h
    exact a3 ((memBad w).2 ⟨⟨h, a1⟩, a2⟩)
  refine ⟨Sec, d, hsec, hinS, ⟨⟨Finset.disjoint_empty_left _, Finset.disjoint_empty_left _, Finset.disjoint_sdiff⟩,
    fun w => (hϖ w).1.1, fun w hw => absurd hw (Finset.notMem_empty w), fun w hw => ?_, fun a ha w hw => ?_,
    fun a ha w hw y hy => ?_, fun a ha w hw => ?_⟩, rfl, fun _ => rfl, hϖ,
    fun w hw => ⟨hS₀S w hw, (Finset.mem_filter.1 hw).2⟩, fun w hw hs => Finset.mem_filter.2 ⟨hw, hs⟩,
    fun w hw => ⟨((memBad w).1 hw).1.2, fun hs hu => ((memBad w).1 hw).1.1 ⟨hu, hin w hs⟩⟩, hgd, ⟨fun w => ?_, ?_⟩,
    fun K'' hK'' => ?_, fun a ha w hw => by rw [dK w hw, dF a w hw]; exact (hBd a w ha hw).2.2,
    ⟨fun w hw => absurd hw (Finset.notMem_empty w), fun w hw => ?_, fun w hw hs => ⟨by rw [dK w hw]; exact hfam.1 w, fun a ha => ?_⟩,
      fun w hw hs => ⟨m, hm, by rw [dK w hw]; exact hfam.1 w, fun γ => ?_, fun a ha => ?_⟩⟩,
    fun w hw => ⟨if_neg hw, fun a => if_neg hw⟩⟩
  · obtain ⟨-, b1, b2, b3, b4, b5, b6, -⟩ := hSp w hw
    exact ⟨b1, b2, b3, b4, b5, b6⟩
  · show IsPairLevel (if w ∈ S₀ then LS w a else LB a w)
    by_cases a1 : w ∈ S₀
    · rw [if_pos a1]; exact ((hSp w a1).2.2.2.2.2.2.2 a ha).1
    · rw [if_neg a1]; exact (hBd a w ha ((Finset.mem_union.1 hw).resolve_left a1)).1
  · have hy' : y ∈ (if w ∈ S₀ then LS w a else LB a w) := hy
    rw [if_pos (show w ∈ S₀ from hw)] at hy'
    exact ((hSp w hw).2.2.2.2.2.2.2 a ha).2 y hy'
  · rw [dF a w hw]
    show IsHecke (if w ∈ S₀ then LS w a else LB a w) (fx a w)
    rw [if_neg ((memBad w).1 hw).2]
    exact (hBd a w ha hw).2.1
  · rw [hKU]
    split_ifs
    · exact hfam.1 w
    · exact isLevel_KL w (hfam.1 w)
  · filter_upwards [(S₀ ∪ Bad).eventually_cofinite_notMem] with w hw
    rw [hKU, if_neg hw]
  · obtain ⟨φ, a1, a2, a3⟩ := hlev (fun w => if w ∈ Sec then K'' w else K₀ w) fun w => by
      split_ifs with hw
      · refine (hK'' w).trans ?_
        rw [hKU]
        split_ifs with hR
        · exact le_rfl
        · rw [Finset.mem_union, not_or] at hR
          rw [hgood w (hgd w hw hR.1 hR.2).1 (by rw [Finset.mem_union, not_or]; exact hR)]
      · exact le_rfl
    exact ⟨φ, a1, a2, fun w hw x hx hk => a3 w hw x hx (by simpa only [if_pos hw] using hk)⟩
  · have hs : IsSplitAt w := (Finset.mem_filter.1 hw).2
    refine ⟨hs, fun g => by simp [UL, hs], ?_⟩
    show GlobalTheory.BCT.IsLevel _ _ ((K' w).subgroupOf (UL n w))
    rw [(hSp w hw).1]
    exact hfam.1 w
  · rw [dF a w hw, dK w hw]
    show fixFn n a w (μ.loc w) m (K₀ w) = _
    rw [fixFn, dite_eq_left ha, if_pos hs]
  · rw [dK w hw]
    exact hcong w (Or.inr (Finset.mem_union_right _ hw)) γ
  · rw [dF a w hw, dK w hw]
    show fixFn n a w (μ.loc w) m (K₀ w) = _
    rw [fixFn, dite_eq_left ha, if_neg hs]

end PositivityTheory.Rg.BcB.F.Ex0

end
end

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.F.Ex0
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.Ex0

set_option maxHeartbeats 1000000 in
theorem frameEx0_of (hW : WeightEx) (hun : Rig.UnrAE) (hMu : MuEx) (hSec : SecEx) (hU : UnifEx) (hLev : LevelEx) (hS : SplitEx)
    (hB : BadEx2) (hK : KEx) (hT : TranslEx) (hC : ChainEx) (hA : ArchEx) (hWx : F0.WEx) : FrameEx0 := by
  intro hR E _ _ _ hE n hn π hπ S hS1
  choose lam hlam using fun v : InfinitePlace E => hW E n π hπ v.embedding
  obtain ⟨μ, e, hμ, hin, hae, hop⟩ := hMu E hE
  obtain ⟨Sec, d, h⟩ := local_existence_of_unramified hSec hU hLev hS hB hE π hπ (hun E n π hπ) S hS1 μ hin hae hop
  choose u hu using hT E
  obtain ⟨C⟩ := hC E hE n hn μ e hμ lam
  have A := fun i : C.ι => (hA E hE (C.a i) (n - C.a i) (C.l₁ i) (C.l₂ i) _ _ _ _ (C.hG (C.a i)) (C.hG (n - C.a i))
    (C.hC (C.a i)) (C.hC (n - C.a i))).some
  obtain ⟨K, k1, k2, k3, k4, k5⟩ := hK E n Sec h.hSec (d.S₀ ∪ d.Bad)
    (fun w hw => (Finset.mem_union.1 hw).elim (fun a => (h.S₀ w a).1) fun a => (h.bad w a).1) (fun w => μ.loc w) hop d.L h.ok₀.L
  obtain ⟨W, w1, w2⟩ := hWx hR E n μ e lam C A
  have hk : ∀ w : Pl E, ∃ k : ℕ, w ∈ d.Bad → ¬ IsSplitAt w → 1 ≤ k ∧ (∀ γ : UL n w, γ ∈ d.KB w ↔ γ.1 ∈ MB.congK n w k) ∧
      ∀ a ≤ n, d.fix a w = fun y => (((d.KB w).relIndex (KL n w) : ℕ) : ℂ) * MB.pairIndicatorMatch n a (n - a) w k y := fun w => by
    by_cases hw : w ∈ d.Bad ∧ ¬ IsSplitAt w
    · obtain ⟨k, a1, -, a2, a3⟩ := h.mok₀.badI w hw.1 hw.2
      exact ⟨k, fun _ _ => ⟨a1, a2, a3⟩⟩
    · exact ⟨0, fun a b => absurd ⟨a, b⟩ hw⟩
  choose kB hkB using hk
  refine ⟨{ lam := lam, hlam := hlam, μ := μ, e := e, hμ := hμ, Sec := Sec, hSec := h.hSec, d₀ := d, ok₀ := h.ok₀, T₀ := h.T₀
            μloc := h.μloc, unif := h.unif, S₀ := h.S₀, S_le := h.S_le, bad := h.bad, good := h.good, kB := kB
            kB_pos := fun w a b => (hkB w a b).1, KBs := d.KB, KBs_lev := fun w a b => (h.mok₀.badS w a b).1
            KB_def := fun w => ?_, fix_def := fun a ha w => ?_, K'_lev := fun w a => (h.mok₀.S w a).2.2
            levFam := h.levFam, level := h.level, fix := h.fix, u₁ := fun a => u a, u₂ := fun a => u (n - a)
            hu := fun a => ⟨hu a, hu (n - a)⟩, C := C, A := A, K := K, hK := k1, Kc := k2, K_good := k3, K_bad := k4
            K_conj := k5, W := W, hW := w1, W_join := w2 }⟩
  · split_ifs with a b
    · rfl
    · have : {γ : UL n w | γ.1 ∈ MB.congK n w (kB w)} = (d.KB w : Set (UL n w)) := Set.ext fun γ => ((hkB w a b).2.1 γ).symm
      rw [this, Subgroup.closure_eq]
    · exact (h.off w a).1
  · split_ifs with b c
    · exact (h.mok₀.badS w b c).2 a ha
    · exact (hkB w b c).2.2 a ha
    · exact (h.off w b).2 a

end PositivityTheory.Rg.BcB.F.Ex0

end
end

namespace PositivityTheory.Rg.BcB.F.Ex0

open PositivityTheory.Rg.BcB.F

theorem frameEx0_plug (h2 : PositivityTheory.Rg.Bc.ArchbcB.B.M2) (h3 : PositivityTheory.Rg.Bc.ArchbcB.B.M3) : FrameEx0 :=
  frameEx0_of Rig.weightEx Rig.unrAE_holds (GlobalTheory.T.mu_character_exists Fok.Mu3.muExists) GlobalTheory.T.sec_ex GlobalTheory.T.uniformizer_exists GlobalTheory.T.level_exists_bis
    GlobalTheory.T.split_place_exists (badEx2_of h2 h3) GlobalTheory.T.compact_level_exists PositivityTheory.Rg.BcB.G8.translation_existence_holds F0.chainEx_holds F0.archEx_holds F0.wEx_holds

theorem frameEx0 : FrameEx0 := frameEx0_plug PositivityTheory.HtPt.Bc.CongruenceInertMatching.matchCongInert PositivityTheory.HtPt.Bc.SplitMuMatching.matchCtMuSplit

end PositivityTheory.Rg.BcB.F.Ex0
