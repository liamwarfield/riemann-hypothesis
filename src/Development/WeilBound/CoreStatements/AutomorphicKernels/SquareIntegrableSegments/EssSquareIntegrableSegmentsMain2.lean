module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothWeightPullbackChartFormula
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Development
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.Development
public import Development.WeilBound.CoreStatements.PublishedTheorems.LanglandsClassification.Bridge
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsSocleOfOrderFree
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUnitPowTendstoZeroStatement

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CohomologicalCsdTemperedOfUsed
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Zltwo

def EssSqIntUsed : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (δ : IrrGL (k := k)), 1 ≤ δ.1 → IsSqIntCoeff δ.rep → ∃ Δ : Segment k, IsLSeg Δ δ.rep

end PositivityTheory.Zltwo
end
end

section -- merged from Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.TempProdUsedOf
section -- merged from Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.TemperedProducts.Development
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SquareIntegrableSingleSegment
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightedAntitoneLastNonpos
namespace GlobalTheory.CompanionTheory.Inequalities

theorem weighted_antitone_last_nonpos : ∀ (h : ℕ) (d e : Fin h → ℝ), 2 ≤ h → (∀ i, 0 < d i) →
    Antitone e → ∑ i, d i * e i = 0 →
    ∃ j : Fin h, 0 < j.val ∧ ∑ i ∈ Finset.univ.filter (fun i => j ≤ i), d i * e i ≤ 0 := by
  intro h d e hh hd he hs
  obtain ⟨n, rfl⟩ : ∃ n, h = n + 2 := ⟨h - 2, by omega⟩
  refine ⟨Fin.last (n + 1), by simp, ?_⟩
  have hf : Finset.univ.filter (fun i : Fin (n + 2) => Fin.last (n + 1) ≤ i)
      = {Fin.last (n + 1)} := by
    ext i
    simp [Fin.last_le_iff]
  rw [hf, Finset.sum_singleton]
  have hle : (∑ i, d i) * e (Fin.last (n + 1)) ≤ 0 := by
    rw [Finset.sum_mul, ← hs]
    exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (he (Fin.le_last i)) (hd i).le
  have hpos : 0 < ∑ i, d i :=
    Finset.sum_pos (fun i _ => hd i) ⟨Fin.last _, Finset.mem_univ _⟩
  have hel : e (Fin.last (n + 1)) ≤ 0 := by
    by_contra hc
    exact absurd (mul_pos hpos (not_le.mp hc)) (not_lt.mpr hle)
  exact mul_nonpos_of_nonneg_of_nonpos (hd _).le hel

end GlobalTheory.CompanionTheory.Inequalities
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SquareIntegrableSingleSegment
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

namespace GlobalTheory.CompanionTheory.SquareIntegrableSegments

theorem length_le_one_of_partial_products {h : ℕ} (d e f : Fin h → ℝ) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hd : ∀ i, 0 < d i) (he : Antitone e) (hf : ∀ i, f i = q ^ (d i * e i))
    (hpart : ∀ j : Fin h, j.val + 1 < h → ∏ i ∈ Finset.univ.filter (· ≤ j), f (Fin.rev i) < 1)
    (hfull : ∏ i, f (Fin.rev i) = 1) : h ≤ 1 := by
  by_contra hh
  have h2 : 2 ≤ h := by omega
  have hlog : Real.log q ≠ 0 := (Real.log_neg hq0 hq1).ne
  have hprod : ∀ s : Finset (Fin h), ∏ i ∈ s, f i = q ^ (∑ i ∈ s, d i * e i) := fun s => by
    rw [Real.rpow_sum_of_pos hq0]
    exact Finset.prod_congr rfl fun i _ => hf i
  have htot : ∑ i, d i * e i = 0 := by
    have h1 : ∏ i, f i = 1 := by
      rw [← hfull]
      exact (Equiv.prod_comp Fin.revPerm f).symm
    rw [hprod] at h1
    have h3 := congrArg Real.log h1
    rw [Real.log_rpow hq0, Real.log_one] at h3
    exact (mul_eq_zero.1 h3).resolve_right hlog
  obtain ⟨j, hj0, hj⟩ := GlobalTheory.CompanionTheory.Inequalities.weighted_antitone_last_nonpos h d e h2 hd he htot
  have hlt := hpart (Fin.rev j) (by have := j.isLt; rw [Fin.val_rev]; omega)
  have hrw := GlobalTheory.CompanionTheory.FinReversal.prod_filter_le_rev h f (Fin.rev j)
  rw [Fin.rev_rev] at hrw
  rw [hrw, hprod] at hlt
  exact absurd hlt (not_lt.2 (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hq0 hq1.le hj))

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem deg_eq_of_isLSeg {Δ : Segment k} {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin N) k) V} (h : IsLSeg Δ π) : Δ.deg = N := by
  obtain ⟨hd, -⟩ := h
  rw [← hd, Segment.sum_term_fst]

theorem sum_deg_of_listing {h : ℕ} {D : Fin h → Segment k} {𝔪 : Multiset (Segment k)}
    (hD : Finset.univ.val.map D = 𝔪) : ∑ i, (D i).deg = (𝔪.map Segment.deg).sum := by
  rw [← hD, Multiset.map_map]
  rfl

theorem exists_class (hE : Zc.LSegExists k) (Δ : Segment k) : ∃ y : IrrGL (k := k), IsLSeg Δ y.rep := by
  obtain ⟨π, hd, hc⟩ := hE Δ
  exact ⟨IrrGL.of π.ρ π.smooth π.irr, hd,
    hc.of_equiv (IrrGL.equivOf π.ρ π.smooth π.irr) (Representation.Equiv.refl _)⟩

theorem card_eq_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    Zc.LSocleGL k → Zl.CasselmanNecSq k → Zc.LSegExists k → ∀ (𝔪 : Multiset (Segment k)) (N : ℕ) {V : Type}
      [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), 1 ≤ N → IsSmooth π → π.IsIrreducible →
        IsSqIntCoeff π → IsL 𝔪 π → 𝔪.card = 1 := by
  intro k _ _ _ _ hS hC hE 𝔪 N V _ _ π hN hsm hirr hsq hL
  choose y hy using exists_class hE
  have hdeg : ∀ Δ, (y Δ).1 = Δ.deg := fun Δ => (deg_eq_of_isLSeg (hy Δ)).symm
  have hpos : ∀ Δ, 0 < (y Δ).1 := fun Δ => by
    rw [hdeg]
    exact Nat.mul_pos Δ.len_pos Δ.d_pos
  choose s hs using fun Δ => GlobalTheory.T.central_character_norm_eq_pow k (y Δ) (hpos Δ)
  obtain ⟨h, D, hD, hanti, hno⟩ := GlobalTheory.CompanionTheory.Multiset.exists_antitone_listing 𝔪 s Segment.Precedes
    fun a b hab => GlobalTheory.T.exponent_lt_of_precedes_of_isLSeg k a b (y a) (y b) (s a) (s b) (hy a) (hy b) (hs a) (hs b) hab
  let x : Fin h → IrrGL (k := k) := fun i => y (D i)
  have hLF : LFactors 𝔪 x := ⟨D, ⟨hD, hno⟩, fun i => hy (D i)⟩
  have hsum : ∑ a, (x a).1 = N := by
    obtain ⟨h', x', hd', ⟨D', ⟨hD', -⟩, hx'⟩, -⟩ := hL
    rw [← hd']
    have e1 : ∑ a, (x a).1 = ∑ a, (D a).deg := Finset.sum_congr rfl fun a _ => hdeg (D a)
    have e2 : ∑ a, (x' a).1 = ∑ a, (D' a).deg :=
      Finset.sum_congr rfl fun a _ => (deg_eq_of_isLSeg (hx' a)).symm
    rw [e1, e2, sum_deg_of_listing hD, sum_deg_of_listing hD']
  have hsumrev : ∑ a, (x (Fin.rev a)).1 = N := by
    rw [← hsum]
    exact Equiv.sum_comp Fin.revPerm fun a => (x a).1
  have hsoc := hS 𝔪 h N x hsumrev hLF π hL
  have hposrev : ∀ a, 0 < ((x ∘ Fin.rev) a).1 := fun a => hpos _
  have hjm := GlobalTheory.T.jacquet_multiplicity_pos_of_socle k h N (x ∘ Fin.rev) hsumrev π hsm hposrev hsoc
  have hex := hC N π hN hsm hirr hsq h (x ∘ Fin.rev) hsumrev hposrev hjm
  obtain ⟨t, ht⟩ := GlobalTheory.T.exists_unit_pow_tendsto_zero' k
  have hnabs := GlobalTheory.T.norm_lt_one_of_pow_tendsto_zero k t ht
  choose c hc using fun i => GlobalTheory.T.central_character_exists k (x i) t
  obtain ⟨hpart, hfull⟩ := hex t ht (c ∘ Fin.rev) fun i => hc (Fin.rev i)
  have hle : h ≤ 1 := length_le_one_of_partial_products (fun i => ((x i).1 : ℝ)) (fun i => s (D i))
    (fun i => ‖c i‖) (nabs_pos' k t) hnabs (fun i => by exact_mod_cast hpos (D i)) hanti
    (fun i => hs (D i) t (c i) (hc i)) hpart hfull
  have hh0 : h ≠ 0 := by
    rintro rfl
    simp at hsum
    omega
  have hcard : 𝔪.card = h := by
    rw [← hD]
    simp
  omega

end GlobalTheory.CompanionTheory.SquareIntegrableSegments
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SquareIntegrableSingleSegmentStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.square_integrable_single_segment : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], Zc.LSocleGL k → Zl.CasselmanNecSq k → Zc.LSegExists k → ∀ (𝔪 : Multiset (Segment k)) (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), 1 ≤ N → IsSmooth π → π.IsIrreducible → IsSqIntCoeff π → IsL 𝔪 π → 𝔪.card = 1 := by
  first | exact @GlobalTheory.CompanionTheory.SquareIntegrableSegments.card_eq_one | exact GlobalTheory.CompanionTheory.SquareIntegrableSegments.card_eq_one | (intros; apply GlobalTheory.CompanionTheory.SquareIntegrableSegments.card_eq_one <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsSingleSegmentIsSegmentRep
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsSingleSegmentIsSegmentRep
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

namespace GlobalTheory.CompanionTheory.LocGL

theorem isLSeg_of_isL_singleton : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (Δ : Segment k) (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V), IsL {Δ} π → IsLSeg Δ π := by
  intro k _ _ _ _ Δ N V _ _ π h
  obtain ⟨h', x, hd, ⟨Δ', ⟨hm, -⟩, hL⟩, hc⟩ := h
  have hcard : h' = 1 := by
    have := congrArg Multiset.card hm
    simpa using this
  subst hcard
  have hΔ : Δ' 0 = Δ := by
    have hmem : Δ' 0 ∈ Finset.univ.val.map Δ' := Multiset.mem_map_of_mem _ (Finset.mem_univ_val _)
    rw [hm] at hmem
    simpa using hmem
  have hL0 : IsLSeg Δ (x 0).rep := hΔ ▸ hL 0
  obtain ⟨y, rfl⟩ : ∃ y, x = fun _ => y := ⟨x 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
  have hN : y.1 = N := by simpa using hd
  subst hN
  obtain ⟨ψ⟩ := nonempty_equiv_prodIrr_one y hd
  obtain ⟨φ⟩ := hc.unique ((isCosocle_self y.2.rep.irr).of_equiv (.refl _) ψ)
  exact hL0.of_equiv φ

end GlobalTheory.CompanionTheory.LocGL
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsSingleSegmentIsSegmentRepStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.langlands_single_segment_is_segment_rep : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Δ : Segment k) (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsL {Δ} π → IsLSeg Δ π := by
  first | exact @GlobalTheory.CompanionTheory.LocGL.isLSeg_of_isL_singleton | exact GlobalTheory.CompanionTheory.LocGL.isLSeg_of_isL_singleton | (intros; apply GlobalTheory.CompanionTheory.LocGL.isLSeg_of_isL_singleton <;> assumption)
end
end

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

noncomputable section

namespace Zz

theorem zblsegsingle : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Δ : Segment k) (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsL {Δ} π → IsLSeg Δ π := GlobalTheory.T.langlands_single_segment_is_segment_rep

theorem zbz1core : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], Zc.LSocleGL k → Zl.CasselmanNecSq k → Zc.LSegExists k → ∀ (𝔪 : Multiset (Segment k)) (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), 1 ≤ N → IsSmooth π → π.IsIrreducible → IsSqIntCoeff π → IsL 𝔪 π → 𝔪.card = 1 := GlobalTheory.T.square_integrable_single_segment

theorem sqInt_isLSeg (hE : GlobalTheory.Published.LanglandsExhaustionGL) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (hS : Zc.LSocleGL k)
    (hC : Zl.CasselmanNecSq k) (hL : Zc.LSegExists k) (δ : IrrGL (k := k)) (h1 : 1 ≤ δ.1) (hδ : IsSqIntCoeff δ.rep) :
    ∃ Δ : Segment k, IsLSeg Δ δ.rep := by
  obtain ⟨𝔪, h𝔪⟩ := hE k δ
  have hc := zbz1core k hS hC hL 𝔪 δ.1 δ.rep h1 δ.2.rep.smooth δ.2.rep.irr hδ h𝔪
  obtain ⟨Δ, rfl⟩ := Multiset.card_eq_one.1 hc
  exact ⟨Δ, zblsegsingle k Δ δ.1 δ.rep h𝔪⟩

end Zz

end
end

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL

namespace PositivityTheory.Zltwo

theorem essSqIntUsed_of (hE : GlobalTheory.Published.LanglandsExhaustionGL)
    (hS : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k],
      Zc.LSocleGL k)
    (hL : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k],
      Zc.LSegExists k) : EssSqIntUsed := by
  intro k _ _ _ _ _ δ h1 hδ
  exact Zz.sqInt_isLSeg hE k (hS k) (Zl.JC.casselmanNecSq_holds k) (hL k) δ h1 hδ

end PositivityTheory.Zltwo
end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SquareIntegrableSegments.EssSquareIntegrableSegmentsOfLit
section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SquareIntegrableSegments.Development
section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SquareIntegrableSegments.SegmentOfTwistedSquareIntegrable
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL

namespace PositivityTheory.PfEss.H13

theorem isLSeg_of_eq {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {Δ : Segment k} {x y : IrrGL (k := k)} (hxy : x = y) (h : IsLSeg Δ x.rep) : IsLSeg Δ y.rep := by
  subst hxy
  exact h

theorem segment_of_twisted_square_integrable (hU : PositivityTheory.Zltwo.EssSqIntUsed) :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (δ : IrrGL (k := k)), 1 ≤ δ.1 →
      (∃ (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ), IsSqIntCoeff (δ.tw χ hχ).rep) → ∃ Δ : Segment k, IsLSeg Δ δ.rep := by
  intro k _ _ _ _ _ δ hδ ⟨χ, hχ, hs⟩
  obtain ⟨Δ', hΔ'⟩ := hU k (δ.tw χ hχ) hδ hs
  refine ⟨Δ'.tw χ⁻¹ hχ.inv, ?_⟩
  exact isLSeg_of_eq (IrrGL.tw_tw_inv δ χ hχ)
    ((hΔ'.tw χ⁻¹ hχ.inv).of_equiv ((δ.tw χ hχ).twEquiv χ⁻¹ hχ.inv))

theorem square_integrable_of_segment_twist
    (h2 : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (y : IrrGL (k := k)),
      ∃ (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ), ∀ (t : kˣ) (c : ℂ), Zl.ScalarBy (y.tw χ hχ) t c → ‖c‖ = 1)
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hF : GlobalTheory.Published.StandardFunctorsFiniteLength) :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], Zc.LSegJacquet k → ∀ (δ : IrrGL (k := k)), (∃ Δ : Segment k, IsLSeg Δ δ.rep) →
      ∃ (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ), IsSqIntCoeff (δ.tw χ hχ).rep := by
  intro k _ _ _ _ hJ δ ⟨Δ, hΔ⟩
  obtain ⟨χ, hχ, hc⟩ := h2 k δ
  exact ⟨χ, hχ, Zls.FreeSingleHomotopyEquivDiscreteChains.centredSegSqInt k hA hF hJ (Δ.tw χ hχ) (δ.tw χ hχ)
    ((hΔ.tw χ hχ).of_equiv (δ.twEquiv χ hχ)) hc⟩

end PositivityTheory.PfEss.H13

end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SquareIntegrableSegments.ExistsUnitaryCentralTwist
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

namespace PositivityTheory.PfEss.H2

private theorem nontrivial_irrRep_V {G : Type} [Group G] [TopologicalSpace G] (σ : IrrRep G) :
    Nontrivial σ.V := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  haveI : IsSimpleOrder (Subrepresentation σ.ρ) := σ.irr
  apply (bot_ne_top : (⊥ : Subrepresentation σ.ρ) ≠ ⊤)
  apply Subrepresentation.ext
  ext v
  rw [Subsingleton.elim v 0]
  exact ⟨fun _ => (⊤ : Subrepresentation σ.ρ).toSubmodule.zero_mem,
    fun _ => (⊥ : Subrepresentation σ.ρ).toSubmodule.zero_mem⟩

private theorem exists_smooth_central_character_of_admissible {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (σ : IrrRep (GL (Fin n) k)) (hadm : IsAdmissible σ.ρ) :
    ∃ ω : kˣ →* ℂˣ, IsSmoothChar ω ∧ HasCentralChar σ.ρ ω := by
  classical
  haveI hnt : Nontrivial σ.V := nontrivial_irrRep_V σ
  haveI : IsSimpleOrder (Subrepresentation σ.ρ) := σ.irr
  obtain ⟨v0, hv0⟩ := exists_ne (0 : σ.V)
  have hinv : ∀ (g : GL (Fin n) k) (v : σ.V), σ.ρ g⁻¹ (σ.ρ g v) = v := by
    intro g v
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  let S : Subgroup (GL (Fin n) k) :=
    { carrier := {g | σ.ρ g v0 = v0}
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
        rw [hb, ha]
      one_mem' := by simp
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at *
        calc σ.ρ a⁻¹ v0 = σ.ρ a⁻¹ (σ.ρ a v0) := by rw [ha]
          _ = v0 := hinv a v0 }
  have hSopen : IsOpen (S : Set (GL (Fin n) k)) := σ.smooth v0
  let K : Subgroup (GL (Fin n) k) := KO k (Fin n) ⊓ S
  have hKo : IsOpen (K : Set (GL (Fin n) k)) := by
    rw [Subgroup.coe_inf]
    exact GlobalTheory.SplitFlip.isOpen_KO.inter hSopen
  have hKc : IsCompact (K : Set (GL (Fin n) k)) :=
    GlobalTheory.SplitFlip.isCompact_KO.of_isClosed_subset (Subgroup.isClosed_of_isOpen K hKo)
      (fun x hx => (Subgroup.mem_inf.mp hx).1)
  haveI hfd : FiniteDimensional ℂ (fixed σ.ρ K) := hadm.2 K hKo hKc
  have hv0K : v0 ∈ fixed σ.ρ K := by
    show ∀ h : K, σ.ρ h v0 = ((1 : K →* ℂˣ) h : ℂ) • v0
    intro h
    rw [MonoidHom.one_apply, Units.val_one, one_smul]
    exact (Subgroup.mem_inf.mp h.2).2
  have hcomm : ∀ (t : kˣ) (g : GL (Fin n) k),
      Matrix.GeneralLinearGroup.scalar (Fin n) t * g = g * Matrix.GeneralLinearGroup.scalar (Fin n) t := by
    intro t g
    ext : 1
    simp only [Matrix.GeneralLinearGroup.scalar, Units.val_mul, Units.coe_map, MonoidHom.coe_coe]
    exact Matrix.scalar_commute _ (fun _ => Commute.all _ _) _
  have key : ∀ t : kˣ, ∃ c : ℂ, ∀ v, σ.ρ (Matrix.GeneralLinearGroup.scalar (Fin n) t) v = c • v := by
    intro t
    set s := Matrix.GeneralLinearGroup.scalar (Fin n) t with hs
    have hρc : ∀ g v, σ.ρ s (σ.ρ g v) = σ.ρ g (σ.ρ s v) := by
      intro g v
      rw [← Module.End.mul_apply, ← map_mul, hcomm, map_mul, Module.End.mul_apply]
    have hW : ∀ w ∈ fixed σ.ρ K, σ.ρ s w ∈ fixed σ.ρ K := by
      intro w hw
      have hw' : ∀ h : K, σ.ρ h w = ((1 : K →* ℂˣ) h : ℂ) • w := hw
      show ∀ h : K, σ.ρ h (σ.ρ s w) = ((1 : K →* ℂˣ) h : ℂ) • (σ.ρ s w)
      intro h
      have := hw' h
      rw [MonoidHom.one_apply, Units.val_one, one_smul] at this ⊢
      rw [← hρc, this]
    let f : Module.End ℂ (fixed σ.ρ K) := (σ.ρ s).restrict hW
    haveI : Nontrivial (fixed σ.ρ K) :=
      ⟨⟨⟨v0, hv0K⟩, 0, fun h => hv0 (congrArg Subtype.val h)⟩⟩
    obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue f
    obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
    let E : Subrepresentation σ.ρ :=
      { toSubmodule := LinearMap.ker (σ.ρ s - c • LinearMap.id)
        apply_mem_toSubmodule := by
          intro g v hv
          simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
            sub_eq_zero] at hv ⊢
          rw [hρc, hv, map_smul] }
    rcases IsSimpleOrder.eq_bot_or_eq_top E with hE | hE
    · exfalso
      have hwE : (w : σ.V) ∈ E.toSubmodule := by
        simp only [E, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
          sub_eq_zero]
        exact congrArg Subtype.val hw.apply_eq_smul
      rw [hE] at hwE
      exact hw.2 (Subtype.ext ((Submodule.mem_bot ℂ).mp hwE))
    · refine ⟨c, fun v => ?_⟩
      have hvE : v ∈ (⊤ : Subrepresentation σ.ρ).toSubmodule := Submodule.mem_top
      rw [← hE] at hvE
      simpa [E, sub_eq_zero] using hvE
  choose c hc using key
  have huniq : ∀ a b : ℂ, a • v0 = b • v0 → a = b := fun a b h => smul_left_injective ℂ hv0 h
  have hc0 : ∀ t, c t ≠ 0 := by
    intro t h
    have h1 := hc t v0
    rw [h, zero_smul] at h1
    apply hv0
    rw [← hinv (Matrix.GeneralLinearGroup.scalar (Fin n) t) v0, h1, map_zero]
  have hmul : ∀ a b, c (a * b) = c a * c b := by
    intro a b
    apply huniq
    rw [← hc, map_mul, map_mul, Module.End.mul_apply, hc b, map_smul, hc a, smul_smul, mul_comm]
  have hone : c 1 = 1 := by
    apply huniq
    rw [← hc, map_one, map_one, Module.End.one_apply, one_smul]
  let ω : kˣ →* ℂˣ :=
    { toFun := fun t => Units.mk0 (c t) (hc0 t)
      map_one' := Units.ext (by simp [hone])
      map_mul' := fun a b => Units.ext (by simp [hmul]) }
  have hcont : Continuous (Matrix.GeneralLinearGroup.scalar (Fin n) : kˣ → GL (Fin n) k) := by
    apply Units.continuous_iff.mpr
    constructor
    · simp only [Matrix.GeneralLinearGroup.scalar, Units.coe_map, MonoidHom.coe_coe]
      exact Continuous.matrix_diagonal (continuous_pi fun _ => Units.continuous_val)
    · simp only [Matrix.GeneralLinearGroup.scalar, Units.coe_map_inv, MonoidHom.coe_coe, map_inv]
      exact Continuous.matrix_diagonal (continuous_pi fun _ => Units.continuous_coe_inv)
  refine ⟨ω, ?_, fun z v => hc z v⟩
  show IsOpen (ω.ker : Set kˣ)
  have hker : (ω.ker : Set kˣ) =
      (Matrix.GeneralLinearGroup.scalar (Fin n) : kˣ → GL (Fin n) k) ⁻¹' (S : Set (GL (Fin n) k)) := by
    ext t
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage]
    show Units.mk0 (c t) (hc0 t) = 1 ↔ σ.ρ (Matrix.GeneralLinearGroup.scalar (Fin n) t) v0 = v0
    rw [hc t v0, Units.ext_iff, Units.val_mk0, Units.val_one]
    constructor
    · intro h
      rw [h, one_smul]
    · intro h
      apply huniq
      rw [h, one_smul]
  rw [hker]
  exact hSopen.preimage hcont

theorem exists_unitary_central_twist (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (y : IrrGL (k := k)), ∃ (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ),
      ∀ (t : kˣ) (c : ℂ), Zl.ScalarBy (y.tw χ hχ) t c → ‖c‖ = 1 := by
  intro k _ _ _ _ y
  obtain ⟨ω, hωs, hω⟩ := exists_smooth_central_character_of_admissible y.fst y.snd.rep
    (hA k y.fst y.snd.rep.V y.snd.rep.ρ y.snd.rep.smooth y.snd.rep.irr)
  obtain ⟨r, hr⟩ := GlobalTheory.SmoothCharNorm.norm_eq_nabs_rpow k ω hωs
  set s' : ℝ := -(r / (y.fst : ℝ)) with hs'
  refine ⟨absPow k (s' : ℂ), GlobalTheory.LocGL.isSmoothChar_absPow _, fun t c hsc => ?_⟩
  have hsc' : ∀ v, (y.nu (s' : ℂ)).rep (Matrix.GeneralLinearGroup.scalar (Fin (y.nu (s' : ℂ)).fst) t) v = c • v :=
    hsc
  have hcc := GlobalTheory.LocGL.UnitaryOrder.hasCentralChar_nu y hω (s' : ℂ)
  haveI : Nontrivial (y.nu (s' : ℂ)).snd.rep.V := nontrivial_irrRep_V _
  obtain ⟨v0, hv0⟩ := exists_ne (0 : (y.nu (s' : ℂ)).snd.rep.V)
  by_cases hn : y.fst = 0
  · have hn' : (y.nu (s' : ℂ)).fst = 0 := hn
    have h1 := hsc' v0
    have hs1 : Matrix.GeneralLinearGroup.scalar (Fin (y.nu (s' : ℂ)).fst) t = 1 := by
      ext i j
      exact absurd i.2 (by omega)
    rw [hs1, map_one, Module.End.one_apply] at h1
    have hc1 : c = 1 := smul_left_injective ℂ hv0 (by show c • v0 = (1 : ℂ) • v0; rw [one_smul]; exact h1.symm)
    rw [hc1, norm_one]
  · have hc : c = ((ω * absPow k (s' : ℂ) ^ y.fst) t : ℂ) :=
      smul_left_injective ℂ hv0 ((hsc' v0).symm.trans (hcc t v0))
    rw [hc]
    have hpos : 0 < ‖((ω * absPow k (s' : ℂ) ^ y.fst) t : ℂ)‖ := norm_pos_iff.mpr (Units.ne_zero _)
    have hL := GlobalTheory.LocGL.UnitaryOrder.log_norm_mul_absPow ω s' y.fst t
    rw [hr t, Real.log_rpow (GlobalTheory.SplitWeil.nabs_pos k t)] at hL
    apply Real.eq_one_of_pos_of_log_eq_zero hpos
    rw [hL, hs']
    have hn0 : (y.fst : ℝ) ≠ 0 := by exact_mod_cast hn
    field_simp
    ring

end PositivityTheory.PfEss.H2

end
end

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL

namespace PositivityTheory.PfEss

theorem segment_of_twisted_square_integrable (hU : PositivityTheory.Zltwo.EssSqIntUsed) :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (δ : IrrGL (k := k)), 1 ≤ δ.1 →
      (∃ (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ), IsSqIntCoeff (δ.tw χ hχ).rep) → ∃ Δ : Segment k, IsLSeg Δ δ.rep := by
  exact PositivityTheory.PfEss.H13.segment_of_twisted_square_integrable hU

theorem exists_unitary_central_twist (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (y : IrrGL (k := k)), ∃ (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ),
      ∀ (t : kˣ) (c : ℂ), Zl.ScalarBy (y.tw χ hχ) t c → ‖c‖ = 1 := by
  exact PositivityTheory.PfEss.H2.exists_unitary_central_twist hA

theorem segment_gives_square_integrable (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hF : GlobalTheory.Published.StandardFunctorsFiniteLength) :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], Zc.LSegJacquet k → ∀ (δ : IrrGL (k := k)), (∃ Δ : Segment k, IsLSeg Δ δ.rep) →
      ∃ (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ), IsSqIntCoeff (δ.tw χ hχ).rep := by
  exact PositivityTheory.PfEss.H13.square_integrable_of_segment_twist (exists_unitary_central_twist hA) hA hF

theorem essSquareIntegrableSegments_of (hE : GlobalTheory.Published.LanglandsExhaustionGL)
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hF : GlobalTheory.Published.StandardFunctorsFiniteLength)
    (hS : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k], Zc.LSocleGL k)
    (hL : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k], Zc.LSegExists k)
    (hJ : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k], Zc.LSegJacquet k) : GlobalTheory.Published.EssSquareIntegrableSegments := by
  intro k _ _ _ _ _ δ hδ
  exact ⟨segment_of_twisted_square_integrable (PositivityTheory.Zltwo.essSqIntUsed_of hE hS hL) k δ hδ, segment_gives_square_integrable hA hF k (hJ k) δ⟩

end PositivityTheory.PfEss

end
end

noncomputable section

namespace PositivityTheory.PfEss

theorem essSquareIntegrableSegments_main (hE : GlobalTheory.Published.LanglandsExhaustionGL)
    (hF : GlobalTheory.Published.StandardFunctorsFiniteLength)
    (hS : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k], Zc.LSocleGL k)
    (hL : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k], Zc.LSegExists k)
    (hJ : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k], Zc.LSegJacquet k) : GlobalTheory.Published.EssSquareIntegrableSegments :=
  essSquareIntegrableSegments_of hE PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top hF hS hL hJ

end PositivityTheory.PfEss

end
end

noncomputable section

namespace PositivityTheory.PfEss

theorem lSocleGL_of_orderFree (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hO : Zc.LOrderFree k) : Zc.LSocleGL k :=
  GlobalTheory.T.langlands_socle_of_order_free PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top (GlobalTheory.T.local_langlands_of_irreducible_admissible PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top) hO

theorem essSquareIntegrableSegments_main2 (hE : GlobalTheory.Published.LanglandsExhaustionGL)
    (hF : GlobalTheory.Published.StandardFunctorsFiniteLength)
    (hO : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k], Zc.LOrderFree k)
    (hL : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k], Zc.LSegExists k)
    (hJ : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k], Zc.LSegJacquet k) : GlobalTheory.Published.EssSquareIntegrableSegments :=
  essSquareIntegrableSegments_main hE hF (fun k _ _ _ _ _ => lSocleGL_of_orderFree k (hO k)) hL hJ

end PositivityTheory.PfEss

end
