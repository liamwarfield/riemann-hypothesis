module

public import Development.WeilBound.CoreStatements.HodgeTatePoints.Imports
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XCoherentGens
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.X_join_model
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TensorProductHopfOrders
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeFamilyInjectiveModelFacts
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeGoodBaseChange

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PowerSeriesPowPFrobenius
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PowerSeriesPowPFrobenius
namespace GlobalTheory.CompanionTheory.Ar.Conj

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

theorem pow_eq_ev_frobenius : ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] (d n : ℕ) (f : PS R n d),
    f ^ p = ev (fun j => ptPow R d p j) (MvPowerSeries.map (frobenius R p) f) :=
  PositivityTheory.HtPt.Cb.frob_subst

end GlobalTheory.CompanionTheory.Ar.Conj
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PowerSeriesPowPFrobeniusStatement
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.power_series_pow_p_frobenius : ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] (d n : ℕ) (f : PS R n d), f ^ p = ev (fun j => ptPow R d p j) (MvPowerSeries.map (frobenius R p) f) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.pow_eq_ev_frobenius | exact GlobalTheory.CompanionTheory.Ar.Conj.pow_eq_ev_frobenius | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.pow_eq_ev_frobenius <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ModelRefinementExists
section -- merged from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.X_normal_join
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

namespace PositivityTheory.Xgn.A_normal_join

open PositivityTheory.Xgn.A_coherent_gens (mem_spanOver spanOver_le)
open PositivityTheory.Xgn.A_chart_noeth_frac (mseg_join ratio_eq)
open ReciprocityTheory.ChartRestriction.G.Geo (exists_pow_mul_mem_chartRing div_mem_chartRing)

variable {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]

def intGrp (R : Subalgebra O Ω) : AddSubgroup Ω :=
  (integralClosure R Ω).toSubring.toAddSubgroup

theorem mem_intGrp {R : Subalgebra O Ω} {v : Ω} : v ∈ intGrp R ↔ IsIntegral R v := Iff.rfl

theorem isIntegral_of_mem {R : Subalgebra O Ω} {a : Ω} (ha : a ∈ R) : IsIntegral R a :=
  isIntegral_algebraMap (R := R) (A := Ω) (x := ⟨a, ha⟩)

theorem exists_pow_mul_isIntegral (R R' : Subalgebra O Ω) {r : Ω} (hr : IsIntegral R r)
    (h : ∀ a ∈ R', ∃ n : ℕ, IsIntegral R (r ^ n * a)) {v : Ω} (hv : IsIntegral R' v) :
    ∃ n : ℕ, IsIntegral R (r ^ n * v) := by
  obtain ⟨p, hp, hpv⟩ := hv
  choose m hm using fun i => h _ (p.coeff i).2
  let N := p.support.sup m
  let q : Polynomial Ω := Polynomial.C (r ^ N) * p.map (algebraMap R' Ω)
  have hq : q ∈ Polynomial.lifts (algebraMap (integralClosure R Ω) Ω) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    refine ⟨⟨q.coeff i, ?_⟩, rfl⟩
    show IsIntegral R (q.coeff i)
    simp only [q, Polynomial.coeff_C_mul, Polynomial.coeff_map]
    by_cases hi : i ∈ p.support
    · have hle : m i ≤ N := Finset.le_sup hi
      have e : r ^ N * algebraMap R' Ω (p.coeff i) = r ^ (N - m i) * (r ^ m i * (p.coeff i : Ω)) := by
        rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]; rfl
      rw [e]
      exact (hr.pow _).mul (hm i)
    · rw [Polynomial.notMem_support_iff.1 hi, map_zero, mul_zero]
      exact isIntegral_zero
  obtain ⟨Q, hQ⟩ := (Polynomial.mem_lifts _).1 hq
  have h0 : Polynomial.aeval v Q = 0 := by
    rw [← Polynomial.aeval_map_algebraMap Ω, hQ]
    simp only [q, map_mul, Polynomial.aeval_map_algebraMap]
    rw [Polynomial.aeval_def (R := R'), hpv, mul_zero]
  have h1 := isIntegral_leadingCoeff_smul Q v h0
  have h2 : algebraMap (integralClosure R Ω) Ω Q.leadingCoeff = r ^ N := by
    have hinj : Function.Injective (algebraMap (integralClosure R Ω) Ω) := Subtype.val_injective
    rw [← Polynomial.leadingCoeff_map_of_injective hinj, hQ]
    simp only [q]
    rw [(hp.map _).leadingCoeff_C_mul]
  rw [Algebra.smul_def, h2] at h1
  set_option synthInstance.maxHeartbeats 200000 in
    exact ⟨N, isIntegral_trans (R := R) (A := integralClosure R Ω) (B := Ω) (r ^ N * v) h1⟩

theorem exists_span (R : Subalgebra O Ω) [h : Module.Finite R (integralClosure R Ω)] :
    ∃ S : Finset Ω, intGrp R = spanOver R (S : Set Ω) := by
  have hfg : (Subalgebra.toSubmodule (integralClosure R Ω)).FG :=
    Module.Finite.iff_fg.1 h
  obtain ⟨S, hS⟩ := hfg
  refine ⟨S, le_antisymm (fun v hv => ?_) (spanOver_le R (fun a ha v hv => ?_) fun e he => ?_)⟩
  · have hv' : v ∈ Submodule.span R (S : Set Ω) := by rw [hS]; exact hv
    obtain ⟨f, hf⟩ := (Submodule.mem_span_finset).1 hv'
    rw [← hf.2]
    exact sum_mem fun e he => AddSubgroup.subset_closure ⟨f e, (f e).2, e, he, rfl⟩
  · exact (isIntegral_of_mem ha).mul hv
  · have he' : e ∈ Submodule.span R (S : Set Ω) := Submodule.subset_span he
    rw [hS] at he'
    exact he'

theorem isIntegrallyClosedIn (R R' : Subalgebra O Ω) {u : Ω} (hu0 : u ≠ 0) (hu : IsIntegral R u)
    (h1 : ∀ a, IsIntegral R a → u⁻¹ * a ∈ R') (h2 : ∀ a ∈ R', ∃ n : ℕ, IsIntegral R (u ^ n * a)) :
    IsIntegrallyClosedIn R' Ω := by
  refine isIntegrallyClosedIn_iff.2 ⟨Subtype.val_injective, fun {v} hv => ?_⟩
  obtain ⟨n, hn⟩ := exists_pow_mul_isIntegral R R' hu h2 hv
  have hi : u⁻¹ ∈ R' := by simpa using h1 1 isIntegral_one
  have ha := mul_mem (pow_mem hi n) (h1 _ (hu.mul hn))
  have e : u⁻¹ ^ n * (u⁻¹ * (u * (u ^ n * v))) = v := by
    rw [inv_mul_cancel_left₀ hu0, inv_pow, inv_mul_cancel_left₀ (pow_ne_zero _ hu0)]
  rw [e] at ha
  exact ⟨⟨v, ha⟩, rfl⟩

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


omit [∀ k, Fintype (ι k)] in
theorem fam (x : (Σ k, ι k) → Ω) : IsLatFamily O x fun c => intGrp (chartRing O (mseg x) c) := by
  refine ⟨fun s _ a ha v hv => (isIntegral_of_mem ha).mul hv, fun s t hs _ v hv => ?_⟩
  refine exists_pow_mul_isIntegral _ (chartRing O (mseg x) s)
    (isIntegral_of_mem (div_mem_chartRing (mseg x) t s)) (fun a ha => ?_) hv
  obtain ⟨n, hn⟩ := exists_pow_mul_mem_chartRing (mseg x) s t hs ha
  exact ⟨n, isIntegral_of_mem hn⟩

end PositivityTheory.Xgn.A_normal_join

open PositivityTheory.Xgn.A_normal_join PositivityTheory.Xgn.A_coherent_gens PositivityTheory.Xgn.A_chart_noeth_frac in
theorem PositivityTheory.Xgn.t_normal_join : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) [CharZero O] (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → fnField O x = ⊤ → ∃ (K' : Type) (_ : Fintype K') (_ : DecidableEq K') (ι' : K' → Type) (_ : ∀ k, Fintype (ι' k)) (z : (Σ k, ι' k) → Ω), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z)) d ∧ NormalCharts O (joinCoord x z) := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x _ d hx htop
  obtain ⟨hK, hx0, hinj, hT⟩ := (PositivityTheory.Xgn.A_join_model.isModelOver_iff x d).1 hx
  obtain ⟨-, hfrac, hjoin⟩ := PositivityTheory.Xgn.t_chart_noeth_frac O Ω K ι x
  have hfg : ∀ c, mseg x c ≠ 0 → ∃ S : Finset Ω, intGrp (chartRing O (mseg x) c) =
      spanOver (chartRing O (mseg x) c) (S : Set Ω) := by
    intro c hc
    have := hfrac htop c hc
    have : Algebra.FiniteType O (chartRing O (mseg x) c) :=
      (Subalgebra.fg_iff_finiteType _).1 (Subalgebra.fg_def.2 ⟨_, Set.finite_range _, rfl⟩)
    have : Algebra.EssFiniteType (chartRing O (mseg x) c) Ω :=
      .of_isLocalization Ω (nonZeroDivisors _)
    have := GlobalTheory.finite_integralClosure_of_injective O (chartRing O (mseg x) c) Ω hinj
    exact exists_span _
  obtain ⟨a, ha⟩ := PositivityTheory.Xgn.t_coherent_gens O Ω K ι x Ω _ (fam x) hfg
  obtain ⟨M, v, hv⟩ := ha a le_rfl
  let z : (Σ _ : Unit, Fin M) → Ω := fun p => v p.2
  obtain ⟨hf, hle⟩ := hjoin Unit (fun _ => Fin M) z
  have hz : ∃ j, v j ≠ 0 := by
    by_contra hn
    push Not at hn
    choose c hc using hx0
    have hc' : mseg x c ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hc k
    have h1 : (1 : Ω) ∈ intGrp (chartRing O (mseg x) c) := isIntegral_one
    rw [hv c hc'] at h1
    have h2 := spanOver_le (L := ⊥) (chartRing O (mseg x) c)
      (S := Set.range fun j => (chartMon x c a)⁻¹ • v j)
      (fun a _ w hw => by rw [AddSubgroup.mem_bot.1 hw, smul_zero]; exact zero_mem _)
      (by rintro _ ⟨j, rfl⟩; simp [hn j]) h1
    exact one_ne_zero (AddSubgroup.mem_bot.1 h2)
  refine ⟨Unit, inferInstance, inferInstance, fun _ => Fin M, inferInstance, z, ?_, fun c' hc' => ?_⟩
  · refine (PositivityTheory.Xgn.A_join_model.isModelOver_iff (joinCoord x z) d).2 ⟨inferInstance, ?_, hinj, ?_⟩
    · rintro (k | k)
      · exact hx0 k
      · exact hz
    · rw [hf htop, ← htop]
      exact hT
  · obtain ⟨hc, hR⟩ := hle c' hc'
    have hj : ∀ t : ∀ k : K ⊕ Unit, Sum.elim ι (fun _ => Fin M) k,
        mseg (joinCoord x z) t = mseg x (restrictChart t) * v (t (.inr ())) := by
      intro t
      rw [mseg_join]
      simp [mseg, z]
    have hl : v (c' (.inr ())) ≠ 0 := by
      rw [hj] at hc'
      exact right_ne_zero_of_mul hc'
    have hm : chartMon x (restrictChart c') a ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun k _ =>
        zpow_ne_zero _ (Finset.prod_ne_zero_iff.1 hc k (Finset.mem_univ k))
    have hw : ∀ j, IsIntegral (chartRing O (mseg x) (restrictChart c'))
        ((chartMon x (restrictChart c') a)⁻¹ * v j) := by
      intro j
      rw [← mem_intGrp, hv _ hc]
      exact mem_spanOver _ ⟨j, rfl⟩
    refine isIntegrallyClosedIn (chartRing O (mseg x) (restrictChart c')) _
      (mul_ne_zero (inv_ne_zero hm) hl) (hw _) (fun b hb => ?_) (fun b hb => ?_)
    · rw [← mem_intGrp, hv _ hc] at hb
      refine spanOver_le (L := (chartRing O (mseg (joinCoord x z)) c').toSubring.toAddSubgroup.comap
        (AddMonoidHom.mulLeft ((chartMon x (restrictChart c') a)⁻¹ * v (c' (.inr ())))⁻¹)) _
        (fun r hr w hw => ?_) ?_ hb
      · show _ * (r * w) ∈ chartRing O (mseg (joinCoord x z)) c'
        rw [mul_left_comm]
        exact mul_mem (hR hr) hw
      · rintro _ ⟨j, rfl⟩
        show _ * (_ * v j) ∈ chartRing O (mseg (joinCoord x z)) c'
        have e : ((chartMon x (restrictChart c') a)⁻¹ * v (c' (.inr ())))⁻¹ *
            ((chartMon x (restrictChart c') a)⁻¹ * v j) = v j / v (c' (.inr ())) := by
          field_simp
        rw [e]
        have e2 := ratio_eq (joinCoord x z) c' hc' (.inr ()) j
        have e3 : v j / v (c' (.inr ())) =
            mseg (joinCoord x z) (Function.update c' (.inr ()) j) / mseg (joinCoord x z) c' := e2.symm
        rw [e3]
        exact ReciprocityTheory.ChartRestriction.G.Geo.div_mem_chartRing (o := O) _ _ _
    · unfold chartRing at hb
      induction hb using Algebra.adjoin_induction with
      | mem b hb =>
        obtain ⟨t, rfl⟩ := hb
        refine ⟨1, ?_⟩
        have e : ((chartMon x (restrictChart c') a)⁻¹ * v (c' (.inr ()))) ^ 1 *
            (mseg (joinCoord x z) t / mseg (joinCoord x z) c') =
            (mseg x (restrictChart t) / mseg x (restrictChart c')) *
              ((chartMon x (restrictChart c') a)⁻¹ * v (t (.inr ()))) := by
          rw [hj, hj]
          field_simp
        simp only
        rw [e]
        exact (isIntegral_of_mem (ReciprocityTheory.ChartRestriction.G.Geo.div_mem_chartRing (o := O) _ _ _)).mul (hw _)
      | algebraMap r =>
        exact ⟨0, isIntegral_of_mem (by rw [pow_zero, one_mul]; exact Subalgebra.algebraMap_mem _ r)⟩
      | add b₁ b₂ _ _ h₁ h₂ =>
        obtain ⟨n₁, h₁⟩ := h₁
        obtain ⟨n₂, h₂⟩ := h₂
        refine ⟨n₁ + n₂, ?_⟩
        have h := (((hw (c' (.inr ()))).pow n₂).mul h₁).add (((hw (c' (.inr ()))).pow n₁).mul h₂)
        have e : ∀ u : Ω, u ^ (n₁ + n₂) * (b₁ + b₂) = u ^ n₂ * (u ^ n₁ * b₁) + u ^ n₁ * (u ^ n₂ * b₂) :=
          fun u => by ring
        rw [e]
        exact h
      | mul b₁ b₂ _ _ h₁ h₂ =>
        obtain ⟨n₁, h₁⟩ := h₁
        obtain ⟨n₂, h₂⟩ := h₂
        refine ⟨n₁ + n₂, ?_⟩
        have e : ∀ u : Ω, u ^ (n₁ + n₂) * (b₁ * b₂) = u ^ n₁ * b₁ * (u ^ n₂ * b₂) := fun u => by ring
        rw [e]
        exact h₁.mul h₂
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ModelRefinementExists
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

namespace GlobalTheory.CompanionTheory.Ar.NormalJoin

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) [CharZero O] (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → fnField O x = ⊤ → ∃ (K' : Type) (_ : Fintype K') (_ : DecidableEq K') (ι' : K' → Type) (_ : ∀ k, Fintype (ι' k)) (z : (Σ k, ι' k) → Ω), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z)) d ∧ NormalCharts O (joinCoord x z) := by
  exact @PositivityTheory.Xgn.t_normal_join

end GlobalTheory.CompanionTheory.Ar.NormalJoin
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ModelRefinementExistsStatement
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_refinement_exists : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) [CharZero O] (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → fnField O x = ⊤ → ∃ (K' : Type) (_ : Fintype K') (_ : DecidableEq K') (ι' : K' → Type) (_ : ∀ k, Fintype (ι' k)) (z : (Σ k, ι' k) → Ω), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z)) d ∧ NormalCharts O (joinCoord x z) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.NormalJoin.main | exact GlobalTheory.CompanionTheory.Ar.NormalJoin.main | (intros; apply GlobalTheory.CompanionTheory.Ar.NormalJoin.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeFamilyModelChern
section -- merged from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XFlattenLines
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

namespace PositivityTheory.Xgn.A_flatten_lines

theorem span_line {O Ω : Type} [CommRing O] [Field Ω] [Algebra O Ω] (R R' : Subalgebra O Ω) (hle : R ≤ R')
    {M : ℕ} (v : Fin M → Ω) (m : Ω) (l₀ : Fin M) (h0 : v l₀ ≠ 0) (hq : ∀ l, v l / v l₀ ∈ R') (w : Ω) :
    w ∈ spanOver R' (spanOver R (Set.range fun l => m • v l) : Set Ω) ↔ ∃ r ∈ R', w = r * (m * v l₀) := by
  let L : AddSubgroup Ω :=
    { carrier := {w | ∃ r ∈ R', w = r * (m * v l₀)}
      add_mem' := by
        rintro _ _ ⟨r, hr, rfl⟩ ⟨s, hs, rfl⟩
        exact ⟨r + s, R'.add_mem hr hs, by ring⟩
      zero_mem' := ⟨0, R'.zero_mem, by simp⟩
      neg_mem' := by
        rintro _ ⟨r, hr, rfl⟩
        exact ⟨-r, R'.neg_mem hr, by ring⟩ }
  have hin : spanOver R (Set.range fun l => m • v l) ≤ L := by
    unfold spanOver
    rw [AddSubgroup.closure_le]
    rintro _ ⟨a, ha, e, ⟨l, rfl⟩, rfl⟩
    refine ⟨a * (v l / v l₀), R'.mul_mem (hle ha) (hq l), ?_⟩
    simp only [smul_eq_mul]
    field_simp
  have hout : spanOver R' (spanOver R (Set.range fun l => m • v l) : Set Ω) ≤ L := by
    unfold spanOver
    rw [AddSubgroup.closure_le]
    rintro _ ⟨a, ha, e, he, rfl⟩
    obtain ⟨r, hr, rfl⟩ := hin he
    exact ⟨a * r, R'.mul_mem ha hr, by simp only [smul_eq_mul]; ring⟩
  constructor
  · intro hw
    exact hout hw
  · rintro ⟨r, hr, rfl⟩
    have hm : m • v l₀ ∈ spanOver R (Set.range fun l => m • v l) :=
      AddSubgroup.subset_closure ⟨1, R.one_mem, m • v l₀, ⟨l₀, rfl⟩, by simp⟩
    exact AddSubgroup.subset_closure ⟨r, hr, m • v l₀, hm, by simp⟩

theorem chartMon_join {Ω : Type} [Field Ω] {K K' : Type} [Fintype K] [Fintype K'] [DecidableEq K']
    {ι : K → Type} {ι' : K' → Type} (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω)
    (c : ∀ k : K ⊕ K', Sum.elim ι ι' k) (a : K → ℤ) (j : K') :
    chartMon (joinCoord x z) c (Sum.elim (-a) (Pi.single j 1)) =
      (chartMon x (restrictChart c) a)⁻¹ * z ⟨j, c (.inr j)⟩ := by
  unfold chartMon restrictChart
  rw [Fintype.prod_sum_type]
  simp only [joinCoord, Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, zpow_neg, Finset.prod_inv_distrib]
  congr 1
  rw [Finset.prod_eq_single j]
  · simp
  · intro b _ hb
    simp [Pi.single_apply, hb]
  · intro h
    exact absurd (Finset.mem_univ j) h

end PositivityTheory.Xgn.A_flatten_lines

theorem PositivityTheory.Xgn.t_flatten_lines : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → fnField O x = ⊤ → ∀ (I : Type) [Fintype I] (Γ : I → (∀ k, ι k) → AddSubgroup Ω), (∀ j, IsLatFamily O x (Γ j) ∧ ∀ c, mseg x c ≠ 0 → Γ j c ≠ ⊥ ∧ ∃ S : Finset Ω, Γ j c = spanOver (chartRing O (mseg x) c) (S : Set Ω)) → ∃ (K' : Type) (_ : Fintype K') (_ : DecidableEq K') (ι' : K' → Type) (_ : ∀ k, Fintype (ι' k)) (z : (Σ k, ι' k) → Ω), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z)) d ∧ ∀ j, ∃ a : K ⊕ K' → ℤ, IsLine O (joinCoord x z) 1 a fun c => spanOver (chartRing O (mseg (joinCoord x z)) c) (Γ j (restrictChart c) : Set Ω) := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x d hmod hfn I _ Γ hΓ
  classical
  obtain ⟨_, hx0, _, _⟩ := (PositivityTheory.Xgn.A_join_model.isModelOver_iff x d).mp hmod
  choose c0 hc0 using hx0
  have hm0 : mseg x c0 ≠ 0 := by
    unfold mseg
    exact Finset.prod_ne_zero_iff.mpr fun k _ => hc0 k
  have key : ∀ j, ∃ (a : K → ℤ) (M : ℕ) (v : Fin M → Ω), ∀ c, mseg x c ≠ 0 →
      Γ j c = spanOver (chartRing O (mseg x) c) (Set.range fun l => (chartMon x c a)⁻¹ • v l) := by
    intro j
    obtain ⟨a₁, ha₁⟩ := PositivityTheory.Xgn.t_coherent_gens O Ω K ι x Ω (Γ j) (hΓ j).1
      (fun c hc => ((hΓ j).2 c hc).2)
    obtain ⟨M, v, hv⟩ := ha₁ a₁ le_rfl
    exact ⟨a₁, M, v, hv⟩
  choose a M v hv using key
  have hnz : ∀ j, ∃ l, v j l ≠ 0 := by
    intro j
    by_contra hall
    push_neg at hall
    apply ((hΓ j).2 c0 hm0).1
    rw [hv j c0 hm0, eq_bot_iff]
    unfold spanOver
    rw [AddSubgroup.closure_le]
    rintro _ ⟨r, _, e, ⟨l, rfl⟩, rfl⟩
    simp [hall l]
  let z : (Σ j : I, Fin (M j)) → Ω := fun p => v p.1 p.2
  have hJ := (PositivityTheory.Xgn.t_chart_noeth_frac O Ω K ι x).2.2 I (fun j => Fin (M j)) z
  refine ⟨I, inferInstance, inferInstance, fun j => Fin (M j), fun _ => inferInstance, z, ?_, ?_⟩
  · have hmodJ := PositivityTheory.Xgn.t_join_model O Ω K ι x d 0 hmod I (fun j => Fin (M j)) z hnz
      Fin.elim0 algebraicIndependent_empty_type (fun i => Fin.elim0 i) ?_
    · convert hmodJ using 1
    · intro w _
      have hw : w ∈ fnField O x := by
        rw [hfn]
        exact Subfield.mem_top w
      exact isAlgebraic_algebraMap
        (⟨w, IntermediateField.algebraMap_mem _ (⟨w, hw⟩ : fnField O x)⟩ :
          IntermediateField.adjoin (fnField O x) (Set.range (Fin.elim0 : Fin 0 → Ω)))
  · intro j
    refine ⟨Sum.elim (-a j) (Pi.single j 1), ?_⟩
    intro c hc w
    obtain ⟨hrc, hle⟩ := hJ.2 c hc
    have hmz := PositivityTheory.Xgn.A_chart_noeth_frac.mseg_join x z c
    have hz0 : z ⟨j, c (Sum.inr j)⟩ ≠ 0 := by
      rw [hmz] at hc
      have h2 := right_ne_zero_of_mul hc
      unfold mseg at h2
      exact Finset.prod_ne_zero_iff.mp h2 j (Finset.mem_univ _)
    show w ∈ spanOver (chartRing O (mseg (joinCoord x z)) c) (Γ j (restrictChart c) : Set Ω) ↔ _
    rw [hv j _ hrc, one_mul, PositivityTheory.Xgn.A_flatten_lines.chartMon_join]
    refine PositivityTheory.Xgn.A_flatten_lines.span_line _ _ hle _ _ (c (Sum.inr j)) hz0 ?_ w
    intro l
    have h := PositivityTheory.Xgn.A_chart_noeth_frac.ratio_eq (joinCoord x z) c hc (Sum.inr j) l
    have hmem : mseg (joinCoord x z) (Function.update c (Sum.inr j) l) / mseg (joinCoord x z) c ∈
        chartRing O (mseg (joinCoord x z)) c := Algebra.subset_adjoin ⟨_, rfl⟩
    rw [h] at hmem
    exact hmem
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LineLatticeFamilyModel
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LineLatticeFamilyModel
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

namespace GlobalTheory.CompanionTheory.Ar.FlattenLines

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → fnField O x = ⊤ → ∀ (I : Type) [Fintype I] (Γ : I → (∀ k, ι k) → AddSubgroup Ω), (∀ j, IsLatFamily O x (Γ j) ∧ ∀ c, mseg x c ≠ 0 → Γ j c ≠ ⊥ ∧ ∃ S : Finset Ω, Γ j c = spanOver (chartRing O (mseg x) c) (S : Set Ω)) → ∃ (K' : Type) (_ : Fintype K') (_ : DecidableEq K') (ι' : K' → Type) (_ : ∀ k, Fintype (ι' k)) (z : (Σ k, ι' k) → Ω), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z)) d ∧ ∀ j, ∃ a : K ⊕ K' → ℤ, IsLine O (joinCoord x z) 1 a fun c => spanOver (chartRing O (mseg (joinCoord x z)) c) (Γ j (restrictChart c) : Set Ω) :=
  @PositivityTheory.Xgn.t_flatten_lines

end GlobalTheory.CompanionTheory.Ar.FlattenLines
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LineLatticeFamilyModelStatement
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.line_lattice_family_model : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → fnField O x = ⊤ → ∀ (I : Type) [Fintype I] (Γ : I → (∀ k, ι k) → AddSubgroup Ω), (∀ j, IsLatFamily O x (Γ j) ∧ ∀ c, mseg x c ≠ 0 → Γ j c ≠ ⊥ ∧ ∃ S : Finset Ω, Γ j c = spanOver (chartRing O (mseg x) c) (S : Set Ω)) → ∃ (K' : Type) (_ : Fintype K') (_ : DecidableEq K') (ι' : K' → Type) (_ : ∀ k, Fintype (ι' k)) (z : (Σ k, ι' k) → Ω), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z)) d ∧ ∀ j, ∃ a : K ⊕ K' → ℤ, IsLine O (joinCoord x z) 1 a fun c => spanOver (chartRing O (mseg (joinCoord x z)) c) (Γ j (restrictChart c) : Set Ω) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlattenLines.main | exact GlobalTheory.CompanionTheory.Ar.FlattenLines.main | (intros; apply GlobalTheory.CompanionTheory.Ar.FlattenLines.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeFamilyModelChern
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

namespace GlobalTheory.CompanionTheory.Ar.FamLines

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {V : Type} [AddCommGroup V] [Module Ω V]

theorem exists_finset {R : Subalgebra o Ω} {r : ℕ} {L : AddSubgroup V} (h : LocFree R r L) :
    ∃ S : Finset V, L = spanOver R (S : Set V) := by
  classical
  let L' : Submodule R V := { L with smul_mem' := fun a e he => h.1 a a.2 e he }
  obtain ⟨k, φ, v, hφ, hv⟩ := LocFreeProj.exists_dualBasis (L := L') (r := r) h
  refine ⟨Finset.univ.image fun i => (v i : V), le_antisymm (fun e he => ?_) ?_⟩
  · rw [← hv e]
    · refine sum_mem fun i _ => AddSubgroup.subset_closure ⟨φ i e, hφ i e he, v i, ?_, rfl⟩
      simp
  · refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨a, ha, e, he, rfl⟩
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at he
    obtain ⟨i, rfl⟩ := he
    exact h.1 a ha _ (v i).2

theorem ne_bot {R : Subalgebra o Ω} {L : AddSubgroup V} (h : LocFree R 1 L) : L ≠ ⊥ := by
  obtain ⟨-, k, f, c, -, -, hs, hb⟩ := h
  have hex : ∃ l, f l ≠ 0 := by
    by_contra hn
    push Not at hn
    simp [hn] at hs
  obtain ⟨l, hl⟩ := hex
  obtain ⟨b, hli, -, hb⟩ := hb l
  obtain ⟨m, hm⟩ := (hb (b 0)).2 ⟨fun _ => 1, fun _ => ⟨0, by simp⟩, by simp⟩
  rintro rfl
  exact smul_ne_zero (pow_ne_zero m hl) (hli.ne_zero 0) (AddSubgroup.mem_bot.1 hm)

theorem injective {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω]
    {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {x : (Σ k, ι k) → Ω} {d : ℕ}
    (h : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d) :
    Function.Injective (algebraMap O Ω) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  have h1 : a ∈ (mcIdeal O x).comap (C : O →+* _) := by
    rw [Ideal.mem_comap, mcIdeal, RingHom.mem_ker]
    change GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcMap O x (algebraMap O _ a) = 0
    rw [AlgHom.commutes, MvPolynomial.algebraMap_apply, ha, map_zero]
  rw [h.2.2.1] at h1
  exact h1

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → fnField O x = ⊤ → ∀ {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} [Fintype Sg] {r s : Sg → ℕ} (p : ℕ), p.Prime → ∀ (w : O) (χ : Sg → F → O) (φ : Equiv.Perm Sg) (D : (∀ k, ι k) → LieLatticeData Ω F n Sg r s), IsLatticeFamily O x p w χ φ D → (∀ c, mseg x c ≠ 0 → (D c).Good₁ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a))) → ∃ (K' : Type) (_ : Fintype K') (_ : DecidableEq K') (ι' : K' → Type) (_ : ∀ k, Fintype (ι' k)) (z : (Σ k, ι' k) → Ω), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z)) d ∧ (∀ τ i, ∃ (u : Ω) (a : _ → ℤ), u ≠ 0 ∧ IsLine O (joinCoord x z) u a fun c => (pullFamily O x z D c).xId (fun a => algebraMap O Ω (χ τ a)) i) := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x d hx hfn F _ _ _ n Sg _ r s p hp w χ φ D hD hG
  have hinj := injective hx
  have hchar : ∀ R : Subalgebra O Ω,
      CharData R p (algebraMap O Ω w) (fun τ a => algebraMap O Ω (χ τ a)) := by
    intro R
    obtain ⟨hp0, ⟨u, hu, huw⟩, -, h01, hχ⟩ := hD.char
    refine ⟨?_, R.algebraMap_mem _, ?_, h01, fun τ => ⟨?_, ?_, fun a => R.algebraMap_mem _⟩⟩
    · rw [← map_natCast (algebraMap O Ω)]
      exact fun h => hp0 (hinj (h.trans (map_zero _).symm))
    · obtain ⟨u, rfl⟩ := hu
      refine ⟨algebraMap O Ω (↑u⁻¹ * w ^ (p - 2)), R.algebraMap_mem _, ?_⟩
      rw [← map_mul, ← map_natCast (algebraMap O Ω), mul_assoc, ← pow_succ,
        show p - 2 + 1 = p - 1 by have := hp.two_le; omega, huw, Units.inv_mul_cancel_left]
    · simp [(hχ τ).1]
    · simp [(hχ τ).2]
  have hbc := fun c (hc : mseg x c ≠ 0) =>
    GlobalTheory.T.lattice_good_base_change (D c) (chartRing O (mseg x) c) p _ _ (hchar _) (hD.base c hc) (hG c hc)
  have hfam := (GlobalTheory.T.lattice_family_injective_model_facts O Ω K ι x hinj p hp w χ φ D hD).2
  obtain ⟨K', i1, i2, ι', i3, z, hz, hl⟩ := GlobalTheory.T.line_lattice_family_model O Ω K ι x d hx hfn (Sg × Fin n)
    (fun j c => (D c).xId (fun a => algebraMap O Ω (χ j.1 a)) j.2) fun j =>
      ⟨((hfam j.1).2.1 j.2).1, fun c hc =>
        ⟨ne_bot (((hbc c hc).1 j.1).2.2.2 j.2),
          exists_finset (((hbc c hc).1 j.1).2.2.2 j.2)⟩⟩
  refine ⟨K', i1, i2, ι', i3, z, hz, fun τ i => ?_⟩
  obtain ⟨a, ha⟩ := hl (τ, i)
  refine ⟨1, a, one_ne_zero, fun c hc v => ?_⟩
  obtain ⟨hc', hle⟩ := ((GlobalTheory.T.chart_rings_noetherian_fraction O Ω K ι x).2.2 K' ι' z).2 c hc
  have h := (((hbc _ hc').2 Ω (chartRing O (mseg (joinCoord x z)) c) fun a ha => hle ha).2 τ).2.2 i
  rw [← ha c hc v]
  simp only [Algebra.algebraMap_self, RingHom.id_apply, Set.image_id'] at h
  simp only [pullFamily, h]

end GlobalTheory.CompanionTheory.Ar.FamLines
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeFamilyModelChernStatement
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_family_model_chern : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → fnField O x = ⊤ → ∀ {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} [Fintype Sg] {r s : Sg → ℕ} (p : ℕ), p.Prime → ∀ (w : O) (χ : Sg → F → O) (φ : Equiv.Perm Sg) (D : (∀ k, ι k) → LieLatticeData Ω F n Sg r s), IsLatticeFamily O x p w χ φ D → (∀ c, mseg x c ≠ 0 → (D c).Good₁ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a))) → ∃ (K' : Type) (_ : Fintype K') (_ : DecidableEq K') (ι' : K' → Type) (_ : ∀ k, Fintype (ι' k)) (z : (Σ k, ι' k) → Ω), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z)) d ∧ (∀ τ i, ∃ (u : Ω) (a : _ → ℤ), u ≠ 0 ∧ IsLine O (joinCoord x z) u a fun c => (pullFamily O x z D c).xId (fun a => algebraMap O Ω (χ τ a)) i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FamLines.main | exact GlobalTheory.CompanionTheory.Ar.FamLines.main | (intros; apply GlobalTheory.CompanionTheory.Ar.FamLines.main <;> assumption)
end
end
