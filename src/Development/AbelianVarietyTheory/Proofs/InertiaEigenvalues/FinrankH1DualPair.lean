module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMutuallyDualStableLattices
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1LatticeIndexGrowth
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1ReductionIndexBoundDual

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1LatticeRankGrowth
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteFinrankOfLocalizes
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

set_option autoImplicit false

namespace GlobalTheory.H1Rank

theorem pow_smul_mem_lattice : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (x : A.V), ∃ n : ℕ, ((l : ℕ) : O) ^ n • x ∈ LA.T := by
  intro l _ K LL _ _ _ O _ _ hG A LA x
  obtain ⟨-, -, hmod, htop, hopen⟩ := hG
  haveI := hmod
  haveI := htop
  have hT : IsOpen (LA.T : Set A.V) := GlobalTheory.Cyc.isOpen_of_fg_of_span_eq_top hopen LA.T LA.fg LA.span
  haveI := IsModuleTopology.toContinuousSMul LL A.V
  have h1 : Filter.Tendsto (fun n : ℕ => (l : ℚ_[l]) ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one Padic.norm_p_lt_one
  have h2 : Filter.Tendsto (fun n : ℕ => algebraMap ℚ_[l] LL ((l : ℚ_[l]) ^ n) • x) Filter.atTop (nhds 0) := by
    have := ((GlobalTheory.GoodCoeff.continuous_algebraMap_padic (l := l) (LL := LL)).tendsto 0).comp h1
    rw [map_zero] at this
    simpa using this.smul_const x
  have h3 : ∀ n : ℕ, ((l : ℕ) : O) ^ n • x = algebraMap ℚ_[l] LL ((l : ℚ_[l]) ^ n) • x := by
    intro n
    rw [← algebraMap_smul LL, map_pow, map_pow, map_natCast, map_natCast]
  obtain ⟨n, hn⟩ := (h2.eventually (hT.mem_nhds LA.T.zero_mem)).exists
  exact ⟨n, by rw [h3]; exact hn⟩

end GlobalTheory.H1Rank

namespace GlobalTheory.H1Rank

theorem not_isUnit_l : ∀ (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ¬ IsUnit ((l : ℕ) : O) := by
  intro l _ LL _ _ _ O _ _ hG hu
  obtain ⟨u, hu⟩ := hu
  have hint := ((GlobalTheory.GoodCoeff.good_coeff_integers l LL O hG).1 (algebraMap O LL (↑u⁻¹ : O))).1 ⟨_, rfl⟩
  have hl0 : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hx : algebraMap O LL (↑u⁻¹ : O) = algebraMap ℚ_[l] LL ((l : ℚ_[l])⁻¹) := by
    have h1 : algebraMap O LL (↑u⁻¹ : O) * algebraMap O LL (u : O) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have h2 : algebraMap O LL (u : O) = algebraMap ℚ_[l] LL (l : ℚ_[l]) := by
      rw [hu, map_natCast, map_natCast]
    rw [h2] at h1
    calc algebraMap O LL (↑u⁻¹ : O)
        = algebraMap O LL (↑u⁻¹ : O) * (algebraMap ℚ_[l] LL (l : ℚ_[l]) * algebraMap ℚ_[l] LL ((l : ℚ_[l])⁻¹)) := by
          rw [← map_mul, mul_inv_cancel₀ hl0, map_one, mul_one]
      _ = algebraMap ℚ_[l] LL ((l : ℚ_[l])⁻¹) := by rw [← mul_assoc, h1, one_mul]
  rw [hx] at hint
  obtain ⟨p, hpm, hp⟩ := hint
  have hp' : Polynomial.eval₂ (algebraMap ℤ_[l] ℚ_[l]) ((l : ℚ_[l])⁻¹) p = 0 := by
    apply (algebraMap ℚ_[l] LL).injective
    rw [map_zero, Polynomial.hom_eval₂]
    exact hp
  have hI : IsIntegral ℤ_[l] ((l : ℚ_[l])⁻¹) := ⟨p, hpm, hp'⟩
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 hI
  have h1 : ‖(z : ℚ_[l])‖ ≤ 1 := PadicInt.norm_le_one z
  have h3 : algebraMap ℤ_[l] ℚ_[l] z = (z : ℚ_[l]) := rfl
  rw [← h3, hz, norm_inv, Padic.norm_p, inv_inv] at h1
  have : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  linarith
end GlobalTheory.H1Rank

namespace GlobalTheory.H1Rank

theorem finite_finrank_of_localizes : ∀ (O LL M N : Type) [CommRing O] [IsDomain O] [Field LL] [Algebra O LL] [IsFractionRing O LL] [AddCommGroup M] [Module O M] [Module.Finite O M] [AddCommGroup N] [Module LL N] [Module O N] [IsScalarTower O LL N] (f : M →ₗ[O] N) (t : O), t ≠ 0 → (∀ y : N, ∃ n : ℕ, ∃ x : M, f x = t ^ n • y) → (∀ x : M, f x = 0 → ∃ n : ℕ, t ^ n • x = 0) → Module.Finite LL N ∧ finrank LL N = finrank O M := by
  intro O LL M N _ _ _ _ _ _ _ _ _ _ _ _ f t ht hs hk
  have htn : ∀ n : ℕ, t ^ n ∈ nonZeroDivisors O := fun n => pow_mem (mem_nonZeroDivisors_of_ne_zero ht) n
  haveI : IsLocalizedModule (nonZeroDivisors O) f :=
    { map_units := by
        intro s
        rw [Module.End.isUnit_iff]
        have ha : algebraMap O LL (s : O) ≠ 0 :=
          (map_ne_zero_iff _ (IsFractionRing.injective O LL)).2 (nonZeroDivisors.ne_zero s.2)
        have he : ∀ y : N, (algebraMap O (Module.End O N) (s : O)) y = algebraMap O LL (s : O) • y := fun y => by
          rw [Module.algebraMap_end_apply, algebraMap_smul]
        refine ⟨fun y z h => ?_, fun y => ⟨(algebraMap O LL (s : O))⁻¹ • y, ?_⟩⟩
        · rw [he, he] at h
          exact smul_right_injective N ha h
        · rw [he, smul_smul, mul_inv_cancel₀ ha, one_smul]
      surj := by
        intro y
        obtain ⟨n, x, hx⟩ := hs y
        exact ⟨(x, ⟨t ^ n, htn n⟩), hx.symm⟩
      exists_of_eq := by
        intro x₁ x₂ h
        obtain ⟨n, hn⟩ := hk (x₁ - x₂) (by rw [map_sub, h, sub_self])
        exact ⟨⟨t ^ n, htn n⟩, by rw [Submonoid.smul_def]; rw [smul_sub, sub_eq_zero] at hn; exact hn⟩ }
  refine ⟨Module.Finite.of_isLocalizedModule (nonZeroDivisors O) (Rₚ := LL) f, ?_⟩
  rw [IsLocalization.finrank_eq LL (nonZeroDivisors O) le_rfl, IsLocalizedModule.finrank_eq (nonZeroDivisors O) f le_rfl]
end GlobalTheory.H1Rank

namespace GlobalTheory.H1Rank

theorem pow_smul_mem_B1T : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ), ∀ c ∈ latticeCocycles LA, c ∈ B1 A.ρ → ∃ n : ℕ, ((l : ℕ) : O) ^ n • c ∈ latticeCoboundaries LA := by
  intro l _ K LL _ _ _ O _ _ hG A LA c _ hc
  obtain ⟨x, rfl⟩ := hc
  obtain ⟨n, hn⟩ := pow_smul_mem_lattice l K LL O hG A LA x
  exact ⟨n, _, hn, by rw [LinearMap.map_smul_of_tower]; rfl⟩

theorem pow_smul_mem_Z1T : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ), ∀ c ∈ continuousCocycles A.ρ, ∃ n : ℕ, ((l : ℕ) : O) ^ n • c ∈ latticeCocycles LA := by
  intro l _ K LL _ _ _ O _ _ hG A LA c hc
  haveI : CompactSpace ↥(GK K) := by
    haveI := K.2
    exact isCompact_iff_compactSpace.1 (IntermediateField.fixingSubgroup_isClosed K.1).isCompact
  have hG' := hG
  obtain ⟨-, -, hmod, htop, hopen⟩ := hG'
  haveI := hmod
  haveI := htop
  have hT : IsOpen (LA.T : Set A.V) := GlobalTheory.Cyc.isOpen_of_fg_of_span_eq_top hopen LA.T LA.fg LA.span
  let U : ℕ → Set A.V := fun n => (fun v : A.V => ((l : ℕ) : O) ^ n • v) ⁻¹' (LA.T : Set A.V)
  have hUo : ∀ n, IsOpen (U n) := by
    intro n
    refine hT.preimage ?_
    have : (fun v : A.V => ((l : ℕ) : O) ^ n • v) = fun v : A.V => algebraMap O LL (((l : ℕ) : O) ^ n) • v :=
      funext fun v => (algebraMap_smul LL _ v).symm
    rw [this]
    exact continuous_const_smul _
  have hUm : Monotone U := by
    refine monotone_nat_of_le_succ fun n v hv => ?_
    show ((l : ℕ) : O) ^ (n + 1) • v ∈ LA.T
    rw [pow_succ', mul_smul]
    exact LA.T.smul_mem _ hv
  have hcov : Set.range c ⊆ ⋃ n, U n := fun v _ => Set.mem_iUnion.2 (pow_smul_mem_lattice l K LL O hG A LA v)
  obtain ⟨n, hn⟩ := (isCompact_range hc.1).elim_directed_cover U hUo hcov hUm.directed_le
  refine ⟨n, ⟨(continuousCocycles A.ρ).smul_of_tower_mem _ hc, fun g _ => hn ⟨g, rfl⟩⟩⟩

end GlobalTheory.H1Rank

namespace GlobalTheory.H1Rank
section
variable {l : ℕ} [Fact l.Prime] {K : FinExt l} {LL : Type} [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] {O : Type} [CommRing O] [Algebra O LL]
  {A : GRep ↥(GK K) ℚ_[l] LL O} (LA : Lattice (O := O) A.ρ)

def incl : ↥(latticeCocycles LA) →ₗ[O] ↥(continuousCocycles A.ρ) where
  toFun c := ⟨c, c.2.1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def toH1V : LatticeCohomology LA →ₗ[O] H1V A.ρ :=
  Submodule.liftQ ((latticeCoboundaries LA).comap (latticeCocycles LA).subtype)
    ((((B1 A.ρ).comap (continuousCocycles A.ρ).subtype).mkQ.restrictScalars O).comp (incl LA)) (by
      intro c hc
      obtain ⟨x, -, hx⟩ := hc
      simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
        Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply]
      exact ⟨x, hx⟩)

theorem toH1V_mk (c : ↥(latticeCocycles LA)) :
    toH1V LA (Submodule.Quotient.mk c) = Submodule.Quotient.mk (incl LA c) := rfl
end
end GlobalTheory.H1Rank
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardQuotSpanPowEqCardPowDomain
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardQuotSpanPowEqCardPowDomain
open Module

namespace GlobalTheory

theorem card_quot_span_pow_succ_eq_mul_domain (O : Type) [CommRing O] [IsDomain O] (t : O) (ht : t ≠ 0)
    (r : ℕ) :
    Nat.card (O ⧸ Ideal.span {t ^ (r + 1)}) =
      Nat.card (O ⧸ Ideal.span {t}) * Nat.card (O ⧸ Ideal.span {t ^ r}) := by
  set H := (Ideal.span {t ^ (r + 1)}).toAddSubgroup with hH
  set K := (Ideal.span {t ^ r}).toAddSubgroup with hK
  have hHK : H ≤ K := by
    intro x hx
    simp only [hH, hK, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton] at hx ⊢
    exact (pow_dvd_pow t (Nat.le_succ r)).trans hx
  have e1 : Nat.card (O ⧸ Ideal.span {t ^ (r + 1)}) = H.index := rfl
  have e2 : Nat.card (O ⧸ Ideal.span {t ^ r}) = K.index := rfl
  have e3 : Nat.card (O ⧸ Ideal.span {t}) = (Ideal.span {t}).toAddSubgroup.index := rfl
  rw [e1, e2, e3, ← AddSubgroup.relIndex_mul_index hHK]
  congr 1
  let φ : O →+ K :=
    { toFun := fun x => ⟨t ^ r * x, by
        simp only [hK, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton]
        exact dvd_mul_right _ _⟩
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp [mul_add] }
  have hφ : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    have hy' : y ∈ Ideal.span {t ^ r} := hy
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton.mp hy'
    exact ⟨a, rfl⟩
  have hc : (H.addSubgroupOf K).comap φ = (Ideal.span {t}).toAddSubgroup := by
    ext x
    simp only [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf, hH,
      Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton]
    change t ^ (r + 1) ∣ t ^ r * x ↔ t ∣ x
    rw [pow_succ]
    exact mul_dvd_mul_iff_left (pow_ne_zero r ht)
  rw [AddSubgroup.relIndex, ← hc, AddSubgroup.index_comap_of_surjective _ hφ]

theorem card_quot_span_pow :
    ∀ (O : Type) [CommRing O] [IsDomain O] (t : O), t ≠ 0 → Finite (O ⧸ Ideal.span {t}) →
      ∀ r : ℕ, Nat.card (O ⧸ Ideal.span {t ^ r}) = Nat.card (O ⧸ Ideal.span {t}) ^ r := by
  intro O _ _ t ht _ r
  induction r with
  | zero =>
    rw [pow_zero, pow_zero, Ideal.span_singleton_one]
    exact Nat.card_unique
  | succ r ih =>
    rw [card_quot_span_pow_succ_eq_mul_domain O t ht r, ih, pow_succ, mul_comm]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardQuotSpanPowEqCardPowDomainStatement
open Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_quot_span_pow_eq_card_pow_domain : ∀ (O : Type) [CommRing O] [IsDomain O] (t : O), t ≠ 0 → Finite (O ⧸ Ideal.span {t}) → ∀ r : ℕ, Nat.card (O ⧸ Ideal.span {t ^ r}) = Nat.card (O ⧸ Ideal.span {t}) ^ r := by
  first | exact @GlobalTheory.card_quot_span_pow | exact GlobalTheory.card_quot_span_pow | (intros; apply GlobalTheory.card_quot_span_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1LatticeRankGrowth
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

set_option autoImplicit false

namespace GlobalTheory.H1Rank

theorem growth_H1T_dim_H1V : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ), Module.Finite O (LatticeCohomology LA) → Module.Finite LL (H1V A.ρ) ∧ ∃ C : ℕ, 0 < C ∧ ∀ r : ℕ, Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * finrank LL (H1V A.ρ)) ≤ Nat.card (LatticeCohomology LA ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O (LatticeCohomology LA))) ∧ Nat.card (LatticeCohomology LA ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O (LatticeCohomology LA))) ≤ C * Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * finrank LL (H1V A.ρ)) := by
  intro l _ K LL _ _ _ O _ _ hG A LA hfin
  have hG' := hG
  obtain ⟨⟨hD, hDVR, hFr⟩, -, -, -, -⟩ := hG'
  haveI := hD
  haveI := hDVR
  haveI := hFr
  have hl0 : ((l : ℕ) : O) ≠ 0 := by
    intro h
    have h1 : algebraMap O LL ((l : ℕ) : O) = 0 := by rw [h, map_zero]
    rw [map_natCast] at h1
    have h2 : ((l : ℕ) : LL) = algebraMap ℚ_[l] LL (l : ℚ_[l]) := by rw [map_natCast]
    rw [h2] at h1
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) ((map_eq_zero_iff _ (algebraMap ℚ_[l] LL).injective).1 h1)
  have hfq : ∀ r : ℕ, Finite (O ⧸ Ideal.span {((l : ℕ) : O) ^ r}) :=
    (GlobalTheory.GoodCoeff.good_coeff_integers l LL O hG).2.2.1
  have hfq1 : Finite (O ⧸ Ideal.span {((l : ℕ) : O)}) := by simpa using hfq 1
  have hsurj : ∀ y : H1V A.ρ, ∃ n : ℕ, ∃ x : LatticeCohomology LA, toH1V LA x = ((l : ℕ) : O) ^ n • y := by
    intro y
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨n, hn⟩ := pow_smul_mem_Z1T l K LL O hG A LA c.1 c.2
    refine ⟨n, Submodule.Quotient.mk ⟨_, hn⟩, ?_⟩
    rw [toH1V_mk]
    rfl
  have hker : ∀ x : LatticeCohomology LA, toH1V LA x = 0 → ∃ n : ℕ, ((l : ℕ) : O) ^ n • x = 0 := by
    intro x hx
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [toH1V_mk, Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨n, hn⟩ := pow_smul_mem_B1T l K LL O hG A LA c.1 c.2 hx
    refine ⟨n, ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact hn
  obtain ⟨hF, hr⟩ := finite_finrank_of_localizes O LL (LatticeCohomology LA) (H1V A.ρ) (toH1V LA) _ hl0 hsurj hker
  refine ⟨hF, ?_⟩
  rw [hr]
  obtain ⟨C, hC, hb⟩ := GlobalTheory.T.card_quot_pow_smul_bounds_dvr_fg_module O (LatticeCohomology LA) _ hl0 (not_isUnit_l l LL O hG) hfq
  have e2 : ∀ r : ℕ, Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * finrank O (LatticeCohomology LA)) = Nat.card (O ⧸ Ideal.span {((l : ℕ) : O) ^ r}) ^ finrank O (LatticeCohomology LA) := by
    intro r
    rw [GlobalTheory.T.card_quot_span_pow_eq_card_pow_domain O _ hl0 hfq1 r, pow_mul]
  refine ⟨C, hC, fun r => ⟨?_, ?_⟩⟩
  · exact (e2 r).trans_le (hb r).1
  · exact (hb r).2.trans_eq (congrArg (C * ·) (e2 r).symm)

end GlobalTheory.H1Rank
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1LatticeRankGrowthStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.H1_lattice_rank_growth_of_goodO : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ), Module.Finite O (LatticeCohomology LA) → Module.Finite LL (H1V A.ρ) ∧ ∃ C : ℕ, 0 < C ∧ ∀ r : ℕ, Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * finrank LL (H1V A.ρ)) ≤ Nat.card (LatticeCohomology LA ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O (LatticeCohomology LA))) ∧ Nat.card (LatticeCohomology LA ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O (LatticeCohomology LA))) ≤ C * Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * finrank LL (H1V A.ρ)) := by
  first | exact @GlobalTheory.H1Rank.growth_H1T_dim_H1V | exact GlobalTheory.H1Rank.growth_H1T_dim_H1V | (intros; apply GlobalTheory.H1Rank.growth_H1T_dim_H1V <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GrowthGaloisInvariantsModPrimePowerLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinsetFixedMemInvariants
namespace GlobalTheory.FixedFinsetInvariants

theorem exists_finset_fixed_mem_invariants {G LL V : Type} [Group G] [Field LL] [AddCommGroup V]
    [Module LL V] [FiniteDimensional LL V] (ρ : Representation LL G V) :
    ∃ s : Finset G, ∀ v : V, (∀ g ∈ s, ρ g v = v) → v ∈ Formalism.WeaklyAdmissibleFiltrations.H0V ρ := by
  classical
  let F : Finset G → Submodule LL V := fun s => ⨅ g ∈ s, LinearMap.ker (ρ g - LinearMap.id)
  have hF : ∀ (s : Finset G) (v : V), v ∈ F s ↔ ∀ g ∈ s, ρ g v = v := by
    intro s v
    simp only [F, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero]
  obtain ⟨_, ⟨s, rfl⟩, hmin⟩ :=
    (wellFounded_lt (α := Submodule LL V)).has_min (Set.range F) ⟨F ∅, ∅, rfl⟩
  refine ⟨s, fun v hv => ?_⟩
  unfold Formalism.WeaklyAdmissibleFiltrations.H0V
  rw [Submodule.mem_iInf]
  intro g
  have hle : F (insert g s) ≤ F s := by
    intro w hw
    rw [hF] at hw ⊢
    exact fun h hh => hw h (Finset.mem_insert_of_mem hh)
  have heq : F (insert g s) = F s := by
    by_contra hne
    exact hmin _ ⟨insert g s, rfl⟩ (lt_of_le_of_ne hle hne)
  have hv' : v ∈ F (insert g s) := heq ▸ (hF s v).2 hv
  have hg := (hF _ v).1 hv' g (Finset.mem_insert_self g s)
  simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  exact hg

end GlobalTheory.FixedFinsetInvariants
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsTail
namespace GlobalTheory.NonzeroScalarMembership

theorem exists_ne_zero_smul_mem {O LL V : Type} [CommRing O] [IsDomain O] [Field LL]
    [Algebra O LL] [IsFractionRing O LL] [AddCommGroup V] [Module LL V] [Module O V]
    [IsScalarTower O LL V] (T : Submodule O V)
    (hT : Submodule.span LL (↑T : Set V) = ⊤) (x : V) :
    ∃ d : O, d ≠ 0 ∧ d • x ∈ T := by
  have hx : x ∈ Submodule.span LL (↑T : Set V) := hT ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine T.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact T.smul_mem b hay
    · rw [mul_smul]
      exact T.smul_mem a hbz
  | smul c y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨⟨p, q⟩, hpq⟩ := IsLocalization.surj (nonZeroDivisors O) c
    have hq : (q : O) ≠ 0 := nonZeroDivisors.coe_ne_zero q
    refine ⟨q * a, mul_ne_zero hq ha, ?_⟩
    have h : ((q : O) * a) • c • y = p • a • y := by
      have h1 : (q : O) • c • y = p • y := by
        rw [← algebraMap_smul LL (q : O), smul_smul, mul_comm, hpq, algebraMap_smul]
      rw [mul_comm, mul_smul, h1, smul_comm]
    rw [h]
    exact T.smul_mem p hay

end GlobalTheory.NonzeroScalarMembership
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GrowthGaloisInvariantsModPrimePowerLattice
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.GrowthOfInvariants

open Pointwise

theorem card_quot_smul_top_of_basis {O M ι : Type} [CommRing O] [AddCommGroup M] [Module O M]
    [Fintype ι] (b : Basis ι O M) (I : Ideal O) :
    Nat.card (M ⧸ I • (⊤ : Submodule O M)) = Nat.card (O ⧸ I) ^ Fintype.card ι := by
  rw [← Nat.card_congr ((quotTensorEquivQuotSMul M I).toEquiv),
    Nat.card_congr (b.baseChange (O ⧸ I)).equivFun.toEquiv, Nat.card_fun, Nat.card_eq_fintype_card (α := ι)]

theorem card_quot_span_pow {O : Type} [CommRing O] [IsDomain O] (a : O) (ha : a ≠ 0) (r : ℕ) :
    Nat.card (O ⧸ Ideal.span {a ^ r}) = Nat.card (O ⧸ Ideal.span {a}) ^ r := by
  induction r with
  | zero =>
    rw [pow_zero, pow_zero, Ideal.span_singleton_one]
    exact Nat.card_unique
  | succ r ih =>
    let f : O →ₗ[O] O ⧸ Ideal.span {a ^ (r + 1)} :=
      (Ideal.span {a ^ (r + 1)}).mkQ ∘ₗ LinearMap.mulLeft O (a ^ r)
    have hker : LinearMap.ker f = Ideal.span {a} := by
      ext x
      simp only [f, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero, LinearMap.mulLeft_apply, Ideal.mem_span_singleton]
      rw [pow_succ]
      exact mul_dvd_mul_iff_left (pow_ne_zero r ha)
    have hrange : LinearMap.range f = Submodule.map (Ideal.span {a ^ (r + 1)}).mkQ (Ideal.span {a ^ r}) := by
      ext y
      simp only [f, LinearMap.mem_range, LinearMap.comp_apply, LinearMap.mulLeft_apply,
        Submodule.mem_map, Ideal.mem_span_singleton']
      constructor
      · rintro ⟨x, rfl⟩; exact ⟨a ^ r * x, ⟨x, mul_comm _ _⟩, rfl⟩
      · rintro ⟨z, ⟨x, rfl⟩, rfl⟩; exact ⟨x, by rw [mul_comm]⟩
    have hle : Ideal.span {a ^ (r + 1)} ≤ Ideal.span {a ^ r} := by
      rw [Ideal.span_singleton_le_span_singleton, pow_succ]; exact dvd_mul_right _ _
    have h1 := Submodule.card_eq_card_quotient_mul_card (LinearMap.range f)
    have h2 : Nat.card (LinearMap.range f) = Nat.card (O ⧸ Ideal.span {a}) := by
      rw [← hker]; exact (Nat.card_congr f.quotKerEquivRange.toEquiv).symm
    have h3 : Nat.card ((O ⧸ Ideal.span {a ^ (r + 1)}) ⧸ LinearMap.range f) =
        Nat.card (O ⧸ Ideal.span {a ^ r}) := by
      rw [hrange]
      exact Nat.card_congr (Submodule.quotientQuotientEquivQuotient _ _ hle).toEquiv
    rw [h1, h2, h3, ih, pow_succ, mul_comm]

theorem exists_finset_fixed {G LL V : Type} [Group G] [Field LL] [AddCommGroup V] [Module LL V]
    [FiniteDimensional LL V] (ρ : Representation LL G V) :
    ∃ s : Finset G, ∀ v : V, (∀ g ∈ s, ρ g v = v) → v ∈ H0V ρ := by
  first
  | (rename_i h_3 h_4 h_5 h_6 h_7; revert G LL V h_3 h_4 h_5 h_6 h_7 ρ; exact @_root_.GlobalTheory.FixedFinsetInvariants.exists_finset_fixed_mem_invariants)
  | exact @_root_.GlobalTheory.FixedFinsetInvariants.exists_finset_fixed_mem_invariants
  | exact _root_.GlobalTheory.FixedFinsetInvariants.exists_finset_fixed_mem_invariants
  | (apply _root_.GlobalTheory.FixedFinsetInvariants.exists_finset_fixed_mem_invariants <;> assumption)
  | (intros; apply _root_.GlobalTheory.FixedFinsetInvariants.exists_finset_fixed_mem_invariants <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FixedFinsetInvariants.exists_finset_fixed_mem_invariants <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FixedFinsetInvariants.exists_finset_fixed_mem_invariants ..)

theorem exists_artinRees_pow {O M P : Type} [CommRing O] [IsNoetherianRing O] [AddCommGroup M]
    [Module O M] [AddCommGroup P] [Module O P] [Module.Finite O P] (φ : M →ₗ[O] P) (a : O) :
    ∃ c : ℕ, ∀ r, c ≤ r → ∀ x : M, φ x ∈ a ^ r • (⊤ : Submodule O P) →
      ∃ y : M, φ (x - a ^ (r - c) • y) = 0 := by
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul (Ideal.span {a}) (LinearMap.range φ)
  refine ⟨c, fun r hr x hx => ?_⟩
  have h1 : φ x ∈ Ideal.span {a} ^ r • (⊤ : Submodule O P) ⊓ LinearMap.range φ := by
    refine ⟨?_, LinearMap.mem_range_self φ x⟩
    rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul]; exact hx
  rw [hc r hr] at h1
  have h2 : φ x ∈ a ^ (r - c) • LinearMap.range φ := by
    rw [← Submodule.ideal_span_singleton_smul, ← Ideal.span_singleton_pow]
    exact Submodule.smul_mono le_rfl inf_le_right h1
  obtain ⟨z, ⟨y, rfl⟩, hz⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 h2
  exact ⟨y, by rw [map_sub, map_smul, hz, sub_self]⟩

end GlobalTheory.GrowthOfInvariants

namespace GlobalTheory.GrowthOfInvariants

open Pointwise

theorem exists_smul_mem {O LL V : Type} [CommRing O] [IsDomain O] [Field LL] [Algebra O LL]
    [IsFractionRing O LL] [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    (T : Submodule O V) (hspan : Submodule.span LL (T : Set V) = ⊤) (x : V) :
    ∃ d : O, d ≠ 0 ∧ d • x ∈ T := by
  first
  | (rename_i h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11; revert O LL V h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 T hspan x; exact @_root_.GlobalTheory.NonzeroScalarMembership.exists_ne_zero_smul_mem)
  | exact @_root_.GlobalTheory.NonzeroScalarMembership.exists_ne_zero_smul_mem
  | exact _root_.GlobalTheory.NonzeroScalarMembership.exists_ne_zero_smul_mem
  | (apply _root_.GlobalTheory.NonzeroScalarMembership.exists_ne_zero_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.NonzeroScalarMembership.exists_ne_zero_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NonzeroScalarMembership.exists_ne_zero_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NonzeroScalarMembership.exists_ne_zero_smul_mem ..)

theorem exists_basis_comap {O LL V : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
    [Field LL] [Algebra O LL] [IsFractionRing O LL] [AddCommGroup V] [Module LL V] [Module O V]
    [IsScalarTower O LL V] (T : Submodule O V) [Module.Free O T] [Module.Finite O T]
    (hspan : Submodule.span LL (T : Set V) = ⊤) (W : Submodule LL V) :
    Nonempty (Basis (Fin (finrank LL W)) O ↥((W.restrictScalars O).comap T.subtype)) := by
  set T₀ := (W.restrictScalars O).comap T.subtype
  obtain ⟨n, b0⟩ := Submodule.basisOfPid (Module.Free.chooseBasis O T) T₀
  let ι : T₀ →ₗ[O] V := T.subtype ∘ₗ T₀.subtype
  have hι : Function.Injective ι := T.injective_subtype.comp T₀.injective_subtype
  let v : Fin n → V := fun i => ι (b0 i)
  have hvW : ∀ i, v i ∈ W := fun i => (b0 i).2
  have hliO : LinearIndependent O v := b0.linearIndependent.map' ι (LinearMap.ker_eq_bot.2 hι)
  have hli : LinearIndependent LL v := (LinearIndependent.iff_fractionRing O LL).1 hliO
  have hspanW : Submodule.span LL (Set.range v) = W := by
    apply le_antisymm
    · rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩; exact hvW i
    · intro x hx
      obtain ⟨d, hd, hdx⟩ := exists_smul_mem T hspan x
      have hdxW : d • x ∈ W := by rw [← algebraMap_smul LL]; exact W.smul_mem _ hx
      let t0 : T₀ := ⟨⟨d • x, hdx⟩, hdxW⟩
      have hmem : d • x ∈ Submodule.span O (Set.range v) := by
        have ht : ι t0 = d • x := rfl
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← ht, ← b0.sum_repr t0, map_sum]
        exact Submodule.sum_mem _ fun i _ => by
          rw [map_smul]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      have hmemLL : d • x ∈ Submodule.span LL (Set.range v) :=
        Submodule.span_le_restrictScalars O LL _ hmem
      have hd' : algebraMap O LL d ≠ 0 :=
        IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hd)
      have hx' : x = (algebraMap O LL d)⁻¹ • (d • x) := by
        rw [← algebraMap_smul LL d x, smul_smul, inv_mul_cancel₀ hd', one_smul]
      rw [hx']; exact Submodule.smul_mem _ _ hmemLL
  have hrank : finrank LL W = n := by
    rw [← hspanW, finrank_span_eq_card hli, Fintype.card_fin]
  exact ⟨b0.reindex (finCongr hrank.symm)⟩

end GlobalTheory.GrowthOfInvariants

namespace GlobalTheory.GrowthOfInvariants

theorem exists_fin_fixed {G LL V : Type} [Group G] [Field LL] [AddCommGroup V] [Module LL V]
    [FiniteDimensional LL V] (ρ : Representation LL G V) :
    ∃ (n : ℕ) (g : Fin n → G), ∀ v : V, (∀ i, ρ (g i) v = v) → v ∈ H0V ρ := by
  obtain ⟨s, hs⟩ := exists_finset_fixed ρ
  refine ⟨s.card, fun i => (s.equivFin.symm i).1, fun v hv => hs v fun g hg => ?_⟩
  have := hv (s.equivFin ⟨g, hg⟩)
  simpa using this

end GlobalTheory.GrowthOfInvariants

namespace GlobalTheory.GrowthOfInvariants

open Pointwise

theorem growth_core {G LL O V : Type} [Group G] [Field LL] [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra O LL] [IsFractionRing O LL] [AddCommGroup V]
    [Module LL V] [Module O V] [IsScalarTower O LL V] [FiniteDimensional LL V]
    (ρ : Representation LL G V) (LA : Lattice (O := O) ρ) (a : O) (ha0 : a ≠ 0)
    (hfinq : ∀ n : ℕ, Finite (O ⧸ Ideal.span {a ^ n})) :
    ∃ C : ℕ, 0 < C ∧ ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {a ^ r} • ⊤ : Submodule O ↥LA.T)),
      Nat.card (O ⧸ Ideal.span {a}) ^ (r * finrank LL ↥(H0V ρ)) ≤
        Nat.card {x : ↥LA.T ⧸ (Ideal.span {a ^ r} • ⊤ : Submodule O ↥LA.T) //
          ∀ g, actQ LA _ hI g x = x} ∧
      Nat.card {x : ↥LA.T ⧸ (Ideal.span {a ^ r} • ⊤ : Submodule O ↥LA.T) //
          ∀ g, actQ LA _ hI g x = x} ≤
        C * Nat.card (O ⧸ Ideal.span {a}) ^ (r * finrank LL ↥(H0V ρ)) := by
  haveI : Module.Free O LA.T := LA.free
  haveI : Module.Finite O LA.T := Module.Finite.iff_fg.2 LA.fg
  set T₀ : Submodule O LA.T := ((H0V ρ).restrictScalars O).comap LA.T.subtype with hT₀
  have hb := exists_basis_comap LA.T LA.span (H0V ρ)
  rcases hb with ⟨b0⟩
  have hH0 : ∀ v : V, v ∈ H0V ρ ↔ ∀ g, ρ g v = v := by
    intro v
    simp only [H0V, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero]
  have hsat : ∀ n (v : V), a ^ n • v ∈ H0V ρ → v ∈ H0V ρ := by
    intro n v hv
    have hne : algebraMap O LL (a ^ n) ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero (pow_ne_zero n ha0))
    rw [← algebraMap_smul LL] at hv
    exact (Submodule.smul_mem_iff _ hne).1 hv
  have hposO : ∀ n, 0 < Nat.card (O ⧸ Ideal.span {a ^ n}) := fun n => by
    haveI := hfinq n; exact Nat.card_pos
  have hqpos : 0 < Nat.card (O ⧸ Ideal.span {a}) := by have := hposO 1; rwa [pow_one] at this
  have hcardT : ∀ n, Nat.card (LA.T ⧸ (Ideal.span {a ^ n} • ⊤ : Submodule O LA.T)) =
      Nat.card (O ⧸ Ideal.span {a ^ n}) ^ Fintype.card (Module.Free.ChooseBasisIndex O LA.T) :=
    fun n => card_quot_smul_top_of_basis (Module.Free.chooseBasis O LA.T) _
  have hcard0 : ∀ n, Nat.card (T₀ ⧸ (Ideal.span {a ^ n} • ⊤ : Submodule O T₀)) =
      Nat.card (O ⧸ Ideal.span {a}) ^ (n * finrank LL ↥(H0V ρ)) := by
    intro n
    rw [card_quot_smul_top_of_basis b0, card_quot_span_pow a ha0, Fintype.card_fin, ← pow_mul]
  have hfinT : ∀ n, Finite (LA.T ⧸ (Ideal.span {a ^ n} • ⊤ : Submodule O LA.T)) := fun n =>
    Nat.finite_of_card_ne_zero (by rw [hcardT]; exact pow_ne_zero _ (hposO n).ne')
  have hfin0 : ∀ n, Finite (T₀ ⧸ (Ideal.span {a ^ n} • ⊤ : Submodule O T₀)) := fun n =>
    Nat.finite_of_card_ne_zero (by rw [hcard0]; exact pow_ne_zero _ hqpos.ne')
  have memI : ∀ n (x : LA.T), x ∈ (Ideal.span {a ^ n} • ⊤ : Submodule O LA.T) ↔
      ∃ y : LA.T, a ^ n • y = x := by
    intro n x
    rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
    simp

  have hs0 := exists_fin_fixed ρ
  rcases hs0 with ⟨k, gs, hs⟩
  let Φ : LA.T →ₗ[O] (Fin k → LA.T) := LinearMap.pi fun i => actT LA (gs i) - LinearMap.id
  have hc0 := exists_artinRees_pow (O := O) (M := LA.T) (P := Fin k → LA.T) Φ a
  rcases hc0 with ⟨c, hc⟩
  haveI := hfinT c
  refine ⟨Nat.card (LA.T ⧸ (Ideal.span {a ^ c} • ⊤ : Submodule O LA.T)), Nat.card_pos, ?_⟩
  intro r hI
  haveI := hfinT r
  haveI := hfin0 r
  let Ir : Submodule O LA.T := Ideal.span {a ^ r} • ⊤
  let I0 : Submodule O T₀ := Ideal.span {a ^ r} • ⊤
  let Jc : Submodule O LA.T := Ideal.span {a ^ c} • ⊤
  let f1 : T₀ →ₗ[O] LA.T ⧸ Ir := Ir.mkQ ∘ₗ T₀.subtype
  have hf1 : I0 ≤ LinearMap.ker f1 := by
    refine Submodule.smul_le.2 fun b hb t _ => ?_
    simp only [f1, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, Submodule.coe_subtype, Submodule.coe_smul]
    exact Submodule.smul_mem_smul hb Submodule.mem_top
  let L0 := I0.liftQ f1 hf1
  have hL0 : ∀ t : T₀, L0 (Submodule.Quotient.mk t) = Submodule.Quotient.mk (t : LA.T) := fun t => rfl
  have hactmk : ∀ g (x : LA.T), actQ LA Ir hI g (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (actT LA g x) := fun g x => rfl
  have hfix0 : ∀ (t : T₀) g, actT LA g (t : LA.T) = t := by
    intro t g
    apply Subtype.ext
    exact (hH0 _).1 t.2 g
  constructor
  ·
    have hinv : ∀ z, ∀ g, actQ LA Ir hI g (L0 z) = L0 z := by
      intro z g
      obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective I0 z
      rw [hL0, hactmk, hfix0]
    have hinj : Function.Injective L0 := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro z hz
      obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective I0 z
      rw [hL0, Submodule.Quotient.mk_eq_zero] at hz
      obtain ⟨y, hy⟩ := (memI r _).1 hz
      have hyT : (y : V) ∈ H0V ρ := by
        apply hsat r
        have : ((a ^ r • y : LA.T) : V) = ((t : LA.T) : V) := by rw [hy]
        rw [← Submodule.coe_smul]
        rw [this]; exact t.2
      rw [Submodule.Quotient.mk_eq_zero]
      have ht : t = a ^ r • (⟨y, hyT⟩ : T₀) := Subtype.ext hy.symm
      rw [ht]
      exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
    rw [← hcard0 r]
    exact Nat.card_le_card_of_injective (fun z => ⟨L0 z, hinv z⟩)
      (fun z1 z2 h12 => hinj (congrArg Subtype.val h12))
  ·
    let f2 : LA.T →ₗ[O] LA.T ⧸ Ir := Ir.mkQ ∘ₗ (a ^ (r - c) • LinearMap.id)
    have hf2 : Jc ≤ LinearMap.ker f2 := by
      refine Submodule.smul_le.2 fun b hb y _ => ?_
      obtain ⟨e, rfl⟩ := Ideal.mem_span_singleton'.1 hb
      simp only [f2, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero, LinearMap.smul_apply, LinearMap.id_apply]
      have hk : r - c + c = r + (r - c + c - r) := by omega
      have : a ^ (r - c) • (e * a ^ c) • y = a ^ r • ((e * a ^ (r - c + c - r)) • y) := by
        have hp : a ^ (r - c) * a ^ c = a ^ r * a ^ (r - c + c - r) := by
          rw [← pow_add, ← pow_add, ← hk]
        rw [smul_smul, smul_smul]
        congr 1
        linear_combination e * hp
      rw [this]
      exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
    let F := L0.coprod (Jc.liftQ f2 hf2)
    have hsurj : ∀ x : {x : LA.T ⧸ Ir // ∀ g, actQ LA Ir hI g x = x}, ∃ d, F d = x.1 := by
      rintro ⟨x, hx⟩
      obtain ⟨x0, rfl⟩ := Submodule.Quotient.mk_surjective Ir x
      have hdiv : ∀ g, ∃ y : LA.T, a ^ r • y = actT LA g x0 - x0 := by
        intro g
        have := hx g
        rw [hactmk, Submodule.Quotient.eq] at this
        exact (memI r _).1 this
      choose y hy using hdiv
      have hΦ : Φ x0 ∈ a ^ r • (⊤ : Submodule O (Fin k → LA.T)) := by
        rw [Submodule.mem_smul_pointwise_iff_exists]
        refine ⟨fun i => y (gs i), Submodule.mem_top, funext fun i => ?_⟩
        simp only [Φ, Pi.smul_apply, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply, hy]
      by_cases hrc : c ≤ r
      · obtain ⟨z, hz⟩ := hc r hrc x0 hΦ
        have ht : ((x0 - a ^ (r - c) • z : LA.T) : V) ∈ H0V ρ := by
          refine hs _ fun i => ?_
          have h1 := congrFun hz i
          simp only [Φ, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply, Pi.zero_apply,
            sub_eq_zero] at h1
          exact congrArg Subtype.val h1
        refine ⟨(Submodule.Quotient.mk ⟨x0 - a ^ (r - c) • z, ht⟩, Submodule.Quotient.mk z), ?_⟩
        simp only [F, LinearMap.coprod_apply, hL0, Submodule.liftQ_apply, f2, LinearMap.comp_apply,
          Submodule.mkQ_apply, LinearMap.smul_apply, LinearMap.id_apply]
        rw [← Submodule.Quotient.mk_add, sub_add_cancel]
      · have h0 : r - c = 0 := by omega
        refine ⟨(0, Submodule.Quotient.mk x0), ?_⟩
        simp only [F, LinearMap.coprod_apply, map_zero, zero_add, Submodule.liftQ_apply, f2,
          LinearMap.comp_apply, Submodule.mkQ_apply, LinearMap.smul_apply, LinearMap.id_apply, h0,
          pow_zero, one_smul]
    choose σ hσ using hsurj
    have hσinj : Function.Injective σ := fun x y hxy =>
      Subtype.ext (by rw [← hσ x, ← hσ y, hxy])
    calc _ ≤ Nat.card ((T₀ ⧸ I0) × (LA.T ⧸ Jc)) := Nat.card_le_card_of_injective σ hσinj
      _ = _ := by rw [Nat.card_prod, hcard0, mul_comm]

end GlobalTheory.GrowthOfInvariants

namespace GlobalTheory.GrowthOfInvariants

theorem growth_galois_invariants_mod_prime_power_lattice_alt : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ), ∃ C : ℕ, 0 < C ∧ ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)), Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * finrank LL ↥(H0V A.ρ)) ≤ Nat.card {x : ↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T) // ∀ g, actQ LA _ hI g x = x} ∧ Nat.card {x : ↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T) // ∀ g, actQ LA _ hI g x = x} ≤ C * Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * finrank LL ↥(H0V A.ρ)) := by
  intro l _ K LL _ _ _ O _ _ hG A LA
  obtain ⟨-, -, hfinq, -⟩ := GlobalTheory.GoodCoeff.good_coeff_integers l LL O hG
  obtain ⟨⟨hD, hDVR, hFr⟩, -, -, -, -⟩ := hG
  haveI := hD; haveI := hDVR; haveI := hFr
  have ha0 : ((l : ℕ) : O) ≠ 0 := by
    intro h
    have h1 : algebraMap O LL ((l : ℕ) : O) = ((l : ℕ) : LL) := map_natCast _ _
    rw [h, map_zero] at h1
    have h2 : algebraMap ℚ_[l] LL ((l : ℕ) : ℚ_[l]) = 0 := by rw [map_natCast]; exact h1.symm
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
      ((map_eq_zero_iff _ (algebraMap ℚ_[l] LL).injective).1 h2)
  exact growth_core A.ρ LA _ ha0 hfinq

end GlobalTheory.GrowthOfInvariants
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GrowthGaloisInvariantsModPrimePowerLatticeStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.growth_galois_invariants_mod_prime_power_lattice : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ), ∃ C : ℕ, 0 < C ∧ ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)), Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * finrank LL ↥(H0V A.ρ)) ≤ Nat.card {x : ↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T) // ∀ g, actQ LA _ hI g x = x} ∧ Nat.card {x : ↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T) // ∀ g, actQ LA _ hI g x = x} ≤ C * Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * finrank LL ↥(H0V A.ρ)) := by
  first | exact @GlobalTheory.GrowthOfInvariants.growth_galois_invariants_mod_prime_power_lattice_alt | exact GlobalTheory.GrowthOfInvariants.growth_galois_invariants_mod_prime_power_lattice_alt | (intros; apply GlobalTheory.GrowthOfInvariants.growth_galois_invariants_mod_prime_power_lattice_alt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankH1DualPair
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.EulerCharH1

theorem le_of_pow_le {q a b C : ℕ} (hq : 2 ≤ q) (h : ∀ r : ℕ, q ^ (r * a) ≤ C * q ^ (r * b)) :
    a ≤ b := by
  by_contra hab
  push_neg at hab
  have key : ∀ r : ℕ, q ^ r ≤ C := by
    intro r
    have h1 := h r
    have hpos : 0 < q ^ (r * b) := pow_pos (by omega) _
    have : q ^ (r * a) ≥ q ^ (r * b) * q ^ r := by
      rw [← pow_add]
      apply Nat.pow_le_pow_right (by omega)
      nlinarith
    have : q ^ (r * b) * q ^ r ≤ C * q ^ (r * b) := le_trans this h1
    rw [mul_comm (q ^ (r * b))] at this
    exact Nat.le_of_mul_le_mul_right this hpos
  have h2 := key C
  have h3 : C < 2 ^ C := Nat.lt_two_pow_self
  have h4 : 2 ^ C ≤ q ^ C := Nat.pow_le_pow_left hq C
  omega

theorem stableSub_span_smul {G LL O V : Type} [Group G] [Field LL] [CommRing O] [Algebra O LL]
    [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    {ρ : Representation LL G V} (L : Lattice (O := O) ρ) (c : O) :
    StableSub L (Ideal.span {c} • ⊤ : Submodule O ↥L.T) := by
  intro g x hx
  rw [Submodule.ideal_span_singleton_smul] at hx ⊢
  obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
  exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨actT L g y, Submodule.mem_top, (map_smul _ _ _).symm⟩

end GlobalTheory.EulerCharH1

namespace GlobalTheory.EulerCharH1

theorem natCast_not_isUnit (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL]
    (O : Type) [CommRing O] [Algebra O LL]
    (hint : ∀ x : LL, x ∈ Set.range (algebraMap O LL) ↔
      RingHom.IsIntegralElem ((algebraMap ℚ_[l] LL).comp (algebraMap ℤ_[l] ℚ_[l])) x) :
    ¬ IsUnit ((l : ℕ) : O) := by
  rintro ⟨u, hu⟩
  have hl0 : ((l : ℕ) : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hy : algebraMap O LL ((u⁻¹ : Oˣ) : O) = algebraMap ℚ_[l] LL (((l : ℕ) : ℚ_[l])⁻¹) := by
    rw [map_inv₀, map_natCast]
    have h1 : algebraMap O LL ((u⁻¹ : Oˣ) : O) * algebraMap O LL (u : O) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    rw [hu, map_natCast] at h1
    exact eq_inv_of_mul_eq_one_left h1
  obtain ⟨p, hpm, hp⟩ := (hint _).mp ⟨_, hy⟩
  rw [← Polynomial.hom_eval₂] at hp
  have hp' : p.eval₂ (algebraMap ℤ_[l] ℚ_[l]) (((l : ℕ) : ℚ_[l])⁻¹) = 0 :=
    (algebraMap ℚ_[l] LL).injective (by rw [hp, map_zero])
  have hI : IsIntegral ℤ_[l] (((l : ℕ) : ℚ_[l])⁻¹) := ⟨p, hpm, hp'⟩
  obtain ⟨w, hw⟩ := IsIntegrallyClosed.isIntegral_iff.mp hI
  have hlw : ((l : ℕ) : ℤ_[l]) * w = 1 := by
    apply IsFractionRing.injective ℤ_[l] ℚ_[l]
    rw [map_mul, hw, map_natCast, map_one, mul_inv_cancel₀ hl0]
  exact PadicInt.p_nonunit (IsUnit.of_mul_eq_one _ hlw)

end GlobalTheory.EulerCharH1

namespace GlobalTheory.EulerCharH1

theorem two_le_card (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL]
    [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL]
    (hO : GoodO (Qp := ℚ_[l]) LL O) : 2 ≤ Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) := by
  obtain ⟨hint, -, hfin, -⟩ := GlobalTheory.T.coefficient_ring_integers_compact_adic_properties l LL O hO
  have hf : Finite (O ⧸ Ideal.span {((l : ℕ) : O)}) := by
    simpa using hfin 1
  have : Nontrivial (O ⧸ Ideal.span {((l : ℕ) : O)}) :=
    Ideal.Quotient.nontrivial_iff.mpr (by
      rw [Ne, Ideal.span_singleton_eq_top]; exact natCast_not_isUnit l LL O hint)
  exact Finite.one_lt_card

theorem eq_of_bounds {q a h0 h0' d C1 C2 C3 C4 : ℕ} (X Y H H' : ℕ → ℕ) (hq : 2 ≤ q)
    (hX : ∀ r, q ^ (r * a) ≤ X r ∧ X r ≤ C1 * q ^ (r * a))
    (hY : ∀ r, X r ≤ Y r ∧ Y r ≤ C2 * X r)
    (hE : ∀ r, Y r = H r * H' r * q ^ (r * d))
    (hH : ∀ r, q ^ (r * h0) ≤ H r ∧ H r ≤ C3 * q ^ (r * h0))
    (hH' : ∀ r, q ^ (r * h0') ≤ H' r ∧ H' r ≤ C4 * q ^ (r * h0')) :
    a = h0 + h0' + d := by
  have key : ∀ r : ℕ, q ^ (r * a) ≤ C3 * C4 * q ^ (r * (h0 + h0' + d)) ∧
      q ^ (r * (h0 + h0' + d)) ≤ C2 * C1 * q ^ (r * a) := by
    intro r
    obtain ⟨hX1, hX2⟩ := hX r
    obtain ⟨hY1, hY2⟩ := hY r
    obtain ⟨hH1, hH2⟩ := hH r
    obtain ⟨hH1', hH2'⟩ := hH' r
    have hpow : q ^ (r * (h0 + h0' + d)) = q ^ (r * h0) * q ^ (r * h0') * q ^ (r * d) := by
      rw [← pow_add, ← pow_add]; ring_nf
    constructor
    · calc q ^ (r * a) ≤ X r := hX1
        _ ≤ Y r := hY1
        _ = H r * H' r * q ^ (r * d) := hE r
        _ ≤ (C3 * q ^ (r * h0)) * (C4 * q ^ (r * h0')) * q ^ (r * d) := by
          gcongr
        _ = C3 * C4 * q ^ (r * (h0 + h0' + d)) := by rw [hpow]; ring
    · calc q ^ (r * (h0 + h0' + d)) = q ^ (r * h0) * q ^ (r * h0') * q ^ (r * d) := hpow
        _ ≤ H r * H' r * q ^ (r * d) := by gcongr
        _ = Y r := (hE r).symm
        _ ≤ C2 * X r := hY2
        _ ≤ C2 * (C1 * q ^ (r * a)) := by gcongr
        _ = C2 * C1 * q ^ (r * a) := by ring
  have h1 := le_of_pow_le hq (fun r => (key r).1)
  have h2 := le_of_pow_le hq (fun r => (key r).2)
  omega

theorem finite_and_finrank_H1V : Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK →
    ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l), ∀ (K : FinExt l) (LL : Type) [Field LL]
    [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL],
    GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O)
    (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDual1 (P.PD K) A.ρ A'.ρ m →
    Module.Finite LL (H1V A.ρ) ∧ finrank LL (H1V A.ρ) = finrank LL ↥(H0V A.ρ) +
      finrank LL ↥(H0V A'.ρ) + finrank ℚ_[l] ↥K.1 * finrank LL A.V := by
  intro hTD hEC l _ P K LL _ _ _ O _ _ hO A A' m hm
  obtain ⟨LA, LA', hLL, -⟩ := GlobalTheory.T.exists_mutuallyDual_stable_lattices l P K LL O hO A A' m hm
  have hfinT : Module.Finite O (LatticeCohomology LA) := GlobalTheory.T.finite_H1_period_datum hTD l P K LL O hO A LA
  obtain ⟨hfinV, C1, -, hX⟩ := GlobalTheory.T.H1_lattice_rank_growth_of_goodO l K LL O hO A LA hfinT
  obtain ⟨C2, -, hY⟩ := GlobalTheory.T.H1_reduction_index_bound_of_tateDuality hTD l P K LL O hO A A' LA LA' m hLL
  obtain ⟨C3, -, hH⟩ := GlobalTheory.T.growth_galois_invariants_mod_prime_power_lattice l K LL O hO A LA
  obtain ⟨C4, -, hH'⟩ := GlobalTheory.T.growth_galois_invariants_mod_prime_power_lattice l K LL O hO A' LA'
  exact ⟨hfinV, eq_of_bounds _ _ _ _ (two_le_card l LL O hO) hX
    (fun r => hY r (stableSub_span_smul LA _))
    (fun r => GlobalTheory.T.H1_lattice_index_growth_of_tateDuality_eulerChar hTD hEC l P K LL O hO A A' LA LA' m hLL r
      (stableSub_span_smul LA _) (stableSub_span_smul LA' _))
    (fun r => hH r (stableSub_span_smul LA _)) (fun r => hH' r (stableSub_span_smul LA' _))⟩

end GlobalTheory.EulerCharH1
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankH1DualPairStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_H1_dual_pair : Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l), ∀ (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDual1 (P.PD K) A.ρ A'.ρ m → Module.Finite LL (H1V A.ρ) ∧ finrank LL (H1V A.ρ) = finrank LL ↥(H0V A.ρ) + finrank LL ↥(H0V A'.ρ) + finrank ℚ_[l] ↥K.1 * finrank LL A.V := by
  first | exact @GlobalTheory.EulerCharH1.finite_and_finrank_H1V | exact GlobalTheory.EulerCharH1.finite_and_finrank_H1V | (intros; apply GlobalTheory.EulerCharH1.finite_and_finrank_H1V <;> assumption)
end
