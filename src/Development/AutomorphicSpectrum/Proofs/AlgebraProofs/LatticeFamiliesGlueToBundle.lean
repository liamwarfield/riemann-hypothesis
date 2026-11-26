module

public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XChartNoethFrac
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import Development.WeilBound.CoreStatements.HodgeTatePoints.TwhopfFin
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenWeil
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.WeilBound.CoreStatements.HodgeTatePoints.RiRank
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Comp1IdentityLeft
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.PolarisedFlagStatement
public import ReciprocityTheory.DualLattices.HasLenCokerDet
public import Development.WeilBound.CoreStatements.HodgeTatePoints.CntCoord
public import Development.WeilBound.CoreStatements.HodgeTatePoints.MaBase
public import Development.WeilBound.CoreStatements.HodgeTatePoints.HasLenOfEquiv
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateNormComparison
public import Development.WeilBound.CoreStatements.HodgeTatePoints.FirstPowerZeroAt
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HermitianCombinationSmoothConj

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeFamiliesGlueToBundle
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeFamiliesGlueToBundle
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.Num.BundleOfFamily

theorem main : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V], (∀ Γ : (∀ k, ι k) → AddSubgroup V, IsLatFamily O x Γ → (∀ s, mseg x s ≠ 0 → LocFree (chartRing O (mseg x) s) N (Γ s)) → ∃ E : ChartBundle O (mseg x) N V, ∀ s, mseg x s ≠ 0 → E.lat s = Γ s) ∧ ∀ E : ChartBundle O (mseg x) N V, IsLatFamily O x E.lat ∧ ∀ s, mseg x s ≠ 0 → LocFree (chartRing O (mseg x) s) N (E.lat s) :=
  @PositivityTheory.Xgn.t_bundle_of_family

end GlobalTheory.CompanionTheory.Ar.Num.BundleOfFamily
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeFamiliesGlueToBundleStatement
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_families_glue_to_bundle : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V], (∀ Γ : (∀ k, ι k) → AddSubgroup V, IsLatFamily O x Γ → (∀ s, mseg x s ≠ 0 → LocFree (chartRing O (mseg x) s) N (Γ s)) → ∃ E : ChartBundle O (mseg x) N V, ∀ s, mseg x s ≠ 0 → E.lat s = Γ s) ∧ ∀ E : ChartBundle O (mseg x) N V, IsLatFamily O x E.lat ∧ ∀ s, mseg x s ≠ 0 → LocFree (chartRing O (mseg x) s) N (E.lat s) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.BundleOfFamily.main | exact GlobalTheory.CompanionTheory.Ar.Num.BundleOfFamily.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.BundleOfFamily.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CompleteIntegersProperties
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CompleteIntegersProperties
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem padicComplete_integers_structure : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O), Nonempty (Algebra ℤ_[p] O) ∧ HenselianLocalRing O ∧ IsIntegrallyClosed O ∧ ValuationRing O ∧ IsAlgClosed (FractionRing O) ∧ IsFractionRing O C :=
  @PositivityTheory.HtPt.Twhopf.padic_alg

end GlobalTheory.CompanionTheory.Ar.HT
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CompleteIntegersPropertiesStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complete_integers_properties : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O), Nonempty (Algebra ℤ_[p] O) ∧ HenselianLocalRing O ∧ IsIntegrallyClosed O ∧ ValuationRing O ∧ IsAlgClosed (FractionRing O) ∧ IsFractionRing O C := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.padicComplete_integers_structure | exact GlobalTheory.CompanionTheory.Ar.HT.padicComplete_integers_structure | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.padicComplete_integers_structure <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EigCoordApply
open scoped NNReal
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.ExG

def kerFil {C : Type} [Field C] {w : Valuation C ℝ≥0} {S W : Type} [AddCommGroup W] [Module C W]
    (a : S → w.valuationSubring) (r : ℕ) (g : S → (Fin r → C) →ₗ[C] W) :
    Submodule w.valuationSubring (S → Fin r → C) where
  carrier := {f | f ∈ freeLattice a r ∧ ∀ s, g s (f s) = 0}
  zero_mem' := ⟨zero_mem _, fun s => by simp⟩
  add_mem' := fun hx hy => ⟨add_mem hx.1 hy.1, fun s => by simp [hx.2 s, hy.2 s]⟩
  smul_mem' := fun c f hf => ⟨Submodule.smul_mem _ c hf.1, fun s => by
    have e : (c • f) s = (c : C) • f s := rfl
    rw [e, map_smul, hf.2 s, smul_zero]⟩

def eigCoord {E : Type} [Field E] [NumberField E] {C M : Type} [Field C] [AddCommGroup M] [Module C M]
    (ρ : 𝓞 E →+* Module.End C M) {N : ℕ} (t : Fin N → M) (s : E →+* C) : (Fin N → C) →ₗ[C] M :=
  Fintype.linearCombination C (fun j => HT.eigProj ρ s (t j))

theorem eigCoord_apply {E : Type} [Field E] [NumberField E] {C M : Type} [Field C] [AddCommGroup M] [Module C M]
    (ρ : 𝓞 E →+* Module.End C M) {N : ℕ} (t : Fin N → M) (s : E →+* C) (y : Fin N → C) :
    eigCoord ρ t s y = ∑ j, y j • HT.eigProj ρ s (t j) := by
  simp [eigCoord, Fintype.linearCombination_apply]

def TargetO : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (C : Type) [Field C] [CharZero C] (ν : Valuation C ℝ≥0)
    (bar : 𝓞 E ≃+* 𝓞 E) (σ σ' : E →+* C) (rk : (E →+* C) → ℕ) (p q : ℕ),
    (∃ ℓ : C, 0 < ν ℓ ∧ ν ℓ < 1) →
    (∀ (s : E →+* C) (a : 𝓞 E), s (a : E) ∈ ν.valuationSubring) →
    Nat.card (E →+* C) = Module.finrank ℚ E → (∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) →
    (∀ a, bar (bar a) = a) →
    ∃ γ : C, γ ≠ 0 ∧ ∀ (W : Type) [AddCommGroup W] [Module C W] [Module ν.valuationSubring W]
      [IsScalarTower ν.valuationSubring C W] [FiniteDimensional C W]
      (ρ : 𝓞 E →+* Module.End C W) (ρH : 𝓞 E →+* Module.End C (W × Module.Dual C W))
      (HV : Submodule ν.valuationSubring (W × Module.Dual C W)) (Lie : Submodule ν.valuationSubring W)
      (x : Fin (p + q) → W × Module.Dual C W) (v : Fin p → W) (w : Fin q → W)
      (u : Fin (p + q) → W × Module.Dual C W) (A : Matrix (Fin (p + q)) (Fin (p + q)) C),
      (∀ a y, (ρH a y).1 = ρ a y.1) → (∀ a φ, ρH a (0, φ) = (0, φ ∘ₗ ρ (bar a))) →
      HV.map ((LinearMap.fst C W (Module.Dual C W)).restrictScalars ν.valuationSubring) = Lie →
      (∀ φ : Module.Dual C W, (0, φ) ∈ HV ↔ ∀ e ∈ Lie, φ e ∈ (algebraMap ν.valuationSubring C).range) →
      HT.IsFreeOn ρH HV x → (∀ s, Module.finrank C (HT.eigSp ρ s) = rk s) →
      LinearIndependent C v → Submodule.span ν.valuationSubring (Set.range v) = HT.eigSub ρ σ Lie →
      LinearIndependent C w → Submodule.span ν.valuationSubring (Set.range w) = HT.eigSub ρ σ' Lie →
      IsAdapted ρH σ v w u → LinearIndependent C (fun i => ∑ j, A i j • u j) →
      Submodule.span ν.valuationSubring (Set.range fun i => ∑ j, A i j • u j) = HT.eigQuot ρH σ HV →
      ∃ ε : (ν.valuationSubring)ˣ, A.det = algebraMap ν.valuationSubring C ε * γ

end GlobalTheory.CompanionTheory.Ar.Flat.ExG
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FundamentalCharacterIdealPowers
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open PositivityTheory.HtPt.Ri (wsum wsum_eq mem_xIdeal v_card_sub_one)
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem r_decomp_relay : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (AA : HopfOrder (C := C) R F), FStable (F := F) AA.carrier → ∀ σ : MulChar F R, IsFund p σ → ∀ c : ℕ → R, (∀ m, xIdeal AA.carrier (σ ^ m) = Ideal.span {c m}) → augIdeal AA.carrier = Submodule.span R ((fun m (a : F) => algebraMap R C (c m * (σ ^ m) a)) '' (Finset.Icc 1 (p ^ f - 1) : Set ℕ)) ∧ AA.carrier = Submodule.span R {(1 : F → C)} ⊔ augIdeal AA.carrier ∧ HasColen R v AA.carrier (∏ m ∈ Finset.Icc 1 (p ^ f - 1), v (algebraMap R C (c m))) := by
  intro p _ C _ _ _ v R _ _ hv hpv F _ _ _ _ f hcard AA hM σ hσ c hc
  have wsum_one (χ : MulChar F R) {g : F → C} (hg : g ∈ AA.carrier)
      (h0 : wsum χ g 0 = 0) :
      ∃ r ∈ xIdeal AA.carrier χ, algebraMap R C r = wsum χ g 1 := by
    have heq : wsum χ g = ∑ a : F, χ⁻¹ a • fun x => g (a • x) := by
      funext x
      simp [wsum, Finset.sum_apply, Algebra.smul_def]
    have hm : wsum χ g ∈ AA.carrier := by
      rw [heq]
      exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (hM a g hg)
    obtain ⟨r, hr⟩ := AA.le_int hm 1
    refine ⟨r, (mem_xIdeal _ _ _).2 ?_, hr⟩
    convert hm using 1
    funext a
    rw [wsum_eq χ g h0 a, hr, mul_comm]
  obtain ⟨hord, -, -, -, hsep⟩ := GlobalTheory.CompanionTheory.Ar.GR.FundGen.main p C v R hv hpv F f hcard σ hσ
  set n := p ^ f - 1 with hn
  have hcardn : Fintype.card F = n + 1 := by
    rw [hcard, hn, Nat.sub_add_cancel (Nat.one_le_pow _ _ (Fact.out : p.Prime).pos)]
  have hn1 : 1 ≤ n := by
    have := Fintype.one_lt_card (α := F)
    omega
  have hσn : σ ^ n = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one σ
  have hpow : ∀ m, m ≠ 0 → ∀ z : F, (σ ^ m) z = σ z ^ m := fun m hm z => MulChar.pow_apply' σ hm z
  have hIcc : ∀ g : ℕ → C, ∑ m ∈ Finset.Icc 1 n, g m = ∑ i ∈ Finset.range n, g (i + 1) := by
    intro g
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel, add_comm 1]
  have horth : ∀ z : F, ∑ m ∈ Finset.Icc 1 n, algebraMap R C ((σ ^ m) z) = if z = 1 then (n : C) else 0 := by
    intro z
    by_cases hz1 : z = 1
    · subst hz1
      simp
    rw [ite_eq_right hz1]
    by_cases hz0 : z = 0
    · subst hz0
      refine Finset.sum_eq_zero fun m _ => ?_
      rw [MulChar.map_nonunit _ not_isUnit_zero, map_zero]
    have hsz := hsep z 1 hz1
    have hζ1 : algebraMap R C (σ z) ≠ 1 := by
      intro h
      rw [map_sub, h, map_one, map_one, sub_self, map_zero] at hsz
      exact zero_ne_one hsz
    have hζn : algebraMap R C (σ z) ^ n = 1 := by
      rw [← map_pow, ← hpow n (by omega), hσn, MulChar.one_apply (Ne.isUnit hz0), map_one]
    rw [hIcc]
    have e : ∀ i, algebraMap R C ((σ ^ (i + 1)) z) = algebraMap R C (σ z) * algebraMap R C (σ z) ^ i := by
      intro i
      rw [hpow _ (Nat.succ_ne_zero i), map_pow, pow_succ, mul_comm]
    simp_rw [e, ← Finset.mul_sum, geom_sum_eq hζ1, hζn, sub_self, zero_div, mul_zero]
  have hb : ∀ m, (fun a : F => algebraMap R C (c m * (σ ^ m) a)) ∈ AA.carrier := by
    intro m
    have := (mem_xIdeal AA.carrier (σ ^ m) (c m)).mp (by rw [hc m]; exact Ideal.mem_span_singleton_self _)
    simpa only [map_mul] using this
  have hn0 : (n : C) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  obtain ⟨qi, hqi⟩ : ∃ qi : R, algebraMap R C qi = (n : C)⁻¹ := by
    have h5 := v_card_sub_one (R := R) (F := F) p hv hpv
    rw [hcardn, Nat.cast_succ, add_sub_cancel_right] at h5
    exact hv.exists_of_le_one (by rw [map_inv₀, h5, inv_one])
  have hI : augIdeal AA.carrier = Submodule.span R ((fun m (a : F) => algebraMap R C (c m * (σ ^ m) a)) '' (Finset.Icc 1 (p ^ f - 1) : Set ℕ)) := by
    apply le_antisymm
    · intro g hg
      simp only [augIdeal, Submodule.mem_inf, LinearMap.mem_ker] at hg
      have hgA := hg.1
      have hg0 : g 0 = 0 := hg.2
      have hk : ∀ m, ∃ k : R, wsum (σ ^ m) g 1 = algebraMap R C (k * c m) := by
        intro m
        obtain ⟨r, hr, hr1⟩ := wsum_one (σ ^ m) hgA (by simp [wsum, hg0])
        rw [hc m] at hr
        obtain ⟨k, rfl⟩ := Ideal.mem_span_singleton'.mp hr
        exact ⟨k, hr1.symm⟩
      choose k hk using hk
      have e4 : ∀ a : F, ∑ m ∈ Finset.Icc 1 n, algebraMap R C ((σ ^ m)⁻¹ a) = if a = 1 then (n : C) else 0 := by
        intro a
        simp_rw [MulChar.inv_apply']
        rw [horth a⁻¹]
        simp [inv_eq_one]
      have hg_eq : g = ∑ m ∈ Finset.Icc 1 n, (qi * k m) • (fun a : F => algebraMap R C (c m * (σ ^ m) a)) := by
        funext x
        rw [Finset.sum_apply]
        simp only [Pi.smul_apply, Algebra.smul_def, map_mul, hqi]
        have hw : ∀ m ∈ Finset.Icc 1 n, wsum (σ ^ m) g x = algebraMap R C ((σ ^ m) x) * (algebraMap R C (k m) * algebraMap R C (c m)) := by
          intro m _
          rw [wsum_eq (σ ^ m) g (by simp [wsum, hg0]) x, hk m, map_mul]
        have hsum : ∑ m ∈ Finset.Icc 1 n, wsum (σ ^ m) g x = (n : C) * g x := by
          simp only [wsum]
          calc ∑ m ∈ Finset.Icc 1 n, ∑ a, algebraMap R C ((σ ^ m)⁻¹ a) * g (a * x)
              = ∑ a, (∑ m ∈ Finset.Icc 1 n, algebraMap R C ((σ ^ m)⁻¹ a)) * g (a * x) := by
                rw [Finset.sum_comm]
                simp_rw [Finset.sum_mul]
            _ = _ := by
                simp_rw [e4]
                simp [ite_mul]
        rw [Finset.sum_congr rfl hw] at hsum
        calc g x = (n : C)⁻¹ * ((n : C) * g x) := by field_simp
          _ = _ := by
            rw [← hsum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun m _ => ?_
            ring
      rw [hg_eq]
      exact Submodule.sum_mem _ fun m hm => Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, Finset.mem_coe.mpr hm, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨m, hm, rfl⟩
      simp only [augIdeal, SetLike.mem_coe, Submodule.mem_inf, LinearMap.mem_ker]
      refine ⟨hb m, ?_⟩
      show algebraMap R C (c m * (σ ^ m) 0) = 0
      rw [MulChar.map_nonunit _ not_isUnit_zero, mul_zero, map_zero]
  have hII : AA.carrier = Submodule.span R {(1 : F → C)} ⊔ augIdeal AA.carrier := by
    apply le_antisymm
    · intro g hg
      obtain ⟨r, hr⟩ : ∃ r : R, algebraMap R C r = g 0 := AA.le_int hg 0
      rw [← add_sub_cancel (r • (1 : F → C)) g]
      refine Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)) ?_
      simp only [augIdeal, Submodule.mem_inf, LinearMap.mem_ker]
      refine ⟨AA.carrier.sub_mem hg (AA.carrier.smul_mem r AA.one_mem), ?_⟩
      show (g - r • (1 : F → C)) 0 = 0
      simp [Algebra.smul_def, ← hr]
    · refine sup_le ?_ (fun g hg => by simp only [augIdeal, Submodule.mem_inf] at hg; exact hg.1)
      rw [Submodule.span_le, Set.singleton_subset_iff]
      exact AA.one_mem
  refine ⟨hI, hII, ?_⟩
  let e := Fintype.equivFinOfCardEq hcardn
  have hre : ∀ g : ℕ → C, ∑ j : F, g (e j : ℕ) = g 0 + ∑ m ∈ Finset.Icc 1 n, g m := by
    intro g
    rw [e.sum_comp (fun k : Fin (n + 1) => g k), Fin.sum_univ_eq_sum_range g (n + 1), Finset.sum_range_succ', hIcc, add_comm]
  have hreP : ∀ g : ℕ → NNReal, ∏ j : F, g (e j : ℕ) = g 0 * ∏ m ∈ Finset.Icc 1 n, g m := by
    intro g
    rw [e.prod_comp (fun k : Fin (n + 1) => g k), Fin.prod_univ_eq_prod_range g (n + 1), Finset.prod_range_succ',
      ← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range, mul_comm]
    simp only [Nat.add_sub_cancel, add_comm 1]
  let TR : Matrix F F R := Matrix.of fun x j => if (e j : ℕ) = 0 then 1 else (σ ^ (e j : ℕ)) x
  let UR : Matrix F F R := Matrix.of fun j y => if (e j : ℕ) = 0 then (if y = 0 then 1 else 0)
    else if y = 0 then (if (e j : ℕ) = n then -1 else 0) else qi * (σ ^ (e j : ℕ))⁻¹ y
  let d : F → C := fun j => if (e j : ℕ) = 0 then 1 else algebraMap R C (c (e j))
  let T := TR.map (algebraMap R C)
  let U := UR.map (algebraMap R C)
  have hTU : T * U = 1 := by
    ext x y
    rw [Matrix.mul_apply]
    simp only [T, U, Matrix.map_apply, Matrix.of_apply, TR, UR]
    have h6 := hre (fun k => algebraMap R C (if k = 0 then 1 else (σ ^ k) x) *
      algebraMap R C (if k = 0 then (if y = 0 then 1 else 0) else if y = 0 then (if k = n then -1 else 0) else qi * (σ ^ k)⁻¹ y))
    simp only at h6
    rw [h6]
    rw [Finset.sum_congr rfl (g := fun m => algebraMap R C ((σ ^ m) x) * algebraMap R C (if y = 0 then (if m = n then -1 else 0) else qi * (σ ^ m)⁻¹ y))
      (fun m hm => by rw [ite_eq_right (by simp at hm; omega), ite_eq_right (by simp at hm; omega)])]
    by_cases hy : y = 0
    · subst hy
      simp only [ite_true, map_one, apply_ite (algebraMap R C), map_neg, map_zero, mul_ite, mul_neg, mul_one, mul_zero]
      rw [Finset.sum_ite_eq' (Finset.Icc 1 n) n, ite_eq_left (Finset.mem_Icc.mpr ⟨hn1, le_rfl⟩), hσn]
      by_cases hx : x = 0
      · subst hx
        rw [MulChar.map_nonunit (1 : MulChar F R) (not_isUnit_zero (M₀ := F)), map_zero, neg_zero, add_zero,
          Matrix.one_apply_eq]
      · rw [MulChar.one_apply (Ne.isUnit hx), map_one, Matrix.one_apply_ne hx]
        ring
    · simp only [ite_eq_right hy, ite_true, map_zero, mul_zero, zero_add, map_mul, hqi]
      have e5 : ∀ m, algebraMap R C ((σ ^ m) x) * ((n : C)⁻¹ * algebraMap R C ((σ ^ m)⁻¹ y)) =
          (n : C)⁻¹ * algebraMap R C ((σ ^ m) (x * y⁻¹)) := by
        intro m
        rw [MulChar.inv_apply', map_mul (σ ^ m) x, map_mul]
        ring
      simp_rw [e5]
      rw [← Finset.mul_sum, horth, Matrix.one_apply]
      by_cases hxy : x = y
      · subst hxy
        rw [mul_inv_cancel₀ hy, ite_eq_left rfl, ite_eq_left rfl, inv_mul_cancel₀ hn0]
      · rw [ite_eq_right (by rwa [mul_inv_eq_one₀ hy]), ite_eq_right hxy, mul_zero]
  have hdetTU : T.det * U.det = 1 := by rw [← Matrix.det_mul, hTU, Matrix.det_one]
  have hTdet : T.det = algebraMap R C TR.det := (RingHom.map_det _ _).symm
  have hUdet : U.det = algebraMap R C UR.det := (RingHom.map_det _ _).symm
  have hvT : v T.det = 1 := by
    have h1 := congrArg v hdetTU
    rw [map_mul, map_one, hUdet] at h1
    have hT1 : v T.det ≤ 1 := by
      rw [hTdet]
      exact hv.map_le_one _
    have hU1 := hv.map_le_one UR.det
    refine le_antisymm hT1 ?_
    calc (1 : NNReal) = v T.det * v (algebraMap R C UR.det) := h1.symm
      _ ≤ v T.det * 1 := by gcongr
      _ = v T.det := mul_one _
  have hcol : ∀ j, (fun x => (T * Matrix.diagonal d) x j) =
      fun x => if (e j : ℕ) = 0 then 1 else algebraMap R C (c (e j) * (σ ^ (e j : ℕ)) x) := by
    intro j
    funext x
    rw [Matrix.mul_diagonal]
    simp only [T, d, TR, Matrix.map_apply, Matrix.of_apply]
    split_ifs <;> simp [map_mul, mul_comm]
  refine ⟨T * Matrix.diagonal d, ?_, ?_⟩
  · apply le_antisymm
    · rw [hII, hI, sup_le_iff]
      constructor
      · rw [Submodule.span_le, Set.singleton_subset_iff]
        apply Submodule.subset_span
        refine ⟨e.symm ⟨0, by omega⟩, (hcol _).trans ?_⟩
        funext x
        simp
      · rw [Submodule.span_le]
        rintro _ ⟨m, hm, rfl⟩
        have hm' : 1 ≤ m ∧ m ≤ n := by simpa using hm
        apply Submodule.subset_span
        refine ⟨e.symm ⟨m, by omega⟩, (hcol _).trans ?_⟩
        funext x
        simp only [Equiv.apply_symm_apply]
        split_ifs with h0
        · exact absurd (h0 : m = 0) (by omega)
        · rfl
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      show (fun x => (T * Matrix.diagonal d) x j) ∈ AA.carrier
      rw [hcol j]
      by_cases hj : (e j : ℕ) = 0
      · simp only [hj, ite_true]
        exact AA.one_mem
      · simp only [hj, ite_false]
        exact hb _
  · rw [Matrix.det_mul, Matrix.det_diagonal, map_mul, hvT, one_mul, map_prod]
    have h7 := hreP (fun k => v (if k = 0 then 1 else algebraMap R C (c k)))
    simp only at h7
    rw [show (∏ j, v (d j)) = ∏ j, v (if (e j : ℕ) = 0 then 1 else algebraMap R C (c (e j))) from rfl, h7]
    simp only [↓reduceIte, map_one, one_mul]
    refine Finset.prod_congr rfl fun m hm => ?_
    rw [ite_eq_right (by simp at hm; omega)]

end GlobalTheory.CompanionTheory.Ar.GR
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalBilinearTermProduct
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalBilinearTermProduct
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Conj.BilCalc

theorem bil_calc : ∀ (R : Type) [CommRing R] (d : ℕ) (f g : PS R 2 d) (φ ψ : Pt R 1 d), AxOne f → AxOne g → (∀ i, constantCoeff (φ i) = 0) → (∀ i, constantCoeff (ψ i) = 0) → AxOne (f * g) ∧ (∀ m, bil (f * g) m 1 = bil f m 1 + bil g m 1) ∧ (∀ n, bil (f * g) 1 n = bil f 1 n + bil g 1 n) ∧ AxOne (ev (n := 2) ![comp1 φ (pt R d 0), comp1 ψ (pt R d 1)] f) ∧ bil (ev (n := 2) ![comp1 φ (pt R d 0), comp1 ψ (pt R d 1)] f) 1 1 = (lin φ 1).transpose * bil f 1 1 * lin ψ 1 ∧ (∀ m n, bil (ev (n := 2) ![pt R d 1, pt R d 0] f) m n = (bil f n m).transpose) ∧ ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → bil (ev (n := 2) ![ptPow R d m 0, ptPow R d n 1] f) m n = bil f 1 1 :=
  @PositivityTheory.HtPt.Ca.bil_calc

end GlobalTheory.CompanionTheory.Ar.Conj.BilCalc
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalBilinearTermProductStatement
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_bilinear_term_product : ∀ (R : Type) [CommRing R] (d : ℕ) (f g : PS R 2 d) (φ ψ : Pt R 1 d), AxOne f → AxOne g → (∀ i, constantCoeff (φ i) = 0) → (∀ i, constantCoeff (ψ i) = 0) → AxOne (f * g) ∧ (∀ m, bil (f * g) m 1 = bil f m 1 + bil g m 1) ∧ (∀ n, bil (f * g) 1 n = bil f 1 n + bil g 1 n) ∧ AxOne (ev (n := 2) ![comp1 φ (pt R d 0), comp1 ψ (pt R d 1)] f) ∧ bil (ev (n := 2) ![comp1 φ (pt R d 0), comp1 ψ (pt R d 1)] f) 1 1 = (lin φ 1).transpose * bil f 1 1 * lin ψ 1 ∧ (∀ m n, bil (ev (n := 2) ![pt R d 1, pt R d 0] f) m n = (bil f n m).transpose) ∧ ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → bil (ev (n := 2) ![ptPow R d m 0, ptPow R d n 1] f) m n = bil f 1 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.BilCalc.bil_calc | exact GlobalTheory.CompanionTheory.Ar.Conj.BilCalc.bil_calc | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.BilCalc.bil_calc <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PolarisedAugmentationTheorem
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AugmentationLengthsExist
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AugmentationLengthsExist
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem lens_exist : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], (∀ x : N, p • x = 0) → ∀ AA : HopfOrder (C := C) R N, ∃ cA cN cO : NNReal, cA ≠ 0 ∧ cN ≠ 0 ∧ cO ≠ 0 ∧ HasLen v R (AFQuot p AA.carrier) cA ∧ HasColen R v AA.carrier cN ∧ HasLen v R (OmAA AA.carrier) cO :=
  @PositivityTheory.HtPt.Rc.lens

end GlobalTheory.CompanionTheory.Ar.GR
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AugmentationLengthsExistStatement
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.augmentation_lengths_exist : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], (∀ x : N, p • x = 0) → ∀ AA : HopfOrder (C := C) R N, ∃ cA cN cO : NNReal, cA ≠ 0 ∧ cN ≠ 0 ∧ cO ≠ 0 ∧ HasLen v R (AFQuot p AA.carrier) cA ∧ HasColen R v AA.carrier cN ∧ HasLen v R (OmAA AA.carrier) cO := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.lens_exist | exact GlobalTheory.CompanionTheory.Ar.GR.lens_exist | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.lens_exist <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AugmentationLengthColengthBound
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AugmentationLengthColengthBound
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.augmentation_length_colength_bound : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], (∀ x : N, p • x = 0) → ∀ AA : HopfOrder (C := C) R N, ∀ cA cN, HasLen v R (AFQuot p AA.carrier) cA → HasColen R v AA.carrier cN → cA ^ (Fintype.card N * (p - 1)) ≤ cN ^ 2 ∧ (cA ^ (Fintype.card N * (p - 1)) = cN ^ 2 → GenAF p AA.carrier ⊥) := by
  first | exact @PositivityTheory.HtPt.Ra.cnt | exact PositivityTheory.HtPt.Ra.cnt
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AugmentationLengthColengthBoundStatement
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.augmentation_length_colength_bound : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], (∀ x : N, p • x = 0) → ∀ AA : HopfOrder (C := C) R N, ∀ cA cN, HasLen v R (AFQuot p AA.carrier) cA → HasColen R v AA.carrier cN → cA ^ (Fintype.card N * (p - 1)) ≤ cN ^ 2 ∧ (cA ^ (Fintype.card N * (p - 1)) = cN ^ 2 → GenAF p AA.carrier ⊥) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.augmentation_length_colength_bound | exact GlobalTheory.CompanionTheory.Relay.augmentation_length_colength_bound | (intros; apply GlobalTheory.CompanionTheory.Relay.augmentation_length_colength_bound <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeLengthMonoStrict
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeLengthMonoStrict
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem submodule_eq_of_hasLen_eq : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → ∀ (ι : Type) [Fintype ι] (L L' : Submodule R (ι → R)), L ≤ L' → ∀ x y : NNReal, x ≠ 0 → HasLen v R ((ι → R) ⧸ L) x → HasLen v R ((ι → R) ⧸ L') y → x ≤ y ∧ (x = y → L = L') :=
  @PositivityTheory.HtPt.Rh.len_eq

end GlobalTheory.CompanionTheory.Ar.GR
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeLengthMonoStrictStatement
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_length_mono_strict : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → ∀ (ι : Type) [Fintype ι] (L L' : Submodule R (ι → R)), L ≤ L' → ∀ x y : NNReal, x ≠ 0 → HasLen v R ((ι → R) ⧸ L) x → HasLen v R ((ι → R) ⧸ L') y → x ≤ y ∧ (x = y → L = L') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.submodule_eq_of_hasLen_eq | exact GlobalTheory.CompanionTheory.Ar.GR.submodule_eq_of_hasLen_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.submodule_eq_of_hasLen_eq <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AugmentationQuotientEquivLattice
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AugmentationQuotientEquivLattice
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem afQuot_equiv_coords : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (AA : HopfOrder (C := C) R (ι → ZMod p)), Nonempty (AFQuot p AA.carrier ≃ₗ[R] ((ι → R) ⧸ afLat p AA.carrier)) :=
  PositivityTheory.HtPt.Rh.afquot

end GlobalTheory.CompanionTheory.Ar.GR
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AugmentationQuotientEquivLatticeStatement
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.augmentation_quotient_equiv_lattice : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (AA : HopfOrder (C := C) R (ι → ZMod p)), Nonempty (AFQuot p AA.carrier ≃ₗ[R] ((ι → R) ⧸ afLat p AA.carrier)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.afQuot_equiv_coords | exact GlobalTheory.CompanionTheory.Ar.GR.afQuot_equiv_coords | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.afQuot_equiv_coords <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PolarisedAugmentationTheorem
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GR.PolAF

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]

theorem hasLen_omAA_htd {p : ℕ} [Fact p.Prime] {g : ℕ} {v : Valuation C NNReal} [Algebra ℤ_[p] R]
    {O : Type} [CommRing O] [Algebra ℤ_[p] O] {σ : O ≃ₐ[ℤ_[p]] O} {cp : R}
    (H : HodgeTateDatum p g v R O σ cp) :
    HasLen v R (OmAA H.AA.carrier) (v (algebraMap R C (p : R)) ^ g) := by
  refine ⟨g, fun _ => (p : R), ⟨?_⟩, by simp⟩
  exact (Submodule.quotEquivOfEq _ _ H.cotangent_ker_eq.symm).trans
    ((LinearMap.quotKerEquivOfSurjective H.φ H.cotangent_surjective).trans (PullbackHopfOrder.qPi p g))

theorem mem_afLat_of_cong {p : ℕ} [Fact p.Prime] {g : ℕ} [Algebra ℤ_[p] R]
    (M : Submodule R (Nb p g → C)) (l : Ix g → R) (f : Nb p g → C) (hf : f ∈ M)
    (h : ∀ t : TT p g, ∃ r : R, algebraMap R C (∑ i, l i * algebraMap ℤ_[p] R (t i)) -
      f (red p g t) = algebraMap R C (p * r)) : l ∈ afLat p M := by
  refine ⟨f, hf, fun x => ?_⟩
  obtain ⟨r, hr⟩ := h (fun i => ((x i).val : ℤ_[p]))
  have hred : red p g (fun i => ((x i).val : ℤ_[p])) = x := by
    funext i; simp [red]
  have hsum : (∑ i, l i * algebraMap ℤ_[p] R (((x i).val : ℕ) : ℤ_[p])) =
      ∑ i, l i * ((x i).val : R) := by
    exact Finset.sum_congr rfl fun i _ => by rw [map_natCast]
  rw [hred, hsum] at hr
  have hx : f x - algebraMap R C (∑ i, l i * ((x i).val : R)) = -(algebraMap R C (p * r)) := by
    rw [← hr]; ring
  show _ ∈ Submodule.span R {(p : C)}
  rw [hx, Submodule.mem_span_singleton]
  refine ⟨-r, ?_⟩
  rw [Algebra.smul_def, map_mul, map_neg, map_natCast]
  ring

theorem rows_mem_afLat {p : ℕ} [Fact p.Prime] {g : ℕ} {v : Valuation C NNReal} [Algebra ℤ_[p] R]
    {O : Type} [CommRing O] [Algebra ℤ_[p] O] {σ : O ≃ₐ[ℤ_[p]] O} {cp : R}
    (H : HodgeTateDatum p g v R O σ cp) (k : Ix g) :
    Matrix.fromRows H.Ht H.Bt k ∈ afLat p H.AA.carrier := by
  rcases k with k | k
  · obtain ⟨f, hf, h⟩ := (H.h4 k).1
    exact mem_afLat_of_cong H.AA.carrier (H.Ht k) f hf h
  · obtain ⟨f, hf, h⟩ := (H.h4 k).2
    exact mem_afLat_of_cong H.AA.carrier (H.Bt k) f hf h

theorem span_rows_integral {g : ℕ} (v : Valuation C NNReal) (hv : v.Integers R)
    (Ht Bt : Matrix (Fin g) (Ix g) R) (x : Ix g → C) :
    (∀ l ∈ Submodule.span R (Set.range fun k => Matrix.fromRows Ht Bt k),
      v (∑ i, algebraMap R C (l i) * x i) ≤ 1) ↔
    (∀ k, v ((Ht.map (algebraMap R C) *ᵥ x) k) ≤ 1) ∧
      ∀ k, v ((Bt.map (algebraMap R C) *ᵥ x) k) ≤ 1 := by
  constructor
  · intro h
    refine ⟨fun k => ?_, fun k => ?_⟩
    · simpa [Matrix.mulVec, dotProduct] using h _ (Submodule.subset_span ⟨Sum.inl k, rfl⟩)
    · simpa [Matrix.mulVec, dotProduct] using h _ (Submodule.subset_span ⟨Sum.inr k, rfl⟩)
  · rintro ⟨h1, h2⟩ l hl
    induction hl using Submodule.span_induction with
    | mem l hl =>
      obtain ⟨k, rfl⟩ := hl
      rcases k with k | k
      · simpa [Matrix.mulVec, dotProduct] using h1 k
      · simpa [Matrix.mulVec, dotProduct] using h2 k
    | zero => simp
    | add a b _ _ ha hb =>
      simp only [Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]
      exact (v.map_add _ _).trans (max_le ha hb)
    | smul r a _ ha =>
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc, ← Finset.mul_sum]
      exact mul_le_one' (hv.map_le_one r) ha

end GlobalTheory.CompanionTheory.Ar.GR.PolAF

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem polarisedAF : PolarisedAFStatement := by
  intro p _ g C _ _ _ v R _ _ _ O _ _ σ cp hS H
  intro φ AF H' hb
  classical
  have hv : v.Integers R := hS.integers
  have hp1 : v (p : C) < 1 := by simpa [map_natCast] using hS.p_lt
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hvcp : v (algebraMap R C cp) ≠ 0 := by
    intro h0
    have h := hS.cp_val
    rw [h0, zero_pow (by omega)] at h
    exact hS.p_ne h.symm
  have hcp : cp ≠ 0 := by rintro rfl; exact hvcp (by simp)
  have hEalt : (H.E.map (algebraMap ℤ_[p] R))ᵀ = -(H.E.map (algebraMap ℤ_[p] R)) := by
    ext i j
    have h := congrFun (congrFun H.E_alternating.1 j) i
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at h
    simp [Matrix.transpose_apply, Matrix.map_apply, h]
  have hEu : IsUnit (H.E.map (algebraMap ℤ_[p] R)).det := by
    have : (H.E.map (algebraMap ℤ_[p] R)).det = algebraMap ℤ_[p] R H.E.det :=
      (RingHom.map_det _ _).symm
    rw [this]; exact H.isUnit_det_E.map _
  obtain ⟨hdet, hker, himg, hcpmem⟩ :=
    GlobalTheory.T.symplectic_period_matrix_integrality C v R hv g H.Ht H.Bt _ cp hcp hEalt hEu H.form_eq_alt

  set L := Submodule.span R (Set.range fun k => Matrix.fromRows H.Ht H.Bt k) with hL
  have hLle : L ≤ AF :=
    Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact PolAF.rows_mem_afLat H k)
  have hLlen : HasLen v R ((Ix g → R) ⧸ L) (v (algebraMap R C cp) ^ g) := by
    have h := hasLen_coker_det' v R hv (Ix g) (Matrix.fromRows H.Ht H.Bt)ᵀ
    rw [Matrix.det_transpose, hdet, Matrix.range_mulVecLin] at h
    exact h

  have hkill : ∀ x : Nb p g, p • x = 0 := by intro x; ext i; simp
  obtain ⟨cA, cN, cO, -, -, -, hA, hN, hO⟩ := GlobalTheory.T.augmentation_lengths_exist p C v R hv hp1 (Nb p g) hkill H.AA
  have hcO : cO = v (algebraMap R C (p : R)) ^ g := hasLen_unique hv hO (PolAF.hasLen_omAA_htd H)
  have hdeg := u4 p C v R hv hp1 (Nb p g) hkill H.AA cN cO hN hO
  obtain ⟨hcnt, hgen⟩ := GlobalTheory.T.augmentation_length_colength_bound p C v R hv hp1 (Nb p g) hkill H.AA cA cN hA hN
  obtain ⟨eq⟩ := GlobalTheory.T.augmentation_quotient_equiv_lattice p C v R hv hp1 (Ix g) H.AA
  have hAF : HasLen v R ((Ix g → R) ⧸ AF) cA := hasLen_of_equiv eq.symm hA
  obtain ⟨hle, hLeq⟩ :=
    GlobalTheory.T.lattice_length_mono_strict C v R hv (Ix g) L AF hLle _ _ (pow_ne_zero _ hvcp) hLlen hAF
  have hn : Fintype.card (Nb p g) * (p - 1) ≠ 0 :=
    Nat.mul_ne_zero Fintype.card_ne_zero (by omega)
  have hOeq : cO ^ Fintype.card (Nb p g) =
      (v (algebraMap R C cp) ^ g) ^ (Fintype.card (Nb p g) * (p - 1)) := by
    rw [hcO, ← hS.cp_val, ← pow_mul, ← pow_mul, ← pow_mul]
    congr 1; ring
  have h1 : (v (algebraMap R C cp) ^ g) ^ (Fintype.card (Nb p g) * (p - 1)) ≤
      cA ^ (Fintype.card (Nb p g) * (p - 1)) := pow_le_pow_left₀ zero_le hle _
  have hAn : cA ^ (Fintype.card (Nb p g) * (p - 1)) = cN ^ 2 :=
    le_antisymm hcnt (hdeg.trans (hOeq ▸ h1))
  have hOn : cO ^ Fintype.card (Nb p g) = cN ^ 2 :=
    le_antisymm (hOeq ▸ h1.trans hAn.le) hdeg
  have hcA : cA = v (algebraMap R C cp) ^ g :=
    ((pow_left_inj₀ zero_le zero_le hn).1 (hAn.trans (hOn.symm.trans hOeq)))
  have hLAF : L = AF := hLeq hcA.symm

  have hmem : ∀ x, x ∈ H' ↔ (∀ k, v ((H.Ht.map φ *ᵥ x) k) ≤ 1) ∧
      ∀ k, v ((H.Bt.map φ *ᵥ x) k) ≤ 1 := by
    intro x
    show (∀ l ∈ AF, _) ↔ _
    rw [← hLAF]
    exact PolAF.span_rows_integral v hv H.Ht H.Bt x
  refine ⟨hLAF.symm, fun l => hLAF ▸ hcpmem l, hLAF ▸ hLlen, hcA ▸ hA, hmem, ?_, ?_,
    hgen hAn, ⟨cA, cN, cO, hA, hN, hO, hAn, hOn⟩⟩
  · intro x
    rw [← hker x, hmem]
    constructor
    · rintro ⟨⟨-, h2⟩, h0⟩; exact ⟨h0, h2⟩
    · rintro ⟨h0, h2⟩; exact ⟨⟨fun k => by rw [show H.Ht.map φ *ᵥ x = 0 from h0]; simp, h2⟩, h0⟩
  · intro w hw
    obtain ⟨x, hx1, hx2⟩ := himg w hw
    refine ⟨x, (hmem x).2 ⟨fun k => by rw [hx1]; exact hw k, fun k => by rw [show H.Bt.map φ *ᵥ x = 0 from hx2]; simp⟩, hx1⟩

end GlobalTheory.CompanionTheory.Ar.GR
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PolarisedAugmentationTheoremStatement
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarised_augmentation_theorem : GlobalTheory.CompanionTheory.Ar.GR.PolarisedAFStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.polarisedAF | exact GlobalTheory.CompanionTheory.Ar.GR.polarisedAF | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.polarisedAF <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeTateConstantDividesPSq
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PrimRootSubOnePowAssociated
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem primRoot_sub_one_pow_associated {O : Type*} [CommRing O] [IsDomain O] {p : ℕ}
    (hp : p.Prime) {ζ : O} (hζ : IsPrimitiveRoot ζ p) :
    Associated ((ζ - 1) ^ (p - 1)) (p : O) := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by have := hp.pos; omega⟩
  have h := hζ.prod_one_sub_pow_eq_order
  have h2 : Associated (∏ _k ∈ Finset.range n, (ζ - 1)) (∏ k ∈ Finset.range n, (1 - ζ ^ (k + 1))) := by
    refine Associated.prod _ _ _ fun k hk => ?_
    have hk' := Finset.mem_range.1 hk
    have hc : (k + 1).Coprime (n + 1) :=
      (Nat.coprime_of_lt_prime (by omega) (by omega) hp).symm
    have := hζ.associated_sub_one_pow_sub_one_of_coprime hc
    rw [← neg_sub (ζ ^ (k + 1)) 1]
    exact this.neg_right
  rw [h, Finset.prod_const, Finset.card_range] at h2
  simpa using h2

end GlobalTheory.CompanionTheory.Ar.HT
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeTateConstantDividesPSq
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem isPrimitiveRoot_map_of_charZero {A C : Type} [CommRing A] [IsDomain A] [Field C] [CharZero C]
    (ψ : A →+* C) (p : ℕ) [hp : Fact p.Prime] {ζ : A} (hζ : IsPrimitiveRoot ζ p) :
    IsPrimitiveRoot (ψ ζ) p := by
  have hp1 := hp.out
  have h1 : ψ ζ ^ p = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
  have h2 : ψ ζ ≠ 1 := by
    intro h
    have hs := congrArg ψ (hζ.geom_sum_eq_zero hp1.one_lt)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_zero] at hs
    simp only [map_pow, h, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one] at hs
    exact hp1.ne_zero (by exact_mod_cast hs)
  exact IsPrimitiveRoot.iff_orderOf.2 (orderOf_eq_prime h1 h2)

theorem isHTConst_sub_one_of_primitive {C : Type} [Field C] (v : Valuation C NNReal) {O : Type} [CommRing O]
    [Algebra O C] (hv : v.Integers O) [CharZero C] (p : ℕ) [hp : Fact p.Prime] {A : Type} [CommRing A] [IsDomain A]
    (φ : A →+* O) {ζ : A} (hζ : IsPrimitiveRoot ζ p) :
    IsHTConst v p (φ (ζ - 1)) ∧ (ζ - 1) ∣ (p : A) ^ 2 := by
  have h1 : IsPrimitiveRoot ((algebraMap O C) (φ ζ)) p :=
    GlobalTheory.CompanionTheory.Ar.HT.isPrimitiveRoot_map_of_charZero ((algebraMap O C).comp φ) p hζ
  have hne : p - 1 ≠ 0 := by
    have := hp.out.two_le
    omega
  refine ⟨?_, ?_⟩
  · rw [map_sub, map_one]
    exact GlobalTheory.CompanionTheory.Ar.HT.PointTest.isHTConst_sub_one h1
  · exact (dvd_pow_self (ζ - 1) hne).trans
      ((GlobalTheory.CompanionTheory.Ar.HT.primRoot_sub_one_pow_associated hp.out hζ).dvd.trans
        (dvd_pow_self _ two_ne_zero))

theorem isHTConst_of_isCp : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O) [CharZero C] (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [IsDomain A] [CharZero A] (φ : A →+* O) (κ : A), v (p : C) < 1 → (if p = 2 then κ = 4 else ∃ ζ : A, IsPrimitiveRoot ζ p ∧ κ = ζ - 1) → IsHTConst v p (φ κ) ∧ κ ∣ (p : A) ^ 2 := by
  intro C _ v O _ _ hv _ p _ A _ _ _ φ κ hvp hκ
  split_ifs at hκ with h2
  · subst h2
    subst hκ
    have hv2 : v (2 : C) < 1 := by exact_mod_cast hvp
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [map_ofNat, map_ofNat]
      norm_num
    · rw [map_ofNat, map_ofNat]
      have h4 : (4 : C) = 2 * 2 := by norm_num
      rw [h4, map_mul]
      norm_num
      exact mul_le_of_le_one_left' hv2.le
    · exact ⟨1, by norm_num⟩
  · obtain ⟨ζ, hζ, rfl⟩ := hκ
    exact GlobalTheory.CompanionTheory.Ar.HT.isHTConst_sub_one_of_primitive v hv p φ hζ

end GlobalTheory.CompanionTheory.Ar.HT
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeTateConstantDividesPSqStatement
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_constant_divides_p_sq : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O) [CharZero C] (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [IsDomain A] [CharZero A] (φ : A →+* O) (κ : A), v (p : C) < 1 → (if p = 2 then κ = 4 else ∃ ζ : A, IsPrimitiveRoot ζ p ∧ κ = ζ - 1) → IsHTConst v p (φ κ) ∧ κ ∣ (p : A) ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.isHTConst_of_isCp | exact GlobalTheory.CompanionTheory.Ar.HT.isHTConst_of_isCp | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.isHTConst_of_isCp <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PowTwoSymplecticRelation
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PowTwoSymplecticRelation
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Conj

theorem pow_sy_exchange : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (n : ℕ), pow2 B n * B.sy ^ n = ev (n := 2) ![pt R d 0, comp1 (B.A.act (n : O)) (pt R d 1)] B.sy * ev (n := 2) ![pt R d 1, pt R d 0] (pow1 B n) :=
  @PositivityTheory.HtPt.Cc.pow_sy

end GlobalTheory.CompanionTheory.Ar.Conj
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PowTwoSymplecticRelationStatement
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pow_two_symplectic_relation : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (n : ℕ), pow2 B n * B.sy ^ n = ev (n := 2) ![pt R d 0, comp1 (B.A.act (n : O)) (pt R d 1)] B.sy * ev (n := 2) ![pt R d 1, pt R d 0] (pow1 B n) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.pow_sy_exchange | exact GlobalTheory.CompanionTheory.Ar.Conj.pow_sy_exchange | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.pow_sy_exchange <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PowOnePowTwoCommutation
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PowOnePowTwoCommutation
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Conj

theorem pow_interchange : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (m n : ℕ), pow2 B n ^ m * ev (n := 2) ![pt R d 0, comp1 (B.A.act (n : O)) (pt R d 1)] (pow1 B m) = pow1 B m ^ n * ev (n := 2) ![comp1 (B.A.act (m : O)) (pt R d 0), pt R d 1] (pow2 B n) :=
  PositivityTheory.HtPt.Cc.pow_inter

end GlobalTheory.CompanionTheory.Ar.Conj
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PowOnePowTwoCommutationStatement
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pow_one_pow_two_commutation : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (m n : ℕ), pow2 B n ^ m * ev (n := 2) ![pt R d 0, comp1 (B.A.act (n : O)) (pt R d 1)] (pow1 B m) = pow1 B m ^ n * ev (n := 2) ![comp1 (B.A.act (m : O)) (pt R d 0), pt R d 1] (pow2 B n) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.pow_interchange | exact GlobalTheory.CompanionTheory.Ar.Conj.pow_interchange | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.pow_interchange <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocalComparisonOfOrbitsHolds
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocalComparisonOfOrbitsHolds
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num NumberField

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem orbit_map_pow {A B : Type} (e : A → B) (a : Equiv.Perm A) (b : Equiv.Perm B)
    (he : ∀ t, e (a t) = b (e t)) (n : ℕ) (t : A) : e ((a ^ n) t) = (b ^ n) (e t) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, he, ih]

theorem local_comparison_of_orbits : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Sg : Type) [Fintype Sg] [DecidableEq Sg] (P : Ideal (MRing ι O)) (d p : ℕ), 2 ≤ p → ∀ (φ : Equiv.Perm Sg) (r s : Sg → ℕ) (lie : ∀ τ, LocPair ι O (Fin (r τ))) (om : ∀ τ, LocPair ι O (Fin (s τ))), (∀ τ, ∃ (Sg' : Type) (_ : Finite Sg') (e : Sg' → Sg) (φ' : Equiv.Perm Sg'), τ ∈ Set.range e ∧ (∀ t, e (φ' t) = φ (e t)) ∧ Relations (r := fun t => r (e t)) (s := fun t => s (e t)) P d p φ' (fun t => lie (e t)) (fun t => om (e t))) → LabelChernComparison P d p φ lie om := by
  intro O _ _ _ K _ _ ι _ Sg _ _ P d p hp φ r s lie om hrel k hk Q hQ τ
  obtain ⟨Sg', hfin, e, φ', ⟨t0, ht0⟩, hcomm, hR⟩ := hrel τ
  subst ht0
  haveI : Fintype Sg' := Fintype.ofFinite Sg'
  obtain ⟨h, h1, h2⟩ := hR k hk Q hQ
  obtain ⟨La, hLa⟩ : ∃ La : Sg → ℝ, La = fun σ => ((laNum P (p : O) (lie σ).x k Q : ℤ) : ℝ) := ⟨_, rfl⟩
  have hLa' : ∀ σ, La σ = ((laNum P (p : O) (lie σ).x k Q : ℤ) : ℝ) := fun σ => by rw [hLa]
  have h1' : ∀ t, (((lie (e t)).ck P k Q : ℤ) : ℝ) + (((om (e t)).ck P k Q : ℤ) : ℝ)
      = h t - ((laNum P (p : O) (lie (e t)).x k Q : ℤ) : ℝ) / ((p : ℝ) - 1) := fun t => h1 t
  have h2' : ∀ t, (p : ℝ) ^ k * h t = h (φ' t) + La (e (φ' t)) := by
    intro t
    rw [hLa']
    exact h2 t
  have hp1 : (1 : ℝ) < (p : ℝ) := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  have hpk : (1 : ℝ) < (p : ℝ) ^ k := one_lt_pow₀ hp1 (by omega)
  have hpk0 : (p : ℝ) ^ k ≠ 0 := (zero_lt_one.trans hpk).ne'
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = ((p : ℝ) ^ k)⁻¹ := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by
    rw [hc]
    exact inv_nonneg.mpr (zero_lt_one.trans hpk).le
  have hc1 : c < 1 := by
    rw [hc]
    exact inv_lt_one_of_one_lt₀ hpk
  have hrec : ∀ t, h t = c * (h (φ' t) + La (e (φ' t))) := by
    intro t
    rw [hc, ← h2' t, ← mul_assoc, inv_mul_cancel₀ hpk0, one_mul]
  have hpart : ∀ N t, h t = (∑ n ∈ Finset.range N, c ^ (n + 1) * La (e ((φ' ^ (n + 1)) t)))
      + c ^ N * h ((φ' ^ N) t) := by
    intro N
    induction N with
    | zero => intro t; simp
    | succ N ih =>
      intro t
      have hstep : φ' ((φ' ^ N) t) = (φ' ^ (N + 1)) t := by
        rw [pow_succ', Equiv.Perm.mul_apply]
      rw [ih t, Finset.sum_range_succ, hrec ((φ' ^ N) t), hstep]
      ring
  have hbd : ∀ f : Sg' → ℝ, ∀ t, |f t| ≤ ∑ u, |f u| := fun f t =>
    Finset.single_le_sum (f := fun u => |f u|) (fun u _ => abs_nonneg (f u)) (Finset.mem_univ t)
  have hsum : Summable (fun n : ℕ => c ^ (n + 1) * La (e ((φ' ^ (n + 1)) t0))) := by
    have hg : Summable (fun n : ℕ => (∑ u, |La (e u)|) * c ^ (n + 1)) := by
      refine ((summable_geometric_of_lt_one hc0 hc1).mul_left ((∑ u, |La (e u)|) * c)).congr
        (fun n => ?_)
      ring
    refine Summable.of_norm_bounded (g := fun n : ℕ => (∑ u, |La (e u)|) * c ^ (n + 1)) hg
      (fun n => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hc0 _), mul_comm (∑ u, |La (e u)|)]
    exact mul_le_mul_of_nonneg_left (hbd (fun u => La (e u)) _) (pow_nonneg hc0 _)
  have hlim1 : Filter.Tendsto (fun N => ∑ n ∈ Finset.range N, c ^ (n + 1) * La (e ((φ' ^ (n + 1)) t0)))
      Filter.atTop (nhds (∑' n, c ^ (n + 1) * La (e ((φ' ^ (n + 1)) t0)))) :=
    hsum.hasSum.tendsto_sum_nat
  have hz : Filter.Tendsto (fun N : ℕ => c ^ N * h ((φ' ^ N) t0)) Filter.atTop (nhds 0) := by
    have hg : Filter.Tendsto (fun N : ℕ => (∑ u, |h u|) * c ^ N) Filter.atTop (nhds 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).const_mul (∑ u, |h u|)
      rw [mul_zero] at this
      exact this
    refine squeeze_zero_norm (fun N => ?_) hg
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hc0 _), mul_comm (∑ u, |h u|)]
    exact mul_le_mul_of_nonneg_left (hbd h _) (pow_nonneg hc0 _)
  have hlim2 : Filter.Tendsto (fun N => ∑ n ∈ Finset.range N, c ^ (n + 1) * La (e ((φ' ^ (n + 1)) t0)))
      Filter.atTop (nhds (h t0)) := by
    have hconst : Filter.Tendsto (fun _ : ℕ => h t0) Filter.atTop (nhds (h t0)) := tendsto_const_nhds
    have := hconst.sub hz
    rw [sub_zero] at this
    refine this.congr (fun N => ?_)
    rw [hpart N t0]
    ring
  have hh : h t0 = ∑' n, c ^ (n + 1) * La (e ((φ' ^ (n + 1)) t0)) := tendsto_nhds_unique hlim2 hlim1
  have hh2 : h t0 = ∑' n : ℕ, ((p : ℝ) ^ k)⁻¹ ^ (n + 1) * La ((φ ^ (n + 1)) (e t0)) := by
    rw [hh, hc]
    refine tsum_congr (fun n => ?_)
    rw [orbit_map_pow e φ' φ hcomm]
  have key := (co_series_three_step).1 Sg φ p k hp hk La (e t0)
  have final : (((lie (e t0)).ck P k Q : ℤ) : ℝ) + (((om (e t0)).ck P k Q : ℤ) : ℝ)
      = ∑ σ, GroundTheory.Heights₂.Heights.ModelLeaves.co φ p k (e t0) σ * La σ := by
    rw [key, h1' t0, hh2, hLa' (e t0)]
  subst hLa
  exact final

end GlobalTheory.CompanionTheory.Ar.Num
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocalComparisonOfOrbitsHoldsStatement
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_comparison_of_orbits_holds : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Sg : Type) [Fintype Sg] [DecidableEq Sg] (P : Ideal (MRing ι O)) (d p : ℕ), 2 ≤ p → ∀ (φ : Equiv.Perm Sg) (r s : Sg → ℕ) (lie : ∀ τ, LocPair ι O (Fin (r τ))) (om : ∀ τ, LocPair ι O (Fin (s τ))), (∀ τ, ∃ (Sg' : Type) (_ : Finite Sg') (e : Sg' → Sg) (φ' : Equiv.Perm Sg'), τ ∈ Set.range e ∧ (∀ t, e (φ' t) = φ (e t)) ∧ Relations (r := fun t => r (e t)) (s := fun t => s (e t)) P d p φ' (fun t => lie (e t)) (fun t => om (e t))) → LabelChernComparison P d p φ lie om := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.local_comparison_of_orbits | exact GlobalTheory.CompanionTheory.Ar.Num.local_comparison_of_orbits | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.local_comparison_of_orbits <;> assumption)
end
end
