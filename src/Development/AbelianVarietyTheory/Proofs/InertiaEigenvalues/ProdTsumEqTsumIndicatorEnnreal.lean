module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalBasic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfIdem
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvariantImageOpenClosedLocalSections
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedStandardAddCharConductorProperties
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ValIrreducible
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualHermitianLatticeBasisExists
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DltEqZero
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueFixedPointOfAdicContraction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TsumExpNegAbsIntLtTop

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProdTsumEqTsumIndicatorEnnreal
open Filter Topology
open scoped ENNReal

namespace GlobalTheory.EulerSum

variable {I X : Type} [Zero X]

noncomputable def ofFinset (S : Finset I) (y : S → X) : I →₀ X := by
  classical
  exact Finsupp.onFinset S (fun i => if h : i ∈ S then y ⟨i, h⟩ else 0) (by
    intro i hi; by_contra h; exact hi (dif_neg h))

theorem ofFinset_apply (S : Finset I) (y : S → X) (i : S) : ofFinset S y i = y i := by
  classical
  simp [ofFinset, Finsupp.onFinset_apply, i.2]

theorem ofFinset_apply_of_notMem (S : Finset I) (y : S → X) {i : I} (h : i ∉ S) :
    ofFinset S y i = 0 := by
  classical
  simp [ofFinset, Finsupp.onFinset_apply, h]

theorem ofFinset_injective (S : Finset I) : Function.Injective (ofFinset (X := X) S) := by
  intro y z h; funext i; rw [← ofFinset_apply S y i, ← ofFinset_apply S z i, h]

theorem support_ofFinset_subset (S : Finset I) (y : S → X) : (ofFinset S y).support ⊆ S := by
  intro i hi
  by_contra h
  exact (Finsupp.mem_support_iff.1 hi) (ofFinset_apply_of_notMem S y h)

theorem mem_range_ofFinset (S : Finset I) (l : I →₀ X) (hl : l.support ⊆ S) :
    l ∈ Set.range (ofFinset S) := by
  refine ⟨fun i => l i, ?_⟩
  ext i
  by_cases h : i ∈ S
  · exact ofFinset_apply S _ ⟨i, h⟩
  · rw [ofFinset_apply_of_notMem S _ h]
    exact (Finsupp.notMem_support_iff.1 (fun hi => h (hl hi))).symm

theorem prod_ofFinset {M : Type} [CommMonoid M] (f : I → X → M) (hf0 : ∀ v, f v 0 = 1)
    (S : Finset I) (y : S → X) : (ofFinset S y).prod f = ∏ i : S, f i (y i) := by
  rw [Finsupp.prod_of_support_subset _ (support_ofFinset_subset S y) f (fun i _ => hf0 i),
    ← Finset.prod_coe_sort S]
  exact Finset.prod_congr rfl fun i _ => by rw [ofFinset_apply]

theorem tsum_indicator_support_subset {R : Type} [CommSemiring R] [TopologicalSpace R]
    (f : I → X → R) (hf0 : ∀ v, f v 0 = 1) (S : Finset I) :
    ∑' l : I →₀ X, ({l : I →₀ X | l.support ⊆ S}.indicator (fun l => l.prod f) l) =
      ∑' y : S → X, ∏ i : S, f i (y i) := by
  refine ((ofFinset_injective S).tsum_eq ?_).symm.trans ?_
  · intro l hl
    by_contra h
    exact hl (Set.indicator_of_notMem (fun hs => h (mem_range_ofFinset S l hs)) _)
  · refine tsum_congr fun y => ?_
    rw [Set.indicator_of_mem (show ofFinset S y ∈ {l : I →₀ X | l.support ⊆ S} from
      support_ofFinset_subset S y), prod_ofFinset f hf0]

theorem prod_tsum_eq_tsum_indicator_ennreal (f : I → X → ℝ≥0∞) (hf0 : ∀ v, f v 0 = 1)
    (S : Finset I) :
    ∏ v ∈ S, ∑' x, f v x =
      ∑' l : I →₀ X, ({l : I →₀ X | l.support ⊆ S}.indicator (fun l => l.prod f) l) := by
  rw [tsum_indicator_support_subset f hf0 S,
    GlobalTheory.VolBoxMajorant.tsum_pi_prod_ennreal' (fun (i : S) x => f i x),
    Finset.prod_coe_sort S (fun v => ∑' x, f v x)]

theorem prod_tsum_eq_tsum_indicator (f : I → X → ℂ) (hf0 : ∀ v, f v 0 = 1)
    (hv : ∀ v, Summable fun x => ‖f v x‖) (S : Finset I) :
    ∏ v ∈ S, ∑' x, f v x =
      ∑' l : I →₀ X, ({l : I →₀ X | l.support ⊆ S}.indicator (fun l => l.prod f) l) := by
  classical
  rw [tsum_indicator_support_subset f hf0 S,
    (GlobalTheory.hasSum_pi_prod_of_summable_norm S (fun _ => X) (fun i x => f i x)
      (fun i => hv i)).tsum_eq,
    Finset.prod_coe_sort S (fun v => ∑' x, f v x)]

theorem hasProd_tsum_finsupp_ennreal (f : I → X → ℝ≥0∞) (hf0 : ∀ v, f v 0 = 1) :
    HasProd (fun v => ∑' x, f v x) (∑' l : I →₀ X, l.prod f) := by
  classical
  have hmono : Monotone (fun S : Finset I => ∏ v ∈ S, ∑' x, f v x) := by
    intro S T hST
    exact Finset.prod_le_prod_of_subset_of_one_le' hST
      (fun v _ _ => (hf0 v).symm.le.trans (ENNReal.le_tsum 0))
  have hsup : ⨆ S : Finset I, ∏ v ∈ S, ∑' x, f v x = ∑' l : I →₀ X, l.prod f := by
    simp_rw [prod_tsum_eq_tsum_indicator_ennreal f hf0]
    refine le_antisymm (iSup_le fun S => ENNReal.tsum_le_tsum fun l => ?_) ?_
    · exact Set.indicator_le_self _ _ l
    · rw [ENNReal.tsum_eq_iSup_sum]
      refine iSup_le fun T => le_iSup_of_le (T.biUnion Finsupp.support) ?_
      calc ∑ l ∈ T, l.prod f
          = ∑ l ∈ T, ({l : I →₀ X | l.support ⊆ T.biUnion Finsupp.support}.indicator
              (fun l => l.prod f) l) :=
            Finset.sum_congr rfl fun l hl =>
              (Set.indicator_of_mem (show l ∈ {l : I →₀ X | l.support ⊆ T.biUnion Finsupp.support}
                from Finset.subset_biUnion_of_mem Finsupp.support hl) (fun l : I →₀ X => l.prod f)).symm
        _ ≤ _ := ENNReal.sum_le_tsum T
  have := tendsto_atTop_iSup hmono
  rw [hsup] at this
  exact this

theorem tsum_finsupp_eq_tprod_ennreal (f : I → X → ℝ≥0∞) (hf0 : ∀ v, f v 0 = 1) :
    ∑' l : I →₀ X, l.prod f = ∏' v, ∑' x, f v x :=
  (hasProd_tsum_finsupp_ennreal f hf0).tprod_eq.symm

theorem summable_norm_local (f : I → X → ℂ)
    (hsum : Summable fun p : I × {x : X // x ≠ 0} => ‖f p.1 p.2‖) (v : I) :
    Summable fun x => ‖f v x‖ := by
  have h1 : Summable fun x : {x : X // x ≠ 0} => ‖f v x‖ :=
    ((summable_prod_of_nonneg fun _ => norm_nonneg _).1 hsum).1 v
  haveI : Finite ↥({x : X | x ≠ 0}ᶜ) :=
    ((Set.finite_singleton (0 : X)).subset (by intro x hx; simpa using hx)).to_subtype
  exact (summable_subtype_and_compl (s := {x : X | x ≠ 0})).1 ⟨h1, Summable.of_finite⟩

theorem summable_norm_finsupp_prod (f : I → X → ℂ) (hf0 : ∀ v, f v 0 = 1)
    (hsum : Summable fun p : I × {x : X // x ≠ 0} => ‖f p.1 p.2‖) :
    Summable fun l : I →₀ X => ‖l.prod f‖ := by
  classical
  have hP := (summable_prod_of_nonneg fun _ => norm_nonneg _).1 hsum
  let a : I → ℝ := fun v => ∑' x : {x : X // x ≠ 0}, ‖f v x‖
  have hA : Summable a := hP.2
  have ha0 : ∀ v, 0 ≤ a v := fun v => tsum_nonneg fun _ => norm_nonneg _
  let g : I → X → ℝ≥0∞ := fun v x => ENNReal.ofReal ‖f v x‖
  have hg0 : ∀ v, g v 0 = 1 := by intro v; simp [g, hf0 v]
  have hgv : ∀ v, ∑' x, g v x = ENNReal.ofReal (1 + a v) := by
    intro v
    rw [ENNReal.tsum_eq_add_tsum_ite 0, hg0, ENNReal.ofReal_add zero_le_one (ha0 v),
      ENNReal.ofReal_one, ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (hP.1 v)]
    congr 1
    refine Eq.trans ?_ (tsum_subtype {x : X | x ≠ 0} (fun x => ENNReal.ofReal ‖f v x‖)).symm
    refine tsum_congr fun x => ?_
    by_cases hx : x = 0 <;> simp [hx, g]
  have hprod : ∀ l : I →₀ X, ENNReal.ofReal ‖l.prod f‖ = l.prod g := by
    intro l
    simp only [Finsupp.prod, norm_prod, g]
    exact ENNReal.ofReal_prod_of_nonneg fun _ _ => norm_nonneg _
  refine summable_of_sum_le (c := Real.exp (∑' v, a v)) (fun _ => norm_nonneg _) fun T => ?_
  have hS := prod_tsum_eq_tsum_indicator_ennreal g hg0 (T.biUnion Finsupp.support)
  rw [← ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le,
    ENNReal.ofReal_sum_of_nonneg fun _ _ => norm_nonneg _]
  calc ∑ l ∈ T, ENNReal.ofReal ‖l.prod f‖
      = ∑ l ∈ T, ({l : I →₀ X | l.support ⊆ T.biUnion Finsupp.support}.indicator
          (fun l => l.prod g) l) :=
        Finset.sum_congr rfl fun l hl => by
          rw [hprod, Set.indicator_of_mem (show l ∈ {l : I →₀ X | l.support ⊆ T.biUnion Finsupp.support}
            from Finset.subset_biUnion_of_mem Finsupp.support hl) (fun l : I →₀ X => l.prod g)]
    _ ≤ _ := ENNReal.sum_le_tsum T
    _ = ∏ v ∈ T.biUnion Finsupp.support, ∑' x, g v x := hS.symm
    _ = ENNReal.ofReal (∏ v ∈ T.biUnion Finsupp.support, (1 + a v)) := by
        rw [ENNReal.ofReal_prod_of_nonneg fun v _ => by linarith [ha0 v]]
        exact Finset.prod_congr rfl fun v _ => hgv v
    _ ≤ ENNReal.ofReal (Real.exp (∑' v, a v)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        calc ∏ v ∈ T.biUnion Finsupp.support, (1 + a v)
            ≤ ∏ v ∈ T.biUnion Finsupp.support, Real.exp (a v) :=
              Finset.prod_le_prod₀ (fun v _ => by linarith [ha0 v])
                fun v _ => by linarith [Real.add_one_le_exp (a v)]
          _ = Real.exp (∑ v ∈ T.biUnion Finsupp.support, a v) := (Real.exp_sum _ _).symm
          _ ≤ Real.exp (∑' v, a v) := Real.exp_le_exp.2 (hA.sum_le_tsum _ (fun v _ => ha0 v))

theorem hasProd_tsum_finsupp (f : I → X → ℂ) (hf0 : ∀ v, f v 0 = 1)
    (hsum : Summable fun p : I × {x : X // x ≠ 0} => ‖f p.1 p.2‖) :
    HasProd (fun v => ∑' x, f v x) (∑' l : I →₀ X, l.prod f) := by
  classical
  have hN := summable_norm_finsupp_prod f hf0 hsum
  have key : (fun S : Finset I => ∏ v ∈ S, ∑' x, f v x) = fun S =>
      ∑' l : I →₀ X, ({l : I →₀ X | l.support ⊆ S}.indicator (fun l => l.prod f) l) :=
    funext (prod_tsum_eq_tsum_indicator f hf0 (summable_norm_local f hsum))
  show Tendsto (fun S : Finset I => ∏ v ∈ S, ∑' x, f v x) atTop _
  rw [key]
  refine tendsto_tsum_of_dominated_convergence (bound := fun l : I →₀ X => ‖l.prod f‖) hN
    (fun l => ?_) (Eventually.of_forall fun S l => norm_indicator_le_norm_self _ _)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop l.support] with S hS
  exact (Set.indicator_of_mem (show l ∈ {l : I →₀ X | l.support ⊆ S} from hS)
    (fun l : I →₀ X => l.prod f)).symm

theorem euler_product_intVec {I : Type} (n : ℕ) (f : I → (Fin n → ℤ) → ℂ)
    (hf0 : ∀ v, f v 0 = 1)
    (hsum : Summable fun p : I × {x : Fin n → ℤ // x ≠ 0} => ‖f p.1 p.2‖) :
    (Summable fun l : I →₀ (Fin n → ℤ) => ‖l.prod f‖) ∧
      HasProd (fun v => ∑' x, f v x) (∑' l : I →₀ (Fin n → ℤ), l.prod f) ∧
      ∑' l : I →₀ (Fin n → ℤ), l.prod f = ∏' v, ∑' x, f v x :=
  ⟨summable_norm_finsupp_prod f hf0 hsum, hasProd_tsum_finsupp f hf0 hsum,
    (hasProd_tsum_finsupp f hf0 hsum).tprod_eq.symm⟩

theorem euler_product_intVec_ennreal {I : Type} (n : ℕ) (f : I → (Fin n → ℤ) → ℝ≥0∞)
    (hf0 : ∀ v, f v 0 = 1) :
    HasProd (fun v => ∑' x, f v x) (∑' l : I →₀ (Fin n → ℤ), l.prod f) ∧
      ∑' l : I →₀ (Fin n → ℤ), l.prod f = ∏' v, ∑' x, f v x :=
  ⟨hasProd_tsum_finsupp_ennreal f hf0, tsum_finsupp_eq_tprod_ennreal f hf0⟩

end GlobalTheory.EulerSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardResidueFieldAdjoinUnitaryProd
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardResidueFieldAdjoinUnitaryProd
noncomputable section

namespace GlobalTheory.UnitLemma.ResDeg

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Orbit Polynomial IsLocalRing

theorem odd_of_involution {k₀ k : Type} [Field k₀] [Field k] [Fintype k₀] [Finite k] (ι : k₀ →+* k) (q d : ℕ)
    (h0 : Fintype.card k₀ = q ^ 2) (hk : Nat.card k = q ^ (2 * d)) (τ : k ≃+* k) (hτ : ∀ z, τ (τ z) = z)
    (x y : k₀) (hxy : τ (ι x) = ι y) (hne : x ≠ y) : Odd d := by
  classical
  have hfix : ∀ m : ℕ, τ (ι x) ≠ (ι x) ^ (q ^ (2 * m)) := by
    intro m h
    rw [← map_pow, pow_mul, ← h0, FiniteField.pow_card_pow, hxy] at h
    exact hne (ι.injective h).symm
  letI := Fintype.ofFinite k
  obtain ⟨p, hchar⟩ := CharP.exists k
  haveI := hchar
  haveI : Fact p.Prime := ⟨CharP.char_is_prime k p⟩
  letI : Algebra (ZMod p) k := ZMod.algebra k p
  let τA : k ≃ₐ[ZMod p] k := AlgEquiv.ofRingEquiv (f := τ) (fun r => by
    have := RingHom.ext_zmod ((τ : k →+* k).comp (algebraMap (ZMod p) k)) (algebraMap (ZMod p) k)
    exact DFunLike.congr_fun this r)
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod p) k).2 τA
  have hord := FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic (ZMod p) k
  have hsq : τA ^ 2 = 1 := AlgEquiv.ext fun z => hτ z
  have hdvd : Module.finrank (ZMod p) k ∣ 2 * n.1 := by
    have := orderOf_dvd_iff_pow_eq_one.2
      (show FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) k ^ (2 * n.1) = 1 by
        rw [pow_mul']; exact (congrArg (· ^ 2) hn).trans hsq)
    rwa [hord] at this
  have hcard : Fintype.card k = p ^ Module.finrank (ZMod p) k := by
    rw [Module.card_eq_pow_finrank (K := ZMod p), ZMod.card]
  have hτz : ∀ z, τ z = z ^ (p ^ n.1) := by
    intro z
    have h1 := DFunLike.congr_fun hn z
    simp only at h1
    rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate, ZMod.card] at h1
    exact h1.symm
  have hN := n.2
  obtain ⟨c, hc⟩ := hdvd
  have hc2 : c < 2 := by
    by_contra hh
    push_neg at hh
    nlinarith
  interval_cases c
  · exfalso
    have hn0 : n.1 = 0 := by omega
    apply hfix 0
    rw [hτz, hn0]; simp
  · have hpq : p ^ n.1 = q ^ d := by
      have e1 : p ^ (2 * n.1) = q ^ (2 * d) := by
        rw [← hk, Nat.card_eq_fintype_card, hcard, hc, mul_one]
      have e : (p ^ n.1) ^ 2 = (q ^ d) ^ 2 := by
        rw [← pow_mul, ← pow_mul, mul_comm n.1 2, mul_comm d 2]; exact e1
      exact Nat.pow_left_injective two_ne_zero e
    by_contra hodd
    obtain ⟨m, hm⟩ := Nat.not_odd_iff_even.1 hodd
    apply hfix m
    rw [hτz, hpq, hm, two_mul]

end GlobalTheory.UnitLemma.ResDeg

namespace GlobalTheory.UnitLemma.ResDeg

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Orbit Polynomial IsLocalRing

variable {K : UQ}

def sigmaAdj (B : InvAlg K) (hu : B.g * B.σ B.g = 1) (hi : IsIntegral K.O B.g) :
    Algebra.adjoin K.O ({B.g} : Set B.A) ≃+* Algebra.adjoin K.O ({B.g} : Set B.A) where
  toFun y := ⟨B.σ (y : B.A), adjoin_stable B hu hi y.2⟩
  invFun y := ⟨B.σ (y : B.A), adjoin_stable B hu hi y.2⟩
  left_inv y := Subtype.ext (B.σ_σ (y : B.A))
  right_inv y := Subtype.ext (B.σ_σ (y : B.A))
  map_mul' x y := Subtype.ext (map_mul B.σ (x : B.A) (y : B.A))
  map_add' x y := Subtype.ext (map_add B.σ (x : B.A) (y : B.A))

theorem card_residueField (B : InvAlg K) (hu : B.g * B.σ B.g = 1) (hi : IsIntegral K.O B.g)
    (hl : IsLocalRing (Algebra.adjoin K.O ({B.g} : Set B.A))) :
    ∃ d : ℕ, Odd d ∧
      Nat.card (@IsLocalRing.ResidueField (Algebra.adjoin K.O ({B.g} : Set B.A)) _ hl) = K.q ^ (2 * d) := by
  set_option synthInstance.maxHeartbeats 200000 in
  classical
  haveI := hl
  haveI : Module.Finite K.O (Algebra.adjoin K.O ({B.g} : Set B.A)) :=
    Module.Finite.iff_fg.mpr hi.fg_adjoin_singleton
  letI : Fintype (ResidueField K.O) := Fintype.ofFinite _
  haveI : Finite (ResidueField (Algebra.adjoin K.O ({B.g} : Set B.A))) :=
    Module.finite_of_finite (ResidueField K.O)
  letI : Fintype (ResidueField (Algebra.adjoin K.O ({B.g} : Set B.A))) := Fintype.ofFinite _
  set τ := ResidueField.mapEquiv (sigmaAdj B hu hi)
  have hτ : ∀ z, τ (τ z) = z := by
    intro z
    obtain ⟨r, rfl⟩ := residue_surjective z
    simp only [τ, ResidueField.mapEquiv_apply, ResidueField.map_residue]
    congr 1
    exact Subtype.ext (B.σ_σ r)
  obtain ⟨x, y, hxy, hne⟩ := K.c_res
  refine ⟨Module.finrank (ResidueField K.O) (ResidueField (Algebra.adjoin K.O ({B.g} : Set B.A))),
    odd_of_involution (algebraMap (ResidueField K.O) _) K.q _ ?_ ?_ τ hτ (residue K.O x) (residue K.O y) ?_ ?_, ?_⟩
  · rw [← K.card_res, Nat.card_eq_fintype_card]
  · rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ResidueField K.O), ← Nat.card_eq_fintype_card,
      K.card_res, pow_mul]
  · show ResidueField.map _ (residue _ (algebraMap K.O _ x)) = residue _ (algebraMap K.O _ y)
    rw [ResidueField.map_residue]
    congr 1
    apply Subtype.ext
    change B.σ (algebraMap K.O B.A x) = algebraMap K.O B.A y
    rw [IsScalarTower.algebraMap_apply K.O K.E B.A, B.σ_alg, hxy, ← IsScalarTower.algebraMap_apply]
  · intro h
    exact hne (Ideal.Quotient.eq.1 h)
  · rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ResidueField K.O), ← Nat.card_eq_fintype_card,
      K.card_res, pow_mul]

theorem card_residueField_prod : ∀ (K : UQ), K.Odd → ∀ B₁ B₂ : InvAlg K, B₁.g * B₁.σ B₁.g = 1 →
    B₂.g * B₂.σ B₂.g = 1 → (B₁.P * B₂.P).Separable → IsIntegral K.O B₁.g → IsIntegral K.O B₂.g →
    ∀ hl : IsLocalRing (Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A)),
      ∃ d : ℕ, Odd d ∧ Nat.card (@IsLocalRing.ResidueField
        (Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A)) _ hl) = K.q ^ (2 * d) := by
  intro K _ B₁ B₂ h₁ h₂ _ i₁ i₂ hl
  exact card_residueField (B₁.prod B₂) (Prod.ext h₁ h₂) (IsIntegral.pair i₁ i₂) hl

end GlobalTheory.UnitLemma.ResDeg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardResidueFieldAdjoinUnitaryProdStatement
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_residueField_adjoin_unitary_prod : ∀ (K : UQ), K.Odd → ∀ B₁ B₂ : InvAlg K, B₁.g * B₁.σ B₁.g = 1 → B₂.g * B₂.σ B₂.g = 1 → (B₁.P * B₂.P).Separable → IsIntegral K.O B₁.g → IsIntegral K.O B₂.g → ∀ hl : IsLocalRing (Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A)), ∃ d : ℕ, Odd d ∧ Nat.card (@IsLocalRing.ResidueField (Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A)) _ hl) = K.q ^ (2 * d) := by
  first | exact @GlobalTheory.UnitLemma.ResDeg.card_residueField_prod | exact GlobalTheory.UnitLemma.ResDeg.card_residueField_prod | (intros; apply GlobalTheory.UnitLemma.ResDeg.card_residueField_prod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisOrbitalIntegrandIsLocallyConstantCo
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisOrbitalIntegrandIsLocallyConstantCo
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.OrbTest

theorem eta_eq_of_norm_eq {F : Type} [NormedField F] {x y : F} (h : ‖x‖ = ‖y‖) : eta x = eta y := by
  unfold eta
  by_cases hx : ∃ z : F, ‖x‖ = ‖z‖ ^ 2
  · rw [if_pos hx, if_pos (h ▸ hx)]
  · rw [if_neg hx, if_neg (h ▸ hx)]

theorem isLocallyConstant_eta_comp {X F : Type} [TopologicalSpace X] [NormedField F] [IsUltrametricDist F]
    (h : X → F) (hc : Continuous h) (h0 : ∀ x, h x ≠ 0) : IsLocallyConstant (fun x => eta (h x)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hx : 0 < ‖h x‖ := norm_pos_iff.mpr (h0 x)
  have hev : ∀ᶠ y in 𝓝 x, dist (h y) (h x) < ‖h x‖ := (hc.tendsto x) (Metric.ball_mem_nhds _ hx)
  filter_upwards [hev] with y hy
  apply eta_eq_of_norm_eq
  rw [dist_eq_norm] at hy
  have hy' : ‖h x - h y‖ < ‖h x‖ := by rwa [norm_sub_rev]
  have e1 : ‖h y‖ ≤ max ‖h y - h x‖ ‖h x‖ := by
    simpa using IsUltrametricDist.norm_add_le_max (h y - h x) (h x)
  have e2 : ‖h x‖ ≤ max ‖h x - h y‖ ‖h y‖ := by
    simpa using IsUltrametricDist.norm_add_le_max (h x - h y) (h y)
  apply le_antisymm
  · exact e1.trans (max_le hy.le le_rfl)
  · rcases le_total ‖h x - h y‖ ‖h y‖ with hh | hh
    · exact e2.trans (max_le hh le_rfl)
    · exact absurd (e2.trans (max_le le_rfl hh)) (not_le.mpr hy')

theorem continuous_act {r : ℕ} {k : Type} [CommRing k] [TopologicalSpace k] [IsTopologicalRing k] (Y : Gl r k) :
    Continuous (fun g : GL (Fin r) k => act g Y) := by
  unfold act
  refine Continuous.prodMk ?_ (Continuous.prodMk ?_ (Continuous.prodMk ?_ continuous_const))
  · exact (Units.continuous_val.matrix_mul continuous_const).matrix_mul Units.continuous_coe_inv
  · exact Units.continuous_val.matrix_mulVec continuous_const
  · exact continuous_const.matrix_vecMul Units.continuous_coe_inv

theorem actU_mul {r : ℕ} {F E : Type} [CommRing F] [CommRing E] [StarRing E] [Algebra F E]
    (g h : Matrix.unitaryGroup (Fin r) E) (X : Hn r F E) : actU (g * h) X = actU g (actU h X) := by
  unfold actU
  refine Prod.ext (Subtype.ext ?_) (Prod.ext ?_ rfl)
  · simp only [Submonoid.coe_mul, star_mul, Matrix.mul_assoc]
  · simp only [Submonoid.coe_mul, Matrix.mulVec_mulVec]

theorem continuous_actU {r : ℕ} {F E : Type} [CommRing F] [CommRing E] [StarRing E] [Algebra F E]
    [TopologicalSpace F] [TopologicalSpace E] [IsTopologicalRing E] [ContinuousStar E] (X : Hn r F E) :
    Continuous (fun g : Matrix.unitaryGroup (Fin r) E => actU g X) := by
  unfold actU
  refine Continuous.prodMk (Continuous.subtype_mk ?_ _) (Continuous.prodMk ?_ continuous_const)
  · exact (continuous_subtype_val.matrix_mul continuous_const).matrix_mul continuous_subtype_val.star
  · exact continuous_subtype_val.matrix_mulVec continuous_const

end GlobalTheory.JR.OrbTest

namespace GlobalTheory.JR.OrbTest

theorem isTest_orbG_integrand (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (f' : Gl r F → ℂ) (hf : IsTest f') (Y : Gl r F)
    (hY : Delta (inv Y) ≠ 0) :
    IsTest (fun g : GL (Fin r) F => f' (act g Y) * omega (act g Y)) := by
  haveI : IsUltrametricDist F := Unram.ultraF (E := E)
  obtain ⟨-, hL1b, hL1c, hL1d, hL1e⟩ := GlobalTheory.T.jacquetRallis_borderedMatrix_normalForm_invariants F r
  obtain ⟨hL6a, hL6b⟩ := GlobalTheory.T.jacquetRallis_transfer_factor_krylov_det F r
  obtain ⟨-, -, -, hL4⟩ := GlobalTheory.T.jacquetRallis_orbit_invariant_map_proper F E r
  have hC : (Cm Y).det ≠ 0 := by
    intro h0; apply hY; rw [Delta, ← hL1c Y, Matrix.det_mul, h0, zero_mul]
  have hld : (fun g : GL (Fin r) F => lastDet (act g Y)) = fun g =>
      (-1) ^ r * ((Cm Y).det * ((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F).det) := by
    funext g; rw [hL6a, hL6b, Matrix.det_mul]
  refine ⟨?_, ?_⟩
  · refine IsLocallyConstant.comp₂ (hf.1.comp_continuous (continuous_act Y)) ?_ (fun a b => a * b)
    show IsLocallyConstant (fun g : GL (Fin r) F => eta (lastDet (act g Y)))
    refine isLocallyConstant_eta_comp (fun g : GL (Fin r) F => lastDet (act g Y)) ?_ ?_
    · rw [hld]
      exact continuous_const.mul (continuous_const.mul Units.continuous_coe_inv.matrix_det)
    · intro g
      rw [show lastDet (act g Y) = _ from congrFun hld g]
      refine mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (mul_ne_zero hC ?_)
      exact ((Matrix.isUnit_iff_isUnit_det _).mp (g⁻¹).isUnit).ne_zero
  · have ha : Delta (inv (sec (inv Y))) ≠ 0 := by rw [hL1b]; exact hY
    obtain ⟨g₀, ⟨hg₀, -⟩, -⟩ := hL1e (sec (inv Y)) Y ha (hL1b _).symm
    have hS : IsCompact {h : GL (Fin r) F | act h (sec (inv Y)) ∈ tsupport f'} := by
      have := hL4 (tsupport f') {inv Y} hf.2 isCompact_singleton (by rintro b rfl; exact hY)
      convert this.image continuous_fst using 1
      ext h; constructor
      · intro hh; exact ⟨(h, inv Y), ⟨rfl, hh⟩, rfl⟩
      · rintro ⟨⟨h', a'⟩, ⟨ha', hc⟩, rfl⟩
        simp only [Set.mem_singleton_iff] at ha'; subst ha'; exact hc
    have hK : IsCompact {g : GL (Fin r) F | act g Y ∈ tsupport f'} := by
      have := (Homeomorph.mulRight g₀).isCompact_preimage.mpr hS
      convert this using 1
      ext g; simp [Homeomorph.coe_mulRight, hL1d, hg₀]
    refine HasCompactSupport.intro' hK ((isClosed_tsupport f').preimage (continuous_act Y)) ?_
    intro g hg
    simp only [Set.mem_setOf_eq] at hg
    simp only [image_eq_zero_of_notMem_tsupport hg, zero_mul]

theorem isTest_orbU_integrand (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (f : Hn r F E → ℂ) (hf : IsTest f) (a : Inv r F)
    (X : Hn r F E) (ha : Delta a ≠ 0) (hX : HasInv X a) :
    IsTest (fun g : Matrix.unitaryGroup (Fin r) E => f (actU g X)) := by
  haveI : ContinuousStar E := ⟨by
    have : Continuous (starAddEquiv : E ≃+ E) :=
      AddMonoidHomClass.continuous_of_bound (starAddEquiv : E ≃+ E) 1
        (fun x => by rw [starAddEquiv_apply, Unram.norm_star (F := F), one_mul])
    exact this⟩
  obtain ⟨-, -, hL5c, -⟩ := GlobalTheory.T.unitary_action_hermitian_invariants_transitive F E r
  obtain ⟨-, hL5iv⟩ := GlobalTheory.T.invariant_image_openClosed_local_sections F E r a ha
  obtain ⟨Ω, s, -, -, haΩ, -, hs, hprop⟩ := hL5iv ⟨X, hX⟩
  obtain ⟨g₀, hg₀, -⟩ := hL5c (s a) X a ha (hs a haΩ).2 hX
  refine ⟨hf.1.comp_continuous (continuous_actU X), ?_⟩
  have hS : IsCompact {h : Matrix.unitaryGroup (Fin r) E | actU h (s a) ∈ tsupport f} := by
    have h1 := (hprop (tsupport f) hf.2).inter_right (isClosed_univ.prod (isClosed_singleton (x := a)))
    convert h1.image continuous_fst using 1
    ext h; constructor
    · intro hh; exact ⟨(h, a), ⟨⟨haΩ, hh⟩, Set.mem_univ _, rfl⟩, rfl⟩
    · rintro ⟨⟨h', a'⟩, ⟨⟨-, hc⟩, -, ha'⟩, rfl⟩
      simp only [Set.mem_singleton_iff] at ha'; subst ha'; exact hc
  have hK : IsCompact {g : Matrix.unitaryGroup (Fin r) E | actU g X ∈ tsupport f} := by
    have := (Homeomorph.mulRight g₀).isCompact_preimage.mpr hS
    convert this using 1
    ext g; simp [Homeomorph.coe_mulRight, actU_mul, hg₀]
  refine HasCompactSupport.intro' hK ((isClosed_tsupport f).preimage (continuous_actU X)) ?_
  intro g hg
  simp only [Set.mem_setOf_eq] at hg
  exact image_eq_zero_of_notMem_tsupport hg

end GlobalTheory.JR.OrbTest


open GlobalTheory.JR.OrbTest in
theorem GlobalTheory.JR.orb_integrand_isTest : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E), (∀ (f' : Gl r F → ℂ), IsTest f' → ∀ Y : Gl r F, Delta (inv Y) ≠ 0 → IsTest (fun g : GL (Fin r) F => f' (act g Y) * omega (act g Y))) ∧ ∀ (f : Hn r F E → ℂ), IsTest f → ∀ (a : Inv r F) (X : Hn r F E), Delta a ≠ 0 → HasInv X a → IsTest (fun g : Matrix.unitaryGroup (Fin r) E => f (actU g X)) := by
  intro F E _ _ _ _ _ r _
  exact ⟨fun f' hf Y hY => isTest_orbG_integrand F E r f' hf Y hY,
    fun f hf a X ha hX => isTest_orbU_integrand F E r f hf a X ha hX⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisOrbitalIntegrandIsLocallyConstantCoStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquetRallis_orbitalIntegrand_isLocallyConstantCompactSupport : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E), (∀ (f' : Gl r F → ℂ), IsTest f' → ∀ Y : Gl r F, Delta (inv Y) ≠ 0 → IsTest (fun g : GL (Fin r) F => f' (act g Y) * omega (act g Y))) ∧ ∀ (f : Hn r F E → ℂ), IsTest f → ∀ (a : Inv r F) (X : Hn r F E), Delta a ≠ 0 → HasInv X a → IsTest (fun g : Matrix.unitaryGroup (Fin r) E => f (actU g X)) := by
  first | exact @GlobalTheory.JR.orb_integrand_isTest | exact GlobalTheory.JR.orb_integrand_isTest | (intros; apply GlobalTheory.JR.orb_integrand_isTest <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegerSpanningFamilyOfUnramifiedExt
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegerSpanningFamilyOfUnramifiedExt
noncomputable section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma IsDedekindDomain IsLocalRing

variable {K K' : UQ} {d : ℕ} {φ : K.E →+* K'.E}

theorem valuation_map_eq_of_unr (hU : IsUnrExt K K' d φ) (x : K.E) :
    (IsDiscreteValuationRing.maximalIdeal K'.O).valuation K'.E (φ x) =
      (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E x := by
  by_cases hx : x = 0
  · simp [hx]
  have h := hU.2.2.1 x
  unfold val at h
  have h0 : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E x ≠ 0 := by simpa using hx
  have h0' : (IsDiscreteValuationRing.maximalIdeal K'.O).valuation K'.E (φ x) ≠ 0 := by simpa using hx
  rw [← WithZero.exp_log h0, ← WithZero.exp_log h0']
  congr 1
  omega

theorem exists_intMap_of_unr (hU : IsUnrExt K K' d φ) :
    ∃ ψ : K.O →+* K'.O, ∀ a, algebraMap K'.O K'.E (ψ a) = φ (algebraMap K.O K.E a) := by
  choose f hf using exists_int_image hU
  have inj := IsFractionRing.injective K'.O K'.E
  let ψ : K.O →+* K'.O :=
    { toFun := f, map_one' := inj (by simp only [hf, map_one]),
      map_mul' := fun a b => inj (by simp only [hf, map_mul]),
      map_zero' := inj (by simp only [hf, map_zero]),
      map_add' := fun a b => inj (by simp only [hf, map_add (f := _)]) }
  exact ⟨ψ, hf⟩

theorem exists_int_basis_of_unr (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E) (hU : IsUnrExt K K' d φ) :
    ∃ u : Fin d → K'.O, ∀ y : K'.O, ∃ a : Fin d → K.O,
      algebraMap K'.O K'.E y = ∑ i, φ (algebraMap K.O K.E (a i)) * algebraMap K'.O K'.E (u i) := by
  classical
  obtain ⟨ψ, hψ⟩ := exists_intMap_of_unr hU
  have hv := valuation_map_eq_of_unr hU
  set v := (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E with hvdef
  set v' := (IsDiscreteValuationRing.maximalIdeal K'.O).valuation K'.E with hv'def

  have memK : ∀ a : K.O, a ∈ maximalIdeal K.O ↔ v (algebraMap K.O K.E a) < 1 := fun a =>
    (HeightOneSpectrum.valuation_lt_one_iff_mem (IsDiscreteValuationRing.maximalIdeal K.O) a).symm
  have memK' : ∀ a : K'.O, a ∈ maximalIdeal K'.O ↔ v' (algebraMap K'.O K'.E a) < 1 := fun a =>
    (HeightOneSpectrum.valuation_lt_one_iff_mem (IsDiscreteValuationRing.maximalIdeal K'.O) a).symm
  haveI : IsLocalHom ψ := ⟨fun a ha => by
    by_contra hna
    have h1 : a ∈ maximalIdeal K.O := (mem_maximalIdeal a).2 hna
    have h2 : ψ a ∈ maximalIdeal K'.O := by
      rw [memK', hψ, hv]; exact (memK a).1 h1
    exact (mem_maximalIdeal _).1 h2 ha⟩
  letI : Algebra (ResidueField K.O) (ResidueField K'.O) := (ResidueField.map ψ).toAlgebra
  letI : Fintype (ResidueField K.O) := Fintype.ofFinite _
  letI : Fintype (ResidueField K'.O) := Fintype.ofFinite _
  have hfr : Module.finrank (ResidueField K.O) (ResidueField K'.O) = d := by
    have h1 := Module.card_eq_pow_finrank (K := ResidueField K.O) (V := ResidueField K'.O)
    have c1 : Fintype.card (ResidueField K.O) = K.q ^ 2 := by
      rw [← Nat.card_eq_fintype_card]; exact K.card_res
    have c2 : Fintype.card (ResidueField K'.O) = (K.q ^ 2) ^ d := by
      rw [← Nat.card_eq_fintype_card, K'.card_res, hU.1, ← pow_mul, ← pow_mul, mul_comm]
    have h2 : 2 ≤ K.q ^ 2 := by
      rw [← c1]; exact Fintype.one_lt_card
    rw [c1, c2] at h1
    exact (Nat.pow_right_injective h2 h1).symm
  let b := Module.finBasisOfFinrankEq (ResidueField K.O) (ResidueField K'.O) hfr
  choose u hu using fun i => IsLocalRing.residue_surjective (b i)

  have hres : ∀ c : Fin d → K.O, ∀ j, c j = 1 → ∑ i, ψ (c i) * u i ∉ maximalIdeal K'.O := by
    intro c j hj hmem
    have h0 : residue K'.O (∑ i, ψ (c i) * u i) = 0 := (IsLocalRing.residue_eq_zero_iff _).2 hmem
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at h0
    simp only [map_mul, ← ResidueField.map_residue, hu] at h0
    have h1 : ∑ i, residue K.O (c i) • b i = 0 := by
      simpa only [Algebra.smul_def, RingHom.algebraMap_toAlgebra] using h0
    have := Fintype.linearIndependent_iff.1 b.linearIndependent _ h1 j
    rw [hj, map_one] at this
    exact one_ne_zero this

  set U : Fin d → K'.E := fun i => algebraMap K'.O K'.E (u i) with hUdef

  have key : ∀ e : Fin d → K.E, ∀ j, (∀ i, v (e i) ≤ v (e j)) → e j ≠ 0 →
      v (e j) ≤ v' (∑ i, φ (e i) * U i) := by
    intro e j hmax hj
    have hpos : 0 < v (e j) := zero_lt_iff.2 (by simpa using hj)
    have hc : ∀ i, ∃ a : K.O, algebraMap K.O K.E a = e i / e j := fun i =>
      IsDiscreteValuationRing.exists_lift_of_le_one (by
        rw [map_div₀]; exact (div_le_one₀ hpos).2 (hmax i))
    choose a ha using hc
    have haj : a j = 1 := IsFractionRing.injective K.O K.E (by rw [ha, div_self hj, map_one])
    have h1 := hres a j haj
    rw [memK', not_lt] at h1
    have h2 : algebraMap K'.O K'.E (∑ i, ψ (a i) * u i) = ∑ i, φ (e i / e j) * U i := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_mul, hψ, ha, hUdef]
    have h3 : ∑ i, φ (e i) * U i = φ (e j) * ∑ i, φ (e i / e j) * U i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← mul_assoc, ← map_mul, mul_div_cancel₀ _ hj]
    rw [h3, map_mul, hv, ← h2]
    exact le_mul_of_one_le_right' h1
  letI : Algebra K.E K'.E := φ.toAlgebra
  have hsmul : ∀ (x : K.E) (y : K'.E), x • y = φ x * y := fun x y => by
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  have hli : LinearIndependent K.E U := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    by_contra hi
    obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun i => v (g i)) ⟨i, Finset.mem_univ i⟩
    have hgi : 0 < v (g i) := zero_lt_iff.2 (by simpa using hi)
    have hgj : g j ≠ 0 := by
      intro h0
      have := hj i (Finset.mem_univ i)
      rw [h0, map_zero] at this
      exact absurd this (not_le.2 hgi)
    have := key g j (fun i => hj i (Finset.mem_univ i)) hgj
    simp only [← hsmul] at this
    rw [hg, map_zero] at this
    exact hgj ((map_eq_zero v).1 (le_antisymm this zero_le'))
  have hd : Module.finrank K.E K'.E = d := hU.2.2.2.2
  haveI : Nonempty (Fin d) := by
    have : 0 < d := hfr ▸ Module.finrank_pos
    exact ⟨⟨0, this⟩⟩
  have hspan := hli.span_eq_top_of_card_eq_finrank (by rw [Fintype.card_fin, hd])
  refine ⟨u, fun y => ?_⟩
  have hy : algebraMap K'.O K'.E y ∈ Submodule.span K.E (Set.range U) := hspan ▸ Submodule.mem_top
  obtain ⟨e, he⟩ := (Submodule.mem_span_range_iff_exists_fun K.E).1 hy
  have hint : ∀ i, v (e i) ≤ 1 := by
    intro i
    by_contra hi
    rw [not_le] at hi
    obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun i => v (e i)) ⟨i, Finset.mem_univ i⟩
    have hej : e j ≠ 0 := by
      intro h0
      have := hj i (Finset.mem_univ i)
      rw [h0, map_zero] at this
      exact absurd (lt_of_lt_of_le hi this) (not_lt.2 zero_le')
    have h1 := key e j (fun i => hj i (Finset.mem_univ i)) hej
    simp only [← hsmul] at h1
    rw [he] at h1
    have h2 := HeightOneSpectrum.valuation_le_one (IsDiscreteValuationRing.maximalIdeal K'.O) (K := K'.E) y
    exact absurd (lt_of_lt_of_le hi (le_trans (hj i (Finset.mem_univ i)) (le_trans h1 h2))) (lt_irrefl _)
  choose a ha using fun i => IsDiscreteValuationRing.exists_lift_of_le_one (hint i)
  refine ⟨a, ?_⟩
  rw [← he]
  simp only [hsmul, ha, hUdef]

end GlobalTheory.UnitLemma.Unr
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegerSpanningFamilyOfUnramifiedExtStatement
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integer_spanning_family_of_unramifiedExt : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∃ u : Fin d → K'.O, ∀ y : K'.O, ∃ a : Fin d → K.O, algebraMap K'.O K'.E y = ∑ i, φ (algebraMap K.O K.E (a i)) * algebraMap K'.O K'.E (u i) := by
  first | exact @GlobalTheory.UnitLemma.Unr.exists_int_basis_of_unr | exact GlobalTheory.UnitLemma.Unr.exists_int_basis_of_unr | (intros; apply GlobalTheory.UnitLemma.Unr.exists_int_basis_of_unr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceIntOfIsIntegral
noncomputable section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma Polynomial

theorem IsUnrExt.ne_zero {K K' : UQ} {d : ℕ} {φ : K.E →+* K'.E} (hU : IsUnrExt K K' d φ) : d ≠ 0 := by
  intro hd
  have h1 : Nat.card (IsLocalRing.ResidueField K'.O) = 1 := by
    rw [K'.card_res, hU.1, hd, pow_zero, one_pow]
  have h2 := Finite.one_lt_card (α := IsLocalRing.ResidueField K'.O)
  omega

theorem trace_int_of_isIntegral {K K' : UQ} {d : ℕ} {φ : K.E →+* K'.E} (hU : IsUnrExt K K' d φ) (z : K'.E)
    (hz : @IsIntegral K.O K'.E _ _ (φ.comp (algebraMap K.O K.E)).toAlgebra z) :
    ∃ a : K.O, @Algebra.trace K.E K'.E _ _ φ.toAlgebra z = algebraMap K.O K.E a := by
  letI : Algebra K.E K'.E := φ.toAlgebra
  letI : Algebra K.O K'.E := (φ.comp (algebraMap K.O K.E)).toAlgebra
  haveI : IsScalarTower K.O K.E K'.E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : FiniteDimensional K.E K'.E :=
    Module.finite_of_finrank_pos (by rw [hU.2.2.2.2]; exact Nat.pos_of_ne_zero hU.ne_zero)
  have h := Algebra.isIntegral_trace (R := K.O) (L := K.E) hz
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp h
  exact ⟨a, ha.symm⟩

end GlobalTheory.UnitLemma.Unr
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaGramDetEqOneOfSelfDualLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaGramDetEqOneOfSelfDualLattice
noncomputable section

namespace GlobalTheory.UnitLemma.Unimod

open GlobalTheory.UnitLemma Polynomial

theorem eta_gramDet_eq_one : ∀ (K : UQ) (B : InvAlg K) (x : B.A), B.σ x = x → (B.X x).Nonempty →
    K.eta (B.gramDet x) = 1 := by
  intro K B x hx ⟨L, hlat, _, hsd⟩
  obtain ⟨b, -, hb⟩ := GlobalTheory.T.self_dual_hermitian_lattice_basis_exists K B.A (B.herm x)
    (fun y y' z => by unfold InvAlg.herm; rw [mul_add, add_mul, map_add (f := _)])
    (fun e y z => Basic.herm_smul_left B x y z e)
    (fun y z => Basic.herm_symm B x hx y z) L hlat.1 hlat.2 hsd
  rw [← Orbit.eta_gram B x b]
  have h1 : (Matrix.of fun i j => B.herm x (b i) (b j)) = 1 := by
    ext i j; simp [hb, Matrix.one_apply]
  rw [h1, Matrix.det_one]
  simp [UQ.eta, val]

end GlobalTheory.UnitLemma.Unimod
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaGramDetEqOneOfSelfDualLatticeStatement
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eta_gramDet_eq_one_of_selfDual_lattice : ∀ (K : UQ) (B : InvAlg K) (x : B.A), B.σ x = x → (B.X x).Nonempty → K.eta (B.gramDet x) = 1 := by
  first | exact @GlobalTheory.UnitLemma.Unimod.eta_gramDet_eq_one | exact GlobalTheory.UnitLemma.Unimod.eta_gramDet_eq_one | (intros; apply GlobalTheory.UnitLemma.Unimod.eta_gramDet_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsReducedOfSeparableMarkedCharpoly
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsReducedOfSeparableMarkedCharpoly
namespace GlobalTheory.UnitLemma

open Polynomial

theorem InvAlg.isReduced_of_separable_P : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → IsReduced B.A := by
  intro K B h
  obtain ⟨e, he⟩ := exists_basis_pow_of_separable K B h
  have h2 : minpoly K.E (LinearMap.mulLeft K.E B.g) = minpoly K.E B.g :=
    minpoly.algHom_eq (Algebra.lmul K.E B.A) (Algebra.lmul_injective) B.g
  have hms : (minpoly K.E B.g).Separable :=
    h.of_dvd (h2 ▸ LinearMap.minpoly_dvd_charpoly (LinearMap.mulLeft K.E B.g))
  have hsurj : ∀ a : B.A, ∃ q : K.E[X], aeval B.g q = a := by
    intro a
    have hle : Submodule.span K.E (Set.range e) ≤
        Subalgebra.toSubmodule (Algebra.adjoin K.E ({B.g} : Set B.A)) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rw [he]
      exact Subalgebra.pow_mem (Algebra.adjoin K.E ({B.g} : Set B.A))
        (Algebra.subset_adjoin (Set.mem_singleton B.g)) _
    have ha : a ∈ Algebra.adjoin K.E ({B.g} : Set B.A) := hle (e.span_eq ▸ Submodule.mem_top)
    rw [Algebra.adjoin_singleton_eq_range_aeval] at ha
    obtain ⟨q, hq⟩ := ha
    exact ⟨q, hq⟩
  refine ⟨fun n hn => ?_⟩
  obtain ⟨k, hk⟩ := hn
  obtain ⟨q, rfl⟩ := hsurj n
  rcases Nat.eq_zero_or_pos k with h0 | h0
  · subst h0
    rw [pow_zero] at hk
    haveI := subsingleton_of_zero_eq_one hk.symm
    exact Subsingleton.elim _ _
  have hdk : minpoly K.E B.g ∣ q ^ k := minpoly.dvd _ _ (by rw [map_pow, hk])
  obtain ⟨r, hr⟩ := (hms.squarefree.dvd_pow_iff_dvd h0.ne').1 hdk
  rw [hr, map_mul, minpoly.aeval, zero_mul]

end GlobalTheory.UnitLemma
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsReducedOfSeparableMarkedCharpolyStatement
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isReduced_of_separable_markedCharpoly : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → IsReduced B.A := by
  first | exact @GlobalTheory.UnitLemma.InvAlg.isReduced_of_separable_P | exact GlobalTheory.UnitLemma.InvAlg.isReduced_of_separable_P | (intros; apply GlobalTheory.UnitLemma.InvAlg.isReduced_of_separable_P <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraEtaleOfSeparableCharpolyMulLeft
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraEtaleOfSeparableCharpolyMulLeft
open Polynomial

namespace GlobalTheory

theorem etale_of_separable_charpoly_mulLeft (E A : Type) [Field E] [CommRing A] [Algebra E A]
    [Module.Finite E A] (g : A) (h : (LinearMap.mulLeft E g).charpoly.Separable) :
    Algebra.Etale E A := by
  have hd := GlobalTheory.UnitLemma.charpoly_dvd_minpoly_of_separable (LinearMap.mulLeft E g) h
  have h2 : minpoly E (LinearMap.mulLeft E g) = minpoly E g :=
    minpoly.algHom_eq (Algebra.lmul E A) (Algebra.lmul_injective) g
  have hint : IsIntegral E g := Algebra.IsIntegral.isIntegral g
  have hm : (minpoly E g).Monic := minpoly.monic hint
  have hd' : minpoly E g ∣ (LinearMap.mulLeft E g).charpoly := by
    rw [← h2]; exact LinearMap.minpoly_dvd_charpoly _
  rw [h2] at hd
  have heq : minpoly E g = (LinearMap.mulLeft E g).charpoly :=
    eq_of_monic_of_associated hm (LinearMap.charpoly_monic _) (associated_of_dvd_dvd hd' hd)
  have hsep : (minpoly E g).Separable := heq ▸ h
  have hdeg : (minpoly E g).natDegree = Module.finrank E A := by
    rw [heq, LinearMap.charpoly_natDegree]
  haveI : Module.Finite E (AdjoinRoot (minpoly E g)) := hm.finite_adjoinRoot
  let φ : AdjoinRoot (minpoly E g) →ₐ[E] A := AdjoinRoot.liftAlgHom (minpoly E g) (Algebra.ofId E A) g (minpoly.aeval E g)
  have hli : LinearIndependent E fun i : Fin (minpoly E g).natDegree => g ^ (i : ℕ) :=
    linearIndependent_pow g
  let b := basisOfLinearIndependentOfCardEqFinrank' _ hli (by simp [hdeg])
  have hsurj : Function.Surjective φ.toLinearMap := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← b.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨AdjoinRoot.root (minpoly E g) ^ (i : ℕ), ?_⟩
    simp only [b, coe_basisOfLinearIndependentOfCardEqFinrank', AlgHom.toLinearMap_apply, map_pow]
    congr 1
    exact AdjoinRoot.liftAlgHom_root _ _ _ _
  have hfr : Module.finrank E (AdjoinRoot (minpoly E g)) = Module.finrank E A := by
    rw [(AdjoinRoot.powerBasis' hm).finrank]; simpa using hdeg
  have hinj : Function.Injective φ.toLinearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).2 hsurj
  let e : AdjoinRoot (minpoly E g) ≃ₐ[E] A := AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩
  have hu : IsUnit (AdjoinRoot.mk (minpoly E g) (minpoly E g).derivative) := by
    obtain ⟨a, c, hac⟩ := hsep
    have := congrArg (AdjoinRoot.mk (minpoly E g)) hac
    rw [map_add (f := _), map_mul, map_mul, AdjoinRoot.mk_self, mul_zero, zero_add, map_one] at this
    exact isUnit_iff_exists_inv.2 ⟨_, by rw [mul_comm]; exact this⟩
  have := GlobalTheory.etale_adjoinRoot_of_isUnit_derivative hm hu
  exact Algebra.Etale.of_equiv e

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraEtaleOfSeparableCharpolyMulLeftStatement
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraEtale_of_separable_charpoly_mulLeft : ∀ (E A : Type) [Field E] [CommRing A] [Algebra E A] [Module.Finite E A] (g : A), (LinearMap.mulLeft E g).charpoly.Separable → Algebra.Etale E A := by
  first | exact @GlobalTheory.etale_of_separable_charpoly_mulLeft | exact GlobalTheory.etale_of_separable_charpoly_mulLeft | (intros; apply GlobalTheory.etale_of_separable_charpoly_mulLeft <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemRangeAlgebraMapOfStarEq
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemRangeAlgebraMapOfStarEq
open GlobalTheory.UnitLemma Matrix MeasureTheory

namespace GlobalTheory.JR

theorem Unram.mem_range_of_star_eq : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [GlobalTheory.JR.Unram F E] (y : E), star y = y → ∃ x : F, algebraMap F E x = y := by
  intro F E _ _ _ _ h y hy
  haveI := h.charZero
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap F E).injective
  obtain ⟨b, d, hb0, hs, -, -⟩ := Unram.exists_basis_antifixed F E
  have hsum := b.sum_repr y
  rw [Fin.sum_univ_two, hb0] at hsum
  set a := b.repr y 0
  set c := b.repr y 1
  have hst : star y = a • (1 : E) - c • b 1 := by
    rw [← hsum]
    simp only [Algebra.smul_def, star_add, star_mul', h.star_fix, hs, star_one]
    ring
  have h2 : (2 : E) * (c • b 1) = 0 := by linear_combination hsum + hst - hy
  have hc : c • b 1 = 0 := (mul_eq_zero.1 h2).resolve_left two_ne_zero
  refine ⟨a, ?_⟩
  rw [← hsum, hc, add_zero, Algebra.algebraMap_eq_smul_one]

end GlobalTheory.JR
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemRangeAlgebraMapOfStarEqStatement
open GlobalTheory.UnitLemma Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_range_algebraMap_of_star_eq : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [GlobalTheory.JR.Unram F E] (y : E), star y = y → ∃ x : F, algebraMap F E x = y := by
  first | exact @GlobalTheory.JR.Unram.mem_range_of_star_eq | exact GlobalTheory.JR.Unram.mem_range_of_star_eq | (intros; apply GlobalTheory.JR.Unram.mem_range_of_star_eq <;> assumption)
end
end
