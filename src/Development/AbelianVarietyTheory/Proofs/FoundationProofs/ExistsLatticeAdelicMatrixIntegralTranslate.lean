module

public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
public import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
public import Formalism.FormalDegreeBessel.StatementG
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashToGLSmul
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusPowerReductionCongruence

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeAdelicMatrixIntegralTranslate
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeAdelicMatrixIntegralTranslate
open scoped Matrix
open NumberField IsDedekindDomain

namespace GlobalTheory.AdelicMatLat

variable (E : Type) [Field E] [NumberField E]

def intAdeles : Subring (FiniteAdeleRing (𝓞 E) E) where
  carrier := {a | ∀ v, a v ∈ v.adicCompletionIntegers E}
  mul_mem' ha hb v := mul_mem (ha v) (hb v)
  one_mem' v := one_mem (v.adicCompletionIntegers E)
  add_mem' ha hb v := add_mem (ha v) (hb v)
  zero_mem' v := zero_mem (v.adicCompletionIntegers E)
  neg_mem' ha v := neg_mem (ha v)

theorem mem_intAdeles {a : FiniteAdeleRing (𝓞 E) E} :
    a ∈ intAdeles E ↔ ∀ v, a v ∈ v.adicCompletionIntegers E := Iff.rfl

theorem algebraMap_mem_iff (x : E) :
    algebraMap E (FiniteAdeleRing (𝓞 E) E) x ∈ intAdeles E ↔ ∃ r : 𝓞 E, (r : E) = x := by
  rw [mem_intAdeles, ← GlobalTheory.AdLat.mem_adelicIdeal_one_iff_integral,
    GlobalTheory.Idele.algebraMap_mem_adelicIdeal (GlobalTheory.AdLat.one_ne_zero_fracIdeal E),
    FractionalIdeal.mem_one_iff]

theorem exists_nat_denom (x : E) : ∃ d : ℕ, 0 < d ∧ ∃ r : 𝓞 E, (r : E) = d * x := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {b}))
  refine ⟨Ideal.absNorm (Ideal.span {b}), Nat.pos_of_ne_zero ?_, c * a, ?_⟩
  · simpa [Ideal.absNorm_eq_zero_iff] using hb0
  · have h1 : ((Ideal.absNorm (Ideal.span {b}) : ℕ) : E) =
        algebraMap (𝓞 E) E c * algebraMap (𝓞 E) E b := by
      rw [← map_mul, hc, map_natCast]
    have h2 : algebraMap (𝓞 E) E b ≠ 0 := by
      simpa using hb0
    rw [h1]
    change algebraMap (𝓞 E) E (c * a) = _
    rw [map_mul]
    field_simp

theorem exists_nat_mul_mem (a : FiniteAdeleRing (𝓞 E) E) :
    ∃ d : ℕ, 0 < d ∧ (d : FiniteAdeleRing (𝓞 E) E) * a ∈ intAdeles E := by
  obtain ⟨x, b, hb, rfl⟩ := GlobalTheory.AdLat.exists_eq_algebraMap_add_nsmul E 1 one_pos a
  obtain ⟨d, hd, r, hr⟩ := exists_nat_denom E x
  refine ⟨d, hd, ?_⟩
  rw [mul_add, one_smul]
  refine add_mem ?_ (mul_mem (natCast_mem _ d) hb)
  rw [← map_natCast (algebraMap E (FiniteAdeleRing (𝓞 E) E)), ← map_mul, algebraMap_mem_iff]
  exact ⟨r, hr⟩

theorem exists_nat_mul_mem_family {ι : Type} [Fintype ι] (a : ι → FiniteAdeleRing (𝓞 E) E) :
    ∃ d : ℕ, 0 < d ∧ ∀ i, (d : FiniteAdeleRing (𝓞 E) E) * a i ∈ intAdeles E := by
  classical
  choose d hd h using fun i => exists_nat_mul_mem E (a i)
  refine ⟨∏ i, d i, Finset.prod_pos fun i _ => hd i, fun i => ?_⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), Nat.cast_mul, mul_assoc]
  exact mul_mem (natCast_mem _ _) (h i)

variable {E} {n : ℕ}

def lat (β : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) : Submodule (𝓞 E) (Fin n → E) where
  carrier := {x | ∀ j, ∑ k, algebraMap E (FiniteAdeleRing (𝓞 E) E) (x k) * β k j ∈ intAdeles E}
  add_mem' {x y} hx hy j := by
    simpa only [Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib] using add_mem (hx j) (hy j)
  zero_mem' j := by simp
  smul_mem' c x hx j := by
    have h : algebraMap E (FiniteAdeleRing (𝓞 E) E) (c : E) ∈ intAdeles E :=
      (algebraMap_mem_iff E _).2 ⟨c, rfl⟩
    have h2 := mul_mem h (hx j)
    rw [Finset.mul_sum] at h2
    convert h2 using 2 with k
    rw [← mul_assoc, ← map_mul]
    rfl

theorem span_lat (β : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) :
    Submodule.span E (lat β : Set (Fin n → E)) = ⊤ := by
  classical
  obtain ⟨d, hd, h⟩ := exists_nat_mul_mem_family E (fun p : Fin n × Fin n => β p.1 p.2)
  rw [eq_top_iff, ← (Pi.basisFun E (Fin n)).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  have hm : (Pi.single i (d : E) : Fin n → E) ∈ lat β := by
    intro j
    rw [Finset.sum_eq_single i (by intro k _ hk; simp [Pi.single_eq_of_ne hk]) (by simp)]
    simpa using h (i, j)
  have hd' : (d : E) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
  have he : Pi.basisFun E (Fin n) i = (d : E)⁻¹ • (Pi.single i (d : E) : Fin n → E) := by
    rw [Pi.basisFun_apply, ← Pi.single_smul, smul_eq_mul, inv_mul_cancel₀ hd']
  rw [he]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hm)

theorem fg_lat (β : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) : (lat β.1).FG := by
  classical
  obtain ⟨d, hd, h⟩ := exists_nat_mul_mem_family E (fun p : Fin n × Fin n => β⁻¹.1 p.1 p.2)
  have hd' : (d : E) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
  have hle : lat β.1 ≤ Submodule.span (𝓞 E)
      (Set.range fun i : Fin n => (Pi.single i (d : E)⁻¹ : Fin n → E)) := by
    intro x hx
    have h1 : ∀ j, ∃ r : 𝓞 E, (r : E) = d * x j := by
      intro j
      rw [← algebraMap_mem_iff]
      have h2 : algebraMap E (FiniteAdeleRing (𝓞 E) E) (d * x j) =
          ∑ l, (∑ k, algebraMap E (FiniteAdeleRing (𝓞 E) E) (x k) * β.1 k l) *
            ((d : FiniteAdeleRing (𝓞 E) E) * β⁻¹.1 l j) := by
        have h3 : ((fun k => algebraMap E (FiniteAdeleRing (𝓞 E) E) (x k)) ᵥ* β.1) ᵥ* β⁻¹.1 =
            fun k => algebraMap E (FiniteAdeleRing (𝓞 E) E) (x k) := by
          rw [Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one]
        rw [map_mul, map_natCast, ← congrFun h3 j]
        simp only [Matrix.vecMul, dotProduct]
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => mul_left_comm _ _ _
      rw [h2]
      exact sum_mem fun l _ => mul_mem (hx l) (h (l, j))
    choose r hr using h1
    have h4 : x = ∑ i, r i • (Pi.single i (d : E)⁻¹ : Fin n → E) := by
      ext j
      rw [Finset.sum_apply, Finset.sum_eq_single j
        (by intro k _ hk; simp [Pi.single_eq_of_ne hk.symm]) (by simp)]
      rw [Pi.smul_apply, Pi.single_eq_same]
      change x j = (r j : E) * (d : E)⁻¹
      rw [hr]
      field_simp
    rw [h4]
    exact sum_mem fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  haveI := isNoetherian_span_of_finite (𝓞 E)
    (Set.finite_range fun i : Fin n => (Pi.single i (d : E)⁻¹ : Fin n → E))
  exact Submodule.FG.of_le_of_isNoetherian hle

theorem isLattice_lat (β : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) :
    Submodule.IsFullLattice E (lat β.1) := by
  exact { toIsLattice := Submodule.IsLattice.of_fg E (fg_lat β)
          span_eq_top := span_lat β.1 }

theorem inv_mul_mem (β : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) (M : ℕ) (δ : GL (Fin n) E)
    (hδ : ∀ x ∈ lat β.1, ∃ y : Fin n → 𝓞 E, (M : E) • x = (fun i => (y i : E)) ᵥ* δ.1)
    (i j : Fin n) :
    (M : FiniteAdeleRing (𝓞 E) E) *
      (β⁻¹.1 * δ⁻¹.1.map (algebraMap E (FiniteAdeleRing (𝓞 E) E))) i j ∈ intAdeles E := by
  classical
  obtain ⟨d₁, hd₁, h₁⟩ := exists_nat_mul_mem_family E (fun p : Fin n × Fin n => β.1 p.1 p.2)
  obtain ⟨d₂, hd₂, h₂⟩ := exists_nat_mul_mem_family E
    (fun p : Fin n × Fin n => algebraMap E (FiniteAdeleRing (𝓞 E) E) (δ⁻¹.1 p.1 p.2))
  choose x b hb hx using fun k => GlobalTheory.AdLat.exists_eq_algebraMap_add_nsmul E (d₁ * d₂)
    (Nat.mul_pos hd₁ hd₂) (β⁻¹.1 i k)
  have hxl : x ∈ lat β.1 := by
    intro l
    have h3 : ∑ k, algebraMap E (FiniteAdeleRing (𝓞 E) E) (x k) * β.1 k l =
        (β⁻¹.1 * β.1) i l - ∑ k, ((d₂ : FiniteAdeleRing (𝓞 E) E) * b k) *
          ((d₁ : FiniteAdeleRing (𝓞 E) E) * β.1 k l) := by
      rw [Matrix.mul_apply, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hx k, nsmul_eq_mul, Nat.cast_mul]
      ring
    rw [h3, Units.inv_mul]
    refine sub_mem ?_ (sum_mem fun k _ => mul_mem (mul_mem (natCast_mem _ _) (hb k)) (h₁ (k, l)))
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  obtain ⟨y, hy⟩ := hδ x hxl
  have h4 : (y j : E) = ∑ k, (M : E) * x k * δ⁻¹.1 k j := by
    have h5 : ((M : E) • x) ᵥ* δ⁻¹.1 = fun i => (y i : E) := by
      rw [hy, Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one]
    rw [← congrFun h5 j]
    rfl
  have h6 : (M : FiniteAdeleRing (𝓞 E) E) *
      (β⁻¹.1 * δ⁻¹.1.map (algebraMap E (FiniteAdeleRing (𝓞 E) E))) i j =
      algebraMap E (FiniteAdeleRing (𝓞 E) E) (y j : E) +
        ∑ k, ((M : FiniteAdeleRing (𝓞 E) E) * ((d₁ : FiniteAdeleRing (𝓞 E) E) * b k)) *
          ((d₂ : FiniteAdeleRing (𝓞 E) E) *
            algebraMap E (FiniteAdeleRing (𝓞 E) E) (δ⁻¹.1 k j)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h4, map_sum, Matrix.mul_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hx k, nsmul_eq_mul, Nat.cast_mul, Matrix.map_apply, map_mul, map_mul, map_natCast]
    ring
  rw [h6]
  exact add_mem ((algebraMap_mem_iff E _).2 ⟨y j, rfl⟩) (sum_mem fun k _ =>
    mul_mem (mul_mem (natCast_mem _ _) (mul_mem (natCast_mem _ _) (hb k))) (h₂ (k, j)))

theorem exists_lattice_integral : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (β : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)), ∃ Λ : Submodule (𝓞 E) (Fin n → E), Submodule.IsFullLattice E Λ ∧ ∀ (M : ℕ) (δ : GL (Fin n) E), (∀ i, δ.1 i ∈ Λ) → (∀ x ∈ Λ, ∃ y : Fin n → 𝓞 E, (M : E) • x = (fun i => (y i : E)) ᵥ* δ.1) → ∀ (i j : Fin n) (v : HeightOneSpectrum (𝓞 E)), (δ.1.map (algebraMap E (FiniteAdeleRing (𝓞 E) E)) * β.1) i j v ∈ v.adicCompletionIntegers E ∧ ((M : FiniteAdeleRing (𝓞 E) E) * (β⁻¹.1 * δ⁻¹.1.map (algebraMap E (FiniteAdeleRing (𝓞 E) E))) i j) v ∈ v.adicCompletionIntegers E := by
  intro E _ _ n β
  refine ⟨lat β.1, isLattice_lat β, fun M δ h1 h2 i j v => ⟨?_, inv_mul_mem β M δ h2 i j v⟩⟩
  rw [Matrix.mul_apply]
  exact h1 i j v

end GlobalTheory.AdelicMatLat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeAdelicMatrixIntegralTranslateStatement
open scoped Matrix
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lattice_adelicMatrix_integral_translate : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (β : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)), ∃ Λ : Submodule (𝓞 E) (Fin n → E), Submodule.IsFullLattice E Λ ∧ ∀ (M : ℕ) (δ : GL (Fin n) E), (∀ i, δ.1 i ∈ Λ) → (∀ x ∈ Λ, ∃ y : Fin n → 𝓞 E, (M : E) • x = (fun i => (y i : E)) ᵥ* δ.1) → ∀ (i j : Fin n) (v : HeightOneSpectrum (𝓞 E)), (δ.1.map (algebraMap E (FiniteAdeleRing (𝓞 E) E)) * β.1) i j v ∈ v.adicCompletionIntegers E ∧ ((M : FiniteAdeleRing (𝓞 E) E) * (β⁻¹.1 * δ⁻¹.1.map (algebraMap E (FiniteAdeleRing (𝓞 E) E))) i j) v ∈ v.adicCompletionIntegers E :=
  @GlobalTheory.AdelicMatLat.exists_lattice_integral
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelFunctionHolomorphic
noncomputable section

open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam GlobalTheory.Sieg.Model

namespace GlobalTheory.Sieg.Hol

theorem differentiable_ee : Differentiable ℂ ee := by
  unfold ee
  exact (differentiable_id.const_mul _).cexp

theorem differentiableOn_geomProd {g : ℂ → ℂ} (hg : Differentiable ℂ g) :
    DifferentiableOn ℂ (fun z => ∏' m : ℕ, (1 - ee z ^ (m + 1) * g z)) {z : ℂ | 0 < z.im} := by
  have hU : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hec : Continuous ee := differentiable_ee.continuous
  have hgc : Continuous g := hg.continuous
  have hloc : HasProdLocallyUniformlyOn (fun (m : ℕ) (z : ℂ) => 1 + -(ee z ^ (m + 1) * g z))
      (fun z => ∏' m : ℕ, (1 + -(ee z ^ (m + 1) * g z))) {z : ℂ | 0 < z.im} := by
    refine hasProdLocallyUniformlyOn_of_forall_compact hU fun K hK hKc => ?_
    rcases K.eq_empty_or_nonempty with hK0 | hKne
    · subst hK0
      exact Summable.hasProdUniformlyOn_nat_one_add hKc (u := fun _ => (0 : ℝ)) summable_zero
        (.of_forall fun n z hz => absurd hz (Set.notMem_empty z))
        (fun n => (by fun_prop : Continuous fun z => -(ee z ^ (n + 1) * g z)).continuousOn)
    obtain ⟨z₀, hz₀, hmax⟩ := hKc.exists_isMaxOn hKne (continuous_norm.comp hec).continuousOn
    obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hgc.continuousOn
    set r := ‖ee z₀‖ with hr_def
    have hr1 : r < 1 := norm_ee_lt_one ⟨z₀, hK hz₀⟩
    have hr0 : 0 ≤ r := norm_nonneg _
    have hr : ∀ z ∈ K, ‖ee z‖ ≤ r := fun z hz => hmax hz
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC z₀ hz₀)
    refine Summable.hasProdUniformlyOn_nat_one_add hKc (u := fun n => C * r * r ^ n)
      ((summable_geometric_of_lt_one hr0 hr1).mul_left (C * r)) (.of_forall fun n z hz => ?_)
      (fun n => (by fun_prop : Continuous fun z => -(ee z ^ (n + 1) * g z)).continuousOn)
    rw [norm_neg, norm_mul, norm_pow]
    calc ‖ee z‖ ^ (n + 1) * ‖g z‖ ≤ r ^ (n + 1) * C :=
          mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hr z hz) _) (hC z hz) (norm_nonneg _) (pow_nonneg hr0 _)
      _ = C * r * r ^ n := by ring
  have hd := hloc.differentiableOn (.of_forall fun n => by
    simpa [Finset.prod_fn] using DifferentiableOn.finsetProd (fun i _ =>
      ((differentiable_const (1 : ℂ)).add ((differentiable_ee.pow (i + 1)).mul hg).neg).differentiableOn)) hU
  refine hd.congr fun z _ => ?_
  simp only [sub_eq_add_neg]

def geomProd (q a : ℂ) : ℂ := ∏' m : ℕ, (1 - q ^ (m + 1) * a)

theorem tprod_cthFac {c : ℕ} {x : Fin 2 → ℚ} (h : admitted c x) (τ : ℍ) :
    geomProd (ee τ) (ee (pt x τ) ^ c) * geomProd (ee τ) (ee (pt x τ) ^ c)⁻¹ ≠ 0 ∧
    ∏' m : ℕ, cthFac c (ee τ) (ee (pt x τ)) (m + 1) =
      geomProd (ee τ) (ee (pt x τ)) ^ (c ^ 2) * geomProd (ee τ) (ee (pt x τ))⁻¹ ^ (c ^ 2) /
        (geomProd (ee τ) (ee (pt x τ) ^ c) * geomProd (ee τ) (ee (pt x τ) ^ c)⁻¹) := by
  obtain ⟨hc1, hc6, hnot⟩ := h
  have hq : ‖ee τ‖ < 1 := norm_ee_lt_one τ
  have hx : ¬ (x 0 ∈ Set.range ((↑) : ℤ → ℚ) ∧ x 1 ∈ Set.range ((↑) : ℤ → ℚ)) := by
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact hnot ⟨⟨(c : ℤ) * a, by push_cast; rw [ha]⟩, ⟨(c : ℤ) * b, by push_cast; rw [hb]⟩⟩
  have hcx : ¬ ((c • x) 0 ∈ Set.range ((↑) : ℤ → ℚ) ∧ (c • x) 1 ∈ Set.range ((↑) : ℤ → ℚ)) := by
    simpa [nsmul_eq_mul] using hnot
  have htc : ee (pt x τ) ^ c = ee (pt (c • x) τ) := ee_pt_pow c x τ
  have n1 : ∀ m : ℕ, 1 - ee τ ^ (m + 1) * ee (pt x τ) ≠ 0 := fun m => (ne_one_of_not_int hx τ (m + 1)).1
  have n2 : ∀ m : ℕ, 1 - ee τ ^ (m + 1) * (ee (pt x τ))⁻¹ ≠ 0 := fun m => (ne_one_of_not_int hx τ (m + 1)).2
  have n3 : ∀ m : ℕ, 1 - ee τ ^ (m + 1) * ee (pt x τ) ^ c ≠ 0 := fun m => by
    rw [htc]; exact (ne_one_of_not_int hcx τ (m + 1)).1
  have n4 : ∀ m : ℕ, 1 - ee τ ^ (m + 1) * (ee (pt x τ) ^ c)⁻¹ ≠ 0 := fun m => by
    rw [htc]; exact (ne_one_of_not_int hcx τ (m + 1)).2
  obtain ⟨P1, -, h1⟩ := hasProd_geom hq _ n1
  obtain ⟨P2, -, h2⟩ := hasProd_geom hq _ n2
  obtain ⟨P3, hP3, h3⟩ := hasProd_geom hq _ n3
  obtain ⟨P4, hP4, h4⟩ := hasProd_geom hq _ n4
  have e1 : geomProd (ee τ) (ee (pt x τ)) = P1 := h1.tprod_eq
  have e2 : geomProd (ee τ) (ee (pt x τ))⁻¹ = P2 := h2.tprod_eq
  have e3 : geomProd (ee τ) (ee (pt x τ) ^ c) = P3 := h3.tprod_eq
  have e4 : geomProd (ee τ) (ee (pt x τ) ^ c)⁻¹ = P4 := h4.tprod_eq
  rw [e1, e2, e3, e4]
  refine ⟨mul_ne_zero hP3 hP4, ?_⟩
  have hall := ((hasProd_pow h1 (c ^ 2)).mul (hasProd_pow h2 (c ^ 2))).mul
    (hasProd_inv (h3.mul h4) (mul_ne_zero hP3 hP4))
  rw [div_eq_mul_inv, ← hall.tprod_eq]
  refine tprod_congr fun m => ?_
  unfold cthFac
  rw [div_eq_mul_inv]

end GlobalTheory.Sieg.Hol

namespace GlobalTheory.Sieg

open Hol

theorem mdifferentiable_sg :
    ∀ (c : ℕ) (x : Fin 2 → ℚ), admitted c x → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (sg c x) := by
  intro c x h
  rw [UpperHalfPlane.mdifferentiable_iff]
  set T : ℂ → ℂ := fun z => ee ((x 0 : ℂ) * z + (x 1 : ℂ)) with hT
  have hTd : Differentiable ℂ T := differentiable_ee.comp ((differentiable_id.const_mul _).add_const _)
  have hT0 : ∀ z, T z ≠ 0 := fun z => ee_ne_zero _
  have hG1 := differentiableOn_geomProd hTd
  have hG2 := differentiableOn_geomProd (hTd.inv hT0)
  have hG3 := differentiableOn_geomProd (hTd.pow c)
  have hG4 := differentiableOn_geomProd ((hTd.pow c).inv fun z => pow_ne_zero _ (hT0 z))
  have hnd : ∀ z ∈ {z : ℂ | 0 < z.im}, 1 - T z ^ c ≠ 0 := fun z hz =>
    (multipliable_and_sg_ne_zero h ⟨z, hz⟩).2.1
  have hnG : ∀ z ∈ {z : ℂ | 0 < z.im}, geomProd (ee z) (T z ^ c) * geomProd (ee z) (T z ^ c)⁻¹ ≠ 0 :=
    fun z hz => (tprod_cthFac h ⟨z, hz⟩).1
  have hH : DifferentiableOn ℂ (fun z => ee z ^ ((c ^ 2 - 1) / 12) * (-T z) ^ (((c : ℤ) - (c : ℤ) ^ 2) / 2) *
      (1 - T z) ^ (c ^ 2) / (1 - T z ^ c) *
      (geomProd (ee z) (T z) ^ (c ^ 2) * geomProd (ee z) (T z)⁻¹ ^ (c ^ 2) /
        (geomProd (ee z) (T z ^ c) * geomProd (ee z) (T z ^ c)⁻¹))) {z : ℂ | 0 < z.im} := by
    refine DifferentiableOn.mul (DifferentiableOn.div (DifferentiableOn.mul (DifferentiableOn.mul ?_ ?_) ?_) ?_ hnd)
      (DifferentiableOn.div (DifferentiableOn.mul (hG1.pow _) (hG2.pow _)) (hG3.mul hG4) hnG)
    · exact (differentiable_ee.pow _).differentiableOn
    · exact hTd.neg.differentiableOn.zpow (Or.inl fun z _ => neg_ne_zero.mpr (hT0 z))
    · exact (((differentiable_const _).sub hTd).pow _).differentiableOn
    · exact ((differentiable_const _).sub (hTd.pow c)).differentiableOn
  refine hH.congr fun z hz => ?_
  have hz' : 0 < z.im := hz
  simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hz']
  unfold sg cth
  rw [(tprod_cthFac h ⟨z, hz'⟩).2]
  rfl

end GlobalTheory.Sieg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LeadingMinorInvariant
open Matrix

noncomputable section

namespace GlobalTheory.LeadingMinorInv

open Formalism.QuantumDeterminants

def UpUni {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  (∀ i j, j < i → U i j = 0) ∧ ∀ i, U i i = 1

lemma minor_mul {n l : ℕ} (hl : l ≤ n) (A U : Matrix (Fin n) (Fin n) ℂ) (hU : UpUni U) :
    ((A * U).submatrix (Fin.castLE hl) (Fin.castLE hl)).det =
      (A.submatrix (Fin.castLE hl) (Fin.castLE hl)).det := by
  have hsub : (A * U).submatrix (Fin.castLE hl) (Fin.castLE hl) =
      A.submatrix (Fin.castLE hl) (Fin.castLE hl) * U.submatrix (Fin.castLE hl) (Fin.castLE hl) := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.mul_apply]
    symm
    apply Fintype.sum_of_injective (Fin.castLE hl) (Fin.castLE_injective hl)
    · intro b hb
      have hjb : Fin.castLE hl j < b := by
        rw [Fin.lt_def]
        show j.val < b.val
        by_contra hc
        have := j.isLt
        exact hb ⟨⟨b.val, by omega⟩, Fin.ext rfl⟩
      rw [hU.1 b _ hjb, mul_zero]
    · intro a
      rfl
  have hdet : (U.submatrix (Fin.castLE hl) (Fin.castLE hl)).det = 1 := by
    rw [Matrix.det_of_isUpperTriangular]
    · simp [Matrix.submatrix_apply, hU.2]
    · intro i j hij
      simp only [Matrix.submatrix_apply]
      apply hU.1
      rw [Fin.lt_def] at hij ⊢
      exact hij
  rw [hsub, Matrix.det_mul, hdet, mul_one]

lemma minor_mul_left {n l : ℕ} (hl : l ≤ n) (A U : Matrix (Fin n) (Fin n) ℂ) (hU : UpUni U) :
    ((Uᴴ * A).submatrix (Fin.castLE hl) (Fin.castLE hl)).det =
      (A.submatrix (Fin.castLE hl) (Fin.castLE hl)).det := by
  have e : Uᴴ * A = (Aᴴ * U)ᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rw [e, ← Matrix.conjTranspose_submatrix, Matrix.det_conjTranspose, minor_mul hl _ _ hU,
    ← Matrix.conjTranspose_submatrix, Matrix.det_conjTranspose, star_star]

def flagMat (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) :
    Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) ℂ := Matrix.of fun i a => fvec k r z a i

lemma mul_flagMat (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i) (b) :
    (g * flagMat k r z) i b = (g *ᵥ fvec k r z b) i := rfl

lemma zhat_eq (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Zhat k r z z' g = (flagMat k r z)ᴴ * (Hpk k r * (g * flagMat k r z')) := by
  ext a b
  simp only [Zhat, herm, Matrix.mul_apply, Matrix.conjTranspose_apply, flagMat, Matrix.of_apply,
    dotProduct, Matrix.mulVec, Pi.star_apply]

lemma exists_N (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z)
    (m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hm : m ∈ Nset k r) :
    ∃ U : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ, UpUni U ∧ m * flagMat k r z = flagMat k r z * U := by
  simp only [Nset, Set.mem_setOf_eq] at hm
  obtain ⟨-, hm2, hm3⟩ := hm
  have key : ∀ (a : Fin (r + 1)) (i : Fin (2 * r + k + 1)),
      (m *ᵥ fvec k r z a) i =
        fvec k r z a i + if i.val < a.val then (m *ᵥ fvec k r z a) i else 0 := by
    intro a i
    have ha := a.isLt
    by_cases hia : i.val < a.val
    · rw [if_pos hia]
      suffices h0 : fvec k r z a i = 0 by rw [h0, zero_add]
      by_cases har : a.val < r
      · simp only [fvec, dif_pos har, bvec]
        rw [Pi.single_apply, if_neg]
        intro he
        have h1 := congrArg Fin.val he
        simp [eI] at h1
        omega
      · simp only [fvec, dif_neg har]
        exact hz i (Or.inl (by omega))
    · rw [if_neg hia, add_zero]
      by_cases har : a.val < r
      · simp only [fvec, dif_pos har, bvec]
        simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
          Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
        exact hm2 ⟨a.val, har⟩ i (by show a.val ≤ i.val; omega)
      · simp only [fvec, dif_neg har]
        have hterm : ∀ j, m i j * z j = if i = j then z j else 0 := by
          intro j
          by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
          · rw [hm3 i j hj.1 hj.2 (by omega)]
            split_ifs <;> simp
          · rw [hz j (by omega)]
            simp
        simp only [Matrix.mulVec, dotProduct, hterm, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  refine ⟨Matrix.of fun b a => (if b = a then 1 else 0) +
      (if hba : b.val < a.val then
        (m *ᵥ fvec k r z a) (eI k r ⟨b.val, by have := a.isLt; omega⟩) else 0), ⟨?_, ?_⟩, ?_⟩
  · intro i j hij
    have h1 : i ≠ j := hij.ne'
    have h2 : ¬ i < j := by rw [Fin.lt_def] at hij ⊢; omega
    simp [h1, h2]
  · intro i
    simp
  · ext i a
    rw [mul_flagMat, Matrix.mul_apply]
    simp only [flagMat, Matrix.of_apply, mul_add, Finset.sum_add_distrib, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [key a i]
    congr 1
    have ha := a.isLt
    by_cases hia : i.val < a.val
    · have hir : i.val < r := by omega
      rw [if_pos hia, Finset.sum_eq_single (⟨i.val, by omega⟩ : Fin (r + 1))]
      · have he : eI k r ⟨i.val, hir⟩ = i := Fin.ext rfl
        simp [fvec, hir, hia, he, bvec]
      · intro b _ hb
        split_ifs with hba
        · have hbr : b.val < r := by omega
          have hne : i ≠ eI k r ⟨b.val, hbr⟩ := by
            intro he
            apply hb
            ext
            exact (congrArg Fin.val he).symm
          simp [fvec, hbr, bvec, Pi.single_apply, hne]
        · simp
      · simp
    · rw [if_neg hia]
      symm
      apply Finset.sum_eq_zero
      intro b _
      split_ifs with hba
      · have hbr : b.val < r := by omega
        have hne : i ≠ eI k r ⟨b.val, hbr⟩ := by
          intro he
          apply hia
          rw [he]
          exact hba
        simp [fvec, hbr, bvec, Pi.single_apply, hne]
      · simp

lemma exists_S (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z)
    (s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hs : s ∈ Sset k r z) :
    sᴴ * Hpk k r * s = Hpk k r ∧ ∃ U : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ, UpUni U ∧ s * flagMat k r z = flagMat k r z * U := by
  simp only [Sset, Set.mem_setOf_eq] at hs
  obtain ⟨h, hh, m, hm, rfl⟩ := hs
  obtain ⟨U, hU, hmF⟩ := exists_N k r z hz m hm
  simp only [UWset, Set.mem_setOf_eq] at hh
  obtain ⟨hhU, hfix, hhz⟩ := hh
  have hmU : mᴴ * Hpk k r * m = Hpk k r := by
    simp only [Nset, Set.mem_setOf_eq] at hm
    exact hm.1
  have hhU' : hᴴ * Hpk k r * h = Hpk k r := hhU
  refine ⟨?_, U, hU, ?_⟩
  · calc (h * m)ᴴ * Hpk k r * (h * m) = mᴴ * (hᴴ * Hpk k r * h) * m := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Hpk k r := by rw [hhU', hmU]
  · have hF : h * flagMat k r z = flagMat k r z := by
      ext i b
      rw [mul_flagMat]
      simp only [flagMat, Matrix.of_apply]
      by_cases hb : b.val < r
      · simp only [fvec, dif_pos hb]
        rw [(hfix ⟨b.val, hb⟩).1]
      · simp only [fvec, dif_neg hb]
        rw [hhz]
    rw [Matrix.mul_assoc, hmF, ← Matrix.mul_assoc, hF]

end GlobalTheory.LeadingMinorInv

namespace GlobalTheory

open Formalism.QuantumDeterminants LeadingMinorInv

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspidalAtAllCuspsSL2SlashIntMatrix
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspidalAtAllCuspsSL2SlashIntMatrix
open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold

noncomputable section

namespace GlobalTheory.HeckeFamilyMatrices

private def toGLQ (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : M.det ≠ 0) : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero ((Int.castRingHom ℚ).mapMatrix M)
    (by rw [← RingHom.map_det]; simpa using hM)

private lemma toGL_eq_map (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : M.det ≠ 0) :
    toGL M = Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (toGLQ M hM) := by
  ext i j
  rw [toGL_val M hM]
  simp [toGLQ, Matrix.GeneralLinearGroup.map]

lemma isCusp_SL2Z_toGL_smul (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : M.det ≠ 0) {c : OnePoint ℝ}
    (hc : IsCusp c 𝒮ℒ) : IsCusp (toGL M • c) 𝒮ℒ := by
  rw [isCusp_SL2Z_iff] at hc ⊢
  obtain ⟨c, rfl⟩ := hc
  rw [toGL_eq_map M hM]
  exact ⟨toGLQ M hM • c, by rw [← Rat.coe_castHom, OnePoint.map_smul]⟩

theorem cuspAll_slash_toGL : ∀ (k : ℤ) (M : Matrix (Fin 2) (Fin 2) ℤ) (G : ℍ → ℂ), 0 < M.det →
    CuspAll k G → CuspAll k (G ∣[k] toGL M) := by
  intro k M G hM hG
  refine ⟨MDifferentiable.slash hG.1 k (toGL M), fun c hc => ?_⟩
  rw [← OnePoint.IsZeroAt.smul_iff]
  exact hG.2 _ (isCusp_SL2Z_toGL_smul M hM.ne' hc)

end GlobalTheory.HeckeFamilyMatrices
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspidalAtAllCuspsSL2SlashIntMatrixStatement
open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCuspidalAtAllCuspsSL2_slash_intMatrix : ∀ (k : ℤ) (M : Matrix (Fin 2) (Fin 2) ℤ) (G : ℍ → ℂ), 0 < M.det → CuspAll k G → CuspAll k (G ∣[k] toGL M) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.cuspAll_slash_toGL | exact GlobalTheory.HeckeFamilyMatrices.cuspAll_slash_toGL | (intros; apply GlobalTheory.HeckeFamilyMatrices.cuspAll_slash_toGL <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AdmissibleOfSl2Action
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AdmissibleOfSl2Action
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

namespace GlobalTheory.Sieg

private theorem natCast_mul_act_mem_range_intCast (c : ℕ) (z : Fin 2 → ℚ) (δ : SL(2, ℤ))
    (h0 : (c : ℚ) * z 0 ∈ Set.range ((↑) : ℤ → ℚ)) (h1 : (c : ℚ) * z 1 ∈ Set.range ((↑) : ℤ → ℚ))
    (i : Fin 2) : (c : ℚ) * act z δ i ∈ Set.range ((↑) : ℤ → ℚ) := by
  obtain ⟨a, ha⟩ := h0
  obtain ⟨b, hb⟩ := h1
  refine ⟨a * (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 i + b * (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 i, ?_⟩
  simp only [act, Fin.sum_univ_two]
  push_cast
  rw [ha, hb]
  ring

private theorem act_act_inv' (x : Fin 2 → ℚ) (γ : SL(2, ℤ)) : act (act x γ) γ⁻¹ = x := by
  have hd := γ.2
  rw [Matrix.det_fin_two] at hd
  have hq : ((((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1
      - (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ)) : ℚ) = 1 := by
    rw [hd]; simp
  push_cast at hq
  funext i
  fin_cases i <;>
    simp [act, Fin.sum_univ_two, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two] <;>
    push_cast
  · linear_combination x 0 * hq
  · linear_combination x 1 * hq

theorem admissible_act_SL2 : ∀ (c : ℕ) (x : Fin 2 → ℚ) (γ : SL(2, ℤ)), admitted c x → admitted c (act x γ) := by
  rintro c x γ ⟨h1, h2, h3⟩
  refine ⟨h1, h2, fun ⟨k0, k1⟩ => h3 ?_⟩
  rw [← act_act_inv' x γ]
  exact ⟨natCast_mul_act_mem_range_intCast c _ _ k0 k1 0, natCast_mul_act_mem_range_intCast c _ _ k0 k1 1⟩

end GlobalTheory.Sieg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AdmissibleOfSl2ActionStatement
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissible_of_sl2_action : ∀ (c : ℕ) (x : Fin 2 → ℚ) (γ : SL(2, ℤ)), admitted c x → admitted c (act x γ) := by
  first | exact @GlobalTheory.Sieg.admissible_act_SL2 | exact GlobalTheory.Sieg.admissible_act_SL2 | (intros; apply GlobalTheory.Sieg.admissible_act_SL2 <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDerivationOnISupOfCompatible
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDerivationOnISupOfCompatible
open GlobalTheory.AlmostEt

namespace GlobalTheory.AlmostEt

theorem isDerOn_iSup_glue (A S M : Type) [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M]
    [Module S M] (B : ℕ → Subalgebra A S) (hB : Monotone B) (D : ℕ → S → M)
    (hDer : ∀ m, IsDerOn (B m) (D m)) (hcomp : ∀ m, ∀ x ∈ B m, D (m + 1) x = D m x) :
    ∃ D' : S → M, IsDerOn (⨆ m, B m) D' ∧ ∀ m, ∀ x ∈ B m, D' x = D m x := by
  classical
  have hD : ∀ m k, m ≤ k → ∀ x ∈ B m, D k x = D m x := by
    intro m k hmk
    induction k, hmk using Nat.le_induction with
    | base => intro x _; rfl
    | succ k hmk ih =>
      intro x hx
      rw [hcomp k x (hB hmk hx), ih x hx]
  let D' : S → M := fun x => if h : ∃ m, x ∈ B m then D (Nat.find h) x else 0
  have hD' : ∀ m, ∀ x ∈ B m, D' x = D m x := by
    intro m x hx
    have h : ∃ m, x ∈ B m := ⟨m, hx⟩
    simp only [D', dif_pos h]
    exact (hD _ m (Nat.find_min' h hx) x (Nat.find_spec h)).symm
  have hmem : ∀ x ∈ (⨆ m, B m), ∃ m, x ∈ B m := fun x hx =>
    by
    have := hx
    rw [← SetLike.mem_coe, Subalgebra.coe_iSup_of_directed hB.directed_le, Set.mem_iUnion] at this
    exact this
  refine ⟨D', ⟨?_, ?_, ?_⟩, hD'⟩
  · intro x hx y hy
    obtain ⟨m, hm⟩ := hmem x hx
    obtain ⟨n, hn⟩ := hmem y hy
    have hx' : x ∈ B (max m n) := hB (le_max_left m n) hm
    have hy' : y ∈ B (max m n) := hB (le_max_right m n) hn
    rw [hD' _ _ (add_mem hx' hy'), hD' _ _ hx', hD' _ _ hy', (hDer _).add x hx' y hy']
  · intro x hx y hy
    obtain ⟨m, hm⟩ := hmem x hx
    obtain ⟨n, hn⟩ := hmem y hy
    have hx' : x ∈ B (max m n) := hB (le_max_left m n) hm
    have hy' : y ∈ B (max m n) := hB (le_max_right m n) hn
    rw [hD' _ _ (mul_mem hx' hy'), hD' _ _ hx', hD' _ _ hy', (hDer _).mul x hx' y hy']
  · intro a
    rw [hD' 0 _ ((B 0).algebraMap_mem a), (hDer 0).alg a]

end GlobalTheory.AlmostEt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDerivationOnISupOfCompatibleStatement
open GlobalTheory.AlmostEt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_derivationOn_iSup_of_compatible : ∀ (A S M : Type) [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M] [Module S M] (B : ℕ → Subalgebra A S), Monotone B → ∀ D : ℕ → S → M, (∀ m, IsDerOn (B m) (D m)) → (∀ m, ∀ x ∈ B m, D (m + 1) x = D m x) → ∃ D' : S → M, IsDerOn (⨆ m, B m) D' ∧ ∀ m, ∀ x ∈ B m, D' x = D m x := by
  first | exact @GlobalTheory.AlmostEt.isDerOn_iSup_glue | exact GlobalTheory.AlmostEt.isDerOn_iSup_glue | (intros; apply GlobalTheory.AlmostEt.isDerOn_iSup_glue <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KaehlerRelationOfDerivationOnLargeSubalgebra
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KaehlerRelationOfDerivationOnLargeSubalgebra
noncomputable section

namespace GlobalTheory.AlmostEt

open Finsupp

theorem kerTotal_gen_local {A S : Type} [CommRing A] [CommRing S] [Algebra A S]
    (g : S →₀ S)
    (hg : g ∈ ((Set.range fun x : S × S => single x.1 1 + single x.2 1 - single (x.1 + x.2) 1) ∪
        Set.range fun x : S × S => single x.2 x.1 + single x.1 x.2 - single (x.1 * x.2) 1) ∪
      Set.range fun x : A => single (algebraMap A S x) 1) :
    ∃ F : Finset S, ∀ C : Subalgebra A S, (↑F : Set S) ⊆ C →
      ∀ (M : Type) [AddCommGroup M] [Module S M] (D : S → M), IsDerOn C D →
        Finsupp.linearCombination S D g = 0 := by
  classical
  rcases hg with (⟨⟨u, w⟩, rfl⟩ | ⟨⟨u, w⟩, rfl⟩) | ⟨a, rfl⟩
  · refine ⟨{u, w}, fun C hC M _ _ D hD => ?_⟩
    have hu : u ∈ C := hC (by simp)
    have hw : w ∈ C := hC (by simp)
    simp [hD.add u hu w hw]
  · refine ⟨{u, w}, fun C hC M _ _ D hD => ?_⟩
    have hu : u ∈ C := hC (by simp)
    have hw : w ∈ C := hC (by simp)
    simp [hD.mul u hu w hw, add_comm]
  · refine ⟨∅, fun C _ M _ _ D hD => ?_⟩
    simp [hD.alg a]

theorem kaehler_rel_local : ∀ (A S : Type) [CommRing A] [CommRing S] [Algebra A S] (n : ℕ)
    (x y : Fin n → S), ∑ i, x i • KaehlerDifferential.D A S (y i) = 0 →
    ∃ T : Finset S, ∀ C : Subalgebra A S, (↑T : Set S) ⊆ C → (∀ i, y i ∈ C) →
      ∀ (M : Type) [AddCommGroup M] [Module S M] (D : S → M), IsDerOn C D →
        ∑ i, x i • D (y i) = 0 := by
  intro A S _ _ _ n x y h
  classical
  set v : S →₀ S := ∑ i, single (y i) (x i) with hv
  have hlc : ∀ (M : Type) [AddCommGroup M] [Module S M] (D : S → M),
      Finsupp.linearCombination S D v = ∑ i, x i • D (y i) := by
    intro M _ _ D
    set_option synthInstance.maxHeartbeats 100000 in
      simp [hv, map_sum, Finsupp.linearCombination_single]
  have hmem : v ∈ KaehlerDifferential.kerTotal A S := by
    rw [← KaehlerDifferential.kerTotal_eq, LinearMap.mem_ker, hlc, h]
  obtain ⟨G, hGs, hvG⟩ := Submodule.mem_span_finite_of_mem_span hmem
  have key := fun g (hg : g ∈ G) => kerTotal_gen_local (A := A) g (hGs hg)
  choose F hF using key
  refine ⟨G.attach.biUnion (fun g => F g.1 g.2), ?_⟩
  intro C hC _ M _ _ D hD
  rw [← hlc]
  have hle : Submodule.span S (↑G : Set (S →₀ S)) ≤
      LinearMap.ker (Finsupp.linearCombination S D) := by
    rw [Submodule.span_le]
    intro g hg
    refine hF g hg C (fun z hz => hC ?_) M D hD
    simp only [Finset.coe_biUnion, Finset.coe_attach, Set.mem_univ, Set.iUnion_true,
      Set.mem_iUnion]
    exact ⟨⟨g, hg⟩, hz⟩
  exact hle hvG

end GlobalTheory.AlmostEt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KaehlerRelationOfDerivationOnLargeSubalgebraStatement
open GlobalTheory.AlmostEt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kaehler_relation_of_derivation_on_large_subalgebra : ∀ (A S : Type) [CommRing A] [CommRing S] [Algebra A S] (n : ℕ) (x y : Fin n → S), ∑ i, x i • KaehlerDifferential.D A S (y i) = 0 → ∃ T : Finset S, ∀ C : Subalgebra A S, (↑T : Set S) ⊆ C → (∀ i, y i ∈ C) → ∀ (M : Type) [AddCommGroup M] [Module S M] (D : S → M), IsDerOn C D → ∑ i, x i • D (y i) = 0 := by
  first | exact @GlobalTheory.AlmostEt.kaehler_rel_local | exact GlobalTheory.AlmostEt.kaehler_rel_local | (intros; apply GlobalTheory.AlmostEt.kaehler_rel_local <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationTowerZetaSubOne
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationTowerZetaSubOne
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

namespace GlobalTheory.K5.ZetaNonvanishing₂

variable {Ω : Type} [Field Ω]

theorem valuation_sub_one_pow_sub_le (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (v : Valuation Ω ℝ≥0) (x : Ω) (hx : v x ≤ 1) :
    v ((x - 1) ^ p - (x ^ p - 1)) ≤ v (p : Ω) := by
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp (⟨x, hx⟩ : v.integer) (-1)
  have hr' := congrArg Subtype.val hr
  push_cast at hr'
  have hodd : Odd p := hp.odd_of_ne_two hp2
  rw [hodd.neg_one_pow] at hr'
  have e : (x - 1) ^ p - (x ^ p - 1) = (p : Ω) * (-(x * (r : Ω))) := by
    rw [sub_eq_add_neg x 1, hr']; ring
  rw [e, v.map_mul, v.map_neg, v.map_mul]
  have hr1 : v (r : Ω) ≤ 1 := r.2
  calc v (p : Ω) * (v x * v (r : Ω)) ≤ v (p : Ω) * (1 * 1) := by gcongr
    _ = v (p : Ω) := by simp

theorem valuation_zeta_sub_one : ∀ (p : ℕ) [hpf : Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], p ≠ 2 → ∀ (T : Tower p Ω) (v : Valuation Ω ℝ≥0), v (p : Ω) < 1 → ∀ n : ℕ, 1 ≤ n → v (T.ζ n - 1) < 1 ∧ v (p : Ω) ≤ v (T.ζ 1 - 1) * v (T.ζ n - 1) := by
  intro p hpf Ω _ _ hp2 T v hvp
  have hp := hpf.out

  have hvz : ∀ n, v (T.ζ n) = 1 := by
    intro n
    have h1 : v (T.ζ n) ^ (p ^ n) = 1 := by
      rw [← v.map_pow, (T.prim n).pow_eq_one, v.map_one]
    exact (pow_eq_one_iff_of_nonneg (zero_le') (pow_ne_zero _ hp.ne_zero)).1 h1

  have hlt : ∀ n, v (T.ζ n - 1) < 1 := by
    intro n
    induction n with
    | zero =>
      have : T.ζ 0 = 1 := by
        have := T.prim 0
        rw [pow_zero] at this
        exact IsPrimitiveRoot.one_right_iff.1 this
      simp [this]
    | succ n ih =>
      have hb := valuation_sub_one_pow_sub_le p hp hp2 v (T.ζ (n + 1)) (hvz _).le
      rw [T.ζpow n] at hb
      have h2 : v ((T.ζ (n + 1) - 1) ^ p) < 1 := by
        have : (T.ζ (n + 1) - 1) ^ p = ((T.ζ (n + 1) - 1) ^ p - (T.ζ n - 1)) + (T.ζ n - 1) := by ring
        rw [this]
        exact lt_of_le_of_lt (v.map_add _ _) (max_lt (lt_of_le_of_lt hb hvp) ih)
      rw [v.map_pow] at h2
      by_contra hc
      push_neg at hc
      exact absurd h2 (not_lt.2 (one_le_pow₀ hc))
  intro n hn
  refine ⟨hlt n, ?_⟩

  have hge : v (T.ζ 1 - 1) ≤ v (T.ζ n - 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hz : ∀ k, T.ζ (k + 1) ^ (p ^ k) = T.ζ 1 := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ', pow_mul, T.ζpow, ih]
    have e : T.ζ 1 - 1 = (∑ i ∈ Finset.range (p ^ m), T.ζ (m + 1) ^ i) * (T.ζ (m + 1) - 1) := by
      rw [geom_sum_mul, hz m]
    rw [e, v.map_mul]
    have hs : v (∑ i ∈ Finset.range (p ^ m), T.ζ (m + 1) ^ i) ≤ 1 :=
      v.map_sum_le fun i _ => by rw [v.map_pow, hvz, one_pow]
    calc v (∑ i ∈ Finset.range (p ^ m), T.ζ (m + 1) ^ i) * v (T.ζ (m + 1) - 1)
        ≤ 1 * v (T.ζ (m + 1) - 1) := by gcongr
      _ = v (T.ζ (m + 1) - 1) := one_mul _
  have h1 := GlobalTheory.T.valuation_primitiveRoot_sub_one_pow_pred_eq Ω v p hp (T.ζ 1) (by simpa using T.prim 1)
  have ha1 : v (T.ζ 1 - 1) ≤ 1 := (hlt 1).le
  have hp3 : 2 ≤ p - 1 := by have := hp.two_le; omega
  rw [← h1]
  calc v (T.ζ 1 - 1) ^ (p - 1) ≤ v (T.ζ 1 - 1) ^ 2 := pow_le_pow_of_le_one (zero_le') ha1 hp3
    _ = v (T.ζ 1 - 1) * v (T.ζ 1 - 1) := sq _
    _ ≤ v (T.ζ 1 - 1) * v (T.ζ n - 1) := by gcongr

end GlobalTheory.K5.ZetaNonvanishing₂
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationTowerZetaSubOneStatement
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_tower_zeta_sub_one : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], p ≠ 2 → ∀ (T : Tower p Ω) (v : Valuation Ω ℝ≥0), v (p : Ω) < 1 → ∀ n : ℕ, 1 ≤ n → v (T.ζ n - 1) < 1 ∧ v (p : Ω) ≤ v (T.ζ 1 - 1) * v (T.ζ n - 1) := by
  first | exact @GlobalTheory.K5.ZetaNonvanishing₂.valuation_zeta_sub_one | exact GlobalTheory.K5.ZetaNonvanishing₂.valuation_zeta_sub_one | (intros; apply GlobalTheory.K5.ZetaNonvanishing₂.valuation_zeta_sub_one <;> assumption)
end
end
