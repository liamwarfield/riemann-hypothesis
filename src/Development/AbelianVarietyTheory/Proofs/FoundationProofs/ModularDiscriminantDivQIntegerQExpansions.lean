module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormMulTransposeMulFormInvMem
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsPolynomialModularJOfHasQExpansion
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.RosatiAdj
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGaloisInvariantValuationIntegersEqIntegral

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularDiscriminantDivQIntegerQExpansions
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularDiscriminantDivQIntegerQExpansions
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

noncomputable section

namespace GlobalTheory.FN

private theorem qParam_one_eq (τ : ℍ) :
    Function.Periodic.qParam 1 (τ : ℂ) = Complex.exp (2 * Real.pi * Complex.I * τ) := by
  simp [Function.Periodic.qParam]

private theorem disc_vadd (τ : ℍ) :
    ModularForm.discriminant ((1 : ℝ) +ᵥ τ) = ModularForm.discriminant τ := by
  have h := SlashInvariantFormClass.periodic_comp_ofComplex CuspForm.discriminant
    one_mem_strictPeriods_SL (τ : ℂ)
  simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply] at h
  have e : UpperHalfPlane.ofComplex ((τ : ℂ) + ((1 : ℝ) : ℂ)) = (1 : ℝ) +ᵥ τ := by
    ext
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos (by simpa using τ.im_pos)]
    simp [add_comm]
  rw [e] at h
  simpa [CuspForm.coe_discriminant] using h

private theorem qParam_ne (τ : ℍ) : Function.Periodic.qParam 1 (τ : ℂ) ≠ 0 :=
  Function.Periodic.qParam_ne_zero _

theorem dd_div_q_and_q_div_dd :
    (∃ c : ℕ → ℤ, c 0 = 1 ∧ HasQ 1 (fun τ => DD τ / Complex.exp (2 * Real.pi * Complex.I * τ))
      fun n => (c n : ℂ)) ∧
    ∃ c : ℕ → ℤ, c 0 = 1 ∧ HasQ 1 (fun τ => Complex.exp (2 * Real.pi * Complex.I * τ) / DD τ)
      fun n => (c n : ℂ) := by
  obtain ⟨U, hU0, hU⟩ := GlobalTheory.exists_hasQExpansion_discriminant
  have hu : GlobalTheory.HasQExpansion 1 (fun τ ↦ ModularForm.discriminant τ / Function.Periodic.qParam 1 τ)
      (PowerSeries.map (Int.castRingHom ℂ) U) :=
    .of_qParam_mul (hU.congr fun τ ↦ by field_simp [qParam_ne τ])
  have hcast : ∀ (V : PowerSeries ℤ) (g : ℍ → ℂ),
      GlobalTheory.HasQExpansion 1 g (PowerSeries.map (Int.castRingHom ℂ) V) →
        HasQ 1 g fun n => ((PowerSeries.coeff n V : ℤ) : ℂ) := by
    intro V g hg
    have := (hasQ_coeff_iff_hasQExpansion 1 g _).mpr (by exact_mod_cast hg)
    simpa [PowerSeries.coeff_map] using this
  refine ⟨⟨fun n => PowerSeries.coeff n U, hU0, ?_⟩, ?_⟩
  · have := hcast U _ hu
    convert this using 2 with τ
    rw [qParam_one_eq]; rfl

  set f : ℍ → ℂ := fun τ ↦ Function.Periodic.qParam 1 τ / ModularForm.discriminant τ with hf
  have hper : ∀ τ : ℍ, f ((1 : ℝ) +ᵥ τ) = f τ := fun τ ↦ by
    simp only [hf, GlobalTheory.qParam_one_vadd, disc_vadd]
  have hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f :=
    ((GlobalTheory.HasQExpansion.qParam 1).mdifferentiable one_pos).div CuspForm.discriminant.holo'
      ModularForm.discriminant_ne_zero
  have hbdd : UpperHalfPlane.IsBoundedAtImInfty f := by
    have ht := (tendsto_const_nhds (x := (1 : ℂ))).div (hu.tendsto one_pos)
      (by simp [PowerSeries.coeff_map, hU0])
    have : f = fun τ ↦ 1 / (ModularForm.discriminant τ / Function.Periodic.qParam 1 τ) := by
      funext τ; simp only [hf]; field_simp
    rw [this]
    exact ht.isBigO_one ℝ
  have h1 := GlobalTheory.HasQExpansion.of_periodic one_pos
    (GlobalTheory.periodic_comp_ofComplex_of_vadd hper) hhol hbdd
  have h2 := (h1.mul hu).unique one_pos ((GlobalTheory.HasQExpansion.const 1 (1 : ℂ)).congr fun τ ↦ by
    simp only [hf]; field_simp [qParam_ne τ, ModularForm.discriminant_ne_zero τ])
  have hUV : U * U.invOfUnit 1 = 1 := PowerSeries.mul_invOfUnit U 1 (by simpa using hU0)
  have h3 : UpperHalfPlane.qExpansion 1 f =
      PowerSeries.map (Int.castRingHom ℂ) (U.invOfUnit 1) := by
    have e := congrArg (· * PowerSeries.map (Int.castRingHom ℂ) (U.invOfUnit 1)) h2
    simp only [mul_assoc, ← map_mul, hUV, map_one, mul_one, one_mul] at e
    exact e
  refine ⟨fun n => PowerSeries.coeff n (U.invOfUnit 1), ?_, ?_⟩
  · simp
  · have := hcast _ _ (h3 ▸ h1)
    convert this using 2 with τ
    simp only [hf, qParam_one_eq]; rfl

end GlobalTheory.FN
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularDiscriminantDivQIntegerQExpansionsStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modularDiscriminant_div_q_integer_qExpansions : (∃ c : ℕ → ℤ, c 0 = 1 ∧ HasQ 1 (fun τ => DD τ / Complex.exp (2 * Real.pi * Complex.I * τ)) fun n => (c n : ℂ)) ∧ ∃ c : ℕ → ℤ, c 0 = 1 ∧ HasQ 1 (fun τ => Complex.exp (2 * Real.pi * Complex.I * τ) / DD τ) fun n => (c n : ℂ) := by
  first | exact @GlobalTheory.FN.dd_div_q_and_q_div_dd | exact GlobalTheory.FN.dd_div_q_and_q_div_dd | (intros; apply GlobalTheory.FN.dd_div_q_and_q_div_dd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesCongruenceSubgroupInvMem
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesCongruenceSubgroupInvMem
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

noncomputable section

namespace GlobalTheory.PsType

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

def congrAlg (ψ : Fin n → kˣ →* ℂˣ) (hψ : Ordered ψ) :
    Subalgebra 𝒪[k] (Matrix (Fin n) (Fin n) 𝒪[k]) where
  carrier := {M | ∀ i j : Fin n, i < j → Triv (ψ i / ψ j) ((M i j : 𝒪[k]) : k)}
  mul_mem' := by
    intro A B hA hB i j hij
    simp only [Set.mem_setOf_eq] at hA hB
    rw [Matrix.mul_apply]
    push_cast
    refine Finset.sum_induction _ (fun x => Triv (ψ i / ψ j) x) (fun x y hx hy => triv_add _ x y hx hy)
      (triv_zero _) ?_
    intro l _
    have hAv : valuation k ((A i l : 𝒪[k]) : k) ≤ 1 := (A i l).2
    have hBv : valuation k ((B l j : 𝒪[k]) : k) ≤ 1 := (B l j).2
    have h1 : valuation k ((A i l : 𝒪[k]) : k) * valuation k ((B l j : 𝒪[k]) : k) ≤
        valuation k ((B l j : 𝒪[k]) : k) := mul_le_of_le_one_left' hAv
    have h2 : valuation k ((A i l : 𝒪[k]) : k) * valuation k ((B l j : 𝒪[k]) : k) ≤
        valuation k ((A i l : 𝒪[k]) : k) := mul_le_of_le_one_right' hBv
    rcases le_or_gt l i with hli | hil
    · refine triv_mono _ ((B l j : 𝒪[k]) : k) _ (by rw [map_mul]; exact h1) ?_
      exact hψ l i j j hli hij.le le_rfl _ (hB l j (lt_of_le_of_lt hli hij))
    rcases le_or_gt j l with hjl | hlj
    · refine triv_mono _ ((A i l : 𝒪[k]) : k) _ (by rw [map_mul]; exact h2) ?_
      exact hψ i i j l le_rfl hij.le hjl _ (hA i l hil)
    · have e : ψ i / ψ l * (ψ l / ψ j) = ψ i / ψ j := div_mul_div_cancel _ _ _
      rw [← e]
      exact triv_mul _ _ _ (triv_mono _ ((A i l : 𝒪[k]) : k) _ (by rw [map_mul]; exact h2) (hA i l hil))
        (triv_mono _ ((B l j : 𝒪[k]) : k) _ (by rw [map_mul]; exact h1) (hB l j hlj))
  one_mem' := by
    intro i j hij
    simp [Matrix.one_apply_ne hij.ne, triv_zero]
  add_mem' := by
    intro A B hA hB i j hij
    simp only [Set.mem_setOf_eq] at hA hB
    simpa using triv_add _ _ _ (hA i j hij) (hB i j hij)
  zero_mem' := by
    intro i j hij
    simp [triv_zero]
  algebraMap_mem' := by
    intro c i j hij
    simp [Matrix.algebraMap_eq_diagonal, Matrix.diagonal_apply_ne _ hij.ne, triv_zero]

theorem inv_val_mem_adjoin {R : Type} [CommRing R] {m : ℕ} (g : GL (Fin m) R) :
    ((g⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) ∈ Algebra.adjoin R {(g : Matrix (Fin m) (Fin m) R)} := by
  set A : Matrix (Fin m) (Fin m) R := (g : Matrix (Fin m) (Fin m) R)
  set p := A.charpoly
  have hCH : Polynomial.aeval A p = 0 := Matrix.aeval_self_charpoly A
  have hdec : p.divX * Polynomial.X + Polynomial.C (p.coeff 0) = p := Polynomial.divX_mul_X_add p
  have hdet : A.det = (-1) ^ Fintype.card (Fin m) * p.coeff 0 := Matrix.det_eq_sign_charpoly_coeff A
  have hu : IsUnit (p.coeff 0) := by
    have h := (Matrix.isUnit_iff_isUnit_det A).mp (Units.isUnit g)
    rw [hdet] at h
    exact isUnit_of_mul_isUnit_right h
  obtain ⟨u, hu⟩ := hu
  have h1 : Polynomial.aeval A p.divX * A = -algebraMap R _ (p.coeff 0) := by
    rw [← hdec] at hCH
    simp only [map_add (f := _), map_mul, Polynomial.aeval_X, Polynomial.aeval_C] at hCH
    exact eq_neg_of_add_eq_zero_left hCH
  have key : ((-(↑u⁻¹ : R)) • Polynomial.aeval A p.divX) * A = 1 := by
    rw [smul_mul_assoc, h1, Algebra.algebraMap_eq_smul_one, ← hu, neg_smul_neg, smul_smul,
      Units.inv_mul, one_smul]
  have e : ((g⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) = (-(↑u⁻¹ : R)) • Polynomial.aeval A p.divX :=
    Units.inv_eq_of_mul_eq_one_left key
  rw [e]
  exact Subalgebra.smul_mem _ (Polynomial.aeval_mem_adjoin_singleton R A) _

end GlobalTheory.PsType

theorem GlobalTheory.PsType.grp_inv_mem : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), Ordered ψ → ∀ a ∈ grp ψ, a⁻¹ ∈ grp ψ := by
  intro k _ _ _ _ n ψ hψ a ha
  obtain ⟨haK, hat⟩ := ha
  obtain ⟨g, rfl⟩ := haK
  have hg : (g : Matrix (Fin n) (Fin n) 𝒪[k]) ∈ congrAlg ψ hψ := fun i j hij => hat i j hij
  have hinv : ((g⁻¹ : GL (Fin n) 𝒪[k]) : Matrix (Fin n) (Fin n) 𝒪[k]) ∈ congrAlg ψ hψ :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr hg) (inv_val_mem_adjoin g)
  refine ⟨inv_mem ⟨g, rfl⟩, ?_⟩
  intro i j hij
  rw [← map_inv]
  exact hinv i j hij
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesCongruenceSubgroupInvMemStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalSeriesCongruenceSubgroup_inv_mem : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), Ordered ψ → ∀ a ∈ grp ψ, a⁻¹ ∈ grp ψ := by
  first | exact @GlobalTheory.PsType.grp_inv_mem | exact GlobalTheory.PsType.grp_inv_mem | (intros; apply GlobalTheory.PsType.grp_inv_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNeZeroHalfStandardAltFormConstOfExponentOn
open Function

namespace GlobalTheory

section General

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem pow_succ_dvd_bilin_of_const_on_cosets (h2 : IsUnit (2 : R)) (r : R)
    (B : LinearMap.BilinForm R M) (hB : ∀ x y, B x y = B y x) (T : Set M)
    (hT : ∀ x, ∃ t ∈ T, ∃ a, x = t + r • a) (c : R) (hc : ∀ t ∈ T, B t t = c) (i : ℕ)
    (hi : ∀ x y, r ^ i ∣ B x y) (x y : M) : r ^ (i + 1) ∣ B x y := by
  have h1 : ∀ z, r ^ (i + 1) ∣ B z z - c := by
    intro z
    obtain ⟨t, ht, a, rfl⟩ := hT z
    have : B (t + r • a) (t + r • a) - c = (B t a + B a t + r * B a a) * r := by
      simp only [map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        ← hc t ht]
      ring
    rw [this, pow_succ]
    exact mul_dvd_mul_right (((hi _ _).add (hi _ _)).add ((hi _ _).mul_left _)) r
  have h0 : r ^ (i + 1) ∣ c := by simpa using h1 0
  have h3 : ∀ z, r ^ (i + 1) ∣ B z z := fun z => by simpa using (h1 z).add h0
  have h4 : 2 * B x y = B (x + y) (x + y) - B x x - B y y := by
    simp only [map_add (f := _), LinearMap.add_apply, hB y x]
    ring
  exact h2.dvd_mul_left.1 (h4 ▸ ((h3 _).sub (h3 _)).sub (h3 _))

theorem bilin_eq_zero_of_const_on_cosets (h2 : IsUnit (2 : R)) {r : R} (hr : IsNilpotent r)
    (B : LinearMap.BilinForm R M) (hB : ∀ x y, B x y = B y x) (T : Set M)
    (hT : ∀ x, ∃ t ∈ T, ∃ a, x = t + r • a) (c : R) (hc : ∀ t ∈ T, B t t = c) : B = 0 := by
  have h : ∀ (i : ℕ) (x y : M), r ^ i ∣ B x y := by
    intro i
    induction i with
    | zero => simp
    | succ i ih => exact pow_succ_dvd_bilin_of_const_on_cosets h2 r B hB T hT c hc i ih
  obtain ⟨k, hk⟩ := hr
  ext x y
  simpa [hk] using h k x y

theorem end_eq_zero_of_quad_const_on_cosets (h2 : IsUnit (2 : R)) {r : R} (hr : IsNilpotent r)
    (ω : LinearMap.BilinForm R M) (hω : Injective ω) (S : M →ₗ[R] M)
    (hS : ∀ x y, ω (S x) y = ω (S y) x) (u : Rˣ) (q : M → R)
    (hq : ∀ x, 2 * q x = u * ω (S x) x) (T : Set M)
    (hT : ∀ x, ∃ t ∈ T, ∃ a, x = t + r • a) (c : R) (hc : ∀ t ∈ T, q t = c) : S = 0 := by
  have h : (ω ∘ₗ S : LinearMap.BilinForm R M) = 0 := by
    refine bilin_eq_zero_of_const_on_cosets h2 hr (ω ∘ₗ S) hS T hT (↑u⁻¹ * (2 * c)) fun t ht => ?_
    rw [← hc t ht, hq, Units.inv_mul_cancel_left]
    rfl
  ext x
  exact hω ((LinearMap.congr_fun h x).trans (by simp))

end General

section ZMod

variable {n k : ℕ}

theorem isUnit_two_zmod_pow (hn : Odd n) (k : ℕ) : IsUnit (2 : ZMod (n ^ k)) := by
  have h : Nat.Coprime 2 (n ^ k) := (Nat.coprime_two_left.2 hn).pow_right k
  simpa using (ZMod.isUnit_iff_coprime 2 (n ^ k)).2 h

theorem exists_eq_nsmul_of_nsmul_eq_zero_zmod (hn : n ≠ 0) (hk : 2 ≤ k) (x : ZMod (n ^ k))
    (hx : n • x = 0) : ∃ a, x = n • a := by
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
  have h1 : (((n : ℤ) * z : ℤ) : ZMod (n ^ (j + 2))) = 0 := by
    rw [← hx]; simp
  obtain ⟨w, hw⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h1
  have h2 : z = n * ((n : ℤ) ^ j * w) := by
    apply mul_left_cancel₀ (Int.natCast_ne_zero.2 hn)
    rw [hw]; push_cast; ring
  exact ⟨(((n : ℤ) ^ j * w : ℤ) : ZMod (n ^ (j + 2))), by rw [h2]; simp⟩

end ZMod

section LevelForm

open ReciprocityTheory.ChartRestriction.G.Out

theorem injective_toBilin'_stdSymp {R : Type*} [CommRing R] (g : ℕ) :
    Injective (Matrix.toBilin' (Matrix.of fun i j => ((stdSymp g i j : ℤ) : R))) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  funext i
  have key : ∀ j, ∑ l, x l * ((stdSymp g l j : ℤ) : R) = 0 := fun j => by
    have := LinearMap.congr_fun hx (Pi.single j 1)
    simpa [Matrix.toBilin'_apply, Pi.single_apply] using this
  by_cases hi : (i : ℕ) < g
  · have h := key ⟨i + g, by omega⟩
    rw [Finset.sum_eq_single i] at h
    · simpa [stdSymp, hi] using h
    · intro l _ hl
      have h1 : (l : ℕ) ≠ i := fun h => hl (Fin.ext h)
      have : stdSymp g l ⟨i + g, by omega⟩ = 0 := by
        unfold stdSymp
        rw [if_neg (by simp only; omega), if_neg (by simp only; omega)]
      simp [this]
    · simp
  · have hi2 := i.2
    have h := key ⟨i - g, by omega⟩
    rw [Finset.sum_eq_single i] at h
    · have : stdSymp g i ⟨i - g, by omega⟩ = -1 := by
        unfold stdSymp
        rw [if_neg (by simp only; omega), if_pos (by simp only; omega)]
      simpa [this] using h
    · intro l _ hl
      have h1 : (l : ℕ) ≠ i := fun h => hl (Fin.ext h)
      have : stdSymp g l ⟨i - g, by omega⟩ = 0 := by
        unfold stdSymp
        rw [if_neg (by simp only; omega), if_neg (by simp only; omega)]
      simp [this]
    · simp

end LevelForm

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationSubringNonunitsPowModEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationSubringNonunitsPowModEqZero
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory

open Polynomial in
theorem cgA_pow_of_mem_nonunits {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ)
    [hl : Fact l.Prime] (A : ValuationSubring Ω) (hlA : ((l : ℕ) : Ω) ∈ A.nonunits)
    (x : Ω) (hx : x ∈ A.nonunits) : ∃ k : ℕ, CgA A l 1 (x ^ k) 0 := by
  classical
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  have hl0 : ((l : ℕ) : Ω) ≠ 0 := by exact_mod_cast hl.out.ne_zero
  have hvl : A.valuation (l : Ω) < 1 := (A.mem_nonunits_iff).1 hlA
  have hvx : A.valuation x < 1 := (A.mem_nonunits_iff).1 hx
  have hvl0 : A.valuation (l : Ω) ≠ 0 := by simpa using hl0
  have key : ∀ k : ℕ, A.valuation x ^ k ≤ A.valuation (l : Ω) → CgA A l 1 (x ^ k) 0 := by
    intro k hk
    refine ⟨x ^ k / l, ?_, ?_⟩
    · rw [← A.valuation_le_one_iff, map_div₀, map_pow]
      exact (div_le_one₀ (zero_lt_iff.2 hvl0)).2 hk
    · rw [sub_zero, pow_one]; field_simp
  by_contra H
  push_neg at H
  have hlt : ∀ k : ℕ, A.valuation (l : Ω) < A.valuation x ^ k :=
    fun k => not_le.1 (fun h => H k (key k h))
  have hx0 : x ≠ 0 := by
    intro h
    have := hlt 1
    simp [h] at this
  have hvx0 : A.valuation x ≠ 0 := by simpa using hx0

  have hint : ∀ n : ℤ, A.valuation (n : Ω) ≤ 1 := fun n =>
    (A.valuation_le_one_iff _).2 (intCast_mem A n)
  have hdvd : ∀ n : ℤ, (l : ℤ) ∣ n → A.valuation (n : Ω) ≤ A.valuation (l : Ω) := by
    rintro n ⟨m, rfl⟩
    push_cast
    rw [map_mul]
    exact mul_le_of_le_one_right' (hint m)
  have hpl : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl.out
  have hunit : ∀ n : ℤ, ¬ (l : ℤ) ∣ n → A.valuation (n : Ω) = 1 := by
    intro n hn
    refine le_antisymm (hint n) (not_lt.1 fun h => ?_)
    obtain ⟨a, b, hab⟩ := (Prime.coprime_iff_not_dvd hpl).2 hn
    have h1 : ((a : Ω) * (l : Ω) + (b : Ω) * (n : Ω)) = 1 := by exact_mod_cast hab
    have h2 : A.valuation ((a : Ω) * (l : Ω) + (b : Ω) * (n : Ω)) < 1 := by
      apply Valuation.map_add_lt
      · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint a)) hvl
      · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint b)) h
    rw [h1, map_one] at h2
    exact lt_irrefl _ h2

  obtain ⟨p, hp0, hpx⟩ := (IsFractionRing.isAlgebraic_iff ℤ ℚ Ω).2 (Algebra.IsAlgebraic.isAlgebraic x)
  set q := p.primPart with hqdef
  have hqprim : q.IsPrimitive := isPrimitive_primPart p
  have hqx : aeval x q = 0 := by
    have hc : p.content ≠ 0 := by
      intro h; exact hp0 ((content_eq_zero_iff).1 h)
    have h := hpx
    rw [eq_C_content_mul_primPart p, map_mul, aeval_C] at h
    rcases mul_eq_zero.1 h with h' | h'
    · exfalso; apply hc; simpa using h'
    · exact h'
  have hex : ∃ i, ¬ (l : ℤ) ∣ q.coeff i := by
    by_contra h
    push_neg at h
    have hu := hqprim (l : ℤ) ((C_dvd_iff_dvd_coeff _ _).2 h)
    exact hpl.not_unit hu
  set i0 := Nat.find hex with hi0
  have hi0spec : ¬ (l : ℤ) ∣ q.coeff i0 := Nat.find_spec hex
  have hi0min : ∀ i < i0, (l : ℤ) ∣ q.coeff i := fun i hi => by
    simpa using Nat.find_min hex hi
  have hi0deg : i0 < q.natDegree + 1 := by
    by_contra h
    apply hi0spec
    rw [coeff_eq_zero_of_natDegree_lt (by omega)]
    exact dvd_zero _
  set f : ℕ → Ω := fun i => (q.coeff i : Ω) * x ^ i with hf
  have hsum : aeval x q = ∑ i ∈ Finset.range (q.natDegree + 1), f i := by
    rw [aeval_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [hf, zsmul_eq_mul]
  have hfi0 : A.valuation (f i0) = A.valuation x ^ i0 := by
    simp only [hf, map_mul, map_pow, hunit _ hi0spec, one_mul]
  have hg : A.valuation x ^ i0 ≠ 0 := pow_ne_zero _ hvx0
  have hrest : A.valuation (∑ i ∈ (Finset.range (q.natDegree + 1)).erase i0, f i)
      < A.valuation x ^ i0 := by
    apply Valuation.map_sum_lt _ hg
    intro i hi
    have hne : i ≠ i0 := Finset.ne_of_mem_erase hi
    simp only [hf, map_mul, map_pow]
    rcases lt_or_gt_of_ne hne with h | h
    · calc A.valuation (q.coeff i : Ω) * A.valuation x ^ i
            ≤ A.valuation (l : Ω) * 1 :=
              mul_le_mul' (hdvd _ (hi0min i h)) (pow_le_one₀ zero_le' hvx.le)
        _ = A.valuation (l : Ω) := mul_one _
        _ < A.valuation x ^ i0 := hlt i0
    · calc A.valuation (q.coeff i : Ω) * A.valuation x ^ i
            ≤ 1 * A.valuation x ^ i := mul_le_mul' (hint _) le_rfl
        _ = A.valuation x ^ i := one_mul _
        _ < A.valuation x ^ i0 := pow_lt_pow_right_of_lt_one₀ (zero_lt_iff.2 hvx0) hvx h
  have htot : A.valuation (aeval x q) = A.valuation x ^ i0 := by
    rw [hsum, ← Finset.add_sum_erase _ _ (Finset.mem_range.2 hi0deg),
      Valuation.map_add_eq_of_lt_left _ (by rw [hfi0]; exact hrest), hfi0]
  rw [hqx, map_zero] at htot
  exact hg htot.symm

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationSubringNonunitsPowModEqZeroStatement
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuationSubring_nonunits_pow_modEq_zero : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), ((l : ℕ) : Ω) ∈ A.nonunits → ∀ x ∈ A.nonunits, ∃ k : ℕ, CgA A l 1 (x ^ k) 0 := by
  first | exact @GlobalTheory.cgA_pow_of_mem_nonunits | exact GlobalTheory.cgA_pow_of_mem_nonunits | (intros; apply GlobalTheory.cgA_pow_of_mem_nonunits <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLogDerivQExpansionModPrimePowRescale
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLogDerivQExpansionModPrimePowRescale
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

noncomputable section

namespace GlobalTheory.DlRescale

def mulN (N : ℕ) : ℚ →+ ℚ := AddMonoidHom.mulLeft (N : ℚ)

theorem mulN_le (N : ℕ) (hN : 0 < N) (g g' : ℚ) : mulN N g ≤ mulN N g' ↔ g ≤ g' := by
  have : (0:ℚ) < N := by exact_mod_cast hN
  simp [mulN, mul_le_mul_iff_of_pos_left this]

theorem mulN_inj (N : ℕ) (hN : 0 < N) : Function.Injective (mulN N) := fun g g' h =>
  le_antisymm ((mulN_le N hN g g').1 h.le) ((mulN_le N hN g' g).1 h.ge)

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

def resc (N : ℕ) (hN : 0 < N) : HahnSeries ℚ Ω →+* HahnSeries ℚ Ω :=
  HahnSeries.embDomainRingHom (mulN N) (mulN_inj N hN) (mulN_le N hN)

theorem resc_coeff (N : ℕ) (hN : 0 < N) (ψ : HahnSeries ℚ Ω) (r : ℚ) :
    (resc N hN ψ).coeff r = ψ.coeff (r / N) := by
  have hN' : (N:ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have e : r = mulN N (r / N) := by simp [mulN]; field_simp
  conv_lhs => rw [e]
  simp only [resc, HahnSeries.embDomainRingHom_apply]
  exact HahnSeries.embDomain_coeff (f := ⟨⟨mulN N, mulN_inj N hN⟩, mulN_le N hN _ _⟩)

theorem forall_div (N : ℕ) (hN : 0 < N) (Q : ℚ → Prop) : (∀ r : ℚ, Q (r / N)) ↔ ∀ r, Q r := by
  have hN' : (N:ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  refine ⟨fun h r => ?_, fun h r => h _⟩
  have := h (N * r)
  rwa [mul_div_cancel_left₀ r hN'] at this

theorem theta_resc (N : ℕ) (hN : 0 < N) (s : ℚ) (ψ : HahnSeries ℚ Ω) :
    theta (s / N) (resc N hN ψ) = resc N hN (theta s ψ) := by
  ext r
  simp only [theta, resc_coeff]
  congr 2
  ring

theorem prim_resc (A : ValuationSubring Ω) (N : ℕ) (hN : 0 < N) (ψ : HahnSeries ℚ Ω) :
    Prim A (resc N hN ψ) ↔ Prim A ψ := by
  unfold Prim
  simp only [resc_coeff]
  rw [forall_div N hN (fun r => ψ.coeff r ∈ A)]
  constructor
  · rintro ⟨h1, r, h2, h3⟩; exact ⟨h1, r / N, h2, h3⟩
  · rintro ⟨h1, r, h2, h3⟩
    have hN' : (N:ℚ) ≠ 0 := by exact_mod_cast hN.ne'
    refine ⟨h1, N * r, ?_⟩
    rw [mul_div_cancel_left₀ r hN']; exact ⟨h2, h3⟩

theorem eOm_zero (ε : Ω →+* ℂ) : eOm ε 0 = 1 := by
  unfold eOm
  simp only [Rat.cast_zero, mul_zero, Complex.exp_zero]
  rw [← map_one ε]
  exact Function.leftInverse_invFun ε.injective 1

theorem exp_sl_diag (ε : Ω →+* ℂ) (X : Tower Ω ε) (N : ℕ) (hN : 0 < N) (u : X.K) :
    X.exp (X.sl (toGQ !![(N : ℤ), 0; 0, 1]) u) = resc N hN (X.exp u) := by
  have hdet : (0 : ℤ) < (!![(N : ℤ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).det := by
    simp [Matrix.det_fin_two]; exact_mod_cast hN
  have e00 : ent (toGQ !![(N : ℤ), 0; 0, 1]) 0 0 = N := by simp [ent, toGQ, hN, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  have e01 : ent (toGQ !![(N : ℤ), 0; 0, 1]) 0 1 = 0 := by simp [ent, toGQ, hN, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  have e10 : ent (toGQ !![(N : ℤ), 0; 0, 1]) 1 0 = 0 := by simp [ent, toGQ, hN, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  have e11 : ent (toGQ !![(N : ℤ), 0; 0, 1]) 1 1 = 1 := by simp [ent, toGQ, hN, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  have hN' : (N:ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  ext r
  rw [resc_coeff]
  have h := X.exp_upper (toGQ !![(N : ℤ), 0; 0, 1]) e10 u (r / N)
  rw [e00, e01, e11, mul_zero, zero_div, eOm_zero, one_mul, div_one, div_mul_cancel₀ r hN'] at h
  exact h

end GlobalTheory.DlRescale

end

open GlobalTheory.DlRescale in
theorem GlobalTheory.Glue.isDl_rescale : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), ((l : ℕ) : Ω) ∈ A.nonunits → ∀ (n N : ℕ) (s : ℚ) (f : X.K) (φ φ' : HahnSeries ℚ Ω), 0 < N → (∀ r : ℚ, φ'.coeff r = φ.coeff (r / N)) → (IsDl X A l n s f φ ↔ IsDl X A l n (s / N) (X.sl (toGQ !![(N : ℤ), 0; 0, 1]) f) φ') := by
  intro Ω _ _ _ ε X _ l _ A _ n N s f φ φ' hN hφ
  have hφ' : φ' = resc N hN φ := by ext r; rw [hφ, resc_coeff]
  subst hφ'
  have hexp := exp_sl_diag ε X N hN
  set g := toGQ !![(N : ℤ), 0; 0, 1]
  have key : ∀ a b : X.K, (∀ r, CgA A l n ((resc N hN φ * X.exp (X.sl g a) * X.exp (X.sl g b)).coeff r)
      ((theta (s / N) (X.exp (X.sl g a)) * X.exp (X.sl g b) - X.exp (X.sl g a) * theta (s / N) (X.exp (X.sl g b))).coeff r)) ↔
      ∀ r, CgA A l n ((φ * X.exp a * X.exp b).coeff r) ((theta s (X.exp a) * X.exp b - X.exp a * theta s (X.exp b)).coeff r) := by
    intro a b
    simp only [hexp, theta_resc, ← map_mul, ← map_sub, resc_coeff]
    exact forall_div N hN (fun r => CgA A l n ((φ * X.exp a * X.exp b).coeff r) ((theta s (X.exp a) * X.exp b - X.exp a * theta s (X.exp b)).coeff r))
  have hA : (∀ r, (resc N hN φ).coeff r ∈ A) ↔ ∀ r, φ.coeff r ∈ A := by
    simp only [resc_coeff]; exact forall_div N hN (fun r => φ.coeff r ∈ A)
  constructor
  · rintro ⟨h0, a, b, κ, hκ, hfb, pa, pb, hc⟩
    refine ⟨hA.2 h0, X.sl g a, X.sl g b, κ, hκ, ?_, ?_, ?_, (key a b).2 hc⟩
    · rw [← map_mul, hfb, map_mul, AlgEquiv.commutes]
    · rw [hexp]; exact (prim_resc A N hN _).2 pa
    · rw [hexp]; exact (prim_resc A N hN _).2 pb
  · rintro ⟨h0, a', b', κ, hκ, hfb, pa, pb, hc⟩
    obtain ⟨a, rfl⟩ := (X.sl g).surjective a'
    obtain ⟨b, rfl⟩ := (X.sl g).surjective b'
    refine ⟨hA.1 h0, a, b, κ, hκ, ?_, ?_, ?_, (key a b).1 hc⟩
    · apply (X.sl g).injective
      rw [map_mul, map_mul, AlgEquiv.commutes]; exact hfb
    · rw [hexp] at pa; exact (prim_resc A N hN _).1 pa
    · rw [hexp] at pb; exact (prim_resc A N hN _).1 pb
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLogDerivQExpansionModPrimePowRescaleStatement
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLogDerivQExpansionModPrimePow_rescale : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), ((l : ℕ) : Ω) ∈ A.nonunits → ∀ (n N : ℕ) (s : ℚ) (f : X.K) (φ φ' : HahnSeries ℚ Ω), 0 < N → (∀ r : ℚ, φ'.coeff r = φ.coeff (r / N)) → (IsDl X A l n s f φ ↔ IsDl X A l n (s / N) (X.sl (toGQ !![(N : ℤ), 0; 0, 1]) f) φ') := by
  first | exact @GlobalTheory.Glue.isDl_rescale | exact GlobalTheory.Glue.isDl_rescale | (intros; apply GlobalTheory.Glue.isDl_rescale <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraicElementApproximation
open GlobalTheory.K5 Polynomial
open scoped NNReal

namespace GlobalTheory.K5.Dense

theorem exists_near_root {Ωl : Type} [Field Ωl] [CharZero Ωl] (v : Valuation Ωl ℝ≥0)
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] (j : Ω →+* Ωl) (e : Ωl) (t : ℝ≥0) (Q : ℤ[X])
    (h : v (Q.eval₂ (Int.castRingHom Ωl) e) < v (Q.leadingCoeff : Ωl) * t ^ Q.natDegree) :
    ∃ a : Ω, v (e - j a) < t := by
  have : CharZero Ω := j.charZero
  by_contra hcon
  push Not at hcon
  set R : Polynomial Ω := Q.map (Int.castRingHom Ω) with hR
  have hinj : Function.Injective (Int.castRingHom Ω) := Int.cast_injective
  have hdeg : R.natDegree = Q.natDegree := natDegree_map_eq_of_injective hinj Q
  have hlc : R.leadingCoeff = (Q.leadingCoeff : Ω) := leadingCoeff_map_of_injective hinj Q
  have hcard : Multiset.card R.roots = R.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hprod := C_leadingCoeff_mul_prod_multiset_X_sub_C hcard
  have h1 : Q.eval₂ (Int.castRingHom Ωl) e = R.eval₂ j e := by
    rw [hR, eval₂_map]
    congr 1
    exact RingHom.ext_int _ _
  have h2 : R.eval₂ j e = (Q.leadingCoeff : Ωl) * (R.roots.map fun a => e - j a).prod := by
    conv_lhs => rw [← hprod]
    rw [eval₂_mul, eval₂_C, eval₂_multiset_prod, Multiset.map_map, hlc, map_intCast]
    simp
  rw [h1, h2, map_mul, map_multiset_prod, Multiset.map_map] at h
  have h3 : t ^ Q.natDegree ≤ (R.roots.map (v ∘ fun a => e - j a)).prod := by
    have := Multiset.pow_card_le_prod (s := R.roots.map (v ∘ fun a => e - j a)) (a := t) (by
      intro x hx
      obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 hx
      exact hcon a)
    rwa [Multiset.card_map, hcard, hdeg] at this
  exact absurd h (not_lt.2 (by gcongr))

theorem exists_approx {p : ℕ} [Fact p.Prime] (P : ℤ_[p][X]) (N : ℕ) :
    ∃ (Q : ℤ[X]) (R : ℤ_[p][X]), Q.natDegree ≤ P.natDegree ∧
      P = Q.map (Int.castRingHom ℤ_[p]) + C ((p : ℤ_[p]) ^ N) * R := by
  have h : ∀ x : ℤ_[p], ∃ (m : ℤ) (r : ℤ_[p]), x = m + (p : ℤ_[p]) ^ N * r := by
    intro x
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.1 (PadicInt.appr_spec N x)
    exact ⟨PadicInt.appr x N, r, by push_cast; linear_combination hr⟩
  choose m r hmr using h
  refine ⟨∑ i ∈ Finset.range (P.natDegree + 1), monomial i (m (P.coeff i)),
    ∑ i ∈ Finset.range (P.natDegree + 1), monomial i (r (P.coeff i)), ?_, ?_⟩
  · refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
    exact (natDegree_monomial_le _).trans (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [Polynomial.map_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      conv_lhs => rw [P.as_sum_range]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_monomial, C_mul_monomial, ← map_add (f := _), eq_intCast, ← hmr]

theorem exists_cong : ∀ (p : ℕ) [Fact p.Prime] (Ωl : Type) [Field Ωl] [Algebra (O0 p) Ωl],
    IsClo p Ωl → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (j : Ω →+* Ωl) (k : ℕ) (e : Ωl),
    IsInt (p := p) e → IsAlgZp (p := p) e → ∃ a : Ω, IsInt (p := p) (j a) ∧ Cong (p := p) k e (j a) := by
  intro p hp Ωl _ _ hclo Ω _ _ j k e he ⟨P, hP0, hP⟩
  have : CharZero Ωl := Basic.charZero_of_isClo hclo
  have hpne : (p : Ωl) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hvaluation : ∃ v : Valuation Ωl ℝ≥0, (∀ x, v x ≤ 1 ↔ IsInt (p := p) x) ∧
      v (p : Ωl) < 1 := by
    obtain ⟨_, hdvr, hirr⟩ := GlobalTheory.T.completed_laurent_isDVR_statement p
    have : IsAdicComplete (IsLocalRing.maximalIdeal (O0 p)) (O0 p) := by
      rw [hirr.maximalIdeal_eq]
      exact GlobalTheory.T.unramified_integers_adic_complete p
    have := hclo.alg
    obtain ⟨v, hv⟩ := GlobalTheory.T.exists_valuation_le_one_iff_isIntegral_of_complete_dvr
      (O0 p) Ωl hclo.inj
    refine ⟨v, hv, lt_of_le_of_ne ((hv _).2 ?_) ?_⟩
    · simpa [IsInt] using Basic.isInt_intCast (p := p) (Ω := Ωl) (p : ℤ)
    · intro h_eq
      have hi : v (p : Ωl)⁻¹ ≤ 1 := by rw [map_inv₀, h_eq, inv_one]
      exact Basic.not_cong_one_zero hclo 1 one_ne_zero
        ⟨(p : Ωl)⁻¹, (hv _).1 hi, by rw [sub_zero, pow_one, mul_inv_cancel₀ hpne]⟩
  obtain ⟨v, hv, hp1⟩ := hvaluation
  set φ : ℤ_[p] →+* Ωl := (algebraMap (O0 p) Ωl).comp (algebraMap ℤ_[p] (O0 p)) with hφ
  have hPe : P.eval₂ φ e = 0 := by rwa [aeval_def, eval₂_map] at hP
  have hφint : ∀ x, v (φ x) ≤ 1 := fun x => (hv _).2 isIntegral_algebraMap
  have hc0 : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hP0
  have hc : φ P.leadingCoeff ≠ 0 := by
    rw [PadicInt.unitCoeff_spec hc0, map_mul, map_pow, map_natCast]
    exact mul_ne_zero ((Units.isUnit _).map φ).ne_zero (pow_ne_zero _ hpne)
  have hvc : 0 < v (φ P.leadingCoeff) := (Valuation.pos_iff v).2 hc
  have hp0 : 0 < v (p : Ωl) := (Valuation.pos_iff v).2 hpne
  obtain ⟨N, hN⟩ := NNReal.exists_pow_lt_of_lt_one
    (mul_pos hvc (pow_pos (pow_pos hp0 k) P.natDegree)) hp1
  have hpk : v (p : Ωl) ^ k ≤ 1 := pow_le_one₀ zero_le hp1.le
  have hN' : v (p : Ωl) ^ N < v (φ P.leadingCoeff) :=
    hN.trans_le (mul_le_of_le_one_right zero_le (pow_le_one₀ zero_le hpk))
  obtain ⟨Q, R, hdeg, hQR⟩ := exists_approx P N
  have hsmall : ∀ y : Ωl, v y ≤ 1 → v ((p : Ωl) ^ N * y) ≤ v (p : Ωl) ^ N := by
    intro y hy
    rw [map_mul, map_pow]
    exact mul_le_of_le_one_right zero_le hy
  have hco : φ P.leadingCoeff = (Q.coeff P.natDegree : Ωl) + (p : Ωl) ^ N * φ (R.coeff P.natDegree) := by
    have := congrArg (fun (S : ℤ_[p][X]) => φ (S.coeff P.natDegree)) hQR
    simp only [coeff_add, coeff_C_mul, coeff_map, map_add (f := _), map_mul, eq_intCast, map_intCast] at this
    rw [map_pow, map_natCast] at this
    exact this
  have hvQ : v (Q.coeff P.natDegree : Ωl) = v (φ P.leadingCoeff) := by
    rw [eq_sub_of_add_eq hco.symm]
    exact Valuation.map_sub_eq_of_lt_left v ((hsmall _ (hφint _)).trans_lt hN')
  have hQ0 : Q.coeff P.natDegree ≠ 0 := by
    intro h0
    rw [h0, Int.cast_zero, map_zero] at hvQ
    exact hvc.ne hvQ
  have hdeg' : Q.natDegree = P.natDegree := natDegree_eq_of_le_of_coeff_ne_zero hdeg hQ0
  have hRe : v (R.eval₂ φ e) ≤ 1 := by
    rw [eval₂_eq_sum_range]
    refine Valuation.map_sum_le v fun i _ => ?_
    rw [map_mul, map_pow]
    exact (mul_le_of_le_one_right zero_le (pow_le_one₀ zero_le ((hv _).2 he))).trans (hφint _)
  have hQe : Q.eval₂ (Int.castRingHom Ωl) e = -((p : Ωl) ^ N * R.eval₂ φ e) := by
    rw [hQR, eval₂_add, eval₂_mul, eval₂_C, eval₂_map, map_pow, map_natCast,
      RingHom.ext_int (φ.comp _) (Int.castRingHom Ωl)] at hPe
    exact eq_neg_of_add_eq_zero_left hPe
  obtain ⟨a, ha⟩ := exists_near_root v j e (v (p : Ωl) ^ k) Q (by
    rw [hQe, Valuation.map_neg, leadingCoeff, hdeg', hvQ]
    exact (hsmall _ hRe).trans_lt hN)
  refine ⟨a, (hv _).1 ?_, (e - j a) / (p : Ωl) ^ k, (hv _).1 ?_, ?_⟩
  · rw [show j a = e - (e - j a) by ring]
    exact Valuation.map_sub_le v ((hv _).2 he) (ha.le.trans hpk)
  · rw [map_div₀, map_pow]
    exact div_le_one_of_le₀ ha.le zero_le
  · field_simp

end GlobalTheory.K5.Dense
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLevelMulPowOfInvariantModPow
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLevelMulPowOfInvariantModPow
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.KZ.ES.CongruenceDescent

theorem mem_Gamma_iff_exists {N : ℕ} {γ : SL(2, ℤ)} :
    γ ∈ CongruenceSubgroup.Gamma N ↔ ∃ B : Matrix (Fin 2) (Fin 2) ℤ, (γ : Matrix (Fin 2) (Fin 2) ℤ) = 1 + (N : ℤ) • B := by
  rw [CongruenceSubgroup.Gamma_mem]
  constructor
  · rintro ⟨h00, h01, h10, h11⟩
    have d00 : (N : ℤ) ∣ γ 0 0 - 1 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [h00]; ring
    have d01 : (N : ℤ) ∣ γ 0 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h01
    have d10 : (N : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h10
    have d11 : (N : ℤ) ∣ γ 1 1 - 1 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [h11]; ring
    obtain ⟨a, ha⟩ := d00; obtain ⟨b, hb⟩ := d01; obtain ⟨c, hc⟩ := d10; obtain ⟨d, hd⟩ := d11
    refine ⟨!![a, b; c, d], ?_⟩
    ext i j; fin_cases i <;> fin_cases j <;> simp <;> linarith
  · rintro ⟨B, hB⟩
    have e : ∀ i j, γ i j = (1 : Matrix (Fin 2) (Fin 2) ℤ) i j + N * B i j := fun i j => by
      rw [show γ i j = (γ : Matrix (Fin 2) (Fin 2) ℤ) i j from rfl, hB, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [e] <;> simp

theorem Gamma_le_of_dvd {N M : ℕ} (h : N ∣ M) : CongruenceSubgroup.Gamma M ≤ CongruenceSubgroup.Gamma N := by
  intro γ hγ
  obtain ⟨B, hB⟩ := mem_Gamma_iff_exists.1 hγ
  obtain ⟨c, rfl⟩ := h
  exact mem_Gamma_iff_exists.2 ⟨(c : ℤ) • B, by rw [hB, smul_smul]; push_cast; ring_nf⟩

theorem pow_mem_Gamma_mul {L q : ℕ} (hq : q ∣ L) {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma L) :
    γ ^ q ∈ CongruenceSubgroup.Gamma (L * q) := by
  obtain ⟨B, hB⟩ := mem_Gamma_iff_exists.1 hγ
  have key : ∀ m : ℕ, ∃ Y : Matrix (Fin 2) (Fin 2) ℤ,
      (γ : Matrix (Fin 2) (Fin 2) ℤ) ^ m = 1 + ((m : ℤ) * L) • B + ((L : ℤ) * L) • (B * B * Y) := by
    intro m
    induction m with
    | zero => exact ⟨0, by simp⟩
    | succ m ih =>
      obtain ⟨Y, hY⟩ := ih
      refine ⟨(m : ℤ) • 1 + Y + Y * ((L : ℤ) • B), ?_⟩
      rw [pow_succ, hY, hB]
      simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, mul_one, one_mul, smul_add, smul_smul, Matrix.mul_assoc]
      push_cast
      module
  obtain ⟨Y, hY⟩ := key q
  obtain ⟨c, rfl⟩ := hq
  refine mem_Gamma_iff_exists.2 ⟨B + (c : ℤ) • (B * B * Y), ?_⟩
  rw [Matrix.SpecialLinearGroup.coe_pow, hY, smul_add, smul_smul]
  push_cast
  module

theorem pow_pow_mem_Gamma_mul {L q : ℕ} (hq : q ∣ L) {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma L) (j : ℕ) :
    γ ^ (q ^ j) ∈ CongruenceSubgroup.Gamma (L * q ^ j) := by
  induction j with
  | zero => simpa only [pow_zero, pow_one, mul_one] using hγ
  | succ j ih =>
    rw [pow_succ, pow_mul, ← mul_assoc]
    exact pow_mem_Gamma_mul (hq.mul_right _) ih

theorem coprime_card_of_pow_eq_one {Q : Type} [Group Q] [Finite Q] {l m : ℕ} (hl : l.Prime) (hm : l.Coprime m)
    (h : ∀ x : Q, x ^ m = 1) : l.Coprime (Nat.card Q) := by
  rw [hl.coprime_iff_not_dvd]
  intro hd
  haveI := Fact.mk hl
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' l hd
  have := orderOf_dvd_of_pow_eq_one (h x)
  rw [hx] at this
  exact (hl.coprime_iff_not_dvd.1 hm) this

theorem exists_invariant {H A : Type} [Group H] [CommGroup A] (s : H → A →* A)
    (hs : ∀ g h a, s (g * h) a = s h (s g a)) (D : Subgroup H) [D.Normal] [Finite (H ⧸ D)] {m : ℕ}
    (hm : m.Coprime (Nat.card (H ⧸ D))) (f : A) (hD : ∀ δ ∈ D, s δ f = f) (hf : ∀ γ, ∃ g : A, s γ f = f * g ^ m) :
    ∃ h : A, ∀ γ, s γ (f * h ^ m) = f * h ^ m := by
  classical
  haveI := Fintype.ofFinite (H ⧸ D)
  choose g hg using hf
  have hwd : ∀ a b : H, (a : H ⧸ D) = b → s a f = s b f := by
    intro a b hab
    have h1 : a * (a⁻¹ * b) * a⁻¹ ∈ D :=
      Subgroup.Normal.conj_mem (a⁻¹ * b) (QuotientGroup.eq.1 hab) a
    have h2 : b = (a * (a⁻¹ * b) * a⁻¹) * a := by group
    conv_rhs => rw [h2, hs, hD _ h1]
  set F : A := ∏ x : H ⧸ D, s x.out f with hF
  have hinv : ∀ γ, s γ F = F := by
    intro γ
    rw [hF, map_prod]
    refine Fintype.prod_equiv (Equiv.mulRight (γ : H ⧸ D)) _ _ fun x => ?_
    rw [← hs]
    apply hwd
    simp
  have hFeq : F = f ^ Nat.card (H ⧸ D) * (∏ x : H ⧸ D, g x.out) ^ m := by
    rw [hF]
    simp only [hg, Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_const, Finset.card_univ,
      Nat.card_eq_fintype_card]
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hm
  refine ⟨f ^ (-u) * (∏ x : H ⧸ D, g x.out) ^ v, fun γ => ?_⟩
  have e : f * (f ^ (-u) * (∏ x : H ⧸ D, g x.out) ^ v) ^ m = F ^ v := by
    have e1 : f * f ^ (-u * (m : ℤ)) = f ^ ((Nat.card (H ⧸ D) : ℤ) * v) := by
      rw [← _root_.zpow_one_add]
      congr 1
      linear_combination -huv
    rw [hFeq, mul_pow, _root_.mul_zpow, ← _root_.zpow_natCast, ← _root_.zpow_natCast, ← _root_.zpow_natCast,
      ← _root_.zpow_natCast]
    simp only [← _root_.zpow_mul]
    rw [← mul_assoc, e1, mul_comm v]
  rw [e, map_zpow, hinv]

end GlobalTheory.KZ.ES.CongruenceDescent

namespace GlobalTheory.KZ.ES

open CongruenceDescent CongruenceSubgroup in
theorem exists_lev_mul_pow_of_invariant_mod_pow :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), ∀ (l n M e : ℕ), l.Prime → 0 < M → ∀ f : X.Kˣ, Lev X (M ^ e) f → (∀ γ ∈ CongruenceSubgroup.Gamma M, ∃ g : X.Kˣ, X.sl (ofSL γ) (f : X.K) = f * (g : X.K) ^ (l ^ n)) → ∃ (k : ℕ) (h : X.Kˣ), Lev X (M * l ^ k) ((f : X.K) * (h : X.K) ^ (l ^ n)) := by
  intro Ω _ _ _ ε X l n M e hl hM f hlev hf
  obtain ⟨a, q, hq, hMq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hM.ne' l hl.ne_one
  have hlq : l.Coprime q := hl.coprime_iff_not_dvd.2 hq
  let H : Subgroup SL(2, ℤ) := CongruenceSubgroup.Gamma (M * l ^ (a * e))
  haveI := CongruenceSubgroup.Gamma_normal (M ^ e)
  haveI : NeZero (M ^ e) := ⟨(pow_pos hM e).ne'⟩
  let D : Subgroup H := (CongruenceSubgroup.Gamma (M ^ e)).subgroupOf H
  haveI : D.FiniteIndex := inferInstance
  have hcard : l.Coprime (Nat.card (H ⧸ D)) := by
    refine CongruenceDescent.coprime_card_of_pow_eq_one hl (hlq.pow_right e) fun x => ?_
    obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective x
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.coe_pow]
    refine CongruenceDescent.Gamma_le_of_dvd ?_ (CongruenceDescent.pow_pow_mem_Gamma_mul (q := q) ?_ γ.2 e)
    · exact ⟨M, by rw [hMq]; ring⟩
    · exact ⟨l ^ a * l ^ (a * e), by rw [hMq]; ring⟩
  obtain ⟨h, hh⟩ := CongruenceDescent.exists_invariant (H := H) (A := X.Kˣ)
    (fun γ => Units.map (X.sl (ofSL γ) : X.K →* X.K))
    (fun g h a => Units.ext (by simp [X.sl_mul])) D (hcard.pow_left n) f
    (fun δ hδ => Units.ext (by simpa using hlev δ hδ))
    (fun γ => by
      obtain ⟨g, hg⟩ := hf γ (CongruenceDescent.Gamma_le_of_dvd (dvd_mul_right _ _) γ.2)
      exact ⟨g, Units.ext (by simpa using hg)⟩)
  refine ⟨a * e, h, fun γ hγ => ?_⟩
  have := congrArg Units.val (hh ⟨γ, hγ⟩)
  simpa using this

end GlobalTheory.KZ.ES
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLevelMulPowOfInvariantModPowStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_level_mul_pow_of_invariant_mod_pow : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), ∀ (l n M e : ℕ), l.Prime → 0 < M → ∀ f : X.Kˣ, Lev X (M ^ e) f → (∀ γ ∈ CongruenceSubgroup.Gamma M, ∃ g : X.Kˣ, X.sl (ofSL γ) (f : X.K) = f * (g : X.K) ^ (l ^ n)) → ∃ (k : ℕ) (h : X.Kˣ), Lev X (M * l ^ k) ((f : X.K) * (h : X.K) ^ (l ^ n)) := by
  first | exact @GlobalTheory.KZ.ES.exists_lev_mul_pow_of_invariant_mod_pow | exact GlobalTheory.KZ.ES.exists_lev_mul_pow_of_invariant_mod_pow | (intros; apply GlobalTheory.KZ.ES.exists_lev_mul_pow_of_invariant_mod_pow <;> assumption)
end
end
