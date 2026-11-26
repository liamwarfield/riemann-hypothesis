module

public import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
public import Development.AbelianVarietyTheory.Definitions.Foundations.FrobLiftWittClosure
public import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HsCodiscreteNeBot
noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix

namespace GlobalTheory.KZ.BettiB

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def BtN (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime] (n : ℕ) (b : X.Fn l)
    (c : Gam N l → MvPolynomial (Fin 2) (ZMod (l ^ n))) : Prop :=
  ∀ u : Fin 2 → ℤ_[l], ∃ χ : SL(2, ℤ) → ZMod (l ^ n), H3.Kum X l n (b u) χ ∧ ∃ M : ℕ, 0 < M ∧
    ∀ δ : Gam N l, (δ : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma M →
      MvPolynomial.eval (fun i => PadicInt.toZModPow n (u i)) (c δ) = χ δ

def BtZ (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime] (b : X.Fn l) (c : Gam N l → MvPolynomial (Fin 2) ℤ_[l]) : Prop :=
  ∀ n : ℕ, BtN X N l n b (fun δ => MvPolynomial.map (PadicInt.toZModPow n) (c δ))

def Z1 (N l w : ℕ) [Fact l.Prime] : Submodule ℤ_[l] (Gam N l → MvPolynomial (Fin 2) ℤ_[l]) where
  carrier := {c | (∀ γ, (c γ).IsHomogeneous w) ∧
    ∀ γ δ : Gam N l, c (γ * δ) = slP ((δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (c γ) + c δ}
  add_mem' := by
    rintro c c' ⟨h1, h2⟩ ⟨h1', h2'⟩
    refine ⟨fun γ => (h1 γ).add (h1' γ), fun γ δ => ?_⟩
    simp only [Pi.add_apply, h2, h2', map_add (f := _)]; abel
  zero_mem' := ⟨fun γ => MvPolynomial.isHomogeneous_zero _ _ _, fun γ δ => by simp⟩
  smul_mem' := by
    rintro r c ⟨h1, h2⟩
    refine ⟨fun γ => ?_, fun γ δ => ?_⟩
    · simpa [MvPolynomial.smul_eq_C_mul] using (MvPolynomial.isHomogeneous_C _ r).mul (h1 γ)
    · simp only [Pi.smul_apply, h2, map_smul, smul_add]

theorem hs_codiscrete_neBot : (Filter.codiscreteWithin Hs).NeBot := by
  rw [Filter.neBot_iff]
  intro h
  have hmem : (∅ : Set ℂ) ∈ Filter.codiscreteWithin Hs := by rw [h]; exact Filter.mem_bot
  rw [mem_codiscreteWithin] at hmem
  have hI : Complex.I ∈ Hs := by simp [Hs]
  have hd := hmem Complex.I hI
  simp only [Set.diff_empty] at hd
  have hopen : IsOpen Hs := isOpen_lt continuous_const Complex.continuous_im
  have hle : nhdsWithin Complex.I {Complex.I}ᶜ ≤ Filter.principal Hs :=
    le_trans nhdsWithin_le_nhds (Filter.le_principal_iff.2 (hopen.mem_nhds hI))
  have hbot : nhdsWithin Complex.I {Complex.I}ᶜ = ⊥ := by
    have := hd.mono_right hle
    exact disjoint_self.1 this
  exact (NormedField.nhdsNE_neBot Complex.I).ne hbot

theorem btZ_zero (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime] : BtZ X N l 0 0 := by
  intro n u
  refine ⟨0, ⟨1, fun _ => 1, fun _ => 1, 1, one_pos, ?_, ?_, ?_⟩, 1, one_pos, fun δ _ => by simp⟩
  · simp [Tower.cls]
  · apply H3.isRoot_one
    haveI := hs_codiscrete_neBot
    exact one_ne_zero
  · intro δ _ z _; simp

end GlobalTheory.KZ.BettiB
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinsetPrimesMemValuationSubringOver
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinsetPrimesMemValuationSubringOver
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory

theorem isIntegral_int_mem_every_valuationSubring {F : Type} [Field F] (V : ValuationSubring F)
    {y : F} (hy : IsIntegral ℤ y) : y ∈ V := by
  have hV : IsIntegral V y := hy.tower_top
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hV
  rw [← hz]
  exact z.2

theorem valuationSubring_valuation_intCast_coprime_eq_one {F : Type} [Field F] (V : ValuationSubring F)
    {q : ℕ} (hq : ((q : ℕ) : F) ∈ V.nonunits) {n : ℤ} (hn : IsCoprime n (q : ℤ)) :
    V.valuation (n : F) = 1 := by
  obtain ⟨a, b, hab⟩ := hn
  have hint : ∀ m : ℤ, V.valuation (m : F) ≤ 1 := fun m =>
    (V.valuation_le_one_iff _).2 (by simp)
  have hq' : V.valuation ((q : ℕ) : F) < 1 := V.mem_nonunits_iff.1 hq
  refine le_antisymm (hint n) (not_lt.1 fun hlt => ?_)
  have hsum : ((a : F) * n + (b : F) * ((q : ℕ) : F)) = 1 := by
    have := congrArg (fun t : ℤ => (t : F)) hab
    simpa using this
  have h1 : V.valuation ((a : F) * n) < 1 := by
    rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint a)) hlt
  have h2 : V.valuation ((b : F) * ((q : ℕ) : F)) < 1 := by
    rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint b)) hq'
  have h3 := Valuation.map_add_lt _ h1 h2
  rw [hsum, map_one] at h3
  exact lt_irrefl _ h3

theorem exists_finset_primes_forall_mem_valuationSubring :
    ∀ {F : Type} [Field F] [CharZero F] [Algebra.IsAlgebraic ℚ F] (s : Finset F),
      ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ V : ValuationSubring F,
        ((q : ℕ) : F) ∈ V.nonunits → ∀ x ∈ s, x ∈ V := by
  intro F _ _ _ s
  have : Algebra.IsAlgebraic ℤ F :=
    ⟨fun x => (IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic x)⟩
  obtain ⟨d, hd0, hd⟩ := Algebra.IsAlgebraic.exists_integral_multiples ℤ s
  refine ⟨d.natAbs.primeFactors, fun q hq hqS V hqV x hx => ?_⟩
  have hndvd : ¬ q ∣ d.natAbs := fun h =>
    hqS (Nat.mem_primeFactors.2 ⟨hq, h, Int.natAbs_ne_zero.2 hd0⟩)
  have hcop : IsCoprime d (q : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have := (Nat.Prime.coprime_iff_not_dvd hq).2 hndvd
    simpa [Int.gcd, Nat.Coprime, Nat.gcd_comm] using this
  have hdx : (d : F) * x ∈ V := by
    have := isIntegral_int_mem_every_valuationSubring V (hd x hx)
    simpa [zsmul_eq_mul] using this
  have hv1 := valuationSubring_valuation_intCast_coprime_eq_one V hqV hcop
  rw [← V.valuation_le_one_iff]
  have := (V.valuation_le_one_iff _).2 hdx
  rwa [map_mul, hv1, one_mul] at this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinsetPrimesMemValuationSubringOverStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_primes_mem_valuationSubring_over : ∀ {F : Type} [Field F] [CharZero F] [Algebra.IsAlgebraic ℚ F] (s : Finset F), ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ V : ValuationSubring F, ((q : ℕ) : F) ∈ V.nonunits → ∀ x ∈ s, x ∈ V := by
  first | exact @GlobalTheory.exists_finset_primes_forall_mem_valuationSubring | exact GlobalTheory.exists_finset_primes_forall_mem_valuationSubring | (intros; apply GlobalTheory.exists_finset_primes_forall_mem_valuationSubring <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBasisOneAddXPow
noncomputable section
open GlobalTheory.Col PowerSeries

namespace GlobalTheory.Col

private theorem one_add_X_pow_eq_sum_fin_choose {R : Type} [CommRing R] (p j : ℕ) (hj : j < p) :
    (1 + X : R⟦X⟧) ^ j = ∑ i : Fin p, ((j.choose i : ℕ) : R⟦X⟧) * X ^ (i : ℕ) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => ((j.choose i : ℕ) : R⟦X⟧) * X ^ i) p, add_comm, add_pow]
  have hsub : Finset.range (j + 1) ⊆ Finset.range p := Finset.range_subset_range.2 (by omega)
  rw [← Finset.sum_subset hsub (fun i _ hi => by
    rw [Finset.mem_range, not_lt] at hi
    rw [Nat.choose_eq_zero_of_lt (by omega)]; simp)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [one_pow, mul_one, mul_comm]

private theorem subsingleton_of_isUnit_natCast_of_isAdicComplete {R : Type} [CommRing R] (p : ℕ)
    (hR : IsAdicComplete (Ideal.span {(p : R)}) R) (hu : IsUnit (p : R)) : Subsingleton R := by
  have htop : Ideal.span {(p : R)} = ⊤ := Ideal.span_singleton_eq_top.2 hu
  constructor
  intro a b
  have h := hR.toIsHausdorff.haus (a - b) (fun n => by
    rw [htop, Ideal.top_pow, Submodule.top_smul]; exact SModEq.top)
  exact sub_eq_zero.1 h

theorem _root_.GlobalTheory.Col.exists_basis_one_add_X_pow (R : Type) [CommRing R] (p : ℕ) [hp : Fact p.Prime]
    (hR : IsAdicComplete (Ideal.span {(p : R)}) R) :
    ∃ b : @Module.Basis (Fin p) (PowerSeries R) (PowerSeries R) _ _
      (@Algebra.toModule _ _ _ _ (_root_.GlobalTheory.Col.phi (R := R) p hp.out.pos).toRingHom.toAlgebra), ∀ i, b i = (1 + X) ^ (i : ℕ) := by
  by_cases hn : (p : R) ∈ nonunits R
  · haveI := hR
    set e := _root_.GlobalTheory.Col.Model.basis (R := R) p hn
    have he : ∀ i, e i = _root_.GlobalTheory.Col.Model.toUp p (X ^ (i : ℕ)) := fun i => by
      show (_root_.GlobalTheory.Col.Model.basis (R := R) p hn) i = _
      unfold _root_.GlobalTheory.Col.Model.basis
      rw [Module.Basis.mk_apply]
      rfl
    let v : Fin p → _root_.GlobalTheory.Col.Model.Up R p :=
      fun j => _root_.GlobalTheory.Col.Model.toUp p ((1 + X) ^ (j : ℕ))
    have hv : ∀ j : Fin p, v j = ∑ i : Fin p, (((j : ℕ).choose i : ℕ) : R⟦X⟧) • e i := by
      intro j
      simp only [he, Algebra.smul_def, map_natCast]
      exact one_add_X_pow_eq_sum_fin_choose p j j.2
    have hrepr : ∀ j i : Fin p, e.repr (v j) i = (((j : ℕ).choose i : ℕ) : R⟦X⟧) := by
      intro j i
      rw [hv, e.repr_sum_self]
    have hdet : e.det v = 1 := by
      rw [Module.Basis.det_apply, Matrix.det_of_upperTriangular]
      · simp [Module.Basis.toMatrix_apply, hrepr]
      · intro i j hij
        simp [Module.Basis.toMatrix_apply, hrepr, Nat.choose_eq_zero_of_lt (show (j : ℕ) < i from hij)]
    obtain ⟨hli, hspan⟩ := (Module.Basis.is_basis_iff_det e).2 (by rw [hdet]; exact isUnit_one)
    let b : Module.Basis (Fin p) R⟦X⟧ (_root_.GlobalTheory.Col.Model.Up R p) := Module.Basis.mk hli hspan.ge
    have hb : ∀ i, b i = v i := fun i => Module.Basis.mk_apply hli hspan.ge i
    exact ⟨b, hb⟩
  · have hu : IsUnit (p : R) := by simpa [mem_nonunits_iff] using hn
    haveI := subsingleton_of_isUnit_natCast_of_isAdicComplete p hR hu
    haveI : Subsingleton R⟦X⟧ := ⟨fun a b => PowerSeries.ext fun n => Subsingleton.elim _ _⟩
    haveI : Subsingleton (_root_.GlobalTheory.Col.Model.Up R p) := ‹Subsingleton R⟦X⟧›
    haveI : Subsingleton (Fin p →₀ R⟦X⟧) := ⟨fun a b => Finsupp.ext fun i => Subsingleton.elim _ _⟩
    let b : Module.Basis (Fin p) R⟦X⟧ (_root_.GlobalTheory.Col.Model.Up R p) :=
      Module.Basis.ofRepr (LinearEquiv.ofSubsingleton _ _)
    have hb : ∀ i, b i = _root_.GlobalTheory.Col.Model.toUp p ((1 + X) ^ (i : ℕ)) := fun i => Subsingleton.elim _ _
    exact ⟨b, hb⟩

end GlobalTheory.Col
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntMatrixPrimeDetCosetRepresentatives
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntMatrixPrimeDetCosetRepresentatives
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory

theorem exists_right_div_upperTriangular_prime_det (q : ℕ) (m : Matrix (Fin 2) (Fin 2) ℤ) (k : ℕ)
    (h1 : (q : ℤ) ∣ m 0 1 - m 0 0 * k) (h2 : (q : ℤ) ∣ m 1 1 - m 1 0 * k) :
    ∃ g : Matrix (Fin 2) (Fin 2) ℤ, g * !![1, (k : ℤ); 0, (q : ℤ)] = m := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨c, hc⟩ := h2
  refine ⟨!![m 0 0, a; m 1 0, c], ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | linear_combination -ha | linear_combination ha | linear_combination -hc

theorem cosetPrimeDet : ∀ (q : ℕ), q.Prime → ∀ m : Matrix (Fin 2) (Fin 2) ℤ, m.det = q →
    (∃ g : Matrix (Fin 2) (Fin 2) ℤ, g * !![(q : ℤ), 0; 0, 1] = m) ∨
    ∃ k : ℕ, k < q ∧ ∃ g : Matrix (Fin 2) (Fin 2) ℤ, g * !![1, (k : ℤ); 0, (q : ℤ)] = m := by
  intro q hq m hdet
  have := Fact.mk hq
  have : NeZero q := ⟨hq.ne_zero⟩
  rw [Matrix.det_fin_two] at hdet
  have hd : ((m 0 0 : ℤ) : ZMod q) * (m 1 1 : ℤ) - ((m 0 1 : ℤ) : ZMod q) * (m 1 0 : ℤ) = 0 := by
    have : ((m 0 0 * m 1 1 - m 0 1 * m 1 0 : ℤ) : ZMod q) = 0 := by
      rw [hdet]; simp
    push_cast at this
    exact this

  have dv : ∀ x : ℤ, (x : ZMod q) = 0 → (q : ℤ) ∣ x := fun x hx =>
    (ZMod.intCast_zmod_eq_zero_iff_dvd x q).mp hx

  have fin : ∀ t : ZMod q, ((m 0 1 : ℤ) : ZMod q) - (m 0 0 : ℤ) * t = 0 →
      ((m 1 1 : ℤ) : ZMod q) - (m 1 0 : ℤ) * t = 0 →
      ∃ k : ℕ, k < q ∧ ∃ g : Matrix (Fin 2) (Fin 2) ℤ, g * !![1, (k : ℤ); 0, (q : ℤ)] = m := by
    intro t ht1 ht2
    refine ⟨t.val, ZMod.val_lt t, exists_right_div_upperTriangular_prime_det q m t.val (dv _ ?_) (dv _ ?_)⟩
    · push_cast; rw [ZMod.natCast_zmod_val]; exact ht1
    · push_cast; rw [ZMod.natCast_zmod_val]; exact ht2
  by_cases ha : ((m 0 0 : ℤ) : ZMod q) = 0
  · by_cases hc : ((m 1 0 : ℤ) : ZMod q) = 0
    ·
      left
      obtain ⟨x, hx⟩ := dv _ ha
      obtain ⟨y, hy⟩ := dv _ hc
      refine ⟨!![x, m 0 1; y, m 1 1], ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
        first | linear_combination -hx | linear_combination hx | linear_combination -hy
    · right
      have h01 : ((m 0 1 : ℤ) : ZMod q) = 0 := by
        have : ((m 0 1 : ℤ) : ZMod q) * (m 1 0 : ℤ) = 0 := by
          linear_combination -hd + ((m 1 1 : ℤ) : ZMod q) * ha
        exact (mul_eq_zero.mp this).resolve_right hc
      have hinv := mul_inv_cancel₀ hc
      refine fin (((m 1 1 : ℤ) : ZMod q) * ((m 1 0 : ℤ) : ZMod q)⁻¹) ?_ ?_
      · rw [ha, h01]; ring
      · linear_combination -((m 1 1 : ℤ) : ZMod q) * hinv
  · right
    have hinv := mul_inv_cancel₀ ha
    refine fin (((m 0 1 : ℤ) : ZMod q) * ((m 0 0 : ℤ) : ZMod q)⁻¹) ?_ ?_
    · linear_combination -((m 0 1 : ℤ) : ZMod q) * hinv
    · linear_combination ((m 0 0 : ℤ) : ZMod q)⁻¹ * hd - ((m 1 1 : ℤ) : ZMod q) * hinv

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntMatrixPrimeDetCosetRepresentativesStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intMatrix_prime_det_coset_representatives : ∀ (q : ℕ), q.Prime → ∀ m : Matrix (Fin 2) (Fin 2) ℤ, m.det = q → (∃ g : Matrix (Fin 2) (Fin 2) ℤ, g * !![(q : ℤ), 0; 0, 1] = m) ∨ ∃ k : ℕ, k < q ∧ ∃ g : Matrix (Fin 2) (Fin 2) ℤ, g * !![1, (k : ℤ); 0, (q : ℤ)] = m := by
  first | exact @GlobalTheory.cosetPrimeDet | exact GlobalTheory.cosetPrimeDet | (intros; apply GlobalTheory.cosetPrimeDet <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TraceCompLeftFunLeft
open Polynomial Classical GlobalTheory.BadShare

noncomputable section
namespace GlobalTheory.BadShare

theorem trace_compLeft_funLeft {G W : Type} [Fintype G] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (A : W →ₗ[ℂ] W) (f : G → G) :
    LinearMap.trace ℂ (G → W) (A.compLeft G ∘ₗ LinearMap.funLeft ℂ W f) =
      ∑ x, if f x = x then LinearMap.trace ℂ W A else 0 := by
  have h : A.compLeft G ∘ₗ LinearMap.funLeft ℂ W f =
      ∑ x, LinearMap.single ℂ (fun _ : G => W) x ∘ₗ (A ∘ₗ LinearMap.proj (f x)) := by
    refine LinearMap.ext fun φ => funext fun y => ?_
    simp [LinearMap.sum_apply, Finset.sum_apply, Pi.single_apply, LinearMap.funLeft_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [LinearMap.trace_comp_comm']
  split_ifs with hx
  · congr 1
    ext w
    simp [hx]
  · have : (A ∘ₗ LinearMap.proj (f x)) ∘ₗ LinearMap.single ℂ (fun _ : G => W) x = 0 := by
      ext w
      simp [hx]
    rw [this, map_zero]

section
variable {G : Type} [Group G] [Fintype G] {Γ : Type} [Group Γ] [Fintype Γ] (r : Γ →* G)
  {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (σ : Representation ℂ Γ W)

def coindSum : (G → W) →ₗ[ℂ] Representation.coindV r σ :=
  LinearMap.codRestrict _
    (∑ γ : Γ, (σ γ⁻¹ : W →ₗ[ℂ] W).compLeft G ∘ₗ LinearMap.funLeft ℂ W fun x => r γ * x) (by
      intro φ δ x
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [LinearMap.sum_apply, Finset.sum_apply, LinearMap.comp_apply, LinearMap.compLeft_apply,
        Function.comp_apply, LinearMap.funLeft_apply, map_sum]
      refine Fintype.sum_equiv (Equiv.mulRight δ) _ _ fun γ => ?_
      simp only [Equiv.coe_mulRight, map_mul r, mul_assoc, mul_inv_rev]
      rw [← Module.End.mul_apply, ← map_mul σ, mul_inv_cancel_left])

omit [Fintype G] [FiniteDimensional ℂ W] in
theorem coindSum_apply (φ : G → W) (x : G) :
    (coindSum r σ φ).1 x = ∑ γ : Γ, σ γ⁻¹ (φ (r γ * x)) := by
  change (∑ γ : Γ, (σ γ⁻¹ : W →ₗ[ℂ] W).compLeft G ∘ₗ LinearMap.funLeft ℂ W fun x => r γ * x) φ x = _
  simp [LinearMap.sum_apply, Finset.sum_apply, LinearMap.funLeft_apply]

theorem trace_coind_mul_card (g : G) :
    LinearMap.trace ℂ _ (Representation.coind r σ g) * (Fintype.card Γ : ℂ) =
      ∑ γ : Γ, ∑ x : G, if r γ * (x * g) = x then LinearMap.trace ℂ W (σ γ⁻¹) else 0 := by
  have h1 : (Fintype.card Γ : ℂ) • (Representation.coind r σ g : _ →ₗ[ℂ] _) =
      coindSum r σ ∘ₗ (LinearMap.funLeft ℂ W (fun x => x * g) ∘ₗ (Representation.coindV r σ).subtype) := by
    refine LinearMap.ext fun φ => Subtype.ext (funext fun x => ?_)
    rw [LinearMap.comp_apply, coindSum_apply]
    have : ∀ γ : Γ, σ γ⁻¹ ((LinearMap.funLeft ℂ W (fun x => x * g) ∘ₗ (Representation.coindV r σ).subtype) φ (r γ * x))
        = φ.1 (x * g) := by
      intro γ
      change σ γ⁻¹ (φ.1 (r γ * x * g)) = _
      rw [mul_assoc, φ.2 γ, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [Finset.sum_congr rfl fun γ _ => this γ, Finset.sum_const, Finset.card_univ]
    change (Fintype.card Γ : ℂ) • φ.1 (x * g) = _
    rw [Nat.cast_smul_eq_nsmul]
  have h2 : (LinearMap.funLeft ℂ W (fun x => x * g) ∘ₗ (Representation.coindV r σ).subtype) ∘ₗ coindSum r σ =
      ∑ γ : Γ, (σ γ⁻¹ : W →ₗ[ℂ] W).compLeft G ∘ₗ LinearMap.funLeft ℂ W fun x => r γ * (x * g) := by
    refine LinearMap.ext fun φ => funext fun x => ?_
    change (coindSum r σ φ).1 (x * g) = _
    rw [coindSum_apply]
    simp [LinearMap.sum_apply, Finset.sum_apply, LinearMap.funLeft_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [mul_comm, ← smul_eq_mul, ← map_smul, h1, LinearMap.trace_comp_comm', h2, map_sum]
  exact Finset.sum_congr rfl fun γ _ => trace_compLeft_funLeft _ _

end

end GlobalTheory.BadShare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerFunctionSlTwoIntInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerFunctionSlTwoIntInvariant
open scoped MatrixGroups
open GlobalTheory.KZ

noncomputable section

namespace GlobalTheory.KZ.InvFun

open Filter Topology

theorem mob_ofSL_den_ne_zero (γ : SL(2, ℤ)) {z : ℂ} (hz : z ∈ Hs) :
    (ent (ofSL γ) 1 0 : ℂ) * z + (ent (ofSL γ) 1 1 : ℂ) ≠ 0 := by
  have hz' : 0 < z.im := hz
  have e10 : (ent (ofSL γ) 1 0 : ℂ) = ((γ 1 0 : ℤ) : ℂ) := by simp [ent, ofSL]
  have e11 : (ent (ofSL γ) 1 1 : ℂ) = ((γ 1 1 : ℤ) : ℂ) := by simp [ent, ofSL]
  rw [e10, e11]
  intro h0
  have him := congrArg Complex.im h0
  simp at him
  rcases him with hc | hc
  · have hre := congrArg Complex.re h0
    simp [hc] at hre
    have hdet := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at hdet
    rw [hc, hre] at hdet
    simp at hdet
  · exact absurd hc hz'.ne'

theorem continuousAt_mob_ofSL (γ : SL(2, ℤ)) {z : ℂ} (hz : z ∈ Hs) : ContinuousAt (mob (ofSL γ)) z := by
  unfold mob
  exact ((continuous_const.mul continuous_id).add continuous_const).continuousAt.div
    ((continuous_const.mul continuous_id).add continuous_const).continuousAt (mob_ofSL_den_ne_zero γ hz)

theorem mob_ofSL_mem (γ : SL(2, ℤ)) {z : ℂ} (hz : z ∈ Hs) : mob (ofSL γ) z ∈ Hs := by
  have := SiegelModel.mob_ofSL γ ⟨z, hz⟩
  show 0 < (mob (ofSL γ) z).im
  have e : ((⟨z, hz⟩ : UpperHalfPlane) : ℂ) = z := rfl
  rw [e] at this
  rw [this]
  exact (γ • (⟨z, hz⟩ : UpperHalfPlane)).im_pos

theorem fun_inv {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (h : X.K) (φ : ℂ → ℂ) :
    ContinuousOn φ Hs → X.an h = (φ : Mero) → (∀ γ : SL(2, ℤ), X.sl (ofSL γ) h = h) →
      ∀ γ : SL(2, ℤ), ∀ z ∈ Hs, φ (mob (ofSL γ) z) = φ z := by
  intro hφ han hinv γ z hz
  have e := X.an_sl (ofSL γ) h φ han
  rw [hinv γ, han, Filter.Germ.coe_eq] at e
  have h1 := (mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 e) z hz
  have h2 : Hs ∈ 𝓝[≠] z := mem_nhdsWithin_of_mem_nhds (SiegelModel.isOpen_Hs.mem_nhds hz)
  have hev : (fun w => φ (mob (ofSL γ) w)) =ᶠ[𝓝[≠] z] φ := by
    filter_upwards [h1, h2] with w hw1 hw2
    rcases hw1 with hw | hw
    · exact hw.symm
    · exact absurd hw2 hw
  have hc1 : ContinuousAt φ z := hφ.continuousAt (SiegelModel.isOpen_Hs.mem_nhds hz)
  have hc2 : ContinuousAt (fun w => φ (mob (ofSL γ) w)) z :=
    ContinuousAt.comp (f := mob (ofSL γ)) (g := φ)
      (hφ.continuousAt (SiegelModel.isOpen_Hs.mem_nhds (mob_ofSL_mem γ hz))) (continuousAt_mob_ofSL γ hz)
  have t1 : Tendsto (fun w => φ (mob (ofSL γ) w)) (𝓝[≠] z) (𝓝 (φ (mob (ofSL γ) z))) :=
    hc2.tendsto.mono_left nhdsWithin_le_nhds
  have t2 : Tendsto (fun w => φ (mob (ofSL γ) w)) (𝓝[≠] z) (𝓝 (φ z)) :=
    (hc1.tendsto.mono_left nhdsWithin_le_nhds).congr' hev.symm
  exact tendsto_nhds_unique t1 t2

end GlobalTheory.KZ.InvFun
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerFunctionSlTwoIntInvariantStatement
open scoped MatrixGroups
open GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modularTower_function_slTwoInt_invariant : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (h : X.K) (φ : ℂ → ℂ), ContinuousOn φ Hs → X.an h = (φ : Mero) → (∀ γ : SL(2, ℤ), X.sl (ofSL γ) h = h) → ∀ γ : SL(2, ℤ), ∀ z ∈ Hs, φ (mob (ofSL γ) z) = φ z := by
  first | exact @GlobalTheory.KZ.InvFun.fun_inv | exact GlobalTheory.KZ.InvFun.fun_inv | (intros; apply GlobalTheory.KZ.InvFun.fun_inv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerPadicCompletionMapEvalDependsOnLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerPadicCompletionMapEvalDependsOnLevel
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ.LevelRed

theorem _root_.GlobalTheory.KZ.LevelRed.gamma_le_of_dvd {M M0 : ℕ} (h : M ∣ M0) :
    CongruenceSubgroup.Gamma M0 ≤ CongruenceSubgroup.Gamma M := by
  intro γ hγ
  rw [CongruenceSubgroup.Gamma_mem] at hγ ⊢
  have key : ∀ z : ℤ, ((z : ZMod M0).cast : ZMod M) = z := ZMod.cast_intCast h
  obtain ⟨h1, h2, h3, h4⟩ := hγ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← key, h1, ZMod.cast_one h]
  · rw [← key, h2, ZMod.cast_zero]
  · rw [← key, h3, ZMod.cast_zero]
  · rw [← key, h4, ZMod.cast_one h]

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

noncomputable abbrev bc (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (φ : X.K ≃+* X.K) : X.Kl l →ₗ[ℤ_[l]] X.Kl l :=
  LinearMap.baseChange ℤ_[l] (AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Units.map φ.toMonoidHom)))

end GlobalTheory.KZ.LevelRed

namespace GlobalTheory.KZ

private lemma exists_level_bc_eq_of_agree_on_level {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}
    (X : _root_.GlobalTheory.KZ.Tower Ω ε) (l : ℕ) [Fact l.Prime] (m : X.Kl l) :
    ∃ M0 : ℕ, 0 < M0 ∧ ∀ φ ψ : X.K ≃+* X.K,
      (∀ f : X.K, (∀ γ ∈ CongruenceSubgroup.Gamma M0,
        X.sl (_root_.GlobalTheory.KZ.ofSL γ) f = f) → φ f = ψ f) →
      _root_.GlobalTheory.KZ.LevelRed.bc X l φ m = _root_.GlobalTheory.KZ.LevelRed.bc X l ψ m := by
  induction m using TensorProduct.induction_on with
  | zero => exact ⟨1, one_pos, fun φ ψ _ => by simp⟩
  | tmul c u =>
    obtain ⟨M, hM, hfix⟩ := X.level ((Additive.toMul u : X.Kˣ) : X.K)
    refine ⟨M, hM, fun φ ψ h => ?_⟩
    have hu : Units.map φ.toMonoidHom (Additive.toMul u) =
        Units.map ψ.toMonoidHom (Additive.toMul u) :=
      Units.ext (by simpa using h _ hfix)
    simp only [LinearMap.baseChange_tmul]
    congr 1
  | add x y hx hy =>
    obtain ⟨M1, hM1, h1⟩ := hx
    obtain ⟨M2, hM2, h2⟩ := hy
    refine ⟨M1 * M2, Nat.mul_pos hM1 hM2, fun φ ψ h => ?_⟩
    rw [map_add (f := _), map_add (f := _),
      h1 φ ψ fun f hf => h f fun γ hγ => hf γ (_root_.GlobalTheory.KZ.LevelRed.gamma_le_of_dvd (dvd_mul_right M1 M2) hγ),
      h2 φ ψ fun f hf => h f fun γ hγ => hf γ (_root_.GlobalTheory.KZ.LevelRed.gamma_le_of_dvd (dvd_mul_left M2 M1) hγ)]

theorem _root_.GlobalTheory.KZ.Tower.eval_kmap_levelRed : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : _root_.GlobalTheory.KZ.Tower Ω ε) (l : ℕ) [Fact l.Prime] (a : X.Khat l) (n : ℕ), ∃ M0 : ℕ, 0 < M0 ∧ ∀ φ ψ : X.K ≃+* X.K, (∀ f : X.K, (∀ γ ∈ CongruenceSubgroup.Gamma M0, X.sl (_root_.GlobalTheory.KZ.ofSL γ) f = f) → φ f = ψ f) → AdicCompletion.eval (_root_.GlobalTheory.KZ.idl l) (X.Kl l) n (X.kmap l φ a) = AdicCompletion.eval (_root_.GlobalTheory.KZ.idl l) (X.Kl l) n (X.kmap l ψ a) := by
  intro Ω _ _ ε X l _ a n
  obtain ⟨m, hm⟩ := Submodule.Quotient.mk_surjective _ (a.1 n)
  obtain ⟨M0, hM0, hlev⟩ := exists_level_bc_eq_of_agree_on_level X l m
  refine ⟨M0, hM0, fun φ ψ h => ?_⟩
  unfold _root_.GlobalTheory.KZ.Tower.kmap
  simp only [LinearMap.coe_restrictScalars, AdicCompletion.map_val_apply,
    AdicCompletion.eval_apply]
  rw [← hm]
  simp only [LinearMap.reduceModIdeal_apply]
  exact congrArg _ (hlev φ ψ h)

end GlobalTheory.KZ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerPadicCompletionMapEvalDependsOnLevelStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.towerPadicCompletionMap_eval_depends_on_level : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (a : X.Khat l) (n : ℕ), ∃ M0 : ℕ, 0 < M0 ∧ ∀ φ ψ : X.K ≃+* X.K, (∀ f : X.K, (∀ γ ∈ CongruenceSubgroup.Gamma M0, X.sl (ofSL γ) f = f) → φ f = ψ f) → AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l φ a) = AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l ψ a) := by
  first | exact @GlobalTheory.KZ.Tower.eval_kmap_levelRed | exact GlobalTheory.KZ.Tower.eval_kmap_levelRed | (intros; apply GlobalTheory.KZ.Tower.eval_kmap_levelRed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeCharacterTriangular
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeCharacterTriangular
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem minor_of_triangular (g : GL (Fin n) k) (m : Fin n)
    (h : (∀ i j : Fin n, i < j → g.val i j = 0) ∨ ∀ i j : Fin n, j < i → g.val i j = 0) :
    minor g m = ∏ i ∈ Finset.univ.filter (fun i => i ≤ m), g.val i i := by
  unfold minor
  have hdet : (g.val.toSquareBlockProp fun i => i ≤ m).det = ∏ i : {i : Fin n // i ≤ m}, g.val i i := by
    rcases h with h | h
    · rw [Matrix.det_of_lowerTriangular]
      · rfl
      · intro i j hij
        exact h i j (OrderDual.toDual_lt_toDual.1 hij)
    · rw [Matrix.det_of_upperTriangular]
      · rfl
      · intro i j hij
        exact h i j hij
  rw [hdet]
  exact (Finset.prod_subtype (Finset.univ.filter (fun i => i ≤ m)) (p := fun i => i ≤ m)
    (fun x => by simp) (fun i => g.val i i)).symm

theorem prod_div_nxt (ψ : Fin n → kˣ →* ℂˣ) (a : Fin n) (u : kˣ) :
    ∏ m ∈ Finset.univ.filter (fun m => a ≤ m), (ψ m / nxt ψ m) u = ψ a u := by
  let f : ℕ → ℂˣ := fun j => if h : j < n then ψ ⟨j, h⟩ u else 1
  have hf : ∀ m : Fin n, f m = ψ m u := fun m => by
    show (if h : (m : ℕ) < n then ψ ⟨m, h⟩ u else 1) = ψ m u
    rw [dite_eq_left m.isLt]
  have hnx : ∀ m : Fin n, nxt ψ m u = f (m + 1) := by
    intro m
    unfold nxt
    split_ifs with h
    · simp [f, h]
    · simp [f, h]
  let G : ℕ → ℂˣ := fun j => if (a : ℕ) ≤ j then (f (j + 1))⁻¹ / (f j)⁻¹ else 1
  rw [Finset.prod_filter]
  have hterm : ∀ m : Fin n, (if a ≤ m then (ψ m / nxt ψ m) u else 1) = G m := by
    intro m
    simp only [G, Fin.le_def, MonoidHom.div_apply, hnx, ← hf m, inv_div_inv]
  rw [Finset.prod_congr rfl fun m _ => hterm m, Fin.prod_univ_eq_prod_range G n, ← Finset.prod_filter]
  have hs : (Finset.range n).filter (fun j => (a : ℕ) ≤ j) = Finset.Ico (a : ℕ) n := by
    ext j; simp; omega
  rw [hs, Finset.prod_Ico_div (f := fun j => (f j)⁻¹) a.isLt.le]
  simp [f, hf a]

theorem theta_of_triangular : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ) (g : GL (Fin n) k) (t : Fin n → kˣ), (∀ i, valuation k (t i : k) = 1) → (∀ i, g.val i i = t i) → ((∀ i j : Fin n, i < j → g.val i j = 0) ∨ ∀ i j : Fin n, j < i → g.val i j = 0) → theta ψ g = ∏ i, (ψ i (t i) : ℂ) := by
  intro k _ _ _ _ n ψ g t ht hd htri
  have hmin : ∀ m, minor g m = ((∏ i ∈ Finset.univ.filter (fun i => i ≤ m), t i : kˣ) : k) := by
    intro m
    rw [minor_of_triangular g m htri, Units.coe_prod]
    exact Finset.prod_congr rfl fun i _ => hd i
  have hev : ∀ (χ : kˣ →* ℂˣ) (u : kˣ), valuation k (u : k) = 1 → ev χ u = χ u := by
    intro χ u hu
    unfold ev
    rw [dite_eq_left hu]
    congr 2
    ext
    rfl
  have hval : ∀ s : Finset (Fin n), valuation k ((∏ i ∈ s, t i : kˣ) : k) = 1 := by
    intro s
    rw [Units.coe_prod, map_prod]
    exact Finset.prod_eq_one fun i _ => ht i
  unfold theta
  rw [Finset.prod_congr rfl fun m _ => by rw [hmin m, hev _ _ (hval _)]]
  rw [← Units.coe_prod, ← Units.coe_prod]
  congr 1
  simp only [map_prod]
  rw [Finset.prod_comm' (t' := Finset.univ) (s' := fun i => Finset.univ.filter (fun m => i ≤ m))
    (by intro x y; simp)]
  exact Finset.prod_congr rfl fun i _ => prod_div_nxt ψ i (t i)

end GlobalTheory.PsType
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeCharacterTriangularStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalSeriesTypeCharacter_triangular : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ) (g : GL (Fin n) k) (t : Fin n → kˣ), (∀ i, valuation k (t i : k) = 1) → (∀ i, g.val i i = t i) → ((∀ i j : Fin n, i < j → g.val i j = 0) ∨ ∀ i j : Fin n, j < i → g.val i j = 0) → theta ψ g = ∏ i, (ψ i (t i) : ℂ) := by
  first | exact @GlobalTheory.PsType.theta_of_triangular | exact GlobalTheory.PsType.theta_of_triangular | (intros; apply GlobalTheory.PsType.theta_of_triangular <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCharacterAverageEigenvectorCompactSubgroup
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCharacterAverageEigenvectorCompactSubgroup
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem avg_eig : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V), IsSmooth π → ∀ (H : Set G) (θ : G → ℂ), Datum H θ → ∀ w : V,
    ∃ R : Finset G, (1 : G) ∈ R ∧ (∀ j ∈ R, j ∈ H) ∧ IsEig π H θ (∑ j ∈ R, (θ j)⁻¹ • π j w) := by
  intro G V _ _ _ _ _ π hπ H θ hD w
  classical
  let Hs : Subgroup G :=
    { carrier := H
      mul_mem' := fun {a b} ha hb => hD.mul a ha b hb
      one_mem' := hD.one
      inv_mem' := fun {a} ha => hD.inv a ha }
  have hθinv : ∀ a ∈ H, θ a⁻¹ * θ a = 1 := fun a ha => by
    rw [← hD.val_mul _ (hD.inv a ha) _ ha, inv_mul_cancel, hD.val_one]
  have hθ0 : ∀ a ∈ H, θ a ≠ 0 := fun a ha h0 => by
    have := hθinv a ha; rw [h0, mul_zero] at this; exact zero_ne_one this
  have hπmul : ∀ a b : G, π (a * b) w = π a (π b w) := fun a b => by rw [map_mul]; rfl
  let T : Subgroup Hs :=
    { carrier := {j | π j w = θ j • w}
      one_mem' := by simp [hD.val_one]
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, Subgroup.coe_mul] at ha hb ⊢
        rw [hπmul, hb, map_smul, ha, smul_smul, hD.val_mul _ a.2 _ b.2, mul_comm]
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq, InvMemClass.coe_inv] at ha ⊢
        have h1 : w = θ a • π (a : G)⁻¹ w := by
          rw [← map_smul, ← ha, ← hπmul, inv_mul_cancel, map_one]; rfl
        have h2 : θ (a : G)⁻¹ = (θ a)⁻¹ := eq_inv_of_mul_eq_one_left (hθinv a a.2)
        rw [h2]
        conv_rhs => rw [h1]
        rw [smul_smul, inv_mul_cancel₀ (hθ0 a a.2), one_smul] }
  haveI : CompactSpace Hs := isCompact_iff_compactSpace.mp hD.compact
  have hopen : IsOpen (T : Set Hs) := by
    apply Subgroup.isOpen_of_mem_nhds T (g := 1)
    rw [nhds_subtype_eq_comap, Filter.mem_comap]
    obtain ⟨U, hU, hUθ⟩ := hD.near
    refine ⟨U ∩ {g | π g w = w}, Filter.inter_mem hU ((hπ w).mem_nhds (by simp)), ?_⟩
    rintro j ⟨hjU, hjw⟩
    show π j w = θ j • w
    rw [hjw, hUθ _ hjU j.2, one_smul]
  haveI : Finite (Hs ⧸ T) := Subgroup.quotient_finite_of_isOpen T hopen
  haveI : Fintype (Hs ⧸ T) := Fintype.ofFinite _
  let f : Hs → V := fun j => (θ j)⁻¹ • π j w
  have hf : ∀ a b : Hs, (a : Hs ⧸ T) = b → f a = f b := by
    intro a b hab
    rw [QuotientGroup.eq] at hab
    have hb : b = a * (a⁻¹ * b) := by group
    generalize a⁻¹ * b = s at hab hb
    subst hb
    have hs : π s w = θ s • w := hab
    simp only [f, Subgroup.coe_mul]
    rw [hπmul, hs, map_smul, smul_smul, hD.val_mul _ a.2 _ s.2, mul_inv, mul_assoc,
      inv_mul_cancel₀ (hθ0 s s.2), mul_one]
  have hact : ∀ h a : Hs, π h (f a) = θ h • f (h * a) := by
    intro h a
    simp only [f, Subgroup.coe_mul]
    rw [map_smul, hπmul, smul_smul, hD.val_mul _ h.2 _ a.2, mul_inv, ← mul_assoc,
      mul_inv_cancel₀ (hθ0 h h.2), one_mul]
  let rep : Hs ⧸ T → Hs := fun q => if q = ((1 : Hs) : Hs ⧸ T) then 1 else q.out
  have hrep : ∀ q, ((rep q : Hs) : Hs ⧸ T) = q := by
    intro q
    simp only [rep]
    split_ifs with hq
    · exact hq.symm
    · exact QuotientGroup.out_eq' q
  have hsum : ∀ h : Hs, π h (∑ q, f (rep q)) = θ h • ∑ q, f (rep q) := by
    intro h
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.smul_sum]
    simp_rw [hact]
    have : ∀ q, f (h * rep q) = f (rep (h • q)) := fun q => by
      apply hf
      rw [hrep (h • q)]
      conv_rhs => rw [← hrep q]
      rw [MulAction.Quotient.smul_mk, smul_eq_mul]
    simp_rw [this]
    exact Equiv.sum_comp (MulAction.toPerm h) (fun q => θ h • f (rep q))
  refine ⟨Finset.univ.image (fun q => ((rep q : Hs) : G)), ?_, ?_, ?_⟩
  · refine Finset.mem_image.mpr ⟨((1 : Hs) : Hs ⧸ T), Finset.mem_univ _, ?_⟩
    simp [rep]
  · intro j hj
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hj
    exact (rep q).2
  · have hinj : Set.InjOn (fun q => ((rep q : Hs) : G)) (Finset.univ : Finset (Hs ⧸ T)) := by
      intro q₁ _ q₂ _ h
      rw [← hrep q₁, ← hrep q₂, Subtype.ext h]
    rw [Finset.sum_image hinj]
    intro h hh
    exact hsum ⟨h, hh⟩

end GlobalTheory.PsType
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCharacterAverageEigenvectorCompactSubgroupStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_character_average_eigenvector_compact_subgroup : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∀ (H : Set G) (θ : G → ℂ), Datum H θ → ∀ w : V, ∃ R : Finset G, (1 : G) ∈ R ∧ (∀ j ∈ R, j ∈ H) ∧ IsEig π H θ (∑ j ∈ R, (θ j)⁻¹ • π j w) := by
  first | exact @GlobalTheory.PsType.avg_eig | exact GlobalTheory.PsType.avg_eig | (intros; apply GlobalTheory.PsType.avg_eig <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerFunctionTendstoConstTermExponential
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerFunctionTendstoConstTermExponential
open scoped MatrixGroups
open GlobalTheory.KZ

namespace GlobalTheory.KZ.ExpBound

theorem series_bound (a : ℕ → ℂ) (ψ : ℂ → ℂ) (C : ℝ)
    (hs : ∀ z : ℂ, C < z.im →
      HasSum (fun n : ℕ => a n * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * z)) (ψ z)) :
    ∃ B t : ℝ, ∀ w : ℂ, t < w.im → ‖ψ w - a 0‖ ≤ B * Real.exp (-(2 * Real.pi * (w.im - t))) := by
  have hnorm : ∀ (n : ℕ) (z : ℂ), ‖a n * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * z)‖ =
      ‖a n‖ * Real.exp (-(2 * Real.pi * n * z.im)) := by
    intro n z
    rw [norm_mul, Complex.norm_exp]
    congr 2
    simp [Complex.mul_re, Complex.mul_im]
  set t0 : ℝ := C + 1 with ht0
  have hz0 : ((t0 : ℂ) * Complex.I).im = t0 := by simp
  have hsm : Summable (fun n : ℕ => ‖a n‖ * Real.exp (-(2 * Real.pi * n * t0))) := by
    have h1 := (hs ((t0 : ℂ) * Complex.I) (by rw [hz0]; linarith)).summable
    have h2 := summable_norm_iff.mpr h1
    simpa only [hnorm, hz0] using h2
  set B0 : ℝ := ∑' n : ℕ, ‖a n‖ * Real.exp (-(2 * Real.pi * n * t0)) with hB0
  have hle : ∀ n : ℕ, ‖a n‖ * Real.exp (-(2 * Real.pi * n * t0)) ≤ B0 := fun n =>
    hsm.le_tsum n (fun j _ => by positivity)
  have hB0nn : 0 ≤ B0 := tsum_nonneg (fun j => by positivity)
  refine ⟨2 * B0, t0 + 1, fun w hw => ?_⟩
  set ρ : ℝ := Real.exp (-(2 * Real.pi * (w.im - t0))) with hρ
  have hρ0 : 0 < ρ := Real.exp_pos _
  have hpi := Real.pi_gt_three
  have hρ2 : ρ ≤ 1 / 2 := by
    have h1 : 1 ≤ 2 * Real.pi * (w.im - t0) := by nlinarith
    have h2 := Real.add_one_le_exp (2 * Real.pi * (w.im - t0))
    rw [hρ, Real.exp_neg, one_div]
    exact inv_anti₀ (by norm_num) (by linarith)
  have hsh := (hasSum_nat_add_iff' 1).mpr (hs w (by linarith))
  simp only [Finset.sum_range_one, Nat.cast_zero, mul_zero, zero_mul, Complex.exp_zero, mul_one] at hsh
  have hg : HasSum (fun n : ℕ => B0 * ρ * ρ ^ n) (B0 * ρ * (1 - ρ)⁻¹) :=
    (hasSum_geometric_of_lt_one hρ0.le (by linarith)).mul_left _
  have hb := tsum_of_norm_bounded hg (f := fun n : ℕ =>
      a (n + 1) * Complex.exp (2 * Real.pi * Complex.I * ((n + 1 : ℕ) : ℂ) * w)) (fun n => by
    rw [hnorm]
    have e : Real.exp (-(2 * Real.pi * ((n + 1 : ℕ) : ℝ) * w.im)) =
        Real.exp (-(2 * Real.pi * ((n + 1 : ℕ) : ℝ) * t0)) * ρ ^ (n + 1) := by
      rw [hρ, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    rw [e, ← mul_assoc, mul_assoc B0, ← pow_succ']
    exact mul_le_mul_of_nonneg_right (hle (n + 1)) (by positivity))
  rw [hsh.tsum_eq] at hb
  have h3 : B0 * ρ * (1 - ρ)⁻¹ ≤ 2 * B0 * ρ := by
    rw [← div_eq_mul_inv, div_le_iff₀ (by linarith)]
    nlinarith [mul_nonneg (mul_nonneg hB0nn hρ0.le) (show 0 ≤ 1 - 2 * ρ by linarith)]
  have h4 : ρ ≤ Real.exp (-(2 * Real.pi * (w.im - (t0 + 1)))) := by
    rw [hρ]
    exact Real.exp_le_exp.mpr (by nlinarith)
  calc ‖ψ w - a 0‖ ≤ B0 * ρ * (1 - ρ)⁻¹ := hb
    _ ≤ 2 * B0 * ρ := h3
    _ ≤ _ := mul_le_mul_of_nonneg_left h4 (by positivity)

theorem bound_at_infinity : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (h : X.K) (φ : ℂ → ℂ), ContinuousOn φ Hs → X.an h = (φ : Mero) → (∀ r : ℚ, (X.exp h).coeff r ≠ 0 → ∃ n : ℕ, r = n) → ∃ B t : ℝ, ∀ z ∈ Hs, t < z.im → ‖φ z - ε ((X.exp h).coeff 0)‖ ≤ B * Real.exp (-(2 * Real.pi * (z.im - t))) := by
  intro Ω _ _ ε X h φ hφc hφ hsupp
  obtain ⟨φ', C, hφ', hsum⟩ := X.an_exp h
  have hsumN : ∀ z : ℂ, C < z.im → HasSum (fun n : ℕ => ε ((X.exp h).coeff (n : ℚ)) *
      Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * z)) (φ' z) := by
    intro z hz
    have h1 := hsum z hz
    rw [← (Nat.cast_injective (R := ℚ)).hasSum_iff] at h1
    · simpa [Function.comp_def] using h1
    · intro r hr
      have : (X.exp h).coeff r = 0 := by
        by_contra hne
        obtain ⟨n, rfl⟩ := hsupp r hne
        exact hr ⟨n, rfl⟩
      simp [this]
  obtain ⟨B, t, hB⟩ := series_bound (fun n : ℕ => ε ((X.exp h).coeff (n : ℚ))) φ' C hsumN
  simp only [Nat.cast_zero] at hB
  refine ⟨B, t, fun z hz htz => ?_⟩
  have hev : φ =ᶠ[Filter.codiscreteWithin Hs] φ' := Filter.Germ.coe_eq.mp (hφ.symm.trans hφ')
  have h1 := mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp hev z hz
  have hHs : Hs ∈ nhds z := SiegelModel.isOpen_Hs.mem_nhds hz
  have h2 : Hs ∈ nhdsWithin z {z}ᶜ := mem_nhdsWithin_of_mem_nhds hHs
  have h3 : {w : ℂ | t < w.im} ∈ nhdsWithin z {z}ᶜ :=
    mem_nhdsWithin_of_mem_nhds ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds htz)
  have hl : Filter.Tendsto (fun w => ‖φ w - ε ((X.exp h).coeff 0)‖) (nhdsWithin z {z}ᶜ)
      (nhds ‖φ z - ε ((X.exp h).coeff 0)‖) :=
    (((hφc.continuousAt hHs).sub continuousAt_const).norm.tendsto).mono_left nhdsWithin_le_nhds
  have hc : Continuous fun w : ℂ => B * Real.exp (-(2 * Real.pi * (w.im - t))) := by fun_prop
  refine le_of_tendsto_of_tendsto hl ((hc.tendsto z).mono_left nhdsWithin_le_nhds) ?_
  filter_upwards [h1, h2, h3] with w hw1 hw2 hw3
  rcases hw1 with e | e
  · have e' : φ w = φ' w := e
    rw [e']
    exact hB w hw3
  · exact absurd hw2 e

end GlobalTheory.KZ.ExpBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerFunctionTendstoConstTermExponentialStatement
open scoped MatrixGroups
open GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modularTower_function_tendsto_constTerm_exponential : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (h : X.K) (φ : ℂ → ℂ), ContinuousOn φ Hs → X.an h = (φ : Mero) → (∀ r : ℚ, (X.exp h).coeff r ≠ 0 → ∃ n : ℕ, r = n) → ∃ B t : ℝ, ∀ z ∈ Hs, t < z.im → ‖φ z - ε ((X.exp h).coeff 0)‖ ≤ B * Real.exp (-(2 * Real.pi * (z.im - t))) := by
  first | exact @GlobalTheory.KZ.ExpBound.bound_at_infinity | exact GlobalTheory.KZ.ExpBound.bound_at_infinity | (intros; apply GlobalTheory.KZ.ExpBound.bound_at_infinity <;> assumption)
end
end
