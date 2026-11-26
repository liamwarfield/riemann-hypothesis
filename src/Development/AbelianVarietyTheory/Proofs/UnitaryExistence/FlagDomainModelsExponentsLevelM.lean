module

public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemPrincipalCongruenceInterCuspCentreIff
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.TraceFormDualOneTraceFormDual

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExponentMatchingIndependentOfCuspBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExponentMatchingIndependentOfCuspBasis
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.CuspBasis

open GlobalTheory.CuspCentre

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}

theorem map_cc_mul (A B : Matrix (Fin ρ) (Fin ρ) E) : (A * B).map cc = A.map cc * B.map cc := by
  ext a b
  simp [Matrix.mul_apply, cc_sum', cc_mul']

theorem map_cc_cc (A : Matrix (Fin ρ) (Fin ρ) E) : (A.map cc).map cc = A := by
  ext a b
  simp [cc_cc']

theorem map_cc_one : (1 : Matrix (Fin ρ) (Fin ρ) E).map cc = 1 := by
  ext a b
  by_cases h : a = b <;> simp [Matrix.one_apply, h, cc]

theorem isSkew_iff (β : Matrix (Fin ρ) (Fin ρ) E) : FJ.IsSkew β ↔ β.map cc = -βᵀ :=
  ⟨fun h => by ext a b; exact h a b, fun h a b => congrFun (congrFun h a) b⟩

theorem isHerm_iff (β : Matrix (Fin ρ) (Fin ρ) E) : FJ.IsHermE β ↔ β.map cc = βᵀ :=
  ⟨fun h => by ext a b; exact h a b, fun h a b => congrFun (congrFun h a) b⟩

theorem isHerm_conj (P χ : Matrix (Fin ρ) (Fin ρ) E) (h : FJ.IsHermE χ) :
    FJ.IsHermE (P * χ * (P.map cc)ᵀ) := by
  rw [isHerm_iff] at h ⊢
  rw [map_cc_mul, map_cc_mul, h, Matrix.transpose_map, map_cc_cc]
  simp [Matrix.transpose_mul, Matrix.mul_assoc]

theorem isSkew_conj (P β : Matrix (Fin ρ) (Fin ρ) E) (h : FJ.IsSkew β) :
    FJ.IsSkew (Pᵀ * β * P.map cc) := by
  rw [isSkew_iff] at h ⊢
  rw [map_cc_mul, map_cc_mul, h, Matrix.transpose_map, map_cc_cc]
  simp [Matrix.transpose_mul, Matrix.mul_assoc]

theorem comb_change {e₀ e : Fin ρ → Fin r → E} {P : Matrix (Fin ρ) (Fin ρ) E}
    (h : ∀ a, e₀ a = ∑ b, P a b • e b) (v : Fin ρ → E) :
    ∑ a, v a • e₀ a = ∑ b, (v ᵥ* P) b • e b := by
  simp only [h, Finset.smul_sum, smul_smul, Matrix.vecMul, dotProduct, Finset.sum_smul]
  exact Finset.sum_comm

theorem zMatE_change (X : Data E r) {e₀ e : Fin ρ → Fin r → E} {P : Matrix (Fin ρ) (Fin ρ) E}
    (h : ∀ a, e₀ a = ∑ b, P a b • e b) (β : Matrix (Fin ρ) (Fin ρ) E) :
    FJ.zMatE X e₀ β = FJ.zMatE X e (Pᵀ * β * P.map cc) := by
  rw [Matrix.ext_iff_mulVec]
  intro v
  rw [zMatE_mulVec, zMatE_mulVec, comb_change h]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  have h1 : (fun b => herm X.Gm v (e₀ b)) = P.map cc *ᵥ fun d => herm X.Gm v (e d) := by
    funext b
    rw [h b, herm_comb_r]
    rfl
  change ((β *ᵥ fun b => herm X.Gm v (e₀ b)) ᵥ* P) c =
    ((Pᵀ * β * P.map cc) *ᵥ fun d => herm X.Gm v (e d)) c
  rw [h1, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

variable {X : Data E r} {cu₀ cu : FJ.CuspFD X ρ} {P : Matrix (Fin ρ) (Fin ρ) E}

theorem zGam_change (h : ∀ a, cu₀.e a = ∑ b, P a b • cu.e b) {β : Matrix (Fin ρ) (Fin ρ) E}
    (hβ : β ∈ FJ.zGam X cu₀) : Pᵀ * β * P.map cc ∈ FJ.zGam X cu := by
  obtain ⟨hs, γ, hγ, e⟩ := hβ
  exact ⟨isSkew_conj P β hs, γ, hγ, e.trans (zMatE_change X h β)⟩

theorem lattice_le (h : ∀ a, cu₀.e a = ∑ b, P a b • cu.e b) : cu₀.I ≤ cu.I := by
  refine inf_le_inf_left _ fun x hx => ?_
  have hle : Submodule.span E (Set.range cu₀.e) ≤ Submodule.span E (Set.range cu.e) := by
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    rw [h a]
    exact sum_mem fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
  exact hle hx

theorem crdI_change (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
    (h : ∀ a, cu₀.e a = ∑ b, P a b • cu.e b) {v : Fin ρ → E} (hv : v ∈ FJ.crdI 𝔄 cu₀) :
    v ᵥ* P ∈ FJ.crdI 𝔄 cu := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨a, ha, x, hx, e⟩ := hv
    exact Submodule.subset_span ⟨a, ha, x, lattice_le h hx, e.trans (comb_change h v)⟩
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.add_vecMul]; exact add_mem hx hy
  | smul c x _ hx => rw [Matrix.smul_vecMul]; exact Submodule.smul_mem _ _ hx

theorem pair_change (P : Matrix (Fin ρ) (Fin ρ) E) (l x : Fin ρ → E) :
    ∑ i, (P *ᵥ l) i * x i = ∑ i, l i * (x ᵥ* P) i := by
  change (P *ᵥ l) ⬝ᵥ x = l ⬝ᵥ (x ᵥ* P)
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, dotProduct_comm]

theorem xcFD_change (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
    (h : ∀ a, cu₀.e a = ∑ b, P a b • cu.e b) {l : Fin ρ → E} (hl : l ∈ FJ.XcFD 𝔄 cu) :
    P *ᵥ l ∈ FJ.XcFD 𝔄 cu₀ := by
  rw [← SetLike.mem_coe, FJ.xcFD_coe] at hl ⊢
  intro x hx
  rw [pair_change]
  exact hl _ (crdI_change 𝔄 h hx)

theorem dualOE_change (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
    (h : ∀ a, cu₀.e a = ∑ b, P a b • cu.e b) {u : Fin ρ → E} (hu : u ∈ FJ.dualOE (FJ.XcFD 𝔄 cu₀)) :
    u ᵥ* P ∈ FJ.dualOE (FJ.XcFD 𝔄 cu) := by
  intro l hl
  have h1 := hu _ (xcFD_change 𝔄 h hl)
  have h2 := pair_change P l u
  simp only [mul_comm (u _), mul_comm ((u ᵥ* P) _)] at h1 ⊢
  rwa [← h2]

theorem prE_change (X : Data E r) (P χ β : Matrix (Fin ρ) (Fin ρ) E) :
    FJ.prE X (P * χ * (P.map cc)ᵀ) β = FJ.prE X χ (Pᵀ * β * P.map cc) := by
  have : Matrix.trace ((P * χ * (P.map cc)ᵀ)ᵀ * β) = Matrix.trace (χᵀ * (Pᵀ * β * P.map cc)) := by
    rw [← Matrix.mul_assoc χᵀ, Matrix.trace_mul_comm _ (P.map cc)]
    simp [Matrix.transpose_mul, Matrix.mul_assoc]
  simp only [FJ.prE, this]

theorem form_eq (χ : Matrix (Fin ρ) (Fin ρ) E) (u m : Fin ρ → E) :
    ∑ i, ∑ k, u i * χ i k * cc (m k) = u ⬝ᵥ (χ *ᵥ fun k => cc (m k)) := by
  simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem form_change (P χ : Matrix (Fin ρ) (Fin ρ) E) (u m : Fin ρ → E) :
    ∑ i, ∑ k, u i * (P * χ * (P.map cc)ᵀ) i k * cc (m k) =
      ∑ i, ∑ k, (u ᵥ* P) i * χ i k * cc ((m ᵥ* P) k) := by
  have h1 : (fun k => cc ((m ᵥ* P) k)) = (P.map cc)ᵀ *ᵥ fun k => cc (m k) := by
    funext k
    simp [Matrix.vecMul, Matrix.mulVec, dotProduct, cc_sum', cc_mul', mul_comm]
  rw [form_eq, form_eq, h1, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

theorem phase_change (h : ∀ a, cu₀.e a = ∑ b, P a b • cu.e b) {χ : Matrix (Fin ρ) (Fin ρ) E}
    (hχ : ∀ β ∈ FJ.zGam X cu, ∃ n : ℤ, FJ.prE X χ β = n) :
    ∀ β ∈ FJ.zGam X cu₀, ∃ n : ℤ, FJ.prE X (P * χ * (P.map cc)ᵀ) β = n := fun β hβ => by
  rw [prE_change]
  exact hχ _ (zGam_change h hβ)

theorem integral_change (N : ℕ) (h : ∀ a, cu₀.e a = ∑ b, P a b • cu.e b)
    {χ : Matrix (Fin ρ) (Fin ρ) E}
    (hχ : ∀ u ∈ FJ.dualOE (FJ.XcFD 1 cu), ∀ m ∈ FJ.dualOE (FJ.XcFD 1 cu),
      (N : E) * ∑ i, ∑ k, u i * χ i k * cc (m k) ∈ Set.range (algebraMap (𝓞 E) E)) :
    ∀ u ∈ FJ.dualOE (FJ.XcFD 1 cu₀), ∀ m ∈ FJ.dualOE (FJ.XcFD 1 cu₀),
      (N : E) * ∑ i, ∑ k, u i * (P * χ * (P.map cc)ᵀ) i k * cc (m k) ∈
        Set.range (algebraMap (𝓞 E) E) := fun u hu m hm => by
  rw [form_change]
  exact hχ _ (dualOE_change 1 h hu) _ (dualOE_change 1 h hm)

theorem basis_inv (hP : IsUnit P.det) (h : ∀ a, cu₀.e a = ∑ b, P a b • cu.e b) (a : Fin ρ) :
    cu.e a = ∑ b, P⁻¹ a b • cu₀.e b := by
  rw [comb_change h (P⁻¹ a)]
  have h1 : P⁻¹ a ᵥ* P = (1 : Matrix (Fin ρ) (Fin ρ) E) a := by
    rw [← Matrix.nonsing_inv_mul P hP]
    rfl
  rw [h1]
  simp [Matrix.one_apply]

theorem conj_inv (hP : IsUnit P.det) (χ : Matrix (Fin ρ) (Fin ρ) E) :
    P * (P⁻¹ * χ * (P⁻¹.map cc)ᵀ) * (P.map cc)ᵀ = χ := by
  have h1 : (P⁻¹.map cc)ᵀ * (P.map cc)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← map_cc_mul, Matrix.mul_nonsing_inv P hP, map_cc_one,
      Matrix.transpose_one]
  rw [Matrix.mul_assoc, Matrix.mul_assoc, h1, Matrix.mul_one, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv P hP, Matrix.one_mul]

theorem expoMatch_of_basis_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ N : ℕ) (X : Data E r) (cu₀ cu : FJ.CuspFD X ρ) (P : Matrix (Fin ρ) (Fin ρ) E), IsUnit P.det → (∀ a, cu₀.e a = ∑ b, P a b • cu.e b) → (∀ χ, FJ.IsHermE χ → ((∀ β ∈ FJ.zGam X cu, ∃ n : ℤ, FJ.prE X χ β = n) ↔ ∀ u ∈ FJ.dualOE (FJ.XcFD 1 cu), ∀ m ∈ FJ.dualOE (FJ.XcFD 1 cu), (N : E) * ∑ i, ∑ k, u i * χ i k * cc (m k) ∈ Set.range (algebraMap (𝓞 E) E))) → ∀ χ, FJ.IsHermE χ → ((∀ β ∈ FJ.zGam X cu₀, ∃ n : ℤ, FJ.prE X χ β = n) ↔ ∀ u ∈ FJ.dualOE (FJ.XcFD 1 cu₀), ∀ m ∈ FJ.dualOE (FJ.XcFD 1 cu₀), (N : E) * ∑ i, ∑ k, u i * χ i k * cc (m k) ∈ Set.range (algebraMap (𝓞 E) E)) := by
  intro E _ _ _ r ρ N X cu₀ cu P hP h H χ hχ
  have hQ := basis_inv hP h
  have H' := H _ (isHerm_conj P⁻¹ χ hχ)
  constructor
  · intro hA
    have := integral_change N h (H'.1 (phase_change hQ hA))
    rwa [conj_inv hP] at this
  · intro hB
    have := phase_change h (H'.2 (integral_change N hQ hB))
    rwa [conj_inv hP] at this

end GlobalTheory.CuspBasis
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExponentMatchingIndependentOfCuspBasisStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exponentMatching_independent_of_cuspBasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ N : ℕ) (X : Data E r) (cu₀ cu : FJ.CuspFD X ρ) (P : Matrix (Fin ρ) (Fin ρ) E), IsUnit P.det → (∀ a, cu₀.e a = ∑ b, P a b • cu.e b) → (∀ χ, FJ.IsHermE χ → ((∀ β ∈ FJ.zGam X cu, ∃ n : ℤ, FJ.prE X χ β = n) ↔ ∀ u ∈ FJ.dualOE (FJ.XcFD 1 cu), ∀ m ∈ FJ.dualOE (FJ.XcFD 1 cu), (N : E) * ∑ i, ∑ k, u i * χ i k * cc (m k) ∈ Set.range (algebraMap (𝓞 E) E))) → ∀ χ, FJ.IsHermE χ → ((∀ β ∈ FJ.zGam X cu₀, ∃ n : ℤ, FJ.prE X χ β = n) ↔ ∀ u ∈ FJ.dualOE (FJ.XcFD 1 cu₀), ∀ m ∈ FJ.dualOE (FJ.XcFD 1 cu₀), (N : E) * ∑ i, ∑ k, u i * χ i k * cc (m k) ∈ Set.range (algebraMap (𝓞 E) E)) := by
  first | exact @GlobalTheory.CuspBasis.expoMatch_of_basis_change | exact GlobalTheory.CuspBasis.expoMatch_of_basis_change | (intros; apply GlobalTheory.CuspBasis.expoMatch_of_basis_change <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CuspPairingIntIffHermitianExponentIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CmFieldHostElementAddConjEqOne
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.DiagDifferent

theorem trace_conj {E : Type} [Field E] [NumberField E] [IsCMField E] (a : E) :
    Algebra.trace ℚ E (cc a) = Algebra.trace ℚ E a :=
  Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) a

theorem conj_rt {E : Type} [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : cc (H.rt : E) = -(H.rt : E) := by
  have hs : (H.rt : E) ^ 2 = -(H.d : E) := by
    have := congrArg (fun x : 𝓞 E => (x : E)) H.rt_sq
    simpa using this
  have hsq : (cc (H.rt : E)) ^ 2 = (H.rt : E) ^ 2 := by
    unfold cc
    rw [← map_pow, hs, map_neg, map_natCast]
  refine (sq_eq_sq_iff_eq_or_eq_neg.1 hsq).resolve_left fun h1 => ?_
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h2 := IsCMField.complexEmbedding_complexConj E τ (H.rt : E)
  unfold cc at h1
  rw [h1] at h2
  have h3 : (τ (H.rt : E)) ^ 2 = -(H.d : ℂ) := by
    rw [← map_pow, hs, map_neg, map_natCast]
  obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 h2.symm
  rw [hr] at h3
  have h4 : r ^ 2 = -(H.d : ℝ) := by exact_mod_cast h3
  have h5 : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  nlinarith [sq_nonneg r]

theorem cmField_host_element_add_conj_eq_one {E : Type} [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : (H.w0 : E) + cc (H.w0 : E) = 1 := by
  have h1 : 2 * (H.w0 : E) = 1 + (H.rt : E) := by
    have := congrArg (fun x : 𝓞 E => (x : E)) H.two_weight_eq_one_add_root
    simpa [map_ofNat] using this
  have h2 : 2 * cc (H.w0 : E) = 1 + cc (H.rt : E) := by
    have := congrArg (IsCMField.complexConj E) h1
    rw [map_mul, map_add (f := _), map_one, map_ofNat] at this
    exact this
  rw [conj_rt] at h2
  have : (2 : E) * ((H.w0 : E) + cc (H.w0 : E)) = 2 * 1 := by linear_combination h1 + h2
  exact mul_left_cancel₀ two_ne_zero this

theorem trace_even_real_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (I : FractionalIdeal (𝓞 E)⁰ E) (x : E), (∀ a ∈ I, cc a ∈ I) → cc x = x → ((∀ s ∈ I, cc s = s → ∃ n : ℤ, Algebra.trace ℚ E (x * s) = 2 * n) ↔ ∀ s ∈ I, ∃ n : ℤ, Algebra.trace ℚ E (x * s) = n) := by
  intro E _ _ _ H I x hI hx
  have hmul : ∀ a b : E, cc (a * b) = cc a * cc b := fun a b => map_mul _ a b
  have hadd : ∀ a b : E, cc (a + b) = cc a + cc b := fun a b => map_add _ a b
  have hcc : ∀ a : E, cc (cc a) = a := fun a => IsCMField.complexConj_apply_apply E a
  constructor
  · intro h s hs
    have hm : s + cc s ∈ I := Submodule.add_mem (I : Submodule (𝓞 E) E) hs (hI s hs)
    obtain ⟨n, hn⟩ := h (s + cc s) hm (by rw [hadd, hcc, add_comm])
    refine ⟨n, ?_⟩
    have e : x * cc s = cc (x * s) := by rw [hmul, hx]
    rw [mul_add, map_add (f := _), e, trace_conj] at hn
    linarith
  · intro h s hs hcs
    have hm : (H.w0 : E) * s ∈ I := Submodule.smul_mem (I : Submodule (𝓞 E) E) H.w0 hs
    obtain ⟨n, hn⟩ := h _ hm
    refine ⟨n, ?_⟩
    have e : x * s = x * ((H.w0 : E) * s) + cc (x * ((H.w0 : E) * s)) := by
      rw [hmul, hmul, hx, hcs]
      linear_combination (-(x * s)) * cmField_host_element_add_conj_eq_one H
    rw [e, map_add (f := _), trace_conj, hn]
    ring

end GlobalTheory.DiagDifferent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CuspPairingIntIffHermitianExponentIntegral
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.ExponentTrace

section

variable {E : Type} [Field E] [NumberField E]

noncomputable abbrev dif (E : Type) [Field E] [NumberField E] : FractionalIdeal (𝓞 E)⁰ E :=
  ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E)

theorem mem_mul_inv_iff {A B : FractionalIdeal (𝓞 E)⁰ E} (hA : A ≠ 0) (x : E) :
    x ∈ B * A⁻¹ ↔ ∀ y ∈ A, x * y ∈ B := by
  rw [← div_eq_mul_inv, FractionalIdeal.mem_div_iff_of_ne_zero hA]

theorem mem_one_iff_range (x : E) :
    x ∈ Set.range (algebraMap (𝓞 E) E) ↔ x ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
  rw [FractionalIdeal.mem_one_iff]; rfl

theorem trace_dual_iff {A : FractionalIdeal (𝓞 E)⁰ E} (hA : A ≠ 0) (y : E) :
    (∀ a ∈ A, ∃ n : ℤ, Algebra.trace ℚ E (y * a) = n) ↔ y ∈ (dif E)⁻¹ * A⁻¹ := by
  have hdiff {x : E} : x ∈ (dif E)⁻¹ ↔
      ∀ a : E, IsIntegral ℤ a → ∃ k : ℤ, Algebra.trace ℚ E (x * a) = k := by
    unfold dif
    rw [coeIdeal_differentIdeal ℤ ℚ E (𝓞 E), inv_inv,
      FractionalIdeal.mem_dual (one_ne_zero (α := FractionalIdeal (𝓞 E)⁰ E))]
    refine forall_congr' fun a => ?_
    rw [mem_one_fractionalIdeal_iff, Algebra.traceForm_apply]
    exact imp_congr_right fun _ => ⟨fun ⟨k, hk⟩ => ⟨k, hk.symm⟩, fun ⟨k, hk⟩ => ⟨k, hk.symm⟩⟩
  rw [mem_mul_inv_iff hA]
  constructor
  · intro h a ha
    rw [hdiff]
    intro o ho
    have hm : a * o ∈ A := by
      have := FractionalIdeal.mul_mem_mul ha (mem_one_fractionalIdeal_iff.2 ho)
      rwa [mul_one] at this
    rw [mul_assoc]
    exact h _ hm
  · intro h a ha
    simpa using hdiff.1 (h a ha) 1 isIntegral_one

theorem coord_iff {A : FractionalIdeal (𝓞 E)⁰ E} (hA : A ≠ 0) (u : E) :
    (∀ y : E, (∀ a ∈ A, ∃ n : ℤ, Algebra.trace ℚ E (y * a) = n) →
      u * y ∈ Set.range (algebraMap (𝓞 E) E)) ↔ u ∈ dif E * A := by
  have hd : dif E ≠ 0 := coe_different_ne_zero
  have h0 : (dif E)⁻¹ * A⁻¹ ≠ 0 := mul_ne_zero (inv_ne_zero hd) (inv_ne_zero hA)
  have e : dif E * A = 1 * ((dif E)⁻¹ * A⁻¹)⁻¹ := by rw [mul_inv, inv_inv, inv_inv, one_mul]
  rw [e, mem_mul_inv_iff h0]
  simp only [trace_dual_iff hA, mem_one_iff_range]

variable [IsCMField E]

noncomputable def pairIdeal (N : ℕ) (A B : FractionalIdeal (𝓞 E)⁰ E) : FractionalIdeal (𝓞 E)⁰ E :=
  FractionalIdeal.spanSingleton (𝓞 E)⁰ (N : E) * A * (dif E * conjFrac B)

theorem pairIdeal_ne_zero {N : ℕ} (hN : 0 < N) {A B : FractionalIdeal (𝓞 E)⁰ E} (hA : A ≠ 0)
    (hB : B ≠ 0) : pairIdeal N A B ≠ 0 :=
  mul_ne_zero (mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.2
    (Nat.cast_ne_zero.2 hN.ne')) hA) (mul_ne_zero coe_different_ne_zero (conjFrac_ne_zero hB))

theorem ccm (a b : E) : cc (a * b) = cc a * cc b := map_mul _ a b
theorem cca (a b : E) : cc (a + b) = cc a + cc b := map_add _ a b
theorem ccc (a : E) : cc (cc a) = a := IsCMField.complexConj_apply_apply E a

theorem conj_mem_pairIdeal {N : ℕ} {A B : FractionalIdeal (𝓞 E)⁰ E} {s : E}
    (hs : s ∈ pairIdeal N A B) : cc s ∈ pairIdeal N B A := by
  have e : pairIdeal N B A = conjFrac (pairIdeal N A B) := by
    have hN : cc (N : E) = N := map_natCast _ N
    unfold pairIdeal
    rw [map_mul, map_mul, map_mul, conjFrac_conjFrac, conjFrac_spanSingleton, hN,
      conjFrac_different]
    ring
  rw [e]
  exact cc_mem_conjFrac.2 hs

theorem entry_iff (N : ℕ) (A : FractionalIdeal (𝓞 E)⁰ E) {B : FractionalIdeal (𝓞 E)⁰ E}
    (hB : B ≠ 0) (s : E) :
    (∀ y : E, (∀ a' ∈ B, ∃ n : ℤ, Algebra.trace ℚ E (y * cc a') = n) →
      ∃ z ∈ A, s * y = (N : E) * z) ↔ s ∈ pairIdeal N A B := by
  have hd : dif E ≠ 0 := coe_different_ne_zero
  have hB' := conjFrac_ne_zero hB
  have h0 : (dif E)⁻¹ * (conjFrac B)⁻¹ ≠ 0 := mul_ne_zero (inv_ne_zero hd) (inv_ne_zero hB')
  have e : pairIdeal N A B = (FractionalIdeal.spanSingleton (𝓞 E)⁰ (N : E) * A) *
      ((dif E)⁻¹ * (conjFrac B)⁻¹)⁻¹ := by
    rw [mul_inv, inv_inv, inv_inv]; rfl
  rw [e, mem_mul_inv_iff h0]
  refine forall_congr' fun y => imp_congr ?_ FractionalIdeal.mem_singleton_mul.symm
  rw [← trace_dual_iff hB']
  constructor
  · intro h a ha
    have := h _ (mem_conjFrac.1 ha)
    rwa [ccc] at this
  · intro h a ha
    exact h _ (cc_mem_conjFrac.2 ha)

theorem pair_iff {N : ℕ} (hN : 0 < N) {A B : FractionalIdeal (𝓞 E)⁰ E} (hA : A ≠ 0)
    (hB : B ≠ 0) (x : E) :
    (∀ s ∈ pairIdeal N A B, ∃ n : ℤ, Algebra.trace ℚ E (x * s) = n) ↔
      ∀ u ∈ dif E * A, ∀ m ∈ dif E * B,
        (N : E) * (u * x * cc m) ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
  have hd : dif E ≠ 0 := coe_different_ne_zero
  have hB' := conjFrac_ne_zero hB
  have hN' : (N : E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hs : FractionalIdeal.spanSingleton (𝓞 E)⁰ (N : E) ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.2 hN'
  have hc : conjFrac (dif E * B) = dif E * conjFrac B := by rw [map_mul, conjFrac_different]
  have e : (dif E)⁻¹ * (pairIdeal N A B)⁻¹ =
      FractionalIdeal.spanSingleton (𝓞 E)⁰ (N : E)⁻¹ *
        (1 * (dif E * conjFrac B)⁻¹ * (dif E * A)⁻¹) := by
    rw [← FractionalIdeal.spanSingleton_inv]
    unfold pairIdeal
    simp only [mul_inv]
    ring
  rw [trace_dual_iff (pairIdeal_ne_zero hN hA hB), e, FractionalIdeal.mem_singleton_mul]
  simp only [mem_mul_inv_iff (mul_ne_zero hd hA), mem_mul_inv_iff (mul_ne_zero hd hB')]
  constructor
  · rintro ⟨y, hy, rfl⟩ u hu m hm
    have := hy u hu (cc m) (hc ▸ cc_mem_conjFrac.2 hm)
    convert this using 1
    field_simp
  · intro h
    refine ⟨(N : E) * x, fun u hu m hm => ?_, by field_simp⟩
    have := h u hu (cc m) (mem_conjFrac.1 (hc ▸ hm))
    rw [ccc] at this
    convert this using 1
    ring

theorem prE_int_iff {r ρ : ℕ} (X : Data E r) (χ β : Matrix (Fin ρ) (Fin ρ) E) :
    (∃ n : ℤ, FJ.prE X χ β = n) ↔
      ∃ n : ℤ, Algebra.trace ℚ E (∑ a, ∑ b, χ a b * (β a b / X.ξ0)) = 2 * n := by
  have h1 : FJ.prE X χ β =
      (Algebra.trace ℚ E (Matrix.trace (χ.transpose * β) / (X.κ0 / 2)) : ℝ) / 2 := by
    rw [← X.re_sum_Psi, Complex.re_sum]; rfl
  have h2 : Matrix.trace (χ.transpose * β) / X.ξ0 = ∑ a, ∑ b, χ a b * (β a b / X.ξ0) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply,
      Finset.sum_div, mul_div_assoc]
    rw [Finset.sum_comm]
  rw [h1, ← h2]
  have key : ∀ (q : ℚ) (n : ℤ), (q : ℝ) / 2 = n ↔ q = 2 * n := fun q n => by
    rw [div_eq_iff two_ne_zero, mul_comm]
    exact_mod_cast Iff.rfl
  simp only [key]
  rcases X.κ0_xi with h | h
  · rw [h, mul_div_cancel_left₀ _ two_ne_zero]
  · rw [h, neg_div, mul_div_cancel_left₀ _ two_ne_zero, div_neg, map_neg]
    constructor <;> rintro ⟨n, hn⟩ <;> exact ⟨-n, by push_cast; linarith⟩

theorem skew_iff (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) {r ρ : ℕ} (X : Data E r)
    (I : Fin ρ → Fin ρ → FractionalIdeal (𝓞 E)⁰ E) (hI : ∀ a b, ∀ s ∈ I a b, cc s ∈ I b a)
    (χ : Matrix (Fin ρ) (Fin ρ) E) (hχ : FJ.IsHermE χ) :
    (∀ β, FJ.IsSkew β → (∀ a b, β a b / X.ξ0 ∈ I a b) → ∃ n : ℤ, FJ.prE X χ β = n) ↔
      ∀ a b, ∀ s ∈ I a b, ∃ n : ℤ, Algebra.trace ℚ E (χ a b * s) = n := by
  have hξ := X.ξ0_ne
  have hc0 : cc (0 : E) = 0 := map_zero _
  simp only [prE_int_iff]
  constructor
  · intro h a b s hs
    let S : Matrix (Fin ρ) (Fin ρ) E := Matrix.of fun i j =>
      (if a = i ∧ b = j then s else 0) + (if b = i ∧ a = j then cc s else 0)
    have hS : ∀ i j, (X.ξ0 • S) i j / X.ξ0 = S i j := fun i j => by
      rw [Matrix.smul_apply, smul_eq_mul, mul_div_cancel_left₀ _ hξ]
    obtain ⟨n, hn⟩ := h (X.ξ0 • S) (fun i j => by
      simp only [Matrix.smul_apply, smul_eq_mul, S, Matrix.of_apply, ccm, cca, X.ξ0_im,
        apply_ite cc, ccc, hc0, and_comm (a := a = j), and_comm (a := b = j)]
      ring) (fun i j => by
      rw [hS]
      refine Submodule.add_mem (I i j : Submodule (𝓞 E) E) ?_ ?_
      · split_ifs with h
        · obtain ⟨rfl, rfl⟩ := h; exact hs
        · exact zero_mem _
      · split_ifs with h
        · obtain ⟨rfl, rfl⟩ := h; exact hI _ _ s hs
        · exact zero_mem _)
    refine ⟨n, ?_⟩
    have e : ∑ i, ∑ j, χ i j * ((X.ξ0 • S) i j / X.ξ0) = χ a b * s + cc (χ a b * s) := by
      simp only [hS]
      simp only [S, Matrix.of_apply, mul_add, Finset.sum_add_distrib, ite_and, mul_ite, mul_zero]
      rw [ccm, hχ a b]
      simp
    rw [e, map_add (f := _), trace_cc] at hn
    linarith
  · intro h β hβ hm
    have hreal : cc (∑ a, ∑ b, χ a b * (β a b / X.ξ0)) = ∑ a, ∑ b, χ a b * (β a b / X.ξ0) := by
      have h1 : ∀ a b, IsCMField.complexConj E (χ a b) = χ b a := hχ
      have h2 : ∀ a b, IsCMField.complexConj E (β a b) = -β b a := hβ
      have h3 : IsCMField.complexConj E X.ξ0 = -X.ξ0 := X.ξ0_im
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [cc, map_sum, map_mul, map_div₀, h1, h2, h3, neg_div_neg_eq]
      rw [Finset.sum_comm]
    have := (DiagDifferent.trace_even_real_iff E H 1 _ (fun a ha =>
      mem_one_fractionalIdeal_iff.2 (isIntegral_cc (mem_one_fractionalIdeal_iff.1 ha))) hreal).2
      (fun o ho => ?_) 1 (FractionalIdeal.one_mem_one _) (map_one _)
    · rwa [mul_one] at this
    · have hh : ∀ a b, ∃ n : ℤ, Algebra.trace ℚ E (χ a b * (β a b / X.ξ0 * o)) = n := fun a b =>
        h a b _ (by
          have := FractionalIdeal.mul_mem_mul (hm a b) ho
          rwa [mul_one] at this)
      choose k hk using hh
      refine ⟨∑ a, ∑ b, k a b, ?_⟩
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Finset.sum_mul, map_sum, mul_assoc, hk]
      push_cast
      rfl

end

theorem prE_int_iff_values_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (r ρ : ℕ) (X : Data E r) (N : ℕ) (cc' : Fin ρ → FractionalIdeal (𝓞 E)⁰ E) (χ : Matrix (Fin ρ) (Fin ρ) E), 0 < N → (∀ b, cc' b ≠ 0) → FJ.IsHermE χ → ((∀ β, FJ.IsSkew β → (∀ a b (y : E), (∀ a' ∈ cc' b, ∃ n : ℤ, Algebra.trace ℚ E (y * cc a') = n) → ∃ z ∈ cc' a, β a b / X.ξ0 * y = (N : E) * z) → ∃ n : ℤ, FJ.prE X χ β = n) ↔ ∀ u m : Fin ρ → E, (∀ a (y : E), (∀ a' ∈ cc' a, ∃ n : ℤ, Algebra.trace ℚ E (y * a') = n) → u a * y ∈ Set.range (algebraMap (𝓞 E) E)) → (∀ a (y : E), (∀ a' ∈ cc' a, ∃ n : ℤ, Algebra.trace ℚ E (y * a') = n) → m a * y ∈ Set.range (algebraMap (𝓞 E) E)) → (N : E) * ∑ i, ∑ k, u i * χ i k * cc (m k) ∈ Set.range (algebraMap (𝓞 E) E)) := by
  intro E _ _ _ H r ρ X N cc' χ hN hc hχ
  have h1 := skew_iff H X (fun a b => pairIdeal N (cc' a) (cc' b))
    (fun a b s hs => conj_mem_pairIdeal hs) χ hχ
  simp only [entry_iff N _ (hc _), coord_iff (hc _)]
  rw [h1]
  simp only [pair_iff hN (hc _) (hc _), mem_one_iff_range]
  constructor
  · intro h u m hu hm
    simp only [Finset.mul_sum]
    exact Submodule.sum_mem ((1 : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) fun i _ =>
      Submodule.sum_mem _ fun k _ => h i k _ (hu i) _ (hm k)
  · intro h a b u hu m hm
    have hc0 : cc (0 : E) = 0 := map_zero _
    have hs : ∀ (a : Fin ρ) (u : E), u ∈ dif E * cc' a →
        ∀ i, (Pi.single a u : Fin ρ → E) i ∈ dif E * cc' i := fun a u hu i => by
      by_cases hi : i = a
      · subst hi; simpa using hu
      · rw [Pi.single_eq_of_ne hi]; exact FractionalIdeal.zero_mem _
    have := h _ _ (hs a u hu) (hs b m hm)
    simpa [Pi.single_apply, apply_ite cc, hc0] using this

end GlobalTheory.ExponentTrace
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CuspPairingIntIffHermitianExponentIntegralStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspPairing_int_iff_hermitianExponent_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (r ρ : ℕ) (X : Data E r) (N : ℕ) (cc' : Fin ρ → FractionalIdeal (𝓞 E)⁰ E) (χ : Matrix (Fin ρ) (Fin ρ) E), 0 < N → (∀ b, cc' b ≠ 0) → FJ.IsHermE χ → ((∀ β, FJ.IsSkew β → (∀ a b (y : E), (∀ a' ∈ cc' b, ∃ n : ℤ, Algebra.trace ℚ E (y * cc a') = n) → ∃ z ∈ cc' a, β a b / X.ξ0 * y = (N : E) * z) → ∃ n : ℤ, FJ.prE X χ β = n) ↔ ∀ u m : Fin ρ → E, (∀ a (y : E), (∀ a' ∈ cc' a, ∃ n : ℤ, Algebra.trace ℚ E (y * a') = n) → u a * y ∈ Set.range (algebraMap (𝓞 E) E)) → (∀ a (y : E), (∀ a' ∈ cc' a, ∃ n : ℤ, Algebra.trace ℚ E (y * a') = n) → m a * y ∈ Set.range (algebraMap (𝓞 E) E)) → (N : E) * ∑ i, ∑ k, u i * χ i k * cc (m k) ∈ Set.range (algebraMap (𝓞 E) E)) := by
  first | exact @GlobalTheory.ExponentTrace.prE_int_iff_values_integral | exact GlobalTheory.ExponentTrace.prE_int_iff_values_integral | (intros; apply GlobalTheory.ExponentTrace.prE_int_iff_values_integral <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCuspPseudoBasisAdaptedLatticeStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCuspPseudoBasisAdaptedLattice
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open scoped Matrix nonZeroDivisors

namespace GlobalTheory

theorem herm_comb_eq_zero_of_iso {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}
    (G : Matrix (Fin r) (Fin r) E) (e : Fin ρ → Fin r → E)
    (h : ∀ a b, herm G (e a) (e b) = 0) (u v : Fin ρ → E) :
    herm G (∑ i, u i • e i) (∑ j, v j • e j) = 0 := by
  have key : herm G (∑ i, u i • e i) (∑ j, v j • e j)
      = ∑ i, ∑ j, u i * cc (v j) * herm G (e i) (e j) := by
    have h1 : ∀ (y : Fin r → E), herm G (∑ i, u i • e i) y = ∑ i, u i * herm G (e i) y := by
      intro y
      simp only [herm, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
        Finset.sum_mul]
      rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin ρ)))]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    have h2 : ∀ (x : Fin r → E), herm G x (∑ j, v j • e j) = ∑ j, cc (v j) * herm G x (e j) := by
      intro x
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [herm, cc, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul,
        Finset.mul_sum]
      rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin ρ)))]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    simp only [h1, h2, Finset.mul_sum, mul_assoc]
  rw [key]
  simp [h]

theorem exists_cusp_pseudoBasis :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ) (X : Data E r) (cu₀ : FJ.CuspFD X ρ), ∃ (cu : FJ.CuspFD X ρ) (P : Matrix (Fin ρ) (Fin ρ) E) (cc' : Fin ρ → FractionalIdeal (𝓞 E)⁰ E), IsUnit P.det ∧ (∀ a, cu₀.e a = ∑ b, P a b • cu.e b) ∧ (∀ b, cc' b ≠ 0) ∧ (∀ a : Fin ρ → E, (∑ b, a b • cu.e b) ∈ X.Λ ↔ ∀ b, a b ∈ cc' b) := by
  intro E _ _ _ r ρ X cu₀
  classical
  let T : (Fin ρ → E) →ₗ[E] (Fin r → E) := Fintype.linearCombination E cu₀.e
  have hT : ∀ v, T v = ∑ i, v i • cu₀.e i := fun v => Fintype.linearCombination_apply E cu₀.e v
  obtain ⟨Ψ, hΨ⟩ := FJ.exists_crdMap cu₀
  have hinj : Function.Injective T := by
    refine Function.LeftInverse.injective (g := Ψ) fun v => ?_
    rw [hT, hΨ]
  let L : Submodule (𝓞 E) (Fin ρ → E) := X.Λ.comap (T.restrictScalars (𝓞 E))
  have hL : ∀ v, v ∈ L ↔ T v ∈ X.Λ := fun v => Iff.rfl
  have hfg : L.FG := by
    refine Submodule.FG.of_le (X.Λ_fg.map (Ψ.restrictScalars (𝓞 E))) fun v hv => ?_
    refine ⟨T v, (hL v).1 hv, ?_⟩
    show Ψ (T v) = v
    rw [hT, hΨ]
  have hsp : Submodule.span E (L : Set (Fin ρ → E)) = ⊤ := by
    rw [eq_top_iff]
    intro w _
    obtain ⟨c, hc, hcw⟩ := FJ.exists_smul_mem X (T w)
    have hcE : algebraMap (𝓞 E) E c ≠ 0 := fun h =>
      hc (IsFractionRing.injective (𝓞 E) E (by rw [map_zero]; exact h))
    have hm : algebraMap (𝓞 E) E c • w ∈ L := by
      rw [hL, map_smul, algebraMap_smul]
      exact hcw
    have := Submodule.smul_mem (Submodule.span E (L : Set (Fin ρ → E))) (algebraMap (𝓞 E) E c)⁻¹
      (Submodule.subset_span hm)
    rwa [smul_smul, inv_mul_cancel₀ hcE, one_smul] at this
  obtain ⟨s, e, c, hc, hmem, -⟩ := exists_pseudoBasis_adapted E ρ L ⊤ hfg hsp
  have hsum : ∀ a : Fin ρ → E, ∑ b, a b • T (e b) = T (∑ b, a b • e b) := by
    intro a
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul]
  refine ⟨⟨fun b => T (e b), e.linearIndependent.map' T (LinearMap.ker_eq_bot.2 hinj), ?_⟩,
    (e.toMatrix (Pi.basisFun E (Fin ρ)))ᵀ, c, ?_, ?_, hc, ?_⟩
  · intro a b
    simp only [hT]
    exact herm_comb_eq_zero_of_iso _ _ cu₀.iso _ _
  · rw [Matrix.det_transpose]
    exact e.isUnit_det _
  · intro a
    show cu₀.e a = ∑ b, e.repr (Pi.basisFun E (Fin ρ) a) b • T (e b)
    rw [hsum, e.sum_repr, hT]
    simp [Pi.single_apply]
  · intro a
    show ∑ b, a b • T (e b) ∈ X.Λ ↔ _
    rw [hsum, ← hL, hmem]
    simp only [e.repr_sum_self]

end GlobalTheory
end

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cusp_pseudoBasis_adapted_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ) (X : Data E r) (cu₀ : FJ.CuspFD X ρ), ∃ (cu : FJ.CuspFD X ρ) (P : Matrix (Fin ρ) (Fin ρ) E) (cc' : Fin ρ → FractionalIdeal (𝓞 E)⁰ E), IsUnit P.det ∧ (∀ a, cu₀.e a = ∑ b, P a b • cu.e b) ∧ (∀ b, cc' b ≠ 0) ∧ (∀ a : Fin ρ → E, (∑ b, a b • cu.e b) ∈ X.Λ ↔ ∀ b, a b ∈ cc' b) := by
  first | exact @GlobalTheory.exists_cusp_pseudoBasis | exact GlobalTheory.exists_cusp_pseudoBasis | (intros; apply GlobalTheory.exists_cusp_pseudoBasis <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemDualCuspCharacterLatticeIffAdaptedBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemDualCuspCharacterLatticeIffAdaptedBasis
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory

theorem mem_crdI_one_iff_of_adapted {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}
    {X : Data E r} (cu : FJ.CuspFD X ρ) (cc' : Fin ρ → FractionalIdeal (𝓞 E)⁰ E)
    (h : ∀ a : Fin ρ → E, (∑ b, a b • cu.e b) ∈ X.Λ ↔ ∀ b, a b ∈ cc' b) (v : Fin ρ → E) :
    v ∈ FJ.crdI 1 cu ↔ ∀ b, v b ∈ cc' b := by
  constructor
  · intro hv
    unfold FJ.crdI at hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨a, ha, x, hx, hax⟩ := hv
      rw [← h, ← hax]
      obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff (𝓞 E)⁰).1 (FractionalIdeal.mem_coe.1 ha)
      rw [algebraMap_smul]
      exact X.Λ.smul_mem o hx.1
    | zero => exact fun b => (cc' b).zero_mem
    | add x y _ _ hx hy =>
      exact fun b => FractionalIdeal.mem_coe.1
        (Submodule.add_mem _ (FractionalIdeal.mem_coe.2 (hx b)) (FractionalIdeal.mem_coe.2 (hy b)))
    | smul c x _ hx =>
      exact fun b => FractionalIdeal.mem_coe.1
        (Submodule.smul_mem _ c (FractionalIdeal.mem_coe.2 (hx b)))
  · intro hv
    refine Submodule.subset_span ⟨1, FractionalIdeal.mem_coe.2 (FractionalIdeal.one_mem_one _),
      ∑ i, v i • cu.e i, ⟨(h v).2 hv, ?_⟩, one_smul _ _⟩
    exact (show ∑ i, v i • cu.e i ∈ Submodule.span E (Set.range cu.e) from
      sum_mem fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

theorem mem_dualOE_xcFD_one_iff_of_adapted : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ) (X : Data E r) (cu : FJ.CuspFD X ρ) (cc' : Fin ρ → FractionalIdeal (𝓞 E)⁰ E), (∀ a : Fin ρ → E, (∑ b, a b • cu.e b) ∈ X.Λ ↔ ∀ b, a b ∈ cc' b) → ∀ u : Fin ρ → E, u ∈ FJ.dualOE (FJ.XcFD 1 cu) ↔ ∀ a (y : E), (∀ a' ∈ cc' a, ∃ n : ℤ, Algebra.trace ℚ E (y * a') = n) → u a * y ∈ Set.range (algebraMap (𝓞 E) E) := by
  intro E _ _ _ r ρ X cu cc' h u
  have hc := mem_crdI_one_iff_of_adapted cu cc' h
  constructor
  · intro hu a y hy
    have hm : (Pi.single a y : Fin ρ → E) ∈ FJ.XcFD 1 cu := by
      refine Submodule.subset_span fun x hx => ?_
      obtain ⟨n, hn⟩ := hy (x a) ((hc x).1 hx a)
      refine ⟨n, ?_⟩
      rw [← hn]
      congr 1
      simp [Pi.single_apply]
    have h2 := hu _ hm
    simpa [Pi.single_apply] using h2
  · intro hu x hx
    change ∑ i, u i * x i ∈ (algebraMap (𝓞 E) E).range
    unfold FJ.XcFD at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      refine sum_mem fun i _ => hu i (x i) fun a' ha' => ?_
      have hm : (Pi.single i a' : Fin ρ → E) ∈ FJ.crdI 1 cu := by
        rw [hc]
        intro b
        by_cases hb : b = i
        · subst hb; simpa using ha'
        · rw [Pi.single_eq_of_ne hb]; exact (cc' b).zero_mem
      obtain ⟨n, hn⟩ := hx _ hm
      refine ⟨n, ?_⟩
      rw [hn]
      congr 1
      simp [Pi.single_apply]
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      exact add_mem hx hy
    | smul c x _ hx =>
      have e : ∑ i, u i * (c • x) i = algebraMap (𝓞 E) E c * ∑ i, u i * x i := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Pi.smul_apply, Algebra.smul_def]; ring
      rw [e]
      exact mul_mem ⟨c, rfl⟩ hx

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemDualCuspCharacterLatticeIffAdaptedBasisStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_dual_cuspCharacterLattice_iff_adapted_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ) (X : Data E r) (cu : FJ.CuspFD X ρ) (cc' : Fin ρ → FractionalIdeal (𝓞 E)⁰ E), (∀ a : Fin ρ → E, (∑ b, a b • cu.e b) ∈ X.Λ ↔ ∀ b, a b ∈ cc' b) → ∀ u : Fin ρ → E, u ∈ FJ.dualOE (FJ.XcFD 1 cu) ↔ ∀ a (y : E), (∀ a' ∈ cc' a, ∃ n : ℤ, Algebra.trace ℚ E (y * a') = n) → u a * y ∈ Set.range (algebraMap (𝓞 E) E) := by
  first | exact @GlobalTheory.mem_dualOE_xcFD_one_iff_of_adapted | exact GlobalTheory.mem_dualOE_xcFD_one_iff_of_adapted | (intros; apply GlobalTheory.mem_dualOE_xcFD_one_iff_of_adapted <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FlagDomainModelsExponentsLevelM
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.ExpoModels

theorem exists_equiv_of_stab {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (γ : GL (Fin r) E)
    (h : IsUStab G Λ γ) :
    ∃ e : Λ ≃ₗ[𝓞 E] Λ, ∀ v : Λ, (e v : Fin r → E) = (γ : Matrix (Fin r) (Fin r) E) *ᵥ (v : Fin r → E) := by
  have hri : ∀ v, (γ : Matrix (Fin r) (Fin r) E) *ᵥ (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v) = v :=
    fun v => by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hli : ∀ v, ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) = v :=
    fun v => by rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  refine ⟨{ toFun := fun v => ⟨(γ : Matrix (Fin r) (Fin r) E) *ᵥ (v : Fin r → E), (h.2 _).1 v.2⟩
            invFun := fun v => ⟨((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ (v : Fin r → E),
              (h.2 _).2 (by rw [hri]; exact v.2)⟩
            map_add' := fun x y => Subtype.ext (by simp [Matrix.mulVec_add])
            map_smul' := fun a x => Subtype.ext (by simp [Matrix.mulVec_smul])
            left_inv := fun v => Subtype.ext (hli _)
            right_inv := fun v => Subtype.ext (hri _) }, fun v => rfl⟩

theorem mem_gamma_iff {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    {F : FamilyUnif Xo σ' ty} {r : ℕ} {M : ModelsOf F r} (hM : ModelBase M) (hA : l.A = 1) (k : Fin F.n)
    (γ : GL (Fin r) E) :
    γ ∈ (M.X k).Γ ↔ IsUStab (M.X k).Gm (M.X k).Λ γ ∧ ∀ v ∈ (M.X k).Λ, ∃ w ∈ (M.X k).Λ,
      (γ : Matrix (Fin r) (Fin r) E) *ᵥ v = v + l.M • w := by
  rw [hM.gam k γ]
  refine and_congr_right fun hs => ?_
  obtain ⟨e, he⟩ := exists_equiv_of_stab _ _ γ hs
  constructor
  · rintro ⟨h1, -⟩ v hv
    let gam : (F.Di k).La ≃ₗ[𝓞 E] (F.Di k).La := (M.φ k).trans (e.trans (M.φ k).symm)
    have hg : ∀ a, (M.φ k (gam a) : Fin r → E) = (γ : Matrix (Fin r) (Fin r) E) *ᵥ (M.φ k a : Fin r → E) := by
      intro a
      simp only [gam, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, he]
    have key := GlobalTheory.LevelHalf.trivial_mod_of_trivial_on_half E H (F.Di k) l gam
      (fun a b => by
        have h2 := hM.ef k (gam a) (gam b)
        rw [hg, hg, hs.1, ← hM.ef k a b] at h2
        exact_mod_cast h2)
      (fun a ha => by
        obtain ⟨b, hb⟩ := h1 a ha
        refine ⟨b, (M.φ k).injective (Subtype.ext ?_)⟩
        rw [hg, hb, map_add (f := _), map_nsmul]
        rfl)
    obtain ⟨b, hb⟩ := key ((M.φ k).symm ⟨v, hv⟩)
    refine ⟨M.φ k b, (M.φ k b).2, ?_⟩
    have h3 := hg ((M.φ k).symm ⟨v, hv⟩)
    rw [hb, map_add (f := _), map_nsmul, LinearEquiv.apply_symm_apply] at h3
    exact h3.symm
  · intro h
    refine ⟨fun a _ => ?_, fun a => ?_⟩
    · obtain ⟨w, hw, h2⟩ := h _ (M.φ k a).2
      refine ⟨(M.φ k).symm ⟨w, hw⟩, ?_⟩
      rw [LinearEquiv.apply_symm_apply]
      exact h2
    · refine ⟨(M.φ k).symm (e (M.φ k a) - M.φ k a), ?_⟩
      rw [LinearEquiv.apply_symm_apply, hA, one_smul, ← he]
      simp

theorem expoMatch_models : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ' : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ' ty) (r : ℕ) (M : ModelsOf F r) (ρ : ℕ), ModelBase M → l.A = 1 → FJ.ExpoMatch M.X 1 ρ l.M := by
  intro E _ _ _ H Dw l Xo σ' g ty F r M ρ hM hA cu₀
  obtain ⟨k, cu₀⟩ := cu₀
  obtain ⟨cu, P, cc', hP, hPe, hne, hΛ⟩ := GlobalTheory.T.exists_cusp_pseudoBasis_adapted_lattice E r ρ (M.X k) cu₀
  refine GlobalTheory.T.exponentMatching_independent_of_cuspBasis E r ρ l.M (M.X k) cu₀ cu P hP hPe ?_
  intro χ hχ
  let φ : (F.Di k).La →ₗ[𝓞 E] (Fin r → E) := (M.X k).Λ.subtype ∘ₗ (M.φ k).toLinearMap
  have hr : LinearMap.range φ = (M.X k).Λ := by
    simp only [φ, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, Submodule.range_subtype]
  have hz := GlobalTheory.T.mem_principalCongruence_inter_cuspCentre_iff E H r ρ (M.X k) l.M (F.Di k) φ cu cc' hr
    ⟨Subtype.val_injective.comp (M.φ k).injective,
      by rw [← LinearMap.coe_range, hr]; exact (M.X k).Λ_span,
      (M.X k).Gm_herm, (M.X k).Gm_det, hM.ef k⟩ (mem_gamma_iff hM hA k) hΛ
  have hd := GlobalTheory.T.mem_dual_cuspCharacterLattice_iff_adapted_basis E r ρ (M.X k) cu cc' hΛ
  have ht := GlobalTheory.T.cuspPairing_int_iff_hermitianExponent_integral E H r ρ (M.X k) l.M cc' χ (by have := l.three_le; omega) hne hχ
  constructor
  · intro h u hu m hm
    exact ht.1 (fun β h1 h2 => h β ((hz β).2 ⟨h1, h2⟩)) u m ((hd u).1 hu) ((hd m).1 hm)
  · intro h β hβ
    exact ht.2 (fun u m hu hm => h u ((hd u).2 hu) m ((hd m).2 hm)) β ((hz β).1 hβ).1 ((hz β).1 hβ).2

end GlobalTheory.ExpoModels
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FlagDomainModelsExponentsLevelMStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagDomainModels_exponents_levelM : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ' : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ' ty) (r : ℕ) (M : ModelsOf F r) (ρ : ℕ), ModelBase M → l.A = 1 → FJ.ExpoMatch M.X 1 ρ l.M := by
  first | exact @GlobalTheory.ExpoModels.expoMatch_models | exact GlobalTheory.ExpoModels.expoMatch_models | (intros; apply GlobalTheory.ExpoModels.expoMatch_models <;> assumption)
end
