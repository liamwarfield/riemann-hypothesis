module

public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HasRationalTorsionIffMemRange

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsIntegralModelOfForms
namespace GlobalTheory

open WeierstrassCurve Polynomial

theorem j_mul_Δ {R : Type*} [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic] :
    W.j * W.Δ = W.c₄ ^ 3 := by
  rw [WeierstrassCurve.j, ← coe_Δ', mul_right_comm, Units.inv_mul, one_mul]

section Saturation

variable {K : Type*} [Field K]

def powSaturation (S : Subring K) (p : ℕ) : Subring K where
  carrier := {x | ∃ n : ℕ, (p : K) ^ n * x ∈ S}
  mul_mem' := by
    rintro x y ⟨m, hm⟩ ⟨n, hn⟩
    exact ⟨m + n, by convert S.mul_mem hm hn using 1; ring⟩
  one_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro x y ⟨m, hm⟩ ⟨n, hn⟩
    refine ⟨m + n, ?_⟩
    convert S.add_mem (S.mul_mem (S.pow_mem (natCast_mem S p) n) hm)
      (S.mul_mem (S.pow_mem (natCast_mem S p) m) hn) using 1
    ring
  zero_mem' := ⟨0, by simp⟩
  neg_mem' := by
    rintro x ⟨m, hm⟩
    exact ⟨m, by convert S.neg_mem hm using 1; ring⟩

theorem mem_powSaturation {S : Subring K} {p : ℕ} {x y : K} (n : ℕ) (hy : y ∈ S)
    (h : (p : K) ^ n * x = y) : x ∈ powSaturation S p :=
  ⟨n, h ▸ hy⟩

theorem mem_of_mem_powSaturation {S : Subring K} {p q : ℕ} (hpq : p.Coprime q) {x : K}
    (hp : x ∈ powSaturation S p) (hq : x ∈ powSaturation S q) : x ∈ S := by
  obtain ⟨m, hm⟩ := hp
  obtain ⟨n, hn⟩ := hq
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr (hpq.pow m n)
  have h : (u : K) * p ^ m + v * q ^ n = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → K) huv
  convert S.add_mem (S.mul_mem (intCast_mem S u) hm) (S.mul_mem (intCast_mem S v) hn) using 1
  linear_combination -x * h

theorem coeff_mem_variableChange (S : Subring K) {W : WeierstrassCurve K} {r s t : K}
    (h₁ : W.a₁ ∈ S) (h₂ : W.a₂ ∈ S) (h₃ : W.a₃ ∈ S) (h₄ : W.a₄ ∈ S) (h₆ : W.a₆ ∈ S)
    (hr : r ∈ S) (hs : s ∈ S) (ht : t ∈ S) {W' : WeierstrassCurve K}
    (e : (⟨1, r, s, t⟩ : VariableChange K) • W = W') :
    W'.a₁ ∈ S ∧ W'.a₂ ∈ S ∧ W'.a₃ ∈ S ∧ W'.a₄ ∈ S ∧ W'.a₆ ∈ S := by
  subst e
  simp only [variableChange_def, inv_one, Units.val_one, one_pow, one_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> aesop

end Saturation

section Models

variable (A : Type*) [CommRing A] {K : Type*} [Field K] [Algebra A K] [IsIntegrallyClosedIn A K]

variable {A} in
theorem mem_range_of_quartic {x c₀ c₁ c₂ c₃ : K} (h₀ : c₀ ∈ (algebraMap A K).range)
    (h₁ : c₁ ∈ (algebraMap A K).range) (h₂ : c₂ ∈ (algebraMap A K).range)
    (h₃ : c₃ ∈ (algebraMap A K).range) (h : x ^ 4 + c₃ * x ^ 3 + c₂ * x ^ 2 + c₁ * x + c₀ = 0) :
    x ∈ (algebraMap A K).range := by
  obtain ⟨c₀, rfl⟩ := h₀
  obtain ⟨c₁, rfl⟩ := h₁
  obtain ⟨c₂, rfl⟩ := h₂
  obtain ⟨c₃, rfl⟩ := h₃
  apply IsIntegrallyClosedIn.algebraMap_eq_of_integral
  refine ⟨X ^ 4 + C c₃ * X ^ 3 + C c₂ * X ^ 2 + C c₁ * X + C c₀, by monicity!, ?_⟩
  simpa [eval₂_add, eval₂_mul, eval₂_pow] using h

variable [CharZero K] {L : Type*} [Field L] [Algebra K L] [IsAlgClosed L]
  {W : WeierstrassCurve K} [W.IsElliptic]

theorem exists_integral_model_of_forms (hj : W.j ∈ (algebraMap A K).range) (hΔ : W.Δ = 1)
    {C₂ C₃ : VariableChange K} (hu₂ : C₂.u = 1) (hu₃ : C₃.u = 1) {P Q a b : K}
    (e₂ : C₂ • W = splitCurve P Q) (e₃ : C₃ • W = deuringCurve a b) :
    ∃ (C : VariableChange K) (W₀ : WeierstrassCurve A), C • W = W₀.baseChange K ∧ W₀.Δ = 1 := by
  have hinj : Function.Injective (algebraMap A K) := IsIntegralClosure.algebraMap_injective A A K
  set S := (algebraMap A K).range with hS
  have hjΔ := j_mul_Δ W
  have hrel := W.c_relation
  rw [hΔ] at hjΔ hrel
  have hc₄ : W.c₄ ∈ S := mem_range_of_quartic (zero_mem _) (neg_mem hj) (zero_mem _) (zero_mem _)
    (by linear_combination -W.c₄ * hjΔ)
  have hc₆ : W.c₆ ∈ S := mem_range_of_quartic (zero_mem _) (zero_mem _)
    (sub_mem (ofNat_mem _ 1728) (pow_mem hc₄ 3)) (zero_mem _)
    (by linear_combination W.c₆ ^ 2 * hrel)
  have p₄ := variableChange_c₄ W C₂
  have pΔ := variableChange_Δ W C₂
  have q₄ := variableChange_c₄ W C₃
  have q₆ := variableChange_c₆ W C₃
  have qΔ := variableChange_Δ W C₃
  rw [e₂, hu₂] at p₄ pΔ
  rw [e₃, hu₃] at q₄ q₆ qΔ
  simp only [inv_one, Units.val_one, one_pow, one_mul, hΔ, splitCurve_Δ, splitCurve_c₄,
    deuringCurve_Δ, deuringCurve_c₄] at p₄ pΔ q₄ q₆ qΔ
  replace q₆ : -a ^ 6 + 36 * a ^ 3 * b - 216 * b ^ 2 = W.c₆ := by
    rw [← q₆]
    simp only [deuringCurve, c₆, b₂, b₄, b₆]
    ring
  have hN : 16 * (P * Q) ∈ S := mem_range_of_quartic (zero_mem _) (ofNat_mem _ 256) (zero_mem _)
    (neg_mem hc₄) (by rw [← p₄]; linear_combination -256 * 16 * (P * Q) * pΔ)
  have hM : 4 * (P + Q) ∈ S := mem_range_of_quartic (zero_mem _) (zero_mem _)
    (neg_mem (add_mem hc₄ (mul_mem (ofNat_mem _ 3) hN))) (zero_mem _) (by rw [← p₄]; ring)
  have ha₂ : a ^ 2 ∈ S := mem_range_of_quartic (mul_mem (neg_mem (ofNat_mem _ 3)) (pow_mem hc₄ 2))
    (mul_mem (neg_mem (ofNat_mem _ 8)) hc₆) (mul_mem (neg_mem (ofNat_mem _ 6)) hc₄) (zero_mem _)
    (by rw [← q₄, ← q₆]; ring)
  have ha : a ∈ S := mem_range_of_quartic (zero_mem _) (zero_mem _) (neg_mem ha₂) (zero_mem _)
    (by ring)
  have hb : 27 * b ∈ S := mem_range_of_quartic (ofNat_mem _ 19683) (zero_mem _) (zero_mem _)
    (neg_mem (pow_mem ha 3)) (by linear_combination -19683 * qΔ)
  obtain ⟨r, s, t, hD⟩ : ∃ r s t : K, C₃ * C₂⁻¹ = ⟨1, r, s, t⟩ :=
    ⟨_, _, _, VariableChange.ext (by simp [VariableChange.mul_def, VariableChange.inv_def, hu₂, hu₃])
      rfl rfl rfl⟩
  have eD : (⟨1, r, s, t⟩ : VariableChange K) • splitCurve P Q = deuringCurve a b := by
    rw [← hD, ← e₂, ← e₃, mul_smul, inv_smul_smul]
  have d₁ := congrArg WeierstrassCurve.a₁ eD
  have d₂ := congrArg WeierstrassCurve.a₂ eD
  have d₃ := congrArg WeierstrassCurve.a₃ eD
  simp only [variableChange_def, splitCurve, deuringCurve, inv_one, Units.val_one] at d₁ d₂ d₃
  have hr : 12 * r ∈ S := by
    convert add_mem ha₂ hM using 1
    linear_combination 4 * d₂ + (2 * s + a) * d₁
  have ht : 54 * (t - 4 * r * s) ∈ S := by
    convert sub_mem hb (mul_mem (ofNat_mem _ 9) (mul_mem hr ha)) using 1
    linear_combination 27 * d₃ - 108 * r * d₁
  set W' := (⟨1, -4 * r, 0, -28 * (t - 4 * r * s)⟩ : VariableChange K) • deuringCurve a b with hW'
  have e' : (⟨1, -3 * r, s, -27 * (t - 4 * r * s)⟩ : VariableChange K) • splitCurve P Q = W' := by
    rw [hW', ← eD, ← mul_smul]
    congr 1
    simp only [VariableChange.mul_def, Units.val_one, mul_one]
    ext <;> dsimp only <;> ring
  have m₃ := coeff_mem_variableChange (powSaturation S 3) (W := deuringCurve a b)
    (mem_powSaturation 0 ha (by simp [deuringCurve])) (zero_mem _)
    (mem_powSaturation 3 hb (by simp only [deuringCurve]; norm_num)) (zero_mem _) (zero_mem _)
    (mem_powSaturation 1 (neg_mem hr) (by push_cast; ring)) (zero_mem _)
    (mem_powSaturation 3 (mul_mem (neg_mem (ofNat_mem _ 14)) ht) (by push_cast; ring)) hW'.symm
  have m₂ := coeff_mem_variableChange (powSaturation S 2) (W := splitCurve P Q)
    (zero_mem _) (mem_powSaturation 2 (neg_mem hM) (by simp only [splitCurve]; push_cast; ring))
    (zero_mem _) (mem_powSaturation 4 hN (by simp only [splitCurve]; push_cast; ring)) (zero_mem _)
    (mem_powSaturation 2 (neg_mem hr) (by push_cast; ring))
    (mem_powSaturation 1 ha (by push_cast; linear_combination d₁))
    (mem_powSaturation 1 (neg_mem ht) (by push_cast; ring)) e'
  have hc : Nat.Coprime 2 3 := by norm_num
  obtain ⟨W₀, hW₀⟩ := (isIntegral_of_exists_lift A
    (mem_of_mem_powSaturation hc m₂.1 m₃.1) (mem_of_mem_powSaturation hc m₂.2.1 m₃.2.1)
    (mem_of_mem_powSaturation hc m₂.2.2.1 m₃.2.2.1)
    (mem_of_mem_powSaturation hc m₂.2.2.2.1 m₃.2.2.2.1)
    (mem_of_mem_powSaturation hc m₂.2.2.2.2 m₃.2.2.2.2)).integral
  refine ⟨⟨1, -4 * r, 0, -28 * (t - 4 * r * s)⟩ * C₃, W₀, by rw [mul_smul, e₃, ← hW₀], hinj ?_⟩
  rw [← map_Δ, ← WeierstrassCurve.baseChange, ← hW₀, hW', variableChange_Δ, deuringCurve_Δ, qΔ]
  simp

theorem exists_integral_model (hj : W.j ∈ (algebraMap A K).range)
    (h : HasRationalTorsion W L 12) :
    ∃ (C : VariableChange K) (W₀ : WeierstrassCurve A), C • W = W₀.baseChange K ∧ W₀.Δ = 1 := by
  obtain ⟨δ, hδ⟩ := h.exists_pow_twelve_eq_Δ
  have hΔ := W.isUnit_Δ.ne_zero
  have hδ0 : δ ≠ 0 := by rintro rfl; simp [← hδ] at hΔ
  set C₁ : VariableChange K := ⟨Units.mk0 δ hδ0, 0, 0, 0⟩ with hC₁
  have h' := h.variableChange C₁
  obtain ⟨C₂, P, Q, hu₂, e₂⟩ := (h'.of_dvd (by norm_num : 2 ∣ 12)).exists_splitCurve
  obtain ⟨C₃, a, b, -, hu₃, e₃, -⟩ := (h'.of_dvd (by norm_num : 3 ∣ 12)).exists_deuringCurve
  obtain ⟨C, W₀, e, h₀⟩ := exists_integral_model_of_forms A (W := C₁ • W)
    (by rwa [variableChange_j]) (by rw [variableChange_Δ, ← hδ]; simp [hC₁, hδ0]) hu₂ hu₃ e₂ e₃
  exact ⟨C * C₁, W₀, by rw [mul_smul, e], h₀⟩

end Models

end GlobalTheory
end

namespace GlobalTheory

open WeierstrassCurve WeierstrassCurve.Affine Polynomial NumberField IsDedekindDomain
open scoped nonZeroDivisors

section Valuation

variable (V : Type*) [CommRing V] [IsDomain V] [ValuationRing V] {K : Type*} [Field K] [CharZero K]
  [Algebra V K] [IsFractionRing V K] {L : Type*} [Field L] [Algebra K L] [IsAlgClosed L]
  {W : WeierstrassCurve K} [W.IsElliptic]

end Valuation

section Good

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {K : Type*} [Field K]
  [Algebra R K] [IsFractionRing R K]

end Good

instance isDiscreteValuationRing_valuationSubringAtPrime {R : Type*} [CommRing R]
    [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (p : HeightOneSpectrum R) : IsDiscreteValuationRing (p.valuationSubringAtPrime K) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R p.ne_bot _

section Global

variable {M : Type*} [Field M] [CharZero M] {L : Type*} [Field L] [Algebra M L] [IsAlgClosed L]
  {W : WeierstrassCurve M} [W.IsElliptic]

theorem exists_model_ringOfIntegers (hj : IsIntegral ℤ W.j) (h : HasRationalTorsion W L 12)
    (M' : Type*) [Field M'] [Algebra M M'] :
    ∃ (C : VariableChange M') (W₀ : WeierstrassCurve (𝓞 M')),
      C • W.baseChange M' = W₀.baseChange M' ∧ W₀.Δ = 1 := by
  have : IsIntegrallyClosedIn (𝓞 M) M := inferInstance
  obtain ⟨C, W₀, e, h₀⟩ := exists_integral_model (𝓞 M) ⟨⟨W.j, hj⟩, rfl⟩ h
  refine ⟨C.map (algebraMap M M'), W₀.map (algebraMap (𝓞 M) (𝓞 M')), ?_, by rw [map_Δ, h₀, map_one]⟩
  rw [WeierstrassCurve.baseChange, map_variableChange, e]
  rfl

end Global

section Finite

theorem finite_nsmul_eq_zero_mul {G : Type*} [AddCommGroup G] {m n : ℕ}
    (hm : {x : G | m • x = 0}.Finite) (hn : {x : G | n • x = 0}.Finite) :
    {x : G | (m * n) • x = 0}.Finite := by
  refine Set.Finite.of_finite_fibers (fun x => m • x) (hn.subset ?_) ?_
  · rintro _ ⟨x, hx, rfl⟩
    simpa [mul_nsmul] using hx
  · rintro _ ⟨x, -, rfl⟩
    refine (hm.image (· + x)).subset fun y hy => ⟨y - x, ?_, sub_add_cancel _ _⟩
    have : m • y = m • x := hy.2
    simp [smul_sub, this]

variable {F : Type*} [Field F] {W : WeierstrassCurve F}

theorem finite_points_of_root {p : F[X]} (hp : p ≠ 0) {s : Set W.toAffine.Point}
    (hs : ∀ x y h, Point.some x y h ∈ s → p.eval x = 0) : s.Finite := by
  refine Set.Finite.of_finite_fibers Point.xRep
    ((((p.rootSet_finite F).image fun x => ![x, 1]).insert ![1, 0]).subset ?_) ?_
  · rintro _ ⟨_ | ⟨x, y, h⟩, hP, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨x, by simpa [mem_rootSet, hp] using hs x y h hP, rfl⟩
  · rintro _ ⟨P, -, rfl⟩
    exact (Set.toFinite {P, -P}).subset fun Q hQ => Point.eq_or_eq_neg_of_xRep_eq_xRep hQ.2

variable [CharZero F] [DecidableEq F]

theorem finite_two_torsion : {P : W.toAffine.Point | 2 • P = 0}.Finite := by
  refine finite_points_of_root (W.Ψ₂Sq_ne_zero (by norm_num)) fun x y h hP => ?_
  have hy : y = W.toAffine.negY x y := by
    by_contra hy
    rw [Set.mem_setOf_eq, two_nsmul, Point.add_self_of_Y_ne hy] at hP
    exact Point.some_ne_zero _ hP
  have hE := (equation_iff ..).mp h.1
  rw [negY] at hy
  simp only [Ψ₂Sq, b₂, b₄, b₆, eval_add, eval_mul, eval_pow, eval_C, eval_X]
  linear_combination -4 * hE + (2 * y + W.a₁ * x + W.a₃) * hy

theorem finite_three_torsion : {P : W.toAffine.Point | 3 • P = 0}.Finite :=
  finite_points_of_root (W.Ψ₃_ne_zero three_ne_zero) fun _ _ h hP =>
    (three_nsmul_eq_zero_iff h).mp hP

theorem finite_twelve_torsion : {P : W.toAffine.Point | 12 • P = 0}.Finite :=
  finite_nsmul_eq_zero_mul (m := 2 * 2) (n := 3)
    (finite_nsmul_eq_zero_mul finite_two_torsion finite_two_torsion) finite_three_torsion

end Finite

theorem exists_finite_hasRationalTorsion_twelve {K : Type*} [Field K] [CharZero K]
    (W : WeierstrassCurve K) (L : Type*) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] :
    ∃ M : IntermediateField K L, FiniteDimensional K M ∧
      HasRationalTorsion (W.baseChange M) L 12 := by
  classical
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  let c : (W.baseChange L).toAffine.Point → Set L
    | .zero => ∅
    | .some x y _ => {x, y}
  have hfin : (⋃ P ∈ {P : (W.baseChange L).toAffine.Point | 12 • P = 0}, c P).Finite := by
    refine finite_twelve_torsion.biUnion ?_
    rintro (_ | _) - <;> simp [c]
  have := hfin.to_subtype
  refine ⟨IntermediateField.adjoin K _, IntermediateField.finiteDimensional_adjoin
    (S := ⋃ P ∈ {P : (W.baseChange L).toAffine.Point | 12 • P = 0}, c P)
    fun x _ => Algebra.IsIntegral.isIntegral x, ?_⟩
  rw [hasRationalTorsion_iff]
  intro x y h h0
  exact ⟨⟨⟨x, IntermediateField.subset_adjoin _ _ (Set.mem_biUnion (x := .some x y h) h0
      (by simp [c]))⟩, rfl⟩,
    ⟨⟨y, IntermediateField.subset_adjoin _ _ (Set.mem_biUnion (x := .some x y h) h0
      (by simp [c]))⟩, rfl⟩⟩

theorem exists_finite_model_ringOfIntegers {K : Type*} [Field K] [NumberField K]
    (W : WeierstrassCurve K) [W.IsElliptic] (hj : IsIntegral ℤ W.j) :
    ∃ M : IntermediateField K (AlgebraicClosure K), NumberField M ∧
      HasRationalTorsion (W.baseChange M) (AlgebraicClosure K) 12 ∧
      ∃ (C : VariableChange M) (W₀ : WeierstrassCurve (𝓞 M)),
        C • W.baseChange M = W₀.baseChange M ∧ W₀.Δ = 1 := by
  obtain ⟨M, hM, h⟩ := exists_finite_hasRationalTorsion_twelve W (AlgebraicClosure K)
  have : NumberField M := NumberField.of_module_finite K M
  have : (W.baseChange M).IsElliptic := inferInstanceAs (W.map (algebraMap K M)).IsElliptic
  have hj' : IsIntegral ℤ (W.baseChange M).j := by
    rw [show (W.baseChange M).j = algebraMap K M W.j from W.map_j _]
    exact hj.algebraMap
  exact ⟨M, inferInstance, h, exists_model_ringOfIntegers hj' h M⟩

end GlobalTheory
