module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.RamUnit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.SplitUnitElements.Fst
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.SplitUnitElements.Imports

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.SplitUnitElements.IntE
open QuadraticAlgebra Matrix UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

theorem UpperTheory.V.Z.Sym.Loc.One.intE :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
        (∃ u : Oˣ, algebraMap O K u = τ ^ 2 - 4) → τ ∈ (algebraMap O K).range ∧ (∃ u : Oˣ, algebraMap O K u = 2 - τ) ∧ (∃ u : Oˣ, algebraMap O K u = 2 + τ) ∧
        ∀ x : Etau K τ, IsIntegral O x ↔ x.re ∈ (algebraMap O K).range ∧ x.im ∈ (algebraMap O K).range := by
  rintro O K _ _ _ _ _ Δ τ L ⟨u, hu⟩
  haveI := L.frac
  have sq_int : ∀ (x : K) (a : O), x ^ 2 = algebraMap O K a → ∃ b : O, algebraMap O K b = x := fun x a h =>
    IsIntegrallyClosed.algebraMap_eq_of_integral (IsIntegral.of_pow (n := 2) (by norm_num) (h ▸ isIntegral_algebraMap))
  obtain ⟨τ₀, e₀⟩ := sq_int τ (4 + u) (by rw [map_add (f := _), hu, map_ofNat]; ring)
  have hm : (2 - τ₀) * (2 + τ₀) = (-u : Oˣ) := IsFractionRing.injective O K (by
    simp only [map_mul, map_sub, map_add (f := _), map_ofNat, e₀, Units.val_neg, map_neg, hu]; ring)
  have h1 : IsUnit (2 - τ₀) := isUnit_of_mul_isUnit_left (hm ▸ (-u).isUnit)
  have h2 : IsUnit (2 + τ₀) := isUnit_of_mul_isUnit_right (hm ▸ (-u).isUnit)
  refine ⟨⟨τ₀, e₀⟩, ⟨h1.unit, by simp [map_ofNat, e₀]⟩, ⟨h2.unit, by simp [map_ofNat, e₀]⟩, fun x => ⟨fun hx => ?_, ?_⟩⟩
  · have down : ∀ a : K, IsIntegral O (algebraMap K (Etau K τ) a) → ∃ b : O, algebraMap O K b = a := fun a h =>
      IsIntegrallyClosed.algebraMap_eq_of_integral ((isIntegral_algebraMap_iff ).1 h)
    obtain ⟨t, ht⟩ := down (2 * x.re + τ * x.im) (by
      convert hx.add (isIntegral_star hx) using 1
      ext <;> simp; ring)
    obtain ⟨d, hd⟩ := down (x.im ^ 2 * (τ ^ 2 - 4)) (by
      convert (hx.sub (isIntegral_star hx)).pow 2 using 1
      ext <;> simp [sq] <;> ring)
    have hi : algebraMap O K u * algebraMap O K (u⁻¹ : Oˣ) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    obtain ⟨b, hb⟩ := sq_int x.im (d * (u⁻¹ : Oˣ)) (by rw [map_mul, hd, ← hu]; linear_combination (-x.im ^ 2) * hi)
    obtain ⟨i, hi2⟩ := L.two.exists_right_inv
    have hi2' : 2 * algebraMap O K i = 1 := by rw [← map_ofNat (algebraMap O K) 2, ← map_mul, hi2, map_one]
    refine ⟨⟨i * (t - τ₀ * b), ?_⟩, ⟨b, hb⟩⟩
    rw [map_mul, map_sub, map_mul, ht, e₀, hb]
    linear_combination x.re * hi2'
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine isIntegral_of_trace_norm (2 * a + τ₀ * b) (a * a + τ₀ * a * b + b * b) ?_ ?_
    · simp [QuadraticAlgebra.trace_def, map_ofNat, ha, hb, e₀]
    · simp [QuadraticAlgebra.norm_def, ha, hb, e₀]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.SplitUnitElements.EUnit
open QuadraticAlgebra Matrix UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

theorem UpperTheory.V.Z.Sym.Loc.One.eUnit :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
        (∃ u : Oˣ, algebraMap O K u = τ ^ 2 - 4) → ∀ u : (Etau K τ)ˣ, (∃ ε : Oˣ, QuadraticAlgebra.norm (u : Etau K τ) = algebraMap O K ε) →
        ∃ z v : (Etau K τ)ˣ, IsIntegral O (v : Etau K τ) ∧ IsIntegral O ((v⁻¹ : (Etau K τ)ˣ) : Etau K τ) ∧ (u : Etau K τ) = quo z * v := by
  intro O K _ _ _ _ _ Δ τ L hU u hε0
  obtain ⟨U, hU⟩ := hU
  obtain ⟨ε, hε⟩ := hε0
  haveI := L.frac
  let D : K := τ ^ 2 - 4
  have L' : IsLoc O D := ⟨L.frac, L.compl, L.fin, L.two, ⟨U, 1, one_ne_zero, by simp [D, hU]⟩⟩
  have hw : ((2 : K) • (ω : Etau K τ) - algebraMap K _ τ) * ((2 : K) • ω - algebraMap K _ τ)
      = D • 1 + (0 : K) • ((2 : K) • ω - algebraMap K _ τ) := by
    ext <;> simp [D] <;> ring
  let φ : Lsq K D →ₐ[K] Etau K τ := QuadraticAlgebra.lift ⟨_, hw⟩
  have hφ : ∀ z : Lsq K D, φ z = ⟨z.re - τ * z.im, 2 * z.im⟩ := by
    intro z
    ext <;> simp [φ] <;> ring
  have hn : ∀ z : Lsq K D, QuadraticAlgebra.norm (φ z) = QuadraticAlgebra.norm z := by
    intro z
    rw [hφ]
    simp [QuadraticAlgebra.norm_def, D]
    ring
  have hs : ∀ z : Lsq K D, φ (star z) = star (φ z) := by
    intro z
    rw [hφ, hφ]
    ext <;> simp <;> ring
  obtain ⟨ν, hνi, hνn⟩ := normEx O K D L' ε
  have hv0n : QuadraticAlgebra.norm (φ ν) = algebraMap O K ε := by rw [hn, hνn]
  have hεK : IsUnit (algebraMap O K (ε : O)) := ε.isUnit.map _
  have hv0u : IsUnit (φ ν) := QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr (by rw [hv0n]; exact hεK)
  obtain ⟨v, hv⟩ := hv0u
  have hvi : IsIntegral O (v : Etau K τ) := by
    rw [hv]
    exact IsIntegral.map (φ.restrictScalars O) hνi
  let β : Etau K τ := (u : Etau K τ) * ((v⁻¹ : (Etau K τ)ˣ) : Etau K τ)
  have hβn : QuadraticAlgebra.norm β = 1 := by
    have h1 : QuadraticAlgebra.norm (v : Etau K τ) * QuadraticAlgebra.norm ((v⁻¹ : (Etau K τ)ˣ) : Etau K τ) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    rw [hv, hv0n] at h1
    simp only [β, map_mul, hε]
    exact h1
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_isLoc L
  let β' : Lsq K D := ⟨β.re + τ * β.im / 2, β.im / 2⟩
  have hφβ : φ β' = β := by
    rw [hφ]
    ext <;> simp [β'] <;> field_simp <;> ring
  have hβ'n : QuadraticAlgebra.norm β' = 1 := by rw [← hn, hφβ, hβn]
  obtain ⟨y, hy⟩ := h90L O K D L' β' hβ'n
  let w : (Etau K τ)ˣ := Units.map (φ : Lsq K D →* Etau K τ) y
  have hw' : (w : Etau K τ) = φ y := rfl
  refine ⟨w⁻¹, v, hvi, ?_, ?_⟩
  · have e : ((v⁻¹ : (Etau K τ)ˣ) : Etau K τ)
        = star (v : Etau K τ) * algebraMap O (Etau K τ) ((ε⁻¹ : Oˣ) : O) := by
      apply Units.inv_eq_of_mul_eq_one_right
      rw [← mul_assoc, ← QuadraticAlgebra.algebraMap_norm_eq_mul_star, hv, hv0n,
        algebraMap_etau (τ := τ) ((ε⁻¹ : Oˣ) : O), ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    rw [e]
    exact (isIntegral_star hvi).mul isIntegral_algebraMap
  · have hq : quo w⁻¹ = β := by
      unfold quo
      rw [inv_inv, hw', ← hs, hy, map_mul, hφβ, mul_left_comm, ← hw', Units.inv_mul, mul_one]
    rw [hq]
    simp only [β, mul_assoc, Units.inv_mul, mul_one]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.SplitUnitElements.Princ
open QuadraticAlgebra Matrix UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

theorem UpperTheory.V.Z.Sym.Loc.One.princ :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
        (∃ u : Oˣ, algebraMap O K u = τ ^ 2 - 4) → ∀ S : Set (Etau K τ), IsLat O τ S → (∀ x ∈ S, ω * x ∈ S) →
        ∃ u : (Etau K τ)ˣ, ∀ x, x ∈ S ↔ IsIntegral O (((u⁻¹ : (Etau K τ)ˣ) : Etau K τ) * x) := by
  intro O K _ _ _ _ _ Δ τ hl hu S hS hω
  obtain ⟨hτ, -, -, -⟩ := One.intE O K Δ τ hl hu
  have hne : τ ^ 2 - 4 ≠ 0 := by
    obtain ⟨v, hv⟩ := hu
    rw [← hv]
    exact (Units.map (algebraMap O K).toMonoidHom v).ne_zero
  have hg : PK.Gen1 (O := O) (ω : Etau K τ) := by
    refine ⟨?_, ?_, ?_⟩
    · simpa [QuadraticAlgebra.trace] using hτ
    · exact ⟨1, by simp [QuadraticAlgebra.norm]⟩
    · simpa using hu
  exact PK.Gen1.princ hl hne hg hS hω
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.SplitUnitElements.Snd
open QuadraticAlgebra Matrix UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

theorem UpperTheory.V.Z.Sym.Loc.One.snd :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
        (∃ u : Oˣ, algebraMap O K u = τ ^ 2 - 4) → ∀ (c : K) (d m : EL Δ τ), IsDat c d m → ∀ (s : K) (ε : Oˣ), Δ * s ^ 2 = algebraMap O K ε →
        ∃ y₀ : (EL Δ τ)ˣ, ∀ S : Set (Sp Δ τ), IsFix O c d m S → ∀ x : EL Δ τ, ((0, x) : Sp Δ τ) ∈ S ↔
          ∃ a b : Etau K τ, x = (y₀ : EL Δ τ) * (ofE Δ a + (⟨0, s⟩ : Lsq K Δ) • ofE Δ b) ∧
            ((0, (y₀ : EL Δ τ) * ofE Δ a) : Sp Δ τ) ∈ S ∧ ((0, (y₀ : EL Δ τ) * ofE Δ b) : Sp Δ τ) ∈ S := by
  intro O K _ _ _ _ _ Δ τ L hD c d m h s ε hε
  obtain ⟨hτ, hu, ⟨n, hn⟩, -⟩ := One.intE O K Δ τ L hD
  have h2 := two_ne_zero_of_isLoc L
  have hε0 : algebraMap O K ε ≠ 0 := (ε.isUnit.map _).ne_zero
  have hn0 : 2 + τ ≠ 0 := hn ▸ (n.isUnit.map _).ne_zero
  have hs0 : s ≠ 0 := fun h => hε0 (by rw [← hε, h]; ring)
  have alg : ∀ x : O, algebraMap O (Lsq K Δ) x = algebraMap K _ (algebraMap O K x) := fun x => IsScalarTower.algebraMap_apply O K _ x
  have hww : (⟨0, s⟩ : Lsq K Δ) * ⟨0, s⟩ = algebraMap K _ (algebraMap O K ε) := by
    ext <;> simp
    rw [← hε]; ring
  have hw : IsInt O (⟨0, s⟩ : Lsq K Δ) := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    rw [sq, hww, ← alg]; exact isIntegral_algebraMap
  obtain ⟨i, hi⟩ := L.two.exists_right_inv
  have hi' : algebraMap K (Lsq K Δ) (algebraMap O K i) * 2 = 1 := by
    rw [← alg, ← map_ofNat (algebraMap O (Lsq K Δ)) 2, ← map_mul, mul_comm, hi, map_one]
  have hε' : algebraMap K (Lsq K Δ) (algebraMap O K (ε⁻¹ : Oˣ)) * algebraMap K _ (algebraMap O K ε) = 1 := by
    rw [← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]
  have hn' : algebraMap K (Lsq K Δ) (algebraMap O K (n⁻¹ : Oˣ)) * algebraMap K _ (2 + τ) = 1 := by
    rw [← hn, ← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]
  obtain ⟨lam, hl, hln⟩ := normEx O K Δ L n
  have hll : lam * star lam = algebraMap K _ (2 + τ) := by rw [← hn, ← hln, QuadraticAlgebra.algebraMap_norm_eq_mul_star]
  set r : Lsq K Δ := algebraMap O _ ((n⁻¹ : Oˣ) : O) * lam with hr
  have hri : IsInt O r := isIntegral_algebraMap.mul hl
  have hrr : r * star r * algebraMap K _ (2 + τ) = 1 := by
    have : star (algebraMap K (Lsq K Δ) (algebraMap O K (n⁻¹ : Oˣ))) = algebraMap K _ (algebraMap O K (n⁻¹ : Oˣ)) := by ext <;> simp
    rw [hr, star_mul', alg, this]
    linear_combination (algebraMap K (Lsq K Δ) (algebraMap O K (n⁻¹ : Oˣ)) ^ 2 * algebraMap K (Lsq K Δ) (2 + τ)) * hll +
      (algebraMap K (Lsq K Δ) (algebraMap O K (n⁻¹ : Oˣ)) * algebraMap K (Lsq K Δ) (2 + τ) + 1) * hn'
  have sg : ∀ (a : Lsq K Δ) (x : EL Δ τ), sigL (a • x) = star a • sigL x := fun a x => by ext <;> simp [sigL] <;> ring
  set d' : EL Δ τ := r • (ofE Δ ⟨1 + τ, -1⟩ * d) with hd'
  have hdd : sigL d' * sigL (sigL d') = 1 := by
    have e : ofE Δ (⟨1 + τ, -1⟩ : Etau K τ) * ofE Δ ⟨1 + τ, -1⟩ * ofE Δ ω = algebraMap K (Lsq K Δ) (2 + τ) • (1 : EL Δ τ) := by
      ext <;> simp [ofE, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] <;> ring
    rw [sigL_sigL, hd', sg, sigL_mul, sigL_ofE, smul_mul_smul_comm,
      show ofE Δ (⟨1 + τ, -1⟩ : Etau K τ) * sigL d * (ofE Δ ⟨1 + τ, -1⟩ * d) = ofE Δ ⟨1 + τ, -1⟩ * ofE Δ ⟨1 + τ, -1⟩ * (d * sigL d) by ring,
      h.d_norm, e, smul_smul, mul_comm (star r), hrr, one_smul]
  obtain ⟨y, hy⟩ := h90 O K Δ τ L h.reg _ hdd
  have hy' : d' * sigL (y : EL Δ τ) = y := by
    have := congrArg sigL hy
    rwa [sigL_mul, sigL_sigL, sigL_sigL, eq_comm] at this
  refine ⟨y, fun S hS x => ?_⟩
  obtain ⟨A, M, -, E⟩ := One.splitS O K Δ τ L hτ hu c d m h S hS
  have add : ∀ a b : EL Δ τ, ((0, a) : Sp Δ τ) ∈ S → ((0, b) : Sp Δ τ) ∈ S → ((0, a + b) : Sp Δ τ) ∈ S := fun a b ha hb => by
    simpa using A _ ha _ hb
  have mul : ∀ (t : Lsq K Δ) (a : EL Δ τ), IsInt O t → ((0, a) : Sp Δ τ) ∈ S → ((0, t • a) : Sp Δ τ) ∈ S := fun t a ht ha => by
    simpa using M _ ha t ht
  constructor
  · intro hx
    have h1 : ((0, d' * sigL x) : Sp Δ τ) ∈ S := by
      have a1 : semi d (0, x) ∈ S := hS.stab ▸ Set.mem_image_of_mem _ hx
      obtain ⟨τ₀, e₀⟩ := hτ
      have := mul r _ hri (E _ a1 ⟨1 + τ, -1⟩ ⟨1 + τ₀, by simp [e₀]⟩ ⟨-1, by simp⟩)
      rwa [hd', smul_mul_assoc, mul_assoc]
    obtain ⟨X, rfl⟩ : ∃ X, x = (y : EL Δ τ) * X := ⟨(y⁻¹ : (EL Δ τ)ˣ) * x, by simp⟩
    obtain ⟨a, b, rfl⟩ : ∃ a b : Etau K τ, X = ofE Δ a + (⟨0, s⟩ : Lsq K Δ) • ofE Δ b :=
      ⟨⟨X.re.re, X.im.re⟩, ⟨X.re.im / s, X.im.im / s⟩, by ext <;> simp [ofE] <;> field_simp⟩
    have e : sigL (ofE Δ a + (⟨0, s⟩ : Lsq K Δ) • ofE Δ b) = ofE Δ a - (⟨0, s⟩ : Lsq K Δ) • ofE Δ b := by
      ext <;> simp [sigL, ofE]
    rw [sigL_mul, ← mul_assoc, hy', e] at h1
    refine ⟨a, b, rfl, ?_, ?_⟩
    · convert mul _ _ (isIntegral_algebraMap (x := i)) (add _ _ hx h1) using 2
      rw [show (y : EL Δ τ) * (ofE Δ a + (⟨0, s⟩ : Lsq K Δ) • ofE Δ b) + (y : EL Δ τ) * (ofE Δ a - (⟨0, s⟩ : Lsq K Δ) • ofE Δ b) =
        (2 : Lsq K Δ) • ((y : EL Δ τ) * ofE Δ a) by rw [two_smul]; ring, smul_smul, alg, hi', one_smul]
    · convert mul _ _ (((isIntegral_algebraMap (x := i)).mul (isIntegral_algebraMap (x := ((ε⁻¹ : Oˣ) : O)))).mul hw)
        (add _ _ hx (mul _ _ isIntegral_one.neg h1)) using 2
      rw [show (y : EL Δ τ) * (ofE Δ a + (⟨0, s⟩ : Lsq K Δ) • ofE Δ b) + (-1 : Lsq K Δ) • ((y : EL Δ τ) * (ofE Δ a - (⟨0, s⟩ : Lsq K Δ) • ofE Δ b)) =
        ((2 : Lsq K Δ) * ⟨0, s⟩) • ((y : EL Δ τ) * ofE Δ b) by rw [mul_smul, two_smul, neg_one_smul, ← mul_smul_comm]; ring, smul_smul, alg, alg]
      rw [show algebraMap K (Lsq K Δ) (algebraMap O K i) * algebraMap K (Lsq K Δ) (algebraMap O K (ε⁻¹ : Oˣ)) * ⟨0, s⟩ * (2 * ⟨0, s⟩) = 1 by
        linear_combination (2 * algebraMap K (Lsq K Δ) (algebraMap O K i) * algebraMap K (Lsq K Δ) (algebraMap O K (ε⁻¹ : Oˣ))) * hww +
          (2 * algebraMap K (Lsq K Δ) (algebraMap O K i)) * hε' + hi', one_smul]
  · rintro ⟨a, b, rfl, ha, hb⟩
    rw [mul_add, mul_smul_comm]
    exact add _ _ ha (mul _ _ hw hb)
end

open QuadraticAlgebra Matrix UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

private theorem ofE_mul {K : Type} [Field K] {Δ τ : K} (x y : Etau K τ) : ofE Δ (x * y) = ofE Δ x * ofE Δ y := by
  ext <;> simp [ofE]

private theorem ofE_one {K : Type} [Field K] {Δ τ : K} : ofE Δ (1 : Etau K τ) = 1 := by
  ext <;> simp [ofE, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

private theorem herm_adj {K : Type} [Field K] {Δ τ : K} (c : K) (m : EL Δ τ) (u : Etau K τ) (x : Sp Δ τ) (y : EL Δ τ) :
    herm c m x (0, ofE Δ (star u) * y) = herm c m (0, ofE Δ u * x.2) (0, y) := by
  have e : star (sigL (ofE Δ (star u) * y)) = ofE Δ u * star (sigL y) := by
    ext <;> simp [ofE, sigL] <;> ring
  simp only [herm, e, star_zero, mul_zero, zero_add]
  congr 1
  ring


set_option maxHeartbeats 800000 in
theorem UpperTheory.V.Z.Sym.Loc.One.uniq :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
    (∃ u : Oˣ, algebraMap O K u = τ ^ 2 - 4) → ∀ (c : K) (d m : EL Δ τ), IsDat c d m → ∀ S₀ S₁ : Set (Sp Δ τ), IsFix O c d m S₀ → IsFix O c d m S₁ →
    ∃ z : (Etau K τ)ˣ, ∀ x, x ∈ S₀ ↔ tor Δ z x ∈ S₁ := by
  intro O K _ _ _ _ _ Δ τ hl hu c d m hd
  haveI := hl.frac
  obtain ⟨hτ, h2, -, hint⟩ := One.intE O K Δ τ hl hu
  obtain ⟨ε, s₀, hs₀, hΔ⟩ := hl.even
  obtain ⟨y₀, hy⟩ := One.snd O K Δ τ hl hu c d m hd s₀⁻¹ ε (by rw [hΔ]; field_simp)
  have hsp := One.splitS O K Δ τ hl hτ h2 c d m hd
  have hmul : ∀ S, IsFix O c d m S → ∀ v : Etau K τ, IsIntegral O v → ∀ x ∈ S, ((0, ofE Δ v * x.2) : Sp Δ τ) ∈ S :=
    fun S hS v hv x hx => (hsp S hS).2.2.2 x hx v ((hint v).1 hv).1 ((hint v).1 hv).2
  have hsnd : ∀ S, IsFix O c d m S → ∀ x ∈ S, ((0, x.2) : Sp Δ τ) ∈ S := fun S hS x hx => by
    simpa [ofE_one] using hmul S hS 1 isIntegral_one x hx
  have hpr : ∀ S, IsFix O c d m S → ∃ u : (Etau K τ)ˣ, ∀ a, ((0, (y₀ : EL Δ τ) * ofE Δ a) : Sp Δ τ) ∈ S ↔
      IsIntegral O (((u⁻¹ : (Etau K τ)ˣ) : Etau K τ) * a) := fun S hS => by
    refine One.princ O K Δ τ hl hu _ (One.lat O K Δ τ hl c d m S hS y₀) fun a ha => ?_
    have hω : IsIntegral O (ω : Etau K τ) := (hint _).2 ⟨by simp, by simp⟩
    have := hmul S hS ω hω _ ha
    change ((0, (y₀ : EL Δ τ) * ofE Δ (ω * a)) : Sp Δ τ) ∈ S
    rw [ofE_mul, mul_left_comm]
    exact this
  have half : ∀ S S', IsFix O c d m S → IsFix O c d m S' → ∀ u u' : (Etau K τ)ˣ,
      (∀ a, ((0, (y₀ : EL Δ τ) * ofE Δ a) : Sp Δ τ) ∈ S ↔ IsIntegral O (((u⁻¹ : (Etau K τ)ˣ) : Etau K τ) * a)) →
      (∀ a, ((0, (y₀ : EL Δ τ) * ofE Δ a) : Sp Δ τ) ∈ S' ↔ IsIntegral O (((u'⁻¹ : (Etau K τ)ˣ) : Etau K τ) * a)) →
      (∀ x ∈ S, ((0, ofE Δ ((u' * u⁻¹ : (Etau K τ)ˣ) : Etau K τ) * x.2) : Sp Δ τ) ∈ S') ∧
        QuadraticAlgebra.norm ((u' * u⁻¹ : (Etau K τ)ˣ) : Etau K τ) ∈ (algebraMap O K).range := by
    intro S S' hS hS' u u' h h'
    have k : ∀ a, ((0, (y₀ : EL Δ τ) * ofE Δ a) : Sp Δ τ) ∈ S →
        ((0, (y₀ : EL Δ τ) * ofE Δ (((u' * u⁻¹ : (Etau K τ)ˣ) : Etau K τ) * a)) : Sp Δ τ) ∈ S' := fun a ha => by
      rw [h', Units.val_mul, mul_assoc, Units.inv_mul_cancel_left]
      exact (h a).1 ha
    have f : ∀ x ∈ S, ((0, ofE Δ ((u' * u⁻¹ : (Etau K τ)ˣ) : Etau K τ) * x.2) : Sp Δ τ) ∈ S' := fun x hx => by
      obtain ⟨a, b, e, ha, hb⟩ := (hy S hS x.2).1 (hsnd S hS x hx)
      refine (hy S' hS' _).2 ⟨_, _, ?_, k a ha, k b hb⟩
      rw [e, ofE_mul, ofE_mul, ← mul_smul_comm]
      ring
    refine ⟨f, ?_⟩
    generalize ((u' * u⁻¹ : (Etau K τ)ˣ) : Etau K τ) = t at f
    have g : ∀ y, ((0, y) : Sp Δ τ) ∈ S' → ((0, ofE Δ (star t) * y) : Sp Δ τ) ∈ S := fun y hy' =>
      (hS.dual _).2 fun x hx => by
        rw [herm_adj]
        exact (hS'.dual _).1 hy' _ (f x hx)
    have h1 : ((0, (y₀ : EL Δ τ) * ofE Δ (u : Etau K τ)) : Sp Δ τ) ∈ S := by
      rw [h, Units.inv_mul]; exact isIntegral_one
    have h3 := g _ (f _ h1)
    have e : ofE Δ (star t) * (ofE Δ t * ((y₀ : EL Δ τ) * ofE Δ (u : Etau K τ))) =
        (y₀ : EL Δ τ) * ofE Δ ((u : Etau K τ) * (t * star t)) := by
      rw [ofE_mul, ofE_mul]; ring
    dsimp only at h3
    rw [e, h, Units.inv_mul_cancel_left, ← algebraMap_norm_eq_mul_star] at h3
    simpa using ((hint _).1 h3).1
  intro S₀ S₁ h₀ h₁
  obtain ⟨u₀, hu₀⟩ := hpr S₀ h₀
  obtain ⟨u₁, hu₁⟩ := hpr S₁ h₁
  obtain ⟨f₀, n₀, hn₀⟩ := half S₀ S₁ h₀ h₁ u₀ u₁ hu₀ hu₁
  obtain ⟨f₁, n₁, hn₁⟩ := half S₁ S₀ h₁ h₀ u₁ u₀ hu₁ hu₀
  have hinv : u₀ * u₁⁻¹ = (u₁ * u₀⁻¹)⁻¹ := by simp
  rw [hinv] at f₁ hn₁
  generalize u₁ * u₀⁻¹ = u at f₀ f₁ hn₀ hn₁
  have hn : n₀ * n₁ = 1 := IsFractionRing.injective O K (by
    rw [map_mul, hn₀, hn₁, ← map_mul, Units.mul_inv, map_one, map_one])
  obtain ⟨z, v, hv, hv', e⟩ := One.eUnit O K Δ τ hl hu u ⟨Units.mkOfMulEqOne n₀ n₁ hn, hn₀.symm⟩
  refine ⟨z, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · have a := One.fst O K Δ τ hl hτ h2 c d m hd S₀ S₁ h₀ h₁ _ ((hsp S₀ h₀).2.2.1 x hx)
    have b := f₀ _ (hmul S₀ h₀ _ hv' x hx)
    have := (hsp S₁ h₁).1 _ a _ b
    rw [e, ← mul_assoc, ← ofE_mul, Units.mul_inv_cancel_right] at this
    simpa [tor] using this
  · have a := One.fst O K Δ τ hl hτ h2 c d m hd S₁ S₀ h₁ h₀ _ ((hsp S₁ h₁).2.2.1 _ hx)
    have b := f₁ _ (hmul S₁ h₁ _ hv _ hx)
    have := (hsp S₀ h₀).1 _ a _ b
    have e' : ofE Δ ((u⁻¹ : (Etau K τ)ˣ) : Etau K τ) * (ofE Δ (v : Etau K τ) * (ofE Δ (quo z) * x.2)) = x.2 := by
      rw [← mul_assoc (ofE Δ (v : Etau K τ)), ← ofE_mul, mul_comm (v : Etau K τ), ← e, ← mul_assoc, ← ofE_mul, Units.inv_mul, ofE_one,
        one_mul]
    simp only [tor, e'] at this
    simpa using this
